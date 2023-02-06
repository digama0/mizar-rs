#![allow(unused)]
use crate::ast::{CaseKind, FormulaBinder, FormulaBinop, ReservedId, VarKind};
use crate::checker::Checker;
use crate::reader::Reader;
use crate::types::*;
use crate::*;
use std::ops::Range;

const MAX_EXPANSIONS: usize = 20;

struct Analyzer<'a> {
  r: &'a mut Reader,
  sch_func_args: IdxVec<SchFuncId, Box<[Type]>>,
  priv_func_args: IdxVec<PrivPredId, Box<[Type]>>,
  priv_pred: IdxVec<PrivPredId, (Box<[Type]>, Box<Formula>)>,
  sch_pred_args: IdxVec<SchPredId, Box<[Type]>>,
  thesis: Option<Box<Formula>>,
  reserved: IdxVec<ReservedId, Type>,
}
impl<'a> std::ops::Deref for Analyzer<'a> {
  type Target = &'a mut Reader;
  fn deref(&self) -> &Self::Target { &self.r }
}
impl<'a> std::ops::DerefMut for Analyzer<'a> {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.r }
}

impl Reader {
  pub fn run_analyzer(&mut self, path: &MizPath) {
    if !ENABLE_ANALYZER {
      panic!("analyzer is not enabled")
    }
    let mut analyzer = Analyzer {
      r: self,
      sch_func_args: Default::default(),
      priv_func_args: Default::default(),
      priv_pred: Default::default(),
      sch_pred_args: Default::default(),
      thesis: None,
      reserved: Default::default(),
    };
    let r = path.open_msx().unwrap().parse_items();
    println!("parsed {:?}, {} items", path.0, r.len());
    for (i, it) in r.iter().enumerate() {
      if let Some(n) = FIRST_VERBOSE_TOP_ITEM {
        set_verbose(i >= n);
      }
      if TOP_ITEM_HEADER {
        eprintln!("item {i}: {it:?}");
      }
      analyzer.elab_top_item(it);
    }
  }
}

impl Pattern {
  fn check_types<'a>(
    &self, g: &Global, lc: &LocalContext, args: &'a [TermQua],
  ) -> Option<Subst<'a>> {
    if self.primary.is_empty() {
      return Some(Subst::new(0))
    }
    let mut subst = Subst::from_essential(self.primary.len(), &self.visible, args);
    if subst.check_types(g, lc, &self.primary) {
      Some(subst)
    } else {
      None
    }
  }
}

/// Agree
fn agrees(g: &Global, lc: &LocalContext, tms: &[TermQua], tys: &[Type]) -> bool {
  let mut subst = Subst { subst_term: tms.iter().map(|tm| Some(CowBox::Borrowed(tm))).collect() };
  subst.check_types(g, lc, tys)
}

struct Scope {
  sc: crate::reader::Scope,
  priv_preds: usize,
  thesis: Option<Box<Formula>>,
}

impl Analyzer<'_> {
  fn open_scope(&mut self, push_label: bool, copy_thesis: bool) -> Scope {
    Scope {
      sc: self.r.open_scope(push_label),
      priv_preds: self.priv_pred.len(),
      thesis: if copy_thesis { self.thesis.clone() } else { self.thesis.take() },
    }
  }

  fn close_scope(&mut self, sc: Scope, check_for_local_const: bool) {
    self.priv_func_args.0.truncate(sc.sc.priv_funcs);
    self.priv_pred.0.truncate(sc.priv_preds);
    self.thesis = sc.thesis;
    self.r.close_scope(sc.sc, check_for_local_const);
  }

  fn scope<R>(
    &mut self, label: Option<LabelId>, copy_thesis: bool, check_for_local_const: bool,
    f: impl FnOnce(&mut Self) -> R,
  ) -> R {
    let sc = self.open_scope(label.is_some(), copy_thesis);
    let r = f(self);
    self.close_scope(sc, check_for_local_const);
    r
  }

  fn elab_top_item(&mut self, it: &ast::Item) {
    match &it.kind {
      ast::ItemKind::Section | ast::ItemKind::Pragma { .. } => {}
      ast::ItemKind::Block { kind, items, .. } => {
        let mut br = BlockReader::new(*kind, &self.lc);
        self.scope(None, false, false, |this| br.elab_proof(this, items));
        br.after_scope(self)
      }
      ast::ItemKind::SchemeBlock(it) => self.scope(None, false, false, |this| this.elab_scheme(it)),
      ast::ItemKind::Theorem { prop, just } => {
        let f = self.elab_proposition(prop);
        Exportable.visit_formula(&f);
        self.elab_justification(&f, just)
      }
      ast::ItemKind::Reservation(it) => {
        self.lc.term_cache.get_mut().open_scope();
        assert!(self.lc.bound_var.is_empty());
        for ty in it.tys.as_deref().unwrap() {
          let ty = self.elab_type(ty);
          self.lc.bound_var.push(ty);
        }
        let ty = self.elab_type(&it.ty);
        Exportable.visit_type(&ty);
        self.reserved.push(ty);
        self.lc.bound_var.0.clear();
        self.lc.term_cache.get_mut().close_scope();
      }
      _ => self.elab_stmt_item(it),
    }
  }

  fn elab_scheme(&mut self, ast::SchemeBlock { end, head, items }: &ast::SchemeBlock) {
    let ast::SchemeHead { sym, nr, groups, concl, prems } = head;
    assert!(self.lc.sch_func_ty.is_empty());
    let infer_consts = self.lc.infer_const.get_mut().0.len();
    for group in groups {
      match group {
        ast::SchemeBinderGroup::Func { vars, tys, ret, .. } => {
          self.elab_intern_push_locus_tys(tys);
          let ret = self.elab_intern_type(ret);
          assert!(!vars.is_empty());
          for _ in 1..vars.len() {
            self.sch_func_args.push(self.r.lc.locus_ty.0.to_vec().into());
            self.r.lc.sch_func_ty.push(ret.clone());
          }
          self.sch_func_args.push(self.r.lc.locus_ty.0.drain(..).collect());
          self.r.lc.sch_func_ty.push(ret);
        }
        ast::SchemeBinderGroup::Pred { vars, tys, .. } => {
          self.elab_intern_push_locus_tys(tys);
          assert!(!vars.is_empty());
          for _ in 1..vars.len() {
            self.sch_pred_args.push(self.r.lc.locus_ty.0.to_vec().into());
          }
          self.sch_pred_args.push(self.r.lc.locus_ty.0.drain(..).collect());
        }
      }
    }
    let prems = prems.iter().map(|prop| self.elab_proposition(prop)).collect::<Box<[_]>>();
    let mut thesis = self.elab_intern_formula(concl, true);
    self.elab_proof(None, &thesis, items);
    let mut primary = self.lc.sch_func_ty.0.drain(..).collect::<Box<[_]>>();
    let mut sch = Scheme { sch_funcs: primary, prems, thesis };
    self.lc.expand_consts(|c| sch.visit(c));
    sch.sch_funcs.iter().for_each(|ty| Exportable.visit_type(ty));
    sch.prems.iter().for_each(|ty| Exportable.visit_formula(ty));
    Exportable.visit_formula(&sch.thesis);
    self.lc.infer_const.get_mut().truncate(infer_consts);
    self.libs.sch.insert((ArticleId::SELF, *nr), sch);
  }

  fn elab_stmt_item(&mut self, item: &ast::Item) {
    match &item.kind {
      ast::ItemKind::Set { value, .. } => {
        let term = self.elab_intern_term(value);
        let ty = term.get_type_uncached(&self.g, &self.lc);
        self.lc.fixed_var.push(FixedVar { ty, def: Some(Box::new(term)) });
      }
      ast::ItemKind::DefFunc { var, tys, value } => {
        self.lc.term_cache.get_mut().open_scope();
        self.elab_intern_push_locus_tys(tys);
        let value = self.elab_intern_term(value);
        let ty = value.get_type(&self.g, &self.lc, false);
        let primary = self.r.lc.locus_ty.0.drain(..).collect();
        self.lc.term_cache.get_mut().close_scope();
        self.r.lc.priv_func.push(FuncDef { primary, ty: Box::new(ty), value: Box::new(value) });
      }
      ast::ItemKind::DefPred { var, tys, value } => {
        self.lc.term_cache.get_mut().open_scope();
        self.elab_intern_push_locus_tys(tys);
        let value = self.elab_intern_formula(value, true);
        let primary = self.r.lc.locus_ty.0.drain(..).collect();
        self.lc.term_cache.get_mut().close_scope();
        self.priv_pred.push((primary, Box::new(value)));
      }
      ast::ItemKind::Reconsider { vars, ty, just } => {
        let ty = self.elab_intern_type(ty);
        let f = Formula::mk_and_with(|conjs| {
          for var in vars {
            let ast::ReconsiderVar::Equality { tm, .. } = var else { unreachable!() };
            let tm = Box::new(self.elab_intern_term(tm));
            conjs.push(Formula::Is { term: tm.clone(), ty: Box::new(ty.clone()) });
            self.lc.fixed_var.push(FixedVar { ty: ty.clone(), def: Some(tm) });
          }
        });
        self.elab_justification(&f, just)
      }
      ast::ItemKind::Consider { vars, conds, just } => {
        let start = self.lc.fixed_var.len();
        for var in vars {
          self.elab_fixed_vars(var);
        }
        let mut f = Formula::mk_and_with(|conjs| {
          conds.iter().for_each(|prop| self.elab_proposition(prop).append_conjuncts_to(conjs))
        })
        .mk_neg();
        let end = self.lc.fixed_var.len();
        self.lc.mk_forall(start..end, false, &mut f);
        self.elab_justification(&f.mk_neg(), just);
      }
      ast::ItemKind::Statement(stmt) => {
        self.elab_stmt(stmt);
      }
      _ => unreachable!("unexpected item"),
    }
  }

  fn elab_stmt(&mut self, stmt: &ast::Statement) -> Formula {
    match stmt {
      ast::Statement::Proposition { prop, just } => {
        let f = self.elab_proposition(prop);
        self.elab_justification(&f, just);
        f
      }
      ast::Statement::IterEquality { prop, just, steps } => {
        if let Formula::Pred { nr, args } = self.elab_intern_formula(&prop.f, true) {
          if let (nr, [lhs, rhs]) = Formula::adjust_pred(nr, &args, &self.g.constrs) {
            if self.g.reqs.equals_to() == Some(nr) {
              self.elab_justification(&self.g.reqs.mk_eq(lhs.clone(), rhs.clone()), just);
              let mut mid = rhs.clone();
              for ast::IterStep { rhs, just, .. } in steps {
                let rhs = self.elab_intern_term(rhs);
                self.elab_justification(&self.g.reqs.mk_eq(mid, rhs.clone()), just);
                mid = rhs;
              }
              let f = self.g.reqs.mk_eq(lhs.clone(), mid);
              self.push_prop(prop.label.as_ref().map(|l| l.id.0), f.clone());
              return f
            }
          }
        }
        panic!("not an equality")
      }
      ast::Statement::Now { label, items, .. } => {
        ReconstructThesis { stack: vec![] }.elab_proof(self, items);
        *self.thesis.take().unwrap()
      }
    }
  }

  fn elab_proof(&mut self, label: Option<LabelId>, thesis: &Formula, items: &[ast::Item]) {
    self.scope(label, false, false, |this| {
      this.thesis = Some(Box::new(thesis.clone()));
      WithThesis.elab_proof(this, items)
    })
  }

  fn elab_fixed_vars(&mut self, var: &ast::BinderGroup) {
    assert!(!var.vars.is_empty());
    let ty = self.elab_intern_type(var.ty.as_deref().unwrap());
    for _ in 1..var.vars.len() {
      self.lc.fixed_var.push(FixedVar { ty: ty.clone(), def: None });
    }
    self.lc.fixed_var.push(FixedVar { ty, def: None });
  }

  fn elab_proposition(&mut self, prop: &ast::Proposition) -> Formula {
    let f = self.elab_intern_formula(&prop.f, true);
    self.push_prop(prop.label.as_ref().map(|l| l.id.0), f.clone());
    f
  }

  fn elab_justification(&mut self, thesis: &Formula, just: &ast::Justification) {
    match just {
      &ast::Justification::Inference { pos, ref kind, ref refs } => {
        let it = Inference {
          kind: match kind {
            ast::InferenceKind::By { link } => InferenceKind::By { linked: link.is_some() },
            &ast::InferenceKind::From { sch } => InferenceKind::From { sch },
          },
          pos,
          refs: refs.clone(),
        };
        self.r.read_inference(thesis, &it)
      }
      ast::Justification::Block { items, .. } => self.elab_proof(None, thesis, items),
    }
  }

  fn elab_corr_conds(
    &mut self, mut cc: CorrConds, conds: &[ast::CorrCond], corr: &Option<ast::Correctness>,
  ) {
    for cond in conds {
      let mut thesis = cc.0[cond.kind].take().unwrap();
      thesis.visit(&mut self.intern_const());
      self.elab_justification(&thesis, &cond.just);
      self.push_prop(None, *thesis);
    }
    if let Some(corr) = corr {
      let mut thesis = Formula::mk_and_with(|conjs| {
        for &kind in &corr.conds {
          cc.0[kind].take().unwrap().append_conjuncts_to(conjs);
        }
      });
      thesis.visit(&mut self.intern_const());
      self.elab_justification(&thesis, &corr.just);
      self.push_prop(None, thesis);
    }
    assert!(cc.0.iter().all(|p| p.1.is_none()));
  }

  fn elab_properties(&mut self, props: &[ast::Property], out: &mut PropertySet) {
    for prop in props {
      // todo!();
      out.set(prop.kind);
    }
  }

  fn elab_def_case<T, U>(
    &mut self, def: &ast::DefCase<T>, f: impl FnOnce(&mut Self, &T) -> U + Copy,
  ) -> DefCase<U> {
    let case = f(self, &def.case);
    let it_type = self.lc.it_type.take(); // can't use 'it' inside the guard
    let guard = self.elab_formula(&def.guard, true);
    self.lc.it_type = it_type;
    DefCase { case, guard }
  }

  fn elab_def_body<T, U>(
    &mut self, body: &ast::DefBody<T>, f: impl FnOnce(&mut Self, &T) -> U + Copy,
  ) -> DefBody<U> {
    DefBody {
      cases: body.cases.iter().map(|c| self.elab_def_case(c, f)).collect(),
      otherwise: body.otherwise.as_deref().map(|ow| f(self, ow)),
    }
  }

  fn elab_def_value(&mut self, value: &ast::DefValue, pos: bool) -> DefValue {
    match value {
      ast::DefValue::Term(body) => {
        let it_type = self.lc.it_type.take();
        let res = DefValue::Term(self.elab_def_body(body, |this, t| this.elab_term(t)));
        self.lc.it_type = it_type;
        res
      }
      ast::DefValue::Formula(body) =>
        DefValue::Formula(self.elab_def_body(body, |this, f| this.elab_formula(f, pos))),
    }
  }

  fn elab_functor_term(&mut self, fmt: FormatFunc, args: &[ast::Term]) -> Term {
    let args = self.elab_terms_qua(args);
    let fmt = self.formats[&Format::Func(fmt)];
    for pat in self.notations.functor.iter().rev() {
      if pat.fmt == fmt {
        if let Some(subst) = pat.check_types(&self.g, &self.lc, &args) {
          let PatternKind::Func(nr) = pat.kind else { unreachable!() };
          let mut args = subst.trim_to(self.g.constrs.functor[nr].primary.len());
          args.iter_mut().for_each(|t| t.strip_qua_mut());
          let tm = Term::Functor { nr, args };
          TermCollection::insert(&self.g, &self.lc, &tm, false);
          return tm
        }
      }
    }
    panic!("type error")
  }

  fn elab_pred(&mut self, fmt: FormatPred, args: Vec<TermQua>, pos: bool) -> Formula {
    let fmt = self.formats[&Format::Pred(fmt)];
    for pat in self.notations.predicate.iter().rev() {
      if pat.fmt == fmt {
        if let Some(subst) = pat.check_types(&self.g, &self.lc, &args) {
          let PatternKind::Pred(nr) = pat.kind else { unreachable!() };
          let mut args = subst.trim_to(self.g.constrs.predicate[nr].primary.len());
          args.iter_mut().for_each(|t| t.strip_qua_mut());
          return Formula::Pred { nr, args }.maybe_neg(pat.pos == pos)
        }
      }
    }
    panic!("type error")
  }

  fn elab_term_qua(&mut self, tm: &ast::Term) -> TermQua {
    // vprintln!("elab_term {tm:?}");
    match *tm {
      ast::Term::Placeholder { nr, .. } => Term::Locus(nr),
      ast::Term::Simple { kind, var, .. } => match kind {
        VarKind::Free => Term::Locus(LocusId(var as _)),
        VarKind::Reserved => Term::FreeVar(FVarId(var)),
        VarKind::Bound => Term::Bound(BoundId(var)),
        VarKind::Const | VarKind::DefConst => Term::Constant(ConstId(var)),
        _ => unreachable!(),
      },
      ast::Term::Numeral { value, .. } => Term::Numeral(value),
      ast::Term::Infix { ref sym, left, ref args, .. } => self.elab_functor_term(
        FormatFunc::Func { sym: sym.0, left, right: args.len() as u8 - left },
        args,
      ),
      ast::Term::Bracket { ref lsym, ref rsym, ref args, .. } => self.elab_functor_term(
        FormatFunc::Bracket { lsym: lsym.0, rsym: rsym.0, args: args.len() as u8 },
        args,
      ),
      ast::Term::PrivFunc { kind, ref sym, ref args, .. } => {
        let mut args = self.elab_terms_qua(args);
        match kind {
          VarKind::PrivFunc => {
            let nr = PrivFuncId(sym.0);
            let def = &self.lc.priv_func[nr];
            assert!(agrees(&self.g, &self.lc, &args, &def.primary));
            args.iter_mut().for_each(|t| t.strip_qua_mut());
            let depth = self.lc.bound_var.len() as u32;
            let value = def.value.visit_cloned(&mut Inst { subst: &args, base: 0, depth });
            Term::PrivFunc { nr, args, value }
          }
          VarKind::SchFunc => {
            let nr = SchFuncId(sym.0);
            assert!(agrees(&self.g, &self.lc, &args, &self.sch_func_args[nr]));
            args.iter_mut().for_each(|t| t.strip_qua_mut());
            let depth = self.lc.bound_var.len() as u32;
            Term::SchFunc { nr, args }
          }
          _ => unreachable!(),
        }
      }
      ast::Term::Aggregate { ref sym, ref args, .. } => {
        let args = self.elab_terms_qua(args);
        let fmt = self.formats[&Format::Aggr(FormatAggr { sym: sym.0, args: args.len() as u8 })];
        for pat in self.notations.functor.iter().rev() {
          if pat.fmt == fmt {
            if let Some(subst) = pat.check_types(&self.g, &self.lc, &args) {
              let PatternKind::Aggr(nr) = pat.kind else { unreachable!() };
              let mut args = subst.trim_to(self.g.constrs.aggregate[nr].primary.len());
              args.iter_mut().for_each(|t| t.strip_qua_mut());
              let tm = Term::Aggregate { nr, args };
              TermCollection::insert(&self.g, &self.lc, &tm, false);
              return tm
            }
          }
        }
        panic!("type error")
      }
      ast::Term::SubAggr { ref sym, ref arg, .. } => {
        let arg = self.elab_term_qua(arg);
        let fmt = self.formats[&Format::SubAggr(sym.0)];
        for pat in self.notations.sub_aggr.iter().rev() {
          if pat.fmt == fmt {
            if let Some(subst) = pat.check_types(&self.g, &self.lc, std::slice::from_ref(&arg)) {
              let PatternKind::SubAggr(nr) = pat.kind else { unreachable!() };
              let ty = arg.get_type_uncached(&self.g, &self.lc);
              return Term::mk_aggr(&self.g, nr, &arg.strip_qua(), &ty)
            }
          }
        }
        panic!("type error")
      }
      ast::Term::Selector { ref sym, ref arg, .. } => {
        let arg = self.elab_term_qua(arg);
        let fmt = self.formats[&Format::Sel(sym.0)];
        for pat in self.notations.selector.iter().rev() {
          if pat.fmt == fmt {
            if let Some(subst) = pat.check_types(&self.g, &self.lc, std::slice::from_ref(&arg)) {
              let PatternKind::Sel(nr) = pat.kind else { unreachable!() };
              let mut args = subst.trim_to(self.g.constrs.selector[nr].primary.len());
              args.iter_mut().for_each(|t| t.strip_qua_mut());
              let tm = Term::Selector { nr, args };
              TermCollection::insert(&self.g, &self.lc, &tm, false);
              return tm
            }
          }
        }
        panic!("type error")
      }
      ast::Term::InternalSelector { ref sym, .. } => {
        // only occurs inside elab_struct_def, ensured by parser
        Term::Constant(ConstId(sym.0))
      }
      ast::Term::The { ref ty, .. } => Term::The { ty: Box::new(self.elab_type(ty)) },
      ast::Term::Fraenkel { ref vars, ref scope, ref compr, .. } => {
        self.lc.term_cache.get_mut().open_scope();
        let orig_len = self.lc.bound_var.len();
        for var in vars {
          assert!(!var.vars.is_empty());
          let dom = self.elab_type(var.ty.as_deref().unwrap());
          assert!(dom.is_set(&self.g, &self.lc, &self.properties));
          self.push_many_bound(dom, var.vars.len());
        }
        let scope = Box::new(self.elab_term(scope));
        let compr = Box::new(compr.as_ref().map_or(Formula::True, |f| self.elab_formula(f, true)));
        let args = self.lc.bound_var.0.split_off(orig_len).into();
        self.lc.term_cache.get_mut().close_scope();
        Term::Fraenkel { args, scope, compr }
      }
      ast::Term::Qua { ref term, ref ty, .. } =>
        Term::Qua { value: Box::new(self.elab_term(term)), ty: Box::new(self.elab_type(ty)) },
      ast::Term::It { .. } => {
        assert!(self.lc.it_type.is_some(), "unexpected 'it'");
        Term::It
      }
    }
  }

  fn elab_term(&mut self, tm: &ast::Term) -> Term { self.elab_term_qua(tm).strip_qua() }

  fn elab_terms_qua(&mut self, tms: &[ast::Term]) -> Box<[TermQua]> {
    tms.iter().map(|t| self.elab_term_qua(t)).collect()
  }

  fn elab_terms(&mut self, tms: &[ast::Term]) -> Box<[Term]> {
    tms.iter().map(|t| self.elab_term(t)).collect()
  }

  /// AnalyzeAttrFrm
  fn elab_is_attr(&mut self, attr: &ast::Attr, pos: bool, tm: &TermQua) -> Formula {
    match attr {
      ast::Attr::Non { attr, .. } => self.elab_is_attr(attr, !pos, tm),
      ast::Attr::Attr { sym, args, .. } => {
        let args = (args.iter().map(|t| self.elab_term_qua(t)))
          .chain(std::iter::once(tm.clone()))
          .collect_vec();
        let fmt = self.formats[&Format::Attr(FormatAttr { sym: sym.0, args: args.len() as u8 })];
        for pat in self.notations.attribute.iter().rev() {
          if pat.fmt == fmt {
            if let Some(subst) = pat.check_types(&self.g, &self.lc, &args) {
              let PatternKind::Attr(nr) = pat.kind else { unreachable!() };
              let mut args = subst.trim_to(self.g.constrs.attribute[nr].primary.len());
              args.iter_mut().for_each(|t| t.strip_qua_mut());
              let (nr, args) = Formula::adjust_attr(nr, &args, &self.g.constrs);
              return Formula::Attr { nr, args: args.to_owned().into() }.maybe_neg(pat.pos == pos)
            }
          }
        }
        panic!("type error")
      }
    }
  }

  /// AnalyzeAttribute
  fn elab_push_attr(&mut self, attr: &ast::Attr, mut pos: bool, ty: &mut Type) {
    match attr {
      ast::Attr::Non { attr, .. } => self.elab_push_attr(attr, !pos, ty),
      ast::Attr::Attr { sym, args, .. } => {
        let v = self.lc.bound_var.push(std::mem::take(ty));
        let args = (args.iter().map(|t| self.elab_term_qua(t)))
          .chain(std::iter::once(Term::Bound(v)))
          .collect_vec();
        let fmt = self.formats[&Format::Attr(FormatAttr { sym: sym.0, args: args.len() as u8 })];
        for pat in self.r.notations.attribute.iter().rev() {
          if pat.fmt == fmt {
            if let Some(subst) = pat.check_types(&self.g, &self.lc, &args) {
              let PatternKind::Attr(nr) = pat.kind else { unreachable!() };
              let c = &self.g.constrs.attribute[nr].c;
              let nr = c.redefines.unwrap_or(nr);
              assert!(c.superfluous == 0); // check with mizar if this fails
              let args = (subst.subst_term.into_vec().into_iter().take(c.primary.len() - 1))
                .map(|t| *t.unwrap().to_owned())
                .collect::<Box<[_]>>();
              *ty = self.r.lc.bound_var.0.pop().unwrap();
              pos = pat.pos == pos;
              ty.attrs.0.insert(&self.g.constrs, Attr { nr, pos, args: args.clone() });
              ty.attrs.1.insert(&self.g.constrs, Attr { nr, pos, args });
              ty.round_up_with_self(&self.g, &self.lc, false);
              assert!(matches!(ty.attrs.0, Attrs::Consistent(_)));
              return
            }
          }
        }
        panic!("type error")
      }
    }
  }

  fn elab_type(&mut self, ty: &ast::Type) -> Type {
    // vprintln!("elab_type {ty:?}");
    match ty {
      ast::Type::Mode { sym, args, .. } => {
        let args = self.elab_terms_qua(args);
        let fmt = self.formats[&Format::Mode(FormatMode { sym: sym.0, args: args.len() as u8 })];
        for pat in self.notations.mode.iter().rev() {
          if pat.fmt == fmt {
            if let Some(subst) = pat.check_types(&self.g, &self.lc, &args) {
              let mut ty;
              let depth = self.lc.bound_var.len() as u32;
              match pat.kind {
                PatternKind::Mode(nr) => {
                  let mut args = subst.trim_to(self.g.constrs.mode[nr].primary.len()).to_vec();
                  args.iter_mut().for_each(|t| t.strip_qua_mut());
                  ty = Type { kind: TypeKind::Mode(nr), attrs: Default::default(), args }
                }
                PatternKind::ExpandableMode { ref expansion } => {
                  ty = (**expansion).clone();
                  ty.visit(&mut Inst { subst: &subst.finish(), base: 0, depth });
                }
                _ => unreachable!(),
              }
              let mut attrs = ty.attrs.1.clone();
              if let TypeKind::Mode(nr) = ty.kind {
                if nr != ModeId::ANY {
                  attrs.enlarge_by(&self.g.constrs, &self.g.constrs.mode[nr].ty.attrs.1, |attr| {
                    attr.visit_cloned(&mut Inst { subst: &ty.args, base: 0, depth })
                  })
                }
              }
              attrs.round_up_with(&self.g, &self.lc, &ty, false);
              ty.attrs.1 = attrs;
              return ty
            }
          }
        }
        panic!("type error")
      }
      ast::Type::Struct { sym, args, .. } => {
        let args = self.elab_terms_qua(args);
        let fmt =
          self.formats[&Format::Struct(FormatStruct { sym: sym.0, args: args.len() as u8 })];
        for pat in self.notations.struct_mode.iter().rev() {
          if pat.fmt == fmt {
            if let Some(subst) = pat.check_types(&self.g, &self.lc, &args) {
              let PatternKind::Struct(nr) = pat.kind else { unreachable!() };
              let mut args = subst.trim_to(self.g.constrs.struct_mode[nr].primary.len()).to_vec();
              args.iter_mut().for_each(|t| t.strip_qua_mut());
              return Type { kind: TypeKind::Struct(nr), attrs: Default::default(), args }
            }
          }
        }
        panic!("type error")
      }
      ast::Type::Cluster { attrs, ty, .. } => {
        let mut ty = self.elab_type(ty);
        let mut ty2 = ty.clone();
        attrs.iter().rev().for_each(|attr| self.elab_push_attr(attr, true, &mut ty2));
        for cl in self.g.clusters.registered.iter().rev() {
          let mut subst = Subst::new(cl.primary.len());
          if subst.eq_radices(&self.g, &self.lc, &cl.ty, &ty)
            && (ty2.attrs.0)
              .is_subset_of(&cl.ty.attrs.1, |a2, a1| subst.eq_attr(&self.g, &self.lc, a1, a2))
            && subst.check_loci_types::<false>(&self.g, &self.lc, &cl.primary, false)
          {
            let mut attrs = ty2.attrs.0.clone();
            attrs.enlarge_by(&self.g.constrs, &ty.attrs.1, Attr::clone);
            attrs.round_up_with(&self.g, &self.lc, &ty, false);
            assert!(matches!(ty2.attrs.0, Attrs::Consistent(_)));
            ty.attrs = (ty2.attrs.0, attrs);
            subst.finish();
            return ty
          }
        }
        panic!("non registered cluster")
      }
      ast::Type::Reservation { nr, subst, .. } => {
        let mut ty = self.reserved[nr.unwrap()].clone();
        if !subst.is_empty() {
          let subst = subst
            .iter()
            .map(|&(kind, nr)| match kind {
              VarKind::Free | VarKind::Reserved => Term::FreeVar(FVarId(nr)),
              VarKind::Bound => Term::Bound(BoundId(nr)),
              VarKind::Const | VarKind::DefConst => Term::Constant(ConstId(nr)),
              _ => unreachable!(),
            })
            .collect_vec();
          Inst::new(&subst).visit_type(&mut ty)
        }
        ty
      }
    }
  }

  fn elab_flex_and(&mut self, f1: &ast::Formula, f2: &ast::Formula, pos: bool) -> Formula {
    let Some(natural) = self.g.reqs.natural() else { panic!("requirement NUMERALS missing") };
    let Some(le) = self.g.reqs.less_or_equal() else { panic!("requirement REAL missing") };
    let f1 = self.elab_formula(f1, pos);
    let f2 = self.elab_formula(f2, pos);
    todo!()
  }

  fn elab_push_conjuncts(&mut self, f: &ast::Formula, conjs: &mut Vec<Formula>, pos: bool) {
    match f {
      ast::Formula::Not { f, .. } => self.elab_push_conjuncts(f, conjs, !pos),
      ast::Formula::Binop { kind: FormulaBinop::And, f1, f2, .. } if pos => {
        self.elab_push_conjuncts(f1, conjs, pos);
        self.elab_push_conjuncts(f2, conjs, pos);
      }
      ast::Formula::Binop { kind: FormulaBinop::Or, f1, f2, .. } if !pos => {
        self.elab_push_conjuncts(f1, conjs, pos);
        self.elab_push_conjuncts(f2, conjs, pos);
      }
      ast::Formula::Binop { kind: FormulaBinop::Imp, f1, f2, .. } if !pos => {
        self.elab_push_conjuncts(f1, conjs, !pos);
        self.elab_push_conjuncts(f2, conjs, pos);
      }
      _ => self.elab_formula(f, pos).append_conjuncts_to(conjs),
    }
  }

  fn elab_and(&mut self, f1: &ast::Formula, f2: &ast::Formula, pos1: bool, pos2: bool) -> Formula {
    Formula::mk_and_with(|conjs| {
      self.elab_push_conjuncts(f1, conjs, pos1);
      self.elab_push_conjuncts(f2, conjs, pos2);
    })
  }

  fn push_many_bound(&mut self, mut dom: Type, n: usize) {
    assert!(n != 0);
    for _ in 1..n {
      let base = self.lc.bound_var.len() as u32;
      let dom2 = dom.visit_cloned(&mut OnVarMut(|nr| {
        if *nr >= base {
          *nr += 1
        }
      }));
      self.lc.bound_var.push(std::mem::replace(&mut dom, dom2));
    }
    self.lc.bound_var.push(dom);
  }

  fn elab_forall(&mut self, var: &ast::BinderGroup, scope: &ast::Formula, pos: bool) -> Formula {
    self.lc.term_cache.get_mut().open_scope();
    assert!(!var.vars.is_empty());
    let dom = self.elab_type(var.ty.as_deref().unwrap());
    self.push_many_bound(dom, var.vars.len());
    let mut scope = self.elab_formula(scope, pos);
    for i in 0..var.vars.len() {
      let dom = Box::new(self.lc.bound_var.0.pop().unwrap());
      scope = Formula::ForAll { dom, scope: Box::new(scope) }
    }
    self.lc.term_cache.get_mut().close_scope();
    scope
  }

  fn elab_formula(&mut self, f: &ast::Formula, pos: bool) -> Formula {
    // vprintln!("elab_formula {pos:?} {f:?}");
    match f {
      ast::Formula::Not { f, .. } => self.elab_formula(f, !pos),
      ast::Formula::Binop { kind: FormulaBinop::And, f1, f2, .. } =>
        self.elab_and(f1, f2, true, true).maybe_neg(pos),
      ast::Formula::Binop { kind: FormulaBinop::Or, f1, f2, .. } =>
        self.elab_and(f1, f2, false, false).maybe_neg(!pos),
      ast::Formula::Binop { kind: FormulaBinop::FlexAnd, f1, f2, .. } =>
        self.elab_flex_and(f1, f2, true).maybe_neg(pos),
      ast::Formula::Binop { kind: FormulaBinop::FlexOr, f1, f2, .. } =>
        self.elab_flex_and(f1, f2, false).maybe_neg(!pos),
      ast::Formula::Binop { kind: FormulaBinop::Imp, f1, f2, .. } =>
        self.elab_and(f1, f2, true, false).maybe_neg(!pos),
      ast::Formula::Binop { kind: FormulaBinop::Iff, f1, f2, .. } =>
        self.elab_formula(f1, true).mk_iff(self.elab_formula(f2, true)).maybe_neg(pos),
      ast::Formula::Pred { pred, .. } => {
        let args = self.elab_terms_qua(&pred.args);
        let right = args.len() as u8 - pred.left;
        self.elab_pred(FormatPred { sym: pred.sym.0, left: pred.left, right }, args.into(), pos)
      }
      ast::Formula::ChainPred { first, rest, .. } => {
        let mut args = self.elab_terms_qua(&first.args).into_vec();
        let mut sym = first.sym.0;
        let mut left = first.left;
        Formula::mk_and_with(|conjs| {
          for rhs in rest {
            let mut mid: Vec<_> = args[left as usize..].into();
            let right = mid.len() as u8;
            self.elab_pred(FormatPred { sym, left, right }, args, true).append_conjuncts_to(conjs);
            mid.extend(rhs.right.iter().map(|t| self.elab_term_qua(t)));
            (args, sym, left) = (mid, rhs.sym.0, right);
          }
          let right = args.len() as u8 - left;
          self.elab_pred(FormatPred { sym, left, right }, args, true).append_conjuncts_to(conjs);
        })
        .maybe_neg(pos)
      }
      ast::Formula::PrivPred { sym, kind, args, .. } => {
        let mut args = self.elab_terms_qua(args);
        match kind {
          VarKind::PrivPred => {
            let nr = PrivPredId(sym.0);
            let def = &self.priv_pred[nr];
            assert!(agrees(&self.g, &self.lc, &args, &def.0));
            args.iter_mut().for_each(|t| t.strip_qua_mut());
            let depth = self.lc.bound_var.len() as u32;
            let value = def.1.visit_cloned(&mut Inst { subst: &args, base: 0, depth });
            Formula::PrivPred { nr, args, value }.maybe_neg(pos)
          }
          VarKind::SchPred => {
            let nr = SchPredId(sym.0);
            assert!(agrees(&self.g, &self.lc, &args, &self.sch_pred_args[nr]));
            args.iter_mut().for_each(|t| t.strip_qua_mut());
            let depth = self.lc.bound_var.len() as u32;
            Formula::SchPred { nr, args }.maybe_neg(pos)
          }
          _ => unreachable!(),
        }
      }
      ast::Formula::Attr { term, attrs, .. } => {
        let term = self.elab_term_qua(term);
        Formula::mk_and_with(|conjs| {
          for attr in attrs {
            self.elab_is_attr(attr, true, &term).append_conjuncts_to(conjs)
          }
        })
        .maybe_neg(pos)
      }
      ast::Formula::Is { term, ty, .. } =>
        Formula::Is { term: Box::new(self.elab_term(term)), ty: Box::new(self.elab_type(ty)) }
          .maybe_neg(pos),
      ast::Formula::Binder { kind: FormulaBinder::ForAll, var, scope, .. } =>
        self.elab_forall(var, scope, true).maybe_neg(pos),
      ast::Formula::Binder { kind: FormulaBinder::Exists, var, scope, .. } =>
        self.elab_forall(var, scope, false).maybe_neg(!pos),
      ast::Formula::False { .. } => Formula::True.maybe_neg(!pos),
      ast::Formula::Thesis { .. } => self.thesis.as_deref().unwrap().clone(),
    }
  }

  /// AnalizeArgTypeList
  fn elab_intern_push_locus_tys(&mut self, tys: &[ast::Type]) {
    assert!(self.lc.locus_ty.is_empty());
    for ty in tys {
      let mut ty = self.elab_type(ty);
      ty.visit(&mut self.r.intern_const());
      self.lc.locus_ty.push(ty);
    }
  }

  fn elab_intern_term(&mut self, tm: &ast::Term) -> Term {
    let mut tm = self.elab_term(tm);
    tm.visit(&mut self.r.intern_const());
    tm
  }

  fn elab_intern_type(&mut self, ty: &ast::Type) -> Type {
    let mut ty = self.elab_type(ty);
    ty.visit(&mut self.r.intern_const());
    ty
  }

  fn elab_intern_formula(&mut self, f: &ast::Formula, pos: bool) -> Formula {
    let mut f = self.elab_formula(f, pos);
    f.visit(&mut self.r.intern_const());
    f
  }

  /// replaces `f` with the normalized version,
  /// satisfying `f -> new_f` (up = true) or `new_f -> f` (up = false)
  fn whnf(&self, up: bool, mut atomic: usize, f: &mut (bool, Box<Formula>)) -> usize {
    'start: loop {
      let mut args_buf;
      let (kind, args) = match &mut *f.1 {
        Formula::Neg { f: f2 } => {
          *f = (!f.0, std::mem::take(f2));
          continue 'start
        }
        Formula::PrivPred { value, .. } | Formula::FlexAnd { expansion: value, .. } => {
          f.1 = std::mem::take(value);
          continue 'start
        }
        Formula::Pred { nr, args } if atomic > 0 => {
          let (n, args) = Formula::adjust_pred(*nr, args, &self.g.constrs);
          (ConstrKind::Pred(n), args)
        }
        Formula::Attr { nr, args } if atomic > 0 => {
          let (n, args) = Formula::adjust_attr(*nr, args, &self.g.constrs);
          (ConstrKind::Attr(n), args)
        }
        Formula::Is { term, ty } if atomic > 0 => {
          let TypeKind::Mode(n) = ty.kind else { break };
          if !matches!(&ty.attrs.0, Attrs::Consistent(attrs) if attrs.is_empty()) {
            break
          }
          args_buf = ty.args.clone();
          args_buf.push((**term).clone());
          (ConstrKind::Mode(n), &*args_buf)
        }
        _ => break,
      };
      for def in &self.definitions {
        let Some(subst) = def.matches(&self.g, &self.lc, kind, args) else { continue };
        let subst = subst.finish();
        let mut inst = Inst::new(&subst);
        let DefValue::Formula(value) = &def.value else { unreachable!() };
        let (pos2, f2) = if value.cases.is_empty() {
          (f.0, value.otherwise.as_ref().unwrap().visit_cloned(&mut inst))
        } else {
          let f = Formula::mk_and_with(|disjs| {
            let mut otherwise = vec![];
            for case in &*value.cases {
              let guard = case.guard.visit_cloned(&mut inst);
              if value.otherwise.is_some() {
                guard.clone().mk_neg().append_conjuncts_to(&mut otherwise)
              }
              let f = Formula::mk_and_with(|conj| {
                guard.append_conjuncts_to(conj);
                case.case.visit_cloned(&mut inst).maybe_neg(f.0).append_conjuncts_to(conj);
              });
              f.mk_neg().append_conjuncts_to(disjs)
            }
            if let Some(ow) = &value.otherwise {
              ow.visit_cloned(&mut inst).maybe_neg(f.0).append_conjuncts_to(&mut otherwise);
              Formula::mk_and(otherwise).mk_neg().append_conjuncts_to(disjs)
            }
          });
          (false, f)
        };
        if matches!(def.assumptions, Formula::True) {
          f.0 = pos2;
          *f.1 = f2;
        } else {
          *f.1 = Formula::mk_and_with(|conjs| {
            def.assumptions.visit_cloned(&mut inst).append_conjuncts_to(conjs);
            f2.maybe_neg(pos2 != up).append_conjuncts_to(conjs);
            f.0 = !up;
          });
        }
        atomic -= 1;
        continue 'start
      }
      break
    }
    atomic
  }

  /// ChopVars(Conclusion = !up)
  /// Attempts to instantiate `for x holds P[x]` to `P[term]`.
  /// * If `up = true` then `f -> (for x holds P[x])` (used for unfolding in hyps)
  /// * If `up = false` then `(for x holds P[x]) -> f` (unfolding thesis)
  fn inst_forall(&self, term: &Term, widenable: bool, up: bool, f: &mut (bool, Box<Formula>)) {
    self.whnf(up, MAX_EXPANSIONS, f);
    assert!(f.0, "not a forall");
    let Formula::ForAll { dom, scope } = &mut *f.1 else { panic!("not a forall") };
    let ty = term.get_type(&self.g, &self.lc, false);
    Inst0(term).visit_formula(scope);
    let ok = if !widenable {
      ().eq_type(&self.g, &self.lc, dom, &ty)
    } else if up {
      dom.is_wider_than(&self.g, &self.lc, &ty)
    } else {
      ty.is_wider_than(&self.g, &self.lc, dom)
    };
    *f.1 = if ok {
      std::mem::take(scope)
    } else {
      assert!(ty.is_wider_than(&self.g, &self.lc, dom));
      assert!(().eq_attrs(&self.g, &self.lc, &ty, dom));
      Formula::mk_and_with(|conds| {
        loop {
          conds.push(Formula::Is { term: Box::new(term.clone()), ty: dom.clone() });
          *dom = dom.widening(&self.g).unwrap();
          if ().eq_radices(&self.g, &self.lc, &ty, dom) {
            break
          }
        }
        conds.reverse();
        std::mem::take(scope).mk_neg().append_conjuncts_to(conds);
      })
      .mk_neg()
    }
  }

  /// ChopVars(Conclusion = !up)
  /// Attempts to unfold `for x1..xn holds P[x1..xn]` to `P[c1..cn]`
  /// where `c1..cn` are the fixed_vars starting at `start`.
  /// * If `up = true` then `f -> (for x1..xn holds P[x1..xn])` (used for unfolding in hyps)
  /// * If `up = false` then `(for x1..xn holds P[x1..xn]) -> f` (unfolding thesis)
  fn forall_telescope(
    &self, start: usize, widenable: bool, up: bool, f: &mut (bool, Box<Formula>),
  ) {
    for v in (start..self.lc.fixed_var.len()).map(ConstId::from_usize) {
      self.inst_forall(&Term::Constant(v), widenable, up, f)
    }
  }

  /// Chopped(Conclusion = !up)
  /// Attempts to rewrite `conjs := tgt /\ conjs2` to `conjs2`.
  /// * If `up = true` then `conjs -> tgt /\ conjs2` (used for unfolding in hyps)
  /// * If `up = false` then `tgt /\ conjs2 -> conjs` (unfolding thesis)
  fn and_telescope(
    &mut self, mut tgt: Vec<Formula>, up: bool, mut conjs: Vec<Formula>,
  ) -> Vec<Formula> {
    let mut stack1 = vec![];
    let mut stack2 = vec![];
    let mut iter1 = tgt.into_iter();
    let mut iter2 = conjs.into_iter();
    'ok: loop {
      let mut f1 = loop {
        if let Some(f1) = iter1.next() {
          if !matches!(f1, Formula::True) {
            break (true, f1)
          }
        }
        let Some(iter) = stack1.pop() else { break 'ok };
        iter1 = iter;
      };
      let f2 = loop {
        if let Some(f2) = iter2.next() {
          break f2
        }
        let Some(iter) = stack2.pop() else { break Formula::True };
        iter2 = iter;
      };
      let mut f2 = (true, Box::new(f2));
      loop {
        if f1.0 == f2.0 && ().eq_formula(&self.g, &self.lc, &f1.1, &f2.1) {
          continue 'ok
        }
        match (&mut f1.1, &mut *f2.1) {
          (Formula::And { args }, _) if f1.0 => {
            let mut iter = std::mem::take(args).into_iter();
            f1.1 = iter.next().unwrap();
            stack1.push(std::mem::replace(&mut iter1, iter));
          }
          (_, Formula::And { args }) if f2.0 => {
            let mut iter = std::mem::take(args).into_iter();
            *f2.1 = iter.next().unwrap();
            stack2.push(std::mem::replace(&mut iter2, iter));
          }
          (Formula::Neg { f }, _) => {
            f1.1 = std::mem::take(f);
            f1.0 = !f1.0;
          }
          (_, Formula::Neg { f }) => {
            f2.1 = std::mem::take(f);
            f2.0 = !f2.0;
          }
          (
            Formula::PrivPred { nr: n1, args: args1, value: v1 },
            Formula::PrivPred { nr: n2, args: args2, value: v2 },
          ) => match (*n1).cmp(n2) {
            Ordering::Less => f2.1 = std::mem::take(v2),
            Ordering::Equal => panic!("formula mismatch"),
            Ordering::Greater => f1.1 = std::mem::take(v1),
          },
          (Formula::PrivPred { value, .. }, _) => f1.1 = std::mem::take(value),
          (_, Formula::PrivPred { value, .. }) => f2.1 = std::mem::take(value),
          _ => {
            assert!(self.whnf(up, 1, &mut f2) < 1, "formula mismatch");
          }
        }
      }
    }
    iter2.chain(stack2.into_iter().rev().flatten()).collect()
  }

  fn elab_spec(&mut self, spec: Option<&ast::Type>, tgt: &Type) -> Type {
    if let Some(ty) = spec {
      let ty = self.elab_type(ty);
      assert!(tgt.is_wider_than(&self.g, &self.lc, &ty));
      ty
    } else {
      tgt.clone()
    }
  }
}

struct Exportable;

impl Visit for Exportable {
  fn visit_term(&mut self, tm: &Term) {
    match tm {
      Term::Constant(_) => panic!("local constant in exportable item"),
      Term::PrivFunc { .. } => panic!("private function in exportable item"),
      _ => self.super_visit_term(tm),
    }
  }

  fn visit_formula(&mut self, f: &Formula) {
    match f {
      Formula::PrivPred { .. } => panic!("private predicate in exportable item"),
      _ => self.super_visit_formula(f),
    }
  }
}

trait ReadProof {
  type CaseIterable;
  type CaseIter<'a>;
  type SupposeRecv;

  /// Changes the thesis from `for x1..xn holds P` to `P`
  /// where `x1..xn` are the fixed_vars introduced since `start`
  fn intro(&mut self, elab: &mut Analyzer, start: usize);

  /// Changes the thesis from `!(conj1 & ... & conjn & rest)` to `!rest`
  fn assume(&mut self, elab: &mut Analyzer, conjs: Vec<Formula>);

  /// Changes the thesis from `!(!(for x1..xn holds !f) & rest)` to `!rest`
  /// (that is, `(ex x1..xn st f) -> rest` to `rest`)
  /// where `x1..xn` are the fixed_vars introduced since `start`
  fn given(&mut self, elab: &mut Analyzer, start: usize, f: Formula);

  /// Changes the thesis from `ex x st P(x)` to `P(term)`
  fn take(&mut self, elab: &mut Analyzer, term: Term);

  /// Changes the thesis from `ex x st P(x)` to `P(v)`,
  /// where `v` is the last `fixed_var` to be introduced
  fn take_as_var(&mut self, elab: &mut Analyzer, v: ConstId) { self.take(elab, Term::Constant(v)); }

  /// Changes the thesis from `f & rest` to `rest`
  fn thus(&mut self, elab: &mut Analyzer, f: Formula);

  fn new_thesis_case(&mut self, elab: &mut Analyzer) -> Self::CaseIterable;

  fn new_thesis_case_iter<'a>(
    &mut self, elab: &mut Analyzer, case: &'a mut Self::CaseIterable,
  ) -> Self::CaseIter<'a>;

  fn next_thesis_case(&mut self, elab: &mut Analyzer, case: &mut Self::CaseIter<'_>, f: &[Formula]);

  fn finish_thesis_case(&mut self, elab: &mut Analyzer, case: Self::CaseIter<'_>);

  fn new_suppose(&mut self, elab: &mut Analyzer) -> Self::SupposeRecv;

  fn next_suppose(&mut self, elab: &mut Analyzer, recv: &mut Self::SupposeRecv) {}

  fn finish_proof(&mut self, elab: &mut Analyzer);

  fn super_elab_item(&mut self, elab: &mut Analyzer, item: &ast::Item) -> bool {
    match &item.kind {
      ast::ItemKind::Let { var } | ast::ItemKind::LetLocus { var } => {
        let n = elab.lc.fixed_var.len();
        elab.elab_fixed_vars(var);
        self.intro(elab, n)
      }
      ast::ItemKind::Assume(asm) => {
        let mut conjs = vec![];
        for prop in asm.conds() {
          elab.elab_proposition(prop).append_conjuncts_to(&mut conjs);
        }
        self.assume(elab, conjs);
      }
      ast::ItemKind::Given { vars, conds } => {
        let n = elab.lc.fixed_var.len();
        for var in vars {
          elab.elab_fixed_vars(var);
        }
        let f = Formula::mk_and_with(|conjs| {
          conds.iter().for_each(|prop| elab.elab_proposition(prop).append_conjuncts_to(conjs))
        });
        self.given(elab, n, f);
      }
      ast::ItemKind::Take { var: None, term } => {
        let term = elab.elab_intern_term(term.as_deref().unwrap());
        self.take(elab, term);
      }
      ast::ItemKind::Take { var: Some(_), term } => {
        let term = elab.elab_intern_term(term.as_deref().unwrap());
        let ty = term.get_type(&elab.g, &elab.lc, false);
        let v = elab.lc.fixed_var.push(FixedVar { ty, def: Some(Box::new(term)) });
        self.take_as_var(elab, v);
      }
      ast::ItemKind::Thus(stmt) => {
        let f = elab.elab_stmt(stmt);
        self.thus(elab, f)
      }
      ast::ItemKind::PerCases { just, kind: CaseKind::Case, blocks } => {
        let mut iter = self.new_thesis_case(elab);
        let mut iter = self.new_thesis_case_iter(elab, &mut iter);
        let f = Formula::mk_and_with(|disjs| {
          for bl in blocks {
            elab.scope(None, true, false, |elab| {
              let f = Formula::mk_and_with(|conjs| {
                for prop in bl.hyp.conds() {
                  elab.elab_proposition(prop).append_conjuncts_to(conjs);
                }
                self.next_thesis_case(elab, &mut iter, conjs);
              });
              f.mk_neg().append_conjuncts_to(disjs);
              self.elab_proof(elab, &bl.items);
            });
          }
          self.finish_thesis_case(elab, iter);
        });
        elab.elab_justification(&f.mk_neg(), just);
        return false
      }
      ast::ItemKind::PerCases { just, kind: CaseKind::Suppose, blocks } => {
        let f = Formula::mk_and_with(|disjs| {
          let mut recv = self.new_suppose(elab);
          for bl in blocks {
            elab.scope(None, true, false, |elab| {
              let f = Formula::mk_and_with(|conjs| {
                for prop in bl.hyp.conds() {
                  elab.elab_proposition(prop).append_conjuncts_to(conjs);
                }
              });
              f.mk_neg().append_conjuncts_to(disjs);
              self.elab_proof(elab, &bl.items);
              self.next_suppose(elab, &mut recv);
            });
          }
        });
        elab.elab_justification(&f.mk_neg(), just);
        return false
      }
      _ => elab.elab_stmt_item(item),
    }
    true
  }

  fn elab_item(&mut self, elab: &mut Analyzer, item: &ast::Item) -> bool {
    self.super_elab_item(elab, item)
  }

  fn elab_proof(&mut self, elab: &mut Analyzer, items: &[ast::Item]) {
    for item in items {
      if !self.elab_item(elab, item) {
        break
      }
    }
    self.finish_proof(elab)
  }
}

struct CorrConds(EnumMap<CorrCondKind, Option<Box<Formula>>>);

impl CorrConds {
  const fn new() -> Self { Self(EnumMap::from_array([None, None, None, None, None, None])) }
}

struct AbstractIt(u32, u32);
impl AbstractIt {
  fn forall(it_type: &Type, mut f: Formula, pos: bool) -> Formula {
    AbstractIt(0, 1).visit_formula(&mut f);
    Formula::ForAll { dom: Box::new(it_type.clone()), scope: Box::new(f.maybe_neg(pos)) }
  }
}

impl VisitMut for AbstractIt {
  fn visit_term(&mut self, tm: &mut Term) {
    match tm {
      Term::Bound(n) => n.0 += self.1,
      Term::It => *tm = Term::Bound(BoundId(self.0)),
      _ => self.super_visit_term(tm),
    }
  }
}

struct AbstractLocus(u32);
impl VisitMut for AbstractLocus {
  fn visit_term(&mut self, tm: &mut Term) {
    match tm {
      Term::Bound(n) => n.0 += self.0,
      Term::Constant(_) => panic!("unexpected local constant"),
      Term::Locus(LocusId(n)) => *tm = Term::Bound(BoundId(*n as _)),
      Term::It => *tm = Term::Bound(BoundId(self.0 - 1)),
      _ => self.super_visit_term(tm),
    }
  }
}

pub trait BodyKind {
  fn it_eq(&self, g: &Global) -> Formula;
  fn mk_eq(&self, g: &Global, other: &Self) -> Formula;
}
impl BodyKind for Term {
  fn it_eq(&self, g: &Global) -> Formula { g.reqs.mk_eq(Term::It, self.clone()) }
  fn mk_eq(&self, g: &Global, other: &Self) -> Formula { g.reqs.mk_eq(self.clone(), other.clone()) }
}
impl BodyKind for Formula {
  fn it_eq(&self, _: &Global) -> Formula { self.clone() }
  fn mk_eq(&self, g: &Global, other: &Self) -> Formula { self.clone().mk_iff(other.clone()) }
}

impl<T: BodyKind> DefBody<T> {
  fn mk_consistency(&self, g: &Global, it_type: Option<&Type>) -> Option<Box<Formula>> {
    if self.cases.is_empty() {
      return None
    }
    let f = Formula::mk_and_with(|conjs| {
      for (i, j) in self.cases.iter().tuple_combinations() {
        let f = Formula::mk_and_with(|disj| {
          i.guard.clone().append_conjuncts_to(disj);
          j.guard.clone().append_conjuncts_to(disj);
          i.case.it_eq(g).mk_iff(j.case.it_eq(g)).mk_neg().append_conjuncts_to(disj);
        });
        f.mk_neg().append_conjuncts_to(conjs);
      }
    });
    Some(Box::new(match it_type {
      Some(it_type) => AbstractIt::forall(it_type, f, true),
      None => f,
    }))
  }

  fn by_cases(&self, neg_f: impl Fn(&T) -> Formula) -> Box<Formula> {
    let mut els = self.otherwise.as_ref().map(|_| vec![]);
    Box::new(Formula::mk_and_with(|conjs| {
      for def in &*self.cases {
        let f = Formula::mk_and_with(|disj| {
          def.guard.clone().append_conjuncts_to(disj);
          neg_f(&def.case).append_conjuncts_to(disj);
        });
        f.mk_neg().append_conjuncts_to(conjs);
        if let Some(els) = &mut els {
          def.guard.clone().mk_neg().append_conjuncts_to(els)
        }
      }
      if let (Some(mut els), Some(ow)) = (els, &self.otherwise) {
        neg_f(ow).append_conjuncts_to(&mut els);
        Formula::mk_and(els).mk_neg().append_conjuncts_to(conjs)
      }
    }))
  }

  fn iffthm_for(&self, g: &Global, defines: &Formula) -> Box<Formula> {
    self.by_cases(|case| defines.clone().mk_iff(case.it_eq(g)).mk_neg())
  }

  fn defthm_for(&self, g: &Global, defines: &T) -> Box<Formula> {
    self.by_cases(|case| defines.mk_eq(g, case).mk_neg())
  }

  fn mk_compatibility(
    &self, g: &Global, it_type: Option<&Type>, defines: &Formula,
  ) -> Box<Formula> {
    let mut f = self.iffthm_for(g, defines);
    if let Some(it_type) = it_type {
      *f = AbstractIt::forall(it_type, std::mem::take(&mut *f), true)
    }
    f
  }
}

impl DefBody<Formula> {
  fn mk_existence(&self, it_type: &Type) -> Box<Formula> {
    self.by_cases(|case| AbstractIt::forall(it_type, case.clone(), false))
  }

  fn mk_uniqueness(&self, g: &Global, it_type: &Type) -> Box<Formula> {
    let scope = self.by_cases(|case| {
      Formula::mk_and_with(|conjs| {
        case.visit_cloned(&mut AbstractIt(0, 2)).append_conjuncts_to(conjs);
        case.visit_cloned(&mut AbstractIt(1, 2)).append_conjuncts_to(conjs);
        conjs.push(g.reqs.mk_eq(Term::Bound(BoundId(0)), Term::Bound(BoundId(1))).mk_neg())
      })
    });
    let it_type2 = it_type.visit_cloned(&mut AbstractIt(0, 1));
    let scope = Box::new(Formula::ForAll { dom: Box::new(it_type2), scope });
    Box::new(Formula::ForAll { dom: Box::new(it_type.clone()), scope })
  }
}

impl DefBody<Term> {
  fn mk_coherence(&self, it_type: &Type) -> Box<Formula> {
    self.by_cases(|case| {
      Formula::Is { term: Box::new(case.clone()), ty: Box::new(it_type.clone()) }.mk_neg()
    })
  }
}

fn mk_mode_coherence(nr: ModeId, attrs: &Attrs, args: &[Term], it_type: &Type) -> Box<Formula> {
  Box::new(Formula::ForAll {
    dom: Box::new(Type {
      kind: TypeKind::Mode(nr),
      attrs: (Attrs::EMPTY, attrs.visit_cloned(&mut Inst::new(args))),
      args: args.into(),
    }),
    scope: Box::new(Formula::Is {
      term: Box::new(Term::Bound(BoundId(0))),
      ty: Box::new(it_type.clone()),
    }),
  })
}

fn mk_func_coherence(nr: FuncId, args: &[Term], it_type: &Type) -> Box<Formula> {
  Box::new(Formula::Is {
    term: Box::new(Term::Functor { nr, args: args.to_vec().into() }),
    ty: Box::new(it_type.clone()),
  })
}

impl DefValue {
  fn mk_consistency(&self, g: &Global, it_type: Option<&Type>) -> Option<Box<Formula>> {
    match self {
      DefValue::Term(value) => value.mk_consistency(g, it_type),
      DefValue::Formula(value) => value.mk_consistency(g, it_type),
    }
  }

  fn mk_compatibility(
    &self, g: &Global, it_type: Option<&Type>, defines: &Formula,
  ) -> Box<Formula> {
    match self {
      DefValue::Term(value) => value.mk_compatibility(g, it_type, defines),
      DefValue::Formula(value) => value.mk_compatibility(g, it_type, defines),
    }
  }
}

struct WithThesis;

impl ReadProof for WithThesis {
  type CaseIterable = Formula;
  type CaseIter<'a> = std::slice::Iter<'a, Formula>;
  type SupposeRecv = ();

  fn intro(&mut self, elab: &mut Analyzer, start: usize) {
    let mut thesis = (true, elab.thesis.take().unwrap());
    elab.forall_telescope(start, false, false, &mut thesis);
    elab.thesis = Some(Box::new(thesis.1.maybe_neg(thesis.0)));
  }

  fn assume(&mut self, elab: &mut Analyzer, conjs: Vec<Formula>) {
    let thesis = elab.thesis.take().unwrap().mk_neg().into_conjuncts();
    elab.thesis = Some(Box::new(Formula::mk_and(elab.and_telescope(conjs, true, thesis)).mk_neg()))
  }

  fn given(&mut self, elab: &mut Analyzer, start: usize, f: Formula) {
    let mut f = f.mk_neg();
    let end = elab.lc.fixed_var.len();
    elab.lc.mk_forall(start..end, false, &mut f);
    self.assume(elab, vec![f.mk_neg()]);
  }

  fn take(&mut self, elab: &mut Analyzer, term: Term) {
    let mut thesis = (false, elab.thesis.take().unwrap());
    elab.inst_forall(&term, true, true, &mut thesis);
    elab.thesis = Some(Box::new(thesis.1.maybe_neg(!thesis.0)));
  }

  fn thus(&mut self, elab: &mut Analyzer, f: Formula) {
    let thesis = elab.thesis.take().unwrap().into_conjuncts();
    elab.thesis =
      Some(Box::new(Formula::mk_and(elab.and_telescope(f.into_conjuncts(), false, thesis))))
  }

  fn new_thesis_case(&mut self, elab: &mut Analyzer) -> Formula {
    elab.thesis.as_ref().unwrap().clone().mk_neg()
  }

  fn new_thesis_case_iter<'a>(
    &mut self, elab: &mut Analyzer, case: &'a mut Formula,
  ) -> Self::CaseIter<'a> {
    case.conjuncts().iter()
  }

  fn next_thesis_case(
    &mut self, elab: &mut Analyzer, case: &mut Self::CaseIter<'_>, f: &[Formula],
  ) {
    elab.thesis = Some(Box::new(case.next().cloned().unwrap_or(Formula::True).mk_neg()));
    self.assume(elab, f.to_vec())
  }

  fn finish_thesis_case(&mut self, elab: &mut Analyzer, mut case: Self::CaseIter<'_>) {
    assert!(case.next().is_none())
  }

  fn new_suppose(&mut self, _: &mut Analyzer) {}

  fn finish_proof(&mut self, elab: &mut Analyzer) {
    assert!(matches!(elab.thesis.as_deref(), Some(Formula::True)))
  }
}

enum ProofStep {
  Let { range: Range<usize> },
  Assume { conjs: Vec<Formula> },
  Given { range: Range<usize>, not_f: Formula },
  TakeAsVar { range: Range<usize> },
  Thus { conjs: Vec<Formula> },
  Case,
}

#[derive(Default)]
struct ReconstructThesis {
  stack: Vec<ProofStep>,
}

impl ReconstructThesis {
  fn reconstruct(&mut self, elab: &mut Analyzer, pos: bool) -> Formula {
    struct Reconstruction {
      pos: bool,
      conjs: Vec<Formula>,
    }
    impl Reconstruction {
      fn as_pos(&mut self, pos: bool) -> &mut Vec<Formula> {
        if self.pos != pos {
          self.pos = pos;
          self.conjs = vec![Formula::mk_and(std::mem::take(&mut self.conjs)).mk_neg()];
        }
        &mut self.conjs
      }
    }
    let mut rec = Reconstruction { pos, conjs: vec![] };
    while let Some(step) = self.stack.pop() {
      match step {
        ProofStep::Let { range } => {
          let mut f = Formula::mk_and(std::mem::take(rec.as_pos(true)));
          elab.lc.mk_forall(range, true, &mut f);
          rec.conjs = vec![f];
        }
        ProofStep::Assume { mut conjs } => {
          let rest = rec.as_pos(false);
          std::mem::swap(&mut conjs, rest);
          rest.append(&mut conjs)
        }
        ProofStep::Given { range, mut not_f } => {
          let rest = rec.as_pos(false);
          elab.lc.mk_forall(range, true, &mut not_f);
          rest.insert(0, not_f.mk_neg())
        }
        ProofStep::TakeAsVar { range } => {
          let mut f = Formula::mk_and(std::mem::take(rec.as_pos(false)));
          elab.lc.mk_forall(range, true, &mut f);
          rec.conjs = vec![f];
        }
        ProofStep::Thus { mut conjs } => {
          let rest = rec.as_pos(true);
          std::mem::swap(&mut conjs, rest);
          rest.append(&mut conjs)
        }
        ProofStep::Case => return Formula::mk_and(std::mem::take(rec.as_pos(false))),
      }
    }
    return Formula::mk_and(std::mem::take(rec.as_pos(true)))
  }
}

impl ReadProof for ReconstructThesis {
  type CaseIterable = ();
  type CaseIter<'a> = ();
  type SupposeRecv = Option<Box<Formula>>;

  fn intro(&mut self, elab: &mut Analyzer, start: usize) {
    match self.stack.last_mut() {
      Some(ProofStep::Let { range }) if range.end == start => range.end = elab.lc.fixed_var.len(),
      _ => self.stack.push(ProofStep::Let { range: start..elab.lc.fixed_var.len() }),
    }
  }

  fn assume(&mut self, elab: &mut Analyzer, mut conjs: Vec<Formula>) {
    if let Some(ProofStep::Assume { conjs: rest }) = self.stack.last_mut() {
      rest.append(&mut conjs)
    } else {
      self.stack.push(ProofStep::Assume { conjs })
    }
  }

  fn given(&mut self, elab: &mut Analyzer, start: usize, f: Formula) {
    self.stack.push(ProofStep::Given { range: start..elab.lc.fixed_var.len(), not_f: f.mk_neg() })
  }

  fn take(&mut self, _: &mut Analyzer, _: Term) { panic!("take steps are not reconstructible") }

  fn take_as_var(&mut self, elab: &mut Analyzer, v: ConstId) {
    if !matches!(self.stack.last(), Some(ProofStep::TakeAsVar { .. })) {
      self.stack.push(ProofStep::TakeAsVar { range: v.0 as usize..elab.lc.fixed_var.len() })
    }
  }

  fn thus(&mut self, elab: &mut Analyzer, f: Formula) {
    if let Some(ProofStep::Thus { conjs }) = self.stack.last_mut() {
      conjs.push(f)
    } else {
      self.stack.push(ProofStep::Thus { conjs: vec![f] })
    }
  }

  fn new_thesis_case(&mut self, elab: &mut Analyzer) {}
  fn new_thesis_case_iter(&mut self, _: &mut Analyzer, _: &mut ()) {}
  fn next_thesis_case(&mut self, _: &mut Analyzer, _: &mut (), conjs: &[Formula]) {
    self.stack.push(ProofStep::Case);
    self.stack.push(ProofStep::Thus { conjs: conjs.to_vec() });
  }
  fn finish_thesis_case(&mut self, elab: &mut Analyzer, _: ()) {
    let f = self.reconstruct(elab, false);
    self.assume(elab, vec![f]);
  }

  fn new_suppose(&mut self, _: &mut Analyzer) -> Self::SupposeRecv { Default::default() }

  fn next_suppose(&mut self, elab: &mut Analyzer, recv: &mut Self::SupposeRecv) {
    if let Some(thesis) = recv {
      assert!(().eq_formula(&elab.g, &elab.lc, thesis, elab.thesis.as_ref().unwrap()))
    } else {
      *recv = Some(elab.thesis.take().unwrap())
    }
  }

  fn finish_proof(&mut self, elab: &mut Analyzer) {
    elab.thesis = Some(Box::new(self.reconstruct(elab, true)))
  }
}

#[derive(Default)]
struct ToLocus(IdxVec<ConstId, Option<LocusId>>);

impl ToLocus {
  fn get(&self, c: ConstId) -> LocusId {
    self.0.get(c).and_then(|l| *l).expect("local constant in exported item")
  }
}

impl VisitMut for ToLocus {
  fn visit_term(&mut self, tm: &mut Term) {
    match *tm {
      Term::Constant(c) => *tm = Term::Locus(self.get(c)),
      _ => self.super_visit_term(tm),
    }
  }
}

struct MakeSelector {
  base: u8,
  terms: Vec<Result<Box<Term>, SelId>>,
}

impl VisitMut for MakeSelector {
  fn visit_term(&mut self, tm: &mut Term) {
    if let Term::Locus(n) = tm {
      if let Some(i) = n.0.checked_sub(self.base) {
        *tm = match self.terms[i as usize] {
          Ok(ref t) => (**t).clone(),
          Err(nr) =>
            Term::Selector { nr, args: (0..=self.base).map(LocusId).map(Term::Locus).collect() },
        }
      }
    } else {
      self.super_visit_term(tm)
    }
  }
}

struct BlockReader {
  kind: BlockKind,
  to_locus: ToLocus,
  primary: IdxVec<LocusId, Type>,
  assums: Vec<Formula>,
  defthms: Vec<(Option<LabelId>, Box<Formula>)>,
}

struct CheckAccess(IdxVec<LocusId, bool>);
impl CheckAccess {
  fn check(primary: &[Type], visible: &[LocusId]) {
    let mut occ = Self(IdxVec::from_default(primary.len()));
    visible.iter().for_each(|&v| occ.0[v] = true);
    for (i, ty) in primary.iter().enumerate().rev() {
      assert!(occ.0[LocusId::from_usize(i)]);
      occ.visit_type(ty)
    }
  }
}

impl Visit for CheckAccess {
  fn visit_term(&mut self, tm: &Term) {
    match *tm {
      Term::Locus(i) => self.0[i] = true,
      _ => self.super_visit_term(tm),
    }
  }
}

impl BlockReader {
  fn new(kind: BlockKind, lc: &LocalContext) -> Self {
    Self {
      kind,
      to_locus: ToLocus(IdxVec::from_default(lc.fixed_var.len())),
      primary: Default::default(),
      assums: vec![],
      defthms: vec![],
    }
  }

  fn after_scope(self, elab: &mut Analyzer) {
    for (label, thm) in self.defthms {
      let thm = elab.intern(&thm);
      elab.push_prop(label, *thm)
    }
  }

  fn forall_locus(&self, mut f: Box<Formula>) -> Box<Formula> {
    let mut al = AbstractLocus(self.primary.len() as u32);
    if !self.assums.is_empty() {
      let f2 = f.mk_neg();
      *f = Formula::mk_and_with(|conjs| {
        conjs.extend(self.assums.iter().map(|f| f.visit_cloned(&mut al)));
        f2.append_conjuncts_to(conjs);
      })
    }
    for ty in self.primary.0.iter().rev() {
      al.0 -= 1;
      f = Box::new(Formula::ForAll { dom: Box::new(ty.visit_cloned(&mut al)), scope: f })
    }
    f
  }

  fn check_compatible_args(&self, subst: &Subst<'_>) {
    let n = self.primary.len().checked_sub(subst.subst_term.len()).expect("too many args");
    for ((i, ty), tm) in self.primary.enum_iter().skip(n).zip(&*subst.subst_term) {
      if let Some(tm) = tm {
        if let Term::Constant(c) = **tm {
          if self.to_locus.get(c) == i {
            continue
          }
        }
      }
      panic!("incorrect args to redefinition")
    }
  }

  fn elab_func_def(
    &mut self, elab: &mut Analyzer, pat: &ast::PatternFunc, it: &ast::Definition,
    spec: &Option<Box<ast::Type>>, def: Option<&ast::Definiens>,
  ) {
    let fmt = elab.formats[&Format::Func(pat.to_format())];
    let mut cc = CorrConds::new();
    let primary: Box<[_]> = self.primary.0.iter().cloned().collect();
    let visible: Box<[_]> = pat.args().iter().map(|v| self.to_locus.get(ConstId(v.id.0))).collect();
    let mut args: Box<[_]> = Box::new([]);
    let (redefines, superfluous, it_type, mut properties, arg1, arg2);
    if it.redef {
      args = pat.args().iter().map(|v| Term::Constant(ConstId(v.id.0))).collect();
      let pat = elab.notations.functor.iter().rev().find(|pat| {
        pat.fmt == fmt
          && !matches!(pat.kind, PatternKind::Func(nr)
            if elab.g.constrs.functor[nr].redefines.is_some())
          && matches!(pat.check_types(&elab.g, &elab.lc, &args),
            Some(subst) if { self.check_compatible_args(&subst); true })
      });
      let pat = pat.expect("type error");
      let PatternKind::Func(nr) = pat.kind else { unreachable!() };
      (redefines, superfluous) = (Some(nr), (self.primary.len() - pat.primary.len()) as u8);
      let c = &elab.g.constrs.functor[nr];
      (properties, arg1, arg2) = (c.properties, c.arg1 + superfluous, c.arg2 + superfluous);
      it_type = elab.elab_spec(spec.as_deref(), &c.ty.clone());
      if spec.is_some() {
        cc.0[CorrCondKind::Coherence] =
          Some(mk_func_coherence(nr, &args[superfluous as usize..], &it_type));
      }
    } else {
      (redefines, superfluous) = (None, 0);
      it_type = spec.as_deref().map_or(Type::ANY, |ty| elab.elab_type(ty));
      (properties, arg1, arg2) = Default::default();
    }
    elab.lc.it_type = Some(Box::new(it_type));
    let value = def.as_ref().map(|def| elab.elab_def_value(&def.kind, true));
    let mut it_type = elab.lc.it_type.take().unwrap();
    if let Some(value) = &value {
      cc.0[CorrCondKind::Consistency] = value.mk_consistency(&elab.g, Some(&it_type));
      if let Some(nr) = redefines {
        let defined = Term::Functor { nr, args }.it_eq(&elab.g);
        cc.0[CorrCondKind::Compatibility] =
          Some(value.mk_compatibility(&elab.g, Some(&it_type), &defined));
      }
    }
    if !it.redef {
      match value.as_ref().unwrap() {
        DefValue::Term(value) => cc.0[CorrCondKind::Coherence] = Some(value.mk_coherence(&it_type)),
        DefValue::Formula(value) => {
          cc.0[CorrCondKind::Existence] = Some(value.mk_existence(&it_type));
          cc.0[CorrCondKind::Uniqueness] = Some(value.mk_uniqueness(&elab.g, &it_type));
        }
      }
    }
    elab.elab_corr_conds(cc, &it.conds, &it.corr);
    elab.elab_properties(&it.props, &mut properties);
    it_type.visit(&mut self.to_locus);
    CheckAccess::check(&primary, &visible);
    let n;
    if value.is_some() || superfluous != 0 || !it.props.is_empty() {
      let primary = primary.clone();
      n = elab.g.constrs.functor.push(TyConstructor {
        c: Constructor { primary, redefines, superfluous, properties, arg1, arg2 },
        ty: (*it_type).clone(),
      });
      elab.push_constr(ConstrKind::Func(n));
      if let Some(mut value) = value {
        value.visit(&mut self.to_locus);
        let formals: Box<[_]> = self.primary.enum_iter().map(|(i, _)| Term::Locus(i)).collect();
        let primary: Box<[_]> = self.primary.0.iter().chain([&*it_type]).cloned().collect();
        it_type.visit(&mut Inst::new(&formals));
        let defined = Term::Functor { nr: n, args: formals };
        let depth = self.primary.len() as u32;
        let mut f;
        match &value {
          DefValue::Term(value) => {
            f = value.defthm_for(&elab.g, &defined);
            AbstractLocus(depth).visit_formula(&mut f);
          }
          DefValue::Formula(value) => {
            f = value.iffthm_for(&elab.g, &defined.it_eq(&elab.g));
            AbstractLocus(depth + 1).visit_formula(&mut f);
            AbstractLocus(depth).visit_type(&mut it_type);
            f = Box::new(Formula::ForAll { dom: it_type, scope: f });
          }
        };
        let thm = self.forall_locus(f);
        self.defthms.push((def.as_ref().unwrap().label.as_ref().map(|l| l.id.0), thm));
        elab.r.read_definiens(&Definiens {
          essential: (superfluous..primary.len() as u8).map(LocusId).collect(),
          c: ConstrDef { constr: ConstrKind::Func(n), primary },
          assumptions: Formula::mk_and(self.assums.clone()),
          value,
        });
      }
    } else {
      n = redefines.unwrap()
    }
    let pat = Pattern {
      kind: PatternKind::Func(n),
      fmt,
      redefines: redefines.map(|x| x.0),
      primary,
      visible,
      pos: true,
    };
    elab.r.lc.formatter.push(&elab.r.g.constrs, &pat);
    elab.r.notations.functor.push(pat)
  }

  fn elab_pred_def(
    &mut self, elab: &mut Analyzer, pat: &ast::PatternPred, it: &ast::Definition,
    def: Option<&ast::Definiens>,
  ) {
    let fmt = elab.formats[&Format::Pred(pat.to_format())];
    let mut cc = CorrConds::new();
    let primary: Box<[_]> = self.primary.0.iter().cloned().collect();
    let visible: Box<[_]> = pat.args.iter().map(|v| self.to_locus.get(ConstId(v.id.0))).collect();
    let mut args: Box<[_]> = Box::new([]);
    let (redefines, superfluous, pos, mut properties, arg1, arg2);
    if it.redef {
      args = pat.args.iter().map(|v| Term::Constant(ConstId(v.id.0))).collect();
      let pat = elab.notations.predicate.iter().rev().find(|pat| {
        pat.fmt == fmt
          && !matches!(pat.kind, PatternKind::Pred(nr)
            if elab.g.constrs.predicate[nr].redefines.is_some())
          && matches!(pat.check_types(&elab.g, &elab.lc, &args),
            Some(subst) if { self.check_compatible_args(&subst); true })
      });
      let pat = pat.expect("type error");
      let PatternKind::Pred(nr) = pat.kind else { unreachable!() };
      let c = &elab.g.constrs.predicate[nr];
      (redefines, superfluous, pos) =
        (Some(nr), (self.primary.len() - pat.primary.len()) as u8, pat.pos);
      (properties, arg1, arg2) = (c.properties, c.arg1 + superfluous, c.arg2 + superfluous)
    } else {
      (redefines, superfluous, pos) = (None, 0, true);
      (properties, arg1, arg2) = Default::default();
    }
    let value = def.as_ref().map(|def| elab.elab_def_value(&def.kind, pos));
    if let Some(value) = &value {
      cc.0[CorrCondKind::Consistency] = value.mk_consistency(&elab.g, None);
      if let Some(nr) = redefines {
        cc.0[CorrCondKind::Compatibility] =
          Some(value.mk_compatibility(&elab.g, None, &Formula::Pred { nr, args }));
      }
    }
    elab.elab_corr_conds(cc, &it.conds, &it.corr);
    elab.elab_properties(&it.props, &mut properties);
    CheckAccess::check(&primary, &visible);
    let n;
    if superfluous != 0 || !it.props.is_empty() {
      let p = primary.clone();
      let c = Constructor { primary: p, redefines, superfluous, properties, arg1, arg2 };
      n = elab.g.constrs.predicate.push(c);
      elab.push_constr(ConstrKind::Pred(n));
      if let Some(mut value) = value {
        let DefValue::Formula(mut value) = value else { unreachable!() };
        value.visit(&mut self.to_locus);
        let formals = self.primary.enum_iter().map(|(i, _)| Term::Locus(i)).collect();
        let mut f = value.defthm_for(&elab.g, &Formula::Pred { nr: n, args: formals });
        AbstractLocus(self.primary.len() as u32).visit_formula(&mut f);
        let thm = self.forall_locus(f);
        self.defthms.push((def.as_ref().unwrap().label.as_ref().map(|l| l.id.0), thm));
        elab.r.read_definiens(&Definiens {
          essential: (superfluous..primary.len() as u8).map(LocusId).collect(),
          c: ConstrDef { constr: ConstrKind::Pred(n), primary: primary.clone() },
          assumptions: Formula::mk_and(self.assums.clone()),
          value: DefValue::Formula(value),
        });
      }
    } else {
      n = redefines.unwrap()
    }
    let pat = Pattern {
      kind: PatternKind::Pred(n),
      fmt,
      redefines: redefines.map(|x| x.0),
      primary,
      visible,
      pos,
    };
    elab.r.lc.formatter.push(&elab.r.g.constrs, &pat);
    elab.r.notations.predicate.push(pat)
  }

  fn elab_mode_def(
    &mut self, elab: &mut Analyzer, pat: &ast::PatternMode, kind: &ast::DefModeKind,
    it: &ast::Definition,
  ) {
    let fmt = elab.formats[&Format::Mode(pat.to_format())];
    let mut cc = CorrConds::new();
    let mut properties = Default::default();
    let primary: Box<[_]> = self.primary.0.iter().cloned().collect();
    let visible = pat.args.iter().map(|v| self.to_locus.get(ConstId(v.id.0))).collect();
    match kind {
      ast::DefModeKind::Expandable { expansion } => {
        let mut expansion = Box::new(elab.elab_type(expansion));
        elab.elab_corr_conds(cc, &it.conds, &it.corr);
        elab.elab_properties(&it.props, &mut properties);
        expansion.visit(&mut self.to_locus);
        let pat = Pattern {
          kind: PatternKind::ExpandableMode { expansion },
          fmt,
          redefines: None,
          primary,
          visible,
          pos: true,
        };
        CheckAccess::check(&pat.primary, &pat.visible);
        elab.r.lc.formatter.push(&elab.r.g.constrs, &pat);
        elab.r.notations.mode.push(pat)
      }
      ast::DefModeKind::Standard { spec, def } => {
        let mut args: Box<[_]> = Box::new([]);
        let (redefines, superfluous, it_type);
        if it.redef {
          args = pat.args.iter().map(|v| Term::Constant(ConstId(v.id.0))).collect();
          let pat = elab.notations.mode.iter().rev().find(|pat| {
            pat.fmt == fmt
              && !matches!(pat.kind, PatternKind::Mode(nr)
              if elab.g.constrs.mode[nr].redefines.is_some())
              && matches!(pat.check_types(&elab.g, &elab.lc, &args),
              Some(subst) if { self.check_compatible_args(&subst); true })
          });
          let pat = pat.expect("type error");
          let PatternKind::Mode(nr) = pat.kind else { panic!("redefining expandable mode") };
          (redefines, superfluous) = (Some(nr), (self.primary.len() - pat.primary.len()) as u8);
          let tgt = elab.g.constrs.mode[nr].ty.clone();
          if elab.g.constrs.mode[nr].properties.get(PropertyKind::Sethood) {
            properties.set(PropertyKind::Sethood)
          }
          it_type = elab.elab_spec(spec.as_deref(), &tgt);
          if spec.is_some() {
            let args2 = &args[superfluous as usize..];
            cc.0[CorrCondKind::Coherence] =
              Some(mk_mode_coherence(nr, &tgt.attrs.1, args2, &it_type));
          }
        } else {
          (redefines, superfluous) = (None, 0);
          it_type = spec.as_deref().map_or(Type::ANY, |ty| elab.elab_type(ty));
        }
        elab.lc.it_type = Some(Box::new(it_type));
        let value = def.as_ref().map(|def| elab.elab_def_value(&def.kind, true));
        let mut it_type = elab.lc.it_type.take().unwrap();
        if let Some(value) = &value {
          cc.0[CorrCondKind::Consistency] = value.mk_consistency(&elab.g, Some(&it_type));
          if let Some(nr) = redefines {
            let ty = Box::new(Type {
              kind: TypeKind::Mode(nr),
              attrs: (Attrs::EMPTY, it_type.attrs.1.clone()),
              args: (*args).to_owned(),
            });
            let defined = Formula::Is { term: Box::new(Term::It), ty };
            cc.0[CorrCondKind::Compatibility] =
              Some(value.mk_compatibility(&elab.g, Some(&it_type), &defined));
          }
        }
        if !it.redef {
          let Some(DefValue::Formula(value)) = &value else { panic!() };
          cc.0[CorrCondKind::Existence] = Some(value.mk_existence(&it_type));
        }
        if let TypeKind::Mode(nr) = it_type.kind {
          if elab.g.constrs.mode[nr].properties.get(PropertyKind::Sethood) {
            properties.set(PropertyKind::Sethood)
          }
        }
        elab.elab_corr_conds(cc, &it.conds, &it.corr);
        elab.elab_properties(&it.props, &mut properties);
        it_type.visit(&mut self.to_locus);
        CheckAccess::check(&primary, &visible);
        let n;
        if value.is_some() || superfluous != 0 {
          let primary = primary.clone();
          n = elab.g.constrs.mode.push(TyConstructor {
            c: Constructor { primary, redefines, superfluous, properties, arg1: 0, arg2: 0 },
            ty: (*it_type).clone(),
          });
          elab.push_constr(ConstrKind::Mode(n));
          if let Some(mut value) = value {
            let DefValue::Formula(mut value) = value else { unreachable!() };
            value.visit(&mut self.to_locus);
            let formals = self.primary.enum_iter().map(|(i, _)| Term::Locus(i)).collect_vec();
            let primary: Box<[_]> = self.primary.0.iter().chain([&*it_type]).cloned().collect();
            it_type.visit(&mut Inst::new(&formals));
            let ty = Box::new(Type {
              kind: TypeKind::Mode(n),
              attrs: (Attrs::EMPTY, it_type.attrs.1.clone()),
              args: formals,
            });
            let defined = Formula::Is { term: Box::new(Term::It), ty };
            let mut f = value.defthm_for(&elab.g, &defined);
            let depth = self.primary.len() as u32;
            AbstractLocus(depth + 1).visit_formula(&mut f);
            AbstractLocus(depth).visit_type(&mut it_type);
            let thm = self.forall_locus(Box::new(Formula::ForAll { dom: it_type, scope: f }));
            self.defthms.push((def.as_ref().unwrap().label.as_ref().map(|l| l.id.0), thm));
            elab.r.read_definiens(&Definiens {
              essential: (superfluous..primary.len() as u8).map(LocusId).collect(),
              c: ConstrDef { constr: ConstrKind::Mode(n), primary },
              assumptions: Formula::mk_and(self.assums.clone()),
              value: DefValue::Formula(value),
            });
          }
        } else {
          n = redefines.unwrap()
        }
        let pat = Pattern {
          kind: PatternKind::Mode(n),
          fmt,
          redefines: redefines.map(|x| x.0),
          primary,
          visible,
          pos: true,
        };
        elab.r.lc.formatter.push(&elab.r.g.constrs, &pat);
        elab.r.notations.mode.push(pat)
      }
    }
  }

  fn elab_attr_def(
    &mut self, elab: &mut Analyzer, pat: &ast::PatternAttr, it: &ast::Definition,
    def: Option<&ast::Definiens>,
  ) {
    let fmt = elab.formats[&Format::Attr(pat.to_format())];
    let mut cc = CorrConds::new();
    let primary: Box<[_]> = self.primary.0.iter().cloned().collect();
    let visible: Box<[_]> = pat.args.iter().map(|v| self.to_locus.get(ConstId(v.id.0))).collect();
    let mut args: Box<[_]> = Box::new([]);
    let (redefines, superfluous, pos);
    if it.redef {
      args = pat.args.iter().map(|v| Term::Constant(ConstId(v.id.0))).collect();
      let pat = elab.notations.attribute.iter().rev().find(|pat| {
        pat.fmt == fmt
          && !matches!(pat.kind, PatternKind::Attr(nr)
              if elab.g.constrs.attribute[nr].redefines.is_some())
          && matches!(pat.check_types(&elab.g, &elab.lc, &args),
            Some(subst) if { self.check_compatible_args(&subst); true })
      });
      let pat = pat.expect("type error");
      let PatternKind::Attr(nr) = pat.kind else { unreachable!() };
      let c = &elab.g.constrs.attribute[nr];
      (redefines, superfluous, pos) =
        (Some(nr), (self.primary.len() - pat.primary.len()) as u8, pat.pos);
    } else {
      (redefines, superfluous, pos) = (None, 0, true);
    }
    let value = def.as_ref().map(|def| elab.elab_def_value(&def.kind, pos));
    if let Some(value) = &value {
      cc.0[CorrCondKind::Consistency] = value.mk_consistency(&elab.g, None);
      if let Some(nr) = redefines {
        cc.0[CorrCondKind::Compatibility] =
          Some(value.mk_compatibility(&elab.g, None, &Formula::Attr { nr, args }));
      }
    }
    elab.elab_corr_conds(cc, &it.conds, &it.corr);
    let mut properties = Default::default();
    elab.elab_properties(&it.props, &mut properties);
    CheckAccess::check(&primary, &visible);
    let n;
    if superfluous != 0 || !it.props.is_empty() {
      let p = primary.clone();
      n = elab.g.constrs.attribute.push(TyConstructor {
        c: Constructor { primary: p, redefines, superfluous, properties, arg1: 0, arg2: 0 },
        ty: self.primary.0.last().unwrap().clone(),
      });
      elab.push_constr(ConstrKind::Attr(n));
      if let Some(mut value) = value {
        let DefValue::Formula(mut value) = value else { unreachable!() };
        value.visit(&mut self.to_locus);
        let formals =
          (superfluous..self.primary.len() as u8).map(LocusId).map(Term::Locus).collect();
        let mut f =
          value.defthm_for(&elab.g, &Formula::Attr { nr: redefines.unwrap_or(n), args: formals });
        AbstractLocus(self.primary.len() as u32).visit_formula(&mut f);
        let thm = self.forall_locus(f);
        self.defthms.push((def.as_ref().unwrap().label.as_ref().map(|l| l.id.0), thm));
        elab.r.read_definiens(&Definiens {
          essential: (superfluous..primary.len() as u8).map(LocusId).collect(),
          c: ConstrDef { constr: ConstrKind::Attr(n), primary: primary.clone() },
          assumptions: Formula::mk_and(self.assums.clone()),
          value: DefValue::Formula(value),
        });
      }
    } else {
      n = redefines.unwrap()
    }
    let pat = Pattern {
      kind: PatternKind::Attr(n),
      fmt,
      redefines: redefines.map(|x| x.0),
      primary,
      visible,
      pos,
    };
    elab.r.lc.formatter.push(&elab.r.g.constrs, &pat);
    elab.r.notations.attribute.push(pat)
  }

  fn elab_struct_def(&mut self, elab: &mut Analyzer, it: &ast::DefStruct) {
    elab.elab_corr_conds(CorrConds::new(), &it.conds, &it.corr);
    let mut parents: Box<[_]> = it.parents.iter().map(|ty| elab.elab_type(ty)).collect();
    let formals = self.primary.enum_iter().map(|(i, _)| Term::Locus(i)).collect_vec();
    let struct_primary: Box<[_]> = self.primary.0.iter().cloned().collect();
    let struct_id = StructId::from_usize(elab.g.constrs.struct_mode.len());
    let struct_pat = Pattern {
      kind: PatternKind::Struct(struct_id),
      fmt: elab.formats[&Format::Struct(it.pat.to_mode_format())],
      redefines: None,
      primary: struct_primary.clone(),
      visible: it.pat.args.iter().map(|v| self.to_locus.get(ConstId(v.id.0))).collect(),
      pos: true,
    };
    CheckAccess::check(&struct_pat.primary, &struct_pat.visible);
    elab.r.lc.formatter.push(&elab.r.g.constrs, &struct_pat);
    elab.r.notations.struct_mode.push(struct_pat);

    let struct_ty = Type {
      kind: TypeKind::Struct(struct_id),
      attrs: (Attrs::EMPTY, Attrs::EMPTY),
      args: formals,
    };
    let fixed_vars = elab.lc.fixed_var.len();
    let base = self.primary.len() as u8;
    self.to_locus.0 .0.resize(fixed_vars, None);
    let mut cur_locus = LocusId(base);
    for group in &it.fields {
      let ty = elab.elab_intern_type(&group.ty);
      for _ in &group.vars {
        elab.lc.fixed_var.push(FixedVar { ty: ty.clone(), def: None });
        self.to_locus.0.push(Some(cur_locus.fresh()));
      }
    }
    let mut field_tys = elab.lc.fixed_var.0.drain(fixed_vars..).map(|v| v.ty).collect_vec();
    field_tys.visit(&mut self.to_locus);
    let aggr_primary: Box<[_]> = self.primary.0.iter().chain(&field_tys).cloned().collect();
    let mut fields: Vec<SelId> = vec![];
    let aggr_id = AggrId::from_usize(elab.g.constrs.aggregate.len());
    let aggr_pat = Pattern {
      kind: PatternKind::Aggr(aggr_id),
      fmt: elab.formats[&Format::Aggr(it.pat.to_aggr_format())],
      redefines: None,
      primary: aggr_primary.clone(),
      visible: (base..cur_locus.0).map(LocusId).collect(),
      pos: true,
    };
    CheckAccess::check(&aggr_pat.primary, &aggr_pat.visible);
    elab.r.lc.formatter.push(&elab.r.g.constrs, &aggr_pat);
    elab.r.notations.aggregate.push(aggr_pat);

    let mut prefixes = vec![];
    for ty in &*parents {
      assert!(ty.attrs.0.attrs().is_empty());
      let TypeKind::Struct(s) = ty.kind else { panic!("not a struct type") };
      prefixes.push(elab.g.constrs.struct_mode[s].fields.clone().into_vec());
    }

    let sel_primary_it = self.primary.0.iter().chain([&struct_ty]).cloned();
    let subaggr_pat = Pattern {
      kind: PatternKind::SubAggr(struct_id),
      fmt: elab.formats[&Format::SubAggr(it.pat.to_subaggr_format())],
      redefines: None,
      primary: sel_primary_it.clone().collect(),
      visible: Box::new([LocusId(base)]),
      pos: true,
    };
    elab.r.lc.formatter.push(&elab.r.g.constrs, &subaggr_pat);
    elab.r.notations.sub_aggr.push(subaggr_pat);

    let mut mk_sel = MakeSelector { base, terms: vec![] };
    let mut field_fmt = vec![];
    let mut new_fields = vec![];
    for (v, mut ty) in it.fields.iter().flat_map(|group| &group.vars).zip(field_tys) {
      let fmt = elab.formats[&Format::Sel(v.sym.0)];
      assert!(!field_fmt.contains(&fmt), "duplicate field name");
      field_fmt.push(fmt);
      ty.visit(&mut mk_sel);
      let mut iter = parents.iter().zip(&mut prefixes).filter_map(|(ty, fields)| {
        let arg = Term::Constant(elab.lc.fixed_var.push(FixedVar { ty: ty.clone(), def: None }));
        for pat in elab.notations.selector.iter().rev() {
          if pat.fmt == fmt {
            if let Some(subst) = pat.check_types(&elab.g, &elab.lc, std::slice::from_ref(&arg)) {
              let PatternKind::Sel(nr) = pat.kind else { unreachable!() };
              let args = subst.trim_to(elab.g.constrs.selector[nr].primary.len());
              let ty2 = elab.g.constrs.selector[nr].ty.visit_cloned(&mut Inst::new(&args));
              assert!(().eq_type(&elab.g, &elab.lc, ty, &ty2), "field type mismatch");
              elab.lc.fixed_var.0.pop();
              fields.retain(|&x| x != nr);
              return Some((nr, args))
            }
          }
        }
        elab.lc.fixed_var.0.pop();
        None
      });
      if let Some((sel_id, args)) = iter.next() {
        assert!(iter.all(|(nr, _)| sel_id == nr), "overlapping parent fields");
        mk_sel.terms.push(Ok(Box::new(Term::Selector { nr: sel_id, args })));
        fields.push(sel_id);
      } else {
        let sel = TyConstructor { c: Constructor::new(sel_primary_it.clone().collect()), ty };
        let sel_id = elab.g.constrs.selector.push(sel);
        let sel_pat = Pattern {
          kind: PatternKind::Sel(sel_id),
          fmt,
          redefines: None,
          primary: sel_primary_it.clone().collect(),
          visible: Box::new([LocusId(base)]),
          pos: true,
        };
        CheckAccess::check(&sel_pat.primary, &sel_pat.visible);
        elab.r.lc.formatter.push(&elab.r.g.constrs, &sel_pat);
        elab.r.notations.selector.push(sel_pat);
        new_fields.push(sel_id);
        mk_sel.terms.push(Err(sel_id));
        fields.push(sel_id);
      }
    }

    assert!(prefixes.iter().all(|prefix| prefix.is_empty()), "structure does not extend parent");
    parents.visit(&mut self.to_locus);

    let struct_id2 = elab.g.constrs.struct_mode.push(StructMode {
      c: Constructor::new(struct_primary),
      parents,
      aggr: aggr_id,
      fields: fields.clone().into(),
    });
    assert!(struct_id == struct_id2);

    let aggr_id2 = elab.g.constrs.aggregate.push(Aggregate {
      c: TyConstructor { c: Constructor::new(aggr_primary), ty: struct_ty.clone() },
      base,
      fields: fields.into(),
    });
    assert!(aggr_id == aggr_id2);

    let mut c = Constructor::new(sel_primary_it.clone().collect());
    c.properties.set(PropertyKind::Abstractness);
    let attr_primary = sel_primary_it.collect();
    let attr_id = elab.g.constrs.attribute.push(TyConstructor { c, ty: struct_ty });
    let attr_pat = Pattern {
      kind: PatternKind::Attr(attr_id),
      fmt: FormatId::STRICT,
      redefines: None,
      primary: attr_primary,
      visible: Box::new([LocusId(base)]),
      pos: true,
    };
    elab.r.lc.formatter.push(&elab.r.g.constrs, &attr_pat);
    elab.r.notations.attribute.push(attr_pat);

    elab.push_constr(ConstrKind::Attr(attr_id));
    elab.push_constr(ConstrKind::Struct(struct_id));
    elab.push_constr(ConstrKind::Aggr(aggr_id));
    new_fields.into_iter().for_each(|sel_id| elab.push_constr(ConstrKind::Sel(sel_id)));

    // TODO: existential cluster
  }
}

impl ReadProof for BlockReader {
  type CaseIterable = std::convert::Infallible;
  type CaseIter<'a> = std::convert::Infallible;
  type SupposeRecv = std::convert::Infallible;

  fn intro(&mut self, elab: &mut Analyzer, start: usize) {
    self.to_locus.0 .0.resize(start, None);
    for fv in &elab.lc.fixed_var.0[start..] {
      let ty = fv.ty.visit_cloned(&mut self.to_locus);
      Exportable.visit_type(&ty);
      let i = self.primary.push(ty);
      self.to_locus.0.push(Some(i));
    }
  }

  fn assume(&mut self, elab: &mut Analyzer, mut conjs: Vec<Formula>) {
    conjs.visit(&mut self.to_locus);
    conjs.iter().for_each(|f| Exportable.visit_formula(f));
    self.assums.append(&mut conjs);
  }

  fn given(&mut self, elab: &mut Analyzer, start: usize, f: Formula) {
    let mut f = f.mk_neg();
    let end = elab.lc.fixed_var.len();
    elab.lc.mk_forall(start..end, false, &mut f);
    self.assume(elab, vec![f.mk_neg()]);
  }

  fn take(&mut self, elab: &mut Analyzer, term: Term) { panic!("invalid item") }
  fn thus(&mut self, elab: &mut Analyzer, f: Formula) { panic!("invalid item") }
  fn new_thesis_case(&mut self, elab: &mut Analyzer) -> Self::CaseIterable {
    panic!("invalid item")
  }

  fn new_thesis_case_iter(
    &mut self, _: &mut Analyzer, case: &mut Self::CaseIterable,
  ) -> Self::CaseIter<'_> {
    *case
  }

  fn next_thesis_case(
    &mut self, elab: &mut Analyzer, case: &mut Self::CaseIter<'_>, f: &[Formula],
  ) {
  }

  fn finish_thesis_case(&mut self, elab: &mut Analyzer, case: Self::CaseIter<'_>) { match case {} }
  fn new_suppose(&mut self, elab: &mut Analyzer) -> Self::SupposeRecv { panic!("invalid item") }
  fn next_suppose(&mut self, elab: &mut Analyzer, recv: &mut Self::SupposeRecv) {}
  fn finish_proof(&mut self, elab: &mut Analyzer) {}

  fn elab_item(&mut self, elab: &mut Analyzer, item: &ast::Item) -> bool {
    match (self.kind, &item.kind) {
      (BlockKind::Definition, ast::ItemKind::Definition(it)) => match &it.kind {
        ast::DefinitionKind::Func { pat, spec, def } =>
          self.elab_func_def(elab, pat, it, spec, def.as_deref()),
        ast::DefinitionKind::Pred { pat, def } => self.elab_pred_def(elab, pat, it, def.as_deref()),
        ast::DefinitionKind::Mode { pat, kind } => self.elab_mode_def(elab, pat, kind, it),
        ast::DefinitionKind::Attr { pat, def } => self.elab_attr_def(elab, pat, it, def.as_deref()),
      },
      (BlockKind::Definition, ast::ItemKind::DefStruct(it)) => self.elab_struct_def(elab, it),
      (BlockKind::Notation, ast::ItemKind::PatternRedef { kind, orig, new }) => match kind {
        ast::PatternRedefKind::PredSynonym { pos } => todo!("ikItmDefPred"),
        ast::PatternRedefKind::FuncNotation => todo!("ikItmDefFunc"),
        ast::PatternRedefKind::ModeNotation => todo!("ikItmDefMode"),
        ast::PatternRedefKind::AttrSynonym { pos } => todo!("ikItmDefPrAttr"),
      },
      (BlockKind::Registration, ast::ItemKind::Cluster(it)) => match &it.kind {
        ast::ClusterDeclKind::Exist { concl, ty } => todo!("ikItmCluRegistered"),
        ast::ClusterDeclKind::Func { term, concl, ty } => todo!("ikItmCluFunctor"),
        ast::ClusterDeclKind::Cond { antecedent, concl, ty } => todo!("ikItmCluConditional"),
      },
      (BlockKind::Registration, ast::ItemKind::Identify(_)) => todo!("ikIdFunctors"),
      (BlockKind::Registration, ast::ItemKind::Reduction(it)) => todo!("ikReduceFunctors"),
      (BlockKind::Registration, ast::ItemKind::SethoodRegistration { ty, just }) =>
        todo!("ikProperty"),
      _ => return self.super_elab_item(elab, item),
    }
    true
  }
}
