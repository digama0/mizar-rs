use crate::ast::{CaseKind, FormulaBinder, FormulaBinop, Pragma, ReservedId, VarKind};
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
  thesis_stack: Vec<Option<Box<Formula>>>,
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
      thesis_stack: vec![],
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
}

impl Analyzer<'_> {
  fn open_scope(&mut self, push_label: bool, copy_thesis: bool) -> Scope {
    self.thesis_stack.push(if copy_thesis { self.thesis.clone() } else { self.thesis.take() });
    Scope { sc: self.r.open_scope(push_label), priv_preds: self.priv_pred.len() }
  }

  fn close_scope(&mut self, sc: Scope, check_for_local_const: bool) -> Descope {
    self.priv_func_args.0.truncate(sc.sc.priv_funcs);
    self.priv_pred.0.truncate(sc.priv_preds);
    self.thesis = self.thesis_stack.pop().unwrap();
    self.r.close_scope(sc.sc, check_for_local_const)
  }

  fn scope<R: Visitable<Descope>>(
    &mut self, label: Option<LabelId>, copy_thesis: bool, check_for_local_const: bool,
    f: impl FnOnce(&mut Self) -> R,
  ) -> R {
    let sc = self.open_scope(label.is_some(), copy_thesis);
    let mut r = f(self);
    let mut dsc = self.close_scope(sc, check_for_local_const);
    r.visit(&mut dsc);
    r
  }

  fn item_header(&mut self, it: &ast::Item, s: &str) {
    if let Some(n) = crate::FIRST_VERBOSE_ITEM {
      set_verbose(self.items >= n);
    }
    if crate::ITEM_HEADER {
      eprint!("item[{}]: ", self.items);
      if crate::ALWAYS_VERBOSE_ITEM || verbose() {
        eprintln!("{it:#?}");
      } else {
        eprintln!("{s} @ {:?}", it.pos)
      }
    }
    self.items += 1;
  }

  fn elab_top_item(&mut self, it: &ast::Item) {
    match &it.kind {
      // ast::ItemKind::Section { .. } => self.item_header(it, "Section"),
      ast::ItemKind::Pragma { .. } => self.item_header(it, "Pragma"),
      ast::ItemKind::Block { .. } => self.item_header(it, "Block"),
      ast::ItemKind::SchemeBlock { .. } => self.item_header(it, "SchemeBlock"),
      ast::ItemKind::Theorem { .. } => self.item_header(it, "Theorem"),
      ast::ItemKind::Reservation { .. } => self.item_header(it, "Reservation"),
      _ => {}
    }
    match &it.kind {
      ast::ItemKind::Section => {}
      ast::ItemKind::Block { end, kind, items } => {
        let mut br = BlockReader::new(*kind, &self.lc);
        self.scope(None, false, false, |this| br.elab_proof(this, items, *end));
        br.after_scope(self)
      }
      ast::ItemKind::SchemeBlock(it) => self.scope(None, false, false, |this| this.elab_scheme(it)),
      ast::ItemKind::Theorem { prop, just } => {
        let f = self.elab_intern_formula(&prop.f, true);
        Exportable.visit_formula(&f);
        let label = prop.label.as_ref().map(|l| l.id.0);
        self.elab_justification(label, &f, just);
        self.push_prop(label, f);
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
      &ast::ItemKind::Pragma(Pragma::Canceled(k, n)) => self.elab_canceled(k, n),
      ast::ItemKind::Pragma(Pragma::ThmDesc(_)) => {}
      _ => self.elab_stmt_item(it),
    }
  }

  fn elab_scheme(&mut self, ast::SchemeBlock { end, head, items }: &ast::SchemeBlock) {
    let ast::SchemeHead { nr, groups, concl, prems, .. } = head;
    assert!(self.sch_func_args.is_empty());
    assert!(self.sch_pred_args.is_empty());
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
    let prems = prems.iter().map(|prop| self.elab_proposition(prop, true)).collect::<Box<[_]>>();
    let thesis = self.elab_intern_formula(concl, true);
    self.elab_proof(None, &thesis, items, *end);
    let primary: Box<[_]> = self.lc.sch_func_ty.0.drain(..).collect();
    let mut sch = Scheme { sch_funcs: primary, prems, thesis };
    self.lc.expand_consts(|c| sch.visit(c));
    sch.sch_funcs.iter().for_each(|ty| Exportable.visit_type(ty));
    sch.prems.iter().for_each(|ty| Exportable.visit_formula(ty));
    Exportable.visit_formula(&sch.thesis);
    self.lc.infer_const.get_mut().truncate(infer_consts);
    self.sch_func_args.0.clear();
    self.sch_pred_args.0.clear();
    self.libs.sch.insert((ArticleId::SELF, *nr), sch);
  }

  fn elab_stmt_item(&mut self, it: &ast::Item) {
    match &it.kind {
      ast::ItemKind::Set { .. } => self.item_header(it, "Set"),
      ast::ItemKind::DefFunc { .. } => self.item_header(it, "DefFunc"),
      ast::ItemKind::DefPred { .. } => self.item_header(it, "DefPred"),
      ast::ItemKind::Reconsider { .. } => self.item_header(it, "Reconsider"),
      ast::ItemKind::Consider { .. } => self.item_header(it, "Consider"),
      ast::ItemKind::Statement { .. } => self.item_header(it, "Statement"),
      _ => {}
    }
    match &it.kind {
      ast::ItemKind::Set { value, .. } => {
        let term = self.elab_intern_term(value);
        let ty = term.get_type_uncached(&self.g, &self.lc);
        self.lc.fixed_var.push(FixedVar { ty, def: Some((Box::new(term), true)) });
      }
      ast::ItemKind::DefFunc { tys, value, .. } => {
        self.lc.term_cache.get_mut().open_scope();
        self.elab_intern_push_locus_tys(tys);
        let value = self.elab_intern_term(value);
        let ty = value.get_type(&self.g, &self.lc, false);
        let primary = self.r.lc.locus_ty.0.drain(..).collect();
        self.lc.term_cache.get_mut().close_scope();
        self.r.lc.priv_func.push(FuncDef { primary, ty: Box::new(ty), value: Box::new(value) });
      }
      ast::ItemKind::DefPred { tys, value, .. } => {
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
            self.lc.fixed_var.push(FixedVar { ty: ty.clone(), def: Some((tm, false)) });
          }
        });
        self.elab_justification(None, &f, just)
      }
      ast::ItemKind::Consider { vars, conds, just } => {
        let start = self.lc.fixed_var.len();
        let istart = self.lc.infer_const.get_mut().len() as u32;
        for var in vars {
          self.elab_fixed_vars(var);
        }
        let mut to_push = vec![];
        let mut f = Formula::mk_and_with(|conjs| {
          for prop in conds {
            let f = self.elab_intern_formula(&prop.f, true);
            f.clone().append_conjuncts_to(conjs);
            to_push.push((prop.label.as_ref().map(|l| l.id.0), f))
          }
        })
        .mk_neg();
        let end = self.lc.fixed_var.len();
        self.lc.mk_forall(start..end, istart, false, &mut f);
        self.elab_justification(None, &f.mk_neg(), just);
        for (label, f) in to_push {
          self.push_prop(label, f);
        }
      }
      ast::ItemKind::Statement(stmt) => {
        self.elab_stmt(stmt);
      }
      _ => unreachable!("unexpected item: {it:?}"),
    }
  }

  fn elab_stmt(&mut self, stmt: &ast::Statement) -> Formula {
    // vprintln!("elab_stmt (thesis = {:?}) {stmt:?}", self.thesis);
    match stmt {
      ast::Statement::Proposition { prop, just } => {
        let f = self.elab_intern_formula(&prop.f, true);
        let label = prop.label.as_ref().map(|l| l.id.0);
        self.elab_justification(label, &f, just);
        self.push_prop(label, f.clone());
        f
      }
      ast::Statement::IterEquality { prop, just, steps } => {
        if let Formula::Pred { nr, args } = self.elab_intern_formula(&prop.f, true) {
          if let (nr, [lhs, rhs]) = Formula::adjust_pred(nr, &args, &self.g.constrs) {
            if self.g.reqs.equals_to() == Some(nr) {
              self.elab_justification(None, &self.g.reqs.mk_eq(lhs.clone(), rhs.clone()), just);
              let mut mid = rhs.clone();
              for ast::IterStep { rhs, just, .. } in steps {
                let rhs = self.elab_intern_term(rhs);
                self.elab_justification(None, &self.g.reqs.mk_eq(mid, rhs.clone()), just);
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
      ast::Statement::Now { end, label, items } => {
        let label = label.as_ref().map(|l| l.id.0);
        let f = self.scope(label, false, true, |this| {
          ReconstructThesis { stack: vec![ProofStep::Break(true)] }.elab_proof(this, items, *end)
        });
        self.push_prop(label, f.clone());
        f
      }
    }
  }

  fn elab_proof(
    &mut self, label: Option<LabelId>, thesis: &Formula, items: &[ast::Item], end: Position,
  ) {
    self.scope(label, false, false, |this| {
      this.thesis = Some(Box::new(thesis.clone()));
      WithThesis.elab_proof(this, items, end)
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

  fn elab_proposition(&mut self, prop: &ast::Proposition, quotable: bool) -> Formula {
    let f = self.elab_intern_formula(&prop.f, true);
    if quotable {
      self.push_prop(prop.label.as_ref().map(|l| l.id.0), f.clone());
    }
    f
  }

  fn elab_justification(
    &mut self, label: Option<LabelId>, thesis: &Formula, just: &ast::Justification,
  ) {
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
      ast::Justification::Block { pos, items } => self.elab_proof(label, thesis, items, pos.1),
    }
  }

  fn elab_corr_conds(
    &mut self, mut cc: CorrConds, conds: &[ast::CorrCond], corr: &Option<ast::Correctness>,
  ) {
    for cond in conds {
      let mut thesis = cc.0[cond.kind].take().unwrap();
      thesis.visit(&mut self.intern_const());
      self.elab_justification(None, &thesis, &cond.just);
    }
    if let Some(corr) = corr {
      let mut thesis = Formula::mk_and_with(|conjs| {
        for &kind in &corr.conds {
          cc.0[kind].take().unwrap().append_conjuncts_to(conjs);
        }
      });
      thesis.visit(&mut self.intern_const());
      self.elab_justification(None, &thesis, &corr.just);
    }
    assert!(cc.0.iter().all(|p| p.1.is_none()));
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

  fn elab_canceled(&mut self, _k: CancelKind, _n: u32) {}

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
    vprintln!("elab_term {tm:?}");
    let res = match *tm {
      ast::Term::Placeholder { nr, .. } => Term::Locus(nr),
      ast::Term::Simple { kind, var, .. } => match kind {
        VarKind::Bound => Term::Bound(BoundId(var)),
        VarKind::Const | VarKind::DefConst => {
          if let Some((ref def, true)) = self.lc.fixed_var[ConstId(var)].def {
            (**def).clone()
          } else {
            Term::Constant(ConstId(var))
          }
        }
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
      ast::Term::PrivFunc { kind, var, ref args, .. } => {
        let mut args = self.elab_terms_qua(args);
        match kind {
          VarKind::PrivFunc => {
            let nr = PrivFuncId(var);
            let def = &self.lc.priv_func[nr];
            assert!(agrees(&self.g, &self.lc, &args, &def.primary));
            args.iter_mut().for_each(|t| t.strip_qua_mut());
            let base = self.lc.bound_var.len() as u32;
            let value = def.value.visit_cloned(&mut Inst { subst: &args, base, depth: 0 });
            Term::PrivFunc { nr, args, value }
          }
          VarKind::SchFunc => {
            let nr = SchFuncId(var);
            assert!(agrees(&self.g, &self.lc, &args, &self.sch_func_args[nr]));
            args.iter_mut().for_each(|t| t.strip_qua_mut());
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
          if pat.fmt == fmt
            && pat.check_types(&self.g, &self.lc, std::slice::from_ref(&arg)).is_some()
          {
            let PatternKind::SubAggr(nr) = pat.kind else { unreachable!() };
            let ty = arg.get_type_uncached(&self.g, &self.lc);
            return Term::mk_aggr(&self.g, nr, &arg.strip_qua(), &ty)
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
    };
    vprintln!("elab_term {tm:?}\n -> {res:?}");
    res
  }

  fn elab_term(&mut self, tm: &ast::Term) -> Term { self.elab_term_qua(tm).strip_qua() }

  fn elab_terms_qua(&mut self, tms: &[ast::Term]) -> Box<[TermQua]> {
    tms.iter().map(|t| self.elab_term_qua(t)).collect()
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
  fn elab_attr(&mut self, attr: &ast::Attr, mut pos: bool, ty: &mut Type) -> Attr {
    match attr {
      ast::Attr::Non { attr, .. } => self.elab_attr(attr, !pos, ty),
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
              assert!(matches!(ty.attrs.0, Attrs::Consistent(_)));
              return Attr { nr, pos, args }
            }
          }
        }
        panic!("type error")
      }
    }
  }

  fn elab_type(&mut self, ty: &ast::Type) -> Type {
    vprintln!("elab_type {ty:?}");
    let res = (|| match ty {
      ast::Type::Mode { sym, args, .. } => {
        let args = self.elab_terms_qua(args);
        let fmt = self.formats[&Format::Mode(FormatMode { sym: sym.0, args: args.len() as u8 })];
        for pat in self.notations.mode.iter().rev() {
          if pat.fmt == fmt {
            if let Some(subst) = pat.check_types(&self.g, &self.lc, &args) {
              let mut ty;
              let base = self.lc.bound_var.len() as u32;
              match pat.kind {
                PatternKind::Mode(nr) => {
                  let mut args = subst.trim_to(self.g.constrs.mode[nr].primary.len()).to_vec();
                  args.iter_mut().for_each(|t| t.strip_qua_mut());
                  ty = Type { kind: TypeKind::Mode(nr), attrs: Default::default(), args }
                }
                PatternKind::ExpandableMode { ref expansion } => {
                  ty = (**expansion).clone();
                  let mut args = subst.finish();
                  args.iter_mut().for_each(|t| t.strip_qua_mut());
                  ty.visit(&mut Inst { subst: &args, base, depth: 0 });
                }
                _ => unreachable!(),
              }
              let mut attrs = ty.attrs.1.clone();
              if let TypeKind::Mode(nr) = ty.kind {
                if nr != ModeId::ANY {
                  attrs.enlarge_by(&self.g.constrs, &self.g.constrs.mode[nr].ty.attrs.1, |attr| {
                    attr.visit_cloned(&mut Inst { subst: &ty.args, base, depth: 0 })
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
        attrs.iter().rev().for_each(|attr| {
          let attr = self.elab_attr(attr, true, &mut ty2);
          ty2.attrs.0.insert(&self.g.constrs, attr.clone());
          ty2.attrs.1.insert(&self.g.constrs, attr);
          ty2.round_up_with_self(&self.g, &self.lc, false);
          assert!(matches!(ty2.attrs.0, Attrs::Consistent(_)));
        });
        for cl in self.g.clusters.registered.iter().rev() {
          let mut subst = Subst::new(cl.primary.len());
          if subst.eq_radices(&self.g, &self.lc, &cl.ty, &ty)
            && (ty2.attrs.0)
              .is_subset_of(&cl.consequent.1, |a2, a1| subst.eq_attr(&self.g, &self.lc, a1, a2))
            && subst.check_loci_types::<false>(&self.g, &self.lc, &cl.primary, false)
          {
            let mut attrs = ty2.attrs.0.clone();
            attrs.enlarge_by(&self.g.constrs, &ty.attrs.1, Attr::clone);
            attrs.round_up_with(&self.g, &self.lc, &ty, false);
            assert!(matches!(ty2.attrs.0, Attrs::Consistent(_)));
            ty.attrs = (ty2.attrs.0, attrs);
            return ty
          }
        }
        panic!("non registered cluster \"{ty2:?}\"")
      }
      ast::Type::Reservation { nr, subst, .. } => {
        let mut ty = self.reserved[nr.unwrap()].clone();
        if !subst.is_empty() {
          InstReservation(subst).visit_type(&mut ty)
        }
        ty
      }
    })();
    vprintln!("elab_type {ty:?}\n -> {res:?}");
    res
  }

  fn elab_flex_and(&mut self, f1: &ast::Formula, f2: &ast::Formula, pos: bool) -> Formula {
    #[derive(Clone, Copy, Default)]
    enum OneDiff<'a> {
      #[default]
      Same,
      One(&'a Term, &'a Term),
      Fail,
    }

    impl<'a> OneDiff<'a> {
      fn bool(b: bool) -> Self { Self::then(b, || Self::Same) }
      fn then(b: bool, f: impl FnOnce() -> Self) -> Self {
        if b {
          f()
        } else {
          Self::Fail
        }
      }

      fn merge(&mut self, ctx: &Constructors, other: Self) {
        match (*self, other) {
          (OneDiff::Fail, _) | (_, OneDiff::Same) => {}
          (_, OneDiff::Fail) | (OneDiff::Same, _) => *self = other,
          (OneDiff::One(a1, a2), OneDiff::One(b1, b2)) => {
            if a1.cmp(ctx, None, b1, CmpStyle::Strict).is_ne()
              || a2.cmp(ctx, None, b2, CmpStyle::Strict).is_ne()
            {
              *self = OneDiff::Fail
            }
          }
        }
      }

      fn merge_many(ctx: &Constructors, it: impl IntoIterator<Item = Self>) -> Self {
        let mut out = OneDiff::Same;
        for other in it {
          out.merge(ctx, other);
          if let OneDiff::Fail = out {
            break
          }
        }
        out
      }

      fn and_then(mut self, ctx: &Constructors, other: impl FnOnce() -> Self) -> Self {
        match self {
          OneDiff::Same => other(),
          OneDiff::One(..) => {
            self.merge(ctx, other());
            self
          }
          OneDiff::Fail => self,
        }
      }

      fn eq_term(
        g: &Global, lc: &LocalContext, ic: &'a IdxVec<InferId, Assignment>, t1: &'a Term,
        t2: &'a Term,
      ) -> Self {
        use Term::*;
        let res = match (t1, t2) {
          (Bound(BoundId(n1)), Bound(BoundId(n2)))
          | (Constant(ConstId(n1)), Constant(ConstId(n2)))
          | (Numeral(n1), Numeral(n2)) => Self::bool(n1 == n2),
          (Infer(InferId(n1)), Infer(InferId(n2))) if n1 == n2 => Self::bool(true),
          (Functor { nr: n1, args: args1 }, Functor { nr: n2, args: args2 }) => {
            let (n1, args1) = Term::adjust(*n1, args1, &g.constrs);
            let (n2, args2) = Term::adjust(*n2, args2, &g.constrs);
            Self::then(n1 == n2, || Self::eq_terms(g, lc, ic, args1, args2))
          }
          (
            SchFunc { nr: SchFuncId(n1), args: args1 },
            SchFunc { nr: SchFuncId(n2), args: args2 },
          )
          | (
            Aggregate { nr: AggrId(n1), args: args1 },
            Aggregate { nr: AggrId(n2), args: args2 },
          )
          | (Selector { nr: SelId(n1), args: args1 }, Selector { nr: SelId(n2), args: args2 })
            if n1 == n2 =>
            Self::eq_terms(g, lc, ic, args1, args2),
          (The { ty: ty1 }, The { ty: ty2 }) => Self::eq_type(g, lc, ic, ty1, ty2),
          (
            Fraenkel { args: args1, scope: sc1, compr: c1 },
            Fraenkel { args: args2, scope: sc2, compr: c2 },
          ) => Self::then(args1.len() == args2.len(), || {
            Self::merge_many(
              &g.constrs,
              args1.iter().zip(&**args2).map(|(ty1, ty2)| Self::eq_type(g, lc, ic, ty1, ty2)),
            )
            .and_then(&g.constrs, || Self::eq_term(g, lc, ic, sc1, sc2))
            .and_then(&g.constrs, || Self::eq_formula(g, lc, ic, c1, c2))
          }),
          (It, It) => Self::bool(true),
          (_, &Infer(nr)) => Self::eq_term(g, lc, ic, t1, &ic[nr].def),
          (&Infer(nr), _) => Self::eq_term(g, lc, ic, &ic[nr].def, t2),
          (Locus(_), _) | (_, Locus(_)) => unreachable!(),
          (Qua { .. }, _) | (_, Qua { .. }) => unreachable!(),
          (EqMark(_), _) | (_, EqMark(_)) => unreachable!(),
          (EqClass(_), _) | (_, EqClass(_)) => unreachable!(),
          (FreeVar(_), _) | (_, FreeVar(_)) => unreachable!(),
          (PrivFunc { .. }, _) | (_, PrivFunc { .. }) =>
            Self::eq_term(g, lc, ic, t1.skip_priv_func(None), t2.skip_priv_func(None)),
          _ => Self::bool(false),
        };
        if let Self::Fail = res {
          Self::One(t1, t2)
        } else {
          res
        }
      }

      fn eq_terms(
        g: &Global, lc: &LocalContext, ic: &'a IdxVec<InferId, Assignment>, t1: &'a [Term],
        t2: &'a [Term],
      ) -> Self {
        Self::then(t1.len() == t2.len(), || {
          Self::merge_many(
            &g.constrs,
            t1.iter().zip(t2).map(|(t1, t2)| Self::eq_term(g, lc, ic, t1, t2)),
          )
        })
      }

      fn eq_type(
        g: &Global, lc: &LocalContext, ic: &'a IdxVec<InferId, Assignment>, ty1: &'a Type,
        ty2: &'a Type,
      ) -> Self {
        Self::then(().eq_attrs(g, lc, ty1, ty2) && ty1.kind == ty2.kind, || {
          Self::eq_terms(g, lc, ic, &ty1.args, &ty2.args)
        })
      }

      fn eq_formula(
        g: &Global, lc: &LocalContext, ic: &'a IdxVec<InferId, Assignment>, f1: &'a Formula,
        f2: &'a Formula,
      ) -> Self {
        use Formula::*;
        match (f1.skip_priv_pred(), f2.skip_priv_pred()) {
          (True, True) => Self::bool(true),
          (Neg { f: f1 }, Neg { f: f2 }) => Self::eq_formula(g, lc, ic, f1, f2),
          (Is { term: t1, ty: ty1 }, Is { term: t2, ty: ty2 }) => Self::eq_term(g, lc, ic, t1, t2)
            .and_then(&g.constrs, || Self::eq_type(g, lc, ic, ty1, ty2)),
          (And { args: args1 }, And { args: args2 }) =>
            Self::then(args1.len() == args2.len(), || {
              Self::merge_many(
                &g.constrs,
                args1.iter().zip(args2).map(|(f1, f2)| Self::eq_formula(g, lc, ic, f1, f2)),
              )
            }),
          (
            SchPred { nr: SchPredId(n1), args: args1 },
            SchPred { nr: SchPredId(n2), args: args2 },
          )
          | (
            PrivPred { nr: PrivPredId(n1), args: args1, .. },
            PrivPred { nr: PrivPredId(n2), args: args2, .. },
          )
          | (Attr { nr: AttrId(n1), args: args1 }, Attr { nr: AttrId(n2), args: args2 })
          | (Pred { nr: PredId(n1), args: args1 }, Pred { nr: PredId(n2), args: args2 })
            if n1 == n2 =>
            Self::eq_terms(g, lc, ic, args1, args2),
          (ForAll { dom: dom1, scope: sc1 }, ForAll { dom: dom2, scope: sc2 }) =>
            Self::eq_type(g, lc, ic, dom1, dom2)
              .and_then(&g.constrs, || Self::eq_formula(g, lc, ic, sc1, sc2)),
          #[allow(clippy::explicit_auto_deref)]
          (FlexAnd { terms: t1, scope: sc1 }, FlexAnd { terms: t2, scope: sc2 }) =>
            Self::eq_terms(g, lc, ic, &**t1, &**t2)
              .and_then(&g.constrs, || Self::eq_formula(g, lc, ic, sc1, sc2)),
          _ => Self::bool(false),
        }
      }
    }

    struct Apply<'a> {
      g: &'a Global,
      lc: &'a LocalContext,
      t1: &'a Term,
      t2: &'a Term,
      base: u32,
      depth: u32,
    }

    impl<'a> Apply<'a> {
      fn term(&mut self, t1: &Term, t2: &Term) -> Term {
        use Term::*;
        if ().eq_term(self.g, self.lc, t1, t2) {
          return t1.visit_cloned(&mut OnVarMut(|nr| {
            if *nr >= self.base {
              *nr += 1
            }
          }))
        }
        if ().eq_term(self.g, self.lc, self.t1, t1) && ().eq_term(self.g, self.lc, self.t2, t2) {
          return Term::Bound(BoundId(self.depth))
        }
        match (t1, t2) {
          (Functor { nr: n1, args: args1 }, Functor { nr: n2, args: args2 }) if n1 == n2 =>
            Functor { nr: *n1, args: self.terms(args1, args2) },
          (SchFunc { nr: n1, args: args1 }, SchFunc { nr: n2, args: args2 }) if n1 == n2 =>
            SchFunc { nr: *n1, args: self.terms(args1, args2) },
          (Aggregate { nr: n1, args: args1 }, Aggregate { nr: n2, args: args2 }) if n1 == n2 =>
            Aggregate { nr: *n1, args: self.terms(args1, args2) },
          (Selector { nr: n1, args: args1 }, Selector { nr: n2, args: args2 }) if n1 == n2 =>
            Selector { nr: *n1, args: self.terms(args1, args2) },
          (The { ty: ty1 }, The { ty: ty2 }) => The { ty: Box::new(self.ty(ty1, ty2)) },
          (
            Fraenkel { args: args1, scope: sc1, compr: c1 },
            Fraenkel { args: args2, scope: sc2, compr: c2 },
          ) => {
            let depth = self.depth;
            let args = args1
              .iter()
              .zip(&**args2)
              .map(|(t1, t2)| {
                let t = self.ty(t1, t2);
                self.depth += 1;
                t
              })
              .collect();
            let scope = Box::new(self.term(sc1, sc2));
            let compr = Box::new(self.formula(c1, c2));
            self.depth = depth;
            Fraenkel { args, scope, compr }
          }
          (_, &Infer(nr)) => self.term(t1, &self.lc.infer_const.borrow()[nr].def),
          (&Infer(nr), _) => self.term(&self.lc.infer_const.borrow()[nr].def, t2),
          (Locus(_), _) | (_, Locus(_)) => unreachable!(),
          (Qua { .. }, _) | (_, Qua { .. }) => unreachable!(),
          (EqMark(_), _) | (_, EqMark(_)) => unreachable!(),
          (EqClass(_), _) | (_, EqClass(_)) => unreachable!(),
          (FreeVar(_), _) | (_, FreeVar(_)) => unreachable!(),
          (PrivFunc { .. }, _) | (_, PrivFunc { .. }) =>
            self.term(t1.skip_priv_func(None), t2.skip_priv_func(None)),
          _ => panic!("flex-and construction failed"),
        }
      }

      fn terms(&mut self, args1: &[Term], args2: &[Term]) -> Box<[Term]> {
        args1.iter().zip(args2).map(|(t1, t2)| self.term(t1, t2)).collect()
      }

      fn ty(&mut self, ty1: &Type, ty2: &Type) -> Type {
        assert!(().eq_attrs(self.g, self.lc, ty1, ty2) && ty1.kind == ty2.kind);
        let attrs = ty1.attrs.visit_cloned(&mut OnVarMut(|nr| {
          if *nr >= self.base {
            *nr += 1
          }
        }));
        Type { attrs, kind: ty1.kind, args: self.terms(&ty1.args, &ty2.args).into() }
      }

      fn formula(&mut self, f1: &Formula, f2: &Formula) -> Formula {
        use Formula::*;
        if ().eq_formula(self.g, self.lc, f1, f2) {
          return f1.visit_cloned(&mut OnVarMut(|nr| {
            if *nr >= self.base {
              *nr += 1
            }
          }))
        }
        match (f1.skip_priv_pred(), f2.skip_priv_pred()) {
          (Neg { f: f1 }, Neg { f: f2 }) => Neg { f: Box::new(self.formula(f1, f2)) },
          (Is { term: t1, ty: ty1 }, Is { term: t2, ty: ty2 }) =>
            Is { term: Box::new(self.term(t1, t2)), ty: Box::new(self.ty(ty1, ty2)) },
          (And { args: args1 }, And { args: args2 }) =>
            And { args: args1.iter().zip(args2).map(|(f1, f2)| self.formula(f1, f2)).collect() },
          (SchPred { nr: n1, args: args1 }, SchPred { nr: n2, args: args2 }) if n1 == n2 =>
            SchPred { nr: *n1, args: self.terms(args1, args2) },
          (
            PrivPred { nr: n1, args: args1, value: v1 },
            PrivPred { nr: n2, args: args2, value: v2 },
          ) if n1 == n2 => PrivPred {
            nr: *n1,
            args: self.terms(args1, args2),
            value: Box::new(self.formula(v1, v2)),
          },
          (Attr { nr: n1, args: args1 }, Attr { nr: n2, args: args2 }) if n1 == n2 =>
            Attr { nr: *n1, args: self.terms(args1, args2) },
          (Pred { nr: n1, args: args1 }, Pred { nr: n2, args: args2 }) if n1 == n2 =>
            Pred { nr: *n1, args: self.terms(args1, args2) },
          (ForAll { dom: dom1, scope: sc1 }, ForAll { dom: dom2, scope: sc2 }) => {
            let dom = Box::new(self.ty(dom1, dom2));
            self.depth += 1;
            let scope = Box::new(self.formula(sc1, sc2));
            self.depth -= 1;
            ForAll { dom, scope }
          }
          #[allow(clippy::explicit_auto_deref)]
          (FlexAnd { terms: t1, scope: sc1 }, FlexAnd { terms: t2, scope: sc2 }) => {
            let terms = Box::new([self.term(&t1[0], &t2[0]), self.term(&t1[1], &t2[1])]);
            self.depth += 1;
            let scope = Box::new(self.formula(sc1, sc2));
            self.depth -= 1;
            FlexAnd { terms, scope }
          }
          _ => panic!("flex-and construction failed"),
        }
      }
    }

    let Some(natural) = self.g.reqs.natural() else { panic!("requirement NUMERALS missing") };
    let Some(_le) = self.g.reqs.less_or_equal() else { panic!("requirement REAL missing") };
    let f1 = self.elab_formula(f1, pos);
    let f2 = self.elab_formula(f2, pos);
    let (t1, t2) = {
      let ic = self.lc.infer_const.borrow();
      let OneDiff::One(t1, t2) = OneDiff::eq_formula(&self.g, &self.lc, &ic, &f1, &f2) else {
        panic!("can't abstract flex-and term, must have exactly one difference")
      };
      (t1.clone(), t2.clone())
    };
    let base = self.lc.bound_var.len() as u32;
    let only_constant = !CheckBound::get(base, |cb| {
      cb.visit_term(&t1);
      cb.visit_term(&t2);
    });
    assert!(only_constant, "can't abstract flex-and term, contains bound variables");
    let natural = Attrs::Consistent(vec![Attr::new0(natural, true)]);
    let is_natural = |t: &Term| {
      natural.is_subset_of(&t.get_type(&self.g, &self.lc, false).attrs.1, |a1, a2| {
        ().eq_attr(&self.g, &self.lc, a1, a2)
      })
    };
    assert!(
      is_natural(&t1) && is_natural(&t2),
      "can't abstract flex-and term, boundary variable does not have 'natural' adjective"
    );
    let scope =
      Apply { g: &self.g, lc: &self.lc, t1: &t1, t2: &t2, base, depth: base }.formula(&f1, &f2);
    Formula::FlexAnd { terms: Box::new([t1, t2]), scope: Box::new(scope) }
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
    // for i in 0..n {
    //   vprintln!("push_bound b{}: {dom:?}", self.lc.bound_var.len() + i);
    // }
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
    for _ in 0..var.vars.len() {
      scope = Formula::forall(self.lc.bound_var.0.pop().unwrap(), scope)
    }
    self.lc.term_cache.get_mut().close_scope();
    scope
  }

  fn elab_formula(&mut self, f: &ast::Formula, pos: bool) -> Formula {
    // vprintln!("elab_formula {pos:?} {f:?}");
    let res = match f {
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
      ast::Formula::PrivPred { kind, var, args, .. } => {
        let mut args = self.elab_terms_qua(args);
        match kind {
          VarKind::PrivPred => {
            let nr = PrivPredId(*var);
            let (ty, value) = &self.priv_pred[nr];
            assert!(agrees(&self.g, &self.lc, &args, ty));
            args.iter_mut().for_each(|t| t.strip_qua_mut());
            let base = self.lc.bound_var.len() as u32;
            let value = value.visit_cloned(&mut Inst { subst: &args, base, depth: 0 });
            Formula::PrivPred { nr, args, value }.maybe_neg(pos)
          }
          VarKind::SchPred => {
            let nr = SchPredId(*var);
            assert!(agrees(&self.g, &self.lc, &args, &self.sch_pred_args[nr]));
            args.iter_mut().for_each(|t| t.strip_qua_mut());
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
      ast::Formula::Thesis { pos: loc } => self
        .thesis
        .as_deref()
        // this step is super sketchy, but Mizar actually lets you access the
        // `thesis` of outer `proof` scopes in a `now` block
        .or_else(|| self.thesis_stack.iter().rev().find_map(Option::as_deref))
        .unwrap_or_else(|| panic!("at {}:{loc:?}: thesis is not known", self.article))
        .clone()
        .maybe_neg(pos),
    };
    vprintln!("elab_formula {pos:?} {f:?}\n -> {res:?}");
    res
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
      vprintln!("whnf (up = {up}, atomic = {atomic}) <- {f:?}");
      let mut args_buf;
      let (kind, args) = match &mut *f.1 {
        Formula::Neg { f: f2 } => {
          *f = (!f.0, std::mem::take(f2));
          continue 'start
        }
        Formula::PrivPred { value, .. } => {
          f.1 = std::mem::take(value);
          continue 'start
        }
        Formula::FlexAnd { .. } => {
          let (Some(nat), Some(le)) = (&self.g.nat, self.g.reqs.less_or_equal()) else { break };
          let Formula::FlexAnd { terms, scope } = std::mem::take(&mut *f.1) else { unreachable!() };
          *f.1 = self.g.expand_flex_and(nat, le, *terms, scope, 0);
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
      for def in self.definitions.iter().rev() {
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
        // vprintln!("expanded {def:?}");
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
    vprintln!("inst_forall {term:?}, {widenable}, {up}, {f:?}");
    let (true, Formula::ForAll { dom, scope }) = (f.0, &mut *f.1) else { panic!("not a forall") };
    let ty = term.get_type(&self.g, &self.lc, false);
    vprintln!("inst_forall {term:?}: {ty:?}");
    Inst0(0, term).visit_formula(scope);
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
  fn and_telescope(&mut self, tgt: Vec<Formula>, up: bool, conjs: Vec<Formula>) -> Vec<Formula> {
    vprintln!("and_telescope {tgt:?} <- {conjs:?}");
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
            Formula::PrivPred { nr: n1, value: v1, .. },
            Formula::PrivPred { nr: n2, value: v2, .. },
          ) => match (*n1).cmp(n2) {
            Ordering::Less => f2.1 = std::mem::take(v2),
            Ordering::Equal => panic!("formula mismatch"),
            Ordering::Greater => f1.1 = std::mem::take(v1),
          },
          (Formula::PrivPred { value, .. }, _) => f1.1 = std::mem::take(value),
          (_, Formula::PrivPred { value, .. }) => f2.1 = std::mem::take(value),
          _ => {
            vprintln!("compare: {f1:?} <> {f2:?}");
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

  /// RClusterObj.RegisterCluster
  fn register_cluster(&mut self, mut attrs: Attrs, primary: Box<[Type]>, mut ty: Type) {
    let mut attrs1 = attrs.clone();
    attrs1.enlarge_by(&self.g.constrs, &ty.attrs.0, |a| a.clone());
    attrs.enlarge_by(&self.g.constrs, &ty.attrs.1, |a| a.clone());
    attrs.round_up_with(&self.g, &self.lc, &ty, false);
    let Attrs::Consistent(_) = attrs else { panic!("inconsistent existential cluster") };
    ty.attrs = (Attrs::EMPTY, Attrs::EMPTY);
    self.read_registered_cluster(RegisteredCluster {
      cl: Cluster { primary, consequent: (attrs1, attrs) },
      ty: Box::new(ty),
    });
  }
}

struct InstReservation<'a>(&'a [(VarKind, u32)]);

impl VisitMut for InstReservation<'_> {
  fn visit_term(&mut self, tm: &mut Term) {
    match *tm {
      Term::Bound(nr) => {
        let (kind, nr) = self.0[nr.0 as usize];
        match kind {
          VarKind::Bound => *tm = Term::Bound(BoundId(nr)),
          VarKind::Const | VarKind::DefConst => *tm = Term::Constant(ConstId(nr)),
          _ => unreachable!(),
        }
      }
      _ => self.super_visit_term(tm),
    }
  }
}

#[derive(Clone, Copy, Debug)]
enum Args {
  Unary([ConstId; 1]),
  Binary([ConstId; 2]),
}

#[derive(Debug)]
struct InstN<const N: usize> {
  from: [ConstId; N],
  to: [BoundId; N],
  it: BoundId,
  lift: u32,
}

impl<const N: usize> InstN<N> {
  fn new(args: [ConstId; N], lift: u32, it: u32, tgt: [u32; N]) -> InstN<N> {
    InstN { from: args, to: tgt.map(BoundId), it: BoundId(it), lift }
  }
}

impl<const N: usize> VisitMut for InstN<N> {
  fn visit_term(&mut self, tm: &mut Term) {
    match *tm {
      Term::Bound(ref mut nr) => nr.0 += self.lift,
      Term::Constant(c) =>
        for i in 0..N {
          if c == self.from[i] {
            *tm = Term::Bound(self.to[i]);
            return
          }
        },
      Term::It => *tm = Term::Bound(self.it),
      _ => self.super_visit_term(tm),
    }
  }
}

#[derive(Clone, Copy, Debug)]
enum PropertyDeclKind<'a> {
  Func(Option<(FuncId, &'a [ConstId])>, Args),
  Pred(Args, bool),
  Mode(&'a DefBody<Formula>),
  None,
}

#[derive(Debug)]
struct PropertiesBuilder<'a> {
  visible: &'a [LocusId],
  kind: PropertyDeclKind<'a>,
  props: Properties,
  formula: Option<Box<Formula>>,
}

impl<'a> PropertiesBuilder<'a> {
  const fn new(visible: &'a [LocusId]) -> Self {
    Self { visible, kind: PropertyDeclKind::None, props: Properties::EMPTY, formula: None }
  }

  fn load_args(
    &mut self, g: &Global, lc: &LocalContext, to_const: &IdxVec<LocusId, ConstId>,
    f: impl FnOnce(Args) -> PropertyDeclKind<'a>,
  ) {
    match *self.visible {
      [v1] => {
        let c1 = to_const[v1];
        self.props.arg1 = v1.0;
        self.kind = f(Args::Unary([c1]));
      }
      [v1, v2] => {
        let c1 = to_const[v1];
        let c2 = to_const[v2];
        if ().eq_type(g, lc, &lc.fixed_var[c1].ty, &lc.fixed_var[c2].ty) {
          self.props.arg1 = v1.0;
          self.props.arg2 = v2.0;
          self.kind = f(Args::Binary([c1, c2]));
        }
      }
      _ => {}
    }
  }

  fn the_formula<const N: usize>(
    &self, args: [ConstId; N], lift: u32, it: u32, tgt: [u32; N],
  ) -> Formula {
    let f = self.formula.as_deref().unwrap();
    f.visit_cloned(&mut InstN::new(args, lift, it, tgt))
  }

  fn reflexivity(&self, lc: &LocalContext, args: [ConstId; 2], pos: bool) -> Formula {
    let ty = &lc.fixed_var[args[0]].ty;
    Formula::forall(ty.clone(), self.the_formula(args, 1, 0, [0, 0]).maybe_neg(pos))
  }

  fn asymmetry(&self, lc: &LocalContext, args: [ConstId; 2], pos1: bool, pos2: bool) -> Formula {
    let ty = &lc.fixed_var[args[0]].ty;
    let f = Formula::mk_and_with(|conj| {
      self.the_formula(args, 2, 0, [0, 1]).maybe_neg(pos1).append_conjuncts_to(conj);
      self.the_formula(args, 2, 0, [1, 0]).maybe_neg(pos2).append_conjuncts_to(conj);
    });
    Formula::forall(ty.clone(), Formula::forall(ty.clone(), f.mk_neg()))
  }

  fn elab_properties(&mut self, elab: &mut Analyzer<'_>, props: &[ast::Property]) {
    for prop in props {
      let (g, lc) = (&elab.g, &elab.lc);
      let thesis = match (prop.kind, &self.kind) {
        (PropertyKind::Symmetry, &PropertyDeclKind::Pred(Args::Binary(args), pos)) =>
          self.asymmetry(lc, args, pos, !pos),
        (PropertyKind::Reflexivity, &PropertyDeclKind::Pred(Args::Binary(args), pos)) =>
          self.reflexivity(lc, args, pos),
        (PropertyKind::Irreflexivity, &PropertyDeclKind::Pred(Args::Binary(args), pos)) =>
          self.reflexivity(lc, args, !pos),
        (PropertyKind::Connectedness, &PropertyDeclKind::Pred(Args::Binary(args), pos)) =>
          self.asymmetry(lc, args, !pos, !pos),
        (PropertyKind::Asymmetry, &PropertyDeclKind::Pred(Args::Binary(args), pos)) =>
          self.asymmetry(lc, args, pos, pos),
        (PropertyKind::Commutativity, &PropertyDeclKind::Func(t, Args::Binary(args))) => {
          let ty = &lc.fixed_var[args[0]].ty;
          eprintln!("elab commutativity <- {self:#?}");
          if let Some((nr, args2)) = t {
            let term = |tgt| {
              let inst = &mut InstN::new(args, 2, 0, tgt);
              let args = args2.iter().map(|&c| Term::Constant(c).visit_cloned(inst)).collect();
              Term::Functor { nr, args }
            };
            Formula::forall(
              ty.clone(),
              Formula::forall(ty.clone(), g.reqs.mk_eq(term([0, 1]), term([1, 0]))),
            )
          } else {
            let f = Formula::mk_and_with(|conj| {
              self.the_formula(args, 3, 0, [1, 2]).append_conjuncts_to(conj);
              self.the_formula(args, 3, 0, [2, 1]).mk_neg().append_conjuncts_to(conj);
            });
            Formula::forall(
              lc.it_type.as_deref().unwrap().clone(),
              Formula::forall(ty.clone(), Formula::forall(ty.clone(), f.mk_neg())),
            )
          }
        }
        (PropertyKind::Idempotence, &PropertyDeclKind::Func(_, Args::Binary(args))) => {
          let ty = &lc.fixed_var[args[0]].ty;
          assert!(lc.it_type.as_ref().unwrap().is_wider_than(g, lc, ty));
          Formula::forall(ty.clone(), self.the_formula(args, 1, 0, [0, 0]))
        }
        (PropertyKind::Involutiveness, &PropertyDeclKind::Func(_, Args::Unary(args))) => {
          let ty = &lc.fixed_var[args[0]].ty;
          let it_ty = lc.it_type.as_deref().unwrap();
          assert!(().eq_type(g, lc, it_ty, ty));
          let f = Formula::mk_and_with(|conj| {
            self.the_formula(args, 2, 0, [1]).append_conjuncts_to(conj);
            self.the_formula(args, 2, 1, [0]).mk_neg().append_conjuncts_to(conj);
          });
          Formula::forall(it_ty.clone(), Formula::forall(it_ty.clone(), f.mk_neg()))
        }
        (PropertyKind::Projectivity, &PropertyDeclKind::Func(_, Args::Unary(args))) => {
          let ty = &lc.fixed_var[args[0]].ty;
          let it_ty = lc.it_type.as_deref().unwrap();
          let wty = &*ty.widening_of(g, it_ty).unwrap();
          assert!(().eq_radices(g, lc, wty, ty));
          assert!(ty.attrs.0.is_subset_of(&wty.attrs.1, |a1, a2| ().eq_attr(g, lc, a1, a2)));
          let f = Formula::mk_and_with(|conj| {
            self.the_formula(args, 2, 0, [1]).append_conjuncts_to(conj);
            self.the_formula(args, 2, 0, [0]).mk_neg().append_conjuncts_to(conj);
          });
          Formula::forall(it_ty.clone(), Formula::forall(ty.clone(), f.mk_neg()))
        }
        (PropertyKind::Sethood, PropertyDeclKind::Mode(value)) => {
          let it_ty = lc.it_type.as_deref().unwrap();
          let f = value.by_cases(|case| {
            let f = Formula::mk_and_with(|conj| {
              case.visit_cloned(&mut AbstractIt(1, 2)).append_conjuncts_to(conj);
              let f = Formula::Pred {
                nr: g.reqs.belongs_to().unwrap(),
                args: Box::new([Term::Bound(BoundId(1)), Term::Bound(BoundId(0))]),
              };
              conj.push(f.mk_neg())
            });
            Formula::forall(Type::SET, Formula::forall(it_ty.clone(), f.mk_neg()).mk_neg()).mk_neg()
          });
          f.mk_neg()
        }
        (PropertyKind::Associativity, PropertyDeclKind::Func(_, Args::Binary(_))) =>
          panic!("associativity declarations are not supported"),
        (PropertyKind::Transitivity, &PropertyDeclKind::Pred(Args::Binary(_), _)) =>
          panic!("transitivity declarations are not supported"),
        (PropertyKind::Abstractness, _) => unreachable!(),
        (k, tgt) => panic!("property {k:?} is not applicable to {tgt:?}"),
      };
      elab.elab_justification(None, &thesis, &prop.just);
      self.props.set(prop.kind);
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
  type Output: Visitable<Descope>;

  /// Changes the thesis from `for x1..xn holds P` to `P`
  /// where `x1..xn` are the fixed_vars introduced since `start`
  fn intro(&mut self, elab: &mut Analyzer, start: usize, istart: u32);

  /// Changes the thesis from `!(conj1 & ... & conjn & rest)` to `!rest`
  fn assume(&mut self, elab: &mut Analyzer, conjs: Vec<Formula>);

  /// Changes the thesis from `!(!(for x1..xn holds !f) & rest)` to `!rest`
  /// (that is, `(ex x1..xn st f) -> rest` to `rest`)
  /// where `x1..xn` are the fixed_vars introduced since `start`
  fn given(&mut self, elab: &mut Analyzer, start: usize, istart: u32, f: Formula);

  /// Changes the thesis from `ex x st P(x)` to `P(term)`
  fn take(&mut self, elab: &mut Analyzer, term: Term);

  /// Changes the thesis from `ex x st P(x)` to `P(v)`,
  /// where `v` is the last `fixed_var` to be introduced
  fn take_as_var(&mut self, elab: &mut Analyzer, v: ConstId) { self.take(elab, Term::Constant(v)); }

  /// Changes the thesis from `conjs & rest` to `rest`
  fn thus(&mut self, elab: &mut Analyzer, conjs: Vec<Formula>);

  fn new_cases(&mut self, elab: &mut Analyzer) -> Self::CaseIterable;

  fn new_cases_iter<'a>(
    &mut self, elab: &mut Analyzer, case: &'a mut Self::CaseIterable,
  ) -> Self::CaseIter<'a>;

  fn new_case(&mut self, _: &mut Analyzer, _: &mut Self::CaseIter<'_>, _: &[Formula]) {}

  fn end_case(&mut self, _: &mut Analyzer, _: &mut Self::CaseIter<'_>, _: Self::Output) {}

  fn end_cases(&mut self, _: &mut Analyzer, _: Self::CaseIter<'_>) {}

  fn new_supposes(&mut self, elab: &mut Analyzer) -> Self::SupposeRecv;

  fn new_suppose(&mut self, _: &mut Analyzer, _: &mut Self::SupposeRecv, _: &[Formula]) {}

  fn end_suppose(&mut self, _: &mut Analyzer, _: &mut Self::SupposeRecv, _: Self::Output) {}

  fn end_supposes(&mut self, _: &mut Analyzer, _: Self::SupposeRecv) {}

  fn end_block(&mut self, elab: &mut Analyzer, end: Position) -> Self::Output;

  fn super_elab_item(&mut self, elab: &mut Analyzer, it: &ast::Item) -> bool {
    match &it.kind {
      ast::ItemKind::Let { .. } => elab.item_header(it, "Let"),
      ast::ItemKind::Assume { .. } => elab.item_header(it, "Assume"),
      ast::ItemKind::Given { .. } => elab.item_header(it, "Given"),
      ast::ItemKind::Take { .. } => elab.item_header(it, "Take"),
      ast::ItemKind::Thus { .. } => elab.item_header(it, "Thus"),
      ast::ItemKind::PerCases { .. } => elab.item_header(it, "PerCases"),
      _ => {}
    }
    match &it.kind {
      ast::ItemKind::Let { var } => {
        let n = elab.lc.fixed_var.len();
        let istart = elab.lc.infer_const.get_mut().len() as u32;
        elab.elab_fixed_vars(var);
        self.intro(elab, n, istart)
      }
      ast::ItemKind::Assume(asm) => {
        let mut conjs = vec![];
        for prop in asm.conds() {
          elab.elab_proposition(prop, true).append_conjuncts_to(&mut conjs);
        }
        self.assume(elab, conjs)
      }
      ast::ItemKind::Given { vars, conds } => {
        let n = elab.lc.fixed_var.len();
        let istart = elab.lc.infer_const.get_mut().len() as u32;
        for var in vars {
          elab.elab_fixed_vars(var);
        }
        let f = Formula::mk_and_with(|conjs| {
          conds.iter().for_each(|prop| elab.elab_proposition(prop, true).append_conjuncts_to(conjs))
        });
        self.given(elab, n, istart, f);
      }
      ast::ItemKind::Take { var: None, term } => {
        let term = elab.elab_intern_term(term.as_deref().unwrap());
        self.take(elab, term)
      }
      ast::ItemKind::Take { var: Some(_), term } => {
        let term = elab.elab_intern_term(term.as_deref().unwrap());
        let ty = term.get_type(&elab.g, &elab.lc, false);
        let v = elab.lc.fixed_var.push(FixedVar { ty, def: Some((Box::new(term), false)) });
        self.take_as_var(elab, v)
      }
      ast::ItemKind::Thus(stmt) => {
        let f = elab.elab_stmt(stmt);
        self.thus(elab, f.into_conjuncts())
      }
      ast::ItemKind::PerCases { just, kind: CaseKind::Case, blocks } => {
        let mut iter = self.new_cases(elab);
        let mut iter = self.new_cases_iter(elab, &mut iter);
        let f = Formula::mk_and_with(|disjs| {
          for bl in blocks {
            let (case, o) = elab.scope(None, true, false, |elab| {
              let case = Formula::mk_and_with(|conjs| {
                for prop in bl.hyp.conds() {
                  elab.elab_proposition(prop, true).append_conjuncts_to(conjs);
                }
                self.new_case(elab, &mut iter, conjs)
              });
              (case, self.elab_proof(elab, &bl.items, bl.end))
            });
            case.mk_neg().append_conjuncts_to(disjs);
            self.end_case(elab, &mut iter, o);
          }
          self.end_cases(elab, iter);
        });
        elab.elab_justification(None, &f.mk_neg(), just);
        return false
      }
      ast::ItemKind::PerCases { just, kind: CaseKind::Suppose, blocks } => {
        let f = Formula::mk_and_with(|disjs| {
          let mut recv = self.new_supposes(elab);
          for bl in blocks {
            let (case, o) = elab.scope(None, true, false, |elab| {
              let case = Formula::mk_and_with(|conjs| {
                for prop in bl.hyp.conds() {
                  elab.elab_proposition(prop, true).append_conjuncts_to(conjs);
                }
                self.new_suppose(elab, &mut recv, conjs);
              });
              (case, self.elab_proof(elab, &bl.items, bl.end))
            });
            case.mk_neg().append_conjuncts_to(disjs);
            self.end_suppose(elab, &mut recv, o);
          }
          self.end_supposes(elab, recv)
        });
        elab.elab_justification(None, &f.mk_neg(), just);
        return false
      }
      _ => elab.elab_stmt_item(it),
    }
    true
  }

  fn elab_item(&mut self, elab: &mut Analyzer, item: &ast::Item) -> bool {
    self.super_elab_item(elab, item)
  }

  fn elab_proof(
    &mut self, elab: &mut Analyzer, items: &[ast::Item], end: Position,
  ) -> Self::Output {
    for item in items {
      if !self.elab_item(elab, item) {
        break
      }
    }
    self.end_block(elab, end)
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
    Formula::forall(it_type.clone(), f.maybe_neg(pos))
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
  fn mk_eq(&self, _: &Global, other: &Self) -> Formula { self.clone().mk_iff(other.clone()) }
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
    Box::new(Formula::forall(it_type.clone(), Formula::forall(it_type2, *scope)))
  }
}

impl DefBody<Term> {
  fn mk_coherence(&self, it_type: &Type) -> Box<Formula> {
    self.by_cases(|case| {
      Formula::Is { term: Box::new(case.clone()), ty: Box::new(it_type.clone()) }.mk_neg()
    })
  }
}

fn mk_mode_coherence(nr: ModeId, attrs: &Attrs, args: Vec<Term>, it_type: &Type) -> Box<Formula> {
  Box::new(Formula::forall(
    Type {
      kind: TypeKind::Mode(nr),
      attrs: (Attrs::EMPTY, attrs.visit_cloned(&mut Inst::new(&args))),
      args,
    },
    Formula::Is { term: Box::new(Term::Bound(BoundId(0))), ty: Box::new(it_type.clone()) },
  ))
}

fn mk_func_coherence(nr: FuncId, args: Box<[Term]>, it_type: &Type) -> Box<Formula> {
  Box::new(Formula::Is {
    term: Box::new(Term::Functor { nr, args }),
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

  fn as_formula(&self, g: &Global) -> Box<Formula> {
    match self {
      DefValue::Term(value) => value.by_cases(|case| case.it_eq(g).mk_neg()),
      DefValue::Formula(value) => value.by_cases(|case| case.it_eq(g).mk_neg()),
    }
  }
}

struct WithThesis;

impl ReadProof for WithThesis {
  type CaseIterable = Formula;
  type CaseIter<'a> = std::slice::Iter<'a, Formula>;
  type SupposeRecv = ();
  type Output = ();

  fn intro(&mut self, elab: &mut Analyzer, start: usize, _: u32) {
    let mut thesis = (true, elab.thesis.take().unwrap());
    elab.forall_telescope(start, false, false, &mut thesis);
    elab.thesis = Some(Box::new(thesis.1.maybe_neg(thesis.0)));
  }

  fn assume(&mut self, elab: &mut Analyzer, conjs: Vec<Formula>) {
    let thesis = elab.thesis.take().unwrap().mk_neg().into_conjuncts();
    elab.thesis = Some(Box::new(Formula::mk_and(elab.and_telescope(conjs, true, thesis)).mk_neg()))
  }

  fn given(&mut self, elab: &mut Analyzer, start: usize, istart: u32, f: Formula) {
    let mut f = f.mk_neg();
    let end = elab.lc.fixed_var.len();
    elab.lc.mk_forall(start..end, istart, false, &mut f);
    self.assume(elab, vec![f.mk_neg()]);
  }

  fn take(&mut self, elab: &mut Analyzer, term: Term) {
    let mut thesis = (false, elab.thesis.take().unwrap());
    elab.inst_forall(&term, true, true, &mut thesis);
    elab.thesis = Some(Box::new(thesis.1.maybe_neg(!thesis.0)));
  }

  fn thus(&mut self, elab: &mut Analyzer, f: Vec<Formula>) {
    let thesis = elab.thesis.take().unwrap().into_conjuncts();
    elab.thesis = Some(Box::new(Formula::mk_and(elab.and_telescope(f, false, thesis))))
  }

  fn new_cases(&mut self, elab: &mut Analyzer) -> Formula {
    elab.thesis.as_ref().unwrap().clone().mk_neg()
  }

  fn new_cases_iter<'a>(&mut self, _: &mut Analyzer, case: &'a mut Formula) -> Self::CaseIter<'a> {
    case.conjuncts().iter()
  }

  fn new_case(&mut self, elab: &mut Analyzer, case: &mut Self::CaseIter<'_>, f: &[Formula]) {
    elab.thesis = Some(Box::new(case.next().cloned().unwrap_or(Formula::True).mk_neg()));
    self.thus(elab, f.to_vec())
  }

  fn end_cases(&mut self, elab: &mut Analyzer, mut case: Self::CaseIter<'_>) {
    assert!(case.next().is_none());
    **elab.thesis.as_mut().unwrap() = Formula::True;
  }

  fn new_supposes(&mut self, _: &mut Analyzer) {}

  fn end_supposes(&mut self, elab: &mut Analyzer, _: ()) {
    **elab.thesis.as_mut().unwrap() = Formula::True;
  }

  fn end_block(&mut self, elab: &mut Analyzer, end: Position) {
    let f = elab.thesis.as_deref().unwrap();
    if !matches!(f, Formula::True) {
      eprintln!(
        "error at {}:{end:?}: block incomplete; thesis at end of block:\n  {f:?}",
        elab.article
      );
      panic!("{end:?}: block incomplete")
    }
  }
}

#[derive(Debug)]
enum ProofStep {
  Let { range: Range<usize>, istart: u32 },
  Assume { conjs: Vec<Formula> },
  Given { range: Range<usize>, istart: u32, not_f: Formula },
  TakeAsVar { range: Range<usize>, istart: u32 },
  Thus { conjs: Vec<Formula> },
  Break(bool),
}

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
    let conjs = elab.thesis.take().map_or_else(Vec::new, |f| f.into_conjuncts());
    let mut rec = Reconstruction { pos, conjs };
    loop {
      match self.stack.pop().unwrap() {
        ProofStep::Let { range, istart } => {
          let mut f = Formula::mk_and(std::mem::take(rec.as_pos(true)));
          elab.lc.mk_forall(range, istart, true, &mut f);
          rec.conjs = vec![f];
        }
        ProofStep::Assume { mut conjs } => {
          let rest = rec.as_pos(false);
          std::mem::swap(&mut conjs, rest);
          rest.append(&mut conjs)
        }
        ProofStep::Given { range, istart, mut not_f } => {
          let rest = rec.as_pos(false);
          elab.lc.mk_forall(range, istart, true, &mut not_f);
          rest.insert(0, not_f.mk_neg())
        }
        ProofStep::TakeAsVar { range, istart } => {
          let mut f = Formula::mk_and(std::mem::take(rec.as_pos(false)));
          elab.lc.mk_forall(range, istart, true, &mut f);
          rec.conjs = vec![f];
        }
        ProofStep::Thus { mut conjs } => {
          let rest = rec.as_pos(true);
          std::mem::swap(&mut conjs, rest);
          rest.append(&mut conjs)
        }
        ProofStep::Break(pos2) => {
          assert_eq!(pos, pos2);
          return Formula::mk_and(std::mem::take(rec.as_pos(pos)))
        }
      }
    }
  }
}

impl ReadProof for ReconstructThesis {
  type CaseIterable = ();
  type CaseIter<'a> = ();
  type SupposeRecv = Option<Box<Formula>>;
  type Output = Formula;

  fn intro(&mut self, elab: &mut Analyzer, start: usize, istart: u32) {
    match self.stack.last_mut() {
      Some(ProofStep::Let { range, .. }) if range.end == start =>
        range.end = elab.lc.fixed_var.len(),
      _ => self.stack.push(ProofStep::Let { range: start..elab.lc.fixed_var.len(), istart }),
    }
  }

  fn assume(&mut self, _: &mut Analyzer, mut conjs: Vec<Formula>) {
    if let Some(ProofStep::Assume { conjs: rest }) = self.stack.last_mut() {
      rest.append(&mut conjs)
    } else {
      self.stack.push(ProofStep::Assume { conjs })
    }
  }

  fn given(&mut self, elab: &mut Analyzer, start: usize, istart: u32, f: Formula) {
    self.stack.push(ProofStep::Given {
      range: start..elab.lc.fixed_var.len(),
      istart,
      not_f: f.mk_neg(),
    })
  }

  fn take(&mut self, _: &mut Analyzer, _: Term) { panic!("take steps are not reconstructible") }

  fn take_as_var(&mut self, elab: &mut Analyzer, v: ConstId) {
    if !matches!(self.stack.last(), Some(ProofStep::TakeAsVar { .. })) {
      self.stack.push(ProofStep::TakeAsVar {
        range: v.0 as usize..elab.lc.fixed_var.len(),
        istart: elab.lc.infer_const.get_mut().len() as u32,
      })
    }
  }

  fn thus(&mut self, _: &mut Analyzer, mut f: Vec<Formula>) {
    if let Some(ProofStep::Thus { conjs }) = self.stack.last_mut() {
      conjs.append(&mut f)
    } else {
      self.stack.push(ProofStep::Thus { conjs: f })
    }
  }

  fn new_cases(&mut self, _: &mut Analyzer) { self.stack.push(ProofStep::Break(false)) }
  fn new_cases_iter(&mut self, _: &mut Analyzer, _: &mut ()) {}
  fn new_case(&mut self, _: &mut Analyzer, _: &mut (), conjs: &[Formula]) {
    self.stack.push(ProofStep::Break(true));
    self.stack.push(ProofStep::Thus { conjs: conjs.to_vec() })
  }

  fn end_case(&mut self, elab: &mut Analyzer, _: &mut Self::CaseIter<'_>, f: Formula) {
    self.assume(elab, f.mk_neg().into_conjuncts());
  }

  fn end_cases(&mut self, elab: &mut Analyzer, _: ()) {
    let f = self.reconstruct(elab, false);
    self.thus(elab, f.mk_neg().into_conjuncts())
  }

  fn new_supposes(&mut self, _: &mut Analyzer) -> Self::SupposeRecv { None }

  fn new_suppose(&mut self, _: &mut Analyzer, _: &mut Self::SupposeRecv, _: &[Formula]) {
    self.stack.push(ProofStep::Break(true))
  }

  fn end_suppose(&mut self, elab: &mut Analyzer, recv: &mut Self::SupposeRecv, f: Formula) {
    if let Some(thesis) = recv {
      assert!(().eq_formula(&elab.g, &elab.lc, thesis, &f))
    } else {
      *recv = Some(Box::new(f))
    }
  }

  fn end_supposes(&mut self, elab: &mut Analyzer, recv: Self::SupposeRecv) {
    self.thus(elab, recv.unwrap().into_conjuncts())
  }

  fn end_block(&mut self, elab: &mut Analyzer, _: Position) -> Formula {
    self.reconstruct(elab, true)
  }
}

struct ToLocus<'a> {
  infer_const: &'a IdxVec<InferId, Assignment>,
  to_locus: &'a IdxVec<ConstId, Option<LocusId>>,
}

impl ToLocus<'_> {
  fn get(&self, c: ConstId) -> LocusId {
    self.to_locus.get(c).and_then(|l| *l).expect("local constant in exported item")
  }
}

impl VisitMut for ToLocus<'_> {
  fn visit_term(&mut self, tm: &mut Term) {
    loop {
      match *tm {
        Term::Constant(c) => *tm = Term::Locus(self.get(c)),
        Term::Infer(n) => {
          *tm = self.infer_const[n].def.clone();
          continue
        }
        _ => self.super_visit_term(tm),
      }
      break
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
  to_locus: IdxVec<ConstId, Option<LocusId>>,
  to_const: IdxVec<LocusId, ConstId>,
  primary: IdxVec<LocusId, Type>,
  assums: Vec<Formula>,
  defthms: Vec<(Option<LabelId>, Box<Formula>)>,
  needs_round_up: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct CheckAccess(u64);
impl CheckAccess {
  const fn new(n: usize) -> Self {
    assert!(n < u64::BITS as usize);
    Self(0)
  }

  const fn get(&self, n: LocusId) -> bool { self.0 & (1 << n.0 as u64) != 0 }
  fn set(&mut self, n: LocusId) { self.0 |= 1 << n.0 as u64 }

  fn with(primary: &[Type], f: impl FnOnce(&mut Self)) {
    let mut occ = Self::new(primary.len());
    f(&mut occ);
    for (i, ty) in primary.iter().enumerate().rev() {
      assert!(occ.get(LocusId::from_usize(i)));
      occ.visit_type(ty)
    }
  }
}
impl Pattern {
  fn check_access(&self) {
    CheckAccess::with(&self.primary, |occ| self.visible.iter().for_each(|&v| occ.set(v)))
  }
}

impl Visit for CheckAccess {
  fn visit_term(&mut self, tm: &Term) {
    match *tm {
      Term::Locus(i) => self.set(i),
      _ => self.super_visit_term(tm),
    }
  }
}

struct PatternFuncResult {
  nr: FuncId,
  args: Box<[Term]>,
  var_set: CheckAccess,
}

impl BlockReader {
  fn new(kind: BlockKind, lc: &LocalContext) -> Self {
    Self {
      kind,
      to_locus: IdxVec::from_default(lc.fixed_var.len()),
      to_const: IdxVec::default(),
      primary: Default::default(),
      assums: vec![],
      defthms: vec![],
      needs_round_up: false,
    }
  }

  fn to_locus<R>(&self, elab: &Analyzer, f: impl FnOnce(&mut ToLocus<'_>) -> R) -> R {
    f(&mut ToLocus { infer_const: &elab.lc.infer_const.borrow(), to_locus: &self.to_locus })
  }

  fn locus(&self, c: ConstId) -> LocusId {
    self.to_locus.get(c).and_then(|l| *l).expect("local constant in exported item")
  }

  fn after_scope(self, elab: &mut Analyzer) {
    for (label, mut thm) in self.defthms {
      thm.visit(&mut elab.intern_const());
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
      .mk_neg()
    }
    for ty in self.primary.0.iter().rev() {
      al.0 -= 1;
      f = Box::new(Formula::ForAll { dom: Box::new(ty.visit_cloned(&mut al)), scope: f })
    }
    f
  }

  fn check_compatible_args(&self, subst: &Subst<'_>) {
    let n = self.primary.len().checked_sub(subst.subst_term.len()).expect("too many args");
    for ((i, _), tm) in self.primary.enum_iter().skip(n).zip(&*subst.subst_term) {
      if let Some(tm) = tm {
        if let Term::Constant(c) = **tm {
          if self.locus(c) == i {
            continue
          }
        }
      }
      panic!("incorrect args to redefinition")
    }
  }

  fn elab_func_def(
    &mut self, elab: &mut Analyzer, pat: &ast::PatternFunc, it: &ast::Definition,
    spec: Option<&ast::Type>, def: Option<&ast::Definiens>,
  ) {
    let fmt = elab.formats[&Format::Func(pat.to_format())];
    let mut cc = CorrConds::new();
    let primary: Box<[_]> = self.primary.0.iter().cloned().collect();
    let visible: Box<[_]> = pat.args().iter().map(|v| self.locus(v.var())).collect();
    let mut properties = PropertiesBuilder::new(&visible);
    let (redefines, superfluous, it_type);
    if it.redef {
      let args: Box<[_]> = pat.args().iter().map(|v| Term::Constant(v.var())).collect();
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
      properties.props = c.properties.offset(superfluous);
      it_type = elab.elab_spec(spec, &c.ty.clone());
      if spec.is_some() {
        let args2 =
          self.to_const.0[superfluous as usize..].iter().map(|c| Term::Constant(*c)).collect();
        cc.0[CorrCondKind::Coherence] = Some(mk_func_coherence(nr, args2, &it_type));
      }
    } else {
      (redefines, superfluous) = (None, 0);
      it_type = spec.map_or(Type::ANY, |ty| elab.elab_type(ty));
    }
    elab.lc.it_type = Some(Box::new(it_type));
    let value = def.as_ref().map(|def| elab.elab_def_value(&def.kind, true));
    let mut it_type = elab.lc.it_type.take().unwrap();
    if let Some(value) = &value {
      cc.0[CorrCondKind::Consistency] = value.mk_consistency(&elab.g, Some(&it_type));
      if let Some(nr) = redefines {
        let args2 =
          self.to_const.0[superfluous as usize..].iter().map(|c| Term::Constant(*c)).collect();
        let defined = Term::Functor { nr, args: args2 }.it_eq(&elab.g);
        cc.0[CorrCondKind::Compatibility] =
          Some(value.mk_compatibility(&elab.g, Some(&it_type), &defined));
      }
      properties.formula = Some(value.as_formula(&elab.g))
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
    if self.assums.is_empty() {
      properties.load_args(&elab.g, &elab.lc, &self.to_const, |args| {
        PropertyDeclKind::Func(
          redefines.filter(|_| it.redef).map(|t| (t, &self.to_const.0[superfluous as usize..])),
          args,
        )
      });
    }
    elab.lc.it_type = Some(it_type);
    properties.elab_properties(elab, &it.props);
    it_type = elab.lc.it_type.take().unwrap();
    self.to_locus(elab, |l| it_type.visit(l));
    let n;
    if it.redef && value.is_none() && superfluous == 0 && it.props.is_empty() {
      n = redefines.unwrap()
    } else {
      let primary = primary.clone();
      n = elab.g.constrs.functor.push(TyConstructor {
        c: Constructor { primary, redefines, superfluous, properties: properties.props },
        ty: (*it_type).clone(),
      });
      elab.push_constr(ConstrKind::Func(n));
    }
    if let Some(mut value) = value {
      self.to_locus(elab, |l| value.visit(l));
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
        c: ConstrDef { constr: ConstrKind::Func(redefines.unwrap_or(n)), primary },
        assumptions: Formula::mk_and(self.assums.clone()),
        value,
      });
    }
    let pat = Pattern { kind: PatternKind::Func(n), fmt, primary, visible, pos: true };
    pat.check_access();
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
    let visible: Box<[_]> = pat.args.iter().map(|v| self.locus(v.var())).collect();
    let mut properties = PropertiesBuilder::new(&visible);
    let args: Box<[_]> = pat.args.iter().map(|v| Term::Constant(v.var())).collect();
    let (redefines, superfluous, pos);
    if it.redef {
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
      properties.props = c.properties.offset(superfluous)
    } else {
      (redefines, superfluous, pos) = (None, 0, true)
    }
    let value = def.as_ref().map(|def| elab.elab_def_value(&def.kind, pos));
    if let Some(value) = &value {
      cc.0[CorrCondKind::Consistency] = value.mk_consistency(&elab.g, None);
      if let Some(nr) = redefines {
        let args2 =
          self.to_const.0[superfluous as usize..].iter().map(|c| Term::Constant(*c)).collect();
        cc.0[CorrCondKind::Compatibility] =
          Some(value.mk_compatibility(&elab.g, None, &Formula::Pred { nr, args: args2 }));
      }
      properties.formula = Some(value.as_formula(&elab.g))
    } else if let Some(nr) = redefines {
      let args2 =
        self.to_const.0[superfluous as usize..].iter().map(|c| Term::Constant(*c)).collect();
      properties.formula = Some(Box::new(Formula::Pred { nr, args: args2 }))
    }
    elab.elab_corr_conds(cc, &it.conds, &it.corr);
    if self.assums.is_empty() {
      properties
        .load_args(&elab.g, &elab.lc, &self.to_const, |args| PropertyDeclKind::Pred(args, pos));
    }
    properties.elab_properties(elab, &it.props);
    let n;
    if it.redef && superfluous == 0 && it.props.is_empty() {
      n = redefines.unwrap()
    } else {
      let p = primary.clone();
      let c = Constructor { primary: p, redefines, superfluous, properties: properties.props };
      n = elab.g.constrs.predicate.push(c);
      elab.push_constr(ConstrKind::Pred(n));
    }
    if let Some(value) = value {
      let DefValue::Formula(mut value) = value else { unreachable!() };
      self.to_locus(elab, |l| value.visit(l));
      let formals = self.primary.enum_iter().map(|(i, _)| Term::Locus(i)).collect();
      let mut f = value.defthm_for(&elab.g, &Formula::Pred { nr: n, args: formals });
      AbstractLocus(self.primary.len() as u32).visit_formula(&mut f);
      let thm = self.forall_locus(f);
      self.defthms.push((def.as_ref().unwrap().label.as_ref().map(|l| l.id.0), thm));
      elab.r.read_definiens(&Definiens {
        essential: (superfluous..primary.len() as u8).map(LocusId).collect(),
        c: ConstrDef { constr: ConstrKind::Pred(redefines.unwrap_or(n)), primary: primary.clone() },
        assumptions: Formula::mk_and(self.assums.clone()),
        value: DefValue::Formula(value),
      });
    }
    let pat = Pattern { kind: PatternKind::Pred(n), fmt, primary, visible, pos };
    pat.check_access();
    elab.r.lc.formatter.push(&elab.r.g.constrs, &pat);
    elab.r.notations.predicate.push(pat)
  }

  fn elab_mode_def(
    &mut self, elab: &mut Analyzer, pat: &ast::PatternMode, kind: &ast::DefModeKind,
    it: &ast::Definition,
  ) {
    let fmt = elab.formats[&Format::Mode(pat.to_format())];
    let mut cc = CorrConds::new();
    let primary: Box<[_]> = self.primary.0.iter().cloned().collect();
    let visible: Box<[_]> = pat.args.iter().map(|v| self.locus(v.var())).collect();
    let mut properties = PropertiesBuilder::new(&visible);
    match kind {
      ast::DefModeKind::Expandable { expansion } => {
        let mut expansion = Box::new(elab.elab_type(expansion));
        elab.elab_corr_conds(cc, &it.conds, &it.corr);
        properties.elab_properties(elab, &it.props);
        self.to_locus(elab, |l| expansion.visit(l));
        let kind = PatternKind::ExpandableMode { expansion };
        let pat = Pattern { kind, fmt, primary, visible, pos: true };
        pat.check_access();
        elab.r.lc.formatter.push(&elab.r.g.constrs, &pat);
        elab.r.notations.mode.push(pat)
      }
      ast::DefModeKind::Standard { spec, def } => {
        let (args, redefines, superfluous, it_type);
        if it.redef {
          args = pat.args.iter().map(|v| Term::Constant(v.var())).collect::<Box<[_]>>();
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
            properties.props.set(PropertyKind::Sethood)
          }
          it_type = elab.elab_spec(spec.as_deref(), &tgt);
          if spec.is_some() {
            let args2 =
              self.to_const.0[superfluous as usize..].iter().map(|c| Term::Constant(*c)).collect();
            cc.0[CorrCondKind::Coherence] =
              Some(mk_mode_coherence(nr, &tgt.attrs.1, args2, &it_type));
          }
        } else {
          (args, redefines, superfluous) = Default::default();
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
          properties.kind = PropertyDeclKind::Mode(value);
        }
        if let TypeKind::Mode(nr) = it_type.kind {
          if elab.g.constrs.mode[nr].properties.get(PropertyKind::Sethood) {
            properties.props.set(PropertyKind::Sethood)
          }
        }
        elab.elab_corr_conds(cc, &it.conds, &it.corr);
        elab.lc.it_type = Some(it_type);
        properties.elab_properties(elab, &it.props);
        it_type = elab.lc.it_type.take().unwrap();
        self.to_locus(elab, |l| it_type.visit(l));
        let n;
        if it.redef && value.is_none() && superfluous == 0 {
          n = redefines.unwrap()
        } else {
          let primary = primary.clone();
          n = elab.g.constrs.mode.push(TyConstructor {
            c: Constructor { primary, redefines, superfluous, properties: properties.props },
            ty: (*it_type).clone(),
          });
          elab.push_constr(ConstrKind::Mode(n));
        }
        if let Some(value) = value {
          let DefValue::Formula(mut value) = value else { unreachable!() };
          self.to_locus(elab, |l| value.visit(l));
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
            c: ConstrDef { constr: ConstrKind::Mode(redefines.unwrap_or(n)), primary },
            assumptions: Formula::mk_and(self.assums.clone()),
            value: DefValue::Formula(value),
          });
        }
        let pat = Pattern { kind: PatternKind::Mode(n), fmt, primary, visible, pos: true };
        pat.check_access();
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
    let visible: Box<[_]> = pat.args.iter().map(|v| self.locus(v.var())).collect();
    let args: Box<[_]>;
    let (redefines, superfluous, pos) = if it.redef {
      args = pat.args.iter().map(|v| Term::Constant(v.var())).collect();
      let pat = elab.notations.attribute.iter().rev().find(|pat| {
        pat.fmt == fmt
          && !matches!(pat.kind, PatternKind::Attr(nr)
              if elab.g.constrs.attribute[nr].redefines.is_some())
          && matches!(pat.check_types(&elab.g, &elab.lc, &args),
            Some(subst) if { self.check_compatible_args(&subst); true })
      });
      let pat = pat.expect("type error");
      let PatternKind::Attr(nr) = pat.kind else { unreachable!() };
      (Some(nr), (self.primary.len() - pat.primary.len()) as u8, pat.pos)
    } else {
      args = Box::new([]);
      (None, 0, true)
    };
    let value = def.as_ref().map(|def| elab.elab_def_value(&def.kind, pos));
    if let Some(value) = &value {
      cc.0[CorrCondKind::Consistency] = value.mk_consistency(&elab.g, None);
      if let Some(nr) = redefines {
        cc.0[CorrCondKind::Compatibility] =
          Some(value.mk_compatibility(&elab.g, None, &Formula::Attr { nr, args }));
      }
    }
    elab.elab_corr_conds(cc, &it.conds, &it.corr);
    let mut properties = PropertiesBuilder::new(&visible);
    properties.elab_properties(elab, &it.props);
    let n;
    if it.redef && superfluous == 0 && it.props.is_empty() {
      n = redefines.unwrap()
    } else {
      let p = primary.clone();
      n = elab.g.constrs.attribute.push(TyConstructor {
        c: Constructor { primary: p, redefines, superfluous, properties: properties.props },
        ty: self.primary.0.last().unwrap().clone(),
      });
      elab.push_constr(ConstrKind::Attr(n));
    }
    if let Some(value) = value {
      let DefValue::Formula(mut value) = value else { unreachable!() };
      self.to_locus(elab, |l| value.visit(l));
      let formals = (superfluous..self.primary.len() as u8).map(LocusId).map(Term::Locus).collect();
      let mut f =
        value.defthm_for(&elab.g, &Formula::Attr { nr: redefines.unwrap_or(n), args: formals });
      AbstractLocus(self.primary.len() as u32).visit_formula(&mut f);
      let thm = self.forall_locus(f);
      self.defthms.push((def.as_ref().unwrap().label.as_ref().map(|l| l.id.0), thm));
      elab.r.read_definiens(&Definiens {
        essential: (superfluous..primary.len() as u8).map(LocusId).collect(),
        c: ConstrDef { constr: ConstrKind::Attr(redefines.unwrap_or(n)), primary: primary.clone() },
        assumptions: Formula::mk_and(self.assums.clone()),
        value: DefValue::Formula(value),
      });
    }
    let pat = Pattern { kind: PatternKind::Attr(n), fmt, primary, visible, pos };
    pat.check_access();
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
      primary: struct_primary.clone(),
      visible: it.pat.args.iter().map(|v| self.locus(v.var())).collect(),
      pos: true,
    };
    struct_pat.check_access();
    elab.r.lc.formatter.push(&elab.r.g.constrs, &struct_pat);
    elab.r.notations.struct_mode.push(struct_pat);

    let struct_ty = Type {
      kind: TypeKind::Struct(struct_id),
      attrs: (Attrs::EMPTY, Attrs::EMPTY),
      args: formals.clone(),
    };
    let fixed_vars = elab.lc.fixed_var.len();
    let base = self.primary.len() as u8;
    self.to_locus.0.resize(fixed_vars, None);
    let mut cur_locus = LocusId(base);
    for group in &it.fields {
      let ty = elab.elab_intern_type(&group.ty);
      for _ in &group.vars {
        elab.lc.fixed_var.push(FixedVar { ty: ty.clone(), def: None });
        self.to_locus.0.push(Some(cur_locus.fresh()));
      }
    }
    let mut field_tys = elab.lc.fixed_var.0.drain(fixed_vars..).map(|v| v.ty).collect_vec();
    self.to_locus(elab, |l| field_tys.visit(l));
    let aggr_primary: Box<[_]> = self.primary.0.iter().chain(&field_tys).cloned().collect();
    let mut fields: Vec<SelId> = vec![];
    let aggr_id = AggrId::from_usize(elab.g.constrs.aggregate.len());
    let aggr_pat = Pattern {
      kind: PatternKind::Aggr(aggr_id),
      fmt: elab.formats[&Format::Aggr(it.pat.to_aggr_format())],
      primary: aggr_primary.clone(),
      visible: (base..cur_locus.0).map(LocusId).collect(),
      pos: true,
    };
    aggr_pat.check_access();
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
          primary: sel_primary_it.clone().collect(),
          visible: Box::new([LocusId(base)]),
          pos: true,
        };
        sel_pat.check_access();
        elab.r.lc.formatter.push(&elab.r.g.constrs, &sel_pat);
        elab.r.notations.selector.push(sel_pat);
        new_fields.push(sel_id);
        mk_sel.terms.push(Err(sel_id));
        fields.push(sel_id);
      }
    }

    assert!(prefixes.iter().all(|prefix| prefix.is_empty()), "structure does not extend parent");
    self.to_locus(elab, |l| parents.visit(l));

    let mut c = Constructor::new(sel_primary_it.clone().collect());
    c.properties.set(PropertyKind::Abstractness);
    let attr_primary = sel_primary_it.collect();
    let attr_id = elab.g.constrs.attribute.push(TyConstructor { c, ty: struct_ty.clone() });
    let attr_pat = Pattern {
      kind: PatternKind::Attr(attr_id),
      fmt: FormatId::STRICT,
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

    let attrs = Attrs::Consistent(vec![Attr { nr: attr_id, pos: true, args: formals.into() }]);
    std::mem::swap(&mut self.primary, &mut elab.lc.locus_ty);
    elab.register_cluster(attrs.clone(), struct_primary.clone(), struct_ty.clone());
    std::mem::swap(&mut self.primary, &mut elab.lc.locus_ty);

    let struct_id2 = elab.g.constrs.struct_mode.push(StructMode {
      c: Constructor::new(struct_primary),
      parents,
      aggr: aggr_id,
      fields: fields.clone().into(),
    });
    assert!(struct_id == struct_id2);

    let mut aggr_ty = struct_ty;
    aggr_ty.attrs = (attrs.clone(), attrs);
    let aggr_id2 = elab.g.constrs.aggregate.push(Aggregate {
      c: TyConstructor { c: Constructor::new(aggr_primary), ty: aggr_ty },
      base,
      fields: fields.into(),
    });
    assert!(aggr_id == aggr_id2);
  }

  fn elab_exist_reg(
    &mut self, elab: &mut Analyzer, it: &ast::Cluster, concl: &[ast::Attr], ty: &ast::Type,
  ) {
    let mut ty = elab.elab_type(ty);
    let mut attrs = ty.attrs.0.clone();
    let f = Formula::mk_and_with(|conjs| {
      for attr in concl {
        let attr = elab.elab_attr(attr, true, &mut ty);
        let args = attr.args.iter().cloned().chain([Term::Bound(BoundId(0))]).collect();
        conjs.push(Formula::Attr { nr: attr.nr, args }.maybe_neg(attr.pos));
        attrs.insert(&elab.g.constrs, attr);
      }
    });
    let (kind, args) = match ty.kind {
      TypeKind::Mode(nr) => {
        let (n, args) = Type::adjust(nr, &ty.args, &elab.g.constrs);
        (TypeKind::Mode(n), args)
      }
      _ => (ty.kind, &*ty.args),
    };
    let mut ty2 = Type { kind, attrs: ty.attrs.clone(), args: args.to_vec() };
    let mut cc = CorrConds::new();
    cc.0[CorrCondKind::Existence] = Some(Box::new(Formula::forall(ty, f.mk_neg()).mk_neg()));
    elab.elab_corr_conds(cc, &it.conds, &it.corr);

    let primary: Box<[_]> = self.primary.0.iter().cloned().collect();
    self.to_locus(elab, |l| {
      attrs.visit(l);
      ty2.visit(l);
    });
    CheckAccess::with(&primary, |occ| {
      occ.visit_attrs(&attrs);
      occ.visit_terms(&ty2.args);
    });
    std::mem::swap(&mut self.primary, &mut elab.lc.locus_ty);
    elab.register_cluster(attrs, primary, ty2);
    std::mem::swap(&mut self.primary, &mut elab.lc.locus_ty);
  }

  fn elab_cond_reg(
    &mut self, elab: &mut Analyzer, it: &ast::Cluster, antecedent: &[ast::Attr],
    concl: &[ast::Attr], ty: &ast::Type,
  ) {
    let mut ty = elab.elab_type(ty);
    let (kind, args) = match ty.kind {
      TypeKind::Mode(nr) => {
        let (n, args) = Type::adjust(nr, &ty.args, &elab.g.constrs);
        (TypeKind::Mode(n), args)
      }
      _ => (ty.kind, &*ty.args),
    };
    let mut ty2 = Type { kind, attrs: (Attrs::EMPTY, Attrs::EMPTY), args: args.to_vec() };

    let (mut attrs1, mut attrs2) = (ty.attrs.0.clone(), ty.attrs.0.clone());
    let f = Formula::mk_and_with(|conjs| {
      for attr in antecedent {
        let attr = elab.elab_attr(attr, true, &mut ty);
        let args = attr.args.iter().cloned().chain([Term::Bound(BoundId(0))]).collect();
        conjs.push(Formula::Attr { nr: attr.nr, args }.maybe_neg(attr.pos));
        attrs1.insert(&elab.g.constrs, attr);
      }
      let f = Formula::mk_and_with(|conjs| {
        for attr in concl {
          let attr = elab.elab_attr(attr, true, &mut ty);
          let args = attr.args.iter().cloned().chain([Term::Bound(BoundId(0))]).collect();
          conjs.push(Formula::Attr { nr: attr.nr, args }.maybe_neg(attr.pos));
          attrs2.insert(&elab.g.constrs, attr);
        }
      });
      f.mk_neg().append_conjuncts_to(conjs)
    });
    let mut cc = CorrConds::new();
    cc.0[CorrCondKind::Coherence] = Some(Box::new(Formula::forall(ty, f.mk_neg())));
    elab.elab_corr_conds(cc, &it.conds, &it.corr);

    let primary: Box<[_]> = self.primary.0.iter().cloned().collect();
    self.to_locus(elab, |l| {
      attrs1.visit(l);
      attrs2.visit(l);
      ty2.visit(l);
    });
    CheckAccess::with(&primary, |occ| {
      occ.visit_attrs(&attrs1);
      occ.visit_terms(&ty2.args);
    });
    let Attrs::Consistent(_) = attrs1 else { panic!("inconsistent cluster antecedent") };
    let Attrs::Consistent(_) = attrs2 else { panic!("inconsistent cluster consequent") };
    elab.read_conditional_cluster(ConditionalCluster {
      cl: Cluster { primary, consequent: (attrs2.clone(), attrs2) },
      ty: Box::new(ty2),
      antecedent: attrs1,
    });
    self.needs_round_up = true;
  }

  fn elab_func_reg(
    &mut self, elab: &mut Analyzer, it: &ast::Cluster, term: &ast::Term, concl: &[ast::Attr],
    oty: Option<&ast::Type>,
  ) {
    let term = elab.elab_term(term);
    let mut term2 = match term {
      Term::Functor { nr, ref args } => {
        let (nr, args) = Term::adjust(nr, args, &elab.g.constrs);
        Term::Functor { nr, args: args.to_vec().into() }
      }
      Term::Aggregate { .. } | Term::Selector { .. } => term.clone(),
      _ => panic!("invalid functor registration target"),
    };
    let mut ty = match oty {
      None => term2.get_type(&elab.g, &elab.lc, false),
      Some(ty) => elab.elab_type(ty),
    };
    let concl = concl.iter().map(|attr| elab.elab_attr(attr, true, &mut ty)).collect_vec();
    let mut cc = CorrConds::new();
    cc.0[CorrCondKind::Coherence] = Some(Box::new(if oty.is_some() {
      let f = Formula::mk_and_with(|conj| {
        conj.push(elab.g.reqs.mk_eq(Term::Bound(BoundId(0)), term));
        let f = Formula::mk_and_with(|conj| {
          for attr in &concl {
            let args = attr.args.iter().cloned().chain([Term::Bound(BoundId(0))]).collect();
            conj.push(Formula::Attr { nr: attr.nr, args }.maybe_neg(attr.pos))
          }
        });
        f.mk_neg().append_conjuncts_to(conj)
      });
      Formula::forall(ty.clone(), f.mk_neg())
    } else {
      Formula::mk_and_with(|conj| {
        for attr in &concl {
          let args = attr.args.iter().chain([&term]).cloned().collect();
          conj.push(Formula::Attr { nr: attr.nr, args }.maybe_neg(attr.pos))
        }
      })
    }));
    elab.elab_corr_conds(cc, &it.conds, &it.corr);

    let mut attrs = ty.attrs.0.clone();
    for attr in concl {
      attrs.insert(&elab.g.constrs, attr);
    }

    let primary: Box<[_]> = self.primary.0.iter().cloned().collect();
    let mut attrs1 = attrs.clone();
    attrs.enlarge_by(&elab.g.constrs, &ty.attrs.1, |a| a.clone());
    attrs.round_up_with(&elab.g, &elab.lc, &ty, false);
    let Attrs::Consistent(_) = attrs else { panic!("inconsistent functor registration") };
    self.to_locus(elab, |l| {
      term2.visit(l);
      attrs1.visit(l);
      attrs.visit(l);
      ty.visit(l);
    });
    CheckAccess::with(&primary, |occ| occ.visit_term(&term2));
    attrs1.visit(&mut elab.intern_const());
    elab.read_functor_cluster(FunctorCluster {
      cl: Cluster { primary, consequent: (attrs1, attrs) },
      ty: oty.map(|_| Box::new(ty)),
      term: Box::new(term2),
    });
    self.needs_round_up = true;
  }

  fn elab_identify_pattern_func(
    &self, elab: &Analyzer, pat: &ast::PatternFunc,
  ) -> PatternFuncResult {
    let fmt = elab.formats[&Format::Func(pat.to_format())];
    let visible: Box<[_]> = pat.args().iter().map(|v| self.locus(v.var())).collect();
    let args: Box<[_]> = pat.args().iter().map(|v| Term::Constant(v.var())).collect();
    let pat = elab.notations.functor.iter().rev().find(|pat| {
      pat.fmt == fmt
        && matches!(pat.check_types(&elab.g, &elab.lc, &args),
          Some(subst) if { self.check_compatible_args(&subst); true })
    });
    let pat = pat.expect("type error");
    let PatternKind::Func(nr) = pat.kind else { unreachable!() };
    let mut var_set = CheckAccess::new(self.primary.len());
    for &i in &*visible {
      var_set.set(i);
      var_set.visit_type(&self.primary[i]);
    }
    PatternFuncResult { nr, args, var_set }
  }

  fn elab_identify_func(&mut self, elab: &mut Analyzer, it: &ast::IdentifyFunc) {
    let orig = self.elab_identify_pattern_func(elab, &it.orig);
    let new = self.elab_identify_pattern_func(elab, &it.new);
    assert!(
      (orig.var_set.0 | new.var_set.0) == (1 << self.primary.len() as u64) - 1,
      "Unused locus"
    );
    let mut eq_args = vec![];
    let mut occ = CheckAccess::new(self.primary.len() as _);
    for (v1, v2) in &it.eqs {
      let (c1, c2) = (v1.var(), v2.var());
      let (v1, v2) = (self.locus(c1), self.locus(c2));
      let (c1, c2, v1) = match (
        orig.var_set.get(v1) as i8 - new.var_set.get(v1) as i8,
        orig.var_set.get(v2) as i8 - new.var_set.get(v2) as i8,
      ) {
        (1, -1) => (c1, c2, v1),
        (-1, 1) => (c2, c1, v2),
        (1, 1) | (-1, -1) => panic!("Cannot mix left and right pattern arguments"),
        _ => panic!("The argument(s) must belong to the left or right pattern"),
      };
      eq_args.push((c1, c2));
      occ.set(v1);
      assert!(elab.lc.fixed_var[c2].ty.is_wider_than(&elab.g, &elab.lc, &elab.lc.fixed_var[c1].ty));
    }
    eq_args.sort_unstable();

    for (i, ty) in self.primary.enum_iter() {
      if occ.get(i) {
        occ.visit_type(ty)
      }
    }
    assert!(occ == orig.var_set, "Left and right pattern must have the same number of arguments");
    let mut cc = CorrConds::new();
    let lhs =
      Term::Functor { nr: orig.nr, args: self.to_locus(elab, |l| orig.args.visit_cloned(l)) };
    let rhs = Term::Functor { nr: new.nr, args: self.to_locus(elab, |l| new.args.visit_cloned(l)) };
    let f = Formula::mk_and_with(|conjs| {
      conjs.extend(
        eq_args.iter().map(|&(c1, c2)| elab.g.reqs.mk_eq(Term::Constant(c1), Term::Constant(c2))),
      );
      let f = elab.g.reqs.mk_eq(
        Term::Functor { nr: orig.nr, args: orig.args },
        Term::Functor { nr: new.nr, args: new.args },
      );
      conjs.push(f.mk_neg());
    });
    cc.0[CorrCondKind::Compatibility] = Some(Box::new(f.mk_neg()));
    elab.elab_corr_conds(cc, &it.conds, &it.corr);
    elab.r.push_identify(&IdentifyFunc {
      primary: self.primary.0.iter().cloned().collect(),
      lhs,
      rhs,
      eq_args: eq_args.into_iter().map(|(c1, c2)| (self.locus(c1), self.locus(c2))).collect(),
    });
  }

  fn elab_reduction(&mut self, elab: &mut Analyzer, it: &ast::Reduction) {
    fn is_ssubterm(g: &Global, lc: &LocalContext, sup: &Term, sub: &Term) -> bool {
      use Term::*;
      match sup {
        Numeral(_) | Locus(_) | Bound(_) | Constant(_) | Infer(_) => ().eq_term(g, lc, sup, sub),
        PrivFunc { value, .. } => is_ssubterm(g, lc, value, sub),
        Functor { args, .. }
        | SchFunc { args, .. }
        | Aggregate { args, .. }
        | Selector { args, .. } => subterm_list(g, lc, args, sub),
        The { .. } | Fraenkel { .. } => false,
        EqClass(_) | EqMark(_) | Qua { .. } | FreeVar(_) | It => unreachable!(),
      }
    }
    fn subterm_list(g: &Global, lc: &LocalContext, args: &[Term], sub: &Term) -> bool {
      args.iter().any(|t| ().eq_term(g, lc, t, sub) || is_ssubterm(g, lc, t, sub))
    }

    let mut from = elab.elab_term(&it.from);
    let mut to = elab.elab_term(&it.to);
    let reduction_allowed = {
      let Term::Functor { nr, ref args } = from else {
        panic!("reduction must have a functor term on the LHS")
      };
      let args = Term::adjust(nr, args, &elab.g.constrs).1;
      subterm_list(&elab.g, &elab.lc, args, to.skip_priv_func(Some(&elab.lc)))
    };
    assert!(reduction_allowed, "Right term must be a subterm of the left term");
    let mut cc = CorrConds::new();
    cc.0[CorrCondKind::Reducibility] = Some(Box::new(elab.g.reqs.mk_eq(from.clone(), to.clone())));
    elab.elab_corr_conds(cc, &it.conds, &it.corr);
    self.to_locus(elab, |l| {
      from.visit(l);
      to.visit(l)
    });
    let primary: Box<[_]> = self.primary.0.iter().cloned().collect();
    CheckAccess::with(&primary, |occ| occ.visit_term(&from));
    elab.r.reductions.push(Reduction { primary, terms: [from, to] });
  }

  fn elab_sethood_registration(
    &mut self, elab: &mut Analyzer, ty: &ast::Type, just: &ast::Justification,
  ) {
    let mut ty = elab.elab_type(ty);
    let primary: Box<[_]> = self.primary.0.iter().cloned().collect();
    let mut property = Formula::mk_neg(Formula::forall(
      Type::SET,
      Formula::mk_neg(Formula::forall(
        ty.clone(),
        Formula::Pred {
          nr: elab.g.reqs.belongs_to().unwrap(),
          args: Box::new([Term::Bound(BoundId(1)), Term::Bound(BoundId(0))]),
        },
      )),
    ));
    self.to_locus(elab, |l| ty.visit(l));
    CheckAccess::with(&primary, |occ| occ.visit_type(&ty));
    property.visit(&mut elab.intern_const());
    elab.elab_justification(None, &property, just);
    elab.properties.push(Property { primary, ty, kind: PropertyKind::Sethood })
  }

  fn elab_pred_notation(
    &mut self, elab: &mut Analyzer, new: &ast::PatternPred, orig: &ast::PatternPred, pos: bool,
  ) {
    let fmt_orig = elab.formats[&Format::Pred(orig.to_format())];
    let primary: Box<[_]> = self.primary.0.iter().cloned().collect();
    CheckAccess::with(&primary, |occ| orig.args.iter().for_each(|v| occ.set(self.locus(v.var()))));
    let args: Box<[_]> = orig.args.iter().map(|v| Term::Constant(v.var())).collect();
    let pat = elab.notations.predicate.iter().rev().find(|pat| {
      pat.fmt == fmt_orig
        && !matches!(pat.kind, PatternKind::Pred(nr)
            if elab.g.constrs.predicate[nr].redefines.is_some())
        && matches!(pat.check_types(&elab.g, &elab.lc, &args),
            Some(subst) if { self.check_compatible_args(&subst); true })
    });
    let pat = pat.expect("type error");
    let PatternKind::Pred(nr) = pat.kind else { unreachable!() };
    let c = &elab.g.constrs.predicate[nr];
    let pat = Pattern {
      kind: PatternKind::Pred(c.redefines.unwrap_or(nr)),
      fmt: elab.formats[&Format::Pred(new.to_format())],
      primary,
      visible: new.args.iter().map(|v| self.locus(v.var())).collect(),
      pos: pos == pat.pos,
    };
    pat.check_access();
    elab.r.lc.formatter.push(&elab.r.g.constrs, &pat);
    elab.r.notations.predicate.push(pat)
  }

  fn elab_func_notation(
    &mut self, elab: &mut Analyzer, new: &ast::PatternFunc, orig: &ast::PatternFunc,
  ) {
    let fmt_orig = elab.formats[&Format::Func(orig.to_format())];
    let primary: Box<[_]> = self.primary.0.iter().cloned().collect();
    CheckAccess::with(&primary, |occ| {
      orig.args().iter().for_each(|v| occ.set(self.locus(v.var())))
    });
    let args: Box<[_]> = orig.args().iter().map(|v| Term::Constant(v.var())).collect();
    let pat = elab.notations.functor.iter().rev().find(|pat| {
      pat.fmt == fmt_orig
        && !matches!(pat.kind, PatternKind::Func(nr)
            if elab.g.constrs.functor[nr].redefines.is_some())
        && matches!(pat.check_types(&elab.g, &elab.lc, &args),
            Some(subst) if { self.check_compatible_args(&subst); true })
    });
    let pat = pat.expect("type error");
    let PatternKind::Func(nr) = pat.kind else { unreachable!() };
    let c = &elab.g.constrs.functor[nr];
    let pat = Pattern {
      kind: PatternKind::Func(c.redefines.unwrap_or(nr)),
      fmt: elab.formats[&Format::Func(new.to_format())],
      primary,
      visible: new.args().iter().map(|v| self.locus(v.var())).collect(),
      pos: true,
    };
    pat.check_access();
    elab.r.lc.formatter.push(&elab.r.g.constrs, &pat);
    elab.r.notations.functor.push(pat)
  }

  fn elab_mode_notation(
    &mut self, elab: &mut Analyzer, new: &ast::PatternMode, orig: &ast::PatternMode,
  ) {
    let fmt_orig = elab.formats[&Format::Mode(orig.to_format())];
    let primary: Box<[_]> = self.primary.0.iter().cloned().collect();
    CheckAccess::with(&primary, |occ| orig.args.iter().for_each(|v| occ.set(self.locus(v.var()))));
    let args: Box<[_]> = orig.args.iter().map(|v| Term::Constant(v.var())).collect();
    let pat = elab.notations.mode.iter().rev().find(|pat| {
      pat.fmt == fmt_orig
        && !matches!(pat.kind, PatternKind::Mode(nr)
            if elab.g.constrs.mode[nr].redefines.is_some())
        && matches!(pat.check_types(&elab.g, &elab.lc, &args),
            Some(subst) if { self.check_compatible_args(&subst); true })
    });
    let pat = pat.expect("type error");
    let PatternKind::Mode(nr) = pat.kind else { panic!("redefining expandable mode") };
    let c = &elab.g.constrs.mode[nr];
    let pat = Pattern {
      kind: PatternKind::Mode(c.redefines.unwrap_or(nr)),
      fmt: elab.formats[&Format::Mode(new.to_format())],
      primary,
      visible: new.args.iter().map(|v| self.locus(v.var())).collect(),
      pos: true,
    };
    pat.check_access();
    elab.r.lc.formatter.push(&elab.r.g.constrs, &pat);
    elab.r.notations.mode.push(pat)
  }

  fn elab_attr_notation(
    &mut self, elab: &mut Analyzer, new: &ast::PatternAttr, orig: &ast::PatternAttr, pos: bool,
  ) {
    let fmt_orig = elab.formats[&Format::Attr(orig.to_format())];
    let primary: Box<[_]> = self.primary.0.iter().cloned().collect();
    CheckAccess::with(&primary, |occ| orig.args.iter().for_each(|v| occ.set(self.locus(v.var()))));
    let args: Box<[_]> = orig.args.iter().map(|v| Term::Constant(v.var())).collect();
    let pat = elab.notations.attribute.iter().rev().find(|pat| {
      pat.fmt == fmt_orig
        && !matches!(pat.kind, PatternKind::Attr(nr)
            if elab.g.constrs.attribute[nr].redefines.is_some())
        && matches!(pat.check_types(&elab.g, &elab.lc, &args),
            Some(subst) if { self.check_compatible_args(&subst); true })
    });
    let pat = pat.expect("type error");
    let PatternKind::Attr(nr) = pat.kind else { unreachable!() };
    let c = &elab.g.constrs.attribute[nr];
    let pat = Pattern {
      kind: PatternKind::Attr(c.redefines.unwrap_or(nr)),
      fmt: elab.formats[&Format::Attr(new.to_format())],
      primary,
      visible: new.args.iter().map(|v| self.locus(v.var())).collect(),
      pos: pos == pat.pos,
    };
    pat.check_access();
    elab.r.lc.formatter.push(&elab.r.g.constrs, &pat);
    elab.r.notations.attribute.push(pat)
  }
}

impl ReadProof for BlockReader {
  type CaseIterable = std::convert::Infallible;
  type CaseIter<'a> = std::convert::Infallible;
  type SupposeRecv = std::convert::Infallible;
  type Output = ();

  fn intro(&mut self, elab: &mut Analyzer, start: usize, _: u32) {
    self.to_locus.0.resize(start, None);
    for fv in &elab.r.lc.fixed_var.0[start..] {
      let ty = self.to_locus(elab, |l| fv.ty.visit_cloned(l));
      Exportable.visit_type(&ty);
      let i = self.primary.push(ty);
      self.to_const.0.push(self.to_locus.push(Some(i)));
    }
  }

  fn assume(&mut self, elab: &mut Analyzer, mut conjs: Vec<Formula>) {
    self.to_locus(elab, |l| conjs.visit(l));
    conjs.iter().for_each(|f| Exportable.visit_formula(f));
    self.assums.append(&mut conjs);
  }

  fn given(&mut self, elab: &mut Analyzer, start: usize, istart: u32, f: Formula) {
    let mut f = f.mk_neg();
    let end = elab.lc.fixed_var.len();
    elab.lc.mk_forall(start..end, istart, false, &mut f);
    self.assume(elab, vec![f.mk_neg()]);
  }

  fn take(&mut self, _: &mut Analyzer, _: Term) { panic!("invalid item") }
  fn thus(&mut self, _: &mut Analyzer, _: Vec<Formula>) { panic!("invalid item") }
  fn new_cases(&mut self, _: &mut Analyzer) -> Self::CaseIterable { panic!("invalid item") }

  fn new_cases_iter(
    &mut self, _: &mut Analyzer, case: &mut Self::CaseIterable,
  ) -> Self::CaseIter<'_> {
    *case
  }

  fn new_supposes(&mut self, _: &mut Analyzer) -> Self::SupposeRecv { panic!("invalid item") }

  fn end_block(&mut self, elab: &mut Analyzer, _: Position) {
    if self.needs_round_up {
      let mut attrs = elab.g.numeral_type.attrs.1.clone();
      attrs.round_up_with(&elab.g, &elab.lc, &elab.g.numeral_type, false);
      elab.g.numeral_type.attrs.1 = attrs;
      if let Some(mut nat) = elab.g.nat.take() {
        nat.round_up_with_self(&elab.g, &elab.lc, false);
        elab.g.nat = Some(nat)
      }
      for i in 0..elab.g.clusters.registered.len() {
        let cl = &elab.r.g.clusters.registered[i];
        let mut attrs = cl.consequent.1.clone();
        elab.r.lc.with_locus_tys(&cl.primary, |lc| {
          attrs.round_up_with(&elab.r.g, lc, &cl.ty, false);
        });
        elab.r.g.clusters.registered[i].consequent.1 = attrs;
      }
    }
  }

  fn elab_item(&mut self, elab: &mut Analyzer, it: &ast::Item) -> bool {
    match &it.kind {
      ast::ItemKind::Definition { .. } => elab.item_header(it, "Definition"),
      ast::ItemKind::DefStruct { .. } => elab.item_header(it, "DefStruct"),
      ast::ItemKind::PatternRedef { .. } => elab.item_header(it, "PatternRedef"),
      ast::ItemKind::Cluster { .. } => elab.item_header(it, "Cluster"),
      ast::ItemKind::Reduction { .. } => elab.item_header(it, "Reduction"),
      ast::ItemKind::IdentifyFunc { .. } => elab.item_header(it, "IdentifyFunc"),
      ast::ItemKind::SethoodRegistration { .. } => elab.item_header(it, "SethoodRegistration"),
      _ => {}
    }
    match (self.kind, &it.kind) {
      (BlockKind::Definition, ast::ItemKind::Definition(it)) => match &it.kind {
        ast::DefinitionKind::Func { pat, spec, def } =>
          self.elab_func_def(elab, pat, it, spec.as_deref(), def.as_deref()),
        ast::DefinitionKind::Pred { pat, def } => self.elab_pred_def(elab, pat, it, def.as_deref()),
        ast::DefinitionKind::Mode { pat, kind } => self.elab_mode_def(elab, pat, kind, it),
        ast::DefinitionKind::Attr { pat, def } => self.elab_attr_def(elab, pat, it, def.as_deref()),
      },
      (BlockKind::Definition, ast::ItemKind::DefStruct(it)) => self.elab_struct_def(elab, it),
      (BlockKind::Notation, ast::ItemKind::PatternRedef(it)) => match it {
        ast::PatternRedef::Pred { new, orig, pos } =>
          self.elab_pred_notation(elab, new, orig, *pos),
        ast::PatternRedef::Func { new, orig } => self.elab_func_notation(elab, new, orig),
        ast::PatternRedef::Mode { new, orig } => self.elab_mode_notation(elab, new, orig),
        ast::PatternRedef::Attr { new, orig, pos } =>
          self.elab_attr_notation(elab, new, orig, *pos),
      },
      (BlockKind::Registration, ast::ItemKind::Cluster(it)) => match &it.kind {
        ast::ClusterDeclKind::Exist { concl, ty } => self.elab_exist_reg(elab, it, concl, ty),
        ast::ClusterDeclKind::Func { term, concl, ty } =>
          self.elab_func_reg(elab, it, term, concl, ty.as_deref()),
        ast::ClusterDeclKind::Cond { antecedent, concl, ty } =>
          self.elab_cond_reg(elab, it, antecedent, concl, ty),
      },
      (BlockKind::Registration, ast::ItemKind::IdentifyFunc(it)) =>
        self.elab_identify_func(elab, it),
      (BlockKind::Registration, ast::ItemKind::Reduction(it)) => self.elab_reduction(elab, it),
      (BlockKind::Registration, ast::ItemKind::SethoodRegistration { ty, just }) =>
        self.elab_sethood_registration(elab, ty, just),
      (BlockKind::Definition, &ast::ItemKind::Pragma(Pragma::Canceled(CancelKind::Def, n))) =>
        elab.elab_canceled(CancelKind::Def, n),
      _ => return self.super_elab_item(elab, it),
    }
    true
  }
}
