#![allow(unused)]
use crate::ast::{CaseKind, FormulaBinder, FormulaBinop, VarKind};
use crate::checker::Checker;
use crate::reader::Reader;
use crate::types::*;
use crate::*;

struct Analyzer<'a> {
  r: &'a mut Reader,
  sch_func_args: IdxVec<SchFuncId, Box<[Type]>>,
  priv_func_args: IdxVec<PrivPredId, Box<[Type]>>,
  priv_pred: IdxVec<PrivPredId, (Box<[Type]>, Box<Formula>)>,
  sch_pred_args: IdxVec<SchPredId, Box<[Type]>>,
  thesis: Option<Box<Formula>>,
  reserved: Vec<Type>,
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
      ast::ItemKind::Block { kind, items, .. } => match kind {
        BlockKind::Definition => {}
        BlockKind::Registration => panic!("Registration"),
        BlockKind::Notation => panic!("Notation"),
      },
      ast::ItemKind::SchemeBlock(it) => self.scope(None, false, false, |this| this.elab_scheme(it)),
      ast::ItemKind::Theorem { prop, just } => panic!("Theorem"),
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
      ast::ItemKind::Thus(_) => panic!("Thus"),
      ast::ItemKind::Statement(_) => panic!("Statement"),
      ast::ItemKind::Consider { vars, conds, just } => panic!("Consider"),
      ast::ItemKind::Reconsider { vars, ty, just } => panic!("Reconsider"),
      ast::ItemKind::DefFunc { var, tys, value } => panic!("DefFunc"),
      ast::ItemKind::DefPred { var, tys, value } => panic!("DefPred"),
      ast::ItemKind::Set { var, value } => panic!("Set"),
      ast::ItemKind::Let { var } => panic!("Let"),
      ast::ItemKind::LetLocus { var } => panic!("LetLocus"),
      ast::ItemKind::Given { vars, conds } => panic!("Given"),
      ast::ItemKind::Take { var, term } => panic!("Take"),
      ast::ItemKind::PerCases { just, kind, blocks } => panic!("PerCases"),
      ast::ItemKind::Assume(_) => panic!("Assumption"),
      ast::ItemKind::Property { prop, just } => panic!("Property"),
      ast::ItemKind::Definition(_) => panic!("Definition"),
      ast::ItemKind::DefStruct(_) => panic!("DefStruct"),
      ast::ItemKind::PatternRedef { kind, orig, new } => panic!("PatternRedef"),
      ast::ItemKind::Cluster(_) => panic!("Cluster"),
      ast::ItemKind::Identify(_) => panic!("Identify"),
      ast::ItemKind::Reduction(_) => panic!("Reduction"),
      ast::ItemKind::SethoodRegistration { ty, just } => panic!("SethoodRegistration"),
      ast::ItemKind::SchemeHead(_)
      | ast::ItemKind::CaseHead(..)
      | ast::ItemKind::PerCasesHead(_) => panic!("invalid top level item"),
    }
  }

  fn elab_scheme(&mut self, ast::SchemeBlock { end, head, items }: &ast::SchemeBlock) {
    let ast::SchemeHead { sym, nr, groups, concl, prems } = head;
    assert!(self.lc.sch_func_ty.is_empty());
    let infer_consts = self.lc.infer_const.get_mut().0.len();
    for group in groups {
      match group {
        ast::SchemeBinderGroup::Func { vars, tys, ret, .. } => {
          self.elab_push_locus_tys(tys);
          let ret = self.elab_intern_type(ret);
          assert!(!vars.is_empty());
          for _ in 1..vars.len() {
            self.sch_func_args.push((&*self.r.lc.locus_ty.0).to_vec().into());
            self.r.lc.sch_func_ty.push(ret.clone());
          }
          self.sch_func_args.push(self.r.lc.locus_ty.0.drain(..).collect());
          self.r.lc.sch_func_ty.push(ret);
        }
        ast::SchemeBinderGroup::Pred { vars, tys, .. } => {
          self.elab_push_locus_tys(tys);
          assert!(!vars.is_empty());
          for _ in 1..vars.len() {
            self.sch_pred_args.push((&*self.r.lc.locus_ty.0).to_vec().into());
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
      ast::ItemKind::Block { end, kind, items } => todo!(),
      ast::ItemKind::SchemeBlock(_) => todo!(),
      ast::ItemKind::Theorem { prop, just } => todo!(),
      ast::ItemKind::Reservation(_) => todo!(),
      ast::ItemKind::Section => todo!(),
      ast::ItemKind::Thus(_) => todo!(),
      ast::ItemKind::Statement(_) => todo!(),
      ast::ItemKind::Consider { vars, conds, just } => todo!(),
      ast::ItemKind::Reconsider { vars, ty, just } => todo!(),
      ast::ItemKind::DefFunc { var, tys, value } => todo!(),
      ast::ItemKind::DefPred { var, tys, value } => todo!(),
      ast::ItemKind::Set { var, value } => todo!(),
      ast::ItemKind::Let { var } => todo!(),
      ast::ItemKind::LetLocus { var } => todo!(),
      ast::ItemKind::Given { vars, conds } => todo!(),
      ast::ItemKind::Take { var, term } => todo!(),
      ast::ItemKind::Assume(_) => todo!(),
      ast::ItemKind::Property { prop, just } => todo!(),
      ast::ItemKind::Definition(_) => todo!(),
      ast::ItemKind::DefStruct(_) => todo!(),
      ast::ItemKind::PatternRedef { kind, orig, new } => todo!(),
      ast::ItemKind::Cluster(_) => todo!(),
      ast::ItemKind::Identify(_) => todo!(),
      ast::ItemKind::Reduction(_) => todo!(),
      ast::ItemKind::SethoodRegistration { ty, just } => todo!(),
      ast::ItemKind::Pragma { spelling } => todo!(),
      ast::ItemKind::SchemeHead(_) => todo!(),
      ast::ItemKind::PerCases { just, kind, blocks } => todo!(),
      ast::ItemKind::CaseHead(_, _) => todo!(),
      ast::ItemKind::PerCasesHead(_) => todo!(),
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

  fn elab_justification(&mut self, thesis: &Formula, just: &ast::Justification) { todo!() }

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
      ast::Term::InternalSelector { ref sym, .. } => Term::Constant(ConstId(sym.0)), // WTF?
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
      ast::Term::It { .. } => Term::It,
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
                PatternKind::ExpandableMode => {
                  ty = pat.expansion.as_deref().unwrap().clone();
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
          self.formats[&Format::Struct(FormatStructMode { sym: sym.0, args: args.len() as u8 })];
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
        todo!()
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
    let mut conjs = vec![];
    self.elab_push_conjuncts(f1, &mut conjs, pos1);
    self.elab_push_conjuncts(f2, &mut conjs, pos2);
    Formula::mk_and(conjs)
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
        let mut conjs = vec![];
        for rhs in rest {
          let mut mid: Vec<_> = args[left as usize..].into();
          let right = mid.len() as u8;
          self
            .elab_pred(FormatPred { sym, left, right }, args, true)
            .append_conjuncts_to(&mut conjs);
          mid.extend(rhs.right.iter().map(|t| self.elab_term_qua(t)));
          (args, sym, left) = (mid, rhs.sym.0, right);
        }
        let right = args.len() as u8 - left;
        self.elab_pred(FormatPred { sym, left, right }, args, true).append_conjuncts_to(&mut conjs);
        Formula::mk_and(conjs).maybe_neg(pos)
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
        let mut conjs = vec![];
        for attr in attrs {
          self.elab_is_attr(attr, true, &term).append_conjuncts_to(&mut conjs)
        }
        Formula::mk_and(conjs).maybe_neg(pos)
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
  fn elab_push_locus_tys(&mut self, tys: &[ast::Type]) {
    assert!(self.lc.locus_ty.is_empty());
    for ty in tys {
      let ty = self.elab_type(ty);
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
}

struct Exportable;

impl Visit for Exportable {
  fn visit_term(&mut self, tm: &Term) {
    match tm {
      Term::Constant(_) => todo!("skel const something"),
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
  type SupposeRecv: Default;

  /// Changes the thesis from `for x1..xn holds P` to `P`
  /// where `x1..xn` are the fixed_vars introduced since `start`
  fn intro_from(&mut self, elab: &mut Analyzer, start: usize);

  /// Changes the thesis from `!(conj1 & ... & conjn & rest)` to `!rest`
  fn assume(&mut self, elab: &mut Analyzer, conjs: Vec<Formula>);

  /// Changes the thesis from `!(!(for x1..xn holds !(conj1 & ... & conjn)) & rest)` to `!rest`
  /// (that is, `(ex x1..xn st conj1 & ... & conjn) -> rest` to `rest`)
  /// where `x1..xn` are the fixed_vars introduced since `start`
  fn given(&mut self, elab: &mut Analyzer, start: usize, conjs: Vec<Formula>);

  /// Changes the thesis from `ex x st P(x)` to `P(term)`
  fn take(&mut self, elab: &mut Analyzer, term: Term);

  /// Changes the thesis from `ex x st P(x)` to `P(v)`,
  /// where `v` is the last `fixed_var` to be introduced
  fn take_as_var(&mut self, elab: &mut Analyzer, v: ConstId);

  /// Changes the thesis from `f & rest` to `rest`
  fn thus(&mut self, elab: &mut Analyzer, f: Formula);

  fn new_thesis_case(&mut self, elab: &mut Analyzer) -> Self::CaseIterable;

  fn new_thesis_case_iter<'a>(
    &mut self, elab: &mut Analyzer, case: &'a mut Self::CaseIterable,
  ) -> Self::CaseIter<'a>;

  fn next_thesis_case(&mut self, elab: &mut Analyzer, case: &mut Self::CaseIter<'_>, f: &[Formula]);

  fn finish_thesis_case(&mut self, elab: &mut Analyzer, case: Self::CaseIter<'_>);

  fn next_suppose(&mut self, elab: &mut Analyzer, recv: &mut Self::SupposeRecv);

  fn finish_proof(&mut self, elab: &mut Analyzer);

  fn elab_proof(&mut self, elab: &mut Analyzer, items: &[ast::Item]) {
    for item in items {
      match &item.kind {
        ast::ItemKind::Let { var } => {
          let n = elab.lc.fixed_var.len();
          elab.elab_fixed_vars(var);
          self.intro_from(elab, n)
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
          let mut conjs = vec![];
          for prop in conds {
            elab.elab_proposition(prop).append_conjuncts_to(&mut conjs);
          }
          self.given(elab, n, conjs);
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
          let mut disjs = vec![];
          for bl in blocks {
            elab.scope(None, true, false, |elab| {
              let mut conjs = vec![];
              for prop in bl.hyp.conds() {
                elab.elab_proposition(prop).append_conjuncts_to(&mut conjs);
              }
              self.next_thesis_case(elab, &mut iter, &conjs);
              Formula::mk_and(conjs).mk_neg().append_conjuncts_to(&mut disjs);
              self.elab_proof(elab, items);
            });
          }
          self.finish_thesis_case(elab, iter);
          elab.elab_justification(&Formula::mk_and(disjs).mk_neg(), just);
          break
        }
        ast::ItemKind::PerCases { just, kind: CaseKind::Suppose, blocks } => {
          let mut disjs = vec![];
          let mut recv = Default::default();
          for bl in blocks {
            elab.scope(None, true, false, |elab| {
              let mut conjs = vec![];
              for prop in bl.hyp.conds() {
                elab.elab_proposition(prop).append_conjuncts_to(&mut conjs);
              }
              Formula::mk_and(conjs).mk_neg().append_conjuncts_to(&mut disjs);
              self.elab_proof(elab, items);
              self.next_suppose(elab, &mut recv);
            });
          }
          elab.elab_justification(&Formula::mk_and(disjs).mk_neg(), just);
          break
        }
        _ => elab.elab_stmt_item(item),
      }
    }
    self.finish_proof(elab)
  }
}

struct WithThesis;

impl ReadProof for WithThesis {
  type CaseIterable = Formula;
  type CaseIter<'a> = std::slice::Iter<'a, Formula>;
  type SupposeRecv = ();

  fn intro_from(&mut self, elab: &mut Analyzer, start: usize) { todo!() }

  fn assume(&mut self, elab: &mut Analyzer, conjs: Vec<Formula>) { todo!() }

  fn given(&mut self, elab: &mut Analyzer, start: usize, conjs: Vec<Formula>) { todo!() }

  fn take(&mut self, elab: &mut Analyzer, term: Term) { todo!() }

  fn take_as_var(&mut self, elab: &mut Analyzer, v: ConstId) { todo!() }

  fn thus(&mut self, elab: &mut Analyzer, f: Formula) { todo!() }

  fn new_thesis_case(&mut self, elab: &mut Analyzer) -> Self::CaseIterable {
    elab.thesis.as_ref().unwrap().clone().mk_neg()
  }

  fn new_thesis_case_iter<'a>(
    &mut self, elab: &mut Analyzer, case: &'a mut Self::CaseIterable,
  ) -> Self::CaseIter<'a> {
    case.conjuncts().iter()
  }

  fn next_thesis_case(
    &mut self, elab: &mut Analyzer, case: &mut Self::CaseIter<'_>, f: &[Formula],
  ) {
    todo!()
  }

  fn finish_thesis_case(&mut self, elab: &mut Analyzer, mut case: Self::CaseIter<'_>) {
    assert!(case.next().is_none())
  }

  fn next_suppose(&mut self, _: &mut Analyzer, _: &mut ()) {}

  fn finish_proof(&mut self, elab: &mut Analyzer) { todo!() }
}

enum ProofStep {
  Let { start: usize },
  Assume { conjs: Vec<Formula> },
  Given { start: usize, not_f: Formula },
  TakeAsVar { start: usize },
  Thus { conjs: Vec<Formula> },
  Case,
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
    let mut rec = Reconstruction { pos, conjs: vec![] };
    while let Some(step) = self.stack.pop() {
      match step {
        ProofStep::Let { start } => {
          let mut f = Formula::mk_and(std::mem::take(rec.as_pos(true)));
          elab.lc.mk_forall(start, &mut f);
          rec.conjs = vec![f];
        }
        ProofStep::Assume { mut conjs } => {
          let rest = rec.as_pos(false);
          std::mem::swap(&mut conjs, rest);
          rest.append(&mut conjs)
        }
        ProofStep::Given { start, mut not_f } => {
          let rest = rec.as_pos(false);
          elab.lc.mk_forall(start, &mut not_f);
          rest.insert(0, not_f.mk_neg())
        }
        ProofStep::TakeAsVar { start } => {
          let mut f = Formula::mk_and(std::mem::take(rec.as_pos(false)));
          elab.lc.mk_forall(start, &mut f);
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

  fn intro_from(&mut self, elab: &mut Analyzer, start: usize) {
    if !matches!(self.stack.last(), Some(ProofStep::Let { .. })) {
      self.stack.push(ProofStep::Let { start })
    }
  }

  fn assume(&mut self, elab: &mut Analyzer, mut conjs: Vec<Formula>) {
    if let Some(ProofStep::Assume { conjs: rest }) = self.stack.last_mut() {
      rest.append(&mut conjs)
    } else {
      self.stack.push(ProofStep::Assume { conjs })
    }
  }

  fn given(&mut self, elab: &mut Analyzer, start: usize, conjs: Vec<Formula>) {
    self.stack.push(ProofStep::Given { start, not_f: Formula::mk_and(conjs).mk_neg() })
  }

  fn take(&mut self, _: &mut Analyzer, _: Term) { panic!("take steps are not reconstructible") }

  fn take_as_var(&mut self, elab: &mut Analyzer, v: ConstId) {
    if !matches!(self.stack.last(), Some(ProofStep::TakeAsVar { .. })) {
      self.stack.push(ProofStep::TakeAsVar { start: v.0 as usize })
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
  fn new_thesis_case_iter<'a>(&mut self, _: &mut Analyzer, _: &'a mut ()) {}
  fn next_thesis_case(&mut self, _: &mut Analyzer, _: &mut (), conjs: &[Formula]) {
    self.stack.push(ProofStep::Case);
    self.stack.push(ProofStep::Thus { conjs: conjs.to_vec() });
  }
  fn finish_thesis_case(&mut self, elab: &mut Analyzer, _: ()) {
    let f = self.reconstruct(elab, false);
    self.assume(elab, vec![f]);
  }

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
