#![allow(unused)]
use crate::ast::{FormulaBinder, FormulaBinop, VarKind};
use crate::checker::Checker;
use crate::reader::Reader;
use crate::types::*;
use crate::*;

struct Analyzer<'a> {
  r: &'a mut Reader,
  sch_func_args: IdxVec<SchFuncId, Box<[Type]>>,
  priv_pred: IdxVec<PrivPredId, (Box<[Type]>, Box<Formula>)>,
  sch_pred_args: IdxVec<SchPredId, Box<[Type]>>,
  thesis: Option<Box<Formula>>,
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
    let mut analyzer = Analyzer {
      r: self,
      sch_func_args: Default::default(),
      priv_pred: Default::default(),
      sch_pred_args: Default::default(),
      thesis: None,
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

impl Analyzer<'_> {
  fn elab_top_item(&mut self, it: &ast::Item) {
    match &it.kind {
      ast::ItemKind::Section | ast::ItemKind::Pragma { .. } => {}
      ast::ItemKind::Block { kind, items, .. } => match kind {
        BlockKind::Definition => {}
        BlockKind::Registration => {} //stat("Registration"),
        BlockKind::Notation => {}     //stat("Notation"),
      },
      ast::ItemKind::SchemeBlock(_) => {} //stat("SchemeBlock"),
      ast::ItemKind::Theorem { prop, just } => {} //stat("Theorem"),
      ast::ItemKind::Reservation(_) => {} //stat("Reservation"),
      ast::ItemKind::Thus(_) => {}        //stat("Thus"),
      ast::ItemKind::Statement(_) => {}   //stat("Statement"),
      ast::ItemKind::Consider { vars, conds, just } => {} //stat("Consider"),
      ast::ItemKind::Reconsider { vars, ty, just } => {} //stat("Reconsider"),
      ast::ItemKind::DefFunc { var, tys, value } => {} //stat("DefFunc"),
      ast::ItemKind::DefPred { var, tys, value } => {} //stat("DefPred"),
      ast::ItemKind::Set { var, value } => {} //stat("Set"),
      ast::ItemKind::Let { var } => {}    //stat("Let"),
      ast::ItemKind::LetLocus { var } => {} //stat("LetLocus"),
      ast::ItemKind::Given { vars, conds } => {} //stat("Given"),
      ast::ItemKind::Take { var, term } => {} //stat("Take"),
      ast::ItemKind::PerCases { just } => {} //stat("PerCases"),
      ast::ItemKind::CaseOrSuppose { end, kind, hyp, items } => {} //stat("CaseOrSuppose"),
      ast::ItemKind::Assumption(_) => {}  //stat("Assumption"),
      ast::ItemKind::Property { prop, just } => {} //stat("Property"),
      ast::ItemKind::Definition(_) => {}  //stat("Definition"),
      ast::ItemKind::DefStruct(_) => {}   //stat("DefStruct"),
      ast::ItemKind::PatternRedef { kind, orig, new } => {} //stat("PatternRedef"),
      ast::ItemKind::Cluster(_) => {}     //stat("Cluster"),
      ast::ItemKind::Identify(_) => {}    //stat("Identify"),
      ast::ItemKind::Reduction(_) => {}   //stat("Reduction"),
      ast::ItemKind::SethoodRegistration { ty, just } => {} //stat("SethoodRegistration"),
      ast::ItemKind::SchemeHead(_) | ast::ItemKind::CaseHead(_) | ast::ItemKind::SupposeHead(_) =>
        panic!("invalid top level item"),
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
}

struct Exportable {
  ok: bool,
}
impl Exportable {
  fn get(f: impl FnOnce(&mut Self)) -> bool {
    let mut e = Exportable { ok: true };
    f(&mut e);
    e.ok
  }
}
impl Visit for Exportable {
  fn abort(&self) -> bool { !self.ok }

  fn visit_term(&mut self, tm: &Term) {
    match tm {
      Term::Constant(_) => todo!("skel const something"),
      Term::PrivFunc { .. } => self.ok = false,
      _ => self.super_visit_term(tm),
    }
  }

  fn visit_formula(&mut self, f: &Formula) {
    match f {
      Formula::PrivPred { .. } => self.ok = false,
      _ => self.super_visit_formula(f),
    }
  }
}
