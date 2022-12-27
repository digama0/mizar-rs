use crate::checker::Checker;
use crate::types::*;
use crate::*;
use std::collections::HashSet;

enum PendingDef {
  Constr(ConstrKind),
  // Cluster,
}

pub struct Reader {
  pub g: Global,
  pub lc: LocalContext,
  pub libs: Libraries,
  article: Article,
  treat_thm_as_axiom: bool,
  /// EqDefinientia
  pub equalities: Vec<Definiens>,
  /// ExDefinientia
  pub expansions: Vec<Definiens>,
  /// gPropertiesList
  pub properties: Vec<Property>,
  /// gIdentifications
  pub identify: Vec<Identify>,
  /// gReductions
  pub reductions: Vec<Reduction>,
  pub equals: BTreeMap<ConstrKind, Vec<EqualsDef>>,
  pub func_ids: BTreeMap<ConstrKind, Vec<usize>>,
  props: Vec<Formula>,
  labels: IdxVec<LabelId, Option<usize>>,
  pending_defs: Vec<PendingDef>,
  items: usize,
  inference_nr: usize,
}

impl Reader {
  pub fn new(reqs: RequirementIndexes, numeral_type: Type, article: Article) -> Self {
    Reader {
      g: Global {
        reqs,
        constrs: Default::default(),
        clusters: Default::default(),
        numeral_type,
        recursive_round_up: false,
        rounded_up_clusters: false,
      },
      lc: LocalContext::default(),
      libs: Libraries::default(),
      article,
      treat_thm_as_axiom: matches!(article.as_str(), "tarski_0" | "tarski_a"),
      equalities: Default::default(),
      expansions: Default::default(),
      properties: Default::default(),
      identify: Default::default(),
      reductions: Default::default(),
      equals: Default::default(),
      func_ids: Default::default(),
      props: Default::default(),
      labels: Default::default(),
      pending_defs: Default::default(),
      items: 0,
      inference_nr: 0,
    }
  }

  fn intern<'a, T: Clone + Visitable<InternConst<'a>>>(&'a self, t: &T) -> T {
    let mut t = t.clone();
    t.visit(&mut self.intern_const());
    t
  }

  pub fn intern_const(&self) -> InternConst<'_> {
    InternConst::new(&self.g, &self.lc, &self.equals, &self.identify, &self.func_ids)
  }

  fn push_prop(&mut self, label: Option<LabelId>, prop: Formula) {
    // eprintln!("push_prop {:?}", label);
    if let Some(label) = label {
      assert_eq!(label, self.labels.push(Some(self.props.len())));
    }
    self.props.push(prop);
  }

  fn read_proposition(&mut self, prop: &Proposition) {
    self.push_prop(prop.label, self.intern(&prop.f))
  }

  fn push_fixed_var(&mut self, ty: &Type) {
    self.lc.fixed_var.push(FixedVar { ty: self.intern(ty), def: None });
  }

  fn read_fixed_vars(&mut self, vars: &[Type]) {
    vars.iter().for_each(|ty| self.push_fixed_var(ty))
  }

  fn scope<R>(
    &mut self, label: Option<LabelId>, check_for_local_const: bool, f: impl FnOnce(&mut Self) -> R,
  ) -> R {
    let labels = self.labels.len();
    // eprintln!("new block {:?}, labels = {labels}", label);
    if label.is_some() {
      self.labels.push(None);
    }
    let fixed_var = self.lc.fixed_var.len();
    let props = self.props.len();
    let pending_defs = self.pending_defs.len();
    let priv_funcs = self.lc.priv_func.len();
    let infer_const = self.lc.infer_const.get_mut().len();
    let sc = self.lc.term_cache.get_mut().scope;
    // vprintln!("open scope {:?}", (labels, fixed_var, props, priv_funcs, infer_const, sc));
    self.lc.term_cache.get_mut().open_scope();

    let r = f(self);

    self.lc.term_cache.get_mut().close_scope();
    let labels2 = self.labels.len();
    let fixed_var2 = self.lc.fixed_var.len();
    let props2 = self.props.len();
    let priv_funcs2 = self.lc.priv_func.len();
    let infer_const2 = self.lc.infer_const.get_mut().len();
    // vprintln!(
    //   "close scope {:?} <- {:?}",
    //   (labels, fixed_var, props, priv_funcs, infer_const, sc),
    //   (labels2, fixed_var2, props2, priv_funcs2, infer_const2, sc + 1)
    // );
    self.lc.fixed_var.0.truncate(fixed_var);
    self.props.truncate(props);
    self.labels.0.truncate(labels);
    self.lc.priv_func.0.truncate(priv_funcs);
    let mut renumber =
      self.lc.truncate_infer_const(&self.g.constrs, check_for_local_const, infer_const);
    // let infer_const3 = self.lc.infer_const.get_mut().len();
    // if infer_const3 > infer_const {
    //   vprintln!("reinserted {:?} -> {:?}", infer_const, infer_const3);
    // }
    if renumber.is_empty() {
      self.pending_defs.truncate(pending_defs)
    } else {
      for x in self.pending_defs.drain(pending_defs..) {
        match x {
          PendingDef::Constr(k) => self.g.constrs.visit_at(&mut renumber, k),
          // PendingDef::Cluster => {}
        }
      }
    }

    // self.dbg_scope_check();
    r
  }

  pub fn read_item(&mut self, it: &Item) {
    if let Some(n) = crate::FIRST_VERBOSE_ITEM {
      set_verbose(self.items >= n);
    }
    if crate::ITEM_HEADER {
      eprint!("item[{}]: ", self.items);
      if verbose() {
        eprintln!("{it:#?}");
      } else {
        match it {
          Item::Let(_) => eprintln!("Let"),
          Item::Given(_) => eprintln!("Given"),
          Item::Thus(_) => eprintln!("Conclusion"),
          Item::Assume(_) => eprintln!("Assume"),
          Item::Take(_) => eprintln!("Take"),
          Item::TakeAsVar(_, _) => eprintln!("TakeAsVar"),
          Item::PerCases(_) => eprintln!("PerCases"),
          Item::AuxiliaryItem(it) => match it {
            AuxiliaryItem::PrivateStatement(it) => match it {
              PrivateStatement::Proposition { .. } => eprintln!("Proposition"),
              PrivateStatement::IterEquality { .. } => eprintln!("IterEquality"),
              PrivateStatement::Now { .. } => eprintln!("Now"),
            },
            AuxiliaryItem::Consider { .. } => eprintln!("Consider"),
            AuxiliaryItem::Set { .. } => eprintln!("Set"),
            AuxiliaryItem::Reconsider { .. } => eprintln!("Reconsider"),
            AuxiliaryItem::DefFunc { .. } => eprintln!("DefFunc"),
            AuxiliaryItem::DefPred { .. } => eprintln!("DefPred"),
          },
          Item::Registration(_) => eprintln!("Registration"),
          Item::Scheme(_) => eprintln!("Scheme"),
          Item::Theorem { .. } => eprintln!("Theorem"),
          Item::DefTheorem { kind, .. } => eprintln!("DefTheorem {kind:?}"),
          Item::Reservation { .. } => eprintln!("Reservation"),
          Item::Section => eprintln!("Section"),
          Item::Canceled(_) => eprintln!("Canceled"),
          Item::Definition(_) => eprintln!("Definition"),
          Item::DefStruct(_) => eprintln!("DefStruct"),
          Item::Definiens(_) => eprintln!("Definiens"),
          Item::Block { kind, .. } => eprintln!("{kind:?} block"),
          Item::Pattern(_) => eprintln!("Pattern"),
        }
      }
    }
    self.items += 1;
    match it {
      // reservations not handled by checker
      Item::Reservation { .. } | Item::Section => {}
      Item::Let(vars) => self.read_fixed_vars(vars),
      Item::Given(GivenItem { prop, fixed, intro }) => {
        self.read_proposition(prop);
        self.read_fixed_vars(fixed);
        intro.iter().for_each(|prop| self.read_proposition(prop));
      }
      Item::Assume(intro) => intro.iter().for_each(|prop| self.read_proposition(prop)),
      Item::Take(_) => {}
      Item::TakeAsVar(ty, tm) => {
        let fv = FixedVar { ty: self.intern(ty), def: Some(Box::new(self.intern(tm))) };
        self.lc.fixed_var.push(fv);
      }
      Item::PerCases(PerCases { pos, label, block_thesis, cases, prop, just, thesis }) => {
        self.scope(*label, false, |this| {
          for CaseOrSupposeBlock { pos, label, block_thesis, cs, items, thesis } in cases {
            this.scope(*label, false, |this| {
              let (CaseOrSuppose::Case(props) | CaseOrSuppose::Suppose(props)) = cs;
              props.iter().for_each(|p| this.read_proposition(p));
              for it in items {
                this.read_item(&it.0);
                // if let Some(thesis) = &it.1 {
                //   let _ = this.intern(&thesis.f);
                // }
              }
            });
          }
          this.read_just_prop(prop, just)
        });
        self.push_prop(*label, self.intern(block_thesis))
      }
      Item::AuxiliaryItem(AuxiliaryItem::PrivateStatement(it)) | Item::Thus(it) =>
        self.read_private_stmt(it),
      Item::AuxiliaryItem(AuxiliaryItem::Consider { prop, just, fixed, intro }) => {
        self.read_just_prop(prop, just);
        self.read_fixed_vars(fixed);
        intro.iter().for_each(|prop| self.read_proposition(prop));
      }
      Item::AuxiliaryItem(AuxiliaryItem::Set { ty, .. }) => self.push_fixed_var(ty),
      Item::AuxiliaryItem(AuxiliaryItem::Reconsider { terms, prop, just }) => {
        for (ty, tm) in terms {
          let fv = FixedVar { ty: self.intern(ty), def: Some(Box::new(self.intern(tm))) };
          self.lc.fixed_var.push(fv);
        }
        self.read_just_prop(prop, just);
      }
      Item::AuxiliaryItem(AuxiliaryItem::DefFunc { args, ty, value }) => {
        self.lc.priv_func.push(FuncDef { ty: self.intern(ty), value: self.intern(value) });
      }
      Item::AuxiliaryItem(AuxiliaryItem::DefPred { args, value }) => {}
      Item::Registration(reg) => match reg {
        Registration::Cluster(cl) => self.read_cluster_decl(cl),
        Registration::Identify { kind, conds, corr } => {
          self.read_corr_conds(conds, corr);
          self.push_identify(kind)
        }
        Registration::Reduction { kind, conds, corr } => {
          self.read_corr_conds(conds, corr);
          self.reductions.push(kind.clone())
        }
        Registration::Property { prop, just, .. } => self.read_just_prop(prop, just),
      },
      Item::Scheme(sch) => self.read_scheme(sch),
      Item::Theorem { prop, just } => self.read_just_prop(prop, just),
      Item::DefTheorem { kind, prop } => self.read_proposition(prop),
      Item::Canceled(_) => {}
      Item::Definition(d) => {
        let Definition { pos, label, redef, kind, conds, corr, props, constr, patts } = d;
        self.read_corr_conds(conds, corr);
        for JustifiedProperty { prop, just, .. } in props {
          self.read_just_prop(prop, just)
        }
        if let Some(constr) = constr {
          self.pending_defs.push(PendingDef::Constr(self.g.constrs.push(self.intern(constr))));
        }
        self.lc.formatter.extend(&self.g.constrs, patts)
      }
      Item::DefStruct(DefStruct { pos, label, constrs, cl, conds, corr, patts }) => {
        for c in constrs {
          self.pending_defs.push(PendingDef::Constr(self.g.constrs.push(self.intern(c))));
        }
        self.read_cluster_decl(cl);
        self.read_corr_conds(conds, corr);
        self.lc.formatter.extend(&self.g.constrs, patts)
      }
      Item::Definiens(df) => self.read_definiens(df),
      Item::Block { kind, pos, label, items } => {
        let check = matches!(kind, BlockKind::Definition | BlockKind::Registration);
        self.scope(*label, check, |this| {
          for it in items {
            this.read_item(it);
          }
        });
      }
      Item::Pattern(pat) => self.lc.formatter.push(&self.g.constrs, pat),
    }
  }

  fn read_scheme(&mut self, SchemeBlock { nr, decls, prems, thesis, just, .. }: &SchemeBlock) {
    self.scope(None, false, |this| {
      let sch_funcs = this.lc.sch_func_ty.len();
      let infer_consts = this.lc.infer_const.get_mut().0.len();
      for decl in decls {
        if let SchemeDecl::Func { ty, .. } = decl {
          this.lc.sch_func_ty.0.push(this.intern(ty))
        }
      }
      let mut prems = prems
        .iter()
        .map(|prem| {
          let f = this.intern(&prem.f);
          this.push_prop(prem.label, f.clone());
          f
        })
        .collect();
      let mut thesis = this.intern(&thesis.f);
      this.read_justification(&thesis, just);
      let primary = this.lc.sch_func_ty.0.drain(sch_funcs..).collect();
      this.lc.expand_consts(|c| (&mut prems, &mut thesis).visit(c));
      this.lc.infer_const.get_mut().truncate(infer_consts);
      this.libs.sch.insert((ArticleId::SELF, *nr), Scheme { primary, prems, thesis });
    });
  }

  fn read_definiens(&mut self, df: &Definiens) {
    self.equalities.push(df.clone());
    self.expansions.push(df.clone());
    if let Some(func) = df.equals_expansion() {
      let f = func.pattern.0;
      if !func.expansion.has_func(&self.g.constrs, f) {
        let mut i = 0;
        loop {
          let mut ic = self.lc.infer_const.borrow_mut();
          let Some(asgn) = ic.0.get_mut(i) else { break };
          if let Term::Functor { nr, args } = &asgn.def {
            let (nr, args) = Term::adjust(*nr, args, &self.g.constrs);
            if f == nr {
              let args = &args.to_owned();
              drop(ic);
              if let Some(mut t) = func.expand_if_equal(&self.g, &self.lc, args, 0) {
                t.visit(&mut self.intern_const());
                let Term::Infer(nr) = t else { unreachable!() };
                ic = self.lc.infer_const.borrow_mut();
                ic.0[i].eq_const.insert(nr);
                ic.0[i].has_numbers |= ic[nr].has_numbers;
              }
            }
          }
          i += 1;
        }
        self.equals.entry(df.constr).or_default().push(func);
      }
    }
  }

  fn read_justification(&mut self, thesis: &Formula, just: &Justification) {
    match just {
      Justification::Simple(it) => self.read_inference(thesis, it),
      Justification::Proof { label, thesis: block_thesis, items, .. } => {
        let block_thesis = self.intern(block_thesis);
        assert!(
          ().eq_formula(&self.g, &self.lc, thesis, &block_thesis),
          "\n{thesis:?}\n !=\n{block_thesis:?}"
        );
        self.scope(*label, false, |this| {
          for it in items {
            this.read_item(&it.0);
          }
        });
      }
      Justification::SkippedProof => assert!(matches!(thesis, Formula::True)),
    }
  }

  fn read_just_prop(&mut self, prop: &Proposition, just: &Justification) {
    let f = self.intern(&prop.f);
    self.read_justification(&f, just);
    self.push_prop(prop.label, f);
  }

  fn read_private_stmt(&mut self, it: &PrivateStatement) {
    match it {
      PrivateStatement::Proposition { prop, just } => self.read_just_prop(prop, just),
      PrivateStatement::IterEquality { start, label, lhs, steps } => {
        let mut lhs = self.intern(lhs);
        let llhs = lhs.clone();
        for (rhs, step) in steps {
          let rhs = self.intern(rhs);
          self.read_inference(&self.g.reqs.mk_eq(lhs, rhs.clone()), step);
          lhs = rhs;
        }
        self.push_prop(*label, self.g.reqs.mk_eq(llhs, lhs))
      }
      PrivateStatement::Now { label, thesis, items, .. } => {
        self.scope(*label, true, |this| {
          for it in &**items {
            this.read_item(it);
          }
        });
        self.push_prop(*label, self.intern(thesis));
      }
    }
  }

  fn read_corr_conds(&mut self, conds: &[CorrCond], corr: &Option<Correctness>) {
    conds.iter().for_each(|c| self.read_just_prop(&c.prop, &c.just));
    if let Some(c) = corr {
      self.read_just_prop(&c.prop, &c.just)
    }
  }

  fn push_identify(&mut self, id: &Identify) {
    if let IdentifyKind::Func { lhs, rhs } = &id.kind {
      let mut ic = self.lc.infer_const.borrow();
      let mut i = InferId::default();
      while let Some(asgn) = ic.get(i) {
        if matches!(asgn.def, Term::Functor { .. }) {
          if let Some(subst) = id.try_apply_lhs(&self.g, &self.lc, lhs, &asgn.def) {
            let mut tm = subst.inst_term(rhs, 0);
            drop(ic);
            tm.visit(&mut self.intern_const());
            let Term::Infer(n) = tm else { unreachable!() };
            self.lc.infer_const.borrow_mut()[i].eq_const.insert(n);
            ic = self.lc.infer_const.borrow();
          }
        }
        i.0 += 1;
      }
      let Term::Functor { nr, args } = lhs else { unreachable!() };
      let k = ConstrKind::Func(Term::adjusted_nr(*nr, &self.g.constrs));
      self.func_ids.entry(k).or_default().push(self.identify.len());
    }
    self.identify.push(id.clone());
  }

  /// RoundUpFurther
  fn round_up_further<T>(&mut self, rounded_up: BTreeMap<InferId, T>) {
    if rounded_up.is_empty() {
      return
    }
    let mut i = *rounded_up.first_key_value().unwrap().0;
    let mut ic = self.lc.infer_const.borrow();
    while let Some(asgn) = ic.get(i) {
      match &asgn.def {
        Term::Functor { args, .. }
        | Term::Selector { args, .. }
        | Term::Aggregate { args, .. }
        | Term::SchFunc { args, .. } => {
          if args.iter().any(|t| matches!(t, Term::Infer(i) if rounded_up.contains_key(i))) {
            let mut ty = asgn.def.round_up_type(&self.g, &self.lc).to_owned();
            ty.attrs.1.round_up_with(&self.g, &self.lc, &asgn.ty);
            ty.attrs.1.visit(&mut self.intern_const());
            drop(ic);
            self.lc.infer_const.borrow_mut()[i].ty = *ty;
            ic = self.lc.infer_const.borrow();
          }
        }
        Term::Numeral(_) => {
          let mut attrs = asgn.ty.attrs.1.clone();
          attrs.round_up_with(&self.g, &self.lc, &asgn.ty);
          attrs.visit(&mut self.intern_const());
          drop(ic);
          self.lc.infer_const.borrow_mut()[i].ty.attrs.1 = attrs;
          ic = self.lc.infer_const.borrow();
        }
        _ => {}
      }
      i.0 += 1;
    }
    //
  }

  fn read_cluster_decl(&mut self, cl: &ClusterDecl) {
    self.read_corr_conds(&cl.conds, &cl.corr);
    match &cl.kind {
      ClusterDeclKind::R(cl) => {
        let mut cl = cl.clone();
        cl.consequent.1.visit(&mut self.intern_const());
        self.g.clusters.registered.push(cl)
      }
      ClusterDeclKind::F(cl) => {
        let mut cl = cl.clone();
        cl.consequent.1.visit(&mut self.intern_const());
        let mut rounded_up = BTreeMap::new();
        for (i, asgn) in self.lc.infer_const.borrow().enum_iter() {
          let mut attrs = asgn.ty.attrs.1.clone();
          let orig = attrs.attrs().len();
          cl.round_up_with(&self.g, &self.lc, &asgn.def, &asgn.ty, &mut attrs);
          assert!(matches!(attrs, Attrs::Consistent(_)));
          attrs.round_up_with(&self.g, &self.lc, &asgn.ty);
          if attrs.attrs().len() > orig {
            attrs.visit(&mut self.intern_const());
            rounded_up.insert(i, attrs);
          }
        }
        let (_, i) = (self.g.clusters.functor)
          .equal_range(|a| FunctorCluster::cmp_term(&a.term, &self.g.constrs, &cl.term));
        self.g.clusters.functor.insert_at(i, cl);
        let ic = self.lc.infer_const.get_mut();
        for (&i, attrs) in &mut rounded_up {
          self.lc.infer_const.get_mut()[i].ty.attrs.1 = std::mem::take(attrs);
        }
        self.round_up_further(rounded_up);
      }
      ClusterDeclKind::C(cl) => {
        let mut cl = cl.clone();
        cl.consequent.1.visit(&mut self.intern_const());
        let mut rounded_up = BTreeMap::new();
        for (i, asgn) in self.lc.infer_const.borrow().enum_iter() {
          if let Some(subst) = cl.try_apply(&self.g, &self.lc, &asgn.ty.attrs.1, &asgn.ty) {
            let mut attrs = asgn.ty.attrs.1.clone();
            let orig = attrs.attrs().len();
            // eprintln!("enlarge {:?} by {:?}", self, cl.consequent.1);
            attrs.enlarge_by(&self.g.constrs, &cl.consequent.1, |a| {
              a.visit_cloned(&mut Inst::new(&subst))
            });
            assert!(matches!(attrs, Attrs::Consistent(_)));
            attrs.round_up_with(&self.g, &self.lc, &asgn.ty);
            if attrs.attrs().len() > orig {
              attrs.visit(&mut self.intern_const());
              rounded_up.insert(i, attrs);
            }
          }
        }
        self.g.clusters.conditional.push(&self.g.constrs, cl);
        let ic = self.lc.infer_const.get_mut();
        for (&i, attrs) in &mut rounded_up {
          self.lc.infer_const.get_mut()[i].ty.attrs.1 = std::mem::take(attrs);
        }
        self.round_up_further(rounded_up);
      }
    }
  }

  fn read_inference(&mut self, thesis: &Formula, it: &Inference) {
    match it.kind {
      InferenceKind::By { linked } => {
        let neg_thesis = thesis.clone().mk_neg();
        let mut premises = vec![&neg_thesis];
        if linked {
          premises.push(self.props.last().unwrap());
        }
        premises.extend(it.refs.iter().map(|r| match r.kind {
          ReferenceKind::Priv(lab) => &self.props[self.labels[lab].unwrap()],
          ReferenceKind::Thm(thm) => &self.libs.thm[&thm],
          ReferenceKind::Def(def) => &self.libs.def[&def],
        }));
        Checker {
          g: &mut self.g,
          lc: &mut self.lc,
          expansions: &self.expansions,
          equals: &self.equals,
          identify: &self.identify,
          func_ids: &self.func_ids,
          reductions: &self.reductions,
          idx: self.inference_nr,
          pos: it.pos,
        }
        .justify(premises);
        self.inference_nr += 1;
      }
      InferenceKind::From { sch } => stat("from"),
    }
  }

  #[allow(clippy::blocks_in_if_conditions)]
  fn dbg_scope_check(&self) {
    let ic = self.lc.infer_const.borrow();
    let infer_const = ic.len();

    struct Checker(u32, bool);
    impl Visit for Checker {
      fn abort(&self) -> bool { !self.1 }
      fn visit_term(&mut self, tm: &Term) {
        self.super_visit_term(tm);
        // Term::PrivFunc { nr, args, value } => self.2 &= nr.0 < self.0,
        if let Term::Infer(nr) = tm {
          self.1 &= nr.0 < self.0
        }
      }
    }
    fn with(ic: usize, f: impl FnOnce(&mut Checker)) -> bool {
      let mut ck = Checker(ic as u32, true);
      f(&mut ck);
      ck.1
    }
    for (i, c) in self.g.constrs.functor.0.iter().enumerate() {
      if !with(infer_const, |ck| ck.visit_type(&c.ty)) {
        panic!("bad functor: F{i:?}: {c:?}")
      }
    }
    for c in &self.lc.term_cache.borrow().terms {
      if !with(infer_const, |ck| {
        ck.visit_term(&c.0);
        ck.visit_type(&c.1)
      }) {
        panic!("bad term cache: {c:?}")
      }
    }
    for (i, c) in ic.enum_iter() {
      if !with(infer_const, |ck| {
        ck.visit_term(&c.def);
        ck.visit_type(&c.ty)
      }) {
        panic!("bad infer const: ?{i:?} := {c:?}")
      }
    }
  }
}
