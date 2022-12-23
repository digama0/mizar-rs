use crate::checker::{Atoms, Conjunct, Dnf, Open, OrUnsat, Unsat};
use crate::equate::Equalizer;
use crate::types::*;
use crate::{vprintln, CheckLocus, Equate, ExpandPrivFunc, Global, LocalContext, Visit, VisitMut};
use enum_map::{Enum, EnumMap};
use itertools::Itertools;
use std::collections::{BTreeMap, HashMap};

const ENABLE_UNIFIER: bool = true;

#[derive(Default)]
struct EqTerm {
  id: EqClassId,
  ty_class: Vec<Type>,
  supercluster: Attrs,
  terms: EnumMap<ComplexTermKind, Vec<EqMarkId>>,
}

pub struct Unifier<'a> {
  g: &'a Global,
  lc: &'a mut LocalContext,
  infer: HashMap<InferId, EqClassId>,
  eq_class: IdxVec<EqClassId, EqTerm>,
  bas: &'a EnumMap<bool, Atoms>,
}

#[derive(Copy, Clone, Debug, Enum)]
enum ComplexTermKind {
  Functor,
  SchFunc,
  PrivFunc,
  Aggregate,
  Selector,
  Fraenkel,
  Choice,
}
use ComplexTermKind as CTK;

impl Term {
  fn complex_kind(&self) -> Option<ComplexTermKind> {
    match self {
      Term::Functor { .. } => Some(CTK::Functor),
      Term::SchFunc { .. } => Some(CTK::SchFunc),
      Term::PrivFunc { .. } => Some(CTK::PrivFunc),
      Term::Aggregate { .. } => Some(CTK::Aggregate),
      Term::Selector { .. } => Some(CTK::Selector),
      Term::Fraenkel { .. } => Some(CTK::Fraenkel),
      Term::Choice { .. } => Some(CTK::Choice),
      _ => None,
    }
  }
}

impl<'a> Unifier<'a> {
  /// InitUnifier
  pub fn new(eq: Equalizer<'a>, bas: &'a EnumMap<bool, Atoms>) -> Self {
    let mut u = Self {
      g: eq.g,
      lc: eq.lc,
      infer: Default::default(),
      eq_class: IdxVec::from_default(eq.next_eq_class.into_usize()),
      bas,
    };
    for etm in eq.terms.0 {
      let ec = &mut u.eq_class[etm.id];
      if !etm.eq_class.is_empty() {
        for m in etm.eq_class {
          let t = &u.lc.marks[m].0;
          match t.complex_kind() {
            Some(k) => ec.terms[k].push(m),
            None => match *t {
              Term::Infer(i) => drop(u.infer.insert(i, etm.id)),
              Term::Numeral(_) => {}
              _ => unreachable!(),
            },
          }
        }
        // TODO: numeric_value
        ec.ty_class = etm.ty_class;
        ec.supercluster = etm.supercluster;
      }
    }
    for i in 0..eq.next_eq_class.0 {
      u.eq_class[EqClassId(i)].id = EqClassId(i)
    }
    u
  }

  /// Verify: Attempts to prove f |- false
  fn falsify(&mut self, mut f: Formula) -> OrUnsat<()> {
    Standardize { g: self.g, lc: self.lc }.visit_formula(&mut f, 0);
    if crate::UNIFY_HEADER {
      eprintln!("verifying: {f:?}");
    }
    let mut fvars = IdxVec::default();
    // Suppose f = ∀ xs, F(xs).
    // First, introduce metavariables ("free vars") to obtain a formula F(?v)
    OpenAsFreeVar(&mut fvars.0).open_quantifiers(&mut f, false);
    let bas = self.bas;
    let mut u = self.unify(&fvars);

    // want to show: ∃ ?v. |- !F(?v)
    // Normalize !F(?v) into DNF: ∃ ?v. |- C_1(?v) \/ ... \/ C_n(?v)
    // If we get !F(?v) = true then we are done.
    let mut atoms = Atoms::default();
    let Dnf::Or(clauses) = atoms.normalize(u.g, u.lc, f, false) else { return Err(Unsat) };

    // For the remainder we prove each clause separately.
    // Any of them being true will finish the goal.
    'next: for clause in clauses {
      // We want to show: ∃ ?v. |- C(?v)
      assert!(!clause.0.is_empty()); // this would be a proof but is also not reachable

      // The strategy is to come up with an "assignment" P(?v) such that
      // ∃ ?v. P(?v) is true structurally and ∀ ?v. (P(?v) -> C(?v)) holds.
      // We write P(?v) in DNF, and ensure that each conjunct is satisfiable,
      // so it suffices to check that P(?v) is not identically false to ensure ∃ ?v. P(?v).

      let mut insts = vec![];
      // C(?v) is a conjunction A_1(?v) /\ ... /\ A_n(?v);
      // for each A_i(?v) we will construct P_i(?v) and AND them together
      for (a, val) in clause.0 {
        // Negate the conclusion to !A_i(?v) |- false to match the usual polarity,
        // and get an instantiation P_i(?v) such that P_i(?v), !A_i(?v) |- false.
        match u.compute_inst(bas, &atoms.0[a], !val) {
          // A_i(?v) is true without our help
          Dnf::True => {}
          // We failed to construct an instantiation,
          // the strongest P_i(?v) we could come up with is 'false'
          Dnf::Or(conjs) if conjs.is_empty() => continue 'next,
          // Otherwise we push P_i(?v) on insts (we delay the join operation
          // in case we can get one of the other two cases on some atoms)
          Dnf::Or(conjs) => insts.push(conjs),
        }
      }
      // Unless /\_i P_i(?v) is the empty disjunction (false), it is satisfiable and we are done
      if !Dnf::and_many(insts).is_false() {
        return Err(Unsat)
      }
    }
    // falsification failed
    Ok(())
  }

  /// Unifiable
  fn unify_one(&mut self, fs: &[&Formula]) -> OrUnsat<()> {
    //
    Ok(())
  }

  /// Unification
  pub fn run(&mut self) -> OrUnsat<()> {
    let univ =
      self.bas[true].0 .0.iter().filter(|f| matches!(f, Formula::ForAll { .. })).collect_vec();
    for &f in &univ {
      self.falsify(f.clone())?;
    }
    if ENABLE_UNIFIER {
      for f in &univ {
        self.unify_one(&[f])?;
      }
      for (f1, f2) in univ.iter().tuple_combinations() {
        self.unify_one(&[f1, f2])?;
      }
    }

    let mut fraenkel_fmlas = vec![];
    for (pos, bas) in self.bas.iter() {
      for f in &bas.0 .0 {
        if let Formula::Pred { nr, args } = f {
          let (nr, args) = Formula::adjust_pred(*nr, args, &self.g.constrs);
          if self.g.reqs.belongs_to() == Some(nr) {
            for &m in &self.eq_class[args[1].unmark(self.lc).class().unwrap()].terms[CTK::Fraenkel]
            {
              if let Term::Fraenkel { args: tys, scope, compr } = &self.lc.marks[m].0 {
                let (tys, scope, compr) = (tys.clone(), (**scope).clone(), (**compr).clone());
                let mut fm = args[0].clone().not_in_fraenkel(tys, scope, compr, &self.g.reqs);
                fm.distribute_quantifiers(&self.g.constrs, 0);
                fraenkel_fmlas.push(fm.maybe_neg(!pos))
              }
            }
            for f in fraenkel_fmlas.drain(..) {
              self.falsify(f)?;
            }
          }
        }
      }
    }
    Ok(())
  }
}

struct OpenAsFreeVar<'a>(&'a mut Vec<Type>);

impl Open for OpenAsFreeVar<'_> {
  fn mk_var(n: u32) -> Term { Term::FreeVar(FVarId(n)) }
  fn base(&self) -> u32 { self.0.len() as u32 }
  fn new_var(&mut self, mut ty: Type) { self.0.push(ty); }
}

impl Term {
  /// Given a fraenkel term `{ F(xs) where xs : P(xs) }` and a main term `self`,
  /// constructs the formula equivalent to `¬(self ∈ { F(xs) where xs : P(xs) })`,
  /// that is: `¬ ∃ xs, self = F(xs) /\ P(xs)`
  fn not_in_fraenkel(
    self, args: Box<[Type]>, scope: Term, compr: Formula, reqs: &RequirementIndexes,
  ) -> Formula {
    let mut conjs = vec![reqs.mk_eq(self, scope)];
    compr.append_conjuncts_to(&mut conjs);
    let mut f = Formula::Neg { f: Box::new(Formula::And { args: conjs }) };
    for ty in args.into_vec().into_iter().rev() {
      f = Formula::ForAll { dom: Box::new(ty), scope: Box::new(f) }
    }
    f
  }
}

struct Standardize<'a> {
  g: &'a Global,
  lc: &'a mut LocalContext,
}

impl VisitMut for Standardize<'_> {
  fn visit_term(&mut self, tm: &mut Term, depth: u32) {}
  fn visit_terms(&mut self, tms: &mut [Term], depth: u32) {}

  fn visit_type(&mut self, ty: &mut Type, depth: u32) {
    assert!(!CheckLocus::get(|cl| {
      cl.visit_attrs(&ty.attrs.0, depth);
      cl.visit_attrs(&ty.attrs.1, depth);
    }));
    self.visit_terms(&mut ty.args, depth);
  }

  fn visit_formula(&mut self, f: &mut Formula, depth: u32) {
    self.standardize_formula(f, true, depth)
  }
}

impl Standardize<'_> {
  /// * pos = true: PositivelyStandardized
  /// * pos = false: NegativelyStandardized
  fn standardize_formula(&mut self, f: &mut Formula, pos: bool, depth: u32) {
    loop {
      match f {
        Formula::Neg { f } => self.standardize_formula(f, !pos, depth),
        Formula::And { args } =>
          args.iter_mut().for_each(|f| self.standardize_formula(f, pos, depth)),
        Formula::ForAll { dom, scope, .. } =>
          if pos {
            self.visit_type(dom, depth);
            self.lc.bound_var.push(std::mem::take(dom));
            self.standardize_formula(scope, pos, depth + 1);
            **dom = self.lc.bound_var.0.pop().unwrap();
          },
        Formula::SchPred { args, .. } | Formula::Pred { args, .. } => self.visit_terms(args, depth),
        Formula::Attr { mut nr, args } => {
          let (main, rest) = args.split_last_mut().unwrap();
          self.visit_term(main, depth);
          let attr = Attr { nr, pos: true, args: rest.to_owned().into() };
          *f = Box::new(std::mem::take(main)).mk_is(self.g, self.lc, attr);
          continue
        }
        Formula::PrivPred { args, value, .. } => {
          self.visit_terms(args, depth);
          ExpandPrivFunc { ctx: &self.g.constrs }.visit_formula(value, depth);
        }
        Formula::Is { term, ty } => {
          self.visit_term(term, depth);
          self.visit_type(ty, depth)
        }
        Formula::FlexAnd { .. } | Formula::True => {}
      }
      break
    }
  }
}

impl Term {
  /// ChReconQualFrm
  fn mk_is(self: Box<Term>, g: &Global, lc: &LocalContext, attr: Attr) -> Formula {
    let mut ty = self.get_type_uncached(g, lc);
    ty.attrs.0.insert(&g.constrs, attr);
    if matches!(ty.attrs.0, Attrs::Inconsistent) {
      Formula::Neg { f: Box::new(Formula::True) }
    } else {
      ty.attrs.1 = ty.attrs.0.clone();
      Formula::Is { term: self, ty: Box::new(ty) }
    }
  }
}

struct Unify<'a> {
  g: &'a Global,
  lc: &'a LocalContext,
  infer: &'a HashMap<InferId, EqClassId>,
  eq_class: &'a IdxVec<EqClassId, EqTerm>,
  fvars: &'a IdxVec<FVarId, Type>,
  cache: BTreeMap<(FVarId, EqClassId), Dnf<FVarId, EqClassId>>,
  base: u32,
  depth: u32,
}

impl Unifier<'_> {
  fn unify<'a>(&'a mut self, fvars: &'a IdxVec<FVarId, Type>) -> Unify<'a> {
    Unify {
      g: self.g,
      lc: self.lc,
      infer: &self.infer,
      eq_class: &self.eq_class,
      fvars,
      cache: Default::default(),
      base: 0,
      depth: 0,
    }
  }
}

impl Unify<'_> {
  /// Constructs an instantiation P(?v) such that
  /// * pos = true: COMPInstAsTrue - P(?v) /\ F(?v) |- false
  /// * pos = false: COMPInstAsFalse - P(?v) /\ !F(?v) |- false
  fn compute_inst(
    &mut self, bas: &EnumMap<bool, Atoms>, f: &Formula, pos: bool,
  ) -> Dnf<FVarId, EqClassId> {
    let mut inst = Dnf::FALSE;
    match f {
      // We already DNF'd f so there should be no top-level propositional connectives remaining
      Formula::True | Formula::Neg { .. } | Formula::And { .. } => unreachable!(),
      Formula::Pred { mut nr, args } => {
        let (nr, args) = Formula::adjust_pred(nr, args, &self.g.constrs);
        let pred = &self.g.constrs.predicate[nr];
        if pred.properties.get(if pos {
          PropertyKind::Irreflexivity
        } else {
          PropertyKind::Reflexivity
        }) {
          for ec in &self.eq_class.0 {
            let t = Term::EqClass(ec.id);
            let mut inst1 = self.unify_term(&args[pred.arg1 as usize], &t);
            if !inst1.is_false() {
              inst1.mk_and(self.unify_term(&args[pred.arg2 as usize], &t));
              inst.mk_or(inst1);
            }
          }
        }
        if self.g.reqs.belongs_to() == Some(nr) {
          let [arg1, arg2] = args else { unreachable!() };
          if let Some(empty) = self.g.reqs.empty() {
            for ec in &self.eq_class.0 {
              if ec.supercluster.find0(&self.g.constrs, empty, pos) {
                let mut inst1 = self.unify_term(arg2, &Term::EqClass(ec.id));
                if !inst1.is_false() {
                  if let (false, Some(element)) = (pos, self.g.reqs.element()) {
                    let ty = Type { args: vec![Term::EqClass(ec.id)], ..Type::new(element.into()) };
                    let mut inst2 = Dnf::FALSE;
                    for ec2 in &self.eq_class.0 {
                      if ec2.ty_class.iter().any(|ty2| ().eq_radices(self.g, self.lc, ty2, &ty)) {
                        inst2.mk_or(self.unify_term(arg1, &Term::EqClass(ec2.id)));
                      }
                    }
                    inst1.mk_and(inst2);
                  }
                  inst.mk_or(inst1);
                }
              }
            }
          }
          if pos {
            for f in &bas[false].0 .0 {
              if let Formula::Is { term, ty } = f {
                if let TypeKind::Mode(n) = ty.kind {
                  let (n, args) = Type::adjust(n, &ty.args, &self.g.constrs);
                  if self.g.reqs.element() == Some(n) {
                    let mut inst1 = self.unify_term(arg1, term);
                    if !inst1.is_false() {
                      inst1.mk_and(self.unify_term(arg2, &args[0]));
                      inst.mk_or(inst1);
                    }
                  }
                }
              }
            }
          }
        } else if self.g.reqs.inclusion() == Some(nr) {
          if let Some(power) = self.g.reqs.power_set() {
            let [arg1, arg2] = args else { unreachable!() };
            if pos {
              for f in &bas[false].0 .0 {
                if let Formula::Is { term, ty } = f {
                  if let TypeKind::Mode(n) = ty.kind {
                    let (n, args) = Type::adjust(n, &ty.args, &self.g.constrs);
                    if self.g.reqs.element() == Some(n) {
                      let mut inst1 = self.unify_term(arg1, term);
                      if !inst1.is_false() {
                        if let Term::EqClass(ec) = *arg2 {
                          let Term::EqClass(ec2) = args[0] else { unreachable!()};
                          if self.get_eq_class(&Term::Functor {
                            nr: power,
                            args: Box::new([Term::EqClass(ec)]),
                          }) == Some(ec2)
                          {
                            inst.mk_or(inst1)
                          }
                        } else {
                          let t = Term::Functor { nr: power, args: Box::new([arg2.clone()]) };
                          inst1.mk_and(self.unify_term(&t, &args[0]));
                          inst.mk_or(inst1)
                        }
                      }
                    }
                  }
                }
              }
            } else if let Some(element) = self.g.reqs.element() {
              for ec1 in &self.eq_class.0 {
                let mut inst1 = self.unify_term(arg2, &Term::EqClass(ec1.id));
                if !inst1.is_false() {
                  let mut inst2 = Dnf::FALSE;
                  if let Some(ec2) = self.get_eq_class(&Term::Functor {
                    nr: power,
                    args: Box::new([Term::EqClass(ec1.id)]),
                  }) {
                    let ty = Type { args: vec![Term::EqClass(ec2)], ..Type::new(element.into()) };
                    for ec2 in &self.eq_class.0 {
                      if ec2.ty_class.iter().any(|ty2| ().eq_radices(self.g, self.lc, ty2, &ty)) {
                        inst2.mk_or(self.unify_term(arg1, &Term::EqClass(ec2.id)));
                      }
                    }
                    inst1.mk_and(inst2);
                  }
                }
              }
            }
          }
          // FIXME: the original control flow seems very haphazard/inconsistent here
          if !pos {
            return inst
          }
        } else if self.g.reqs.less_or_equal() == Some(nr) {
          let [arg1, arg2] = args else { unreachable!() };
          if !pos {
            for f2 in &bas[true].0 .0 {
              inst.mk_or(self.unify_formula(f, f2));
            }
          }
          // TODO: numeric_value
          if let (Some(positive), Some(negative)) = (self.g.reqs.positive(), self.g.reqs.negative())
          {
            for ec1 in &self.eq_class.0 {
              let mut inst1 = self.unify_term(arg1, &Term::EqClass(ec1.id));
              if !inst1.is_false() {
                let mut inst2 = Dnf::FALSE;
                if pos {
                  let pos1 = ec1.supercluster.find0(&self.g.constrs, positive, true);
                  let nonneg1 = ec1.supercluster.find0(&self.g.constrs, negative, false);
                  for ec2 in &self.eq_class.0 {
                    if pos1 && ec2.supercluster.find0(&self.g.constrs, positive, false)
                      || nonneg1 && ec2.supercluster.find0(&self.g.constrs, negative, true)
                    {
                      inst2.mk_or(self.unify_term(arg2, &Term::EqClass(ec2.id)));
                    }
                  }
                } else {
                  let nonpos1 = ec1.supercluster.find0(&self.g.constrs, positive, false);
                  for ec2 in &self.eq_class.0 {
                    if nonpos1 && ec2.supercluster.find0(&self.g.constrs, negative, false) {
                      inst2.mk_or(self.unify_term(arg2, &Term::EqClass(ec2.id)));
                    }
                  }
                }
                inst1.mk_and(inst2);
                inst.mk_or(inst1);
              }
            }
          }
          if !pos {
            return inst
          }
        } else if self.g.reqs.equals_to() == Some(nr) {
          let [arg1, arg2] = args else { unreachable!() };
          // TODO: numeric_value
          if !pos {
            return inst
          }
        }
      }
      Formula::Attr { mut nr, args } => {
        // UniAttrFrm
        let (arg0, args) = args.split_last().unwrap();
        for attr in self.eq_class[arg0.class().unwrap()].supercluster.attrs() {
          if attr.nr == nr && attr.pos != pos {
            inst.mk_or(self.unify_terms(args, &attr.args));
          }
        }
        return inst
      }
      Formula::Is { term, ty } => {
        if pos {
          for f2 in &bas[!pos].0 .0 {
            if let Formula::Is { term: term2, ty: ty2 } = f2 {
              let mut inst1 = self.unify_term(term, term2);
              if !inst1.is_false() {
                let mut inst2 = Dnf::FALSE;
                match ty2.kind {
                  TypeKind::Mode(n2) =>
                    if let TypeKind::Mode(n) = ty.kind {
                      let (n, args) = Type::adjust(n, &ty.args, &self.g.constrs);
                      let mut pty = CowBox::Borrowed(&**ty);
                      assert!(n != ModeId::ANY);
                      while let TypeKind::Mode(pn) = pty.kind {
                        if pn < n {
                          break
                        }
                        inst2.mk_or(self.unify_radix_type(&pty, ty2));
                        pty = CowBox::Owned(pty.widening(self.g).unwrap());
                      }
                    },
                  TypeKind::Struct(_) =>
                    if let Some(ty) = ty2.widening_of(self.g, ty) {
                      inst2 = self.unify_radix_type(&ty, ty2);
                    },
                }
                inst1.mk_and(inst2);
                inst.mk_or(inst1);
              }
            }
          }
          for ec in &self.eq_class.0 {
            let mut inst1 = self.unify_term(term, &Term::EqClass(ec.id));
            if !inst1.is_false() {
              let mut inst2 = Dnf::FALSE;
              for attr in ty.attrs.1.attrs() {
                for attr2 in ec.supercluster.attrs() {
                  self.or_unify_attr(attr, attr2, false, &mut inst2)
                }
              }
              inst1.mk_and(inst2);
              inst.mk_or(inst1);
            }
          }
        } else {
          for ec in &self.eq_class.0 {
            let mut inst1 = self.unify_term(term, &Term::EqClass(ec.id));
            if !inst1.is_false() {
              inst1.mk_and(self.unify_eq_class_types(ec, ty));
              inst.mk_or(inst1);
            }
          }
        }
        return inst
      }
      _ => {}
    }
    for f2 in &bas[!pos].0 .0 {
      inst.mk_or(self.unify_formula(f, f2));
    }
    inst
  }

  fn get_eq_class(&self, tm: &Term) -> Option<EqClassId> {
    self.equate_class().get(self.g, self.lc, tm)
  }

  /// InstCollection.UNIEqClassTyps
  fn unify_eq_class_types(&mut self, ec: &EqTerm, ty: &Type) -> Dnf<FVarId, EqClassId> {
    let mut inst = Dnf::FALSE;
    for ty2 in &ec.ty_class {
      inst.mk_or(self.unify_radix_type(ty, ty2))
    }
    inst.mk_and(self.unify_subset_attrs(&ty.attrs.0, &ec.supercluster, true));
    inst
  }

  /// * pos = true: InstCollection.UNIAttr
  /// * pos = false: InstCollection.UNIAttr1
  fn or_unify_attr(
    &mut self, attr1: &Attr, attr2: &Attr, pos: bool, out: &mut Dnf<FVarId, EqClassId>,
  ) {
    let (n1, args1) = attr1.adjust(&self.g.constrs);
    let (n2, args2) = attr2.adjust(&self.g.constrs);
    if n1 == n2 && (attr1.pos == attr2.pos) == pos {
      out.mk_or(self.unify_terms(args1, args2))
    }
  }

  /// InstCollection.UNIRadices
  fn unify_radix_type(&mut self, ty1: &Type, ty2: &Type) -> Dnf<FVarId, EqClassId> {
    match (ty1.kind, ty2.kind) {
      (TypeKind::Mode(n1), TypeKind::Mode(n2)) => {
        let (n1, args1) = Type::adjust(n1, &ty1.args, &self.g.constrs);
        let (n2, args2) = Type::adjust(n2, &ty2.args, &self.g.constrs);
        if n1 == n2 {
          self.unify_terms(args1, args2)
        } else {
          Dnf::FALSE
        }
      }
      (TypeKind::Struct(n1), TypeKind::Struct(n2)) if n1 == n2 =>
        self.unify_terms(&ty1.args, &ty2.args),
      _ => Dnf::FALSE,
    }
  }

  /// InstCollection.UNIInclClusters
  fn unify_subset_attrs(
    &mut self, attrs1: &Attrs, attrs2: &Attrs, fwd: bool,
  ) -> Dnf<FVarId, EqClassId> {
    let Attrs::Consistent(attrs1) = attrs1 else { unreachable!() };
    let Attrs::Consistent(attrs2) = attrs2 else { unreachable!() };
    let mut inst = Dnf::True;
    for attr1 in attrs1 {
      let n = attr1.adjusted_nr(&self.g.constrs);
      for attr2 in attrs2 {
        if attr2.adjusted_nr(&self.g.constrs) >= n {}
      }
      let mut inst1 = Dnf::FALSE;
      for (attr2, _) in attrs2
        .iter()
        .map(|a| (a, a.adjusted_nr(&self.g.constrs)))
        .skip_while(|a| a.1 < n)
        .take_while(|a| a.1 <= n)
      {
        if fwd {
          self.or_unify_attr(attr1, attr2, true, &mut inst1);
        } else {
          self.or_unify_attr(attr2, attr1, true, &mut inst1);
        }
      }
      inst.mk_and(inst1);
      if inst.is_false() {
        break
      }
    }
    inst
  }

  /// InstCollection.UNITyp
  fn unify_type(&mut self, ty1: &Type, ty2: &Type) -> Dnf<FVarId, EqClassId> {
    if ty1.kind == ty2.kind {
      let mut inst = self.unify_subset_attrs(&ty1.attrs.0, &ty2.attrs.1, true);
      if !inst.is_false() {
        inst.mk_and(self.unify_subset_attrs(&ty2.attrs.0, &ty1.attrs.1, false));
        if !inst.is_false() {
          inst.mk_and(self.unify_radix_type(ty1, ty2));
        }
      }
      inst
    } else {
      Dnf::FALSE
    }
  }

  /// InstCollection.UNIFunc
  fn unify_func(&mut self, n1: FuncId, args1: &[Term], t2: &Term) -> Dnf<FVarId, EqClassId> {
    let Term::Functor { nr: mut n2, args: args2 } = t2 else { return Dnf::FALSE };
    if n1 == n2 {
      self.unify_terms(args1, args2)
    } else {
      let (n1, args1) = Term::adjust(n1, args1, &self.g.constrs);
      let (n2, args2) = Term::adjust(n2, args2, &self.g.constrs);
      if n1 == n2 {
        self.unify_terms(args1, args2)
      } else {
        Dnf::FALSE
      }
    }
  }

  /// InstCollection.UNIFraenkelTrm
  fn unify_fraenkel(
    &mut self, args1: &[Type], scope1: &Term, compr1: &Formula, args2: &[Type], scope2: &Term,
    compr2: &Formula,
  ) -> Dnf<FVarId, EqClassId> {
    if args1.len() != args2.len() {
      return Dnf::FALSE
    }
    let depth = self.depth;
    let mut inst = Dnf::True;
    for (ty1, ty2) in args1.iter().zip(args2) {
      inst.mk_and(self.unify_type(ty1, ty2));
      self.depth += 1;
    }
    if !inst.is_false() {
      inst.mk_and(self.unify_term(scope1, scope2));
      if !inst.is_false() {
        inst.mk_and(self.unify_formula(compr1, compr2))
      }
    }
    self.depth = depth;
    inst
  }

  /// InstCollection.UNITrm
  fn unify_term(&mut self, t1: &Term, t2: &Term) -> Dnf<FVarId, EqClassId> {
    macro_rules! function_like {
      ($tk:ident { $nr:expr, $args:expr }) => {{
        let mut inst = match t2 {
          Term::$tk { nr, args, .. } if $nr == nr => self.unify_terms($args, args),
          _ => Dnf::FALSE,
        };
        for &m in &self.eq_class[self.get_eq_class(t2).unwrap()].terms[CTK::$tk] {
          let Term::$tk { nr, args, .. } = &self.lc.marks[m].0 else { unreachable!() };
          if $nr == nr {
            inst.mk_or(self.unify_terms($args, args))
          }
        }
        inst
      }};
    }
    match t1 {
      &Term::FreeVar(n) =>
        if let Some(ec) = self.get_eq_class(t2) {
          if let Some(inst) = self.cache.get(&(n, ec)) {
            inst.clone()
          } else {
            let mut inst = self.unify_eq_class_types(&self.eq_class[ec], &self.fvars[n].clone());
            inst.mk_and_single(n, ec);
            self.cache.insert((n, ec), inst.clone());
            inst
          }
        } else {
          Dnf::FALSE
        },
      Term::Bound(n1) => Dnf::mk_bool(matches!(t2, Term::Bound(n2) if n1.0 - self.base == n2.0)),
      Term::Functor { mut nr, args } => {
        let mut inst = self.unify_func(nr, args, t2);
        for &m in &self.eq_class[self.get_eq_class(t2).unwrap()].terms[CTK::Functor] {
          inst.mk_or(self.unify_func(nr, args, &self.lc.marks[m].0))
        }
        inst
      }
      Term::Aggregate { nr, args } => function_like!(Aggregate { nr, args }),
      Term::SchFunc { nr, args } => function_like!(SchFunc { nr, args }),
      Term::PrivFunc { nr, args, .. } => function_like!(PrivFunc { nr, args }),
      Term::Selector { nr, args } => function_like!(Selector { nr, args }),
      Term::Fraenkel { args: a1, scope: s1, compr: c1 } => {
        let mut inst = if let Term::Fraenkel { args: a2, scope: s2, compr: c2 } = t2 {
          self.unify_fraenkel(a1, s1, c1, a2, s2, c2)
        } else {
          Dnf::FALSE
        };
        let base = self.base;
        self.base = self.depth;
        for &m in &self.eq_class[self.get_eq_class(t2).unwrap()].terms[CTK::Fraenkel] {
          let Term::Fraenkel { args: a2, scope: s2, compr: c2 } = &self.lc.marks[m].0
          else { unreachable!() };
          inst.mk_or(self.unify_fraenkel(a1, s1, c1, a2, s2, c2))
        }
        self.base = base;
        inst
      }
      Term::Choice { ty } => {
        let mut inst =
          if let Term::Choice { ty: ty2 } = t2 { self.unify_type(ty, ty2) } else { Dnf::FALSE };
        for &m in &self.eq_class[self.get_eq_class(t2).unwrap()].terms[CTK::Choice] {
          let Term::Choice { ty: ty2 } = &self.lc.marks[m].0 else { unreachable!() };
          inst.mk_or(self.unify_type(ty, ty2))
        }
        inst
      }
      &Term::EqClass(n) => Dnf::mk_bool(self.get_eq_class(t2) == Some(n)),
      Term::Numeral(_) | Term::Constant(_) | Term::Infer(_) =>
        Dnf::mk_bool(self.get_eq_class(t1).unwrap() == self.get_eq_class(t2).unwrap()),
      Term::Locus(_)
      | Term::EqMark(_)
      | Term::PrivFunc { .. }
      | Term::LambdaVar(_)
      | Term::Qua { .. }
      | Term::It => unreachable!(),
      _ => Dnf::FALSE,
    }
  }

  /// InstCollection.UNITrmList
  fn unify_terms(&mut self, tms1: &[Term], tms2: &[Term]) -> Dnf<FVarId, EqClassId> {
    assert!(tms1.len() == tms2.len());
    let mut res = Dnf::True;
    for (t1, t2) in tms1.iter().zip(tms2) {
      res.mk_and(self.unify_term(t1, t2));
      if res.is_false() {
        break
      }
    }
    res
  }

  /// InstCollection.UNIFrm
  fn unify_formula(&mut self, f1: &Formula, f2: &Formula) -> Dnf<FVarId, EqClassId> {
    match (f1, f2) {
      (Formula::True, Formula::True) => Dnf::True,
      (Formula::Neg { f: f1 }, Formula::Neg { f: f2 }) => self.unify_formula(f1, f2),
      (Formula::And { args: args1 }, Formula::And { args: args2 })
        if args1.len() == args2.len() =>
      {
        let mut res = Dnf::True;
        args1.iter().zip(args2).for_each(|(f1, f2)| res.mk_and(self.unify_formula(f1, f2)));
        res
      }
      (Formula::Pred { nr: n1, args: args1 }, Formula::Pred { nr: n2, args: args2 }) => {
        let (n1, args1) = Formula::adjust_pred(*n1, args1, &self.g.constrs);
        let (n2, args2) = Formula::adjust_pred(*n2, args2, &self.g.constrs);
        if n1 != n2 {
          return Dnf::FALSE
        }
        let mut inst = self.unify_terms(args1, args2);
        let c = &self.g.constrs.predicate[n1];
        if c.properties.get(PropertyKind::Symmetry) {
          let mut args1 = args1.to_vec();
          args1.swap(c.arg1 as usize, c.arg2 as usize);
          inst.mk_or(self.unify_terms(&args1[c.superfluous as usize..], args2));
        }
        let c = &self.g.constrs.predicate[n2];
        if c.properties.get(PropertyKind::Symmetry) {
          let mut args2 = args2.to_vec();
          args2.swap(c.arg1 as usize, c.arg2 as usize);
          inst.mk_or(self.unify_terms(args1, &args2[c.superfluous as usize..]));
        }
        inst
      }
      (
        Formula::SchPred { nr: SchPredId(n1), args: args1 },
        Formula::SchPred { nr: SchPredId(n2), args: args2 },
      )
      | (
        Formula::PrivPred { nr: PrivPredId(n1), args: args1, .. },
        Formula::PrivPred { nr: PrivPredId(n2), args: args2, .. },
      ) if n1 == n2 => self.unify_terms(args1, args2),
      (Formula::Attr { nr: n1, args: args1 }, Formula::Attr { nr: n2, args: args2 }) => {
        let (n1, args1) = Formula::adjust_attr(*n1, args1, &self.g.constrs);
        let (n2, args2) = Formula::adjust_attr(*n2, args2, &self.g.constrs);
        if n1 == n2 {
          self.unify_terms(args1, args2)
        } else {
          Dnf::FALSE
        }
      }
      (Formula::ForAll { dom: dom1, scope: sc1 }, Formula::ForAll { dom: dom2, scope: sc2 }) => {
        let mut inst = self.unify_type(dom1, dom2);
        self.depth += 1;
        inst.mk_and(self.unify_formula(sc1, sc2));
        self.depth -= 1;
        inst
      }
      (Formula::Is { term: tm1, ty: ty1 }, Formula::Is { term: tm2, ty: ty2 }) => {
        let mut inst = self.unify_term(tm1, tm2);
        if !inst.is_false() {
          inst.mk_and(self.unify_type(ty1, ty2))
        }
        inst
      }
      (Formula::FlexAnd { orig: orig1, .. }, Formula::FlexAnd { orig: orig2, .. }) => {
        let mut inst = self.unify_formula(&orig1[0], &orig2[0]);
        if !inst.is_false() {
          inst.mk_and(self.unify_formula(&orig1[1], &orig2[1]));
        }
        inst
      }
      _ => Dnf::FALSE,
    }
  }
}

#[derive(Default)]
struct FVarCtx {
  types: Vec<Type>,
  cache: BTreeMap<(FVarId, EqClassId), Dnf<FVarId, EqClassId>>,
}

struct EquateClass<'a> {
  infer: &'a HashMap<InferId, EqClassId>,
  eq_class: &'a IdxVec<EqClassId, EqTerm>,
}

impl Unify<'_> {
  fn equate_class(&self) -> EquateClass<'_> {
    EquateClass { infer: self.infer, eq_class: self.eq_class }
  }
}

impl EquateClass<'_> {
  /// EqClassNr
  fn get(&mut self, g: &Global, lc: &LocalContext, tm: &Term) -> Option<EqClassId> {
    macro_rules! func_like {
      ($tk:ident { $nr:expr, $args:expr }) => {{
        let ecs = $args.iter().map(|t| self.get(g, lc, t)).collect::<Option<Vec<_>>>()?;
        for (ec, etm) in self.eq_class.enum_iter() {
          for &m in &etm.terms[CTK::$tk] {
            let Term::$tk { nr, ref args, .. } = lc.marks[m].0 else { unreachable!() };
            if $nr == nr && args.iter().zip(&ecs).all(|(arg, &ec2)| arg.class().unwrap() == ec2) {
              return Some(ec)
            }
          }
        }
        None
      }};
    }
    match *tm {
      Term::EqClass(ec) => Some(ec),
      Term::Numeral(i) => {
        (self.eq_class.enum_iter())
          .find(|(ec, etm)| {
            // TODO: numeric_value
            false
          })
          .map(|p| p.0)
      }
      Term::Infer(n) => self.infer.get(&n).copied(),
      Term::Functor { nr, ref args } => {
        let ecs = args.iter().map(|t| self.get(g, lc, t)).collect::<Option<Vec<_>>>()?;
        for (ec, etm) in self.eq_class.enum_iter() {
          for &m in &etm.terms[CTK::Functor] {
            let Term::Functor { nr: nr2, args: ref args2 } = lc.marks[m].0
            else { unreachable!() };
            let it = if nr == nr2 {
              args2.iter().zip(&*ecs)
            } else {
              let (nr, adj) = Term::adjust(nr, args, &g.constrs);
              let (nr2, adj2) = Term::adjust(nr2, args2, &g.constrs);
              if nr != nr2 {
                continue
              }
              adj2.iter().zip(&ecs[args.len() - adj.len()..])
            };
            if { it }.all(|(arg, &ec2)| arg.class().unwrap() == ec2) {
              return Some(ec)
            }
          }
        }
        None
      }
      Term::Aggregate { nr, ref args } => func_like!(Aggregate { nr, args }),
      Term::SchFunc { nr, ref args } => func_like!(SchFunc { nr, args }),
      Term::PrivFunc { nr, ref args, .. } => func_like!(PrivFunc { nr, args }),
      Term::Selector { nr, ref args } => func_like!(Selector { nr, args }),
      Term::Locus(_) | Term::Bound(_) => None,
      Term::Fraenkel { .. } => (self.eq_class.enum_iter())
        .find(|p| p.1.terms[CTK::Fraenkel].iter().any(|&m| self.eq_term(g, lc, tm, &lc.marks[m].0)))
        .map(|p| p.0),
      Term::Choice { ref ty } => (self.eq_class.enum_iter())
        .find(|p| p.1.terms[CTK::Choice].iter().any(|&m| self.eq_term(g, lc, tm, &lc.marks[m].0)))
        .map(|p| p.0),
      Term::Constant(_)
      | Term::EqMark(_)
      | Term::FreeVar(_)
      | Term::LambdaVar(_)
      | Term::Qua { .. }
      | Term::It => unreachable!(),
    }
  }
}

impl Equate for EquateClass<'_> {
  fn eq_class_right(&mut self, g: &Global, lc: &LocalContext, t1: &Term, ec: EqClassId) -> bool {
    self.get(g, lc, t1) == Some(ec)
  }

  fn eq_pred(
    &mut self, g: &Global, lc: &LocalContext, n1: PredId, n2: PredId, args1: &[Term],
    args2: &[Term],
  ) -> bool {
    if n1 != n2 {
      return false
    }
    if self.eq_terms(g, lc, args1, args2) {
      return true
    }
    let c = &g.constrs.predicate[n1];
    if c.properties.get(PropertyKind::Symmetry) {
      let mut args1 = args1.iter().collect_vec();
      args1.swap(c.arg1 as usize, c.arg2 as usize);
      args1[c.superfluous as usize..].iter().zip(args2).all(|(t1, t2)| self.eq_term(g, lc, t1, t2))
    } else {
      let c = &g.constrs.predicate[n2];
      c.properties.get(PropertyKind::Symmetry) && {
        let mut args2 = args2.iter().collect_vec();
        args2.swap(c.arg1 as usize, c.arg2 as usize);
        (args1.iter().zip(&args2[c.superfluous as usize..]))
          .all(|(t1, t2)| self.eq_term(g, lc, t1, t2))
      }
    }
  }
}
