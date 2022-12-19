use crate::checker::{Atoms, Dnf, Open, OrUnsat, Unsat};
use crate::equate::{Equalizer, EqualizerResult};
use crate::types::*;
use crate::{vprintln, CheckLocus, ExpandPrivFunc, Global, LocalContext, Visit, VisitMut};
use enum_map::{Enum, EnumMap};
use itertools::Itertools;
use std::collections::HashMap;

const ENABLE_UNIFIER: bool = true;

pub struct Unifier<'a> {
  g: &'a Global,
  lc: &'a mut LocalContext,
  infer: HashMap<InferId, EqClassId>,
  terms: EnumMap<ComplexTermKind, IdxVec<EqClassId, Vec<EqMarkId>>>,
  ty_class: IdxVec<EqClassId, Vec<Type>>,
  supercluster: IdxVec<EqClassId, Attrs>,
  eterm: IdxVec<EqClassId, EqClassId>,
  res: &'a EqualizerResult,
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
  pub fn new(eq: Equalizer<'a>, res: &'a EqualizerResult) -> Self {
    let mut u = Self {
      g: eq.g,
      lc: eq.lc,
      infer: Default::default(),
      terms: EnumMap::from_array(std::array::from_fn(|_| {
        IdxVec::from_default(eq.next_eq_class.into_usize())
      })),
      ty_class: IdxVec::from_default(eq.next_eq_class.into_usize()),
      supercluster: IdxVec::from_default(eq.next_eq_class.into_usize()),
      eterm: Default::default(),
      res,
    };
    for etm in eq.terms.0 {
      if !etm.eq_class.is_empty() {
        for m in etm.eq_class {
          let t = &u.lc.marks[m].0;
          match t.complex_kind() {
            Some(k) => u.terms[k][etm.id].push(m),
            None => match *t {
              Term::Infer(i) => drop(u.infer.insert(i, etm.id)),
              Term::Numeral(_) => {}
              _ => unreachable!(),
            },
          }
        }
        // TODO: numeric_value
        u.ty_class[etm.id] = etm.ty_class;
        u.supercluster[etm.id] = etm.supercluster;
      }
    }
    for i in 0..eq.next_eq_class.0 {
      u.eterm.0.push(EqClassId(i))
    }
    u
  }

  /// Verify: Attempts to prove f |- false
  fn falsify(&mut self, mut f: Formula) -> OrUnsat<()> {
    Standardize { g: self.g, lc: self.lc }.visit_formula(&mut f, 0);
    if crate::UNIFY_HEADER {
      eprintln!("verifying: {f:?}");
    }
    let mut free_vars = vec![];
    // Suppose f = ∀ xs, F(xs).
    // First, introduce metavariables ("free vars") to obtain a formula F(?v)
    OpenAsFreeVar { u: self, free_vars: &mut free_vars }.open_quantifiers(&mut f, false);

    // want to show: ∃ ?v. |- !F(?v)
    // Normalize !F(?v) into DNF: ∃ ?v. |- C_1(?v) \/ ... \/ C_n(?v)
    // If we get !F(?v) = true then we are done.
    let mut atoms = Atoms::default();
    let Dnf::Or(clauses) = atoms.normalize(self.g, self.lc, f, false) else { return Err(Unsat) };

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
        match self.compute_inst(&atoms.0[a], !val) {
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
      if !matches!(Dnf::and_many(insts), Dnf::Or(conjs) if conjs.is_empty()) {
        return Err(Unsat)
      }
    }
    // falsification failed
    Ok(())
  }

  /// Constructs an instantiation P(?v) such that
  /// * pos = true: COMPInstAsTrue - P(?v) /\ F(?v) |- false
  /// * pos = false: COMPInstAsFalse - P(?v) /\ !F(?v) |- false
  fn compute_inst(&mut self, f: &Formula, pos: bool) -> Dnf<u32, u32> {
    //
    Dnf::True
  }

  /// Unifiable
  fn unify_one(&mut self, fs: &[&Formula]) -> OrUnsat<()> {
    //
    Ok(())
  }

  /// Unification
  pub fn unify(&mut self) -> OrUnsat<()> {
    let univ =
      self.res.pos_bas.0 .0.iter().filter(|f| matches!(f, Formula::ForAll { .. })).collect_vec();
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
    for (neg, bas) in [(false, &self.res.pos_bas), (true, &self.res.neg_bas)] {
      for f in &bas.0 .0 {
        if let Formula::Pred { nr, args } = f {
          let (nr, args) = Formula::adjust_pred(*nr, args, &self.g.constrs);
          if self.g.reqs.belongs_to() == Some(nr) {
            for &m in &self.terms[CTK::Fraenkel][args[1].unmark(self.lc).class().unwrap()] {
              if let Term::Fraenkel { args: tys, scope, compr } = &self.lc.marks[m].0 {
                let (tys, scope, compr) = (tys.clone(), (**scope).clone(), (**compr).clone());
                let mut fm = args[0].clone().not_in_fraenkel(tys, scope, compr, &self.g.reqs);
                fm.distribute_quantifiers(&self.g.constrs, 0);
                fraenkel_fmlas.push(fm.maybe_neg(neg))
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

struct OpenAsFreeVar<'a, 'b> {
  u: &'b mut Unifier<'a>,
  free_vars: &'b mut Vec<Type>,
}

impl Open for OpenAsFreeVar<'_, '_> {
  fn mk_var(n: u32) -> Term { Term::FreeVar(FVarId(n)) }
  fn base(&self) -> u32 { self.free_vars.len() as u32 }
  fn new_var(&mut self, mut ty: Type) { self.free_vars.push(ty); }
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
