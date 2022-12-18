use crate::checker::OrUnsat;
use crate::equate::{Equalizer, EqualizerResult};
use crate::types::*;
use crate::{Global, LocalContext};
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
  pub fn new(eq: Equalizer<'a>) -> Self {
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

  /// Verify
  fn verify(&self, f: &Formula) -> OrUnsat<()> {
    //
    Ok(())
  }

  /// Unifiable
  fn unify_one(&mut self, fs: &[&Formula]) -> OrUnsat<()> {
    //
    Ok(())
  }

  /// Unification
  pub fn unify(&mut self, res: EqualizerResult) -> OrUnsat<()> {
    let univ =
      res.pos_bas.0 .0.iter().filter(|f| matches!(f, Formula::ForAll { .. })).collect_vec();
    for &f in &univ {
      self.verify(f)?;
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
    for (neg, bas) in [(false, &res.pos_bas), (true, &res.neg_bas)] {
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
              self.verify(&f)?;
            }
          }
        }
      }
    }
    Ok(())
  }
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
