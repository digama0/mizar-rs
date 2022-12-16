use crate::equate::Equalizer;
use crate::retain_mut_from::RetainMutFrom;
use crate::types::*;
use crate::verify::Verifier;
use crate::{
  inst, set_verbose, vprintln, Equate, ExpandPrivFunc, FixedVar, Global, InternConst, LocalContext,
  OnVarMut, Subst, VisitMut,
};
use itertools::EitherOrBoth;
use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::marker::PhantomData;
use std::ops::ControlFlow;

pub struct Checker<'a> {
  pub g: &'a mut Global,
  pub lc: &'a mut LocalContext,
  pub expansions: &'a [Definiens],
  pub equals: &'a BTreeMap<ConstrKind, Vec<EqualsDef>>,
  pub identify: &'a [Identify],
  pub func_ids: &'a BTreeMap<ConstrKind, Vec<usize>>,
  pub reductions: &'a [Reduction],
  pub idx: usize,
  pub pos: Position,
}

impl<'a> Checker<'a> {
  fn as_mut(&mut self) -> Checker<'_> {
    Checker {
      g: self.g,
      lc: self.lc,
      expansions: self.expansions,
      equals: self.equals,
      identify: self.identify,
      func_ids: self.func_ids,
      reductions: self.reductions,
      idx: self.idx,
      pos: self.pos,
    }
  }

  fn intern_const(&self) -> InternConst<'_> {
    InternConst::new(self.g, self.lc, self.equals, self.identify, self.func_ids)
  }

  pub fn justify(&mut self, premises: Vec<&'a Formula>) {
    // set_verbose(self.idx >= 69);
    self.lc.term_cache.get_mut().open_scope();
    let infer_const = self.lc.infer_const.borrow().len();
    let fixed_var = self.lc.fixed_var.len();

    // eprintln!();
    let mut conjs = vec![];
    for f in premises {
      // eprintln!("input: {f:?}");
      let mut f = f.clone();
      Expand { g: self.g, lc: self.lc, expansions: self.expansions }.expand(&mut f, true);
      f.distribute_quantifiers(&self.g.constrs, 0);
      // eprintln!("distributed: {f:?}");
      f.append_conjuncts_to(&mut conjs);
    }
    let mut check_f = Formula::mk_and(conjs);
    // eprintln!("checking {} @ {:?}:\n  {check_f:?}", self.idx, self.pos);

    self.open_quantifiers::<ConstId>(&mut check_f, true);
    // eprintln!("opened {} @ {:?}:\n  {check_f:?}", self.idx, self.pos);

    check_f.visit(&mut self.intern_const());
    // eprintln!("interned {} @ {:?}:\n  {check_f:?}", self.idx, self.pos);

    let mut atoms = Atoms::default();
    let Dnf::Or(normal_form) = atoms.normalize(self.g, self.lc, check_f, true)
    else { panic!("it is not true") };
    // for (i, a) in atoms.0.enum_iter() {
    //   vprintln!("atom {i:?}: {a:?}");
    // }
    self.g.recursive_round_up = true;
    for f in normal_form {
      // vprintln!("falsifying: {f:?}");
      let sat = (|| {
        Equalizer::new(self).equate(&atoms, f)?;
        self.pre_unification()?;
        let unifier = self.unifier();
        unifier.unify(self)
      })();
      assert!(sat.is_err(), "failed to justify");
    }
    self.g.recursive_round_up = false;
    self.lc.fixed_var.0.truncate(fixed_var);
    self.lc.infer_const.get_mut().truncate(infer_const);
    self.lc.term_cache.get_mut().close_scope();
  }

  fn pre_unification(&self) -> OrUnsat<()> { Ok(()) }

  fn unifier(&self) -> Unifier { Unifier {} }
}

#[derive(Copy, Clone, Debug)]
pub struct Unsat;
pub type OrUnsat<T> = Result<T, Unsat>;

struct Expand<'a> {
  g: &'a Global,
  lc: &'a mut LocalContext,
  expansions: &'a [Definiens],
}

impl Expand<'_> {
  fn expand(&mut self, f: &mut Formula, pos: bool) {
    match f {
      Formula::Neg { f: arg } => self.expand(arg, !pos),
      Formula::And { args } => {
        let mut new_args = vec![];
        for mut f in std::mem::take(args) {
          self.expand(&mut f, pos);
          f.append_conjuncts_to(&mut new_args);
        }
        *f = Formula::mk_and(new_args)
      }
      Formula::ForAll { dom, scope } if !pos => {
        self.lc.bound_var.push((**dom).clone());
        self.expand(scope, pos);
        self.lc.bound_var.0.pop().unwrap();
      }
      Formula::Pred { nr, args } => {
        let c = &self.g.constrs.predicate[*nr];
        if let Some(nr2) = c.redefines {
          *nr = nr2;
          *args = args[c.superfluous as usize..].to_vec().into()
        }
        let expansions = self.well_matched_expansions(ConstrKind::Pred(*nr), args);
        f.conjdisj_many(pos, expansions);
      }
      Formula::Attr { nr, args } => {
        let c = &self.g.constrs.attribute[*nr];
        if let Some(nr2) = c.redefines {
          *nr = nr2;
          *args = args[c.superfluous as usize..].to_vec().into()
        }
        let expansions = self.well_matched_expansions(ConstrKind::Attr(*nr), args);
        f.conjdisj_many(pos, expansions);
      }
      Formula::FlexAnd { orig, terms, expansion } =>
        if self.lc.bound_var.is_empty() {
          let mut epf = ExpandPrivFunc { ctx: &self.g.constrs };
          let depth = self.lc.bound_var.len() as u32;
          let mut f1 = Formula::FlexAnd {
            orig: orig.clone(),
            terms: terms.clone(),
            expansion: expansion.clone(),
          };
          epf.visit_formula(&mut f1, depth);
          let f2 = {
            let Formula::FlexAnd { orig, terms, expansion } = &f1 else { unreachable!() };
            (**expansion).clone()
          };
          let mut conjs = vec![f1.maybe_neg(pos)];
          f2.maybe_neg(pos).append_conjuncts_to(&mut conjs);
          self.expand_flex(terms, expansion, &mut conjs, pos);
          *f = Formula::mk_and(conjs).maybe_neg(pos)
        },
      Formula::SchPred { .. }
      | Formula::PrivPred { .. }
      | Formula::Is { .. }
      | Formula::ForAll { .. }
      | Formula::True
      | Formula::Thesis => {}
    }
  }

  /// ExpandFlex
  fn expand_flex(
    &mut self, terms: &mut Box<[Term; 2]>, expansion: &Formula, conjs: &mut Vec<Formula>, pos: bool,
  ) {
    assert!(self.lc.bound_var.is_empty());
    let mut zero = None;
    let left = match &terms[0] {
      Term::Functor { nr, args }
        if Some(Term::adjust(*nr, args, &self.g.constrs).0) == self.g.reqs.zero_number() =>
      {
        zero = Some(terms[0].clone());
        0
      }
      Term::Numeral(nr) => *nr,
      _ => return,
    };
    let Term::Numeral(right) = terms[1] else { return };
    if right.saturating_sub(left) <= 100 {
      let Formula::ForAll { scope, .. } = expansion else { unreachable!() };
      let Formula::Neg { f } = &**scope else { unreachable!() };
      let Formula::And { args } = &**f else { unreachable!() };
      // FIXME: this could be wrong if the scope expression is an And,
      // but mizar already segfaults on (0 = 0 & 0 = 0) & ... & (1 = 1 & 1 = 1);
      let scope = &args[2];
      for i in left..=right {
        struct Inst0(Term);
        impl VisitMut for Inst0 {
          /// ReplacePlaceHolderByConjunctNumber
          fn visit_term(&mut self, tm: &mut Term, depth: u32) {
            match tm {
              Term::Bound(BoundId(0)) => *tm = self.0.clone(),
              Term::Bound(nr) => nr.0 -= 1,
              _ => self.super_visit_term(tm, depth),
            }
          }
        }
        let mut inst = Inst0(if i == 0 { zero.clone().unwrap() } else { Term::Numeral(i) });
        let mut tm = scope.clone();
        inst.visit_formula(&mut tm, 0);
        tm.maybe_neg(!pos).append_conjuncts_to(conjs);
      }
    }
  }

  fn well_matched_expansions(&self, kind: ConstrKind, args: &[Term]) -> Vec<Formula> {
    let mut expansions = vec![];
    for exp in self.expansions.iter().rev() {
      let Formula::True = exp.assumptions else { continue };
      let DefValue::Formula(body) = &exp.value else { continue };
      let [] = *body.cases else { continue };
      let Some(subst) = exp.matches(self.g, self.lc, kind, args) else { continue };
      let base = self.lc.bound_var.len() as u32;
      let mut result = body.otherwise.as_ref().expect("no cases and no otherwise?").clone();
      OnVarMut(|nr, _| *nr += base).visit_formula(&mut result, 0);
      subst.inst_formula_mut(&mut result, base);
      expansions.push(result)
    }
    expansions
  }
}

impl Formula {
  fn distribute_quantifiers(&mut self, ctx: &Constructors, depth: u32) {
    loop {
      match self {
        Formula::Neg { f: arg } => {
          arg.distribute_quantifiers(ctx, depth);
          *self = std::mem::take(arg).mk_neg();
        }
        Formula::And { args } => {
          let mut conjs = vec![];
          for mut f in std::mem::take(args) {
            f.distribute_quantifiers(ctx, depth);
            f.append_conjuncts_to(&mut conjs)
          }
          *self = Formula::mk_and(conjs)
        }
        Formula::ForAll { dom, scope, .. } => {
          ExpandPrivFunc { ctx }.visit_type(dom, depth);
          scope.distribute_quantifiers(ctx, depth + 1);
          if let Formula::And { args } = &mut **scope {
            for f in args {
              let mut nontrivial = false;
              f.visit(&mut OnVarMut(|nr, _| nontrivial |= *nr == depth));
              if nontrivial {
                *f = Formula::ForAll { dom: dom.clone(), scope: Box::new(std::mem::take(f)) }
              } else {
                f.visit(&mut OnVarMut(|nr, _| {
                  if *nr > depth {
                    *nr -= 1
                  }
                }))
              }
            }
            *self = std::mem::take(scope);
          }
        }
        Formula::PrivPred { args, value, .. } => {
          *self = std::mem::take(value);
          continue
        }
        Formula::SchPred { .. }
        | Formula::Pred { .. }
        | Formula::Attr { .. }
        | Formula::Is { .. }
        | Formula::FlexAnd { .. }
        | Formula::True
        | Formula::Thesis => ExpandPrivFunc { ctx }.visit_formula(self, depth),
      }
      break
    }
  }
}

trait VarKind: Idx {
  fn mk_var(n: u32) -> Term;
  fn base(lc: &LocalContext) -> u32;
  fn push_var(lc: &mut LocalContext, ty: Type);
}

impl VarKind for ConstId {
  fn mk_var(n: u32) -> Term { Term::Constant(ConstId(n)) }
  fn base(lc: &LocalContext) -> u32 { lc.fixed_var.len() as u32 }
  fn push_var(lc: &mut LocalContext, ty: Type) { lc.fixed_var.push(FixedVar { ty, def: None }); }
}
// impl VarKind for FVarId {
//   fn mk_var(n: u32) -> Term { Term::FreeVar { nr: FVarId(n) } }
//   fn base(lc: &LocalContext) -> u32 { lc.free_var.len() as u32 }
//   fn push_var(lc: &mut LocalContext, ty: Box<Type>) {
//     lc.free_var.push(FixedVar { ty, def: None });
//   }
// }

struct SetVar<V> {
  depth: u32,
  base: u32,
  var: PhantomData<V>,
}

impl<V: VarKind> SetVar<V> {
  fn new(lc: &LocalContext, depth: u32) -> SetVar<V> {
    SetVar { depth, base: V::base(lc), var: PhantomData }
  }
}

impl<V: VarKind> VisitMut for SetVar<V> {
  fn visit_term(&mut self, tm: &mut Term, depth: u32) {
    match tm {
      Term::Bound(nr) =>
        if nr.0 >= self.depth {
          nr.0 -= self.depth
        } else {
          *tm = V::mk_var(self.base + nr.0)
        },
      _ => self.super_visit_term(tm, depth),
    }
  }
}

impl<'a> Checker<'a> {
  fn new_var<V: VarKind>(&mut self, mut ty: Type) {
    ty.visit(&mut self.intern_const());
    V::push_var(self.lc, ty)
  }

  /// * pos = true: RemoveIntQuantifier
  /// * pos = false: RemoveExtQuantifier
  fn open_quantifiers<V: VarKind>(&mut self, fmla: &mut Formula, pos: bool) {
    loop {
      match fmla {
        Formula::Neg { f } => {
          self.open_quantifiers::<V>(f, !pos);
          if let Formula::Neg { f } = &mut **f {
            *fmla = std::mem::take(f);
          }
        }
        Formula::And { args } => {
          let mut conjs = vec![];
          for mut f in std::mem::take(args) {
            self.open_quantifiers::<V>(&mut f, pos);
            f.append_conjuncts_to(&mut conjs)
          }
          *fmla = Formula::mk_and(conjs)
        }
        Formula::ForAll { dom, scope } =>
          if !pos {
            let mut set_var = SetVar::<V>::new(self.lc, 1);
            self.new_var::<V>(std::mem::take(&mut **dom));
            let mut f = std::mem::take(scope);
            while let Formula::ForAll { mut dom, scope } = *f {
              set_var.visit_type(&mut dom, set_var.depth);
              self.new_var::<V>(*dom);
              set_var.depth += 1;
              f = scope
            }
            set_var.visit_formula(&mut f, set_var.depth);
            *fmla = *f;
            continue
          },
        Formula::SchPred { .. }
        | Formula::Pred { .. }
        | Formula::Attr { .. }
        | Formula::PrivPred { .. }
        | Formula::Is { .. }
        | Formula::FlexAnd { .. }
        | Formula::True
        | Formula::Thesis => {}
      }
      return
    }
  }
}

#[derive(Default)]
pub struct Atoms(pub IdxVec<AtomId, Formula>);

impl Atoms {
  pub fn find(&self, g: &Global, lc: &LocalContext, f: &Formula) -> Option<AtomId> {
    self.0.enum_iter().find(|(_, atom)| ().eq_formula(g, lc, f, atom)).map(|p| p.0)
  }

  pub fn insert(&mut self, g: &Global, lc: &LocalContext, f: Cow<'_, Formula>) -> AtomId {
    match self.find(g, lc, &f) {
      Some(i) => i,
      None => self.0.push(f.into_owned()),
    }
  }
}

/// A conjunction is a map from atoms to true or false, so
/// `{a: true, b: false, c: true}` represents `a /\ ~b /\ c`.
/// Invariant: the map is not empty when in a `DNF`.
#[derive(Clone, Default)]
pub struct Conjunct<K, V>(pub BTreeMap<K, V>);

impl<K: std::fmt::Debug> std::fmt::Debug for Conjunct<K, bool> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut it = self.0.iter();
    if let Some((a, &b)) = it.next() {
      if b {
        write!(f, "{}a{:?}", if b { "" } else { "¬" }, a)?;
      }
      for (a, &b) in it {
        write!(f, " ∧ {}a{:?}", if b { "" } else { "¬" }, a)?;
      }
      Ok(())
    } else {
      write!(f, "false")
    }
  }
}

impl<K: Ord + Clone, V: PartialEq + Clone> Conjunct<K, V> {
  /// InitSingle
  pub fn single(k: K, v: V) -> Self { Self(std::iter::once((k, v)).collect()) }

  /// NatFunc.WeakerThan
  /// True if every atom in other is present in self with the same polarity.
  fn weaker_than(&self, other: &Self) -> bool {
    self.0.len() <= other.0.len()
      && self.0.iter().all(|(a, val2)| other.0.get(a).map_or(false, |val1| val1 == val2))
  }

  /// NatFunc.JoinAtom
  /// If it returns Err, then the conjunction is unsatisfiable
  /// and `self` is left in indeterminate state.
  fn mk_and(&mut self, other: &Self) -> Result<(), ()> {
    for (k, v) in &other.0 {
      if let Some(v1) = self.0.insert(k.clone(), v.clone()) {
        if v1 != *v {
          return Err(())
        }
      }
    }
    Ok(())
  }
}

pub enum Dnf<K, V> {
  /// The constant true is represented specially, although we could use `Or([[]])`
  /// to represent it (that is, the singleton of the empty map).
  True,
  /// A collection of conjunctions connected by OR.
  Or(Vec<Conjunct<K, V>>),
}

impl<K: Ord + Clone, V: PartialEq + Clone> Dnf<K, V> {
  pub const FALSE: Dnf<K, V> = Dnf::Or(vec![]);

  /// * pos = true: PreInstCollection.InitTop
  /// * pos = false: PreInstCollection.InitBottom
  pub fn mk_bool(pos: bool) -> Self {
    if pos {
      Self::True
    } else {
      Self::FALSE
    }
  }

  pub fn insert_and_absorb(this: &mut Vec<Conjunct<K, V>>, conj: Conjunct<K, V>) {
    for (i, conj1) in this.iter_mut().enumerate() {
      if conj.weaker_than(conj1) {
        return
      }
      if conj1.weaker_than(&conj) {
        this.retain_mut_from(i + 1, |conj2| !conj2.weaker_than(&conj));
        this[i] = conj;
        return
      }
    }
  }

  /// PreInstCollection.JoinWith
  pub fn mk_and(&mut self, other: Self) {
    let Dnf::Or(this) = self else { *self = other; return };
    let Dnf::Or(other) = other else { return };
    other.into_iter().for_each(|disj| Self::insert_and_absorb(this, disj));
  }

  /// PreInstCollection.UnionWith
  pub fn mk_or(&mut self, other: &Self) {
    let Dnf::Or(this) = self else { return };
    let Dnf::Or(other) = other else { *self = Dnf::True; return };
    if let [conj2] = &**other {
      this.retain_mut(|conj1| conj1.mk_and(conj2).is_ok());
    } else {
      // TODO: instantiation limit
      for conj1 in std::mem::take(this) {
        for conj2 in other {
          let mut conj = conj1.clone();
          if let Ok(()) = conj.mk_and(conj2) {
            this.push(conj);
          }
        }
      }
    }
  }
}

impl Atoms {
  fn normalize(
    &mut self, g: &Global, lc: &LocalContext, f: Formula, pos: bool,
  ) -> Dnf<AtomId, bool> {
    match f {
      Formula::Neg { f } => self.normalize(g, lc, *f, !pos),
      Formula::And { args } => {
        let mut res = Dnf::mk_bool(pos);
        if pos {
          args.into_iter().for_each(|f| res.mk_and(self.normalize(g, lc, f, pos)))
        } else {
          args.into_iter().for_each(|f| res.mk_or(&self.normalize(g, lc, f, pos)));
        }
        res
      }
      Formula::True => Dnf::mk_bool(pos),
      _ => {
        let a = self.insert(g, lc, Cow::Owned(f));
        Dnf::Or(vec![Conjunct::single(a, pos)])
      }
    }
  }
}

struct Unifier {}
impl Unifier {
  fn unify(&self, ck: &mut Checker) -> OrUnsat<()> { Err(Unsat) }
}
