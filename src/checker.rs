use crate::equate::Equalizer;
use crate::retain_mut_from::RetainMutFrom;
use crate::types::*;
use crate::unify::Unifier;
use crate::verify::Verifier;
use crate::{
  inst, set_verbose, stat, vprintln, Equate, ExpandPrivFunc, FixedVar, Global, InternConst,
  LocalContext, OnVarMut, Subst, VisitMut,
};
use itertools::{EitherOrBoth, Itertools};
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
    if let Some(n) = crate::FIRST_VERBOSE_CHECKER {
      set_verbose(self.idx >= n);
    }
    self.lc.term_cache.get_mut().open_scope();
    let infer_const = self.lc.infer_const.borrow().len();
    let fixed_var = self.lc.fixed_var.len();

    if crate::CHECKER_INPUTS {
      eprintln!();
    }
    let mut conjs = vec![];
    for f in premises {
      if crate::CHECKER_INPUTS {
        eprintln!("input: {f:?}");
      }
      let mut f = f.clone();
      Expand { g: self.g, lc: self.lc, expansions: self.expansions }.expand(&mut f, true);
      f.distribute_quantifiers(&self.g.constrs, 0);
      // eprintln!("distributed: {f:?}");
      f.append_conjuncts_to(&mut conjs);
    }
    let mut check_f = Formula::mk_and(conjs);
    if crate::CHECKER_HEADER {
      eprintln!("checking {} @ {:?}:\n  {check_f:?}", self.idx, self.pos);
    }

    OpenAsConst(self).open_quantifiers(&mut check_f, true);
    // eprintln!("opened {} @ {:?}:\n  {check_f:?}", self.idx, self.pos);

    check_f.visit(&mut self.intern_const());
    // eprintln!("interned {} @ {:?}:\n  {check_f:?}", self.idx, self.pos);

    let mut atoms = Atoms::default();
    let Dnf::Or(normal_form) = atoms.normalize(self.g, self.lc, check_f, true)
    else { panic!("it is not true") };
    self.g.recursive_round_up = true;
    for f in normal_form {
      if crate::CHECKER_CONJUNCTS {
        eprintln!(
          "falsifying: {:#?}",
          f.0.iter().map(|(&a, &val)| atoms.0[a].clone().maybe_neg(val)).collect_vec()
        );
      }
      let sat = (|| {
        let mut eq = Equalizer::new(self);
        let res = eq.run(&atoms, &f)?;
        Unifier::new(eq, &res).run()
      })();
      // assert!(sat.is_err(), "failed to justify");
      if sat.is_ok() {
        stat("failure");
        if crate::CHECKER_RESULT {
          eprintln!(
            "FAILED TO JUSTIFY {} @ {:?}: {:#?}",
            self.idx,
            self.pos,
            f.0.iter().map(|(&a, &val)| atoms.0[a].clone().maybe_neg(val)).collect_vec()
          );
        }
        if crate::PANIC_ON_FAIL {
          panic!("failed to justify {} @ {:?}", self.idx, self.pos);
        }
      } else {
        stat("success");
        if crate::CHECKER_RESULT {
          eprintln!(
            "proved {} @ {:?}! {:#?}",
            self.idx,
            self.pos,
            f.0.iter().map(|(&a, &val)| atoms.0[a].clone().maybe_neg(val)).collect_vec()
          );
        }
      }
    }
    self.g.recursive_round_up = false;
    self.lc.fixed_var.0.truncate(fixed_var);
    self.lc.infer_const.get_mut().truncate(infer_const);
    self.lc.term_cache.get_mut().close_scope();
  }
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
        let (n2, args2) = Formula::adjust_pred(*nr, args, &self.g.constrs);
        let expansions = self.well_matched_expansions(ConstrKind::Pred(n2), args2);
        f.conjdisj_many(pos, expansions);
      }
      Formula::Attr { nr, args } => {
        let (n2, args2) = Formula::adjust_attr(*nr, args, &self.g.constrs);
        let expansions = self.well_matched_expansions(ConstrKind::Attr(n2), args);
        f.conjdisj_many(pos, expansions);
      }
      Formula::FlexAnd { orig, terms, expansion } =>
        if self.lc.bound_var.is_empty() {
          let mut epf = ExpandPrivFunc(&self.g.constrs);
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
      | Formula::True => {}
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
  pub fn distribute_quantifiers(&mut self, ctx: &Constructors, depth: u32) {
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
          ExpandPrivFunc(ctx).visit_type(dom, depth);
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
        | Formula::True => ExpandPrivFunc(ctx).visit_formula(self, depth),
      }
      break
    }
  }
}

pub trait Open {
  fn mk_var(n: u32) -> Term;
  fn base(&self) -> u32;
  fn new_var(&mut self, ty: Type);

  /// * pos = true: RemoveIntQuantifier
  /// * pos = false: RemoveExtQuantifier
  fn open_quantifiers(&mut self, fmla: &mut Formula, pos: bool) {
    loop {
      match fmla {
        Formula::Neg { f } => {
          self.open_quantifiers(f, !pos);
          if let Formula::Neg { f } = &mut **f {
            *fmla = std::mem::take(f);
          }
        }
        Formula::And { args } => {
          let mut conjs = vec![];
          for mut f in std::mem::take(args) {
            self.open_quantifiers(&mut f, pos);
            f.append_conjuncts_to(&mut conjs)
          }
          *fmla = Formula::mk_and(conjs)
        }
        Formula::ForAll { dom, scope } =>
          if !pos {
            let mut set_var = SetVar::new(self, 1);
            self.new_var(std::mem::take(&mut **dom));
            let mut f = std::mem::take(scope);
            while let Formula::ForAll { mut dom, scope } = *f {
              set_var.visit_type(&mut dom, set_var.depth);
              self.new_var(*dom);
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
        | Formula::True => {}
      }
      return
    }
  }
}

struct OpenAsConst<'a, 'b>(&'b mut Checker<'a>);

impl Open for OpenAsConst<'_, '_> {
  fn mk_var(n: u32) -> Term { Term::Constant(ConstId(n)) }
  fn base(&self) -> u32 { self.0.lc.fixed_var.len() as u32 }
  fn new_var(&mut self, mut ty: Type) {
    ty.visit(&mut self.0.intern_const());
    self.0.lc.fixed_var.push(FixedVar { ty, def: None });
  }
}

struct SetVar<O: ?Sized> {
  depth: u32,
  base: u32,
  open: PhantomData<O>,
}

impl<O: Open + ?Sized> SetVar<O> {
  fn new(open: &O, depth: u32) -> SetVar<O> {
    SetVar { depth, base: open.base(), open: PhantomData }
  }
}

impl<O: Open + ?Sized> VisitMut for SetVar<O> {
  fn visit_term(&mut self, tm: &mut Term, depth: u32) {
    match tm {
      Term::Bound(nr) =>
        if nr.0 >= self.depth {
          nr.0 -= self.depth
        } else {
          *tm = O::mk_var(self.base + nr.0)
        },
      _ => self.super_visit_term(tm, depth),
    }
  }
}

#[derive(Default, Debug)]
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

impl<K, V> Conjunct<K, V> {
  pub const TRUE: Self = Self(BTreeMap::new());
}

impl<K: std::fmt::Debug> std::fmt::Debug for Conjunct<K, bool> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut it = self.0.iter();
    if let Some((a, &b)) = it.next() {
      write!(f, "{}a{:?}", if b { "" } else { "¬" }, a)?;
      for (a, &b) in it {
        write!(f, " ∧ {}a{:?}", if b { "" } else { "¬" }, a)?;
      }
      Ok(())
    } else {
      write!(f, "false")
    }
  }
}
impl<K: std::fmt::Debug, V: Idx> std::fmt::Debug for Conjunct<K, V> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut it = self.0.iter();
    if let Some((a, b)) = it.next() {
      write!(f, "v{:?} := e{:?}", a, b.into_usize())?;
      for (a, &b) in it {
        write!(f, " ∧ v{:?} := e{:?}", a, b.into_usize())?;
      }
      Ok(())
    } else {
      write!(f, "false")
    }
  }
}

impl<K: Ord + Clone, V: PartialEq + Clone> Conjunct<K, V>
where Self: std::fmt::Debug
{
  /// InitSingle
  pub fn single(k: K, v: V) -> Self { Self(std::iter::once((k, v)).collect()) }

  /// NatFunc.WeakerThan
  /// True if every atom in self is present in other with the same polarity.
  fn weaker_than(&self, other: &Self) -> bool {
    self.0.len() <= other.0.len() && self.0.iter().all(|(a, val2)| other.0.get(a) == Some(val2))
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

#[derive(Clone)]
pub enum Dnf<K, V> {
  /// The constant true is represented specially, although we could use `Or([[]])`
  /// to represent it (that is, the singleton of the empty map).
  True,
  /// A collection of conjunctions connected by OR.
  Or(Vec<Conjunct<K, V>>),
}

// We can handle a few orders of magnitude more than this before
// things really start to chug, but Mizar has this as a hard limit
// so if we go past it using MML inputs then something must have gone wrong
const MAX_DISJUNCTS: usize = 6000;

impl<K, V> std::fmt::Debug for Dnf<K, V>
where Conjunct<K, V>: std::fmt::Debug
{
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::True => write!(f, "True"),
      Self::Or(arg0) => f.debug_tuple("Or").field(arg0).finish(),
    }
  }
}

impl<K: Ord + Clone, V: PartialEq + Clone> Dnf<K, V>
where Conjunct<K, V>: std::fmt::Debug
{
  pub const FALSE: Dnf<K, V> = Dnf::Or(vec![]);

  pub fn is_false(&self) -> bool { matches!(self, Dnf::Or(conjs) if conjs.is_empty()) }

  /// * pos = true: PreInstCollection.InitTop
  /// * pos = false: PreInstCollection.InitBottom
  pub fn mk_bool(pos: bool) -> Self {
    if pos {
      Self::True
    } else {
      Self::FALSE
    }
  }

  #[inline]
  pub fn single(conj: Conjunct<K, V>) -> Self { Self::Or(vec![conj]) }

  /// PreInstCollection.InsertAndAbsorb
  pub fn insert_and_absorb(this: &mut Vec<Conjunct<K, V>>, conj: Conjunct<K, V>) {
    for (i, conj1) in this.iter_mut().enumerate() {
      if conj1.weaker_than(&conj) {
        return
      }
      if conj.weaker_than(conj1) {
        this.retain_mut_from(i + 1, |conj2| !conj.weaker_than(conj2));
        this[i] = conj;
        return
      }
    }
    this.push(conj)
  }

  /// PreInstCollection.UnionWith
  pub fn mk_or(&mut self, other: Self) {
    let Dnf::Or(this) = self else { return };
    let Dnf::Or(other) = other else { *self = Dnf::True; return };
    other.into_iter().for_each(|conj| Self::insert_and_absorb(this, conj));
  }

  /// PreInstCollection.UnionWith
  #[inline]
  pub fn mk_or_else(&mut self, other: impl FnOnce() -> Self) {
    if matches!(self, Dnf::Or(_)) {
      self.mk_or(other())
    }
  }

  pub fn mk_and_single(&mut self, k: K, v: V) {
    match self {
      Dnf::True => *self = Dnf::single(Conjunct::single(k, v)),
      Dnf::Or(conjs) => conjs.iter_mut().for_each(|conj| {
        conj.0.insert(k.clone(), v.clone());
      }),
    }
  }

  fn mk_and_core(this: &mut Vec<Conjunct<K, V>>, other: Vec<Conjunct<K, V>>) {
    if let [conj2] = &*other {
      this.retain_mut(|conj1| conj1.mk_and(conj2).is_ok())
    } else {
      for conj1 in std::mem::take(this) {
        for conj2 in &other {
          let mut conj = conj1.clone();
          if let Ok(()) = conj.mk_and(conj2) {
            Self::insert_and_absorb(this, conj);
            assert!(this.len() <= MAX_DISJUNCTS);
          }
        }
      }
    }
  }

  /// PreInstCollection.JoinWith
  pub fn mk_and(&mut self, other: Self) {
    match self {
      Dnf::True => *self = other,
      Dnf::Or(this) => match other {
        Dnf::True => {}
        _ if this.is_empty() => {}
        Dnf::Or(other) if other.is_empty() => this.clear(),
        Dnf::Or(other) => Self::mk_and_core(this, other),
      },
    }
  }

  pub fn mk_and_then(&mut self, other: impl FnOnce() -> Self) {
    if !self.is_false() {
      self.mk_and(other())
    }
  }

  /// PreInstCollection.JoinInstList
  /// Constructs the AND of a set of (nontrivial) DNF expressions.
  pub fn and_many(mut dnfs: Vec<Vec<Conjunct<K, V>>>) -> Self {
    // We sort the DNFs by length to prioritize a small accumulator
    dnfs.sort_unstable_by_key(|dnf| dnf.len());
    let mut it = dnfs.into_iter();
    if let Some(mut this) = it.next() {
      it.for_each(|other| Self::mk_and_core(&mut this, other));
      Dnf::Or(this)
    } else {
      Dnf::True
    }
  }
}

impl Atoms {
  /// * pos = true: PreInstCollection.NormalizeAsTrue
  /// * pos = false: PreInstCollection.NormalizeAsFalse
  pub fn normalize(
    &mut self, g: &Global, lc: &LocalContext, f: Formula, pos: bool,
  ) -> Dnf<AtomId, bool> {
    match f {
      Formula::Neg { f } => self.normalize(g, lc, *f, !pos),
      Formula::And { args } => {
        let mut res = Dnf::mk_bool(pos);
        if pos {
          args.into_iter().for_each(|f| res.mk_and_then(|| self.normalize(g, lc, f, pos)))
        } else {
          args.into_iter().for_each(|f| res.mk_or_else(|| self.normalize(g, lc, f, pos)));
        }
        res
      }
      Formula::True => Dnf::mk_bool(pos),
      _ => {
        let a = self.insert(g, lc, Cow::Owned(f));
        Dnf::single(Conjunct::single(a, pos))
      }
    }
  }
}
