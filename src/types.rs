use crate::VisitMut;
use enum_map::{Enum, EnumMap};
use paste::paste;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::marker::PhantomData;
use std::ops::{Index, IndexMut, Range};

#[derive(Clone)]
pub enum CowBox<'a, A: ?Sized> {
  Borrowed(&'a A),
  Owned(Box<A>),
}

impl<'a, A: ?Sized + std::fmt::Debug> std::fmt::Debug for CowBox<'a, A> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { (**self).fmt(f) }
}

impl<A: ?Sized> std::ops::Deref for CowBox<'_, A> {
  type Target = A;
  fn deref(&self) -> &Self::Target {
    match self {
      CowBox::Borrowed(x) => x,
      CowBox::Owned(x) => x,
    }
  }
}

impl<A: ?Sized + Clone> CowBox<'_, A> {
  #[allow(clippy::wrong_self_convention)]
  pub fn to_owned(self) -> Box<A> {
    match self {
      CowBox::Borrowed(x) => Box::new(x.clone()),
      CowBox::Owned(x) => x,
    }
  }
}

/// A trait for newtyped integers, that can be used as index types in vectors and sets.
pub trait Idx: Copy + Eq + std::hash::Hash + Ord {
  /// Convert from `T` to `usize`
  fn into_usize(self) -> usize;
  /// Convert from `usize` to `T`
  fn from_usize(_: usize) -> Self;
  /// Generate a fresh variable from a `&mut ID` counter.
  #[must_use]
  fn fresh(&mut self) -> Self {
    let n = *self;
    *self = Self::from_usize(self.into_usize() + 1);
    n
  }
}

impl Idx for usize {
  fn into_usize(self) -> usize { self }
  fn from_usize(n: usize) -> Self { n }
}
impl Idx for u32 {
  fn into_usize(self) -> usize { self as _ }
  fn from_usize(n: usize) -> Self { n as _ }
}

/// A vector indexed by a custom indexing type `I`, usually a newtyped integer.
pub struct IdxVec<I, T>(pub Vec<T>, PhantomData<I>);

impl<I, T: std::fmt::Debug> std::fmt::Debug for IdxVec<I, T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.0.fmt(f) }
}

impl<I, T: Clone> Clone for IdxVec<I, T> {
  fn clone(&self) -> Self { Self(self.0.clone(), PhantomData) }
}

impl<I, T> IdxVec<I, T> {
  /// Construct a new empty [`IdxVec`].
  #[must_use]
  pub const fn new() -> Self { Self(vec![], PhantomData) }

  /// Construct a new [`IdxVec`] with the specified capacity.
  #[must_use]
  pub fn with_capacity(capacity: usize) -> Self { Vec::with_capacity(capacity).into() }

  /// Construct a new [`IdxVec`] by calling the specified function.
  #[must_use]
  pub fn from_fn(size: usize, f: impl FnMut() -> T) -> Self {
    Self::from(std::iter::repeat_with(f).take(size).collect::<Vec<_>>())
  }

  /// Construct a new [`IdxVec`] using the default element `size` times.
  #[must_use]
  pub fn from_default(size: usize) -> Self
  where T: Default {
    Self::from_fn(size, T::default)
  }

  /// The number of elements in the [`IdxVec`].
  #[must_use]
  pub fn len(&self) -> usize { self.0.len() }

  /// Get a value by index into the vector.
  pub fn get(&self, index: I) -> Option<&T>
  where I: Idx {
    self.0.get(I::into_usize(index))
  }

  /// Get a value by index into the vector.
  pub fn get_mut(&mut self, index: I) -> Option<&mut T>
  where I: Idx {
    self.0.get_mut(I::into_usize(index))
  }

  /// Returns the value that would be returned by the next call to `push`.
  pub fn peek(&mut self) -> I
  where I: Idx {
    I::from_usize(self.0.len())
  }

  /// Insert a new value at the end of the vector.
  pub fn push(&mut self, val: T) -> I
  where I: Idx {
    let id = self.peek();
    self.0.push(val);
    id
  }

  /// Grow the vector until it is long enough that `vec[idx]` will work.
  pub fn extend_to_include(&mut self, idx: I)
  where
    I: Idx,
    T: Default,
  {
    let n = I::into_usize(idx) + 1;
    if self.0.len() < n {
      self.0.resize_with(n, T::default)
    }
  }

  /// Get the element with index `idx`, extending the vector if necessary.
  pub fn get_mut_extending(&mut self, idx: I) -> &mut T
  where
    I: Idx,
    T: Default,
  {
    self.extend_to_include(idx);
    &mut self[idx]
  }

  /// An iterator including the indexes, like `iter().enumerate()`, as `BlockId`s.
  pub fn enum_iter(&self) -> impl Iterator<Item = (I, &T)>
  where I: Idx {
    self.0.iter().enumerate().map(|(n, val)| (I::from_usize(n), val))
  }

  /// An iterator including the indexes, like `iter_mut().enumerate()`, as `BlockId`s.
  pub fn enum_iter_mut(&mut self) -> impl Iterator<Item = (I, &mut T)>
  where I: Idx {
    self.0.iter_mut().enumerate().map(|(n, val)| (I::from_usize(n), val))
  }

  /// Returns `true` if the vector contains no elements.
  #[must_use]
  pub fn is_empty(&self) -> bool { self.0.is_empty() }
}

impl<I, T> From<Vec<T>> for IdxVec<I, T> {
  fn from(vec: Vec<T>) -> Self { Self(vec, PhantomData) }
}

impl<I, T> std::iter::FromIterator<T> for IdxVec<I, T> {
  fn from_iter<J: IntoIterator<Item = T>>(iter: J) -> Self { Vec::from_iter(iter).into() }
}

impl<I, T> Default for IdxVec<I, T> {
  fn default() -> Self { vec![].into() }
}

impl<I: Idx, T> Index<I> for IdxVec<I, T> {
  type Output = T;
  fn index(&self, index: I) -> &Self::Output { &self.0[I::into_usize(index)] }
}

impl<I: Idx, T> IndexMut<I> for IdxVec<I, T> {
  fn index_mut(&mut self, index: I) -> &mut Self::Output { &mut self.0[I::into_usize(index)] }
}

impl<I: Idx, T> Index<Range<I>> for IdxVec<I, T> {
  type Output = [T];
  fn index(&self, r: Range<I>) -> &Self::Output {
    &self.0[I::into_usize(r.start)..I::into_usize(r.end)]
  }
}

#[macro_export]
macro_rules! mk_id {
  ($($id:ident,)*) => {
    $(
      #[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
      pub struct $id(pub u32);
      impl Idx for $id {
        fn from_usize(n: usize) -> Self { Self(n as u32) }
        fn into_usize(self) -> usize { self.0 as usize }
      }
      impl std::fmt::Debug for $id {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.0.fmt(f) }
      }
      impl std::str::FromStr for $id {
        type Err = std::num::ParseIntError;
        fn from_str(s: &str) -> Result<Self, Self::Err> { u32::from_str(s).map($id) }
      }
    )*
  };
}

#[derive(Clone)]
pub struct SortedIdxVec<I, T> {
  pub vec: IdxVec<I, T>,
  pub sorted: Vec<I>,
}
impl<I, T> std::ops::Deref for SortedIdxVec<I, T> {
  type Target = IdxVec<I, T>;
  fn deref(&self) -> &Self::Target { &self.vec }
}
impl<I, T> std::ops::DerefMut for SortedIdxVec<I, T> {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.vec }
}

impl<I, T> Default for SortedIdxVec<I, T> {
  fn default() -> Self { Self { vec: Default::default(), sorted: Default::default() } }
}

impl<I: Idx, T: std::fmt::Debug> std::fmt::Debug for SortedIdxVec<I, T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_list().entries(self.sorted.iter().map(|&i| &self.vec[i])).finish()
  }
}

impl<I: Idx, T> SortedIdxVec<I, T> {
  pub fn find_index(&self, p: impl Fn(&T) -> Ordering) -> Result<I, usize> {
    let i = self.sorted.partition_point(|&i| p(&self.vec[i]) == Ordering::Less);
    let Some(&idx) = self.sorted.get(i) else { return Err(i) };
    let Ordering::Equal = p(&self.vec[idx]) else { return Err(i) };
    Ok(idx)
  }

  pub fn find(&self, p: impl Fn(&T) -> Ordering) -> Option<(I, &T)> {
    let i = self.find_index(p).ok()?;
    Some((i, &self.vec[i]))
  }

  pub fn sort_all(&mut self, f: impl Fn(&T, &T) -> Ordering) {
    self.sorted = (0..self.vec.len()).map(Idx::from_usize).collect();
    self.sorted.sort_by(|&a, &b| f(&self.vec[a], &self.vec[b]));
  }

  /// Assumes `idx` is the sorted index of `t` (as returned by `find_idx`)
  pub fn insert_at(&mut self, idx: usize, t: T) -> I {
    let i = self.vec.push(t);
    self.sorted.insert(idx, i);
    i
  }

  pub fn truncate(&mut self, len: usize) {
    if len < self.0.len() {
      self.vec.0.truncate(len);
      self.sorted.retain(|t| Idx::into_usize(*t) < len);
      assert!(self.sorted.len() == len)
    }
  }
}

mk_id! {
  ModeId,
  StructId,
  AttrId,
  PredId,
  FuncId,
  SelId,
  AggrId,
  BoundId,
  ConstId,
  FVarId,
  InferId,
  EqClassId,
  EqTermId,
  EqMarkId,
  SchFuncId,
  PrivFuncId,
  LocusId,
  LabelId,
  ArticleId,
  DefId,
  ThmId,
  SchId,
  AtomId,
}
impl ArticleId {
  pub const SELF: ArticleId = ArticleId(0);
}

const MAX_FUNC_NUM: usize = 1500;

pub struct RequirementIndexes {
  pub fwd: EnumMap<Requirement, u32>,
  pub rev: [Option<Requirement>; MAX_FUNC_NUM],
}

impl Default for RequirementIndexes {
  fn default() -> Self { Self { fwd: Default::default(), rev: [None; MAX_FUNC_NUM] } }
}

impl std::fmt::Debug for RequirementIndexes {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.fwd.fmt(f) }
}

macro_rules! mk_requirements {
  ($($id:ident: $ty:ty,)*) => {
    #[derive(Copy, Clone, Debug, Enum)]
    pub enum Requirement {
      $($id,)*
    }
    paste! {
      impl RequirementIndexes {
        $(
          pub fn [<$id:snake>](&self) -> Option<$ty> { self.get(Requirement::$id).map($ty) }
        )*
      }
    }
  }
}
mk_requirements! {
  Any: ModeId,
  SetMode: ModeId,
  EqualsTo: PredId,
  BelongsTo: PredId,
  Empty: AttrId,
  EmptySet: FuncId,
  Element: ModeId,
  PowerSet: FuncId,
  Inclusion: PredId,
  SubDomElem: ModeId,
  RealDom: FuncId,
  NatDom: FuncId,
  RealAdd: FuncId,
  RealMult: FuncId,
  LessOrEqual: PredId,
  Succ: FuncId,
  Union: FuncId,
  Intersection: FuncId,
  Subtraction: FuncId,
  SymmetricDifference: FuncId,
  Meets: PredId,
  RealNeg: FuncId,
  RealInv: FuncId,
  RealDiff: FuncId,
  RealDiv: FuncId,
  Real: AttrId,
  Positive: AttrId,
  Negative: AttrId,
  Natural: AttrId,
  ImaginaryUnit: FuncId,
  Complex: AttrId,
  Omega: FuncId,
  ZeroNumber: FuncId,
  Zero: AttrId,
}

impl ModeId {
  // Every mizar file needs this one and it needs to be mode 0
  pub const ANY: ModeId = ModeId(0);
  // Every mizar file needs this one and it needs to be mode 1
  pub const SET: ModeId = ModeId(1);
}

impl RequirementIndexes {
  pub fn init_rev(&mut self) {
    assert_eq!(self.fwd[Requirement::Any], ModeId::ANY.0 + 1);
    assert_eq!(self.fwd[Requirement::SetMode], ModeId::SET.0 + 1);
    for (req, &val) in &self.fwd {
      self.rev[val as usize] = Some(req);
    }
  }

  pub fn get(&self, req: Requirement) -> Option<u32> { self.fwd[req].checked_sub(1) }

  pub fn mk_eq(&self, t1: Term, t2: Term) -> Formula {
    Formula::Pred { nr: self.equals_to().unwrap(), args: Box::new([t1, t2]) }
  }
}

pub trait Visitable<V> {
  fn visit_d(&mut self, v: &mut V, depth: u32);
  fn visit(&mut self, v: &mut V) { self.visit_d(v, 0) }
  fn visit_cloned_d(&self, v: &mut V, depth: u32) -> Self
  where Self: Clone {
    let mut t = self.clone();
    t.visit_d(v, depth);
    t
  }
  fn visit_cloned(&self, v: &mut V) -> Self
  where Self: Clone {
    self.visit_cloned_d(v, 0)
  }
}

impl<V, T: Visitable<V>> Visitable<V> for &mut T {
  fn visit_d(&mut self, v: &mut V, d: u32) { (**self).visit_d(v, d) }
}
impl<V, T: Visitable<V>> Visitable<V> for Box<T> {
  fn visit_d(&mut self, v: &mut V, d: u32) { (**self).visit_d(v, d) }
}
impl<V, T: Visitable<V>> Visitable<V> for Box<[T]> {
  fn visit_d(&mut self, v: &mut V, d: u32) { self.iter_mut().for_each(|t| t.visit_d(v, d)) }
}
impl<V, T: Visitable<V>> Visitable<V> for Option<T> {
  fn visit_d(&mut self, v: &mut V, d: u32) { self.iter_mut().for_each(|t| t.visit_d(v, d)) }
}
impl<V, T: Visitable<V>> Visitable<V> for Vec<T> {
  fn visit_d(&mut self, v: &mut V, d: u32) { self.iter_mut().for_each(|t| t.visit_d(v, d)) }
}
impl<I, V, T: Visitable<V>> Visitable<V> for IdxVec<I, T> {
  fn visit_d(&mut self, v: &mut V, d: u32) { self.0.visit_d(v, d) }
}
impl<V, A: Visitable<V>, B: Visitable<V>> Visitable<V> for (A, B) {
  fn visit_d(&mut self, v: &mut V, d: u32) {
    self.0.visit_d(v, d);
    self.1.visit_d(v, d)
  }
}

#[derive(Clone)]
pub enum Term {
  /// Locus numbers are shifted from mizar to start at 0
  Locus(LocusId),
  /// Bound var numbers are shifted from mizar to start at 0
  Bound(BoundId),
  /// Constant numbers are shifted from mizar to start at 0
  Constant(ConstId),
  /// ikEqConst: This is used by the equalizer, it is not read in
  EqClass(EqClassId),
  /// Not in mizar. Used for term sharing in the equalizer
  EqMark(EqMarkId),
  /// Used for term sharing in the verifier, but not used in mizar imports
  Infer(InferId),
  SchFunc {
    nr: SchFuncId,
    args: Box<[Term]>,
  },
  Aggregate {
    nr: AggrId,
    args: Box<[Term]>,
  },
  PrivFunc {
    nr: PrivFuncId,
    args: Box<[Term]>,
    value: Box<Term>,
  },
  Functor {
    nr: FuncId,
    args: Box<[Term]>,
  },
  /// Invariant: nr != 0. Zero is not a numeral (!),
  /// it is a `Functor` using Requirement::ZeroNumber
  Numeral(u32),
  Selector {
    nr: SelId,
    args: Box<[Term]>,
  },
  FreeVar(FVarId),
  LambdaVar(u32),
  Qua {
    value: Box<Term>,
    ty: Box<Type>,
  },
  Choice {
    ty: Box<Type>,
  },
  Fraenkel {
    args: Box<[Type]>,
    scope: Box<Term>,
    compr: Box<Formula>,
  },
  // Should not appear in checker imports
  It,
}

impl Default for Term {
  fn default() -> Self { Self::It }
}

impl Term {
  fn debug_args(
    kind: &str, nr: u32, args: &[Term], f: &mut std::fmt::Formatter<'_>,
  ) -> std::fmt::Result {
    write!(f, "{}{}", kind, nr)?;
    let mut s = f.debug_tuple("");
    for arg in args {
      s.field(arg);
    }
    s.finish()
  }

  pub fn args(&self) -> Option<&[Term]> {
    match self {
      Term::SchFunc { args, .. }
      | Term::Aggregate { args, .. }
      | Term::PrivFunc { args, .. }
      | Term::Functor { args, .. }
      | Term::Selector { args, .. } => Some(args),
      _ => None,
    }
  }
}

impl std::fmt::Debug for Term {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Locus(nr) => write!(f, "k{}", nr.0),
      Self::Bound(nr) => write!(f, "b{}", nr.0),
      Self::Constant(nr) => write!(f, "c{}", nr.0),
      Self::EqClass(nr) => write!(f, "e{}", nr.0),
      Self::EqMark(nr) => write!(f, "i{}", nr.0),
      Self::Infer(nr) => write!(f, "?{}", nr.0),
      Self::SchFunc { nr, args } => Self::debug_args("S", nr.0, args, f),
      Self::Aggregate { nr, args } => Self::debug_args("G", nr.0, args, f),
      Self::PrivFunc { nr, args, .. } => Self::debug_args("$F", nr.0, args, f),
      Self::Functor { nr, args } => Self::debug_args("F", nr.0, args, f),
      Self::Numeral(nr) => nr.fmt(f),
      Self::Selector { nr, args } => Self::debug_args("Sel", nr.0, args, f),
      Self::FreeVar(nr) => write!(f, "v{}", nr.0),
      Self::LambdaVar(nr) => write!(f, "l{}", nr),
      Self::Qua { value, ty } => write!(f, "({:?} qua {:?})", value, ty),
      Self::Choice { ty } => write!(f, "(the {:?})", ty),
      Self::Fraenkel { args, scope, compr } =>
        write!(f, "{{{:?} where {:?} : {:?}}}", scope, args, compr),
      Self::It => write!(f, "it"),
    }
  }
}

impl<V: VisitMut> Visitable<V> for Term {
  fn visit_d(&mut self, v: &mut V, d: u32) { v.visit_term(self, d) }
}

impl Term {
  pub fn discr(&self) -> u8 {
    match self {
      Term::Locus(_) => b'A',
      Term::Bound(_) => b'B',
      Term::Constant(_) => b'C',
      Term::Infer(_) => b'D',
      Term::EqClass(..) => b'E',
      Term::EqMark(_) => b'M', // NEW
      Term::SchFunc { .. } => b'F',
      Term::Aggregate { .. } => b'G',
      Term::PrivFunc { .. } => b'H',
      Term::Functor { .. } => b'K',
      Term::Numeral(_) => b'N',
      Term::Selector { .. } => b'U',
      Term::FreeVar(_) => b'X',
      Term::LambdaVar(_) => b'Z',
      Term::Qua { .. } => 213,
      Term::Choice { .. } => 216,
      Term::Fraenkel { .. } => 232,
      Term::It { .. } => 234,
    }
  }
}

#[derive(Clone, Default)]
pub struct Type {
  /// The kind of type (either Mode or Struct), and the id
  pub kind: TypeKind,
  /// The first is the attributes written by the user ("lower cluster"),
  /// the second is the attributes calculated by the system ("upper cluster")
  pub attrs: (Attrs, Attrs),
  /// The mode arguments (ModArgs)
  pub args: Vec<Term>,
}

impl Type {
  pub const fn new(kind: TypeKind) -> Self {
    Self { kind, attrs: (Attrs::EMPTY, Attrs::EMPTY), args: vec![] }
  }
  pub const ANY: Type = Type::new(TypeKind::Mode(ModeId::ANY));
  pub const SET: Type = Type::new(TypeKind::Mode(ModeId::SET));

  /// precondition: the type has kind Struct
  pub fn struct_id(&self) -> StructId {
    match self.kind {
      TypeKind::Mode(_) => panic!("not a struct"),
      TypeKind::Struct(n) => n,
    }
  }
}

impl std::fmt::Debug for Type {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{:?}", self.attrs.0)?;
    // write!(f, "|{:?}", self.attrs.1)?;
    write!(f, "{:?}", self.kind)?;
    if !self.args.is_empty() {
      write!(f, "{:?}", self.args)?;
    }
    Ok(())
  }
}

impl<V: VisitMut> Visitable<V> for Type {
  fn visit_d(&mut self, v: &mut V, d: u32) { v.visit_type(self, d) }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeKind {
  Struct(StructId),
  Mode(ModeId),
}

impl Default for TypeKind {
  fn default() -> Self { Self::Mode(ModeId(0)) }
}

impl std::fmt::Debug for TypeKind {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match *self {
      Self::Struct(n) => write!(f, "S{n:?}"),
      Self::Mode(n) => write!(f, "M{n:?}"),
    }
  }
}

impl From<StructId> for TypeKind {
  fn from(v: StructId) -> Self { Self::Struct(v) }
}

impl From<ModeId> for TypeKind {
  fn from(v: ModeId) -> Self { Self::Mode(v) }
}

impl TypeKind {
  pub fn discr(&self) -> u8 {
    match self {
      TypeKind::Mode(_) => b'M',
      TypeKind::Struct(_) => b'G',
    }
  }
}

#[derive(Clone)]
pub enum Formula {
  SchemePred {
    nr: u32,
    args: Box<[Term]>,
  },
  Pred {
    nr: PredId,
    args: Box<[Term]>,
  },
  Attr {
    nr: AttrId,
    /// Invariant: args is not empty
    args: Box<[Term]>,
  },
  PrivPred {
    nr: u32,
    args: Box<[Term]>,
    value: Box<Formula>,
  },
  /// ikFrmQual
  Is {
    term: Box<Term>,
    ty: Box<Type>,
  },
  Neg {
    /// Invariant: the formula is not Neg
    f: Box<Formula>,
  },
  /// ikFrmConj
  And {
    /// Invariant: args.len() > 1 and does not contain And expressions
    args: Vec<Formula>,
  },
  /// ikFrmUniv
  ForAll {
    dom: Box<Type>,
    scope: Box<Formula>,
  },
  /// ikFrmFlexConj
  FlexAnd {
    orig: Box<[Formula; 2]>,
    terms: Box<[Term; 2]>,
    expansion: Box<Formula>,
  },
  /// ikFrmVerum
  True,
  Thesis,
}

impl Default for Formula {
  fn default() -> Self { Self::True }
}

impl<V: VisitMut> Visitable<V> for Formula {
  fn visit_d(&mut self, v: &mut V, d: u32) { v.visit_formula(self, d) }
}

impl std::fmt::Debug for Formula {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::SchemePred { nr, args } => Term::debug_args("SP", *nr, args, f),
      Self::Pred { nr, args } => Term::debug_args("P", nr.0, args, f),
      Self::Attr { nr, args } => Term::debug_args("A", nr.0, args, f),
      Self::PrivPred { nr, args, value } => Term::debug_args("$P", *nr, args, f),
      Self::Is { term, ty } => write!(f, "({:?} is {:?})", term, ty),
      Self::Neg { f: fmla } => write!(f, "¬{:?}", fmla),
      Self::And { args } => match &**args {
        [] | [_] => unreachable!(),
        [fs @ .., fmla] => {
          write!(f, "(")?;
          for fm in fs {
            write!(f, "{:?} ∧ ", fm)?
          }
          write!(f, "{:?})", fmla)
        }
      },
      Self::ForAll { dom, scope } => write!(f, "∀ {:?}, {:?}", dom, scope),
      Self::FlexAnd { orig, terms, expansion } => write!(f, "{:?} ∧ ... ∧ {:?}", orig[0], orig[1]),
      Self::True => write!(f, "true"),
      Self::Thesis => write!(f, "thesis"),
    }
  }
}

impl Formula {
  pub fn discr(&self) -> u8 {
    match self {
      Formula::SchemePred { .. } => b'P',
      Formula::Pred { .. } => b'R',
      Formula::Attr { .. } => b'V',
      Formula::PrivPred { .. } => b'S',
      Formula::Is { .. } => 144,
      Formula::Neg { .. } => 170,
      Formula::And { .. } => b'&',
      Formula::ForAll { .. } => 157,
      Formula::FlexAnd { .. } => b'b',
      Formula::True => b'%',
      Formula::Thesis => b'$',
    }
  }

  pub fn mk_neg(self) -> Self {
    match self {
      Formula::Neg { f } => *f,
      _ => Formula::Neg { f: Box::new(self) },
    }
  }

  pub fn maybe_neg(self, pos: bool) -> Self {
    if pos {
      self
    } else {
      self.mk_neg()
    }
  }

  // postcondition: the things pushed to vec are not And expressions
  pub fn append_conjuncts_to(self, vec: &mut Vec<Formula>) {
    match self {
      Formula::True => {}
      Formula::And { mut args } => vec.append(&mut args),
      f => vec.push(f),
    }
  }

  // Precondition: the args are not And expressions
  pub fn mk_and(args: Vec<Formula>) -> Formula {
    match args.len() {
      0 => Formula::True,
      1 => { args }.pop().unwrap(),
      _ => Formula::And { args },
    }
  }

  /// * pos = true: constructs self && vec[0] && ... && vec[n-1]
  /// * pos = false: constructs self || vec[0] || ... || vec[n-1]
  pub fn conjdisj_many(&mut self, pos: bool, vec: Vec<Formula>) {
    if !vec.is_empty() {
      let mut conjs = vec![];
      std::mem::take(self).maybe_neg(pos).append_conjuncts_to(&mut conjs);
      vec.into_iter().for_each(|f| f.maybe_neg(pos).append_conjuncts_to(&mut conjs));
      *self = Formula::mk_and(conjs).maybe_neg(pos);
    }
  }
}

#[derive(Clone)]
pub enum Attrs {
  Inconsistent,
  Consistent(Vec<Attr>),
}

impl Attrs {
  pub const EMPTY: Attrs = Self::Consistent(vec![]);

  pub fn attrs(&self) -> &[Attr] {
    match self {
      Attrs::Inconsistent => &[],
      Attrs::Consistent(attrs) => attrs,
    }
  }
}
impl std::fmt::Debug for Attrs {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Attrs::Inconsistent => write!(f, "F+"),
      Attrs::Consistent(attrs) => {
        for a in attrs {
          write!(f, "{:?}+", a)?
        }
        Ok(())
      }
    }
  }
}

impl Default for Attrs {
  fn default() -> Self { Self::EMPTY }
}

impl<V: VisitMut> Visitable<V> for Attrs {
  fn visit_d(&mut self, v: &mut V, d: u32) { v.visit_attrs(self, d) }
}

#[derive(Clone)]
pub struct Attr {
  pub nr: AttrId,
  pub pos: bool,
  pub args: Box<[Term]>,
}

impl std::fmt::Debug for Attr {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if !self.pos {
      write!(f, "-")?
    }
    write!(f, "A{}", self.nr.0)?;
    if !self.args.is_empty() {
      write!(f, "{:?}", self.args)?;
    }
    Ok(())
  }
}
impl<V: VisitMut> Visitable<V> for Attr {
  fn visit_d(&mut self, v: &mut V, d: u32) { self.args.visit_d(v, d) }
}

#[derive(Copy, Clone, Default, PartialEq, Eq)]
pub struct Article([u8; 8]);

impl std::fmt::Debug for Article {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    std::fmt::Display::fmt(self, f)
  }
}

impl std::fmt::Display for Article {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.as_str().fmt(f) }
}
impl Article {
  pub fn from_bytes(s: &[u8]) -> Article {
    let mut arr = [0; 8];
    arr[..s.len()].copy_from_slice(s);
    Article(arr)
  }
  pub fn as_str(&self) -> &str {
    std::str::from_utf8(&self.0[..self.0.iter().position(|&x| x == 0).unwrap_or(8)]).unwrap()
  }
}

#[derive(Copy, Clone, Debug, Enum)]
pub enum PropertyKind {
  Symmetry,
  Reflexivity,
  Irreflexivity,
  Associativity,
  Transitivity,
  Commutativity,
  Connectedness,
  Asymmetry,
  Idempotence,
  Involutiveness,
  Projectivity,
  Sethood,
  Abstractness,
}

impl TryFrom<&[u8]> for PropertyKind {
  type Error = ();
  fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
    match value {
      b"Symmetry" => Ok(PropertyKind::Symmetry),
      b"Reflexivity" => Ok(PropertyKind::Reflexivity),
      b"Irreflexivity" => Ok(PropertyKind::Irreflexivity),
      b"Associativity" => Ok(PropertyKind::Associativity),
      b"Transitivity" => Ok(PropertyKind::Transitivity),
      b"Commutativity" => Ok(PropertyKind::Commutativity),
      b"Connectedness" => Ok(PropertyKind::Connectedness),
      b"Asymmetry" => Ok(PropertyKind::Asymmetry),
      b"Idempotence" => Ok(PropertyKind::Idempotence),
      b"Involutiveness" => Ok(PropertyKind::Involutiveness),
      b"Projectivity" => Ok(PropertyKind::Projectivity),
      b"Sethood" => Ok(PropertyKind::Sethood),
      b"Abstractness" => Ok(PropertyKind::Abstractness),
      _ => Err(()),
    }
  }
}

#[derive(Copy, Clone, Default)]
pub struct PropertySet(u16);

impl std::fmt::Debug for PropertySet {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_set()
      .entries((0..PropertyKind::LENGTH).map(PropertyKind::from_usize).filter(|&p| self.get(p)))
      .finish()
  }
}

impl PropertySet {
  pub fn get(&self, prop: PropertyKind) -> bool { self.0 & (1 << prop as u16) != 0 }
  pub fn set(&mut self, prop: PropertyKind) { self.0 |= 1 << prop as u16 }
}

#[derive(Clone, Default, Debug)]
pub struct Constructor<I> {
  // pub data: ConstructorData,
  pub article: Article,
  /// number of constructor in article
  pub abs_nr: u32,
  pub primary: Box<[Type]>,
  pub redefines: Option<I>,
  pub superfluous: u8,
  pub properties: PropertySet,
  pub arg1: u32,
  pub arg2: u32,
}
impl<I, V: VisitMut> Visitable<V> for Constructor<I> {
  fn visit_d(&mut self, v: &mut V, d: u32) { self.primary.visit_d(v, d) }
}

#[derive(Clone, Debug)]
pub struct TyConstructor<I> {
  pub c: Constructor<I>,
  pub ty: Type,
}

impl<I> std::ops::Deref for TyConstructor<I> {
  type Target = Constructor<I>;
  fn deref(&self) -> &Self::Target { &self.c }
}
impl<I, V: VisitMut> Visitable<V> for TyConstructor<I> {
  fn visit_d(&mut self, v: &mut V, d: u32) {
    self.c.visit_d(v, d);
    self.ty.visit_d(v, d)
  }
}

#[derive(Clone, Debug)]
pub struct StructMode {
  pub c: Constructor<StructId>,
  // These are guaranteed to be struct types
  pub prefixes: Box<[Type]>,
  pub aggr: Option<AggrId>,
  pub fields: Box<[SelId]>,
}

impl std::ops::Deref for StructMode {
  type Target = Constructor<StructId>;
  fn deref(&self) -> &Self::Target { &self.c }
}
impl<V: VisitMut> Visitable<V> for StructMode {
  fn visit_d(&mut self, v: &mut V, d: u32) {
    self.c.visit_d(v, d);
    self.prefixes.visit_d(v, d)
  }
}

#[derive(Clone, Debug)]
pub struct Aggregate {
  pub c: TyConstructor<AggrId>,
  pub base: u32,
  pub coll: Box<[SelId]>,
}
impl<V: VisitMut> Visitable<V> for Aggregate {
  fn visit_d(&mut self, v: &mut V, d: u32) { self.c.visit_d(v, d) }
}

impl std::ops::Deref for Aggregate {
  type Target = TyConstructor<AggrId>;
  fn deref(&self) -> &Self::Target { &self.c }
}
impl std::ops::DerefMut for Aggregate {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.c }
}

#[derive(Clone, Debug, Default)]
pub struct Constructors {
  pub mode: IdxVec<ModeId, TyConstructor<ModeId>>,
  pub struct_mode: IdxVec<StructId, StructMode>,
  pub attribute: IdxVec<AttrId, TyConstructor<AttrId>>,
  pub predicate: IdxVec<PredId, Constructor<PredId>>,
  pub functor: IdxVec<FuncId, TyConstructor<FuncId>>,
  pub selector: IdxVec<SelId, TyConstructor<SelId>>,
  pub aggregate: IdxVec<AggrId, Aggregate>,
}
impl<V: VisitMut> Visitable<V> for Constructors {
  fn visit_d(&mut self, v: &mut V, d: u32) {
    self.mode.visit_d(v, d);
    self.struct_mode.visit_d(v, d);
    self.attribute.visit_d(v, d);
    self.predicate.visit_d(v, d);
    self.functor.visit_d(v, d);
    self.selector.visit_d(v, d);
    self.aggregate.visit_d(v, d);
  }
}

impl Constructors {
  pub fn push(&mut self, c: ConstructorDef) -> ConstrKind {
    match c {
      ConstructorDef::Mode(c) => ConstrKind::Mode(self.mode.push(c)),
      ConstructorDef::StructMode(c) => ConstrKind::Struct(self.struct_mode.push(c)),
      ConstructorDef::Attr(c) => ConstrKind::Attr(self.attribute.push(c)),
      ConstructorDef::Pred(c) => ConstrKind::Pred(self.predicate.push(c)),
      ConstructorDef::Func(c) => ConstrKind::Func(self.functor.push(c)),
      ConstructorDef::Sel(c) => ConstrKind::Sel(self.selector.push(c)),
      ConstructorDef::Aggr(c) => ConstrKind::Aggr(self.aggregate.push(c)),
    }
  }

  pub fn visit_at<V: VisitMut>(&mut self, v: &mut V, k: ConstrKind) {
    match k {
      ConstrKind::Mode(k) => self.mode[k].visit(v),
      ConstrKind::Struct(k) => self.struct_mode[k].visit(v),
      ConstrKind::Attr(k) => self.attribute[k].visit(v),
      ConstrKind::Pred(k) => self.predicate[k].visit(v),
      ConstrKind::Func(k) => self.functor[k].visit(v),
      ConstrKind::Sel(k) => self.selector[k].visit(v),
      ConstrKind::Aggr(k) => self.aggregate[k].visit(v),
    }
  }
}

#[derive(Clone, Debug, Default)]
pub struct Clusters {
  pub registered: Vec<RegisteredCluster>,
  /// sorted by |a, b| FunctorCluster::cmp_term(&a.term, ctx, &b.term)
  pub functor: SortedIdxVec<usize, FunctorCluster>,
  pub conditional: ConditionalClusters,
}

#[derive(Clone)]
pub struct Cluster {
  /// nPrimaryList
  pub primary: Box<[Type]>,
  /// nConsequent.(Lower, Upper)
  pub consequent: (Attrs, Attrs),
  /// nArticle
  pub article: Article,
  /// nAbsNr
  pub abs_nr: u32,
}
impl<V: VisitMut> Visitable<V> for Cluster {
  fn visit_d(&mut self, v: &mut V, d: u32) {
    self.primary.visit_d(v, d);
    self.consequent.visit_d(v, d);
  }
}

impl std::fmt::Debug for Cluster {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("Cluster")
      .field("primary", &self.primary)
      .field("consequent.lower", &self.consequent.0)
      .field("consequent.upper", &self.consequent.1)
      .field("article", &self.article)
      .field("abs_nr", &self.abs_nr)
      .finish()
  }
}

#[derive(Clone, Debug)]
pub struct RegisteredCluster {
  pub cl: Cluster,
  pub ty: Box<Type>,
}

impl std::ops::Deref for RegisteredCluster {
  type Target = Cluster;
  fn deref(&self) -> &Self::Target { &self.cl }
}
impl std::ops::DerefMut for RegisteredCluster {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.cl }
}
impl<V: VisitMut> Visitable<V> for RegisteredCluster {
  fn visit_d(&mut self, v: &mut V, d: u32) {
    self.cl.visit_d(v, d);
    self.ty.visit_d(v, d);
  }
}

#[derive(Clone, Debug)]
pub struct ConditionalCluster {
  pub cl: Cluster,
  pub ty: Box<Type>,
  pub antecedent: Attrs,
}
impl std::ops::Deref for ConditionalCluster {
  type Target = Cluster;
  fn deref(&self) -> &Self::Target { &self.cl }
}
impl std::ops::DerefMut for ConditionalCluster {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.cl }
}
impl<V: VisitMut> Visitable<V> for ConditionalCluster {
  fn visit_d(&mut self, v: &mut V, d: u32) {
    self.cl.visit_d(v, d);
    self.ty.visit_d(v, d);
    self.antecedent.visit_d(v, d);
  }
}

#[derive(Clone, Debug)]
pub struct FunctorCluster {
  pub cl: Cluster,
  pub ty: Option<Box<Type>>,
  pub term: Box<Term>,
}

impl std::ops::Deref for FunctorCluster {
  type Target = Cluster;
  fn deref(&self) -> &Self::Target { &self.cl }
}
impl std::ops::DerefMut for FunctorCluster {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.cl }
}
impl<V: VisitMut> Visitable<V> for FunctorCluster {
  fn visit_d(&mut self, v: &mut V, d: u32) {
    self.cl.visit_d(v, d);
    self.ty.visit_d(v, d);
    self.term.visit_d(v, d);
  }
}

impl FunctorCluster {
  pub fn cmp_term(this: &Term, ctx: &Constructors, other: &Term) -> std::cmp::Ordering {
    match (this, other) {
      (&Term::Functor { nr: n1, .. }, &Term::Functor { nr: n2, .. }) => {
        let n1 = ctx.functor[n1].redefines.unwrap_or(n1);
        let n2 = ctx.functor[n2].redefines.unwrap_or(n2);
        n1.cmp(&n2)
      }
      (Term::Functor { .. }, _) => std::cmp::Ordering::Greater,
      (_, Term::Functor { .. }) => std::cmp::Ordering::Less,
      (_, _) => std::cmp::Ordering::Equal,
    }
  }
}

#[derive(Clone, Debug, Default)]
pub struct ConditionalClusters {
  pub vec: Vec<ConditionalCluster>,
  pub attr_clusters: EnumMap<bool, BTreeMap<AttrId, BTreeSet<u32>>>,
}
impl std::ops::Deref for ConditionalClusters {
  type Target = Vec<ConditionalCluster>;
  fn deref(&self) -> &Self::Target { &self.vec }
}
impl std::ops::DerefMut for ConditionalClusters {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.vec }
}
impl<V: VisitMut> Visitable<V> for ConditionalClusters {
  fn visit_d(&mut self, v: &mut V, d: u32) { self.vec.visit_d(v, d); }
}

impl ConditionalClusters {
  pub fn push(&mut self, ctx: &Constructors, cc: ConditionalCluster) {
    if let Attrs::Consistent(attrs) = &cc.antecedent {
      for attr in attrs {
        self.attr_clusters[attr.pos]
          .entry(attr.adjusted_nr(ctx))
          .or_default()
          .insert(self.vec.len() as u32);
      }
    }
    self.vec.push(cc)
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConstrKind {
  Mode(ModeId),
  Struct(StructId),
  Attr(AttrId),
  Pred(PredId),
  Func(FuncId),
  Sel(SelId),
  Aggr(AggrId),
}

impl ConstrKind {
  pub fn discr(&self) -> u8 {
    match self {
      ConstrKind::Mode(_) => b'M',
      ConstrKind::Struct(_) => b'S',
      ConstrKind::Pred(_) => b'R',
      ConstrKind::Attr(_) => b'V',
      ConstrKind::Func(_) => b'K',
      ConstrKind::Sel(_) => b'U',
      ConstrKind::Aggr(_) => b'G',
    }
  }
}

#[derive(Clone, Debug)]
pub struct ConstrDescr {
  pub def_nr: u32,
  pub article: Article,
  pub constr: ConstrKind,
  pub primary: Box<[Type]>,
}
impl<V: VisitMut> Visitable<V> for ConstrDescr {
  fn visit_d(&mut self, v: &mut V, d: u32) { self.primary.visit_d(v, d) }
}

#[derive(Clone, Debug)]
pub struct ConstrDef {
  pub descr: ConstrDescr,
  pub pattern: Option<()>,
}
impl std::ops::Deref for ConstrDef {
  type Target = ConstrDescr;
  fn deref(&self) -> &Self::Target { &self.descr }
}
impl<V: VisitMut> Visitable<V> for ConstrDef {
  fn visit_d(&mut self, v: &mut V, d: u32) { self.descr.visit_d(v, d) }
}

#[derive(Clone, Debug)]
pub struct DefCase<T> {
  pub case: T,
  pub guard: Formula,
}
impl<V: VisitMut, T: Visitable<V>> Visitable<V> for DefCase<T> {
  fn visit_d(&mut self, v: &mut V, d: u32) {
    self.case.visit_d(v, d);
    self.guard.visit_d(v, d)
  }
}

#[derive(Clone, Debug)]
pub struct DefBody<T> {
  /// nPartialDefinientia
  pub cases: Box<[DefCase<T>]>,
  pub otherwise: Option<T>,
}
impl<V: VisitMut, T: Visitable<V>> Visitable<V> for DefBody<T> {
  fn visit_d(&mut self, v: &mut V, d: u32) {
    self.cases.visit_d(v, d);
    self.otherwise.visit_d(v, d)
  }
}

#[derive(Clone, Debug)]
pub enum DefValue {
  Term(DefBody<Term>),
  Formula(DefBody<Formula>),
}
impl<V: VisitMut> Visitable<V> for DefValue {
  fn visit_d(&mut self, v: &mut V, d: u32) {
    match self {
      DefValue::Term(body) => body.visit_d(v, d),
      DefValue::Formula(body) => body.visit_d(v, d),
    }
  }
}

impl DefValue {
  pub fn discr(&self) -> u8 {
    match self {
      DefValue::Term(_) => b'e',
      DefValue::Formula(_) => b'm',
    }
  }
}

#[derive(Clone, Debug)]
pub enum ConstructorDef {
  Mode(TyConstructor<ModeId>),
  StructMode(StructMode),
  Attr(TyConstructor<AttrId>),
  Pred(Constructor<PredId>),
  Func(TyConstructor<FuncId>),
  Sel(TyConstructor<SelId>),
  Aggr(Aggregate),
}
impl<V: VisitMut> Visitable<V> for ConstructorDef {
  fn visit_d(&mut self, v: &mut V, d: u32) {
    match self {
      ConstructorDef::Mode(c) => c.visit_d(v, d),
      ConstructorDef::StructMode(c) => c.visit_d(v, d),
      ConstructorDef::Attr(c) => c.visit_d(v, d),
      ConstructorDef::Pred(c) => c.visit_d(v, d),
      ConstructorDef::Func(c) => c.visit_d(v, d),
      ConstructorDef::Sel(c) => c.visit_d(v, d),
      ConstructorDef::Aggr(c) => c.visit_d(v, d),
    }
  }
}

#[derive(Clone, Debug)]
pub struct Definiens {
  pub c: ConstrDef,
  pub lab_id: Option<LabelId>,
  pub essential: Box<[LocusId]>,
  pub assumptions: Formula,
  pub value: DefValue,
}

impl std::ops::Deref for Definiens {
  type Target = ConstrDef;
  fn deref(&self) -> &Self::Target { &self.c }
}

impl<V: VisitMut> Visitable<V> for Definiens {
  fn visit_d(&mut self, v: &mut V, d: u32) {
    self.c.visit_d(v, d);
    self.assumptions.visit_d(v, d);
    self.value.visit_d(v, d)
  }
}

#[derive(Clone, Debug)]
pub struct Property {
  pub article: Article,
  pub abs_nr: u32,
  pub primary: Box<[Type]>,
  pub ty: Type,
  pub kind: PropertyKind,
}
impl<V: VisitMut> Visitable<V> for Property {
  fn visit_d(&mut self, v: &mut V, d: u32) {
    self.primary.visit_d(v, d);
    self.ty.visit_d(v, d);
  }
}

#[derive(Clone, Debug)]
pub enum IdentifyKind {
  /// lhs must be Term::Functor
  Func { lhs: Term, rhs: Term },
  /// lhs must be Formula::Attr
  Attr { lhs: Formula, rhs: Formula },
  /// lhs must be Formula::Pred
  Pred { lhs: Formula, rhs: Formula },
}
impl<V: VisitMut> Visitable<V> for IdentifyKind {
  fn visit_d(&mut self, v: &mut V, d: u32) {
    match self {
      IdentifyKind::Func { lhs, rhs } => (lhs, rhs).visit_d(v, d),
      IdentifyKind::Attr { lhs, rhs } => (lhs, rhs).visit_d(v, d),
      IdentifyKind::Pred { lhs, rhs } => (lhs, rhs).visit_d(v, d),
    }
  }
}

impl IdentifyKind {
  pub fn discr(&self) -> u8 {
    match self {
      IdentifyKind::Func { .. } => b'K',
      IdentifyKind::Attr { .. } => b'V',
      IdentifyKind::Pred { .. } => b'R',
    }
  }
}

#[derive(Debug)]
pub struct Identify {
  pub article: Article,
  pub abs_nr: u32,
  pub primary: Box<[Type]>,
  pub kind: IdentifyKind,
  pub eq_args: Box<[(LocusId, LocusId)]>,
}

#[derive(Debug)]
pub struct Reduction {
  pub article: Article,
  pub abs_nr: u32,
  pub primary: Box<[Type]>,
  pub terms: [Term; 2],
}

#[derive(Debug)]
pub struct EqualsDef {
  pub primary: Box<[Type]>,
  pub expansion: Term,
  pub pattern: (FuncId, Box<[Term]>),
  pub essential: Box<[LocusId]>,
}

#[derive(Default)]
pub struct PropList {
  vec: Vec<()>,
  labeled: IdxVec<LabelId, u32>,
}

type ThmRef = (ArticleId, ThmId);
type DefRef = (ArticleId, DefId);
type SchRef = (ArticleId, SchId);

#[derive(Default, Debug)]
pub struct References {
  pub thm: HashMap<ThmRef, u32>,
  pub def: HashMap<DefRef, u32>,
  pub sch: HashMap<SchRef, u32>,
}

#[derive(Debug)]
pub struct Scheme {
  pub tys: Box<[Type]>,
  pub prems: Box<[Formula]>,
  pub thesis: Formula,
}

#[derive(Default, Debug)]
pub struct Libraries {
  pub thm: BTreeMap<ThmRef, Formula>,
  pub def: BTreeMap<DefRef, Formula>,
  pub sch: BTreeMap<SchRef, Scheme>,
}

#[derive(Copy, Clone, Default)]
pub struct Position {
  pub line: u32,
  pub col: u32,
}

impl std::fmt::Debug for Position {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}:{}", self.line, self.col)
  }
}

#[derive(Clone, Debug)]
pub enum SchemeDecl {
  Func { args: Box<[Type]>, ty: Type },
  Pred { args: Box<[Type]> },
}
impl<V: VisitMut> Visitable<V> for SchemeDecl {
  fn visit_d(&mut self, v: &mut V, d: u32) {
    match self {
      SchemeDecl::Func { args, ty } => (args, ty).visit_d(v, d),
      SchemeDecl::Pred { args } => args.visit_d(v, d),
    }
  }
}

#[derive(Debug)]
pub enum InferenceKind {
  By { linked: bool },
  From { sch: SchRef },
}

#[derive(Debug)]
pub enum ReferenceKind {
  Priv(LabelId),
  Thm(ThmRef),
  Def(DefRef),
}

#[derive(Debug)]
pub struct Reference {
  pub pos: Position,
  pub kind: ReferenceKind,
}

#[derive(Debug)]
pub struct Inference {
  pub kind: InferenceKind,
  pub pos: Position,
  pub refs: Vec<Reference>,
}

#[derive(Debug)]
pub struct Thesis {
  pub f: Formula,
  pub exps: Vec<(u32, u32)>,
}

#[derive(Debug)]
pub enum Justification {
  Simple(Inference),
  Proof {
    pos: (Position, Position),
    label: Option<LabelId>,
    thesis: Formula,
    items: Vec<(Item, Option<Thesis>)>,
  },
  SkippedProof,
}

#[derive(Debug, PartialEq, Eq)]
pub enum DefinitionKind {
  PrAttr,
  Mode,
  Pred,
  Func,
  ExpandMode,
}

#[derive(Debug)]
pub enum ClusterKind {
  R,
  F,
  C,
}

#[derive(Debug)]
pub enum ClusterDeclKind {
  R(RegisteredCluster),
  F(FunctorCluster),
  C(ConditionalCluster),
}
impl<V: VisitMut> Visitable<V> for ClusterDeclKind {
  fn visit_d(&mut self, v: &mut V, d: u32) {
    match self {
      ClusterDeclKind::R(c) => c.visit_d(v, d),
      ClusterDeclKind::F(c) => c.visit_d(v, d),
      ClusterDeclKind::C(c) => c.visit_d(v, d),
    }
  }
}

#[derive(Debug)]
pub struct ClusterDecl {
  pub kind: ClusterDeclKind,
  pub conds: Vec<CorrCond>,
  pub corr: Option<Correctness>,
}

#[derive(Debug)]
pub struct JustifiedProperty {
  pub kind: PropertyKind,
  pub prop: Proposition,
  pub just: Justification,
}

#[derive(Debug)]
pub struct Definition {
  pub pos: Position,
  pub label: Option<LabelId>,
  pub redef: bool,
  pub kind: DefinitionKind,
  pub conds: Vec<CorrCond>,
  pub corr: Option<Correctness>,
  pub props: Vec<JustifiedProperty>,
  pub constr: Option<ConstructorDef>,
}

#[derive(Debug)]
pub struct DefStruct {
  pub pos: Position,
  pub label: Option<LabelId>,
  pub constrs: Vec<ConstructorDef>,
  pub cl: ClusterDecl,
  pub conds: Vec<CorrCond>,
  pub corr: Option<Correctness>,
}

#[derive(Clone)]
pub struct Proposition {
  pub pos: Position,
  pub label: Option<LabelId>,
  pub f: Formula,
}

impl std::fmt::Debug for Proposition {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "[{:?}] ", self.pos)?;
    if let Some(id) = self.label {
      write!(f, "L{:?}: ", id)?;
    }
    write!(f, "{:?}", self.f)
  }
}
impl<V: VisitMut> Visitable<V> for Proposition {
  fn visit_d(&mut self, v: &mut V, d: u32) { self.f.visit_d(v, d) }
}
#[derive(Debug)]
pub enum PrivateStatement {
  Proposition { prop: Proposition, just: Justification },
  IterEquality { start: Position, label: Option<LabelId>, lhs: Term, steps: Vec<(Term, Inference)> },
  Now { pos: (Position, Position), label: Option<LabelId>, thesis: Formula, items: Box<[Item]> },
}

#[derive(Debug)]
pub struct GivenItem {
  pub prop: Proposition,
  pub fixed: Vec<Type>,
  pub intro: Vec<Proposition>,
}

#[derive(Debug)]
pub enum AuxiliaryItem {
  PrivateStatement(PrivateStatement),
  /// itChoice
  Consider {
    prop: Proposition,
    just: Justification,
    fixed: Vec<Type>,
    intro: Vec<Proposition>,
  },
  /// itConstantDefinition
  Set {
    term: Term,
    ty: Type,
  },
  Reconsider {
    terms: Vec<(Type, Term)>,
    prop: Proposition,
    just: Justification,
  },
  /// itPrivFuncDefinition
  DefFunc {
    args: Box<[Type]>,
    value: Term,
    ty: Type,
  },
  /// itPrivPredDefinition
  DefPred {
    args: Box<[Type]>,
    value: Formula,
  },
}

#[derive(Debug)]
pub enum Registration {
  Cluster(ClusterDecl),
  Identify { kind: Identify, conds: Vec<CorrCond>, corr: Option<Correctness> },
  Reduction { kind: Reduction, conds: Vec<CorrCond>, corr: Option<Correctness> },
  Property { kind: Property, prop: Proposition, just: Justification },
}

#[derive(Debug)]
pub enum CorrCondKind {
  Coherence,
  Compatibility,
  Consistency,
  Existence,
  Uniqueness,
  Reducibility,
}

#[derive(Debug)]
pub struct SimpleCorrCond {
  pub kind: CorrCondKind,
  pub f: Formula,
}

#[derive(Debug)]
pub struct CorrCond {
  pub kind: CorrCondKind,
  pub prop: Proposition,
  pub just: Justification,
}

#[derive(Debug)]
pub struct Correctness {
  pub conds: Vec<SimpleCorrCond>,
  pub prop: Proposition,
  pub just: Justification,
}

#[derive(Debug)]
pub struct SchemeBlock {
  pub pos: (Position, Position),
  pub nr: SchId,
  pub decls: Vec<SchemeDecl>,
  pub prems: Vec<Proposition>,
  pub thesis: Proposition,
  pub just: Justification,
}

#[derive(Debug)]
pub enum CancelKind {
  Def,
  Thm,
  Sch,
}

#[derive(Debug)]
pub enum CaseOrSuppose {
  Case(Vec<Proposition>),
  Suppose(Vec<Proposition>),
}

#[derive(Debug)]
pub struct CaseOrSupposeBlock {
  pub pos: (Position, Position),
  pub label: Option<LabelId>,
  pub block_thesis: Formula,
  pub cs: CaseOrSuppose,
  pub items: Vec<(Item, Option<Thesis>)>,
  pub thesis: Option<Thesis>,
}

#[derive(Debug)]
pub struct PerCases {
  pub pos: (Position, Position),
  pub label: Option<LabelId>,
  pub block_thesis: Formula,
  pub cases: Vec<CaseOrSupposeBlock>,
  pub prop: Proposition,
  pub just: Justification,
  pub thesis: Option<Thesis>,
}

#[derive(Copy, Clone, Debug)]
pub enum BlockKind {
  Definition,
  Registration,
  Notation,
}

#[derive(Debug)]
pub enum Item {
  /// itGeneralization
  Let(Vec<Type>),
  /// itExistentialAssumption
  Given(GivenItem),
  Conclusion(PrivateStatement),
  /// itAssumption
  Assume(Vec<Proposition>),
  /// itSimpleExemplification
  Take(Term),
  /// itExemplificationWithEquality
  TakeAsVar(Type, Term),
  PerCases(PerCases),
  AuxiliaryItem(AuxiliaryItem),
  Registration(Registration),
  Scheme(SchemeBlock),
  Theorem {
    prop: Proposition,
    just: Justification,
  },
  DefTheorem {
    kind: Option<ConstrKind>,
    prop: Proposition,
  },
  Reservation {
    ids: Vec<u32>,
    ty: Box<Type>,
  },
  Section,
  Canceled(CancelKind),
  Definition(Definition),
  DefStruct(DefStruct),
  Definiens(Definiens),
  Block {
    kind: BlockKind,
    pos: (Position, Position),
    label: Option<LabelId>,
    items: Vec<Item>,
  },
}
