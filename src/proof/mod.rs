#![allow(unused)]

use crate::types::{FuncId as MFuncId, PredId as MPredId, *};
use crate::{mk_id, Assignment, FixedVar, LocalContext};
use hashbrown::raw::RawTable;
use hashbrown::{HashMap, HashSet};
use std::cell::{Cell, RefCell};
use std::fs::File;
use std::hash::{Hash, Hasher};
use std::io::BufWriter;
use std::ops::{Index, IndexMut};
use write::{OProofId, ProofWriter};

mod accom;
mod write;

pub use write::{Step, WriteProof, XmlProofWriter};

mk_id! {
  FuncId(u32),
  TFuncId(u32),
  PredId(u32),
  VarId(u32),
  GProofId(u32),
  LProofId(u32),
  HypId(u32),
}

#[derive(Debug)]
pub enum ProofIdKind {
  Local(LProofId),
  Global(GProofId),
}

impl ProofIdKind {
  fn pack(self) -> ProofId {
    match self {
      ProofIdKind::Local(n) => n.into(),
      ProofIdKind::Global(n) => n.into(),
    }
  }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct ProofId(u32);
impl std::fmt::Debug for ProofId {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.unpack().fmt(f) }
}

impl Default for ProofId {
  fn default() -> Self { ProofId::INVALID }
}
impl<V> Visitable<V> for ProofId {
  fn visit(&mut self, v: &mut V) {}
}

impl ProofId {
  pub const INVALID: Self = Self(u32::MAX);
  pub const C0: Self = Self::Global(GProofId::C0);
  #[allow(non_snake_case)]
  const fn Global(v: GProofId) -> Self { Self(v.0 | 1 << 31) }
  #[allow(non_snake_case)]
  const fn Local(v: LProofId) -> Self { Self(v.0) }

  #[inline]
  fn is_local(self) -> bool { self.0 & (1 << 31) == 0 }
  #[inline]
  fn unpack(self) -> ProofIdKind {
    if self.is_local() {
      ProofIdKind::Local(LProofId(self.0))
    } else {
      ProofIdKind::Global(GProofId(self.0 & !(1 << 31)))
    }
  }

  fn add(self, other: u32) -> Self {
    match self.unpack() {
      ProofIdKind::Local(this) => LProofId(this.0 + other).into(),
      ProofIdKind::Global(this) => GProofId(this.0 + other).into(),
    }
  }
}

impl GProofId {
  const C0: Self = Self(0);
}

impl From<LProofId> for ProofId {
  #[inline]
  fn from(v: LProofId) -> Self { Self::Local(v) }
}
impl From<GProofId> for ProofId {
  #[inline]
  fn from(v: GProofId) -> Self { Self::Global(v) }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProofSlice(ProofId, u32);

impl ProofSlice {
  const EMPTY: Self = Self(ProofId::Global(GProofId(0)), 0);
  fn slice(self, i: u32, len: u32) -> Self {
    assert!(len <= i + self.1);
    Self(self.0.add(i), len)
  }
}

#[derive(Clone, Copy, Debug)]
pub enum TypedExprKind {
  IsObject,
  IsSet,
  Numeral,
  Var,
  Func { id: TFuncId, args: ProofSlice },
  SchFunc { args: ProofSlice },
  The,
  Proof { pf: ProofId },
}

#[derive(Clone, Copy, Debug)]
pub enum ProofKind {
  // Context constructors
  C0,
  CVar { ctx: ProofId, ty: ProofId },
  CSchFunc { ctx: ProofId, ctx2: ProofId, ty: ProofId },
  CSchPred { ctx: ProofId, ctx2: ProofId },
  CHyp { ctx: ProofId, stmt: ProofId },

  // Expr constructors
  ENumeral(u32),
  EVar { ctx: ProofId, idx: VarId },
  ESchFunc { ctx: ProofId, idx: SchFuncId, args: ProofSlice },
  EFunc { ctx: ProofId, id: FuncId, args: ProofSlice },
  EThe { ty: ProofId },
  EFraenkel { ctx: ProofId, ctx2: ProofId, scope: ProofId, compr: ProofId },

  // Formula constructors
  FTrue,
  FSchPred { ctx: ProofId, idx: SchPredId, args: ProofSlice },
  FPred { ctx: ProofId, id: PredId, args: ProofSlice },
  FIs { ctx: ProofId, term: ProofId, ty: ProofId },
  FNeg { f: ProofId },
  FAnd { ctx: ProofId, args: ProofSlice },
  FForAll { ctx2: ProofId, scope: ProofId },

  // Type constructors
  // packed representation with `args[..nargs]` being the pred args,
  // and `args[nargs..]` being the attrs
  Type { ctx: ProofId, id: PredId, args: ProofSlice, nargs: u32 },
  Attr { pos: bool, id: PredId, args: ProofSlice },

  // Proofs
  TypedExpr { kind: TypedExprKind, term: ProofId, ty: ProofId },
  VConv { stmt: ProofId, pf: ProofId },
  VExternal { stmt: ProofId, pf: OProofId },
  VAndElim { stmt: ProofId, i: u32, len: u32, pf: ProofId },
  VTrue { stmt: ProofId },
  VHyp { stmt: ProofId, ctx: ProofId, idx: HypId },
  VEqTrans { stmt: ProofId, pf1: ProofId, pf2: ProofId },

  Redirect(ProofId),
}

pub struct ProofBuilderRef<'a> {
  local: &'a IdxVec<LProofId, ProofKind>,
  local_arr: &'a Vec<ProofId>,
  global: &'a IdxVec<GProofId, ProofKind>,
  global_arr: &'a Vec<GProofId>,
}

impl<'a> ProofBuilderRef<'a> {
  fn new(
    local: &'a IdxVec<LProofId, ProofKind>, local_arr: &'a Vec<ProofId>,
    global: &'a IdxVec<GProofId, ProofKind>, global_arr: &'a Vec<GProofId>,
  ) -> Self {
    Self { local, local_arr, global, global_arr }
  }
}

macro_rules! mk_on_local_ids {
  ($d:tt $trait:ident, $func:ident$( -> $ret:ty$(:$mark:literal)?)?$(, $mutbl:tt)?) => {
    trait $trait {
      fn $func(
        self, ctx: &$($mutbl)? ProofBuilderInner,
        f: &mut impl FnMut(&$($mutbl)? ProofBuilderInner, LProofId)$(-> $ret)?
      );
    }
    impl $trait for $(&$mutbl)? ProofId {
      fn $func(
        self, ctx: &$($mutbl)? ProofBuilderInner,
        f: &mut impl FnMut(&$($mutbl)? ProofBuilderInner, LProofId)$(-> $ret)?
      ) {
        if let ProofIdKind::Local(i) = self.unpack() {
          $(*self = $($mark)?)? f(ctx, i)
        }
      }
    }
    impl $trait for ProofSlice {
      fn $func(
        self, ctx: &$($mutbl)? ProofBuilderInner,
        f: &mut impl FnMut(&$($mutbl)? ProofBuilderInner, LProofId)$(-> $ret)?
      ) {
        if let ProofIdKind::Local(i) = self.0.unpack() {
          for j in i.0..i.0 + self.1 {
            if let ProofIdKind::Local(i) = ctx.local.arr[j as usize].unpack() {
              $(ctx.local.arr[j as usize] = $($mark)?)? f(ctx, i)
            }
          }
        }
      }
    }
    impl $trait for &$($mutbl)? TypedExprKind {
      fn $func(
        self, ctx: &$($mutbl)? ProofBuilderInner,
        f: &mut impl FnMut(&$($mutbl)? ProofBuilderInner, LProofId)$(-> $ret)?
      ) {
        macro_rules! visit { ($d($d e:expr),*) => {{$d($d e.$func(ctx, f);)*}} }
        match self {
          TypedExprKind::IsObject => {}
          TypedExprKind::IsSet => {}
          TypedExprKind::Numeral => {}
          TypedExprKind::Var => {}
          TypedExprKind::Func { id: _, args } => visit!(args),
          TypedExprKind::SchFunc { args } => visit!(args),
          TypedExprKind::The => {}
          TypedExprKind::Proof { pf } => visit!(pf),
        }
      }
    }
    impl $trait for &$($mutbl)? ProofKind {
      fn $func(
        self, ctx: &$($mutbl)? ProofBuilderInner,
        f: &mut impl FnMut(&$($mutbl)? ProofBuilderInner, LProofId)$(-> $ret)?
      ) {
        macro_rules! visit { ($d ($d e:expr),*) => {{$d($d e.$func(ctx, f);)*}} }
        match self {
          ProofKind::Redirect(i) => visit!(i),
          ProofKind::C0 => {}
          ProofKind::CVar { ctx, ty } => visit!(ctx, ty),
          ProofKind::CSchFunc { ctx, ctx2, ty } => visit!(ctx, ctx2, ty),
          ProofKind::CSchPred { ctx, ctx2 } => visit!(ctx, ctx2),
          ProofKind::CHyp { ctx, stmt } => visit!(ctx, stmt),
          ProofKind::ENumeral(_) => {}
          ProofKind::EVar { ctx, idx: _ } => visit!(ctx),
          ProofKind::ESchFunc { ctx, idx: _, args } => visit!(ctx, args),
          ProofKind::EFunc { ctx, id: _, args } => visit!(ctx, args),
          ProofKind::EThe { ty } => visit!(ty),
          ProofKind::EFraenkel { ctx, ctx2, scope, compr } => visit!(ctx, ctx2, scope, compr),
          ProofKind::FTrue => {}
          ProofKind::FSchPred { ctx, idx: _, args } => visit!(ctx, args),
          ProofKind::FPred { ctx, id: _, args } => visit!(ctx, args),
          ProofKind::FIs { ctx, term, ty } => visit!(ctx, term, ty),
          ProofKind::FNeg { f: id } => visit!(id),
          ProofKind::FAnd { ctx, args } => visit!(ctx, args),
          ProofKind::FForAll { ctx2, scope } => visit!(ctx2, scope),
          ProofKind::Type { ctx, id: _, args, nargs: _ } => visit!(ctx, args),
          ProofKind::Attr { pos: _, id: _, args } => visit!(args),
          ProofKind::TypedExpr { kind: _, term, ty } => visit!(term, ty),
          ProofKind::VConv { stmt, .. }
          | ProofKind::VExternal { stmt, .. }
          | ProofKind::VAndElim { stmt, .. }
          | ProofKind::VTrue { stmt, .. }
          | ProofKind::VHyp { stmt, .. }
          | ProofKind::VEqTrans { stmt, .. } => visit!(stmt),
        }
      }
    }
  }
}
mk_on_local_ids!($OnLocalIds, on_local_ids);
mk_on_local_ids!($OnLocalIdsMut, on_local_ids_mut -> ProofId, mut);

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
enum ProofHash<'a> {
  // Context constructors
  C0,
  CVar { ctx: ProofId, ty: ProofId },
  CSchFunc { ctx: ProofId, ctx2: ProofId, ty: ProofId },
  CSchPred { ctx: ProofId, ctx2: ProofId },
  CHyp { ctx: ProofId, stmt: ProofId },

  // Expr constructors
  ENumeral(u32),
  EVar { ctx: ProofId, idx: VarId },
  ESchFunc { ctx: ProofId, idx: SchFuncId, args: &'a [ProofId] },
  EFunc { ctx: ProofId, id: FuncId, args: &'a [ProofId] },
  EThe { ty: ProofId },
  EFraenkel { ctx: ProofId, ctx2: ProofId, scope: ProofId, compr: ProofId },

  // Formula constructors
  FTrue,
  FSchPred { ctx: ProofId, idx: SchPredId, args: &'a [ProofId] },
  FPred { ctx: ProofId, id: PredId, args: &'a [ProofId] },
  FIs { ctx: ProofId, term: ProofId, ty: ProofId },
  FNeg { f: ProofId },
  FAnd { ctx: ProofId, args: &'a [ProofId] },
  FForAll { ctx2: ProofId, scope: ProofId },

  // Type constructors
  Type { ctx: ProofId, id: PredId, args: &'a [ProofId], nargs: u32 },
  Attr { pos: bool, id: PredId, args: &'a [ProofId] },

  // Proofs
  TypedExpr { expr: ProofId, ty: ProofId },
  Proof { stmt: ProofId },
}

impl<'a> ProofHash<'a> {
  #[allow(clippy::wrong_self_convention)]
  fn to_hash(&self) -> u64 {
    let mut hash = ahash::AHasher::default();
    self.hash(&mut hash);
    hash.finish()
  }
}
pub trait ProofRc: Default {
  fn inc(&self);
  fn dec(&self);
}
impl ProofRc for () {
  fn inc(&self) {}
  fn dec(&self) {}
}
impl ProofRc for Cell<u32> {
  fn inc(&self) { self.set(self.get() + 1) }
  fn dec(&self) { self.set(self.get() - 1) }
}

pub trait ProofIdx: Idx {
  type Rc: ProofRc;
  fn get(_: &ProofBuilderInner) -> &ProofArray<Self>;
  fn get_mut(_: &mut ProofBuilderInner) -> &mut ProofArray<Self>;
}
impl ProofIdx for LProofId {
  type Rc = Cell<u32>;
  fn get(p: &ProofBuilderInner) -> &ProofArray<LProofId> { &p.local }
  fn get_mut(p: &mut ProofBuilderInner) -> &mut ProofArray<LProofId> { &mut p.local }
}
impl ProofIdx for GProofId {
  type Rc = ();
  fn get(p: &ProofBuilderInner) -> &ProofArray<GProofId> { &p.global }
  fn get_mut(p: &mut ProofBuilderInner) -> &mut ProofArray<GProofId> { &mut p.global }
}

#[derive(Default)]
pub struct ProofArray<I: ProofIdx> {
  /// The second component is a reference count, which counts how many references there are to this
  /// ProofIdx later in this array, as well as in `arr` (but not other stack locals).
  vec: IdxVec<I, (ProofKind, I::Rc)>,
  arr: Vec<ProofId>,
  dedup: RefCell<RawTable<I>>,
}

impl<I: ProofIdx> ProofArray<I> {
  fn clear(&mut self) {
    self.vec.0.clear();
    self.arr.clear();
    self.dedup.get_mut().clear()
  }
}

impl<I: ProofIdx> Index<I> for ProofArray<I> {
  type Output = ProofKind;
  fn index(&self, i: I) -> &Self::Output { &self.vec[i].0 }
}
impl<I: ProofIdx> IndexMut<I> for ProofArray<I> {
  fn index_mut(&mut self, i: I) -> &mut Self::Output { &mut self.vec[i].0 }
}
impl<I: ProofIdx> Index<(I, u32)> for ProofArray<I> {
  type Output = [ProofId];
  fn index(&self, (start, len): (I, u32)) -> &Self::Output {
    &self.arr[start.into_usize()..][..len as usize]
  }
}
impl<I: ProofIdx> IndexMut<(I, u32)> for ProofArray<I> {
  fn index_mut(&mut self, (start, len): (I, u32)) -> &mut Self::Output {
    &mut self.arr[start.into_usize()..][..len as usize]
  }
}
impl<I: ProofIdx> ProofArray<I> {
  fn dealloc_slice(&mut self, start: I, len: u32) {
    if start.into_usize() + len as usize == self.arr.len() {
      self.arr.truncate(start.into_usize())
    }
  }
}

pub enum CoProof {
  Justify { stmt: ProofId },
  ExistElim { pf: ProofId, nvars: u32 },
  Assume,
}

#[derive(Default)]
pub struct ProofBuilderInner {
  local: ProofArray<LProofId>,
  /// The proofs in this array must not use any `LProofId`s
  global: ProofArray<GProofId>,
  ctx: ProofId,
  depth: u32,
  pred: IdxVec<MPredId, PredId>,
  attr: IdxVec<AttrId, PredId>,
  mode: IdxVec<ModeId, PredId>,
  struct_mode: IdxVec<StructId, PredId>,
  aggr: IdxVec<AggrId, FuncId>,
  func: IdxVec<MFuncId, (FuncId, u8)>,
  sel: IdxVec<SelId, FuncId>,
  locus_base: u32,
  bound_base: u32,
  fixed_var: IdxVec<ConstId, (ProofId, ProofId)>,
  infer_const: IdxVec<InferId, Option<ProofId>>,
  pub coproof_stack: Vec<CoProof>,
  pub thesis: ProofId,
  hyps: IdxVec<HypId, ProofId>,
}

impl Index<ProofId> for ProofBuilderInner {
  type Output = ProofKind;
  fn index(&self, i: ProofId) -> &Self::Output {
    match i.unpack() {
      ProofIdKind::Local(i) => &self.local[i],
      ProofIdKind::Global(i) => &self.global[i],
    }
  }
}
impl IndexMut<ProofId> for ProofBuilderInner {
  fn index_mut(&mut self, i: ProofId) -> &mut Self::Output {
    match i.unpack() {
      ProofIdKind::Local(i) => &mut self.local[i],
      ProofIdKind::Global(i) => &mut self.global[i],
    }
  }
}

impl Index<ProofSlice> for ProofBuilderInner {
  type Output = [ProofId];
  fn index(&self, slice: ProofSlice) -> &Self::Output {
    match slice.0.unpack() {
      ProofIdKind::Local(i) => &self.local[(i, slice.1)],
      ProofIdKind::Global(i) => &self.global[(i, slice.1)],
    }
  }
}
impl IndexMut<ProofSlice> for ProofBuilderInner {
  fn index_mut(&mut self, slice: ProofSlice) -> &mut Self::Output {
    match slice.0.unpack() {
      ProofIdKind::Local(i) => &mut self.local[(i, slice.1)],
      ProofIdKind::Global(i) => &mut self.global[(i, slice.1)],
    }
  }
}

impl ProofBuilderInner {
  pub fn ctx(&self) -> ProofId { self.ctx }

  fn dealloc_slice(&mut self, slice: ProofSlice) {
    match slice.0.unpack() {
      ProofIdKind::Local(n) => self.local.dealloc_slice(n, slice.1),
      ProofIdKind::Global(n) => self.global.dealloc_slice(n, slice.1),
    }
  }

  fn to_hash(&self, kind: &ProofKind) -> ProofHash<'_> {
    match *kind {
      ProofKind::C0 => ProofHash::C0,
      ProofKind::CVar { ctx, ty } => ProofHash::CVar { ctx, ty },
      ProofKind::CSchFunc { ctx, ctx2, ty } => ProofHash::CSchFunc { ctx, ctx2, ty },
      ProofKind::CSchPred { ctx, ctx2 } => ProofHash::CSchPred { ctx, ctx2 },
      ProofKind::CHyp { ctx, stmt } => ProofHash::CHyp { ctx, stmt },
      ProofKind::ENumeral(n) => ProofHash::ENumeral(n),
      ProofKind::EVar { ctx, idx } => ProofHash::EVar { ctx, idx },
      ProofKind::ESchFunc { ctx, idx, args } => ProofHash::ESchFunc { ctx, idx, args: &self[args] },
      ProofKind::EFunc { ctx, id, args } => ProofHash::EFunc { ctx, id, args: &self[args] },
      ProofKind::EThe { ty } => ProofHash::EThe { ty },
      ProofKind::EFraenkel { ctx, ctx2, scope, compr } =>
        ProofHash::EFraenkel { ctx, ctx2, scope, compr },
      ProofKind::FTrue => ProofHash::FTrue,
      ProofKind::FSchPred { ctx, idx, args } => ProofHash::FSchPred { ctx, idx, args: &self[args] },
      ProofKind::FPred { ctx, id, args } => ProofHash::FPred { ctx, id, args: &self[args] },
      ProofKind::FIs { ctx, term, ty } => ProofHash::FIs { ctx, term, ty },
      ProofKind::FNeg { f } => ProofHash::FNeg { f },
      ProofKind::FAnd { ctx, args } => ProofHash::FAnd { ctx, args: &self[args] },
      ProofKind::FForAll { ctx2, scope } => ProofHash::FForAll { ctx2, scope },
      ProofKind::Type { ctx, id, args, nargs } =>
        ProofHash::Type { ctx, id, args: &self[args], nargs },
      ProofKind::Attr { pos, id, args } => ProofHash::Attr { pos, id, args: &self[args] },
      ProofKind::TypedExpr { term: expr, ty, .. } => ProofHash::TypedExpr { expr, ty },
      ProofKind::VConv { stmt, .. }
      | ProofKind::VExternal { stmt, .. }
      | ProofKind::VAndElim { stmt, .. }
      | ProofKind::VTrue { stmt, .. }
      | ProofKind::VHyp { stmt, .. }
      | ProofKind::VEqTrans { stmt, .. } => ProofHash::Proof { stmt },
      ProofKind::Redirect(n) => self.to_hash(&self[n]),
    }
  }

  fn get1<I: ProofIdx>(&self, key: ProofHash<'_>) -> Option<I> {
    let arr = I::get(self);
    let hash = key.to_hash();
    arr.dedup.borrow().get(hash, |&p| key == self.to_hash(&arr[p])).copied()
  }

  fn insert1<I: ProofIdx>(&mut self, kind: &ProofKind) -> I {
    let key = self.to_hash(kind);
    let arr = I::get(self);
    let hash = key.to_hash();
    if let Some(&p) = arr.dedup.borrow().get(hash, |&p| key == self.to_hash(&arr[p])) {
      return p
    }
    self.inc_ref(kind);
    let i = I::get_mut(self).vec.push((*kind, I::Rc::default()));
    let arr = I::get(self);
    *arr.dedup.borrow_mut().insert_entry(hash, i, |&k| self.to_hash(&arr[k]).to_hash())
  }

  fn get(&mut self, key: ProofHash<'_>) -> Option<ProofId> {
    match self.get1(key) {
      Some(n) => Some(GProofId::into(n)),
      None => self.get1(key).map(LProofId::into),
    }
  }

  fn insert(&mut self, kind: ProofKind) -> ProofId {
    let key = self.to_hash(&kind);
    match self.get1(key) {
      Some(n) => GProofId::into(n),
      None => LProofId::into(self.insert1(&kind)),
    }
  }

  fn push_globalized_inner(&mut self, mut kind: ProofKind) -> GProofId {
    kind.on_local_ids_mut(self, &mut |this, i| {
      let (ProofKind::Redirect(j), ref rc) = this.local.vec[i] else { unreachable!() };
      let ProofIdKind::Global(j) = j.unpack() else { unreachable!() };
      rc.set(rc.get() - 1);
      j.into()
    });
    self.insert1(&kind)
  }

  fn globalize_many(&mut self, stack: &mut Vec<LProofId>) {
    while let Some(&i) = stack.last() {
      let n = stack.len();
      self.local[i].on_local_ids(self, &mut |this, i| {
        if !matches!(this.local.vec[i].0, ProofKind::Redirect(_)) {
          stack.push(i)
        }
      });
      if stack.len() == n {
        stack.pop();
        let key = self.to_hash(&self.local[i]);
        let hash = key.to_hash();
        let arr = LProofId::get(self);
        arr.dedup.borrow_mut().remove_entry(hash, |&p| key == self.to_hash(&arr[p]));
        let j = self.push_globalized_inner(self.local[i]);
        self.local[i] = ProofKind::Redirect(j.into());
        let key = self.to_hash(&self.global[j]);
        let arr = LProofId::get(self);
        let hash = key.to_hash();
        let mut dedup = arr.dedup.borrow_mut();
        if dedup.find(hash, |&p| key == self.to_hash(&arr[p])).is_none() {
          dedup.insert(hash, i, |&k| self.to_hash(&arr[k]).to_hash());
        }
      }
    }
  }

  fn push_globalized(&mut self, kind: ProofKind) -> GProofId {
    let mut stack = vec![];
    kind.on_local_ids(self, &mut |_, i| stack.push(i));
    self.globalize_many(&mut stack);
    self.push_globalized_inner(kind)
  }

  fn globalize(&mut self, id: ProofId) -> GProofId {
    match id.unpack() {
      ProofIdKind::Global(i) => i,
      ProofIdKind::Local(i) => {
        let mut stack = vec![];
        self.local[i].on_local_ids(self, &mut |_, i| stack.push(i));
        self.globalize_many(&mut stack);
        let j = self.push_globalized_inner(self.local[i]);
        self.local[i] = ProofKind::Redirect(j.into());
        j
      }
    }
  }

  fn dec_ref(&self, t: impl OnLocalIds) {
    t.on_local_ids(self, &mut |_, i| self.local.vec[i].1.dec());
  }
  fn inc_ref(&self, t: impl OnLocalIds) {
    t.on_local_ids(self, &mut |_, i| self.local.vec[i].1.inc());
  }

  pub fn alloc_slice(&mut self, local_scope: bool, vec: &mut [ProofId]) -> ProofSlice {
    if vec.is_empty() {
      ProofSlice::EMPTY
    } else if local_scope {
      let n = self.local.arr.len();
      self.local.arr.extend_from_slice(vec);
      ProofSlice(LProofId(n as u32).into(), vec.len() as u32)
    } else {
      vec.iter_mut().for_each(|i| *i = self.globalize(*i).into());
      let n = self.global.arr.len();
      self.global.arr.extend_from_slice(vec);
      ProofSlice(GProofId(n as u32).into(), vec.len() as u32)
    }
  }

  pub fn copy_slice(&mut self, local_scope: bool, slice: ProofSlice) -> ProofSlice {
    if slice.1 == 0 {
      ProofSlice::EMPTY
    } else if local_scope {
      let n = self.local.arr.len();
      match slice.0.unpack() {
        ProofIdKind::Local(i) =>
          self.local.arr.extend_from_within(i.0 as usize..i.0 as usize + slice.1 as usize),
        ProofIdKind::Global(i) => self.local.arr.extend_from_slice(&self.global[(i, slice.1)]),
      }
      ProofSlice(LProofId(n as u32).into(), slice.1)
    } else {
      let n = self.global.arr.len();
      match slice.0.unpack() {
        ProofIdKind::Local(i) =>
          for j in 0..slice.1 {
            let val = self.globalize(self.local.arr[(i.0 + j) as usize]);
            self.global.arr.push(val.into());
          },
        ProofIdKind::Global(i) =>
          self.global.arr.extend_from_within(i.0 as usize..i.0 as usize + slice.1 as usize),
      }
      ProofSlice(GProofId(n as u32).into(), slice.1)
    }
  }

  fn concl(&self, pf: ProofId) -> ProofId {
    if pf == ProofId::INVALID {
      return ProofId::INVALID
    }
    match self[pf] {
      ProofKind::VConv { stmt, .. }
      | ProofKind::VExternal { stmt, .. }
      | ProofKind::VAndElim { stmt, .. }
      | ProofKind::VTrue { stmt, .. }
      | ProofKind::VHyp { stmt, .. }
      | ProofKind::VEqTrans { stmt, .. } => stmt,
      ProofKind::Redirect(id) => self.concl(id),
      ProofKind::C0 { .. }
      | ProofKind::CVar { .. }
      | ProofKind::CSchFunc { .. }
      | ProofKind::CSchPred { .. }
      | ProofKind::CHyp { .. }
      | ProofKind::ENumeral { .. }
      | ProofKind::EVar { .. }
      | ProofKind::ESchFunc { .. }
      | ProofKind::EFunc { .. }
      | ProofKind::EThe { .. }
      | ProofKind::EFraenkel { .. }
      | ProofKind::FTrue { .. }
      | ProofKind::FSchPred { .. }
      | ProofKind::FPred { .. }
      | ProofKind::FIs { .. }
      | ProofKind::FNeg { .. }
      | ProofKind::FAnd { .. }
      | ProofKind::FForAll { .. }
      | ProofKind::Type { .. }
      | ProofKind::Attr { .. }
      | ProofKind::TypedExpr { .. } => unreachable!(),
    }
  }

  pub fn and_elim(&mut self, pf: ProofId, i: u32, len: u32) -> ProofId {
    match self[self.concl(pf)] {
      ProofKind::FTrue => {
        assert!(i == 0 && len == 0);
        pf
      }
      _ if len == 0 => {
        let stmt = self.insert(ProofKind::FTrue);
        self.insert(ProofKind::VTrue { stmt })
      }
      ProofKind::FAnd { ctx, args } => {
        assert!(i + len <= args.1);
        let stmt = if len == 1 {
          args.0.add(i)
        } else {
          let sub = self.copy_slice(true, args.slice(i, len));
          self.insert(ProofKind::FAnd { ctx, args: sub })
        };
        self.insert(ProofKind::VAndElim { stmt, i, len, pf })
      }
      _ => {
        assert!(i == 0 && len == 1);
        pf
      }
    }
  }

  fn neg(&mut self, f: ProofId) -> ProofId {
    match self[f] {
      ProofKind::FNeg { f } => f,
      _ => self.insert(ProofKind::FNeg { f }),
    }
  }

  fn insert_args(
    &mut self, local_scope: bool, args: &mut [ProofId],
    hash: impl FnOnce(&[ProofId]) -> ProofHash<'_>, mk: impl FnOnce(ProofSlice) -> ProofKind,
  ) -> ProofId {
    let key = hash(args);
    if let Some(n) = self.get(key) {
      n
    } else {
      let kind = mk(self.alloc_slice(local_scope, args));
      self.insert(kind)
    }
  }

  pub fn assume(&mut self, stmt: ProofId) -> ProofId {
    self.ctx = self.insert(ProofKind::CHyp { ctx: self.ctx, stmt });
    let hyp = self.hyps.push(stmt);
    self.insert(ProofKind::VHyp { stmt, ctx: self.ctx, idx: hyp })
  }

  pub fn read_reconsider(&mut self, fixed_var: &IdxVec<ConstId, FixedVar>, pf: ProofId) {
    for (i, var) in fixed_var.0[self.fixed_var.len()..].iter().enumerate() {
      let pf = self.and_elim(pf, i as u32, 1);
      let ProofKind::FIs { term, ty, .. } = self[self.concl(pf)] else { unreachable!() };
      let pf = self.insert(ProofKind::TypedExpr { kind: TypedExprKind::Proof { pf }, term, ty });
      self.fixed_var.push((term, pf));
    }
  }

  pub fn intro(&mut self, ctx2: ProofId) {
    self.ctx = ctx2;
    let ProofKind::CVar { ctx, ty } = self[ctx2] else { unreachable!() };
    let term = self.insert(ProofKind::EVar { ctx: ctx2, idx: VarId(self.depth) });
    let pf = self.insert(ProofKind::TypedExpr { kind: TypedExprKind::Var, term, ty });
    self.depth += 1;
    self.fixed_var.push((term, pf));
  }
}

macro_rules! mk_insert {
  ($(fn $name:ident$([ctx$($ctx:literal)?])?($($id:ident: $ty:ty),*) = $v:ident;)*) => {
    impl ProofBuilderInner {
      $(
        fn $name(
          &mut self, local_scope: bool, $($id: $ty,)* args: &mut [ProofId],
        ) -> ProofId {
          $(let ctx = self.ctx; $($ctx)?)?
          self.insert_args(
            local_scope,
            args,
            |args| ProofHash::$v { $(ctx, $($ctx)?)? $($id,)* args },
            |args| ProofKind::$v { $(ctx, $($ctx)?)? $($id,)* args },
          )
        }
      )*
    }
  }
}
mk_insert! {
  fn insert_attr(pos: bool, id: PredId) = Attr;
  fn insert_sch_func[ctx](idx: SchFuncId) = ESchFunc;
  fn insert_func[ctx](id: FuncId) = EFunc;
  fn insert_type[ctx](id: PredId, nargs: u32) = Type;
  fn insert_pred[ctx](id: PredId) = FPred;
  fn insert_sch_pred[ctx](idx: SchPredId) = FSchPred;
  fn insert_and[ctx]() = FAnd;
}

struct Translate<'a> {
  inner: &'a mut ProofBuilderInner,
  infer_const: &'a IdxVec<InferId, Assignment>,
  local_scope: bool,
  buf: Vec<ProofId>,
}

impl Translate<'_> {
  fn tr_func(&mut self, (id, superfluous): (FuncId, u8), args: &[Term]) -> ProofId {
    let args = &args[superfluous as usize..];
    let start = self.tr_push_terms(args);
    let out = self.inner.insert_func(self.local_scope, id, &mut self.buf[start..]);
    self.buf.truncate(start);
    out
  }

  fn tr_term(&mut self, tm: &Term) -> ProofId {
    match tm {
      Term::Numeral(n) => self.inner.insert(ProofKind::ENumeral(*n)),
      Term::Locus(n) => self.inner.insert(ProofKind::EVar {
        ctx: self.inner.ctx,
        idx: VarId(n.0 as u32 + self.inner.locus_base),
      }),
      Term::Bound(n) => self
        .inner
        .insert(ProofKind::EVar { ctx: self.inner.ctx, idx: VarId(n.0 + self.inner.bound_base) }),
      Term::Const(n) => self.inner.fixed_var[*n].0,
      &Term::Infer(n) => match self.inner.infer_const.get_mut_extending(n) {
        Some(val) => *val,
        None => {
          let val = self.tr_term(&self.infer_const[n].def);
          self.inner.infer_const[n] = Some(val);
          val
        }
      },
      Term::SchFunc { nr, args } => {
        let start = self.tr_push_terms(args);
        let out = self.inner.insert_sch_func(self.local_scope, *nr, &mut self.buf[start..]);
        self.buf.truncate(start);
        out
      }
      Term::Aggregate { nr, args } => self.tr_func((self.inner.aggr[*nr], 0), args),
      Term::PrivFunc { nr, args, value } => self.tr_term(value),
      Term::Functor { nr, args } => self.tr_func(self.inner.func[*nr], args),
      Term::Selector { nr, args } => self.tr_func((self.inner.sel[*nr], 0), args),
      Term::The { ty } => {
        let ty = self.tr_type(ty);
        self.inner.insert(ProofKind::EThe { ty })
      }
      Term::Fraenkel { args, scope, compr } => {
        let base = (self.inner.ctx, self.inner.depth);
        for (_, ty) in &**args {
          let ty = self.tr_type(ty);
          self.inner.ctx = self.inner.insert(ProofKind::CVar { ctx: self.inner.ctx, ty });
          self.inner.depth += 1;
        }
        let scope = self.tr_term(scope);
        let compr = self.tr_formula(compr);
        let tm = self.inner.insert(ProofKind::EFraenkel {
          ctx: base.0,
          ctx2: self.inner.ctx,
          scope,
          compr,
        });
        (self.inner.ctx, self.inner.depth) = base;
        tm
      }
      Term::Qua { value, .. } => self.tr_term(value),
      Term::EqClass(_) | Term::EqMark(_) | Term::FreeVar(_) | Term::It => unreachable!(),
    }
  }

  fn tr_push_terms(&mut self, tms: &[Term]) -> usize {
    let start = self.buf.len();
    for tm in tms {
      let tm = self.tr_term(tm);
      self.buf.push(tm);
    }
    start
  }

  fn tr_attr(&mut self, attr: &Attr) -> ProofId {
    let start = self.tr_push_terms(&attr.args);
    let id = self.inner.attr[attr.nr];
    let out = self.inner.insert_attr(self.local_scope, attr.pos, id, &mut self.buf[start..]);
    self.buf.truncate(start);
    out
  }

  fn tr_type(&mut self, ty: &Type) -> ProofId {
    let start = self.tr_push_terms(&ty.args);
    let id = match ty.kind {
      TypeKind::Struct(id) => self.inner.struct_mode[id],
      TypeKind::Mode(id) => self.inner.mode[id],
    };
    let nargs = ty.args.len() as u32;
    let Attrs::Consistent(attrs) = &ty.attrs.0 else { unreachable!() };
    for attr in attrs {
      let attr = self.tr_attr(attr);
      self.buf.push(attr);
    }
    let out = self.inner.insert_type(self.local_scope, id, nargs, &mut self.buf[start..]);
    self.buf.truncate(start);
    out
  }

  fn tr_pred(&mut self, id: PredId, args: &[Term]) -> ProofId {
    let start = self.tr_push_terms(args);
    let out = self.inner.insert_pred(self.local_scope, id, &mut self.buf[start..]);
    self.buf.truncate(start);
    out
  }

  fn tr_formula(&mut self, f: &Formula) -> ProofId {
    match f {
      Formula::SchPred { nr, args } => {
        let start = self.tr_push_terms(args);
        let out = self.inner.insert_sch_pred(self.local_scope, *nr, &mut self.buf[start..]);
        self.buf.truncate(start);
        out
      }
      Formula::Pred { nr, args } => self.tr_pred(self.inner.pred[*nr], args),
      Formula::Attr { nr, args } => self.tr_pred(self.inner.attr[*nr], args),
      Formula::PrivPred { nr, args, value } => self.tr_formula(value),
      Formula::Is { term, ty } => {
        let term = self.tr_term(term);
        let ty = self.tr_type(ty);
        self.inner.insert(ProofKind::FIs { ctx: self.inner.ctx, term, ty })
      }
      Formula::Neg { f } => {
        let f = self.tr_formula(f);
        self.inner.insert(ProofKind::FNeg { f })
      }
      Formula::And { args } => {
        let start = self.buf.len();
        for f in args {
          let f = self.tr_formula(f);
          self.buf.push(f);
        }
        let out = self.inner.insert_and(self.local_scope, &mut self.buf[start..]);
        self.buf.truncate(start);
        out
      }
      Formula::ForAll { id: _, dom, scope } => {
        let ty = self.tr_type(dom);
        let ctx = self.inner.ctx;
        self.inner.ctx = self.inner.insert(ProofKind::CVar { ctx, ty });
        self.inner.depth += 1;
        let scope = self.tr_formula(scope);
        let f = self.inner.insert(ProofKind::FForAll { ctx2: self.inner.ctx, scope });
        self.inner.ctx = ctx;
        self.inner.depth -= 1;
        f
      }
      Formula::FlexAnd { nat, le, terms, scope } =>
        self.tr_formula(&crate::Global::expand_flex_and(
          nat.clone(),
          *le,
          (**terms).clone(),
          scope.clone(),
          self.inner.depth,
        )),
      Formula::LegacyFlexAnd { expansion, .. } => self.tr_formula(expansion),
      Formula::True => self.inner.insert(ProofKind::FTrue),
    }
  }
}

pub struct ProofBuilder<W> {
  local_scope: bool,
  inner: RefCell<ProofBuilderInner>,
  w: ProofWriter<W>,
}

pub struct OptProofBuilder<W>(pub Option<Box<ProofBuilder<W>>>);

impl<W> Default for OptProofBuilder<W> {
  fn default() -> Self { Self(None) }
}

impl<W: WriteProof> OptProofBuilder<W> {
  pub fn init(&mut self, w: W) { assert!(self.0.replace(Box::new(ProofBuilder::new(w))).is_none()) }

  #[inline]
  fn with<R: Default>(&self, f: impl FnOnce(&ProofBuilder<W>) -> R) -> R {
    match &self.0 {
      Some(p) => f(p),
      None => Default::default(),
    }
  }
  #[inline]
  pub fn with_mut<R: Default>(&mut self, f: impl FnOnce(&mut ProofBuilder<W>) -> R) -> R {
    match &mut self.0 {
      Some(p) => f(p),
      None => Default::default(),
    }
  }

  #[inline]
  pub fn inner_mut<R: Default>(&mut self, f: impl FnOnce(&mut ProofBuilderInner) -> R) -> R {
    self.with_mut(|p| f(p.inner.get_mut()))
  }

  pub fn finish(&mut self) {
    if let Some(p) = &mut self.0 {
      p.w.w.finish().unwrap()
    }
  }
}

impl<W> ProofBuilder<W> {
  pub fn inner(&mut self) -> &mut ProofBuilderInner { self.inner.get_mut() }

  pub fn push(&self, kind: ProofKind) -> ProofId {
    if self.local_scope {
      self.inner.borrow_mut().insert(kind)
    } else {
      self.inner.borrow_mut().push_globalized(kind).into()
    }
  }

  pub fn alloc_slice(&self, vec: &mut [ProofId]) -> ProofSlice {
    self.inner.borrow_mut().alloc_slice(self.local_scope, vec)
  }

  fn tr<R: Default>(&mut self, lc: &LocalContext, f: impl FnOnce(&mut Translate<'_>) -> R) -> R {
    f(&mut Translate {
      inner: self.inner.get_mut(),
      local_scope: self.local_scope,
      buf: vec![],
      infer_const: &lc.infer_const.borrow(),
    })
  }
  pub fn tr_term(&mut self, lc: &LocalContext, tm: &Term) -> ProofId {
    self.tr(lc, |tr| tr.tr_term(tm))
  }
  pub fn tr_type(&mut self, lc: &LocalContext, ty: &Type) -> ProofId {
    self.tr(lc, |tr| tr.tr_type(ty))
  }
  pub fn tr_formula(&mut self, lc: &LocalContext, f: &Formula) -> ProofId {
    self.tr(lc, |tr| tr.tr_formula(f))
  }

  pub fn tr_formula_with_empty_ctx(&mut self, lc: &LocalContext, f: &Formula) -> ProofId {
    self.tr(lc, |tr| {
      let ctx = tr.inner.ctx;
      tr.inner.ctx = ProofId::C0;
      let f = tr.tr_formula(f);
      tr.inner.ctx = ctx;
      f
    })
  }

  pub fn set_local_scope(&mut self, local: bool) -> bool {
    let old = self.local_scope;
    self.local_scope = local;
    if !local {
      self.inner.get_mut().local.clear();
    }
    old
  }

  pub fn def_const(&mut self, fixed_var: &IdxVec<ConstId, FixedVar>, pf: ProofId) -> ProofId {
    let inner = self.inner.get_mut();
    if self.local_scope {
      let nvars = (fixed_var.len() - inner.fixed_var.len()) as u32;
      let mut stmt = inner.neg(inner.concl(pf));
      for (i, var) in fixed_var.0[inner.fixed_var.len()..].iter().enumerate() {
        let ProofKind::FForAll { ctx2, scope } = inner[stmt] else { unreachable!() };
        inner.intro(ctx2);
        stmt = scope;
      }
      let stmt = inner.neg(stmt);
      inner.coproof_stack.push(CoProof::ExistElim { pf, nvars });
      inner.assume(stmt)
    } else {
      panic!("TODO: consider at top level")
    }
  }

  pub fn eq_trans(&mut self, pf1: ProofId, pf2: ProofId) -> ProofId {
    let inner = self.inner.get_mut();
    let ProofKind::FPred { id, args, .. } = inner[inner.concl(pf1)] else { unreachable!() };
    let ProofKind::FPred { args: args2, .. } = inner[inner.concl(pf2)] else { unreachable!() };
    let stmt = inner.insert_pred(self.local_scope, id, &mut [inner[args][0], inner[args2][1]]);
    inner.insert(ProofKind::VEqTrans { stmt, pf1, pf2 })
  }

  pub fn start_block(&mut self) {}

  pub fn finish_with_thesis_block(&mut self) -> ProofId { todo!() }
}

impl<W: WriteProof> ProofBuilder<W> {
  pub fn new(w: W) -> Self {
    let mut inner = ProofBuilderInner { ctx: ProofId::C0, ..Default::default() };
    inner.insert1::<GProofId>(&ProofKind::C0);
    Self { local_scope: false, inner: RefCell::new(inner), w: ProofWriter::new(w) }
  }

  pub fn maybe_externalize(&mut self, local: bool, push: bool, pf: ProofId) -> ProofId {
    if local {
      return pf
    }
    let inner = self.inner.get_mut();
    let out = self.w.output(inner, true, push, pf).unwrap();
    ProofId::Global(inner.insert1(&ProofKind::VExternal { stmt: inner.concl(pf), pf: out }))
  }

  /// Writes the given step to the output. Returns the id of the step, if available.
  /// * If `def = true` then the result is always valid
  /// * If `push = true` then the result is also pushed to the top of the stack
  pub fn output(&mut self, def: bool, push: bool, id: ProofId) -> OProofId {
    self.w.output(self.inner.get_mut(), def, push, id).unwrap_or_default()
  }

  pub fn step(&mut self, step: Step) { self.w.w.write_step(step).unwrap() }
}
