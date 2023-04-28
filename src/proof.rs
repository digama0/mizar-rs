#![allow(unused)]
use crate::mk_id;
use crate::types::*;
use hashbrown::raw::RawTable;
use hashbrown::{HashMap, HashSet};
use std::cell::{Cell, RefCell};
use std::hash::{Hash, Hasher};
use std::ops::{Index, IndexMut};

mk_id! {
  FuncId(u32),
  TFuncId(u32),
  PredId(u32),
  VarId(u32),
  GProofId(u32),
  LProofId(u32),
  OProofId(u32),
}

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

impl ProofId {
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

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ProofSlice(ProofId, u32);

impl ProofSlice {
  const EMPTY: Self = Self(ProofId::Global(GProofId(0)), 0);
}

#[derive(Clone, Copy)]
pub enum TypedExprKind {
  IsObject,
  IsSet,
  Numeral,
  Var,
  Func { id: TFuncId, args: ProofSlice },
  SchFunc { args: ProofSlice },
  The,
}

#[derive(Clone, Copy)]
pub enum ProofKind {
  // Context constructors
  C0,
  CVar { ctx: ProofId, ty: ProofId },
  CSchFunc { ctx: ProofId, ctx2: ProofId, ty: ProofId },
  CSchPred { ctx: ProofId, ctx2: ProofId },

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
  FNeg { f: ProofId },
  FAnd { ctx: ProofId, args: ProofSlice },
  FForAll { ctx2: ProofId, scope: ProofId },

  // Type constructors
  // packed representation with `packed[..nargs]` being the pred args,
  // and `packed[nargs..]` being the attrs
  Type { ctx: ProofId, id: PredId, packed: ProofSlice, nargs: u32 },
  Attr { pos: bool, id: PredId, args: ProofSlice },

  // Proofs
  VExpr { kind: TypedExprKind, expr: ProofId, ty: ProofId },

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
          ProofKind::ENumeral(_) => {}
          ProofKind::EVar { ctx, idx: _ } => visit!(ctx),
          ProofKind::ESchFunc { ctx, idx: _, args } => visit!(ctx, args),
          ProofKind::EFunc { ctx, id: _, args } => visit!(ctx, args),
          ProofKind::EThe { ty } => visit!(ty),
          ProofKind::EFraenkel { ctx, ctx2, scope, compr } => visit!(ctx, ctx2, scope, compr),
          ProofKind::FTrue => {}
          ProofKind::FSchPred { ctx, idx: _, args } => visit!(ctx, args),
          ProofKind::FPred { ctx, id: _, args } => visit!(ctx, args),
          ProofKind::FNeg { f: id } => visit!(id),
          ProofKind::FAnd { ctx, args } => visit!(ctx, args),
          ProofKind::FForAll { ctx2, scope } => visit!(ctx2, scope),
          ProofKind::Type { ctx, id: _, packed, nargs: _ } => visit!(ctx, packed),
          ProofKind::Attr { pos: _, id: _, args } => visit!(args),
          ProofKind::VExpr { kind, expr, ty } => visit!(kind, expr, ty),
        }
      }
    }
  }
}
mk_on_local_ids!($OnLocalIds, on_local_ids);
mk_on_local_ids!($OnLocalIdsMut, on_local_ids_mut -> ProofId, mut);

#[derive(Hash, PartialEq, Eq)]
enum ProofHash<'a> {
  // Context constructors
  C0,
  CVar { ctx: ProofId, ty: ProofId },
  CSchFunc { ctx: ProofId, ctx2: ProofId, ty: ProofId },
  CSchPred { ctx: ProofId, ctx2: ProofId },

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
  FNeg { f: ProofId },
  FAnd { ctx: ProofId, args: &'a [ProofId] },
  FForAll { ctx2: ProofId, scope: ProofId },

  // Type constructors
  Type { ctx: ProofId, id: PredId, packed: &'a [ProofId] },
  Attr { pos: bool, id: PredId, args: &'a [ProofId] },

  // Proofs
  TypedExpr { expr: ProofId, ty: ProofId },
}

impl<'a> ProofHash<'a> {
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

impl<I: ProofIdx> Index<I> for ProofArray<I> {
  type Output = ProofKind;
  fn index(&self, i: I) -> &Self::Output { &self.vec[i].0 }
}
impl<I: ProofIdx> IndexMut<I> for ProofArray<I> {
  fn index_mut(&mut self, i: I) -> &mut Self::Output { &mut self.vec[i].0 }
}
impl<I: ProofIdx> ProofArray<I> {
  fn dealloc_slice(&mut self, start: I, len: u32) {
    if start.into_usize() + len as usize == self.arr.len() {
      self.arr.truncate(start.into_usize())
    }
  }
  fn to_slice_hash(&self, start: I, len: u32) -> &[ProofId] {
    &self.arr[start.into_usize()..][..len as usize]
  }
}

#[derive(Default)]
pub struct ProofBuilderInner {
  local: ProofArray<LProofId>,
  /// The proofs in this array must not use any `LProofId`s
  global: ProofArray<GProofId>,
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

impl ProofBuilderInner {
  fn dealloc_slice(&mut self, slice: ProofSlice) {
    match slice.0.unpack() {
      ProofIdKind::Local(n) => self.local.dealloc_slice(n, slice.1),
      ProofIdKind::Global(n) => self.global.dealloc_slice(n, slice.1),
    }
  }

  fn to_slice(&self, slice: ProofSlice) -> &[ProofId] {
    match slice.0.unpack() {
      ProofIdKind::Local(i) => self.local.to_slice_hash(i, slice.1),
      ProofIdKind::Global(i) => self.global.to_slice_hash(i, slice.1),
    }
  }

  fn to_hash(&self, kind: &ProofKind) -> ProofHash<'_> {
    macro_rules! h {
      ($e:expr) => {
        self.to_slice($e)
      };
    }
    match *kind {
      ProofKind::C0 => ProofHash::C0,
      ProofKind::CVar { ctx, ty } => ProofHash::CVar { ctx, ty },
      ProofKind::CSchFunc { ctx, ctx2, ty } => ProofHash::CSchFunc { ctx, ctx2, ty },
      ProofKind::CSchPred { ctx, ctx2 } => ProofHash::CSchPred { ctx, ctx2 },
      ProofKind::ENumeral(n) => ProofHash::ENumeral(n),
      ProofKind::EVar { ctx, idx } => ProofHash::EVar { ctx, idx },
      ProofKind::ESchFunc { ctx, idx, args } => ProofHash::ESchFunc { ctx, idx, args: h!(args) },
      ProofKind::EFunc { ctx, id, args } => ProofHash::EFunc { ctx, id, args: h!(args) },
      ProofKind::EThe { ty } => ProofHash::EThe { ty },
      ProofKind::EFraenkel { ctx, ctx2, scope, compr } =>
        ProofHash::EFraenkel { ctx, ctx2, scope, compr },
      ProofKind::FTrue => ProofHash::FTrue,
      ProofKind::FSchPred { ctx, idx, args } => ProofHash::FSchPred { ctx, idx, args: h!(args) },
      ProofKind::FPred { ctx, id, args } => ProofHash::FPred { ctx, id, args: h!(args) },
      ProofKind::FNeg { f } => ProofHash::FNeg { f },
      ProofKind::FAnd { ctx, args } => ProofHash::FAnd { ctx, args: h!(args) },
      ProofKind::FForAll { ctx2, scope } => ProofHash::FForAll { ctx2, scope },
      ProofKind::Type { ctx, id, packed, nargs: _ } =>
        ProofHash::Type { ctx, id, packed: h!(packed) },
      ProofKind::Attr { pos, id, args } => ProofHash::Attr { pos, id, args: h!(args) },
      ProofKind::VExpr { expr, ty, .. } => ProofHash::TypedExpr { expr, ty },
      ProofKind::Redirect(n) => self.to_hash(&self[n]),
    }
  }

  fn get1<I: ProofIdx>(&self, kind: &ProofKind) -> Option<I> {
    let key = self.to_hash(kind);
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

  fn insert(&mut self, key: &ProofKind) -> ProofId {
    match self.get1(key) {
      Some(n) => GProofId::into(n),
      None => LProofId::into(self.insert1(key)),
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
      self.local[i].on_local_ids(self, &mut |_, i| stack.push(i));
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
    if local_scope {
      let n = self.local.arr.len();
      self.local.arr.extend_from_slice(vec);
      ProofSlice(LProofId(n as u32).into(), vec.len() as u32)
    } else {
      vec.iter_mut().for_each(|i| *i = self.globalize(*i).into());
      let n = self.global.arr.len();
      self.local.arr.extend_from_slice(vec);
      ProofSlice(GProofId(n as u32).into(), vec.len() as u32)
    }
  }
}

pub struct ProofBuilder<W> {
  local_scope: bool,
  inner: RefCell<ProofBuilderInner>,
  w: ProofWriter<W>,
}

impl<W> ProofWriter<W> {
  fn new(w: W) -> Self {
    Self {
      local_out: Default::default(),
      global_out: Default::default(),
      out_num: Default::default(),
      w,
    }
  }
}
pub struct ProofWriter<W> {
  local_out: HashMap<LProofId, OProofId>,
  global_out: HashMap<GProofId, OProofId>,
  out_num: OProofId,
  w: W,
}

impl<W> ProofBuilder<W> {
  pub fn new(w: W) -> Self {
    let mut inner = ProofBuilderInner { local: Default::default(), global: Default::default() };
    inner.insert1::<GProofId>(&ProofKind::C0);
    Self { local_scope: false, inner: RefCell::new(inner), w: ProofWriter::new(w) }
  }

  pub fn push(&self, kind: ProofKind) -> ProofId {
    if self.local_scope {
      self.inner.borrow_mut().insert(&kind)
    } else {
      self.inner.borrow_mut().push_globalized(kind).into()
    }
  }

  pub fn alloc_slice(&self, vec: &mut [ProofId]) -> ProofSlice {
    self.inner.borrow_mut().alloc_slice(self.local_scope, vec)
  }
}

impl<W: WriteProof> ProofWriter<W> {
  fn output_uncached(
    &mut self, inner: &ProofBuilderInner, def: bool, push: bool, kind: ProofKind,
  ) -> Option<OProofId> {
    debug_assert!(def || push);
    let mut def_step = false;
    match kind {
      ProofKind::C0 => {
        self.w.write_step(Step::C0).unwrap();
        def_step = true
      }
      ProofKind::CVar { ctx, ty } => {
        let ctx = self.output(inner, true, false, ctx).unwrap();
        self.output(inner, false, true, ty);
        self.w.write_step(Step::CVar { ctx }).unwrap();
        def_step = true
      }
      ProofKind::CSchFunc { ctx, ctx2, ty } => {
        let ctx = self.output(inner, true, false, ctx).unwrap();
        let ctx2 = self.output(inner, true, false, ctx2).unwrap();
        self.output(inner, false, true, ty);
        self.w.write_step(Step::CSchFunc { ctx, ctx2 }).unwrap();
        def_step = true
      }
      ProofKind::CSchPred { ctx, ctx2 } => {
        let ctx = self.output(inner, true, false, ctx).unwrap();
        let ctx2 = self.output(inner, true, false, ctx2).unwrap();
        self.w.write_step(Step::CSchPred { ctx, ctx2 }).unwrap();
        def_step = true
      }
      ProofKind::ENumeral(n) => self.w.write_step(Step::ENumeral(n)).unwrap(),
      ProofKind::EVar { ctx, idx } => {
        let ctx = self.output(inner, true, false, ctx).unwrap();
        self.w.write_step(Step::EVar { ctx, idx }).unwrap();
      }
      ProofKind::ESchFunc { ctx, idx, args } => {
        let ctx = self.output(inner, true, false, ctx).unwrap();
        self.w.write_step(Step::ESchFunc { ctx, idx }).unwrap();
      }
      ProofKind::EFunc { ctx, id, args } => {
        let ctx = self.output(inner, true, false, ctx).unwrap();
        self.push_slice(inner, args);
        self.w.write_step(Step::EFunc { ctx, id }).unwrap();
      }
      ProofKind::EThe { ty } => {
        self.output(inner, false, true, ty);
        self.w.write_step(Step::EThe).unwrap();
      }
      ProofKind::EFraenkel { ctx, ctx2, scope, compr } => {
        let ctx = self.output(inner, true, false, ctx).unwrap();
        let ctx2 = self.output(inner, true, false, ctx2).unwrap();
        self.output(inner, false, true, scope);
        self.output(inner, false, true, compr);
        self.w.write_step(Step::EFraenkel { ctx, ctx2 }).unwrap();
      }
      ProofKind::FTrue => self.w.write_step(Step::FTrue).unwrap(),
      ProofKind::FSchPred { ctx, idx, args } => {
        let ctx = self.output(inner, true, false, ctx).unwrap();
        self.push_slice(inner, args);
        self.w.write_step(Step::FSchPred { ctx, idx }).unwrap();
      }
      ProofKind::FPred { ctx: _, id, args } => {
        self.push_slice(inner, args);
        self.w.write_step(Step::FPred { id }).unwrap();
      }
      ProofKind::FNeg { f } => {
        self.output(inner, false, true, f);
        self.w.write_step(Step::FNeg).unwrap();
      }
      ProofKind::FAnd { ctx: _, args } => {
        self.push_slice(inner, args);
        self.w.write_step(Step::FAnd { len: args.1 }).unwrap();
      }
      ProofKind::FForAll { ctx2, scope } => {
        let ctx2 = self.output(inner, true, false, ctx2).unwrap();
        self.output(inner, false, true, scope);
        self.w.write_step(Step::FForAll { ctx2 }).unwrap();
      }
      ProofKind::Type { ctx: _, id, packed, nargs } => {
        self.push_slice(inner, packed);
        self.w.write_step(Step::Type { id, attrs: packed.1 - nargs }).unwrap();
      }
      ProofKind::Attr { pos, id, args } => {
        self.push_slice(inner, args);
        self.w.write_step(Step::Attr { pos, id }).unwrap();
      }
      ProofKind::VExpr { kind, expr, ty } => {
        let step = match kind {
          TypedExprKind::IsObject => Step::VEIsObject,
          TypedExprKind::IsSet => Step::VEIsSet,
          TypedExprKind::Numeral => Step::VENumeral,
          TypedExprKind::Var => Step::VEVar,
          TypedExprKind::Func { id, args } => {
            self.push_slice(inner, args);
            Step::VEFunc { id }
          }
          TypedExprKind::SchFunc { args } => {
            self.push_slice(inner, args);
            Step::VESchFunc
          }
          TypedExprKind::The => Step::VEThe,
        };
        self.output(inner, false, true, expr);
        self.output(inner, false, true, ty);
        self.w.write_step(step).unwrap();
      }
      ProofKind::Redirect(i) => return self.output(inner, def, push, i),
    }
    if def_step {
      let n = self.out_num.fresh();
      if push {
        self.w.write_step(Step::Ref(n));
      }
      return Some(n)
    }
    if def {
      self.w.write_step(Step::Def { push }).unwrap();
      return Some(self.out_num.fresh())
    }
    None
  }

  /// Writes the given step to the output. Returns the id of the step, if available.
  /// * If `def = true` then the result is always `Some`
  /// * If `push = true` then the result is also pushed to the top of the stack
  fn output(
    &mut self, inner: &ProofBuilderInner, def: bool, push: bool, id: ProofId,
  ) -> Option<OProofId> {
    match id.unpack() {
      ProofIdKind::Local(i) =>
        if let Some(&j) = self.local_out.get(&i) {
          if push {
            self.w.write_step(Step::Ref(j));
          }
          Some(j)
        } else {
          let (pf, ref rc) = inner.local.vec[i];
          let rc_val = rc.get();
          inner.dec_ref(&pf);
          let j = self.output_uncached(inner, rc_val != 0 || def, push, pf)?;
          inner.inc_ref(&pf);
          inner.local.vec[i].1.inc();
          self.local_out.insert(i, j);
          Some(j)
        },
      ProofIdKind::Global(i) =>
        if let Some(&j) = self.global_out.get(&i) {
          if push {
            self.w.write_step(Step::Ref(j)).unwrap();
          }
          Some(j)
        } else {
          let j = self.output_uncached(inner, true, push, inner.global[i]).unwrap();
          self.global_out.insert(i, j);
          Some(j)
        },
    }
  }

  fn push_slice(&mut self, inner: &ProofBuilderInner, slice: ProofSlice) {
    for &id in inner.to_slice(slice) {
      self.output(inner, false, true, id);
    }
  }
}

pub enum Step {
  Ref(OProofId),
  Def { push: bool },
  // Context constructors
  C0,
  CVar { ctx: OProofId },
  CSchFunc { ctx: OProofId, ctx2: OProofId },
  CSchPred { ctx: OProofId, ctx2: OProofId },

  // Expr constructors
  ENumeral(u32),
  EVar { ctx: OProofId, idx: VarId },
  ESchFunc { ctx: OProofId, idx: SchFuncId },
  EFunc { ctx: OProofId, id: FuncId },
  EThe,
  EFraenkel { ctx: OProofId, ctx2: OProofId },

  // Formula constructors
  FTrue,
  FSchPred { ctx: OProofId, idx: SchPredId },
  FPred { id: PredId },
  FNeg,
  FAnd { len: u32 },
  FForAll { ctx2: OProofId },

  // Type constructors
  Type { id: PredId, attrs: u32 },
  Attr { pos: bool, id: PredId },

  // Proofs
  VEIsObject,
  VEIsSet,
  VENumeral,
  VEVar,
  VEFunc { id: TFuncId },
  VESchFunc,
  VEThe,

  Theorem,
}

pub trait WriteProof {
  fn write_step(&mut self, step: Step) -> std::io::Result<()>;
}
