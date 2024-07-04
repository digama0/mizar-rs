use super::{
  FuncId, GProofId, HypId, LProofId, PredId, ProofBuilderInner, ProofId, ProofIdKind, ProofKind,
  ProofRc, ProofSlice, TFuncId, VarId,
};
use crate::proof::TypedExprKind;
use crate::types::{FuncId as MFuncId, PredId as MPredId, *};
use crate::write::MizWriter;
use crate::{mk_id, MizPath};
use hashbrown::raw::RawTable;
use hashbrown::{HashMap, HashSet};
use std::cell::{Cell, RefCell};
use std::fs::File;
use std::hash::{Hash, Hasher};
use std::io::{self, BufWriter, Write};
use std::ops::{Index, IndexMut};

mk_id! {
  OProofId(u32),
}
pub struct ProofWriter<W> {
  local_out: HashMap<LProofId, OProofId>,
  global_out: HashMap<GProofId, OProofId>,
  out_num: OProofId,
  pub pred_num: PredId,
  pub func_num: FuncId,
  pub w: W,
}

impl OProofId {
  const C0: Self = Self(0);
  const INVALID: Self = Self(u32::MAX);
}

impl<W: WriteProof> ProofWriter<W> {
  pub fn new(mut w: W) -> Self {
    let mut this = Self {
      local_out: Default::default(),
      global_out: Default::default(),
      out_num: Default::default(),
      pred_num: Default::default(),
      func_num: Default::default(),
      w,
    };
    this.global_out.insert(GProofId::C0, OProofId::C0);
    this.out_num.0 += 1;
    this.w.write_step(Step::C0).unwrap();
    this
  }

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
      ProofKind::CHyp { ctx, stmt } => {
        let ctx = self.output(inner, true, false, ctx).unwrap();
        self.output(inner, false, true, stmt);
        self.w.write_step(Step::CHyp { ctx }).unwrap();
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
      ProofKind::FIs { ctx, term, ty } => {
        self.output(inner, false, true, term);
        self.output(inner, false, true, ty);
        self.w.write_step(Step::FIs).unwrap();
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
      ProofKind::Type { ctx: _, id, args, nargs } => {
        self.push_slice(inner, args);
        self.w.write_step(Step::Type { id, attrs: args.1 - nargs }).unwrap();
      }
      ProofKind::Attr { pos, id, args } => {
        self.push_slice(inner, args);
        self.w.write_step(Step::Attr { pos, id }).unwrap();
      }
      ProofKind::TypedExpr { kind, term, ty } => {
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
          TypedExprKind::Proof { pf } => return self.output(inner, def, push, pf),
        };
        self.output(inner, false, true, term);
        self.output(inner, false, true, ty);
        self.w.write_step(step).unwrap();
      }
      ProofKind::Redirect(i) => return self.output(inner, def, push, i),
      ProofKind::VConv { stmt, pf } => {
        self.output(inner, false, true, pf);
        self.output(inner, false, true, stmt);
        self.w.write_step(Step::VConv).unwrap();
      }
      ProofKind::VExternal { stmt: _, pf } => {
        if push {
          self.w.write_step(Step::Ref(pf));
        }
        return Some(pf)
      }
      ProofKind::VAndElim { stmt: _, i, len, pf } => {
        self.output(inner, false, true, pf);
        self.w.write_step(Step::VAndElim { i, len }).unwrap();
      }
      ProofKind::VTrue { stmt: _ } => self.w.write_step(Step::VTrue).unwrap(),
      ProofKind::VHyp { stmt: _, ctx, idx } => {
        let ctx = self.output(inner, true, false, ctx).unwrap();
        self.w.write_step(Step::VHyp { ctx, idx }).unwrap();
      }
      ProofKind::VEqTrans { stmt: _, pf1, pf2 } => {
        self.output(inner, false, true, pf1);
        self.output(inner, false, true, pf2);
        self.w.write_step(Step::VEqTrans).unwrap();
      }
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
  pub fn output(
    &mut self, inner: &ProofBuilderInner, def: bool, push: bool, id: ProofId,
  ) -> Option<OProofId> {
    if id == ProofId::INVALID {
      if push {
        self.w.write_step(Step::Invalid);
      }
      return Some(OProofId::INVALID)
    }
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
    for &id in &inner[slice] {
      self.output(inner, false, true, id);
    }
  }
}

#[derive(Debug)]
pub enum PredName {
  Mode(Article, ModeId),
  Struct(Article, StructId),
  Attr(Article, AttrId),
  Pred(Article, MPredId),
}

impl std::fmt::Display for PredName {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      PredName::Mode(art, n) => write!(f, "{art}:mode {}", n.0),
      PredName::Struct(art, n) => write!(f, "{art}:struct {}", n.0),
      PredName::Attr(art, n) => write!(f, "{art}:attr {}", n.0),
      PredName::Pred(art, n) => write!(f, "{art}:pred {}", n.0),
    }
  }
}

#[derive(Debug)]
pub enum FuncName {
  Func(Article, MFuncId),
  Sel(Article, SelId),
  Aggr(Article, AggrId),
}

impl std::fmt::Display for FuncName {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      FuncName::Func(art, n) => write!(f, "{art}:func {}", n.0),
      FuncName::Sel(art, n) => write!(f, "{art}:sel {}", n.0),
      FuncName::Aggr(art, n) => write!(f, "{art}:aggr {}", n.0),
    }
  }
}

#[derive(Debug)]
pub enum TFuncName {
  Func(Article, MFuncId),
}

impl std::fmt::Display for TFuncName {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      TFuncName::Func(art, n) => write!(f, "{art}:func {}", n.0),
    }
  }
}

#[derive(Debug)]
pub enum Step {
  Ref(OProofId),
  Def { push: bool },
  // Context constructors
  C0,
  CVar { ctx: OProofId },
  CSchFunc { ctx: OProofId, ctx2: OProofId },
  CSchPred { ctx: OProofId, ctx2: OProofId },
  CHyp { ctx: OProofId },

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
  FIs,
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

  VConv,
  VAndElim { i: u32, len: u32 },
  VTrue,
  VHyp { ctx: OProofId, idx: HypId },
  VEqTrans,

  Theorem,
  Scheme,

  LoadPred { name: PredName, req: Option<Requirement> },
  LoadFunc { name: FuncName, req: Option<Requirement> },
  LoadTFunc { name: TFuncName },

  Invalid,
}

pub trait WriteProof {
  fn write_step(&mut self, step: Step) -> std::io::Result<()>;

  fn finish(&mut self) -> std::io::Result<()> { Ok(()) }
}

impl WriteProof for () {
  fn write_step(&mut self, step: Step) -> std::io::Result<()> {
    eprintln!("step: {step:?}");
    Ok(())
  }
}

pub struct XmlProofWriter<W: Write = BufWriter<File>> {
  w: MizWriter<W>,
  out: OProofId,
  pred: PredId,
  func: FuncId,
  tfunc: TFuncId,
}

impl XmlProofWriter {
  pub fn new(path: &MizPath) -> io::Result<Self> {
    let mut w = path.create_xml(true, false, "ppf")?;
    w.start("Proof");
    Ok(XmlProofWriter {
      w,
      out: Default::default(),
      pred: Default::default(),
      func: Default::default(),
      tfunc: Default::default(),
    })
  }
}

impl<W: Write> WriteProof for XmlProofWriter<W> {
  fn write_step(&mut self, step: Step) -> std::io::Result<()> {
    match step {
      Step::Ref(i) => self.w.with_attr("Ref", |e| e.attr_str(b"id", i.0)),
      Step::Def { push: false } =>
        self.w.with_attr("Def", |w| w.attr_str(b"self", self.out.fresh().0)),
      Step::Def { push: true } =>
        self.w.with_attr("Save", |w| w.attr_str(b"self", self.out.fresh().0)),
      Step::C0 => self.w.with_attr("C0", |w| w.attr_str(b"self", self.out.fresh().0)),
      Step::CVar { ctx } => self.w.with_attr("CVar", |w| {
        w.attr_str(b"self", self.out.fresh().0);
        w.attr_str(b"parent", ctx.0)
      }),
      Step::CSchFunc { ctx, ctx2 } => self.w.with_attr("CSchFunc", |w| {
        w.attr_str(b"self", self.out.fresh().0);
        w.attr_str(b"parent", ctx.0);
        w.attr_str(b"val", ctx2.0)
      }),
      Step::CSchPred { ctx, ctx2 } => self.w.with_attr("CSchPred", |w| {
        w.attr_str(b"self", self.out.fresh().0);
        w.attr_str(b"parent", ctx.0);
        w.attr_str(b"val", ctx2.0)
      }),
      Step::CHyp { ctx } => self.w.with_attr("CHyp", |w| {
        w.attr_str(b"self", self.out.fresh().0);
        w.attr_str(b"parent", ctx.0)
      }),
      Step::ENumeral(n) => self.w.with_attr("ENumeral", |w| w.attr_str(b"nr", n)),
      Step::EVar { ctx, idx } => self.w.with_attr("EVar", |w| {
        w.attr_str(b"ctx", ctx.0);
        w.attr_str(b"nr", idx.0)
      }),
      Step::ESchFunc { ctx, idx } => self.w.with_attr("ESchFunc", |w| {
        w.attr_str(b"ctx", ctx.0);
        w.attr_str(b"nr", idx.0)
      }),
      Step::EFunc { ctx, id } => self.w.with_attr("EFunc", |w| {
        w.attr_str(b"ctx", ctx.0);
        w.attr_str(b"id", id.0)
      }),
      Step::EThe => self.w.with0("EThe", |_| {}),
      Step::EFraenkel { ctx, ctx2 } => self.w.with_attr("EFraenkel", |w| {
        w.attr_str(b"ctx", ctx.0);
        w.attr_str(b"args", ctx2.0)
      }),
      Step::FTrue => self.w.with0("FTrue", |_| {}),
      Step::FSchPred { ctx, idx } => self.w.with_attr("FSchPred", |w| {
        w.attr_str(b"ctx", ctx.0);
        w.attr_str(b"nr", idx.0)
      }),
      Step::FPred { id } => self.w.with_attr("FPred", |w| w.attr_str(b"id", id.0)),
      Step::FIs => self.w.with0("FIs", |_| {}),
      Step::FNeg => self.w.with0("FNeg", |_| {}),
      Step::FAnd { len } => self.w.with_attr("FAnd", |w| w.attr_str(b"sz", len)),
      Step::FForAll { ctx2 } => self.w.with_attr("FForAll", |w| {
        w.attr_str(b"args", ctx2.0);
      }),
      Step::Type { id, attrs } => self.w.with_attr("Type", |w| {
        w.attr_str(b"id", id.0);
        w.attr_str(b"attrs", attrs)
      }),
      Step::Attr { pos: true, id } => self.w.with_attr("Attr", |w| w.attr_str(b"id", id.0)),
      Step::Attr { pos: false, id } => self.w.with_attr("NegAttr", |w| w.attr_str(b"id", id.0)),
      Step::VEIsObject => self.w.with0("VEIsObject", |_| {}),
      Step::VEIsSet => self.w.with0("VEIsSet", |_| {}),
      Step::VENumeral => self.w.with0("VENumeral", |_| {}),
      Step::VEVar => self.w.with0("VEVar", |_| {}),
      Step::VEFunc { id } => self.w.with_attr("VEFunc", |w| w.attr_str(b"id", id.0)),
      Step::VESchFunc => self.w.with0("VESchFunc", |_| {}),
      Step::VEThe => self.w.with0("VEThe", |_| {}),
      Step::VConv => self.w.with0("VConv", |_| {}),
      Step::VAndElim { i, len } => self.w.with_attr("VAndElim", |w| {
        w.attr_str(b"idx", i);
        w.attr_str(b"len", len)
      }),
      Step::VTrue => self.w.with0("VTrue", |_| {}),
      Step::VHyp { ctx, idx } => self.w.with_attr("VAndElim", |w| {
        w.attr_str(b"ctx", ctx.0);
        w.attr_str(b"idx", idx.0)
      }),
      Step::VEqTrans => self.w.with0("VEqTrans", |_| {}),
      Step::Theorem => self.w.with0("Theorem", |_| {}),
      Step::Scheme => self.w.with0("Scheme", |_| {}),
      Step::LoadPred { name, req } => self.w.with_attr("LoadPred", |w| {
        w.attr_str(b"self", self.pred.fresh().0);
        w.attr_str(b"name", format!("{name}"));
        if let Some(req) = req {
          w.attr_str(b"req", format!("{req:?}"))
        }
      }),
      Step::LoadFunc { name, req } => self.w.with_attr("LoadFunc", |w| {
        w.attr_str(b"self", self.func.fresh().0);
        w.attr_str(b"name", format!("{name}"));
        if let Some(req) = req {
          w.attr_str(b"req", format!("{req:?}"))
        }
      }),
      Step::LoadTFunc { name } => self.w.with_attr("LoadTFunc", |w| {
        w.attr_str(b"self", self.tfunc.fresh().0);
        w.attr_str(b"name", format!("{name}"))
      }),
      Step::Invalid => self.w.with0("Invalid", |_| {}),
    }
    Ok(())
  }

  fn finish(&mut self) -> std::io::Result<()> {
    self.w.end_tag("Proof");
    self.w.finish();
    Ok(())
  }
}
