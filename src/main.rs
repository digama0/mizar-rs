#![allow(clippy::needless_range_loop)]
#![allow(unused)]

use crate::types::*;
use crate::verify::Verifier;
use enum_map::EnumMap;
use itertools::EitherOrBoth;
use once_cell::sync::Lazy;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fs::File;
use std::io;
use std::iter::Peekable;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicU32};
use std::sync::Mutex;

mod parser;
mod types;
mod verify;

static MIZFILES: Lazy<PathBuf> = Lazy::new(|| {
  std::env::var_os("MIZFILES").expect("MIZFILES environment variable is not set").into()
});
static PREL: Lazy<PathBuf> = Lazy::new(|| MIZFILES.join("prel"));

pub struct MizPath(Article, PathBuf);

// fn get_mml_article(article: &str) -> MizPath {
//   let mut path = PREL.join(&article[..1]);
//   path.push(article);
//   MizPath(path)
// }

impl MizPath {
  fn new(s: &str) -> Self {
    Self(Article::from_bytes(s.as_bytes()), format!("../mizshare/mml/{}", s).into())
  }

  fn open(&self, ext: &str) -> io::Result<File> {
    let mut path = self.1.clone();
    path.set_extension(ext);
    File::open(path)
  }
}

const MAX_FUNC_NUM: usize = 1500;

pub struct RequirementIndexes {
  fwd: EnumMap<Requirement, u32>,
  rev: [Option<Requirement>; MAX_FUNC_NUM],
}

impl Default for RequirementIndexes {
  fn default() -> Self { Self { fwd: Default::default(), rev: [None; MAX_FUNC_NUM] } }
}

impl std::fmt::Debug for RequirementIndexes {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.fwd.fmt(f) }
}

impl RequirementIndexes {
  pub fn init_rev(&mut self) {
    for (req, &val) in &self.fwd {
      self.rev[val as usize] = Some(req);
    }
  }

  pub fn get(&self, req: Requirement) -> Option<u32> { self.fwd[req].checked_sub(1) }

  pub fn any(&self) -> ModeId { ModeId(self.get(Requirement::Any).unwrap()) }
  pub fn set(&self) -> ModeId { ModeId(self.get(Requirement::SetMode).unwrap()) }
  pub fn zero(&self) -> Option<AttrId> { self.get(Requirement::Zero).map(AttrId) }
  pub fn element(&self) -> Option<ModeId> { self.get(Requirement::Element).map(ModeId) }
  pub fn omega(&self) -> Option<FuncId> { self.get(Requirement::Omega).map(FuncId) }
  pub fn positive(&self) -> Option<AttrId> { self.get(Requirement::Positive).map(AttrId) }
  pub fn equals_to(&self) -> Option<PredId> { self.get(Requirement::EqualsTo).map(PredId) }
  pub fn mk_eq(&self, t1: Term, t2: Term) -> Formula {
    Formula::Pred { nr: self.equals_to().unwrap(), args: Box::new([t1, t2]) }
  }
}

impl Global {
  /// TypReachable(fWider = wider, fNarrower = narrower)
  fn type_reachable(&self, wider: &Type, narrower: &Type) -> bool {
    // vprintln!("TypReachable {wider:?} -> {narrower:?}");
    if let (TypeKind::Mode(_), TypeKind::Mode(w_mode)) = (narrower.kind, wider.kind) {
      if w_mode == self.reqs.any() {
        return true
      }
      let mode = self.constrs.mode[w_mode].redefines.unwrap_or(w_mode);
      let mut narrower = narrower;
      while let TypeKind::Mode(n_mode) = narrower.kind {
        if n_mode < mode {
          return false
        }
        if n_mode == mode {
          return true
        }
        let cnst = &self.constrs.mode[n_mode];
        if cnst.redefines == Some(mode) {
          return true
        }
        narrower = &cnst.ty;
      }
      false
    } else {
      true
    }
  }

  fn round_up_clusters(&mut self, lc: &mut LocalContext) {
    for k in 0..self.clusters.registered.len() {
      let mut cl = &self.clusters.registered[k];
      for l in 0..cl.primary.len() {
        lc.load_locus_tys(&cl.primary);
        let mut attrs = cl.primary[l].attrs.1.clone();
        attrs.round_up_with(self, lc, &cl.primary[l]);
        self.clusters.registered[k].primary[l].attrs.1 = attrs;
        cl = &self.clusters.registered[k];
        lc.unload_locus_tys();
      }
      lc.load_locus_tys(&cl.primary);
      let mut attrs = cl.consequent.1.clone();
      attrs.round_up_with(self, lc, &cl.ty);
      self.clusters.registered[k].consequent.1 = attrs;
      lc.unload_locus_tys();
    }

    for k in 0..self.clusters.functor.len() {
      let mut cl = &self.clusters.functor[k];
      lc.load_locus_tys(&cl.primary);
      let mut attrs = cl.consequent.1.clone();
      let ty = match &cl.ty {
        None => cl.term.round_up_type(self, lc),
        Some(ty) => CowBox::Borrowed(&**ty),
      };
      attrs.enlarge_by(&self.constrs, &ty.attrs.1, |a| a.clone());
      attrs.round_up_with(self, lc, &ty);
      self.clusters.functor[k].consequent.1 = attrs;
      lc.unload_locus_tys();
    }

    macro_rules! round_up_constrs {
      ($($x:ident),*) => {$(
        for k in 0..self.constrs.$x.0.len() {
          self.constrs.$x.0[k].ty.attrs.1 = self.constrs.$x.0[k].round_up(self, lc);
        }
      )*};
    }
    // TODO: why not round up aggregate too? (copied from original source)
    round_up_constrs! { mode, functor, selector };
    lc.term_cache.borrow_mut().terms = vec![];
    self.rounded_up_clusters = true;
  }
}

fn sorted_subset<T: Ord>(a: &[T], b: &[T]) -> bool {
  if b.len() < a.len() {
    return false
  }
  let mut it = b.iter();
  'a: for i in a {
    for j in it.by_ref() {
      match j.cmp(i) {
        Ordering::Less => {}
        Ordering::Equal => continue 'a,
        Ordering::Greater => break,
      }
    }
    return false
  }
  true
}

impl Attr {
  pub fn adjusted_nr(&self, ctx: &Constructors) -> AttrId {
    ctx.attribute[self.nr].c.redefines.unwrap_or(self.nr)
  }

  fn adjust(&self, ctx: &Constructors) -> (AttrId, &[Term]) {
    let c = &ctx.attribute[self.nr].c;
    match c.redefines {
      Some(nr) => (nr, &self.args[c.superfluous as usize..]),
      None => (self.nr, &self.args),
    }
  }

  fn cmp_abs(&self, ctx: &Constructors, other: &Self, style: CmpStyle) -> Ordering {
    let (n1, args1) = self.adjust(ctx);
    let (n2, args2) = other.adjust(ctx);
    n1.cmp(&n2).then_with(|| Term::cmp_list(ctx, args1, args2, style))
  }

  fn cmp(&self, ctx: &Constructors, other: &Self, style: CmpStyle) -> Ordering {
    self.cmp_abs(ctx, other, style).then_with(|| self.pos.cmp(&other.pos))
  }

  fn inst(&self, subst: &[Term], base: u32, depth: u32) -> Self {
    Self { nr: self.nr, pos: self.pos, args: Term::inst_list(&self.args, subst, base, depth) }
  }
}

#[derive(Copy, Clone)]
enum CmpStyle {
  Strict,
  Red,
  Alt,
}

impl Term {
  fn adjust<'a>(n: FuncId, args: &'a [Term], ctx: &Constructors) -> (FuncId, &'a [Term]) {
    let c = &ctx.functor[n].c;
    match c.redefines {
      Some(nr) => (nr, &args[c.superfluous as usize..]),
      None => (n, args),
    }
  }

  fn skip_priv_func(&self) -> &Self {
    let mut t = self;
    while let Term::PrivFunc { value, .. } = t {
      t = value
    }
    t
  }

  /// SizeOfTrm(fTrm:TrmPtr)
  fn size(&self) -> u32 {
    match self {
      Term::SchemeFunctor { args, .. }
      | Term::Aggregate { args, .. }
      | Term::Functor { args, .. }
      | Term::Selector { args, .. } => args.iter().map(|t| t.size()).sum::<u32>() + 1,
      Term::PrivFunc { value, .. } => value.size(),
      Term::Qua { value, ty } => value.size() + ty.size(),
      Term::Choice { ty } => ty.size(),
      // Term::Fraenkel { .. } => {} // FIXME?
      _ => 1,
    }
  }

  /// * CmpStyle::Strict: CompTrms(fTrm1 = self, fTrm2 = other)
  /// * CmpStyle::Red: CompRdTrms(fTrm1 = self, fTrm2 = other)
  /// * CmpStyle::Alt: CompareTrms(fTrm1 = self, fTrm2 = other)
  fn cmp(&self, ctx: &Constructors, other: &Term, style: CmpStyle) -> Ordering {
    use Term::*;
    let (this, other) = match style {
      CmpStyle::Strict => (self, other),
      CmpStyle::Red => (self.skip_priv_func(), other.skip_priv_func()),
      CmpStyle::Alt => {
        match self.size().cmp(&other.size()) {
          Ordering::Equal => {}
          o => return o,
        }
        (self.skip_priv_func(), other.skip_priv_func())
      }
    };
    this.discr().cmp(&other.discr()).then_with(|| match (this, other) {
      (Locus { nr: LocusId(n1) }, Locus { nr: LocusId(n2) })
      | (Bound { nr: BoundId(n1) }, Bound { nr: BoundId(n2) })
      | (Constant { nr: ConstantId(n1) }, Constant { nr: ConstantId(n2) })
      | (Infer { nr: InferId(n1) }, Infer { nr: InferId(n2) })
      | (FreeVar { nr: n1 }, FreeVar { nr: n2 })
      | (LambdaVar { nr: n1 }, LambdaVar { nr: n2 })
      | (EqConst { nr: n1 }, EqConst { nr: n2 })
      | (Numeral { nr: n1 }, Numeral { nr: n2 }) => n1.cmp(n2),
      (Functor { nr: n1, args: args1 }, Functor { nr: n2, args: args2 }) => match style {
        CmpStyle::Strict | CmpStyle::Alt =>
          n1.cmp(n2).then_with(|| Term::cmp_list(ctx, args1, args2, style)),
        CmpStyle::Red => {
          let (n1, args1) = Term::adjust(*n1, args1, ctx);
          let (n2, args2) = Term::adjust(*n2, args2, ctx);
          n1.cmp(&n2).then_with(|| Term::cmp_list(ctx, args1, args2, style))
        }
      },
      (
        SchemeFunctor { nr: SchFuncId(n1), args: args1 },
        SchemeFunctor { nr: SchFuncId(n2), args: args2 },
      )
      | (Aggregate { nr: AggrId(n1), args: args1 }, Aggregate { nr: AggrId(n2), args: args2 })
      | (
        PrivFunc { nr: PrivFuncId(n1), args: args1, .. },
        PrivFunc { nr: PrivFuncId(n2), args: args2, .. },
      )
      | (Selector { nr: SelId(n1), args: args1 }, Selector { nr: SelId(n2), args: args2 }) =>
        n1.cmp(n2).then_with(|| Term::cmp_list(ctx, args1, args2, style)),
      (Choice { ty: ty1 }, Choice { ty: ty2 }) => ty1.cmp(ctx, ty2, style),
      (
        Fraenkel { args: args1, scope: sc1, compr: c1 },
        Fraenkel { args: args2, scope: sc2, compr: c2 },
      ) => sc1.cmp(ctx, sc2, style).then_with(|| {
        c1.cmp(ctx, c2, style)
          .then_with(|| cmp_list(args1, args2, |ty1, ty2| ty1.1.cmp(ctx, &ty2.1, style)))
      }),
      (It, It) => Ordering::Equal,
      (Qua { value: val1, ty: ty1 }, Qua { value: val2, ty: ty2 }) =>
        val1.cmp(ctx, val2, style).then_with(|| ty1.cmp(ctx, ty2, style)),
      _ => unreachable!(),
    })
  }

  fn cmp_list(ctx: &Constructors, tms1: &[Term], tms2: &[Term], style: CmpStyle) -> Ordering {
    cmp_list(tms1, tms2, |tm1, tm2| tm1.cmp(ctx, tm2, style))
  }
}

struct WideningStruct<'a> {
  g: &'a Global,
  stack: Vec<Option<&'a Type>>,
  tgt: StructId,
}

impl<'a> WideningStruct<'a> {
  fn new(g: &'a Global, tgt: StructId) -> Self { Self { g, stack: vec![], tgt } }

  fn widening_path(&mut self, n: StructId) -> bool {
    let c = &self.g.constrs.struct_mode[n];
    let pos = self.stack.len();
    self.stack.push(None);
    for ty in &*c.prefixes {
      let n = ty.struct_id();
      if n == self.tgt {
        self.stack[pos] = Some(ty);
        return true
      }
      if self.widening_path(n) {
        self.stack[pos] = Some(ty);
        return true
      }
    }
    self.stack.pop();
    false
  }
}

fn cmp_list<T>(a: &[T], b: &[T], mut cmp: impl FnMut(&T, &T) -> Ordering) -> Ordering {
  assert!(a.len() == b.len());
  for (a, b) in a.iter().zip(b) {
    match cmp(a, b) {
      Ordering::Equal => {}
      o => return o,
    }
  }
  Ordering::Equal
}

impl Type {
  fn adjust<'a>(n: ModeId, args: &'a [Term], ctx: &Constructors) -> (ModeId, &'a [Term]) {
    let c = &ctx.mode[n].c;
    match c.redefines {
      Some(mode) => (mode, &args[c.superfluous as usize..]),
      None => (n, args),
    }
  }

  fn cmp(&self, ctx: &Constructors, other: &Type, style: CmpStyle) -> Ordering {
    self.kind.cmp(&other.kind).then_with(|| {
      let o = self.attrs.0.cmp(ctx, &other.attrs.0, style);
      o.then_with(|| Term::cmp_list(ctx, &self.args, &other.args, style))
    })
  }

  fn cmp_list(ctx: &Constructors, tys1: &[Type], tys2: &[Type], style: CmpStyle) -> Ordering {
    cmp_list(tys1, tys2, |ty1, ty2| ty1.cmp(ctx, ty2, style))
  }

  fn inst(&self, subst: &[Term], base: u32, depth: u32) -> Self {
    Self {
      kind: self.kind,
      attrs: (self.attrs.0.inst(subst, base, depth), self.attrs.1.inst(subst, base, depth)),
      args: Term::inst_list(&self.args, subst, base, depth),
    }
  }

  /// SizeOfTyp(fTyp:TypPtr)
  fn size(&self) -> u32 { self.args.iter().map(|t| t.size()).sum::<u32>() + 1 }

  /// TypObj.DecreasingAttrs but with f flipped
  fn decreasing_attrs(&self, other: &Self, f: impl FnMut(&Attr, &Attr) -> bool) -> bool {
    matches!(&other.attrs.0, Attrs::Consistent(attrs) if attrs.is_empty())
      || other.attrs.0.is_subset_of(&self.attrs.1, f)
  }

  /// TypObj.Widening
  fn widening(&self, g: &Global) -> Option<Box<Self>> {
    match self.kind {
      TypeKind::Mode(n) => {
        if n == g.reqs.any() {
          return None
        }
        let cnst = &g.constrs.mode[n];
        let mut ty = Box::new(cnst.ty.inst(&self.args, 0, 0));
        ty.attrs.1 = self.attrs.1.clone_allowed(&g.constrs, n, &self.args);
        Some(ty)
      }
      TypeKind::Struct(_) => Some(Box::new(Type {
        kind: g.reqs.set().into(), // should be any()?
        attrs: Default::default(),
        args: Default::default(),
      })),
    }
  }

  /// TypObj.WidenToStruct
  /// postcondition: the returned type has kind Struct
  fn widen_to_struct(&self, g: &Global) -> Option<Box<Self>> {
    let mut ty = Box::new(self.clone());
    while let TypeKind::Mode(_) = ty.kind {
      ty = ty.widening(g)?
    }
    Some(ty)
  }

  /// TypObj.WideningOf
  fn widening_of<'a>(&self, g: &Global, from: &'a Type) -> Option<CowBox<'a, Self>> {
    match self.kind {
      TypeKind::Mode(n) => {
        let (n, _) = Type::adjust(n, &self.args, &g.constrs);
        let mut ty = CowBox::Borrowed(from);
        loop {
          match ty.kind {
            TypeKind::Mode(n2) if n2 >= n => {
              if n2 == n {
                return Some(ty)
              }
              let cnst = &g.constrs.mode[n2];
              if cnst.redefines == Some(n) {
                return Some(ty)
              }
              ty = CowBox::Owned(ty.widening(g)?);
            }
            TypeKind::Struct(_) if n == g.reqs.set() =>
              return Some(CowBox::Owned(Box::new(Type::new(g.reqs.set().into())))),
            TypeKind::Struct(_) if n == g.reqs.any() =>
              return Some(CowBox::Owned(Box::new(Type::new(g.reqs.any().into())))),
            _ => return None,
          }
        }
      }
      TypeKind::Struct(tgt) => {
        let mut ty = from.widen_to_struct(g)?;
        let n = ty.struct_id();
        if tgt == n {
          return Some(CowBox::Owned(ty))
        }
        let c = &g.constrs.struct_mode[tgt];
        if c.fields.is_empty() || !sorted_subset(&c.fields, &g.constrs.struct_mode[n].fields) {
          return None
        }
        let mut widening = WideningStruct::new(g, tgt);
        if !widening.widening_path(n) {
          return None
        }
        for ty2 in widening.stack {
          ty = Box::new(ty2.unwrap().inst(&ty.args, 0, 0));
        }
        Some(CowBox::Owned(ty))
      }
    }
  }

  /// TypObj.IsWiderThan
  fn is_wider_than(&self, g: &Global, lc: &LocalContext, other: &Self) -> bool {
    if !other.decreasing_attrs(self, |a1, a2| ().eq_attr(g, lc, a1, a2)) {
      return false
    }
    match self.kind {
      TypeKind::Mode(n) => {
        let (n, args) = Type::adjust(n, &self.args, &g.constrs);
        let mut w = CowBox::Borrowed(other);
        loop {
          let TypeKind::Mode(n2) = w.kind else { break };
          let true = n2 >= n else { break };
          if ().eq_radices(g, lc, self, &w) {
            return true
          }
          let Some(w2) = w.widening(g) else { break };
          w = CowBox::Owned(w2)
        }
        matches!(w.kind, TypeKind::Struct(_)) && (n == g.reqs.set() || n == g.reqs.any())
      }
      TypeKind::Struct(_) => {
        let Some(w) = other.widening(g) else { return false };
        ().eq_radices(g, lc, self, &w)
      }
    }
  }

  fn round_up_with_self(&mut self, g: &Global, lc: &LocalContext) {
    // vprintln!("[{:?}] round_up_with_self {:?}", lc.infer_const.borrow().len(), self);
    let mut attrs = self.attrs.1.clone();
    attrs.round_up_with(g, lc, self);
    self.attrs.1 = attrs;
    // vprintln!("[{:?}] round_up_with_self -> {:?}", lc.infer_const.borrow().len(), self);
  }
}

impl Formula {
  fn adjust_pred<'a>(n: PredId, args: &'a [Term], ctx: &Constructors) -> (PredId, &'a [Term]) {
    let c = &ctx.predicate[n];
    match c.redefines {
      Some(nr) => (nr, &args[c.superfluous as usize..]),
      None => (n, args),
    }
  }

  fn adjust_attr<'a>(n: AttrId, args: &'a [Term], ctx: &Constructors) -> (AttrId, &'a [Term]) {
    let c = &ctx.attribute[n].c;
    match c.redefines {
      Some(nr) => (nr, &args[c.superfluous as usize..]),
      None => (n, args),
    }
  }

  fn cmp(&self, ctx: &Constructors, other: &Formula, style: CmpStyle) -> Ordering {
    // vprintln!("{self:?} <?> {other:?}");
    self.discr().cmp(&other.discr()).then_with(|| {
      use Formula::*;
      match (self, other) {
        (True, True) | (Thesis, Thesis) => Ordering::Equal,
        (Neg { f: f1 }, Neg { f: f2 }) => f1.cmp(ctx, f2, style),
        (Is { term: t1, ty: ty1 }, Is { term: t2, ty: ty2 }) =>
          t1.cmp(ctx, t2, style).then_with(|| ty1.cmp(ctx, ty2, style)),
        (And { args: args1 }, And { args: args2 }) =>
          args1.len().cmp(&args2.len()).then_with(|| Formula::cmp_list(ctx, args1, args2, style)),
        (SchemePred { nr: n1, args: args1 }, SchemePred { nr: n2, args: args2 })
        | (PrivPred { nr: n1, args: args1, .. }, PrivPred { nr: n2, args: args2, .. }) =>
          n1.cmp(n2).then_with(|| Term::cmp_list(ctx, args1, args2, style)),
        (Attr { nr: n1, args: args1 }, Attr { nr: n2, args: args2 }) => match style {
          CmpStyle::Strict | CmpStyle::Alt =>
            n1.cmp(n2).then_with(|| Term::cmp_list(ctx, args1, args2, style)),
          CmpStyle::Red => {
            let (n1, args1) = Formula::adjust_attr(*n1, args1, ctx);
            let (n2, args2) = Formula::adjust_attr(*n2, args2, ctx);
            n1.cmp(&n2).then_with(|| Term::cmp_list(ctx, args1, args2, style))
          }
        },
        (Pred { nr: n1, args: args1 }, Pred { nr: n2, args: args2 }) => match style {
          CmpStyle::Strict | CmpStyle::Alt =>
            n1.cmp(n2).then_with(|| Term::cmp_list(ctx, args1, args2, style)),
          CmpStyle::Red => {
            let (n1, args1) = Formula::adjust_pred(*n1, args1, ctx);
            let (n2, args2) = Formula::adjust_pred(*n2, args2, ctx);
            n1.cmp(&n2).then_with(|| Term::cmp_list(ctx, args1, args2, style))
          }
        },
        (ForAll { dom: dom1, scope: sc1, .. }, ForAll { dom: dom2, scope: sc2, .. }) =>
          dom1.cmp(ctx, dom2, style).then_with(|| sc1.cmp(ctx, sc2, style)),
        #[allow(clippy::explicit_auto_deref)]
        (FlexAnd { orig: orig1, .. }, FlexAnd { orig: orig2, .. }) =>
          Formula::cmp_list(ctx, &**orig1, &**orig2, style),
        _ => unreachable!(),
      }
    })
  }

  fn cmp_list(ctx: &Constructors, fs1: &[Formula], fs2: &[Formula], style: CmpStyle) -> Ordering {
    // vprintln!("{fs1:?} <?> {fs2:?}");
    cmp_list(fs1, fs2, |f1, f2| f1.cmp(ctx, f2, style))
  }

  fn inst(&self, subst: &[Term], base: u32, depth: u32) -> Self {
    match *self {
      Formula::SchemePred { nr, ref args } =>
        Formula::SchemePred { nr, args: Term::inst_list(args, subst, base, depth) },
      Formula::Pred { nr, ref args } =>
        Formula::Pred { nr, args: Term::inst_list(args, subst, base, depth) },
      Formula::Attr { nr, ref args } =>
        Formula::Attr { nr, args: Term::inst_list(args, subst, base, depth) },
      Formula::PrivPred { nr, ref args, ref value } => Formula::PrivPred {
        nr,
        args: Term::inst_list(args, subst, base, depth),
        value: Box::new(value.inst(subst, base, depth)),
      },
      Formula::Is { ref term, ref ty } => Formula::Is {
        term: Box::new(term.inst(subst, base, depth)),
        ty: Box::new(ty.inst(subst, base, depth)),
      },
      Formula::Neg { ref f } => Formula::Neg { f: Box::new(f.inst(subst, base, depth)) },
      Formula::And { ref args } =>
        Formula::And { args: args.iter().map(|f| f.inst(subst, base, depth)).collect() },
      Formula::ForAll { var_id, ref dom, ref scope } => Formula::ForAll {
        var_id,
        dom: Box::new(dom.inst(subst, base, depth)),
        scope: Box::new(scope.inst(subst, base, depth + 1)),
      },
      Formula::FlexAnd { ref orig, ref terms, ref expansion } => {
        let [orig_l, orig_r] = &**orig;
        let [tm_l, tm_r] = &**terms;
        Formula::FlexAnd {
          orig: Box::new([orig_l, orig_r].map(|f| f.inst(subst, base, depth))),
          terms: Box::new([tm_l, tm_r].map(|f| f.inst(subst, base, depth))),
          expansion: Box::new(expansion.inst(subst, base, depth)),
        }
      }
      Formula::True | Formula::Thesis => self.clone(),
    }
  }
}

trait Equate {
  const ADJUST_LEFT: bool = true;

  fn locus_var_left(&mut self, _g: &Global, _lc: &LocalContext, _nr: LocusId, _t2: &Term) -> bool {
    false
  }
  fn eq_locus_var(&mut self, n1: u32, n2: u32) -> bool { n1 == n2 }

  fn eq_terms(&mut self, g: &Global, lc: &LocalContext, t1: &[Term], t2: &[Term]) -> bool {
    t1.len() == t2.len() && t1.iter().zip(t2).all(|(t1, t2)| self.eq_term(g, lc, t1, t2))
  }

  /// on (): EqTrm(fTrm1 = t1, fTrm2 = t2)
  /// on Subst: EsTrm(fTrm = t1, aTrm = t2)
  fn eq_term(&mut self, g: &Global, lc: &LocalContext, t1: &Term, t2: &Term) -> bool {
    use Term::*;
    // vprintln!("{t1:?} =? {t2:?}");
    match (t1, t2) {
      (&Locus { nr }, _) if self.locus_var_left(g, lc, nr, t2) => true,
      (&Locus { nr: LocusId(n1) }, &Locus { nr: LocusId(n2) }) if self.eq_locus_var(n1, n2) => true,
      (Bound { nr: BoundId(n1) }, Bound { nr: BoundId(n2) })
      | (Constant { nr: ConstantId(n1) }, Constant { nr: ConstantId(n2) })
      | (FreeVar { nr: n1 }, FreeVar { nr: n2 })
      | (LambdaVar { nr: n1 }, LambdaVar { nr: n2 })
      | (EqConst { nr: n1 }, EqConst { nr: n2 })
      | (Numeral { nr: n1 }, Numeral { nr: n2 }) => n1 == n2,
      (Infer { nr: n1 }, Infer { nr: n2 }) if n1 == n2 => true,
      (Functor { nr: n1, args: args1 }, Functor { nr: n2, args: args2 }) =>
        if n1 == n2 {
          self.eq_terms(g, lc, args1, args2)
        } else {
          let (n1, args1) = Term::adjust(*n1, args1, &g.constrs);
          let (n2, args2) = Term::adjust(*n2, args2, &g.constrs);
          n1 == n2 && self.eq_terms(g, lc, args1, args2)
        },
      (
        SchemeFunctor { nr: SchFuncId(n1), args: args1 },
        SchemeFunctor { nr: SchFuncId(n2), args: args2 },
      )
      | (Aggregate { nr: AggrId(n1), args: args1 }, Aggregate { nr: AggrId(n2), args: args2 })
      | (
        PrivFunc { nr: PrivFuncId(n1), args: args1, .. },
        PrivFunc { nr: PrivFuncId(n2), args: args2, .. },
      )
      | (Selector { nr: SelId(n1), args: args1 }, Selector { nr: SelId(n2), args: args2 }) =>
        n1 == n2 && self.eq_terms(g, lc, args1, args2),
      (Choice { ty: ty1 }, Choice { ty: ty2 }) => self.eq_type(g, lc, ty1, ty2),
      (
        Fraenkel { args: args1, scope: sc1, compr: c1 },
        Fraenkel { args: args2, scope: sc2, compr: c2 },
      ) =>
        args1.len() == args2.len()
          && args1.iter().zip(&**args2).all(|(ty1, ty2)| self.eq_type(g, lc, &ty1.1, &ty2.1))
          && self.eq_term(g, lc, sc1, sc2)
          && self.eq_formula(g, lc, c1, c2),
      (It, It) => true,
      (Qua { .. }, Qua { .. }) => panic!("invalid qua"),
      (_, &Infer { nr }) => self.eq_term(g, lc, t1, &lc.infer_const.borrow()[nr].def),
      (&Infer { nr }, _) => self.eq_term(g, lc, &lc.infer_const.borrow()[nr].def, t2),
      (PrivFunc { .. }, _) | (_, PrivFunc { .. }) =>
        self.eq_term(g, lc, t1.skip_priv_func(), t2.skip_priv_func()),
      _ => false,
    }
  }

  /// for (): TypObj.EqRadices
  fn eq_radices(&mut self, g: &Global, lc: &LocalContext, ty1: &Type, ty2: &Type) -> bool {
    match (ty1.kind, ty2.kind) {
      (TypeKind::Mode(n1), TypeKind::Mode(n2)) =>
        if n1 == n2 {
          self.eq_terms(g, lc, &ty1.args, &ty2.args)
        } else {
          let (n1, args1) = if Self::ADJUST_LEFT {
            Type::adjust(n1, &ty1.args, &g.constrs)
          } else {
            (n1, &*ty1.args)
          };
          let (n2, args2) = Type::adjust(n2, &ty2.args, &g.constrs);
          n1 == n2 && self.eq_terms(g, lc, args1, args2)
        },
      (TypeKind::Struct(n1), TypeKind::Struct(n2)) =>
        n1 == n2 && self.eq_terms(g, lc, &ty1.args, &ty2.args),
      _ => false,
    }
  }

  fn eq_type(&mut self, g: &Global, lc: &LocalContext, ty1: &Type, ty2: &Type) -> bool {
    ty1.attrs.0.is_subset_of(&ty2.attrs.1, |a1, a2| self.eq_attr(g, lc, a1, a2))
      && ty2.attrs.0.is_subset_of(&ty1.attrs.1, |a2, a1| self.eq_attr(g, lc, a1, a2))
      && self.eq_radices(g, lc, ty1, ty2)
  }

  /// on (): EqAttr
  /// on Subst: EsAttr
  fn eq_attr(&mut self, g: &Global, lc: &LocalContext, a1: &Attr, a2: &Attr) -> bool {
    // vprintln!("{a1:?} =? {a2:?}");
    let (n1, args1) = a1.adjust(&g.constrs);
    let (n2, args2) = a2.adjust(&g.constrs);
    n1 == n2 && a1.pos == a2.pos && self.eq_terms(g, lc, args1, args2)
  }

  fn eq_formulas(
    &mut self, g: &Global, lc: &LocalContext, args1: &[Formula], args2: &[Formula],
  ) -> bool {
    args1.len() == args2.len()
      && args1.iter().zip(args2).all(|(f1, f2)| self.eq_formula(g, lc, f1, f2))
  }

  fn eq_and(
    &mut self, g: &Global, lc: &LocalContext, args1: &[Formula], args2: &[Formula],
  ) -> bool {
    self.eq_formulas(g, lc, args1, args2)
  }

  fn eq_pred(
    &mut self, g: &Global, lc: &LocalContext, n1: PredId, n2: PredId, args1: &[Term],
    args2: &[Term],
  ) -> bool {
    n1 == n2 && self.eq_terms(g, lc, args1, args2)
  }

  fn eq_formula(&mut self, g: &Global, lc: &LocalContext, f1: &Formula, f2: &Formula) -> bool {
    use Formula::*;
    match (f1.skip_priv_pred(), f2.skip_priv_pred()) {
      (True, True) | (Thesis, Thesis) => true,
      (Neg { f: f1 }, Neg { f: f2 }) => self.eq_formula(g, lc, f1, f2),
      (Is { term: t1, ty: ty1 }, Is { term: t2, ty: ty2 }) =>
        self.eq_term(g, lc, t1, t2) && self.eq_type(g, lc, ty1, ty2),
      (And { args: args1 }, And { args: args2 }) => self.eq_and(g, lc, args1, args2),
      (SchemePred { nr: n1, args: args1 }, SchemePred { nr: n2, args: args2 })
      | (PrivPred { nr: n1, args: args1, .. }, PrivPred { nr: n2, args: args2, .. }) =>
        n1 == n2 && self.eq_terms(g, lc, args1, args2),
      (Attr { nr: n1, args: args1 }, Attr { nr: n2, args: args2 }) => {
        let (n1, args1) = Formula::adjust_attr(*n1, args1, &g.constrs);
        let (n2, args2) = Formula::adjust_attr(*n2, args2, &g.constrs);
        n1 == n2 && self.eq_terms(g, lc, args1, args2)
      }
      (Pred { nr: n1, args: args1 }, Pred { nr: n2, args: args2 }) => {
        let (n1, args1) = if Self::ADJUST_LEFT {
          Formula::adjust_pred(*n1, args1, &g.constrs)
        } else {
          (*n1, &**args1)
        };
        let (n2, args2) = Formula::adjust_pred(*n2, args2, &g.constrs);
        self.eq_pred(g, lc, n1, n2, args1, args2)
      }
      (ForAll { dom: dom1, scope: sc1, .. }, ForAll { dom: dom2, scope: sc2, .. }) =>
        self.eq_type(g, lc, dom1, dom2) && self.eq_formula(g, lc, sc1, sc2),
      #[allow(clippy::explicit_auto_deref)]
      (FlexAnd { orig: orig1, .. }, FlexAnd { orig: orig2, .. }) =>
        self.eq_formulas(g, lc, &**orig1, &**orig2),
      _ => false,
    }
  }
}

impl Equate for () {
  fn eq_and(
    &mut self, g: &Global, lc: &LocalContext, args1: &[Formula], args2: &[Formula],
  ) -> bool {
    if args1.len() == args2.len() {
      args1.iter().zip(args2).all(|(f1, f2)| self.eq_formula(g, lc, f1, f2))
    } else {
      let mut conjs1 = ConjIter([].iter(), args1.iter());
      let mut conjs2 = ConjIter([].iter(), args2.iter());
      loop {
        match (conjs1.next(), conjs2.next()) {
          (None, None) => break true,
          (Some(f1), Some(f2)) if self.eq_formula(g, lc, f1, f2) => {}
          _ => break false,
        }
      }
    }
  }

  fn eq_pred(
    &mut self, g: &Global, lc: &LocalContext, n1: PredId, n2: PredId, args1: &[Term],
    args2: &[Term],
  ) -> bool {
    n1 == n2
      && (self.eq_terms(g, lc, args1, args2)
        || Some(n1) == g.reqs.equals_to()
          && if let ([l1, r1], [l2, r2]) = (args1, args2) {
            self.eq_term(g, lc, r1, l2) && self.eq_term(g, lc, l1, r2)
          } else {
            unreachable!()
          })
  }
}

#[derive(Clone, Debug, Default)]
struct Subst {
  // subst_ty: Vec<Option<Box<Term>>>,
  /// gSubstTrm
  /// `IdxVec<LocusId, Option<Box<Term>>>` but fixed length
  subst_term: Box<[Option<Box<Term>>]>,
}

macro_rules! mk_visit {
  ($visit:ident$(, $mutbl:tt)?) => {
    pub trait $visit {
      #[inline] fn abort(&self) -> bool { false }
      fn super_visit_term(&mut self, tm: &$($mutbl)? Term, depth: u32) {
        if self.abort() { return }
        match tm {
          Term::Locus { .. }
          | Term::Bound { .. }
          | Term::Constant { .. }
          | Term::EqConst { .. }
          | Term::Infer { .. }
          | Term::FreeVar { .. }
          | Term::LambdaVar { .. }
          | Term::It => {}
          Term::SchemeFunctor { args, .. }
          | Term::Aggregate { args, .. }
          | Term::Functor { args, .. }
          | Term::Selector { args, .. } => self.visit_terms(args, depth),
          Term::PrivFunc { args, value, .. } => {
            self.visit_terms(args, depth);
            self.visit_term(value, depth)
          }
          Term::Numeral { .. } => {}
          Term::Qua { .. } => unreachable!("visit_term(Qua)"),
          Term::Choice { ty } => self.visit_type(ty, depth),
          Term::Fraenkel { args, scope, compr } => {
            let mut depth = depth;
            for (_, ty) in &$($mutbl)? **args {
              self.visit_type(ty, depth);
              depth += 1;
            }
            self.visit_term(scope, depth);
            self.visit_formula(compr, depth)
          }
        }
      }

      fn visit_term(&mut self, tm: &$($mutbl)? Term, depth: u32) {
        self.super_visit_term(tm, depth)
      }

      fn visit_terms(&mut self, tms: &$($mutbl)? [Term], depth: u32) {
        for tm in tms {
          if self.abort() { return }
          self.visit_term(tm, depth)
        }
      }

      fn visit_type(&mut self, ty: &$($mutbl)? Type, depth: u32) {
        if self.abort() { return }
        self.visit_attrs(&$($mutbl)? ty.attrs.0, depth);
        self.visit_attrs(&$($mutbl)? ty.attrs.1, depth);
        self.visit_terms(&$($mutbl)? ty.args, depth);
      }

      fn visit_types(&mut self, tys: &$($mutbl)? [Type], depth: u32) {
        for ty in tys {
          if self.abort() { return }
          self.visit_type(ty, depth)
        }
      }

      fn visit_attrs(&mut self, attrs: &$($mutbl)? Attrs, depth: u32) {
        if let Attrs::Consistent(attrs) = attrs {
          for attr in attrs {
            if self.abort() { return }
            self.visit_terms(&$($mutbl)? attr.args, depth)
          }
        }
      }

      fn super_visit_formula(&mut self, f: &$($mutbl)? Formula, depth: u32) {
        if self.abort() { return }
        match f {
          Formula::SchemePred { args, .. }
          | Formula::Pred { args, .. }
          | Formula::Attr { args, .. } => self.visit_terms(args, depth),
          Formula::PrivPred { args, value, .. } => {
            self.visit_terms(args, depth);
            self.visit_formula(value, depth)
          }
          Formula::Is { term, ty } => {
            self.visit_term(term, depth);
            self.visit_type(ty, depth)
          }
          Formula::Neg { f } => self.visit_formula(f, depth),
          Formula::And { args } =>
            for f in args {
              self.visit_formula(f, depth)
            },
          Formula::ForAll { dom, scope, .. } => {
            self.visit_type(dom, depth);
            self.visit_formula(scope, depth + 1)
          }
          Formula::FlexAnd { orig, terms, expansion } => {
            let [orig_l, orig_r] = &$($mutbl)? **orig;
            let [tm_l, tm_r] = &$($mutbl)? **terms;
            self.visit_formula(orig_l, depth);
            self.visit_formula(orig_r, depth);
            self.visit_formula(expansion, depth);
            self.visit_term(tm_l, depth);
            self.visit_term(tm_r, depth);
          }
          Formula::True | Formula::Thesis => {}
        }
      }

      fn visit_formula(&mut self, f: &$($mutbl)? Formula, depth: u32) {
        self.super_visit_formula(f, depth)
      }
    }
  };
}
mk_visit!(Visit);
mk_visit!(VisitMut, mut);

struct OnVarMut<F: FnMut(&mut u32, u32)>(F);
impl<F: FnMut(&mut u32, u32)> VisitMut for OnVarMut<F> {
  fn visit_term(&mut self, tm: &mut Term, depth: u32) {
    self.super_visit_term(tm, depth);
    if let Term::Bound { nr: BoundId(nr) } = tm {
      self.0(nr, depth)
    }
  }
}

struct CheckBound(bool, u32);
impl CheckBound {
  fn get(base: u32, f: impl FnOnce(&mut Self)) -> bool {
    let mut cb = Self(false, base);
    f(&mut cb);
    cb.0
  }
}
impl Visit for CheckBound {
  fn abort(&self) -> bool { self.0 }
  fn visit_term(&mut self, tm: &Term, depth: u32) {
    self.super_visit_term(tm, depth);
    if let Term::Bound { nr: BoundId(nr) } = *tm {
      self.0 |= nr < self.1
    }
  }
}

struct OnFunc<F: FnMut(FuncId, &[Term])>(F);
impl<F: FnMut(FuncId, &[Term])> Visit for OnFunc<F> {
  fn visit_term(&mut self, tm: &Term, depth: u32) {
    self.super_visit_term(tm, depth);
    if let Term::Functor { nr, args } = tm {
      (self.0)(*nr, args)
    }
  }
  fn visit_type(&mut self, ty: &Type, depth: u32) {}
  fn visit_formula(&mut self, f: &Formula, depth: u32) {}
}

fn has_func<'a>(ctx: &'a Constructors, nr: FuncId, found: &'a mut bool) -> impl Visit + 'a {
  OnFunc(move |n, args| *found |= n == nr || Term::adjust(n, args, ctx).0 == nr)
}

impl Term {
  fn has_func(&self, ctx: &Constructors, nr: FuncId) -> bool {
    let mut found = false;
    has_func(ctx, nr, &mut found).visit_term(self, 0);
    found
  }

  fn inst(&self, subst: &[Term], base: u32, mut depth: u32) -> Self {
    match *self {
      Term::Locus { nr } => {
        let mut tm = subst[nr.0 as usize].clone();
        OnVarMut(|nr, depth| {
          if *nr >= base {
            *nr += depth - base
          }
        })
        .visit_term(&mut tm, depth);
        tm
      }
      Term::Bound { .. }
      | Term::Constant { .. }
      | Term::EqConst { .. }
      | Term::Infer { .. }
      | Term::Numeral { .. }
      | Term::FreeVar { .. }
      | Term::LambdaVar { .. }
      | Term::It => self.clone(),
      Term::SchemeFunctor { nr, ref args } =>
        Term::SchemeFunctor { nr, args: Term::inst_list(args, subst, base, depth) },
      Term::Aggregate { nr, ref args } =>
        Term::Aggregate { nr, args: Term::inst_list(args, subst, base, depth) },
      Term::PrivFunc { nr, ref args, ref value } => Term::PrivFunc {
        nr,
        args: Term::inst_list(args, subst, base, depth),
        value: Box::new(value.inst(subst, base, depth)),
      },
      Term::Functor { nr, ref args } =>
        Term::Functor { nr, args: Term::inst_list(args, subst, base, depth) },
      Term::Selector { nr, ref args } =>
        Term::Selector { nr, args: Term::inst_list(args, subst, base, depth) },
      Term::Qua { ref value, ref ty } => Term::Qua {
        value: Box::new(value.inst(subst, base, depth)),
        ty: Box::new(ty.inst(subst, base, depth)),
      },
      Term::Choice { ref ty } => Term::Choice { ty: Box::new(ty.inst(subst, base, depth)) },
      Term::Fraenkel { ref args, ref scope, ref compr } => Term::Fraenkel {
        args: args.iter().map(|(n, v)| ((*n, v.inst(subst, base, depth)), depth += 1).0).collect(),
        scope: Box::new(scope.inst(subst, base, depth)),
        compr: Box::new(compr.inst(subst, base, depth)),
      },
    }
  }

  fn inst_list(this: &[Self], subst: &[Term], base: u32, depth: u32) -> Box<[Self]> {
    this.iter().map(|tm| tm.inst(subst, base, depth)).collect()
  }

  /// RoundUpTrmType(fTrm = self)
  fn round_up_type<'a>(&self, g: &Global, lc: &'a LocalContext) -> CowBox<'a, Type> {
    let tm = self.skip_priv_func();
    let ty = tm.get_type_uncached(g, lc);
    tm.round_up_type_from(g, lc, CowBox::Owned(ty))
  }

  /// RoundUpTrmTypeWithType(lTyp = ty, fTrm = self)
  fn round_up_type_from<'a>(
    &self, g: &Global, lc: &'a LocalContext, mut ty: CowBox<'a, Type>,
  ) -> CowBox<'a, Type> {
    // vprintln!("RoundUpTrmTypeWithType {self:?}, {ty:?}");
    if let Term::Functor { .. } | Term::Selector { .. } | Term::Aggregate { .. } = self {
      let mut attrs = ty.attrs.1.clone();
      // if verbose() {
      //   eprintln!("compare: {self:?}");
      //   for &i in &g.clusters.functor.sorted {
      //     eprintln!(
      //       "{:?} <- {:?}",
      //       FunctorCluster::cmp_term(&g.clusters.functor.vec[i].term, &g.constrs, self),
      //       g.clusters.functor.vec[i].term
      //     )
      //   }
      // }
      let fcs = &g.clusters.functor.sorted[g.clusters.functor.sorted.partition_point(|&i| {
        FunctorCluster::cmp_term(&g.clusters.functor.vec[i].term, &g.constrs, self)
          == Ordering::Less
      })..];
      let fcs = &fcs[..fcs.partition_point(|&i| {
        FunctorCluster::cmp_term(&g.clusters.functor.vec[i].term, &g.constrs, self)
          != Ordering::Greater
      })];
      if !fcs.is_empty() {
        let mut used = vec![false; fcs.len()];
        'main: loop {
          for (&i, used) in fcs.iter().zip(&mut used) {
            if *used {
              continue
            }
            let fc = &g.clusters.functor.vec[i];
            if fc.round_up_with(g, lc, self, &ty, &mut attrs) {
              attrs.round_up_with(g, lc, &ty);
              let mut ty2 = ty.to_owned();
              ty2.attrs.1 = attrs.clone();
              ty = CowBox::Owned(ty2);
              if let Attrs::Inconsistent = ty.attrs.1 {
                break 'main
              }
              *used = true;
              if fc.ty.is_some() {
                continue 'main
              }
            } else if fc.ty.is_none() {
              *used = true
            }
          }
          break
        }
      }
    }
    ty
  }

  /// GetTrmType(self = fTrm)
  fn get_type(&self, g: &Global, lc: &LocalContext) -> Box<Type> {
    // vprintln!("GetTrmType {self:?}");
    if matches!(self, Term::Functor { .. } | Term::Selector { .. } | Term::Aggregate { .. }) {
      let cache = lc.term_cache.borrow();
      if let Ok(i) = cache.find(&g.constrs, self) {
        return cache.terms[i].1.clone()
      }
      drop(cache);
      let i = TermCollection::insert(g, lc, self);
      lc.term_cache.borrow().terms[i].1.clone()
    } else {
      self.get_type_uncached(g, lc)
    }
  }

  /// CopyTrmType(self = fTrm)
  fn get_type_uncached(&self, g: &Global, lc: &LocalContext) -> Box<Type> {
    let ty = match *self {
      Term::Bound { nr } => Box::new(lc.bound_var[nr].clone()),
      Term::Constant { nr } => {
        let mut ty = lc.fixed_var[nr].ty.clone();
        OnVarMut(|nr, depth| *nr += depth).visit_type(&mut ty, 0);
        ty
      }
      Term::Infer { nr } => lc.infer_const.borrow()[nr].ty.clone(),
      Term::Numeral { .. } => Box::new(g.nonzero_type.clone()),
      Term::Locus { nr } => Box::new(lc.locus_ty[nr].clone()),
      Term::SchemeFunctor { nr, .. } => Box::new(lc.sch_func_ty[nr].clone()),
      Term::PrivFunc { nr, ref args, .. } => Box::new(lc.priv_func[nr].ty.inst(args, 0, 0)),
      Term::Functor { nr, ref args } => Box::new(g.constrs.functor[nr].ty.inst(args, 0, 0)),
      Term::Selector { nr, ref args } => Box::new(g.constrs.selector[nr].ty.inst(args, 0, 0)),
      Term::Aggregate { nr, ref args } => Box::new(g.constrs.aggregate[nr].ty.inst(args, 0, 0)),
      Term::Fraenkel { .. } => Box::new(Type::new(TypeKind::Mode(g.reqs.set()))),
      Term::It => lc.it_type.as_ref().unwrap().clone(),
      Term::Choice { ref ty } | Term::Qua { ref ty, .. } => ty.clone(),
      Term::EqConst { .. } => unreachable!("get_type_uncached(EqConst)"),
      Term::FreeVar { .. } => unreachable!("get_type_uncached(FreeVar)"),
      Term::LambdaVar { .. } => unreachable!("get_type_uncached(LambdaVar)"),
    };
    // vprintln!("[{:?}] get_type {:?} -> {:?}", lc.infer_const.borrow().len(), self, ty);
    ty
  }
}

#[derive(Default)]
struct TermCollection {
  scope: u32,
  terms: Vec<(Term, Box<Type>, u32)>,
}

impl TermCollection {
  /// MarkTermsInTTColl
  fn open_scope(&mut self) { self.scope += 1; }

  /// RemoveTermsFromTTColl
  fn close_scope(&mut self) {
    self.scope -= 1;
    self.terms.retain(|a| a.2 <= self.scope);
  }

  /// MSortedCollection.Search(self = self, Key = tm, out Index)
  fn find(&self, ctx: &Constructors, tm: &Term) -> Result<usize, usize> {
    self.terms.binary_search_by(|a| a.0.cmp(ctx, tm, CmpStyle::Alt))
  }

  fn insert_raw(&mut self, ctx: &Constructors, tm: Term, ty: Box<Type>) -> usize {
    let i = self.find(ctx, &tm).unwrap_err();
    self.terms.insert(i, (tm, ty, self.scope));
    i
  }

  fn get_mut(&mut self, ctx: &Constructors, tm: &Term) -> &mut (Term, Box<Type>, u32) {
    let i = self.find(ctx, tm).unwrap();
    &mut self.terms[i]
  }

  /// InsertTermInTTColl(fTrm = tm)
  fn insert(g: &Global, lc: &LocalContext, tm: &Term) -> usize {
    // eprintln!("[{}] InsertTermInTTColl {tm:?}", lc.term_cache.borrow().scope);
    if let Term::Functor { args, .. } | Term::Selector { args, .. } | Term::Aggregate { args, .. } =
      tm
    {
      for tm in &**args {
        let tm = tm.skip_priv_func();
        if let Term::Functor { .. } | Term::Selector { .. } | Term::Aggregate { .. } = tm {
          Self::insert(g, lc, tm);
        }
      }
    }
    if let Ok(i) = lc.term_cache.borrow().find(&g.constrs, tm) {
      return i
    }

    // There are some horrible race conditions here.
    // get_type_uncached(), round_up_type_from() and round_up_with_self()
    // are all mutually recursive with this function, so we can end up trying to insert a term
    // while things are changing under us. We have to clone the type several times,
    // and we also have to search anew for the term every time
    // because it might have been shuffled about.

    // Get the type of the term. Since we haven't inserted yet, re-entrancy here is bad news
    let ty = tm.get_type_uncached(g, lc);

    // 1. Insert the term with its type provisionally into the cache
    let mut i = lc.term_cache.borrow_mut().insert_raw(&g.constrs, tm.clone(), ty);

    // clone the type so that we don't hold on to the cache for the next bit
    let ty = lc.term_cache.borrow().terms[i].1.clone();
    // Round up the type using the term we inserted
    let mut ty = tm.round_up_type_from(g, lc, CowBox::Owned(ty)).to_owned();
    // 2. Put the new type into the cache.
    // (Yes, stuff between (1) and (2) can see the term with the unrounded type...)
    // also clone the type *again*
    lc.term_cache.borrow_mut().get_mut(&g.constrs, tm).1 = ty.clone();

    // Round up the type using its own attributes
    ty.round_up_with_self(g, lc);
    // eprintln!("[{}] caching {tm:?} : {ty:?}", lc.term_cache.borrow().scope);
    let cache = &mut *lc.term_cache.borrow_mut();
    // search for the term one last time and return the index.
    // This index has a very limited shelf life
    let i = cache.find(&g.constrs, tm).unwrap();
    // 3. Put the newer type into the cache.
    cache.terms[i].1 = ty;

    // Note: the original source doesn't do the two clones above,
    // but that's definitely a segfault hazard.
    i
  }

  fn clear(&mut self) { self.terms.clear() }
}

// fn ensure_has<T>(vec: &mut Vec<T>, i: usize, default: impl FnMut() -> T) {
//   if i >= vec.len() {
//     vec.resize_with(i + 1, default)
//   }
// }

fn to_ptr<T>(x: &Option<Box<T>>) -> *const T {
  match x {
    Some(x) => &**x,
    None => std::ptr::null(),
  }
}

impl Subst {
  fn new(size: usize) -> Self { Self { subst_term: vec![None; size].into() } }

  fn clear(&mut self) {
    for t in &mut *self.subst_term {
      *t = None;
    }
  }

  /// InitEssentialsArgs
  fn from_essential(len: usize, essential: &[LocusId], args: &[Term]) -> Self {
    // eprintln!("from_essential {essential:?}");
    assert_eq!(args.len(), essential.len());
    let mut subst = Self::new(len);
    for (&n, t) in essential.iter().zip(args) {
      subst.subst_term[Idx::into_usize(n)] = Some(Box::new(t.clone()))
    }
    subst
  }

  /// InitInst
  fn finish(&self) -> Box<[Term]> {
    self.subst_term.iter().map(|t| t.as_deref().unwrap().clone()).collect()
  }

  /// InstSubstTrm
  fn inst_term(&self, tm: &Term, depth: u32) -> Term { tm.inst(&self.finish(), depth, depth) }

  /// CheckLociTypes
  fn check_loci_types(&mut self, g: &Global, lc: &LocalContext, tys: &[Type]) -> bool {
    let mut i = tys.len();
    assert!(self.subst_term.len() == i);
    let mut subst_ty = vec![None; i];
    // self.subst_term, tys, and subst_ty are all parallel arrays.
    // * subst_term[i] is either missing (unassigned), or it should have type tys[i].
    // * subst_ty[i] is the actual type of subst_term[i], which should be a subtype of tys[i].
    //
    // At the start of the algorithm, subst_ty is empty, and subst_term is partially filled.
    // The index i is where we are currently working; we progress from right to left.
    // We maintain the invariant that if subst_ty[i] is set, then we have checked that
    //
    //   subst_term[i] : subst_ty[i]   and   subst_ty[i] <: subst(tys[i]).
    //
    // let n = CALLS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    // vprintln!("\nCheckLociTypes {n}: subst = {:?} : {subst_ty:?}, tys = {tys:?}", self.subst_term);
    'main: loop {
      // vprintln!("main {i:?}, subst = {:?} : {subst_ty:?}", self.subst_term);
      // Decrease i to skip past `None`s in subst_term, and then `let Some(tm) = subst_term[i]`
      let tm = loop {
        if i == 0 {
          return true
        }
        i -= 1;
        if let Some(t) = &self.subst_term[i] {
          break &**t
        }
      };
      // vprintln!("main {i:?}, subst = {:?} : {subst_ty:?}, tm = {tm:?}", self.subst_term);
      let orig_subst = self.subst_term.iter().map(Option::is_some).collect::<Vec<_>>();
      // let wty be the type of subst_term[i]
      let wty = if g.recursive_round_up {
        tm.round_up_type(g, lc)
      } else {
        CowBox::Owned(tm.get_type(g, lc))
      };
      // vprintln!("main {i:?}, subst = {:?} : {subst_ty:?}, wty = {wty:?}", self.subst_term);
      // Are the attributes of tys[i] all contained in wty's?
      // This is a necessary condition for wty <: tys[i].
      let mut ok = if wty.decreasing_attrs(&tys[i], |a1, a2| self.eq_attr(g, lc, a1, a2)) {
        Some(wty)
      } else {
        None
      };
      // This loop { match ... } is a workaround for the lack of goto in rust
      loop {
        // vprintln!("loop {i:?}, subst = {:?} : {subst_ty:?}, ok = {ok:?}", self.subst_term);
        if let Some(wty) = ok {
          // We have a candidate type `wty` which is the type of `subst_term[i]`.

          // Try widening wty to make it a candidate for unification with tys[i].
          // If this fails, we have to backtrack
          let Some(wty) = tys[i].widening_of(g, &wty) else {
            ok = None;
            continue
          };

          // Unify subst(tys[i]) and wty, which can assign some entries in subst_term.
          let comp = self.cmp_type(g, lc, &tys[i], &wty, false);
          // Record that subst_ty[i] := wty
          subst_ty[i] = Some(wty.to_owned());
          if comp {
            // We were successful, so we can continue the main loop
            continue 'main
          }
          // Unset anything that was set as a result of the unification
          for j in 0..=i {
            match &mut self.subst_term[j] {
              x @ Some(_) if !orig_subst[j] => *x = None,
              _ => {}
            }
          }
        } else {
          // we get here when we want to backtrack because we can't satisfy
          // the current substitution
          loop {
            // Increase i to the beginning of the last run of Nones in subst_term,
            // by checking that subst_term[i+1] is set
            loop {
              i += 1;
              match self.subst_term.get(i + 1) {
                None => return false,
                Some(Some(_)) => break,
                _ => {}
              }
            }
            // FIXME: Bug? Why is subst_ty[i] Some here
            // vprintln!("bad {i:?}, subst = {:?} : {subst_ty:?}", self.subst_term);
            let ty = subst_ty[i].as_deref().unwrap();
            // vprintln!("bad {i:?}, subst = {:?} : {subst_ty:?}, ty = {ty:?}", self.subst_term);

            // I don't know what this check is doing. I guess StructId(0) is special?
            // In tests it is always STRUCT_0:1 which is "1-sorted".
            // Maybe it is a superclass of all structs?
            if ty.kind != TypeKind::Struct(StructId(0))
              && matches!(tys[i].kind, TypeKind::Mode(n) if g.constrs.mode[n].redefines.is_none())
            {
              break
            }
          }
        }
        // subst_ty[i] is necessarily filled at this point,
        // and the substitution didn't work out.
        // So we unset it and widen it:
        // * if the widening fails, then we continue to backtrack
        // * If we get wty we pass it back to the unification check
        ok = subst_ty[i].take().unwrap().widening(g).map(CowBox::Owned)
      }
    }
  }

  fn cmp_type(
    &mut self, g: &Global, lc: &LocalContext, ty1: &Type, ty2: &Type, exact: bool,
  ) -> bool {
    // eprintln!("{ty1:?} <?> {ty2:?}");
    match (ty1.kind, ty2.kind) {
      (TypeKind::Mode(n1), TypeKind::Mode(n2)) if n1 == n2 =>
        self.eq_terms(g, lc, &ty1.args, &ty2.args),
      (TypeKind::Mode(n1), TypeKind::Mode(n2)) if !exact => {
        let (n2, args2) = Type::adjust(n2, &ty2.args, &g.constrs);
        n1 == n2 && self.eq_terms(g, lc, &ty1.args, args2)
      }
      (TypeKind::Struct(n1), TypeKind::Struct(n2)) =>
        n1 == n2 && self.eq_terms(g, lc, &ty1.args, &ty2.args),
      _ => false,
    }
  }
}

impl Equate for Subst {
  const ADJUST_LEFT: bool = false;

  fn eq_locus_var(&mut self, _n1: u32, _n2: u32) -> bool { false }
  fn locus_var_left(&mut self, g: &Global, lc: &LocalContext, nr: LocusId, t2: &Term) -> bool {
    // vprintln!("{self:?} @ v{nr:?} =? {t2:?}");
    match &mut self.subst_term[Idx::into_usize(nr)] {
      x @ None => {
        *x = Some(Box::new(t2.clone()));
        true
      }
      Some(tm) => {
        let v = match **tm {
          Term::Qua { ref value, .. } => value,
          _ => tm,
        };
        ().eq_term(g, lc, t2, v)
      }
    }
  }
}

struct ConjIter<'a>(std::slice::Iter<'a, Formula>, std::slice::Iter<'a, Formula>);

impl<'a> Iterator for ConjIter<'a> {
  type Item = &'a Formula;
  fn next(&mut self) -> Option<Self::Item> {
    loop {
      if let Some(f) = self.0.next() {
        return Some(f)
      }
      match self.1.next()?.skip_priv_pred() {
        Formula::And { args } => self.0 = args.iter(),
        f => return Some(f),
      }
    }
  }
}

impl Formula {
  fn skip_priv_pred(&self) -> &Self {
    let mut ty = self;
    while let Formula::PrivPred { value, .. } = ty {
      ty = value;
      while let Formula::PrivPred { value, .. } = ty {
        ty = value
      }
      if let Formula::Neg { f } = ty {
        if let Formula::PrivPred { value, .. } = &**f {
          let mut l = &**value;
          while let Formula::PrivPred { value, .. } = l {
            l = value
          }
          if let Formula::Neg { f } = l {
            ty = f
          }
        }
      }
    }
    ty
  }
}
impl Attrs {
  pub fn push(&mut self, attr: Attr) {
    if let Self::Consistent(attrs) = self {
      attrs.push(attr)
    }
  }

  /// MAttrCollection.IsSubsetOf(self = self, aClu = other, aEqAttr(x, y) = eq(y, x))
  pub fn is_subset_of(&self, other: &Self, mut eq: impl FnMut(&Attr, &Attr) -> bool) -> bool {
    // let n = CALLS2.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    // vprintln!("{n:?}: {self:?} <:? {other:?}");
    match (self, other) {
      (Attrs::Inconsistent, Attrs::Consistent(_)) => false,
      (Attrs::Consistent(this), Attrs::Consistent(other)) =>
        other.len() >= this.len() && this.iter().all(|i| other.iter().any(|j| eq(i, j))),
      (_, Attrs::Inconsistent) => {
        // You would think this case is just "true", but we use this function to
        // construct substitutions by unification, and so we have to report "false"
        // if a variable that would have been unified is left unbound.
        struct ContainsLocusVar(bool);
        impl Visit for ContainsLocusVar {
          fn abort(&self) -> bool { self.0 }
          fn visit_term(&mut self, tm: &Term, depth: u32) {
            match tm {
              Term::Locus { .. } => self.0 = true,
              _ => self.super_visit_term(tm, depth),
            }
          }
        }
        let mut v = ContainsLocusVar(false);
        v.visit_attrs(self, 0);
        !v.0
      }
    }
  }

  fn cmp(&self, ctx: &Constructors, other: &Attrs, style: CmpStyle) -> Ordering {
    let (this, other) = (self.attrs(), other.attrs());
    this.len().cmp(&other.len()).then_with(|| cmp_list(this, other, |a, b| a.cmp(ctx, b, style)))
  }

  fn inst(&self, subst: &[Term], base: u32, depth: u32) -> Self {
    match self {
      Attrs::Inconsistent => Attrs::Inconsistent,
      Attrs::Consistent(attrs) =>
        Attrs::Consistent(attrs.iter().map(|attr| attr.inst(subst, base, depth)).collect()),
    }
  }

  /// MAttrCollection.CopyAllowed(aTyp = (n, args), aOrigin = self)
  pub fn clone_allowed(&self, ctx: &Constructors, n: ModeId, args: &[Term]) -> Self {
    match self {
      Attrs::Inconsistent => Attrs::Inconsistent,
      Attrs::Consistent(attrs) => {
        let mut out = Self::default();
        let (n, _) = Type::adjust(n, args, ctx);
        for attr in attrs {
          if ctx.attribute[attr.adjusted_nr(ctx)].ty.kind != TypeKind::Mode(n) {
            out.push(attr.clone());
          }
        }
        out
      }
    }
  }

  /// MAttrCollection.Insert(self = self, aItem = item)
  pub fn insert(&mut self, ctx: &Constructors, item: Attr) {
    if let Self::Consistent(this) = self {
      match this.binary_search_by(|attr| attr.cmp_abs(ctx, &item, CmpStyle::Strict)) {
        Ok(i) =>
          if this[i].pos != item.pos {
            *self = Self::Inconsistent
          },
        Err(i) => this.insert(i, item),
      }
    }
  }

  fn reinsert_all(&mut self, ctx: &Constructors, mut f: impl FnMut(&mut Attr)) {
    if let Attrs::Consistent(attrs1) = self {
      for mut attr in std::mem::take(attrs1) {
        f(&mut attr);
        self.insert(ctx, attr)
      }
    }
  }

  /// MAttrCollection.EnlargeBy(self = self, aAnother = other, CopyAttribute = map)
  pub fn enlarge_by(&mut self, ctx: &Constructors, other: &Self, map: impl FnMut(&Attr) -> Attr) {
    if let Self::Consistent(this) = self {
      if let Self::Consistent(other) = other {
        if other.is_empty() {
          return
        }
        for item in itertools::merge_join_by(
          std::mem::take(this).into_iter(),
          other.iter().map(map),
          |a, b| a.cmp_abs(ctx, b, CmpStyle::Strict),
        ) {
          match item {
            EitherOrBoth::Left(attr) | EitherOrBoth::Right(attr) => this.push(attr),
            EitherOrBoth::Both(attr1, attr2) => {
              if attr1.pos != attr2.pos {
                *self = Self::Inconsistent;
                return
              }
              this.push(attr1)
            }
          }
        }
      } else {
        *self = Self::Inconsistent
      }
    }
  }

  /// MCondClList.RoundUpCluster(aCluster = self, aTyp = ty)
  /// MAttrCollection.RoundUpWith(self = self, aTyp = ty)
  pub fn round_up_with(&mut self, g: &Global, lc: &LocalContext, ty: &Type) {
    struct State<'a> {
      cl_fire: Vec<u32>,
      jobs: Vec<u32>,
      old_attr_nums: &'a mut EnumMap<bool, BTreeMap<AttrId, u32>>,
      new_attr_nums: &'a mut EnumMap<bool, BTreeMap<AttrId, u32>>,
    }
    fn sorted_insert(jobs: &mut Vec<u32>, value: u32) {
      if let Err(i) = jobs.binary_search(&value) {
        jobs.insert(i, value)
      }
    }

    impl State<'_> {
      /// HandleUsageAndFire
      fn handle_usage_and_fire(&mut self, g: &Global, attrs: &Attrs) {
        if let Attrs::Consistent(attrs) = attrs {
          for (_, map) in &mut *self.new_attr_nums {
            map.clear()
          }
          for attr in attrs {
            *self.new_attr_nums[attr.pos].entry(attr.adjusted_nr(&g.constrs)).or_default() += 1;
          }
          for (pos, map) in &*self.new_attr_nums {
            for (&adj_nr, &val) in map {
              if self.old_attr_nums[pos].get(&adj_nr).map_or(true, |&v| v < val) {
                if let Some(set) = g.clusters.conditional.attr_clusters[pos].get(&adj_nr) {
                  for &nr in set {
                    let x = &mut self.cl_fire[nr as usize];
                    *x = x.saturating_sub(1);
                    if *x == 0 {
                      sorted_insert(&mut self.jobs, nr);
                    }
                  }
                }
              }
            }
          }
          std::mem::swap(self.old_attr_nums, self.new_attr_nums)
        }
      }
    }

    // eprintln!("round_up_with {:?}", self);
    let mut state = State {
      cl_fire: Default::default(),
      jobs: Default::default(),
      old_attr_nums: &mut Default::default(),
      new_attr_nums: &mut Default::default(),
    };
    state.cl_fire.extend(g.clusters.conditional.vec.iter().map(|cl| match cl.antecedent {
      Attrs::Inconsistent => 0,
      Attrs::Consistent(ref attrs) => attrs.len() as u32,
    }));
    for (j, &c) in state.cl_fire.iter().enumerate() {
      if c == 0 {
        sorted_insert(&mut state.jobs, j as u32);
      }
    }
    state.handle_usage_and_fire(g, self);
    while let Self::Consistent(_) = self {
      let last = if let Some(last) = state.jobs.pop() { last } else { break };
      // vprintln!("job {last}");
      let cl = &g.clusters.conditional.vec[last as usize];
      let mut subst = Subst::new(cl.primary.len());
      // TryRounding()
      if g.type_reachable(&cl.ty, ty)
        && cl.antecedent.is_subset_of(self, |a1, a2| subst.eq_attr(g, lc, a1, a2))
        && !cl.consequent.1.is_subset_of(self, |a1, a2| {
          (a1.adjusted_nr(&g.constrs), a1.pos) == (a2.adjusted_nr(&g.constrs), a2.pos)
        })
      {
        // eprintln!(
        //   "try rounding cc {last} = {:?} + {:?} + {:?} by {:?}",
        //   cl.ty, cl.consequent.1, cl.primary, ty
        // );
        if let Some(ty) = cl.ty.widening_of(g, ty) {
          if subst.cmp_type(g, lc, &cl.ty, &ty, false)
            && cl.ty.attrs.0.is_subset_of(&ty.attrs.1, |a1, a2| subst.eq_attr(g, lc, a1, a2))
            && subst.check_loci_types(g, lc, &cl.primary)
          {
            let subst =
              subst.subst_term.into_vec().into_iter().map(|x| *x.unwrap()).collect::<Box<[Term]>>();
            // eprintln!("enlarge {:?} by {:?}", self, cl.consequent.1);
            self.enlarge_by(&g.constrs, &cl.consequent.1, |a| a.inst(&subst, 0, 0));
            state.handle_usage_and_fire(g, self)
          }
        }
      }
    }
  }
}

impl<I> TyConstructor<I> {
  fn round_up(&self, g: &Global, lc: &mut LocalContext) -> Attrs {
    let mut attrs = self.ty.attrs.0.clone();
    if let TypeKind::Mode(nr) = self.ty.kind {
      let cl = g.constrs.mode[nr].ty.attrs.1.inst(&self.ty.args, 0, 0);
      attrs.enlarge_by(&g.constrs, &cl, |a| a.clone())
    }
    lc.load_locus_tys(&self.primary);
    attrs.round_up_with(g, lc, &self.ty);
    lc.unload_locus_tys();
    attrs
  }
}

impl FunctorCluster {
  /// RoundUpWith(fCluster = self, fTrm = term, fTyp = ty, fClusterPtr = attrs)
  fn round_up_with(
    &self, g: &Global, lc: &LocalContext, term: &Term, ty: &Type, attrs: &mut Attrs,
  ) -> bool {
    // vprintln!("RoundUpWith {term:?}, {ty:?} <- {attrs:?} in {self:?}");
    let mut subst = Subst::new(self.primary.len());
    let mut eq =
      subst.eq_term(g, lc, &self.term, term) && subst.check_loci_types(g, lc, &self.primary);
    if !eq {
      if let Term::Functor { nr, ref args } = *term {
        let c = &g.constrs.functor[nr];
        if c.properties.get(PropertyKind::Commutativity) {
          let mut args = args.clone();
          args.swap(c.arg1 as usize, c.arg2 as usize);
          let term = Term::Functor { nr, args };
          subst.clear();
          eq =
            subst.eq_term(g, lc, &self.term, &term) && subst.check_loci_types(g, lc, &self.primary);
        }
      }
    }
    if eq {
      if let Some(cluster_ty) = &self.ty {
        match cluster_ty.widening_of(g, ty) {
          Some(ty)
            if subst.cmp_type(g, lc, cluster_ty, &ty, false)
              && cluster_ty
                .attrs
                .0
                .is_subset_of(&ty.attrs.1, |a1, a2| subst.eq_attr(g, lc, a1, a2))
              && subst.check_loci_types(g, lc, &self.primary) => {}
          _ => return false,
        }
      }
      let subst = subst.finish();
      attrs.enlarge_by(&g.constrs, &self.consequent.1, |a| a.inst(&subst, 0, 0));
    }
    eq
  }
}

impl Definiens {
  /// EqualsExpansion
  fn equals_expansion(&self) -> Option<EqualsDef> {
    let ConstrKind::Func(nr) = self.constr else { return None };
    let Formula::True = self.assumptions else { return None };
    let DefValue::Term(DefBody { cases, otherwise: Some(ow) }) = &self.value else { return None };
    let [] = **cases else { return None };
    let primary = self.primary.split_last().unwrap().1.to_vec().into(); // TODO: is this an unwrap?
    let expansion = ow.clone();
    let essential = self.essential.split_last().unwrap().1.to_vec().into(); // TODO: is this an unwrap?
    let args = self.essential.iter().map(|&nr| Term::Locus { nr }).collect();
    Some(EqualsDef { primary, expansion, pattern: (nr, args), essential })
  }
}

impl EqualsDef {
  /// ExpandTrmIfEqual
  fn expand_if_equal(
    &self, g: &Global, lc: &LocalContext, args: &[Term], depth: u32,
  ) -> Option<Term> {
    let mut subst = Subst::from_essential(self.primary.len(), &self.essential, args);
    let true = subst.check_loci_types(g, lc, &self.primary) else { return None };
    Some(subst.inst_term(&self.expansion, depth))
  }
}

struct ExpandPrivFunc<'a> {
  ctx: &'a Constructors,
}

impl VisitMut for ExpandPrivFunc<'_> {
  /// CopyExpTrm
  fn visit_term(&mut self, tm: &mut Term, depth: u32) {
    if let Term::PrivFunc { value, .. } = tm {
      *tm = std::mem::replace(value, Term::It);
      self.visit_term(tm, depth)
    } else {
      self.super_visit_term(tm, depth)
    }
  }

  fn visit_attrs(&mut self, attrs: &mut Attrs, depth: u32) {
    attrs.reinsert_all(self.ctx, |attr| self.visit_terms(&mut attr.args, depth))
  }

  /// CopyExpFrm
  fn visit_formula(&mut self, f: &mut Formula, depth: u32) {
    if let Formula::And { args } = f {
      for mut f in std::mem::take(args) {
        self.visit_formula(&mut f, depth);
        match f {
          Formula::And { args: fs } => args.extend(fs),
          _ => args.push(f),
        }
      }
    } else {
      self.super_visit_formula(f, depth);
    }
  }
}

pub struct InternConst<'a> {
  g: &'a Global,
  lc: &'a LocalContext,
  equals: &'a BTreeMap<ConstrKind, Vec<EqualsDef>>,
  identify: &'a [Identify],
  func_ids: &'a BTreeMap<ConstrKind, Vec<usize>>,
  only_constants: bool,
  equals_expansion_level: u32,
  /// InferConsts
  infer_consts: BTreeSet<FuncId>,
}

impl<'a> InternConst<'a> {
  fn new(
    g: &'a Global, lc: &'a LocalContext, equals: &'a BTreeMap<ConstrKind, Vec<EqualsDef>>,
    identify: &'a [Identify], func_ids: &'a BTreeMap<ConstrKind, Vec<usize>>,
  ) -> Self {
    Self {
      g,
      lc,
      equals,
      func_ids,
      identify,
      only_constants: true,
      equals_expansion_level: 0,
      infer_consts: Default::default(),
    }
  }

  /// CollectInferConst
  /// * precondition: tm must be Term::Functor
  /// * postcondition: if self.only_constants, then tm will be Term::Infer after
  fn collect_infer_const(&mut self, tm: &mut Term, depth: u32) {
    if self.only_constants {
      let mut ic = self.lc.infer_const.borrow_mut();
      let nr = match ic.find_index(|a| a.def.cmp(&self.g.constrs, tm, CmpStyle::Strict)) {
        Ok(nr) => nr,
        Err(i) => {
          drop(ic);
          let mut ty = tm.round_up_type(self.g, self.lc).to_owned();
          ty.round_up_with_self(self.g, self.lc);
          let def = Box::new(std::mem::replace(tm, Term::It));
          // TODO: numeric_value
          ic = self.lc.infer_const.borrow_mut();
          let nr = ic.insert_at(i, Assignment { def, ty, eq_const: Default::default() });
          // eprintln!("insert ?{nr:?} : {:?} := {:?}", ic[nr].ty, ic[nr].def);
          let mut ty = (*ic[nr].ty).clone();
          drop(ic);
          self.visit_type(&mut ty, depth);
          *self.lc.infer_const.borrow_mut()[nr].ty = ty;
          nr
        }
      };
      *tm = Term::Infer { nr };
    }
  }

  /// CollectEqualsConst
  /// precondition: tm must be Term::Functor
  fn collect_equals_const(&mut self, tm: &Term, depth: u32) -> BTreeSet<InferId> {
    let mut eq = BTreeSet::new();
    if self.equals_expansion_level >= 3 {
      return eq
    }
    let (nr, args) = {
      let Term::Functor { nr, ref args } = *tm else { unreachable!() };
      Term::adjust(nr, args, &self.g.constrs)
    };
    if self.infer_consts.contains(&nr) {
      return eq
    }
    let mut insert_one = |this: &mut Self, mut tm| {
      ExpandPrivFunc { ctx: &this.g.constrs }.visit_term(&mut tm, depth);
      this.equals_expansion_level += 1;
      this.infer_consts.insert(nr);
      this.visit_term(&mut tm, 0);
      this.equals_expansion_level -= 1;
      this.infer_consts.remove(&nr);
      let Term::Infer { nr } = tm else { unreachable!("{:?}", tm) };
      eq.insert(nr);
    };
    if let Some(eq_defs) = self.equals.get(&ConstrKind::Func(nr)) {
      for eq_def in eq_defs {
        if let Some(tm) = eq_def.expand_if_equal(self.g, self.lc, args, depth) {
          insert_one(self, tm);
        }
      }
    }
    if let Some(ids) = self.func_ids.get(&ConstrKind::Func(nr)) {
      for &id in ids {
        let id = &self.identify[id];
        let IdentifyKind::Func { lhs, rhs } = &id.kind else { unreachable!() };
        let mut subst = Subst::new(id.primary.len());
        if subst.eq_term(self.g, self.lc, lhs, tm)
          && subst.check_loci_types(self.g, self.lc, &id.primary)
        {
          let mut widening = true;
          for &(x, y) in &*id.eq_args {
            let (ux, uy) = (Idx::into_usize(x), Idx::into_usize(y));
            assert!(subst.subst_term[uy].is_none());
            widening |= id.primary[uy].is_wider_than(self.g, self.lc, &id.primary[ux]);
            subst.subst_term[uy] = subst.subst_term[ux].clone();
          }
          if widening {
            insert_one(self, subst.inst_term(rhs, depth));
          }
        }
      }
    }
    eq
  }
}

impl VisitMut for InternConst<'_> {
  /// CollectConstInTrm
  fn visit_term(&mut self, tm: &mut Term, depth: u32) {
    let only_constants = std::mem::replace(&mut self.only_constants, true);
    let equals_expansion_level = std::mem::replace(&mut self.equals_expansion_level, 0);
    match tm {
      Term::Locus { .. } | Term::Bound { .. } | Term::FreeVar { .. } | Term::LambdaVar { .. } =>
        self.only_constants = false,
      &mut Term::Constant { nr } => {
        let mut eq = BTreeSet::new();
        if let Some(fv) = &self.lc.fixed_var[nr].def {
          let mut fv = (**fv).clone();
          ExpandPrivFunc { ctx: &self.g.constrs }.visit_term(&mut fv, depth);
          self.visit_term(&mut fv, depth);
          if self.only_constants {
            let Term::Infer { nr } = fv else { unreachable!() };
            eq.insert(nr);
          }
          self.only_constants = true;
        }
        self.collect_infer_const(tm, depth);
        let Term::Infer { nr } = *tm else { unreachable!() };
        self.lc.infer_const.borrow_mut()[nr].eq_const.extend(eq);
      }
      Term::Infer { .. } => {}
      Term::SchemeFunctor { args, .. }
      | Term::Aggregate { args, .. }
      | Term::Selector { args, .. } => {
        self.visit_terms(args, depth);
        self.collect_infer_const(tm, depth)
      }
      Term::PrivFunc { args, value, .. } => {
        self.visit_terms(args, depth);
        self.visit_term(value, depth)
      }
      Term::Functor { args, .. } => {
        self.visit_terms(args, depth);
        if self.only_constants {
          let ic = self.lc.infer_const.borrow();
          match ic.find_index(|a| a.def.cmp(&self.g.constrs, tm, CmpStyle::Strict)) {
            Ok(nr) => *tm = Term::Infer { nr },
            _ => {
              drop(ic);
              self.collect_infer_const(tm, depth);
              let Term::Infer { nr } = *tm else { unreachable!() };
              self.equals_expansion_level = equals_expansion_level;
              let tm = self.lc.infer_const.borrow()[nr].def.clone();
              let eq = self.collect_equals_const(&tm, depth);
              self.lc.infer_const.borrow_mut()[nr].eq_const.extend(eq);
            }
          }
        }
      }
      Term::Numeral { .. } => self.collect_infer_const(tm, depth),
      Term::Choice { ty } => {
        self.visit_type(ty, depth);
        self.collect_infer_const(tm, depth)
      }
      Term::Fraenkel { args, scope, compr } => {
        let mut i = depth;
        for (_, ty) in &mut **args {
          self.visit_type(ty, i);
          i += 1;
        }
        self.visit_term(scope, i);
        self.visit_formula(compr, i);
        self.only_constants = !CheckBound::get(depth, |cb| cb.visit_term(tm, depth));
        if self.only_constants {
          OnVarMut(|n, _| *n -= depth).visit_term(tm, depth);
          self.collect_infer_const(tm, depth)
        }
      }
      Term::EqConst { .. } | Term::It | Term::Qua { .. } =>
        unreachable!("CollectConst::visit_term(EqConst | It | Qua)"),
    }
    self.only_constants &= only_constants;
    self.equals_expansion_level = equals_expansion_level;
  }

  fn visit_attrs(&mut self, attrs: &mut Attrs, depth: u32) {
    attrs.reinsert_all(&self.g.constrs, |attr| self.visit_terms(&mut attr.args, depth))
  }
}

pub struct ExpandConsts<'a>(&'a IdxVec<InferId, Assignment>);
impl LocalContext {
  pub fn expand_consts(&self, f: impl FnOnce(&mut ExpandConsts<'_>)) {
    f(&mut ExpandConsts(&self.infer_const.borrow().vec))
  }
}

impl VisitMut for ExpandConsts<'_> {
  /// ExpandInferConsts
  fn visit_term(&mut self, tm: &mut Term, depth: u32) {
    if let Term::Infer { nr } = *tm {
      *tm = (*self.0[nr].def).clone();
      OnVarMut(|v, _| *v += depth).visit_term(tm, depth)
    }
    self.super_visit_term(tm, depth);
  }
}

struct Renumber(HashMap<InferId, InferId>);

impl Renumber {
  fn is_empty(&self) -> bool { self.0.is_empty() }
}

impl VisitMut for Renumber {
  fn visit_term(&mut self, tm: &mut Term, depth: u32) {
    self.super_visit_term(tm, depth);
    if let Term::Infer { nr } = tm {
      if let Some(&nr2) = self.0.get(nr) {
        *nr = nr2;
      }
    }
  }
}

#[derive(Debug)]
struct FixedVar {
  // ident: u32,
  ty: Box<Type>,
  // exp: bool,
  def: Option<Box<Term>>,
  // skel_const: u32,
}

#[derive(Debug)]
struct Assignment {
  /// Must be Term::Functor
  def: Box<Term>,
  ty: Box<Type>,
  eq_const: BTreeSet<InferId>,
  // numeric_value: Option<Complex>,
}
impl<V: VisitMut> Visitable<V> for Assignment {
  fn visit(&mut self, v: &mut V) {
    self.def.visit(v);
    self.ty.visit(v);
  }
}

#[derive(Debug)]
struct FuncDef {
  value: Term,
  ty: Type,
}

#[derive(Debug)]
pub struct Global {
  reqs: RequirementIndexes,
  constrs: Constructors,
  clusters: Clusters,
  nonzero_type: Type,
  /// ItIsChecker in mizar
  recursive_round_up: bool,
  /// AfterClusters
  rounded_up_clusters: bool,
}

#[derive(Default)]
pub struct LocalContext {
  /// LocArgTyp
  // FIXME: this is non-owning in mizar
  locus_ty: IdxVec<LocusId, Type>,
  /// BoundVarNbr, BoundVar
  bound_var: IdxVec<BoundId, Type>,
  /// FixedVar
  fixed_var: IdxVec<ConstantId, FixedVar>,
  /// InferConstDef
  /// sorted by Assignment::def (by CmpStyle::Strict)
  infer_const: RefCell<SortedIdxVec<InferId, Assignment>>,
  sch_func_ty: IdxVec<SchFuncId, Type>,
  /// LocFuncDef
  priv_func: IdxVec<PrivFuncId, FuncDef>,
  /// gTermCollection
  term_cache: RefCell<TermCollection>,
  /// ItTyp
  it_type: Option<Box<Type>>,
}

impl LocalContext {
  /// gTermCollection.FreeAll
  fn clear_term_cache(&self) { self.term_cache.borrow_mut().clear() }

  fn load_locus_tys(&mut self, tys: &[Type]) { self.locus_ty.0.extend_from_slice(tys); }

  fn unload_locus_tys(&mut self) {
    self.locus_ty.0.clear();
    self.clear_term_cache()
  }

  fn with_locus_tys<R>(&mut self, tys: &[Type], f: impl FnOnce(&mut Self) -> R) -> R {
    self.load_locus_tys(tys);
    let r = f(self);
    self.unload_locus_tys();
    r
  }

  /// FreeConstDef
  fn truncate_infer_const(
    &mut self, ctx: &Constructors, check_for_local_const: bool, len: usize,
  ) -> Renumber {
    let ic = self.infer_const.get_mut();
    let mut renumber = Renumber(HashMap::new());
    if len >= ic.0.len() {
      return renumber
    }
    if !check_for_local_const {
      ic.truncate(len);
      return renumber
    }
    let mut old: Vec<_> = ic.vec.0.drain(len..).collect();
    ic.sorted.retain(|t| Idx::into_usize(*t) < len);
    assert!(ic.sorted.len() == len);
    let mut has_local_const = HashSet::<InferId>::new();
    // vprintln!("start loop {} -> {}", len, old.len());
    'retry: loop {
      for (i, asgn) in old.iter().enumerate() {
        let i = Idx::from_usize(len + i);
        if has_local_const.contains(&i) {
          continue
        }
        struct CheckForLocalConst<'a> {
          has_local_const: &'a HashSet<InferId>,
          num_consts: u32,
          found: bool,
        }
        impl Visit for CheckForLocalConst<'_> {
          fn abort(&self) -> bool { self.found }
          fn visit_term(&mut self, tm: &Term, depth: u32) {
            self.super_visit_term(tm, depth);
            match tm {
              Term::Constant { nr } => self.found |= nr.0 >= self.num_consts,
              Term::Infer { nr } => self.found |= self.has_local_const.contains(nr),
              _ => {}
            }
          }
        }
        let mut cc = CheckForLocalConst {
          has_local_const: &has_local_const,
          num_consts: self.fixed_var.len() as u32,
          found: false,
        };
        cc.visit_term(&asgn.def, 0);
        cc.visit_type(&asgn.ty, 0);
        if cc.found {
          has_local_const.insert(i);
          continue 'retry
        }
      }
      break
    }
    // vprintln!("done loop {} -> {}", len, old.len());
    let mut i = Idx::from_usize(len);
    for asgn in old {
      if !has_local_const.contains(&i) {
        match ic.find_index(|a| a.def.cmp(ctx, &asgn.def, CmpStyle::Strict)) {
          Ok(nr) => renumber.0.insert(i, nr),
          Err(idx) => {
            let j = ic.insert_at(idx, asgn);
            // eprintln!("reinsert ?{i:?} => ?{j:?} : {:?} := {:?}", ic[j].ty, ic[j].def);
            renumber.0.insert(i, j)
          }
        };
      }
      i.0 += 1;
    }
    if !renumber.is_empty() {
      for asgn in &mut ic.0[len..] {
        asgn.visit(&mut renumber);
      }
    }
    for asgn in &mut ic.0 {
      if asgn.eq_const.iter().any(|n| renumber.0.contains_key(n)) {
        for n in std::mem::take(&mut asgn.eq_const) {
          if let Some(&n2) = renumber.0.get(&n) {
            asgn.eq_const.insert(n2);
          } else if Idx::into_usize(n) < len {
            asgn.eq_const.insert(n);
          }
        }
      }
    }
    renumber
  }
}

fn load(path: &MizPath, stats: &mut HashMap<&'static str, u32>) {
  // MizPBlockObj.InitPrepData
  let mut refs = References::default();
  path.read_ref(&mut refs).unwrap();

  // Load_EnvConstructors
  let mut reqs = RequirementIndexes::default();
  path.read_ere(&mut reqs).unwrap();
  let mut has_omega = false;
  let nonzero_type = if let (Some(element), Some(omega)) = (reqs.element(), reqs.omega()) {
    has_omega = true;
    Type {
      kind: TypeKind::Mode(element),
      attrs: Default::default(),
      args: Box::new([Term::Functor { nr: omega, args: Box::new([]) }]),
    }
  } else {
    Type::new(reqs.set().into())
  };
  let mut v = Verifier::new(reqs, nonzero_type, path.0);
  path.read_atr(&mut v.g.constrs).unwrap();
  path.read_ecl(&v.g.constrs, &mut v.g.clusters).unwrap();
  let mut attrs = Attrs::default();
  if let Some(zero) = v.g.reqs.zero() {
    attrs.push(Attr { nr: zero, pos: false, args: Box::new([]) })
  }
  if has_omega {
    if let Some(positive) = v.g.reqs.positive() {
      attrs.push(Attr { nr: positive, pos: true, args: Box::new([]) })
    }
  }
  attrs.round_up_with(&v.g, &v.lc, &v.g.nonzero_type);
  v.g.nonzero_type.attrs.1 = attrs;
  v.lc.clear_term_cache();
  v.g.round_up_clusters(&mut v.lc);

  // LoadEqualities
  path.read_definitions(&v.g.constrs, "dfe", &mut v.equalities);

  // LoadExpansions
  path.read_definitions(&v.g.constrs, "dfx", &mut v.expansions);

  // LoadPropertiesReg
  path.read_epr(&v.g.constrs, &mut v.properties);

  // LoadIdentify
  path.read_eid(&v.g.constrs, &mut v.identifications);

  // LoadReductions
  path.read_erd(&v.g.constrs, &mut v.reductions);

  for df in &v.equalities {
    if let Some(func) = df.equals_expansion() {
      let nr = func.pattern.0;
      if !func.expansion.has_func(&v.g.constrs, nr) {
        v.equals.entry(df.constr).or_default().push(func);
      }
    }
  }

  for id in &mut v.identifications {
    for i in 0..id.primary.len() {
      v.lc.load_locus_tys(&id.primary);
      id.primary[i].round_up_with_self(&v.g, &v.lc);
      v.lc.unload_locus_tys();
    }
  }

  for (i, id) in v.identifications.iter().enumerate() {
    if let IdentifyKind::Func { lhs: Term::Functor { nr, args }, rhs } = &id.kind {
      let k = ConstrKind::Func(Term::adjust(*nr, args, &v.g.constrs).0);
      v.func_ids.entry(k).or_default().push(i);
    }
  }

  // CollectConstInEnvConstructors
  let mut cc = v.intern_const();
  let nonzero_type = v.g.nonzero_type.visit_cloned(&mut cc);
  let constrs = v.g.constrs.visit_cloned(&mut cc);
  let mut clusters = v.g.clusters.clone();
  clusters.registered.iter_mut().for_each(|c| c.consequent.1.visit(&mut cc));
  clusters.conditional.iter_mut().for_each(|c| c.consequent.1.visit(&mut cc));
  // note: collecting in the functor term breaks the sort order
  clusters.functor.vec.0.iter_mut().for_each(|c| c.consequent.1.visit(&mut cc));
  v.g.nonzero_type = nonzero_type;
  v.g.constrs = constrs;
  v.g.clusters = clusters;

  let mut props = PropList::default();
  // let mut loc_func = vec![];

  // InLibraries
  path.read_eth(&v.g.constrs, &refs, &mut v.libs).unwrap();
  let mut cc = InternConst::new(&v.g, &v.lc, &v.equals, &v.identifications, &v.func_ids);
  v.libs.thm.values_mut().for_each(|f| cc.visit_formula(f, 0));
  v.libs.def.values_mut().for_each(|f| cc.visit_formula(f, 0));
  const ONLY_THEOREMS: bool = true;
  if !ONLY_THEOREMS {
    path.read_esh(&v.g.constrs, &refs, &mut v.libs).unwrap();
  }

  // Prepare
  let r = path.read_xml().unwrap();
  println!("parsed {:?}, {} items", path.0, r.len());
  for (i, it) in r.iter().enumerate() {
    assert!(matches!(
      it,
      Item::AuxiliaryItem(_)
        | Item::Scheme(_)
        | Item::Theorem { .. }
        | Item::DefTheorem { .. }
        | Item::Reservation { .. }
        | Item::Canceled(_)
        | Item::Definiens(_)
        | Item::Block { .. }
    ));
    // stat(s);
    set_verbose(i >= 210);
    // eprintln!("item {i}");
    v.read_item(it);
  }
}

pub fn stat(s: &'static str) {
  *STATS.lock().unwrap().get_or_insert_with(HashMap::new).entry(s).or_default() += 1;
}

#[macro_export]
macro_rules! vprintln {
  ($($args:tt)*) => {
    if verbose() {
      eprintln!($($args)*)
    }
  };
}

static VERBOSE: AtomicBool = AtomicBool::new(false);
pub fn verbose() -> bool { VERBOSE.load(std::sync::atomic::Ordering::SeqCst) }
pub fn set_verbose(b: bool) { VERBOSE.store(b, std::sync::atomic::Ordering::SeqCst) }

static CALLS: AtomicU32 = AtomicU32::new(0);
static CALLS2: AtomicU32 = AtomicU32::new(0);
static STATS: Mutex<Option<HashMap<&'static str, u32>>> = Mutex::new(None);

fn print_stats_and_exit() {
  let mut g = STATS.lock().unwrap();
  let mut vec: Vec<_> = g.get_or_insert_with(HashMap::new).iter().collect();
  vec.sort();
  for (s, i) in vec {
    println!("{s}: {i}");
  }
  std::process::exit(0)
}

fn main() {
  ctrlc::set_handler(print_stats_and_exit).expect("Error setting Ctrl-C handler");
  // set_verbose(true);

  let mut stats = Default::default();
  for (i, s) in std::fs::read_to_string("../mizshare/mml.lar").unwrap().lines().enumerate().skip(0)
  //.skip(1).take(1)
  {
    println!("{}: {}", i, s);
    let path = MizPath::new(s);
    load(&path, &mut stats);
  }
  // let path = MizPath("../mizshare/mml/xcmplx_0".into());
  // load(&path);
  print_stats_and_exit();
}
