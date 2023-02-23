use crate::types::*;
use crate::{LocalContext, MizPath};
use pretty::{Arena, DocAllocator, DocBuilder};
use std::borrow::Cow;
use std::cell::Cell;
use std::collections::HashMap;

const ENABLE_FORMATTER: bool = true;
const SHOW_INFER: bool = false;
const SHOW_ONLY_INFER: bool = false;
const SHOW_PRIV: bool = false;
const SHOW_MARKS: bool = false;
const SHOW_INVISIBLE: bool = false;
const SHOW_ORIG: bool = false;
const UPPER_CLUSTERS: bool = false;
const BOTH_CLUSTERS: bool = false;
const NEGATION_SUGAR: bool = true;

#[derive(Default, Debug)]
pub struct Formatter {
  symbols: HashMap<SymbolKind, String>,
  formats: IdxVec<FormatId, Format>,
  mode: HashMap<ModeId, (u8, Box<[LocusId]>, FormatMode)>,
  struct_mode: HashMap<StructId, (u8, Box<[LocusId]>, FormatStruct)>,
  attr: HashMap<AttrId, (u8, Box<[LocusId]>, FormatAttr)>,
  pred: HashMap<PredId, (u8, Box<[LocusId]>, FormatPred)>,
  func: HashMap<FuncId, (u8, Box<[LocusId]>, FormatFunc)>,
  sel: HashMap<SelId, (u8, Box<[LocusId]>, SelSymId)>,
  aggr: HashMap<AggrId, (u8, Box<[LocusId]>, FormatAggr)>,
}

impl Formatter {
  pub fn push(&mut self, ctx: &Constructors, pat: &Pattern) {
    if !ENABLE_FORMATTER {
      return
    }
    if crate::DUMP_FORMATTER {
      eprintln!("{pat:#?}")
    }
    fn ins<I: Idx, F: std::fmt::Debug>(
      c: &Constructor<I>, map: &mut HashMap<I, (u8, Box<[LocusId]>, F)>, pat: &Pattern, i: I, f: F,
    ) {
      if pat.pos {
        assert!(pat.visible.iter().all(|i| (i.0 as usize) < pat.primary.len()));
        let mut visible = pat.visible.clone();
        let extra = pat.primary.len() - c.primary.len();
        if extra > 0 {
          visible.iter_mut().for_each(|n| n.0 -= extra as u8);
        }
        map.entry(i).or_insert((c.primary.len() as u8, visible, f));
      }
    }
    match (&pat.kind, self.formats[pat.fmt]) {
      (&PatternKind::Mode(n), Format::Mode(f)) => ins(&ctx.mode[n], &mut self.mode, pat, n, f),
      (&PatternKind::Struct(n), Format::Struct(f)) =>
        ins(&ctx.struct_mode[n], &mut self.struct_mode, pat, n, f),
      (&PatternKind::Attr(n), Format::Attr(f)) => ins(&ctx.attribute[n], &mut self.attr, pat, n, f),
      (&PatternKind::Pred(n), Format::Pred(f)) => ins(&ctx.predicate[n], &mut self.pred, pat, n, f),
      (&PatternKind::Func(n), Format::Func(f)) => ins(&ctx.functor[n], &mut self.func, pat, n, f),
      (&PatternKind::Sel(n), Format::Sel(f)) => ins(&ctx.selector[n], &mut self.sel, pat, n, f),
      (&PatternKind::Aggr(n), Format::Aggr(f)) => ins(&ctx.aggregate[n], &mut self.aggr, pat, n, f),
      (PatternKind::SubAggr(_), _) => {}            // unused
      (PatternKind::ExpandableMode { .. }, _) => {} // not handled here
      _ => panic!("incompatible format for pattern"),
    }
  }

  pub fn extend(&mut self, ctx: &Constructors, pats: &[Pattern]) {
    pats.iter().for_each(|pat| self.push(ctx, pat))
  }

  pub fn init(&mut self, path: &MizPath, formats: Option<IdxVec<FormatId, Format>>) {
    if !ENABLE_FORMATTER {
      return
    }
    let mut symbols = Default::default();
    path.read_dcx(&mut symbols).unwrap();
    self.symbols = symbols.0.into_iter().collect();
    self.formats = formats.unwrap_or_else(|| {
      let mut formats = Default::default();
      path.read_formats("frx", &mut formats).unwrap();
      formats.formats
    });
    for f in &self.formats.0 {
      match f {
        Format::Aggr(f) => assert!(self.symbols.contains_key(&f.sym.into())),
        &Format::SubAggr(sym) => assert!(self.symbols.contains_key(&sym.into())),
        Format::Struct(f) => assert!(self.symbols.contains_key(&f.sym.into())),
        Format::Mode(f) => assert!(self.symbols.contains_key(&f.sym.into())),
        &Format::Sel(sym) => assert!(self.symbols.contains_key(&sym.into())),
        Format::Attr(f) => assert!(self.symbols.contains_key(&f.sym.into())),
        &Format::Func(FormatFunc::Func { sym, .. }) =>
          assert!(self.symbols.contains_key(&sym.into())),
        &Format::Func(FormatFunc::Bracket { lsym, rsym, .. }) => assert!(
          self.symbols.contains_key(&lsym.into()) && self.symbols.contains_key(&rsym.into())
        ),
        Format::Pred(f) => assert!(self.symbols.contains_key(&f.sym.into())),
      }
    }
  }
}

impl Formula {
  fn is_positive(&self, pos: bool) -> bool {
    match self {
      Formula::Neg { f } => f.is_positive(!pos),
      Formula::And { args } => args.iter().all(|f| f.is_positive(pos)),
      Formula::ForAll { scope, .. } | Formula::FlexAnd { scope, .. } => scope.is_positive(pos),
      Formula::LegacyFlexAnd { orig } => orig.iter().all(|f| f.is_positive(pos)),
      _ => pos,
    }
  }
}

thread_local! {
  static LOCAL_CONTEXT: Cell<*const LocalContext> = Cell::new(std::ptr::null());
}

impl LocalContext {
  // pub fn pp<'a, T>(&'a self, t: &'a T) -> Print<'a, T> { Print(Some(self), t) }

  pub fn start_stash(&self) -> *const Self { LOCAL_CONTEXT.with(|lc| lc.replace(self)) }
  pub fn end_stash(old: *const Self) { LOCAL_CONTEXT.with(|lc| lc.set(old)); }

  pub fn stash<R>(&self, f: impl FnOnce() -> R) -> R {
    let old = self.start_stash();
    let r = f();
    Self::end_stash(old);
    r
  }

  pub fn with<R>(f: impl FnOnce(Option<&Self>) -> R) -> R {
    LOCAL_CONTEXT.with(|lc| f(unsafe { lc.get().as_ref() }))
  }
}

struct Pretty<'a> {
  lc: Option<&'a LocalContext>,
  arena: &'a Arena<'a>,
  comma: Doc<'a>,
}

impl Pretty<'_> {
  fn with_lc<R>(lc: Option<&LocalContext>, f: impl for<'b> FnOnce(&'b Pretty<'b>) -> R) -> R {
    let arena = Arena::new();
    f(&Pretty { lc, arena: &arena, comma: arena.text(",").append(arena.line()) })
  }

  fn with<R>(f: impl for<'b> FnOnce(&'b Pretty<'b>) -> R) -> R {
    LocalContext::with(|lc| Self::with_lc(lc, f))
  }
}

impl<'a> std::ops::Deref for Pretty<'a> {
  type Target = &'a Arena<'a>;
  fn deref(&self) -> &Self::Target { &self.arena }
}

type Doc<'a> = DocBuilder<'a, Arena<'a>>;

impl<'a> Pretty<'a> {
  fn commas(&self, docs: impl IntoIterator<Item = Doc<'a>>) -> Doc<'a> {
    self.intersperse(docs, self.comma.clone()).nest(2).group()
  }
  fn terms(&self, vis: Option<&[LocusId]>, tms: &[Term], depth: u32, lift: u32) -> Doc<'a> {
    match vis {
      Some(vis) =>
        self.commas(vis.iter().map(|&i| self.term(false, &tms[i.0 as usize], depth, lift))),
      None => self.commas(tms.iter().map(|tm| self.term(false, tm, depth, lift))),
    }
  }

  fn parens_if(&self, prec: bool, doc: Doc<'a>) -> Doc<'a> {
    if prec {
      doc.parens()
    } else {
      doc
    }
  }

  #[allow(clippy::too_many_arguments)]
  fn infix_term(
    &self, prec: bool, len: u8, vis: &[LocusId], orig: u32, sym: SymbolKind, left: u8, right: u8,
    args: &[Term], depth: u32, lift: u32,
  ) -> Doc<'a> {
    let lc = self.lc.unwrap();
    assert_eq!(len as usize, args.len());
    let vis = (!SHOW_INVISIBLE || vis.len() == args.len()).then_some(vis);
    let (left, right) = if let Some(vis) = vis {
      assert_eq!(vis.len(), (left + right) as usize);
      (left, right)
    } else {
      (0, args.len() as u8)
    };
    let doc = match (left, vis) {
      (_, None) | (0, _) => self.nil(),
      (1, Some(vis)) => self.term(true, &args[vis[0].0 as usize], depth, lift).append(self.space()),
      (_, Some(vis)) =>
        self.terms(Some(&vis[..left as usize]), args, depth, lift).parens().append(self.space()),
    };
    let doc = if SHOW_ORIG {
      doc.append(self.text(format!("{}[{}]", &lc.formatter.symbols[&sym], orig)))
    } else {
      doc.append(self.text(&lc.formatter.symbols[&sym]))
    };
    let doc = match right {
      0 => doc,
      1 => {
        let i = vis.map_or(0, |v| v[left as usize].0 as usize);
        doc.append(self.line()).append(self.term(true, &args[i], depth, lift))
      }
      _ => doc
        .append(self.line())
        .append(self.terms(vis.map(|v| &v[left as usize..]), args, depth, lift).parens()),
    };
    let doc = doc.group();
    return if prec && left + right != 0 { doc.parens() } else { doc }
  }

  fn term(&self, prec: bool, tm: &Term, depth: u32, lift: u32) -> Doc<'a> {
    match tm {
      Term::Locus(nr) => self.text(format!("a{}", nr.0)),
      Term::Bound(nr) => self.text(format!("b{}", nr.0 + lift)),
      Term::Constant(nr) => self.text(format!("c{}", nr.0)),
      Term::EqClass(nr) => self.text(format!("e{}", nr.0)),
      Term::EqMark(nr) => {
        if let Some(lc) = self.lc {
          return if SHOW_MARKS {
            self.text(format!("{:?}'", lc.marks[*nr].1)).append(self.term(
              true,
              &lc.marks[*nr].0,
              depth,
              lift,
            ))
          } else {
            self.term(prec, &lc.marks[*nr].0, depth, lift)
          }
        }
        self.text(format!("m{}", nr.0))
      }
      Term::Infer(nr) => {
        if !SHOW_ONLY_INFER {
          if let Some(ic) = self.lc.and_then(|lc| lc.infer_const.try_borrow().ok()) {
            return if SHOW_INFER {
              let doc = self.term(true, &ic[*nr].def, depth, depth);
              self.text(format!("?{}=", nr.0)).append(doc)
            } else {
              self.term(prec, &ic[*nr].def, depth, depth)
            }
          }
        }
        self.text(format!("?{}", nr.0))
      }
      Term::SchFunc { nr, args } =>
        self.text(format!("S{}", nr.0)).append(self.terms(None, args, depth, lift).parens()),
      Term::Aggregate { nr, args } => {
        let (mut doc, mut ovis) = (None, None);
        if let Some(lc) = self.lc {
          if let Some(&(len, ref vis, FormatAggr { sym, args: n })) = lc.formatter.aggr.get(nr) {
            assert_eq!(len as usize, args.len());
            assert_eq!(vis.len(), n as usize);
            doc = Some(if SHOW_ORIG {
              self.text(format!("{}[{}]", lc.formatter.symbols[&sym.into()], nr.0))
            } else {
              self.text(&lc.formatter.symbols[&sym.into()])
            });
            ovis = Some(&**vis)
          }
        }
        let doc = doc.unwrap_or_else(|| self.text(format!("G{}", nr.0)));
        self.terms(ovis, args, depth, lift).enclose(doc.append("(#"), "#)")
      }
      Term::PrivFunc { nr, args, value } => {
        let doc =
          self.text(format!("$F{}", nr.0)).append(self.terms(None, args, depth, lift).parens());
        if SHOW_PRIV {
          doc.append("=").append(self.term(true, value, depth, lift))
        } else {
          doc
        }
      }
      Term::Functor { nr, args } => {
        if let Some(lc) = self.lc {
          match lc.formatter.func.get(nr) {
            Some(&(len, ref vis, FormatFunc::Func { sym, left, right })) => {
              let sym = sym.into();
              return self.infix_term(prec, len, vis, nr.0, sym, left, right, args, depth, lift)
            }
            Some(&(len, ref vis, FormatFunc::Bracket { lsym, rsym, args: n })) => {
              assert_eq!(len as usize, args.len());
              assert_eq!(vis.len(), n as usize);
              let left = if SHOW_ORIG {
                self.text(format!("{}[{}] ", &lc.formatter.symbols[&lsym.into()], nr.0))
              } else {
                self.text(&*lc.formatter.symbols[&lsym.into()])
              };
              return self
                .terms(Some(vis), args, depth, lift)
                .enclose(left, &lc.formatter.symbols[&rsym.into()])
            }
            None => {}
          }
        }
        let doc = self.text(format!("F{}", nr.0));
        match args.len() {
          0 => doc,
          _ => doc.append(self.terms(None, args, depth, lift).parens()),
        }
      }
      Term::Numeral(nr) => self.as_string(nr),
      Term::Selector { nr, args } => {
        let (mut s, mut ovis) = (None, None);
        if let Some(lc) = self.lc {
          if let Some(&(len, ref vis, sym)) = lc.formatter.sel.get(nr) {
            assert_eq!(len as usize, args.len());
            assert_eq!(vis.len(), 1);
            ovis = Some(&**vis);
            s = Some(&lc.formatter.symbols[&sym.into()]);
          }
        }
        let doc = self.text(match s {
          Some(sym) if SHOW_ORIG => format!("the {sym}[{}] of", nr.0),
          Some(sym) => format!("the {sym} of"),
          None => format!("the Sel{} of", nr.0),
        });
        let doc = doc.append(self.line()).append(self.terms(ovis, args, depth, lift)).group();
        self.parens_if(prec, doc)
      }
      Term::FreeVar(nr) => self.text(format!("v{}", nr.0)),
      Term::The { ty } =>
        self.parens_if(prec, self.text("the ").append(self.ty(ty, depth, lift)).group()),
      Term::Fraenkel { args, scope, compr } => {
        let doc = self.term(false, scope, depth + args.len() as u32, lift).append(self.line());
        let inner = self
          .text("where ")
          .append(self.commas(args.iter().enumerate().map(|(i, ty)| {
            let doc = self.ty(ty, depth + i as u32, lift);
            self.text(format!("b{}: ", depth + i as u32)).append(doc)
          })))
          .append(" : ")
          .append(self.formula(false, true, compr, depth + args.len() as u32, lift))
          .nest(2)
          .group();
        doc.append(inner).group().braces()
      }
      Term::Qua { value, ty } => {
        let doc = self
          .term(true, value, depth, lift)
          .append(self.line())
          .append("qua ")
          .append(self.ty(ty, depth, lift))
          .group();
        self.parens_if(prec, doc)
      }
      Term::It => self.text("it"),
    }
  }

  fn adjective(&self, nr: AttrId, args: &[Term], depth: u32, lift: u32) -> Doc<'a> {
    if let Some(lc) = self.lc {
      if let Some(&(len, ref vis, FormatAttr { sym, args: n })) = lc.formatter.attr.get(&nr) {
        assert_eq!(len as usize, args.len() + 1);
        assert_eq!(vis.len(), n as usize);
        let (v0, vis) = vis.split_last().unwrap();
        assert_eq!(v0.0 as usize, args.len());
        let vis = (!SHOW_INVISIBLE || vis.len() == args.len()).then_some(vis);
        let sym = if SHOW_ORIG {
          self.text(format!("{}[{}]", lc.formatter.symbols[&sym.into()], nr.0))
        } else {
          self.text(&lc.formatter.symbols[&sym.into()])
        };
        return match (vis, args) {
          (None, []) | (Some([]), _) => sym,
          (Some(&[v]), _) => self.term(true, &args[v.0 as usize], depth, lift).append(sym),
          (Some(vis), _) => self.terms(Some(vis), args, depth, lift).parens().append(sym),
          (None, _) => sym.append(self.terms(None, args, depth, lift).parens()),
        }
      }
    }
    let doc = self.text(format!("A{}", nr.0));
    match args.len() {
      0 => doc,
      _ => doc.append(self.terms(None, args, depth, lift).parens()),
    }
  }

  fn attr(&self, attr: &Attr, plus: bool, depth: u32, lift: u32) -> Doc<'a> {
    if plus { self.text("+") } else { self.nil() }
      .append(if attr.pos { self.nil() } else { self.text("non ") })
      .append(self.adjective(attr.nr, &attr.args, depth, lift))
  }

  fn attrs(&self, attrs: &Attrs, plus: bool, depth: u32, lift: u32) -> Doc<'a> {
    match attrs {
      Attrs::Inconsistent => self.text("false").append(self.space()),
      Attrs::Consistent(attrs) =>
        self.concat(attrs.iter().map(|a| self.attr(a, plus, depth, lift).append(self.softline()))),
    }
  }

  fn ty(&self, ty: &Type, depth: u32, lift: u32) -> Doc<'a> {
    let (mut ovis, mut s) = (None, None);
    if let Some(lc) = self.lc {
      match ty.kind {
        TypeKind::Struct(n) =>
          if let Some(&(len, ref vis, FormatStruct { sym, args })) =
            lc.formatter.struct_mode.get(&n)
          {
            assert_eq!(len as usize, ty.args.len());
            assert_eq!(vis.len(), args as usize);
            ovis = (!SHOW_INVISIBLE || vis.len() == ty.args.len()).then_some(&**vis);
            s = Some(if SHOW_ORIG {
              Cow::Owned(format!("{}({})", &*lc.formatter.symbols[&sym.into()], n.0))
            } else {
              Cow::Borrowed(&*lc.formatter.symbols[&sym.into()])
            })
          },
        TypeKind::Mode(n) =>
          if let Some(&(len, ref vis, FormatMode { sym, args })) = lc.formatter.mode.get(&n) {
            assert_eq!(len as usize, ty.args.len());
            assert_eq!(vis.len(), args as usize);
            ovis = (!SHOW_INVISIBLE || vis.len() == ty.args.len()).then_some(&**vis);
            s = Some(if SHOW_ORIG {
              Cow::Owned(format!("{}[{}]", &*lc.formatter.symbols[&sym.into()], n.0))
            } else {
              Cow::Borrowed(&*lc.formatter.symbols[&sym.into()])
            })
          },
      }
    }
    let doc = if BOTH_CLUSTERS {
      self.attrs(&ty.attrs.0, false, depth, lift).append(self.attrs(&ty.attrs.1, true, depth, lift))
    } else {
      let attrs = if UPPER_CLUSTERS { &ty.attrs.1 } else { &ty.attrs.0 };
      self.attrs(attrs, UPPER_CLUSTERS, depth, lift)
    };
    let doc = doc.append(match s {
      Some(sym) => self.text(sym),
      None => self.text(format!("{:?}", ty.kind)),
    });
    let doc = match ovis.map_or(ty.args.len(), |vis| vis.len()) {
      0 => doc,
      n => {
        let of = match ty.kind {
          TypeKind::Mode(_) => " of ",
          TypeKind::Struct(_) => " over ",
        };
        doc.append(of).append(self.parens_if(n != 1, self.terms(ovis, &ty.args, depth, lift)))
      }
    };
    doc.group()
  }

  fn formula(&self, prec: bool, pos: bool, fmla: &Formula, depth: u32, lift: u32) -> Doc<'a> {
    match (pos, fmla) {
      (false, _) if !NEGATION_SUGAR =>
        self.text("¬").append(self.formula(true, true, fmla, depth, lift)),
      (pos, Formula::Neg { f }) => self.formula(prec, !pos, f, depth, lift),
      (false, Formula::And { args }) => {
        let i = args.iter().position(|f| f.is_positive(false)).unwrap_or(args.len() - 1);
        let lhs = if i > 0 {
          let sep = self.text(" ∧").append(self.line());
          let doc = self
            .intersperse(args[..i].iter().map(|f| self.formula(true, true, f, depth, lift)), sep);
          doc.append(" →").append(self.line())
        } else {
          self.nil()
        };
        let sep = self.text(" ∨").append(self.line());
        let doc = self
          .intersperse(args[i..].iter().map(|f| self.formula(true, false, f, depth, lift)), sep);
        self.parens_if(prec, lhs.append(doc).nest(2).group())
      }
      (true, Formula::And { args }) => {
        let sep = self.text(" ∧").append(self.line());
        let doc =
          self.intersperse(args.iter().map(|f| self.formula(true, true, f, depth, lift)), sep);
        self.parens_if(prec, doc.nest(2).group())
      }
      (pos, Formula::ForAll { .. }) => {
        let mut f = fmla;
        let mut depth = depth;
        let iter = std::iter::from_fn(|| {
          if let Formula::ForAll { dom, scope } = f {
            let doc = self.text(format!(" b{depth}: ")).append(self.ty(dom, depth, lift));
            f = scope;
            depth += 1;
            Some(doc)
          } else {
            None
          }
        });
        let doc = self
          .text(if pos { "∀" } else { "∃" })
          .append(self.intersperse(iter, self.text(",")).group())
          .append(if pos { " holds" } else { " st" })
          .append(self.line().append(self.formula(false, pos, f, depth, lift)).nest(2));
        self.parens_if(prec, doc.group())
      }
      (pos, Formula::FlexAnd { terms, scope }) => {
        let doc = self
          .text(format!("{} [b{depth}=", if pos { "⋀" } else { "⋁" }))
          .append(self.term(false, &terms[0], depth, lift))
          .append(" to ")
          .append(self.term(false, &terms[1], depth, lift))
          .append("]")
          .append(self.line().append(self.formula(false, pos, scope, depth + 1, lift)).nest(2));
        self.parens_if(prec, doc.group())
      }
      (pos, Formula::LegacyFlexAnd { orig }) => {
        let doc = self
          .formula(false, pos, &orig[0], depth, lift)
          .append(if pos { " ∧ ... ∧" } else { " ∨ ... ∨" })
          .append(self.line())
          .append(self.formula(false, pos, &orig[1], depth, lift));
        self.parens_if(prec, doc.group())
      }
      (pos, Formula::True) => self.as_string(pos),
      (true, Formula::SchPred { nr, args }) =>
        self.text(format!("SP{}", nr.0)).append(self.terms(None, args, depth, lift).brackets()),
      (true, Formula::Pred { nr, args }) => {
        if let Some(lc) = self.lc {
          if let Some(&(len, ref vis, FormatPred { sym, left, right })) = lc.formatter.pred.get(nr)
          {
            return self.infix_term(prec, len, vis, nr.0, sym.into(), left, right, args, depth, lift)
          }
        }
        self.text(format!("P{}", nr.0)).append(self.terms(None, args, depth, lift).brackets())
      }
      (true, Formula::Attr { nr, args }) => {
        let (arg0, args) = args.split_last().unwrap();
        let doc = self
          .term(false, arg0, depth, lift)
          .append(" is ")
          .append(self.adjective(*nr, args, depth, lift));
        self.parens_if(prec, doc.group())
      }
      (true, Formula::PrivPred { nr, args, value }) => {
        let doc =
          self.text(format!("$P{}", nr.0)).append(self.terms(None, args, depth, lift).brackets());
        if SHOW_PRIV {
          doc.append("=").append(self.formula(true, true, value, depth, lift))
        } else {
          doc
        }
      }
      (true, Formula::Is { term, ty }) => {
        let doc =
          self.term(false, term, depth, lift).append(" is ").append(self.ty(ty, depth, lift));
        self.parens_if(prec, doc.group())
      }
      (false, _) => self.text("¬").append(self.formula(true, true, fmla, depth, lift)),
    }
  }
}

impl std::fmt::Debug for Term {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    Pretty::with(|p| p.term(false, self, 0, 0).nest(2).render_fmt(100, f))
  }
}
impl std::fmt::Debug for Formula {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    Pretty::with(|p| p.formula(false, true, self, 0, 0).nest(2).render_fmt(100, f))
  }
}
impl std::fmt::Debug for Attr {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    Pretty::with(|p| p.attr(self, false, 0, 0).nest(2).render_fmt(100, f))
  }
}
impl std::fmt::Debug for Attrs {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    Pretty::with(|p| p.attrs(self, false, 0, 0).nest(2).render_fmt(100, f))
  }
}
impl std::fmt::Debug for Type {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    Pretty::with(|p| p.ty(self, 0, 0).nest(2).render_fmt(100, f))
  }
}
