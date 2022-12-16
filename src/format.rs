use crate::types::*;
use crate::{LocalContext, MizPath};
use pretty::{Arena, DocAllocator, DocBuilder, RefDoc};
use std::borrow::Cow;
use std::cell::Cell;
use std::collections::HashMap;

const ENABLE_FORMATTER: bool = true;

#[derive(Default, Debug)]
pub struct Formatter {
  symbols: HashMap<SymbolKind, String>,
  formats: IdxVec<FormatId, Format>,
  mode: HashMap<ModeId, (Box<[u8]>, FormatMode)>,
  struct_mode: HashMap<StructId, (Box<[u8]>, FormatStructMode)>,
  attr: HashMap<AttrId, (Box<[u8]>, FormatAttr)>,
  pred: HashMap<PredId, (Box<[u8]>, FormatPred)>,
  func: HashMap<FuncId, (Box<[u8]>, FormatFunc)>,
  sel: HashMap<SelId, (Box<[u8]>, FormatSel)>,
  aggr: HashMap<AggrId, (Box<[u8]>, FormatAggr)>,
}

impl Formatter {
  pub fn push(&mut self, pat: &Pattern) {
    if !ENABLE_FORMATTER {
      return
    }
    fn ins<I: Idx, F: std::fmt::Debug>(
      map: &mut HashMap<I, (Box<[u8]>, F)>, pat: &Pattern, i: I, f: F,
    ) {
      if pat.pos && pat.redefines.is_none() {
        map.insert(i, (pat.visible.clone(), f));
        // FIXME: this isn't true? Redefinitions are not always marked
        // assert!(map.insert(i, (pat.visible.clone(), f)).is_none())
      }
    }
    match (pat.kind, self.formats[pat.fmt]) {
      (PatternKind::Mode(n), Format::Mode(f)) => ins(&mut self.mode, pat, n, f),
      (PatternKind::Struct(n), Format::Struct(f)) => ins(&mut self.struct_mode, pat, n, f),
      (PatternKind::Attr(n), Format::Attr(f)) => ins(&mut self.attr, pat, n, f),
      (PatternKind::Pred(n), Format::Pred(f)) => ins(&mut self.pred, pat, n, f),
      (PatternKind::Func(n), Format::Func(f)) => ins(&mut self.func, pat, n, f),
      (PatternKind::Sel(n), Format::Sel(f)) => ins(&mut self.sel, pat, n, f),
      (PatternKind::Aggr(n), Format::Aggr(f)) => ins(&mut self.aggr, pat, n, f),
      (PatternKind::ForgetFunc(_), _) => {}  // unused
      (PatternKind::ExpandableMode, _) => {} // not handled here
      _ => panic!("incompatible format for pattern"),
    }
  }

  pub fn extend(&mut self, pats: &[Pattern]) { pats.iter().for_each(|pat| self.push(pat)) }

  pub fn init(&mut self, path: &MizPath) {
    if !ENABLE_FORMATTER {
      return
    }
    let (mut symbols, mut formats, mut notations) = Default::default();
    path.read_dcx(&mut symbols).unwrap();
    self.symbols = symbols.0.into_iter().collect();
    path.read_formats("frx", &mut formats).unwrap();
    self.formats = formats.formats;
    path.read_eno(&mut notations).unwrap();
    self.extend(&notations.0);
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
  fn terms(&self, vis: Option<&[u8]>, tms: &[Term]) -> Doc<'a> {
    match vis {
      Some(vis) => self.commas(vis.iter().map(|&i| self.term(false, &tms[i as usize]))),
      None => self.commas(tms.iter().map(|tm| self.term(false, tm))),
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
    &self, prec: bool, vis: &[u8], sym: SymbolKind, left: u8, right: u8, args: &[Term], k: &str,
    nr: u32,
  ) -> Doc<'a> {
    let lc = self.lc.unwrap();
    assert_eq!(vis.len(), (left + right) as usize);
    let doc = match left {
      0 => self.nil(),
      1 => self.term(true, &args[vis[0] as usize]).append(self.space()),
      _ => self.terms(Some(&vis[..left as usize]), args).parens().append(self.space()),
    };
    let doc = doc.append(match lc.formatter.symbols.get(&sym) {
      Some(sym) => self.text(sym),
      None => self.text(format!("{k}{nr}")),
    });
    let doc = match right {
      0 => doc,
      1 => doc.append(self.line()).append(self.term(true, &args[vis[left as usize] as usize])),
      _ => doc.append(self.line()).append(self.terms(Some(&vis[left as usize..]), args).parens()),
    };
    let doc = doc.group();
    return if prec && left + right != 0 { doc.parens() } else { doc }
  }

  fn term(&self, prec: bool, tm: &Term) -> Doc<'a> {
    match tm {
      Term::Locus(nr) => self.text(format!("a{}", nr.0)),
      Term::Bound(nr) => self.text(format!("b{}", nr.0)),
      Term::Constant(nr) => self.text(format!("c{}", nr.0)),
      Term::EqClass(nr) => self.text(format!("e{}", nr.0)),
      Term::EqMark(nr) => {
        if let Some(lc) = self.lc {
          return self.term(prec, &lc.marks[*nr].0)
        }
        self.text(format!("m{}", nr.0))
      }
      Term::Infer(nr) => {
        if let Some(lc) = self.lc {
          return self.term(prec, &lc.infer_const.borrow()[*nr].def)
        }
        self.text(format!("?{}", nr.0))
      }
      Term::SchFunc { nr, args } =>
        self.text(format!("S{}", nr.0)).append(self.terms(None, args).parens()),
      Term::Aggregate { nr, args } => {
        let (mut doc, mut ovis) = (None, None);
        if let Some(lc) = self.lc {
          if let Some(&(ref vis, FormatAggr { sym, args: n })) = lc.formatter.aggr.get(nr) {
            assert_eq!(vis.len(), n as usize);
            doc = lc.formatter.symbols.get(&sym.into()).map(|sym| self.text(sym));
            ovis = Some(&**vis)
          }
        }
        let doc = doc.unwrap_or_else(|| self.text(format!("G{}", nr.0)));
        self.terms(ovis, args).enclose(doc.append("(#"), "#)")
      }
      Term::PrivFunc { nr, args, .. } =>
        self.text(format!("$F{}", nr.0)).append(self.terms(None, args).parens()),
      Term::Functor { nr, args } => {
        let mut ovis = None;
        if let Some(lc) = self.lc {
          match lc.formatter.func.get(nr) {
            Some(&(ref vis, FormatFunc::Func { sym, left, right })) =>
              return self.infix_term(prec, vis, sym.into(), left, right, args, "F", nr.0),
            Some(&(ref vis, FormatFunc::Bracket { lsym, rsym, args: n })) => {
              assert_eq!(vis.len(), n as usize);
              if let Some(lsym) = lc.formatter.symbols.get(&lsym.into()) {
                if let Some(rsym) = lc.formatter.symbols.get(&rsym.into()) {
                  return self.terms(Some(vis), args).enclose(lsym, rsym)
                }
              }
              ovis = Some(&**vis)
            }
            None => {}
          }
        }
        self.text(format!("F{}", nr.0)).append(self.terms(ovis, args).parens())
      }
      Term::Numeral(nr) => self.as_string(nr),
      Term::Selector { nr, args } => {
        let (mut s, mut ovis) = (None, None);
        if let Some(lc) = self.lc {
          if let Some(&(ref vis, FormatSel { sym, args: n })) = lc.formatter.sel.get(nr) {
            assert_eq!(vis.len(), n as usize);
            ovis = Some(&**vis);
            s = lc.formatter.symbols.get(&sym.into());
          }
        }
        let doc = self.text(match s {
          Some(sym) => format!("the {sym} of"),
          None => format!("the Sel{} of", nr.0),
        });
        let doc = doc.append(self.line()).append(self.terms(ovis, args)).group();
        self.parens_if(prec, doc)
      }
      Term::FreeVar(nr) => self.text(format!("v{}", nr.0)),
      Term::LambdaVar(nr) => self.text(format!("l{nr}")),
      Term::Qua { value, ty } => {
        let doc =
          self.term(true, value).append(self.line()).append("qua ").append(self.ty(ty)).group();
        self.parens_if(prec, doc)
      }
      Term::Choice { ty } => self.parens_if(prec, self.text("the ").append(self.ty(ty)).group()),
      Term::Fraenkel { args, scope, compr } => {
        let doc = self.term(false, scope).append(self.line());
        let inner = self
          .text("where ")
          .append(self.commas(args.iter().map(|ty| self.text("_: ").append(self.ty(ty)))))
          .append(" : ")
          .append(self.formula(false, true, compr))
          .nest(2)
          .group();
        doc.append(inner).group().braces()
      }
      Term::It => self.text("it"),
    }
  }

  fn adjective(&self, nr: AttrId, args: &[Term]) -> Doc<'a> {
    if let Some(lc) = self.lc {
      if let Some(&(ref vis, FormatAttr { sym, args: n })) = lc.formatter.attr.get(&nr) {
        assert_eq!(vis.len(), n as usize);
        let (v0, vis) = vis.split_last().unwrap();
        assert_eq!(*v0 as usize, args.len());
        if let Some(sym) = lc.formatter.symbols.get(&sym.into()) {
          return match vis.len() {
            0 => self.text(sym),
            1 => self.term(true, &args[vis[0] as usize]).append(self.text(sym)),
            _ => self.terms(Some(vis), args).parens().append(self.text(sym)),
          }
        }
      }
    }
    match args.len() {
      0 => self.text(format!("A{}", nr.0)),
      _ => self.terms(None, args).parens(),
    }
  }

  fn attr(&self, attr: &Attr) -> Doc<'a> {
    if attr.pos { self.nil() } else { self.text("non ") }
      .append(self.adjective(attr.nr, &attr.args))
  }

  fn attrs(&self, attrs: &Attrs) -> Doc<'a> {
    match attrs {
      Attrs::Inconsistent => self.text("false").append(self.space()),
      Attrs::Consistent(attrs) =>
        self.concat(attrs.iter().map(|a| self.attr(a).append(self.space()))),
    }
  }

  fn ty(&self, ty: &Type) -> Doc<'a> {
    let (mut ovis, mut s) = (None, None);
    if let Some(lc) = self.lc {
      match ty.kind {
        TypeKind::Struct(n) =>
          if let Some(&(ref vis, FormatStructMode { sym, args })) = lc.formatter.struct_mode.get(&n)
          {
            assert_eq!(vis.len(), args as usize);
            ovis = Some(&**vis);
            s = lc.formatter.symbols.get(&sym.into())
          },
        TypeKind::Mode(n) =>
          if let Some(&(ref vis, FormatMode { sym, args })) = lc.formatter.mode.get(&n) {
            assert_eq!(vis.len(), args as usize);
            ovis = Some(&**vis);
            s = lc.formatter.symbols.get(&sym.into())
          },
      }
    }
    let doc = self.attrs(&ty.attrs.0).append(match s {
      Some(sym) => self.text(sym),
      None => self.text(format!("{:?}", ty.kind)),
    });
    let doc = match ovis.map_or(ty.args.len(), |vis| vis.len()) {
      0 => doc,
      _ => doc.append(" of ").append(self.terms(ovis, &ty.args)),
    };
    doc.group()
  }

  fn formula(&self, prec: bool, pos: bool, fmla: &Formula) -> Doc<'a> {
    match (pos, fmla) {
      (pos, Formula::Neg { f }) => self.formula(true, !pos, f),
      (pos, Formula::And { args }) => {
        let sep = self.text(if pos { " ∧" } else { " ∨" }).append(self.line());
        let doc = self.intersperse(args.iter().map(|f| self.formula(true, pos, f)), sep);
        self.parens_if(prec, doc.nest(2).group())
      }
      (true, Formula::And { args }) => {
        let sep = self.text(" ∧").append(self.line());
        let doc = self.intersperse(args.iter().map(|f| self.formula(true, true, f)), sep);
        self.parens_if(prec, doc.nest(2).group())
      }
      (pos, Formula::ForAll { .. }) => {
        let mut f = fmla;
        let iter = std::iter::from_fn(|| {
          if let Formula::ForAll { dom, scope } = f {
            f = scope;
            Some(self.text(" _: ").append(self.ty(dom)))
          } else {
            None
          }
        });
        let doc = self
          .text(if pos { "∀" } else { "∃" })
          .append(self.intersperse(iter, self.text(",")).group())
          .append(if pos { " holds" } else { " st" })
          .append(self.line().append(self.formula(false, pos, f)).nest(2));
        doc.group()
      }
      (pos, Formula::FlexAnd { orig, terms, expansion }) => {
        let doc = self
          .formula(false, pos, &orig[0])
          .append(if pos { " ∧ ... ∧" } else { " ∨ ... ∨" })
          .append(self.line())
          .append(self.formula(false, pos, &orig[1]));
        self.parens_if(prec, doc.group())
      }
      (pos, Formula::True) => self.as_string(pos),
      (true, Formula::SchPred { nr, args }) =>
        self.text(format!("SP{}", nr.0)).append(self.terms(None, args).brackets()),
      (true, Formula::Pred { nr, args }) => {
        let mut ovis = None;
        if let Some(lc) = self.lc {
          if let Some(&(ref vis, FormatPred { sym, left, right })) = lc.formatter.pred.get(nr) {
            return self.infix_term(prec, vis, sym.into(), left, right, args, "P", nr.0)
          }
        }
        self.text(format!("P{}", nr.0)).append(self.terms(ovis, args).brackets())
      }
      (true, Formula::Attr { nr, args }) => {
        let (arg0, args) = args.split_last().unwrap();
        let doc = self.term(false, arg0).append(" is ").append(self.adjective(*nr, args)).group();
        self.parens_if(prec, doc)
      }
      (true, Formula::PrivPred { nr, args, value }) =>
        self.text(format!("$P{}", nr.0)).append(self.terms(None, args).brackets()),
      (true, Formula::Is { term, ty }) => {
        let doc = self.term(false, term).append(" is ").append(self.ty(ty)).group();
        self.parens_if(prec, doc)
      }
      (true, Formula::Thesis) => self.text("thesis"),
      (false, _) => self.text("¬").append(self.formula(true, true, fmla)),
    }
  }
}

impl std::fmt::Debug for Term {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    Pretty::with(|p| p.term(false, self).render_fmt(100, f))
  }
}
impl std::fmt::Debug for Formula {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    Pretty::with(|p| p.formula(false, true, self).render_fmt(100, f))
  }
}
impl std::fmt::Debug for Attr {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    Pretty::with(|p| p.attr(self).render_fmt(100, f))
  }
}
impl std::fmt::Debug for Attrs {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    Pretty::with(|p| p.attrs(self).render_fmt(100, f))
  }
}
impl std::fmt::Debug for Type {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    Pretty::with(|p| p.ty(self).render_fmt(100, f))
  }
}
