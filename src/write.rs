use crate::accom::SigBuilder;
use crate::types::*;
use crate::{Global, LocalContext, MizPath};
use enum_map::{Enum, EnumMap};
use quick_xml::events::attributes::Attribute;
use quick_xml::events::{BytesDecl, BytesEnd, BytesStart, Event};
use std::borrow::Cow;
use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufWriter, ErrorKind, Write};
use std::rc::Rc;

const INDENT: usize = 0;

struct MizWriter {
  w: quick_xml::Writer<BufWriter<File>>,
  pending: Option<Elem>,
  depth: u32,
}

impl MizPath {
  fn create_xml(&self, mml: bool, new_prel: bool, ext: &str) -> io::Result<MizWriter> {
    let w = BufWriter::new(self.create(mml, new_prel, ext)?);
    let mut w = quick_xml::Writer::new_with_indent(w, b' ', INDENT);
    w.write_event(Event::Decl(BytesDecl::new("1.0", None, None))).unwrap();
    Ok(MizWriter { w, pending: None, depth: 0 })
  }

  pub fn write_dfr(&self, new_prel: bool, vocs: &Vocabularies, formats: &[Format]) {
    let mut w = self.create_xml(false, new_prel, "dfr").unwrap();
    w.with0("Formats", |w| {
      w.write_vocabularies(vocs);
      formats.iter().for_each(|fmt| w.write_format(None, fmt));
    });
    w.finish()
  }

  pub fn write_dco(
    &self, new_prel: bool, base: &ConstructorsBase,
    DepConstructors { sig, counts, constrs }: &DepConstructors,
  ) {
    let mut w = self.create_xml(false, new_prel, "dco").unwrap();
    w.with0("Constructors", |w| {
      w.write_signature(sig);
      w.with0("ConstrCounts", |w| {
        w.write_constr_count(b'M', counts.mode);
        w.write_constr_count(b'L', counts.struct_mode);
        w.write_constr_count(b'V', counts.attribute);
        w.write_constr_count(b'R', counts.predicate);
        w.write_constr_count(b'K', counts.functor);
        w.write_constr_count(b'U', counts.selector);
        w.write_constr_count(b'G', counts.aggregate);
      });

      #[derive(Clone, Copy)]
      struct S<'a> {
        art: &'a [u8],
        base: &'a ConstructorsBase,
      }
      impl ForeachConstructor for S<'_> {
        fn foreach<I: Idx, T>(
          self, arr: &IdxVec<I, T>, base: impl Fn(&ConstructorsBase) -> u32,
          mut body: impl FnMut(&[u8], u32, u32, &T),
        ) {
          let base = base(self.base);
          for (i, c) in arr.enum_iter() {
            let i = i.into_usize() as u32;
            body(self.art, i, base + i, c)
          }
        }
      }
      w.write_constructors(
        constrs,
        S { art: self.art.as_str().to_ascii_uppercase().as_bytes(), base },
      )
    });
    w.finish()
  }

  pub fn write_dno(&self, new_prel: bool, DepNotation { sig, vocs, pats }: &DepNotation) {
    let mut w = self.create_xml(false, new_prel, "dno").unwrap();
    w.with0("Notations", |w| {
      w.write_signature(sig);
      w.write_vocabularies(vocs);
      for pat in pats {
        w.write_pattern(pat, None, |_| None, |w, fmt| w.write_format(None, fmt))
      }
    });
    w.finish()
  }

  pub fn write_dcl(&self, new_prel: bool, DepClusters { sig, cl }: &DepClusters) {
    let mut w = self.create_xml(false, new_prel, "dcl").unwrap();
    w.with0("Registrations", |w| {
      w.write_signature(sig);
      let art = self.art.as_str().to_ascii_uppercase();
      let art = art.as_bytes();
      for (i, cl) in cl.registered.iter().enumerate() {
        w.write_cluster("RCluster", art, i, cl, |w| {
          w.write_type(None, &cl.ty);
          w.write_attrs(None, &cl.consequent.0)
        })
      }
      for (i, cl) in cl.functor.iter().enumerate() {
        w.write_cluster("FCluster", art, i, cl, |w| {
          w.write_term(None, &cl.term);
          w.write_attrs(None, &cl.consequent.0);
          if let Some(ty) = &cl.ty {
            w.write_type(None, ty)
          }
        })
      }
      for (i, cl) in cl.conditional.iter().enumerate() {
        w.write_cluster("CCluster", art, i, cl, |w| {
          w.write_attrs(None, &cl.antecedent);
          w.write_type(None, &cl.ty);
          w.write_attrs(None, &cl.consequent.0)
        })
      }
    });
    w.finish()
  }

  pub fn write_def(&self, new_prel: bool, sig: &[Article], def: &[Definiens]) {
    let mut w = self.create_xml(false, new_prel, "def").unwrap();
    w.with0("Definientia", |w| {
      w.write_signature(sig);
      w.write_definitions(false, def)
    });
    w.finish()
  }

  pub fn write_did(&self, new_prel: bool, sig: &[Article], ids: &[IdentifyFunc]) {
    let mut w = self.create_xml(false, new_prel, "did").unwrap();
    w.with0("IdentifyRegistrations", |w| {
      w.write_signature(sig);
      let art = self.art.as_str().to_ascii_uppercase();
      let art = art.as_bytes();
      for (i, id) in ids.iter().enumerate() {
        let attrs = |w: &mut Elem| {
          w.attr(b"aid", art);
          w.attr_str(b"nr", i + 1);
          w.attr(b"constrkind", &b"K"[..]);
        };
        w.with("Identify", attrs, |w| {
          w.write_types(None, &id.primary);
          w.write_term(None, &id.lhs);
          w.write_term(None, &id.rhs);
          w.with0("EqArgs", |w| {
            for &(x, y) in &*id.eq_args {
              w.with_attr("Pair", |w| {
                w.attr_str(b"x", x.0 + 1);
                w.attr_str(b"y", y.0 + 1)
              })
            }
          })
        })
      }
    });
    w.finish()
  }

  pub fn write_drd(&self, new_prel: bool, sig: &[Article], reds: &[Reduction]) {
    let mut w = self.create_xml(false, new_prel, "drd").unwrap();
    w.with0("ReductionRegistrations", |w| {
      w.write_signature(sig);
      let art = self.art.as_str().to_ascii_uppercase();
      let art = art.as_bytes();
      for (i, red) in reds.iter().enumerate() {
        let attrs = |w: &mut Elem| {
          w.attr(b"aid", art);
          w.attr_str(b"nr", i + 1);
        };
        w.with("Reduction", attrs, |w| {
          w.write_types(None, &red.primary);
          w.write_term(None, &red.terms[0]);
          w.write_term(None, &red.terms[1])
        })
      }
    });
    w.finish()
  }

  pub fn write_dpr(&self, new_prel: bool, sig: &[Article], props: &[Property]) {
    let mut w = self.create_xml(false, new_prel, "dpr").unwrap();
    w.with0("PropertyRegistration", |w| {
      w.write_signature(sig);
      let art = self.art.as_str().to_ascii_uppercase();
      let art = art.as_bytes();
      for (i, prop) in props.iter().enumerate() {
        let attrs = |w: &mut Elem| {
          w.attr(b"aid", art);
          w.attr_str(b"nr", i + 1);
          w.attr_str(b"x", prop.kind as u8 + 1);
        };
        w.with("Property", attrs, |w| {
          w.write_arg_types(None, &prop.primary);
          w.write_type(None, &prop.ty)
        })
      }
    });
    w.finish()
  }

  pub fn write_the(&self, new_prel: bool, DepTheorems { sig, thm }: &DepTheorems) {
    let mut w = self.create_xml(false, new_prel, "the").unwrap();
    w.with0("Theorems", |w| {
      w.write_signature(sig);
      for thm in thm {
        let attrs = |w: &mut Elem| {
          let k = match thm.kind {
            TheoremKind::Thm | TheoremKind::CanceledThm => b'T',
            TheoremKind::Def(_) | TheoremKind::CanceledDef => b'D',
          };
          w.attr(b"kind", &[k][..]);
          if let TheoremKind::Def(c) = &thm.kind {
            let (k, nr) = c.discr_nr();
            w.attr(b"constrkind", &[k][..]);
            w.attr_str(b"constrnr", nr + 1);
          }
        };
        w.with("Theorem", attrs, |w| w.write_formula(None, &thm.stmt))
      }
    });
    w.finish()
  }

  pub fn write_sch(&self, new_prel: bool, DepSchemes { sig, sch }: &DepSchemes) {
    let mut w = self.create_xml(false, new_prel, "sch").unwrap();
    w.with0("Schemes", |w| {
      w.write_signature(sig);
      for sch in sch {
        if let Some(sch) = sch {
          w.with0("Scheme", |w| {
            w.write_arg_types(None, &sch.sch_funcs);
            w.write_formula(None, &sch.thesis);
            w.write_formulas(None, &sch.prems)
          })
        } else {
          w.with0("Canceled", |_| {})
        }
      }
    });
    w.finish()
  }

  fn write_symbols<'a>(&self, ext: &str, iter: impl Iterator<Item = (u8, u32, &'a str)>) {
    let mut w = self.create_xml(true, false, ext).unwrap();
    w.with0("Symbols", |w| {
      for (kind, n, s) in iter {
        w.with_attr("Symbol", |e| {
          e.attr(b"kind", &[kind][..]);
          e.attr_str(b"nr", n + 1);
          e.attr_escaped(b"name", s);
        })
      }
    });
    w.finish()
  }

  pub fn write_idx(&self, idents: &[Rc<str>]) {
    self.write_symbols("idx", idents.iter().enumerate().map(|(i, id)| (b'I', i as u32, &**id)))
  }

  pub fn write_dcx(&self, symbols: &HashMap<SymbolKind, String>) {
    let mut symbols = symbols.iter().map(|(&k, v)| (k, v)).collect::<Vec<_>>();
    symbols.sort_by_key(|e| e.0);
    let iter = symbols.into_iter().map(|(kind, s)| {
      let (kind, n) = kind.into();
      (kind.discr(), n, &**s)
    });
    self.write_symbols("dcx", iter)
  }

  pub fn write_formats(
    &self, ext: &str, formats: &IdxVec<FormatId, Format>, func_prio: &HashMap<FuncSymId, u32>,
  ) {
    let mut w = self.create_xml(true, false, ext).unwrap();
    w.with0("Formats", |w| {
      for (i, fmt) in formats.enum_iter() {
        w.write_format(Some(i.0), fmt);
      }
      let mut prio = func_prio.iter().map(|(&k, &v)| (k, v)).collect::<Vec<_>>();
      prio.sort_by_key(|e| e.0);
      for (id, prio) in prio {
        w.with_attr("Priority", |e| {
          e.attr(b"kind", &b"O"[..]);
          e.attr_str(b"symbolnr", id.0 + 1);
          e.attr_str(b"value", prio);
        })
      }
    });
    w.finish()
  }

  pub fn write_eno(&self, notas: &EnumMap<PatternKindClass, ExtVec<Pattern>>) {
    let mut w = self.create_xml(true, false, "eno").unwrap();
    w.xsl();
    w.with0("Notations", |w| {
      for (_, pats) in notas {
        for (i, pat) in pats.vec.iter().enumerate() {
          w.write_pattern(pat, Some(i as u32), |fmt| Some(fmt.0 + 1), |_, _| {});
        }
      }
    });
    w.finish()
  }

  pub fn write_atr(&self, sig: &SigBuilder, constrs: &Constructors) {
    let mut w = self.create_xml(true, false, "atr").unwrap();
    w.xsl();
    w.with0("Constructors", |w| {
      #[derive(Clone, Copy)]
      struct S<'a>(&'a SigBuilder);
      impl ForeachConstructor for S<'_> {
        fn foreach<I: Idx, T>(
          self, arr: &IdxVec<I, T>, base: impl Fn(&ConstructorsBase) -> u32,
          mut body: impl FnMut(&[u8], u32, u32, &T),
        ) {
          for (i, &(art, ref lo)) in self.0.sig.enum_iter() {
            let art = art.as_str().to_ascii_uppercase();
            let art = art.as_bytes();
            let lo = base(lo);
            for j in lo..base(self.0.hi(i)) {
              body(art, j - lo, j, &arr.0[j as usize])
            }
          }
        }
      }
      w.write_constructors(constrs, S(sig))
    });
    w.finish()
  }

  pub fn write_dfs(&self, def: &[Definiens]) {
    if def.is_empty() {
      match std::fs::remove_file(self.to_path(true, false, "dfs")) {
        Err(e) if e.kind() == ErrorKind::NotFound => {}
        e => e.unwrap(),
      }
      return
    }
    let mut w = self.create_xml(true, false, "dfs").unwrap();
    w.xsl();
    w.with0("Definientia", |w| w.write_definitions(true, def));
    w.finish()
  }

  pub fn write_eth(self) -> WriteEth { WriteEth(MizWriterPart::Empty(self)) }
  pub fn write_esh(self) -> WriteEsh { WriteEsh(MizWriterPart::Empty(self)) }
}

enum MizWriterPart {
  Empty(MizPath),
  Ready(MizWriter),
}

trait WritePart {
  const EXT: &'static str;
  const ROOT: &'static str;
  fn write_part(w: &mut MizWriterPart) -> &mut MizWriter {
    match w {
      MizWriterPart::Empty(path) => {
        *w = MizWriterPart::Ready(path.create_xml(true, false, Self::EXT).unwrap());
        let MizWriterPart::Ready(w) = w else { unreachable!() };
        w.xsl();
        w.start(Self::ROOT);
        w
      }
      MizWriterPart::Ready(w) => w,
    }
  }
  fn finish_part(w: MizWriterPart) {
    match w {
      MizWriterPart::Empty(path) =>
        match std::fs::remove_file(path.to_path(true, false, Self::EXT)) {
          Err(e) if e.kind() == ErrorKind::NotFound => {}
          e => e.unwrap(),
        },
      MizWriterPart::Ready(mut w) => {
        w.end_tag(Self::ROOT);
        w.finish()
      }
    }
  }
}

#[must_use = "use finish() to close the file"]
pub struct WriteEth(MizWriterPart);
impl WritePart for WriteEth {
  const EXT: &'static str = "eth";
  const ROOT: &'static str = "Theorems";
}
impl WriteEth {
  pub fn write(&mut self, art_id: ArticleId, abs_nr: u32, art: Article, thm: &Theorem) {
    let w = Self::write_part(&mut self.0);
    let attrs = |w: &mut Elem| {
      w.attr_str(b"articlenr", art_id.0 + 1);
      w.attr_str(b"nr", abs_nr + 1);
      w.attr(b"aid", art.as_bytes());
      let k = match thm.kind {
        TheoremKind::Thm | TheoremKind::CanceledThm => b'T',
        TheoremKind::Def(_) | TheoremKind::CanceledDef => b'D',
      };
      w.attr(b"kind", &[k][..]);
      if let TheoremKind::Def(c) = &thm.kind {
        let (k, nr) = c.discr_nr();
        w.attr(b"constrkind", &[k][..]);
        w.attr_str(b"constrnr", nr + 1);
      }
    };
    w.with("Theorem", attrs, |w| w.write_formula(None, &thm.stmt))
  }
  pub fn finish(self) { Self::finish_part(self.0) }
}

#[must_use = "use finish() to close the file"]
pub struct WriteEsh(MizWriterPart);
impl WritePart for WriteEsh {
  const EXT: &'static str = "esh";
  const ROOT: &'static str = "Schemes";
}
impl WriteEsh {
  pub fn write(&mut self, art_id: ArticleId, abs_nr: u32, art: Article, sch: &Scheme) {
    let w = Self::write_part(&mut self.0);
    let attrs = |w: &mut Elem| {
      w.attr_str(b"articlenr", art_id.0 + 1);
      w.attr_str(b"nr", abs_nr + 1);
      w.attr(b"aid", art.as_bytes());
    };
    w.with("Scheme", attrs, |w| {
      w.write_arg_types(None, &sch.sch_funcs);
      w.write_formula(None, &sch.thesis);
      w.write_formulas(None, &sch.prems)
    })
  }
  pub fn finish(self) { Self::finish_part(self.0) }
}

struct Elem(BytesStart<'static>);

impl Elem {
  fn attr<'a>(&mut self, key: &[u8], value: impl Into<Cow<'a, [u8]>>) {
    self.0.push_attribute(Attribute { key: quick_xml::name::QName(key), value: value.into() })
  }
  fn attr_str(&mut self, key: &[u8], value: impl ToString) {
    self.attr(key, value.to_string().into_bytes())
  }
  fn opt_attr_str(&mut self, key: &[u8], value: Option<impl ToString>) {
    if let Some(value) = value {
      self.attr_str(key, value)
    }
  }
  fn attr_escaped(&mut self, key: &[u8], value: &str) {
    let value = match quick_xml::escape::escape(value) {
      Cow::Borrowed(s) => Cow::Borrowed(s.as_bytes()),
      Cow::Owned(s) => Cow::Owned(s.into_bytes()),
    };
    self.attr(key, value)
  }

  fn pos(&mut self, pos: Position) {
    self.attr_str(b"line", pos.line);
    self.attr_str(b"col", pos.col);
  }

  fn label(&mut self, label: Option<LabelId>) { self.opt_attr_str(b"nr", label.map(|x| x.0 - 1)) }
  fn pos_and_label(&mut self, pos: Position, label: Option<LabelId>) {
    self.pos(pos);
    self.label(label)
  }
}

impl MizWriter {
  fn clear_pending(&mut self) {
    if let Some(elem) = self.pending.take() {
      self.w.write_event(Event::Start(elem.0)).unwrap()
    }
  }

  fn start(&mut self, tag: &'static str) -> &mut Elem {
    self.clear_pending();
    self.pending.insert(Elem(BytesStart::new(tag)))
  }

  fn finish(mut self) {
    assert!(self.pending.is_none());
    self.w.get_mut().write_all(b"\n").unwrap();
    self.w.get_mut().flush().unwrap()
  }

  pub fn xsl(&mut self) {
    const XSL: &[u8] = b"\n<?xml-stylesheet type=\"text/xml\" href=\"../miz.xml\"?>";
    self.w.get_mut().write_all(XSL).unwrap();
  }

  #[inline]
  fn with(
    &mut self, tag: &'static str, attrs: impl FnOnce(&mut Elem), body: impl FnOnce(&mut Self),
  ) {
    attrs(self.start(tag));
    body(self);
    self.end_tag(tag)
  }

  #[inline]
  fn with0(&mut self, tag: &'static str, body: impl FnOnce(&mut Self)) {
    self.with(tag, |_| {}, body);
  }

  #[inline]
  fn with_attr(&mut self, tag: &'static str, attrs: impl FnOnce(&mut Elem)) {
    self.with(tag, attrs, |_| {})
  }

  fn end_tag(&mut self, tag: &'static str) {
    match self.pending.take() {
      Some(elem) => self.w.write_event(Event::Empty(elem.0)).unwrap(),
      None => self.w.write_event(Event::End(BytesEnd::new(tag))).unwrap(),
    }
  }

  fn write_signature(&mut self, sig: &[Article]) {
    self.with0("Signature", |w| {
      for art in sig {
        w.with_attr("ArticleID", |e| e.attr_str(b"name", art.as_str().to_ascii_uppercase()))
      }
    })
  }

  fn write_vocabularies(&mut self, vocs: &Vocabularies) {
    self.with0("Vocabularies", |w| {
      for (art, symbols) in &vocs.0 {
        w.with0("Vocabulary", |w| {
          w.with_attr("ArticleID", |e| e.attr_str(b"name", art.as_str().to_ascii_uppercase()));
          for (c, &n) in &symbols.0 {
            w.with_attr("SymbolCount", |e| {
              e.attr(b"kind", &[c.discr()][..]);
              e.attr_str(b"nr", n);
            })
          }
        })
      }
    })
  }

  fn write_format(&mut self, nr: Option<u32>, fmt: &Format) {
    self.with_attr("Format", |e| {
      e.attr(b"kind", &[fmt.discr()][..]);
      e.opt_attr_str(b"nr", nr.map(|x| x + 1));
      let (sym, args, left, rsym) = match *fmt {
        Format::Aggr(FormatAggr { sym: StructSymId(sym), args })
        | Format::Struct(FormatStruct { sym: StructSymId(sym), args })
        | Format::Mode(FormatMode { sym: ModeSymId(sym), args })
        | Format::Attr(FormatAttr { sym: AttrSymId(sym), args }) => (sym + 1, args, None, None),
        Format::SubAggr(StructSymId(sym)) | Format::Sel(SelSymId(sym)) => (sym + 1, 1, None, None),
        Format::Func(FormatFunc::Bracket { lsym, rsym, args }) =>
          (lsym.0 + 1, args, None, Some(rsym.0 + 1)),
        Format::Func(FormatFunc::Func { sym: FuncSymId(sym), left, right })
        | Format::Pred(FormatPred { sym: PredSymId(sym), left, right }) =>
          (sym + 1, left + right, Some(left), None),
      };
      e.attr_str(b"symbolnr", sym);
      e.attr_str(b"argnr", args);
      e.opt_attr_str(b"leftargnr", left);
      e.opt_attr_str(b"rightsymbolnr", rsym);
    })
  }

  fn write_pattern<F>(
    &mut self, pat: &Pattern<F>, rel_nr: Option<u32>, fmt_attr: impl FnOnce(&F) -> Option<u32>,
    fmt_body: impl FnOnce(&mut Self, &F),
  ) {
    let (kind, nr) = match pat.kind {
      PatternKind::Mode(ModeId(n)) => (b'M', n + 1),
      PatternKind::ExpandableMode { .. } => (b'M', 0),
      PatternKind::Struct(StructId(n)) => (b'L', n + 1),
      PatternKind::Attr(AttrId(n)) => (b'V', n + 1),
      PatternKind::Pred(PredId(n)) => (b'R', n + 1),
      PatternKind::Func(FuncId(n)) => (b'K', n + 1),
      PatternKind::Sel(SelId(n)) => (b'U', n + 1),
      PatternKind::Aggr(AggrId(n)) => (b'G', n + 1),
      PatternKind::SubAggr(StructId(n)) => (b'J', n + 1),
    };
    let attrs = |w: &mut Elem| {
      w.attr(b"kind", &[kind][..]);
      w.attr_str(b"nr", pat.abs_nr + 1);
      w.attr(b"aid", pat.article.as_str().to_ascii_uppercase().as_bytes());
      w.opt_attr_str(b"formatnr", fmt_attr(&pat.fmt));
      w.attr(b"constrkind", &[kind][..]);
      w.attr_str(b"constrnr", nr);
      if !pat.pos {
        w.attr(b"antonymic", &b"true"[..])
      }
      w.opt_attr_str(b"relnr", rel_nr.map(|x| x + 1));
      // w.attr_str(b"redefnr", redefines);
    };
    self.with("Pattern", attrs, |w| {
      fmt_body(w, &pat.fmt);
      w.write_arg_types(None, &pat.primary);
      w.write_loci("Visible", &pat.visible);
      if let PatternKind::ExpandableMode { expansion } = &pat.kind {
        w.with0("Expansion", |w| w.write_type(None, expansion))
      }
    })
  }

  fn write_constr_count(&mut self, kind: u8, value: u32) {
    if value != 0 {
      self.with_attr("ConstrCount", |w| {
        w.attr(b"kind", &[kind][..]);
        w.attr_str(b"nr", value);
      })
    }
  }

  fn write_constructor<I: Idx>(
    &mut self, art: &[u8], (kind, nr): (u8, u32), rel: u32, c: &Constructor<I>,
    attrs: impl FnOnce(&mut Elem), body: impl FnOnce(&mut Self),
  ) {
    let attrs = |w: &mut Elem| {
      w.attr(b"kind", &[kind][..]);
      w.attr_str(b"nr", nr + 1);
      w.attr(b"aid", art);
      w.attr_str(b"relnr", rel + 1);
      if let Some(redef) = c.redefines {
        w.attr_str(b"redefnr", redef.into_usize() + 1);
        w.attr_str(b"superfluous", c.superfluous);
      }
      attrs(w)
    };
    self.with("Constructor", attrs, |w| {
      let attrs = |w: &mut Elem| {
        let arg1 = if c.properties.uses_arg1() { c.properties.arg1 + 1 } else { 0 };
        w.attr_str(b"propertyarg1", arg1);
        let arg2 = if c.properties.uses_arg2() { c.properties.arg2 + 1 } else { 0 };
        w.attr_str(b"propertyarg2", arg2);
      };
      if c.properties.properties != PropertySet::EMPTY {
        w.with("Properties", attrs, |w| {
          for prop in (0..PropertyKind::LENGTH).map(PropertyKind::from_usize) {
            if c.properties.properties.get(prop) {
              w.with0(prop.to_upper(), |_| {})
            }
          }
        })
      }
      w.write_arg_types(None, &c.primary);
      body(w)
    })
  }

  fn write_ty_constructor<I: Idx>(
    &mut self, art: &[u8], kind: (u8, u32), rel: u32, c: &TyConstructor<I>,
  ) {
    self.write_constructor(art, kind, rel, c, |_| {}, |w| w.write_type(None, &c.ty))
  }

  fn write_fields(&mut self, fields: &[SelId]) {
    self.with0("Fields", |w| {
      fields.iter().for_each(|field| w.with_attr("Field", |w| w.attr_str(b"nr", field.0 + 1)))
    })
  }

  fn write_constructors(&mut self, constrs: &Constructors, body: impl ForeachConstructor) {
    body.foreach(
      &constrs.attribute,
      |base| base.attribute,
      |art, i, rel, c| self.write_ty_constructor(art, (b'V', i), rel, c),
    );
    body.foreach(
      &constrs.functor,
      |base| base.functor,
      |art, i, rel, c| self.write_ty_constructor(art, (b'K', i), rel, c),
    );
    body.foreach(
      &constrs.mode,
      |base| base.mode,
      |art, i, rel, c| self.write_ty_constructor(art, (b'M', i), rel, c),
    );
    body.foreach(
      &constrs.predicate,
      |base| base.predicate,
      |art, i, rel, c| self.write_constructor(art, (b'R', i), rel, c, |_| {}, |_| {}),
    );
    body.foreach(
      &constrs.struct_mode,
      |base| base.struct_mode,
      |art, i, rel, c| {
        let attrs = |w: &mut Elem| w.attr_str(b"structmodeaggrnr", c.aggr.0 + 1);
        self.write_constructor(art, (b'L', i), rel, c, attrs, |w| {
          w.write_types(None, &c.parents);
          w.write_fields(&c.fields);
        })
      },
    );
    body.foreach(
      &constrs.aggregate,
      |base| base.aggregate,
      |art, i, rel, c| {
        let attrs = |w: &mut Elem| w.attr_str(b"aggregbase", c.base);
        self.write_constructor(art, (b'G', i), rel, c, attrs, |w| {
          w.write_type(None, &c.ty);
          w.write_fields(&c.fields)
        })
      },
    );
    body.foreach(
      &constrs.selector,
      |base| base.selector,
      |art, i, rel, c| self.write_ty_constructor(art, (b'U', i), rel, c),
    );
  }

  fn write_cluster(
    &mut self, tag: &'static str, art: &[u8], nr: usize, cl: &Cluster, body: impl FnOnce(&mut Self),
  ) {
    let attrs = |w: &mut Elem| {
      w.attr(b"aid", art);
      w.attr_str(b"nr", nr + 1);
    };
    self.with(tag, attrs, |w| {
      w.write_arg_types(None, &cl.primary);
      body(w)
    })
  }

  fn write_def_body<T>(
    &mut self, kind: u8, body: &DefBody<T>, mut elem: impl FnMut(&mut Self, &T),
  ) {
    let attrs = |w: &mut Elem| w.attr(b"kind", &[kind][..]);
    self.with("DefMeaning", attrs, |w| {
      for case in &*body.cases {
        w.with0("PartialDef", |w| {
          elem(w, &case.case);
          w.write_formula(None, &case.guard)
        })
      }
      if let Some(ow) = &body.otherwise {
        elem(w, ow)
      }
    })
  }

  pub fn write_definitions(&mut self, rel: bool, def: &[Definiens]) {
    for (i, def) in def.iter().enumerate() {
      let attrs = |w: &mut Elem| {
        let (kind, nr) = def.constr.discr_nr();
        w.attr(b"constrkind", &[kind][..]);
        w.attr_str(b"constrnr", nr + 1);
        w.attr(b"aid", def.article.as_str().to_ascii_uppercase().as_bytes());
        w.attr_str(b"defnr", def.def_nr.0 + 1);
        // w.attr_str(b"vid", lab_id);
        if rel {
          w.attr_str(b"relnr", i + 1);
        }
      };
      self.with("Definiens", attrs, |w| {
        w.write_types(None, &def.primary);
        w.write_loci("Essentials", &def.essential);
        if !matches!(def.assumptions, Formula::True) {
          w.write_formula(None, &def.assumptions)
        }
        match &def.value {
          DefValue::Term(body) => w.write_def_body(b'e', body, |w, t| w.write_term(None, t)),
          DefValue::Formula(body) => w.write_def_body(b'm', body, |w, f| w.write_formula(None, f)),
        }
      })
    }
  }

  fn write_attrs(&mut self, lc: Option<&LocalContext>, attrs: &Attrs) {
    let Attrs::Consistent(attrs) = attrs else { unreachable!() };
    self.with0("Cluster", |w| {
      for attr in attrs {
        let attrs = |w: &mut Elem| {
          w.attr_str(b"nr", attr.nr.0 + 1);
          if !attr.pos {
            w.attr(b"value", &b"false"[..])
          }
          // w.attr_str(b"pid", pat_nr);
        };
        w.with("Adjective", attrs, |w| w.write_terms(lc, &attr.args))
      }
    })
  }

  fn write_type(&mut self, lc: Option<&LocalContext>, ty: &Type) {
    let attrs = |w: &mut Elem| {
      let (kind, n) = match ty.kind {
        TypeKind::Struct(n) => (b'G', n.0),
        TypeKind::Mode(n) => (b'M', n.0),
      };
      w.attr(b"kind", &[kind][..]);
      w.attr_str(b"nr", n + 1)
    };
    self.with("Typ", attrs, |w| {
      w.write_attrs(lc, &ty.attrs.0);
      w.write_terms(lc, &ty.args)
    })
  }

  fn write_types(&mut self, lc: Option<&LocalContext>, tys: &[Type]) {
    tys.iter().for_each(|ty| self.write_type(lc, ty))
  }

  fn write_arg_types(&mut self, lc: Option<&LocalContext>, tys: &[Type]) {
    self.with0("ArgTypes", |w| w.write_types(lc, tys))
  }

  fn write_term(&mut self, lc: Option<&LocalContext>, tm: &Term) {
    match tm {
      Term::Numeral(n) => self.with_attr("Num", |w| w.attr_str(b"nr", *n)),
      Term::Locus(n) => self.with_attr("LocusVar", |w| w.attr_str(b"nr", n.0 + 1)),
      Term::Bound(n) => self.with_attr("Var", |w| w.attr_str(b"nr", n.0 + 1)),
      Term::Const(n) => self.with_attr("Const", |w| w.attr_str(b"nr", n.0 + 1)),
      Term::SchFunc { nr, args } => self.write_func(lc, "Func", b'F', nr.0, args),
      Term::Aggregate { nr, args } => self.write_func(lc, "Func", b'G', nr.0, args),
      Term::PrivFunc { nr, args, value } => {
        let attrs = |w: &mut Elem| w.attr_str(b"nr", nr.0 + 1);
        self.with("PrivFunc", attrs, |w| {
          w.write_term(lc, value);
          w.write_terms(lc, args)
        })
      }
      Term::Functor { nr, args } => self.write_func(lc, "Func", b'K', nr.0, args),
      Term::Selector { nr, args } => self.write_func(lc, "Func", b'U', nr.0, args),
      Term::The { ty } => self.with0("Choice", |w| w.write_type(lc, ty)),
      Term::Fraenkel { args, scope, compr } => self.with0("Fraenkel", |w| {
        for ty in &**args {
          w.write_type(lc, ty);
          w.depth += 1;
        }
        w.write_term(lc, scope);
        w.write_formula(lc, compr);
        w.depth -= args.len() as u32
      }),
      Term::Infer(i) if lc.is_some() =>
        self.write_term(lc, &lc.unwrap().infer_const.borrow()[*i].def),
      Term::EqClass(_)
      | Term::EqMark(_)
      | Term::Infer(_)
      | Term::FreeVar(_)
      | Term::Qua { .. }
      | Term::It => unreachable!(),
    }
  }
  fn write_terms(&mut self, lc: Option<&LocalContext>, tys: &[Term]) {
    tys.iter().for_each(|ty| self.write_term(lc, ty))
  }

  fn write_func(
    &mut self, lc: Option<&LocalContext>, tag: &'static str, kind: u8, nr: u32, args: &[Term],
  ) {
    let attrs = |w: &mut Elem| {
      w.attr(b"kind", &[kind][..]);
      w.attr_str(b"nr", nr + 1)
    };
    self.with(tag, attrs, |w| w.write_terms(lc, args))
  }

  fn write_formula(&mut self, lc: Option<&LocalContext>, f: &Formula) {
    match f {
      Formula::SchPred { nr, args } => self.write_func(lc, "Pred", b'P', nr.0, args),
      Formula::Pred { nr, args } => self.write_func(lc, "Pred", b'R', nr.0, args),
      Formula::Attr { nr, args } => self.write_func(lc, "Pred", b'V', nr.0, args),
      Formula::PrivPred { nr, args, value } => {
        let attrs = |w: &mut Elem| w.attr_str(b"nr", nr.0 + 1);
        self.with("PrivPred", attrs, |w| {
          w.write_terms(lc, args);
          w.write_formula(lc, value)
        })
      }
      Formula::Is { term, ty } => self.with0("Is", |w| {
        w.write_term(lc, term);
        w.write_type(lc, ty)
      }),
      Formula::Neg { f } => self.with0("Not", |w| w.write_formula(lc, f)),
      Formula::And { args } => self.with0("And", |w| w.write_formulas(lc, args)),
      Formula::ForAll { dom, scope } => {
        let attrs = |_: &mut Elem| {
          // w.attr_str(b"vid", var_id)
        };
        self.with("For", attrs, |w| {
          w.write_type(lc, dom);
          w.depth += 1;
          w.write_formula(lc, scope);
          w.depth -= 1;
        })
      }
      Formula::FlexAnd { nat, le, terms, scope } => self.write_formula(
        lc,
        &Global::into_legacy_flex_and(
          &mut nat.clone(),
          *le,
          &mut terms.clone(),
          &mut scope.clone(),
          self.depth,
        ),
      ),
      Formula::LegacyFlexAnd { orig, terms, expansion } => self.with0("FlexFrm", |w| {
        w.write_formulas(lc, &**orig);
        w.write_terms(lc, &**terms);
        w.write_formula(lc, expansion)
      }),
      Formula::True => self.with0("Verum", |_| {}),
    }
  }

  fn write_formulas(&mut self, lc: Option<&LocalContext>, fs: &[Formula]) {
    fs.iter().for_each(|ty| self.write_formula(lc, ty))
  }

  fn write_loci(&mut self, tag: &'static str, args: &[LocusId]) {
    self.with0(tag, |w| args.iter().for_each(|n| w.with_attr("Int", |w| w.attr_str(b"x", n.0 + 1))))
  }

  pub fn write_pairs(&mut self, xs: &[(u32, u32)]) {
    for &(x, y) in xs {
      self.with_attr("Pair", |w| {
        w.attr_str(b"x", x);
        w.attr_str(b"y", y)
      })
    }
  }
}

trait ForeachConstructor: Copy {
  fn foreach<I: Idx, T>(
    self, arr: &IdxVec<I, T>, base: impl Fn(&ConstructorsBase) -> u32,
    body: impl FnMut(&[u8], u32, u32, &T),
  );
}

pub struct OWriteXml(Option<Box<WriteXml>>);

impl MizPath {
  pub fn write_xml(&self, write: bool) -> OWriteXml {
    OWriteXml(write.then(|| {
      let mut w = self.create_xml(true, false, "xml").unwrap();
      w.xsl();
      w.start("Article");
      Box::new(WriteXml(w))
    }))
  }
}

impl OWriteXml {
  #[inline]
  pub fn on<R: Default>(&mut self, f: impl FnOnce(&mut WriteXml) -> R) -> R {
    if let Some(w) = &mut self.0 {
      f(w)
    } else {
      R::default()
    }
  }

  pub fn finish(&mut self) {
    if let Some(mut w) = self.0.take() {
      w.0.end_tag("Article");
      w.0.finish()
    }
  }
}

pub struct WriteXml(MizWriter);

impl WriteXml {
  pub fn start_tag(&mut self, tag: &'static str) { self.0.start(tag); }
  pub fn end_tag(&mut self, tag: &'static str) { self.0.end_tag(tag) }

  #[inline]
  fn with(
    &mut self, tag: &'static str, attrs: impl FnOnce(&mut Elem), body: impl FnOnce(&mut Self),
  ) {
    attrs(self.0.start(tag));
    body(self);
    self.0.end_tag(tag)
  }

  #[inline]
  fn with0(&mut self, tag: &'static str, body: impl FnOnce(&mut Self)) {
    self.with(tag, |_| {}, body);
  }

  pub fn end_pos(&mut self, pos: Position) { self.0.with_attr("EndPosition", |w| w.pos(pos)) }

  pub fn write_term(&mut self, lc: &LocalContext, tm: &Term) { self.0.write_term(Some(lc), tm) }
  pub fn write_terms(&mut self, lc: &LocalContext, tms: &[Term]) {
    self.0.write_terms(Some(lc), tms)
  }
  pub fn write_type(&mut self, lc: &LocalContext, ty: &Type) { self.0.write_type(Some(lc), ty) }
  pub fn write_types(&mut self, lc: &LocalContext, tys: &[Type]) {
    self.0.write_types(Some(lc), tys)
  }
  pub fn write_formula(&mut self, lc: &LocalContext, f: &Formula) {
    self.0.write_formula(Some(lc), f)
  }
  pub fn write_proposition(
    &mut self, lc: &LocalContext, pos: Position, label: Option<LabelId>, f: &Formula,
  ) {
    self.with("Proposition", |w| w.pos_and_label(pos, label), |w| w.write_formula(lc, f))
  }

  pub fn write_thesis(&mut self, lc: &LocalContext, thesis: &Formula, expansions: &[(u32, u32)]) {
    self.0.with0("Thesis", |w| {
      w.write_formula(Some(lc), thesis);
      w.with0("ThesisExpansions", |w| w.write_pairs(expansions))
    })
  }

  pub fn write_block_thesis<'a>(
    &mut self, lc: &LocalContext, theses: impl Iterator<Item = &'a Formula>, res: &Formula,
  ) {
    self.with0("BlockThesis", |w| {
      for f in theses {
        w.write_thesis(lc, f, &[])
      }
      w.write_formula(lc, res)
    })
  }

  pub fn canceled(&mut self, kind: CancelKind, n: u32) {
    for _ in 0..n {
      self.0.with_attr("Canceled", |w| w.attr(b"kind", &[kind.discr()][..]))
    }
  }

  pub fn let_(&mut self, lc: &LocalContext, start: usize) {
    self.with0("Let", |w| {
      for fv in &lc.fixed_var.0[start..] {
        w.write_type(lc, &fv.ty)
      }
    })
  }

  pub fn start_assume(&mut self) { self.start_tag("Assume") }
  pub fn end_assume(&mut self) { self.end_tag("Assume") }

  pub fn given(
    &mut self, lc: &LocalContext, pos: Position, start: usize,
    conds: &[(Position, Option<LabelId>, Formula)], ex: &Formula,
  ) {
    self.with0("Given", |w| {
      w.write_proposition(lc, pos, None, ex);
      for fv in &lc.fixed_var.0[start..] {
        w.write_type(lc, &fv.ty)
      }
      for &(pos, label, ref f) in conds {
        w.write_proposition(lc, pos, label, f)
      }
    })
  }

  pub fn take(&mut self, lc: &LocalContext, tm: &Term) {
    self.with0("Take", |w| w.write_term(lc, tm))
  }

  pub fn take_as_var(&mut self, lc: &LocalContext, ty: &Type, tm: &Term) {
    self.with0("TakeAsVar", |w| {
      w.write_type(lc, ty);
      w.write_term(lc, tm)
    })
  }

  pub fn start_thus(&mut self) { self.start_tag("Conclusion") }
  pub fn end_thus(&mut self) { self.end_tag("Conclusion") }

  pub fn start_now(&mut self, pos: Position, label: Option<LabelId>) {
    self.0.start("Now").pos_and_label(pos, label)
  }
  pub fn end_now(&mut self) { self.end_tag("Now") }

  pub fn start_cases(&mut self, pos: Position) { self.0.start("PerCasesReasoning").pos(pos) }
  pub fn end_cases(&mut self) { self.end_tag("PerCasesReasoning") }

  pub fn start_cases_just(&mut self, lc: &LocalContext, pos: Position, f: &Formula) {
    self.start_tag("PerCases");
    self.write_proposition(lc, pos, None, f)
  }
  pub fn end_cases_just(&mut self) { self.end_tag("PerCases") }

  pub fn start_case(&mut self, lc: &LocalContext, pos: Position, thesis: Option<&Formula>) {
    self.0.start("CaseBlock").pos(pos);
    if let Some(f) = thesis {
      self.write_block_thesis(lc, std::iter::empty(), f)
    }
    self.start_tag("Case")
  }
  pub fn mid_case(&mut self) { self.end_tag("Case") }
  pub fn end_case(&mut self) { self.end_tag("CaseBlock") }

  pub fn start_suppose(&mut self, lc: &LocalContext, pos: Position, thesis: Option<&Formula>) {
    self.0.start("SupposeBlock").pos(pos);
    if let Some(f) = thesis {
      self.write_block_thesis(lc, std::iter::empty(), f)
    }
    self.start_tag("Suppose")
  }
  pub fn mid_suppose(&mut self) { self.end_tag("Suppose") }
  pub fn end_suppose(&mut self) { self.end_tag("SupposeBlock") }

  pub fn start_scheme(&mut self, pos: Position) { self.0.start("SchemeBlock").pos(pos) }
  pub fn end_scheme(&mut self, end: Position) {
    self.end_pos(end);
    self.end_tag("SchemeBlock")
  }

  pub fn decl_scheme_func(&mut self, lc: &LocalContext, ret: &Type) {
    self.with0("SchemeFuncDecl", |w| {
      w.0.write_arg_types(Some(lc), &lc.locus_ty.0);
      w.0.write_type(Some(lc), ret)
    })
  }

  pub fn decl_scheme_pred(&mut self, lc: &LocalContext) {
    self.with0("SchemePredDecl", |w| w.0.write_arg_types(Some(lc), &lc.locus_ty.0))
  }

  pub fn start_scheme_prems(&mut self) { self.start_tag("SchemePremises") }
  pub fn end_scheme_prems(&mut self) { self.end_tag("SchemePremises") }

  pub fn start_proof(
    &mut self, lc: &LocalContext, pos: Position, label: Option<LabelId>, thesis: &Formula,
  ) {
    self.0.start("Proof").pos_and_label(pos, label);
    self.write_block_thesis(lc, std::iter::empty(), thesis)
  }
  pub fn end_proof(&mut self) { self.end_tag("Proof") }
}
