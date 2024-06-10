use crate::accom::SigBuilder;
use crate::ast::CaseKind;
use crate::types::{self, *};
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
  two_clusters: bool,
  depth: u32,
  shift: Vec<u32>,
}

impl MizPath {
  fn create_xml(&self, mml: bool, new_prel: bool, ext: &str) -> io::Result<MizWriter> {
    let w = BufWriter::new(self.create(mml, new_prel, ext)?);
    let mut w = quick_xml::Writer::new_with_indent(w, b' ', INDENT);
    w.write_event(Event::Decl(BytesDecl::new("1.0", None, None))).unwrap();
    Ok(MizWriter { w, pending: None, depth: 0, two_clusters: false, shift: vec![] })
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
        w.write_cluster("RCluster", Some((art, i as u32)), cl, |w| {
          w.write_type(None, &cl.ty);
          w.write_attrs(None, &cl.consequent.0)
        })
      }
      for (i, cl) in cl.functor.iter().enumerate() {
        w.write_cluster("FCluster", Some((art, i as u32)), cl, |w| {
          w.write_term(None, &cl.term);
          w.write_attrs(None, &cl.consequent.0);
          if let Some(ty) = &cl.ty {
            w.write_type(None, ty)
          }
        })
      }
      for (i, cl) in cl.conditional.iter().enumerate() {
        w.write_cluster("CCluster", Some((art, i as u32)), cl, |w| {
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
        w.write_identify(Some((art, i as u32)), id)
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
        w.write_reduction(Some((art, i as u32)), red)
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
          w.aid_ref(Some((art, i as u32)));
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
            w.constr_kind(c)
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
          w.write_pattern(pat, Some(i as u32), |fmt| Some(fmt.0), |_, _| {});
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
      w.aid_ref(Some((art.as_bytes(), abs_nr)));
      let k = match thm.kind {
        TheoremKind::Thm | TheoremKind::CanceledThm => b'T',
        TheoremKind::Def(_) | TheoremKind::CanceledDef => b'D',
      };
      w.attr(b"kind", &[k][..]);
      if let TheoremKind::Def(c) = &thm.kind {
        w.constr_kind(c)
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
      w.aid_ref(Some((art.as_bytes(), abs_nr)));
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

  fn constr_kind(&mut self, c: &ConstrKind) {
    let (k, nr) = c.discr_nr();
    self.attr(b"constrkind", &[k][..]);
    self.attr_str(b"constrnr", nr + 1);
  }

  fn aid_ref(&mut self, aid_nr: Option<(&[u8], u32)>) {
    if let Some((aid, nr)) = aid_nr {
      self.attr(b"aid", aid);
      self.attr_str(b"nr", nr + 1);
    }
  }
}

impl MizWriter {
  fn clear_pending(&mut self) {
    if let Some(elem) = self.pending.take() {
      self.w.write_event(Event::Start(elem.0)).unwrap();
      self.w.get_mut().flush().unwrap();
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

  pub fn newline(&mut self) {
    self.clear_pending();
    self.w.get_mut().write_all(b"\n").unwrap();
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
    self.w.get_mut().flush().unwrap();
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
      w.aid_ref(Some((pat.article.as_str().to_ascii_uppercase().as_bytes(), pat.abs_nr)));
      w.opt_attr_str(b"formatnr", fmt_attr(&pat.fmt).map(|x| x + 1));
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
    &mut self, kind: u8, aid_nr: Option<(&[u8], u32)>, rel: u32, c: &Constructor<I>,
    attrs: impl FnOnce(&mut Elem), body: impl FnOnce(&mut Self),
  ) {
    let attrs = |w: &mut Elem| {
      w.attr(b"kind", &[kind][..]);
      w.aid_ref(aid_nr);
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
    &mut self, kind: u8, aid_nr: Option<(&[u8], u32)>, rel: u32, c: &TyConstructor<I>,
  ) {
    self.write_constructor(kind, aid_nr, rel, c, |_| {}, |w| w.write_type(None, &c.ty))
  }

  fn write_fields(&mut self, fields: &[SelId]) {
    self.with0("Fields", |w| {
      fields.iter().for_each(|field| w.with_attr("Field", |w| w.attr_str(b"nr", field.0 + 1)))
    })
  }

  fn write_attr_constructor(
    &mut self, aid_nr: Option<(&[u8], u32)>, rel: u32, c: &TyConstructor<AttrId>,
  ) {
    self.write_ty_constructor(b'V', aid_nr, rel, c)
  }
  fn write_func_constructor(
    &mut self, aid_nr: Option<(&[u8], u32)>, rel: u32, c: &TyConstructor<FuncId>,
  ) {
    self.write_ty_constructor(b'K', aid_nr, rel, c)
  }
  fn write_mode_constructor(
    &mut self, aid_nr: Option<(&[u8], u32)>, rel: u32, c: &TyConstructor<ModeId>,
  ) {
    self.write_ty_constructor(b'M', aid_nr, rel, c)
  }
  fn write_pred_constructor(
    &mut self, aid_nr: Option<(&[u8], u32)>, rel: u32, c: &Constructor<PredId>,
  ) {
    self.write_constructor(b'R', aid_nr, rel, c, |_| {}, |_| {})
  }
  fn write_struct_constructor(&mut self, aid_nr: Option<(&[u8], u32)>, rel: u32, c: &StructMode) {
    let attrs = |w: &mut Elem| w.attr_str(b"structmodeaggrnr", c.aggr.0 + 1);
    self.write_constructor(b'L', aid_nr, rel, c, attrs, |w| {
      w.write_types(None, &c.parents);
      w.write_fields(&c.fields);
    })
  }
  fn write_aggr_constructor(&mut self, aid_nr: Option<(&[u8], u32)>, rel: u32, c: &Aggregate) {
    let attrs = |w: &mut Elem| w.attr_str(b"aggregbase", c.base);
    self.write_constructor(b'G', aid_nr, rel, c, attrs, |w| {
      w.write_type(None, &c.ty);
      w.write_fields(&c.fields)
    })
  }
  fn write_sel_constructor(
    &mut self, aid_nr: Option<(&[u8], u32)>, rel: u32, c: &TyConstructor<SelId>,
  ) {
    self.write_ty_constructor(b'U', aid_nr, rel, c)
  }

  fn write_constructors(&mut self, constrs: &Constructors, body: impl ForeachConstructor) {
    macro_rules! mk_body {
      ($($field:ident => $func:ident,)*) => {
        $(body.foreach(
          &constrs.$field, |base| base.$field,
          |art, i, rel, c| self.$func(Some((art, i)), rel, c),
        );)*
      }
    }
    mk_body! {
      attribute => write_attr_constructor,
      functor => write_func_constructor,
      mode => write_mode_constructor,
      predicate => write_pred_constructor,
      struct_mode => write_struct_constructor,
      aggregate => write_aggr_constructor,
      selector => write_sel_constructor,
    }
  }

  fn write_cluster(
    &mut self, tag: &'static str, art_nr: Option<(&[u8], u32)>, cl: &Cluster,
    body: impl FnOnce(&mut Self),
  ) {
    let attrs = |w: &mut Elem| w.aid_ref(art_nr);
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

  pub fn write_definiens(&mut self, rel: Option<usize>, def: &Definiens) {
    let attrs = |w: &mut Elem| {
      w.constr_kind(&def.constr);
      w.attr(b"aid", def.article.as_str().to_ascii_uppercase().as_bytes());
      w.attr_str(b"defnr", def.def_nr.0 + 1);
      // w.attr_str(b"vid", lab_id);
      if let Some(i) = rel {
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

  pub fn write_definitions(&mut self, rel: bool, def: &[Definiens]) {
    for (i, def) in def.iter().enumerate() {
      self.write_definiens(rel.then(|| i + 1), def)
    }
  }

  fn write_identify(&mut self, aid_nr: Option<(&[u8], u32)>, id: &IdentifyFunc) {
    let attrs = |w: &mut Elem| {
      w.aid_ref(aid_nr);
      w.attr(b"constrkind", &b"K"[..]);
    };
    self.with("Identify", attrs, |w| {
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

  fn write_reduction(&mut self, aid_nr: Option<(&[u8], u32)>, red: &Reduction) {
    let attrs = |w: &mut Elem| w.aid_ref(aid_nr);
    self.with("Reduction", attrs, |w| {
      w.write_types(None, &red.primary);
      w.write_term(None, &red.terms[0]);
      w.write_term(None, &red.terms[1])
    })
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
      if w.two_clusters {
        w.write_attrs(lc, &ty.attrs.1);
      }
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
      Term::Bound(n) => {
        let sh = self.shift.partition_point(|&x| x <= n.0);
        self.with_attr("Var", |w| w.attr_str(b"nr", n.0 + sh as u32 + 1))
      }
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
          w.shift.push(w.depth);
          w.write_type(lc, ty);
          w.shift.pop();
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
          w.shift.push(w.depth);
          w.write_type(lc, dom);
          w.shift.pop();
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

  fn write_pairs(&mut self, xs: &[(u32, u32)]) {
    for &(x, y) in xs {
      self.with_attr("Pair", |w| {
        w.attr_str(b"x", x);
        w.attr_str(b"y", y)
      })
    }
  }

  fn write_proposition(
    &mut self, lc: Option<&LocalContext>, pos: Position, label: Option<LabelId>, f: &Formula,
  ) {
    self.with("Proposition", |w| w.pos_and_label(pos, label), |w| w.write_formula(lc, f))
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
      w.two_clusters = true;
      w.xsl();
      let art = self.art.as_str().to_ascii_uppercase();
      w.start("Article").attr(b"aid", art.as_bytes());
      Box::new(WriteXml { w, state: State::Block(BlockKind::Top), stack: vec![], art })
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
      w.w.end_tag("Article");
      w.w.finish()
    }
  }
}

#[derive(Debug, Clone, Copy)]
enum BlockKind {
  Top,
  Block,
  Diffuse,
  Proof,
}

#[derive(Debug, Clone, Copy)]
enum PropKind {
  Consider(BlockKind),
  Reconsider(BlockKind),
  CorrCond(CorrectnessState, CorrCondKind),
  Correctness(CorrectnessState),
  Property,
}

#[derive(Debug, Clone, Copy)]
enum RegistrationKind {
  Reg,
  Identify,
  Struct,
}

#[derive(Debug, Clone, Copy)]
enum CorrectnessState {
  Definition,
  Registration(RegistrationKind),
}

#[derive(Debug)]
enum State {
  SchemeBlock1,
  SchemePremises,
  SchemeBlock2,
  SchemeBlock3,
  SchemeBlock4,
  Justification,
  Reasoning1,
  Block(BlockKind),
  AfterReasoning,
  AfterBlockThesis,
  BlockThesis,
  EndBlock(BlockKind),
  Assume(BlockKind),
  InnerAssume,
  IterEquality(BlockKind),
  AfterIterStep(BlockKind),
  PerCases0Proof,
  PerCases1(BlockKind),
  PerCases2(BlockKind),
  PerCases3(BlockKind),
  PerCases4(BlockKind),
  PerCases5(BlockKind),
  PerCases6Diffuse,
  AfterPerCases(BlockKind),
  Case1(BlockKind, CaseKind),
  Prop1(PropKind),
  Prop2(PropKind),
  Correctness1(CorrectnessState),
  DefProperties,
  DefEnd,
  StructDef1,
  StructDef2,
  RegistrationEnd(RegistrationKind),
  SethoodRegistration1,
  SethoodRegistration2,
}

impl State {
  fn after_reasoning(kind: BlockKind) -> Self {
    match kind {
      BlockKind::Proof => State::AfterReasoning,
      kind => State::Block(kind),
    }
  }
}

#[derive(Debug)]
enum Stack {
  SchemeBlock,
  Thus(BlockKind),
  Reasoning(BlockKind, bool),
  Now(BlockKind),
  Prop(PropKind),
  IterEquality(BlockKind),
  Case(CaseKind),
  PerCases(BlockKind),
  // Reconsider(BlockKind),
  Block(types::BlockKind),
  // CorrCond(CorrCondKind),
  // Correctness,
  SethoodRegistration,
}

pub struct WriteXml {
  w: MizWriter,
  state: State,
  stack: Vec<Stack>,
  art: String,
}

impl WriteXml {
  pub fn start_tag(&mut self, tag: &'static str) { self.w.start(tag); }
  pub fn end_tag(&mut self, tag: &'static str) { self.w.end_tag(tag) }

  #[inline]
  fn with(
    &mut self, tag: &'static str, attrs: impl FnOnce(&mut Elem), body: impl FnOnce(&mut Self),
  ) {
    attrs(self.w.start(tag));
    body(self);
    self.w.end_tag(tag)
  }

  #[inline]
  fn with0(&mut self, tag: &'static str, body: impl FnOnce(&mut Self)) {
    self.with(tag, |_| {}, body);
  }

  pub fn end_pos(&mut self, pos: Position) {
    match self.state {
      State::SchemeBlock3 => self.state = State::SchemeBlock4,
      State::Block(kind) => self.state = State::EndBlock(kind),
      State::PerCases4(kind) => self.state = State::PerCases5(kind),
      State::AfterPerCases(kind) => self.state = State::EndBlock(kind),
      _ => unreachable!(),
    }
    self.w.with_attr("EndPosition", |w| w.pos(pos))
  }

  pub fn write_term(&mut self, lc: &LocalContext, tm: &Term) { self.w.write_term(Some(lc), tm) }
  pub fn write_terms(&mut self, lc: &LocalContext, tms: &[Term]) {
    self.w.write_terms(Some(lc), tms)
  }
  pub fn write_type(&mut self, lc: &LocalContext, ty: &Type) { self.w.write_type(Some(lc), ty) }
  pub fn write_types(&mut self, lc: &LocalContext, tys: &[Type]) {
    self.w.write_types(Some(lc), tys)
  }
  pub fn write_formula(&mut self, lc: &LocalContext, f: &Formula) {
    self.w.write_formula(Some(lc), f)
  }
  pub fn write_proposition(
    &mut self, lc: &LocalContext, pos: Position, label: Option<LabelId>, f: &Formula,
  ) {
    match self.state {
      State::SchemePremises | State::Assume(_) | State::InnerAssume | State::Case1(_, _) => {}
      State::SchemeBlock2
      | State::Block(_)
      | State::Prop1(_)
      | State::PerCases2(_)
      | State::SethoodRegistration1 => {
        self.stack.push(match self.state {
          State::SchemeBlock2 => Stack::SchemeBlock,
          State::Block(kind) => Stack::Reasoning(kind, false),
          State::Prop1(kind) => Stack::Prop(kind),
          State::PerCases2(kind) => Stack::PerCases(kind),
          State::SethoodRegistration1 => Stack::SethoodRegistration,
          _ => unreachable!(),
        });
        self.state = State::Justification;
      }
      _ => unreachable!("{:?}", self.state),
    }
    self.w.write_proposition(Some(lc), pos, label, f)
  }

  pub fn write_thesis(&mut self, lc: &LocalContext, thesis: &Formula, expansions: &[(u32, u32)]) {
    match self.state {
      State::BlockThesis | State::PerCases4(BlockKind::Proof) => {}
      State::AfterReasoning => self.state = State::Block(BlockKind::Proof),
      _ => unreachable!(),
    }
    self.w.with0("Thesis", |w| {
      w.write_formula(Some(lc), thesis);
      w.with0("ThesisExpansions", |w| w.write_pairs(expansions))
    })
  }

  pub fn write_block_thesis<'a>(
    &mut self, lc: &LocalContext, theses: impl Iterator<Item = &'a Formula>, res: &Formula,
  ) {
    let state = match self.state {
      State::Reasoning1 => State::Block(BlockKind::Proof),
      State::EndBlock(BlockKind::Diffuse) => State::AfterBlockThesis,
      State::PerCases0Proof => State::PerCases1(BlockKind::Proof),
      State::Case1(BlockKind::Proof, ck) => State::Case1(BlockKind::Proof, ck),
      State::PerCases5(BlockKind::Diffuse) => State::PerCases6Diffuse,
      _ => unreachable!(),
    };
    self.state = State::BlockThesis;
    self.with0("BlockThesis", |w| {
      for f in theses {
        w.write_thesis(lc, f, &[])
      }
      w.write_formula(lc, res)
    });
    self.state = state;
  }

  pub fn canceled(&mut self, kind: CancelKind, n: u32) {
    assert!(matches!(self.state, State::Block(BlockKind::Top)));
    for _ in 0..n {
      self.w.with_attr("Canceled", |w| w.attr(b"kind", &[kind.discr()][..]))
    }
    self.w.newline()
  }

  pub fn let_(&mut self, lc: &LocalContext, start: usize) {
    let State::Block(kind) = self.state else { unreachable!() };
    self.state = State::after_reasoning(kind);
    self.with0("Let", |w| {
      for fv in &lc.fixed_var.0[start..] {
        w.write_type(lc, &fv.ty)
      }
    })
  }

  pub fn start_assume(&mut self) {
    let State::Block(kind) = self.state else { unreachable!() };
    self.state = State::Assume(kind);
    self.start_tag("Assume")
  }
  pub fn end_assume(&mut self) {
    let State::Assume(kind) = self.state else { unreachable!() };
    self.state = State::after_reasoning(kind);
    self.end_tag("Assume")
  }

  pub fn given(
    &mut self, lc: &LocalContext, pos: Position, start: usize,
    conds: &[(Position, Option<LabelId>, Formula)], ex: &Formula,
  ) {
    let State::Block(kind) = self.state else { unreachable!() };
    self.state = State::InnerAssume;
    self.with0("Given", |w| {
      w.write_proposition(lc, pos, None, ex);
      for fv in &lc.fixed_var.0[start..] {
        w.write_type(lc, &fv.ty)
      }
      for &(pos, label, ref f) in conds {
        w.write_proposition(lc, pos, label, f)
      }
    });
    self.state = State::after_reasoning(kind);
  }

  pub fn take(&mut self, lc: &LocalContext, tm: &Term) {
    let State::Block(kind) = self.state else { unreachable!() };
    self.state = State::after_reasoning(kind);
    self.with0("Take", |w| w.write_term(lc, tm))
  }

  pub fn take_as_var(&mut self, lc: &LocalContext, ty: &Type, tm: &Term) {
    let State::Block(kind) = self.state else { unreachable!() };
    self.state = State::after_reasoning(kind);
    self.with0("TakeAsVar", |w| {
      w.write_type(lc, ty);
      w.write_term(lc, tm)
    })
  }

  pub fn start_thus(&mut self) {
    let State::Block(kind @ (BlockKind::Proof | BlockKind::Diffuse)) = self.state else {
      unreachable!()
    };
    self.state = State::Block(BlockKind::Proof);
    self.stack.push(Stack::Thus(kind));
    self.start_tag("Conclusion")
  }
  pub fn end_thus(&mut self) {
    assert!(matches!(self.state, State::Block(BlockKind::Proof)));
    let Some(Stack::Thus(kind)) = self.stack.pop() else { unreachable!() };
    self.state = State::after_reasoning(kind);
    self.end_tag("Conclusion")
  }

  pub fn start_now(&mut self, pos: Position, label: Option<LabelId>) {
    let State::Block(kind) = self.state else { unreachable!("{:?}", self.state) };
    self.state = State::Block(BlockKind::Diffuse);
    self.stack.push(Stack::Now(kind));
    self.w.start("Now").pos_and_label(pos, label)
  }
  pub fn end_now(&mut self) {
    assert!(matches!(self.state, State::AfterBlockThesis));
    let Some(Stack::Now(kind)) = self.stack.pop() else { unreachable!() };
    self.state = State::Block(kind);
    self.end_tag("Now")
  }

  pub fn start_iter_equality(
    &mut self, lc: &LocalContext, pos: Position, label: Option<LabelId>, lhs: &Term,
  ) {
    let State::Block(kind) = self.state else { unreachable!() };
    self.state = State::IterEquality(kind);
    self.w.start("IterEquality").pos_and_label(pos, label);
    self.write_term(lc, lhs)
  }
  pub fn end_iter_equality(&mut self) {
    let State::IterEquality(kind) = self.state else { unreachable!() };
    self.state = State::Block(kind);
    self.end_tag("IterEquality")
  }

  pub fn start_iter_step(&mut self, lc: &LocalContext, rhs: &Term) {
    let State::IterEquality(kind) = self.state else { unreachable!() };
    self.stack.push(Stack::IterEquality(kind));
    self.state = State::Justification;
    self.w.start("IterStep");
    self.write_term(lc, rhs)
  }
  pub fn end_iter_step(&mut self) {
    let State::AfterIterStep(kind) = self.state else { unreachable!() };
    self.state = State::IterEquality(kind);
    self.end_tag("IterStep")
  }

  pub fn start_cases(&mut self, pos: Position) {
    self.state = match self.state {
      State::Block(BlockKind::Proof) => State::PerCases0Proof,
      State::Block(kind @ BlockKind::Diffuse) => State::PerCases1(kind),
      _ => unreachable!(),
    };
    self.w.start("PerCasesReasoning").pos(pos)
  }
  pub fn end_cases(&mut self) {
    self.state = match self.state {
      State::PerCases5(BlockKind::Proof) => State::AfterPerCases(BlockKind::Proof),
      State::PerCases6Diffuse => State::AfterPerCases(BlockKind::Diffuse),
      _ => unreachable!(),
    };
    self.end_tag("PerCasesReasoning")
  }

  pub fn start_cases_just(&mut self, lc: &LocalContext, pos: Position, f: &Formula) {
    let State::PerCases1(diff) = self.state else { unreachable!() };
    self.state = State::PerCases2(diff);
    self.start_tag("PerCases");
    self.write_proposition(lc, pos, None, f)
  }
  pub fn end_cases_just(&mut self) {
    let State::PerCases3(diff) = self.state else { unreachable!() };
    self.state = State::PerCases4(diff);
    self.end_tag("PerCases")
  }

  pub fn start_case(
    &mut self, lc: &LocalContext, ck: CaseKind, pos: Position, thesis: Option<&Formula>,
  ) {
    let State::PerCases1(diff) = self.state else { unreachable!() };
    self.state = State::Case1(diff, ck);
    self.w.start(ck.block_name()).pos(pos);
    if let Some(f) = thesis {
      self.write_block_thesis(lc, std::iter::empty(), f)
    }
    self.start_tag(ck.name())
  }
  pub fn mid_case(&mut self, ck: CaseKind) {
    let State::Case1(kind, ck2) = self.state else { unreachable!() };
    assert_eq!(ck, ck2);
    self.state = State::after_reasoning(kind);
    self.stack.push(Stack::Case(ck));
    self.end_tag(ck.name())
  }
  pub fn end_case(&mut self, ck: CaseKind) {
    self.state = match self.state {
      State::EndBlock(BlockKind::Proof) => State::PerCases1(BlockKind::Proof),
      State::AfterBlockThesis => State::PerCases1(BlockKind::Diffuse),
      _ => unreachable!(),
    };
    assert!(matches!(self.stack.pop(), Some(Stack::Case(ck2)) if ck2 == ck));
    self.end_tag(ck.block_name())
  }

  pub fn start_scheme(&mut self, pos: Position, nr: SchId) {
    assert!(matches!(self.state, State::Block(BlockKind::Top)));
    self.state = State::SchemeBlock1;
    let w = self.w.start("SchemeBlock");
    w.pos(pos);
    w.attr_str(b"schemenr", nr.0 + 1)
  }
  pub fn end_scheme(&mut self, end: Position) {
    self.end_pos(end);
    assert!(matches!(self.state, State::SchemeBlock4));
    self.state = State::Block(BlockKind::Top);
    self.end_tag("SchemeBlock");
    self.w.newline()
  }

  pub fn decl_scheme_func(&mut self, lc: &LocalContext, id: SchFuncId, ret: &Type) {
    assert!(matches!(self.state, State::SchemeBlock1));
    let attrs = |w: &mut Elem| w.attr_str(b"nr", id.0 + 1);
    self.with("SchemeFuncDecl", attrs, |w| {
      w.w.write_arg_types(Some(lc), &lc.locus_ty.0);
      w.w.write_type(Some(lc), ret)
    })
  }

  pub fn decl_scheme_pred(&mut self, lc: &LocalContext, id: SchPredId) {
    assert!(matches!(self.state, State::SchemeBlock1));
    let attrs = |w: &mut Elem| w.attr_str(b"nr", id.0 + 1);
    self.with("SchemePredDecl", attrs, |w| w.w.write_arg_types(Some(lc), &lc.locus_ty.0))
  }

  pub fn start_scheme_prems(&mut self) {
    assert!(matches!(self.state, State::SchemeBlock1));
    self.state = State::SchemePremises;
    self.start_tag("SchemePremises")
  }
  pub fn end_scheme_prems(&mut self) {
    assert!(matches!(self.state, State::SchemePremises));
    self.state = State::SchemeBlock2;
    self.end_tag("SchemePremises")
  }

  fn pop_justification(&mut self) {
    self.state = match self.stack.pop() {
      Some(Stack::SchemeBlock) => State::SchemeBlock3,
      Some(Stack::Reasoning(kind, true)) => State::after_reasoning(kind),
      Some(Stack::Reasoning(kind, false)) => State::Block(kind),
      Some(Stack::Prop(kind)) => State::Prop2(kind),
      Some(Stack::PerCases(kind)) => State::PerCases3(kind),
      Some(Stack::IterEquality(kind)) => State::AfterIterStep(kind),
      Some(Stack::SethoodRegistration) => State::SethoodRegistration2,
      _ => unreachable!(),
    }
  }

  pub fn start_proof(
    &mut self, lc: &LocalContext, pos: Position, label: Option<LabelId>, thesis: &Formula,
  ) {
    assert!(matches!(self.state, State::Justification));
    self.state = State::Reasoning1;
    self.w.start("Proof").pos_and_label(pos, label);
    self.write_block_thesis(lc, std::iter::empty(), thesis)
  }
  pub fn end_proof(&mut self) {
    let (State::EndBlock(BlockKind::Proof) | State::AfterBlockThesis) = self.state else {
      unreachable!()
    };
    self.pop_justification();
    self.end_tag("Proof");
  }

  pub fn dbg(&self) {
    eprintln!("{:?} {:?}\n{:?}", self.state, self.stack, backtrace::Backtrace::new());
  }

  pub fn write_inference(&mut self, it: &Inference) {
    let State::Justification = self.state else { unreachable!() };
    self.pop_justification();
    let body = |w: &mut MizWriter| {
      for r in &it.refs {
        w.with_attr("Ref", |w| {
          match r.kind {
            ReferenceKind::Priv(label) => w.attr_str(b"nr", label.0 + 1),
            ReferenceKind::Thm((art, thm)) => {
              w.attr_str(b"nr", thm.0 + 1);
              w.attr_str(b"articlenr", art.0);
              w.attr(b"kind", &b"T"[..]);
            }
            ReferenceKind::Def((art, thm)) => {
              w.attr_str(b"nr", thm.0 + 1);
              w.attr_str(b"articlenr", art.0);
              w.attr(b"kind", &b"D"[..]);
            }
          };
          w.pos(r.pos)
        })
      }
    };
    match it.kind {
      InferenceKind::By { linked } => {
        let attrs = |w: &mut Elem| {
          if linked {
            w.attr(b"linked", &b"true"[..])
          }
          w.pos(it.pos)
        };
        self.w.with("By", attrs, body)
      }
      InferenceKind::From { sch } => {
        let attrs = |w: &mut Elem| {
          w.attr_str(b"articlenr", sch.0 .0);
          w.attr_str(b"nr", sch.1 .0 + 1);
          w.pos(it.pos)
        };
        self.w.with("From", attrs, body)
      }
    };
  }

  pub fn start_theorem(
    &mut self, lc: &LocalContext, pos: Position, label: Option<LabelId>, f: &Formula,
  ) {
    assert!(matches!(self.state, State::Block(BlockKind::Top)));
    self.state = State::Block(BlockKind::Proof);
    self.start_tag("JustifiedTheorem");
    self.write_proposition(lc, pos, label, f)
  }
  pub fn end_theorem(&mut self) {
    assert!(matches!(self.state, State::Block(BlockKind::Proof)));
    self.state = State::Block(BlockKind::Top);
    self.end_tag("JustifiedTheorem");
    self.w.newline()
  }

  pub fn start_consider(
    &mut self, lc: &LocalContext, pos: Position, label: Option<LabelId>, f: &Formula,
  ) {
    let State::Block(kind) = self.state else { unreachable!() };
    self.state = State::Prop1(PropKind::Consider(kind));
    self.start_tag("Consider");
    self.write_proposition(lc, pos, label, f);
  }
  #[allow(clippy::type_complexity)]
  pub fn end_consider(
    &mut self, lc: &LocalContext, start: usize,
    assums: &[(Position, Option<(Option<LabelId>, Rc<str>)>, Formula)],
  ) {
    let State::Prop2(PropKind::Consider(kind)) = self.state else { unreachable!() };
    for fv in &lc.fixed_var.0[start..] {
      self.write_type(lc, &fv.ty)
    }
    self.state = State::InnerAssume;
    for &(pos, ref label, ref f) in assums {
      let label = label.as_ref().and_then(|l| l.0);
      self.write_proposition(lc, pos, label, f)
    }
    self.state = State::Block(kind);
    self.end_tag("Consider")
  }

  pub fn start_reconsider(&mut self) {
    let State::Block(kind) = self.state else { unreachable!() };
    self.state = State::Prop1(PropKind::Reconsider(kind));
    self.start_tag("Reconsider");
  }
  pub fn end_reconsider(&mut self) {
    let State::Prop2(PropKind::Reconsider(kind)) = self.state else { unreachable!() };
    self.state = State::Block(kind);
    self.end_tag("Reconsider")
  }

  pub fn reconsider_var(&mut self, lc: &LocalContext, ty: &Type, tm: &Term) {
    assert!(matches!(self.state, State::Prop1(PropKind::Reconsider(_))));
    self.write_type(lc, ty);
    self.write_term(lc, tm);
  }

  pub fn start_block(&mut self, kind: types::BlockKind, pos: Position) {
    assert!(matches!(self.state, State::Block(BlockKind::Top)));
    self.state = State::Block(BlockKind::Block);
    self.stack.push(Stack::Block(kind));
    self.w.start(kind.name()).pos(pos);
  }
  pub fn end_block(&mut self, kind: types::BlockKind) {
    assert!(matches!(self.state, State::EndBlock(BlockKind::Block)));
    let Some(Stack::Block(kind2)) = self.stack.pop() else { unreachable!() };
    assert!(kind == kind2);
    self.state = State::Block(BlockKind::Top);
    self.w.end_tag(kind.name());
    self.w.newline()
  }

  pub fn write_definiens(&mut self, def: &Definiens) {
    assert!(matches!(self.state, State::Block(BlockKind::Top)));
    self.w.write_definiens(None, def)
  }

  pub fn write_defthm(
    &mut self, lc: &LocalContext, kind: &ConstrKind, pos: Position, label: Option<LabelId>,
    f: &Formula,
  ) {
    assert!(matches!(self.state, State::Block(BlockKind::Top)));
    let attrs = |w: &mut Elem| w.constr_kind(kind);
    self.w.with("DefTheorem", attrs, |w| w.write_proposition(Some(lc), pos, label, f))
  }

  pub fn start_def(
    &mut self, kind: DefinitionKind, pos: Position, label: Option<LabelId>, redef: bool,
  ) {
    assert!(matches!(self.state, State::Block(BlockKind::Block)));
    self.state = State::Correctness1(CorrectnessState::Definition);
    let w = self.w.start("Definition");
    match kind {
      DefinitionKind::Attr => w.attr(b"kind", &b"V"[..]),
      DefinitionKind::Mode => w.attr(b"kind", &b"M"[..]),
      DefinitionKind::Pred => w.attr(b"kind", &b"R"[..]),
      DefinitionKind::Func => w.attr(b"kind", &b"K"[..]),
      DefinitionKind::ExpandMode => {
        w.attr(b"kind", &b"M"[..]);
        w.attr(b"expandable", &b"true"[..])
      }
    }
    if redef {
      w.attr(b"redefinition", &b"true"[..])
    }
    w.pos_and_label(pos, label);
  }
  pub fn end_def(&mut self) {
    let (State::DefEnd | State::StructDef2) = self.state else { unreachable!() };
    self.state = State::Block(BlockKind::Block);
    self.w.end_tag("Definition")
  }

  pub fn start_struct_def(&mut self, pos: Position) {
    assert!(matches!(self.state, State::Block(BlockKind::Block)));
    self.state = State::StructDef1;
    let w = self.w.start("Definition");
    w.attr(b"kind", &b"G"[..]);
    w.pos(pos);
  }
  pub fn end_struct_def(&mut self) { self.end_def() }

  fn start_registration(&mut self) {
    let reg = match self.state {
      State::Block(BlockKind::Block) => RegistrationKind::Reg,
      State::StructDef1 => RegistrationKind::Struct,
      _ => unreachable!(),
    };
    self.state = State::Correctness1(CorrectnessState::Registration(reg));
    self.w.start("Registration");
  }
  pub fn end_registration(&mut self) {
    self.state = match self.state {
      State::RegistrationEnd(RegistrationKind::Reg) => State::Block(BlockKind::Block),
      State::RegistrationEnd(RegistrationKind::Struct) => State::StructDef2,
      _ => unreachable!(),
    };
    self.w.end_tag("Registration")
  }

  pub fn start_identify_func(&mut self, id: &IdentifyFunc) {
    let State::Block(BlockKind::Block) = self.state else { unreachable!() };
    self.state = State::Correctness1(CorrectnessState::Registration(RegistrationKind::Identify));
    self.w.start("IdentifyRegistration");
    self.w.write_identify(None, id)
  }
  pub fn end_identify_func(&mut self) {
    let State::RegistrationEnd(RegistrationKind::Identify) = self.state else { unreachable!() };
    self.state = State::Block(BlockKind::Block);
    self.w.end_tag("IdentifyRegistration")
  }

  pub fn start_reduction(&mut self, red: &Reduction) {
    let State::Block(BlockKind::Block) = self.state else { unreachable!() };
    self.state = State::Correctness1(CorrectnessState::Registration(RegistrationKind::Identify));
    self.w.start("ReductionRegistration");
    self.w.write_reduction(None, red)
  }
  pub fn end_reduction(&mut self) {
    let State::RegistrationEnd(RegistrationKind::Identify) = self.state else { unreachable!() };
    self.state = State::Block(BlockKind::Block);
    self.w.end_tag("ReductionRegistration")
  }

  pub fn start_rcluster(&mut self, primary: &[Type], ty: &Type, attrs: &Attrs) {
    self.start_registration();
    self.w.with0("RCluster", |w| {
      w.write_arg_types(None, primary);
      w.write_type(None, ty);
      w.write_attrs(None, attrs);
      w.write_attrs(None, attrs)
    })
  }

  pub fn start_fcluster(
    &mut self, primary: &[Type], term: &Term, attrs: &Attrs, ty: Option<&Type>,
  ) {
    self.start_registration();
    self.w.with0("FCluster", |w| {
      w.write_arg_types(None, primary);
      w.write_term(None, term);
      w.write_attrs(None, attrs);
      w.write_attrs(None, attrs);
      if let Some(ty) = ty {
        w.write_type(None, ty)
      }
    })
  }

  pub fn start_ccluster(
    &mut self, primary: &[Type], antecedent: &Attrs, ty: &Type, consequent: &Attrs,
  ) {
    self.start_registration();
    self.w.with0("CCluster", |w| {
      w.write_arg_types(None, primary);
      w.write_attrs(None, antecedent);
      w.write_type(None, ty);
      w.write_attrs(None, consequent);
      w.write_attrs(None, consequent)
    })
  }

  pub fn start_sethood_registration(&mut self, prop: &Property) {
    let State::Block(BlockKind::Block) = self.state else { unreachable!() };
    self.state = State::SethoodRegistration1;
    self.w.start("PropertyRegistration");
    let attrs = |w: &mut Elem| w.attr_str(b"x", prop.kind as u8 + 1);
    self.w.with("Property", attrs, |w| {
      w.write_arg_types(None, &prop.primary);
      w.write_type(None, &prop.ty)
    })
  }
  pub fn end_sethood_registration(&mut self) {
    let State::SethoodRegistration2 = self.state else { unreachable!() };
    self.state = State::Block(BlockKind::Block);
    self.w.end_tag("PropertyRegistration")
  }

  pub fn start_corr_cond(&mut self, kind: CorrCondKind) {
    let State::Correctness1(state) = self.state else { unreachable!() };
    self.state = State::Prop1(PropKind::CorrCond(state, kind));
    self.w.start(kind.tag());
  }
  pub fn end_corr_cond(&mut self, kind: CorrCondKind) {
    let State::Prop2(PropKind::CorrCond(state, kind2)) = self.state else { unreachable!() };
    assert!(kind == kind2);
    self.state = State::Correctness1(state);
    self.w.end_tag(kind.tag())
  }

  pub fn skip_correctness(&mut self) {
    let State::Correctness1(state) = self.state else { unreachable!() };
    self.state = match state {
      CorrectnessState::Definition => State::DefProperties,
      CorrectnessState::Registration(kind) => State::RegistrationEnd(kind),
    }
  }
  pub fn start_correctness(&mut self) {
    let State::Correctness1(state) = self.state else { unreachable!() };
    self.state = State::Prop1(PropKind::Correctness(state));
    self.w.start("Correctness");
  }
  pub fn end_correctness(&mut self) {
    let State::Prop2(PropKind::Correctness(state)) = self.state else { unreachable!() };
    self.w.end_tag("Correctness");
    self.state = State::Correctness1(state);
    self.skip_correctness()
  }

  pub fn simple_corr_cond(&mut self, lc: &LocalContext, kind: CorrCondKind, f: &Formula) {
    assert!(matches!(self.state, State::Prop1(PropKind::Correctness(_))));
    self.w.with0(kind.tag(), |w| w.write_formula(Some(lc), f));
  }

  pub fn start_property(&mut self, kind: PropertyKind) {
    assert!(matches!(self.state, State::DefProperties));
    self.state = State::Prop1(PropKind::Property);
    self.w.start("JustifiedProperty");
    self.w.with0(kind.to_upper(), |_| {});
  }
  pub fn end_property(&mut self) {
    let State::Prop2(PropKind::Property) = self.state else { unreachable!() };
    self.state = State::DefProperties;
    self.w.end_tag("JustifiedProperty")
  }

  pub fn skip_constructor(&mut self) {
    assert!(matches!(self.state, State::DefProperties));
    self.state = State::DefEnd;
  }

  pub fn write_pattern(&mut self, i: u32, pat: &Pattern) {
    match self.state {
      State::DefEnd | State::StructDef2 => {}
      State::Block(BlockKind::Block)
        if matches!(self.stack.last(), Some(Stack::Block(types::BlockKind::Notation))) => {}
      _ => unreachable!(),
    }
    self.w.write_pattern(pat, Some(i), |fmt| Some(fmt.0), |_, _| {});
  }
}

macro_rules! mk_write_constructor {
  ($(fn $func:ident($idty:ty, $ty:ty);)*) => {
    impl WriteXml {
      $(
        pub fn $func(&mut self, base: u32, i: $idty, c: &$ty) {
          match self.state {
            State::DefProperties => self.state = (State::DefEnd),
            State::StructDef1 => {}
            _ => unreachable!(),
          }
          self.w.$func(Some((self.art.as_bytes(), i.0)), base + i.0, c);
        }
      )*
    }
  }
}
mk_write_constructor! {
  fn write_attr_constructor(AttrId, TyConstructor<AttrId>);
  fn write_func_constructor(FuncId, TyConstructor<FuncId>);
  fn write_mode_constructor(ModeId, TyConstructor<ModeId>);
  fn write_pred_constructor(PredId, Constructor<PredId>);
  fn write_struct_constructor(StructId, StructMode);
  fn write_aggr_constructor(AggrId, Aggregate);
}
