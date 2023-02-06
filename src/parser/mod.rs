use crate::parser::article::ArticleParser;
use crate::types::*;
use crate::{CmpStyle, MizPath, OnVarMut, RequirementIndexes, VisitMut};
use enum_map::Enum;
use quick_xml::escape::unescape;
use quick_xml::events::{BytesStart, Event};
use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Read};
use std::str::FromStr;

mod article;
mod msm;

impl MizPath {
  pub fn read_ere(&self, idx: &mut RequirementIndexes) -> io::Result<()> {
    let mut r = BufReader::new(self.open("ere")?);
    let mut buf = String::new();
    r.read_line(&mut buf).unwrap();
    assert!(buf.trim_end() == "0");
    buf.clear();
    for (_, val) in &mut idx.fwd {
      r.read_line(&mut buf).unwrap();
      *val = buf.trim_end().parse().unwrap();
      buf.clear();
    }
    idx.init_rev();
    Ok(())
  }

  pub fn read_ref(&self, refs: &mut References) -> io::Result<()> {
    let mut r = BufReader::new(self.open("ref")?);
    fn parse_one<T: Idx>(
      r: &mut impl BufRead, buf: &mut String, map: &mut HashMap<(ArticleId, T), u32>,
    ) -> io::Result<()> {
      let mut c = [0];
      loop {
        r.read_exact(&mut c)?;
        if let [b';'] = c {
          return Ok(())
        }
        r.read_line(buf).unwrap();
        let mut it = buf.split_whitespace();
        let [x1, x2, y] = [(); 3].map(|_| it.next().unwrap().parse().unwrap());
        assert!(map.insert((ArticleId(x1), T::from_usize(x2 as usize)), y).is_none());
        buf.clear();
      }
    }
    let mut buf = String::new();
    parse_one(&mut r, &mut buf, &mut refs.sch)?;
    parse_one(&mut r, &mut buf, &mut refs.thm)?;
    parse_one(&mut r, &mut buf, &mut refs.def)?;
    Ok(())
  }
}

enum MaybeMut<'a, T> {
  Mut(&'a mut T),
  Not(&'a T),
  None,
}
impl<'a, T> From<&'a T> for MaybeMut<'a, T> {
  fn from(v: &'a T) -> Self { Self::Not(v) }
}
impl<'a, T> From<&'a mut T> for MaybeMut<'a, T> {
  fn from(v: &'a mut T) -> Self { Self::Mut(v) }
}
impl<'a, T> MaybeMut<'a, T> {
  fn get(&self) -> Option<&T> {
    match self {
      MaybeMut::Mut(t) => Some(t),
      MaybeMut::Not(t) => Some(t),
      MaybeMut::None => None,
    }
  }
}

struct XmlReader(quick_xml::Reader<BufReader<File>>);

impl XmlReader {
  fn new(file: File, buf: &mut Vec<u8>) -> Self {
    let mut r = quick_xml::Reader::from_reader(BufReader::new(file));
    r.trim_text(true);
    r.expand_empty_elements(true);
    r.check_end_names(true);
    assert!(matches!(r.read_event(buf).unwrap(), Event::Decl(_)));
    Self(r)
  }

  fn read_event<'a>(&mut self, buf: &'a mut Vec<u8>) -> Event<'a> {
    buf.clear();
    let e = self.0.read_event(buf).unwrap();
    // eprintln!("{:w$}{:?}", "", e, w = backtrace::Backtrace::new().frames().len());
    e
  }

  fn try_read_start<'a>(
    &mut self, buf: &'a mut Vec<u8>, expecting: Option<&[u8]>,
  ) -> Result<BytesStart<'a>, Event<'a>> {
    match self.read_event(buf) {
      Event::Start(e) => {
        if let Some(expecting) = expecting {
          assert!(
            e.local_name() == expecting,
            "expected <{}>, got <{}>",
            std::str::from_utf8(expecting).unwrap(),
            std::str::from_utf8(e.local_name()).unwrap()
          )
        }
        Ok(e)
      }
      e => Err(e),
    }
  }

  fn read_start<'a>(&mut self, buf: &'a mut Vec<u8>, expecting: Option<&[u8]>) -> BytesStart<'a> {
    self.try_read_start(buf, expecting).unwrap_or_else(|e| panic!("{:?}", (e, self.dump()).0))
  }

  fn get_attr<F: FromStr>(&self, value: &[u8]) -> F {
    self.0.decode_without_bom(value).unwrap().parse().ok().unwrap()
  }

  fn get_attr_unescaped(&self, value: &[u8]) -> String {
    String::from_utf8(unescape(value).unwrap().into()).unwrap()
  }

  fn read_to_end(&mut self, tag: &[u8], buf: &mut Vec<u8>) {
    buf.clear();
    self.0.read_to_end(tag, buf).unwrap()
  }

  fn end_tag(&mut self, buf: &mut Vec<u8>) {
    match self.read_event(buf) {
      Event::End(_) => {}
      e => panic!("{:?}", (e, self.dump()).0),
    }
  }

  fn dump(&mut self) {
    let r = self.0.get_mut();
    r.seek_relative(-1024).unwrap();
    let mut out = vec![];
    r.read_to_end(&mut out).unwrap();
    println!("{}", std::str::from_utf8(&out[..1024]).unwrap());
  }

  fn get_pos(&mut self, e: &BytesStart<'_>) -> Position {
    let mut pos = Position::default();
    for attr in e.attributes().map(Result::unwrap) {
      match attr.key {
        b"line" => pos.line = self.get_attr(&attr.value),
        b"col" => pos.col = self.get_attr(&attr.value),
        _ => {}
      }
    }
    pos
  }

  fn get_pos_and_label(&mut self, e: &BytesStart<'_>) -> (Position, Option<LabelId>) {
    let (mut pos, mut nr) = (Position::default(), 0u32);
    for attr in e.attributes().map(Result::unwrap) {
      match attr.key {
        b"line" => pos.line = self.get_attr(&attr.value),
        b"col" => pos.col = self.get_attr(&attr.value),
        b"nr" => nr = self.get_attr(&attr.value),
        _ => {}
      }
    }
    (pos, nr.checked_sub(1).map(LabelId))
  }

  fn parse_int_list<T>(&mut self, buf: &mut Vec<u8>, f: impl Fn(u32) -> T) -> Box<[T]> {
    let mut out = vec![];
    while let Ok(e) = self.try_read_start(buf, Some(b"Int")) {
      out.push(f(self.get_attr(&e.try_get_attribute(b"x").unwrap().unwrap().value)));
      self.end_tag(buf);
    }
    out.into()
  }
}

struct MizReader<'a> {
  r: XmlReader,
  /// false = InMMLFileObj or InEnvFileObj, true = InVRFFileObj
  two_clusters: bool,
  ctx: MaybeMut<'a, Constructors>,
  depth: u32,
  suppress_bvar_errors: bool,
}
impl std::ops::Deref for MizReader<'_> {
  type Target = XmlReader;
  fn deref(&self) -> &Self::Target { &self.r }
}
impl std::ops::DerefMut for MizReader<'_> {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.r }
}

impl MizPath {
  // pub fn open_adhoc(&self, ext: &str) -> io::Result<AdHocReader> {
  //   Ok(AdHocReader(BufReader::new(self.open(ext)?)))
  // }

  fn open_xml_no_pi<'a>(
    &self, ctx: impl Into<MaybeMut<'a, Constructors>>, ext: &str, two_clusters: bool,
  ) -> io::Result<(MizReader<'a>, Vec<u8>)> {
    let mut buf = vec![];
    let r = XmlReader::new(self.open(ext)?, &mut buf);
    Ok((MizReader { r, two_clusters, ctx: ctx.into(), depth: 0, suppress_bvar_errors: false }, buf))
  }

  /// two_clusters: false = InMMLFileObj or InEnvFileObj, true = InVRFFileObj
  fn open_xml<'a>(
    &self, ctx: impl Into<MaybeMut<'a, Constructors>>, ext: &str, two_clusters: bool,
  ) -> io::Result<(MizReader<'a>, Vec<u8>)> {
    let mut r = self.open_xml_no_pi(ctx, ext, two_clusters)?;
    assert!(matches!(r.0.r.read_event(&mut r.1), Event::PI(_)));
    Ok(r)
  }

  pub fn read_dcx(&self, syms: &mut Symbols) -> io::Result<()> {
    let (mut r, mut buf) = self.open_xml_no_pi(MaybeMut::None, "dcx", false)?;
    let buf = &mut buf;
    r.read_start(buf, Some(b"Symbols"));
    while let Event::Start(e) = r.read_event(buf) {
      assert!(e.local_name() == b"Symbol");
      let (mut kind, mut nr, mut name) = Default::default();
      for attr in e.attributes().map(Result::unwrap) {
        match attr.key {
          b"kind" => kind = r.get_attr_unescaped(&attr.value).chars().next().unwrap() as u8,
          b"nr" => nr = r.get_attr::<u32>(&attr.value),
          b"name" => name = r.get_attr_unescaped(&attr.value),
          _ => {}
        }
      }
      r.end_tag(buf);
      let kind = match kind {
        b'O' => SymbolKind::Functor(FuncSymId(nr - 1)),
        b'K' | b'[' | b'{' => SymbolKind::LeftBrk(LeftBrkSymId(nr - 1)),
        b'L' | b']' | b'}' => SymbolKind::RightBrk(RightBrkSymId(nr - 1)),
        b'R' | b'=' => SymbolKind::Pred(PredSymId(nr - 1)), // '=' is its own token
        b'M' | 0xE0 => SymbolKind::Mode(ModeSymId(nr - 1)), // 0xE0 = "set", which is in its own token class
        b'V' => SymbolKind::Attr(AttrSymId(nr - 1)),
        b'G' => SymbolKind::Struct(StructSymId(nr - 1)),
        b'U' => SymbolKind::Selector(SelSymId(nr - 1)),
        _ => continue, // the dcx file has a bunch of other crap too
      };
      syms.0.push((kind, name));
    }
    assert!(matches!(r.read_event(buf), Event::Eof));
    Ok(())
  }

  pub fn read_formats(&self, ext: &str, formats: &mut Formats) -> io::Result<()> {
    let (mut r, mut buf) = self.open_xml_no_pi(MaybeMut::None, ext, false)?;
    let buf = &mut buf;
    r.read_start(buf, Some(b"Formats"));
    while let Event::Start(e) = r.read_event(buf) {
      match e.local_name() {
        b"Format" => {
          assert!(formats.priority.is_empty(), "expected <Priority>");
          let (mut kind, mut sym, mut args, mut left, mut rsym) = Default::default();
          for attr in e.attributes().map(Result::unwrap) {
            match attr.key {
              b"kind" => kind = unescape(&attr.value).unwrap()[0],
              b"symbolnr" => sym = r.get_attr::<u32>(&attr.value) - 1,
              b"argnr" => args = Some(r.get_attr(&attr.value)),
              b"leftargnr" => left = Some(r.get_attr(&attr.value)),
              b"rightsymbolnr" => rsym = Some(r.get_attr::<u32>(&attr.value) - 1),
              _ => {}
            }
          }
          let args = args.unwrap();
          formats.formats.push(match kind {
            b'G' => Format::Aggr(FormatAggr { sym: StructSymId(sym), args }),
            b'J' => Format::SubAggr(StructSymId(sym)),
            b'L' => Format::Struct(FormatStruct { sym: StructSymId(sym), args }),
            b'M' => Format::Mode(FormatMode { sym: ModeSymId(sym), args }),
            b'U' => Format::Sel(SelSymId(sym)),
            b'V' => Format::Attr(FormatAttr { sym: AttrSymId(sym), args }),
            b'O' => {
              let left = left.unwrap();
              Format::Func(FormatFunc::Func { sym: FuncSymId(sym), left, right: args - left })
            }
            b'R' => {
              let left = left.unwrap();
              Format::Pred(FormatPred { sym: PredSymId(sym), left, right: args - left })
            }
            b'K' => Format::Func(FormatFunc::Bracket {
              lsym: LeftBrkSymId(sym),
              rsym: RightBrkSymId(rsym.unwrap()),
              args,
            }),
            _ => panic!("unknown format kind"),
          });
        }
        b"Priority" => {
          let (mut kind, mut sym, mut value) = Default::default();
          for attr in e.attributes().map(Result::unwrap) {
            match attr.key {
              b"kind" => kind = attr.value[0],
              b"symbolnr" => sym = r.get_attr(&attr.value),
              b"value" => value = Some(r.get_attr(&attr.value)),
              _ => {}
            }
          }
          let kind = match kind {
            b'O' => PriorityKind::Functor(FuncSymId(sym)),
            b'K' => PriorityKind::LeftBrk(LeftBrkSymId(sym)),
            b'L' => PriorityKind::RightBrk(RightBrkSymId(sym)),
            _ => panic!("unknown format kind"),
          };
          formats.priority.push((kind, value.unwrap()));
        }
        _ => panic!("expected <Format> or <Priority>"),
      }
      r.end_tag(buf);
    }
    assert!(matches!(r.read_event(buf), Event::Eof));
    assert!(matches!(
      formats.formats.get(FormatId::STRICT),
      Some(Format::Attr(FormatAttr { args: 1, .. }))
    ));
    Ok(())
  }

  pub fn read_eno(&self, notas: &mut Vec<Pattern>) -> io::Result<()> {
    let (mut r, mut buf) = self.open_xml(MaybeMut::None, "eno", false)?;
    let buf = &mut buf;
    r.read_start(buf, Some(b"Notations"));
    while let Ok(e) = r.try_read_start(buf, Some(b"Pattern")) {
      let attrs = r.parse_pattern_attrs(&e);
      notas.push(r.parse_pattern_body(buf, attrs))
    }
    assert!(matches!(r.read_event(buf), Event::Eof));
    Ok(())
  }

  pub fn read_atr(&self, constrs: &mut Constructors) -> io::Result<()> {
    let (mut r, mut buf) = self.open_xml(constrs, "atr", false)?;
    let buf = &mut buf;
    r.read_start(buf, Some(b"Constructors"));
    while let Ok(e) = r.try_read_start(buf, Some(b"Constructor")) {
      let attrs = r.parse_constructor_attrs(&e);
      let constr = r.parse_constructor_body(buf, attrs);
      let MaybeMut::Mut(constrs) = &mut r.ctx else { unreachable!() };
      constrs.push(constr);
    }
    assert!(matches!(r.read_event(buf), Event::Eof));
    Ok(())
  }

  pub fn read_ecl(&self, ctx: &Constructors, clusters: &mut Clusters) -> io::Result<()> {
    let (mut r, mut buf) = self.open_xml(ctx, "ecl", false)?;
    r.read_start(&mut buf, Some(b"Registrations"));
    while let Event::Start(e) = r.read_event(&mut buf) {
      match r.parse_cluster_attrs(&e) {
        (aid, ClusterKind::R) => clusters.registered.push(r.parse_rcluster(&mut buf, aid)),
        (aid, ClusterKind::F) => clusters.functor.vec.0.push(r.parse_fcluster(&mut buf, aid)),
        (aid, ClusterKind::C) => clusters.conditional.push(ctx, r.parse_ccluster(&mut buf, aid)),
      }
    }
    assert!(matches!(r.read_event(&mut buf), Event::Eof));
    clusters.functor.sort_all(|a, b| FunctorCluster::cmp_term(&a.term, ctx, &b.term));
    Ok(())
  }

  pub fn read_definitions(
    &self, ctx: &Constructors, ext: &str, defs: &mut Vec<Definiens>,
  ) -> io::Result<()> {
    let (mut r, mut buf) = match self.open_xml(ctx, ext, false) {
      Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
      r => r?,
    };
    let buf = &mut buf;
    r.read_start(buf, Some(b"Definientia"));
    while let Ok(e) = r.try_read_start(buf, Some(b"Definiens")) {
      let attrs = r.parse_definiens_attrs(e);
      defs.push(r.parse_definiens_body(buf, attrs))
    }
    assert!(matches!(r.read_event(buf), Event::Eof));
    Ok(())
  }

  pub fn read_epr(&self, ctx: &Constructors, props: &mut Vec<Property>) -> io::Result<()> {
    let (mut r, mut buf) = match self.open_xml(ctx, "epr", false) {
      Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
      r => r?,
    };
    let buf = &mut buf;
    r.read_start(buf, Some(b"PropertyRegistration"));
    while let Ok(e) = r.try_read_start(buf, Some(b"Property")) {
      let attrs = r.parse_property_attrs(&e);
      props.push(r.parse_property_body(buf, attrs))
    }
    assert!(matches!(r.read_event(buf), Event::Eof));
    Ok(())
  }

  pub fn read_eid(&self, ctx: &Constructors, ids: &mut Vec<Identify>) -> io::Result<()> {
    let (mut r, mut buf) = match self.open_xml(ctx, "eid", false) {
      Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
      r => r?,
    };
    let buf = &mut buf;
    r.read_start(buf, Some(b"IdentifyRegistrations"));
    while let Ok(e) = r.try_read_start(buf, Some(b"Identify")) {
      let attrs = r.parse_identify_attrs(&e);
      ids.push(r.parse_identify_body(buf, attrs));
    }
    assert!(matches!(r.read_event(buf), Event::Eof));
    Ok(())
  }

  pub fn read_erd(&self, ctx: &Constructors, reds: &mut Vec<Reduction>) -> io::Result<()> {
    let (mut r, mut buf) = match self.open_xml(ctx, "erd", false) {
      Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
      r => r?,
    };
    let buf = &mut buf;
    r.read_start(buf, Some(b"ReductionRegistrations"));
    while let Ok(e) = r.try_read_start(buf, Some(b"Reduction")) {
      let attrs = r.parse_reduction_attrs(&e);
      reds.push(r.parse_reduction_body(buf, attrs));
    }
    assert!(matches!(r.read_event(buf), Event::Eof));
    Ok(())
  }

  pub fn read_eth(
    &self, ctx: &Constructors, refs: &References, libs: &mut Libraries,
  ) -> io::Result<()> {
    let (mut r, mut buf) = match self.open_xml(ctx, "eth", false) {
      Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
      r => r?,
    };
    let buf = &mut buf;
    r.read_start(buf, Some(b"Theorems"));
    while let Ok(e) = r.try_read_start(buf, Some(b"Theorem")) {
      let (mut lib_nr, mut thm_nr, mut kind) = Default::default();
      for attr in e.attributes().map(Result::unwrap) {
        match attr.key {
          b"articlenr" => lib_nr = r.get_attr(&attr.value),
          b"nr" => thm_nr = r.get_attr(&attr.value),
          b"kind" => kind = attr.value[0],
          _ => {}
        }
      }
      match kind {
        b'T' if refs.thm.contains_key(&(lib_nr, ThmId(thm_nr))) => {
          let th = r.parse_formula(buf).unwrap();
          r.end_tag(buf);
          libs.thm.insert((lib_nr, ThmId(thm_nr)), th);
        }
        b'D' if refs.def.contains_key(&(lib_nr, DefId(thm_nr))) => {
          let th = r.parse_formula(buf).unwrap();
          r.end_tag(buf);
          libs.def.insert((lib_nr, DefId(thm_nr)), th);
        }
        b'T' | b'D' => r.read_to_end(b"Theorem", buf),
        _ => panic!("unknown theorem kind"),
      }
    }
    assert!(matches!(r.read_event(buf), Event::Eof));
    Ok(())
  }

  pub fn read_esh(
    &self, ctx: &Constructors, refs: &References, libs: &mut Libraries,
  ) -> io::Result<()> {
    let (mut r, mut buf) = match self.open_xml(ctx, "esh", false) {
      Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
      r => r?,
    };
    let buf = &mut buf;
    r.read_start(buf, Some(b"Schemes"));
    while let Ok(e) = r.try_read_start(buf, Some(b"Scheme")) {
      let (mut lib_nr, mut sch_nr) = Default::default();
      for attr in e.attributes().map(Result::unwrap) {
        match attr.key {
          b"articlenr" => lib_nr = r.get_attr(&attr.value),
          b"nr" => sch_nr = r.get_attr(&attr.value),
          _ => {}
        }
      }
      if refs.sch.contains_key(&(lib_nr, sch_nr)) {
        let sch_funcs = r.parse_arg_types(buf);
        let thesis = r.parse_formula(buf).unwrap();
        let mut prems = vec![];
        while let Some(f) = r.parse_formula(buf) {
          prems.push(f)
        }
        assert!(lib_nr != ArticleId::SELF);
        libs.sch.insert((lib_nr, sch_nr), Scheme { sch_funcs, prems: prems.into(), thesis });
      } else {
        r.read_to_end(b"Scheme", buf)
      }
    }
    assert!(matches!(r.read_event(buf), Event::Eof));
    Ok(())
  }

  pub fn read_xml(&self) -> io::Result<Vec<Item>> {
    let (mut r, mut buf) = self.open_xml(MaybeMut::None, "xml", true)?;
    r.read_start(&mut buf, Some(b"Article"));
    let mut p = ArticleParser { r, buf };
    let items = p.parse_items();
    assert!(matches!(p.r.read_event(&mut p.buf), Event::Eof));
    Ok(items)
  }
}

#[derive(Default)]
struct ConstructorAttrs {
  _article: Article,
  _abs_nr: u32,
  redefines: u32,
  superfluous: u8,
  kind: u8,
  aggr: u32,
  base: u8,
}

#[derive(Default)]
struct PatternAttrs {
  _article: Article,
  _abs_nr: u32,
  kind: u8,
  fmt: FormatId,
  constr: u32,
  redefines: Option<u32>,
  pid: u32,
  pos: bool,
}

#[derive(Default)]
struct IdentifyAttrs {
  _article: Article,
  _abs_nr: u32,
  kind: u8,
}

#[derive(Default)]
struct ReductionAttrs {
  _article: Article,
  _abs_nr: u32,
}

struct PropertyAttrs {
  _article: Article,
  _abs_nr: u32,
  kind: PropertyKind,
}

impl MizReader<'_> {
  fn parse_type(&mut self, buf: &mut Vec<u8>) -> Option<Type> {
    match self.parse_elem(buf) {
      Elem::Type(ty) => Some(ty),
      _ => None,
    }
  }

  fn parse_attrs(&mut self, buf: &mut Vec<u8>) -> Attrs {
    self.read_start(buf, Some(b"Cluster"));
    let mut attrs = vec![];
    while let Some(attr) = self.parse_attr(buf) {
      attrs.push(attr)
    }
    if let Some(ctx) = self.ctx.get() {
      attrs.sort_by(|a, b| a.cmp(ctx, None, b, CmpStyle::Strict));
    }
    Attrs::Consistent(attrs)
  }

  fn parse_attr(&mut self, buf: &mut Vec<u8>) -> Option<Attr> {
    if let Ok(e) = self.try_read_start(buf, Some(b"Adjective")) {
      let mut nr = 0;
      let mut pos = true;
      for attr in e.attributes().map(Result::unwrap) {
        match attr.key {
          b"nr" => nr = self.get_attr(&attr.value),
          b"value" if &*attr.value != b"true" => pos = false,
          _ => {}
        }
      }
      Some(Attr { nr: AttrId(nr - 1), pos, args: self.parse_term_list(buf) })
    } else {
      None
    }
  }

  fn get_basic_attrs(&mut self, e: &BytesStart<'_>) -> (u8, u32) {
    let mut kind = 0;
    let mut nr = 0;
    for attr in e.attributes().map(Result::unwrap) {
      match attr.key {
        b"kind" => kind = attr.value[0],
        b"nr" => nr = self.get_attr(&attr.value),
        _ => {}
      }
    }
    (kind, nr)
  }

  fn parse_cluster_attrs(&mut self, e: &BytesStart<'_>) -> ((Article, u32), ClusterKind) {
    let mut article = Article::default();
    let mut abs_nr = 0;
    for attr in e.attributes().map(Result::unwrap) {
      match attr.key {
        b"aid" => article = Article::from_bytes(&attr.value),
        b"nr" => abs_nr = self.get_attr(&attr.value),
        _ => {}
      }
    }
    match e.local_name() {
      b"RCluster" => ((article, abs_nr), ClusterKind::R),
      b"FCluster" => ((article, abs_nr), ClusterKind::F),
      b"CCluster" => ((article, abs_nr), ClusterKind::C),
      _ => panic!("unexpected cluster kind"),
    }
  }

  fn parse_rcluster(
    &mut self, buf: &mut Vec<u8>, (_article, _abs_nr): (Article, u32),
  ) -> RegisteredCluster {
    let primary = self.parse_arg_types(buf);
    let ty = Box::new(self.parse_type(buf).unwrap());
    let attrs = self.parse_attrs(buf);
    let attrs2 = if self.two_clusters { self.parse_attrs(buf) } else { attrs.clone() };
    let cl = Cluster { primary, consequent: (attrs, attrs2) };
    self.end_tag(buf);
    RegisteredCluster { cl, ty }
  }

  fn parse_fcluster(
    &mut self, buf: &mut Vec<u8>, (_article, _abs_nr): (Article, u32),
  ) -> FunctorCluster {
    let primary = self.parse_arg_types(buf);
    let term = Box::new(self.parse_term(buf).unwrap());
    let attrs = self.parse_attrs(buf);
    let attrs2 = if self.two_clusters { self.parse_attrs(buf) } else { attrs.clone() };
    let cl = Cluster { primary, consequent: (attrs, attrs2) };
    let ty = self.parse_type(buf).map(Box::new);
    if ty.is_some() {
      self.end_tag(buf);
    }
    FunctorCluster { cl, ty, term }
  }

  fn parse_ccluster(
    &mut self, buf: &mut Vec<u8>, (_article, _abs_nr): (Article, u32),
  ) -> ConditionalCluster {
    let primary = self.parse_arg_types(buf);
    let antecedent = self.parse_attrs(buf);
    let ty = Box::new(self.parse_type(buf).unwrap());
    let attrs = self.parse_attrs(buf);
    let attrs2 = if self.two_clusters { self.parse_attrs(buf) } else { attrs.clone() };
    let cl = Cluster { primary, consequent: (attrs, attrs2) };
    self.end_tag(buf);
    ConditionalCluster { cl, ty, antecedent }
  }

  fn parse_pairs(&mut self, buf: &mut Vec<u8>, name: &[u8], mut f: impl FnMut(u32, u32)) {
    assert!(matches!(self.read_event(buf), Event::Start(e) if e.local_name() == name));
    while let Ok(e) = self.try_read_start(buf, Some(b"Pair")) {
      let (mut x, mut y) = (0, 0);
      for attr in e.attributes().map(Result::unwrap) {
        match attr.key {
          b"x" => x = self.get_attr(&attr.value),
          b"y" => y = self.get_attr(&attr.value),
          _ => {}
        }
      }
      self.end_tag(buf);
      f(x, y)
    }
  }

  fn parse_nr_attr(&mut self, e: BytesStart<'_>) -> u32 {
    let attr = e.attributes().next().unwrap().unwrap();
    assert!(attr.key == b"nr");
    self.get_attr(&attr.value)
  }

  fn parse_pattern_attrs(&mut self, e: &BytesStart<'_>) -> PatternAttrs {
    let mut attrs = PatternAttrs { pos: true, ..PatternAttrs::default() };
    for attr in e.attributes().map(Result::unwrap) {
      match attr.key {
        b"nr" => attrs._abs_nr = self.get_attr(&attr.value),
        b"aid" => attrs._article = Article::from_bytes(&attr.value),
        b"kind" => attrs.kind = attr.value[0],
        b"formatnr" => attrs.fmt = FormatId(self.get_attr::<u32>(&attr.value) - 1),
        b"constrnr" => attrs.constr = self.get_attr(&attr.value),
        b"antonymic" => attrs.pos = &*attr.value != b"true",
        b"relnr" => attrs.pid = self.get_attr::<u32>(&attr.value),
        b"redefnr" => attrs.redefines = self.get_attr::<u32>(&attr.value).checked_sub(1),
        _ => {}
      }
    }
    attrs.pid = attrs.pid.checked_sub(1).unwrap();
    attrs
  }

  fn parse_pattern_body(
    &mut self, buf: &mut Vec<u8>,
    PatternAttrs { kind, fmt, constr, redefines, pos, .. }: PatternAttrs,
  ) -> Pattern {
    let primary = self.parse_arg_types(buf);
    self.read_start(buf, Some(b"Visible"));
    let visible = self.parse_int_list(buf, |n| LocusId(n as u8 - 1));
    let kind = match (kind, constr.checked_sub(1)) {
      (b'M', Some(nr)) => PatternKind::Mode(ModeId(nr)),
      (b'M', None) => {
        self.read_start(buf, Some(b"Expansion"));
        let expansion = Box::new(self.parse_type(buf).unwrap());
        self.end_tag(buf);
        PatternKind::ExpandableMode { expansion }
      }
      (b'L', Some(nr)) => PatternKind::Struct(StructId(nr)),
      (b'V', Some(nr)) => PatternKind::Attr(AttrId(nr)),
      (b'R', Some(nr)) => PatternKind::Pred(PredId(nr)),
      (b'K', Some(nr)) => PatternKind::Func(FuncId(nr)),
      (b'U', Some(nr)) => PatternKind::Sel(SelId(nr)),
      (b'G', Some(nr)) => PatternKind::Aggr(AggrId(nr)),
      (b'J', Some(nr)) => PatternKind::SubAggr(StructId(nr)),
      _ => panic!("unknown pattern kind"),
    };
    self.end_tag(buf);
    Pattern { kind, fmt, redefines, primary, visible, pos }
  }

  fn parse_constructor_attrs(&mut self, e: &BytesStart<'_>) -> ConstructorAttrs {
    let mut attrs = ConstructorAttrs::default();
    for attr in e.attributes().map(Result::unwrap) {
      match attr.key {
        b"kind" => attrs.kind = attr.value[0],
        b"nr" => attrs._abs_nr = self.get_attr(&attr.value),
        b"aid" => attrs._article = Article::from_bytes(&attr.value),
        b"redefnr" => attrs.redefines = self.get_attr(&attr.value),
        b"superfluous" => attrs.superfluous = self.get_attr(&attr.value),
        b"structmodeaggrnr" => attrs.aggr = self.get_attr(&attr.value),
        b"aggregbase" => attrs.base = self.get_attr(&attr.value),
        _ => {}
      }
    }
    attrs
  }

  fn parse_constructor_body(
    &mut self, buf: &mut Vec<u8>,
    ConstructorAttrs { redefines, superfluous, kind, aggr, base, .. }: ConstructorAttrs,
  ) -> ConstructorDef {
    let ((arg1, arg2, properties), primary) = match self.parse_elem(buf) {
      Elem::Properties(props) => (props, self.parse_arg_types(buf)),
      Elem::ArgTypes(args) => (Default::default(), args),
      _ => panic!("expected <ArgTypes>"),
    };
    macro_rules! constructor {
      ($id:ident) => {{
        let redefines = redefines.checked_sub(1).map($id);
        Constructor { primary, redefines, superfluous, properties, arg1, arg2 }
      }};
    }
    let kind = match kind {
      b'M' => {
        let c = constructor!(ModeId);
        ConstructorDef::Mode(TyConstructor { c, ty: self.parse_type(buf).unwrap() })
      }
      b'L' => {
        let c = constructor!(StructId);
        let mut parents = vec![];
        let aggr = AggrId(aggr - 1);
        let fields = loop {
          match self.parse_elem(buf) {
            Elem::Type(ty) => {
              assert!(matches!(ty.kind, TypeKind::Struct(_)), "not a struct");
              parents.push(ty)
            }
            Elem::Fields(args) => break args,
            _ => panic!("expected <Fields>"),
          }
        };
        ConstructorDef::StructMode(StructMode { c, parents: parents.into(), aggr, fields })
      }
      b'V' => {
        let c = constructor!(AttrId);
        ConstructorDef::Attr(TyConstructor { c, ty: self.parse_type(buf).unwrap() })
      }
      b'R' => ConstructorDef::Pred(constructor!(PredId)),
      b'K' => {
        let c = constructor!(FuncId);
        ConstructorDef::Func(TyConstructor { c, ty: self.parse_type(buf).unwrap() })
      }
      b'U' => {
        let c = constructor!(SelId);
        ConstructorDef::Sel(TyConstructor { c, ty: self.parse_type(buf).unwrap() })
      }
      b'G' | b'J' => {
        let c = constructor!(AggrId);
        ConstructorDef::Aggr(Aggregate {
          c: TyConstructor { c, ty: self.parse_type(buf).unwrap() },
          base,
          fields: match self.parse_elem(buf) {
            Elem::Fields(args) => args,
            _ => panic!("expected <Fields>"),
          },
        })
      }
      _ => panic!("bad kind"),
    };
    self.end_tag(buf);
    kind
  }

  fn parse_constr_kind(&mut self, e: &BytesStart<'_>) -> Option<ConstrKind> {
    let (mut constr_nr, mut constr_kind) = Default::default();
    for attr in e.attributes().map(Result::unwrap) {
      match attr.key {
        b"constrkind" => constr_kind = attr.value[0],
        b"constrnr" => constr_nr = self.get_attr::<u32>(&attr.value) - 1,
        _ => {}
      }
    }
    match constr_kind {
      0 => None,
      b'R' => Some(ConstrKind::Pred(PredId(constr_nr))),
      b'V' => Some(ConstrKind::Attr(AttrId(constr_nr))),
      b'K' => Some(ConstrKind::Func(FuncId(constr_nr))),
      b'M' => Some(ConstrKind::Mode(ModeId(constr_nr))),
      c => panic!("bad constr kind {c}"),
    }
  }

  fn parse_definiens_attrs(&mut self, e: BytesStart<'_>) -> (u32, Article, ConstrKind) {
    let (mut article, mut def_nr) = Default::default();
    for attr in e.attributes().map(Result::unwrap) {
      match attr.key {
        b"aid" => article = Article::from_bytes(&attr.value),
        b"defnr" => def_nr = self.get_attr(&attr.value),
        _ => {}
      }
    }
    (def_nr, article, self.parse_constr_kind(&e).unwrap())
  }

  fn parse_definiens_body(
    &mut self, buf: &mut Vec<u8>, (_def_nr, _article, constr): (u32, Article, ConstrKind),
  ) -> Definiens {
    let mut primary = vec![];
    let essential = loop {
      match self.parse_elem(buf) {
        Elem::Type(ty) => primary.push(ty),
        Elem::Essentials(args) => break args,
        _ => panic!("expected <Essentials>"),
      }
    };
    let (assumptions, value) = match self.parse_elem(buf) {
      Elem::Formula(f) => match self.parse_elem(buf) {
        Elem::DefMeaning(df) => (f, df),
        _ => panic!("expected <DefMeaning>"),
      },
      Elem::DefMeaning(df) => (Formula::True, df),
      _ => panic!("expected <DefMeaning>"),
    };
    self.end_tag(buf);
    let c = ConstrDef { constr, primary: primary.into() };
    Definiens { c, essential, assumptions, value }
  }

  fn parse_identify_attrs(&mut self, e: &BytesStart<'_>) -> IdentifyAttrs {
    let mut attrs = IdentifyAttrs::default();
    for attr in e.attributes().map(Result::unwrap) {
      match attr.key {
        b"aid" => attrs._article = Article::from_bytes(&attr.value),
        b"nr" => attrs._abs_nr = self.get_attr(&attr.value),
        b"constrkind" => attrs.kind = attr.value[0],
        _ => {}
      }
    }
    attrs
  }

  fn parse_identify_body(
    &mut self, buf: &mut Vec<u8>, IdentifyAttrs { kind, .. }: IdentifyAttrs,
  ) -> Identify {
    let mut primary = vec![];
    let kind = loop {
      match self.parse_elem(buf) {
        Elem::Type(ty) => primary.push(ty),
        Elem::Term(lhs) if kind == b'K' =>
          break IdentifyKind::Func { lhs, rhs: self.parse_term(buf).unwrap() },
        Elem::Formula(lhs) if kind == b'K' =>
          break IdentifyKind::Attr { lhs, rhs: self.parse_formula(buf).unwrap() },
        Elem::Formula(lhs) if kind == b'R' =>
          break IdentifyKind::Pred { lhs, rhs: self.parse_formula(buf).unwrap() },
        _ => panic!("unknown identify kind"),
      }
    };
    let mut eq_args = vec![];
    self.parse_pairs(buf, b"EqArgs", |x, y| {
      eq_args.push((LocusId(x as u8 - 1), LocusId(y as u8 - 1)))
    });
    self.end_tag(buf);
    Identify { primary: primary.into(), kind, eq_args: eq_args.into() }
  }

  fn parse_reduction_attrs(&mut self, e: &BytesStart<'_>) -> ReductionAttrs {
    let mut attrs = ReductionAttrs::default();
    for attr in e.attributes().map(Result::unwrap) {
      match attr.key {
        b"aid" => attrs._article = Article::from_bytes(&attr.value),
        b"nr" => attrs._abs_nr = self.get_attr(&attr.value),
        _ => {}
      }
    }
    attrs
  }

  fn parse_reduction_body(
    &mut self, buf: &mut Vec<u8>, ReductionAttrs { .. }: ReductionAttrs,
  ) -> Reduction {
    let mut primary = vec![];
    let terms = loop {
      match self.parse_elem(buf) {
        Elem::Type(ty) => primary.push(ty),
        Elem::Term(t1) => break [t1, self.parse_term(buf).unwrap()],
        _ => panic!("unknown reduction kind"),
      }
    };
    self.end_tag(buf);
    Reduction { primary: primary.into(), terms }
  }

  fn parse_property_attrs(&mut self, e: &BytesStart<'_>) -> PropertyAttrs {
    let (mut _abs_nr, mut _article, mut kind) = Default::default();
    for attr in e.attributes().map(Result::unwrap) {
      match attr.key {
        b"aid" => _article = Article::from_bytes(&attr.value),
        b"nr" => _abs_nr = self.get_attr(&attr.value),
        b"x" => kind = self.get_attr::<usize>(&attr.value),
        _ => {}
      }
    }
    PropertyAttrs { _article, _abs_nr, kind: PropertyKind::from_usize(kind - 1) }
  }

  fn parse_property_body(
    &mut self, buf: &mut Vec<u8>, PropertyAttrs { kind, .. }: PropertyAttrs,
  ) -> Property {
    let primary = self.parse_arg_types(buf);
    let ty = self.parse_type(buf).unwrap();
    self.end_tag(buf);
    Property { primary, ty, kind }
  }

  fn lower(&self) -> impl VisitMut + '_ {
    OnVarMut(|nr| {
      if *nr >= self.depth {
        assert!(*nr != self.depth || self.suppress_bvar_errors);
        *nr = nr.saturating_sub(1)
      }
    })
  }

  fn parse_elem(&mut self, buf: &mut Vec<u8>) -> Elem {
    if let Event::Start(e) = self.read_event(buf) {
      macro_rules! parse_var {
        () => {{
          let nr = self.parse_nr_attr(e);
          self.end_tag(buf);
          nr
        }};
      }
      match e.local_name() {
        b"Typ" => {
          let (kind, nr) = self.get_basic_attrs(&e);
          let kind = match kind {
            b'L' | b'G' => TypeKind::Struct(StructId(nr - 1)),
            b'M' => TypeKind::Mode(ModeId(nr - 1)),
            _ => panic!("bad type kind"),
          };
          let lower = self.parse_attrs(buf);
          let upper = if self.two_clusters { self.parse_attrs(buf) } else { lower.clone() };
          let mut args = vec![];
          while let Some(tm) = self.parse_term(buf) {
            args.push(tm)
          }
          // FIXME: if !g.rounded_up_clusters and we use InEnvFileObj
          // then we have to round up upper here
          Elem::Type(Type { kind, attrs: (lower, upper), args })
        }
        b"Properties" => {
          let mut args = (0, 0, PropertySet::EMPTY);
          for attr in e.attributes().map(Result::unwrap) {
            match attr.key {
              b"propertyarg1" => args.0 = self.get_attr::<u8>(&attr.value).saturating_sub(1),
              b"propertyarg2" => args.1 = self.get_attr::<u8>(&attr.value).saturating_sub(1),
              _ => {}
            }
          }
          while let Event::Start(e) = self.read_event(buf) {
            args.2.set(e.local_name().try_into().expect("unexpected property"));
            self.end_tag(buf);
          }
          Elem::Properties(args)
        }
        b"ArgTypes" => {
          let mut primaries = vec![];
          while let Some(ty) = self.parse_type(buf) {
            primaries.push(ty)
          }
          Elem::ArgTypes(primaries.into())
        }
        b"Fields" => {
          let mut fields = vec![];
          while let Ok(e) = self.try_read_start(buf, Some(b"Field")) {
            let attr = e.attributes().next().unwrap().unwrap();
            assert!(attr.key == b"nr");
            fields.push(SelId(self.get_attr::<u32>(&attr.value) - 1));
            self.end_tag(buf);
          }
          Elem::Fields(fields.into())
        }
        b"LocusVar" => Elem::Term(Term::Locus(LocusId(parse_var!() as u8 - 1))),
        b"Var" => Elem::Term(Term::Bound(BoundId(parse_var!() - 1))),
        b"Const" => Elem::Term(Term::Constant(ConstId(parse_var!() - 1))),
        // b"InfConst" => Elem::Term(Term::Infer { nr: InferId(parse_var!() - 1) }),
        // b"FreeVar" => Elem::Term(Term::FreeVar { nr: parse_var!() - 1 }),
        b"Num" => Elem::Term(Term::Numeral(parse_var!())),
        b"Func" => {
          let (kind, nr) = self.get_basic_attrs(&e);
          let args = self.parse_term_list(buf);
          match kind {
            b'F' => Elem::Term(Term::SchFunc { nr: SchFuncId(nr - 1), args }),
            b'G' => Elem::Term(Term::Aggregate { nr: AggrId(nr - 1), args }),
            b'K' => Elem::Term(Term::Functor { nr: FuncId(nr - 1), args }),
            b'U' => Elem::Term(Term::Selector { nr: SelId(nr - 1), args }),
            _ => panic!("unknown function kind"),
          }
        }
        b"PrivFunc" => {
          let nr = self.parse_nr_attr(e) - 1;
          let value = Box::new(self.parse_term(buf).unwrap());
          let args = self.parse_term_list(buf);
          Elem::Term(Term::PrivFunc { nr: PrivFuncId(nr), args, value })
        }
        b"Fraenkel" => {
          let mut args = vec![];
          let scope = loop {
            match self.parse_elem(buf) {
              Elem::Type(mut ty) => {
                ty.visit(&mut self.lower());
                args.push(ty);
                self.depth += 1;
              }
              Elem::Term(scope) => break Box::new(scope),
              _ => panic!("expected scope term"),
            }
          };
          let compr = Box::new(self.parse_formula(buf).unwrap());
          self.depth -= args.len() as u32;
          self.end_tag(buf);
          Elem::Term(Term::Fraenkel { args: args.into_boxed_slice(), scope, compr })
        }
        b"Choice" => {
          let ty = Box::new(self.parse_type(buf).unwrap());
          self.end_tag(buf);
          Elem::Term(Term::The { ty })
        }
        b"Not" => {
          let f = Box::new(self.parse_formula(buf).unwrap());
          self.end_tag(buf);
          Elem::Formula(Formula::Neg { f })
        }
        b"And" => {
          let mut args = vec![];
          while let Some(f) = self.parse_formula(buf) {
            args.push(f)
          }
          Elem::Formula(Formula::And { args })
        }
        b"Pred" => {
          let (kind, mut nr) = self.get_basic_attrs(&e);
          nr -= 1;
          let args = self.parse_term_list(buf);
          Elem::Formula(match kind {
            b'P' => Formula::SchPred { nr: SchPredId(nr), args },
            b'R' => Formula::Pred { nr: PredId(nr), args },
            b'V' => Formula::Attr { nr: AttrId(nr), args },
            _ => panic!("unknown predicate kind"),
          })
        }
        b"PrivPred" => {
          let nr = self.parse_nr_attr(e) - 1;
          let mut args = vec![];
          let value = loop {
            match self.parse_elem(buf) {
              Elem::Term(tm) => args.push(tm),
              Elem::Formula(f) => break Box::new(f),
              _ => panic!("expected formula"),
            }
          };
          self.end_tag(buf);
          Elem::Formula(Formula::PrivPred { nr: PrivPredId(nr), args: args.into(), value })
        }
        b"For" => {
          // let mut var_id = 0;
          // for attr in e.attributes().map(Result::unwrap) {
          //   if let b"vid" = attr.key {
          //     var_id = self.get_attr(&attr.value)
          //   }
          // }
          let mut dom = Box::new(self.parse_type(buf).unwrap());
          dom.visit(&mut self.lower());
          self.depth += 1;
          let scope = Box::new(self.parse_formula(buf).unwrap());
          self.depth -= 1;
          self.end_tag(buf);
          Elem::Formula(Formula::ForAll { dom, scope })
        }
        b"Is" => {
          let term = Box::new(self.parse_term(buf).unwrap());
          let ty = Box::new(self.parse_type(buf).unwrap());
          self.end_tag(buf);
          Elem::Formula(Formula::Is { term, ty })
        }
        b"FlexFrm" => {
          let orig = Box::new([self.parse_formula(buf).unwrap(), self.parse_formula(buf).unwrap()]);
          let terms = Box::new([self.parse_term(buf).unwrap(), self.parse_term(buf).unwrap()]);
          let expansion = Box::new(self.parse_formula(buf).unwrap());
          self.end_tag(buf);
          Elem::Formula(Formula::FlexAnd { orig, terms, expansion })
        }
        b"Verum" => {
          self.end_tag(buf);
          Elem::Formula(Formula::True)
        }
        b"Essentials" => Elem::Essentials(self.parse_int_list(buf, |n| LocusId(n as u8 - 1))),
        b"DefMeaning" => match self.get_basic_attrs(&e).0 {
          b'm' => {
            let f = |e| if let Elem::Formula(f) = e { Some(f) } else { None };
            Elem::DefMeaning(DefValue::Formula(self.parse_def_body(buf, f)))
          }
          b'e' => {
            let f = |e| if let Elem::Term(f) = e { Some(f) } else { None };
            Elem::DefMeaning(DefValue::Term(self.parse_def_body(buf, f)))
          }
          _ => panic!("unknown def kind"),
        },
        b"PartialDef" => {
          let case = self.parse_elem(buf);
          let guard = self.parse_formula(buf).unwrap();
          self.end_tag(buf);
          Elem::PartialDef(Box::new((case, guard)))
        }
        b"Ident" => {
          let vid =
            e.try_get_attribute(b"vid").unwrap().map_or(0, |attr| self.get_attr(&attr.value));
          self.end_tag(buf);
          Elem::Ident(vid)
        }
        b"Proposition" => {
          let (pos, label) = self.get_pos_and_label(&e);
          let f = self.parse_formula(buf).unwrap();
          self.end_tag(buf);
          Elem::Proposition(Proposition { pos, label, f })
        }
        b"Thesis" => {
          let f = self.parse_formula(buf).unwrap();
          let mut exps = vec![];
          self.parse_pairs(buf, b"ThesisExpansions", |x, y| exps.push((x, y)));
          self.end_tag(buf);
          Elem::Thesis(Thesis { f, exps })
        }
        _ => Elem::Other,
      }
    } else {
      Elem::End
    }
  }

  fn parse_term(&mut self, buf: &mut Vec<u8>) -> Option<Term> {
    match self.parse_elem(buf) {
      Elem::Term(tm) => Some(tm),
      _ => None,
    }
  }

  fn parse_term_list(&mut self, buf: &mut Vec<u8>) -> Box<[Term]> {
    let mut args = vec![];
    while let Some(tm) = self.parse_term(buf) {
      args.push(tm)
    }
    args.into()
  }

  fn parse_formula(&mut self, buf: &mut Vec<u8>) -> Option<Formula> {
    match self.parse_elem(buf) {
      Elem::Formula(f) => Some(f),
      _ => None,
    }
  }

  fn parse_proposition(&mut self, buf: &mut Vec<u8>, quotable: bool) -> Option<Proposition> {
    match self.parse_elem(buf) {
      Elem::Proposition(f) => {
        assert!(quotable || f.label.is_none());
        Some(f)
      }
      _ => None,
    }
  }

  fn parse_arg_types(&mut self, buf: &mut Vec<u8>) -> Box<[Type]> {
    match self.parse_elem(buf) {
      Elem::ArgTypes(tys) => tys,
      _ => panic!("expected <ArgTypes>"),
    }
  }

  fn parse_def_body<T>(
    &mut self, buf: &mut Vec<u8>, get: impl Fn(Elem) -> Option<T>,
  ) -> DefBody<T> {
    let mut cases = vec![];
    let otherwise = loop {
      match self.parse_elem(buf) {
        Elem::PartialDef(e) => cases.push(DefCase { case: get(e.0).unwrap(), guard: e.1 }),
        Elem::End => break None,
        e => {
          self.end_tag(buf);
          break Some(get(e).unwrap())
        }
      }
    };
    DefBody { cases: cases.into(), otherwise }
  }
}

#[derive(Debug)]
enum Elem {
  Type(Type),
  Term(Term),
  Formula(Formula),
  Properties((u8, u8, PropertySet)),
  ArgTypes(Box<[Type]>),
  Fields(Box<[SelId]>),
  Essentials(Box<[LocusId]>),
  DefMeaning(DefValue),
  PartialDef(Box<(Elem, Formula)>),
  Ident(u32),
  Proposition(Proposition),
  Thesis(Thesis),
  Other,
  End,
}

impl TryFrom<Elem> for Type {
  type Error = ();
  fn try_from(e: Elem) -> Result<Type, Self::Error> {
    match e {
      Elem::Type(v) => Ok(v),
      _ => Err(()),
    }
  }
}
impl TryFrom<Elem> for Term {
  type Error = ();
  fn try_from(e: Elem) -> Result<Term, Self::Error> {
    match e {
      Elem::Term(v) => Ok(v),
      _ => Err(()),
    }
  }
}
impl TryFrom<Elem> for Formula {
  type Error = ();
  fn try_from(e: Elem) -> Result<Formula, Self::Error> {
    match e {
      Elem::Formula(v) => Ok(v),
      _ => Err(()),
    }
  }
}
