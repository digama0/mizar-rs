use crate::types::*;
use crate::{CmpStyle, MizPath, OnVarMut, RequirementIndexes, VisitMut};
use enum_map::Enum;
use quick_xml::escape::unescape;
use quick_xml::events::{BytesStart, Event};
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::fs::File;
use std::io::{self, BufRead, BufReader, Read};
use std::str::FromStr;

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

struct XmlReader<'a> {
  r: quick_xml::Reader<BufReader<File>>,
  /// false = InMMLFileObj or InEnvFileObj, true = InVRFFileObj
  two_clusters: bool,
  ctx: MaybeMut<'a, Constructors>,
  depth: u32,
  suppress_bvar_errors: bool,
}

impl MizPath {
  // pub fn open_adhoc(&self, ext: &str) -> io::Result<AdHocReader> {
  //   Ok(AdHocReader(BufReader::new(self.open(ext)?)))
  // }

  fn open_xml_no_pi<'a>(
    &self, ctx: impl Into<MaybeMut<'a, Constructors>>, ext: &str, two_clusters: bool,
  ) -> io::Result<(XmlReader<'a>, Vec<u8>)> {
    let mut r = quick_xml::Reader::from_reader(BufReader::new(self.open(ext)?));
    let mut buf = vec![];
    r.trim_text(true);
    r.expand_empty_elements(true);
    r.check_end_names(true);
    assert!(matches!(r.read_event(&mut buf).unwrap(), Event::Decl(_)));
    Ok((XmlReader { r, two_clusters, ctx: ctx.into(), depth: 0, suppress_bvar_errors: false }, buf))
  }

  /// two_clusters: false = InMMLFileObj or InEnvFileObj, true = InVRFFileObj
  fn open_xml<'a>(
    &self, ctx: impl Into<MaybeMut<'a, Constructors>>, ext: &str, two_clusters: bool,
  ) -> io::Result<(XmlReader<'a>, Vec<u8>)> {
    let mut r = self.open_xml_no_pi(ctx, ext, two_clusters)?;
    assert!(matches!(r.0.r.read_event(&mut r.1).unwrap(), Event::PI(_)));
    Ok(r)
  }

  pub fn read_dcx(&self, syms: &mut Symbols) -> io::Result<()> {
    let (mut r, mut buf) = self.open_xml_no_pi(MaybeMut::None, "dcx", false)?;
    let buf = &mut buf;
    assert!(matches!(r.read_event(buf), Event::Start(e) if e.local_name() == b"Symbols"));
    while let Event::Start(e) = r.read_event(buf) {
      assert!(e.local_name() == b"Symbol");
      let (mut kind, mut nr, mut name) = Default::default();
      for attr in e.attributes() {
        let attr = attr.unwrap();
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
    assert!(matches!(r.read_event(buf), Event::Start(e) if e.local_name() == b"Formats"));
    while let Event::Start(e) = r.read_event(buf) {
      match e.local_name() {
        b"Format" => {
          assert!(formats.priority.is_empty(), "expected <Priority>");
          let (mut kind, mut sym, mut args, mut left, mut rsym) = Default::default();
          for attr in e.attributes() {
            let attr = attr.unwrap();
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
            b'J' => Format::ForgetFunc(FormatForgetFunc { sym: StructSymId(sym), args }),
            b'L' => Format::Struct(FormatStructMode { sym: StructSymId(sym), args }),
            b'M' => Format::Mode(FormatMode { sym: ModeSymId(sym), args }),
            b'U' => Format::Sel(FormatSel { sym: SelSymId(sym), args }),
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
          for attr in e.attributes() {
            let attr = attr.unwrap();
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
    Ok(())
  }

  pub fn read_eno(&self, notas: &mut Notations) -> io::Result<()> {
    let (mut r, mut buf) = self.open_xml(MaybeMut::None, "eno", false)?;
    let buf = &mut buf;
    assert!(matches!(r.read_event(buf), Event::Start(e) if e.local_name() == b"Notations"));
    while let Event::Start(e) = r.read_event(buf) {
      assert!(e.local_name() == b"Pattern");
      let attrs = r.parse_pattern_attrs(&e);
      notas.0.push(r.parse_pattern_body(buf, attrs))
    }
    assert!(matches!(r.read_event(buf), Event::Eof));
    Ok(())
  }

  pub fn read_atr(&self, constrs: &mut Constructors) -> io::Result<()> {
    let (mut r, mut buf) = self.open_xml(constrs, "atr", false)?;
    let buf = &mut buf;
    assert!(matches!(r.read_event(buf), Event::Start(e) if e.local_name() == b"Constructors"));
    while let Event::Start(e) = r.read_event(buf) {
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
    assert!(matches!(r.read_event(&mut buf),
      Event::Start(e) if e.local_name() == b"Registrations"));
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
    assert!(matches!(r.read_event(buf), Event::Start(e) if e.local_name() == b"Definientia"));
    while let Event::Start(e) = r.read_event(buf) {
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
    assert!(
      matches!(r.read_event(buf), Event::Start(e) if e.local_name() == b"PropertyRegistration")
    );
    while let Event::Start(e) = r.read_event(buf) {
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
    assert!(
      matches!(r.read_event(buf), Event::Start(e) if e.local_name() == b"IdentifyRegistrations")
    );
    while let Event::Start(e) = r.read_event(buf) {
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
    assert!(
      matches!(r.read_event(buf), Event::Start(e) if e.local_name() == b"ReductionRegistrations")
    );
    while let Event::Start(e) = r.read_event(buf) {
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
    assert!(matches!(r.read_event(buf), Event::Start(e) if e.local_name() == b"Theorems"));
    while let Event::Start(e) = r.read_event(buf) {
      assert!(e.local_name() == b"Theorem");
      let (mut lib_nr, mut thm_nr, mut kind) = Default::default();
      for attr in e.attributes() {
        let attr = attr.unwrap();
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
    assert!(matches!(r.read_event(buf), Event::Start(e) if e.local_name() == b"Schemes"));
    while let Event::Start(e) = r.read_event(buf) {
      assert!(e.local_name() == b"Scheme");
      let (mut lib_nr, mut sch_nr) = Default::default();
      for attr in e.attributes() {
        let attr = attr.unwrap();
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
    assert!(matches!(r.read_event(&mut buf), Event::Start(e) if e.local_name() == b"Article"));
    let mut p = ArticleParser { r, buf };
    let items = p.parse_items();
    assert!(matches!(p.r.read_event(&mut p.buf), Event::Eof));
    Ok(items)
  }
}

impl XmlReader<'_> {
  fn get_attr<F: FromStr>(&self, value: &[u8]) -> F {
    self.r.decode_without_bom(value).unwrap().parse().ok().unwrap()
  }

  fn get_attr_unescaped(&self, value: &[u8]) -> String {
    String::from_utf8(unescape(value).unwrap().into()).unwrap()
  }

  fn read_event<'a>(&mut self, buf: &'a mut Vec<u8>) -> Event<'a> {
    buf.clear();
    let e = self.r.read_event(buf).unwrap();
    // eprintln!("{:w$}{:?}", "", e, w = backtrace::Backtrace::new().frames().len());
    e
  }

  fn read_to_end(&mut self, tag: &[u8], buf: &mut Vec<u8>) {
    buf.clear();
    self.r.read_to_end(tag, buf).unwrap()
  }

  fn end_tag(&mut self, buf: &mut Vec<u8>) {
    match self.read_event(buf) {
      Event::End(_) => {}
      e => panic!("{:?}", (e, self.dump()).0),
    }
  }

  fn dump(&mut self) {
    let n = self.r.buffer_position();
    let r = self.r.get_mut();
    r.seek_relative(-1024).unwrap();
    let mut out = vec![];
    r.read_to_end(&mut out).unwrap();
    println!("{}", std::str::from_utf8(&out[..1024]).unwrap());
  }

  fn parse_type(&mut self, buf: &mut Vec<u8>) -> Option<Type> {
    match self.parse_elem(buf) {
      Elem::Type(ty) => Some(ty),
      _ => None,
    }
  }

  fn parse_attrs(&mut self, buf: &mut Vec<u8>) -> Attrs {
    assert!(matches!(self.read_event(buf), Event::Start(e) if e.local_name() == b"Cluster"));
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
    if let Event::Start(e) = self.read_event(buf) {
      assert!(e.local_name() == b"Adjective");
      let mut nr = 0;
      let mut pos = true;
      for attr in e.attributes() {
        let attr = attr.unwrap();
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
    for attr in e.attributes() {
      let attr = attr.unwrap();
      match attr.key {
        b"kind" => kind = attr.value[0],
        b"nr" => nr = self.get_attr(&attr.value),
        _ => {}
      }
    }
    (kind, nr)
  }

  fn get_pos_and_label(&mut self, e: &BytesStart<'_>) -> (Position, Option<LabelId>) {
    let (mut pos, mut nr) = (Position::default(), 0u32);
    for attr in e.attributes() {
      let attr = attr.unwrap();
      match attr.key {
        b"line" => pos.line = self.get_attr(&attr.value),
        b"col" => pos.col = self.get_attr(&attr.value),
        b"nr" => nr = self.get_attr(&attr.value),
        _ => {}
      }
    }
    (pos, nr.checked_sub(1).map(LabelId))
  }

  fn parse_cluster_attrs(&mut self, e: &BytesStart<'_>) -> ((Article, u32), ClusterKind) {
    let mut article = Article::default();
    let mut abs_nr = 0;
    for attr in e.attributes() {
      let attr = attr.unwrap();
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
    &mut self, buf: &mut Vec<u8>, (article, abs_nr): (Article, u32),
  ) -> RegisteredCluster {
    let primary = self.parse_arg_types(buf);
    let ty = Box::new(self.parse_type(buf).unwrap());
    let attrs = self.parse_attrs(buf);
    let attrs2 = if self.two_clusters { self.parse_attrs(buf) } else { attrs.clone() };
    let cl = Cluster { primary, consequent: (attrs, attrs2), article, abs_nr };
    self.end_tag(buf);
    RegisteredCluster { cl, ty }
  }

  fn parse_fcluster(
    &mut self, buf: &mut Vec<u8>, (article, abs_nr): (Article, u32),
  ) -> FunctorCluster {
    let primary = self.parse_arg_types(buf);
    let term = Box::new(self.parse_term(buf).unwrap());
    let attrs = self.parse_attrs(buf);
    let attrs2 = if self.two_clusters { self.parse_attrs(buf) } else { attrs.clone() };
    let cl = Cluster { primary, consequent: (attrs, attrs2), article, abs_nr };
    let ty = self.parse_type(buf).map(Box::new);
    if ty.is_some() {
      self.end_tag(buf);
    }
    FunctorCluster { cl, ty, term }
  }

  fn parse_ccluster(
    &mut self, buf: &mut Vec<u8>, (article, abs_nr): (Article, u32),
  ) -> ConditionalCluster {
    let primary = self.parse_arg_types(buf);
    let antecedent = self.parse_attrs(buf);
    let ty = Box::new(self.parse_type(buf).unwrap());
    let attrs = self.parse_attrs(buf);
    let attrs2 = if self.two_clusters { self.parse_attrs(buf) } else { attrs.clone() };
    let cl = Cluster { primary, consequent: (attrs, attrs2), article, abs_nr };
    self.end_tag(buf);
    ConditionalCluster { cl, ty, antecedent }
  }

  fn parse_pairs(&mut self, buf: &mut Vec<u8>, name: &[u8], mut f: impl FnMut(u32, u32)) {
    assert!(matches!(self.read_event(buf), Event::Start(e) if e.local_name() == name));
    while let Event::Start(e) = self.read_event(buf) {
      assert!(e.local_name() == b"Pair");
      let (mut x, mut y) = (0, 0);
      for attr in e.attributes() {
        let attr = attr.unwrap();
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

  fn parse_pattern_attrs(
    &mut self, e: &BytesStart<'_>,
  ) -> (u32, Article, u8, FormatId, u32, Option<u32>, u32, bool) {
    assert!(e.local_name() == b"Pattern");
    let (mut abs_nr, mut article, mut kind, mut fmt, mut constr, mut redefines, mut pid) =
      Default::default();
    let mut pos = true;
    for attr in e.attributes() {
      let attr = attr.unwrap();
      match attr.key {
        b"nr" => abs_nr = self.get_attr(&attr.value),
        b"aid" => article = Article::from_bytes(&attr.value),
        b"kind" => kind = attr.value[0],
        b"formatnr" => fmt = FormatId(self.get_attr::<u32>(&attr.value) - 1),
        b"constrnr" => constr = self.get_attr(&attr.value),
        b"antonymic" => pos = &*attr.value != b"true",
        b"relnr" => pid = Some(self.get_attr::<u32>(&attr.value) - 1),
        b"redefnr" => redefines = self.get_attr::<u32>(&attr.value).checked_sub(1),
        _ => {}
      }
    }
    (abs_nr, article, kind, fmt, constr, redefines, pid.unwrap(), pos)
  }

  fn parse_pattern_body(
    &mut self, buf: &mut Vec<u8>,
    (abs_nr, article, kind, fmt, constr, redefines, pid, pos): (
      u32,
      Article,
      u8,
      FormatId,
      u32,
      Option<u32>,
      u32,
      bool,
    ),
  ) -> Pattern {
    let primary = self.parse_arg_types(buf);
    assert!(matches!(self.read_event(buf),
      Event::Start(e) if e.local_name() == b"Visible"));
    let visible = self.parse_int_list(buf, |n| n as u8 - 1);
    let expansion = if let Event::Start(e) = self.read_event(buf) {
      assert!(e.local_name() == b"Expansion");
      let ty = Box::new(self.parse_type(buf).unwrap());
      self.end_tag(buf);
      self.end_tag(buf);
      Some(ty)
    } else {
      None
    };
    let kind = match (kind, constr.checked_sub(1)) {
      (b'M', Some(nr)) => PatternKind::Mode(ModeId(nr)),
      (b'L', Some(nr)) => PatternKind::Struct(StructId(nr)),
      (b'V', Some(nr)) => PatternKind::Attr(AttrId(nr)),
      (b'R', Some(nr)) => PatternKind::Pred(PredId(nr)),
      (b'K', Some(nr)) => PatternKind::Func(FuncId(nr)),
      (b'U', Some(nr)) => PatternKind::Sel(SelId(nr)),
      (b'G', Some(nr)) => PatternKind::Aggr(AggrId(nr)),
      (b'J', Some(nr)) => PatternKind::ForgetFunc(nr),
      (b'M', None) => PatternKind::ExpandableMode,
      _ => panic!("unknown pattern kind"),
    };
    Pattern { kind, pid, article, abs_nr, fmt, redefines, primary, visible, pos, expansion }
  }

  fn parse_constructor_attrs(
    &mut self, e: &BytesStart<'_>,
  ) -> (Article, u32, u32, u8, u8, u32, u32) {
    assert!(e.local_name() == b"Constructor");
    let (mut article, mut abs_nr, mut redefines, mut superfluous, mut kind, mut aggr, mut base) =
      Default::default();
    for attr in e.attributes() {
      let attr = attr.unwrap();
      match attr.key {
        b"kind" => kind = attr.value[0],
        b"nr" => abs_nr = self.get_attr(&attr.value),
        b"aid" => article = Article::from_bytes(&attr.value),
        b"redefnr" => redefines = self.get_attr(&attr.value),
        b"superfluous" => superfluous = self.get_attr(&attr.value),
        b"structmodeaggrnr" => aggr = self.get_attr(&attr.value),
        b"aggregbase" => base = self.get_attr(&attr.value),
        _ => {}
      }
    }
    (article, abs_nr, redefines, superfluous, kind, aggr, base)
  }

  fn parse_constructor_body(
    &mut self, buf: &mut Vec<u8>,
    (article, abs_nr, redefines, superfluous, kind, aggr, base): (
      Article,
      u32,
      u32,
      u8,
      u8,
      u32,
      u32,
    ),
  ) -> ConstructorDef {
    let ((arg1, arg2, properties), primary) = match self.parse_elem(buf) {
      Elem::Properties(props) => (props, self.parse_arg_types(buf)),
      Elem::ArgTypes(args) => (Default::default(), args),
      _ => panic!("expected <ArgTypes>"),
    };
    macro_rules! constructor {
      ($id:ident) => {{
        let redefines = redefines.checked_sub(1).map($id);
        Constructor { article, abs_nr, primary, redefines, superfluous, properties, arg1, arg2 }
      }};
    }
    let kind = match kind {
      b'M' => {
        let c = constructor!(ModeId);
        ConstructorDef::Mode(TyConstructor { c, ty: self.parse_type(buf).unwrap() })
      }
      b'L' => {
        let c = constructor!(StructId);
        let mut prefixes = vec![];
        let aggr = AggrId(aggr - 1);
        let fields = loop {
          match self.parse_elem(buf) {
            Elem::Type(ty) => {
              assert!(matches!(ty.kind, TypeKind::Struct(_)), "not a struct");
              prefixes.push(ty)
            }
            Elem::Fields(args) => break args,
            _ => panic!("expected <Fields>"),
          }
        };
        ConstructorDef::StructMode(StructMode { c, prefixes: prefixes.into(), aggr, fields })
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
          coll: match self.parse_elem(buf) {
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
    for attr in e.attributes() {
      let attr = attr.unwrap();
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
    assert!(e.local_name() == b"Definiens");
    let (mut article, mut def_nr) = Default::default();
    for attr in e.attributes() {
      let attr = attr.unwrap();
      match attr.key {
        b"aid" => article = Article::from_bytes(&attr.value),
        b"defnr" => def_nr = self.get_attr(&attr.value),
        _ => {}
      }
    }
    (def_nr, article, self.parse_constr_kind(&e).unwrap())
  }

  fn parse_definiens_body(
    &mut self, buf: &mut Vec<u8>, (def_nr, article, constr): (u32, Article, ConstrKind),
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
    let descr = ConstrDescr { def_nr, article, constr, primary: primary.into() };
    let c = ConstrDef { descr, pattern: None };
    Definiens { c, lab_id: None, essential, assumptions, value }
  }

  fn parse_identify_attrs(&mut self, e: &BytesStart<'_>) -> (Article, u32, u8) {
    assert!(e.local_name() == b"Identify");
    let (mut article, mut abs_nr, mut kind) = Default::default();
    for attr in e.attributes() {
      let attr = attr.unwrap();
      match attr.key {
        b"aid" => article = Article::from_bytes(&attr.value),
        b"nr" => abs_nr = self.get_attr(&attr.value),
        b"constrkind" => kind = attr.value[0],
        _ => {}
      }
    }
    (article, abs_nr, kind)
  }

  fn parse_identify_body(
    &mut self, buf: &mut Vec<u8>, (article, abs_nr, kind): (Article, u32, u8),
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
    self.parse_pairs(buf, b"EqArgs", |x, y| eq_args.push((LocusId(x - 1), LocusId(y - 1))));
    self.end_tag(buf);
    Identify { article, abs_nr, primary: primary.into(), kind, eq_args: eq_args.into() }
  }

  fn parse_reduction_attrs(&mut self, e: &BytesStart<'_>) -> (Article, u32) {
    assert!(e.local_name() == b"Reduction");
    let (mut abs_nr, mut article) = Default::default();
    for attr in e.attributes() {
      let attr = attr.unwrap();
      match attr.key {
        b"aid" => article = Article::from_bytes(&attr.value),
        b"nr" => abs_nr = self.get_attr(&attr.value),
        _ => {}
      }
    }
    (article, abs_nr)
  }

  fn parse_reduction_body(
    &mut self, buf: &mut Vec<u8>, (article, abs_nr): (Article, u32),
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
    Reduction { article, abs_nr, primary: primary.into(), terms }
  }

  fn parse_property_attrs(&mut self, e: &BytesStart<'_>) -> (Article, u32, PropertyKind) {
    assert!(e.local_name() == b"Property");
    let (mut abs_nr, mut article, mut kind) = Default::default();
    for attr in e.attributes() {
      let attr = attr.unwrap();
      match attr.key {
        b"aid" => article = Article::from_bytes(&attr.value),
        b"nr" => abs_nr = self.get_attr(&attr.value),
        b"x" => kind = self.get_attr::<usize>(&attr.value),
        _ => {}
      }
    }
    (article, abs_nr, PropertyKind::from_usize(kind - 1))
  }

  fn parse_property_body(
    &mut self, buf: &mut Vec<u8>, (article, abs_nr, kind): (Article, u32, PropertyKind),
  ) -> Property {
    let primary = self.parse_arg_types(buf);
    let ty = self.parse_type(buf).unwrap();
    self.end_tag(buf);
    Property { article, abs_nr, primary, ty, kind }
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
          let mut args = (0, 0, PropertySet::default());
          for attr in e.attributes() {
            let attr = attr.unwrap();
            match attr.key {
              b"propertyarg1" => args.0 = self.get_attr::<u32>(&attr.value).saturating_sub(1),
              b"propertyarg2" => args.1 = self.get_attr::<u32>(&attr.value).saturating_sub(1),
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
          while let Event::Start(e) = self.read_event(buf) {
            assert!(e.local_name() == b"Field");
            let attr = e.attributes().next().unwrap().unwrap();
            assert!(attr.key == b"nr");
            fields.push(SelId(self.get_attr::<u32>(&attr.value) - 1));
            self.end_tag(buf);
          }
          Elem::Fields(fields.into())
        }
        b"LocusVar" => Elem::Term(Term::Locus(LocusId(parse_var!() - 1))),
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
        b"Qua" => {
          let value = Box::new(self.parse_term(buf).unwrap());
          let ty = Box::new(self.parse_type(buf).unwrap());
          self.end_tag(buf);
          Elem::Term(Term::Qua { value, ty })
        }
        b"Choice" => {
          let ty = Box::new(self.parse_type(buf).unwrap());
          self.end_tag(buf);
          Elem::Term(Term::Choice { ty })
        }
        b"It" => {
          self.end_tag(buf);
          Elem::Term(Term::It)
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
          // for attr in e.attributes() {
          //   let attr = attr.unwrap();
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
        b"Essentials" => Elem::Essentials(self.parse_int_list(buf, |n| LocusId(n - 1))),
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

  fn parse_proposition(&mut self, buf: &mut Vec<u8>, quot: bool) -> Option<Proposition> {
    match self.parse_elem(buf) {
      Elem::Proposition(f) => {
        assert!(quot || f.label.is_none());
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

  fn parse_int_list<T>(&mut self, buf: &mut Vec<u8>, f: impl Fn(u32) -> T) -> Box<[T]> {
    let mut out = vec![];
    while let Event::Start(e) = self.read_event(buf) {
      assert!(e.local_name() == b"Int");
      out.push(f(self.get_attr(&e.try_get_attribute(b"x").unwrap().unwrap().value)));
      self.end_tag(buf);
    }
    out.into()
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
  Properties((u32, u32, PropertySet)),
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

struct ArticleParser<'a> {
  r: XmlReader<'a>,
  buf: Vec<u8>,
}

#[derive(Debug)]
enum ArticleElem {
  Item(Item),
  AuxiliaryItem(AuxiliaryItem),
  Let(Vec<Type>),
  Assume(Vec<Proposition>),
  Given(GivenItem),
  Take(Term),
  TakeAsVar(Type, Term),
  Definition(Definition),
  DefStruct(DefStruct),
  Canceled(CancelKind),
  Thus(PrivateStatement),
  PerCases(PerCases),
  PerCasesJustification(Proposition, Justification),
  Registration(Registration),
  SimpleCorrCond(SimpleCorrCond),
  CorrCond(CorrCond),
  Correctness(Correctness),
  JustifiedProperty(JustifiedProperty),
  Constructor(ConstructorDef),
  Pattern(Pattern),
  BlockThesis(Formula),
  Proposition(Proposition),
  CaseOrSupposeBlock(CaseOrSupposeBlock),
  CaseOrSuppose(CaseOrSuppose),
  EndPosition(Position),
  Other,
  End,
}

impl From<ArticleElem> for Item {
  fn from(value: ArticleElem) -> Self {
    match value {
      ArticleElem::Item(it) => it,
      ArticleElem::AuxiliaryItem(it) => Item::AuxiliaryItem(it),
      ArticleElem::Let(it) => Item::Let(it),
      ArticleElem::Assume(it) => Item::Assume(it),
      ArticleElem::Given(it) => Item::Given(it),
      ArticleElem::Take(tm) => Item::Take(tm),
      ArticleElem::TakeAsVar(ty, tm) => Item::TakeAsVar(ty, tm),
      ArticleElem::Definition(decl) => Item::Definition(decl),
      ArticleElem::DefStruct(decl) => Item::DefStruct(decl),
      ArticleElem::Canceled(it) => Item::Canceled(it),
      ArticleElem::Thus(s) => Item::Thus(s),
      ArticleElem::PerCases(it) => Item::PerCases(it),
      ArticleElem::Registration(it) => Item::Registration(it),
      ArticleElem::Pattern(it) => Item::Pattern(it),
      ArticleElem::CorrCond(_)
      | ArticleElem::SimpleCorrCond(_)
      | ArticleElem::Correctness(_)
      | ArticleElem::JustifiedProperty(_)
      | ArticleElem::Constructor(_)
      | ArticleElem::BlockThesis(_)
      | ArticleElem::Proposition(_)
      | ArticleElem::PerCasesJustification(..)
      | ArticleElem::CaseOrSupposeBlock(_)
      | ArticleElem::CaseOrSuppose(_)
      | ArticleElem::EndPosition(_)
      | ArticleElem::Other
      | ArticleElem::End => panic!(),
    }
  }
}

impl ArticleParser<'_> {
  pub fn parse_item(&mut self) -> Option<Item> {
    match self.parse_elem() {
      e @ (ArticleElem::Item(_) | ArticleElem::AuxiliaryItem(_) | ArticleElem::Canceled(_)) =>
        Some(e.into()),
      ArticleElem::Proposition(prop) => Some(self.finish_proposition(prop)),
      ArticleElem::End => {
        assert!(matches!(self.r.read_event(&mut self.buf), Event::Eof));
        None
      }
      _ => panic!("unexpected element"),
    }
  }

  fn parse_items(&mut self) -> Vec<Item> {
    let mut items = vec![];
    while let Some(item) = self.parse_item() {
      items.push(item)
    }
    items
  }

  fn finish_proposition(&mut self, prop: Proposition) -> Item {
    let s = PrivateStatement::Proposition { prop, just: self.parse_justification() };
    Item::AuxiliaryItem(AuxiliaryItem::PrivateStatement(s))
  }

  fn parse_block_thesis(&mut self) -> Option<Formula> {
    match self.parse_elem() {
      ArticleElem::BlockThesis(f) => Some(f),
      _ => None,
    }
  }

  fn parse_thesis(&mut self) -> Thesis {
    let Elem::Thesis(f) = self.r.parse_elem(&mut self.buf) else { panic!("expected thesis") };
    f
  }

  fn parse_reasoning(&mut self, diffuse: bool) -> (Vec<(Item, Option<Thesis>)>, Position) {
    let mut items = vec![];
    let end = loop {
      let e = self.parse_elem();
      match e {
        ArticleElem::AuxiliaryItem(_) | ArticleElem::PerCases(_) => items.push((e.into(), None)),
        ArticleElem::Proposition(prop) => items.push((self.finish_proposition(prop), None)),
        ArticleElem::Let(_)
        | ArticleElem::Thus(_)
        | ArticleElem::Assume(_)
        | ArticleElem::Given(_)
        | ArticleElem::Take(_)
        | ArticleElem::TakeAsVar(..) => {
          let mut thesis = None;
          if !diffuse {
            thesis = Some(self.parse_thesis())
          }
          items.push((e.into(), thesis));
        }
        ArticleElem::EndPosition(pos) => break pos,
        _ => panic!("unexpected reasoning element"),
      }
    };
    (items, end)
  }

  fn parse_references(&mut self) -> Vec<Reference> {
    let mut refs = vec![];
    while let Event::Start(e) = self.r.read_event(&mut self.buf) {
      assert!(e.local_name() == b"Ref");
      let (pos, label) = self.r.get_pos_and_label(&e);
      let (mut article_nr, mut nr, mut kind) = Default::default();
      for attr in e.attributes() {
        let attr = attr.unwrap();
        match attr.key {
          b"kind" => kind = attr.value[0],
          b"nr" => nr = self.r.get_attr(&attr.value),
          b"articlenr" => article_nr = self.r.get_attr(&attr.value),
          _ => {}
        }
      }
      let kind = match kind {
        0 => ReferenceKind::Priv(label.unwrap()),
        b'T' => ReferenceKind::Thm((ArticleId(article_nr), ThmId(nr))),
        b'D' => ReferenceKind::Def((ArticleId(article_nr), DefId(nr))),
        _ => panic!("unexpected inference kind"),
      };
      self.r.end_tag(&mut self.buf);
      refs.push(Reference { pos, kind });
    }
    refs
  }

  fn parse_justification(&mut self) -> Justification {
    let Event::Start(e) = self.r.read_event(&mut self.buf)
    else { panic!("expected justification") };
    match e.local_name() {
      b"By" => {
        let linked =
          e.try_get_attribute(b"linked").unwrap().map_or(false, |attr| &*attr.value == b"true");
        Justification::Simple(Inference {
          kind: InferenceKind::By { linked },
          pos: self.r.get_pos_and_label(&e).0,
          refs: self.parse_references(),
        })
      }
      b"From" => {
        let (mut article_nr, mut nr) = Default::default();
        for attr in e.attributes() {
          let attr = attr.unwrap();
          match attr.key {
            b"nr" => nr = self.r.get_attr(&attr.value),
            b"articlenr" => article_nr = self.r.get_attr(&attr.value),
            _ => {}
          }
        }
        Justification::Simple(Inference {
          kind: InferenceKind::From { sch: (ArticleId(article_nr), SchId(nr)) },
          pos: self.r.get_pos_and_label(&e).0,
          refs: self.parse_references(),
        })
      }
      b"Proof" => {
        let (start, label) = self.r.get_pos_and_label(&e);
        let thesis = self.parse_block_thesis().unwrap();
        let (items, end) = self.parse_reasoning(false);
        self.r.end_tag(&mut self.buf);
        Justification::Proof { pos: (start, end), label, thesis, items }
      }
      b"SkippedProof" => {
        self.r.end_tag(&mut self.buf);
        Justification::SkippedProof
      }
      _ => panic!("unexpected justification"),
    }
  }

  fn parse_simple_justification(&mut self) -> Inference {
    match self.parse_justification() {
      Justification::Simple(just) => just,
      _ => panic!("expected simple justification"),
    }
  }

  fn parse_end_pos(&mut self) -> Position {
    let ArticleElem::EndPosition(pos) = self.parse_elem() else { panic!("expected <EndPosition>") };
    pos
  }

  fn parse_corr_cond(&mut self, kind: CorrCondKind) -> ArticleElem {
    match self.r.parse_elem(&mut self.buf) {
      Elem::Formula(f) => {
        self.r.end_tag(&mut self.buf);
        ArticleElem::SimpleCorrCond(SimpleCorrCond { kind, f })
      }
      Elem::Proposition(prop) => {
        let just = self.parse_justification();
        self.r.end_tag(&mut self.buf);
        ArticleElem::CorrCond(CorrCond { kind, prop, just })
      }
      _ => panic!("invalid correctness condition"),
    }
  }

  fn parse_cond_and_correctness(&mut self) -> (Vec<CorrCond>, Option<Correctness>) {
    let mut conds = vec![];
    loop {
      match self.parse_elem() {
        ArticleElem::CorrCond(cond) => conds.push(cond),
        ArticleElem::Correctness(corr) => {
          self.r.end_tag(&mut self.buf);
          break (conds, Some(corr))
        }
        ArticleElem::End => break (conds, None),
        _ => panic!("expected <Correctness>"),
      }
    }
  }

  fn parse_case_or_suppose_block(
    &mut self, (start, label): (Position, Option<LabelId>),
  ) -> CaseOrSupposeBlock {
    let mut block_thesis = None;
    let cs = loop {
      match self.parse_elem() {
        ArticleElem::BlockThesis(f) => assert!(block_thesis.replace(f).is_none()),
        ArticleElem::CaseOrSuppose(cs) => break cs,
        _ => panic!("expected <Case> / <Suppose>"),
      }
    };
    let thesis = block_thesis.as_ref().map(|_| self.parse_thesis());
    let (items, end) = self.parse_reasoning(block_thesis.is_none());
    let block_thesis = block_thesis.unwrap_or_else(|| self.parse_block_thesis().unwrap());
    self.r.end_tag(&mut self.buf);
    CaseOrSupposeBlock { pos: (start, end), label, block_thesis, cs, items, thesis }
  }

  fn parse_elem(&mut self) -> ArticleElem {
    if let Event::Start(e) = self.r.read_event(&mut self.buf) {
      match e.local_name() {
        b"Section" => {
          // note: unattested in MML
          self.r.end_tag(&mut self.buf);
          ArticleElem::Item(Item::Section)
        }
        b"DefinitionBlock" => {
          let (start, label) = self.r.get_pos_and_label(&e);
          let mut items = vec![];
          let end = loop {
            let e = self.parse_elem();
            match e {
              ArticleElem::AuxiliaryItem(_)
              | ArticleElem::Let(_)
              | ArticleElem::Assume(_)
              | ArticleElem::Given(_)
              | ArticleElem::Definition(_)
              | ArticleElem::DefStruct(_)
              | ArticleElem::Canceled(_) => items.push(e.into()),
              ArticleElem::Proposition(prop) => items.push(self.finish_proposition(prop)),
              ArticleElem::EndPosition(pos) => break pos,
              e => panic!("unexpected definition item {e:?}"),
            }
          };
          self.r.end_tag(&mut self.buf);
          let kind = BlockKind::Definition;
          ArticleElem::Item(Item::Block { kind, pos: (start, end), label, items })
        }
        b"RegistrationBlock" => {
          let (start, label) = self.r.get_pos_and_label(&e);
          let mut items = vec![];
          let end = loop {
            let e = self.parse_elem();
            match e {
              ArticleElem::AuxiliaryItem(_)
              | ArticleElem::Let(_)
              | ArticleElem::Registration(_)
              | ArticleElem::Canceled(_) => items.push(e.into()),
              ArticleElem::Proposition(prop) => items.push(self.finish_proposition(prop)),
              ArticleElem::EndPosition(pos) => break pos,
              _ => panic!("unexpected definition item"),
            }
          };
          self.r.end_tag(&mut self.buf);
          let kind = BlockKind::Registration;
          ArticleElem::Item(Item::Block { kind, pos: (start, end), label, items })
        }
        b"NotationBlock" => {
          let (start, label) = self.r.get_pos_and_label(&e);
          let mut items = vec![];
          let end = loop {
            let e = self.parse_elem();
            match e {
              ArticleElem::AuxiliaryItem(_) | ArticleElem::Let(_) | ArticleElem::Pattern(_) =>
                items.push(e.into()),
              ArticleElem::Proposition(prop) => items.push(self.finish_proposition(prop)),
              ArticleElem::EndPosition(pos) => break pos,
              _ => panic!("unexpected definition item"),
            }
          };
          self.r.end_tag(&mut self.buf);
          let kind = BlockKind::Notation;
          ArticleElem::Item(Item::Block { kind, pos: (start, end), label, items })
        }
        b"Reservation" => {
          // Note: <Var> elements inside reservations are seriously broken. For example, in:
          //   reserve A for set, f for Function of A, {x where x is Nat : x = A};
          // both x and A in the equality are represented as <Var nr="1"/>.
          // Luckily, the checker doesn't really care about reservations, so we just skip them.
          self.r.suppress_bvar_errors = true;
          let mut ids = vec![];
          let ty = loop {
            match self.r.parse_elem(&mut self.buf) {
              Elem::Ident(id) => ids.push(id),
              Elem::Type(ty) => break Box::new(ty),
              _ => panic!("unexpected reservation item"),
            }
          };
          self.r.suppress_bvar_errors = false;
          self.r.end_tag(&mut self.buf);
          ArticleElem::Item(Item::Reservation { ids, ty })
        }
        b"SchemeBlock" => {
          let start = self.r.get_pos_and_label(&e).0;
          let nr = self.r.get_attr(&e.try_get_attribute(b"schemenr").unwrap().unwrap().value);
          let mut decls = vec![];
          loop {
            if let Event::Start(e) = self.r.read_event(&mut self.buf) {
              match e.local_name() {
                b"SchemeFuncDecl" => {
                  let args = self.r.parse_arg_types(&mut self.buf);
                  let ty = self.r.parse_type(&mut self.buf).unwrap();
                  self.r.end_tag(&mut self.buf);
                  decls.push(SchemeDecl::Func { args, ty });
                }
                b"SchemePredDecl" => {
                  let args = self.r.parse_arg_types(&mut self.buf);
                  self.r.end_tag(&mut self.buf);
                  decls.push(SchemeDecl::Pred { args });
                }
                b"SchemePremises" => break,
                _ => panic!("unexpected scheme decl"),
              }
            }
          }
          let mut prems = vec![];
          while let Some(prop) = self.r.parse_proposition(&mut self.buf, true) {
            prems.push(prop);
          }
          let thesis = self.r.parse_proposition(&mut self.buf, false).unwrap();
          let just = self.parse_justification();
          let end = self.parse_end_pos();
          self.r.end_tag(&mut self.buf);
          let bl = SchemeBlock { pos: (start, end), nr: SchId(nr), decls, prems, thesis, just };
          ArticleElem::Item(Item::Scheme(bl))
        }
        b"CaseBlock" => {
          let attrs = self.r.get_pos_and_label(&e);
          let bl = self.parse_case_or_suppose_block(attrs);
          assert!(matches!(bl.cs, CaseOrSuppose::Case(_)));
          ArticleElem::CaseOrSupposeBlock(bl)
        }
        b"SupposeBlock" => {
          let attrs = self.r.get_pos_and_label(&e);
          let bl = self.parse_case_or_suppose_block(attrs);
          assert!(matches!(bl.cs, CaseOrSuppose::Suppose(_)));
          ArticleElem::CaseOrSupposeBlock(bl)
        }
        b"Case" => {
          let mut props = vec![];
          while let Some(prop) = self.r.parse_proposition(&mut self.buf, true) {
            props.push(prop)
          }
          ArticleElem::CaseOrSuppose(CaseOrSuppose::Case(props))
        }
        b"Suppose" => {
          let mut props = vec![];
          while let Some(prop) = self.r.parse_proposition(&mut self.buf, true) {
            props.push(prop)
          }
          ArticleElem::CaseOrSuppose(CaseOrSuppose::Suppose(props))
        }
        b"JustifiedTheorem" => {
          let prop = self.r.parse_proposition(&mut self.buf, true).unwrap();
          let just = self.parse_justification();
          self.r.end_tag(&mut self.buf);
          ArticleElem::Item(Item::Theorem { prop, just })
        }
        b"DefTheorem" => {
          let kind = self.r.parse_constr_kind(&e);
          let prop = self.r.parse_proposition(&mut self.buf, true).unwrap();
          self.r.end_tag(&mut self.buf);
          ArticleElem::Item(Item::DefTheorem { kind, prop })
        }
        b"Definiens" => {
          let attrs = self.r.parse_definiens_attrs(e);
          let df = self.r.parse_definiens_body(&mut self.buf, attrs);
          ArticleElem::Item(Item::Definiens(df))
        }
        b"Proposition" => {
          let (pos, label) = self.r.get_pos_and_label(&e);
          let f = self.r.parse_formula(&mut self.buf).unwrap();
          self.r.end_tag(&mut self.buf);
          ArticleElem::Proposition(Proposition { pos, label, f })
        }
        b"IterEquality" => {
          let (start, label) = self.r.get_pos_and_label(&e);
          let lhs = self.r.parse_term(&mut self.buf).unwrap();
          let mut steps = vec![];
          while let Event::Start(e) = self.r.read_event(&mut self.buf) {
            assert!(e.local_name() == b"IterStep");
            let rhs = self.r.parse_term(&mut self.buf).unwrap();
            let just = self.parse_simple_justification();
            self.r.end_tag(&mut self.buf);
            steps.push((rhs, just));
          }
          let s = PrivateStatement::IterEquality { start, label, lhs, steps };
          ArticleElem::AuxiliaryItem(AuxiliaryItem::PrivateStatement(s))
        }
        b"Now" => {
          let (start, label) = self.r.get_pos_and_label(&e);
          let (items, end) = self.parse_reasoning(true);
          let thesis = self.parse_block_thesis().unwrap();
          self.r.end_tag(&mut self.buf);
          let s = PrivateStatement::Now {
            pos: (start, end),
            label,
            thesis,
            items: items.into_iter().map(|p| p.0).collect(),
          };
          ArticleElem::AuxiliaryItem(AuxiliaryItem::PrivateStatement(s))
        }
        b"Consider" => {
          let prop = self.r.parse_proposition(&mut self.buf, false).unwrap();
          let just = self.parse_justification();
          let (mut fixed, mut parsing_fixed, mut intro) = (vec![], true, vec![]);
          loop {
            match self.r.parse_elem(&mut self.buf) {
              Elem::Type(ty) if parsing_fixed => fixed.push(ty),
              Elem::Proposition(prop) => {
                parsing_fixed = false;
                intro.push(prop)
              }
              Elem::End => break,
              _ => panic!("expected proposition"),
            }
          }
          ArticleElem::AuxiliaryItem(AuxiliaryItem::Consider { prop, just, fixed, intro })
        }
        b"Set" => {
          let term = self.r.parse_term(&mut self.buf).unwrap();
          let ty = self.r.parse_type(&mut self.buf).unwrap();
          self.r.end_tag(&mut self.buf);
          ArticleElem::AuxiliaryItem(AuxiliaryItem::Set { term, ty })
        }
        b"Reconsider" => {
          let mut terms = vec![];
          let prop = loop {
            match self.r.parse_elem(&mut self.buf) {
              Elem::Type(ty) => terms.push((ty, self.r.parse_term(&mut self.buf).unwrap())),
              Elem::Proposition(prop) => break prop,
              _ => panic!("expected proposition"),
            }
          };
          assert!(prop.label.is_none());
          let just = self.parse_justification();
          self.r.end_tag(&mut self.buf);
          ArticleElem::AuxiliaryItem(AuxiliaryItem::Reconsider { terms, prop, just })
        }
        b"DefFunc" => {
          let args = self.r.parse_arg_types(&mut self.buf);
          let value = self.r.parse_term(&mut self.buf).unwrap();
          let ty = self.r.parse_type(&mut self.buf).unwrap();
          self.r.end_tag(&mut self.buf);
          ArticleElem::AuxiliaryItem(AuxiliaryItem::DefFunc { args, value, ty })
        }
        b"DefPred" => {
          let args = self.r.parse_arg_types(&mut self.buf);
          let value = self.r.parse_formula(&mut self.buf).unwrap();
          self.r.end_tag(&mut self.buf);
          ArticleElem::AuxiliaryItem(AuxiliaryItem::DefPred { args, value })
        }
        b"Let" => {
          let mut fixed = vec![];
          while let Some(ty) = self.r.parse_type(&mut self.buf) {
            fixed.push(ty)
          }
          ArticleElem::Let(fixed)
        }
        b"Assume" => {
          let mut props = vec![];
          while let Some(prop) = self.r.parse_proposition(&mut self.buf, true) {
            props.push(prop)
          }
          ArticleElem::Assume(props)
        }
        b"Given" => {
          let prop = self.r.parse_proposition(&mut self.buf, false).unwrap();
          let (mut fixed, mut parsing_fixed, mut intro) = (vec![], true, vec![]);
          loop {
            match self.r.parse_elem(&mut self.buf) {
              Elem::Type(ty) if parsing_fixed => fixed.push(ty),
              Elem::Proposition(prop) => {
                parsing_fixed = false;
                intro.push(prop)
              }
              Elem::End => break,
              _ => panic!("expected proposition"),
            }
          }
          ArticleElem::Given(GivenItem { prop, fixed, intro })
        }
        b"Definition" => {
          let (pos, label) = self.r.get_pos_and_label(&e);
          let (mut expand, mut redef, mut kind) = Default::default();
          for attr in e.attributes() {
            let attr = attr.unwrap();
            match attr.key {
              b"kind" => kind = attr.value[0],
              b"expandable" => expand = &*attr.value == b"true",
              b"redefinition" => redef = &*attr.value == b"true",
              _ => {}
            }
          }
          if kind == b'G' {
            assert!(!expand && !redef);
            let mut constrs = vec![];
            let cl = loop {
              match self.parse_elem() {
                ArticleElem::Constructor(it) => constrs.push(it),
                ArticleElem::Registration(Registration::Cluster(decl)) => break decl,
                _ => panic!("expected cluster"),
              }
            };
            let (mut conds, mut corr, mut patts, mut state) = (vec![], None, vec![], false);
            loop {
              match self.parse_elem() {
                ArticleElem::CorrCond(it) if !state => conds.push(it),
                ArticleElem::Correctness(it) if !state => {
                  state = true;
                  corr = Some(it)
                }
                ArticleElem::Pattern(it) => {
                  state = true;
                  patts.push(it)
                }
                ArticleElem::End => break,
                _ => panic!("expected correctness condition or pattern"),
              }
            }
            ArticleElem::DefStruct(DefStruct { pos, label, constrs, cl, conds, corr, patts })
          } else {
            let kind = match (expand, kind) {
              (false, b'V') => DefinitionKind::PrAttr,
              (false, b'M') => DefinitionKind::Mode,
              (false, b'R') => DefinitionKind::Pred,
              (false, b'K') => DefinitionKind::Func,
              (true, b'M') => DefinitionKind::ExpandMode,
              _ => panic!("unexpected definition kind"),
            };
            let (mut conds, mut corr, mut props, mut constr, mut patts, mut state) =
              (vec![], None, vec![], None, vec![], 0u8);
            loop {
              match self.parse_elem() {
                ArticleElem::CorrCond(it) if state == 0 => conds.push(it),
                ArticleElem::Correctness(it) if state == 0 => {
                  state = 1;
                  corr = Some(it)
                }
                ArticleElem::JustifiedProperty(it) if state <= 1 => {
                  state = 1;
                  props.push(it)
                }
                ArticleElem::Constructor(it) if state <= 1 => {
                  state = 2;
                  constr = Some(it)
                }
                ArticleElem::Pattern(it) if state <= 2 => {
                  state = 3;
                  patts.push(it)
                }
                ArticleElem::End => break,
                _ => panic!("expected correctness condition or pattern"),
              }
            }
            let d = Definition { pos, label, redef, kind, props, conds, corr, constr, patts };
            ArticleElem::Definition(d)
          }
        }
        b"Canceled" => {
          let kind = e.try_get_attribute(b"kind").unwrap().unwrap().value[0];
          self.r.end_tag(&mut self.buf);
          ArticleElem::Canceled(match kind {
            b'D' => CancelKind::Def,
            b'T' => CancelKind::Thm,
            b'S' => CancelKind::Sch,
            _ => panic!("unknown cancel kind"),
          })
        }
        b"Conclusion" => {
          let s = match self.parse_elem() {
            ArticleElem::AuxiliaryItem(AuxiliaryItem::PrivateStatement(s)) => s,
            ArticleElem::Proposition(prop) =>
              PrivateStatement::Proposition { prop, just: self.parse_justification() },
            _ => panic!("expected justified proposition"),
          };
          self.r.end_tag(&mut self.buf);
          ArticleElem::Thus(s)
        }
        b"Take" => {
          let tm = self.r.parse_term(&mut self.buf).unwrap();
          self.r.end_tag(&mut self.buf);
          ArticleElem::Take(tm)
        }
        b"TakeAsVar" => {
          let ty = self.r.parse_type(&mut self.buf).unwrap();
          let tm = self.r.parse_term(&mut self.buf).unwrap();
          self.r.end_tag(&mut self.buf);
          ArticleElem::TakeAsVar(ty, tm)
        }
        b"PerCasesReasoning" => {
          let (start, label) = self.r.get_pos_and_label(&e);
          let mut block_thesis = None;
          let mut cases = vec![];
          let (prop, just) = loop {
            match self.parse_elem() {
              ArticleElem::BlockThesis(f) => assert!(block_thesis.replace(f).is_none()),
              ArticleElem::CaseOrSupposeBlock(cs) => cases.push(cs),
              ArticleElem::PerCasesJustification(prop, just) => break (prop, just),
              _ => panic!("expected <PerCases>"),
            }
          };
          let thesis = block_thesis.as_ref().map(|_| self.parse_thesis());
          let pos = (start, self.parse_end_pos());
          let block_thesis = block_thesis.unwrap_or_else(|| self.parse_block_thesis().unwrap());
          self.r.end_tag(&mut self.buf);
          ArticleElem::PerCases(PerCases { label, cases, prop, just, thesis, pos, block_thesis })
        }
        b"PerCases" => {
          let prop = self.r.parse_proposition(&mut self.buf, false).unwrap();
          let just = self.parse_justification();
          self.r.end_tag(&mut self.buf);
          ArticleElem::PerCasesJustification(prop, just)
        }
        b"Registration" => {
          let Event::Start(e) = self.r.read_event(&mut self.buf)
          else { panic!("expected property") };
          let kind = match self.r.parse_cluster_attrs(&e) {
            (aid, ClusterKind::R) => ClusterDeclKind::R(self.r.parse_rcluster(&mut self.buf, aid)),
            (aid, ClusterKind::F) => ClusterDeclKind::F(self.r.parse_fcluster(&mut self.buf, aid)),
            (aid, ClusterKind::C) => ClusterDeclKind::C(self.r.parse_ccluster(&mut self.buf, aid)),
          };
          let (conds, corr) = self.parse_cond_and_correctness();
          ArticleElem::Registration(Registration::Cluster(ClusterDecl { kind, conds, corr }))
        }
        b"IdentifyRegistration" => {
          let Event::Start(e) = self.r.read_event(&mut self.buf)
          else { panic!("expected identify") };
          let attrs = self.r.parse_identify_attrs(&e);
          let kind = self.r.parse_identify_body(&mut self.buf, attrs);
          let (conds, corr) = self.parse_cond_and_correctness();
          ArticleElem::Registration(Registration::Identify { kind, conds, corr })
        }
        b"ReductionRegistration" => {
          let Event::Start(e) = self.r.read_event(&mut self.buf)
          else { panic!("expected reduction") };
          let attrs = self.r.parse_reduction_attrs(&e);
          let kind = self.r.parse_reduction_body(&mut self.buf, attrs);
          let (conds, corr) = self.parse_cond_and_correctness();
          ArticleElem::Registration(Registration::Reduction { kind, conds, corr })
        }
        b"PropertyRegistration" => {
          let Event::Start(e) = self.r.read_event(&mut self.buf)
          else { panic!("expected property") };
          let attrs = self.r.parse_property_attrs(&e);
          let kind = self.r.parse_property_body(&mut self.buf, attrs);
          let prop = self.r.parse_proposition(&mut self.buf, false).unwrap();
          let just = self.parse_justification();
          self.r.end_tag(&mut self.buf);
          ArticleElem::Registration(Registration::Property { kind, prop, just })
        }
        b"Coherence" => self.parse_corr_cond(CorrCondKind::Coherence),
        b"Compatibility" => self.parse_corr_cond(CorrCondKind::Compatibility),
        b"Consistency" => self.parse_corr_cond(CorrCondKind::Consistency),
        b"Existence" => self.parse_corr_cond(CorrCondKind::Existence),
        b"Uniqueness" => self.parse_corr_cond(CorrCondKind::Uniqueness),
        b"Reducibility" => self.parse_corr_cond(CorrCondKind::Reducibility),
        b"Correctness" => {
          let mut conds = vec![];
          let prop = loop {
            match self.parse_elem() {
              ArticleElem::SimpleCorrCond(it) => conds.push(it),
              ArticleElem::Proposition(prop) => break prop,
              _ => panic!("expected proposition"),
            }
          };
          let just = self.parse_justification();
          self.r.end_tag(&mut self.buf);
          ArticleElem::Correctness(Correctness { conds, prop, just })
        }
        b"JustifiedProperty" => {
          let Event::Start(e) = self.r.read_event(&mut self.buf)
          else { panic!("expected property") };
          let kind = e.local_name().try_into().expect("unexpected property");
          self.r.end_tag(&mut self.buf);
          let prop = self.r.parse_proposition(&mut self.buf, false).unwrap();
          let just = self.parse_justification();
          self.r.end_tag(&mut self.buf);
          ArticleElem::JustifiedProperty(JustifiedProperty { kind, prop, just })
        }
        b"Constructor" => {
          let attrs = self.r.parse_constructor_attrs(&e);
          ArticleElem::Constructor(self.r.parse_constructor_body(&mut self.buf, attrs))
        }
        b"Pattern" => {
          let attrs = self.r.parse_pattern_attrs(&e);
          ArticleElem::Pattern(self.r.parse_pattern_body(&mut self.buf, attrs))
        }
        b"BlockThesis" => {
          // Note: It seems to be somewhat rare, but there is a bvar error in the block thesis
          // at ring_2.miz:2267 indicating some kind of bvar bug in the analyzer.
          // This is in the <Thesis> element which is ignored here, so we just suppress the error.
          self.r.suppress_bvar_errors = true;
          let f = loop {
            match self.r.parse_elem(&mut self.buf) {
              Elem::Formula(f) => break f,
              Elem::Thesis(_) => {}
              _ => panic!("unexpected block thesis element"),
            }
          };
          self.r.suppress_bvar_errors = false;
          self.r.end_tag(&mut self.buf);
          ArticleElem::BlockThesis(f)
        }
        b"EndPosition" => {
          let end = self.r.get_pos_and_label(&e).0;
          self.r.end_tag(&mut self.buf);
          ArticleElem::EndPosition(end)
        }
        _ => ArticleElem::Other,
      }
    } else {
      ArticleElem::End
    }
  }
}
