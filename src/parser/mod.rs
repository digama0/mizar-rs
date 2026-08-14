use crate::parser::article::ArticleParser;
use crate::types::*;
use crate::{CmpStyle, LineMap, MizPath, OnVarMut, RequirementIndexes, VisitMut};
use enum_map::Enum;
use quick_xml::events::{BytesStart, Event};
use std::borrow::Cow;
use std::collections::HashSet;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Read};
use std::path::PathBuf;
use std::result::Result as StdResult;
use std::str::FromStr;
use std::sync::Arc;

mod article;
mod core;
mod json;
mod miz;
mod msm;

pub use core::{Parser, ParserCore};
pub use json::JsonParser;
pub use miz::{MizParser, ParseErr};
pub use msm::MsmParser;

impl MizPath {
  pub fn read_ere(&self, idx: &mut RequirementIndexes) -> Result<()> {
    let mut r = BufReader::new(self.open(true, false, "ere")?);
    let mut buf = String::new();
    let mut pos = r.read_line(&mut buf)?;
    if buf.trim_end() != "0" {
      return Err(ParseError::unexpected_elem(0, "0", None))
    }
    buf.clear();
    for (_, val) in &mut idx.fwd {
      let line = r.read_line(&mut buf)?;
      *val = buf.trim_end().parse().map_err(|_| ParseError::BadInteger(pos))?;
      buf.clear();
      pos += line;
    }
    Ok(())
  }

  pub fn read_ref(&self, refs: &mut References) -> Result<()> {
    let mut r = BufReader::new(self.open(true, false, "ref")?);
    fn parse_one<T: Idx>(
      r: &mut impl BufRead, pos: &mut usize, buf: &mut String, map: &mut HashSet<(ArticleId, T)>,
    ) -> Result<()> {
      let mut c = [0];
      loop {
        r.read_exact(&mut c)?;
        if let [b';'] = c {
          return Ok(())
        }
        *pos += 1;
        let mut pos2 = *pos;
        let line = r.read_line(buf)?;
        let mut it = buf.split_whitespace();
        let mut parse_num = || -> Result<u32> {
          let s = it.next().ok_or_else(|| ParseError::unexpected_elem(pos2, "number", None))?;
          let n = s.parse().map_err(|_| ParseError::BadInteger(pos2))?;
          pos2 += s.len() + 1;
          Ok(n)
        };
        let (x1, x2, _y) = (parse_num()?, parse_num()?, parse_num()?);
        if let Some(x2) = x2.checked_sub(1) {
          if !map.insert((ArticleId(x1), T::from_usize(x2 as usize))) {
            return Err(ParseError::unexpected_elem(pos2, "distinct reference", None))
          }
        }
        buf.clear();
        *pos += line;
      }
    }
    let mut buf = String::new();
    let mut pos = 0;
    parse_one(&mut r, &mut pos, &mut buf, &mut refs.sch)?;
    parse_one(&mut r, &mut pos, &mut buf, &mut refs.thm)?;
    parse_one(&mut r, &mut pos, &mut buf, &mut refs.def)?;
    Ok(())
  }

  pub fn read_sgl(&self, arts: &mut Vec<Article>) -> PathResult<()> {
    with_open(self.to_path(true, false, "sgl"), false, |file| {
      let mut r = BufReader::new(file);
      let mut buf = String::new();
      let mut pos = r.read_line(&mut buf)?;
      let n = buf.trim_end().parse().map_err(|_| ParseError::BadInteger(0))?;
      for _ in 0..n {
        buf.clear();
        let line = r.read_line(&mut buf)?;
        let art = Article::from_upper(buf.trim_end().as_bytes());
        arts.push(art.map_err(|e| ParseError::ToArticle(e, pos))?);
        pos += line;
      }
      // Note: this is not the end of the file (constructor data follows),
      // but the remainder is never parsed by Mizar
      Ok(())
    })
  }

  // pub fn read_dct(file: File, syms: &mut Vec<Token>) -> io::Result<()> {
  //   let mut r = BufReader::new(file);
  //   let mut buf = vec![];
  //   loop {
  //     r.read_until(b'\n', &mut buf)?;
  //     let [c, ref rest @ ..] = *buf else { break };
  //     let i = rest.iter().position(|&c| c == b' ').unwrap();
  //     let n: u32 = std::str::from_utf8(&rest[..i]).unwrap().parse().unwrap();
  //     let value = std::str::from_utf8(&rest[i + 1..]).unwrap().trim_end().to_owned();
  //     syms.push(Token { kind: TokenKind(c, n), value });
  //     buf.clear();
  //   }
  //   Ok(())
  // }
}

impl Article {
  pub fn read_vct<'a>(self, buf: &'a [u8], voc: &mut Vocabulary<'a>) -> Result<bool> {
    let mut pattern = [0; 9];
    let n = self.as_bytes().len();
    pattern[..n].copy_from_slice(self.as_bytes());
    pattern[..n].make_ascii_uppercase();
    pattern[n] = b'\n';
    let pattern = &pattern[..=n];
    let mut pos = 0;
    while let Some(i) = memchr::memchr(b'#', &buf[pos..]) {
      if i.checked_sub(1).is_none_or(|i| buf[pos + i] == b'\n')
        && buf[pos + i + 1..].get(0..pattern.len()) == Some(pattern)
      {
        pos += i + 1 + pattern.len();
        let mut total = 0;
        for (kind, base) in voc.base.0.iter_mut() {
          if buf.get(pos) != Some(&kind.discr()) {
            return Err(ParseError::unexpected_elem(pos, "symbol kind", None))
          }
          let i = (buf[pos + 1..].iter().position(|&c| c == b' '))
            .ok_or_else(|| ParseError::unexpected_elem(pos + 1, "space", Some("eof".into())))?;
          *base = (std::str::from_utf8(&buf[pos + 1..][..i]).ok().and_then(|p| p.parse().ok()))
            .ok_or_else(|| ParseError::BadInteger(pos + 1))?;
          total += *base;
          pos += i + 2;
        }
        pos += 1;
        for _ in 0..total {
          let kind = (buf.get(pos).copied().and_then(parse_symbol_kind))
            .ok_or_else(|| ParseError::unexpected_elem(pos, "symbol kind", None))?;
          let i = (buf[pos + 1..].iter().position(|&c| c == b'\n'))
            .ok_or_else(|| ParseError::unexpected_elem(pos + 1, "newline", Some("eof".into())))?;
          let line = std::str::from_utf8(&buf[pos + 1..][..i])
            .map_err(|_| ParseError::unexpected_elem(pos + 1, "ASCII", None))?
            .trim_end();
          let (token, kind) = match (kind, line.split_once(' ')) {
            (SymbolKindClass::Func, Some((left, right))) => {
              let prio = (right.parse())
                .map_err(|_| ParseError::InvalidVocabLine(pos + 1, line.to_owned()))?;
              (left, SymbolDataKind::Func { prio })
            }
            (SymbolKindClass::Pred, Some((left, right))) => {
              if right.is_empty() || right.contains(' ') {
                return Err(ParseError::unexpected_elem(
                  pos + 2 + left.len(),
                  "token",
                  Some(right.to_owned().into()),
                ))
              }
              (left, SymbolDataKind::Pred { infinitive: Some(right) })
            }
            (_, Some(_)) => return Err(ParseError::InvalidVocabLine(pos + 1, line.to_owned())),
            (SymbolKindClass::Struct, None) => (line, SymbolDataKind::Struct),
            (SymbolKindClass::LeftBrk, None) => (line, SymbolDataKind::LeftBrk),
            (SymbolKindClass::RightBrk, None) => (line, SymbolDataKind::RightBrk),
            (SymbolKindClass::Mode, None) => (line, SymbolDataKind::Mode),
            (SymbolKindClass::Func, None) => (line, SymbolDataKind::Func { prio: DEFAULT_PRIO }),
            (SymbolKindClass::Pred, None) => (line, SymbolDataKind::Pred { infinitive: None }),
            (SymbolKindClass::Sel, None) => (line, SymbolDataKind::Sel),
            (SymbolKindClass::Attr, None) => (line, SymbolDataKind::Attr),
          };
          if token.is_empty() {
            return Err(ParseError::unexpected_elem(pos + 1, "symbol token", None))
          }
          voc.symbols.push(SymbolData { kind, token });
          pos += i + 2;
        }
        return Ok(true)
      }
      pos += i + 1;
    }
    Ok(false)
  }
}

/// A non-panicking version of [`SymbolKindClass::parse`], for bytes that come
/// from a (possibly malformed) dependency file.
fn parse_symbol_kind(c: u8) -> Option<SymbolKindClass> {
  match c {
    b'G' => Some(SymbolKindClass::Struct),
    b'K' => Some(SymbolKindClass::LeftBrk),
    b'L' => Some(SymbolKindClass::RightBrk),
    b'M' => Some(SymbolKindClass::Mode),
    b'O' => Some(SymbolKindClass::Func),
    b'R' => Some(SymbolKindClass::Pred),
    b'U' => Some(SymbolKindClass::Sel),
    b'V' => Some(SymbolKindClass::Attr),
    _ => None,
  }
}

pub enum MaybeMut<'a, T> {
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

#[derive(Debug)]
pub enum ParseError {
  Xml(Option<usize>, quick_xml::Error),
  UnexpectedElement { pos: usize, expected: &'static str, found: Option<Cow<'static, str>> },
  ExpectedEof(usize),
  BadInteger(usize),
  ToArticle(ToArticleError, usize),
  InvalidVocabLine(usize, String),
  MissingFile,
  BadUtf8(usize),
}

impl ParseError {
  pub fn unexpected_elem(
    pos: usize, expected: &'static str, found: Option<Cow<'static, str>>,
  ) -> Self {
    Self::UnexpectedElement { pos, expected, found }
  }
}

pub type Result<T> = StdResult<T, ParseError>;
pub type PathResult<T> = StdResult<T, (PathBuf, ParseError)>;

impl From<quick_xml::Error> for ParseError {
  fn from(v: quick_xml::Error) -> Self { Self::Xml(None, v) }
}
impl From<quick_xml::events::attributes::AttrError> for ParseError {
  fn from(v: quick_xml::events::attributes::AttrError) -> Self { Self::Xml(None, v.into()) }
}
impl From<io::Error> for ParseError {
  fn from(v: io::Error) -> Self { Self::Xml(None, v.into()) }
}

impl std::fmt::Display for ParseError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      ParseError::Xml(_, e) => e.fmt(f),
      ParseError::UnexpectedElement { expected, found: Some(found), .. } =>
        write!(f, "expected {expected}, got {found}"),
      ParseError::UnexpectedElement { expected, found: None, .. } =>
        write!(f, "expected {expected}"),
      ParseError::ExpectedEof(_) => write!(f, "expected EOF"),
      ParseError::BadInteger(_) => write!(f, "not an integer or out of range"),
      ParseError::InvalidVocabLine(_, line) => write!(f, "invalid vocabulary line '{line}'"),
      ParseError::MissingFile => write!(f, "file not found"),
      ParseError::BadUtf8(_) => write!(f, "the file is not valid UTF-8"),
      ParseError::ToArticle(e, _) => e.fmt(f),
    }
  }
}

impl ParseError {
  pub fn pos(&self) -> Option<usize> {
    match *self {
      ParseError::Xml(pos, _) => pos,
      ParseError::UnexpectedElement { pos, .. }
      | ParseError::ExpectedEof(pos)
      | ParseError::BadInteger(pos)
      | ParseError::ToArticle(_, pos)
      | ParseError::InvalidVocabLine(pos, _)
      | ParseError::BadUtf8(pos) => Some(pos),
      ParseError::MissingFile => None,
    }
  }
}

pub trait FromStrPos: FromStr {
  fn to_err(e: Self::Err, pos: usize) -> ParseError;
}
impl FromStrPos for u8 {
  fn to_err(_: Self::Err, pos: usize) -> ParseError { ParseError::BadInteger(pos) }
}
impl FromStrPos for u32 {
  fn to_err(_: Self::Err, pos: usize) -> ParseError { ParseError::BadInteger(pos) }
}
impl FromStrPos for usize {
  fn to_err(_: Self::Err, pos: usize) -> ParseError { ParseError::BadInteger(pos) }
}

pub fn catch_missing<T>(result: PathResult<T>) -> PathResult<Option<T>> {
  match result {
    Err((_, ParseError::MissingFile)) => Ok(None),
    _ => result.map(Some),
  }
}

/// The second field is the line map of the current article's `.miz` source,
/// used to translate the legacy `line:col` positions in the XML back into
/// byte-offset [`Span`]s. `None` when the source is unavailable, in which case
/// positions become [`Span::NONE`]. TODO(spans): thread the source through the
/// secondary (`-P`/`-c`) read paths so this is populated.
struct XmlReader(quick_xml::Reader<BufReader<File>>, Option<Arc<LineMap>>);

impl XmlReader {
  fn new(file: File, buf: &mut Vec<u8>) -> Result<Self> {
    let mut r = quick_xml::Reader::from_reader(BufReader::new(file));
    r.trim_text(true);
    r.expand_empty_elements(true);
    r.check_end_names(true);
    if !matches!(r.read_event_into(buf)?, Event::Decl(_)) {
      return Err(ParseError::unexpected_elem(r.buffer_position(), "xml declaration", None))
    }
    Ok(Self(r, None))
  }

  fn set_pos(&self, e: &mut ParseError) {
    match e {
      ParseError::Xml(pos @ None, _) => *pos = Some(self.0.buffer_position()),
      ParseError::Xml(..)
      | ParseError::UnexpectedElement { .. }
      | ParseError::ExpectedEof(_)
      | ParseError::BadInteger(_)
      | ParseError::ToArticle(..)
      | ParseError::InvalidVocabLine(..)
      | ParseError::MissingFile
      | ParseError::BadUtf8(_) => {}
    }
  }

  fn read_event<'a>(&mut self, buf: &'a mut Vec<u8>) -> Result<Event<'a>> {
    buf.clear();
    let e = self.0.read_event_into(buf)?;
    // vprintln!("{:w$}{:?}", "", e, w = backtrace::Backtrace::new().frames().len());
    Ok(e)
  }

  fn try_read_start<'a>(
    &mut self, buf: &'a mut Vec<u8>, expecting: Option<&'static str>,
  ) -> Result<StdResult<BytesStart<'a>, Event<'a>>> {
    let pos = self.0.buffer_position();
    Ok(match self.read_event(buf)? {
      Event::Start(e) => {
        if let Some(expecting) = expecting {
          if e.local_name().as_ref() != expecting.as_bytes() {
            let got = String::from_utf8_lossy(e.local_name().as_ref()).to_string();
            return Err(ParseError::unexpected_elem(pos, expecting, Some(got.into())))
          }
        }
        Ok(e)
      }
      e => Err(e),
    })
  }

  fn read_start<'a>(
    &mut self, buf: &'a mut Vec<u8>, expecting: Option<&'static str>,
  ) -> Result<BytesStart<'a>> {
    let pos = self.0.buffer_position();
    match self.try_read_start(buf, expecting)? {
      Ok(t) => Ok(t),
      Err(e) => Err(ParseError::unexpected_elem(
        pos,
        expecting.unwrap_or("element start"),
        Some(format!("{e:?}").into()),
      )),
    }
  }

  fn eof(&mut self, buf: &mut Vec<u8>) -> Result<()> {
    if let Event::Eof = self.read_event(buf)? {
      Ok(())
    } else {
      Err(ParseError::ExpectedEof(self.0.buffer_position()))
    }
  }

  fn get_attr<F: FromStrPos>(&self, value: &[u8]) -> Result<F> {
    let pos = self.0.buffer_position();
    self.0.decoder().decode(value)?.parse().map_err(|e| F::to_err(e, pos))
  }

  /// A parse error at the current byte position. The dependency readers use this to
  /// turn structural assumptions about the XML into recoverable errors: the message
  /// is deliberately terse, but the position lets `ParseError::report` point at
  /// `path:line:col`.
  fn err<T>(&self, expected: &'static str) -> Result<T> {
    Err(ParseError::unexpected_elem(self.0.buffer_position(), expected, None))
  }

  /// Read a 1-based index attribute and convert it to the 0-based representation.
  ///
  /// The legacy XML format numbers these from 1, so `0` is not a legal value and
  /// used to underflow-panic in debug builds. Fields where `0` legitimately means
  /// "absent" instead use `get_attr(..)?.checked_sub(1)` and stay `Option`.
  fn idx_attr(&self, value: &[u8]) -> Result<u32> {
    match self.get_attr::<u32>(value)?.checked_sub(1) {
      Some(n) => Ok(n),
      None => Err(ParseError::BadInteger(self.0.buffer_position())),
    }
  }

  /// [`idx_attr`](Self::idx_attr) for the `u8`-width indices (loci).
  fn idx_attr_u8(&self, value: &[u8]) -> Result<u8> {
    match self.get_attr::<u8>(value)?.checked_sub(1) {
      Some(n) => Ok(n),
      None => Err(ParseError::BadInteger(self.0.buffer_position())),
    }
  }

  /// [`idx_attr`](Self::idx_attr) for a 1-based index that was already read (rather
  /// than read straight from an attribute), reporting instead of underflow-panicking
  /// on a corrupt file where it is `0`.
  fn dec1(&self, n: u32) -> Result<u32> {
    n.checked_sub(1).ok_or_else(|| ParseError::BadInteger(self.0.buffer_position()))
  }

  /// Parse an article name coming from the file, reporting a positioned error
  /// instead of panicking when it isn't a valid article identifier.
  fn to_article(&self, value: &[u8]) -> Result<Article> {
    Article::from_upper(value).map_err(|e| ParseError::ToArticle(e, self.0.buffer_position()))
  }

  /// The first byte of an attribute's raw value.
  fn attr_byte(&self, attr: &quick_xml::events::attributes::Attribute<'_>) -> Result<u8> {
    match attr.value.first() {
      Some(&c) => Ok(c),
      None => self.err("nonempty attribute"),
    }
  }

  /// The first character of an attribute's unescaped value, as a byte.
  fn attr_char(&self, attr: &quick_xml::events::attributes::Attribute<'_>) -> Result<u8> {
    match attr.unescape_value()?.chars().next() {
      Some(c) => Ok(c as u8),
      None => self.err("nonempty attribute"),
    }
  }

  fn read_to_end(&mut self, tag: &[u8], buf: &mut Vec<u8>) -> Result<()> {
    buf.clear();
    self.0.read_to_end_into(quick_xml::name::QName(tag), buf)?;
    Ok(())
  }

  fn end_tag(&mut self, buf: &mut Vec<u8>) -> Result<()> {
    match self.read_event(buf)? {
      Event::End(_) => Ok(()),
      _ => self.err("element end"),
    }
  }

  #[allow(unused)]
  fn dump(&mut self) {
    let r = self.0.get_mut();
    let _ = r.seek_relative(-1024);
    let mut out = vec![];
    r.read_to_end(&mut out).unwrap();
    println!("{}", std::str::from_utf8(&out[..1024]).unwrap());
  }

  /// Translate a legacy `line:col` (with optional `posline:poscol` end) into a
  /// byte-offset [`Span`], or [`Span::NONE`] if no source line map is loaded.
  fn to_span(&self, start: (u32, u32), end: (u32, u32)) -> Span {
    self.1.as_ref().map_or(Span::NONE, |lines| lines.span(start, end))
  }

  fn get_pos(&mut self, e: &BytesStart<'_>) -> Result<Span> {
    let (mut start, mut end) = ((0, 0), (0, 0));
    for attr in e.attributes() {
      let attr = attr?;
      match attr.key.0 {
        b"line" => start.0 = self.get_attr(&attr.value)?,
        b"col" => start.1 = self.get_attr(&attr.value)?,
        b"posline" => end.0 = self.get_attr(&attr.value)?,
        b"poscol" => end.1 = self.get_attr(&attr.value)?,
        _ => {}
      }
    }
    Ok(self.to_span(start, end))
  }

  fn get_pos_and_label(&mut self, e: &BytesStart<'_>) -> Result<(Span, Option<LabelId>)> {
    let (mut start, mut end, mut nr) = ((0, 0), (0, 0), 0u32);
    for attr in e.attributes() {
      let attr = attr?;
      match attr.key.0 {
        b"line" => start.0 = self.get_attr(&attr.value)?,
        b"col" => start.1 = self.get_attr(&attr.value)?,
        b"posline" => end.0 = self.get_attr(&attr.value)?,
        b"poscol" => end.1 = self.get_attr(&attr.value)?,
        b"nr" => nr = self.get_attr(&attr.value)?,
        _ => {}
      }
    }
    Ok((self.to_span(start, end), nr.checked_sub(1).map(LabelId)))
  }

  fn parse_loci(&mut self, buf: &mut Vec<u8>) -> Result<Box<[LocusId]>> {
    let mut out = vec![];
    while let Ok(e) = self.try_read_start(buf, Some("Int"))? {
      let Some(attr) = e.try_get_attribute(b"x")? else { return self.err("x attribute") };
      out.push(LocusId(self.idx_attr_u8(&attr.value)?));
      self.end_tag(buf)?;
    }
    Ok(out.into())
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

impl<'a> MizReader<'a> {
  /// two_clusters: false = InMMLFileObj or InEnvFileObj, true = InVRFFileObj
  fn new(
    file: File, ctx: impl Into<MaybeMut<'a, Constructors>>, two_clusters: bool,
  ) -> Result<(MizReader<'a>, Vec<u8>)> {
    let mut buf = vec![];
    let r = XmlReader::new(file, &mut buf)?;
    Ok((MizReader { r, two_clusters, ctx: ctx.into(), depth: 0, suppress_bvar_errors: false }, buf))
  }

  fn position(&self) -> usize { self.r.0.buffer_position() }

  fn with<R>(
    file: File, ctx: impl Into<MaybeMut<'a, Constructors>>, two_clusters: bool,
    f: impl FnOnce(&mut MizReader<'a>, &mut Vec<u8>) -> Result<R>,
  ) -> Result<R> {
    let (mut r, mut buf) = Self::new(file, ctx, two_clusters)?;
    let mut result = f(&mut r, &mut buf);
    if let Err(e) = &mut result {
      r.set_pos(e)
    }
    result
  }

  fn read_pi(&mut self, buf: &mut Vec<u8>) -> Result<()> {
    if !matches!(self.r.read_event(buf)?, Event::PI(_)) {
      return self.err("processing instruction")
    }
    Ok(())
  }
}

fn with_open<T>(
  path: PathBuf, allow_empty: bool, f: impl FnOnce(File) -> Result<T>,
) -> PathResult<T> {
  match File::open(&path) {
    Err(e) if allow_empty && e.kind() == io::ErrorKind::NotFound =>
      Err((path, ParseError::MissingFile)),
    file => (|| f(file?))().map_err(|e| (path, e)),
  }
}

fn with_open0(path: PathBuf, f: impl FnOnce(File) -> Result<()>) -> PathResult<()> {
  catch_missing(with_open(path, true, f)).map(|_| ())
}

impl MizPath {
  pub fn read_evl(&self, dirs: &mut Directives) -> PathResult<()> {
    with_open(self.to_path(true, false, "evl"), false, |file| {
      MizReader::with(file, MaybeMut::None, false, |r, buf| {
        r.read_start(buf, Some("Environ"))?;
        for (i, dir) in &mut dirs.0 {
          let e = r.read_start(buf, Some("Directive"))?;
          let Some(attr) = e.try_get_attribute("name")? else { return r.err("name attribute") };
          if *attr.value != *i.name().as_bytes() {
            return r.err("directive name")
          }
          while let Ok(e) = r.try_read_start(buf, Some("Ident"))? {
            let pos = r.get_pos(&e)?;
            let Some(attr) = e.try_get_attribute("name")? else { return r.err("name attribute") };
            dir.push(ArticleAt { pos, art: r.to_article(&attr.value)? });
            r.end_tag(buf)?;
          }
        }
        r.end_tag(buf)?;
        r.eof(buf)
      })
    })
  }

  pub fn read_dcx(&self, syms: &mut Symbols) -> PathResult<()> {
    with_open(self.to_path(true, false, "dcx"), false, |file| {
      MizReader::with(file, MaybeMut::None, false, |r, buf| {
        r.read_start(buf, Some("Symbols"))?;
        while let Ok(e) = r.try_read_start(buf, Some("Symbol"))? {
          let (mut kind, mut nr, mut name) = Default::default();
          for attr in e.attributes() {
            let attr = attr?;
            match attr.key.0 {
              b"kind" => kind = r.attr_char(&attr)?,
              b"nr" => nr = r.get_attr::<u32>(&attr.value)?,
              b"name" => name = attr.unescape_value()?.to_string(),
              _ => {}
            }
          }
          r.end_tag(buf)?;
          // legacy 1-based symbol index; 0 (or a missing `nr`) is not legal
          let Some(nr) = nr.checked_sub(1) else { return r.err("symbol nr") };
          let kind = match kind {
            b'O' => SymbolKind::Func(FuncSymId(nr)),
            b'K' | b'[' | b'{' | b'(' => SymbolKind::LeftBrk(LeftBrkSymId(nr)),
            b'L' | b']' | b'}' | b')' => SymbolKind::RightBrk(RightBrkSymId(nr)),
            b'R' | b'=' => SymbolKind::Pred(PredSymId(nr)), // '=' is its own token
            b'M' | 0xE0 => SymbolKind::Mode(ModeSymId(nr)), // 0xE0 = "set", which is in its own token class
            b'V' => SymbolKind::Attr(AttrSymId(nr)),
            b'G' => SymbolKind::Struct(StructSymId(nr)),
            b'U' => SymbolKind::Sel(SelSymId(nr)),
            _ => continue, // the dcx file has a bunch of other crap too
          };
          syms.push((kind, name));
        }
        r.eof(buf)
      })
    })
  }

  pub fn read_vcl(&self, vocs: &mut Vocabularies) -> PathResult<()> {
    with_open(self.to_path(true, false, "vcl"), false, |file| {
      MizReader::with(file, MaybeMut::None, false, |r, buf| {
        r.parse_vocabularies(buf, vocs)?;
        r.eof(buf)
      })
    })
  }

  pub fn read_formats(&self, ext: &str, formats: &mut Formats) -> PathResult<()> {
    with_open(self.to_path(true, false, ext), false, |file| {
      MizReader::with(file, MaybeMut::None, false, |r, buf| {
        r.read_start(buf, Some("Formats"))?;
        r.parse_formats_body(buf, &mut formats.formats, true)?;
        r.eof(buf)?;
        if !matches!(
          formats.formats.get(FormatId::STRICT),
          Some(Format::Attr(FormatAttr { args: 1, .. }))
        ) {
          return r.err("strict format")
        }
        Ok(())
      })
    })
  }

  pub fn read_dfr_uncached(
    &self, new_prel: bool, vocs: &mut Vocabularies, formats: &mut IdxVec<FormatId, Format>,
  ) -> PathResult<()> {
    with_open0(self.to_path(false, new_prel, "dfr"), |file| {
      MizReader::with(file, MaybeMut::None, false, |r, buf| {
        r.read_start(buf, Some("Formats"))?;
        r.parse_vocabularies(buf, vocs)?;
        r.parse_formats_body(buf, formats, false)?;
        r.eof(buf)
      })
    })
  }

  pub fn read_eno(&self, notas: &mut Vec<Pattern>) -> PathResult<()> {
    with_open(self.to_path(true, false, "eno"), false, |file| {
      MizReader::with(file, MaybeMut::None, false, |r, buf| {
        r.read_pi(buf)?;
        r.read_start(buf, Some("Notations"))?;
        while let Ok(e) = r.try_read_start(buf, Some("Pattern"))? {
          let attrs = r.parse_pattern_attrs(&e)?;
          notas.push(r.parse_pattern_body(buf, attrs, |x| x)?)
        }
        r.eof(buf)
      })
    })
  }

  pub fn read_dno_uncached(&self, new_prel: bool, dno: &mut DepNotation) -> PathResult<()> {
    with_open0(self.to_path(false, new_prel, "dno"), |file| {
      MizReader::with(file, MaybeMut::None, false, |r, buf| {
        r.read_start(buf, Some("Notations"))?;
        r.parse_signature(buf, &mut dno.sig)?;
        r.parse_vocabularies(buf, &mut dno.vocs)?;
        while let Ok(e) = r.try_read_start(buf, Some("Pattern"))? {
          let attrs = r.parse_pattern_attrs(&e)?;
          let Elem::Format(fmt) = r.parse_elem(buf)? else { return r.err("Format") };
          dno.pats.push(r.parse_pattern_body(buf, attrs, |_| fmt)?)
        }
        r.eof(buf)
      })
    })
  }

  pub fn read_atr(&self, constrs: &mut Constructors) -> PathResult<()> {
    with_open(self.to_path(true, false, "atr"), false, |file| {
      MizReader::with(file, constrs, false, |r, buf| {
        r.read_pi(buf)?;
        r.read_start(buf, Some("Constructors"))?;
        r.parse_constructors_body(buf, None)?;
        r.eof(buf)
      })
    })
  }

  pub fn read_aco(&self, aco: &mut AccumConstructors) -> PathResult<()> {
    with_open(self.to_path(true, false, "aco"), false, |file| {
      MizReader::with(file, MaybeMut::None, false, |r, buf| {
        r.read_pi(buf)?;
        r.read_start(buf, Some("Constructors"))?;
        r.read_start(buf, Some("SignatureWithCounts"))?;
        while let Ok(e) = r.try_read_start(buf, Some("ConstrCounts"))? {
          let Some(attr) = e.try_get_attribute(b"name")? else { return r.err("name attribute") };
          let art = r.to_article(&attr.value)?;
          let mut counts = Default::default();
          r.parse_constr_counts_body(buf, &mut counts)?;
          aco.sig.sig.push((art, std::mem::replace(&mut aco.sig.base, counts)));
        }
        r.parse_constructors_body(buf, Some(&mut aco.constrs))?;
        r.eof(buf)?;
        if aco.sig.sig.0.first().map(|p| p.0) != Some(Article::HIDDEN) {
          return r.err("HIDDEN signature")
        }
        Ok(())
      })
    })
  }

  pub fn read_dco_uncached(
    &self, new_prel: bool, dco: &mut DepConstructors, read_constrs: bool,
  ) -> PathResult<()> {
    with_open0(self.to_path(false, new_prel, "dco"), |file| {
      MizReader::with(file, MaybeMut::None, false, |r, buf| {
        r.read_start(buf, Some("Constructors"))?;
        r.parse_signature(buf, &mut dco.sig)?;
        r.read_start(buf, Some("ConstrCounts"))?;
        r.parse_constr_counts_body(buf, &mut dco.counts)?;
        if read_constrs {
          r.parse_constructors_body(buf, Some(&mut dco.constrs))?;
          r.eof(buf)?;
        }
        Ok(())
      })
    })
  }

  pub fn read_dre_uncached(&self, dre: &mut DepRequirements) -> PathResult<()> {
    with_open(self.to_path(false, false, "dre"), false, |file| {
      MizReader::with(file, MaybeMut::None, false, |r, buf| {
        r.read_start(buf, Some("Requirements"))?;
        r.parse_signature(buf, &mut dre.sig)?;
        while let Ok(e) = r.try_read_start(buf, Some("Requirement"))? {
          let Some(kind) = r.parse_constr_kind(&e)? else { return r.err("constructor kind") };
          let Some(attr) = e.try_get_attribute(b"nr")? else { return r.err("nr attribute") };
          let nr: u32 = r.get_attr(&attr.value)?;
          let req = (nr.checked_sub(1))
            .filter(|&i| (i as usize) < <Requirement as Enum>::LENGTH)
            .map(|i| Requirement::from_usize(i as _));
          let Some(req) = req else { return r.err("requirement number") };
          dre.reqs.push(DepRequirement { req, kind });
          r.end_tag(buf)?
        }
        r.eof(buf)
      })
    })
  }

  pub fn read_ecl(&self, ctx: &Constructors, clusters: &mut Clusters) -> PathResult<()> {
    with_open(self.to_path(true, false, "ecl"), false, |file| {
      MizReader::with(file, ctx, false, |r, buf| {
        r.read_pi(buf)?;
        r.read_start(buf, Some("Registrations"))?;
        while let Event::Start(e) = r.read_event(buf)? {
          match r.parse_cluster_attrs(&e)? {
            (aid, ClusterKind::R) => clusters.registered.push(r.parse_rcluster(buf, aid)?),
            (aid, ClusterKind::F) => clusters.functor.vec.0.push(r.parse_fcluster(buf, aid)?),
            (aid, ClusterKind::C) => clusters.conditional.push(ctx, r.parse_ccluster(buf, aid)?),
          }
        }
        r.eof(buf)
      })
    })
  }

  pub fn read_dcl_uncached(&self, new_prel: bool, dcl: &mut DepClusters) -> PathResult<()> {
    with_open0(self.to_path(false, new_prel, "dcl"), |file| {
      MizReader::with(file, MaybeMut::None, false, |r, buf| {
        r.read_start(buf, Some("Registrations"))?;
        r.parse_signature(buf, &mut dcl.sig)?;
        while let Event::Start(e) = r.read_event(buf)? {
          match r.parse_cluster_attrs(&e)? {
            (aid, ClusterKind::R) => dcl.cl.registered.push(r.parse_rcluster(buf, aid)?),
            (aid, ClusterKind::F) => dcl.cl.functor.push(r.parse_fcluster(buf, aid)?),
            (aid, ClusterKind::C) => dcl.cl.conditional.push(r.parse_ccluster(buf, aid)?),
          }
        }
        r.eof(buf)
      })
    })
  }

  pub fn read_definitions<'a>(
    &self, ctx: impl Into<MaybeMut<'a, Constructors>>, new_prel: bool, ext: &str,
    sig: Option<&mut Vec<Article>>, defs: &mut Vec<Definiens>,
  ) -> PathResult<()> {
    with_open0(self.to_path(sig.is_none(), new_prel, ext), |file| {
      MizReader::with(file, ctx, false, |r, buf| {
        if sig.is_none() {
          r.read_pi(buf)?;
        }
        r.read_start(buf, Some("Definientia"))?;
        if let Some(sig) = sig {
          r.parse_signature(buf, sig)?;
        }
        while let Ok(e) = r.try_read_start(buf, Some("Definiens"))? {
          let attrs = r.parse_definiens_attrs(e)?;
          defs.push(r.parse_definiens_body(buf, attrs)?)
        }
        r.eof(buf)
      })
    })
  }

  pub fn read_properties<'a>(
    &self, ctx: impl Into<MaybeMut<'a, Constructors>>, new_prel: bool, ext: &str,
    sig: Option<&mut Vec<Article>>, props: &mut Vec<Property>,
  ) -> PathResult<()> {
    with_open0(self.to_path(sig.is_none(), new_prel, ext), |file| {
      MizReader::with(file, ctx, false, |r, buf| {
        if sig.is_none() {
          r.read_pi(buf)?
        }
        r.read_start(buf, Some("PropertyRegistration"))?;
        if let Some(sig) = sig {
          r.parse_signature(buf, sig)?;
        }
        while let Ok(e) = r.try_read_start(buf, Some("Property"))? {
          let attrs = r.parse_property_attrs(&e)?;
          props.push(r.parse_property_body(buf, attrs)?)
        }
        r.eof(buf)
      })
    })
  }

  pub fn read_identify_regs<'a>(
    &self, ctx: impl Into<MaybeMut<'a, Constructors>>, new_prel: bool, ext: &str,
    sig: Option<&mut Vec<Article>>, ids: &mut Vec<IdentifyFunc>,
  ) -> PathResult<()> {
    with_open0(self.to_path(sig.is_none(), new_prel, ext), |file| {
      MizReader::with(file, ctx, false, |r, buf| {
        if sig.is_none() {
          r.read_pi(buf)?
        }
        r.read_start(buf, Some("IdentifyRegistrations"))?;
        if let Some(sig) = sig {
          r.parse_signature(buf, sig)?;
        }
        while let Ok(e) = r.try_read_start(buf, Some("Identify"))? {
          let attrs = r.parse_identify_attrs(&e)?;
          ids.push(r.parse_identify_body(buf, attrs)?);
        }
        r.eof(buf)
      })
    })
  }

  pub fn read_reduction_regs<'a>(
    &self, ctx: impl Into<MaybeMut<'a, Constructors>>, new_prel: bool, ext: &str,
    sig: Option<&mut Vec<Article>>, reds: &mut Vec<Reduction>,
  ) -> PathResult<()> {
    with_open0(self.to_path(sig.is_none(), new_prel, ext), |file| {
      MizReader::with(file, ctx, false, |r, buf| {
        if sig.is_none() {
          r.read_pi(buf)?
        }
        r.read_start(buf, Some("ReductionRegistrations"))?;
        if let Some(sig) = sig {
          r.parse_signature(buf, sig)?;
        }
        while let Ok(e) = r.try_read_start(buf, Some("Reduction"))? {
          let attrs = r.parse_reduction_attrs(&e)?;
          reds.push(r.parse_reduction_body(buf, attrs)?);
        }
        r.eof(buf)
      })
    })
  }

  pub fn read_eth(
    &self, ctx: &Constructors, refs: Option<&References>, libs: &mut Libraries,
  ) -> PathResult<()> {
    with_open0(self.to_path(true, false, "eth"), |file| {
      MizReader::with(file, ctx, false, |r, buf| {
        r.read_pi(buf)?;
        r.read_start(buf, Some("Theorems"))?;
        while let Ok(e) = r.try_read_start(buf, Some("Theorem"))? {
          let (mut lib_nr, mut thm_nr, mut kind) = Default::default();
          for attr in e.attributes() {
            let attr = attr?;
            match attr.key.0 {
              b"articlenr" => lib_nr = r.get_attr(&attr.value)?,
              b"nr" => thm_nr = r.idx_attr(&attr.value)?,
              b"kind" => kind = r.attr_byte(&attr)?,
              _ => {}
            }
          }
          match kind {
            b'T' if refs.is_none_or(|refs| refs.thm.contains(&(lib_nr, ThmId(thm_nr)))) => {
              let Some(th) = r.parse_formula(buf)? else { return r.err("formula") };
              r.end_tag(buf)?;
              libs.thm.insert((lib_nr, ThmId(thm_nr)), th);
            }
            b'D' if refs.is_none_or(|refs| refs.def.contains(&(lib_nr, DefId(thm_nr)))) => {
              let Some(th) = r.parse_formula(buf)? else { return r.err("formula") };
              r.end_tag(buf)?;
              libs.def.insert((lib_nr, DefId(thm_nr)), th);
            }
            b'T' | b'D' => r.read_to_end(b"Theorem", buf)?,
            _ => return r.err("theorem kind"),
          }
        }
        r.eof(buf)
      })
    })
  }

  pub fn read_the_uncached(&self, new_prel: bool, thms: &mut DepTheorems) -> PathResult<()> {
    with_open0(self.to_path(false, new_prel, "the"), |file| {
      MizReader::with(file, MaybeMut::None, false, |r, buf| {
        r.read_start(buf, Some("Theorems"))?;
        r.parse_signature(buf, &mut thms.sig)?;
        while let Ok(e) = r.try_read_start(buf, Some("Theorem"))? {
          let Some(attr) = e.try_get_attribute(b"kind")? else { return r.err("kind attribute") };
          let kind = r.attr_byte(&attr)?;
          let constr_kind = r.parse_constr_kind(&e)?;
          let Some(stmt) = r.parse_formula(buf)? else { return r.err("formula") };
          r.end_tag(buf)?;
          let kind = match kind {
            b'T' => match stmt {
              Formula::True => TheoremKind::CanceledThm,
              _ => TheoremKind::Thm,
            },
            b'D' => match (&stmt, constr_kind) {
              (Formula::True, None) => TheoremKind::CanceledDef,
              (_, Some(constr_kind)) => TheoremKind::Def(constr_kind),
              (_, None) => return r.err("constructor kind"),
            },
            _ => return r.err("theorem kind"),
          };
          thms.thm.push(Theorem { pos: Span::default(), kind, stmt });
        }
        r.eof(buf)
      })
    })
  }

  pub fn read_esh(
    &self, ctx: &Constructors, refs: Option<&References>, libs: &mut Libraries,
  ) -> PathResult<()> {
    with_open0(self.to_path(true, false, "esh"), |file| {
      MizReader::with(file, ctx, false, |r, buf| {
        r.read_pi(buf)?;
        r.read_start(buf, Some("Schemes"))?;
        while let Ok(e) = r.try_read_start(buf, Some("Scheme"))? {
          let (mut lib_nr, mut sch_nr) = Default::default();
          for attr in e.attributes() {
            let attr = attr?;
            match attr.key.0 {
              b"articlenr" => lib_nr = r.get_attr(&attr.value)?,
              b"nr" => sch_nr = SchId(r.idx_attr(&attr.value)?),
              _ => {}
            }
          }
          if refs.is_none_or(|refs| refs.sch.contains(&(lib_nr, sch_nr))) {
            let sch_funcs = r.parse_arg_types(buf)?;
            if let Some(thesis) = r.parse_formula(buf)? {
              let mut prems = vec![];
              while let Some(f) = r.parse_formula(buf)? {
                prems.push(f)
              }
              if lib_nr == ArticleId::SELF {
                return r.err("external article")
              }
              libs.sch.insert((lib_nr, sch_nr), Scheme { sch_funcs, prems: prems.into(), thesis });
            } // else canceled scheme
          } else {
            r.read_to_end(b"Scheme", buf)?
          }
        }
        r.eof(buf)
      })
    })
  }

  pub fn read_sch_uncached(&self, new_prel: bool, schs: &mut DepSchemes) -> PathResult<()> {
    with_open0(self.to_path(false, new_prel, "sch"), |file| {
      MizReader::with(file, MaybeMut::None, false, |r, buf| {
        r.read_start(buf, Some("Schemes"))?;
        r.parse_signature(buf, &mut schs.sig)?;
        while let Event::Start(e) = r.read_event(buf)? {
          match e.local_name().as_ref() {
            b"Canceled" => {
              r.end_tag(buf)?;
              schs.sch.push(None)
            }
            b"Scheme" => {
              let sch_funcs = r.parse_arg_types(buf)?;
              let Some(thesis) = r.parse_formula(buf)? else { return r.err("formula") };
              let mut prems = vec![];
              while let Some(f) = r.parse_formula(buf)? {
                prems.push(f)
              }
              schs.sch.push(Some(Scheme { sch_funcs, prems: prems.into(), thesis }));
            }
            _ => return r.err("Scheme"),
          }
        }
        r.eof(buf)
      })
    })
  }

  pub fn read_xml(&self, lines: Option<Arc<LineMap>>, mut f: impl FnMut(Item)) -> PathResult<()> {
    with_open0(self.to_path(true, false, "xml"), |file| {
      let (mut r, mut buf) = MizReader::new(file, MaybeMut::None, true)?;
      r.r.1 = lines;
      r.read_pi(&mut buf)?;
      r.read_start(&mut buf, Some("Article"))?;
      let mut p = ArticleParser { r, buf };
      while let Some(item) = p.parse_item()? {
        f(item)
      }
      p.r.eof(&mut p.buf)?;
      Ok(())
    })
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
  article: Article,
  abs_nr: u32,
  kind: u8,
  fmt: FormatId,
  constr: u32,
  _redefines: Option<u32>,
  pid: Option<u32>,
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
  fn parse_type_vid(&mut self, buf: &mut Vec<u8>) -> Result<Option<(Type, IdentId)>> {
    Ok(match self.parse_elem(buf)? {
      Elem::Type(ty, id) => Some((ty, id)),
      _ => None,
    })
  }
  fn parse_type(&mut self, buf: &mut Vec<u8>) -> Result<Option<Type>> {
    Ok(self.parse_type_vid(buf)?.map(|t| t.0))
  }

  /// Like [`Self::parse_type`], but the type is required to be present.
  fn parse_type_req(&mut self, buf: &mut Vec<u8>) -> Result<Type> {
    match self.parse_type(buf)? {
      Some(ty) => Ok(ty),
      None => self.err("Typ"),
    }
  }

  /// Like [`Self::parse_term`], but the term is required to be present.
  fn parse_term_req(&mut self, buf: &mut Vec<u8>) -> Result<Term> {
    match self.parse_term(buf)? {
      Some(tm) => Ok(tm),
      None => self.err("term"),
    }
  }

  /// Like [`Self::parse_formula`], but the formula is required to be present.
  fn parse_formula_req(&mut self, buf: &mut Vec<u8>) -> Result<Formula> {
    match self.parse_formula(buf)? {
      Some(f) => Ok(f),
      None => self.err("formula"),
    }
  }

  fn parse_attrs(&mut self, buf: &mut Vec<u8>) -> Result<Attrs> {
    self.read_start(buf, Some("Cluster"))?;
    let mut attrs = vec![];
    while let Ok(e) = self.try_read_start(buf, Some("Adjective"))? {
      let mut nr: u32 = 0;
      let mut pos = true;
      for attr in e.attributes() {
        let attr = attr?;
        match attr.key.0 {
          b"nr" => nr = self.get_attr(&attr.value)?,
          b"value" if &*attr.value != b"true" => pos = false,
          _ => {}
        }
      }
      let Some(nr) = nr.checked_sub(1) else { return self.err("attribute nr") };
      attrs.push(Attr { nr: AttrId(nr), pos, args: self.parse_term_list(buf)? })
    }
    let ctx = self.ctx.get();
    attrs.sort_by(|a, b| a.cmp(ctx, None, b, CmpStyle::Attr));
    Ok(Attrs::Consistent(attrs))
  }

  /// [`get_basic_attrs`](Self::get_basic_attrs) with `nr` converted from the legacy
  /// 1-based index (see [`idx_attr`](Self::idx_attr)). Used by the callers that turn
  /// it into a constructor id; the one caller that ignores `nr` uses the raw form.
  fn get_basic_idx(&mut self, e: &BytesStart<'_>) -> Result<(u8, u32)> {
    let (kind, nr) = self.get_basic_attrs(e)?;
    match nr.checked_sub(1) {
      Some(nr) => Ok((kind, nr)),
      None => Err(ParseError::BadInteger(self.0.buffer_position())),
    }
  }

  fn get_basic_attrs(&mut self, e: &BytesStart<'_>) -> Result<(u8, u32)> {
    let mut kind = 0;
    let mut nr = 0;
    for attr in e.attributes() {
      let attr = attr?;
      match attr.key.0 {
        b"kind" => kind = self.attr_byte(&attr)?,
        b"nr" => nr = self.get_attr(&attr.value)?,
        _ => {}
      }
    }
    Ok((kind, nr))
  }

  fn get_vid(&mut self, e: &BytesStart<'_>) -> Result<IdentId> {
    Ok(match e.try_get_attribute(b"vid")? {
      Some(attr) => IdentId(self.get_attr(&attr.value)?),
      None => IdentId::NONE,
    })
  }

  fn parse_signature(&mut self, buf: &mut Vec<u8>, sig: &mut Vec<Article>) -> Result<()> {
    self.read_start(buf, Some("Signature"))?;
    while let Ok(e) = self.try_read_start(buf, Some("ArticleID"))? {
      let Some(attr) = e.try_get_attribute(b"name")? else { return self.err("name attribute") };
      sig.push(self.to_article(&attr.value)?);
      self.end_tag(buf)?;
    }
    Ok(())
  }

  fn parse_vocabularies(&mut self, buf: &mut Vec<u8>, vocs: &mut Vocabularies) -> Result<()> {
    self.read_start(buf, Some("Vocabularies"))?;
    while self.try_read_start(buf, Some("Vocabulary"))?.is_ok() {
      let e = self.read_start(buf, Some("ArticleID"))?;
      let Some(attr) = e.try_get_attribute(b"name")? else { return self.err("name attribute") };
      let aid = self.to_article(&attr.value)?;
      self.end_tag(buf)?;
      let mut symbols = SymbolsBase::default();
      while let Ok(e) = self.try_read_start(buf, Some("SymbolCount"))? {
        let (mut kind, mut nr) = Default::default();
        for attr in e.attributes() {
          let attr = attr?;
          match attr.key.0 {
            b"kind" => kind = self.attr_char(&attr)?,
            b"nr" => nr = self.get_attr::<u32>(&attr.value)?,
            _ => {}
          }
        }
        self.end_tag(buf)?;
        let Some(kind) = parse_symbol_kind(kind) else { return self.err("symbol kind") };
        symbols.0[kind] += nr;
      }
      vocs.0.push((aid, symbols));
    }
    Ok(())
  }

  pub fn parse_formats_body(
    &mut self, buf: &mut Vec<u8>, formats: &mut IdxVec<FormatId, Format>, allow_priority: bool,
  ) -> Result<()> {
    let mut found_prio = false;
    loop {
      match self.parse_elem(buf)? {
        Elem::Format(fmt) => {
          if allow_priority && found_prio {
            return self.err("Priority")
          }
          formats.push(fmt);
        }
        Elem::Priority(_, _) if allow_priority => found_prio = true,
        Elem::End => break,
        _ => return self.err("Format or Priority"),
      }
    }
    Ok(())
  }

  fn parse_cluster_attrs(&mut self, e: &BytesStart<'_>) -> Result<((Article, u32), ClusterKind)> {
    let mut article = Article::default();
    let mut abs_nr = 0;
    for attr in e.attributes() {
      let attr = attr?;
      match attr.key.0 {
        b"aid" => article = self.to_article(&attr.value)?,
        b"nr" => abs_nr = self.get_attr(&attr.value)?,
        _ => {}
      }
    }
    let kind = match e.local_name().as_ref() {
      b"RCluster" => ClusterKind::R,
      b"FCluster" => ClusterKind::F,
      b"CCluster" => ClusterKind::C,
      _ => return self.err("cluster kind"),
    };
    Ok(((article, abs_nr), kind))
  }

  fn parse_rcluster(
    &mut self, buf: &mut Vec<u8>, (_article, _abs_nr): (Article, u32),
  ) -> Result<RegisteredCluster> {
    let primary = self.parse_arg_types(buf)?;
    let ty = Box::new(self.parse_type_req(buf)?);
    let attrs = self.parse_attrs(buf)?;
    let attrs2 = if self.two_clusters { self.parse_attrs(buf)? } else { attrs.clone() };
    let cl = Cluster { primary, consequent: (attrs, attrs2) };
    self.end_tag(buf)?;
    Ok(RegisteredCluster { cl, ty })
  }

  fn parse_fcluster(
    &mut self, buf: &mut Vec<u8>, (_article, _abs_nr): (Article, u32),
  ) -> Result<FunctorCluster> {
    let primary = self.parse_arg_types(buf)?;
    let term = Box::new(self.parse_term_req(buf)?);
    let attrs = self.parse_attrs(buf)?;
    let attrs2 = if self.two_clusters { self.parse_attrs(buf)? } else { attrs.clone() };
    let cl = Cluster { primary, consequent: (attrs, attrs2) };
    let ty = self.parse_type(buf)?.map(Box::new);
    if ty.is_some() {
      self.end_tag(buf)?;
    }
    Ok(FunctorCluster { cl, ty, term })
  }

  fn parse_ccluster(
    &mut self, buf: &mut Vec<u8>, (_article, _abs_nr): (Article, u32),
  ) -> Result<ConditionalCluster> {
    let primary = self.parse_arg_types(buf)?;
    let antecedent = self.parse_attrs(buf)?;
    let ty = Box::new(self.parse_type_req(buf)?);
    let attrs = self.parse_attrs(buf)?;
    let attrs2 = if self.two_clusters { self.parse_attrs(buf)? } else { attrs.clone() };
    let cl = Cluster { primary, consequent: (attrs, attrs2) };
    self.end_tag(buf)?;
    Ok(ConditionalCluster { cl, ty, antecedent })
  }

  fn parse_pairs(
    &mut self, buf: &mut Vec<u8>, name: &[u8], mut f: impl FnMut(u32, u32),
  ) -> Result<()> {
    if !matches!(self.read_event(buf)?, Event::Start(e) if e.local_name().as_ref() == name) {
      return self.err("pair list")
    }
    while let Ok(e) = self.try_read_start(buf, Some("Pair"))? {
      let (mut x, mut y) = (0, 0);
      for attr in e.attributes() {
        let attr = attr?;
        match attr.key.0 {
          b"x" => x = self.get_attr(&attr.value)?,
          b"y" => y = self.get_attr(&attr.value)?,
          _ => {}
        }
      }
      self.end_tag(buf)?;
      f(x, y)
    }
    Ok(())
  }

  fn parse_nr_attr(&mut self, e: BytesStart<'_>) -> Result<u32> {
    let Some(attr) = e.attributes().next().transpose()? else { return self.err("nr attribute") };
    if attr.key.0 != b"nr" {
      return self.err("nr attribute")
    }
    self.get_attr(&attr.value)
  }

  /// [`parse_nr_attr`](Self::parse_nr_attr) as a 1-based index: see [`idx_attr`](Self::idx_attr).
  fn parse_nr_idx(&mut self, e: BytesStart<'_>) -> Result<u32> {
    match self.parse_nr_attr(e)?.checked_sub(1) {
      Some(n) => Ok(n),
      None => Err(ParseError::BadInteger(self.0.buffer_position())),
    }
  }

  fn parse_pattern_attrs(&mut self, e: &BytesStart<'_>) -> Result<PatternAttrs> {
    let mut attrs = PatternAttrs { pos: true, ..PatternAttrs::default() };
    let mut constr_kind = 0;
    for attr in e.attributes() {
      let attr = attr?;
      match attr.key.0 {
        b"nr" => attrs.abs_nr = self.idx_attr(&attr.value)?,
        b"aid" => attrs.article = self.to_article(&attr.value)?,
        b"kind" => attrs.kind = self.attr_byte(&attr)?,
        b"formatnr" => attrs.fmt = FormatId(self.idx_attr(&attr.value)?),
        b"constrkind" => constr_kind = self.attr_byte(&attr)?,
        b"constrnr" => attrs.constr = self.get_attr(&attr.value)?,
        b"antonymic" => attrs.pos = &*attr.value != b"true",
        b"relnr" => attrs.pid = self.get_attr::<u32>(&attr.value)?.checked_sub(1),
        b"redefnr" => attrs._redefines = self.get_attr::<u32>(&attr.value)?.checked_sub(1),
        _ => {}
      }
    }
    if attrs.kind != constr_kind {
      return self.err("matching pattern kind")
    }
    Ok(attrs)
  }

  fn parse_pattern_body<F>(
    &mut self, buf: &mut Vec<u8>,
    PatternAttrs { article, abs_nr, kind, fmt, constr, pos, .. }: PatternAttrs,
    map: impl FnOnce(FormatId) -> F,
  ) -> Result<Pattern<F>> {
    let primary = self.parse_arg_types(buf)?;
    self.read_start(buf, Some("Visible"))?;
    let visible = self.parse_loci(buf)?;
    let kind = match (kind, constr.checked_sub(1)) {
      (b'M', Some(nr)) => PatternKind::Mode(ModeId(nr)),
      (b'M', None) => {
        self.read_start(buf, Some("Expansion"))?;
        let expansion = Box::new(self.parse_type_req(buf)?);
        self.end_tag(buf)?;
        PatternKind::ExpandableMode { expansion }
      }
      (b'L', Some(nr)) => PatternKind::Struct(StructId(nr)),
      (b'V', Some(nr)) => PatternKind::Attr(AttrId(nr)),
      (b'R', Some(nr)) => PatternKind::Pred(PredId(nr)),
      (b'K', Some(nr)) => PatternKind::Func(FuncId(nr)),
      (b'U', Some(nr)) => PatternKind::Sel(SelId(nr)),
      (b'G', Some(nr)) => PatternKind::Aggr(AggrId(nr)),
      (b'J', Some(nr)) => PatternKind::SubAggr(StructId(nr)),
      _ => return self.err("pattern kind"),
    };
    self.end_tag(buf)?;
    Ok(Pattern { article, abs_nr, kind, fmt: map(fmt), primary, visible, pos })
  }

  fn parse_constr_counts_body(
    &mut self, buf: &mut Vec<u8>, counts: &mut ConstructorsBase,
  ) -> Result<()> {
    while let Ok(e) = self.try_read_start(buf, Some("ConstrCount"))? {
      let (mut kind, mut nr) = Default::default();
      for attr in e.attributes() {
        let attr = attr?;
        match attr.key.0 {
          b"kind" => kind = self.attr_char(&attr)?,
          b"nr" => nr = self.get_attr::<u32>(&attr.value)?,
          _ => {}
        }
      }
      match kind {
        b'M' => counts.mode += nr,
        b'L' => counts.struct_mode += nr,
        b'V' => counts.attribute += nr,
        b'R' => counts.predicate += nr,
        b'K' => counts.functor += nr,
        b'U' => counts.selector += nr,
        b'G' => counts.aggregate += nr,
        _ => return self.err("constructor kind"),
      }
      self.end_tag(buf)?
    }
    Ok(())
  }

  fn parse_constructor_attrs(&mut self, e: &BytesStart<'_>) -> Result<ConstructorAttrs> {
    let mut attrs = ConstructorAttrs::default();
    for attr in e.attributes() {
      let attr = attr?;
      match attr.key.0 {
        b"kind" => attrs.kind = self.attr_byte(&attr)?,
        b"nr" => attrs._abs_nr = self.get_attr(&attr.value)?,
        b"aid" => attrs._article = self.to_article(&attr.value)?,
        b"redefnr" => attrs.redefines = self.get_attr(&attr.value)?,
        b"superfluous" => attrs.superfluous = self.get_attr(&attr.value)?,
        b"structmodeaggrnr" => attrs.aggr = self.get_attr(&attr.value)?,
        b"aggregbase" => attrs.base = self.get_attr(&attr.value)?,
        _ => {}
      }
    }
    Ok(attrs)
  }

  fn parse_constructor_body(
    &mut self, buf: &mut Vec<u8>,
    ConstructorAttrs { redefines, superfluous, kind, aggr, base, .. }: ConstructorAttrs,
  ) -> Result<ConstructorDef> {
    let (properties, primary) = match self.parse_elem(buf)? {
      Elem::Properties(props) => (props, self.parse_arg_types(buf)?),
      Elem::ArgTypes(args) => (Default::default(), args),
      _ => return self.err("ArgTypes"),
    };
    macro_rules! constructor {
      ($id:ident) => {{
        let redefines = redefines.checked_sub(1).map($id);
        Constructor { primary, redefines, superfluous, properties }
      }};
    }
    let kind = match kind {
      b'M' => {
        let c = constructor!(ModeId);
        ConstructorDef::Mode(TyConstructor { c, ty: self.parse_type_req(buf)? })
      }
      b'L' => {
        let c = constructor!(StructId);
        let mut parents = vec![];
        let aggr = AggrId(self.dec1(aggr)?);
        let fields = loop {
          match self.parse_elem(buf)? {
            Elem::Type(ty, _) => {
              if !matches!(ty.kind, TypeKind::Struct(_)) {
                return self.err("struct type")
              }
              parents.push(ty)
            }
            Elem::Fields(args) => break args,
            _ => return self.err("Fields"),
          }
        };
        ConstructorDef::Struct(StructMode { c, parents: parents.into(), aggr, fields })
      }
      b'V' => {
        let c = constructor!(AttrId);
        ConstructorDef::Attr(TyConstructor { c, ty: self.parse_type_req(buf)? })
      }
      b'R' => ConstructorDef::Pred(constructor!(PredId)),
      b'K' => {
        let c = constructor!(FuncId);
        ConstructorDef::Func(TyConstructor { c, ty: self.parse_type_req(buf)? })
      }
      b'U' => {
        let c = constructor!(SelId);
        ConstructorDef::Sel(TyConstructor { c, ty: self.parse_type_req(buf)? })
      }
      b'G' | b'J' => {
        let c = constructor!(AggrId);
        ConstructorDef::Aggr(Aggregate {
          c: TyConstructor { c, ty: self.parse_type_req(buf)? },
          base,
          fields: match self.parse_elem(buf)? {
            Elem::Fields(args) => args,
            _ => return self.err("Fields"),
          },
        })
      }
      _ => return self.err("constructor kind"),
    };
    self.end_tag(buf)?;
    Ok(kind)
  }

  fn parse_constr_kind(&mut self, e: &BytesStart<'_>) -> Result<Option<ConstrKind>> {
    let (mut constr_nr, mut constr_kind) = Default::default();
    for attr in e.attributes() {
      let attr = attr?;
      match attr.key.0 {
        b"constrkind" => constr_kind = self.attr_byte(&attr)?,
        b"constrnr" => constr_nr = self.idx_attr(&attr.value)?,
        _ => {}
      }
    }
    Ok(match constr_kind {
      0 => None,
      b'R' => Some(ConstrKind::Pred(PredId(constr_nr))),
      b'V' => Some(ConstrKind::Attr(AttrId(constr_nr))),
      b'K' => Some(ConstrKind::Func(FuncId(constr_nr))),
      b'M' => Some(ConstrKind::Mode(ModeId(constr_nr))),
      _ => return self.err("constructor kind"),
    })
  }

  fn parse_constructors_body(
    &mut self, buf: &mut Vec<u8>, mut constrs: Option<&mut Constructors>,
  ) -> Result<()> {
    while let Ok(e) = self.try_read_start(buf, Some("Constructor"))? {
      let attrs = self.parse_constructor_attrs(&e)?;
      let constr = self.parse_constructor_body(buf, attrs)?;
      if let Some(constrs) = &mut constrs {
        constrs.push(constr);
      } else {
        let MaybeMut::Mut(constrs) = &mut self.ctx else { unreachable!() };
        constrs.push(constr);
      }
    }
    Ok(())
  }

  fn parse_definiens_attrs(&mut self, e: BytesStart<'_>) -> Result<(DefId, Article, ConstrKind)> {
    let (mut article, mut def_nr) = Default::default();
    for attr in e.attributes() {
      let attr = attr?;
      match attr.key.0 {
        b"aid" => article = self.to_article(&attr.value)?,
        b"defnr" => def_nr = DefId(self.idx_attr(&attr.value)?),
        _ => {}
      }
    }
    let Some(kind) = self.parse_constr_kind(&e)? else { return self.err("constructor kind") };
    Ok((def_nr, article, kind))
  }

  fn parse_definiens_body(
    &mut self, buf: &mut Vec<u8>, (def_nr, article, constr): (DefId, Article, ConstrKind),
  ) -> Result<Definiens> {
    let mut primary = vec![];
    let essential = loop {
      match self.parse_elem(buf)? {
        Elem::Type(ty, _) => primary.push(ty),
        Elem::Essentials(args) => break args,
        _ => return self.err("Essentials"),
      }
    };
    let (assumptions, value) = match self.parse_elem(buf)? {
      Elem::Formula(f) => match self.parse_elem(buf)? {
        Elem::DefMeaning(df) => (f, df),
        _ => return self.err("DefMeaning"),
      },
      Elem::DefMeaning(df) => (Formula::True, df),
      _ => return self.err("DefMeaning"),
    };
    self.end_tag(buf)?;
    let c = ConstrDef { def_nr, article, constr, primary: primary.into() };
    Ok(Definiens { c, essential, assumptions, value })
  }

  fn parse_identify_attrs(&mut self, e: &BytesStart<'_>) -> Result<IdentifyAttrs> {
    let mut attrs = IdentifyAttrs::default();
    for attr in e.attributes() {
      let attr = attr?;
      match attr.key.0 {
        b"aid" => attrs._article = self.to_article(&attr.value)?,
        b"nr" => attrs._abs_nr = self.get_attr(&attr.value)?,
        b"constrkind" => attrs.kind = self.attr_byte(&attr)?,
        _ => {}
      }
    }
    Ok(attrs)
  }

  fn parse_identify_body(
    &mut self, buf: &mut Vec<u8>, IdentifyAttrs { kind, .. }: IdentifyAttrs,
  ) -> Result<IdentifyFunc> {
    let mut primary = vec![];
    let lhs = loop {
      match self.parse_elem(buf)? {
        Elem::Type(ty, _) => primary.push(ty),
        Elem::Term(lhs) if kind == b'K' => break lhs,
        _ => return self.err("Term"),
      }
    };
    let rhs = self.parse_term_req(buf)?;
    let mut eq_args = vec![];
    // `x`/`y` are 1-based loci; on a corrupt file a `0` (or a value past `u8`) would
    // underflow/truncate. The closure cannot borrow `self` to report, so flag it and
    // report after the pair list is consumed.
    let mut bad = false;
    self.parse_pairs(buf, b"EqArgs", |x, y| match (x.checked_sub(1), y.checked_sub(1)) {
      (Some(x), Some(y)) if x <= u8::MAX as u32 && y <= u8::MAX as u32 =>
        eq_args.push((LocusId(x as u8), LocusId(y as u8))),
      _ => bad = true,
    })?;
    if bad {
      return self.err("EqArgs locus index")
    }
    self.end_tag(buf)?;
    Ok(IdentifyFunc { primary: primary.into(), lhs, rhs, eq_args: eq_args.into() })
  }

  fn parse_reduction_attrs(&mut self, e: &BytesStart<'_>) -> Result<ReductionAttrs> {
    let mut attrs = ReductionAttrs::default();
    for attr in e.attributes() {
      let attr = attr?;
      match attr.key.0 {
        b"aid" => attrs._article = self.to_article(&attr.value)?,
        b"nr" => attrs._abs_nr = self.get_attr(&attr.value)?,
        _ => {}
      }
    }
    Ok(attrs)
  }

  fn parse_reduction_body(
    &mut self, buf: &mut Vec<u8>, ReductionAttrs { .. }: ReductionAttrs,
  ) -> Result<Reduction> {
    let mut primary = vec![];
    let terms = loop {
      match self.parse_elem(buf)? {
        Elem::Type(ty, _) => primary.push(ty),
        Elem::Term(t1) => break [t1, self.parse_term_req(buf)?],
        _ => return self.err("Term"),
      }
    };
    self.end_tag(buf)?;
    Ok(Reduction { primary: primary.into(), terms })
  }

  fn parse_property_attrs(&mut self, e: &BytesStart<'_>) -> Result<PropertyAttrs> {
    let (mut _abs_nr, mut _article, mut kind) = Default::default();
    for attr in e.attributes() {
      let attr = attr?;
      match attr.key.0 {
        b"aid" => _article = self.to_article(&attr.value)?,
        b"nr" => _abs_nr = self.get_attr(&attr.value)?,
        b"x" => kind = self.get_attr::<usize>(&attr.value)?,
        _ => {}
      }
    }
    let kind = kind.checked_sub(1).filter(|&i| i < <PropertyKind as Enum>::LENGTH);
    let Some(kind) = kind else { return self.err("property kind") };
    Ok(PropertyAttrs { _article, _abs_nr, kind: PropertyKind::from_usize(kind) })
  }

  fn parse_property_body(
    &mut self, buf: &mut Vec<u8>, PropertyAttrs { kind, .. }: PropertyAttrs,
  ) -> Result<Property> {
    let primary = self.parse_arg_types(buf)?;
    let ty = self.parse_type_req(buf)?;
    self.end_tag(buf)?;
    Ok(Property { primary, ty, kind })
  }

  fn lower(&self) -> impl VisitMut + '_ {
    OnVarMut(|nr| {
      if *nr >= self.depth {
        assert!(*nr != self.depth || self.suppress_bvar_errors);
        *nr = nr.saturating_sub(1)
      }
    })
  }

  fn parse_elem(&mut self, buf: &mut Vec<u8>) -> Result<Elem> {
    Ok(if let Event::Start(e) = self.read_event(buf)? {
      macro_rules! parse_var {
        () => {{
          let nr = self.parse_nr_attr(e)?;
          self.end_tag(buf)?;
          // These variable references are 1-based in the file; report rather than
          // underflow-panic on a corrupt `0`.
          self.dec1(nr)?
        }};
      }
      match e.local_name().as_ref() {
        b"Typ" => {
          let (kind, nr) = self.get_basic_idx(&e)?;
          let kind = match kind {
            b'G' => TypeKind::Struct(StructId(nr)),
            b'M' => TypeKind::Mode(ModeId(nr)),
            _ => return self.err("type kind"),
          };
          let id = self.get_vid(&e)?;
          let lower = self.parse_attrs(buf)?;
          let upper = if self.two_clusters { self.parse_attrs(buf)? } else { lower.clone() };
          let mut args = vec![];
          while let Some(tm) = self.parse_term(buf)? {
            args.push(tm)
          }
          Elem::Type(Type { kind, attrs: (lower, upper), args }, id)
        }
        b"Properties" => {
          let mut props = Properties::EMPTY;
          for attr in e.attributes() {
            let attr = attr?;
            match attr.key.0 {
              b"propertyarg1" => props.arg1 = self.get_attr::<u8>(&attr.value)?.saturating_sub(1),
              b"propertyarg2" => props.arg2 = self.get_attr::<u8>(&attr.value)?.saturating_sub(1),
              _ => {}
            }
          }
          while let Event::Start(e) = self.read_event(buf)? {
            let Ok(prop) = e.local_name().as_ref().try_into() else { return self.err("property") };
            props.set(prop);
            self.end_tag(buf)?;
          }
          props.trim();
          Elem::Properties(props)
        }
        b"ArgTypes" => {
          let mut primaries = vec![];
          while let Some(ty) = self.parse_type(buf)? {
            primaries.push(ty)
          }
          Elem::ArgTypes(primaries.into())
        }
        b"Fields" => {
          let mut fields = vec![];
          while let Ok(e) = self.try_read_start(buf, Some("Field"))? {
            let Some(attr) = e.attributes().next().transpose()? else {
              return self.err("nr attribute")
            };
            if attr.key.0 != b"nr" {
              return self.err("nr attribute")
            }
            fields.push(SelId(self.idx_attr(&attr.value)?));
            self.end_tag(buf)?;
          }
          Elem::Fields(fields.into())
        }
        b"LocusVar" => Elem::Term(Term::Locus(LocusId(parse_var!() as u8))),
        b"Var" => Elem::Term(Term::Bound(BoundId(parse_var!()))),
        b"Const" => Elem::Term(Term::Const(ConstId(parse_var!()))),
        // b"InfConst" => Elem::Term(Term::Infer { nr: InferId(parse_var!()) }),
        // b"FreeVar" => Elem::Term(Term::FreeVar { nr: parse_var!() }),
        b"Num" => Elem::Term(Term::Numeral(parse_var!())),
        b"Func" => {
          let (kind, nr) = self.get_basic_idx(&e)?;
          let args = self.parse_term_list(buf)?;
          match kind {
            b'F' => Elem::Term(Term::SchFunc { nr: SchFuncId(nr), args }),
            b'G' => Elem::Term(Term::Aggregate { nr: AggrId(nr), args }),
            b'K' => Elem::Term(Term::Functor { nr: FuncId(nr), args }),
            b'U' => Elem::Term(Term::Selector { nr: SelId(nr), args }),
            _ => return self.err("function kind"),
          }
        }
        b"PrivFunc" => {
          let nr = self.parse_nr_idx(e)?;
          let value = Box::new(self.parse_term_req(buf)?);
          let args = self.parse_term_list(buf)?;
          Elem::Term(Term::PrivFunc { nr: PrivFuncId(nr), args, value })
        }
        b"Fraenkel" => {
          let mut args = vec![];
          let scope = loop {
            match self.parse_elem(buf)? {
              Elem::Type(mut ty, id) => {
                ty.visit(&mut self.lower());
                args.push((id, ty));
                self.depth += 1;
              }
              Elem::Term(scope) => break Box::new(scope),
              _ => return self.err("scope term"),
            }
          };
          let compr = Box::new(self.parse_formula_req(buf)?);
          self.depth -= args.len() as u32;
          self.end_tag(buf)?;
          Elem::Term(Term::Fraenkel { args: args.into_boxed_slice(), scope, compr })
        }
        b"Choice" => {
          let ty = Box::new(self.parse_type_req(buf)?);
          self.end_tag(buf)?;
          Elem::Term(Term::The { ty })
        }
        b"Not" => {
          let f = Box::new(self.parse_formula_req(buf)?);
          self.end_tag(buf)?;
          Elem::Formula(Formula::Neg { f })
        }
        b"And" => {
          let mut args = vec![];
          while let Some(f) = self.parse_formula(buf)? {
            args.push(f)
          }
          Elem::Formula(Formula::And { args })
        }
        b"Pred" => {
          let (kind, nr) = self.get_basic_idx(&e)?;
          let args = self.parse_term_list(buf)?;
          Elem::Formula(match kind {
            b'P' => Formula::SchPred { nr: SchPredId(nr), args },
            b'R' => Formula::Pred { nr: PredId(nr), args },
            b'V' => Formula::Attr { nr: AttrId(nr), args },
            _ => return self.err("predicate kind"),
          })
        }
        b"PrivPred" => {
          let nr = self.parse_nr_idx(e)?;
          let mut args = vec![];
          let value = loop {
            match self.parse_elem(buf)? {
              Elem::Term(tm) => args.push(tm),
              Elem::Formula(f) => break Box::new(f),
              _ => return self.err("formula"),
            }
          };
          self.end_tag(buf)?;
          Elem::Formula(Formula::PrivPred { nr: PrivPredId(nr), args: args.into(), value })
        }
        b"For" => {
          let id = match e.try_get_attribute(b"vid")? {
            Some(attr) => IdentId(self.get_attr(&attr.value)?),
            None => IdentId::NONE,
          };
          let mut dom = Box::new(self.parse_type_req(buf)?);
          dom.visit(&mut self.lower());
          self.depth += 1;
          let scope = Box::new(self.parse_formula_req(buf)?);
          self.depth -= 1;
          self.end_tag(buf)?;
          Elem::Formula(Formula::ForAll { id, dom, scope })
        }
        b"Is" => {
          let term = Box::new(self.parse_term_req(buf)?);
          let ty = Box::new(self.parse_type_req(buf)?);
          self.end_tag(buf)?;
          Elem::Formula(Formula::Is { term, ty })
        }
        b"FlexFrm" => {
          let _orig1 = self.parse_formula_req(buf)?;
          let _orig2 = self.parse_formula_req(buf)?;
          let terms = Box::new([self.parse_term_req(buf)?, self.parse_term_req(buf)?]);
          let Formula::ForAll { id: _, dom, scope } = self.parse_formula_req(buf)? else {
            return self.err("For")
          };
          let sc2 = scope.mk_neg();
          let &[Formula::Pred { nr: le, .. }, _, ref rest @ ..] = sc2.conjuncts() else {
            return self.err("flex conjunction")
          };
          let scope = Formula::mk_and(rest.to_owned());
          self.end_tag(buf)?;
          Elem::Formula(Formula::FlexAnd { nat: dom, le, terms, scope: Box::new(scope.mk_neg()) })
        }
        b"Verum" => {
          self.end_tag(buf)?;
          Elem::Formula(Formula::True)
        }
        b"Essentials" => Elem::Essentials(self.parse_loci(buf)?),
        b"DefMeaning" => match self.get_basic_attrs(&e)?.0 {
          b'm' => {
            let f = |e| if let Elem::Formula(f) = e { Some(f) } else { None };
            Elem::DefMeaning(DefValue::Formula(self.parse_def_body(buf, f)?))
          }
          b'e' => {
            let f = |e| if let Elem::Term(f) = e { Some(f) } else { None };
            Elem::DefMeaning(DefValue::Term(self.parse_def_body(buf, f)?))
          }
          _ => return self.err("definiens kind"),
        },
        b"PartialDef" => {
          let case = self.parse_elem(buf)?;
          let guard = self.parse_formula_req(buf)?;
          self.end_tag(buf)?;
          Elem::PartialDef(Box::new((case, guard)))
        }
        b"Ident" => {
          let vid = match e.try_get_attribute(b"vid")? {
            Some(attr) => self.get_attr(&attr.value)?,
            None => 0,
          };
          self.end_tag(buf)?;
          Elem::Ident(vid)
        }
        b"Proposition" => {
          let (pos, label) = self.get_pos_and_label(&e)?;
          let f = self.parse_formula_req(buf)?;
          self.end_tag(buf)?;
          Elem::Proposition(Proposition { pos, label, f })
        }
        b"Thesis" => {
          let f = self.parse_formula_req(buf)?;
          let mut exps = vec![];
          self.parse_pairs(buf, b"ThesisExpansions", |x, y| exps.push((x, y)))?;
          self.end_tag(buf)?;
          Elem::Thesis(Thesis { f, exps })
        }
        b"Format" => {
          let (mut kind, mut sym, mut args, mut left, mut rsym) = Default::default();
          for attr in e.attributes() {
            let attr = attr?;
            match attr.key.0 {
              b"kind" => kind = self.attr_char(&attr)?,
              b"symbolnr" => sym = self.idx_attr(&attr.value)?,
              b"argnr" => args = Some(self.get_attr(&attr.value)?),
              b"leftargnr" => left = Some(self.get_attr(&attr.value)?),
              b"rightsymbolnr" => rsym = Some(self.idx_attr(&attr.value)?),
              _ => {}
            }
          }
          let Some(args) = args else { return self.err("argnr attribute") };
          let fmt = match kind {
            b'G' => Format::Aggr(FormatAggr { sym: StructSymId(sym), args }),
            b'J' => Format::SubAggr(StructSymId(sym)),
            b'L' => Format::Struct(FormatStruct { sym: StructSymId(sym), args }),
            b'M' => Format::Mode(FormatMode { sym: ModeSymId(sym), args }),
            b'U' => Format::Sel(SelSymId(sym)),
            b'V' => Format::Attr(FormatAttr { sym: AttrSymId(sym), args }),
            b'O' => {
              let Some(left) = left else { return self.err("leftargnr attribute") };
              let Some(right) = args.checked_sub(left) else {
                return self.err("functor format arity")
              };
              Format::Func(FormatFunc::Func { sym: FuncSymId(sym), left, right })
            }
            b'R' => {
              let Some(left) = left else { return self.err("leftargnr attribute") };
              let Some(right) = args.checked_sub(left) else {
                return self.err("predicate format arity")
              };
              Format::Pred(FormatPred { sym: PredSymId(sym), left, right })
            }
            b'K' => {
              let Some(rsym) = rsym else { return self.err("rightsymbolnr attribute") };
              Format::Func(FormatFunc::Bracket {
                lsym: LeftBrkSymId(sym),
                rsym: RightBrkSymId(rsym),
                args,
              })
            }
            _ => return self.err("format kind"),
          };
          self.end_tag(buf)?;
          Elem::Format(fmt)
        }
        b"Priority" => {
          let (mut kind, mut sym, mut value) = Default::default();
          for attr in e.attributes() {
            let attr = attr?;
            match attr.key.0 {
              b"kind" => kind = self.attr_byte(&attr)?,
              b"symbolnr" => sym = self.idx_attr(&attr.value)?,
              b"value" => value = Some(self.get_attr(&attr.value)?),
              _ => {}
            }
          }
          let kind = match kind {
            b'O' => PriorityKind::Functor(FuncSymId(sym)),
            b'K' => PriorityKind::LeftBrk(LeftBrkSymId(sym)),
            b'L' => PriorityKind::RightBrk(RightBrkSymId(sym)),
            _ => return self.err("priority kind"),
          };
          self.end_tag(buf)?;
          let Some(value) = value else { return self.err("value attribute") };
          Elem::Priority(kind, value)
        }
        _ => Elem::Other,
      }
    } else {
      Elem::End
    })
  }

  fn parse_term(&mut self, buf: &mut Vec<u8>) -> Result<Option<Term>> {
    Ok(match self.parse_elem(buf)? {
      Elem::Term(tm) => Some(tm),
      _ => None,
    })
  }

  fn parse_term_list(&mut self, buf: &mut Vec<u8>) -> Result<Box<[Term]>> {
    let mut args = vec![];
    while let Some(tm) = self.parse_term(buf)? {
      args.push(tm)
    }
    Ok(args.into())
  }

  fn parse_formula(&mut self, buf: &mut Vec<u8>) -> Result<Option<Formula>> {
    Ok(match self.parse_elem(buf)? {
      Elem::Formula(f) => Some(f),
      _ => None,
    })
  }

  fn parse_proposition(
    &mut self, buf: &mut Vec<u8>, quotable: bool,
  ) -> Result<Option<Proposition>> {
    Ok(match self.parse_elem(buf)? {
      Elem::Proposition(f) => {
        if !quotable && f.label.is_some() {
          return self.err("unlabeled proposition")
        }
        Some(f)
      }
      _ => None,
    })
  }

  fn parse_arg_types(&mut self, buf: &mut Vec<u8>) -> Result<Box<[Type]>> {
    Ok(match self.parse_elem(buf)? {
      Elem::ArgTypes(tys) => tys,
      _ => return self.err("ArgTypes"),
    })
  }

  fn parse_def_body<T>(
    &mut self, buf: &mut Vec<u8>, get: impl Fn(Elem) -> Option<T>,
  ) -> Result<DefBody<T>> {
    let mut cases = vec![];
    let otherwise = loop {
      match self.parse_elem(buf)? {
        Elem::PartialDef(e) => {
          let Some(case) = get(e.0) else { return self.err("definiens case") };
          cases.push(DefCase { case, guard: e.1 })
        }
        Elem::End => break None,
        e => {
          self.end_tag(buf)?;
          let Some(e) = get(e) else { return self.err("definiens case") };
          break Some(e)
        }
      }
    };
    Ok(DefBody { cases: cases.into(), otherwise })
  }
}

#[derive(Debug)]
enum Elem {
  Type(Type, IdentId),
  Term(Term),
  Formula(Formula),
  Properties(Properties),
  ArgTypes(Box<[Type]>),
  Fields(Box<[SelId]>),
  Essentials(Box<[LocusId]>),
  DefMeaning(DefValue),
  PartialDef(Box<(Elem, Formula)>),
  Ident(u32),
  Proposition(Proposition),
  Thesis(Thesis),
  Format(Format),
  #[allow(dead_code)]
  Priority(PriorityKind, u32),
  Other,
  End,
}

impl TryFrom<Elem> for Type {
  type Error = ();
  fn try_from(e: Elem) -> StdResult<Type, Self::Error> {
    match e {
      Elem::Type(v, _) => Ok(v),
      _ => Err(()),
    }
  }
}
impl TryFrom<Elem> for Term {
  type Error = ();
  fn try_from(e: Elem) -> StdResult<Term, ()> {
    match e {
      Elem::Term(v) => Ok(v),
      _ => Err(()),
    }
  }
}
impl TryFrom<Elem> for Formula {
  type Error = ();
  fn try_from(e: Elem) -> StdResult<Formula, ()> {
    match e {
      Elem::Formula(v) => Ok(v),
      _ => Err(()),
    }
  }
}
