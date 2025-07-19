use crate::ast::*;
use crate::parser::{JsonParser, MizParser};
use crate::types::{
  Article, ArticleId, Directives, Format, FormatId, FuncSymId, IdxVec, Position, PredSymId,
  PriorityKind, SymbolKind, Symbols,
};
use crate::write::OWriteJson;
use std::collections::HashMap;

pub enum Parser<'a> {
  Miz(MizParser<'a>),
  Json(JsonParser),
}

pub struct ParserCore {
  pub art: Article,
  pub articles: HashMap<Article, ArticleId>,
  pub formats: Box<IdxVec<FormatId, Format>>,
  pub func_prio: HashMap<FuncSymId, u32>,
  #[allow(clippy::box_collection)]
  pub format_lookup: Box<HashMap<Format, FormatId>>,
  pub write_json: OWriteJson,
}

impl ParserCore {
  pub fn new(art: Article, write_json: OWriteJson) -> Self {
    Self {
      art,
      articles: Default::default(),
      formats: Default::default(),
      func_prio: Default::default(),
      format_lookup: Default::default(),
      write_json,
    }
  }

  pub fn load_prio(&mut self, prio: &[(PriorityKind, u32)]) {
    for &(kind, value) in prio {
      if let PriorityKind::Functor(sym) = kind {
        self.func_prio.insert(sym, value);
      }
    }
  }

  pub fn on_symbols(
    syms: &Symbols, infinitives: &[(PredSymId, &str)], mut f: impl FnMut(SymbolKind, &str),
  ) {
    syms.iter().for_each(|(kind, s)| f(*kind, s));
    infinitives.iter().for_each(|&(n, s)| f(SymbolKind::Pred(n), s))
  }

  pub fn push_format(&mut self, _pos: Position, fmt: Format) -> bool {
    if let std::collections::hash_map::Entry::Vacant(e) = self.format_lookup.entry(fmt) {
      e.insert(self.formats.push(fmt));
      return true
    }
    false
  }

  pub fn after_definition(&mut self, pos: Position, redef: bool, fmt: Format) -> bool {
    if redef {
      assert!(self.format_lookup.contains_key(&fmt), "{:?}: unknown format for redeclaration", pos);
      false
    } else {
      self.push_format(pos, fmt)
    }
  }

  pub fn after_def_struct(
    pos: Position, def: &DefStruct, mut push_format: impl FnMut(Position, Format),
  ) {
    let num_fields = def.fields.iter().map(|f| f.vars.len()).sum();
    push_format(pos, Format::SubAggr(def.pat.to_subaggr_format()));
    push_format(pos, Format::Struct(def.pat.to_mode_format()));
    for group in &def.fields {
      for f in &group.vars {
        push_format(f.pos, Format::Sel(f.sym));
      }
    }
    push_format(pos, Format::Aggr(def.pat.to_aggr_format(num_fields)));
  }
}

impl<'a> Parser<'a> {
  pub fn core_mut(&mut self) -> &mut ParserCore {
    match self {
      Parser::Miz(p) => &mut p.core,
      Parser::Json(p) => &mut p.core,
    }
  }

  pub fn push_parse_item(&mut self, buf: &mut Vec<Item>) -> bool {
    match self {
      Parser::Miz(p) => p.push_parse_item(buf),
      Parser::Json(p) => p.push_parse_item(buf),
    }
  }

  pub fn load_symbols(
    &mut self, syms: &Symbols, infinitives: &[(PredSymId, &str)], prio: &[(PriorityKind, u32)],
  ) {
    match self {
      Parser::Miz(p) => p.load_symbols(syms, infinitives, prio),
      Parser::Json(p) => p.load_symbols(syms, infinitives, prio),
    }
  }

  pub fn parse_env(&mut self, dirs: &mut Directives) {
    match self {
      Parser::Miz(p) => p.parse_env(dirs),
      Parser::Json(p) => p.parse_env(dirs),
    }
  }

  pub fn read_formats(&mut self, fmts: &[Format]) {
    match self {
      Parser::Miz(p) => fmts.iter().for_each(|fmt| p.read_format(fmt)),
      Parser::Json(_) => {}
    }
  }
}
