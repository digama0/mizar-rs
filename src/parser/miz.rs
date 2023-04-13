use crate::ast::*;
use crate::types::{
  Article, ArticleId, BlockKind, CorrCondKind, DefId, DirectiveKind, Directives, Format, FormatId,
  Idx, IdxVec, LeftBrkSymId, LocusId, ModeSymId, Position, PredSymId, PropertyKind, RightBrkSymId,
  SchId, StructSymId, SymbolKind, Symbols, ThmId, MAX_ARTICLE_LEN,
};
use enum_map::Enum;
use radix_trie::{Trie, TrieCommon};
use std::collections::HashMap;

macro_rules! mk_keywords {
  ($($id:ident: $lit:expr,)*) => {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Keyword { $($id),* }
    const KEYWORDS: &[(&[u8], Keyword)] = &[
      $(($lit, Keyword::$id),)*
      (b"being", Keyword::Be),
      (b"does", Keyword::Do),
    ];
  }
}

mk_keywords! {
  AggrLeftBrk: b"(#",
  AggrRightBrk: b"#)",
  Amp: b"&",
  Comma: b",",
  Arrow: b"->",
  Ellipsis: b"...",
  DotEquals: b".=",
  Colon: b":",
  Semicolon: b";",
  // According: b"according",
  // Aggregate: b"aggregate",
  All: b"all",
  And: b"and",
  Antonym: b"antonym",
  Are: b"are",
  As: b"as",
  Assume: b"assume",
  Attr: b"attr",
  Be: b"be",
  Begin: b"begin",
  By: b"by",
  Case: b"case",
  Cases: b"cases",
  Cluster: b"cluster",
  Consider: b"consider",
  Contradiction: b"contradiction",
  Correctness: b"correctness",
  Def: b"def",
  DefFunc: b"deffunc",
  // Define: b"define",
  Definition: b"definition",
  DefPred: b"defpred",
  Do: b"do",
  End: b"end",
  Environ: b"environ",
  Equals: b"equals",
  Ex: b"ex",
  // Exactly: b"exactly",
  For: b"for",
  From: b"from",
  Func: b"func",
  Given: b"given",
  Hence: b"hence",
  Hereby: b"hereby",
  Holds: b"holds",
  Identify: b"identify",
  If: b"if",
  Iff: b"iff",
  Implies: b"implies",
  Is: b"is",
  It: b"it",
  Let: b"let",
  Means: b"means",
  Mode: b"mode",
  Non: b"non",
  Not: b"not",
  Notation: b"notation",
  Now: b"now",
  Of: b"of",
  Or: b"or",
  Otherwise: b"otherwise",
  Over: b"over",
  Per: b"per",
  Pred: b"pred",
  // Prefix: b"prefix",
  Proof: b"proof",
  Provided: b"provided",
  Qua: b"qua",
  Reconsider: b"reconsider",
  Redefine: b"redefine",
  Reduce: b"reduce",
  Registration: b"registration",
  Reserve: b"reserve",
  Sch: b"sch",
  Scheme: b"scheme",
  // Section: b"section",
  // Selector: b"selector",
  St: b"st",
  Struct: b"struct",
  Such: b"such",
  Suppose: b"suppose",
  Synonym: b"synonym",
  Take: b"take",
  That: b"that",
  The: b"the",
  Then: b"then",
  Theorem: b"theorem",
  Thesis: b"thesis",
  Thus: b"thus",
  To: b"to",
  // Wrt: b"wrt",
  Where: b"where",
  When: b"when",
  With: b"with",
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TokenKind {
  Pragma,
  Dollar(u32),
  Number(u32),
  Ident,
  Symbol(SymbolKind),
  Keyword(Keyword),
  Property(PropertyKind),
  CorrCond(CorrCondKind),
  Directive(DirectiveKind),
  Error,
  Eof,
}

impl From<Keyword> for TokenKind {
  fn from(v: Keyword) -> Self { Self::Keyword(v) }
}

impl TokenKind {
  const SET: Self = Self::Symbol(SymbolKind::Mode(ModeSymId::SET)); // set
  const EQUAL: Self = Self::Symbol(SymbolKind::Pred(PredSymId::EQUAL)); // =
  const LBRACK: Self = Self::Symbol(SymbolKind::LeftBrk(LeftBrkSymId::LBRACK)); // [
  const RBRACK: Self = Self::Symbol(SymbolKind::RightBrk(RightBrkSymId::RBRACK)); // ]
  const LBRACE: Self = Self::Symbol(SymbolKind::LeftBrk(LeftBrkSymId::LBRACE)); // {
  const RBRACE: Self = Self::Symbol(SymbolKind::RightBrk(RightBrkSymId::RBRACE)); // }
  const LPAREN: Self = Self::Symbol(SymbolKind::LeftBrk(LeftBrkSymId::LPAREN)); // (
  const RPAREN: Self = Self::Symbol(SymbolKind::RightBrk(RightBrkSymId::RPAREN)); // )
}

#[derive(Clone, Copy, Debug)]
struct Token<'a> {
  spelling: &'a str,
  pos: Position,
  kind: TokenKind,
}

impl<'a> Token<'a> {
  fn end(&self) -> Position {
    Position { line: self.pos.line, col: self.pos.col + self.spelling.len() as u32 }
  }
}

pub struct Scanner<'a> {
  data: &'a [u8],
  line: u32,
  line_start: usize,
  pos: usize,
  allow_underscore: bool,
  phrase_end: Option<usize>,
  tokens: Trie<Vec<u8>, TokenKind>,
  lookahead: Option<Token<'a>>,
  lookahead2: Option<Token<'a>>,
}

impl<'a> Scanner<'a> {
  fn new(data: &'a [u8]) -> Self {
    let mut tokens = Trie::default();
    let mut push1 = |cc: &[u8], kind| assert!(tokens.insert(cc.to_owned(), kind).is_none());
    push1(b"$", TokenKind::Dollar(0));
    for &(s, kind) in KEYWORDS {
      push1(s, TokenKind::Keyword(kind))
    }
    for prop in (0..PropertyKind::LENGTH).map(PropertyKind::from_usize) {
      push1(prop.to_lower(), TokenKind::Property(prop))
    }
    for cc in (0..CorrCondKind::LENGTH).map(CorrCondKind::from_usize) {
      push1(cc.name(), TokenKind::CorrCond(cc))
    }
    for dir in (0..DirectiveKind::LENGTH).map(DirectiveKind::from_usize) {
      push1(dir.name().as_bytes(), TokenKind::Directive(dir))
    }
    Self {
      data,
      line: 1,
      line_start: 0,
      pos: 0,
      phrase_end: None,
      allow_underscore: true,
      tokens,
      lookahead: None,
      lookahead2: None,
    }
  }

  pub fn load_symbols(&mut self, syms: &Symbols, infinitives: &[(PredSymId, &'a str)]) {
    for (kind, s) in syms {
      assert!(self.tokens.insert(s.as_bytes().to_owned(), TokenKind::Symbol(*kind)).is_none())
    }
    for &(n, s) in infinitives {
      assert!(self
        .tokens
        .insert(s.as_bytes().to_owned(), TokenKind::Symbol(SymbolKind::Pred(n)))
        .is_none())
    }
  }

  fn pos(&self) -> Position {
    Position { line: self.line, col: (self.pos - self.line_start) as u32 + 1 }
  }

  fn undo(&mut self, tok: Token<'a>) {
    // vprintln!("undo <- {tok:?}, {:?}, {:?}", self.lookahead, self.lookahead2);
    assert!(self.lookahead2.is_none());
    self.lookahead2 = self.lookahead.take();
    self.lookahead = Some(tok)
  }

  fn peek(&mut self) -> &Token<'a> {
    // Safety: this is NLL problem case 3
    match unsafe { &*(&self.lookahead as *const _) } {
      Some(tok) => tok,
      None => {
        let tok = self.next();
        self.lookahead.insert(tok)
      }
    }
  }

  fn next(&mut self) -> Token<'a> {
    if let Some(tok) = self.lookahead.take() {
      self.lookahead = self.lookahead2.take();
      return tok
    }
    'slice_phrase: loop {
      if let Some(end) = self.phrase_end {
        let ident_end = (self.data[self.pos..end].iter())
          .position(|&c| !(c.is_ascii_alphanumeric() || (self.allow_underscore && c == b'_')))
          .map_or(end, |len| self.pos + len);
        let pos = self.pos();
        let (tok_end, kind) = 'tok: {
          if let Some(subtrie) = self.tokens.get_ancestor(&self.data[self.pos..end]) {
            let len = subtrie.key().unwrap().len();
            let tok = subtrie.value().unwrap();
            if let TokenKind::Dollar(_) = tok {
              let num_end = (self.data[self.pos + 1..end].iter())
                .position(|&c| !c.is_ascii_digit())
                .map_or(end, |len| self.pos + 1 + len);
              // Safety: it is valid UTF8
              let str = unsafe { std::str::from_utf8_unchecked(&self.data[self.pos + 1..num_end]) };
              if let Ok(n) = str.parse() {
                if num_end >= ident_end {
                  break 'tok (num_end, TokenKind::Dollar(n))
                }
              }
            } else {
              let tok_end = self.pos + len;
              if tok_end >= ident_end {
                break 'tok (tok_end, *tok)
              }
            }
          }
          if ident_end > self.pos {
            let tok = if (b'1'..=b'9').contains(&self.data[self.pos])
              && self.data[self.pos + 1..ident_end].iter().all(|c| c.is_ascii_digit())
            {
              // Safety: it is valid UTF8
              let str = unsafe { std::str::from_utf8_unchecked(&self.data[self.pos..ident_end]) };
              if let Ok(n) = str.parse() {
                TokenKind::Number(n)
              } else {
                TokenKind::Error
              }
            } else {
              TokenKind::Ident
            };
            (ident_end, tok)
          } else {
            (end, TokenKind::Error)
          }
        };
        let spelling = std::str::from_utf8(&self.data[self.pos..tok_end]).unwrap();
        self.pos = tok_end;
        if tok_end == end {
          self.phrase_end = None;
        }
        return Token { spelling, pos, kind }
      }
      loop {
        let Some(&c) = self.data.get(self.pos) else {
          return Token { spelling: "", pos: self.pos(), kind: TokenKind::Eof }
        };
        if c == b' ' {
          self.pos += 1;
          continue
        }
        if c == b'\n' {
          self.pos += 1;
          self.line += 1;
          self.line_start = self.pos;
          continue
        }
        if c == b':' && self.data.get(self.pos + 1) == Some(&b':') {
          if self.pos == self.line_start && self.data.get(self.pos + 2) == Some(&b'$') {
            let start = self.pos;
            let pos = self.pos();
            self.pos += 3;
            let spelling = if let Some(len) = memchr::memchr(b'\n', &self.data[self.pos..]) {
              self.pos += len + 1;
              self.line += 1;
              self.line_start = self.pos;
              &self.data[start..][..len + 3]
            } else {
              self.pos = self.data.len();
              &self.data[start..]
            };
            let spelling = std::str::from_utf8(spelling).unwrap();
            return Token { spelling, pos, kind: TokenKind::Pragma }
          }
          self.pos += 2;
          match memchr::memchr(b'\n', &self.data[self.pos..]) {
            Some(x) => self.pos += x + 1,
            None => self.pos = self.data.len(),
          }
          self.line += 1;
          self.line_start = self.pos;
          continue
        }
        let end = memchr::memchr3_iter(b' ', b'\n', b':', &self.data[self.pos..])
          .map(|i| self.pos + i)
          .find(|&i| self.data[i] != b':' || self.data.get(i + 1) == Some(&b':'))
          .unwrap_or(self.data.len());
        // vprintln!("phrase = {:?}", std::str::from_utf8(&self.data[self.pos..end]).unwrap());
        // crate::set_verbose(self.line >= 402);
        self.phrase_end = Some(end);
        continue 'slice_phrase
      }
    }
    // vprintln!("next = {tok:?}\n{:?}", backtrace::Backtrace::new());
  }

  fn next_if(&mut self, f: impl FnOnce(&Token<'a>) -> bool) -> Option<Token<'a>> {
    if f(self.peek()) {
      return Some(self.next())
    }
    None
  }

  #[track_caller]
  fn accept(&mut self, kind: impl Into<TokenKind>) -> Token<'a> {
    let kind = kind.into();
    let tok = self.next();
    assert!(tok.kind == kind, "{:?}: expected {kind:?}", tok.pos);
    tok
  }

  fn try_accept(&mut self, kind: impl Into<TokenKind>) -> bool {
    self.next_if(|tok| tok.kind == kind.into()).is_some()
  }
}

pub struct Parser<'a> {
  pub scan: Scanner<'a>,
  pub art: Article,
  pub articles: HashMap<Article, ArticleId>,
  sch: (HashMap<&'a str, SchId>, SchId),
  pub formats: IdxVec<FormatId, Format>,
  max_mode_args: HashMap<ModeSymId, u8>,
  max_struct_args: HashMap<StructSymId, u8>,
  max_pred_rhs: HashMap<PredSymId, u8>,
}

impl<'a> Parser<'a> {
  pub fn new(art: Article, data: &'a [u8]) -> Self {
    Self {
      scan: Scanner::new(data),
      art,
      articles: Default::default(),
      sch: Default::default(),
      formats: Default::default(),
      max_mode_args: Default::default(),
      max_struct_args: Default::default(),
      max_pred_rhs: Default::default(),
    }
  }

  pub fn read_format(&mut self, fmt: &Format) {
    match fmt {
      Format::Mode(fmt) => {
        let max = self.max_mode_args.entry(fmt.sym).or_default();
        *max = (*max).max(fmt.args)
      }
      Format::Struct(fmt) => {
        let max = self.max_struct_args.entry(fmt.sym).or_default();
        *max = (*max).max(fmt.args)
      }
      Format::Pred(fmt) => {
        let max = self.max_pred_rhs.entry(fmt.sym).or_default();
        *max = (*max).max(fmt.right)
      }
      _ => {}
    }
  }

  pub fn push_format(&mut self, fmt: Format) {
    self.read_format(&fmt);
    self.formats.push(fmt);
  }

  fn parse_article(tok: Token<'a>) -> Article {
    assert!(
      tok.spelling.len() <= MAX_ARTICLE_LEN,
      "article names are at most {MAX_ARTICLE_LEN} characters"
    );
    Article::from_upper(tok.spelling.as_bytes())
  }

  pub fn parse_env(&mut self, dirs: &mut Directives) {
    dirs.0[DirectiveKind::Vocabularies].push((Position::default(), Article::HIDDEN));
    dirs.0[DirectiveKind::Notations].push((Position::default(), Article::HIDDEN));
    dirs.0[DirectiveKind::Constructors].push((Position::default(), Article::HIDDEN));
    dirs.0[DirectiveKind::Requirements].push((Position::default(), Article::HIDDEN));
    self.scan.accept(Keyword::Environ);
    loop {
      let tok = self.scan.next();
      match tok.kind {
        TokenKind::Directive(dir) => loop {
          let tok = self.scan.accept(TokenKind::Ident);
          dirs.0[dir].push((tok.pos, Self::parse_article(tok)));
          let tok = self.scan.next();
          match tok.kind {
            TokenKind::Keyword(Keyword::Comma) => {}
            TokenKind::Keyword(Keyword::Semicolon) => break,
            _ => panic!("{:?}: expected ',' or ';'", tok.pos),
          }
        },
        TokenKind::Keyword(Keyword::Begin) => break,
        _ => panic!("{:?}: expected 'begin'", tok.pos),
      }
    }
    self.scan.allow_underscore = false
  }

  fn parse_variable(&mut self) -> Variable {
    let tok = self.scan.accept(TokenKind::Ident);
    Variable { pos: tok.pos, id: 0, var: None, spelling: tok.spelling.to_owned() }
  }

  fn parse_label(&mut self) -> Option<Box<Label>> {
    if !matches!(self.scan.peek().kind, TokenKind::Ident) {
      return None
    }
    let tok = self.scan.next();
    if matches!(self.scan.peek().kind, TokenKind::Keyword(Keyword::Colon)) {
      self.scan.next();
      Some(Box::new(Label { pos: tok.pos, id: (Default::default(), tok.spelling.to_owned()) }))
    } else {
      self.scan.undo(tok);
      None
    }
  }

  fn separated<T>(&mut self, kw: Keyword, mut f: impl FnMut(&mut Self) -> T) -> Vec<T> {
    let mut out = vec![];
    loop {
      out.push(f(self));
      if self.scan.peek().kind != TokenKind::Keyword(kw) {
        break
      }
      self.scan.next();
    }
    out
  }

  fn comma_separated<T>(&mut self, f: impl FnMut(&mut Self) -> T) -> Vec<T> {
    self.separated(Keyword::Comma, f)
  }

  fn comma_separated_upto<T>(&mut self, mut max: u8, mut f: impl FnMut(&mut Self) -> T) -> Vec<T> {
    let mut out = vec![];
    loop {
      out.push(f(self));
      max -= 1;
      if max == 0 || !self.scan.try_accept(Keyword::Comma) {
        break
      }
    }
    out
  }

  fn parse_where(&mut self) -> Vec<BinderGroup> {
    let mut out = vec![];
    loop {
      let vars = self.comma_separated(|this| this.parse_variable());
      let ty = (self.scan)
        .next_if(|tok| matches!(tok.kind, TokenKind::Keyword(Keyword::Is | Keyword::Are)))
        .map(|_| self.parse_type());
      out.push(BinderGroup { vars, ty });
      if !matches!(self.scan.peek().kind, TokenKind::Keyword(Keyword::Where | Keyword::Comma)) {
        break
      }
      self.scan.next();
    }
    out
  }

  fn parse_terms(&mut self) -> Vec<Term> { self.comma_separated(|this| *this.parse_term()) }

  fn parse_term_hi(&mut self) -> Option<Box<Term>> {
    let tok = self.scan.next();
    Some(match tok.kind {
      TokenKind::LPAREN => {
        let t = self.parse_term();
        self.scan.accept(TokenKind::RPAREN);
        t
      }
      TokenKind::Ident =>
        if self.scan.try_accept(TokenKind::LPAREN) {
          let args =
            if self.scan.peek().kind == TokenKind::RPAREN { vec![] } else { self.parse_terms() };
          self.scan.accept(TokenKind::RPAREN);
          Box::new(Term::PrivFunc {
            pos: tok.pos,
            kind: VarKind::Unknown,
            var: 0,
            spelling: tok.spelling.to_owned(),
            args,
          })
        } else {
          Box::new(Term::Simple {
            pos: tok.pos,
            kind: VarKind::Unknown,
            var: 0,
            spelling: tok.spelling.to_owned(),
            origin: VarKind::Unknown,
          })
        },
      TokenKind::Number(value) => Box::new(Term::Numeral { pos: tok.pos, value }),
      TokenKind::Keyword(Keyword::It) => Box::new(Term::It { pos: tok.pos }),
      TokenKind::Dollar(nr) => {
        let nr =
          nr.checked_sub(1).expect("expected positive integer").try_into().expect("out of range");
        Box::new(Term::Placeholder { pos: tok.pos, nr: LocusId(nr) })
      }
      TokenKind::Symbol(SymbolKind::Struct(sym)) if self.scan.try_accept(Keyword::AggrLeftBrk) => {
        let args = self.parse_terms();
        self.scan.accept(Keyword::AggrRightBrk);
        Box::new(Term::Aggregate { pos: tok.pos, sym: (sym, tok.spelling.to_owned()), args })
      }
      TokenKind::Symbol(SymbolKind::LeftBrk(lsym)) => {
        let args = self.parse_terms();
        let tok2 = self.scan.next();
        if lsym == LeftBrkSymId::LBRACE
          && args.len() == 1
          && matches!(tok2.kind, TokenKind::Keyword(Keyword::Colon | Keyword::Where))
        {
          let scope = Box::new({ args }.pop().unwrap());
          let vars;
          if tok2.kind == Keyword::Where.into() {
            vars = self.parse_where();
            self.scan.accept(Keyword::Colon);
          } else {
            vars = vec![]
          }
          let compr = Some(self.parse_formula());
          self.scan.accept(TokenKind::RBRACE);
          Box::new(Term::Fraenkel { pos: tok.pos, vars, scope, compr })
        } else {
          let lsym = (lsym, tok.spelling.to_owned());
          let TokenKind::Symbol(SymbolKind::RightBrk(rsym)) = tok2.kind else {
            panic!("{:?}: expected right bracket symbol", tok2.pos)
          };
          let rsym = (rsym, tok2.spelling.to_owned());
          Box::new(Term::Bracket { pos: tok.pos, lsym, rsym, args })
        }
      }
      TokenKind::Keyword(Keyword::The) => {
        let tok2 = self.scan.next();
        match tok2.kind {
          TokenKind::Symbol(SymbolKind::Sel(sym)) => {
            let sym = (sym, tok2.spelling.to_owned());
            if self.scan.try_accept(Keyword::Of) {
              Box::new(Term::Selector { pos: tok.pos, sym, arg: self.parse_term() })
            } else {
              Box::new(Term::InternalSelector { pos: tok.pos, sym, id: Default::default() })
            }
          }
          TokenKind::Symbol(SymbolKind::Struct(sym)) if self.scan.try_accept(Keyword::Of) => {
            let sym = (sym, tok2.spelling.to_owned());
            Box::new(Term::SubAggr { pos: tok.pos, sym, arg: self.parse_term() })
          }
          TokenKind::SET if self.scan.try_accept(Keyword::Of) => {
            self.scan.accept(Keyword::All);
            let scope = self.parse_term();
            let vars =
              if self.scan.try_accept(Keyword::Where) { self.parse_where() } else { vec![] };
            Box::new(Term::Fraenkel { pos: tok.pos, vars, scope, compr: None })
          }
          _ => {
            self.scan.undo(tok2);
            Box::new(Term::The { pos: tok.pos, ty: self.parse_type() })
          }
        }
      }
      _ => {
        self.scan.undo(tok);
        return None
      }
    })
  }

  /// if max_out is Some(n), then at most n results will be returned at paren level 0
  /// (unless n = 0 in which case 1 return is still possible)
  fn parse_func_rhs(
    &mut self, paren: &mut u32, mut max_out: Option<u8>, mut lhs: Vec<Term>,
  ) -> Vec<Term> {
    loop {
      match self.scan.peek().kind {
        TokenKind::Symbol(SymbolKind::Func(sym)) => {
          let tok = self.scan.next();
          let sym = (sym, tok.spelling.to_owned());
          let mut args;
          if self.scan.try_accept(TokenKind::LPAREN) {
            args = self.parse_terms();
            self.scan.accept(TokenKind::RPAREN);
          } else {
            args = match self.parse_term_hi() {
              Some(tm) => vec![*tm],
              None => vec![],
            }
          }
          let left = lhs.len() as u8;
          lhs.append(&mut args);
          lhs = vec![Term::Infix { pos: tok.pos, sym, left, args: lhs }]
        }
        TokenKind::Keyword(Keyword::Qua) if lhs.len() == 1 => {
          let tok = self.scan.next();
          let ty = self.parse_type();
          lhs = vec![Term::Qua { pos: tok.pos, term: Box::new(lhs.pop().unwrap()), ty }]
        }
        TokenKind::Keyword(Keyword::Comma)
          if !lhs.is_empty()
            && (*paren > 0 || max_out.as_mut().map_or(true, |n| *n > 1 && (*n -= 1, true).1)) =>
        {
          self.scan.next();
          lhs.push(*self.parse_term());
        }
        TokenKind::RPAREN if *paren > 0 => {
          *paren -= 1;
          self.scan.next();
        }
        _ => break,
      }
    }
    lhs
  }

  fn with_parens<R>(&mut self, f: impl FnOnce(&mut Self, &mut u32) -> R) -> R {
    let mut paren = 0;
    while self.scan.try_accept(TokenKind::LPAREN) {
      paren += 1;
    }
    let out = f(self, &mut paren);
    for _ in 0..paren {
      self.scan.accept(TokenKind::RPAREN);
    }
    out
  }

  fn parse_terms_lo_or_radix_type(
    &mut self, upto: Option<u8>, allow_type: bool,
  ) -> Result<Vec<Term>, Box<Type>> {
    self.with_parens(|this, paren| {
      let lhs = match this.parse_term_hi() {
        Some(tm) => vec![*tm],
        None => vec![],
      };
      let args = this.parse_func_rhs(paren, upto, lhs);
      if allow_type && args.is_empty() {
        if let Some(ty) = this.parse_radix_type() {
          return Err(ty)
        }
      }
      Ok(args)
    })
  }

  /// * If `allow_type` is false, the `Option<Box<Type>>` is always None
  /// * If `allow_term` is false, the `Err` variant never occurs
  #[allow(clippy::type_complexity)]
  fn parse_attrs_or_type_or_term(
    &mut self, allow_type: bool, allow_term: bool,
  ) -> Result<(Vec<Attr>, Option<Box<Type>>), Box<Term>> {
    let mut attrs = vec![];
    loop {
      let non = self.scan.next_if(|tok| tok.kind == Keyword::Non.into());
      let args = match self.parse_terms_lo_or_radix_type(None, allow_type && non.is_none()) {
        Ok(args) => args,
        Err(ty) => {
          if let Some(non) = non {
            panic!("{:?}: expected attribute", non.pos);
          }
          return Ok((attrs, Some(ty)))
        }
      };
      let tok = self.scan.next();
      let TokenKind::Symbol(SymbolKind::Attr(sym)) = tok.kind else {
        self.scan.undo(tok);
        if allow_term && non.is_none() && attrs.is_empty() && args.len() == 1 {
          return Err(Box::new({ args }.pop().unwrap()))
        }
        assert!(non.is_none() && args.is_empty(), "{:?}: expected attribute", tok.pos);
        return Ok((attrs, if allow_type { self.parse_radix_type() } else { None }))
      };
      let mut attr = Attr::Attr { pos: tok.pos, sym: (sym, tok.spelling.to_owned()), args };
      if let Some(non) = non {
        attr = Attr::Non { pos: non.pos, attr: Box::new(attr) };
      }
      attrs.push(attr)
    }
  }

  fn parse_term(&mut self) -> Box<Term> {
    self.with_parens(|this, paren| {
      let lhs = match this.parse_term_hi() {
        Some(tm) => vec![*tm],
        None => vec![],
      };
      let out = this.parse_func_rhs(paren, Some(0), lhs);
      assert!(out.len() == 1, "{:?}: expected functor symbol", this.scan.peek().pos);
      Box::new({ out }.pop().unwrap())
    })
  }

  fn parse_atomic_formula(&mut self, paren: &mut u32) -> Box<Formula> {
    let lhs = match self.parse_term_hi() {
      Some(tm) => vec![*tm],
      None => vec![],
    };
    let args = self.parse_func_rhs(paren, None, lhs);
    let is =
      if args.len() == 1 { self.scan.next_if(|tok| tok.kind == Keyword::Is.into()) } else { None };
    if let Some(tok) = is {
      let positive = !self.scan.try_accept(Keyword::Not);
      let term = Box::new({ args }.pop().unwrap());
      let (attrs, ty) = self.parse_attrs_or_type_or_term(true, false).unwrap();
      if let Some(mut ty) = ty {
        if !attrs.is_empty() {
          ty = Box::new(Type::Cluster { pos: attrs[0].pos(), attrs, ty })
        }
        Box::new(Formula::Is { pos: tok.pos, positive, term, ty })
      } else {
        assert!(!attrs.is_empty(), "{:?}: expected attribute", self.scan.peek().pos);
        Box::new(Formula::Attr { pos: tok.pos, positive, term, attrs })
      }
    } else {
      let mut lhs = Err(args);
      let (first, rest) = loop {
        let mut tok = self.scan.next();
        let (positive, sym) = match tok.kind {
          TokenKind::Symbol(SymbolKind::Pred(sym)) => (true, sym),
          TokenKind::Keyword(Keyword::Do) => {
            self.scan.accept(Keyword::Not);
            tok = self.scan.next();
            let TokenKind::Symbol(SymbolKind::Pred(sym)) = tok.kind else {
              panic!("{:?}: expected predicate symbol", tok.pos)
            };
            (false, sym)
          }
          _ => {
            self.scan.undo(tok);
            break lhs.unwrap_or_else(|_| panic!("{:?}: expected predicate symbol", tok.pos))
          }
        };
        let mut right =
          self.parse_terms_lo_or_radix_type(Some(self.max_pred_rhs[&sym]), false).unwrap();
        let sym = (sym, tok.spelling.to_owned());
        lhs = Ok(match lhs {
          Err(mut args) => {
            let left = args.len().try_into().expect("too many arguments");
            args.append(&mut right);
            (Box::new(Pred { pos: tok.pos, positive, sym, left, args }), vec![])
          }
          Ok((pred, mut rhss)) => {
            Vec::push(&mut rhss, PredRhs { pos: tok.pos, positive, sym, right });
            (pred, rhss)
          }
        })
      };
      if rest.is_empty() {
        Box::new(Formula::Pred(first))
      } else {
        Box::new(Formula::ChainPred { pos: first.pos, first, rest })
      }
    }
  }

  fn parse_formula_lhs(&mut self) -> Box<Formula> {
    let mut paren = 0;
    while self.scan.try_accept(TokenKind::LPAREN) {
      paren += 1;
    }
    let tok = self.scan.next();
    let mut lhs = match tok.kind {
      TokenKind::Keyword(Keyword::For) => {
        let vars = self.parse_binders();
        let st = self.scan.try_accept(Keyword::St).then(|| self.parse_formula());
        if !self.scan.try_accept(Keyword::Holds) {
          let tok = self.scan.peek();
          assert!(
            matches!(tok.kind, TokenKind::Keyword(Keyword::For | Keyword::Ex)),
            "{:?}: expected 'holds'",
            tok.pos
          )
        }
        let scope = self.parse_formula();
        Box::new(Formula::Binder { kind: FormulaBinder::ForAll, pos: tok.pos, vars, st, scope })
      }
      TokenKind::Keyword(Keyword::Ex) => {
        let vars = self.parse_binders();
        self.scan.accept(Keyword::St);
        let (st, scope) = (None, self.parse_formula());
        Box::new(Formula::Binder { kind: FormulaBinder::Exists, pos: tok.pos, vars, st, scope })
      }
      TokenKind::Keyword(Keyword::Contradiction) => Box::new(Formula::False { pos: tok.pos }),
      TokenKind::Keyword(Keyword::Thesis) => Box::new(Formula::Thesis { pos: tok.pos }),
      TokenKind::Keyword(Keyword::Not) =>
        Box::new(Formula::Not { pos: tok.pos, f: self.parse_formula_lhs() }),
      TokenKind::Ident if self.scan.try_accept(TokenKind::LBRACK) => {
        let args =
          if self.scan.peek().kind == TokenKind::RBRACK { vec![] } else { self.parse_terms() };
        self.scan.accept(TokenKind::RBRACK);
        Box::new(Formula::PrivPred {
          pos: tok.pos,
          kind: VarKind::Unknown,
          var: 0,
          spelling: tok.spelling.to_owned(),
          args,
        })
      }
      _ => {
        self.scan.undo(tok);
        self.parse_atomic_formula(&mut paren)
      }
    };
    for _ in 0..paren {
      lhs = self.parse_formula_rhs(0, lhs);
      self.scan.accept(TokenKind::RPAREN);
    }
    lhs
  }

  fn parse_formula_rhs(&mut self, prec: u8, mut lhs: Box<Formula>) -> Box<Formula> {
    const IFF_PREC: u8 = 0;
    const IMP_PREC: u8 = 0;
    const FLEX_OR_PREC: u8 = 1;
    const OR_PREC: u8 = 2;
    const FLEX_AND_PREC: u8 = 3;
    const AND_PREC: u8 = 4;
    const MAX_PREC: u8 = 4;
    loop {
      let tok = self.scan.next();
      let then_ellipsis = matches!(tok.kind, TokenKind::Keyword(Keyword::Amp | Keyword::Or))
        && self.scan.peek().kind == Keyword::Ellipsis.into();
      macro_rules! binop {
        ($binop:ident, $prec:expr) => {{
          let mut rhs = self.parse_formula_lhs();
          if $prec < MAX_PREC {
            rhs = self.parse_formula_rhs($prec + 1, rhs);
          }
          let kind = FormulaBinop::$binop;
          lhs = Box::new(Formula::Binop { kind, pos: tok.pos, f1: lhs, f2: rhs })
        }};
      }
      #[allow(clippy::absurd_extreme_comparisons)]
      match tok.kind {
        TokenKind::Keyword(Keyword::Amp) if then_ellipsis && prec <= FLEX_AND_PREC => {
          self.scan.next();
          self.scan.accept(Keyword::Amp);
          binop!(FlexAnd, FLEX_AND_PREC)
        }
        TokenKind::Keyword(Keyword::Amp) if !then_ellipsis && prec <= AND_PREC =>
          binop!(And, AND_PREC),
        TokenKind::Keyword(Keyword::Or) if then_ellipsis && prec <= FLEX_OR_PREC => {
          self.scan.next();
          self.scan.accept(Keyword::Or);
          binop!(FlexOr, FLEX_OR_PREC)
        }
        TokenKind::Keyword(Keyword::Or) if !then_ellipsis && prec <= OR_PREC => binop!(Or, OR_PREC),
        TokenKind::Keyword(Keyword::Iff) if prec <= IFF_PREC => binop!(Iff, IFF_PREC),
        TokenKind::Keyword(Keyword::Implies) if prec <= IMP_PREC => binop!(Imp, IMP_PREC),
        _ => {
          self.scan.undo(tok);
          return lhs
        }
      }
    }
  }

  fn parse_formula(&mut self) -> Box<Formula> {
    let lhs = self.parse_formula_lhs();
    self.parse_formula_rhs(0, lhs)
  }

  fn parse_radix_type(&mut self) -> Option<Box<Type>> {
    self.with_parens(|this, paren| {
      let tok = this.scan.next();
      match tok.kind {
        TokenKind::Symbol(SymbolKind::Mode(sym)) => {
          let max = this.max_mode_args[&sym];
          let sym = (sym, tok.spelling.to_owned());
          let args = if max > 0 && this.scan.try_accept(Keyword::Of) {
            this.comma_separated_upto(max, |this| *this.parse_term())
          } else {
            vec![]
          };
          Some(Box::new(Type::Mode { pos: tok.pos, sym, args }))
        }
        TokenKind::Symbol(SymbolKind::Struct(sym)) => {
          let max = this.max_struct_args[&sym];
          let sym = (sym, tok.spelling.to_owned());
          let args = if max > 0 && this.scan.try_accept(Keyword::Over) {
            this.comma_separated_upto(max, |this| *this.parse_term())
          } else {
            vec![]
          };
          Some(Box::new(Type::Struct { pos: tok.pos, sym, args }))
        }
        _ if *paren == 0 => {
          this.scan.undo(tok);
          None
        }
        _ => panic!("{:?}: expected type", tok.pos),
      }
    })
  }

  fn parse_type(&mut self) -> Box<Type> {
    let (attrs, ty) = self.parse_attrs_or_type_or_term(true, false).unwrap();
    let mut ty = ty.unwrap_or_else(|| panic!("{:?}: expected type", self.scan.peek().pos));
    if !attrs.is_empty() {
      ty = Box::new(Type::Cluster { pos: attrs[0].pos(), attrs, ty })
    }
    ty
  }

  fn parse_types(&mut self) -> Vec<Type> {
    if matches!(self.scan.peek().kind, TokenKind::RBRACK | TokenKind::RPAREN) {
      vec![]
    } else {
      self.comma_separated(|this| *this.parse_type())
    }
  }

  fn parse_proposition(&mut self) -> Proposition {
    Proposition { label: self.parse_label(), f: *self.parse_formula() }
  }

  fn assert_no_link(link: Option<Position>) {
    if let Some(pos) = link {
      panic!("{pos:?}: 'then' not expected here");
    }
  }

  fn with_underscore<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
    let old = self.scan.allow_underscore;
    assert!(self.scan.lookahead.is_none(), "can't reset underscore state, already parsed");
    self.scan.allow_underscore = true;
    let r = f(self);
    self.scan.allow_underscore = old;
    r
  }

  fn parse_references(&mut self) -> Vec<Reference> {
    self.comma_separated(|this| {
      let id = this.scan.accept(TokenKind::Ident);
      let kind = if this.scan.try_accept(Keyword::Colon) {
        let art = *this.articles.get(&Self::parse_article(id)).unwrap_or_else(|| {
          panic!("article not found, perhaps you forgot 'theorems {}'", id.spelling)
        });
        let mut refs = vec![];
        loop {
          refs.push(if this.scan.try_accept(Keyword::Def) {
            let tok = this.scan.next();
            let TokenKind::Number(n) = tok.kind else { panic!("{:?}: expected numeral", tok.pos) };
            let id = DefId(n.checked_sub(1).expect("expected nonzero numeral"));
            RefFragment::Def { pos: tok.pos, id }
          } else {
            let tok = this.scan.next();
            let TokenKind::Number(n) = tok.kind else { panic!("{:?}: expected numeral", tok.pos) };
            let id = ThmId(n.checked_sub(1).expect("expected nonzero numeral"));
            RefFragment::Thm { pos: tok.pos, id }
          });
          let tok = this.scan.next();
          if tok.kind != TokenKind::Keyword(Keyword::Comma)
            || this.scan.peek().kind == TokenKind::Ident
          {
            this.scan.undo(tok);
            break ReferenceKind::Global(art, refs)
          }
        }
      } else {
        ReferenceKind::UnresolvedPriv(id.spelling.to_owned())
      };
      Reference { pos: id.pos, kind }
    })
  }

  fn parse_simple_justification(&mut self, link: Option<Position>) -> Justification {
    let tok = self.scan.next();
    match tok.kind {
      TokenKind::Keyword(Keyword::By) => Justification::Inference {
        pos: tok.pos,
        kind: InferenceKind::By { link },
        refs: self.with_underscore(|this| this.parse_references()),
      },
      TokenKind::Keyword(Keyword::From) => self.with_underscore(|this| {
        let id = this.scan.accept(TokenKind::Ident);
        let sch = if this.scan.try_accept(Keyword::Colon) {
          let art = *this.articles.get(&Self::parse_article(id)).unwrap_or_else(|| {
            panic!("article not found, perhaps you forgot 'schemes {}'", id.spelling)
          });
          this.scan.accept(Keyword::Sch);
          let tok = this.scan.next();
          let TokenKind::Number(n) = tok.kind else { panic!("expected numeral") };
          (art, SchId(n.checked_sub(1).expect("expected nonzero numeral")))
        } else {
          let sch = *(this.sch.0.get(id.spelling))
            .unwrap_or_else(|| panic!("local scheme '{}' not found", id.spelling));
          (ArticleId::SELF, sch)
        };
        let mut refs = vec![];
        if this.scan.try_accept(TokenKind::LPAREN) {
          refs = this.parse_references();
          this.scan.accept(TokenKind::RPAREN);
        }
        Justification::Inference { pos: tok.pos, kind: InferenceKind::From { sch }, refs }
      }),
      _ => {
        self.scan.undo(tok);
        Justification::Inference { pos: tok.pos, kind: InferenceKind::By { link }, refs: vec![] }
      }
    }
  }

  fn parse_justification(&mut self, link: Option<Position>) -> Justification {
    if let Some(tok) = self.scan.next_if(|tok| tok.kind == Keyword::Proof.into()) {
      Self::assert_no_link(link);
      let (items, end) = self.parse_proof();
      Justification::Block { pos: (tok.pos, end), items }
    } else {
      self.parse_simple_justification(link)
    }
  }

  fn parse_justification_semi(&mut self, link: Option<Position>) -> Justification {
    let just = self.parse_justification(link);
    self.scan.accept(Keyword::Semicolon);
    just
  }

  fn parse_scheme(&mut self) -> Box<SchemeBlock> {
    let sym =
      (self.scan.next_if(|tok| matches!(tok.kind, TokenKind::Ident))).map(|tok| tok.spelling);
    self.scan.accept(TokenKind::LBRACE);
    let groups = self.comma_separated(|this| {
      let pos = this.scan.peek().pos;
      let vars = this.comma_separated(|this| this.parse_variable());
      let tok = this.scan.next();
      match tok.kind {
        TokenKind::LBRACK => {
          let tys = this.parse_types();
          this.scan.accept(TokenKind::RBRACK);
          SchemeBinderGroup::Pred { pos, vars, tys }
        }
        TokenKind::LPAREN => {
          let tys = this.parse_types();
          this.scan.accept(TokenKind::RPAREN);
          this.scan.accept(TokenKind::Keyword(Keyword::Arrow));
          let ret = *this.parse_type();
          SchemeBinderGroup::Func { pos, vars, tys, ret }
        }
        _ => panic!("{:?}: expected ',', '[', '{{'", tok.pos),
      }
    });
    self.scan.accept(TokenKind::RBRACE);
    self.scan.accept(Keyword::Colon);
    let concl = *self.parse_formula();
    let prems = if self.scan.try_accept(Keyword::Provided) {
      self.separated(Keyword::And, |this| this.parse_proposition())
    } else {
      vec![]
    };
    self.scan.accept(Keyword::Proof);
    let (items, end) = self.parse_proof();
    self.scan.accept(Keyword::Semicolon);
    let id = self.sch.1.fresh();
    let sym = sym.map(|sym| {
      self.sch.0.insert(sym, id);
      sym.to_owned()
    });
    let head = SchemeHead { sym, nr: SchId(0), groups, concl, prems };
    Box::new(SchemeBlock { end, head, items })
  }

  fn parse_params(&mut self, must_paren: bool) -> Vec<Variable> {
    if self.scan.try_accept(TokenKind::LPAREN) {
      let args = self.comma_separated(|this| this.parse_variable());
      self.scan.accept(TokenKind::RPAREN);
      args
    } else if self.scan.peek().kind == TokenKind::Ident {
      if must_paren {
        vec![self.parse_variable()]
      } else {
        self.comma_separated(|this| this.parse_variable())
      }
    } else {
      vec![]
    }
  }

  fn parse_pattern_rhs(&mut self, pos: Position, paren: bool, mut args: Vec<Variable>) -> Pattern {
    let tok = self.scan.next();
    match tok.kind {
      TokenKind::Symbol(SymbolKind::Func(sym)) if paren || args.len() <= 1 => {
        let sym = (sym, tok.spelling.to_owned());
        let left = args.len().try_into().expect("too many arguments");
        args.append(&mut self.parse_params(true));
        Pattern::Func(Box::new(PatternFunc::Func { pos, sym, left, args }))
      }
      TokenKind::Symbol(SymbolKind::LeftBrk(lsym)) if args.is_empty() => {
        let lsym = (lsym, tok.spelling.to_owned());
        args = self.comma_separated(|this| this.parse_variable());
        let tok = self.scan.next();
        let TokenKind::Symbol(SymbolKind::RightBrk(rsym)) = tok.kind else {
          panic!("{:?}: expected right bracket symbol", tok.pos)
        };
        let rsym = (rsym, tok.spelling.to_owned());
        Pattern::Func(Box::new(PatternFunc::Bracket { pos, lsym, rsym, args }))
      }
      TokenKind::Symbol(SymbolKind::Pred(sym)) if !paren => {
        let left = args.len().try_into().expect("too many arguments");
        if self.scan.peek().kind == TokenKind::Ident {
          args.append(&mut self.comma_separated(|this| this.parse_variable()));
        }
        Pattern::Pred(Box::new(PatternPred {
          pos,
          sym: (sym, tok.spelling.to_owned()),
          left,
          args,
        }))
      }
      _ => panic!("{:?}: expected functor or predicate symbol", tok.pos),
    }
  }

  fn parse_pattern(&mut self) -> Pattern {
    let tok = self.scan.next();
    match tok.kind {
      TokenKind::Symbol(SymbolKind::Mode(sym)) => {
        let args = if self.scan.try_accept(Keyword::Of) {
          self.comma_separated(|this| this.parse_variable())
        } else {
          vec![]
        };
        Pattern::Mode(Box::new(PatternMode {
          pos: tok.pos,
          sym: (sym, tok.spelling.to_owned()),
          args,
        }))
      }
      TokenKind::LPAREN => {
        let args = self.comma_separated(|this| this.parse_variable());
        self.scan.accept(TokenKind::RPAREN);
        self.parse_pattern_rhs(tok.pos, true, args)
      }
      TokenKind::Ident => {
        let id = Variable { pos: tok.pos, id: 0, var: None, spelling: tok.spelling.to_owned() };
        if self.scan.try_accept(Keyword::Is) {
          let mut args = self.parse_params(false);
          args.push(id);
          let tok = self.scan.next();
          let TokenKind::Symbol(SymbolKind::Attr(n)) = tok.kind else {
            panic!("{:?}: expected attr symbol", tok.pos)
          };
          Pattern::Attr(Box::new(PatternAttr {
            pos: tok.pos,
            sym: (n, tok.spelling.to_owned()),
            args,
          }))
        } else {
          let mut args = vec![id];
          while self.scan.try_accept(Keyword::Comma) {
            args.push(self.parse_variable())
          }
          self.parse_pattern_rhs(tok.pos, false, args)
        }
      }
      _ => {
        self.scan.undo(tok);
        self.parse_pattern_rhs(tok.pos, false, vec![])
      }
    }
  }

  fn parse_definiens<T>(
    &mut self, mut f: impl FnMut(&mut Self) -> Box<T>, mk_kind: impl FnOnce(DefBody<T>) -> DefValue,
  ) -> Box<Definiens> {
    let label =
      if self.scan.try_accept(Keyword::Colon) { Some(self.parse_label().unwrap()) } else { None };
    let pos = self.scan.peek().pos;
    let mut value = f(self);
    let mut cases = vec![];
    let otherwise = if self.scan.try_accept(Keyword::If) {
      loop {
        cases.push(DefCase { case: value, guard: self.parse_formula() });
        if !self.scan.try_accept(Keyword::Comma) {
          break
        }
        value = f(self);
        self.scan.accept(Keyword::If);
      }
      self.scan.try_accept(Keyword::Otherwise).then(|| f(self))
    } else {
      Some(value)
    };
    Box::new(Definiens { pos, label, kind: mk_kind(DefBody { cases, otherwise }) })
  }

  fn parse_corr_conds(&mut self) -> (Vec<CorrCond>, Option<Correctness>) {
    let mut conds = vec![];
    while let TokenKind::CorrCond(kind) = self.scan.peek().kind {
      let pos = self.scan.next().pos;
      conds.push(CorrCond { pos, kind, just: self.parse_justification_semi(None) });
    }
    let corr = (self.scan.next_if(|tok| tok.kind == Keyword::Correctness.into()))
      .map(|tok| Correctness { pos: tok.pos, just: self.parse_justification_semi(None) });
    (conds, corr)
  }

  fn parse_properties(&mut self) -> Vec<Property> {
    let mut props = vec![];
    while let TokenKind::Property(kind) = self.scan.peek().kind {
      self.scan.next();
      props.push(Property { kind, just: Box::new(self.parse_justification_semi(None)) });
    }
    props
  }

  fn parse_definition(&mut self, redef: bool, mut kind: DefinitionKind) -> ItemKind {
    if let DefinitionKind::Func { def, .. }
    | DefinitionKind::Pred { def, .. }
    | DefinitionKind::Mode { kind: DefModeKind::Standard { def, .. }, .. }
    | DefinitionKind::Attr { def, .. } = &mut kind
    {
      if self.scan.try_accept(Keyword::Means) {
        *def = Some(self.parse_definiens(|this| this.parse_formula(), DefValue::Formula))
      } else if self.scan.try_accept(Keyword::Equals) {
        *def = Some(self.parse_definiens(|this| this.parse_term(), DefValue::Term))
      }
    }
    self.scan.accept(Keyword::Semicolon);
    let (conds, corr) = self.parse_corr_conds();
    let props = self.parse_properties();
    match &kind {
      DefinitionKind::Func { pat, .. } => self.push_format(Format::Func(pat.to_format())),
      DefinitionKind::Pred { pat, .. } => self.push_format(Format::Pred(pat.to_format())),
      DefinitionKind::Mode { pat, .. } => self.push_format(Format::Mode(pat.to_format())),
      DefinitionKind::Attr { pat, .. } => self.push_format(Format::Attr(pat.to_format())),
    }
    ItemKind::Definition(Box::new(Definition { redef, kind, conds, corr, props }))
  }

  fn parse_binders(&mut self) -> Vec<BinderGroup> {
    self.comma_separated(|this| {
      let vars = this.comma_separated(|this| this.parse_variable());
      let ty = this.scan.try_accept(Keyword::Be).then(|| this.parse_type());
      BinderGroup { vars, ty }
    })
  }

  fn parse_choice(&mut self) -> (Vec<BinderGroup>, Vec<Proposition>) {
    let vars = self.parse_binders();
    self.scan.accept(Keyword::Such);
    self.scan.accept(Keyword::That);
    let conds = self.separated(Keyword::And, |this| this.parse_proposition());
    (vars, conds)
  }

  fn parse_then(&mut self) -> Option<Position> {
    let tok = self.scan.peek();
    if let TokenKind::Keyword(Keyword::Then) = tok.kind {
      Some(self.scan.next().pos)
    } else {
      None
    }
  }

  fn parse_stmt(&mut self, link: Option<Position>) -> Statement {
    let label = self.parse_label();
    let tok = self.scan.next();
    match tok.kind {
      TokenKind::Keyword(Keyword::Now) => {
        Self::assert_no_link(link);
        let (items, end) = self.parse_proof();
        Statement::Now { end, label, items }
      }
      _ => {
        self.scan.undo(tok);
        let prop = Box::new(Proposition { label, f: *self.parse_formula() });
        if let Some(tok) = self.scan.next_if(|tok| tok.kind == Keyword::Proof.into()) {
          Self::assert_no_link(link);
          let (items, end) = self.parse_proof();
          let just = Box::new(Justification::Block { pos: (tok.pos, end), items });
          Statement::Proposition { prop, just }
        } else {
          let just = Box::new(self.parse_simple_justification(link));
          let mut steps = vec![];
          while let Some(tok) = self.scan.next_if(|tok| tok.kind == Keyword::DotEquals.into()) {
            let rhs = *self.parse_term();
            let just = self.parse_simple_justification(None);
            steps.push(IterStep { pos: tok.pos, rhs, just });
          }
          if steps.is_empty() {
            Statement::Proposition { prop, just }
          } else {
            Statement::IterEquality { prop, just, steps }
          }
        }
      }
    }
  }

  fn parse_stmt_item(&mut self) -> ItemKind {
    let link = self.parse_then();
    let tok = self.scan.next();
    match tok.kind {
      TokenKind::Keyword(Keyword::DefFunc) => {
        Self::assert_no_link(link);
        let var = Box::new(self.parse_variable());
        self.scan.accept(TokenKind::LPAREN);
        let tys = self.parse_types();
        self.scan.accept(TokenKind::RPAREN);
        self.scan.accept(TokenKind::EQUAL);
        let value = self.parse_term();
        ItemKind::DefFunc { var, tys, value }
      }
      TokenKind::Keyword(Keyword::DefPred) => {
        Self::assert_no_link(link);
        let var = Box::new(self.parse_variable());
        self.scan.accept(TokenKind::LBRACK);
        let tys = self.parse_types();
        self.scan.accept(TokenKind::RBRACK);
        self.scan.accept(Keyword::Means);
        let value = self.parse_formula();
        ItemKind::DefPred { var, tys, value }
      }
      TokenKind::SET => {
        Self::assert_no_link(link);
        ItemKind::Set(self.comma_separated(|this| {
          let var = Box::new(this.parse_variable());
          this.scan.accept(TokenKind::EQUAL);
          SetDecl { var, value: this.parse_term() }
        }))
      }
      TokenKind::Keyword(Keyword::Reconsider) => {
        let vars = self.comma_separated(|this| {
          let var = this.parse_variable();
          if this.scan.try_accept(TokenKind::EQUAL) {
            ReconsiderVar::Equality { var, tm: *this.parse_term() }
          } else {
            ReconsiderVar::Var(var)
          }
        });
        self.scan.accept(Keyword::As);
        let ty = self.parse_type();
        ItemKind::Reconsider { vars, ty, just: Box::new(self.parse_simple_justification(link)) }
      }
      TokenKind::Keyword(Keyword::Consider) => {
        let (vars, conds) = self.parse_choice();
        ItemKind::Consider { vars, conds, just: Box::new(self.parse_simple_justification(link)) }
      }
      _ => {
        self.scan.undo(tok);
        ItemKind::Statement(self.parse_stmt(link))
      }
    }
  }

  fn parse_assumption(&mut self, pos: Position) -> Assumption {
    if self.scan.try_accept(Keyword::That) {
      let conds = self.separated(Keyword::And, |this| this.parse_proposition());
      Assumption::Collective { pos, conds }
    } else {
      Assumption::Single { pos, prop: Box::new(self.parse_proposition()) }
    }
  }

  fn parse_per_cases(
    &mut self, link: Option<Position>, pos: Position, items: &mut Vec<Item>,
  ) -> Position {
    self.scan.accept(Keyword::Cases);
    let just = Box::new(self.parse_simple_justification(link));
    self.scan.accept(Keyword::Semicolon);
    let mut casekind = None;
    let mut blocks = vec![];
    let end = loop {
      let tok = self.scan.next();
      let kind = match tok.kind {
        TokenKind::Keyword(Keyword::End) => break tok.end(),
        TokenKind::Keyword(Keyword::Case) => CaseKind::Case,
        TokenKind::Keyword(Keyword::Suppose) => CaseKind::Suppose,
        _ => panic!("{:?}: expected 'case' or 'suppose'", tok.pos),
      };
      if let Some(kind2) = casekind.replace(kind) {
        assert!(kind == kind2, "{:?}: expected 'case', got 'suppose' or vice versa", tok.pos)
      }
      let hyp = Box::new(self.parse_assumption(tok.pos));
      self.scan.accept(Keyword::Semicolon);
      let (items, end) = self.parse_proof();
      self.scan.accept(Keyword::Semicolon);
      blocks.push(CaseBlock { end, hyp, items })
    };
    let kind = casekind.unwrap_or_else(|| panic!("{:?}: no cases", pos));
    items.push(Item { pos, kind: ItemKind::PerCases { just, kind, blocks } });
    end
  }

  fn parse_proof(&mut self) -> (Vec<Item>, Position) {
    let mut items = vec![];
    let end = loop {
      let tok = self.scan.next();
      let kind = match tok.kind {
        TokenKind::Keyword(Keyword::End) => break tok.end(),
        TokenKind::Keyword(Keyword::Take) => ItemKind::Take(self.comma_separated(|this| {
          let mut var = None;
          if matches!(this.scan.peek().kind, TokenKind::Ident) {
            let tok = this.scan.next();
            if matches!(this.scan.peek().kind, TokenKind::EQUAL) {
              this.scan.next();
              var = Some(Box::new(Variable {
                pos: tok.pos,
                id: 0,
                var: None,
                spelling: tok.spelling.to_owned(),
              }))
            } else {
              this.scan.undo(tok);
            }
          }
          TakeDecl { var, term: this.parse_term() }
        })),
        TokenKind::Keyword(Keyword::Hereby) => {
          let (items, end) = self.parse_proof();
          ItemKind::Thus(Statement::Now { end, label: None, items })
        }
        TokenKind::Keyword(Keyword::Hence) => ItemKind::Thus(self.parse_stmt(Some(tok.pos))),
        TokenKind::Keyword(Keyword::Thus) => {
          let link = self.parse_then();
          ItemKind::Thus(self.parse_stmt(link))
        }
        TokenKind::Keyword(Keyword::Then) if self.scan.peek().kind == Keyword::Per.into() => {
          let pos = self.scan.next().pos;
          break self.parse_per_cases(Some(tok.pos), pos, &mut items)
        }
        TokenKind::Keyword(Keyword::Per) => break self.parse_per_cases(None, tok.pos, &mut items),
        _ => self.parse_block_item(tok.pos, tok),
      };
      self.scan.accept(Keyword::Semicolon);
      items.push(Item { pos: tok.pos, kind })
    };
    (items, end)
  }

  fn parse_block_item(&mut self, pos: Position, tok: Token<'a>) -> ItemKind {
    match tok.kind {
      TokenKind::Keyword(Keyword::Let) => {
        let vars = self.parse_binders();
        let conds = if self.scan.try_accept(Keyword::Such) {
          self.scan.accept(Keyword::That);
          self.separated(Keyword::And, |this| this.parse_proposition())
        } else {
          vec![]
        };
        ItemKind::Let { vars, conds }
      }
      TokenKind::Keyword(Keyword::Given) => {
        let (vars, conds) = self.parse_choice();
        ItemKind::Given { vars, conds }
      }
      TokenKind::Keyword(Keyword::Assume) => ItemKind::Assume(self.parse_assumption(pos)),
      _ => {
        self.scan.undo(tok);
        self.parse_stmt_item()
      }
    }
  }

  fn parse_block(&mut self, kind: BlockKind) -> ItemKind {
    let mut items = vec![];
    let end = loop {
      let mut tok = self.scan.next();
      let start = tok.pos;
      let redef = match tok.kind {
        TokenKind::Keyword(Keyword::End) => break tok.end(),
        TokenKind::Pragma => {
          items.push(Item { pos: start, kind: ItemKind::Pragma(tok.spelling.to_owned().into()) });
          continue
        }
        TokenKind::Keyword(Keyword::Redefine) => {
          tok = self.scan.next();
          assert!(matches!(
            tok.kind,
            TokenKind::Keyword(Keyword::Mode | Keyword::Attr | Keyword::Func | Keyword::Pred)
          ));
          true
        }
        _ => false,
      };
      let kind = match (tok.kind, kind) {
        (TokenKind::Keyword(Keyword::Mode), BlockKind::Definition) => {
          let pat = self.parse_pattern();
          let Pattern::Mode(pat) = pat else { panic!("{:?}: expected mode pattern", pat.pos()) };
          let kind = if self.scan.try_accept(Keyword::Is) {
            DefModeKind::Expandable { expansion: self.parse_type() }
          } else {
            let spec = self.scan.try_accept(Keyword::Arrow).then(|| self.parse_type());
            DefModeKind::Standard { spec, def: None }
          };
          self.parse_definition(redef, DefinitionKind::Mode { pat, kind })
        }
        (TokenKind::Keyword(Keyword::Attr), BlockKind::Definition) => {
          let pat = self.parse_pattern();
          let Pattern::Attr(pat) = pat else { panic!("{:?}: expected attr pattern", pat.pos()) };
          self.parse_definition(redef, DefinitionKind::Attr { pat, def: None })
        }
        (TokenKind::Keyword(Keyword::Func), BlockKind::Definition) => {
          let pat = self.parse_pattern();
          let Pattern::Func(pat) = pat else { panic!("{:?}: expected func pattern", pat.pos()) };
          let spec = self.scan.try_accept(Keyword::Arrow).then(|| self.parse_type());
          self.parse_definition(redef, DefinitionKind::Func { pat, spec, def: None })
        }
        (TokenKind::Keyword(Keyword::Pred), BlockKind::Definition) => {
          let pat = self.parse_pattern();
          let Pattern::Pred(pat) = pat else { panic!("{:?}: expected pred pattern", pat.pos()) };
          self.parse_definition(redef, DefinitionKind::Pred { pat, def: None })
        }
        (TokenKind::Keyword(Keyword::Struct), BlockKind::Definition) => {
          let parents;
          if self.scan.try_accept(TokenKind::LPAREN) {
            parents = self.comma_separated(|this| *this.parse_type());
            self.scan.accept(TokenKind::RPAREN);
          } else {
            parents = vec![]
          }
          let tok = self.scan.next();
          let TokenKind::Symbol(SymbolKind::Struct(sym)) = tok.kind else {
            panic!("expected a struct symbol")
          };
          let args = if self.scan.try_accept(Keyword::Over) {
            self.comma_separated(|this| this.parse_variable())
          } else {
            vec![]
          };
          let pat = PatternStruct { sym: (sym, tok.spelling.to_owned()), args };
          self.scan.accept(Keyword::AggrLeftBrk);
          let fields = self.comma_separated(|this| {
            let pos = this.scan.peek().pos;
            let vars = this.comma_separated(|this| {
              let tok = this.scan.next();
              let TokenKind::Symbol(SymbolKind::Sel(sym)) = tok.kind else {
                panic!("expected a selector symbol")
              };
              Field { pos, sym: (sym, tok.spelling.to_owned()) }
            });
            this.scan.accept(Keyword::Arrow);
            FieldGroup { pos, vars, ty: *this.parse_type() }
          });
          self.scan.accept(Keyword::AggrRightBrk);
          self.scan.accept(Keyword::Semicolon);
          self.push_format(Format::SubAggr(pat.to_subaggr_format()));
          self.push_format(Format::Struct(pat.to_mode_format()));
          self.push_format(Format::Aggr(pat.to_aggr_format(fields.len())));
          for group in &fields {
            group.vars.iter().for_each(|f| self.push_format(Format::Sel(f.sym.0)))
          }
          ItemKind::DefStruct(Box::new(DefStruct { parents, pat, fields }))
        }
        (TokenKind::Keyword(Keyword::Synonym | Keyword::Antonym), BlockKind::Notation) => {
          let pos = tok.kind == TokenKind::Keyword(Keyword::Synonym);
          let new = self.parse_pattern();
          self.scan.accept(Keyword::For);
          let orig = self.parse_pattern();
          self.scan.accept(Keyword::Semicolon);
          ItemKind::PatternRedef(match (new, orig) {
            (Pattern::Pred(new), Pattern::Pred(orig)) => {
              self.push_format(Format::Pred(new.to_format()));
              PatternRedef::Pred { new, orig, pos }
            }
            (Pattern::Func(new), Pattern::Func(orig)) if pos => {
              self.push_format(Format::Func(new.to_format()));
              PatternRedef::Func { new, orig }
            }
            (Pattern::Mode(new), Pattern::Mode(orig)) if pos => {
              self.push_format(Format::Mode(new.to_format()));
              PatternRedef::Mode { new, orig }
            }
            (Pattern::Attr(new), Pattern::Attr(orig)) => {
              self.push_format(Format::Attr(new.to_format()));
              PatternRedef::Attr { new, orig, pos }
            }
            (Pattern::Func(_), Pattern::Func(_)) | (Pattern::Mode(_), Pattern::Mode(_)) =>
              panic!("{:?}: 'antonym' not allowed here", start),
            (_, rhs) => panic!("{:?}: pattern type mismatch", rhs.pos()),
          })
        }
        (TokenKind::Keyword(Keyword::Cluster), BlockKind::Registration) => {
          let kind = match self.parse_attrs_or_type_or_term(false, true) {
            Ok((attrs, _)) => {
              let tok = self.scan.next();
              match tok.kind {
                TokenKind::Keyword(Keyword::Arrow) => {
                  let concl = self.parse_attrs_or_type_or_term(false, false).unwrap().0;
                  self.scan.accept(Keyword::For);
                  ClusterDeclKind::Cond { antecedent: attrs, concl, ty: self.parse_type() }
                }
                TokenKind::Keyword(Keyword::For) =>
                  ClusterDeclKind::Exist { concl: attrs, ty: self.parse_type() },
                _ => panic!("{:?}: expected '->' or 'for'", tok.pos),
              }
            }
            Err(term) => {
              self.scan.accept(Keyword::Arrow);
              let concl = self.parse_attrs_or_type_or_term(false, false).unwrap().0;
              let ty = self.scan.try_accept(Keyword::For).then(|| self.parse_type());
              ClusterDeclKind::Func { term, concl, ty }
            }
          };
          self.scan.accept(Keyword::Semicolon);
          let (conds, corr) = self.parse_corr_conds();
          ItemKind::Cluster(Box::new(Cluster { kind, conds, corr }))
        }
        (TokenKind::Keyword(Keyword::Reduce), BlockKind::Registration) => {
          let from = self.parse_term();
          self.scan.accept(Keyword::To);
          let to = self.parse_term();
          self.scan.accept(Keyword::Semicolon);
          let (conds, corr) = self.parse_corr_conds();
          ItemKind::Reduction(Box::new(Reduction { from, to, conds, corr }))
        }
        (TokenKind::Keyword(Keyword::Identify), BlockKind::Registration) => {
          let lhs = self.parse_pattern();
          self.scan.accept(Keyword::With);
          let rhs = self.parse_pattern();
          let eqs = if self.scan.try_accept(Keyword::When) {
            self.comma_separated(|this| {
              let lhs = this.parse_variable();
              this.scan.accept(TokenKind::EQUAL);
              (lhs, this.parse_variable())
            })
          } else {
            vec![]
          };
          self.scan.accept(Keyword::Semicolon);
          let (conds, corr) = self.parse_corr_conds();
          match (lhs, rhs) {
            (Pattern::Func(lhs), Pattern::Func(rhs)) =>
              ItemKind::IdentifyFunc(Box::new(IdentifyFunc { lhs, rhs, eqs, conds, corr })),
            (Pattern::Pred(_), Pattern::Pred(_))
            | (Pattern::Attr(_), Pattern::Attr(_))
            | (Pattern::Mode(_), Pattern::Mode(_)) =>
              panic!("{:?}: unsupported identification type", start),
            (_, rhs) => panic!("{:?}: pattern type mismatch", rhs.pos()),
          }
        }
        (TokenKind::Property(PropertyKind::Sethood), BlockKind::Registration) => {
          self.scan.accept(Keyword::Of);
          let ty = self.parse_type();
          let just = Box::new(self.parse_justification_semi(None));
          ItemKind::SethoodRegistration { ty, just }
        }
        (TokenKind::Property(prop), BlockKind::Registration) =>
          panic!("{start:?}: illegal standalone property registration {prop:?}"),
        _ => {
          let kind = self.parse_block_item(start, tok);
          self.scan.accept(Keyword::Semicolon);
          kind
        }
      };
      items.push(Item { pos: start, kind })
    };
    self.scan.accept(Keyword::Semicolon);
    ItemKind::Block { end, kind, items }
  }

  fn parse_reservation(&mut self) -> ItemKind {
    let ress = self.comma_separated(|this| {
      let vars = this.comma_separated(|this| this.parse_variable());
      this.scan.accept(Keyword::For);
      Reservation { vars, tys: None, ty: this.parse_type(), fvars: None }
    });
    self.scan.accept(Keyword::Semicolon);
    ItemKind::Reservation(ress)
  }

  pub fn parse_items(&mut self) -> Vec<Item> {
    let mut items = vec![];
    loop {
      let tok = self.scan.next();
      let kind = match tok.kind {
        TokenKind::Pragma => ItemKind::Pragma(tok.spelling.to_owned().into()),
        TokenKind::Keyword(Keyword::Begin) => ItemKind::Section,
        TokenKind::Keyword(Keyword::Scheme) => ItemKind::SchemeBlock(self.parse_scheme()),
        TokenKind::Keyword(Keyword::Definition) => self.parse_block(BlockKind::Definition),
        TokenKind::Keyword(Keyword::Notation) => self.parse_block(BlockKind::Notation),
        TokenKind::Keyword(Keyword::Registration) => self.parse_block(BlockKind::Registration),
        TokenKind::Keyword(Keyword::Reserve) => self.parse_reservation(),
        TokenKind::Keyword(Keyword::Theorem) => ItemKind::Theorem {
          prop: Box::new(self.parse_proposition()),
          just: Box::new(self.parse_justification_semi(None)),
        },
        TokenKind::Eof => return items,
        _ => {
          self.scan.undo(tok);
          let kind = self.parse_stmt_item();
          self.scan.accept(Keyword::Semicolon);
          kind
        }
      };
      items.push(Item { pos: tok.pos, kind })
    }
  }
}