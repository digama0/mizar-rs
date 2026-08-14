use crate::ast::{SchRef, *};
use crate::parser::core::ParserCore;
use crate::types::{
  Article, ArticleAt, BlockKind, CorrCondKind, DefId, DirectiveKind, Directives, Format,
  FormatFunc, FuncSymId, LeftBrkSymId, LocusId, ModeSymId, PredSymId, PriorityKind, PropertyKind,
  RightBrkSymId, SchId, Span, StructSymId, SymbolKind, Symbols, ThmId,
};
use crate::{Diagnostic, ErrorReported, MizResult, Reporter, READ_MAX_LINE_COUNT};
use enum_map::Enum;
use indicatif::ProgressBar;
use radix_trie::{Trie, TrieCommon};
use std::collections::HashMap;
use std::sync::Arc;

/// Parser result: `Err(ErrorReported)` means a diagnostic was emitted and the
/// caller should recover at (or bubble to) the nearest synchronization point.
type PResult<T> = MizResult<T>;

/// AST nodes that can stand in as a recovered placeholder after a parse error
/// (e.g. recovering `a,,b` to `[a, <error>, b]`). Only expression nodes have a
/// dedicated error variant; other list elements recover by skipping.
trait ErrorNode {
  fn error(pos: Span) -> Self;
}
impl ErrorNode for Term {
  fn error(pos: Span) -> Self { Term::Error { pos } }
}
impl ErrorNode for Type {
  fn error(pos: Span) -> Self { Type::Error { pos } }
}
impl ErrorNode for Box<Term> {
  fn error(pos: Span) -> Self { Box::new(Term::Error { pos }) }
}
impl ErrorNode for Box<Type> {
  fn error(pos: Span) -> Self { Box::new(Type::Error { pos }) }
}
impl ErrorNode for Box<Formula> {
  fn error(pos: Span) -> Self { Box::new(Formula::Error { pos }) }
}

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
  Imports: b"imports",
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
  Unfolding: b"unfolding",
  // Wrt: b"wrt",
  Where: b"where",
  When: b"when",
  With: b"with",
}

/// Whether a diagnostic is a *syntax* failure (the parser could not proceed at the
/// current token) or a *validation* failure (the input parsed, but a construct
/// failed a condition the grammar cannot express: a pattern of the wrong kind, an
/// unresolvable infix format, a `per cases` with no cases).
///
/// The distinction is not cosmetic — it is what makes error ordering checkable.
/// A syntax error can only ever be reported at the token the parser is stuck on,
/// so syntax errors come out in strictly increasing source order. A validation
/// error is reported at the *head* of the construct it judges, which is behind any
/// error already recovered from inside that construct, so validation errors are
/// legitimately out of order. They are also bounded by one per AST node, so only
/// syntax errors can repeat unboundedly — which makes strictly-increasing syntax
/// positions a live check for non-progressing recovery. See `Scanner::err`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum DiagClass {
  Syntax,
  Validation,
}

/// How many syntax diagnostics may pile up at one offset before we call it a
/// non-advancing recovery loop. Genuine alternation produces two or three (one per
/// failed alternative); the runaway that motivated this check produced tens of
/// thousands.
#[cfg(debug_assertions)]
const MAX_SYNTAX_REPEAT: u32 = 16;

/// A syntax or well-formedness error from the `.miz` parser.
///
/// Call sites pick a variant and supply its interpolants; they never write a
/// message or a code. [`ParseErr::format`] renders the message and
/// [`ParseErr::code`] supplies the legacy Mizar number for `.err` output.
///
/// Not to be confused with [`crate::parser::ParseError`], which covers malformed
/// *XML* (dependency files and pre-accommodated artifacts).
#[derive(Debug)]
pub enum ParseErr {
  // --- syntax: reported at the token the parser is stuck on ---
  /// A specific token was required. `what` is the rendered expectation.
  Expected(ExpectedTok),
  ExpectedIdent,
  ExpectedLabel,
  ExpectedNumeral,
  ExpectedNonzeroNumeral,
  ExpectedPlaceholderIndex,
  ExpectedType,
  ExpectedAttribute,
  ExpectedFunctorSymbol,
  ExpectedPredicateSymbol,
  ExpectedFunctorOrPredicateSymbol,
  ExpectedAttrSymbol,
  ExpectedStructSymbol,
  ExpectedSelectorSymbol,
  ExpectedRightBracket,
  ExpectedCommaOrSemicolon,
  ExpectedBegin,
  ExpectedHolds,
  ExpectedPatternStart,
  ExpectedRedefKind,
  ExpectedArrowOrFor,
  ExpectedCaseOrSuppose,
  /// A symbol that exists in the vocabulary but has no format declared at this
  /// arity, so the parser cannot tell how many arguments to read.
  UnknownFormat(PatKind),
  MixedCaseSuppose,
  InvalidArticleName,

  // --- validation: reported at the head of the construct being judged ---
  BadInfixExpression,
  LinkNotAllowed,
  NoCases,
  ExpectedPattern(PatKind),
  PatternTypeMismatch,
  AntonymNotAllowed,
  UnsupportedIdentification,
  IllegalPropertyRegistration(PropertyKind),
  /// An article referenced without the corresponding environment directive.
  ArticleNotFound {
    spelling: String,
    directive: &'static str,
  },
  /// A functor/predicate application or pattern with more than 255 arguments on one
  /// side (the argument count is stored in a `u8`).
  TooManyArgs,
}

/// The kind of pattern a definition/notation item required.
#[derive(Copy, Clone, Debug)]
pub enum PatKind {
  Mode,
  Attr,
  Func,
  Pred,
  Struct,
}

impl PatKind {
  fn name(self) -> &'static str {
    match self {
      PatKind::Mode => "mode",
      PatKind::Attr => "attr",
      PatKind::Func => "func",
      PatKind::Pred => "pred",
      PatKind::Struct => "structure",
    }
  }
}

/// A token expectation, carrying enough structure for [`ParseErr::code`] to pick
/// the matching legacy code without exposing the parser's `TokenKind`.
#[derive(Debug)]
pub enum ExpectedTok {
  Semicolon,
  Of,
  For,
  Is,
  St,
  As,
  Means,
  Proof,
  That,
  Such,
  RightParen,
  RightSquare,
  RightCurly,
  /// Anything else, rendered from the token kind's `Debug`.
  Other(String),
}

impl ExpectedTok {
  fn name(&self) -> &str {
    match self {
      ExpectedTok::Semicolon => "';'",
      ExpectedTok::Of => "'of'",
      ExpectedTok::For => "'for'",
      ExpectedTok::Is => "'is'",
      ExpectedTok::St => "'st'",
      ExpectedTok::As => "'as'",
      ExpectedTok::Means => "'means'",
      ExpectedTok::Proof => "'proof'",
      ExpectedTok::That => "'that'",
      ExpectedTok::Such => "'such'",
      ExpectedTok::RightParen => "')'",
      ExpectedTok::RightSquare => "']'",
      ExpectedTok::RightCurly => "'}'",
      ExpectedTok::Other(s) => s,
    }
  }

  /// The legacy `pa*Exp` code for this expectation.
  fn code(&self) -> Option<u32> {
    Some(match self {
      ExpectedTok::Semicolon => 330, // Unexpected end of an item (perhaps ";" missing) // approximate
      ExpectedTok::Of => 256,        // "of" expected
      ExpectedTok::For => 382,       // "for" expected
      ExpectedTok::Is => 383,        // "is" expected
      ExpectedTok::St => 387,        // "st" expected
      ExpectedTok::As => 388,        // "as" expected
      ExpectedTok::Means => 386,     // "means" or "equals" expected // approximate
      ExpectedTok::Proof => 389,     // "proof" expected
      ExpectedTok::That => 350,      // "that" expected
      ExpectedTok::Such => 403,      // "such" expected
      ExpectedTok::RightParen => 370, // ")" expected
      ExpectedTok::RightSquare => 371, // "]" expected
      ExpectedTok::RightCurly => 372, // "}" expected
      ExpectedTok::Other(_) => return None,
    })
  }
}

impl ParseErr {
  /// See [`DiagClass`]. Derived from the variant, so it cannot drift from the
  /// position a call site actually passes.
  pub fn class(&self) -> DiagClass {
    match self {
      ParseErr::BadInfixExpression
      | ParseErr::LinkNotAllowed
      | ParseErr::NoCases
      | ParseErr::ExpectedPattern(_)
      | ParseErr::PatternTypeMismatch
      | ParseErr::AntonymNotAllowed
      | ParseErr::UnsupportedIdentification
      | ParseErr::IllegalPropertyRegistration(_)
      | ParseErr::UnknownFormat(_)
      | ParseErr::ArticleNotFound { .. } => DiagClass::Validation,
      _ => DiagClass::Syntax,
    }
  }

  /// The legacy Mizar error number from `mizar.msg`, where one corresponds.
  ///
  /// Named after the constant in the Pascal parser (`base/parser.pas:27-148`).
  /// Many-to-one is expected: Mizar itself names each *site*
  /// (`paIdentExp1`..`paIdentExp13`) but collapses them onto one code (300).
  /// `None` means we report something Mizar has no code for.
  pub fn code(&self) -> Option<u32> {
    Some(match self {
      ParseErr::Expected(e) => return e.code(),
      ParseErr::ExpectedIdent => 300,   // Identifier expected
      ParseErr::ExpectedLabel => 300,   // Identifier expected // approximate
      ParseErr::ExpectedNumeral => 307, // Numeral expected
      ParseErr::ExpectedPlaceholderIndex => 307, // Numeral expected // approximate
      ParseErr::ExpectedNonzeroNumeral => 146, // Theorem number must be > 0 // approximate
      ParseErr::ExpectedType => 398,    // Type expected
      ParseErr::ExpectedAttribute => 306, // Attribute symbol expected // approximate
      ParseErr::ExpectedAttrSymbol => 306, // Attribute symbol expected
      ParseErr::ExpectedFunctorSymbol => 302, // Functor symbol expected
      ParseErr::ExpectedPredicateSymbol => 301, // Predicate symbol expected
      ParseErr::ExpectedFunctorOrPredicateSymbol => 314, // Incorrect beginning of a pattern // approximate
      ParseErr::ExpectedStructSymbol => 304,             // Structure symbol expected
      ParseErr::ExpectedSelectorSymbol => 305,           // Selector symbol expected
      ParseErr::ExpectedRightBracket => 311, // Paired functor brackets must be of the same kind // approximate
      ParseErr::ExpectedCommaOrSemicolon => 330, // Unexpected end of an item // approximate
      ParseErr::ExpectedBegin => 213,        // "begin" missing
      ParseErr::ExpectedHolds => 340,        // "holds", "for" or "ex" expected // approximate
      ParseErr::ExpectedPatternStart => 314, // Incorrect beginning of a pattern
      ParseErr::ExpectedRedefKind => 314,    // Incorrect beginning of a pattern // approximate
      ParseErr::ExpectedArrowOrFor => 406,   // "for" or "->" expected
      ParseErr::ExpectedCaseOrSuppose => 232, // "case" or "suppose" expected
      ParseErr::UnknownFormat(k) => match k {
        PatKind::Mode => 151,   // Unknown mode format
        PatKind::Pred => 153,   // Unknown predicate format
        PatKind::Func => 165,   // Unknown functor format
        PatKind::Attr => 175,   // Unknown attribute format
        PatKind::Struct => 176, // Unknown structure format
      },
      ParseErr::MixedCaseSuppose => 58, // Mixing "case" with "suppose" is not allowed ...
      ParseErr::InvalidArticleName => 391, // Incorrect beginning of a text item // approximate
      ParseErr::BadInfixExpression => 397, // Term expected // approximate
      ParseErr::LinkNotAllowed => 164,  // Nothing to link // approximate
      ParseErr::NoCases => 351,         // "cases" expected // approximate
      ParseErr::ExpectedPattern(_) => 314, // Incorrect beginning of a pattern // approximate
      ParseErr::PatternTypeMismatch => 273, // "redefine" is not allowed here // approximate
      ParseErr::AntonymNotAllowed => 198, // It is meaningless to define an antonym to a functor or a mode
      ParseErr::UnsupportedIdentification => 400, // Still not implemented // approximate
      ParseErr::IllegalPropertyRegistration(_) => 400, // Still not implemented // approximate
      ParseErr::ArticleNotFound { .. } => 191, // Check if scheme is in "schemes" ... // approximate
      ParseErr::TooManyArgs => return None, // no legacy counterpart (a u8-arity limit)
    })
  }

  /// The human-readable message.
  pub fn format(&self) -> String {
    match self {
      ParseErr::Expected(e) => format!("expected {}", e.name()),
      ParseErr::ExpectedIdent => "expected identifier".to_string(),
      ParseErr::ExpectedLabel => "expected label".to_string(),
      ParseErr::ExpectedNumeral => "expected numeral".to_string(),
      ParseErr::ExpectedNonzeroNumeral => "expected nonzero numeral".to_string(),
      ParseErr::ExpectedPlaceholderIndex =>
        "expected a placeholder index like '$1' or '$2'".to_string(),
      ParseErr::ExpectedType => "expected type".to_string(),
      ParseErr::ExpectedAttribute => "expected attribute".to_string(),
      ParseErr::ExpectedFunctorSymbol => "expected functor symbol".to_string(),
      ParseErr::ExpectedPredicateSymbol => "expected predicate symbol".to_string(),
      ParseErr::ExpectedFunctorOrPredicateSymbol =>
        "expected functor or predicate symbol".to_string(),
      ParseErr::ExpectedAttrSymbol => "expected an attribute symbol".to_string(),
      ParseErr::ExpectedStructSymbol => "expected a structure symbol".to_string(),
      ParseErr::ExpectedSelectorSymbol => "expected a selector symbol".to_string(),
      ParseErr::ExpectedRightBracket => "expected a closing bracket symbol".to_string(),
      ParseErr::ExpectedCommaOrSemicolon => "expected ',' or ';'".to_string(),
      ParseErr::ExpectedBegin => "expected 'begin' to start the text proper".to_string(),
      ParseErr::ExpectedHolds => "expected 'holds' after the quantifier".to_string(),
      ParseErr::ExpectedPatternStart =>
        "expected the start of a pattern: ',', '[', or '{'".to_string(),
      ParseErr::ExpectedRedefKind =>
        "expected the kind being redefined: 'mode', 'attr', 'func', or 'pred'".to_string(),
      ParseErr::ExpectedArrowOrFor => "expected '->' or 'for'".to_string(),
      ParseErr::ExpectedCaseOrSuppose => "expected 'case' or 'suppose'".to_string(),
      ParseErr::UnknownFormat(k) =>
        format!("no {} notation with this symbol and argument count has been declared", k.name()),
      ParseErr::MixedCaseSuppose =>
        "a 'per cases' block cannot mix 'case' and 'suppose'; use one or the other".to_string(),
      ParseErr::InvalidArticleName => "not a valid article name".to_string(),
      ParseErr::BadInfixExpression =>
        "could not parse this expression: the symbols do not form a valid term (check the \
         notation and bracketing)"
          .to_string(),
      ParseErr::LinkNotAllowed =>
        "'then' cannot appear here: it must follow a statement in the same reasoning".to_string(),
      ParseErr::NoCases =>
        "a 'per cases' block must contain at least one 'case' or 'suppose'".to_string(),
      ParseErr::ExpectedPattern(k) => format!("expected a {} pattern here", k.name()),
      ParseErr::PatternTypeMismatch =>
        "the two sides are different kinds of pattern (e.g. a functor and a predicate)".to_string(),
      ParseErr::AntonymNotAllowed =>
        "'antonym' can only be declared for a predicate or attribute, not a functor or mode"
          .to_string(),
      ParseErr::UnsupportedIdentification =>
        "'identify' is only supported between two functor patterns".to_string(),
      ParseErr::IllegalPropertyRegistration(prop) =>
        format!("the {prop:?} property cannot be registered on its own here"),
      ParseErr::ArticleNotFound { spelling, directive } => format!(
        "no imported article named '{spelling}'; did you forget to list it in your \
         '{directive}' directive?"
      ),
      ParseErr::TooManyArgs =>
        "too many arguments here: at most 255 are allowed on one side".to_string(),
    }
  }
}

impl std::fmt::Display for ParseErr {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { f.write_str(&self.format()) }
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
  pos: Span,
  kind: TokenKind,
}

impl<'a> Token<'a> {
  /// A zero-width span at the byte offset just past this token.
  fn end(&self) -> Span { Span::at(self.pos.end) }
}

struct Scanner<'a> {
  /// Start offset of the last *syntax* diagnostic and how many consecutive ones
  /// have landed there, for the ordering check in [`Scanner::err`].
  last_syntax: std::cell::Cell<(u32, u32)>,
  data: &'a [u8],
  /// Byte offset of the start of the current line, used to detect `::$` pragmas
  /// (which must begin a line).
  line_start: usize,
  pos: usize,
  allow_underscore: bool,
  phrase_end: Option<usize>,
  tokens: Trie<Vec<u8>, TokenKind>,
  lookahead: Option<Token<'a>>,
  lookahead2: Option<Token<'a>>,
  reporter: Arc<dyn Reporter>,
}

impl<'a> Scanner<'a> {
  fn new(data: &'a [u8], progress: Option<&ProgressBar>, reporter: Arc<dyn Reporter>) -> Self {
    let mut tokens = Trie::default();
    let mut push1 = |cc: &[u8], kind| assert!(tokens.insert(cc.to_owned(), kind).is_none());
    push1(b"$", TokenKind::Dollar(0));
    for &(s, kind) in KEYWORDS {
      push1(s, TokenKind::Keyword(kind))
    }
    for prop in (0..PropertyKind::LENGTH).map(PropertyKind::from_usize) {
      // 'abstractness' is not a keyword
      if prop != PropertyKind::Abstractness {
        push1(prop.to_lower(), TokenKind::Property(prop))
      }
    }
    for cc in (0..CorrCondKind::LENGTH).map(CorrCondKind::from_usize) {
      push1(cc.name(), TokenKind::CorrCond(cc))
    }
    for dir in (0..DirectiveKind::LENGTH).map(DirectiveKind::from_usize) {
      push1(dir.name().as_bytes(), TokenKind::Directive(dir))
    }
    if READ_MAX_LINE_COUNT {
      if let Some(progress) = progress {
        progress.set_length(bytecount::count(data, b'\n') as u64 + 1)
      }
    }
    Self {
      last_syntax: Default::default(),
      data,
      line_start: 0,
      pos: 0,
      phrase_end: None,
      allow_underscore: true,
      tokens,
      lookahead: None,
      lookahead2: None,
      reporter,
    }
  }

  /// Report a parse error and return the [`ErrorReported`] token to bubble to
  /// the nearest recovery point. See `notes/error-handling.md`.
  fn err(&self, span: Span, msg: impl Into<crate::error::DiagKind>) -> ErrorReported {
    let kind = msg.into();
    // Syntax positions must not go *backwards*: a syntax error can only be
    // reported at the token the parser is stuck on, and the scanner only moves
    // forward. Validation errors are exempt by construction — they sit at the head
    // of the construct they judge, which is behind anything recovered from inside
    // it.
    //
    // Equal positions are legitimate and do happen: `accept` reports at a token and
    // then `undo`s it, so an enclosing alternative can fail at the same offset
    // (`for x being Element of {}` gives "expected attribute" then "expected
    // 'holds'", both at the same byte). What is *not* legitimate is an unbounded
    // run of them — that is the shape that once spun forever on a stray `end;`,
    // re-reporting at one offset without end. So bound the run instead of
    // forbidding repeats.
    #[cfg(debug_assertions)]
    if let crate::error::DiagKind::Parse(e) = &kind {
      if e.class() == DiagClass::Syntax && !span.is_none() {
        let (last, run) = self.last_syntax.get();
        debug_assert!(
          span.start >= last,
          "syntax diagnostics must not go backwards: {last} then {} ({e:?})",
          span.start
        );
        let run = if span.start == last { run + 1 } else { 0 };
        debug_assert!(
          run < MAX_SYNTAX_REPEAT,
          "{run} syntax diagnostics at offset {} ({e:?}): recovery is not advancing",
          span.start
        );
        self.last_syntax.set((span.start, run));
      }
    }
    self.reporter.error(Diagnostic::error(span, kind))
  }

  /// The current byte offset.
  fn pos(&self) -> u32 { self.pos as u32 }

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
        return Token { spelling, pos: Span::new(pos, self.pos as u32), kind }
      }
      loop {
        let Some(&c) = self.data.get(self.pos) else {
          return Token { spelling: "", pos: Span::at(self.pos()), kind: TokenKind::Eof }
        };
        if c == b' ' {
          self.pos += 1;
          continue
        }
        if c == b'\n' {
          self.pos += 1;
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
              self.line_start = self.pos;
              &self.data[start..][..len + 3]
            } else {
              self.pos = self.data.len();
              &self.data[start..]
            };
            let spelling = std::str::from_utf8(spelling).unwrap();
            return Token { spelling, pos: Span::new(pos, self.pos as u32), kind: TokenKind::Pragma }
          }
          self.pos += 2;
          match memchr::memchr(b'\n', &self.data[self.pos..]) {
            Some(x) => self.pos += x + 1,
            None => self.pos = self.data.len(),
          }
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

  fn accept(&mut self, kind: impl Into<TokenKind>) -> PResult<Token<'a>> {
    let kind = kind.into();
    let tok = self.next();
    if tok.kind == kind {
      Ok(tok)
    } else {
      // Leave the unexpected token in place so the enclosing recovery point can
      // resynchronize on it (e.g. a `;` or block keyword).
      let (pos, msg) = (tok.pos, expected_err(kind));
      self.undo(tok);
      Err(self.err(pos, msg))
    }
  }

  fn try_accept(&mut self, kind: impl Into<TokenKind>) -> bool {
    self.next_if(|tok| tok.kind == kind.into()).is_some()
  }
}

/// The [`ParseErr`] for a failed token expectation. Specific variants where a
/// legacy code exists, `Expected(Other(..))` otherwise (preserving the old
/// `expected {kind:?}` rendering).
fn expected_err(kind: TokenKind) -> ParseErr {
  let other = || ParseErr::Expected(ExpectedTok::Other(format!("{kind:?}")));
  if kind == TokenKind::RPAREN {
    return ParseErr::Expected(ExpectedTok::RightParen)
  } else if kind == TokenKind::RBRACK {
    return ParseErr::Expected(ExpectedTok::RightSquare)
  } else if kind == TokenKind::RBRACE {
    return ParseErr::Expected(ExpectedTok::RightCurly)
  }
  match kind {
    TokenKind::Ident => ParseErr::ExpectedIdent,
    TokenKind::Keyword(kw) => ParseErr::Expected(match kw {
      Keyword::Semicolon => ExpectedTok::Semicolon,
      Keyword::Of => ExpectedTok::Of,
      Keyword::For => ExpectedTok::For,
      Keyword::Is => ExpectedTok::Is,
      Keyword::St => ExpectedTok::St,
      Keyword::As => ExpectedTok::As,
      Keyword::Means => ExpectedTok::Means,
      Keyword::Proof => ExpectedTok::Proof,
      Keyword::That => ExpectedTok::That,
      Keyword::Such => ExpectedTok::Such,
      _ => return other(),
    }),
    _ => other(),
  }
}

pub struct MizParser<'a> {
  scan: Scanner<'a>,
  pub core: ParserCore,
  allow_internal_selector: bool,
  max_mode_args: HashMap<ModeSymId, u8>,
  max_struct_args: HashMap<StructSymId, u8>,
  max_pred_rhs: HashMap<PredSymId, u8>,
}

impl<'a> MizParser<'a> {
  pub fn new(core: ParserCore, progress: Option<&ProgressBar>, data: &'a [u8]) -> Self {
    Self {
      scan: Scanner::new(data, progress, core.reporter.clone()),
      core,
      allow_internal_selector: false,
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

  pub fn load_symbols(
    &mut self, syms: &Symbols, infinitives: &[(PredSymId, &str)], prio: &[(PriorityKind, u32)],
  ) {
    ParserCore::on_symbols(syms, infinitives, |kind, s| {
      assert!(self.scan.tokens.insert(s.as_bytes().to_owned(), TokenKind::Symbol(kind)).is_none())
    });
    self.core.load_prio(prio);
  }

  pub fn push_format(&mut self, pos: Span, fmt: Format) {
    if self.core.push_format(pos, fmt) {
      self.read_format(&fmt);
    }
  }

  fn parse_article(&mut self, tok: Token<'a>) -> PResult<Article> {
    match Article::from_upper(tok.spelling.as_bytes()) {
      Ok(art) => Ok(art),
      Err(_) => Err(self.scan.err(tok.pos, ParseErr::InvalidArticleName)),
    }
  }

  /// Returns `true` if the environment was fatally malformed (the caller should
  /// abandon the article). The `.miz` parser always recovers, so it returns `false`;
  /// this exists for the shared [`Parser::parse_env`] dispatch (see the JSON parser).
  pub fn parse_env(&mut self, dirs: &mut Directives) -> bool {
    let hidden = ArticleAt { pos: Span::default(), art: Article::HIDDEN };
    dirs.0[DirectiveKind::Vocabularies].push(hidden);
    dirs.0[DirectiveKind::Notations].push(hidden);
    dirs.0[DirectiveKind::Constructors].push(hidden);
    dirs.0[DirectiveKind::Requirements].push(hidden);
    let _ = self.scan.accept(Keyword::Environ);
    'env: loop {
      let tok = self.scan.next();
      match tok.kind {
        TokenKind::Directive(_) | TokenKind::Keyword(Keyword::Imports) => loop {
          let id = match self.scan.accept(TokenKind::Ident) {
            Ok(id) => id,
            Err(_) => break 'env,
          };
          let art = match self.parse_article(id) {
            Ok(art) => ArticleAt { pos: id.pos, art },
            Err(_) => break 'env,
          };
          match tok.kind {
            TokenKind::Directive(dir) => dirs.0[dir].push(art),
            TokenKind::Keyword(Keyword::Imports) =>
              for &dir in DirectiveKind::IMPORTED {
                dirs.0[dir].push(art)
              },
            _ => unreachable!(),
          }
          let tok = self.scan.next();
          match tok.kind {
            TokenKind::Keyword(Keyword::Comma) => {}
            TokenKind::Keyword(Keyword::Semicolon) => break,
            _ => {
              self.scan.err(tok.pos, ParseErr::ExpectedCommaOrSemicolon);
              break 'env
            }
          }
        },
        TokenKind::Keyword(Keyword::Begin) => break,
        _ => {
          self.scan.err(tok.pos, ParseErr::ExpectedBegin);
          break
        }
      }
    }
    self.scan.allow_underscore = false;
    self.core.write_json.on(|w| w.write_env(dirs));
    false
  }

  fn parse_variable(&mut self) -> PResult<Variable> {
    let tok = self.scan.accept(TokenKind::Ident)?;
    Ok(Variable { pos: tok.pos, var: None, spelling: tok.spelling.into() })
  }

  fn parse_label(&mut self) -> Option<Box<Label>> {
    if !matches!(self.scan.peek().kind, TokenKind::Ident) {
      return None
    }
    let tok = self.scan.next();
    if matches!(self.scan.peek().kind, TokenKind::Keyword(Keyword::Colon)) {
      self.scan.next();
      Some(Box::new(Label { pos: tok.pos, id: None, spelling: tok.spelling.into() }))
    } else {
      self.scan.undo(tok);
      None
    }
  }

  /// Skip tokens until the next token is the separator `sep` or a hard
  /// block/statement/EOF boundary, without consuming it.
  ///
  /// Note this does *not* by itself guarantee progress: if the failing parse was
  /// already sitting on a boundary, nothing is skipped. Looping callers that do
  /// not unconditionally consume a token per iteration must follow up with
  /// [`Self::ensure_progress`].
  fn recover_to(&mut self, sep: Keyword) {
    loop {
      match self.scan.peek().kind {
        TokenKind::Eof | TokenKind::Keyword(Keyword::Semicolon | Keyword::End | Keyword::Begin) =>
          break,
        TokenKind::Keyword(k) if k == sep => break,
        _ => {
          self.scan.next();
        }
      }
    }
  }

  /// Skip tokens up to and including the next `close` token, or stop (without
  /// consuming) at a hard `;`/`end`/`begin`/EOF boundary. Bounds a bracketed
  /// group after a parse error.
  fn recover_past(&mut self, close: TokenKind) {
    loop {
      match self.scan.peek().kind {
        TokenKind::Eof | TokenKind::Keyword(Keyword::Semicolon | Keyword::End | Keyword::Begin) =>
          break,
        k if k == close => {
          self.scan.next();
          break
        }
        _ => {
          self.scan.next();
        }
      }
    }
  }

  /// Force forward progress after a failed item that began at offset `start`.
  ///
  /// A parse that consumed its first token and then [`Scanner::undo`]s it can
  /// fail while positioned right back at that token; if it is a hard boundary,
  /// `recover_to` skips nothing and the scanner is exactly where the item began.
  /// A caller that re-reads from there loops forever on the same token, emitting
  /// the same diagnostic each time (a stray `end;` at top level did this: `end`
  /// starts no item, and at top level closes no block). Dropping one token is
  /// enough to break it, and is a no-op whenever recovery already advanced.
  ///
  /// Returns whether a token was dropped.
  fn ensure_progress(&mut self, start: u32) -> bool {
    let tok = self.scan.peek();
    if !matches!(tok.kind, TokenKind::Eof) && tok.pos.start <= start {
      self.scan.next();
      return true
    }
    false
  }

  /// Parse one item inside a block/proof body via `f`; on failure (a diagnostic
  /// was already reported) resynchronize to the next `;` and yield
  /// `ItemKind::Error`, so the rest of the block still parses. This is the
  /// nested recovery point, analogous to `push_parse_item` at the top level.
  fn recover_block_item(
    &mut self, start: u32, f: impl FnOnce(&mut Self) -> PResult<ItemKind>,
  ) -> ItemKind {
    match f(self) {
      Ok(kind) => kind,
      Err(_) => {
        self.recover_to(Keyword::Semicolon);
        self.scan.try_accept(Keyword::Semicolon);
        // Force forward progress (as `push_parse_item` does at top level): a leaf parser
        // can `undo` the offending token back onto a hard boundary (e.g. `begin`) that
        // `recover_to` refuses to pass, leaving the enclosing block/proof loop to re-read
        // the same token forever (the MAX_SYNTAX_REPEAT stall). Drop one token to break it.
        if self.ensure_progress(start) {
          self.scan.try_accept(Keyword::Semicolon);
        }
        ItemKind::Error
      }
    }
  }

  /// A `sep`-separated list where a failed element becomes an error placeholder
  /// (recovering `a,,b` to `[a, <error>, b]`).
  fn separated<T: ErrorNode>(
    &mut self, kw: Keyword, mut f: impl FnMut(&mut Self) -> PResult<T>,
  ) -> Vec<T> {
    let mut out = vec![];
    loop {
      match f(self) {
        Ok(t) => out.push(t),
        Err(_) => {
          out.push(T::error(self.scan.peek().pos));
          self.recover_to(kw);
        }
      }
      if self.scan.peek().kind != TokenKind::Keyword(kw) {
        break
      }
      self.scan.next();
    }
    out
  }

  fn comma_separated<T: ErrorNode>(&mut self, f: impl FnMut(&mut Self) -> PResult<T>) -> Vec<T> {
    self.separated(Keyword::Comma, f)
  }

  /// A `sep`-separated list where a failed element is skipped rather than
  /// replaced by a placeholder (for element types without an error variant).
  fn separated_skip<T>(
    &mut self, kw: Keyword, mut f: impl FnMut(&mut Self) -> PResult<T>,
  ) -> Vec<T> {
    let mut out = vec![];
    loop {
      match f(self) {
        Ok(t) => out.push(t),
        Err(_) => self.recover_to(kw),
      }
      if self.scan.peek().kind != TokenKind::Keyword(kw) {
        break
      }
      self.scan.next();
    }
    out
  }

  fn comma_separated_skip<T>(&mut self, f: impl FnMut(&mut Self) -> PResult<T>) -> Vec<T> {
    self.separated_skip(Keyword::Comma, f)
  }

  fn comma_separated_upto<T: ErrorNode>(
    &mut self, mut max: u8, mut f: impl FnMut(&mut Self) -> PResult<T>,
  ) -> Vec<T> {
    let mut out = vec![];
    loop {
      match f(self) {
        Ok(t) => out.push(t),
        Err(_) => {
          out.push(T::error(self.scan.peek().pos));
          self.recover_to(Keyword::Comma);
        }
      }
      max -= 1;
      if max == 0 || !self.scan.try_accept(Keyword::Comma) {
        break
      }
    }
    out
  }

  fn parse_terms(&mut self) -> Vec<Term> {
    self.comma_separated(|this| this.parse_term().map(|t| *t))
  }

  fn parse_term_hi(&mut self) -> PResult<Option<Box<Term>>> {
    let tok = self.scan.next();
    Ok(Some(match tok.kind {
      TokenKind::LPAREN => match (|| -> PResult<Box<Term>> {
        let t = self.parse_term()?;
        self.scan.accept(TokenKind::RPAREN)?;
        Ok(t)
      })() {
        Ok(t) => t,
        Err(_) => {
          self.recover_past(TokenKind::RPAREN);
          Box::new(Term::Error { pos: tok.pos })
        }
      },
      TokenKind::Ident =>
        if self.scan.try_accept(TokenKind::LPAREN) {
          match (|| -> PResult<Vec<Term>> {
            let args =
              if self.scan.peek().kind == TokenKind::RPAREN { vec![] } else { self.parse_terms() };
            self.scan.accept(TokenKind::RPAREN)?;
            Ok(args)
          })() {
            Ok(args) => Box::new(Term::PrivFunc {
              pos: tok.pos,
              kind: None,
              spelling: tok.spelling.into(),
              args,
            }),
            Err(_) => {
              self.recover_past(TokenKind::RPAREN);
              Box::new(Term::Error { pos: tok.pos })
            }
          }
        } else {
          Box::new(Term::Var { pos: tok.pos, kind: None, spelling: tok.spelling.to_owned() })
        },
      TokenKind::Number(value) => Box::new(Term::Numeral { pos: tok.pos, value }),
      TokenKind::Keyword(Keyword::It) => Box::new(Term::It { pos: tok.pos }),
      TokenKind::Dollar(nr) => {
        let nr = match nr.checked_sub(1).and_then(|n| n.try_into().ok()) {
          Some(nr) => nr,
          None => return Err(self.scan.err(tok.pos, ParseErr::ExpectedPlaceholderIndex)),
        };
        Box::new(Term::Placeholder { pos: tok.pos, nr: LocusId(nr) })
      }
      TokenKind::Symbol(SymbolKind::Struct(sym)) if self.scan.try_accept(Keyword::AggrLeftBrk) =>
        match (|| -> PResult<Vec<Term>> {
          let args = self.parse_terms();
          self.scan.accept(Keyword::AggrRightBrk)?;
          Ok(args)
        })() {
          Ok(args) =>
            Box::new(Term::Aggregate { pos: tok.pos, sym, spelling: tok.spelling.to_owned(), args }),
          Err(_) => {
            self.recover_past(TokenKind::Keyword(Keyword::AggrRightBrk));
            Box::new(Term::Error { pos: tok.pos })
          }
        },
      TokenKind::Symbol(SymbolKind::LeftBrk(lsym)) => {
        let args = self.parse_terms();
        let tok2 = self.scan.next();
        if lsym == LeftBrkSymId::LBRACE
          && args.len() == 1
          && matches!(tok2.kind, TokenKind::Keyword(Keyword::Colon | Keyword::Where))
        {
          let scope = Box::new({ args }.pop().unwrap());
          let is_where = tok2.kind == Keyword::Where.into();
          match (|| -> PResult<Box<Term>> {
            let vars = if is_where {
              let vars = self.parse_where()?;
              self.scan.accept(Keyword::Colon)?;
              vars
            } else {
              vec![]
            };
            let compr = Some(self.parse_formula()?);
            self.scan.accept(TokenKind::RBRACE)?;
            Ok(Box::new(Term::Fraenkel { pos: tok.pos, vars, scope, compr, nameck: None }))
          })() {
            Ok(t) => t,
            Err(_) => {
              self.recover_past(TokenKind::RBRACE);
              Box::new(Term::Error { pos: tok.pos })
            }
          }
        } else {
          let lspelling = tok.spelling.to_owned();
          let TokenKind::Symbol(SymbolKind::RightBrk(rsym)) = tok2.kind else {
            self.scan.undo(tok2);
            return Err(self.scan.err(tok2.pos, ParseErr::ExpectedRightBracket))
          };
          let rspelling = tok2.spelling.to_owned();
          Box::new(Term::Bracket { pos: tok.pos, lsym, lspelling, rsym, rspelling, args })
        }
      }
      TokenKind::Keyword(Keyword::The) => {
        let tok2 = self.scan.next();
        match tok2.kind {
          TokenKind::Symbol(SymbolKind::Sel(sym)) => {
            let spelling = tok2.spelling.to_owned();
            if self.scan.try_accept(Keyword::Of) {
              Box::new(Term::Selector { pos: tok.pos, sym, spelling, arg: self.parse_term()? })
            } else if self.allow_internal_selector {
              Box::new(Term::InternalSelector { pos: tok.pos, sym, spelling, id: None })
            } else {
              let pos = self.scan.peek().pos;
              return Err(self.scan.err(pos, ParseErr::Expected(ExpectedTok::Of)))
            }
          }
          TokenKind::Symbol(SymbolKind::Struct(sym)) if self.scan.try_accept(Keyword::Of) => {
            let spelling = tok2.spelling.to_owned();
            Box::new(Term::SubAggr { pos: tok.pos, sym, spelling, arg: self.parse_term()? })
          }
          TokenKind::SET if self.scan.try_accept(Keyword::Of) => {
            self.scan.accept(Keyword::All)?;
            let scope = self.parse_term()?;
            let vars =
              if self.scan.try_accept(Keyword::Where) { self.parse_where()? } else { vec![] };
            Box::new(Term::Fraenkel { pos: tok.pos, vars, scope, compr: None, nameck: None })
          }
          _ => {
            self.scan.undo(tok2);
            Box::new(Term::The { pos: tok.pos, ty: self.parse_type()? })
          }
        }
      }
      _ => {
        self.scan.undo(tok);
        return Ok(None)
      }
    }))
  }
}

#[derive(Debug)]
struct TermElem<'a> {
  lhs: Vec<Term>,
  pos: Span,
  sym: FuncSymId,
  spelling: &'a str,
  prio: u32,
  parent: usize,
  to_right: bool,
}

#[derive(Debug)]
struct LongTermBuilder<'a> {
  stack: Vec<TermElem<'a>>,
  rhs: Vec<Term>,
  fast_path: Result<(), Span>,
}

impl<'a> LongTermBuilder<'a> {
  fn new(rhs: Vec<Term>) -> Self { Self { stack: vec![], rhs, fast_path: Ok(()) } }

  fn push(&mut self, p: &MizParser<'a>, tok: Token<'a>, args: Vec<Term>) {
    let TokenKind::Symbol(SymbolKind::Func(sym)) = tok.kind else { unreachable!() };
    // No declared format for this symbol: there is no way to report from here (this
    // returns `()`), but the chain already has a channel for "cannot take the fast
    // path", and the slow path reports `BadInfixExpression` at this position.
    let prio = match p.core.func_prio.get(&sym) {
      Some(&prio) => prio,
      None => {
        self.fast_path = Err(tok.pos);
        0
      }
    };
    let lhs = std::mem::replace(&mut self.rhs, args);
    let mut right = lhs.len() as u8;
    let mut parent = self.stack.len();
    if self.fast_path.is_ok() {
      while parent != 0 {
        let elem = &self.stack[parent - 1];
        if elem.prio < prio {
          break
        }
        let left = if parent - 1 == elem.parent { elem.lhs.len() as u8 } else { 1 };
        let fmt = FormatFunc::Func { sym: elem.sym, left, right };
        if !p.core.format_lookup.contains_key(&Format::Func(fmt)) {
          self.fast_path = Err(elem.pos);
          break
        }
        parent = elem.parent;
        right = 1;
      }
    }
    let Token { pos, spelling, .. } = tok;
    self.stack.push(TermElem { lhs, pos, sym, spelling, prio, parent, to_right: true });
  }

  fn accum_left(stack: &mut [TermElem<'a>], lo: usize, mut hi: usize, rhs: &mut Vec<Term>) {
    while lo < hi {
      let i = hi - 1;
      let TermElem { ref mut lhs, pos, sym, spelling, parent, .. } = stack[i];
      let mut args = std::mem::take(lhs);
      let left = args.len() as u8;
      args.append(rhs);
      rhs.push(Term::Infix { pos, sym, spelling: spelling.to_owned(), left, args });
      hi = parent
    }
  }

  fn valid(&self, p: &MizParser<'a>, i: usize) -> bool {
    let sym = self.stack[i].sym;
    let left = if self.stack[i].to_right { self.stack[i].lhs.len() as u8 } else { 1 };
    let right = if self.stack.get(i + 1).is_some_and(|elem| elem.to_right) {
      1
    } else {
      self.stack.get(i + 1).map_or(&self.rhs, |elem| &elem.lhs).len() as u8
    };
    p.core.format_lookup.contains_key(&Format::Func(FormatFunc::Func { sym, left, right }))
  }

  fn rebalance(&mut self, p: &MizParser) -> PResult<()> {
    for k in 1..self.stack.len() {
      self.stack[k].to_right = self.stack[k - 1].prio < self.stack[k].prio;
    }
    let mut bl = if self.valid(p, 0) {
      0
    } else {
      self.stack[1].to_right ^= true;
      if !self.valid(p, 0) {
        return Err(p.scan.err(self.stack[0].pos, ParseErr::BadInfixExpression))
      }
      1
    };
    'next: for k in 1..self.stack.len() - 1 {
      if !self.valid(p, k) {
        self.stack[k + 1].to_right ^= true;
        if !self.valid(p, k) {
          if bl == k {
            return Err(p.scan.err(self.stack[k].pos, ParseErr::BadInfixExpression))
          }
          self.stack[k + 1].to_right ^= true;
          self.stack[k].to_right ^= true;
          let bl2 = if self.valid(p, k) {
            k
          } else {
            self.stack[k + 1].to_right ^= true;
            if !self.valid(p, k) {
              return Err(p.scan.err(self.stack[k].pos, ParseErr::BadInfixExpression))
            }
            k + 1
          };
          for j in (bl + 1..k).rev() {
            if self.valid(p, j) {
              continue 'next
            }
            self.stack[j].to_right ^= true;
            if !self.valid(p, j) {
              return Err(p.scan.err(self.stack[k].pos, ParseErr::BadInfixExpression))
            }
          }
          if !self.valid(p, bl) {
            return Err(p.scan.err(self.stack[k].pos, ParseErr::BadInfixExpression))
          }
          bl = bl2;
        }
      }
    }
    for j in (bl + 1..self.stack.len()).rev() {
      if self.valid(p, j) {
        return Ok(())
      }
      self.stack[j].to_right ^= true;
      if !self.valid(p, j) {
        return Err(p.scan.err(self.stack.last().unwrap().pos, ParseErr::BadInfixExpression))
      }
    }
    if !self.valid(p, bl) {
      return Err(p.scan.err(self.stack.last().unwrap().pos, ParseErr::BadInfixExpression))
    }
    Ok(())
  }

  #[cold]
  fn slow_path(&mut self, p: &MizParser<'a>) -> PResult<()> {
    self.rebalance(p)?;
    for i in 1..self.stack.len() {
      let mut parent = i;
      if !self.stack[i].to_right {
        parent = self.stack[i - 1].parent;
        while parent != 0 {
          let elem = &self.stack[parent - 1];
          if elem.prio < self.stack[i].prio {
            break
          }
          parent = elem.parent;
        }
      }
      self.stack[i].parent = parent;
    }
    for i in 0..self.stack.len() {
      // Invariant of the rebalanced stack (not user-reachable): each element points to
      // itself as parent iff it associates to the right.
      debug_assert!(self.stack[i].to_right == (self.stack[i].parent == i));
    }
    Ok(())
  }

  fn finish(mut self, p: &MizParser<'a>) -> PResult<Vec<Term>> {
    if self.fast_path.is_ok() {
      let mut parent = self.stack.len();
      let mut right = self.rhs.len() as u8;
      while parent != 0 {
        let elem = &self.stack[parent - 1];
        let left = if parent - 1 == elem.parent { elem.lhs.len() as u8 } else { 1 };
        let fmt = FormatFunc::Func { sym: elem.sym, left, right };
        if !p.core.format_lookup.contains_key(&Format::Func(fmt)) {
          self.fast_path = Err(elem.pos);
          break
        }
        parent = elem.parent;
        right = 1;
      }
    }
    if self.fast_path.is_err() {
      if self.stack.len() <= 1 {
        return Err(p.scan.err(self.stack[0].pos, ParseErr::BadInfixExpression))
      }
      self.slow_path(p)?
    }
    for i in 0..self.stack.len() {
      let lo = self.stack[i].parent;
      if lo < i {
        let [stack @ .., rhs] = &mut self.stack[..i + 1] else { unreachable!() };
        Self::accum_left(stack, lo, i, &mut rhs.lhs);
      }
    }
    let hi = self.stack.len();
    Self::accum_left(&mut self.stack, 0, hi, &mut self.rhs);
    Ok(self.rhs)
  }
}

impl<'a> MizParser<'a> {
  /// if max_out is Some(n), then at most n results will be returned at paren level 0
  /// (unless n = 0 in which case 1 return is still possible)
  fn parse_func_rhs(
    &mut self, paren: &mut u32, mut max_out: Option<u8>, mut lhs: Vec<Term>,
  ) -> PResult<Vec<Term>> {
    loop {
      match self.scan.peek().kind {
        TokenKind::Symbol(SymbolKind::Func(_)) => {
          let mut lterm = LongTermBuilder::new(lhs);
          loop {
            let tok = self.scan.next();
            let args;
            if self.scan.try_accept(TokenKind::LPAREN) {
              args = self.parse_terms();
              self.scan.accept(TokenKind::RPAREN)?;
            } else {
              args = match self.parse_term_hi()? {
                Some(tm) => vec![*tm],
                None => vec![],
              }
            }
            lterm.push(self, tok, args);
            if !matches!(self.scan.peek().kind, TokenKind::Symbol(SymbolKind::Func(_))) {
              break
            }
          }
          lhs = lterm.finish(self)?;
        }
        TokenKind::Keyword(Keyword::Qua) if lhs.len() == 1 => {
          let tok = self.scan.next();
          let ty = self.parse_type()?;
          lhs = vec![Term::Qua { pos: tok.pos, term: Box::new(lhs.pop().unwrap()), ty }]
        }
        TokenKind::Keyword(Keyword::Comma)
          if !lhs.is_empty()
            && (*paren > 0 || max_out.as_mut().is_none_or(|n| *n > 1 && (*n -= 1, true).1)) =>
        {
          self.scan.next();
          lhs.push(*self.parse_term()?);
        }
        TokenKind::RPAREN if *paren > 0 => {
          *paren -= 1;
          self.scan.next();
        }
        _ => break,
      }
    }
    Ok(lhs)
  }

  fn with_parens<R>(&mut self, f: impl FnOnce(&mut Self, &mut u32) -> PResult<R>) -> PResult<R> {
    let mut paren = 0;
    while self.scan.try_accept(TokenKind::LPAREN) {
      paren += 1;
    }
    let out = f(self, &mut paren)?;
    for _ in 0..paren {
      self.scan.accept(TokenKind::RPAREN)?;
    }
    Ok(out)
  }

  fn parse_terms_lo_or_radix_type(
    &mut self, upto: Option<u8>, allow_type: bool,
  ) -> PResult<Result<Vec<Term>, Box<Type>>> {
    self.with_parens(|this, paren| {
      let lhs = match this.parse_term_hi()? {
        Some(tm) => vec![*tm],
        None => vec![],
      };
      let args = this.parse_func_rhs(paren, upto, lhs)?;
      if allow_type && args.is_empty() {
        if let Some(ty) = this.parse_radix_type()? {
          return Ok(Err(ty))
        }
      }
      Ok(Ok(args))
    })
  }

  /// * If `allow_type` is false, the `Option<Box<Type>>` is always None
  /// * If `allow_term` is false, the `Err` variant never occurs
  #[allow(clippy::type_complexity)]
  fn parse_attrs_or_type_or_term(
    &mut self, allow_type: bool, allow_term: bool,
  ) -> PResult<Result<(Vec<Attr>, Option<Box<Type>>), Box<Term>>> {
    let mut attrs = vec![];
    loop {
      let non = self.scan.next_if(|tok| tok.kind == Keyword::Non.into());
      let args = match self.parse_terms_lo_or_radix_type(None, allow_type && non.is_none())? {
        Ok(args) => args,
        Err(ty) => {
          if let Some(non) = non {
            return Err(self.scan.err(non.pos, ParseErr::ExpectedAttribute))
          }
          return Ok(Ok((attrs, Some(ty))))
        }
      };
      let tok = self.scan.next();
      let TokenKind::Symbol(SymbolKind::Attr(sym)) = tok.kind else {
        self.scan.undo(tok);
        if allow_term && non.is_none() && attrs.is_empty() && args.len() == 1 {
          return Ok(Err(Box::new({ args }.pop().unwrap())))
        }
        if !(non.is_none() && args.is_empty()) {
          return Err(self.scan.err(tok.pos, ParseErr::ExpectedAttribute))
        }
        return Ok(Ok((attrs, if allow_type { self.parse_radix_type()? } else { None })))
      };
      let mut attr = Attr::Attr { pos: tok.pos, sym, spelling: tok.spelling.to_owned(), args };
      if let Some(non) = non {
        attr = Attr::Non { pos: non.pos, attr: Box::new(attr) };
      }
      attrs.push(attr)
    }
  }

  fn parse_term(&mut self) -> PResult<Box<Term>> {
    self.with_parens(|this, paren| {
      let lhs = match this.parse_term_hi()? {
        Some(tm) => vec![*tm],
        None => vec![],
      };
      let out = this.parse_func_rhs(paren, Some(0), lhs)?;
      if out.len() != 1 {
        let pos = this.scan.peek().pos;
        return Err(this.scan.err(pos, ParseErr::ExpectedFunctorSymbol))
      }
      Ok(Box::new({ out }.pop().unwrap()))
    })
  }

  fn parse_atomic_formula(&mut self, paren: &mut u32) -> PResult<Box<Formula>> {
    let lhs = match self.parse_term_hi()? {
      Some(tm) => vec![*tm],
      None => vec![],
    };
    let args = self.parse_func_rhs(paren, None, lhs)?;
    let is =
      if args.len() == 1 { self.scan.next_if(|tok| tok.kind == Keyword::Is.into()) } else { None };
    Ok(if let Some(tok) = is {
      let positive = !self.scan.try_accept(Keyword::Not);
      let term = Box::new({ args }.pop().unwrap());
      let (attrs, ty) = self.parse_attrs_or_type_or_term(true, false)?.unwrap();
      if let Some(mut ty) = ty {
        if !attrs.is_empty() {
          ty = Box::new(Type::Cluster { pos: attrs[0].pos(), attrs, ty })
        }
        Box::new(Formula::Is { pos: tok.pos, positive, term, ty })
      } else {
        if attrs.is_empty() {
          let pos = self.scan.peek().pos;
          return Err(self.scan.err(pos, ParseErr::ExpectedAttribute))
        }
        Box::new(Formula::Attr { pos: tok.pos, positive, term, attrs })
      }
    } else {
      let mut lhs = Err(args);
      let (first, rest) = loop {
        let mut tok = self.scan.next();
        let (positive, sym) = match tok.kind {
          TokenKind::Symbol(SymbolKind::Pred(sym)) => (true, sym),
          TokenKind::Keyword(Keyword::Do) => {
            self.scan.accept(Keyword::Not)?;
            tok = self.scan.next();
            let TokenKind::Symbol(SymbolKind::Pred(sym)) = tok.kind else {
              return Err(self.scan.err(tok.pos, ParseErr::ExpectedPredicateSymbol))
            };
            (false, sym)
          }
          _ => {
            self.scan.undo(tok);
            break match lhs {
              Ok(v) => v,
              Err(_) => return Err(self.scan.err(tok.pos, ParseErr::ExpectedPredicateSymbol)),
            }
          }
        };
        let mut right = match self.max_pred_rhs.get(&sym) {
          Some(&max) => self.parse_terms_lo_or_radix_type(Some(max), false)?.unwrap(),
          None => return Err(self.scan.err(tok.pos, ParseErr::UnknownFormat(PatKind::Pred))),
        };
        let spelling = tok.spelling.to_owned();
        lhs = Ok(match lhs {
          Err(mut args) => {
            let Ok(left) = args.len().try_into() else {
              return Err(self.scan.err(tok.pos, ParseErr::TooManyArgs))
            };
            args.append(&mut right);
            (Box::new(Pred { pos: tok.pos, positive, sym, spelling, left, args }), vec![])
          }
          Ok((pred, mut rhss)) => {
            Vec::push(&mut rhss, PredRhs { pos: tok.pos, positive, sym, spelling, right });
            (pred, rhss)
          }
        })
      };
      if rest.is_empty() {
        Box::new(Formula::Pred(first))
      } else {
        Box::new(Formula::ChainPred { pos: first.pos, first, rest })
      }
    })
  }

  fn parse_formula_lhs(&mut self) -> PResult<Box<Formula>> {
    let mut paren = 0;
    while self.scan.try_accept(TokenKind::LPAREN) {
      paren += 1;
    }
    let tok = self.scan.next();
    let mut lhs = match tok.kind {
      TokenKind::Keyword(Keyword::For) => {
        let vars = self.parse_binders()?;
        let st = if self.scan.try_accept(Keyword::St) { Some(self.parse_formula()?) } else { None };
        if !self.scan.try_accept(Keyword::Holds)
          && !matches!(self.scan.peek().kind, TokenKind::Keyword(Keyword::For | Keyword::Ex))
        {
          let pos = self.scan.peek().pos;
          return Err(self.scan.err(pos, ParseErr::ExpectedHolds))
        }
        let scope = self.parse_formula()?;
        Box::new(Formula::Binder { kind: FormulaBinder::ForAll, pos: tok.pos, vars, st, scope })
      }
      TokenKind::Keyword(Keyword::Ex) => {
        let vars = self.parse_binders()?;
        self.scan.accept(Keyword::St)?;
        let (st, scope) = (None, self.parse_formula()?);
        Box::new(Formula::Binder { kind: FormulaBinder::Exists, pos: tok.pos, vars, st, scope })
      }
      TokenKind::Keyword(Keyword::Contradiction) => Box::new(Formula::False { pos: tok.pos }),
      TokenKind::Keyword(Keyword::Thesis) => Box::new(Formula::Thesis { pos: tok.pos }),
      TokenKind::Keyword(Keyword::Not) =>
        Box::new(Formula::Not { pos: tok.pos, f: self.parse_formula_lhs()? }),
      TokenKind::Ident if self.scan.try_accept(TokenKind::LBRACK) => {
        let args =
          if self.scan.peek().kind == TokenKind::RBRACK { vec![] } else { self.parse_terms() };
        self.scan.accept(TokenKind::RBRACK)?;
        Box::new(Formula::PrivPred {
          pos: tok.pos,
          kind: None,
          spelling: tok.spelling.into(),
          args,
        })
      }
      _ => {
        self.scan.undo(tok);
        self.parse_atomic_formula(&mut paren)?
      }
    };
    for _ in 0..paren {
      lhs = self.parse_formula_rhs(0, lhs)?;
      self.scan.accept(TokenKind::RPAREN)?;
    }
    Ok(lhs)
  }

  fn parse_formula_rhs(&mut self, prec: u8, mut lhs: Box<Formula>) -> PResult<Box<Formula>> {
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
          let mut rhs = self.parse_formula_lhs()?;
          if $prec < MAX_PREC {
            rhs = self.parse_formula_rhs($prec + 1, rhs)?;
          }
          let kind = FormulaBinop::$binop;
          lhs = Box::new(Formula::Binop { kind, pos: tok.pos, f1: lhs, f2: rhs })
        }};
      }
      #[allow(clippy::absurd_extreme_comparisons)]
      match tok.kind {
        TokenKind::Keyword(Keyword::Amp) if then_ellipsis && prec <= FLEX_AND_PREC => {
          self.scan.next();
          self.scan.accept(Keyword::Amp)?;
          binop!(FlexAnd, FLEX_AND_PREC)
        }
        TokenKind::Keyword(Keyword::Amp) if !then_ellipsis && prec <= AND_PREC =>
          binop!(And, AND_PREC),
        TokenKind::Keyword(Keyword::Or) if then_ellipsis && prec <= FLEX_OR_PREC => {
          self.scan.next();
          self.scan.accept(Keyword::Or)?;
          binop!(FlexOr, FLEX_OR_PREC)
        }
        TokenKind::Keyword(Keyword::Or) if !then_ellipsis && prec <= OR_PREC => binop!(Or, OR_PREC),
        TokenKind::Keyword(Keyword::Iff) if prec <= IFF_PREC => binop!(Iff, IFF_PREC),
        TokenKind::Keyword(Keyword::Implies) if prec <= IMP_PREC => binop!(Imp, IMP_PREC),
        _ => {
          self.scan.undo(tok);
          return Ok(lhs)
        }
      }
    }
  }

  fn parse_formula(&mut self) -> PResult<Box<Formula>> {
    let lhs = self.parse_formula_lhs()?;
    self.parse_formula_rhs(0, lhs)
  }

  fn parse_radix_type(&mut self) -> PResult<Option<Box<Type>>> {
    self.with_parens(|this, paren| {
      let tok = this.scan.next();
      Ok(match tok.kind {
        TokenKind::Symbol(SymbolKind::Mode(sym)) => {
          let Some(&max) = this.max_mode_args.get(&sym) else {
            return Err(this.scan.err(tok.pos, ParseErr::UnknownFormat(PatKind::Mode)))
          };
          let spelling = tok.spelling.to_owned();
          let args = if max > 0 && this.scan.try_accept(Keyword::Of) {
            this.comma_separated_upto(max, |this| this.parse_term().map(|t| *t))
          } else {
            vec![]
          };
          Some(Box::new(Type::Mode { pos: tok.pos, sym, spelling, args }))
        }
        TokenKind::Symbol(SymbolKind::Struct(sym)) => {
          let Some(&max) = this.max_struct_args.get(&sym) else {
            return Err(this.scan.err(tok.pos, ParseErr::UnknownFormat(PatKind::Struct)))
          };
          let spelling = tok.spelling.to_owned();
          let args = if max > 0 && this.scan.try_accept(Keyword::Over) {
            this.comma_separated_upto(max, |this| this.parse_term().map(|t| *t))
          } else {
            vec![]
          };
          Some(Box::new(Type::Struct { pos: tok.pos, sym, spelling, args }))
        }
        _ if *paren == 0 => {
          this.scan.undo(tok);
          None
        }
        _ => return Err(this.scan.err(tok.pos, ParseErr::ExpectedType)),
      })
    })
  }

  fn parse_type(&mut self) -> PResult<Box<Type>> {
    let (attrs, ty) = self.parse_attrs_or_type_or_term(true, false)?.unwrap();
    let mut ty = match ty {
      Some(ty) => ty,
      None => {
        let pos = self.scan.peek().pos;
        return Err(self.scan.err(pos, ParseErr::ExpectedType))
      }
    };
    if !attrs.is_empty() {
      ty = Box::new(Type::Cluster { pos: attrs[0].pos(), attrs, ty })
    }
    Ok(ty)
  }

  fn parse_types(&mut self) -> Vec<Type> {
    if matches!(self.scan.peek().kind, TokenKind::RBRACK | TokenKind::RPAREN) {
      vec![]
    } else {
      self.comma_separated(|this| this.parse_type().map(|t| *t))
    }
  }

  fn parse_proposition(&mut self) -> PResult<Proposition> {
    Ok(Proposition { label: self.parse_label(), f: *self.parse_formula()? })
  }

  fn assert_no_link(&self, link: Option<Span>) -> PResult<()> {
    match link {
      Some(pos) => Err(self.scan.err(pos, ParseErr::LinkNotAllowed)),
      None => Ok(()),
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
    self.comma_separated_skip(|this| {
      let id = this.scan.accept(TokenKind::Ident)?;
      let kind = if this.scan.try_accept(Keyword::Colon) {
        let spelling = this.parse_article(id)?;
        let art = match this.core.articles.get(&spelling) {
          Some(art) => *art,
          None =>
            return Err(this.scan.err(
              id.pos,
              ParseErr::ArticleNotFound {
                spelling: id.spelling.to_string(),
                directive: "theorems",
              },
            )),
        };
        let mut refs = vec![];
        loop {
          refs.push(if this.scan.try_accept(Keyword::Def) {
            let tok = this.scan.next();
            let TokenKind::Number(n) = tok.kind else {
              return Err(this.scan.err(tok.pos, ParseErr::ExpectedNumeral))
            };
            let n = match n.checked_sub(1) {
              Some(n) => n,
              None => return Err(this.scan.err(tok.pos, ParseErr::ExpectedNonzeroNumeral)),
            };
            RefFragment::Def { pos: tok.pos, id: DefId(n) }
          } else {
            let tok = this.scan.next();
            let TokenKind::Number(n) = tok.kind else {
              return Err(this.scan.err(tok.pos, ParseErr::ExpectedNumeral))
            };
            let n = match n.checked_sub(1) {
              Some(n) => n,
              None => return Err(this.scan.err(tok.pos, ParseErr::ExpectedNonzeroNumeral)),
            };
            RefFragment::Thm { pos: tok.pos, id: ThmId(n) }
          });
          let tok = this.scan.next();
          if tok.kind != TokenKind::Keyword(Keyword::Comma)
            || this.scan.peek().kind == TokenKind::Ident
          {
            this.scan.undo(tok);
            break ReferenceKind::Global { art, spelling, refs }
          }
        }
      } else {
        ReferenceKind::UnresolvedPriv(id.spelling.to_owned())
      };
      Ok(Reference { pos: id.pos, kind })
    })
  }

  fn parse_simple_justification(&mut self, link: Option<Span>) -> PResult<Justification> {
    let tok = self.scan.next();
    Ok(match tok.kind {
      TokenKind::Keyword(Keyword::By) => Justification::Inference {
        pos: tok.pos,
        kind: InferenceKind::By { link },
        refs: self.with_underscore(|this| this.parse_references()),
      },
      TokenKind::Keyword(Keyword::From) => self.with_underscore(|this| {
        let id = this.scan.accept(TokenKind::Ident)?;
        let sch = if this.scan.try_accept(Keyword::Colon) {
          let spelling = this.parse_article(id)?;
          let art = match this.core.articles.get(&spelling) {
            Some(art) => *art,
            None =>
              return Err(this.scan.err(
                id.pos,
                ParseErr::ArticleNotFound {
                  spelling: id.spelling.to_string(),
                  directive: "schemes",
                },
              )),
          };
          this.scan.accept(Keyword::Sch)?;
          let tok = this.scan.next();
          let TokenKind::Number(n) = tok.kind else {
            return Err(this.scan.err(tok.pos, ParseErr::ExpectedNumeral))
          };
          let n = match n.checked_sub(1) {
            Some(n) => n,
            None => return Err(this.scan.err(tok.pos, ParseErr::ExpectedNonzeroNumeral)),
          };
          SchRef::Resolved { art, spelling, sch: SchId(n) }
        } else {
          SchRef::UnresolvedPriv(id.spelling.to_owned())
        };
        let mut refs = vec![];
        if this.scan.try_accept(TokenKind::LPAREN) {
          refs = this.parse_references();
          this.scan.accept(TokenKind::RPAREN)?;
        }
        Ok(Justification::Inference { pos: tok.pos, kind: InferenceKind::From(sch), refs })
      })?,
      _ => {
        self.scan.undo(tok);
        Justification::Inference { pos: tok.pos, kind: InferenceKind::By { link }, refs: vec![] }
      }
    })
  }

  fn parse_justification(&mut self, link: Option<Span>) -> PResult<Justification> {
    if let Some(tok) = self.scan.next_if(|tok| tok.kind == Keyword::Proof.into()) {
      self.assert_no_link(link)?;
      let (items, end) = self.parse_proof(false)?;
      Ok(Justification::Block { pos: (tok.pos, end), items })
    } else {
      self.parse_simple_justification(link)
    }
  }

  fn parse_justification_semi(&mut self, link: Option<Span>) -> PResult<Justification> {
    let just = self.parse_justification(link)?;
    self.scan.accept(Keyword::Semicolon)?;
    Ok(just)
  }

  fn parse_scheme(&mut self) -> PResult<Box<SchemeBlock>> {
    let sym = (self.scan.next_if(|tok| matches!(tok.kind, TokenKind::Ident)))
      .map(|tok| tok.spelling.into());
    self.scan.accept(TokenKind::LBRACE)?;
    let groups = self.comma_separated_skip(|this| {
      let pos = this.scan.peek().pos;
      let vars = this.comma_separated_skip(|this| this.parse_variable());
      let tok = this.scan.next();
      Ok(match tok.kind {
        TokenKind::LBRACK => {
          let tys = this.parse_types();
          this.scan.accept(TokenKind::RBRACK)?;
          SchemeBinderGroup::Pred { pos, vars, tys }
        }
        TokenKind::LPAREN => {
          let tys = this.parse_types();
          this.scan.accept(TokenKind::RPAREN)?;
          this.scan.accept(TokenKind::Keyword(Keyword::Arrow))?;
          let ret = *this.parse_type()?;
          SchemeBinderGroup::Func { pos, vars, tys, ret }
        }
        _ => return Err(this.scan.err(tok.pos, ParseErr::ExpectedPatternStart)),
      })
    });
    self.scan.accept(TokenKind::RBRACE)?;
    self.scan.accept(Keyword::Colon)?;
    let concl = *self.parse_formula()?;
    let prems = if self.scan.try_accept(Keyword::Provided) {
      self.separated_skip(Keyword::And, |this| this.parse_proposition())
    } else {
      vec![]
    };
    self.scan.accept(Keyword::Proof)?;
    let (items, end) = self.parse_proof(false)?;
    self.scan.accept(Keyword::Semicolon)?;
    Ok(Box::new(SchemeBlock {
      end,
      head: SchemeHead { sym, nr: None, groups, concl, prems },
      items,
    }))
  }

  fn parse_params(&mut self, must_paren: bool) -> PResult<Vec<Variable>> {
    Ok(if self.scan.try_accept(TokenKind::LPAREN) {
      let args = self.comma_separated_skip(|this| this.parse_variable());
      self.scan.accept(TokenKind::RPAREN)?;
      args
    } else if self.scan.peek().kind == TokenKind::Ident {
      if must_paren {
        vec![self.parse_variable()?]
      } else {
        self.comma_separated_skip(|this| this.parse_variable())
      }
    } else {
      vec![]
    })
  }

  fn parse_pattern_rhs(
    &mut self, pos: Span, paren: bool, mut args: Vec<Variable>,
  ) -> PResult<Pattern> {
    let tok = self.scan.next();
    Ok(match tok.kind {
      TokenKind::Symbol(SymbolKind::Func(sym)) if paren || args.len() <= 1 => {
        let spelling = tok.spelling.to_owned();
        let Ok(left) = args.len().try_into() else {
          return Err(self.scan.err(tok.pos, ParseErr::TooManyArgs))
        };
        args.append(&mut self.parse_params(true)?);
        Pattern::Func(Box::new(PatternFunc::Func { pos, sym, spelling, left, args }))
      }
      TokenKind::Symbol(SymbolKind::LeftBrk(lsym)) if args.is_empty() => {
        let lspelling = tok.spelling.to_owned();
        args = self.comma_separated_skip(|this| this.parse_variable());
        let tok = self.scan.next();
        let TokenKind::Symbol(SymbolKind::RightBrk(rsym)) = tok.kind else {
          return Err(self.scan.err(tok.pos, ParseErr::ExpectedRightBracket))
        };
        let rspelling = tok.spelling.to_owned();
        let pat = PatternFunc::Bracket { pos, lsym, lspelling, rsym, rspelling, args };
        Pattern::Func(Box::new(pat))
      }
      TokenKind::Symbol(SymbolKind::Pred(sym)) if !paren => {
        let Ok(left) = args.len().try_into() else {
          return Err(self.scan.err(tok.pos, ParseErr::TooManyArgs))
        };
        if self.scan.peek().kind == TokenKind::Ident {
          args.append(&mut self.comma_separated_skip(|this| this.parse_variable()));
        }
        let spelling = tok.spelling.to_owned();
        Pattern::Pred(Box::new(PatternPred { pos, sym, spelling, left, args }))
      }
      _ => return Err(self.scan.err(tok.pos, ParseErr::ExpectedFunctorOrPredicateSymbol)),
    })
  }

  fn parse_pattern(&mut self) -> PResult<Pattern> {
    let tok = self.scan.next();
    Ok(match tok.kind {
      TokenKind::Symbol(SymbolKind::Mode(sym)) => {
        let args = if self.scan.try_accept(Keyword::Of) {
          self.comma_separated_skip(|this| this.parse_variable())
        } else {
          vec![]
        };
        let spelling = tok.spelling.to_owned();
        Pattern::Mode(Box::new(PatternMode { pos: tok.pos, sym, spelling, args }))
      }
      TokenKind::LPAREN => {
        let args = self.comma_separated_skip(|this| this.parse_variable());
        self.scan.accept(TokenKind::RPAREN)?;
        self.parse_pattern_rhs(tok.pos, true, args)?
      }
      TokenKind::Ident => {
        let id = Variable { pos: tok.pos, var: None, spelling: tok.spelling.into() };
        if self.scan.try_accept(Keyword::Is) {
          let mut args = self.parse_params(false)?;
          args.push(id);
          let tok = self.scan.next();
          let TokenKind::Symbol(SymbolKind::Attr(n)) = tok.kind else {
            return Err(self.scan.err(tok.pos, ParseErr::ExpectedAttrSymbol))
          };
          let spelling = tok.spelling.to_owned();
          Pattern::Attr(Box::new(PatternAttr { pos: tok.pos, sym: n, spelling, args }))
        } else {
          let mut args = vec![id];
          while self.scan.try_accept(Keyword::Comma) {
            args.push(self.parse_variable()?)
          }
          self.parse_pattern_rhs(tok.pos, false, args)?
        }
      }
      _ => {
        self.scan.undo(tok);
        self.parse_pattern_rhs(tok.pos, false, vec![])?
      }
    })
  }

  fn parse_definiens<T>(
    &mut self, mut f: impl FnMut(&mut Self) -> PResult<Box<T>>,
    mk_kind: impl FnOnce(DefBody<T>) -> DefValue,
  ) -> PResult<Box<Definiens>>
  where
    Box<T>: ErrorNode,
  {
    let label = if self.scan.try_accept(Keyword::Colon) {
      match self.parse_label() {
        Some(l) => Some(l),
        None => {
          let pos = self.scan.peek().pos;
          return Err(self.scan.err(pos, ParseErr::ExpectedLabel))
        }
      }
    } else {
      None
    };
    let pos = self.scan.peek().pos;
    let mut value = f(self)?;
    let mut cases = vec![];
    let otherwise = if self.scan.try_accept(Keyword::If) {
      loop {
        // `value` is already parsed; parse this case's guard. On failure, keep the
        // value with an error guard and resync to the next `,` so later cases parse.
        match self.parse_formula() {
          Ok(guard) => cases.push(DefCase { case: value, guard }),
          Err(_) => {
            let epos = self.scan.peek().pos;
            cases.push(DefCase { case: value, guard: <Box<Formula>>::error(epos) });
            self.recover_to(Keyword::Comma);
          }
        }
        if !self.scan.try_accept(Keyword::Comma) {
          break
        }
        // Parse the next case's `value if`. On failure, resync to the next `,` and
        // substitute an error value so the loop keeps making progress.
        value = match (|| -> PResult<Box<T>> {
          let v = f(self)?;
          self.scan.accept(Keyword::If)?;
          Ok(v)
        })() {
          Ok(v) => v,
          Err(_) => {
            let epos = self.scan.peek().pos;
            self.recover_to(Keyword::Comma);
            <Box<T>>::error(epos)
          }
        };
      }
      if self.scan.try_accept(Keyword::Otherwise) {
        Some(f(self)?)
      } else {
        None
      }
    } else {
      Some(value)
    };
    Ok(Box::new(Definiens { pos, label, kind: mk_kind(DefBody { cases, otherwise }) }))
  }

  fn parse_corr_conds(&mut self) -> PResult<(Vec<CorrCond>, Option<Correctness>)> {
    let mut conds = vec![];
    while let TokenKind::CorrCond(kind) = self.scan.peek().kind {
      let pos = self.scan.next().pos;
      match (|| -> PResult<CorrCond> {
        Ok(CorrCond { pos, kind, just: self.parse_justification_semi(None)? })
      })() {
        Ok(c) => conds.push(c),
        Err(_) => {
          self.recover_to(Keyword::Semicolon);
          self.scan.try_accept(Keyword::Semicolon);
        }
      }
    }
    let corr = match self.scan.next_if(|tok| tok.kind == Keyword::Correctness.into()) {
      Some(tok) => Some(Correctness { pos: tok.pos, just: self.parse_justification_semi(None)? }),
      None => None,
    };
    Ok((conds, corr))
  }

  fn parse_properties(&mut self) -> PResult<Vec<Property>> {
    let mut props = vec![];
    while let TokenKind::Property(kind) = self.scan.peek().kind {
      let pos = self.scan.next().pos;
      match (|| -> PResult<Property> {
        Ok(Property { pos, kind, just: Box::new(self.parse_justification_semi(None)?) })
      })() {
        Ok(p) => props.push(p),
        Err(_) => {
          self.recover_to(Keyword::Semicolon);
          self.scan.try_accept(Keyword::Semicolon);
        }
      }
    }
    Ok(props)
  }

  fn parse_definition(&mut self, redef: bool, mut kind: DefinitionKind) -> PResult<ItemKind> {
    if let DefinitionKind::Func { def, .. }
    | DefinitionKind::Pred { def, .. }
    | DefinitionKind::Mode { kind: DefModeKind::Standard { def, .. }, .. }
    | DefinitionKind::Attr { def, .. } = &mut kind
    {
      if self.scan.try_accept(Keyword::Means) {
        *def = Some(self.parse_definiens(|this| this.parse_formula(), DefValue::Formula)?)
      } else if self.scan.try_accept(Keyword::Equals) {
        *def = Some(self.parse_definiens(|this| this.parse_term(), DefValue::Term)?)
      }
    }
    self.scan.accept(Keyword::Semicolon)?;
    let (conds, corr) = self.parse_corr_conds()?;
    let props = self.parse_properties()?;
    let fmt = kind.to_format();
    if self.core.after_definition(kind.pos(), redef, fmt) {
      self.read_format(&fmt);
    }
    let body = DefinitionBody { redef, conds, corr, props };
    Ok(ItemKind::Definition(Box::new(Definition { kind, body })))
  }

  fn parse_binders_gen(
    &mut self, is: impl Fn(TokenKind) -> bool, more: impl Fn(TokenKind) -> bool,
  ) -> PResult<Vec<BinderGroup>> {
    let mut out = vec![];
    loop {
      let vars = self.comma_separated_skip(|this| this.parse_variable());
      let ty = match (self.scan).next_if(|tok| is(tok.kind)) {
        Some(_) => {
          let epos = self.scan.peek().pos;
          Some(match self.parse_type() {
            Ok(ty) => ty,
            Err(_) => <Box<Type>>::error(epos),
          })
        }
        None => None,
      };
      if ty.is_some() {
        out.push(BinderGroup { vars, ty });
      } else {
        out.extend(vars.into_iter().map(|var| BinderGroup { vars: vec![var], ty: None }));
      }
      if !more(self.scan.peek().kind) {
        break
      }
      self.scan.next();
    }
    Ok(out)
  }

  fn parse_binders(&mut self) -> PResult<Vec<BinderGroup>> {
    self.parse_binders_gen(|k| k == Keyword::Be.into(), |k| k == Keyword::Comma.into())
  }

  fn parse_where(&mut self) -> PResult<Vec<BinderGroup>> {
    self.parse_binders_gen(
      |k| matches!(k, TokenKind::Keyword(Keyword::Is | Keyword::Are)),
      |k| matches!(k, TokenKind::Keyword(Keyword::Where | Keyword::Comma)),
    )
  }

  fn parse_choice(&mut self) -> PResult<(Vec<BinderGroup>, Vec<Proposition>)> {
    let vars = self.parse_binders()?;
    self.scan.accept(Keyword::Such)?;
    self.scan.accept(Keyword::That)?;
    let conds = self.separated_skip(Keyword::And, |this| this.parse_proposition());
    Ok((vars, conds))
  }

  fn parse_then(&mut self) -> Option<Span> {
    let tok = self.scan.peek();
    if let TokenKind::Keyword(Keyword::Then) = tok.kind {
      Some(self.scan.next().pos)
    } else {
      None
    }
  }

  fn parse_stmt(&mut self, link: Option<Span>) -> PResult<Statement> {
    let label = self.parse_label();
    let tok = self.scan.next();
    Ok(match tok.kind {
      TokenKind::Keyword(Keyword::Now) => {
        self.assert_no_link(link)?;
        let (items, end) = self.parse_proof(true)?;
        Statement::Now { end, label, items }
      }
      _ => {
        self.scan.undo(tok);
        let prop = Box::new(Proposition { label, f: *self.parse_formula()? });
        if let Some(tok) = self.scan.next_if(|tok| tok.kind == Keyword::Proof.into()) {
          self.assert_no_link(link)?;
          let (items, end) = self.parse_proof(false)?;
          let just = Box::new(Justification::Block { pos: (tok.pos, end), items });
          Statement::Proposition { prop, just }
        } else {
          let just = Box::new(self.parse_simple_justification(link)?);
          let mut steps = vec![];
          while let Some(tok) = self.scan.next_if(|tok| tok.kind == Keyword::DotEquals.into()) {
            let rhs = *self.parse_term()?;
            let just = self.parse_simple_justification(None)?;
            steps.push(IterStep { pos: tok.pos, rhs, just });
          }
          if steps.is_empty() {
            Statement::Proposition { prop, just }
          } else {
            Statement::IterEquality { prop, just, steps }
          }
        }
      }
    })
  }

  fn parse_stmt_item(&mut self) -> PResult<ItemKind> {
    let link = self.parse_then();
    let tok = self.scan.next();
    Ok(match tok.kind {
      TokenKind::Keyword(Keyword::DefFunc) => {
        self.assert_no_link(link)?;
        let var = Box::new(self.parse_variable()?);
        self.scan.accept(TokenKind::LPAREN)?;
        let tys = self.parse_types();
        self.scan.accept(TokenKind::RPAREN)?;
        self.scan.accept(TokenKind::EQUAL)?;
        let value = self.parse_term()?;
        ItemKind::DefFunc { var, tys, value }
      }
      TokenKind::Keyword(Keyword::DefPred) => {
        self.assert_no_link(link)?;
        let var = Box::new(self.parse_variable()?);
        self.scan.accept(TokenKind::LBRACK)?;
        let tys = self.parse_types();
        self.scan.accept(TokenKind::RBRACK)?;
        self.scan.accept(Keyword::Means)?;
        let value = self.parse_formula()?;
        ItemKind::DefPred { var, tys, value }
      }
      TokenKind::SET => {
        self.assert_no_link(link)?;
        ItemKind::Set(self.comma_separated_skip(|this| {
          let var = Box::new(this.parse_variable()?);
          this.scan.accept(TokenKind::EQUAL)?;
          Ok(SetDecl { var, value: this.parse_term()? })
        }))
      }
      TokenKind::Keyword(Keyword::Reconsider) => {
        let vars = self.comma_separated_skip(|this| {
          let var = this.parse_variable()?;
          Ok(if this.scan.try_accept(TokenKind::EQUAL) {
            ReconsiderVar::Equality { var, tm: *this.parse_term()? }
          } else {
            ReconsiderVar::Var(var)
          })
        });
        self.scan.accept(Keyword::As)?;
        let ty = self.parse_type()?;
        ItemKind::Reconsider { vars, ty, just: Box::new(self.parse_simple_justification(link)?) }
      }
      TokenKind::Keyword(Keyword::Consider) => {
        let (vars, conds) = self.parse_choice()?;
        ItemKind::Consider { vars, conds, just: Box::new(self.parse_simple_justification(link)?) }
      }
      _ => {
        self.scan.undo(tok);
        ItemKind::Statement(self.parse_stmt(link)?)
      }
    })
  }

  fn parse_assumption(&mut self, pos: Span) -> PResult<Assumption> {
    Ok(if self.scan.try_accept(Keyword::That) {
      let conds = self.separated_skip(Keyword::And, |this| this.parse_proposition());
      Assumption::Collective { pos, conds }
    } else {
      Assumption::Single { pos, prop: Box::new(self.parse_proposition()?) }
    })
  }

  fn parse_per_cases(
    &mut self, diffuse: bool, link: Option<Span>, pos: Span, items: &mut Vec<Item>,
  ) -> PResult<Span> {
    self.scan.accept(Keyword::Cases)?;
    let just = Box::new(self.parse_simple_justification(link)?);
    self.scan.accept(Keyword::Semicolon)?;
    let mut casekind = None;
    let mut blocks = vec![];
    let end = loop {
      let tok = self.scan.next();
      let kind = match tok.kind {
        TokenKind::Keyword(Keyword::End) => break tok.end(),
        TokenKind::Keyword(Keyword::Case) => CaseKind::Case,
        TokenKind::Keyword(Keyword::Suppose) => CaseKind::Suppose,
        _ => return Err(self.scan.err(tok.pos, ParseErr::ExpectedCaseOrSuppose)),
      };
      if let Some(kind2) = casekind.replace(kind) {
        if kind != kind2 {
          return Err(self.scan.err(tok.pos, ParseErr::MixedCaseSuppose))
        }
      }
      let hyp = Box::new(self.parse_assumption(tok.pos)?);
      self.scan.accept(Keyword::Semicolon)?;
      let (items, end) = self.parse_proof(diffuse)?;
      self.scan.accept(Keyword::Semicolon)?;
      blocks.push(CaseBlock { end, hyp, items })
    };
    let kind = match casekind {
      Some(kind) => kind,
      None => return Err(self.scan.err(pos, ParseErr::NoCases)),
    };
    items.push(Item { pos, kind: ItemKind::PerCases { just, kind, blocks } });
    Ok(end)
  }

  fn parse_proof(&mut self, diffuse: bool) -> PResult<(Vec<Item>, Span)> {
    let mut items = vec![];
    let end = loop {
      let tok = self.scan.next();
      let start = tok.pos;
      match tok.kind {
        TokenKind::Keyword(Keyword::End) => break tok.end(),
        // Unterminated proof at end of file: report and stop, rather than feeding the
        // idempotent `Eof` token back into recovery forever (`ensure_progress` will not
        // drop `Eof`). Downstream also reports the thesis as not fully discharged.
        TokenKind::Eof => {
          self.scan.err(start, ParseErr::Expected(ExpectedTok::Other("'end'".into())));
          break start
        }
        TokenKind::Keyword(Keyword::Then) if self.scan.peek().kind == Keyword::Per.into() => {
          let pos = self.scan.next().pos;
          break self.parse_per_cases(diffuse, Some(start), pos, &mut items)?
        }
        TokenKind::Keyword(Keyword::Per) =>
          break self.parse_per_cases(diffuse, None, start, &mut items)?,
        _ => {
          let kind = self.recover_block_item(start.start, |this| {
            let kind = match tok.kind {
              TokenKind::Keyword(Keyword::Take) =>
                ItemKind::Take(this.comma_separated_skip(|this| {
                  if matches!(this.scan.peek().kind, TokenKind::Ident) {
                    let tok = this.scan.next();
                    let lookahead = this.scan.peek().kind;
                    if matches!(lookahead, TokenKind::EQUAL)
                      || diffuse
                        && matches!(
                          lookahead,
                          TokenKind::Keyword(Keyword::Comma | Keyword::Semicolon)
                        )
                    {
                      let var = Box::new(Variable {
                        pos: tok.pos,
                        var: None,
                        spelling: tok.spelling.into(),
                      });
                      return Ok(if matches!(lookahead, TokenKind::EQUAL) {
                        this.scan.next();
                        TakeDecl { var: Some(var), term: this.parse_term()? }
                      } else {
                        TakeDecl { term: Box::new(var.to_term()), var: Some(var) }
                      })
                    } else {
                      this.scan.undo(tok);
                    }
                  }
                  Ok(TakeDecl { var: None, term: this.parse_term()? })
                })),
              TokenKind::Keyword(Keyword::Hereby) => {
                let (items, end) = this.parse_proof(true)?;
                ItemKind::Thus(Statement::Now { end, label: None, items })
              }
              TokenKind::Keyword(Keyword::Hence) => ItemKind::Thus(this.parse_stmt(Some(start))?),
              TokenKind::Keyword(Keyword::Thus) => {
                let link = this.parse_then();
                ItemKind::Thus(this.parse_stmt(link)?)
              }
              _ => this.parse_block_item(start, tok)?,
            };
            this.scan.accept(Keyword::Semicolon)?;
            Ok(kind)
          });
          items.push(Item { pos: start, kind })
        }
      }
    };
    Ok((items, end))
  }

  fn parse_block_item(&mut self, pos: Span, tok: Token<'a>) -> PResult<ItemKind> {
    Ok(match tok.kind {
      TokenKind::Keyword(Keyword::Let) => {
        let vars = self.parse_binders()?;
        let conds = if self.scan.try_accept(Keyword::Such) {
          self.scan.accept(Keyword::That)?;
          self.separated_skip(Keyword::And, |this| this.parse_proposition())
        } else {
          vec![]
        };
        ItemKind::Let { vars, conds }
      }
      TokenKind::Keyword(Keyword::Given) => {
        let (vars, conds) = self.parse_choice()?;
        ItemKind::Given { vars, conds }
      }
      TokenKind::Keyword(Keyword::Unfolding) => ItemKind::Unfold(self.parse_references()),
      TokenKind::Keyword(Keyword::Assume) => ItemKind::Assume(self.parse_assumption(pos)?),
      _ => {
        self.scan.undo(tok);
        self.parse_stmt_item()?
      }
    })
  }

  fn parse_block(&mut self, kind: BlockKind) -> PResult<ItemKind> {
    let mut items = vec![];
    let block_kind = kind;
    let end = loop {
      let tok = self.scan.next();
      let start = tok.pos;
      match tok.kind {
        TokenKind::Keyword(Keyword::End) => break tok.end(),
        // Unterminated block at end of file: report and stop rather than looping on the
        // idempotent `Eof` token (see `parse_proof`).
        TokenKind::Eof => {
          self.scan.err(start, ParseErr::Expected(ExpectedTok::Other("'end'".into())));
          break start
        }
        TokenKind::Pragma => {
          let pragma = tok.spelling[2..].parse().unwrap();
          items.push(Item { pos: start, kind: ItemKind::Pragma(pragma) });
          continue
        }
        _ => {}
      }
      let item_kind = self.recover_block_item(start.start, |this| {
        let mut tok = tok;
        let redef = match tok.kind {
          TokenKind::Keyword(Keyword::Redefine) => {
            tok = this.scan.next();
            if !matches!(
              tok.kind,
              TokenKind::Keyword(Keyword::Mode | Keyword::Attr | Keyword::Func | Keyword::Pred)
            ) {
              return Err(this.scan.err(tok.pos, ParseErr::ExpectedRedefKind))
            }
            true
          }
          _ => false,
        };
        let kind = match (tok.kind, block_kind) {
          (TokenKind::Keyword(Keyword::Mode), BlockKind::Definition) => {
            let pat = this.parse_pattern()?;
            let Pattern::Mode(pat) = pat else {
              return Err(this.scan.err(pat.pos(), ParseErr::ExpectedPattern(PatKind::Mode)))
            };
            let kind = if this.scan.try_accept(Keyword::Is) {
              DefModeKind::Expandable { expansion: this.parse_type()? }
            } else {
              let spec =
                if this.scan.try_accept(Keyword::Arrow) { Some(this.parse_type()?) } else { None };
              DefModeKind::Standard { spec, def: None }
            };
            this.parse_definition(redef, DefinitionKind::Mode { pat, kind })?
          }
          (TokenKind::Keyword(Keyword::Attr), BlockKind::Definition) => {
            let pat = this.parse_pattern()?;
            let Pattern::Attr(pat) = pat else {
              return Err(this.scan.err(pat.pos(), ParseErr::ExpectedPattern(PatKind::Attr)))
            };
            this.parse_definition(redef, DefinitionKind::Attr { pat, def: None })?
          }
          (TokenKind::Keyword(Keyword::Func), BlockKind::Definition) => {
            let pat = this.parse_pattern()?;
            let Pattern::Func(pat) = pat else {
              return Err(this.scan.err(pat.pos(), ParseErr::ExpectedPattern(PatKind::Func)))
            };
            let spec =
              if this.scan.try_accept(Keyword::Arrow) { Some(this.parse_type()?) } else { None };
            this.parse_definition(redef, DefinitionKind::Func { pat, spec, def: None })?
          }
          (TokenKind::Keyword(Keyword::Pred), BlockKind::Definition) => {
            let pat = this.parse_pattern()?;
            let Pattern::Pred(pat) = pat else {
              return Err(this.scan.err(pat.pos(), ParseErr::ExpectedPattern(PatKind::Pred)))
            };
            this.parse_definition(redef, DefinitionKind::Pred { pat, def: None })?
          }
          (TokenKind::Keyword(Keyword::Struct), BlockKind::Definition) => {
            let parents;
            if this.scan.try_accept(TokenKind::LPAREN) {
              parents = this.comma_separated(|this| this.parse_type().map(|t| *t));
              this.scan.accept(TokenKind::RPAREN)?;
            } else {
              parents = vec![]
            }
            let tok = this.scan.next();
            let TokenKind::Symbol(SymbolKind::Struct(sym)) = tok.kind else {
              return Err(this.scan.err(tok.pos, ParseErr::ExpectedStructSymbol))
            };
            let args = if this.scan.try_accept(Keyword::Over) {
              this.comma_separated_skip(|this| this.parse_variable())
            } else {
              vec![]
            };
            let pat = PatternStruct { sym, spelling: tok.spelling.to_owned(), args };
            this.scan.accept(Keyword::AggrLeftBrk)?;
            this.allow_internal_selector = true;
            let fields = this.comma_separated_skip(|this| {
              let pos = this.scan.peek().pos;
              let vars = this.comma_separated_skip(|this| {
                let tok = this.scan.next();
                let TokenKind::Symbol(SymbolKind::Sel(sym)) = tok.kind else {
                  return Err(this.scan.err(tok.pos, ParseErr::ExpectedSelectorSymbol))
                };
                Ok(Field { pos, sym, spelling: tok.spelling.into() })
              });
              this.scan.accept(Keyword::Arrow)?;
              Ok(FieldGroup { pos, vars, ty: *this.parse_type()? })
            });
            this.scan.accept(Keyword::AggrRightBrk)?;
            this.scan.accept(Keyword::Semicolon)?;
            this.allow_internal_selector = false;
            let def = DefStruct { parents, pat, fields };
            ParserCore::after_def_struct(tok.pos, &def, |pos, fmt| this.push_format(pos, fmt));
            ItemKind::DefStruct(Box::new(def))
          }
          (TokenKind::Keyword(Keyword::Synonym | Keyword::Antonym), BlockKind::Notation) => {
            let positive = tok.kind == TokenKind::Keyword(Keyword::Synonym);
            let new = this.parse_pattern()?;
            this.scan.accept(Keyword::For)?;
            let orig = this.parse_pattern()?;
            this.scan.accept(Keyword::Semicolon)?;
            ItemKind::PatternRedef(match (new, orig) {
              (Pattern::Pred(new), Pattern::Pred(orig)) => {
                this.push_format(new.pos, Format::Pred(new.to_format()));
                PatternRedef::Pred { new, orig, positive }
              }
              (Pattern::Func(new), Pattern::Func(orig)) if positive => {
                this.push_format(new.pos(), Format::Func(new.to_format()));
                PatternRedef::Func { new, orig }
              }
              (Pattern::Mode(new), Pattern::Mode(orig)) if positive => {
                this.push_format(new.pos, Format::Mode(new.to_format()));
                PatternRedef::Mode { new, orig }
              }
              (Pattern::Attr(new), Pattern::Attr(orig)) => {
                this.push_format(new.pos, Format::Attr(new.to_format()));
                PatternRedef::Attr { new, orig, positive }
              }
              (Pattern::Func(_), Pattern::Func(_)) | (Pattern::Mode(_), Pattern::Mode(_)) =>
                return Err(this.scan.err(start, ParseErr::AntonymNotAllowed)),
              (_, rhs) => return Err(this.scan.err(rhs.pos(), ParseErr::PatternTypeMismatch)),
            })
          }
          (TokenKind::Keyword(Keyword::Cluster), BlockKind::Registration) => {
            let kind = match this.parse_attrs_or_type_or_term(false, true)? {
              Ok((attrs, _)) => {
                let tok = this.scan.next();
                match tok.kind {
                  TokenKind::Keyword(Keyword::Arrow) => {
                    let concl = this.parse_attrs_or_type_or_term(false, false)?.unwrap().0;
                    this.scan.accept(Keyword::For)?;
                    ClusterDeclKind::Cond { antecedent: attrs, concl, ty: this.parse_type()? }
                  }
                  TokenKind::Keyword(Keyword::For) =>
                    ClusterDeclKind::Exist { concl: attrs, ty: this.parse_type()? },
                  _ => return Err(this.scan.err(tok.pos, ParseErr::ExpectedArrowOrFor)),
                }
              }
              Err(term) => {
                this.scan.accept(Keyword::Arrow)?;
                let concl = this.parse_attrs_or_type_or_term(false, false)?.unwrap().0;
                let ty =
                  if this.scan.try_accept(Keyword::For) { Some(this.parse_type()?) } else { None };
                ClusterDeclKind::Func { term, concl, ty }
              }
            };
            this.scan.accept(Keyword::Semicolon)?;
            let (conds, corr) = this.parse_corr_conds()?;
            ItemKind::Cluster(Box::new(Cluster { kind, conds, corr }))
          }
          (TokenKind::Keyword(Keyword::Reduce), BlockKind::Registration) => {
            let from = this.parse_term()?;
            this.scan.accept(Keyword::To)?;
            let to = this.parse_term()?;
            this.scan.accept(Keyword::Semicolon)?;
            let (conds, corr) = this.parse_corr_conds()?;
            ItemKind::Reduction(Box::new(Reduction { from, to, conds, corr }))
          }
          (TokenKind::Keyword(Keyword::Identify), BlockKind::Registration) => {
            let lhs = this.parse_pattern()?;
            this.scan.accept(Keyword::With)?;
            let rhs = this.parse_pattern()?;
            let eqs = if this.scan.try_accept(Keyword::When) {
              this.comma_separated_skip(|this| {
                let lhs = this.parse_variable()?;
                this.scan.accept(TokenKind::EQUAL)?;
                Ok((lhs, this.parse_variable()?))
              })
            } else {
              vec![]
            };
            this.scan.accept(Keyword::Semicolon)?;
            let (conds, corr) = this.parse_corr_conds()?;
            match (lhs, rhs) {
              (Pattern::Func(lhs), Pattern::Func(rhs)) =>
                ItemKind::IdentifyFunc(Box::new(IdentifyFunc { lhs, rhs, eqs, conds, corr })),
              (Pattern::Pred(_), Pattern::Pred(_))
              | (Pattern::Attr(_), Pattern::Attr(_))
              | (Pattern::Mode(_), Pattern::Mode(_)) =>
                return Err(this.scan.err(start, ParseErr::UnsupportedIdentification)),
              (_, rhs) => return Err(this.scan.err(rhs.pos(), ParseErr::PatternTypeMismatch)),
            }
          }
          (TokenKind::Property(PropertyKind::Sethood), BlockKind::Registration) => {
            this.scan.accept(Keyword::Of)?;
            let ty = this.parse_type()?;
            let just = Box::new(this.parse_justification_semi(None)?);
            ItemKind::SethoodRegistration { ty, just }
          }
          (TokenKind::Property(prop), BlockKind::Registration) =>
            return Err(this.scan.err(start, ParseErr::IllegalPropertyRegistration(prop))),
          _ => {
            let kind = this.parse_block_item(start, tok)?;
            this.scan.accept(Keyword::Semicolon)?;
            kind
          }
        };
        Ok(kind)
      });
      items.push(Item { pos: start, kind: item_kind })
    };
    self.scan.accept(Keyword::Semicolon)?;
    Ok(ItemKind::Block { end, kind, items })
  }

  fn parse_reservation(&mut self) -> PResult<ItemKind> {
    let ress = self.comma_separated_skip(|this| {
      let vars = this.comma_separated_skip(|this| this.parse_variable());
      this.scan.accept(Keyword::For)?;
      Ok(Reservation { vars, tys: None, ty: this.parse_type()?, fvars: None })
    });
    self.scan.accept(Keyword::Semicolon)?;
    Ok(ItemKind::Reservation(ress))
  }

  pub fn push_parse_item(&mut self, buf: &mut Vec<Item>) -> bool {
    let tok = self.scan.next();
    if let TokenKind::Eof = tok.kind {
      return false
    }
    let result = (|this: &mut Self| -> PResult<ItemKind> {
      Ok(match tok.kind {
        TokenKind::Pragma => ItemKind::Pragma(tok.spelling[2..].parse().unwrap()),
        TokenKind::Keyword(Keyword::Begin) => ItemKind::Section,
        TokenKind::Keyword(Keyword::Scheme) => ItemKind::SchemeBlock(this.parse_scheme()?),
        TokenKind::Keyword(Keyword::Definition) => this.parse_block(BlockKind::Definition)?,
        TokenKind::Keyword(Keyword::Notation) => this.parse_block(BlockKind::Notation)?,
        TokenKind::Keyword(Keyword::Registration) => this.parse_block(BlockKind::Registration)?,
        TokenKind::Keyword(Keyword::Reserve) => this.parse_reservation()?,
        TokenKind::Keyword(Keyword::Theorem) => {
          // Recover a bad theorem body into a labeled sorry: the label still gets
          // declared (so later references resolve) but the statement is an error
          // value, so the checker leaves it as an unproven sorry.
          let label = this.parse_label();
          match this.parse_formula() {
            Ok(f) => ItemKind::Theorem {
              prop: Box::new(Proposition { label, f: *f }),
              just: Box::new(this.parse_justification_semi(None)?),
            },
            Err(_) => {
              this.recover_to(Keyword::Semicolon);
              this.scan.try_accept(Keyword::Semicolon);
              ItemKind::Theorem {
                prop: Box::new(Proposition { label, f: Formula::Error { pos: tok.pos } }),
                just: Box::new(Justification::Inference {
                  pos: tok.pos,
                  kind: InferenceKind::By { link: None },
                  refs: vec![],
                }),
              }
            }
          }
        }
        _ => {
          this.scan.undo(tok);
          let kind = this.parse_stmt_item()?;
          this.scan.accept(Keyword::Semicolon)?;
          kind
        }
      })
    })(self);
    let item = match result {
      Ok(kind) => {
        let item = Item { pos: tok.pos, kind };
        self.core.write_json.on(|w| w.write_item(&item));
        item
      }
      Err(_) => {
        // A diagnostic was already reported; resynchronize to the next `;` so the
        // following item can parse. This loop consumes `tok` up front but arms
        // that `undo` it can land recovery back on it, so make progress explicit.
        self.recover_to(Keyword::Semicolon);
        self.scan.try_accept(Keyword::Semicolon);
        if self.ensure_progress(tok.pos.start) {
          // The dropped token may carry its own terminator (a stray `end;`);
          // take it too rather than starting a bogus item on the `;`.
          self.scan.try_accept(Keyword::Semicolon);
        }
        Item { pos: tok.pos, kind: ItemKind::Error }
      }
    };
    buf.push(item);
    true
  }
}
