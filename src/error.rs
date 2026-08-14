use crate::parser::ParseError;
use crate::types::{Article, CorrCondKind, DirectiveKind, PropertyKind};
use crate::{Diagnostic, Global, Reporter, Severity, Span};
use std::path::{Path, PathBuf};

impl ParseError {
  /// A diagnostic for this failure, positioned within `path`. Reader/accommodator
  /// errors are about a *different* file than the article, so they carry their own
  /// path; going through [`Diagnostic`] keeps them in the same sink (and counted)
  /// rather than out-of-band on stderr.
  pub fn to_diagnostic(&self, path: &Path) -> Diagnostic {
    Diagnostic::in_file(Severity::Error, path.to_owned(), self.pos(), self.to_string())
  }

  pub fn report(self, reporter: &dyn Reporter, path: &Path) {
    reporter.emit(self.to_diagnostic(path))
  }
}

/// A missing/empty imported directive. Unlike a parse failure this *is* positioned
/// in the article (at the `environ` directive), so it renders with a source snippet.
pub fn accom_warning(kind: DirectiveKind, path: PathBuf, art: Article, pos: Span) -> Diagnostic {
  Diagnostic::warning(
    pos,
    format!(
      "{kind} for {art} not found or empty (looked in {path})",
      kind = kind.name(),
      path = path.to_string_lossy()
    ),
  )
}

/// Everything that can be reported, as structured data rather than a rendered
/// string. A [`Diagnostic`] carries one of these, so a reporter can render it for
/// a human ([`std::fmt::Display`]) *or* map it to a legacy error number
/// ([`DiagKind::mizar`]) for a Mizar-compatible `.err` file.
///
/// Payloads that need context to render (a [`Formula`] needs a `LocalContext` to
/// pretty-print) are stored pre-rendered as `String`, since only the emission site
/// has that context.
#[derive(Debug)]
pub enum DiagKind {
  /// A syntax or well-formedness error from the `.miz` parser.
  Parse(crate::parser::ParseErr),
  /// An error from the analyzer/checker.
  Analyze(MizError),
  /// A malformed dependency file or pre-accommodated artifact.
  Read(ParseError),
  /// Not yet structured. The parser's syntax errors still take this path; they
  /// render fine but carry no legacy code.
  Msg(String),
}

impl std::fmt::Display for DiagKind {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      DiagKind::Parse(e) => e.fmt(f),
      DiagKind::Analyze(e) => e.fmt(f),
      DiagKind::Read(e) => e.fmt(f),
      DiagKind::Msg(s) => f.write_str(s),
    }
  }
}

impl DiagKind {
  /// The legacy Mizar error number, for `.err` output. `None` where we report
  /// something Mizar has no code for (or where the mapping is not yet done).
  pub fn mizar(&self) -> Option<u32> {
    match self {
      DiagKind::Parse(e) => e.code(),
      DiagKind::Analyze(e) => e.mizar(),
      DiagKind::Read(_) | DiagKind::Msg(_) => None,
    }
  }
}

impl From<crate::parser::ParseErr> for DiagKind {
  fn from(e: crate::parser::ParseErr) -> Self { DiagKind::Parse(e) }
}
impl From<MizError> for DiagKind {
  fn from(e: MizError) -> Self { DiagKind::Analyze(e) }
}
impl From<ParseError> for DiagKind {
  fn from(e: ParseError) -> Self { DiagKind::Read(e) }
}
impl From<String> for DiagKind {
  fn from(s: String) -> Self { DiagKind::Msg(s) }
}
impl From<&str> for DiagKind {
  fn from(s: &str) -> Self { DiagKind::Msg(s.to_string()) }
}

#[derive(Debug)]
pub enum MizError {
  UnexpectedPragma(String),
  /// The pretty-printed formula, rendered at the emission site.
  IterEqualityNotAnEquality(String),
  MissingReference(String),
  MissingScheme(String),
  NotADefinition,
  InaccessibleDefinition,
  /// Carries the pretty-printed thesis (the user cannot see it otherwise).
  ThesisNotExpandable(String),
  /// Carries the pretty-printed thesis.
  BadUnfold(String),
  /// Carries the pretty-printed thesis.
  ThesisMismatch(String),
  /// The pretty-printed unproved thesis, rendered at the emission site.
  IncompleteProof(String),
  MissingCorrectness(CorrCondKind),
  InapplicableProperty(PropertyKind),
  UnsupportedProperty(PropertyKind),
  /// Carries the pretty-printed thesis.
  BadVarIntro(String),
  /// Carries the pretty-printed thesis.
  VarTypeMismatch(String),
  /// No applicable notation for a *use* of a constructor: the symbol resolved but
  /// no pattern accepted these argument types. One variant per constructor kind,
  /// mirroring the legacy codes 101-106.
  UnknownMode,
  UnknownPredicate,
  UnknownFunctor,
  UnknownStructure,
  UnknownAttribute,
  IllegalProjection,
  /// No pattern found for the original a definition or notation redefines. The
  /// legacy analyzer distinguishes these from the use-site cases above (112-115).
  RedefUnknownPredicate,
  RedefUnknownFunctor,
  RedefUnknownMode,
  RedefUnknownAttribute,
  /// A redefinition's specified type is not a subtype of the inherited one.
  InvalidSpecification,
  /// A private-predicate or scheme-predicate application whose argument types do
  /// not match the declaration.
  ArgTypeMismatch,
  /// A scheme application whose premises do not match the scheme's.
  SchemeMismatch,
  /// A property whose declaration requires a relationship between the result type
  /// and the argument types that does not hold.
  PropertyTypeMismatch(PropertyKind),
  /// A correctness condition was stated that this definition does not require.
  UnexpectedCorrCond(CorrCondKind),
  /// A `case` that cannot be matched against the thesis. Carries the pp'd thesis.
  InvalidCase(String),
  /// A constant from an enclosing scope survived into a generalized item.
  NongeneralizableVariable,
  /// A linked inference (`then`) with no preceding statement to link to.
  NothingToLink,
  /// A pattern declares a locus that its visible arguments never use.
  UnusedLocus,
  /// A reserved variable appears where reservations cannot be expanded.
  ReservedVarNotAllowed,
  /// A variable that name resolution could not resolve. Name checking reports this
  /// first; this covers the analyzer reaching one anyway.
  UnknownVariable(String),
  /// An exported item (theorem, reservation, scheme, definition) mentions something
  /// scope-local: a constant, or a private functor/predicate.
  NotExportable,
  InconsistentType,
  UnregisteredCluster,
  NotSethood,
  MissingVarType,
  NotAStructParent,
  DuplicateField,
  BadFunctorRegistration,
  BadReduction,
  UnexpectedIt,
  BadNowStep,
  IncompleteCases,
  InconsistentCluster,
  UnresolvedPrivFunc(String),
  UnresolvedPrivPred(String),
  FieldTypeMismatch,
  UnexpectedThesis,
  /// A flexary conjunction (`a = … = b`) needs the `NUMERALS`/`REAL` requirements,
  /// which this article's `requirements` directive did not load.
  FlexaryRequirement,
  /// A flexary conjunction (`a = … = b`) whose two sides do not differ in exactly one
  /// place with a `natural`-numbered boundary, so the `…` cannot be expanded.
  BadFlexary,
  /// A structure field's type refers to `the <selector>` for a selector that is not a
  /// field of this structure (or not yet declared at that point).
  NoSuchField,
  /// A structure does not re-list a field it inherits from one of its parents.
  StructMissingParentField,
  /// A field is inherited from two parents as different selectors, so it is ambiguous.
  AmbiguousParentField,
  /// The branches of a `now … per cases` reasoning conclude different theses.
  InconsistentCaseThesis,
  /// A predicate/mode/attribute definiens was given with `equals` (a term) where a
  /// formula (`means`) is required.
  DefiniensMustBeFormula,
  /// A definition or registration has more parameters than the checker can track (≥64).
  TooManyLoci,
  /// An `identify … with … when …` clause whose two patterns cannot be paired up:
  /// an equated argument is not one-left-one-right, the arities differ, or the paired
  /// argument types are incompatible.
  BadIdentify,
  /// An item that is not allowed in the block it appears in (e.g. `unfolding` outside
  /// a proof).
  UnexpectedItem,
  /// A reference in a justification (`by`/`from`) that does not resolve to any
  /// statement, theorem, or definition in scope — e.g. a theorem number that is out
  /// of range for the imported article. Detected in the checker, where the analyzer
  /// only verified the article was imported, not that the specific item exists.
  UnresolvedReference,
}

impl MizError {
  pub fn report(self, pos: Span, g: &Global) -> crate::ErrorReported {
    g.reporter.error(Diagnostic::error(pos, self))
  }

  /// The legacy Mizar error number from `mizar.msg`, where one corresponds.
  ///
  /// Many-to-one is normal and matches the Pascal system, which gives each *site*
  /// a name (`paIdentExp1`..`paIdentExp13`) but collapses them onto one code (300).
  /// `None` means we report something Mizar has no code for.
  pub fn mizar(&self) -> Option<u32> {
    Some(match self {
      MizError::IterEqualityNotAnEquality(_) => 62, // Free variables not allowed in an iterative equality // approximate
      MizError::MissingReference(_) => 144,         // Unknown label
      MizError::UnresolvedReference => 144,         // Unknown label/reference // approximate
      MizError::MissingScheme(_) => 191, // Check if scheme is in "schemes" ... // approximate
      MizError::NotADefinition => 288,   // A reference to a definitional theorem required
      MizError::InaccessibleDefinition => 199, // Inaccessible definitional theorem
      MizError::ThesisNotExpandable(_) => 61, // Thesis is not expandable
      MizError::ThesisMismatch(_) => 51, // Invalid conclusion // approximate
      MizError::IncompleteProof(_) => 70, // Something remains to be proved
      MizError::MissingCorrectness(_) => 73, // Correctness condition missing
      MizError::BadVarIntro(_) => 55,    // Invalid generalization // approximate
      MizError::VarTypeMismatch(_) => 56, // Disagreement of types // approximate
      MizError::UnknownMode => 101,      // Unknown mode
      MizError::UnknownPredicate => 102, // Unknown predicate
      MizError::UnknownFunctor => 103,   // Unknown functor
      MizError::UnknownStructure => 104, // Unknown structure
      MizError::IllegalProjection => 105, // Illegal projection
      MizError::UnknownAttribute => 106, // Unknown attribute
      MizError::RedefUnknownPredicate => 112, // Unknown predicate
      MizError::RedefUnknownFunctor => 113, // Unknown functor
      MizError::RedefUnknownMode => 114, // Unknown mode
      MizError::RedefUnknownAttribute => 115, // Unknown attribute
      MizError::InvalidSpecification => 117, // Invalid specification
      MizError::ArgTypeMismatch => 120,  // Disagreement of argument types
      MizError::SchemeMismatch => 20,    // The structure of the sentences disagrees with the scheme
      MizError::PropertyTypeMismatch(_) => 85, // The result type must widen to the type of the argument
      MizError::UnexpectedCorrCond(_) => 72,   // Unexpected correctness condition
      MizError::InvalidCase(_) => 53,          // Invalid case
      MizError::NongeneralizableVariable => 50, // Nongeneralizable variable in the skeleton of a reasoning
      MizError::NothingToLink => 164,           // Nothing to link
      MizError::UnusedLocus => 100,             // Unused locus
      MizError::ReservedVarNotAllowed => 160, // This variable still cannot be accessed // approximate
      MizError::UnknownVariable(_) => 140,    // Unknown variable
      MizError::NotExportable => 50, // Nongeneralizable variable in the skeleton of a reasoning // approximate
      MizError::UnregisteredCluster => 111, // Non registered attribute cluster
      MizError::NotSethood => 86,    // It is only meaningful for sethood property // approximate
      MizError::NotAStructParent => 94, // Prefix must be a structure // approximate
      MizError::DuplicateField => 91, // Homonymic fields in structure declaration
      MizError::FieldTypeMismatch => 92, // Type of the field must be equal to the type in prefix
      MizError::BadFunctorRegistration => 96, // Only standard functors and selectors ... // approximate
      MizError::UnexpectedIt => 80, // Cannot be used in a permissive definition // approximate
      MizError::IncompleteCases => 54, // The cases are not exhausted
      MizError::InconsistentCluster => 95, // Inconsistent cluster
      MizError::InconsistentType => 95, // Inconsistent cluster // approximate
      MizError::UnresolvedPrivFunc(_) => 148, // Unknown private functor
      MizError::UnresolvedPrivPred(_) => 149, // Unknown private predicate
      MizError::UnexpectedThesis => 65, // "thesis" is only allowed inside a proof
      MizError::MissingVarType => 140, // Unknown variable // approximate
      MizError::BadReduction => 258, // Global choice and Fraenkel terms are not allowed in reductions // approximate
      MizError::BadNowStep => 64, // Invalid exemplification in a diffuse statement // approximate
      MizError::InapplicableProperty(_) => 81, // It is only meaningful for binary predicates // approximate
      MizError::UnsupportedProperty(_) => 77,  // Still not implemented // approximate
      MizError::BadUnfold(_) => 67,            // Expanded definition does not match thesis
      MizError::NoSuchField => 90, // This field is not present in the prefix // approximate
      MizError::StructMissingParentField => 90, // This field is not present in the prefix // approximate
      MizError::AmbiguousParentField => 91, // Homonymic fields in structure declaration // approximate
      MizError::InconsistentCaseThesis => 53, // Invalid case // approximate
      MizError::BadIdentify => 120,         // Disagreement of argument types // approximate
      // No clear legacy counterpart for these.
      MizError::FlexaryRequirement
      | MizError::BadFlexary
      | MizError::DefiniensMustBeFormula
      | MizError::TooManyLoci
      | MizError::UnexpectedItem => return None,
      // No legacy counterpart at all: Mizar has no pragma diagnostic of this shape.
      MizError::UnexpectedPragma(_) => return None,
    })
  }
}

impl std::fmt::Display for MizError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let msg = match self {
      MizError::UnexpectedPragma(pragma) => format!("unknown pragma '{pragma}'"),
      MizError::IterEqualityNotAnEquality(it) =>
        format!("an iterative-equality step must be an equality 'a = b', but this is: {it}"),
      MizError::MissingReference(name) =>
        format!("unknown label '{name}': no statement with this label is in scope here"),
      MizError::MissingScheme(name) =>
        format!("unknown scheme '{name}': no such scheme is in scope (is it in your 'schemes' directive?)"),
      MizError::NotADefinition =>
        "this reference is a theorem, not a definition; 'unfolding' needs a definition like 'ART:def 3'".to_string(),
      MizError::InaccessibleDefinition =>
        "this definition cannot be reached: it is not imported, or its number is out of range".to_string(),
      MizError::ThesisNotExpandable(thesis) => format!(
        "the thesis cannot be unfolded here: only an atomic statement (a single predicate, \
         attribute, or 'is') can be expanded, but the thesis is: {thesis}"
      ),
      MizError::BadUnfold(thesis) => format!(
        "the named definition does not expand the goal: what it expands to does not match the \
         thesis: {thesis}"
      ),
      MizError::ThesisMismatch(thesis) =>
        format!("this does not match what remains to be proved; the thesis is: {thesis}"),
      MizError::IncompleteProof(thesis) =>
        format!("the proof ends but part of the goal is still unproved: {thesis}"),
      MizError::MissingCorrectness(kind) => format!(
        "this definition needs a correctness proof for '{}', but none was given",
        String::from_utf8_lossy(kind.name())
      ),
      MizError::InapplicableProperty(kind) =>
        format!("the {kind:?} property does not apply to a definition of this shape"),
      MizError::UnsupportedProperty(kind) => format!("the {kind:?} property is not supported here"),
      MizError::BadVarIntro(thesis) => format!(
        "cannot introduce a variable with 'let' here: the thesis is not a universal statement \
         ('for … holds …'); it is: {thesis}"
      ),
      MizError::VarTypeMismatch(ty) => format!(
        "the type of this variable does not match the type the thesis quantifies over: expected {ty}"
      ),
      MizError::UnknownMode => "unknown mode: no applicable notation for these argument types".to_string(),
      MizError::UnknownPredicate =>
        "unknown predicate: no applicable notation for these argument types".to_string(),
      MizError::UnknownFunctor =>
        "unknown functor: no applicable notation for these argument types".to_string(),
      MizError::UnknownStructure =>
        "unknown structure: no applicable notation for these argument types".to_string(),
      MizError::UnknownAttribute =>
        "unknown attribute: no applicable notation for these argument types".to_string(),
      MizError::IllegalProjection =>
        "illegal projection: this term has no such field for this argument type".to_string(),
      MizError::RedefUnknownPredicate =>
        "unknown predicate: nothing matching is available to redefine".to_string(),
      MizError::RedefUnknownFunctor =>
        "unknown functor: nothing matching is available to redefine".to_string(),
      MizError::RedefUnknownMode =>
        "unknown mode: nothing matching is available to redefine".to_string(),
      MizError::RedefUnknownAttribute =>
        "unknown attribute: nothing matching is available to redefine".to_string(),
      MizError::InvalidSpecification =>
        "invalid specification: the specified type is not a subtype of the one it redefines"
          .to_string(),
      MizError::ArgTypeMismatch =>
        "the argument types here do not match the declared parameter types".to_string(),
      MizError::SchemeMismatch =>
        "the premises supplied do not match this scheme's assumptions".to_string(),
      MizError::PropertyTypeMismatch(kind) =>
        format!("the {kind:?} property requires the result type to match the argument type, but it does not"),
      MizError::UnexpectedCorrCond(kind) => format!(
        "a '{}' correctness proof was given, but this definition does not require one",
        String::from_utf8_lossy(kind.name())
      ),
      MizError::InvalidCase(thesis) =>
        format!("this case does not correspond to any case of the thesis; the thesis is: {thesis}"),
      MizError::NongeneralizableVariable =>
        "this uses a variable from an inner scope that cannot be generalized out to here".to_string(),
      MizError::NothingToLink =>
        "'then' has nothing to link to: there is no preceding statement in this reasoning block"
          .to_string(),
      MizError::UnusedLocus =>
        "this parameter is declared but never used by the pattern"
          .to_string(),
      MizError::ReservedVarNotAllowed =>
        "a reserved variable cannot appear here; reservations are only expanded in statements"
          .to_string(),
      MizError::UnknownVariable(name) =>
        format!("unknown variable '{name}': it was never introduced (e.g. with 'let') or reserved"),
      MizError::NotExportable =>
        "this cannot be exported: it mentions a local constant or private functor/predicate"
          .to_string(),
      MizError::InconsistentType =>
        "inconsistent type: the attributes are contradictory".to_string(),
      MizError::UnregisteredCluster =>
        "this attributed type is not known to be non-empty: no registration guarantees an object with all these attributes exists".to_string(),
      MizError::NotSethood =>
        "this type does not have the 'sethood' property, so it cannot range over a set built with '{ … where … }'".to_string(),
      MizError::MissingVarType =>
        "this variable has no type: give it one (e.g. 'let x be set') or 'reserve' it".to_string(),
      MizError::NotAStructParent =>
        "a structure can only extend a plain structure type (no attributes on the parent)".to_string(),
      MizError::DuplicateField =>
        "two fields of this structure have the same name".to_string(),
      MizError::BadFunctorRegistration =>
        "the target of this registration must be a functor term, a structure constructor, or a field access".to_string(),
      MizError::BadReduction =>
        "a reduction must rewrite a functor term to one of its own subterms".to_string(),
      MizError::UnexpectedIt =>
        "'it' can only be used inside a definition, where it stands for the object being defined"
          .to_string(),
      MizError::BadNowStep =>
        "this kind of step is not allowed inside a 'now' reasoning block".to_string(),
      MizError::IncompleteCases =>
        "these cases do not cover the thesis: some case of the goal is left unproved".to_string(),
      MizError::InconsistentCluster =>
        "these attributes are inconsistent: they contradict each other".to_string(),
      MizError::UnresolvedPrivFunc(name) =>
        format!("unknown private functor '{name}': no 'deffunc' with this name is in scope"),
      MizError::UnresolvedPrivPred(name) =>
        format!("unknown private predicate '{name}': no 'defpred' with this name is in scope"),
      MizError::FieldTypeMismatch =>
        "this field is inherited from a parent structure but redeclared at an incompatible type"
          .to_string(),
      MizError::UnexpectedThesis =>
        "'thesis' can only be used inside a proof, where it names the goal of the current block"
          .to_string(),
      MizError::FlexaryRequirement =>
        "a '…' abbreviation needs the number requirements: add 'requirements NUMERALS, REAL;' to the environment"
          .to_string(),
      MizError::BadFlexary =>
        "this '…' abbreviation could not be expanded: the two sides must differ in exactly one place, at a boundary indexed by a natural number".to_string(),
      MizError::NoSuchField =>
        "this refers to a field that the structure does not have (or that is not yet declared at this point)".to_string(),
      MizError::StructMissingParentField =>
        "this structure does not list every field it inherits from its parent structures".to_string(),
      MizError::AmbiguousParentField =>
        "this field is inherited from more than one parent structure as different fields, so it is ambiguous".to_string(),
      MizError::InconsistentCaseThesis =>
        "the branches of this 'per cases' reasoning prove different statements".to_string(),
      MizError::DefiniensMustBeFormula =>
        "this definition must be given with 'means' (a formula), not 'equals' (a term)".to_string(),
      MizError::TooManyLoci =>
        "this definition has too many parameters to check (the limit is 64)".to_string(),
      MizError::BadIdentify =>
        "the two patterns of this 'identify' cannot be matched up: their arguments must pair one-to-one, left with right, at compatible types".to_string(),
      MizError::UnexpectedItem =>
        "this item is not allowed here (for example, 'unfolding' only inside a proof, or a definition outside a definition block)".to_string(),
      MizError::UnresolvedReference =>
        "this reference does not resolve to a statement, theorem, or definition in scope (is the number in range for the imported article?)".to_string(),
    };
    f.write_str(&msg)
  }
}
