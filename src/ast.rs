use crate::mk_id;
use crate::types::*;
use serde_derive::Serialize;
use std::rc::Rc;
use std::str::FromStr;

#[derive(Clone, Debug, Serialize)]
pub struct Variable {
  pub pos: Position,
  /// 'varnr' attribute, MSLocusObj.nVarNr, MSVariableObj.nVarNr
  #[serde(skip_serializing_if = "Option::is_none")]
  pub var: Option<ConstId>,
  pub spelling: Rc<str>,
}

impl Variable {
  #[track_caller]
  pub fn var(&self) -> ConstId { self.var.expect("variable is not resolved") }

  pub fn to_term(&self) -> Term {
    Term::Var {
      pos: self.pos,
      kind: self.var.map(VarKind::Const),
      spelling: (*self.spelling).into(),
    }
  }
}

#[derive(Copy, Clone, Debug, Serialize)]
pub enum VarKind {
  Bound(BoundId),
  Const(ConstId),
  Reserved(ReservedId),
}

#[derive(Copy, Clone, Debug, Serialize)]
pub enum PrivFuncKind {
  PrivFunc(PrivFuncId),
  SchFunc(SchFuncId),
}

#[derive(Debug, Serialize)]
pub enum Term {
  Placeholder {
    pos: Position,
    nr: LocusId,
  },
  Numeral {
    pos: Position,
    value: u32,
  },
  Var {
    pos: Position,
    #[serde(skip_serializing_if = "Option::is_none")]
    kind: Option<VarKind>,
    spelling: String,
  },
  PrivFunc {
    pos: Position,
    #[serde(skip_serializing_if = "Option::is_none")]
    kind: Option<PrivFuncKind>,
    spelling: Rc<str>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    args: Vec<Term>,
  },
  Infix {
    pos: Position,
    sym: FuncSymId,
    spelling: String,
    left: u8,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    args: Vec<Term>,
  },
  Bracket {
    pos: Position,
    lsym: LeftBrkSymId,
    lspelling: String,
    rsym: RightBrkSymId,
    rspelling: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    args: Vec<Term>,
  },
  Aggregate {
    pos: Position,
    sym: StructSymId,
    spelling: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    args: Vec<Term>,
  },
  SubAggr {
    pos: Position,
    sym: StructSymId,
    spelling: String,
    arg: Box<Term>,
  },
  Selector {
    pos: Position,
    sym: SelSymId,
    spelling: String,
    arg: Box<Term>,
  },
  InternalSelector {
    pos: Position,
    sym: SelSymId,
    spelling: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    id: Option<ConstId>,
  },
  Qua {
    pos: Position,
    term: Box<Term>,
    ty: Box<Type>,
  },
  The {
    pos: Position,
    ty: Box<Type>,
  },
  Fraenkel {
    pos: Position,
    vars: Vec<BinderGroup>,
    scope: Box<Term>,
    #[serde(skip_serializing_if = "Option::is_none")]
    compr: Option<Box<Formula>>,
    #[serde(skip)]
    nameck: Option<Box<crate::analyze::FraenkelNameckResult>>,
  },
  It {
    pos: Position,
  },
}
impl Term {
  pub fn pos(&self) -> Position {
    match self {
      Term::Placeholder { pos, .. }
      | Term::Numeral { pos, .. }
      | Term::Var { pos, .. }
      | Term::PrivFunc { pos, .. }
      | Term::Infix { pos, .. }
      | Term::Bracket { pos, .. }
      | Term::Aggregate { pos, .. }
      | Term::SubAggr { pos, .. }
      | Term::Selector { pos, .. }
      | Term::InternalSelector { pos, .. }
      | Term::Qua { pos, .. }
      | Term::The { pos, .. }
      | Term::Fraenkel { pos, .. }
      | Term::It { pos } => *pos,
    }
  }
}

mk_id! {
  ReservedId(u32),
  ResGroupId(u32),
}

#[derive(Debug, Serialize)]
pub enum Type {
  Mode {
    pos: Position,
    sym: ModeSymId,
    spelling: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    args: Vec<Term>,
  },
  Struct {
    pos: Position,
    sym: StructSymId,
    spelling: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    args: Vec<Term>,
  },
  Cluster {
    pos: Position,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    attrs: Vec<Attr>,
    ty: Box<Type>,
  },
  Reservation {
    pos: Position,
    group: ResGroupId,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    subst: Vec<VarKind>,
  },
}
impl Type {
  pub fn pos(&self) -> Position {
    match self {
      Type::Mode { pos, .. }
      | Type::Struct { pos, .. }
      | Type::Cluster { pos, .. }
      | Type::Reservation { pos, .. } => *pos,
    }
  }
}

#[derive(Copy, Clone, Debug, Serialize)]
pub enum PrivPredKind {
  PrivPred(PrivPredId),
  SchPred(SchPredId),
}

#[derive(Copy, Clone, Debug, Serialize)]
pub enum FormulaBinop {
  And,
  Or,
  Imp,
  Iff,
  FlexAnd,
  FlexOr,
}

#[derive(Copy, Clone, Debug, Serialize)]
pub enum FormulaBinder {
  ForAll,
  Exists,
}

#[derive(Debug, Serialize)]
pub struct Pred {
  pub pos: Position,
  pub positive: bool,
  pub sym: PredSymId,
  pub spelling: String,
  pub left: u8,
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub args: Vec<Term>,
}

#[derive(Debug, Serialize)]
pub struct PredRhs {
  pub pos: Position,
  pub positive: bool,
  pub sym: PredSymId,
  pub spelling: String,
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub right: Vec<Term>,
}

#[derive(Debug, Serialize)]
pub enum Formula {
  Not {
    pos: Position,
    f: Box<Formula>,
  },
  Binop {
    kind: FormulaBinop,
    pos: Position,
    f1: Box<Formula>,
    f2: Box<Formula>,
  },
  Pred(Box<Pred>),
  ChainPred {
    pos: Position,
    first: Box<Pred>,
    rest: Vec<PredRhs>,
  },
  PrivPred {
    pos: Position,
    #[serde(skip_serializing_if = "Option::is_none")]
    kind: Option<PrivPredKind>,
    spelling: Rc<str>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    args: Vec<Term>,
  },
  Attr {
    pos: Position,
    positive: bool,
    term: Box<Term>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    attrs: Vec<Attr>,
  },
  Is {
    pos: Position,
    positive: bool,
    term: Box<Term>,
    ty: Box<Type>,
  },
  Binder {
    kind: FormulaBinder,
    pos: Position,
    vars: Vec<BinderGroup>,
    #[serde(skip_serializing_if = "Option::is_none")]
    st: Option<Box<Formula>>,
    scope: Box<Formula>,
  },
  False {
    pos: Position,
  },
  Thesis {
    pos: Position,
  },
}
impl Formula {
  pub fn pos(&self) -> Position {
    match self {
      Formula::Pred(p) => p.pos,
      Formula::Not { pos, .. }
      | Formula::Binop { pos, .. }
      | Formula::False { pos, .. }
      | Formula::ChainPred { pos, .. }
      | Formula::PrivPred { pos, .. }
      | Formula::Attr { pos, .. }
      | Formula::Is { pos, .. }
      | Formula::Binder { pos, .. }
      | Formula::Thesis { pos } => *pos,
    }
  }
}

#[derive(Debug, Serialize)]
pub struct Proposition {
  #[serde(skip_serializing_if = "Option::is_none")]
  pub label: Option<Box<Label>>,
  pub f: Formula,
}

#[derive(Debug, Serialize)]
pub enum SchRef {
  #[serde(untagged)]
  Resolved(ArticleId, SchId),
  #[serde(untagged)]
  UnresolvedPriv(String),
}

#[derive(Debug, Serialize)]
pub enum InferenceKind {
  By {
    #[serde(skip_serializing_if = "Option::is_none")]
    link: Option<Position>,
  },
  From(SchRef),
}

#[derive(Debug, Clone, Serialize)]
pub enum RefFragment {
  Thm { pos: Position, id: ThmId },
  Def { pos: Position, id: DefId },
}
#[derive(Debug, Clone, Serialize)]
pub enum ReferenceKind {
  Priv(#[serde(skip_serializing_if = "Option::is_none")] Option<LabelId>),
  Global(ArticleId, Vec<RefFragment>),
  #[serde(untagged)]
  UnresolvedPriv(String),
}

#[derive(Debug, Clone, Serialize)]
pub struct Reference {
  pub pos: Position,
  pub kind: ReferenceKind,
}

#[derive(Debug, Serialize)]
pub enum Justification {
  Inference {
    pos: Position,
    kind: InferenceKind,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    refs: Vec<Reference>,
  },
  Block {
    pos: (Position, Position),
    #[serde(skip_serializing_if = "Vec::is_empty")]
    items: Vec<Item>,
  },
}

#[derive(Debug, Serialize)]
pub enum SchemeBinderGroup {
  Pred {
    pos: Position,
    vars: Vec<Variable>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    tys: Vec<Type>,
  },
  Func {
    pos: Position,
    vars: Vec<Variable>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    tys: Vec<Type>,
    ret: Type,
  },
}

#[derive(Debug, Serialize)]
pub struct BinderGroup {
  pub vars: Vec<Variable>,
  // The vars list must be length 1 when this is None
  #[serde(skip_serializing_if = "Option::is_none")]
  pub ty: Option<Box<Type>>,
}

#[derive(Debug, Serialize)]
pub enum ReconsiderVar {
  /// Only occurs in wsm
  Var(Variable),
  Equality {
    var: Variable,
    tm: Term,
  },
}

#[derive(Debug, Serialize)]
pub struct Item {
  pub pos: Position,
  pub kind: ItemKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum CaseKind {
  Case,
  Suppose,
}
impl CaseKind {
  pub fn name(self) -> &'static str {
    match self {
      CaseKind::Case => "Case",
      CaseKind::Suppose => "Suppose",
    }
  }
  pub fn block_name(self) -> &'static str {
    match self {
      CaseKind::Case => "CaseBlock",
      CaseKind::Suppose => "SupposeBlock",
    }
  }
}

#[derive(Debug, Serialize)]
pub struct Field {
  pub pos: Position,
  pub sym: SelSymId,
  pub spelling: Rc<str>,
}

#[derive(Debug, Serialize)]
pub struct FieldGroup {
  pub pos: Position,
  pub vars: Vec<Field>,
  pub ty: Type,
}

#[derive(Debug, Serialize)]
pub struct PatternStruct {
  pub sym: StructSymId,
  pub spelling: String,
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub args: Vec<Variable>,
}

impl PatternStruct {
  pub fn to_mode_format(&self) -> FormatStruct {
    FormatStruct { sym: self.sym, args: self.args.len() as u8 }
  }
  pub fn to_aggr_format(&self, n: usize) -> FormatAggr {
    FormatAggr { sym: self.sym, args: n as u8 }
  }
  pub fn to_subaggr_format(&self) -> StructSymId { self.sym }
}

#[derive(Debug, Serialize)]
pub enum PatternFunc {
  Func {
    pos: Position,
    sym: FuncSymId,
    spelling: String,
    left: u8,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    args: Vec<Variable>,
  },
  Bracket {
    pos: Position,
    lsym: LeftBrkSymId,
    lspelling: String,
    rsym: RightBrkSymId,
    rspelling: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    args: Vec<Variable>,
  },
}

impl PatternFunc {
  pub fn pos(&self) -> Position {
    let (PatternFunc::Func { pos, .. } | PatternFunc::Bracket { pos, .. }) = *self;
    pos
  }
  pub fn args(&self) -> &[Variable] {
    let (PatternFunc::Func { args, .. } | PatternFunc::Bracket { args, .. }) = self;
    args
  }
  pub fn args_mut(&mut self) -> &mut [Variable] {
    let (PatternFunc::Func { args, .. } | PatternFunc::Bracket { args, .. }) = self;
    args
  }
  pub fn to_format(&self) -> FormatFunc {
    match *self {
      PatternFunc::Func { sym, left, ref args, .. } =>
        FormatFunc::Func { sym, left, right: args.len() as u8 - left },
      PatternFunc::Bracket { lsym, rsym, ref args, .. } =>
        FormatFunc::Bracket { lsym, rsym, args: args.len() as u8 },
    }
  }
}

#[derive(Debug, Serialize)]
pub struct PatternPred {
  pub pos: Position,
  pub sym: PredSymId,
  pub spelling: String,
  pub left: u8,
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub args: Vec<Variable>,
}
impl PatternPred {
  pub fn to_format(&self) -> FormatPred {
    FormatPred { sym: self.sym, left: self.left, right: self.args.len() as u8 - self.left }
  }
}

#[derive(Debug, Serialize)]
pub struct PatternMode {
  pub pos: Position,
  pub sym: ModeSymId,
  pub spelling: String,
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub args: Vec<Variable>,
}
impl PatternMode {
  pub fn to_format(&self) -> FormatMode {
    FormatMode { sym: self.sym, args: self.args.len() as u8 }
  }
}

#[derive(Debug, Serialize)]
pub struct PatternAttr {
  pub pos: Position,
  pub sym: AttrSymId,
  pub spelling: String,
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub args: Vec<Variable>,
}
impl PatternAttr {
  pub fn to_format(&self) -> FormatAttr {
    FormatAttr { sym: self.sym, args: self.args.len() as u8 }
  }
}

#[derive(Debug, Serialize)]
pub enum Pattern {
  Pred(Box<PatternPred>),
  Func(Box<PatternFunc>),
  Mode(Box<PatternMode>),
  Attr(Box<PatternAttr>),
}

impl Pattern {
  pub fn pos(&self) -> Position {
    match self {
      Pattern::Pred(p) => p.pos,
      Pattern::Func(p) => p.pos(),
      Pattern::Mode(p) => p.pos,
      Pattern::Attr(p) => p.pos,
    }
  }
}

#[derive(Debug, Serialize)]
pub struct DefCase<T> {
  pub case: Box<T>,
  pub guard: Box<Formula>,
}

#[derive(Debug, Serialize)]
pub struct DefBody<T> {
  /// nPartialDefinientia
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub cases: Vec<DefCase<T>>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub otherwise: Option<Box<T>>,
}

#[derive(Debug, Serialize)]
pub enum DefValue {
  Term(DefBody<Term>),
  Formula(DefBody<Formula>),
}

#[derive(Debug, Serialize)]
pub struct Definiens {
  pub pos: Position,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub label: Option<Box<Label>>,
  pub kind: DefValue,
}

#[derive(Debug, Serialize)]
pub enum DefModeKind {
  Expandable {
    expansion: Box<Type>,
  },
  Standard {
    #[serde(skip_serializing_if = "Option::is_none")]
    spec: Option<Box<Type>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    def: Option<Box<Definiens>>,
  },
}

#[derive(Debug, Serialize)]
pub enum PatternRedef {
  Pred { new: Box<PatternPred>, orig: Box<PatternPred>, pos: bool },
  Func { new: Box<PatternFunc>, orig: Box<PatternFunc> },
  Mode { new: Box<PatternMode>, orig: Box<PatternMode> },
  Attr { new: Box<PatternAttr>, orig: Box<PatternAttr>, pos: bool },
}

#[derive(Debug, Serialize)]
pub enum Attr {
  Attr {
    pos: Position,
    sym: AttrSymId,
    spelling: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    args: Vec<Term>,
  },
  Non {
    pos: Position,
    attr: Box<Attr>,
  },
}

impl Attr {
  pub fn pos(&self) -> Position {
    match *self {
      Attr::Attr { pos, .. } | Attr::Non { pos, .. } => pos,
    }
  }
}

#[derive(Debug, Serialize)]
pub enum ClusterDeclKind {
  Exist {
    concl: Vec<Attr>,
    ty: Box<Type>,
  },
  Func {
    term: Box<Term>,
    concl: Vec<Attr>,
    #[serde(skip_serializing_if = "Option::is_none")]
    ty: Option<Box<Type>>,
  },
  Cond {
    #[serde(skip_serializing_if = "Vec::is_empty")]
    antecedent: Vec<Attr>,
    concl: Vec<Attr>,
    ty: Box<Type>,
  },
}

#[derive(Debug, Serialize)]
pub struct Label {
  pub pos: Position,
  pub id: Option<LabelId>,
  pub spelling: Rc<str>,
}

#[derive(Debug, Serialize)]
pub enum Assumption {
  Single { pos: Position, prop: Box<Proposition> },
  Collective { pos: Position, conds: Vec<Proposition> },
}
impl Assumption {
  pub fn conds(&mut self) -> &mut [Proposition] {
    match self {
      Assumption::Single { prop, .. } => std::slice::from_mut(prop),
      Assumption::Collective { conds, .. } => conds,
    }
  }
}

#[derive(Debug, Serialize)]
pub struct SetDecl {
  pub var: Box<Variable>,
  pub value: Box<Term>,
}

#[derive(Debug, Serialize)]
pub struct TakeDecl {
  #[serde(skip_serializing_if = "Option::is_none")]
  pub var: Option<Box<Variable>>,
  pub term: Box<Term>,
}

#[derive(Debug, Serialize)]
pub struct IterStep {
  pub pos: Position,
  pub rhs: Term,
  pub just: Justification,
}

#[derive(Debug, Serialize)]
pub enum Statement {
  Proposition {
    prop: Box<Proposition>,
    just: Box<Justification>,
  },
  IterEquality {
    /// lhs = first rhs
    prop: Box<Proposition>,
    just: Box<Justification>,
    /// subsequent rhs's
    steps: Vec<IterStep>,
  },
  Now {
    #[serde(skip_serializing_if = "Option::is_none")]
    label: Option<Box<Label>>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    items: Vec<Item>,
    end: Position,
  },
}

#[derive(Debug, Serialize)]
pub enum DefinitionKind {
  Func {
    pat: Box<PatternFunc>,
    #[serde(skip_serializing_if = "Option::is_none")]
    spec: Option<Box<Type>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    def: Option<Box<Definiens>>,
  },
  Pred {
    pat: Box<PatternPred>,
    #[serde(skip_serializing_if = "Option::is_none")]
    def: Option<Box<Definiens>>,
  },
  Mode {
    pat: Box<PatternMode>,
    kind: DefModeKind,
  },
  Attr {
    pat: Box<PatternAttr>,
    #[serde(skip_serializing_if = "Option::is_none")]
    def: Option<Box<Definiens>>,
  },
}

impl DefinitionKind {
  pub fn pos(&self) -> Position {
    match self {
      DefinitionKind::Func { pat, .. } => match **pat {
        PatternFunc::Func { pos, .. } | PatternFunc::Bracket { pos, .. } => pos,
      },
      DefinitionKind::Pred { pat, .. } => pat.pos,
      DefinitionKind::Mode { pat, .. } => pat.pos,
      DefinitionKind::Attr { pat, .. } => pat.pos,
    }
  }
}

#[derive(Debug, Serialize)]
pub struct CorrCond {
  pub pos: Position,
  pub kind: CorrCondKind,
  pub just: Justification,
}

#[derive(Debug, Serialize)]
pub struct Correctness {
  pub pos: Position,
  pub just: Justification,
}

#[derive(Debug, Serialize)]
pub struct Property {
  pub pos: Position,
  pub kind: PropertyKind,
  pub just: Box<Justification>,
}

#[derive(Debug, Serialize)]
pub struct SchemeHead {
  #[serde(skip_serializing_if = "Option::is_none")]
  pub sym: Option<Rc<str>>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub nr: Option<SchId>,
  pub groups: Vec<SchemeBinderGroup>,
  pub concl: Formula,
  pub prems: Vec<Proposition>,
}

#[derive(Debug, Serialize)]
pub struct SchemeBlock {
  #[serde(flatten)]
  pub head: SchemeHead,
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub items: Vec<Item>,
  pub end: Position,
}

#[derive(Debug, Serialize)]
pub struct Reservation {
  pub vars: Vec<Variable>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub tys: Option<Vec<Type>>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub fvars: Option<IdxVec<BoundId, ReservedId>>,
  pub ty: Box<Type>,
}

#[derive(Debug, Serialize)]
pub struct Definition {
  pub kind: DefinitionKind,
  #[serde(flatten)]
  pub body: DefinitionBody,
}
#[derive(Debug, Serialize)]
pub struct DefinitionBody {
  #[serde(skip_serializing_if = "std::ops::Not::not")]
  pub redef: bool,
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub conds: Vec<CorrCond>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub corr: Option<Correctness>,
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub props: Vec<Property>,
}

#[derive(Debug, Serialize)]
pub struct DefStruct {
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub parents: Vec<Type>,
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub fields: Vec<FieldGroup>,
  pub pat: PatternStruct,
}

#[derive(Debug, Serialize)]
pub struct Cluster {
  pub kind: ClusterDeclKind,
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub conds: Vec<CorrCond>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub corr: Option<Correctness>,
}

#[derive(Debug, Serialize)]
pub struct IdentifyFunc {
  pub lhs: Box<PatternFunc>,
  pub rhs: Box<PatternFunc>,
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub eqs: Vec<(Variable, Variable)>,
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub conds: Vec<CorrCond>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub corr: Option<Correctness>,
}

#[derive(Debug, Serialize)]
pub struct Reduction {
  pub from: Box<Term>,
  pub to: Box<Term>,
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub conds: Vec<CorrCond>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub corr: Option<Correctness>,
}

#[derive(Debug, Serialize)]
pub struct CaseBlock {
  pub hyp: Box<Assumption>,
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub items: Vec<Item>,
  pub end: Position,
}

#[derive(Debug, Serialize)]
pub enum Pragma {
  /// $CD, $CT, $CS
  Canceled(CancelKind, u32),
  /// $N
  ThmDesc(String),
  /// $INSERT
  Insert(String),
  /// $V-, $V+
  SetVerify(bool),
  Other(String),
}

impl FromStr for Pragma {
  type Err = std::convert::Infallible;
  fn from_str(spelling: &str) -> Result<Self, Self::Err> {
    let parse_num = |s: &str| {
      if s.is_empty() {
        1
      } else {
        s.trim().parse::<u32>().unwrap()
      }
    };
    Ok(if let Some(s) = spelling.strip_prefix("$CD") {
      Pragma::Canceled(CancelKind::Def, parse_num(s))
    } else if let Some(s) = spelling.strip_prefix("$CT") {
      Pragma::Canceled(CancelKind::Thm, parse_num(s))
    } else if let Some(s) = spelling.strip_prefix("$CS") {
      Pragma::Canceled(CancelKind::Sch, parse_num(s))
    } else if let Some(s) = spelling.strip_prefix("$N") {
      Pragma::ThmDesc(s.trim_start().to_owned())
    } else if let Some(s) = spelling.strip_prefix("$INSERT") {
      Pragma::Insert(s.trim_start().to_owned())
    } else {
      match spelling {
        "$V-" => Pragma::SetVerify(false),
        "$V+" => Pragma::SetVerify(true),
        _ => Pragma::Other(spelling.to_owned()),
      }
    })
  }
}

#[derive(Debug, Serialize)]
pub enum ItemKind {
  Section,
  Block {
    kind: BlockKind,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    items: Vec<Item>,
    end: Position,
  },
  SchemeBlock(Box<SchemeBlock>),
  Theorem {
    prop: Box<Proposition>,
    just: Box<Justification>,
  },
  Reservation(Vec<Reservation>),
  /// itConclusion
  Thus(Statement),
  /// itChoice
  Consider {
    vars: Vec<BinderGroup>,
    conds: Vec<Proposition>,
    just: Box<Justification>,
  },
  Reconsider {
    vars: Vec<ReconsiderVar>,
    ty: Box<Type>,
    just: Box<Justification>,
  },
  /// itPrivFuncDefinition
  DefFunc {
    var: Box<Variable>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    tys: Vec<Type>,
    value: Box<Term>,
  },
  /// itPrivPredDefinition
  DefPred {
    var: Box<Variable>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    tys: Vec<Type>,
    value: Box<Formula>,
  },
  /// itConstantDefinition
  Set(Vec<SetDecl>),
  /// itGeneralization, itLociDeclaration
  Let {
    vars: Vec<BinderGroup>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    conds: Vec<Proposition>,
  },
  /// itExistentialAssumption
  Given {
    vars: Vec<BinderGroup>,
    conds: Vec<Proposition>,
  },
  /// itExemplification
  Take(Vec<TakeDecl>),
  PerCases {
    just: Box<Justification>,
    kind: CaseKind,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    blocks: Vec<CaseBlock>,
  },
  Assume(Assumption),
  Unfold(Vec<Reference>),
  Definition(Box<Definition>),
  DefStruct(Box<DefStruct>),
  PatternRedef(PatternRedef),
  Cluster(Box<Cluster>),
  IdentifyFunc(Box<IdentifyFunc>),
  Reduction(Box<Reduction>),
  SethoodRegistration {
    ty: Box<Type>,
    just: Box<Justification>,
  },
  Pragma(Pragma),
  /// parser internal use only
  SchemeHead(Box<SchemeHead>),
  /// parser internal use only
  CaseHead(CaseKind, Assumption),
  /// parser internal use only
  PerCasesHead(Box<Justification>),
  #[serde(untagged)]
  Statement(Statement),
}

impl Default for ItemKind {
  fn default() -> Self { Self::Section }
}
