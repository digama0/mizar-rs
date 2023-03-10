use crate::mk_id;
use crate::types::{
  AttrSymId, BlockKind, CancelKind, ConstId, CorrCondKind, FormatAggr, FormatAttr, FormatFunc,
  FormatMode, FormatPred, FormatStruct, FuncSymId, LabelId, LeftBrkSymId, LocusId, ModeSymId,
  Position, PredSymId, PropertyKind, Reference, RightBrkSymId, SchId, SchRef, SelSymId,
  StructSymId,
};
use enum_map::Enum;

#[derive(Debug, Default)]
pub struct Variable {
  pub pos: Position,
  /// 'idnr' attribute, LocusObj.nVarId, VariableObj.nIdent
  pub id: u32,
  /// 'varnr' attribute, MSLocusObj.nVarNr, MSVariableObj.nVarNr
  pub var: Option<ConstId>,
  pub spelling: String,
}

impl Variable {
  pub fn var(&self) -> ConstId { self.var.unwrap() }
}

#[derive(Copy, Clone, Debug, Enum)]
pub enum VarKind {
  Unknown,
  Free,
  Reserved,
  Bound,
  Const,
  DefConst,
  SchFunc,
  PrivFunc,
  SchPred,
  PrivPred,
}
impl Default for VarKind {
  fn default() -> Self { Self::Unknown }
}

#[derive(Debug)]
pub enum Term {
  Placeholder {
    pos: Position,
    nr: LocusId,
  },
  Numeral {
    pos: Position,
    value: u32,
  },
  Simple {
    pos: Position,
    kind: VarKind,
    var: u32,
    spelling: String,
    origin: VarKind,
  },
  PrivFunc {
    pos: Position,
    kind: VarKind,
    var: u32,
    spelling: String,
    args: Vec<Term>,
  },
  Infix {
    pos: Position,
    sym: (FuncSymId, String),
    left: u8,
    args: Vec<Term>,
  },
  Bracket {
    pos: Position,
    lsym: (LeftBrkSymId, String),
    rsym: (RightBrkSymId, String),
    args: Vec<Term>,
  },
  Aggregate {
    pos: Position,
    sym: (StructSymId, String),
    args: Vec<Term>,
  },
  SubAggr {
    pos: Position,
    sym: (StructSymId, String),
    arg: Box<Term>,
  },
  Selector {
    pos: Position,
    sym: (SelSymId, String),
    arg: Box<Term>,
  },
  InternalSelector {
    pos: Position,
    sym: (SelSymId, String),
    id: ConstId,
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
    compr: Option<Box<Formula>>,
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
      | Term::Simple { pos, .. }
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
}

#[derive(Debug)]
pub enum Type {
  Mode { pos: Position, sym: (ModeSymId, String), args: Vec<Term> },
  Struct { pos: Position, sym: (StructSymId, String), args: Vec<Term> },
  Cluster { pos: Position, attrs: Vec<Attr>, ty: Box<Type> },
  Reservation { pos: Position, nr: Option<ReservedId>, subst: Vec<(VarKind, u32)> },
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

#[derive(Copy, Clone, Debug)]
pub enum FormulaBinop {
  And,
  Or,
  Imp,
  Iff,
  FlexAnd,
  FlexOr,
}

#[derive(Copy, Clone, Debug)]
pub enum FormulaBinder {
  ForAll,
  Exists,
}

#[derive(Debug)]
pub struct Pred {
  pub sym: (PredSymId, String),
  pub left: u8,
  pub args: Vec<Term>,
}

#[derive(Debug)]
pub struct PredRhs {
  pub sym: (PredSymId, String),
  pub right: Vec<Term>,
}

#[derive(Debug)]
pub enum Formula {
  Not { pos: Position, f: Box<Formula> },
  Binop { kind: FormulaBinop, pos: Position, f1: Box<Formula>, f2: Box<Formula> },
  Pred { pos: Position, pred: Pred },
  ChainPred { pos: Position, first: Pred, rest: Vec<PredRhs> },
  PrivPred { pos: Position, kind: VarKind, var: u32, spelling: String, args: Vec<Term> },
  Attr { pos: Position, term: Box<Term>, attrs: Vec<Attr> },
  Is { pos: Position, term: Box<Term>, ty: Box<Type> },
  Binder { kind: FormulaBinder, pos: Position, var: Box<BinderGroup>, scope: Box<Formula> },
  False { pos: Position },
  Thesis { pos: Position },
}
impl Formula {
  pub fn pos(&self) -> Position {
    match self {
      Formula::Not { pos, .. }
      | Formula::Binop { pos, .. }
      | Formula::False { pos, .. }
      | Formula::Pred { pos, .. }
      | Formula::ChainPred { pos, .. }
      | Formula::PrivPred { pos, .. }
      | Formula::Attr { pos, .. }
      | Formula::Is { pos, .. }
      | Formula::Binder { pos, .. }
      | Formula::Thesis { pos } => *pos,
    }
  }
}

#[derive(Debug)]
pub struct Proposition {
  pub label: Option<Box<Label>>,
  pub f: Formula,
}

#[derive(Debug)]
pub enum InferenceKind {
  By { link: Option<Position> },
  From { sch: SchRef },
}

#[derive(Debug)]
pub enum Justification {
  Inference { pos: Position, kind: InferenceKind, refs: Vec<Reference> },
  Block { pos: (Position, Position), items: Vec<Item> },
}

#[derive(Debug)]
pub enum SchemeBinderGroup {
  Pred { pos: Position, vars: Vec<Variable>, tys: Vec<Type> },
  Func { pos: Position, vars: Vec<Variable>, tys: Vec<Type>, ret: Type },
}

#[derive(Debug)]
pub struct BinderGroup {
  pub vars: Vec<Variable>,
  pub ty: Option<Box<Type>>,
}

#[derive(Debug)]
pub enum ReconsiderVar {
  /// Only occurs in wsm
  Var(Variable),
  Equality {
    var: Variable,
    tm: Term,
  },
}

#[derive(Debug)]
pub struct Item {
  pub pos: Position,
  pub kind: ItemKind,
}

#[derive(Debug, PartialEq, Eq)]
pub enum CaseKind {
  Case,
  Suppose,
}

#[derive(Debug)]
pub struct Field {
  pub pos: Position,
  pub sym: (SelSymId, String),
}

#[derive(Debug)]
pub struct FieldGroup {
  pub pos: Position,
  pub vars: Vec<Field>,
  pub ty: Type,
}

#[derive(Debug)]
pub struct PatternStruct {
  pub sym: (StructSymId, String),
  pub args: Vec<Variable>,
}

impl PatternStruct {
  pub fn to_mode_format(&self) -> FormatStruct {
    FormatStruct { sym: self.sym.0, args: self.args.len() as u8 }
  }
  pub fn to_aggr_format(&self, n: usize) -> FormatAggr {
    FormatAggr { sym: self.sym.0, args: n as u8 }
  }
  pub fn to_subaggr_format(&self) -> StructSymId { self.sym.0 }
}

#[derive(Debug)]
pub enum PatternFunc {
  Func {
    pos: Position,
    sym: (FuncSymId, String),
    left: u8,
    args: Vec<Variable>,
  },
  Bracket {
    pos: Position,
    lsym: (LeftBrkSymId, String),
    rsym: (RightBrkSymId, String),
    args: Vec<Variable>,
  },
}

impl PatternFunc {
  pub fn args(&self) -> &[Variable] {
    let (PatternFunc::Func { args, .. } | PatternFunc::Bracket { args, .. }) = self;
    args
  }
  pub fn to_format(&self) -> FormatFunc {
    match *self {
      PatternFunc::Func { ref sym, left, ref args, .. } =>
        FormatFunc::Func { sym: sym.0, left, right: args.len() as u8 - left },
      PatternFunc::Bracket { ref lsym, ref rsym, ref args, .. } =>
        FormatFunc::Bracket { lsym: lsym.0, rsym: rsym.0, args: args.len() as u8 },
    }
  }
}

#[derive(Debug)]
pub struct PatternPred {
  pub pos: Position,
  pub sym: (PredSymId, String),
  pub left: u8,
  pub args: Vec<Variable>,
}
impl PatternPred {
  pub fn to_format(&self) -> FormatPred {
    FormatPred { sym: self.sym.0, left: self.left, right: self.args.len() as u8 - self.left }
  }
}

#[derive(Debug)]
pub struct PatternMode {
  pub pos: Position,
  pub sym: (ModeSymId, String),
  pub args: Vec<Variable>,
}
impl PatternMode {
  pub fn to_format(&self) -> FormatMode {
    FormatMode { sym: self.sym.0, args: self.args.len() as u8 }
  }
}

#[derive(Debug)]
pub struct PatternAttr {
  pub pos: Position,
  pub sym: (AttrSymId, String),
  pub args: Vec<Variable>,
}
impl PatternAttr {
  pub fn to_format(&self) -> FormatAttr {
    FormatAttr { sym: self.sym.0, args: self.args.len() as u8 }
  }
}

#[derive(Debug)]
pub enum Pattern {
  Pred(Box<PatternPred>),
  Func(Box<PatternFunc>),
  Mode(Box<PatternMode>),
  Attr(Box<PatternAttr>),
}

#[derive(Debug)]
pub struct DefCase<T> {
  pub case: Box<T>,
  pub guard: Box<Formula>,
}

#[derive(Debug)]
pub struct DefBody<T> {
  /// nPartialDefinientia
  pub cases: Vec<DefCase<T>>,
  pub otherwise: Option<Box<T>>,
}

#[derive(Debug)]
pub enum DefValue {
  Term(DefBody<Term>),
  Formula(DefBody<Formula>),
}

#[derive(Debug)]
pub struct Definiens {
  pub pos: Position,
  pub label: Option<Box<Label>>,
  pub kind: DefValue,
}

#[derive(Debug)]
pub enum DefModeKind {
  Expandable { expansion: Box<Type> },
  Standard { spec: Option<Box<Type>>, def: Option<Box<Definiens>> },
}

#[derive(Debug)]
pub enum PatternRedef {
  Pred { new: Box<PatternPred>, orig: Box<PatternPred>, pos: bool },
  Func { new: Box<PatternFunc>, orig: Box<PatternFunc> },
  Mode { new: Box<PatternMode>, orig: Box<PatternMode> },
  Attr { new: Box<PatternAttr>, orig: Box<PatternAttr>, pos: bool },
}

#[derive(Debug)]
pub enum Attr {
  Attr { pos: Position, sym: (AttrSymId, String), args: Vec<Term> },
  Non { pos: Position, attr: Box<Attr> },
}

#[derive(Debug)]
pub enum ClusterDeclKind {
  Exist { concl: Vec<Attr>, ty: Box<Type> },
  Func { term: Box<Term>, concl: Vec<Attr>, ty: Option<Box<Type>> },
  Cond { antecedent: Vec<Attr>, concl: Vec<Attr>, ty: Box<Type> },
}

#[derive(Debug)]
pub struct Label {
  pub pos: Position,
  pub id: (LabelId, String),
}

#[derive(Debug)]
pub enum Assumption {
  Single { pos: Position, prop: Box<Proposition> },
  Collective { pos: Position, conds: Vec<Proposition> },
}
impl Assumption {
  pub fn conds(&self) -> &[Proposition] {
    match self {
      Assumption::Single { prop, .. } => std::slice::from_ref(prop),
      Assumption::Collective { conds, .. } => conds,
    }
  }
}

#[derive(Debug)]
pub struct IterStep {
  pub pos: Position,
  pub rhs: Term,
  pub just: Justification,
}

#[derive(Debug)]
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
    end: Position,
    label: Option<Box<Label>>,
    items: Vec<Item>,
  },
}

#[derive(Debug)]
pub enum DefinitionKind {
  Func { pat: Box<PatternFunc>, spec: Option<Box<Type>>, def: Option<Box<Definiens>> },
  Pred { pat: Box<PatternPred>, def: Option<Box<Definiens>> },
  Mode { pat: Box<PatternMode>, kind: DefModeKind },
  Attr { pat: Box<PatternAttr>, def: Option<Box<Definiens>> },
}

#[derive(Debug)]
pub struct CorrCond {
  pub pos: Position,
  pub kind: CorrCondKind,
  pub just: Justification,
}

#[derive(Debug)]
pub struct Correctness {
  pub pos: Position,
  pub conds: Vec<CorrCondKind>,
  pub just: Justification,
}

#[derive(Debug)]
pub struct Property {
  pub kind: PropertyKind,
  pub just: Box<Justification>,
}

#[derive(Debug)]
pub struct SchemeHead {
  pub sym: (u32, String),
  pub nr: SchId,
  pub groups: Vec<SchemeBinderGroup>,
  pub concl: Formula,
  pub prems: Vec<Proposition>,
}

#[derive(Debug)]
pub struct SchemeBlock {
  pub end: Position,
  pub head: SchemeHead,
  pub items: Vec<Item>,
}

#[derive(Debug)]
pub struct Reservation {
  pub vars: Vec<Variable>,
  pub tys: Option<Vec<Type>>,
  pub fvars: Option<Vec<u32>>,
  pub ty: Box<Type>,
}

#[derive(Debug)]
pub struct Definition {
  pub redef: bool,
  pub kind: DefinitionKind,
  pub conds: Vec<CorrCond>,
  pub corr: Option<Correctness>,
  pub props: Vec<Property>,
}

#[derive(Debug)]
pub struct DefStruct {
  pub parents: Vec<Type>,
  pub fields: Vec<FieldGroup>,
  pub pat: PatternStruct,
  pub conds: Vec<CorrCond>,
  pub corr: Option<Correctness>,
}

#[derive(Debug)]
pub struct Cluster {
  pub kind: ClusterDeclKind,
  pub conds: Vec<CorrCond>,
  pub corr: Option<Correctness>,
}

#[derive(Debug)]
pub struct IdentifyFunc {
  pub lhs: PatternFunc,
  pub rhs: PatternFunc,
  pub eqs: Vec<(Variable, Variable)>,
  pub conds: Vec<CorrCond>,
  pub corr: Option<Correctness>,
}

#[derive(Debug)]
pub struct Reduction {
  pub from: Term,
  pub to: Term,
  pub conds: Vec<CorrCond>,
  pub corr: Option<Correctness>,
}

#[derive(Debug)]
pub struct CaseBlock {
  pub end: Position,
  pub hyp: Box<Assumption>,
  pub items: Vec<Item>,
}

#[derive(Debug)]
pub enum Pragma {
  /// $CD, $CT, $CS
  Canceled(CancelKind, u32),
  /// $N
  ThmDesc(String),
  Other(String),
}

#[derive(Debug)]
pub enum ItemKind {
  Section,
  Block {
    end: Position,
    kind: BlockKind,
    items: Vec<Item>,
  },
  SchemeBlock(Box<SchemeBlock>),
  Theorem {
    prop: Box<Proposition>,
    just: Box<Justification>,
  },
  Reservation(Box<Reservation>),
  /// itConclusion
  Thus(Statement),
  Statement(Statement),
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
    tys: Vec<Type>,
    value: Box<Term>,
  },
  /// itPrivPredDefinition
  DefPred {
    var: Box<Variable>,
    tys: Vec<Type>,
    value: Box<Formula>,
  },
  /// itConstantDefinition
  Set {
    var: Box<Variable>,
    value: Box<Term>,
  },
  /// itGeneralization, itLociDeclaration
  Let {
    var: Box<BinderGroup>,
  },
  /// itExistentialAssumption
  Given {
    vars: Vec<BinderGroup>,
    conds: Vec<Proposition>,
  },
  /// itExemplification
  Take {
    var: Option<Box<Variable>>,
    term: Option<Box<Term>>,
  },
  PerCases {
    just: Box<Justification>,
    kind: CaseKind,
    blocks: Vec<CaseBlock>,
  },
  Assume(Assumption),
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
}

impl Default for ItemKind {
  fn default() -> Self { Self::Section }
}
