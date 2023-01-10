use crate::mk_id;
use crate::types::{BlockKind, CorrCondKind, Position, PropertyKind, SchId, SchRef};

mk_id! {
  IdentId,
}

#[derive(Debug)]
pub struct Variable {
  pub pos: Position,
  pub id: (IdentId, String),
}

#[derive(Debug)]
pub enum Term {
  Placeholder { pos: Position, nr: u32 },
  Numeral { pos: Position, value: u32 },
  Simple { pos: Position, sym: (u32, String) },
  PrivateFunctor { pos: Position, sym: (u32, String), args: Vec<Term> },
  Infix { pos: Position, sym: (u32, String), left: Vec<Term>, right: Vec<Term> },
  Circumfix { pos: Position, lsym: (u32, String), rsym: (u32, String), args: Vec<Term> },
  Aggregate { pos: Position, sym: (u32, String), args: Vec<Term> },
  ForgetfulFunctor { pos: Position, sym: (u32, String), arg: Box<Term> },
  Selector { pos: Position, sym: (u32, String), arg: Box<Term> },
  InternalSelector { pos: Position, sym: (u32, String) },
  Qualification { pos: Position, term: Box<Term>, ty: Box<Type> },
  GlobalChoice { pos: Position, ty: Box<Type> },
  Fraenkel { pos: Position, vars: Vec<BinderGroup>, scope: Box<Term>, compr: Option<Box<Formula>> },
  It { pos: Position },
}

#[derive(Debug)]
pub enum Type {
  Standard { pos: Position, sym: (u32, String), args: Vec<Term> },
  Struct { pos: Position, sym: (u32, String), args: Vec<Term> },
  Cluster { pos: Position, attrs: Vec<Adjective>, ty: Box<Type> },
  Reservation { pos: Position, sym: (u32, String), nr: u32, subst: Vec<[u32; 3]> },
}

#[derive(Debug)]
pub enum FormulaBinop {
  And,
  Or,
  Imp,
  Iff,
  FlexAnd,
  FlexOr,
}

#[derive(Debug)]
pub enum FormulaBinder {
  ForAll,
  Exists,
}

#[derive(Debug)]
pub struct Pred {
  pub sym: (u32, String),
  pub left: Vec<Term>,
  pub right: Vec<Term>,
}

#[derive(Debug)]
pub struct PredRhs {
  pub sym: (u32, String),
  pub right: Vec<Term>,
}

#[derive(Debug)]
pub enum Formula {
  Not { pos: Position, f: Box<Formula> },
  Binop { kind: FormulaBinop, pos: Position, f: [Box<Formula>; 2] },
  False { pos: Position },
  Pred { pos: Position, f: Pred },
  ChainPred { pos: Position, first: Pred, rest: Vec<PredRhs> },
  PrivPred { pos: Position, sym: (u32, String), args: Vec<Term> },
  Attr { pos: Position, term: Box<Term>, attrs: Vec<Adjective> },
  Is { pos: Position, term: Box<Term>, ty: Box<Type> },
  Binder { kind: FormulaBinder, pos: Position, var: Box<BinderGroup>, f: Box<Formula> },
  Thesis { pos: Position },
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
  pub subst: Vec<[u32; 3]>,
}

#[derive(Debug)]
pub enum ReconsiderVar {
  Var(Variable),
  Equality { var: Variable, tm: Term },
}

#[derive(Debug)]
pub struct Item {
  pub pos: Position,
  pub kind: ItemKind,
}

#[derive(Debug)]
pub enum CaseOrSupposeKind {
  Case,
  Suppose,
}

#[derive(Debug)]
pub struct Field {
  pub pos: Position,
  pub sym: (u32, String),
}

#[derive(Debug)]
pub struct FieldGroup {
  pub pos: Position,
  pub fields: Vec<Field>,
  pub ty: Type,
}

#[derive(Debug)]
pub struct PatternStruct {
  pub sym: (u32, String),
  pub args: Vec<Variable>,
  pub groups: Vec<FieldGroup>,
}

#[derive(Debug)]
pub enum PatternFunc {
  Func { pos: Position, sym: (u32, String), left: Vec<Variable>, right: Vec<Variable> },
  Bracket { pos: Position, lsym: (u32, String), rsym: (u32, String), args: Vec<Variable> },
}

#[derive(Debug)]
pub struct PatternPred {
  pub pos: Position,
  pub sym: (u32, String),
  pub left: Vec<Variable>,
  pub right: Vec<Variable>,
}
#[derive(Debug)]
pub struct PatternMode {
  pub pos: Position,
  pub sym: (u32, String),
  pub args: Vec<Variable>,
}
#[derive(Debug)]
pub struct PatternAttr {
  pub pos: Position,
  pub sym: (u32, String),
  pub arg: Box<Variable>,
  pub args: Vec<Variable>,
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
pub enum DefFuncKind {
  None,
  Means(Box<Definiens>),
  Equals(Box<Definiens>),
}

#[derive(Debug)]
pub enum PatternRedefKind {
  PredSynonym { pos: bool },
  FuncNotation,
  ModeNotation,
  AttrSynonym { pos: bool },
}

#[derive(Debug)]
pub enum Adjective {
  Positive { pos: Position, sym: (u32, String), args: Vec<Term> },
  Negative { pos: Position, attr: Box<Adjective> },
}

#[derive(Debug)]
pub enum ClusterDeclKind {
  Exist { concl: Vec<Adjective>, ty: Box<Type> },
  Func { term: Box<Term>, concl: Vec<Adjective>, ty: Option<Box<Type>> },
  Cond { antecedent: Vec<Adjective>, concl: Vec<Adjective>, ty: Box<Type> },
}

#[derive(Debug)]
pub struct Label {
  pub pos: Position,
  pub id: (u32, String),
}

#[derive(Debug)]
pub enum Assumption {
  Single { pos: Position, prop: Box<Proposition> },
  Collective { pos: Position, conds: Vec<Proposition> },
}

#[derive(Debug)]
pub struct IterStep {
  pub pos: Position,
  pub rhs: Term,
  pub just: Justification,
}

#[derive(Debug)]
pub enum Reference {
  Local { pos: Position, lab: u32 },
  Thm { pos: Position, article_nr: u32, thm_nr: u32 },
  Def { pos: Position, article_nr: u32, def_nr: u32 },
}

#[derive(Debug)]
pub enum PrivateStatement {
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
  Func { pat: Box<PatternFunc>, spec: Option<Box<Type>>, kind: DefFuncKind },
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
}

#[derive(Debug)]
pub struct DefStruct {
  pub parents: Vec<Type>,
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
pub struct Identify {
  pub orig: Pattern,
  pub new: Pattern,
  pub eqs: Vec<(Variable, Variable)>,
  pub conds: Vec<CorrCond>,
  pub corr: Option<Correctness>,
}

#[derive(Debug)]
pub struct Reduction {
  pub orig: Term,
  pub new: Term,
  pub conds: Vec<CorrCond>,
  pub corr: Option<Correctness>,
}

#[derive(Debug)]
pub enum ItemKind {
  Block { end: Position, kind: BlockKind, items: Vec<Item> },
  SchemeBlock(Box<SchemeBlock>),
  SchemeHead(Box<SchemeHead>),
  Theorem { prop: Box<Proposition>, just: Box<Justification> },
  Reservation(Box<Reservation>),
  Section,
  Conclusion(PrivateStatement),
  RegularStatement(PrivateStatement),
  Consider { vars: Vec<BinderGroup>, conds: Vec<Proposition>, just: Box<Justification> },
  Reconsider { vars: Vec<ReconsiderVar>, ty: Box<Type>, just: Box<Justification> },
  PrivFuncDefinition { var: Box<Variable>, tys: Vec<Type>, value: Box<Term> },
  PrivPredDefinition { var: Box<Variable>, tys: Vec<Type>, value: Box<Formula> },
  ConstantDefinition { var: Box<Variable>, value: Box<Term> },
  Generalization { var: Box<BinderGroup> },
  LociDeclaration { var: Box<BinderGroup> },
  ExistentialAssumption { vars: Vec<BinderGroup>, conds: Vec<Proposition> },
  Exemplification { var: Option<Box<Variable>>, term: Option<Box<Term>> },
  PerCases { just: Box<Justification> },
  CaseOrSuppose { end: Position, kind: CaseOrSupposeKind, items: Vec<Item> },
  CaseHead(Assumption),
  SupposeHead(Assumption),
  Assumption(Assumption),
  Property { prop: PropertyKind, just: Box<Justification> },
  Definition(Box<Definition>),
  DefStruct(Box<DefStruct>),
  PatternRedef { kind: PatternRedefKind, orig: Pattern, new: Pattern },
  Cluster(Box<Cluster>),
  Identify(Box<Identify>),
  Reduction(Box<Reduction>),
  SethoodRegistration { ty: Box<Type>, just: Box<Justification> },
  Pragma { spelling: String },
}
