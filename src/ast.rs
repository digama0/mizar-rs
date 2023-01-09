use crate::mk_id;
use crate::types::{CorrCondKind, Position, PropertyKind, SchId, SchRef};

mk_id! {
  IdentId,
}

pub enum Correctness {
  Correctness,
  CorrCond(CorrCondKind),
}

pub enum BlockKind {
  Diffuse,
  Hereby,
  Proof,
  Definition,
  Notation,
  Registration,
  Case,
  Suppose,
  PublicScheme,
}

pub struct Variable {
  pub pos: Position,
  pub id: (IdentId, String),
}

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

pub enum Type {
  Standard { pos: Position, sym: (u32, String), args: Vec<Term> },
  Struct { pos: Position, sym: (u32, String), args: Vec<Term> },
  Cluster { pos: Position, attrs: Vec<Adjective>, ty: Box<Type> },
  Reservation { pos: Position, sym: (u32, String), nr: u32, subst: Vec<[u32; 3]> },
}

pub enum FormulaBinop {
  And,
  Or,
  Imp,
  Iff,
  FlexAnd,
  FlexOr,
}

pub enum FormulaBinder {
  ForAll,
  Exists,
}

pub struct Pred {
  pub sym: (u32, String),
  pub left: Vec<Term>,
  pub right: Vec<Term>,
}

pub struct PredRhs {
  pub sym: (u32, String),
  pub right: Vec<Term>,
}

pub enum Formula {
  Not { pos: Position, f: Box<Formula> },
  Binop { kind: FormulaBinop, pos: Position, f: Box<[Formula; 2]> },
  False { pos: Position },
  Pred { pos: Position, f: Pred },
  ChainPred { pos: Position, first: Pred, rest: Vec<PredRhs> },
  PrivPred { pos: Position, sym: (u32, String), args: Vec<Term> },
  Attr { pos: Position, term: Box<Term>, attrs: Vec<Adjective> },
  Is { pos: Position, term: Box<Term>, ty: Box<Type> },
  Binder { kind: FormulaBinder, pos: Position, var: BinderGroup, f: Box<Formula> },
  Thesis { pos: Position },
}

pub struct Proposition {
  pub label: Option<Label>,
  pub f: Formula,
}

pub enum InferenceKind {
  By { link: Option<Position> },
  From { sch: SchRef },
}

pub enum Justification {
  Inference { pos: Position, kind: InferenceKind, refs: Vec<Reference> },
  Block { pos: (Position, Position), items: Vec<Item> },
}

pub enum SchemeBinderGroup {
  Pred { pos: Position, vars: Vec<Variable>, tys: Vec<Type> },
  Func { pos: Position, vars: Vec<Variable>, tys: Vec<Type>, ret: Type },
}

pub struct BinderGroup {
  pub vars: Vec<Variable>,
  pub ty: Option<Type>,
}

pub enum ReconsiderVar {
  Var(Variable),
  Equality { var: Variable, tm: Term },
}

pub struct Item {
  pub pos: Position,
  pub kind: ItemKind,
}

pub enum CaseOrSupposeKind {
  Case,
  Suppose,
}

pub struct Field {
  pub pos: Position,
  pub sym: (u32, String),
}

pub struct FieldGroup {
  pub pos: Position,
  pub fields: Vec<Field>,
  pub ty: Type,
}

pub struct PatternStruct {
  pub sym: (u32, String),
  pub args: Vec<Variable>,
  pub groups: Vec<FieldGroup>,
}

pub enum PatternFunc {
  Func { pos: Position, sym: (u32, String), left: Vec<Variable>, right: Vec<Variable> },
  Bracket { pos: Position, lsym: (u32, String), rsym: (u32, String), args: Vec<Variable> },
}

pub struct PatternPred {
  pub pos: Position,
  pub sym: (u32, String),
  pub left: Vec<Variable>,
  pub right: Vec<Variable>,
}
pub struct PatternMode {
  pub pos: Position,
  pub sym: (u32, String),
  pub args: Vec<Variable>,
}
pub struct PatternAttr {
  pub pos: Position,
  pub sym: (u32, String),
  pub arg: Box<Variable>,
  pub args: Vec<Variable>,
}

pub enum Pattern {
  Pred(PatternPred),
  Func(PatternFunc),
  Mode(PatternMode),
  Attr(PatternAttr),
}

pub struct DefCase<T> {
  pub case: T,
  pub guard: Formula,
}

pub struct DefBody<T> {
  /// nPartialDefinientia
  pub cases: Vec<DefCase<T>>,
  pub otherwise: Option<T>,
}

pub enum DefValue {
  Term(DefBody<Term>),
  Formula(DefBody<Formula>),
}

pub struct Definiens {
  pub pos: Position,
  pub kind: DefValue,
}

pub enum DefModeKind {
  Expandable { expansion: Type },
  Standard { spec: Option<Type>, def: Definiens },
}

pub enum DefFuncKind {
  None,
  Means(Definiens),
  Equals(Definiens),
}

pub enum PatternRedefKind {
  PredSynonym { pos: bool },
  FuncNotation,
  ModeNotation,
  AttrSynonym { pos: bool },
}

pub enum Adjective {
  Positive { pos: Position, sym: (u32, String), args: Vec<Term> },
  Negative { pos: Position, attr: Box<Adjective> },
}

pub enum ClusterDeclKind {
  Exist { concl: Vec<Adjective> },
  Func { term: Term, concl: Vec<Adjective>, ty: Option<Type> },
  Cond { antecedent: Vec<Adjective>, concl: Vec<Adjective>, ty: Type },
}

pub struct Label {
  pub pos: Position,
  pub id: (u32, String),
}

pub enum Assumption {
  Single { pos: Position, prop: Proposition },
  Collective { pos: Position, conds: Vec<Proposition> },
}

pub struct IterStep {
  pub pos: Position,
  pub rhs: Term,
  pub just: Justification,
}

pub enum Reference {
  Local { pos: Position, lab: u32 },
  Thm { pos: Position, article_nr: u32, thm_nr: u32 },
  Def { pos: Position, article_nr: u32, def_nr: u32 },
}

pub enum PrivateStatement {
  Proposition {
    prop: Proposition,
    just: Justification,
  },
  IterEquality {
    /// lhs = first rhs
    prop: Proposition,
    just: Justification,
    /// subsequent rhs's
    steps: Vec<IterStep>,
  },
  Now {
    end: Position,
    label: Option<Label>,
    items: Vec<Item>,
  },
}

pub enum ItemKind {
  DefinitionBlock {
    end: Position,
    items: Vec<Item>,
  },
  SchemeBlock {
    end: Position,
    sym: (u32, String),
    nr: SchId,
    groups: Vec<SchemeBinderGroup>,
    concl: Formula,
    prems: Vec<Proposition>,
  },
  SchemeHead {
    sym: (u32, String),
    nr: SchId,
    groups: Vec<SchemeBinderGroup>,
    concl: Formula,
    prems: Vec<Proposition>,
  },
  Theorem {
    prop: Proposition,
    just: Justification,
  },
  Reservation {
    vars: Vec<Variable>,
    tys: Option<Vec<Type>>,
    fvars: Option<Vec<u32>>,
    ty: Type,
  },
  Section,
  Conclusion(PrivateStatement),
  RegularStatement(PrivateStatement),
  Consider {
    vars: Vec<BinderGroup>,
    conds: Vec<Proposition>,
    just: Justification,
  },
  Reconsider {
    vars: Vec<ReconsiderVar>,
    ty: Type,
    just: Justification,
  },
  PrivFuncDefinition {
    var: Variable,
    tys: Vec<Type>,
    value: Term,
  },
  PrivPredDefinition {
    var: Variable,
    tys: Vec<Type>,
    value: Formula,
  },
  ConstantDefinition {
    var: Variable,
    value: Term,
  },
  Generalization {
    var: BinderGroup,
  },
  LociDeclaration {
    var: BinderGroup,
  },
  ExistentialAssumption {
    vars: Vec<BinderGroup>,
    conds: Vec<Proposition>,
  },
  Exemplification {
    var: Option<Variable>,
    term: Option<Term>,
  },
  PerCases {
    just: Justification,
  },
  CaseOrSuppose {
    end: Position,
    kind: CaseOrSupposeKind,
    items: Vec<Item>,
  },
  CaseHead(Assumption),
  SupposeHead(Assumption),
  Assumption(Assumption),
  CorrCond {
    cond: Correctness,
    just: Justification,
  },
  Correctness {
    conds: Vec<Correctness>,
    just: Justification,
  },
  Property {
    prop: PropertyKind,
    just: Justification,
  },
  DefFunc {
    redef: bool,
    pat: PatternFunc,
    spec: Option<Type>,
    kind: DefFuncKind,
  },
  DefPred {
    redef: bool,
    pat: PatternPred,
    def: Definiens,
  },
  DefMode {
    redef: bool,
    pat: PatternMode,
    kind: DefModeKind,
  },
  DefAttr {
    redef: bool,
    pat: PatternAttr,
    def: Definiens,
  },
  DefStruct {
    parents: Vec<Type>,
    pat: PatternStruct,
  },
  PatternRedef {
    kind: PatternRedefKind,
    orig: Pattern,
    new: Pattern,
  },
  Cluster(ClusterDeclKind),
  Identify {
    orig: Pattern,
    new: Pattern,
    eqs: Vec<(Variable, Variable)>,
  },
  Reduction {
    orig: Term,
    new: Term,
  },
  SethoodRegistration {
    ty: Type,
    just: Justification,
  },
  Pragma {
    spelling: String,
  },
}
