#![warn(unused)]
use super::{ParseError, PathResult, Result, XmlReader};
use crate::ast::{SchRef, *};
use crate::types::{
  Article, ArticleId, AttrSymId, BoundId, ConstId, DefId, FuncSymId, IdxVec, LabelId, LeftBrkSymId,
  LocusId, ModeSymId, PredSymId, PrivFuncId, PrivPredId, PropertyKind, RightBrkSymId, SchFuncId,
  SchId, SchPredId, SelSymId, Span, StructSymId, ThmId,
};
use crate::{types, LineMap, MizPath};
use enum_map::Enum;
use quick_xml::events::{BytesStart, Event};
use std::borrow::Cow;
use std::fs::File;
use std::path::PathBuf;
use std::sync::Arc;

// Parser for WSM and MSM formats
pub struct MsmParser {
  r: XmlReader,
  pub path: PathBuf,
  buf: Vec<u8>,
  // true for MSM, false for WSM
  msm: bool,
}

impl MizPath {
  pub fn open_msx(&self, lines: Option<Arc<LineMap>>) -> PathResult<MsmParser> {
    MsmParser::new(self.to_path(true, false, "msx"), true, lines)
  }

  pub fn open_wsx(&self, lines: Option<Arc<LineMap>>) -> PathResult<MsmParser> {
    MsmParser::new(self.to_path(true, false, "wsx"), false, lines)
  }
}

#[derive(Copy, Clone, Debug, Enum, Default)]
pub enum IdentKind {
  #[default]
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

impl std::str::FromStr for IdentKind {
  type Err = String;
  fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
    match s {
      "Free" => Ok(Self::Free),
      "Reserved" => Ok(Self::Reserved),
      "Bound" => Ok(Self::Bound),
      "Constant" => Ok(Self::Const),
      "DefConstant" => Ok(Self::DefConst),
      "SchemataFunc" => Ok(Self::SchFunc),
      "PrivateFunc" => Ok(Self::PrivFunc),
      "SchemataPred" => Ok(Self::SchPred),
      "PrivatePred" => Ok(Self::PrivPred),
      _ => Err(s.to_string()),
    }
  }
}
impl super::FromStrPos for IdentKind {
  fn to_err(s: String, pos: usize) -> ParseError {
    ParseError::UnexpectedElement { pos, expected: "identifier kind", found: Some(s.into()) }
  }
}

impl TryFrom<&[u8]> for Shape {
  type Error = ();
  fn try_from(value: &[u8]) -> std::result::Result<Self, Self::Error> {
    match value {
      b"Diffuse-Statement" => Ok(Self::DiffuseStatement),
      b"Compact-Statement" => Ok(Self::CompactStatement),
      b"Iterative-Equality" => Ok(Self::IterativeEquality),
      _ => Err(()),
    }
  }
}

#[derive(Debug)]
pub enum BlockKind {
  Def(types::BlockKind),
  Now,
  Hereby,
  Proof,
  Case(CaseKind),
  Scheme,
}

#[derive(Debug)]
struct Block {
  kind: BlockKind,
  pos: (Span, Span),
  items: Vec<Item>,
}

impl ItemKind {
  fn corr_mut(&mut self) -> Option<(&mut Vec<CorrCond>, &mut Option<Correctness>)> {
    match self {
      ItemKind::Definition(it) => Some((&mut it.body.conds, &mut it.body.corr)),
      ItemKind::Cluster(it) => Some((&mut it.conds, &mut it.corr)),
      ItemKind::IdentifyFunc(it) => Some((&mut it.conds, &mut it.corr)),
      ItemKind::Reduction(it) => Some((&mut it.conds, &mut it.corr)),
      _ => None,
    }
  }

  fn property_mut(&mut self) -> Option<&mut Vec<Property>> {
    match self {
      ItemKind::Definition(it) => Some(&mut it.body.props),
      _ => None,
    }
  }
}

pub enum Shape {
  DiffuseStatement,
  CompactStatement,
  IterativeEquality,
}

#[derive(Debug)]
enum Elem {
  Block(Box<Block>),
  Inference(Span, InferenceKind, Vec<Reference>),
  Binder(Box<BinderGroup>),
  Conditions(Vec<Proposition>),
  Variable(Box<Variable>),
  Equality(Box<Variable>, Box<Term>),
  Type(Box<Type>),
  Term(Box<Term>),
  Formula(Box<Formula>),
  PredRhs(Box<PredRhs>),
  Redefine,
  Pattern(Pattern),
  TypeSpecification(Box<Type>),
  Definiens(Box<Definiens>),
  LociEquality(Box<Variable>, Box<Variable>),
  Label(Option<Box<Label>>),
  Link(Span),
  Reference(Reference),
  DefCaseTerm(DefCase<Term>),
  DefCaseFormula(DefCase<Formula>),
  Selector(Field),
  Other,
  End,
}

impl XmlReader {
  fn parse_variable_attrs(&mut self, e: &BytesStart<'_>) -> Result<Box<Variable>> {
    let (mut var, mut spelling) = <(_, _)>::default();
    let pos = self.get_pos(e)?;
    for attr in e.attributes() {
      let attr = attr?;
      match attr.key.0 {
        b"varnr" => var = self.get_attr::<u32>(&attr.value)?.checked_sub(1).map(ConstId),
        b"spelling" => spelling = attr.unescape_value()?,
        // omitted: origin, kind, serialnr, idnr
        _ => {}
      }
    }
    Ok(Box::new(Variable { pos, var, spelling: spelling.into() }))
  }
}

impl MsmParser {
  fn new(path: PathBuf, msm: bool, lines: Option<Arc<LineMap>>) -> PathResult<MsmParser> {
    let mut buf = vec![];
    let result = (|| {
      let file = File::open(&path)?;
      let mut r = XmlReader::new(file, &mut buf)?;
      r.1 = lines;
      match r.read_event(&mut buf)? {
        Event::Start(e) if e.local_name().as_ref() == b"Text-Proper" => {}
        _ => return r.err("Text-Proper"),
      }
      Ok(r)
    })();
    match result {
      Ok(r) => Ok(MsmParser { r, path, buf, msm }),
      Err(e) => Err((path, e)),
    }
  }

  fn parse_variable(&mut self) -> Result<Option<Box<Variable>>> {
    Ok(match self.parse_elem()? {
      Elem::Variable(v) => Some(v),
      Elem::End => None,
      _ => return self.r.err("<Variable>"),
    })
  }

  /// Like [`Self::parse_variable`], but the element is required.
  fn parse_variable1(&mut self) -> Result<Box<Variable>> {
    match self.parse_variable()? {
      Some(v) => Ok(v),
      None => self.r.err("Variable"),
    }
  }

  fn parse_variables(&mut self) -> Result<Vec<Variable>> {
    self.r.read_start(&mut self.buf, Some("Variables"))?;
    let mut out = vec![];
    while let Some(v) = self.parse_variable()? {
      out.push(*v)
    }
    Ok(out)
  }

  fn parse_substitution(&mut self) -> Result<Vec<VarKind>> {
    let mut vars = vec![];
    while let Ok(e) = self.r.try_read_start(&mut self.buf, Some("Substitution"))? {
      let (mut y1, mut y2) = <_>::default();
      for attr in e.attributes() {
        let attr = attr?;
        match attr.key.0 {
          b"y1" => y1 = IdentKind::from_usize(self.r.get_attr::<usize>(&attr.value)?),
          b"y2" => y2 = self.r.idx_attr(&attr.value)?,
          _ => {}
        }
      }
      self.r.end_tag(&mut self.buf)?;
      vars.push(match y1 {
        IdentKind::Bound => VarKind::Bound(BoundId(y2)),
        IdentKind::Const | IdentKind::DefConst => VarKind::Const(ConstId(y2)),
        _ => return self.r.err("bound or constant substitution"),
      })
    }
    Ok(vars)
  }

  fn parse_formula(&mut self) -> Result<Box<Formula>> {
    Ok(match self.parse_elem()? {
      Elem::Formula(f) => f,
      _ => return self.r.err("formula"),
    })
  }

  fn parse_term(&mut self) -> Result<Option<Box<Term>>> {
    Ok(match self.parse_elem()? {
      Elem::Term(t) => Some(t),
      Elem::End => None,
      _ => return self.r.err("term"),
    })
  }

  /// Like [`Self::parse_term`], but the element is required.
  fn parse_term1(&mut self) -> Result<Box<Term>> {
    match self.parse_term()? {
      Some(t) => Ok(t),
      None => self.r.err("term"),
    }
  }

  fn parse_terms(&mut self) -> Result<Vec<Term>> {
    let mut terms = vec![];
    while let Some(t) = self.parse_term()? {
      terms.push(*t)
    }
    Ok(terms)
  }

  fn parse_type(&mut self) -> Result<Option<Box<Type>>> {
    Ok(match self.parse_elem()? {
      Elem::Type(ty) => Some(ty),
      Elem::End => None,
      _ => return self.r.err("type"),
    })
  }

  /// Like [`Self::parse_type`], but the element is required.
  fn parse_type1(&mut self) -> Result<Box<Type>> {
    match self.parse_type()? {
      Some(ty) => Ok(ty),
      None => self.r.err("type"),
    }
  }

  fn parse_types(&mut self) -> Result<Vec<Type>> {
    self.r.read_start(&mut self.buf, Some("Type-List"))?;
    let mut tys = vec![];
    while let Some(t) = self.parse_type()? {
      tys.push(*t)
    }
    Ok(tys)
  }

  fn parse_proposition(&mut self) -> Result<Option<Box<Proposition>>> {
    let Ok(_) = self.r.try_read_start(&mut self.buf, Some("Proposition"))? else { return Ok(None) };
    let (label, f) = match self.parse_elem()? {
      Elem::Label(lab) => (lab, self.parse_formula()?),
      Elem::Formula(f) => (None, f),
      _ => return self.r.err("formula"),
    };
    self.r.end_tag(&mut self.buf)?;
    Ok(Some(Box::new(Proposition { label, f: *f })))
  }

  /// Like [`Self::parse_proposition`], but the element is required.
  fn parse_proposition1(&mut self) -> Result<Box<Proposition>> {
    match self.parse_proposition()? {
      Some(p) => Ok(p),
      None => self.r.err("Proposition"),
    }
  }

  fn parse_stmt(&mut self, shape: Shape) -> Result<Statement> {
    Ok(match shape {
      Shape::DiffuseStatement => {
        let (label, bl) = match self.parse_elem()? {
          Elem::Label(lab) => (lab, self.parse_block1()?),
          Elem::Block(bl) => (None, bl),
          _ => return self.r.err("block"),
        };
        self.r.end_tag(&mut self.buf)?;
        if !matches!(bl.kind, BlockKind::Now | BlockKind::Hereby) {
          return self.r.err("now or hereby block")
        }
        Statement::Now { end: bl.pos.1, label, items: bl.items }
      }
      Shape::CompactStatement => {
        let prop = self.parse_proposition1()?;
        let just = self.parse_justification()?;
        self.r.end_tag(&mut self.buf)?;
        Statement::Proposition { prop, just }
      }
      Shape::IterativeEquality => {
        let prop = self.parse_proposition1()?;
        let just = self.parse_justification()?;
        let mut steps = vec![];
        while let Ok(e) = self.r.try_read_start(&mut self.buf, Some("Iterative-Step"))? {
          steps.push(IterStep {
            pos: self.r.get_pos(&e)?,
            rhs: *self.parse_term1()?,
            just: *self.parse_justification()?,
          });
          self.r.end_tag(&mut self.buf)?;
        }
        Statement::IterEquality { prop, just, steps }
      }
    })
  }

  fn parse_justification(&mut self) -> Result<Box<Justification>> {
    Ok(Box::new(match self.parse_elem()? {
      Elem::Block(bl) if matches!(bl.kind, BlockKind::Proof) =>
        Justification::Block { pos: bl.pos, items: bl.items },
      Elem::Inference(pos, kind, refs) => Justification::Inference { pos, kind, refs },
      _ => return self.r.err("justification"),
    }))
  }

  fn parse_block(&mut self) -> Result<Option<Box<Block>>> {
    Ok(match self.parse_elem()? {
      Elem::Block(bl) => Some(bl),
      Elem::End => None,
      _ => return self.r.err("<Block>"),
    })
  }

  /// Like [`Self::parse_block`], but the element is required.
  fn parse_block1(&mut self) -> Result<Box<Block>> {
    match self.parse_block()? {
      Some(bl) => Ok(bl),
      None => self.r.err("Block"),
    }
  }

  fn parse_binder(&mut self) -> Result<Box<BinderGroup>> {
    Ok(match self.parse_elem()? {
      Elem::Binder(var) => var,
      _ => return self.r.err("binder group"),
    })
  }

  fn parse_pattern(&mut self) -> Result<Pattern> {
    Ok(match self.parse_elem()? {
      Elem::Pattern(pat) => pat,
      _ => return self.r.err("pattern"),
    })
  }

  fn parse_attr(&mut self) -> Result<Option<Attr>> {
    let Ok(e) = self.r.try_read_start(&mut self.buf, None)? else { return Ok(None) };
    Ok(Some(match e.local_name().as_ref() {
      b"Adjective" => {
        let (mut sym, mut spelling) = <(_, _)>::default();
        let pos = self.r.get_pos(&e)?;
        for attr in e.attributes() {
          let attr = attr?;
          match attr.key.0 {
            b"nr" => sym = AttrSymId(self.r.idx_attr(&attr.value)?),
            b"spelling" => spelling = attr.unescape_value()?.to_string(),
            _ => {}
          }
        }
        let args = self.parse_terms()?;
        Attr::Attr { pos, sym, spelling, args }
      }
      b"NegatedAdjective" => {
        let attr = Attr::Non { pos: self.r.get_pos(&e)?, attr: Box::new(self.parse_attr1()?) };
        self.r.end_tag(&mut self.buf)?;
        attr
      }
      _ => return self.r.err("adjective"),
    }))
  }

  /// Like [`Self::parse_attr`], but the element is required.
  fn parse_attr1(&mut self) -> Result<Attr> {
    match self.parse_attr()? {
      Some(a) => Ok(a),
      None => self.r.err("adjective"),
    }
  }

  fn parse_attrs(&mut self) -> Result<Vec<Attr>> {
    self.r.read_start(&mut self.buf, Some("Adjective-Cluster"))?;
    let mut attrs = vec![];
    while let Some(attr) = self.parse_attr()? {
      attrs.push(attr)
    }
    Ok(attrs)
  }

  fn parse_definiens(&mut self) -> Result<Option<Box<Definiens>>> {
    Ok(match self.parse_elem()? {
      Elem::Definiens(d) => Some(d),
      Elem::End => None,
      _ => return self.r.err("<Definiens>"),
    })
  }

  fn parse_locus(&mut self) -> Result<Option<Box<Variable>>> {
    let Ok(e) = self.r.try_read_start(&mut self.buf, Some("Locus"))? else { return Ok(None) };
    let v = self.r.parse_variable_attrs(&e)?;
    self.r.end_tag(&mut self.buf)?;
    Ok(Some(v))
  }

  /// Like [`Self::parse_locus`], but the element is required.
  fn parse_locus1(&mut self) -> Result<Box<Variable>> {
    match self.parse_locus()? {
      Some(v) => Ok(v),
      None => self.r.err("Locus"),
    }
  }

  fn parse_loci(&mut self, out: &mut Vec<Variable>) -> Result<()> {
    self.r.read_start(&mut self.buf, Some("Loci"))?;
    while let Some(v) = self.parse_locus()? {
      out.push(*v)
    }
    Ok(())
  }

  fn parse_right_pattern(&mut self) -> Result<(RightBrkSymId, String)> {
    let (mut rsym, mut rsp) = Default::default();
    let e = self.r.read_start(&mut self.buf, Some("Right-Circumflex-Symbol"))?;
    for attr in e.attributes() {
      let attr = attr?;
      match attr.key.0 {
        b"nr" => rsym = RightBrkSymId(self.r.idx_attr(&attr.value)?),
        b"spelling" => rsp = attr.unescape_value()?.to_string(),
        _ => {}
      }
    }
    self.r.end_tag(&mut self.buf)?;
    Ok((rsym, rsp))
  }

  fn parse_assumption(&mut self) -> Result<Assumption> {
    let e = self.r.read_start(&mut self.buf, None)?;
    let pos = self.r.get_pos(&e)?;
    let out = match e.local_name().as_ref() {
      b"Single-Assumption" => Assumption::Single { pos, prop: self.parse_proposition1()? },
      b"Collective-Assumption" => {
        let Elem::Conditions(conds) = self.parse_elem()? else { return self.r.err("<Conditions>") };
        Assumption::Collective { pos, conds }
      }
      _ => return self.r.err("assumption"),
    };
    self.r.end_tag(&mut self.buf)?;
    Ok(out)
  }

  fn parse_references(&mut self) -> Result<Vec<Reference>> {
    let mut refs = vec![];
    loop {
      match self.parse_elem()? {
        Elem::Reference(r) => refs.push(r),
        Elem::End => break,
        _ => return self.r.err("reference"),
      }
    }
    Ok(refs)
  }

  pub fn push_parse_item(&mut self, items: &mut Vec<Item>) -> Result<bool> {
    let Ok(e) = self.r.try_read_start(&mut self.buf, Some("Item"))? else { return Ok(false) };
    let (mut kind, mut property, mut shape, mut spelling, mut condition) = Default::default();
    let pos = self.r.get_pos(&e)?;
    for attr in e.attributes() {
      let attr = attr?;
      match attr.key.0 {
        b"kind" => kind = attr.value,
        b"property" => match (*attr.value).try_into() {
          Ok(p) => property = Some(p),
          Err(_) => return self.r.err("property kind"),
        },
        b"shape" => shape = attr.value,
        b"spelling" => spelling = Some(attr.unescape_value()?),
        b"condition" => condition = attr.value,
        // Some((*attr.value).try_into().unwrap()),
        _ => {}
      }
    }
    let mut end_tag = false;
    let kind = match &*kind {
      b"Definition-Item" => {
        let Block { pos, kind: BlockKind::Def(kind), items } = *self.parse_block1()? else {
          return self.r.err("definition block")
        };
        ItemKind::Block { end: pos.1, kind, items }
      }
      b"Scheme-Block-Item" => {
        let Block { pos, kind: BlockKind::Scheme, mut items } = *self.parse_block1()? else {
          return self.r.err("scheme block")
        };
        if items.is_empty() {
          return self.r.err("scheme head")
        }
        let ItemKind::SchemeHead(head) = items.remove(0).kind else {
          return self.r.err("scheme head")
        };
        ItemKind::SchemeBlock(Box::new(SchemeBlock { end: pos.1, head: *head, items }))
      }
      b"Scheme-Head" => {
        let e = self.r.read_start(&mut self.buf, Some("Scheme"))?;
        let (mut spelling, mut nr) = <_>::default();
        for attr in e.attributes() {
          let attr = attr?;
          match attr.key.0 {
            b"nr" => nr = Some(SchId(self.r.idx_attr(&attr.value)?)),
            b"spelling" => spelling = attr.unescape_value()?.to_string(),
            _ => {}
          }
        }
        self.r.end_tag(&mut self.buf)?;
        self.r.read_start(&mut self.buf, Some("Schematic-Variables"))?;
        let mut groups = vec![];
        while let Event::Start(e) = self.r.read_event(&mut self.buf)? {
          let pos = self.r.get_pos(&e)?;
          match e.local_name().as_ref() {
            b"Predicate-Segment" => groups.push(SchemeBinderGroup::Pred {
              pos,
              vars: self.parse_variables()?,
              tys: self.parse_types()?,
            }),
            b"Functor-Segment" => groups.push(SchemeBinderGroup::Func {
              pos,
              vars: self.parse_variables()?,
              tys: self.parse_types()?,
              ret: match self.parse_elem()? {
                Elem::TypeSpecification(ty) => *ty,
                _ => return self.r.err("<Type-Specification>"),
              },
            }),
            _ => return self.r.err("scheme variable group"),
          }
          self.r.end_tag(&mut self.buf)?;
        }
        let concl = *self.parse_formula()?;
        let mut prems = vec![];
        if self.r.try_read_start(&mut self.buf, Some("Provisional-Formulas"))?.is_ok() {
          while let Some(p) = self.parse_proposition()? {
            prems.push(*p)
          }
        } else {
          end_tag = true;
        }
        let sym = if spelling.is_empty() { None } else { Some(spelling.into()) };
        ItemKind::SchemeHead(Box::new(SchemeHead { sym, nr, groups, concl, prems }))
      }
      b"Theorem-Item" =>
        ItemKind::Theorem { prop: self.parse_proposition1()?, just: self.parse_justification()? },
      b"Reservation" => {
        let vars = self.parse_variables()?;
        let tys = if self.msm { Some(self.parse_types()?) } else { None };
        let ty = self.parse_type1()?;
        let fvars = if self.msm {
          let mut out = IdxVec::default();
          while let Ok(e) = self.r.try_read_start(&mut self.buf, Some("SetMember"))? {
            let Some(attr) = e.try_get_attribute(b"x")? else { return self.r.err("x attribute") };
            out.push(ReservedId(self.r.idx_attr(&attr.value)?));
            self.r.end_tag(&mut self.buf)?;
          }
          end_tag = true;
          Some(out)
        } else {
          None
        };
        ItemKind::Reservation(vec![Reservation { vars, tys, ty, fvars }])
      }
      b"Section-Pragma" => ItemKind::Section,
      b"Choice-Statement" => {
        let mut vars = vec![];
        let conds = loop {
          match self.parse_elem()? {
            Elem::Binder(var) => vars.push(*var),
            Elem::Conditions(conds) => break conds,
            _ => return self.r.err("<Conditions>"),
          }
        };
        ItemKind::Consider { vars, conds, just: self.parse_justification()? }
      }
      b"Type-Changing-Statement" => {
        let mut vars = vec![];
        let ty = loop {
          match self.parse_elem()? {
            Elem::Variable(var) => vars.push(ReconsiderVar::Var(*var)),
            Elem::Equality(var, tm) => vars.push(ReconsiderVar::Equality { var: *var, tm: *tm }),
            Elem::Type(ty) => break ty,
            _ => return self.r.err("variable, equality, or type"),
          }
        };
        ItemKind::Reconsider { vars, ty, just: self.parse_justification()? }
      }
      b"Private-Functor-Definition" => ItemKind::DefFunc {
        var: self.parse_variable1()?,
        tys: self.parse_types()?,
        value: self.parse_term1()?,
      },
      b"Private-Predicate-Definition" => ItemKind::DefPred {
        var: self.parse_variable1()?,
        tys: self.parse_types()?,
        value: self.parse_formula()?,
      },
      b"Constant-Definition" =>
        ItemKind::Set(vec![SetDecl { var: self.parse_variable1()?, value: self.parse_term1()? }]),
      b"Generalization" | b"Loci-Declaration" =>
        ItemKind::Let { vars: vec![*self.parse_binder()?], conds: vec![] },
      b"Existential-Assumption" => {
        let mut vars = vec![];
        let conds = loop {
          match self.parse_elem()? {
            Elem::Binder(var) => vars.push(*var),
            Elem::Conditions(conds) => break conds,
            _ => return self.r.err("<Conditions>"),
          }
        };
        ItemKind::Given { vars, conds }
      }
      b"Exemplification" => {
        let (mut var, mut term) = (None, None);
        loop {
          match self.parse_elem()? {
            Elem::Variable(v) => var = Some(v),
            Elem::Term(t) => term = Some(t),
            Elem::End => break,
            _ => return self.r.err("variable or term"),
          }
        }
        end_tag = true;
        let term = match (term, &var) {
          (Some(t), _) => t,
          (None, Some(v)) => Box::new(v.to_term()),
          (None, None) => return self.r.err("variable or term"),
        };
        ItemKind::Take(vec![TakeDecl { var, term }])
      }
      b"Unfolding" => {
        self.r.read_start(&mut self.buf, Some("Unfolding"))?;
        ItemKind::Unfold(self.parse_references()?)
      }
      b"Per-Cases" => ItemKind::PerCasesHead(self.parse_justification()?),
      b"Regular-Statement" => {
        let Ok(shape) = (*shape).try_into() else { return self.r.err("statement shape") };
        end_tag = true;
        ItemKind::Statement(self.parse_stmt(shape)?)
      }
      b"Conclusion" => {
        let Ok(shape) = (*shape).try_into() else { return self.r.err("statement shape") };
        end_tag = true;
        ItemKind::Thus(self.parse_stmt(shape)?)
      }
      b"Case-Block" => {
        let mut bl = self.parse_block1()?;
        let BlockKind::Case(kind) = bl.kind else { return self.r.err("case or suppose block") };
        if bl.items.is_empty() {
          return self.r.err("case/suppose head")
        }
        let hyp = Box::new(match bl.items.remove(0).kind {
          ItemKind::CaseHead(k2, hyp) if k2 == kind => hyp,
          _ => return self.r.err("case/suppose head"),
        });
        let bl = CaseBlock { end: bl.pos.1, hyp, items: bl.items };
        let Some(last) = items.last_mut() else { return self.r.err("per cases head") };
        let it = &mut last.kind;
        match it {
          ItemKind::PerCases { kind: k2, blocks, .. } if *k2 == kind => blocks.push(bl),
          _ => {
            let ItemKind::PerCasesHead(just) = std::mem::take(it) else {
              return self.r.err("per cases head")
            };
            *it = ItemKind::PerCases { just, kind, blocks: vec![bl] };
          }
        }
        self.r.end_tag(&mut self.buf)?;
        return Ok(true)
      }
      b"Case-Head" => ItemKind::CaseHead(CaseKind::Case, self.parse_assumption()?),
      b"Suppose-Head" => ItemKind::CaseHead(CaseKind::Suppose, self.parse_assumption()?),
      b"Assumption" => ItemKind::Assume(self.parse_assumption()?),
      b"Correctness-Condition" => {
        let Ok(kind) = (*condition).try_into() else {
          return self.r.err("correctness condition kind")
        };
        let Some(corr) = items.last_mut().and_then(|it| it.kind.corr_mut()) else {
          return self.r.err("item with correctness conditions")
        };
        let corr = corr.0;
        corr.push(CorrCond { pos, kind, just: *self.parse_justification()? });
        self.r.end_tag(&mut self.buf)?;
        return Ok(true)
      }
      b"Correctness" => {
        self.r.read_start(&mut self.buf, Some("CorrectnessConditions"))?;
        // let mut conds = vec![];
        while let Ok(_e) = self.r.try_read_start(&mut self.buf, Some("Correctness"))? {
          // conds.push((*e.try_get_attribute(b"condition").unwrap().unwrap().value).try_into().unwrap());
          self.r.end_tag(&mut self.buf)?;
        }
        let Some(corr) = items.last_mut().and_then(|it| it.kind.corr_mut()) else {
          return self.r.err("item with correctness conditions")
        };
        let corr = corr.1;
        if corr.is_some() {
          return self.r.err("at most one correctness block")
        }
        *corr = Some(Correctness { pos, just: *self.parse_justification()? });
        self.r.end_tag(&mut self.buf)?;
        return Ok(true)
      }
      b"Property" => {
        let Some(props) = items.last_mut().and_then(|it| it.kind.property_mut()) else {
          return self.r.err("item with properties")
        };
        let Some(kind) = property else { return self.r.err("property attribute") };
        props.push(Property { pos, kind, just: self.parse_justification()? });
        self.r.end_tag(&mut self.buf)?;
        return Ok(true)
      }
      b"Mode-Definition" => {
        let (redef, pat) = match self.parse_elem()? {
          Elem::Redefine => (true, self.parse_pattern()?),
          Elem::Pattern(pat) => (false, pat),
          _ => return self.r.err("pattern"),
        };
        let Pattern::Mode(pat) = pat else { return self.r.err("mode pattern") };
        let e = self.r.read_start(&mut self.buf, None)?;
        let kind = match e.local_name().as_ref() {
          b"Expandable-Mode" => DefModeKind::Expandable { expansion: self.parse_type1()? },
          b"Standard-Mode" => {
            let (spec, def) = match self.parse_elem()? {
              Elem::TypeSpecification(ty) => (Some(ty), self.parse_definiens()?),
              Elem::Definiens(d) => (None, Some(d)),
              Elem::End => (None, None),
              _ => return self.r.err("<Definiens>"),
            };
            end_tag = def.is_none();
            DefModeKind::Standard { spec, def }
          }
          _ => return self.r.err("def mode kind"),
        };
        self.r.end_tag(&mut self.buf)?;
        let kind = DefinitionKind::Mode { pat, kind };
        let body = DefinitionBody { redef, conds: vec![], corr: None, props: vec![] };
        ItemKind::Definition(Box::new(Definition { kind, body }))
      }
      b"Attribute-Definition" => {
        let (redef, pat) = match self.parse_elem()? {
          Elem::Redefine => (true, self.parse_pattern()?),
          Elem::Pattern(pat) => (false, pat),
          _ => return self.r.err("pattern"),
        };
        let Pattern::Attr(pat) = pat else { return self.r.err("attribute pattern") };
        let def = self.parse_definiens()?;
        end_tag = def.is_none();
        let kind = DefinitionKind::Attr { pat, def };
        let body = DefinitionBody { redef, conds: vec![], corr: None, props: vec![] };
        ItemKind::Definition(Box::new(Definition { kind, body }))
      }
      b"Predicate-Definition" => {
        let (redef, pat) = match self.parse_elem()? {
          Elem::Redefine => (true, self.parse_pattern()?),
          Elem::Pattern(pat) => (false, pat),
          _ => return self.r.err("pattern"),
        };
        let Pattern::Pred(pat) = pat else { return self.r.err("predicate pattern") };
        let def = self.parse_definiens()?;
        end_tag = def.is_none();
        let kind = DefinitionKind::Pred { pat, def };
        let body = DefinitionBody { redef, conds: vec![], corr: None, props: vec![] };
        ItemKind::Definition(Box::new(Definition { kind, body }))
      }
      b"Functor-Definition" => {
        let shape = match &*shape {
          b"No-Definiens" => None,
          b"Means" => Some(false),
          b"Equals" => Some(true),
          _ => return self.r.err("functor shape"),
        };
        let (redef, pat) = match self.parse_elem()? {
          Elem::Redefine => (true, self.parse_pattern()?),
          Elem::Pattern(pat) => (false, pat),
          _ => return self.r.err("pattern"),
        };
        let Pattern::Func(pat) = pat else { return self.r.err("functor pattern") };
        let (spec, def) = match self.parse_elem()? {
          Elem::TypeSpecification(ty) => (Some(ty), self.parse_definiens()?),
          Elem::Definiens(d) => (None, Some(d)),
          Elem::End => (None, None),
          _ => return self.r.err("<Definiens>"),
        };
        end_tag = def.is_none();
        let shape2 = def.as_ref().map(|d| matches!(d.kind, DefValue::Term(_)));
        if shape != shape2 {
          return self.r.err("matching definiens shape")
        }
        let kind = DefinitionKind::Func { pat, spec, def };
        let body = DefinitionBody { redef, conds: vec![], corr: None, props: vec![] };
        ItemKind::Definition(Box::new(Definition { kind, body }))
      }
      b"Structure-Definition" => {
        self.r.read_start(&mut self.buf, Some("Ancestors"))?;
        let mut parents = vec![];
        while let Some(t) = self.parse_type()? {
          parents.push(*t);
        }
        let e = self.r.read_start(&mut self.buf, Some("Structure-Pattern"))?;
        let (mut sym, mut spelling) = <_>::default();
        for attr in e.attributes() {
          let attr = attr?;
          match attr.key.0 {
            b"nr" => sym = StructSymId(self.r.idx_attr(&attr.value)?),
            b"spelling" => spelling = attr.unescape_value()?.to_string(),
            _ => {}
          }
        }
        let mut args = vec![];
        self.parse_loci(&mut args)?;
        let mut fields = vec![];
        while let Ok(e) = self.r.try_read_start(&mut self.buf, Some("Field-Segment"))? {
          let pos = self.r.get_pos(&e)?;
          let mut vars = vec![];
          let ty = loop {
            match self.parse_elem()? {
              Elem::Selector(field) => vars.push(field),
              Elem::Type(ty) => break ty,
              _ => return self.r.err("type"),
            }
          };
          self.r.end_tag(&mut self.buf)?;
          fields.push(FieldGroup { pos, vars, ty: *ty })
        }
        let pat = PatternStruct { sym, spelling, args };
        ItemKind::DefStruct(Box::new(DefStruct { parents, fields, pat }))
      }
      b"Pred-Synonym" => {
        let Pattern::Pred(orig) = self.parse_pattern()? else { return self.r.err("pred pattern") };
        let Pattern::Pred(new) = self.parse_pattern()? else { return self.r.err("pred pattern") };
        ItemKind::PatternRedef(PatternRedef::Pred { new, orig, positive: true })
      }
      b"Pred-Antonym" => {
        let Pattern::Pred(orig) = self.parse_pattern()? else { return self.r.err("pred pattern") };
        let Pattern::Pred(new) = self.parse_pattern()? else { return self.r.err("pred pattern") };
        ItemKind::PatternRedef(PatternRedef::Pred { new, orig, positive: false })
      }
      b"Func-Synonym" => {
        let Pattern::Func(orig) = self.parse_pattern()? else { return self.r.err("func pattern") };
        let Pattern::Func(new) = self.parse_pattern()? else { return self.r.err("func pattern") };
        ItemKind::PatternRedef(PatternRedef::Func { new, orig })
      }
      b"Mode-Synonym" => {
        let Pattern::Mode(orig) = self.parse_pattern()? else { return self.r.err("mode pattern") };
        let Pattern::Mode(new) = self.parse_pattern()? else { return self.r.err("mode pattern") };
        ItemKind::PatternRedef(PatternRedef::Mode { new, orig })
      }
      b"Attr-Synonym" => {
        let Pattern::Attr(orig) = self.parse_pattern()? else { return self.r.err("attr pattern") };
        let Pattern::Attr(new) = self.parse_pattern()? else { return self.r.err("attr pattern") };
        ItemKind::PatternRedef(PatternRedef::Attr { new, orig, positive: true })
      }
      b"Attr-Antonym" => {
        let Pattern::Attr(orig) = self.parse_pattern()? else { return self.r.err("attr pattern") };
        let Pattern::Attr(new) = self.parse_pattern()? else { return self.r.err("attr pattern") };
        ItemKind::PatternRedef(PatternRedef::Attr { new, orig, positive: false })
      }
      b"Cluster" => {
        let e = self.r.read_start(&mut self.buf, None)?;
        let kind = match e.local_name().as_ref() {
          b"Existential-Registration" =>
            ClusterDeclKind::Exist { concl: self.parse_attrs()?, ty: self.parse_type1()? },
          b"Conditional-Registration" => ClusterDeclKind::Cond {
            antecedent: self.parse_attrs()?,
            concl: self.parse_attrs()?,
            ty: self.parse_type1()?,
          },
          b"Functorial-Registration" => {
            let term = self.parse_term1()?;
            let concl = self.parse_attrs()?;
            let ty = self.parse_type()?;
            end_tag = ty.is_none();
            ClusterDeclKind::Func { term, concl, ty }
          }
          _ => return self.r.err("cluster registration kind"),
        };
        self.r.end_tag(&mut self.buf)?;
        ItemKind::Cluster(Box::new(Cluster { kind, conds: vec![], corr: None }))
      }
      b"Identify" => {
        let Pattern::Func(rhs) = self.parse_pattern()? else {
          return self.r.err("functor pattern")
        };
        let Pattern::Func(lhs) = self.parse_pattern()? else {
          return self.r.err("functor pattern")
        };
        let mut eqs = vec![];
        loop {
          match self.parse_elem()? {
            Elem::LociEquality(x1, x2) => eqs.push((*x1, *x2)),
            Elem::End => break,
            _ => return self.r.err("<LociEquality>"),
          }
        }
        end_tag = true;
        let id = IdentifyFunc { lhs, rhs, eqs, conds: vec![], corr: None };
        ItemKind::IdentifyFunc(Box::new(id))
      }
      b"Property-Registration" => {
        if !matches!(property, Some(PropertyKind::Sethood)) {
          return self.r.err("sethood property")
        }
        ItemKind::SethoodRegistration { ty: self.parse_type1()?, just: self.parse_justification()? }
      }
      b"Reduction" => {
        let (t1, t2) = (self.parse_term1()?, self.parse_term1()?);
        let (from, to) = if self.msm { (t2, t1) } else { (t1, t2) }; // Yes, this is silly
        ItemKind::Reduction(Box::new(Reduction { from, to, conds: vec![], corr: None }))
      }
      b"Pragma" => {
        let Some(spelling) = spelling else { return self.r.err("spelling attribute") };
        // the `FromStr` impl for pragmas is infallible
        ItemKind::Pragma(spelling.parse().unwrap())
      }
      _ => return self.r.err("item kind"),
    };
    if !end_tag {
      self.r.end_tag(&mut self.buf)?;
    }
    items.push(Item { pos, kind });
    Ok(true)
  }

  pub fn parse_items(&mut self) -> Result<Vec<Item>> {
    let mut items = vec![];
    while self.push_parse_item(&mut items)? {}
    Ok(items)
  }

  fn parse_elem(&mut self) -> Result<Elem> {
    // Note: this is only really an issue in debug mode, but this function
    // is both recursive and has a pretty big stack frame, so it is liable to run out
    // of stack space on some of the deep `p1 & p2 & ... & pn` expressions in some MML articles.
    // We use the stacker library here to allocate space on the heap to avoid stack overflow.
    stacker::maybe_grow(0x20000, 0x100000, || {
      Ok(if let Event::Start(e) = self.r.read_event(&mut self.buf)? {
        let elem = match e.local_name().as_ref() {
          b"Block" => {
            let mut kind: Cow<'_, [u8]> = Default::default();
            // The block's start (`line`/`col`) and end (`posline`/`poscol`) are
            // recovered as the two endpoints of the element's position span.
            let bl = self.r.get_pos(&e)?;
            let (start, end) = (Span::at(bl.start), Span::at(bl.end));
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"kind" => kind = attr.value,
                _ => {}
              }
            }
            return Ok(Elem::Block(Box::new(Block {
              kind: match &*kind {
                b"Now-Reasoning" => BlockKind::Now,
                b"Hereby-Reasoning" => BlockKind::Hereby,
                b"Proof" => BlockKind::Proof,
                b"Definitional-Block" => BlockKind::Def(types::BlockKind::Definition),
                b"Notation-Block" => BlockKind::Def(types::BlockKind::Notation),
                b"Registration-Block" => BlockKind::Def(types::BlockKind::Registration),
                b"Case" => BlockKind::Case(CaseKind::Case),
                b"Suppose" => BlockKind::Case(CaseKind::Suppose),
                b"Scheme-Block" => BlockKind::Scheme,
                _ => return self.r.err("block kind"),
              },
              pos: (start, end),
              items: self.parse_items()?,
            })))
          }
          b"Straightforward-Justification" => {
            let pos = self.r.get_pos(&e)?;
            let (mut link, mut refs) = (None, vec![]);
            loop {
              match self.parse_elem()? {
                Elem::Link(pos) => {
                  if self.msm {
                    // MSM mode adds a garbage extra local ref for linked inferences.
                    // We can't use it anyway because they aren't labeled, so we just discard it
                    match self.parse_elem()? {
                      Elem::Reference(r) if matches!(r.kind, ReferenceKind::Priv(_)) => {}
                      _ => return self.r.err("local reference for link"),
                    }
                  }
                  link = Some(pos)
                }
                Elem::Reference(r) => refs.push(r),
                Elem::End => break,
                _ => return self.r.err("link or reference"),
              }
            }
            return Ok(Elem::Inference(pos, InferenceKind::By { link }, refs))
          }
          b"Scheme-Justification" => {
            let (mut art, mut sch, mut id, mut spelling) = <(_, _, _, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => art = self.r.get_attr(&attr.value)?,
                b"idnr" => id = self.r.get_attr::<u32>(&attr.value)?,
                b"schnr" => sch = self.r.get_attr::<u32>(&attr.value)?,
                b"spelling" => spelling = attr.unescape_value()?.to_string(),
                _ => {}
              }
            }
            let refs = self.parse_references()?;
            let sch = if art == ArticleId::SELF {
              if let Some(sch) = sch.checked_sub(1) {
                let spelling = self.r.to_article(spelling.as_bytes())?;
                SchRef::Resolved { art, spelling, sch: SchId(sch) }
              } else {
                SchRef::UnresolvedPriv(spelling)
              }
            } else {
              let spelling = self.r.to_article(spelling.as_bytes())?;
              let Some(id) = id.checked_sub(1) else { return self.r.err("scheme number") };
              SchRef::Resolved { art, spelling, sch: SchId(id) }
            };
            return Ok(Elem::Inference(pos, InferenceKind::From(sch), refs))
          }
          b"Implicitly-Qualified-Segment" => {
            let nr = match e.try_get_attribute(b"nr")? {
              Some(attr) => Some(self.r.get_attr::<u32>(&attr.value)?),
              None => None,
            };
            let var = self.parse_variable1()?;
            let pos = var.pos;
            let ty = if self.msm {
              let Some(nr) = nr else { return self.r.err("nr attribute") };
              let Some(nr) = nr.checked_sub(1) else { return self.r.err("reservation nr") };
              let group = ResGroupId(nr);
              Some(Box::new(Type::Reservation { pos, group, subst: self.parse_substitution()? }))
            } else {
              self.r.end_tag(&mut self.buf)?;
              None
            };
            return Ok(Elem::Binder(Box::new(BinderGroup { vars: vec![*var], ty })))
          }
          b"Explicitly-Qualified-Segment" => Elem::Binder(Box::new(BinderGroup {
            vars: self.parse_variables()?,
            ty: Some(self.parse_type1()?),
          })),
          b"Conditions" => {
            let mut conds = vec![];
            while let Some(p) = self.parse_proposition()? {
              conds.push(*p);
            }
            return Ok(Elem::Conditions(conds))
          }
          b"Variable" => Elem::Variable(self.r.parse_variable_attrs(&e)?),
          b"Equality" => Elem::Equality(self.parse_variable1()?, self.parse_term1()?),
          b"Redefine" => Elem::Redefine,
          b"Type-Specification" => Elem::TypeSpecification(self.parse_type1()?),
          b"Definiens" => {
            let (mut kind, mut is_term) = (<Cow<'_, [u8]>>::default(), false);
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"kind" => kind = attr.value,
                b"shape" =>
                  is_term = match &*attr.value {
                    b"Term-Expression" => true,
                    b"Formula-Expression" => false,
                    _ => return self.r.err("definiens shape"),
                  },
                _ => {}
              }
            }
            let (label, end_tag, kind) = match &*kind {
              b"Simple-Definiens" if is_term => {
                let (lab, t) = match self.parse_elem()? {
                  Elem::Label(lab) => (lab, self.parse_term1()?),
                  Elem::Term(t) => (None, t),
                  _ => return self.r.err("term"),
                };
                (lab, false, DefValue::Term(DefBody { cases: vec![], otherwise: Some(t) }))
              }
              b"Simple-Definiens" => {
                let (lab, f) = match self.parse_elem()? {
                  Elem::Label(lab) => (lab, self.parse_formula()?),
                  Elem::Formula(f) => (None, f),
                  _ => return self.r.err("formula"),
                };
                (lab, false, DefValue::Formula(DefBody { cases: vec![], otherwise: Some(f) }))
              }
              b"Conditional-Definiens" if is_term => {
                let (mut lab, mut cases) = (None, vec![]);
                let otherwise = loop {
                  match self.parse_elem()? {
                    Elem::Label(l) => lab = l,
                    Elem::DefCaseTerm(case) => cases.push(case),
                    Elem::End => break None,
                    Elem::Term(t) => break Some(t),
                    _ => return self.r.err("definiens case or term"),
                  }
                };
                (lab, otherwise.is_none(), DefValue::Term(DefBody { cases, otherwise }))
              }
              b"Conditional-Definiens" => {
                let (mut lab, mut cases) = (None, vec![]);
                let otherwise = loop {
                  match self.parse_elem()? {
                    Elem::Label(l) => lab = l,
                    Elem::DefCaseFormula(case) => cases.push(case),
                    Elem::End => break None,
                    Elem::Formula(t) => break Some(t),
                    _ => return self.r.err("definiens case or formula"),
                  }
                };
                (lab, otherwise.is_none(), DefValue::Formula(DefBody { cases, otherwise }))
              }
              _ => return self.r.err("definiens kind"),
            };
            if !end_tag {
              self.r.end_tag(&mut self.buf)?;
            }
            return Ok(Elem::Definiens(Box::new(Definiens { pos, label, kind })))
          }
          b"LociEquality" => Elem::LociEquality(self.parse_locus1()?, self.parse_locus1()?),
          b"Label" => {
            let (mut id, mut spelling) = <(_, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"labelnr" => id = self.r.get_attr::<u32>(&attr.value)?.checked_sub(1).map(LabelId),
                b"spelling" => spelling = attr.unescape_value()?,
                _ => {}
              }
            }
            Elem::Label((!spelling.is_empty()).then(|| {
              let spelling = spelling.into();
              Box::new(Label { pos, id, spelling })
            }))
          }
          b"Link" => Elem::Link(self.r.get_pos(&e)?),
          b"Local-Reference" => {
            let pos = self.r.get_pos(&e)?;
            let kind = if self.msm {
              let Some(attr) = e.try_get_attribute(b"labelnr")? else {
                return self.r.err("labelnr attribute")
              };
              ReferenceKind::Priv(self.r.get_attr::<u32>(&attr.value)?.checked_sub(1).map(LabelId))
            } else {
              let Some(attr) = e.try_get_attribute(b"spelling")? else {
                return self.r.err("spelling attribute")
              };
              ReferenceKind::UnresolvedPriv(attr.unescape_value()?.to_string())
            };
            Elem::Reference(Reference { pos, kind })
          }
          b"Theorem-Reference" => {
            let (mut art, mut id, mut spelling) = <(_, _, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => art = self.r.get_attr(&attr.value)?,
                b"spelling" => spelling = self.r.to_article(attr.unescape_value()?.as_bytes())?,
                b"number" => id = ThmId(self.r.idx_attr(&attr.value)?),
                _ => {}
              }
            }
            let refs = vec![RefFragment::Thm { pos, id }];
            Elem::Reference(Reference { pos, kind: ReferenceKind::Global { art, spelling, refs } })
          }
          b"Definition-Reference" => {
            let (mut art, mut id, mut spelling) = <(_, _, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => art = self.r.get_attr(&attr.value)?,
                b"spelling" => spelling = self.r.to_article(attr.unescape_value()?.as_bytes())?,
                b"number" => id = DefId(self.r.idx_attr(&attr.value)?),
                _ => {}
              }
            }
            let refs = vec![RefFragment::Def { pos, id }];
            Elem::Reference(Reference { pos, kind: ReferenceKind::Global { art, spelling, refs } })
          }
          b"Partial-Definiens" => match self.parse_elem()? {
            Elem::Term(case) => Elem::DefCaseTerm(DefCase { case, guard: self.parse_formula()? }),
            Elem::Formula(case) =>
              Elem::DefCaseFormula(DefCase { case, guard: self.parse_formula()? }),
            _ => return self.r.err("term or formula"),
          },
          b"Placeholder-Term" => {
            let mut nr = Default::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              if attr.key.0 == b"nr" {
                nr = LocusId(self.r.idx_attr_u8(&attr.value)?)
              }
            }
            Elem::Term(Box::new(Term::Placeholder { pos, nr }))
          }
          b"Numeral-Term" => {
            let mut value = Default::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"number" => value = self.r.get_attr(&attr.value)?,
                _ => {}
              }
            }
            Elem::Term(Box::new(Term::Numeral { pos, value }))
          }
          b"Simple-Term" => {
            let (mut kind, mut var, mut spelling) = <(_, _, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                // b"idnr" => sym = self.r.idx_attr(&attr.value)?,
                b"spelling" => spelling = attr.unescape_value()?.to_string(),
                // b"origin" => origin = self.r.get_attr(&attr.value)?,
                b"kind" => kind = self.r.get_attr(&attr.value)?,
                // b"serialnr" => serial = self.r.get_attr(&attr.value)?,
                b"varnr" => var = self.r.idx_attr(&attr.value)?,
                _ => {}
              }
            }
            let kind = match kind {
              IdentKind::Free => None,
              IdentKind::Bound => Some(VarKind::Bound(BoundId(var))),
              IdentKind::Const | IdentKind::DefConst => Some(VarKind::Const(ConstId(var))),
              _ => return self.r.err("variable kind"),
            };
            let term = Term::Var { pos, kind, spelling };
            Elem::Term(Box::new(term))
          }
          b"Private-Functor-Term" => {
            let (mut shape, mut var, mut spelling) = <(_, _, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                // b"idnr" => id = self.r.idx_attr(&attr.value)?,
                b"spelling" => spelling = attr.unescape_value()?,
                b"shape" => shape = self.r.get_attr(&attr.value)?,
                // b"serialnr" => serial = self.r.get_attr(&attr.value)?,
                b"nr" => var = self.r.idx_attr(&attr.value)?,
                _ => {}
              }
            }
            let (spelling, args) = (spelling.into(), self.parse_terms()?);
            let kind = match shape {
              IdentKind::Free => None,
              IdentKind::PrivFunc => Some(PrivFuncKind::PrivFunc(PrivFuncId(var))),
              IdentKind::SchFunc => Some(PrivFuncKind::SchFunc(SchFuncId(var))),
              _ => return self.r.err("private functor kind"),
            };
            let term = Term::PrivFunc { pos, kind, spelling, args };
            return Ok(Elem::Term(Box::new(term)))
          }
          b"Infix-Term" => {
            let (mut sym, mut spelling) = <(_, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => sym = FuncSymId(self.r.idx_attr(&attr.value)?),
                b"spelling" => spelling = attr.unescape_value()?.to_string(),
                _ => {}
              }
            }
            self.r.read_start(&mut self.buf, Some("Arguments"))?;
            let mut args = self.parse_terms()?;
            let Ok(left) = args.len().try_into() else {
              return self.r.err("at most 255 arguments")
            };
            self.r.read_start(&mut self.buf, Some("Arguments"))?;
            while let Some(t) = self.parse_term()? {
              args.push(*t);
            }
            Elem::Term(Box::new(Term::Infix { pos, sym, spelling, left, args }))
          }
          b"Circumfix-Term" => {
            let (mut lsym, mut lspelling) = <(_, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => lsym = LeftBrkSymId(self.r.idx_attr(&attr.value)?),
                b"spelling" => lspelling = attr.unescape_value()?.to_string(),
                _ => {}
              }
            }
            let ((rsym, rspelling), args) = (self.parse_right_pattern()?, self.parse_terms()?);
            let term = Term::Bracket { pos, lsym, lspelling, rsym, rspelling, args };
            return Ok(Elem::Term(Box::new(term)))
          }
          b"Aggregate-Term" => {
            let (mut sym, mut spelling) = <(_, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => sym = StructSymId(self.r.idx_attr(&attr.value)?),
                b"spelling" => spelling = attr.unescape_value()?.to_string(),
                _ => {}
              }
            }
            let args = self.parse_terms()?;
            return Ok(Elem::Term(Box::new(Term::Aggregate { pos, sym, spelling, args })))
          }
          b"Forgetful-Functor-Term" => {
            let (mut sym, mut spelling) = <(_, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => sym = StructSymId(self.r.idx_attr(&attr.value)?),
                b"spelling" => spelling = attr.unescape_value()?.to_string(),
                _ => {}
              }
            }
            let arg = self.parse_term1()?;
            Elem::Term(Box::new(Term::SubAggr { pos, sym, spelling, arg }))
          }
          b"Selector-Term" => {
            let (mut sym, mut spelling) = <(_, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => sym = SelSymId(self.r.idx_attr(&attr.value)?),
                b"spelling" => spelling = attr.unescape_value()?.to_string(),
                _ => {}
              }
            }
            let arg = self.parse_term1()?;
            Elem::Term(Box::new(Term::Selector { pos, sym, spelling, arg }))
          }
          b"Internal-Selector-Term" => {
            let (mut sym, mut spelling, mut id) = <(_, _, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => sym = SelSymId(self.r.idx_attr(&attr.value)?),
                b"varnr" => id = self.r.get_attr::<u32>(&attr.value)?.checked_sub(1).map(ConstId),
                b"spelling" => spelling = attr.unescape_value()?.to_string(),
                _ => {}
              }
            }
            Elem::Term(Box::new(Term::InternalSelector { pos, sym, spelling, id }))
          }
          b"Qualification-Term" => {
            let pos = self.r.get_pos(&e)?;
            let term = self.parse_term1()?;
            let ty = self.parse_type1()?;
            Elem::Term(Box::new(Term::Qua { pos, term, ty }))
          }
          b"Global-Choice-Term" => {
            let pos = self.r.get_pos(&e)?;
            let ty = self.parse_type1()?;
            Elem::Term(Box::new(Term::The { pos, ty }))
          }
          b"Simple-Fraenkel-Term" => {
            let pos = self.r.get_pos(&e)?;
            let mut vars = vec![];
            let scope = loop {
              match self.parse_elem()? {
                Elem::Binder(var) => vars.push(*var),
                Elem::Term(t) => break t,
                _ => return self.r.err("<Conditions>"),
              }
            };
            Elem::Term(Box::new(Term::Fraenkel { pos, vars, scope, compr: None, nameck: None }))
          }
          b"Fraenkel-Term" => {
            let pos = self.r.get_pos(&e)?;
            let mut vars = vec![];
            let scope = loop {
              match self.parse_elem()? {
                Elem::Binder(var) => vars.push(*var),
                Elem::Term(t) => break t,
                _ => return self.r.err("<Conditions>"),
              }
            };
            let compr = Some(self.parse_formula()?);
            Elem::Term(Box::new(Term::Fraenkel { pos, vars, scope, compr, nameck: None }))
          }
          b"it-Term" => {
            let pos = self.r.get_pos(&e)?;
            Elem::Term(Box::new(Term::It { pos }))
          }
          b"Standard-Type" => {
            let (mut sym, mut spelling) = <(_, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => sym = ModeSymId(self.r.idx_attr(&attr.value)?),
                b"spelling" => spelling = attr.unescape_value()?.to_string(),
                _ => {}
              }
            }
            let args = self.parse_terms()?;
            return Ok(Elem::Type(Box::new(Type::Mode { pos, sym, spelling, args })))
          }
          b"Struct-Type" => {
            let (mut sym, mut spelling) = <(_, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => sym = StructSymId(self.r.idx_attr(&attr.value)?),
                b"spelling" => spelling = attr.unescape_value()?.to_string(),
                _ => {}
              }
            }
            let args = self.parse_terms()?;
            return Ok(Elem::Type(Box::new(Type::Struct { pos, sym, spelling, args })))
          }
          b"Clustered-Type" => Elem::Type(Box::new(Type::Cluster {
            pos: self.r.get_pos(&e)?,
            attrs: self.parse_attrs()?,
            ty: self.parse_type1()?,
          })),
          b"ReservedDscr-Type" if self.msm => {
            let mut group = Default::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              if attr.key.0 == b"nr" {
                group = ResGroupId(self.r.idx_attr(&attr.value)?)
              }
            }
            let subst = self.parse_substitution()?;
            return Ok(Elem::Type(Box::new(Type::Reservation { pos, group, subst })))
          }
          b"Negated-Formula" => {
            let pos = self.r.get_pos(&e)?;
            Elem::Formula(Box::new(Formula::Not { pos, f: self.parse_formula()? }))
          }
          b"Conjunctive-Formula" => {
            let (pos, f1, f2) = (self.r.get_pos(&e)?, self.parse_formula()?, self.parse_formula()?);
            Elem::Formula(Box::new(Formula::Binop { kind: FormulaBinop::And, pos, f1, f2 }))
          }
          b"Disjunctive-Formula" => {
            let (pos, f1, f2) = (self.r.get_pos(&e)?, self.parse_formula()?, self.parse_formula()?);
            Elem::Formula(Box::new(Formula::Binop { kind: FormulaBinop::Or, pos, f1, f2 }))
          }
          b"Conditional-Formula" => {
            let (pos, f1, f2) = (self.r.get_pos(&e)?, self.parse_formula()?, self.parse_formula()?);
            Elem::Formula(Box::new(Formula::Binop { kind: FormulaBinop::Imp, pos, f1, f2 }))
          }
          b"Biconditional-Formula" => {
            let (pos, f1, f2) = (self.r.get_pos(&e)?, self.parse_formula()?, self.parse_formula()?);
            Elem::Formula(Box::new(Formula::Binop { kind: FormulaBinop::Iff, pos, f1, f2 }))
          }
          b"FlexaryConjunctive-Formula" => {
            let (pos, f1, f2) = (self.r.get_pos(&e)?, self.parse_formula()?, self.parse_formula()?);
            Elem::Formula(Box::new(Formula::Binop { kind: FormulaBinop::FlexAnd, pos, f1, f2 }))
          }
          b"FlexaryDisjunctive-Formula" => {
            let (pos, f1, f2) = (self.r.get_pos(&e)?, self.parse_formula()?, self.parse_formula()?);
            Elem::Formula(Box::new(Formula::Binop { kind: FormulaBinop::FlexOr, pos, f1, f2 }))
          }
          b"Predicative-Formula" => {
            let (mut sym, mut spelling) = <(_, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => sym = PredSymId(self.r.idx_attr(&attr.value)?),
                b"spelling" => spelling = attr.unescape_value()?.to_string(),
                _ => {}
              }
            }
            self.r.read_start(&mut self.buf, Some("Arguments"))?;
            let mut args = self.parse_terms()?;
            let Ok(left) = args.len().try_into() else {
              return self.r.err("at most 255 arguments")
            };
            self.r.read_start(&mut self.buf, Some("Arguments"))?;
            while let Some(t) = self.parse_term()? {
              args.push(*t)
            }
            let pred = Box::new(Pred { pos, positive: true, sym, spelling, left, args });
            Elem::Formula(Box::new(Formula::Pred(pred)))
          }
          b"RightSideOf-Predicative-Formula" => {
            let (mut sym, mut spelling) = <(_, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => sym = PredSymId(self.r.idx_attr(&attr.value)?),
                b"spelling" => spelling = attr.unescape_value()?.to_string(),
                _ => {}
              }
            }
            self.r.read_start(&mut self.buf, Some("Arguments"))?;
            let right = self.parse_terms()?;
            Elem::PredRhs(Box::new(PredRhs { pos, positive: true, sym, spelling, right }))
          }
          b"Multi-Predicative-Formula" => {
            let pos = self.r.get_pos(&e)?;
            let first = match *self.parse_formula()? {
              Formula::Not { f, .. } => match *f {
                Formula::Pred(mut pred) => {
                  pred.positive = !pred.positive;
                  pred
                }
                _ => return self.r.err("predicate"),
              },
              Formula::Pred(pred) => pred,
              _ => return self.r.err("predicate"),
            };
            let mut rest = vec![];
            loop {
              match self.parse_elem()? {
                Elem::PredRhs(rhs) => rest.push(*rhs),
                Elem::End => break,
                _ => return self.r.err("<RightSideOf-Predicative-Formula>"),
              }
            }
            return Ok(Elem::Formula(Box::new(Formula::ChainPred { pos, first, rest })))
          }
          b"Private-Predicate-Formula" => {
            let (mut shape, mut var, mut spelling) = <(_, _, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                // b"idnr" => id = self.r.idx_attr(&attr.value)?,
                b"spelling" => spelling = attr.unescape_value()?,
                b"shape" => shape = self.r.get_attr(&attr.value)?,
                b"nr" => var = self.r.idx_attr(&attr.value)?,
                _ => {}
              }
            }
            let (spelling, args) = (spelling.into(), self.parse_terms()?);
            let kind = match shape {
              IdentKind::Free => None,
              IdentKind::PrivPred => Some(PrivPredKind::PrivPred(PrivPredId(var))),
              IdentKind::SchPred => Some(PrivPredKind::SchPred(SchPredId(var))),
              _ => return self.r.err("private predicate kind"),
            };
            return Ok(Elem::Formula(Box::new(Formula::PrivPred { pos, kind, spelling, args })))
          }
          b"Attributive-Formula" => Elem::Formula(Box::new(Formula::Attr {
            pos: self.r.get_pos(&e)?,
            positive: true,
            term: self.parse_term1()?,
            attrs: self.parse_attrs()?,
          })),
          b"Qualifying-Formula" => Elem::Formula(Box::new(Formula::Is {
            pos: self.r.get_pos(&e)?,
            positive: true,
            term: self.parse_term1()?,
            ty: self.parse_type1()?,
          })),
          b"Universal-Quantifier-Formula" => {
            let pos = self.r.get_pos(&e)?;
            let (vars, scope) = (vec![*self.parse_binder()?], self.parse_formula()?);
            let f = Formula::Binder { kind: FormulaBinder::ForAll, pos, vars, st: None, scope };
            Elem::Formula(Box::new(f))
          }
          b"Existential-Quantifier-Formula" => {
            let pos = self.r.get_pos(&e)?;
            let (vars, scope) = (vec![*self.parse_binder()?], self.parse_formula()?);
            let f = Formula::Binder { kind: FormulaBinder::Exists, pos, vars, st: None, scope };
            Elem::Formula(Box::new(f))
          }
          b"Thesis" => Elem::Formula(Box::new(Formula::Thesis { pos: self.r.get_pos(&e)? })),
          b"Contradiction" => Elem::Formula(Box::new(Formula::False { pos: self.r.get_pos(&e)? })),
          b"Predicate-Pattern" => {
            let (mut sym, mut spelling) = <(_, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => sym = PredSymId(self.r.idx_attr(&attr.value)?),
                b"spelling" => spelling = attr.unescape_value()?.to_string(),
                _ => {}
              }
            }
            let mut args = vec![];
            self.parse_loci(&mut args)?;
            let left = args.len() as u8;
            self.parse_loci(&mut args)?;
            let pat = PatternPred { pos, sym, spelling, left, args };
            Elem::Pattern(Pattern::Pred(Box::new(pat)))
          }
          b"Operation-Functor-Pattern" => {
            let (mut sym, mut spelling) = <(_, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => sym = FuncSymId(self.r.idx_attr(&attr.value)?),
                b"spelling" => spelling = attr.unescape_value()?.to_string(),
                _ => {}
              }
            }
            let mut args = vec![];
            self.parse_loci(&mut args)?;
            let left = args.len() as u8;
            self.parse_loci(&mut args)?;
            let pat = PatternFunc::Func { pos, sym, spelling, left, args };
            Elem::Pattern(Pattern::Func(Box::new(pat)))
          }
          b"Bracket-Functor-Pattern" => {
            let (mut lsym, mut lspelling) = <(_, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => lsym = LeftBrkSymId(self.r.idx_attr(&attr.value)?),
                b"spelling" => lspelling = attr.unescape_value()?.to_string(),
                _ => {}
              }
            }
            let ((rsym, rspelling), mut args) = (self.parse_right_pattern()?, vec![]);
            self.parse_loci(&mut args)?;
            let pat = PatternFunc::Bracket { pos, lsym, lspelling, rsym, rspelling, args };
            Elem::Pattern(Pattern::Func(Box::new(pat)))
          }
          b"Mode-Pattern" => {
            let (mut sym, mut spelling) = <(_, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => sym = ModeSymId(self.r.idx_attr(&attr.value)?),
                b"spelling" => spelling = attr.unescape_value()?.to_string(),
                _ => {}
              }
            }
            let mut args = vec![];
            self.parse_loci(&mut args)?;
            let pat = PatternMode { pos, sym, spelling, args };
            Elem::Pattern(Pattern::Mode(Box::new(pat)))
          }
          b"Attribute-Pattern" => {
            let (mut sym, mut spelling) = <(_, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => sym = AttrSymId(self.r.idx_attr(&attr.value)?),
                b"spelling" => spelling = attr.unescape_value()?.to_string(),
                _ => {}
              }
            }
            let arg = self.parse_locus1()?;
            let mut args = vec![];
            self.parse_loci(&mut args)?;
            args.push(*arg);
            let pat = PatternAttr { pos, sym, spelling, args };
            Elem::Pattern(Pattern::Attr(Box::new(pat)))
          }
          b"Selector" => {
            let (mut sym, mut spelling) = <(_, _)>::default();
            let pos = self.r.get_pos(&e)?;
            for attr in e.attributes() {
              let attr = attr?;
              match attr.key.0 {
                b"nr" => sym = SelSymId(self.r.idx_attr(&attr.value)?),
                b"spelling" => spelling = attr.unescape_value()?.to_string(),
                _ => {}
              }
            }
            Elem::Selector(Field { pos, sym, spelling: spelling.into() })
          }
          _ => Elem::Other,
        };
        self.r.end_tag(&mut self.buf)?;
        elem
      } else {
        Elem::End
      })
    })
  }
}
