#![warn(unused)]
use super::XmlReader;
use crate::ast::*;
use crate::types::{Position, PropertyKind, SchRef};
use crate::{types, MizPath};
use quick_xml::events::{BytesStart, Event};
use std::borrow::Cow;
use std::fs::File;
use std::io;

// Parser for WSM and MSM formats
pub struct MsmParser {
  r: XmlReader,
  buf: Vec<u8>,
  // true for MSM, false for WSM
  msm: bool,
}

impl MizPath {
  pub fn open_msx(&self) -> io::Result<MsmParser> { Ok(MsmParser::new(self.open("msx")?, true)) }

  pub fn open_wsx(&self) -> io::Result<MsmParser> { Ok(MsmParser::new(self.open("wsx")?, false)) }

  pub fn read_msx(&self) -> Vec<Item> { self.open_msx().unwrap().parse_items() }
}

impl TryFrom<&[u8]> for Shape {
  type Error = ();
  fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
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
  CS(CaseOrSupposeKind),
  Scheme,
}

#[derive(Debug)]
struct Block {
  kind: BlockKind,
  pos: (Position, Position),
  items: Vec<Item>,
}

impl ItemKind {
  fn corr_mut(&mut self) -> Option<(&mut Vec<CorrCond>, &mut Option<Correctness>)> {
    match self {
      ItemKind::Definition(it) => Some((&mut it.conds, &mut it.corr)),
      ItemKind::DefStruct(it) => Some((&mut it.conds, &mut it.corr)),
      ItemKind::Cluster(it) => Some((&mut it.conds, &mut it.corr)),
      ItemKind::Identify(it) => Some((&mut it.conds, &mut it.corr)),
      ItemKind::Reduction(it) => Some((&mut it.conds, &mut it.corr)),
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
  Inference(Position, InferenceKind, Vec<Reference>),
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
  Label(Box<Label>),
  Link(Position),
  Reference(Reference),
  DefCaseTerm(DefCase<Term>),
  DefCaseFormula(DefCase<Formula>),
  Selector(Field),
  Other,
  End,
}

impl XmlReader {
  fn parse_variable_attrs(&mut self, e: &BytesStart<'_>) -> Box<Variable> {
    let (mut pos, mut id, mut spelling) = <(Position, _, _)>::default();
    for attr in e.attributes().map(Result::unwrap) {
      match attr.key {
        b"line" => pos.line = self.get_attr(&attr.value),
        b"col" => pos.col = self.get_attr(&attr.value),
        b"idnr" => id = IdentId(self.get_attr(&attr.value)),
        b"spelling" => spelling = self.get_attr_unescaped(&attr.value),
        // TODO: origin, kind, serialnr, varnr
        _ => {}
      }
    }
    Box::new(Variable { pos, id: (id, spelling) })
  }
}
impl MsmParser {
  fn new(file: File, msm: bool) -> MsmParser {
    let mut buf = vec![];
    let mut r = XmlReader::new(file, &mut buf);
    assert!(matches!(r.read_event(&mut buf), Event::Start(e) if e.local_name() == b"Text-Proper"));
    MsmParser { r, buf, msm }
  }

  fn parse_variable(&mut self) -> Option<Box<Variable>> {
    match self.parse_elem() {
      Elem::Variable(v) => Some(v),
      Elem::End => None,
      _ => panic!("expected <Variable>"),
    }
  }

  fn parse_variables(&mut self) -> Vec<Variable> {
    self.r.read_start(&mut self.buf, Some(b"Variables"));
    std::iter::from_fn(|| self.parse_variable().map(|v| *v)).collect()
  }

  fn parse_substitution(&mut self) -> Vec<[u32; 3]> {
    std::iter::from_fn(|| {
      let e = self.r.try_read_start(&mut self.buf, Some(b"Substitution")).ok()?;
      let (mut x, mut y1, mut y2) = <_>::default();
      for attr in e.attributes().map(Result::unwrap) {
        match attr.key {
          b"x" => x = self.r.get_attr(&attr.value),
          b"y1" => y1 = self.r.get_attr(&attr.value),
          b"y2" => y2 = self.r.get_attr(&attr.value),
          _ => {}
        }
      }
      self.r.end_tag(&mut self.buf);
      Some([x, y1, y2])
    })
    .collect()
  }

  fn parse_formula(&mut self) -> Box<Formula> {
    match self.parse_elem() {
      Elem::Formula(f) => f,
      _ => panic!("expected formula"),
    }
  }

  fn parse_term(&mut self) -> Option<Box<Term>> {
    match self.parse_elem() {
      Elem::Term(t) => Some(t),
      Elem::End => None,
      _ => panic!("expected term"),
    }
  }

  fn parse_terms(&mut self) -> Vec<Term> {
    std::iter::from_fn(|| self.parse_term().map(|t| *t)).collect()
  }

  fn parse_type(&mut self) -> Option<Box<Type>> {
    match self.parse_elem() {
      Elem::Type(ty) => Some(ty),
      Elem::End => None,
      _ => panic!("expected type"),
    }
  }

  fn parse_types(&mut self) -> Vec<Type> {
    self.r.read_start(&mut self.buf, Some(b"Type-List"));
    std::iter::from_fn(|| self.parse_type().map(|t| *t)).collect()
  }

  fn parse_proposition(&mut self) -> Option<Box<Proposition>> {
    self.r.try_read_start(&mut self.buf, Some(b"Proposition")).ok()?;
    let (label, f) = match self.parse_elem() {
      Elem::Label(lab) => (Some(lab), self.parse_formula()),
      Elem::Formula(f) => (None, f),
      _ => panic!("expected formula"),
    };
    self.r.end_tag(&mut self.buf);
    Some(Box::new(Proposition { label, f: *f }))
  }

  fn parse_stmt(&mut self, shape: Shape) -> Statement {
    match shape {
      Shape::DiffuseStatement => {
        let (label, bl) = match self.parse_elem() {
          Elem::Label(lab) => (Some(lab), self.parse_block().unwrap()),
          Elem::Block(bl) => (None, bl),
          _ => panic!("expected block"),
        };
        self.r.end_tag(&mut self.buf);
        Statement::Now { end: bl.pos.1, label, items: bl.items }
      }
      Shape::CompactStatement => {
        let prop = self.parse_proposition().unwrap();
        let just = self.parse_justification();
        self.r.end_tag(&mut self.buf);
        Statement::Proposition { prop, just }
      }
      Shape::IterativeEquality => {
        let prop = self.parse_proposition().unwrap();
        let just = self.parse_justification();
        let mut steps = vec![];
        while let Ok(e) = self.r.try_read_start(&mut self.buf, Some(b"Iterative-Step")) {
          steps.push(IterStep {
            pos: self.r.get_pos(&e),
            rhs: *self.parse_term().unwrap(),
            just: *self.parse_justification(),
          });
          self.r.end_tag(&mut self.buf);
        }
        Statement::IterEquality { prop, just, steps }
      }
    }
  }

  fn parse_justification(&mut self) -> Box<Justification> {
    Box::new(match self.parse_elem() {
      Elem::Block(bl) if matches!(bl.kind, BlockKind::Proof) =>
        Justification::Block { pos: bl.pos, items: bl.items },
      Elem::Inference(pos, kind, refs) => Justification::Inference { pos, kind, refs },
      _ => panic!("expected justification"),
    })
  }

  fn parse_block(&mut self) -> Option<Box<Block>> {
    match self.parse_elem() {
      Elem::Block(bl) => Some(bl),
      Elem::End => None,
      _ => panic!("expected <Block>"),
    }
  }

  fn parse_binder(&mut self) -> Box<BinderGroup> {
    match self.parse_elem() {
      Elem::Binder(var) => var,
      _ => panic!("expected binder group"),
    }
  }

  fn parse_pattern(&mut self) -> Pattern {
    match self.parse_elem() {
      Elem::Pattern(pat) => pat,
      _ => panic!("expected pattern"),
    }
  }

  fn parse_pattern_redef(&mut self, kind: PatternRedefKind) -> ItemKind {
    ItemKind::PatternRedef { kind, orig: self.parse_pattern(), new: self.parse_pattern() }
  }

  fn parse_adjective(&mut self) -> Option<Adjective> {
    let e = self.r.try_read_start(&mut self.buf, None).ok()?;
    Some(match e.local_name() {
      b"Adjective" => {
        let (mut pos, mut sym, mut spelling) = <(Position, _, _)>::default();
        for attr in e.attributes().map(Result::unwrap) {
          match attr.key {
            b"line" => pos.line = self.r.get_attr(&attr.value),
            b"col" => pos.col = self.r.get_attr(&attr.value),
            b"nr" => sym = self.r.get_attr(&attr.value),
            b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
            _ => {}
          }
        }
        let args = self.parse_terms();
        Adjective::Attr { pos, sym: (sym, spelling), args }
      }
      b"NegatedAdjective" => {
        let attr = Adjective::Non {
          pos: self.r.get_pos(&e),
          attr: Box::new(self.parse_adjective().unwrap()),
        };
        self.r.end_tag(&mut self.buf);
        attr
      }
      _ => panic!("expected an adjective"),
    })
  }

  fn parse_adjectives(&mut self) -> Vec<Adjective> {
    self.r.read_start(&mut self.buf, Some(b"Adjective-Cluster"));
    std::iter::from_fn(|| self.parse_adjective()).collect()
  }

  fn parse_definiens(&mut self) -> Option<Box<Definiens>> {
    match self.parse_elem() {
      Elem::Definiens(d) => Some(d),
      Elem::End => None,
      _ => panic!("expected <Definiens>"),
    }
  }

  fn parse_locus(&mut self) -> Option<Box<Variable>> {
    let e = self.r.try_read_start(&mut self.buf, Some(b"Locus")).ok()?;
    let v = self.r.parse_variable_attrs(&e);
    self.r.end_tag(&mut self.buf);
    Some(v)
  }

  fn parse_loci(&mut self) -> Vec<Variable> {
    self.r.read_start(&mut self.buf, Some(b"Loci"));
    std::iter::from_fn(|| self.parse_locus().map(|v| *v)).collect()
  }

  fn parse_right_pattern(&mut self) -> (u32, String) {
    let (mut rsym, mut rsp) = Default::default();
    let e = self.r.read_start(&mut self.buf, Some(b"Right-Circumflex-Symbol"));
    for attr in e.attributes().map(Result::unwrap) {
      match attr.key {
        b"nr" => rsym = self.r.get_attr(&attr.value),
        b"spelling" => rsp = self.r.get_attr_unescaped(&attr.value),
        _ => {}
      }
    }
    self.r.end_tag(&mut self.buf);
    (rsym, rsp)
  }

  fn parse_assumption(&mut self) -> Assumption {
    let e = self.r.read_start(&mut self.buf, None);
    let pos = self.r.get_pos(&e);
    let out = match e.local_name() {
      b"Single-Assumption" => Assumption::Single { pos, prop: self.parse_proposition().unwrap() },
      b"Collective-Assumption" => {
        let Elem::Conditions(conds) = self.parse_elem() else { panic!("expected <Conditions>") };
        Assumption::Collective { pos, conds }
      }
      _ => panic!("expected assumption"),
    };
    self.r.end_tag(&mut self.buf);
    out
  }

  fn push_parse_item(&mut self, items: &mut Vec<Item>) -> bool {
    let Ok(e) = self.r.try_read_start(&mut self.buf, Some(b"Item")) else { return false };
    let (mut pos, (mut kind, mut property, mut shape, mut spelling, mut condition)) =
      <(Position, _)>::default();
    for attr in e.attributes().map(Result::unwrap) {
      match attr.key {
        b"line" => pos.line = self.r.get_attr(&attr.value),
        b"col" => pos.col = self.r.get_attr(&attr.value),
        b"kind" => kind = attr.value,
        b"property" => property = Some((*attr.value).try_into().unwrap()),
        b"shape" => shape = attr.value,
        b"spelling" => spelling = Some(self.r.get_attr_unescaped(&attr.value)),
        b"condition" => condition = attr.value,
        // Some((*attr.value).try_into().unwrap()),
        _ => {}
      }
    }
    let mut end_tag = false;
    let kind = match &*kind {
      b"Definition-Item" => {
        let Block { pos, kind: BlockKind::Def(kind), items } = *self.parse_block().unwrap()
        else { panic!("expected a definition block") };
        ItemKind::Block { end: pos.1, kind, items }
      }
      b"Scheme-Block-Item" => {
        let Block { pos, kind: BlockKind::Scheme, mut items } = *self.parse_block().unwrap()
        else { panic!("expected a scheme block") };
        let ItemKind::SchemeHead(head) = items.remove(0).kind else { panic!() };
        ItemKind::SchemeBlock(Box::new(SchemeBlock { end: pos.1, head: *head, items }))
      }
      b"Scheme-Head" => {
        let e = self.r.read_start(&mut self.buf, Some(b"Scheme"));
        let (mut sym, mut spelling, mut nr) = <_>::default();
        for attr in e.attributes().map(Result::unwrap) {
          match attr.key {
            b"nr" => nr = self.r.get_attr(&attr.value),
            b"idnr" => sym = self.r.get_attr(&attr.value),
            b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
            _ => {}
          }
        }
        self.r.end_tag(&mut self.buf);
        self.r.read_start(&mut self.buf, Some(b"Schematic-Variables"));
        let mut groups = vec![];
        while let Event::Start(e) = self.r.read_event(&mut self.buf) {
          let pos = self.r.get_pos(&e);
          match e.local_name() {
            b"Predicate-Segment" => groups.push(SchemeBinderGroup::Pred {
              pos,
              vars: self.parse_variables(),
              tys: self.parse_types(),
            }),
            b"Functor-Segment" => groups.push(SchemeBinderGroup::Func {
              pos,
              vars: self.parse_variables(),
              tys: self.parse_types(),
              ret: match self.parse_elem() {
                Elem::TypeSpecification(ty) => *ty,
                _ => panic!("expected <Type-Specification>"),
              },
            }),
            _ => panic!("unexpected scheme variable group"),
          }
          self.r.end_tag(&mut self.buf);
        }
        let concl = *self.parse_formula();
        let mut prems = vec![];
        if self.r.try_read_start(&mut self.buf, Some(b"Provisional-Formulas")).is_ok() {
          prems.extend(std::iter::from_fn(|| self.parse_proposition().map(|p| *p)))
        } else {
          end_tag = true;
        }
        let body = SchemeHead { sym: (sym, spelling), nr, groups, concl, prems };
        ItemKind::SchemeHead(Box::new(body))
      }
      b"Theorem-Item" => ItemKind::Theorem {
        prop: self.parse_proposition().unwrap(),
        just: self.parse_justification(),
      },
      b"Reservation" => {
        let vars = self.parse_variables();
        let tys = if self.msm { Some(self.parse_types()) } else { None };
        let ty = self.parse_type().unwrap();
        let fvars = if self.msm {
          let mut out: Vec<u32> = vec![];
          while let Ok(e) = self.r.try_read_start(&mut self.buf, Some(b"SetMember")) {
            out.push(self.r.get_attr(&e.try_get_attribute(b"x").unwrap().unwrap().value));
            self.r.end_tag(&mut self.buf);
          }
          end_tag = true;
          Some(out)
        } else {
          None
        };
        ItemKind::Reservation(Box::new(Reservation { vars, tys, ty, fvars }))
      }
      b"Section-Pragma" => ItemKind::Section,
      b"Choice-Statement" => {
        let mut vars = vec![];
        let conds = loop {
          match self.parse_elem() {
            Elem::Binder(var) => vars.push(*var),
            Elem::Conditions(conds) => break conds,
            _ => panic!("expected <Conditions>"),
          }
        };
        ItemKind::Consider { vars, conds, just: self.parse_justification() }
      }
      b"Type-Changing-Statement" => {
        let mut vars = vec![];
        let ty = loop {
          match self.parse_elem() {
            Elem::Variable(var) => vars.push(ReconsiderVar::Var(*var)),
            Elem::Equality(var, tm) => vars.push(ReconsiderVar::Equality { var: *var, tm: *tm }),
            Elem::Type(ty) => break ty,
            _ => panic!("expected variable, equality, or type"),
          }
        };
        ItemKind::Reconsider { vars, ty, just: self.parse_justification() }
      }
      b"Private-Functor-Definition" => ItemKind::DefFunc {
        var: self.parse_variable().unwrap(),
        tys: self.parse_types(),
        value: self.parse_term().unwrap(),
      },
      b"Private-Predicate-Definition" => ItemKind::DefPred {
        var: self.parse_variable().unwrap(),
        tys: self.parse_types(),
        value: self.parse_formula(),
      },
      b"Constant-Definition" =>
        ItemKind::Set { var: self.parse_variable().unwrap(), value: self.parse_term().unwrap() },
      b"Generalization" => ItemKind::Let { var: self.parse_binder() },
      b"Loci-Declaration" => ItemKind::LetLocus { var: self.parse_binder() },
      b"Existential-Assumption" => {
        let mut vars = vec![];
        let conds = loop {
          match self.parse_elem() {
            Elem::Binder(var) => vars.push(*var),
            Elem::Conditions(conds) => break conds,
            _ => panic!("expected <Conditions>"),
          }
        };
        ItemKind::Given { vars, conds }
      }
      b"Exemplification" => {
        let (mut var, mut term) = (None, None);
        loop {
          match self.parse_elem() {
            Elem::Variable(v) => var = Some(v),
            Elem::Term(t) => term = Some(t),
            Elem::End => break,
            _ => panic!("unexpected element"),
          }
        }
        end_tag = true;
        ItemKind::Take { var, term }
      }
      b"Per-Cases" => ItemKind::PerCases { just: self.parse_justification() },
      b"Regular-Statement" => {
        let shape = (*shape).try_into().unwrap();
        end_tag = true;
        ItemKind::Statement(self.parse_stmt(shape))
      }
      b"Conclusion" => {
        let shape = (*shape).try_into().unwrap();
        end_tag = true;
        ItemKind::Thus(self.parse_stmt(shape))
      }
      b"Case-Block" => {
        let mut bl = self.parse_block().unwrap();
        let BlockKind::CS(kind) = bl.kind else { panic!("expected case or suppose block") };
        let hyp = Box::new(match (&kind, bl.items.remove(0).kind) {
          (CaseOrSupposeKind::Case, ItemKind::CaseHead(hyp))
          | (CaseOrSupposeKind::Suppose, ItemKind::SupposeHead(hyp)) => hyp,
          _ => panic!("missing case/suppose head"),
        });
        ItemKind::CaseOrSuppose { end: bl.pos.1, kind, hyp, items: bl.items }
      }
      b"Case-Head" => ItemKind::CaseHead(self.parse_assumption()),
      b"Suppose-Head" => ItemKind::SupposeHead(self.parse_assumption()),
      b"Assumption" => ItemKind::Assumption(self.parse_assumption()),
      b"Correctness-Condition" => {
        let kind = (*condition).try_into().unwrap();
        let corr = items.last_mut().and_then(|it| it.kind.corr_mut()).unwrap().0;
        corr.push(CorrCond { pos, kind, just: *self.parse_justification() });
        self.r.end_tag(&mut self.buf);
        return true
      }
      b"Correctness" => {
        self.r.read_start(&mut self.buf, Some(b"CorrectnessConditions"));
        let mut conds = vec![];
        while let Ok(e) = self.r.try_read_start(&mut self.buf, Some(b"Correctness")) {
          conds
            .push((*e.try_get_attribute(b"condition").unwrap().unwrap().value).try_into().unwrap());
          self.r.end_tag(&mut self.buf);
        }
        let corr = items.last_mut().and_then(|it| it.kind.corr_mut()).unwrap().1;
        assert!(corr.is_none());
        *corr = Some(Correctness { pos, conds, just: *self.parse_justification() });
        self.r.end_tag(&mut self.buf);
        return true
      }
      b"Property" =>
        ItemKind::Property { prop: property.unwrap(), just: self.parse_justification() },
      b"Mode-Definition" => {
        let (redef, pat) = match self.parse_elem() {
          Elem::Redefine => (true, self.parse_pattern()),
          Elem::Pattern(pat) => (false, pat),
          _ => panic!("expected pattern"),
        };
        let Pattern::Mode(pat) = pat else { panic!("expected a mode pattern") };
        let e = self.r.read_start(&mut self.buf, None);
        let kind = match e.local_name() {
          b"Expandable-Mode" => DefModeKind::Expandable { expansion: self.parse_type().unwrap() },
          b"Standard-Mode" => {
            let (spec, def) = match self.parse_elem() {
              Elem::TypeSpecification(ty) => (Some(ty), self.parse_definiens()),
              Elem::Definiens(d) => (None, Some(d)),
              Elem::End => (None, None),
              _ => panic!("expected <Definiens>"),
            };
            end_tag = def.is_none();
            DefModeKind::Standard { spec, def }
          }
          _ => panic!("unknown def mode kind"),
        };
        self.r.end_tag(&mut self.buf);
        let kind = DefinitionKind::Mode { pat, kind };
        ItemKind::Definition(Box::new(Definition { redef, kind, conds: vec![], corr: None }))
      }
      b"Attribute-Definition" => {
        let (redef, pat) = match self.parse_elem() {
          Elem::Redefine => (true, self.parse_pattern()),
          Elem::Pattern(pat) => (false, pat),
          _ => panic!("expected pattern"),
        };
        let Pattern::Attr(pat) = pat else { panic!("expected an attribute pattern") };
        let def = self.parse_definiens();
        end_tag = def.is_none();
        let kind = DefinitionKind::Attr { pat, def };
        ItemKind::Definition(Box::new(Definition { redef, kind, conds: vec![], corr: None }))
      }
      b"Predicate-Definition" => {
        let (redef, pat) = match self.parse_elem() {
          Elem::Redefine => (true, self.parse_pattern()),
          Elem::Pattern(pat) => (false, pat),
          _ => panic!("expected pattern"),
        };
        let Pattern::Pred(pat) = pat else { panic!("expected a predicate pattern") };
        let def = self.parse_definiens();
        end_tag = def.is_none();
        let kind = DefinitionKind::Pred { pat, def };
        ItemKind::Definition(Box::new(Definition { redef, kind, conds: vec![], corr: None }))
      }
      b"Functor-Definition" => {
        let shape = match &*shape {
          b"No-Definiens" => None,
          b"Means" => Some(false),
          b"Equals" => Some(true),
          _ => panic!("unexpected functor shape attribute"),
        };
        let (redef, pat) = match self.parse_elem() {
          Elem::Redefine => (true, self.parse_pattern()),
          Elem::Pattern(pat) => (false, pat),
          _ => panic!("expected pattern"),
        };
        let Pattern::Func(pat) = pat else { panic!("expected a functor pattern") };
        let (spec, def) = match self.parse_elem() {
          Elem::TypeSpecification(ty) => (Some(ty), self.parse_definiens()),
          Elem::Definiens(d) => (None, Some(d)),
          Elem::End => (None, None),
          _ => panic!("expected <Definiens>"),
        };
        end_tag = def.is_none();
        let kind = match (shape, def) {
          (None, None) => DefFuncKind::None,
          (Some(false), Some(def)) => DefFuncKind::Means(def),
          (Some(true), Some(def)) => DefFuncKind::Equals(def),
          _ => panic!("unexpected or missing <Definiens>"),
        };
        let kind = DefinitionKind::Func { pat, spec, kind };
        ItemKind::Definition(Box::new(Definition { redef, kind, conds: vec![], corr: None }))
      }
      b"Structure-Definition" => {
        self.r.read_start(&mut self.buf, Some(b"Ancestors"));
        let parents = std::iter::from_fn(|| self.parse_type().map(|t| *t)).collect();
        let e = self.r.read_start(&mut self.buf, Some(b"Structure-Pattern"));
        let (mut sym, mut spelling) = <_>::default();
        for attr in e.attributes().map(Result::unwrap) {
          match attr.key {
            b"nr" => sym = self.r.get_attr(&attr.value),
            b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
            _ => {}
          }
        }
        let args = self.parse_loci();
        let mut groups = vec![];
        while let Ok(e) = self.r.try_read_start(&mut self.buf, Some(b"Field-Segment")) {
          let pos = self.r.get_pos(&e);
          let mut fields = vec![];
          let ty = loop {
            match self.parse_elem() {
              Elem::Selector(field) => fields.push(field),
              Elem::Type(ty) => break ty,
              _ => panic!("expected type"),
            }
          };
          self.r.end_tag(&mut self.buf);
          groups.push(FieldGroup { pos, fields, ty: *ty })
        }
        let pat = PatternStruct { sym: (sym, spelling), args, groups };
        ItemKind::DefStruct(Box::new(DefStruct { parents, pat, conds: vec![], corr: None }))
      }
      b"Pred-Synonym" => self.parse_pattern_redef(PatternRedefKind::PredSynonym { pos: true }),
      b"Pred-Antonym" => self.parse_pattern_redef(PatternRedefKind::PredSynonym { pos: false }),
      b"Func-Synonym" => self.parse_pattern_redef(PatternRedefKind::FuncNotation),
      b"Mode-Synonym" => self.parse_pattern_redef(PatternRedefKind::ModeNotation),
      b"Attr-Synonym" => self.parse_pattern_redef(PatternRedefKind::AttrSynonym { pos: true }),
      b"Attr-Antonym" => self.parse_pattern_redef(PatternRedefKind::AttrSynonym { pos: false }),
      b"Cluster" => {
        let e = self.r.read_start(&mut self.buf, None);
        let kind = match e.local_name() {
          b"Existential-Registration" => ClusterDeclKind::Exist {
            concl: self.parse_adjectives(),
            ty: self.parse_type().unwrap(),
          },
          b"Conditional-Registration" => ClusterDeclKind::Cond {
            antecedent: self.parse_adjectives(),
            concl: self.parse_adjectives(),
            ty: self.parse_type().unwrap(),
          },
          b"Functorial-Registration" => {
            let term = self.parse_term().unwrap();
            let concl = self.parse_adjectives();
            let ty = self.parse_type();
            end_tag = ty.is_none();
            ClusterDeclKind::Func { term, concl, ty }
          }
          _ => panic!("unexpected cluster registration kind"),
        };
        self.r.end_tag(&mut self.buf);
        ItemKind::Cluster(Box::new(Cluster { kind, conds: vec![], corr: None }))
      }
      b"Identify" => {
        let orig = self.parse_pattern();
        let new = self.parse_pattern();
        let mut eqs = vec![];
        loop {
          match self.parse_elem() {
            Elem::LociEquality(x1, x2) => eqs.push((*x1, *x2)),
            Elem::End => break,
            _ => panic!("expected <LociEquality>"),
          }
        }
        end_tag = true;
        ItemKind::Identify(Box::new(Identify { orig, new, eqs, conds: vec![], corr: None }))
      }
      b"Property-Registration" => {
        assert!(matches!(property.unwrap(), PropertyKind::Sethood));
        ItemKind::SethoodRegistration {
          ty: self.parse_type().unwrap(),
          just: self.parse_justification(),
        }
      }
      b"Reduction" => ItemKind::Reduction(Box::new(Reduction {
        orig: *self.parse_term().unwrap(),
        new: *self.parse_term().unwrap(),
        conds: vec![],
        corr: None,
      })),
      b"Pragma" => ItemKind::Pragma { spelling: spelling.unwrap() },
      _ => panic!("unrecognized item kind"),
    };
    if !end_tag {
      self.r.end_tag(&mut self.buf);
    }
    items.push(Item { pos, kind });
    true
  }

  pub fn parse_items(&mut self) -> Vec<Item> {
    let mut items = vec![];
    while self.push_parse_item(&mut items) {}
    items
  }

  fn parse_elem(&mut self) -> Elem {
    // Note: this is only really an issue in debug mode, but this function
    // is both recursive and has a pretty big stack frame, so it is liable to run out
    // of stack space on some of the deep `p1 & p2 & ... & pn` expressions in some MML articles.
    // We use the stacker library here to allocate space on the heap to avoid stack overflow.
    stacker::maybe_grow(0x20000, 0x100000, || {
      if let Event::Start(e) = self.r.read_event(&mut self.buf) {
        let elem = match e.local_name() {
          b"Block" => {
            let (mut start, mut end, mut kind) = <(Position, Position, Cow<'_, [u8]>)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => start.line = self.r.get_attr(&attr.value),
                b"col" => start.col = self.r.get_attr(&attr.value),
                b"posline" => end.line = self.r.get_attr(&attr.value),
                b"poscol" => end.col = self.r.get_attr(&attr.value),
                b"kind" => kind = attr.value,
                _ => {}
              }
            }
            return Elem::Block(Box::new(Block {
              kind: match &*kind {
                b"Now-Reasoning" => BlockKind::Now,
                b"Hereby-Reasoning" => BlockKind::Hereby,
                b"Proof" => BlockKind::Proof,
                b"Definitional-Block" => BlockKind::Def(types::BlockKind::Definition),
                b"Notation-Block" => BlockKind::Def(types::BlockKind::Notation),
                b"Registration-Block" => BlockKind::Def(types::BlockKind::Registration),
                b"Case" => BlockKind::CS(CaseOrSupposeKind::Case),
                b"Suppose" => BlockKind::CS(CaseOrSupposeKind::Suppose),
                b"Scheme-Block" => BlockKind::Scheme,
                kind => panic!("unrecognized block kind: {}", std::str::from_utf8(kind).unwrap()),
              },
              pos: (start, end),
              items: self.parse_items(),
            }))
          }
          b"Straightforward-Justification" => {
            let pos = self.r.get_pos(&e);
            let (mut link, mut refs) = (None, vec![]);
            loop {
              match self.parse_elem() {
                Elem::Link(pos) => link = Some(pos),
                Elem::Reference(r) => refs.push(r),
                Elem::End => break,
                _ => panic!("unexpected element"),
              }
            }
            return Elem::Inference(pos, InferenceKind::By { link }, refs)
          }
          b"Scheme-Justification" => {
            let (mut pos, mut sch) = <(Position, SchRef)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"idnr" => sch.0 = self.r.get_attr(&attr.value),
                b"nr" => sch.1 = self.r.get_attr(&attr.value),
                _ => {}
              }
            }
            let mut refs = vec![];
            loop {
              match self.parse_elem() {
                Elem::Reference(r) => refs.push(r),
                Elem::End => break,
                _ => panic!("unexpected element"),
              }
            }
            return Elem::Inference(pos, InferenceKind::From { sch }, refs)
          }
          b"Implicitly-Qualified-Segment" =>
            return Elem::Binder(Box::new(BinderGroup {
              vars: vec![*self.parse_variable().unwrap()],
              ty: None,
              subst: if self.msm {
                self.parse_substitution()
              } else {
                self.r.end_tag(&mut self.buf);
                vec![]
              },
            })),
          b"Explicitly-Qualified-Segment" => Elem::Binder(Box::new(BinderGroup {
            vars: self.parse_variables(),
            ty: Some(self.parse_type().unwrap()),
            subst: vec![],
          })),
          b"Conditions" =>
            return Elem::Conditions(
              std::iter::from_fn(|| self.parse_proposition().map(|p| *p)).collect(),
            ),
          b"Variable" => Elem::Variable(self.r.parse_variable_attrs(&e)),
          b"Equality" => Elem::Equality(self.parse_variable().unwrap(), self.parse_term().unwrap()),
          b"Redefine" => Elem::Redefine,
          b"Type-Specification" => Elem::TypeSpecification(self.parse_type().unwrap()),
          b"Definiens" => {
            let ((mut pos, mut kind), mut is_term) = (<(Position, _)>::default(), false);
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"kind" => kind = attr.value,
                b"shape" =>
                  is_term = match &*attr.value {
                    b"Term-Expression" => true,
                    b"Formula-Expression" => false,
                    _ => panic!("unexpected definiens shape"),
                  },
                _ => {}
              }
            }
            let (label, end_tag, kind) = match &*kind {
              b"Simple-Definiens" if is_term => {
                let (lab, t) = match self.parse_elem() {
                  Elem::Label(lab) => (Some(lab), self.parse_term().unwrap()),
                  Elem::Term(t) => (None, t),
                  _ => panic!("expected term"),
                };
                (lab, false, DefValue::Term(DefBody { cases: vec![], otherwise: Some(t) }))
              }
              b"Simple-Definiens" => {
                let (lab, f) = match self.parse_elem() {
                  Elem::Label(lab) => (Some(lab), self.parse_formula()),
                  Elem::Formula(f) => (None, f),
                  _ => panic!("expected formula"),
                };
                (lab, false, DefValue::Formula(DefBody { cases: vec![], otherwise: Some(f) }))
              }
              b"Conditional-Definiens" if is_term => {
                let (mut lab, mut cases) = (None, vec![]);
                let otherwise = loop {
                  match self.parse_elem() {
                    Elem::Label(l) => lab = Some(l),
                    Elem::DefCaseTerm(case) => cases.push(case),
                    Elem::End => break None,
                    Elem::Term(t) => break Some(t),
                    _ => panic!("unexpected element"),
                  }
                };
                (lab, otherwise.is_none(), DefValue::Term(DefBody { cases, otherwise }))
              }
              b"Conditional-Definiens" => {
                let (mut lab, mut cases) = (None, vec![]);
                let otherwise = loop {
                  match self.parse_elem() {
                    Elem::Label(l) => lab = Some(l),
                    Elem::DefCaseFormula(case) => cases.push(case),
                    Elem::End => break None,
                    Elem::Formula(t) => break Some(t),
                    _ => panic!("unexpected element"),
                  }
                };
                (lab, otherwise.is_none(), DefValue::Formula(DefBody { cases, otherwise }))
              }
              _ => panic!("unknown definiens kind"),
            };
            if !end_tag {
              self.r.end_tag(&mut self.buf);
            }
            return Elem::Definiens(Box::new(Definiens { pos, label, kind }))
          }
          b"LociEquality" =>
            Elem::LociEquality(self.parse_locus().unwrap(), self.parse_locus().unwrap()),
          b"Label" => {
            let (mut pos, (mut id, mut spelling)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"idnr" => id = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            Elem::Label(Box::new(Label { pos, id: (id, spelling) }))
          }
          b"Link" => Elem::Link(self.r.get_pos(&e)),
          b"Local-Reference" => {
            let pos = self.r.get_pos(&e);
            let lab = self.r.get_attr(&e.try_get_attribute(b"idnr").unwrap().unwrap().value);
            Elem::Reference(Reference::Local { pos, lab })
          }
          b"Theorem-Reference" => {
            let (mut pos, (mut article_nr, mut thm_nr)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => article_nr = self.r.get_attr(&attr.value),
                // b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                b"number" => thm_nr = self.r.get_attr(&attr.value),
                _ => {}
              }
            }
            Elem::Reference(Reference::Thm { pos, article_nr, thm_nr })
          }
          b"Definition-Reference" => {
            let (mut pos, (mut article_nr, mut def_nr)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => article_nr = self.r.get_attr(&attr.value),
                // b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                b"number" => def_nr = self.r.get_attr(&attr.value),
                _ => {}
              }
            }
            Elem::Reference(Reference::Def { pos, article_nr, def_nr })
          }
          b"Partial-Definiens" => match self.parse_elem() {
            Elem::Term(case) => Elem::DefCaseTerm(DefCase { case, guard: self.parse_formula() }),
            Elem::Formula(case) =>
              Elem::DefCaseFormula(DefCase { case, guard: self.parse_formula() }),
            _ => panic!("expected term or formula"),
          },
          b"Placeholder-Term" => {
            let (mut pos, mut nr) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => nr = self.r.get_attr(&attr.value),
                _ => {}
              }
            }
            Elem::Term(Box::new(Term::Placeholder { pos, nr }))
          }
          b"Numeral-Term" => {
            let (mut pos, mut value) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"number" => value = self.r.get_attr(&attr.value),
                _ => {}
              }
            }
            Elem::Term(Box::new(Term::Numeral { pos, value }))
          }
          b"Simple-Term" => {
            let (mut pos, (mut sym, mut spelling)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"idnr" => sym = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            Elem::Term(Box::new(Term::Simple { pos, sym: (sym, spelling) }))
          }
          b"Private-Functor-Term" => {
            let (mut pos, (mut nr, mut spelling)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"idnr" => nr = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            return Elem::Term(Box::new(Term::PrivFunc {
              pos,
              sym: (nr, spelling),
              args: self.parse_terms(),
            }))
          }
          b"Infix-Term" => {
            let (mut pos, (mut sym, mut spelling)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => sym = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            self.r.read_start(&mut self.buf, Some(b"Arguments"));
            let left = self.parse_terms();
            self.r.read_start(&mut self.buf, Some(b"Arguments"));
            let right = self.parse_terms();
            Elem::Term(Box::new(Term::Infix { pos, sym: (sym, spelling), left, right }))
          }
          b"Circumfix-Term" => {
            let (mut pos, (mut lsym, mut lsp)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => lsym = self.r.get_attr(&attr.value),
                b"spelling" => lsp = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            let (rsym, args) = (self.parse_right_pattern(), self.parse_terms());
            return Elem::Term(Box::new(Term::Bracket { pos, lsym: (lsym, lsp), rsym, args }))
          }
          b"Aggregate-Term" => {
            let (mut pos, (mut sym, mut spelling)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => sym = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            let args = self.parse_terms();
            return Elem::Term(Box::new(Term::Aggregate { pos, sym: (sym, spelling), args }))
          }
          b"Forgetful-Functor-Term" => {
            let (mut pos, (mut sym, mut spelling)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => sym = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            let arg = self.parse_term().unwrap();
            Elem::Term(Box::new(Term::ForgetFunc { pos, sym: (sym, spelling), arg }))
          }
          b"Selector-Term" => {
            let (mut pos, (mut sym, mut spelling)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => sym = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            let arg = self.parse_term().unwrap();
            Elem::Term(Box::new(Term::Selector { pos, sym: (sym, spelling), arg }))
          }
          b"Internal-Selector-Term" => {
            let (mut pos, (mut sym, mut spelling)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => sym = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            Elem::Term(Box::new(Term::InternalSelector { pos, sym: (sym, spelling) }))
          }
          b"Qualification-Term" => {
            let pos = self.r.get_pos(&e);
            let term = self.parse_term().unwrap();
            let ty = self.parse_type().unwrap();
            Elem::Term(Box::new(Term::Qua { pos, term, ty }))
          }
          b"Global-Choice-Term" => {
            let pos = self.r.get_pos(&e);
            let ty = self.parse_type().unwrap();
            Elem::Term(Box::new(Term::The { pos, ty }))
          }
          b"Simple-Fraenkel-Term" => {
            let pos = self.r.get_pos(&e);
            let mut vars = vec![];
            let scope = loop {
              match self.parse_elem() {
                Elem::Binder(var) => vars.push(*var),
                Elem::Term(t) => break t,
                _ => panic!("expected <Conditions>"),
              }
            };
            Elem::Term(Box::new(Term::Fraenkel { pos, vars, scope, compr: None }))
          }
          b"Fraenkel-Term" => {
            let pos = self.r.get_pos(&e);
            let mut vars = vec![];
            let scope = loop {
              match self.parse_elem() {
                Elem::Binder(var) => vars.push(*var),
                Elem::Term(t) => break t,
                _ => panic!("expected <Conditions>"),
              }
            };
            let compr = Some(self.parse_formula());
            Elem::Term(Box::new(Term::Fraenkel { pos, vars, scope, compr }))
          }
          b"it-Term" => {
            let pos = self.r.get_pos(&e);
            Elem::Term(Box::new(Term::It { pos }))
          }
          b"Standard-Type" => {
            let (mut pos, (mut sym, mut spelling)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => sym = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            let args = self.parse_terms();
            return Elem::Type(Box::new(Type::Standard { pos, sym: (sym, spelling), args }))
          }
          b"Struct-Type" => {
            let (mut pos, (mut sym, mut spelling)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => sym = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            let args = self.parse_terms();
            return Elem::Type(Box::new(Type::Struct { pos, sym: (sym, spelling), args }))
          }
          b"Clustered-Type" => Elem::Type(Box::new(Type::Cluster {
            pos: self.r.get_pos(&e),
            attrs: self.parse_adjectives(),
            ty: self.parse_type().unwrap(),
          })),
          b"ReservedDscr-Type" if self.msm => {
            let (mut pos, (mut sym, mut spelling, mut nr)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => nr = self.r.get_attr(&attr.value),
                b"idnr" => sym = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            let subst = self.parse_substitution();
            return Elem::Type(Box::new(Type::Reservation { pos, sym: (sym, spelling), nr, subst }))
          }
          b"Negated-Formula" => {
            let pos = self.r.get_pos(&e);
            Elem::Formula(Box::new(Formula::Not { pos, f: self.parse_formula() }))
          }
          b"Conjunctive-Formula" => {
            let pos = self.r.get_pos(&e);
            let f = [self.parse_formula(), self.parse_formula()];
            Elem::Formula(Box::new(Formula::Binop { kind: FormulaBinop::And, pos, f }))
          }
          b"Disjunctive-Formula" => {
            let pos = self.r.get_pos(&e);
            let f = [self.parse_formula(), self.parse_formula()];
            Elem::Formula(Box::new(Formula::Binop { kind: FormulaBinop::Or, pos, f }))
          }
          b"Conditional-Formula" => {
            let pos = self.r.get_pos(&e);
            let f = [self.parse_formula(), self.parse_formula()];
            Elem::Formula(Box::new(Formula::Binop { kind: FormulaBinop::Imp, pos, f }))
          }
          b"Biconditional-Formula" => {
            let pos = self.r.get_pos(&e);
            let f = [self.parse_formula(), self.parse_formula()];
            Elem::Formula(Box::new(Formula::Binop { kind: FormulaBinop::Iff, pos, f }))
          }
          b"FlexaryConjunctive-Formula" => {
            let pos = self.r.get_pos(&e);
            let f = [self.parse_formula(), self.parse_formula()];
            Elem::Formula(Box::new(Formula::Binop { kind: FormulaBinop::FlexAnd, pos, f }))
          }
          b"FlexaryDisjunctive-Formula" => {
            let pos = self.r.get_pos(&e);
            let f = [self.parse_formula(), self.parse_formula()];
            Elem::Formula(Box::new(Formula::Binop { kind: FormulaBinop::FlexOr, pos, f }))
          }
          b"Predicative-Formula" => {
            let (mut pos, (mut sym, mut spelling)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => sym = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            self.r.read_start(&mut self.buf, Some(b"Arguments"));
            let left = self.parse_terms();
            self.r.read_start(&mut self.buf, Some(b"Arguments"));
            let right = self.parse_terms();
            let f = Pred { sym: (sym, spelling), left, right };
            Elem::Formula(Box::new(Formula::Pred { pos, f }))
          }
          b"RightSideOf-Predicative-Formula" => {
            let (mut sym, mut spelling) = <_>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"nr" => sym = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            self.r.read_start(&mut self.buf, Some(b"Arguments"));
            let right = self.parse_terms();
            Elem::PredRhs(Box::new(PredRhs { sym: (sym, spelling), right }))
          }
          b"Multi-Predicative-Formula" => {
            let pos = self.r.get_pos(&e);
            let first = match *self.parse_formula() {
              Formula::Pred { f, .. } => f,
              _ => panic!("expected predicate"),
            };
            let mut rest = vec![];
            loop {
              match self.parse_elem() {
                Elem::PredRhs(rhs) => rest.push(*rhs),
                Elem::End => break,
                _ => panic!("expected <RightSideOf-Predicative-Formula>"),
              }
            }
            return Elem::Formula(Box::new(Formula::ChainPred { pos, first, rest }))
          }
          b"Private-Predicate-Formula" => {
            let (mut pos, (mut sym, mut spelling)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"idnr" => sym = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            let args = self.parse_terms();
            return Elem::Formula(Box::new(Formula::PrivPred { pos, sym: (sym, spelling), args }))
          }
          b"Attributive-Formula" => Elem::Formula(Box::new(Formula::Attr {
            pos: self.r.get_pos(&e),
            term: self.parse_term().unwrap(),
            attrs: self.parse_adjectives(),
          })),
          b"Qualifying-Formula" => Elem::Formula(Box::new(Formula::Is {
            pos: self.r.get_pos(&e),
            term: self.parse_term().unwrap(),
            ty: self.parse_type().unwrap(),
          })),
          b"Universal-Quantifier-Formula" => {
            let pos = self.r.get_pos(&e);
            let (var, f) = (self.parse_binder(), self.parse_formula());
            Elem::Formula(Box::new(Formula::Binder { kind: FormulaBinder::ForAll, pos, var, f }))
          }
          b"Existential-Quantifier-Formula" => {
            let pos = self.r.get_pos(&e);
            let (var, f) = (self.parse_binder(), self.parse_formula());
            Elem::Formula(Box::new(Formula::Binder { kind: FormulaBinder::Exists, pos, var, f }))
          }
          b"Thesis" => Elem::Formula(Box::new(Formula::Thesis { pos: self.r.get_pos(&e) })),
          b"Contradiction" => Elem::Formula(Box::new(Formula::False { pos: self.r.get_pos(&e) })),
          b"Predicate-Pattern" => {
            let (mut pos, (mut sym, mut spelling)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => sym = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            let (left, right) = (self.parse_loci(), self.parse_loci());
            let pat = PatternPred { pos, sym: (sym, spelling), left, right };
            Elem::Pattern(Pattern::Pred(Box::new(pat)))
          }
          b"Operation-Functor-Pattern" => {
            let (mut pos, (mut sym, mut spelling)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => sym = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            let (left, right) = (self.parse_loci(), self.parse_loci());
            let pat = PatternFunc::Func { pos, sym: (sym, spelling), left, right };
            Elem::Pattern(Pattern::Func(Box::new(pat)))
          }
          b"Bracket-Functor-Pattern" => {
            let (mut pos, (mut lsym, mut lsp)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => lsym = self.r.get_attr(&attr.value),
                b"spelling" => lsp = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            let (rsym, args) = (self.parse_right_pattern(), self.parse_loci());
            let pat = PatternFunc::Bracket { pos, lsym: (lsym, lsp), rsym, args };
            Elem::Pattern(Pattern::Func(Box::new(pat)))
          }
          b"Mode-Pattern" => {
            let (mut pos, (mut sym, mut spelling)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => sym = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            let pat = PatternMode { pos, sym: (sym, spelling), args: self.parse_loci() };
            Elem::Pattern(Pattern::Mode(Box::new(pat)))
          }
          b"Attribute-Pattern" => {
            let (mut pos, (mut sym, mut spelling)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => sym = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            let (arg, args) = (self.parse_locus().unwrap(), self.parse_loci());
            let pat = PatternAttr { pos, sym: (sym, spelling), arg, args };
            Elem::Pattern(Pattern::Attr(Box::new(pat)))
          }
          b"Selector" => {
            let (mut pos, (mut sym, mut spelling)) = <(Position, _)>::default();
            for attr in e.attributes().map(Result::unwrap) {
              match attr.key {
                b"line" => pos.line = self.r.get_attr(&attr.value),
                b"col" => pos.col = self.r.get_attr(&attr.value),
                b"nr" => sym = self.r.get_attr(&attr.value),
                b"spelling" => spelling = self.r.get_attr_unescaped(&attr.value),
                _ => {}
              }
            }
            Elem::Selector(Field { pos, sym: (sym, spelling) })
          }
          _ => Elem::Other,
        };
        self.r.end_tag(&mut self.buf);
        elem
      } else {
        Elem::End
      }
    })
  }
}