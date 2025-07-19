use crate::ast::{SchRef, *};
use crate::parser::core::ParserCore;
use crate::types::{
  Article, ArticleId, DirectiveKind, Directives, Format, FromSymbolKind, PredSymId, PriorityKind,
  SymbolKindClass, Symbols,
};
use enum_map::{Enum, EnumMap};
use serde::Deserialize;
use serde_json::Value;
use std::collections::HashMap;

enum State {
  Init(Value),
  Main(std::vec::IntoIter<Value>),
}
pub struct JsonParser {
  state: State,
  pub core: ParserCore,
  symbols: EnumMap<SymbolKindClass, HashMap<String, u32>>,
}

impl JsonParser {
  pub fn new(core: ParserCore, jv: Value) -> Self {
    Self { core, state: State::Init(jv), symbols: Default::default() }
  }

  pub fn load_symbols(
    &mut self, syms: &Symbols, infinitives: &[(PredSymId, &str)], prio: &[(PriorityKind, u32)],
  ) {
    ParserCore::on_symbols(syms, infinitives, |kind, s| {
      let (kind, n) = kind.into();
      assert!(self.symbols[kind].insert(s.to_string(), n).is_none())
    });
    self.core.load_prio(prio)
  }

  pub fn parse_env(&mut self, dirs: &mut Directives) {
    let State::Init(val) = &mut self.state else { unreachable!() };
    let Value::Object(obj) = val.take() else { panic!("expected object") };
    for dir in (0..DirectiveKind::LENGTH).map(DirectiveKind::from_usize) {
      if let Some(v) = obj.get(dir.name()) {
        <_>::deserialize_in_place(v, &mut dirs.0[dir]).expect("parse error")
      }
    }
    for dir in [
      DirectiveKind::Vocabularies,
      DirectiveKind::Notations,
      DirectiveKind::Constructors,
      DirectiveKind::Requirements,
    ] {
      assert_eq!(dirs.0[dir].first().map(|x| x.art), Some(Article::HIDDEN))
    }
    self.core.write_json.on(|w| w.write_env(dirs));
    let Some(Value::Array(body)) = { obj }.remove("body") else { panic!("expected body array") };
    self.state = State::Main(body.into_iter())
  }

  fn fix_terms(&mut self, tms: &mut [Term]) { tms.into_iter().for_each(|tm| self.fix_term(tm)); }

  fn fix<T: FromSymbolKind>(&mut self, id: &mut T, spelling: &str) {
    if !self.symbols[T::CLASS].contains_key(spelling) {
      eprintln!("{:?}", &self.symbols[T::CLASS]);
      eprintln!("{:?}", spelling);
    }
    *id = T::from_usize(self.symbols[T::CLASS][spelling] as usize);
  }

  fn fix_article(&mut self, art: &mut ArticleId, spelling: &Article) {
    *art = *self.core.articles.get(spelling).expect("article not found");
  }

  fn fix_binders(&mut self, vars: &mut [BinderGroup]) {
    for BinderGroup { ty, .. } in vars {
      if let Some(ty) = ty {
        self.fix_type(ty)
      }
    }
  }

  fn fix_term(&mut self, tm: &mut Term) {
    match tm {
      Term::PrivFunc { args, .. } => self.fix_terms(args),
      Term::Infix { sym, spelling, args, .. } => {
        self.fix(sym, spelling);
        self.fix_terms(args)
      }
      Term::Bracket { lsym, lspelling, rsym, rspelling, args, .. } => {
        self.fix(lsym, lspelling);
        self.fix(rsym, rspelling);
        self.fix_terms(args)
      }
      Term::Aggregate { sym, spelling, args, .. } => {
        self.fix(sym, spelling);
        self.fix_terms(args)
      }
      Term::SubAggr { sym, spelling, arg, .. } => {
        self.fix(sym, spelling);
        self.fix_term(arg)
      }
      Term::Selector { sym, spelling, arg, .. } => {
        self.fix(sym, spelling);
        self.fix_term(arg)
      }
      Term::InternalSelector { sym, spelling, .. } => self.fix(sym, spelling),
      Term::Qua { term, ty, .. } => {
        self.fix_term(term);
        self.fix_type(ty)
      }
      Term::The { ty, .. } => self.fix_type(ty),
      Term::Fraenkel { vars, scope, compr, .. } => {
        self.fix_binders(vars);
        self.fix_term(scope);
        if let Some(f) = compr {
          self.fix_formula(f)
        }
      }
      _ => {}
    }
  }

  fn fix_pred(&mut self, Pred { sym, spelling, args, .. }: &mut Pred) {
    self.fix(sym, spelling);
    self.fix_terms(args)
  }

  fn fix_pred_rhs(&mut self, PredRhs { sym, spelling, right, .. }: &mut PredRhs) {
    self.fix(sym, spelling);
    self.fix_terms(right)
  }

  fn fix_formula(&mut self, f: &mut Formula) {
    match f {
      Formula::Not { f, .. } => self.fix_formula(f),
      Formula::Binop { f1, f2, .. } => {
        self.fix_formula(f1);
        self.fix_formula(f2)
      }
      Formula::Pred(pred) => self.fix_pred(pred),
      Formula::ChainPred { first, rest, .. } => {
        self.fix_pred(first);
        rest.iter_mut().for_each(|p| self.fix_pred_rhs(p))
      }
      Formula::PrivPred { args, .. } => self.fix_terms(args),
      Formula::Attr { term, attrs, .. } => {
        self.fix_term(term);
        self.fix_attrs(attrs)
      }
      Formula::Is { term, ty, .. } => {
        self.fix_term(term);
        self.fix_type(ty)
      }
      Formula::Binder { vars, st, scope, .. } => {
        self.fix_binders(vars);
        if let Some(st) = st {
          self.fix_formula(st)
        }
        self.fix_formula(scope)
      }
      _ => {}
    }
  }

  fn fix_type(&mut self, ty: &mut Type) {
    match ty {
      Type::Mode { sym, spelling, args, .. } => {
        self.fix(sym, spelling);
        self.fix_terms(args)
      }
      Type::Struct { sym, spelling, args, .. } => {
        self.fix(sym, spelling);
        self.fix_terms(args)
      }
      Type::Cluster { attrs, ty, .. } => {
        self.fix_attrs(attrs);
        self.fix_type(ty)
      }
      _ => {}
    }
  }

  fn fix_attr(&mut self, attr: &mut Attr) {
    match attr {
      Attr::Attr { sym, spelling, args, .. } => {
        self.fix(sym, spelling);
        self.fix_terms(args)
      }
      Attr::Non { attr, .. } => self.fix_attr(attr),
    }
  }

  fn fix_attrs(&mut self, attrs: &mut [Attr]) {
    attrs.into_iter().for_each(|attr| self.fix_attr(attr))
  }

  fn fix_types(&mut self, ts: &mut [Type]) { ts.iter_mut().for_each(|ty| self.fix_type(ty)) }

  fn fix_references(&mut self, rs: &mut [Reference]) {
    for r in rs {
      if let ReferenceKind::Global { art, spelling, .. } = &mut r.kind {
        *art = *(self.core.articles.get(&spelling))
          .unwrap_or_else(|| panic!("article not found, perhaps you forgot 'theorems {spelling}'"));
      }
    }
  }

  fn fix_propositions(&mut self, ps: &mut [Proposition]) {
    ps.iter_mut().for_each(|p| self.fix_formula(&mut p.f))
  }

  fn fix_justification(&mut self, j: &mut Justification) {
    match j {
      Justification::Inference { kind, refs, .. } => {
        if let InferenceKind::From(SchRef::Resolved { art, spelling, .. }) = kind {
          self.fix_article(art, spelling);
        }
        self.fix_references(refs)
      }
      Justification::Block { items, .. } => self.fix_items(items),
    }
  }

  fn fix_pattern_func(&mut self, pat: &mut PatternFunc) {
    match pat {
      PatternFunc::Func { sym, spelling, .. } => self.fix(sym, spelling),
      PatternFunc::Bracket { lsym, lspelling, rsym, rspelling, .. } => {
        self.fix(lsym, lspelling);
        self.fix(rsym, rspelling)
      }
    }
  }

  fn fix_def_body<T>(&mut self, body: &mut DefBody<T>, mut fix: impl FnMut(&mut Self, &mut T)) {
    for DefCase { case, guard, .. } in &mut body.cases {
      fix(self, case);
      self.fix_formula(guard)
    }
    if let Some(f) = &mut body.otherwise {
      fix(self, f)
    }
  }

  fn fix_definiens(&mut self, d: &mut Option<Box<Definiens>>) {
    if let Some(d) = d {
      match &mut d.kind {
        DefValue::Term(body) => self.fix_def_body(body, |this, x| this.fix_term(x)),
        DefValue::Formula(body) => self.fix_def_body(body, |this, x| this.fix_formula(x)),
      }
    }
  }

  fn fix_corr_conds(&mut self, cc: &mut [CorrCond], corr: &mut Option<Correctness>) {
    cc.into_iter().for_each(|c| self.fix_justification(&mut c.just));
    if let Some(corr) = corr {
      self.fix_justification(&mut corr.just)
    }
  }

  fn fix_properties(&mut self, props: &mut [Property]) {
    props.into_iter().for_each(|p| self.fix_justification(&mut p.just));
  }

  fn fix_definition(&mut self, def: &mut Definition) {
    match &mut def.kind {
      DefinitionKind::Func { pat, spec, def } => {
        self.fix_pattern_func(pat);
        if let Some(spec) = spec {
          self.fix_type(spec)
        }
        self.fix_definiens(def)
      }
      DefinitionKind::Pred { pat, def } => {
        self.fix(&mut pat.sym, &pat.spelling);
        self.fix_definiens(def)
      }
      DefinitionKind::Mode { pat, kind } => {
        self.fix(&mut pat.sym, &pat.spelling);
        match kind {
          DefModeKind::Expandable { expansion } => self.fix_type(expansion),
          DefModeKind::Standard { spec, def } => {
            if let Some(spec) = spec {
              self.fix_type(spec)
            }
            self.fix_definiens(def)
          }
        }
      }
      DefinitionKind::Attr { pat, def } => {
        self.fix(&mut pat.sym, &pat.spelling);
        self.fix_definiens(def)
      }
    }
    self.fix_corr_conds(&mut def.body.conds, &mut def.body.corr);
    self.fix_properties(&mut def.body.props);
    self.core.after_definition(def.kind.pos(), def.body.redef, def.kind.to_format());
  }

  fn fix_stmt(&mut self, s: &mut Statement) {
    match s {
      Statement::Proposition { prop, just } => {
        self.fix_formula(&mut prop.f);
        self.fix_justification(just)
      }
      Statement::IterEquality { prop, just, steps } => {
        self.fix_formula(&mut prop.f);
        self.fix_justification(just);
        for step in steps {
          self.fix_term(&mut step.rhs);
          self.fix_justification(&mut step.just)
        }
      }
      Statement::Now { items, .. } => self.fix_items(items),
    }
  }

  fn fix_assumption(&mut self, a: &mut Assumption) {
    match a {
      Assumption::Single { prop, .. } => self.fix_formula(&mut prop.f),
      Assumption::Collective { conds, .. } => self.fix_propositions(conds),
    }
  }

  fn fix_items(&mut self, is: &mut [Item]) { is.iter_mut().for_each(|i| self.fix_item(i)) }

  fn fix_item(&mut self, i: &mut Item) {
    match &mut i.kind {
      ItemKind::Section | ItemKind::Pragma(_) => {}
      ItemKind::Block { items, .. } => self.fix_items(items),
      ItemKind::SchemeBlock(s) => {
        for g in &mut s.head.groups {
          match g {
            SchemeBinderGroup::Pred { tys, .. } => self.fix_types(tys),
            SchemeBinderGroup::Func { tys, ret, .. } => {
              self.fix_types(tys);
              self.fix_type(ret)
            }
          }
        }
        self.fix_formula(&mut s.head.concl);
        self.fix_propositions(&mut s.head.prems);
        self.fix_items(&mut s.items)
      }
      ItemKind::Theorem { prop, just } => {
        self.fix_formula(&mut prop.f);
        self.fix_justification(just)
      }
      ItemKind::Reservation(r) => r.iter_mut().for_each(|r| self.fix_type(&mut r.ty)),
      ItemKind::Thus(s) => self.fix_stmt(s),
      ItemKind::Consider { vars, conds, just } => {
        self.fix_binders(vars);
        self.fix_propositions(conds);
        self.fix_justification(just)
      }
      ItemKind::Reconsider { vars, ty, just } => {
        for v in vars {
          if let ReconsiderVar::Equality { tm, .. } = v {
            self.fix_term(tm)
          }
        }
        self.fix_type(ty);
        self.fix_justification(just)
      }
      ItemKind::DefFunc { tys, value, .. } => {
        self.fix_types(tys);
        self.fix_term(value)
      }
      ItemKind::DefPred { tys, value, .. } => {
        self.fix_types(tys);
        self.fix_formula(value)
      }
      ItemKind::Set(ds) => ds.iter_mut().for_each(|d| self.fix_term(&mut d.value)),
      ItemKind::Let { vars, conds } | ItemKind::Given { vars, conds } => {
        self.fix_binders(vars);
        self.fix_propositions(conds)
      }
      ItemKind::Take(ds) => ds.iter_mut().for_each(|d| self.fix_term(&mut d.term)),
      ItemKind::PerCases { just, blocks, .. } => {
        self.fix_justification(just);
        for b in blocks {
          self.fix_assumption(&mut b.hyp);
          self.fix_items(&mut b.items)
        }
      }
      ItemKind::Assume(a) => self.fix_assumption(a),
      ItemKind::Unfold(rs) => self.fix_references(rs),
      ItemKind::Definition(def) => self.fix_definition(def),
      ItemKind::DefStruct(def) => {
        self.fix_types(&mut def.parents);
        for f in &mut def.fields {
          f.vars.iter_mut().for_each(|v| self.fix(&mut v.sym, &mut v.spelling));
          self.fix_type(&mut f.ty);
        }
        self.fix(&mut def.pat.sym, &mut def.pat.spelling);
        ParserCore::after_def_struct(i.pos, def, |pos, fmt| {
          self.core.push_format(pos, fmt);
        });
      }
      ItemKind::PatternRedef(PatternRedef::Pred { new, orig, .. }) => {
        self.fix(&mut new.sym, &new.spelling);
        self.fix(&mut orig.sym, &orig.spelling);
        self.core.push_format(new.pos, Format::Pred(new.to_format()));
      }
      ItemKind::PatternRedef(PatternRedef::Func { new, orig }) => {
        self.fix_pattern_func(new);
        self.fix_pattern_func(orig);
        self.core.push_format(new.pos(), Format::Func(new.to_format()));
      }
      ItemKind::PatternRedef(PatternRedef::Mode { new, orig }) => {
        self.fix(&mut new.sym, &new.spelling);
        self.fix(&mut orig.sym, &orig.spelling);
        self.core.push_format(new.pos, Format::Mode(new.to_format()));
      }
      ItemKind::PatternRedef(PatternRedef::Attr { new, orig, .. }) => {
        self.fix(&mut new.sym, &new.spelling);
        self.fix(&mut orig.sym, &orig.spelling);
        self.core.push_format(new.pos, Format::Attr(new.to_format()));
      }
      ItemKind::Cluster(c) => {
        match &mut c.kind {
          ClusterDeclKind::Exist { concl, ty } => {
            self.fix_attrs(concl);
            self.fix_type(ty)
          }
          ClusterDeclKind::Func { term, concl, ty } => {
            self.fix_term(term);
            self.fix_attrs(concl);
            if let Some(ty) = ty {
              self.fix_type(ty)
            }
          }
          ClusterDeclKind::Cond { antecedent, concl, ty } => {
            self.fix_attrs(antecedent);
            self.fix_attrs(concl);
            self.fix_type(ty)
          }
        }
        self.fix_corr_conds(&mut c.conds, &mut c.corr)
      }
      ItemKind::IdentifyFunc(f) => {
        self.fix_pattern_func(&mut f.lhs);
        self.fix_pattern_func(&mut f.rhs);
        self.fix_corr_conds(&mut f.conds, &mut f.corr)
      }
      ItemKind::Reduction(r) => {
        self.fix_term(&mut r.from);
        self.fix_term(&mut r.to);
        self.fix_corr_conds(&mut r.conds, &mut r.corr)
      }
      ItemKind::SethoodRegistration { ty, just } => {
        self.fix_type(ty);
        self.fix_justification(just)
      }
      ItemKind::Statement(s) => self.fix_stmt(s),
      ItemKind::SchemeHead(..) | ItemKind::CaseHead(..) | ItemKind::PerCasesHead(..) =>
        unreachable!(),
    }
  }

  pub fn push_parse_item(&mut self, buf: &mut Vec<Item>) -> bool {
    let State::Main(val) = &mut self.state else { unreachable!() };
    let Some(it) = val.next() else { return false };
    let mut item: Item = serde_json::from_value(it).unwrap();
    self.fix_item(&mut item);
    self.core.write_json.on(|w| w.write_item(&item));
    buf.push(item);
    true
  }
}
