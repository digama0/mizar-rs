use crate::ast::{SchRef, *};
use crate::parser::core::ParserCore;
use crate::types::{
  Article, ArticleId, DirectiveKind, Directives, Format, FromSymbolKind, PredSymId, PriorityKind,
  Span, SymbolKindClass, Symbols,
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
  /// Set by `fix_*` when the current item references something the JSON did not
  /// bind (an unknown symbol or article). `push_parse_item` poisons the item to
  /// `ItemKind::Error` when it is set, so no half-fixed item reaches the analyzer.
  had_error: bool,
  /// Position of the item currently being fixed, used as the span for `fix_*`
  /// diagnostics (the failing sub-term carries no span of its own).
  cur_pos: Span,
}

impl JsonParser {
  pub fn new(core: ParserCore, jv: Value) -> Self {
    Self {
      core,
      state: State::Init(jv),
      symbols: Default::default(),
      had_error: false,
      cur_pos: Span::NONE,
    }
  }

  /// Report a malformed-JSON error. `.wsx`/`.miz.json` input is mizar-rs's own
  /// alternate front-end, so these are structural mismatches rather than syntax
  /// errors with a source span; they render fine as plain messages (see
  /// `notes/error-handling.md`) and, being `Error`-severity, fail the article and
  /// block export exactly like any other diagnostic.
  fn report(&self, span: Span, msg: impl Into<String>) {
    self.core.reporter.emit(crate::Diagnostic::error(span, msg.into()));
  }

  /// Report against the current item and mark it tainted (see [`Self::had_error`]).
  fn err(&mut self, msg: impl Into<String>) {
    self.report(self.cur_pos, msg);
    self.had_error = true;
  }

  /// A predicate/pattern carries a `left`/`right` split; the right arity is formed as
  /// `args.len() - left`, so `left` past the argument count underflows in every
  /// `to_format`/elaboration site. Valid input keeps `left <= nargs`.
  fn check_left(&mut self, left: u8, nargs: usize, what: &str) {
    if left as usize > nargs {
      self.err(format!(
        "malformed .miz.json: {what} splits at {left} but has only {nargs} argument(s)"
      ));
    }
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

  /// Returns `true` if the environment was fatally malformed. A broken environment
  /// cannot yield a well-formed article — in particular the required HIDDEN
  /// directives would be missing, tripping `RequirementIndexes::init_rev` downstream
  /// — so any structural failure here reports and asks the caller to abandon the
  /// article, rather than limping on with a half-built environment.
  #[must_use]
  pub fn parse_env(&mut self, dirs: &mut Directives) -> bool {
    let State::Init(val) = &mut self.state else { unreachable!() };
    let val = val.take();
    // Default to an empty body; the success path below overwrites it. This also
    // releases the borrow of `self.state` taken above.
    self.state = State::Main(Vec::new().into_iter());
    let Value::Object(mut obj) = val else {
      self.report(Span::NONE, "malformed .miz.json: expected a top-level object");
      return true
    };
    let mut fatal = false;
    for dir in (0..DirectiveKind::LENGTH).map(DirectiveKind::from_usize) {
      if let Some(v) = obj.get(dir.name()) {
        if let Err(e) = <_>::deserialize_in_place(v, &mut dirs.0[dir]) {
          self
            .report(Span::NONE, format!("malformed .miz.json in directive '{}': {e}", dir.name()));
          fatal = true;
        }
      }
    }
    for dir in [
      DirectiveKind::Vocabularies,
      DirectiveKind::Notations,
      DirectiveKind::Constructors,
      DirectiveKind::Requirements,
    ] {
      if dirs.0[dir].first().map(|x| x.art) != Some(Article::HIDDEN) {
        let name = dir.name();
        self.report(
          Span::NONE,
          format!("malformed .miz.json: directive '{name}' must begin with the HIDDEN article"),
        );
        fatal = true;
      }
    }
    self.core.write_json.on(|w| w.write_env(dirs));
    if let Some(Value::Array(body)) = obj.remove("body") {
      self.state = State::Main(body.into_iter())
    } else {
      self.report(Span::NONE, "malformed .miz.json: expected a 'body' array");
      fatal = true;
    }
    fatal
  }

  fn fix_terms(&mut self, tms: &mut [Term]) { tms.iter_mut().for_each(|tm| self.fix_term(tm)); }

  fn fix<T: FromSymbolKind>(&mut self, id: &mut T, spelling: &str) {
    *id = if let Some(&n) = self.symbols[T::CLASS].get(spelling) {
      T::from_usize(n as usize)
    } else {
      self.err(format!("malformed .miz.json: unknown {:?} symbol {spelling:?}", T::CLASS));
      // Keep a well-formed (if meaningless) id; the item is poisoned regardless.
      T::from_usize(0)
    }
  }

  fn fix_article(&mut self, art: &mut ArticleId, spelling: &Article) {
    match self.core.articles.get(spelling) {
      Some(&a) => *art = a,
      None => self.err(format!("malformed .miz.json: reference to unknown article {spelling}")),
    }
  }

  fn fix_binders(&mut self, vars: &mut [BinderGroup]) {
    for BinderGroup { ty, vars } in vars {
      // Every binder context (let/given, consider, ∀/∃, fraenkel) declares at least
      // one variable per group; an empty group trips a genuine analyzer invariant.
      if vars.is_empty() {
        self.err("malformed .miz.json: a variable binding declares no variables");
      }
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

  fn fix_pred(&mut self, Pred { sym, spelling, args, left, .. }: &mut Pred) {
    self.fix(sym, spelling);
    self.check_left(*left, args.len(), "predicate");
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
    attrs.iter_mut().for_each(|attr| self.fix_attr(attr))
  }

  fn fix_types(&mut self, ts: &mut [Type]) { ts.iter_mut().for_each(|ty| self.fix_type(ty)) }

  fn fix_references(&mut self, rs: &mut [Reference]) {
    for r in rs {
      if let ReferenceKind::Global { art, spelling, .. } = &mut r.kind {
        match self.core.articles.get(spelling).copied() {
          Some(a) => *art = a,
          None => {
            let msg = format!(
              "malformed .miz.json: reference to unknown article {spelling} \
               (perhaps a missing 'theorems {spelling}' directive)"
            );
            self.err(msg)
          }
        }
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
      PatternFunc::Func { sym, spelling, left, args, .. } => {
        self.fix(sym, spelling);
        self.check_left(*left, args.len(), "functor pattern");
      }
      // `Bracket`'s format is `args.len()` with no split, so it cannot underflow.
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
    cc.iter_mut().for_each(|c| self.fix_justification(&mut c.just));
    if let Some(corr) = corr {
      self.fix_justification(&mut corr.just)
    }
  }

  fn fix_properties(&mut self, props: &mut [Property]) {
    props.iter_mut().for_each(|p| self.fix_justification(&mut p.just));
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
        self.check_left(pat.left, pat.args.len(), "predicate pattern");
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
    // Skip registering the format of a malformed definition: the item is poisoned,
    // and `to_format` on a bad functor/predicate pattern (left > argc) would underflow.
    if !self.had_error {
      self.core.after_definition(def.kind.pos(), def.body.redef, def.kind.to_format());
    }
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

  fn fix_items(&mut self, is: &mut [Item]) { is.iter_mut().for_each(|i| self.fix_item_checked(i)) }

  /// Fix one item with its own `had_error` scope, poisoning just this item to
  /// `ItemKind::Error` on failure. Scoping per item keeps a malformed item from
  /// tainting its valid siblings in the same block.
  fn fix_item_checked(&mut self, i: &mut Item) {
    let outer = std::mem::take(&mut self.had_error);
    self.fix_item(i);
    if self.had_error {
      i.kind = ItemKind::Error;
    }
    self.had_error = outer;
  }

  fn fix_item(&mut self, i: &mut Item) {
    self.cur_pos = i.pos;
    match &mut i.kind {
      ItemKind::Section | ItemKind::Pragma(_) | ItemKind::Error => {}
      ItemKind::Block { items, .. } => self.fix_items(items),
      ItemKind::SchemeBlock(s) => {
        for g in &mut s.head.groups {
          // Each declaration group elaborates one scheme functor/predicate per
          // variable, so an empty group is malformed (the analyzer asserts this).
          match g {
            SchemeBinderGroup::Pred { tys, vars, .. } => {
              if vars.is_empty() {
                self.err("malformed .miz.json: scheme predicate declaration has no variables");
              }
              self.fix_types(tys)
            }
            SchemeBinderGroup::Func { tys, ret, vars, .. } => {
              if vars.is_empty() {
                self.err("malformed .miz.json: scheme functor declaration has no variables");
              }
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
          f.vars.iter_mut().for_each(|v| self.fix(&mut v.sym, &v.spelling));
          self.fix_type(&mut f.ty);
        }
        self.fix(&mut def.pat.sym, &def.pat.spelling);
        ParserCore::after_def_struct(i.pos, def, |pos, fmt| {
          self.core.push_format(pos, fmt);
        });
      }
      ItemKind::PatternRedef(PatternRedef::Pred { new, orig, .. }) => {
        self.fix(&mut new.sym, &new.spelling);
        self.fix(&mut orig.sym, &orig.spelling);
        self.check_left(new.left, new.args.len(), "predicate pattern");
        self.check_left(orig.left, orig.args.len(), "predicate pattern");
        if !self.had_error {
          self.core.push_format(new.pos, Format::Pred(new.to_format()));
        }
      }
      ItemKind::PatternRedef(PatternRedef::Func { new, orig }) => {
        self.fix_pattern_func(new);
        self.fix_pattern_func(orig);
        if !self.had_error {
          self.core.push_format(new.pos(), Format::Func(new.to_format()));
        }
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
    let mut item: Item = match serde_json::from_value(it) {
      Ok(item) => item,
      Err(e) => {
        // A malformed item becomes an error item, and the next one starts fresh.
        self.report(Span::NONE, format!("malformed .miz.json item: {e}"));
        Item { pos: Span::NONE, kind: ItemKind::Error }
      }
    };
    self.fix_item_checked(&mut item);
    self.core.write_json.on(|w| w.write_item(&item));
    buf.push(item);
    true
  }
}
