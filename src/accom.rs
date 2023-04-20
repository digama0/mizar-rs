use crate::types::*;
use crate::{mk_id, CmpStyle, MizPath, VisitMut};
use std::collections::HashMap;
use std::io;

mk_id! {
  VocId(u32),
  SigId(u32),
}

#[derive(Debug, Default)]
struct VocBuilder {
  pub voc: IdxVec<VocId, (Article, SymbolsBase)>,
  base: SymbolsBase,
}

impl VocBuilder {
  fn push(&mut self, art: Article, val: &SymbolsBase) -> VocId {
    let i = self.voc.push((art, self.base));
    self.base += val;
    i
  }

  fn get_or_push(&mut self, art: Article, val: &SymbolsBase) -> VocId {
    let res = self.voc.enum_iter().find(|p| p.1 .0 == art);
    if let Some((i, (_, val2))) = res {
      assert_eq!(*self.hi(i) - val2, *val);
      i
    } else {
      self.push(art, val)
    }
  }

  fn hi(&self, id: VocId) -> &SymbolsBase {
    self.voc.get(VocId(id.0 + 1)).map_or(&self.base, |(_, base)| base)
  }

  fn truncate(&mut self, len: usize) {
    if self.voc.len() > len {
      self.base = self.voc.0[len].1;
      self.voc.0.truncate(len)
    }
  }
}

#[derive(Debug, Default)]
pub struct SigBuilder {
  pub sig: IdxVec<SigId, (Article, ConstructorsBase)>,
  pub base: ConstructorsBase,
}

impl SigBuilder {
  fn push(&mut self, constrs: Option<&mut Constructors>, art: Article) -> SigId {
    let mut dco = Default::default();
    assert!(MizPath::new(art.as_str()).read_dco(false, &mut dco, constrs.is_some()).unwrap());
    self.push_from(constrs, art, &mut dco)
  }

  fn push_from(
    &mut self, constrs: Option<&mut Constructors>, art: Article, dco: &mut DepConstructors,
  ) -> SigId {
    if let Some(constrs) = constrs {
      let mut rename = RenameConstr::default();
      for &art2 in &dco.sig {
        let i = self.get(art2);
        rename.push(self, i, true);
      }
      let i = self.sig.push((art, self.base));
      self.base += dco.counts;
      rename.push(self, i, true);
      dco.constrs.visit(&mut rename);
      constrs.append(&mut dco.constrs);
      i
    } else {
      let i = self.sig.push((art, self.base));
      self.base += dco.counts;
      i
    }
  }

  fn get_or_push(&mut self, constrs: Option<&mut Constructors>, art: Article) -> SigId {
    let id = self.sig.enum_iter().find(|p| p.1 .0 == art);
    id.map(|p| p.0).unwrap_or_else(|| self.push(constrs, art))
  }

  fn get(&self, art: Article) -> SigId {
    match self.sig.enum_iter().find(|p| p.1 .0 == art) {
      Some((id, _)) => id,
      None => panic!("{art} declared out of order"),
    }
  }

  fn hi(&self, id: SigId) -> &ConstructorsBase {
    self.sig.get(SigId(id.0 + 1)).map_or(&self.base, |(_, base)| base)
  }

  fn rename<'a>(&mut self, sig: &[Article], ctx: Option<&'a Constructors>) -> RenameConstr<'a> {
    let mut rename = RenameConstr { ctx, ..Default::default() };
    let limit = self.sig.len();
    for &art in sig {
      let id = self.get_or_push(None, art);
      rename.push(self, id, id.into_usize() < limit)
    }
    rename
  }

  fn truncate(&mut self, len: usize) {
    if self.sig.len() > len {
      self.base = self.sig.0[len].1;
      self.sig.0.truncate(len)
    }
  }
}

#[derive(Debug, Default)]
pub struct Accomodator {
  pub dirs: Directives,
  pub sig: SigBuilder,
  pub articles: HashMap<Article, ArticleId>,
  dict: VocBuilder,
}

#[derive(Debug, Default)]
struct RenameSymbol {
  trans: Vec<(SymbolsBase, SymbolsBase, bool)>,
  base: SymbolsBase,
  failed: bool,
}
impl RenameSymbol {
  fn push(&mut self, val: &SymbolsBase, tgt: &SymbolsBase, allow: bool) {
    self.trans.push((self.base, *tgt, allow));
    self.base += val;
  }
  fn apply(&mut self, k: SymbolKindClass, n: &mut u32) {
    if let Some(i) = self.trans.partition_point(|(base, _, _)| base.0[k] <= *n).checked_sub(1) {
      let (from, to, allow) = &self.trans[i];
      *n = *n - from.0[k] + to.0[k];
      self.failed |= !*allow;
    }
  }
  fn ok(&mut self) -> bool { !std::mem::take(&mut self.failed) }
}

#[derive(Debug, Default)]
struct RenameConstr<'a> {
  trans: Vec<(ConstructorsBase, ConstructorsBase, bool)>,
  base: ConstructorsBase,
  failed: bool,
  ctx: Option<&'a Constructors>,
}
impl RenameConstr<'_> {
  fn push(&mut self, sig: &SigBuilder, i: SigId, allow: bool) {
    let lo = self.base;
    self.base += *sig.hi(i) - sig.sig[i].1;
    self.trans.push((lo, sig.sig[i].1, allow))
  }

  fn apply(&mut self, n: &mut u32, key: impl Fn(&ConstructorsBase) -> u32) {
    assert!(*n < key(&self.base));
    if let Some(i) = self.trans.partition_point(|p| key(&p.0) <= *n).checked_sub(1) {
      let (from, to, allow) = &self.trans[i];
      *n = *n - key(from) + key(to);
      self.failed |= !*allow;
    }
  }

  fn ok(&mut self) -> bool { !std::mem::take(&mut self.failed) }
}

impl VisitMut for RenameConstr<'_> {
  const MODIFY_IDS: bool = true;
  fn abort(&self) -> bool { self.failed }
  fn visit_mode_id(&mut self, n: &mut ModeId) { self.apply(&mut n.0, |b| b.mode) }
  fn visit_struct_id(&mut self, n: &mut StructId) { self.apply(&mut n.0, |b| b.struct_mode) }
  fn visit_attr_id(&mut self, n: &mut AttrId) { self.apply(&mut n.0, |b| b.attribute) }
  fn visit_pred_id(&mut self, n: &mut PredId) { self.apply(&mut n.0, |b| b.predicate) }
  fn visit_func_id(&mut self, n: &mut FuncId) { self.apply(&mut n.0, |b| b.functor) }
  fn visit_sel_id(&mut self, n: &mut SelId) { self.apply(&mut n.0, |b| b.selector) }
  fn visit_aggr_id(&mut self, n: &mut AggrId) { self.apply(&mut n.0, |b| b.aggregate) }
  fn visit_attrs(&mut self, attrs: &mut Attrs) {
    if let Attrs::Consistent(attrs) = attrs {
      for attr in &mut *attrs {
        self.visit_attr_id(&mut attr.nr);
        self.visit_terms(&mut attr.args);
        if self.failed {
          return
        }
      }
      attrs.sort_by(|a, b| a.cmp(self.ctx, None, b, CmpStyle::Attr));
    }
  }
}

impl Accomodator {
  /// ProcessVocabularies
  pub fn accom_symbols<'a>(
    &mut self, mml_vct: &'a [u8], syms: &mut Symbols, priority: &mut Vec<(PriorityKind, u32)>,
    mut infinitives: Option<&mut Vec<(PredSymId, &'a str)>>,
  ) {
    for &(_, art) in &self.dirs.0[DirectiveKind::Vocabularies] {
      let mut voc = Default::default();
      assert!(art.read_vct(mml_vct, &mut voc)); // TODO: private vocabularies
      let hidden = self.dict.voc.is_empty();
      self.dict.voc.push((art, self.dict.base));
      if hidden {
        // The setup here is a bit weird. The HIDDEN article has some tokens defined
        // here by hard-coding, and other tokens defined in mml.vct. The net result is
        // that even though mml.vct says "G0 K0 L0 M1 O0 R2 U0 V1" it is really
        // treated as "G0 K3 L3 M2 O0 R3 U0 V1" when appearing in .dno files.
        for &(c, token) in SymbolData::BUILTIN_SYMBOLS {
          let n = self.dict.base.0[c];
          self.dict.base.0[c] += 1;
          syms.push(((c, n).into(), token.to_owned()));
        }
      }
      for SymbolData { kind, token } in voc.symbols {
        let c = kind.class();
        let n = self.dict.base.0[c];
        self.dict.base.0[c] += 1;
        match kind {
          SymbolDataKind::LeftBrk =>
            priority.push((PriorityKind::LeftBrk(LeftBrkSymId(n)), DEFAULT_PRIO)),
          SymbolDataKind::RightBrk =>
            priority.push((PriorityKind::RightBrk(RightBrkSymId(n)), DEFAULT_PRIO)),
          SymbolDataKind::Func { prio } =>
            priority.push((PriorityKind::Functor(FuncSymId(n)), prio)),
          SymbolDataKind::Pred { infinitive: Some(inf) } =>
            if let Some(infs) = &mut infinitives {
              infs.push((PredSymId(n), inf))
            },
          _ => {}
        }
        syms.push(((c, n).into(), token.to_owned()))
      }
    }
  }

  pub fn accom_articles(&mut self) {
    let mut id = ArticleId(1); // 0 is reserved for SELF
    for &(_, art) in &self.dirs.0[DirectiveKind::Theorems] {
      assert!(self.articles.insert(art, id.fresh()).is_none())
    }
    for &(_, art) in &self.dirs.0[DirectiveKind::Schemes] {
      self.articles.entry(art).or_insert_with(|| id.fresh());
    }
  }

  /// ProcessConstructors
  pub fn accom_constructors(&mut self, constrs: &mut Constructors) -> io::Result<()> {
    for &(_, art) in &self.dirs.0[DirectiveKind::Constructors] {
      let mut dco = Default::default();
      assert!(MizPath::new(art.as_str()).read_dco(false, &mut dco, true).unwrap());
      for &art2 in &dco.sig {
        self.sig.get_or_push(Some(constrs), art2);
      }
      if !self.sig.sig.0.iter().any(|p| p.0 == art) {
        self.sig.push_from(Some(constrs), art, &mut dco);
      }
    }
    Ok(())
  }

  /// ProcessRequirements
  pub fn accom_requirements(
    &mut self, ctx: &Constructors, idx: &mut RequirementIndexes,
  ) -> io::Result<()> {
    for &(_, art) in &self.dirs.0[DirectiveKind::Requirements] {
      let mut dre = Default::default();
      MizPath::new(art.as_str()).read_dre(&mut dre)?;
      let len = self.sig.sig.len();
      let mut rename = self.sig.rename(&dre.sig, Some(ctx));
      for DepRequirement { req, mut kind } in dre.reqs {
        kind.visit(&mut rename);
        assert!(rename.ok() && kind.lt(&ctx.len()), "inaccessible requirement");
        idx.set(req, kind);
      }
      self.sig.truncate(len);
    }
    Ok(())
  }

  /// ProcessClusters
  pub fn accom_clusters(&mut self, ctx: &Constructors, clusters: &mut Clusters) -> io::Result<()> {
    for &(_, art) in &self.dirs.0[DirectiveKind::Registrations] {
      let mut dcl = Default::default();
      if MizPath::new(art.as_str()).read_dcl(false, &mut dcl)? {
        let len = self.sig.sig.len();
        let mut rename = self.sig.rename(&dcl.sig, Some(ctx));
        for mut cl in dcl.cl.registered {
          cl.visit(&mut rename);
          if rename.ok() {
            clusters.registered.push(cl);
          }
        }
        for mut cl in dcl.cl.functor {
          cl.visit(&mut rename);
          if rename.ok() {
            clusters.functor.0.push(cl);
          }
        }
        for mut cl in dcl.cl.conditional {
          cl.visit(&mut rename);
          if rename.ok() {
            clusters.conditional.push(ctx, cl);
          }
        }
        self.sig.truncate(len);
      }
    }
    Ok(())
  }

  /// ProcessNotation
  pub fn accom_notations(
    &mut self, fmt_map: &mut HashMap<Format, FormatId>, mut fmts: Option<&mut Formats>,
    pats: &mut Vec<Pattern>,
  ) -> io::Result<()> {
    if let Some(fmts) = &mut fmts {
      assert_eq!(fmts.formats.push(Format::Attr(FormatAttr::STRICT)), FormatId::STRICT);
      fmt_map.insert(Format::Attr(FormatAttr::STRICT), FormatId::STRICT);
    }
    for &(_, art) in &self.dirs.0[DirectiveKind::Notations] {
      let dict_len = self.dict.voc.len();
      let mut dno = Default::default();
      assert!(MizPath::new(art.as_str()).read_dno(false, &mut dno)?);
      let mut s_rename = RenameSymbol::default();
      for &(art, ref val) in &dno.vocs.0 {
        let i = self.dict.get_or_push(art, val);
        s_rename.push(val, &self.dict.voc[i].1, i.0 < dict_len as u32);
      }
      let sig_len = self.sig.sig.len();
      let mut rename = self.sig.rename(&dno.sig, None);
      for Pattern { mut kind, mut fmt, mut primary, visible, pos } in dno.pats {
        fmt.visit_mut(|k, c| s_rename.apply(k, c));
        if s_rename.ok() {
          if let Some(fmt) = match &mut fmts {
            Some(fmts) => Some(*fmt_map.entry(fmt).or_insert_with(|| fmts.formats.push(fmt))),
            None => fmt_map.get(&fmt).copied(),
          } {
            kind.visit(&mut rename);
            primary.visit(&mut rename);
            if rename.ok() {
              pats.push(Pattern { kind, fmt, primary, visible, pos })
            }
          }
        }
      }
      self.dict.truncate(dict_len);
      self.sig.truncate(sig_len);
    }
    pats.sort_by_key(|pat| pat.kind.class() as u8);
    Ok(())
  }

  /// ProcessIdentify
  pub fn accom_identify_regs(
    &mut self, ctx: &Constructors, ids: &mut Vec<IdentifyFunc>,
  ) -> io::Result<()> {
    for &(_, art) in &self.dirs.0[DirectiveKind::Registrations] {
      let (mut sig, mut did) = Default::default();
      let path = MizPath::new(art.as_str());
      if path.read_did(false, &mut sig, &mut did)? {
        let len = self.sig.sig.len();
        let mut rename = self.sig.rename(&sig, Some(ctx));
        for mut id in did {
          id.visit(&mut rename);
          if rename.ok() {
            ids.push(id);
          }
        }
        self.sig.truncate(len);
      }
    }
    Ok(())
  }

  /// ProcessReductions
  pub fn accom_reduction_regs(
    &mut self, ctx: &Constructors, reds: &mut Vec<Reduction>,
  ) -> io::Result<()> {
    for &(_, art) in &self.dirs.0[DirectiveKind::Registrations] {
      let (mut sig, mut drd) = Default::default();
      let path = MizPath::new(art.as_str());
      if path.read_drd(false, &mut sig, &mut drd)? {
        let len = self.sig.sig.len();
        let mut rename = self.sig.rename(&sig, Some(ctx));
        for mut red in drd {
          red.visit(&mut rename);
          if rename.ok() {
            reds.push(red);
          }
        }
        self.sig.truncate(len);
      }
    }
    Ok(())
  }

  /// ProcessProperties
  pub fn accom_properties(
    &mut self, ctx: &Constructors, props: &mut Vec<Property>,
  ) -> io::Result<()> {
    for &(_, art) in &self.dirs.0[DirectiveKind::Registrations] {
      let (mut sig, mut dpr) = Default::default();
      let path = MizPath::new(art.as_str());
      if path.read_dpr(false, &mut sig, &mut dpr)? {
        let len = self.sig.sig.len();
        let mut rename = self.sig.rename(&sig, Some(ctx));
        for mut prop in dpr {
          prop.visit(&mut rename);
          if rename.ok() {
            props.push(prop);
          }
        }
        self.sig.truncate(len);
      }
    }
    Ok(())
  }

  /// ProcessDefinitions
  pub fn accom_definitions(
    &mut self, ctx: &Constructors, kind: DirectiveKind, defs: &mut Vec<Definiens>,
  ) -> io::Result<()> {
    for &(_, art) in &self.dirs.0[kind] {
      let (mut sig, mut def) = Default::default();
      let path = MizPath::new(art.as_str());
      if path.read_def(false, &mut sig, &mut def)? {
        let len = self.sig.sig.len();
        let mut rename = self.sig.rename(&sig, Some(ctx));
        for mut def in def {
          def.visit(&mut rename);
          if rename.ok() {
            defs.push(def);
          }
        }
        self.sig.truncate(len);
      }
    }
    Ok(())
  }

  /// ProcessTheorems
  pub fn accom_theorems(&mut self, ctx: &Constructors, libs: &mut Libraries) -> io::Result<()> {
    for &(_, art) in &self.dirs.0[DirectiveKind::Theorems] {
      let mut thms = Default::default();
      if MizPath::new(art.as_str()).read_the(false, &mut thms)? {
        let len = self.sig.sig.len();
        let mut rename = self.sig.rename(&thms.sig, Some(ctx));
        let (mut thm_nr, mut def_nr) = <(ThmId, DefId)>::default();
        let lib_nr = self.articles.get(&art).copied();
        for mut thm in thms.thm {
          match thm.kind {
            TheoremKind::Def(_) | TheoremKind::CanceledDef => {
              let def_nr = def_nr.fresh();
              thm.stmt.visit(&mut rename);
              if rename.ok() {
                libs.def.insert((lib_nr.unwrap(), def_nr), thm.stmt);
              }
            }
            TheoremKind::Thm | TheoremKind::CanceledThm => {
              let thm_nr = thm_nr.fresh();
              thm.stmt.visit(&mut rename);
              if rename.ok() {
                libs.thm.insert((lib_nr.unwrap(), thm_nr), thm.stmt);
              }
            }
          }
        }
        self.sig.truncate(len);
      }
    }
    Ok(())
  }

  /// ProcessSchemes
  pub fn accom_schemes(&mut self, ctx: &Constructors, libs: &mut Libraries) -> io::Result<()> {
    for &(_, art) in &self.dirs.0[DirectiveKind::Schemes] {
      let mut schs = Default::default();
      if MizPath::new(art.as_str()).read_sch(false, &mut schs)? {
        let len = self.sig.sig.len();
        let mut rename = self.sig.rename(&schs.sig, Some(ctx));
        let mut sch_nr = SchId::default();
        let lib_nr = self.articles.get(&art).copied();
        for sch in schs.sch {
          let sch_nr = sch_nr.fresh();
          if let Some(mut sch) = sch {
            sch.visit(&mut rename);
            if rename.ok() {
              libs.sch.insert((lib_nr.unwrap(), sch_nr), sch);
            }
          }
        }
        self.sig.truncate(len);
      }
    }
    Ok(())
  }
}
