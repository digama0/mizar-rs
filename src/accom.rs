use crate::types::*;
use crate::{mk_id, MizPath, VisitMut};
use std::collections::{BTreeMap, HashMap};
use std::io;

mk_id! {
  VocId(u32),
  SigId(u32),
}

#[derive(Default)]
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
      assert_eq!(val2, val);
      i
    } else {
      self.push(art, val)
    }
  }
}

#[derive(Default)]
pub struct SigBuilder {
  pub sig: IdxVec<SigId, (Article, ConstructorsBase)>,
  pub base: ConstructorsBase,
}

impl SigBuilder {
  fn push(&mut self, constrs: &mut Constructors, art: Article) -> SigId {
    let mut dco = Default::default();
    assert!(MizPath::new(art.as_str()).read_dco(false, &mut dco).unwrap());
    self.push_from(constrs, art, &mut dco)
  }

  fn push_from(
    &mut self, constrs: &mut Constructors, art: Article, dco: &mut DepConstructors,
  ) -> SigId {
    let mut rename = RenameConstr::default();
    for &art2 in &dco.sig {
      let i = self.get(art2);
      rename.push(self, i);
    }
    dco.constrs.visit(&mut rename);
    constrs.append(&mut dco.constrs);
    let i = self.sig.push((art, self.base));
    self.base += dco.counts;
    i
  }

  fn get_or_push(&mut self, constrs: &mut Constructors, art: Article) -> SigId {
    let id = self.sig.enum_iter().find(|p| p.1 .0 == art).map(|p| p.0);
    id.unwrap_or_else(|| self.push(constrs, art))
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

  fn rename(&self, sig: &[Article]) -> RenameConstr {
    let mut rename = RenameConstr::default();
    sig.iter().for_each(|&art| rename.push(self, self.get(art)));
    rename
  }
}

#[derive(Default)]
pub struct Accomodator {
  pub dirs: Directives,
  pub sig: SigBuilder,
  pub articles: HashMap<Article, ArticleId>,
}

#[derive(Default)]
struct RenameSymbol {
  trans: Vec<(SymbolsBase, SymbolsBase)>,
  base: SymbolsBase,
}
impl RenameSymbol {
  fn push(&mut self, val: &SymbolsBase, tgt: &SymbolsBase) {
    self.trans.push((self.base, *tgt));
    self.base += val;
  }
  fn apply(&mut self, k: SymbolKindClass, n: &mut u32) {
    let (from, to) = &self.trans[self.trans.partition_point(|(base, _)| base.0[k] <= *n) - 1];
    *n = *n - from.0[k] + to.0[k]
  }
}

#[derive(Default)]
struct RenameConstr {
  trans: Vec<(ConstructorsBase, ConstructorsBase)>,
  base: ConstructorsBase,
}
impl RenameConstr {
  fn push(&mut self, sig: &SigBuilder, i: SigId) {
    let lo = self.base;
    self.base += *sig.hi(i) - sig.sig[i].1;
    self.trans.push((lo, sig.sig[i].1))
  }

  fn apply(&mut self, n: &mut u32, key: impl Fn(&ConstructorsBase) -> u32) {
    let (from, to) = &self.trans[self.trans.partition_point(|(base, _)| key(base) <= *n) - 1];
    *n = *n - key(from) + key(to)
  }
}

impl VisitMut for RenameConstr {
  fn visit_mode_id(&mut self, n: &mut ModeId) { self.apply(&mut n.0, |b| b.mode) }
  fn visit_struct_id(&mut self, n: &mut StructId) { self.apply(&mut n.0, |b| b.struct_mode) }
  fn visit_attr_id(&mut self, n: &mut AttrId) { self.apply(&mut n.0, |b| b.attribute) }
  fn visit_pred_id(&mut self, n: &mut PredId) { self.apply(&mut n.0, |b| b.predicate) }
  fn visit_func_id(&mut self, n: &mut FuncId) { self.apply(&mut n.0, |b| b.functor) }
  fn visit_sel_id(&mut self, n: &mut SelId) { self.apply(&mut n.0, |b| b.selector) }
  fn visit_aggr_id(&mut self, n: &mut AggrId) { self.apply(&mut n.0, |b| b.aggregate) }
}

impl Accomodator {
  pub fn init_symbols(&mut self, symbols: &[(SymbolKind, String)]) {
    for (kind, name) in symbols {
      if let SymbolKind::Article(n) = *kind {
        assert!(self.articles.insert(Article::from_upper(name.as_bytes()), n).is_none());
      }
    }
  }

  /// ProcessConstructors
  pub fn accom_constructors(&mut self, constrs: &mut Constructors) -> io::Result<()> {
    for &(_, art) in &self.dirs.0[DirectiveKind::Constructors] {
      let mut dco = Default::default();
      assert!(MizPath::new(art.as_str()).read_dco(false, &mut dco).unwrap());
      for &art2 in &dco.sig {
        self.sig.get_or_push(constrs, art2);
      }
      if !self.sig.sig.0.iter().any(|p| p.0 == art) {
        self.sig.push_from(constrs, art, &mut dco);
      }
    }
    Ok(())
  }

  /// ProcessRequirements
  pub fn accom_requirements(
    &self, ctx: &Constructors, idx: &mut RequirementIndexes,
  ) -> io::Result<()> {
    for &(_, art) in &self.dirs.0[DirectiveKind::Requirements] {
      let mut dre = Default::default();
      MizPath::new(art.as_str()).read_dre(&mut dre)?;
      let mut rename = self.sig.rename(&dre.sig);
      for DepRequirement { req, mut kind } in dre.reqs {
        kind.visit(&mut rename);
        assert!(kind.lt(&ctx.len()), "inaccessible requirement");
        idx.set(req, kind);
      }
    }
    Ok(())
  }

  /// ProcessClusters
  pub fn accom_clusters(&self, ctx: &Constructors, clusters: &mut Clusters) -> io::Result<()> {
    for &(_, art) in &self.dirs.0[DirectiveKind::Registrations] {
      let mut dcl = Default::default();
      if MizPath::new(art.as_str()).read_dcl(false, &mut dcl)? {
        dcl.cl.visit(&mut self.sig.rename(&dcl.sig));
        clusters.append(ctx, &mut dcl.cl);
      }
    }
    Ok(())
  }

  /// ProcessNotations
  pub fn accom_notations(
    &self, fmt_map: &mut BTreeMap<Format, FormatId>, mut fmts: Option<&mut Formats>,
    pats: &mut Vec<Pattern>,
  ) -> io::Result<()> {
    let mut dict = VocBuilder::default();
    for &(_, art) in &self.dirs.0[DirectiveKind::Notations] {
      let mut dno = Default::default();
      assert!(MizPath::new(art.as_str()).read_dno(false, &mut dno)?);
      let mut s_rename = RenameSymbol::default();
      if fmts.is_some() {
        for &(art, ref val) in &dno.vocs.0 {
          let i = dict.get_or_push(art, val);
          s_rename.push(val, &dict.voc[i].1);
        }
      }
      let mut rename = self.sig.rename(&dno.sig);
      for (mut fmt, mut pat) in dno.pats {
        pat.visit(&mut rename);
        if let Some(fmts) = fmts.as_deref_mut() {
          fmt.visit_mut(|k, c| s_rename.apply(k, c));
          pat.fmt = *fmt_map.entry(fmt).or_insert_with(|| fmts.formats.push(fmt));
        }
        pats.push(pat)
      }
    }
    Ok(())
  }

  /// ProcessIdentify
  pub fn accom_identify_regs(
    &self, ctx: &Constructors, ids: &mut Vec<IdentifyFunc>,
  ) -> io::Result<()> {
    for &(_, art) in &self.dirs.0[DirectiveKind::Registrations] {
      let (mut sig, mut did) = Default::default();
      let path = MizPath::new(art.as_str());
      if path.read_identify_regs(ctx, false, "did", Some(&mut sig), &mut did)? {
        did.visit(&mut self.sig.rename(&sig));
        ids.append(&mut did);
      }
    }
    Ok(())
  }

  /// ProcessReductions
  pub fn accom_reduction_regs(
    &self, ctx: &Constructors, reds: &mut Vec<Reduction>,
  ) -> io::Result<()> {
    for &(_, art) in &self.dirs.0[DirectiveKind::Registrations] {
      let (mut sig, mut drd) = Default::default();
      let path = MizPath::new(art.as_str());
      if path.read_reduction_regs(ctx, false, "drd", Some(&mut sig), &mut drd)? {
        drd.visit(&mut self.sig.rename(&sig));
        reds.append(&mut drd);
      }
    }
    Ok(())
  }

  /// ProcessProperties
  pub fn accom_properties(&self, ctx: &Constructors, props: &mut Vec<Property>) -> io::Result<()> {
    for &(_, art) in &self.dirs.0[DirectiveKind::Registrations] {
      let (mut sig, mut dpr) = Default::default();
      if MizPath::new(art.as_str()).read_properties(ctx, false, "dpr", Some(&mut sig), &mut dpr)? {
        dpr.visit(&mut self.sig.rename(&sig));
        props.append(&mut dpr);
      }
    }
    Ok(())
  }

  /// ProcessDefinitions
  pub fn accom_definitions(
    &self, ctx: &Constructors, kind: DirectiveKind, defs: &mut Vec<Definiens>,
  ) -> io::Result<()> {
    for &(_, art) in &self.dirs.0[kind] {
      let (mut sig, mut def) = Default::default();
      if MizPath::new(art.as_str()).read_definitions(ctx, false, "def", Some(&mut sig), &mut def)? {
        def.visit(&mut self.sig.rename(&sig));
        defs.append(&mut def);
      }
    }
    Ok(())
  }

  /// ProcessTheorems
  pub fn accom_theorems(&self, libs: &mut Libraries) -> io::Result<()> {
    for &(_, art) in &self.dirs.0[DirectiveKind::Theorems] {
      let mut thms = Default::default();
      if MizPath::new(art.as_str()).read_the(false, &mut thms)? {
        let mut rename = self.sig.rename(&thms.sig);
        let (mut thm_nr, mut def_nr) = <(ThmId, DefId)>::default();
        let lib_nr = self.articles.get(&art).copied();
        for mut thm in thms.thm {
          match thm.kind {
            TheoremKind::CanceledThm => thm_nr.0 += 1,
            TheoremKind::CanceledDef => def_nr.0 += 1,
            TheoremKind::Def(_) => {
              thm.stmt.visit(&mut rename);
              libs.def.insert((lib_nr.unwrap(), def_nr.fresh()), thm.stmt);
            }
            TheoremKind::Thm => {
              thm.stmt.visit(&mut rename);
              libs.thm.insert((lib_nr.unwrap(), thm_nr.fresh()), thm.stmt);
            }
          }
        }
      }
    }
    Ok(())
  }

  /// ProcessSchemes
  pub fn accom_schemes(&self, libs: &mut Libraries) -> io::Result<()> {
    for &(_, art) in &self.dirs.0[DirectiveKind::Schemes] {
      let mut schs = Default::default();
      if MizPath::new(art.as_str()).read_sch(false, &mut schs)? {
        let mut rename = self.sig.rename(&schs.sig);
        let mut sch_nr = SchId::default();
        let lib_nr = self.articles.get(&art).copied();
        for sch in schs.sch {
          let sch_nr = sch_nr.fresh();
          if let Some(mut sch) = sch {
            sch.visit(&mut rename);
            libs.sch.insert((lib_nr.unwrap(), sch_nr), sch);
          }
        }
      }
    }
    Ok(())
  }
}
