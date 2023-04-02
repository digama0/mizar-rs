use crate::analyze::Analyzer;
use crate::parser::MaybeMut;
use crate::types::*;
use crate::{Assignment, Global, LocalContext, OnVarMut, VisitMut};
use enum_map::EnumMap;
use itertools::Itertools;
use std::fmt::Debug;

const DOUBLE_CHECK: bool = false;

#[derive(Default)]
pub struct Exporter {
  pub notations_base: EnumMap<PatternKindClass, u32>,
  pub constrs_base: ConstructorsBase,
  pub clusters_base: ClustersBase,
  pub definitions_base: u32,
  pub identify_base: u32,
  pub reductions_base: u32,
  pub properties_base: u32,
  pub theorems: Vec<Theorem>,
  pub schemes: Vec<Option<SchId>>,
}

fn assert_eq_iter<T: Debug + PartialEq<U>, U: Debug>(
  header: &str, mut it1: impl Iterator<Item = T> + Clone, mut it2: impl Iterator<Item = U> + Clone,
) {
  if !it1.clone().eq(it2.clone()) {
    eprintln!("failure in {header}:");
    for i in 0.. {
      match (it1.next(), it2.next()) {
        (None, None) => break,
        (Some(x1), Some(x2)) if x1 == x2 => eprintln!("{i}: both: {x1:?}"),
        (a, b) => eprintln!("{i}: mismatch:\n{a:?}\n{b:?}\n"),
      }
    }
    panic!("failure in {header}");
  }
}

struct ExportPrep<'a> {
  ctx: Option<&'a Constructors>,
  lc: &'a LocalContext,
  ic: &'a IdxVec<InferId, Assignment>,
  depth: u32,
}
impl VisitMut for ExportPrep<'_> {
  fn push_bound(&mut self, _: &mut Type) { self.depth += 1 }
  fn pop_bound(&mut self, n: u32) { self.depth -= n }
  fn visit_term(&mut self, tm: &mut Term) {
    if let Term::Infer(nr) = *tm {
      *tm = self.ic[nr].def.visit_cloned(&mut OnVarMut(|v| *v += self.depth));
    }
    self.super_visit_term(tm);
  }
  fn visit_formula(&mut self, f: &mut Formula) {
    if let Formula::FlexAnd { nat, le, terms, scope } = f {
      *f = Global::into_legacy_flex_and(nat, *le, terms, scope, self.depth)
    }
    self.super_visit_formula(f)
  }
  fn visit_attrs(&mut self, attrs: &mut Attrs) {
    attrs.reinsert_all(self.ctx, self.lc, true, |attr| self.visit_terms(&mut attr.args))
  }
  fn visit_attr_pair(&mut self, attrs: &mut (Attrs, Attrs)) {
    self.visit_attrs(&mut attrs.0);
    attrs.1.clone_from(&attrs.0);
  }
}

impl<'a> ExportPrep<'a> {
  fn with_ctx(&mut self, ctx: Option<&Constructors>, f: impl FnOnce(&mut ExportPrep<'_>)) {
    f(&mut ExportPrep { ctx, ..*self });
  }
}

fn mark_formats<T>(
  vocs: &Vocabularies, marked_vocs: &mut Vocabularies, fmts: &mut [T],
  get: impl Fn(&mut T) -> &mut Format,
) {
  let mut trans = EnumMap::<_, Vec<_>>::default();
  let (mut hi, mut new) = <(SymbolsBase, SymbolsBase)>::default();
  for (_, (art, counts)) in vocs.0.iter().enumerate() {
    let lo = hi;
    hi += counts;
    let used = fmts.iter_mut().any(|fmt| {
      let mut used = false;
      get(fmt).visit(|k, sym| used |= (lo.0[k]..hi.0[k]).contains(&sym));
      used
    });
    if used {
      marked_vocs.0.push((*art, *counts));
      for (kind, &count) in &counts.0 {
        trans[kind].extend((0..count).map(|i| Some(i + new.0[kind])))
      }
      new += counts;
    } else {
      for (kind, &count) in &counts.0 {
        trans[kind].extend((0..count).map(|_| None))
      }
    }
  }
  for fmt in fmts {
    get(fmt).visit_mut(|k, sym| *sym = trans[k][*sym as usize].unwrap());
  }
}

#[derive(Debug)]
struct MarkConstr<'a> {
  /// Article, plus the constructor counts *excluding* this article.
  /// The current article may be in the list, in which case it is at the end.
  accum: &'a [(Article, ConstructorsBase)],
  /// The total constructor counts
  base: &'a ConstructorsBase,
  /// This is a parallel array, where `used[i]` corresponds to `accum[i]`,
  /// and `used.last()` is true if constructors from the current article are used.
  /// (Because this always contains an entry for the current article it may either
  /// be the same length or one longer than accum.)
  used: Vec<bool>,
}

impl<'a> MarkConstr<'a> {
  fn new(accum: &'a [(Article, ConstructorsBase)], base: &'a ConstructorsBase, n: usize) -> Self {
    Self { accum, base, used: vec![false; n + 1] }
  }

  fn mark(&mut self, n: u32, key: impl Fn(&ConstructorsBase) -> u32) {
    if n < key(self.base) {
      self.used[self.accum[1..].partition_point(|(_, base)| key(base) <= n)] = true
    }
  }

  fn closure(&mut self, constrs: &mut Constructors) {
    let mut base = *self.base;
    // We skip the first two because the first is HIDDEN (which is always used)
    // and the second step can't have any effect
    for (i, (_, lo)) in self.accum.iter().enumerate().skip(2).rev() {
      if self.used[i] {
        constrs.visit_range(self, lo..&base)
      }
      base = *lo
    }
    self.used[0] = true
  }

  fn apply(&self) -> ApplyMarkConstr {
    let (mut offset, mut base) = Default::default();
    let mut apply = ApplyMarkConstr::default();
    let mut prev = true;
    for (accum, &mark) in self.accum.iter().map(|p| &p.1).chain([self.base]).zip(&self.used).skip(1)
    {
      if prev != mark {
        if mark {
          offset += *accum - base;
          apply.0.push((base, offset));
        } else {
          base = *accum;
        }
        prev = mark
      }
    }
    apply
  }

  fn apply_with(&self, f: impl FnOnce(&mut ApplyMarkConstr)) {
    let mut apply = self.apply();
    if !apply.0.is_empty() {
      f(&mut apply)
    }
  }

  fn filtered<T: Copy>(&self, ts: &[T]) -> Vec<T> {
    ts.iter().zip(&self.used).filter(|p| *p.1).map(|p| *p.0).collect_vec()
  }
}

impl VisitMut for MarkConstr<'_> {
  fn visit_mode_id(&mut self, n: &mut ModeId) { self.mark(n.0, |b| b.mode) }
  fn visit_struct_id(&mut self, n: &mut StructId) { self.mark(n.0, |b| b.struct_mode) }
  fn visit_attr_id(&mut self, n: &mut AttrId) { self.mark(n.0, |b| b.attribute) }
  fn visit_pred_id(&mut self, n: &mut PredId) { self.mark(n.0, |b| b.predicate) }
  fn visit_func_id(&mut self, n: &mut FuncId) { self.mark(n.0, |b| b.functor) }
  fn visit_sel_id(&mut self, n: &mut SelId) { self.mark(n.0, |b| b.selector) }
  fn visit_aggr_id(&mut self, n: &mut AggrId) { self.mark(n.0, |b| b.aggregate) }
}

#[derive(Default, Debug)]
struct ApplyMarkConstr(Vec<(ConstructorsBase, ConstructorsBase)>);
impl ApplyMarkConstr {
  fn apply(&mut self, n: &mut u32, key: impl Fn(&ConstructorsBase) -> u32) {
    if let Some(i) = self.0.partition_point(|(base, _)| key(base) <= *n).checked_sub(1) {
      *n -= key(&self.0[i].1)
    }
  }
}

impl VisitMut for ApplyMarkConstr {
  const MODIFY_IDS: bool = true;
  fn visit_mode_id(&mut self, n: &mut ModeId) { self.apply(&mut n.0, |b| b.mode) }
  fn visit_struct_id(&mut self, n: &mut StructId) { self.apply(&mut n.0, |b| b.struct_mode) }
  fn visit_attr_id(&mut self, n: &mut AttrId) { self.apply(&mut n.0, |b| b.attribute) }
  fn visit_pred_id(&mut self, n: &mut PredId) { self.apply(&mut n.0, |b| b.predicate) }
  fn visit_func_id(&mut self, n: &mut FuncId) { self.apply(&mut n.0, |b| b.functor) }
  fn visit_sel_id(&mut self, n: &mut SelId) { self.apply(&mut n.0, |b| b.selector) }
  fn visit_aggr_id(&mut self, n: &mut AggrId) { self.apply(&mut n.0, |b| b.aggregate) }
}

impl AccumConstructors {
  fn mark<T: for<'a> Visitable<MarkConstr<'a>> + Visitable<ApplyMarkConstr>>(
    &mut self, t: &mut T, n: usize, arts: &[Article],
  ) -> Vec<Article> {
    let mut marks = MarkConstr::new(&self.accum, &self.base, n);
    t.visit(&mut marks);
    marks.closure(&mut self.constrs);
    marks.apply_with(|v| t.visit(v));
    marks.filtered(arts)
  }
}

impl Analyzer<'_> {
  pub fn export(&mut self) {
    let ep = &mut ExportPrep {
      ctx: Some(&self.r.g.constrs),
      lc: &self.r.lc,
      ic: &self.r.lc.infer_const.borrow().vec,
      depth: 0,
    };
    let new_prel = !self.g.cfg.overwrite_prel;

    // loading .sgl
    let mut arts2 = vec![];
    if let Some(accom) = &self.accom {
      arts2.extend(accom.sig.sig.0.iter().map(|p| p.0));
    } else {
      self.path.read_sgl(&mut arts2).unwrap()
    }
    let arts1 = if self.g.constrs.since(&self.export.constrs_base).is_empty() {
      &*arts2
    } else {
      let n = arts2.len();
      arts2.push(self.article);
      &arts2[..n]
    };

    // loading .vcl
    let (mut vocs1, mut aco) = <(_, AccumConstructors)>::default();
    self.path.read_vcl(&mut vocs1).unwrap();

    // loading .aco
    if let Some(accom) = &mut self.r.accom {
      aco.accum = std::mem::take(&mut accom.sig.sig.0);
      aco.base = accom.sig.base;
      aco.constrs.extend(&self.g.constrs.upto(&aco.base));
      aco.constrs.visit(ep);
    } else {
      self.path.read_aco(&mut aco).unwrap();
    }
    assert_eq!(self.export.constrs_base, aco.constrs.len());
    assert_eq!(arts1.len(), aco.accum.len());

    // validating .dfr
    {
      let format_base = {
        let mut f = Default::default();
        self.path.read_formats("frm", &mut f).unwrap();
        f.formats.len()
      };
      let dfr1 = &self.lc.formatter.formats.formats.0[format_base..];
      let (mut vocs2, mut dfr2) = Default::default();
      let nonempty = !dfr1.is_empty();
      if self.g.cfg.verify_export {
        assert_eq!(nonempty, self.path.read_dfr(false, &mut vocs2, &mut dfr2).unwrap());
      }
      if nonempty {
        let mut marked_vocs = Vocabularies::default();
        let mut dfr1 = dfr1.to_owned();
        mark_formats(&vocs1, &mut marked_vocs, &mut dfr1, |x| x);
        if self.g.cfg.verify_export {
          assert_eq!(marked_vocs, vocs2);
          assert_eq!(dfr1, dfr2.0);
        }
        if self.g.cfg.xml_export {
          self.path.write_dfr(new_prel, &marked_vocs, &dfr1);
          if DOUBLE_CHECK {
            let (mut vocs3, mut dfr3) = Default::default();
            self.path.read_dfr(new_prel, &mut vocs3, &mut dfr3).unwrap();
            assert_eq!(marked_vocs, vocs3);
            assert_eq!(dfr1, dfr3.0);
          }
        }
      }
    }

    // validating .dco (also push current article to aco)
    {
      let mut dco2 = Default::default();
      let since1 = self.g.constrs.since(&self.export.constrs_base);
      let nonempty = !since1.is_empty();
      if self.g.cfg.verify_export {
        assert_eq!(nonempty, self.path.read_dco(false, &mut dco2, true).unwrap())
      }
      let mut constrs1 = since1.to_owned();
      constrs1.visit(ep);
      assert_eq!(!since1.is_empty(), nonempty);
      if nonempty {
        aco.constrs.append(&mut constrs1.clone());
        let mut marks = MarkConstr::new(&aco.accum, &aco.base, arts1.len());
        *marks.used.last_mut().unwrap() = true;
        constrs1.visit(&mut marks);
        marks.closure(&mut aco.constrs);
        marks.apply_with(|v| constrs1.visit(v));
        let dco1 =
          DepConstructors { sig: marks.filtered(arts1), counts: constrs1.len(), constrs: constrs1 };
        if self.g.cfg.verify_export {
          assert_eq!(dco1.sig, dco2.sig);
          assert_eq!(dco1.counts, dco2.counts);
          macro_rules! process { ($($field:ident),*) => {$(
            assert_eq_iter(concat!("constrs.", stringify!($field)),
              dco1.constrs.$field.0.iter(), dco2.constrs.$field.0.iter());
          )*}}
          process!(mode, struct_mode, attribute, predicate, functor, selector, aggregate);
        }
        if self.g.cfg.xml_export {
          self.path.write_dco(new_prel, &dco1);
          if DOUBLE_CHECK {
            let mut dco3 = Default::default();
            self.path.read_dco(new_prel, &mut dco3, true).unwrap();
            assert_eq!(dco1, dco3);
          }
        }
        aco.accum.push((self.article, aco.base));
        aco.base = self.g.constrs.len();
      }
    }

    // validating .dno
    {
      let mut pats1 = (self.notations.iter())
        .flat_map(|(i, nota)| &nota[self.export.notations_base[i] as usize..])
        .map(|pat| {
          let Pattern { kind, fmt, primary, visible, pos } = pat.visit_cloned(ep);
          Pattern { kind, fmt: self.lc.formatter.formats.formats[fmt], primary, visible, pos }
        })
        .collect_vec();
      let mut dno2 = Default::default();
      let nonempty = !pats1.is_empty();
      if self.g.cfg.verify_export {
        assert_eq!(nonempty, self.path.read_dno(false, &mut dno2).unwrap());
      }
      if nonempty {
        let mut marked_vocs = Vocabularies::default();
        mark_formats(&vocs1, &mut marked_vocs, &mut pats1, |p| &mut p.fmt);
        let mut marks = MarkConstr::new(&aco.accum, &aco.base, arts1.len());
        pats1.iter_mut().for_each(|p| p.visit(&mut marks));
        marks.closure(&mut aco.constrs);
        marks.apply_with(|v| pats1.iter_mut().for_each(|p| p.visit(v)));
        let dno1 = DepNotation { sig: marks.filtered(&arts2), vocs: marked_vocs, pats: pats1 };
        if self.g.cfg.verify_export {
          assert_eq!(dno1.sig, dno2.sig);
          assert_eq!(dno1.vocs, dno2.vocs);
          assert_eq_iter("notations", dno1.pats.iter(), dno2.pats.iter());
        }
        if self.g.cfg.xml_export {
          self.path.write_dno(new_prel, &dno1);
          if DOUBLE_CHECK {
            let mut dno3 = Default::default();
            self.path.read_dno(new_prel, &mut dno3).unwrap();
            assert_eq!(dno1, dno3);
          }
        }
      }
    }

    // validating .dcl
    {
      let mut dcl2 = Default::default();
      let since1 = self.g.clusters.since(&self.export.clusters_base);
      let nonempty = !since1.is_empty();
      if self.g.cfg.verify_export {
        assert_eq!(self.path.read_dcl(false, &mut dcl2).unwrap(), nonempty);
      }
      if nonempty {
        let mut cl1 = since1.to_owned();
        cl1.visit(ep);
        let dcl1 = DepClusters { sig: aco.mark(&mut cl1, arts1.len(), &arts2), cl: cl1 };
        if self.g.cfg.verify_export {
          ep.with_ctx(None, |ep| dcl2.cl.visit(ep));
          assert_eq!(dcl1.sig, dcl2.sig);
          macro_rules! process { ($($field:ident),*) => {$({
            assert_eq_iter(concat!("clusters.", stringify!($field)),
              dcl1.cl.$field.iter(), dcl2.cl.$field.iter());
          })*}}
          process!(registered, functor, conditional);
        }
        if self.g.cfg.xml_export {
          self.path.write_dcl(new_prel, &dcl1);
          if DOUBLE_CHECK {
            let mut dcl3 = Default::default();
            self.path.read_dcl(new_prel, &mut dcl3).unwrap();
            assert_eq!(dcl1, dcl3);
          }
        }
      }
    }

    // validating .def
    {
      let (mut sig, mut def2) = Default::default();
      let def1 = &self.definitions[self.export.definitions_base as usize..];
      let nonempty = !def1.is_empty();
      if self.g.cfg.verify_export {
        let nonempty2 = self
          .path
          .read_definitions(MaybeMut::None, false, "def", Some(&mut sig), &mut def2)
          .unwrap();
        assert_eq!(nonempty, nonempty2);
      }
      if nonempty {
        let mut def1 = def1.to_owned();
        def1.visit(ep);
        let sig1 = aco.mark(&mut def1, arts1.len(), &arts2);
        if self.g.cfg.verify_export {
          ep.with_ctx(None, |ep| def2.visit(ep));
          assert_eq!(sig1, sig);
          assert_eq_iter("definitions", def1.iter(), def2.iter());
        }
        if self.g.cfg.xml_export {
          self.path.write_def(new_prel, &sig1, &def1);
          if DOUBLE_CHECK {
            let (mut sig3, mut def3) = Default::default();
            (self.path)
              .read_definitions(MaybeMut::None, new_prel, "def", Some(&mut sig3), &mut def3)
              .unwrap();
            ep.with_ctx(None, |ep| def3.visit(ep));
            assert_eq!(sig1, sig3);
            assert_eq!(def1, def3);
          }
        }
      }
    }

    // validating .did
    {
      let (mut sig, mut did2) = Default::default();
      let did1 = &self.identify[self.export.identify_base as usize..];
      let nonempty = !did1.is_empty();
      if self.g.cfg.verify_export {
        let nonempty2 = (self.path)
          .read_identify_regs(MaybeMut::None, false, "did", Some(&mut sig), &mut did2)
          .unwrap();
        assert_eq!(nonempty, nonempty2);
      }
      if nonempty {
        let mut did1 = did1.to_owned();
        did1.visit(ep);
        let sig1 = aco.mark(&mut did1, arts1.len(), &arts2);
        if self.g.cfg.verify_export {
          ep.with_ctx(None, |ep| did2.visit(ep));
          assert_eq!(sig1, sig);
          assert_eq_iter("identities", did1.iter(), did2.iter());
        }
        if self.g.cfg.xml_export {
          self.path.write_did(new_prel, &sig1, &did1);
          if DOUBLE_CHECK {
            let (mut sig3, mut did3) = Default::default();
            (self.path)
              .read_identify_regs(MaybeMut::None, new_prel, "did", Some(&mut sig3), &mut did3)
              .unwrap();
            ep.with_ctx(None, |ep| did3.visit(ep));
            assert_eq!(sig1, sig3);
            assert_eq!(did1, did3);
          }
        }
      }
    }

    // validating .drd
    {
      let (mut sig, mut drd2) = Default::default();
      let drd1 = &self.reductions[self.export.reductions_base as usize..];
      let nonempty = !drd1.is_empty();
      if self.g.cfg.verify_export {
        let nonempty2 = (self.path)
          .read_reduction_regs(MaybeMut::None, false, "drd", Some(&mut sig), &mut drd2)
          .unwrap();
        assert_eq!(nonempty, nonempty2);
      }
      if nonempty {
        let mut drd1 = drd1.to_owned();
        drd1.visit(ep);
        let sig1 = aco.mark(&mut drd1, arts1.len(), &arts2);
        if self.g.cfg.verify_export {
          ep.with_ctx(None, |ep| drd2.visit(ep));
          assert_eq!(sig1, sig);
          assert_eq_iter("reductions", drd1.iter(), drd2.iter());
        }
        if self.g.cfg.xml_export {
          self.path.write_drd(new_prel, &sig1, &drd1);
          if DOUBLE_CHECK {
            let (mut sig3, mut drd3) = Default::default();
            (self.path)
              .read_reduction_regs(MaybeMut::None, new_prel, "drd", Some(&mut sig3), &mut drd3)
              .unwrap();
            ep.with_ctx(None, |ep| drd3.visit(ep));
            assert_eq!(sig1, sig3);
            assert_eq!(drd1, drd3);
          }
        }
      }
    }

    // validating .dpr
    {
      let (mut sig, mut dpr2) = Default::default();
      let dpr1 = &self.properties[self.export.properties_base as usize..];
      let nonempty = !dpr1.is_empty();
      if self.g.cfg.verify_export {
        let nonempty2 = (self.path)
          .read_properties(MaybeMut::None, false, "dpr", Some(&mut sig), &mut dpr2)
          .unwrap();
        assert_eq!(nonempty, nonempty2);
        dpr2.visit(ep);
      }
      if nonempty {
        let mut dpr1 = dpr1.to_owned();
        dpr1.visit(ep);
        let sig1 = aco.mark(&mut dpr1, arts1.len(), &arts2);
        if self.g.cfg.verify_export {
          ep.with_ctx(None, |ep| dpr2.visit(ep));
          assert_eq!(sig1, sig);
          assert_eq_iter("properties", dpr1.iter(), dpr2.iter());
        }
        if self.g.cfg.xml_export {
          self.path.write_dpr(new_prel, &sig1, &dpr1);
          if DOUBLE_CHECK {
            let (mut sig3, mut dpr3) = Default::default();
            (self.path)
              .read_properties(MaybeMut::None, new_prel, "dpr", Some(&mut sig3), &mut dpr3)
              .unwrap();
            ep.with_ctx(None, |ep| dpr3.visit(ep));
            assert_eq!(sig1, sig3);
            assert_eq!(dpr1, dpr3);
          }
        }
      }
    }

    // validating .the
    {
      let mut thms2 = Default::default();
      let mut thms1 = std::mem::take(&mut self.export.theorems);
      let nonempty = !thms1.is_empty();
      if self.g.cfg.verify_export {
        assert_eq!(nonempty, self.path.read_the(false, &mut thms2).unwrap());
      }
      if nonempty {
        thms1.visit(ep);
        let thms1 = DepTheorems { sig: aco.mark(&mut thms1, arts1.len(), &arts2), thm: thms1 };
        if self.g.cfg.verify_export {
          ep.with_ctx(None, |ep| thms2.thm.visit(ep));
          assert_eq!(thms1.sig, thms2.sig);
          assert_eq_iter("theorems", thms1.thm.iter(), thms2.thm.iter());
        }
        if self.g.cfg.xml_export {
          self.path.write_the(new_prel, &thms1);
          if DOUBLE_CHECK {
            let mut thms3 = Default::default();
            self.path.read_the(new_prel, &mut thms3).unwrap();
            ep.with_ctx(None, |ep| thms3.thm.visit(ep));
            assert_eq!(thms1, thms3);
          }
        }
      }
    }

    // validating .sch
    {
      let mut schs2 = Default::default();
      let nonempty = !self.export.schemes.is_empty();
      if self.g.cfg.verify_export {
        assert_eq!(nonempty, self.path.read_sch(false, &mut schs2).unwrap());
      }
      if nonempty {
        let mut schs1 = (self.export.schemes.iter())
          .map(|i| i.map(|i| self.libs.sch[&(ArticleId::SELF, i)].visit_cloned(ep)))
          .collect_vec();
        let schs1 = DepSchemes { sig: aco.mark(&mut schs1, arts1.len(), &arts2), sch: schs1 };
        if self.g.cfg.verify_export {
          ep.with_ctx(None, |ep| schs2.sch.visit(ep));
          assert_eq!(schs1.sig, schs2.sig);
          assert_eq_iter("schemes", schs1.sch.iter(), schs2.sch.iter());
        }
        if self.g.cfg.xml_export {
          self.path.write_sch(new_prel, &schs1);
          if DOUBLE_CHECK {
            let mut schs3 = Default::default();
            self.path.read_sch(new_prel, &mut schs3).unwrap();
            ep.with_ctx(None, |ep| schs3.sch.visit(ep));
            assert_eq!(schs1, schs3);
          }
        }
      }
    }
  }
}
