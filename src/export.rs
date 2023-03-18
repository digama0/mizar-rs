use crate::analyze::Analyzer;
use crate::parser::MaybeMut;
use crate::types::{
  ArticleId, Attrs, ClustersBase, Constructors, ConstructorsBase, IdxVec, InferId,
  PatternKindClass, SchId, Term, Theorem, Type, Visitable,
};
use crate::{Assignment, LocalContext, OnVarMut, VisitMut};
use enum_map::EnumMap;
use itertools::Itertools;
use std::fmt::Debug;

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
  ctx: &'a Constructors,
  lc: &'a LocalContext,
  ic: &'a IdxVec<InferId, Assignment>,
  depth: u32,
}
impl VisitMut for ExportPrep<'_> {
  fn push_bound(&mut self, _: Option<&mut Type>) { self.depth += 1 }
  fn pop_bound(&mut self, n: u32) { self.depth -= n }
  fn visit_term(&mut self, tm: &mut Term) {
    if let Term::Infer(nr) = *tm {
      *tm = self.ic[nr].def.visit_cloned(&mut OnVarMut(|v| *v += self.depth));
    }
    self.super_visit_term(tm);
  }
  fn visit_attrs(&mut self, attrs: &mut Attrs) {
    attrs.reinsert_all(self.ctx, self.lc, true, |attr| self.visit_terms(&mut attr.args))
  }
  fn visit_attr_pair(&mut self, attrs: &mut (Attrs, Attrs)) {
    self.visit_attrs(&mut attrs.0);
    attrs.1.clone_from(&attrs.0);
  }
}

impl Analyzer<'_> {
  pub fn export(&mut self) {
    // TODO: use prel/ instead of mml/ (this requires `transfer` in addition to `exporter`)
    const MML: bool = true;

    // self.r.g.clusters.visit(&mut ExportPrep { ctx: &self.r.g.constrs, lc: &self.r.lc });
    let ep = &mut ExportPrep {
      ctx: &self.r.g.constrs,
      lc: &self.r.lc,
      ic: &self.r.lc.infer_const.borrow().vec,
      depth: 0,
    };
    self.export.theorems.visit(ep);

    // loading .sgl
    let mut arts2 = vec![];
    self.path.read_sgl(&mut arts2).unwrap();
    let arts1 = if self.g.constrs.since(&self.export.constrs_base).is_empty() {
      &*arts2
    } else {
      let n = arts2.len();
      arts2.push(self.article);
      &arts2[..n]
    };

    // loading .vcl
    let mut vocs1 = Default::default();
    self.path.read_vcl(&mut vocs1).unwrap();

    // validating .dfr
    {
      let format_base = {
        let mut f = Default::default();
        self.path.read_formats("frm", &mut f).unwrap();
        f.formats.len()
      };
      let dfr1 = &self.lc.formatter.formats.formats.0[format_base..];
      let (mut vocs2, mut dfr2) = Default::default();
      if self.path.read_dfr(MML, &mut vocs2, &mut dfr2).unwrap() {
        assert_eq!(vocs1, vocs2);
      }
      assert_eq!(dfr1, dfr2.0);
    }

    // validating .dno
    {
      let mut dno2 = Default::default();
      if self.path.read_dno(MML, &mut dno2).unwrap() {
        assert_eq!(arts2, dno2.sig);
        assert_eq!(vocs1, dno2.vocs);
      }
      let pats1: Vec<_> = (self.notations.iter())
        .flat_map(|(i, nota)| &nota[self.export.notations_base[i] as usize..])
        .map(|pat| {
          let mut pat = pat.visit_cloned(ep);
          (&self.lc.formatter.formats.formats[std::mem::take(&mut pat.fmt)], pat)
        })
        .collect();
      assert_eq_iter(
        "notations",
        pats1.iter().map(|(f, no)| (*f, no)),
        dno2.pats.iter().map(|(f, no)| (f, no)),
      );
    }

    // validating .dco
    {
      let mut dco2 = Default::default();
      let since1 = self.g.constrs.since(&self.export.constrs_base);
      if self.path.read_dco(MML, &mut dco2).unwrap() {
        assert_eq!(arts1, dco2.sig);
        assert_eq!(since1.len(), dco2.counts);
      }
      macro_rules! process {
        ($($field:ident),*) => {$({
          let cs = since1.$field.iter().map(|c| c.visit_cloned(ep)).collect_vec();
          assert_eq_iter(concat!("constrs.", stringify!($field)),
            cs.iter(), dco2.constrs.$field.0.iter());
        })*};
      }
      process!(mode, struct_mode, attribute, predicate, functor, selector, aggregate);
    }

    // validating .dcl
    {
      let mut dcl2 = Default::default();
      if self.path.read_dcl(MML, &mut dcl2).unwrap() {
        assert_eq!(arts2, dcl2.sig);
      }
      let since1 = self.g.clusters.since(&self.export.clusters_base);
      macro_rules! process {
        ($($field:ident),*) => {$({
          dcl2.$field.visit(ep);
          let cs = since1.$field.iter().map(|c| c.visit_cloned(ep)).collect_vec();
          assert_eq_iter(concat!("clusters.", stringify!($field)),
            cs.iter(), dcl2.$field.iter());
        })*};
      }
      process!(registered, functor, conditional);
    }

    // validating .def
    {
      let (mut sig, mut def2) = Default::default();
      if self.path.read_definitions(MaybeMut::None, MML, "def", Some(&mut sig), &mut def2).unwrap()
      {
        assert_eq!(arts2, sig);
      }
      let def1 = &self.definitions[self.export.definitions_base as usize..];
      let def1 = def1.iter().map(|c| c.visit_cloned(ep)).collect_vec();
      assert_eq_iter("definitions", def1.iter(), def2.iter());
    }

    // validating .did
    {
      let (mut sig, mut did2) = Default::default();
      if self
        .path
        .read_identify_regs(MaybeMut::None, MML, "did", Some(&mut sig), &mut did2)
        .unwrap()
      {
        assert_eq!(arts2, sig);
      }
      let did1 = &self.identify[self.export.identify_base as usize..];
      let did1 = did1.iter().map(|c| c.visit_cloned(ep)).collect_vec();
      assert_eq_iter("identities", did1.iter(), did2.iter());
    }

    // validating .drd
    {
      let (mut sig, mut drd2) = Default::default();
      if self
        .path
        .read_reduction_regs(MaybeMut::None, MML, "drd", Some(&mut sig), &mut drd2)
        .unwrap()
      {
        assert_eq!(arts2, sig);
      }
      let drd1 = &self.reductions[self.export.reductions_base as usize..];
      let drd1 = drd1.iter().map(|c| c.visit_cloned(ep)).collect_vec();
      assert_eq_iter("reductions", drd1.iter(), drd2.iter());
    }

    // validating .dpr
    {
      let (mut sig, mut dpr2) = Default::default();
      if self.path.read_properties(MaybeMut::None, MML, "dpr", Some(&mut sig), &mut dpr2).unwrap() {
        assert_eq!(arts2, sig);
      }
      let dpr1 = &self.properties[self.export.properties_base as usize..];
      let dpr1 = dpr1.iter().map(|c| c.visit_cloned(ep)).collect_vec();
      assert_eq_iter("properties", dpr1.iter(), dpr2.iter());
    }

    if true {
      return // TODO
    }

    // validating .the
    {
      let mut thms2 = Default::default();
      if self.path.read_the(MML, &mut thms2).unwrap() {
        assert_eq!(arts2, thms2.sig);
      }
      assert_eq_iter("theorems", self.export.theorems.iter(), thms2.thm.iter());
    }

    // validating .sch
    {
      let mut schs2 = Default::default();
      if self.path.read_sch(MML, &mut schs2).unwrap()
        // tarski.sch has a manual override
        && self.article.as_str() != "tarski"
      {
        assert_eq!(arts2, schs2.sig);
      }
      let sch1 =
        self.export.schemes.iter().map(|i| i.map(|i| &self.libs.sch[&(ArticleId::SELF, i)]));
      assert_eq_iter("schemes", sch1, schs2.sch.iter().map(Option::as_ref));
    }
  }
}
