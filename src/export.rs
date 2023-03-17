use crate::analyze::Analyzer;
use crate::parser::MaybeMut;
use crate::types::{ArticleId, ClustersBase, ConstructorsBase, PatternKindClass, SchId, Theorem};
use enum_map::EnumMap;

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

impl Analyzer<'_> {
  pub fn export(&mut self) {
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
      if self.path.read_dfr(&mut vocs2, &mut dfr2).unwrap() {
        assert_eq!(vocs1, vocs2);
      }
      assert_eq!(dfr1, dfr2.0);
    }

    // validating .dno
    {
      let mut dno2 = Default::default();
      if self.path.read_dno(&mut dno2).unwrap() {
        assert_eq!(arts2, dno2.sig);
        assert_eq!(vocs1, dno2.vocs);
      }
      let pats1 = (self.notations.iter())
        .flat_map(|(i, nota)| &nota[self.export.notations_base[i] as usize..])
        .map(|no| (&self.lc.formatter.formats.formats[no.fmt], no));
      assert!(pats1.eq(dno2.pats.iter().map(|(f, no)| (f, no))));
    }

    // validating .dco
    {
      let mut dco2 = Default::default();
      if self.path.read_dco(&mut dco2).unwrap() {
        assert_eq!(arts1, dco2.sig);
        assert_eq!(self.export.constrs_base, dco2.counts);
      }
      let since1 = self.g.constrs.since(&self.export.constrs_base);
      let since2 = dco2.constrs.since(&Default::default());
      assert_eq!(since1, since2);
    }

    // validating .dcl
    {
      let mut dcl2 = Default::default();
      if self.path.read_dcl(&mut dcl2).unwrap() {
        assert_eq!(arts2, dcl2.sig);
      }
      let since1 = self.g.clusters.since(&self.export.clusters_base);
      assert_eq!(since1, dcl2.as_ref());
    }

    // validating .def
    {
      let (mut sig, mut def2) = Default::default();
      if self.path.read_definitions(MaybeMut::None, "def", Some(&mut sig), &mut def2).unwrap() {
        assert_eq!(arts2, sig);
      }
      let since1 = &self.definitions[self.export.definitions_base as usize..];
      assert_eq!(since1, def2);
    }

    // validating .did
    {
      let (mut sig, mut did2) = Default::default();
      if self.path.read_identify_regs(MaybeMut::None, "did", Some(&mut sig), &mut did2).unwrap() {
        assert_eq!(arts2, sig);
      }
      let since1 = &self.identify[self.export.identify_base as usize..];
      assert_eq!(since1, did2);
    }

    // validating .drd
    {
      let (mut sig, mut drd2) = Default::default();
      if self.path.read_reduction_regs(MaybeMut::None, "drd", Some(&mut sig), &mut drd2).unwrap() {
        assert_eq!(arts2, sig);
      }
      let since1 = &self.reductions[self.export.reductions_base as usize..];
      assert_eq!(since1, drd2);
    }

    // validating .dpr
    {
      let (mut sig, mut dpr2) = Default::default();
      if self.path.read_properties(MaybeMut::None, "dpr", Some(&mut sig), &mut dpr2).unwrap() {
        assert_eq!(arts2, sig);
      }
      let since1 = &self.properties[self.export.properties_base as usize..];
      assert_eq!(since1, dpr2);
    }

    // validating .the
    {
      let mut thms2 = Default::default();
      if self.path.read_the(&mut thms2).unwrap() {
        assert_eq!(arts2, thms2.sig);
      }
      assert_eq!(self.export.theorems, thms2.thm);
    }

    // validating .sch
    {
      let mut schs2 = Default::default();
      if self.path.read_sch(&mut schs2).unwrap() {
        assert_eq!(arts2, schs2.sig);
      }
      let sch1 =
        self.export.schemes.iter().map(|i| i.map(|i| &self.libs.sch[&(ArticleId::SELF, i)]));
      assert!(sch1.eq(schs2.sch.iter().map(Option::as_ref)));
    }
  }
}
