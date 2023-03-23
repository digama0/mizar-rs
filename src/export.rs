use crate::analyze::Analyzer;
use crate::parser::MaybeMut;
use crate::types::*;
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
  ctx: Option<&'a Constructors>,
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
  let (mut hi, mut new): (EnumMap<_, u32>, EnumMap<_, u32>) = Default::default();
  for (_, (art, counts)) in vocs.0.iter().enumerate() {
    let lo = hi;
    counts.iter().for_each(|(i, &count)| hi[i] += count);
    let used = fmts.iter_mut().any(|fmt| {
      let mut used = false;
      get(fmt).visit(|k, sym| used |= (lo[k]..hi[k]).contains(&sym));
      used
    });
    if used {
      marked_vocs.0.push((*art, *counts));
      for (kind, &count) in counts {
        trans[kind].extend((0..count).map(|i| Some(i + new[kind])));
        new[kind] += count
      }
    } else {
      for (kind, &count) in counts {
        trans[kind].extend((0..count).map(|_| None))
      }
    }
  }
  for fmt in fmts {
    get(fmt).visit_mut(|k, sym| *sym = trans[k][*sym as usize].unwrap());
  }
}

struct MarkConstr<'a> {
  /// Article, plus the constructor counts *including* this article.
  /// The current article may be in the list, in which case it is at the end.
  accum: &'a [(Article, ConstructorsBase)],
  /// This is a parallel array, where `used[i]` corresponds to `accum[i+1]`.
  /// `used[-1] -> accum[0]` is effectively true always because it is the HIDDEN article,
  /// and `used.last()` is true if constructors from the current article are used.
  /// (Because this always contains an entry for the current article it may either
  /// be the same length or one shorter than accum.)
  used: Vec<bool>,
}

impl<'a> MarkConstr<'a> {
  fn new(accum: &'a [(Article, ConstructorsBase)], n: usize) -> Self {
    Self { accum, used: vec![false; n] }
  }

  fn mark(&mut self, n: u32, key: impl Fn(&ConstructorsBase) -> u32) {
    if let Some(i) = self.accum.partition_point(|(_, base)| key(base) <= n).checked_sub(1) {
      self.used[i] = true
    }
  }

  fn closure(&mut self, constrs: &mut Constructors) {
    let n = self.accum.len() - 1;
    let mut base = self.accum[n].1;
    for i in (0..n).rev() {
      let lo = &self.accum[i].1;
      if self.used[i] {
        constrs.visit_range(self, lo..&base)
      }
      base = *lo
    }
  }

  fn apply(&self) -> ApplyMarkConstr {
    let (mut offset, mut base) = Default::default();
    let mut apply = ApplyMarkConstr::default();
    let mut prev = true;
    for ((_, accum), &mark) in self.accum.iter().zip(&self.used) {
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
    ts.iter().zip([true].iter().chain(&self.used)).filter(|p| *p.1).map(|p| *p.0).collect_vec()
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

#[derive(Default)]
struct ApplyMarkConstr(Vec<(ConstructorsBase, ConstructorsBase)>);
impl ApplyMarkConstr {
  fn apply(&mut self, n: &mut u32, key: impl Fn(&ConstructorsBase) -> u32) {
    if let Some(i) = self.0.partition_point(|(base, _)| key(base) <= *n).checked_sub(1) {
      *n -= key(&self.0[i].1)
    }
  }
}

impl VisitMut for ApplyMarkConstr {
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
    let mut marks = MarkConstr::new(&self.accum, n);
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
    let (mut vocs1, mut aco) = Default::default();
    self.path.read_vcl(&mut vocs1).unwrap();

    // loading .aco
    self.path.read_aco(&mut aco).unwrap();
    assert_eq!(self.export.constrs_base, aco.constrs.len());
    assert_eq!(arts1.len(), aco.accum.len());

    // validating .dfr
    {
      let format_base = {
        let mut f = Default::default();
        self.path.read_formats("frm", &mut f).unwrap();
        f.formats.len()
      };
      let mut dfr1 = &self.lc.formatter.formats.formats.0[format_base..];
      let (mut vocs2, mut dfr2) = Default::default();
      let nonempty = self.path.read_dfr(false, &mut vocs2, &mut dfr2).unwrap();
      assert_eq!(!dfr1.is_empty(), nonempty);
      let mut marked_dfr;
      if nonempty {
        let mut marked_vocs = Vocabularies::default();
        marked_dfr = dfr1.to_owned();
        mark_formats(&vocs1, &mut marked_vocs, &mut marked_dfr, |x| x);
        assert_eq!(marked_vocs, vocs2);
        dfr1 = &marked_dfr;
      }
      assert_eq!(dfr1, dfr2.0);
    }

    // validating .dco (also push current article to aco)
    {
      let mut dco2 = Default::default();
      let nonempty = self.path.read_dco(false, &mut dco2).unwrap();
      let since1 = self.g.constrs.since(&self.export.constrs_base);
      let mut constrs1 = since1.to_owned();
      constrs1.visit(ep);
      assert_eq!(!since1.is_empty(), nonempty);
      if nonempty {
        aco.constrs.append(constrs1.clone());
        let mut marks = MarkConstr::new(&aco.accum, arts1.len());
        *marks.used.last_mut().unwrap() = true;
        constrs1.visit(&mut marks);
        marks.closure(&mut aco.constrs);
        marks.apply_with(|v| constrs1.visit(v));
        assert_eq!(marks.filtered(arts1), dco2.sig);
        assert_eq!(constrs1.len(), dco2.counts);
        aco.accum.push((self.article, self.g.constrs.len()));
      }
      macro_rules! process { ($($field:ident),*) => {$(
        assert_eq_iter(concat!("constrs.", stringify!($field)),
          constrs1.$field.0.iter(), dco2.constrs.$field.0.iter());
      )*}}
      process!(mode, struct_mode, attribute, predicate, functor, selector, aggregate);
    }

    // validating .dno
    {
      let mut pats1 = (self.notations.iter())
        .flat_map(|(i, nota)| &nota[self.export.notations_base[i] as usize..])
        .map(|pat| {
          let mut pat = pat.visit_cloned(ep);
          (self.lc.formatter.formats.formats[std::mem::take(&mut pat.fmt)], pat)
        })
        .collect_vec();
      let mut dno2 = Default::default();
      let nonempty = self.path.read_dno(false, &mut dno2).unwrap();
      assert_eq!(!pats1.is_empty(), nonempty);
      if nonempty {
        let mut marked_vocs = Vocabularies::default();
        mark_formats(&vocs1, &mut marked_vocs, &mut pats1, |(fmt, _)| fmt);
        let mut marks = MarkConstr::new(&aco.accum, arts1.len());
        pats1.iter_mut().for_each(|p| p.1.visit(&mut marks));
        marks.closure(&mut aco.constrs);
        marks.apply_with(|v| pats1.iter_mut().for_each(|p| p.1.visit(v)));
        assert_eq!(marks.filtered(&arts2), dno2.sig);
        assert_eq!(marked_vocs, dno2.vocs);
      }
      assert_eq_iter("notations", pats1.iter(), dno2.pats.iter());
    }

    // validating .dcl
    {
      let mut dcl2 = Default::default();
      let nonempty = self.path.read_dcl(false, &mut dcl2).unwrap();
      ep.with_ctx(None, |ep| dcl2.cl.visit(ep));
      let since1 = self.g.clusters.since(&self.export.clusters_base);
      assert_eq!(!since1.is_empty(), nonempty);
      let mut cl1 = since1.to_owned();
      cl1.visit(ep);
      if nonempty {
        assert_eq!(aco.mark(&mut cl1, arts1.len(), &arts2), dcl2.sig);
      }
      macro_rules! process { ($($field:ident),*) => {$({
        assert_eq_iter(concat!("clusters.", stringify!($field)),
          cl1.$field.iter(), dcl2.cl.$field.iter());
      })*}}
      process!(registered, functor, conditional);
    }

    // validating .def
    {
      let (mut sig, mut def2) = Default::default();
      let nonempty = (self.path)
        .read_definitions(MaybeMut::None, false, "def", Some(&mut sig), &mut def2)
        .unwrap();
      let mut def1 = self.definitions[self.export.definitions_base as usize..].to_owned();
      def1.visit(ep);
      assert_eq!(!def1.is_empty(), nonempty);
      if nonempty {
        assert_eq!(aco.mark(&mut def1, arts1.len(), &arts2), sig);
      }
      assert_eq_iter("definitions", def1.iter(), def2.iter());
    }

    // validating .did
    {
      let (mut sig, mut did2) = Default::default();
      let nonempty = (self.path)
        .read_identify_regs(MaybeMut::None, false, "did", Some(&mut sig), &mut did2)
        .unwrap();
      let mut did1 = self.identify[self.export.identify_base as usize..].to_owned();
      did1.visit(ep);
      assert_eq!(!did1.is_empty(), nonempty);
      if nonempty {
        assert_eq!(aco.mark(&mut did1, arts1.len(), &arts2), sig);
      }
      assert_eq_iter("identities", did1.iter(), did2.iter());
    }

    // validating .drd
    {
      let (mut sig, mut drd2) = Default::default();
      let nonempty = (self.path)
        .read_reduction_regs(MaybeMut::None, false, "drd", Some(&mut sig), &mut drd2)
        .unwrap();
      let mut drd1 = self.reductions[self.export.reductions_base as usize..].to_owned();
      drd1.visit(ep);
      assert_eq!(!drd1.is_empty(), nonempty);
      if nonempty {
        assert_eq!(aco.mark(&mut drd1, arts1.len(), &arts2), sig);
      }
      assert_eq_iter("reductions", drd1.iter(), drd2.iter());
    }

    // validating .dpr
    {
      let (mut sig, mut dpr2) = Default::default();
      let nonempty =
        self.path.read_properties(MaybeMut::None, false, "dpr", Some(&mut sig), &mut dpr2).unwrap();
      let mut dpr1 = self.properties[self.export.properties_base as usize..].to_owned();
      dpr1.visit(ep);
      assert_eq!(!dpr1.is_empty(), nonempty);
      if nonempty {
        assert_eq!(aco.mark(&mut dpr1, arts1.len(), &arts2), sig);
      }
      assert_eq_iter("properties", dpr1.iter(), dpr2.iter());
    }

    // validating .the
    {
      let mut thms2 = Default::default();
      let nonempty = self.path.read_the(false, &mut thms2).unwrap();
      let mut thms1 = std::mem::take(&mut self.export.theorems);
      assert_eq!(!thms1.is_empty(), nonempty);
      if nonempty {
        thms1.visit(ep);
        assert_eq!(aco.mark(&mut thms1, arts1.len(), &arts2), thms2.sig);
      }
      assert_eq_iter("theorems", thms1.iter(), thms2.thm.iter());
    }

    // validating .sch
    {
      let mut schs2 = Default::default();
      let nonempty = self.path.read_sch(false, &mut schs2).unwrap();
      let mut schs1 = (self.export.schemes.iter())
        .map(|i| i.map(|i| self.libs.sch[&(ArticleId::SELF, i)].visit_cloned(ep)))
        .collect_vec();
      assert_eq!(!schs1.is_empty(), nonempty);
      if nonempty {
        assert_eq!(aco.mark(&mut schs1, arts1.len(), &arts2), schs2.sig);
      }
      assert_eq_iter("schemes", schs1.iter(), schs2.sch.iter());
    }
  }
}
