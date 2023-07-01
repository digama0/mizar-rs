use crate::parser::MaybeMut;
use crate::types::*;
use crate::MizPath;
use once_cell::sync::OnceCell;
use std::collections::HashMap;
use std::io;

struct CacheMap {
  articles: HashMap<Article, Cache>,
  reqs: HashMap<Article, OnceCell<DepRequirements>>,
}

static CACHE: OnceCell<CacheMap> = OnceCell::new();

#[derive(Default)]
pub struct Cache {
  pub wait: bool,
  pub dfr: OnceCell<(Vocabularies, Vec<Format>)>,
  pub dno: OnceCell<DepNotation>,
  pub dco: OnceCell<DepConstructors>,
  pub dcl: OnceCell<DepClusters>,
  pub def: OnceCell<(Vec<Article>, Vec<Definiens>)>,
  pub dpr: OnceCell<(Vec<Article>, Vec<Property>)>,
  pub did: OnceCell<(Vec<Article>, Vec<IdentifyFunc>)>,
  pub drd: OnceCell<(Vec<Article>, Vec<Reduction>)>,
  pub the: OnceCell<DepTheorems>,
  pub sch: OnceCell<DepSchemes>,
}

pub fn init_cache<'a>(articles: impl Iterator<Item = (&'a str, bool)>) {
  let articles = ["hidden", "tarski_0", "tarski_a"]
    .into_iter()
    .map(|x| (x, false))
    .chain(articles)
    .map(|(s, wait)| (Article::from_lower(s.as_bytes()), Cache { wait, ..Cache::default() }))
    .collect();
  let reqs = ["arithm", "boole", "hidden", "numerals", "real", "subset"]
    .into_iter()
    .map(|s| (Article::from_lower(s.as_bytes()), Default::default()))
    .collect();
  CACHE.set(CacheMap { articles, reqs }).ok().unwrap()
}

impl MizPath {
  pub fn with_cache<T>(&self, get: impl FnOnce(&Cache) -> &OnceCell<T>, value: T) {
    if let Some(c) = CACHE.get().and_then(|map| map.articles.get(&self.art)) {
      get(c).get_or_init(|| value);
    }
  }

  fn get_cache<A, T, R>(
    &self, no: bool, args: &mut A, get: impl FnOnce(&Cache) -> &OnceCell<T>,
    read: impl FnOnce(&mut A, bool) -> io::Result<R>, take: impl FnOnce(&mut A, R) -> T,
    copy: impl FnOnce(&mut A, &T) -> R,
  ) -> io::Result<R> {
    if !no {
      if let Some(c) = CACHE.get().and_then(|map| map.articles.get(&self.art)) {
        let t = if c.wait {
          get(c).wait()
        } else {
          get(c).get_or_try_init(|| read(args, true).map(|r| take(args, r)))?
        };
        return Ok(copy(args, t))
      }
    }
    read(args, false)
  }

  fn get_cache_basic<A: Default + Clone, R>(
    &self, no: bool, args: &mut A, get: impl FnOnce(&Cache) -> &OnceCell<A>,
    read: impl FnOnce(&mut A) -> io::Result<R>, result: impl FnOnce(&A) -> R,
  ) -> io::Result<R> {
    self.get_cache(
      no,
      args,
      get,
      |a, _| read(a),
      |a, _| std::mem::take(a),
      |a, t| {
        a.clone_from(t);
        result(t)
      },
    )
  }

  pub fn read_dfr(
    &self, new_prel: bool, vocs: &mut Vocabularies, formats: &mut IdxVec<FormatId, Format>,
  ) -> io::Result<bool> {
    self.get_cache(
      new_prel,
      &mut (vocs, formats),
      |c| &c.dfr,
      |(vocs, formats), _| self.read_dfr_uncached(new_prel, vocs, formats),
      |(vocs, formats), _| (std::mem::take(vocs), std::mem::take(&mut formats.0)),
      |(vocs, formats), (vocs2, formats2)| {
        vocs.clone_from(vocs2);
        formats.0.clone_from(formats2);
        !formats2.is_empty()
      },
    )
  }

  pub fn read_dno(&self, new_prel: bool, dno: &mut DepNotation) -> io::Result<bool> {
    self.get_cache_basic(
      new_prel,
      dno,
      |c| &c.dno,
      |dno| self.read_dno_uncached(new_prel, dno),
      |dno| !dno.pats.is_empty(),
    )
  }

  pub fn read_dco(
    &self, new_prel: bool, dco: &mut DepConstructors, read_constrs: bool,
  ) -> io::Result<bool> {
    self.get_cache(
      new_prel,
      dco,
      |c| &c.dco,
      |dco, cache| self.read_dco_uncached(new_prel, dco, read_constrs || cache),
      |dco, _| std::mem::take(dco),
      |dco, dco2| {
        dco.sig.clone_from(&dco2.sig);
        dco.counts = dco2.counts;
        if read_constrs {
          dco.constrs.clone_from(&dco2.constrs);
        }
        !dco2.constrs.as_ref().is_empty()
      },
    )
  }

  pub fn read_dre(&self, dre: &mut DepRequirements) -> io::Result<()> {
    if let Some(c) = CACHE.get().and_then(|map| map.reqs.get(&self.art)) {
      dre.clone_from(c.get_or_init(|| {
        let mut dre = Default::default();
        self.read_dre_uncached(&mut dre).unwrap();
        dre
      }));
      Ok(())
    } else {
      self.read_dre_uncached(dre)
    }
  }

  pub fn read_dcl(&self, new_prel: bool, dcl: &mut DepClusters) -> io::Result<bool> {
    self.get_cache_basic(
      new_prel,
      dcl,
      |c| &c.dcl,
      |dcl| self.read_dcl_uncached(new_prel, dcl),
      |dcl| !dcl.cl.as_ref().is_empty(),
    )
  }

  pub fn read_def(
    &self, new_prel: bool, sig: &mut Vec<Article>, defs: &mut Vec<Definiens>,
  ) -> io::Result<bool> {
    self.get_cache(
      new_prel,
      &mut (sig, defs),
      |c| &c.def,
      |(sig, defs), _| self.read_definitions(MaybeMut::None, new_prel, "def", Some(sig), defs),
      |(sig, defs), _| (std::mem::take(sig), std::mem::take(defs)),
      |(sig, defs), (sig2, defs2)| {
        sig.clone_from(sig2);
        defs.clone_from(defs2);
        !defs2.is_empty()
      },
    )
  }

  pub fn read_dpr(
    &self, new_prel: bool, sig: &mut Vec<Article>, dpr: &mut Vec<Property>,
  ) -> io::Result<bool> {
    self.get_cache(
      new_prel,
      &mut (sig, dpr),
      |c| &c.dpr,
      |(sig, dpr), _| self.read_properties(MaybeMut::None, new_prel, "dpr", Some(sig), dpr),
      |(sig, dpr), _| (std::mem::take(sig), std::mem::take(dpr)),
      |(sig, dpr), (sig2, dpr2)| {
        sig.clone_from(sig2);
        dpr.clone_from(dpr2);
        !dpr2.is_empty()
      },
    )
  }

  pub fn read_did(
    &self, new_prel: bool, sig: &mut Vec<Article>, did: &mut Vec<IdentifyFunc>,
  ) -> io::Result<bool> {
    self.get_cache(
      new_prel,
      &mut (sig, did),
      |c| &c.did,
      |(sig, did), _| self.read_identify_regs(MaybeMut::None, new_prel, "did", Some(sig), did),
      |(sig, did), _| (std::mem::take(sig), std::mem::take(did)),
      |(sig, did), (sig2, did2)| {
        sig.clone_from(sig2);
        did.clone_from(did2);
        !did2.is_empty()
      },
    )
  }

  pub fn read_drd(
    &self, new_prel: bool, sig: &mut Vec<Article>, drd: &mut Vec<Reduction>,
  ) -> io::Result<bool> {
    self.get_cache(
      new_prel,
      &mut (sig, drd),
      |c| &c.drd,
      |(sig, drd), _| self.read_reduction_regs(MaybeMut::None, new_prel, "drd", Some(sig), drd),
      |(sig, drd), _| (std::mem::take(sig), std::mem::take(drd)),
      |(sig, drd), (sig2, drd2)| {
        sig.clone_from(sig2);
        drd.clone_from(drd2);
        !drd2.is_empty()
      },
    )
  }

  pub fn read_the(&self, new_prel: bool, the: &mut DepTheorems) -> io::Result<bool> {
    self.get_cache_basic(
      new_prel,
      the,
      |c| &c.the,
      |the| self.read_the_uncached(new_prel, the),
      |the| !the.thm.is_empty(),
    )
  }

  pub fn read_sch(&self, new_prel: bool, sch: &mut DepSchemes) -> io::Result<bool> {
    self.get_cache_basic(
      new_prel,
      sch,
      |c| &c.sch,
      |sch| self.read_sch_uncached(new_prel, sch),
      |sch| !sch.sch.is_empty(),
    )
  }
}
