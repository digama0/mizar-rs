use crate::checker::{Atoms, Checker, Conjunct, Dnf, OrUnsat, Unsat};
use crate::types::*;
use crate::{
  mk_id, verbose, vprintln, CheckBound, CmpStyle, Equate, ExpandPrivFunc, Global, Inst,
  LocalContext, OnVarMut, Visit, VisitMut,
};
use enum_map::EnumMap;
use itertools::Itertools;
use std::borrow::{Borrow, Cow};
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::ControlFlow;

pub struct EqTerm {
  id: EqClassId,
  /// Term is EqMark(mark)
  mark: EqMarkId,
  eq_class: Vec<EqMarkId>,
  ty_class: Vec<Type>,
  supercluster: Attrs,
  // TODO: polynomial_values
}

#[derive(Default)]
struct ConstrMap<I>(BTreeMap<I, Vec<EqMarkId>>);

impl<I: Idx> ConstrMap<I> {
  fn insert(&mut self, nr: I, mark: EqMarkId) { self.0.entry(nr).or_default().push(mark) }

  fn find(&self, g: &Global, lc: &LocalContext, nr: I, args: &[Term]) -> Option<EqMarkId> {
    let entry = self.0.get(&nr)?;
    entry.iter().copied().find(|&m| ().eq_terms(g, lc, args, lc.marks[m].0.args().unwrap()))
  }
}

impl Attrs {
  fn try_attrs(&self) -> OrUnsat<&[Attr]> {
    match self {
      Attrs::Inconsistent => Err(Unsat),
      Attrs::Consistent(attrs) => Ok(attrs),
    }
  }
  fn try_insert(&mut self, ctx: &Constructors, item: Attr) -> OrUnsat<()> {
    self.insert(ctx, item);
    self.try_attrs()?;
    Ok(())
  }
}

#[derive(Default)]
struct ConstrMaps {
  priv_func: ConstrMap<PrivFuncId>,
  functor: ConstrMap<FuncId>,
  selector: ConstrMap<SelId>,
  aggregate: ConstrMap<AggrId>,
  fraenkel: Vec<EqMarkId>,
  choice: Vec<EqMarkId>,
}

pub struct Equalizer<'a> {
  g: &'a Global,
  lc: &'a mut LocalContext,
  reductions: &'a [Reduction],
  infers: IdxVec<InferId, Option<EqMarkId>>,
  constrs: ConstrMaps,
  /// TrmS
  terms: IdxVec<EqTermId, EqTerm>,
  next_eq_class: EqClassId,
  allowed_ccl: Vec<Attrs>,
  allowed_fcl: Vec<Attrs>,
}

struct CheckE<'a> {
  marks: &'a IdxVec<EqMarkId, (Term, EqTermId)>,
  found: bool,
}

impl<'a> CheckE<'a> {
  fn with(marks: &'a IdxVec<EqMarkId, (Term, EqTermId)>, f: impl FnOnce(&mut CheckE<'a>)) -> bool {
    let mut ce = CheckE { marks, found: false };
    f(&mut ce);
    ce.found
  }
}

impl Visit for CheckE<'_> {
  fn abort(&self) -> bool { self.found }
  fn visit_term(&mut self, tm: &Term, depth: u32) {
    match *tm {
      Term::EqClass(_) => self.found = true,
      Term::EqMark(m) if matches!(self.marks[m].0, Term::EqClass(_)) => self.found = true,
      _ => self.super_visit_term(tm, depth),
    }
  }
}

struct EqMarks;

impl Equate for EqMarks {
  const IGNORE_MARKS: bool = false;
  fn eq_pred(
    &mut self, g: &Global, lc: &LocalContext, n1: PredId, n2: PredId, args1: &[Term],
    args2: &[Term],
  ) -> bool {
    n1 == n2
      && (self.eq_terms(g, lc, args1, args2)
        || {
          let c = &g.constrs.predicate[n1];
          c.properties.get(PropertyKind::Symmetry) && {
            let mut args1 = args1.iter().collect_vec();
            args1.swap(c.arg1 as usize, c.arg2 as usize);
            args1[c.superfluous as usize..]
              .iter()
              .zip(args2)
              .all(|(&t1, t2)| self.eq_term(g, lc, t1, t2))
          }
        }
        || {
          let c = &g.constrs.predicate[n2];
          c.properties.get(PropertyKind::Symmetry) && {
            let mut args2 = args2.iter().collect_vec();
            args2.swap(c.arg1 as usize, c.arg2 as usize);
            args1
              .iter()
              .zip(&args2[c.superfluous as usize..])
              .all(|(t1, &t2)| self.eq_term(g, lc, t1, t2))
          }
        })
  }

  // EqMarks.eq_term: EqTrms
  // EqMarks.eq_formula: EqFrms
}

impl Term {
  fn mark(&self) -> Option<EqMarkId> {
    match *self {
      Term::EqMark(m) => Some(m),
      _ => None,
    }
  }

  fn unmark<'a>(&'a self, lc: &'a LocalContext) -> &'a Term {
    match *self {
      Term::EqMark(m) => &lc.marks[m].0,
      _ => self,
    }
  }
}

impl Equalizer<'_> {
  /// YEqClass
  fn new_eq_class(&mut self, tm: &mut Term) -> (EqMarkId, EqTermId) {
    let id = self.next_eq_class.fresh();
    let et = self.terms.push(EqTerm {
      id,
      mark: Default::default(),
      eq_class: vec![],
      ty_class: vec![Type::ANY],
      supercluster: Attrs::default(),
    });
    let m = self.lc.marks.push((std::mem::take(tm), et));
    *tm = Term::EqMark(m);
    self.terms[et].mark = self.lc.marks.push((Term::EqClass(id), et));
    self.terms[et].eq_class.push(m);
    (m, et)
  }

  fn insert_type(&mut self, mut new: Type, et: EqTermId, depth: u32) -> OrUnsat<()> {
    self.y(|y| y.visit_type(&mut new, depth))?;
    let mut eq_term = &mut self.terms[et];
    let mut i;
    loop {
      if let Some(old) = (eq_term.ty_class.iter())
        .find(|old| old.kind == new.kind && ().eq_terms(self.g, self.lc, &old.args, &new.args))
      {
        if !(new.attrs.1)
          .is_subset_of(&eq_term.supercluster, |a1, a2| ().eq_attr(self.g, self.lc, a1, a2))
        {
          for attr in new.attrs.1.try_attrs().unwrap() {
            eq_term.supercluster.try_insert(&self.g.constrs, attr.clone())?
          }
        }
        return Ok(())
      }
      self.y(|y| y.visit_type(&mut new, depth))?; // is this okay? we already visited it
      let Attrs::Consistent(attrs) = std::mem::take(&mut new.attrs).1 else { unreachable!() };
      eq_term = &mut self.terms[et];
      for attr in attrs {
        eq_term.supercluster.try_insert(&self.g.constrs, attr)?;
      }
      if let Some(new2) = new.widening(self.g) {
        eq_term.ty_class.push(std::mem::replace(&mut new, *new2))
      } else {
        i = eq_term.ty_class.len();
        eq_term.ty_class.push(new);
        break
      }
    }
    if let TypeKind::Struct(mut m) = eq_term.ty_class[i].kind {
      loop {
        let prefixes = self.g.constrs.struct_mode[m].prefixes.clone();
        for mut ty in prefixes.into_vec() {
          ty.visit(&mut Inst::new(&eq_term.ty_class[i].args));
          self.y(|y| y.visit_type(&mut ty, depth))?;
          eq_term = &mut self.terms[et];
          ty.attrs = Default::default();
          if !(eq_term.ty_class.iter())
            .any(|old| old.kind == ty.kind && ().eq_terms(self.g, self.lc, &old.args, &ty.args))
          {
            eq_term.ty_class.push(ty)
          }
        }
        i += 1;
        let Some(new) = eq_term.ty_class.get(i) else { return Ok(()) };
        let TypeKind::Struct(m2) = new.kind else { unreachable!() };
        m = m2;
      }
    }
    Ok(())
  }
}

/// Not sure why it's called this but all the mizar functions here
/// are called YSomething so there it is.
struct Y<'a, 'b> {
  eq: &'b mut Equalizer<'a>,
  unsat: OrUnsat<()>,
}
impl<'a, 'b> std::ops::Deref for Y<'a, 'b> {
  type Target = &'b mut Equalizer<'a>;
  fn deref(&self) -> &Self::Target { &self.eq }
}
impl<'a, 'b> std::ops::DerefMut for Y<'a, 'b> {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.eq }
}

impl<'a> Equalizer<'a> {
  fn y<'b, R>(&'b mut self, f: impl FnOnce(&mut Y<'a, 'b>) -> R) -> OrUnsat<R> {
    let mut y = Y { eq: self, unsat: Ok(()) };
    let r = f(&mut y);
    y.unsat?;
    Ok(r)
  }
}

impl<'a, 'b> Y<'a, 'b> {
  fn visit_args(&mut self, tms: &mut [Term], depth: u32) -> bool {
    self.visit_terms(tms, depth);
    tms.iter().all(|tm| matches!(tm, Term::EqMark(_)))
  }

  fn add_binder_into(
    &mut self, tm: &mut Term, depth: u32, coll: fn(&mut ConstrMaps) -> &mut Vec<EqMarkId>,
  ) -> Option<EqTermId> {
    if CheckBound::get(depth, |cb| cb.visit_term(tm, depth)) {
      return None
    }
    OnVarMut(|n, _| *n -= depth).visit_term(tm, depth);
    let vec = coll(&mut self.eq.constrs);
    match vec
      .binary_search_by(|&m| self.eq.lc.marks[m].0.cmp(&self.eq.g.constrs, tm, CmpStyle::Red))
    {
      Ok(i) => {
        *tm = Term::EqMark(self.eq.terms[self.eq.lc.marks[vec[i]].1].mark);
        None
      }
      Err(i) => {
        let (m, et) = self.new_eq_class(tm);
        coll(&mut self.constrs).insert(i, m);
        Some(et)
      }
    }
  }
}

impl VisitMut for Y<'_, '_> {
  fn abort(&self) -> bool { self.unsat.is_err() }

  /// YTerm
  fn visit_term(&mut self, tm: &mut Term, depth: u32) {
    if self.abort() {
      return
    }
    // vprintln!("y term {depth} <- {tm:?} <- {:?}", tm.unmark(self.lc));
    let et = match tm {
      Term::Bound(_) | Term::EqClass(_) => return,
      &mut Term::Infer(nr) => {
        if let Some(&Some(em)) = self.infers.get(nr) {
          *tm = Term::EqMark(em);
        } else {
          let (m, et) = self.new_eq_class(tm);
          self.eq.infers.get_mut_extending(nr).insert(self.eq.terms[et].mark);
          // TODO: numeric_value
          let mut ty = self.lc.infer_const.get_mut()[nr].ty.clone();
          ExpandPrivFunc { ctx: &self.g.constrs }.visit_type(&mut ty, depth);
          self.insert_type(ty, et, depth);
          *tm = Term::EqMark(self.terms[et].mark);
        }
        return
      }
      Term::Functor { mut nr, args } => {
        let orig = args.clone();
        if !self.visit_args(args, depth) {
          return
        }
        let mut args1 = args.clone();
        let mut ty = if CheckE::with(&self.lc.marks, |ce| ce.visit_terms(&orig, depth)) {
          Term::Functor { nr, args: orig }.get_type_uncached(self.g, self.lc)
        } else {
          *Term::Functor { nr, args: orig }.round_up_type(self.g, self.lc).to_owned()
        };
        let (nr2, args2) = Term::adjust(nr, args, &self.g.constrs);
        if let Some(m) = self.constrs.functor.find(self.g, self.lc, nr2, args2) {
          *tm = Term::EqMark(self.terms[self.lc.marks[m].1].mark);
          return
        }
        *tm = Term::Functor { nr: nr2, args: args2.to_vec().into() };
        let (m, et) = self.new_eq_class(tm);
        self.constrs.functor.insert(nr2, m);
        self.insert_type(ty, et, depth);
        if self.g.reqs.zero_number() == Some(Term::adjusted_nr(nr2, &self.g.constrs)) {
          // TODO: numeric_value
        }
        let constr = &self.g.constrs.functor[nr];
        if constr.properties.get(PropertyKind::Commutativity) {
          args1.swap(constr.arg1 as usize, constr.arg2 as usize);
          let (nr3, comm_args) = Term::adjust(nr, &args1, &self.g.constrs);
          let m =
            self.lc.marks.push((Term::Functor { nr: nr3, args: comm_args.to_vec().into() }, et));
          self.terms[et].eq_class.push(m);
          self.constrs.functor.insert(nr3, m)
        }
        *tm = Term::EqMark(self.terms[et].mark);
        return
      }
      Term::SchFunc { nr, args } => {
        if !self.visit_args(args, depth) {
          return
        }
        self.new_eq_class(tm).1
      }
      Term::PrivFunc { mut nr, args, .. } => {
        if !self.visit_args(args, depth) {
          return
        }
        let (m, et) = self.new_eq_class(tm);
        self.constrs.priv_func.insert(nr, m);
        et
      }
      Term::Aggregate { mut nr, args, .. } => {
        if !self.visit_args(args, depth) {
          return
        }
        if let Some(m) = self.constrs.aggregate.find(self.g, self.lc, nr, args) {
          *tm = Term::EqMark(self.terms[self.lc.marks[m].1].mark);
          return
        }
        let (m, et) = self.new_eq_class(tm);
        self.constrs.aggregate.insert(nr, m);
        et
      }
      Term::Selector { mut nr, args, .. } => {
        if !self.visit_args(args, depth) {
          return
        }
        if let Some(m) = self.constrs.selector.find(self.g, self.lc, nr, args) {
          *tm = Term::EqMark(self.terms[self.lc.marks[m].1].mark);
          return
        }
        let (m, et) = self.new_eq_class(tm);
        self.constrs.selector.insert(nr, m);
        et
      }
      Term::Fraenkel { args, scope, compr } => {
        let mut depth2 = depth;
        for ty in &mut **args {
          self.visit_type(ty, depth2);
          depth2 += 1;
        }
        self.visit_term(scope, depth2);
        self.visit_formula(compr, depth2);
        let Some(et) = self.add_binder_into(tm, depth, |c| &mut c.fraenkel) else { return };
        et
      }
      Term::Choice { ty } => {
        self.visit_type(ty, depth);
        let Some(et) = self.add_binder_into(tm, depth, |c| &mut c.choice) else { return };
        et
      }
      Term::EqMark(mut m) => match &self.lc.marks[m].0 {
        Term::Bound(_) | Term::EqClass(_) => return,
        _ => unreachable!("already marked"),
      },
      Term::Locus(_)
      | Term::Constant(_)
      | Term::FreeVar(_)
      | Term::LambdaVar(_)
      | Term::Numeral(_)
      | Term::Qua { .. }
      | Term::It => unreachable!(),
    };
    let mut ty = tm.get_type_uncached(self.g, self.lc);
    self.insert_type(ty, et, depth);
    *tm = Term::EqMark(self.terms[et].mark);
    // vprintln!("y term {depth} -> {tm:?} -> {:?}", tm.mark().map(|m| &self.lc.marks[m]));
  }
}

#[derive(Default)]
struct Equals(BTreeSet<(EqTermId, EqTermId)>);

impl Equals {
  #[inline]
  fn insert(&mut self, et1: EqTermId, et2: EqTermId) {
    match et1.cmp(&et2) {
      Ordering::Less => self.0.insert((et1, et2)),
      Ordering::Equal => false,
      Ordering::Greater => self.0.insert((et2, et1)),
    };
  }
}

struct HasInfer<'a> {
  infers: &'a IdxVec<InferId, Option<EqMarkId>>,
  found: bool,
}
impl<'a> HasInfer<'a> {
  pub fn get(infers: &'a IdxVec<InferId, Option<EqMarkId>>, f: impl FnOnce(&mut Self)) -> bool {
    let mut cb = Self { infers, found: false };
    f(&mut cb);
    cb.found
  }
}
impl Visit for HasInfer<'_> {
  fn abort(&self) -> bool { self.found }
  fn visit_term(&mut self, tm: &Term, depth: u32) {
    match *tm {
      Term::Infer(n) => self.found |= self.infers.get(n).map_or(true, |i| i.is_none()),
      _ => self.super_visit_term(tm, depth),
    }
  }
}

impl Attr {
  fn is_strict(&self, ctx: &Constructors) -> bool {
    self.pos && ctx.attribute[self.nr].properties.get(PropertyKind::Abstractness)
  }
}

struct Instantiate<'a> {
  g: &'a Global,
  lc: &'a LocalContext,
  terms: &'a IdxVec<EqTermId, EqTerm>,
  subst: &'a [Type],
}

impl Instantiate<'_> {
  /// InstantiateTerm(fCluster = self.subst, eTrm = tgt, aTrm = src)
  fn inst_term(&mut self, src: &Term, tgt: &Term) -> Dnf<LocusId, EqClassId> {
    match (tgt.unmark(self.lc), src) {
      (Term::Numeral(n), Term::Numeral(n2)) if n == n2 => Dnf::True,
      (Term::Functor { nr: n1, args: args1 }, Term::Functor { nr: n2, args: args2 }) => {
        let (n1, args1) = Term::adjust(*n1, args1, &self.g.constrs);
        let (n2, args2) = Term::adjust(*n2, args2, &self.g.constrs);
        if n1 == n2 {
          let mut res = Dnf::True;
          for (a, b) in args1.iter().zip(args2) {
            res.mk_and(self.inst_term(a, b))
          }
          res
        } else {
          Dnf::FALSE
        }
      }
      (
        Term::Selector { nr: SelId(n1), args: args1 },
        Term::Selector { nr: SelId(n2), args: args2 },
      )
      | (
        Term::Aggregate { nr: AggrId(n1), args: args1 },
        Term::Aggregate { nr: AggrId(n2), args: args2 },
      ) if n1 == n2 => {
        let mut res = Dnf::True;
        for (a, b) in args1.iter().zip(&**args2) {
          res.mk_and(self.inst_term(a, b))
        }
        res
      }
      (
        Term::Numeral(_) | Term::Functor { .. } | Term::Selector { .. } | Term::Aggregate { .. },
        _,
      ) => Dnf::FALSE,
      (Term::EqClass(_), _) => {
        let et = self.lc.marks[self.terms[self.lc.marks[tgt.mark().unwrap()].1].mark].1;
        match src {
          &Term::Locus(v) => {
            let mut z = self.inst_type(&self.subst[v.0 as usize], et);
            if let Dnf::Or(conjs) = &mut z {
              Dnf::insert_and_absorb(conjs, Conjunct::single(v, self.terms[et].id));
            }
            z
          }
          // TODO: numeric_value
          // &Term::Numeral(n) if numeric_value => {}
          Term::Numeral(_) => Dnf::FALSE,
          Term::Functor { nr: n2, args: args2 } => {
            let (n2, args2) = Term::adjust(*n2, args2, &self.g.constrs);
            let mut res = Dnf::FALSE;
            for &m in &self.terms[et].eq_class {
              if let Term::Functor { nr: n1, args: args1 } = &self.lc.marks[m].0 {
                let (n1, args1) = Term::adjust(*n1, args1, &self.g.constrs);
                if n1 == n2 {
                  res.mk_or(&self.inst_terms(args1, args2))
                }
              }
            }
            res
          }
          Term::Selector { nr: n2, args: args2 } => {
            let mut res = Dnf::True;
            for &m in &self.terms[et].eq_class {
              if let Term::Selector { nr: n1, args: args1 } = &self.lc.marks[m].0 {
                if n1 == n2 {
                  res.mk_or(&self.inst_terms(args1, args2))
                }
              }
            }
            res
          }
          Term::Aggregate { nr: n2, args: args2 } => {
            let mut res = Dnf::True;
            for &m in &self.terms[et].eq_class {
              if let Term::Aggregate { nr: n1, args: args1 } = &self.lc.marks[m].0 {
                if n1 == n2 {
                  res.mk_or(&self.inst_terms(args1, args2))
                }
              }
            }
            res
          }
          _ => unreachable!(),
        }
      }
      _ => unreachable!(),
    }
  }

  fn inst_terms(&mut self, args1: &[Term], args2: &[Term]) -> Dnf<LocusId, EqClassId> {
    assert!(args1.len() == args2.len());
    let mut res = Dnf::True;
    for (a, b) in args1.iter().zip(args2) {
      res.mk_and(self.inst_term(a, b))
    }
    res
  }

  /// InstantiateType(cCluster = self.subst, enr = et, aTyp = ty)
  fn inst_type(&mut self, ty: &Type, et: EqTermId) -> Dnf<LocusId, EqClassId> {
    let et = self.lc.marks[self.terms[et].mark].1;
    let mut res = Dnf::FALSE;
    match ty.kind {
      TypeKind::Struct(_) =>
        for ty2 in &self.terms[et].ty_class {
          if ty.kind == ty2.kind {
            res.mk_or(&self.inst_terms(&ty.args, &ty2.args));
            if let Dnf::True = res {
              break
            }
          }
        },
      TypeKind::Mode(n) => {
        let (n, args) = Type::adjust(n, &ty.args, &self.g.constrs);
        for ty2 in &self.terms[et].ty_class {
          if let TypeKind::Mode(n2) = ty2.kind {
            let (n2, args2) = Type::adjust(n2, &ty2.args, &self.g.constrs);
            if n == n2 {
              res.mk_or(&self.inst_terms(&ty.args, args2));
              if let Dnf::True = res {
                break
              }
            }
          }
        }
      }
    }
    self.and_inst_attrs(&ty.attrs.0, et, &mut res);
    res
  }

  fn and_inst_attrs(&mut self, attrs: &Attrs, et: EqTermId, res: &mut Dnf<LocusId, EqClassId>) {
    let Attrs::Consistent(attrs) = attrs else { unreachable!() };
    let Attrs::Consistent(sc) = &self.terms[et].supercluster else { unreachable!() };
    for a1 in attrs {
      let (n1, args1) = a1.adjust(&self.g.constrs);
      let mut z = Dnf::FALSE;
      for a2 in sc {
        let (n2, args2) = a2.adjust(&self.g.constrs);
        if n1 == n2 && a1.pos == a2.pos {
          z.mk_or(&self.inst_terms(args1, args2));
          if let Dnf::True = z {
            break
          }
        }
      }
      res.mk_and(z);
    }
  }

  fn inst_fcluster(&mut self, cl: &FunctorCluster) { todo!() }
}

impl<'a> Equalizer<'a> {
  pub fn new(ck: &'a mut Checker<'_>) -> Self {
    Self {
      g: ck.g,
      lc: ck.lc,
      reductions: ck.reductions,
      infers: Default::default(),
      constrs: Default::default(),
      terms: Default::default(),
      next_eq_class: Default::default(),
      allowed_ccl: Default::default(),
      allowed_fcl: Default::default(),
    }
  }

  fn filter_allowed(&self, attrs: &Attrs) -> Attrs {
    match attrs {
      Attrs::Inconsistent => Attrs::Inconsistent,
      Attrs::Consistent(attrs) => {
        let attrs =
          attrs.iter().filter(|a| !HasInfer::get(&self.infers, |ci| ci.visit_terms(&a.args, 0)));
        Attrs::Consistent(attrs.cloned().collect())
      }
    }
  }

  fn add_symm(&self, pos: &Atoms, neg: &mut Atoms, prop: PropertyKind) {
    for f in &pos.0 .0 {
      if let Formula::Pred { mut nr, args } = f {
        let pred = &self.g.constrs.predicate[nr];
        // Why are we searching for f in neg_bas here?
        if pred.properties.get(prop) && neg.find(self.g, self.lc, f).is_none() {
          let mut args = args.clone();
          args.swap(pred.arg1 as usize, pred.arg2 as usize);
          neg.insert(self.g, self.lc, Cow::Owned(Formula::Pred { nr, args }));
        }
      }
    }
  }

  fn drain_pending(
    &mut self, to_y_term: &mut Vec<(EqTermId, Term)>, eq_pendings: &mut Equals,
  ) -> OrUnsat<()> {
    for (i, mut tm) in to_y_term.drain(..) {
      self.y(|y| y.visit_term(&mut tm, 0))?;
      eq_pendings.insert(i, self.lc.marks[tm.mark().unwrap()].1)
    }
    Ok(())
  }

  /// UnionTrms
  fn union_terms(&mut self, x: EqTermId, y: EqTermId) -> OrUnsat<()> {
    let (x, y) = (self.lc.marks[self.terms[x].mark].1, self.lc.marks[self.terms[y].mark].1);
    let (from, to) = match x.cmp(&y) {
      Ordering::Less => (y, x),
      Ordering::Equal => return Ok(()),
      Ordering::Greater => (x, y),
    };
    let mut clash = true;
    // TODO: numeric_value
    for &m in &self.terms[from].eq_class {
      let m = self.terms[self.lc.marks[m].1].mark;
      self.lc.marks[m].1 = to;
    }
    let eq_class = std::mem::take(&mut self.terms[from].eq_class);
    self.terms[to].eq_class.append(&mut { eq_class });
    let Attrs::Consistent(attrs) = std::mem::take(&mut self.terms[from].supercluster)
    else { unreachable!() };
    for attr in attrs {
      self.terms[to].supercluster.try_insert(&self.g.constrs, attr)?;
    }
    for ty in std::mem::take(&mut self.terms[from].ty_class) {
      self.insert_type(ty, to, 0)?
    }
    // TODO: polynomial_values
    Ok(())
  }

  fn instantiate<'b>(&'b self, subst: &'b [Type]) -> Instantiate<'b> {
    Instantiate { g: self.g, lc: self.lc, terms: &self.terms, subst }
  }

  fn locate_terms(
    &self, inst: &Conjunct<LocusId, EqClassId>, args1: &[Term], args2: &[Term],
  ) -> Option<()> {
    assert!(args1.len() == args2.len());
    for (t1, t2) in args1.iter().zip(args2) {
      let m1 = self.locate_term(inst, t1)?;
      matches!(*t2, Term::EqMark(m2) if m1 == m2).then_some(())?;
    }
    Some(())
  }

  fn locate_term(&self, inst: &Conjunct<LocusId, EqClassId>, tm: &Term) -> Option<EqMarkId> {
    match *tm {
      Term::Locus(n) => {
        let id = *inst.0.get(&n)?;
        Some(self.terms.0.iter().find(|&et| et.id == id)?.mark)
      }
      Term::Infer(n) => self.terms.0.iter().find_map(|et| {
        (et.eq_class.iter().copied())
          .find(|&m| matches!(self.lc.marks[m].0, Term::Infer(n2) if n == n2))
      }),
      Term::Numeral(_) => None, // TODO: numeric_value
      Term::Functor { nr, ref args } => self.terms.0.iter().find_map(|et| {
        et.eq_class.iter().copied().find(|&m| {
          matches!(&self.lc.marks[m].0, Term::Functor { nr: nr2, args: args2 }
            if nr == *nr2 && self.locate_terms(inst, args, args2).is_some())
        })
      }),
      Term::Selector { nr, ref args } => self.terms.0.iter().find_map(|et| {
        et.eq_class.iter().copied().find(|&m| {
          matches!(&self.lc.marks[m].0, Term::Selector { nr: nr2, args: args2 }
            if nr == *nr2 && self.locate_terms(inst, args, args2).is_some())
        })
      }),
      Term::Aggregate { nr, ref args } => self.terms.0.iter().find_map(|et| {
        et.eq_class.iter().copied().find(|&m| {
          matches!(&self.lc.marks[m].0, Term::Aggregate { nr: nr2, args: args2 }
            if nr == *nr2 && self.locate_terms(inst, args, args2).is_some())
        })
      }),
      _ => None,
    }
  }

  /// ProcessReductions
  fn process_reductions(&mut self) -> OrUnsat<()> {
    let mut i = 0;
    while let Some(m) = self.infers.0.get(i) {
      if let Some(m) = *m {
        let et = self.lc.marks[m].1;
        if !self.terms[et].eq_class.is_empty() {
          for red in self.reductions {
            let inst = self
              .instantiate(&red.primary)
              .inst_term(&red.terms[0], &Term::EqMark(self.terms[et].mark));
            match inst {
              Dnf::True => panic!("unreachable?"),
              Dnf::Or(conjs) =>
                if let Some(conj) = conjs.first() {
                  let m = if let Term::Functor { nr, args } = &red.terms[1] {
                    let (nr, args) = Term::adjust(*nr, args, &self.g.constrs);
                    self.locate_term(conj, &Term::Functor { nr, args: args.to_vec().into() })
                  } else {
                    self.locate_term(conj, &red.terms[1])
                  };
                  self.union_terms(et, self.lc.marks[m.unwrap()].1)?;
                },
            }
          }
        }
      }
      i += 1;
    }
    Ok(())
  }

  pub fn equate(&mut self, atoms: &Atoms, conj: Conjunct<AtomId, bool>) -> OrUnsat<()> {
    self.lc.marks.0.clear();
    let mut eqs = Equals::default();
    let mut bas = EnumMap::<bool, Atoms>::default();
    for pos in [true, false] {
      for (i, f) in atoms.0.enum_iter() {
        // vprintln!("y pass atom {f:?}");
        if conj.0.get(&i).copied() == Some(pos) {
          match f {
            Formula::Is { term, ty } if pos => {
              let x_type = self.y(|y| (**ty).visit_cloned(y))?;
              let x_term = self.y(|y| (**term).visit_cloned(y))?;
              self.insert_type(x_type, self.lc.marks[x_term.mark().unwrap()].1, 0);
            }
            Formula::Attr { mut nr, args } => {
              let mut args = self.y(|y| args.visit_cloned(y))?.into_vec();
              let term = args.pop().unwrap();
              let et = self.lc.marks[term.mark().unwrap()].1;
              let et = self.lc.marks[self.terms[et].mark].1;
              let attr = Attr { nr, pos, args: args.into() };
              self.terms[et].supercluster.try_insert(&self.g.constrs, attr)?;
              self.terms[et].supercluster.try_attrs()?;
            }
            Formula::Pred { mut nr, args } if pos => {
              let (nr, args) = Formula::adjust_pred(nr, args, &self.g.constrs);
              if self.g.reqs.equals_to() == Some(nr) {
                let [arg1, arg2] = args else { unreachable!() };
                let m1 = self.y(|y| arg1.visit_cloned(y))?.mark().unwrap();
                let m2 = self.y(|y| arg2.visit_cloned(y))?.mark().unwrap();
                eqs.insert(self.lc.marks[m1].1, self.lc.marks[m2].1);
              } else {
                bas[pos].0.push(self.y(|y| f.visit_cloned(y))?);
              }
            }
            _ => {
              bas[pos].0.push(self.y(|y| f.visit_cloned(y))?);
            }
          }
        }
      }
    }

    // InitAllowedClusters
    self.allowed_ccl = (self.g.clusters.conditional.iter())
      .map(|cl| self.filter_allowed(&cl.consequent.1))
      .filter(|attrs| !attrs.attrs().is_empty())
      .collect();
    self.allowed_fcl = (self.g.clusters.functor.vec.0.iter())
      .map(|cl| self.filter_allowed(&cl.consequent.1))
      .filter(|attrs| !attrs.attrs().is_empty())
      .collect();

    let [mut neg_bas, mut pos_bas] = bas.into_array();
    self.add_symm(&pos_bas, &mut neg_bas, PropertyKind::Asymmetry);
    self.add_symm(&neg_bas, &mut pos_bas, PropertyKind::Connectedness);

    let mut eq_pendings = Equals::default();
    let mut to_y_term = vec![];
    for (i, ets) in self.terms.enum_iter() {
      let mut j = 0;
      for &m in &ets.eq_class {
        if let Term::Infer(id) = self.lc.marks[m].0 {
          for &z in &self.lc.infer_const.get_mut()[id].eq_const {
            to_y_term.push((i, Term::Infer(z)));
          }
        }
      }
    }
    self.drain_pending(&mut to_y_term, &mut eq_pendings)?;

    // InitEmptyInEqClass
    if let Some(empty_set) = self.g.reqs.empty_set() {
      let empty = self.g.reqs.empty().unwrap();
      for (i, ets) in self.terms.enum_iter() {
        assert!(!ets.eq_class.is_empty()); // TODO: is this true?
        if !ets.eq_class.is_empty() {
          if let Some(attr) = ets.supercluster.find0(&self.g.constrs, empty) {
            if attr.pos {
              to_y_term.push((i, Term::Functor { nr: empty_set, args: Box::new([]) }))
            }
          }
        }
      }
      self.drain_pending(&mut to_y_term, &mut eq_pendings)?;
    }
    if let Some(zero_number) = self.g.reqs.zero_number() {
      let zero = self.g.reqs.zero().unwrap();
      for (i, ets) in self.terms.enum_iter() {
        assert!(!ets.eq_class.is_empty()); // TODO: is this true?
        if !ets.eq_class.is_empty() {
          if let Some(attr) = ets.supercluster.find0(&self.g.constrs, zero) {
            if attr.pos {
              to_y_term.push((i, Term::Functor { nr: zero_number, args: Box::new([]) }))
            }
          }
        }
      }
      self.drain_pending(&mut to_y_term, &mut eq_pendings)?;
    }

    // InitStructuresInEqClass
    for (i, mut tm) in to_y_term.drain(..) {
      self.y(|y| y.visit_term(&mut tm, 0))?;
      eq_pendings.insert(i, self.lc.marks[tm.mark().unwrap()].1)
    }

    for (i, ets) in self.terms.enum_iter() {
      assert!(!ets.eq_class.is_empty()); // TODO: is this true?
      if !ets.eq_class.is_empty() {
        let ei = self.lc.marks[ets.mark].1;
        let mut strict_struct = None;
        for attr in ets.supercluster.try_attrs().unwrap() {
          if attr.is_strict(&self.g.constrs) {
            let TypeKind::Struct(s) = self.g.constrs.attribute[attr.nr].ty.kind else { panic!() };
            if matches!(strict_struct.replace(s), Some(old) if old != s) {
              return Err(Unsat)
            }
          }
        }
        if let Some(s) = strict_struct {
          for ty in &ets.ty_class {
            if ty.kind == TypeKind::Struct(s) {
              to_y_term.push((ei, Term::mk_aggr(self.g, s, &Term::EqMark(ets.mark), ty)))
            }
          }
        }
      }
    }
    let mut eqs = Equals::default();
    self.drain_pending(&mut to_y_term, &mut eqs)?;
    for (x, y) in eqs.0 {
      self.union_terms(x, y)?
    }

    self.process_reductions();

    Ok(())
  }
}
