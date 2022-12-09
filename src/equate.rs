use crate::checker::{Atoms, Checker, Conjunct, OrUnsat, Unsat};
use crate::types::*;
use crate::{
  mk_id, verbose, vprintln, CheckBound, CmpStyle, Equate, ExpandPrivFunc, Global, Inst,
  LocalContext, OnVarMut, Visit, VisitMut,
};
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::ControlFlow;

pub struct EqTerm {
  id: EqClassId,
  mark: EqMarkId,
  eq_class: Vec<EqMarkId>,
  ty_class: Vec<Type>,
  supercluster: Attrs,
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
  ck: Checker<'a>,
  infers: IdxVec<InferId, Option<EqMarkId>>,
  constrs: ConstrMaps,
  /// TrmS
  eq_term: IdxVec<EqTermId, EqTerm>,
}
impl<'a> std::ops::Deref for Equalizer<'a> {
  type Target = Checker<'a>;
  fn deref(&self) -> &Self::Target { &self.ck }
}
impl<'a> std::ops::DerefMut for Equalizer<'a> {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.ck }
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

/// Not sure why it's called this but all the mizar functions here
/// are called YSomething so there it is.
struct Y<'a> {
  g: &'a mut Global,
  lc: &'a mut LocalContext,
  infers: &'a mut IdxVec<InferId, Option<EqMarkId>>,
  eq_term: &'a mut IdxVec<EqTermId, EqTerm>,
  next_eq_class: EqClassId,
  // numeric_value: Option<Complex>,
  constrs: &'a mut ConstrMaps,
  unsat: OrUnsat<()>,
}

macro_rules! y_try {
  ($self:expr, $e:expr) => {
    match $e {
      Ok(e) => e,
      Err(Unsat) => {
        $self.unsat = Err(Unsat);
        return
      }
    }
  };
}

impl<'a> Y<'a> {
  fn new(eq: &'a mut Equalizer) -> Self {
    Y {
      g: eq.ck.g,
      lc: eq.ck.lc,
      infers: &mut eq.infers,
      eq_term: &mut eq.eq_term,
      next_eq_class: EqClassId::default(),
      constrs: &mut eq.constrs,
      unsat: Ok(()),
    }
  }

  fn new_eq_class(&mut self, tm: &mut Term) -> (EqMarkId, EqTermId) {
    let id = self.next_eq_class.fresh();
    let et = self.eq_term.push(EqTerm {
      id,
      mark: Default::default(),
      eq_class: vec![],
      ty_class: vec![Type::ANY],
      supercluster: Attrs::default(),
    });
    let em = self.lc.marks.push((std::mem::take(tm), et));
    *tm = Term::EqMark(em);
    self.eq_term[et].mark = self.lc.marks.push((Term::EqClass(id), et));
    self.eq_term[et].eq_class.push(em);
    (em, et)
  }

  fn visit_args(&mut self, tms: &mut [Term], depth: u32) -> bool {
    self.visit_terms(tms, depth);
    tms.iter().all(|tm| matches!(tm, Term::EqMark(_)))
  }

  fn insert_type(&mut self, mut new: Box<Type>, et: EqTermId, depth: u32) {
    self.visit_type(&mut new, depth);
    let mut eq_term = &mut self.eq_term[et];
    let mut i;
    loop {
      if let Some(old) = (eq_term.ty_class.iter())
        .find(|old| old.kind == new.kind && ().eq_terms(self.g, self.lc, &old.args, &new.args))
      {
        if !(new.attrs.1)
          .is_subset_of(&eq_term.supercluster, |a1, a2| ().eq_attr(self.g, self.lc, a1, a2))
        {
          for attr in new.attrs.1.try_attrs().unwrap() {
            y_try!(self, eq_term.supercluster.try_insert(&self.g.constrs, attr.clone()))
          }
        }
        return
      }
      self.visit_type(&mut new, depth); // is this okay? we already visited it
      let Attrs::Consistent(attrs) = std::mem::take(&mut new.attrs).1 else { unreachable!() };
      eq_term = &mut self.eq_term[et];
      for attr in attrs {
        y_try!(self, eq_term.supercluster.try_insert(&self.g.constrs, attr));
      }
      if let Some(new2) = new.widening(self.g) {
        eq_term.ty_class.push(*std::mem::replace(&mut new, new2))
      } else {
        i = eq_term.ty_class.len();
        eq_term.ty_class.push(*new);
        break
      }
    }
    if let TypeKind::Struct(mut m) = eq_term.ty_class[i].kind {
      loop {
        let prefixes = self.g.constrs.struct_mode[m].prefixes.clone();
        for mut ty in prefixes.into_vec() {
          ty.visit(&mut Inst::new(&eq_term.ty_class[i].args));
          self.visit_type(&mut ty, depth);
          eq_term = &mut self.eq_term[et];
          ty.attrs = Default::default();
          if !(eq_term.ty_class.iter())
            .any(|old| old.kind == ty.kind && ().eq_terms(self.g, self.lc, &old.args, &ty.args))
          {
            eq_term.ty_class.push(ty)
          }
        }
        i += 1;
        let Some(new) = eq_term.ty_class.get(i) else { return };
        let TypeKind::Struct(m2) = new.kind else { unreachable!() };
        m = m2;
      }
    }
  }

  fn add_binder_into(
    &mut self, tm: &mut Term, depth: u32, coll: fn(&mut ConstrMaps) -> &mut Vec<EqMarkId>,
  ) -> Option<EqTermId> {
    if CheckBound::get(depth, |cb| cb.visit_term(tm, depth)) {
      return None
    }
    OnVarMut(|n, _| *n -= depth).visit_term(tm, depth);
    let vec = coll(self.constrs);
    match vec.binary_search_by(|&m| self.lc.marks[m].0.cmp(&self.g.constrs, tm, CmpStyle::Red)) {
      Ok(i) => {
        *tm = Term::EqMark(self.eq_term[self.lc.marks[vec[i]].1].mark);
        None
      }
      Err(i) => {
        let (m, et) = self.new_eq_class(tm);
        coll(self.constrs).insert(i, m);
        Some(et)
      }
    }
  }
}

impl VisitMut for Y<'_> {
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
          self.infers.get_mut_extending(nr).insert(self.eq_term[et].mark);
          // TODO: numeric_value
          let mut ty = self.lc.infer_const.borrow()[nr].ty.clone();
          ExpandPrivFunc { ctx: &self.g.constrs }.visit_type(&mut ty, depth);
          self.insert_type(ty, et, depth);
          *tm = Term::EqMark(self.eq_term[et].mark);
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
          Term::Functor { nr, args: orig }.round_up_type(self.g, self.lc).to_owned()
        };
        let (nr2, args2) = Term::adjust(nr, args, &self.g.constrs);
        if let Some(m) = self.constrs.functor.find(self.g, self.lc, nr2, args2) {
          *tm = Term::EqMark(self.eq_term[self.lc.marks[m].1].mark);
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
          self.eq_term[et].eq_class.push(m);
          self.constrs.functor.insert(nr3, m)
        }
        *tm = Term::EqMark(self.eq_term[et].mark);
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
          *tm = Term::EqMark(self.eq_term[self.lc.marks[m].1].mark);
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
          *tm = Term::EqMark(self.eq_term[self.lc.marks[m].1].mark);
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
    *tm = Term::EqMark(self.eq_term[et].mark);
    // vprintln!("y term {depth} -> {tm:?} -> {:?}", tm.mark().map(|m| &self.lc.marks[m]));
  }
}

#[derive(Default)]
struct Equals(BTreeSet<(EqTermId, EqTermId)>);

impl Equals {
  fn insert(&mut self, et1: EqTermId, et2: EqTermId) {
    match et1.cmp(&et2) {
      Ordering::Less => self.0.insert((et1, et2)),
      Ordering::Equal => false,
      Ordering::Greater => self.0.insert((et2, et1)),
    };
  }
}

impl Y<'_> {
  fn process_atoms(&mut self, eqs: &mut Equals, atoms: &Atoms, conj: &Conjunct) -> OrUnsat<Atoms> {
    let mut pos_bas = Atoms::default();
    for (i, f) in atoms.0.enum_iter() {
      // vprintln!("y pass atom {f:?}");
      if let Some(true) = conj.0.get(&i) {
        match f {
          Formula::Is { term, ty } => {
            let x_type = ty.visit_cloned(self);
            let x_term = term.visit_cloned(self);
            self.insert_type(x_type, self.lc.marks[x_term.mark().unwrap()].1, 0);
          }
          Formula::Attr { mut nr, args } => {
            let mut args = args.visit_cloned(self).into_vec();
            let term = args.pop().unwrap();
            let et = self.lc.marks[term.mark().unwrap()].1;
            let et = self.lc.marks[self.eq_term[et].mark].1;
            let attr = Attr { nr, pos: true, args: args.into() };
            self.eq_term[et].supercluster.try_insert(&self.g.constrs, attr)?;
            self.eq_term[et].supercluster.try_attrs()?;
          }
          Formula::Pred { mut nr, args } => {
            let (nr, args) = Formula::adjust_pred(nr, args, &self.g.constrs);
            if self.g.reqs.equals_to() == Some(nr) {
              let [arg1, arg2] = args else { unreachable!() };
              let m1 = arg1.visit_cloned(self).mark().unwrap();
              let m2 = arg2.visit_cloned(self).mark().unwrap();
              eqs.insert(self.lc.marks[m1].1, self.lc.marks[m2].1);
            } else {
              pos_bas.0.push(f.visit_cloned(self));
            }
          }
          _ => {
            pos_bas.0.push(f.visit_cloned(self));
          }
        }
        self.unsat?;
      }
    }
    Ok(pos_bas)
  }
}

impl<'a> Equalizer<'a> {
  pub fn new(ck: Checker<'a>) -> Self {
    Self {
      ck,
      infers: Default::default(),
      constrs: Default::default(),
      eq_term: Default::default(),
    }
  }

  pub fn equate(&mut self, atoms: &Atoms, conj: Conjunct) -> OrUnsat<()> {
    let mut yy = Y::new(self);
    let mut eqs = Equals::default();
    let pos_bas = yy.process_atoms(&mut eqs, atoms, &conj)?;
    Ok(())
  }
}
