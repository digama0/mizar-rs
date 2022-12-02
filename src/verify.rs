use crate::{types::*, *};

pub struct Verifier {
  pub g: Global,
  pub lc: LocalContext,
  pub libs: Libraries,
  pub article: Article,
  pub treat_thm_as_axiom: bool,
  pub equalities: Vec<Definiens>,
  pub expansions: Vec<Definiens>,
  pub properties: Vec<Property>,
  pub identifications: Vec<Identify>,
  pub reductions: Vec<Reduction>,
  pub equals: BTreeMap<ConstrKind, Vec<EqualsDef>>,
  pub func_ids: BTreeMap<ConstrKind, Vec<usize>>,
  pub props: Vec<Formula>,
  pub labels: IdxVec<LabelId, usize>,
}

struct BlockReset {
  fixed_var: usize,
  props: usize,
  labels: usize,
}

impl BlockReset {
  fn finish(self, v: &mut Verifier) {
    v.lc.fixed_var.0.truncate(self.fixed_var);
    v.props.truncate(self.props);
    v.labels.0.truncate(self.labels);
  }
}

impl Verifier {
  pub fn new(reqs: RequirementIndexes, nonzero_type: Type, article: Article) -> Self {
    Verifier {
      g: Global {
        reqs,
        constrs: Default::default(),
        clusters: Default::default(),
        nonzero_type,
        recursive_round_up: false,
        rounded_up_clusters: false,
      },
      lc: LocalContext::default(),
      libs: Libraries::default(),
      article,
      treat_thm_as_axiom: matches!(article.as_str(), "tarski_0" | "tarski_a"),
      equalities: Default::default(),
      expansions: Default::default(),
      properties: Default::default(),
      identifications: Default::default(),
      reductions: Default::default(),
      equals: Default::default(),
      func_ids: Default::default(),
      props: Default::default(),
      labels: Default::default(),
    }
  }

  fn new_block(&self) -> BlockReset {
    BlockReset {
      fixed_var: self.lc.fixed_var.len(),
      props: self.props.len(),
      labels: self.labels.len(),
    }
  }

  pub fn intern<'a, T: Clone + Visitable<InternConst<'a>>>(&'a self, t: &T) -> T {
    let mut t = t.clone();
    t.visit(&mut self.intern_const());
    t
  }

  pub fn intern_const(&self) -> InternConst<'_> {
    InternConst::new(&self.g, &self.lc, &self.equals, &self.identifications, &self.func_ids)
  }

  pub fn push_prop(&mut self, label: Option<LabelId>, prop: Formula) {
    self.props.push(prop);
    if let Some(label) = label {
      assert!(label == self.labels.push(self.props.len()));
    }
  }

  pub fn verify_item(&mut self, it: &Item) {
    eprintln!("item: {:#?}", it);
    match it {
      Item::Let(vars) =>
        for ty in vars {
          self.lc.fixed_var.push(FixedVar { ty: Box::new(self.intern(ty)), def: None });
        },
      Item::Given(_) => todo!(),
      Item::Conclusion(_) => todo!(),
      Item::Assume(_) => todo!(),
      Item::Take(_) => todo!(),
      Item::TakeAsVar(_, _) => todo!(),
      Item::PerCases(_) => todo!(),
      Item::AuxiliaryItem(_) => todo!(),
      Item::Registration(_) => todo!(),
      Item::Scheme(bl) => {
        let SchemeBlock { pos, label, sch_nr, decls, prems, thesis, just } = &**bl;
        let sch_funcs = self.lc.sch_func_ty.len();
        for decl in decls {
          match decl {
            SchemeDecl::Func { args, ty } => {
              self.intern(args);
              self.lc.sch_func_ty.0.push(self.intern(ty))
            }
            SchemeDecl::Pred { args } => {
              self.intern(args);
            }
          }
        }
        let prems = self.intern(prems);
        let thesis = self.intern(thesis);
        self.lc.sch_func_ty.0.truncate(sch_funcs);
      }
      Item::Theorem { prop, just } => todo!(),
      Item::DefTheorem { kind, prop } => todo!(),
      Item::Reservation { .. } => {} // reservations not handled by checker
      Item::Section => {}
      Item::Canceled(_) => todo!(),
      Item::Definition(Definition { pos, label, redef, kind, conds, corr, props, constr }) => {
        assert!(!redef);
        assert!(conds.is_empty() && corr.is_none());
        assert!(props.is_empty());
        if let Some(constr) = constr {
          self.g.constrs.push(self.intern(constr))
        }
      }
      Item::DefStruct(_) => todo!(),
      Item::Definiens(df) => {
        let df = self.intern(df);
        self.equalities.push(df.clone()); // TODO: is this needed?
        self.expansions.push(df);
      }
      Item::Block { kind, pos, label, items } => {
        let bl = self.new_block();
        for it in items {
          self.verify_item(it);
        }
        bl.finish(self);
      }
    }
  }

  pub fn verify_justification(&mut self, thesis: Option<&Formula>, just: &Justification) {
    match just {
      Justification::Simple(_) => todo!(),
      Justification::Proof { pos, label, thesis: block_thesis, items } => {
        assert!(thesis.map_or(true, |t| ().eq_formula(&self.g, &self.lc, t, block_thesis)));
      }
      Justification::SkippedProof => todo!(),
      Justification::Error => todo!(),
    }
  }
}
