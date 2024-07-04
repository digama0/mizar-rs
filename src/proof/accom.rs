use super::write::{PredName, Step, WriteProof};
use super::{OptProofBuilder, ProofBuilder};
use crate::accom::{Accomodator, SigBuilder};
use crate::proof::write::FuncName;
use crate::types::{
  AggrId, AttrId, Constructors, FuncId as MFuncId, Idx, ModeId, PredId as MPredId,
  RequirementIndexes, RequirementKind, SelId, StructId,
};
use crate::HashMap;

impl<W: WriteProof> ProofBuilder<W> {
  pub fn accom_constructors(
    &mut self, sig: &SigBuilder, constrs: &Constructors, reqs: &RequirementIndexes,
  ) {
    let inner = self.inner.get_mut();
    let mut rev = HashMap::new();
    for (req, _) in reqs.fwd {
      if let Some(kind) = reqs.get(req) {
        assert!(rev.insert(kind, req).is_none())
      }
    }
    for (i, &(art, ref lo)) in sig.sig.enum_iter() {
      let hi = sig.hi(i);
      for id in (lo.mode..hi.mode).map(ModeId) {
        let name = PredName::Mode(art, ModeId(id.0 - lo.mode));
        let req = rev.get(&RequirementKind::Mode(id)).copied();
        self.w.w.write_step(Step::LoadPred { name, req }).unwrap();
        assert_eq!(id, inner.mode.push(self.w.pred_num.fresh()));
      }
      for id in (lo.struct_mode..hi.struct_mode).map(StructId) {
        let name = PredName::Struct(art, StructId(id.0 - lo.struct_mode));
        self.w.w.write_step(Step::LoadPred { name, req: None }).unwrap();
        assert_eq!(id, inner.struct_mode.push(self.w.pred_num.fresh()));
      }
      for id in (lo.attribute..hi.attribute).map(AttrId) {
        let name = PredName::Attr(art, AttrId(id.0 - lo.attribute));
        let req = rev.get(&RequirementKind::Attr(id)).copied();
        self.w.w.write_step(Step::LoadPred { name, req }).unwrap();
        assert_eq!(id, inner.attr.push(self.w.pred_num.fresh()));
      }
      for id in (lo.predicate..hi.predicate).map(MPredId) {
        let name = PredName::Pred(art, MPredId(id.0 - lo.predicate));
        let req = rev.get(&RequirementKind::Pred(id)).copied();
        self.w.w.write_step(Step::LoadPred { name, req }).unwrap();
        assert_eq!(id, inner.pred.push(self.w.pred_num.fresh()));
      }
      for id in (lo.functor..hi.functor).map(MFuncId) {
        let name = FuncName::Func(art, MFuncId(id.0 - lo.functor));
        let req = rev.get(&RequirementKind::Func(id)).copied();
        self.w.w.write_step(Step::LoadFunc { name, req }).unwrap();
        assert_eq!(id, inner.func.push((self.w.func_num.fresh(), constrs.functor[id].superfluous)));
      }
      for id in (lo.selector..hi.selector).map(SelId) {
        let name = FuncName::Sel(art, SelId(id.0 - lo.selector));
        self.w.w.write_step(Step::LoadFunc { name, req: None }).unwrap();
        assert_eq!(id, inner.sel.push(self.w.func_num.fresh()));
      }
      for id in (lo.aggregate..hi.aggregate).map(AggrId) {
        let name = FuncName::Aggr(art, AggrId(id.0 - lo.aggregate));
        self.w.w.write_step(Step::LoadFunc { name, req: None }).unwrap();
        assert_eq!(id, inner.aggr.push(self.w.func_num.fresh()));
      }
    }
  }
}
