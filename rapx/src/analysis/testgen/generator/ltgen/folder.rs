use super::lifetime::Rid;
use rustc_infer::infer::{self, InferCtxt};
use rustc_middle::ty::{self, Ty, TyCtxt, TypeFoldable};
use rustc_span::DUMMY_SP;

pub struct RidExtractFolder<'tcx> {
    tcx: TyCtxt<'tcx>,
    rids: Vec<Rid>,
}

impl<'tcx> RidExtractFolder<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> RidExtractFolder<'tcx> {
        RidExtractFolder {
            tcx,
            rids: Vec::new(),
        }
    }
    pub fn rids(&self) -> &[Rid] {
        &self.rids
    }
}

impl<'tcx> ty::TypeFolder<TyCtxt<'tcx>> for RidExtractFolder<'tcx> {
    fn cx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
    fn fold_region(&mut self, region: ty::Region<'tcx>) -> ty::Region<'tcx> {
        match region.kind() {
            ty::RegionKind::ReVar(vid) => {
                self.rids.push(vid.into());
            }
            _ => {
                panic!("unexpected region kind: {:?}", region);
            }
        }
        region
    }
}

pub fn extract_rids<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Vec<Rid> {
    let mut folder = RidExtractFolder::new(tcx);
    ty.fold_with(&mut folder);
    folder.rids
}

pub struct InfcxVarFolder<'tcx, 'a> {
    infcx: &'a InferCtxt<'tcx>,
    tcx: TyCtxt<'tcx>,
    cnt: usize,
}

impl<'tcx, 'a> InfcxVarFolder<'tcx, 'a> {
    pub fn new(infcx: &'a InferCtxt<'tcx>, tcx: TyCtxt<'tcx>) -> InfcxVarFolder<'tcx, 'a> {
        InfcxVarFolder { infcx, tcx, cnt: 0 }
    }

    pub fn cnt(&self) -> usize {
        self.cnt
    }
}

impl<'tcx, 'a> ty::TypeFolder<TyCtxt<'tcx>> for InfcxVarFolder<'tcx, 'a> {
    fn cx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
    fn fold_region(&mut self, region: ty::Region<'tcx>) -> ty::Region<'tcx> {
        match region.kind() {
            ty::ReVar(_) => {
                panic!("unexpected region kind: {:?}", region);
            }
            _ => {
                self.cnt += 1;
                self.infcx.next_region_var(infer::MiscVariable(DUMMY_SP))
            }
        }
    }
}
