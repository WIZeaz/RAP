use crate::analysis::utils::fn_info::*;
use rustc_hir::{Safety, def_id::DefId};
use rustc_middle::mir::Local;
use std::collections::HashSet;

#[derive(Debug, Clone)]
pub struct UPGUnit {
    pub caller: FnInfo,
    pub callees: HashSet<FnInfo>,
    pub raw_ptrs: HashSet<Local>,
    pub static_muts: HashSet<DefId>,
    pub caller_cons: HashSet<FnInfo>,
    pub mut_methods: Vec<DefId>,
}

impl UPGUnit {
    pub fn new(
        caller: FnInfo,
        callees: HashSet<FnInfo>,
        raw_ptrs: HashSet<Local>,
        static_muts: HashSet<DefId>,
        caller_cons: HashSet<FnInfo>,
        mut_methods: Vec<DefId>,
    ) -> Self {
        Self {
            caller,
            callees,
            raw_ptrs,
            static_muts,
            caller_cons,
            mut_methods,
        }
    }

    pub fn count_basic_units(&self, data: &mut [u32]) {
        if self.caller.fn_safety == Safety::Unsafe && self.callees.is_empty() {
            data[0] += 1;
        }
        if self.caller.fn_safety == Safety::Safe && self.caller.fn_kind != FnKind::Method {
            for callee in &self.callees {
                if callee.fn_kind == FnKind::Method {
                    data[2] += 1;
                } else {
                    data[1] += 1;
                }
            }
        }
        if self.caller.fn_safety == Safety::Unsafe && self.caller.fn_kind != FnKind::Method {
            for callee in &self.callees {
                if callee.fn_kind == FnKind::Method {
                    data[4] += 1;
                } else {
                    data[3] += 1;
                }
            }
        }
        if self.caller.fn_safety == Safety::Unsafe && self.caller.fn_kind == FnKind::Method {
            let mut unsafe_cons = 0;
            let mut safe_cons = 0;
            for cons in &self.caller_cons {
                if cons.fn_safety == Safety::Unsafe {
                    unsafe_cons += 1;
                } else {
                    safe_cons += 1;
                }
            }
            if unsafe_cons == 0 && safe_cons == 0 {
                safe_cons = 1;
            }
            for callee in &self.callees {
                if callee.fn_kind == FnKind::Method {
                    data[7] += safe_cons;
                    data[8] += unsafe_cons;
                } else {
                    data[5] += safe_cons;
                    data[6] += unsafe_cons;
                }
            }
        }
        if self.caller.fn_safety == Safety::Safe && self.caller.fn_kind == FnKind::Method {
            let mut unsafe_cons = 0;
            let mut safe_cons = 0;
            for cons in &self.caller_cons {
                if cons.fn_safety == Safety::Unsafe {
                    unsafe_cons += 1;
                } else {
                    safe_cons += 1;
                }
            }
            if unsafe_cons == 0 && safe_cons == 0 {
                safe_cons = 1;
            }
            for callee in &self.callees {
                if callee.fn_kind == FnKind::Method {
                    data[11] += safe_cons;
                    data[12] += unsafe_cons;
                } else {
                    data[9] += safe_cons;
                    data[10] += unsafe_cons;
                }
            }
        }
    }
}
