use super::{bug_records::TyBug, graph::*};
use crate::{
    analysis::{
        core::alias_analysis::default::value::*,
        utils::fn_info::{convert_alias_to_sets, generate_mir_cfg_dot},
    },
    utils::source::*,
};
use rustc_data_structures::fx::FxHashSet;
use rustc_middle::mir::SourceInfo;
use rustc_span::{Span, symbol::Symbol};

use crate::{rap_debug, rap_info, rap_warn};

impl<'tcx> SafeDropGraph<'tcx> {
    pub fn report_bugs(&self) {
        let filename = get_filename(self.tcx, self.def_id);
        match filename {
            Some(filename) => {
                if filename.contains(".cargo") {
                    return;
                }
            }
            None => {}
        }
        if self.bug_records.is_bug_free() {
            return;
        }
        let fn_name = match get_name(self.tcx, self.def_id) {
            Some(name) => name,
            None => Symbol::intern("no symbol available"),
        };
        self.bug_records.df_bugs_output(fn_name, self.span);
        self.bug_records.uaf_bugs_output(fn_name, self.span);
        self.bug_records.dp_bug_output(fn_name, self.span);
        let _ = generate_mir_cfg_dot(self.tcx, self.def_id);
        rap_warn!("Alias: {:?}", convert_alias_to_sets(self.alias_set.clone()));
    }

    pub fn uaf_check(&mut self, bb_idx: usize, idx: usize, span: Span, is_func_call: bool) {
        if !self.values[idx].may_drop {
            return;
        }
        let mut record = FxHashSet::default();
        if !self.already_dropped(idx, &mut record, false) {
            return;
        }
        if self.values[idx].is_ptr()
            //&& self.values[idx].local == local
            && !is_func_call
        {
            return;
        }
        let bug = TyBug {
            drop_bb: self.drop_record[idx].1,
            drop_id: self.drop_record[idx].2,
            trigger_bb: bb_idx,
            trigger_id: self.values[idx].local,
            span: span.clone(),
        };
        if self.bug_records.uaf_bugs.contains(&bug) {
            return;
        }
        self.bug_records.uaf_bugs.insert(bug);
        rap_debug!(
            "Find use-after-free bug {:?}; add to records",
            self.values[idx]
        );
    }

    pub fn already_dropped(
        &mut self,
        node: usize,
        record: &mut FxHashSet<usize>,
        dangling: bool,
    ) -> bool {
        if node >= self.values.len() {
            return false;
        }
        //if is a dangling pointer check, only check the pointer type varible.
        if self.values[node].is_dropped() && (dangling && self.values[node].is_ptr() || !dangling) {
            return true;
        }
        record.insert(node);
        if self.union_has_alias(node) {
            for i in 0..self.alias_set.len() {
                if i != node && !self.union_is_same(i, node) {
                    continue;
                }
                if record.contains(&i) == false && self.already_dropped(i, record, dangling) {
                    return true;
                }
            }
        }
        for i in self.values[node].fields.clone().into_iter() {
            if record.contains(&i.1) == false && self.already_dropped(i.1, record, dangling) {
                return true;
            }
        }
        return false;
    }

    pub fn is_dangling(&mut self, local: usize) -> bool {
        let mut record = FxHashSet::default();
        return self.already_dropped(local, &mut record, local != 0);
    }

    pub fn df_check(&mut self, bb_idx: usize, idx: usize, span: Span, flag_cleanup: bool) -> bool {
        let root = self.values[idx].local;
        if !self.values[idx].is_dropped() {
            return false;
        }
        let bug = TyBug {
            drop_bb: self.drop_record[idx].1,
            drop_id: self.drop_record[idx].2,
            trigger_bb: bb_idx,
            trigger_id: self.values[idx].local,
            span: span.clone(),
        };

        if flag_cleanup {
            if !self.bug_records.df_bugs_unwind.contains_key(&root) {
                self.bug_records.df_bugs_unwind.insert(idx, bug);
                rap_debug!(
                    "Find DF bug {:?}:{:?} during unwinding; add to records.",
                    idx,
                    root
                );
            }
        } else {
            if !self.bug_records.df_bugs.contains_key(&root) {
                self.bug_records.df_bugs.insert(idx, bug);
                rap_debug!("Find DF bug {:?}:{:?}; add to records.", idx, root);
            }
        }
        return true;
    }

    pub fn dp_check(&mut self, flag_cleanup: bool) {
        if flag_cleanup {
            for i in 0..self.arg_size {
                if self.values[i + 1].is_ptr() && self.is_dangling(i + 1) {
                    let bug = TyBug {
                        drop_bb: self.drop_record[i + 1].1,
                        drop_id: self.drop_record[i + 1].2,
                        trigger_bb: usize::MAX,
                        trigger_id: i,
                        span: self.span.clone(),
                    };
                    self.bug_records.dp_bugs_unwind.insert(bug);
                    rap_debug!(
                        "Find dangling pointer {:?} during unwinding; add to record.",
                        self.values[i + 1]
                    );
                }
            }
        } else {
            if self.values[0].may_drop && self.is_dangling(0) {
                let bug = TyBug {
                    drop_bb: self.drop_record[0].1,
                    drop_id: self.drop_record[0].2,
                    trigger_bb: usize::MAX,
                    trigger_id: 0,
                    span: self.span.clone(),
                };
                self.bug_records.dp_bugs.insert(bug);
                rap_debug!("Find dangling pointer {:?}; add to record.", self.values[0]);
            } else {
                for i in 0..self.arg_size {
                    if self.values[i + 1].is_ptr() && self.is_dangling(i + 1) {
                        let bug = TyBug {
                            drop_bb: self.drop_record[i + 1].1,
                            drop_id: self.drop_record[i + 1].2,
                            trigger_bb: usize::MAX,
                            trigger_id: i,
                            span: self.span.clone(),
                        };
                        self.bug_records.dp_bugs.insert(bug);
                        rap_debug!(
                            "Find dangling pointer {:?}; add to record.",
                            self.values[i + 1]
                        );
                    }
                }
            }
        }
    }

    /*
     * Mark the node as dropped.
     * flag_cleanup: used to distinguish if a bug occurs in the unwinding path.
     */
    pub fn drop_node(
        &mut self,
        idx: usize,     // the value to be dropped
        via_idx: usize, // the value is dropped via its alias: via_idx
        birth: usize,
        info: &SourceInfo,
        flag_inprocess: bool,
        bb_idx: usize,
        flag_cleanup: bool,
    ) {
        //Rc drop
        if self.values[idx].is_corner_case() {
            return;
        }
        //check if there is a double free bug.
        if !flag_inprocess && self.df_check(bb_idx, idx, self.span, flag_cleanup) {
            return;
        }
        let (flag_dropped, _, _) = self.drop_record[idx];
        if flag_dropped {
            return;
        } else {
            self.drop_record[idx] = (true, bb_idx, self.values[via_idx].local);
        }
        //drop their alias
        if self.alias_set[idx] != idx {
            for i in 0..self.values.len() {
                if !self.union_is_same(idx, i) || i == idx || self.values[i].is_ref() {
                    continue;
                }
                self.drop_node(
                    i,
                    self.values[via_idx].local,
                    birth,
                    info,
                    true,
                    bb_idx,
                    flag_cleanup,
                );
            }
        }
        //drop the fields of the root node.
        //alias flag is used to avoid the fields of the alias are dropped repeatly.
        if !flag_inprocess {
            for (_, field_idx) in self.values[idx].fields.clone() {
                if self.values[idx].is_tuple() && !self.values[field_idx].need_drop {
                    continue;
                }
                self.drop_node(
                    field_idx,
                    self.values[via_idx].local,
                    birth,
                    info,
                    false,
                    bb_idx,
                    flag_cleanup,
                );
            }
        }
        //SCC.
        if self.values[idx].birth < birth as isize && self.values[idx].may_drop {
            self.values[idx].drop();
        }
    }

    pub fn get_field_seq(&self, value: &ValueNode) -> Vec<usize> {
        let mut field_id_seq = vec![];
        let mut node_ref = value;
        while node_ref.field_id != usize::MAX {
            field_id_seq.push(node_ref.field_id);
            node_ref = &self.values[value.father];
        }
        return field_id_seq;
    }
}
