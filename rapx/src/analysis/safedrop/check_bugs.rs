use super::graph::*;
use crate::analysis::utils::fn_info::{convert_alias_to_sets, generate_mir_cfg_dot};
use crate::utils::source::*;
use rustc_data_structures::fx::FxHashSet;
use rustc_middle::mir::SourceInfo;
use rustc_span::symbol::Symbol;
use rustc_span::Span;

use crate::rap_warn;
use crate::rap_debug;

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

    pub fn uaf_check(&mut self, aliaset_idx: usize, span: Span, local: usize, is_func_call: bool) {
        let mut record = FxHashSet::default();
        if self.values[aliaset_idx].may_drop
            && (!self.values[aliaset_idx].is_ptr()
                || self.values[aliaset_idx].local != local
                || is_func_call)
            && self.already_dropped(aliaset_idx, &mut record, false)
            && !self.bug_records.uaf_bugs.contains(&span)
        {
            self.bug_records.uaf_bugs.insert(span.clone());
            rap_warn!("UAF bug for local {:?}", local);
        }
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
        if self.values[node].is_dangling() == false
            && (dangling && self.values[node].is_ptr() || !dangling)
        {
            return true;
        }
        record.insert(node);
        if self.union_has_alias(node) {
            // for i in self.values[node].alias.clone().into_iter() {
            //     if i != node && record.contains(&i) == false && self.already_dropped(i, record, dangling)
            //     {
            //         return true;
            //     }
            // }
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

    pub fn df_check(&mut self, drop: usize, span: Span, flag_cleanup: bool) -> bool {
        let root = self.values[drop].local;
        if self.values[drop].is_dangling() {
            return false;
        }
        if flag_cleanup {
            if !self.bug_records.df_bugs_unwind.contains_key(&root) {
                self.bug_records.df_bugs_unwind.insert(root, span.clone());
                rap_debug!("DF bug for {:?} during unwinding", drop);
            }
        } else {
            if !self.bug_records.df_bugs.contains_key(&root) {
                self.bug_records.df_bugs.insert(root, span.clone());
                rap_debug!("DF bug for {:?}", drop);
            }
        }
        return true;
    }

    pub fn dp_check(&mut self, current_block: &BlockNode<'tcx>) {
        match current_block.is_cleanup {
            true => {
                for i in 0..self.arg_size {
                    if self.values[i + 1].is_ptr() && self.is_dangling(i + 1) {
                        self.bug_records.dp_bugs_unwind.insert(self.span);
                        rap_warn!("DP bug for local {:?}", i + 1);
                    }
                }
            }
            false => {
                if self.values[0].may_drop && self.is_dangling(0) {
                    self.bug_records.dp_bugs.insert(self.span);
                    rap_warn!("DP bug for local {:?}", 0);
                } else {
                    for i in 0..self.arg_size {
                        if self.values[i + 1].is_ptr() && self.is_dangling(i + 1) {
                            self.bug_records.dp_bugs.insert(self.span);
                            rap_warn!("DP bug for local {:?}", i + 1);
                        }
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
        drop: usize,
        birth: usize,
        info: &SourceInfo,
        flag_inprocess: bool,
        flag_cleanup: bool,
    ) {
        //Rc drop
        if self.values[drop].is_corner_case() {
            return;
        }
        //check if there is a double free bug.
        if !flag_inprocess && self.df_check(drop, info.span, flag_cleanup) {
            return;
        }
        if self.drop_record[drop] {
            return;
        } else {
            self.drop_record[drop] = true;
        }
        //drop their alias
        if self.alias_set[drop] != drop {
            // for i in self.values[drop].alias.clone().into_iter() {
            //     if self.values[i].is_ref() {
            //         continue;
            //     }
            //     self.drop_node(i, birth, info, true);
            // }
            for i in 0..self.values.len() {
                if !self.union_is_same(drop, i) || i == drop || self.values[i].is_ref() {
                    continue;
                }
                self.drop_node(i, birth, info, true, flag_cleanup);
            }
        }
        //drop the fields of the root node.
        //alias flag is used to avoid the fields of the alias are dropped repeatly.
        if !flag_inprocess {
            for (_, field_idx) in self.values[drop].fields.clone() {
                if self.values[drop].is_tuple() && !self.values[field_idx].need_drop {
                    continue;
                }
                self.drop_node(field_idx, birth, info, false, flag_cleanup);
            }
        }
        //SCC.
        if self.values[drop].birth < birth as isize && self.values[drop].may_drop {
            self.values[drop].drop();
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
