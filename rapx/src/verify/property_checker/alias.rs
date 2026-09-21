//! Checkers for `Alias` and `Owning` properties.
//!
//! `Alias` delegates to [`crate::verify::vm::alias::check_alias_vm`]; `Owning`
//! is a simple liveness check on the target allocation.

use crate::helpers::mir_scan::Checkpoint;
use crate::verify::contract::Property;
use crate::verify::report::CheckResult;
use crate::verify::vm::state::VmState;
use z3::Solver;

use super::PropertyChecker;

impl PropertyChecker {
    pub(super) fn check_alias<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        match crate::verify::vm::alias::check_alias_vm(vm_state, checkpoint, property) {
            crate::verify::vm::alias::VmAliasResult::Proved => CheckResult::ProvedByRule,
            crate::verify::vm::alias::VmAliasResult::Failed(_msg) => CheckResult::Failed,
            crate::verify::vm::alias::VmAliasResult::Unknown => CheckResult::Unknown,
        }
    }

    pub(super) fn check_owning<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(value) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::Unknown;
        };
        // `p` may be a pointer just derived from an owner (`Box::into_raw` /
        // `as_mut_ptr`), whose term still points at the owner's address but whose
        // own provenance slot is empty. Fall back to the owner's field provenance.
        let alloc_id = value.provenance_alloc_id().or_else(|| {
            vm_state
                .find_local_by_address(&value.term)
                .and_then(|owner| vm_state.owner_ptr_field(owner))
                .and_then(|v| v.provenance_alloc_id())
        });
        let Some(alloc_id) = alloc_id else {
            // No allocation to double-free (the pointer's provenance was not
            // materialized) — treat as safe rather than unknown.
            return CheckResult::ProvedByRule;
        };
        // Owning(p): p is the sole carrier of *p's ownership. A live `needs_drop`
        // owner whose buffer aliases `alloc_id` means a second owner will drop the
        // same allocation — a double free. The reconstructed owner (the call's
        // destination) is not a violation, so exclude it.
        let dest_local = checkpoint.destination.or_else(|| {
            let body = vm_state.tcx.optimized_mir(checkpoint.caller);
            match &body.basic_blocks[checkpoint.block].terminator().kind {
                rustc_middle::mir::TerminatorKind::Call { destination, .. } => {
                    Some(destination.local)
                }
                _ => None,
            }
        });
        // The local the `Owning(p)` argument names (e.g. `raw` in
        // `Box::from_raw(raw)`), resolved to the caller's local.
        let raw_local = property.target_place().and_then(|cp| match cp.base {
            crate::verify::contract::PlaceBase::Arg(n) => {
                checkpoint.args.get(n).and_then(|op| {
                    crate::helpers::mir_utils::operand_mir_place(op).map(|p| p.local)
                })
            }
            crate::verify::contract::PlaceBase::Local(n) => {
                Some(rustc_middle::mir::Local::from_usize(n))
            }
            crate::verify::contract::PlaceBase::Return => None,
        });
        let live = crate::verify::vm::alias_hazard::live_locals_at(
            vm_state.tcx,
            checkpoint.caller,
            checkpoint.block,
            // `Owning` fires at a call terminator; scan the whole block so a
            // `StorageDead` of a consumed parameter (`Box::into_raw(value)`) in
            // the same block still counts as dead.
            usize::MAX,
            true,
            true,
        );
        let typing_env =
            rustc_middle::ty::TypingEnv::non_body_analysis(vm_state.tcx, checkpoint.caller);
        // `p`'s term often points at the owner's address (e.g. `s.as_mut_ptr()`
        // yields a term `addr__1` for `s`). Trace it back to the owner local and
        // report a second owner directly, without needing its field provenance.
        if let Some(owner) = vm_state.find_local_by_address(&value.term) {
            if live.contains(&owner)
                && Some(owner) != dest_local
                && Some(owner) != raw_local
                && !traces_to_dest(vm_state, owner, dest_local)
            {
                let oty = vm_state.body.local_decls[owner].ty;
                if oty.needs_drop(vm_state.tcx, typing_env) {
                    return CheckResult::Failed;
                }
            }
        }
        for (local, _val) in &vm_state.locals {
            if Some(*local) == dest_local {
                continue;
            }
            if !live.contains(local) {
                continue;
            }
            let ty = vm_state.body.local_decls[*local].ty;
            if !ty.needs_drop(vm_state.tcx, typing_env) {
                continue;
            }
            // A move alias of the destination (`boxed = move dest`) is the owner
            // just rebuilt by this call. A *previous* call's owner is also a
            // shallow field but traces to a different destination.
            if traces_to_dest(vm_state, *local, dest_local) {
                continue;
            }
            for ((l, _path), val) in &vm_state.field_values {
                if *l != *local {
                    continue;
                }
                if val.provenance_alloc_id() != Some(alloc_id) {
                    continue;
                }
                return CheckResult::Failed;
            }
        }
        CheckResult::ProvedByRule
    }
}

/// Whether `local` is a move alias of `dest` (or of a local that is), following
/// the whole-place move chain (`_3 = move _4`).
fn traces_to_dest<'ctx, 'tcx>(
    vm_state: &VmState<'ctx, 'tcx>,
    mut local: rustc_middle::mir::Local,
    dest: Option<rustc_middle::mir::Local>,
) -> bool {
    let mut seen = std::collections::HashSet::new();
    loop {
        if Some(local) == dest {
            return true;
        }
        if !seen.insert(local) {
            // Defensive: a cycle in the move chain is unexpected, but stop.
            return false;
        }
        match vm_state.move_sources.get(&local) {
            Some(src) => local = *src,
            None => return false,
        }
    }
}
