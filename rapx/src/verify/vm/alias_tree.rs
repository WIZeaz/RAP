//! Tree-shaped alias tracking for the `Alias` hazard.
//!
//! A per-function derivation *forest*: every pointer-bearing local is a node,
//! and an edge `parent ← child` records that the child was derived from the
//! parent (reborrow, raw-pointer cast, address-of, copy). Each node carries a
//! `NodeKind` (the origin type) so the shared-XOR-mutable invariant can be
//! checked over *live* nodes sharing a common root rather than only at the
//! immediate callsite.
//!
//! The permission state machine (`Reserved`/`Active`/`Frozen`/`Disabled`) is a
//! later phase; for now `Disabled` is derived from liveness at query time.

use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Local, Operand, Rvalue, StatementKind};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

/// A node identifier (index into [`AliasTree::nodes`]).
pub(crate) type TagId = usize;

/// The origin type a node was derived from.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum NodeKind {
    /// An owned container (`Box`/`Vec`/`CString`/`NonNull`/…): the allocation's
    /// unique owner, always a tree root.
    Owned,
    /// `&mut T`.
    MutRef,
    /// `&T`.
    SharedRef,
    /// `*mut T` / `*const T` (an intermediate pointer, not itself a view).
    RawPtr,
}

/// A single node in the alias forest.
#[derive(Clone, Debug)]
pub(crate) struct AliasNode {
    pub kind: NodeKind,
    pub parent: Option<TagId>,
    /// Field projections (`ProjectionElem::Field` indices) from the parent's
    /// referent down to this pointer (e.g. `self.node.ptr` → `[node, ptr]`).
    /// Empty for whole-local pointers. Used by [`AliasTree::resolve_to_root`] to
    /// reconstruct the nested-field origin.
    pub fields: Vec<usize>,
    pub local: Local,
}

/// The per-function alias derivation forest.
#[derive(Clone, Debug)]
pub(crate) struct AliasTree {
    pub nodes: Vec<AliasNode>,
    /// The tag that `local` currently names (its most recent binding).
    tag_of_local: FxHashMap<Local, TagId>,
}

impl AliasTree {
    /// Build the derivation forest for `def_id` by scanning its MIR.
    ///
    /// Parameters are roots; every `target = <ref/cast/raw/copy> source`
    /// statement adds an edge from `source`'s tag to a new (or shared) tag for
    /// `target`. `StorageDead`/moves are *not* applied here — liveness is a
    /// query-time concern (see [`AliasTree::check_shared_xor_mutable`]).
    pub(crate) fn build<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Self {
        let body = tcx.optimized_mir(def_id);
        let mut tree = AliasTree {
            nodes: Vec::new(),
            tag_of_local: FxHashMap::default(),
        };

        for local_index in 1..=body.arg_count {
            let local = Local::from_usize(local_index);
            let ty = body.local_decls[local].ty;
            if let Some(kind) = classify(ty) {
                tree.add(kind, None, Vec::new(), local);
            }
        }

        for block in body.basic_blocks.iter() {
            for statement in &block.statements {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let (target, rvalue) = assign.as_ref();
                match rvalue {
                    // Copy/move of a *whole* pointer is the same tag, not a new
                    // node. A copy through a field projection (`_2 = (*self).next`)
                    // is a *derivation* (reads the raw field), so it falls through
                    // to the derivation arm below.
                    Rvalue::Use(Operand::Copy(place), ..)
                    | Rvalue::Use(Operand::Move(place), ..)
                    | Rvalue::CopyForDeref(place)
                        if field_projection(place).is_empty() =>
                    {
                        if let Some(tag) = tree.tag_of_local.get(&place.local).copied() {
                            tree.tag_of_local.insert(target.local, tag);
                        }
                    }
                    // True derivation: reborrow (`&mut x`), raw-pointer creation
                    // (`addr_of!(x)`), cast (`&mut → *mut`, `*mut → *const`) and
                    // field read (`(*self).next`).
                    _ => {
                        if let Some(place) =
                            crate::helpers::mir_utils::rvalue_source_place(rvalue)
                            && let Some(parent) = tree.tag_of_local.get(&place.local).copied()
                        {
                            let ty = body.local_decls[target.local].ty;
                            if let Some(kind) = classify(ty) {
                                tree.add(kind, Some(parent), field_projection(place), target.local);
                            }
                        }
                    }
                }
            }

            // Call destinations: `p = v.as_mut_ptr()` / `into_raw` /
            // `from_raw_parts` — the returned pointer derives from the first
            // argument (the receiver/pointer). An *owned* result (`Box::new`,
            // `Vec::new`, `Box::from_raw`) is a fresh owner, so it becomes a root
            // regardless of whether its first argument is a place.
            if let rustc_middle::mir::TerminatorKind::Call {
                args,
                destination,
                ..
            } = &block.terminator().kind
            {
                let dest_local = destination.local;
                let dest_ty = body.local_decls[dest_local].ty;
                if let Some(kind) = classify(dest_ty) {
                    if kind == NodeKind::Owned {
                        tree.add(kind, None, Vec::new(), dest_local);
                    } else if let Some(first_arg) = args.first()
                        && let Some(place) = first_arg.node.place()
                        && let Some(parent) = tree.tag_of_local.get(&place.local).copied()
                    {
                        tree.add(kind, Some(parent), field_projection(&place), dest_local);
                    }
                }
            }
        }

        tree
    }

    fn add(
        &mut self,
        kind: NodeKind,
        parent: Option<TagId>,
        fields: Vec<usize>,
        local: Local,
    ) -> TagId {
        let tag = self.nodes.len();
        self.nodes.push(AliasNode {
            kind,
            parent,
            fields,
            local,
        });
        self.tag_of_local.insert(local, tag);
        tag
    }

    /// The tag bound to `local`, if any.
    pub(crate) fn tag_of(&self, local: Local) -> Option<TagId> {
        self.tag_of_local.get(&local).copied()
    }

    /// Check the shared-XOR-mutable invariant when creating a view
    /// (`unique == true` for `&mut`, `false` for `&`) from `origin_tag`.
    ///
    /// Aliasing is decided by the *union* of two grouping keys:
    /// 1. **tree root** (the ultimate owned origin): catches views whose
    ///    `AllocId` differs after an owned origin is split (e.g. a slice view
    ///    and the raw pointer it was split from);
    /// 2. **allocation** (`alloc_of`): catches two independent pointers
    ///    (e.g. separate raw-pointer parameters) naming the same allocation.
    ///
    /// A conflict exists when a *different* live view shares either key and
    /// carries the opposite mutability (a live `&` against a new `&mut`, or a
    /// live `&mut` against a new `&`).
    pub(crate) fn check_shared_xor_mutable(
        &self,
        origin_tag: TagId,
        origin_alloc: Option<crate::verify::vm::state::AllocId>,
        unique: bool,
        live: &std::collections::HashSet<Local>,
        alloc_of: &impl Fn(Local) -> Option<crate::verify::vm::state::AllocId>,
    ) -> Option<String> {
        let origin_root = self.resolve_to_root(origin_tag);
        for (idx, node) in self.nodes.iter().enumerate() {
            if idx == origin_tag {
                continue;
            }
            if !live.contains(&node.local) {
                continue;
            }
            // A local that is `StorageLive` but not yet *assigned* (e.g. the
            // return-place reborrow, live from function entry) has no provenance
            // and is not a live view.
            let Some(node_alloc) = alloc_of(node.local) else {
                continue;
            };
            // Same *root path*: two nodes share a root only when one's field path
            // is a prefix of the other's (`s` overlaps `s.a`, but `s.a` does not
            // overlap `s.b`), so two independent fields of one struct are not
            // conflated.
            let node_root = self.resolve_to_root(idx);
            let same_root = origin_root.0 == node_root.0 && {
                let min_len = origin_root.1.len().min(node_root.1.len());
                origin_root.1[..min_len] == node_root.1[..min_len]
            };
            let same_alloc = Some(node_alloc) == origin_alloc;
            if !same_root && !same_alloc {
                continue;
            }
            // Only references are "views" for the invariant; raw pointers and
            // the owned root itself do not count (matching the callsite check).
            let view_mut = match node.kind {
                NodeKind::MutRef => Some(true),
                NodeKind::SharedRef => Some(false),
                _ => None,
            };
            let Some(view_mut) = view_mut else {
                continue;
            };
            let conflicts = if unique { !view_mut } else { view_mut };
            if conflicts {
                let produced = if unique { "&mut" } else { "&" };
                let live_kind = if view_mut { "&mut" } else { "&" };
                return Some(format!(
                    "producing {produced} while a live {live_kind} aliases the same data"
                ));
            }
        }
        None
    }

    /// Walk `tag`'s parent edges to the root, concatenating the `fields` of each
    /// hop. Returns the root local and the full field path (`self.node.ptr` →
    /// `(self, [node, ptr])`).
    pub(crate) fn resolve_to_root(&self, tag: TagId) -> (Local, Vec<usize>) {
        let mut cur = tag;
        let mut fields: Vec<usize> = Vec::new();
        let mut guard = 0;
        loop {
            let node = &self.nodes[cur];
            let mut combined = node.fields.clone();
            combined.extend(fields.iter().copied());
            fields = combined;
            match node.parent {
                Some(parent) => cur = parent,
                None => return (node.local, fields),
            }
            guard += 1;
            if guard > self.nodes.len() {
                return (self.nodes[cur].local, fields);
            }
        }
    }

    /// Resolve a local to its root `(root_local, field_path)` via the tree. An
    /// unmapped local resolves to itself with an empty field path.
    pub(crate) fn resolve_local_to_root(&self, local: Local) -> (usize, Vec<usize>) {
        match self.tag_of(local) {
            Some(tag) => {
                let (root, fields) = self.resolve_to_root(tag);
                (root.as_usize(), fields)
            }
            None => (local.as_usize(), Vec::new()),
        }
    }
}

/// The `Field` projection indices of `place`, in order (`Deref`/index/etc. are
/// skipped), matching `PlaceKey::fields`.
fn field_projection(place: &rustc_middle::mir::Place<'_>) -> Vec<usize> {
    place
        .projection
        .iter()
        .filter_map(|p| match p {
            rustc_middle::mir::ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
            _ => None,
        })
        .collect()
}

/// Classify a type into a [`NodeKind`], or `None` when the type is not
/// pointer-bearing (no alias-relevant node).
fn classify(ty: Ty<'_>) -> Option<NodeKind> {
    match ty.kind() {
        TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut) => Some(NodeKind::MutRef),
        TyKind::Ref(_, _, rustc_middle::ty::Mutability::Not) => Some(NodeKind::SharedRef),
        TyKind::RawPtr(_, _) => Some(NodeKind::RawPtr),
        TyKind::Adt(_, _) => Some(NodeKind::Owned),
        _ => None,
    }
}
