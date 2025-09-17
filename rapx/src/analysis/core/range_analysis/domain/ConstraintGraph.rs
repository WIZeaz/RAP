#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unused_assignments)]
#![allow(unused_parens)]
#![allow(non_snake_case)]

use super::domain::*;
use crate::analysis::core::range_analysis::{Range, RangeType};

use crate::analysis::core::range_analysis::domain::SymbolicExpr::*;
use crate::rap_debug;
use crate::rap_info;
use crate::rap_trace;
use num_traits::Bounded;
use once_cell::sync::{Lazy, OnceCell};
// use rand::Rng;
use rustc_abi::FieldIdx;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::{def, def_id::DefId};
use rustc_index::IndexVec;
use rustc_middle::{
    mir::*,
    ty::{self, print, ScalarInt, TyCtxt},
};
use rustc_span::source_map::Spanned;
use rustc_span::sym::var;

use std::cell::RefCell;
use std::rc::Rc;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    default,
    fmt::Debug,
};
#[derive(Debug, Clone)]

pub struct ConstraintGraph<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    // Protected fields
    pub self_def_id: DefId,      // The DefId of the function being analyzed
    pub vars: VarNodes<'tcx, T>, // The variables of the source program
    pub oprs: Vec<BasicOpKind<'tcx, T>>, // The operations of the source program

    // func: Option<Function>,             // Save the last Function analyzed
    pub defmap: DefMap<'tcx>, // Map from variables to the operations that define them
    pub usemap: UseMap<'tcx>, // Map from variables to operations where variables are used
    pub symbmap: SymbMap<'tcx>, // Map from variables to operations where they appear as bounds
    pub values_branchmap: HashMap<&'tcx Place<'tcx>, ValueBranchMap<'tcx, T>>, // Store intervals, basic blocks, and branches
    constant_vector: Vec<T>, // Vector for constants from an SCC

    pub inst_rand_place_set: Vec<Place<'tcx>>,
    pub essa: DefId,
    pub ssa: DefId,
    // values_switchmap: ValuesSwitchMap<'tcx, T>, // Store intervals for switch branches
    pub index: i32,
    pub dfs: HashMap<&'tcx Place<'tcx>, i32>,
    pub root: HashMap<&'tcx Place<'tcx>, &'tcx Place<'tcx>>,
    pub in_component: HashSet<&'tcx Place<'tcx>>,
    pub components: HashMap<&'tcx Place<'tcx>, HashSet<&'tcx Place<'tcx>>>,
    pub worklist: VecDeque<&'tcx Place<'tcx>>,
    pub numAloneSCCs: usize,
    pub numSCCs: usize, // Add a stub for pre_update to resolve the missing method error.
    pub final_vars: VarNodes<'tcx, T>,
    pub arg_count: usize,
    pub rerurn_places: HashSet<&'tcx Place<'tcx>>,
    pub switchbbs: HashMap<BasicBlock, (Place<'tcx>, Place<'tcx>)>,
    pub const_func_place: HashMap<&'tcx Place<'tcx>, usize>,
}

impl<'tcx, T> ConstraintGraph<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    pub fn convert_const(c: &Const) -> Option<T> {
        T::from_const(c)
    }
    pub fn new(self_def_id: DefId, essa: DefId, ssa: DefId) -> Self {
        Self {
            self_def_id,
            vars: VarNodes::new(),
            oprs: GenOprs::new(),
            // func: None,
            defmap: DefMap::new(),
            usemap: UseMap::new(),
            symbmap: SymbMap::new(),
            values_branchmap: ValuesBranchMap::new(),
            // values_switchmap: ValuesSwitchMap::new(),
            constant_vector: Vec::new(),
            inst_rand_place_set: Vec::new(),
            essa,
            ssa,
            index: 0,
            dfs: HashMap::new(),
            root: HashMap::new(),
            in_component: HashSet::new(),
            components: HashMap::new(),
            worklist: VecDeque::new(),
            numAloneSCCs: 0,
            numSCCs: 0,
            final_vars: VarNodes::new(),
            arg_count: 0,
            rerurn_places: HashSet::new(),
            switchbbs: HashMap::new(),
            const_func_place: HashMap::new(),
        }
    }
    pub fn new_without_ssa(self_def_id: DefId) -> Self {
        Self {
            self_def_id,
            vars: VarNodes::new(),
            oprs: GenOprs::new(),
            // func: None,
            defmap: DefMap::new(),
            usemap: UseMap::new(),
            symbmap: SymbMap::new(),
            values_branchmap: ValuesBranchMap::new(),
            // values_switchmap: ValuesSwitchMap::new(),
            constant_vector: Vec::new(),
            inst_rand_place_set: Vec::new(),
            essa: self_def_id, // Assuming essa is the same as self_def_id
            ssa: self_def_id,  // Assuming ssa is the same as self_def_id
            index: 0,
            dfs: HashMap::new(),
            root: HashMap::new(),
            in_component: HashSet::new(),
            components: HashMap::new(),
            worklist: VecDeque::new(),
            numAloneSCCs: 0,
            numSCCs: 0,
            final_vars: VarNodes::new(),
            arg_count: 0,
            rerurn_places: HashSet::new(),
            switchbbs: HashMap::new(),
            const_func_place: HashMap::new(),
        }
    }
    pub fn build_final_vars(
        &mut self,
        places_map: &HashMap<Place<'tcx>, HashSet<Place<'tcx>>>,
    ) -> (VarNodes<'tcx, T>, Vec<Place<'tcx>>) {
        let mut final_vars: VarNodes<'tcx, T> = HashMap::new();
        let mut not_found: Vec<Place<'tcx>> = Vec::new();

        for (&_key_place, place_set) in places_map {
            for &place in place_set {
                let found = self.vars.iter().find(|(&p, _)| *p == place);

                if let Some((&found_place, var_node)) = found {
                    final_vars.insert(found_place, var_node.clone());
                } else {
                    not_found.push(place);
                }
            }
        }
        self.final_vars = final_vars.clone();
        (final_vars, not_found)
    }
    pub fn filter_final_vars(
        vars: &VarNodes<'tcx, T>,
        places_map: &HashMap<Place<'tcx>, HashSet<Place<'tcx>>>,
    ) -> HashMap<Place<'tcx>, Range<T>> {
        let mut final_vars = HashMap::new();

        for (&_key_place, place_set) in places_map {
            for &place in place_set {
                if let Some(var_node) = vars.get(&place) {
                    final_vars.insert(place, var_node.get_range().clone());
                }
            }
        }
        final_vars
    }
    pub fn test_and_print_all_symbolic_expressions(&self) {
        rap_info!("\n==== Testing and Printing All Symbolic Expressions ====");

        let mut places: Vec<&'tcx Place<'tcx>> = self.vars.keys().copied().collect();
        places.sort_by_key(|p| p.local.as_usize());

        for place in places {
            rap_info!("--- Place: {:?}", place);
            match self.get_symbolicexpression(place) {
                Some(sym_expr) => {
                    rap_info!("    Symbolic Expr: {}", sym_expr);
                }
                None => {
                    rap_info!("    Symbolic Expr: Could not be resolved (None returned).");
                }
            }
        }
        rap_info!("==== End of Symbolic Expression Test ====\n");
    }
    pub fn rap_print_final_vars(&self) {
        for (&key, value) in &self.final_vars {
            rap_debug!("Var: {:?}, {} ", key, value.get_range());
        }
    }
    pub fn rap_print_vars(&self) {
        for (&key, value) in &self.vars {
            rap_trace!("Var: {:?}. {} ", key, value.get_range());
        }
    }
    pub fn print_vars(&self) {
        for (&key, value) in &self.vars {
            rap_trace!("Var: {:?}. {} ", key, value.get_range());
        }
    }
    pub fn print_conponent_vars(&self) {
        rap_trace!("====print_conponent_vars====");
        for (key, value) in &self.components {
            if value.len() > 1 {
                rap_trace!("component: {:?} ", key);
                for v in value {
                    if let Some(var_node) = self.vars.get(v) {
                        rap_trace!("Var: {:?}. {} ", v, var_node.get_range());
                    } else {
                        rap_trace!("Var: {:?} not found", v);
                    }
                }
            }
        }
    }
    fn print_values_branchmap(&self) {
        for (&key, value) in &self.values_branchmap {
            rap_info!("vbm place: {:?}. {:?}\n ", key, value);
        }
    }
    fn print_symbmap(&self) {
        for (&key, value) in &self.symbmap {
            for op in value.iter() {
                if let Some(op) = self.oprs.get(*op) {
                    rap_trace!("symbmap op: {:?}. {:?}\n ", key, op);
                } else {
                    rap_trace!("symbmap op: {:?} not found\n ", op);
                }
            }
        }
    }
    fn print_defmap(&self) {
        for (key, value) in self.defmap.clone() {
            rap_trace!(
                "place: {:?} def in stmt:{:?} {:?}",
                key,
                self.oprs[value].get_type_name(),
                self.oprs[value].get_instruction()
            );
        }
    }
    fn print_compusemap(
        &self,
        component: &HashSet<&'tcx Place<'tcx>>,
        comp_use_map: &HashMap<&'tcx Place<'tcx>, HashSet<usize>>,
    ) {
        for (key, value) in comp_use_map.clone() {
            if component.contains(key) {
                for v in value {
                    rap_trace!(
                        "compusemap place: {:?} use in stmt:{:?} {:?}",
                        key,
                        self.oprs[v].get_type_name(),
                        self.oprs[v].get_instruction()
                    );
                }
            }
        }
    }
    fn print_usemap(&self) {
        for (key, value) in self.usemap.clone() {
            for v in value {
                rap_trace!(
                    "place: {:?} use in stmt:{:?} {:?}",
                    key,
                    self.oprs[v].get_type_name(),
                    self.oprs[v].get_instruction()
                );
            }
        }
    }
    // pub fn create_random_place(&mut self) -> Place<'tcx> {
    //     let mut rng = rand::rng();
    //     let random_local = Local::from_usize(rng.random_range(10000..100000));
    //     let place = Place {
    //         local: random_local,
    //         projection: ty::List::empty(),
    //     };
    //     self.inst_rand_place_set.push(place);
    //     place
    // }
    pub fn get_vars(&self) -> &VarNodes<'tcx, T> {
        &self.vars
    }
    pub fn add_varnode(&mut self, v: &'tcx Place<'tcx>) -> &mut VarNode<'tcx, T> {
        let node = VarNode::new(v);
        let node_ref: &mut VarNode<'tcx, T> = self.vars.entry(v).or_insert(node);
        self.usemap.entry(v).or_insert(HashSet::new());

        node_ref
    }

    pub fn build_graph(&mut self, body: &'tcx Body<'tcx>) {
        self.arg_count = body.arg_count;
        self.build_value_maps(body);
        for block in body.basic_blocks.indices() {
            let block_data = &body[block];
            // Traverse statements

            for statement in block_data.statements.iter() {
                self.build_operations(statement, block);
            }
            self.build_terminator(block, block_data.terminator.as_ref().unwrap());
        }

        // self.print_vars();
        // self.print_defmap();
        // self.print_usemap();
        // rap_trace!("end\n");
    }

    pub fn build_value_maps(&mut self, body: &'tcx Body<'tcx>) {
        for bb in body.basic_blocks.indices() {
            let block_data = &body[bb];
            if let Some(terminator) = &block_data.terminator {
                match &terminator.kind {
                    TerminatorKind::SwitchInt { discr, targets } => {
                        self.build_value_branch_map(body, discr, targets, bb, block_data);
                    }
                    TerminatorKind::Goto { target } => {
                        // self.build_value_goto_map(block_index, *target);
                    }
                    _ => {
                        // rap_trace!(
                        //     "BasicBlock {:?} has an unsupported terminator: {:?}",
                        //     block_index, terminator.kind
                        // );
                    }
                }
            }
        }
        // rap_trace!("value_branchmap{:?}\n", self.values_branchmap);
        // rap_trace!("varnodes{:?}\n,", self.vars);
    }

    pub fn build_value_branch_map(
        &mut self,
        body: &Body<'tcx>,
        discr: &'tcx Operand<'tcx>,
        targets: &'tcx SwitchTargets,
        block: BasicBlock,
        block_data: &'tcx BasicBlockData<'tcx>,
    ) {
        // let place1: &Place<'tcx>;
        if let Operand::Copy(place) | Operand::Move(place) = discr {
            if let Some((op1, op2, cmp_op)) = self.extract_condition(place, block_data) {
                let const_op1 = op1.constant();
                let const_op2 = op2.constant();
                match (const_op1, const_op2) {
                    (Some(c1), Some(c2)) => {}
                    (Some(c), None) | (None, Some(c)) => {
                        let const_in_left: bool;
                        let variable;
                        if const_op1.is_some() {
                            const_in_left = true;
                            variable = match op2 {
                                Operand::Copy(p) | Operand::Move(p) => p,
                                _ => panic!("Expected a place"),
                            };
                        } else {
                            const_in_left = false;
                            variable = match op1 {
                                Operand::Copy(p) | Operand::Move(p) => p,
                                _ => panic!("Expected a place"),
                            };
                        }
                        self.add_varnode(variable);
                        rap_trace!("add_vbm_varnode{:?}\n", variable.clone());

                        // let value = c.const_.try_to_scalar_int().unwrap();
                        let value = Self::convert_const(&c.const_).unwrap();
                        let const_range =
                            Range::new(value.clone(), value.clone(), RangeType::Unknown);
                        rap_trace!("cmp_op{:?}\n", cmp_op);
                        rap_trace!("const_in_left{:?}\n", const_in_left);
                        let mut true_range =
                            self.apply_comparison(value.clone(), cmp_op, true, const_in_left);
                        let mut false_range =
                            self.apply_comparison(value.clone(), cmp_op, false, const_in_left);
                        true_range.set_regular();
                        false_range.set_regular();
                        // rap_trace!("true_range{:?}\n", true_range);
                        // rap_trace!("false_range{:?}\n", false_range);
                        let target_vec = targets.all_targets();

                        let vbm = ValueBranchMap::new(
                            variable,
                            &target_vec[0],
                            &target_vec[1],
                            IntervalType::Basic(BasicInterval::new(false_range)),
                            IntervalType::Basic(BasicInterval::new(true_range)),
                        );
                        self.values_branchmap.insert(variable, vbm);
                        // self.switchbbs.insert(block, (place, variable));
                    }
                    (None, None) => {
                        let CR = Range::new(T::min_value(), T::max_value(), RangeType::Unknown);

                        let p1 = match op1 {
                            Operand::Copy(p) | Operand::Move(p) => p,
                            _ => panic!("Expected a place"),
                        };
                        let p2 = match op2 {
                            Operand::Copy(p) | Operand::Move(p) => p,
                            _ => panic!("Expected a place"),
                        };
                        let target_vec = targets.all_targets();
                        self.add_varnode(&p1);
                        rap_trace!("add_vbm_varnode{:?}\n", p1.clone());

                        self.add_varnode(&p2);
                        rap_trace!("add_vbm_varnode{:?}\n", p2.clone());
                        let flipped_cmp_op = Self::flipped_binop(cmp_op).unwrap();
                        let reversed_cmp_op = Self::reverse_binop(cmp_op).unwrap();
                        let reversed_flippedd_cmp_op =
                            Self::flipped_binop(reversed_cmp_op).unwrap();
                        let STOp1 = IntervalType::Symb(SymbInterval::new(CR.clone(), p2, cmp_op));
                        let SFOp1 =
                            IntervalType::Symb(SymbInterval::new(CR.clone(), p2, flipped_cmp_op));
                        let STOp2 =
                            IntervalType::Symb(SymbInterval::new(CR.clone(), p1, reversed_cmp_op));
                        let SFOp2 = IntervalType::Symb(SymbInterval::new(
                            CR.clone(),
                            p1,
                            reversed_flippedd_cmp_op,
                        ));
                        rap_trace!("SFOp1{:?}\n", SFOp1);
                        rap_trace!("SFOp2{:?}\n", SFOp2);
                        rap_trace!("STOp1{:?}\n", STOp1);
                        rap_trace!("STOp2{:?}\n", STOp2);
                        let vbm_1 =
                            ValueBranchMap::new(p1, &target_vec[0], &target_vec[1], SFOp1, STOp1);
                        let vbm_2 =
                            ValueBranchMap::new(p2, &target_vec[0], &target_vec[1], SFOp2, STOp2);
                        self.values_branchmap.insert(&p1, vbm_1);
                        self.values_branchmap.insert(&p2, vbm_2);
                        self.switchbbs.insert(block, (*p1, *p2));
                    }
                }
            };
        }
    }
    pub fn flipped_binop(op: BinOp) -> Option<BinOp> {
        use BinOp::*;
        Some(match op {
            Eq => Eq,
            Ne => Ne,
            Lt => Ge,
            Le => Gt,
            Gt => Le,
            Ge => Lt,
            Add => Add,
            Mul => Mul,
            BitXor => BitXor,
            BitAnd => BitAnd,
            BitOr => BitOr,
            _ => {
                return None;
            }
        })
    }
    fn reverse_binop(op: BinOp) -> Option<BinOp> {
        use BinOp::*;
        Some(match op {
            Eq => Eq,
            Ne => Ne,
            Lt => Gt,
            Le => Ge,
            Gt => Lt,
            Ge => Le,
            Add => Add,
            Mul => Mul,
            BitXor => BitXor,
            BitAnd => BitAnd,
            BitOr => BitOr,
            _ => {
                return None;
            }
        })
    }
    fn extract_condition(
        &mut self,
        place: &'tcx Place<'tcx>,
        switch_block: &'tcx BasicBlockData<'tcx>,
    ) -> Option<(&'tcx Operand<'tcx>, &'tcx Operand<'tcx>, BinOp)> {
        for stmt in &switch_block.statements {
            if let StatementKind::Assign(box (lhs, Rvalue::BinaryOp(bin_op, box (op1, op2)))) =
                &stmt.kind
            {
                if lhs == place {
                    let mut return_op1: &Operand<'tcx> = &op1;
                    let mut return_op2: &Operand<'tcx> = &op2;
                    for stmt_original in &switch_block.statements {
                        if let StatementKind::Assign(box (lhs, Rvalue::Use(OP1))) =
                            &stmt_original.kind
                        {
                            if lhs.clone() == op1.place().unwrap() {
                                return_op1 = OP1;
                            }
                        }
                    }
                    if op2.constant().is_none() {
                        for stmt_original in &switch_block.statements {
                            if let StatementKind::Assign(box (lhs, Rvalue::Use(OP2))) =
                                &stmt_original.kind
                            {
                                if lhs.clone() == op2.place().unwrap() {
                                    return_op2 = OP2;
                                }
                            }
                        }
                    }

                    return Some((return_op1, return_op2, *bin_op));
                }
            }
        }
        None
    }

    fn apply_comparison<U: IntervalArithmetic>(
        &self,
        constant: U,
        cmp_op: BinOp,
        is_true_branch: bool,
        const_in_left: bool,
    ) -> Range<U> {
        match cmp_op {
            BinOp::Lt => {
                if is_true_branch ^ const_in_left {
                    Range::new(U::min_value(), constant.sub(U::one()), RangeType::Unknown)
                } else {
                    Range::new(constant, U::max_value(), RangeType::Unknown)
                }
            }

            BinOp::Le => {
                if is_true_branch ^ const_in_left {
                    Range::new(U::min_value(), constant, RangeType::Unknown)
                } else {
                    Range::new(constant.add(U::one()), U::max_value(), RangeType::Unknown)
                }
            }

            BinOp::Gt => {
                if is_true_branch ^ const_in_left {
                    Range::new(U::min_value(), constant, RangeType::Unknown)
                } else {
                    Range::new(constant.add(U::one()), U::max_value(), RangeType::Unknown)
                }
            }

            BinOp::Ge => {
                if is_true_branch ^ const_in_left {
                    Range::new(U::min_value(), constant, RangeType::Unknown)
                } else {
                    Range::new(constant, U::max_value().sub(U::one()), RangeType::Unknown)
                }
            }

            BinOp::Eq => {
                if is_true_branch ^ const_in_left {
                    Range::new(U::min_value(), constant, RangeType::Unknown)
                } else {
                    Range::new(constant, U::max_value(), RangeType::Unknown)
                }
            }

            _ => Range::new(constant.clone(), constant.clone(), RangeType::Empty),
        }
    }

    fn build_value_goto_map(&self, block_index: BasicBlock, target: BasicBlock) {
        rap_trace!(
            "Building value map for Goto in block {:?} targeting block {:?}",
            block_index,
            target
        );
    }
    pub fn build_varnodes(&mut self) {
        // Builds VarNodes
        for (name, node) in self.vars.iter_mut() {
            let is_undefined = !self.defmap.contains_key(name);
            node.init(is_undefined);
        }
    }
    pub fn build_symbolic_intersect_map(&mut self) {
        for i in 0..self.oprs.len() {
            if let BasicOpKind::Essa(essaop) = &self.oprs[i] {
                if let IntervalType::Symb(symbi) = essaop.get_intersect() {
                    let v = symbi.get_bound();
                    self.symbmap.entry(v).or_insert_with(HashSet::new).insert(i);
                    rap_trace!("symbmap insert {:?} {:?}\n", v, essaop);
                }
            }
        }
        // rap_trace!("symbmap: {:?}", self.symbmap);
    }
    pub fn build_use_map(
        &mut self,
        component: &HashSet<&'tcx Place<'tcx>>,
    ) -> HashMap<&'tcx Place<'tcx>, HashSet<usize>> {
        // Builds use map
        let mut comp_use_map = HashMap::new();
        for &place in component {
            if let Some(uses) = self.usemap.get(place) {
                for op in uses.iter() {
                    let sink = self.oprs[*op].get_sink();
                    if component.contains(&sink) {
                        comp_use_map
                            .entry(place)
                            .or_insert_with(HashSet::new)
                            .insert(*op);
                    }
                }
            }
        }

        self.print_compusemap(component, &comp_use_map);
        comp_use_map
    }
    pub fn build_terminator(&mut self, block: BasicBlock, terminator: &'tcx Terminator<'tcx>) {
        match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                target: _,
                unwind: _,
                fn_span: _,
                call_source,
            } => {
                rap_trace!(
                    "TerminatorKind::Call in block {:?} with function {:?} destination {:?} args {:?}\n",
                    block,
                    func,
                    destination,
                    args
                );
                // Handle the call operation
                self.add_call_op(destination, args, terminator, func, block);
            }
            TerminatorKind::Return => {}
            TerminatorKind::Goto { target } => {
                rap_trace!(
                    "TerminatorKind::Goto in block {:?} targeting block {:?}\n",
                    block,
                    target
                );
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                rap_trace!(
                    "TerminatorKind::SwitchInt in block {:?} with discr {:?} and targets {:?}\n",
                    block,
                    discr,
                    targets
                );
            }
            _ => {
                rap_trace!(
                    "Unsupported terminator kind in block {:?}: {:?}",
                    block,
                    terminator.kind
                );
            }
        }
    }
    pub fn build_operations(&mut self, inst: &'tcx Statement<'tcx>, block: BasicBlock) {
        match &inst.kind {
            StatementKind::Assign(box (sink, rvalue)) => {
                match rvalue {
                    Rvalue::BinaryOp(op, box (op1, op2)) => match op {
                        BinOp::Add
                        | BinOp::Sub
                        | BinOp::Mul
                        | BinOp::Div
                        | BinOp::Rem
                        | BinOp::AddUnchecked => {
                            self.add_binary_op(sink, inst, op1, op2, *op);
                        }
                        BinOp::AddWithOverflow => {
                            self.add_binary_op(sink, inst, op1, op2, *op);
                        }
                        BinOp::SubUnchecked => {
                            self.add_binary_op(sink, inst, op1, op2, *op);
                        }
                        BinOp::SubWithOverflow => {
                            self.add_binary_op(sink, inst, op1, op2, *op);
                        }
                        BinOp::MulUnchecked => {
                            self.add_binary_op(sink, inst, op1, op2, *op);
                        }
                        BinOp::MulWithOverflow => {
                            self.add_binary_op(sink, inst, op1, op2, *op);
                        }

                        _ => {}
                    },
                    Rvalue::UnaryOp(unop, operand) => {
                        self.add_unary_op(sink, inst, operand, *unop);
                    }
                    Rvalue::Aggregate(kind, operends) => {
                        match **kind {
                            AggregateKind::Adt(def_id, _, _, _, _) => {
                                if def_id == self.essa {
                                    self.add_essa_op(sink, inst, operends, block);
                                    // rap_trace!("Adt{:?}\n", operends);
                                }
                                if def_id == self.ssa {
                                    self.add_ssa_op(sink, inst, operends);
                                    // rap_trace!("Adt{:?}\n", operends);
                                }
                            }
                            _ => {}
                        }
                    }
                    Rvalue::Use(operend) => {
                        self.add_use_op(sink, inst, operend);
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
    // ... inside your struct impl ...

    /// Adds a function call operation to the graph.
    fn add_call_op(
        &mut self,
        sink: &'tcx Place<'tcx>,
        args: &'tcx Box<[Spanned<Operand<'tcx>>]>,
        terminator: &'tcx Terminator<'tcx>,
        func: &'tcx Operand<'tcx>,
        block: BasicBlock,
    ) {
        rap_trace!("add_call_op for sink: {:?} {:?}\n", sink, terminator);
        let sink_node = self.add_varnode(&sink);

        // Convert Operand arguments to Place arguments.
        // An Operand can be a Constant or a moved/copied Place.
        // We only care about Places for our analysis.
        let mut func_def_id = None;
        if let Operand::Constant(box const_operand) = func {
            let fn_ty = const_operand.ty();
            if let ty::TyKind::FnDef(def_id, _substs) = fn_ty.kind() {
                // Found the DefId for a direct function call!
                func_def_id = Some(def_id);
            }
        }

        if let Some(def_id) = func_def_id {
            rap_trace!(
                "TerminatorKind::Call in block {:?} with DefId {:?}\n",
                block,
                def_id
            );
            // You can now use the def_id
        } else {
            rap_trace!(
                "TerminatorKind::Call in block {:?} is an indirect call (e.g., function pointer)\n",
                block
            );
            // This handles cases where the call is not a direct one,
            // such as calling a function pointer stored in a variable.
        }
        let mut constant_count = 0 as usize;
        let arg_count = args.len();
        let mut arg_operands: Vec<Operand<'tcx>> = Vec::new();
        for op in args.iter() {
            match &op.node {
                Operand::Copy(place) | Operand::Move(place) => {
                    arg_operands.push(op.node.clone());

                    self.add_varnode(place);
                    self.usemap
                        .entry(place)
                        .or_default()
                        .insert(self.oprs.len());
                }

                Operand::Constant(_) => {
                    // If it's not a Place, we can still add it as an operand.
                    // This is useful for constants or other non-place operands.
                    arg_operands.push(op.node.clone());
                    constant_count += 1;
                }
            }
        }
        {
            let bi = BasicInterval::new(Range::default(T::min_value()));

            let call_op = CallOp::new(
                IntervalType::Basic(bi),
                &sink,
                terminator, // Pass the allocated dummy statement
                arg_operands,
                *func_def_id.unwrap(), // Use the DefId if available
            );
            rap_debug!("call_op: {:?}\n", call_op);
            let bop_index = self.oprs.len();

            // Insert the operation into the graph.
            self.oprs.push(BasicOpKind::Call(call_op));

            // Insert this definition in defmap
            self.defmap.insert(&sink, bop_index);
            if constant_count == arg_count {
                rap_trace!("all args are constants\n");
                self.const_func_place.insert(&sink, bop_index);
            }
        }
    }
    fn add_ssa_op(
        &mut self,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        operands: &'tcx IndexVec<FieldIdx, Operand<'tcx>>,
    ) {
        rap_trace!("ssa_op{:?}\n", inst);

        let sink_node = self.add_varnode(sink);
        rap_trace!("addsink_in_ssa_op{:?}\n", sink_node);

        let BI: BasicInterval<T> = BasicInterval::new(Range::default(T::min_value()));
        let mut phiop = PhiOp::new(IntervalType::Basic(BI), sink, inst, 0);
        let bop_index = self.oprs.len();
        for i in 0..operands.len() {
            let source = match &operands[FieldIdx::from_usize(i)] {
                Operand::Copy(place) | Operand::Move(place) => {
                    self.add_varnode(place);
                    Some(place)
                }
                _ => None,
            };
            if let Some(source) = source {
                self.add_varnode(source);
                phiop.add_source(source);
                rap_trace!("addvar_in_ssa_op{:?}\n", source);
                self.usemap.entry(source).or_default().insert(bop_index);
            }
        }
        // Insert the operation in the graph.

        self.oprs.push(BasicOpKind::Phi(phiop));

        // Insert this definition in defmap

        self.defmap.insert(sink, bop_index);
    }
    fn add_use_op(
        &mut self,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        op: &'tcx Operand<'tcx>,
    ) {
        rap_trace!("use_op{:?}\n", inst);

        let BI: BasicInterval<T> = BasicInterval::new(Range::default(T::min_value()));
        let mut source: Option<&'tcx Place<'tcx>> = None;

        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                if sink.local == RETURN_PLACE && sink.projection.is_empty() {
                    self.rerurn_places.insert(place);
                    let sink_node = self.add_varnode(sink);

                    rap_debug!("add_return_place{:?}\n", place);
                } else {
                    self.add_varnode(place);
                    source = Some(place);
                    if let Some(source) = source {
                        rap_trace!("addvar_in_use_op{:?}\n", source);
                        let sink_node = self.add_varnode(sink);

                        let useop =
                            UseOp::new(IntervalType::Basic(BI), sink, inst, Some(source), None);
                        // Insert the operation in the graph.
                        let bop_index = self.oprs.len();

                        self.oprs.push(BasicOpKind::Use(useop));
                        // Insert this definition in defmap
                        self.usemap.entry(source).or_default().insert(bop_index);

                        self.defmap.insert(sink, bop_index);
                    }
                }
            }
            Operand::Constant(constant) => {
                rap_trace!("add_constant_op{:?}\n", inst);
                let Some(c) = op.constant() else {
                    rap_trace!("add_constant_op: constant is None\n");
                    return;
                };
                let useop = UseOp::new(IntervalType::Basic(BI), sink, inst, None, Some(c.const_));
                // Insert the operation in the graph.
                let bop_index = self.oprs.len();

                self.oprs.push(BasicOpKind::Use(useop));
                // Insert this definition in defmap

                self.defmap.insert(sink, bop_index);
                let sink_node = self.add_varnode(sink);

                if let Some(value) = Self::convert_const(&c.const_) {
                    sink_node.set_range(Range::new(
                        value.clone(),
                        value.clone(),
                        RangeType::Regular,
                    ));
                    rap_trace!("set_const {:?} value: {:?}\n", sink_node, value);
                    // rap_trace!("sinknoderange: {:?}\n", sink_node.get_range());
                } else {
                    sink_node.set_range(Range::default(T::min_value()));
                };
            }
        }
    }
    fn add_essa_op(
        &mut self,
        sink: &'tcx Place<'tcx>,

        inst: &'tcx Statement<'tcx>,
        operands: &'tcx IndexVec<FieldIdx, Operand<'tcx>>,
        block: BasicBlock,
    ) {
        // rap_trace!("essa_op{:?}\n", inst);
        let sink_node = self.add_varnode(sink);
        // rap_trace!("addsink_in_essa_op {:?}\n", sink_node);

        // let BI: BasicInterval<T> = BasicInterval::new(Range::default(T::min_value()));
        let loc_1: usize = 0;
        let loc_2: usize = 1;
        let source1 = match &operands[FieldIdx::from_usize(loc_1)] {
            Operand::Copy(place) | Operand::Move(place) => {
                self.add_varnode(place);
                Some(place)
            }
            _ => None,
        };
        let op = &operands[FieldIdx::from_usize(loc_2)];
        let bop_index = self.oprs.len();

        let BI: IntervalType<'_, T>;
        if let Operand::Constant(c) = op {
            let vbm = self.values_branchmap.get(source1.unwrap()).unwrap();
            if block == *vbm.get_bb_true() {
                rap_trace!("essa_op true branch{:?}\n", block);
                BI = vbm.get_itv_t();
            } else {
                rap_trace!("essa_op false branch{:?}\n", block);
                BI = vbm.get_itv_f();
            }
            self.usemap
                .entry(source1.unwrap())
                .or_default()
                .insert(bop_index);

            let essaop = EssaOp::new(BI, sink, inst, source1.unwrap(), 0, false);
            rap_trace!(
                "addvar_in_essa_op {:?} from const {:?}\n",
                essaop,
                source1.unwrap()
            );

            // Insert the operation in the graph.

            self.oprs.push(BasicOpKind::Essa(essaop));
            // Insert this definition in defmap
            // self.usemap
            //     .entry(source1.unwrap())
            //     .or_default()
            //     .insert(bop_index);

            self.defmap.insert(sink, bop_index);
        } else {
            let vbm = self.values_branchmap.get(source1.unwrap()).unwrap();
            if block == *vbm.get_bb_true() {
                rap_trace!("essa_op true branch{:?}\n", block);
                BI = vbm.get_itv_t();
            } else {
                rap_trace!("essa_op false branch{:?}\n", block);
                BI = vbm.get_itv_f();
            }
            let source2 = match op {
                Operand::Copy(place) | Operand::Move(place) => {
                    self.add_varnode(place);
                    Some(place)
                }
                _ => None,
            };
            self.usemap
                .entry(source1.unwrap())
                .or_default()
                .insert(bop_index);
            // self.usemap
            // .entry(source2.unwrap())
            // .or_default()
            // .insert(bop_index);
            let essaop = EssaOp::new(BI, sink, inst, source1.unwrap(), 0, true);
            // Insert the operation in the graph.
            rap_trace!(
                "addvar_in_essa_op {:?} from {:?}\n",
                essaop,
                source1.unwrap()
            );

            self.oprs.push(BasicOpKind::Essa(essaop));
            // Insert this definition in defmap
            // self.usemap
            //     .entry(source1.unwrap())
            //     .or_default()
            //     .insert(bop_index);

            self.defmap.insert(sink, bop_index);
        }
    }
    fn add_unary_op(
        &mut self,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        operand: &'tcx Operand<'tcx>,
        op: UnOp,
    ) {
        rap_trace!("unary_op{:?}\n", inst);

        let sink_node = self.add_varnode(sink);
        rap_trace!("addsink_in_unary_op{:?}\n", sink_node);

        let BI: BasicInterval<T> = BasicInterval::new(Range::default(T::min_value()));
        let loc_1: usize = 0;

        let source = match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.add_varnode(place);
                Some(place)
            }
            _ => None,
        };

        rap_trace!("addvar_in_unary_op{:?}\n", source.unwrap());
        self.add_varnode(&source.unwrap());

        let unaryop = UnaryOp::new(IntervalType::Basic(BI), sink, inst, source.unwrap(), op);
        // Insert the operation in the graph.
        let bop_index = self.oprs.len();

        self.oprs.push(BasicOpKind::Unary(unaryop));
        // Insert this definition in defmap

        self.defmap.insert(sink, bop_index);
    }

    fn add_binary_op(
        &mut self,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        op1: &'tcx Operand<'tcx>,
        op2: &'tcx Operand<'tcx>,
        bin_op: BinOp,
    ) {
        rap_trace!("binary_op{:?}\n", inst);
        let sink_node = self.add_varnode(sink);
        rap_trace!("addsink_in_binary_op{:?}\n", sink_node);
        let bop_index = self.oprs.len();
        let BI: BasicInterval<T> = BasicInterval::new(Range::default(T::min_value()));

        let source1_place = match op1 {
            Operand::Copy(place) | Operand::Move(place) => {
                self.add_varnode(place);
                rap_trace!("addvar_in_binary_op{:?}\n", place);

                Some(place)
            }
            Operand::Constant(_) => None,
        };

        match op2 {
            Operand::Copy(place) | Operand::Move(place) => {
                self.add_varnode(place);
                rap_trace!("addvar_in_binary_op{:?}\n", place);

                let source2_place = Some(place);
                let BOP = BinaryOp::new(
                    IntervalType::Basic(BI),
                    sink,
                    inst,
                    source1_place,
                    source2_place,
                    None,
                    bin_op.clone(),
                );
                self.oprs.push(BasicOpKind::Binary(BOP));
                // let bop_ref = unsafe { &*(self.oprs.last().unwrap() as *const BasicOp<'tcx, T>) };
                self.defmap.insert(sink, bop_index);
                if let Some(place) = source1_place {
                    self.usemap.entry(place).or_default().insert(bop_index);
                }

                if let Some(place) = source2_place {
                    self.usemap.entry(place).or_default().insert(bop_index);
                }
            }
            Operand::Constant(c) => {
                // let const_value = Self::convert_const(&c.const_).unwrap();
                let BOP = BinaryOp::new(
                    IntervalType::Basic(BI),
                    sink,
                    inst,
                    source1_place,
                    None,
                    Some(c.const_),
                    bin_op.clone(),
                );
                self.oprs.push(BasicOpKind::Binary(BOP));
                // let bop_ref = unsafe { &*(self.oprs.last().unwrap() as *const BasicOp<'tcx, T>) };
                self.defmap.insert(sink, bop_index);
                if let Some(place) = source1_place {
                    self.usemap.entry(place).or_default().insert(bop_index);
                }
            }
        };

        // rap_trace!("varnodes{:?}\n", self.vars);
        // rap_trace!("defmap{:?}\n", self.defmap);
        // rap_trace!("usemap{:?}\n", self.usemap);
        // rap_trace!("{:?}add_binary_op{:?}\n", inst,sink);
        // ...
    }
    fn fix_intersects(&mut self, component: &HashSet<&'tcx Place<'tcx>>) {
        for &place in component.iter() {
            // node.fix_intersects();
            if let Some(sit) = self.symbmap.get_mut(place) {
                let node = self.vars.get(place).unwrap();

                for &op in sit.iter() {
                    let op = &mut self.oprs[op];
                    let sinknode = self.vars.get(op.get_sink()).unwrap();

                    op.op_fix_intersects(node, sinknode);
                }
            }
        }
    }
    pub fn widen(
        &mut self,
        op: usize,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) -> bool {
        // use crate::range_util::{get_first_less_from_vector, get_first_greater_from_vector};
        // assert!(!constant_vector.is_empty(), "Invalid constant vector");
        let op_kind = &self.oprs[op];
        let sink = op_kind.get_sink();
        let old_interval = self.vars.get(sink).unwrap().get_range().clone();

        // HERE IS THE SPECIALIZATION:
        // We check the operation type and call the appropriate eval function.
        let estimated_interval = match op_kind {
            BasicOpKind::Call(call_op) => {
                // For a call, use the special inter-procedural eval.
                call_op.eval_call(&self.vars, cg_map, vars_map)
            }
            _ => {
                // For all other operations, use the simple, generic eval.
                op_kind.eval(&self.vars)
            }
        };
        let old_lower = old_interval.get_lower();
        let old_upper = old_interval.get_upper();
        let new_lower = estimated_interval.get_lower();
        let new_upper = estimated_interval.get_upper();
        // op.set_intersect(estimated_interval.clone());

        // let nlconstant = get_first_less_from_vector(constant_vector, new_lower);
        // let nuconstant = get_first_greater_from_vector(constant_vector, new_upper);
        // let nlconstant = constant_vector
        //     .iter()
        //     .find(|&&c| c <= new_lower)
        //     .cloned()
        //     .unwrap_or(T::min_value());
        // let nuconstant = constant_vector
        //     .iter()
        //     .find(|&&c| c >= new_upper)
        //     .cloned()
        //     .unwrap_or(T::max_value());

        let updated = if old_interval.is_unknown() {
            estimated_interval.clone()
        } else if new_lower < old_lower && new_upper > old_upper {
            Range::new(T::min_value(), T::max_value(), RangeType::Regular)
        } else if new_lower < old_lower {
            Range::new(T::min_value(), old_upper.clone(), RangeType::Regular)
        } else if new_upper > old_upper {
            Range::new(old_lower.clone(), T::max_value(), RangeType::Regular)
        } else {
            old_interval.clone()
        };

        self.vars.get_mut(sink).unwrap().set_range(updated.clone());
        rap_trace!(
            "WIDEN in {} set {:?}: E {} U {} {} -> {}",
            op,
            sink,
            estimated_interval,
            updated,
            old_interval,
            updated
        );

        old_interval != updated
    }
    pub fn narrow(
        &mut self,
        op: usize,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) -> bool {
        let op_kind = &self.oprs[op];
        let sink = op_kind.get_sink();
        let old_interval = self.vars.get(sink).unwrap().get_range().clone();

        // SPECIALIZATION for narrow:
        let estimated_interval = match op_kind {
            BasicOpKind::Call(call_op) => {
                // For a call, use the special inter-procedural eval.
                call_op.eval_call(&self.vars, cg_map, vars_map)
            }
            _ => {
                // For all other operations, use the simple, generic eval.
                op_kind.eval(&self.vars)
            }
        };
        let old_lower = old_interval.get_lower();
        let old_upper = old_interval.get_upper();
        let new_lower = estimated_interval.get_lower();
        let new_upper = estimated_interval.get_upper();
        // op.set_intersect(estimated_interval.clone());
        // let mut hasChanged = false;
        let mut final_lower = old_lower.clone();
        let mut final_upper = old_upper.clone();
        if old_lower.clone() == T::min_value() && new_lower.clone() > T::min_value() {
            final_lower = new_lower.clone();
            // tightened = Range::new(new_lower.clone(), old_upper.clone(), RangeType::Regular);
            // hasChanged = true;
        } else if old_lower.clone() <= new_lower.clone() {
            final_lower = new_lower.clone();

            // tightened = Range::new(new_lower.clone(), old_upper.clone(), RangeType::Regular);
            // hasChanged = true;
        };
        if old_upper.clone() == T::max_value() && new_upper.clone() < T::max_value() {
            final_upper = new_upper.clone();
            // tightened = Range::new(old_lower.clone(), new_upper.clone(), RangeType::Regular);
            // hasChanged = true;
        } else if old_upper.clone() >= new_upper.clone() {
            final_upper = new_upper.clone();
            // tightened = Range::new(old_lower.clone(), new_upper.clone(), RangeType::Regular);
            // hasChanged = true;
        }
        let tightened = Range::new(final_lower, final_upper, RangeType::Regular);

        self.vars
            .get_mut(sink)
            .unwrap()
            .set_range(tightened.clone());
        rap_trace!(
            "NARROW in {} set {:?}: E {} U {} {} -> {}",
            op,
            sink,
            estimated_interval,
            tightened,
            old_interval,
            tightened
        );
        let hasChanged = old_interval != tightened;

        hasChanged
    }

    fn pre_update(
        &mut self,
        comp_use_map: &HashMap<&'tcx Place<'tcx>, HashSet<usize>>,
        entry_points: &HashSet<&'tcx Place<'tcx>>,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) {
        let mut worklist: Vec<&'tcx Place<'tcx>> = entry_points.iter().cloned().collect();

        while let Some(place) = worklist.pop() {
            if let Some(op_set) = comp_use_map.get(place) {
                for &op in op_set {
                    if self.widen(op, cg_map, vars_map) {
                        let sink = self.oprs[op].get_sink();
                        rap_trace!("W {:?}\n", sink);
                        // let sink_node = self.vars.get_mut(sink).unwrap();
                        worklist.push(sink);
                    }
                }
            }
        }
    }

    fn pos_update(
        &mut self,
        comp_use_map: &HashMap<&'tcx Place<'tcx>, HashSet<usize>>,
        entry_points: &HashSet<&'tcx Place<'tcx>>,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) {
        let mut worklist: Vec<&'tcx Place<'tcx>> = entry_points.iter().cloned().collect();
        let mut iteration = 0;
        while let Some(place) = worklist.pop() {
            iteration += 1;
            if (iteration > 1000) {
                rap_trace!("Iteration limit reached, breaking out of pos_update\n");
                break;
            }

            if let Some(op_set) = comp_use_map.get(place) {
                for &op in op_set {
                    if self.narrow(op, cg_map, vars_map) {
                        let sink = self.oprs[op].get_sink();
                        rap_trace!("N {:?}\n", sink);

                        // let sink_node = self.vars.get_mut(sink).unwrap();
                        worklist.push(sink);
                    }
                }
            }
        }
        rap_trace!("pos_update finished after {} iterations\n", iteration);
    }
    fn generate_active_vars(
        &mut self,
        component: &HashSet<&'tcx Place<'tcx>>,
        active_vars: &mut HashSet<&'tcx Place<'tcx>>,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) {
        for place in component {
            let node = self.vars.get(place).unwrap();
        }
    }
    fn generate_entry_points(
        &mut self,
        component: &HashSet<&'tcx Place<'tcx>>,
        entry_points: &mut HashSet<&'tcx Place<'tcx>>,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) {
        for &place in component {
            let op = self.defmap.get(place).unwrap();
            if let BasicOpKind::Essa(essaop) = &mut self.oprs[*op] {
                if essaop.is_unresolved() {
                    let source = essaop.get_source();
                    let new_range = essaop.eval(&self.vars);
                    let sink_node = self.vars.get_mut(source).unwrap();
                    sink_node.set_range(new_range);
                }
                essaop.mark_resolved();
            }
            if (!self.vars[place].get_range().is_unknown()) {
                entry_points.insert(place);
            }
        }
    }
    fn propagate_to_next_scc(
        &mut self,
        component: &HashSet<&'tcx Place<'tcx>>,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) {
        for &place in component.iter() {
            let node = self.vars.get_mut(place).unwrap();
            for &op in self.usemap.get(place).unwrap().iter() {
                let op_kind = &mut self.oprs[op];
                let sink = op_kind.get_sink();
                if !component.contains(sink) {
                    let new_range = op_kind.eval(&self.vars);
                    let new_range = match op_kind {
                        BasicOpKind::Call(call_op) => {
                            call_op.eval_call(&self.vars, cg_map, vars_map)
                        }
                        _ => {
                            // For all other operations, use the simple, generic eval.
                            op_kind.eval(&self.vars)
                        }
                    };
                    let sink_node = self.vars.get_mut(sink).unwrap();
                    rap_trace!(
                        "prop component {:?} set {} to {:?} through {:?}\n",
                        component,
                        new_range,
                        sink,
                        op_kind.get_instruction()
                    );
                    sink_node.set_range(new_range);
                    // if self.symbmap.contains_key(sink) {
                    //     let symb_set = self.symbmap.get_mut(sink).unwrap();
                    //     symb_set.insert(op.get_index());
                    // }
                    if let BasicOpKind::Essa(essaop) = op_kind {
                        if essaop.get_intersect().get_range().is_unknown() {
                            essaop.mark_unresolved();
                        }
                    }
                }
            }
        }
    }
    pub fn solve_const_func_call(
        &mut self,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) {
        for (&sink, op) in &self.const_func_place {
            rap_trace!(
                "solve_const_func_call for sink {:?} with opset {:?}\n",
                sink,
                op
            );
            if let BasicOpKind::Call(call_op) = &self.oprs[*op] {
                let new_range = call_op.eval_call(&self.vars, cg_map, vars_map);
                rap_trace!("Setting range for {:?} to {:?}\n", sink, new_range);
                self.vars.get_mut(sink).unwrap().set_range(new_range);
            }
        }
    }
    pub fn store_vars(&mut self, varnodes_vec: &mut Vec<RefCell<VarNodes<'tcx, T>>>) {
        rap_trace!("Storing vars\n");
        let old_vars = self.vars.clone();
        varnodes_vec.push(RefCell::new(old_vars));
    }
    pub fn reset_vars(&mut self, varnodes_vec: &mut Vec<RefCell<VarNodes<'tcx, T>>>) {
        rap_trace!("Resetting vars\n");
        self.vars = varnodes_vec[0].borrow_mut().clone();
    }
    pub fn find_intervals(
        &mut self,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) {
        // let scc_list = Nuutila::new(&self.vars, &self.usemap, &self.symbmap,false,&self.oprs);
        // self.print_vars();

        self.solve_const_func_call(cg_map, vars_map);
        self.numSCCs = self.worklist.len();
        let mut seen = HashSet::new();
        let mut components = Vec::new();

        for &place in self.worklist.iter().rev() {
            if seen.contains(place) {
                continue;
            }

            if let Some(component) = self.components.get(place) {
                for &p in component {
                    seen.insert(p);
                }

                components.push(component.clone());
            }
        }
        rap_trace!("TOLO:{:?}\n", components);

        for component in components {
            rap_trace!("===start component {:?}===\n", component);
            if component.len() == 1 {
                self.numAloneSCCs += 1;

                self.fix_intersects(&component);

                let variable: &Place<'tcx> = *component.iter().next().unwrap();
                let varnode = self.vars.get_mut(variable).unwrap();
                if varnode.get_range().is_unknown() {
                    varnode.set_default();
                }
            } else {
                // self.pre_update(&comp_use_map, &entry_points);
                let comp_use_map = self.build_use_map(&component);
                // build_constant_vec(&component, &self.oprs, &mut self.constant_vec);
                let mut entry_points = HashSet::new();
                // self.print_vars();

                self.generate_entry_points(&component, &mut entry_points, cg_map, vars_map);
                rap_trace!("entry_points {:?}  \n", entry_points);
                // rap_trace!("comp_use_map {:?}  \n ", comp_use_map);
                self.pre_update(&comp_use_map, &entry_points, cg_map, vars_map);
                self.fix_intersects(&component);

                // for &variable in &component {
                //     let varnode = self.vars.get_mut(variable).unwrap();
                //     if varnode.get_range().is_unknown() {
                //         varnode.set_default();
                //     }
                // }

                let mut active_vars = HashSet::new();
                self.generate_active_vars(&component, &mut active_vars, cg_map, vars_map);
                self.pos_update(&comp_use_map, &entry_points, cg_map, vars_map);
            }
            self.propagate_to_next_scc(&component, cg_map, vars_map);
        }
        self.merge_return_places();
        let Some(varnodes_vec) = vars_map.get_mut(&self.self_def_id) else {
            rap_trace!(
                "No variable map entry for this function {:?}, skipping Nuutila\n",
                self.self_def_id
            );
            return;
        };
        self.store_vars(varnodes_vec);
    }
    pub fn merge_return_places(&mut self) {
        rap_trace!("====Merging return places====\n");
        for &place in self.rerurn_places.iter() {
            rap_debug!("merging return place {:?}\n", place);
            let mut merged_range = Range::default(T::min_value());
            if let Some(opset) = self.vars.get(place) {
                merged_range = merged_range.unionwith(opset.get_range());
            }
            if let Some(return_node) = self.vars.get_mut(&Place::return_place()) {
                rap_debug!("Assigning final merged range {} to _0", merged_range);
                return_node.set_range(merged_range);
            } else {
                // This case is unlikely for functions that return a value, as `_0`
                // should have been created during the initial graph build.
                // We add a trace message for robustness.
                rap_trace!("Warning: RETURN_PLACE (_0) not found in self.vars. Cannot assign merged return range.");
            }
        }
    }

    pub fn add_control_dependence_edges(&mut self) {
        rap_trace!("====Add control dependence edges====\n");
        self.print_symbmap();
        for (&place, opset) in self.symbmap.iter() {
            for &op in opset.iter() {
                let bop_index = self.oprs.len();
                let opkind = &self.oprs[op];
                let control_edge = ControlDep::new(
                    IntervalType::Basic(BasicInterval::default()),
                    opkind.get_sink(),
                    opkind.get_instruction().unwrap(),
                    place,
                );
                rap_trace!(
                    "Adding control_edge {:?} for place {:?} at index {}\n",
                    control_edge,
                    place,
                    bop_index
                );
                self.oprs.push(BasicOpKind::ControlDep(control_edge));
                self.usemap.entry(place).or_default().insert(bop_index);
            }
        }
    }
    pub fn del_control_dependence_edges(&mut self) {
        rap_trace!("====Delete control dependence edges====\n");

        let mut remove_from = self.oprs.len();
        while remove_from > 0 {
            match &self.oprs[remove_from - 1] {
                BasicOpKind::ControlDep(dep) => {
                    let place = dep.source;
                    rap_trace!(
                        "removing control_edge at idx {}: {:?}\n",
                        remove_from - 1,
                        dep
                    );
                    if let Some(set) = self.usemap.get_mut(&place) {
                        set.remove(&(remove_from - 1));
                        if set.is_empty() {
                            self.usemap.remove(&place);
                        }
                    }
                    remove_from -= 1;
                }
                _ => break,
            }
        }

        self.oprs.truncate(remove_from);
    }

    pub fn build_nuutila(&mut self, single: bool) {
        rap_trace!("====Building graph====\n");
        self.print_usemap();
        self.build_symbolic_intersect_map();

        if single {
        } else {
            for place in self.vars.keys().copied() {
                self.dfs.insert(place, -1);
            }

            self.add_control_dependence_edges();

            let places: Vec<_> = self.vars.keys().copied().collect();
            rap_trace!("places{:?}\n", places);
            for place in places {
                if self.dfs[&place] < 0 {
                    rap_trace!("start place{:?}\n", place);
                    let mut stack = Vec::new();
                    self.visit(place, &mut stack);
                }
            }

            self.del_control_dependence_edges();
        }
        rap_trace!("components{:?}\n", self.components);
        rap_trace!("worklist{:?}\n", self.worklist);
        rap_trace!("dfs{:?}\n", self.dfs);
    }
    pub fn visit(&mut self, place: &'tcx Place<'tcx>, stack: &mut Vec<&'tcx Place<'tcx>>) {
        self.dfs.entry(place).and_modify(|v| *v = self.index);
        self.index += 1;
        self.root.insert(place, place);
        let uses = self.usemap.get(place).unwrap().clone();
        for op in uses {
            let name = self.oprs[op].get_sink();
            rap_trace!("place {:?} get name{:?}\n", place, name);
            if self.dfs.get(name).copied().unwrap_or(-1) < 0 {
                self.visit(name, stack);
            }

            if (!self.in_component.contains(name)
                && self.dfs[self.root[place]] >= self.dfs[self.root[name]])
            {
                *self.root.get_mut(place).unwrap() = self.root.get(name).copied().unwrap();

                // let weq = self.root.get(place)
            }
        }

        if self.root.get(place).copied().unwrap() == place {
            self.worklist.push_back(place);

            let mut scc = HashSet::new();
            scc.insert(place);

            self.in_component.insert(place);

            while let Some(top) = stack.last() {
                if self.dfs.get(top).copied().unwrap_or(-1) > self.dfs.get(place).copied().unwrap()
                {
                    let node = stack.pop().unwrap();
                    self.in_component.insert(node);

                    scc.insert(node);
                } else {
                    break;
                }
            }

            self.components.insert(place, scc);
        } else {
            stack.push(place);
        }
    }
    pub fn get_symbolicexpression(&self, place: &'tcx Place<'tcx>) -> Option<SymbolicExpr<'tcx>> {
        let mut memo: HashMap<&'tcx Place<'tcx>, Option<SymbolicExpr<'tcx>>> = HashMap::new();
        let mut in_progress: HashSet<&'tcx Place<'tcx>> = HashSet::new();

        self.get_symbolic_expression_recursive(place, &mut memo, &mut in_progress)
    }

    fn get_symbolic_expression_recursive(
        &self,
        place: &'tcx Place<'tcx>,
        memo: &mut HashMap<&'tcx Place<'tcx>, Option<SymbolicExpr<'tcx>>>,
        in_progress: &mut HashSet<&'tcx Place<'tcx>>,
    ) -> Option<SymbolicExpr<'tcx>> {
        if memo.contains_key(place) {
            return memo.get(place).cloned().unwrap();
        }

        if !in_progress.insert(place) {
            rap_trace!("Cyclic dependency detected for place: {:?}", place);
            let expr = Some(SymbolicExpr::Unknown(UnknownReason::CyclicDependency));
            memo.insert(place, expr.clone());
            return expr;
        }

        let result = if place.projection.is_empty() {
            if let Some(&op_idx) = self.defmap.get(place) {
                let op_kind = &self.oprs[op_idx];
                self.op_kind_to_symbolic_expr(op_kind, memo, in_progress)
            } else if place.local.as_usize() > 0 {
                rap_trace!(
                    "Place {:?} not found in defmap, assuming it's an argument.",
                    place
                );
                Some(SymbolicExpr::Argument(*place))
            } else {
                let op_idx = self.defmap.get(place);
                let op_kind = &self.oprs[*op_idx.unwrap()];

                rap_trace!("Local {:?} not defined by an operation and not considered an argument. Returning Unknown.", place);
                Some(SymbolicExpr::Unknown(UnknownReason::CyclicDependency))
            }
        } else {
            let mut current_expr =
                match self.get_symbolic_expression_recursive(place, memo, in_progress) {
                    Some(e) => e,
                    None => {
                        in_progress.remove(place);
                        memo.insert(place, None);
                        return None;
                    }
                };

            for proj_elem in place.projection.iter() {
                match proj_elem {
                    PlaceElem::Deref => {
                        // 解引用操作：`*expr`
                        current_expr = SymbolicExpr::Deref(Box::new(current_expr));
                    }
                    PlaceElem::Field(field_idx, _ty) => {
                        rap_trace!("Unsupported PlaceElem::Field {:?} at {:?}. Returning Unknown for SymbolicExpr.", field_idx, place);
                        in_progress.remove(place);
                        memo.insert(
                            place,
                            Some(SymbolicExpr::Unknown(UnknownReason::CyclicDependency)),
                        );
                        return Some(SymbolicExpr::Unknown(UnknownReason::CyclicDependency));
                    }
                    PlaceElem::Index(index_place) => {
                        // let index_expr = match self.get_symbolic_expression_recursive(index_place, memo, in_progress) {
                        //     Some(e) => e,
                        //     None => {
                        //         rap_trace!("Could not resolve index place {:?} for projected place {:?}. Returning Unknown.", index_place, place);
                        //         in_progress.remove(place);
                        //         memo.insert(place, Some(SymbolicExpr::Unknown(UnknownReason::CyclicDependency)));
                        //         return Some(SymbolicExpr::Unknown(UnknownReason::CyclicDependency));
                        //     }
                        // };
                        // current_expr = SymbolicExpr::Index {
                        //     base: Box::new(current_expr),
                        //     index: Box::new(index_expr),
                        // };
                        return Some(SymbolicExpr::Unknown(UnknownReason::Unsupported));
                    }
                    PlaceElem::ConstantIndex {
                        offset,
                        min_length,
                        from_end,
                    } => {
                        rap_trace!("Unsupported PlaceElem::ConstantIndex at {:?}. Requires TyCtxt to create Const<'tcx>. Returning Unknown.", place);
                        in_progress.remove(place);
                        memo.insert(
                            place,
                            Some(SymbolicExpr::Unknown(UnknownReason::CyclicDependency)),
                        );
                        return Some(SymbolicExpr::Unknown(UnknownReason::CyclicDependency));
                    }

                    _ => {
                        rap_trace!("Unsupported PlaceElem kind at {:?}. Cannot convert to SymbolicExpr. Returning Unknown.", place);
                        in_progress.remove(place);
                        memo.insert(
                            place,
                            Some(SymbolicExpr::Unknown(UnknownReason::CyclicDependency)),
                        );
                        return Some(SymbolicExpr::Unknown(UnknownReason::CyclicDependency));
                    }
                }
            }
            Some(current_expr)
        };

        in_progress.remove(place);
        memo.insert(place, result.clone());
        result
    }

    fn op_kind_to_symbolic_expr(
        &self,
        op_kind: &BasicOpKind<'tcx, T>,
        memo: &mut HashMap<&'tcx Place<'tcx>, Option<SymbolicExpr<'tcx>>>,
        in_progress: &mut HashSet<&'tcx Place<'tcx>>,
    ) -> Option<SymbolicExpr<'tcx>> {
        match op_kind {
            BasicOpKind::Binary(bop) => {
                let (original_op1, original_op2) = {
                    if let StatementKind::Assign(box (
                        _lhs,
                        Rvalue::BinaryOp(_op, box (op1_mir, op2_mir)),
                    )) = &bop.inst.kind
                    {
                        (op1_mir, op2_mir)
                    } else {
                        // This case should ideally not happen if BasicOpKind::Binary is correctly formed from MIR.
                        rap_trace!("Error: BinaryOp's instruction {:?} is not a BinaryOp statement. Returning Unknown.", bop.inst);
                        return Some(SymbolicExpr::Unknown(UnknownReason::CannotParse));
                    }
                };

                let left_expr = if let Some(src_place) = bop.source1 {
                    self.get_symbolic_expression_recursive(src_place, memo, in_progress)?
                } else if let Operand::Constant(c) = original_op1 {
                    SymbolicExpr::Constant(c.const_)
                } else {
                    rap_trace!("Error: BinaryOp source1 is None, but original op1 is not a constant for inst {:?}. Returning Unknown.", bop.inst);
                    return Some(SymbolicExpr::Unknown(UnknownReason::CannotParse));
                };

                let right_expr = if let Some(src_place) = bop.source2 {
                    self.get_symbolic_expression_recursive(src_place, memo, in_progress)?
                } else if let Operand::Constant(c) = original_op2 {
                    SymbolicExpr::Constant(c.const_)
                } else {
                    rap_trace!("Error: BinaryOp source2 is None, but original op2 is not a constant for inst {:?}. Returning Unknown.", bop.inst);
                    return Some(SymbolicExpr::Unknown(UnknownReason::CannotParse));
                };

                Some(SymbolicExpr::BinaryOp {
                    op: bop.op,
                    left: Box::new(left_expr),
                    right: Box::new(right_expr),
                })
            }
            BasicOpKind::Unary(uop) => {
                let original_operand_mir = {
                    if let StatementKind::Assign(box (_lhs, Rvalue::UnaryOp(_op, operand_mir))) =
                        &uop.inst.kind
                    {
                        operand_mir
                    } else {
                        rap_trace!("Error: UnaryOp's instruction {:?} is not a UnaryOp statement. Returning Unknown.", uop.inst);
                        return Some(SymbolicExpr::Unknown(UnknownReason::CannotParse));
                    }
                };

                let operand_expr = if let Operand::Constant(c) = original_operand_mir {
                    SymbolicExpr::Constant(c.const_)
                } else if let Operand::Copy(place) | Operand::Move(place) = original_operand_mir {
                    self.get_symbolic_expression_recursive(place, memo, in_progress)?
                } else {
                    rap_trace!("Error: UnaryOp's operand is neither Place nor Constant for inst {:?}. Returning Unknown.", uop.inst);
                    return Some(SymbolicExpr::Unknown(UnknownReason::CannotParse));
                };

                Some(SymbolicExpr::UnaryOp {
                    op: uop.op,
                    operand: Box::new(operand_expr),
                })
            }
            BasicOpKind::Use(use_op) => {
                if let Some(c) = use_op.const_value {
                    Some(SymbolicExpr::Constant(c))
                } else if let Some(source_place) = use_op.source {
                    self.get_symbolic_expression_recursive(source_place, memo, in_progress)
                } else {
                    rap_trace!("Error: UseOp has neither source nor const_value for inst {:?}. Returning Unknown.", use_op.inst);
                    Some(SymbolicExpr::Unknown(UnknownReason::CannotParse))
                }
            }
            BasicOpKind::Phi(phi_op) => {
                let mut operands_exprs = Vec::new();
                for &source_place in phi_op.get_sources() {
                    // Note: If a source is itself part of a cycle, this recursive call
                    // will correctly return Unknown(CyclicDependency), which then
                    // is propagated up as part of the Phi's sources.
                    if let Some(expr) =
                        self.get_symbolic_expression_recursive(source_place, memo, in_progress)
                    {
                        operands_exprs.push(expr);
                    } else {
                        // If any source cannot be resolved (e.g., due to an unhandled MIR construct),
                        // the entire Phi node becomes unresolvable.
                        rap_trace!("Warning: One source of Phi {:?} cannot be resolved to a symbolic expression. Returning Unknown for the Phi.", phi_op.sink);
                        return Some(SymbolicExpr::Unknown(UnknownReason::CannotParse));
                    }
                }
                Some(SymbolicExpr::Ssa(operands_exprs))
            }
            BasicOpKind::Essa(essa_op) => {
                let operand_expr = self.get_symbolic_expression_recursive(
                    essa_op.get_source(),
                    memo,
                    in_progress,
                )?;

                // Now, extract constraint_operand and bin_op from EssaOp's IntervalType
                // This is the tricky part because EssaOp might use SymbInterval for constraints.
                let (constraint_op_operand, bin_op) = match essa_op.get_intersect() {
                    super::domain::IntervalType::Symb(symb_interval) => {
                        // If it's a SymbInterval, it contains the Place and the BinOp
                        (
                            VarorConst::Place(*symb_interval.get_bound()),
                            symb_interval.get_operation(),
                        )
                    }
                    super::domain::IntervalType::Basic(basic_interval) => {
                        if let Some(vbm) = self.values_branchmap.get(essa_op.get_source()) {
                            rap_trace!("Warning: EssaOp with BasicInterval constraint. Cannot directly reconstruct original BinOp and constraint_operand from EssaOp's internal state. Returning Unknown for constraint part.",);
                            // Fallback if we cannot precisely reconstruct
                            return Some(SymbolicExpr::Unknown(UnknownReason::CannotParse));
                        } else {
                            rap_trace!("Warning: EssaOp with BasicInterval constraint, but source not found in values_branchmap. Returning Unknown for constraint part.",);
                            return Some(SymbolicExpr::Unknown(UnknownReason::CannotParse));
                        }
                    }
                };

                Some(SymbolicExpr::Essa {
                    operand: Box::new(operand_expr),
                    constraint_operand: constraint_op_operand,
                    bin_op: bin_op,
                })
            }
            BasicOpKind::ControlDep(_) => {
                rap_trace!("Encountered unexpected ControlDep operation defining a place. Returning Unknown.");
                Some(SymbolicExpr::Unknown(UnknownReason::CannotParse))
            }
            BasicOpKind::Call(call_op) => todo!(),
        }
    }
    pub fn start_analyze_path_constraints(
        &mut self,
        body: &'tcx Body<'tcx>,
        all_paths_indices: &[Vec<usize>],
    ) -> HashMap<Vec<usize>, Vec<(Place<'tcx>, Place<'tcx>, BinOp)>> {
        self.build_value_maps(body);
        let result = self.analyze_path_constraints(body, all_paths_indices);
        result
    }

    pub fn analyze_path_constraints(
        &self,
        body: &'tcx Body<'tcx>,
        all_paths_indices: &[Vec<usize>],
    ) -> HashMap<Vec<usize>, Vec<(Place<'tcx>, Place<'tcx>, BinOp)>> {
        let mut all_path_results: HashMap<Vec<usize>, Vec<(Place<'tcx>, Place<'tcx>, BinOp)>> =
            HashMap::with_capacity(all_paths_indices.len());

        for path_indices in all_paths_indices {
            let mut current_path_constraints: Vec<(Place<'tcx>, Place<'tcx>, BinOp)> = Vec::new();

            let path_bbs: Vec<BasicBlock> = path_indices
                .iter()
                .map(|&idx| BasicBlock::from_usize(idx))
                .collect();

            for window in path_bbs.windows(2) {
                let current_bb = window[0];

                if self.switchbbs.contains_key(&current_bb) {
                    let next_bb = window[1];
                    let current_bb_data = &body[current_bb];

                    if let Some(Terminator {
                        kind: TerminatorKind::SwitchInt { discr, .. },
                        ..
                    }) = &current_bb_data.terminator
                    {
                        let (constraint_place_1, constraint_place_2) =
                            self.switchbbs.get(&current_bb).unwrap();
                        if let Some(vbm) = self.values_branchmap.get(constraint_place_1) {
                            let relevant_interval_opt = if next_bb == *vbm.get_bb_true() {
                                Some(vbm.get_itv_t())
                            } else if next_bb == *vbm.get_bb_false() {
                                Some(vbm.get_itv_f())
                            } else {
                                None
                            };

                            if let Some(relevant_interval) = relevant_interval_opt {
                                match relevant_interval {
                                    IntervalType::Basic(basic_interval) => {}
                                    IntervalType::Symb(symb_interval) => {
                                        current_path_constraints.push((
                                            constraint_place_1.clone(),
                                            constraint_place_2.clone(),
                                            symb_interval.get_operation().clone(),
                                        ));
                                    }
                                }
                            }
                        }
                    }
                }
            }

            all_path_results.insert(path_indices.clone(), (current_path_constraints));
        }

        all_path_results
    }
}

#[derive(Debug)]
pub struct Nuutila<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub variables: &'tcx VarNodes<'tcx, T>,
    pub index: i32,
    pub dfs: HashMap<&'tcx Place<'tcx>, i32>,
    pub root: HashMap<&'tcx Place<'tcx>, &'tcx Place<'tcx>>,
    pub in_component: HashSet<&'tcx Place<'tcx>>,
    pub components: HashMap<&'tcx Place<'tcx>, HashSet<&'tcx Place<'tcx>>>,
    pub worklist: VecDeque<&'tcx Place<'tcx>>,
    // pub oprs: &Vec<BasicOpKind<'tcx, T>>,
}

impl<'tcx, T> Nuutila<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    pub fn new(
        varNodes: &'tcx VarNodes<'tcx, T>,
        use_map: &'tcx UseMap<'tcx>,
        symb_map: &'tcx SymbMap<'tcx>,
        single: bool,
        oprs: &'tcx Vec<BasicOpKind<'tcx, T>>,
    ) -> Self {
        let mut n: Nuutila<'_, T> = Nuutila {
            variables: varNodes,
            index: 0,
            dfs: HashMap::new(),
            root: HashMap::new(),
            in_component: HashSet::new(),
            components: HashMap::new(),
            worklist: std::collections::VecDeque::new(),
            // oprs:oprs
        };

        if single {
            // let mut scc = HashSet::new();
            // for var_node in variables.values() {
            //     scc.insert(var_node.clone());
            // }

            // for (place, _) in variables.iter() {
            //     n.components.insert(place.clone(), scc.clone());
            // }

            // if let Some((first_place, _)) = variables.iter().next() {
            //     n.worklist.push_back(first_place.clone());
            // }
        } else {
            for place in n.variables.keys().copied() {
                n.dfs.insert(place, -1);
            }

            n.add_control_dependence_edges(symb_map, use_map, varNodes);

            for place in n.variables.keys() {
                if n.dfs[place] < 0 {
                    let mut stack = Vec::new();
                    n.visit(place, &mut stack, use_map, oprs);
                }
            }

            // n.del_control_dependence_edges(use_map);
        }

        n
    }

    pub fn visit(
        &mut self,
        place: &'tcx Place<'tcx>,
        stack: &mut Vec<&'tcx Place<'tcx>>,
        use_map: &'tcx UseMap<'tcx>,
        oprs: &'tcx Vec<BasicOpKind<'tcx, T>>,
    ) {
        self.dfs.entry(place).and_modify(|v| *v = self.index);
        self.index += 1;
        self.root.insert(place, place);

        if let Some(uses) = use_map.get(place) {
            for op in uses {
                let name = oprs[*op].get_sink();

                if self.dfs.get(name).copied().unwrap_or(-1) < 0 {
                    self.visit(name, stack, use_map, oprs);
                }

                if (!self.in_component.contains(name)
                    && self.dfs[self.root[place]] >= self.dfs[self.root[name]])
                {
                    *self.root.get_mut(place).unwrap() = self.root.get(name).copied().unwrap();

                    // let weq = self.root.get(place)
                }
            }
        }

        if self.root.get(place).copied().unwrap() == place {
            self.worklist.push_back(place);

            let mut scc = HashSet::new();
            scc.insert(place);

            self.in_component.insert(place);

            while let Some(&top) = stack.last() {
                if self.dfs.get(top).copied().unwrap_or(-1) > self.dfs.get(place).copied().unwrap()
                {
                    let node = stack.pop().unwrap();
                    self.in_component.insert(node);

                    scc.insert(node);
                } else {
                    break;
                }
            }

            self.components.insert(place, scc);
        } else {
            stack.push(place);
        }
    }

    pub fn add_control_dependence_edges(
        &mut self,
        _symb_map: &'tcx SymbMap<'tcx>,
        _use_map: &'tcx UseMap<'tcx>,
        _vars: &'tcx VarNodes<'tcx, T>,
    ) {
        todo!()
    }

    pub fn del_control_dependence_edges(&mut self, _use_map: &'tcx mut UseMap<'tcx>) {
        todo!()
    }
}
