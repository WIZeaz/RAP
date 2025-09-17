#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unused_assignments)]
#![allow(unused_parens)]
#![allow(non_snake_case)]

use crate::analysis::core::range_analysis::domain::ConstraintGraph::ConstraintGraph;
use crate::analysis::core::range_analysis::{Range, RangeType};
use crate::{rap_debug, rap_trace};
use num_traits::{Bounded, CheckedAdd, CheckedSub, One, ToPrimitive, Zero};
use rustc_abi::Size;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::coverage::Op;
use rustc_middle::mir::{
    BasicBlock, BinOp, Const, Local, LocalDecl, Operand, Place, Rvalue, Statement, StatementKind,
    Terminator, UnOp,
};
use rustc_middle::ty::ScalarInt;
use rustc_span::sym::no_default_passes;
use std::cell::RefCell;
use std::cmp::PartialEq;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::{Add, Mul, Sub};
use std::rc::Rc;
pub trait ConstConvert: Sized {
    fn from_const(c: &Const) -> Option<Self>;
}

impl ConstConvert for u32 {
    fn from_const(c: &Const) -> Option<Self> {
        if let Some(scalar) = c.try_to_scalar_int() {
            Some(scalar.to_bits(scalar.size()) as u32)
        } else {
            None
        }
    }
}
impl ConstConvert for usize {
    fn from_const(c: &Const) -> Option<Self> {
        if let Some(scalar) = c.try_to_scalar_int() {
            Some(scalar.to_bits(scalar.size()) as usize)
        } else {
            None
        }
    }
}
impl ConstConvert for i32 {
    fn from_const(c: &Const) -> Option<Self> {
        if let Some(scalar) = c.try_to_scalar_int() {
            Some(scalar.to_bits(scalar.size()) as i32)
        } else {
            None
        }
    }
}

impl ConstConvert for i64 {
    fn from_const(c: &Const) -> Option<Self> {
        if let Some(scalar) = c.try_to_scalar_int() {
            Some(scalar.to_bits(scalar.size()) as i64)
        } else {
            None
        }
    }
}
impl ConstConvert for i128 {
    fn from_const(c: &Const) -> Option<Self> {
        if let Some(scalar) = c.try_to_scalar_int() {
            Some(scalar.to_bits(scalar.size()) as i128)
        } else {
            None
        }
    }
}
pub trait IntervalArithmetic:
    PartialOrd
    + Clone
    + Bounded
    + Zero
    + Copy
    + One
    + CheckedAdd
    + CheckedSub
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + fmt::Display
{
}

impl<T> IntervalArithmetic for T where
    T: PartialOrd
        + Clone
        + Bounded
        + Zero
        + One
        + Copy
        + CheckedAdd
        + CheckedSub
        + Add<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + fmt::Display
{
}
#[derive(Debug, Clone, PartialEq)]
pub enum IntervalType<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    Basic(BasicInterval<T>),
    Symb(SymbInterval<'tcx, T>), // Using 'static for simplicity, adjust lifetime as needed
}
impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> fmt::Display for IntervalType<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IntervalType::Basic(b) => write!(f, "BasicInterval: {}", b.get_range()),
            IntervalType::Symb(s) => write!(f, "SymbInterval: {}", s.get_range()),
        }
    }
}
pub trait IntervalTypeTrait<T: IntervalArithmetic + ConstConvert + Debug> {
    // fn get_value_id(&self) -> IntervalId;
    fn get_range(&self) -> &Range<T>;
    fn set_range(&mut self, new_range: Range<T>);
}
impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> IntervalTypeTrait<T>
    for IntervalType<'tcx, T>
{
    fn get_range(&self) -> &Range<T> {
        match self {
            IntervalType::Basic(b) => b.get_range(),
            IntervalType::Symb(s) => s.get_range(),
        }
    }

    fn set_range(&mut self, new_range: Range<T>) {
        match self {
            IntervalType::Basic(b) => b.set_range(new_range),
            IntervalType::Symb(s) => s.set_range(new_range),
        }
    }
}
#[derive(Debug, Clone, PartialEq)]
pub struct BasicInterval<T: IntervalArithmetic + ConstConvert + Debug> {
    range: Range<T>,
}

impl<T: IntervalArithmetic + ConstConvert + Debug> BasicInterval<T> {
    pub fn new(range: Range<T>) -> Self {
        Self { range }
    }
    pub fn default() -> Self {
        Self {
            range: Range::default(T::min_value()),
        }
    }
}

impl<T: IntervalArithmetic + ConstConvert + Debug> IntervalTypeTrait<T> for BasicInterval<T> {
    // fn get_value_id(&self) -> IntervalId {
    //     IntervalId::BasicIntervalId
    // }

    fn get_range(&self) -> &Range<T> {
        &self.range
    }

    fn set_range(&mut self, new_range: Range<T>) {
        self.range = new_range;
        if self.range.get_lower() > self.range.get_upper() {
            self.range.set_empty();
        }
    }
}

#[derive(Debug, Clone, PartialEq)]

pub struct SymbInterval<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    range: Range<T>,
    symbound: &'tcx Place<'tcx>,
    predicate: BinOp,
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> SymbInterval<'tcx, T> {
    pub fn new(range: Range<T>, symbound: &'tcx Place<'tcx>, predicate: BinOp) -> Self {
        Self {
            range: range,
            symbound,
            predicate,
        }
    }

    pub fn get_operation(&self) -> BinOp {
        self.predicate
    }

    pub fn get_bound(&self) -> &'tcx Place<'tcx> {
        self.symbound
    }

    pub fn sym_fix_intersects(
        &self,
        bound: &VarNode<'tcx, T>,
        sink: &VarNode<'tcx, T>,
    ) -> Range<T> {
        let l = bound.get_range().get_lower().clone();
        let u = bound.get_range().get_upper().clone();

        let lower = sink.get_range().get_lower().clone();
        let upper = sink.get_range().get_upper().clone();

        match self.predicate {
            BinOp::Eq => Range::new(l, u, RangeType::Regular),

            BinOp::Le => Range::new(lower, u, RangeType::Regular),

            BinOp::Lt => {
                if u != T::max_value() {
                    let u_minus_1 = u.checked_sub(&T::one()).unwrap_or(u);
                    Range::new(lower, u_minus_1, RangeType::Regular)
                } else {
                    Range::new(lower, u, RangeType::Regular)
                }
            }

            BinOp::Ge => Range::new(l, upper, RangeType::Regular),

            BinOp::Gt => {
                if l != T::min_value() {
                    let l_plus_1 = l.checked_add(&T::one()).unwrap_or(l);
                    Range::new(l_plus_1, upper, RangeType::Regular)
                } else {
                    Range::new(l, upper, RangeType::Regular)
                }
            }

            BinOp::Ne => Range::new(T::min_value(), T::max_value(), RangeType::Regular),

            _ => Range::new(T::min_value(), T::max_value(), RangeType::Regular),
        }
    }
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> IntervalTypeTrait<T>
    for SymbInterval<'tcx, T>
{
    // fn get_value_id(&self) -> IntervalId {
    //     IntervalId::SymbIntervalId
    // }

    fn get_range(&self) -> &Range<T> {
        &self.range
    }

    fn set_range(&mut self, new_range: Range<T>) {
        self.range = new_range;
    }
}

// Define the basic operation trait
pub trait Operation<T: IntervalArithmetic + ConstConvert + Debug> {
    fn eval(&self) -> Range<T>; // Method to evaluate the range of the operation
    fn print(&self, os: &mut dyn fmt::Write);
}

#[derive(Debug, Clone)]
pub enum BasicOpKind<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    Unary(UnaryOp<'tcx, T>),
    Binary(BinaryOp<'tcx, T>),
    Essa(EssaOp<'tcx, T>),
    ControlDep(ControlDep<'tcx, T>),
    Phi(PhiOp<'tcx, T>),
    Use(UseOp<'tcx, T>),
    Call(CallOp<'tcx, T>),
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> fmt::Display for BasicOpKind<'tcx, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BasicOpKind::Unary(op) => write!(f, "UnaryOp: intersect {} sink:{:?} source:{:?} inst:{:?} ",op.intersect,op.sink,op.source,op.inst),
            BasicOpKind::Binary(op) => write!(f, "BinaryOp: intersect {} sink:{:?} source1:{:?} source2:{:?} inst:{:?} const_value:{} ",op.intersect,op.sink,op.source1,op.source2,op.inst,op.const_value.clone().unwrap()),
            BasicOpKind::Essa(op) => write!(f, "EssaOp: intersect {} sink:{:?} source:{:?} inst:{:?} unresolved:{:?} ",op.intersect,op.sink,op.source,op.inst,op.unresolved),
            BasicOpKind::ControlDep(op) => write!(f, "ControlDep: intersect {} sink:{:?} source:{:?} inst:{:?}  ",op.intersect,op.sink,op.source,op.inst),
            BasicOpKind::Phi(op) => write!(f, "PhiOp: intersect {} sink:{:?} source:{:?} inst:{:?}  ",op.intersect,op.sink,op.sources,op.inst),
            BasicOpKind::Use(op) => write!(f, "UseOp: intersect {} sink:{:?} source:{:?} inst:{:?} ",op.intersect,op.sink,op.source,op.inst ),
            BasicOpKind::Call(op) => write!(f, "CallOp: intersect {} sink:{:?} args:{:?} inst:{:?}", op.intersect, op.sink, op.args, op.inst),
        }
    }
}
impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> BasicOpKind<'tcx, T> {
    pub fn eval(&self, vars: &VarNodes<'tcx, T>) -> Range<T> {
        match self {
            BasicOpKind::Unary(op) => op.eval(),
            BasicOpKind::Binary(op) => op.eval(vars),
            BasicOpKind::Essa(op) => op.eval(vars),
            BasicOpKind::ControlDep(op) => op.eval(),
            BasicOpKind::Phi(op) => op.eval(vars),
            BasicOpKind::Use(op) => op.eval(vars),
            BasicOpKind::Call(op) => op.eval(vars),
        }
    }
    pub fn get_type_name(&self) -> &'static str {
        match self {
            BasicOpKind::Unary(_) => "Unary",
            BasicOpKind::Binary(_) => "Binary",
            BasicOpKind::Essa(_) => "Essa",
            BasicOpKind::ControlDep(_) => "ControlDep",
            BasicOpKind::Phi(_) => "Phi",
            BasicOpKind::Use(_) => "Use",
            BasicOpKind::Call(_) => "Call",
        }
    }
    pub fn get_sink(&self) -> &'tcx Place<'tcx> {
        match self {
            BasicOpKind::Unary(op) => op.sink,
            BasicOpKind::Binary(op) => op.sink,
            BasicOpKind::Essa(op) => op.sink,
            BasicOpKind::ControlDep(op) => op.sink,
            BasicOpKind::Phi(op) => op.sink,
            BasicOpKind::Use(op) => op.sink,
            BasicOpKind::Call(op) => op.sink,
        }
    }
    pub fn get_instruction(&self) -> Option<&'tcx Statement<'tcx>> {
        match self {
            BasicOpKind::Unary(op) => Some(op.inst),
            BasicOpKind::Binary(op) => Some(op.inst),
            BasicOpKind::Essa(op) => Some(op.inst),
            BasicOpKind::ControlDep(op) => Some(op.inst),
            BasicOpKind::Phi(op) => Some(op.inst),
            BasicOpKind::Use(op) => Some(op.inst),
            BasicOpKind::Call(op) => None,
        }
    }
    pub fn get_intersect(&self) -> &IntervalType<'tcx, T> {
        match self {
            BasicOpKind::Unary(op) => &op.intersect,
            BasicOpKind::Binary(op) => &op.intersect,
            BasicOpKind::Essa(op) => &op.intersect,
            BasicOpKind::ControlDep(op) => &op.intersect,
            BasicOpKind::Phi(op) => &op.intersect,
            BasicOpKind::Use(op) => &op.intersect,
            BasicOpKind::Call(op) => &op.intersect,
        }
    }
    pub fn op_fix_intersects(&mut self, v: &VarNode<'tcx, T>, sink: &VarNode<'tcx, T>) {
        let intersect = self.get_intersect_mut();

        if let IntervalType::Symb(symbi) = intersect {
            let range = symbi.sym_fix_intersects(v, sink);
            rap_trace!(
                "from {:?} to {:?} fix_intersects: {:} -> {}\n",
                v.get_value().clone(),
                sink.get_value().clone(),
                intersect.clone(),
                range
            );
            self.set_intersect(range);
        }
    }
    pub fn set_intersect(&mut self, new_intersect: Range<T>) {
        match self {
            BasicOpKind::Unary(op) => op.intersect.set_range(new_intersect),
            BasicOpKind::Binary(op) => op.intersect.set_range(new_intersect),
            BasicOpKind::Essa(op) => op.intersect.set_range(new_intersect),
            BasicOpKind::ControlDep(op) => op.intersect.set_range(new_intersect),
            BasicOpKind::Phi(op) => op.intersect.set_range(new_intersect),
            BasicOpKind::Use(op) => op.intersect.set_range(new_intersect),
            BasicOpKind::Call(op) => op.intersect.set_range(new_intersect),
        }
    }
    pub fn get_intersect_mut(&mut self) -> &mut IntervalType<'tcx, T> {
        match self {
            BasicOpKind::Unary(op) => &mut op.intersect,
            BasicOpKind::Binary(op) => &mut op.intersect,
            BasicOpKind::Essa(op) => &mut op.intersect,
            BasicOpKind::ControlDep(op) => &mut op.intersect,
            BasicOpKind::Phi(op) => &mut op.intersect,
            BasicOpKind::Use(op) => &mut op.intersect,
            BasicOpKind::Call(op) => &mut op.intersect,
        }
    }
}
#[derive(Debug, Clone)]
pub struct CallOp<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Terminator<'tcx>,
    pub args: Vec<Operand<'tcx>>,
    pub def_id: DefId,
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> CallOp<'tcx, T> {
    pub fn convert_const(c: &Const) -> Option<T> {
        T::from_const(c)
    }
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Terminator<'tcx>,
        args: Vec<Operand<'tcx>>,
        def_id: DefId,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            args,
            def_id,
        }
    }

    pub fn eval(&self, caller_vars: &VarNodes<'tcx, T>) -> Range<T> {
        return Range::default(T::min_value());
    }
    pub fn eval_call(
        &self,
        caller_vars: &VarNodes<'tcx, T>,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) -> Range<T> {
        // 1. Find the callee's ConstraintGraph in the map.
        if let Some(rc_callee_cg_cell) = cg_map.get(&self.def_id) {
            rap_debug!(
                "Evaluating call to {:?} with args {:?}",
                self.def_id,
                self.args
            );
            // 2. Try to get a mutable borrow of the callee's graph.
            //    Using `try_borrow_mut` is safer than `borrow_mut` to avoid panicking on recursive calls.
            if let Ok(mut callee_cg) = rc_callee_cg_cell.try_borrow_mut() {
                // 3. Pass arguments from caller to callee.
                //    This assumes arguments are in order and `_1`, `_2`, ... in the callee MIR.
                for (i, caller_arg_operand) in self.args.iter().enumerate() {
                    rap_debug!(
                        "Processing argument {}: {:?} to callee {:?}",
                        i,
                        caller_arg_operand,
                        self.def_id
                    );
                    match caller_arg_operand {
                        Operand::Copy(caller_arg_place) | Operand::Move(caller_arg_place) => {
                            // Add the variable node for the caller's argument.
                            // Callee arguments are typically `_1`, `_2`, ...
                            let callee_arg_local = rustc_middle::mir::Local::from_usize(i + 1);

                            // Find the corresponding Place and VarNode in the callee.
                            if let Some(callee_arg_node) = callee_cg.vars.values_mut().find(|v| {
                                v.v.local == callee_arg_local && v.v.projection.is_empty()
                            }) {
                                // Get the range from the caller's variable and set it for the callee's argument.
                                if let Some(caller_arg_node) = caller_vars.get(&caller_arg_place) {
                                    let arg_range = caller_arg_node.get_range().clone();
                                    callee_arg_node.set_range(arg_range);
                                    rap_debug!(
                                                    "Passing argument from {:?} to callee {:?} : {:?} {:?} -> {:?}",
                                                    caller_arg_place,
                                                    self.def_id,
                                                    callee_arg_node.get_value(),
                                                    caller_arg_node.get_range(),
                                                    callee_arg_node.get_range()
                                                );
                                }
                            }
                        }
                        Operand::Constant(const_operand) => {
                            rap_debug!(
                                "constant argument {:?} to callee {:?}",
                                const_operand,
                                self.def_id
                            );
                            let callee_arg_local = rustc_middle::mir::Local::from_usize(i + 1);
                            if let Some(const_value) = Self::convert_const(&const_operand.const_) {
                                if let Some(callee_arg_node) =
                                    callee_cg.vars.values_mut().find(|v| {
                                        v.v.local == callee_arg_local && v.v.projection.is_empty()
                                    })
                                {
                                    // Get the range from the caller's variable and set it for the callee's argument.

                                    let arg_range = Range::new(
                                        const_value.clone(),
                                        const_value.clone(),
                                        RangeType::Regular,
                                    );
                                    callee_arg_node.set_range(arg_range.clone());
                                    rap_debug!(
                                                    "Passing argument from {:?} to callee {:?} : {:?} {:?} -> {:?}",
                                                    const_value,
                                                    self.def_id,
                                                    callee_arg_node.get_value(),
                                                    arg_range,
                                                    callee_arg_node.get_range()
                                                );
                                }
                            }
                            // Find the corresponding Place and VarNode in the callee.
                        }
                    }
                }

                // 4. Run analysis on the callee.
                //    NOTE: This is a simplification. A full implementation would use memoization
                //    or a bottom-up analysis order to avoid re-analyzing functions repeatedly.
                //    For now, we re-run it to ensure argument values are propagated.
                callee_cg.find_intervals(cg_map, vars_map);

                // 5. Retrieve the return value.
                //    The return value is stored in `_0` (RETURN_PLACE).
                let return_place_local = 0 as usize; // `_0` is typically the first local.
                let mut return_range = Range::default(T::min_value());

                // Find all variables that contribute to the return value.
                // The `rerurn_places` set in the callee's graph tracks these.
                if let Some(return_node) = callee_cg.vars.get_mut(&Place::return_place()) {
                    return_range = return_node.get_range().clone();
                    rap_debug!(" final return range {} ", return_range);
                    return return_range;
                }
                let Some(callee_varnodes_vec) = vars_map.get_mut(&self.def_id) else {
                    panic!(
                        "No variable map entry for this function {:?}, skipping Nuutila\n",
                        self.def_id
                    );
                };
                callee_cg.reset_vars(callee_varnodes_vec);
            } else {
                // Recursive call detected or graph is already borrowed.
                // Conservatively return a full range.
                rap_trace!(
                    "Recursive call or existing borrow for {:?}, returning top.",
                    self.def_id
                );
                return Range::new(T::min_value(), T::max_value(), RangeType::Regular);
            }
        }

        // Callee not found (e.g., external library function, function pointer).
        // Return a conservative full range.
        rap_trace!(
            "Callee ConstraintGraph for {:?} not found, returning top.",
            self.def_id
        );
        Range::new(T::min_value(), T::max_value(), RangeType::Regular)
    }
}
#[derive(Debug, Clone)]
pub struct UseOp<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub source: Option<&'tcx Place<'tcx>>,
    pub const_value: Option<Const<'tcx>>,
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> UseOp<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        source: Option<&'tcx Place<'tcx>>,
        const_value: Option<Const<'tcx>>,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            source,
            const_value,
        }
    }

    pub fn eval(&self, vars: &VarNodes<'tcx, T>) -> Range<T> {
        if let Some(source) = self.source {
            let range = vars[source].get_range().clone();
            let mut result = Range::default(T::min_value());
            if range.is_regular() {
                result = range
            } else {
            }
            result
        } else {
            // If no source is provided, return the intersect range
            self.intersect.get_range().clone()
        }
    }
}
#[derive(Debug, Clone)]
pub struct UnaryOp<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub source: &'tcx Place<'tcx>,
    pub op: UnOp,
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> UnaryOp<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        source: &'tcx Place<'tcx>,
        op: UnOp,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            source,
            op,
        }
    }

    pub fn eval(&self) -> Range<T> {
        Range::default(T::min_value())
    }
}
#[derive(Debug, Clone)]

pub struct EssaOp<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub source: &'tcx Place<'tcx>,
    pub opcode: u32,
    pub unresolved: bool,
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> EssaOp<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        source: &'tcx Place<'tcx>,
        opcode: u32,
        unresolved: bool,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            source,
            opcode,
            unresolved,
        }
    }

    pub fn eval(&self, vars: &VarNodes<'tcx, T>) -> Range<T> {
        let source_range = vars[self.source].get_range().clone();
        let result = source_range.intersectwith(self.intersect.get_range());
        rap_trace!(
            "EssaOp eval: {:?} {} intersectwith {}-> {}\n",
            self.source,
            self.intersect.get_range(),
            source_range,
            result
        );
        result
    }
    pub fn get_source(&self) -> &'tcx Place<'tcx> {
        self.source
    }
    pub fn get_instruction(&self) -> &'tcx Statement<'tcx> {
        self.inst
    }
    pub fn get_sink(&self) -> &'tcx Place<'tcx> {
        self.sink
    }
    pub fn is_unresolved(&self) -> bool {
        self.unresolved
    }

    pub fn mark_resolved(&mut self) {
        self.unresolved = false;
    }

    pub fn mark_unresolved(&mut self) {
        self.unresolved = true;
    }
    pub fn get_intersect(&self) -> &IntervalType<'tcx, T> {
        &self.intersect
    }
}
#[derive(Debug, Clone)]
pub struct BinaryOp<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub source1: Option<&'tcx Place<'tcx>>,
    pub source2: Option<&'tcx Place<'tcx>>,
    pub const_value: Option<Const<'tcx>>,
    pub op: BinOp,
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> BinaryOp<'tcx, T> {
    pub fn convert_const(c: &Const) -> Option<T> {
        T::from_const(c)
    }
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        source1: Option<&'tcx Place<'tcx>>,
        source2: Option<&'tcx Place<'tcx>>,
        const_value: Option<Const<'tcx>>,

        op: BinOp,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            source1,
            source2,
            const_value, // Default value, can be set later
            op,
        }
    }

    pub fn eval(&self, vars: &VarNodes<'tcx, T>) -> Range<T> {
        let op1 = vars[self.source1.unwrap()].get_range().clone();
        let mut op2 = Range::default(T::min_value());
        if let Some(const_value) = &self.const_value {
            // If const_value is provided, use it as the second operand
            let value = Self::convert_const(const_value).unwrap();
            op2 = Range::new(value, value, RangeType::Regular);
        } else {
            op2 = vars[self.source2.unwrap()].get_range().clone();
        }
        let mut result = Range::default(T::min_value());
        match &self.inst.kind {
            StatementKind::Assign(box (place, rvalue)) => match rvalue {
                Rvalue::BinaryOp(binop, _) => match binop {
                    BinOp::Add | BinOp::AddUnchecked | BinOp::AddWithOverflow => {
                        result = op1.add(&op2);
                    }

                    BinOp::SubUnchecked | BinOp::SubWithOverflow | BinOp::Sub => {
                        result = op1.sub(&op2);
                    }

                    BinOp::MulUnchecked | BinOp::MulWithOverflow | BinOp::Mul => {
                        result = op1.mul(&op2);
                    }

                    _ => {}
                },
                _ => {}
            },

            _ => {}
        }

        result
    }
}
#[derive(Debug, Clone)]

pub struct PhiOp<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub sources: Vec<&'tcx Place<'tcx>>,
    pub opcode: u32,
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> PhiOp<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        opcode: u32,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            sources: vec![],
            opcode,
        }
    }

    pub fn add_source(&mut self, src: &'tcx Place<'tcx>) {
        self.sources.push(src);
    }
    pub fn eval(&self, vars: &VarNodes<'tcx, T>) -> Range<T> {
        let first = self.sources[0];
        let mut result = vars[first].get_range().clone();
        for &phisource in self.sources.iter() {
            let node = &vars[phisource];
            result = result.unionwith(node.get_range());
            rap_trace!(
                "PhiOp eval:  {} unionwith {} -> {}\n",
                vars[first].get_range().clone(),
                node.get_range(),
                result
            );
        }
        result
    }
    pub fn get_sources(&self) -> &[&'tcx Place<'tcx>] {
        &self.sources
    }
}
#[derive(Debug, Clone)]

pub struct ControlDep<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub source: &'tcx Place<'tcx>,
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> ControlDep<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        source: &'tcx Place<'tcx>,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            source,
        }
    }

    pub fn eval(&self) -> Range<T> {
        Range::default(T::min_value())
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct VarNode<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    // The program variable which is represented.
    pub v: &'tcx Place<'tcx>,
    // A Range associated to the variable.
    pub interval: Range<T>,
    // Used by the crop meet operator.
    pub abstract_state: char,
}
impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> VarNode<'tcx, T> {
    pub fn new(v: &'tcx Place<'tcx>) -> Self {
        Self {
            v,
            interval: Range::default(T::min_value()),
            abstract_state: '?',
        }
    }

    /// Initializes the value of the node.
    pub fn init(&mut self, outside: bool) {
        let value = self.get_value();
    }

    /// Returns the range of the variable represented by this node.
    pub fn get_range(&self) -> &Range<T> {
        &self.interval
    }

    /// Returns the variable represented by this node.
    pub fn get_value(&self) -> &'tcx Place<'tcx> {
        self.v
    }

    /// Changes the status of the variable represented by this node.
    pub fn set_range(&mut self, new_interval: Range<T>) {
        self.interval = new_interval;
    }

    /// Pretty print.
    pub fn print(&self, os: &mut dyn std::io::Write) {
        // Implementation of pretty printing using the `os` writer.
    }
    pub fn set_default(&mut self) {
        self.interval.set_default();
    }

    pub fn get_abstract_state(&self) -> char {
        self.abstract_state
    }

    /// The possible states are '0', '+', '-', and '?'.
    pub fn store_abstract_state(&mut self) {
        // Implementation of storing the abstract state.
    }
}
#[derive(Debug, Clone)]
pub struct ValueBranchMap<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    v: &'tcx Place<'tcx>,         // The value associated with the branch
    bb_true: &'tcx BasicBlock,    // True side of the branch
    bb_false: &'tcx BasicBlock,   // False side of the branch
    itv_t: IntervalType<'tcx, T>, // Interval for the true side
    itv_f: IntervalType<'tcx, T>,
}
impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> ValueBranchMap<'tcx, T> {
    pub fn new(
        v: &'tcx Place<'tcx>,
        bb_false: &'tcx BasicBlock,
        bb_true: &'tcx BasicBlock,
        itv_f: IntervalType<'tcx, T>,
        itv_t: IntervalType<'tcx, T>,
    ) -> Self {
        Self {
            v,
            bb_false,
            bb_true,
            itv_f,
            itv_t,
        }
    }

    /// Get the "false side" of the branch
    pub fn get_bb_false(&self) -> &BasicBlock {
        self.bb_false
    }

    /// Get the "true side" of the branch
    pub fn get_bb_true(&self) -> &BasicBlock {
        self.bb_true
    }

    /// Get the interval associated with the true side of the branch
    pub fn get_itv_t(&self) -> IntervalType<'tcx, T> {
        self.itv_t.clone()
    }

    /// Get the interval associated with the false side of the branch
    pub fn get_itv_f(&self) -> IntervalType<'tcx, T> {
        self.itv_f.clone()
    }

    /// Get the value associated with the branch
    pub fn get_v(&self) -> &'tcx Place<'tcx> {
        self.v
    }

    // pub fn set_itv_t(&mut self, itv: &IntervalType<'tcx, T>) {
    //     self.itv_t = itv;
    // }

    // /// Change the interval associated with the false side of the branch
    // pub fn set_itv_f(&mut self, itv: &IntervalType<'tcx, T>) {
    //     self.itv_f = itv;
    // }

    // pub fn clear(&mut self) {
    //     self.itv_t = Box::new(EmptyInterval::new());
    //     self.itv_f = Box::new(EmptyInterval::new());
    // }
}

pub type VarNodes<'tcx, T> = HashMap<&'tcx Place<'tcx>, VarNode<'tcx, T>>;
pub type GenOprs<'tcx, T> = Vec<BasicOpKind<'tcx, T>>;
pub type UseMap<'tcx> = HashMap<&'tcx Place<'tcx>, HashSet<usize>>;
pub type SymbMap<'tcx> = HashMap<&'tcx Place<'tcx>, HashSet<usize>>;
pub type DefMap<'tcx> = HashMap<&'tcx Place<'tcx>, usize>;
pub type ValuesBranchMap<'tcx, T> = HashMap<&'tcx Place<'tcx>, ValueBranchMap<'tcx, T>>;
