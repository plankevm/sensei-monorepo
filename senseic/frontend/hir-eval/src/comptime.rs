use sensei_core::{Idx, IndexVec};
use sensei_hir::{self as hir, ConstDef};
use sensei_values::{TypeId, ValueId};

use crate::{Evaluator, value::Value};

struct ReturnValue(ValueId);

pub(crate) struct ComptimeEvaluator<'a, 'hir> {
    eval: &'a mut Evaluator<'hir>,
    bindings: IndexVec<hir::LocalId, Option<ValueId>>,
    value_buf: Vec<ValueId>,
    type_buf: Vec<TypeId>,
    name_buf: Vec<sensei_parser::StrId>,
}

impl<'a, 'hir> ComptimeEvaluator<'a, 'hir> {
    fn new(eval: &'a mut Evaluator<'hir>) -> Self {
        Self {
            eval,
            bindings: IndexVec::new(),
            value_buf: Vec::new(),
            type_buf: Vec::new(),
            name_buf: Vec::new(),
        }
    }

    pub fn eval_const(eval: &mut Evaluator<'hir>, const_def: ConstDef) -> ValueId {
        let mut comptime = ComptimeEvaluator::new(eval);
        let _ = comptime.walk_block(const_def.body);
        comptime.get_local(const_def.result)
    }

    fn set_local(&mut self, local: hir::LocalId, value: ValueId) {
        if local.get() as usize >= self.bindings.len() {
            self.bindings.raw.resize(local.get() as usize + 1, None);
        }
        self.bindings[local] = Some(value);
    }

    // Invariant: HIR lowerer ensures locals are bound before use.
    // Failure here indicates a compiler bug, not a user error.
    fn get_local(&self, local: hir::LocalId) -> ValueId {
        self.bindings[local].expect("unbound local")
    }

    fn type_of_value(&self, value: ValueId) -> TypeId {
        match self.eval.values.lookup(value) {
            Value::Void => TypeId::VOID,
            Value::Bool(_) => TypeId::BOOL,
            Value::BigNum(_) => TypeId::U256,
            Value::Type(_) => TypeId::TYPE,
            Value::Closure { .. } => TypeId::FUNCTION,
            Value::StructVal { ty, .. } => ty,
        }
    }

    fn walk_block(&mut self, block_id: hir::BlockId) -> Result<(), ReturnValue> {
        for &instr in &self.eval.hir.blocks[block_id] {
            self.walk_instruction(instr)?;
        }
        Ok(())
    }

    fn walk_instruction(&mut self, _instr: hir::Instruction) -> Result<(), ReturnValue> {
        todo!("instruction handling")
    }

    fn eval_expr(&mut self, _expr: hir::Expr) -> Result<ValueId, ReturnValue> {
        todo!("expression evaluation")
    }
}
