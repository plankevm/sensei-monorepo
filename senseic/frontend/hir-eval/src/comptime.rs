use sensei_core::{Idx, IndexVec};
use sensei_hir::{self as hir, ConstDef};
use sensei_parser::StrId;
use sensei_values::{TypeId, ValueId};

use crate::{Evaluator, value::Value};

#[derive(Debug)]
struct ReturnValue(ValueId);

pub(crate) struct ComptimeInterpreter<'a, 'hir> {
    eval: &'a mut Evaluator<'hir>,
    bindings: IndexVec<hir::LocalId, Option<ValueId>>,
    value_buf: Vec<ValueId>,
    type_buf: Vec<TypeId>,
    name_buf: Vec<StrId>,
}

impl<'a, 'hir> ComptimeInterpreter<'a, 'hir> {
    fn new(eval: &'a mut Evaluator<'hir>) -> Self {
        const EST_MAX_FIELD_COUNT: usize = 64;
        Self {
            eval,
            bindings: IndexVec::new(),
            value_buf: Vec::new(),
            type_buf: Vec::with_capacity(EST_MAX_FIELD_COUNT),
            name_buf: Vec::with_capacity(EST_MAX_FIELD_COUNT),
        }
    }

    pub fn eval_const(eval: &mut Evaluator<'hir>, const_def: ConstDef) -> ValueId {
        let mut comptime = ComptimeInterpreter::new(eval);
        comptime.interpret_block(const_def.body).expect("hir: const expr shouldn't have `return`");
        comptime.get_local(const_def.result)
    }

    fn set_local(&mut self, local: hir::LocalId, value: ValueId) -> Option<ValueId> {
        if local.get() as usize >= self.bindings.len() {
            self.bindings.raw.resize(local.idx() + 1, None);
        }
        self.bindings[local].replace(value)
    }

    fn get_local(&self, local: hir::LocalId) -> ValueId {
        self.bindings[local].expect("hir: unbound local")
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

    fn interpret_block(&mut self, block_id: hir::BlockId) -> Result<(), ReturnValue> {
        for &instr in &self.eval.hir.blocks[block_id] {
            self.interpret_instruction(instr)?;
        }
        Ok(())
    }

    fn interpret_instruction(&mut self, instr: hir::Instruction) -> Result<(), ReturnValue> {
        match instr {
            hir::Instruction::Set { local, expr } => {
                let value = self.eval_expr(expr)?;
                if self.set_local(local, value).is_some() {
                    unreachable!("hir: overwriting with set");
                }
            }
            hir::Instruction::Eval(expr) => {
                self.eval_expr(expr)?;
            }
            hir::Instruction::Return(expr) => {
                let value = self.eval_expr(expr)?;
                return Err(ReturnValue(value));
            }
            hir::Instruction::AssertType { value, of_type } => {
                let type_vid = self.get_local(of_type);
                let expected_type = match self.eval.values.lookup(type_vid) {
                    Value::Type(tid) => tid,
                    _ => todo!("diagnostic: type error, value not type"),
                };
                let value_vid = self.get_local(value);
                let actual_type = self.type_of_value(value_vid);
                if actual_type != expected_type {
                    todo!("diagnostic: hir-ty-assert type mismatch");
                }
            }
            hir::Instruction::Assign { target, value } => {
                let new_value = self.eval_expr(value)?;
                let Some(prev_value) = self.set_local(target, new_value) else {
                    unreachable!("hir: init with assign")
                };
                if self.type_of_value(new_value) != self.type_of_value(prev_value) {
                    todo!("diagnostic: assign type mismatch");
                }
            }
            hir::Instruction::If { condition, then_block, else_block } => {
                let cond_vid = self.get_local(condition);
                match self.eval.values.lookup(cond_vid) {
                    Value::Bool(true) => self.interpret_block(then_block)?,
                    Value::Bool(false) => self.interpret_block(else_block)?,
                    _ => todo!("diagnostic: type err, condition not bool"),
                }
            }
            hir::Instruction::While { .. } => {
                todo!("comptime while loops not yet implemented")
            }
        }
        Ok(())
    }

    fn eval_expr(&mut self, expr: hir::Expr) -> Result<ValueId, ReturnValue> {
        let value = match expr {
            hir::Expr::Void => ValueId::VOID,
            hir::Expr::Bool(false) => ValueId::FALSE,
            hir::Expr::Bool(true) => ValueId::TRUE,
            hir::Expr::BigNum(id) => self.eval.values.intern_num(id),
            hir::Expr::Type(type_id) => self.eval.values.intern_type(type_id),
            hir::Expr::ConstRef(const_id) => self.eval.ensure_const_evaluated(const_id),
            hir::Expr::LocalRef(local_id) => self.get_local(local_id),
            hir::Expr::FnDef(fn_def_id) => self.eval_fn_def(fn_def_id)?,
            hir::Expr::Call { callee, args } => self.eval_call(callee, args)?,
            hir::Expr::StructDef(struct_def_id) => self.eval_struct_def(struct_def_id)?,
            hir::Expr::StructLit { ty, fields } => self.eval_struct_lit(ty, fields)?,
            hir::Expr::Member { object, member } => self.eval_member(object, member)?,
        };
        Ok(value)
    }

    fn eval_fn_def(&mut self, fn_def: hir::FnDefId) -> Result<ValueId, ReturnValue> {
        let capture_start = self.value_buf.len();
        for capture in &self.eval.hir.fn_captures[fn_def] {
            self.value_buf.push(self.get_local(capture.outer_local));
        }

        let closure = Value::Closure { fn_def, captures: &self.value_buf[capture_start..] };
        let value_id = self.eval.values.intern(closure);

        self.value_buf.truncate(capture_start);

        Ok(value_id)
    }

    fn eval_struct_def(&mut self, struct_def_id: hir::StructDefId) -> Result<ValueId, ReturnValue> {
        let struct_def = self.eval.hir.struct_defs[struct_def_id];
        let type_index_vid = self.get_local(struct_def.type_index);
        let fields_info = &self.eval.hir.fields[struct_def.fields];

        debug_assert!(self.type_buf.is_empty());
        debug_assert!(self.name_buf.is_empty());

        for field in fields_info {
            let field_vid = self.get_local(field.value);
            match self.eval.values.lookup(field_vid) {
                Value::Type(tid) => {
                    self.type_buf.push(tid);
                    self.name_buf.push(field.name);
                }
                _ => todo!("diagnostic: struct field type must be Type"),
            }
        }

        let struct_type_id =
            self.eval.types.intern(sensei_values::Type::Struct(sensei_values::StructInfo {
                source: struct_def.source,
                type_index: type_index_vid,
                fields: &self.type_buf,
                field_names: &self.name_buf,
            }));

        self.type_buf.clear();
        self.name_buf.clear();

        Ok(self.eval.values.intern_type(struct_type_id))
    }

    fn eval_struct_lit(
        &mut self,
        ty: hir::LocalId,
        fields_id: hir::FieldsId,
    ) -> Result<ValueId, ReturnValue> {
        let type_vid = self.get_local(ty);
        let struct_type_id = match self.eval.values.lookup(type_vid) {
            Value::Type(tid) => tid,
            _ => todo!("diagnostic: struct literal type must be Type"),
        };

        let fields_info = &self.eval.hir.fields[fields_id];

        let buf_start = self.value_buf.len();
        for field in fields_info {
            self.value_buf.push(self.get_local(field.value));
        }

        let result = self
            .eval
            .values
            .intern(Value::StructVal { ty: struct_type_id, fields: &self.value_buf[buf_start..] });

        self.value_buf.truncate(buf_start);

        Ok(result)
    }

    fn eval_member(
        &mut self,
        object: hir::LocalId,
        member: sensei_parser::StrId,
    ) -> Result<ValueId, ReturnValue> {
        let obj_vid = self.get_local(object);
        match self.eval.values.lookup(obj_vid) {
            Value::StructVal { ty, fields } => {
                let Some(field_index) = self.eval.types.field_index_by_name(ty, member) else {
                    todo!("diagnostic: unknown struct field");
                };
                Ok(fields[field_index as usize])
            }
            _ => todo!("diagnostic: member access on non-struct"),
        }
    }

    fn eval_call(
        &mut self,
        callee: hir::LocalId,
        args: hir::CallArgsId,
    ) -> Result<ValueId, ReturnValue> {
        let closure_vid = self.get_local(callee);
        let (fn_def_id, captures) = match self.eval.values.lookup(closure_vid) {
            Value::Closure { fn_def, captures } => (fn_def, captures),
            _ => todo!("diagnostic: comptime call on non-function"),
        };

        let capture_start = self.value_buf.len();
        self.value_buf.extend_from_slice(captures);

        let fn_def = self.eval.hir.fns[fn_def_id];
        let params = &self.eval.hir.fn_params[fn_def_id];
        let hir_captures = &self.eval.hir.fn_captures[fn_def_id];
        let arg_locals = &self.eval.hir.call_params[args];

        if params.len() != arg_locals.len() {
            todo!("diagnostic: function argument count mismatch");
        }

        let args_start = self.value_buf.len();
        for &local in arg_locals {
            self.value_buf.push(self.get_local(local));
        }

        let saved_bindings = std::mem::take(&mut self.bindings);

        for (i, capture_info) in hir_captures.iter().enumerate() {
            self.set_local(capture_info.inner_local, self.value_buf[capture_start + i]);
        }

        for (i, param) in params.iter().enumerate() {
            self.set_local(param.local, self.value_buf[args_start + i]);
        }

        self.value_buf.truncate(capture_start);

        let result = match self.interpret_block(fn_def.body) {
            Ok(()) => ValueId::VOID,
            Err(ReturnValue(vid)) => vid,
        };

        self.bindings = saved_bindings;

        Ok(result)
    }
}
