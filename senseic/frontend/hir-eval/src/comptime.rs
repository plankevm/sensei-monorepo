use sensei_core::{Idx, IndexVec};
use sensei_hir::{self as hir, ConstDef};
use sensei_values::{TypeId, ValueId};

use crate::{value::Value, Evaluator};

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

    fn eval_expr(&mut self, expr: hir::Expr) -> Result<ValueId, ReturnValue> {
        match expr {
            hir::Expr::Void => Ok(self.eval.values.intern(Value::Void)),
            hir::Expr::Bool(b) => Ok(self.eval.values.intern(Value::Bool(b))),
            hir::Expr::BigNum(id) => Ok(self.eval.values.intern(Value::BigNum(id))),
            hir::Expr::Type(type_id) => Ok(self.eval.values.intern(Value::Type(type_id))),
            hir::Expr::ConstRef(const_id) => Ok(self.eval.ensure_const_evaluated(const_id)),
            hir::Expr::LocalRef(local_id) => Ok(self.get_local(local_id)),
            hir::Expr::FnDef(fn_def_id) => self.eval_fn_def(fn_def_id),
            hir::Expr::Call { callee, args } => self.eval_call(callee, args),
            hir::Expr::StructDef(struct_def_id) => self.eval_struct_def(struct_def_id),
            hir::Expr::StructLit { ty, fields } => self.eval_struct_lit(ty, fields),
            hir::Expr::Member { object, member } => self.eval_member(object, member),
        }
    }

    fn eval_fn_def(&mut self, fn_def_id: hir::FnDefId) -> Result<ValueId, ReturnValue> {
        let captures = &self.eval.hir.fn_captures[fn_def_id];

        let capture_start = self.value_buf.len();
        for capture in captures {
            self.value_buf.push(self.get_local(capture.outer_local));
        }

        let value_id = self.eval.values.intern(Value::Closure {
            fn_def: fn_def_id,
            captures: &self.value_buf[capture_start..],
        });

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
                _ => panic!("struct field type must be a Type value"),
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

        Ok(self.eval.values.intern(Value::Type(struct_type_id)))
    }

    fn eval_struct_lit(
        &mut self,
        ty: hir::LocalId,
        fields_id: hir::FieldsId,
    ) -> Result<ValueId, ReturnValue> {
        let type_vid = self.get_local(ty);
        let struct_type_id = match self.eval.values.lookup(type_vid) {
            Value::Type(tid) => tid,
            _ => panic!("struct literal type must be a Type value"),
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
                let field_index =
                    self.eval.types.field_index_by_name(ty, member).expect("no such field");
                Ok(fields[field_index as usize])
            }
            _ => panic!("member access on non-struct value"),
        }
    }

    fn eval_call(
        &mut self,
        _callee: hir::LocalId,
        _args: hir::CallArgsId,
    ) -> Result<ValueId, ReturnValue> {
        todo!("comptime function call interpretation")
    }
}
