use sensei_core::Idx;
use sensei_hir::{self as hir, ConstDef};
use sensei_mir::{self as mir};
use sensei_types::{TypeId, ValueId};

use crate::{Evaluator, value::Value};

#[derive(Clone, Copy)]
pub(crate) enum Local {
    Comptime(ValueId),
    Runtime { mir_local: mir::LocalId, ty: Option<TypeId> },
}

struct BodyLowerer<'a, 'hir> {
    eval: &'a mut Evaluator<'hir>,
    locals: Vec<Local>,
    instructions: Vec<mir::Instruction>,
    local_types: Vec<Option<TypeId>>,
    arg_buf: Vec<mir::LocalId>,
    return_type: Option<TypeId>,
}

impl<'a, 'hir> BodyLowerer<'a, 'hir> {
    fn new(eval: &'a mut Evaluator<'hir>) -> Self {
        Self {
            eval,
            locals: Vec::new(),
            instructions: Vec::new(),
            local_types: Vec::new(),
            arg_buf: Vec::new(),
            return_type: None,
        }
    }

    fn alloc_mir_local(&mut self, ty: Option<TypeId>) -> mir::LocalId {
        let id = mir::LocalId::new(self.local_types.len() as u32);
        self.local_types.push(ty);
        id
    }

    fn set_local(&mut self, local: hir::LocalId, value: Local) {
        let idx = local.get() as usize;
        if idx < self.locals.len() {
            self.locals[idx] = value;
        } else {
            debug_assert_eq!(idx, self.locals.len());
            self.locals.push(value);
        }
    }

    fn get_local(&self, local: hir::LocalId) -> Local {
        self.locals[local.get() as usize]
    }

    fn materialize(&mut self, value_id: ValueId) -> mir::LocalId {
        let value = self.eval.values.lookup(value_id);
        let mir_expr = match value {
            Value::Void => mir::Expr::Void,
            Value::Bool(b) => mir::Expr::Bool(b),
            Value::BigNum(n) => {
                let big_num_id = self
                    .eval
                    .hir
                    .big_nums
                    .enumerate_idx()
                    .find(|&(_, &v)| v == n)
                    .map(|(id, _)| id)
                    .expect("BigNum value not found in HIR big_nums");
                mir::Expr::BigNum(big_num_id)
            }
            // Types are erased at runtime
            Value::Type(_) => return self.alloc_mir_local(None),
            _ => todo!("cannot materialize value"),
        };
        let mir_local = self.alloc_mir_local(None);
        self.instructions.push(mir::Instruction::Set { local: mir_local, expr: mir_expr });
        mir_local
    }

    fn ensure_runtime(&mut self, local: Local) -> mir::LocalId {
        match local {
            Local::Runtime { mir_local, .. } => mir_local,
            Local::Comptime(value_id) => self.materialize(value_id),
        }
    }

    fn eval_expr(&mut self, expr: hir::Expr) -> Local {
        match expr {
            hir::Expr::Void => Local::Comptime(self.eval.values.intern(Value::Void)),
            hir::Expr::Bool(b) => Local::Comptime(self.eval.values.intern(Value::Bool(b))),
            hir::Expr::BigNum(id) => {
                let value = self.eval.hir.big_nums[id];
                Local::Comptime(self.eval.values.intern(Value::BigNum(value)))
            }
            hir::Expr::Type(type_id) => {
                Local::Comptime(self.eval.values.intern(Value::Type(type_id)))
            }
            hir::Expr::ConstRef(const_id) => {
                let value_id = self.eval.ensure_const_evaluated(const_id);
                Local::Comptime(value_id)
            }
            hir::Expr::LocalRef(local_id) => self.get_local(local_id),
            hir::Expr::FnDef(fn_def_id) => {
                let captures = &self.eval.hir.fn_captures[fn_def_id];
                let mut capture_values: Vec<ValueId> = Vec::new();
                for capture in captures {
                    match self.get_local(capture.outer_local) {
                        Local::Comptime(vid) => capture_values.push(vid),
                        Local::Runtime { .. } => todo!("runtime capture not supported"),
                    }
                }
                let params = &self.eval.hir.fn_params[fn_def_id];
                for param in params {
                    if param.comptime {
                        todo!("comptime params");
                    }
                }
                let value_id = self
                    .eval
                    .values
                    .intern(Value::Closure { fn_def: fn_def_id, captures: &capture_values });
                Local::Comptime(value_id)
            }
            hir::Expr::Call { callee, args: call_args_id } => {
                let callee_local = self.get_local(callee);
                let closure_value_id = match callee_local {
                    Local::Comptime(vid) => vid,
                    Local::Runtime { .. } => todo!("runtime callee not supported"),
                };
                let closure = self.eval.values.lookup(closure_value_id);
                let (fn_def_id, captures) = match closure {
                    Value::Closure { fn_def, captures } => (fn_def, captures.to_vec()),
                    _ => panic!("callee is not a function"),
                };

                let mir_fn_id = if let Some(&cached) = self.eval.fn_cache.get(&closure_value_id) {
                    cached
                } else {
                    let fn_id = lower_fn_body(self.eval, fn_def_id, &captures);
                    self.eval.fn_cache.insert(closure_value_id, fn_id);
                    fn_id
                };

                let hir_args: Vec<hir::LocalId> = self.eval.hir.call_params[call_args_id].to_vec();
                let buf_start = self.arg_buf.len();
                for &arg_local in &hir_args {
                    let arg = self.get_local(arg_local);
                    let mir_local = self.ensure_runtime(arg);
                    self.arg_buf.push(mir_local);
                }
                let args = self.eval.mir_args.push_iter(self.arg_buf.drain(buf_start..));

                let mir_local = self.alloc_mir_local(None);
                self.instructions.push(mir::Instruction::Set {
                    local: mir_local,
                    expr: mir::Expr::Call { callee: mir_fn_id, args },
                });
                Local::Runtime { mir_local, ty: None }
            }
            _ => todo!("expr not yet supported"),
        }
    }

    fn walk_block(&mut self, block_id: hir::BlockId) {
        let block = &self.eval.hir.blocks[block_id];
        let len = block.len();
        for i in 0..len {
            let instr = self.eval.hir.blocks[block_id][i];
            self.walk_instruction(instr);
        }
    }

    fn walk_instruction(&mut self, instr: hir::Instruction) {
        match instr {
            hir::Instruction::Set { local, expr } => {
                let value = self.eval_expr(expr);
                match value {
                    Local::Comptime(_) => self.set_local(local, value),
                    Local::Runtime { mir_local: src, ty } => {
                        let dst = self.alloc_mir_local(ty);
                        self.instructions.push(mir::Instruction::Set {
                            local: dst,
                            expr: mir::Expr::LocalRef(src),
                        });
                        self.set_local(local, Local::Runtime { mir_local: dst, ty });
                    }
                }
            }
            hir::Instruction::Eval(expr) => {
                self.eval_expr(expr);
            }
            hir::Instruction::AssertType { value, of_type } => {
                let type_local = self.get_local(of_type);
                let type_id = match type_local {
                    Local::Comptime(vid) => match self.eval.values.lookup(vid) {
                        Value::Type(tid) => tid,
                        _ => panic!("AssertType of_type must be a Type value"),
                    },
                    _ => panic!("AssertType of_type must be comptime"),
                };

                let val = &mut self.locals[value.get() as usize];
                match val {
                    Local::Runtime { ty, .. } => {
                        *ty = Some(type_id);
                    }
                    Local::Comptime(_) => {}
                }
            }
            hir::Instruction::Return(expr) => {
                let value = self.eval_expr(expr);
                if let Local::Runtime { ty: Some(ty), .. } = value {
                    self.return_type = Some(ty);
                }
                let mir_local = self.ensure_runtime(value);
                self.instructions.push(mir::Instruction::Return(mir::Expr::LocalRef(mir_local)));
            }
            _ => todo!("instruction not yet supported"),
        }
    }

    fn flush_as_fn(self, param_count: u32, return_type: TypeId) -> mir::FnId {
        let body = self.eval.mir_blocks.push_iter(self.instructions.into_iter());
        let fn_id = self.eval.mir_fns.push(mir::FnDef { body, param_count, return_type });
        let locals_id = self.eval.mir_fn_locals.push_iter(self.local_types.into_iter());
        debug_assert_eq!(fn_id, locals_id);
        fn_id
    }
}

fn lower_fn_body(
    eval: &mut Evaluator<'_>,
    fn_def_id: hir::FnDefId,
    captures: &[ValueId],
) -> mir::FnId {
    let fn_def = eval.hir.fns[fn_def_id];
    let params: Vec<hir::ParamInfo> = eval.hir.fn_params[fn_def_id].to_vec();
    let hir_captures: Vec<hir::CaptureInfo> = eval.hir.fn_captures[fn_def_id].to_vec();

    let mut lowerer = BodyLowerer::new(eval);

    for (capture_info, &value_id) in hir_captures.iter().zip(captures) {
        lowerer.set_local(capture_info.inner_local, Local::Comptime(value_id));
    }

    let param_count = params.len() as u32;
    for param in &params {
        let mir_local = lowerer.alloc_mir_local(None);
        lowerer.set_local(param.local, Local::Runtime { mir_local, ty: None });
    }

    lowerer.walk_block(fn_def.body);

    let return_type = match lowerer.return_type {
        Some(ty) => ty,
        None => lowerer.eval.types.intern(sensei_types::Type::Void),
    };

    lowerer.flush_as_fn(param_count, return_type)
}

pub(crate) fn eval_const_body(eval: &mut Evaluator<'_>, const_def: ConstDef) -> ValueId {
    let mut lowerer = BodyLowerer::new(eval);
    lowerer.walk_block(const_def.body);
    match lowerer.locals[const_def.result.get() as usize] {
        Local::Comptime(value_id) => value_id,
        Local::Runtime { .. } => panic!("const body produced runtime value"),
    }
}

pub(crate) fn lower_block_as_fn(eval: &mut Evaluator<'_>, hir_block: hir::BlockId) -> mir::FnId {
    let return_type = eval.types.intern(sensei_types::Type::Void);
    let mut lowerer = BodyLowerer::new(eval);
    lowerer.walk_block(hir_block);
    lowerer.flush_as_fn(0, return_type)
}
