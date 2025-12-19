use crate::Span;
use crate::ast;
use crate::ast::IfThenElse;
use crate::ast::MemberAccess;
use crate::comptime_value::*;
use std::collections::HashMap;

pub fn interpret(create_runtime: &ast::Expr) -> Result<Value, InterpretError> {
    let mut ctx = InterpretContext::new();

    eval(create_runtime, &mut ctx)
}

#[derive(Debug, Clone)]
pub struct InterpretError {
    pub message: String,
    pub span: Span<usize>,
}

#[derive(Debug, Clone)]
struct Scope {
    parent_scope: Option<ScopeId>,
    binds: HashMap<Box<str>, Value>,
}

#[derive(Debug, Clone)]
struct InterpretContext {
    scopes: Vec<Scope>,
    current_scope: ScopeId,
}

#[derive(Debug)]
struct OverlappingBindNameInScope;

impl OverlappingBindNameInScope {
    fn to_interpret_err(&self, name: impl AsRef<str>, span: Span<usize>) -> InterpretError {
        InterpretError {
            message: format!("Duplicate binding {:?} in scope", name.as_ref()),
            span,
        }
    }
}

impl InterpretContext {
    fn new() -> Self {
        let root_scope = Scope {
            parent_scope: None,
            binds: HashMap::new(),
        };
        let mut ctx = Self {
            scopes: vec![root_scope],
            current_scope: ScopeId(0),
        };
        ctx.bind_in_current_scope("void", Type::Void.into())
            .unwrap();
        ctx.bind_in_current_scope("i32", Type::Num.into()).unwrap();
        ctx.bind_in_current_scope("bool", Type::Bool.into())
            .unwrap();
        ctx.bind_in_current_scope("memptr", Type::MemoryPointer.into())
            .unwrap();
        ctx.bind_in_current_scope("type", Type::Type.into())
            .unwrap();
        ctx.bind_in_current_scope("function", Type::Function.into())
            .unwrap();
        ctx
    }
    fn get(&self, name: impl AsRef<str>) -> Option<&Value> {
        let name = name.as_ref();
        let mut current = Some(self.current_scope);
        while let Some(scope) = current {
            let scope = &self.scopes[scope.0];
            if let Some(value) = scope.binds.get(name) {
                return Some(value);
            }
            current = scope.parent_scope;
        }
        None
    }

    fn bind_in_current_scope(
        &mut self,
        name: impl AsRef<str>,
        value: Value,
    ) -> Result<(), OverlappingBindNameInScope> {
        let name = name.as_ref();
        let scope = &mut self.scopes[self.current_scope.0];
        match scope.binds.insert(name.into(), value) {
            Some(_) => Err(OverlappingBindNameInScope),
            None => Ok(()),
        }
    }

    fn push_new_child_scope(&mut self) {
        let new_child_scope = Scope {
            parent_scope: Some(self.current_scope),
            binds: HashMap::new(),
        };
        let scope_id = ScopeId(self.scopes.len());
        self.scopes.push(new_child_scope);
        self.current_scope = scope_id;
    }

    fn pop_scope(&mut self) {
        let parent = self.scopes[self.current_scope.0]
            .parent_scope
            .expect("tried to pop root scope");
        self.current_scope = parent;
    }
}

fn eval(expr: &ast::Expr, ctx: &mut InterpretContext) -> Result<Value, InterpretError> {
    use ast::ExprKind;
    let span = expr.span;
    let v = match &expr.kind {
        ExprKind::ConstVoid => Value::Void,
        ExprKind::ConstInt(x) => Value::Num(*x),
        ExprKind::ConstBool(x) => Value::Bool(*x),
        ExprKind::Var(name) => ctx.get(&name).cloned().ok_or_else(|| InterpretError {
            message: format!("Reference {name:?} not found"),
            span,
        })?,
        ExprKind::Value(value) => *(value.clone()),
        ExprKind::IfThenElse(if_else) => {
            let cond = match eval(&if_else.condition, ctx)? {
                Value::Bool(cond) => cond,
                non_bool => {
                    return Err(InterpretError {
                        message: format!(
                            "Expected if-else condition to be boolean, got: {:?}",
                            non_bool
                        ),
                        span,
                    });
                }
            };
            if cond {
                eval(&if_else.true_branch, ctx)?
            } else {
                eval(&if_else.false_branch, ctx)?
            }
        }
        ExprKind::Block(block) => {
            ctx.push_new_child_scope();
            for r#let in &block.lets {
                let value = eval(&r#let.assigned, ctx)?;
                let bind = &r#let.bind_local;
                ctx.bind_in_current_scope(&bind.name, value)
                    .map_err(|e| e.to_interpret_err(&bind.name, bind.span))?;
            }
            let block_end_value = eval(&block.end_expr, ctx)?;
            ctx.pop_scope();
            block_end_value
        }
        ExprKind::FuncDef(func_def) => {
            let r#type = match eval(&func_def.bind_type_expr, ctx)? {
                Value::Type(r#type) => r#type,
                non_type_value => {
                    return Err(InterpretError {
                        message: format!(
                            "Expected closure type expression to evaluate to type, got: {:?}",
                            non_type_value
                        ),
                        span: func_def.bind_type_expr.span,
                    });
                }
            };
            Value::Closure(Box::new(Closure {
                r#type: *r#type,
                binds: func_def.func_bind.name.clone(),
                body: partial_eval(&func_def.body, ctx), // TODO (partial eval)
                captures: ctx.current_scope,
            }))
        }
        ExprKind::StructDef(struct_def) => {
            ctx.push_new_child_scope();
            let defs = struct_def
                .associated_defs
                .iter()
                .map(|r#let| {
                    let value = eval(&r#let.assigned, ctx)?;
                    let bind = &r#let.bind_local;
                    ctx.bind_in_current_scope(&r#let.bind_local.name, value.clone())
                        .map_err(|e| e.to_interpret_err(&bind.name, bind.span))?;
                    Ok(value)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let fields = struct_def
                .fields
                .iter()
                .map(|field| {
                    let r#type = match eval(&field.r#type, ctx)? {
                        Value::Type(r#type) => r#type,
                        non_type_value => {
                            return Err(InterpretError {
                                message: format!(
                                    "Expected struct field type to evaluate to type, got: {:?}",
                                    non_type_value
                                ),
                                span: field.r#type.span,
                            });
                        }
                    };
                    Ok((field.name.name.clone(), *r#type))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let struct_type = StructType {
                def_uuid: struct_def.def_uuid,
                defs,
                fields,
            };
            ctx.pop_scope();
            Type::Struct(struct_type).into()
        } // _ => {
          //     return Err(InterpretError {
          //         message: format!("Unimplemented expression kind"),
          //         span: expr.span,
          //     });
          // }
    };
    Ok(v)
}

fn partial_eval(expr: &ast::Expr, ctx: &mut InterpretContext) -> ast::Expr {
    use ast::{Expr, ExprKind};
    let new_kind = match &expr.kind {
        ExprKind::ConstVoid => ExprKind::Value(Box::new(Value::Void)),
        ExprKind::ConstInt(x) => ExprKind::Value(Box::new(Value::Num(*x))),
        ExprKind::ConstBool(b) => ExprKind::Value(Box::new(Value::Bool(*b))),
        ExprKind::Var(name) => match ctx.get(name) {
            Some(v) => ExprKind::Value(Box::new(v.clone())),
            None => ExprKind::Var(name.clone()),
        },
        ExprKind::MemberAccess(member_access) => {
            let r#struct = partial_eval(&member_access.r#struct, ctx);
            ExprKind::MemberAccess(Box::new(MemberAccess {
                r#struct,
                member: member_access.member.clone(),
            }))
        }
        ExprKind::IfThenElse(if_then_else) => {
            let condition = partial_eval(&if_then_else.condition, ctx);
            let known_bool = match &condition.kind {
                ExprKind::Value(value) => match value as &Value {
                    Value::Bool(b) => Some(*b),
                    _ => None,
                },
                _ => None,
            };
            match known_bool {
                Some(true) => return partial_eval(&if_then_else.true_branch, ctx),
                Some(false) => return partial_eval(&if_then_else.false_branch, ctx),
                None => {
                    let true_branch = partial_eval(&if_then_else.true_branch, ctx);
                    let false_branch = partial_eval(&if_then_else.false_branch, ctx);
                    ExprKind::IfThenElse(Box::new(IfThenElse {
                        condition,
                        true_branch,
                        false_branch,
                    }))
                }
            }
        }
        _ => expr.kind.clone(),
    };
    Expr {
        kind: new_kind,
        span: expr.span,
    }
}
