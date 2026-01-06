use crate::Span;
use crate::ast::*;
use crate::comptime_value::*;

pub fn interpret(runtime: &Expr) -> Result<Expr, InterpretError> {
    let mut interpreter = Interpreter::new();

    let out = interpreter.partial_eval(runtime);
    println!("Scope tree:\n{}", interpreter.fmt_scope_tree());

    out
}

#[derive(Debug, Clone)]
pub struct InterpretError {
    pub message: String,
    pub spans: Vec<Span<usize>>,
}

impl InterpretError {
    pub fn new(message: impl Into<String>, span: Span<usize>) -> Self {
        Self {
            message: message.into(),
            spans: vec![span],
        }
    }

    pub fn naked(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            spans: vec![],
        }
    }
}

pub trait PushErrSpan<T> {
    fn push_err_span(self, span: Span<usize>) -> Result<T, InterpretError>;
}

impl<T> PushErrSpan<T> for Result<T, InterpretError> {
    fn push_err_span(self, span: Span<usize>) -> Result<T, InterpretError> {
        self.map_err(|mut e| {
            e.spans.push(span);
            e
        })
    }
}

#[derive(Debug, Clone)]
struct Scope {
    parent: ScopeId,
    bind: Box<str>,
    value: ValueOrFree,
}

#[derive(Debug, Clone)]
enum ValueOrFree {
    Value(Value),
    Free,
}

#[derive(Debug, Clone)]
struct Interpreter {
    scope_tree: Vec<Scope>,
    current_scope: ScopeId,
}

fn short_fmt(value: impl std::fmt::Debug, max_len: usize) -> String {
    let str = format!("{:?}", value);
    if str.len() > max_len {
        format!("{}...", &str[..max_len])
    } else {
        str
    }
}

impl Interpreter {
    const ROOT_SCOPE: ScopeId = ScopeId(0);

    fn new() -> Self {
        let scope_tree = Vec::with_capacity(128);
        let mut i = Self {
            scope_tree,
            current_scope: Self::ROOT_SCOPE,
        };

        // Types
        i.bind("void", Type::Void);
        i.bind("i32", Type::Num);
        i.bind("bool", Type::Bool);
        i.bind("memptr", Type::MemoryPointer);
        i.bind("type", Type::Type);
        i.bind("fn", Type::Function);

        i
    }

    fn bind(&mut self, name: impl AsRef<str>, value: impl Into<Value>) {
        self.scope_tree.push(Scope {
            parent: self.current_scope,
            bind: name.as_ref().into(),
            value: ValueOrFree::Value(value.into()),
        });
        self.current_scope = ScopeId(self.scope_tree.len());
    }

    fn bind_free(&mut self, name: impl AsRef<str>) {
        let parent = self.current_scope;
        self.scope_tree.push(Scope {
            parent,
            bind: name.as_ref().into(),
            value: ValueOrFree::Free,
        });
        self.current_scope = ScopeId(self.scope_tree.len());
    }

    fn get(&self, name: &str) -> Option<&ValueOrFree> {
        let mut scope_id = self.current_scope;
        while scope_id != Self::ROOT_SCOPE {
            let scope = &self.scope_tree[scope_id.0 - 1];
            if name == &scope.bind as &str {
                return Some(&scope.value);
            }
            scope_id = scope.parent;
        }
        return None;
    }

    fn fmt_scope_tree(&self) -> String {
        use std::fmt::Write;
        let mut output = String::new();

        for (i, scope) in self.scope_tree.iter().enumerate().rev() {
            writeln!(
                output,
                "  [{}] {:?} = {} (parent: {})",
                i + 1,
                &scope.bind as &str,
                short_fmt(&scope.value, 60),
                scope.parent.0
            )
            .unwrap();
        }

        output
    }

    fn fmt_scope(&self, mut id: ScopeId) -> String {
        use std::fmt::Write;
        let mut output = String::new();

        while id != Self::ROOT_SCOPE {
            let scope = &self.scope_tree[id.0 - 1];
            writeln!(
                output,
                "  [{}] {:?} = {} (parent: {})",
                id.0,
                &scope.bind as &str,
                short_fmt(&scope.value, 60),
                scope.parent.0
            )
            .unwrap();
            id = scope.parent;
        }

        output
    }

    fn comptime_eval(&mut self, expr: &Expr) -> Result<Value, InterpretError> {
        let span = expr.span;
        let v = match &expr.kind {
            ExprKind::Value(v) => Value::clone(v),
            ExprKind::Var(name) => match self.get(&name) {
                Some(ValueOrFree::Value(v)) => v.clone(),
                Some(ValueOrFree::Free) => {
                    return Err(InterpretError::new(
                        format!("Comptime expression references free variable {:?}", name),
                        span,
                    ));
                }
                None => {
                    return Err(InterpretError::new(
                        format!("Undefined reference {:?}", name),
                        span,
                    ));
                }
            },
            ExprKind::IfThenElse(if_else) => {
                let cond = self.comptime_eval(&if_else.condition).push_err_span(span)?;
                let Value::Bool(cond) = cond else {
                    return Err(InterpretError::new(
                        format!("Expected boolean, got: {:?}", cond),
                        span,
                    ));
                };
                if cond {
                    self.comptime_eval(&if_else.true_branch)
                        .push_err_span(span)?
                } else {
                    self.comptime_eval(&if_else.false_branch)
                        .push_err_span(span)?
                }
            }
            ExprKind::FuncDef(func_def) => self.eval_func_def(&func_def)?.into(),
            ExprKind::FuncApp(func_app) => {
                let func = self.comptime_eval(&func_app.func_expr)?;
                let apply = self.comptime_eval(&func_app.applying_expr)?;
                match func {
                    Value::Closure(closure) => self.eval_closure(*closure, apply, span)?,
                    non_func => {
                        return Err(InterpretError::new(
                            format!("Expected function, got: {:?}", non_func),
                            span,
                        ));
                    }
                }
            }
            ExprKind::StructDef(struct_def) => {
                let capture = self.comptime_eval(&struct_def.capture)?;
                let fields = struct_def
                    .fields
                    .iter()
                    .map(|field| {
                        let type_value = self.comptime_eval(&field.r#type)?;
                        let r#type = Self::as_type(type_value, field.span)?;
                        Ok((field.name.name.clone(), r#type))
                    })
                    .collect::<Result<_, _>>()?;
                Value::Type(Box::new(Type::Struct(StructType {
                    def_uuid: struct_def.def_uuid,
                    fields,
                    capture,
                })))
            }
            ExprKind::BuiltinCall(call) => self.eval_builtin(call).push_err_span(span)?,
            ExprKind::MemberAccess(_) | ExprKind::StructInit(_) => {
                return Err(InterpretError::new(
                    format!("comptime: unimplemented: <{}>", short_fmt(&expr.kind, 60)),
                    expr.span,
                ));
            }
        };

        Ok(v)
    }

    fn as_type(value: Value, error_span: Span<usize>) -> Result<Type, InterpretError> {
        match value {
            Value::Type(r#type) => Ok(*r#type),
            non_type => Err(InterpretError::new(
                format!(
                    "Expected closure type expression to evaluate to type, got: {:?}",
                    non_type.get_type()
                ),
                error_span,
            )),
        }
    }

    fn eval_func_def(&mut self, func_def: &FuncDef) -> Result<Closure, InterpretError> {
        let type_value = self.comptime_eval(&func_def.bind_type_expr)?;
        let r#type = Self::as_type(type_value, func_def.bind_type_expr.span)?;
        Ok(Closure {
            r#type,
            is_comptime: func_def.is_comptime,
            recursive_name: func_def.recursive_name.clone().map(|name| name.name),
            binds: func_def.func_bind.name.clone(),
            body: func_def.body.clone(),
            captures: self.current_scope,
        })
    }

    fn eval_closure(
        &mut self,
        closure: Closure,
        apply: Value,
        span: Span<usize>,
    ) -> Result<Value, InterpretError> {
        let apply_type = apply.get_type();
        if apply_type != closure.r#type {
            return Err(InterpretError::new(
                format!(
                    "Type mismatch: expected {:?}, got: {:?}",
                    apply_type, closure.r#type
                ),
                span,
            ));
        }

        let return_scope = self.current_scope;
        self.current_scope = closure.captures;
        self.bind(&closure.binds, apply);
        if let Some(recurse_bind) = &closure.recursive_name {
            self.bind(recurse_bind, Value::Closure(Box::new(closure.clone())));
        }

        let body_res = self.comptime_eval(&closure.body).push_err_span(span);
        self.current_scope = return_scope;

        body_res
    }

    fn eval_builtin(&mut self, call: &BuiltinCall) -> Result<Value, InterpretError> {
        let mut values = call.arguments.iter().map(|arg| self.comptime_eval(arg));
        let v = match call.builtin {
            Builtin::IsStruct => {
                let r#type = values.next().expect("missing bcall arg")?;
                let Value::Type(r#type) = r#type else {
                    return Err(InterpretError::naked(format!(
                        "Cannot determine struct-ness of non-type value <{:?}>",
                        r#type.get_type()
                    )));
                };
                Value::Bool(r#type.is_struct())
            }
            Builtin::GetTotalStructFields => {
                let struct_type = values.next().expect("missing bcall arg")?;
                let field_count = match struct_type {
                    Value::Type(r#type) => match *r#type {
                        Type::Struct(s) => s.fields.len() as i32,
                        non_struct => {
                            return Err(InterpretError::naked(format!(
                                "Cannot get struct field count of non-struct type <{:?}>",
                                non_struct
                            )));
                        }
                    },
                    non_type => {
                        return Err(InterpretError::naked(format!(
                            "Cannot get struct field count of non-type value <{:?}>",
                            non_type.get_type()
                        )));
                    }
                };
                Value::Num(field_count)
            }
            Builtin::GetStructField => {
                let struct_type = values.next().expect("missing bcall arg")?;
                let field_index = values.next().expect("missing bcall arg")?;
                let r#struct = match struct_type {
                    Value::Type(r#type) => match *r#type {
                        Type::Struct(s) => s,
                        non_struct => {
                            return Err(InterpretError::naked(format!(
                                "Cannot get struct field count of non-struct type <{:?}>",
                                non_struct
                            )));
                        }
                    },
                    non_type => {
                        return Err(InterpretError::naked(format!(
                            "Cannot get struct field count of non-type value <{:?}>",
                            non_type.get_type()
                        )));
                    }
                };
                let index = match field_index {
                    Value::Num(i) if i >= 0 => i as usize,
                    Value::Num(i) => {
                        return Err(InterpretError::naked(format!(
                            "Struct field index expected to be positive, got: {}",
                            i
                        )));
                    }
                    non_num => {
                        return Err(InterpretError::naked(format!(
                            "Expected struct field index to be number, got: {:?}",
                            non_num.get_type()
                        )));
                    }
                };
                let Some((_, field_type)) = r#struct.fields.get(index) else {
                    return Err(InterpretError::naked(format!(
                        "Struct field index out of bounds (index = {}, total fields = {})",
                        index,
                        r#struct.fields.len()
                    )));
                };
                Value::Type(Box::new(field_type.clone()))
            }
            Builtin::Add => {
                let x = values.next().expect("missing bcall arg")?;
                let y = values.next().expect("missing bcall arg")?;
                let Value::Num(x) = x else {
                    return Err(InterpretError::naked(format!(
                        "Unsupported type for addition (lhs): {:?}",
                        x.get_type()
                    )));
                };
                let Value::Num(y) = y else {
                    return Err(InterpretError::naked(format!(
                        "Unsupported type for addition (rhs): {:?}",
                        y.get_type()
                    )));
                };
                Value::Num(x.wrapping_add(y))
            }
            Builtin::Eq => {
                let x = values.next().expect("missing bcall arg")?;
                let y = values.next().expect("missing bcall arg")?;
                Value::Bool(x == y)
            }
            builtin => {
                return Err(InterpretError::naked(format!(
                    "comptime: unimplemented builtin <{:?}>",
                    builtin
                )));
            }
        };
        Ok(v)
    }

    fn partially_eval_value(&mut self, value: &Value) -> Result<Value, InterpretError> {
        let v = match value {
            Value::Closure(closure) => {
                let mut closure = *closure.clone();
                if !closure.is_comptime {
                    let return_scope = self.current_scope;
                    self.current_scope = closure.captures;

                    self.bind_free(&closure.binds);
                    if let Some(recursive_bind) = &closure.recursive_name {
                        self.bind_free(recursive_bind);
                    }
                    closure.body = self.partial_eval(&closure.body)?;

                    self.current_scope = return_scope;
                }

                closure.into()
            }
            non_closure => non_closure.clone(),
        };
        Ok(v)
    }

    fn partial_eval(&mut self, expr: &Expr) -> Result<Expr, InterpretError> {
        let span = expr.span;
        let kind = match &expr.kind {
            ExprKind::Var(name) => {
                let bound_value = self.get(name).ok_or_else(|| {
                    InterpretError::new(
                        format!(
                            "Undefined name {:?}\n{}",
                            name,
                            self.fmt_scope(self.current_scope)
                        ),
                        span,
                    )
                })?;

                match bound_value {
                    ValueOrFree::Value(v) => ExprKind::Value(Box::new(v.clone())),
                    ValueOrFree::Free => ExprKind::Var(name.clone()),
                }
            }
            ExprKind::Value(value) => self.partially_eval_value(value)?.into(),
            ExprKind::BuiltinCall(bcall) => {
                if bcall.builtin.comptime_only() {
                    self.eval_builtin(bcall)?.into()
                } else {
                    let arguments = bcall
                        .arguments
                        .iter()
                        .map(|arg| self.partial_eval(arg))
                        .collect::<Result<_, _>>()?;
                    ExprKind::BuiltinCall(Box::new(BuiltinCall {
                        builtin: bcall.builtin,
                        arguments,
                    }))
                }
            }
            ExprKind::FuncApp(func_app) => {
                let func_expr = self.partial_eval(&func_app.func_expr)?;
                let applying_expr = self.partial_eval(&func_app.applying_expr)?;
                let closure = match &func_expr.kind {
                    ExprKind::Value(v) => match v as &Value {
                        Value::Closure(closure) if closure.is_comptime => Some(*closure.clone()),
                        _ => None,
                    },
                    ExprKind::FuncDef(func_def) if func_def.is_comptime => {
                        Some(self.eval_func_def(func_def)?)
                    }
                    _ => None,
                };

                if let Some(closure) = closure {
                    let apply_value = match applying_expr.kind {
                        ExprKind::Value(apply_value) => *apply_value,
                        ExprKind::FuncDef(func_def) => self.eval_func_def(&func_def)?.into(),
                        _ => {
                            return Err(InterpretError::new(
                                format!(
                                    "Applying non-value to comptime closure [2]: {}",
                                    &applying_expr
                                ),
                                span,
                            ));
                        }
                    };
                    let closure_result = self
                        .eval_closure(closure, apply_value, span)
                        .push_err_span(span)?;
                    self.partially_eval_value(&closure_result)
                        .push_err_span(span)?
                        .into()
                } else {
                    ExprKind::FuncApp(Box::new(FuncApp {
                        func_expr,
                        applying_expr,
                    }))
                }
            }
            ExprKind::FuncDef(func_def) => {
                let mut func_def = func_def.clone();

                let type_value = self.comptime_eval(&func_def.bind_type_expr)?;
                let r#type = Self::as_type(type_value, func_def.bind_type_expr.span)?;
                func_def.bind_type_expr = Expr {
                    span: func_def.bind_type_expr.span,
                    kind: r#type.into(),
                };

                if !func_def.is_comptime {
                    let return_scope = self.current_scope;
                    self.bind_free(&func_def.func_bind.name);
                    func_def.body = self.partial_eval(&func_def.body)?;
                    self.current_scope = return_scope;
                }

                ExprKind::FuncDef(func_def)
            }
            ExprKind::IfThenElse(_) => expr.kind.clone(),
            _ => {
                return Err(InterpretError::new(
                    format!(
                        "partial-eval: expr type <{}>, not yet implemented",
                        short_fmt(&expr.kind, 60)
                    ),
                    span,
                ));
            }
        };
        let e = Expr { kind, span };
        Ok(e)
    }
}
