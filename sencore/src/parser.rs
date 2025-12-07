use crate::ast::*;
use crate::lexer::{Lexer, Token};

use crate::span::Span;

#[derive(Debug, Clone)]
pub struct SNode<'src> {
    pub kind: SNodeKind<'src>,
    pub span: Span<usize>,
}

impl<'src> SNode<'src> {
    pub fn new(kind: SNodeKind<'src>, span: Span<usize>) -> Self {
        Self { kind, span }
    }
}

#[derive(Debug, Clone)]
pub enum SNodeKind<'src> {
    Num(i32),
    Bool(bool),
    Name(&'src str),
    List(Vec<SNode<'src>>),
}

pub struct Parser<'src> {
    source: &'src str,
    tokens: std::iter::Peekable<Lexer<'src>>,
}

macro_rules! snode {
    ($name:ident, $span:expr) => {
        SNode::new(SNodeKind::$name, $span)
    };
    ($name:ident, $value:expr, $span:expr) => {
        SNode::new(SNodeKind::$name($value), $span)
    };
}

#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
    pub span: Span<usize>,
}

pub struct LoweringCtx {
    next_struct_id: u32,
}

impl LoweringCtx {
    pub fn new() -> Self {
        Self { next_struct_id: 0 }
    }

    fn alloc_struct_id(&mut self) -> u32 {
        let id = self.next_struct_id;
        self.next_struct_id += 1;
        id
    }
}

impl Default for LoweringCtx {
    fn default() -> Self {
        Self::new()
    }
}

fn expect_name<'src>(node: &SNode<'src>) -> Result<Name, ParseError> {
    match &node.kind {
        SNodeKind::Name(name) => Ok(Name {
            name: (*name).into(),
            span: node.span,
        }),
        _ => Err(ParseError {
            message: format!("Expected name, got {:?}", node.kind),
            span: node.span,
        }),
    }
}

fn expect_list<'src, 'a>(node: &'a SNode<'src>) -> Result<&'a [SNode<'src>], ParseError> {
    match &node.kind {
        SNodeKind::List(list) => Ok(list.as_slice()),
        _ => Err(ParseError {
            message: format!("Expected list, got {:?}", node.kind),
            span: node.span,
        }),
    }
}

impl<'src> Parser<'src> {
    pub fn new(source: &'src str) -> Self {
        Self {
            source,
            tokens: Lexer::new(source).peekable(),
        }
    }

    pub fn parse_list(&mut self) -> Result<Option<SNode<'src>>, ParseError> {
        let eof_span = Span::new(self.source.len(), self.source.len());

        let tok = self.tokens.next();
        let start_span = match tok {
            Some((Token::RoundOpen, start_span)) => start_span,
            Some((ty, span)) => {
                return Err(ParseError {
                    message: format!("Unexpected token {:?}, expected '(' or EOF", ty),
                    span,
                });
            }
            None => return Ok(None),
        };

        let mut children = Vec::new();
        let mut end_span;

        loop {
            let (ty, span) = *self.tokens.peek().ok_or_else(|| ParseError {
                message: format!("Unexpected EOF, expected <list_item> or EOF"),
                span: eof_span,
            })?;
            end_span = span;
            match ty {
                Token::True => {
                    self.tokens.next();
                    children.push(snode!(Bool, true, span));
                }
                Token::False => {
                    self.tokens.next();
                    children.push(snode!(Bool, false, span));
                }
                Token::RoundClose => {
                    self.tokens.next();
                    break;
                }
                Token::Ident(name) => {
                    self.tokens.next();
                    children.push(snode!(Name, name, span));
                }
                Token::Num(num) => {
                    self.tokens.next();
                    let num = num.parse().expect("lexer didn't validate num");
                    children.push(snode!(Num, num, span));
                }
                Token::RoundOpen => {
                    children.push(
                        self.parse_list()?
                            .expect("expected Some(list)/error got: None"),
                    );
                }
                Token::Error => {
                    return Err(ParseError {
                        message: format!(
                            "Invalid character sequence: {:?}",
                            &self.source[span.range()]
                        ),
                        span,
                    });
                }
            }
        }

        Ok(Some(snode!(
            List,
            children,
            Span::new(start_span.start, end_span.end)
        )))
    }
}

/// (apply e1 e2 ... eN) => left-fold into FuncApp: ((e1 e2) e3) ... eN
fn lower_apply(
    ctx: &mut LoweringCtx,
    span: Span<usize>,
    args: &[SNode],
) -> Result<Expr, ParseError> {
    let (first, remaining_args) = args.split_first().ok_or_else(|| ParseError {
        message: format!("apply requires at least 1 argument, got 0"),
        span,
    })?;

    let first = snode_to_expr(ctx, first)?;
    remaining_args.iter().try_fold(first, |acc, node| {
        let arg = snode_to_expr(ctx, node)?;
        Ok(Expr {
            span: Span::new(acc.span.start, arg.span.end),
            kind: ExprKind::FuncApp(Box::new(FuncApp {
                func_expr: acc,
                applying_expr: arg,
            })),
        })
    })
}

/// (func <bind:name> <type:expr> <body:expr>)
fn lower_func(
    ctx: &mut LoweringCtx,
    span: Span<usize>,
    args: &[SNode],
) -> Result<Expr, ParseError> {
    let [bind, type_expr, body] = args else {
        return Err(ParseError {
            message: format!(
                "func requires exactly 3 arguments (bind, type, body), got {}",
                args.len()
            ),
            span,
        });
    };

    let func_bind = expect_name(bind)?;
    let bind_type_expr = snode_to_expr(ctx, type_expr)?;
    let body = snode_to_expr(ctx, body)?;

    Ok(Expr {
        span,
        kind: ExprKind::FuncDef(Box::new(FuncDef {
            func_bind,
            bind_type_expr,
            body,
        })),
    })
}

/// (if <condition> <true_branch> <false_branch>)
fn lower_if(ctx: &mut LoweringCtx, span: Span<usize>, args: &[SNode]) -> Result<Expr, ParseError> {
    let [cond, then_branch, else_branch] = args else {
        return Err(ParseError {
            message: format!(
                "if requires exactly 3 arguments (condition, then, else), got {}",
                args.len()
            ),
            span,
        });
    };

    let condition = snode_to_expr(ctx, cond)?;
    let true_branch = snode_to_expr(ctx, then_branch)?;
    let false_branch = snode_to_expr(ctx, else_branch)?;

    Ok(Expr {
        span,
        kind: ExprKind::IfThenElse(Box::new(IfThenElse {
            span,
            condition,
            true_branch,
            false_branch,
        })),
    })
}

/// (block (<name> <type>? <value>)* <result>)
fn lower_block(
    ctx: &mut LoweringCtx,
    span: Span<usize>,
    args: &[SNode],
) -> Result<Expr, ParseError> {
    let (end_node, let_nodes) = args.split_last().ok_or_else(|| ParseError {
        message: "block requires at least a result expression".into(),
        span,
    })?;

    let lets = let_nodes
        .iter()
        .map(|node| lower_let_bind(ctx, node))
        .collect::<Result<Vec<_>, _>>()?;
    let end_expr = snode_to_expr(ctx, end_node)?;

    Ok(Expr {
        span,
        kind: ExprKind::Block(Box::new(Block { lets, end_expr })),
    })
}

/// (attr <path_segment:name>+ <struct_expr>)
/// Left-fold: (attr a b expr) => MemberAccess(MemberAccess(expr, a), b)
fn lower_attr(
    ctx: &mut LoweringCtx,
    span: Span<usize>,
    args: &[SNode],
) -> Result<Expr, ParseError> {
    if args.len() < 2 {
        return Err(ParseError {
            message: format!(
                "attr requires at least 2 arguments (path segment(s) and struct expr), got {}",
                args.len()
            ),
            span,
        });
    }

    let (struct_node, path_segments) = args.split_last().unwrap();
    let mut acc = snode_to_expr(ctx, struct_node)?;

    for seg_node in path_segments {
        let member = expect_name(seg_node)?;
        acc = Expr {
            span: Span::new(acc.span.start, member.span.end),
            kind: ExprKind::MemberAccess(Box::new(MemberAccess {
                r#struct: acc,
                member,
            })),
        };
    }

    Ok(acc)
}

/// (struct_def (fields (<name> <type>)*) (defs <def_node>*))
fn lower_struct(
    ctx: &mut LoweringCtx,
    span: Span<usize>,
    args: &[SNode],
) -> Result<Expr, ParseError> {
    let [fields_node, defs_node] = args else {
        return Err(ParseError {
            message: format!(
                "struct requires exactly 2 arguments (fields, defs), got {}",
                args.len()
            ),
            span,
        });
    };

    // Parse fields: (fields (<name> <type>)*)
    let fields_list = expect_list(fields_node)?;
    let fields_span = fields_node.span;

    let (fields_keyword, field_entries) = fields_list.split_first().ok_or_else(|| ParseError {
        message: "fields list cannot be empty, must start with 'fields' keyword".into(),
        span: fields_span,
    })?;

    match &fields_keyword.kind {
        SNodeKind::Name("fields") => {}
        _ => {
            return Err(ParseError {
                message: format!("Expected 'fields' keyword, got {:?}", fields_keyword.kind),
                span: fields_keyword.span,
            });
        }
    }

    let mut fields = Vec::with_capacity(field_entries.len());
    for field_node in field_entries {
        let field_list = expect_list(field_node)?;
        let [name_node, type_node] = field_list else {
            return Err(ParseError {
                message: format!(
                    "field must have exactly 2 elements (name, type), got {}",
                    field_list.len()
                ),
                span: field_node.span,
            });
        };

        let name = expect_name(name_node)?;
        let r#type = snode_to_expr(ctx, type_node)?;
        fields.push(StructField {
            span: field_node.span,
            name,
            r#type,
        });
    }

    // Parse defs: (defs <def_node>*)
    let defs_list = expect_list(defs_node)?;

    let (defs_keyword, def_entries) = defs_list.split_first().ok_or_else(|| ParseError {
        message: "defs list cannot be empty, must start with 'defs' keyword".into(),
        span: defs_node.span,
    })?;

    match &defs_keyword.kind {
        SNodeKind::Name("defs") => {}
        _ => {
            return Err(ParseError {
                message: format!("Expected 'defs' keyword, got {:?}", defs_keyword.kind),
                span: defs_keyword.span,
            });
        }
    }

    let associated_defs = def_entries
        .iter()
        .map(|def_node| lower_let_bind(ctx, def_node))
        .collect::<Result<Vec<_>, _>>()?;

    let def_uuid = ctx.alloc_struct_id();

    Ok(Expr {
        span,
        kind: ExprKind::StructDef(Box::new(StructDef {
            def_uuid,
            fields_span,
            fields,
            associated_defs,
        })),
    })
}

/// (struct_init <struct_type:expr> (<field:name> <value:expr>)*)
fn lower_struct_init(
    ctx: &mut LoweringCtx,
    span: Span<usize>,
    args: &[SNode],
) -> Result<Expr, ParseError> {
    let (type_node, field_nodes) = args.split_first().ok_or_else(|| ParseError {
        message: "struct_init requires at least a struct type argument".into(),
        span,
    })?;

    let struct_type = snode_to_expr(ctx, type_node)?;

    let mut fields = Vec::with_capacity(field_nodes.len());
    for field_node in field_nodes {
        let field_list = expect_list(field_node)?;
        let [name_node, value_node] = field_list else {
            return Err(ParseError {
                message: format!(
                    "struct_init field must have exactly 2 elements (name, value), got {}",
                    field_list.len()
                ),
                span: field_node.span,
            });
        };

        let name = expect_name(name_node)?;
        let value = snode_to_expr(ctx, value_node)?;
        fields.push(StructInitField {
            span: field_node.span,
            name,
            value,
        });
    }

    Ok(Expr {
        span,
        kind: ExprKind::StructInit(Box::new(StructInit {
            struct_type,
            fields,
        })),
    })
}

fn lower_builtin_args<const N: usize>(
    ctx: &mut LoweringCtx,
    span: Span<usize>,
    name: &str,
    args: &[SNode],
) -> Result<Box<BuiltinInvoke<N>>, ParseError> {
    let arg_nodes: &[SNode; N] = args.try_into().map_err(|_| ParseError {
        message: format!(
            "`{name}` requires exactly {N} argument{}, got {}",
            if N == 1 { "" } else { "s" },
            args.len()
        ),
        span,
    })?;
    let args = arg_nodes
        .iter()
        .map(|node| snode_to_expr(ctx, node))
        .collect::<Result<Vec<_>, _>>()?
        .try_into()
        .unwrap();
    Ok(Box::new(BuiltinInvoke { args }))
}

fn snode_to_expr(ctx: &mut LoweringCtx, node: &SNode) -> Result<Expr, ParseError> {
    let expr = |kind| Expr {
        span: node.span,
        kind,
    };
    let e = match &node.kind {
        SNodeKind::Num(x) => expr(ExprKind::ConstInt(*x)),
        SNodeKind::Bool(b) => expr(ExprKind::ConstBool(*b)),
        SNodeKind::Name(name) => expr(ExprKind::Var((*name).into())),
        SNodeKind::List(list) => match list.as_slice() {
            [] => expr(ExprKind::ConstVoid),
            [single] => return snode_to_expr(ctx, single),
            [kind_node, args @ ..] => {
                let SNodeKind::Name(form_name) = &kind_node.kind else {
                    return Err(ParseError {
                        message: format!(
                            "Expected form name (identifier), got {:?}",
                            kind_node.kind
                        ),
                        span: kind_node.span,
                    });
                };
                match *form_name {
                    "apply" => lower_apply(ctx, node.span, args)?,
                    "func" => lower_func(ctx, node.span, args)?,
                    "if" => lower_if(ctx, node.span, args)?,
                    "block" => lower_block(ctx, node.span, args)?,
                    "attr" => lower_attr(ctx, node.span, args)?,
                    "struct_def" => lower_struct(ctx, node.span, args)?,
                    "struct_init" => lower_struct_init(ctx, node.span, args)?,
                    "add" => expr(ExprKind::Add(lower_builtin_args(
                        ctx, node.span, form_name, args,
                    )?)),
                    "eq" => expr(ExprKind::Eq(lower_builtin_args(
                        ctx, node.span, form_name, args,
                    )?)),
                    "type_of" => expr(ExprKind::TypeOf(lower_builtin_args(
                        ctx, node.span, form_name, args,
                    )?)),
                    "malloc" => expr(ExprKind::MemoryAllocate(lower_builtin_args(
                        ctx, node.span, form_name, args,
                    )?)),
                    "ptr_store" => expr(ExprKind::PointerStore(lower_builtin_args(
                        ctx, node.span, form_name, args,
                    )?)),
                    "ptr_load" => expr(ExprKind::PointerLoad(lower_builtin_args(
                        ctx, node.span, form_name, args,
                    )?)),
                    "return" => expr(ExprKind::RuntimeReturn(lower_builtin_args(
                        ctx, node.span, form_name, args,
                    )?)),
                    "copy_input" => expr(ExprKind::LoadInput(lower_builtin_args(
                        ctx, node.span, form_name, args,
                    )?)),
                    "input_size" => expr({
                        if !args.is_empty() {
                            return Err(ParseError {
                                message: format!(
                                    "`input_size` takes no arguments, got: {}",
                                    args.len()
                                ),
                                span: node.span,
                            });
                        }
                        ExprKind::InputSize
                    }),
                    other => {
                        return Err(ParseError {
                            message: format!("Unknown form: {}", other),
                            span: kind_node.span,
                        });
                    }
                }
            }
        },
    };
    Ok(e)
}

fn lower_let_bind(ctx: &mut LoweringCtx, node: &SNode) -> Result<LetBind, ParseError> {
    let let_list = expect_list(node)?;
    let let_span = node.span;

    match let_list {
        [name_node, value_node] => Ok(LetBind {
            span: let_span,
            bind_local: expect_name(name_node)?,
            local_type: None,
            assigned: snode_to_expr(ctx, value_node)?,
        }),
        [name_node, type_node, value_node] => Ok(LetBind {
            span: let_span,
            bind_local: expect_name(name_node)?,
            local_type: Some(snode_to_expr(ctx, type_node)?),
            assigned: snode_to_expr(ctx, value_node)?,
        }),
        _ => Err(ParseError {
            message: format!(
                "let binding must have 2 (name, value) or 3 (name, type, value) elements, got {}",
                let_list.len()
            ),
            span: let_span,
        }),
    }
}

pub fn lower_sexpr_to_ast(main: &SNode) -> Result<Ast, ParseError> {
    let mut ctx = LoweringCtx::new();
    let runtime_main = snode_to_expr(&mut ctx, main)?;
    Ok(Ast { runtime_main })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_and_lower(source: &str) -> Result<Ast, ParseError> {
        let mut parser = Parser::new(source);
        let node = parser.parse_list()?.expect("expected at least one s-expr");
        lower_sexpr_to_ast(&node)
    }

    #[test]
    fn test_lower_constants() {
        let ast = parse_and_lower("(42)").unwrap();
        assert!(matches!(ast.runtime_main.kind, ExprKind::ConstInt(42)));

        let ast = parse_and_lower("(true)").unwrap();
        assert!(matches!(ast.runtime_main.kind, ExprKind::ConstBool(true)));

        let ast = parse_and_lower("(())").unwrap();
        assert!(matches!(ast.runtime_main.kind, ExprKind::ConstVoid));
    }

    #[test]
    fn test_lower_var() {
        let ast = parse_and_lower("(foo)").unwrap();
        assert!(matches!(&ast.runtime_main.kind, ExprKind::Var(name) if &**name == "foo"));
    }

    #[test]
    fn test_lower_if() {
        let ast = parse_and_lower("(if true 1 2)").unwrap();
        assert!(matches!(ast.runtime_main.kind, ExprKind::IfThenElse(_)));
    }

    #[test]
    fn test_lower_block() {
        let ast = parse_and_lower("(block (x 10) (y word 20) x)").unwrap();
        let ExprKind::Block(block) = &ast.runtime_main.kind else {
            panic!("Expected Block");
        };
        assert_eq!(block.lets.len(), 2);
        assert!(block.lets[0].local_type.is_none());
        assert!(block.lets[1].local_type.is_some());
    }

    #[test]
    fn test_lower_apply() {
        let ast = parse_and_lower("(apply f x y)").unwrap();
        // Should be FuncApp(FuncApp(f, x), y)
        let ExprKind::FuncApp(outer) = &ast.runtime_main.kind else {
            panic!("Expected FuncApp");
        };
        assert!(matches!(outer.func_expr.kind, ExprKind::FuncApp(_)));
    }

    #[test]
    fn test_lower_func() {
        let ast = parse_and_lower("(func x word x)").unwrap();
        assert!(matches!(ast.runtime_main.kind, ExprKind::FuncDef(_)));
    }

    #[test]
    fn test_lower_builtins() {
        let ast = parse_and_lower("(add 1 2)").unwrap();
        assert!(matches!(ast.runtime_main.kind, ExprKind::Add(_)));

        let ast = parse_and_lower("(eq 1 2)").unwrap();
        assert!(matches!(ast.runtime_main.kind, ExprKind::Eq(_)));

        let ast = parse_and_lower("(type_of x)").unwrap();
        assert!(matches!(ast.runtime_main.kind, ExprKind::TypeOf(_)));
    }

    #[test]
    fn test_lower_attr() {
        let ast = parse_and_lower("(attr foo bar my_struct)").unwrap();
        // Should be MemberAccess(MemberAccess(my_struct, foo), bar)
        let ExprKind::MemberAccess(outer) = &ast.runtime_main.kind else {
            panic!("Expected MemberAccess");
        };
        assert_eq!(&*outer.member.name, "bar");
        let ExprKind::MemberAccess(inner) = &outer.r#struct.kind else {
            panic!("Expected inner MemberAccess");
        };
        assert_eq!(&*inner.member.name, "foo");
    }

    #[test]
    fn test_lower_struct() {
        let ast = parse_and_lower("(struct_def (fields (x word) (y bool)) (defs))").unwrap();
        let ExprKind::StructDef(s) = &ast.runtime_main.kind else {
            panic!("Expected StructDef");
        };
        assert_eq!(s.fields.len(), 2);
        assert_eq!(s.def_uuid, 0);
    }

    #[test]
    fn test_lower_struct_with_defs() {
        let ast = parse_and_lower(
            "(struct_def (fields (x word)) (defs (new (func self word self)) (get_x word 42)))",
        )
        .unwrap();
        let ExprKind::StructDef(s) = &ast.runtime_main.kind else {
            panic!("Expected StructDef");
        };
        assert_eq!(s.fields.len(), 1);
        assert_eq!(s.associated_defs.len(), 2);
        assert_eq!(&*s.associated_defs[0].bind_local.name, "new");
        assert!(s.associated_defs[0].local_type.is_none());
        assert_eq!(&*s.associated_defs[1].bind_local.name, "get_x");
        assert!(s.associated_defs[1].local_type.is_some());
    }

    #[test]
    fn test_lower_struct_init() {
        let ast = parse_and_lower("(struct_init Point (x 10) (y 20))").unwrap();
        let ExprKind::StructInit(s) = &ast.runtime_main.kind else {
            panic!("Expected StructInit");
        };
        assert_eq!(s.fields.len(), 2);
        assert_eq!(&*s.fields[0].name.name, "x");
        assert_eq!(&*s.fields[1].name.name, "y");
    }

    #[test]
    fn test_lower_struct_init_empty() {
        let ast = parse_and_lower("(struct_init EmptyStruct)").unwrap();
        let ExprKind::StructInit(s) = &ast.runtime_main.kind else {
            panic!("Expected StructInit");
        };
        assert_eq!(s.fields.len(), 0);
    }
}
