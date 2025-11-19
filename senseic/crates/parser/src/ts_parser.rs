use allocator_api2::vec::Vec;
use bumpalo::Bump;
use smallvec::SmallVec;
use tree_sitter::{Node, Parser, TreeCursor};

use crate::{StringInterner, ast::*};

struct Cursor<'tree>(TreeCursor<'tree>);

impl<'tree> std::ops::Deref for Cursor<'tree> {
    type Target = TreeCursor<'tree>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'tree> std::ops::DerefMut for Cursor<'tree> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'tree> Cursor<'tree> {
    fn unnamed_then_ignore(&mut self) {
        let skipping = self.next();
        debug_assert!(!skipping.is_named(), "tried to skip named");
    }

    fn next(&mut self) -> Node<'tree> {
        let node = self.node();
        self.0.goto_next_sibling();
        node
    }

    fn next_expect(&mut self, expected_kind: &'static str) -> Node<'tree> {
        let node = self.next();
        debug_assert_eq!(node.kind(), expected_kind);
        node
    }

    fn enter_current_node<F, O>(&mut self, f: F) -> O
    where
        F: FnOnce(&mut Self) -> O,
    {
        assert!(self.0.goto_first_child(), "failed to enter, no children");
        let output = f(self);
        self.0.goto_parent();
        output
    }

    fn with_next<F, O>(&mut self, f: F) -> O
    where
        F: FnOnce(&mut Self, Node<'tree>) -> O,
    {
        let node = self.node();
        let output = f(self, node);
        self.goto_next_sibling();
        output
    }
}

fn check_no_error<'tree>(node: Node<'tree>, cursor: &mut Cursor<'tree>) {
    let start = node.start_position();
    let line = start.row + 1;
    let column = start.column + 1;
    assert!(!node.is_error(), "found error node L{}:{}", line, column);
    assert!(!node.is_missing(), "found missing node L{}:{}", line, column);
    let children = node.child_count();
    if children == 0 {
        return;
    }

    cursor.enter_current_node(|cursor| {
        for _ in 0..children {
            cursor.with_next(|cursor, child| {
                check_no_error(child, cursor);
            })
        }
    });
}

pub fn parse_stuff<'src, 'ast>(
    source: &'src str,
    arena: &'ast Bump,
) -> (Ast<'ast>, StringInterner) {
    let mut interner = StringInterner::with_capacity_and_hasher(256, Default::default());
    let mut parser = Parser::new();

    let language = tree_sitter_sensei::LANGUAGE.into();
    parser.set_language(&language).expect("Error loading sensei tree-sitter language");

    let tree = parser.parse(source, None).expect("parsing failed");
    let root = tree.root_node();
    let ast = convert_root_to_ast(root, arena, &mut interner);

    (ast, interner)
}

fn convert_root_to_ast<'tree, 'ast>(
    root: Node<'tree>,
    arena: &'ast Bump,
    interner: &mut StringInterner,
) -> Ast<'ast> {
    let mut declarations = Vec::with_capacity_in(32, arena);

    let mut cursor = Cursor(root.walk());

    check_no_error(root, &mut cursor);

    cursor.enter_current_node(|cursor| {
        for _ in 0..root.child_count() {
            cursor.with_next(|cursor, declaration| {
                declarations.extend(convert_decl(declaration, cursor, arena, interner));
            })
        }
    });

    Ast { declarations }
}

fn convert_decl<'tree, 'ast>(
    declaration: Node<'tree>,
    cursor: &mut Cursor<'tree>,
    arena: &'ast Bump,
    interner: &mut StringInterner,
) -> Option<Declaration<'ast>> {
    if !declaration.is_named() {
        return None;
    }

    Some(match declaration.kind() {
        "const_item" => {
            println!("const!");
            cursor.enter_current_node(|cursor| {
                for _ in 0..declaration.child_count() {
                    let child = cursor.next();
                    println!("  child.kind(): {:?}", child.kind());
                }
            });
            return None;
        }
        "run" => Declaration::Run(cursor.enter_current_node(|cursor| {
            cursor.unnamed_then_ignore();
            let block = cursor.next_expect("block");
            convert_block(block, cursor, arena, interner)
        })),
        "init" => Declaration::Init(cursor.enter_current_node(|cursor| {
            cursor.unnamed_then_ignore();
            let block = cursor.next_expect("block");
            convert_block(block, cursor, arena, interner)
        })),
        kind => panic!("unexpected declaration kind: {:?}", kind),
    })
}

fn convert_block<'tree, 'ast>(
    block: Node<'tree>,
    cursor: &mut Cursor<'tree>,
    arena: &'ast Bump,
    interner: &mut StringInterner,
) -> Block<'ast> {
    cursor.enter_current_node(|cursor| {
        let mut last_expr = None;
        let mut statements = SmallVec::<[Statement<'ast>; 16]>::new();

        for _ in 0..block.child_count() {
            cursor.with_next(|cursor, child| {
                let field = cursor.field_name();
                if !child.is_named() {
                    return;
                }

                match field {
                    Some("stmts") => statements.push(convert_stmt(child, cursor, arena, interner)),
                    Some("last_expr") => {
                        last_expr = Some(arena.alloc(convert_expr(child, cursor, arena, interner)));
                    }
                    _ => panic!("Node {:?} with unexpected field {:?}", child.kind(), field),
                }
            })
        }
        Block { statements: arena.alloc(statements), last_expr }
    })
}

fn convert_stmt<'tree, 'ast>(
    stmt: Node<'tree>,
    cursor: &mut Cursor<'tree>,
    arena: &'ast Bump,
    interner: &mut StringInterner,
) -> Statement<'ast> {
    println!("stmt [{:?}]", stmt.kind());
    match stmt.kind() {
        "let" => Statement::Let(arena.alloc(convert_let(stmt, cursor, arena, interner))),
        kind => panic!("Unknown stmt node {:?}", kind),
    }
}

fn convert_let<'tree, 'ast>(
    r#let: Node<'tree>,
    cursor: &mut Cursor<'tree>,
    arena: &'ast Bump,
    interner: &mut StringInterner,
) -> LetStmt<'ast> {
}

fn convert_expr<'tree, 'ast>(
    block: Node<'tree>,
    cursor: &mut Cursor<'tree>,
    arena: &'ast Bump,
    interner: &mut StringInterner,
) -> Expr<'ast> {
    todo!()
}
