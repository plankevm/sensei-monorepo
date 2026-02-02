use super::{assert_parses_to_cst_no_errors, dedent_preserve_indent};

fn assert_parses_to_cst_no_errors_dedented(source: &str, expected: &str) {
    assert_parses_to_cst_no_errors(
        &dedent_preserve_indent(source),
        &dedent_preserve_indent(expected),
    );
}

// =============================================================================
// Literals
// =============================================================================

#[test]
fn test_literal_bool_true() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = true;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                " "
                LiteralExpr
                    "true"
                ";"
        "#,
    );
}

#[test]
fn test_literal_bool_false() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = false;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                " "
                LiteralExpr
                    "false"
                ";"
        "#,
    );
}

#[test]
fn test_literal_hex() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = 0xFF;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                " "
                LiteralExpr
                    "0xFF"
                ";"
        "#,
    );
}

#[test]
fn test_literal_binary() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = 0b1010;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                " "
                LiteralExpr
                    "0b1010"
                ";"
        "#,
    );
}

#[test]
fn test_literal_decimal() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = 3469;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                " "
                LiteralExpr
                    "3469"
                ";"
        "#,
    );
}

// =============================================================================
// Identifiers & Paths
// =============================================================================

#[test]
fn test_ident_simple() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = foo;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                " "
                Identifier
                    "foo"
                ";"
        "#,
    );
}

#[test]
fn test_member_access_single() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = a.b;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                MemberExpr
                    " "
                    Identifier
                        "a"
                    "."
                    Identifier
                        "b"
                ";"
        "#,
    );
}

#[test]
fn test_member_priority() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = 3 * a.b;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                BinaryExpr(Star)
                    " "
                    LiteralExpr
                        "3"
                    " "
                    "*"
                    MemberExpr
                        " "
                        Identifier
                            "a"
                        "."
                        Identifier
                            "b"
                ";"
        "#,
    );
}

#[test]
fn test_member_access_chain() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = a.b.c;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                MemberExpr
                    MemberExpr
                        " "
                        Identifier
                            "a"
                        "."
                        Identifier
                            "b"
                    "."
                    Identifier
                        "c"
                ";"
        "#,
    );
}

// =============================================================================
// Paren Expressions
// =============================================================================

#[test]
fn test_paren_expr_simple() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = (42);",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                " "
                ParenExpr
                    "("
                    LiteralExpr
                        "42"
                    ")"
                ";"
        "#,
    );
}

#[test]
fn test_paren_expr_nested() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = ((a));",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                " "
                ParenExpr
                    "("
                    ParenExpr
                        "("
                        Identifier
                            "a"
                        ")"
                    ")"
                ";"
        "#,
    );
}

// =============================================================================
// Unary Expressions
// =============================================================================

#[test]
fn test_unary_minus() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = -a;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                UnaryExpr(Minus)
                    " "
                    "-"
                    Identifier
                        "a"
                ";"
        "#,
    );
}

#[test]
fn test_unary_not() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = !a;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                UnaryExpr(Bang)
                    " "
                    "!"
                    Identifier
                        "a"
                ";"
        "#,
    );
}

#[test]
fn test_unary_tilde() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = ~a;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                UnaryExpr(Tilde)
                    " "
                    "~"
                    Identifier
                        "a"
                ";"
        "#,
    );
}

#[test]
fn test_unary_nested() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = -~a;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                UnaryExpr(Minus)
                    " "
                    "-"
                    UnaryExpr(Tilde)
                        "~"
                        Identifier
                            "a"
                ";"
        "#,
    );
}

// =============================================================================
// Binary Expressions
// =============================================================================

#[test]
fn test_binary_plus() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = a + b;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                BinaryExpr(Plus)
                    " "
                    Identifier
                        "a"
                    " "
                    "+"
                    " "
                    Identifier
                        "b"
                ";"
        "#,
    );
}

#[test]
fn test_binary_minus() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = a - b;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                BinaryExpr(Minus)
                    " "
                    Identifier
                        "a"
                    " "
                    "-"
                    " "
                    Identifier
                        "b"
                ";"
        "#,
    );
}

#[test]
fn test_binary_double_equals() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = a == b;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                BinaryExpr(DoubleEquals)
                    " "
                    Identifier
                        "a"
                    " "
                    "=="
                    " "
                    Identifier
                        "b"
                ";"
        "#,
    );
}

#[test]
fn test_binary_not_equals() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = a != b;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                BinaryExpr(BangEquals)
                    " "
                    Identifier
                        "a"
                    " "
                    "!="
                    " "
                    Identifier
                        "b"
                ";"
        "#,
    );
}

#[test]
fn test_binary_greater_than() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = a > b;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                BinaryExpr(GreaterThan)
                    " "
                    Identifier
                        "a"
                    " "
                    ">"
                    " "
                    Identifier
                        "b"
                ";"
        "#,
    );
}

#[test]
fn test_binary_and() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = a and b;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                BinaryExpr(And)
                    " "
                    Identifier
                        "a"
                    " "
                    "and"
                    " "
                    Identifier
                        "b"
                ";"
        "#,
    );
}

#[test]
fn test_binary_ampersand() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = a & b;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                BinaryExpr(Ampersand)
                    " "
                    Identifier
                        "a"
                    " "
                    "&"
                    " "
                    Identifier
                        "b"
                ";"
        "#,
    );
}

#[test]
fn test_binary_precedence_mul_add() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = 1 + 2 * 3;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                BinaryExpr(Plus)
                    " "
                    LiteralExpr
                        "1"
                    " "
                    "+"
                    BinaryExpr(Star)
                        " "
                        LiteralExpr
                            "2"
                        " "
                        "*"
                        " "
                        LiteralExpr
                            "3"
                ";"
        "#,
    );
}

#[test]
fn test_binary_precedence_cmp_and() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = a < b and c > d;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                BinaryExpr(And)
                    BinaryExpr(LessThan)
                        " "
                        Identifier
                            "a"
                        " "
                        "<"
                        " "
                        Identifier
                            "b"
                        " "
                    "and"
                    BinaryExpr(GreaterThan)
                        " "
                        Identifier
                            "c"
                        " "
                        ">"
                        " "
                        Identifier
                            "d"
                ";"
        "#,
    );
}

// =============================================================================
// If Expressions
// =============================================================================

#[test]
fn test_if_expr_if_else() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = if a { b; } else { c; };",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                " "
                If
                    "if"
                    " "
                    Identifier
                        "a"
                    " "
                    Block
                        "{"
                        StatementsList
                            " "
                            Identifier
                                "b"
                            ";"
                            " "
                        "}"
                    ElseIfBranchList
                        " "
                        "else"
                        " "
                    Block
                        "{"
                        StatementsList
                            " "
                            Identifier
                                "c"
                            ";"
                            " "
                        "}"
                ";"
        "#,
    );
}

#[test]
fn test_if_expr_if_elseif_else() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = if a { b; } else if c { d; } else { e; };",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                " "
                If
                    "if"
                    " "
                    Identifier
                        "a"
                    " "
                    Block
                        "{"
                        StatementsList
                            " "
                            Identifier
                                "b"
                            ";"
                            " "
                        "}"
                    ElseIfBranchList
                        " "
                        ElseIfBranch
                            "else"
                            " "
                            "if"
                            " "
                            Identifier
                                "c"
                            " "
                            Block
                                "{"
                                StatementsList
                                    " "
                                    Identifier
                                        "d"
                                    ";"
                                    " "
                                "}"
                        " "
                        "else"
                        " "
                    Block
                        "{"
                        StatementsList
                            " "
                            Identifier
                                "e"
                            ";"
                            " "
                        "}"
                ";"
        "#,
    );
}

// =============================================================================
// Function Calls
// =============================================================================

#[test]
fn test_fn_call_zero_args() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = f();",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                CallExpr
                    " "
                    Identifier
                        "f"
                    "("
                    ")"
                ";"
        "#,
    );
}

#[test]
fn test_fn_call_one_arg() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = f(a);",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                CallExpr
                    " "
                    Identifier
                        "f"
                    "("
                    Identifier
                        "a"
                    ")"
                ";"
        "#,
    );
}

#[test]
fn test_fn_call_two_args() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = f(a, b);",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                CallExpr
                    " "
                    Identifier
                        "f"
                    "("
                    Identifier
                        "a"
                    ","
                    " "
                    Identifier
                        "b"
                    ")"
                ";"
        "#,
    );
}

#[test]
fn test_fn_call_trailing_comma() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = f(a, b,);",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                CallExpr
                    " "
                    Identifier
                        "f"
                    "("
                    Identifier
                        "a"
                    ","
                    " "
                    Identifier
                        "b"
                    ","
                    ")"
                ";"
        "#,
    );
}

// =============================================================================
// Function Definitions
// =============================================================================

#[test]
fn test_fn_def_zero_params() {
    assert_parses_to_cst_no_errors_dedented(
        "const f = fn() void {};",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "f"
                " "
                "="
                " "
                FnDef
                    "fn"
                    "("
                    ParamList
                    ")"
                    " "
                    Identifier
                        "void"
                    " "
                    Block
                        "{"
                        StatementsList
                        "}"
                ";"
        "#,
    );
}

#[test]
fn test_fn_def_one_param() {
    assert_parses_to_cst_no_errors_dedented(
        "const f = fn(x: T) void {};",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "f"
                " "
                "="
                " "
                FnDef
                    "fn"
                    "("
                    ParamList
                        Parameter
                            Identifier
                                "x"
                            ":"
                            " "
                            Identifier
                                "T"
                    ")"
                    " "
                    Identifier
                        "void"
                    " "
                    Block
                        "{"
                        StatementsList
                        "}"
                ";"
        "#,
    );
}

#[test]
fn test_fn_def_two_params() {
    assert_parses_to_cst_no_errors_dedented(
        "const f = fn(x: T(void), y: U) void {};",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "f"
                " "
                "="
                " "
                FnDef
                    "fn"
                    "("
                    ParamList
                        Parameter
                            Identifier
                                "x"
                            ":"
                            CallExpr
                                " "
                                Identifier
                                    "T"
                                "("
                                Identifier
                                    "void"
                                ")"
                        ","
                        " "
                        Parameter
                            Identifier
                                "y"
                            ":"
                            " "
                            Identifier
                                "U"
                    ")"
                    " "
                    Identifier
                        "void"
                    " "
                    Block
                        "{"
                        StatementsList
                        "}"
                ";"
        "#,
    );
}

#[test]
fn test_fn_def_with_return_type() {
    assert_parses_to_cst_no_errors_dedented(
        "const f = fn() Wow(32) {};",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "f"
                " "
                "="
                " "
                FnDef
                    "fn"
                    "("
                    ParamList
                    ")"
                    CallExpr
                        " "
                        Identifier
                            "Wow"
                        "("
                        LiteralExpr
                            "32"
                        ")"
                    " "
                    Block
                        "{"
                        StatementsList
                        "}"
                ";"
        "#,
    );
}

#[test]
fn test_fn_def_full() {
    assert_parses_to_cst_no_errors_dedented(
        "const f = fn(x: T) U { x; };",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "f"
                " "
                "="
                " "
                FnDef
                    "fn"
                    "("
                    ParamList
                        Parameter
                            Identifier
                                "x"
                            ":"
                            " "
                            Identifier
                                "T"
                    ")"
                    " "
                    Identifier
                        "U"
                    " "
                    Block
                        "{"
                        StatementsList
                            " "
                            Identifier
                                "x"
                            ";"
                            " "
                        "}"
                ";"
        "#,
    );
}

// =============================================================================
// Struct Definitions
// =============================================================================

#[test]
fn test_struct_def_zero_fields() {
    assert_parses_to_cst_no_errors_dedented(
        "const S = struct {};",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "S"
                " "
                "="
                StructDef
                    " "
                    "struct"
                    " "
                    "{"
                    FieldList
                    "}"
                ";"
        "#,
    );
}

#[test]
fn test_struct_def_one_field() {
    assert_parses_to_cst_no_errors_dedented(
        "const S = struct { x: T };",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "S"
                " "
                "="
                StructDef
                    " "
                    "struct"
                    " "
                    "{"
                    FieldList
                        " "
                        FieldDef
                            Identifier
                                "x"
                            ":"
                            " "
                            Identifier
                                "T"
                            " "
                    "}"
                ";"
        "#,
    );
}

#[test]
fn test_struct_def_two_fields() {
    assert_parses_to_cst_no_errors_dedented(
        "const S = struct { x: T, y: U };",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "S"
                " "
                "="
                StructDef
                    " "
                    "struct"
                    " "
                    "{"
                    FieldList
                        " "
                        FieldDef
                            Identifier
                                "x"
                            ":"
                            " "
                            Identifier
                                "T"
                        ","
                        " "
                        FieldDef
                            Identifier
                                "y"
                            ":"
                            " "
                            Identifier
                                "U"
                            " "
                    "}"
                ";"
        "#,
    );
}

#[test]
fn test_struct_def_trailing_comma() {
    assert_parses_to_cst_no_errors_dedented(
        "const S = struct { x: T, };",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "S"
                " "
                "="
                StructDef
                    " "
                    "struct"
                    " "
                    "{"
                    FieldList
                        " "
                        FieldDef
                            Identifier
                                "x"
                            ":"
                            " "
                            Identifier
                                "T"
                        ","
                        " "
                    "}"
                ";"
        "#,
    );
}

// =============================================================================
// Struct Literals
// =============================================================================

#[test]
fn test_struct_lit_zero_fields() {
    assert_parses_to_cst_no_errors_dedented(
        "const s = S {};",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "s"
                " "
                "="
                StructLit
                    " "
                    Identifier
                        "S"
                    " "
                    "{"
                    FieldList
                    "}"
                ";"
        "#,
    );
}

#[test]
fn test_struct_lit_one_field() {
    assert_parses_to_cst_no_errors_dedented(
        "const s = S { x: 1 };",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "s"
                " "
                "="
                StructLit
                    " "
                    Identifier
                        "S"
                    " "
                    "{"
                    FieldList
                        " "
                        FieldDef
                            Identifier
                                "x"
                            ":"
                            " "
                            LiteralExpr
                                "1"
                            " "
                    "}"
                ";"
        "#,
    );
}

#[test]
fn test_struct_lit_two_fields() {
    assert_parses_to_cst_no_errors_dedented(
        "const s = S { x: 1, y: 2 };",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "s"
                " "
                "="
                StructLit
                    " "
                    Identifier
                        "S"
                    " "
                    "{"
                    FieldList
                        " "
                        FieldDef
                            Identifier
                                "x"
                            ":"
                            " "
                            LiteralExpr
                                "1"
                        ","
                        " "
                        FieldDef
                            Identifier
                                "y"
                            ":"
                            " "
                            LiteralExpr
                                "2"
                            " "
                    "}"
                ";"
        "#,
    );
}

#[test]
fn test_struct_lit_trailing_comma() {
    assert_parses_to_cst_no_errors_dedented(
        "const s = S { x: 1, };",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "s"
                " "
                "="
                StructLit
                    " "
                    Identifier
                        "S"
                    " "
                    "{"
                    FieldList
                        " "
                        FieldDef
                            Identifier
                                "x"
                            ":"
                            " "
                            LiteralExpr
                                "1"
                        ","
                        " "
                    "}"
                ";"
        "#,
    );
}

// =============================================================================
// Blocks
// =============================================================================

#[test]
fn test_block_atom_expr_stmt() {
    assert_parses_to_cst_no_errors_dedented(
        "init { 34; }",
        r#"
        File
            InitBlock
                "init"
                " "
                "{"
                StatementsList
                    " "
                    LiteralExpr
                        "34"
                    ";"
                    " "
                "}"
        "#,
    );
}

#[test]
fn test_block_end_expr() {
    assert_parses_to_cst_no_errors_dedented(
        "init { 34; 35; bob }",
        r#"
        File
            InitBlock
                "init"
                " "
                "{"
                StatementsList
                    " "
                    LiteralExpr
                        "34"
                    ";"
                    " "
                    LiteralExpr
                        "35"
                    ";"
                    " "
                Identifier
                    "bob"
                " "
                "}"
        "#,
    );
}

// =============================================================================
// Let Statements
// =============================================================================

#[test]
fn test_let_basic() {
    assert_parses_to_cst_no_errors_dedented(
        "init { let x = 1; }",
        r#"
        File
            InitBlock
                "init"
                " "
                "{"
                StatementsList
                    " "
                    LetStmt { mutable: false, typed: false }
                        "let"
                        " "
                        Identifier
                            "x"
                        " "
                        "="
                        " "
                        LiteralExpr
                            "1"
                        ";"
                    " "
                "}"
        "#,
    );
}

#[test]
fn test_let_with_mut() {
    assert_parses_to_cst_no_errors_dedented(
        "init { let mut x = 1; }",
        r#"
        File
            InitBlock
                "init"
                " "
                "{"
                StatementsList
                    " "
                    LetStmt { mutable: true, typed: false }
                        "let"
                        " "
                        "mut"
                        " "
                        Identifier
                            "x"
                        " "
                        "="
                        " "
                        LiteralExpr
                            "1"
                        ";"
                    " "
                "}"
        "#,
    );
}

#[test]
fn test_let_with_type() {
    assert_parses_to_cst_no_errors_dedented(
        "init { let x: T = 1; }",
        r#"
        File
            InitBlock
                "init"
                " "
                "{"
                StatementsList
                    " "
                    LetStmt { mutable: false, typed: true }
                        "let"
                        " "
                        Identifier
                            "x"
                        ":"
                        " "
                        Identifier
                            "T"
                        " "
                        "="
                        " "
                        LiteralExpr
                            "1"
                        ";"
                    " "
                "}"
        "#,
    );
}

#[test]
fn test_let_full() {
    assert_parses_to_cst_no_errors_dedented(
        "init { let mut x: T = 1; }",
        r#"
        File
            InitBlock
                "init"
                " "
                "{"
                StatementsList
                    " "
                    LetStmt { mutable: true, typed: true }
                        "let"
                        " "
                        "mut"
                        " "
                        Identifier
                            "x"
                        ":"
                        " "
                        Identifier
                            "T"
                        " "
                        "="
                        " "
                        LiteralExpr
                            "1"
                        ";"
                    " "
                "}"
        "#,
    );
}

// =============================================================================
// Other Statements
// =============================================================================

#[test]
fn test_return_stmt() {
    assert_parses_to_cst_no_errors_dedented(
        "
        init {
            return 42;
        }
        ",
        r#"
        File
            InitBlock
                "init"
                " "
                "{"
                StatementsList
                    "\n    "
                    ReturnStmt
                        "return"
                        " "
                        LiteralExpr
                            "42"
                        ";"
                    "\n"
                "}"
        "#,
    );
}

#[test]
fn test_assign_stmt() {
    assert_parses_to_cst_no_errors_dedented(
        "init { x = 1; }",
        r#"
        File
            InitBlock
                "init"
                " "
                "{"
                StatementsList
                    " "
                    AssignStmt
                        Identifier
                            "x"
                        " "
                        "="
                        " "
                        LiteralExpr
                            "1"
                        ";"
                    " "
                "}"
        "#,
    );
}

#[test]
fn test_assign_stmt_member_expr() {
    assert_parses_to_cst_no_errors_dedented(
        "init { a.b.c = 34; }",
        r#"
        File
            InitBlock
                "init"
                " "
                "{"
                StatementsList
                    " "
                    AssignStmt
                        MemberExpr
                            MemberExpr
                                Identifier
                                    "a"
                                "."
                                Identifier
                                    "b"
                            "."
                            Identifier
                                "c"
                        " "
                        "="
                        " "
                        LiteralExpr
                            "34"
                        ";"
                    " "
                "}"
        "#,
    );
}

#[test]
fn test_assign_stmt_complex_rhs() {
    assert_parses_to_cst_no_errors_dedented(
        "init { x = a + b; }",
        r#"
        File
            InitBlock
                "init"
                " "
                "{"
                StatementsList
                    " "
                    AssignStmt
                        Identifier
                            "x"
                        " "
                        "="
                        BinaryExpr(Plus)
                            " "
                            Identifier
                                "a"
                            " "
                            "+"
                            " "
                            Identifier
                                "b"
                        ";"
                    " "
                "}"
        "#,
    );
}

#[test]
fn test_while_basic() {
    assert_parses_to_cst_no_errors_dedented(
        "init { while x { y; } }",
        r#"
        File
            InitBlock
                "init"
                " "
                "{"
                StatementsList
                    " "
                    WhileStmt
                        "while"
                        " "
                        Identifier
                            "x"
                        " "
                        Block
                            "{"
                            StatementsList
                                " "
                                Identifier
                                    "y"
                                ";"
                                " "
                            "}"
                    " "
                "}"
        "#,
    );
}

#[test]
fn test_while_inline() {
    assert_parses_to_cst_no_errors_dedented(
        "init { inline while x { y; } }",
        r#"
        File
            InitBlock
                "init"
                " "
                "{"
                StatementsList
                    " "
                    InlineWhileStmt
                        "inline"
                        " "
                        "while"
                        " "
                        Identifier
                            "x"
                        " "
                        Block
                            "{"
                            StatementsList
                                " "
                                Identifier
                                    "y"
                                ";"
                                " "
                            "}"
                    " "
                "}"
        "#,
    );
}

#[test]
fn test_if_stmt_if_only() {
    assert_parses_to_cst_no_errors_dedented(
        "init { if x { y; } }",
        r#"
        File
            InitBlock
                "init"
                " "
                "{"
                StatementsList
                    " "
                If
                    "if"
                    " "
                    Identifier
                        "x"
                    " "
                    Block
                        "{"
                        StatementsList
                            " "
                            Identifier
                                "y"
                            ";"
                            " "
                        "}"
                    ElseIfBranchList
                        " "

                "}"
        "#,
    );
}

#[test]
fn test_if_stmt_if_elseif() {
    assert_parses_to_cst_no_errors_dedented(
        r#"
        init {
            if a {
                b;
            } else if 34 {
                d;
            }
        }
        "#,
        r#"
        File
            InitBlock
                "init"
                " "
                "{"
                StatementsList
                    "\n    "
                If
                    "if"
                    " "
                    Identifier
                        "a"
                    " "
                    Block
                        "{"
                        StatementsList
                            "\n        "
                            Identifier
                                "b"
                            ";"
                            "\n    "
                        "}"
                    ElseIfBranchList
                        " "
                        ElseIfBranch
                            "else"
                            " "
                            "if"
                            " "
                            LiteralExpr
                                "34"
                            " "
                            Block
                                "{"
                                StatementsList
                                    "\n        "
                                    Identifier
                                        "d"
                                    ";"
                                    "\n    "
                                "}"
                        "\n"
                "}"
        "#,
    );
}

#[test]
fn test_empty_program() {
    assert_parses_to_cst_no_errors_dedented(
        r#"
        // Wow very nice,
        /* stuf */
        "#,
        r#"
        File
            "// Wow very nice,\n"
            "/* stuf */"
        "#,
    );
}

#[test]
fn test_empty_init_run() {
    let source = r#"
        init {}
        /* something /* very nice */ */
        run {}
        "#;
    assert_parses_to_cst_no_errors_dedented(
        source,
        r#"
        File
            InitBlock
                "init"
                " "
                "{"
                StatementsList
                "}"
            "\n"
            "/* something /* very nice */ */"
            "\n"
            RunBlock
                "run"
                " "
                "{"
                StatementsList
                "}"
        "#,
    );
}

#[test]
fn test_untyped_const_decl() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = 42;",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                " "
                LiteralExpr
                    "42"
                ";"
        "#,
    );
}

#[test]
fn test_typed_const_decl() {
    assert_parses_to_cst_no_errors_dedented(
        "const y: comptime_int = 67;",
        r#"
        File
            ConstDecl { typed: true }
                "const"
                " "
                Identifier
                    "y"
                ":"
                " "
                Identifier
                    "comptime_int"
                " "
                "="
                " "
                LiteralExpr
                    "67"
                ";"
        "#,
    );
}

#[test]
fn test_empty_block_expr() {
    assert_parses_to_cst_no_errors_dedented(
        "const x = {};",
        r#"
        File
            ConstDecl { typed: false }
                "const"
                " "
                Identifier
                    "x"
                " "
                "="
                " "
                Block
                    "{"
                    StatementsList
                    "}"
                ";"
        "#,
    );
}
