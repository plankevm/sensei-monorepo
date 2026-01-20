use crate::tests::assert_parser_errors;

#[test]
fn test_missing_semicolon() {
    assert_parser_errors(
        r#"const x =
            init {
                if (false) {
                    awesome = a == 5;
                }
            }
            "#,
        &["
                error: unexpected `init`, expected one of `-`, `!`, `~`, decimal literal, hex literal, binary literal, `true`, `false`, `(`, `fn`, `struct`, `if`, `comptime`, identifier
                  --> line 2:13
                   |
                  2|             init {
                   |             ^^^^
            "],
    );
}

#[test]
fn test_unclosed_if() {
    assert_parser_errors(
        r#"run {
            if (wow) {
                my_awesome_statement(3 + a, nice);



        }"#,
        &["
                error: unexpected EOF, expected `}`
                  --> line 7:9
                   |
                  7|         }
                   |         ^
            "],
    );
}

#[test]
fn test_missing_open_run_block() {
    assert_parser_errors(
        r#"
            run }
            "#,
        &["
                error: unexpected `}`, expected `{`
                  --> line 1:5
                   |
                  1| run }
                   |     ^
            "],
    );
}
#[test]
fn test_missing_close_run_block() {
    assert_parser_errors(
        "run {",
        &["
                error: unexpected EOF, expected `}`
                  --> line 1:5
                   |
                  1| run {
                   |     ^
            "],
    );
}

#[test]
fn test_unexpected_token_at_top_level() {
    assert_parser_errors(
        "5;",
        &[
            "
                    error: unexpected decimal literal, expected one of `init`, `run`, `const`
                      --> line 1:1
                       |
                      1| 5;
                       | ^
                ",
            "
                    error: unexpected `;`, expected one of `init`, `run`, `const`
                      --> line 1:2
                       |
                      1| 5;
                       |  ^
                ",
        ],
    );
}

#[test]
fn test_unexpcted_token_post_const_decl() {
    assert_parser_errors(
        r#"const name run {}

            "#,
        &[r#"
                error: unexpected `run`, expected one of `:`, `=`
                  --> line 1:12
                   |
                  1| const name run {}
                   |            ^^^
                "#],
    );
}

#[test]
fn test_const_decl_missing_expr() {
    assert_parser_errors(
        r#"
        const x =
        init { }
        "#,
        &[
            "
            error: unexpected `init`, expected one of `-`, `!`, `~`, decimal literal, hex literal, binary literal, `true`, `false`, `(`, `fn`, `struct`, `if`, `comptime`, identifier
              --> line 2:1
               |
              2| init { }
               | ^^^^
            ",
        ],
    );
}

// ==============================================================================
// Tests exposing brittle/weak parsing patterns
// ==============================================================================

/// Issue: `advance_with_error()` consumes recovery tokens like `init`, causing cascading errors.
/// Input: `const x = \n init { }` (missing value before init)
/// Expected: One error about missing expression, then `init` block parses normally.
/// Actual: `init` gets consumed as error, causing "unexpected `{`" cascade.

/// Issue: `parse_name_path` leaves dot unconsumed when followed by non-identifier.
/// Input: `run { foo.123; }`
/// Ideal: Single error about expecting identifier after `.`.
/// Actual: Dot left unconsumed, causes re-parsing of `123` producing duplicate errors.
#[test]
fn test_name_path_dot_not_followed_by_ident() {
    assert_parser_errors(
        r#"run { foo.123; }"#,
        &[
            // First error from parse_member when it can't find ident after dot
            r#"
                error: unexpected decimal literal, expected identifier
                  --> line 1:11
                   |
                  1| run { foo.123; }
                   |           ^^^
            "#,
            // Second error: `123` re-parsed as statement, cascading error
            r#"
                error: unexpected decimal literal, expected one of identifier, `||`, `&&`, `==`, `!=`, `<`, `>`, `<=`, `>=`, `|`, `^`, `&`, `<<`, `>>`, `+`, `-`, `+%`, `-%`, `*`, `/`, `%`, `*%`, `/+`, `/-`, `/<`, `/>`, `=`, `;`
                  --> line 1:11
                   |
                  1| run { foo.123; }
                   |           ^^^
            "#,
        ],
    );
}

/// Issue: `parse_field_list` breaks silently on unexpected tokens without error.
/// Input: `const S = struct { x: u32, 123 y: u32 };`
/// Ideal: One error about unexpected token, then continue parsing remaining fields.
/// Actual: Silent break causes massive cascade - every subsequent token errors.
#[test]
fn test_field_list_garbage_silent_exit() {
    assert_parser_errors(
        r#"const S = struct { x: u32, 123 y: u32 };"#,
        &[
            // First error from parse_struct_def expecting `}`
            r#"
                error: unexpected decimal literal, expected `}`
                  --> line 1:28
                   |
                  1| const S = struct { x: u32, 123 y: u32 };
                   |                            ^^^
            "#,
            // Cascading: parse_const_decl expects `;` after struct
            r#"
                error: unexpected decimal literal, expected one of `}`, `||`, `&&`, `==`, `!=`, `<`, `>`, `<=`, `>=`, `|`, `^`, `&`, `<<`, `>>`, `+`, `-`, `+%`, `-%`, `*`, `/`, `%`, `*%`, `/+`, `/-`, `/<`, `/>`, `;`
                  --> line 1:28
                   |
                  1| const S = struct { x: u32, 123 y: u32 };
                   |                            ^^^
            "#,
            // Cascading: top-level expects init/run/const
            r#"
                error: unexpected decimal literal, expected one of `}`, `||`, `&&`, `==`, `!=`, `<`, `>`, `<=`, `>=`, `|`, `^`, `&`, `<<`, `>>`, `+`, `-`, `+%`, `-%`, `*`, `/`, `%`, `*%`, `/+`, `/-`, `/<`, `/>`, `;`, `init`, `run`, `const`
                  --> line 1:28
                   |
                  1| const S = struct { x: u32, 123 y: u32 };
                   |                            ^^^
            "#,
            r#"
                error: unexpected identifier, expected one of `init`, `run`, `const`
                  --> line 1:32
                   |
                  1| const S = struct { x: u32, 123 y: u32 };
                   |                                ^
            "#,
            r#"
                error: unexpected `:`, expected one of `init`, `run`, `const`
                  --> line 1:33
                   |
                  1| const S = struct { x: u32, 123 y: u32 };
                   |                                 ^
            "#,
            r#"
                error: unexpected identifier, expected one of `init`, `run`, `const`
                  --> line 1:35
                   |
                  1| const S = struct { x: u32, 123 y: u32 };
                   |                                   ^^^
            "#,
            r#"
                error: unexpected `}`, expected one of `init`, `run`, `const`
                  --> line 1:39
                   |
                  1| const S = struct { x: u32, 123 y: u32 };
                   |                                       ^
            "#,
            r#"
                error: unexpected `;`, expected one of `init`, `run`, `const`
                  --> line 1:40
                   |
                  1| const S = struct { x: u32, 123 y: u32 };
                   |                                        ^
            "#,
        ],
    );
}

/// Issue: `parse_arg_list` breaks silently after comma when expression parsing fails.
/// Input: `run { foo(a, , b); }`
/// Ideal: One error about missing argument, then continue parsing `b`.
/// Actual: Silent break after first `,`, remaining tokens cause cascading errors.
#[test]
fn test_arg_list_empty_after_comma() {
    assert_parser_errors(
        r#"run { foo(a, , b); }"#,
        &[
            // parse_call expects `)` after arg_list breaks
            r#"
                error: unexpected `,`, expected one of `-`, `!`, `~`, decimal literal, hex literal, binary literal, `true`, `false`, `(`, `fn`, `struct`, `if`, `comptime`, identifier, `)`
                  --> line 1:14
                   |
                  1| run { foo(a, , b); }
                   |              ^
            "#,
            // `,` re-parsed as statement expression, expects `=` or `;`
            r#"
                error: unexpected `,`, expected one of `-`, `!`, `~`, decimal literal, hex literal, binary literal, `true`, `false`, `(`, `fn`, `struct`, `if`, `comptime`, identifier, `)`, `||`, `&&`, `==`, `!=`, `<`, `>`, `<=`, `>=`, `|`, `^`, `&`, `<<`, `>>`, `+`, `+%`, `-%`, `*`, `/`, `%`, `*%`, `/+`, `/-`, `/<`, `/>`, `=`, `;`
                  --> line 1:14
                   |
                  1| run { foo(a, , b); }
                   |              ^
            "#,
            // `)` seen as unexpected in statement context
            r#"
                error: unexpected `)`, expected one of `||`, `&&`, `==`, `!=`, `<`, `>`, `<=`, `>=`, `|`, `^`, `&`, `<<`, `>>`, `+`, `-`, `+%`, `-%`, `*`, `/`, `%`, `*%`, `/+`, `/-`, `/<`, `/>`, `=`, `;`
                  --> line 1:17
                   |
                  1| run { foo(a, , b); }
                   |                 ^
            "#,
        ],
    );
}

/// Issue: `parse_param_list` breaks silently when parameter parsing fails.
/// Input: `const f = fn(x: u32, , y: u32) -> u32 { return x; };`
/// Ideal: One error about empty parameter, then continue parsing `y: u32`.
/// Actual: Catastrophic cascade - 16 errors! Every remaining token triggers an error.
#[test]
fn test_param_list_empty_after_comma() {
    assert_parser_errors(
        r#"const f = fn(x: u32, , y: u32) -> u32 { return x; };"#,
        &[
            // parse_fn_def expects `)` after param_list breaks
            r#"
                error: unexpected identifier, expected `)`
                  --> line 1:24
                   |
                  1| const f = fn(x: u32, , y: u32) -> u32 { return x; };
                   |                        ^
            "#,
            // Then expects `->` or `{`
            r#"
                error: unexpected identifier, expected one of `)`, `->`, `{`
                  --> line 1:24
                   |
                  1| const f = fn(x: u32, , y: u32) -> u32 { return x; };
                   |                        ^
            "#,
            // Cascading through block recovery
            r#"
                error: unexpected identifier, expected one of `)`, `->`, `{`, `}`, `||`, `&&`, `==`, `!=`, `<`, `>`, `<=`, `>=`, `|`, `^`, `&`, `<<`, `>>`, `+`, `-`, `+%`, `-%`, `*`, `/`, `%`, `*%`, `/+`, `/-`, `/<`, `/>`, `;`
                  --> line 1:24
                   |
                  1| const f = fn(x: u32, , y: u32) -> u32 { return x; };
                   |                        ^
            "#,
            // Bubbles up to top-level
            r#"
                error: unexpected identifier, expected one of `)`, `->`, `{`, `}`, `||`, `&&`, `==`, `!=`, `<`, `>`, `<=`, `>=`, `|`, `^`, `&`, `<<`, `>>`, `+`, `-`, `+%`, `-%`, `*`, `/`, `%`, `*%`, `/+`, `/-`, `/<`, `/>`, `;`, `init`, `run`, `const`
                  --> line 1:24
                   |
                  1| const f = fn(x: u32, , y: u32) -> u32 { return x; };
                   |                        ^
            "#,
            // Every subsequent token errors at top-level
            r#"
                error: unexpected `:`, expected one of `init`, `run`, `const`
                  --> line 1:25
                   |
                  1| const f = fn(x: u32, , y: u32) -> u32 { return x; };
                   |                         ^
            "#,
            r#"
                error: unexpected identifier, expected one of `init`, `run`, `const`
                  --> line 1:27
                   |
                  1| const f = fn(x: u32, , y: u32) -> u32 { return x; };
                   |                           ^^^
            "#,
            r#"
                error: unexpected `)`, expected one of `init`, `run`, `const`
                  --> line 1:30
                   |
                  1| const f = fn(x: u32, , y: u32) -> u32 { return x; };
                   |                              ^
            "#,
            r#"
                error: unexpected `->`, expected one of `init`, `run`, `const`
                  --> line 1:32
                   |
                  1| const f = fn(x: u32, , y: u32) -> u32 { return x; };
                   |                                ^^
            "#,
            r#"
                error: unexpected identifier, expected one of `init`, `run`, `const`
                  --> line 1:35
                   |
                  1| const f = fn(x: u32, , y: u32) -> u32 { return x; };
                   |                                   ^^^
            "#,
            r#"
                error: unexpected `{`, expected one of `init`, `run`, `const`
                  --> line 1:39
                   |
                  1| const f = fn(x: u32, , y: u32) -> u32 { return x; };
                   |                                       ^
            "#,
            r#"
                error: unexpected `return`, expected one of `init`, `run`, `const`
                  --> line 1:41
                   |
                  1| const f = fn(x: u32, , y: u32) -> u32 { return x; };
                   |                                         ^^^^^^
            "#,
            r#"
                error: unexpected identifier, expected one of `init`, `run`, `const`
                  --> line 1:48
                   |
                  1| const f = fn(x: u32, , y: u32) -> u32 { return x; };
                   |                                                ^
            "#,
            r#"
                error: unexpected `;`, expected one of `init`, `run`, `const`
                  --> line 1:49
                   |
                  1| const f = fn(x: u32, , y: u32) -> u32 { return x; };
                   |                                                 ^
            "#,
            r#"
                error: unexpected `}`, expected one of `init`, `run`, `const`
                  --> line 1:51
                   |
                  1| const f = fn(x: u32, , y: u32) -> u32 { return x; };
                   |                                                   ^
            "#,
            r#"
                error: unexpected `;`, expected one of `init`, `run`, `const`
                  --> line 1:52
                   |
                  1| const f = fn(x: u32, , y: u32) -> u32 { return x; };
                   |                                                    ^
            "#,
        ],
    );
}

/// Issue: `expect_ident` returns None without creating error node in member access.
/// Input: `run { foo.; }`
/// Expected: Error about missing identifier after `.`.
/// Actual: Error emitted but no error node in CST.
#[test]
fn test_member_access_missing_ident() {
    assert_parser_errors(
        r#"run { foo.; }"#,
        &[r#"
                error: unexpected `;`, expected identifier
                  --> line 1:11
                   |
                  1| run { foo.; }
                   |           ^
            "#],
    );
}

/// Issue: Binary expression RHS uses `advance_with_error()` without checking recovery.
/// Input: `run { x = 1 + ; }`
/// Ideal: Error about missing operand after `+`, then continue parsing.
/// Actual: `;` consumed as error node, causing missing `;` error at `}`.
#[test]
fn test_binary_expr_missing_rhs() {
    assert_parser_errors(
        r#"run { x = 1 + ; }"#,
        &[
            // `;` was eaten by advance_with_error(), now expects `;` at `}`
            r#"
                error: unexpected `}`, expected one of `||`, `&&`, `==`, `!=`, `<`, `>`, `<=`, `>=`, `|`, `^`, `&`, `<<`, `>>`, `+`, `-`, `+%`, `-%`, `*`, `/`, `%`, `*%`, `/+`, `/-`, `/<`, `/>`, `;`
                  --> line 1:17
                   |
                  1| run { x = 1 + ; }
                   |                 ^
            "#,
        ],
    );
}

/// Issue: Unary expression operand uses `advance_with_error()` without checking recovery.
/// Input: `run { x = -; }`
/// Ideal: Error about missing operand after `-`.
/// Actual: `;` consumed as error node, causing missing `;` error at `}`.
#[test]
fn test_unary_expr_missing_operand() {
    assert_parser_errors(
        r#"run { x = -; }"#,
        &[
            // `;` was eaten by advance_with_error(), now expects `;` at `}`
            r#"
                error: unexpected `}`, expected one of `||`, `&&`, `==`, `!=`, `<`, `>`, `<=`, `>=`, `|`, `^`, `&`, `<<`, `>>`, `+`, `-`, `+%`, `-%`, `*`, `/`, `%`, `*%`, `/+`, `/-`, `/<`, `/>`, `;`
                  --> line 1:14
                   |
                  1| run { x = -; }
                   |              ^
            "#,
        ],
    );
}

/// Issue: Paren expression uses `advance_with_error()` for missing inner expr.
/// Input: `run { x = (); }`
/// Ideal: Error about empty parentheses at `)`.
/// Actual: `)` consumed as error node, then expects `)` at `;`.
#[test]
fn test_paren_expr_empty() {
    assert_parser_errors(
        r#"run { x = (); }"#,
        &[
            // `)` was eaten by advance_with_error(), now expects `)` at `;`
            r#"
                error: unexpected `;`, expected `)`
                  --> line 1:13
                   |
                  1| run { x = (); }
                   |             ^
            "#,
        ],
    );
}
