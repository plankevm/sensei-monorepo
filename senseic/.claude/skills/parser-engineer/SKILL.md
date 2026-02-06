---
name: parser-engineer
description: Mandatory use when developing or analyzing the parser or other tightly coupled data structures such as the CST & lexer.
---

## File Structure & Organization

**Crate:** `frontend/parser` (`sensei-parser`)

```
frontend/parser/src/
├── lib.rs              # Crate root, re-exports
├── lexer.rs            # Token definitions (logos) and Lexer implementation
├── parser.rs           # Main parser implementation
├── cst/
│   ├── mod.rs          # CST types: Node, NodeKind, NodeIdx, TokenIdx
│   └── display.rs      # Pretty-printing CST for tests/debugging
├── diagnostics.rs      # DiagnosticsContext trait
├── error_report.rs     # Error formatting, LineIndex
└── tests/
    ├── mod.rs          # Test utilities: assert_parses_to_cst_no_errors, etc.
    └── errorless.rs    # Happy-path parsing tests
```

**Key Types:**
- `Token` (lexer.rs): Token enum with all language tokens
- `NodeKind` (cst/mod.rs): CST node variants
- `Node` (cst/mod.rs): CST node with `kind`, `tokens` span, `first_child`, `next_sibling`
- `Parser` (parser.rs): Internal parser state with token stream, node arena, diagnostics

**Grammar Reference:** `docs/Grammar.md`

## Parser Testing Conventions

Tests live in `frontend/parser/src/tests/`. Use the provided test utilities:

**Preferred Pattern:** Inline snapshot-style tests with `assert_parses_to_cst_no_errors_dedented`:

```rust
#[test]
fn test_while_basic() {
    assert_parses_to_cst_no_errors_dedented(
        "init { while x { y; } }",      // Input source
        r#"
        File
            InitBlock
                "init"
                " "
                "{"
                " "
                WhileStmt
                    "while"
                    " "
                    Identifier
                        "x"
                    " "
                    Block
                        "{"
                        ...
                        "}"
                " "
                "}"
        "#,                              // Expected CST structure
    );
}
```

**Key Conventions:**
- Use `dedent_preserve_indent` variant (via `assert_parses_to_cst_no_errors_dedented`) for readable multi-line expected output
- Input and expected output should be inline and adjacent for easy comparison
- Node kinds appear as `NodeKind` (e.g., `WhileStmt`, `BinaryExpr(Plus)`)
- Tokens appear as quoted strings (e.g., `"while"`, `" "`, `"{"`)
- Child nodes are indented under their parent
- Trivia tokens (whitespace, comments) appear in token spans between nodes

**Error Tests:** Use `assert_parser_errors` for testing error recovery:

```rust
#[test]
fn test_missing_semicolon() {
    assert_parser_errors(
        "const x = init { }",
        &["error: unexpected `init`, expected ..."],
    );
}
```

## Parsing Resilience

The parser must be constructed in a resilient way. Resilient parsing recognizes
as much syntactic structure as possible from incomplete or erroneous code. An
error in one function shouldn't break parsing of unrelated functions. A missing
semicolon should produce one error, not dozens of cascading errors.

## Never Crash on Errors

The parser must consume all input regardless of how malformed it is. When encountering unexpected tokens:
- Wrap them in error nodes
- Emit a diagnostic
- Continue parsing

The parser should never panic, return early, or leave tokens unconsumed due to syntax errors.


## Guards Before Parsing

Check for expected tokens before calling sub-parsers:
```rust
if self.at(Token::LeftParen) {
    self.parse_param_list();
}
```

This reduces cascading. The missing `(` is reported once, but we don't enter `parse_param_list` in a broken state where it might consume tokens it shouldn't.

## Avoid Recursion

When possible model the parsing of syntatical constructs as parsing variable
length lists of sub-productions rather than recursively. Recursion in the parser
consumes the stack and artificially limits how large/nested certain constructs
can become.

## Tree Representation

We use a homogenous Concrete Syntax Tree (CST) to represent the input source
file. The primary purpose of this data structure is:
- faithfully represent the entire input source file, even when it contains
  incomplete constructs or extra tokens
- memory dense for better cache performance
- nodes should be created such that the final tree is stored as close to pre-order
  traversal as possible without compromising the parser's top-down, constant
  lookahead (e.g. parsing post-fix operator expressions such as `(3 + x).b` cannot easily have its nodes generated in pre-order without an uncapped lookahead)
- all relevant semantic information should always be inferable from the tree
  **without having to** look at the associated tokens with the exception of
  atoms (literals, identifiers), this includes keywords that modify the semantic
  meaning of constructs e.g. `inline`, `mut`, `comptime`

To achieve this children are stored as a linked list, with siblings holding
indices to their next sibling and to their first child.

**Defining New Syntax Constructors**

When defining parsers & node kinds for new syntax constructs the child count of a node should only
vary for **one** reason, this ensures that variations and details of nodes can easily be retrieved
with intricate introspection of children.
- ❌ Bad: `If`-node with variable number of `ElseIfBranch` nodes **and** an
  optional else `Block` (`If` could have 3 child nodes for several reasons)
- ✅ Good: `If`-node with guaranteed `ElseIfBranchList` child node but
  optional else `Block` (`If` child count only varies for a single reason)

Existing examples in codebase:
- `ConstDecl` vs `TypedConstDecl` (with/without type annotation)
- `Block` vs `ComptimeBlock` (runtime vs compile-time)

## Robust Expected Token Set Tracking

Use `check` + `emit_unexpected` instead of `emit_missing_token`. Each `check` call that fails adds to the expected token set, so chained checks automatically produce descriptive errors.

**Anti-pattern:**
```rust
if let Some(name) = self.parse_ident() {
    // use name
} else {
    self.diagnostics.emit_missing_token(Token::Identifier, span);
}
```

This only reports "missing Identifier"—no context about what was found.

**Correct pattern:** Chain `check` calls to build the expected set:
```rust
if self.check(Token::Colon) {
    // parse type annotation...
} else if self.check(Token::Equals) {
    // parse value...
} else {
    self.emit_unexpected();  // "found `run`, expected `:` or `=`"
}
```

For `const x run`, this produces "unexpected `run`, expected `:` or `=`" because both `check` calls added to the expected set before `emit_unexpected` was called.

Use `expect` if the token is required.

## Parser Method Reference

**Token Checking & Consumption:**

| Method | Consumes? | Side Effects | Use When |
|--------|-----------|--------------|----------|
| `at(Token)` | No | None | Raw check, no trivia skip |
| `check(Token)` | No | Skips trivia, adds to expected set | Testing if token present before committing |
| `eat(Token)` | If matches | Skips trivia, adds to expected set | Optional tokens |
| `expect(Token)` | If matches | Skips trivia, emits error if no match | Required tokens |

**Node Construction Pattern:**

```rust
// 1. Record start position
let start = self.current_token_idx;

// 2. Consume tokens that begin the construct
self.expect(Token::While);

// 3. Allocate node (uses start position)
let mut node = self.alloc_node_from(start, NodeKind::WhileStmt);

// 4. Parse and attach children
let condition = self.parse_expr(ParseExprMode::CondExpr);
self.push_child(&mut node, condition);

let body = self.parse_block(self.current_token_idx, NodeKind::Block);
self.push_child(&mut node, body);

// 5. Close node (sets end token position)
self.close_node(node)
```

**Statement Results:**

`try_parse_stmt` returns `Option<StmtResult>`:

| Variant | Meaning | Example |
|---------|---------|---------|
| `Statement(node)` | Complete statement, consumed semicolon | `x = 1;` |
| `MaybeEndExpr(node)` | No semicolon, could be end expr or statement | `{ }`, `if x { } else { }`, `while x { }` |
| `ForcedEndExpr(node)` | Must be end expr (requires semi if used as stmt) | `x + y` without `;` |

**Expression Modes:**

| Mode | Use Case |
|------|----------|
| `AllowAll` | General expression context |
| `CondExpr` | Condition in `if`/`while` (prevents block ambiguity) |
| `TypeExpr` | Type annotation context |
