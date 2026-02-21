---
name: parser-engineer
description: Mandatory use when developing or analyzing the parser, CST, lexer, or AST. Use when adding new syntax constructs, fixing parse errors, improving error recovery, or debugging tokenization issues.
---

# Parser Engineer

## Overview

LSP-grade error-resilient parser for the Sensei language. Core principle: **faithfully represent ALL input, including malformed code, while maximizing recovered syntactic structure.**

**Crate:** `frontend/parser` (`sensei-parser`)
**Grammar Reference:** `docs/Grammar.md` — always consult before implementing new parsing rules.
**Cross-reference:** When modifying CST node definitions, also use the `data-structure` skill.

## File Structure

```
frontend/parser/src/
├── lib.rs              # Crate root, re-exports
├── lexer.rs            # Token definitions (logos) and Lexer
├── parser.rs           # Main parser implementation
├── ast.rs              # AST definitions
├── cst/
│   ├── mod.rs          # Node, NodeKind, NodeIdx, TokenIdx
│   └── display.rs      # Pretty-printing for tests/debugging
├── diagnostics.rs      # DiagnosticsContext trait
├── error_report.rs     # Error formatting, LineIndex
└── tests/
    ├── mod.rs          # Test utilities
    ├── errorless.rs    # Happy-path tests
    └── resiliency.rs   # Error recovery tests
```

## Key Principles

### Never Crash on Errors

The parser must consume all input regardless of how malformed. When encountering unexpected tokens:
1. Wrap them in error nodes
2. Emit a diagnostic
3. Continue parsing

Never panic, return early, or leave tokens unconsumed.

### Guards Before Parsing

Check for expected tokens before calling sub-parsers:
```rust
if self.at(Token::LeftParen) {
    self.parse_param_list();
}
```
This prevents cascading errors from entering parsers in broken states.

### Avoid Recursion

Model syntactic constructs as variable-length lists rather than recursive calls. Recursion consumes stack and artificially limits nesting depth.

### Single-Reason Child Count Variance

A node's child count should only vary for **one** reason, enabling easy introspection:

- ❌ Bad: `If` with variable `ElseIfBranch` count AND optional else `Block`
- ✅ Good: `If` with guaranteed `ElseIfBranchList` and optional else `Block`

Examples: `ConstDecl` vs `TypedConstDecl`, `Block` vs `ComptimeBlock`

## CST Representation

Homogeneous tree storing the entire input faithfully. Children are linked lists (indices to next sibling and first child).

**Requirements:**
- Represent incomplete constructs and extra tokens
- Semantic info inferable from tree structure alone (no token inspection needed except for atoms)
- Keywords modifying semantics (`inline`, `mut`, `comptime`) must be reflected in node structure

**Memory layout:** Nodes stored in pre-order in the arena for cache performance. Post-fix operators may require allocating parents after children.

## Parser Method Reference

| Method | Consumes? | Side Effects | Use When |
|--------|-----------|--------------|----------|
| `at(Token)` | No | None | Raw check, no trivia skip |
| `check(Token)` | No | Skips trivia, adds to expected set | Testing before committing |
| `eat(Token)` | If matches | Skips trivia, adds to expected set | Optional tokens |
| `expect(Token)` | If matches | Skips trivia, emits error if no match | Required tokens |

### Node Construction Pattern

```rust
let start = self.current_token_idx;           // 1. Record start
self.expect(Token::While);                    // 2. Consume opening tokens
let mut node = self.alloc_node_from(start, NodeKind::WhileStmt);  // 3. Allocate

let condition = self.parse_expr(ParseExprMode::CondExpr);         // 4. Parse children
self.push_child(&mut node, condition);
let body = self.parse_block(self.current_token_idx, NodeKind::Block);
self.push_child(&mut node, body);

self.close_node(node)                         // 5. Close (sets end position)
```

### Expected Token Set Tracking

Use `check` chains + `emit_unexpected` instead of `emit_missing_token`:

```rust
// ❌ Anti-pattern: only reports "missing Identifier"
if let Some(name) = self.parse_ident() { ... }
else { self.diagnostics.emit_missing_token(Token::Identifier, span); }

// ✅ Correct: "unexpected `run`, expected `:` or `=`"
if self.check(Token::Colon) { ... }
else if self.check(Token::Equals) { ... }
else { self.emit_unexpected(); }
```

Each `check` call adds to the expected set, producing descriptive errors.

### Statement Results

`try_parse_stmt` returns `Option<StmtResult>`:

| Variant | Meaning | Example |
|---------|---------|---------|
| `Statement(node)` | Complete, consumed semicolon | `x = 1;` |
| `MaybeEndExpr(node)` | No semicolon, could be end expr | `{ }`, `if x { } else { }` |
| `ForcedEndExpr(node)` | Must be end expr (needs semi if stmt) | `x + y` without `;` |

### Expression Modes

| Mode | Use Case |
|------|----------|
| `AllowAll` | General expression context |
| `CondExpr` | Condition in `if`/`while` (prevents block ambiguity) |
| `TypeExpr` | Type annotation context |

## Testing Conventions

Use test utilities in `frontend/parser/src/tests/`:

**Snapshot tests:**
```rust
#[test]
fn test_while_basic() {
    assert_parses_to_cst_no_errors_dedented(
        "init { while x { y; } }",
        r#"
        File
            InitBlock
                "init"
                " "
                ...
        "#,
    );
}
```

- Node kinds: `WhileStmt`, `BinaryExpr(Plus)`
- Tokens: quoted strings (`"while"`, `" "`)
- Children indented under parents

**Error tests:**
```rust
assert_parser_errors("const x = init { }", &["error: unexpected `init`..."]);
```

## Common Mistakes

| Mistake | Fix |
|---------|-----|
| Using `emit_missing_token` directly | Use `check` chains + `emit_unexpected` |
| Recursive parsing for variable-length constructs | Use iterative loops |
| Variable child count for multiple reasons | Split node kinds or use list wrappers |
| Not wrapping unexpected tokens in error nodes | Always consume all input |
| Inspecting tokens to determine semantics | Reflect meaning in node structure |
