---
name: parser-engineer
description: Resilient Parsing engineering guidelines. Use when working on the parser or tightly coupled data structures such as the CST & lexer.
---

# Resilient Parser Engineering

## Why Resilient Parsing?

Resilient parsing recognizes as much syntactic structure as possible from incomplete or erroneous code. An error in one function shouldn't break parsing of unrelated functions. A missing semicolon should produce one error, not dozens of cascading errors.

## Never Crash on Errors

The parser must consume all input regardless of how malformed it is. When encountering unexpected tokens:
- Wrap them in error nodes
- Emit a diagnostic
- Continue parsing

The parser should never panic, return early, or leave tokens unconsumed due to syntax errors.

## Never Consume Recovery Tokens in the Wrong Context

Recovery tokens signal "stop parsing this construct, let the parent handle it." Consuming them causes cascading errors.

**Anti-pattern:**
```rust
let value = self.parse_expr().unwrap_or_else(|| self.advance_with_error());
```

This blindly consumes any token on parse failure, even recovery tokens like `init`, `}`, or `;`. If the user wrote `const x = \n init { ... }` (missing value and semicolon), `advance_with_error()` eats `init`, then every subsequent token triggers "unexpected" errors.

**Correct approach:** Check recovery tokens before advancing:
```rust
if let Some(expr) = self.parse_expr() {
    expr
} else if self.at_any(RECOVERY_SET) {
    self.emit_error();
    self.synthetic_error_node()  // No advance—let parent handle recovery token
} else {
    self.advance_with_error()  // Only consume non-recovery tokens
}
```

## Recovery Sets

Define recovery sets per context level containing:
- **Follow set**: Tokens that can legally follow this construct
- **Ancestor follow sets**: Tokens that start sibling/parent constructs

When inside a loop, decide between:
- **Skip**: Consume unexpected token, stay in loop (token not in recovery set)
- **Break**: Exit loop, let parent handle (token IS in recovery set)

The key insight: recovery sets form a hierarchy. Top-level parsers should not consume tokens that belong to their siblings or ancestors.

## Every Loop Must Make Progress

Any loop that doesn't consume at least one token per iteration will hang. The fuel mechanism catches this during development—every `peek` decrements fuel, every `advance` restores it. Zero fuel = panic indicating a bug.

Ensure every loop iteration either:
1. Calls a sub-parser that consumes tokens, OR
2. Calls `advance_with_error()` to skip one token, OR
3. Breaks out of the loop

## Guards Before Parsing

Check for expected tokens before calling sub-parsers:
```rust
if self.at(Token::LeftParen) {
    self.parse_param_list();
}
```

This reduces cascading. The missing `(` is reported once, but we don't enter `parse_param_list` in a broken state where it might consume tokens it shouldn't.

## Homogeneous Tree Structure

The CST uses a linked-list tree (`first_child` → `next_sibling` chains) rather than typed AST nodes. This allows:
- Error nodes to appear anywhere as siblings
- No fixed schema—malformed trees are representable
- Valid prefixes are always captured

The parser should produce a useful tree even from broken code, localizing errors to where they occur.
