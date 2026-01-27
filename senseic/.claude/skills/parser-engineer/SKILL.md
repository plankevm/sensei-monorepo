---
name: parser-engineer
description: Mandatory use when developing or analyzing the parser or other tightly coupled data structures such as the CST & lexer.
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
self.clear_expected();
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
