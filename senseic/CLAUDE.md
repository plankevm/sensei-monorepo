## Project Overview

Neosen is a compiler frontend for the Sensei programming language.

## Commands

```bash
cargo test -p <crate name> # Run during work on a specific crate for validation
cargo test # Run all tests at end of task

# Run formatter & linter at the end of a task
cargo +nightly fmt --all
cargo +nightly clippy --workspace --all --all-features --locked -- -D warnings
```

## Workspace Structure

Cargo workspace with crates in `crates/`:

- **Docs** (`docs`): Documentation
- **neosen-data** (`crates/data`):
    - `index.rs`: `X32` easily new-typed index 
    - `span.rs`: Range-like start, end with a more convenient API
    - `bigint.rs`: Arena allocated big int with parsing helpers
- **neosen-parser** (`crates/parser`):
  - `lexer.rs`: Token lexer using the `logos` crate
  - `cst.rs`: Homogeneous syntax tree that stores well-formed nodes & errors
  - `parser.rs`: LSP-grade error resilient parser


## Coding Style

**DRY Principle:** If you find yourself writing the same pattern 2-3 times, 
extract it into a helper method. Common cases:
- Checking multiple tokens with a semantic expected value → add a helper like 
`check_with(tok, expected)` or `expect_any(toks, expected)`
- Repeated error recovery sequences → add a recovery helper

**Comments:** Do NOT add inline comments that describe what the code does 
(e.g., "// Parse next element"). The code should be self-documenting. 
Only add comments for non-obvious *why* decisions.


**Type Driven Development:** Use types to define & rule out certain kinds of
errors.
