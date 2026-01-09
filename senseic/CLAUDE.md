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

- **Docs** (`docs`): Documentation (Never commit temporary files related to
  project management or tasks, any documentation outside of `docs` is usually
  temporary stuff)
- **neosen-data** (`crates/data`): Core data structures (`X32<M>` type-safe indices, `Span<T>` ranges)
- **neosen-parser** (`crates/parser`): Lexer, parser, and AST definitions
  - `lexer.rs`: Token lexer using the `logos` crate
  - `ast.rs`: AST node definitions


## Coding Style

- Comments are code that is never tested. Avoid unless necessary to explain
  intricate code.

