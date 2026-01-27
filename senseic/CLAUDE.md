## Project Overview

Neosen is a compiler frontend for the Sensei programming language.

## Commands

```bash
cargo test -p <crate name> # Run during work on a specific crate for validation
./run-all-tests.sh # Run all tests at end of task

# Run formatter & linter at the end of a task
cargo +nightly fmt --all
cargo +nightly clippy --workspace --all --all-features --locked -- -D warnings
```

## Workspace Structure

Cargo workspace with general-purpose crates in `crates/` and frontend crates in `frontend/`:

- **Docs** (`docs`): Documentation
- **sensei-core** (`crates/sensei-core`):
    - `index.rs`: `X32` easily new-typed index 
    - `span.rs`: Range-like start, end with a more convenient API
    - `bigint.rs`: Arena allocated big int with parsing helpers
- **neosen-parser** (`frontend/parser`):
  - `lexer.rs`: Token lexer using the `logos` crate
  - `cst.rs`: Homogeneous syntax tree that stores well-formed nodes & errors
  - `parser.rs`: LSP-grade error resilient parser


## Coding Style

### Comments
Do NOT add inline comments that describe what the code does 
(e.g., "// Parse next element"). The code should be self-documenting. 
Only add comments for non-obvious *why* decisions.

### Type Driven Development
- Always prefer a compile-time, type-level check over a runtime check
- Liberally use panic-triggering asserts (`assert!`, `assert_eq!`, `.unwrap()`,
  `.expect(comment on what this assert is check)`) but only for invariants &
  assumptions that **CANNOT BE ENFORCED VIA THE TYPE SYSTEM**
