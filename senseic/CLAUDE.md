## Project Overview

Senseic is a compiler frontend for the Sensei programming language.

## Commands

```bash
cargo test -p <crate name> # Run during work on a specific crate for validation

# Run formatter & linter at the end of a task
just check

# Run all rust tests
just test

# Run all tests (including SIR solidity diff tests)
just test-all
```

## Workspace Structure

Cargo workspace with general-purpose crates in `crates/` and frontend crates in `frontend/`:

- **Docs** (`docs`): Documentation
- **sensei-core** (`crates/sensei-core`): Core utilities
    - `index.rs`: `X32` easily new-typed index
    - `index_vec.rs`: IndexVec collection type
    - `span.rs`: Range-like start, end with a more convenient API
    - `bigint.rs`: Arena allocated big int with parsing helpers
    - `intern.rs`: String interning
    - `dense_index_set.rs`: Dense index set implementation
- **sensei-parser** (`frontend/parser`): LSP-grade error resilient parser
    - `lexer.rs`: Token lexer using the `logos` crate
    - `cst/`: Homogeneous syntax tree that stores well-formed nodes & errors
    - `parser.rs`: Main parser implementation
    - `ast.rs`: AST definitions
    - `diagnostics.rs`: Diagnostic context trait
- **sensei-hir** (`frontend/hir`): High-level IR
- **sensei-cli** (`frontend/cli`): CLI frontend


## Coding Style

### Comments
Do NOT add inline comments that describe *what* the code does
(e.g., "// Parse next element"). The code should be self-documenting.
Only add comments for non-obvious *why* decisions.

### Type Driven Development
- Always prefer a compile-time, type-level check over a runtime check
- Liberally use panic-triggering asserts (`assert!`, `assert_eq!`, `.unwrap()`,
    `.expect(comment on what this assert is check)`) but only for invariants &
    assumptions that **CANNOT BE ENFORCED VIA THE TYPE SYSTEM**
- Always use the most precise type possible, favor the new typed indices,
    IndexVec and RelSlice type variants instead of the general purpose u32/usize,
    Vec & [T] alternatives.

### O(1) Allocation Principle

Where heap allocations cannot be avoided you MUST ENSURE that the algorithms or
functions you write at a high-level only make a constant number of allocations
relative to the input size.

### Warnings

Never add `#[allow(dead_code)]` to supress dead code warnings. For WIP code it
is expected, for code that's actually dead no longer used & will not be used in
future delete.

## Docs (`docs/`)
- `./docs/Grammar.md`: Grammar definition, to be referenced for parser work
- `./docs/Frontend-Architecture.md`: Frontend architecture, read for context on
  intended frontend design and structure.

