# Instructions for AI Agents Working This Repository

## Project Overview

This project defines the Sensei intermediate representation (SIR) for compilers looking to target the EVM. It defines the IR itself, useful analysis functions, optimizations passes as well as backends to target different EVM versions. The repository is in an early stage of development.

## Design Philosophy

**This is a bespoke EVM IR, not a Solidity IR.** Design for efficiency & simplicity. Only model what the EVM specification requires. External interfaces (Solidity ABI, etc.) are implemented in user space by emitting IR, not baked into the IR itself.

## Development Commands

### When Iterating/Working on a specific part of the code
To improve the feedback loop you can narrow down what tests to run if you're fixing a bug in a
specific component:
- `cargo test -p <crate-name>`: Only run tests of a specific crate
- `forge test --ffi` (ran from within `sir-solidity-diff-tests/`): To just run the diff tests, can
  narrow down further with `--mc <contract name>` or `--mt <test name>`

## Coding Style
### Code Cleanliness
- Avoid comments, except when necessary to explain terse code
- Descriptive function & variable names should explain the code

### Type Driven Development
- leverage Rust enums & matches to avoid redundant control flow and nonsensical states
- leverage the "new type" pattern to create more specific versions of less-specific types (for indices/dense IDs use `crates/data/index.rs`)
- avoid converting from untyped indices to typed indices unless necessary, use typed ranges & slices
  where relevant
- avoid using `&IndexSlice` as indices are often used as keys and sub-slices will always start at `0`, instead pass `&IndexVec` or a normal slice if sub-slices are expected

### Security-Centric Development
- if a bug in a given component could result in a miscompilation or other critical flaw it's considered **security critical**
- attempt to minimize **security critical** code
- separate **security critical** and noncritical code to minimize the lines of code external auditors need to verify
- prioritize readability & maintainability over compile-time efficiency, but avoid obviously inefficient runtime patterns (unnecessary clones, temporary allocations)
- sprinkle assertions to verify assumptions in data, better to crash at compile-time than to
  miscompile

### Idiomatic Rust Performance
Apply these patterns by default—they're both more idiomatic *and* faster:
- Pass `&T` or `&[T]` instead of cloning when ownership transfer isn't needed
- Accept `&[T]` instead of `&Vec<T>` in function parameters
- Use iterator chains instead of intermediate `Vec`s (`.map().filter()` not `.collect()` then iterate)
- Only `.clone()` when necessary: true ownership transfer, persistence across scopes, Arc/Rc sharing
- **Avoid**: premature optimization with complex lifetimes, unsafe blocks, or manual memory management without clear, documented justification

### Data Oriented Design
When designing new components, think about data layout upfront:
- Consider access patterns: will this be iterated, randomly accessed, frequently cloned?
- Prefer contiguous, dense representations where appropriate (Vec-based indices vs HashMap)
- Design types that compose well (small, copyable IDs; separate maps for properties)
- *For hot paths*: optimize for cache efficiency (struct-of-arrays, alignment, locality)

### Refactors and Delusions
- If something is no longer needed or unused don't simply underscore it or commented out, delete it unless truly required by an external api or user facing api that would cause breaking changes

## Workspace Structure
- **`/crates`**: Collection of Rust crates that make up SIR
  - **`data`** (`sir-data`): Core IR types and foundational utilities
  - **`analyses`** (`sir-analyses`): Analysis passes built on top of the IR
  - **`parser`** (`sir-parser`): Front-end for parsing source into the IR
  - **`debug-backend`** (`sir-debug-backend`): Minimal SIR->EVM backend focused on simplicity
  - **`assembler`** (`sir-assembler`): Converts assembly to bytecode
  - **`cli`** (`sir-cli`): CLI tool for SIR
  - **`optimizations`** (`sir-optimizations`): Optimization passes
- **`/test-utils`**: Shared helpers and fixtures for integration tests
- **`/docs`**: Reference material for opcodes, forks, and other EVM context

## Documentation
### EVM Reference
- [`docs/evm_opcodes_and_precompiles.md`](docs/evm_opcodes_and_precompiles.md)
    When working on tasks that require EVM knowledge, make sure to pull this doc file into your
    context so you understand the EVM.
- [`docs/opcode_fork_mapping.md`](docs/opcode_fork_mapping.md)

### IR
- [`docs/ir_text_format.md`](docs/ir_text_format.md)
    Complete specification of the SIR text format including EBNF grammar, operation mnemonics,
    parser usage, and examples. Reference this when working with the parser or writing/reading IR text.
