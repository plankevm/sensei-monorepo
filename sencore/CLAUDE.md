# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

```bash
# Build the project
cargo build

# Run the project (parses s-expressions from a file)
cargo run -- <path-to-file>

# Run tests
cargo test

# Run a specific test
cargo test <test_name>

# Check without building
cargo check
```

## Project Overview

Sencore (Sensei-core) is a prototype for the Sensei EVM Smart Contract language implemented in Rust.
It's goals are to validate the initial semantics & functionality as well act as a throwaway
implementation to better understand how to structure the production compiler.

Sensei is to be language with staged computation closely modelling Zig:
- Stage I: side effect free, compile-time execution that behaves almost like a dynamic language,
  able to specialize functions, inspect types and have dynamically typed variables
- Stage II: side effectful runtime to be compiled, for the constructs it shares with Stage I they
  should have identical semantics. However Stage II is strictly statically typed. Anything dynamic
  from `Stage I` must be evaluated away/specialized into concrete functions. Stage II can be modeled
  as an extended simply typed lambda calculus, with side effects (EVM IO) and a memory model
  (allocations, read & write)

## Sencore Architecture

Because Sencore is for prototyping & testing purposes the main goal is the ability to quickly
iterate & have understandable code. Therefore:
- s-expressions are used as the input syntax to simplify parsing
- parser has no error recovery and just stops at the first error
- spans are tracked on all parts of the AST/S-Expression parse tree to be able to at least put a
  helpful location on errors
- For stage 1 the ast will directly be interpreted to create a final "runtime function" term
- `src/lib.rs` contains a definition for what stage 2 might look like
- `src/ast.rs` contains the input AST for stage 1 execution

### Span Tracking

`src/span.rs` provides `Span<T>` for tracking source locations throughout the compilation pipeline. All AST nodes carry spans for error reporting.
