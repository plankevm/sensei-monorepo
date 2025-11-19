# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Neosen is a compiler frontend for the Sensei programming language. The project is in early development, currently implementing the lexer and parser stages. Sensei is a language focused on arithmetic safety with explicit overflow/underflow handling (e.g., `+` for checked addition, `+%` for wrapping addition).

## Building and Testing

```bash
# Check all crates for compilation errors
cargo check

# Run all tests
cargo test ```

## Workspace Structure

This is a Cargo workspace with crates in `crates/`:

- **neosen-data**: Core data structures (`X32<M>` type-safe indices, `Span<T>` ranges)
- **neosen-parser**: Lexer, parser, and AST definitions
  - `lexer.rs`: Token lexer using the `logos` crate
  - `ast.rs`: AST node definitions

## Architecture

### Memory Management Strategy

The parser uses **arena allocation** (bumpalo) for all AST nodes:
- AST nodes are allocated in a bump arena that outlives the parser
- `AstBox<'ast, T>` is a type alias for `&'ast mut T`
- The `parse()` function leaks the arena using `Box::leak()` to return AST with `'static` lifetime
- Use `Vec::leak()` or `arena.alloc()` to allocate slices/values in the arena
- String interning uses the same arena for memory efficiency

### AST Design

- All AST structs have **public fields** to allow easy construction and access
- `Spanned<T>` wraps values with source location (`Span<u32>`)
- The AST is designed for minimal size (see size assertions in ast.rs:168-179)
- `X32<M>` provides type-safe 32-bit indices with phantom markers to prevent mixing different index types

### Parser Implementation

The parser is a **recursive descent parser** that:
- Panics on the first parse error (no error recovery)
- Uses precedence climbing for binary expressions (ast.rs:228-246 defines operators)
- Properly handles postfix operators (member access `.`, function calls `()`)
- Distinguishes trailing expressions from statement expressions in blocks

Key parsing patterns:
- All parsing methods return `Spanned<T>` to track source locations
- Use `self.spanned(span_usize, inner)` to wrap values with spans
- Convert `Span<u32>` from AST back to `Span<usize>` when needed for internal operations
- The lexer is wrapped with `peek()` and `next()` methods for lookahead

## Examples

Test cases use examples in `examples/`:
- `basic-001.sen`: Basic syntax demo with const definitions, init/run blocks

When writing parser code, test against these examples to ensure compatibility.

## Lexer Token Types

See `lexer.rs:10-118` for the complete token set. The lexer:
- Uses logos for fast token matching
- Handles line comments (`//`) and nested multiline comments (`/* */`)
- Has diagnostic tokens for common errors (e.g., `ErrorBadNumericLiteral`)
- Returns token type + span for each token
