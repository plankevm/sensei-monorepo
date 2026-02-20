# Frontend Architecture

The architecture for the frontend of the compiler, to be usable for both the
codegeneration CLI and eventually also LSP server.

1. Lexing & Parser: input source files are parsed into CSTs
2. Semantic Analysis (Sema): Performs simultaenous analysis and lowering from
   the CST to untyped HIR with the help of AST wrappers
3. HIR Interpreter: Executes the emitted HIR to resolve compile-time functions,
   generics and type-checks emitting the final pre-MIR instructions.
4. Typecheck & final MIR validation:
    - Typechecking ensures all types are concrete, correct and certain runtime-illegal
    - Validation ensures comptime only structures such as first class
    function invocations are all resolved.
5. MIR => SIR lowering:
    - MIR structs are flattened to locals
    - control flow constructs transformed into BBs & CFGs
    - BB inputs & outputs set for SSA

Once lowered into SIR we've reached the middle-end and are no longer in the
frontend.
