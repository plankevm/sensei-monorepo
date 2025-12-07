# S-Expressions AST Format

This describes how given s-expressions should translate into the Sencore AST.

## Base Expressions
```
() => void constant
34 => number constant
true/false => boolean constant
<name> => variable reference (`Var(name)`)
```

## Compound Expressions

```
[function application] (apply e1 e2 ... e<N>) =>  (((e1 e2) e3) ...) e<N>
[function definition] (func <bind:name> <type:expr> <body:expr>)
[if-else] (if <condition:expr> <true_branch:expr> <false_branch:expr>)
[block] (block (<let_bind:name> <type:expr>? <assigned:expr>)* <block_final_result:expr>)
[member-access] (attr <path_segment:name>* <struct_expr:expr>) =>
    ((struct_expr.segment[0]).segment[1]) ... .segment[n]
[struct definition] (struct_def
    (fields (<field_name:name> <type:expr>)*)
    (defs <def_node:sexpr_node>*)
)
[struct init] (struct_init <struct_type:expr> (<field:name> <value:expr>)*)
[all builtins] (<builtin_name_in_snake_case> <arg1:expr> <arg2:expr> ...)

```
