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
[function application] (e1 e2 ... e<N>) =>  (((e1 e2) e3) ...) e<N>
    - also: (apply e1 e2 ... e<N>) for explicit form
[function definition] (funcdef comptime? <bind:name> <type:expr> <body:expr>)
[recursive function definition] (recfuncdef <funcref:name> comptime? <bind:name> <type:expr> <body:expr>)
[if-else] (if <condition:expr> <true_branch:expr> <false_branch:expr>)
[block] (block (comptime? <let_bind:name> <assigned:expr>)* <block_final_result:expr>)
[member-access] (attr <path_segment:name>* <struct_expr:expr>) =>
    ((struct_expr.segment[0]).segment[1]) ... .segment[n]
[struct definition] (struct_def
    (fields (<field_name:name> <type:expr>)*)
    (defs <def_node:sexpr_node>*)
)
[struct init] (struct_init <struct_type:expr> (<field:name> <value:expr>)*)
```

Note: Builtins are not part of the AST syntax. They are injected at evaluation time.
