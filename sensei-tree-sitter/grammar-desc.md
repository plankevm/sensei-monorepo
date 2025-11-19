# Sensei Grammar

```ebnf
program = decl*
decl = init | run | const_def ";"
init = "init" block
run = "run" block

const_def = const IDENT (":" type_expr)? "=" expr
expr =
    type_expr | block | binary_op_expr | paren_expr | literal
    | IDENT | expr "." IDENT | fn_call | if

type_expr = name_path | fn_def | struct_def
block = "{" stmt* expr? "}"
binary_op_expr = expr bin_op expr
paren_expr = "(" expr ")"
literal = NUM_LITERAL | "true" | "false" | struct_literal
fn_call = expr "(" comma_separated{expr}? ")"

if = "if" expr block ("else" "if" expr block)* ("else" block)?

stmt = (let | expr | return | const_def | assign) ";"
let = "let" "mut"? IDENT "=" expr
return = "return" expr
assign = name_path assign_op expr

fn_def = "fn" "(" param_def_list? ")" ("->" type_expr) block
param_def_list = comma_separated {IDENT ":" type_expr}

struct_def = "struct" "{" comma_separated{IDENT ":" type_expr}? "}"
struct_literal = name_path "{" comma_separated{IDENT ":" expr} "}"

comma_separated {p} -> (p ("," p)* ","?)
name_path = IDENT ("." IDENT)*
```
