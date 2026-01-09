# Sensei Grammar

```ebnf
program = decl*
decl = init | run | const_def

init = "init" block
run = "run" block
const_def = "const" IDENT (":" expr)? "=" expr ";"

expr = ("comptime" block) | cond_expr | expr_no_block
expr_no_block =
    IDENT | literal | member
    | fn_call | fn_def | struct_def | struct_lit

cond_expr = "if" expr block ("else" "if" expr block)* "else" block


block = "{" stmt* expr? "}"
fn_call = expr "(" comma_separated{expr}? ")"
member = expr "." IDENT

literal = bool_literal | hex_literal | bin_literal | dec_literal
bool_literal = "true" | "false"
hex_literal = /-?0x[0-9A-Fa-f][0-9A-Fa-f_]*/
bin_literal = /-?0b[01][01_]*/
dec_literal = /-?[0-9][0-9_]*/

cond_stmt = "if" expr block ("else" "if" expr block)*

stmt =
    (expr_no_block | return | assign | let) ";"
    | (block | cond_expr) ";"?
    | cond_stmt | while

while = "inline"? "while" expr block
let = "let" "mut"? IDENT (":" expr)? "=" expr
return = "return" expr
assign = name_path "=" expr

fn_def = "fn" "(" param_def_list? ")" ("->" expr)? block
param_def_list = comma_separated{"comptime"? IDENT ":" expr}

struct_def = "struct" "{" comma_separated{IDENT ":" expr}? "}"
struct_lit = name_path "{" comma_separated{IDENT ":" expr}? "}"

comma_separated{p} = (p ("," p)* ","?)
name_path = IDENT ("." IDENT)*
line_comment = /\/\/[^\n]*/
```
