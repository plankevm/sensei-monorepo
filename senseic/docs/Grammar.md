# Sensei Grammar

```ebnf
program = decl*
decl = init | run | const_def | import

import = "import" (import_all | import_select) "from" STRING ";"
import_all = "*" ("as" IDENT)?
import_select = "{" import_selection+ "}"
import_selection = IDENT ("as" IDENT)?

init = "init" block
run = "run" block

const_def = "export"? const_item ";"
const_item = "const" IDENT (":" type_expr)? "=" expr

expr = block | expr_no_block
expr_no_block =
    fn_call | binary_expr | paren_expr | member | type_def
    | literal | IDENT | struct_lit

type_expr = name_path | struct_def
type_def = fn_def | struct_def

block = "{" stmt* expr? "}"
binary_expr = expr bin_op expr
paren_expr = "(" expr ")"
fn_call = expr "(" comma_separated{expr}? ")"
member = expr "." IDENT

literal = bool_literal | hex_literal | bin_literal | dec_literal
bool_literal = "true" | "false"
hex_literal = /-?0x[0-9A-Fa-f][0-9A-Fa-f_]*/
bin_literal = /-?0b[01][01_]*/
dec_literal = /-?[0-9][0-9_]*/

cond_stmt = "if" expr block ("else" "if" expr block)* ("else" block)?

stmt =
    (const_item | expr_no_block | return | assign | let) ";"
    | block ";"?
    | cond_stmt

let = "let" "mut"? IDENT (":" type_expr)? "=" expr
return = "return" expr
assign = name_path "=" expr

fn_def = "fn" "(" param_def_list? ")" ("->" type_expr)? block
param_def_list = comma_separated{IDENT ":" type_expr}

struct_def = "struct" "{" comma_separated{IDENT ":" type_expr}? "}"
struct_lit = name_path "{" comma_separated{IDENT ":" expr} "}"

comma_separated{p} = (p ("," p)* ","?)
name_path = IDENT ("." IDENT)*
line_comment = /\/\/[^\n]*/
```
