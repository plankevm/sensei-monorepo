# Sensei Grammar

```ebnf
program = decl*
decl = init | run | const_def

init = "init" block
run = "run" block
const_def = "const" IDENT (":" expr)? "=" expr ";"

# Expressions
expr = "comptime"? block | if_expr | expr_no_block
expr_no_block =
    IDENT | literal | member
    | fn_call | fn_def | struct_def | struct_lit
    | binary | unary | paren
binary = expr binary_op expr
unary = unary_op expr
paren = "(" expr ")"
fn_call = expr "(" comma_separated{expr}? ")"
member = expr "." IDENT

binary_op = "or" | "and"
          | "==" | "!=" | "<" | ">" | "<=" | ">="
          | "|" | "^" | "&" | "<<" | ">>"
          | "+" | "-" | "+%" | "-%"
          | "*" | "/" | "%" | "*%" | "/+" | "/-" | "/<" | "/>"
unary_op = "-" | "!" | "~"

if_expr = "if" expr block ("else" "if" expr block)* ("else" block)?

block = "{" stmt* expr? "}"

# Statements
stmt =
    (expr_no_block | return | assign | let) ";"
    | if_expr ";"?
    | while

while = "inline"? "while" expr block
let = "let" "mut"? IDENT (":" expr)? "=" expr
return = "return" expr
assign = expr "=" expr

# Definitions
fn_def = "fn" "(" param_def_list? ")" expr block
param_def_list = comma_separated{"comptime"? IDENT ":" expr}

struct_def = "struct" "{" comma_separated{IDENT ":" expr}? "}"
struct_lit = expr "{" comma_separated{IDENT ":" expr}? "}"

# Literals
literal = bool_literal | hex_literal | bin_literal | dec_literal
bool_literal = "true" | "false"
hex_literal = /-?0x[0-9A-Fa-f][0-9A-Fa-f_]*/
bin_literal = /-?0b[01][01_]*/
dec_literal = /-?[0-9][0-9_]*/

# Helpers
comma_separated{p} = (p ("," p)* ","?)
line_comment = /\/\/[^\n]*/
```
