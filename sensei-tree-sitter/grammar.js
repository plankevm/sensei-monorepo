/**
 * @file A tree-sitter parser for sensei
 * @author Philogy <philogy@senseilang.org>
 * @license MIT
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

const PREC = {
  OR: 1,
  AND: 2,
  COMPARE: 3,
  BIT_OR: 4,
  BIT_XOR: 5,
  BIT_AND: 6,
  SHIFT: 7,
  ADDITIVE: 8,
  MULTIPLICATIVE: 9,
  UNARY: 10,
}

module.exports = grammar({
  name: "sensei",

  extras: ($) => [/\s/, $.line_comment],
  conflicts: ($) => [
    [$._expr, $._stmt],
    [$.block, $.struct_lit],
    [$.struct_def, $.struct_lit],
    [$.field_def, $.field_init],
  ],

  rules: {
    source_file: ($) => repeat($._decl),

    _decl: ($) => choice($.init, $.run, $.const_def),

    init: ($) => seq("init", $.block),
    run: ($) => seq("run", $.block),
    const_def: ($) => seq("const", $.identifier, optional(seq(":", $._expr)), "=", $._expr, ";"),

    // Expressions
    _expr: ($) => choice($.comptime_block, $.block, $.if_expr, $._expr_no_block),
    comptime_block: ($) => seq("comptime", $.block),
    _expr_no_block: ($) => choice(
      $.identifier,
      $._literal,
      $.member,
      $.fn_call,
      $.fn_def,
      $.struct_def,
      $.struct_lit,
      $.binary_expr,
      $.unary_expr,
      $.paren_expr
    ),

    binary_expr: ($) => {
      /**
       * @param {number} precedence
       * @param {string[]} operators
       */
      const bin_op_variant = (precedence, operators) => prec.left(precedence, seq(
        field("lhs", $._expr),
        field("op", operators.length === 1 ? operators[0] : choice(...operators)),
        field("rhs", $._expr)
      ));

      return choice(
        bin_op_variant(PREC.OR, ["or"]),
        bin_op_variant(PREC.AND, ["and"]),
        bin_op_variant(PREC.COMPARE, ["==", "!=", "<", ">", "<=", ">="]),
        bin_op_variant(PREC.BIT_OR, ["|"]),
        bin_op_variant(PREC.BIT_XOR, ["^"]),
        bin_op_variant(PREC.BIT_AND, ["&"]),
        bin_op_variant(PREC.SHIFT, ["<<", ">>"]),
        bin_op_variant(PREC.ADDITIVE, ["+", "-", "+%", "-%"]),
        bin_op_variant(PREC.MULTIPLICATIVE, ["*", "/", "%", "*%", "/+", "/-", "/<", "/>"]),
      )
    },

    unary_expr: ($) => prec(PREC.UNARY, seq(
      field("op", choice("-", "!", "~")),
      field("operand", $._expr)
    )),

    paren_expr: ($) => seq("(", $._expr, ")"),
    fn_call: ($) => seq(field("fn", $._expr), "(", commaSeparated($._expr, "args"), ")"),
    member: ($) => seq($._expr, ".", $.identifier),

    if_expr: ($) => seq(
      "if",
      field("condition", $._expr),
      field("then", $.block),
      repeat(seq("else", "if", field("condition", $._expr), field("then", $.block))),
      optional(seq("else", field("else", $.block)))
    ),

    block: ($) => seq("{", field("stmts", repeat($._stmt)), field("last_expr", optional($._expr)), "}"),

    // Statements
    _stmt: ($) => choice(
      seq(choice($._expr_no_block, $.return, $.assign, $.let), ";"),
      seq($.if_expr, optional(";")),
      $.while
    ),

    while: ($) => seq(optional("inline"), "while", field("condition", $._expr), field("body", $.block)),
    let: ($) => seq("let", optional("mut"), $.identifier, optional(seq(":", $._expr)), "=", $._expr),
    return: ($) => seq("return", $._expr),
    assign: ($) => seq($._expr, "=", $._expr),

    // Definitions
    fn_def: ($) => seq(
      "fn",
      "(",
      commaSeparated($.param_def, "params"),
      ")",
      field("return_type", $._expr),
      field("body", $.block)
    ),
    param_def: ($) => seq(
      optional("comptime"),
      field("name", $.identifier),
      ":",
      field("type", $._expr)
    ),

    struct_def: ($) => seq("struct", field("size", $._expr), "{", commaSeparated($.field_def, "fields"), "}"),
    field_def: ($) => seq(field("name", $.identifier), ":", field("type", $._expr)),

    struct_lit: ($) => seq(field("type", $._expr), "{", commaSeparated($.field_init, "fields"), "}"),
    field_init: ($) => seq(field("name", $.identifier), ":", field("value", $._expr)),

    // Literals
    _literal: ($) => choice($.bool_literal, $.hex_literal, $.bin_literal, $.dec_literal),
    bool_literal: (_) => choice("true", "false"),
    hex_literal: (_) => /-?0x[0-9A-Fa-f][0-9A-Fa-f_]*/,
    bin_literal: (_) => /-?0b[01][01_]*/,
    dec_literal: (_) => /-?[0-9][0-9_]*/,

    // Helpers
    line_comment: (_) => /\/\/[^\n]*/,
    identifier: (_) => /[a-zA-Z_][a-zA-Z0-9_]*/,
  },
});


/**
 * Creates a rule that matches a comma separated list of the input rule, allowing a trailing comma.
 *
 * @param {RuleOrLiteral} rule
 * @param {string | null} fieldName
 *
 * @returns {ChoiceRule}
 */
function commaSeparated(rule, fieldName = null) {
  if (fieldName === null) {
    return optional(seq(rule, repeat(seq(",", rule)), optional(",")));
  } else {
    return optional(seq(field(fieldName, rule), repeat(seq(",", field(fieldName, rule))), optional(",")));
  }
}
