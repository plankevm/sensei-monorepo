/**
 * @file A tree-sitter parser for sensei
 * @author Philogy <philogy@senseilang.org>
 * @license MIT
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

const PREC_MUL = 10
const PREC_ADDITIVE = 9
const PREC_COMPARATIVE = 3

module.exports = grammar({
  name: "sensei",

  extras: ($) => [/\s/, $.line_comment],
  conflicts: ($) => [
    [$._expr_no_block, $.name_path],
    [$._expr, $._stmt]
  ],

  rules: {
    source_file: ($) => repeat(choice(
      $.init,
      $.run,
      $._const_def
    )),

    init: ($) => seq("init", $.block),
    run: $ => seq("run", $.block),
    _const_def: $ => seq($.const_item, ";"),

    const_item: $ => seq(
      "const",
      $.identifier,
      optional(seq(":", $.type_expr)),
      "=",
      $._expr
    ),

    block: $ => seq("{", field("stmts", repeat($._stmt)), field("last_expr", optional($._expr)), "}"),
    type_expr: $ => choice($.name_path, $.type_def),
    _expr: $ => choice($.block, $._expr_no_block),
    _expr_no_block: $ => choice(
      $.fn_call,
      $.binary_expr,
      $._paren_expr,
      $.member,
      $.type_def,
      $._literal,
      $.identifier,
      $.struct_lit
    ),
    fn_call: $ => seq(
      field("fn", $._expr),
      "(",
      field("params", commaSeparated($._expr)),
      ")"
    ),
    binary_expr: $ => {
      /**
       * @param {number} precedence
       * @param {string[]} operators
       */
      const bin_op_variant = (precedence, operators) => prec.left(precedence, seq(
        field("lhs", $._expr),
        field("op", choice(...operators)),
        field("rhs", $._expr)
      ));

      return choice(
        bin_op_variant(PREC_MUL, ["*", "*%", "/-", "/+", "/^", "/$", "%"]),
        bin_op_variant(PREC_ADDITIVE, ["+", "+%", "-", "-%"]),
        bin_op_variant(PREC_COMPARATIVE, ["==", "<", "<=", "!=", ">", ">="])
      )
    },
    _paren_expr: $ => seq("(", $._expr, ")"),
    member: $ => seq($._expr, ".", $.identifier),
    _stmt: $ => choice(seq(choice($.const_item, $._expr_no_block, $.return, $.assign, $.let), ";"), seq($.block, optional(";"))),
    return: $ => seq("return", $._expr),
    let: $ => seq("let", optional("mut"), $.identifier, "=", $._expr),
    assign: $ => seq($.name_path, "=", $._expr),
    cond_stmt: $ => seq(
      "if",
      $._expr,
      $.block,
      repeat(seq("else", "if", $._expr, $.block)),
      optional(seq("else", $.block))
    ),
    struct_lit: $ => seq($.name_path, "{", commaSeparated($.struct_lit_field), "}"),
    struct_lit_field: $ => seq($.identifier, ":", $._expr),

    type_def: $ => choice($.fn_def, $.struct_def),
    fn_def: $ => seq("fn", "(", commaSeparated($.typed_item_def), ")", $.type_expr, $.block),
    struct_def: $ => seq("struct", "{", commaSeparated($.typed_item_def), "}"),
    typed_item_def: $ => seq($.identifier, ":", $.type_expr),

    _literal: $ => choice($.bool_literal, $.hex_literal, $.bin_literal, $.dec_literal),
    bool_literal: (_) => choice("true", "false"),
    hex_literal: (_) => /0x[0-9A-Fa-f][0-9A-Fa-f_]*/,
    bin_literal: (_) => /0b[01][01_]*/,
    dec_literal: (_) => /[0-9][0-9_]*/,

    name_path: $ => seq($.identifier, repeat(seq(".", $.identifier))),
    line_comment: (_) => /\/\/[^\n]*/,
    identifier: (_) => /[a-zA-Z_][a-zA-Z0-9_]*/,
  },
});


/**
 * Creates a rule that matches a comma separated list of the input rule, allowing a trailing comma.
 * Matches at least one.
 *
 * @param {RuleOrLiteral} rule
 *
 * @returns {ChoiceRule}
 */
function commaSeparated(rule) {
  return optional(seq(rule, repeat(seq(",", rule)), optional(",")));
}
