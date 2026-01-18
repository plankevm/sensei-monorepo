use crate::{
    cst::{self, *},
    diagnostics::DiagnosticsContext,
    lexer::*,
    parser::token_item_iter::TokenItems,
};
use allocator_api2::vec::Vec;
use bumpalo::Bump;
use neosen_data::Span;

type TokenItem = (Token, TokenIdx, SourceSpan);

// Recovery sets - tokens that signal "stop skipping, parent can handle this"
const BLOCK_RECOVERY: &[Token] = &[Token::RightCurly, Token::Init, Token::Run, Token::Const];
const EXPR_RECOVERY: &[Token] =
    &[Token::Semicolon, Token::RightCurly, Token::Comma, Token::RightRound];
const PARAM_RECOVERY: &[Token] = &[Token::RightRound, Token::ThinArrow, Token::LeftCurly];

// Ensure fields are private letting us more easily enforce the invariant that the iterator either
// consumes fuel or advances.
mod token_item_iter {
    use super::TokenItem;
    use std::iter::Peekable;

    pub(super) struct TokenItems<TokenIter: Iterator<Item = TokenItem>> {
        tokens: Peekable<TokenIter>,
        fuel: u32,
    }

    impl<TokenIter: Iterator<Item = TokenItem>> TokenItems<TokenIter> {
        const DEFAULT_FUEL: u32 = 256;

        pub(crate) fn new(tokens: TokenIter) -> TokenItems<TokenIter> {
            TokenItems { tokens: tokens.peekable(), fuel: Self::DEFAULT_FUEL }
        }

        pub(crate) fn peek(&mut self) -> Option<TokenItem> {
            self.fuel -= 1;
            assert!(self.fuel > 0, "out of fuel");
            self.tokens.peek().copied()
        }

        pub(super) fn next(&mut self) -> Option<TokenItem> {
            self.fuel = Self::DEFAULT_FUEL;
            self.tokens.next()
        }
    }
}

struct Parser<'ast, 'd, TokenIter: Iterator<Item = TokenItem>, D: DiagnosticsContext> {
    nodes: Vec<cst::Node, &'ast Bump>,
    expected: Vec<Token, &'ast Bump>,
    tokens: TokenItems<TokenIter>,
    diagnostics: &'d mut D,
    last_token_idx: TokenIdx,
    last_src_span: SourceSpan,
}

impl<'ast, 'd, TokenIter, D> Parser<'ast, 'd, TokenIter, D>
where
    D: DiagnosticsContext,
    TokenIter: Iterator<Item = TokenItem>,
{
    fn new(
        arena: &'ast Bump,
        tokens: TokenIter,
        estimated_node_count: usize,
        diagnostics: &'d mut D,
    ) -> Self {
        Parser {
            tokens: TokenItems::new(tokens),
            nodes: Vec::with_capacity_in(estimated_node_count, arena),
            expected: Vec::with_capacity_in(8, arena),
            diagnostics,
            last_token_idx: TokenIdx::ZERO,
            last_src_span: Span::new(0, 0),
        }
    }

    fn alloc_node(&mut self, kind: NodeKind) -> NodeIdx {
        let id = NodeIdx::new(self.nodes.len() as u32);
        self.nodes.push(Node {
            kind,
            tokens: Span::new(TokenIdx::ZERO, TokenIdx::ZERO),
            next_sibling: None,
            first_child: None,
        });
        id
    }

    fn current(&mut self) -> Option<TokenItem> {
        self.tokens.peek()
    }

    fn current_token(&mut self) -> Option<Token> {
        self.current().map(|(t, _, _)| t)
    }

    fn current_token_idx(&mut self) -> TokenIdx {
        self.current().map_or(self.last_token_idx, |(_, idx, _)| idx)
    }

    fn current_src_span(&mut self) -> SourceSpan {
        self.current().map_or(self.last_src_span, |(_, _, span)| span)
    }

    fn advance(&mut self) -> TokenItem {
        self.expected.clear();
        let item = self.tokens.next().expect("advancing past EOF");

        let (token, ti, src_span) = item;
        self.last_token_idx = ti;
        self.last_src_span = src_span;
        if token.is_error() {
            self.diagnostics.emit_lexer_error(token, ti, src_span);
        }

        item
    }

    fn at(&mut self, token: Token) -> bool {
        self.current().is_some_and(|(next_token, _, _)| next_token == token)
    }

    fn at_any(&mut self, tokens: &[Token]) -> bool {
        self.current().is_some_and(|(next_token, _, _)| tokens.contains(&next_token))
    }

    fn check(&mut self, token: Token) -> bool {
        if self.at(token) {
            return true;
        }
        if !self.expected.contains(&token) {
            self.expected.push(token);
        }
        false
    }

    fn eat(&mut self, token: Token) -> bool {
        if self.check(token) {
            self.advance();
            return true;
        }
        false
    }

    fn emit_unexpected(&mut self) {
        let found = self.current_token();
        let span = self.current_src_span();
        self.diagnostics.emit_unexpected_token(found, &self.expected, span);
    }

    fn eof(&mut self) -> bool {
        self.current().is_none()
    }

    fn expect(&mut self, token: Token) -> bool {
        if self.eat(token) {
            return true;
        }
        self.emit_unexpected();
        false
    }

    fn expect_ident(&mut self) -> Option<NodeIdx> {
        if self.check(Token::Identifier) {
            self.parse_ident()
        } else {
            self.emit_unexpected();
            None
        }
    }

    fn skip_until(&mut self, stop: &[Token]) {
        while let Some((tok, _, _)) = self.current() {
            if stop.contains(&tok) || tok.is_trivia() {
                break;
            }
            self.advance();
        }
    }

    fn advance_with_error(&mut self) -> NodeIdx {
        let err = self.alloc_node(NodeKind::Error);
        let start = self.current_token_idx();
        self.advance();
        self.finalize_node(err, start);
        err
    }

    fn parse_expr_or_error(&mut self, recovery: &[Token]) -> NodeIdx {
        if let Some(expr) = self.parse_expr() {
            return expr;
        }
        if self.at_any(recovery) {
            let err = self.alloc_node(NodeKind::Error);
            let start = self.current_token_idx();
            self.finalize_node(err, start);
            return err;
        }
        self.advance_with_error()
    }

    fn skip_trivia(&mut self) {
        while let Some(token) = self.current_token()
            && (token.is_trivia() || token.is_error())
        {
            self.advance();
        }
    }

    fn finalize_node(&mut self, node: NodeIdx, start: TokenIdx) {
        let end = TokenIdx::new(self.last_token_idx.get() + 1);
        self.nodes[node.idx()].tokens = Span::new(start, end);
    }

    fn link_child(&mut self, parent: NodeIdx, child: NodeIdx, last: &mut Option<NodeIdx>) {
        if let Some(prev) = last.replace(child) {
            self.nodes[prev.idx()].next_sibling = Some(child);
        } else {
            self.nodes[parent.idx()].first_child = Some(child);
        }
    }

    // ======================== ATOM PARSING ========================

    fn parse_literal(&mut self) -> Option<NodeIdx> {
        let tok = self.current_token()?;
        if !matches!(
            tok,
            Token::DecimalLiteral
                | Token::HexLiteral
                | Token::BinLiteral
                | Token::True
                | Token::False
        ) {
            return None;
        }
        let node = self.alloc_node(NodeKind::Literal);
        let start = self.current_token_idx();
        self.advance();
        self.finalize_node(node, start);
        Some(node)
    }

    fn parse_ident(&mut self) -> Option<NodeIdx> {
        if !self.at(Token::Identifier) {
            return None;
        }
        let node = self.alloc_node(NodeKind::Ident);
        let start = self.current_token_idx();
        self.advance();
        self.finalize_node(node, start);
        Some(node)
    }

    fn parse_name_path(&mut self) -> Option<NodeIdx> {
        if !self.at(Token::Identifier) {
            return None;
        }
        let node = self.alloc_node(NodeKind::NamePath);
        let start = self.current_token_idx();
        let mut last: Option<NodeIdx> = None;

        let first_ident = self.parse_ident()?;
        self.link_child(node, first_ident, &mut last);

        while self.at(Token::Dot) {
            self.skip_trivia();
            if !self.at(Token::Identifier) {
                break;
            }
            self.advance(); // consume dot
            self.skip_trivia();
            if let Some(ident) = self.parse_ident() {
                self.link_child(node, ident, &mut last);
            } else {
                break;
            }
        }

        self.finalize_node(node, start);
        Some(node)
    }

    // ======================== EXPRESSION PARSING (PRATT) ========================

    fn binding_power(token: Token) -> Option<(u8, u8)> {
        Some(match token {
            Token::Or => (1, 2),
            Token::And => (3, 4),
            Token::DoubleEquals
            | Token::NotEquals
            | Token::LessThan
            | Token::GreaterThan
            | Token::LessEquals
            | Token::GreaterEquals => (5, 6),
            Token::Pipe => (7, 8),
            Token::Caret => (9, 10),
            Token::Ampersand => (11, 12),
            Token::ShiftLeft | Token::ShiftRight => (13, 14),
            Token::Plus | Token::Minus | Token::PlusPercent | Token::MinusPercent => (15, 16),
            Token::Star
            | Token::Slash
            | Token::Percent
            | Token::StarPercent
            | Token::SlashPlus
            | Token::SlashNeg
            | Token::SlashLess
            | Token::SlashGreater => (17, 18),
            _ => return None,
        })
    }

    fn is_binary_op(&mut self) -> Option<(u8, u8)> {
        Self::binding_power(self.current_token()?)
    }

    fn unary_binding_power(token: Token) -> Option<u8> {
        match token {
            Token::Minus | Token::Not | Token::Tilde => Some(19),
            _ => None,
        }
    }

    fn is_unary_op(&mut self) -> Option<u8> {
        Self::unary_binding_power(self.current_token()?)
    }

    fn parse_expr(&mut self) -> Option<NodeIdx> {
        self.skip_trivia();
        self.parse_expr_bp(0)
    }

    fn parse_expr_bp(&mut self, min_bp: u8) -> Option<NodeIdx> {
        let mut lhs = self.parse_expr_prefix()?;

        loop {
            self.skip_trivia();

            if let Some((l_bp, r_bp)) = self.is_binary_op() {
                if l_bp < min_bp {
                    break;
                }

                let bin_node = self.alloc_node(NodeKind::BinaryExpr);
                let start = self.nodes[lhs.idx()].tokens.start;

                self.advance(); // consume operator
                self.skip_trivia();

                let rhs = self.parse_expr_bp(r_bp).unwrap_or_else(|| self.advance_with_error());

                let mut last = None;
                self.link_child(bin_node, lhs, &mut last);
                self.link_child(bin_node, rhs, &mut last);
                self.finalize_node(bin_node, start);

                lhs = bin_node;
            } else {
                break;
            }
        }

        Some(lhs)
    }

    fn parse_expr_prefix(&mut self) -> Option<NodeIdx> {
        self.skip_trivia();

        if let Some(r_bp) = self.is_unary_op() {
            let node = self.alloc_node(NodeKind::UnaryExpr);
            let start = self.current_token_idx();
            self.advance(); // consume operator
            self.skip_trivia();

            let operand = self.parse_expr_bp(r_bp).unwrap_or_else(|| self.advance_with_error());

            let mut last = None;
            self.link_child(node, operand, &mut last);
            self.finalize_node(node, start);
            return Some(node);
        }

        self.parse_expr_primary()
    }

    fn parse_expr_primary(&mut self) -> Option<NodeIdx> {
        let mut expr = self.parse_expr_atom()?;

        loop {
            self.skip_trivia();
            if self.at(Token::LeftRound) {
                expr = self.parse_call(expr);
            } else if self.at(Token::Dot) {
                expr = self.parse_member(expr);
            } else {
                break;
            }
        }

        Some(expr)
    }

    fn parse_expr_atom(&mut self) -> Option<NodeIdx> {
        self.skip_trivia();

        // Literals
        if let Some(lit) = self.parse_literal() {
            return Some(lit);
        }

        // Parenthesized expression
        if self.at(Token::LeftRound) {
            return Some(self.parse_paren_expr());
        }

        // Function definition
        if self.at(Token::Fn) {
            return Some(self.parse_fn_def());
        }

        // Struct definition
        if self.at(Token::Struct) {
            return Some(self.parse_struct_def());
        }

        // Conditional expression
        if self.at(Token::If) {
            return self.parse_cond_expr();
        }

        // Comptime expression
        if self.at(Token::Comptime) {
            return Some(self.parse_comptime_expr());
        }

        // Identifier or struct literal (name_path followed by optional `{`)
        if self.at(Token::Identifier) {
            let name = self.parse_name_path()?;
            self.skip_trivia();

            // Check for struct literal
            if self.at(Token::LeftCurly) {
                return Some(self.parse_struct_lit(name));
            }

            return Some(name);
        }

        None
    }

    fn parse_paren_expr(&mut self) -> NodeIdx {
        let node = self.alloc_node(NodeKind::ParenExpr);
        let start = self.current_token_idx();
        self.advance(); // consume '('
        self.skip_trivia();

        let inner = self.parse_expr().unwrap_or_else(|| self.advance_with_error());

        let mut last = None;
        self.link_child(node, inner, &mut last);

        self.skip_trivia();
        self.expect(Token::RightRound);
        self.finalize_node(node, start);
        node
    }

    fn parse_comptime_expr(&mut self) -> NodeIdx {
        let node = self.alloc_node(NodeKind::ComptimeExpr);
        let start = self.current_token_idx();
        self.advance(); // consume 'comptime'
        self.skip_trivia();

        let inner = self.parse_expr().unwrap_or_else(|| self.advance_with_error());

        let mut last = None;
        self.link_child(node, inner, &mut last);
        self.finalize_node(node, start);
        node
    }

    // ======================== POSTFIX OPERATIONS ========================

    fn parse_call(&mut self, callee: NodeIdx) -> NodeIdx {
        let node = self.alloc_node(NodeKind::CallExpr);
        let start = self.nodes[callee.idx()].tokens.start;
        self.advance(); // consume '('

        let mut last = None;
        self.link_child(node, callee, &mut last);

        let args = self.parse_arg_list();
        self.link_child(node, args, &mut last);

        self.skip_trivia();
        self.expect(Token::RightRound);
        self.finalize_node(node, start);
        node
    }

    fn parse_arg_list(&mut self) -> NodeIdx {
        let node = self.alloc_node(NodeKind::ArgList);
        let start = self.current_token_idx();
        let mut last = None;

        self.skip_trivia();
        if !self.at(Token::RightRound)
            && let Some(first) = self.parse_expr()
        {
            self.link_child(node, first, &mut last);

            loop {
                self.skip_trivia();
                if !self.eat(Token::Comma) {
                    break;
                }
                self.skip_trivia();
                if self.at(Token::RightRound) {
                    break;
                }
                if let Some(arg) = self.parse_expr() {
                    self.link_child(node, arg, &mut last);
                } else {
                    self.skip_until(EXPR_RECOVERY);
                    break;
                }
            }
        }

        self.finalize_node(node, start);
        node
    }

    fn parse_member(&mut self, base: NodeIdx) -> NodeIdx {
        let node = self.alloc_node(NodeKind::MemberExpr);
        let start = self.nodes[base.idx()].tokens.start;
        assert!(self.eat(Token::Dot), "invoked without '.'");

        let mut last = None;
        self.link_child(node, base, &mut last);

        self.skip_trivia();
        if let Some(ident) = self.expect_ident() {
            self.link_child(node, ident, &mut last);
        }

        self.finalize_node(node, start);
        node
    }

    // ======================== FUNCTION DEFINITION ========================

    fn parse_fn_def(&mut self) -> NodeIdx {
        let node = self.alloc_node(NodeKind::FnDef);
        let start = self.current_token_idx();
        self.advance(); // consume 'fn'
        self.skip_trivia();

        let mut last = None;

        self.expect(Token::LeftRound);
        let params = self.parse_param_list();
        self.link_child(node, params, &mut last);
        self.skip_trivia();
        self.expect(Token::RightRound);

        // Optional return type
        self.skip_trivia();
        if self.eat(Token::ThinArrow) {
            self.skip_trivia();
            let ret_type = self.parse_expr().unwrap_or_else(|| self.advance_with_error());
            self.link_child(node, ret_type, &mut last);
        }

        // Body block
        self.skip_trivia();
        let body = self.parse_block();
        self.link_child(node, body, &mut last);

        self.finalize_node(node, start);
        node
    }

    fn parse_param_list(&mut self) -> NodeIdx {
        let node = self.alloc_node(NodeKind::ParamList);
        let start = self.current_token_idx();
        let mut last = None;

        self.skip_trivia();
        if !self.at(Token::RightRound)
            && let Some(first) = self.parse_param_def()
        {
            self.link_child(node, first, &mut last);

            loop {
                self.skip_trivia();
                if !self.eat(Token::Comma) {
                    break;
                }
                self.skip_trivia();
                if self.at(Token::RightRound) {
                    break;
                }
                if let Some(param) = self.parse_param_def() {
                    self.link_child(node, param, &mut last);
                } else {
                    self.skip_until(PARAM_RECOVERY);
                    break;
                }
            }
        }

        self.finalize_node(node, start);
        node
    }

    fn parse_param_def(&mut self) -> Option<NodeIdx> {
        if !self.at(Token::Identifier) {
            return None;
        }
        let node = self.alloc_node(NodeKind::ParamDef);
        let start = self.current_token_idx();
        let mut last = None;

        let name = self.parse_ident()?;
        self.link_child(node, name, &mut last);

        self.skip_trivia();
        self.expect(Token::Colon);
        self.skip_trivia();

        let type_expr = self.parse_expr().unwrap_or_else(|| self.advance_with_error());
        self.link_child(node, type_expr, &mut last);

        self.finalize_node(node, start);
        Some(node)
    }

    // ======================== STRUCT DEFINITION ========================

    fn parse_struct_def(&mut self) -> NodeIdx {
        let node = self.alloc_node(NodeKind::StructDef);
        let start = self.current_token_idx();
        self.advance(); // consume 'struct'
        self.skip_trivia();

        let mut last = None;

        self.expect(Token::LeftCurly);
        let fields = self.parse_field_list();
        self.link_child(node, fields, &mut last);
        self.skip_trivia();
        self.expect(Token::RightCurly);

        self.finalize_node(node, start);
        node
    }

    fn parse_struct_lit(&mut self, name: NodeIdx) -> NodeIdx {
        let node = self.alloc_node(NodeKind::StructLit);
        let start = self.nodes[name.idx()].tokens.start;
        self.advance(); // consume '{'

        let mut last = None;
        self.link_child(node, name, &mut last);

        let fields = self.parse_field_list();
        self.link_child(node, fields, &mut last);

        self.skip_trivia();
        self.expect(Token::RightCurly);

        self.finalize_node(node, start);
        node
    }

    fn parse_field_list(&mut self) -> NodeIdx {
        let node = self.alloc_node(NodeKind::FieldList);
        let start = self.current_token_idx();
        let mut last = None;

        self.skip_trivia();
        while !self.at(Token::RightCurly) && !self.eof() {
            if let Some(field) = self.parse_field_def() {
                self.link_child(node, field, &mut last);
                self.skip_trivia();
                if !self.eat(Token::Comma) {
                    break;
                }
                self.skip_trivia();
            } else {
                break;
            }
        }

        self.finalize_node(node, start);
        node
    }

    fn parse_field_def(&mut self) -> Option<NodeIdx> {
        if !self.at(Token::Identifier) {
            return None;
        }
        let node = self.alloc_node(NodeKind::FieldDef);
        let start = self.current_token_idx();
        let mut last = None;

        let name = self.parse_ident()?;
        self.link_child(node, name, &mut last);

        self.skip_trivia();
        self.expect(Token::Colon);
        self.skip_trivia();

        let type_expr = self.parse_expr().unwrap_or_else(|| self.advance_with_error());
        self.link_child(node, type_expr, &mut last);

        self.finalize_node(node, start);
        Some(node)
    }

    // ======================== CONDITIONAL EXPRESSIONS ========================

    fn parse_cond_expr(&mut self) -> Option<NodeIdx> {
        let node = self.alloc_node(NodeKind::CondExpr);
        let start = self.current_token_idx();
        self.advance(); // consume 'if'
        self.skip_trivia();

        let mut last = None;

        self.expect(Token::LeftRound);
        self.skip_trivia();
        let cond = self.parse_expr().unwrap_or_else(|| self.advance_with_error());
        self.link_child(node, cond, &mut last);
        self.skip_trivia();
        self.expect(Token::RightRound);

        self.skip_trivia();
        let then_block = self.parse_block();
        self.link_child(node, then_block, &mut last);

        // Parse else branches
        loop {
            self.skip_trivia();
            if !self.eat(Token::Else) {
                break;
            }

            let else_node = self.alloc_node(NodeKind::ElseBranch);
            let else_start = self.last_token_idx;

            self.skip_trivia();
            if self.eat(Token::If) {
                // else if
                self.skip_trivia();
                self.expect(Token::LeftRound);
                self.skip_trivia();
                let else_cond = self.parse_expr().unwrap_or_else(|| self.advance_with_error());
                let mut else_last = None;
                self.link_child(else_node, else_cond, &mut else_last);
                self.skip_trivia();
                self.expect(Token::RightRound);

                self.skip_trivia();
                let else_block = self.parse_block();
                self.link_child(else_node, else_block, &mut else_last);
                self.finalize_node(else_node, else_start);
                self.link_child(node, else_node, &mut last);
            } else {
                // final else
                let else_block = self.parse_block();
                let mut else_last = None;
                self.link_child(else_node, else_block, &mut else_last);
                self.finalize_node(else_node, else_start);
                self.link_child(node, else_node, &mut last);
                break;
            }
        }

        self.finalize_node(node, start);
        Some(node)
    }

    // ======================== STATEMENTS ========================

    fn parse_stmt(&mut self) -> Option<NodeIdx> {
        self.skip_trivia();

        if self.at(Token::Let) {
            return Some(self.parse_let_stmt());
        }
        if self.at(Token::Return) {
            return Some(self.parse_return_stmt());
        }
        if self.at(Token::While) || self.at(Token::Inline) {
            return Some(self.parse_while_stmt());
        }
        if self.at(Token::If) {
            return Some(self.parse_cond_stmt());
        }
        if self.at(Token::LeftCurly) {
            return Some(self.parse_block());
        }

        // Expression statement or assignment
        self.parse_assign_or_expr_stmt()
    }

    fn parse_let_stmt(&mut self) -> NodeIdx {
        let node = self.alloc_node(NodeKind::LetStmt);
        let start = self.current_token_idx();
        self.advance(); // consume 'let'
        self.skip_trivia();

        let mut last = None;

        // Optional mut
        self.eat(Token::Mut);
        self.skip_trivia();

        // Name
        if let Some(name) = self.expect_ident() {
            self.link_child(node, name, &mut last);
        }

        // Optional type annotation
        self.skip_trivia();
        if self.eat(Token::Colon) {
            self.skip_trivia();
            let type_expr = self.parse_expr_or_error(BLOCK_RECOVERY);
            self.link_child(node, type_expr, &mut last);
        }

        // = value
        self.skip_trivia();
        if !self.eat(Token::Equals) {
            self.emit_unexpected();
            if self.at_any(BLOCK_RECOVERY) {
                self.finalize_node(node, start);
                return node;
            }
        }
        let after_eq_span = self.current_src_span();
        self.skip_trivia();
        if self.at_any(BLOCK_RECOVERY) {
            self.diagnostics.emit_missing_token(Token::Semicolon, after_eq_span);
            self.finalize_node(node, start);
            return node;
        }
        let value = self.parse_expr_or_error(BLOCK_RECOVERY);
        self.link_child(node, value, &mut last);

        self.skip_trivia();
        self.expect(Token::Semicolon);

        self.finalize_node(node, start);
        node
    }

    fn parse_return_stmt(&mut self) -> NodeIdx {
        let node = self.alloc_node(NodeKind::ReturnStmt);
        let start = self.current_token_idx();
        self.advance(); // consume 'return'
        self.skip_trivia();

        let mut last = None;

        let value = self.parse_expr_or_error(BLOCK_RECOVERY);
        self.link_child(node, value, &mut last);

        self.skip_trivia();
        self.expect(Token::Semicolon);

        self.finalize_node(node, start);
        node
    }

    fn parse_while_stmt(&mut self) -> NodeIdx {
        let node = self.alloc_node(NodeKind::WhileStmt);
        let start = self.current_token_idx();

        // Optional inline
        self.eat(Token::Inline);
        self.skip_trivia();

        self.expect(Token::While);
        self.skip_trivia();

        let mut last = None;

        self.expect(Token::LeftRound);
        self.skip_trivia();
        let cond = self.parse_expr().unwrap_or_else(|| self.advance_with_error());
        self.link_child(node, cond, &mut last);
        self.skip_trivia();
        self.expect(Token::RightRound);

        self.skip_trivia();
        let body = self.parse_block();
        self.link_child(node, body, &mut last);

        self.finalize_node(node, start);
        node
    }

    fn parse_cond_stmt(&mut self) -> NodeIdx {
        let node = self.alloc_node(NodeKind::CondStmt);
        let start = self.current_token_idx();
        self.advance(); // consume 'if'
        self.skip_trivia();

        let mut last = None;

        self.expect(Token::LeftRound);
        self.skip_trivia();
        let cond = self.parse_expr().unwrap_or_else(|| self.advance_with_error());
        self.link_child(node, cond, &mut last);
        self.skip_trivia();
        self.expect(Token::RightRound);

        self.skip_trivia();
        let then_block = self.parse_block();
        self.link_child(node, then_block, &mut last);

        // Parse else if branches (but not final else in statement form)
        loop {
            self.skip_trivia();
            if !self.at(Token::Else) {
                break;
            }

            // Peek ahead to see if this is else-if or final else
            self.advance(); // consume 'else'
            self.skip_trivia();

            if self.at(Token::If) {
                let else_node = self.alloc_node(NodeKind::ElseBranch);
                let else_start = self.last_token_idx;
                self.advance(); // consume 'if'

                self.skip_trivia();
                self.expect(Token::LeftRound);
                self.skip_trivia();
                let else_cond = self.parse_expr().unwrap_or_else(|| self.advance_with_error());
                let mut else_last = None;
                self.link_child(else_node, else_cond, &mut else_last);
                self.skip_trivia();
                self.expect(Token::RightRound);

                self.skip_trivia();
                let else_block = self.parse_block();
                self.link_child(else_node, else_block, &mut else_last);
                self.finalize_node(else_node, else_start);
                self.link_child(node, else_node, &mut last);
            } else {
                // Final else - this means it's actually a cond_expr being used as statement
                // For simplicity, handle it here
                let else_node = self.alloc_node(NodeKind::ElseBranch);
                let else_start = self.last_token_idx;
                let else_block = self.parse_block();
                let mut else_last = None;
                self.link_child(else_node, else_block, &mut else_last);
                self.finalize_node(else_node, else_start);
                self.link_child(node, else_node, &mut last);
                break;
            }
        }

        self.finalize_node(node, start);
        node
    }

    fn parse_assign_or_expr_stmt(&mut self) -> Option<NodeIdx> {
        let expr = self.parse_expr()?;

        self.skip_trivia();
        if self.eat(Token::Equals) {
            // Assignment
            let node = self.alloc_node(NodeKind::AssignStmt);
            let start = self.nodes[expr.idx()].tokens.start;

            self.skip_trivia();
            let value = self.parse_expr_or_error(BLOCK_RECOVERY);

            let mut last = None;
            self.link_child(node, expr, &mut last);
            self.link_child(node, value, &mut last);

            self.skip_trivia();
            self.expect(Token::Semicolon);

            self.finalize_node(node, start);
            Some(node)
        } else {
            // Expression statement
            let node = self.alloc_node(NodeKind::ExprStmt);
            let start = self.nodes[expr.idx()].tokens.start;

            let mut last = None;
            self.link_child(node, expr, &mut last);

            self.skip_trivia();
            self.expect(Token::Semicolon);

            self.finalize_node(node, start);
            Some(node)
        }
    }

    // ======================== BLOCKS ========================

    fn parse_block(&mut self) -> NodeIdx {
        let node = self.alloc_node(NodeKind::Block);
        let start = self.current_token_idx();

        self.skip_trivia();
        let has_open = self.expect(Token::LeftCurly);

        let mut last = None;

        if has_open {
            loop {
                self.skip_trivia();
                if self.at(Token::RightCurly) || self.eof() {
                    break;
                }

                if let Some(stmt) = self.parse_stmt() {
                    self.link_child(node, stmt, &mut last);
                } else {
                    if self.at_any(BLOCK_RECOVERY) {
                        break;
                    }
                    let err = self.advance_with_error();
                    self.link_child(node, err, &mut last);
                }
            }

            self.skip_trivia();
            self.expect(Token::RightCurly);
        } else {
            self.skip_trivia();
            self.eat(Token::RightCurly);
        }

        self.finalize_node(node, start);
        node
    }

    // ======================== TOP-LEVEL DECLARATIONS ========================

    fn parse_program(&mut self) {
        loop {
            self.skip_trivia();
            if self.eof() {
                break;
            }

            if self.check(Token::Init) {
                self.parse_init_block();
            } else if self.check(Token::Run) {
                self.parse_run_block();
            } else if self.check(Token::Const) {
                self.parse_const_decl();
            } else {
                self.emit_unexpected();
                self.advance();
            }
        }
    }

    fn parse_init_block(&mut self) {
        let node = self.alloc_node(NodeKind::InitBlock);
        let start = self.current_token_idx();
        self.advance(); // consume 'init'

        self.skip_trivia();
        let block = self.parse_block();

        let mut last = None;
        self.link_child(node, block, &mut last);

        self.finalize_node(node, start);
    }

    fn parse_run_block(&mut self) {
        let node = self.alloc_node(NodeKind::RunBlock);
        let start = self.current_token_idx();
        self.advance(); // consume 'run'

        self.skip_trivia();
        let block = self.parse_block();

        let mut last = None;
        self.link_child(node, block, &mut last);

        self.finalize_node(node, start);
    }

    fn parse_const_decl(&mut self) {
        let node = self.alloc_node(NodeKind::ConstDecl);
        let start = self.current_token_idx();
        self.advance(); // consume 'const'
        self.skip_trivia();

        let mut last = None;

        // Name
        if let Some(name) = self.expect_ident() {
            self.link_child(node, name, &mut last);
        }

        // Optional type annotation
        self.skip_trivia();
        if self.eat(Token::Colon) {
            self.skip_trivia();
            let type_expr = self.parse_expr_or_error(BLOCK_RECOVERY);
            self.link_child(node, type_expr, &mut last);
        }

        // = value
        self.skip_trivia();
        if !self.expect(Token::Equals) && self.at_any(BLOCK_RECOVERY) {
            self.finalize_node(node, start);
            return;
        }

        let after_eq_span = self.current_src_span();
        self.skip_trivia();
        if self.at_any(BLOCK_RECOVERY) {
            self.diagnostics.emit_missing_token(Token::Semicolon, after_eq_span);
            self.finalize_node(node, start);
            return;
        }
        let value = self.parse_expr_or_error(BLOCK_RECOVERY);
        self.link_child(node, value, &mut last);

        self.skip_trivia();
        self.expect(Token::Semicolon);

        self.finalize_node(node, start);
    }
}

pub fn parse<'ast, 'src, D: DiagnosticsContext>(
    arena: &'ast Bump,
    lexer: Lexer<'src>,
    estimated_node_count: usize,
    diagnostics: &mut D,
) -> ConcreteSyntaxTree<'ast> {
    let mut parser = Parser::new(
        arena,
        lexer.enumerate().map(|(i, (tok, span))| (tok, TokenIdx::new(i as u32), span)),
        estimated_node_count,
        diagnostics,
    );

    parser.parse_program();

    ConcreteSyntaxTree { nodes: parser.nodes }
}
