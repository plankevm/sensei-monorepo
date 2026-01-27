use crate::{
    cst::{self, *},
    diagnostics::DiagnosticsContext,
    lexer::*,
    parser::token_item_iter::TokenItems,
};
use allocator_api2::vec::Vec;
use bumpalo::Bump;
use neosen_data::{IndexVec, Span, span::IncIterable};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct OpPriority(u8);

impl OpPriority {
    const ZERO: Self = OpPriority(0);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ParseExprMode {
    AllowAll,
    CondExpr,
    TypeExpr,
}

enum StmtResult {
    Statement(NodeIdx),
    MaybeEndExpr(NodeIdx),
    ForcedEndExpr(NodeIdx),
}

#[derive(Debug, Clone, Copy)]
struct UnfinishedNode {
    idx: NodeIdx,
    last_child: Option<NodeIdx>,
}

// Ensure fields are private letting us more easily enforce the invariant that the iterator either
// consumes fuel or advances.
mod token_item_iter {
    use crate::lexer::{Lexer, SourceSpan, Token};

    pub(super) struct TokenItems<'src> {
        lexer: Lexer<'src>,
        peeked: Option<(Token, SourceSpan)>,
        fuel: u32,
    }

    impl<'src> TokenItems<'src> {
        const DEFAULT_FUEL: u32 = 256;

        pub(crate) fn new(lexer: Lexer<'src>) -> Self {
            TokenItems { lexer, peeked: None, fuel: Self::DEFAULT_FUEL }
        }

        fn next_fuel_unchanged(&mut self) -> (Token, SourceSpan) {
            self.peeked.take().unwrap_or_else(|| {
                let (tok, span) = self.lexer.next_with_eof();
                (tok, span)
            })
        }

        pub(crate) fn peek(&mut self) -> (Token, SourceSpan) {
            self.fuel =
                self.fuel.checked_sub(1).expect("out of fuel: likely caused by infinite loop");
            let next = self.next_fuel_unchanged();
            self.peeked = Some(next);
            next
        }

        pub(super) fn next(&mut self) -> (Token, SourceSpan) {
            self.fuel = Self::DEFAULT_FUEL;
            self.peeked.take().unwrap_or_else(|| self.next_fuel_unchanged())
        }
    }
}

struct Parser<'ast, 'd, 'src, D: DiagnosticsContext> {
    nodes: IndexVec<NodeIndex, cst::Node, &'ast Bump>,
    expected: Vec<Token, &'ast Bump>,
    tokens: TokenItems<'src>,
    diagnostics: &'d mut D,
    current_token_idx: TokenIdx,
    last_src_span: SourceSpan,
    last_unexpected: Option<TokenIdx>,
}

impl<'ast, 'd, 'src, D> Parser<'ast, 'd, 'src, D>
where
    D: DiagnosticsContext,
{
    const UNARY_PRIORITY: OpPriority = OpPriority(19);
    const _MEMBER_PRIORITY: OpPriority = OpPriority(21);

    fn new(
        arena: &'ast Bump,
        lexer: Lexer<'src>,
        estimated_node_count: usize,
        diagnostics: &'d mut D,
    ) -> Self {
        Parser {
            tokens: TokenItems::new(lexer),
            nodes: IndexVec::with_capacity_in(estimated_node_count, arena),
            expected: Vec::with_capacity_in(8, arena),
            diagnostics,
            current_token_idx: TokenIdx::ZERO,
            last_src_span: Span::new(0, 0),
            last_unexpected: None,
        }
    }

    fn assert_complete(&mut self) {
        assert!(self.eof());
        for (i, node) in self.nodes.enumerate_idx() {
            assert!(!node.tokens.is_dummy(), "node #{} has dummy token span", i.get());
        }
    }

    fn current_token(&mut self) -> Token {
        self.tokens.peek().0
    }

    fn current_src_span(&mut self) -> SourceSpan {
        self.tokens.peek().1
    }

    fn advance(&mut self) {
        self.expected.clear();

        let (token, src_span) = self.tokens.next();
        let ti = self.current_token_idx.get_and_inc();
        self.last_src_span = src_span;
        if token.is_lex_error() {
            self.diagnostics.emit_lexer_error(token, ti, src_span);
        }
    }

    fn at(&mut self, token: Token) -> bool {
        self.current_token() == token
    }

    fn skip_trivia(&mut self) {
        while let token = self.current_token()
            && (token.is_trivia() || token.is_lex_error())
        {
            self.advance();
        }
    }

    fn check(&mut self, token: Token) -> bool {
        self.skip_trivia();
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
        if self.last_unexpected.is_some_and(|ti| ti == self.current_token_idx) {
            return;
        }
        let found = self.current_token();
        let span = self.current_src_span();
        self.last_unexpected = Some(self.current_token_idx);
        self.diagnostics.emit_unexpected_token(found, &self.expected, span);
        self.expected.clear();
    }

    fn eof(&mut self) -> bool {
        self.skip_trivia();
        self.at(Token::Eof)
    }

    fn expect(&mut self, token: Token) -> bool {
        let eaten = self.eat(token);
        if !eaten {
            self.emit_unexpected();
        }
        eaten
    }

    fn alloc_node_from(&mut self, start: TokenIdx, kind: NodeKind) -> UnfinishedNode {
        let idx = self.nodes.push(Node {
            kind,
            tokens: Span::new(start, start),
            next_sibling: None,
            first_child: None,
        });
        UnfinishedNode { idx, last_child: None }
    }

    fn alloc_node(&mut self, kind: NodeKind) -> UnfinishedNode {
        let idx = self.nodes.push(Node {
            kind,
            tokens: Span::new(self.current_token_idx, self.current_token_idx),
            next_sibling: None,
            first_child: None,
        });
        UnfinishedNode { idx, last_child: None }
    }

    fn close_node(&mut self, node: UnfinishedNode) -> NodeIdx {
        self.nodes[node.idx].tokens.end = self.current_token_idx;
        node.idx
    }

    fn update_kind(&mut self, node: UnfinishedNode, kind: NodeKind) {
        self.nodes[node.idx].kind = kind;
    }

    fn push_child(&mut self, parent: &mut UnfinishedNode, child: NodeIdx) {
        match parent.last_child {
            Some(last_child) => {
                debug_assert!(self.nodes[parent.idx].first_child.is_some());
                debug_assert!(self.nodes[last_child].next_sibling.is_none());
                debug_assert!(
                    self.nodes[last_child].tokens.end <= self.nodes[child].tokens.start,
                    "children tokens overlap"
                );
                self.nodes[last_child].next_sibling = Some(child);
                parent.last_child = Some(child);
            }
            None => {
                debug_assert!(self.nodes[parent.idx].first_child.is_none());
                self.nodes[parent.idx].first_child = Some(child);
                parent.last_child = Some(child);
            }
        }
    }

    fn alloc_last_token_as_node(&mut self, kind: NodeKind) -> NodeIdx {
        let node = self.alloc_node_from(self.current_token_idx - 1, kind);
        self.close_node(node)
    }

    // ======================== EXPRESSION PARSING (PRATT) ========================

    fn check_binary_op(&mut self) -> Option<(OpPriority, OpPriority, BinaryOp)> {
        macro_rules! check_binary_op {
            ($($kind:ident => ($left:literal, $right:literal)),* $(,)?) => {
                $(
                    if self.check(Token::$kind) {
                        return Some((OpPriority($left), OpPriority($right), BinaryOp::$kind));
                    }
                )*
            };
        }

        check_binary_op! {
            Or => (1, 2),
            And => (3, 4),
            DoubleEquals => (5, 6),
            BangEquals => (5, 6),
            LessThan => (5, 6),
            GreaterThan => (5, 6),
            LessEquals => (5, 6),
            GreaterEquals => (5, 6),
            Pipe => (7, 8),
            Caret => (9, 10),
            Ampersand => (11, 12),
            ShiftLeft => (13, 14),
            ShiftRight => (13, 14),
            Plus => (15, 16),
            Minus => (15, 16),
            PlusPercent => (15, 16),
            MinusPercent => (15, 16),
            Star => (17, 18),
            Slash => (17, 18),
            Percent => (17, 18),
            StarPercent => (17, 18),
            SlashPlus => (17, 18),
            SlashNeg => (17, 18),
            SlashLess => (17, 18),
            SlashGreater => (17, 18),
        }

        None
    }

    fn eat_unary(&mut self) -> Option<((), OpPriority, UnaryOp)> {
        if self.eat(Token::Minus) {
            return Some(((), Self::UNARY_PRIORITY, UnaryOp::Minus));
        }
        if self.eat(Token::Bang) {
            return Some(((), Self::UNARY_PRIORITY, UnaryOp::Bang));
        }
        if self.eat(Token::Tilde) {
            return Some(((), Self::UNARY_PRIORITY, UnaryOp::Tilde));
        }
        None
    }

    // ========================== EXPRESSION PARSING ==========================

    fn try_parse_conditional(&mut self) -> Option<NodeIdx> {
        let condition_chain_start = self.current_token_idx;
        if !self.eat(Token::If) {
            return None;
        }

        let mut conditional = self.alloc_node_from(condition_chain_start, NodeKind::If);

        let if_condition = self.parse_expr(ParseExprMode::CondExpr);
        self.push_child(&mut conditional, if_condition);
        let if_body = self.parse_block(self.current_token_idx, NodeKind::Block);
        self.push_child(&mut conditional, if_body);

        let mut else_ifs = self.alloc_node(NodeKind::ElseIfBranchList);

        let mut r#else = None;
        while self.check(Token::Else) {
            // More robust way to get token offset at the `Else` token than `eat; current-1`.
            let branch_start = self.current_token_idx;
            assert!(self.expect(Token::Else));

            if !self.eat(Token::If) {
                let else_body = self.parse_block(self.current_token_idx, NodeKind::Block);
                r#else = Some(else_body);

                break;
            }

            let mut else_if = self.alloc_node_from(branch_start, NodeKind::ElseIfBranch);

            let else_condition = self.parse_expr(ParseExprMode::CondExpr);
            self.push_child(&mut else_if, else_condition);
            let branch_body = self.parse_block(self.current_token_idx, NodeKind::Block);
            self.push_child(&mut else_if, branch_body);

            let else_if = self.close_node(else_if);
            self.push_child(&mut else_ifs, else_if);
        }

        let else_ifs = self.close_node(else_ifs);
        self.push_child(&mut conditional, else_ifs);

        if let Some(r#else) = r#else {
            self.nodes[else_ifs].tokens.end = self.nodes[r#else].tokens.start;
            self.push_child(&mut conditional, r#else);
        }

        Some(self.close_node(conditional))
    }

    fn try_parse_standalone_expr(&mut self, _mode: ParseExprMode) -> Option<NodeIdx> {
        let start = self.current_token_idx;

        if self.eat(Token::DecimalLiteral)
            || self.eat(Token::BinLiteral)
            || self.eat(Token::HexLiteral)
            || self.eat(Token::True)
            || self.eat(Token::False)
        {
            return Some(self.alloc_last_token_as_node(NodeKind::LiteralExpr));
        }

        if self.eat(Token::Identifier) {
            return Some(self.alloc_last_token_as_node(NodeKind::Identifier));
        }

        if self.eat(Token::LeftRound) {
            // TODO: Track recursion to emit nice error instead of stack overflow.
            let mut paren_expr = self.alloc_node_from(start, NodeKind::ParenExpr);
            let inner_expr = self.parse_expr(ParseExprMode::AllowAll);
            self.push_child(&mut paren_expr, inner_expr);
            self.expect(Token::RightRound);
            return Some(self.close_node(paren_expr));
        }

        if self.eat(Token::Comptime) {
            return Some(self.parse_block(start, NodeKind::ComptimeBlock));
        }

        if self.check(Token::LeftCurly) {
            return Some(self.parse_block(self.current_token_idx, NodeKind::Block));
        }

        if let Some(conditional) = self.try_parse_conditional() {
            return Some(conditional);
        }

        None
    }

    fn parse_expr(&mut self, mode: ParseExprMode) -> NodeIdx {
        self.try_parse_expr(mode).unwrap_or_else(|| {
            self.emit_unexpected();
            let err = self.alloc_node(NodeKind::Error);
            self.close_node(err)
        })
    }

    fn try_parse_expr(&mut self, mode: ParseExprMode) -> Option<NodeIdx> {
        self.try_parse_expr_min_bp(mode, OpPriority::ZERO)
    }

    fn try_parse_expr_min_bp(
        &mut self,
        mode: ParseExprMode,
        min_bp: OpPriority,
    ) -> Option<NodeIdx> {
        let start = self.current_token_idx;

        let mut expr = if let Some(((), rhs, kind)) = self.eat_unary() {
            let mut unary = self.alloc_node_from(start, NodeKind::UnaryExpr(kind));
            // TODO: Track recursion
            let expr = self.try_parse_expr_min_bp(mode, rhs).unwrap_or_else(|| {
                self.emit_unexpected();
                let err = self.alloc_node(NodeKind::Error);
                self.close_node(err)
            });
            self.push_child(&mut unary, expr);
            self.close_node(unary)
        } else {
            self.try_parse_standalone_expr(mode)?
        };

        loop {
            if self.eat(Token::Dot) {
                let mut member = self.alloc_node_from(start, NodeKind::MemberExpr);
                self.push_child(&mut member, expr);
                let access_name = if self.expect(Token::Identifier) {
                    self.alloc_last_token_as_node(NodeKind::Identifier)
                } else {
                    let error = self.alloc_node(NodeKind::Error);
                    self.close_node(error)
                };
                self.push_child(&mut member, access_name);
                expr = self.close_node(member);
                continue;
            }

            if let Some((lhs, rhs, kind)) = self.check_binary_op() {
                if lhs < min_bp {
                    break;
                }
                self.advance(); // consume operator token
                let mut binary_expr = self.alloc_node_from(start, NodeKind::BinaryExpr(kind));
                self.push_child(&mut binary_expr, expr);
                let rhs_expr = self.try_parse_expr_min_bp(mode, rhs).unwrap_or_else(|| {
                    self.emit_unexpected();
                    let err = self.alloc_node(NodeKind::Error);
                    self.close_node(err)
                });
                self.push_child(&mut binary_expr, rhs_expr);
                expr = self.close_node(binary_expr);
                continue;
            }

            break;
        }

        Some(expr)
    }

    // ========================== STATEMENT PARSING ==========================

    fn try_parse_stmt(&mut self) -> Option<StmtResult> {
        let stmt_start = self.current_token_idx;
        let expr = self.try_parse_expr(ParseExprMode::AllowAll)?;

        if self.eat(Token::Semicolon) {
            let mut expr_stmt = self.alloc_node_from(stmt_start, NodeKind::ExprStmt);
            self.push_child(&mut expr_stmt, expr);
            let expr_stmt = self.close_node(expr_stmt);
            return Some(StmtResult::Statement(expr_stmt));
        }

        let expr_kind = self.nodes[expr].kind;
        let requires_semi = expr_kind
            .expr_requires_semi_as_stmt()
            .unwrap_or_else(|| panic!("`try_parse_expr` returned non-expr node {:?}", expr_kind));

        if requires_semi {
            Some(StmtResult::ForcedEndExpr(expr))
        } else {
            Some(StmtResult::MaybeEndExpr(expr))
        }
    }

    fn parse_block(&mut self, block_start: TokenIdx, block_kind: NodeKind) -> NodeIdx {
        let mut block = self.alloc_node_from(block_start, block_kind);

        self.expect(Token::LeftCurly);

        let mut statements_list = self.alloc_node(NodeKind::StatementsList);
        let mut end_expr = None;

        while !self.check(Token::RightCurly) {
            let Some(result) = self.try_parse_stmt() else {
                self.emit_unexpected();
                break;
            };

            if let Some(prev_end) = end_expr.take() {
                self.push_child(&mut statements_list, prev_end);
            }

            match result {
                StmtResult::Statement(stmt) => self.push_child(&mut statements_list, stmt),
                StmtResult::MaybeEndExpr(expr) => end_expr = Some(expr),
                StmtResult::ForcedEndExpr(expr) => {
                    end_expr = Some(expr);
                    break;
                }
            }
        }

        let statements_list = self.close_node(statements_list);
        self.push_child(&mut block, statements_list);
        if let Some(end_expr) = end_expr {
            self.nodes[statements_list].tokens.end = self.nodes[end_expr].tokens.start;
            self.push_child(&mut block, end_expr);
        }

        self.expect(Token::RightCurly);

        self.close_node(block)
    }

    // ======================== TOP-LEVEL DECLARATIONS ========================

    fn parse_file(&mut self) -> NodeIdx {
        let mut file = self.alloc_node(NodeKind::File);

        while !self.eof() {
            let new_decl = self.parse_decl();
            self.push_child(&mut file, new_decl);
        }

        self.close_node(file)
    }

    fn parse_decl(&mut self) -> NodeIdx {
        let start = self.current_token_idx;
        if self.eat(Token::Init) {
            self.parse_block(start, NodeKind::InitBlock)
        } else if self.eat(Token::Run) {
            self.parse_block(start, NodeKind::RunBlock)
        } else if self.check(Token::Const) {
            self.parse_const_decl()
        } else {
            self.emit_unexpected();
            self.advance();
            self.alloc_last_token_as_node(NodeKind::Error)
        }
    }

    fn parse_const_decl(&mut self) -> NodeIdx {
        let start = self.current_token_idx;
        assert!(self.expect(Token::Const));

        let mut r#const = self.alloc_node_from(start, NodeKind::ConstDecl);

        let name = if self.expect(Token::Identifier) {
            self.alloc_last_token_as_node(NodeKind::Identifier)
        } else {
            let error = self.alloc_node(NodeKind::Error);
            self.close_node(error)
        };
        self.push_child(&mut r#const, name);

        // Optional type annotation
        if self.eat(Token::Colon) {
            self.update_kind(r#const, NodeKind::TypedConstDecl);
            let type_expr = self.parse_expr(ParseExprMode::TypeExpr);
            self.push_child(&mut r#const, type_expr);
        }

        // = value
        self.expect(Token::Equals);

        let expr = self.parse_expr(ParseExprMode::AllowAll);
        self.push_child(&mut r#const, expr);

        self.expect(Token::Semicolon);

        self.close_node(r#const)
    }
}

pub fn parse<'ast, 'src, D: DiagnosticsContext>(
    arena: &'ast Bump,
    lexer: Lexer<'src>,
    estimated_node_count: usize,
    diagnostics: &mut D,
) -> ConcreteSyntaxTree<'ast> {
    let mut parser = Parser::new(arena, lexer, estimated_node_count, diagnostics);

    let file = parser.parse_file();
    assert_eq!(file, ConcreteSyntaxTree::FILE_IDX);

    parser.assert_complete();

    ConcreteSyntaxTree { nodes: parser.nodes }
}
