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

const DECL_RECOVERY: &[Token] = &[Token::Init, Token::Run, Token::Const];
// Recovery sets - tokens that signal "stop skipping, parent can handle this"
const BLOCK_RECOVERY: &[Token] = &[Token::RightCurly, Token::Init, Token::Run, Token::Const];
const EXPR_RECOVERY: &[Token] =
    &[Token::Semicolon, Token::RightCurly, Token::Comma, Token::RightRound];
const PARAM_RECOVERY: &[Token] = &[Token::RightRound, Token::ThinArrow, Token::LeftCurly];

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
            self.fuel = self.fuel.checked_sub(1).expect("out of fuel");
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

    fn at_any(&mut self, tokens: &[Token]) -> bool {
        tokens.contains(&self.current_token())
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

    fn alloc_node(&mut self, kind: NodeKind) -> NodeIdx {
        self.nodes.push(Node { kind, tokens: Span::dummy(), next_sibling: None, first_child: None })
    }

    fn finalize_node(&mut self, node: NodeIdx, start: TokenIdx) -> NodeIdx {
        let end = self.current_token_idx;
        self.nodes[node].tokens = Span::new(start, end);
        node
    }

    fn update_kind(&mut self, node: NodeIdx, kind: NodeKind) {
        self.nodes[node].kind = kind;
    }

    fn set_first_child(&mut self, parent: NodeIdx, child: NodeIdx) -> NodeIdx {
        debug_assert!(self.nodes[parent].first_child.is_none(), "ovewriting child");
        self.nodes[parent].first_child = Some(child);
        child
    }

    fn push_sibling(&mut self, last: &mut NodeIdx, child: NodeIdx) {
        debug_assert!(self.nodes[*last].next_sibling.is_none(), "overwriting sibling");
        self.nodes[*last].next_sibling = Some(child);
        *last = child;
    }

    fn link_child(&mut self, parent: NodeIdx, child: NodeIdx, last: &mut Option<NodeIdx>) {
        if let Some(prev) = last.replace(child) {
            self.nodes[prev].next_sibling = Some(child);
        } else {
            self.nodes[parent].first_child = Some(child);
        }
    }

    fn alloc_single_token_node(&mut self, kind: NodeKind) -> NodeIdx {
        let node = self.alloc_node(kind);
        self.finalize_node(node, self.current_token_idx - 1);
        node
    }

    // ======================== EXPRESSION PARSING (PRATT) ========================

    fn check_binary_op(&mut self) -> Option<(OpPriority, OpPriority, BinaryKind)> {
        macro_rules! check_binary_op {
            ($($kind:ident => ($left:literal, $right:literal)),* $(,)?) => {
                $(
                    if self.check(Token::$kind) {
                        return Some((OpPriority($left), OpPriority($right), BinaryKind::$kind));
                    }
                )*
            };
        }

        check_binary_op! {
            Or => (1, 2),
            And => (3, 4),
            DoubleEquals => (5, 6),
            NotEquals => (5, 6),
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

    fn check_unary(&mut self) -> Option<UnaryKind> {
        if self.eat(Token::Minus) {
            return Some(UnaryKind::Minus);
        }
        if self.eat(Token::Not) {
            return Some(UnaryKind::Not);
        }
        if self.eat(Token::Tilde) {
            return Some(UnaryKind::Tilde);
        }
        None
    }

    // ========================== EXPRESSION PARSING ==========================

    fn parse_atom(&mut self) -> NodeIdx {
        let start = self.current_token_idx;
        let expr = if self.eat(Token::DecimalLiteral)
            || self.eat(Token::BinLiteral)
            || self.eat(Token::HexLiteral)
            || self.eat(Token::True)
            || self.eat(Token::False)
        {
            self.alloc_single_token_node(NodeKind::LiteralExpr)
        } else if self.eat(Token::Identifier) {
            self.alloc_single_token_node(NodeKind::Identifier)
        } else if self.eat(Token::LeftRound) {
            // TODO: Track recursion to emit nice error instead of stack overflow.
            let paren_expr = self.alloc_node(NodeKind::ParenExpr);
            let inner_expr = self.parse_expr(ParseExprMode::AllowAll);
            self.set_first_child(paren_expr, inner_expr);
            self.expect(Token::RightRound);
            self.finalize_node(paren_expr, start)
        } else {
            // return None;
            let err = self.alloc_node(NodeKind::Error);
            self.finalize_node(err, self.current_token_idx)
        };
        expr
    }

    fn parse_expr(&mut self, mode: ParseExprMode) -> NodeIdx {
        let start = self.current_token_idx;
        let mut lhs = self.parse_atom();
        while self.eat(Token::Dot) {
            let member = self.alloc_node(NodeKind::MemberExpr);
            let mut last = self.set_first_child(member, lhs);
            let access_name = if self.expect(Token::Identifier) {
                self.alloc_single_token_node(NodeKind::Identifier)
            } else {
                let error = self.alloc_node(NodeKind::Error);
                self.finalize_node(error, self.current_token_idx)
            };
            self.push_sibling(&mut last, access_name);
            lhs = self.finalize_node(member, start);
        }
        lhs
    }

    // ========================== STATEMENT PARSING ==========================

    fn parse_block(&mut self, start: TokenIdx, block_kind: NodeKind) -> NodeIdx {
        let block = self.alloc_node(block_kind);

        self.expect(Token::LeftCurly);
        self.expect(Token::RightCurly);

        self.finalize_node(block, start)
    }

    // ======================== TOP-LEVEL DECLARATIONS ========================

    fn parse_file(&mut self) -> NodeIdx {
        let file = self.alloc_node(NodeKind::File);
        let mut last = None;

        while !self.eof() {
            let new_decl = self.parse_decl();
            self.link_child(file, new_decl, &mut last);
        }

        self.finalize_node(file, TokenIdx::ZERO)
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
            self.alloc_single_token_node(NodeKind::Error)
        }
    }

    fn parse_const_decl(&mut self) -> NodeIdx {
        let start = self.current_token_idx;
        assert!(self.expect(Token::Const));

        let r#const = self.alloc_node(NodeKind::ConstDecl);

        let name = if self.expect(Token::Identifier) {
            self.alloc_single_token_node(NodeKind::Identifier)
        } else {
            let error = self.alloc_node(NodeKind::Error);
            self.finalize_node(error, self.current_token_idx)
        };
        let mut last = self.set_first_child(r#const, name);

        // Optional type annotation
        if self.eat(Token::Colon) {
            self.update_kind(r#const, NodeKind::TypedConstDecl);
            let type_expr = self.parse_expr(ParseExprMode::TypeExpr);
            self.push_sibling(&mut last, type_expr);
        }

        // = value
        self.expect(Token::Equals);

        let expr = self.parse_expr(ParseExprMode::AllowAll);
        self.push_sibling(&mut last, expr);

        self.expect(Token::Semicolon);

        self.finalize_node(r#const, start)
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
