use allocator_api2::vec::Vec;
use bumpalo::Bump;

use crate::{
    ast::*,
    diagnostics::DiagnosticsContext,
    lexer::{Lexer, SourceSpan, Token},
};
use neosen_data::{Span, bigint::FrozenBigUint};

#[derive(Debug, Clone)]
pub struct ParseError;

fn estimate_declaration_count(source: &str) -> usize {
    const AVG_DECLARATIONS_PER_SRC_BYTES: usize = 30;
    source.len().div_ceil(AVG_DECLARATIONS_PER_SRC_BYTES)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Recovered {
    No,
    Yes,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExpectedToken {
    Token(Token),
    Ident,
    Literal,
    Expr,
}

impl std::fmt::Display for ExpectedToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExpectedToken::Token(tok) => write!(f, "{}", token_description(*tok)),
            ExpectedToken::Ident => write!(f, "identifier"),
            ExpectedToken::Literal => write!(f, "literal"),
            ExpectedToken::Expr => write!(f, "expression"),
        }
    }
}

fn token_description(token: Token) -> &'static str {
    match token {
        Token::Semicolon => "`;`",
        Token::Comma => "`,`",
        Token::Colon => "`:`",
        Token::Dot => "`.`",
        Token::LeftCurly => "`{`",
        Token::RightCurly => "`}`",
        Token::LeftRound => "`(`",
        Token::RightRound => "`)`",
        Token::LeftSquare => "`[`",
        Token::RightSquare => "`]`",
        Token::ThinArrow => "`->`",
        Token::Equals => "`=`",
        Token::Plus => "`+`",
        Token::PlusPercent => "`+%`",
        Token::Minus => "`-`",
        Token::MinusPercent => "`-%`",
        Token::Star => "`*`",
        Token::StarPercent => "`*%`",
        Token::Slash => "`/`",
        Token::SlashPlus => "`/+`",
        Token::SlashNeg => "`/-`",
        Token::SlashLess => "`/<`",
        Token::SlashGreater => "`/>`",
        Token::Percent => "`%`",
        Token::DoubleEquals => "`==`",
        Token::NotEquals => "`!=`",
        Token::LessThan => "`<`",
        Token::GreaterThan => "`>`",
        Token::LessEquals => "`<=`",
        Token::GreaterEquals => "`>=`",
        Token::And => "`&&`",
        Token::Or => "`||`",
        Token::Not => "`!`",
        Token::Ampersand => "`&`",
        Token::Pipe => "`|`",
        Token::Caret => "`^`",
        Token::Tilde => "`~`",
        Token::ShiftLeft => "`<<`",
        Token::ShiftRight => "`>>`",
        Token::If => "`if`",
        Token::Else => "`else`",
        Token::Fn => "`fn`",
        Token::Let => "`let`",
        Token::Mut => "`mut`",
        Token::Const => "`const`",
        Token::Init => "`init`",
        Token::Run => "`run`",
        Token::Struct => "`struct`",
        Token::Return => "`return`",
        Token::Comptime => "`comptime`",
        Token::Inline => "`inline`",
        Token::While => "`while`",
        Token::True => "`true`",
        Token::False => "`false`",
        Token::Identifier => "identifier",
        Token::DecLiteral => "decimal literal",
        Token::HexLiteral => "hex literal",
        Token::BinLiteral => "binary literal",
        Token::Error => "error",
    }
}

const EOF_SPAN: SourceSpan = Span::new(u32::MAX, 0);

pub struct Parser<'src, 'ast> {
    #[allow(dead_code)]
    arena: &'ast Bump,
    source: &'src str,
    interner: StringInterner,
    diagnostics: DiagnosticsContext<'ast>,

    token: Option<Token>,
    current_span: SourceSpan,
    prev_token: Option<Token>,
    prev_span: SourceSpan,

    expected_tokens: std::vec::Vec<ExpectedToken>,
    tokens: std::iter::Peekable<Lexer<'src>>,
}

impl<'src, 'ast> Parser<'src, 'ast> {
    pub fn new(source: &'src str, arena: &'ast Bump) -> Self {
        let mut lexer = Lexer::new(source).peekable();
        let (token, token_span) = lexer.next().map_or((None, EOF_SPAN), |(t, s)| (Some(t), s));

        Self {
            arena,
            source,
            interner: StringInterner::with_hasher(std::hash::RandomState::new()),
            diagnostics: DiagnosticsContext::new(arena),
            token,
            current_span: token_span,
            prev_token: None,
            prev_span: Span::new(0, 0),
            expected_tokens: std::vec::Vec::new(),
            tokens: lexer,
        }
    }

    pub fn bump(&mut self) {
        self.prev_token = self.token;
        self.prev_span = self.current_span;

        let (next_token, next_span) =
            self.tokens.next().map_or((None, EOF_SPAN), |(t, s)| (Some(t), s));
        self.token = next_token;
        self.current_span = next_span;

        self.expected_tokens.clear();
    }

    pub fn check_noexpect(&self, tok: Token) -> bool {
        self.token == Some(tok)
    }

    pub fn check(&mut self, tok: Token) -> bool {
        let is_present = self.check_noexpect(tok);
        if !is_present {
            self.push_expected(ExpectedToken::Token(tok));
        }
        is_present
    }

    pub fn eat(&mut self, tok: Token) -> bool {
        let is_present = self.check(tok);
        if is_present {
            self.bump();
        }
        is_present
    }

    pub fn expect(&mut self, tok: Token) -> Result<Recovered, ParseError> {
        if self.check_noexpect(tok) {
            self.bump();
            Ok(Recovered::No)
        } else {
            self.expected_one_of_not_found(&[tok])
        }
    }

    fn push_expected(&mut self, expected: ExpectedToken) {
        if !self.expected_tokens.contains(&expected) {
            self.expected_tokens.push(expected);
        }
    }

    fn unexpected_token(&mut self) -> ParseError {
        let _ = self.expected_one_of_not_found(&[]);
        ParseError
    }

    fn check_with(&mut self, tok: Token, expected: ExpectedToken) -> bool {
        let is_present = self.check_noexpect(tok);
        if !is_present {
            self.push_expected(expected);
        }
        is_present
    }

    fn expected_one_of_not_found(&mut self, expected: &[Token]) -> Result<Recovered, ParseError> {
        let mut all_expected: std::vec::Vec<ExpectedToken> = expected
            .iter()
            .map(|t| ExpectedToken::Token(*t))
            .chain(self.expected_tokens.iter().cloned())
            .collect();

        all_expected.sort_by_key(|a| a.to_string());
        all_expected.dedup();

        let expected_str = format_expected_list(&all_expected);
        let found_str = self.token.map(token_description).unwrap_or("end of file");

        let msg = format!("expected {}, found {}", expected_str, found_str);
        self.diagnostics.report(self.current_span, msg);

        if self.token.is_none() { Ok(Recovered::Yes) } else { Err(ParseError) }
    }

    pub fn skip_until(&mut self, stop_tokens: &[Token]) -> Recovered {
        while !self.at_eof() {
            if let Some(tok) = self.token
                && stop_tokens.contains(&tok)
            {
                self.bump();
                return Recovered::Yes;
            }
            self.bump();
        }
        Recovered::Yes
    }

    pub fn skip_until_before(&mut self, stop_tokens: &[Token]) -> Recovered {
        while !self.at_eof() {
            if let Some(tok) = self.token
                && stop_tokens.contains(&tok)
            {
                return Recovered::Yes;
            }
            self.bump();
        }
        Recovered::Yes
    }

    pub fn recover_closing_delimiter(
        &mut self,
        close: Token,
        open_span: SourceSpan,
    ) -> Result<Recovered, ParseError> {
        if self.eat(close) {
            return Ok(Recovered::No);
        }

        if self.at_eof() {
            let msg = format!("unclosed delimiter: expected {}", token_description(close));
            self.diagnostics.report_with_span_note(
                self.current_span,
                &msg,
                open_span,
                "opening delimiter here",
            );
            return Ok(Recovered::Yes);
        }

        self.expected_one_of_not_found(&[close])
    }

    pub fn is_at_recovery_point(&self) -> bool {
        matches!(
            self.token,
            Some(
                Token::RightCurly
                    | Token::RightRound
                    | Token::RightSquare
                    | Token::Semicolon
                    | Token::Comma
            )
        ) || self.at_eof()
    }

    pub fn at_eof(&self) -> bool {
        self.token.is_none()
    }

    pub fn peek_token(&mut self) -> Option<Token> {
        self.tokens.peek().map(|(t, _)| *t)
    }

    pub fn slice(&self, span: SourceSpan) -> &'src str {
        &self.source[span.start as usize..span.end as usize]
    }

    pub fn current_slice(&self) -> &'src str {
        self.slice(self.current_span)
    }

    fn parse_next_decl(&mut self) -> Result<Option<Declaration<'ast>>, ParseError> {
        if self.at_eof() {
            return Ok(None);
        }

        if self.check_noexpect(Token::Init) {
            self.parse_init_decl().map(Some)
        } else if self.check_noexpect(Token::Run) {
            self.parse_run_decl().map(Some)
        } else if self.check_noexpect(Token::Const) {
            self.parse_const_def().map(Some)
        } else {
            self.push_expected(ExpectedToken::Token(Token::Init));
            self.push_expected(ExpectedToken::Token(Token::Run));
            self.push_expected(ExpectedToken::Token(Token::Const));
            Err(self.unexpected_token())
        }
    }

    pub fn parse_init_decl(&mut self) -> Result<Declaration<'ast>, ParseError> {
        let lo = self.current_span;
        self.expect(Token::Init)?;
        let block = self.parse_block()?;
        let span = lo.to(self.prev_span);
        Ok(Declaration { span, kind: DeclarationKind::Init(block) })
    }

    pub fn parse_run_decl(&mut self) -> Result<Declaration<'ast>, ParseError> {
        let lo = self.current_span;
        self.expect(Token::Run)?;
        let block = self.parse_block()?;
        let span = lo.to(self.prev_span);
        Ok(Declaration { span, kind: DeclarationKind::Run(block) })
    }

    pub fn parse_const_def(&mut self) -> Result<Declaration<'ast>, ParseError> {
        let lo = self.current_span;
        self.expect(Token::Const)?;
        let ident = self.parse_ident()?.inner;
        let r#type = if self.eat(Token::Colon) { Some(self.parse_expr()?) } else { None };
        self.expect(Token::Equals)?;
        let expr = self.parse_expr()?;
        self.expect(Token::Semicolon)?;
        let span = lo.to(self.prev_span);
        Ok(Declaration {
            span,
            kind: DeclarationKind::ConstDef(ConstDef { span, ident, r#type, expr }),
        })
    }

    pub fn parse_ident(&mut self) -> Result<Ident, ParseError> {
        if self.check_with(Token::Identifier, ExpectedToken::Ident) {
            let span = self.current_span;
            let text = self.current_slice();
            let istr = self.interner.intern(text);
            self.bump();
            Ok(Ident::new(span, istr))
        } else {
            Err(self.unexpected_token())
        }
    }

    pub fn parse_bool_literal(&mut self) -> Result<Spanned<bool>, ParseError> {
        let value = if self.check_noexpect(Token::True) {
            true
        } else if self.check_noexpect(Token::False) {
            false
        } else {
            self.push_expected(ExpectedToken::Literal);
            return Err(self.unexpected_token());
        };
        let span = self.current_span;
        self.bump();
        Ok(Spanned::new(span, value))
    }

    pub fn parse_int_literal(&mut self) -> Result<Spanned<IntLiteral<'ast>>, ParseError> {
        let span = self.current_span;
        let text = self.current_slice();

        let (positive, num) = if self.check_noexpect(Token::DecLiteral) {
            let (positive, digits) = strip_sign(text);
            let num = FrozenBigUint::from_radix10_in(digits, self.arena);
            (positive, num)
        } else if self.check_noexpect(Token::HexLiteral) {
            let (positive, digits) = strip_sign(text);
            let digits = &digits[2..];
            let num = FrozenBigUint::from_radix16_in(digits, self.arena);
            (positive, num)
        } else if self.check_noexpect(Token::BinLiteral) {
            let (positive, digits) = strip_sign(text);
            let digits = &digits[2..];
            let num = FrozenBigUint::from_radix2_in(digits, self.arena);
            (positive, num)
        } else {
            self.push_expected(ExpectedToken::Literal);
            return Err(self.unexpected_token());
        };

        self.bump();
        Ok(Spanned::new(span, IntLiteral { span, positive, num }))
    }

    pub fn parse_name_path(&mut self) -> Result<NamePath<'ast>, ParseError> {
        let mut path_segments = std::vec::Vec::new();

        let first = self.parse_ident()?;
        let lo = first.span;
        path_segments.push(first.inner);

        while self.eat(Token::Dot) {
            let segment = self.parse_ident()?;
            path_segments.push(segment.inner);
        }

        let span = lo.to(self.prev_span);
        let segments = self.arena.alloc_slice_copy(&path_segments);
        Ok(NamePath { span, segments })
    }

    pub fn parse_primary_expr(&mut self) -> Result<Expr<'ast>, ParseError> {
        if self.check_noexpect(Token::Identifier) {
            let ident = self.parse_ident()?;
            Ok(Expr { span: ident.span, kind: ExprKind::Ident(ident.inner) })
        } else if self.check_noexpect(Token::True) || self.check_noexpect(Token::False) {
            let bool_lit = self.parse_bool_literal()?;
            Ok(Expr { span: bool_lit.span, kind: ExprKind::BoolLiteral(bool_lit.inner) })
        } else if self.check_noexpect(Token::DecLiteral)
            || self.check_noexpect(Token::HexLiteral)
            || self.check_noexpect(Token::BinLiteral)
        {
            let int_lit = self.parse_int_literal()?;
            Ok(Expr { span: int_lit.span, kind: ExprKind::IntLiteral(int_lit.inner) })
        } else {
            self.push_expected(ExpectedToken::Expr);
            Err(self.unexpected_token())
        }
    }

    pub fn parse_postfix_expr(&mut self) -> Result<Expr<'ast>, ParseError> {
        let mut expr = self.parse_primary_expr()?;
        let lo = expr.span;

        loop {
            if self.eat(Token::Dot) {
                let ident = self.parse_ident()?;
                let span = lo.to(ident.span);
                let member = Member { span, expr: self.arena.alloc(expr), ident: ident.inner };
                expr = Expr { span, kind: ExprKind::Member(member) };
            } else if self.check_noexpect(Token::LeftRound) {
                let (args, _recovered) =
                    self.parse_comma_separated(Token::LeftRound, Token::RightRound, |p| {
                        p.parse_postfix_expr()
                    })?;

                let span = lo.to(self.prev_span);
                let param_exprs = self.arena.alloc_slice_fill_iter(args);
                let call = FnCall { span, fn_expr: self.arena.alloc(expr), param_exprs };
                expr = Expr { span, kind: ExprKind::FnCall(call) };
            } else {
                break;
            }
        }

        Ok(expr)
    }

    pub fn parse_comma_separated<T>(
        &mut self,
        open: Token,
        close: Token,
        mut parse_element: impl FnMut(&mut Self) -> Result<T, ParseError>,
    ) -> Result<(std::vec::Vec<T>, Recovered), ParseError> {
        let open_span = self.current_span;
        self.expect(open)?;

        let mut items = std::vec::Vec::new();

        if self.check_noexpect(close) {
            self.bump();
            return Ok((items, Recovered::No));
        }

        items.push(parse_element(self)?);

        loop {
            if self.check_noexpect(close) {
                self.bump();
                return Ok((items, Recovered::No));
            }

            if self.at_eof() {
                let msg = format!("unclosed delimiter: expected {}", token_description(close));
                self.diagnostics.report_with_span_note(
                    self.current_span,
                    &msg,
                    open_span,
                    "opening delimiter here",
                );
                return Ok((items, Recovered::Yes));
            }

            match self.expect(Token::Comma) {
                Ok(Recovered::Yes) => return Ok((items, Recovered::Yes)),
                Ok(Recovered::No) => {}
                Err(e) => return Err(e),
            }

            if self.check_noexpect(close) {
                self.bump();
                return Ok((items, Recovered::No));
            }

            if self.at_eof() {
                let msg = format!("unclosed delimiter: expected {}", token_description(close));
                self.diagnostics.report_with_span_note(
                    self.current_span,
                    &msg,
                    open_span,
                    "opening delimiter here",
                );
                return Ok((items, Recovered::Yes));
            }

            items.push(parse_element(self)?);
        }
    }

    pub fn parse_field_def(&mut self) -> Result<FieldDef<'ast>, ParseError> {
        let ident = self.parse_ident()?;
        let lo = ident.span;
        self.expect(Token::Colon)?;
        let r#type = self.parse_primary_expr()?;
        let span = lo.to(r#type.span);
        Ok(FieldDef { span, name: ident.inner, r#type })
    }

    pub fn parse_field_init(&mut self) -> Result<FieldInit<'ast>, ParseError> {
        let ident = self.parse_ident()?;
        let lo = ident.span;
        self.expect(Token::Colon)?;
        let value = self.parse_postfix_expr()?;
        let span = lo.to(value.span);
        Ok(FieldInit { span, name: ident.inner, value })
    }

    pub fn parse_struct_literal(&mut self) -> Result<StructLiteral<'ast>, ParseError> {
        let type_path = self.parse_name_path()?;
        let lo = type_path.span;

        let (fields, _recovered) =
            self.parse_comma_separated(Token::LeftCurly, Token::RightCurly, |p| {
                p.parse_field_init()
            })?;

        let span = lo.to(self.prev_span);
        let fields = self.arena.alloc_slice_fill_iter(fields);
        Ok(StructLiteral { span, type_path, fields })
    }

    pub fn parse_struct_def(&mut self) -> Result<StructDef<'ast>, ParseError> {
        let lo = self.current_span;
        self.expect(Token::Struct)?;

        let (fields, _recovered) =
            self.parse_comma_separated(Token::LeftCurly, Token::RightCurly, |p| {
                p.parse_field_def()
            })?;

        let span = lo.to(self.prev_span);
        let fields = self.arena.alloc_slice_fill_iter(fields);
        Ok(StructDef { span, fields })
    }

    pub fn parse_param_def(&mut self) -> Result<ParamDef<'ast>, ParseError> {
        let lo = self.current_span;
        let comptime = self.eat(Token::Comptime);
        let lo = if comptime { lo } else { self.current_span };
        let name = self.parse_ident()?.inner;
        self.expect(Token::Colon)?;
        let r#type = self.parse_primary_expr()?;
        let span = lo.to(r#type.span);
        Ok(ParamDef { span, comptime, name, r#type })
    }

    pub fn parse_fn_def(&mut self) -> Result<FnDef<'ast>, ParseError> {
        let lo = self.current_span;
        self.expect(Token::Fn)?;

        let (params, _recovered) =
            self.parse_comma_separated(Token::LeftRound, Token::RightRound, |p| {
                p.parse_param_def()
            })?;

        let result =
            if self.eat(Token::ThinArrow) { Some(self.parse_primary_expr()?) } else { None };

        let body = self.parse_block()?;

        let span = lo.to(self.prev_span);
        let params = self.arena.alloc_slice_fill_iter(params);
        Ok(FnDef { span, params, result, body })
    }

    pub fn parse_type_def(&mut self) -> Result<TypeDef<'ast>, ParseError> {
        if self.check_noexpect(Token::Fn) {
            let fn_def = self.parse_fn_def()?;
            Ok(TypeDef::FnDef(self.arena.alloc(fn_def)))
        } else if self.check_noexpect(Token::Struct) {
            let struct_def = self.parse_struct_def()?;
            Ok(TypeDef::StructDef(struct_def))
        } else {
            self.push_expected(ExpectedToken::Token(Token::Fn));
            self.push_expected(ExpectedToken::Token(Token::Struct));
            Err(self.unexpected_token())
        }
    }

    pub fn parse_block(&mut self) -> Result<Block<'ast>, ParseError> {
        let open_span = self.current_span;
        self.expect(Token::LeftCurly)?;

        let mut statements = std::vec::Vec::new();
        let mut last_expr: Option<Expr<'ast>> = None;

        loop {
            if self.check_noexpect(Token::RightCurly) {
                self.bump();
                break;
            }

            if self.at_eof() {
                let msg = "unclosed delimiter: expected `}`";
                self.diagnostics.report_with_span_note(
                    self.current_span,
                    msg,
                    open_span,
                    "opening delimiter here",
                );
                break;
            }

            if self.is_stmt_start() {
                let stmt = self.parse_stmt()?;
                statements.push(stmt);
            } else if self.can_start_expr() {
                let expr = self.parse_primary_expr()?;

                if self.eat(Token::Semicolon) {
                    let stmt_span = expr.span.to(self.prev_span);
                    statements.push(Statement { span: stmt_span, kind: StatementKind::Expr(expr) });
                } else if self.check_noexpect(Token::RightCurly) || self.at_eof() {
                    last_expr = Some(expr);
                } else {
                    self.push_expected(ExpectedToken::Token(Token::Semicolon));
                    self.push_expected(ExpectedToken::Token(Token::RightCurly));
                    return Err(self.unexpected_token());
                }
            } else {
                self.push_expected(ExpectedToken::Token(Token::RightCurly));
                self.push_expected(ExpectedToken::Expr);
                return Err(self.unexpected_token());
            }
        }

        let span = open_span.to(self.prev_span);
        let statements = self.arena.alloc_slice_fill_iter(statements);
        let last_expr = last_expr.map(|e| self.arena.alloc(e) as &mut _);

        Ok(Block { span, statements, last_expr })
    }

    pub fn parse_comptime_block(&mut self) -> Result<Expr<'ast>, ParseError> {
        let lo = self.current_span;
        self.expect(Token::Comptime)?;
        let block = self.parse_block()?;
        let span = lo.to(self.prev_span);
        Ok(Expr { span, kind: ExprKind::Comptime(block) })
    }

    pub fn parse_return_stmt(&mut self) -> Result<Statement<'ast>, ParseError> {
        let lo = self.current_span;
        self.expect(Token::Return)?;
        let expr = self.parse_expr()?;
        self.expect(Token::Semicolon)?;
        let span = lo.to(self.prev_span);
        Ok(Statement { span, kind: StatementKind::Return(expr) })
    }

    pub fn parse_let_stmt(&mut self) -> Result<Statement<'ast>, ParseError> {
        let lo = self.current_span;
        self.expect(Token::Let)?;

        let mutable = self.eat(Token::Mut);
        let ident = self.parse_ident()?.inner;

        let r#type = if self.eat(Token::Colon) { Some(self.parse_expr()?) } else { None };

        self.expect(Token::Equals)?;
        let value = self.parse_expr()?;
        self.expect(Token::Semicolon)?;

        let span = lo.to(self.prev_span);
        let let_stmt = LetStmt { span, mutable, ident, r#type, value };
        Ok(Statement { span, kind: StatementKind::Let(self.arena.alloc(let_stmt)) })
    }

    pub fn parse_assign_stmt(&mut self) -> Result<Statement<'ast>, ParseError> {
        let target = self.parse_name_path()?;
        let lo = target.span;
        self.expect(Token::Equals)?;
        let value = self.parse_expr()?;
        self.expect(Token::Semicolon)?;

        let span = lo.to(self.prev_span);
        let assign_stmt = AssignStmt { span, target, op: AssignOp::Assign, value };
        Ok(Statement { span, kind: StatementKind::Assign(self.arena.alloc(assign_stmt)) })
    }

    fn parse_assign_or_expr_stmt(&mut self) -> Result<Statement<'ast>, ParseError> {
        let first_ident = self.parse_ident()?;
        let lo = first_ident.span;
        let mut path_segments = std::vec::Vec::new();
        path_segments.push(first_ident.inner);

        while self.eat(Token::Dot) {
            if self.check_noexpect(Token::Identifier) {
                let segment = self.parse_ident()?;
                path_segments.push(segment.inner);
            } else {
                self.push_expected(ExpectedToken::Ident);
                return Err(self.unexpected_token());
            }
        }

        if self.eat(Token::Equals) {
            let path_span = lo.to(self.prev_span);
            let target =
                NamePath { span: path_span, segments: self.arena.alloc_slice_copy(&path_segments) };
            let value = self.parse_expr()?;
            self.expect(Token::Semicolon)?;

            let span = lo.to(self.prev_span);
            let assign_stmt = AssignStmt { span, target, op: AssignOp::Assign, value };
            Ok(Statement { span, kind: StatementKind::Assign(self.arena.alloc(assign_stmt)) })
        } else {
            let mut expr = Expr { span: first_ident.span, kind: ExprKind::Ident(path_segments[0]) };
            for &segment in &path_segments[1..] {
                let span = lo.to(self.prev_span);
                let member = Member { span, expr: self.arena.alloc(expr), ident: segment };
                expr = Expr { span, kind: ExprKind::Member(member) };
            }

            loop {
                if self.eat(Token::Dot) {
                    let ident = self.parse_ident()?;
                    let span = lo.to(ident.span);
                    let member = Member { span, expr: self.arena.alloc(expr), ident: ident.inner };
                    expr = Expr { span, kind: ExprKind::Member(member) };
                } else if self.check_noexpect(Token::LeftRound) {
                    let (args, _recovered) =
                        self.parse_comma_separated(Token::LeftRound, Token::RightRound, |p| {
                            p.parse_postfix_expr()
                        })?;

                    let span = lo.to(self.prev_span);
                    let param_exprs = self.arena.alloc_slice_fill_iter(args);
                    let call = FnCall { span, fn_expr: self.arena.alloc(expr), param_exprs };
                    expr = Expr { span, kind: ExprKind::FnCall(call) };
                } else {
                    break;
                }
            }

            self.expect(Token::Semicolon)?;
            let span = lo.to(self.prev_span);
            Ok(Statement { span, kind: StatementKind::Expr(expr) })
        }
    }

    pub fn parse_cond_expr(&mut self) -> Result<Expr<'ast>, ParseError> {
        let lo = self.current_span;
        self.expect(Token::If)?;

        let condition = self.parse_postfix_expr()?;
        let body = self.parse_block()?;
        let if_span = lo.to(body.span);
        let r#if = IfBranch { span: if_span, condition, body };

        let mut else_ifs = std::vec::Vec::new();

        loop {
            if !self.eat(Token::Else) {
                self.diagnostics
                    .report(self.current_span, "conditional expression requires an `else` branch");
                let dummy_span = self.current_span;
                let else_body = MaybeOr::Just(Block {
                    span: dummy_span,
                    statements: self.arena.alloc_slice_fill_iter(std::iter::empty()),
                    last_expr: None,
                });
                let span = lo.to(self.prev_span);
                let else_ifs = self.arena.alloc_slice_fill_iter(else_ifs);
                let cond = Conditional { span, r#if, else_ifs, else_body };
                return Ok(Expr { span, kind: ExprKind::Conditional(self.arena.alloc(cond)) });
            }

            if self.eat(Token::If) {
                let else_if_lo = self.prev_span;
                let condition = self.parse_postfix_expr()?;
                let body = self.parse_block()?;
                let else_if_span = else_if_lo.to(body.span);
                else_ifs.push(IfBranch { span: else_if_span, condition, body });
            } else {
                let else_block = self.parse_block()?;
                let else_body = MaybeOr::Just(else_block);
                let span = lo.to(self.prev_span);
                let else_ifs = self.arena.alloc_slice_fill_iter(else_ifs);
                let cond = Conditional { span, r#if, else_ifs, else_body };
                return Ok(Expr { span, kind: ExprKind::Conditional(self.arena.alloc(cond)) });
            }
        }
    }

    pub fn parse_expr(&mut self) -> Result<Expr<'ast>, ParseError> {
        if self.check_noexpect(Token::Comptime) {
            self.parse_comptime_block()
        } else if self.check_noexpect(Token::If) {
            self.parse_cond_expr()
        } else if self.check_noexpect(Token::LeftCurly) {
            let block = self.parse_block()?;
            let span = block.span;
            Ok(Expr { span, kind: ExprKind::Block(block) })
        } else {
            self.parse_expr_no_block()
        }
    }

    pub fn parse_expr_no_block(&mut self) -> Result<Expr<'ast>, ParseError> {
        if self.check_noexpect(Token::Fn) || self.check_noexpect(Token::Struct) {
            let type_def = self.parse_type_def()?;
            let span = type_def.span();
            Ok(Expr { span, kind: ExprKind::TypeDef(type_def) })
        } else if self.check_noexpect(Token::Identifier)
            && self.peek_token() == Some(Token::LeftCurly)
        {
            let struct_lit = self.parse_struct_literal()?;
            let span = struct_lit.span;
            Ok(Expr { span, kind: ExprKind::StructLiteral(self.arena.alloc(struct_lit)) })
        } else if self.check_noexpect(Token::Identifier) && self.peek_token() == Some(Token::Dot) {
            self.parse_struct_literal_or_postfix()
        } else {
            self.parse_postfix_expr()
        }
    }

    fn parse_struct_literal_or_postfix(&mut self) -> Result<Expr<'ast>, ParseError> {
        let first_ident = self.parse_ident()?;
        let lo = first_ident.span;

        let mut path_segments = std::vec::Vec::new();
        path_segments.push(first_ident.inner);

        while self.eat(Token::Dot) {
            if self.check_noexpect(Token::Identifier) {
                let segment = self.parse_ident()?;
                path_segments.push(segment.inner);

                if self.check_noexpect(Token::LeftCurly) {
                    let path_span = lo.to(segment.span);
                    let type_path = NamePath {
                        span: path_span,
                        segments: self.arena.alloc_slice_copy(&path_segments),
                    };

                    let (fields, _recovered) =
                        self.parse_comma_separated(Token::LeftCurly, Token::RightCurly, |p| {
                            p.parse_field_init()
                        })?;

                    let span = lo.to(self.prev_span);
                    let fields = self.arena.alloc_slice_fill_iter(fields);
                    let struct_lit = StructLiteral { span, type_path, fields };
                    return Ok(Expr {
                        span,
                        kind: ExprKind::StructLiteral(self.arena.alloc(struct_lit)),
                    });
                }
            } else {
                self.push_expected(ExpectedToken::Ident);
                return Err(self.unexpected_token());
            }
        }

        let mut expr = Expr { span: first_ident.span, kind: ExprKind::Ident(path_segments[0]) };
        for &segment in &path_segments[1..] {
            let span = lo.to(self.prev_span);
            let member = Member { span, expr: self.arena.alloc(expr), ident: segment };
            expr = Expr { span, kind: ExprKind::Member(member) };
        }

        loop {
            if self.eat(Token::Dot) {
                let ident = self.parse_ident()?;
                let span = lo.to(ident.span);
                let member = Member { span, expr: self.arena.alloc(expr), ident: ident.inner };
                expr = Expr { span, kind: ExprKind::Member(member) };
            } else if self.check_noexpect(Token::LeftRound) {
                let (args, _recovered) =
                    self.parse_comma_separated(Token::LeftRound, Token::RightRound, |p| {
                        p.parse_postfix_expr()
                    })?;

                let span = lo.to(self.prev_span);
                let param_exprs = self.arena.alloc_slice_fill_iter(args);
                let call = FnCall { span, fn_expr: self.arena.alloc(expr), param_exprs };
                expr = Expr { span, kind: ExprKind::FnCall(call) };
            } else {
                break;
            }
        }

        Ok(expr)
    }

    fn is_stmt_start(&self) -> bool {
        matches!(
            self.token,
            Some(
                Token::Let
                    | Token::Return
                    | Token::If
                    | Token::LeftCurly
                    | Token::Inline
                    | Token::While
            )
        )
    }

    fn can_start_expr(&self) -> bool {
        matches!(
            self.token,
            Some(
                Token::Identifier
                    | Token::True
                    | Token::False
                    | Token::DecLiteral
                    | Token::HexLiteral
                    | Token::BinLiteral
            )
        )
    }

    fn can_start_expr_no_block(&self) -> bool {
        matches!(
            self.token,
            Some(
                Token::True
                    | Token::False
                    | Token::DecLiteral
                    | Token::HexLiteral
                    | Token::BinLiteral
                    | Token::Fn
                    | Token::Struct
            )
        )
    }

    pub fn parse_stmt(&mut self) -> Result<Statement<'ast>, ParseError> {
        if self.check_noexpect(Token::Let) {
            self.parse_let_stmt()
        } else if self.check_noexpect(Token::Return) {
            self.parse_return_stmt()
        } else if self.check_noexpect(Token::If) {
            self.parse_cond_stmt()
        } else if self.check_noexpect(Token::LeftCurly) {
            self.parse_block_stmt()
        } else if self.check_noexpect(Token::Inline) || self.check_noexpect(Token::While) {
            self.parse_while_stmt()
        } else if self.check_noexpect(Token::Identifier) {
            self.parse_assign_or_expr_stmt()
        } else if self.can_start_expr_no_block() {
            self.parse_expr_stmt()
        } else {
            self.push_expected(ExpectedToken::Token(Token::Let));
            self.push_expected(ExpectedToken::Token(Token::Return));
            self.push_expected(ExpectedToken::Token(Token::If));
            self.push_expected(ExpectedToken::Token(Token::LeftCurly));
            self.push_expected(ExpectedToken::Token(Token::While));
            self.push_expected(ExpectedToken::Expr);
            Err(self.unexpected_token())
        }
    }

    pub fn parse_expr_stmt(&mut self) -> Result<Statement<'ast>, ParseError> {
        let expr = self.parse_expr_no_block()?;
        let lo = expr.span;
        self.expect(Token::Semicolon)?;
        let span = lo.to(self.prev_span);
        Ok(Statement { span, kind: StatementKind::Expr(expr) })
    }

    pub fn parse_block_stmt(&mut self) -> Result<Statement<'ast>, ParseError> {
        let block = self.parse_block()?;
        let span = block.span;
        self.eat(Token::Semicolon);
        Ok(Statement { span, kind: StatementKind::Block(block) })
    }

    pub fn parse_while_stmt(&mut self) -> Result<Statement<'ast>, ParseError> {
        let lo = self.current_span;
        let inline = self.eat(Token::Inline);
        self.expect(Token::While)?;
        let condition = self.parse_postfix_expr()?;
        let body = self.parse_block()?;
        let span = lo.to(self.prev_span);
        let while_stmt = WhileStmt { span, inline, condition, body };
        Ok(Statement { span, kind: StatementKind::While(self.arena.alloc(while_stmt)) })
    }

    pub fn parse_cond_stmt(&mut self) -> Result<Statement<'ast>, ParseError> {
        let lo = self.current_span;
        self.expect(Token::If)?;

        let condition = self.parse_postfix_expr()?;
        let body = self.parse_block()?;
        let if_span = lo.to(body.span);
        let r#if = IfBranch { span: if_span, condition, body };

        let mut else_ifs = std::vec::Vec::new();

        loop {
            if !self.eat(Token::Else) {
                let span = lo.to(self.prev_span);
                let else_body = MaybeOr::Other(());
                let else_ifs = self.arena.alloc_slice_fill_iter(else_ifs);
                let cond = Conditional { span, r#if, else_ifs, else_body };
                return Ok(Statement {
                    span,
                    kind: StatementKind::Conditional(self.arena.alloc(cond)),
                });
            }

            if self.eat(Token::If) {
                let else_if_lo = self.prev_span;
                let condition = self.parse_postfix_expr()?;
                let body = self.parse_block()?;
                let else_if_span = else_if_lo.to(body.span);
                else_ifs.push(IfBranch { span: else_if_span, condition, body });
            } else {
                let else_block = self.parse_block()?;
                let else_body = MaybeOr::Just(else_block);
                let span = lo.to(self.prev_span);
                let else_ifs = self.arena.alloc_slice_fill_iter(else_ifs);
                let cond = Conditional { span, r#if, else_ifs, else_body };
                return Ok(Statement {
                    span,
                    kind: StatementKind::Conditional(self.arena.alloc(cond)),
                });
            }
        }
    }

    pub fn parse_comma_separated_until<T>(
        &mut self,
        stop: Token,
        mut parse_element: impl FnMut(&mut Self) -> Result<T, ParseError>,
    ) -> Result<(std::vec::Vec<T>, Recovered), ParseError> {
        let mut items = std::vec::Vec::new();

        if self.check_noexpect(stop) {
            return Ok((items, Recovered::No));
        }

        items.push(parse_element(self)?);

        loop {
            if self.check_noexpect(stop) {
                return Ok((items, Recovered::No));
            }

            if self.at_eof() {
                return Ok((items, Recovered::Yes));
            }

            match self.expect(Token::Comma) {
                Ok(Recovered::Yes) => return Ok((items, Recovered::Yes)),
                Ok(Recovered::No) => {}
                Err(e) => return Err(e),
            }

            if self.check_noexpect(stop) {
                return Ok((items, Recovered::No));
            }

            if self.at_eof() {
                return Ok((items, Recovered::Yes));
            }

            items.push(parse_element(self)?);
        }
    }
}

fn strip_sign(s: &str) -> (bool, &str) {
    if let Some(rest) = s.strip_prefix('-') { (false, rest) } else { (true, s) }
}

fn format_expected_list(expected: &[ExpectedToken]) -> String {
    match expected.len() {
        0 => "nothing".to_string(),
        1 => expected[0].to_string(),
        2 => format!("{} or {}", expected[0], expected[1]),
        _ => {
            let (last, rest) = expected.split_last().unwrap();
            let rest_str: std::vec::Vec<_> = rest.iter().map(|e| e.to_string()).collect();
            format!("{}, or {}", rest_str.join(", "), last)
        }
    }
}

pub fn parse<'ast, 'src: 'ast>(
    source: &'src str,
    arena: &'ast Bump,
) -> Result<Ast<'ast>, ParseError> {
    let mut declarations = Vec::with_capacity_in(estimate_declaration_count(source), arena);

    let mut parser = Parser::new(source, arena);

    while let Some(decl) = parser.parse_next_decl()? {
        declarations.push(decl);
    }

    Ok(Ast { declarations })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_ident_simple() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo", &arena);

        let ident = parser.parse_ident().unwrap();
        assert_eq!(ident.span, Span::new(0, 3));
        assert_eq!(parser.interner.resolve(ident.inner), "foo");
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_ident_advances_token() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo bar", &arena);

        let ident1 = parser.parse_ident().unwrap();
        assert_eq!(parser.interner.resolve(ident1.inner), "foo");
        assert!(!parser.at_eof());

        let ident2 = parser.parse_ident().unwrap();
        assert_eq!(parser.interner.resolve(ident2.inner), "bar");
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_ident_fails_on_keyword() {
        let arena = Bump::new();
        let mut parser = Parser::new("if", &arena);

        let result = parser.parse_ident();
        assert!(result.is_err());
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_ident_fails_on_literal() {
        let arena = Bump::new();
        let mut parser = Parser::new("123", &arena);

        let result = parser.parse_ident();
        assert!(result.is_err());
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_bool_literal_true() {
        let arena = Bump::new();
        let mut parser = Parser::new("true", &arena);

        let result = parser.parse_bool_literal().unwrap();
        assert!(result.inner);
        assert_eq!(result.span, Span::new(0, 4));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_bool_literal_false() {
        let arena = Bump::new();
        let mut parser = Parser::new("false", &arena);

        let result = parser.parse_bool_literal().unwrap();
        assert!(!result.inner);
        assert_eq!(result.span, Span::new(0, 5));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_bool_literal_fails_on_ident() {
        let arena = Bump::new();
        let mut parser = Parser::new("truthy", &arena);

        let result = parser.parse_bool_literal();
        assert!(result.is_err());
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_bool_literal_advances() {
        let arena = Bump::new();
        let mut parser = Parser::new("true false", &arena);

        let first = parser.parse_bool_literal().unwrap();
        assert!(first.inner);

        let second = parser.parse_bool_literal().unwrap();
        assert!(!second.inner);
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_int_literal_decimal() {
        let arena = Bump::new();
        let mut parser = Parser::new("12345", &arena);

        let result = parser.parse_int_literal().unwrap();
        assert!(result.inner.positive);
        assert_eq!(format!("{:x}", result.inner.num), "3039");
        assert_eq!(result.span, Span::new(0, 5));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_int_literal_decimal_negative() {
        let arena = Bump::new();
        let mut parser = Parser::new("-42", &arena);

        let result = parser.parse_int_literal().unwrap();
        assert!(!result.inner.positive);
        assert_eq!(format!("{:x}", result.inner.num), "2a");
        assert_eq!(result.span, Span::new(0, 3));
    }

    #[test]
    fn test_parse_int_literal_decimal_with_underscores() {
        let arena = Bump::new();
        let mut parser = Parser::new("1_000_000", &arena);

        let result = parser.parse_int_literal().unwrap();
        assert!(result.inner.positive);
        assert_eq!(format!("{:x}", result.inner.num), "f4240");
    }

    #[test]
    fn test_parse_int_literal_hex() {
        let arena = Bump::new();
        let mut parser = Parser::new("0xDEAD", &arena);

        let result = parser.parse_int_literal().unwrap();
        assert!(result.inner.positive);
        assert_eq!(format!("{:x}", result.inner.num), "dead");
        assert_eq!(result.span, Span::new(0, 6));
    }

    #[test]
    fn test_parse_int_literal_hex_negative() {
        let arena = Bump::new();
        let mut parser = Parser::new("-0xBEEF", &arena);

        let result = parser.parse_int_literal().unwrap();
        assert!(!result.inner.positive);
        assert_eq!(format!("{:x}", result.inner.num), "beef");
    }

    #[test]
    fn test_parse_int_literal_binary() {
        let arena = Bump::new();
        let mut parser = Parser::new("0b1010", &arena);

        let result = parser.parse_int_literal().unwrap();
        assert!(result.inner.positive);
        assert_eq!(format!("{:x}", result.inner.num), "a");
        assert_eq!(result.span, Span::new(0, 6));
    }

    #[test]
    fn test_parse_int_literal_binary_negative() {
        let arena = Bump::new();
        let mut parser = Parser::new("-0b1111", &arena);

        let result = parser.parse_int_literal().unwrap();
        assert!(!result.inner.positive);
        assert_eq!(format!("{:x}", result.inner.num), "f");
    }

    #[test]
    fn test_parse_int_literal_fails_on_identifier() {
        let arena = Bump::new();
        let mut parser = Parser::new("abc", &arena);

        let result = parser.parse_int_literal();
        assert!(result.is_err());
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_name_path_single() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo", &arena);

        let result = parser.parse_name_path().unwrap();
        assert_eq!(result.segments.len(), 1);
        assert_eq!(parser.interner.resolve(result.segments[0]), "foo");
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_name_path_two_segments() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo.bar", &arena);

        let result = parser.parse_name_path().unwrap();
        assert_eq!(result.segments.len(), 2);
        assert_eq!(parser.interner.resolve(result.segments[0]), "foo");
        assert_eq!(parser.interner.resolve(result.segments[1]), "bar");
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_name_path_three_segments() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo.bar.baz", &arena);

        let result = parser.parse_name_path().unwrap();
        assert_eq!(result.segments.len(), 3);
        assert_eq!(parser.interner.resolve(result.segments[0]), "foo");
        assert_eq!(parser.interner.resolve(result.segments[1]), "bar");
        assert_eq!(parser.interner.resolve(result.segments[2]), "baz");
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_name_path_stops_at_non_ident() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo.bar + baz", &arena);

        let result = parser.parse_name_path().unwrap();
        assert_eq!(result.segments.len(), 2);
        assert_eq!(parser.interner.resolve(result.segments[0]), "foo");
        assert_eq!(parser.interner.resolve(result.segments[1]), "bar");
        assert_eq!(parser.token, Some(Token::Plus));
    }

    #[test]
    fn test_parse_name_path_fails_on_non_ident() {
        let arena = Bump::new();
        let mut parser = Parser::new("123", &arena);

        let result = parser.parse_name_path();
        assert!(result.is_err());
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_name_path_trailing_dot_with_following_token() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo.bar.+", &arena);

        let result = parser.parse_name_path();
        assert!(result.is_err());
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_primary_expr_ident() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo", &arena);

        let result = parser.parse_primary_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::Ident(_)));
        if let ExprKind::Ident(istr) = result.kind {
            assert_eq!(parser.interner.resolve(istr), "foo");
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_primary_expr_bool_true() {
        let arena = Bump::new();
        let mut parser = Parser::new("true", &arena);

        let result = parser.parse_primary_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::BoolLiteral(true)));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_primary_expr_bool_false() {
        let arena = Bump::new();
        let mut parser = Parser::new("false", &arena);

        let result = parser.parse_primary_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::BoolLiteral(false)));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_primary_expr_int_decimal() {
        let arena = Bump::new();
        let mut parser = Parser::new("42", &arena);

        let result = parser.parse_primary_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::IntLiteral(_)));
        if let ExprKind::IntLiteral(lit) = result.kind {
            assert!(lit.positive);
            assert_eq!(format!("{:x}", lit.num), "2a");
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_primary_expr_int_hex() {
        let arena = Bump::new();
        let mut parser = Parser::new("0xDEAD", &arena);

        let result = parser.parse_primary_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::IntLiteral(_)));
        if let ExprKind::IntLiteral(lit) = result.kind {
            assert!(lit.positive);
            assert_eq!(format!("{:x}", lit.num), "dead");
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_primary_expr_int_binary() {
        let arena = Bump::new();
        let mut parser = Parser::new("0b1010", &arena);

        let result = parser.parse_primary_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::IntLiteral(_)));
        if let ExprKind::IntLiteral(lit) = result.kind {
            assert!(lit.positive);
            assert_eq!(format!("{:x}", lit.num), "a");
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_primary_expr_negative_int() {
        let arena = Bump::new();
        let mut parser = Parser::new("-123", &arena);

        let result = parser.parse_primary_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::IntLiteral(_)));
        if let ExprKind::IntLiteral(lit) = result.kind {
            assert!(!lit.positive);
            assert_eq!(format!("{:x}", lit.num), "7b");
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_primary_expr_fails_on_keyword() {
        let arena = Bump::new();
        let mut parser = Parser::new("if", &arena);

        let result = parser.parse_primary_expr();
        assert!(result.is_err());
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_primary_expr_fails_on_operator() {
        let arena = Bump::new();
        let mut parser = Parser::new("+", &arena);

        let result = parser.parse_primary_expr();
        assert!(result.is_err());
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_postfix_member_simple() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo.bar", &arena);

        let result = parser.parse_postfix_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::Member(_)));
        if let ExprKind::Member(member) = result.kind {
            assert!(matches!(member.expr.kind, ExprKind::Ident(_)));
            assert_eq!(parser.interner.resolve(member.ident), "bar");
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_postfix_member_chained() {
        let arena = Bump::new();
        let mut parser = Parser::new("a.b.c", &arena);

        let result = parser.parse_postfix_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::Member(_)));
        if let ExprKind::Member(outer) = result.kind {
            assert_eq!(parser.interner.resolve(outer.ident), "c");
            assert!(matches!(outer.expr.kind, ExprKind::Member(_)));
            if let ExprKind::Member(ref inner) = outer.expr.kind {
                assert_eq!(parser.interner.resolve(inner.ident), "b");
                assert!(matches!(inner.expr.kind, ExprKind::Ident(_)));
            }
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_postfix_no_postfix() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo", &arena);

        let result = parser.parse_postfix_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::Ident(_)));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_postfix_member_stops_at_operator() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo.bar + baz", &arena);

        let result = parser.parse_postfix_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::Member(_)));
        assert_eq!(parser.token, Some(Token::Plus));
    }

    #[test]
    fn test_parse_postfix_fn_call_no_args() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo()", &arena);

        let result = parser.parse_postfix_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::FnCall(_)));
        if let ExprKind::FnCall(call) = result.kind {
            assert!(matches!(call.fn_expr.kind, ExprKind::Ident(_)));
            assert_eq!(call.param_exprs.len(), 0);
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_postfix_fn_call_single_arg() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo(42)", &arena);

        let result = parser.parse_postfix_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::FnCall(_)));
        if let ExprKind::FnCall(call) = result.kind {
            assert_eq!(call.param_exprs.len(), 1);
            assert!(matches!(call.param_exprs[0].kind, ExprKind::IntLiteral(_)));
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_postfix_fn_call_multiple_args() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo(a, b, c)", &arena);

        let result = parser.parse_postfix_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::FnCall(_)));
        if let ExprKind::FnCall(call) = result.kind {
            assert_eq!(call.param_exprs.len(), 3);
            assert!(matches!(call.param_exprs[0].kind, ExprKind::Ident(_)));
            assert!(matches!(call.param_exprs[1].kind, ExprKind::Ident(_)));
            assert!(matches!(call.param_exprs[2].kind, ExprKind::Ident(_)));
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_postfix_fn_call_trailing_comma() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo(a, b,)", &arena);

        let result = parser.parse_postfix_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::FnCall(_)));
        if let ExprKind::FnCall(call) = result.kind {
            assert_eq!(call.param_exprs.len(), 2);
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_postfix_chained_calls() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo()()", &arena);

        let result = parser.parse_postfix_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::FnCall(_)));
        if let ExprKind::FnCall(outer) = result.kind {
            assert_eq!(outer.param_exprs.len(), 0);
            assert!(matches!(outer.fn_expr.kind, ExprKind::FnCall(_)));
            if let ExprKind::FnCall(ref inner) = outer.fn_expr.kind {
                assert_eq!(inner.param_exprs.len(), 0);
                assert!(matches!(inner.fn_expr.kind, ExprKind::Ident(_)));
            }
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_postfix_member_then_call() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo.bar()", &arena);

        let result = parser.parse_postfix_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::FnCall(_)));
        if let ExprKind::FnCall(call) = result.kind {
            assert_eq!(call.param_exprs.len(), 0);
            assert!(matches!(call.fn_expr.kind, ExprKind::Member(_)));
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_postfix_call_then_member() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo().bar", &arena);

        let result = parser.parse_postfix_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::Member(_)));
        if let ExprKind::Member(member) = result.kind {
            assert_eq!(parser.interner.resolve(member.ident), "bar");
            assert!(matches!(member.expr.kind, ExprKind::FnCall(_)));
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_postfix_complex_chain() {
        let arena = Bump::new();
        let mut parser = Parser::new("a.b(c).d(e, f).g", &arena);

        let result = parser.parse_postfix_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::Member(_)));
        if let ExprKind::Member(member) = result.kind {
            assert_eq!(parser.interner.resolve(member.ident), "g");
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_struct_def_empty() {
        let arena = Bump::new();
        let mut parser = Parser::new("struct {}", &arena);

        let result = parser.parse_struct_def().unwrap();
        assert_eq!(result.fields.len(), 0);
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_struct_def_single_field() {
        let arena = Bump::new();
        let mut parser = Parser::new("struct { x: u32 }", &arena);

        let result = parser.parse_struct_def().unwrap();
        assert_eq!(result.fields.len(), 1);
        assert_eq!(parser.interner.resolve(result.fields[0].name), "x");
        assert!(matches!(result.fields[0].r#type.kind, ExprKind::Ident(_)));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_struct_def_multiple_fields() {
        let arena = Bump::new();
        let mut parser = Parser::new("struct { x: u32, y: u64, z: bool }", &arena);

        let result = parser.parse_struct_def().unwrap();
        assert_eq!(result.fields.len(), 3);
        assert_eq!(parser.interner.resolve(result.fields[0].name), "x");
        assert_eq!(parser.interner.resolve(result.fields[1].name), "y");
        assert_eq!(parser.interner.resolve(result.fields[2].name), "z");
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_struct_def_trailing_comma() {
        let arena = Bump::new();
        let mut parser = Parser::new("struct { x: u32, y: u64, }", &arena);

        let result = parser.parse_struct_def().unwrap();
        assert_eq!(result.fields.len(), 2);
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_stmt_fails_on_invalid_token() {
        let arena = Bump::new();
        let mut parser = Parser::new("+", &arena);

        let result = parser.parse_stmt();
        assert!(result.is_err());
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_stmt_fails_on_eof() {
        let arena = Bump::new();
        let mut parser = Parser::new("", &arena);

        let result = parser.parse_stmt();
        assert!(result.is_err());
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_block_empty() {
        let arena = Bump::new();
        let mut parser = Parser::new("{}", &arena);

        let result = parser.parse_block().unwrap();
        assert_eq!(result.statements.len(), 0);
        assert!(result.last_expr.is_none());
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_block_single_trailing_expr() {
        let arena = Bump::new();
        let mut parser = Parser::new("{ foo }", &arena);

        let result = parser.parse_block().unwrap();
        assert_eq!(result.statements.len(), 0);
        assert!(result.last_expr.is_some());
        if let Some(expr) = result.last_expr.as_deref() {
            if let ExprKind::Ident(istr) = expr.kind {
                assert_eq!(parser.interner.resolve(istr), "foo");
            } else {
                panic!("expected Ident expression");
            }
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_block_single_expr_stmt() {
        let arena = Bump::new();
        let mut parser = Parser::new("{ foo; }", &arena);

        let result = parser.parse_block().unwrap();
        assert_eq!(result.statements.len(), 1);
        assert!(result.last_expr.is_none());
        assert!(matches!(result.statements[0].kind, StatementKind::Expr(_)));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_block_expr_stmt_and_trailing_expr() {
        let arena = Bump::new();
        let mut parser = Parser::new("{ foo; bar }", &arena);

        let result = parser.parse_block().unwrap();
        assert_eq!(result.statements.len(), 1);
        assert!(result.last_expr.is_some());
        if let Some(expr) = result.last_expr.as_deref() {
            if let ExprKind::Ident(istr) = expr.kind {
                assert_eq!(parser.interner.resolve(istr), "bar");
            } else {
                panic!("expected Ident expression");
            }
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_block_recovery_on_unclosed() {
        let arena = Bump::new();
        let mut parser = Parser::new("{ foo", &arena);

        let result = parser.parse_block().unwrap();
        assert!(result.last_expr.is_some());
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_fn_def_no_params_no_return() {
        let arena = Bump::new();
        let mut parser = Parser::new("fn () {}", &arena);

        let result = parser.parse_fn_def().unwrap();
        assert_eq!(result.params.len(), 0);
        assert!(result.result.is_none());
        assert_eq!(result.body.statements.len(), 0);
        assert!(result.body.last_expr.is_none());
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_fn_def_single_param() {
        let arena = Bump::new();
        let mut parser = Parser::new("fn (x: u32) {}", &arena);

        let result = parser.parse_fn_def().unwrap();
        assert_eq!(result.params.len(), 1);
        assert!(!result.params[0].comptime);
        assert_eq!(parser.interner.resolve(result.params[0].name), "x");
        assert!(matches!(result.params[0].r#type.kind, ExprKind::Ident(_)));
        assert!(result.result.is_none());
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_fn_def_multiple_params() {
        let arena = Bump::new();
        let mut parser = Parser::new("fn (a: u32, b: u64, c: bool) {}", &arena);

        let result = parser.parse_fn_def().unwrap();
        assert_eq!(result.params.len(), 3);
        assert_eq!(parser.interner.resolve(result.params[0].name), "a");
        assert_eq!(parser.interner.resolve(result.params[1].name), "b");
        assert_eq!(parser.interner.resolve(result.params[2].name), "c");
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_fn_def_comptime_param() {
        let arena = Bump::new();
        let mut parser = Parser::new("fn (comptime T: type) {}", &arena);

        let result = parser.parse_fn_def().unwrap();
        assert_eq!(result.params.len(), 1);
        assert!(result.params[0].comptime);
        assert_eq!(parser.interner.resolve(result.params[0].name), "T");
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_fn_def_with_return_type() {
        let arena = Bump::new();
        let mut parser = Parser::new("fn () -> u32 {}", &arena);

        let result = parser.parse_fn_def().unwrap();
        assert!(result.result.is_some());
        if let Some(expr) = result.result {
            if let ExprKind::Ident(istr) = expr.kind {
                assert_eq!(parser.interner.resolve(istr), "u32");
            } else {
                panic!("expected Ident as return type");
            }
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_fn_def_trailing_comma() {
        let arena = Bump::new();
        let mut parser = Parser::new("fn (x: u32,) {}", &arena);

        let result = parser.parse_fn_def().unwrap();
        assert_eq!(result.params.len(), 1);
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_fn_def_mixed_comptime() {
        let arena = Bump::new();
        let mut parser = Parser::new("fn (comptime T: type, x: T) -> T {}", &arena);

        let result = parser.parse_fn_def().unwrap();
        assert_eq!(result.params.len(), 2);
        assert!(result.params[0].comptime);
        assert!(!result.params[1].comptime);
        assert!(result.result.is_some());
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_type_def_fn() {
        let arena = Bump::new();
        let mut parser = Parser::new("fn (x: u32) -> u64 {}", &arena);

        let result = parser.parse_type_def().unwrap();
        assert!(matches!(result, TypeDef::FnDef(_)));
        if let TypeDef::FnDef(fn_def) = result {
            assert_eq!(fn_def.params.len(), 1);
            assert!(fn_def.result.is_some());
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_type_def_struct() {
        let arena = Bump::new();
        let mut parser = Parser::new("struct { x: u32, y: u64 }", &arena);

        let result = parser.parse_type_def().unwrap();
        assert!(matches!(result, TypeDef::StructDef(_)));
        if let TypeDef::StructDef(struct_def) = result {
            assert_eq!(struct_def.fields.len(), 2);
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_type_def_fails_on_invalid_token() {
        let arena = Bump::new();
        let mut parser = Parser::new("if", &arena);

        let result = parser.parse_type_def();
        assert!(result.is_err());
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_type_def_fails_on_identifier() {
        let arena = Bump::new();
        let mut parser = Parser::new("SomeType", &arena);

        let result = parser.parse_type_def();
        assert!(result.is_err());
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_comptime_block_empty() {
        let arena = Bump::new();
        let mut parser = Parser::new("comptime {}", &arena);

        let result = parser.parse_comptime_block().unwrap();
        assert!(matches!(result.kind, ExprKind::Comptime(_)));
        if let ExprKind::Comptime(block) = result.kind {
            assert_eq!(block.statements.len(), 0);
            assert!(block.last_expr.is_none());
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_comptime_block_with_trailing_expr() {
        let arena = Bump::new();
        let mut parser = Parser::new("comptime { foo }", &arena);

        let result = parser.parse_comptime_block().unwrap();
        assert!(matches!(result.kind, ExprKind::Comptime(_)));
        if let ExprKind::Comptime(block) = result.kind {
            assert_eq!(block.statements.len(), 0);
            assert!(block.last_expr.is_some());
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_comptime_block_with_expr_stmt() {
        let arena = Bump::new();
        let mut parser = Parser::new("comptime { foo; }", &arena);

        let result = parser.parse_comptime_block().unwrap();
        assert!(matches!(result.kind, ExprKind::Comptime(_)));
        if let ExprKind::Comptime(block) = result.kind {
            assert_eq!(block.statements.len(), 1);
            assert!(block.last_expr.is_none());
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_comptime_block_fails_without_block() {
        let arena = Bump::new();
        let mut parser = Parser::new("comptime foo", &arena);

        let result = parser.parse_comptime_block();
        assert!(result.is_err());
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_struct_literal_empty() {
        let arena = Bump::new();
        let mut parser = Parser::new("MyStruct {}", &arena);

        let result = parser.parse_struct_literal().unwrap();
        assert_eq!(result.type_path.segments.len(), 1);
        assert_eq!(parser.interner.resolve(result.type_path.segments[0]), "MyStruct");
        assert_eq!(result.fields.len(), 0);
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_struct_literal_single_field() {
        let arena = Bump::new();
        let mut parser = Parser::new("Point { x: 42 }", &arena);

        let result = parser.parse_struct_literal().unwrap();
        assert_eq!(result.type_path.segments.len(), 1);
        assert_eq!(parser.interner.resolve(result.type_path.segments[0]), "Point");
        assert_eq!(result.fields.len(), 1);
        assert_eq!(parser.interner.resolve(result.fields[0].name), "x");
        assert!(matches!(result.fields[0].value.kind, ExprKind::IntLiteral(_)));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_struct_literal_multiple_fields() {
        let arena = Bump::new();
        let mut parser = Parser::new("Point { x: 1, y: 2, z: 3 }", &arena);

        let result = parser.parse_struct_literal().unwrap();
        assert_eq!(result.type_path.segments.len(), 1);
        assert_eq!(result.fields.len(), 3);
        assert_eq!(parser.interner.resolve(result.fields[0].name), "x");
        assert_eq!(parser.interner.resolve(result.fields[1].name), "y");
        assert_eq!(parser.interner.resolve(result.fields[2].name), "z");
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_struct_literal_trailing_comma() {
        let arena = Bump::new();
        let mut parser = Parser::new("Point { x: 1, y: 2, }", &arena);

        let result = parser.parse_struct_literal().unwrap();
        assert_eq!(result.fields.len(), 2);
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_struct_literal_namespaced() {
        let arena = Bump::new();
        let mut parser = Parser::new("math.geometry.Point { x: 1 }", &arena);

        let result = parser.parse_struct_literal().unwrap();
        assert_eq!(result.type_path.segments.len(), 3);
        assert_eq!(parser.interner.resolve(result.type_path.segments[0]), "math");
        assert_eq!(parser.interner.resolve(result.type_path.segments[1]), "geometry");
        assert_eq!(parser.interner.resolve(result.type_path.segments[2]), "Point");
        assert_eq!(result.fields.len(), 1);
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_struct_literal_field_with_ident_value() {
        let arena = Bump::new();
        let mut parser = Parser::new("Config { value: foo }", &arena);

        let result = parser.parse_struct_literal().unwrap();
        assert_eq!(result.fields.len(), 1);
        assert_eq!(parser.interner.resolve(result.fields[0].name), "value");
        if let ExprKind::Ident(istr) = result.fields[0].value.kind {
            assert_eq!(parser.interner.resolve(istr), "foo");
        } else {
            panic!("expected Ident expression");
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_cond_expr_simple() {
        let arena = Bump::new();
        let mut parser = Parser::new("if true { 1 } else { 2 }", &arena);

        let result = parser.parse_cond_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::Conditional(_)));
        if let ExprKind::Conditional(cond) = result.kind {
            assert!(matches!(cond.r#if.condition.kind, ExprKind::BoolLiteral(true)));
            assert!(cond.r#if.body.last_expr.is_some());
            assert_eq!(cond.else_ifs.len(), 0);
            assert!(matches!(cond.else_body, MaybeOr::Just(_)));
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_cond_expr_with_else_if() {
        let arena = Bump::new();
        let mut parser = Parser::new("if a { 1 } else if b { 2 } else { 3 }", &arena);

        let result = parser.parse_cond_expr().unwrap();
        if let ExprKind::Conditional(cond) = result.kind {
            assert_eq!(cond.else_ifs.len(), 1);
            assert!(matches!(cond.else_body, MaybeOr::Just(_)));
        } else {
            panic!("expected Conditional");
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_cond_expr_multiple_else_ifs() {
        let arena = Bump::new();
        let mut parser =
            Parser::new("if a { 1 } else if b { 2 } else if c { 3 } else { 4 }", &arena);

        let result = parser.parse_cond_expr().unwrap();
        if let ExprKind::Conditional(cond) = result.kind {
            assert_eq!(cond.else_ifs.len(), 2);
            assert!(matches!(cond.else_body, MaybeOr::Just(_)));
        } else {
            panic!("expected Conditional");
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_cond_expr_missing_else_reports_error() {
        let arena = Bump::new();
        let mut parser = Parser::new("if true { 1 }", &arena);

        let result = parser.parse_cond_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::Conditional(_)));
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_expr_no_block_ident() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo", &arena);

        let result = parser.parse_expr_no_block().unwrap();
        assert!(matches!(result.kind, ExprKind::Ident(_)));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_expr_no_block_literal() {
        let arena = Bump::new();
        let mut parser = Parser::new("42", &arena);

        let result = parser.parse_expr_no_block().unwrap();
        assert!(matches!(result.kind, ExprKind::IntLiteral(_)));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_expr_no_block_struct_literal() {
        let arena = Bump::new();
        let mut parser = Parser::new("Point { x: 1, y: 2 }", &arena);

        let result = parser.parse_expr_no_block().unwrap();
        assert!(matches!(result.kind, ExprKind::StructLiteral(_)));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_expr_no_block_fn_def() {
        let arena = Bump::new();
        let mut parser = Parser::new("fn (x: u32) -> u64 {}", &arena);

        let result = parser.parse_expr_no_block().unwrap();
        assert!(matches!(result.kind, ExprKind::TypeDef(TypeDef::FnDef(_))));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_expr_no_block_struct_def() {
        let arena = Bump::new();
        let mut parser = Parser::new("struct { x: u32 }", &arena);

        let result = parser.parse_expr_no_block().unwrap();
        assert!(matches!(result.kind, ExprKind::TypeDef(TypeDef::StructDef(_))));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_expr_no_block_postfix_chain() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo.bar()", &arena);

        let result = parser.parse_expr_no_block().unwrap();
        assert!(matches!(result.kind, ExprKind::FnCall(_)));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_expr_comptime() {
        let arena = Bump::new();
        let mut parser = Parser::new("comptime { 42 }", &arena);

        let result = parser.parse_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::Comptime(_)));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_expr_block() {
        let arena = Bump::new();
        let mut parser = Parser::new("{ foo }", &arena);

        let result = parser.parse_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::Block(_)));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_expr_conditional() {
        let arena = Bump::new();
        let mut parser = Parser::new("if true { 1 } else { 2 }", &arena);

        let result = parser.parse_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::Conditional(_)));
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_expr_delegates_to_no_block() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo.bar(42)", &arena);

        let result = parser.parse_expr().unwrap();
        assert!(matches!(result.kind, ExprKind::FnCall(_)));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_return_stmt_simple() {
        let arena = Bump::new();
        let mut parser = Parser::new("return 42;", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Return(_)));
        if let StatementKind::Return(expr) = result.kind {
            assert!(matches!(expr.kind, ExprKind::IntLiteral(_)));
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_return_stmt_identifier() {
        let arena = Bump::new();
        let mut parser = Parser::new("return foo;", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Return(_)));
        if let StatementKind::Return(expr) = result.kind {
            if let ExprKind::Ident(istr) = expr.kind {
                assert_eq!(parser.interner.resolve(istr), "foo");
            } else {
                panic!("expected Ident");
            }
        } else {
            panic!("expected Return");
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_return_stmt_complex_expr() {
        let arena = Bump::new();
        let mut parser = Parser::new("return foo.bar();", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Return(_)));
        if let StatementKind::Return(expr) = result.kind {
            assert!(matches!(expr.kind, ExprKind::FnCall(_)));
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_return_stmt_missing_semicolon_at_eof_recovers() {
        let arena = Bump::new();
        let mut parser = Parser::new("return 42", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Return(_)));
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_return_stmt_missing_semicolon_before_token_fails() {
        let arena = Bump::new();
        let mut parser = Parser::new("return 42 foo", &arena);

        let result = parser.parse_stmt();
        assert!(result.is_err());
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_let_stmt_simple() {
        let arena = Bump::new();
        let mut parser = Parser::new("let x = 42;", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Let(_)));
        if let StatementKind::Let(let_stmt) = result.kind {
            assert!(!let_stmt.mutable);
            assert_eq!(parser.interner.resolve(let_stmt.ident), "x");
            assert!(let_stmt.r#type.is_none());
            assert!(matches!(let_stmt.value.kind, ExprKind::IntLiteral(_)));
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_let_stmt_mutable() {
        let arena = Bump::new();
        let mut parser = Parser::new("let mut y = foo;", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Let(_)));
        if let StatementKind::Let(let_stmt) = result.kind {
            assert!(let_stmt.mutable);
            assert_eq!(parser.interner.resolve(let_stmt.ident), "y");
            assert!(let_stmt.r#type.is_none());
            assert!(matches!(let_stmt.value.kind, ExprKind::Ident(_)));
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_let_stmt_with_type_annotation() {
        let arena = Bump::new();
        let mut parser = Parser::new("let x: u32 = 42;", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Let(_)));
        if let StatementKind::Let(let_stmt) = result.kind {
            assert!(!let_stmt.mutable);
            assert_eq!(parser.interner.resolve(let_stmt.ident), "x");
            assert!(let_stmt.r#type.is_some());
            if let Some(Expr { kind: ExprKind::Ident(type_istr), .. }) = let_stmt.r#type {
                assert_eq!(parser.interner.resolve(type_istr), "u32");
            } else {
                panic!("expected Ident as type");
            }
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_let_stmt_mutable_with_type() {
        let arena = Bump::new();
        let mut parser = Parser::new("let mut count: u64 = 0;", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Let(_)));
        if let StatementKind::Let(let_stmt) = result.kind {
            assert!(let_stmt.mutable);
            assert_eq!(parser.interner.resolve(let_stmt.ident), "count");
            assert!(let_stmt.r#type.is_some());
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_assign_stmt_simple() {
        let arena = Bump::new();
        let mut parser = Parser::new("x = 42;", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Assign(_)));
        if let StatementKind::Assign(assign) = result.kind {
            assert_eq!(assign.target.segments.len(), 1);
            assert_eq!(parser.interner.resolve(assign.target.segments[0]), "x");
            assert!(matches!(assign.op, AssignOp::Assign));
            assert!(matches!(assign.value.kind, ExprKind::IntLiteral(_)));
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_assign_stmt_name_path() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo.bar.baz = true;", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Assign(_)));
        if let StatementKind::Assign(assign) = result.kind {
            assert_eq!(assign.target.segments.len(), 3);
            assert_eq!(parser.interner.resolve(assign.target.segments[0]), "foo");
            assert_eq!(parser.interner.resolve(assign.target.segments[1]), "bar");
            assert_eq!(parser.interner.resolve(assign.target.segments[2]), "baz");
            assert!(matches!(assign.value.kind, ExprKind::BoolLiteral(true)));
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_assign_stmt_complex_value() {
        let arena = Bump::new();
        let mut parser = Parser::new("target = foo.bar();", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Assign(_)));
        if let StatementKind::Assign(assign) = result.kind {
            assert_eq!(assign.target.segments.len(), 1);
            assert!(matches!(assign.value.kind, ExprKind::FnCall(_)));
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_assign_stmt_missing_semicolon_at_eof_recovers() {
        let arena = Bump::new();
        let mut parser = Parser::new("x = 42", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Assign(_)));
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_block_stmt_empty() {
        let arena = Bump::new();
        let mut parser = Parser::new("{}", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Block(_)));
        if let StatementKind::Block(block) = result.kind {
            assert_eq!(block.statements.len(), 0);
            assert!(block.last_expr.is_none());
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_block_stmt_with_trailing_expr() {
        let arena = Bump::new();
        let mut parser = Parser::new("{ foo }", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Block(_)));
        if let StatementKind::Block(block) = result.kind {
            assert_eq!(block.statements.len(), 0);
            assert!(block.last_expr.is_some());
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_block_stmt_optional_semicolon_present() {
        let arena = Bump::new();
        let mut parser = Parser::new("{}; foo", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Block(_)));
        assert_eq!(parser.token, Some(Token::Identifier));
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_block_stmt_optional_semicolon_absent() {
        let arena = Bump::new();
        let mut parser = Parser::new("{} foo", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Block(_)));
        assert_eq!(parser.token, Some(Token::Identifier));
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_while_stmt_simple() {
        let arena = Bump::new();
        let mut parser = Parser::new("while true {}", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::While(_)));
        if let StatementKind::While(while_stmt) = result.kind {
            assert!(!while_stmt.inline);
            assert!(matches!(while_stmt.condition.kind, ExprKind::BoolLiteral(true)));
            assert_eq!(while_stmt.body.statements.len(), 0);
            assert!(while_stmt.body.last_expr.is_none());
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_while_stmt_inline() {
        let arena = Bump::new();
        let mut parser = Parser::new("inline while cond { foo; }", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::While(_)));
        if let StatementKind::While(while_stmt) = result.kind {
            assert!(while_stmt.inline);
            assert!(matches!(while_stmt.condition.kind, ExprKind::Ident(_)));
            assert_eq!(while_stmt.body.statements.len(), 1);
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_while_stmt_with_body() {
        let arena = Bump::new();
        let mut parser = Parser::new("while x { let y = 1; return y; }", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::While(_)));
        if let StatementKind::While(while_stmt) = result.kind {
            assert!(!while_stmt.inline);
            assert_eq!(while_stmt.body.statements.len(), 2);
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_while_stmt_complex_condition() {
        let arena = Bump::new();
        let mut parser = Parser::new("while foo.bar() {}", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::While(_)));
        if let StatementKind::While(while_stmt) = result.kind {
            assert!(matches!(while_stmt.condition.kind, ExprKind::FnCall(_)));
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_expr_stmt_bool_literal() {
        let arena = Bump::new();
        let mut parser = Parser::new("true;", &arena);

        let result = parser.parse_stmt().unwrap();
        if let StatementKind::Expr(expr) = result.kind {
            assert!(matches!(expr.kind, ExprKind::BoolLiteral(true)));
        } else {
            panic!("expected Expr statement");
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_expr_stmt_int_literal() {
        let arena = Bump::new();
        let mut parser = Parser::new("42;", &arena);

        let result = parser.parse_stmt().unwrap();
        if let StatementKind::Expr(expr) = result.kind {
            assert!(matches!(expr.kind, ExprKind::IntLiteral(_)));
        } else {
            panic!("expected Expr statement");
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_expr_stmt_fn_call() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo();", &arena);

        let result = parser.parse_stmt().unwrap();
        if let StatementKind::Expr(expr) = result.kind {
            assert!(matches!(expr.kind, ExprKind::FnCall(_)));
        } else {
            panic!("expected Expr statement");
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_expr_stmt_requires_semicolon() {
        let arena = Bump::new();
        let mut parser = Parser::new("42 foo", &arena);

        let result = parser.parse_stmt();
        assert!(result.is_err());
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_cond_stmt_simple_no_else() {
        let arena = Bump::new();
        let mut parser = Parser::new("if true {}", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Conditional(_)));
        if let StatementKind::Conditional(cond) = result.kind {
            assert!(matches!(cond.r#if.condition.kind, ExprKind::BoolLiteral(true)));
            assert_eq!(cond.r#if.body.statements.len(), 0);
            assert!(cond.r#if.body.last_expr.is_none());
            assert_eq!(cond.else_ifs.len(), 0);
            assert!(matches!(cond.else_body, MaybeOr::Other(())));
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_cond_stmt_with_else() {
        let arena = Bump::new();
        let mut parser = Parser::new("if cond { foo; } else { bar; }", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Conditional(_)));
        if let StatementKind::Conditional(cond) = result.kind {
            assert!(matches!(cond.r#if.condition.kind, ExprKind::Ident(_)));
            assert_eq!(cond.r#if.body.statements.len(), 1);
            assert_eq!(cond.else_ifs.len(), 0);
            assert!(matches!(cond.else_body, MaybeOr::Just(_)));
            if let MaybeOr::Just(else_body) = &cond.else_body {
                assert_eq!(else_body.statements.len(), 1);
            }
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_cond_stmt_with_else_if() {
        let arena = Bump::new();
        let mut parser = Parser::new("if a {} else if b {} else if c {}", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Conditional(_)));
        if let StatementKind::Conditional(cond) = result.kind {
            assert!(matches!(cond.r#if.condition.kind, ExprKind::Ident(_)));
            assert_eq!(cond.else_ifs.len(), 2);
            assert!(matches!(cond.else_body, MaybeOr::Other(())));
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_cond_stmt_full_chain() {
        let arena = Bump::new();
        let mut parser = Parser::new("if a { x; } else if b { y; } else { z; }", &arena);

        let result = parser.parse_stmt().unwrap();
        assert!(matches!(result.kind, StatementKind::Conditional(_)));
        if let StatementKind::Conditional(cond) = result.kind {
            assert_eq!(cond.r#if.body.statements.len(), 1);
            assert_eq!(cond.else_ifs.len(), 1);
            assert_eq!(cond.else_ifs[0].body.statements.len(), 1);
            assert!(matches!(cond.else_body, MaybeOr::Just(_)));
            if let MaybeOr::Just(else_body) = &cond.else_body {
                assert_eq!(else_body.statements.len(), 1);
            }
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_init_decl_empty() {
        let arena = Bump::new();
        let mut parser = Parser::new("init {}", &arena);

        let result = parser.parse_init_decl().unwrap();
        assert!(matches!(result.kind, DeclarationKind::Init(_)));
        if let DeclarationKind::Init(block) = result.kind {
            assert_eq!(block.statements.len(), 0);
            assert!(block.last_expr.is_none());
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_init_decl_with_statements() {
        let arena = Bump::new();
        let mut parser = Parser::new("init { let x = 42; return x; }", &arena);

        let result = parser.parse_init_decl().unwrap();
        assert!(matches!(result.kind, DeclarationKind::Init(_)));
        if let DeclarationKind::Init(block) = result.kind {
            assert_eq!(block.statements.len(), 2);
            assert!(block.last_expr.is_none());
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_init_decl_with_trailing_expr() {
        let arena = Bump::new();
        let mut parser = Parser::new("init { foo }", &arena);

        let result = parser.parse_init_decl().unwrap();
        assert!(matches!(result.kind, DeclarationKind::Init(_)));
        if let DeclarationKind::Init(block) = result.kind {
            assert_eq!(block.statements.len(), 0);
            assert!(block.last_expr.is_some());
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_init_decl_recovery_unclosed() {
        let arena = Bump::new();
        let mut parser = Parser::new("init { foo", &arena);

        let result = parser.parse_init_decl().unwrap();
        assert!(matches!(result.kind, DeclarationKind::Init(_)));
        if let DeclarationKind::Init(block) = result.kind {
            assert!(block.last_expr.is_some());
        }
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_run_decl_empty() {
        let arena = Bump::new();
        let mut parser = Parser::new("run {}", &arena);

        let result = parser.parse_run_decl().unwrap();
        assert!(matches!(result.kind, DeclarationKind::Run(_)));
        if let DeclarationKind::Run(block) = result.kind {
            assert_eq!(block.statements.len(), 0);
            assert!(block.last_expr.is_none());
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_run_decl_with_statements() {
        let arena = Bump::new();
        let mut parser = Parser::new("run { let x = 42; return x; }", &arena);

        let result = parser.parse_run_decl().unwrap();
        assert!(matches!(result.kind, DeclarationKind::Run(_)));
        if let DeclarationKind::Run(block) = result.kind {
            assert_eq!(block.statements.len(), 2);
            assert!(block.last_expr.is_none());
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_run_decl_with_trailing_expr() {
        let arena = Bump::new();
        let mut parser = Parser::new("run { foo }", &arena);

        let result = parser.parse_run_decl().unwrap();
        assert!(matches!(result.kind, DeclarationKind::Run(_)));
        if let DeclarationKind::Run(block) = result.kind {
            assert_eq!(block.statements.len(), 0);
            assert!(block.last_expr.is_some());
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_run_decl_recovery_unclosed() {
        let arena = Bump::new();
        let mut parser = Parser::new("run { foo", &arena);

        let result = parser.parse_run_decl().unwrap();
        assert!(matches!(result.kind, DeclarationKind::Run(_)));
        if let DeclarationKind::Run(block) = result.kind {
            assert!(block.last_expr.is_some());
        }
        assert!(parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_const_def_simple() {
        let arena = Bump::new();
        let mut parser = Parser::new("const FOO = 42;", &arena);

        let result = parser.parse_const_def().unwrap();
        assert!(matches!(result.kind, DeclarationKind::ConstDef(_)));
        if let DeclarationKind::ConstDef(const_def) = result.kind {
            assert!(const_def.r#type.is_none());
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_const_def_with_type() {
        let arena = Bump::new();
        let mut parser = Parser::new("const BAR: u256 = 100;", &arena);

        let result = parser.parse_const_def().unwrap();
        assert!(matches!(result.kind, DeclarationKind::ConstDef(_)));
        if let DeclarationKind::ConstDef(const_def) = result.kind {
            assert!(const_def.r#type.is_some());
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_const_def_complex_expr() {
        let arena = Bump::new();
        let mut parser = Parser::new("const MAX: u256 = foo.bar(1, 2);", &arena);

        let result = parser.parse_const_def().unwrap();
        assert!(matches!(result.kind, DeclarationKind::ConstDef(_)));
        if let DeclarationKind::ConstDef(const_def) = result.kind {
            assert!(const_def.r#type.is_some());
        }
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_next_decl_eof() {
        let arena = Bump::new();
        let mut parser = Parser::new("", &arena);

        let result = parser.parse_next_decl().unwrap();
        assert!(result.is_none());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_next_decl_init() {
        let arena = Bump::new();
        let mut parser = Parser::new("init { foo }", &arena);

        let result = parser.parse_next_decl().unwrap();
        assert!(result.is_some());
        assert!(matches!(result.unwrap().kind, DeclarationKind::Init(_)));
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_next_decl_run() {
        let arena = Bump::new();
        let mut parser = Parser::new("run { bar }", &arena);

        let result = parser.parse_next_decl().unwrap();
        assert!(result.is_some());
        assert!(matches!(result.unwrap().kind, DeclarationKind::Run(_)));
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_next_decl_const() {
        let arena = Bump::new();
        let mut parser = Parser::new("const X = 42;", &arena);

        let result = parser.parse_next_decl().unwrap();
        assert!(result.is_some());
        assert!(matches!(result.unwrap().kind, DeclarationKind::ConstDef(_)));
        assert!(parser.at_eof());
        assert!(!parser.diagnostics.has_errors());
    }

    #[test]
    fn test_parse_next_decl_invalid_token() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo", &arena);

        let result = parser.parse_next_decl();
        assert!(result.is_err());
        assert!(parser.diagnostics.has_errors());
    }
}
