use super::lexer::{Lexer, Token};
use alloy_primitives::{
    U256, hex,
    ruint::{BaseConvertError, ParseError as UintParseError},
};
use bumpalo::{Bump, collections::Vec as BVec};
use chumsky::{extra, input::IterInput, prelude::*};
use std::ops::Range;

const START_STMT_OUTPUTS_CAPACITY: usize = 1;
const STMT_OUTPUTS_FIRST_RESIZE_CAPACITY: usize = 4;
const DEFAULT_STMT_PARAMS_CAPACITY: usize = 4;
const DEFAULT_BB_STMTS_CAPACITY: usize = 8;
const DEFAULT_SWITCH_CASES_CAPACITY: usize = 8;
const DEFAULT_BB_INPUTS_CAPACITY: usize = 2;
const DEFAULT_BB_OUTPUTS_CAPACITY: usize = 2;
const DEFAULT_FUNCTION_BBS_CAPACITY: usize = 8;
const DEFAULT_TOP_LEVEL_ITEMS_CAPACITY: usize = 8;

pub type Span = Range<usize>;
type Box<'a, T> = &'a mut T;

#[derive(Debug, Clone)]
pub struct Spanned<T> {
    span: Span,
    pub inner: T,
}

impl<T> Spanned<T> {
    pub fn new(inner: T, span: Span) -> Self {
        Self { inner, span }
    }

    pub fn span(&self) -> Span {
        self.span.clone()
    }

    pub fn map<F, O>(self, f: F) -> Spanned<O>
    where
        F: FnOnce(T) -> O,
    {
        Spanned::new(f(self.inner), self.span)
    }
}

impl<T> std::ops::Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T> std::ops::DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

#[derive(Debug)]
pub struct Ast<'arena, 'src> {
    pub functions: BVec<'arena, Function<'arena, 'src>>,
    pub data_segments: BVec<'arena, DataSegment<'arena, 'src>>,
}

#[derive(Debug)]
pub struct DataSegment<'arena, 'src> {
    pub name: Spanned<&'src str>,
    pub data: Spanned<Box<'arena, [u8]>>,
}

#[derive(Debug)]
pub struct Function<'arena, 'src> {
    pub name: Spanned<&'src str>,
    pub basic_blocks: BVec<'arena, BasicBlock<'arena, 'src>>,
}

#[derive(Debug)]
pub struct BasicBlock<'arena, 'src> {
    pub name: Spanned<&'src str>,
    pub inputs: BVec<'arena, Spanned<&'src str>>,
    pub outputs: BVec<'arena, Spanned<&'src str>>,
    pub stmts: BVec<'arena, Statement<'arena, 'src>>,
    pub control_flow: Option<ControlFlow<'arena, 'src>>,
}

#[derive(Debug)]
pub struct Statement<'arena, 'src> {
    pub assigns: BVec<'arena, Spanned<&'src str>>,
    pub op: Spanned<&'src str>,
    pub params: BVec<'arena, ParamExpr<'arena, 'src>>,
}

#[derive(Debug)]
pub enum ParamExpr<'arena, 'src> {
    NameRef(Spanned<&'src str>),
    FuncRef(Spanned<&'src str>),
    DataRef(Spanned<&'src str>),
    Num(Box<'arena, Spanned<U256>>),
}

#[derive(Debug)]
pub enum ControlFlow<'arena, 'src> {
    UnconditionalTo(Spanned<&'src str>),
    Conditional {
        condition: Spanned<&'src str>,
        non_zero_to: Spanned<&'src str>,
        zero_to: Spanned<&'src str>,
    },
    Switch(Box<'arena, Switch<'arena, 'src>>),
    InternalReturn,
}

#[derive(Debug)]
pub struct Switch<'arena, 'src> {
    pub value_ref: Spanned<&'src str>,
    pub fallback: Option<Spanned<&'src str>>,
    pub cases: BVec<'arena, Case<'src>>,
}

#[derive(Debug)]
pub struct Case<'src> {
    pub match_value: U256,
    pub to: Spanned<&'src str>,
}

type ParserError<'src> = extra::Err<Rich<'src, Token, Span>>;

pub fn parse<'arena, 'src>(
    source: &'src str,
    arena: &'arena Bump,
) -> Result<Ast<'arena, 'src>, Vec<Rich<'src, Token, Span>>> {
    let token_iter = Lexer::new(source);
    let eoi = source.len()..source.len();
    let input = IterInput::new(token_iter, eoi);

    parser(source, arena).parse(input).into_result()
}

fn parser<'arena, 'src: 'arena>(
    source: &'src str,
    arena: &'arena Bump,
) -> impl Parser<'src, IterInput<Lexer<'src>, Span>, Ast<'arena, 'src>, ParserError<'src>> + Clone {
    // Token selectors with slice recovery - all produce Spanned values
    let ident = select! { Token::Identifier => () }
        .map_with(|_, e| Spanned::new(&source[e.span()], e.span()));

    let label = select! { Token::Label => () }.map_with(|_, e| {
        let s: &str = &source[e.span()];
        Spanned::new(s.strip_prefix('@').expect("invalid label"), e.span())
    });

    let data_ref = select! { Token::DataRef => () }.map_with(|_, e| {
        let s: &str = &source[e.span()];
        Spanned::new(s.strip_prefix('.').expect("invalid data ref"), e.span())
    });

    let dec_literal_as_u256 = select! { Token::DecLiteral => () }.map_with(|_, e| {
        let s: &str = &source[e.span()];
        match s.strip_prefix('-') {
            Some(abs_s) => abs_s.parse::<U256>().map(|v| U256::ZERO.wrapping_sub(v)),
            None => s.parse::<U256>(),
        }
    });

    let hex_as_u256 = select! { Token::HexLiteral => () }.map_with(|_, e| {
        let s: &str = &source[e.span()];
        let hex_str = s.strip_prefix("0x").unwrap_or(s);
        U256::from_str_radix(hex_str, 16)
    });

    let u256_value = dec_literal_as_u256.or(hex_as_u256).try_map_with(|v, e| {
        let s = &source[e.span()];
        let value = v.map_err(|err| match err {
            UintParseError::BaseConvertError(BaseConvertError::Overflow) => {
                Rich::custom(e.span(), format!("Literal {:?} doesn't fit into 256-bits", s))
            }
            _ => unreachable!("U256 failed to parse {:?} (err: {})", s, err),
        })?;
        Ok(Spanned::new(value, e.span()))
    });

    // Statement parsers - all require explicit mnemonics now
    let statement = {
        let assigns = empty()
            .map(|_| BVec::with_capacity_in(START_STMT_OUTPUTS_CAPACITY, arena))
            .foldl(ident.repeated().at_least(1), |mut assigns, assign| {
                if assigns.len() == START_STMT_OUTPUTS_CAPACITY {
                    assigns.reserve(STMT_OUTPUTS_FIRST_RESIZE_CAPACITY);
                }
                assigns.push(assign);
                assigns
            });
        let mnemonic = ident;
        let params =
            empty().map(|_| BVec::with_capacity_in(DEFAULT_STMT_PARAMS_CAPACITY, arena)).foldl(
                choice((
                    ident.map(ParamExpr::NameRef),
                    label.map(ParamExpr::FuncRef),
                    data_ref.map(ParamExpr::DataRef),
                    u256_value.map(|v| ParamExpr::Num(arena.alloc(v))),
                ))
                .repeated(),
                |mut exprs, expr| {
                    exprs.push(expr);
                    exprs
                },
            );

        assigns.then_ignore(just(Token::Equals)).or_not().then(mnemonic).then(params).map(
            |((assigns, op), params)| Statement {
                assigns: assigns.unwrap_or_else(|| BVec::new_in(arena)),
                op,
                params,
            },
        )
    };

    // Control flow parsers
    let branch = just(Token::ThickArrow)
        .ignore_then(ident)
        .then_ignore(just(Token::Question))
        .then(label)
        .then_ignore(just(Token::Colon))
        .then(label)
        .map(|((condition, non_zero_to), zero_to)| ControlFlow::Conditional {
            condition,
            non_zero_to,
            zero_to,
        });

    let continue_to = just(Token::ThickArrow).ignore_then(label).map(ControlFlow::UnconditionalTo);

    let iret = just(Token::InternalReturn).map(|_| ControlFlow::InternalReturn);

    let switch = just(Token::Switch)
        .ignore_then(ident)
        .then_ignore(just(Token::Newline).repeated())
        .then_ignore(just(Token::LeftBrace))
        .then_ignore(just(Token::Newline).repeated())
        .then(
            empty()
                .map(|_| BVec::with_capacity_in(DEFAULT_SWITCH_CASES_CAPACITY, arena))
                .foldl(
                    u256_value
                        .then_ignore(just(Token::ThickArrow))
                        .then(label)
                        .separated_by(just(Token::Newline).repeated()),
                    |mut cases, (v, to)| {
                        cases.push(Case { match_value: v.inner, to });
                        cases
                    },
                )
                .then_ignore(just(Token::Newline).repeated())
                .then(
                    just(Token::Default)
                        .ignore_then(just(Token::ThickArrow))
                        .ignore_then(label)
                        .or_not(),
                )
                .then_ignore(just(Token::Newline).repeated()),
        )
        .then_ignore(just(Token::RightBrace))
        .map(|(value_ref, (cases, default))| {
            ControlFlow::Switch(arena.alloc(Switch { value_ref, fallback: default, cases }))
        });

    let control_flow = choice((iret, switch, branch, continue_to));

    // Basic block parser
    let basic_block = ident
        .then(empty().map(|_| BVec::with_capacity_in(DEFAULT_BB_INPUTS_CAPACITY, arena)).foldl(
            ident.repeated(),
            |mut inputs, input| {
                inputs.push(input);
                inputs
            },
        ))
        .then(
            just(Token::ThinArrow)
                .ignore_then(
                    empty()
                        .map(|_| BVec::with_capacity_in(DEFAULT_BB_OUTPUTS_CAPACITY, arena))
                        .foldl(ident.repeated(), |mut outputs, output| {
                            outputs.push(output);
                            outputs
                        }),
                )
                .or_not()
                .map(|o| o.unwrap_or_else(|| BVec::new_in(arena))),
        )
        .then_ignore(just(Token::LeftBrace))
        .then_ignore(just(Token::Newline).ignored().repeated())
        .then(
            empty()
                .map(|_| BVec::with_capacity_in(DEFAULT_BB_STMTS_CAPACITY, arena))
                .foldl(
                    statement.separated_by(just(Token::Newline).ignored().repeated().at_least(1)),
                    |mut stmts, stmt| {
                        stmts.push(stmt);
                        stmts
                    },
                )
                .then_ignore(just(Token::Newline).ignored().repeated())
                .then(control_flow.or_not())
                .then_ignore(just(Token::Newline).ignored().repeated()),
        )
        .then_ignore(just(Token::RightBrace))
        .then_ignore(just(Token::Newline).ignored().repeated())
        .map(|(((name, inputs), outputs), (stmts, control_flow))| BasicBlock {
            name,
            inputs,
            outputs,
            stmts,
            control_flow,
        });

    // Function definition
    let function = just(Token::Fn)
        .ignore_then(ident)
        .then_ignore(just(Token::Colon))
        .then_ignore(just(Token::Newline).ignored().or_not())
        .then(empty().map(|_| BVec::with_capacity_in(DEFAULT_FUNCTION_BBS_CAPACITY, arena)).foldl(
            basic_block.repeated().at_least(1),
            |mut bbs, bb| {
                bbs.push(bb);
                bbs
            },
        ))
        .map(|(name, basic_blocks)| Function { name, basic_blocks });

    // Data definition
    let data_def = just(Token::Data)
        .then_ignore(just(Token::Newline).repeated())
        .ignore_then(ident)
        .then_ignore(just(Token::Newline).repeated())
        .then(select! { Token::HexLiteral => () }.try_map_with(|_, e| {
            let s: &str = &source[e.span()];
            let hex_str = s.strip_prefix("0x").expect("invalid hex literal");
            if !hex_str.len().is_multiple_of(2) {
                return Err(Rich::custom(
                    e.span(),
                    "Data definition with odd hex nibbles is ambiguous",
                ));
            }
            let bytes = arena.alloc_slice_fill_default(hex_str.len() / 2);
            hex::decode_to_slice(hex_str, bytes).expect("hex not decoded despite validation");
            Ok(Spanned::new(bytes, e.span()))
        }))
        .then_ignore(just(Token::Newline).ignored().or_not())
        .map(|(name, data)| DataSegment { name, data });

    // Top-level program: func_def* data_segment_def*
    just(Token::Newline)
        .ignored()
        .repeated()
        .ignore_then(
            empty()
                .map(|_| BVec::with_capacity_in(DEFAULT_TOP_LEVEL_ITEMS_CAPACITY, arena))
                .foldl(function.repeated(), |mut functions, f| {
                    functions.push(f);
                    functions
                })
                .then(
                    empty()
                        .map(|_| BVec::with_capacity_in(DEFAULT_TOP_LEVEL_ITEMS_CAPACITY, arena))
                        .foldl(data_def.repeated(), |mut data_segments, d| {
                            data_segments.push(d);
                            data_segments
                        }),
                ),
        )
        .then_ignore(end())
        .map(|(functions, data_segments)| Ast { functions, data_segments })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_parse() {
        let arena = Bump::with_capacity(4000);
        let ast = parse(
            r#"
            fn main:
                entry x {
                    doubled = add x x
                    stop
                }
        "#,
            &arena,
        )
        .unwrap();

        assert_eq!(ast.functions.len(), 1);
        assert_eq!(ast.data_segments.len(), 0);
    }

    #[test]
    fn test_negative_literal_twos_complement() {
        let arena = Bump::with_capacity(4000);
        let source = format!(
            r#"
            fn main:
                entry {{
                    x = large_const -{}
                    stop
                }}
            "#,
            U256::MAX
        );
        let ast = parse(&source, &arena).unwrap();

        let stmt = &ast.functions[0].basic_blocks[0].stmts[0];
        let ParamExpr::Num(n) = &stmt.params[0] else { panic!("expected Num") };
        assert_eq!(n.inner, U256::from(1));
    }
}
