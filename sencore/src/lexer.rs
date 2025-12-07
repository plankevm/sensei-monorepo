use crate::span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Token<'src> {
    Ident(&'src str),
    Num(&'src str),

    RoundOpen,
    RoundClose,

    True,
    False,

    Error,
}

#[derive(Debug, Clone)]
pub struct Lexer<'src> {
    source: &'src str,
    chars: std::iter::Peekable<std::str::CharIndices<'src>>,
}

impl<'src> Lexer<'src> {
    pub fn new(source: &'src str) -> Self {
        Self {
            source,
            chars: source.char_indices().peekable(),
        }
    }

    fn current(&mut self) -> usize {
        self.chars.peek().map_or(self.source.len(), |(i, _)| *i)
    }
}

impl<'src> Iterator for Lexer<'src> {
    type Item = (Token<'src>, Span<usize>);

    fn next(&mut self) -> Option<Self::Item> {
        'find_next_token: while let Some((start, c)) = self.chars.next() {
            let tok = match c {
                '-' | '0'..='9' => {
                    while self.chars.next_if(|(_, c)| c.is_ascii_digit()).is_some() {}
                    Token::Num(&self.source[start..self.current()])
                }
                '_' | 'a'..='z' | 'A'..='Z' => {
                    while self
                        .chars
                        .next_if(|(_, c)| c.is_ascii_alphanumeric() || *c == '_')
                        .is_some()
                    {}
                    match &self.source[start..self.current()] {
                        "true" => Token::True,
                        "false" => Token::False,
                        name => Token::Ident(name),
                    }
                }
                '(' => Token::RoundOpen,
                ')' => Token::RoundClose,
                '/' => match self.chars.next() {
                    Some((_, '/')) => {
                        while self.chars.next().is_some_and(|(_, c)| c != '\n') {}
                        continue;
                    }
                    Some((_, '*')) => {
                        let mut nesting: u32 = 1;
                        'next_block_comment_char: loop {
                            match self.chars.next() {
                                Some((_, '*')) => {
                                    if self.chars.next_if(|(_, c)| *c == '/').is_some() {
                                        nesting -= 1;
                                    }
                                }
                                Some((_, '/')) => {
                                    if self.chars.next_if(|(_, c)| *c == '*').is_some() {
                                        nesting += 1;
                                    }
                                }
                                Some(_) => {}
                                None => break 'next_block_comment_char,
                            }
                            if nesting == 0 {
                                continue 'find_next_token;
                            }
                        }
                        Token::Error
                    }
                    _ => Token::Error,
                },
                ' ' | '\t' | '\n' | '\r' => continue,
                _ => Token::Error,
            };
            return Some((tok, Span::new(start, self.current())));
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lexer() {
        let tokens: Vec<_> = Lexer::new(
            r#"
            hello nice

            34279

            (-123 aaa) )) a_3473bob

            void true

            /*  /* ** / skibidi */    wow */

            %
            false
            "#,
        )
        .collect();
        use Token::*;
        assert_eq!(
            tokens.into_iter().map(|(t, _)| t).collect::<Vec<_>>(),
            [
                Ident("hello"),
                Ident("nice"),
                Num("34279"),
                RoundOpen,
                Num("-123"),
                Ident("aaa"),
                RoundClose,
                RoundClose,
                RoundClose,
                Ident("a_3473bob"),
                Ident("void"),
                True,
                Error,
                False
            ]
        );
    }
}
