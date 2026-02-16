use crate::{
    cst::NodeIdx,
    error_report::LineIndex,
    lexer::{Lexed, SourceSpan, TokenIdx},
};
use sensei_core::{Idx, Span};

use crate::cst::ConcreteSyntaxTree;

#[derive(Debug)]
pub struct DisplayCST<'src, 'lexed, 'ast> {
    line_index: LineIndex,
    lexed: &'lexed Lexed,
    source: &'src str,
    cst: &'ast ConcreteSyntaxTree,
    show_line: bool,
    show_node_index: bool,
    show_token_spans: bool,
}

impl<'src, 'lexed, 'ast> DisplayCST<'src, 'lexed, 'ast> {
    pub fn new(cst: &'ast ConcreteSyntaxTree, source: &'src str, lexed: &'lexed Lexed) -> Self {
        DisplayCST {
            line_index: LineIndex::new(source),
            lexed,
            source,
            cst,
            show_line: false,
            show_node_index: false,
            show_token_spans: false,
        }
    }

    pub fn show_line(mut self, show: bool) -> Self {
        self.show_line = show;
        self
    }

    pub fn show_node_index(mut self, show: bool) -> Self {
        self.show_node_index = show;
        self
    }

    pub fn show_token_spans(mut self, show: bool) -> Self {
        self.show_token_spans = show;
        self
    }

    fn token_src_span(&self, token: TokenIdx) -> SourceSpan {
        self.lexed.get_span(token)
    }

    fn token_src(&self, token: TokenIdx) -> &'src str {
        &self.source[self.token_src_span(token).usize_range()]
    }

    #[allow(dead_code)]
    fn token_span_to_src(&self, tokens: Span<TokenIdx>) -> SourceSpan {
        let start = self.lexed.get_span(tokens.start).start;
        let end = self.lexed.get_span(tokens.end).end;
        Span::new(start, end)
    }

    fn write_indent(f: &mut std::fmt::Formatter<'_>, level: u32) -> std::fmt::Result {
        for _ in 0..level {
            write!(f, "    ")?
        }
        Ok(())
    }

    fn write_token_span(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        tokens: Span<TokenIdx>,
        indent_level: u32,
    ) -> std::fmt::Result {
        for ti in tokens.iter() {
            let src_span = self.token_src_span(ti);

            Self::write_indent(f, indent_level)?;
            write!(f, "{:?}", self.token_src(ti),)?;
            if self.show_line {
                let (start_line, start_col) = self.line_index.line_col(src_span.start);
                let (end_line, end_col) = self.line_index.line_col(src_span.end - 1);
                write!(f, " {}:{}-{}:{}", start_line, start_col, end_line, end_col)?
            }
            writeln!(f)?;
        }
        Ok(())
    }

    fn fmt_node(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        node_idx: NodeIdx,
        indent_level: u32,
    ) -> std::fmt::Result {
        Self::write_indent(f, indent_level)?;
        let node = &self.cst.nodes[node_idx];
        write!(f, "{:?}", node.kind)?;
        if self.show_node_index {
            write!(f, " #{}", node_idx.get())?;
        }
        if self.show_token_spans {
            write!(f, " [{}]", node.tokens)?;
        }
        writeln!(f)?;

        let mut last_token_idx = node.tokens.start;
        let mut next_child = node.first_child;
        while let Some(child_index) = next_child {
            let child = &self.cst.nodes[child_index];

            self.write_token_span(
                f,
                Span::new(last_token_idx, child.tokens.start),
                indent_level + 1,
            )?;

            self.fmt_node(f, child_index, indent_level + 1)?;

            last_token_idx = child.tokens.end;
            next_child = child.next_sibling;
        }

        self.write_token_span(f, Span::new(last_token_idx, node.tokens.end), indent_level + 1)?;

        Ok(())
    }
}

impl<'src, 'lexed, 'ast> std::fmt::Display for DisplayCST<'src, 'lexed, 'ast> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_node(f, ConcreteSyntaxTree::FILE_IDX, 0)
    }
}
