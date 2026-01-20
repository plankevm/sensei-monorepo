use crate::{
    cst::{NodeIdx, TokenIdx, TokenIndex},
    error_report::LineIndex,
    lexer::{Lexer, SourceSpan},
};
use neosen_data::{IndexVec, Span};

use crate::cst::ConcreteSyntaxTree;

#[derive(Debug)]
pub struct DisplayCST<'src, 'ast> {
    line_index: LineIndex,
    token_source_offsets: IndexVec<TokenIndex, u32>,
    source: &'src str,
    cst: ConcreteSyntaxTree<'ast>,
    show_line: bool,
    show_node_index: bool,
}

#[derive(Debug)]
#[must_use]
struct Skibidi(Result<u32, u32>);

impl Drop for Skibidi {
    fn drop(&mut self) {}
}

impl<'src, 'ast> DisplayCST<'src, 'ast> {
    pub fn new(cst: ConcreteSyntaxTree<'ast>, source: &'src str) -> Self {
        DisplayCST {
            line_index: LineIndex::new(source),
            token_source_offsets: Lexer::new(source).map(|(_, span)| span.start).collect(), /* TODO: Lex once and accumulate */
            source,
            cst,
            show_line: false,
            show_node_index: false,
        }
    }

    pub fn show_line(mut self) -> Self {
        self.show_line = true;
        self
    }

    pub fn show_node_index(mut self) -> Self {
        self.show_node_index = true;
        self
    }

    fn token_src_span(&self, token: TokenIdx) -> SourceSpan {
        let start = self.token_source_offsets[token];
        let end =
            self.token_source_offsets.get(token + 1).copied().unwrap_or(self.source.len() as u32);
        Span::new(start, end)
    }

    fn token_src(&self, token: TokenIdx) -> &'src str {
        &self.source[self.token_src_span(token).usize_range()]
    }

    #[allow(dead_code)]
    fn token_span_to_src(&self, tokens: Span<TokenIdx>) -> SourceSpan {
        let start = self.token_source_offsets[tokens.start];
        let end = self
            .token_source_offsets
            .get(tokens.end + 1)
            .copied()
            .unwrap_or(self.source.len() as u32);
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

    fn used_probably(x: bool, b: Skibidi) {
        if x {
            let r = b.0;
            println!("r: {:?}", r);
        }
    }

    fn fmt_node(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        node_idx: NodeIdx,
        indent_level: u32,
    ) -> std::fmt::Result {
        Self::used_probably(false, Skibidi(Ok(3)));
        Self::write_indent(f, indent_level)?;
        let node = &self.cst.nodes[node_idx];
        write!(f, "{:?}", node.kind)?;
        if self.show_node_index {
            write!(f, " #{}", node_idx.get())?;
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

impl<'src, 'ast> std::fmt::Display for DisplayCST<'src, 'ast> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_node(f, ConcreteSyntaxTree::FILE_IDX, 0)
    }
}
