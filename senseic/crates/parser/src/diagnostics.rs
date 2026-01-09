use crate::lexer::SourceSpan;
use allocator_api2::vec::Vec;
use bumpalo::Bump;

#[derive(Debug, Clone)]
pub struct Diagnostic<'ast> {
    pub span: SourceSpan,
    pub message: &'ast str,
    pub notes: Vec<DiagnosticNote<'ast>, &'ast Bump>,
}

#[derive(Debug, Clone)]
pub struct DiagnosticNote<'ast> {
    pub span: Option<SourceSpan>,
    pub message: &'ast str,
}

pub struct DiagnosticsContext<'ast> {
    arena: &'ast Bump,
    errors: Vec<Diagnostic<'ast>, &'ast Bump>,
}

impl<'ast> DiagnosticsContext<'ast> {
    pub fn new(arena: &'ast Bump) -> Self {
        Self { arena, errors: Vec::new_in(arena) }
    }

    pub fn report(&mut self, span: SourceSpan, message: impl AsRef<str>) {
        let message = self.arena.alloc_str(message.as_ref());
        self.errors.push(Diagnostic { span, message, notes: Vec::new_in(self.arena) });
    }

    pub fn report_with_note(
        &mut self,
        span: SourceSpan,
        message: impl AsRef<str>,
        note: impl AsRef<str>,
    ) {
        let message = self.arena.alloc_str(message.as_ref());
        let note_message = self.arena.alloc_str(note.as_ref());
        let mut notes = Vec::new_in(self.arena);
        notes.push(DiagnosticNote { span: None, message: note_message });
        self.errors.push(Diagnostic { span, message, notes });
    }

    pub fn report_with_span_note(
        &mut self,
        span: SourceSpan,
        message: impl AsRef<str>,
        note_span: SourceSpan,
        note: impl AsRef<str>,
    ) {
        let message = self.arena.alloc_str(message.as_ref());
        let note_message = self.arena.alloc_str(note.as_ref());
        let mut notes = Vec::new_in(self.arena);
        notes.push(DiagnosticNote { span: Some(note_span), message: note_message });
        self.errors.push(Diagnostic { span, message, notes });
    }

    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    pub fn error_count(&self) -> usize {
        self.errors.len()
    }

    pub fn errors(&self) -> &[Diagnostic<'ast>] {
        &self.errors
    }

    pub fn into_errors(self) -> Vec<Diagnostic<'ast>, &'ast Bump> {
        self.errors
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use neosen_data::Span;

    #[test]
    fn test_new_context_has_no_errors() {
        let arena = Bump::new();
        let ctx = DiagnosticsContext::new(&arena);
        assert!(!ctx.has_errors());
        assert_eq!(ctx.error_count(), 0);
    }

    #[test]
    fn test_report_single_error() {
        let arena = Bump::new();
        let mut ctx = DiagnosticsContext::new(&arena);
        let span = Span::new(0, 5);
        ctx.report(span, "unexpected token");

        assert!(ctx.has_errors());
        assert_eq!(ctx.error_count(), 1);

        let errors = ctx.errors();
        assert_eq!(errors[0].message, "unexpected token");
        assert_eq!(errors[0].span.start, 0);
        assert_eq!(errors[0].span.end, 5);
        assert!(errors[0].notes.is_empty());
    }

    #[test]
    fn test_report_multiple_errors() {
        let arena = Bump::new();
        let mut ctx = DiagnosticsContext::new(&arena);

        ctx.report(Span::new(0, 3), "first error");
        ctx.report(Span::new(10, 15), "second error");
        ctx.report(Span::new(20, 25), "third error");

        assert_eq!(ctx.error_count(), 3);
        assert_eq!(ctx.errors()[0].message, "first error");
        assert_eq!(ctx.errors()[1].message, "second error");
        assert_eq!(ctx.errors()[2].message, "third error");
    }

    #[test]
    fn test_report_with_note() {
        let arena = Bump::new();
        let mut ctx = DiagnosticsContext::new(&arena);
        let span = Span::new(0, 5);
        ctx.report_with_note(span, "missing semicolon", "add ';' here");

        assert_eq!(ctx.error_count(), 1);
        let error = &ctx.errors()[0];
        assert_eq!(error.message, "missing semicolon");
        assert_eq!(error.notes.len(), 1);
        assert!(error.notes[0].span.is_none());
        assert_eq!(error.notes[0].message, "add ';' here");
    }

    #[test]
    fn test_report_with_span_note() {
        let arena = Bump::new();
        let mut ctx = DiagnosticsContext::new(&arena);
        let error_span = Span::new(10, 15);
        let note_span = Span::new(0, 5);
        ctx.report_with_span_note(
            error_span,
            "mismatched closing delimiter",
            note_span,
            "opening delimiter here",
        );

        assert_eq!(ctx.error_count(), 1);
        let error = &ctx.errors()[0];
        assert_eq!(error.span.start, 10);
        assert_eq!(error.notes.len(), 1);
        let note_span_actual = error.notes[0].span.expect("note should have span");
        assert_eq!(note_span_actual.start, note_span.start);
        assert_eq!(note_span_actual.end, note_span.end);
        assert_eq!(error.notes[0].message, "opening delimiter here");
    }

    #[test]
    fn test_into_errors_consumes_context() {
        let arena = Bump::new();
        let mut ctx = DiagnosticsContext::new(&arena);
        ctx.report(Span::new(0, 1), "error");

        let errors = ctx.into_errors();
        assert_eq!(errors.len(), 1);
    }
}
