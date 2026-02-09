//! Rich error rendering for Podlang diagnostics.
//!
//! Provides [`render_error`], which takes a source string and a [`LangError`] and produces
//! a human-readable, source-annotated error message (similar to `rustc` output).

use annotate_snippets::{Level, Renderer, Snippet};

use crate::lang::{
    error::{LangError, LangErrorKind, ValidationError},
    frontend_ast::Span,
    parser::ParseError,
};

/// Render a [`LangError`] with source context into a human-readable diagnostic string.
///
/// Uses `Renderer::plain()` (no ANSI codes) so the output is stable for tests and log-safe.
///
/// - `source`: the full Podlang source text that was parsed.
/// - `path`: optional file path for the `-->` origin line.
/// - `error`: the error to render.
pub fn render_error(source: &str, path: Option<&str>, error: &LangError) -> String {
    let renderer = Renderer::plain();
    match &error.kind {
        LangErrorKind::Validation(e) => render_validation_error(&renderer, source, path, e),
        LangErrorKind::Parse(e) => render_parse_error(&renderer, source, path, e),
        LangErrorKind::Lowering(_)
        | LangErrorKind::Batching(_)
        | LangErrorKind::Middleware(_)
        | LangErrorKind::Frontend(_) => render_title_only(&renderer, &error.kind.to_string()),
    }
}

/// Render an error with only a title line and no source snippet.
fn render_title_only(renderer: &Renderer, message: &str) -> String {
    let msg = Level::Error.title(message);
    renderer.render(msg).to_string()
}

/// Render an error with a single annotated span in the source.
fn render_with_span(
    renderer: &Renderer,
    source: &str,
    path: Option<&str>,
    title: &str,
    span: &Span,
    label: &str,
) -> String {
    let annotation = Level::Error.span(span.start..span.end).label(label);
    let snippet = build_snippet(source, path).annotation(annotation);
    let msg = Level::Error.title(title).snippet(snippet);
    renderer.render(msg).to_string()
}

/// Render an error with an optional span — delegates to `render_with_span` or `render_title_only`.
fn render_with_optional_span(
    renderer: &Renderer,
    source: &str,
    path: Option<&str>,
    title: &str,
    span: Option<&Span>,
    label: &str,
) -> String {
    match span {
        Some(span) => render_with_span(renderer, source, path, title, span, label),
        None => render_title_only(renderer, title),
    }
}

/// Render an error with two annotated spans (e.g. first definition + duplicate).
#[allow(clippy::too_many_arguments)]
fn render_dual_span(
    renderer: &Renderer,
    source: &str,
    path: Option<&str>,
    title: &str,
    first_span: Option<&Span>,
    first_label: &str,
    second_span: Option<&Span>,
    second_label: &str,
) -> String {
    let mut snippet = build_snippet(source, path);
    if let Some(s) = first_span {
        snippet = snippet.annotation(Level::Info.span(s.start..s.end).label(first_label));
    }
    if let Some(s) = second_span {
        snippet = snippet.annotation(Level::Error.span(s.start..s.end).label(second_label));
    }
    let msg = Level::Error.title(title).snippet(snippet);
    renderer.render(msg).to_string()
}

/// Build a `Snippet` with source and optional path, ready for annotations.
fn build_snippet<'a>(source: &'a str, path: Option<&'a str>) -> Snippet<'a> {
    let mut snippet = Snippet::source(source).fold(true);
    if let Some(p) = path {
        snippet = snippet.origin(p);
    }
    snippet
}

// ---------------------------------------------------------------------------
// Validation errors
// ---------------------------------------------------------------------------

fn render_validation_error(
    renderer: &Renderer,
    source: &str,
    path: Option<&str>,
    error: &ValidationError,
) -> String {
    match error {
        ValidationError::UndefinedWildcard {
            name,
            pred_name,
            span,
        } => {
            let title = format!("undefined wildcard `{}`", name);
            let label = format!("not declared in predicate `{}`", pred_name);
            render_with_optional_span(renderer, source, path, &title, span.as_ref(), &label)
        }

        ValidationError::UndefinedPredicate { name, span } => {
            let title = format!("undefined predicate: {}", name);
            render_with_optional_span(
                renderer,
                source,
                path,
                &title,
                span.as_ref(),
                "not defined or imported",
            )
        }

        ValidationError::DuplicatePredicate {
            name,
            first_span,
            second_span,
        } => {
            let title = format!("duplicate predicate definition: {}", name);
            render_dual_span(
                renderer,
                source,
                path,
                &title,
                first_span.as_ref(),
                "first definition here",
                second_span.as_ref(),
                "duplicate definition",
            )
        }

        ValidationError::ArgumentCountMismatch {
            predicate,
            expected,
            found,
            span,
        } => {
            let title = format!("argument count mismatch for `{}`", predicate);
            let label = format!("expected {} arguments, found {}", expected, found);
            render_with_optional_span(renderer, source, path, &title, span.as_ref(), &label)
        }

        ValidationError::MultipleRequestDefinitions {
            first_span,
            second_span,
        } => render_dual_span(
            renderer,
            source,
            path,
            "multiple REQUEST definitions found",
            first_span.as_ref(),
            "first REQUEST here",
            second_span.as_ref(),
            "second REQUEST here",
        ),

        ValidationError::InvalidArgumentType { predicate, span } => {
            let title = format!("invalid argument type for `{}`", predicate);
            render_with_optional_span(
                renderer,
                source,
                path,
                &title,
                span.as_ref(),
                "anchored keys not allowed here",
            )
        }

        ValidationError::DuplicateWildcard { name, span } => {
            let title = format!("duplicate wildcard: {}", name);
            render_with_optional_span(
                renderer,
                source,
                path,
                &title,
                span.as_ref(),
                "already declared",
            )
        }

        ValidationError::EmptyStatementList { context, span } => {
            let title = format!("empty statement list in {}", context);
            render_with_optional_span(
                renderer,
                source,
                path,
                &title,
                span.as_ref(),
                "no statements",
            )
        }

        ValidationError::InvalidHash { hash, span } => {
            let title = format!("invalid hash: {}", hash);
            render_with_optional_span(
                renderer,
                source,
                path,
                &title,
                span.as_ref(),
                "invalid hash",
            )
        }

        ValidationError::DuplicateImport { name, span } => {
            let title = format!("duplicate import name: {}", name);
            render_with_optional_span(
                renderer,
                source,
                path,
                &title,
                span.as_ref(),
                "already imported",
            )
        }

        ValidationError::ImportArityMismatch {
            expected,
            found,
            span,
        } => {
            let title = "import arity mismatch".to_string();
            let label = format!("expected {}, found {}", expected, found);
            render_with_optional_span(renderer, source, path, &title, span.as_ref(), &label)
        }

        ValidationError::ModuleNotFound { name, span } => {
            let title = format!("module not found: {}", name);
            render_with_optional_span(
                renderer,
                source,
                path,
                &title,
                span.as_ref(),
                "no module with this hash was provided",
            )
        }

        ValidationError::WildcardPredicateNameCollision { name } => {
            let title = format!("wildcard '{}' collides with a predicate name", name);
            render_title_only(renderer, &title)
        }

        ValidationError::PredicatesNotAllowedInRequest { span } => render_with_optional_span(
            renderer,
            source,
            path,
            "predicate definitions are not allowed in requests",
            span.as_ref(),
            "not allowed here",
        ),

        ValidationError::RequestNotAllowedInModule { span } => render_with_optional_span(
            renderer,
            source,
            path,
            "REQUEST block is not allowed in modules",
            span.as_ref(),
            "not allowed here",
        ),

        ValidationError::NoPredicatesInModule => render_title_only(
            renderer,
            "modules must contain at least one predicate definition",
        ),

        ValidationError::NoRequestBlock => {
            render_title_only(renderer, "requests must contain a REQUEST block")
        }
    }
}

// ---------------------------------------------------------------------------
// Parse errors
// ---------------------------------------------------------------------------

fn render_parse_error(
    renderer: &Renderer,
    source: &str,
    path: Option<&str>,
    error: &ParseError,
) -> String {
    match error {
        ParseError::Pest(pest_err) => {
            let span = span_from_pest_location(&pest_err.location);
            let label = format_pest_label(pest_err);
            render_with_span(renderer, source, path, "syntax error", &span, &label)
        }
        _ => render_title_only(renderer, &error.to_string()),
    }
}

/// Extract a byte-offset [`Span`] from a pest `InputLocation`.
fn span_from_pest_location(location: &pest::error::InputLocation) -> Span {
    match *location {
        pest::error::InputLocation::Pos(pos) => Span {
            start: pos,
            end: pos + 1,
        },
        pest::error::InputLocation::Span((start, end)) => Span { start, end },
    }
}

/// Format the expectations from a pest error into a readable label.
fn format_pest_label<R: std::fmt::Debug>(error: &pest::error::Error<R>) -> String {
    match &error.variant {
        pest::error::ErrorVariant::ParsingError {
            positives,
            negatives,
        } => {
            let mut parts = Vec::new();
            if !positives.is_empty() {
                let names: Vec<String> = positives.iter().map(|r| format!("{:?}", r)).collect();
                parts.push(format!("expected {}", names.join(", ")));
            }
            if !negatives.is_empty() {
                let names: Vec<String> = negatives.iter().map(|r| format!("{:?}", r)).collect();
                parts.push(format!("unexpected {}", names.join(", ")));
            }
            if parts.is_empty() {
                "unexpected input".to_string()
            } else {
                parts.join("; ")
            }
        }
        pest::error::ErrorVariant::CustomError { message } => message.clone(),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use crate::lang::error::BatchingError;

    /// Load a module from source and extract the error, or panic.
    fn module_err(source: &str) -> LangError {
        crate::lang::load_module(source, "test", &crate::middleware::Params::default(), &[])
            .unwrap_err()
    }

    /// Parse a request from source and extract the error, or panic.
    fn request_err(source: &str) -> LangError {
        crate::lang::parse_request(source, &crate::middleware::Params::default(), &[]).unwrap_err()
    }

    #[test]
    fn test_undefined_wildcard() {
        let source = r#"
my_pred(A, private: B) = AND(
    Equal(A["key"], C["other"])
)
"#;
        let err = module_err(source);
        let rendered = render_error(source, Some("test.podlang"), &err);

        assert!(
            rendered.contains("undefined wildcard"),
            "rendered: {rendered}"
        );
        assert!(rendered.contains("C"), "rendered: {rendered}");
        assert!(rendered.contains("my_pred"), "rendered: {rendered}");
        assert!(rendered.contains("test.podlang"), "rendered: {rendered}");
    }

    #[test]
    fn test_undefined_predicate() {
        let source = r#"
REQUEST(
    NoSuchPred(A, B)
)
"#;
        let err = request_err(source);
        let rendered = render_error(source, Some("test.podlang"), &err);

        assert!(
            rendered.contains("undefined predicate"),
            "rendered: {rendered}"
        );
        assert!(rendered.contains("NoSuchPred"), "rendered: {rendered}");
    }

    #[test]
    fn test_duplicate_predicate() {
        let source = r#"
my_pred(A) = AND(Equal(A["x"], 1))
my_pred(B) = AND(Equal(B["y"], 2))
"#;
        let err = module_err(source);
        let rendered = render_error(source, Some("test.podlang"), &err);

        assert!(
            rendered.contains("duplicate predicate"),
            "rendered: {rendered}"
        );
        assert!(
            rendered.contains("first definition"),
            "rendered: {rendered}"
        );
        assert!(
            rendered.contains("duplicate definition"),
            "rendered: {rendered}"
        );
    }

    #[test]
    fn test_argument_count_mismatch() {
        let source = r#"
REQUEST(
    Equal(A["x"], B["y"], C["z"])
)
"#;
        let err = request_err(source);
        let rendered = render_error(source, Some("test.podlang"), &err);

        assert!(
            rendered.contains("argument count mismatch"),
            "rendered: {rendered}"
        );
        assert!(rendered.contains("Equal"), "rendered: {rendered}");
    }

    #[test]
    fn test_pest_syntax_error() {
        let source = "REQUEST(!!!invalid!!!";
        let err = request_err(source);
        let rendered = render_error(source, Some("test.podlang"), &err);

        assert!(
            rendered.contains("syntax error") || rendered.contains("error"),
            "rendered: {rendered}"
        );
    }

    #[test]
    fn test_no_path() {
        let source = r#"
REQUEST(
    NoSuchPred(A, B)
)
"#;
        let err = request_err(source);
        let rendered = render_error(source, None, &err);

        assert!(
            rendered.contains("undefined predicate"),
            "rendered: {rendered}"
        );
        assert!(
            !rendered.contains("-->"),
            "should not have path line, rendered: {rendered}"
        );
    }

    #[test]
    fn test_error_without_span() {
        let error = LangError::from(BatchingError::Internal {
            message: "something went wrong".to_string(),
        });
        let rendered = render_error("", None, &error);

        assert!(
            rendered.contains("something went wrong"),
            "rendered: {rendered}"
        );
    }
}
