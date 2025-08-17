//! Pretty-printing functionality for POD2 custom predicates

use std::fmt::Write;

use crate::{
    frontend::PodRequest,
    middleware::{
        CustomPredicate, CustomPredicateBatch, Predicate, StatementTmpl, StatementTmplArg, Value,
    },
};

/// Trait for converting AST nodes to Podlang source code
///
/// This trait provides a consistent interface for pretty-printing different
/// types of AST nodes back to their Podlang source representation.
pub trait PrettyPrint {
    /// Write this AST node to a source writer
    ///
    /// Uses default formatting with no indentation.
    fn fmt_podlang(&self, w: &mut dyn Write) -> std::fmt::Result {
        self.fmt_podlang_with_indent(w, 0)
    }

    /// Write this AST node to a source writer with custom indentation
    fn fmt_podlang_with_indent(&self, w: &mut dyn Write, indent: usize) -> std::fmt::Result;

    /// Convert this AST node to a Podlang source string
    ///
    /// Uses default formatting with no indentation.
    fn to_podlang_string(&self) -> String {
        self.to_podlang_string_with_indent(0)
    }

    /// Convert this AST node to a Podlang source string with custom indentation
    fn to_podlang_string_with_indent(&self, indent: usize) -> String {
        let mut result = String::new();
        let _ = self.fmt_podlang_with_indent(&mut result, indent);
        result
    }
}

impl PrettyPrint for CustomPredicate {
    fn fmt_podlang_with_indent(&self, w: &mut dyn Write, indent: usize) -> std::fmt::Result {
        fmt_predicate_definition(w, self, indent, None)
    }
}

impl PrettyPrint for StatementTmpl {
    fn fmt_podlang_with_indent(&self, w: &mut dyn Write, _indent: usize) -> std::fmt::Result {
        self.fmt_podlang_with_batch_context(w, None)
    }
}

impl StatementTmpl {
    fn fmt_podlang_with_batch_context(
        &self,
        w: &mut dyn Write,
        batch_context: Option<&CustomPredicateBatch>,
    ) -> std::fmt::Result {
        match &self.pred {
            Predicate::Native(native_pred) => {
                write!(w, "{}", native_pred)?;
            }
            Predicate::Custom(custom_ref) => {
                write!(w, "{}", custom_ref.predicate().name)?;
            }
            Predicate::BatchSelf(index) => {
                if let Some(batch) = batch_context {
                    if let Some(predicate) = batch.predicates.get(*index) {
                        write!(w, "{}", predicate.name)?;
                    } else {
                        write!(w, "batch_self_{}", index)?;
                    }
                } else {
                    write!(w, "batch_self_{}", index)?;
                }
            }
        }

        write!(w, "(")?;
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                write!(w, ", ")?;
            }
            arg.fmt_podlang(w)?;
        }
        write!(w, ")")?;

        Ok(())
    }
}

impl PrettyPrint for StatementTmplArg {
    fn fmt_podlang_with_indent(&self, w: &mut dyn Write, _indent: usize) -> std::fmt::Result {
        write!(w, "{}", self)
    }
}

impl PrettyPrint for CustomPredicateBatch {
    fn fmt_podlang_with_indent(&self, w: &mut dyn Write, indent: usize) -> std::fmt::Result {
        for (i, predicate) in self.predicates.iter().enumerate() {
            if i > 0 {
                write!(w, "\n\n")?;
            }
            self.fmt_predicate_with_context(w, predicate, indent)?;
        }
        Ok(())
    }
}

impl CustomPredicateBatch {
    fn fmt_predicate_with_context(
        &self,
        w: &mut dyn Write,
        predicate: &CustomPredicate,
        indent: usize,
    ) -> std::fmt::Result {
        fmt_predicate_definition(w, predicate, indent, Some(self))
    }
}

impl PrettyPrint for Value {
    fn fmt_podlang_with_indent(&self, w: &mut dyn Write, _indent: usize) -> std::fmt::Result {
        write!(w, "{}", self.typed())
    }
}

impl PrettyPrint for PodRequest {
    fn fmt_podlang_with_indent(&self, w: &mut dyn Write, _indent: usize) -> std::fmt::Result {
        write!(w, "REQUEST(")?;
        for (i, template) in self.request_templates.iter().enumerate() {
            if i > 0 {
                write!(w, ", ")?;
            }
            template.fmt_podlang_with_indent(w, 4)?;
        }
        write!(w, ")")
    }
}

fn fmt_predicate_definition(
    w: &mut dyn Write,
    predicate: &CustomPredicate,
    indent: usize,
    batch_context: Option<&CustomPredicateBatch>,
) -> std::fmt::Result {
    let base_indent = " ".repeat(indent);
    let statement_indent = " ".repeat(indent + 4);

    fmt_predicate_signature(w, predicate, &base_indent)?;

    let conjunction_str = if predicate.conjunction { "AND" } else { "OR" };
    writeln!(w, " = {}(", conjunction_str)?;

    for (i, statement) in predicate.statements.iter().enumerate() {
        if i > 0 {
            writeln!(w)?;
        }
        write!(w, "{}", statement_indent)?;
        statement.fmt_podlang_with_batch_context(w, batch_context)?;
    }

    write!(w, "\n{})", base_indent)
}

fn fmt_predicate_signature(
    w: &mut dyn Write,
    predicate: &CustomPredicate,
    base_indent: &str,
) -> std::fmt::Result {
    write!(w, "{}{}", base_indent, predicate.name)?;
    write!(w, "(")?;

    let mut public_args = predicate
        .wildcard_names
        .iter()
        .take(predicate.args_len)
        .peekable();
    while let Some(arg_name) = public_args.next() {
        write!(w, "{}", arg_name)?;
        if public_args.peek().is_some() {
            write!(w, ", ")?;
        }
    }

    let mut private_args = predicate
        .wildcard_names
        .iter()
        .skip(predicate.args_len)
        .peekable();
    if private_args.peek().is_some() {
        if predicate.args_len > 0 {
            write!(w, ", ")?;
        }
        write!(w, "private: ")?;
        while let Some(arg_name) = private_args.next() {
            write!(w, "{}", arg_name)?;
            if private_args.peek().is_some() {
                write!(w, ", ")?;
            }
        }
    }

    write!(w, ")")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        backends::plonky2::primitives::ec::schnorr::SecretKey,
        lang::parse,
        middleware::{
            CustomPredicate, Key, NativePredicate, Params, Predicate, StatementTmpl,
            StatementTmplArg, Value, Wildcard,
        },
    };

    fn create_test_wildcard(name: &str, index: usize) -> Wildcard {
        Wildcard::new(name.to_string(), index)
    }

    #[test]
    fn test_simple_predicate_pretty_print() {
        let params = Params::default();

        // Create a simple predicate: is_equal(PodA, PodB) = AND(Equal(?PodA["key"], ?PodB["key"]))
        let statements = vec![StatementTmpl {
            pred: Predicate::Native(NativePredicate::Equal),
            args: vec![
                StatementTmplArg::AnchoredKey(
                    create_test_wildcard("PodA", 0),
                    Key::new("key".to_string()),
                ),
                StatementTmplArg::AnchoredKey(
                    create_test_wildcard("PodB", 1),
                    Key::new("key".to_string()),
                ),
            ],
        }];

        let predicate = CustomPredicate::and(
            &params,
            "is_equal".to_string(),
            statements,
            2, // args_len (PodA, PodB are public)
            vec!["PodA".to_string(), "PodB".to_string()],
        )
        .unwrap();

        let pretty_printed = predicate.to_podlang_string();

        let expected = r#"is_equal(PodA, PodB) = AND(
    Equal(?PodA["key"], ?PodB["key"])
)"#;
        assert_eq!(pretty_printed, expected);
    }

    #[test]
    fn test_predicate_with_private_args() {
        let params = Params::default();

        // Create: uses_private(A, private: Temp) = AND(Equal(?A["input"], ?Temp["const"]))
        let statements = vec![StatementTmpl {
            pred: Predicate::Native(NativePredicate::Equal),
            args: vec![
                StatementTmplArg::AnchoredKey(
                    create_test_wildcard("A", 0),
                    Key::new("input".to_string()),
                ),
                StatementTmplArg::AnchoredKey(
                    create_test_wildcard("Temp", 1),
                    Key::new("const".to_string()),
                ),
            ],
        }];

        let predicate = CustomPredicate::and(
            &params,
            "uses_private".to_string(),
            statements,
            1, // args_len (only A is public)
            vec!["A".to_string(), "Temp".to_string()],
        )
        .unwrap();

        let pretty_printed = predicate.to_podlang_string();

        let expected = r#"uses_private(A, private: Temp) = AND(
    Equal(?A["input"], ?Temp["const"])
)"#;
        assert_eq!(pretty_printed, expected);
    }

    #[test]
    fn test_statement_with_literal_args() {
        let params = Params::default();

        // Create: check_value(Pod) = AND(Equal(?Pod["field"], 42))
        let statements = vec![StatementTmpl {
            pred: Predicate::Native(NativePredicate::Equal),
            args: vec![
                StatementTmplArg::AnchoredKey(
                    create_test_wildcard("Pod", 0),
                    Key::new("field".to_string()),
                ),
                StatementTmplArg::Literal(Value::from(42i64)),
            ],
        }];

        let predicate = CustomPredicate::and(
            &params,
            "check_value".to_string(),
            statements,
            1,
            vec!["Pod".to_string()],
        )
        .unwrap();

        let pretty_printed = predicate.to_podlang_string();

        let expected = r#"check_value(Pod) = AND(
    Equal(?Pod["field"], 42)
)"#;
        assert_eq!(pretty_printed, expected);
    }

    #[test]
    fn test_or_predicate() {
        let params = Params::default();

        // Create: either_or(A, B) = OR(Equal(?A["x"], 1), Equal(?B["y"], 2))
        let statements = vec![
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    StatementTmplArg::AnchoredKey(
                        create_test_wildcard("A", 0),
                        Key::new("x".to_string()),
                    ),
                    StatementTmplArg::Literal(Value::from(1i64)),
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    StatementTmplArg::AnchoredKey(
                        create_test_wildcard("B", 1),
                        Key::new("y".to_string()),
                    ),
                    StatementTmplArg::Literal(Value::from(2i64)),
                ],
            },
        ];

        let predicate = CustomPredicate::or(
            &params,
            "either_or".to_string(),
            statements,
            2,
            vec!["A".to_string(), "B".to_string()],
        )
        .unwrap();

        let pretty_printed = predicate.to_podlang_string();

        let expected = r#"either_or(A, B) = OR(
    Equal(?A["x"], 1)
    Equal(?B["y"], 2)
)"#;
        assert_eq!(pretty_printed, expected);
    }

    /// Helper function for round-trip testing
    fn assert_round_trip(input: &str) {
        let params = Params::default();
        let available_batches = &[];

        // Step 1: Parse the input
        let parsed_result =
            parse(input, &params, available_batches).expect("Initial parsing should succeed");

        // Step 2: Pretty-print the parsed batch
        let pretty_printed = parsed_result.custom_batch.to_podlang_string();

        // Step 3: Parse the pretty-printed result
        let reparsed_result =
            parse(&pretty_printed, &params, available_batches).expect("Reparsing should succeed");

        // Step 4: Verify the ASTs are equivalent
        assert_eq!(
            parsed_result.custom_batch.predicates, reparsed_result.custom_batch.predicates,
            "Original AST should match reparsed AST.\nOriginal input:\n{}\nPretty-printed:\n{}\n",
            input, pretty_printed
        );
    }

    #[test]
    fn test_round_trip_simple_predicate() {
        let input = r#"
            simple_equal(PodA, PodB) = AND(
                Equal(?PodA["key"], ?PodB["key"])
            )
        "#;
        assert_round_trip(input);
    }

    #[test]
    fn test_round_trip_predicate_with_private_args() {
        let input = r#"
            uses_private(A, private: Temp) = AND(
                Equal(?A["input_key"], ?Temp["const_key"])
                Equal(?Temp["const_key"], "some_value")
            )
        "#;
        assert_round_trip(input);
    }

    #[test]
    fn test_round_trip_or_predicate() {
        let input = r#"
            either_condition(X, Y) = OR(
                Equal(?X["status"], "active")
                Equal(?Y["type"], 1)
            )
        "#;
        assert_round_trip(input);
    }

    #[test]
    fn test_round_trip_multiple_predicates() {
        let input = r#"
            pred_one(A) = AND(
                Equal(?A["field"], 42)
            )

            pred_two(B, C) = AND(
                Equal(?B["value"], ?C["value"])
                NotEqual(?B["id"], ?C["id"])
            )
        "#;
        assert_round_trip(input);
    }

    #[test]
    fn test_round_trip_various_literals() {
        let input = r#"
            literal_test(Pod) = AND(
                Equal(?Pod["int_field"], 123)
                Equal(?Pod["string_field"], "hello world")
                Equal(?Pod["bool_field"], true)
                NotEqual(?Pod["other_bool"], false)
            )
        "#;
        assert_round_trip(input);
    }

    #[test]
    fn test_round_trip_complex_predicate() {
        let input = r#"
            complex_predicate(User, Document, private: Verifier, Timestamp) = AND(
                Equal(?User["active"], true)
                Equal(?Document["owner"], ?User["id"])
                Equal(?Verifier["type"], 1)
                Lt(?Timestamp["created"], ?Timestamp["expires"])
                NotContains(?Document["blocked_users"], ?User["id"])
            )
        "#;
        assert_round_trip(input);
    }

    #[test]
    fn test_round_trip_with_sum_and_hash_operations() {
        let input = r#"
            math_operations(A, B, C) = AND(
                SumOf(?A["value"], ?B["value"], ?C["total"])
                ProductOf(?A["factor"], ?B["factor"], ?C["product"])
                MaxOf(?A["score"], ?B["score"], ?C["max_score"])
                HashOf(?A["data"], ?B["salt"], ?C["hash"])
            )
        "#;
        assert_round_trip(input);
    }

    #[test]
    fn test_round_trip_nested_custom_calls() {
        let input = r#"
            base_check(Pod) = AND(
                Equal(?Pod["status"], "valid")
            )

            derived_check(PodA, PodB) = AND(
                base_check(?PodA)
                base_check(?PodB)
                NotEqual(?PodA["id"], ?PodB["id"])
            )
        "#;
        assert_round_trip(input);
    }

    #[test]
    fn test_round_trip_container_operations() {
        let input = r#"
            container_checks(List, Item, Dict, Key, Value) = AND(
                Contains(?List, ?Item, ?Value)
                NotContains(?Dict, ?Key)
            )
        "#;
        assert_round_trip(input);
    }

    #[test]
    fn test_round_trip_secret_key() {
        let sk = SecretKey::new_rand();
        let input = format!(
            r#"
            secret_key_test(Pod) = AND(
                Equal(?Pod["sk"], {})
            )
            "#,
            Value::from(sk.clone()).to_podlang_string()
        );
        assert_round_trip(&input);
    }

    #[test]
    fn test_round_trip_self() {
        let input = r#"
            self_test(Pod) = AND(
                Equal(?Pod["self"], SELF)
            )
        "#;
        assert_round_trip(input);
    }

    #[test]
    fn test_pretty_print_demonstration() {
        let input = r#"
            base_check(Pod) = AND(
                Equal(?Pod["status"], "valid")
            )

            derived_check(PodA, PodB) = AND(
                base_check(?PodA)
                base_check(?PodB)
                NotEqual(?PodA["id"], ?PodB["id"])
            )
        "#;

        let params = Params::default();
        let parsed_result = parse(input, &params, &[]).expect("Parsing should succeed");

        let pretty_printed = parsed_result.custom_batch.to_podlang_string();

        println!("Original input:\n{}", input);
        println!("\nPretty-printed output:\n{}", pretty_printed);

        let reparsed = parse(&pretty_printed, &params, &[]).expect("Reparsing should succeed");

        assert_eq!(
            parsed_result.custom_batch.predicates,
            reparsed.custom_batch.predicates
        );
    }

    #[test]
    fn test_value_pretty_print_string_escaping() {
        // Test basic string
        let value = Value::from("hello world");
        assert_eq!(value.to_podlang_string(), "\"hello world\"");

        // Test string with quotes
        let value = Value::from("say \"hello\"");
        assert_eq!(value.to_podlang_string(), "\"say \\\"hello\\\"\"");

        // Test string with backslashes
        let value = Value::from("path\\to\\file");
        assert_eq!(value.to_podlang_string(), "\"path\\\\to\\\\file\"");

        // Test string with newlines
        let value = Value::from("line1\nline2");
        assert_eq!(value.to_podlang_string(), "\"line1\\nline2\"");

        // Test string with tabs
        let value = Value::from("col1\tcol2");
        assert_eq!(value.to_podlang_string(), "\"col1\\tcol2\"");

        // Test string with multiple escape sequences
        let value = Value::from("\"quote\"\n\\backslash\\\ttab");
        assert_eq!(
            value.to_podlang_string(),
            "\"\\\"quote\\\"\\n\\\\backslash\\\\\\ttab\""
        );
    }

    #[test]
    fn test_string_escaping_round_trip() {
        let test_cases = vec![
            "simple string",
            "string with \"quotes\"",
            "string with \\backslashes\\",
            "string with\nnewlines",
            "string with\ttabs",
            "mixed: \"quotes\" and \\backslashes\\ and\nnewlines",
            "unicode: café résumé",
            "", // empty string
        ];

        for test_string in test_cases {
            let input = format!(
                r#"
                test_pred(Pod) = AND(
                    Equal(?Pod["field"], "{}")
                )
                "#,
                // Manually escape for the input - this simulates what would be in actual Podlang source
                test_string
                    .replace('\\', "\\\\")
                    .replace('"', "\\\"")
                    .replace('\n', "\\n")
                    .replace('\t', "\\t")
            );

            let params = Params::default();
            let parsed_result = parse(&input, &params, &[]).expect("Should parse successfully");

            let pretty_printed = parsed_result.custom_batch.to_podlang_string();

            let reparsed_result =
                parse(&pretty_printed, &params, &[]).expect("Should reparse successfully");

            assert_eq!(
                parsed_result.custom_batch.predicates, reparsed_result.custom_batch.predicates,
                "Round-trip failed for string: {:?}\nPretty-printed: {}",
                test_string, pretty_printed
            );
        }
    }
}
