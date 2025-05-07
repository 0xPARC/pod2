use pest::{iterators::Pairs, Parser};
use pest_derive::Parser;

// Link to the grammar file
#[derive(Parser)]
#[grammar = "lang/grammar.pest"]
pub struct PodlogParser;

// Enum of possible parsing errors (can be expanded later)
// Using thiserror for structured errors
#[derive(thiserror::Error, Debug)]
pub enum ParseError {
    #[error("Pest parsing error: {0}")]
    Pest(#[from] Box<pest::error::Error<Rule>>),
    // Add more specific semantic errors later if needed during AST construction
}

// Implement From so `?` can convert the original error to the Boxed version
impl From<pest::error::Error<Rule>> for ParseError {
    fn from(err: pest::error::Error<Rule>) -> Self {
        ParseError::Pest(Box::new(err))
    }
}

/// Parses a Podlog input string according to the grammar rules.
///
/// Returns a Result containing the parsed pairs or a ParseError.
pub fn parse_podlog(input: &str) -> Result<Pairs<'_, Rule>, ParseError> {
    let pairs = PodlogParser::parse(Rule::document, input)?;
    // The result of parse is Pairs<'i, Rule>
    // At this stage, we just return the successful parse result (Pairs)
    // or the Pest error wrapped in our ParseError.
    Ok(pairs)
}

// Basic test module
#[cfg(test)]
mod tests {
    use super::*;

    // Helper function to check if a string parses successfully for a given rule
    fn assert_parses(rule: Rule, input: &str) {
        match PodlogParser::parse(rule, input) {
            Ok(_) => (), // Successfully parsed
            Err(e) => panic!("Failed to parse input:\n{}\nError: {}", input, e),
        }
    }

    // Helper function to check if a string fails to parse for a given rule
    fn assert_fails(rule: Rule, input: &str) {
        match PodlogParser::parse(rule, input) {
            Ok(pairs) => panic!(
                "Expected parse to fail, but it succeeded. Parsed:\n{:#?}",
                pairs
            ),
            Err(_) => (), // Failed as expected
        }
    }

    #[test]
    fn test_parse_empty() {
        assert_parses(Rule::document, "");
        assert_parses(Rule::document, " ");
        assert_parses(Rule::document, "\n\n");
        assert_parses(Rule::document, "// comment only");
    }

    #[test]
    fn test_parse_comment() {
        assert_parses(Rule::document, "// This is a comment\n");
        assert_parses(Rule::document, " // Indented comment");
    }

    #[test]
    fn test_parse_identifier() {
        assert_parses(Rule::identifier, "my_pred");
        assert_parses(Rule::identifier, "_internal");
        assert_parses(Rule::identifier, "ValidName123");
        assert_fails(Rule::test_identifier, "?invalid"); // Use test rule
        assert_fails(Rule::test_identifier, "1_invalid_start"); // Use test rule
        assert_fails(Rule::test_identifier, "invalid-char"); // Use test rule
    }

    #[test]
    fn test_parse_variable() {
        assert_parses(Rule::variable, "?Var");
        assert_parses(Rule::variable, "?_Internal");
        assert_parses(Rule::variable, "?X1");
        assert_fails(Rule::test_variable, "NotAVar"); // Use test rule
        assert_fails(Rule::test_variable, "?"); // Use test rule
        assert_fails(Rule::test_variable, "?invalid-char"); // Use test rule
    }

    #[test]
    fn test_parse_anchored_key() {
        assert_parses(Rule::anchored_key, "?PodVar[\"literal_key\"]");
        assert_parses(Rule::anchored_key, "?PodVar[?KeyVar]");
        assert_fails(Rule::anchored_key, "PodVar[\"key\"]"); // Needs variable for pod
        assert_fails(Rule::anchored_key, "?PodVar[invalid_key]"); // Key must be literal string or var
        assert_fails(Rule::anchored_key, "?PodVar[]"); // Key cannot be empty
    }

    #[test]
    fn test_parse_literals() {
        // Int
        assert_parses(Rule::literal_int, "123");
        assert_parses(Rule::literal_int, "-45");
        assert_parses(Rule::literal_int, "0");
        assert_fails(Rule::test_literal_int, "1.23"); // Use test_literal_int rule
                                                      // Bool
        assert_parses(Rule::literal_bool, "true");
        assert_parses(Rule::literal_bool, "false");

        // Raw - Allow any even number of hex digits >= 2
        assert_parses(Rule::literal_raw, "0x00"); // 2 digits is 1 pair
        assert_parses(Rule::literal_raw, "0xabcd");
        assert_parses(Rule::literal_raw, "0xDEADbeef0123");
        let long_valid_raw = format!("0x{}", "a".repeat(64)); // 64 is even
        assert_parses(Rule::literal_raw, &long_valid_raw);

        // Use anchored rule for failure cases
        assert_fails(Rule::test_literal_raw, "0xabc"); // Fails (odd number of digits)
        assert_fails(Rule::test_literal_raw, "0x1"); // Fails (odd number of digits)
        assert_fails(Rule::test_literal_raw, "0x"); // Fails (needs at least one pair)
        assert_fails(Rule::test_literal_raw, "0xGG"); // Fails (invalid hex chars)
                                                      // assert_fails(Rule::test_literal_raw, &format!("0x{}", "a".repeat(62))); // This should pass now
                                                      // assert_fails(Rule::test_literal_raw, &format!("0x{}", "a".repeat(66))); // This should pass now

        // String
        assert_parses(Rule::literal_string, "\"hello\"");
        assert_parses(Rule::literal_string, "\"escaped \\\" quote\"");
        assert_parses(Rule::literal_string, "\"\\\\ backslash\"");
        assert_parses(Rule::literal_string, "\"\\uABCD\"");
        assert_fails(Rule::literal_string, "\"unterminated");
        // Array
        assert_parses(Rule::literal_array, "[]");
        assert_parses(Rule::literal_array, "[1, \"two\", true]");
        assert_parses(Rule::literal_array, "[ [1], #[2] ]"); // Nested
                                                             // Set
        assert_parses(Rule::literal_set, "#[]");
        assert_parses(Rule::literal_set, "#[1, 2, 3]");
        assert_parses(Rule::literal_set, "#[ \"a\", 0x0102 ]"); // Use even digits
                                                                // Dict
        assert_parses(Rule::literal_dict, "{}");
        assert_parses(Rule::literal_dict, "{ \"name\": \"Alice\", \"age\": 30 }");
        assert_parses(Rule::literal_dict, "{ \"nested\": { \"key\": 1 } }");
        assert_parses(Rule::literal_dict, "{ \"raw_val\": 0xab } "); // Use even digits
        assert_fails(Rule::literal_dict, "{ name: \"Alice\" }"); // Key must be string literal
    }

    #[test]
    fn test_parse_simple_request() {
        assert_parses(Rule::request_def, "REQUEST()");
        assert_parses(
            Rule::request_def,
            // Trimmed leading/trailing whitespace
            r#"REQUEST(
                // Check equality
                Equal(?gov["socialSecurityNumber"], ?pay["socialSecurityNumber"])
                // Check age > 18
                ValueOf(?const_holder["const_18y"], 1169909388)
                Lt(?gov["dateOfBirth"], ?const_holder["const_18y"])
            )"#,
        );
    }

    #[test]
    fn test_parse_simple_custom_def() {
        assert_parses(
            Rule::test_custom_predicate_def,
            // Trimmed leading/trailing whitespace
            r#"my_pred(A, B) = AND(
                Equal(?A["foo"], ?B["bar"])
            )"#,
        );
        assert_parses(
            Rule::test_custom_predicate_def,
            // Trimmed leading/trailing whitespace
            r#"pred_with_private(X, private: TempKey) = OR(
                Equal(?X[?TempKey], ?X["other"])
            )"#,
        );
        assert_fails(
            Rule::test_custom_predicate_def,
            r#"pred_no_stmts(A,B) = AND()"#,
        );
    }

    #[test]
    fn test_parse_document() {
        assert_parses(
            Rule::document,
            r#"// File defining one predicate and one request
            is_valid_user(UserPod, private: ConstVal) = AND(
                // User age must be > 18 (using a constant value)
                ValueOf(?ConstVal["min_age"], 18)
                Gt(?UserPod["age"], ?ConstVal["min_age"])
                // User must not be banned
                NotContains(?_BANNED_USERS["list"], ?UserPod["userId"])
            )

            REQUEST(
                is_valid_user(?SomeUser)
                Equal(?SomeUser["country"], ?Other["country"])
            )"#,
        );
    }

    #[test]
    fn test_custom_call() {
        assert_parses(Rule::custom_predicate_call, "my_pred()"); // No args
        assert_parses(Rule::custom_predicate_call, "pred_one(?A)"); // One var arg
        assert_parses(Rule::custom_predicate_call, "pred_lit(123)"); // One lit arg
        assert_fails(Rule::test_custom_predicate_call, "pred_ak(?P[\"k\"])"); // Should fail now
        assert_parses(
            Rule::custom_predicate_call,
            "pred_mixed(?A, 123, \"lit\", #[])", // Removed AK arg
        ); // Mixed args (Var, Lit, Lit, Lit)
        assert_fails(
            Rule::test_custom_predicate_call,
            "pred_fail(?A, ?P[\"k\"])", // Should fail with AK
        );
    }

    #[test]
    fn test_parser_rejects_keyword_as_predicate_name() {
        // Should fail defining a predicate named like a native statement
        assert_fails(
            Rule::test_custom_predicate_def,
            r#"Equal(A) = AND( Lt(?A["x"], ?A["y"]) )"#,
            // "Parser should reject native keyword 'Equal' as custom predicate name"
        );
        assert_fails(
            Rule::test_custom_predicate_def,
            "valueOf(X, Y) = OR( Lt(?X, ?Y) )", // Check different case variation if needed later
                                                // "Parser should reject 'valueOf' (even if case differs) if grammar was case-insensitive"
        );
        assert_fails(
            Rule::test_custom_predicate_def,
            "Gt() = AND()",
            // "Parser should reject native keyword 'Gt' as custom predicate name"
        );

        // Should fail calling a predicate named like a native statement using the test rule
        assert_fails(
            Rule::test_custom_predicate_call,
            "Lt()",
            // "Parser should reject native keyword 'Lt' in a custom call context"
        );
        assert_fails(
            Rule::test_custom_predicate_call,
            "Contains(?A, ?B)",
            // "Parser should reject native keyword 'Contains' in a custom call context"
        );

        // Should also fail within a REQUEST block
        assert_fails(
            Rule::document, // Test within the context of a document
            "REQUEST( Equal(?X) )", // Assuming Equal(?X) doesn't match native Equal due to args
                            // It should fail because Equal is not a valid predicate_identifier here.
                            // "Parser should reject native keyword 'Equal' as custom call inside REQUEST"
        );

        // Valid cases (should parse)
        assert_parses(
            Rule::custom_predicate_def,
            r#"MyEqual(A) = AND( Equal(?A["foo"], ?A["bar"]) )"#,
        );
        assert_parses(Rule::test_custom_predicate_call, "my_Lt()");
        assert_parses(Rule::document, "REQUEST( some_pred() )");
        assert_parses(
            Rule::document,
            r#"pred(X) = AND( Equal(?X["foo"], ?X["bar"]) ) REQUEST( pred(?A) ) "#,
        );
    }
}
