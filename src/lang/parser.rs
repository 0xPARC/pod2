use pest::{iterators::Pairs as PestPairs, Parser};
use pest_derive::Parser;

// Derive the parser from the grammar file
// The Rust analyzer will only reload the grammar file when *this* file is recompiled,
// and changes to the grammar file will not automatically trigger a recompile.
#[derive(Parser)]
#[grammar = "lang/grammar.pest"]
pub struct PodlogParser;

pub type Pairs<'a, R> = PestPairs<'a, R>;

#[derive(thiserror::Error, Debug)]
pub enum ParseError {
    #[error("Pest parsing error: {0}")]
    Pest(Box<pest::error::Error<Rule>>),
}

impl From<pest::error::Error<Rule>> for ParseError {
    fn from(err: pest::error::Error<Rule>) -> Self {
        ParseError::Pest(Box::new(err))
    }
}

/// Parses a Podlog input string according to the grammar rules.
pub fn parse_podlog(input: &str) -> Result<Pairs<'_, Rule>, ParseError> {
    let pairs = PodlogParser::parse(Rule::document, input)?;
    Ok(pairs)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_parses(rule: Rule, input: &str) {
        match PodlogParser::parse(rule, input) {
            Ok(_) => (), // Successfully parsed
            Err(e) => panic!("Failed to parse input:\n{}\nError: {}", input, e),
        }
    }

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
    fn test_parse_wildcard() {
        assert_parses(Rule::wildcard, "?Var");
        assert_parses(Rule::wildcard, "?_Internal");
        assert_parses(Rule::wildcard, "?X1");
        assert_fails(Rule::test_wildcard, "NotAVar"); // Use test rule
        assert_fails(Rule::test_wildcard, "?"); // Use test rule
        assert_fails(Rule::test_wildcard, "?invalid-char"); // Use test rule
    }

    #[test]
    fn test_parse_anchored_key() {
        assert_parses(Rule::anchored_key, "?PodVar[\"literal_key\"]");
        assert_parses(Rule::anchored_key, "?PodVar[?KeyVar]");
        assert_parses(Rule::anchored_key, "SELF[?KeyVar]");
        assert_parses(Rule::anchored_key, "SELF[\"literal_key\"]");
        assert_fails(Rule::anchored_key, "PodVar[\"key\"]"); // Needs wildcard for pod
        assert_fails(Rule::anchored_key, "?PodVar[invalid_key]"); // Key must be literal string or wildcard
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

        // Raw - Require 64 hex digits (32 bytes, equal to 4 * 64-bit field elements)
        assert_parses(
            Rule::literal_raw,
            "0x0000000000000000000000000000000000000000000000000000000000000000",
        );
        assert_parses(
            Rule::literal_raw,
            "0xabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd",
        );
        let long_valid_raw = format!("0x{}", "a".repeat(64));
        assert_parses(Rule::literal_raw, &long_valid_raw);

        // Use anchored rule for failure cases
        assert_fails(Rule::test_literal_raw, "0xabc"); // Fails (string is too short)
        assert_fails(Rule::test_literal_raw, "0x"); // Fails (needs at least one pair)
        assert_fails(Rule::test_literal_raw, &format!("0x{}", "a".repeat(66))); // Fails (string is too long)

        // String
        assert_parses(Rule::literal_string, "\"hello\"");
        assert_parses(Rule::literal_string, "\"escaped \\\" quote\"");
        assert_parses(Rule::literal_string, "\"\\\\ backslash\"");
        assert_parses(Rule::literal_string, "\"\\uABCD\"");
        assert_fails(Rule::literal_string, "\"unterminated");
        // Array
        assert_parses(Rule::literal_array, "[]");
        assert_parses(Rule::literal_array, "[1, \"two\", true]");
        assert_parses(Rule::literal_array, "[ [1], #[2] ]");
        // Set
        assert_parses(Rule::literal_set, "#[]");
        assert_parses(Rule::literal_set, "#[1, 2, 3]");
        assert_parses(
            Rule::literal_set,
            "#[ \"a\", 0x0000000000000000000000000000000000000000000000000000000000000000 ]",
        );
        // Dict
        assert_parses(Rule::literal_dict, "{}");
        assert_parses(Rule::literal_dict, "{ \"name\": \"Alice\", \"age\": 30 }");
        assert_parses(Rule::literal_dict, "{ \"nested\": { \"key\": 1 } }");
        assert_parses(
            Rule::literal_dict,
            "{ \"raw_val\": 0x0000000000000000000000000000000000000000000000000000000000000000 } ",
        );
        assert_fails(Rule::literal_dict, "{ name: \"Alice\" }"); // Key must be string literal with quotes
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
}
