//! This file contains some custom callbacks for bindgen.

use bindgen::callbacks::{Token, TokenKind};
use std::collections::HashSet;

/// This callback will be used to remove the type casts.
/// bindgen has a hard time parsing constants with type casts like
/// ```rust
/// #define SCIP_INVALID (double)1e99
/// ```
///
/// ### Note;
/// Maybe we should be careful on which macros we use this? I can see a situation where Rust and C
/// would have different opinions on what the macro should look like.
#[derive(Debug)]
pub struct DeriveCastedConstant {
    /// Set of macros to target for removing type casts
    targets: HashSet<String>,
}

impl DeriveCastedConstant {
    pub fn new() -> Self {
        DeriveCastedConstant {
            targets: HashSet::new(),
        }
    }

    pub fn target(mut self, name: &str) -> Self {
        self.targets.insert(name.to_string());
        self
    }
}

/// Implement the ParseCallbacks trait for DeriveCastedConstant
impl bindgen::callbacks::ParseCallbacks for DeriveCastedConstant {
    fn modify_macro(&self, _name: &str, _tokens: &mut Vec<Token>) {
        // modify SCIP_INVALID
        if self.targets.contains(_name) {
            // So here we are looking for a pattern like ['(', type, ')']
            let position_cast = _tokens.windows(3).position(|window| match window {
                [Token {
                    kind: TokenKind::Punctuation,
                    raw: left_parenthesis,
                }, Token {
                    // this will not go off on a cast like (SCIP_Real) as SCIP_Real is not a
                    // Clang-keyword
                    kind: TokenKind::Keyword,
                    ..
                }, Token {
                    kind: TokenKind::Punctuation,
                    raw: right_parenthesis,
                }] => **left_parenthesis == *b"(" && **right_parenthesis == *b")",
                _ => false,
            });
            if let Some(pos) = position_cast {
                // position found! So a macro with a type cast exists. We remove the typecast.
                *_tokens = [&_tokens[..pos], &_tokens[pos + 3..]].concat();
            }
        }
    }
}
