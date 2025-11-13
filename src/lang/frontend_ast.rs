//! Frontend AST for the Podlang language
//!
//! This module defines an intermediate AST that captures all features of the grammar
//! and supports bidirectional conversion (parsing and pretty-printing).

use std::fmt;

use hex::{FromHex, ToHex};

use crate::backends::plonky2::primitives::ec::{curve::Point, schnorr::SecretKey};

/// The root document containing all top-level declarations
#[derive(Debug, Clone, PartialEq)]
pub struct Document {
    pub items: Vec<DocumentItem>,
}

/// Top-level items that can appear in a document
#[derive(Debug, Clone, PartialEq)]
pub enum DocumentItem {
    UseBatchStatement(UseBatchStatement),
    UseIntroStatement(UseIntroStatement),
    CustomPredicateDef(CustomPredicateDef),
    RequestDef(RequestDef),
}

/// Import statement: `use batch pred1, pred2, _ from 0x...`
#[derive(Debug, Clone, PartialEq)]
pub struct UseBatchStatement {
    pub imports: Vec<ImportName>,
    pub batch_ref: HashHex,
    pub span: Option<Span>,
}

/// Intro statement: `use intro pred() from 0x...`
#[derive(Debug, Clone, PartialEq)]
pub struct UseIntroStatement {
    pub name: Identifier,
    pub args: Vec<Identifier>,
    pub intro_hash: HashHex,
    pub span: Option<Span>,
}
/// Individual import name (identifier or unused "_")
#[derive(Debug, Clone, PartialEq)]
pub enum ImportName {
    Named(String),
    Unused, // "_"
}

/// Batch reference (hash)
#[derive(Debug, Clone, PartialEq)]
pub struct BatchRef {
    pub hash: HashHex,
    pub span: Option<Span>,
}

/// Intro predicate reference (hash)
#[derive(Debug, Clone, PartialEq)]
pub struct IntroPredicateRef {
    pub hash: HashHex,
    pub span: Option<Span>,
}

/// Custom predicate definition
#[derive(Debug, Clone, PartialEq)]
pub struct CustomPredicateDef {
    pub name: Identifier,
    pub args: ArgSection,
    pub conjunction_type: ConjunctionType,
    pub statements: Vec<StatementTmpl>,
    pub span: Option<Span>,
}

/// Request definition
#[derive(Debug, Clone, PartialEq)]
pub struct RequestDef {
    pub statements: Vec<StatementTmpl>,
    pub span: Option<Span>,
}

/// Argument section with public and optional private arguments
#[derive(Debug, Clone, PartialEq)]
pub struct ArgSection {
    pub public_args: Vec<Identifier>,
    pub private_args: Option<Vec<Identifier>>,
    pub span: Option<Span>,
}

/// Conjunction type for custom predicates
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ConjunctionType {
    And,
    Or,
}

/// Statement template: predicate call with arguments
#[derive(Debug, Clone, PartialEq)]
pub struct StatementTmpl {
    pub predicate: Identifier,
    pub args: Vec<StatementTmplArg>,
    pub span: Option<Span>,
}

/// Arguments that can be passed to statements
#[derive(Debug, Clone, PartialEq)]
pub enum StatementTmplArg {
    Literal(LiteralValue),
    Wildcard(Identifier),
    AnchoredKey(AnchoredKey),
}

/// Anchored key: Var["key"] or Var.key
#[derive(Debug, Clone, PartialEq)]
pub struct AnchoredKey {
    pub root: Identifier,
    pub key: AnchoredKeyPath,
    pub span: Option<Span>,
}

impl AnchoredKey {
    pub fn key_str(&self) -> &str {
        match &self.key {
            AnchoredKeyPath::Bracket(ls) => &ls.value,
            AnchoredKeyPath::Dot(id) => &id.name,
        }
    }
}

/// Key path in an anchored key
#[derive(Debug, Clone, PartialEq)]
pub enum AnchoredKeyPath {
    Bracket(LiteralString), // ["key"]
    Dot(Identifier),        // .key
}

/// Identifier (variable names, predicate names, etc.)
#[derive(Debug, Clone, PartialEq)]
pub struct Identifier {
    pub name: String,
    pub span: Option<Span>,
}

/// Hash value in hex format (0x...)
#[derive(Debug, Clone, PartialEq)]
pub struct HashHex {
    pub hash: crate::middleware::Hash,
    pub span: Option<Span>,
}

/// All possible literal values
#[derive(Debug, Clone, PartialEq)]
pub enum LiteralValue {
    Int(LiteralInt),
    Bool(LiteralBool),
    String(LiteralString),
    Raw(LiteralRaw),
    PublicKey(LiteralPublicKey),
    SecretKey(LiteralSecretKey),
    Array(LiteralArray),
    Set(LiteralSet),
    Dict(LiteralDict),
}

/// Integer literal
#[derive(Debug, Clone, PartialEq)]
pub struct LiteralInt {
    pub value: i64,
    pub span: Option<Span>,
}

/// Boolean literal
#[derive(Debug, Clone, PartialEq)]
pub struct LiteralBool {
    pub value: bool,
    pub span: Option<Span>,
}

/// String literal
#[derive(Debug, Clone, PartialEq)]
pub struct LiteralString {
    pub value: String, // Unescaped value
    pub span: Option<Span>,
}

/// Raw value literal: Raw(0x...)
#[derive(Debug, Clone, PartialEq)]
pub struct LiteralRaw {
    pub hash: HashHex,
    pub span: Option<Span>,
}

/// Public key literal: PublicKey(base58string)
#[derive(Debug, Clone, PartialEq)]
pub struct LiteralPublicKey {
    pub point: Point,
    pub span: Option<Span>,
}

/// Secret key literal: SecretKey(base64string)
#[derive(Debug, Clone, PartialEq)]
pub struct LiteralSecretKey {
    pub secret_key: SecretKey,
    pub span: Option<Span>,
}

/// Array literal: [...]
#[derive(Debug, Clone, PartialEq)]
pub struct LiteralArray {
    pub elements: Vec<LiteralValue>,
    pub span: Option<Span>,
}

/// Set literal: #[...]
#[derive(Debug, Clone, PartialEq)]
pub struct LiteralSet {
    pub elements: Vec<LiteralValue>,
    pub span: Option<Span>,
}

/// Dictionary literal: {...}
#[derive(Debug, Clone, PartialEq)]
pub struct LiteralDict {
    pub pairs: Vec<DictPair>,
    pub span: Option<Span>,
}

/// Key-value pair in a dictionary
#[derive(Debug, Clone, PartialEq)]
pub struct DictPair {
    pub key: LiteralString,
    pub value: LiteralValue,
    pub span: Option<Span>,
}

/// Source location information for error reporting and formatting
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

// Display implementations for pretty-printing

impl fmt::Display for Document {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, item) in self.items.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }
            write!(f, "{}", item)?;
        }
        Ok(())
    }
}

impl fmt::Display for DocumentItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DocumentItem::UseBatchStatement(u) => write!(f, "{}", u),
            DocumentItem::UseIntroStatement(u) => write!(f, "{}", u),
            DocumentItem::CustomPredicateDef(c) => write!(f, "{}", c),
            DocumentItem::RequestDef(r) => write!(f, "{}", r),
        }
    }
}

impl fmt::Display for UseBatchStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "use batch ")?;
        for (i, import) in self.imports.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", import)?;
        }
        write!(f, " from {}", self.batch_ref)
    }
}

impl fmt::Display for UseIntroStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "use intro {}(", self.name)?;
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", arg)?;
        }
        write!(f, ") from {}", self.intro_hash)
    }
}

impl fmt::Display for ImportName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ImportName::Named(name) => write!(f, "{}", name),
            ImportName::Unused => write!(f, "_"),
        }
    }
}

impl fmt::Display for BatchRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.hash)
    }
}

impl fmt::Display for IntroPredicateRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.hash)
    }
}

impl fmt::Display for HashHex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "0x{}", self.hash.encode_hex::<String>())
    }
}

impl fmt::Display for CustomPredicateDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "{}({}) = {}(",
            self.name, self.args, self.conjunction_type
        )?;
        for stmt in &self.statements {
            writeln!(f, "    {}", stmt)?;
        }
        write!(f, ")")
    }
}

impl fmt::Display for ArgSection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, arg) in self.public_args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", arg)?;
        }
        if let Some(private_args) = &self.private_args {
            if !self.public_args.is_empty() {
                write!(f, ", ")?;
            }
            write!(f, "private: ")?;
            for (i, arg) in private_args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", arg)?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for ConjunctionType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConjunctionType::And => write!(f, "AND"),
            ConjunctionType::Or => write!(f, "OR"),
        }
    }
}

impl fmt::Display for RequestDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "REQUEST(")?;
        for stmt in &self.statements {
            writeln!(f, "    {}", stmt)?;
        }
        write!(f, ")")
    }
}

impl fmt::Display for StatementTmpl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(", self.predicate)?;
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", arg)?;
        }
        write!(f, ")")
    }
}

impl fmt::Display for StatementTmplArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StatementTmplArg::Literal(lit) => write!(f, "{}", lit),
            StatementTmplArg::Wildcard(id) => write!(f, "{}", id),
            StatementTmplArg::AnchoredKey(ak) => write!(f, "{}", ak),
        }
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl fmt::Display for AnchoredKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.key {
            AnchoredKeyPath::Bracket(s) => write!(f, "{}[{}]", self.root, s),
            AnchoredKeyPath::Dot(id) => write!(f, "{}.{}", self.root, id),
        }
    }
}

impl fmt::Display for LiteralValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LiteralValue::Int(i) => write!(f, "{}", i),
            LiteralValue::Bool(b) => write!(f, "{}", b),
            LiteralValue::String(s) => write!(f, "{}", s),
            LiteralValue::Raw(r) => write!(f, "{}", r),
            LiteralValue::PublicKey(pk) => write!(f, "{}", pk),
            LiteralValue::SecretKey(sk) => write!(f, "{}", sk),
            LiteralValue::Array(a) => write!(f, "{}", a),
            LiteralValue::Set(s) => write!(f, "{}", s),
            LiteralValue::Dict(d) => write!(f, "{}", d),
        }
    }
}

impl fmt::Display for LiteralInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl fmt::Display for LiteralBool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", if self.value { "true" } else { "false" })
    }
}

impl fmt::Display for LiteralString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"")?;
        for ch in self.value.chars() {
            match ch {
                '"' => write!(f, "\\\"")?,
                '\\' => write!(f, "\\\\")?,
                '\n' => write!(f, "\\n")?,
                '\r' => write!(f, "\\r")?,
                '\t' => write!(f, "\\t")?,
                '\u{0008}' => write!(f, "\\b")?,
                '\u{000C}' => write!(f, "\\f")?,
                _ => write!(f, "{}", ch)?,
            }
        }
        write!(f, "\"")
    }
}

impl fmt::Display for LiteralRaw {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Raw({})", self.hash)
    }
}

impl fmt::Display for LiteralPublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PublicKey({})", self.point)
    }
}

impl fmt::Display for LiteralSecretKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SecretKey({})", self.secret_key)
    }
}

impl fmt::Display for LiteralArray {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, elem) in self.elements.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", elem)?;
        }
        write!(f, "]")
    }
}

impl fmt::Display for LiteralSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#[")?;
        for (i, elem) in self.elements.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", elem)?;
        }
        write!(f, "]")
    }
}

impl fmt::Display for LiteralDict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for (i, pair) in self.pairs.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", pair)?;
        }
        write!(f, "}}")
    }
}

impl fmt::Display for DictPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.key, self.value)
    }
}

// Parser module for converting Pest pairs to AST
pub mod parse {
    use pest::iterators::Pair;

    use super::*;
    use crate::lang::parser::{self, Rule};

    /// Convert a Pest document pair to an AST Document
    pub fn parse_document(pair: Pair<Rule>) -> Result<Document, parser::ParseError> {
        assert_eq!(pair.as_rule(), Rule::document);
        let mut items = Vec::new();

        for inner_pair in pair.into_inner() {
            match inner_pair.as_rule() {
                Rule::use_batch_statement => {
                    items.push(DocumentItem::UseBatchStatement(parse_use_batch_statement(
                        inner_pair,
                    )));
                }
                Rule::use_intro_statement => {
                    items.push(DocumentItem::UseIntroStatement(parse_use_intro_statement(
                        inner_pair,
                    )));
                }
                Rule::custom_predicate_def => {
                    items.push(DocumentItem::CustomPredicateDef(
                        parse_custom_predicate_def(inner_pair)?,
                    ));
                }
                Rule::request_def => {
                    items.push(DocumentItem::RequestDef(parse_request_def(inner_pair)?));
                }
                Rule::EOI => {}
                _ => unreachable!("Unexpected rule in document: {:?}", inner_pair.as_rule()),
            }
        }

        Ok(Document { items })
    }

    fn parse_use_batch_statement(pair: Pair<Rule>) -> UseBatchStatement {
        assert_eq!(pair.as_rule(), Rule::use_batch_statement);
        let span = get_span(&pair);
        let mut inner = pair.into_inner();

        let use_list_pair = inner
            .find(|p| p.as_rule() == Rule::use_predicate_list)
            .unwrap();
        let batch_ref_pair = inner.find(|p| p.as_rule() == Rule::batch_ref).unwrap();

        let imports = use_list_pair
            .into_inner()
            .filter(|p| p.as_rule() == Rule::import_name)
            .map(parse_import_name)
            .collect();

        UseBatchStatement {
            imports,
            batch_ref: parse_hash_hex(batch_ref_pair.into_inner().next().unwrap()),
            span: Some(span),
        }
    }

    fn parse_use_intro_statement(pair: Pair<Rule>) -> UseIntroStatement {
        assert_eq!(pair.as_rule(), Rule::use_intro_statement);
        let span = get_span(&pair);
        let inner = pair.into_inner();

        let name = parse_identifier(
            inner
                .clone()
                .find(|p| p.as_rule() == Rule::identifier)
                .unwrap(),
        );

        let args: Vec<Identifier> = inner
            .clone()
            .find(|p| p.as_rule() == Rule::use_intro_arg_list)
            .map(|arg_list| {
                arg_list
                    .into_inner()
                    .filter(|p| p.as_rule() == Rule::identifier)
                    .map(parse_identifier)
                    .collect()
            })
            .unwrap_or_default();

        let intro_predicate_ref_pair = inner
            .clone()
            .find(|p| p.as_rule() == Rule::intro_predicate_ref)
            .unwrap();

        UseIntroStatement {
            name,
            args,
            intro_hash: parse_hash_hex(intro_predicate_ref_pair.into_inner().next().unwrap()),
            span: Some(span),
        }
    }

    fn parse_import_name(pair: Pair<Rule>) -> ImportName {
        assert_eq!(pair.as_rule(), Rule::import_name);
        let s = pair.as_str();
        if s == "_" {
            ImportName::Unused
        } else {
            ImportName::Named(s.to_string())
        }
    }

    fn parse_hash_hex(pair: Pair<Rule>) -> HashHex {
        assert_eq!(pair.as_rule(), Rule::hash_hex);
        let span = get_span(&pair);
        let hex_str = pair.as_str();

        // Grammar guarantees "0x" prefix and exactly 64 hex chars
        assert!(hex_str.starts_with("0x"));
        let hex_without_prefix = &hex_str[2..];

        // Parse hex string directly to middleware::Hash
        let hash = crate::middleware::Hash::from_hex(hex_without_prefix)
            .expect("Grammar should guarantee valid hex");

        HashHex {
            hash,
            span: Some(span),
        }
    }

    fn parse_custom_predicate_def(
        pair: Pair<Rule>,
    ) -> Result<CustomPredicateDef, parser::ParseError> {
        assert_eq!(pair.as_rule(), Rule::custom_predicate_def);
        let span = get_span(&pair);
        let mut inner = pair.into_inner();

        let name = parse_identifier(inner.next().unwrap());
        let args = parse_arg_section(inner.next().unwrap());
        let conjunction_type = parse_conjunction_type(inner.next().unwrap());
        let statement_list = inner.next().unwrap();

        let statements = statement_list
            .into_inner()
            .filter(|p| p.as_rule() == Rule::statement)
            .map(parse_statement)
            .collect::<Result<Vec<_>, _>>()?;

        Ok(CustomPredicateDef {
            name,
            args,
            conjunction_type,
            statements,
            span: Some(span),
        })
    }

    fn parse_arg_section(pair: Pair<Rule>) -> ArgSection {
        assert_eq!(pair.as_rule(), Rule::arg_section);
        let span = get_span(&pair);
        let mut public_args = Vec::new();
        let mut private_args = None;

        for inner_pair in pair.into_inner() {
            match inner_pair.as_rule() {
                Rule::public_arg_list => {
                    public_args = inner_pair
                        .into_inner()
                        .filter(|p| p.as_rule() == Rule::identifier)
                        .map(parse_identifier)
                        .collect();
                }
                Rule::private_arg_list => {
                    private_args = Some(
                        inner_pair
                            .into_inner()
                            .filter(|p| p.as_rule() == Rule::identifier)
                            .map(parse_identifier)
                            .collect(),
                    );
                }
                _ => {}
            }
        }

        ArgSection {
            public_args,
            private_args,
            span: Some(span),
        }
    }

    fn parse_conjunction_type(pair: Pair<Rule>) -> ConjunctionType {
        assert_eq!(pair.as_rule(), Rule::conjunction_type);
        match pair.as_str() {
            "AND" => ConjunctionType::And,
            "OR" => ConjunctionType::Or,
            _ => unreachable!("Invalid conjunction type: {}", pair.as_str()),
        }
    }

    fn parse_request_def(pair: Pair<Rule>) -> Result<RequestDef, parser::ParseError> {
        assert_eq!(pair.as_rule(), Rule::request_def);
        let span = get_span(&pair);
        let mut statements = Vec::new();

        for inner_pair in pair.into_inner() {
            if inner_pair.as_rule() == Rule::statement_list {
                statements = inner_pair
                    .into_inner()
                    .filter(|p| p.as_rule() == Rule::statement)
                    .map(parse_statement)
                    .collect::<Result<Vec<_>, _>>()?;
            }
        }

        Ok(RequestDef {
            statements,
            span: Some(span),
        })
    }

    fn parse_statement(pair: Pair<Rule>) -> Result<StatementTmpl, parser::ParseError> {
        assert_eq!(pair.as_rule(), Rule::statement);
        let span = get_span(&pair);
        let mut inner = pair.into_inner();

        let predicate = parse_identifier(inner.next().unwrap());
        let mut args = Vec::new();

        if let Some(arg_list) = inner.next() {
            if arg_list.as_rule() == Rule::statement_arg_list {
                args = arg_list
                    .into_inner()
                    .filter(|p| p.as_rule() == Rule::statement_arg)
                    .map(parse_statement_arg)
                    .collect::<Result<Vec<_>, _>>()?;
            }
        }

        Ok(StatementTmpl {
            predicate,
            args,
            span: Some(span),
        })
    }

    fn parse_statement_arg(pair: Pair<Rule>) -> Result<StatementTmplArg, parser::ParseError> {
        assert_eq!(pair.as_rule(), Rule::statement_arg);
        let inner = pair.into_inner().next().unwrap();

        match inner.as_rule() {
            Rule::literal_value => Ok(StatementTmplArg::Literal(parse_literal_value(inner)?)),
            Rule::identifier => Ok(StatementTmplArg::Wildcard(parse_identifier(inner))),
            Rule::anchored_key => Ok(StatementTmplArg::AnchoredKey(parse_anchored_key(inner)?)),
            _ => unreachable!("Unexpected statement arg rule: {:?}", inner.as_rule()),
        }
    }

    fn parse_anchored_key(pair: Pair<Rule>) -> Result<AnchoredKey, parser::ParseError> {
        assert_eq!(pair.as_rule(), Rule::anchored_key);
        let span = get_span(&pair);
        let mut inner = pair.into_inner();

        let root = parse_identifier(inner.next().unwrap());
        let key_part = inner.next().unwrap();

        let key = match key_part.as_rule() {
            Rule::literal_string => AnchoredKeyPath::Bracket(parse_literal_string(key_part)?),
            Rule::identifier => AnchoredKeyPath::Dot(parse_identifier(key_part)),
            _ => unreachable!("Unexpected anchored key part: {:?}", key_part.as_rule()),
        };

        Ok(AnchoredKey {
            root,
            key,
            span: Some(span),
        })
    }

    fn parse_identifier(pair: Pair<Rule>) -> Identifier {
        assert_eq!(pair.as_rule(), Rule::identifier);
        Identifier {
            name: pair.as_str().to_string(),
            span: Some(get_span(&pair)),
        }
    }

    fn parse_literal_value(pair: Pair<Rule>) -> Result<LiteralValue, parser::ParseError> {
        assert_eq!(pair.as_rule(), Rule::literal_value);
        let inner = pair.into_inner().next().unwrap();

        match inner.as_rule() {
            Rule::literal_int => Ok(LiteralValue::Int(parse_literal_int(inner)?)),
            Rule::literal_bool => Ok(LiteralValue::Bool(parse_literal_bool(inner))),
            Rule::literal_string => Ok(LiteralValue::String(parse_literal_string(inner)?)),
            Rule::literal_raw => Ok(LiteralValue::Raw(parse_literal_raw(inner))),
            Rule::literal_public_key => {
                Ok(LiteralValue::PublicKey(parse_literal_public_key(inner)?))
            }
            Rule::literal_secret_key => {
                Ok(LiteralValue::SecretKey(parse_literal_secret_key(inner)?))
            }
            Rule::literal_array => Ok(LiteralValue::Array(parse_literal_array(inner)?)),
            Rule::literal_set => Ok(LiteralValue::Set(parse_literal_set(inner)?)),
            Rule::literal_dict => Ok(LiteralValue::Dict(parse_literal_dict(inner)?)),
            _ => unreachable!("Unexpected literal value rule: {:?}", inner.as_rule()),
        }
    }

    fn parse_literal_int(pair: Pair<Rule>) -> Result<LiteralInt, parser::ParseError> {
        assert_eq!(pair.as_rule(), Rule::literal_int);
        let value = pair
            .as_str()
            .parse()
            .map_err(|e| parser::ParseError::InvalidInt(format!("{}: {}", pair.as_str(), e)))?;
        Ok(LiteralInt {
            value,
            span: Some(get_span(&pair)),
        })
    }

    fn parse_literal_bool(pair: Pair<Rule>) -> LiteralBool {
        assert_eq!(pair.as_rule(), Rule::literal_bool);
        LiteralBool {
            value: pair.as_str() == "true",
            span: Some(get_span(&pair)),
        }
    }

    fn parse_literal_string(pair: Pair<Rule>) -> Result<LiteralString, parser::ParseError> {
        assert_eq!(pair.as_rule(), Rule::literal_string);
        let span = get_span(&pair);

        // Extract the unescaped value from between quotes
        let inner = pair.into_inner().next().unwrap();
        let value = unescape_string(inner.as_str())?;

        Ok(LiteralString {
            value,
            span: Some(span),
        })
    }

    fn parse_literal_raw(pair: Pair<Rule>) -> LiteralRaw {
        assert_eq!(pair.as_rule(), Rule::literal_raw);
        let span = get_span(&pair);
        let hash_pair = pair.into_inner().next().unwrap();
        LiteralRaw {
            hash: parse_hash_hex(hash_pair),
            span: Some(span),
        }
    }

    fn parse_literal_public_key(pair: Pair<Rule>) -> Result<LiteralPublicKey, parser::ParseError> {
        assert_eq!(pair.as_rule(), Rule::literal_public_key);
        let span = get_span(&pair);
        let base58_pair = pair.into_inner().next().unwrap();
        let base58_str = base58_pair.as_str();
        let point = base58_str
            .parse()
            .map_err(|e| parser::ParseError::InvalidPublicKey(format!("{}: {}", base58_str, e)))?;
        Ok(LiteralPublicKey {
            point,
            span: Some(span),
        })
    }

    fn parse_literal_secret_key(pair: Pair<Rule>) -> Result<LiteralSecretKey, parser::ParseError> {
        assert_eq!(pair.as_rule(), Rule::literal_secret_key);
        let span = get_span(&pair);
        let base64_pair = pair.into_inner().next().unwrap();
        let base64_str = base64_pair.as_str();
        let secret_key = base64_str
            .parse()
            .map_err(|e| parser::ParseError::InvalidSecretKey(format!("{}: {}", base64_str, e)))?;
        Ok(LiteralSecretKey {
            secret_key,
            span: Some(span),
        })
    }

    fn parse_literal_array(pair: Pair<Rule>) -> Result<LiteralArray, parser::ParseError> {
        assert_eq!(pair.as_rule(), Rule::literal_array);
        let span = get_span(&pair);
        let elements: Result<Vec<_>, _> = pair
            .into_inner()
            .filter(|p| p.as_rule() == Rule::literal_value)
            .map(parse_literal_value)
            .collect();
        Ok(LiteralArray {
            elements: elements?,
            span: Some(span),
        })
    }

    fn parse_literal_set(pair: Pair<Rule>) -> Result<LiteralSet, parser::ParseError> {
        assert_eq!(pair.as_rule(), Rule::literal_set);
        let span = get_span(&pair);
        let elements: Result<Vec<_>, _> = pair
            .into_inner()
            .filter(|p| p.as_rule() == Rule::literal_value)
            .map(parse_literal_value)
            .collect();
        Ok(LiteralSet {
            elements: elements?,
            span: Some(span),
        })
    }

    fn parse_literal_dict(pair: Pair<Rule>) -> Result<LiteralDict, parser::ParseError> {
        assert_eq!(pair.as_rule(), Rule::literal_dict);
        let span = get_span(&pair);
        let pairs: Result<Vec<_>, _> = pair
            .into_inner()
            .filter(|p| p.as_rule() == Rule::dict_pair)
            .map(parse_dict_pair)
            .collect();
        Ok(LiteralDict {
            pairs: pairs?,
            span: Some(span),
        })
    }

    fn parse_dict_pair(pair: Pair<Rule>) -> Result<DictPair, parser::ParseError> {
        assert_eq!(pair.as_rule(), Rule::dict_pair);
        let span = get_span(&pair);
        let mut inner = pair.into_inner();
        let key = parse_literal_string(inner.next().unwrap())?;
        let value = parse_literal_value(inner.next().unwrap())?;
        Ok(DictPair {
            key,
            value,
            span: Some(span),
        })
    }

    fn get_span(pair: &Pair<Rule>) -> Span {
        let span = pair.as_span();
        Span {
            start: span.start(),
            end: span.end(),
        }
    }

    fn unescape_string(s: &str) -> Result<String, parser::ParseError> {
        let mut result = String::new();
        let mut chars = s.chars().peekable();

        while let Some(ch) = chars.next() {
            if ch == '\\' {
                match chars.next() {
                    Some('"') => result.push('"'),
                    Some('\\') => result.push('\\'),
                    Some('/') => result.push('/'),
                    Some('b') => result.push('\u{0008}'),
                    Some('f') => result.push('\u{000C}'),
                    Some('n') => result.push('\n'),
                    Some('r') => result.push('\r'),
                    Some('t') => result.push('\t'),
                    Some('u') => {
                        // Grammar guarantees exactly 4 hex digits after \u
                        // We only need to check if the codepoint is valid unicode
                        let hex: String = chars.by_ref().take(4).collect();
                        let code = u32::from_str_radix(&hex, 16)
                            .expect("Grammar should guarantee valid hex digits");
                        let unicode_char = char::from_u32(code).ok_or_else(|| {
                            parser::ParseError::InvalidEscapeSequence(format!(
                                "\\u{}: invalid unicode codepoint",
                                hex
                            ))
                        })?;
                        result.push(unicode_char);
                    }
                    Some(other) => {
                        // Grammar should prevent this, but handle gracefully
                        unreachable!(
                            "Grammar should only allow specific escape sequences, got: \\{}",
                            other
                        );
                    }
                    None => {
                        // Grammar should prevent this
                        unreachable!("Grammar should not allow backslash at end of string");
                    }
                }
            } else {
                result.push(ch);
            }
        }

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::parser::parse_podlang;

    /// Test that parsing and pretty-printing produces equivalent output
    fn test_roundtrip(input: &str) {
        let parsed = parse_podlang(input).expect("Failed to parse input");
        let document_pair = parsed.into_iter().next().expect("No document pair");
        let mut ast = parse::parse_document(document_pair).expect("Failed to parse");
        let output = ast.to_string();
        // Parse the output to verify it's still valid
        let reparsed = parse_podlang(&output).expect("Failed to parse pretty-printed output");
        let reparsed_document_pair = reparsed
            .into_iter()
            .next()
            .expect("No document pair in reparse");
        let mut reparsed_ast =
            parse::parse_document(reparsed_document_pair).expect("Failed to parse");

        // Clear spans for comparison (they'll be different after pretty-printing)
        clear_spans(&mut ast);
        clear_spans(&mut reparsed_ast);

        // Compare the ASTs (they should be structurally equivalent)
        assert_eq!(ast, reparsed_ast, "AST mismatch for input:\n{}", input);
    }

    fn clear_spans(doc: &mut Document) {
        for item in &mut doc.items {
            match item {
                DocumentItem::UseBatchStatement(u) => {
                    u.span = None;
                    u.batch_ref.span = None;
                }
                DocumentItem::UseIntroStatement(u) => {
                    u.span = None;
                    u.name.span = None;
                    u.intro_hash.span = None;
                }
                DocumentItem::CustomPredicateDef(c) => {
                    c.span = None;
                    c.name.span = None;
                    c.args.span = None;
                    for arg in &mut c.args.public_args {
                        arg.span = None;
                    }
                    if let Some(private) = &mut c.args.private_args {
                        for arg in private {
                            arg.span = None;
                        }
                    }
                    for stmt in &mut c.statements {
                        clear_statement_spans(stmt);
                    }
                }
                DocumentItem::RequestDef(r) => {
                    r.span = None;
                    for stmt in &mut r.statements {
                        clear_statement_spans(stmt);
                    }
                }
            }
        }
    }

    fn clear_statement_spans(stmt: &mut StatementTmpl) {
        stmt.span = None;
        stmt.predicate.span = None;
        for arg in &mut stmt.args {
            match arg {
                StatementTmplArg::Literal(lit) => clear_literal_spans(lit),
                StatementTmplArg::Wildcard(id) => id.span = None,
                StatementTmplArg::AnchoredKey(ak) => {
                    ak.span = None;
                    ak.root.span = None;
                    match &mut ak.key {
                        AnchoredKeyPath::Bracket(s) => s.span = None,
                        AnchoredKeyPath::Dot(id) => id.span = None,
                    }
                }
            }
        }
    }

    fn clear_literal_spans(lit: &mut LiteralValue) {
        match lit {
            LiteralValue::Int(i) => i.span = None,
            LiteralValue::Bool(b) => b.span = None,
            LiteralValue::String(s) => s.span = None,
            LiteralValue::Raw(r) => {
                r.span = None;
                r.hash.span = None;
            }
            LiteralValue::PublicKey(pk) => pk.span = None,
            LiteralValue::SecretKey(sk) => sk.span = None,
            LiteralValue::Array(a) => {
                a.span = None;
                for elem in &mut a.elements {
                    clear_literal_spans(elem);
                }
            }
            LiteralValue::Set(s) => {
                s.span = None;
                for elem in &mut s.elements {
                    clear_literal_spans(elem);
                }
            }
            LiteralValue::Dict(d) => {
                d.span = None;
                for pair in &mut d.pairs {
                    pair.span = None;
                    pair.key.span = None;
                    clear_literal_spans(&mut pair.value);
                }
            }
        }
    }

    #[test]
    fn test_empty_document() {
        test_roundtrip("");
    }

    #[test]
    fn test_simple_request() {
        let input = r#"REQUEST(
    Equal(A["foo"], B["bar"])
    NotEqual(C["baz"], 123)
)"#;
        test_roundtrip(input);
    }

    #[test]
    fn test_custom_predicate() {
        let input = r#"my_pred(A, B) = AND (
    Equal(A["foo"], B.bar)
    Lt(A["key with spaces"], 100)
)"#;
        test_roundtrip(input);
    }

    #[test]
    fn test_private_args() {
        let input = r#"pred_with_private(X, private: TempKey) = OR (
    Equal(X["key"], TempKey["value"])
    Contains(X["list"], TempKey["item"])
)"#;
        test_roundtrip(input);
    }

    #[test]
    fn test_use_batch_statement() {
        let input = r#"use batch pred1, pred2, _ from 0x0000000000000000000000000000000000000000000000000000000000000000"#;
        test_roundtrip(input);
    }

    #[test]
    fn test_use_intro_statement() {
        let input = r#"use intro pred1() from 0x0000000000000000000000000000000000000000000000000000000000000000"#;
        test_roundtrip(input);
    }

    #[test]
    fn test_literals() {
        // Generate valid PublicKey and SecretKey for the test
        let sk = SecretKey::new_rand();
        let pk = sk.public_key();

        let input = format!(
            r#"REQUEST(
    Equal(A["int"], 42)
    Equal(B["neg"], -100)
    Equal(C["bool"], true)
    Equal(D["bool2"], false)
    Equal(E["string"], "hello world")
    Equal(F["raw"], Raw(0x0000000000000000000000000000000000000000000000000000000000000001))
    Equal(G["pk"], PublicKey({}))
    Equal(H["sk"], SecretKey({}))
)"#,
            pk, sk
        );
        test_roundtrip(&input);
    }

    #[test]
    fn test_containers() {
        let input = r#"REQUEST(
    Equal(A["array"], [1, 2, 3])
    Equal(B["set"], #["a", "b", "c"])
    Equal(C["dict"], {"key1": "value1", "key2": 42})
    Equal(D["nested"], [{"inner": #[1, 2]}, [true, false]])
)"#;
        test_roundtrip(input);
    }

    #[test]
    fn test_anchored_keys() {
        let input = r#"REQUEST(
    Equal(Var["bracket_key"], Other["key2"])
    Equal(Var.dot_key, Other.key3)
)"#;
        test_roundtrip(input);
    }

    #[test]
    fn test_complete_document() {
        let input = r#"use batch imported_pred from 0xabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd

is_valid(User, private: Config) = AND (
    Equal(User["age"], Config["min_age"])
    imported_pred(User, Config)
)

check_both(A, B, C) = OR (
    is_valid(A)
    is_valid(B)
    Equal(C["flag"], true)
)

REQUEST(
    check_both(Pod1, Pod2, Pod3)
    NotContains(Pod1["list"], Pod2["value"])
)"#;
        test_roundtrip(input);
    }

    #[test]
    fn test_string_escapes() {
        let input = r#"REQUEST(
    Equal(A["escaped"], "line1\nline2")
    Equal(B["quote"], "say \"hello\"")
    Equal(C["backslash"], "path\\to\\file")
    Equal(D["tab"], "col1\tcol2")
)"#;

        let parsed = parse_podlang(input).expect("Failed to parse input");
        let document_pair = parsed.into_iter().next().expect("No document pair");
        let ast = parse::parse_document(document_pair).expect("Failed to parse");

        // Check that the AST correctly unescaped the strings
        if let DocumentItem::RequestDef(req) = &ast.items[0] {
            if let StatementTmplArg::Literal(LiteralValue::String(s)) = &req.statements[0].args[1] {
                assert_eq!(s.value, "line1\nline2");
            }
            if let StatementTmplArg::Literal(LiteralValue::String(s)) = &req.statements[1].args[1] {
                assert_eq!(s.value, "say \"hello\"");
            }
            if let StatementTmplArg::Literal(LiteralValue::String(s)) = &req.statements[2].args[1] {
                assert_eq!(s.value, "path\\to\\file");
            }
            if let StatementTmplArg::Literal(LiteralValue::String(s)) = &req.statements[3].args[1] {
                assert_eq!(s.value, "col1\tcol2");
            }
        }
    }

    #[test]
    fn test_ast_structure() {
        let input = r#"my_pred(A, B, private: C) = AND (
    Equal(A["foo"], B["bar"])
)

REQUEST(
    my_pred(X, Y)
)"#;

        let parsed = parse_podlang(input).expect("Failed to parse input");
        let document_pair = parsed.into_iter().next().expect("No document pair");
        let ast = parse::parse_document(document_pair).expect("Failed to parse");

        assert_eq!(ast.items.len(), 2);

        // Check custom predicate structure
        if let DocumentItem::CustomPredicateDef(pred) = &ast.items[0] {
            assert_eq!(pred.name.name, "my_pred");
            assert_eq!(pred.args.public_args.len(), 2);
            assert_eq!(pred.args.public_args[0].name, "A");
            assert_eq!(pred.args.public_args[1].name, "B");
            assert_eq!(pred.args.private_args.as_ref().unwrap().len(), 1);
            assert_eq!(pred.args.private_args.as_ref().unwrap()[0].name, "C");
            assert_eq!(pred.conjunction_type, ConjunctionType::And);
            assert_eq!(pred.statements.len(), 1);
        } else {
            panic!("Expected CustomPredicateDef");
        }

        // Check request structure
        if let DocumentItem::RequestDef(req) = &ast.items[1] {
            assert_eq!(req.statements.len(), 1);
            assert_eq!(req.statements[0].predicate.name, "my_pred");
            assert_eq!(req.statements[0].args.len(), 2);
        } else {
            panic!("Expected RequestDef");
        }
    }

    #[test]
    fn test_invalid_escape_sequences() {
        // Test invalid unicode codepoint - surrogate pair range
        let input = r#"REQUEST(Equal(A["key"], "test\uD800"))"#;
        let parsed = crate::lang::parser::parse_podlang(input).expect("Grammar should accept this");
        let result = parse::parse_document(parsed.into_iter().next().unwrap());
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            crate::lang::parser::ParseError::InvalidEscapeSequence(_)
        ));
    }
}
