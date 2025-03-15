use crate::frontend::containers::{Array, Dictionary, Set};
use crate::frontend::{self, AnchoredKey, Origin, Value};
use crate::middleware::{self, hash_str, NativeOperation, NativePredicate, Predicate};
use serde::{Deserialize, Serialize};

use std::fmt;
use std::hash::{Hash, Hasher};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ProvableStatement {
    ValueOf(AnchoredKey, ProvableValue),
    Equal(AnchoredKey, AnchoredKey),
    NotEqual(AnchoredKey, AnchoredKey),
    Gt(AnchoredKey, AnchoredKey),
    Lt(AnchoredKey, AnchoredKey),
    Contains(AnchoredKey, AnchoredKey),
    NotContains(AnchoredKey, AnchoredKey),
    SumOf(AnchoredKey, AnchoredKey, AnchoredKey),
    ProductOf(AnchoredKey, AnchoredKey, AnchoredKey),
    MaxOf(AnchoredKey, AnchoredKey, AnchoredKey),
}

impl From<ProvableStatement> for frontend::Statement {
    fn from(stmt: ProvableStatement) -> Self {
        match stmt {
            ProvableStatement::ValueOf(ak, v) => frontend::Statement(
                Predicate::Native(NativePredicate::ValueOf),
                vec![
                    frontend::StatementArg::Key(ak.into()),
                    frontend::StatementArg::Literal(v.into()),
                ],
            ),
            ProvableStatement::Equal(ak1, ak2) => frontend::Statement(
                Predicate::Native(NativePredicate::Equal),
                vec![
                    frontend::StatementArg::Key(ak1.into()),
                    frontend::StatementArg::Key(ak2.into()),
                ],
            ),
            ProvableStatement::NotEqual(ak1, ak2) => frontend::Statement(
                Predicate::Native(NativePredicate::NotEqual),
                vec![
                    frontend::StatementArg::Key(ak1.into()),
                    frontend::StatementArg::Key(ak2.into()),
                ],
            ),
            ProvableStatement::Gt(ak1, ak2) => frontend::Statement(
                Predicate::Native(NativePredicate::Gt),
                vec![
                    frontend::StatementArg::Key(ak1.into()),
                    frontend::StatementArg::Key(ak2.into()),
                ],
            ),
            ProvableStatement::Lt(ak1, ak2) => frontend::Statement(
                Predicate::Native(NativePredicate::Lt),
                vec![
                    frontend::StatementArg::Key(ak1.into()),
                    frontend::StatementArg::Key(ak2.into()),
                ],
            ),
            ProvableStatement::Contains(ak1, ak2) => frontend::Statement(
                Predicate::Native(NativePredicate::Contains),
                vec![
                    frontend::StatementArg::Key(ak1.into()),
                    frontend::StatementArg::Key(ak2.into()),
                ],
            ),
            ProvableStatement::NotContains(ak1, ak2) => frontend::Statement(
                Predicate::Native(NativePredicate::NotContains),
                vec![
                    frontend::StatementArg::Key(ak1.into()),
                    frontend::StatementArg::Key(ak2.into()),
                ],
            ),
            ProvableStatement::SumOf(ak1, ak2, ak3) => frontend::Statement(
                Predicate::Native(NativePredicate::SumOf),
                vec![
                    frontend::StatementArg::Key(ak1.into()),
                    frontend::StatementArg::Key(ak2.into()),
                    frontend::StatementArg::Key(ak3.into()),
                ],
            ),
            ProvableStatement::ProductOf(ak1, ak2, ak3) => frontend::Statement(
                Predicate::Native(NativePredicate::ProductOf),
                vec![
                    frontend::StatementArg::Key(ak1.into()),
                    frontend::StatementArg::Key(ak2.into()),
                    frontend::StatementArg::Key(ak3.into()),
                ],
            ),
            ProvableStatement::MaxOf(ak1, ak2, ak3) => frontend::Statement(
                Predicate::Native(NativePredicate::MaxOf),
                vec![
                    frontend::StatementArg::Key(ak1.into()),
                    frontend::StatementArg::Key(ak2.into()),
                    frontend::StatementArg::Key(ak3.into()),
                ],
            ),
        }
    }
}

// impl From<ProvableStatement> for middleware::Statement {
//     fn from(stmt: ProvableStatement) -> Self {
//         match stmt {
//             ProvableStatement::None => middleware::Statement::None,
//             ProvableStatement::ValueOf(ak, v) => {
//                 middleware::Statement::ValueOf(ak.into(), v.into())
//             }
//             ProvableStatement::Equal(ak1, ak2) => {
//                 middleware::Statement::Equal(ak1.into(), ak2.into())
//             }
//             ProvableStatement::NotEqual(ak1, ak2) => {
//                 middleware::Statement::NotEqual(ak1.into(), ak2.into())
//             }
//             ProvableStatement::Gt(ak1, ak2) => middleware::Statement::Gt(ak1.into(), ak2.into()),
//             ProvableStatement::Lt(ak1, ak2) => middleware::Statement::Lt(ak1.into(), ak2.into()),
//             ProvableStatement::Contains(ak1, ak2) => {
//                 middleware::Statement::Contains(ak1.into(), ak2.into())
//             }
//             ProvableStatement::NotContains(ak1, ak2) => {
//                 middleware::Statement::NotContains(ak1.into(), ak2.into())
//             }
//             ProvableStatement::SumOf(ak1, ak2, ak3) => {
//                 middleware::Statement::SumOf(ak1.into(), ak2.into(), ak3.into())
//             }
//             ProvableStatement::ProductOf(ak1, ak2, ak3) => {
//                 middleware::Statement::ProductOf(ak1.into(), ak2.into(), ak3.into())
//             }
//             ProvableStatement::MaxOf(ak1, ak2, ak3) => {
//                 middleware::Statement::MaxOf(ak1.into(), ak2.into(), ak3.into())
//             }
//         }
//     }
// }

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProvableValue {
    String(String),
    Int(i64),
    Bool(bool),
    Dictionary(Dictionary),
    Set(Set),
    Array(Array),
    Raw(middleware::Value),
}

impl From<Value> for ProvableValue {
    fn from(value: Value) -> Self {
        match value {
            Value::String(s) => ProvableValue::String(s),
            Value::Int(i) => ProvableValue::Int(i),
            Value::Bool(b) => ProvableValue::Bool(b),
            Value::Dictionary(d) => ProvableValue::Dictionary(d),
            Value::Set(s) => ProvableValue::Set(s),
            Value::Array(a) => ProvableValue::Array(a),
            Value::Raw(r) => ProvableValue::Raw(r),
        }
    }
}

impl From<ProvableValue> for frontend::Value {
    fn from(value: ProvableValue) -> Self {
        match value {
            ProvableValue::String(s) => frontend::Value::String(s),
            ProvableValue::Int(i) => frontend::Value::Int(i),
            ProvableValue::Bool(b) => frontend::Value::Bool(b),
            ProvableValue::Dictionary(d) => frontend::Value::Dictionary(d),
            ProvableValue::Set(s) => frontend::Value::Set(s),
            ProvableValue::Array(a) => frontend::Value::Array(a),
            ProvableValue::Raw(r) => frontend::Value::Raw(r),
        }
    }
}

impl From<ProvableValue> for middleware::Value {
    fn from(value: ProvableValue) -> Self {
        match value {
            ProvableValue::String(s) => hash_str(&s).value(),
            ProvableValue::Int(v) => middleware::Value::from(v),
            ProvableValue::Bool(b) => middleware::Value::from(b as i64),
            ProvableValue::Dictionary(d) => d.middleware_dict().commitment().value(),
            ProvableValue::Set(s) => s.middleware_set().commitment().value(),
            ProvableValue::Array(a) => a.middleware_array().commitment().value(),
            ProvableValue::Raw(v) => v,
        }
    }
}

impl Hash for ProvableValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash the discriminant first
        std::mem::discriminant(self).hash(state);

        // Hash the inner values only for types that implement Hash
        match self {
            ProvableValue::String(s) => s.hash(state),
            ProvableValue::Int(i) => i.hash(state),
            ProvableValue::Bool(b) => b.hash(state),
            ProvableValue::Dictionary(d) => d.middleware_dict().commitment().hash(state),
            ProvableValue::Set(s) => s.middleware_set().commitment().hash(state),
            ProvableValue::Array(a) => a.middleware_array().commitment().hash(state),
            ProvableValue::Raw(r) => r.hash(state),
        }
    }
}

pub type DeductionStep = (u8, Vec<ProvableStatement>, ProvableStatement);
pub type DeductionChain = Vec<DeductionStep>;

// Helper function to format AnchoredKey
fn format_anchored_key(ak: &AnchoredKey) -> String {
    format!("{}:{}", ak.0 .1.to_string(), ak.1) // Show both origin ID and key
}

impl fmt::Display for ProvableValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProvableValue::String(s) => write!(f, "{}", s),
            ProvableValue::Int(i) => write!(f, "{}", i),
            ProvableValue::Bool(b) => write!(f, "{}", b),
            ProvableValue::Dictionary(d) => write!(f, "{:?}", d),
            ProvableValue::Set(s) => write!(f, "{:?}", s),
            ProvableValue::Array(a) => write!(f, "{:?}", a),
            ProvableValue::Raw(r) => write!(f, "{:?}", r),
        }
    }
}

impl fmt::Display for ProvableStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ValueOf(ak, v) => write!(f, "{} = {}", format_anchored_key(ak), v),
            Self::Equal(ak1, ak2) => write!(
                f,
                "{} = {}",
                format_anchored_key(ak1),
                format_anchored_key(ak2)
            ),
            Self::NotEqual(ak1, ak2) => write!(
                f,
                "{} ≠ {}",
                format_anchored_key(ak1),
                format_anchored_key(ak2)
            ),
            Self::Gt(ak1, ak2) => write!(
                f,
                "{} > {}",
                format_anchored_key(ak1),
                format_anchored_key(ak2)
            ),
            Self::Lt(ak1, ak2) => write!(
                f,
                "{} < {}",
                format_anchored_key(ak1),
                format_anchored_key(ak2)
            ),
            Self::Contains(ak1, ak2) => write!(
                f,
                "{} contains {}",
                format_anchored_key(ak1),
                format_anchored_key(ak2)
            ),
            Self::NotContains(ak1, ak2) => write!(
                f,
                "{} does not contain {}",
                format_anchored_key(ak1),
                format_anchored_key(ak2)
            ),
            Self::SumOf(ak1, ak2, ak3) => write!(
                f,
                "{} = {} + {}",
                format_anchored_key(ak1),
                format_anchored_key(ak2),
                format_anchored_key(ak3)
            ),
            Self::ProductOf(ak1, ak2, ak3) => write!(
                f,
                "{} = {} × {}",
                format_anchored_key(ak1),
                format_anchored_key(ak2),
                format_anchored_key(ak3)
            ),
            Self::MaxOf(ak1, ak2, ak3) => write!(
                f,
                "{} = max({}, {})",
                format_anchored_key(ak1),
                format_anchored_key(ak2),
                format_anchored_key(ak3)
            ),
        }
    }
}

pub fn operation_name(op_code: u8) -> &'static str {
    match op_code {
        x if x == NativeOperation::None as u8 => "None",
        x if x == NativeOperation::NewEntry as u8 => "NewEntry",
        x if x == NativeOperation::CopyStatement as u8 => "CopyStatement",
        x if x == NativeOperation::EqualFromEntries as u8 => "EqualFromEntries",
        x if x == NativeOperation::NotEqualFromEntries as u8 => "NotEqualFromEntries",
        x if x == NativeOperation::GtFromEntries as u8 => "GtFromEntries",
        x if x == NativeOperation::LtFromEntries as u8 => "LtFromEntries",
        x if x == NativeOperation::TransitiveEqualFromStatements as u8 => {
            "TransitiveEqualFromStatements"
        }
        x if x == NativeOperation::GtToNotEqual as u8 => "GtToNotEqual",
        x if x == NativeOperation::LtToNotEqual as u8 => "LtToNotEqual",
        x if x == NativeOperation::ContainsFromEntries as u8 => "ContainsFromEntries",
        x if x == NativeOperation::NotContainsFromEntries as u8 => "NotContainsFromEntries",
        x if x == NativeOperation::SumOf as u8 => "SumOf",
        x if x == NativeOperation::ProductOf as u8 => "ProductOf",
        x if x == NativeOperation::MaxOf as u8 => "MaxOf",
        _ => "Unknown Operation",
    }
}

// The core wildcard type - represents either a concrete origin or a named wildcard
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "type", content = "value")]
pub enum WildcardId {
    Concrete(Origin),
    Named(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(
    into = "WildcardAnchoredKeySerdeHelper",
    from = "WildcardAnchoredKeySerdeHelper"
)]
pub struct WildcardAnchoredKey(pub WildcardId, pub String);

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct WildcardAnchoredKeySerdeHelper {
    pub wildcard_id: WildcardId,
    pub key: String,
}

impl From<WildcardAnchoredKey> for WildcardAnchoredKeySerdeHelper {
    fn from(key: WildcardAnchoredKey) -> Self {
        WildcardAnchoredKeySerdeHelper {
            wildcard_id: key.0,
            key: key.1,
        }
    }
}

impl From<WildcardAnchoredKeySerdeHelper> for WildcardAnchoredKey {
    fn from(helper: WildcardAnchoredKeySerdeHelper) -> Self {
        WildcardAnchoredKey(helper.wildcard_id, helper.key)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum WildcardStatementArg {
    Literal(ProvableValue),
    Key(AnchoredKey),
}

// This is somewhat ugly but we're having to mirror some of the frontend/middleware
// type distinctions to get this to work. Probably there is a better way to do this.

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum FrontendWildcardStatement {
    Equal(WildcardAnchoredKey, WildcardStatementArg),
    NotEqual(WildcardAnchoredKey, WildcardStatementArg),
    Gt(WildcardAnchoredKey, WildcardStatementArg),
    Lt(WildcardAnchoredKey, WildcardStatementArg),
    Contains(WildcardAnchoredKey, WildcardStatementArg),
    NotContains(WildcardAnchoredKey, WildcardStatementArg),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum WildcardStatement {
    ValueOf(WildcardAnchoredKey, ProvableValue),
    Equal(WildcardAnchoredKey, AnchoredKey),
    NotEqual(WildcardAnchoredKey, AnchoredKey),
    Gt(WildcardAnchoredKey, AnchoredKey),
    Lt(WildcardAnchoredKey, AnchoredKey),
    Contains(WildcardAnchoredKey, AnchoredKey),
    NotContains(WildcardAnchoredKey, AnchoredKey),
}

// Helper methods for WildcardAnchoredKey
impl WildcardAnchoredKey {
    pub fn concrete(origin: Origin, key: String) -> Self {
        Self(WildcardId::Concrete(origin), key)
    }

    pub fn wildcard(key: String, name: impl Into<String>) -> Self {
        Self(WildcardId::Named(name.into()), key)
    }

    pub fn matches(&self, concrete: &AnchoredKey) -> bool {
        println!(
            "Matching wildcard {:?} against concrete key {:?}",
            self, concrete
        );
        let result = if let WildcardId::Concrete(origin) = &self.0 {
            let matches = *origin == concrete.0 && self.1 == concrete.1;
            println!(
                "  Concrete match: origin {} == {} ? {}",
                origin.1.to_string(),
                concrete.0 .1.to_string(),
                matches
            );
            matches
        } else if let WildcardId::Named(_) = &self.0 {
            let matches = self.1 == concrete.1;
            println!(
                "  Named match: key {} == {} ? {}",
                self.1, concrete.1, matches
            );
            matches
        } else {
            false
        };
        println!("  Final result: {}", result);
        result
    }
}
