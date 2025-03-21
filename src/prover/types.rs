use crate::frontend::{self, AnchoredKey, Origin, Value};
use crate::middleware::{NativeOperation, NativePredicate, Predicate};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use std::fmt;
use std::hash::{Hash, Hasher};

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
pub enum ProvableStatement {
    ValueOf(AnchoredKey, Value),
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
            ProvableStatement::ValueOf(ak, v) => frontend::Statement {
                predicate: Predicate::Native(NativePredicate::ValueOf),
                args: vec![
                    frontend::StatementArg::Key(ak.into()),
                    frontend::StatementArg::Literal(v.into()),
                ],
            },
            ProvableStatement::Equal(ak1, ak2) => frontend::Statement {
                predicate: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    frontend::StatementArg::Key(ak1.into()),
                    frontend::StatementArg::Key(ak2.into()),
                ],
            },
            ProvableStatement::NotEqual(ak1, ak2) => frontend::Statement {
                predicate: Predicate::Native(NativePredicate::NotEqual),
                args: vec![
                    frontend::StatementArg::Key(ak1.into()),
                    frontend::StatementArg::Key(ak2.into()),
                ],
            },
            ProvableStatement::Gt(ak1, ak2) => frontend::Statement {
                predicate: Predicate::Native(NativePredicate::Gt),
                args: vec![
                    frontend::StatementArg::Key(ak1.into()),
                    frontend::StatementArg::Key(ak2.into()),
                ],
            },
            ProvableStatement::Lt(ak1, ak2) => frontend::Statement {
                predicate: Predicate::Native(NativePredicate::Lt),
                args: vec![
                    frontend::StatementArg::Key(ak1.into()),
                    frontend::StatementArg::Key(ak2.into()),
                ],
            },
            ProvableStatement::Contains(ak1, ak2) => frontend::Statement {
                predicate: Predicate::Native(NativePredicate::Contains),
                args: vec![
                    frontend::StatementArg::Key(ak1.into()),
                    frontend::StatementArg::Key(ak2.into()),
                ],
            },
            ProvableStatement::NotContains(ak1, ak2) => frontend::Statement {
                predicate: Predicate::Native(NativePredicate::NotContains),
                args: vec![
                    frontend::StatementArg::Key(ak1.into()),
                    frontend::StatementArg::Key(ak2.into()),
                ],
            },
            ProvableStatement::SumOf(ak1, ak2, ak3) => frontend::Statement {
                predicate: Predicate::Native(NativePredicate::SumOf),
                args: vec![
                    frontend::StatementArg::Key(ak1.into()),
                    frontend::StatementArg::Key(ak2.into()),
                    frontend::StatementArg::Key(ak3.into()),
                ],
            },
            ProvableStatement::ProductOf(ak1, ak2, ak3) => frontend::Statement {
                predicate: Predicate::Native(NativePredicate::ProductOf),
                args: vec![
                    frontend::StatementArg::Key(ak1.into()),
                    frontend::StatementArg::Key(ak2.into()),
                    frontend::StatementArg::Key(ak3.into()),
                ],
            },
            ProvableStatement::MaxOf(ak1, ak2, ak3) => frontend::Statement {
                predicate: Predicate::Native(NativePredicate::MaxOf),
                args: vec![
                    frontend::StatementArg::Key(ak1.into()),
                    frontend::StatementArg::Key(ak2.into()),
                    frontend::StatementArg::Key(ak3.into()),
                ],
            },
        }
    }
}

impl From<frontend::Statement> for ProvableStatement {
    fn from(stmt: frontend::Statement) -> Self {
        match stmt.predicate {
            Predicate::Native(NativePredicate::ValueOf) => {
                if let (frontend::StatementArg::Key(key), frontend::StatementArg::Literal(value)) =
                    (stmt.args[0].clone(), stmt.args[1].clone())
                {
                    ProvableStatement::ValueOf(key.into(), value.into())
                } else {
                    panic!("Invalid arguments for ValueOf statement")
                }
            }
            Predicate::Native(NativePredicate::Equal) => {
                if let (frontend::StatementArg::Key(key1), frontend::StatementArg::Key(key2)) =
                    (stmt.args[0].clone(), stmt.args[1].clone())
                {
                    ProvableStatement::Equal(key1.into(), key2.into())
                } else {
                    panic!("Invalid arguments for Equal statement")
                }
            }
            Predicate::Native(NativePredicate::NotEqual) => {
                if let (frontend::StatementArg::Key(key1), frontend::StatementArg::Key(key2)) =
                    (stmt.args[0].clone(), stmt.args[1].clone())
                {
                    ProvableStatement::NotEqual(key1.into(), key2.into())
                } else {
                    panic!("Invalid arguments for NotEqual statement")
                }
            }
            Predicate::Native(NativePredicate::Gt) => {
                if let (frontend::StatementArg::Key(key1), frontend::StatementArg::Key(key2)) =
                    (stmt.args[0].clone(), stmt.args[1].clone())
                {
                    ProvableStatement::Gt(key1.into(), key2.into())
                } else {
                    panic!("Invalid arguments for Gt statement")
                }
            }
            Predicate::Native(NativePredicate::Lt) => {
                if let (frontend::StatementArg::Key(key1), frontend::StatementArg::Key(key2)) =
                    (stmt.args[0].clone(), stmt.args[1].clone())
                {
                    ProvableStatement::Lt(key1.into(), key2.into())
                } else {
                    panic!("Invalid arguments for Lt statement")
                }
            }
            Predicate::Native(NativePredicate::Contains) => {
                if let (frontend::StatementArg::Key(key1), frontend::StatementArg::Key(key2)) =
                    (stmt.args[0].clone(), stmt.args[1].clone())
                {
                    ProvableStatement::Contains(key1.into(), key2.into())
                } else {
                    panic!("Invalid arguments for Contains statement")
                }
            }
            Predicate::Native(NativePredicate::NotContains) => {
                if let (frontend::StatementArg::Key(key1), frontend::StatementArg::Key(key2)) =
                    (stmt.args[0].clone(), stmt.args[1].clone())
                {
                    ProvableStatement::NotContains(key1.into(), key2.into())
                } else {
                    panic!("Invalid arguments for NotContains statement")
                }
            }
            Predicate::Native(NativePredicate::SumOf) => {
                if let (
                    frontend::StatementArg::Key(key1),
                    frontend::StatementArg::Key(key2),
                    frontend::StatementArg::Key(key3),
                ) = (
                    stmt.args[0].clone(),
                    stmt.args[1].clone(),
                    stmt.args[2].clone(),
                ) {
                    ProvableStatement::SumOf(key1.into(), key2.into(), key3.into())
                } else {
                    panic!("Invalid arguments for SumOf statement")
                }
            }
            Predicate::Native(NativePredicate::ProductOf) => {
                if let (
                    frontend::StatementArg::Key(key1),
                    frontend::StatementArg::Key(key2),
                    frontend::StatementArg::Key(key3),
                ) = (
                    stmt.args[0].clone(),
                    stmt.args[1].clone(),
                    stmt.args[2].clone(),
                ) {
                    ProvableStatement::ProductOf(key1.into(), key2.into(), key3.into())
                } else {
                    panic!("Invalid arguments for ProductOf statement")
                }
            }
            Predicate::Native(NativePredicate::MaxOf) => {
                if let (
                    frontend::StatementArg::Key(key1),
                    frontend::StatementArg::Key(key2),
                    frontend::StatementArg::Key(key3),
                ) = (
                    stmt.args[0].clone(),
                    stmt.args[1].clone(),
                    stmt.args[2].clone(),
                ) {
                    ProvableStatement::MaxOf(key1.into(), key2.into(), key3.into())
                } else {
                    panic!("Invalid arguments for MaxOf statement")
                }
            }
            _ => panic!("Cannot convert non-native statement to ProvableStatement"),
        }
    }
}

impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash the discriminant first
        std::mem::discriminant(self).hash(state);

        // Hash the inner values only for types that implement Hash
        match self {
            Value::String(s) => s.hash(state),
            Value::Int(i) => i.hash(state),
            Value::Bool(b) => b.hash(state),
            Value::Dictionary(d) => d.middleware_dict().commitment().hash(state),
            Value::Set(s) => s.middleware_set().commitment().hash(state),
            Value::Array(a) => a.middleware_array().commitment().hash(state),
            Value::Raw(r) => r.hash(state),
        }
    }
}

pub type DeductionStep = (NativeOperation, Vec<ProvableStatement>, ProvableStatement);
pub type DeductionChain = Vec<DeductionStep>;

// Helper function to format AnchoredKey
fn format_anchored_key(ak: &AnchoredKey) -> String {
    format!("{:x}:{}", ak.origin.pod_id, ak.key) // Show both origin ID and key
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

// The core wildcard type - represents either a concrete origin or a named wildcard
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
pub enum WildcardId {
    Concrete(Origin),
    Named(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
pub struct WildcardAnchoredKey {
    pub wildcard_id: WildcardId,
    pub key: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
pub enum WildcardStatementArg {
    Literal(Value),
    Key(AnchoredKey),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
pub enum WildcardTargetStatement {
    Equal(WildcardAnchoredKey, WildcardStatementArg),
    NotEqual(WildcardAnchoredKey, WildcardStatementArg),
    Gt(WildcardAnchoredKey, WildcardStatementArg),
    Lt(WildcardAnchoredKey, WildcardStatementArg),
    Contains(WildcardAnchoredKey, WildcardStatementArg),
    NotContains(WildcardAnchoredKey, WildcardStatementArg),
    SumOf(
        WildcardAnchoredKey,
        WildcardStatementArg,
        WildcardStatementArg,
    ),
    ProductOf(
        WildcardAnchoredKey,
        WildcardStatementArg,
        WildcardStatementArg,
    ),
    MaxOf(
        WildcardAnchoredKey,
        WildcardStatementArg,
        WildcardStatementArg,
    ),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, JsonSchema)]
pub enum WildcardStatement {
    ValueOf(WildcardAnchoredKey, Value),
    Equal(WildcardAnchoredKey, AnchoredKey),
    NotEqual(WildcardAnchoredKey, AnchoredKey),
    Gt(WildcardAnchoredKey, AnchoredKey),
    Lt(WildcardAnchoredKey, AnchoredKey),
    Contains(WildcardAnchoredKey, AnchoredKey),
    NotContains(WildcardAnchoredKey, AnchoredKey),
    SumOf(WildcardAnchoredKey, AnchoredKey, AnchoredKey),
    ProductOf(WildcardAnchoredKey, AnchoredKey, AnchoredKey),
    MaxOf(WildcardAnchoredKey, AnchoredKey, AnchoredKey),
}

// Helper methods for WildcardAnchoredKey
impl WildcardAnchoredKey {
    pub fn concrete(origin: Origin, key: String) -> Self {
        Self {
            wildcard_id: WildcardId::Concrete(origin),
            key,
        }
    }

    pub fn wildcard(key: String, name: impl Into<String>) -> Self {
        Self {
            wildcard_id: WildcardId::Named(name.into()),
            key,
        }
    }

    pub fn matches(&self, concrete: &AnchoredKey) -> bool {
        println!(
            "Matching wildcard {:?} against concrete key {:?}",
            self, concrete
        );
        let result = if let WildcardId::Concrete(origin) = &self.wildcard_id {
            let matches = *origin == concrete.origin && self.key == concrete.key;
            println!(
                "  Concrete match: origin {} == {} ? {}",
                origin.pod_id.to_string(),
                concrete.origin.pod_id.to_string(),
                matches
            );
            matches
        } else if let WildcardId::Named(_) = &self.wildcard_id {
            let matches = self.key == concrete.key;
            println!(
                "  Named match: key {} == {} ? {}",
                self.key, concrete.key, matches
            );
            matches
        } else {
            false
        };
        println!("  Final result: {}", result);
        result
    }
}
