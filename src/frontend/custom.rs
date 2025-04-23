#![allow(unused)]
use std::{collections::HashMap, fmt, hash as h, iter, iter::zip, sync::Arc};

use schemars::JsonSchema;

use crate::{
    frontend::{AnchoredKey, Error, Result, Statement, StatementArg},
    middleware::{
        self, hash_str, CustomPredicate, CustomPredicateBatch, Key, KeyOrWildcard, NativePredicate,
        Params, PodId, Predicate, StatementTmpl, StatementTmplArg, ToFields, Value, Wildcard,
    },
};

#[derive(Clone, Debug, PartialEq, Eq)]
/// Argument to a statement template
pub enum KeyOrWildcardStr {
    Key(String), // represents a literal key
    Wildcard(String),
}

/// helper to build a literal KeyOrWildcardStr::Key from the given str
pub fn key(s: &str) -> KeyOrWildcardStr {
    KeyOrWildcardStr::Key(s.to_string())
}

/// Builder Argument for the StatementTmplBuilder
pub enum BuilderArg {
    Literal(Value),
    /// Key: (origin, key), where origin is a Wildcard and key can be both Key or Wildcard
    Key(String, KeyOrWildcardStr),
    WildcardLiteral(String),
}

/// When defining a `BuilderArg`, it can be done from 3 different inputs:
///   i. (&str, literal): this is to set a POD and a field, ie. (POD, literal("field"))
///  ii. (&str, &str): this is to define a origin-key wildcard pair, ie. (src_origin, src_dest)
/// iii. &str: this is to define a WildcardValue wildcard, ie. "src_or"
///
/// case i.
impl From<(&str, KeyOrWildcardStr)> for BuilderArg {
    fn from((origin, lit): (&str, KeyOrWildcardStr)) -> Self {
        // ensure that `lit` is of HashOrWildcardStr::Hash type
        match lit {
            KeyOrWildcardStr::Key(_) => (),
            _ => panic!("not supported"),
        };
        Self::Key(origin.into(), lit)
    }
}
/// case ii.
impl From<(&str, &str)> for BuilderArg {
    fn from((origin, field): (&str, &str)) -> Self {
        Self::Key(origin.into(), KeyOrWildcardStr::Wildcard(field.to_string()))
    }
}
/// case iii.
impl From<&str> for BuilderArg {
    fn from(wc: &str) -> Self {
        Self::WildcardLiteral(wc.to_string())
    }
}

pub fn literal(v: impl Into<Value>) -> BuilderArg {
    BuilderArg::Literal(v.into())
}

pub struct StatementTmplBuilder {
    predicate: Predicate,
    args: Vec<BuilderArg>,
}

impl StatementTmplBuilder {
    pub fn new(p: impl Into<Predicate>) -> StatementTmplBuilder {
        StatementTmplBuilder {
            predicate: p.into(),
            args: Vec::new(),
        }
    }

    pub fn arg(mut self, a: impl Into<BuilderArg>) -> Self {
        self.args.push(a.into());
        self
    }
}

pub struct CustomPredicateBatchBuilder {
    pub name: String,
    pub predicates: Vec<CustomPredicate>,
}

impl CustomPredicateBatchBuilder {
    pub fn new(name: String) -> Self {
        Self {
            name,
            predicates: Vec::new(),
        }
    }

    pub fn predicate_and(
        &mut self,
        name: &str,
        params: &Params,
        args: &[&str],
        priv_args: &[&str],
        sts: &[StatementTmplBuilder],
    ) -> Result<Predicate> {
        self.predicate(name, params, true, args, priv_args, sts)
    }

    pub fn predicate_or(
        &mut self,
        name: &str,
        params: &Params,
        args: &[&str],
        priv_args: &[&str],
        sts: &[StatementTmplBuilder],
    ) -> Result<Predicate> {
        self.predicate(name, params, false, args, priv_args, sts)
    }

    /// creates the custom predicate from the given input, adds it to the
    /// self.predicates, and returns the index of the created predicate
    fn predicate(
        &mut self,
        name: &str,
        params: &Params,
        conjunction: bool,
        args: &[&str],
        priv_args: &[&str],
        sts: &[StatementTmplBuilder],
    ) -> Result<Predicate> {
        if args.len() > params.max_statement_args {
            return Err(Error::max_length(
                "args.len".to_string(),
                args.len(),
                params.max_statement_args,
            ));
        }
        if (args.len() + priv_args.len()) > params.max_custom_predicate_wildcards {
            return Err(Error::max_length(
                "wildcards.len".to_string(),
                args.len() + priv_args.len(),
                params.max_custom_predicate_wildcards,
            ));
        }

        let statements = sts
            .iter()
            .map(|sb| {
                let args = sb
                    .args
                    .iter()
                    .map(|a| match a {
                        BuilderArg::Literal(v) => StatementTmplArg::Literal(v.clone()),
                        BuilderArg::Key(pod_id, key) => StatementTmplArg::Key(
                            resolve_wildcard(args, priv_args, pod_id),
                            resolve_key_or_wildcard(args, priv_args, key),
                        ),
                        BuilderArg::WildcardLiteral(v) => {
                            StatementTmplArg::WildcardLiteral(resolve_wildcard(args, priv_args, v))
                        }
                    })
                    .collect();
                StatementTmpl {
                    pred: sb.predicate.clone(),
                    args,
                }
            })
            .collect();
        let custom_predicate =
            CustomPredicate::new(name.into(), params, conjunction, statements, args.len())?;
        self.predicates.push(custom_predicate);
        Ok(Predicate::BatchSelf(self.predicates.len() - 1))
    }

    pub fn finish(self) -> Arc<CustomPredicateBatch> {
        Arc::new(CustomPredicateBatch {
            name: self.name,
            predicates: self.predicates,
        })
    }
}

fn resolve_key_or_wildcard(
    args: &[&str],
    priv_args: &[&str],
    v: &KeyOrWildcardStr,
) -> KeyOrWildcard {
    match v {
        KeyOrWildcardStr::Key(k) => KeyOrWildcard::Key(Key::from(k)),
        KeyOrWildcardStr::Wildcard(s) => {
            KeyOrWildcard::Wildcard(resolve_wildcard(args, priv_args, s))
        }
    }
}

fn resolve_wildcard(args: &[&str], priv_args: &[&str], s: &str) -> Wildcard {
    args.iter()
        .chain(priv_args.iter())
        .enumerate()
        .find_map(|(i, name)| (s == *name).then_some(Wildcard::new(s.to_string(), i)))
        .unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        examples::custom::{eth_dos_batch, eth_friend_batch},
        middleware,
        middleware::{CustomPredicateRef, Params, PodType},
    };

    #[test]
    fn test_custom_pred() -> Result<()> {
        use NativePredicate as NP;
        use StatementTmplBuilder as STB;

        let params = Params {
            max_statement_args: 6,
            max_custom_predicate_wildcards: 12,
            ..Default::default()
        };
        params.print_serialized_sizes();

        // ETH friend custom predicate batch
        let eth_friend = eth_friend_batch(&params)?;

        // This batch only has 1 predicate, so we pick it already for convenience
        let eth_friend = Predicate::Custom(CustomPredicateRef::new(eth_friend, 0));

        let eth_dos_batch = eth_dos_batch(&params)?;
        let eth_dos_batch_mw: middleware::CustomPredicateBatch =
            Arc::unwrap_or_clone(eth_dos_batch);
        let fields = eth_dos_batch_mw.to_fields(&params);
        println!("Batch b, serialized: {:?}", fields);

        Ok(())
    }
}
