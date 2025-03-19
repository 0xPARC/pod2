#![allow(unused)]
use anyhow::Result;
use std::sync::Arc;

use crate::middleware::{
    hash_str, CustomPredicate, CustomPredicateBatch, Hash, HashOrWildcard, NativePredicate, Params,
    Predicate, StatementTmpl, StatementTmplArg, ToFields, Value, F,
};

/// Argument to a statement template
pub enum HashOrWildcardStr {
    Hash(Hash), // represents a literal key
    Wildcard(String),
}

/// helper to build a literal HashOrWildcardStr::Hash from the given str
pub fn literal(s: &str) -> HashOrWildcardStr {
    HashOrWildcardStr::Hash(hash_str(s))
}

/// helper to build a HashOrWildcardStr::Wildcard from the given str. For the
/// moment this method does not need to be public.
fn wildcard(s: &str) -> HashOrWildcardStr {
    HashOrWildcardStr::Wildcard(s.to_string())
}

/// Builder Argument for the StatementTmplBuilder
pub enum BuilderArg {
    Literal(Value),
    /// Key: (origin, key), where origin & key can be both Hash or Wildcard
    Key(HashOrWildcardStr, HashOrWildcardStr),
}

/// When defining a `BuilderArg`, it can be done from 3 different inputs:
///   i. (&str, literal): this is to set a POD and a field, ie. (POD, literal("field"))
///  ii. (&str, &str): this is to define a origin-key wildcard pair, ie. (src_origin, src_dest)
/// iii. Value: this is to define a literal value, ie. 0
///
/// case i.
impl From<(&str, HashOrWildcardStr)> for BuilderArg {
    fn from((origin, lit): (&str, HashOrWildcardStr)) -> Self {
        // ensure that `lit` is of HashOrWildcardStr::Hash type
        match lit {
            HashOrWildcardStr::Hash(_) => (),
            _ => panic!("not supported"),
        };
        Self::Key(wildcard(origin), lit)
    }
}
/// case ii.
impl From<(&str, &str)> for BuilderArg {
    fn from((origin, field): (&str, &str)) -> Self {
        Self::Key(wildcard(origin), wildcard(field))
    }
}
/// case iii.
impl<V> From<V> for BuilderArg
where
    V: Into<Value>,
{
    fn from(v: V) -> Self {
        Self::Literal(v.into())
    }
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
        params: &Params,
        args: &[&str],
        priv_args: &[&str],
        sts: &[StatementTmplBuilder],
    ) -> Result<Predicate> {
        self.predicate(params, true, args, priv_args, sts)
    }

    pub fn predicate_or(
        &mut self,
        params: &Params,
        args: &[&str],
        priv_args: &[&str],
        sts: &[StatementTmplBuilder],
    ) -> Result<Predicate> {
        self.predicate(params, false, args, priv_args, sts)
    }

    /// creates the custom predicate from the given input, adds it to the
    /// self.predicates, and returns the index of the created predicate
    fn predicate(
        &mut self,
        params: &Params,
        conjunction: bool,
        args: &[&str],
        priv_args: &[&str],
        sts: &[StatementTmplBuilder],
    ) -> Result<Predicate> {
        let statements = sts
            .iter()
            .map(|sb| {
                let args = sb
                    .args
                    .iter()
                    .map(|a| match a {
                        BuilderArg::Literal(v) => StatementTmplArg::Literal(*v),
                        BuilderArg::Key(pod_id, key) => StatementTmplArg::Key(
                            resolve_wildcard(args, priv_args, pod_id),
                            resolve_wildcard(args, priv_args, key),
                        ),
                    })
                    .collect();
                StatementTmpl(sb.predicate.clone(), args)
            })
            .collect();
        let custom_predicate = CustomPredicate::new(params, conjunction, statements, args.len())?;
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

fn resolve_wildcard(args: &[&str], priv_args: &[&str], v: &HashOrWildcardStr) -> HashOrWildcard {
    match v {
        HashOrWildcardStr::Hash(h) => HashOrWildcard::Hash(*h),
        HashOrWildcardStr::Wildcard(s) => HashOrWildcard::Wildcard(
            args.iter()
                .chain(priv_args.iter())
                .enumerate()
                .find_map(|(i, name)| (&s == name).then_some(i))
                .unwrap(),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        examples::custom::{eth_dos_batch, eth_friend_batch},
        middleware::{CustomPredicateRef, Params, PodType},
    };

    #[test]
    fn test_custom_pred() -> Result<()> {
        use NativePredicate as NP;
        use StatementTmplBuilder as STB;

        let params = Params::default();
        params.print_serialized_sizes();

        // ETH friend custom predicate batch
        let eth_friend = eth_friend_batch(&params)?;

        // This batch only has 1 predicate, so we pick it already for convenience
        let eth_friend = Predicate::Custom(CustomPredicateRef(eth_friend, 0));

        let eth_dos_batch = eth_dos_batch(&params)?;
        let fields = eth_dos_batch.to_fields(&params);
        println!("Batch b, serialized: {:?}", fields);

        Ok(())
    }
}
