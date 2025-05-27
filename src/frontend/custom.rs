#![allow(unused)]
use std::{collections::HashMap, fmt, hash as h, iter, iter::zip, sync::Arc};

use schemars::JsonSchema;

use crate::{
    frontend::{AnchoredKey, Error, Result, Statement, StatementArg},
    middleware::{
        self, hash_str, CustomPredicate, CustomPredicateBatch, Key, KeyOrWildcard, NativePredicate,
        Params, PodId, Predicate, SelfOrWildcard, StatementTmpl, StatementTmplArg, ToFields, Value,
        Wildcard,
    },
};

#[derive(Clone, Debug, PartialEq, Eq)]
/// Argument to a statement template
pub enum KeyOrWildcardStr {
    Key(String), // represents a literal key
    Wildcard(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SelfOrWildcardStr {
    SELF,
    Wildcard(String),
}

/// helper to build a literal KeyOrWildcardStr::Key from the given str
pub fn key(s: &str) -> KeyOrWildcardStr {
    KeyOrWildcardStr::Key(s.to_string())
}

/// Builder Argument for the StatementTmplBuilder
#[derive(Clone, Debug)]
pub enum BuilderArg {
    Literal(Value),
    /// Key: (origin, key), where origin is SELF or Wildcard and key is Key or Wildcard
    Key(SelfOrWildcardStr, KeyOrWildcardStr),
    WildcardLiteral(String),
}

impl From<&str> for SelfOrWildcardStr {
    fn from(origin: &str) -> Self {
        if origin == "SELF" {
            SelfOrWildcardStr::SELF
        } else {
            SelfOrWildcardStr::Wildcard(origin.into())
        }
    }
}

/// When defining a `BuilderArg`, it can be done from 3 different inputs:
///   i. (&str, literal): this is to set a POD and a field, ie. (POD, literal("field"))
///  ii. (&str, &str): this is to define a origin-key wildcard pair, ie. (src_origin, src_dest)
/// iii. &str: this is to define a WildcardValue wildcard, ie. "src_or"
///
/// case i.
impl From<(&str, KeyOrWildcardStr)> for BuilderArg {
    fn from((origin, lit): (&str, KeyOrWildcardStr)) -> Self {
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

#[derive(Clone)]
pub struct StatementTmplBuilder {
    pub(crate) predicate: Predicate,
    pub(crate) args: Vec<BuilderArg>,
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

    /// Desugar the predicate to a simpler form
    /// Should mirror the logic in `MainPodBuilder::lower_op`
    pub(crate) fn desugar(self) -> StatementTmplBuilder {
        match self.predicate {
            Predicate::Native(NativePredicate::Gt) => {
                let mut stb = StatementTmplBuilder {
                    predicate: Predicate::Native(NativePredicate::Lt),
                    args: self.args,
                };
                stb.args.swap(0, 1);
                stb
            }
            Predicate::Native(NativePredicate::GtEq) => {
                let mut stb = StatementTmplBuilder {
                    predicate: Predicate::Native(NativePredicate::LtEq),
                    args: self.args,
                };
                stb.args.swap(0, 1);
                stb
            }
            Predicate::Native(NativePredicate::ArrayContains)
            | Predicate::Native(NativePredicate::DictContains) => StatementTmplBuilder {
                predicate: Predicate::Native(NativePredicate::Contains),
                args: self.args,
            },
            Predicate::Native(NativePredicate::DictNotContains)
            | Predicate::Native(NativePredicate::SetNotContains) => StatementTmplBuilder {
                predicate: Predicate::Native(NativePredicate::NotContains),
                args: self.args,
            },
            Predicate::Native(NativePredicate::SetContains) => {
                let mut new_args = self.args.clone();
                new_args.push(self.args[1].clone());
                StatementTmplBuilder {
                    predicate: Predicate::Native(NativePredicate::Contains),
                    args: new_args,
                }
            }
            _ => self,
        }
    }
}

pub struct CustomPredicateBatchBuilder {
    params: Params,
    pub name: String,
    pub predicates: Vec<CustomPredicate>,
}

impl CustomPredicateBatchBuilder {
    pub fn new(params: Params, name: String) -> Self {
        Self {
            params,
            name,
            predicates: Vec::new(),
        }
    }

    pub fn predicate_and(
        &mut self,
        name: &str,
        args: &[&str],
        priv_args: &[&str],
        sts: &[StatementTmplBuilder],
    ) -> Result<Predicate> {
        self.predicate(name, true, args, priv_args, sts)
    }

    pub fn predicate_or(
        &mut self,
        name: &str,
        args: &[&str],
        priv_args: &[&str],
        sts: &[StatementTmplBuilder],
    ) -> Result<Predicate> {
        self.predicate(name, false, args, priv_args, sts)
    }

    /// creates the custom predicate from the given input, adds it to the
    /// self.predicates, and returns the index of the created predicate
    fn predicate(
        &mut self,
        name: &str,
        conjunction: bool,
        args: &[&str],
        priv_args: &[&str],
        sts: &[StatementTmplBuilder],
    ) -> Result<Predicate> {
        if self.predicates.len() >= self.params.max_custom_batch_size {
            return Err(Error::max_length(
                "self.predicates.len".to_string(),
                self.predicates.len(),
                self.params.max_custom_batch_size,
            ));
        }

        if args.len() > self.params.max_statement_args {
            return Err(Error::max_length(
                "args.len".to_string(),
                args.len(),
                self.params.max_statement_args,
            ));
        }
        if (args.len() + priv_args.len()) > self.params.max_custom_predicate_wildcards {
            return Err(Error::max_length(
                "wildcards.len".to_string(),
                args.len() + priv_args.len(),
                self.params.max_custom_predicate_wildcards,
            ));
        }

        let statements = sts
            .iter()
            .map(|sb| {
                let stb = sb.clone().desugar();
                let args = stb
                    .args
                    .iter()
                    .map(|a| match a {
                        BuilderArg::Literal(v) => StatementTmplArg::Literal(v.clone()),
                        BuilderArg::Key(pod_id, key) => StatementTmplArg::AnchoredKey(
                            resolve_self_or_wildcard(args, priv_args, pod_id),
                            resolve_key_or_wildcard(args, priv_args, key),
                        ),
                        BuilderArg::WildcardLiteral(v) => {
                            StatementTmplArg::WildcardLiteral(resolve_wildcard(args, priv_args, v))
                        }
                    })
                    .collect();
                StatementTmpl {
                    pred: stb.predicate.clone(),
                    args,
                }
            })
            .collect();
        let custom_predicate = CustomPredicate::new(
            &self.params,
            name.into(),
            conjunction,
            statements,
            args.len(),
        )?;
        self.predicates.push(custom_predicate);
        Ok(Predicate::BatchSelf(self.predicates.len() - 1))
    }

    pub fn finish(self) -> Arc<CustomPredicateBatch> {
        CustomPredicateBatch::new(&self.params, self.name, self.predicates)
    }
}

fn resolve_self_or_wildcard(
    args: &[&str],
    priv_args: &[&str],
    v: &SelfOrWildcardStr,
) -> SelfOrWildcard {
    match v {
        SelfOrWildcardStr::SELF => SelfOrWildcard::SELF,
        SelfOrWildcardStr::Wildcard(s) => {
            SelfOrWildcard::Wildcard(resolve_wildcard(args, priv_args, s))
        }
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
    use std::collections::HashSet;

    use super::*;
    use crate::{
        backends::plonky2::mock::mainpod::MockProver,
        examples::custom::{eth_dos_batch, eth_friend_batch},
        frontend::MainPodBuilder,
        middleware::{self, containers::Set, CustomPredicateRef, Params, PodType},
        op,
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
        let eth_friend = eth_friend_batch(&params, true)?;

        // This batch only has 1 predicate, so we pick it already for convenience
        let eth_friend = Predicate::Custom(CustomPredicateRef::new(eth_friend, 0));

        let eth_dos_batch = eth_dos_batch(&params, true)?;
        let eth_dos_batch_mw: middleware::CustomPredicateBatch =
            Arc::unwrap_or_clone(eth_dos_batch);
        let fields = eth_dos_batch_mw.to_fields(&params);
        println!("Batch b, serialized: {:?}", fields);

        Ok(())
    }

    #[test]
    fn test_desugared_gt_custom_pred() -> Result<()> {
        let params = Params::default();
        let mut builder = CustomPredicateBatchBuilder::new(params.clone(), "gt_custom_pred".into());

        let gt_stb = StatementTmplBuilder::new(NativePredicate::Gt)
            .arg(("s1_origin", "s1_key"))
            .arg(("s2_origin", "s2_key"));

        builder.predicate_and(
            "gt_custom_pred",
            &["s1_origin", "s1_key", "s2_origin", "s2_key"],
            &[],
            &[gt_stb],
        )?;
        let batch = builder.finish();
        let batch_clone = batch.clone();
        let gt_custom_pred = CustomPredicateRef::new(batch, 0);

        let mut mp_builder = MainPodBuilder::new(&params);

        // 2 > 1
        let s1 = mp_builder.literal(true, Value::from(2))?;
        let s2 = mp_builder.literal(true, Value::from(1))?;

        // Adding a gt operation will produce a desugared lt operation
        let desugared_gt = mp_builder.pub_op(op!(gt, s1, s2))?;
        assert_eq!(
            desugared_gt.predicate(),
            Predicate::Native(NativePredicate::Lt)
        );
        // Check that the desugared predicate is the same as the one in the statement template
        assert_eq!(
            desugared_gt.predicate(),
            *batch_clone.predicates()[0].statements[0].pred()
        );

        // Check that our custom predicate matches the statement template
        // against the desugared gt statement (actually a lt statement)
        mp_builder.pub_op(op!(custom, gt_custom_pred, desugared_gt))?;

        // Check that the POD builds
        let mut prover = MockProver {};
        let proof = mp_builder.prove(&mut prover, &params)?;

        Ok(())
    }

    #[test]
    fn test_desugared_set_contains_custom_pred() -> Result<()> {
        let params = Params::default();
        let mut builder =
            CustomPredicateBatchBuilder::new(params.clone(), "set_contains_custom_pred".into());

        let set_contains_stb = StatementTmplBuilder::new(NativePredicate::SetContains)
            .arg(("s1_origin", "s1_key"))
            .arg(("s2_origin", "s2_key"));

        builder.predicate_and(
            "set_contains_custom_pred",
            &["s1_origin", "s1_key", "s2_origin", "s2_key"],
            &[],
            &[set_contains_stb],
        )?;
        let batch = builder.finish();
        let batch_clone = batch.clone();

        let mut mp_builder = MainPodBuilder::new(&params);

        let set_values: HashSet<Value> = [1, 2, 3].iter().map(|i| Value::from(*i)).collect();
        let s1 = mp_builder.literal(true, Value::from(Set::new(set_values)?))?;
        let s2 = mp_builder.literal(true, Value::from(1))?;

        let set_contains = mp_builder.pub_op(op!(set_contains, s1, s2))?;
        assert_eq!(
            set_contains.predicate(),
            Predicate::Native(NativePredicate::Contains)
        );
        assert_eq!(
            set_contains.predicate(),
            *batch_clone.predicates()[0].statements[0].pred()
        );

        let set_contains_custom_pred = CustomPredicateRef::new(batch, 0);
        mp_builder.pub_op(op!(custom, set_contains_custom_pred, set_contains))?;

        let mut prover = MockProver {};
        let proof = mp_builder.prove(&mut prover, &params)?;

        Ok(())
    }
}
