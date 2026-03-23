#![allow(unused)]
use std::{collections::HashMap, fmt, hash as h, iter, iter::zip, sync::Arc};

use schemars::JsonSchema;

use crate::{
    frontend::{AnchoredKey, Error, Result, Statement, StatementArg},
    middleware::{
        self, hash_str, CustomPredicate, CustomPredicateBatch, Hash, Key, NativePredicate, Params,
        Predicate, StatementTmpl, StatementTmplArg, ToFields, Value, Wildcard,
    },
};

/// Builder Argument for the StatementTmplBuilder
#[derive(Clone, Debug)]
pub enum BuilderArg {
    Literal(Value),
    /// Key: (origin, key), where origin is Wildcard and key is Key
    Key(String, String),
    WildcardLiteral(String),
    /// Reference to a same-batch predicate's identity hash (resolved by name in finish()).
    SelfPredicateHash(String),
}

/// When defining a `BuilderArg`, it can be done from 3 different inputs:
///  i. (&str, &str): this is to define a origin-key pair, ie. attestation_pod["attestation"])
/// ii. &str: this is to define a Value wildcard, ie. distance
///
/// case i.
impl From<(&str, &str)> for BuilderArg {
    fn from((origin, field): (&str, &str)) -> Self {
        Self::Key(origin.to_string(), field.to_string())
    }
}
/// case ii.
impl From<&str> for BuilderArg {
    fn from(wc: &str) -> Self {
        Self::WildcardLiteral(wc.to_string())
    }
}

pub fn literal(v: impl Into<Value>) -> BuilderArg {
    BuilderArg::Literal(v.into())
}

#[derive(Clone, Debug)]
pub enum PredicateOrWildcard {
    Predicate(Predicate),
    Wildcard(String),
}

#[derive(Clone)]
pub struct StatementTmplBuilder {
    pub(crate) pred_or_wc: PredicateOrWildcard,
    pub(crate) args: Vec<BuilderArg>,
}

impl StatementTmplBuilder {
    pub fn new_from_pred(p: impl Into<Predicate>) -> StatementTmplBuilder {
        StatementTmplBuilder {
            pred_or_wc: PredicateOrWildcard::Predicate(p.into()),
            args: Vec::new(),
        }
    }
    pub fn new_from_wc(p: impl Into<String>) -> StatementTmplBuilder {
        StatementTmplBuilder {
            pred_or_wc: PredicateOrWildcard::Wildcard(p.into()),
            args: Vec::new(),
        }
    }
    pub fn new(pred_or_wc: PredicateOrWildcard) -> StatementTmplBuilder {
        StatementTmplBuilder {
            pred_or_wc,
            args: Vec::new(),
        }
    }

    pub fn arg(mut self, a: impl Into<BuilderArg>) -> Self {
        self.args.push(a.into());
        self
    }

    /// Desugar the predicate to a simpler form
    /// Should mirror the logic in `MainPodBuilder::lower_op`
    pub(crate) fn desugar(mut self) -> StatementTmplBuilder {
        let pred = match self.pred_or_wc {
            PredicateOrWildcard::Predicate(p) => p,
            PredicateOrWildcard::Wildcard(_) => return self,
        };
        let pred = match pred {
            Predicate::Native(nat_pred) => Predicate::Native(match nat_pred {
                NativePredicate::Gt => {
                    self.args.swap(0, 1);
                    NativePredicate::Lt
                }
                NativePredicate::GtEq => {
                    self.args.swap(0, 1);
                    NativePredicate::LtEq
                }
                NativePredicate::ArrayContains | NativePredicate::DictContains => {
                    NativePredicate::Contains
                }
                NativePredicate::DictNotContains | NativePredicate::SetNotContains => {
                    NativePredicate::NotContains
                }
                NativePredicate::SetContains => {
                    self.args.push(self.args[1].clone());
                    NativePredicate::Contains
                }
                NativePredicate::DictInsert => NativePredicate::ContainerInsert,
                NativePredicate::SetInsert => {
                    self.args.push(self.args[2].clone());
                    NativePredicate::ContainerInsert
                }
                NativePredicate::DictUpdate | NativePredicate::ArrayUpdate => {
                    NativePredicate::ContainerUpdate
                }
                NativePredicate::DictDelete => NativePredicate::ContainerDelete,
                NativePredicate::SetDelete => NativePredicate::ContainerDelete,
                _ => nat_pred,
            }),
            _ => pred,
        };
        StatementTmplBuilder {
            pred_or_wc: PredicateOrWildcard::Predicate(pred),
            args: self.args,
        }
    }
}

pub struct CustomPredicateBatchBuilder {
    params: Params,
    pub name: String,
    pub predicates: Vec<CustomPredicate>,
    /// Forward references to resolve in finish(): (predicate_idx, statement_idx, arg_idx, name)
    pending_self_pred_hashes: Vec<(usize, usize, usize, String)>,
}

impl CustomPredicateBatchBuilder {
    pub fn new(params: Params, name: String) -> Self {
        Self {
            params,
            name,
            predicates: Vec::new(),
            pending_self_pred_hashes: Vec::new(),
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
    pub fn predicate(
        &mut self,
        name: &str,
        conjunction: bool,
        args: &[&str],
        priv_args: &[&str],
        sts: &[StatementTmplBuilder],
    ) -> Result<Predicate> {
        if self.predicates.iter().any(|p| p.name == name) {
            return Err(Error::custom(format!(
                "Duplicate predicate name '{}' in batch",
                name
            )));
        }
        if self.predicates.len() >= Params::max_custom_batch_size() {
            return Err(Error::max_length(
                "self.predicates.len".to_string(),
                self.predicates.len(),
                Params::max_custom_batch_size(),
            ));
        }

        if args.len() > Params::max_statement_args() {
            return Err(Error::max_length(
                "args.len".to_string(),
                args.len(),
                Params::max_statement_args(),
            ));
        }
        if (args.len() + priv_args.len()) > self.params.max_custom_predicate_wildcards {
            return Err(Error::max_length(
                "wildcards.len".to_string(),
                args.len() + priv_args.len(),
                self.params.max_custom_predicate_wildcards,
            ));
        }

        let pred_idx = self.predicates.len();
        let mut pending = Vec::new();
        let statements = sts
            .iter()
            .enumerate()
            .map(|(stmt_idx, sb)| {
                let stb = sb.clone().desugar();
                let st_tmpl_args = stb
                    .args
                    .iter()
                    .enumerate()
                    .map(|(arg_idx, a)| {
                        Ok::<_, Error>(match a {
                            BuilderArg::Literal(v) => StatementTmplArg::Literal(v.clone()),
                            BuilderArg::Key(root_wc, key_str) => StatementTmplArg::AnchoredKey(
                                resolve_wildcard(args, priv_args, root_wc)?,
                                Key::from(key_str),
                            ),
                            BuilderArg::WildcardLiteral(v) => {
                                StatementTmplArg::Wildcard(resolve_wildcard(args, priv_args, v)?)
                            }
                            BuilderArg::SelfPredicateHash(pred_name) => {
                                // Try backward reference first
                                match self.predicates.iter().position(|p| p.name == *pred_name) {
                                    Some(index) => StatementTmplArg::SelfPredicateHash(index),
                                    None => {
                                        // Forward reference - placeholder, resolved in finish()
                                        pending.push((
                                            pred_idx,
                                            stmt_idx,
                                            arg_idx,
                                            pred_name.clone(),
                                        ));
                                        StatementTmplArg::SelfPredicateHash(0)
                                    }
                                }
                            }
                        })
                    })
                    .collect::<Result<_>>()?;
                let pred_or_wc = match stb.pred_or_wc {
                    PredicateOrWildcard::Predicate(p) => {
                        middleware::PredicateOrWildcard::Predicate(p)
                    }
                    PredicateOrWildcard::Wildcard(v) => middleware::PredicateOrWildcard::Wildcard(
                        resolve_wildcard(args, priv_args, &v)?,
                    ),
                };
                Ok(StatementTmpl {
                    pred_or_wc,
                    args: st_tmpl_args,
                })
            })
            .collect::<Result<_>>()?;
        let custom_predicate = CustomPredicate::new(
            &self.params,
            name.into(),
            conjunction,
            statements,
            args.len(),
            args.iter()
                .chain(priv_args.iter())
                .map(|s| s.to_string())
                .collect(),
        )?;
        self.predicates.push(custom_predicate);
        self.pending_self_pred_hashes.extend(pending);
        Ok(Predicate::BatchSelf(self.predicates.len() - 1))
    }

    pub fn finish(mut self) -> Result<Arc<CustomPredicateBatch>> {
        // Resolve forward references for SelfPredicateHash
        for (pred_idx, stmt_idx, arg_idx, ref name) in &self.pending_self_pred_hashes {
            let target_idx = self
                .predicates
                .iter()
                .position(|p| p.name == *name)
                .ok_or_else(|| {
                    Error::custom(format!(
                        "SelfPredicateHash references unknown predicate '{}'",
                        name
                    ))
                })?;
            self.predicates[*pred_idx].statements[*stmt_idx].args[*arg_idx] =
                StatementTmplArg::SelfPredicateHash(target_idx);
        }
        Ok(CustomPredicateBatch::new(self.name, self.predicates))
    }
}

fn resolve_wildcard(args: &[&str], priv_args: &[&str], s: &str) -> Result<Wildcard> {
    args.iter()
        .chain(priv_args.iter())
        .enumerate()
        .find_map(|(i, name)| (s == *name).then_some(Wildcard::new(s.to_string(), i)))
        .ok_or(Error::custom(format!(
            "Wildcard \"{}\" not amongst args {:?}",
            s,
            [args.to_vec(), priv_args.to_vec()].concat()
        )))
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;
    use crate::{
        backends::plonky2::mock::mainpod::MockProver,
        examples::{custom::eth_dos_batch, MOCK_VD_SET},
        frontend::{MainPodBuilder, Operation},
        middleware::{self, containers::Set, CustomPredicateRef, Params, PodType, DEFAULT_VD_SET},
    };

    #[test]
    fn test_custom_pred() -> Result<()> {
        use NativePredicate as NP;
        use StatementTmplBuilder as STB;

        let params = Params {
            max_custom_predicate_wildcards: 12,
            ..Default::default()
        };
        params.print_serialized_sizes();

        // ETH friend custom predicate batch
        let eth_dos_batch = eth_dos_batch(&params)?;

        // This batch only has 1 predicate, so we pick it already for convenience
        let eth_friend = eth_dos_batch.predicate_ref_by_name("eth_friend").unwrap();

        let eth_dos_batch_mw: middleware::CustomPredicateBatch =
            Arc::unwrap_or_clone(eth_dos_batch);

        Ok(())
    }

    #[test]
    fn test_desugared_gt_custom_pred() -> Result<()> {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;
        let mut builder = CustomPredicateBatchBuilder::new(params.clone(), "gt_custom_pred".into());

        let gt_stb = StatementTmplBuilder::new_from_pred(NativePredicate::Gt)
            .arg("s1")
            .arg("s2");

        builder.predicate_and("gt_custom_pred", &["s1", "s2"], &[], &[gt_stb])?;
        let batch = builder.finish()?;
        let batch_clone = batch.clone();
        let gt_custom_pred = CustomPredicateRef::new(batch, 0);

        let mut mp_builder = MainPodBuilder::new(&params, vd_set);

        // 2 > 1
        // Adding a gt operation will produce a desugared lt operation
        let desugared_gt = mp_builder.pub_op(Operation::gt(2, 1))?;
        assert_eq!(
            desugared_gt.predicate(),
            Predicate::Native(NativePredicate::Lt)
        );
        // Check that the desugared predicate is the same as the one in the statement template
        assert_eq!(
            desugared_gt.predicate(),
            *batch_clone.predicates()[0].statements[0]
                .pred_or_wc()
                .as_pred()
                .unwrap()
        );

        // Check that our custom predicate matches the statement template
        // against the desugared gt statement (actually a lt statement)
        mp_builder.pub_op(Operation::custom(gt_custom_pred, [desugared_gt]))?;

        // Check that the POD builds
        let prover = MockProver {};
        let proof = mp_builder.prove(&prover)?;

        Ok(())
    }

    #[test]
    fn test_desugared_set_contains_custom_pred() -> Result<()> {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;
        let mut builder =
            CustomPredicateBatchBuilder::new(params.clone(), "set_contains_custom_pred".into());

        let set_contains_stb = StatementTmplBuilder::new_from_pred(NativePredicate::SetContains)
            .arg("s1")
            .arg("s2");

        builder.predicate_and(
            "set_contains_custom_pred",
            &["s1", "s2"],
            &[],
            &[set_contains_stb],
        )?;
        let batch = builder.finish()?;
        let batch_clone = batch.clone();

        let mut mp_builder = MainPodBuilder::new(&params, vd_set);

        let set_values: HashSet<Value> = [1, 2, 3].iter().map(|i| Value::from(*i)).collect();
        let s1 = Set::new(set_values);
        let s2 = 1;

        let set_contains = mp_builder.pub_op(Operation::set_contains(s1, s2))?;
        assert_eq!(
            set_contains.predicate(),
            Predicate::Native(NativePredicate::Contains)
        );
        assert_eq!(
            set_contains.predicate(),
            *batch_clone.predicates()[0].statements[0]
                .pred_or_wc()
                .as_pred()
                .unwrap()
        );

        let set_contains_custom_pred = CustomPredicateRef::new(batch, 0);
        mp_builder.pub_op(Operation::custom(set_contains_custom_pred, [set_contains]))?;

        let prover = MockProver {};
        let proof = mp_builder.prove(&prover)?;

        Ok(())
    }

    #[test]
    fn test_builder_self_predicate_hash_unknown_ref() {
        let params = Params::default();
        let mut builder = CustomPredicateBatchBuilder::new(params.clone(), "batch".into());

        let stb = StatementTmplBuilder::new_from_pred(NativePredicate::Equal)
            .arg("x")
            .arg(BuilderArg::SelfPredicateHash("nonexistent".into()));
        builder
            .predicate_and("pred_A", &["x"], &[], &[stb])
            .unwrap();

        // finish() should fail because "nonexistent" was never defined
        assert!(builder.finish().is_err());
    }

    /// Tests cyclic SelfPredicateHash references end-to-end:
    /// pred_A references pred_B's hash (forward ref), pred_B references pred_A's hash (backward
    /// ref). Exercises forward reference resolution in finish(), then builds and verifies a POD
    /// using pred_A via MockProver.
    #[test]
    fn test_builder_self_predicate_hash_e2e() -> Result<()> {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;

        let mut builder = CustomPredicateBatchBuilder::new(params.clone(), "batch".into());

        // pred_A references pred_B's hash (forward ref, pred_B not yet defined)
        let stb_a = StatementTmplBuilder::new_from_pred(NativePredicate::Equal)
            .arg("x")
            .arg(BuilderArg::SelfPredicateHash("pred_B".into()));
        builder.predicate_and("pred_A", &["x"], &[], &[stb_a])?;

        // pred_B references pred_A's hash (backward ref, pred_A already defined)
        let stb_b = StatementTmplBuilder::new_from_pred(NativePredicate::Equal)
            .arg("x")
            .arg(BuilderArg::SelfPredicateHash("pred_A".into()));
        builder.predicate_and("pred_B", &["x"], &[], &[stb_b])?;

        let batch = builder.finish()?;

        // Verify resolution: pred_A references pred_B (index 1), pred_B references pred_A (index 0)
        assert_eq!(
            batch.predicates()[0].statements[0].args[1],
            StatementTmplArg::SelfPredicateHash(1)
        );
        assert_eq!(
            batch.predicates()[1].statements[0].args[1],
            StatementTmplArg::SelfPredicateHash(0)
        );

        // Compute concrete hashes
        let pred_a_ref = CustomPredicateRef::new(batch.clone(), 0);
        let pred_b_ref = CustomPredicateRef::new(batch.clone(), 1);
        let pred_b_hash = Value::from(Predicate::Custom(pred_b_ref.clone()).hash());

        // Build a POD using pred_A: Equal(pred_b_hash, pred_b_hash)
        let mut mp_builder = MainPodBuilder::new(&params, vd_set);
        let eq_st = mp_builder.priv_op(Operation::eq(pred_b_hash.clone(), pred_b_hash.clone()))?;
        mp_builder.pub_op(Operation::custom(pred_a_ref, [eq_st]))?;

        // Prove and verify
        let prover = MockProver {};
        let proof = mp_builder.prove(&prover)?;
        proof.pod.verify()?;

        // Verify the public statement contains pred_b_hash as its argument
        let pub_sts = proof.pod.pub_self_statements();
        let custom_st = pub_sts
            .iter()
            .find(|s| matches!(s, middleware::Statement::Custom(_, _)))
            .expect("should have a custom statement");
        if let middleware::Statement::Custom(_, args) = custom_st {
            assert_eq!(args[0], pred_b_hash);
        }

        Ok(())
    }
}
