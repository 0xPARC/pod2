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
            Predicate::Native(NativePredicate::DictInsert) => StatementTmplBuilder {
                predicate: Predicate::Native(NativePredicate::ContainerInsert),
                args: self.args,
            },
            Predicate::Native(NativePredicate::SetInsert) => {
                let mut new_args = self.args.clone();
                new_args.push(self.args[2].clone());
                StatementTmplBuilder {
                    predicate: Predicate::Native(NativePredicate::ContainerInsert),
                    args: new_args,
                }
            }
            Predicate::Native(NativePredicate::DictUpdate)
            | Predicate::Native(NativePredicate::ArrayUpdate) => StatementTmplBuilder {
                predicate: Predicate::Native(NativePredicate::ContainerUpdate),
                args: self.args,
            },
            Predicate::Native(NativePredicate::DictDelete) => StatementTmplBuilder {
                predicate: Predicate::Native(NativePredicate::ContainerDelete),
                args: self.args,
            },
            Predicate::Native(NativePredicate::SetDelete) => {
                let mut new_args = self.args.clone();
                new_args.push(self.args[2].clone());
                StatementTmplBuilder {
                    predicate: Predicate::Native(NativePredicate::ContainerDelete),
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
                    .map(|a| {
                        Ok::<_, Error>(match a {
                            BuilderArg::Literal(v) => StatementTmplArg::Literal(v.clone()),
                            BuilderArg::Key(root_wc, key_str) => StatementTmplArg::AnchoredKey(
                                resolve_wildcard(args, priv_args, root_wc)?,
                                Key::from(key_str),
                            ),
                            BuilderArg::WildcardLiteral(v) => {
                                StatementTmplArg::Wildcard(resolve_wildcard(args, priv_args, v)?)
                            }
                        })
                    })
                    .collect::<Result<_>>()?;
                Ok(StatementTmpl {
                    pred: stb.predicate.clone(),
                    args,
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
        Ok(Predicate::BatchSelf(self.predicates.len() - 1))
    }

    pub fn finish(self) -> Arc<CustomPredicateBatch> {
        CustomPredicateBatch::new(&self.params, self.name, self.predicates)
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
            max_statement_args: 6,
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
        let fields = eth_dos_batch_mw.to_fields(&params);
        println!("Batch b, serialized: {:?}", fields);

        Ok(())
    }

    #[test]
    fn test_desugared_gt_custom_pred() -> Result<()> {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;
        let mut builder = CustomPredicateBatchBuilder::new(params.clone(), "gt_custom_pred".into());

        let gt_stb = StatementTmplBuilder::new(NativePredicate::Gt)
            .arg("s1")
            .arg("s2");

        builder.predicate_and("gt_custom_pred", &["s1", "s2"], &[], &[gt_stb])?;
        let batch = builder.finish();
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
            *batch_clone.predicates()[0].statements[0].pred()
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

        let set_contains_stb = StatementTmplBuilder::new(NativePredicate::SetContains)
            .arg("s1")
            .arg("s2");

        builder.predicate_and(
            "set_contains_custom_pred",
            &["s1", "s2"],
            &[],
            &[set_contains_stb],
        )?;
        let batch = builder.finish();
        let batch_clone = batch.clone();

        let mut mp_builder = MainPodBuilder::new(&params, vd_set);

        let set_values: HashSet<Value> = [1, 2, 3].iter().map(|i| Value::from(*i)).collect();
        let s1 = Set::new(params.max_depth_mt_containers, set_values)?;
        let s2 = 1;

        let set_contains = mp_builder.pub_op(Operation::set_contains(s1, s2))?;
        assert_eq!(
            set_contains.predicate(),
            Predicate::Native(NativePredicate::Contains)
        );
        assert_eq!(
            set_contains.predicate(),
            *batch_clone.predicates()[0].statements[0].pred()
        );

        let set_contains_custom_pred = CustomPredicateRef::new(batch, 0);
        mp_builder.pub_op(Operation::custom(set_contains_custom_pred, [set_contains]))?;

        let prover = MockProver {};
        let proof = mp_builder.prove(&prover)?;

        Ok(())
    }
}
