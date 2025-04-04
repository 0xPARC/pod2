#![allow(unused)]
use anyhow::{anyhow, Result};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::iter::zip;
use std::sync::Arc;
use std::{fmt, hash as h, iter};

use crate::middleware::{self, hash_str, HashOrWildcard, Params, PodId, ToFields};
use crate::util::hashmap_insert_no_dupe;

use super::{AnchoredKey, NativePredicate, Origin, Statement, StatementArg, Value};

#[derive(Clone, Debug, PartialEq, Eq, h::Hash, Serialize, Deserialize, JsonSchema)]
/// Argument to a statement template
pub enum KeyOrWildcardStr {
    Key(String), // represents a literal key
    Wildcard(String),
}

#[derive(Clone, Debug, PartialEq, Eq, h::Hash, Serialize, Deserialize, JsonSchema)]
pub struct IndexedWildcard {
    wildcard: String,
    index: usize,
}

impl IndexedWildcard {
    pub fn new(wildcard: String, index: usize) -> Self {
        Self { wildcard, index }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, h::Hash, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
/// Represents a key or resolved wildcard
pub enum KeyOrWildcard {
    Key(String),
    Wildcard(IndexedWildcard),
}

impl KeyOrWildcard {
    /// Matches a key or wildcard against a value, returning a pair
    /// representing a wildcard binding (if any) or an error if no
    /// match is possible.
    pub fn match_against(&self, v: &Value) -> Result<Option<(usize, Value)>> {
        match self {
            KeyOrWildcard::Key(k) if Value::from(k.as_str()) == *v => Ok(None),
            KeyOrWildcard::Wildcard(i) => Ok(Some((i.index, v.clone()))),
            _ => Err(anyhow!(
                "Failed to match key or wildcard {} against value {}.",
                self,
                v
            )),
        }
    }
}

impl From<KeyOrWildcard> for middleware::HashOrWildcard {
    fn from(v: KeyOrWildcard) -> Self {
        match v {
            KeyOrWildcard::Key(k) => middleware::HashOrWildcard::Hash(hash_str(&k)),
            KeyOrWildcard::Wildcard(n) => middleware::HashOrWildcard::Wildcard(n.index),
        }
    }
}
impl fmt::Display for KeyOrWildcard {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Key(k) => write!(f, "{}", k),
            Self::Wildcard(n) => write!(f, "*{}", n.wildcard),
        }
    }
}

/// helper to build a literal KeyOrWildcardStr::Key from the given str
pub fn literal(s: &str) -> KeyOrWildcardStr {
    KeyOrWildcardStr::Key(s.to_string())
}

/// helper to build a KeyOrWildcardStr::Wildcard from the given str. For the
/// moment this method does not need to be public.
fn wildcard(s: &str) -> KeyOrWildcardStr {
    KeyOrWildcardStr::Wildcard(s.to_string())
}

/// Builder Argument for the StatementTmplBuilder
pub enum BuilderArg {
    Literal(Value),
    /// Key: (origin, key), where origin & key can be both Hash or Wildcard
    Key(KeyOrWildcardStr, KeyOrWildcardStr),
}

/// When defining a `BuilderArg`, it can be done from 3 different inputs:
///   i. (&str, literal): this is to set a POD and a field, ie. (POD, literal("field"))
///  ii. (&str, &str): this is to define a origin-key wildcard pair, ie. (src_origin, src_dest)
/// iii. Value: this is to define a literal value, ie. 0
///
/// case i.
impl From<(&str, KeyOrWildcardStr)> for BuilderArg {
    fn from((origin, lit): (&str, KeyOrWildcardStr)) -> Self {
        // ensure that `lit` is of HashOrWildcardStr::Hash type
        match lit {
            KeyOrWildcardStr::Key(_) => (),
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
pub enum Predicate {
    Native(NativePredicate),
    BatchSelf(usize),
    Custom(CustomPredicateRef),
}

impl From<NativePredicate> for Predicate {
    fn from(v: NativePredicate) -> Self {
        Self::Native(v)
    }
}

impl From<Predicate> for middleware::Predicate {
    fn from(v: Predicate) -> Self {
        match v {
            Predicate::Native(p) => middleware::Predicate::Native(p.into()),
            Predicate::BatchSelf(i) => middleware::Predicate::BatchSelf(i),
            Predicate::Custom(CustomPredicateRef {
                batch: pb,
                index: i,
            }) => {
                let cpb: middleware::CustomPredicateBatch = Arc::unwrap_or_clone(pb).into();
                middleware::Predicate::Custom(middleware::CustomPredicateRef(Arc::new(cpb), i))
            }
        }
    }
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Native(p) => write!(f, "{:?}", p),
            Self::BatchSelf(i) => write!(f, "self.{}", i),
            Self::Custom(CustomPredicateRef { batch, index }) => {
                write!(f, "{}.{}", batch.name, index)
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct CustomPredicateRef {
    pub batch: Arc<CustomPredicateBatch>,
    pub index: usize,
}

impl From<CustomPredicateRef> for middleware::CustomPredicateRef {
    fn from(v: CustomPredicateRef) -> Self {
        let cpb: middleware::CustomPredicateBatch = Arc::unwrap_or_clone(v.batch).into();
        middleware::CustomPredicateRef(Arc::new(cpb), v.index)
    }
}

impl CustomPredicateRef {
    pub fn new(batch: Arc<CustomPredicateBatch>, index: usize) -> Self {
        Self { batch, index }
    }

    pub fn arg_len(&self) -> usize {
        self.batch.predicates[self.index].args_len
    }
    pub fn match_against(&self, statements: &[Statement]) -> Result<HashMap<usize, Value>> {
        let mut bindings = HashMap::new();
        // Single out custom predicate, replacing batch-self
        // references with custom predicate references.
        let custom_predicate = {
            let cp = &Arc::unwrap_or_clone(self.batch.clone()).predicates[self.index];
            CustomPredicate {
                conjunction: cp.conjunction,
                statements: cp
                    .statements
                    .iter()
                    .map(|StatementTmpl { pred: p, args }| StatementTmpl {
                        pred: match p {
                            Predicate::BatchSelf(i) => {
                                Predicate::Custom(CustomPredicateRef::new(self.batch.clone(), *i))
                            }
                            _ => p.clone(),
                        },
                        args: args.to_vec(),
                    })
                    .collect(),
                args_len: cp.args_len,
                name: cp.name.to_string(),
            }
        };
        match custom_predicate.conjunction {
                    true if custom_predicate.statements.len() == statements.len() => {
                        // Match op args against statement templates
                    let match_bindings = iter::zip(custom_predicate.statements, statements).map(
                        |(s_tmpl, s)| s_tmpl.match_against(s)
                    ).collect::<Result<Vec<_>>>()
                        .map(|v| v.concat())?;
                    // Add bindings to binding table, throwing if there is an inconsistency.
                    match_bindings.into_iter().try_for_each(|kv| hashmap_insert_no_dupe(&mut bindings, kv))?;
                    Ok(bindings)
                    },
                    false if statements.len() == 1 => {
                        // Match op arg against each statement template
                        custom_predicate.statements.iter().map(
                            |s_tmpl| {
                                let mut bindings = bindings.clone();
                                s_tmpl.match_against(&statements[0])?.into_iter().try_for_each(|kv| hashmap_insert_no_dupe(&mut bindings, kv))?;
                                Ok::<_, anyhow::Error>(bindings)
                            }
                        ).find(|m| m.is_ok()).unwrap_or(Err(anyhow!("Statement {} does not match disjunctive custom predicate {}.", &statements[0], custom_predicate)))
                    },
                    _ =>                     Err(anyhow!("Custom predicate statement template list {:?} does not match op argument list {:?}.", custom_predicate.statements, statements))
                }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct CustomPredicateBatch {
    pub name: String,
    pub predicates: Vec<CustomPredicate>,
}

impl From<CustomPredicateBatch> for middleware::CustomPredicateBatch {
    fn from(v: CustomPredicateBatch) -> Self {
        middleware::CustomPredicateBatch {
            name: v.name,
            predicates: v.predicates.into_iter().map(|p| p.into()).collect(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct CustomPredicate {
    /// NOTE: fields are not public (outside of crate) to enforce the struct instantiation through
    /// the `::and/or` methods, which performs checks on the values.

    /// true for "and", false for "or"
    pub(crate) conjunction: bool,
    pub(crate) statements: Vec<StatementTmpl>,
    pub(crate) args_len: usize,
    // TODO: Add private args length?
    // TODO: Add args type information?
    pub(crate) name: String,
}

impl CustomPredicate {
    pub fn and(
        params: &Params,
        statements: Vec<StatementTmpl>,
        args_len: usize,
        name: &str,
    ) -> Result<Self> {
        Self::new(params, true, statements, args_len, name)
    }
    pub fn or(
        params: &Params,
        statements: Vec<StatementTmpl>,
        args_len: usize,
        name: &str,
    ) -> Result<Self> {
        Self::new(params, false, statements, args_len, name)
    }
    pub fn new(
        params: &Params,
        conjunction: bool,
        statements: Vec<StatementTmpl>,
        args_len: usize,
        name: &str,
    ) -> Result<Self> {
        if statements.len() > params.max_custom_predicate_arity {
            return Err(anyhow!("Custom predicate depends on too many statements"));
        }

        Ok(Self {
            conjunction,
            statements,
            args_len,
            name: name.to_string(),
        })
    }
}

impl From<CustomPredicate> for middleware::CustomPredicate {
    fn from(v: CustomPredicate) -> Self {
        middleware::CustomPredicate {
            conjunction: v.conjunction,
            statements: v.statements.into_iter().map(|s| s.into()).collect(),
            args_len: v.args_len,
        }
    }
}
impl fmt::Display for CustomPredicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "{}<", if self.conjunction { "and" } else { "or" })?;
        for st in &self.statements {
            write!(f, "  {}", st.pred)?;
            for (i, arg) in st.args.iter().enumerate() {
                if i != 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", arg)?;
            }
            writeln!(f, "),")?;
        }
        write!(f, ">(")?;
        for i in 0..self.args_len {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "*{}", i)?;
        }
        writeln!(f, ")")?;
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, h::Hash, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
pub enum StatementTmplArg {
    None,
    Literal(Value),
    //  #[schemars(with = "Vec<KeyOrWildcard>")]
    Key(KeyOrWildcard, KeyOrWildcard),
}

impl From<StatementTmplArg> for middleware::StatementTmplArg {
    fn from(v: StatementTmplArg) -> Self {
        match v {
            StatementTmplArg::None => middleware::StatementTmplArg::None,
            StatementTmplArg::Literal(v) => middleware::StatementTmplArg::Literal((&v).into()),
            StatementTmplArg::Key(pod_id, key) => {
                middleware::StatementTmplArg::Key(pod_id.into(), key.into())
            }
        }
    }
}

impl fmt::Display for StatementTmplArg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::None => write!(f, "none"),
            Self::Literal(v) => write!(f, "{}", v),
            Self::Key(pod_id, key) => write!(f, "({}, {})", pod_id, key),
        }
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct StatementTmpl {
    pub pred: Predicate,
    pub args: Vec<StatementTmplArg>,
}

impl StatementTmpl {
    pub fn pred(&self) -> &Predicate {
        &self.pred
    }
    pub fn args(&self) -> &[StatementTmplArg] {
        &self.args
    }
    /// Matches a statement template against a statement, returning
    /// the variable bindings as an association list. Returns an error
    /// if there is type or argument mismatch.
    pub fn match_against(&self, s: &Statement) -> Result<Vec<(usize, Value)>> {
        type P = Predicate;
        if matches!(
            self,
            Self {
                pred: P::BatchSelf(_),
                args: _
            }
        ) {
            Err(anyhow!(
                "Cannot check self-referencing statement templates."
            ))
        } else if self.pred() != &s.predicate {
            Err(anyhow!("Type mismatch between {:?} and {}.", self, s))
        } else {
            zip(self.args(), s.args.clone())
                .map(|(t_arg, s_arg)| t_arg.match_against(&s_arg))
                .collect::<Result<Vec<_>>>()
                .map(|v| v.concat())
        }
    }
}

impl From<StatementTmpl> for middleware::StatementTmpl {
    fn from(v: StatementTmpl) -> Self {
        middleware::StatementTmpl(
            v.pred.into(),
            v.args.into_iter().map(|a| a.into()).collect(),
        )
    }
}

impl StatementTmplArg {
    /// Matches a statement template argument against a statement
    /// argument, returning a wildcard correspondence in the case of
    /// one or more wildcard matches, nothing in the case of a
    /// literal/hash match, and an error otherwise.
    pub fn match_against(&self, s_arg: &StatementArg) -> Result<Vec<(usize, Value)>> {
        match (self, s_arg) {
            //    (Self::None, StatementArg::None) => Ok(vec![]),
            (Self::Literal(v), StatementArg::Literal(w)) if v == w => Ok(vec![]),
            (
                Self::Key(tmpl_o, tmpl_k),
                StatementArg::Key(AnchoredKey {
                    origin: Origin { pod_id: PodId(o) },
                    key: k,
                }),
            ) => {
                let o_corr = tmpl_o.match_against(&(middleware::Value::from(*o)).into())?;
                let k_corr = tmpl_k.match_against(&(*k.as_str()).into())?;
                Ok([o_corr, k_corr].into_iter().flatten().collect())
            }
            _ => Err(anyhow!(
                "Failed to match statement template argument {:?} against statement argument {:?}.",
                self,
                s_arg
            )),
        }
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
        name: &str,
    ) -> Result<Predicate> {
        self.predicate(params, true, args, priv_args, sts, name)
    }

    pub fn predicate_or(
        &mut self,
        params: &Params,
        args: &[&str],
        priv_args: &[&str],
        sts: &[StatementTmplBuilder],
        name: &str,
    ) -> Result<Predicate> {
        self.predicate(params, false, args, priv_args, sts, name)
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
        name: &str,
    ) -> Result<Predicate> {
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
                            resolve_wildcard(args, priv_args, key),
                        ),
                    })
                    .collect();
                StatementTmpl {
                    pred: sb.predicate.clone(),
                    args,
                }
            })
            .collect();
        let custom_predicate =
            CustomPredicate::new(params, conjunction, statements, args.len(), name)?;
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

fn resolve_wildcard(args: &[&str], priv_args: &[&str], v: &KeyOrWildcardStr) -> KeyOrWildcard {
    match v {
        KeyOrWildcardStr::Key(k) => KeyOrWildcard::Key(k.clone()),
        KeyOrWildcardStr::Wildcard(s) => KeyOrWildcard::Wildcard(
            args.iter()
                .chain(priv_args.iter())
                .enumerate()
                .find_map(|(i, name)| (&s == name).then_some(IndexedWildcard::new(s.clone(), i)))
                .unwrap(),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        examples::custom::{eth_dos_batch, eth_friend_batch},
        middleware,
        //   middleware::{CustomPredicateRef, Params, PodType},
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
        let eth_friend = Predicate::Custom(CustomPredicateRef::new(eth_friend, 0));

        let eth_dos_batch = eth_dos_batch(&params)?;
        let eth_dos_batch_mw: middleware::CustomPredicateBatch =
            Arc::unwrap_or_clone(eth_dos_batch).into();
        let fields = eth_dos_batch_mw.to_fields(&params);
        println!("Batch b, serialized: {:?}", fields);

        Ok(())
    }
}
