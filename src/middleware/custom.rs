use std::{collections::HashMap, fmt, iter, iter::zip, sync::Arc};

use anyhow::{anyhow, Result};
use plonky2::field::types::Field;

// use schemars::JsonSchema;

// use serde::{Deserialize, Serialize};
use crate::{
    middleware::HASH_SIZE,
    middleware::{
        hash_fields, AnchoredKey, Hash, Key, NativePredicate, Params, PodId, Statement,
        StatementArg, ToFields, Value, F,
    },
    util::hashmap_insert_no_dupe,
};

#[derive(Clone, Debug, PartialEq)]
pub struct Wildcard {
    pub name: String,
    pub index: usize,
}

impl Wildcard {
    pub fn new(name: String, index: usize) -> Self {
        Self { name, index }
    }
}

impl fmt::Display for Wildcard {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "*{}[{}]", self.index, self.name)
    }
}

impl ToFields for Wildcard {
    fn to_fields(&self, _params: &Params) -> Vec<F> {
        vec![F::from_canonical_u64(self.index as u64)]
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum KeyOrWildcard {
    Key(Key),
    Wildcard(Wildcard),
}

impl KeyOrWildcard {
    // /// Matches a key or wildcard against a value, returning a pair
    // /// representing a wildcard binding (if any) or an error if no
    // /// match is possible.
    // pub fn match_against(&self, v: &Value) -> Result<Option<(usize, Value)>> {
    //     match self {
    //         // TODO: What does this mean? Comparing a key with a value?
    //         KeyOrWildcard::Key(k) if k.hash().0 == v.raw().0 => Ok(None),
    //         KeyOrWildcard::Wildcard(Wildcard { index, .. }) => Ok(Some((*index, v.clone()))),
    //         _ => Err(anyhow!(
    //             "Failed to match key or wildcard {} against value {}.",
    //             self,
    //             v
    //         )),
    //     }
    // }
}

impl fmt::Display for KeyOrWildcard {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Key(k) => write!(f, "{}", k),
            Self::Wildcard(wc) => write!(f, "{}", wc),
        }
    }
}

impl ToFields for KeyOrWildcard {
    fn to_fields(&self, params: &Params) -> Vec<F> {
        match self {
            KeyOrWildcard::Key(k) => k.hash().to_fields(params),
            KeyOrWildcard::Wildcard(wc) => iter::once(F::ZERO)
                .take(HASH_SIZE - 1)
                .chain(iter::once(F::from_canonical_u64(wc.index as u64)))
                .collect(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum StatementTmplArg {
    None,
    Literal(Value),
    // AnchoredKey
    Key(Wildcard, KeyOrWildcard),
}

impl StatementTmplArg {
    // /// Matches a statement template argument against a statement
    // /// argument, returning a wildcard correspondence in the case of
    // /// one or more wildcard matches, nothing in the case of a
    // /// literal/hash match, and an error otherwise.
    // pub fn match_against(&self, s_arg: &StatementArg) -> Result<Vec<(usize, Value)>> {
    //     match (self, s_arg) {
    //         (Self::None, StatementArg::None) => Ok(vec![]),
    //         (Self::Literal(v), StatementArg::Literal(w)) if v == w => Ok(vec![]),
    //         (
    //             Self::Key(tmpl_o, tmpl_k),
    //             StatementArg::Key(AnchoredKey {
    //                 pod_id: PodId(o),
    //                 key,
    //             }),
    //         ) => {
    //             let o_corr = tmpl_o.match_against(&(*o).into())?;
    //             let k_corr = tmpl_k.match_against(&key.hash().into())?;
    //             Ok([o_corr, k_corr].into_iter().flatten().collect())
    //         }
    //         _ => Err(anyhow!(
    //             "Failed to match statement template argument {:?} against statement argument {:?}.",
    //             self,
    //             s_arg
    //         )),
    //     }
    // }
}

impl ToFields for StatementTmplArg {
    fn to_fields(&self, params: &Params) -> Vec<F> {
        // None => (0, ...)
        // Literal(value) => (1, [value], 0, 0, 0, 0)
        // Key(hash_or_wildcard1, hash_or_wildcard2)
        //    => (2, [hash_or_wildcard1], [hash_or_wildcard2])
        // In all three cases, we pad to 2 * hash_size + 1 = 9 field elements
        let statement_tmpl_arg_size = 2 * HASH_SIZE + 1;
        match self {
            StatementTmplArg::None => {
                let fields: Vec<F> = iter::repeat_with(|| F::from_canonical_u64(0))
                    .take(statement_tmpl_arg_size)
                    .collect();
                fields
            }
            StatementTmplArg::Literal(v) => {
                let fields: Vec<F> = iter::once(F::from_canonical_u64(1))
                    .chain(v.raw().to_fields(params))
                    .chain(iter::repeat_with(|| F::from_canonical_u64(0)).take(HASH_SIZE))
                    .collect();
                fields
            }
            StatementTmplArg::Key(hw1, hw2) => {
                let fields: Vec<F> = iter::once(F::from_canonical_u64(2))
                    .chain(hw1.to_fields(params))
                    .chain(hw2.to_fields(params))
                    .collect();
                fields
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

/// Statement Template for a Custom Predicate
#[derive(Clone, Debug, PartialEq)]
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
    // /// Matches a statement template against a statement, returning
    // /// the variable bindings as an association list. Returns an error
    // /// if there is type or argument mismatch.
    // pub fn match_against(&self, s: &Statement) -> Result<Vec<(usize, Value)>> {
    //     type P = Predicate;
    //     if matches!(self, Self(P::BatchSelf(_), _)) {
    //         Err(anyhow!(
    //             "Cannot check self-referencing statement templates."
    //         ))
    //     } else if self.pred() != &s.predicate() {
    //         Err(anyhow!("Type mismatch between {:?} and {}.", self, s))
    //     } else {
    //         zip(self.args(), s.args())
    //             .map(|(t_arg, s_arg)| t_arg.match_against(&s_arg))
    //             .collect::<Result<Vec<_>>>()
    //             .map(|v| v.concat())
    //     }
    // }
}

impl ToFields for StatementTmpl {
    fn to_fields(&self, params: &Params) -> Vec<F> {
        // serialize as:
        // predicate (6 field elements)
        // then the StatementTmplArgs

        // TODO think if this check should go into the StatementTmpl creation,
        // instead of at the `to_fields` method, where we should assume that the
        // values are already valid
        if self.args.len() > params.max_statement_args {
            panic!("Statement template has too many arguments");
        }

        let mut fields: Vec<F> = self
            .pred
            .to_fields(params)
            .into_iter()
            .chain(self.args.iter().flat_map(|sta| sta.to_fields(params)))
            .collect();
        fields.resize_with(params.statement_tmpl_size(), || F::from_canonical_u64(0));
        fields
    }
}

#[derive(Clone, Debug, PartialEq)]
/// NOTE: fields are not public (outside of crate) to enforce the struct instantiation through
/// the `::and/or` methods, which performs checks on the values.
pub struct CustomPredicate {
    pub name: String, // Non-cryptographic metadata
    /// true for "and", false for "or"
    pub(crate) conjunction: bool,
    pub(crate) statements: Vec<StatementTmpl>,
    pub(crate) args_len: usize,
    // TODO: Add private args length?
    // TODO: Add args type information?
}

impl CustomPredicate {
    pub fn and(
        name: String,
        params: &Params,
        statements: Vec<StatementTmpl>,
        args_len: usize,
    ) -> Result<Self> {
        Self::new(name, params, true, statements, args_len)
    }
    pub fn or(
        name: String,
        params: &Params,
        statements: Vec<StatementTmpl>,
        args_len: usize,
    ) -> Result<Self> {
        Self::new(name, params, false, statements, args_len)
    }
    pub fn new(
        name: String,
        params: &Params,
        conjunction: bool,
        statements: Vec<StatementTmpl>,
        args_len: usize,
    ) -> Result<Self> {
        if statements.len() > params.max_custom_predicate_arity {
            return Err(anyhow!("Custom predicate depends on too many statements"));
        }

        Ok(Self {
            name,
            conjunction,
            statements,
            args_len,
        })
    }
}

impl ToFields for CustomPredicate {
    fn to_fields(&self, params: &Params) -> Vec<F> {
        // serialize as:
        // conjunction (one field element)
        // args_len (one field element)
        // statements
        //   (params.max_custom_predicate_arity * params.statement_tmpl_size())
        //   field elements

        // NOTE: this method assumes that the self.params.len() is inside the
        // expected bound, as Self should be instantiated with the constructor
        // method `new` which performs the check.
        if self.statements.len() > params.max_custom_predicate_arity {
            panic!("Custom predicate depends on too many statements");
        }

        let mut fields: Vec<F> = iter::once(F::from_bool(self.conjunction))
            .chain(iter::once(F::from_canonical_usize(self.args_len)))
            .chain(self.statements.iter().flat_map(|st| st.to_fields(params)))
            .collect();
        fields.resize_with(params.custom_predicate_size(), || F::from_canonical_u64(0));
        fields
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

#[derive(Clone, Debug, PartialEq)]
pub struct CustomPredicateBatch {
    pub name: String,
    pub predicates: Vec<CustomPredicate>,
}

impl ToFields for CustomPredicateBatch {
    fn to_fields(&self, params: &Params) -> Vec<F> {
        // all the custom predicates in order

        // TODO think if this check should go into the StatementTmpl creation,
        // instead of at the `to_fields` method, where we should assume that the
        // values are already valid
        if self.predicates.len() > params.max_custom_batch_size {
            panic!("Predicate batch exceeds maximum size");
        }

        let mut fields: Vec<F> = self
            .predicates
            .iter()
            .flat_map(|p| p.to_fields(params))
            .collect();
        fields.resize_with(params.custom_predicate_batch_size_field_elts(), || {
            F::from_canonical_u64(0)
        });
        fields
    }
}

impl CustomPredicateBatch {
    pub fn hash(&self, params: &Params) -> Hash {
        let input = self.to_fields(params);

        hash_fields(&input)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct CustomPredicateRef {
    pub batch: Arc<CustomPredicateBatch>,
    pub index: usize,
}

impl CustomPredicateRef {
    pub fn new(batch: Arc<CustomPredicateBatch>, index: usize) -> Self {
        Self { batch, index }
    }
    pub fn arg_len(&self) -> usize {
        self.batch.predicates[self.index].args_len
    }
    // pub fn match_against(&self, statements: &[Statement]) -> Result<HashMap<usize, Value>> {
    //     let mut bindings = HashMap::new();
    //     // Single out custom predicate, replacing batch-self
    //     // references with custom predicate references.
    //     let custom_predicate = {
    //         let cp = &self.batch.predicates[self.index];
    //         CustomPredicate {
    //             conjunction: cp.conjunction,
    //             statements: cp
    //                 .statements
    //                 .iter()
    //                 .map(|StatementTmpl(p, args)| {
    //                     StatementTmpl(
    //                         match p {
    //                             Predicate::BatchSelf(i) => Predicate::Custom(
    //                                 CustomPredicateRef::new(self.batch.clone(), *i),
    //                             ),
    //                             _ => p.clone(),
    //                         },
    //                         args.to_vec(),
    //                     )
    //                 })
    //                 .collect(),
    //             args_len: cp.args_len,
    //         }
    //     };
    //     match custom_predicate.conjunction {
    //                 true if custom_predicate.statements.len() == statements.len() => {
    //                     // Match op args against statement templates
    //                 let match_bindings = iter::zip(custom_predicate.statements, statements).map(
    //                     |(s_tmpl, s)| s_tmpl.match_against(s)
    //                 ).collect::<Result<Vec<_>>>()
    //                     .map(|v| v.concat())?;
    //                 // Add bindings to binding table, throwing if there is an inconsistency.
    //                 match_bindings.into_iter().try_for_each(|kv| hashmap_insert_no_dupe(&mut bindings, kv))?;
    //                 Ok(bindings)
    //                 },
    //                 false if statements.len() == 1 => {
    //                     // Match op arg against each statement template
    //                     custom_predicate.statements.iter().map(
    //                         |s_tmpl| {
    //                             let mut bindings = bindings.clone();
    //                             s_tmpl.match_against(&statements[0])?.into_iter().try_for_each(|kv| hashmap_insert_no_dupe(&mut bindings, kv))?;
    //                             Ok::<_, anyhow::Error>(bindings)
    //                         }
    //                     ).find(|m| m.is_ok()).unwrap_or(Err(anyhow!("Statement {} does not match disjunctive custom predicate {}.", &statements[0], custom_predicate)))
    //                 },
    //                 _ =>                     Err(anyhow!("Custom predicate statement template list {:?} does not match op argument list {:?}.", custom_predicate.statements, statements))
    //             }
    // }
}

#[derive(Clone, Debug, PartialEq)]
// #[serde(tag = "type", content = "value")]
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

impl ToFields for Predicate {
    fn to_fields(&self, params: &Params) -> Vec<F> {
        // serialize:
        // NativePredicate(id) as (0, id, 0, 0, 0, 0) -- id: usize
        // BatchSelf(i) as (1, i, 0, 0, 0, 0) -- i: usize
        // CustomPredicateRef(pb, i) as
        // (2, [hash of pb], i) -- pb hashes to 4 field elements
        //                      -- i: usize

        // in every case: pad to (hash_size + 2) field elements
        let mut fields: Vec<F> = match self {
            Self::Native(p) => iter::once(F::from_canonical_u64(1))
                .chain(p.to_fields(params))
                .collect(),
            Self::BatchSelf(i) => iter::once(F::from_canonical_u64(2))
                .chain(iter::once(F::from_canonical_usize(*i)))
                .collect(),
            Self::Custom(CustomPredicateRef { batch, index }) => {
                iter::once(F::from_canonical_u64(3))
                    .chain(batch.hash(params).0)
                    .chain(iter::once(F::from_canonical_usize(*index)))
                    .collect()
            }
        };
        fields.resize_with(Params::predicate_size(), || F::from_canonical_u64(0));
        fields
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

/* TODO: Uncomment
#[cfg(test)]
mod tests {
    use std::{array, sync::Arc};

    use anyhow::Result;
    use plonky2::field::goldilocks_field::GoldilocksField;

    use crate::middleware::{
        AnchoredKey, CustomPredicate, CustomPredicateBatch, CustomPredicateRef, Hash,
        KeyOrWildcard, NativePredicate, Operation, Params, PodId, PodType, Predicate, Statement,
        StatementTmpl, StatementTmplArg, SELF,
    };

    fn st(p: Predicate, args: Vec<StatementTmplArg>) -> StatementTmpl {
        StatementTmpl(p, args)
    }

    type STA = StatementTmplArg;
    type HOW = KeyOrWildcard;
    type P = Predicate;
    type NP = NativePredicate;

    #[test]
    fn is_double_test() -> Result<()> {
        let params = Params::default();

        /*
        is_double(S1, S2) :-
        p:value_of(Constant, 2),
        p:product_of(S1, Constant, S2)
         */
        let cust_pred_batch = Arc::new(CustomPredicateBatch {
            name: "is_double".to_string(),
            predicates: vec![CustomPredicate::and(
                &params,
                vec![
                    st(
                        P::Native(NP::ValueOf),
                        vec![
                            STA::Key(HOW::Wildcard(4), HOW::Wildcard(5)),
                            STA::Literal(2.into()),
                        ],
                    ),
                    st(
                        P::Native(NP::ProductOf),
                        vec![
                            STA::Key(HOW::Wildcard(0), HOW::Wildcard(1)),
                            STA::Key(HOW::Wildcard(4), HOW::Wildcard(5)),
                            STA::Key(HOW::Wildcard(2), HOW::Wildcard(3)),
                        ],
                    ),
                ],
                4,
            )?],
        });

        let custom_statement = Statement::Custom(
            CustomPredicateRef(cust_pred_batch.clone(), 0),
            vec![
                AnchoredKey::new(SELF, "Some value"),
                AnchoredKey::new(SELF, "Some other value"),
            ],
        );

        let custom_deduction = Operation::Custom(
            CustomPredicateRef(cust_pred_batch, 0),
            vec![
                Statement::ValueOf(AnchoredKey::new(SELF, "Some constant"), 2.into()),
                Statement::ProductOf(
                    AnchoredKey::new(SELF, "Some value"),
                    AnchoredKey::new(SELF, "Some constant"),
                    AnchoredKey::new(SELF, "Some other value"),
                ),
            ],
        );

        assert!(custom_deduction.check(&params, &custom_statement)?);

        Ok(())
    }

    #[test]
    fn ethdos_test() -> Result<()> {
        let params = Params::default();

        let eth_friend_cp = CustomPredicate::and(
            &params,
            vec![
                st(
                    P::Native(NP::ValueOf),
                    vec![
                        STA::Key(HOW::Wildcard(4), KeyOrWildcard::Hash("type".into())),
                        STA::Literal(PodType::Signed.into()),
                    ],
                ),
                st(
                    P::Native(NP::Equal),
                    vec![
                        STA::Key(HOW::Wildcard(4), KeyOrWildcard::Hash("signer".into())),
                        STA::Key(HOW::Wildcard(0), HOW::Wildcard(1)),
                    ],
                ),
                st(
                    P::Native(NP::Equal),
                    vec![
                        STA::Key(HOW::Wildcard(4), KeyOrWildcard::Hash("attestation".into())),
                        STA::Key(HOW::Wildcard(2), HOW::Wildcard(3)),
                    ],
                ),
            ],
            4,
        )?;

        let eth_friend_batch = Arc::new(CustomPredicateBatch {
            name: "eth_friend".to_string(),
            predicates: vec![eth_friend_cp],
        });

        let eth_dos_base = CustomPredicate::and(
            &params,
            vec![
                st(
                    P::Native(NP::Equal),
                    vec![
                        STA::Key(HOW::Wildcard(0), HOW::Wildcard(1)),
                        STA::Key(HOW::Wildcard(2), HOW::Wildcard(3)),
                    ],
                ),
                st(
                    P::Native(NP::ValueOf),
                    vec![
                        STA::Key(HOW::Wildcard(4), HOW::Wildcard(5)),
                        STA::Literal(0.into()),
                    ],
                ),
            ],
            6,
        )?;

        let eth_dos_ind = CustomPredicate::and(
            &params,
            vec![
                st(
                    P::BatchSelf(2),
                    vec![
                        STA::Key(HOW::Wildcard(0), HOW::Wildcard(1)),
                        STA::Key(HOW::Wildcard(10), HOW::Wildcard(11)),
                        STA::Key(HOW::Wildcard(8), HOW::Wildcard(9)),
                    ],
                ),
                st(
                    P::Native(NP::ValueOf),
                    vec![
                        STA::Key(HOW::Wildcard(6), HOW::Wildcard(7)),
                        STA::Literal(1.into()),
                    ],
                ),
                st(
                    P::Native(NP::SumOf),
                    vec![
                        STA::Key(HOW::Wildcard(4), HOW::Wildcard(5)),
                        STA::Key(HOW::Wildcard(8), HOW::Wildcard(9)),
                        STA::Key(HOW::Wildcard(6), HOW::Wildcard(7)),
                    ],
                ),
                st(
                    P::Custom(CustomPredicateRef(eth_friend_batch.clone(), 0)),
                    vec![
                        STA::Key(HOW::Wildcard(10), HOW::Wildcard(11)),
                        STA::Key(HOW::Wildcard(2), HOW::Wildcard(3)),
                    ],
                ),
            ],
            6,
        )?;

        let eth_dos_distance_either = CustomPredicate::or(
            &params,
            vec![
                st(
                    P::BatchSelf(0),
                    vec![
                        STA::Key(HOW::Wildcard(0), HOW::Wildcard(1)),
                        STA::Key(HOW::Wildcard(2), HOW::Wildcard(3)),
                        STA::Key(HOW::Wildcard(4), HOW::Wildcard(5)),
                    ],
                ),
                st(
                    P::BatchSelf(1),
                    vec![
                        STA::Key(HOW::Wildcard(0), HOW::Wildcard(1)),
                        STA::Key(HOW::Wildcard(2), HOW::Wildcard(3)),
                        STA::Key(HOW::Wildcard(4), HOW::Wildcard(5)),
                    ],
                ),
            ],
            6,
        )?;

        let eth_dos_distance_batch = Arc::new(CustomPredicateBatch {
            name: "ETHDoS_distance".to_string(),
            predicates: vec![eth_dos_base, eth_dos_ind, eth_dos_distance_either],
        });

        // Some POD IDs
        let pod_id1 = PodId(Hash(array::from_fn(|i| GoldilocksField(i as u64))));
        let pod_id2 = PodId(Hash(array::from_fn(|i| GoldilocksField((i * i) as u64))));
        let pod_id3 = PodId(Hash(array::from_fn(|i| GoldilocksField((2 * i) as u64))));
        let pod_id4 = PodId(Hash(array::from_fn(|i| GoldilocksField((2 * i) as u64))));

        // Example statement
        let ethdos_example = Statement::Custom(
            CustomPredicateRef(eth_dos_distance_batch.clone(), 2),
            vec![
                AnchoredKey::new(pod_id1, "Alice"),
                AnchoredKey::new(pod_id2, "Bob"),
                AnchoredKey::new(SELF, "Seven"),
            ],
        );

        // Copies should work.
        assert!(Operation::CopyStatement(ethdos_example.clone()).check(&params, &ethdos_example)?);

        // This could arise as the inductive step.
        let ethdos_ind_example = Statement::Custom(
            CustomPredicateRef(eth_dos_distance_batch.clone(), 1),
            vec![
                AnchoredKey::new(pod_id1, "Alice"),
                AnchoredKey::new(pod_id2, "Bob"),
                AnchoredKey::new(SELF, "Seven"),
            ],
        );

        assert!(Operation::Custom(
            CustomPredicateRef(eth_dos_distance_batch.clone(), 2),
            vec![ethdos_ind_example.clone()]
        )
        .check(&params, &ethdos_example)?);

        // And the inductive step would arise as follows: Say the
        // ETHDoS distance from Alice to Charlie is 6, which is one
        // less than 7, and Charlie is ETH-friends with Bob.
        let ethdos_facts = vec![
            Statement::Custom(
                CustomPredicateRef(eth_dos_distance_batch.clone(), 2),
                vec![
                    AnchoredKey::new(pod_id1, "Alice"),
                    AnchoredKey::new(pod_id3, "Charlie"),
                    AnchoredKey::new(pod_id4, "Six"),
                ],
            ),
            Statement::ValueOf(AnchoredKey::new(SELF, "One"), 1.into()),
            Statement::SumOf(
                AnchoredKey::new(SELF, "Seven"),
                AnchoredKey::new(pod_id4, "Six"),
                AnchoredKey::new(SELF, "One"),
            ),
            Statement::Custom(
                CustomPredicateRef(eth_friend_batch.clone(), 0),
                vec![
                    AnchoredKey::new(pod_id3, "Charlie"),
                    AnchoredKey::new(pod_id2, "Bob"),
                ],
            ),
        ];

        assert!(Operation::Custom(
            CustomPredicateRef(eth_dos_distance_batch.clone(), 1),
            ethdos_facts
        )
        .check(&params, &ethdos_ind_example)?);

        Ok(())
    }
}
*/
