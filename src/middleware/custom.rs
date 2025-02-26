use std::sync::Arc;
use std::{fmt, hash as h, iter::zip};

use anyhow::{anyhow, Result};
use plonky2::field::types::Field;

use super::{
    hash_fields, AnchoredKey, Hash, NativePredicate, Params, PodId, Statement, StatementArg,
    ToFields, Value, F,
};

// BEGIN Custom 1b

#[derive(Clone, Debug, PartialEq, Eq, h::Hash)]
pub enum HashOrWildcard {
    Hash(Hash),
    Wildcard(usize),
}

impl HashOrWildcard {
    /// Matches a hash or wildcard against a value, returning a pair
    /// representing a wildcard binding (if any) or an error if no
    /// match is possible.
    pub fn match_against(&self, v: &Value) -> Result<Option<(usize, Value)>> {
        match self {
            HashOrWildcard::Hash(h) if &Value::from(h.clone()) == v => Ok(None),
            HashOrWildcard::Wildcard(i) => Ok(Some((*i, v.clone()))),
            _ => Err(anyhow!("Failed to match {} against {}.", self, v)),
        }
    }
}

impl fmt::Display for HashOrWildcard {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Hash(h) => write!(f, "{}", h),
            Self::Wildcard(n) => write!(f, "*{}", n),
        }
    }
}

impl ToFields for HashOrWildcard {
    fn to_fields(&self, _params: &Params) -> (Vec<F>, usize) {
        match self {
            HashOrWildcard::Hash(h) => h.to_fields(_params),
            HashOrWildcard::Wildcard(w) => {
                let usizes: Vec<usize> = vec![0, 0, 0, *w];
                let fields: Vec<F> = usizes
                    .iter()
                    .map(|x| F::from_canonical_u64(*x as u64))
                    .collect();
                (fields, 4)
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, h::Hash)]
pub enum StatementTmplArg {
    None,
    Literal(Value),
    Key(HashOrWildcard, HashOrWildcard),
}

impl StatementTmplArg {
    /// Matches a statement template argument against a statement
    /// argument, returning a wildcard correspondence in the case of
    /// one or more wildcard matches, nothing in the case of a
    /// literal/hash match, and an error otherwise.
    pub fn match_against(&self, s_arg: &StatementArg) -> Result<Vec<(usize, Value)>> {
        match (self, s_arg) {
            (Self::None, StatementArg::None) => Ok(vec![]),
            (Self::Literal(v), StatementArg::Literal(w)) if v == w => Ok(vec![]),
            (Self::Key(tmpl_o, tmpl_k), StatementArg::Key(AnchoredKey(PodId(o), k))) => {
                let o_corr = tmpl_o.match_against(&o.clone().into())?;
                let k_corr = tmpl_k.match_against(&k.clone().into())?;
                Ok([o_corr, k_corr].into_iter().flat_map(|x| x).collect())
            }
            _ => Err(anyhow!("Failed to match {} against {}.", self, s_arg)),
        }
    }
}

impl ToFields for StatementTmplArg {
    fn to_fields(&self, _params: &Params) -> (Vec<F>, usize) {
        // None => (0, ...)
        // Literal(value) => (1, [value], 0, 0, 0, 0)
        // Key(hash_or_wildcard1, hash_or_wildcard2)
        //    => (2, [hash_or_wildcard1], [hash_or_wildcard2])
        // In all three cases, we pad to 2 * hash_size + 1 = 9 field elements
        let hash_size = 4;
        let statement_tmpl_arg_size = 2 * hash_size + 1;
        match self {
            StatementTmplArg::None => {
                let fields: Vec<F> = std::iter::repeat_with(|| F::from_canonical_u64(0))
                    .take(statement_tmpl_arg_size)
                    .collect();
                (fields, statement_tmpl_arg_size)
            }
            StatementTmplArg::Literal(v) => {
                let fields: Vec<F> = std::iter::once(F::from_canonical_u64(1))
                    .chain(v.to_fields(_params).0.into_iter())
                    .chain(std::iter::repeat_with(|| F::from_canonical_u64(0)).take(hash_size))
                    .collect();
                (fields, statement_tmpl_arg_size)
            }
            StatementTmplArg::Key(hw1, hw2) => {
                let fields: Vec<F> = std::iter::once(F::from_canonical_u64(2))
                    .chain(hw1.to_fields(_params).0.into_iter())
                    .chain(hw2.to_fields(_params).0.into_iter())
                    .collect();
                (fields, statement_tmpl_arg_size)
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

// END

// BEGIN Custom 2

// pub enum StatementTmplArg {
//     None,
//     Literal(Value),
//     Wildcard(usize),
// }

// END

/// Statement Template for a Custom Predicate
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatementTmpl(pub Predicate, pub Vec<StatementTmplArg>);

impl StatementTmpl {
    pub fn pred(&self) -> &Predicate {
        &self.0
    }
    pub fn args(&self) -> &[StatementTmplArg] {
        &self.1
    }
    /// Matches a statement template against a statement, returning
    /// the variable bindings as an association list. Returns an error
    /// if there is type or argument mismatch.
    pub fn match_against(&self, s: &Statement) -> Result<Vec<(usize, Value)>> {
        type P = Predicate;
        if matches!(self, Self(P::BatchSelf(_), _)) {
            Err(anyhow!(
                "Cannot check self-referencing statement templates."
            ))
        } else if self.pred() != &s.code() {
            Err(anyhow!("Type mismatch between {:?} and {}.", self, s))
        } else {
            zip(self.args(), s.args())
                .map(|(t_arg, s_arg)| t_arg.match_against(&s_arg))
                .collect::<Result<Vec<_>>>()
                .map(|v| v.concat())
        }
    }
}

impl ToFields for StatementTmpl {
    fn to_fields(&self, params: &Params) -> (Vec<F>, usize) {
        // serialize as:
        // predicate (6 field elements)
        // then the StatementTmplArgs

        // TODO think if this check should go into the StatementTmpl creation,
        // instead of at the `to_fields` method, where we should assume that the
        // values are already valid
        if self.1.len() > params.max_statement_args {
            panic!("Statement template has too many arguments");
        }

        let mut fields: Vec<F> = self
            .0
            .to_fields(params)
            .0
            .into_iter()
            .chain(self.1.iter().flat_map(|sta| sta.to_fields(params).0))
            .collect();
        fields.resize_with(params.statement_tmpl_size(), || F::from_canonical_u64(0));
        (fields, params.statement_tmpl_size())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CustomPredicate {
    /// true for "and", false for "or"
    pub conjunction: bool,
    pub statements: Vec<StatementTmpl>,
    pub args_len: usize,
    // TODO: Add private args length?
    // TODO: Add args type information?
}

impl ToFields for CustomPredicate {
    fn to_fields(&self, params: &Params) -> (Vec<F>, usize) {
        // serialize as:
        // conjunction (one field element)
        // args_len (one field element)
        // statements
        //   (params.max_custom_predicate_arity * params.statement_tmpl_size())
        //   field elements

        // TODO think if this check should go into the StatementTmpl creation,
        // instead of at the `to_fields` method, where we should assume that the
        // values are already valid
        if self.statements.len() > params.max_custom_predicate_arity {
            panic!("Custom predicate depends on too many statements");
        }

        let mut fields: Vec<F> = std::iter::once(F::from_bool(self.conjunction))
            .chain(std::iter::once(F::from_canonical_usize(self.args_len)))
            .chain(self.statements.iter().flat_map(|st| st.to_fields(params).0))
            .collect();
        fields.resize_with(params.custom_predicate_size(), || F::from_canonical_u64(0));
        (fields, params.custom_predicate_size())
    }
}

impl fmt::Display for CustomPredicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "{}<", if self.conjunction { "and" } else { "or" })?;
        for st in &self.statements {
            write!(f, "  {}", st.0)?;
            for (i, arg) in st.1.iter().enumerate() {
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CustomPredicateBatch {
    pub name: String,
    pub predicates: Vec<CustomPredicate>,
}

impl ToFields for CustomPredicateBatch {
    fn to_fields(&self, params: &Params) -> (Vec<F>, usize) {
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
            .flat_map(|p| p.to_fields(params).0)
            .collect();
        fields.resize_with(params.custom_predicate_batch_size_field_elts(), || {
            F::from_canonical_u64(0)
        });

        (fields, params.custom_predicate_batch_size_field_elts())
    }
}

impl CustomPredicateBatch {
    pub fn hash(&self, _params: &Params) -> Hash {
        let input = self.to_fields(_params).0;
        let h = hash_fields(&input);
        h
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CustomPredicateRef(pub Arc<CustomPredicateBatch>, pub usize);

#[derive(Clone, Debug, PartialEq, Eq)]
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
    fn to_fields(&self, _params: &Params) -> (Vec<F>, usize) {
        // serialize:
        // NativePredicate(id) as (0, id, 0, 0, 0, 0) -- id: usize
        // BatchSelf(i) as (1, i, 0, 0, 0, 0) -- i: usize
        // CustomPredicateRef(pb, i) as
        // (2, [hash of pb], i) -- pb hashes to 4 field elements
        //                      -- i: usize

        // in every case: pad to (hash_size + 2) field elements
        let mut fields: Vec<F> = match self {
            Self::Native(p) => std::iter::once(F::from_canonical_u64(1))
                .chain(p.to_fields(_params).0.into_iter())
                .collect(),
            Self::BatchSelf(i) => std::iter::once(F::from_canonical_u64(2))
                .chain(std::iter::once(F::from_canonical_usize(*i)))
                .collect(),
            Self::Custom(CustomPredicateRef(pb, i)) => std::iter::once(F::from_canonical_u64(3))
                .chain(pb.hash(_params).0)
                .chain(std::iter::once(F::from_canonical_usize(*i)))
                .collect(),
        };
        fields.resize_with(Params::predicate_size(), || F::from_canonical_u64(0));
        (fields, Params::predicate_size())
    }
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Native(p) => write!(f, "{:?}", p),
            Self::BatchSelf(i) => write!(f, "self.{}", i),
            Self::Custom(CustomPredicateRef(pb, i)) => write!(f, "{}.{}", pb.name, i),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{array, sync::Arc};

    use anyhow::Result;
    use plonky2::field::goldilocks_field::GoldilocksField;

    use crate::middleware::{
        AnchoredKey, CustomPredicate, CustomPredicateBatch, CustomPredicateRef, Hash,
        HashOrWildcard, NativePredicate, Operation, PodId, PodType, Predicate, Statement,
        StatementTmpl, StatementTmplArg, SELF,
    };

    fn st(p: Predicate, args: Vec<StatementTmplArg>) -> StatementTmpl {
        StatementTmpl(p, args)
    }

    type STA = StatementTmplArg;
    type HOW = HashOrWildcard;
    type P = Predicate;
    type NP = NativePredicate;

    #[test]
    fn is_double_test() -> Result<()> {
        /*
        is_double(S1, S2) :-
        p:value_of(Constant, 2),
        p:product_of(S1, Constant, S2)
         */
        let cust_pred_batch = Arc::new(CustomPredicateBatch {
            name: "is_double".to_string(),
            predicates: vec![CustomPredicate {
                conjunction: true,
                statements: vec![
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
                args_len: 4,
            }],
        });

        let custom_statement = Statement::Custom(
            CustomPredicateRef(cust_pred_batch.clone(), 0),
            vec![
                AnchoredKey(SELF, "Some value".into()),
                AnchoredKey(SELF, "Some other value".into()),
            ],
        );

        let custom_deduction = Operation::Custom(
            CustomPredicateRef(cust_pred_batch, 0),
            vec![
                Statement::ValueOf(AnchoredKey(SELF, "Some constant".into()), 2.into()),
                Statement::ProductOf(
                    AnchoredKey(SELF, "Some value".into()),
                    AnchoredKey(SELF, "Some constant".into()),
                    AnchoredKey(SELF, "Some other value".into()),
                ),
            ],
        );

        assert!(custom_deduction.check(&custom_statement)?);

        Ok(())
    }

    #[test]
    fn ethdos_test() -> Result<()> {
        let eth_friend_cp = CustomPredicate {
            conjunction: true,
            statements: vec![
                st(
                    P::Native(NP::ValueOf),
                    vec![
                        STA::Key(HOW::Wildcard(4), HashOrWildcard::Hash("type".into())),
                        STA::Literal(PodType::Signed.into()),
                    ],
                ),
                st(
                    P::Native(NP::Equal),
                    vec![
                        STA::Key(HOW::Wildcard(4), HashOrWildcard::Hash("signer".into())),
                        STA::Key(HOW::Wildcard(0), HOW::Wildcard(1)),
                    ],
                ),
                st(
                    P::Native(NP::Equal),
                    vec![
                        STA::Key(HOW::Wildcard(4), HashOrWildcard::Hash("attestation".into())),
                        STA::Key(HOW::Wildcard(2), HOW::Wildcard(3)),
                    ],
                ),
            ],
            args_len: 4,
        };

        let eth_friend_batch = Arc::new(CustomPredicateBatch {
            name: "eth_friend".to_string(),
            predicates: vec![eth_friend_cp],
        });

        let eth_dos_base = CustomPredicate {
            conjunction: true,
            statements: vec![
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
            args_len: 6,
        };

        let eth_dos_ind = CustomPredicate {
            conjunction: true,
            statements: vec![
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
            args_len: 6,
        };

        let eth_dos_distance_either = CustomPredicate {
            conjunction: false,
            statements: vec![
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
            args_len: 6,
        };

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
                AnchoredKey(pod_id1, "Alice".into()),
                AnchoredKey(pod_id2, "Bob".into()),
                AnchoredKey(SELF, "Seven".into()),
            ],
        );

        // Copies should work.
        assert!(Operation::CopyStatement(ethdos_example.clone()).check(&ethdos_example)?);

        // This could arise as the inductive step.
        let ethdos_ind_example = Statement::Custom(
            CustomPredicateRef(eth_dos_distance_batch.clone(), 1),
            vec![
                AnchoredKey(pod_id1, "Alice".into()),
                AnchoredKey(pod_id2, "Bob".into()),
                AnchoredKey(SELF, "Seven".into()),
            ],
        );

        assert!(Operation::Custom(
            CustomPredicateRef(eth_dos_distance_batch.clone(), 2),
            vec![ethdos_ind_example.clone()]
        )
        .check(&ethdos_example)?);

        // And the inductive step would arise as follows: Say the
        // ETHDoS distance from Alice to Charlie is 6, which is one
        // less than 7, and Charlie is ETH-friends with Bob.
        let ethdos_facts = vec![
            Statement::Custom(
                CustomPredicateRef(eth_dos_distance_batch.clone(), 2),
                vec![
                    AnchoredKey(pod_id1, "Alice".into()),
                    AnchoredKey(pod_id3, "Charlie".into()),
                    AnchoredKey(pod_id4, "Six".into()),
                ],
            ),
            Statement::ValueOf(AnchoredKey(SELF, "One".into()), 1.into()),
            Statement::SumOf(
                AnchoredKey(SELF, "Seven".into()),
                AnchoredKey(pod_id4, "Six".into()),
                AnchoredKey(SELF, "One".into()),
            ),
            Statement::Custom(
                CustomPredicateRef(eth_friend_batch.clone(), 0),
                vec![
                    AnchoredKey(pod_id3, "Charlie".into()),
                    AnchoredKey(pod_id2, "Bob".into()),
                ],
            ),
        ];

        assert!(Operation::Custom(
            CustomPredicateRef(eth_dos_distance_batch.clone(), 1),
            ethdos_facts
        )
        .check(&ethdos_ind_example)?);

        Ok(())
    }
}
