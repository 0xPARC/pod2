use std::{fmt, iter, sync::Arc};

use anyhow::{anyhow, Result};
use plonky2::field::types::Field;

// use schemars::JsonSchema;

// use serde::{Deserialize, Serialize};
use crate::{
    middleware::HASH_SIZE,
    middleware::{hash_fields, Hash, Key, NativePredicate, Params, ToFields, Value, F},
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
    // TODO: This naming is a bit confusing: a WildcardLiteral that contains a Wildcard...
    // Could we merge WildcardValue and Value and allow wildcard value apart from pod_id and key?
    WildcardLiteral(Wildcard),
}

impl ToFields for StatementTmplArg {
    fn to_fields(&self, params: &Params) -> Vec<F> {
        // None => (0, ...)
        // Literal(value) => (1, [value], 0, 0, 0, 0)
        // Key(wildcard1, key_or_wildcard2)
        //    => (2, [wildcard1], [key_or_wildcard2])
        // WildcardLiteral(wildcard) => (3, [wildcard], 0, 0, 0, 0)
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
            StatementTmplArg::Key(wc1, kw2) => {
                let fields: Vec<F> = iter::once(F::from_canonical_u64(2))
                    .chain(wc1.to_fields(params))
                    .chain(kw2.to_fields(params))
                    .collect();
                fields
            }
            StatementTmplArg::WildcardLiteral(wc) => {
                let fields: Vec<F> = iter::once(F::from_canonical_u64(3))
                    .chain(wc.to_fields(params))
                    .chain(iter::repeat_with(|| F::from_canonical_u64(0)).take(HASH_SIZE))
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
            Self::WildcardLiteral(v) => write!(f, "{}", v),
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
}

impl fmt::Display for StatementTmpl {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}(", self.pred)?;
        for (i, arg) in self.args.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", arg)?;
        }
        writeln!(f)
    }
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
            write!(f, "  {}(", st.pred)?;
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
                write!(
                    f,
                    "{}.{}[{}]",
                    batch.name, index, batch.predicates[*index].name
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{array, sync::Arc};

    use anyhow::Result;
    use plonky2::field::goldilocks_field::GoldilocksField;

    use super::*;
    use crate::middleware::{
        AnchoredKey, CustomPredicate, CustomPredicateBatch, CustomPredicateRef, Hash,
        KeyOrWildcard, NativePredicate, Operation, Params, PodId, PodType, Predicate, Statement,
        StatementTmpl, StatementTmplArg, WildcardValue, SELF,
    };

    fn st(p: Predicate, args: Vec<StatementTmplArg>) -> StatementTmpl {
        StatementTmpl { pred: p, args }
    }

    fn kow_wc(i: usize) -> KOW {
        KOW::Wildcard(wc(i))
    }
    fn wc(i: usize) -> Wildcard {
        Wildcard {
            name: format!("{}", i),
            index: i,
        }
    }

    type STA = StatementTmplArg;
    type KOW = KeyOrWildcard;
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
                "_".into(),
                &params,
                vec![
                    st(
                        P::Native(NP::ValueOf),
                        vec![STA::Key(wc(4), kow_wc(5)), STA::Literal(2.into())],
                    ),
                    st(
                        P::Native(NP::ProductOf),
                        vec![
                            STA::Key(wc(0), kow_wc(1)),
                            STA::Key(wc(4), kow_wc(5)),
                            STA::Key(wc(2), kow_wc(3)),
                        ],
                    ),
                ],
                2,
            )?],
        });

        let custom_statement = Statement::Custom(
            CustomPredicateRef::new(cust_pred_batch.clone(), 0),
            vec![
                WildcardValue::PodId(SELF),
                WildcardValue::Key(Key::from("Some value")),
            ],
        );

        let custom_deduction = Operation::Custom(
            CustomPredicateRef::new(cust_pred_batch, 0),
            vec![
                Statement::ValueOf(AnchoredKey::from((SELF, "Some constant")), 2.into()),
                Statement::ProductOf(
                    AnchoredKey::from((SELF, "Some value")),
                    AnchoredKey::from((SELF, "Some constant")),
                    AnchoredKey::from((SELF, "Some other value")),
                ),
            ],
        );

        assert!(custom_deduction.check(&params, &custom_statement)?);

        Ok(())
    }

    #[test]
    fn ethdos_test() -> Result<()> {
        let params = Params {
            max_custom_predicate_wildcards: 12,
            ..Default::default()
        };

        let eth_friend_cp = CustomPredicate::and(
            "eth_friend_cp".into(),
            &params,
            vec![
                st(
                    P::Native(NP::ValueOf),
                    vec![
                        STA::Key(wc(4), KeyOrWildcard::Key("type".into())),
                        STA::Literal(PodType::Signed.into()),
                    ],
                ),
                st(
                    P::Native(NP::Equal),
                    vec![
                        STA::Key(wc(4), KeyOrWildcard::Key("signer".into())),
                        STA::Key(wc(0), kow_wc(1)),
                    ],
                ),
                st(
                    P::Native(NP::Equal),
                    vec![
                        STA::Key(wc(4), KeyOrWildcard::Key("attestation".into())),
                        STA::Key(wc(2), kow_wc(3)),
                    ],
                ),
            ],
            4,
        )?;

        let eth_friend_batch = Arc::new(CustomPredicateBatch {
            name: "eth_friend".to_string(),
            predicates: vec![eth_friend_cp],
        });

        // 0
        let eth_dos_base = CustomPredicate::and(
            "eth_dos_base".into(),
            &params,
            vec![
                st(
                    P::Native(NP::Equal),
                    vec![STA::Key(wc(0), kow_wc(1)), STA::Key(wc(2), kow_wc(3))],
                ),
                st(
                    P::Native(NP::ValueOf),
                    vec![STA::Key(wc(4), kow_wc(5)), STA::Literal(0.into())],
                ),
            ],
            6,
        )?;

        // 1
        let eth_dos_ind = CustomPredicate::and(
            "eth_dos_ind".into(),
            &params,
            vec![
                st(
                    P::BatchSelf(2),
                    vec![
                        STA::WildcardLiteral(wc(0)),
                        STA::WildcardLiteral(wc(1)),
                        STA::WildcardLiteral(wc(10)),
                        STA::WildcardLiteral(wc(11)),
                        STA::WildcardLiteral(wc(8)),
                        STA::WildcardLiteral(wc(9)),
                    ],
                ),
                st(
                    P::Native(NP::ValueOf),
                    vec![STA::Key(wc(6), kow_wc(7)), STA::Literal(1.into())],
                ),
                st(
                    P::Native(NP::SumOf),
                    vec![
                        STA::Key(wc(4), kow_wc(5)),
                        STA::Key(wc(8), kow_wc(9)),
                        STA::Key(wc(6), kow_wc(7)),
                    ],
                ),
                st(
                    P::Custom(CustomPredicateRef::new(eth_friend_batch.clone(), 0)),
                    vec![
                        STA::WildcardLiteral(wc(10)),
                        STA::WildcardLiteral(wc(11)),
                        STA::WildcardLiteral(wc(2)),
                        STA::WildcardLiteral(wc(3)),
                    ],
                ),
            ],
            6,
        )?;

        // 2
        let eth_dos_distance_either = CustomPredicate::or(
            "eth_dos_distance_either".into(),
            &params,
            vec![
                st(
                    P::BatchSelf(0),
                    vec![
                        STA::WildcardLiteral(wc(0)),
                        STA::WildcardLiteral(wc(1)),
                        STA::WildcardLiteral(wc(2)),
                        STA::WildcardLiteral(wc(3)),
                        STA::WildcardLiteral(wc(4)),
                        STA::WildcardLiteral(wc(5)),
                    ],
                ),
                st(
                    P::BatchSelf(1),
                    vec![
                        STA::WildcardLiteral(wc(0)),
                        STA::WildcardLiteral(wc(1)),
                        STA::WildcardLiteral(wc(2)),
                        STA::WildcardLiteral(wc(3)),
                        STA::WildcardLiteral(wc(4)),
                        STA::WildcardLiteral(wc(5)),
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
            CustomPredicateRef::new(eth_dos_distance_batch.clone(), 2),
            vec![
                WildcardValue::PodId(pod_id1),
                WildcardValue::Key(Key::from("Alice")),
                WildcardValue::PodId(pod_id2),
                WildcardValue::Key(Key::from("Bob")),
                WildcardValue::PodId(SELF),
                WildcardValue::Key(Key::from("Seven")),
            ],
        );

        // Copies should work.
        assert!(Operation::CopyStatement(ethdos_example.clone()).check(&params, &ethdos_example)?);

        // This could arise as the inductive step.
        let ethdos_ind_example = Statement::Custom(
            CustomPredicateRef::new(eth_dos_distance_batch.clone(), 1),
            vec![
                WildcardValue::PodId(pod_id1),
                WildcardValue::Key(Key::from("Alice")),
                WildcardValue::PodId(pod_id2),
                WildcardValue::Key(Key::from("Bob")),
                WildcardValue::PodId(SELF),
                WildcardValue::Key(Key::from("Seven")),
            ],
        );

        assert!(Operation::Custom(
            CustomPredicateRef::new(eth_dos_distance_batch.clone(), 2),
            vec![Statement::None, ethdos_ind_example.clone()]
        )
        .check(&params, &ethdos_example)?);

        // And the inductive step would arise as follows: Say the
        // ETHDoS distance from Alice to Charlie is 6, which is one
        // less than 7, and Charlie is ETH-friends with Bob.
        let ethdos_facts = vec![
            Statement::Custom(
                CustomPredicateRef::new(eth_dos_distance_batch.clone(), 2),
                vec![
                    WildcardValue::PodId(pod_id1),
                    WildcardValue::Key(Key::from("Alice")),
                    WildcardValue::PodId(pod_id3),
                    WildcardValue::Key(Key::from("Charlie")),
                    WildcardValue::PodId(pod_id4),
                    WildcardValue::Key(Key::from("Six")),
                ],
            ),
            Statement::ValueOf(AnchoredKey::from((SELF, "One")), 1.into()),
            Statement::SumOf(
                AnchoredKey::from((SELF, "Seven")),
                AnchoredKey::from((pod_id4, "Six")),
                AnchoredKey::from((SELF, "One")),
            ),
            Statement::Custom(
                CustomPredicateRef::new(eth_friend_batch.clone(), 0),
                vec![
                    WildcardValue::PodId(pod_id3),
                    WildcardValue::Key(Key::from("Charlie")),
                    WildcardValue::PodId(pod_id2),
                    WildcardValue::Key(Key::from("Bob")),
                ],
            ),
        ];

        assert!(Operation::Custom(
            CustomPredicateRef::new(eth_dos_distance_batch.clone(), 1),
            ethdos_facts
        )
        .check(&params, &ethdos_ind_example)?);

        Ok(())
    }
}
