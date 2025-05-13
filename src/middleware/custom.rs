use std::{fmt, iter, sync::Arc};

use plonky2::field::types::Field;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::middleware::{
    hash_fields, Error, Hash, Key, NativePredicate, Params, Predicate, Result, ToFields, Value,
    EMPTY_HASH, F, HASH_SIZE, VALUE_SIZE,
};

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, JsonSchema)]
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

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
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
    // Encoding:
    // - Key(k) => [[k]]
    // - Wildcard(index) => [[index], 0, 0, 0]
    fn to_fields(&self, params: &Params) -> Vec<F> {
        match self {
            KeyOrWildcard::Key(k) => k.hash().to_fields(params),
            KeyOrWildcard::Wildcard(wc) => iter::once(F::from_canonical_u64(wc.index as u64))
                .chain(iter::repeat(F::ZERO))
                .take(HASH_SIZE)
                .collect(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
pub enum StatementTmplArg {
    None,
    Literal(Value),
    // AnchoredKey
    AnchoredKey(Wildcard, KeyOrWildcard),
    // TODO: This naming is a bit confusing: a WildcardLiteral that contains a Wildcard...
    // Could we merge WildcardValue and Value and allow wildcard value apart from pod_id and key?
    WildcardLiteral(Wildcard),
}

#[derive(Clone, Copy)]
pub enum StatementTmplArgPrefix {
    None = 0,
    Literal = 1,
    AnchoredKey = 2,
    WildcardLiteral = 3,
}

impl From<StatementTmplArgPrefix> for F {
    fn from(prefix: StatementTmplArgPrefix) -> Self {
        Self::from_canonical_usize(prefix as usize)
    }
}

impl ToFields for StatementTmplArg {
    fn to_fields(&self, params: &Params) -> Vec<F> {
        // Encoding:
        // None =>                      (0,          0, 0, 0, 0,  0, 0, 0, 0)
        // Literal(v) =>                (1,        [v         ],  0, 0, 0, 0)
        // Key(wc_index, key_or_wc) =>  (2, [wc_index], 0, 0, 0, [key_or_wc])
        // WildcardLiteral(wc_index) => (3, [wc_index], 0, 0, 0,  0, 0, 0, 0)
        // In all three cases, we pad to 2 * hash_size + 1 = 9 field elements
        match self {
            StatementTmplArg::None => {
                let fields: Vec<F> = iter::once(F::from(StatementTmplArgPrefix::None))
                    .chain(iter::repeat(F::ZERO))
                    .take(Params::statement_tmpl_arg_size())
                    .collect();
                fields
            }
            StatementTmplArg::Literal(v) => {
                let fields: Vec<F> = iter::once(F::from(StatementTmplArgPrefix::Literal))
                    .chain(v.raw().to_fields(params))
                    .chain(iter::repeat(F::ZERO))
                    .take(Params::statement_tmpl_arg_size())
                    .collect();
                fields
            }
            StatementTmplArg::AnchoredKey(wc1, kw2) => {
                let fields: Vec<F> = iter::once(F::from(StatementTmplArgPrefix::AnchoredKey))
                    .chain(wc1.to_fields(params))
                    .chain(iter::repeat(F::ZERO).take(VALUE_SIZE - 1))
                    .chain(kw2.to_fields(params))
                    .collect();
                fields
            }
            StatementTmplArg::WildcardLiteral(wc) => {
                let fields: Vec<F> = iter::once(F::from(StatementTmplArgPrefix::WildcardLiteral))
                    .chain(wc.to_fields(params))
                    .chain(iter::repeat(F::ZERO))
                    .take(Params::statement_tmpl_arg_size())
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
            Self::AnchoredKey(pod_id, key) => write!(f, "({}, {})", pod_id, key),
            Self::WildcardLiteral(v) => write!(f, "{}", v),
        }
    }
}

/// Statement Template for a Custom Predicate
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, JsonSchema)]
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
            panic!(
                "Statement template has too many arguments {} > {}",
                self.args.len(),
                params.max_statement_args
            );
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

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
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
    pub fn empty() -> Self {
        Self {
            name: "empty".to_string(),
            conjunction: false,
            statements: vec![StatementTmpl {
                pred: Predicate::Native(NativePredicate::None),
                args: vec![],
            }],
            args_len: 0,
        }
    }
    pub fn and(
        params: &Params,
        name: String,
        statements: Vec<StatementTmpl>,
        args_len: usize,
    ) -> Result<Self> {
        Self::new(params, name, true, statements, args_len)
    }
    pub fn or(
        params: &Params,
        name: String,
        statements: Vec<StatementTmpl>,
        args_len: usize,
    ) -> Result<Self> {
        Self::new(params, name, false, statements, args_len)
    }
    pub fn new(
        params: &Params,
        name: String,
        conjunction: bool,
        statements: Vec<StatementTmpl>,
        args_len: usize,
    ) -> Result<Self> {
        if statements.len() > params.max_custom_predicate_arity {
            return Err(Error::max_length(
                "statements.len".to_string(),
                statements.len(),
                params.max_custom_predicate_arity,
            ));
        }
        if args_len > params.max_statement_args {
            return Err(Error::max_length(
                "statement_args.len".to_string(),
                args_len,
                params.max_statement_args,
            ));
        }

        Ok(Self {
            name,
            conjunction,
            statements,
            args_len,
        })
    }
    pub fn pad_statement_tmpl(&self) -> StatementTmpl {
        StatementTmpl {
            pred: Predicate::Native(if self.conjunction {
                NativePredicate::None
            } else {
                NativePredicate::False
            }),
            args: vec![],
        }
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

        let pad_st = self.pad_statement_tmpl();
        let fields: Vec<F> = iter::once(F::from_bool(self.conjunction))
            .chain(iter::once(F::from_canonical_usize(self.args_len)))
            .chain(
                self.statements
                    .iter()
                    .chain(iter::repeat(&pad_st))
                    .take(params.max_custom_predicate_arity)
                    .flat_map(|st| st.to_fields(params)),
            )
            .collect();
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

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, JsonSchema)]
pub struct CustomPredicateBatch {
    id: Hash,
    pub name: String,
    predicates: Vec<CustomPredicate>,
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

        let pad_pred = CustomPredicate::empty();
        let fields: Vec<F> = self
            .predicates
            .iter()
            .chain(iter::repeat(&pad_pred))
            .take(params.max_custom_batch_size)
            .flat_map(|p| p.to_fields(params))
            .collect();
        fields
    }
}

impl CustomPredicateBatch {
    pub fn new(params: &Params, name: String, predicates: Vec<CustomPredicate>) -> Arc<Self> {
        let mut cpb = Self {
            id: EMPTY_HASH,
            name,
            predicates,
        };
        let id = cpb.calculate_id(params);
        cpb.id = id;
        Arc::new(cpb)
    }

    /// Cryptographic identifier for the batch.
    fn calculate_id(&self, params: &Params) -> Hash {
        // NOTE: This implementation just hashes the concatenation of all the custom predicates,
        // but ideally we want to use the root of a merkle tree built from the custom predicates.
        let input = self.to_fields(params);

        hash_fields(&input)
    }

    pub fn id(&self) -> Hash {
        self.id
    }
    pub fn predicates(&self) -> &[CustomPredicate] {
        &self.predicates
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, JsonSchema)]
pub struct CustomPredicateRef {
    pub batch: Arc<CustomPredicateBatch>,
    pub index: usize,
}

impl CustomPredicateRef {
    pub fn new(batch: Arc<CustomPredicateBatch>, index: usize) -> Self {
        Self { batch, index }
    }
    pub fn arg_len(&self) -> usize {
        self.predicate().args_len
    }
    pub fn predicate(&self) -> &CustomPredicate {
        &self.batch.predicates[self.index]
    }
}

#[cfg(test)]
mod tests {
    use std::array;

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
        let cust_pred_batch = CustomPredicateBatch::new(
            &params,
            "is_double".to_string(),
            vec![CustomPredicate::and(
                &params,
                "_".into(),
                vec![
                    st(
                        P::Native(NP::ValueOf),
                        vec![STA::AnchoredKey(wc(4), kow_wc(5)), STA::Literal(2.into())],
                    ),
                    st(
                        P::Native(NP::ProductOf),
                        vec![
                            STA::AnchoredKey(wc(0), kow_wc(1)),
                            STA::AnchoredKey(wc(4), kow_wc(5)),
                            STA::AnchoredKey(wc(2), kow_wc(3)),
                        ],
                    ),
                ],
                2,
            )?],
        );

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
            max_statement_args: 6,
            ..Default::default()
        };

        let eth_friend_cp = CustomPredicate::and(
            &params,
            "eth_friend_cp".into(),
            vec![
                st(
                    P::Native(NP::ValueOf),
                    vec![
                        STA::AnchoredKey(wc(4), KeyOrWildcard::Key("type".into())),
                        STA::Literal(PodType::Signed.into()),
                    ],
                ),
                st(
                    P::Native(NP::Equal),
                    vec![
                        STA::AnchoredKey(wc(4), KeyOrWildcard::Key("signer".into())),
                        STA::AnchoredKey(wc(0), kow_wc(1)),
                    ],
                ),
                st(
                    P::Native(NP::Equal),
                    vec![
                        STA::AnchoredKey(wc(4), KeyOrWildcard::Key("attestation".into())),
                        STA::AnchoredKey(wc(2), kow_wc(3)),
                    ],
                ),
            ],
            4,
        )?;

        let eth_friend_batch =
            CustomPredicateBatch::new(&params, "eth_friend".to_string(), vec![eth_friend_cp]);

        // 0
        let eth_dos_base = CustomPredicate::and(
            &params,
            "eth_dos_base".into(),
            vec![
                st(
                    P::Native(NP::Equal),
                    vec![
                        STA::AnchoredKey(wc(0), kow_wc(1)),
                        STA::AnchoredKey(wc(2), kow_wc(3)),
                    ],
                ),
                st(
                    P::Native(NP::ValueOf),
                    vec![STA::AnchoredKey(wc(4), kow_wc(5)), STA::Literal(0.into())],
                ),
            ],
            6,
        )?;

        // 1
        let eth_dos_ind = CustomPredicate::and(
            &params,
            "eth_dos_ind".into(),
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
                    vec![STA::AnchoredKey(wc(6), kow_wc(7)), STA::Literal(1.into())],
                ),
                st(
                    P::Native(NP::SumOf),
                    vec![
                        STA::AnchoredKey(wc(4), kow_wc(5)),
                        STA::AnchoredKey(wc(8), kow_wc(9)),
                        STA::AnchoredKey(wc(6), kow_wc(7)),
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
            &params,
            "eth_dos_distance_either".into(),
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

        let eth_dos_distance_batch = CustomPredicateBatch::new(
            &params,
            "ETHDoS_distance".to_string(),
            vec![eth_dos_base, eth_dos_ind, eth_dos_distance_either],
        );

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
