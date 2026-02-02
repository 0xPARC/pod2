use std::{collections::HashMap, fmt, iter, sync::Arc};

use itertools::Itertools;
use plonky2::field::types::Field;
use schemars::JsonSchema;
use serde::{Deserialize, Deserializer, Serialize};

use crate::{
    backends::plonky2::primitives::merkletree::MerkleTree,
    middleware::{
        hash_fields, Error, Hash, Key, NativePredicate, Params, Predicate, RawValue, Result,
        ToFields, Value, BASE_PARAMS, F, VALUE_SIZE,
    },
};

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
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
        if f.alternate() {
            write!(f, "{}:{}", self.index, self.name)
        } else {
            write!(f, "{}", self.name)
        }
    }
}

impl ToFields for Wildcard {
    fn to_fields(&self) -> Vec<F> {
        vec![F::from_canonical_u64(self.index as u64)]
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
pub enum StatementTmplArg {
    None,
    Literal(Value),
    // AnchoredKey where the origin is a wildcard
    AnchoredKey(Wildcard, Key),
    Wildcard(Wildcard),
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
    fn to_fields(&self) -> Vec<F> {
        // Encoding:
        // None =>                      (0,          0, 0, 0, 0,  0, 0, 0, 0)
        // Literal(v) =>                (1,        [v         ],  0, 0, 0, 0)
        // Key(wc_index, key_or_wc) =>  (2, [wc_index], 0, 0, 0, [key_or_wc])
        // WildcardLiteral(wc_index) => (3, [wc_index], 0, 0, 0,  0, 0, 0, 0)
        // In all three cases, we pad to 2 * hash_size + 1 = 9 field elements
        match self {
            StatementTmplArg::None => iter::once(F::from(StatementTmplArgPrefix::None))
                .chain(iter::repeat(F::ZERO))
                .take(Params::statement_tmpl_arg_size())
                .collect_vec(),
            StatementTmplArg::Literal(v) => iter::once(F::from(StatementTmplArgPrefix::Literal))
                .chain(v.raw().to_fields())
                .chain(iter::repeat(F::ZERO))
                .take(Params::statement_tmpl_arg_size())
                .collect_vec(),
            StatementTmplArg::AnchoredKey(wc1, kw2) => {
                iter::once(F::from(StatementTmplArgPrefix::AnchoredKey))
                    .chain(wc1.to_fields())
                    .chain(iter::repeat(F::ZERO).take(VALUE_SIZE - 1))
                    .chain(kw2.to_fields())
                    .collect_vec()
            }
            StatementTmplArg::Wildcard(wc) => {
                iter::once(F::from(StatementTmplArgPrefix::WildcardLiteral))
                    .chain(wc.to_fields())
                    .chain(iter::repeat(F::ZERO))
                    .take(Params::statement_tmpl_arg_size())
                    .collect_vec()
            }
        }
    }
}

impl fmt::Display for StatementTmplArg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::None => write!(f, "none"),
            Self::Literal(v) => v.fmt(f),
            Self::AnchoredKey(root, key) => {
                root.fmt(f)?;
                write!(f, "[")?;
                key.fmt(f)?;
                write!(f, "]")
            }
            Self::Wildcard(v) => v.fmt(f),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
pub enum PredicateOrWildcard {
    Predicate(Predicate),
    Wildcard(Wildcard),
}

impl PredicateOrWildcard {
    pub fn as_pred(&self) -> Option<&Predicate> {
        match self {
            Self::Predicate(pred) => Some(pred),
            _ => None,
        }
    }
    pub fn as_wc(&self) -> Option<&Wildcard> {
        match self {
            Self::Wildcard(wc) => Some(wc),
            _ => None,
        }
    }
}

impl fmt::Display for PredicateOrWildcard {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Predicate(pred) => pred.fmt(f),
            Self::Wildcard(wc) => {
                write!(f, "?")?;
                wc.fmt(f)
            }
        }
    }
}

#[derive(Clone, Copy)]
pub enum PredicateOrWildcardPrefix {
    Predicate = 0,
    Wildcard = 1,
}

impl From<PredicateOrWildcardPrefix> for F {
    fn from(prefix: PredicateOrWildcardPrefix) -> Self {
        Self::from_canonical_usize(prefix as usize)
    }
}

impl ToFields for PredicateOrWildcard {
    fn to_fields(&self) -> Vec<F> {
        // Encoding:
        // Predicate(pred) => (0, [hash(pred)  ])
        // Wildcard(wc)    => (1, wc_index, 0...)
        match self {
            Self::Predicate(pred) => iter::once(F::from(PredicateOrWildcardPrefix::Predicate))
                .chain(pred.hash().to_fields())
                .collect_vec(),
            Self::Wildcard(wc) => iter::once(F::from(PredicateOrWildcardPrefix::Wildcard))
                .chain(wc.to_fields())
                .chain(iter::repeat(F::ZERO))
                .take(Params::pred_hash_or_wc_size())
                .collect_vec(),
        }
    }
}

/// Statement Template for a Custom Predicate
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
pub struct StatementTmpl {
    pub pred_or_wc: PredicateOrWildcard,
    pub args: Vec<StatementTmplArg>,
}

impl StatementTmpl {
    pub fn pred_or_wc(&self) -> &PredicateOrWildcard {
        &self.pred_or_wc
    }
    pub fn args(&self) -> &[StatementTmplArg] {
        &self.args
    }
}

impl fmt::Display for StatementTmpl {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.pred_or_wc.fmt(f)?;
        write!(f, "(")?;
        for (i, arg) in self.args.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            arg.fmt(f)?;
        }
        write!(f, ")")
    }
}

impl ToFields for StatementTmpl {
    fn to_fields(&self) -> Vec<F> {
        // serialize as:
        // predicate (4 field elements)
        // then the StatementTmplArgs

        // TODO think if this check should go into the StatementTmpl creation,
        // instead of at the `to_fields` method, where we should assume that the
        // values are already valid
        if self.args.len() > BASE_PARAMS.max_statement_args {
            panic!(
                "Statement template has too many arguments {} > {}",
                self.args.len(),
                BASE_PARAMS.max_statement_args
            );
        }

        self.pred_or_wc
            .to_fields()
            .into_iter()
            .chain(self.args.iter().flat_map(|sta| sta.to_fields()))
            .chain(iter::repeat(F::ZERO))
            .take(Params::statement_tmpl_size())
            .collect_vec()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
/// NOTE: fields are not public (outside of crate) to enforce the struct instantiation through
/// the `::and/or` methods, which performs checks on the values.
pub struct CustomPredicate {
    pub name: String, // Non-cryptographic metadata
    /// true for "and", false for "or"
    pub(crate) conjunction: bool,
    pub(crate) statements: Vec<StatementTmpl>,
    pub(crate) args_len: usize,
    /// Names of the wildcards, the first `args_len` entries correspond to the `args_len` arguments
    /// of the custom predicate.
    pub(crate) wildcard_names: Vec<String>,
    // TODO: Add private args length?
    // TODO: Add args type information?
}

impl CustomPredicate {
    pub fn empty() -> Self {
        Self {
            name: "empty".to_string(),
            conjunction: false,
            statements: vec![StatementTmpl {
                pred_or_wc: PredicateOrWildcard::Predicate(Predicate::Native(
                    NativePredicate::None,
                )),
                args: vec![],
            }],
            args_len: 0,
            wildcard_names: vec![],
        }
    }
    pub fn and(
        params: &Params,
        name: String,
        statements: Vec<StatementTmpl>,
        args_len: usize,
        wildcard_names: Vec<String>,
    ) -> Result<Self> {
        Self::new(params, name, true, statements, args_len, wildcard_names)
    }
    pub fn or(
        params: &Params,
        name: String,
        statements: Vec<StatementTmpl>,
        args_len: usize,
        wildcard_names: Vec<String>,
    ) -> Result<Self> {
        Self::new(params, name, false, statements, args_len, wildcard_names)
    }
    /// Creates a new custom predicate.
    ///
    /// # Arguments
    /// * `name` - The name of the custom predicate.
    /// * `conjunction` - `true` for an `and` predicate, `false` for an `or` predicate.
    /// * `statements` - The statements required to apply the custom predicate.
    /// * `args_len` - The number of public arguments.
    /// * `wildcard_names` - The names of the arguments (public and private).
    pub fn new(
        params: &Params,
        name: String,
        conjunction: bool,
        statements: Vec<StatementTmpl>,
        args_len: usize,
        wildcard_names: Vec<String>,
    ) -> Result<Self> {
        if statements.len() > Params::max_custom_predicate_arity() {
            return Err(Error::max_length(
                "statements.len".to_string(),
                statements.len(),
                Params::max_custom_predicate_arity(),
            ));
        }
        if args_len > Params::max_statement_args() {
            return Err(Error::max_length(
                "statement_args.len".to_string(),
                args_len,
                Params::max_statement_args(),
            ));
        }
        if wildcard_names.len() > params.max_custom_predicate_wildcards {
            return Err(Error::max_length(
                "custom_predicate_wildcards.len".to_string(),
                wildcard_names.len(),
                params.max_custom_predicate_wildcards,
            ));
        }

        Ok(Self {
            name,
            conjunction,
            statements,
            args_len,
            wildcard_names,
        })
    }
    pub fn pad_statement_tmpl(&self) -> StatementTmpl {
        StatementTmpl {
            pred_or_wc: PredicateOrWildcard::Predicate(Predicate::Native(if self.conjunction {
                NativePredicate::None
            } else {
                NativePredicate::False
            })),
            args: vec![],
        }
    }
    pub fn is_conjunction(&self) -> bool {
        self.conjunction
    }
    pub fn is_disjunction(&self) -> bool {
        !self.conjunction
    }
    pub fn statements(&self) -> &[StatementTmpl] {
        &self.statements
    }
    pub fn args_len(&self) -> usize {
        self.args_len
    }
    pub fn wildcard_names(&self) -> &[String] {
        &self.wildcard_names
    }
}

impl ToFields for CustomPredicate {
    fn to_fields(&self) -> Vec<F> {
        // serialize as:
        // conjunction (one field element)
        // args_len (one field element)
        // statements
        //   (params.max_custom_predicate_arity * params.statement_tmpl_size())
        //   field elements

        // NOTE: this method assumes that the self.params.len() is inside the
        // expected bound, as Self should be instantiated with the constructor
        // method `new` which performs the check.
        if self.statements.len() > BASE_PARAMS.max_custom_predicate_arity {
            panic!("Custom predicate depends on too many statements");
        }

        let pad_st = self.pad_statement_tmpl();
        iter::once(F::from_bool(self.conjunction))
            .chain(iter::once(F::from_canonical_usize(self.args_len)))
            .chain(
                self.statements
                    .iter()
                    .chain(iter::repeat(&pad_st))
                    .take(BASE_PARAMS.max_custom_predicate_arity)
                    .flat_map(|st| st.to_fields()),
            )
            .collect_vec()
    }
}

impl fmt::Display for CustomPredicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}(", self.name)?;
        for (i, name) in self.wildcard_names.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            if i == self.args_len {
                write!(f, "private: ")?;
            }
            if f.alternate() {
                write!(f, "{}:", i)?;
            }
            write!(f, "{}", name)?;
        }
        writeln!(f, ") = {}(", if self.conjunction { "AND" } else { "OR" })?;
        for st in &self.statements {
            write!(f, "  ")?;
            st.pred_or_wc.fmt(f)?;
            write!(f, "(")?;
            for (i, arg) in st.args.iter().enumerate() {
                if i != 0 {
                    write!(f, ", ")?;
                }
                arg.fmt(f)?;
            }
            writeln!(f, ")")?;
        }
        write!(f, ")")?;
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, JsonSchema)]
enum CustomPredicateBatchData {
    Full {
        #[serde(skip)]
        #[schemars(skip)]
        mt: MerkleTree,
        predicates: Vec<CustomPredicate>,
    },
    Opaque {
        id: Hash,
    },
}

// TODO: Rename Batch for Module everywhere in the code base
impl CustomPredicateBatchData {
    fn new_full(predicates: Vec<CustomPredicate>) -> Self {
        let kvs: HashMap<RawValue, RawValue> = predicates
            .iter()
            .enumerate()
            .map(|(index, pred)| {
                let cp_hash = hash_fields(&pred.to_fields());
                (Value::from(index as i64).raw(), Value::from(cp_hash).raw())
            })
            .collect();
        let mt = MerkleTree::new(&kvs);
        Self::Full { mt, predicates }
    }
    fn new_opaque(id: Hash) -> Self {
        Self::Opaque { id }
    }
}

impl<'de> Deserialize<'de> for CustomPredicateBatchData {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        enum Aux {
            Full { predicates: Vec<CustomPredicate> },
            Opaque { id: Hash },
        }
        let aux = Aux::deserialize(deserializer)?;
        Ok(match aux {
            Aux::Opaque { id } => Self::new_opaque(id),
            Aux::Full { predicates } => Self::new_full(predicates),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct CustomPredicateBatch {
    pub name: String,
    data: CustomPredicateBatchData,
}

impl std::hash::Hash for CustomPredicateBatch {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id().hash(state);
    }
}

impl CustomPredicateBatch {
    pub fn new(name: String, predicates: Vec<CustomPredicate>) -> Arc<Self> {
        Arc::new(Self {
            name,
            data: CustomPredicateBatchData::new_full(predicates),
        })
    }

    pub fn new_opaque(name: String, id: Hash) -> Arc<Self> {
        Arc::new(Self {
            name,
            data: CustomPredicateBatchData::Opaque { id },
        })
    }

    pub fn id(&self) -> Hash {
        match &self.data {
            CustomPredicateBatchData::Opaque { id } => *id,
            CustomPredicateBatchData::Full { mt, .. } => mt.root(),
        }
    }
    pub fn predicates(&self) -> &[CustomPredicate] {
        match &self.data {
            // TODO: Return Option here instead of panic
            CustomPredicateBatchData::Opaque { .. } => panic!("opaque batch"),
            CustomPredicateBatchData::Full { predicates, .. } => predicates,
        }
    }
    pub fn mt(&self) -> &MerkleTree {
        match &self.data {
            // TODO: Return Option here instead of panic
            CustomPredicateBatchData::Opaque { .. } => panic!("opaque batch"),
            CustomPredicateBatchData::Full { mt, .. } => mt,
        }
    }
    pub fn predicate_ref_by_name(
        self: &Arc<CustomPredicateBatch>,
        name: &str,
    ) -> Option<CustomPredicateRef> {
        self.predicates()
            .iter()
            .enumerate()
            .find_map(|(i, cp)| (cp.name == name).then(|| CustomPredicateRef::new(self.clone(), i)))
    }
    pub fn predicate_ref_by_index(
        self: &Arc<CustomPredicateBatch>,
        index: usize,
    ) -> Option<CustomPredicateRef> {
        self.predicates()
            .get(index)
            .map(|_| CustomPredicateRef::new(self.clone(), index))
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct CustomPredicateRef {
    pub batch: Arc<CustomPredicateBatch>,
    pub index: usize,
}

impl std::hash::Hash for CustomPredicateRef {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (self.batch.id(), self.index).hash(state);
    }
}

impl PartialEq for CustomPredicateRef {
    fn eq(&self, other: &Self) -> bool {
        self.batch.id() == other.batch.id() && self.index == other.index
    }
}

impl Eq for CustomPredicateRef {}

impl CustomPredicateRef {
    pub fn new(batch: Arc<CustomPredicateBatch>, index: usize) -> Self {
        Self { batch, index }
    }
    pub fn arg_len(&self) -> usize {
        self.predicate().args_len
    }
    pub fn predicate(&self) -> &CustomPredicate {
        &self.batch.predicates()[self.index]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        dict,
        middleware::{
            AnchoredKey, CustomPredicate, CustomPredicateBatch, CustomPredicateRef, Key,
            NativePredicate, Operation, Params, Predicate, Statement, StatementTmpl,
            StatementTmplArg,
        },
    };

    fn st(p: Predicate, args: Vec<StatementTmplArg>) -> StatementTmpl {
        StatementTmpl {
            pred_or_wc: PredicateOrWildcard::Predicate(p),
            args,
        }
    }

    fn key(name: &str) -> Key {
        Key::from(name)
    }
    fn wc(i: usize) -> Wildcard {
        Wildcard {
            name: format!("{}", i),
            index: i,
        }
    }
    fn names(names: &[&str]) -> Vec<String> {
        names.iter().map(|s| s.to_string()).collect()
    }

    #[allow(clippy::upper_case_acronyms)]
    type STA = StatementTmplArg;
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
            "is_double".to_string(),
            vec![CustomPredicate::and(
                &params,
                "_".into(),
                vec![
                    st(
                        P::Native(NP::Equal),
                        vec![STA::AnchoredKey(wc(1), key("c")), STA::Literal(2.into())],
                    ),
                    st(
                        P::Native(NP::ProductOf),
                        vec![
                            STA::AnchoredKey(wc(0), key("a")),
                            STA::AnchoredKey(wc(1), key("b")),
                            STA::Literal(Value::from(3)),
                        ],
                    ),
                ],
                1,
                names(&["0", "1", "2"]),
            )?],
        );

        let d0 = dict!({
            "a" => 10,
        });
        let d1 = dict!({
            "b" => 15,
            "c" => 17,
        });
        let custom_statement = Statement::Custom(
            CustomPredicateRef::new(cust_pred_batch.clone(), 0),
            vec![Value::from(d0.clone())],
        );

        let custom_deduction = Operation::Custom(
            CustomPredicateRef::new(cust_pred_batch, 0),
            vec![
                Statement::equal(AnchoredKey::from((&d1, "c")), 2),
                Statement::product_of(
                    AnchoredKey::from((&d0, "a")),
                    AnchoredKey::from((&d1, "b")),
                    Value::from(3),
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

        let eth_friend = CustomPredicate::and(
            &params,
            "eth_friend".into(),
            vec![
                st(
                    P::Native(NP::SignedBy),
                    vec![STA::Wildcard(wc(2)), STA::Wildcard(wc(0))],
                ),
                st(
                    P::Native(NP::Equal),
                    vec![
                        STA::AnchoredKey(wc(2), Key::from("attestation")),
                        STA::Wildcard(wc(1)),
                    ],
                ),
            ],
            2,
            names(&["0", "1", "2"]),
        )?;

        let eth_friend_batch =
            CustomPredicateBatch::new("eth_friend".to_string(), vec![eth_friend]);

        // 0
        let eth_dos_base = CustomPredicate::and(
            &params,
            "eth_dos_base".into(),
            vec![
                st(
                    P::Native(NP::Equal),
                    vec![STA::Wildcard(wc(0)), STA::Wildcard(wc(1))],
                ),
                st(
                    P::Native(NP::Equal),
                    vec![STA::Wildcard(wc(2)), STA::Literal(0.into())],
                ),
            ],
            3,
            names(&["0", "1", "2"]),
        )?;

        // 1
        let eth_dos_ind = CustomPredicate::and(
            &params,
            "eth_dos_ind".into(),
            vec![
                st(
                    P::BatchSelf(2),
                    vec![
                        STA::Wildcard(wc(0)),
                        STA::Wildcard(wc(4)),
                        STA::Wildcard(wc(3)),
                    ],
                ),
                st(
                    P::Native(NP::SumOf),
                    vec![
                        STA::Wildcard(wc(2)),
                        STA::Wildcard(wc(3)),
                        STA::Literal(Value::from(1)),
                    ],
                ),
                st(
                    P::Custom(CustomPredicateRef::new(eth_friend_batch.clone(), 0)),
                    vec![STA::Wildcard(wc(4)), STA::Wildcard(wc(1))],
                ),
            ],
            3,
            names(&["0", "1", "2", "3", "4"]),
        )?;

        // 2
        let eth_dos = CustomPredicate::or(
            &params,
            "eth_dos".into(),
            vec![
                st(
                    P::BatchSelf(0),
                    vec![
                        STA::Wildcard(wc(0)),
                        STA::Wildcard(wc(1)),
                        STA::Wildcard(wc(2)),
                    ],
                ),
                st(
                    P::BatchSelf(1),
                    vec![
                        STA::Wildcard(wc(0)),
                        STA::Wildcard(wc(1)),
                        STA::Wildcard(wc(2)),
                    ],
                ),
            ],
            3,
            names(&["0", "1", "2"]),
        )?;

        let eth_dos_distance_batch = CustomPredicateBatch::new(
            "ETHDoS_distance".to_string(),
            vec![eth_dos_base, eth_dos_ind, eth_dos],
        );

        // Example statement
        let ethdos_example = Statement::Custom(
            CustomPredicateRef::new(eth_dos_distance_batch.clone(), 2),
            vec![Value::from("Alice"), Value::from("Bob"), Value::from(7)],
        );

        // Copies should work.
        assert!(Operation::CopyStatement(ethdos_example.clone()).check(&params, &ethdos_example)?);

        // This could arise as the inductive step.
        let ethdos_ind_example = Statement::Custom(
            CustomPredicateRef::new(eth_dos_distance_batch.clone(), 1),
            vec![Value::from("Alice"), Value::from("Bob"), Value::from(7)],
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
                vec![Value::from("Alice"), Value::from("Charlie"), Value::from(6)],
            ),
            Statement::sum_of(Value::from(7), Value::from(6), Value::from(1)),
            Statement::Custom(
                CustomPredicateRef::new(eth_friend_batch.clone(), 0),
                vec![Value::from("Charlie"), Value::from("Bob")],
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
