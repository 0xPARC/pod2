//! The middleware includes the type definitions and the traits used to connect the frontend and
//! the backend.

use anyhow::{anyhow, Error, Result};
use dyn_clone::DynClone;
use hex::{FromHex, FromHexError};
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::config::{Hasher, PoseidonGoldilocksConfig};
use std::any::Any;
use std::cmp::{Ord, Ordering};
use std::collections::HashMap;
use std::fmt;
use strum_macros::FromRepr;

pub mod containers;

pub const KEY_SIGNER: &str = "_signer";
pub const KEY_TYPE: &str = "_type";
pub const STATEMENT_ARG_F_LEN: usize = 8;

/// F is the native field we use everywhere.  Currently it's Goldilocks from plonky2
pub type F = GoldilocksField;
/// C is the Plonky2 config used in POD2 to work with Plonky2 recursion.
pub type C = PoseidonGoldilocksConfig;
/// D defines the extension degree of the field used in the Plonky2 proofs (quadratic extension).
pub const D: usize = 2;

#[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq)]
pub struct Value(pub [F; 4]);

impl Ord for Value {
    fn cmp(&self, other: &Self) -> Ordering {
        for (lhs, rhs) in self.0.iter().zip(other.0.iter()).rev() {
            let (lhs, rhs) = (lhs.to_canonical_u64(), rhs.to_canonical_u64());
            if lhs < rhs {
                return Ordering::Less;
            } else if lhs > rhs {
                return Ordering::Greater;
            }
        }
        return Ordering::Equal;
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl From<i64> for Value {
    fn from(v: i64) -> Self {
        let lo = F::from_canonical_u64((v as u64) & 0xffffffff);
        let hi = F::from_canonical_u64((v as u64) >> 32);
        Value([lo, hi, F::ZERO, F::ZERO])
    }
}

impl From<Hash> for Value {
    fn from(h: Hash) -> Self {
        Value(h.0)
    }
}

impl TryInto<i64> for Value {
    type Error = Error;
    fn try_into(self) -> std::result::Result<i64, Self::Error> {
        let value = self.0;
        if &value[2..] != &[F::ZERO, F::ZERO]
            || value[..2]
                .iter()
                .all(|x| x.to_canonical_u64() > u32::MAX as u64)
        {
            Err(anyhow!("Value not an element of the i64 embedding."))
        } else {
            Ok((value[0].to_canonical_u64() + value[1].to_canonical_u64() << 32) as i64)
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0[2].is_zero() && self.0[3].is_zero() {
            // Assume this is an integer
            let (l0, l1) = (self.0[0].to_canonical_u64(), self.0[1].to_canonical_u64());
            assert!(l0 < (1 << 32));
            assert!(l1 < (1 << 32));
            write!(f, "{}", l0 + l1 * (1 << 32))
        } else {
            // Assume this is a hash
            Hash(self.0).fmt(f)
        }
    }
}

#[derive(Clone, Copy, Debug, Default, Hash, Eq, PartialEq)]
pub struct Hash(pub [F; 4]);

impl ToFields for Hash {
    fn to_fields(self) -> (Vec<F>, usize) {
        (self.0.to_vec(), 4)
    }
}

impl Ord for Hash {
    fn cmp(&self, other: &Self) -> Ordering {
        Value(self.0).cmp(&Value(other.0))
    }
}

impl PartialOrd for Hash {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

pub const EMPTY: Value = Value([F::ZERO, F::ZERO, F::ZERO, F::ZERO]);
pub const NULL: Hash = Hash([F::ZERO, F::ZERO, F::ZERO, F::ZERO]);

impl fmt::Display for Hash {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let v0 = self.0[0].to_canonical_u64();
        for i in 0..4 {
            write!(f, "{:02x}", (v0 >> (i * 8)) & 0xff)?;
        }
        write!(f, "…")
    }
}

impl FromHex for Hash {
    type Error = FromHexError;

    fn from_hex<T: AsRef<[u8]>>(hex: T) -> Result<Self, Self::Error> {
        // In little endian
        let bytes = <[u8; 32]>::from_hex(hex)?;
        let mut buf: [u8; 8] = [0; 8];
        let mut inner = [F::ZERO; 4];
        for i in 0..4 {
            buf.copy_from_slice(&bytes[8 * i..8 * (i + 1)]);
            inner[i] = F::from_canonical_u64(u64::from_le_bytes(buf));
        }
        Ok(Self(inner))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct PodId(pub Hash);

impl ToFields for PodId {
    fn to_fields(self) -> (Vec<F>, usize) {
        self.0.to_fields()
    }
}

pub const SELF: PodId = PodId(Hash([F::ONE, F::ZERO, F::ZERO, F::ZERO]));

impl fmt::Display for PodId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self == SELF {
            write!(f, "self")
        } else if self.0 == NULL {
            write!(f, "null")
        } else {
            write!(f, "{}", self.0)
        }
    }
}

pub enum PodType {
    None = 0,
    MockSigned = 1,
    MockMain = 2,
    Signed = 3,
    Main = 4,
}

impl From<PodType> for Value {
    fn from(v: PodType) -> Self {
        Value::from(v as i64)
    }
}

pub fn hash_str(s: &str) -> Hash {
    let mut input = s.as_bytes().to_vec();
    input.push(1); // padding
                   // Merge 7 bytes into 1 field, because the field is slightly below 64 bits
    let input: Vec<F> = input
        .chunks(7)
        .map(|bytes| {
            let mut v: u64 = 0;
            for b in bytes.iter().rev() {
                v <<= 8;
                v += *b as u64;
            }
            F::from_canonical_u64(v)
        })
        .collect();
    Hash(PoseidonHash::hash_no_pad(&input).elements)
}

#[derive(Clone, Debug, Copy)]
pub struct Params {
    pub max_input_signed_pods: usize,
    pub max_input_main_pods: usize,
    pub max_statements: usize,
    pub max_signed_pod_values: usize,
    pub max_public_statements: usize,
    pub max_statement_args: usize,
    pub max_operation_args: usize,
}

impl Params {
    pub fn max_priv_statements(&self) -> usize {
        self.max_statements - self.max_public_statements
    }
}

impl Default for Params {
    fn default() -> Self {
        Self {
            max_input_signed_pods: 3,
            max_input_main_pods: 3,
            max_statements: 20,
            max_signed_pod_values: 8,
            max_public_statements: 10,
            max_statement_args: 5,
            max_operation_args: 5,
        }
    }
}

#[derive(Clone, Copy, Debug, FromRepr, PartialEq, Eq)]
pub enum NativePredicate {
    None = 0,
    ValueOf = 1,
    Equal = 2,
    NotEqual = 3,
    Gt = 4,
    Lt = 5,
    Contains = 6,
    NotContains = 7,
    SumOf = 8,
    ProductOf = 9,
    MaxOf = 10,
}

impl ToFields for NativePredicate {
    fn to_fields(self) -> (Vec<F>, usize) {
        (vec![F::from_canonical_u64(self as u64)], 1)
    }
}

use std::sync::Arc;

// BEGIN Custom 1b

#[derive(Debug)]
pub enum HashOrWildcard {
    Hash(Hash),
    Wildcard(usize),
}

impl fmt::Display for HashOrWildcard {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Hash(h) => write!(f, "{}", h),
            Self::Wildcard(n) => write!(f, "*{}", n),
        }
    }
}

#[derive(Debug)]
pub enum StatementTmplArg {
    None,
    Literal(Value),
    Key(HashOrWildcard, HashOrWildcard),
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
#[derive(Debug)]
pub struct StatementTmpl(Predicate, Vec<StatementTmplArg>);

#[derive(Debug)]
pub struct CustomPredicate {
    /// true for "and", false for "or"
    pub conjunction: bool,
    pub statements: Vec<StatementTmpl>,
    pub args_len: usize,
    // TODO: Add private args length?
    // TODO: Add args type information?
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

#[derive(Debug)]
pub struct CustomPredicateBatch {
    predicates: Vec<CustomPredicate>,
}

impl CustomPredicateBatch {
    pub fn hash(&self) -> Hash {
        // TODO
        hash_str(&format!("{:?}", self))
    }
}

#[derive(Clone, Debug)]
pub enum Predicate {
    Native(NativePredicate),
    BatchSelf(usize),
    Custom(Arc<CustomPredicateBatch>, usize),
}

impl From<NativePredicate> for Predicate {
    fn from(v: NativePredicate) -> Self {
        Self::Native(v)
    }
}

impl ToFields for Predicate {
    fn to_fields(self) -> (Vec<F>, usize) {
        todo!()
    }
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Native(p) => write!(f, "{:?}", p),
            Self::BatchSelf(i) => write!(f, "self.{}", i),
            Self::Custom(pb, i) => write!(f, "{}.{}", pb.hash(), i),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// AnchoredKey is a tuple containing (OriginId: PodId, key: Hash)
pub struct AnchoredKey(pub PodId, pub Hash);

impl AnchoredKey {
    pub fn origin(&self) -> PodId {
        self.0
    }
    pub fn key(&self) -> Hash {
        self.1
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatementArg {
    None,
    Literal(Value),
    Key(AnchoredKey),
}

impl fmt::Display for StatementArg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            StatementArg::None => write!(f, "none"),
            StatementArg::Literal(v) => write!(f, "{}", v),
            StatementArg::Key(r) => write!(f, "{}.{}", r.0, r.1),
        }
    }
}

impl StatementArg {
    pub fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }
    pub fn literal(&self) -> Result<Value> {
        match self {
            Self::Literal(value) => Ok(*value),
            _ => Err(anyhow!("Statement argument {:?} is not a literal.", self)),
        }
    }
    pub fn key(&self) -> Result<AnchoredKey> {
        match self {
            Self::Key(ak) => Ok(ak.clone()),
            _ => Err(anyhow!("Statement argument {:?} is not a key.", self)),
        }
    }
}

impl ToFields for StatementArg {
    fn to_fields(self) -> (Vec<F>, usize) {
        // NOTE: current version returns always the same amount of field elements in the returned
        // vector, which means that the `None` case is padded with 8 zeroes, and the `Literal` case
        // is padded with 4 zeroes. Since the returned vector will mostly be hashed (and reproduced
        // in-circuit), we might be interested into reducing the length of it. If that's the case,
        // we can check if it makes sense to make it dependant on the concrete StatementArg; that
        // is, when dealing with a `None` it would be a single field element (zero value), and when
        // dealing with `Literal` it would be of length 4.
        let f = match self {
            StatementArg::None => vec![F::ZERO; STATEMENT_ARG_F_LEN],
            StatementArg::Literal(v) => {
                let value_f = v.0.to_vec();
                [
                    value_f.clone(),
                    vec![F::ZERO; STATEMENT_ARG_F_LEN - value_f.len()],
                ]
                .concat()
            }
            StatementArg::Key(ak) => {
                let (podid_f, _) = ak.0.to_fields();
                let (hash_f, _) = ak.1.to_fields();
                [podid_f, hash_f].concat()
            }
        };
        assert_eq!(f.len(), STATEMENT_ARG_F_LEN); // sanity check
        (f, STATEMENT_ARG_F_LEN)
    }
}

// TODO: Replace this with a more stringly typed enum as in the Devcon implementation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Statement(pub NativePredicate, pub Vec<StatementArg>);

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} ", self.0)?;
        for (i, arg) in self.1.iter().enumerate() {
            if !(!f.alternate() && arg.is_none()) {
                if i != 0 {
                    write!(f, " ")?;
                }
                write!(f, "{}", arg)?;
            }
        }
        Ok(())
    }
}

impl Statement {
    pub fn code(&self) -> NativePredicate {
        self.0
    }
    pub fn args(&self) -> &[StatementArg] {
        &self.1
    }
    pub fn is_none(&self) -> bool {
        matches!(self.0, NativePredicate::None)
    }
}

impl ToFields for Statement {
    fn to_fields(self) -> (Vec<F>, usize) {
        let (native_statement_f, native_statement_f_len) = self.0.to_fields();
        let (vec_statementarg_f, vec_statementarg_f_len) = self
            .1
            .into_iter()
            .map(|statement_arg| statement_arg.to_fields())
            .fold((Vec::new(), 0), |mut acc, (f, l)| {
                acc.0.extend(f);
                acc.1 += l;
                acc
            });
        (
            [native_statement_f, vec_statementarg_f].concat(),
            native_statement_f_len + vec_statementarg_f_len,
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeOperation {
    None = 0,
    NewEntry = 1,
    CopyStatement = 2,
    EqualFromEntries = 3,
    NotEqualFromEntries = 4,
    GtFromEntries = 5,
    LtFromEntries = 6,
    TransitiveEqualFromStatements = 7,
    GtToNotEqual = 8,
    LtToNotEqual = 9,
    ContainsFromEntries = 10,
    NotContainsFromEntries = 11,
    RenameContainedBy = 12,
    SumOf = 13,
    ProductOf = 14,
    MaxOf = 15,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OperationArg {
    None,
    Statement(Statement),
    Key(AnchoredKey),
}

impl OperationArg {
    pub fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }
    pub fn statement(&self) -> Result<Statement> {
        match self {
            Self::Statement(statement) => Ok(statement.clone()),
            _ => Err(anyhow!("Operation argument {:?} is not a statement.", self)),
        }
    }
    pub fn key(&self) -> Result<AnchoredKey> {
        match self {
            Self::Key(ak) => Ok(ak.clone()),
            _ => Err(anyhow!("Operation argument {:?} is not a key.", self)),
        }
    }
}

// TODO: Replace this with a more stringly typed enum as in the Devcon implementation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Operation(pub NativeOperation, pub Vec<OperationArg>);

impl Operation {
    pub fn code(&self) -> NativeOperation {
        self.0
    }
    pub fn args(&self) -> &[OperationArg] {
        &self.1
    }
    // TODO: Argument checking.
    // TODO: Use `Err` for all type mismatches rather than `false`.
    /// Checks the given operation against a statement.
    pub fn check(&self, output_statement: Statement) -> Result<bool> {
        use NativeOperation::*;
        match self.0 {
            // Nothing to check.
            None => Ok(output_statement.code() == NativePredicate::None),
            // Check that the resulting statement is of type `ValueOf`
            // and its origin is `SELF`.
            NewEntry =>
                Ok(output_statement.code() == NativePredicate::ValueOf && output_statement.args()[0].key()?.origin() == SELF)
            ,
            // Check that the operation acts on a statement *and* the
            // output is equal to this statement.
            CopyStatement => Ok(output_statement == self.args()[0].statement()?)
            ,
            EqualFromEntries => {
                let s1 = self.args()[0].statement()?;
                let (s1_key, s1_value) = (s1.args()[0].key()?, s1.args()[1].literal()?);
                let s2 = self.args()[1].statement()?;
                let (s2_key, s2_value) = (s2.args()[0].key()?, s2.args()[1].literal()?);
                let statements_equal = s1.code() == NativePredicate::ValueOf && s2.code() == NativePredicate::ValueOf && s1_value == s2_value;
                Ok(statements_equal && output_statement.code() == NativePredicate::Equal && output_statement.args()[0].key()? == s1_key && output_statement.args()[1].key()? == s2_key)}
            ,
            NotEqualFromEntries => {
                let s1 = self.args()[0].statement()?;
                let (s1_key, s1_value) = (s1.args()[0].key()?, s1.args()[1].literal()?);
                let s2 = self.args()[1].statement()?;
                let (s2_key, s2_value) = (s2.args()[0].key()?, s2.args()[1].literal()?);
                let statements_not_equal = s1.code() == NativePredicate::ValueOf && s2.code() == NativePredicate::ValueOf && s1_value != s2_value;
                Ok(statements_not_equal && output_statement.code() == NativePredicate::NotEqual && output_statement.args()[0].key()? == s1_key && output_statement.args()[1].key()? == s2_key)}                ,
            GtFromEntries => {
                let s1 = self.args()[0].statement()?;
                let (s1_key, s1_value) = (s1.args()[0].key()?, s1.args()[1].literal()?);
                let s2 = self.args()[1].statement()?;
                let (s2_key, s2_value) = (s2.args()[0].key()?, s2.args()[1].literal()?);
                let statements_not_equal = s1.code() == NativePredicate::ValueOf && s2.code() == NativePredicate::ValueOf && s1_value > s2_value;
                Ok(statements_not_equal && output_statement.code() == NativePredicate::Gt && output_statement.args()[0].key()? == s1_key && output_statement.args()[1].key()? == s2_key)},
            LtFromEntries => {
                let s1 = self.args()[0].statement()?;
                let (s1_key, s1_value) = (s1.args()[0].key()?, s1.args()[1].literal()?);
                let s2 = self.args()[1].statement()?;
                let (s2_key, s2_value) = (s2.args()[0].key()?, s2.args()[1].literal()?);
                let statements_not_equal = s1.code() == NativePredicate::ValueOf && s2.code() == NativePredicate::ValueOf && s1_value < s2_value;
                Ok(statements_not_equal && output_statement.code() == NativePredicate::Lt && output_statement.args()[0].key()? == s1_key && output_statement.args()[1].key()? == s2_key)},
            TransitiveEqualFromStatements => {
                let s1 = self.args()[0].statement()?;
                let s2 = self.args()[1].statement()?;
                let key1 = s1.args()[0].key()?;
                let key2 = s1.args()[1].key()?;
                let key3 = s2.args()[0].key()?;
                let key4 = s2.args()[1].key()?;
                let statements_satisfy_transitivity = s1.code() == NativePredicate::Equal && s2.code() == NativePredicate::Equal && key2 == key3;
                Ok(statements_satisfy_transitivity && output_statement.code() == NativePredicate::Equal && output_statement.args()[0].key()? == key1 && output_statement.args()[1].key()? == key4)
            },
            GtToNotEqual => {
                let s = self.args()[0].statement()?;
                let arg_is_gt = s.code() == NativePredicate::Gt;
                Ok(arg_is_gt && output_statement.code() == NativePredicate::NotEqual && output_statement.args() == s.args())
            },
            LtToNotEqual => {
                let s = self.args()[0].statement()?;
                let arg_is_lt = s.code() == NativePredicate::Lt;
                Ok(arg_is_lt && output_statement.code() == NativePredicate::NotEqual && output_statement.args() == s.args())
            },
            RenameContainedBy => {
                let s1 = self.args()[0].statement()?;
                let s2 = self.args()[1].statement()?;
                let key1 = s1.args()[0].key()?;
                let key2 = s1.args()[1].key()?;
                let key3 = s2.args()[0].key()?;
                let key4 = s2.args()[1].key()?;
                let args_satisfy_rename = s1.code() == NativePredicate::Contains && s2.code() == NativePredicate::Equal && key1 == key3;
                Ok(args_satisfy_rename && output_statement.code() == NativePredicate::Contains && output_statement.args()[0].key()? == key4 && output_statement.args()[1].key()? == key2)
            },
            SumOf => {
                let s1 = self.args()[0].statement()?;
                let s1_key = s1.args()[0].key()?;
                let s1_value: i64 = s1.args()[1].literal()?.try_into()?;
                let s2 = self.args()[1].statement()?;
                let s2_key = s2.args()[0].key()?;
                let s2_value:i64 = s2.args()[1].literal()?.try_into()?;
                let s3 = self.args()[2].statement()?;
                let s3_key = s3.args()[0].key()?;
                let s3_value: i64 = s3.args()[1].literal()?.try_into()?;
                let sum_holds = s1.code() == NativePredicate::ValueOf && s2.code() == NativePredicate::ValueOf && s3.code() == NativePredicate::ValueOf && s1_value == s2_value + s3_value;
                Ok(sum_holds && output_statement.code() == NativePredicate::SumOf && output_statement.args()[0].key()? == s1_key && output_statement.args()[1].key()? == s2_key && output_statement.args()[2].key()? == s3_key)
            },
            // TODO: Remaining ops.
            _ => Ok(true)
        }
    }
}

pub trait Pod: fmt::Debug + DynClone {
    fn verify(&self) -> bool;
    fn id(&self) -> PodId;
    fn pub_statements(&self) -> Vec<Statement>;
    /// Extract key-values from ValueOf public statements
    fn kvs(&self) -> HashMap<AnchoredKey, Value> {
        self.pub_statements()
            .into_iter()
            .filter_map(|st| match st.0 {
                NativePredicate::ValueOf => Some((
                    st.1[0].key().expect("key"),
                    st.1[1].literal().expect("literal"),
                )),
                _ => None,
            })
            .collect()
    }
    // Used for downcasting
    fn into_any(self: Box<Self>) -> Box<dyn Any>;
}

// impl Clone for Box<dyn SignedPod>
dyn_clone::clone_trait_object!(Pod);

pub trait PodSigner {
    fn sign(&mut self, params: &Params, kvs: &HashMap<Hash, Value>) -> Result<Box<dyn Pod>>;
}

/// This is a filler type that fulfills the Pod trait and always verifies.  It's empty.  This
/// can be used to simulate padding in a circuit.
#[derive(Debug, Clone)]
pub struct NonePod {}

impl Pod for NonePod {
    fn verify(&self) -> bool {
        true
    }
    fn id(&self) -> PodId {
        PodId(NULL)
    }
    fn pub_statements(&self) -> Vec<Statement> {
        Vec::new()
    }
    fn into_any(self: Box<Self>) -> Box<dyn Any> {
        self
    }
}

#[derive(Debug)]
pub struct MainPodInputs<'a> {
    pub signed_pods: &'a [&'a Box<dyn Pod>],
    pub main_pods: &'a [&'a Box<dyn Pod>],
    pub statements: &'a [Statement],
    pub operations: &'a [Operation],
    /// Statements that need to be made public (they can come from input pods or input
    /// statements)
    pub public_statements: &'a [Statement],
}

pub trait PodProver {
    fn prove(&mut self, params: &Params, inputs: MainPodInputs) -> Result<Box<dyn Pod>>;
}

pub trait ToFields {
    /// returns Vec<F> representation of the type, and a usize indicating how many field elements
    /// does the vector contain
    fn to_fields(self) -> (Vec<F>, usize);
}

#[cfg(test)]
mod tests {
    use super::*;

    enum HashOrWildcardStr {
        Hash(Hash),
        Wildcard(String),
    }

    fn l(s: &str) -> HashOrWildcardStr {
        HashOrWildcardStr::Hash(hash_str(s))
    }

    fn w(s: &str) -> HashOrWildcardStr {
        HashOrWildcardStr::Wildcard(s.to_string())
    }

    enum BuilderArg {
        Literal(Value),
        Key(HashOrWildcardStr, HashOrWildcardStr),
    }

    impl From<(HashOrWildcardStr, HashOrWildcardStr)> for BuilderArg {
        fn from((pod_id, key): (HashOrWildcardStr, HashOrWildcardStr)) -> Self {
            Self::Key(pod_id, key)
        }
    }

    impl<V> From<V> for BuilderArg
    where
        V: Into<Value>,
    {
        fn from(v: V) -> Self {
            Self::Literal(v.into())
        }
    }

    struct StatementTmplBuilder {
        predicate: Predicate,
        args: Vec<BuilderArg>,
    }

    fn st_tmpl(p: impl Into<Predicate>) -> StatementTmplBuilder {
        StatementTmplBuilder {
            predicate: p.into(),
            args: Vec::new(),
        }
    }

    impl StatementTmplBuilder {
        fn arg(mut self, a: impl Into<BuilderArg>) -> Self {
            self.args.push(a.into());
            self
        }
    }

    struct CustomPredicateBatchBuilder {
        predicates: Vec<CustomPredicate>,
    }

    impl CustomPredicateBatchBuilder {
        fn new() -> Self {
            Self {
                predicates: Vec::new(),
            }
        }

        fn predicate_and(
            &mut self,
            args: &[&str],
            priv_args: &[&str],
            sts: &[StatementTmplBuilder],
        ) -> Predicate {
            self.predicate(true, args, priv_args, sts)
        }

        fn predicate_or(
            &mut self,
            args: &[&str],
            priv_args: &[&str],
            sts: &[StatementTmplBuilder],
        ) -> Predicate {
            self.predicate(false, args, priv_args, sts)
        }

        fn predicate(
            &mut self,
            conjunction: bool,
            args: &[&str],
            priv_args: &[&str],
            sts: &[StatementTmplBuilder],
        ) -> Predicate {
            use BuilderArg as BA;
            let statements = sts
                .iter()
                .map(|sb| {
                    let args = sb
                        .args
                        .iter()
                        .map(|a| match a {
                            BA::Literal(v) => StatementTmplArg::Literal(*v),
                            BA::Key(pod_id, key) => StatementTmplArg::Key(
                                resolve_wildcard(args, priv_args, pod_id),
                                resolve_wildcard(args, priv_args, key),
                            ),
                        })
                        .collect();
                    StatementTmpl(sb.predicate.clone(), args)
                })
                .collect();
            let custom_predicate = CustomPredicate {
                conjunction,
                statements,
                args_len: args.len(),
            };
            self.predicates.push(custom_predicate);
            Predicate::BatchSelf(self.predicates.len() - 1)
        }

        fn finish(self) -> Arc<CustomPredicateBatch> {
            Arc::new(CustomPredicateBatch {
                predicates: self.predicates,
            })
        }
    }

    fn resolve_wildcard(
        args: &[&str],
        priv_args: &[&str],
        v: &HashOrWildcardStr,
    ) -> HashOrWildcard {
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

    #[test]
    fn test_custom_pred() {
        use NativePredicate as NP;

        let mut builder = CustomPredicateBatchBuilder::new();
        let eth_friend = builder.predicate_and(
            &["src_or", "src_key", "dst_or", "dst_key"],
            &["attestation_pod"],
            &[
                st_tmpl(NP::ValueOf)
                    .arg((w("attestation_pod"), l("type")))
                    .arg(PodType::Signed),
                st_tmpl(NP::Equal)
                    .arg((w("attestation_pod"), l("signer")))
                    .arg((w("src_or"), w("src_key"))),
                st_tmpl(NP::Equal)
                    .arg((w("attestation_pod"), l("attestation")))
                    .arg((w("dst_or"), w("dst_key"))),
            ],
        );

        println!("a.0. eth_friend = {}", builder.predicates.last().unwrap());
        let eth_friend = builder.finish();
        // This batch only has 1 predicate, so we pick it already for convenience
        let eth_friend = Predicate::Custom(eth_friend, 0);

        let mut builder = CustomPredicateBatchBuilder::new();
        let eth_dos_distance_base = builder.predicate_and(
            &[
                "src_or",
                "src_key",
                "dst_or",
                "dst_key",
                "distance_or",
                "distance_key",
            ],
            &[],
            &[
                st_tmpl(NP::Equal)
                    .arg((w("src_or"), l("src_key")))
                    .arg((w("dst_or"), w("dst_key"))),
                st_tmpl(NP::ValueOf)
                    .arg((w("distance_or"), w("distance_key")))
                    .arg(0),
            ],
        );

        println!(
            "b.0. eth_dos_distance_base = {}",
            builder.predicates.last().unwrap()
        );

        let eth_dos_distance = Predicate::BatchSelf(3);

        let eth_dos_distance_ind = builder.predicate_and(
            &[
                "src_or",
                "src_key",
                "dst_or",
                "dst_key",
                "distance_or",
                "distance_key",
            ],
            &[
                "one_or",
                "one_key",
                "shorter_distance_or",
                "shorter_distance_key",
                "intermed_or",
                "intermed_key",
            ],
            &[
                st_tmpl(eth_dos_distance)
                    .arg((w("src_or"), w("src_key")))
                    .arg((w("intermed_or"), w("intermed_key")))
                    .arg((w("shorter_distance_or"), w("shorter_distance_key"))),
                // distance == shorter_distance + 1
                st_tmpl(NP::ValueOf).arg((w("one_or"), w("one_key"))).arg(1),
                st_tmpl(NP::SumOf)
                    .arg((w("distance_or"), w("distance_key")))
                    .arg((w("shorter_distance_or"), w("shorter_distance_key")))
                    .arg((w("one_or"), w("one_key"))),
                // intermed is a friend of dst
                st_tmpl(eth_friend)
                    .arg((w("intermed_or"), w("intermed_key")))
                    .arg((w("dst_or"), w("dst_key"))),
            ],
        );

        println!(
            "b.1. eth_dos_distance_ind = {}",
            builder.predicates.last().unwrap()
        );

        let eth_dos_distance = builder.predicate_or(
            &[
                "src_or",
                "src_key",
                "dst_or",
                "dst_key",
                "distance_or",
                "distance_key",
            ],
            &[],
            &[
                st_tmpl(eth_dos_distance_base)
                    .arg((w("src_or"), w("src_key")))
                    .arg((w("dst_or"), w("dst_key")))
                    .arg((w("distance_or"), w("distance_key"))),
                st_tmpl(eth_dos_distance_ind)
                    .arg((w("src_or"), w("src_key")))
                    .arg((w("dst_or"), w("dst_key")))
                    .arg((w("distance_or"), w("distance_key"))),
            ],
        );

        println!(
            "b.2. eth_dos_distance = {}",
            builder.predicates.last().unwrap()
        );
    }
}
