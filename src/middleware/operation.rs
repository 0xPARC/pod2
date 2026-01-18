use std::{fmt, iter};

use itertools::Itertools;
use log::error;
use plonky2::field::types::Field;
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::primitives::{
        ec::{
            curve::{Point as PublicKey, GROUP_ORDER},
            schnorr::{SecretKey, Signature},
        },
        merkletree::{MerkleProof, MerkleTree, MerkleTreeOp, MerkleTreeStateTransitionProof},
    },
    middleware::{
        hash_values, AnchoredKey, CustomPredicate, CustomPredicateRef, Error, Hash, Key,
        MiddlewareInnerError, NativePredicate, Params, Predicate, PredicateOrWildcard, Result,
        Statement, StatementArg, StatementTmpl, StatementTmplArg, ToFields, TypedValue, Value,
        ValueRef, Wildcard, F,
    },
};

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum OperationType {
    Native(NativeOperation),
    Custom(CustomPredicateRef),
}

#[derive(Clone, Debug, PartialEq)]
pub enum OperationAux {
    None,
    MerkleProof(MerkleProof),
    MerkleTreeStateTransitionProof(MerkleTreeStateTransitionProof),
    Signature(Signature),
}

impl fmt::Display for OperationAux {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::None => write!(f, "<no aux>")?,
            Self::MerkleProof(pf) => write!(f, "merkle_proof({})", pf)?,
            // TODO: Make this look nicer.
            Self::MerkleTreeStateTransitionProof(pf) => {
                write!(f, "merkle_tree_state_transition_proof({:?})", pf)?
            }
            Self::Signature(sig) => write!(f, "signature({:?})", sig)?,
        }
        Ok(())
    }
}

impl ToFields for OperationType {
    /// Encoding:
    /// - Native(native_op) => `[1, [native_op], 0, 0, 0, 0]`
    /// - Custom(batch, index) => `[3, [batch.id], index]`
    fn to_fields(&self, params: &Params) -> Vec<F> {
        let mut fields: Vec<F> = match self {
            Self::Native(p) => iter::once(F::from_canonical_u64(1))
                .chain(p.to_fields(params))
                .collect(),
            Self::Custom(CustomPredicateRef { batch, index }) => {
                iter::once(F::from_canonical_u64(3))
                    .chain(batch.id().0)
                    .chain(iter::once(F::from_canonical_usize(*index)))
                    .collect()
            }
        };
        fields.resize_with(Params::operation_type_size(), || F::from_canonical_u64(0));
        fields
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, std::hash::Hash, Serialize, Deserialize)]
pub enum NativeOperation {
    None = 0,
    CopyStatement = 1,
    EqualFromEntries = 2,
    NotEqualFromEntries = 3,
    LtEqFromEntries = 4,
    LtFromEntries = 5,
    TransitiveEqualFromStatements = 6,
    LtToNotEqual = 7,
    ContainsFromEntries = 8,
    NotContainsFromEntries = 9,
    SumOf = 10,
    ProductOf = 11,
    MaxOf = 12,
    HashOf = 13,
    PublicKeyOf = 14,
    SignedBy = 15,
    ContainerInsertFromEntries = 16,
    ContainerUpdateFromEntries = 17,
    ContainerDeleteFromEntries = 18,

    // Syntactic sugar operations.  These operations are not supported by the backend.  The
    // frontend compiler is responsible of translating these operations into the operations above.
    DictContainsFromEntries = 1001,
    DictNotContainsFromEntries = 1002,
    SetContainsFromEntries = 1003,
    SetNotContainsFromEntries = 1004,
    ArrayContainsFromEntries = 1005,
    GtEqFromEntries = 1006,
    GtFromEntries = 1007,
    GtToNotEqual = 1008,
    DictInsertFromEntries = 1009,
    DictUpdateFromEntries = 1010,
    DictDeleteFromEntries = 1011,
    SetInsertFromEntries = 1012,
    SetDeleteFromEntries = 1013,
    ArrayUpdateFromEntries = 1014,
}

impl NativeOperation {
    pub fn is_syntactic_sugar(self) -> bool {
        (self as usize) >= 1000
    }
}

impl ToFields for NativeOperation {
    fn to_fields(&self, _params: &Params) -> Vec<F> {
        vec![F::from_canonical_u64(*self as u64)]
    }
}

impl OperationType {
    /// Gives the type of predicate that the operation will output, if known.
    /// CopyStatement may output any predicate (it will match the statement copied),
    /// so output_predicate returns None on CopyStatement.
    pub fn output_predicate(&self) -> Option<Predicate> {
        match self {
            OperationType::Native(native_op) => match native_op {
                NativeOperation::None => Some(Predicate::Native(NativePredicate::None)),
                NativeOperation::CopyStatement => None,
                NativeOperation::EqualFromEntries => {
                    Some(Predicate::Native(NativePredicate::Equal))
                }
                NativeOperation::NotEqualFromEntries => {
                    Some(Predicate::Native(NativePredicate::NotEqual))
                }
                NativeOperation::LtEqFromEntries => Some(Predicate::Native(NativePredicate::LtEq)),
                NativeOperation::LtFromEntries => Some(Predicate::Native(NativePredicate::Lt)),
                NativeOperation::TransitiveEqualFromStatements => {
                    Some(Predicate::Native(NativePredicate::Equal))
                }
                NativeOperation::LtToNotEqual => Some(Predicate::Native(NativePredicate::NotEqual)),
                NativeOperation::ContainsFromEntries => {
                    Some(Predicate::Native(NativePredicate::Contains))
                }
                NativeOperation::NotContainsFromEntries => {
                    Some(Predicate::Native(NativePredicate::NotContains))
                }
                NativeOperation::SumOf => Some(Predicate::Native(NativePredicate::SumOf)),
                NativeOperation::ProductOf => Some(Predicate::Native(NativePredicate::ProductOf)),
                NativeOperation::MaxOf => Some(Predicate::Native(NativePredicate::MaxOf)),
                NativeOperation::HashOf => Some(Predicate::Native(NativePredicate::HashOf)),
                NativeOperation::PublicKeyOf => {
                    Some(Predicate::Native(NativePredicate::PublicKeyOf))
                }
                NativeOperation::SignedBy => Some(Predicate::Native(NativePredicate::SignedBy)),
                NativeOperation::ContainerInsertFromEntries => {
                    Some(Predicate::Native(NativePredicate::ContainerInsert))
                }
                NativeOperation::ContainerUpdateFromEntries => {
                    Some(Predicate::Native(NativePredicate::ContainerUpdate))
                }
                NativeOperation::ContainerDeleteFromEntries => {
                    Some(Predicate::Native(NativePredicate::ContainerDelete))
                }
                no => unreachable!("Unexpected syntactic sugar op {:?}", no),
            },
            OperationType::Custom(cpr) => Some(Predicate::Custom(cpr.clone())),
        }
    }
}

// TODO: Refine this enum.
#[derive(Clone, Debug, PartialEq)]
pub enum Operation {
    None,
    CopyStatement(Statement),
    EqualFromEntries(Statement, Statement),
    NotEqualFromEntries(Statement, Statement),
    LtEqFromEntries(Statement, Statement),
    LtFromEntries(Statement, Statement),
    TransitiveEqualFromStatements(Statement, Statement),
    LtToNotEqual(Statement),
    ContainsFromEntries(
        /* root  */ Statement,
        /* key   */ Statement,
        /* value */ Statement,
        /* proof */ MerkleProof,
    ),
    NotContainsFromEntries(
        /* root  */ Statement,
        /* key   */ Statement,
        /* proof */ MerkleProof,
    ),
    SumOf(Statement, Statement, Statement),
    ProductOf(Statement, Statement, Statement),
    MaxOf(Statement, Statement, Statement),
    HashOf(Statement, Statement, Statement),
    PublicKeyOf(Statement, Statement),
    SignedBy(Statement, Statement, Signature),
    ContainerInsertFromEntries(
        /* new_root */ Statement,
        /* old_root */ Statement,
        /*  key    */ Statement,
        /*  value  */ Statement,
        /*  proof  */ MerkleTreeStateTransitionProof,
    ),
    ContainerUpdateFromEntries(
        /* new_root */ Statement,
        /* old_root */ Statement,
        /*  key    */ Statement,
        /*  value  */ Statement,
        /*  proof  */ MerkleTreeStateTransitionProof,
    ),
    ContainerDeleteFromEntries(
        /* new_root */ Statement,
        /* old_root */ Statement,
        /*  key    */ Statement,
        /*  proof  */ MerkleTreeStateTransitionProof,
    ),
    Custom(CustomPredicateRef, Vec<Statement>),
}

pub(crate) fn sum_op(x: i64, y: i64) -> i64 {
    x + y
}

pub(crate) fn prod_op(x: i64, y: i64) -> i64 {
    x * y
}

pub(crate) fn max_op(x: i64, y: i64) -> i64 {
    x.max(y)
}

pub(crate) fn hash_op(x: Value, y: Value) -> Value {
    Value::from(hash_values(&[x, y]))
}

impl Operation {
    pub fn op_type(&self) -> OperationType {
        type OT = OperationType;
        use NativeOperation::*;
        match self {
            Self::None => OT::Native(None),
            Self::CopyStatement(_) => OT::Native(CopyStatement),
            Self::EqualFromEntries(_, _) => OT::Native(EqualFromEntries),
            Self::NotEqualFromEntries(_, _) => OT::Native(NotEqualFromEntries),
            Self::LtEqFromEntries(_, _) => OT::Native(LtEqFromEntries),
            Self::LtFromEntries(_, _) => OT::Native(LtFromEntries),
            Self::TransitiveEqualFromStatements(_, _) => OT::Native(TransitiveEqualFromStatements),
            Self::LtToNotEqual(_) => OT::Native(LtToNotEqual),
            Self::ContainsFromEntries(_, _, _, _) => OT::Native(ContainsFromEntries),
            Self::NotContainsFromEntries(_, _, _) => OT::Native(NotContainsFromEntries),
            Self::SumOf(_, _, _) => OT::Native(SumOf),
            Self::ProductOf(_, _, _) => OT::Native(ProductOf),
            Self::MaxOf(_, _, _) => OT::Native(MaxOf),
            Self::HashOf(_, _, _) => OT::Native(HashOf),
            Self::PublicKeyOf(_, _) => OT::Native(PublicKeyOf),
            Self::SignedBy(_, _, _) => OT::Native(SignedBy),
            Self::ContainerInsertFromEntries(_, _, _, _, _) => {
                OT::Native(ContainerInsertFromEntries)
            }
            Self::ContainerUpdateFromEntries(_, _, _, _, _) => {
                OT::Native(ContainerUpdateFromEntries)
            }
            Self::ContainerDeleteFromEntries(_, _, _, _) => OT::Native(ContainerDeleteFromEntries),
            Self::Custom(cpr, _) => OT::Custom(cpr.clone()),
        }
    }

    pub fn args(&self) -> Vec<Statement> {
        match self.clone() {
            Self::None => vec![],
            Self::CopyStatement(s) => vec![s],
            Self::EqualFromEntries(s1, s2) => vec![s1, s2],
            Self::NotEqualFromEntries(s1, s2) => vec![s1, s2],
            Self::LtEqFromEntries(s1, s2) => vec![s1, s2],
            Self::LtFromEntries(s1, s2) => vec![s1, s2],
            Self::TransitiveEqualFromStatements(s1, s2) => vec![s1, s2],
            Self::LtToNotEqual(s) => vec![s],
            Self::ContainsFromEntries(s1, s2, s3, _pf) => vec![s1, s2, s3],
            Self::NotContainsFromEntries(s1, s2, _pf) => vec![s1, s2],
            Self::SumOf(s1, s2, s3) => vec![s1, s2, s3],
            Self::ProductOf(s1, s2, s3) => vec![s1, s2, s3],
            Self::MaxOf(s1, s2, s3) => vec![s1, s2, s3],
            Self::HashOf(s1, s2, s3) => vec![s1, s2, s3],
            Self::PublicKeyOf(s1, s2) => vec![s1, s2],
            Self::SignedBy(s1, s2, _sig) => vec![s1, s2],
            Self::ContainerInsertFromEntries(s1, s2, s3, s4, _pf) => vec![s1, s2, s3, s4],
            Self::ContainerUpdateFromEntries(s1, s2, s3, s4, _pf) => vec![s1, s2, s3, s4],
            Self::ContainerDeleteFromEntries(s1, s2, s3, _pf) => vec![s1, s2, s3],
            Self::Custom(_, args) => args,
        }
    }

    /// Extracts auxiliary data from operation.
    pub fn aux(&self) -> OperationAux {
        match self {
            Self::ContainsFromEntries(_, _, _, mp) => OperationAux::MerkleProof(mp.clone()),
            Self::NotContainsFromEntries(_, _, mp) => OperationAux::MerkleProof(mp.clone()),
            _ => OperationAux::None,
        }
    }

    /// Forms operation from op-code and arguments.
    pub fn op(op_code: OperationType, args: &[Statement], aux: &OperationAux) -> Result<Self> {
        type OA = OperationAux;
        type NO = NativeOperation;
        Ok(match op_code {
            OperationType::Native(o) => match (o, &args, aux.clone()) {
                (NO::None, &[], OA::None) => Self::None,
                (NO::CopyStatement, &[s], OA::None) => Self::CopyStatement(s.clone()),
                (NO::EqualFromEntries, &[s1, s2], OA::None) => {
                    Self::EqualFromEntries(s1.clone(), s2.clone())
                }
                (NO::NotEqualFromEntries, &[s1, s2], OA::None) => {
                    Self::NotEqualFromEntries(s1.clone(), s2.clone())
                }
                (NO::LtEqFromEntries, &[s1, s2], OA::None) => {
                    Self::LtEqFromEntries(s1.clone(), s2.clone())
                }
                (NO::LtFromEntries, &[s1, s2], OA::None) => {
                    Self::LtFromEntries(s1.clone(), s2.clone())
                }
                (NO::ContainsFromEntries, &[s1, s2, s3], OA::MerkleProof(pf)) => {
                    Self::ContainsFromEntries(s1.clone(), s2.clone(), s3.clone(), pf)
                }
                (NO::NotContainsFromEntries, &[s1, s2], OA::MerkleProof(pf)) => {
                    Self::NotContainsFromEntries(s1.clone(), s2.clone(), pf)
                }
                (NO::SumOf, &[s1, s2, s3], OA::None) => {
                    Self::SumOf(s1.clone(), s2.clone(), s3.clone())
                }
                (NO::ProductOf, &[s1, s2, s3], OA::None) => {
                    Self::ProductOf(s1.clone(), s2.clone(), s3.clone())
                }
                (NO::MaxOf, &[s1, s2, s3], OA::None) => {
                    Self::MaxOf(s1.clone(), s2.clone(), s3.clone())
                }
                (NO::HashOf, &[s1, s2, s3], OA::None) => {
                    Self::HashOf(s1.clone(), s2.clone(), s3.clone())
                }
                (NO::PublicKeyOf, &[s1, s2], OA::None) => Self::PublicKeyOf(s1.clone(), s2.clone()),
                (NO::SignedBy, &[s1, s2], OA::Signature(sig)) => {
                    Self::SignedBy(s1.clone(), s2.clone(), sig)
                }
                (
                    NO::ContainerInsertFromEntries,
                    &[s1, s2, s3, s4],
                    OA::MerkleTreeStateTransitionProof(pf),
                ) => Self::ContainerInsertFromEntries(
                    s1.clone(),
                    s2.clone(),
                    s3.clone(),
                    s4.clone(),
                    pf,
                ),
                (
                    NO::ContainerUpdateFromEntries,
                    &[s1, s2, s3, s4],
                    OA::MerkleTreeStateTransitionProof(pf),
                ) => Self::ContainerUpdateFromEntries(
                    s1.clone(),
                    s2.clone(),
                    s3.clone(),
                    s4.clone(),
                    pf,
                ),
                (
                    NO::ContainerDeleteFromEntries,
                    &[s1, s2, s3],
                    OA::MerkleTreeStateTransitionProof(pf),
                ) => Self::ContainerDeleteFromEntries(s1.clone(), s2.clone(), s3.clone(), pf),
                _ => Err(Error::custom(format!(
                    "Ill-formed operation {:?} with {} arguments {:?} and aux {:?}.",
                    op_code,
                    args.len(),
                    args,
                    aux
                )))?,
            },
            OperationType::Custom(cpr) => Self::Custom(cpr, args.to_vec()),
        })
    }

    /// Checks the given operation against a statement, and prints information if the check does not pass
    pub fn check_and_log(&self, params: &Params, output_statement: &Statement) -> Result<bool> {
        let valid: bool = self.check(params, output_statement)?;
        if !valid {
            error!("Check failed on the following statement");
            error!("{}", output_statement);
        }
        Ok(valid)
    }

    pub(crate) fn check_int_fn(
        v1: &Value,
        v2: &Value,
        v3: &Value,
        f: impl FnOnce(i64, i64) -> i64,
    ) -> Result<bool> {
        let i1: i64 = v1.typed().try_into()?;
        let i2: i64 = v2.typed().try_into()?;
        let i3: i64 = v3.typed().try_into()?;
        Ok(i1 == f(i2, i3))
    }

    pub(crate) fn check_public_key(v1: &Value, v2: &Value) -> Result<bool> {
        let pk: PublicKey = v1.typed().try_into()?;
        let sk: SecretKey = v2.typed().try_into()?;
        Ok(sk.0 < *GROUP_ORDER && pk == sk.public_key())
    }

    pub(crate) fn check_signed_by(msg: &Value, pk: &Value, sig: &Signature) -> Result<bool> {
        let pk: PublicKey = pk.typed().try_into()?;
        Ok(sig.verify(pk, msg.raw()))
    }

    /// Checks the given operation against a statement.
    pub fn check(&self, params: &Params, output_statement: &Statement) -> Result<bool> {
        use Statement::*;
        let deduction_err = || Error::invalid_deduction(self.clone(), output_statement.clone());
        let val = |v, s| value_from_op(s, v).ok_or_else(deduction_err);
        let int_val = |v, s| {
            let v_op = value_from_op(s, v).ok_or_else(deduction_err)?;
            match v_op.typed() {
                &TypedValue::Int(i) => Ok(i),
                _ => Err(deduction_err()),
            }
        };
        let b = match (self, output_statement) {
            (Self::None, None) => true,
            (Self::CopyStatement(s1), s2) => s1 == s2,
            (Self::EqualFromEntries(s1, s2), Equal(v3, v4)) => val(v3, s1)? == val(v4, s2)?,
            (Self::NotEqualFromEntries(s1, s2), NotEqual(v3, v4)) => val(v3, s1)? != val(v4, s2)?,
            (Self::LtEqFromEntries(s1, s2), LtEq(v3, v4)) => int_val(v3, s1)? <= int_val(v4, s2)?,
            (Self::LtFromEntries(s1, s2), Lt(v3, v4)) => int_val(v3, s1)? < int_val(v4, s2)?,
            (
                Self::ContainsFromEntries(root_s, key_s, val_s, pf),
                Contains(root_v, key_v, val_v),
            ) => {
                let root = val(root_v, root_s)?;
                let key = val(key_v, key_s)?;
                let value = val(val_v, val_s)?;
                MerkleTree::verify(root.raw().into(), pf, &key.raw(), &value.raw())?;
                true
            }
            (Self::NotContainsFromEntries(root_s, key_s, pf), NotContains(root_v, key_v)) => {
                let root = val(root_v, root_s)?;
                let key = val(key_v, key_s)?;
                MerkleTree::verify_nonexistence(root.raw().into(), pf, &key.raw())?;
                true
            }
            (
                Self::TransitiveEqualFromStatements(Equal(ak1, ak2), Equal(ak3, ak4)),
                Equal(ak5, ak6),
            ) => ak2 == ak3 && ak5 == ak1 && ak6 == ak4,
            (Self::LtToNotEqual(Lt(ak1, ak2)), NotEqual(ak3, ak4)) => ak1 == ak3 && ak2 == ak4,
            (Self::SumOf(s1, s2, s3), SumOf(v4, v5, v6)) => {
                Self::check_int_fn(&val(v4, s1)?, &val(v5, s2)?, &val(v6, s3)?, sum_op)?
            }
            (Self::ProductOf(s1, s2, s3), ProductOf(v4, v5, v6)) => {
                Self::check_int_fn(&val(v4, s1)?, &val(v5, s2)?, &val(v6, s3)?, prod_op)?
            }
            (Self::MaxOf(s1, s2, s3), MaxOf(v4, v5, v6)) => {
                Self::check_int_fn(&val(v4, s1)?, &val(v5, s2)?, &val(v6, s3)?, max_op)?
            }
            (Self::HashOf(s1, s2, s3), HashOf(v4, v5, v6)) => {
                val(v4, s1)? == hash_op(val(v5, s2)?, val(v6, s3)?)
            }
            (Self::PublicKeyOf(s1, s2), PublicKeyOf(v3, v4)) => {
                Self::check_public_key(&val(v3, s1)?, &val(v4, s2)?)?
            }
            (Self::SignedBy(msg_s, pk_s, sig), SignedBy(msg_v, pk_v)) => {
                Self::check_signed_by(&val(msg_v, msg_s)?, &val(pk_v, pk_s)?, sig)?
            }
            (
                Self::ContainerInsertFromEntries(new_root_s, old_root_s, key_s, val_s, pf),
                ContainerInsert(new_root_v, old_root_v, key_v, val_v),
            ) => {
                let old_root = val(old_root_v, old_root_s)?;
                let new_root = val(new_root_v, new_root_s)?;
                let key = val(key_v, key_s)?;
                let value = val(val_v, val_s)?;
                (pf.op == MerkleTreeOp::Insert
                    && Value::from(pf.old_root) == old_root
                    && Value::from(pf.new_root) == new_root
                    && pf.op_key == key.raw()
                    && pf.op_value == value.raw())
                .then_some(())
                .ok_or(Error::custom(
                    "The provided Merkle tree state transition proof does not match the claim."
                        .into(),
                ))?;
                MerkleTree::verify_state_transition(pf)?;
                true
            }
            (
                Self::ContainerUpdateFromEntries(new_root_s, old_root_s, key_s, val_s, pf),
                ContainerUpdate(new_root_v, old_root_v, key_v, val_v),
            ) => {
                let old_root = val(old_root_v, old_root_s)?;
                let new_root = val(new_root_v, new_root_s)?;
                let key = val(key_v, key_s)?;
                let value = val(val_v, val_s)?;
                (pf.op == MerkleTreeOp::Update
                    && Value::from(pf.old_root) == old_root
                    && Value::from(pf.new_root) == new_root
                    && pf.op_key == key.raw()
                    && pf.op_value == value.raw())
                .then_some(())
                .ok_or(Error::custom(
                    "The provided Merkle tree state transition proof does not match the claim."
                        .into(),
                ))?;
                MerkleTree::verify_state_transition(pf)?;
                true
            }
            (
                Self::ContainerDeleteFromEntries(new_root_s, old_root_s, key_s, pf),
                ContainerDelete(new_root_v, old_root_v, key_v),
            ) => {
                let old_root = val(old_root_v, old_root_s)?;
                let new_root = val(new_root_v, new_root_s)?;
                let key = val(key_v, key_s)?;
                (pf.op == MerkleTreeOp::Delete
                    && Value::from(pf.old_root) == old_root
                    && Value::from(pf.new_root) == new_root
                    && pf.op_key == key.raw())
                .then_some(())
                .ok_or(Error::custom(
                    "The provided Merkle tree state transition proof does not match the claim."
                        .into(),
                ))?;
                MerkleTree::verify_state_transition(pf)?;
                true
            }
            (Self::Custom(CustomPredicateRef { batch, index }, args), Custom(cpr, s_args))
                if batch == &cpr.batch && index == &cpr.index =>
            {
                check_custom_pred(params, cpr, args, s_args).map(|_| true)?
            }
            _ => return Err(deduction_err()),
        };
        Ok(b)
    }
}

// Check that the value `v` at wildcard `wc` exists in the map or set it.
fn wc_check_or_set(v: Value, wc: &Wildcard, wildcard_map: &mut [Option<Value>]) -> Result<()> {
    if let Some(prev) = &wildcard_map[wc.index] {
        if *prev != v {
            return Err(Error::invalid_wildcard_assignment(
                wc.clone(),
                v,
                prev.clone(),
            ));
        }
    } else {
        wildcard_map[wc.index] = Some(v);
    }
    Ok(())
}

/// Check that a StatementArg follows a StatementTmplArg based on the currently mapped wildcards.
/// Update the wildcard map with newly found wildcards.
pub fn check_st_tmpl(
    st_tmpl_arg: &StatementTmplArg,
    st_arg: &StatementArg,
    // Map from wildcards to values that we have seen so far.
    wildcard_map: &mut [Option<Value>],
) -> Result<()> {
    match (st_tmpl_arg, st_arg) {
        (StatementTmplArg::None, StatementArg::None) => Ok(()),
        (StatementTmplArg::Literal(lhs), StatementArg::Literal(rhs)) if lhs == rhs => Ok(()),
        (
            StatementTmplArg::AnchoredKey(root_wc, key_tmpl),
            StatementArg::Key(AnchoredKey { root, key }),
        ) => {
            let root_ok = wc_check_or_set(Value::from(*root), root_wc, wildcard_map);
            root_ok.and_then(|_| {
                (key_tmpl == key).then_some(()).ok_or(
                    Error::mismatched_anchored_key_in_statement_tmpl_arg(
                        root_wc.clone(),
                        *root,
                        key_tmpl.clone(),
                        key.clone(),
                    ),
                )
            })
        }
        (StatementTmplArg::Wildcard(wc), StatementArg::Literal(v)) => {
            wc_check_or_set(v.clone(), wc, wildcard_map)
        }
        _ => Err(Error::mismatched_statement_tmpl_arg(
            st_tmpl_arg.clone(),
            st_arg.clone(),
        )),
    }
}

pub fn fill_wildcard_values(
    params: &Params,
    pred: &CustomPredicate,
    args: &[Statement],
    wildcard_map: &mut [Option<Value>],
) -> Result<()> {
    for (st_tmpl, st) in pred.statements.iter().zip(args) {
        let st_args = st.args();
        if let PredicateOrWildcard::Wildcard(wc) = &st_tmpl.pred_or_wc {
            wc_check_or_set(Value::from(st.predicate().hash(params)), wc, wildcard_map)?;
        }
        st_tmpl
            .args
            .iter()
            .zip(&st_args)
            .try_for_each(|(st_tmpl_arg, st_arg)| {
                check_st_tmpl(st_tmpl_arg, st_arg, wildcard_map)
            })?;
    }
    Ok(())
}

pub fn wildcard_values_from_op_st(
    params: &Params,
    pred: &CustomPredicate,
    op_args: &[Statement],
    st_args: &[Value],
) -> Result<Vec<Value>> {
    let mut wildcard_map = st_args
        .iter()
        .map(|v| Some(v.clone()))
        .chain(core::iter::repeat(None))
        .take(params.max_custom_predicate_wildcards)
        .collect_vec();
    fill_wildcard_values(params, pred, op_args, &mut wildcard_map)?;
    // NOTE: We set unresolved wildcard slots with an empty value.  They can be unresolved because
    // they are beyond the number of used wildcards in this custom predicate, or they could be
    // private arguments that are unused in a particular disjunction.
    Ok(wildcard_map
        .into_iter()
        .map(|opt| opt.unwrap_or(Value::from(0)))
        .collect())
}

fn check_custom_pred_argument(
    params: &Params,
    custom_pred_ref: &CustomPredicateRef,
    template: &StatementTmpl,
    statement: &Statement,
    wc_values: &[Value],
) -> Result<()> {
    match &template.pred_or_wc {
        PredicateOrWildcard::Predicate(pred) => {
            let template_pred = match pred {
                &Predicate::BatchSelf(i) => Predicate::Custom(CustomPredicateRef {
                    batch: custom_pred_ref.batch.clone(),
                    index: i,
                }),
                p => p.clone(),
            };
            if template_pred != statement.predicate() {
                return Err(Error::mismatched_statement_type(
                    template_pred,
                    statement.predicate(),
                ));
            }
        }
        PredicateOrWildcard::Wildcard(wc) => {
            let pred_hash = Value::from(statement.predicate().hash(params));
            if wc_values[wc.index] != pred_hash {
                return Err(Error::mismatched_statement_wc_pred(
                    wc_values[wc.index].clone(),
                    pred_hash,
                    statement.predicate(),
                ));
            }
        }
    }
    let st_args_len = statement.args().len();
    if template.args.len() != st_args_len {
        return Err(Error::diff_amount(
            "statement template in custom predicate".to_string(),
            "arguments".to_string(),
            st_args_len,
            template.args.len(),
        ));
    }
    Ok(())
}

pub(crate) fn check_custom_pred(
    params: &Params,
    custom_pred_ref: &CustomPredicateRef,
    args: &[Statement],
    s_args: &[Value],
) -> Result<()> {
    let pred = custom_pred_ref.predicate();
    if pred.statements.len() != args.len() {
        return Err(Error::diff_amount(
            "custom predicate operation".to_string(),
            "statements".to_string(),
            pred.statements.len(),
            args.len(),
        ));
    }
    if pred.args_len != s_args.len() {
        return Err(Error::diff_amount(
            "custom predicate statement".to_string(),
            "args".to_string(),
            pred.args_len,
            s_args.len(),
        ));
    }

    // Check that the resolved wildcards match the statement arguments.
    let wc_values = match wildcard_values_from_op_st(params, pred, args, s_args) {
        Ok(wc_values) => wc_values,
        Err(Error::Inner { inner, backtrace }) => match *inner {
            MiddlewareInnerError::InvalidWildcardAssignment(wc, v, prev)
                if wc.index <= s_args.len() =>
            {
                return Err(Error::mismatched_wildcard_value_and_statement_arg(
                    v,
                    prev,
                    wc.index,
                    pred.clone(),
                ))
            }
            _ => return Err(Error::Inner { inner, backtrace }),
        },
        _ => unreachable!(),
    };

    let mut match_exists = false;
    for (st_tmpl, st) in pred.statements.iter().zip(args) {
        // For `or` predicates, only one statement needs to match the template.
        // The rest of the statements can be `None`.
        let expected_pred_is_none = match &st_tmpl.pred_or_wc {
            PredicateOrWildcard::Predicate(st_tmpl_pred) => {
                *st_tmpl_pred == Predicate::Native(NativePredicate::None)
            }
            PredicateOrWildcard::Wildcard(wc) => {
                wc_values[wc.index]
                    == Value::from(Predicate::Native(NativePredicate::None).hash(params))
            }
        };
        if !pred.conjunction && matches!(st, Statement::None) && !expected_pred_is_none {
            continue;
        }
        check_custom_pred_argument(params, custom_pred_ref, st_tmpl, st, &wc_values)?;
        match_exists = true;
    }

    if !pred.conjunction && !match_exists {
        return Err(Error::unsatisfied_custom_predicate_disjunction(
            pred.clone(),
        ));
    }
    Ok(())
}

impl ToFields for Operation {
    fn to_fields(&self, _params: &Params) -> Vec<F> {
        todo!()
    }
}

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "middleware::Operation:")?;
        writeln!(f, "  {:?} ", self.op_type())?;
        for arg in self.args().iter() {
            writeln!(f, "    {}", arg)?;
        }
        Ok(())
    }
}

pub(crate) fn root_key_to_ak(root: &Value, key: &Value) -> Option<AnchoredKey> {
    let root_hash = Hash::from(root.raw());
    Key::try_from(key.typed())
        .map(|key| AnchoredKey::new(root_hash, key))
        .ok()
}

/// Returns the value associated with `output_ref`.
/// If `output_ref` is a concrete value, returns that value.
/// Otherwise, `output_ref` was constructed using a `Contains` statement, and `input_st`
/// must be that statement.
pub(crate) fn value_from_op(input_st: &Statement, output_ref: &ValueRef) -> Option<Value> {
    match (input_st, output_ref) {
        (Statement::None, ValueRef::Literal(v)) => Some(v.clone()),
        (
            Statement::Contains(
                ValueRef::Literal(root),
                ValueRef::Literal(key),
                ValueRef::Literal(v),
            ),
            ValueRef::Key(out_ak),
        ) => root_key_to_ak(root, key).and_then(|ak| (*out_ak == ak).then(|| v.clone())),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use num::BigUint;

    use crate::{
        backends::plonky2::{
            primitives::{
                ec::{curve::GROUP_ORDER, schnorr::SecretKey},
                merkletree::MerkleTree,
            },
            signer::Signer,
        },
        middleware::{hash_value, Error, Operation, Params, Result, Signer as _, Statement, Value},
    };

    #[test]
    fn check_container_ops() -> Result<()> {
        let params = Params::default();
        // Form Merkle tree
        let kvs = (0..10)
            .map(|i| (hash_value(&i.into()).into(), i.into()))
            .collect::<HashMap<_, _>>();
        let mt = MerkleTree::new(&kvs);
        let root = mt.root();

        // Check existence proofs
        kvs.iter().try_for_each(|(k, v)| {
            let (_, pf) = mt.prove(k)?;

            // Form op
            let op = Operation::ContainsFromEntries(
                Statement::None,
                Statement::None,
                Statement::None,
                pf,
            );
            // Form output statement
            let st = Statement::Contains(root.into(), (*k).into(), (*v).into());

            // Check op against output statement
            op.check(&params, &st).and_then(|ind| {
                if ind {
                    Ok(())
                } else {
                    Err(Error::custom(format!(
                        "ContainedFromEntries check failed for pair ({},{})",
                        k, v
                    )))
                }
            })
        })?;

        // Check non-existence proofs similarly
        (50..60).try_for_each(|k| {
            let pf = mt.prove_nonexistence(&k.into())?;

            let op = Operation::NotContainsFromEntries(Statement::None, Statement::None, pf);
            let st = Statement::NotContains(root.into(), k.into());

            op.check(&params, &st).and_then(|ind| {
                if ind {
                    Ok(())
                } else {
                    Err(Error::custom(format!(
                        "NotContainedFromEntries check failed for key {}",
                        k
                    )))
                }
            })
        })
    }

    #[test]
    fn check_container_update_ops() -> Result<()> {
        let params = Params::default();

        // Form Merkle tree
        let kvs = (0..10)
            .map(|i| (hash_value(&i.into()).into(), i.into()))
            .collect::<HashMap<_, _>>();
        let mut mt = MerkleTree::new(&kvs);

        // Check insertion proofs
        (11..20)
            .map(|i| (hash_value(&i.into()).into(), i.into()))
            .try_for_each(|(k, v)| {
                let old_root = mt.root();
                let mtp = mt.insert(&k, &v)?;
                let new_root = mt.root();

                // Form op
                let op = Operation::ContainerInsertFromEntries(
                    Statement::None,
                    Statement::None,
                    Statement::None,
                    Statement::None,
                    mtp,
                );
                // Form output statement
                let st = Statement::ContainerInsert(
                    new_root.into(),
                    old_root.into(),
                    k.into(),
                    v.into(),
                );

                // Check op against output statement
                op.check(&params, &st).and_then(|ind| {
                    if ind {
                        Ok(())
                    } else {
                        Err(Error::custom(format!(
                            "Insertion op check failed for pair ({},{})",
                            k, v
                        )))
                    }
                })
            })?;

        // Check update proofs
        (11..20)
            .map(|i| (hash_value(&i.into()).into(), (i + 1).into()))
            .try_for_each(|(k, v)| {
                let old_root = mt.root();
                let mtp = mt.update(&k, &v)?;
                let new_root = mt.root();

                // Form op
                let op = Operation::ContainerUpdateFromEntries(
                    Statement::None,
                    Statement::None,
                    Statement::None,
                    Statement::None,
                    mtp,
                );
                // Form output statement
                let st = Statement::ContainerUpdate(
                    new_root.into(),
                    old_root.into(),
                    k.into(),
                    v.into(),
                );

                // Check op against output statement
                op.check(&params, &st).and_then(|ind| {
                    if ind {
                        Ok(())
                    } else {
                        Err(Error::custom(format!(
                            "Update op check failed for pair ({},{})",
                            k, v
                        )))
                    }
                })
            })?;

        // Check deletion proofs
        (11..20)
            .map(|i| hash_value(&i.into()).into())
            .try_for_each(|k| {
                let old_root = mt.root();
                let mtp = mt.delete(&k)?;
                let new_root = mt.root();

                // Form op
                let op = Operation::ContainerDeleteFromEntries(
                    Statement::None,
                    Statement::None,
                    Statement::None,
                    mtp,
                );
                // Form output statement
                let st = Statement::ContainerDelete(new_root.into(), old_root.into(), k.into());

                // Check op against output statement
                op.check(&params, &st).and_then(|ind| {
                    if ind {
                        Ok(())
                    } else {
                        Err(Error::custom(format!(
                            "Deletion op check failed for key {}",
                            k
                        )))
                    }
                })
            })
    }

    #[test]
    fn check_public_key_of_op() -> Result<()> {
        let fixed_sk = SecretKey(BigUint::from(0x1234567890abcdefu64));
        let fixed_pk = fixed_sk.public_key();
        let rand_sk = SecretKey::new_rand();
        let rand_pk = rand_sk.public_key();
        let small_sk = SecretKey(BigUint::from(0x1u32));
        let small_pk = small_sk.public_key();
        let too_large_sk = SecretKey(small_sk.0.clone() + GROUP_ORDER.clone());
        assert_eq!(small_pk, too_large_sk.public_key());

        let test_cases = [
            // Valid pairs
            (fixed_pk, fixed_sk.clone(), true),
            (rand_pk, rand_sk.clone(), true),
            // Mismatched pairs
            (fixed_pk, rand_sk.clone(), false),
            (rand_pk, fixed_sk.clone(), false),
            // Above group order
            (small_pk, small_sk.clone(), true),
            (small_pk, too_large_sk.clone(), false),
        ];

        let params = Params::default();

        test_cases.iter().try_for_each(|(pk, sk, expect_good)| {
            // Form op
            let op = Operation::PublicKeyOf(Statement::None, Statement::None);

            // Form output statement
            let st = Statement::PublicKeyOf((*pk).into(), sk.clone().into());

            // Check
            op.check(&params, &st).map(|is_good| {
                assert_eq!(
                    is_good, *expect_good,
                    "PublicKeyOf({}, {}) => {}",
                    pk, sk, is_good
                );
            })
        })
    }

    #[test]
    fn check_public_key_of_op_arg_types() -> Result<()> {
        let fixed_sk = SecretKey(BigUint::from(0x1234567890abcdefu64));
        let fixed_pk = fixed_sk.public_key();

        let params = Params::default();

        // Bad op and statement with bad first args
        let op = Operation::PublicKeyOf(Statement::None, Statement::None);
        let st = Statement::PublicKeyOf(fixed_pk.into(), fixed_pk.into());

        // Check
        assert!(op.check(&params, &st).is_err());

        // Bad op and statement with bad second args
        let op = Operation::PublicKeyOf(Statement::None, Statement::None);
        let st = Statement::PublicKeyOf(fixed_sk.clone().into(), fixed_sk.clone().into());

        // Check
        assert!(op.check(&params, &st).is_err());

        Ok(())
    }

    #[test]
    fn check_signed_by_op() -> Result<()> {
        let params = Params::default();

        let sk = SecretKey(BigUint::from(0x1234567890abcdefu64));
        let pk = sk.public_key();
        let msg = Value::from("hello");
        let sig = Signer(sk).sign(msg.raw());

        let op = Operation::SignedBy(Statement::None, Statement::None, sig);
        let st = Statement::SignedBy(msg.into(), pk.into());
        op.check(&params, &st)?;

        Ok(())
    }
}
