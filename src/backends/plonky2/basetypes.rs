//! This file exposes the basetypes to be used in the middleware when the `backend_plonky2` feature
//! is enabled.
//! See src/middleware/basetypes.rs for more details.

use plonky2::{
    field::{extension::quadratic::QuadraticExtension, goldilocks_field::GoldilocksField},
    hash::poseidon::PoseidonHash,
    plonk::{circuit_builder, circuit_data, config::GenericConfig, proof},
};
use serde::Serialize;

/// F is the native field we use everywhere.  Currently it's Goldilocks from plonky2
pub type F = GoldilocksField;

/// D defines the extension degree of the field used in the Plonky2 proofs (quadratic extension).
pub const D: usize = 2;

/// FE is the degree D field extension used in Plonky2 proofs.
pub type FE = QuadraticExtension<F>;

/// C is the Plonky2 config used in POD2 to work with Plonky2 recursion.
#[derive(Debug, Copy, Clone, Default, Eq, PartialEq, Serialize)]
pub struct C;
impl GenericConfig<D> for C {
    type F = F;
    type FE = FE;
    type Hasher = PoseidonHash;
    type InnerHasher = PoseidonHash;
}

pub type CircuitData = circuit_data::CircuitData<F, C, D>;
pub type CommonCircuitData = circuit_data::CommonCircuitData<F, D>;
pub type ProverOnlyCircuitData = circuit_data::ProverOnlyCircuitData<F, C, D>;
pub type VerifierOnlyCircuitData = circuit_data::VerifierOnlyCircuitData<C, D>;
pub type VerifierCircuitData = circuit_data::VerifierCircuitData<F, C, D>;
pub type CircuitBuilder = circuit_builder::CircuitBuilder<F, D>;
pub type Proof = proof::Proof<F, C, D>;
pub type ProofWithPublicInputs = proof::ProofWithPublicInputs<F, C, D>;

// TODO decide where to place struct VDSTree and the DEFAULT_VD_TREE
use std::{collections::HashMap, sync::LazyLock};

use plonky2::hash::hash_types::HashOut;

use crate::{
    backends::plonky2::{
        emptypod::STANDARD_EMPTY_POD_DATA, primitives::merkletree::MerkleClaimAndProof,
        DEFAULT_PARAMS, STANDARD_REC_MAIN_POD_CIRCUIT_DATA,
    },
    middleware::{containers::Array, Hash, RawValue, Result, Value},
};

pub static DEFAULT_VD_TREE: LazyLock<VDTree> = LazyLock::new(|| {
    let params = &*DEFAULT_PARAMS;

    let vds = vec![
        STANDARD_REC_MAIN_POD_CIRCUIT_DATA.verifier_only.clone(),
        STANDARD_EMPTY_POD_DATA.1.verifier_only.clone(),
    ];
    VDTree::new(params.max_depth_mt_vds, &vds).unwrap()
});

// TODO: Note: I've used `containers::Array`, but I think that using the `Set`
// would make. With `Array` we save 1 hash per each verifier_data entry, but
// with `Set` we don't need to keep track of which verifier_data is stored at
// which position, and can just get the merkleproof for the given
// `verifier_data` (without first getting its `i`).
/// Struct that allows to get the specific merkle proofs for the given verifier_data
pub struct VDTree {
    root: Hash,
    proofs_map: HashMap<HashOut<F>, MerkleClaimAndProof>,
}
impl VDTree {
    /// builds the verifier_datas tree, and returns the root and the proofs
    pub fn new(tree_depth: usize, vds: &[VerifierOnlyCircuitData]) -> Result<Self> {
        let array = Array::new_with_depth(
            tree_depth,
            vds.iter()
                .map(|vd| Value::from(RawValue(vd.circuit_digest.elements)))
                .collect(),
        )?;

        let root = array.commitment();
        let mut proofs_map = HashMap::<HashOut<F>, MerkleClaimAndProof>::new();

        for (i, vd) in vds.iter().enumerate() {
            let (value, proof) = array.prove(i)?;
            let p = MerkleClaimAndProof {
                root,
                key: RawValue::from(i as i64),
                value: value.raw(),
                proof,
            };
            proofs_map.insert(vd.circuit_digest, p);
        }
        Ok(Self { root, proofs_map })
    }
    pub fn root(&self) -> Hash {
        self.root
    }
    /// returns the vector of merkle proofs corresponding to the given verifier_datas
    pub fn get_vds_proofs(
        &self,
        vds: &[VerifierOnlyCircuitData],
    ) -> Result<Vec<MerkleClaimAndProof>> {
        let mut proofs: Vec<MerkleClaimAndProof> = vec![];
        for vd in vds {
            let p =
                self.proofs_map
                    .get(&vd.circuit_digest)
                    .ok_or(crate::middleware::Error::custom(
                        "verifier_data not found in VDTree".to_string(),
                    ))?;
            proofs.push(p.clone());
        }
        Ok(proofs)
    }
}
