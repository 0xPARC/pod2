//! This file exposes the basetypes to be used in the middleware when the `backend_plonky2` feature
//! is enabled.
//! See src/middleware/basetypes.rs for more details.

/// F is the native field we use everywhere.  Currently it's Goldilocks from plonky2
pub use plonky2::field::goldilocks_field::GoldilocksField as F;
use plonky2::{
    field::extension::quadratic::QuadraticExtension,
    hash::{hash_types, poseidon::PoseidonHash},
    plonk::{circuit_builder, circuit_data, config::GenericConfig, proof},
};
use schemars::JsonSchema;
use serde::{Deserialize, Deserializer, Serialize};

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
pub type HashOut = hash_types::HashOut<F>;

use std::{collections::HashMap, sync::LazyLock};

use crate::{
    backends::plonky2::{
        emptypod::STANDARD_EMPTY_POD_DATA, primitives::merkletree::MerkleClaimAndProof,
        DEFAULT_PARAMS, STANDARD_REC_MAIN_POD_CIRCUIT_DATA,
    },
    middleware::{containers::Array, Hash, RawValue, Result, Value},
};

pub static DEFAULT_VD_SET: LazyLock<VDSet> = LazyLock::new(|| {
    let params = &*DEFAULT_PARAMS;

    let vds = vec![
        STANDARD_REC_MAIN_POD_CIRCUIT_DATA.verifier_only.clone(),
        STANDARD_EMPTY_POD_DATA.1.verifier_only.clone(),
    ];
    VDSet::new(params.max_depth_mt_vds, &vds).unwrap()
});

/// VDSet is the set of the allowed verifier_data hashes. When proving a
/// MainPod, the circuit will enforce that all the used verifier_datas for
/// verifying the recursive proofs of previous PODs appears in the VDSet.
/// The VDSet struct that allows to get the specific merkle proofs for the given
/// verifier_data.
#[derive(Clone, Debug, Serialize, JsonSchema)]
pub struct VDSet {
    #[serde(skip)]
    #[schemars(skip)]
    root: Hash,
    // (verifier_data's hash, merkleproof)
    #[serde(skip)]
    #[schemars(skip)]
    proofs_map: HashMap<Hash, MerkleClaimAndProof>,
    tree_depth: usize,
    vds_hashes: Vec<Hash>,
}

impl PartialEq for VDSet {
    fn eq(&self, other: &Self) -> bool {
        self.root == other.root
            && self.tree_depth == other.tree_depth
            && self.vds_hashes == other.vds_hashes
    }
}
impl Eq for VDSet {}

impl VDSet {
    fn new_from_vds_hashes(tree_depth: usize, mut vds_hashes: Vec<Hash>) -> Result<Self> {
        // before using the hash values, sort them, so that each set of
        // verifier_datas gets the same VDSet root
        vds_hashes.sort();

        let array = Array::new(
            tree_depth,
            vds_hashes.iter().map(|vd| Value::from(*vd)).collect(),
        )?;

        let root = array.commitment();
        let mut proofs_map = HashMap::<Hash, MerkleClaimAndProof>::new();

        for (i, vd) in vds_hashes.iter().enumerate() {
            let (value, proof) = array.prove(i)?;
            let p = MerkleClaimAndProof {
                root,
                key: RawValue::from(i as i64),
                value: value.raw(),
                proof,
            };
            proofs_map.insert(*vd, p);
        }
        Ok(Self {
            root,
            proofs_map,
            tree_depth,
            vds_hashes,
        })
    }
    /// builds the verifier_datas tree, and returns the root and the proofs
    pub fn new(tree_depth: usize, vds: &[VerifierOnlyCircuitData]) -> Result<Self> {
        // compute the verifier_data's hashes
        let vds_hashes: Vec<HashOut> = vds
            .iter()
            .map(crate::backends::plonky2::recursion::circuit::hash_verifier_data)
            .collect::<Vec<_>>();

        let vds_hashes: Vec<Hash> = vds_hashes
            .into_iter()
            .map(|h| Hash(h.elements))
            .collect::<Vec<_>>();

        Self::new_from_vds_hashes(tree_depth, vds_hashes)
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
            let verifier_data_hash =
                crate::backends::plonky2::recursion::circuit::hash_verifier_data(vd);
            let p = self
                .proofs_map
                .get(&Hash(verifier_data_hash.elements))
                .ok_or(crate::middleware::Error::custom(
                    "verifier_data not found in VDSet".to_string(),
                ))?;
            proofs.push(p.clone());
        }
        Ok(proofs)
    }
    /// Returns true if the `verifier_data_hash` is in the set
    pub fn contains(&self, verifier_data_hash: HashOut) -> bool {
        self.proofs_map
            .contains_key(&Hash(verifier_data_hash.elements))
    }
}

impl<'de> Deserialize<'de> for VDSet {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct Aux {
            tree_depth: usize,
            vds_hashes: Vec<Hash>,
        }
        let aux = Aux::deserialize(deserializer)?;
        VDSet::new_from_vds_hashes(aux.tree_depth, aux.vds_hashes).map_err(serde::de::Error::custom)
    }
}
