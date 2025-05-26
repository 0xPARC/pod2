pub mod basetypes;
pub mod circuits;
pub mod emptypod;
mod error;
pub mod mainpod;
pub mod mock;
pub mod primitives;
pub mod recursion;
pub mod signedpod;

use std::{
    collections::HashMap,
    sync::{LazyLock, MappedRwLockReadGuard, RwLock, RwLockReadGuard},
};

pub use error::*;
use plonky2::plonk::{circuit_builder, circuit_data};

use crate::{
    backends::plonky2::{
        basetypes::{CircuitData, Proof, C, D},
        circuits::mainpod::{MainPodVerifyTarget, NUM_PUBLIC_INPUTS},
        mainpod::Statement,
        recursion::common_data_for_recursion,
    },
    middleware::{self, Hash, Params, PodId, F},
    timed,
};

/// Generic function to build a HashMap cache from a static LazyLock.
pub fn get_or_set_map_cache<K, V>(
    cache: &'static LazyLock<RwLock<HashMap<K, V>>>,
    key: &K,
    set_fn: impl Fn(&K) -> V,
) -> MappedRwLockReadGuard<'static, V>
where
    K: Clone + std::cmp::Eq + std::hash::Hash,
{
    // Try to read from the hashmap with a readlock.  If the entry doesn't exist, acquire the write
    // lock, create and insert the entry and finally recurse to suceed with the read lock.
    {
        let read_lock = cache.read().unwrap();
        if read_lock.get(key).is_some() {
            return RwLockReadGuard::map(read_lock, |m| m.get(key).unwrap());
        }
    }
    {
        let mut write_lock = cache.write().unwrap();
        // After acquiring the write lock, we check again if the data exist so that if another
        // thread raced us here we don't call `set_fn` twice.
        if write_lock.get(key).is_none() {
            let data = set_fn(key);
            write_lock.insert(key.clone(), data);
        }
    }
    get_or_set_map_cache(cache, key, set_fn)
}

static RECURSIVE_MAIN_POD_DATA: LazyLock<RwLock<HashMap<Params, CircuitData>>> =
    LazyLock::new(|| RwLock::new(HashMap::new()));

pub fn recursive_main_pod_circuit_data(params: &Params) -> MappedRwLockReadGuard<CircuitData> {
    get_or_set_map_cache(&RECURSIVE_MAIN_POD_DATA, params, |params| {
        timed!(
            "common_data_for_recursion",
            common_data_for_recursion::<MainPodVerifyTarget>(
                params.max_input_recursive_pods,
                NUM_PUBLIC_INPUTS,
                params
            )
            .expect("calculate common_data")
        )
    })
}

pub fn recursive_main_pod_verifier_data_hash(params: &Params) -> Hash {
    let data = recursive_main_pod_circuit_data(params);
    Hash(data.verifier_only.circuit_digest.elements)
}

#[derive(Clone, Debug)]
struct RecursivePodData {
    pub(crate) params: Params,
    pub(crate) id: PodId,
    pub(crate) vds_root: Hash,
    pub(crate) public_statements: Vec<middleware::Statement>,
    pub(crate) proof: Proof,
}
