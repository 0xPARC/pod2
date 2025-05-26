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
        basetypes::{CircuitData, C, D},
        circuits::mainpod::{MainPodVerifyTarget, NUM_PUBLIC_INPUTS},
        recursion::common_data_for_recursion,
    },
    middleware::{Hash, Params, F},
    timed,
};

/// Generic function to build a HashMap cache from a static LazyLock.
pub fn get_or_set_map_cache<K, V>(
    cache: &'static LazyLock<RwLock<HashMap<K, V>>>,
    key: &K,
    try_set_fn: impl Fn(&K) -> Result<V>,
) -> Result<MappedRwLockReadGuard<'static, V>>
where
    K: Clone + std::cmp::Eq + std::hash::Hash,
{
    // Try to read from the hashmap with a readlock.  If the entry doesn't exist, acquire the write
    // lock, create and insert the entry and finally recurse to suceed with the read lock.
    {
        let read_lock = cache.read().unwrap();
        if read_lock.get(key).is_some() {
            return Ok(RwLockReadGuard::map(read_lock, |m| m.get(key).unwrap()));
        }
    }
    {
        let mut write_lock = cache.write().unwrap();
        // After acquiring the write lock, we check again if the data exist so that if another
        // thread raced us here we don't call `try_set_fn` twice.
        if write_lock.get(key).is_none() {
            let data = try_set_fn(key)?;
            write_lock.insert(key.clone(), data);
        }
    }
    get_or_set_map_cache(cache, key, try_set_fn)
}

static RECURSIVE_MAIN_POD_DATA: LazyLock<RwLock<HashMap<Params, CircuitData>>> =
    LazyLock::new(|| RwLock::new(HashMap::new()));

pub fn recursive_main_pod_circuit_data(
    params: &Params,
) -> Result<MappedRwLockReadGuard<CircuitData>> {
    get_or_set_map_cache(&RECURSIVE_MAIN_POD_DATA, params, |params| {
        timed!(
            "common_data_for_recursion",
            common_data_for_recursion::<MainPodVerifyTarget>(
                params.max_input_zk_pods,
                NUM_PUBLIC_INPUTS,
                params
            )
        )
    })
}

pub fn recursive_main_pod_verifier_data_hash(params: &Params) -> Result<Hash> {
    let data = recursive_main_pod_circuit_data(params)?;
    Ok(Hash(data.verifier_only.circuit_digest.elements))
}
