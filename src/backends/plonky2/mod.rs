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

use crate::{
    backends::plonky2::{
        basetypes::CircuitData,
        circuits::mainpod::{MainPodVerifyTarget, NUM_PUBLIC_INPUTS},
        recursion::RecursiveCircuit,
    },
    middleware::{Hash, Params},
    timed,
};

pub static DEFAULT_PARAMS: LazyLock<Params> = LazyLock::new(|| Params::default());

pub static STANDARD_REC_MAIN_POD_CIRCUIT_DATA: LazyLock<CircuitData> = LazyLock::new(|| {
    let params = &*DEFAULT_PARAMS;
    timed!(
        "recursive MainPod circuit_data",
        RecursiveCircuit::<MainPodVerifyTarget>::circuit_data(
            params.max_input_recursive_pods,
            NUM_PUBLIC_INPUTS,
            params
        )
        .expect("calculate circuit_data")
        .1
    )
});

// /// Generic function to build a HashMap cache from a static LazyLock.
// pub fn get_or_set_map_cache<K, V>(
//     name: &str,
//     cache: &'static LazyLock<RwLock<HashMap<K, V>>>,
//     key: &K,
//     set_fn: impl Fn(&K) -> V,
// ) -> MappedRwLockReadGuard<'static, V>
// where
//     K: Clone + std::cmp::Eq + std::hash::Hash,
// {
//     println!("DBG get_or_set_map_cache {}", name);
//     // Try to read from the hashmap with a readlock.  If the entry doesn't exist, acquire the write
//     // lock, create and insert the entry and finally recurse to suceed with the read lock.
//     {
//         let read_lock = cache.read().unwrap();
//         println!("DBG get_or_set_map_cache read locked {}", name);
//         if read_lock.get(key).is_some() {
//             return RwLockReadGuard::map(read_lock, |m| m.get(key).unwrap());
//         }
//         println!("DBG get_or_set_map_cache read unlock {}", name);
//     }
//     {
//         println!("DBG get_or_set_map_cache write before lock {}", name);
//         let mut write_lock = cache.write().unwrap();
//         println!("DBG get_or_set_map_cache write locked {}", name);
//         // After acquiring the write lock, we check again if the data exist so that if another
//         // thread raced us here we don't call `set_fn` twice.
//         if write_lock.get(key).is_none() {
//             let data = set_fn(key);
//             write_lock.insert(key.clone(), data);
//         }
//         println!("DBG get_or_set_map_cache write unlock {}", name);
//     }
//     get_or_set_map_cache(name, cache, key, set_fn)
// }
//
// static RECURSIVE_MAIN_POD_DATA: LazyLock<RwLock<HashMap<Params, CircuitData>>> =
//     LazyLock::new(|| RwLock::new(HashMap::new()));
//
// // TODO: Define a lazy static standard_params that will define the standard recursive main circuit.
// pub fn recursive_main_pod_circuit_data(params: &Params) -> MappedRwLockReadGuard<CircuitData> {
//     get_or_set_map_cache(
//         "recursive_main_pod_circuit_data",
//         &RECURSIVE_MAIN_POD_DATA,
//         params,
//         |params| {
//             timed!(
//                 "recursive MainPod circuit_data",
//                 RecursiveCircuit::<MainPodVerifyTarget>::circuit_data(
//                     params.max_input_recursive_pods,
//                     NUM_PUBLIC_INPUTS,
//                     params
//                 )
//                 .expect("calculate circuit_data")
//                 .1
//             )
//         },
//     )
// }
//
// pub fn recursive_main_pod_verifier_data_hash(params: &Params) -> Hash {
//     let data = recursive_main_pod_circuit_data(params);
//     Hash(data.verifier_only.circuit_digest.elements)
// }
