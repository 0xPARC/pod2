use std::{
    collections::HashMap,
    sync::{LazyLock, Mutex},
};

use crate::middleware::{BackendError, Hash, Params, Pod, PodType, Result, VDSet};

type DeserializeFn = fn(
    params: Params,
    data: serde_json::Value,
    vd_set: VDSet,
    sts_hash: Hash,
) -> Result<Box<dyn Pod>, BackendError>;

static DESERIALIZERS: LazyLock<Mutex<HashMap<usize, DeserializeFn>>> =
    LazyLock::new(backend::deserializers_default);

pub fn register_pod_deserializer(pod_type: usize, deserialize_fn: DeserializeFn) {
    DESERIALIZERS
        .lock()
        .unwrap()
        .insert(pod_type, deserialize_fn);
}

pub fn deserialize_pod(
    pod_type: usize,
    params: Params,
    sts_hash: Hash,
    vd_set: VDSet,
    data: serde_json::Value,
) -> Result<Box<dyn Pod>, BackendError> {
    let deserialize_fn: DeserializeFn =
        *DESERIALIZERS
            .lock()
            .unwrap()
            .get(&pod_type)
            .ok_or(BackendError::custom(format!(
                "pod deserializer for pod_type={} not registered.  See https://github.com/0xPARC/pod2/wiki/PodType for pod type assignments.",
                pod_type
            )))?;

    deserialize_fn(params, data, vd_set, sts_hash)
}

#[cfg(feature = "backend_plonky2")]
mod backend {
    use super::*;
    use crate::backends::plonky2::{
        emptypod::EmptyPod,
        mainpod::MainPod,
        mock::{emptypod::MockEmptyPod, mainpod::MockMainPod},
    };

    pub(super) fn deserializers_default() -> Mutex<HashMap<usize, DeserializeFn>> {
        fn deserialize_data<P: Pod>(
            params: Params,
            data: serde_json::Value,
            vd_set: VDSet,
            sts_hash: Hash,
        ) -> Result<Box<dyn Pod>, BackendError> {
            Ok(Box::new(P::deserialize_data(
                params, data, vd_set, sts_hash,
            )?))
        }

        let mut map: HashMap<usize, DeserializeFn> = HashMap::new();
        map.insert(PodType::Empty as usize, deserialize_data::<EmptyPod>);
        map.insert(PodType::Main as usize, deserialize_data::<MainPod>);
        map.insert(
            PodType::MockEmpty as usize,
            deserialize_data::<MockEmptyPod>,
        );
        map.insert(PodType::MockMain as usize, deserialize_data::<MockMainPod>);
        Mutex::new(map)
    }
}
