use std::{
    collections::HashMap,
    sync::{LazyLock, Mutex},
};

use crate::middleware::{BackendError, Params, Pod, PodId, PodType, RecursivePod, Result, VDSet};

type DeserializeFn = fn(
    params: Params,
    data: serde_json::Value,
    vd_set: VDSet,
    id: PodId,
) -> Result<Box<dyn RecursivePod>, BackendError>;

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
    id: PodId,
    vd_set: VDSet,
    data: serde_json::Value,
) -> Result<Box<dyn RecursivePod>, BackendError> {
    let deserialize_fn: DeserializeFn =
        *DESERIALIZERS
            .lock()
            .unwrap()
            .get(&pod_type)
            .ok_or(BackendError::custom(format!(
                "pod deserializer for pod_type={} not registered.  See https://github.com/0xPARC/pod2/wiki/PodType for pod type assignments.",
                pod_type
            )))?;

    deserialize_fn(params, data, vd_set, id)
}

pub fn deserialize_signed_pod(
    pod_type: usize,
    id: PodId,
    data: serde_json::Value,
) -> Result<Box<dyn Pod>, BackendError> {
    backend::deserialize_signed_pod(pod_type, id, data)
}

#[cfg(feature = "backend_plonky2")]
mod backend {
    use super::*;
    use crate::backends::plonky2::{
        emptypod::EmptyPod,
        mainpod::MainPod,
        mock::{emptypod::MockEmptyPod, mainpod::MockMainPod},
        signedpod::SignedPod,
    };

    pub(super) fn deserializers_default() -> Mutex<HashMap<usize, DeserializeFn>> {
        let mut map: HashMap<usize, DeserializeFn> = HashMap::new();
        map.insert(PodType::Empty as usize, EmptyPod::deserialize_data);
        map.insert(PodType::Main as usize, MainPod::deserialize_data);
        map.insert(PodType::MockEmpty as usize, MockEmptyPod::deserialize_data);
        map.insert(PodType::MockMain as usize, MockMainPod::deserialize_data);
        Mutex::new(map)
    }

    pub(super) fn deserialize_signed_pod(
        pod_type: usize,
        id: PodId,
        data: serde_json::Value,
    ) -> Result<Box<dyn Pod>, BackendError> {
        if pod_type == PodType::Signed as usize {
            SignedPod::deserialize(id, data)
        } else {
            Err(BackendError::custom(format!(
                "unexpected pod_type={} for deserialize_signed_pod",
                pod_type
            )))
        }
    }
}
