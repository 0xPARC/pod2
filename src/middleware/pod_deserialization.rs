use std::{
    collections::HashMap,
    sync::{LazyLock, Mutex},
};

use crate::middleware::{
    BackendResult, Error, Hash, Params, Pod, PodId, PodType, RecursivePod, Result,
};

type DeserializeFn = fn(
    params: Params,
    id: PodId,
    vds_root: Hash,
    data: serde_json::Value,
) -> BackendResult<Box<dyn RecursivePod>>;

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
    vds_root: Hash,
    data: serde_json::Value,
) -> Result<Box<dyn RecursivePod>> {
    let deserialize_fn: DeserializeFn =
        *DESERIALIZERS
            .lock()
            .unwrap()
            .get(&pod_type)
            .ok_or(Error::custom(format!(
                "pod deserializer for pod_type={} not registered.  See https://github.com/0xPARC/pod2/wiki/PodType for pod type assignments.",
                pod_type
            )))?;

    deserialize_fn(params, id, vds_root, data)
        .map_err(|e| Error::custom(format!("deserialize error: {:?}", e)))
}

pub fn deserialize_signed_pod(
    pod_type: usize,
    id: PodId,
    data: serde_json::Value,
) -> Result<Box<dyn Pod>> {
    backend::deserialize_signed_pod(pod_type, id, data)
}

#[cfg(feature = "backend_plonky2")]
mod backend {
    use super::*;
    use crate::backends::plonky2::{
        emptypod::EmptyPod,
        mainpod::MainPod,
        mock::{emptypod::MockEmptyPod, mainpod::MockMainPod, signedpod::MockSignedPod},
        signedpod::SignedPod,
    };

    pub(super) fn deserializers_default() -> Mutex<HashMap<usize, DeserializeFn>> {
        let mut map: HashMap<usize, DeserializeFn> = HashMap::new();
        map.insert(PodType::Empty as usize, EmptyPod::deserialize);
        map.insert(PodType::Main as usize, MainPod::deserialize);
        map.insert(PodType::MockEmpty as usize, MockEmptyPod::deserialize);
        map.insert(PodType::MockMain as usize, MockMainPod::deserialize);
        Mutex::new(map)
    }

    pub(super) fn deserialize_signed_pod(
        pod_type: usize,
        id: PodId,
        data: serde_json::Value,
    ) -> Result<Box<dyn Pod>> {
        if pod_type == PodType::MockSigned as usize {
            MockSignedPod::deserialize(id, data)
                .map_err(|e| Error::custom(format!("deserialize error: {:?}", e)))
        } else if pod_type == PodType::Signed as usize {
            SignedPod::deserialize(id, data)
                .map_err(|e| Error::custom(format!("deserialize error: {:?}", e)))
        } else {
            Err(Error::custom(format!(
                "unexpected pod_type={} for deserialize_signed_pod",
                pod_type
            )))
        }
    }
}
