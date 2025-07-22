use std::{
    any::Any,
    collections::HashMap,
    sync::{LazyLock, Mutex},
    thread, time,
};

use serde::{de::DeserializeOwned, Serialize};
use sha2::{Digest, Sha256};

static CACHE: LazyLock<Mutex<HashMap<String, Option<Box<dyn Any + Send + 'static>>>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

/// Get the artifact named `name` from the memory cache.  If it doesn't exist, it will be built by
/// calling `build_fn` and stored.
/// The artifact is indexed by `params: P`.
pub(crate) fn get<T: Serialize + DeserializeOwned + Clone + Send + 'static, P: Serialize>(
    name: &str,
    params: &P,
    build_fn: fn(&P) -> T,
) -> Result<T, Box<dyn std::error::Error>> {
    let params_json = serde_json::to_string(params)?;
    let params_json_hash = Sha256::digest(&params_json);
    let params_json_hash_str_long = format!("{:x}", params_json_hash);
    let key = format!("{}/{}", &params_json_hash_str_long[..32], name);

    loop {
        let mut cache = CACHE.lock()?;
        if let Some(entry) = cache.get(&key) {
            if let Some(boxed_data) = entry {
                if let Some(data) = boxed_data.downcast_ref::<T>() {
                    return Ok(data.clone());
                } else {
                    panic!(
                        "type={} doesn't match the type in the cached boxed value with name={}",
                        std::any::type_name::<T>(),
                        name
                    );
                }
            } else {
                // Another thread is building this entry, let's retry again in 100 ms
                drop(cache); // release the lock
                thread::sleep(time::Duration::from_millis(100));
                continue;
            }
        }
        // No entry in the cache, let's put a `None` to signal that we're building the
        // artifact, release the lock, build the artifact and insert it.  We do this to avoid
        // locking for a long time.
        cache.insert(key.clone(), None);
        drop(cache); // release the lock
        let data = build_fn(params);
        CACHE.lock()?.insert(key, Some(Box::new(data.clone())));
        return Ok(data);
    }
}
