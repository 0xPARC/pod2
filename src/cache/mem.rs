use std::{
    any::Any,
    collections::HashMap,
    ops::Deref,
    sync::{LazyLock, Mutex},
    thread, time,
};

use serde::{de::DeserializeOwned, Serialize};
use sha2::{Digest, Sha256};

#[allow(clippy::type_complexity)]
static CACHE: LazyLock<Mutex<HashMap<String, Option<&'static (dyn Any + Sync)>>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

pub struct CacheEntry<T: 'static> {
    value: &'static T,
}

impl<T> Deref for CacheEntry<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.value
    }
}

/// Get the artifact named `name` from the memory cache.  If it doesn't exist, it will be built by
/// calling `build_fn` and stored.
/// The artifact is indexed by `params: P`.
pub fn get<T: Serialize + DeserializeOwned + Sync + 'static, P: Serialize>(
    name: &str,
    params: &P,
    build_fn: fn(&P) -> T,
) -> Result<CacheEntry<T>, Box<dyn std::error::Error>> {
    let params_json = serde_json::to_string(params)?;
    let params_json_hash = Sha256::digest(&params_json);
    let params_json_hash_str_long = format!("{:x}", params_json_hash);
    let key = format!("{}/{}", &params_json_hash_str_long[..32], name);
    log::debug!("getting {} from the mem cache", name);

    loop {
        let mut cache = CACHE.lock()?;
        if let Some(entry) = cache.get(&key) {
            if let Some(boxed_data) = entry {
                if let Some(data) = (*boxed_data as &dyn Any).downcast_ref::<T>() {
                    log::debug!("found {} in the mem cache", name);
                    return Ok(CacheEntry { value: data });
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
        log::info!("building {} and storing to the mem cache", name);
        let start = std::time::Instant::now();
        let data = build_fn(params);
        let elapsed = std::time::Instant::now() - start;
        log::debug!("built {} in {:?}", name, elapsed);

        CACHE.lock()?.insert(key, Some(Box::leak(Box::new(data))));
        // Call `get` again and this time we'll retrieve the data from the cache
        return get(name, params, build_fn);
    }
}
