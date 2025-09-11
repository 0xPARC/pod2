use std::{
    fs::{create_dir_all, rename, File, TryLockError},
    io::{Error, ErrorKind, Read, Write},
    ops::Deref,
    thread, time,
};

use directories::BaseDirs;
use serde::{de::DeserializeOwned, Serialize};
use sha2::{Digest, Sha256};

pub struct CacheEntry<T> {
    value: T,
}

impl<T> Deref for CacheEntry<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

/// Get the artifact named `name` from the disk cache.  If it doesn't exist, it will be built by
/// calling `build_fn` and stored.
/// The artifact is indexed by git commit first and then by `params: P` second.
pub fn get<T: Serialize + DeserializeOwned, P: Serialize>(
    name: &str,
    params: &P,
    build_fn: fn(&P) -> T,
) -> Result<CacheEntry<T>, Box<dyn std::error::Error>> {
    let commit_hash_str = env!("VERGEN_GIT_SHA");
    let params_json = serde_json::to_string(params)?;
    let params_json_hash = Sha256::digest(&params_json);
    let params_json_hash_str_long = format!("{:x}", params_json_hash);
    let params_json_hash_str = format!("{}", &params_json_hash_str_long[..32]);
    let log_name = format!("{}/{}/{}.cbor", commit_hash_str, params_json_hash_str, name);
    log::debug!("getting {} from the disk cache", log_name);

    let base_dirs =
        BaseDirs::new().ok_or(Error::new(ErrorKind::Other, "no valid home directory"))?;
    let user_cache_dir = base_dirs.cache_dir();
    let pod2_cache_dir = user_cache_dir.join("pod2");
    let commit_cache_dir = pod2_cache_dir.join(&commit_hash_str);
    create_dir_all(&commit_cache_dir)?;

    let cache_dir = commit_cache_dir.join(&params_json_hash_str);
    create_dir_all(&cache_dir)?;

    // Store the params.json if it doesn't exist for better debuggability
    let params_path = cache_dir.join("params.json");
    if !params_path.try_exists()? {
        // First write the file to .tmp and then rename to avoid a corrupted file if we crash in
        // the middle of the write.
        let params_path_tmp = cache_dir.join("params.json.tmp");
        let mut file = File::create(&params_path_tmp)?;
        file.write_all(params_json.as_bytes())?;
        rename(params_path_tmp, params_path)?;
    }

    let cache_path = cache_dir.join(format!("{}.cbor", name));
    let cache_path_tmp = cache_dir.join(format!("{}.cbor.tmp", name));

    // First try to open the cached file.  If it exists we assume a previous build+cache succeeded
    // so we read, deserialize it and return it.
    // If it doesn't exist we open a corresponding tmp file and try to acquire it exclusively.  If
    // we can't acquire it means another process is building the artifact so we retry again in 100
    // ms.  If we acquire the lock we build the artifact store it in the tmp file and finally
    // rename it to the final cached file.  This way the final cached file either exists and is
    // complete or doesn't exist at all (in case of a crash the corruputed file will be tmp).

    loop {
        let mut file = match File::open(&cache_path) {
            Ok(file) => file,
            Err(err) => {
                if err.kind() == ErrorKind::NotFound {
                    let mut file_tmp = File::create(&cache_path_tmp)?;
                    match file_tmp.try_lock() {
                        Ok(_) => (),
                        Err(TryLockError::WouldBlock) => {
                            // Lock not acquired.  Another process is building the artifact, let's
                            // try again in 100 ms.
                            thread::sleep(time::Duration::from_millis(100));
                            continue;
                        }
                        Err(TryLockError::Error(err)) => return Err(Box::new(err)),
                    }
                    // Exclusive lock acquired, build the artifact, serialize it and store it.
                    log::info!("building {} and storing to the disk cache", log_name);
                    let start = std::time::Instant::now();
                    let data = build_fn(params);
                    let elapsed = std::time::Instant::now() - start;
                    log::debug!("built {} in {:?}", log_name, elapsed);
                    let data_cbor = minicbor_serde::to_vec(&data)?;
                    // First write the file to .tmp and then rename to avoid a corrupted file if we
                    // crash in the middle of the write.
                    file_tmp.write_all(&data_cbor)?;
                    rename(cache_path_tmp, cache_path)?;
                    return Ok(CacheEntry { value: data });
                } else {
                    return Err(Box::new(err));
                }
            }
        };
        log::debug!("found {} in the disk cache", log_name);

        let start = std::time::Instant::now();
        let mut data_cbor = Vec::new();
        file.read_to_end(&mut data_cbor)?;
        let elapsed = std::time::Instant::now() - start;
        log::debug!("read {} from disk in {:?}", log_name, elapsed);

        let start = std::time::Instant::now();
        let data: T = minicbor_serde::from_slice(&data_cbor)?;
        let elapsed = std::time::Instant::now() - start;
        log::debug!("deserialized {} in {:?}", log_name, elapsed);

        return Ok(CacheEntry { value: data });
    }
}
