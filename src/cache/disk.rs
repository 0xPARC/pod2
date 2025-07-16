use std::{
    fs::{create_dir_all, rename, File, TryLockError},
    io::{Error, ErrorKind, Write},
    thread, time,
};

use directories::BaseDirs;
use serde::{de::DeserializeOwned, Serialize};
use sha2::{Digest, Sha256};

/// Get the artifact named `name` from the disk cache.  If it doesn't exist, it will be built by
/// calling `build_fn` and stored.
/// The artifact is indexed by git commit first and then by `params: P` second.
pub(crate) fn get<T: Serialize + DeserializeOwned + Clone, P: Serialize>(
    name: &str,
    params: &P,
    build_fn: fn(&P) -> T,
) -> Result<T, Box<dyn std::error::Error>> {
    let commit_hash_str = env!("VERGEN_GIT_SHA");
    let params_json = serde_json::to_string(params)?;
    let params_json_hash = Sha256::digest(&params_json);
    let params_json_hash_str_long = format!("{:x}", params_json_hash);
    let params_json_hash_str = format!("{}", &params_json_hash_str_long[..32]);
    log::debug!(
        "getting {}/{}/{}.json from the disk cache",
        commit_hash_str,
        params_json_hash_str,
        name
    );

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

    let cache_path = cache_dir.join(format!("{}.json", name));
    let cache_path_tmp = cache_dir.join(format!("{}.json.tmp", name));

    // First try to open the cached file.  If it exists we assume a previous build+cache succeeded
    // so we read, deserailize it and return it.
    // If it doesn't exist we open a corresponding tmp file and try to acquire it exclusively.  If
    // we can't acquire it means another process is building the artifact so we retry again in 100
    // ms.  If we acquire the lock we build the artifact store it in the tmp file and finally
    // rename it to the final cached file.  This way the final cached file either exists and is
    // complete or doesn't exist at all (in case of a crash the corruputed file will be tmp).

    loop {
        let file = match File::open(&cache_path) {
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
                    log::info!(
                        "building {}/{}/{}.json and storing to disk cache",
                        commit_hash_str,
                        params_json_hash_str,
                        name
                    );
                    let data = build_fn(params);
                    let data_json = serde_json::to_string(&data)?;
                    // First write the file to .tmp and then rename to avoid a corrupted file if we
                    // crash in the middle of the write.
                    file_tmp.write_all(data_json.as_bytes())?;
                    rename(cache_path_tmp, cache_path)?;
                    return Ok(data);
                } else {
                    return Err(Box::new(err));
                }
            }
        };
        let data: T = serde_json::from_reader(file)?;
        return Ok(data);
    }
}
