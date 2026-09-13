use std::{
    fs::{create_dir_all, rename, File, OpenOptions, TryLockError},
    io::{self, Error, ErrorKind, Read, Write},
    ops::Deref,
    path::Path,
    thread, time,
};

use directories::BaseDirs;
use serde::{de::DeserializeOwned, Serialize};
use sha2::{Digest, Sha256};

/// How long a writer waits before looking again for an artifact somebody else is building.
const RETRY_INTERVAL: time::Duration = time::Duration::from_millis(100);

pub struct CacheEntry<T> {
    value: T,
}

impl<T> Deref for CacheEntry<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

/// Open `path` for writing without truncating it, and take the exclusive lock.
///
/// Truncation has to wait until the lock is held.  The lock is advisory, so it does not stop
/// another opener from blanking the file its holder is about to rename into place, which is
/// exactly what `File::create` would do here.
///
/// `None` means somebody else holds the lock and the caller should retry.
fn try_lock_tmp(path: &Path) -> io::Result<Option<File>> {
    let file = OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(false)
        .open(path)?;
    match file.try_lock() {
        Ok(()) => Ok(Some(file)),
        Err(TryLockError::WouldBlock) => Ok(None),
        Err(TryLockError::Error(err)) => Err(err),
    }
}

/// Write `bytes` through the locked `tmp_path` and publish them at `path`.
///
/// `file` must be the locked handle on `tmp_path`.  Truncating here rather than at open time is
/// what stops a waiter destroying these bytes, and it also clears any tail left by a writer that
/// crashed part way through.
fn write_and_publish(
    file: &mut File,
    tmp_path: &Path,
    path: &Path,
    bytes: &[u8],
) -> io::Result<()> {
    file.set_len(0)?;
    file.write_all(bytes)?;
    rename(tmp_path, path)
}

/// Get the artifact named `name` from the disk cache.  If it doesn't exist, it will be built by
/// calling `build_fn` and stored.
/// The artifact is indexed by git commit first and then by `params: P` second.
pub fn get<T: Serialize + DeserializeOwned, P: Serialize>(
    name: &str,
    params: &P,
    build_fn: fn(&P) -> T,
) -> Result<CacheEntry<T>, Box<dyn std::error::Error>> {
    let base_dirs =
        BaseDirs::new().ok_or(Error::new(ErrorKind::Other, "no valid home directory"))?;
    get_in(base_dirs.cache_dir(), name, params, build_fn)
}

/// Implementation of [`get`], with the user cache directory passed in so that tests can point it
/// at a temporary directory instead of the real one.
fn get_in<T: Serialize + DeserializeOwned, P: Serialize>(
    user_cache_dir: &Path,
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

    let pod2_cache_dir = user_cache_dir.join("pod2");
    let commit_cache_dir = pod2_cache_dir.join(commit_hash_str);
    create_dir_all(&commit_cache_dir)?;

    let cache_dir = commit_cache_dir.join(&params_json_hash_str);
    create_dir_all(&cache_dir)?;

    // Store the params.json if it doesn't exist for better debuggability
    let params_path = cache_dir.join("params.json");
    let params_path_tmp = cache_dir.join("params.json.tmp");
    while !params_path.try_exists()? {
        let Some(mut file) = try_lock_tmp(&params_path_tmp)? else {
            thread::sleep(RETRY_INTERVAL);
            continue;
        };
        // Somebody else may have published it while we waited for the lock.
        if params_path.try_exists()? {
            continue;
        }
        write_and_publish(
            &mut file,
            &params_path_tmp,
            &params_path,
            params_json.as_bytes(),
        )?;
    }

    let cache_path = cache_dir.join(format!("{}.cbor", name));
    let cache_path_tmp = cache_dir.join(format!("{}.cbor.tmp", name));

    // If the cached file is there a previous build already succeeded, so read it.  Otherwise take
    // the exclusive lock on the tmp file and build.  Whoever loses the lock race sleeps and looks
    // again; the winner re-checks the cached path once it holds the lock, then truncates, writes
    // and renames under it.  So the cached file is either complete or absent, and a crash leaves
    // the mess in the tmp file.
    loop {
        let mut file = match File::open(&cache_path) {
            Ok(file) => file,
            Err(err) if err.kind() != ErrorKind::NotFound => return Err(Box::new(err)),
            Err(_) => {
                let Some(mut file_tmp) = try_lock_tmp(&cache_path_tmp)? else {
                    thread::sleep(RETRY_INTERVAL);
                    continue;
                };
                // Another builder may have finished while we waited for the lock.  Drop the lock
                // and go read what it stored instead of building the artifact again.
                if cache_path.try_exists()? {
                    continue;
                }
                log::info!("building {} and storing to the disk cache", log_name);
                let start = std::time::Instant::now();
                let data = build_fn(params);
                let elapsed = std::time::Instant::now() - start;
                log::debug!("built {} in {:?}", log_name, elapsed);
                let data_cbor = minicbor_serde::to_vec(&data)?;
                write_and_publish(&mut file_tmp, &cache_path_tmp, &cache_path, &data_cbor)?;
                return Ok(CacheEntry { value: data });
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

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};

    use super::*;

    #[derive(Serialize)]
    struct TestParams {
        tag: &'static str,
    }

    const ARTIFACT_LEN: usize = 1 << 20;

    fn artifact() -> Vec<u8> {
        (0..ARTIFACT_LEN).map(|i| (i % 251) as u8).collect()
    }

    /// A waiter that loses the lock race must leave the holder's bytes alone.  Blanking them is
    /// what put zero length files into the cache.
    #[test]
    fn waiter_open_does_not_truncate_lock_holder() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("artifact.cbor.tmp");

        // The lock holder has written its artifact and is about to rename it.
        let mut holder = try_lock_tmp(&path).unwrap().expect("lock should be free");
        holder.write_all(&artifact()).unwrap();
        assert_eq!(std::fs::metadata(&path).unwrap().len(), ARTIFACT_LEN as u64);

        // A waiter now takes its turn at the tmp file and is refused the lock.
        assert!(
            try_lock_tmp(&path).unwrap().is_none(),
            "lock should still be held"
        );

        assert_eq!(
            std::fs::metadata(&path).unwrap().len(),
            ARTIFACT_LEN as u64,
            "waiter truncated the lock holder's file"
        );
    }

    /// Threads racing for the same uncached artifact all see the complete value, and the build
    /// runs once between them.
    #[test]
    fn concurrent_get_is_not_corrupted() {
        static BUILDS: AtomicUsize = AtomicUsize::new(0);

        fn slow_build(_params: &TestParams) -> Vec<u8> {
            BUILDS.fetch_add(1, Ordering::SeqCst);
            // Outlast the retry interval so the waiters really do go round their loop.
            thread::sleep(RETRY_INTERVAL * 2);
            artifact()
        }

        let dir = tempfile::tempdir().unwrap();
        let params = TestParams { tag: "concurrent" };
        let expected = artifact();

        thread::scope(|s| {
            let handles: Vec<_> = (0..8)
                .map(|_| {
                    // `Box<dyn Error>` is not `Send`, so flatten the result before it leaves the
                    // thread.
                    s.spawn(|| {
                        get_in(dir.path(), "artifact", &params, slow_build)
                            .map(|entry| (*entry).clone())
                            .map_err(|err| err.to_string())
                    })
                })
                .collect();
            for handle in handles {
                let value = handle.join().unwrap().expect("cache get failed");
                assert_eq!(value, expected);
            }
        });

        assert_eq!(
            BUILDS.load(Ordering::SeqCst),
            1,
            "the artifact was built more than once"
        );
    }

    /// A tmp file left by a writer that crashed must not leak its tail into the stored artifact.
    #[test]
    fn stale_tmp_file_is_truncated() {
        let dir = tempfile::tempdir().unwrap();
        let params = TestParams { tag: "stale" };
        let expected = artifact();

        // Build once so the cache layout exists, then find where it put things.
        get_in(dir.path(), "artifact", &params, |_| artifact()).unwrap();
        let commit_dir = dir.path().join("pod2").join(env!("VERGEN_GIT_SHA"));
        let mut params_dirs: Vec<_> = std::fs::read_dir(&commit_dir)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .collect();
        assert_eq!(params_dirs.len(), 1, "expected a single params directory");
        let params_dir = params_dirs.pop().unwrap();
        let artifact_path = params_dir.join("artifact.cbor");
        let encoded_len = std::fs::metadata(&artifact_path).unwrap().len();

        // Put back a tmp file longer than the artifact, as a crashed write would have left it.
        std::fs::remove_file(&artifact_path).unwrap();
        std::fs::write(
            params_dir.join("artifact.cbor.tmp"),
            vec![0xff; ARTIFACT_LEN * 4],
        )
        .unwrap();

        let rebuilt = get_in(dir.path(), "artifact", &params, |_| artifact()).unwrap();
        assert_eq!(*rebuilt, expected);
        // Check the stored length too: the decoder tolerates trailing bytes, so an untruncated
        // tail would otherwise go unnoticed.
        assert_eq!(
            std::fs::metadata(&artifact_path).unwrap().len(),
            encoded_len,
            "stale tmp file was not truncated"
        );
    }
}
