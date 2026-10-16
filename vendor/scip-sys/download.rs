use std::error::Error;
use std::fs::File;
use std::io::Cursor;
use std::io::Read;
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;
use std::time::Duration;
use tempfile::tempdir;

/// Extracts a zip archive into `target_dir`. If `strip_toplevel` is set and
/// the archive contains a single top-level directory, its contents are moved
/// up into `target_dir` (mirrors the old `zip_extract::extract` behaviour).
fn extract(source: Cursor<Vec<u8>>, target_dir: &Path, strip_toplevel: bool) -> Result<(), Box<dyn Error>> {
    let mut archive = zip::ZipArchive::new(source)?;
    if !strip_toplevel {
        archive.extract(target_dir)?;
        return Ok(());
    }
    let tmp = tempdir()?;
    archive.extract(tmp.path())?;
    let entries: Vec<_> = std::fs::read_dir(tmp.path())?.collect::<Result<_, _>>()?;
    let root = if entries.len() == 1 && entries[0].file_type()?.is_dir() {
        entries[0].path()
    } else {
        tmp.path().to_path_buf()
    };
    std::fs::create_dir_all(target_dir)?;
    for entry in std::fs::read_dir(&root)? {
        let entry = entry?;
        std::fs::rename(entry.path(), target_dir.join(entry.file_name()))?;
    }
    Ok(())
}

pub fn download_and_extract_zip(url: &str, extract_path: &Path) -> Result<(), Box<dyn Error>> {
    // Download the ZIP file
    println!("cargo:warning=Downloading from {}", url);
    let resp = ureq::get(url).timeout(Duration::from_secs(300)).call()?;
    let mut content: Vec<u8> = Vec::new();
    resp.into_reader().read_to_end(&mut content)?;

    // Create a temporary file to store the ZIP
    let dir = tempdir()?;
    let zip_path = dir.path().join("libscip.zip");

    let mut temp_file = File::create(&zip_path)?;
    temp_file.write_all(&content)?;
    let target_dir = PathBuf::from(extract_path);

    println!("cargo:warning=Downloaded to {:?}", zip_path);
    println!("cargo:warning=Extracting to {:?}", target_dir);
    extract(
        Cursor::new(std::fs::read(zip_path).unwrap()),
        &target_dir,
        false,
    )?;

    extract_nested_zip(&target_dir)?;
    Ok(())
}

/// Downloads a `.tar.gz`/`.tgz` archive and extracts it into `extract_path`.
#[cfg(feature = "from-source")]
pub fn download_and_extract_tar_gz(url: &str, extract_path: &Path) -> Result<(), Box<dyn Error>> {
    println!("cargo:warning=Downloading from {}", url);
    let resp = ureq::get(url).timeout(Duration::from_secs(300)).call()?;
    let mut content: Vec<u8> = Vec::new();
    resp.into_reader().read_to_end(&mut content)?;

    println!("cargo:warning=Extracting to {:?}", extract_path);
    let decoder = flate2::read::GzDecoder::new(Cursor::new(content));
    tar::Archive::new(decoder).unpack(extract_path)?;
    Ok(())
}

/// If extracting produced a single nested zip file, extract that too (some
/// release archives wrap the install in another zip).
fn extract_nested_zip(target_dir: &Path) -> Result<(), Box<dyn Error>> {
    let extracted_files: Vec<_> = std::fs::read_dir(target_dir)?.collect();
    if extracted_files.len() == 1 {
        let first_file = extracted_files[0].as_ref().unwrap();
        if first_file
            .path()
            .extension()
            .map_or(false, |ext| ext == "zip")
        {
            println!("cargo:warning=Found nested zip file, extracting again");
            let nested_zip_path = first_file.path();
            extract(
                Cursor::new(std::fs::read(&nested_zip_path).unwrap()),
                &(target_dir.join("scip_install")),
                true,
            )?;
            std::fs::remove_file(nested_zip_path)?;
        }
    }
    Ok(())
}
