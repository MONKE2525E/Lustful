// name-to-handle-at 0.1.0: handle and mount id forms
// fswatch/unix.rs writes, plus open_by_handle_at's error
// without CAP_DAC_READ_SEARCH. Handle bytes and mount ids
// never print; only comparisons between calls in this run.
use name_to_handle_at::{name_to_handle_at, open_by_handle_at, MountId, AT_EMPTY_PATH, AT_HANDLE_MNT_ID_UNIQUE, AT_SYMLINK_FOLLOW};
use std::path::Path;

fn kind(r: &std::io::Result<(name_to_handle_at::FileHandle, MountId)>) -> &'static str {
    match r {
        Ok((_, MountId::Reusable(_))) => "reusable",
        Ok((_, MountId::Unique(_))) => "unique",
        Err(_) => "err",
    }
}

fn main() {
    let dir = std::env::temp_dir().join(format!("lust-nth-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("f.txt"), b"data").unwrap();

    let dirfd = std::fs::File::open(&dir).unwrap();
    let (h1, m1) = name_to_handle_at(&dirfd, Path::new("f.txt"), 0).unwrap();
    let (h2, m2) = name_to_handle_at(&dirfd, Path::new("f.txt"), 0).unwrap();
    println!("{} {} {}", h1 == h2, m1 == m2, !h1.handle.is_empty());

    let f = std::fs::File::open(dir.join("f.txt")).unwrap();
    let (h3, _) = name_to_handle_at(&f, Path::new(""), AT_EMPTY_PATH).unwrap();
    println!("{}", h3 == h1);

    let (hf, _) = name_to_handle_at(&dirfd, Path::new("f.txt"), AT_SYMLINK_FOLLOW).unwrap();
    println!("{}", hf == h1);

    let r = name_to_handle_at(&dirfd, Path::new("f.txt"), AT_HANDLE_MNT_ID_UNIQUE);
    println!("{} {}", kind(&r), kind(&Ok((h1.clone(), m1))));

    let missing = name_to_handle_at(&dirfd, Path::new("missing"), 0);
    println!("{}", missing.unwrap_err().raw_os_error() == Some(2));

    // open_by_handle_at needs CAP_DAC_READ_SEARCH: EPERM here,
    // including on the gate boxes (no such capability there).
    let opened = open_by_handle_at(&dirfd, &h1, 0);
    println!("{}", opened.unwrap_err().raw_os_error() == Some(1));

    println!("{} {} {} {}", AT_EMPTY_PATH, AT_SYMLINK_FOLLOW, name_to_handle_at::AT_HANDLE_FID, AT_HANDLE_MNT_ID_UNIQUE);
    std::fs::remove_dir_all(&dir).unwrap();
}
