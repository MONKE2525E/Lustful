// rustix 1.1.5 fs::RawDir and fs::inotify::Reader over
// MaybeUninit buffers. Prints only values this program makes
// itself (entry names it created, sorted) or comparisons
// between two calls on the same files.
use rustix::fs::inotify::{self, CreateFlags, Reader, WatchFlags};
use rustix::fs::{FileType, Mode, OFlags, RawDir, openat, CWD};
use std::mem::MaybeUninit;

fn main() {
    let dir = std::env::temp_dir().join(format!("lust-rustix-rawdir-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("sub")).unwrap();
    std::fs::write(dir.join("b.txt"), b"x").unwrap();
    std::fs::write(dir.join("a.txt"), b"yy").unwrap();

    let fd = openat(CWD, &dir, OFlags::RDONLY | OFlags::DIRECTORY | OFlags::CLOEXEC, Mode::empty()).unwrap();
    let mut buf = [MaybeUninit::<u8>::uninit(); 8192];
    let mut raw = RawDir::new(&fd, &mut buf);
    let mut names: Vec<String> = Vec::new();
    let mut types: Vec<FileType> = Vec::new();
    let mut lines: Vec<String> = Vec::new();
    while let Some(ent) = raw.next() {
        let ent = ent.unwrap();
        let name = ent.file_name().to_string_lossy().into_owned();
        if name != "." && name != ".." {
            lines.push(format!("entry {} {:?} ino>0={} cookie!=0={}", name, ent.file_type(), ent.ino() > 0, ent.next_entry_cookie() != 0));
            names.push(name);
            types.push(ent.file_type());
        }
    }
    lines.sort();
    for l in lines {
        println!("{l}");
    }
    println!("{}", raw.is_buffer_empty());
    names.sort();
    println!("{:?}", names);
    println!("{}", types.contains(&FileType::Directory) && types.contains(&FileType::RegularFile));

    // A heap buffer, as ts-rust's fswatch shim passes it.
    let fd2 = openat(CWD, &dir, OFlags::RDONLY | OFlags::DIRECTORY | OFlags::CLOEXEC, Mode::empty()).unwrap();
    let mut vbuf = vec![MaybeUninit::<u8>::uninit(); 64];
    let mut raw2 = RawDir::new(&fd2, &mut vbuf);
    let first = raw2.next().unwrap().unwrap();
    println!("{}", first.ino() > 0);

    // inotify Reader over a stack buffer.
    let ino = inotify::init(CreateFlags::NONBLOCK | CreateFlags::CLOEXEC).unwrap();
    let wd = inotify::add_watch(&ino, &dir, WatchFlags::CREATE | WatchFlags::DELETE).unwrap();
    std::fs::write(dir.join("new.txt"), b"z").unwrap();
    let mut pollfds = [rustix::event::PollFd::new(&ino, rustix::event::PollFlags::IN)];
    let ts = rustix::event::Timespec { tv_sec: 5, tv_nsec: 0 };
    println!("{}", rustix::event::poll(&mut pollfds, Some(&ts)).unwrap());
    let mut ibuf = [MaybeUninit::<u8>::uninit(); 4096];
    let mut reader = Reader::new(&ino, &mut ibuf);
    let ev = reader.next().unwrap();
    println!("{:?}", ev);
    println!("{:#?}", ev.events());
    println!("{} {} {}", ev.wd() == wd, ev.events().contains(inotify::ReadFlags::CREATE), ev.file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default());
    println!("{}", reader.is_buffer_empty());
    println!("{:?}", inotify::ReadFlags::from_bits_retain(0x8000_0001));
    println!("{:?} {:?}", inotify::ReadFlags::empty(), inotify::ReadFlags::from_bits_retain(0x8000_0000));
    println!("{:#?}", inotify::ReadFlags::ISDIR | inotify::ReadFlags::CREATE);
    inotify::remove_watch(&ino, wd).unwrap();
    std::fs::remove_dir_all(&dir).unwrap();
}
