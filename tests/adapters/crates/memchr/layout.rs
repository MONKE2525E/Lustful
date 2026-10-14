// lust-reject: L0652
// The adapter's Finder does not have upstream's layout, so lust must
// not answer size_of for it (ARCH 3.6); the real crate prints its size.
type F = memchr::memmem::Finder<'static>;

fn main() {
    println!("{}", std::mem::size_of::<F>() > 0);
}
