#[path = "else/where.rs"]
mod w;

mod outer {
    #[path = "deep.rs"]
    pub mod deep;
}

fn main() {
    println!("path {}", w::v() + outer::deep::v());
}
