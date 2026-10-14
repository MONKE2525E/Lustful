mod table;

fn main() {
    let t = table::Table::new(3);
    println!("{}", t.get(1));
    eprintln!("about to read past the end");
    println!("{}", t.get(5));
}
