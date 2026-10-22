fn remaining<'a>(text: &'a str) -> &'a str {
    let mut chars = text.chars();
    chars.next();
    chars.as_str()
}

fn main() {
    for text in ["", "a", "hello", "é🦀中!"] {
        let mut chars = text.chars();
        println!("start {:?}", chars.as_str());
        println!("front {:?}", chars.next());
        let view = chars.as_str();
        println!("back {:?}", chars.next_back());
        println!("saved {:?}, current {:?}", view, chars.as_str());
        while chars.next().is_some() {}
        println!("empty {:?}", chars.as_str());
        println!("returned {:?}", remaining(text));
    }
    let empty = String::new();
    assert_eq!(empty.chars().as_str(), "");
    let source = String::from("ßeta");
    let mut chars = source.chars();
    let capitalized = chars.next().unwrap().to_uppercase().collect::<String>() + chars.as_str();
    assert_eq!(capitalized, "SSeta");
    let saved = { let chars = source.chars(); chars.as_str() };
    assert_eq!(saved, source);
    let mut chars = source.chars();
    assert_eq!((&chars).as_str(), source);
    assert_eq!((&mut chars).as_str(), source);
    println!("{} {}", capitalized, saved);
}
