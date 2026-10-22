/// Language edition for the internal lexer and macro-definition mechanics.
/// Source admission remains restricted to edition 2024.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Edition {
    E2021,
    E2024,
}
