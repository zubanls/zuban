use super::Type;

#[derive(Clone, Debug)]
pub enum ResultContext<'db, 'a> {
    Known(Type<'db, 'a>),
    Unknown,
}
