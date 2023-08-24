use crate::{
  data::Data,
  parsing::{
    Info,
    Lexeme, LexItem,
    ParseError, ParseErrorKind,
  },
};

pub fn parse<I>(sequence: I) -> Result<Box<dyn Data>, ParseError>
where
  I: IntoIterator<Item = LexItem>,
{
  todo!();
}

