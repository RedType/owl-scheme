use std::str::FromStr;

mod error;
pub use self::error::{LexError, LexErrorKind};

#[derive(Debug)]
pub enum Lexeme {
  LParen,
  RParen,
  Quote,
  Identifier(String),
  Boolean(bool),
  String(String),
  Integer(i64),
  Float(f64),
}

const CLOSE_ENOUGH: f64 = 0.00000000001;
impl PartialEq<Lexeme> for Lexeme {
  fn eq(&self, other: &Lexeme) -> bool {
    use Lexeme::*;

    match (self, &other) {
      (LParen, LParen) => true,
      (RParen, RParen) => true,
      (Quote, Quote) => true,
      (Identifier(a), Identifier(b)) => a == b,
      (Boolean(a), Boolean(b)) => a == b,
      (String(a), String(b)) => a == b,
      (Integer(a), Integer(b)) => a == b,
      (Float(a), Float(b)) => (a - b).abs() < CLOSE_ENOUGH,
      _ => false,
    }
  }
}
impl Eq for Lexeme {}

#[derive(Debug)]
pub struct LexemeInfo {
  pub lexeme: Lexeme,
  pub line: u64,
  pub col: u64,
  pub boundary_col: u64, // last non-value column
}

#[derive(Clone, Copy)]
enum State {
  Start,
  Comment,
  BoolOrIdent,
  String,
  NegativeOrIdent,
  ZeroPrefixNumeric, // for non-decimal literals
  Hexadecimal,
  Decimal,
  Binary,
}

pub fn lex<I>(source: I) -> Result<Vec<LexemeInfo>, LexError>
where
  I: IntoIterator<Item = char>,
{
  let mut infos = Vec::new();
  let mut state = State::Start;
  // append a " " to end of input so that lexer can finish up
  let mut chars = source.into_iter().chain(" ".chars()).peekable();
  let mut line  = 0u64;
  let mut col   = 0u64;
  let mut boundary_col = 0u64;
  let mut scratch_pad = String::new();
  // for unshift
  let mut prev_line: u64;
  let mut prev_col: u64;
  let mut prev_boundary_col = 0u64;
  // for numerics
  let mut negative = false;

  // help us enforce that either shift or unshift are called
  // every iteration
  let mut shifted = true;

  // iterate over all characters in input. only peek, because
  // some state transitions may not want to consume the character
  while let Some(&ch) = chars.peek() {
    // check shifted
    assert!(shifted);
    #[allow(unused_assignments)]
    { shifted = false; }

    // update counters
    prev_line = line;
    prev_col = col;
    match ch {
      '\n' => {
        line += 1;
        col = 0;
        boundary_col = 0;
      },
      c @ '(' | c @ ')' | c if c.is_whitespace() => {
        col += 1;
        prev_boundary_col = boundary_col;
        boundary_col = col;
      },
      c if c.is_control() => {},
      _ => col += 1,
    }

    // consume current char
    macro_rules! shift {
      () => {
        shifted = true;
        chars.next();
      };
    }

    // reset line info when ch is not consumed
    macro_rules! unshift {
      () => {
        shifted = true;
        line = prev_line;
        col = prev_col;
        boundary_col = prev_boundary_col;
      };
    }

    // pushes a lexeme into the result list, along with all the metadata
    macro_rules! push_lex {
      ($x:expr) => {
        infos.push(LexemeInfo {
          lexeme: $x,
          line,
          col,
          boundary_col,
        })
      };
    }

    // creates and wraps an error
    macro_rules! err {
      ($x:expr) => {
        Err(LexError {
          error: $x,
          line,
          col,
          boundary_col,
        })
      };
    }

    // execute state machine for this iteration
    match state {
      State::Start => {
        match ch {
          ';'  => state = State::Comment,
          '('  => push_lex!(Lexeme::LParen),
          ')'  => push_lex!(Lexeme::RParen),
          '\'' => push_lex!(Lexeme::Quote),
          '"'  => state = State::String,
          '0'  => state = State::ZeroPrefixNumeric,
          '-'  => state = State::NegativeOrIdent,
          c if c.is_whitespace() => {},
          c if c.is_digit(10) => {
            state = State::Decimal;
            scratch_pad.push(c);
          },
          c if c.is_control() =>
            return err!(LexErrorKind::IllegalCharacter(c)),
          c => {
            state = State::BoolOrIdent;
            scratch_pad.push(c);
          }
        }

        // everything in this state consumes ch
        shift!();
      },

      State::Comment => {
        if ch == '\n' {
          state = State::Start;
        }

        shift!();
      },

      State::BoolOrIdent => {
        if ch.is_alphanumeric() {
          scratch_pad.push(ch);
          shift!();
        } else {
          match scratch_pad.as_str() {
            "#t" | "#true"  => push_lex!(Lexeme::Boolean(true)),
            "#f" | "#false" => push_lex!(Lexeme::Boolean(false)),
            _ => push_lex!(Lexeme::Identifier(scratch_pad)),
          }
          scratch_pad = String::new();
          state = State::Start;
          unshift!();
        }
      },

      State::String => {
        match ch {
          '\\' => {
            //TODO do escapes
            todo!();
          },
          '"' => {
            push_lex!(Lexeme::String(scratch_pad));
            scratch_pad = String::new();
            state = State::Start;
          },
          c => scratch_pad.push(c),
        }

        shift!();
      },

      State::NegativeOrIdent => {
        match ch {
          '0' => {
            negative = true;
            state = State::ZeroPrefixNumeric;
          },
          c if c.is_numeric() => {
            negative = true;
            scratch_pad.push(c);
            state = State::Decimal;
          },
          _ => {
            negative = false;
            scratch_pad.push('-');
            state = State::BoolOrIdent;
          },
        }

        shift!();
      },

      State::ZeroPrefixNumeric => {
        match ch {
          'x' => state = State::Hexadecimal,
          'b' => state = State::Binary,
          '.' => {
            scratch_pad.push_str("0.");
            state = State::Decimal;
          },
          c if c.is_numeric() => {
            scratch_pad.push(c);
            state = State::Decimal;
          },
          c if c.is_alphabetic() => return err!(LexErrorKind::InvalidNumber),
          _ => {
            negative = false;
            push_lex!(Lexeme::Integer(0));
            state = State::Start;
            unshift!();
            continue; // so we don't shift later
          },
        }

        shift!();
      },

      State::Hexadecimal => {
        match ch {
          '.' => return err!(LexErrorKind::DotInNonDecimalNumeric),
          c @ '(' | c @ ')' | c if c.is_whitespace() => {
            if let Ok(n) = i64::from_str_radix(&scratch_pad, 16) {
              let final_n = if negative { -1 } else { 1 } * n;
              push_lex!(Lexeme::Integer(final_n));
            } else {
              return err!(LexErrorKind::InvalidNumber);
            }

            negative = false;
            scratch_pad = String::new();
            state = State::Start;
            unshift!();
            continue;
          },
          c if c.is_digit(16) => scratch_pad.push(ch),
          _ => return err!(LexErrorKind::NonHexCharInHex),
        }

        shift!();
      },

      State::Binary => {
        match ch {
          '.' => return err!(LexErrorKind::DotInNonDecimalNumeric),
          c @ '(' | c @ ')' | c if c.is_whitespace() => {
            if let Ok(n) = i64::from_str_radix(&scratch_pad, 2) {
              let final_n = if negative { -1 } else { 1 } * n;
              push_lex!(Lexeme::Integer(final_n));
            } else {
              return err!(LexErrorKind::InvalidNumber);
            }

            negative = false;
            scratch_pad = String::new();
            state = State::Start;
            unshift!();
            continue;
          },
          c if c.is_digit(2) => scratch_pad.push(ch),
          _ => return err!(LexErrorKind::NonBinCharInBin),
        }

        shift!();
      },

      State::Decimal => {
        match ch {
          c @ '(' | c @ ')' | c if c.is_whitespace() => {
            // do conversion
            if scratch_pad.contains('.') {
              // if there's a . then it's a float
              if let Ok(n) = f64::from_str(&scratch_pad) {
                let final_n = if negative { -1.0 } else { 1.0 } * n;
                push_lex!(Lexeme::Float(final_n));
              } else {
                return err!(LexErrorKind::InvalidNumber);
              }
            } else {
              // if there's no . then it's an integer
              if let Ok(n) = i64::from_str_radix(&scratch_pad, 10) {
                let final_n = if negative { -1 } else { 1 } * n;
                push_lex!(Lexeme::Integer(final_n));
              } else {
                return err!(LexErrorKind::InvalidNumber);
              }
            }

            negative = false;
            scratch_pad = String::new();
            state = State::Start;
            unshift!();
            continue;
          },
          '.' => scratch_pad.push('.'),
          c if c.is_digit(10) => scratch_pad.push(c),
          _ => return err!(LexErrorKind::NonDecCharInDec),
        }

        shift!();
      },
    }
  }

  Ok(infos)
}

#[cfg(test)]
mod tests {
  use super::*;

  macro_rules! lex_str {
    ($s:expr) => {
      lex($s.chars())
        .unwrap()
        .into_iter()
        .map(|li| li.lexeme)
        .collect::<Vec<_>>()
    };
  }

  #[test]
  fn empty_string_produces_no_lexemes() {
    let expected: Vec<Lexeme> = Vec::new();
    let actual = lex_str!("");
    assert_eq!(expected, actual);
  }

  #[test]
  fn lexeme_lparen() {
    let expected = vec![Lexeme::LParen];
    let actual = lex_str!("(");
    assert_eq!(expected, actual);

    let expected_double = vec![Lexeme::LParen, Lexeme::LParen];
    let actual_double = lex_str!("((");
    assert_eq!(expected_double, actual_double);
  }

  #[test]
  fn lexeme_rparen() {
    let expected = vec![Lexeme::RParen];
    let actual = lex_str!(")");
    assert_eq!(expected, actual);

    let expected_double = vec![Lexeme::RParen, Lexeme::RParen];
    let actual_double = lex_str!("))");
    assert_eq!(expected_double, actual_double);
  }

  #[test]
  fn lexeme_quote() {
    let expected = vec![Lexeme::Quote];
    let actual = lex_str!("'");
    assert_eq!(expected, actual);

    let expected_double = vec![Lexeme::Quote, Lexeme::Quote];
    let actual_double = lex_str!("''");
    assert_eq!(expected_double, actual_double);
  }

  #[test]
  fn lexeme_identifier() {
    let expected = vec![Lexeme::Identifier("test".into())];
    let actual = lex_str!("test");
    assert_eq!(expected, actual);

    let expected_double = vec![
      Lexeme::Identifier("test".into()),
      Lexeme::Identifier("toast".into()),
    ];
    let actual_double = lex_str!("test toast");
    assert_eq!(expected_double, actual_double);

    let expected_pound = vec![Lexeme::Identifier("#".into())];
    let actual_pound = lex_str!("#");
    assert_eq!(expected_pound, actual_pound);

    let expected_fake_true = vec![Lexeme::Identifier("#tr".into())];
    let actual_fake_true = lex_str!("#tr");
    assert_eq!(expected_fake_true, actual_fake_true);
  }

  #[test]
  fn lexeme_string() {
    let expected = vec![Lexeme::String("test".into())];
    let actual = lex_str!("\"test\"");
    assert_eq!(expected, actual);

    let expected_empty = vec![Lexeme::String("".into())];
    let actual_empty = lex_str!("\"\"");
    assert_eq!(expected_empty, actual_empty);
  }

  #[test]
  fn lexeme_boolean() {
    let expected_true = vec![Lexeme::Boolean(true)];
    let actual_true = lex_str!("#t");
    assert_eq!(expected_true, actual_true);

    let actual_long_true = lex_str!("#true");
    assert_eq!(expected_true, actual_long_true);

    let expected_false = vec![Lexeme::Boolean(false)];
    let actual_false = lex_str!("#f");
    assert_eq!(expected_false, actual_false);

    let actual_long_false = lex_str!("#false");
    assert_eq!(expected_false, actual_long_false);
  }

  #[test]
  fn lexeme_integer_from_decimal() {
    let expected_int = vec![Lexeme::Integer(420)];
    let actual_int = lex_str!("420");
    assert_eq!(expected_int, actual_int);

    let expected_negative_int = vec![Lexeme::Integer(-420)];
    let actual_negative_int = lex_str!("-420");
    assert_eq!(expected_negative_int, actual_negative_int);

    let expected_zero_prefix_int = vec![Lexeme::Integer(420)];
    let actual_zero_prefix_int = lex_str!("0420");
    assert_eq!(expected_zero_prefix_int, actual_zero_prefix_int);

    let expected_zero_prefix_negative_int = vec![Lexeme::Integer(-420)];
    let actual_zero_prefix_negative_int = lex_str!("-0420");
    assert_eq!(
      expected_zero_prefix_negative_int,
      actual_zero_prefix_negative_int,
    );
  }
}

