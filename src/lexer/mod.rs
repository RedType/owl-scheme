pub use error::{LexError, LexErrorKind};

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

pub struct LexemeInfo {
  lexeme: Lexeme,
  line: u64,
  col: u64,
  boundary_col: u64, // last non-value column
}

#[derive(Copy)]
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

pub fn lex<'a, I>(source: I) -> Result<Vec<LexemeInfo>, LexError>
where
  I: IntoIterator<Item = &'a char>,
{
  let mut infos = Vec::new();
  let mut state = State::Start;
  let mut chars = source.into_iter().peekable();
  let mut line  = 0u64;
  let mut col   = 0u64;
  let mut boundary_col = 0u64;
  let mut scratch_pad = String::new();
  // for unshift
  let mut prev_line: u64;
  let mut prev_col: u64;
  let mut prev_boundary_col: u64;
  // for numerics
  let mut negative = false;

  // iterate over all characters in input. only peek, because
  // some state transitions may not want to consume the character
  while let Some(&&ch) = chars.peek() {
    // update counters
    prev_line = line;
    prev_col = col;
    match ch {
      '\n' => {
        line += 1;
        col = 0;
        boundary_col = 0;
      },
      '(' | ')' | c if c.is_whitespace() => {
        col += 1;
        prev_boundary_col = boundary_col;
        boundary_col = col;
      },
      c if c.is_control() => {},
      _ => col += 1,
    }

    // consume current char
    let shift = || chars.next();

    // reset line info when ch is not consumed
    let unshift = || {
      line = prev_line;
      col = prev_col;
      boundary_col = prev_boundary_col;
    };

    // pushes a lexeme into the result list, along with all the metadata
    let push_lex = |lexeme: Lexeme| infos.push(LexemeInfo {
      lexeme,
      line,
      col,
      boundary_col,
    });

    // creates and wraps an error
    let err = |error: LexErrorKind| Err(LexError {
      error,
      line,
      col,
      boundary_col,
    });

    // execute state machine for this iteration
    match state {
      State::Start => {
        match ch {
          ';'  => state = State::Comment,
          '('  => push_lex(Lexeme::LParen),
          ')'  => push_lex(Lexeme::RParen),
          '\'' => push_lex(Lexeme::Quote),
          '"'  => state = State::String,
          '0'  => state = State::ZeroPrefixNumeric,
          '-'  => state = State::NegativeOrIdent,
          c if c.is_whitespace() => {},
          c if c.is_digit(10) => {
            state = State::Decimal;
            scratch_pad.push(c);
          },
          c if c.is_control() =>
            return err(LexErrorKind::IllegalCharacter(c)),
          c => {
            state = State::BoolOrIdent;
            scratch_pad.push(c);
          }
        }

        // everything in this state consumes ch
        shift();
      },

      State::Comment => {
        if ch == '\n' {
          state = State::Start;
        }

        shift();
      },

      State::BoolOrIdent => {
        if ch.is_alphanumeric() {
          scratch_pad.push(ch);
          shift();
        } else {
          match scratch_pad {
            "#t" | "#true"  => push_lex(Lexeme::Boolean(true)),
            "#f" | "#false" => push_lex(Lexeme::Boolean(false)),
            ident => push_lex(Lexeme::Identifier(ident)),
          }
          scratch_pad = String::new();
          state = State::Start;
          unshift();
        }
      },

      State::String => {
        match ch {
          '\\' => {
            //TODO do escapes
            todo!();
          },
          '"' => {
            push_lex(Lexeme::String(scratch_pad));
            scratch_pad = String::new();
            state = State::Start;
          },
          c => scratch_pad.push(c),
        }

        shift();
      },

      State::NegativeOrIdent => {
        match ch {
          '0' => {
            negative = true;
            state = State::ZeroPrefixNumeric;
          },
          c if c.is_numeric() => {
            negative = true;
            state = State::Decimal;
          },
          _ => {
            negative = false;
            scratch_pad.push('-');
            state = State::BoolOrIdent;
          },
        }

        shift();
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
          c if c.is_alphabetic() => return err(LexErrorKind::InvalidNumber),
          _ => {
            negative = false;
            push_lex(Lexeme::Integer(0));
            state = State::Start;
            unshift();
            continue; // so we don't shift later
          },
        }

        shift();
      },

      State::Hexadecimal => {
        match ch {
          '.' => return err(LexErrorKind::DotInNonDecimalNumeric),
          '(' | ')' | c if c.is_whitespace() => {
            if let Ok(n) = i64::from_str_radix(&scratch_pad, 16) {
              let final_n = if negative { -1 } else { 1 } * n;
              push_lex(Lexeme::Integer(final_n));
            } else {
              return err(LexErrorKind::InvalidNumber);
            }

            negative = false;
            scratch_pad = String::new();
            state = State::Start;
            unshift();
            continue;
          },
          c if c.is_digit(16) => scratch_pad.push(ch),
          _ => return err(LexErrorKind::NonHexCharInHex),
        }

        shift();
      },

      State::Binary => {
        match ch {
          '.' => return err(LexErrorKind::DotInNonDecimalNumeric),
          '(' | ')' | c if c.is_whitespace() => {
            if let Ok(n) = i64::from_str_radix(&scratch_pad, 2) {
              let final_n = if negative { -1 } else { 1 } * n;
              push_lex(Lexeme::Integer(final_n));
            } else {
              return err(LexErrorKind::InvalidNumber);
            }

            negative = false;
            scratch_pad = String::new();
            state = State::Start;
            unshift();
            continue;
          },
          c if c.is_digit(2) => scratch_pad.push(ch),
          _ => return err(LexErrorKind::NonBinCharInBin),
        }

        shift();
      },

      State::Decimal => {
        match ch {
          '(' | ')' | c if c.is_whitespace() => {
            // do conversion
            if scratch_pad.contains('.') {
              // if there's a . then it's a float
              if let Ok(n) = f64::from_str(&scratch_pad) {
                let final_n = if negative { -1.0 } else { 1.0 } * n;
                push_lex(Lexeme::Float(final_n));
              } else {
                return err(LexErrorKind::InvalidNumber);
              }
            } else {
              // if there's no . then it's an integer
              if let Ok(n) = i64::from_str_radix(&scratch_pad, 10) {
                let final_n = if negative { -1 } else { 1 } * n;
                push_lex(Lexeme::Integer(final_n));
              } else {
                return err(LexErrorKind::InvalidNumber);
              }
            }

            negative = false;
            scratch_pad = String::new();
            state = State::Start;
            unshift();
            continue;
          },
          '.' => scratch_pad.push('.'),
          c if c.is_digit(10) => scratch_pad.push(c),
          _ => return err(LexErrorKind::NonDecCharInDec),
        }

        shift();
      },
    }
  }

  Ok(infos)
}

