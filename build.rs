use std::{env, fs, path::Path};
use regex_automata::{dfa::dense, MatchKind};

// precompile dfa so it doesn't have to be done at program start
fn main() {
  println!("cargo:rerun-if-changed=build.rs");
  println!("cargo:rerun-if-env-changed=CARGO_CFG_TARGET_ENDIAN");

  // NOTE: Do NOT use unicode word boundaries (\b) or look-around at the beginning
  //       of a pattern
  // NOTE: Patterns are ordered by precedence, so a lower match overrides a higher one
  let re = dense::Builder::new()
    .configure(dense::Config::new().match_kind(MatchKind::All))
    .build_many(&[
    /*        Comment -  0 */ r"\;.*\n",
    /*     Whitespace -  1 */ r"\s*",
    /*         LParen -  2 */ r"\(",
    /*         RParen -  3 */ r"\)",
    /*          Quote -  4 */ r"\'",
    /*  Boolean(true) -  5 */ r"\#t(?:rue)?",
    /* Boolean(false) -  6 */ r"\#f(?:alse)?",
    /*            Dot -  7 */ r"\.[^\w\!\$\%\&\*\+\-\.\/\:\=\?\@\^\_\~<>]",
    /*     Identifier -  8 */ r"[\w\!\$\%\&\*\+\-\.\/\:\=\?\@\^\_\~<>]+",
    /* Extended Ident -  9 */ r"\|[^\|]*\|",
    /*         String - 10 */ r#".*?[^(?:\\")]"#,
    /*          Float - 11 */ r"[\d\_]*\.[\d\_]*",
    /*    Hexadecimal - 12 */ r"0x[AaBbCcDdEeFf\d\_]*",
    /*         Binary - 13 */ r"0b[01\_]*",
    /*        Decimal - 14 */ r"[\d\_]*",
    ]).unwrap();

  let out_dir = env::var_os("OUT_DIR").unwrap();
  let file = Path::new(&out_dir).join("dfa.bin");
  let (bytes, padding) = if cfg!(target_endian = "big") {
    re.to_bytes_big_endian()
  } else {
    re.to_bytes_little_endian()
  };

  // leave off padding
  fs::write(&file, &bytes[padding..]).unwrap();
}

