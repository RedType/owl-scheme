use clap::Parser;
use owl_scheme::{data::Data, vm::VM};
use std::{
  fs::File,
  io::{self, prelude::*},
};

/// owl-scheme language runtime
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
  /// Path of file to interpret and execute
  #[arg(short, long)]
  file: Option<String>,
}

#[allow(dead_code)]
fn main() -> io::Result<()> {
  let Args { file } = Args::parse();

  // execute a file
  if let Some(path) = file {
    let mut vm = VM::new();
    let mut source = String::new();
    let mut file = File::create(path)?;
    file.read_to_string(&mut source)?;

    if let Err(error) = vm.eval_str(&source) {
      println!("{}", error);
    }

  // run in interactive mode
  } else {
    let mut vm = VM::new();
    let stdin = io::stdin();
    let mut stdout = io::stdout();

    #[cfg(not(debug_assertions))]
    println!("owl-scheme v{}", env!("CARGO_PKG_VERSION"));
    #[cfg(debug_assertions)]
    println!("owl-scheme v{} (debug)", env!("CARGO_PKG_VERSION"));

    loop {
      let mut buffer = String::new();
      // nonzero here means debug printing
      #[allow(unused_mut)]
      let mut slice_at = 0;
      print!("> ");
      stdout.flush()?;
      stdin.read_line(&mut buffer)?;

      // check for repl commands
      match buffer.as_str() {
        "\n" => continue,
        ":q\n" => {
          println!("Goodbye <3");
          break;
        },
        #[cfg(debug_assertions)]
        s if s.starts_with(":d ") => {
          slice_at = 3;
        },
        _ => (),
      }

      match vm.eval_str(&buffer[slice_at..]) {
        #[cfg(debug_assertions)]
        Ok(val) if slice_at != 0 => println!("{:#?}", val.data),
        #[cfg(debug_assertions)]
        Err(error) if slice_at != 0 => println!("{:#?}", error),

        Ok(val) => match &val.data {
          d @ Data::Integer(69)
          | d @ Data::Complex(69.0, _)
          | d @ Data::Real(69.0)
          | d @ Data::Rational(69, 1) => println!("{} (nice)", d),
          d @ Data::Integer(420)
          | d @ Data::Complex(420.0, _)
          | d @ Data::Real(420.0)
          | d @ Data::Rational(420, 1) => println!("{} 🔥", d),
          d => println!("{}", d),
        },
        Err(error) => println!("{}", error),
      }
    }
  }

  Ok(())
}
