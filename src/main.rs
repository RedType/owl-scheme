use clap::Parser;
use owl_scheme::vm::VM;
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

const VERSION: &str = env!("CARGO_PKG_VERSION");

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

    println!("owl-scheme v{}", VERSION);

    loop {
      let mut buffer = String::new();
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
        _ => (),
      }

      match vm.eval_str(&buffer) {
        Ok(val) => println!("{}", vm.display_data(&val.data)),
        Err(error) => println!("{}", error),
      }
    }
  }

  Ok(())
}
