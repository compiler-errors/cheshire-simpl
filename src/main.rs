extern crate getopts;
use getopts::Options;
use std::env;
use std::process::{exit, Command};
use std::fs::{self, File};
use std::path::Path;
use std::io::Read;

mod analyzer;
mod parser;
mod lexer;
mod util;
// mod out;
// mod test;

// use analyzer::*;
use parser::Parser;
use lexer::Lexer;
use util::FileReader;
// use out::Out;

fn print_usage(opts: Options) -> ! {
    let brief = "Usage: cheshire CHESHIRE_FILE [options]";
    print!("{}", opts.usage(&brief));
    exit(1);
}

fn main() {
    let args: Vec<_> = env::args().collect();

    let mut opts = Options::new();
    opts.optflag("h", "help", "Print this help menu");
    opts.optopt("O", "output", "Name the output file", "OUTFILE");
    opts.optflag("L",
                 "llvm",
                 "Output an llvm intermediate file instead of an executable");

    let matches = match opts.parse(&args[1..]) {
        Ok(m) => m,
        Err(f) => {
            print_usage(opts);
        }
    };

    if matches.opt_present("h") {
        print_usage(opts);
    }

    let out_llvm = matches.opt_present("L");

    let cheshire_file = if matches.free.len() == 1 {
        matches.free[0].clone()
    } else {
        print_usage(opts);
    };

    let (ll_out_name, exe_out_name) = if out_llvm {
        (matches.opt_str("O").unwrap_or_else(|| format!("{}.ll", &cheshire_file)), "".to_string())
    } else {
        (format!("{}.ll", &cheshire_file),
         matches.opt_str("O").unwrap_or_else(|| format!("{}.out", &cheshire_file)))
    };

    parse_file(cheshire_file, ll_out_name, exe_out_name, out_llvm);
}

fn parse_file(file_name: String, ll_out_name: String, exe_out_name: String, emit_llvm: bool) {
    let mut in_file = match File::open(file_name) {
        Ok(f) => f,
        Err(_) => {
            panic!("Couldn't open input file!"); //TODO: better error..
        }
    };

    fs::remove_file(&ll_out_name);
    let ll_out_file = match File::create(&ll_out_name) {
        Ok(f) => f,
        Err(e) => {
            panic!("Couldn't create output file!");
        }
    };

    let mut contents = "".to_string();
    in_file.read_to_string(&mut contents).unwrap();

    let fr = FileReader::new(&contents);
    let lex = Lexer::new(fr);
    let parse = Parser::new(lex);
    // let mut analyze = Analyzer::new();

    let parsed_file = parse.parse_file();
    // analyze.analyze_file(parsed_file);

    // Out::out(analyze, ll_out_file);

    if !emit_llvm {
        fs::remove_file(&exe_out_name);
        // let out = Command::new("clang")
        // .arg(&ll_out_name)
        // .arg("cheshire_runtime.c")
        // .arg("-O3")
        // .arg("-o")
        // .arg(&exe_out_name)
        // .spawn()
        // .expect("Failed to invoke clang!");
        // arfs::remove_file(&ll_out_name);
    }
}
