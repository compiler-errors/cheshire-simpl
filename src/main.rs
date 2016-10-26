use std::fs::File;
use std::path::Path;
use std::env;
use std::io::Read;

mod analyzer;
mod parser;
mod lexer;
mod util;
mod out;

use analyzer::*;
use parser::Parser;
use lexer::Lexer;
use util::FileReader;
use out::Out;

fn main() {
    if let Some(pathstr) = env::args().nth(1) {
        let path = Path::new(&*pathstr);
        if let Ok(file) = File::open(path) {
            parse_file(file);
        } else {
            println!("Couldn't open file \"{}\"!", pathstr);
        }
    } else {
        println!("Please provide a file argument to test the parser on.");
    }
}

fn parse_file(mut file: File) {
    let mut contents = "".to_string();
    file.read_to_string(&mut contents).unwrap();

    let fr = FileReader::new(&contents);
    let lex = Lexer::new(fr);
    let parse = Parser::new(lex);
    let mut analyze = Analyzer::new();

    let parsed_file = parse.parse_file();
    print!("{:#?}", parsed_file);
    analyze.analyze_file(parsed_file);

    Out::out(analyze);
}
