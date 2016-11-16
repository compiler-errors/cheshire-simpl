use util::*;
use lexer::*;
use parser::*;
use analyzer::*;
use out::*;

fn test_lex(contents: &'static str) {
    let fr = FileReader::new(&contents);
    let mut lex = Lexer::new(fr);
    assert_eq!(lex.bump_token().0, Token::BOF);
    while lex.bump_token().0 != Token::EOF {}
}

fn test_parse(contents: &'static str) {
    let fr = FileReader::new(&contents);
    let lex = Lexer::new(fr);
    let mut parse = Parser::new(lex);

    parse.parse_file();
}

fn test_analyzer(contents: &'static str) {
    let fr = FileReader::new(&contents);
    let lex = Lexer::new(fr);
    let parse = Parser::new(lex);
    let mut analyze = Analyzer::new();

    let parsed_file = parse.parse_file();
    analyze.analyze_file(parsed_file);
}

fn test_output(contents: &'static str) {
    let fr = FileReader::new(&contents);
    let lex = Lexer::new(fr);
    let parse = Parser::new(lex);
    let mut analyze = Analyzer::new();

    let parsed_file = parse.parse_file();
    analyze.analyze_file(parsed_file);

    Out::out(analyze);
}

// ---------------------- SUCCESS ----------------------- //

#[test]
fn testing_lexer() {}

fn testing_parser() {}

fn testing_analyzer() {}

fn testing_output() {}

// ---------------------- FAILURES ---------------------- //
