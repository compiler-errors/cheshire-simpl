mod ast;

use std::process::exit;
use std::str::FromStr;
use lexer::{Lexer, Token};
use util::FileReader;
pub use self::ast::*;

type ParseResult<T> = Result<T, ParseError>;

#[derive(Debug)]
/// An error with a location, error string, and possible comments
pub struct ParseError {
    pub loc: usize,
    pub error: String,
    pub comments: Vec<String>,
}

impl ParseError {
    pub fn new(loc: usize, error: String) -> ParseError {
        ParseError {
            loc: loc,
            error: error,
            comments: Vec::new(),
        }
    }

    pub fn comment(&mut self, comment: String) {
        self.comments.push(comment);
    }
}

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    pos: usize,
    next_token: Token,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>) -> Parser<'a> {
        Parser {
            lexer: lexer,
            pos: 0,
            next_token: Token::BOF,
        }
    }

    /// Report an error at the current position
    fn error<T>(&self, s: String) -> ParseResult<T> {
        Err(ParseError::new(self.pos, s))
    }

    /// Report an error at another position
    fn error_at<T>(&self, loc: usize, s: String) -> ParseResult<T> {
        Err(ParseError::new(loc, s))
    }

    /// Move the parser forward one token
    fn bump(&mut self) {
        self.lexer.bump_token();
        self.pos = self.lexer.peek_token_pos();
        self.next_token = self.lexer.peek_token();
    }

    /// Check for a token but don't consume it, otherwise signal an error
    fn expect(&self, token: Token) -> ParseResult<()> {
        let err_tok = format!("{}", token);
        if self.check(token) {
            Ok(())
        } else {
            self.error(format!("Expected token `{}`, found `{}`.", err_tok, self.next_token))
        }
    }

    /// Check for a token and consume it, otherwise signal an error
    fn expect_consume(&mut self, token: Token) -> ParseResult<()> {
        self.expect(token)?;
        self.bump();
        Ok(())
    }

    /// Test for a token, not consuming and return the status as a boolean
    fn check(&self, token: Token) -> bool {
        return token == self.next_token;
    }

    /// Test and consume a token (if it matches), returning the status as a boolean.
    fn check_consume(&mut self, token: Token) -> bool {
        let x = self.check(token);
        if x {
            self.bump();
        }
        x
    }

    /// `check_consume` but for an Identifier token.
    fn expect_get_identifier(&mut self) -> ParseResult<String> {
        let tok = self.next_token.clone();
        if let Token::Identifier(ident) = tok {
            self.bump();
            Ok(ident)
        } else {
            self.error(format!("Expected token `Identifier`, found `{}`.", tok))
        }
    }

    /// `check_consume` but for a Number token.
    fn expect_get_number(&mut self) -> ParseResult<u32> {
        let tok = self.next_token.clone();
        if let Token::IntLiteral(num) = tok {
            self.bump();
            Ok(u32::from_str(&num).unwrap())
        } else {
            self.error(format!("Expected token `IntLiteral`, found `{}`.", tok))
        }
    }

    /// Parse a top level file.
    pub fn parse_file(mut self) -> ParseFile<'a> {
        self.expect_consume(Token::BOF).unwrap();

        let mut functions = Vec::new();
        while !self.check_consume(Token::EOF) {
            let fun_result = self.parse_function();

            if let Err(e) = fun_result {
                report_parse_err_at(&self.lexer.file, e);
            }

            functions.push(fun_result.unwrap());
        }

        ParseFile::new(self.lexer.file, functions)
    }

    /// Parse a single function from the file.
    fn parse_function(&mut self) -> ParseResult<AstFunction> {
        self.expect_consume(Token::Fn)?;
        let pos = self.pos;
        let fn_name = self.expect_get_identifier()?;
        let parameter_list = self.parse_fn_parameter_list()?;
        let return_type = self.try_parse_return_type()?;
        let definition = self.parse_block()?;

        Ok(AstFunction::new(pos, fn_name, parameter_list, return_type, definition))
    }

    /// Parse a parameter list (including LParen and RParen) following a function.
    fn parse_fn_parameter_list(&mut self) -> ParseResult<Vec<AstFnParameter>> {
        self.expect_consume(Token::LParen)?;
        let mut parameters = Vec::new();

        while !self.check_consume(Token::RParen) {
            if parameters.len() != 0 {
                // If it's not the first, then we need a comma
                self.expect_consume(Token::Comma)?;
            }

            // name colon type
            let param_pos = self.pos;
            let param_name = self.expect_get_identifier()?;
            self.expect_consume(Token::Colon)?;
            let type_pos = self.pos;
            let param_type = self.parse_type()?;
            // Array parameter types can't have infer(s) in them
            self.ensure_not_infer(&param_type, type_pos)?;
            parameters.push(AstFnParameter::new(param_name, param_type, param_pos));
        }

        Ok(parameters)
    }

    /// Parse a function return type (including RArrow) or return AstType::None
    /// If it is not present.
    fn try_parse_return_type(&mut self) -> ParseResult<AstType> {
        // We first check for a `->`
        if self.check_consume(Token::RArrow) {
            let type_pos = self.pos;
            let ret = self.parse_type()?;
            // Also make the return type is not a `_`
            self.ensure_not_infer(&ret, type_pos)?;
            Ok(ret)
        } else {
            Ok(AstType::None)
        }
    }

    /// Try to parse an AstType.
    fn parse_type(&mut self) -> ParseResult<AstType> {
        if let Some(ty) = self.try_parse_builtin_type() {
            Ok(ty)
        } else if self.check(Token::LSqBracket) {
            // [T]
            self.parse_array_type()
        } else if self.check(Token::LParen) {
            // (A, B, C)
            self.parse_tuple_type()
        } else {
            self.error(format!("Expected `identifier`, `<` or `(`, found `{}`",
                               self.next_token))
        }
    }

    fn try_parse_builtin_type(&mut self) -> Option<AstType> {
        let ty = match &self.next_token {
            &Token::Int => Some(AstType::Int),
            &Token::UInt => Some(AstType::UInt),
            &Token::Float => Some(AstType::Float),
            &Token::Bool => Some(AstType::Bool),
            &Token::Char => Some(AstType::Char),
            &Token::StringType => Some(AstType::String),
            &Token::Infer => Some(AstType::Infer),
            _ => None,
        };

        if ty.is_some() {
            /// If we got something, then consume it
            self.bump();
        }

        ty
    }

    fn parse_array_type(&mut self) -> ParseResult<AstType> {
        self.expect_consume(Token::LSqBracket)?;
        let ty = self.parse_type()?;
        self.expect_consume(Token::RSqBracket)?;
        Ok(AstType::array(ty))
    }

    fn parse_tuple_type(&mut self) -> ParseResult<AstType> {
        self.expect_consume(Token::LParen)?;

        if self.check_consume(Token::RParen) {
            Ok(AstType::None)
        } else {
            let mut types = Vec::new();

            while !self.check_consume(Token::RParen) {
                if types.len() != 0 {
                    self.expect_consume(Token::Comma)?;

                    // Tuples of len 1 are like `(T,)`
                    if types.len() == 1 && self.check_consume(Token::RParen) {
                        break;
                    }
                }

                types.push(self.parse_type()?);

                // We don't want `(T)`, so we expect a comma if we have only one type.
                if types.len() == 1 {
                    self.expect(Token::Comma)?;
                }
            }

            Ok(AstType::tuple(types))
        }
    }

    // Parse a block of statements including LBrace and RBrace.
    fn parse_block(&mut self) -> ParseResult<AstBlock> {
        self.expect_consume(Token::LBrace)?;
        let mut statements = Vec::new();

        while !self.check_consume(Token::RBrace) {
            statements.push(self.parse_statement()?);
        }

        Ok(AstBlock::new(statements))
    }

    /// Parse a statement.
    fn parse_statement(&mut self) -> ParseResult<AstStatement> {
        let pos = self.pos;
        match &self.next_token {
            &Token::LBrace => self.parse_block_statement(),
            &Token::Let => self.parse_let_statement(),
            &Token::If => self.parse_if_statement(),
            &Token::While => self.parse_while_loop(),
            &Token::Break => {
                self.bump();
                self.expect_consume(Token::Dot)?;
                Ok(AstStatement::break_stmt(pos))
            }
            &Token::Continue => {
                self.bump();
                self.expect_consume(Token::Dot)?;
                Ok(AstStatement::continue_stmt(pos))
            }
            &Token::Return => self.parse_return_statement(),
            &Token::Assert => self.parse_assert_statement(),
            &Token::Dot => {
                self.expect_consume(Token::Dot)?;
                Ok(AstStatement::noop(pos))
            }
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_block_statement(&mut self) -> ParseResult<AstStatement> {
        let pos = self.pos;
        let block = self.parse_block()?;
        Ok(AstStatement::block(block, pos))
    }

    fn parse_let_statement(&mut self) -> ParseResult<AstStatement> {
        let pos = self.pos;
        self.expect_consume(Token::Let)?;
        let var_name = self.expect_get_identifier()?;

        let ty = if self.check_consume(Token::Colon) {
            self.parse_type()?
        } else {
            AstType::Infer
        };

        if !self.check_consume(Token::Equals) {
            return self.error(format!("Expected `:` or `=`, found `{}`", self.next_token));
        }

        let value = self.parse_expression()?;
        self.expect_consume(Token::Dot)?;
        Ok(AstStatement::let_statement(var_name, ty, value, pos))
    }

    fn parse_if_statement(&mut self) -> ParseResult<AstStatement> {
        let pos = self.pos;
        self.expect_consume(Token::If)?;
        let condition = self.parse_expression()?;
        let block = self.parse_block()?;
        let else_block = if self.check_consume(Token::Else) {
            if self.check(Token::If) {
                AstBlock::new(vec![self.parse_if_statement()?])
            } else {
                self.parse_block()?
            }
        } else {
            AstBlock::empty()
        };

        Ok(AstStatement::if_statement(condition, block, else_block, pos))
    }

    fn parse_while_loop(&mut self) -> ParseResult<AstStatement> {
        let pos = self.pos;
        self.expect_consume(Token::While)?;
        let condition = self.parse_expression()?;
        let block = self.parse_block()?;

        Ok(AstStatement::while_loop(condition, block, pos))
    }

    fn parse_return_statement(&mut self) -> ParseResult<AstStatement> {
        let pos = self.pos;
        self.expect_consume(Token::Return)?;

        if self.check(Token::Dot) {
            self.expect_consume(Token::Dot)?;
            Ok(AstStatement::return_nothing(pos))
        } else {
            let value = self.parse_expression()?;
            self.expect_consume(Token::Dot)?;
            Ok(AstStatement::return_statement(value, pos))
        }
    }

    fn parse_assert_statement(&mut self) -> ParseResult<AstStatement> {
        let pos = self.pos;
        self.expect_consume(Token::Assert)?;
        let condition = self.parse_expression()?;
        self.expect_consume(Token::Dot)?;
        Ok(AstStatement::assert_statement(condition, pos))
    }

    fn parse_expression_statement(&mut self) -> ParseResult<AstStatement> {
        let expr = self.parse_expression()?;
        match &expr.expr {
            &AstExpressionData::BinOp { ref kind, .. } => {
                if *kind != BinOpKind::Set {
                    return self.error_at(expr.pos, format!("Expected expression statement."));
                }
            }
            &AstExpressionData::Call { .. } => {
                // Do nothing
            }
            _ => {
                return self.error_at(expr.pos, format!("Expected expression statement."));
            }
        }
        self.expect_consume(Token::Dot)?;
        Ok(AstStatement::expression_statement(expr))
    }

    fn parse_expression(&mut self) -> ParseResult<AstExpression> {
        self.parse_expr(0)
    }

    fn check_operator(&self) -> bool {
        match &self.next_token {
            &Token::Star |
            &Token::Slash |
            &Token::Modulo |
            &Token::Plus |
            &Token::Minus |
            &Token::ShiftLeft |
            &Token::ShiftRight |
            &Token::Lt |
            &Token::Gt |
            &Token::LessEqual |
            &Token::GreaterEqual |
            &Token::EqualsEquals |
            &Token::NotEquals |
            &Token::Caret |
            &Token::And |
            &Token::Pipe |
            &Token::Equals |
            &Token::Colon |
            &Token::LSqBracket |
            &Token::LParen => true,
            _ => false,
        }
    }

    fn get_precedence(token: &Token) -> i32 {
        match token {
            &Token::Star | &Token::Slash | &Token::Modulo => 7,
            &Token::Plus | &Token::Minus => 6,
            &Token::ShiftLeft |
            &Token::ShiftRight => 5,
            &Token::Lt |
            &Token::Gt |
            &Token::LessEqual |
            &Token::GreaterEqual |
            &Token::EqualsEquals |
            &Token::NotEquals => 4,
            &Token::Caret => 3,
            &Token::And => 2,
            &Token::Pipe => 1,
            &Token::Equals => 0,
            _ => unreachable!(),
        }
    }

    fn parse_expr(&mut self, prec: i32) -> ParseResult<AstExpression> {
        let mut lhs = self.parse_expr_initial()?;

        while self.check_operator() {
            let op = self.next_token.clone();
            let pos = self.pos;

            match op {
                Token::LSqBracket => {
                    self.bump();
                    let idx = self.parse_expr(0)?;
                    self.expect_consume(Token::RSqBracket)?;
                    lhs = AstExpression::access(lhs, idx, pos);
                    continue;
                }
                Token::Colon => {
                    self.bump();
                    let idx = self.expect_get_number()?;
                    lhs = AstExpression::tuple_access(lhs, idx, pos);
                    continue;
                }
                _ => {}
            }

            let new_prec = Parser::get_precedence(&op);
            if new_prec < prec {
                break;
            }

            self.bump(); // Okay, consume the op
            let rhs = if op == Token::Equals {
                self.ensure_lval(&lhs)?;
                    self.parse_expr(new_prec)
            } else {
                self.parse_expr(new_prec + 1)
            }?;

            let op_kind = get_kind(op);
            lhs = AstExpression::binop(lhs, rhs, op_kind, pos);
        }

        Ok(lhs)
    }

    fn parse_expr_initial(&mut self) -> ParseResult<AstExpression> {
        let pos = self.pos;
        match &self.next_token {
            &Token::Not => {
                self.bump();
                let e = self.parse_expr(9)?;
                Ok(AstExpression::not(e, pos))
            }
            &Token::Minus => {
                self.bump();
                let e = self.parse_expr(9)?;
                Ok(AstExpression::neg(e, pos))
            }
            &Token::LParen => self.parse_paren_expr(),
            _ => self.parse_expr_literal(),
        }
    }

    fn parse_expr_literal(&mut self) -> ParseResult<AstExpression> {
        let pos = self.pos;
        match self.next_token.clone() {
            Token::LSqBracket => self.parse_array_literal(),
            Token::LParen => self.parse_paren_expr(),
            Token::String(string, len) => {
                self.bump();
                Ok(AstExpression::string_literal(string, len, pos))
            }
            Token::IntLiteral(num) => {
                self.bump();
                Ok(AstExpression::int_literal(num, pos))
            }
            Token::UIntLiteral(num) => {
                self.bump();
                Ok(AstExpression::uint_literal(num, pos))
            }
            Token::FloatLiteral(num) => {
                self.bump();
                Ok(AstExpression::float_literal(num, pos))
            }
            Token::CharLiteral(ch) => {
                self.bump();
                Ok(AstExpression::char_literal(ch, pos))
            }
            Token::Identifier(identifier) => {
                self.bump();
                if self.check(Token::LParen) {
                    let args = self.parse_expr_args()?;
                    Ok(AstExpression::call(identifier, args, pos))
                } else {
                    Ok(AstExpression::identifier(identifier, pos))
                }
            }
            Token::True => {
                self.bump();
                Ok(AstExpression::true_lit(pos))
            }
            Token::False => {
                self.bump();
                Ok(AstExpression::false_lit(pos))
            }
            Token::Null => {
                self.bump();
                Ok(AstExpression::null_lit(pos))
            }
            _ => {
                self.error(format!("Expected literal, identifier, `new` or `(`, found `{}`",
                                   self.next_token))
            }
        }
    }

    fn parse_array_literal(&mut self) -> ParseResult<AstExpression> {
        let pos = self.pos;
        self.expect_consume(Token::LSqBracket)?;

        if self.check_consume(Token::RSqBracket) {
            return Ok(AstExpression::empty_array_literal(pos));
        }

        let first = self.parse_expr(0)?;

        if self.check(Token::Comma) {
            let mut elements = vec![first];

            while !self.check_consume(Token::RSqBracket) {
                self.expect_consume(Token::Comma)?;
                elements.push(self.parse_expr(0)?);
            }

            Ok(AstExpression::array_literal(elements, pos))
        } else if self.check_consume(Token::RSqBracket) {
            let elements = vec![first];
            Ok(AstExpression::array_literal(elements, pos))
        } else {
            self.error(format!("Expected `]` or `,`, found `{}`", self.next_token))
        }
    }

    fn parse_paren_expr(&mut self) -> ParseResult<AstExpression> {
        let pos = self.pos;
        self.expect_consume(Token::LParen)?;

        if self.check_consume(Token::RParen) {
            return Ok(AstExpression::nothing(pos));
        }

        let first = self.parse_expr(0)?;

        if self.check_consume(Token::RParen) {
            Ok(first)
        } else if self.check_consume(Token::Comma) {
            let mut elements = vec![first];
            let mut first = true;

            while !self.check_consume(Token::RParen) {
                if !first {
                    self.expect_consume(Token::Comma)?;
                }

                elements.push(self.parse_expr(0)?);
                first = false;
            }

            Ok(AstExpression::tuple_literal(elements, pos))
        } else {
            // Expected ) , or ..
            self.error(format!("Expected `)` or `,`, found `{}`", self.next_token))
        }
    }

    fn parse_expr_args(&mut self) -> ParseResult<Vec<AstExpression>> {
        self.expect_consume(Token::LParen)?;
        let mut first = true;
        let mut args = Vec::new();

        while !self.check_consume(Token::RParen) {
            if !first {
                self.expect_consume(Token::Comma)?;
            }

            args.push(self.parse_expr(0)?);
            first = false;
        }

        Ok(args)
    }

    fn ensure_lval(&self, expr: &AstExpression) -> ParseResult<()> {
        match &expr.expr {
            &AstExpressionData::Identifier {..} |
            &AstExpressionData::Access {..} => Ok(()),
            &AstExpressionData::TupleAccess { ref accessible, .. } => {
                self.ensure_lval(accessible)
            }
            _ => self.error_at(expr.pos, format!("Expected lval for left of `=`"))
        }
    }

    fn ensure_not_infer(&mut self, ty: &AstType, pos: usize) -> ParseResult<()> {
        match ty {
            &AstType::Array { ref ty } => self.ensure_not_infer(ty, pos),
            &AstType::Tuple { ref types } => {
                for ty in types {
                    self.ensure_not_infer(ty, pos)?;
                }
                Ok(())
            }
            &AstType::Infer => self.error_at(pos, format!("Infer `_` type not expected")),
            _ => Ok(()),
        }
    }
}

fn get_kind(t: Token) -> BinOpKind {
    match t {
        Token::Star => BinOpKind::Multiply,
        Token::Slash => BinOpKind::Divide,
        Token::Modulo => BinOpKind::Modulo,
        Token::Plus => BinOpKind::Add,
        Token::Minus => BinOpKind::Subtract,
        Token::ShiftLeft => BinOpKind::ShiftLeft,
        Token::ShiftRight => BinOpKind::ShiftRight,
        Token::Lt => BinOpKind::Greater,
        Token::Gt => BinOpKind::Less,
        Token::GreaterEqual => BinOpKind::GreaterEqual,
        Token::LessEqual => BinOpKind::LessEqual,
        Token::NotEquals => BinOpKind::NotEqual,
        Token::EqualsEquals => BinOpKind::EqualsEquals,
        Token::Caret => BinOpKind::Xor,
        Token::And => BinOpKind::And,
        Token::Pipe => BinOpKind::Or,
        Token::Equals => BinOpKind::Set,
        _ => unreachable!(),
    }
}

fn report_parse_err_at(fr: &FileReader, e: ParseError) -> ! {
    let (line, col) = fr.get_row_col(e.loc);
    let line_str = fr.get_line_from_pos(e.loc);

    println!("");
    println!("Error \"{}\" encountered on line {}:", e.error, line + 1); //TODO: in file
    for c in e.comments {
        println!("  > {}", c);
    }

    println!("| {}", line_str);
    for _ in 0..(col + 2) {
        print!("-");
    }
    println!("^");
    exit(1);
}
