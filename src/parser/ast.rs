use util::FileReader;
use analyzer::{Ty, TY_NOTHING};

#[derive(Debug)]
pub struct ParseFile<'a> {
    pub file: FileReader<'a>,
    pub functions: Vec<AstFunction>,
}

impl<'a> ParseFile<'a> {
    pub fn new(file: FileReader<'a>, functions: Vec<AstFunction>) -> ParseFile<'a> {
        ParseFile {
            file: file,
            functions: functions,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct AstFunction {
    pub pos: usize,
    pub name: String,
    pub parameter_list: Vec<AstFnParameter>,
    pub return_type: AstType,
    pub definition: AstBlock,
}

impl AstFunction {
    pub fn new(pos: usize,
               name: String,
               parameter_list: Vec<AstFnParameter>,
               return_type: AstType,
               definition: AstBlock)
               -> AstFunction {
        AstFunction {
            pos: pos,
            name: name,
            parameter_list: parameter_list,
            return_type: return_type,
            definition: definition,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct AstFnParameter {
    pub name: String,
    pub ty: AstType,
    pub pos: usize,
}

impl AstFnParameter {
    pub fn new(name: String, ty: AstType, pos: usize) -> AstFnParameter {
        AstFnParameter {
            name: name,
            ty: ty,
            pos: pos,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum AstType {
    Infer,
    None,
    Int,
    UInt,
    Float,
    Char,
    Bool,
    String,
    Array { ty: Box<AstType> },
    Tuple { types: Vec<AstType> },
}

impl AstType {
    pub fn array(ty: AstType) -> AstType {
        AstType::Array { ty: Box::new(ty) }
    }

    pub fn tuple(types: Vec<AstType>) -> AstType {
        AstType::Tuple { types: types }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct AstBlock {
    pub statements: Vec<AstStatement>,
}

impl AstBlock {
    pub fn new(statements: Vec<AstStatement>) -> AstBlock {
        AstBlock { statements: statements }
    }

    pub fn empty() -> AstBlock {
        AstBlock { statements: Vec::new() }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct AstStatement {
    pub stmt: AstStatementData,
    pub pos: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub enum AstStatementData {
    Block { block: AstBlock },
    Let {
        var_name: String,
        ty: AstType,
        value: AstExpression,
    },
    If {
        condition: AstExpression,
        block: AstBlock,
        else_block: AstBlock,
    },
    While {
        condition: AstExpression,
        block: AstBlock,
    },
    Break,
    Continue,
    Return { value: AstExpression },
    Assert { condition: AstExpression },
    Expression { expression: AstExpression },
    NoOp,
}

impl AstStatement {
    pub fn block(block: AstBlock, pos: usize) -> AstStatement {
        AstStatement {
            stmt: AstStatementData::Block { block: block },
            pos: pos,
        }
    }

    pub fn let_statement(var_name: String,
                         ty: AstType,
                         value: AstExpression,
                         pos: usize)
                         -> AstStatement {
        AstStatement {
            stmt: AstStatementData::Let {
                var_name: var_name,
                ty: ty,
                value: value,
            },
            pos: pos,
        }
    }

    pub fn if_statement(condition: AstExpression,
                        block: AstBlock,
                        else_block: AstBlock,
                        pos: usize)
                        -> AstStatement {
        AstStatement {
            stmt: AstStatementData::If {
                condition: condition,
                block: block,
                else_block: else_block,
            },
            pos: pos,
        }
    }

    pub fn while_loop(condition: AstExpression, block: AstBlock, pos: usize) -> AstStatement {
        AstStatement {
            stmt: AstStatementData::While {
                condition: condition,
                block: block,
            },
            pos: pos,
        }
    }

    pub fn return_statement(value: AstExpression, pos: usize) -> AstStatement {
        AstStatement {
            stmt: AstStatementData::Return { value: value },
            pos: pos,
        }
    }

    pub fn return_nothing(pos: usize) -> AstStatement {
        AstStatement {
            stmt: AstStatementData::Return {
                value: AstExpression {
                    expr: AstExpressionData::Nothing,
                    ty: TY_NOTHING,
                    pos: pos,
                },
            },
            pos: pos,
        }
    }


    pub fn assert_statement(condition: AstExpression, pos: usize) -> AstStatement {
        AstStatement {
            stmt: AstStatementData::Assert { condition: condition },
            pos: pos,
        }
    }


    pub fn expression_statement(expression: AstExpression) -> AstStatement {
        let pos = expression.pos;
        AstStatement {
            stmt: AstStatementData::Expression { expression: expression },
            pos: pos,
        }
    }

    pub fn break_stmt(pos: usize) -> AstStatement {
        AstStatement {
            stmt: AstStatementData::Break,
            pos: pos,
        }
    }

    pub fn continue_stmt(pos: usize) -> AstStatement {
        AstStatement {
            stmt: AstStatementData::Continue,
            pos: pos,
        }
    }

    pub fn noop(pos: usize) -> AstStatement {
        AstStatement {
            stmt: AstStatementData::NoOp,
            pos: pos,
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
pub struct AstExpression {
    pub expr: AstExpressionData,
    pub ty: Ty,
    pub pos: usize,
}

type SubExpression = Box<AstExpression>;

#[derive(Debug, Eq, PartialEq)]
pub enum AstExpressionData {
    Nothing,
    True,
    False,
    String(String),
    Int(String),
    UInt(String),
    Float(String),
    Char(char),
    Identifier(String),
    Tuple { values: Vec<AstExpression> },
    Array { elements: Vec<AstExpression> },

    Call {
        name: String,
        args: Vec<AstExpression>,
    },
    Access {
        accessible: Box<AstExpression>,
        idx: Box<AstExpression>,
    },

    Not(SubExpression),
    Negate(SubExpression),

    BinOp {
        kind: BinOpKind,
        lhs: SubExpression,
        rhs: SubExpression,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOpKind {
    Multiply,
    Divide,
    Modulo,
    Add,
    Subtract,
    ShiftLeft,
    ShiftRight,
    Greater,
    Less,
    GreaterEqual,
    LessEqual,
    EqualsEquals,
    NotEqual,
    Xor,
    And,
    Or,
    Set,
}

impl AstExpression {
    pub fn string_literal(string: String, pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::String(string),
            ty: 0,
            pos: pos,
        }
    }

    pub fn char_literal(ch: char, pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::Char(ch),
            ty: 0,
            pos: pos,
        }
    }

    pub fn int_literal(num: String, pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::Int(num),
            ty: 0,
            pos: pos,
        }
    }

    pub fn uint_literal(num: String, pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::UInt(num),
            ty: 0,
            pos: pos,
        }
    }

    pub fn float_literal(num: String, pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::Float(num),
            ty: 0,
            pos: pos,
        }
    }

    pub fn identifier(identifier: String, pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::Identifier(identifier),
            ty: 0,
            pos: pos,
        }
    }

    pub fn tuple_literal(values: Vec<AstExpression>, pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::Tuple { values: values },
            ty: 0,
            pos: pos,
        }
    }

    pub fn empty_array_literal(pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::Array { elements: Vec::new() },
            ty: 0,
            pos: pos,
        }
    }

    pub fn array_literal(elements: Vec<AstExpression>, pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::Array { elements: elements },
            ty: 0,
            pos: pos,
        }
    }

    pub fn call(name: String, args: Vec<AstExpression>, pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::Call {
                name: name,
                args: args,
            },
            ty: 0,
            pos: pos,
        }
    }

    pub fn access(lhs: AstExpression, idx: AstExpression, pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::Access {
                accessible: Box::new(lhs),
                idx: Box::new(idx),
            },
            ty: 0,
            pos: pos,
        }
    }

    pub fn binop(lhs: AstExpression,
                 rhs: AstExpression,
                 binop: BinOpKind,
                 pos: usize)
                 -> AstExpression {
        AstExpression {
            expr: AstExpressionData::BinOp {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                kind: binop,
            },
            ty: 0,
            pos: pos,
        }
    }

    pub fn not(lhs: AstExpression, pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::Not(Box::new(lhs)),
            ty: 0,
            pos: pos,
        }
    }

    pub fn neg(lhs: AstExpression, pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::Negate(Box::new(lhs)),
            ty: 0,
            pos: pos,
        }
    }

    pub fn nothing(pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::Nothing,
            ty: 0,
            pos: pos,
        }
    }

    pub fn true_lit(pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::True,
            ty: 0,
            pos: pos,
        }
    }

    pub fn false_lit(pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::False,
            ty: 0,
            pos: pos,
        }
    }
}
