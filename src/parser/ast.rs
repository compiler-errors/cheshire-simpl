use util::FileReader;
use analyzer::{Ty, TY_NOTHING, VarId, StringId, ObjId};

#[derive(Debug)]
/// A file that is being parsed, along with the associated
/// parsed functions that are contained in the file.
pub struct ParseFile<'a> {
    pub file: FileReader<'a>,
    pub functions: Vec<AstFunction>,
    pub objects: Vec<AstObject>,
}

impl<'a> ParseFile<'a> {
    pub fn new(file: FileReader<'a>,
               functions: Vec<AstFunction>,
               objects: Vec<AstObject>)
               -> ParseFile<'a> {
        ParseFile {
            file: file,
            functions: functions,
            objects: objects,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
/// A parsed function
/// The variables associated with the function are given by
/// [beginning_of_vars, end_of_vars).
pub struct AstFunction {
    /// The beginning position of the function
    pub pos: usize,
    /// The simple name of the function
    pub name: String,
    /// The parameter list that the function receives
    pub parameter_list: Vec<AstFnParameter>,
    /// The return type of the function, or AstType::None
    pub return_type: AstType,
    /// The collection of statements associated with the function
    pub definition: AstBlock,
    /// The first variable ID associated with the function
    pub beginning_of_vars: VarId,
    /// The last variable ID associated with the function
    pub end_of_vars: VarId,
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
            beginning_of_vars: 0,
            end_of_vars: 0,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
/// A name and type associated with a parameter, along
/// with the position where this parameter is named.
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
/// A type as parsed by the Parser module.
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
/// A collection of statements, given by a `{}` block.
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
    /// The actual Statement enum
    pub stmt: AstStatementData,
    /// The position of the statement
    pub pos: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub enum AstStatementData {
    Block { block: AstBlock },
    Let {
        var_name: String,
        ty: AstType,
        value: AstExpression,
        var_id: VarId,
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
                var_id: 0,
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
    Null,
    String {
        string: String,
        len: u32,
        id: StringId,
    },
    Int(String),
    UInt(String),
    Float(String),
    Char(char),
    Identifier { name: String, var_id: VarId },
    Tuple { values: Vec<AstExpression> },
    Array { elements: Vec<AstExpression> },

    /// A regular function call
    Call {
        name: String,
        args: Vec<AstExpression>,
    },
    /// An array access `a[1u]`
    Access {
        accessible: Box<AstExpression>,
        idx: Box<AstExpression>,
    },
    /// A tuple access `a:1`
    TupleAccess {
        accessible: Box<AstExpression>,
        idx: u32,
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
/// The kind of binary operation
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
    pub fn string_literal(string: String, len: u32, pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::String {
                string: string,
                len: len,
                id: 0,
            },
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
            expr: AstExpressionData::Identifier {
                name: identifier,
                var_id: 0,
            },
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

    pub fn tuple_access(lhs: AstExpression, idx: u32, pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::TupleAccess {
                accessible: Box::new(lhs),
                idx: idx,
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

    pub fn null_lit(pos: usize) -> AstExpression {
        AstExpression {
            expr: AstExpressionData::Null,
            ty: 0,
            pos: pos,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct AstObject {
    /// The beginning position of the object
    pub pos: usize,
    /// The object name
    pub name: String,
    /// The Id associated with the object in Analysis
    pub obj_id: ObjId,
    /// The functions (both static and member) of the object
    pub functions: Vec<AstObjectFunction>,
    /// The members that are contained in the object
    pub members: Vec<AstObjectMember>,
}

impl AstObject {
    pub fn new(pos: usize,
               name: String,
               functions: Vec<AstObjectFunction>,
               members: Vec<AstObjectMember>)
               -> AstObject {
        AstObject {
            pos: pos,
            name: name,
            obj_id: 0,
            functions: functions,
            members: members,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct AstObjectFunction {
    /// The beginning position of the function
    pub pos: usize,
    /// The simple name of the function
    pub name: String,
    /// Whether the function is a member or static function of the type
    pub has_self: bool,
    /// The parameter list that the function receives
    pub parameter_list: Vec<AstFnParameter>,
    /// The return type of the function, or AstType::None
    pub return_type: AstType,
    /// The collection of statements associated with the function
    pub definition: AstBlock,
    /// The first variable ID associated with the function
    pub beginning_of_vars: VarId,
    /// The last variable ID associated with the function
    pub end_of_vars: VarId,
}

impl AstObjectFunction {
    pub fn new(pos: usize,
               name: String,
               has_self: bool,
               parameter_list: Vec<AstFnParameter>,
               return_type: AstType,
               definition: AstBlock)
               -> AstObjectFunction {
        AstObjectFunction {
            pos: pos,
            name: name,
            has_self: has_self,
            parameter_list: parameter_list,
            return_type: return_type,
            definition: definition,
            beginning_of_vars: 0,
            end_of_vars: 0,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct AstObjectMember {
    pub name: String,
    pub ast_ty: AstType,
    pub ty: Ty,
    pub pos: usize,
}

impl AstObjectMember {
    pub fn new(name: String, ast_ty: AstType, pos: usize) -> AstObjectMember {
        AstObjectMember {
            name: name,
            ast_ty: ast_ty,
            ty: 0,
            pos: pos,
        }
    }
}
