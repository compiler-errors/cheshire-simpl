pub type Ty = u32;

pub const TY_NOTHING: Ty = 1;
pub const TY_BOOLEAN: Ty = 2;
pub const TY_INT: Ty = 3;
pub const TY_UINT: Ty = 4;
pub const TY_FLOAT: Ty = 5;
pub const TY_CHAR: Ty = 6;
pub const TY_STRING: Ty = 7;

pub const TY_FIRST_NEW_ID: Ty = 8;

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum AnalyzeType {
    Infer,
    Nothing,
    Boolean,
    Int,
    UInt,
    Float,
    Char,
    String,
    Tuple(Vec<Ty>),
    Array(Ty),

    Same(Ty)
}

#[derive(Clone)]
pub struct FnSignature {
    pub params: Vec<Ty>,
    pub return_ty: Ty
}

impl FnSignature {
    pub fn new(params: Vec<Ty>, return_ty: Ty) -> FnSignature {
        FnSignature {
            params: params,
            return_ty: return_ty
        }
    }
}
