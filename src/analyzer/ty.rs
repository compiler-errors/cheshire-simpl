use std::collections::HashMap;

pub type VarId = u32;
pub type StringId = u32;
pub type ObjId = u32;
pub type MemberId = u32;
pub type Ty = u32;

pub const TY_NOTHING: Ty = 1;
pub const TY_BOOLEAN: Ty = 2;
pub const TY_INT: Ty = 3;
pub const TY_UINT: Ty = 4;
pub const TY_FLOAT: Ty = 5;
pub const TY_CHAR: Ty = 6;
pub const TY_STRING: Ty = 7;

pub const TY_FIRST_NEW_ID: Ty = 8;
pub const VAR_FIRST_NEW_ID: VarId = 1;
pub const STR_FIRST_NEW_ID: StringId = 1;
pub const OBJ_FIRST_NEW_ID: ObjId = 1;

#[derive(PartialEq, Eq, Debug, Clone)]
/** AnalyzeType is the type used by the Analyzer module.
  *
  * The types in this enum are pretty self explanatory,
  * but one caveat that should be noticed is the Same
  * type. Same(ty) essentially conveys that the type is
  * identical to another type, without having to copy
  * the contents of that type or other issues introduced
  * by the Infer and Union processes.
  */
pub enum AnalyzeType {
    Infer,
    NullInfer,

    Nothing,
    Boolean,
    Int,
    UInt,
    Float,
    Char,
    String,
    Tuple(Vec<Ty>),
    Array(Ty),
    Object(ObjId),

    Same(Ty),
}

#[derive(Clone)]
/// FnSignature stores the parameter and return types of a function.
pub struct FnSignature {
    pub params: Vec<Ty>,
    pub return_ty: Ty,
}

impl FnSignature {
    pub fn new(params: Vec<Ty>, return_ty: Ty) -> FnSignature {
        FnSignature {
            params: params,
            return_ty: return_ty,
        }
    }
}

pub struct AnalyzeObject {
    pub name: String,
    pub member_ids: HashMap<String, MemberId>,
    pub member_tys: HashMap<MemberId, Ty>,
    pub member_functions: HashMap<String, FnSignature>,
    pub static_functions: HashMap<String, FnSignature>,
}

impl AnalyzeObject {
    pub fn new(obj_name: String,
               member_ids: HashMap<String, MemberId>,
               member_tys: HashMap<MemberId, Ty>,
               member_functions: HashMap<String, FnSignature>,
               static_functions: HashMap<String, FnSignature>)
               -> AnalyzeObject {
        AnalyzeObject {
            name: obj_name,
            member_ids: member_ids,
            member_tys: member_tys,
            member_functions: member_functions,
            static_functions: static_functions,
        }
    }
}
