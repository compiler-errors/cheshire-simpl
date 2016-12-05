use std::collections::HashMap;

pub type VarId = u32;
pub type StringId = u32;
pub type MemberId = u32;

#[derive(PartialEq, Eq, Debug, Copy, Clone, Hash)]
pub struct Ty(pub u32);

pub const TY_NOTHING: Ty = Ty(1);
pub const TY_BOOLEAN: Ty = Ty(2);
pub const TY_INT: Ty = Ty(3);
pub const TY_UINT: Ty = Ty(4);
pub const TY_FLOAT: Ty = Ty(5);
pub const TY_CHAR: Ty = Ty(6);
pub const TY_STRING: Ty = Ty(7);

pub const TY_FIRST_NEW_ID: Ty = Ty(8);

#[derive(PartialEq, Eq, Debug, Copy, Clone, Hash)]
pub struct TyVarId(pub u32);

#[derive(PartialEq, Eq, Debug, Copy, Clone, Hash)]
pub struct ObjId(pub u32);

#[derive(PartialEq, Eq, Debug, Copy, Clone, Hash)]
pub struct TraitId(pub u32);

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
    Object(ObjId, Vec<Ty>),
    // Trait(TraitId, Vec<Ty>),
    TypeVariable(TyVarId),

    Same(Ty),
}

#[derive(Clone)]
pub struct AnalyzeTraitInstance {
    pub id: TraitId,
    pub generics: Vec<Ty>,
}

#[derive(Clone)]
/// FnSignature stores the parameter and return types of a function.
pub struct FnSignature {
    pub params: Vec<Ty>,
    pub generic_ids: Vec<TyVarId>,
    pub reqs: Vec<AnalyzeRequirement>,
    pub return_ty: Ty,
}

impl FnSignature {
    pub fn new(params: Vec<Ty>,
               generic_ids: Vec<TyVarId>,
               reqs: Vec<AnalyzeRequirement>,
               return_ty: Ty)
               -> FnSignature {
        FnSignature {
            params: params,
            generic_ids: generic_ids,
            reqs: reqs,
            return_ty: return_ty,
        }
    }
}

#[derive(Clone)]
pub struct AnalyzeObject {
    pub id: ObjId,
    pub generic_ids: Vec<TyVarId>,
    pub member_ids: HashMap<String, MemberId>,
    pub member_tys: Vec<Ty>,
    pub reqs: Vec<AnalyzeRequirement>,
}

impl AnalyzeObject {
    pub fn new(id: ObjId,
               generic_ids: Vec<TyVarId>,
               member_ids: HashMap<String, MemberId>,
               member_tys: Vec<Ty>,
               reqs: Vec<AnalyzeRequirement>)
               -> AnalyzeObject {
        AnalyzeObject {
            id: id,
            generic_ids: generic_ids,
            member_ids: member_ids,
            member_tys: member_tys,
            reqs: reqs,
        }
    }
}

#[derive(Clone)]
pub struct AnalyzeImpl {
    pub imp_ty: Ty,
    pub imp_trt: AnalyzeTraitInstance,
    pub trait_id: TraitId,
    pub generic_ids: Vec<TyVarId>,
    pub reqs: Vec<AnalyzeRequirement>,
    pub dummy: bool
}

impl AnalyzeImpl {
    pub fn dummy(ty: Ty, trt: AnalyzeTraitInstance) -> AnalyzeImpl {
        AnalyzeImpl {
            imp_ty: ty,
            trait_id: trt.id,
            imp_trt: trt,
            generic_ids: Vec::new(),
            reqs: Vec::new(),
            dummy: true
        }
    }

    pub fn new(imp_ty: Ty,
               imp_trt: AnalyzeTraitInstance,
               generic_ids: Vec<TyVarId>,
               reqs: Vec<AnalyzeRequirement>)
               -> AnalyzeImpl {
        AnalyzeImpl {
            imp_ty: imp_ty,
            trait_id: imp_trt.id,
            imp_trt: imp_trt,
            generic_ids: generic_ids,
            reqs: reqs,
            dummy: false
        }
    }
}

#[derive(Clone)]
pub struct AnalyzeTrait {
    pub id: TraitId,
    pub generic_ids: Vec<TyVarId>,
    pub member_fns: HashMap<String, FnSignature>,
    pub static_fns: HashMap<String, FnSignature>,
    pub reqs: Vec<AnalyzeRequirement>,
}

impl AnalyzeTrait {
    pub fn new(id: TraitId,
               generic_ids: Vec<TyVarId>,
               member_fns: HashMap<String, FnSignature>,
               static_fns: HashMap<String, FnSignature>,
               reqs: Vec<AnalyzeRequirement>)
               -> AnalyzeTrait {
        AnalyzeTrait {
            id: id,
            generic_ids: generic_ids,
            member_fns: member_fns,
            static_fns: static_fns,
            reqs: reqs,
        }
    }
}

#[derive(Clone)]
pub struct AnalyzeRequirement {
    pub ty_var: TyVarId,
    pub trt: AnalyzeTraitInstance,
}

impl AnalyzeRequirement {
    pub fn new(ty_var: TyVarId, trt: AnalyzeTraitInstance) -> AnalyzeRequirement {
        AnalyzeRequirement {
            ty_var: ty_var,
            trt: trt
        }
    }
}
