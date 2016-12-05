use std::collections::HashMap;
use super::type_system::{Ty, TyVarId, AnalyzeTraitInstance}; //TODO: move into common types mod

pub type VarId = u32;
pub type StringId = u32;
pub type MemberId = u32;

#[derive(PartialEq, Eq, Debug, Copy, Clone, Hash)]
pub struct ObjId(pub u32);

#[derive(PartialEq, Eq, Debug, Copy, Clone, Hash)]
pub struct TraitId(pub u32);

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
}

impl AnalyzeImpl {
    pub fn dummy(ty: Ty, trt: AnalyzeTraitInstance) -> AnalyzeImpl {
        unimplemented!();
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
        unimplemented!();
    }
}
