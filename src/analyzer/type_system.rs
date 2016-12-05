use std::collections::HashMap;
use util::Counter;
use parser::AstType;
use super::{Analyzer, AnalyzeResult};
use super::represent::{ObjId, TraitId};

#[derive(PartialEq, Eq, Debug, Copy, Clone, Hash)]
pub struct Ty(pub u32);

#[derive(PartialEq, Eq, Debug, Copy, Clone, Hash)]
pub struct TyVarId(pub u32);

#[derive(Clone)]
pub struct AnalyzeTraitInstance {
    pub id: TraitId,
    pub generics: Vec<Ty>,
}

pub const TY_NOTHING: Ty = Ty(1);
pub const TY_BOOLEAN: Ty = Ty(2);
pub const TY_INT: Ty = Ty(3);
pub const TY_UINT: Ty = Ty(4);
pub const TY_FLOAT: Ty = Ty(5);
pub const TY_CHAR: Ty = Ty(6);
pub const TY_STRING: Ty = Ty(7);

pub const TY_FIRST_NEW_ID: Ty = Ty(8);

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

pub struct TypeSystem {
    pub fn_generics: HashMap<String, TyVarId>,
    pub obj_generics: HashMap<String, TyVarId>,
    pub ty_var_id_count: Counter,

    ty_id_count: Counter,
    tys: HashMap<Ty, AnalyzeType>,
    ty_history: HashMap<Ty, Option<AnalyzeType>>,
    in_snapshot: bool,
}

impl TypeSystem {
    // TODO: reorganize these methods

    pub fn init_ty(&mut self, analyzer: &Analyzer, ty: &AstType) -> AnalyzeResult<Ty> {
        let aty = match ty {
            &AstType::Infer => AnalyzeType::Infer,
            &AstType::None => AnalyzeType::Nothing,
            &AstType::Int => AnalyzeType::Int,
            &AstType::UInt => AnalyzeType::UInt,
            &AstType::Float => AnalyzeType::Float,
            &AstType::Char => AnalyzeType::Char,
            &AstType::Bool => AnalyzeType::Boolean,
            &AstType::String => AnalyzeType::String,
            &AstType::Array { ref ty } => AnalyzeType::Array(self.init_ty(analyzer, ty)?),
            &AstType::Tuple { ref types } => {
                let tys: Result<Vec<_>, _> =
                    types.iter().map(|t| self.init_ty(analyzer, t)).collect();
                AnalyzeType::Tuple(tys?)
            }
            &AstType::Object(ref name, ref generics, pos) => {
                let mut gen_tys: Result<Vec<_>, _> =
                    generics.iter().map(|t| self.init_ty(analyzer, t)).collect(); //TODO: map_vec_unwrap into util?
                self.make_ident_ty(analyzer, name, gen_tys?)? //TODO: unify in a better way
            }
        };

        Ok(self.register_ty(aty))
    }

    pub fn make_ident_ty(&mut self,
                         analyzer: &Analyzer,
                         name: &String,
                         mut generics: Vec<Ty>)
                         -> AnalyzeResult<AnalyzeType> {
        if self.fn_generics.contains_key(name) {
            if generics.len() != 0 {
                return Err(());
            }

            let ty_var = self.fn_generics[name];
            return Ok(AnalyzeType::TypeVariable(ty_var));
        }

        if self.obj_generics.contains_key(name) {
            if generics.len() != 0 {
                return Err(());
            }

            let ty_var = self.obj_generics[name];
            return Ok(AnalyzeType::TypeVariable(ty_var));
        }

        if let Some((obj_id, generics_len)) = analyzer.get_object_info(name) {
            if generics.len() != generics_len {
                if generics.len() != 0 {
                    return Err(());
                }

                for _ in 0..generics_len {
                    generics.push(self.new_infer_ty());
                }
            }

            Ok(AnalyzeType::Object(obj_id, generics))
        } else {
            // TODO: error for trait?
            Err(())
        }
    }

    pub fn init_trait_instance(&mut self,
                               analyzer: &Analyzer,
                               ty: &AstType)
                               -> AnalyzeResult<AnalyzeTraitInstance> {
        match ty {
            &AstType::Object(ref name, ref generics, pos) => {
                let mut gen_tys: Result<Vec<_>, _> =
                    generics.iter().map(|t| self.init_ty(analyzer, t)).collect(); //TODO: map_vec
                let (id, generics_len) = analyzer.get_trait_info(name).ok_or_else(|| ())?;
                Ok(AnalyzeTraitInstance {
                    // TODO: new
                    id: id,
                    generics: gen_tys?,
                })
            }
            _ => Err(()),
        }
    }

    pub fn new_infer_ty(&mut self) -> Ty {
        self.register_ty(AnalyzeType::Infer)
    }

    pub fn register_ty(&mut self, aty: AnalyzeType) -> Ty {
        let id = Ty(self.ty_id_count.next());
        self.tys.insert(id, aty);

        if self.in_snapshot {
            self.ty_history.insert(id, None);
        }

        id
    }

    fn set_ty(&mut self, ty: Ty, aty: AnalyzeType) {
        let old = self.tys.insert(ty, aty);

        if self.in_snapshot && !self.ty_history.contains_key(&ty) {
            self.ty_history.insert(ty, old); //OMG, 10/10
        }
    }

    pub fn set_ty_checkpoint(&mut self) -> AnalyzeResult<()> {
        if self.in_snapshot {
            return Err(());
        }

        self.in_snapshot = true;
        Ok(())
    }

    pub fn reset_ty_checkpoint(&mut self) -> AnalyzeResult<()> {
        self.in_snapshot = false;

        for (id, old) in self.ty_history.drain() {
            if let Some(old_ty) = old {
                self.tys.insert(id, old_ty);
            } else {
                // None, remove.
                self.tys.remove(&id);
            }
        }

        Ok(())
    }

    pub fn replace_ty(&mut self, ty: Ty, replacements: &HashMap<TyVarId, Ty>) -> Ty {
        let repl_ty = match self.tys[&ty].clone() { //TODO: this is bad rust. I can definitely not copy the vecs twice...
            AnalyzeType::Infer => AnalyzeType::Infer,
            AnalyzeType::NullInfer => AnalyzeType::NullInfer,

            AnalyzeType::Nothing => AnalyzeType::Nothing,
            AnalyzeType::Boolean => AnalyzeType::Boolean,
            AnalyzeType::Int => AnalyzeType::Int,
            AnalyzeType::UInt => AnalyzeType::UInt,
            AnalyzeType::Float => AnalyzeType::Float,
            AnalyzeType::Char => AnalyzeType::Char,
            AnalyzeType::String => AnalyzeType::String,
            AnalyzeType::Tuple(inner_tys) => {
                AnalyzeType::Tuple(inner_tys.into_iter()
                    .map(|t| self.replace_ty(t, replacements))
                    .collect())
            }
            AnalyzeType::Array(inner_ty) => {
                AnalyzeType::Array(self.replace_ty(inner_ty, replacements))
            }
            AnalyzeType::Object(obj_id, generics) => {
                AnalyzeType::Object(obj_id,
                                    generics.into_iter()
                                        .map(|t| self.replace_ty(t, replacements))
                                        .collect())
            }
            AnalyzeType::TypeVariable(var_id) => {
                if replacements.contains_key(&var_id) {
                    AnalyzeType::Same(replacements[&var_id])
                } else {
                    AnalyzeType::TypeVariable(var_id)
                }
            }
            AnalyzeType::Same(same_ty) => AnalyzeType::Same(self.replace_ty(same_ty, replacements)),
        };

        self.register_ty(repl_ty)
    }

    pub fn replace_trait(&mut self,
                         trt: &AnalyzeTraitInstance,
                         replacements: &HashMap<TyVarId, Ty>)
                         -> AnalyzeTraitInstance {
        AnalyzeTraitInstance {
            id: trt.id,
            generics: trt.generics.iter().map(|t| self.replace_ty(*t, replacements)).collect(),
        }
    }

    pub fn union_ty(&mut self, ty1: Ty, ty2: Ty) -> AnalyzeResult<()> {
        if ty1 == ty2 {
            return Ok(());
        }

        // If ty1 is Same, then union the referenced type instead
        if let AnalyzeType::Same(ty1_same) = self.tys[&ty1] {
            return self.union_ty(ty1_same, ty2);
        }

        // If ty2 is Same, then union the referenced type instead
        if let AnalyzeType::Same(ty2_same) = self.tys[&ty2] {
            return self.union_ty(ty1, ty2_same);
        }

        match (self.tys[&ty1].clone(), self.tys[&ty2].clone()) { //TODO: :(
            (AnalyzeType::Infer, _) => {
                self.set_ty(ty1, AnalyzeType::Same(ty2));
            }
            (_, AnalyzeType::Infer) => {
                self.set_ty(ty2, AnalyzeType::Same(ty1));
            }
            // NullInfer can union with any *nullable* type
            (AnalyzeType::NullInfer, t) => {
                if !self.is_nullable(&t) {
                    panic!(""); //ERROR
                }
                self.set_ty(ty1, AnalyzeType::Same(ty2));
            }
            (t, AnalyzeType::NullInfer) => {
                if !self.is_nullable(&t) {
                    panic!(""); //ERROR
                }
                self.set_ty(ty2, AnalyzeType::Same(ty1));
            }
            (AnalyzeType::Nothing, AnalyzeType::Nothing) |
            (AnalyzeType::Boolean, AnalyzeType::Boolean) |
            (AnalyzeType::Int, AnalyzeType::Int) |
            (AnalyzeType::UInt, AnalyzeType::UInt) |
            (AnalyzeType::Float, AnalyzeType::Float) |
            (AnalyzeType::Char, AnalyzeType::Char) |
            (AnalyzeType::String, AnalyzeType::String) => {
                // Do nothing.
            }
            // Tuples union if they're the same length and the sub-types union as well.
            (AnalyzeType::Tuple(ty1_tys), AnalyzeType::Tuple(ty2_tys)) => {
                if ty1_tys.len() != ty2_tys.len() {
                    panic!(""); //ERROR
                }
                for i in 0..ty1_tys.len() {
                    self.union_ty(ty1_tys[i], ty2_tys[i])?;
                }
            }
            // Arrays union if their inner types union as well
            (AnalyzeType::Array(inner_ty1), AnalyzeType::Array(inner_ty2)) => {
                self.union_ty(inner_ty1, inner_ty2)?;
            }
            // Object types
            (AnalyzeType::Object(obj_ty1, generics1), AnalyzeType::Object(obj_ty2, generics2)) => {
                if obj_ty1 != obj_ty2 {
                    panic!(""); //ERROR
                }

                for (gen_ty1, gen_ty2) in generics1.iter().zip(generics2) {
                    self.union_ty(*gen_ty1, gen_ty2)?;
                }
            }
            (AnalyzeType::TypeVariable(tv1), AnalyzeType::TypeVariable(tv2)) => {
                if tv1 != tv2 {
                    panic!(""); //ERROR
                }
            }
            _ => {
                panic!(); /*ERROR*/
            }
        }

        Ok(())
    }

    pub fn union_ty_right(&mut self, ty1: Ty, ty2: Ty) -> AnalyzeResult<()> {
        if ty1 == ty2 {
            return Ok(());
        }

        // If ty1 is Same, then union the referenced type instead
        if let AnalyzeType::Same(ty1_same) = self.tys[&ty1] {
            return self.union_ty_right(ty1_same, ty2);
        }

        // If ty2 is Same, then union the referenced type instead
        if let AnalyzeType::Same(ty2_same) = self.tys[&ty2] {
            return self.union_ty_right(ty1, ty2_same);
        }

        match (self.tys[&ty1].clone(), self.tys[&ty2].clone()) { //TODO: :(
            (_, AnalyzeType::Infer) => {
                self.set_ty(ty2, AnalyzeType::Same(ty1));
            }
            (t, AnalyzeType::NullInfer) => {
                if !self.is_nullable(&t) {
                    panic!(""); //ERROR
                }
                self.set_ty(ty2, AnalyzeType::Same(ty1));
            }
            (AnalyzeType::Nothing, AnalyzeType::Nothing) |
            (AnalyzeType::Boolean, AnalyzeType::Boolean) |
            (AnalyzeType::Int, AnalyzeType::Int) |
            (AnalyzeType::UInt, AnalyzeType::UInt) |
            (AnalyzeType::Float, AnalyzeType::Float) |
            (AnalyzeType::Char, AnalyzeType::Char) |
            (AnalyzeType::String, AnalyzeType::String) => {
                // Do nothing.
            }
            // Tuples union if they're the same length and the sub-types union as well.
            (AnalyzeType::Tuple(ty1_tys), AnalyzeType::Tuple(ty2_tys)) => {
                if ty1_tys.len() != ty2_tys.len() {
                    panic!(""); //ERROR
                }
                for i in 0..ty1_tys.len() {
                    self.union_ty_right(ty1_tys[i], ty2_tys[i])?;
                }
            }
            // Arrays union if their inner types union as well
            (AnalyzeType::Array(inner_ty1), AnalyzeType::Array(inner_ty2)) => {
                self.union_ty_right(inner_ty1, inner_ty2)?;
            }
            // Object types
            (AnalyzeType::Object(obj_ty1, generics1), AnalyzeType::Object(obj_ty2, generics2)) => {
                if obj_ty1 != obj_ty2 {
                    panic!(""); //ERROR
                }

                for (gen_ty1, gen_ty2) in generics1.iter().zip(generics2) {
                    self.union_ty_right(*gen_ty1, gen_ty2)?;
                }
            }
            (AnalyzeType::TypeVariable(tv1), AnalyzeType::TypeVariable(tv2)) => {
                if tv1 != tv2 {
                    panic!(""); //ERROR
                }
            }
            _ => {
                panic!(""); /*ERROR*/
            }
        }

        Ok(())
    }

    pub fn union_trait_right(&mut self,
                             trt1: &AnalyzeTraitInstance,
                             trt2: &AnalyzeTraitInstance)
                             -> AnalyzeResult<()> {
        if trt1.id != trt2.id {
            Err(())
        } else {
            for (ty1, ty2) in trt1.generics.iter().zip(trt2.generics.iter()) {
                self.union_ty_right(*ty1, *ty2)?;
            }

            Ok(())
        }
    }

    fn is_nullable(&self, ty: &AnalyzeType) -> bool {
        match ty {
            &AnalyzeType::NullInfer |
            &AnalyzeType::String |
            &AnalyzeType::Array(_) |
            &AnalyzeType::Object(..) => true,
            &AnalyzeType::Same(_) => unreachable!(),
            _ => false,
        }
    }

    pub fn get_ty_var(&self, ty: Ty) -> AnalyzeResult<TyVarId> {
        match &self.tys[&ty] {
            &AnalyzeType::TypeVariable(ty_var) => Ok(ty_var),
            &AnalyzeType::Same(same_ty) => self.get_ty_var(same_ty),
            _ => Err(()),
        }
    }
}
