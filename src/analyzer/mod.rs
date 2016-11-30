mod ty;

pub use self::ty::*;
use util::{FileReader, Counter};
use parser::*;
use std::collections::HashMap;
use std::process::exit;

const MAX_IMPL_SEARCH_DEPTH: u32 = 5;
type AnalyzeResult<T> = Result<T, ()>;

/** The analyzer "module" is mainly concerned with assigning type information and
  * catching final errors (such as type errors), as well as associating each
  * expression with a type, associating variables with a global number, and each
  * string with a global number as well.
  *
  * In the future, the module should also be responsible for resolving the
  * conversion of local names to global names `fn_name` to `pkg.pkg.fn_name`.
  */
pub struct Analyzer {
    // Immediate analyzer state information
    fn_generics: HashMap<String, TyVarId>,
    obj_generics: HashMap<String, TyVarId>,

    fns: HashMap<String, FnSignature>,

    ty_id_count: Counter,
    tys: HashMap<Ty, AnalyzeType>,
    ty_history: HashMap<Ty, Option<AnalyzeType>>,

    obj_id_count: Counter,
    obj_ids: HashMap<String, ObjId>,
    obj_names: HashMap<ObjId, String>,
    obj_skeletons: HashMap<ObjId, AnalyzeObject>,

    trt_id_count: Counter,
    trt_ids: HashMap<String, TraitId>,
    trt_names: HashMap<TraitId, String>, //TODO: possible not necessary (merge into AnalyzeTrait)
    trt_skeletons: HashMap<TraitId, AnalyzeTrait>,

    impls: Vec<AnalyzeImpl>, //TODO: possible make a HashMap<TraitId, Vec<AnalyzeImpl>> instead?
}

impl Analyzer {
    fn check_file(&mut self, f: ParseFile) {
        let ParseFile { file, mut objects, functions, export_fns, traits, impls } = f;

        for obj in &mut objects {
            obj.id = self.obj_id_count.next();
            self.obj_ids.insert(obj.name.clone(), obj.id);
            self.obj_names.insert(obj.id, obj.name.clone());
        }

        for trt in &mut traits {
            trt.id = self.trt_id_count.next();
            self.trt_ids.insert(trt.name.clone(), trt.id);
            self.trt_names.insert(trt.id, trt.name.clone());
        }

        for trt in &traits {
            let analyze_trt = self.initialize_trait(trt);
            self.trt_skeletons.insert(trt.id, analyze_trt);
        }

        for obj in &objects {
            let analyze_obj = self.initialize_object(obj);
            self.obj_skeletons.insert(obj.id, analyze_obj);
        }

        for imp in &impls {
            let analyze_impl = self.initialize_impl(imp);
            self.impls.push(analyze_impl);
        }

        for (_, trt) in &self.trt_skeletons {
            self.init_integrity_trt(trt);
        }

        for (_, obj) in &self.obj_skeletons {
            self.init_integrity_obj(obj);
        }

        for imp in &self.impls {
            self.init_integirty_imp(imp); //TODO: init integirty for non-dummy impls
        }

        for imp in &self.impls {
            self.check_integrity_impl(imp);
        }
    }

    fn check_expr(&mut self, node: &mut AstExpression, expect_ty: Option<Ty>) -> AnalyzeResult<Ty> {
        let &mut AstExpression { ref mut expr, ref mut ty, pos } = node;

        *ty = match expr {
            &mut AstExpressionData::Call { ref name, ref mut generics, ref mut args } => {
                let fn_sig = self.get_fn_sig(name)?;
                //TODO: store generics
                let mut gen_tys: Vec<_> = map_vec(generics, |t| self.init_ty(t));
                let arg_tys: Vec<_> = map_vec_unwrap(args, |e| self.check_expr(e, None))?;
                self.check_fn(&fn_sig, &mut gen_tys, &arg_tys, expect_ty)?
            }
            &mut AstExpressionData::ObjectCall { ref mut object,
                                                 ref fn_name,
                                                 ref generics,
                                                 ref mut args } => {
                let obj_ty = self.check_expr(object, None)?;
                //TODO: store  generics
                let (trait_id, fn_sigs) = self.get_obj_fn_sigs(obj_ty, fn_name, true)?; //true = member
                let mut gen_tys: Vec<_> = map_vec(generics, |t| self.init_ty(t));

                if generics.len() == 0 {
                    for _ in 0..self.get_generics_len(trait_id, fn_name) {
                        gen_tys.push(self.new_infer_ty());
                    }
                } else if generics.len() != self.get_generics_len(trait_id, fn_name) {
                    panic!(); //TODO: error
                }

                let arg_tys: Vec<_> = map_vec_unwrap(args, |e| self.check_expr(e, None))?;
                self.check_fns(&fn_sigs, &mut gen_tys, &arg_tys, expect_ty)?
            }
            &mut AstExpressionData::StaticCall { ref obj_name,
                                                 ref mut obj_generics,
                                                 ref fn_name,
                                                 ref mut fn_generics,
                                                 ref mut args } => {
                let mut obj_gen_tys: Vec<_> = map_vec(obj_generics, |t| self.init_ty(t));
                let obj_ty = self.make_ident_ty(obj_name, obj_gen_tys);
                let (trait_id, fn_sigs) = self.get_obj_fn_sigs(obj_ty, fn_name, false)?; //false = static
                //TODO: store generics (for both...)
                let mut fn_gen_tys: Vec<_> = map_vec(fn_generics, |t| self.init_ty(t));

                if fn_generics.len() == 0 {
                    for _ in 0..self.get_generics_len(trait_id, fn_name) {
                        fn_gen_tys.push(self.new_infer_ty());
                    }
                } else if fn_generics.len() != self.get_generics_len(trait_id, fn_name) {
                    panic!(); //TODO: error
                }

                let arg_tys: Vec<_> = map_vec_unwrap(args, |e| self.check_expr(e, None))?;
                self.check_fns(&fn_sigs, &mut fn_gen_tys, &arg_tys, expect_ty)?
            }
        };

        Ok(*ty)
    }

    fn check_fn(&mut self, fn_sig: &FnSignature,
                generics: &mut Vec<Ty>,
                args: &Vec<Ty>,
                return_hint: Option<Ty>)
                -> AnalyzeResult<Ty> {
        if generics.len() == 0 && fn_sig.generic_ids.len() != 0 {
            for _ in 0..fn_sig.generic_ids.len() {
                generics.push(self.new_infer_ty());
            }
        }

        if generics.len() != fn_sig.generic_ids.len() {
            panic!(""); //ERROR
        }

        let replacements: HashMap<_, _> = fn_sig.generic_ids.iter().zip(generics).map(|(a, b)| (*a, *b)).collect();

        for (expect_ty, arg_ty) in fn_sig.params.iter().zip(args) {
            let repl_expect_ty = self.replace_ty(*expect_ty, replacements);

            self.union_ty(repl_expect_ty, *arg_ty);
        }

        let repl_return_ty = self.replace_ty(fn_sig.return_ty, replacements);

        if let Some(expect_return_ty) = return_hint {
            self.union_ty(expect_return_ty, repl_return_ty)?;
        }

        self.check_requirements(replacements, fn_sig.reqs, MAX_IMPL_SEARCH_DEPTH)
            .and(Ok(repl_return_ty))
    }

    fn check_fns(&mut self, fn_sigs: &Vec<FnSignature>,
                 generics: &mut Vec<Ty>,
                 args: &Vec<Ty>,
                 return_hint: Option<Ty>)
                 -> AnalyzeResult<Ty> {
        let candidate_fn = None;

        for fn_sig in fn_sigs {
            self.set_ty_checkpoint();
            let check_result = self.check_fn(fn_sig, generics, args, return_hint);

            if check_result.is_ok() {
                if candidate_fn.is_some() {
                    self.reset_ty_checkpoint();
                    panic!(""); //ERROR
                }

                candidate_fn = Some(fn_sig);
            }

            self.reset_ty_checkpoint();
        }

        if candidate_fn.is_none() {
            panic!(""); //ERROR
        }

        self.check_fn(candidate_fn.unwrap(), generics, args, return_hint)
    }

    fn check_requirements(&mut self,
                          replacements: HashMap<TyVarId, Ty>,
                          reqs: Vec<AnalyzeRequirement>,
                          depth: u32) -> AnalyzeResult<()> {
        if depth == 0 {
            panic!(""); //ERROR
        }

        for req in reqs {
            let ty = replacements[&req.ty_var];
            let trt = self.replace_ty(req.trt, replacements);
            let trait_id = self.get_trait_id(trt);

            let mut satisfied = false;

            for imp in self.impls {
                if imp.trait_id != trait_id {
                    continue;
                }

                let imp_replacements: HashMap<_, _> =
                    imp.generic_ids.iter().map(|t| (*t, self.new_infer_ty())).collect();
                let imp_ty = self.replace_ty(imp.imp_ty, imp_replacements);
                let imp_trt = self.replace_ty(imp.imp_trt, imp_replacements);

                if self.union_ty_right(ty, imp_ty).is_ok() &&
                   self.union_ty_right(trt, imp_trt).is_ok() &&
                   self.check_requirements(imp_replacements, imp.reqs, depth - 1).is_ok() {
                    satisfied = true;
                    break;
                }
            }

            if !satisfied {
                panic!(""); //ERROR
            }
        }

        Ok(())
    }

    fn get_fn_sig(&self, name: &String) -> AnalyzeResult<FnSignature> {
        self.fns.get(name).ok_or_else(|| {panic!("")}).map(|o| o.clone()) //ERROR
    }

    fn get_obj_fn_sigs(&self,
                       obj_ty: Ty,
                       name: &String,
                       is_member_fn: bool)
                       -> AnalyzeResult<(TraitId, Vec<FnSignature>)> {
        let sigs = Vec::new();
        let candidate_trt = None;

        for imp in &self.impls {
            if self.trait_has_function(imp.trait_id, name, is_member_fn) {
                if let Some(trait_ty) = self.match_ty_impl(obj_ty, imp) {
                    let fn_sig = self.get_trait_function(trait_ty, name);

                    if let Some(trait_id) = candidate_trt {
                        if trait_id != imp.trait_id {
                            panic!(""); //TODO: ERROR
                        }
                    }

                    candidate_trt = Some(imp.trait_id);
                    sigs.push(fn_sig)
                }
            }
        }

        if candidate_trt.is_none() {
            panic!(""); //TODO: error
        }

        Ok((candidate_trt.unwrap(), sigs))
    }

    fn match_ty_impl(&mut self, obj_ty: Ty, imp: &AnalyzeImpl) -> Option<Ty> {
        // TODO: Result??
        let replacements: HashMap<_, _> =
            imp.generic_ids.iter().map(|t| (*t, self.new_infer_ty())).collect();
        let repl_impl_ty = self.replace_ty(imp.imp_ty, replacements);

        if self.union_ty_right(obj_ty, repl_impl_ty).is_err() {
            return None;
        }

        if self.check_requirements(replacements, imp.reqs, MAX_IMPL_SEARCH_DEPTH).is_err() {
            return None;
        }

        // I don't believe I need to reset the checkpoint...
        Some(self.replace_ty(imp.imp_trt, replacements))
    }

    fn make_ident_ty(&mut self, name: &String, generics: Vec<Ty>) -> AnalyzeResult<Ty> {
        if self.fn_generics.contains_key(name) {
            if generics.len() != 0 {
                panic!(""); //TODO: error
            }

            return self.register_ty(AnalyzeType::TypeVariable(self.fn_generics[name]));
        }

        if self.obj_generics.contains_key(name) {
            if generics.len() != 0 {
                panic!(""); //TODO: error
            }

            return self.register_ty(AnalyzeType::TypeVariable(self.obj_generics[name]));
        }

        if let Some(obj_id) = self.obj_ids.get(name) {
            if let Some(obj_skeleton) = self.obj_skeletons.get(obj_id) {
                if generics.len() != 0 {
                    if obj_skeleton.generic_ids.len() != generics.len() {
                        panic!(); //TODO: error
                    }
                } else {
                    for _ in 0..obj_skeleton.generic_ids.len() {
                        generics.push(self.new_infer_ty());
                    }
                }
            } else {
                unimplemented!(); //TODO: add to some struct to check later, drain at end.
            }

            self.register_ty(AnalyzeType::Object(obj_id, generics))
        } else {
            panic!(""); //TODO: error
        }
    }

    fn replace_ty(&mut self, ty: Ty, &replacements: HashMap<TyVarId, Ty>) -> Ty {
        let repl_ty = match &self.tys[&ty] {
            &AnalyzeType::Infer => AnalyzeType::Infer,
            &AnalyzeType::NullInfer => AnalyzeType::NullInfer,

            &AnalyzeType::Nothing => AnalyzeType::Nothing,
            &AnalyzeType::Boolean => AnalyzeType::Boolean,
            &AnalyzeType::Int => AnalyzeType::Int,
            &AnalyzeType::UInt => AnalyzeType::UInt,
            &AnalyzeType::Float => AnalyzeType::Float,
            &AnalyzeType::Char => AnalyzeType::Char,
            &AnalyzeType::String => AnalyzeType::String,
            &AnalyzeType::Tuple(ref inner_tys) => {
                AnalyzeType::Tuple(inner_tys.iter().map(|t| self.replace_ty(*t, replacements)).collect())
            }
            &AnalyzeType::Array(inner_ty) => AnalyzeType::Array(self.replace_ty(inner_ty, replacements)),
            &AnalyzeType::Object(obj_id, ref generics) =>
                AnalyzeType::Object(obj_id, generics.iter().map(|t| self.replace_ty(*t, replacements)).collect()),

            &AnalyzeType::TypeVariable(var_id) => {
                if replacements.contains_key(var_id) {
                    AnalyzeType::Same(replacements[&var_id])
                } else {
                    AnalyzeType::TypeVariable(var_id)
                }
            }

            &AnalyzeType::Same(same_ty) => AnalyzeType::Same(self.replace_ty(same_ty, replacements)),
        };

        self.register_ty(repl_ty)
    }

    fn initialize_object(&mut self, obj: &AstObject) -> AnalyzeObject {
        unimplemented!();
    }

    fn initialize_trait(&mut self, trt: &AstTrait) -> AnalyzeTrait {
        for generic in trt.generics {
            if self.obj_generics.insert(generic, self.ty_id_count.next()).is_some() {
                panic!(""); //ERROR
            }
        }

        let generic_tys: Vec<_> = trt.generics.iter().map(|t| self.generics[t]).collect();
        let mem_fns = HashMap::new();
        let static_fns = HashMap::new();

        for fun in trt.functions {
            if mem_fns.contains_key(fun.name) || static_fns.contains_key(fun.name) {
                panic!(""); //ERROR
            }

            if fun.has_self { &mem_fns } else { &static_fns }
                .insert(fun.name.clone(), self.initialize_object_function(fun));
        }

        self.obj_generics.clear();
        AnalyzeTrait::new(generic_tys, mem_fns, static_fns)
    }

    fn initialize_impl(&mut self, imp: &AstImpl) -> AnalyzeImpl {
        unimplemented!();
    }

    fn init_integrity_trt(&mut self, trt: &AnalyzeTrait) {
        unimplemented!();
    }

    fn init_integrity_obj(&mut self, trt: &AnalyzeObject) {
        unimplemented!();
    }

    fn check_integrity_impl(&mut self, imp: &AnalyzeImpl) {
        unimplemented!();
    }

    fn init_ty(&mut self, ty: &AstType) -> Ty {
        unimplemented!();
    }

    fn get_generics_len(&self, trt: TraitId, fn_name: &String) -> usize {
        unimplemented!();
    }

    fn trait_has_function(&self, trt_id: TraitId, name: &String, member: bool) -> bool {
        unimplemented!();
    }

    fn get_trait_function(&self, trt_ty: Ty, name: &String) -> FnSignature {
        unimplemented!();
    }

    fn union_ty(&mut self, ty1: Ty, ty2: Ty) -> AnalyzeResult<()> {
        if ty1 == ty2 {
            return Ok(());
        }

        // If ty1 is Same, then union the referenced type instead
        if let AnalyzeType::Same(ty1_same) = self.ty_map[&ty1] {
            return self.union_ty(ty1_same, ty2);
        }

        // If ty2 is Same, then union the referenced type instead
        if let AnalyzeType::Same(ty2_same) = self.ty_map[&ty2] {
            return self.union_ty(ty1, ty2_same);
        }

        match (self.ty_map[&ty1].clone(), self.ty_map[&ty2].clone()) { //TODO: :(
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
                    self.union_ty(gen_ty1, gen_ty2)?;
                }
            }
            (AnalyzeType::TypeVariable(tv1), AnalyzeType::TypeVariable(tv2)) => {
                if tv1 != tv2 {
                    panic!(""); //ERROR
                }
            }
            _ => { panic!(); /*ERROR*/ },
        }
    }

    fn union_ty_right(&mut self, ty1: Ty, ty2: Ty) -> AnalyzeResult<()> {
        if ty1 == ty2 {
            return Ok(());
        }

        // If ty1 is Same, then union the referenced type instead
        if let AnalyzeType::Same(ty1_same) = self.ty_map[&ty1] {
            return self.union_ty_right(ty1_same, ty2);
        }

        // If ty2 is Same, then union the referenced type instead
        if let AnalyzeType::Same(ty2_same) = self.ty_map[&ty2] {
            return self.union_ty_right(ty1, ty2_same);
        }

        match (self.ty_map[&ty1].clone(), self.ty_map[&ty2].clone()) { //TODO: :(
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
                    self.union_ty_right(gen_ty1, gen_ty2)?;
                }
            }
            (AnalyzeType::TypeVariable(tv1), AnalyzeType::TypeVariable(tv2)) => {
                if tv1 != tv2 {
                    panic!(""); //ERROR
                }
            }
            _ => {panic!(""); /*ERROR*/ },
        }
    }

    fn get_trait_id(&self, ty: Ty) -> TraitId {
        unimplemented!();
    }

    fn new_infer_ty(&mut self) -> Ty {
        self.register_ty(AnalyzeType::Infer);
    }

    fn register_ty(&mut self, aty: AnalyzeType) -> Ty {
        let id = self.ty_id_count.next().unwrap();

        self.tys.insert(id, aty);
        self.ty_history.insert(id, None);
    }

    fn set_ty(&mut self, ty: Ty, aty: AnalyzeType) {
        let old = self.tys.insert(ty, aty);
        if !self.ty_history.contains_key(ty) {
            self.ty_history.insert(ty, old); //OMG, 10/10
        }
    }

    fn set_ty_checkpoint(&mut self) -> AnalyzeResult<()> {
        if self.ty_history.len() != 0 {
            panic!(""); //ERROR
        }

        Ok(())
    }

    fn reset_ty_checkpoint(&mut self) -> AnalyzeResult<()> {
        for (id, old) in self.ty_history.drain(..) {
            if let Some(old_ty) = old {
                self.tys.insert(id, old_ty);
            } else {
                // None, remove.
                self.tys.remove(&id);
            }
        }

        Ok(())
    }
}

fn map_vec<T, F, K>(vec: &Vec<T>, fun: F) -> Vec<K>
    where F: Fn(&T) -> K {
    vec.iter().map(fun).collect()
}

fn map_vec_unwrap<T, F, K, E>(vec: &mut Vec<T>, fun: F) -> Result<Vec<K>, E>
    where F: Fn(&mut T) -> Result<K, E> {
    vec.iter_mut().map(fun).collect()
}
