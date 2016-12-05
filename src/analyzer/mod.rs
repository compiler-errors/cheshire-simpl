mod type_system;
mod represent;

pub use self::type_system::*;
pub use self::represent::*;
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
    fns: HashMap<String, FnSignature>,

    obj_id_count: Counter,
    obj_info: HashMap<String, (ObjId, usize)>,
    obj_names: HashMap<ObjId, String>, // TODO: possible not necessary (merge into AnalyzeObject)
    obj_skeletons: HashMap<ObjId, AnalyzeObject>,

    trt_id_count: Counter,
    trt_info: HashMap<String, (TraitId, usize)>,
    trt_names: HashMap<TraitId, String>, // TODO: possible not necessary (merge into AnalyzeTrait)
    trt_skeletons: HashMap<TraitId, AnalyzeTrait>,

    impls: Vec<AnalyzeImpl>, // TODO: possible make a HashMap<TraitId, Vec<AnalyzeImpl>> instead?
}

impl Analyzer {
    fn check_file(&mut self, f: ParseFile, tys: &mut TypeSystem) -> AnalyzeResult<()> {
        let ParseFile { file, mut objects, functions, export_fns, mut traits, mut impls } = f;

        for obj in &mut objects {
            obj.id = ObjId(self.obj_id_count.next());
            self.obj_info.insert(obj.name.clone(), (obj.id, obj.generics.len()));
            self.obj_names.insert(obj.id, obj.name.clone());
        }

        for trt in &mut traits {
            trt.id = TraitId(self.trt_id_count.next());
            self.trt_info.insert(trt.name.clone(), (trt.id, trt.generics.len()));
            // TODO: check for conflicts with objects too..
            self.trt_names.insert(trt.id, trt.name.clone());
        }

        for trt in &traits {
            let analyze_trt = self.initialize_trait(tys, trt)?;
            self.trt_skeletons.insert(trt.id, analyze_trt);
        }

        for obj in &objects {
            let analyze_obj = self.initialize_object(tys, obj)?;
            self.obj_skeletons.insert(obj.id, analyze_obj);
        }

        for imp in &impls {
            let analyze_impl = self.initialize_impl(tys, imp)?;
            self.impls.push(analyze_impl);
        }

        for imp in &self.impls {
            self.check_integrity_impl(imp);
        }

        Ok(())
    }

    fn check_expr(&self,
                  tys: &mut TypeSystem,
                  node: &mut AstExpression,
                  expect_ty: Option<Ty>)
                  -> AnalyzeResult<Ty> {
        let &mut AstExpression { ref mut expr, ref mut ty, pos } = node;

        *ty = match expr {
            &mut AstExpressionData::Call { ref name, ref generics, ref mut args } => {
                let fn_sig = self.get_fn_sig(name)?;
                // TODO: store generics
                let mut gen_tys = map_vec(generics, |t| tys.init_ty(self, t))?;
                let arg_tys = map_vec_mut(args, |e| self.check_expr(tys, e, None))?;
                self.check_fn(tys, &fn_sig, &mut gen_tys, &arg_tys, expect_ty)?
            }
            &mut AstExpressionData::ObjectCall { ref mut object,
                                                 ref fn_name,
                                                 ref generics,
                                                 ref mut args } => {
                let obj_ty = self.check_expr(tys, object, None)?;
                // TODO: store  generics
                let (trait_id, fn_sigs) = self.get_obj_fn_sigs(tys, obj_ty, fn_name, true)?; //true = member
                let mut gen_tys = map_vec(generics, |t| tys.init_ty(self, t))?;

                if generics.len() == 0 {
                    for _ in 0..self.get_generics_len(trait_id, fn_name, true) {
                        gen_tys.push(tys.new_infer_ty());
                    }
                } else if generics.len() != self.get_generics_len(trait_id, fn_name, true) {
                    return Err(());
                }

                let arg_tys = map_vec_mut(args, |e| self.check_expr(tys, e, None))?;
                self.check_fns(tys, &fn_sigs, &mut gen_tys, &arg_tys, expect_ty)?
            }
            &mut AstExpressionData::StaticCall { ref obj_name,
                                                 ref obj_generics,
                                                 ref fn_name,
                                                 ref fn_generics,
                                                 ref mut args } => {
                let mut obj_gen_tys = map_vec(obj_generics, |t| tys.init_ty(self, t))?;
                let obj_aty = tys.make_ident_ty(self, obj_name, obj_gen_tys)?;
                let obj_ty = tys.register_ty(obj_aty); //TODO: ugly
                let (trait_id, fn_sigs) = self.get_obj_fn_sigs(tys, obj_ty, fn_name, false)?; //false = static
                //TODO: store generics (for both...)
                let mut fn_gen_tys = map_vec(fn_generics, |t| tys.init_ty(self, t))?;

                if fn_generics.len() == 0 {
                    for _ in 0..self.get_generics_len(trait_id, fn_name, false) {
                        fn_gen_tys.push(tys.new_infer_ty());
                    }
                } else if fn_generics.len() != self.get_generics_len(trait_id, fn_name, false) {
                    panic!(); //TODO: error
                }

                let arg_tys = map_vec_mut(args, |e| self.check_expr(tys, e, None))?;
                self.check_fns(tys, &fn_sigs, &mut fn_gen_tys, &arg_tys, expect_ty)?
            }
            _ => unimplemented!(),
        };

        Ok(*ty)
    }

    fn check_fn(&self,
                tys: &mut TypeSystem,
                fn_sig: &FnSignature,
                generics: &mut Vec<Ty>,
                args: &Vec<Ty>,
                return_hint: Option<Ty>)
                -> AnalyzeResult<Ty> {
        if generics.len() == 0 && fn_sig.generic_ids.len() != 0 {
            for _ in 0..fn_sig.generic_ids.len() {
                generics.push(tys.new_infer_ty());
            }
        }

        if generics.len() != fn_sig.generic_ids.len() {
            panic!(""); //ERROR
        }

        let replacements: HashMap<_, _> =
            fn_sig.generic_ids.iter().zip(generics).map(|(a, b)| (*a, *b)).collect();

        for (expect_ty, arg_ty) in fn_sig.params.iter().zip(args) {
            let repl_expect_ty = tys.replace_ty(*expect_ty, &replacements);

            tys.union_ty(repl_expect_ty, *arg_ty);
        }

        let repl_return_ty = tys.replace_ty(fn_sig.return_ty, &replacements);

        if let Some(expect_return_ty) = return_hint {
            tys.union_ty(expect_return_ty, repl_return_ty)?;
        }

        self.check_requirements(tys, &replacements, &fn_sig.reqs, MAX_IMPL_SEARCH_DEPTH)
            .and(Ok(repl_return_ty))
    }

    fn check_fns(&self,
                 tys: &mut TypeSystem,
                 fn_sigs: &Vec<FnSignature>,
                 generics: &mut Vec<Ty>,
                 args: &Vec<Ty>,
                 return_hint: Option<Ty>)
                 -> AnalyzeResult<Ty> {
        let mut candidate_fn = None;

        for fn_sig in fn_sigs {
            tys.set_ty_checkpoint();
            let check_result = self.check_fn(tys, fn_sig, generics, args, return_hint);

            if check_result.is_ok() {
                if candidate_fn.is_some() {
                    tys.reset_ty_checkpoint();
                    panic!(""); //ERROR
                }

                candidate_fn = Some(fn_sig);
            }

            tys.reset_ty_checkpoint();
        }

        if candidate_fn.is_none() {
            panic!(""); //ERROR
        }

        self.check_fn(tys, candidate_fn.unwrap(), generics, args, return_hint)
    }

    fn check_requirements(&self,
                          tys: &mut TypeSystem,
                          replacements: &HashMap<TyVarId, Ty>,
                          reqs: &Vec<AnalyzeRequirement>,
                          depth: u32)
                          -> AnalyzeResult<()> {
        if depth == 0 {
            panic!(""); //ERROR
        }

        for req in reqs {
            let ty = replacements[&req.ty_var];
            let trt = tys.replace_trait(&req.trt, replacements);
            let trait_id = trt.id; //TODO: give name?

            let mut satisfied = false;

            for imp in &self.impls {
                if imp.trait_id != trait_id {
                    continue;
                }

                let imp_replacements: HashMap<_, _> =
                    imp.generic_ids.iter().map(|t| (*t, tys.new_infer_ty())).collect();
                let imp_ty = tys.replace_ty(imp.imp_ty, &imp_replacements);
                let imp_trt = tys.replace_trait(&imp.imp_trt, &imp_replacements);

                if tys.union_ty_right(ty, imp_ty).is_ok() &&
                   tys.union_trait_right(&trt, &imp_trt).is_ok() &&
                   self.check_requirements(tys, &imp_replacements, &imp.reqs, depth - 1).is_ok() {
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
        self.fns.get(name).ok_or_else(|| panic!("")).map(|o| o.clone()) //ERROR
    }

    fn get_obj_fn_sigs(&self,
                       tys: &mut TypeSystem,
                       obj_ty: Ty,
                       name: &String,
                       is_member_fn: bool)
                       -> AnalyzeResult<(TraitId, Vec<FnSignature>)> {
        let mut sigs = Vec::new();
        let mut candidate_trt = None;

        for imp in &self.impls {
            if self.trait_has_function(imp.trait_id, name, is_member_fn) {
                if let Some(trait_ty) = self.match_ty_impl(tys, obj_ty, imp) {
                    let fn_sig = self.get_trait_function(tys, &trait_ty, name, is_member_fn);

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

    fn match_ty_impl(&self,
                     tys: &mut TypeSystem,
                     obj_ty: Ty,
                     imp: &AnalyzeImpl)
                     -> Option<AnalyzeTraitInstance> {
        // TODO: Result??
        let replacements: HashMap<_, _> =
            imp.generic_ids.iter().map(|t| (*t, tys.new_infer_ty())).collect();
        let repl_impl_ty = tys.replace_ty(imp.imp_ty, &replacements);

        if tys.union_ty_right(obj_ty, repl_impl_ty).is_err() {
            return None;
        }

        if self.check_requirements(tys, &replacements, &imp.reqs, MAX_IMPL_SEARCH_DEPTH).is_err() {
            return None;
        }

        // I don't believe I need to reset the checkpoint...
        Some(tys.replace_trait(&imp.imp_trt, &replacements))
    }

    fn initialize_object(&mut self,
                         tys: &mut TypeSystem,
                         obj: &AstObject)
                         -> AnalyzeResult<AnalyzeObject> {
        for generic in &obj.generics {
            if tys.obj_generics
                .insert(generic.clone(), TyVarId(tys.ty_var_id_count.next()))
                .is_some() {
                return Err(());
            }
        }

        let generic_ids: Vec<_> = obj.generics.iter().map(|t| tys.obj_generics[t]).collect();
        let mut member_ids = HashMap::new();
        let mut member_tys = Vec::new();

        for ref mem in &obj.members {
            if member_ids.contains_key(&mem.name) {
                return Err(());
            }

            let mem_id = member_tys.len() as u32;
            let mem_ty = tys.init_ty(self, &mem.member_type)?;
            member_tys.push(mem_ty);
            member_ids.insert(mem.name.clone(), mem_id);
        }

        let reqs = self.initialize_reqs(tys, &obj.restrictions)?;

        tys.obj_generics.clear();
        Ok(AnalyzeObject::new(obj.id, generic_ids, member_ids, member_tys, reqs))
    }

    fn initialize_object_fn_sig(&mut self, tys: &mut TypeSystem, fun: &AstObjectFnSignature) -> AnalyzeResult<FnSignature> {
        for generic in &fun.generics {
            if tys.fn_generics
                .insert(generic.clone(), TyVarId(tys.ty_var_id_count.next()))
                .is_some() {
                return Err(());
            }
        }

        let generic_ids: Vec<_> = fun.generics.iter().map(|t| tys.fn_generics[t]).collect();
        let params = map_vec(&fun.parameter_list, |p| tys.init_ty(self, &p.ty))?;
        let reqs = self.initialize_reqs(tys, &fun.restrictions)?;
        let return_ty = tys.init_ty(self, &fun.return_type)?;

        tys.fn_generics.clear();
        Ok(FnSignature::new(params, generic_ids, reqs, return_ty))
    }

    fn initialize_trait(&mut self,
                        tys: &mut TypeSystem,
                        trt: &AstTrait)
                        -> AnalyzeResult<AnalyzeTrait> {
        for generic in &trt.generics {
            if tys.obj_generics
                .insert(generic.clone(), TyVarId(tys.ty_var_id_count.next()))
                .is_some() {
                return Err(());
            }
        }

        let generic_ids: Vec<_> = trt.generics.iter().map(|t| tys.obj_generics[t]).collect();
        let mut mem_fns = HashMap::new();
        let mut static_fns = HashMap::new();

        for fun in &trt.functions {
            if mem_fns.contains_key(&fun.name) || static_fns.contains_key(&fun.name) {
                return Err(());
            }

            if fun.has_self {
                mem_fns.insert(fun.name.clone(), self.initialize_object_fn_sig(tys, fun)?);
            } else {
                static_fns.insert(fun.name.clone(), self.initialize_object_fn_sig(tys, fun)?);
            }
        }

        let reqs = self.initialize_reqs(tys, &trt.restrictions)?;

        tys.obj_generics.clear();
        Ok(AnalyzeTrait::new(trt.id, generic_ids, mem_fns, static_fns, reqs))
    }

    fn initialize_impl(&mut self, tys: &TypeSystem, imp: &AstImpl) -> AnalyzeResult<AnalyzeImpl> {
        unimplemented!();
    }

    fn initialize_reqs(&mut self,
                       tys: &mut TypeSystem,
                       restrictions: &Vec<AstTypeRestriction>)
                       -> AnalyzeResult<Vec<AnalyzeRequirement>> {
        let mut reqs = Vec::new();

        for res in restrictions {
            let ty = tys.init_ty(self, &res.ty)?;
            let ty_var = tys.get_ty_var(ty)?;
            let trt = tys.init_trait_instance(self, &res.trt)?;

            self.impls.push(AnalyzeImpl::dummy(ty, trt.clone()));
            reqs.push(AnalyzeRequirement::new(ty_var, trt));
        }

        Ok(reqs)
    }

    fn check_integrity_impl(&self, imp: &AnalyzeImpl) {
        unimplemented!();
    }

    pub fn get_object_info(&self, name: &String) -> Option<(ObjId, usize)> {
        self.obj_info.get(name).cloned()
    }

    pub fn get_trait_info(&self, name: &String) -> Option<(TraitId, usize)> {
        self.trt_info.get(name).cloned()
    }

    fn trait_has_function(&self, trt_id: TraitId, name: &String, member: bool) -> bool {
        if let Some(trt_skeleton) = self.trt_skeletons.get(&trt_id) {
            if member {
                trt_skeleton.member_fns.contains_key(name)
            } else {
                trt_skeleton.static_fns.contains_key(name)
            }
        } else {
            unreachable!();
        }
    }

    fn get_trait_function(&self,
                          tys: &mut TypeSystem,
                          trt: &AnalyzeTraitInstance,
                          name: &String,
                          member: bool)
                          -> FnSignature {
        let ref trt_skeleton = self.trt_skeletons[&trt.id];

        let fn_sig = if member {
            &trt_skeleton.member_fns[name]
        } else {
            &trt_skeleton.static_fns[name]
        };

        let replacements: HashMap<_, _> =
            trt_skeleton.generic_ids.iter().zip(&trt.generics).map(|(a, b)| (*a, *b)).collect();
        let repl_params: Vec<_> =
            fn_sig.params.iter().map(|t| tys.replace_ty(*t, &replacements)).collect();
        let repl_reqs: Vec<_> = fn_sig.reqs
            .iter()
            .map(|r| AnalyzeRequirement::new(r.ty_var, tys.replace_trait(&r.trt, &replacements)))
            .collect();
        let repl_return_ty = tys.replace_ty(fn_sig.return_ty, &replacements);

        FnSignature::new(repl_params,
                         fn_sig.generic_ids.clone(),
                         repl_reqs,
                         repl_return_ty)
    }

    pub fn get_generics_len(&self, trt: TraitId, fn_name: &String, member: bool) -> usize {
        let ref trt_skeleton = self.trt_skeletons[&trt];

        if member {
            trt_skeleton.member_fns[fn_name].generic_ids.len()
        } else {
            trt_skeleton.static_fns[fn_name].generic_ids.len()
        }
    }
}

fn map_vec<T, F, K, E>(vec: &Vec<T>, fun: F) -> Result<Vec<K>, E>
    where F: FnMut(&T) -> Result<K, E>
{
    vec.iter().map(fun).collect()
}

fn map_vec_mut<T, F, K, E>(vec: &mut Vec<T>, fun: F) -> Result<Vec<K>, E>
    where F: FnMut(&mut T) -> Result<K, E>
{
    vec.iter_mut().map(fun).collect()
}
