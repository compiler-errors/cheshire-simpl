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
    obj_ids: HashMap<String, ObjId>,
    obj_names: HashMap<ObjId, String>, // TODO: possible not necessary (merge into AnalyzeObject)
    obj_skeletons: HashMap<ObjId, AnalyzeObject>,

    trt_id_count: Counter,
    trt_ids: HashMap<String, TraitId>,
    trt_names: HashMap<TraitId, String>, // TODO: possible not necessary (merge into AnalyzeTrait)
    trt_skeletons: HashMap<TraitId, AnalyzeTrait>,

    impls: Vec<AnalyzeImpl>, // TODO: possible make a HashMap<TraitId, Vec<AnalyzeImpl>> instead?
}

impl Analyzer {
    fn check_file(&mut self, f: ParseFile, tys: &mut TypeSystem) {
        let ParseFile { file, mut objects, functions, export_fns, mut traits, mut impls } = f;

        for obj in &mut objects {
            obj.id = ObjId(self.obj_id_count.next());
            self.obj_ids.insert(obj.name.clone(), obj.id);
            self.obj_names.insert(obj.id, obj.name.clone());
        }

        for trt in &mut traits {
            trt.id = TraitId(self.trt_id_count.next());
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

        for imp in &self.impls {
            self.check_integrity_impl(imp);
        }
    }

    fn check_expr(&self,
                  tys: &mut TypeSystem,
                  node: &mut AstExpression,
                  expect_ty: Option<Ty>)
                  -> AnalyzeResult<Ty> {
        let &mut AstExpression { ref mut expr, ref mut ty, pos } = node;

        *ty = match expr {
            &mut AstExpressionData::Call { ref name, ref mut generics, ref mut args } => {
                let fn_sig = self.get_fn_sig(name)?;
                // TODO: store generics
                let mut gen_tys: Vec<_> = map_vec(generics, |t| tys.init_ty(t));
                let arg_tys: Vec<_> = map_vec_unwrap(args, |e| self.check_expr(tys, e, None))?;
                self.check_fn(tys, &fn_sig, &mut gen_tys, &arg_tys, expect_ty)?
            }
            &mut AstExpressionData::ObjectCall { ref mut object,
                                                 ref fn_name,
                                                 ref generics,
                                                 ref mut args } => {
                let obj_ty = self.check_expr(tys, object, None)?;
                // TODO: store  generics
                let (trait_id, fn_sigs) = self.get_obj_fn_sigs(tys, obj_ty, fn_name, true)?; //true = member
                let mut gen_tys: Vec<_> = map_vec(generics, |t| tys.init_ty(t));

                if generics.len() == 0 {
                    for _ in 0..self.get_generics_len(trait_id, fn_name) {
                        gen_tys.push(tys.new_infer_ty());
                    }
                } else if generics.len() != self.get_generics_len(trait_id, fn_name) {
                    panic!(); //TODO: error
                }

                let arg_tys: Vec<_> = map_vec_unwrap(args, |e| self.check_expr(tys, e, None))?;
                self.check_fns(tys, &fn_sigs, &mut gen_tys, &arg_tys, expect_ty)?
            }
            &mut AstExpressionData::StaticCall { ref obj_name,
                                                 ref mut obj_generics,
                                                 ref fn_name,
                                                 ref mut fn_generics,
                                                 ref mut args } => {
                let mut obj_gen_tys: Vec<_> = map_vec(obj_generics, |t| tys.init_ty(t));
                let obj_ty = tys.make_ident_ty(self, obj_name, obj_gen_tys)?;
                let (trait_id, fn_sigs) = self.get_obj_fn_sigs(tys, obj_ty, fn_name, false)?; //false = static
                //TODO: store generics (for both...)
                let mut fn_gen_tys: Vec<_> = map_vec(fn_generics, |t| tys.init_ty(t));

                if fn_generics.len() == 0 {
                    for _ in 0..self.get_generics_len(trait_id, fn_name) {
                        fn_gen_tys.push(tys.new_infer_ty());
                    }
                } else if fn_generics.len() != self.get_generics_len(trait_id, fn_name) {
                    panic!(); //TODO: error
                }

                let arg_tys: Vec<_> = map_vec_unwrap(args, |e| self.check_expr(tys, e, None))?;
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
            let trt = tys.replace_ty(req.trt, replacements);
            let trait_id = tys.get_trait_id(trt);

            let mut satisfied = false;

            for imp in &self.impls {
                if imp.trait_id != trait_id {
                    continue;
                }

                let imp_replacements: HashMap<_, _> =
                    imp.generic_ids.iter().map(|t| (*t, tys.new_infer_ty())).collect();
                let imp_ty = tys.replace_ty(imp.imp_ty, &imp_replacements);
                let imp_trt = tys.replace_ty(imp.imp_trt, &imp_replacements);

                if tys.union_ty_right(ty, imp_ty).is_ok() &&
                   tys.union_ty_right(trt, imp_trt).is_ok() &&
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

    fn match_ty_impl(&self, tys: &mut TypeSystem, obj_ty: Ty, imp: &AnalyzeImpl) -> Option<Ty> {
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
        Some(tys.replace_ty(imp.imp_trt, &replacements))
    }

    fn initialize_object(&self, obj: &AstObject) -> AnalyzeObject {
        unimplemented!();
    }

    fn initialize_object_fn_sig(&self, fun: &AstObjectFnSignature) -> FnSignature {
        unimplemented!();
    }

    fn initialize_trait(&self, trt: &AstTrait) -> AnalyzeTrait {
        // for generic in trt.generics {
        // if self.obj_generics.insert(generic, self.ty_id_count.next()).is_some() {
        // panic!(""); //ERROR
        // }
        // }
        //
        // let generic_ids: Vec<_> = trt.generics.iter().map(|t| self.obj_generics[t]).collect();
        // let mem_fns = HashMap::new();
        // let static_fns = HashMap::new();
        //
        // for fun in &trt.functions {
        // if mem_fns.contains_key(&fun.name) || static_fns.contains_key(&fun.name) {
        // panic!(""); //ERROR
        // }
        //
        // if fun.has_self { &mem_fns } else { &static_fns }
        // .insert(fun.name.clone(), self.initialize_object_fn_sig(fun));
        // }
        //
        // unimplemented!(); //TODO: add dummy impls
        //
        // self.obj_generics.clear();
        // AnalyzeTrait::new(trt.id, generic_ids, mem_fns, static_fns)
        unimplemented!();
    }

    fn initialize_impl(&mut self, imp: &AstImpl) -> AnalyzeImpl {
        unimplemented!();
    }

    fn check_integrity_impl(&self, imp: &AnalyzeImpl) {
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
}

fn map_vec<T, F, K>(vec: &Vec<T>, fun: F) -> Vec<K>
    where F: FnMut(&T) -> K
{
    vec.iter().map(fun).collect()
}

fn map_vec_unwrap<T, F, K, E>(vec: &mut Vec<T>, fun: F) -> Result<Vec<K>, E>
    where F: FnMut(&mut T) -> Result<K, E>
{
    vec.iter_mut().map(fun).collect()
}
