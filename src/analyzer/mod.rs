mod represent;

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

pub struct TypeSystem {
    fn_generics: HashMap<String, TyVarId>,
    obj_generics: HashMap<String, TyVarId>,
    ty_var_id_count: Counter,

    ty_id_count: Counter,
    tys: HashMap<Ty, AnalyzeType>,
    ty_history: HashMap<Ty, Option<AnalyzeType>>,
    in_snapshot: bool,
}

pub fn check_file(f: ParseFile, ana: &mut Analyzer, tys: &mut TypeSystem) -> AnalyzeResult<()> {
    let ParseFile { file, mut objects, functions, export_fns, mut traits, mut impls } = f;

    for obj in &mut objects {
        obj.id = ObjId(ana.obj_id_count.next());
        ana.obj_info.insert(obj.name.clone(), (obj.id, obj.generics.len()));
        ana.obj_names.insert(obj.id, obj.name.clone());
    }

    for trt in &mut traits {
        trt.id = TraitId(ana.trt_id_count.next());
        ana.trt_info.insert(trt.name.clone(), (trt.id, trt.generics.len()));
        // TODO: check for conflicts with objects too..
        ana.trt_names.insert(trt.id, trt.name.clone());
    }

    for trt in &traits {
        let analyze_trt = initialize_trait(ana, tys, trt)?;
        ana.trt_skeletons.insert(trt.id, analyze_trt);
    }

    for obj in &objects {
        let analyze_obj = initialize_object(ana, tys, obj)?;
        ana.obj_skeletons.insert(obj.id, analyze_obj);
    }

    for imp in &impls {
        let analyze_impl = initialize_impl(ana, tys, imp)?;
        ana.impls.push(analyze_impl);
    }

    //for obj in &self.obj_skeletons {
    //
    //}

    //for trt in &self.trt_skeletons {
    //
    //}

    for imp in &ana.impls {
        check_integrity_impl(ana, tys, imp)?;
    }

    // Initialize funs, checking integrity

    // Check impl

    // Check fun

    Ok(())
}

fn check_expr(ana: &Analyzer,
              tys: &mut TypeSystem,
              node: &mut AstExpression,
              expect_ty: Option<Ty>)
              -> AnalyzeResult<Ty> {
    let &mut AstExpression { ref mut expr, ref mut ty, pos } = node;

    *ty = match expr {
        &mut AstExpressionData::Call { ref name, ref generics, ref mut args } => {
            let fn_sig = get_fn_sig(ana, name)?;
            // TODO: store generics
            let mut gen_tys = map_vec(generics, |t| init_ty(ana, tys, t))?;
            let arg_tys = map_vec_mut(args, |e| check_expr(ana, tys, e, None))?;
            check_fn(ana, tys, &fn_sig, &mut gen_tys, &arg_tys, expect_ty)?
        }
        &mut AstExpressionData::ObjectCall { ref mut object,
                                             ref fn_name,
                                             ref generics,
                                             ref mut args } => {
            let obj_ty = check_expr(ana, tys, object, None)?;
            // TODO: store  generics
            let (trait_id, fn_sigs) = get_obj_fn_sigs(ana, tys, obj_ty, fn_name, true)?; //true = member
            let mut gen_tys = map_vec(generics, |t| init_ty(ana, tys, t))?;

            if generics.len() == 0 {
                for _ in 0..get_generics_len(ana, trait_id, fn_name, true) {
                    gen_tys.push(new_infer_ty(tys));
                }
            } else if generics.len() != get_generics_len(ana, trait_id, fn_name, true) {
                return Err(());
            }

            let arg_tys = map_vec_mut(args, |e| check_expr(ana, tys, e, None))?;
            check_fns(ana, tys, &fn_sigs, &mut gen_tys, &arg_tys, expect_ty)?
        }
        &mut AstExpressionData::StaticCall { ref obj_name,
                                             ref obj_generics,
                                             ref fn_name,
                                             ref fn_generics,
                                             ref mut args } => {
            let obj_gen_tys = map_vec(obj_generics, |t| init_ty(ana, tys, t))?;
            let obj_aty = make_ident_ty(ana, tys, obj_name, obj_gen_tys)?;
            let obj_ty = register_ty(tys, obj_aty); //TODO: ugly
            let (trait_id, fn_sigs) = get_obj_fn_sigs(ana, tys, obj_ty, fn_name, false)?; //false = static
            //TODO: store generics (for both...)
            let mut fn_gen_tys = map_vec(fn_generics, |t| init_ty(ana, tys, t))?;

            if fn_generics.len() == 0 {
                for _ in 0..get_generics_len(ana, trait_id, fn_name, false) {
                    fn_gen_tys.push(new_infer_ty(tys));
                }
            } else if fn_generics.len() != get_generics_len(ana, trait_id, fn_name, false) {
                panic!(); //TODO: error
            }

            let arg_tys = map_vec_mut(args, |e| check_expr(ana, tys, e, None))?;
            check_fns(ana, tys, &fn_sigs, &mut fn_gen_tys, &arg_tys, expect_ty)?
        }
        _ => unimplemented!(),
    };

    Ok(*ty)
}

fn check_fn(ana: &Analyzer,
            tys: &mut TypeSystem,
            fn_sig: &FnSignature,
            generics: &mut Vec<Ty>,
            args: &Vec<Ty>,
            return_hint: Option<Ty>)
            -> AnalyzeResult<Ty> {
    if generics.len() == 0 && fn_sig.generic_ids.len() != 0 {
        for _ in 0..fn_sig.generic_ids.len() {
            generics.push(new_infer_ty(tys));
        }
    }

    if generics.len() != fn_sig.generic_ids.len() {
        panic!(""); //ERROR
    }

    let replacements: HashMap<_, _> =
        fn_sig.generic_ids.iter().zip(generics).map(|(a, b)| (*a, *b)).collect();

    for (expect_ty, arg_ty) in fn_sig.params.iter().zip(args) {
        let repl_expect_ty = replace_ty(tys, *expect_ty, &replacements);

        union_ty(tys, repl_expect_ty, *arg_ty);
    }

    let repl_return_ty = replace_ty(tys, fn_sig.return_ty, &replacements);

    if let Some(expect_return_ty) = return_hint {
        union_ty(tys, expect_return_ty, repl_return_ty)?;
    }

    check_requirements(ana, tys, &replacements, &fn_sig.reqs, MAX_IMPL_SEARCH_DEPTH)?;
    Ok(repl_return_ty)
}

fn check_fns(ana: &Analyzer,
             tys: &mut TypeSystem,
             fn_sigs: &Vec<FnSignature>,
             generics: &mut Vec<Ty>,
             args: &Vec<Ty>,
             return_hint: Option<Ty>)
             -> AnalyzeResult<Ty> {
    let mut candidate_fn = None;

    for fn_sig in fn_sigs {
        set_ty_checkpoint(tys);
        let check_result = check_fn(ana, tys, fn_sig, generics, args, return_hint);

        if check_result.is_ok() {
            if candidate_fn.is_some() {
                reset_ty_checkpoint(tys);
                return Err(());
            }

            candidate_fn = Some(fn_sig);
        }

        reset_ty_checkpoint(tys);
    }

    if candidate_fn.is_none() {
        return Err(());
    }

    check_fn(ana, tys, candidate_fn.unwrap(), generics, args, return_hint)
}

fn check_integrity_obj_ty(ana: &Analyzer, tys: &mut TypeSystem, obj_id: ObjId, gen_tys: &Vec<Ty>) -> AnalyzeResult<()> {
    for ty in gen_tys {
        check_integrity_ty(ana, tys, *ty)?;
    }

    let obj_skeleton = &ana.obj_skeletons[&obj_id];
    let replacements: HashMap<_, _> = obj_skeleton.generic_ids.iter().zip(gen_tys).map(|(a, b)| (*a, *b)).collect();
    check_requirements(ana, tys, &replacements, &obj_skeleton.reqs, MAX_IMPL_SEARCH_DEPTH)
}

fn check_integrity_trait_ty(ana: &Analyzer, tys: &mut TypeSystem, trt: &AnalyzeTraitInstance) -> AnalyzeResult<()> {
    for ty in &trt.generics {
        check_integrity_ty(ana, tys, *ty)?;
    }

    let trt_skeleton = &ana.trt_skeletons[&trt.id];
    let replacements: HashMap<_, _> = trt_skeleton.generic_ids.iter().zip(&trt.generics).map(|(a, b)| (*a, *b)).collect();
    check_requirements(ana, tys, &replacements, &trt_skeleton.reqs, MAX_IMPL_SEARCH_DEPTH)
}

fn check_requirements(ana: &Analyzer,
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
        let trt = replace_trait(tys, &req.trt, replacements);
        let trait_id = trt.id; //TODO: give name?

        let mut satisfied = false;

        for imp in &ana.impls {
            if imp.trait_id != trait_id {
                continue;
            }

            let imp_replacements: HashMap<_, _> =
                imp.generic_ids.iter().map(|t| (*t, new_infer_ty(tys))).collect();
            let imp_ty = replace_ty(tys, imp.imp_ty, &imp_replacements);
            let imp_trt = replace_trait(tys, &imp.imp_trt, &imp_replacements);

            if union_ty_right(tys, ty, imp_ty).is_ok() &&
               union_trait_right(tys, &trt, &imp_trt).is_ok() &&
               check_requirements(ana, tys, &imp_replacements, &imp.reqs, depth - 1).is_ok() {
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

fn get_fn_sig(ana: &Analyzer, name: &String) -> AnalyzeResult<FnSignature> {
    ana.fns.get(name).ok_or_else(|| panic!("")).map(|o| o.clone()) //ERROR
}

fn get_obj_fn_sigs(ana: &Analyzer,
                   tys: &mut TypeSystem,
                   obj_ty: Ty,
                   name: &String,
                   is_member_fn: bool)
                   -> AnalyzeResult<(TraitId, Vec<FnSignature>)> {
    let mut sigs = Vec::new();
    let mut candidate_trt = None;

    for imp in &ana.impls {
        if trait_has_function(ana, imp.trait_id, name, is_member_fn) {
            if let Some(trait_ty) = match_ty_impl(ana, tys, obj_ty, imp) {
                let fn_sig = get_trait_function(ana, tys, &trait_ty, name, is_member_fn);

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

fn match_ty_impl(ana: &Analyzer,
                 tys: &mut TypeSystem,
                 obj_ty: Ty,
                 imp: &AnalyzeImpl)
                 -> Option<AnalyzeTraitInstance> {
    // TODO: Result??
    let replacements: HashMap<_, _> =
        imp.generic_ids.iter().map(|t| (*t, new_infer_ty(tys))).collect();
    let repl_impl_ty = replace_ty(tys, imp.imp_ty, &replacements);

    if union_ty_right(tys, obj_ty, repl_impl_ty).is_err() {
        return None;
    }

    if check_requirements(ana, tys, &replacements, &imp.reqs, MAX_IMPL_SEARCH_DEPTH).is_err() {
        return None;
    }

    // I don't believe I need to reset the checkpoint...
    Some(replace_trait(tys, &imp.imp_trt, &replacements))
}

fn initialize_object(ana: &mut Analyzer,
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
        let mem_ty = init_ty(ana, tys, &mem.member_type)?;
        member_tys.push(mem_ty);
        member_ids.insert(mem.name.clone(), mem_id);
    }

    let reqs = initialize_reqs(ana, tys, &obj.restrictions)?;

    tys.obj_generics.clear();
    Ok(AnalyzeObject::new(obj.id, generic_ids, member_ids, member_tys, reqs))
}

fn initialize_object_fn_sig(ana: &mut Analyzer,
                            tys: &mut TypeSystem,
                            fun: &AstObjectFnSignature)
                            -> AnalyzeResult<FnSignature> {
    for generic in &fun.generics {
        if tys.fn_generics
            .insert(generic.clone(), TyVarId(tys.ty_var_id_count.next()))
            .is_some() {
            return Err(());
        }
    }

    let generic_ids: Vec<_> = fun.generics.iter().map(|t| tys.fn_generics[t]).collect();
    let params = map_vec(&fun.parameter_list, |p| init_ty(ana, tys, &p.ty))?;
    let reqs = initialize_reqs(ana, tys, &fun.restrictions)?;
    let return_ty = init_ty(ana, tys, &fun.return_type)?;

    tys.fn_generics.clear();
    Ok(FnSignature::new(params, generic_ids, reqs, return_ty))
}

fn initialize_trait(ana: &mut Analyzer,
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
            mem_fns.insert(fun.name.clone(), initialize_object_fn_sig(ana, tys, fun)?);
        } else {
            static_fns.insert(fun.name.clone(), initialize_object_fn_sig(ana, tys, fun)?);
        }
    }

    let reqs = initialize_reqs(ana, tys, &trt.restrictions)?;

    tys.obj_generics.clear();
    Ok(AnalyzeTrait::new(trt.id, generic_ids, mem_fns, static_fns, reqs))
}

fn initialize_impl(ana: &mut Analyzer,
                   tys: &mut TypeSystem,
                   imp: &AstImpl)
                   -> AnalyzeResult<AnalyzeImpl> {
    for generic in &imp.generics {
        if tys.obj_generics
            .insert(generic.clone(), TyVarId(tys.ty_var_id_count.next()))
            .is_some() {
            return Err(());
        }
    }

    let generic_ids: Vec<_> = imp.generics.iter().map(|t| tys.obj_generics[t]).collect();
    let imp_ty = init_ty(ana, tys, &imp.impl_ty)?;
    let imp_trt = init_trait_instance(ana, tys, &imp.trait_ty)?;
    let reqs = initialize_reqs(ana, tys, &imp.restrictions)?;

    tys.obj_generics.clear();
    Ok(AnalyzeImpl::new(imp_ty, imp_trt, generic_ids, reqs))
}

fn initialize_reqs(ana: &mut Analyzer,
                   tys: &mut TypeSystem,
                   restrictions: &Vec<AstTypeRestriction>)
                   -> AnalyzeResult<Vec<AnalyzeRequirement>> {
    let mut reqs = Vec::new();

    for res in restrictions {
        let ty = init_ty(ana, tys, &res.ty)?;
        let ty_var = get_ty_var(tys, ty)?;
        let trt = init_trait_instance(ana, tys, &res.trt)?;

        ana.impls.push(AnalyzeImpl::dummy(ty, trt.clone()));
        reqs.push(AnalyzeRequirement::new(ty_var, trt));
    }

    Ok(reqs)
}

fn check_integrity_impl(ana: &Analyzer, tys: &mut TypeSystem, imp: &AnalyzeImpl) -> AnalyzeResult<()> {
    let ref trt = ana.trt_skeletons[&imp.trait_id];

    check_integrity_ty(ana, tys, imp.imp_ty)?;
    check_integrity_trait_ty(ana, tys, &imp.imp_trt)?;

    Ok(())
}

//TODO: useless?
fn get_object_info(ana: &Analyzer, name: &String) -> Option<(ObjId, usize)> {
    ana.obj_info.get(name).cloned()
}

fn get_trait_info(ana: &Analyzer, name: &String) -> Option<(TraitId, usize)> {
    ana.trt_info.get(name).cloned()
}

fn trait_has_function(ana: &Analyzer, trt_id: TraitId, name: &String, member: bool) -> bool {
    if let Some(trt_skeleton) = ana.trt_skeletons.get(&trt_id) {
        if member {
            trt_skeleton.member_fns.contains_key(name)
        } else {
            trt_skeleton.static_fns.contains_key(name)
        }
    } else {
        unreachable!();
    }
}

fn get_trait_function(ana: &Analyzer,
                      tys: &mut TypeSystem,
                      trt: &AnalyzeTraitInstance,
                      name: &String,
                      member: bool)
                      -> FnSignature {
    let ref trt_skeleton = ana.trt_skeletons[&trt.id];

    let fn_sig = if member {
        &trt_skeleton.member_fns[name]
    } else {
        &trt_skeleton.static_fns[name]
    };

    let replacements: HashMap<_, _> =
        trt_skeleton.generic_ids.iter().zip(&trt.generics).map(|(a, b)| (*a, *b)).collect();
    let repl_params: Vec<_> =
        fn_sig.params.iter().map(|t| replace_ty(tys, *t, &replacements)).collect();
    let repl_reqs: Vec<_> = fn_sig.reqs
        .iter()
        .map(|r| AnalyzeRequirement::new(r.ty_var, replace_trait(tys, &r.trt, &replacements)))
        .collect();
    let repl_return_ty = replace_ty(tys, fn_sig.return_ty, &replacements);

    FnSignature::new(repl_params,
                     fn_sig.generic_ids.clone(),
                     repl_reqs,
                     repl_return_ty)
}

fn get_generics_len(ana: &Analyzer, trt: TraitId, fn_name: &String, member: bool) -> usize {
    let ref trt_skeleton = ana.trt_skeletons[&trt];

    if member {
        trt_skeleton.member_fns[fn_name].generic_ids.len()
    } else {
        trt_skeleton.static_fns[fn_name].generic_ids.len()
    }
}

fn init_ty(ana: &Analyzer, tys: &mut TypeSystem, ty: &AstType) -> AnalyzeResult<Ty> {
    let aty = match ty {
        &AstType::Infer => AnalyzeType::Infer,
        &AstType::None => AnalyzeType::Nothing,
        &AstType::Int => AnalyzeType::Int,
        &AstType::UInt => AnalyzeType::UInt,
        &AstType::Float => AnalyzeType::Float,
        &AstType::Char => AnalyzeType::Char,
        &AstType::Bool => AnalyzeType::Boolean,
        &AstType::String => AnalyzeType::String,
        &AstType::Array { ref ty } => AnalyzeType::Array(init_ty(ana, tys, ty)?),
        &AstType::Tuple { ref types } => {
            let tys = map_vec(types, |t| init_ty(ana, tys, t))?;
            AnalyzeType::Tuple(tys)
        }
        &AstType::Object(ref name, ref generics, pos) => {
            let gen_tys = map_vec(generics, |t| init_ty(ana, tys, t))?;
            make_ident_ty(ana, tys, name, gen_tys)? //TODO: unify in a better way
        }
    };

    Ok(register_ty(tys, aty))
}

fn make_ident_ty(ana: &Analyzer, tys: &mut TypeSystem,
                     name: &String,
                     mut generics: Vec<Ty>)
                     -> AnalyzeResult<AnalyzeType> {
    if tys.fn_generics.contains_key(name) {
        if generics.len() != 0 {
            return Err(());
        }

        let ty_var = tys.fn_generics[name];
        return Ok(AnalyzeType::TypeVariable(ty_var));
    }

    if tys.obj_generics.contains_key(name) {
        if generics.len() != 0 {
            return Err(());
        }

        let ty_var = tys.obj_generics[name];
        return Ok(AnalyzeType::TypeVariable(ty_var));
    }

    if let Some((obj_id, generics_len)) = get_object_info(ana, name) {
        if generics.len() != generics_len {
            if generics.len() != 0 {
                return Err(());
            }

            for _ in 0..generics_len {
                generics.push(new_infer_ty(tys));
            }
        }

        Ok(AnalyzeType::Object(obj_id, generics))
    } else {
        // TODO: error for trait?
        Err(())
    }
}

fn init_trait_instance(ana: &Analyzer, tys: &mut TypeSystem,
                           ty: &AstType)
                           -> AnalyzeResult<AnalyzeTraitInstance> {
    match ty {
        &AstType::Object(ref name, ref generics, pos) => {
            let mut gen_tys = map_vec(generics, |t| init_ty(ana, tys, t))?;
            let (id, generics_len) = get_trait_info(ana, name).ok_or_else(|| ())?;
            if gen_tys.len() != generics_len {
                return Err(());
            }
            Ok(AnalyzeTraitInstance {
                // TODO: new
                id: id,
                generics: gen_tys,
            })
        }
        _ => Err(()),
    }
}

fn new_infer_ty(tys: &mut TypeSystem) -> Ty {
    register_ty(tys, AnalyzeType::Infer)
}

fn register_ty(tys: &mut TypeSystem, aty: AnalyzeType) -> Ty {
    let id = Ty(tys.ty_id_count.next());
    tys.tys.insert(id, aty);

    if tys.in_snapshot {
        tys.ty_history.insert(id, None);
    }

    id
}

fn set_ty(tys: &mut TypeSystem, ty: Ty, aty: AnalyzeType) {
    let old = tys.tys.insert(ty, aty);

    if tys.in_snapshot && !tys.ty_history.contains_key(&ty) {
        tys.ty_history.insert(ty, old); //OMG, 10/10
    }
}

fn set_ty_checkpoint(tys: &mut TypeSystem) -> AnalyzeResult<()> {
    if tys.in_snapshot {
        return Err(());
    }

    tys.in_snapshot = true;
    Ok(())
}

fn reset_ty_checkpoint(tys: &mut TypeSystem) -> AnalyzeResult<()> {
    tys.in_snapshot = false;

    for (id, old) in tys.ty_history.drain() {
        if let Some(old_ty) = old {
            tys.tys.insert(id, old_ty);
        } else {
            // None, remove.
            tys.tys.remove(&id);
        }
    }

    Ok(())
}

fn replace_ty(tys: &mut TypeSystem, ty: Ty, replacements: &HashMap<TyVarId, Ty>) -> Ty {
    let repl_ty = match tys.tys[&ty].clone() { //TODO: this is bad rust. I can definitely not copy the vecs twice...
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
                .map(|t| replace_ty(tys, t, replacements))
                .collect())
        }
        AnalyzeType::Array(inner_ty) => {
            AnalyzeType::Array(replace_ty(tys, inner_ty, replacements))
        }
        AnalyzeType::Object(obj_id, generics) => {
            AnalyzeType::Object(obj_id,
                                generics.into_iter()
                                    .map(|t| replace_ty(tys, t, replacements))
                                    .collect())
        }
        AnalyzeType::TypeVariable(var_id) => {
            if replacements.contains_key(&var_id) {
                AnalyzeType::Same(replacements[&var_id])
            } else {
                AnalyzeType::TypeVariable(var_id)
            }
        }
        AnalyzeType::Same(same_ty) => AnalyzeType::Same(replace_ty(tys, same_ty, replacements)),
    };

    register_ty(tys, repl_ty)
}

fn replace_trait(tys: &mut TypeSystem,
                     trt: &AnalyzeTraitInstance,
                     replacements: &HashMap<TyVarId, Ty>)
                     -> AnalyzeTraitInstance {
    AnalyzeTraitInstance {
        id: trt.id,
        generics: trt.generics.iter().map(|t| replace_ty(tys, *t, replacements)).collect(),
    }
}

fn union_ty(tys: &mut TypeSystem, ty1: Ty, ty2: Ty) -> AnalyzeResult<()> {
    if ty1 == ty2 {
        return Ok(());
    }

    // If ty1 is Same, then union the referenced type instead
    if let AnalyzeType::Same(ty1_same) = tys.tys[&ty1] {
        return union_ty(tys, ty1_same, ty2);
    }

    // If ty2 is Same, then union the referenced type instead
    if let AnalyzeType::Same(ty2_same) = tys.tys[&ty2] {
        return union_ty(tys, ty1, ty2_same);
    }

    match (tys.tys[&ty1].clone(), tys.tys[&ty2].clone()) { //TODO: :(
        (AnalyzeType::Infer, _) => {
            set_ty(tys, ty1, AnalyzeType::Same(ty2));
        }
        (_, AnalyzeType::Infer) => {
            set_ty(tys, ty2, AnalyzeType::Same(ty1));
        }
        // NullInfer can union with any *nullable* type
        (AnalyzeType::NullInfer, t) => {
            if !is_nullable(&t) {
                panic!(""); //ERROR
            }
            set_ty(tys, ty1, AnalyzeType::Same(ty2));
        }
        (t, AnalyzeType::NullInfer) => {
            if !is_nullable(&t) {
                panic!(""); //ERROR
            }
            set_ty(tys, ty2, AnalyzeType::Same(ty1));
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
                union_ty(tys, ty1_tys[i], ty2_tys[i])?;
            }
        }
        // Arrays union if their inner types union as well
        (AnalyzeType::Array(inner_ty1), AnalyzeType::Array(inner_ty2)) => {
            union_ty(tys, inner_ty1, inner_ty2)?;
        }
        // Object types
        (AnalyzeType::Object(obj_ty1, generics1), AnalyzeType::Object(obj_ty2, generics2)) => {
            if obj_ty1 != obj_ty2 {
                panic!(""); //ERROR
            }

            for (gen_ty1, gen_ty2) in generics1.iter().zip(generics2) {
                union_ty(tys, *gen_ty1, gen_ty2)?;
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

fn union_ty_right(tys: &mut TypeSystem, ty1: Ty, ty2: Ty) -> AnalyzeResult<()> {
    if ty1 == ty2 {
        return Ok(());
    }

    // If ty1 is Same, then union the referenced type instead
    if let AnalyzeType::Same(ty1_same) = tys.tys[&ty1] {
        return union_ty_right(tys, ty1_same, ty2);
    }

    // If ty2 is Same, then union the referenced type instead
    if let AnalyzeType::Same(ty2_same) = tys.tys[&ty2] {
        return union_ty_right(tys, ty1, ty2_same);
    }

    match (tys.tys[&ty1].clone(), tys.tys[&ty2].clone()) { //TODO: :(
        (_, AnalyzeType::Infer) => {
            set_ty(tys, ty2, AnalyzeType::Same(ty1));
        }
        (t, AnalyzeType::NullInfer) => {
            if !is_nullable(&t) {
                panic!(""); //ERROR
            }
            set_ty(tys, ty2, AnalyzeType::Same(ty1));
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
                union_ty_right(tys, ty1_tys[i], ty2_tys[i])?;
            }
        }
        // Arrays union if their inner types union as well
        (AnalyzeType::Array(inner_ty1), AnalyzeType::Array(inner_ty2)) => {
            union_ty_right(tys, inner_ty1, inner_ty2)?;
        }
        // Object types
        (AnalyzeType::Object(obj_ty1, generics1), AnalyzeType::Object(obj_ty2, generics2)) => {
            if obj_ty1 != obj_ty2 {
                panic!(""); //ERROR
            }

            for (gen_ty1, gen_ty2) in generics1.iter().zip(generics2) {
                union_ty_right(tys, *gen_ty1, gen_ty2)?;
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

fn union_trait_right(tys: &mut TypeSystem,
                         trt1: &AnalyzeTraitInstance,
                         trt2: &AnalyzeTraitInstance)
                         -> AnalyzeResult<()> {
    if trt1.id != trt2.id {
        Err(())
    } else {
        for (ty1, ty2) in trt1.generics.iter().zip(trt2.generics.iter()) {
            union_ty_right(tys, *ty1, *ty2)?;
        }

        Ok(())
    }
}

fn check_integrity_ty(ana: &Analyzer, tys: &mut TypeSystem, ty: Ty) -> AnalyzeResult<()> {
    match tys.tys[&ty].clone() {
        AnalyzeType::Infer => Err(()),
        AnalyzeType::NullInfer => Err(()),
        AnalyzeType::Nothing |
        AnalyzeType::Boolean |
        AnalyzeType::Int |
        AnalyzeType::UInt |
        AnalyzeType::Float |
        AnalyzeType::Char |
        AnalyzeType::String |
        AnalyzeType::TypeVariable(..) => {
            Ok(())
        }
        AnalyzeType::Tuple(tuple_tys) => {
            for tuple_ty in tuple_tys {
                check_integrity_ty(ana, tys, tuple_ty)?;
            }

            Ok(())
        }
        AnalyzeType::Array(inner_ty) => check_integrity_ty(ana, tys, inner_ty),
        AnalyzeType::Object(obj_id, gen_tys) => check_integrity_obj_ty(ana, tys, obj_id, &gen_tys),
        AnalyzeType::Same(same_ty) => check_integrity_ty(ana, tys, same_ty),
    }
}

fn is_nullable(ty: &AnalyzeType) -> bool {
    match ty {
        &AnalyzeType::NullInfer |
        &AnalyzeType::String |
        &AnalyzeType::Array(_) |
        &AnalyzeType::Object(..) => true,
        &AnalyzeType::Same(_) => unreachable!(),
        _ => false,
    }
}

fn get_ty_var(tys: &TypeSystem, ty: Ty) -> AnalyzeResult<TyVarId> {
    match &tys.tys[&ty] {
        &AnalyzeType::TypeVariable(ty_var) => Ok(ty_var),
        &AnalyzeType::Same(same_ty) => get_ty_var(tys, same_ty),
        _ => Err(()),
    }
}

fn map_vec<T, F, K, E>(vec: &Vec<T>, fun: F) -> Result<Vec<K>, E>
    where F: FnMut(&T) -> Result<K, E> {
    vec.iter().map(fun).collect()
}

fn map_vec_mut<T, F, K, E>(vec: &mut Vec<T>, fun: F) -> Result<Vec<K>, E>
    where F: FnMut(&mut T) -> Result<K, E> {
    vec.iter_mut().map(fun).collect()
}
