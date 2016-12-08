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
    fns: HashMap<String, AstFunction>,
    fn_sigs: HashMap<String, FnSignature>,

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
    return_ty: Ty,
    breakable: bool,

    fn_generics: HashMap<String, TyVarId>,
    obj_generics: HashMap<String, TyVarId>,
    ty_var_id_count: Counter,

    var_id_count: Counter,
    var_ids: Vec<HashMap<String, VarId>>,
    var_tys: HashMap<VarId, Ty>,

    str_id_count: Counter,
    strings: HashMap<StringId, (String, u32)>,

    ty_id_count: Counter,
    tys: HashMap<Ty, AnalyzeType>,
    ty_history: HashMap<Ty, Option<AnalyzeType>>,
    in_snapshot: bool,
}

pub fn analyze_file(f: ParseFile) {
    let mut ana = Analyzer {
        fns: HashMap::new(),
        fn_sigs: HashMap::new(),
        obj_id_count: Counter::new(1),
        obj_info: HashMap::new(),
        obj_names: HashMap::new(),
        obj_skeletons: HashMap::new(),
        trt_id_count: Counter::new(1),
        trt_info: HashMap::new(),
        trt_names: HashMap::new(),
        trt_skeletons: HashMap::new(),
        impls: Vec::new()
    };

    let mut ty_map = HashMap::new();
    // Insert all of the "basic" fundamental types
    ty_map.insert(TY_NOTHING, AnalyzeType::Nothing);
    ty_map.insert(TY_BOOLEAN, AnalyzeType::Boolean);
    ty_map.insert(TY_INT, AnalyzeType::Int);
    ty_map.insert(TY_UINT, AnalyzeType::UInt);
    ty_map.insert(TY_FLOAT, AnalyzeType::Float);
    ty_map.insert(TY_CHAR, AnalyzeType::Char);
    ty_map.insert(TY_STRING, AnalyzeType::String);

    let mut tys = TypeSystem {
        return_ty: Ty(0),
        breakable: false,
        fn_generics: HashMap::new(),
        obj_generics: HashMap::new(),
        ty_var_id_count: Counter::new(1),
        var_id_count: Counter::new(1),
        var_ids: Vec::new(),
        var_tys: HashMap::new(),
        str_id_count: Counter::new(1),
        strings: HashMap::new(),
        ty_id_count: Counter::new(TY_FIRST_NEW_ID),
        tys: ty_map,
        ty_history: HashMap::new(),
        in_snapshot: false,
    };

    let out = check_file(f, &mut ana, &mut tys);

    out.unwrap();
}

fn check_file(f: ParseFile, ana: &mut Analyzer, tys: &mut TypeSystem) -> AnalyzeResult<()> {
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

    for (_, obj) in &ana.obj_skeletons {
        check_integrity_obj_skeleton(ana, tys, obj)?;
    }

    for (_, trt) in &ana.trt_skeletons {
        check_integrity_trt_skeleton(ana, tys, trt)?;
    }

    for imp in &ana.impls {
        check_integrity_impl(ana, tys, imp)?;
    }

    for sig in &export_fns {
        let fn_sig = initialize_fn_sig(ana, tys, sig)?;

        if ana.fn_sigs.insert(sig.name.clone(), fn_sig).is_some() {
            panic!("");
        }
    }

    for fun in &functions {
        let fn_sig = initialize_fn_sig(ana, tys, &fun.signature)?;
        check_integrity_fn_sig(ana, tys, &fn_sig)?;

        if ana.fn_sigs.insert(fun.signature.name.clone(), fn_sig).is_some() {
            panic!("");
        }
    }

    // TODO: Check impl

    for mut fun in functions {
        check_function(ana, tys, &mut fun)?;
        println!("FUNCTION {} : \n{:#?}", &fun.signature.name, &fun);
        ana.fns.insert(fun.signature.name.clone(), fun);
    }

    Ok(())
}

fn check_function(ana: &Analyzer, tys: &mut TypeSystem, fun: &mut AstFunction) -> AnalyzeResult<()> {
    raise(tys);
    fun.beginning_of_vars = VarId(tys.var_id_count.current());
    set_fn_generics(ana, tys, &fun.signature.name, &fun.signature.generics)?;

    let sig = &fun.signature;

    for &AstFnParameter { ref name, ref ty, pos } in &sig.parameter_list {
        let param_ty = init_ty(ana, tys, ty)?;
        declare_variable(tys, name, param_ty)?;
    }

    // Save the return type
    let return_ty = init_ty(ana, tys, &sig.return_type)?;
    set_return_type(tys, return_ty);

    // Analyze the function's body
    check_block(ana, tys, &mut fun.definition)?;

    reset_fn_generics(tys);
    fun.end_of_vars = VarId(tys.var_id_count.current());
    fall(tys);
    Ok(())
}

fn check_block(ana: &Analyzer, tys: &mut TypeSystem, blk: &mut AstBlock) -> AnalyzeResult<()> {
    raise(tys);

    for stmt in &mut blk.statements {
        check_stmt(ana, tys, stmt)?;
    }

    fall(tys);
    Ok(())
}

fn check_stmt(ana: &Analyzer, tys: &mut TypeSystem, stmt: &mut AstStatement) -> AnalyzeResult<()> {
    match &mut stmt.stmt {
        &mut AstStatementData::Block { ref mut block } => {
            check_block(ana, tys, block)?;
        }
        &mut AstStatementData::Let { ref mut var_name,
                                     ref mut ty,
                                     ref mut value,
                                     ref mut var_id } => {
            let let_ty = init_ty(ana, tys, ty)?;
            let expr_ty = check_expr(ana, tys, value, Some(let_ty))?;
            union_ty(tys, let_ty, expr_ty)?;
            *var_id = declare_variable(tys, var_name, let_ty)?;
        }
        &mut AstStatementData::If { ref mut condition, ref mut block, ref mut else_block } => {
            let ty = check_expr(ana, tys, condition, Some(TY_BOOLEAN))?;
            // We know it must ALWAYS be a boolean
            union_ty(tys, ty, TY_BOOLEAN)?;
            check_block(ana, tys, block)?;
            check_block(ana, tys, else_block)?;
        }
        &mut AstStatementData::While { ref mut condition, ref mut block } => {
            let ty = check_expr(ana, tys, condition, Some(TY_BOOLEAN))?;
            union_ty(tys, ty, TY_BOOLEAN)?;
            // Store the old "breakable" condition while we analyze the block
            let old_breakable = tys.breakable;
            tys.breakable = true;
            check_block(ana, tys, block)?;
            tys.breakable = old_breakable;
            // and restore it when we're done
        }
        &mut AstStatementData::Break |
        &mut AstStatementData::Continue => {
            if !tys.breakable {
                panic!("");
            }
        }
        &mut AstStatementData::NoOp => {}
        &mut AstStatementData::Return { ref mut value } => {
            let return_ty = tys.return_ty;
            let ty = check_expr(ana, tys, value, Some(return_ty))?;
            union_ty(tys, ty, return_ty)?;
        }
        &mut AstStatementData::Assert { ref mut condition } => {
            let ty = check_expr(ana, tys, condition, Some(TY_BOOLEAN))?;
            union_ty(tys, ty, TY_BOOLEAN)?;
        }
        &mut AstStatementData::Expression { ref mut expression } => {
            check_expr(ana, tys, expression, None)?;
        }
    }

    Ok(())
}

fn check_expr(ana: &Analyzer,
              tys: &mut TypeSystem,
              node: &mut AstExpression,
              expect_ty: Option<Ty>)
              -> AnalyzeResult<Ty> {
    let &mut AstExpression { ref mut expr, ref mut ty, pos } = node;

    *ty = match expr {
        &mut AstExpressionData::Nothing => TY_NOTHING,
        &mut AstExpressionData::True => TY_BOOLEAN,
        &mut AstExpressionData::False => TY_BOOLEAN,
        &mut AstExpressionData::Int(_) => TY_INT,
        &mut AstExpressionData::UInt(_) => TY_UINT,
        &mut AstExpressionData::Float(_) => TY_FLOAT,
        &mut AstExpressionData::Char(_) => TY_CHAR,
        &mut AstExpressionData::Null => new_null_infer_ty(tys),
        &mut AstExpressionData::SelfRef => {
            unimplemented!();
        }
        &mut AstExpressionData::String { ref string, ref mut id, len } => {
            // Save string in map, first
            *id = StringId(tys.str_id_count.next());
            tys.strings.insert(*id, (string.clone(), len));
            TY_STRING
        }

        &mut AstExpressionData::Identifier { ref name, ref mut var_id } => {
            let (id, ty) = get_variable_info(tys, name)?;
            *var_id = id;
            ty
        }
        &mut AstExpressionData::Tuple { ref mut values } => {
            //TODO: possibly unbox the expected type into tuple-inner-type expectations?
            let value_tys: Vec<_> = map_vec_mut(values, |v| check_expr(ana, tys, v, None))?;
            make_tuple_ty(tys, value_tys)
        }
        &mut AstExpressionData::Array { ref mut elements } => {
            let ty = new_infer_ty(tys); // We start out as an [_] array...
            for ref mut element in elements {
                let elt_ty = check_expr(ana, tys, element, Some(ty))?;
                union_ty(tys, ty, elt_ty)?;
            }
            make_array_ty(tys, ty)
        }
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
                panic!("");
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
                panic!(""); //TODO: error
            }

            let arg_tys = map_vec_mut(args, |e| check_expr(ana, tys, e, None))?;
            check_fns(ana, tys, &fn_sigs, &mut fn_gen_tys, &arg_tys, expect_ty)?
        }
        &mut AstExpressionData::Access { ref mut accessible, ref mut idx } => {
            let idx_ty = check_expr(ana, tys, idx, None)?;
            union_ty(tys, idx_ty, TY_UINT)?; // The index should be uint
            let array_ty = check_expr(ana, tys, accessible, None)?;
            // We "extract" the inner type T out of the array type [T].
            extract_array_inner_ty(tys, array_ty)?
        }
        &mut AstExpressionData::TupleAccess { ref mut accessible, idx } => {
            let tuple_ty = check_expr(ana, tys, accessible, None)?;
            extract_tuple_inner_ty(tys, tuple_ty, idx as usize)?
        }
        &mut AstExpressionData::ObjectAccess { ref mut object,
                                               ref mem_name,
                                               ref mut mem_idx } => {
            let obj_ty = check_expr(ana, tys, object, None)?;
            let (idx, ty) = extract_object_member_info(ana, tys, obj_ty, mem_name)?;
            *mem_idx = idx;
            ty
        }
        &mut AstExpressionData::Not(ref mut expr) => {
            let ty = check_expr(ana, tys, expr, None)?;
            if is_integral_ty(tys, ty) || is_boolean_ty(tys, ty) {
                ty
            } else {
                panic!("");
            }
        }
        &mut AstExpressionData::Negate(ref mut expr) => {
            let ty = check_expr(ana, tys, expr, None)?;
            if is_numeric_ty(tys, ty) {
                ty
            } else {
                panic!("");
            }
        }
        &mut AstExpressionData::Allocate { ref object } => {
            let obj_ty = init_ty(ana, tys, object)?;
            if is_object_ty(tys, obj_ty) {
                obj_ty
            } else {
                panic!("");
            }
        }
        &mut AstExpressionData::BinOp { kind, ref mut lhs, ref mut rhs } => {
            let lhs_ty = check_expr(ana, tys, lhs, None)?;
            let rhs_ty = check_expr(ana, tys, rhs, None)?;
            union_ty(tys, lhs_ty, rhs_ty)?;
            match kind {
                BinOpKind::Multiply | BinOpKind::Divide | BinOpKind::Modulo |
                BinOpKind::Add | BinOpKind::Subtract => {
                    if !is_numeric_ty(tys, lhs_ty) {
                        panic!("");
                    }
                    lhs_ty
                }
                BinOpKind::ShiftLeft | BinOpKind::ShiftRight => {
                    if !is_integral_ty(tys, lhs_ty) {
                        panic!("");
                    }
                    lhs_ty
                }
                BinOpKind::Greater | BinOpKind::Less | BinOpKind::GreaterEqual |
                BinOpKind::LessEqual => {
                    if !is_numeric_ty(tys, lhs_ty) {
                        panic!("");
                    }
                    TY_BOOLEAN
                }
                BinOpKind::Xor | BinOpKind::And | BinOpKind::Or => {
                    // TODO: also numeric not float
                    if !is_boolean_ty(tys, lhs_ty) {
                        panic!("");
                    }
                    lhs_ty
                }
                BinOpKind::EqualsEquals | BinOpKind::NotEqual => TY_BOOLEAN,
                BinOpKind::Set => lhs_ty,
            }
        }
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

        union_ty(tys, repl_expect_ty, *arg_ty)?;
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
        set_ty_checkpoint(tys)?;
        let check_result = check_fn(ana, tys, fn_sig, generics, args, return_hint);

        if check_result.is_ok() {
            if candidate_fn.is_some() {
                reset_ty_checkpoint(tys)?;
                panic!("");
            }

            candidate_fn = Some(fn_sig);
        }

        reset_ty_checkpoint(tys)?;
    }

    if candidate_fn.is_none() {
        panic!("");
    }

    check_fn(ana, tys, candidate_fn.unwrap(), generics, args, return_hint)
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
    ana.fn_sigs.get(name).ok_or(()).map(|o| o.clone()) //ERROR
}

fn get_obj_fn_sigs(ana: &Analyzer,
                   tys: &mut TypeSystem,
                   obj_ty: Ty,
                   name: &String,
                   is_member_fn: bool)
                   -> AnalyzeResult<(TraitId, Vec<FnSignature>)> {
    //TODO: BROKEN: we need to get
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
                sigs.push(fn_sig);
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
            panic!("");
        }
    }

    let generic_ids: Vec<_> = obj.generics.iter().map(|t| tys.obj_generics[t]).collect();
    let mut member_ids = HashMap::new();
    let mut member_tys = Vec::new();

    for ref mem in &obj.members {
        if member_ids.contains_key(&mem.name) {
            panic!("");
        }

        let mem_id = MemberId(member_tys.len() as u32);
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
            panic!("");
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
            panic!("");
        }
    }

    let generic_ids: Vec<_> = trt.generics.iter().map(|t| tys.obj_generics[t]).collect();
    let mut mem_fns = HashMap::new();
    let mut static_fns = HashMap::new();

    for fun in &trt.functions {
        if mem_fns.contains_key(&fun.name) || static_fns.contains_key(&fun.name) {
            panic!("");
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
            panic!("");
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

fn initialize_fn_sig(ana: &mut Analyzer, tys: &mut TypeSystem, fun: &AstFnSignature) -> AnalyzeResult<FnSignature> {
    for generic in &fun.generics {
        if tys.fn_generics
            .insert(generic.clone(), TyVarId(tys.ty_var_id_count.next()))
            .is_some() {
            panic!("");
        }
    }

    let generic_ids: Vec<_> = fun.generics.iter().map(|t| tys.fn_generics[t]).collect();
    let params = map_vec(&fun.parameter_list, |p| init_ty(ana, tys, &p.ty))?;
    let reqs = initialize_reqs(ana, tys, &fun.restrictions)?;
    let return_ty = init_ty(ana, tys, &fun.return_type)?;

    tys.fn_generics.clear();
    let sig = FnSignature::new(params, generic_ids, reqs, return_ty);
    Ok(sig)
}

fn check_integrity_obj_skeleton(ana: &Analyzer, tys: &mut TypeSystem, obj: &AnalyzeObject) -> AnalyzeResult<()> {
    for mem_ty in &obj.member_tys {
        check_integrity_ty(ana, tys, *mem_ty)?;
    }

    Ok(())
}

fn check_integrity_trt_skeleton(ana: &Analyzer, tys: &mut TypeSystem, trt: &AnalyzeTrait) -> AnalyzeResult<()> {
    for (_, fun) in &trt.member_fns {
        check_integrity_fn_sig(ana, tys, fun)?;
    }

    for (_, fun) in &trt.static_fns {
        check_integrity_fn_sig(ana, tys, fun)?;
    }

    Ok(())
}

fn check_integrity_impl(ana: &Analyzer, tys: &mut TypeSystem, imp: &AnalyzeImpl) -> AnalyzeResult<()> {
    let ref trt = ana.trt_skeletons[&imp.trait_id];

    check_integrity_ty(ana, tys, imp.imp_ty)?;
    check_integrity_trait_ty(ana, tys, &imp.imp_trt)?;

    Ok(())
}

fn check_integrity_fn_sig(ana: &Analyzer, tys: &mut TypeSystem, fn_sig: &FnSignature) -> AnalyzeResult<()> {
    for param_ty in &fn_sig.params {
        check_integrity_ty(ana, tys, *param_ty)?;
    }

    check_integrity_ty(ana, tys, fn_sig.return_ty)?;

    Ok(())
}

fn declare_variable(tys: &mut TypeSystem, name: &String, ty: Ty) -> AnalyzeResult<VarId> {
    let id = VarId(tys.var_id_count.next());

    if tys.var_ids.last_mut().unwrap().contains_key(name) {
        panic!("");
    }

    tys.var_ids.last_mut().unwrap().insert(name.clone(), id);
    tys.var_tys.insert(id, ty);

    Ok(id)
}

fn get_variable_info(tys: &TypeSystem, name: &String) -> AnalyzeResult<(VarId, Ty)> {
    for scope in tys.var_ids.iter().rev() {
        if scope.contains_key(name) {
            let id = scope[name];
            return Ok((id, tys.var_tys[&id]));
        }
    }

    panic!()
}

fn extract_object_member_info(ana: &Analyzer, tys: &mut TypeSystem, obj_ty: Ty, mem_name: &String) -> AnalyzeResult<(MemberId, Ty)> {
    match &tys.tys[&obj_ty] {
        &AnalyzeType::Same(same_ty) => {
            return extract_object_member_info(ana, tys, same_ty, mem_name);
        }
        _ => {}
    }

    //TODO: this is ugly...
    let (obj_skeleton, replacements) = match &tys.tys[&obj_ty] {
        &AnalyzeType::Object(obj_id, ref generics) => {
            let obj_skeleton = &ana.obj_skeletons[&obj_id];
            let replacements: HashMap<_, _> = obj_skeleton.generic_ids.iter().zip(generics).map(|(a, b)| (*a, *b)).collect();

            (obj_skeleton, replacements)
        }
        _ => {
            panic!("");
        }
    };

    if !obj_skeleton.member_ids.contains_key(mem_name) {
        panic!("");
    }

    let MemberId(id) = obj_skeleton.member_ids[mem_name];
    let mem_ty = obj_skeleton.member_tys[id as usize];

    Ok((MemberId(id), replace_ty(tys, mem_ty, &replacements)))
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
        unreachable!(); //TODO: unwrap? access?
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
            panic!("");
        }

        let ty_var = tys.fn_generics[name];
        return Ok(AnalyzeType::TypeVariable(ty_var));
    }

    if tys.obj_generics.contains_key(name) {
        if generics.len() != 0 {
            panic!("");
        }

        let ty_var = tys.obj_generics[name];
        return Ok(AnalyzeType::TypeVariable(ty_var));
    }

    if let Some((obj_id, generics_len)) = get_object_info(ana, name) {
        if generics.len() != generics_len {
            if generics.len() != 0 {
                panic!("");
            }

            for _ in 0..generics_len {
                generics.push(new_infer_ty(tys));
            }
        }

        Ok(AnalyzeType::Object(obj_id, generics))
    } else {
        // TODO: error for trait?
        panic!()
    }
}

fn make_tuple_ty(tys: &mut TypeSystem, value_tys: Vec<Ty>) -> Ty {
    register_ty(tys, AnalyzeType::Tuple(value_tys))
}

fn make_array_ty(tys: &mut TypeSystem, inner_ty: Ty) -> Ty {
    register_ty(tys, AnalyzeType::Array(inner_ty))
}

fn init_trait_instance(ana: &Analyzer, tys: &mut TypeSystem,
                           ty: &AstType)
                           -> AnalyzeResult<AnalyzeTraitInstance> {
    match ty {
        &AstType::Object(ref name, ref generics, pos) => {
            let mut gen_tys = map_vec(generics, |t| init_ty(ana, tys, t))?;
            let (id, generics_len) = get_trait_info(ana, name).ok_or_else(|| ())?;
            if gen_tys.len() != generics_len {
                panic!("");
            }
            Ok(AnalyzeTraitInstance {
                // TODO: new
                id: id,
                generics: gen_tys,
            })
        }
        _ => panic!(),
    }
}

fn new_infer_ty(tys: &mut TypeSystem) -> Ty {
    register_ty(tys, AnalyzeType::Infer)
}

fn new_null_infer_ty(tys: &mut TypeSystem) -> Ty {
    register_ty(tys, AnalyzeType::NullInfer)
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
        panic!("");
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
    println!("Unioning {} and {}", ty1.0, ty2.0);
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
            panic!(""); /*ERROR*/
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
        panic!()
    } else {
        for (ty1, ty2) in trt1.generics.iter().zip(trt2.generics.iter()) {
            union_ty_right(tys, *ty1, *ty2)?;
        }

        Ok(())
    }
}

fn check_integrity_ty(ana: &Analyzer, tys: &mut TypeSystem, ty: Ty) -> AnalyzeResult<()> {
    match tys.tys[&ty].clone() {
        AnalyzeType::Infer => panic!(),
        AnalyzeType::NullInfer => panic!(),
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

fn set_fn_generics(ana: &Analyzer, tys: &mut TypeSystem, name: &String, generics: &Vec<String>) -> AnalyzeResult<()> {
    let sig = ana.fn_sigs.get(name).ok_or_else(|| ())?;

    let vars: HashMap<_, _> = generics.iter().cloned().zip(sig.generic_ids.iter().cloned()).collect();
    tys.fn_generics = vars;
    Ok(())
}

fn reset_fn_generics(tys: &mut TypeSystem) {
    tys.fn_generics.clear();
}

fn set_return_type(tys: &mut TypeSystem, ty: Ty) {
    tys.return_ty = ty;
}

fn raise(tys: &mut TypeSystem) {
    tys.var_ids.push(HashMap::new());
}

fn fall(tys: &mut TypeSystem) {
    tys.var_ids.pop();
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

fn is_boolean_ty(tys: &TypeSystem, ty: Ty) -> bool {
    match &tys.tys[&ty] {
        &AnalyzeType::Boolean => true,
        &AnalyzeType::Same(same_ty) => is_boolean_ty(tys, same_ty),
        _ => false,
    }
}

fn is_object_ty(tys: &TypeSystem, ty: Ty) -> bool {
    match &tys.tys[&ty] {
        &AnalyzeType::Object(..) => true,
        &AnalyzeType::Same(same_ty) => is_object_ty(tys, same_ty),
        _ => false,
    }
}

fn is_integral_ty(tys: &TypeSystem, ty: Ty) -> bool {
    match &tys.tys[&ty] {
        &AnalyzeType::Int |
        &AnalyzeType::UInt => true,
        &AnalyzeType::Same(same_ty) => is_integral_ty(tys, same_ty),
        _ => false,
    }
}

fn is_numeric_ty(tys: &TypeSystem, ty: Ty) -> bool {
    match &tys.tys[&ty] {
        &AnalyzeType::Int |
        &AnalyzeType::UInt |
        &AnalyzeType::Float => true,
        &AnalyzeType::Same(same_ty) => is_numeric_ty(tys, same_ty),
        _ => false,
    }
}

fn extract_array_inner_ty(tys: &TypeSystem, array_ty: Ty) -> AnalyzeResult<Ty> {
    match &tys.tys[&array_ty] {
        &AnalyzeType::Array(inner_ty) => Ok(inner_ty),
        &AnalyzeType::Same(same_ty) => extract_array_inner_ty(tys, same_ty),
        _ => panic!()
    }
}

fn extract_tuple_inner_ty(tys: &TypeSystem, tuple_ty: Ty, idx: usize) -> AnalyzeResult<Ty> {
    match &tys.tys[&tuple_ty] {
        &AnalyzeType::Tuple(ref tuple_tys) => {
            if tuple_tys.len() <= idx {
                panic!("");
            }

            Ok(tuple_tys[idx])
        }
        &AnalyzeType::Same(same_ty) => extract_tuple_inner_ty(tys, same_ty, idx),
        _ => panic!()
    }
}

fn get_ty_var(tys: &TypeSystem, ty: Ty) -> AnalyzeResult<TyVarId> {
    match &tys.tys[&ty] {
        &AnalyzeType::TypeVariable(ty_var) => Ok(ty_var),
        &AnalyzeType::Same(same_ty) => get_ty_var(tys, same_ty),
        _ => panic!(),
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
