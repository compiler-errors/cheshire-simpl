use std::collections::HashMap;
use std::str::FromStr;
use std::fmt::{Display, Formatter, Result};
use std::mem::transmute;
use analyzer::*;
use parser::*;

type ExprId = u32;

enum ExprRef {
    Constant(String),
    ExprId(ExprId),
    None,
}

type BlkId = u32;

pub struct Out {
    ty_map: HashMap<Ty, AnalyzeType>,
    var_tys: HashMap<VarId, Ty>,
    blk_new_id: BlkId,
    expr_new_id: ExprId,
}

impl Out {
    pub fn out(ana: Analyzer) {
        let Analyzer { fn_signatures, fns, var_tys, ty_map, .. } = ana; //TODO: strings

        let mut out = Out {
            ty_map: ty_map,
            var_tys: var_tys,
            blk_new_id: 1,
            expr_new_id: 1,
        };

        for fun in fns.keys() {
            let ref fun_body = fns[fun];
            let ref fun_sig = fn_signatures[fun];

            out.output_function(fun_body, fun_sig);
        }
    }

    fn output_function(&mut self, body: &AstFunction, sig: &FnSignature) {
        let ret_ty_str = self.ty_str(sig.return_ty);
        let decorated_fn_name = &body.name; //TODO: Decorate

        // Output function signature
        print!("\n\ndefine {} @{}(", ret_ty_str, decorated_fn_name);

        // Output function args in signature
        for (i, ty) in sig.params.iter().enumerate() {
            let param_ty_str = self.ty_str(*ty);
            if i != 0 {
                print!(", ");
            }
            print!("{} %arg{}", param_ty_str, i);
        }
        println!(") {{");

        // Declare the function's variables
        for i in body.beginning_of_vars..body.end_of_vars {
            let var_ty_str = self.ty_str(self.var_tys[&i]);
            println!("%var{} = alloca {}", i, var_ty_str); //TODO: store param name?
        }

        for i in 0..(sig.params.len() as VarId) {
            let var_ty_str = self.ty_str(sig.params[i as usize]);
            println!("store {} %arg{}, {}* %var{}",
                     var_ty_str,
                     i,
                     var_ty_str,
                     body.beginning_of_vars + i);
        }

        let returns = self.output_block(&body.definition, None);
        if !returns {
            if self.is_void_ty(sig.return_ty) {
                println!("ret {{}} undef");
            } else {
                println!("ret {} zeroinitializer", ret_ty_str);
            }
        }

        println!("}}");
    }

    fn output_block(&mut self, body: &AstBlock, cont_brk: Option<(BlkId, BlkId)>) -> bool {
        for ref stmt in &body.statements {
            match &stmt.stmt {
                &AstStatementData::Block { ref block } => {
                    let block_returns = self.output_block(block, cont_brk);
                    if block_returns {
                        return true;
                    }
                }
                &AstStatementData::Let { ref value, var_id, .. } => {
                    let value_ref = self.output_expression(value);
                    let var_ty_str = self.ty_str(value.ty);
                    println!("store {} {}, {}* %var{}",
                             var_ty_str,
                             value_ref,
                             var_ty_str,
                             var_id);
                }
                &AstStatementData::If { ref condition, ref block, ref else_block } => {
                    let true_blk = self.blk_new_id;
                    self.blk_new_id += 1;
                    let false_blk = self.blk_new_id;
                    self.blk_new_id += 1;
                    let end_blk = self.blk_new_id;
                    self.blk_new_id += 1;

                    let cond_ref = self.output_expression(condition);
                    println!("br i1 {}, label %br{}, label %br{}",
                             cond_ref,
                             true_blk,
                             false_blk);

                    println!("br{}:", true_blk);
                    let true_returns = self.output_block(block, cont_brk);
                    if !true_returns {
                        println!("br label %br{}", end_blk);
                    }

                    println!("br{}:", false_blk);
                    let false_returns = self.output_block(else_block, cont_brk);
                    if !false_returns {
                        println!("br label %br{}", end_blk);
                    }

                    if true_returns && false_returns {
                        return true;
                    } else {
                        println!("br{}:", end_blk);
                    }
                }
                &AstStatementData::While { ref condition, ref block } => {
                    let test_blk = self.blk_new_id;
                    self.blk_new_id += 1;
                    let true_blk = self.blk_new_id;
                    self.blk_new_id += 1;
                    let end_blk = self.blk_new_id;
                    self.blk_new_id += 1;

                    println!("br label %br{}", test_blk);

                    println!("br{}:", test_blk);
                    let cond_ref = self.output_expression(condition);
                    println!("br i1 %expr{}, label %br{}, label %br{}",
                             cond_ref,
                             true_blk,
                             end_blk);

                    println!("br{}:", true_blk);
                    let while_returns = self.output_block(block, Some((test_blk, end_blk)));
                    if !while_returns {
                        println!("br label %br{}", test_blk);
                    }

                    println!("br{}:", end_blk);
                }
                &AstStatementData::Break => {
                    let break_block = cont_brk.unwrap().1;
                    println!("br label %br{}", break_block);
                    return true;
                }
                &AstStatementData::Continue => {
                    let continue_block = cont_brk.unwrap().0;
                    println!("br label %br{}", continue_block);
                    return true;
                }
                &AstStatementData::Return { ref value } => {
                    let expr_ref = self.output_expression(value);
                    let expr_ty_str = self.ty_str(value.ty);
                    println!("ret {} {}", expr_ty_str, expr_ref);
                    return true;
                }
                &AstStatementData::Assert { ref condition } => {
                    let cond_ref = self.output_expression(condition);
                    println!("call void @cheshire.assert(i1 {})", cond_ref);
                }
                &AstStatementData::Expression { ref expression } => {
                    self.output_expression(expression);
                }
                &AstStatementData::NoOp => println!("call void @llvm.donothing() ; no-op"),
            }
        }

        false
    }

    fn output_expression(&mut self, expr: &AstExpression) -> ExprRef {
        match &expr.expr {
            &AstExpressionData::Nothing => ExprRef::Constant("undef".to_string()),
            &AstExpressionData::True => ExprRef::Constant("true".to_string()),
            &AstExpressionData::False => ExprRef::Constant("false".to_string()),
            &AstExpressionData::Null => ExprRef::Constant("null".to_string()),
            &AstExpressionData::String { id, .. } => ExprRef::Constant(format!("@str{}", id)),
            &AstExpressionData::Int(ref s) => ExprRef::Constant(s.clone()),
            // TODO: check constant right size...
            &AstExpressionData::UInt(ref s) => ExprRef::Constant(s.clone()),
            &AstExpressionData::Float(ref s) => {
                // Since LLVM only supports floats which are exact, let's transmute them!
                let float = f64::from_str(s).unwrap();
                let bitpattern = unsafe { transmute::<f64, u64>(float) };
                ExprRef::Constant(format!("0x{:X}", bitpattern))
            }
            &AstExpressionData::Char(c) => ExprRef::Constant(format!("{}", c as u32)),
            &AstExpressionData::Identifier { var_id, .. } => {
                let value_id = self.expr_new_id;
                let var_ty = self.ty_str(expr.ty);
                self.expr_new_id += 1;
                println!("%expr{} = load {}, {}* %var{}",
                         value_id,
                         var_ty,
                         var_ty,
                         var_id);
                ExprRef::ExprId(value_id)
            }
            &AstExpressionData::Tuple { ref values } => {
                let mut last_tuple = ExprRef::Constant("zeroinitializer".to_string());
                let ty_str = self.ty_str(expr.ty);
                for (i, ref elem) in values.iter().enumerate() {
                    let tuple_stage_id = self.expr_new_id;
                    let elem_ref = self.output_expression(elem);
                    let elem_ty_str = self.ty_str(elem.ty);
                    self.expr_new_id += 1;
                    println!("%expr{} = insertvalue {} {}, {} {}, {}",
                             tuple_stage_id,
                             ty_str,
                             last_tuple,
                             elem_ty_str,
                             elem_ref,
                             i);
                    last_tuple = ExprRef::ExprId(tuple_stage_id);
                }
                last_tuple
            }
            &AstExpressionData::Array { ref elements } => {
                let sizeptr_id = self.expr_new_id + 0; // The pointer signifying the size of T
                let size_id = self.expr_new_id + 1; // The integer signifying the size of T
                let arri8_id = self.expr_new_id + 2; // The T* array malloc'ed as i8* pointer
                let arr_id = self.expr_new_id + 3; // The T* array pointer
                let return_id = self.expr_new_id + 4; // The {i64, T*} value of the finished array
                self.expr_new_id += 5;

                let inner_ty_str = self.array_ty_string(expr.ty);
                println!("%expr{} = getelementptr {}, {}* null, i64 1",
                         sizeptr_id,
                         inner_ty_str,
                         inner_ty_str);
                println!("%expr{} = ptrtoint {}* %expr{} to i64",
                         size_id,
                         inner_ty_str,
                         sizeptr_id); //TODO: maybe i64 for size?
                println!("%expr{} = call i8* @cheshire.malloc_array(i64 %expr{}, i64 {})",
                         arri8_id,
                         size_id,
                         elements.len());
                println!("%expr{} = bitcast i8* %expr{} to {}*",
                         arr_id,
                         arri8_id,
                         inner_ty_str);

                for (i, ref elem) in elements.iter().enumerate() {
                    let elem_ref = self.output_expression(elem);
                    println!("%expr{}_elem{} = getelementptr {}, {}* %expr{}, i64 {}",
                             arr_id,
                             i,
                             inner_ty_str,
                             inner_ty_str,
                             arr_id,
                             i);
                    println!("store {} {}, {}* %expr{}_elem{}",
                             inner_ty_str,
                             elem_ref,
                             inner_ty_str,
                             arr_id,
                             i);
                }

                println!("%expr{} = insertvalue {{i64, {}*}} {{i64 {}, {}* null}}, {}* %expr{}, 1",
                         return_id,
                         inner_ty_str,
                         elements.len(),
                         inner_ty_str,
                         inner_ty_str,
                         arr_id);

                ExprRef::ExprId(return_id)
            }
            &AstExpressionData::Call { ref name, ref args } => {
                let call_id = self.expr_new_id;
                self.expr_new_id += 1;
                let ret_ty_str = self.ty_str(expr.ty);
                let arg_refs: Vec<_> =
                    args.iter().map(|e| (e.ty, self.output_expression(e))).collect();
                print!("%expr{} = call {} @{}(", call_id, ret_ty_str, name);
                for (i, (arg_ty, arg_ref)) in arg_refs.into_iter().enumerate() {
                    if i != 0 {
                        print!(", ");
                    }
                    let arg_ty_str = self.ty_str(arg_ty);
                    print!("{} {}", arg_ty_str, arg_ref);
                }
                println!(")");
                ExprRef::ExprId(call_id)
            }
            &AstExpressionData::Access { ref accessible, ref idx } => {
                let accessible_ref = self.output_expression(accessible);
                let idx_ref = self.output_expression(idx);
                let arrptr_id = self.expr_new_id + 0;
                let valueptr_id = self.expr_new_id + 1;
                let value_id = self.expr_new_id + 2;
                self.expr_new_id += 3;
                let inner_ty_str = self.ty_str(expr.ty);
                println!("%expr{} = extractvalue {{i64, {}*}} {}, 1",
                         arrptr_id,
                         inner_ty_str,
                         accessible_ref);
                // TODO: Test
                println!("%expr{} = getelementptr {}, {}* %expr{}, i64 {}",
                         valueptr_id,
                         inner_ty_str,
                         inner_ty_str,
                         arrptr_id,
                         idx_ref);
                println!("%expr{} = load {}, {}* %expr{}",
                         value_id,
                         inner_ty_str,
                         inner_ty_str,
                         valueptr_id);
                ExprRef::ExprId(value_id)
            }
            &AstExpressionData::Not(ref expr) => {
                let expr_ref = self.output_expression(expr);
                let expr_ty = self.ty_str(expr.ty);
                let not_id = self.expr_new_id;
                self.expr_new_id += 1;
                println!("%expr{} = xor {} {}, -1", not_id, expr_ty, expr_ref);
                ExprRef::ExprId(not_id)
            }
            &AstExpressionData::Negate(ref expr) => {
                let expr_ref = self.output_expression(expr);
                let expr_ty = self.ty_str(expr.ty);
                let neg_id = self.expr_new_id;
                self.expr_new_id += 1;
                println!("%expr{} = sub {} 0, {}", neg_id, expr_ty, expr_ref);
                ExprRef::ExprId(neg_id)
            }
            &AstExpressionData::BinOp { kind, ref lhs, ref rhs } => unimplemented!(),
        }
    }

    fn ty_str(&self, ty: Ty) -> String {
        if let &AnalyzeType::Same(same_ty) = &self.ty_map[&ty] {
            return self.ty_str(same_ty);
        }

        let analyze_ty = &self.ty_map[&ty];

        match analyze_ty {
            &AnalyzeType::Nothing => "{{}}".to_string(),
            &AnalyzeType::Boolean => "i1".to_string(),
            &AnalyzeType::Int => "i64".to_string(),
            &AnalyzeType::UInt => "i64".to_string(),
            &AnalyzeType::Float => "double".to_string(),
            &AnalyzeType::Char => "i8".to_string(), //TODO: Are strings unicode?
            &AnalyzeType::String => "i8*".to_string(),
            &AnalyzeType::Tuple(ref tys) => {
                let mut s = "{".to_string();
                for (i, tuple_ty) in tys.iter().enumerate() {
                    if i != 0 {
                        s += ", ";
                    }
                    s += &self.ty_str(*tuple_ty);
                }
                s += "}";

                s
            }
            &AnalyzeType::Array(inner_ty) => format!("{{i64, {}*}}", self.ty_str(inner_ty)),
            &AnalyzeType::Same(_) |
            &AnalyzeType::NullInfer |
            &AnalyzeType::Infer => unreachable!(),
        }
    }

    fn is_void_ty(&self, ty: Ty) -> bool {
        match &self.ty_map[&ty] {
            &AnalyzeType::Same(array_ty_same) => self.is_void_ty(array_ty_same),
            &AnalyzeType::Array(inner_ty) => true,
            _ => false,
        }
    }

    fn array_ty_string(&self, array_ty: Ty) -> String {
        match &self.ty_map[&array_ty] {
            &AnalyzeType::Same(array_ty_same) => self.array_ty_string(array_ty_same),
            &AnalyzeType::Array(inner_ty) => self.ty_str(inner_ty),
            _ => unreachable!(),
        }
    }
}

impl Display for ExprRef {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            &ExprRef::Constant(ref s) => write!(f, "{}", s),
            &ExprRef::ExprId(id) => write!(f, "%expr{}", id),
            &ExprRef::None => unreachable!(),
        }
    }
}
