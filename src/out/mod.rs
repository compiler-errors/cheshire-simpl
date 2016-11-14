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
    VarId(VarId),
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
            if self.is_simple_ty(sig.return_ty, AnalyzeType::Nothing) {
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
                    println!("br i1 {}, label %br{}, label %br{}",
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
                    println!("br label %br{} ; break", break_block);
                    return true;
                }
                &AstStatementData::Continue => {
                    let continue_block = cont_brk.unwrap().0; //TODO: prettier
                    println!("br label %br{} ; continue", continue_block);
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
                    println!("call void @_cheshire_assert(i1 {})", cond_ref);
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
            &AstExpressionData::Null => {
                if self.is_array_ty(expr.ty) {
                    let inner_ty_str = self.array_ty_str(expr.ty);
                    ExprRef::Constant(format!("{{i64 0, {}* null}}", inner_ty_str))
                } else {
                    ExprRef::Constant("null".to_string())
                }
            }
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

                let inner_ty_str = self.array_ty_str(expr.ty);
                println!("%expr{} = getelementptr {}, {}* null, i64 1",
                         sizeptr_id,
                         inner_ty_str,
                         inner_ty_str);
                println!("%expr{} = ptrtoint {}* %expr{} to i64",
                         size_id,
                         inner_ty_str,
                         sizeptr_id); //TODO: maybe i64 for size?
                println!("%expr{} = call i8* @_cheshire_malloc_array(i64 %expr{}, i64 {})",
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
            &AstExpressionData::TupleAccess { ref accessible, idx } => {
                let tuple_ref = self.output_expression(accessible);
                let tuple_ty_str = self.ty_str(accessible.ty);
                let element_id = self.expr_new_id;
                self.expr_new_id += 1;
                println!("%expr{} = extractvalue {} {}, {}",
                         element_id,
                         tuple_ty_str,
                         tuple_ref,
                         idx);
                ExprRef::ExprId(element_id)
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
            &AstExpressionData::BinOp { kind, ref lhs, ref rhs } => {
                if kind == BinOpKind::Set {
                    let lhs_ref = self.output_expression_lval(lhs);
                    let rhs_ref = self.output_expression(rhs);
                    let expr_ty = self.ty_str(lhs.ty);
                    println!("store {} {}, {}* {}", expr_ty, rhs_ref, expr_ty, lhs_ref);
                    rhs_ref
                } else {
                    let lhs_ref = self.output_expression(lhs);
                    let rhs_ref = self.output_expression(rhs);
                    let op_ty = self.ty_str(lhs.ty);
                    let op_str = self.get_op_string(kind, lhs.ty);
                    let out_id = self.expr_new_id;
                    self.expr_new_id += 1;
                    println!("%expr{} = {} {} {}, {}",
                             out_id,
                             op_str,
                             op_ty,
                             lhs_ref,
                             rhs_ref);
                    ExprRef::ExprId(out_id)
                }
            }
        }
    }

    fn output_expression_lval(&mut self, expr: &AstExpression) -> ExprRef {
        match &expr.expr {
            &AstExpressionData::Identifier { var_id, .. } => ExprRef::VarId(var_id),
            &AstExpressionData::Access { ref accessible, ref idx } => {
                let accessible_ref = self.output_expression(accessible);
                let idx_ref = self.output_expression(idx);
                let arrptr_id = self.expr_new_id + 0;
                let valueptr_id = self.expr_new_id + 1;
                self.expr_new_id += 2;
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
                ExprRef::ExprId(valueptr_id)
            }
            &AstExpressionData::TupleAccess { ref accessible, idx } => {
                let tuple_ref = self.output_expression_lval(accessible);
                let tuple_ty_str = self.ty_str(accessible.ty);
                let element_id = self.expr_new_id;
                self.expr_new_id += 1;
                println!("%expr{} = getelementptr {}, {}* {}, i64 0, i32 {}",
                         element_id,
                         tuple_ty_str,
                         tuple_ty_str,
                         tuple_ref,
                         idx);
                ExprRef::ExprId(element_id)
            }
            _ => unreachable!(),
        }
    }

    fn get_op_string(&self, kind: BinOpKind, ty: Ty) -> &'static str {
        if self.is_simple_ty(ty, AnalyzeType::Int) {
            match kind {
                BinOpKind::Multiply => "mul",
                BinOpKind::Divide => "sdiv",
                BinOpKind::Modulo => "srem",
                BinOpKind::Add => "add",
                BinOpKind::Subtract => "sub",
                BinOpKind::ShiftLeft => "shl",
                BinOpKind::ShiftRight => "ashr",
                BinOpKind::Greater => "icmp sgt",
                BinOpKind::Less => "icmp slt",
                BinOpKind::GreaterEqual => "icmp sge",
                BinOpKind::LessEqual => "icmp sle",
                BinOpKind::EqualsEquals => "icmp eq",
                BinOpKind::NotEqual => "icmp ne",
                BinOpKind::Xor => "xor",
                BinOpKind::And => "and",
                BinOpKind::Or => "or",
                BinOpKind::Set => unreachable!(),
            }
        } else if self.is_simple_ty(ty, AnalyzeType::UInt) {
            match kind {
                BinOpKind::Multiply => "mul",
                BinOpKind::Divide => "udiv",
                BinOpKind::Modulo => "urem",
                BinOpKind::Add => "add",
                BinOpKind::Subtract => "sub",
                BinOpKind::ShiftLeft => "shl",
                BinOpKind::ShiftRight => "lshr",
                BinOpKind::Greater => "icmp ugt",
                BinOpKind::Less => "icmp ult",
                BinOpKind::GreaterEqual => "icmp uge",
                BinOpKind::LessEqual => "icmp ule",
                BinOpKind::EqualsEquals => "icmp eq",
                BinOpKind::NotEqual => "icmp ne",
                BinOpKind::Xor => "xor",
                BinOpKind::And => "and",
                BinOpKind::Or => "or",
                BinOpKind::Set => unreachable!(),
            }
        } else if self.is_simple_ty(ty, AnalyzeType::Float) {
            match kind {
                BinOpKind::Multiply => "fmul",
                BinOpKind::Divide => "fdiv",
                BinOpKind::Modulo => "frem",
                BinOpKind::Add => "fadd",
                BinOpKind::Subtract => "fsub",
                BinOpKind::Greater => "fcmp gt",
                BinOpKind::Less => "fcmp lt",
                BinOpKind::GreaterEqual => "fcmp gre",
                BinOpKind::LessEqual => "fcmp lte",
                BinOpKind::EqualsEquals => "fcmp eq",
                BinOpKind::NotEqual => "fcmp ne",
                _ => unreachable!(),
            }
        } else if self.is_simple_ty(ty, AnalyzeType::Boolean) {
            match kind {
                BinOpKind::EqualsEquals => "icmp eq",
                BinOpKind::NotEqual => "icmp ne",
                BinOpKind::Xor => "xor",
                BinOpKind::And => "and",
                BinOpKind::Or => "or",
                _ => unreachable!(),
            }
        } else {
            unimplemented!() //TODO tuple eq, string eq, etc
        }
    }

    fn ty_str(&self, ty: Ty) -> String {
        if let &AnalyzeType::Same(same_ty) = &self.ty_map[&ty] {
            return self.ty_str(same_ty);
        }

        let analyze_ty = &self.ty_map[&ty];

        match analyze_ty {
            &AnalyzeType::Nothing => "{}".to_string(),
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

    fn is_simple_ty(&self, ty: Ty, candidate: AnalyzeType) -> bool {
        match &self.ty_map[&ty] {
            &AnalyzeType::Same(ty_same) => self.is_simple_ty(ty_same, candidate),
            a => (*a == candidate),
        }
    }

    fn is_array_ty(&self, ty: Ty) -> bool {
        match &self.ty_map[&ty] {
            &AnalyzeType::Same(ty_same) => self.is_array_ty(ty_same),
            &AnalyzeType::Array(_) => true,
            _ => false,
        }
    }

    fn array_ty_str(&self, array_ty: Ty) -> String {
        match &self.ty_map[&array_ty] {
            &AnalyzeType::Same(array_ty_same) => self.array_ty_str(array_ty_same),
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
            &ExprRef::VarId(id) => write!(f, "%var{}", id),
            &ExprRef::None => unreachable!(),
        }
    }
}
