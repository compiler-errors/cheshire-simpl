mod ty;

pub use self::ty::*;
use util::FileReader;
use parser::*;
use std::collections::HashMap;
use std::process::exit;

pub struct Analyzer<'a> {
    functions: HashMap<String, FnSignature>,
    variables: Vec<HashMap<String, Ty>>,
    return_ty: Ty,

    // File which is being analyzed
    file: Option<FileReader<'a>>,

    // Type System
    ty_variables: HashMap<Ty, AnalyzeType>,
    ty_new_id: u32
}

impl <'a> Analyzer<'a> {
    pub fn new() -> Analyzer<'a> {
        let mut ty_variables = HashMap::new();
        ty_variables.insert(TY_NOTHING, AnalyzeType::Nothing);
        ty_variables.insert(TY_BOOLEAN, AnalyzeType::Boolean);
        ty_variables.insert(TY_INT, AnalyzeType::Int);
        ty_variables.insert(TY_UINT, AnalyzeType::UInt);
        ty_variables.insert(TY_FLOAT, AnalyzeType::Float);
        ty_variables.insert(TY_CHAR, AnalyzeType::Char);
        ty_variables.insert(TY_STRING, AnalyzeType::String);

        Analyzer {
            functions: HashMap::new(),
            variables: Vec::new(),
            return_ty: 0,
            file: None,
            ty_variables: ty_variables,
            ty_new_id: TY_FIRST_NEW_ID
        }
    }

    pub fn analyze_file(&mut self, mut f: ParseFile<'a>) {
        self.file = Some(f.file);

        for fun in &f.functions {
            if self.functions.contains_key(&fun.name) {
                self.report_analyze_err_at(fun.pos,
                    format!("Duplicate function name `{}`", fun.name));
            }

            let arg_tys: Vec<_> = fun.parameter_list.iter()
                                     .map(|p| self.initialize_ty(&p.ty)).collect();
            let return_ty = self.initialize_ty(&fun.return_type);
            self.functions.insert(fun.name.clone(), FnSignature::new(arg_tys, return_ty));
        }

        for fun in &mut f.functions {
            self.analyze_function(fun);
        }
    }

    pub fn analyze_function(&mut self, f: &mut AstFunction) {
        self.raise();

        for &mut AstFnParameter { ref name, ref mut ty, pos } in &mut f.parameter_list {
            let param_ty = self.initialize_ty(ty);
            self.declare_variable(name, param_ty, pos);
        }

        let return_ty = self.initialize_ty(&mut f.return_type);
        self.set_return_type(return_ty);
        self.analyze_block(&mut f.definition);

        self.fall();
    }

    fn analyze_block(&mut self, block: &mut AstBlock) {
        self.raise();

        for stmt in &mut block.statements {
            self.analyze_stmt(stmt);
        }

        self.fall();
    }

    fn analyze_stmt(&mut self, stmt: &mut AstStatement) {
        let pos = stmt.pos;
        match &mut stmt.stmt {
            &mut AstStatementData::Block { ref mut block } => {
                self.analyze_block(block);
            }
            &mut AstStatementData::Let { ref mut var_name,
                                         ref mut ty,
                                         ref mut value } => {
                let let_ty = self.initialize_ty(ty);
                let expr_ty = self.typecheck_expr(value);
                self.union_ty(let_ty, expr_ty, pos);
                self.declare_variable(var_name, let_ty, pos);
            }
            &mut AstStatementData::If { ref mut condition,
                                        ref mut block,
                                        ref mut else_block } => {
                let ty = self.typecheck_expr(condition);
                self.union_ty(ty, TY_BOOLEAN, pos); //TODO: more expressive error?
                self.analyze_block(block);
                self.analyze_block(else_block);
            }
            &mut AstStatementData::While { ref mut condition,
                                           ref mut block } => {
                let ty = self.typecheck_expr(condition);
                self.union_ty(ty, TY_BOOLEAN, pos);
                self.analyze_block(block);
            }
            &mut AstStatementData::Break |
            &mut AstStatementData::Continue |
            &mut AstStatementData::NoOp => {
                //TODO: nothing yet
            }
            &mut AstStatementData::Return { ref mut value } => {
                let ty = self.typecheck_expr(value);
                let return_ty = self.get_return_type();
                self.union_ty(ty, return_ty, pos);
            }
            &mut AstStatementData::Assert { ref mut condition } => {
                let ty = self.typecheck_expr(condition);
                self.union_ty(ty, TY_BOOLEAN, pos);
            }
            &mut AstStatementData::Expression { ref mut expression } => {
                self.typecheck_expr(expression);
            }
        }
    }

    fn typecheck_expr(&mut self, expression: &mut AstExpression) -> Ty {
        let &mut AstExpression {
            ref mut expr,
            ref mut ty,
            pos
        } = expression;

        *ty = match expr {
            &mut AstExpressionData::Nothing => {
                TY_NOTHING
            }
            &mut AstExpressionData::True => {
                TY_BOOLEAN
            }
            &mut AstExpressionData::False => {
                TY_BOOLEAN
            }
            &mut AstExpressionData::String(_) => {
                TY_STRING
            }
            &mut AstExpressionData::Int(_) => {
                TY_INT
            }
            &mut AstExpressionData::UInt(_) => {
                TY_UINT
            }
            &mut AstExpressionData::Float(_) => {
                TY_FLOAT
            }
            &mut AstExpressionData::Char(_) => {
                TY_CHAR
            }
            &mut AstExpressionData::Identifier(ref name) => {
                self.get_variable_type(name, pos)
            }
            &mut AstExpressionData::Tuple { ref mut values } => {
                let mut tys = Vec::new();
                for ref mut value in values {
                    tys.push(self.typecheck_expr(value));
                }
                self.make_tuple_ty(tys)
            }
            &mut AstExpressionData::Array { ref mut elements } => {
                let ty = self.new_infer_type();
                for ref mut element in elements {
                    let elt_ty = self.typecheck_expr(element);
                    self.union_ty(ty, elt_ty, element.pos);
                }
                self.make_array_ty(ty)
            }
            &mut AstExpressionData::Call { ref mut name,
                                           ref mut args } => {
                let mut arg_tys = Vec::new();
                for ref mut arg in args {
                    arg_tys.push(self.typecheck_expr(arg));
                }

                let fn_sig = self.get_function_signature(name);

                self.typecheck_function_call(fn_sig, arg_tys, pos)
            }
            &mut AstExpressionData::Access { ref mut accessible,
                                             ref mut idx } => {
                let idx_ty = self.typecheck_expr(idx);
                self.union_ty(idx_ty, TY_UINT, idx.pos);
                let array_ty = self.typecheck_expr(accessible);
                self.extract_array_element_ty(array_ty, accessible.pos)
            }
            &mut AstExpressionData::Not(ref mut expr) => {
                let ty = self.typecheck_expr(expr);
                if self.is_numeric_ty(ty) || self.is_boolean_ty(ty) {
                    ty
                } else {
                    self.report_analyze_err_at(expr.pos,
                        format!("Expected sub-expression of type `Int` or `Bool`"));
                }
            }
            &mut AstExpressionData::Negate(ref mut expr) => {
                let ty = self.typecheck_expr(expr);
                if self.is_numeric_ty(ty) {
                    ty
                } else {
                    self.report_analyze_err_at(expr.pos,
                        format!("Expected sub-expression of type `Int`"));
                }
            }
            &mut AstExpressionData::BinOp { kind,
                                            ref mut lhs,
                                            ref mut rhs } => {
                let lhs_ty = self.typecheck_expr(lhs);
                let rhs_ty = self.typecheck_expr(rhs);
                self.union_ty(lhs_ty, rhs_ty, pos);
                match kind {
                    BinOpKind::Multiply |
                    BinOpKind::Divide |
                    BinOpKind::Modulo |
                    BinOpKind::Add |
                    BinOpKind::Subtract |
                    BinOpKind::ShiftLeft |
                    BinOpKind::ShiftRight => {
                        if !self.is_numeric_ty(lhs_ty) {
                            self.report_analyze_err_at(pos,
                                format!("Expected sub-expression of type `Int`"));
                        }
                        lhs_ty
                    }
                    BinOpKind::Greater |
                    BinOpKind::Less |
                    BinOpKind::GreaterEqual |
                    BinOpKind::LessEqual => {
                        if !self.is_numeric_ty(lhs_ty) {
                            self.report_analyze_err_at(pos,
                                format!("Expected sub-expression of type `Int`"));
                        }
                        TY_BOOLEAN
                    }
                    BinOpKind::Xor |
                    BinOpKind::And |
                    BinOpKind::Or => {
                        if !self.is_boolean_ty(lhs_ty) {
                            self.report_analyze_err_at(pos,
                                format!("Expected sub-expression of type `Bool`"));
                        }
                        lhs_ty
                    }
                    BinOpKind::EqualsEquals |
                    BinOpKind::NotEqual => {
                        TY_BOOLEAN
                    }
                    BinOpKind::Set => {
                        lhs_ty
                    }
                }
            }
        };

        *ty
    }

    fn typecheck_function_call(&mut self,
                               fn_sig: FnSignature,
                               args: Vec<Ty>,
                               pos: usize) -> Ty {
        if fn_sig.params.len() != args.len() {
            self.report_analyze_err_at(pos,
                format!("Expected {} arguments, found {} arguments instead",
                        fn_sig.params.len(),
                        args.len()));
        }

        for i in 0..args.len() {
            self.union_ty(fn_sig.params[i], args[i], pos); //TODO: better
        }

        fn_sig.return_ty
    }

    fn raise(&mut self) {
        self.variables.push(HashMap::new());
    }

    fn fall(&mut self) {
        self.variables.pop();
    }

    fn declare_variable(&mut self, name: &String, ty: Ty, pos: usize) {
        if self.variables.last_mut().unwrap().contains_key(name) {
            self.report_analyze_err_at(pos,
                format!("Variable with name `{}` already declared in scope", name));
        }

        let scope = self.variables.last_mut().unwrap();
        scope.insert(name.clone(), ty);
    }

    fn get_variable_type(&mut self, name: &String, pos: usize) -> Ty {
        for scope in self.variables.iter().rev() {
            if scope.contains_key(name) {
                return scope[name];
            }
        }

        self.report_analyze_err_at(pos,
            format!("Variable with name `{}` not declared in scope", name));
    }

    fn get_function_signature(&mut self, name: &String) -> FnSignature {
        self.functions.get_mut(name).unwrap().clone() //TODO: add error panic!("")
    }

    fn set_return_type(&mut self, return_ty: Ty) {
        self.return_ty = return_ty;
    }

    fn get_return_type(&self) -> Ty {
        self.return_ty
    }

    fn initialize_ty(&mut self, ast_ty: &AstType) -> Ty {
        let ty_id = self.ty_new_id;
        self.ty_new_id += 1;

        let analyze_ty = match ast_ty {
            &AstType::Infer => AnalyzeType::Infer,
            &AstType::None => AnalyzeType::Nothing,
            &AstType::Int => AnalyzeType::Int,
            &AstType::UInt => AnalyzeType::UInt,
            &AstType::Float => AnalyzeType::Float,
            &AstType::Char => AnalyzeType::Char,
            &AstType::Bool => AnalyzeType::Boolean,
            &AstType::String => AnalyzeType::String,
            &AstType::Array { ref ty } => {
                let inner_ty = self.initialize_ty(ty.as_ref());
                AnalyzeType::Array(inner_ty)
            }
            &AstType::Tuple { ref types } => {
                let tuple_tys: Vec<_> = types.iter().map(|t| self.initialize_ty(t)).collect();
                AnalyzeType::Tuple(tuple_tys)
            }
        };

        self.ty_variables.insert(ty_id, analyze_ty);
        ty_id
    }

    fn new_infer_type(&mut self) -> Ty {
        self.initialize_ty(&mut AstType::Infer)
    }

    fn make_tuple_ty(&mut self, tys: Vec<Ty>) -> Ty {
        let ty_id = self.ty_new_id;
        self.ty_new_id += 1;

        self.ty_variables.insert(ty_id, AnalyzeType::Tuple(tys)); //TODO: expect none
        ty_id
    }

    fn make_array_ty(&mut self, inner_ty: Ty) -> Ty {
        let ty_id = self.ty_new_id;
        self.ty_new_id += 1;

        self.ty_variables.insert(ty_id, AnalyzeType::Array(inner_ty));
        ty_id
    }

    fn union_ty(&mut self, ty1: Ty, ty2: Ty, pos: usize) {
        if ty1 == ty2 {
            return;
        }

        if let AnalyzeType::Same(ty1_same) = self.ty_variables[&ty1] {
            self.union_ty(ty1_same, ty2, pos);
            return;
        }

        if let AnalyzeType::Same(ty2_same) = self.ty_variables[&ty2] {
            self.union_ty(ty1, ty2_same, pos);
            return;
        }

        match (self.ty_variables[&ty1].clone(), self.ty_variables[&ty2].clone()) {
            (AnalyzeType::Infer, _) => {
                self.ty_variables.insert(ty1, AnalyzeType::Same(ty2));
            }
            (_, AnalyzeType::Infer) => {
                self.ty_variables.insert(ty2, AnalyzeType::Same(ty1));
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
            (AnalyzeType::Tuple(ty1_tys),
             AnalyzeType::Tuple(ty2_tys)) => {
                if ty1_tys.len() != ty2_tys.len() {
                    self.report_analyze_err_at(pos,
                        format!("Cannot consolidate tuple types of varying lengths"));
                }
                for i in 0..ty1_tys.len() {
                    self.union_ty(ty1_tys[i], ty2_tys[i], pos);
                }
            },
            (AnalyzeType::Array(inner_ty1),
             AnalyzeType::Array(inner_ty2)) => {
                self.union_ty(inner_ty1, inner_ty2, pos);
            }
            _ => self.report_analyze_err_at(pos,
                format!("Cannot consolidate types"))
        }
    }

    fn extract_array_element_ty(&mut self, array_ty: Ty, pos: usize) -> Ty {
        match self.ty_variables[&array_ty] {
            AnalyzeType::Same(same_ty) => self.extract_array_element_ty(same_ty, pos),
            AnalyzeType::Array(inner_ty) => inner_ty,
            _ => self.report_analyze_err_at(pos,
                format!("Cannot extract array type"))
        }
    }

    fn is_boolean_ty(&self, ty: Ty) -> bool {
        match self.ty_variables[&ty] {
            AnalyzeType::Same(same_ty) =>
                self.is_boolean_ty(same_ty),
            AnalyzeType::Boolean => true,
            _ => false
        }
    }

    fn is_numeric_ty(&self, ty: Ty) -> bool {
        match self.ty_variables[&ty] {
            AnalyzeType::Same(same_ty) =>
                self.is_numeric_ty(same_ty),
            AnalyzeType::Int |
            AnalyzeType::UInt |
            AnalyzeType::Float => true,
            _ => false
        }
    }

    fn report_analyze_err_at(&self, pos: usize, err: String) -> ! {
        let fr = self.file.as_ref().unwrap();
        let (line, col) = fr.get_row_col(pos);
        let line_str = fr.get_line_from_pos(pos);

        println!("");
        // TODO: fix tabs later
        println!("Error \"{}\" encountered on line {}:", err, line + 1); //TODO: in file

        println!("| {}", line_str);
        for _ in 0..(col + 2) {
            print!("-");
        }
        println!("^");
        exit(1);
    }
}
