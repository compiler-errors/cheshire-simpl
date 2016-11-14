mod ty;

pub use self::ty::*;
use util::FileReader;
use parser::*;
use std::collections::HashMap;
use std::process::exit;

/** The analyzer "module" is mainly concerned with assigning type information and
  * catching final errors (such as type errors), as well as associating each
  * expression with a type, associating variables with a global number, and each
  * string with a global number as well.
  *
  * In the future, the module should also be responsible for resolving the
  * conversion of local names to global names `fn_name` to `pkg.pkg.fn_name`.
  */
pub struct Analyzer<'a> {
    /// Map which associates a function name to a signature
    pub fn_signatures: HashMap<String, FnSignature>,
    /// Map which associates a function name to its definition (block)
    pub fns: HashMap<String, AstFunction>, // TODO: probably just store the block itself...

    /// Keep track of being inside a "breakable" block
    pub breakable: bool,

    // Keep track of object information
    /// Associates an object name to a unique ID
    pub obj_skeletons: HashMap<String, AnalyzeObject>,
    /// Associates an object ID to a parsed object
    pub objs: HashMap<String, AstObject>,

    // Keep track of variable information
    /// "Scoped map" which associates a variable name to its VarId
    var_ids: Vec<HashMap<String, VarId>>,
    /// Map which associates a VarId to its underlying type
    pub var_tys: HashMap<VarId, Ty>,
    /// Counter which stores the next free VarId
    var_new_id: VarId,
    /// Variable storing the return type of the outer function
    return_ty: Ty,

    // Keep track of string information
    /// Counter which stores the next free StringId
    str_new_id: StringId,
    /// Map which associates a StringId with its corresponding String
    pub strings: HashMap<StringId, String>,

    /// File which is currently being analyzed
    file: Option<FileReader<'a>>,

    // Type System
    /// Map which associates a Ty id with an underlying AnalyzeType
    pub ty_map: HashMap<Ty, AnalyzeType>,
    /// Counter which stores the next free Ty id
    ty_new_id: Ty,
}

impl<'a> Analyzer<'a> {
    pub fn new() -> Analyzer<'a> {
        let mut ty_map = HashMap::new();
        // Insert all of the "basic" fundamental types
        ty_map.insert(TY_NOTHING, AnalyzeType::Nothing);
        ty_map.insert(TY_BOOLEAN, AnalyzeType::Boolean);
        ty_map.insert(TY_INT, AnalyzeType::Int);
        ty_map.insert(TY_UINT, AnalyzeType::UInt);
        ty_map.insert(TY_FLOAT, AnalyzeType::Float);
        ty_map.insert(TY_CHAR, AnalyzeType::Char);
        ty_map.insert(TY_STRING, AnalyzeType::String);

        Analyzer {
            fn_signatures: HashMap::new(),
            fns: HashMap::new(),
            breakable: false,
            var_ids: Vec::new(),
            var_tys: HashMap::new(),
            var_new_id: VAR_FIRST_NEW_ID,
            return_ty: 0,
            obj_skeletons: HashMap::new(),
            objs: HashMap::new(),
            strings: HashMap::new(),
            str_new_id: STR_FIRST_NEW_ID,
            file: None,
            ty_map: ty_map,
            ty_new_id: TY_FIRST_NEW_ID,
        }
    }

    /// Analyze a file
    pub fn analyze_file(&mut self, mut f: ParseFile<'a>) {
        let ParseFile { file, mut objects, functions } = f;

        self.file = Some(file); //TODO: this is wonky, fix?

        for obj in &objects {
            let analyze_obj = self.initialize_object(obj);
            self.obj_skeletons.insert(obj.name.clone(), analyze_obj);
        }

        for fun in &functions {
            if self.fn_signatures.contains_key(&fun.name) {
                self.report_analyze_err_at(fun.pos,
                                           format!("Duplicate function name `{}`", fun.name));
            }

            // Convert a  vec of AstType to Ty id by a mapping operation
            let arg_tys: Vec<_> = fun.parameter_list
                .iter()
                .map(|p| self.initialize_ty(&p.ty))
                .collect();
            let return_ty = self.initialize_ty(&fun.return_type);
            // And insert the function signature into a map associated with its name
            self.fn_signatures.insert(fun.name.clone(), FnSignature::new(arg_tys, return_ty));
        }

        // Let's use a drain so we can take ownership of the function
        for mut fun in functions {
            // First analyze the function
            self.analyze_function(&mut fun);
            // And then store it so we can emit it later
            self.fns.insert(fun.name.clone(), fun);
        }

        for mut obj in objects {
            self.analyze_object(&mut obj);
            self.objs.insert(obj.name.clone(), obj);
        }
    }

    /// Analyze a function
    fn analyze_function(&mut self, f: &mut AstFunction) {
        // Raise a scope level
        self.raise();
        // Store the first VarId associated with the function
        f.beginning_of_vars = self.var_new_id;

        // Declare the parameters as variables
        for &mut AstFnParameter { ref name, ref mut ty, pos } in &mut f.parameter_list {
            let param_ty = self.initialize_ty(ty);
            self.declare_variable(name, param_ty, pos);
        }

        // Save the return type
        let return_ty = self.initialize_ty(&mut f.return_type);
        self.set_return_type(return_ty);

        // Analyze the function's body
        self.analyze_block(&mut f.definition);

        // Store the last VarId associated with the function
        // The VarId's used by the function are given by the range [beginning, end)
        f.end_of_vars = self.var_new_id;
        // Lower the scope
        self.fall();
    }

    /// Analyze a block of statements
    fn analyze_block(&mut self, block: &mut AstBlock) {
        // TODO: make sure break and continue exist only in whiles!!!!
        self.raise();

        for stmt in &mut block.statements {
            self.analyze_stmt(stmt);
        }

        self.fall();
    }

    /// Analyze a single statement
    fn analyze_stmt(&mut self, stmt: &mut AstStatement) {
        let pos = stmt.pos; // Store the position of the statement (for errors!)

        match &mut stmt.stmt {
            &mut AstStatementData::Block { ref mut block } => {
                self.analyze_block(block);
            }
            &mut AstStatementData::Let { ref mut var_name,
                                         ref mut ty,
                                         ref mut value,
                                         ref mut var_id } => {
                // Initialize the declared type of the `let` (or infer)
                let let_ty = self.initialize_ty(ty);
                // Initialize the type of the expression which the `let` is set to
                let expr_ty = self.typecheck_expr(value);
                // We now need to union these types
                self.union_ty(let_ty, expr_ty, pos);
                // And then declare it as a usable variable
                *var_id = self.declare_variable(var_name, let_ty, pos);
            }
            &mut AstStatementData::If { ref mut condition, ref mut block, ref mut else_block } => {
                let ty = self.typecheck_expr(condition);
                // We know it must ALWAYS be a boolean
                self.union_ty(ty, TY_BOOLEAN, pos);
                self.analyze_block(block);
                self.analyze_block(else_block);
            }
            &mut AstStatementData::While { ref mut condition, ref mut block } => {
                // TODO: make sure break and continue exist only in whiles!!!!
                let ty = self.typecheck_expr(condition);
                self.union_ty(ty, TY_BOOLEAN, pos);
                // Store the old "breakable" condition while we analyze the block
                let old_breakable = self.breakable;
                self.breakable = true;
                self.analyze_block(block);
                self.breakable = old_breakable;
                // and restore it when we're done
            }
            &mut AstStatementData::Break |
            &mut AstStatementData::Continue => {
                if !self.breakable {
                    self.report_analyze_err_at(stmt.pos,
                                               format!("Cannot `break` or `continue` outside of \
                                                        a `while`"))
                }
            }
            &mut AstStatementData::NoOp => {}
            &mut AstStatementData::Return { ref mut value } => {
                // Simple: union expected return type and actual type of value being returned
                let ty = self.typecheck_expr(value);
                let return_ty = self.get_return_type();
                self.union_ty(ty, return_ty, pos);
            }
            &mut AstStatementData::Assert { ref mut condition } => {
                // Union condition with BOOLEAN
                let ty = self.typecheck_expr(condition);
                self.union_ty(ty, TY_BOOLEAN, pos);
            }
            &mut AstStatementData::Expression { ref mut expression } => {
                self.typecheck_expr(expression);
            }
        }
    }

    fn typecheck_expr(&mut self, expression: &mut AstExpression) -> Ty {
        let &mut AstExpression { ref mut expr, ref mut ty, pos } = expression;

        *ty = match expr {
            &mut AstExpressionData::Nothing => TY_NOTHING,
            &mut AstExpressionData::True => TY_BOOLEAN,
            &mut AstExpressionData::False => TY_BOOLEAN,
            &mut AstExpressionData::Null => self.new_null_infer_ty(),
            &mut AstExpressionData::String { ref string, ref mut id, .. } => {
                // Save string in map, first
                *id = self.str_new_id;
                self.str_new_id += 1;
                self.strings.insert(*id, string.clone());
                TY_STRING
            }
            &mut AstExpressionData::Int(_) => TY_INT,
            &mut AstExpressionData::UInt(_) => TY_UINT,
            &mut AstExpressionData::Float(_) => TY_FLOAT,
            &mut AstExpressionData::Char(_) => TY_CHAR,
            &mut AstExpressionData::Identifier { ref name, ref mut var_id } => {
                // Get variable, failing if the variable doesn't exist!
                *var_id = self.get_variable_id(name, pos);
                self.get_variable_type(*var_id)
            }
            &mut AstExpressionData::Tuple { ref mut values } => {
                let tys: Vec<_> = values.iter_mut().map(|v| self.typecheck_expr(v)).collect();
                self.make_tuple_ty(tys)
            }
            &mut AstExpressionData::Array { ref mut elements } => {
                let ty = self.new_infer_ty(); // We start out as an [_] array...
                for ref mut element in elements {
                    let elt_ty = self.typecheck_expr(element);
                    // We need to union the array's inner type with each element
                    // since each element must essentially be the same type
                    // (union operator is transitive...)
                    self.union_ty(ty, elt_ty, element.pos);
                }
                self.make_array_ty(ty)
            }
            &mut AstExpressionData::Call { ref mut name, ref mut args } => {
                let arg_tys: Vec<_> = args.iter_mut().map(|v| self.typecheck_expr(v)).collect();
                let fn_sig = self.get_function_signature(name, expression.pos);
                self.typecheck_function_call(fn_sig, arg_tys, pos)
            }
            &mut AstExpressionData::Access { ref mut accessible, ref mut idx } => {
                let idx_ty = self.typecheck_expr(idx);
                self.union_ty(idx_ty, TY_UINT, idx.pos); // The index should be uint
                let array_ty = self.typecheck_expr(accessible);
                // We "extract" the inner type T out of the array type [T].
                self.extract_array_inner_ty(array_ty, accessible.pos)
            }
            &mut AstExpressionData::TupleAccess { ref mut accessible, idx } => {
                let tuple_ty = self.typecheck_expr(accessible);
                self.extract_tuple_inner_ty(tuple_ty, idx, accessible.pos)
            }
            &mut AstExpressionData::Not(ref mut expr) => {
                let ty = self.typecheck_expr(expr);
                if self.is_integral_ty(ty) || self.is_boolean_ty(ty) {
                    ty
                } else {
                    self.report_analyze_err_at(expr.pos,
                                               format!("Expected sub-expression of type `Int`, \
                                                        `UInt` or `Bool`"));
                }
            }
            &mut AstExpressionData::Negate(ref mut expr) => {
                let ty = self.typecheck_expr(expr);
                if self.is_numeric_ty(ty) {
                    ty
                } else {
                    self.report_analyze_err_at(expr.pos,
                                               format!("Expected numeric sub-expression"));
                }
            }
            &mut AstExpressionData::BinOp { kind, ref mut lhs, ref mut rhs } => {
                let lhs_ty = self.typecheck_expr(lhs);
                let rhs_ty = self.typecheck_expr(rhs);
                self.union_ty(lhs_ty, rhs_ty, pos);
                match kind {
                    BinOpKind::Multiply | BinOpKind::Divide | BinOpKind::Modulo |
                    BinOpKind::Add | BinOpKind::Subtract => {
                        if !self.is_numeric_ty(lhs_ty) {
                            self.report_analyze_err_at(pos,
                                                       format!("Expected numeric sub-expression"));
                        }
                        lhs_ty
                    }
                    BinOpKind::ShiftLeft | BinOpKind::ShiftRight => {
                        if !self.is_integral_ty(lhs_ty) {
                            self.report_analyze_err_at(pos,
                                                       format!("Expected integer sub-expression"));
                        }
                        lhs_ty
                    }
                    BinOpKind::Greater | BinOpKind::Less | BinOpKind::GreaterEqual |
                    BinOpKind::LessEqual => {
                        if !self.is_numeric_ty(lhs_ty) {
                            self.report_analyze_err_at(pos,
                                                       format!("Expected numeric sub-expression"));
                        }
                        TY_BOOLEAN
                    }
                    BinOpKind::Xor | BinOpKind::And | BinOpKind::Or => {
                        // TODO: also numeric not float
                        if !self.is_boolean_ty(lhs_ty) {
                            self.report_analyze_err_at(pos,
                                                       format!("Expected sub-expression of type \
                                                                `Bool`"));
                        }
                        lhs_ty
                    }
                    BinOpKind::EqualsEquals | BinOpKind::NotEqual => TY_BOOLEAN,
                    BinOpKind::Set => lhs_ty,
                }
            }
        };

        *ty
    }

    /// Typechecks an argument type array against a function signature,
    /// and returns the function's return type.
    fn typecheck_function_call(&mut self, fn_sig: FnSignature, args: Vec<Ty>, pos: usize) -> Ty {
        if fn_sig.params.len() != args.len() {
            self.report_analyze_err_at(pos,
                                       format!("Expected {} arguments, found {} arguments \
                                                instead",
                                               fn_sig.params.len(),
                                               args.len()));
        }

        for i in 0..args.len() {
            self.union_ty(fn_sig.params[i], args[i], pos); //TODO: better
        }

        fn_sig.return_ty
    }

    fn initialize_object(&mut self, obj: &AstObject) -> AnalyzeObject {
        let mut member_tys = HashMap::new();
        let mut member_signatures = HashMap::new();
        let mut static_signatures = HashMap::new();

        for ref mem in &obj.members {
            if member_tys.contains_key(&mem.name) {
                self.report_analyze_err_at(mem.pos,
                                           format!("Duplicate member named `{}`", mem.name));
            }

            let mem_ty = self.initialize_ty(&mem.ast_ty);
            member_tys.insert(mem.name.clone(), mem_ty);
        }

        for ref fun in &obj.functions {
            let arg_tys: Vec<_> = fun.parameter_list
                .iter()
                .map(|p| self.initialize_ty(&p.ty))
                .collect();
            let return_ty = self.initialize_ty(&fun.return_type);

            if fun.has_self {
                member_signatures.insert(fun.name.clone(), FnSignature::new(arg_tys, return_ty));
            } else {
                static_signatures.insert(fun.name.clone(), FnSignature::new(arg_tys, return_ty));
            }
        }

        AnalyzeObject::new(member_tys, member_signatures, static_signatures)
    }

    fn analyze_object(&mut self, obj: &mut AstObject) {
        self.self_ty = obj.id;
    }

    /// Raises the variable scope up one level.
    /// (i.e. enter a block or other context where variables are unique)
    fn raise(&mut self) {
        self.var_ids.push(HashMap::new());
    }

    /// Lower the variable scope one level.
    fn fall(&mut self) {
        self.var_ids.pop();
    }

    /// Declare a variable with a specific type in the variable scope, assigning to it a unique VarId
    fn declare_variable(&mut self, name: &String, ty: Ty, pos: usize) -> VarId {
        let id = self.var_new_id;
        self.var_new_id += 1;

        if self.var_ids.last_mut().unwrap().contains_key(name) {
            self.report_analyze_err_at(pos,
                                       format!("Variable with name `{}` already declared in \
                                                scope",
                                               name));
        }

        self.var_ids.last_mut().unwrap().insert(name.clone(), id);
        self.var_tys.insert(id, ty);

        id
    }

    /// Get the VarId associated with a name in the highest scope (due to variable shadowing)
    fn get_variable_id(&mut self, name: &String, pos: usize) -> VarId {
        for scope in self.var_ids.iter().rev() {
            if scope.contains_key(name) {
                return scope[name];
            }
        }

        self.report_analyze_err_at(pos,
                                   format!("Variable with name `{}` not declared in scope", name));
    }

    /// Get the Ty associated with a VarId
    fn get_variable_type(&mut self, var_id: VarId) -> Ty {
        self.var_tys[&var_id]
    }

    /// Get a function signature
    fn get_function_signature(&mut self, name: &String, pos: usize) -> FnSignature {
        if !self.fn_signatures.contains_key(name) {
            self.report_analyze_err_at(pos, format!("Function with name `{}` not declared", name));
        }

        self.fn_signatures.get(name).unwrap().clone() //TODO: add error panic!("")
    }

    /// Set expected return type
    fn set_return_type(&mut self, return_ty: Ty) {
        self.return_ty = return_ty;
    }

    /// Get expected return type
    fn get_return_type(&self) -> Ty {
        self.return_ty
    }

    /// Convert an AstType from parsing into a Ty id for use in Analyzer
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

        self.ty_map.insert(ty_id, analyze_ty);
        ty_id
    }

    /// Make a new Ty associated (initially) with the `_` Infer type.
    fn new_infer_ty(&mut self) -> Ty {
        self.initialize_ty(&mut AstType::Infer)
    }

    /// Make a new Ty associated with the "NullInfer" type.
    /// The NullInfer type can be unioned with any type that is nullable (array, string).
    fn new_null_infer_ty(&mut self) -> Ty {
        let ty_id = self.ty_new_id;
        self.ty_new_id += 1;
        self.ty_map.insert(ty_id, AnalyzeType::NullInfer);

        ty_id
    }

    /// Make a new Ty representing a tuple containing all of the passed Tys
    fn make_tuple_ty(&mut self, tys: Vec<Ty>) -> Ty {
        let ty_id = self.ty_new_id;
        self.ty_new_id += 1;

        self.ty_map.insert(ty_id, AnalyzeType::Tuple(tys)); //TODO: expect none
        ty_id
    }

    /// Make an array Ty with the inner type given by inner_ty
    fn make_array_ty(&mut self, inner_ty: Ty) -> Ty {
        let ty_id = self.ty_new_id;
        self.ty_new_id += 1;

        self.ty_map.insert(ty_id, AnalyzeType::Array(inner_ty));
        ty_id
    }

    /** Union two types
      *
      * Unioning two types ensures that they're "essentially" the same type after union.
      * Usually this means setting Infers to agree with the other type, or making sure
      * that two definite types are identical.
      */
    fn union_ty(&mut self, ty1: Ty, ty2: Ty, pos: usize) {
        if ty1 == ty2 {
            return;
        }

        // If ty1 is Same, then union the referenced type instead
        if let AnalyzeType::Same(ty1_same) = self.ty_map[&ty1] {
            self.union_ty(ty1_same, ty2, pos);
            return;
        }

        // If ty2 is Same, then union the referenced type instead
        if let AnalyzeType::Same(ty2_same) = self.ty_map[&ty2] {
            self.union_ty(ty1, ty2_same, pos);
            return;
        }

        match (self.ty_map[&ty1].clone(), self.ty_map[&ty2].clone()) {
            // Infer can union with any type, and make it into a Same
            (AnalyzeType::Infer, _) => {
                self.ty_map.insert(ty1, AnalyzeType::Same(ty2));
            }
            (_, AnalyzeType::Infer) => {
                self.ty_map.insert(ty2, AnalyzeType::Same(ty1));
            }
            // NullInfer can union with any *nullable* type
            (AnalyzeType::NullInfer, t) => {
                if !self.is_nullable(t) {
                    self.report_analyze_err_at(pos,
                                               format!("`null` may only be assigned to types \
                                                        which are nullable."));
                }
                self.ty_map.insert(ty1, AnalyzeType::Same(ty2));
            }
            (t, AnalyzeType::NullInfer) => {
                if !self.is_nullable(t) {
                    self.report_analyze_err_at(pos,
                                               format!("`null` may only be assigned to types \
                                                        which are nullable."));
                }
                self.ty_map.insert(ty2, AnalyzeType::Same(ty1));
            }
            // Duplicates can union without action...
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
                    self.report_analyze_err_at(pos,
                                               format!("Cannot consolidate tuple types of \
                                                        varying lengths"));
                }
                for i in 0..ty1_tys.len() {
                    self.union_ty(ty1_tys[i], ty2_tys[i], pos);
                }
            }
            // Arrays union if their inner types union as well
            (AnalyzeType::Array(inner_ty1), AnalyzeType::Array(inner_ty2)) => {
                self.union_ty(inner_ty1, inner_ty2, pos);
            }
            // Otherwise, welp!
            _ => self.report_analyze_err_at(pos, format!("Cannot consolidate types")),
        }
    }

    // Return true if type can be assigned null (currently String and arrays)
    fn is_nullable(&self, ty: AnalyzeType) -> bool {
        match ty {
            AnalyzeType::String |
            AnalyzeType::Array(_) => true,
            _ => false,
        }
    }

    // Extract the type that the array stores
    fn extract_array_inner_ty(&self, array_ty: Ty, pos: usize) -> Ty {
        match self.ty_map[&array_ty] {
            AnalyzeType::Same(same_ty) => self.extract_array_inner_ty(same_ty, pos),
            AnalyzeType::Array(inner_ty) => inner_ty,
            _ => self.report_analyze_err_at(pos, format!("Cannot extract array type")),
        }
    }

    // Extract the tuple's member type at idx, or panic if out of bounds
    fn extract_tuple_inner_ty(&self, tuple_ty: Ty, idx: u32, pos: usize) -> Ty {
        match self.ty_map[&tuple_ty] {
            AnalyzeType::Same(same_ty) => self.extract_tuple_inner_ty(same_ty, idx, pos),
            AnalyzeType::Tuple(ref tys) => {
                if tys.len() <= (idx as usize) {
                    self.report_analyze_err_at(pos, format!("Tuple access out of bounds"))
                } else {
                    tys[idx as usize]
                }
            }
            _ => self.report_analyze_err_at(pos, format!("Cannot extract tuple type")),
        }
    }

    fn is_boolean_ty(&self, ty: Ty) -> bool {
        match self.ty_map[&ty] {
            AnalyzeType::Same(same_ty) => self.is_boolean_ty(same_ty),
            AnalyzeType::Boolean => true,
            _ => false,
        }
    }

    fn is_float_ty(&self, ty: Ty) -> bool {
        match self.ty_map[&ty] {
            AnalyzeType::Same(same_ty) => self.is_float_ty(same_ty),
            AnalyzeType::Float => true,
            _ => false,
        }
    }

    fn is_integral_ty(&self, ty: Ty) -> bool {
        match self.ty_map[&ty] {
            AnalyzeType::Same(same_ty) => self.is_integral_ty(same_ty),
            AnalyzeType::Int => true,
            AnalyzeType::UInt => true,
            _ => false,
        }
    }

    fn is_numeric_ty(&self, ty: Ty) -> bool {
        match self.ty_map[&ty] {
            AnalyzeType::Same(same_ty) => self.is_numeric_ty(same_ty),
            AnalyzeType::Int | AnalyzeType::UInt | AnalyzeType::Float => true,
            _ => false,
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
