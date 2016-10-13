# Grammar

## Intro
Before I start writing the parser for Cheshire, I'll take a bit of time to write a concise grammar for what I plan on supporting in the first version of the language. I'll be using a custom syntax that looks a lot like EBNF (Extended Backus-Naur Form) to describe the language's parsing elements. Hopefully this can serve as a high-level guide when I'm actually implementing the parser itself, and for answering questions on how the language is structured in general (but don't worry, I'll write a more programmer-centric Cheshire guide later).

## Identifiers and Keywords

An `identifier` is any string matching the regex `[A-Za-z_][A-Za-z0-9_]*` which is not a reserved keyword or type.

```antlr
binary_operator
          : '+' | '-' | '*' | '/' | '%' | '^' | '&' | '|' | ">>" | "<<"
          | '>' | '<' | "<=" | ">=" | "==" | "!="
          ;

unary_operator
          : '!' | '-' ;

builtin_type
          : "Int" | "UInt" | "Bool" | "String" | "Float" | "Char" | "()" ;
```

The reserved keywords are:

 ```
fn let if while return assert break continue
 ```

## Functions

```antlr
function  : "fn" identifier '(' [ fn_parameter [ ',' fn_parameter ] * ] ? ')'
                 [ "->" typename ] ? block ;

fn_parameter : identifier ':' typename ;
```

Functions are declared with an initial `fn` keyword, followed by a name, and a comma separated list of identifer and typename pairs separated with a colon enclosed by parentheses, or else an empty pair of parentheses if there are no parameters. The declaration can be followed by an arrow `->` and a typename if the function is expected to return a value, and then the function signature is followed by a block of code that will be its definition.

## Code Blocks and Statements

```antlr
block     : '{' [ statement ] * '}' ;

statement : block
          | "let" identifier [ ':' typename ] ? '=' expression '.' // Variable declaration
          | expression_statement '.'                               // Expression-like statement
          | "if" expression block [ "else" block_or_if ] ?         // If branch
          | "while" expression block                               // While loop
          | "break" '.' | "continue" '.'                           // Control flow
          | "return" [ expression ] ? '.'                          // Function return
          | "assert" expression '.'
          ;

block_or_if
          : block
          | "if" expression block [ "else" block_or_if ] ?
          ;
```

A code block is a list of statements and control flow structures (`while`, `if`, etc.) enclosed in curly braces.
A statement is more or less associated with an "action," whether it be declaration, branching, looping, method call, etc. A few of these statements can also act as parts of larger expressions, and those are grouped into the expression_statement group which will be discussed below.

## Expressions

Expressions are broken up into 3 categories, expression_statements, lval_expressions, and pure expressions. Expression_statements are expressions which can show up as sub-expressions, but also work as statements in their own right. These are things like assignment, function calls, and struct member function calls. Lval_expressions are those expressions which may show up on the left hand side of an assignment.

```antlr
expression: expression_statement
          | lval_expression
          | literal
          | '(' expression ')'
          | unary_operator expression
          | expression binary_operator expression
          ;

expression_statement
          : lval_expression '=' expression
          | identifier '(' [ expression [ ',' expression ] * ] ? ')'
          ;

lval_expression
          : '(' lval_expression ')'
          | identifier
          | expression '[' expression ']'
          ;

literal   :
          | string_literal
          | numeric_literal
          | char_literal
          | "True" | "False"
          | identifier
          ;
```

## Typenames
```antlr
typename  : builtin_type
          | '[' typename ']'
          | '(' typename ',' ')'
          | '(' typename [',' typename ] + ')'
          ;
```

Types can either be:
* Built in, such as `Int32`.
* Arrays like `[Int32]`.
* The empty type, `()`.
* A tuple: `(Int32,)`, `(TypeOne, TypeTwo)`.
