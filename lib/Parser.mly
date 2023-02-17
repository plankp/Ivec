%{
open Ast
%}

%token LPAREN RPAREN
%token ADD SUB SET
%token LET IN
%token <Z.t> INT
%token <string> STR
%token <string> IDENT
%token EOF

%start <expr option> prog

%%

prog:
  | EOF { None }
  | e = expr; EOF { Some e }

expr:
  | e = expr_infix { e }
  | LET; n = IDENT; SET; i = expr; IN; e = expr { ELet (n, i, e) }

expr_infix:
  | l = expr_infix; ADD; r = expr_prefix { EAdd (l, r) }
  | l = expr_infix; SUB; r = expr_prefix { ESub (l, r) }
  | e = expr_prefix { e }

expr_prefix:
  | ADD; e = expr_vector { EAdd (EInt Z.zero, e) }
  | SUB; e = expr_vector { ESub (EInt Z.zero, e) }
  | e = expr_vector { e }

expr_vector:
  | es = expr_atoms { match es with [e] -> e | _ -> ESeq es }

expr_atom:
  | LPAREN; RPAREN { ESeq [] }
  | LPAREN; e = expr; RPAREN; { e }
  | v = IDENT { EVar v }
  | v = INT { EInt v }
  | v = STR { EStr v }

expr_atoms:
  | e = expr_atom; es = expr_atoms { e :: es }
  | e = expr_atom { [e] }
