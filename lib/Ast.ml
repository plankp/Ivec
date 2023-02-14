type expr =
  | EStr of string
  | EInt of Z.t
  | EAdd of expr * expr
  | ESub of expr * expr
  | ESeq of expr list
