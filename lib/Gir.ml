let ( let< ) = Result.bind

type 'a cnode = {
  mutable prev : 'a cnode;
  mutable next : 'a cnode;
  mutable data : 'a;
}

let mk_cnode (data : 'a) : 'a cnode =
  let rec node = { data; prev = node; next = node } in node

let lnode_is_singleton (node : 'a cnode) : bool =
  (* assuming well-formed nodes, then a circular list with a single node must
   * have both prev and next point to itself. *)
  node.prev == node

let lnode_link (dst_last : 'a cnode) (src_head : 'a cnode) =
  let dst_head = dst_last.next in
  let src_last = src_head.prev in

  dst_last.next <- src_head;
  src_head.prev <- dst_last;

  src_last.prev <- dst_head;
  dst_head.next <- src_last

let lnode_unlink (node : 'a cnode) =
  node.prev.next <- node.next;
  node.next.prev <- node.prev;

  node.prev <- node;
  node.next <- node

type gnode =
  | LetVal of binder * gnode * gnode
  | Lam of binder * gnode
  | Var of binder cnode
  | Int of Z.t
  | Str of string
  | Vec of gnode list
  | PrimBop of prim_bop * gnode * gnode
  | Insert of gnode * int * gnode
(* mapk : trip count * appf * v1 * ... * vk *)
  | Map1 of int option * gnode * gnode
  | Map2 of int option * gnode * gnode * gnode

and prim_bop =
  | Add
  | Sub

and binder = {
  name : string option;               (* binding name (for humans) *)
  mutable occ : binder cnode option;  (* one of the (usage) occurrences *)
  mutable parent : binder;            (* union-find *)
}

let mk_binder (name : string option) : binder =
  let rec node = { name; occ = None; parent = node } in node

let find_root_binder (b : binder) =
  if b.parent == b || b.parent.parent == b.parent then
    (* either this is the root or is directly linked to the root *)
    b.parent
  else
    (* there is at least one extra node between this node and the root:
     * we want to do path compression *)
    let rec compress root = function
      | [] -> root
      | x :: xs -> x.parent <- root; compress root xs in
    let rec find_root acc b =
      if b.parent == b then compress b.parent acc
      else find_root (b :: acc) b.parent in
    find_root [b] b.parent

let merge_binders (repr : binder) (aug : binder) =
  let repr = find_root_binder repr in
  let aug = find_root_binder aug in

  (* always add new nodes under the selected representative's root *)
  if repr != aug then aug.parent <- repr

type t =
  | TAny
  | TInt
  | TStr
  | TVec of t * int option

let rec to_string = function
  | TAny -> "any"
  | TInt -> "int"
  | TStr -> "string"
  | TVec (t, k) ->
    let k = Option.value ~default:~-1 k |> string_of_int in
    "(" ^ k ^ " of " ^ (to_string t) ^ ")"

let rec unify x y =
  match x, y with
    | TInt, TInt -> TInt
    | TStr, TStr -> TStr
    | TVec (t1, k1), TVec (t2, k2) ->
      TVec (unify t1 t2, if k1 = k2 then k1 else None)
    | _ -> TAny

let rec try_numeric_broadcast op (p, pty) (q, qty) =
  let emit_map1 vec eltTy trip scl sclTy flip =
    let binder = mk_binder None in
    let node = mk_cnode binder in
    binder.occ <- Some node;

    let lhs = if flip then (Var node, eltTy) else (scl, sclTy) in
    let rhs = if flip then (scl, sclTy) else (Var node, eltTy) in
    let< (body, ty) = try_numeric_broadcast op lhs rhs in
    Ok (Map1 (trip, Lam (binder, body), vec), TVec (ty, trip)) in

  let emit_map2 v1 eltTy1 v2 eltTy2 trip =
    (* map2 feeds two values, so we need two binders *)
    let lhsBinder = mk_binder None in
    let rhsBinder = mk_binder None in
    let lhsNode = mk_cnode lhsBinder in
    let rhsNode = mk_cnode rhsBinder in
    lhsBinder.occ <- Some lhsNode;
    rhsBinder.occ <- Some rhsNode;

    let< (body, ty) = try_numeric_broadcast
      op ((Var lhsNode), eltTy1) ((Var rhsNode), eltTy2) in
    Ok (Map2 (trip, Lam (lhsBinder, (Lam (rhsBinder, body))), v1, v2),
      TVec (ty, trip)) in

  match pty, qty with
    | TInt, TInt -> Ok (op p q, TInt)

    | TVec (t, trip), TInt -> emit_map1 p t trip q qty true
    | TInt, TVec (t, trip) -> emit_map1 q t trip p pty false

    (* give up if the sizes are known and different *)
    | TVec (t1, Some k1), TVec (t2, Some k2) when k1 = k2 ->
      emit_map2 p t1 q t2 (Some k1)
    | TVec (t1, Some _), TVec (t2, None)
    | TVec (t1, None), TVec (t2, _) ->
      emit_map2 p t1 q t2 None

    | _ -> Error (pty, qty)

let rec check = function
  | Ast.EStr v -> Ok (Str v, TStr)
  | Ast.EInt v -> Ok (Int v, TInt)
  | Ast.ESeq [] -> Ok (Vec [], TVec (TAny, Some 0))
  | Ast.ESeq (v :: vs) -> begin
    let rec loop acc k ty = function
      | [] -> Ok (Vec (List.rev acc), TVec (ty, Some k))
      | v :: vs ->
        let< (v, rty) = check v in
        loop (v :: acc) (k + 1) (unify ty rty) vs in
    let< (v, ty) = check v in
    loop [v] 1 ty vs
  end
  | Ast.EAdd (p, q) -> begin
    let< lhs = check p in
    let< rhs = check q in
    match try_numeric_broadcast (fun p q -> PrimBop (Add, p, q)) lhs rhs with
      | Ok _ as v -> v
      | Error (p, q) ->
        Error ("Unsupported " ^ (to_string p) ^ " + " ^ (to_string q))
  end
  | Ast.ESub (p, q) -> begin
    let< lhs = check p in
    let< rhs = check q in
    match try_numeric_broadcast (fun p q -> PrimBop (Sub, p, q)) lhs rhs with
      | Ok _ as v -> v
      | Error (p, q) ->
        Error ("Unsupported " ^ (to_string p) ^ " - " ^ (to_string q))
  end

let rec to_anf e k =
  match e with
    (* simple values are consumed directly *)
    | Var _ | Int _ | Str _ | Vec [] -> k e

    (* lambdas start a whole new continuation context *)
    | Lam (v, e) ->
      k (Lam (v, to_anf e (fun x -> x)))

    (* letval just needs to make sure the initializer is simple *)
    | LetVal (v, i, e) ->
      to_anf i (fun i -> LetVal (v, i, to_anf e k))

    (* we'll treat non-empty vectors as simple values for now... *)
    | Vec xs ->
      let rec loop acc = function
        | [] -> k (Vec (List.rev acc))
        | x :: xs -> to_anf x (fun x -> loop (x :: acc) xs) in
      loop [] xs

    | PrimBop (bop, p, q) ->
      to_anf p (fun p -> to_anf q (fun q ->
        let binder = mk_binder None in
        let node = mk_cnode binder in
        binder.occ <- Some node;
        LetVal (binder, PrimBop (bop, p, q), k (Var node))))

    | Insert (v, i, e) ->
      to_anf v (fun v -> to_anf e (fun e ->
        let binder = mk_binder None in
        let node = mk_cnode binder in
        binder.occ <- Some node;
        LetVal (binder, Insert (v, i, e), k (Var node))))

    | Map1 (tc, f, v) ->
      to_anf f (fun f -> to_anf v (fun v ->
        let binder = mk_binder None in
        let node = mk_cnode binder in
        binder.occ <- Some node;
        LetVal (binder, Map1 (tc, f, v), k (Var node))))

    | Map2 (tc, f, v1, v2) ->
      to_anf f (fun f -> to_anf v1 (fun v1 -> to_anf v2 (fun v2 ->
        let binder = mk_binder None in
        let node = mk_cnode binder in
        binder.occ <- Some node;
        LetVal (binder, Map2 (tc, f, v1, v2), k (Var node)))))

(* beyond this point it's just some gnode visualization code *)

let rec dump = function
  | Int v -> Z.output stdout v
  | Str v -> Printf.printf "%S" v
  | Vec vs ->
    print_string "(Vec";
    List.iter (fun q -> print_char ' '; dump q) vs;
    print_char ')'
  | Var v ->
    let v = find_root_binder v.data in
    print_string (Option.value ~default:"??" v.name)
  | Insert (v, i, e) ->
    print_string "(Insert ";
    dump v;
    Printf.printf " %d " i;
    dump e;
    print_char ')'
  | PrimBop (bop, p, q) ->
    print_char '(';
    dump p;
    print_string (match bop with
      | Add -> " + "
      | Sub -> " - ");
    dump q;
    print_char ')'
  | Map1 (tc, appf, v) ->
    print_string "(map1/";
    print_int (Option.value ~default:~-1 tc);
    print_char ' ';
    dump appf;
    print_char ' ';
    dump v;
    print_char ')'
  | Map2 (tc, appf, v1, v2) ->
    print_string "(map2/";
    print_int (Option.value ~default:~-1 tc);
    print_char ' ';
    dump appf;
    print_char ' ';
    dump v1;
    print_char ' ';
    dump v2;
    print_char ')'
  | Lam (v, n) ->
    let v = find_root_binder v in
    print_string "(\\";
    print_string (Option.value ~default:"??" v.name);
    print_string " -> ";
    dump n;
    print_char ')'
  | LetVal (v, i, e) ->
    let v = find_root_binder v in
    print_string "(let ";
    print_string (Option.value ~default:"??" v.name);
    print_string " = ";
    dump i;
    print_string " in ";
    dump e;
    print_char ')'
