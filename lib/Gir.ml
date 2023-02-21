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

let lnode_link (h1 : 'a cnode) (h2 : 'a cnode) =
  let t1 = h1.prev in
  let t2 = h2.prev in

  h1.prev <- t2;
  h2.prev <- t1;
  t1.next <- h2;
  t2.next <- h1

let lnode_unlink (node : 'a cnode) =
  node.prev.next <- node.next;
  node.next.prev <- node.prev;

  node.prev <- node;
  node.next <- node

let lnode_count (node : 'a cnode) =
  let rec loop sz curp =
    if curp == node then sz else loop (sz + 1) curp.next in
  loop 1 node.next

(* here we encode a data type to represent the graph intermediate
 * representation, which is inspired by the "Compiling with Continuations,
 * Continued" paper.
 *
 * type gnode encodes all possible expressions (including values) and
 * more-or-less allows representing direct style terms!
 *
 * type binder holds part of the magic used to name intermediate computations.
 * following the paper, it is a node in a union-find structure that either
 * points to another binder or information about how the binder is introduced
 * (e.g. it's a let binding, lambda, whatever). if the binder will also point
 * to one of its free occurrence (provided there is at least one).
 *
 * each free occurrence points to the corresponding binder (chain) and is a circular
 * (doubly) linked list with the other free occurrences. *)

type gnode =
  | Binder of binder * gnode  (* must hold a well-behaved root binder *)
  | Var of binder cnode
  | Int of Z.t
  | Str of string
  | Vec of gnode list
  | PrimBop of prim_bop * gnode * gnode
  | Insert of gnode * int * gnode
  | Apply of gnode * gnode
(* mapk : trip count * appf * v1 * ... * vk *)
  | Map1 of int option * gnode * gnode
  | Map2 of int option * gnode * gnode * gnode

and prim_bop =
  | Add
  | Sub

and bndr_ctx =
(* a CtxChain is either a link to another binder / union-find node or a
 * undefined root binder (if it is a self-loop). *)
  | CtxChain of binder
(* otherwise, a binder is considered a well-behaved root binder *)
  | CtxLam
  | CtxLet of gnode

and binder = {
  name : string option;
  mutable occ : binder cnode option;
  mutable ctx : bndr_ctx;
}

let rec find_root_binder (b : binder) =
  match b.ctx with
    | CtxChain chain when chain != b ->
      (* it's not the root; do path compression *)
      let root = find_root_binder chain in
      (* always hold a ptr to the root for sanity reasons *)
      b.ctx <- CtxChain root;
      root
    | _ -> b

let dummy = ref 0
let mk_binder (name : string option) : binder =
  let name = if name <> None then name else begin
    dummy := !dummy + 1;
    Some ("$" ^ (string_of_int !dummy))
  end in
  let rec node = { name; occ = None; ctx = CtxChain node } in node

let mk_free_occ (b : binder) : gnode =
  let b = find_root_binder b in
  let node = mk_cnode b in
  (* make sure the new node is added to the occurrence list *)
  let () = match b.occ with
    | None -> b.occ <- Some node
    | Some occ -> lnode_link occ node in
  Var node

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
    let node = mk_free_occ binder in

    let lhs = if flip then (node, eltTy) else (scl, sclTy) in
    let rhs = if flip then (scl, sclTy) else (node, eltTy) in
    let< (body, ty) = try_numeric_broadcast op lhs rhs in
    binder.ctx <- CtxLam;
    Ok (Map1 (trip, Binder (binder, body), vec), TVec (ty, trip)) in

  let emit_map2 v1 eltTy1 v2 eltTy2 trip =
    (* map2 feeds two values, so we need two binders *)
    let lhsBinder = mk_binder None in
    let rhsBinder = mk_binder None in
    let lhsNode = mk_free_occ lhsBinder in
    let rhsNode = mk_free_occ rhsBinder in

    let< (body, ty) = try_numeric_broadcast
      op (lhsNode, eltTy1) (rhsNode, eltTy2) in
    lhsBinder.ctx <- CtxLam;
    rhsBinder.ctx <- CtxLam;
    Ok (Map2 (trip, Binder (lhsBinder, (Binder (rhsBinder, body))), v1, v2),
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

module M = Map.Make (String)

type checkstate = (binder * t) M.t

let init_checkstate : checkstate =
  M.empty

let rec check s = function
  | Ast.EVar v -> begin
    match M.find_opt v s with
      | None -> Error ("Binding " ^ v ^ " has not been defined")
      | Some (binder, t) -> Ok (mk_free_occ binder, t)
  end
  | Ast.ELet (v, i, e) -> begin
    let< (i, ity) = check s i in
    let binder = mk_binder (Some v) in
    let< (e, ety) = check (M.add v (binder, ity) s) e in
    binder.ctx <- CtxLet i;
    Ok (Binder (binder, e), ety)
  end

  | Ast.EStr v -> Ok (Str v, TStr)
  | Ast.EInt v -> Ok (Int v, TInt)
  | Ast.ESeq [] -> Ok (Vec [], TVec (TAny, Some 0))
  | Ast.ESeq (v :: vs) -> begin
    let rec loop acc k ty = function
      | [] -> Ok (Vec (List.rev acc), TVec (ty, Some k))
      | v :: vs ->
        let< (v, rty) = check s v in
        loop (v :: acc) (k + 1) (unify ty rty) vs in
    let< (v, ty) = check s v in
    loop [v] 1 ty vs
  end
  | Ast.EAdd (p, q) -> begin
    let< lhs = check s p in
    let< rhs = check s q in
    match try_numeric_broadcast (fun p q -> PrimBop (Add, p, q)) lhs rhs with
      | Ok _ as v -> v
      | Error (p, q) ->
        Error ("Unsupported " ^ (to_string p) ^ " + " ^ (to_string q))
  end
  | Ast.ESub (p, q) -> begin
    let< lhs = check s p in
    let< rhs = check s q in
    match try_numeric_broadcast (fun p q -> PrimBop (Sub, p, q)) lhs rhs with
      | Ok _ as v -> v
      | Error (p, q) ->
        Error ("Unsupported " ^ (to_string p) ^ " - " ^ (to_string q))
  end

let rec to_anf e k =
  match e with
    (* simple values are consumed directly *)
    | Var _ | Int _ | Str _ -> k e

    | Binder (bndr, e) -> begin
      match bndr.ctx with
        | CtxChain _ -> failwith "IMPOSSIBLE BINDER STATE FOUND"
        | CtxLam ->
          (* lambdas start a whole new continuation context *)
          (* to simplify optimization passes, treat lambdas as complex *)
          let binder = mk_binder None in
          let node = mk_free_occ binder in
          binder.ctx <- CtxLet (Binder (bndr, to_anf e (fun x -> x)));
          (Binder (binder, k node))
        | CtxLet i ->
          (* letval just needs to make sure the initializer is simple *)
          to_anf i (fun i -> bndr.ctx <- CtxLet i; Binder (bndr, to_anf e k))
    end

    (* we treat vectors as complex values to avoid nested vectors. this avoids
     * deep recursive calls when inlining *)
    | Vec xs ->
      let rec loop acc = function
        | x :: xs -> to_anf x (fun x -> loop (x :: acc) xs)
        | [] ->
          let binder = mk_binder None in
          let node = mk_free_occ binder in
          binder.ctx <- CtxLet (Vec (List.rev acc));
          (Binder (binder, k node)) in
      loop [] xs

    | PrimBop (bop, p, q) ->
      to_anf p (fun p -> to_anf q (fun q ->
        let binder = mk_binder None in
        let node = mk_free_occ binder in
        binder.ctx <- CtxLet (PrimBop (bop, p, q));
        Binder (binder, k node)))

    | Insert (v, i, e) ->
      to_anf v (fun v -> to_anf e (fun e ->
        let binder = mk_binder None in
        let node = mk_free_occ binder in
        binder.ctx <- CtxLet (Insert (v, i, e));
        Binder (binder, k node)))

    | Apply (p, q) ->
      to_anf p (fun p -> to_anf q (fun q ->
        let binder = mk_binder None in
        let node = mk_free_occ binder in
        binder.ctx <- CtxLet (Apply (p, q));
        Binder (binder, k node)))

    | Map1 (tc, f, v) ->
      to_anf f (fun f -> to_anf v (fun v ->
        let binder = mk_binder None in
        let node = mk_free_occ binder in
        binder.ctx <- CtxLet (Map1 (tc, f, v));
        Binder (binder, k node)))

    | Map2 (tc, f, v1, v2) ->
      to_anf f (fun f -> to_anf v1 (fun v1 -> to_anf v2 (fun v2 ->
        let binder = mk_binder None in
        let node = mk_free_occ binder in
        binder.ctx <- CtxLet (Map2 (tc, f, v1, v2));
        Binder (binder, k node))))

let rec drop' = function
  | [] -> ()
  | Var n :: xs -> begin
    let binder = find_root_binder n.data in
    let () = match binder.occ with
      | Some r when r == n ->
        if lnode_is_singleton n then
          (* this was the last occurrence, so once dropped, binder will
            * have no more occurrences left / None *)
          binder.occ <- None
        else
          (* update the binder to point to another free occurrence *)
          binder.occ <- Some n.prev
      | _ -> () in
    (* then we drop this node *)
    lnode_unlink n;
    (* and continue dropping remaining nodes *)
    drop' xs
  end

  | Binder (bndr, e) :: xs -> begin
    match bndr.ctx with
      | CtxChain _ -> failwith "IMPOSSIBLE BINDER STATE FOUND"
      | CtxLam -> drop' (e :: xs)
      | CtxLet i -> drop' (i :: e :: xs)
  end

  | (Int _ | Str _) :: xs -> drop' xs
  | Vec ys :: xs -> drop' ys; drop' xs
  | PrimBop (_, x, y) :: xs -> drop' (x :: y :: xs)
  | Insert (v, _, e) :: xs -> drop' (v :: e :: xs)
  | Apply (p, q) :: xs -> drop' (p :: q :: xs)
  | Map1 (_, f, v) :: xs -> drop' (f :: v :: xs)
  | Map2 (_, f, v1, v2) :: xs -> drop' (f :: v1 :: v2 :: xs)

and drop gnode = drop' [gnode]

(* copy is scope aware *)
let rec copy s = function
  | Binder ({ ctx = CtxChain _; _ }, _) ->
    failwith "IMPOSSIBLE BINDER STATE FOUND"
  | Binder ({ ctx = CtxLam; name; _ } as prev, e) ->
    let next = { ctx = CtxLam; name; occ = None } in
    Binder (next, copy ((prev, next) :: s) e)
  | Binder ({ ctx = CtxLet i; name; _ } as prev, e) ->
    let next = { ctx = CtxLet (copy s i); name; occ = None } in
    Binder (next, copy ((prev, next) :: s) e)
  | Var n -> begin
    let root = find_root_binder n.data in
    (* if it's in scope, then the binder is being copied, so it should be an
     * occurrence of the newly copied binder *)
    s |> List.assq_opt root         (* find the remapped binder *)
    (* if not, then it means the binder was not being copied, so it should
     * refer to the original binder *)
      |> Option.value ~default:root
    (* once we located the binder, create a new free occurrence of it *)
      |> mk_free_occ
  end
  | Int _ | Str _ | Vec [] as v -> v
  | Vec xs -> Vec (List.map (copy s) xs)
  | PrimBop (op, l, r) -> PrimBop (op, copy s l, copy s r)
  | Insert (v, i, e) -> Insert (copy s v, i, copy s e)
  | Apply (p, q) -> Apply (copy s p, copy s q)
  | Map1 (tc, f, v) -> Map1 (tc, copy s f, copy s v)
  | Map2 (tc, f, v1, v2) -> Map2 (tc, copy s f, copy s v1, copy s v2)

let get_value = function
  | Var n as v -> begin
    let binder = find_root_binder n.data in
    match binder.ctx with
      | CtxLet v -> v
      | _ -> v
  end
  | v -> v

let rec redux_ds modified = function
  | Binder ({ ctx = CtxChain _; _ }, _) ->
    failwith "IMPOSSIBLE BINDER STATE FOUND"
  | Binder ({ ctx = CtxLam; _ } as bndr, e) ->
    let (e, modified) = redux_ds modified e in
    (Binder (bndr, e), modified)
  | Binder ({ ctx = CtxLet i; occ = None; _ }, e) ->
    drop i; redux_ds true e
  | Binder ({ ctx = CtxLet (Var n as node); _ } as bndr, e) -> begin
    (* merge the binders *)
    bndr.ctx <- CtxChain (find_root_binder n.data);
    (* update the occurrence list *)
    lnode_link n (Option.get bndr.occ);
    drop node;
    (* and then optimize the rhs *)
    redux_ds true e
  end
  | Binder ({ ctx = CtxLet i; _ } as bndr, e) -> begin
    let (i, modified) = redux_ds modified i in
    bndr.ctx <- CtxLet i;
    let (e, modified) = redux_ds modified e in
    match bndr.occ with
      | None -> drop i; (e, true)
      | _ -> (Binder (bndr, e), modified)
  end
  | Map1 (tc1, f1, Map1 (tc2, f2, v)) -> begin
    (* map / loop fusion *)
    let tc = match tc1, tc2 with None, v | v, _ -> v in
    let f = mk_binder None in
    f.ctx <- CtxLam;
    let e = Apply (f1, Apply (f2, mk_free_occ f)) in
    let e = Map1 (tc, Binder (f, e), v) in
    redux_ds true e
  end
  | Map1 (_, Binder ({ ctx = CtxLam; _ } as bndr, Var v), t)
    when find_root_binder v.data == bndr ->
    redux_ds true t
  | Map1 (tc, f, v) ->
    let (f, modified) = redux_ds modified f in
    let (v, modified) = redux_ds modified v in
    (Map1 (tc, f, v), modified)
  | Map2 (tc, f1, v1, v2) -> begin
    (* we may conditionally rewrite this into a map1 *)
    let unpack_mapped_vec1 = function
      | Var v -> Some (v, fun v -> v)
      | Map1 (_, f, Var v) -> Some (v, fun v -> Apply (f, v))
      | _ -> None in
    match unpack_mapped_vec1 v1, unpack_mapped_vec1 v2 with
      | Some (v1, fl), Some (v2, fr)
        when find_root_binder v1.data == find_root_binder v2.data -> begin
        drop (Var v2);
        let f = mk_binder None in
        f.ctx <- CtxLam;

        let e = Apply (f1, f |> mk_free_occ |> fl) in
        let e = Apply (e, f |> mk_free_occ |> fr) in
        let e = Map1 (tc, Binder (f, e), Var v1) in
        redux_ds true e
      end
      | _ ->
        let (f1, modified) = redux_ds modified f1 in
        let (v1, modified) = redux_ds modified v1 in
        let (v2, modified) = redux_ds modified v2 in
        (Map2 (tc, f1, v1, v2), modified)
  end
  | Apply (Binder ({ ctx = CtxLam; _ } as bndr, e), v) -> begin
    (* beta reduction *)
    bndr.ctx <- CtxLet v;
    redux_ds true (Binder (bndr, e))
  end
  | Apply (f, v) ->
    let (f, modified) = redux_ds modified f in
    let (v, modified) = redux_ds modified v in
    (Apply (f, v), modified)
  | PrimBop (op, l, r) -> begin
    match op, get_value l, get_value r with
      | (Add | Sub), _, Int q when Z.zero = q ->
        drop r; redux_ds true l
      | Add, Int q, _ when Z.zero = q ->
        drop l; redux_ds true r
      | _ ->
        let (l, modified) = redux_ds modified l in
        let (r, modified) = redux_ds modified r in
        (PrimBop (op, l, r), modified)
  end
  | t -> (t, modified)

let rec opt_ds (t : gnode) =
  match redux_ds false t with
    | (t, true) -> opt_ds t
    | (t, _) -> t

let rec opt_anf = function
  | Binder ({ ctx = CtxChain _; _ }, _) ->
    failwith "IMPOSSIBLE BINDER STATE FOUND"
  | Binder ({ ctx = CtxLam; _ } as bndr, e) -> Binder (bndr, opt_anf e)
  | Binder ({ ctx = CtxLet i; occ = None; _ }, e) -> drop i; opt_anf e
  | Binder ({ ctx = CtxLet (Var n as node); _ } as bndr, e) -> begin
    (* merge the binders *)
    bndr.ctx <- CtxChain (find_root_binder n.data);
    (* update the occurrence list *)
    lnode_link n (Option.get bndr.occ);
    drop node;
    (* and then optimize the rhs *)
    opt_anf e
  end

  | Binder ({ ctx = CtxLet (Apply (Var f, q)); _ } as bndr, e) -> begin
    match get_value (Var f) with
      | Binder ({ ctx = CtxLam; name; _ } as prev, le) ->
        let next = { ctx = CtxLet (copy [] q); name; occ = None } in
        let i = Binder (next, copy [(prev, next)] le) in
        let e = to_anf i (fun i -> bndr.ctx <- CtxLet i; Binder (bndr, e)) in
        drop' [Var f; q];
        opt_anf e
      | _ -> Binder (bndr, opt_anf e)
  end

  | Binder ({ ctx = CtxLet (Map1 (_, q, Var v)); _ } as bndr, e)
    when lnode_is_singleton v -> begin
    match get_value (Var v) with
      | Vec xs ->
        let i = Vec (List.map (fun v -> Apply (copy [] q, copy [] v)) xs) in
        let e = to_anf i (fun i -> bndr.ctx <- CtxLet i; Binder (bndr, e)) in
        drop' [q; Var v];
        opt_anf e
      | _ -> Binder (bndr, opt_anf e)
  end

  | Binder ({ ctx = CtxLet (Map2 (_, q, Var v1, Var v2)); _ } as bndr, e)
    when lnode_is_singleton v1 && lnode_is_singleton v2 -> begin
    match get_value (Var v1), get_value (Var v2) with
      | Vec xs, Vec ys ->
        let i = Vec (List.map2 (fun x y ->
          Apply (Apply (copy [] q, copy [] x), copy [] y)) xs ys) in
        let e = to_anf i (fun i -> bndr.ctx <- CtxLet i; Binder (bndr, e)) in
        drop' [q; Var v1; Var v2];
        opt_anf e
      | _ -> Binder (bndr, opt_anf e)
  end

  | Binder ({ ctx = CtxLet i; _ } as bndr, e) -> begin
    let i = opt_anf i in
    bndr.ctx <- CtxLet i;
    let e = opt_anf e in
    match bndr.occ with
      | None -> drop i; e
      | _ -> Binder (bndr, e)
  end

  | Var _ as v -> begin
    (* we only inline super simple values *)
    match get_value v with
      | Int _ | Str _ as i -> drop v; i
      | _ -> v
  end

  | PrimBop (f, x, y) -> begin
    match f, opt_anf x, opt_anf y with
      | Add, Int l, Int r -> Int (Z.add l r)
      | Sub, Int l, Int r -> Int (Z.sub l r)
      | f, x, y -> PrimBop (f, x, y)
  end

  | Int _ | Str _ as v -> v
  | Vec xs -> Vec (List.map opt_anf xs)
  | Insert (v, i, e) -> Insert (opt_anf v, i, opt_anf e)
  | Apply (p, q) -> Apply (opt_anf p, opt_anf q)
  | Map1 (tc, f, v) -> Map1 (tc, opt_anf f, opt_anf v)
  | Map2 (tc, f, v1, v2) -> Map2 (tc, opt_anf f, opt_anf v1, opt_anf v2)

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
  | Apply (f, v) ->
    print_string "(apply ";
    dump f;
    print_char ' ';
    dump v;
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
  | Binder (bndr, e) ->
    match bndr.ctx with
      | CtxChain _ -> print_string "#MALFORMED BINDER#"
      | CtxLam ->
        print_string "(\\";
        print_string (Option.value ~default:"??" bndr.name);
        print_string " -> ";
        dump e;
        print_char ')'
      | CtxLet i ->
        print_string "(let ";
        print_string (Option.value ~default:"??" bndr.name);
        print_string " = ";
        dump i;
        print_string " in ";
        dump e;
        print_char ')'
