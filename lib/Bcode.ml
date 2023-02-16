type bcode =
  | LdInt of Z.t                  (* -> v *)
  | LdStr of string               (* -> v *)
  | LdVec of int                  (* v1 ... vn -> (v1 ... vn) *)
  | LdLam of int * bcode Array.t  (* -> <fun> *)
  | LdVar of int                  (* -> s; s <- env[i] *)
  | StVar of int                  (* v ->; env[i] <- v *)
  | Dup                           (* v0 -> v0 v0 *)
  | DupX1                         (* v1 v0 -> v0 v1 v0 *)
  | DupX2                         (* v2 v1 v0 -> v0 v2 v1 v0 *)
  | IAdd                          (* v1 v2 -> v1 + v2 *)
  | ISub                          (* v1 v2 -> v1 - v2 *)
  | VCpy                          (* (v1 ... vn) -> (v1 ... vn) *)
  | VMp1                          (* dv <f> ->; mut-map <f> dv *)
  | VMp2                          (* dv <f> sv ->; mut-map2 <f> dv sv *)

type cgstate = {
  scope : (Gir.binder * int) list;
  index : int;
}

let init_cgstate : cgstate = {
  scope = [];
  index = 0;
}

type cgbuf = {
  buf : bcode list;
  len : int;
}

let init_cgbuf : cgbuf = {
  buf = [];
  len = 0;
}

let add_instr instr cgs = {
  buf = instr :: cgs.buf;
  len = cgs.len + 1;
}

let rec compile' s node cgs =
  let should_copy = function
    | Gir.Var _ -> true
    | _ -> false in

  match node with
    | Gir.Lam (v, n) ->
      (* fake closures: we shallow-copy the whole environment *)
      let index = s.index in
      let s = {
        scope = (Gir.find_root_binder v, s.index) :: s.scope;
        index = s.index + 1 } in
      add_instr (LdLam (index, compile s n)) cgs

    | Gir.Int v -> add_instr (LdInt v) cgs
    | Gir.Str v -> add_instr (LdStr v) cgs
    | Gir.Vec v ->
      let (cgs, n) = List.fold_left
        (fun (cgs, n) e -> (compile' s e cgs, n + 1)) (cgs, 0) v in
      add_instr (LdVec n) cgs
    | Gir.Var v ->
      let v = List.assq (Gir.find_root_binder v.data) s.scope in
      add_instr (LdVar v) cgs
    | Gir.LetVal (v, i, e) ->
      let cgs = compile' s i cgs in
      let cgs = add_instr (StVar s.index) cgs in
      let s = {
        scope = (Gir.find_root_binder v, s.index) :: s.scope;
        index = s.index + 1 } in
      compile' s e cgs
    | Gir.PrimBop (Add, p, q) ->
      cgs |> compile' s p |> compile' s q |> add_instr IAdd
    | Gir.PrimBop (Sub, p, q) ->
      cgs |> compile' s p |> compile' s q |> add_instr ISub

    | Gir.Map1 (_, f, v) ->
      (* discard the trip count hint for now *)
      let cgs = compile' s v cgs in
      let cgs = if should_copy v then add_instr VCpy cgs else cgs in
      (* return v on stack before mapping *)
      cgs |> add_instr Dup
          |> compile' s f |> add_instr VMp1

    | Gir.Map2 (_, f, v1, v2) ->
      (* discard the trip count hint for now *)
      let cgs = compile' s v1 cgs in
      let cgs = if should_copy v1 then add_instr VCpy cgs else cgs in
      (* return v1 on stack before mapping *)
      cgs |> add_instr Dup
          |> compile' s f |> compile' s v2 |> add_instr VMp2

    | _ -> failwith "TODO compile"

and compile s e =
  let cgs = compile' s e init_cgbuf in
  cgs.buf |> List.rev |> Array.of_list

module M = Map.Make (Int)

type v =
  | Lam of v M.t * int * bcode Array.t
  | Str of string
  | Int of Z.t
  | Vec of v Array.t

let rec to_buffer buf = function
  | Lam _ -> Buffer.add_string buf "<fun>"
  | Str s -> Buffer.add_string buf s
  | Int v -> Z.bprint buf v
  | Vec v ->
    Buffer.add_char buf '(';
    Array.iteri (fun i e ->
      if i <> 0 then Buffer.add_char buf ' ';
      to_buffer buf e) v;
    Buffer.add_char buf ')'

let to_string = function
  | Lam _ -> "<fun>"
  | Str s -> s
  | Int v -> Z.to_string v
  | v ->
    let buf = Buffer.create 16 in
    to_buffer buf v;
    Buffer.contents buf

type evalstate = {
  ip : int;
  env : v M.t;
  stack : v list;
}

let init_evalstate : evalstate = {
  ip = 0;
  env = M.empty;
  stack = [];
}

let ( let< ) = Result.bind

let pop_stack s =
  match s.stack with
    | x :: stack -> Ok (x, { s with stack })
    | _ -> Error "VALUE STACK IS EMPTY"

let rec eval ibuf s =
  if s.ip >= Array.length ibuf then
    (* return the top-of-stack *)
    pop_stack s |> Result.map fst
  else
    let imath op s =
      let< (r, s) = pop_stack s in
      let< (l, s) = pop_stack s in
      match l, r with
        | Int l, Int r ->
          eval ibuf { s with ip = s.ip + 1; stack = Int (op l r):: s.stack }
        | _ -> Error "Type mismatch" in

    match ibuf.(s.ip) with
    (* simple load store operations *)
      | StVar v ->
        let< (x, s) = pop_stack s in
        eval ibuf { s with ip = s.ip + 1; env = M.add v x s.env }
      | LdVar v ->
        eval ibuf { s with ip = s.ip + 1; stack = M.find v s.env :: s.stack }
      | LdInt v ->
        eval ibuf { s with ip = s.ip + 1; stack = Int v :: s.stack }
      | LdStr v ->
        eval ibuf { s with ip = s.ip + 1; stack = Str v :: s.stack }
      | LdLam (i, v) ->
        eval ibuf {
          s with ip = s.ip + 1; stack = Lam (s.env, i, v) :: s.stack }
      | LdVec q -> begin
        let v = Array.make q (Int Z.zero) in
        let rec loop s = function
          | 0 -> eval ibuf { s with ip = s.ip + 1; stack = Vec v :: s.stack }
          | i ->
            let< (x, s) = pop_stack s in
            v.(i - 1) <- x;
            loop s (i - 1) in
        loop s q
      end

    (* stack manipulation operations *)
      | Dup ->
        let< (t0, s) = pop_stack s in
        eval ibuf { s with ip = s.ip + 1;
          stack = t0 :: t0 :: s.stack }
      | DupX1 ->
        let< (t0, s) = pop_stack s in
        let< (t1, s) = pop_stack s in
        eval ibuf { s with ip = s.ip + 1;
          stack = t0 :: t1 :: t0 :: s.stack }
      | DupX2 ->
        let< (t0, s) = pop_stack s in
        let< (t1, s) = pop_stack s in
        let< (t2, s) = pop_stack s in
        eval ibuf { s with ip = s.ip + 1;
          stack = t0 :: t2 :: t1 :: t0 :: s.stack }

    (* primitives *)
      | IAdd -> imath Z.add s
      | ISub -> imath Z.sub s
      | VCpy -> begin
        let< (v, s) = pop_stack s in
        match v with
          | Vec v ->
            eval ibuf {
              s with ip = s.ip + 1; stack = Vec (Array.copy v) :: s.stack }
          | _ -> Error "Type mismatch"
      end
      | VMp1 -> begin
        let< (f, s) = pop_stack s in
        let< (v, s) = pop_stack s in
        match f, v with
          | Lam (lenv, larg, lbuf), Vec v ->
            let rec loop = function
              | 0 -> eval ibuf { s with ip = s.ip + 1 }
              | n ->
                let i = n - 1 in
                let< r = eval lbuf {
                  ip = 0; env = M.add larg v.(i) lenv; stack = [] } in
                v.(i) <- r;
                loop i in
            loop (Array.length v)
          | _ -> Error "Type mismatch"
      end
      | VMp2 -> begin
        let< (v2, s) = pop_stack s in
        let< (f, s) = pop_stack s in
        let< (v1, s) = pop_stack s in
        match f, v1, v2 with
          | Lam (lenv, larg, lbuf), Vec v1, Vec v2 ->
            let rec loop = function
              | 0 -> eval ibuf { s with ip = s.ip + 1 }
              | n ->
                let i = n - 1 in
                let< r = eval lbuf {
                  ip = 0; env = M.add larg v1.(i) lenv; stack = [] } in
                match r with
                  | Lam (lenv, larg, lbuf) ->
                    let< r = eval lbuf {
                      ip = 0; env = M.add larg v2.(i) lenv; stack = [] } in
                    v1.(i) <- r;
                    loop i
                  | _ -> Error "Type mismatch" in
            let tc = Array.length v1 in
            if tc = Array.length v2 then loop tc
            else Error "Map2 vector shape mismatch"
          | _ -> Error "Type mismatch"
      end
