type v =
  | Str of string
  | Int of Z.t
  | Vec of v Array.t

let rec to_buffer buf = function
  | Str s -> Buffer.add_string buf s
  | Int v -> Z.bprint buf v
  | Vec v ->
    Buffer.add_char buf '(';
    Array.iteri (fun i e ->
      if i <> 0 then Buffer.add_char buf ' ';
      to_buffer buf e) v;
    Buffer.add_char buf ')'

let to_string = function
  | Str s -> s
  | Int v -> Z.to_string v
  | v ->
    let buf = Buffer.create 16 in
    to_buffer buf v;
    Buffer.contents buf

module M = Map.Make (String)

type s = v M.t

let init_state : s = M.empty

let ( let< ) = Result.bind

let broadcast_numeric f l r =
  let rec helper = function
    | Int l, Int r -> Int (f l r)
    | Vec l, Vec r -> Vec (Array.map2 (fun l r -> helper (l, r)) l r)
    | l, Vec r -> Vec (Array.map (fun r -> helper (l, r)) r)
    | Vec l, r -> Vec (Array.map (fun l -> helper (l, r)) l)
    | _ -> failwith "Type mismatch" in
  try
    Ok (helper (l, r))
  with
    | Failure e
    | Invalid_argument e -> Error e

let rec eval s = function
  | Ast.EStr v -> Ok (Str v)
  | Ast.EInt v -> Ok (Int v)
  | Ast.ESeq v -> begin
    let rec loop acc = function
      | [] -> Ok (Vec (acc |> List.rev |> Array.of_list))
      | x :: xs -> let< x = eval s x in loop (x :: acc) xs in
    loop [] v
  end
  | Ast.EAdd (p, q) -> begin
    let< p = eval s p in
    let< q = eval s q in
    broadcast_numeric Z.add p q
  end
  | Ast.ESub (p, q) -> begin
    let< p = eval s p in
    let< q = eval s q in
    broadcast_numeric Z.sub p q
  end
