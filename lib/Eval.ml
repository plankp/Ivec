type v =
  | Str of string
  | Int of Z.t
  | Seq of v list

type s = unit

let rec to_buffer buf = function
  | Str s -> Buffer.add_string buf s
  | Int v -> Z.bprint buf v
  | Seq [] -> Buffer.add_string buf "[]"
  | Seq [x] ->
    Buffer.add_char buf '[';
    to_buffer buf x;
    Buffer.add_char buf ']'
  | Seq (x :: xs) ->
    Buffer.add_char buf '[';
    to_buffer buf x;
    List.iter (fun v -> Buffer.add_char buf ' '; to_buffer buf v) xs;
    Buffer.add_char buf ']'

let to_string = function
  | Str s -> s
  | Int v -> Z.to_string v
  | Seq [] -> "[]"
  | v ->
    let buf = Buffer.create 16 in
    to_buffer buf v;
    Buffer.contents buf

let init_state : s = ()

let ( let< ) = Result.bind

let broadcast_numeric f l r =
  let rec helper = function
    | Int l, Int r -> Int (f l r)
    | Seq l, Seq r -> Seq (List.map2 (fun l r -> helper (l, r)) l r)
    | l, Seq r -> Seq (List.map (fun r -> helper (l, r)) r)
    | Seq l, r -> Seq (List.map (fun l -> helper (l, r)) l)
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
      | [] -> Ok (Seq (List.rev acc))
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
