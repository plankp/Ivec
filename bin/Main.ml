let ( let< ) = Result.bind

let () =
  let process_line state =
    let< v = Ivec.Driver.read_stdin () in
    let< v = Ivec.Driver.parse Ivec.Parser.Incremental.prog v in
    match v with
      | None -> Ok None
      | Some v ->
        let< v = Ivec.Eval.eval state v in
        Ok (Some v) in
  let rec loop state =
    try
      let () = match process_line state with
        | Ok None -> ()
        | Ok (Some v) -> v |> Ivec.Eval.to_string |> print_endline
        | Error e -> print_endline e in
      loop state
    with End_of_file -> () in
  loop Ivec.Eval.init_state
