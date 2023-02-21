let ( let< ) = Result.bind

let () =
  let process_line () =
    let< v = Ivec.Driver.read_stdin () in
    let< v = Ivec.Driver.parse Ivec.Parser.Incremental.prog v in
    match v with
      | None -> Ok None
      | Some v ->
        let< (g, t) = Ivec.Gir.check Ivec.Gir.init_checkstate v in
        t |> Ivec.Gir.to_string |> print_endline;
        Ivec.Gir.dump g; print_endline "";

        let g = Ivec.Gir.opt_ds g in
        Ivec.Gir.dump g; print_endline "";

        let g = Ivec.Gir.to_anf g (fun x -> x) in
        Ivec.Gir.dump g; print_endline "";

        let g = Ivec.Gir.opt_anf g in
        Ivec.Gir.dump g; print_endline "";

        let ibuf = Ivec.Bcode.compile Ivec.Bcode.init_cgstate g in
        let< v = Ivec.Bcode.eval ibuf Ivec.Bcode.init_evalstate in
        Ok (Some v) in
  let rec loop () =
    try
      let () = match process_line () with
        | Ok None -> ()
        | Ok (Some v) -> v |> Ivec.Bcode.to_string |> print_endline
        | Error e -> print_endline e in
      loop ()
    with End_of_file -> () in
  loop ()
