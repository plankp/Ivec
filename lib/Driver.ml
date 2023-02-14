module I = Parser.MenhirInterpreter

let read_stdin () =
  let rec loop unwinder acc prefix =
    print_char prefix;
    print_string "> ";
    flush stdout;

    (* always at least lex until end-of-line.
     * also count balanced parenthesis to see if need to more lines.
     * stop trying if parenthesis becomes unbalanced *)
    let line = input_line stdin in
    let lexbuf = Lexing.from_string line in
    let rec gobble unwinder acc =
      try
        let tok = Lexer.read lexbuf in
        match (tok, unwinder) with
          (* EOF handling *)
          | (EOF, Some (ch :: _)) ->
            (* we need more lines. EOF is dropped *)
            loop unwinder acc ch
          | (EOF, _) ->
            (* we're done. need to fix the token ordering *)
            Ok (List.rev_append acc [tok])

          (* balanced parenthesis handling *)
          | (LPAREN, Some s) ->
            gobble (Some ('(' :: s)) (tok :: acc)
          | (RPAREN, Some (ch :: s)) ->
            gobble (if ch = '(' then Some s else None) (tok :: acc)

          (* generic token handling *)
          | _ -> gobble unwinder (tok :: acc)
      with Lexer.Error msg -> Error msg in
    gobble unwinder acc in
  loop (Some []) [] '>'

let parse rule toks =
  let rec loop toks (checkpoint : 'a I.checkpoint) =
    match checkpoint with
      | I.Accepted v -> Ok v
      | I.Rejected -> assert false (* since we don't recover from error *)
      | I.HandlingError _ -> Error "parsing error"
      | I.Shifting _
      | I.AboutToReduce _ ->
        let checkpoint = I.resume checkpoint in
        loop toks checkpoint
      | I.InputNeeded _ ->
        match toks with
          | [] -> assert false (* shouldn't happen unless EOF got lost *)
          | t :: toks ->
            let checkpoint = I.offer checkpoint (t, Lexing.dummy_pos, Lexing.dummy_pos) in
            loop toks checkpoint in
  loop toks (rule Lexing.dummy_pos)
