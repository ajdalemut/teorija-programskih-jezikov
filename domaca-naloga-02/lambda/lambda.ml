let read_source filename =
  let channel = open_in filename in
  let source = really_input_string channel (in_channel_length channel) in
  close_in channel; source


let main () =
  if Array.length Sys.argv <> 3 || (Sys.argv.(1) <> "eager" && Sys.argv.(1) <> "lazy")
  then failwith ("Run LAMBDA as '" ^ Sys.argv.(0) ^ " eager <filename>.lam' or '" ^ Sys.argv.(0) ^ " lazy <filename>.lam' ")
  else
    let eager = Sys.argv.(1) = "eager" in
    let filename = Sys.argv.(2) in
    let source = read_source filename in
    let e = Parser.parse source in
    print_endline "MALI KORAKI:";
    (if eager then Eval.small_step e else LazyEval.small_step e);
    print_endline "VELIKI KORAKI:";
    (if eager then Eval.big_step e else LazyEval.big_step e)

let _ = main ()
