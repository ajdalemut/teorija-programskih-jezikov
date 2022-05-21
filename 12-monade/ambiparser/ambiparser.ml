let read_source filename =
  let channel = open_in filename in
  let source = really_input_string channel (in_channel_length channel) in
  close_in channel;
  source

let main () =
  if Array.length Sys.argv <> 2 then
    failwith ("Run AMBIPARSER as '" ^ Sys.argv.(0) ^ " <filename>.amb'")
  else
    let filename = Sys.argv.(1) in
    let source = read_source filename in
    let es = Parser.parse source in
    List.iter (fun e -> print_endline (Syntax.string_of_exp e)) es

let _ = main ()
