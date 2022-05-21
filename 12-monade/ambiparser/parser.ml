let explode str = List.init (String.length str) (String.get str)
let implode chrs = String.init (List.length chrs) (List.nth chrs)

(* BASIC PARSERS *)

type 'value parser = int -> char list -> ('value * char list) list

let fail _ _ = []
let return v _ chrs = [ (v, chrs) ]
let character _ = function [] -> [] | chr :: chrs -> [ (chr, chrs) ]

let ( || ) parser1 parser2 n chrs =
  if n > 0 then parser1 (n - 1) chrs @ parser2 (n - 1) chrs else []

let ( >>= ) (parser1 : 'a parser) (parser2 : 'a -> 'b parser) : 'b parser =
 fun n chrs ->
  if n > 0 then
    List.concat_map (fun (v, chrs') -> parser2 v n chrs') (parser1 (n - 1) chrs)
  else []

(* DERIVED PARSERS *)

let ( >> ) parser1 parser2 = parser1 >>= fun _ -> parser2

let satisfy cond parser =
  let cond_parser v = if cond v then return v else fail in
  parser >>= cond_parser

let digit =
  let is_digit = String.contains "0123456789" in
  character |> satisfy is_digit

let alpha =
  let is_alpha = String.contains "_abcdefghijklmnopqrstvwuxyz" in
  character |> satisfy is_alpha

let space =
  let is_space = String.contains " \n\t\r" in
  character |> satisfy is_space

let exactly chr = character |> satisfy (( = ) chr)
let one_of parsers = List.fold_right ( || ) parsers fail

let word str =
  let chrs = explode str in
  List.fold_right (fun chr parser -> exactly chr >> parser) chrs (return ())

let rec many parser = many1 parser || return []

and many1 parser =
  parser >>= fun v ->
  many parser >>= fun vs -> return (v :: vs)

let integer =
  many1 digit >>= fun digits -> return (int_of_string (implode digits))

let spaces = many space >> return ()
let spaces1 = many1 space >> return ()

let parens parser =
  word "(" >> spaces >> parser >>= fun p -> spaces >> word ")" >> return p

let binop parser1 op parser2 f =
  parser1 >>= fun v1 ->
  spaces >> word op >> spaces >> parser2 >>= fun v2 -> return (f v1 v2)

(* LAMBDA PARSERS *)

let ident =
  alpha >>= fun chr ->
  many (alpha || digit || exactly '\'') >>= fun chrs ->
  return (Syntax.Ident (implode (chr :: chrs)))

let rec exp2 chrs =
  one_of
    [
      binop exp2 "+" exp2 (fun e1 e2 -> Syntax.Plus (e1, e2));
      binop exp2 "-" exp2 (fun e1 e2 -> Syntax.Minus (e1, e2));
      exp1;
    ]
    chrs

and exp1 chrs =
  one_of
    [
      binop exp1 "*" exp1 (fun e1 e2 -> Syntax.Times (e1, e2));
      binop exp1 "/" exp1 (fun e1 e2 -> Syntax.Plus (e1, e2));
      exp0;
    ]
    chrs

and exp0 chrs =
  one_of [ (integer >>= fun n -> return (Syntax.Int n)); parens exp2 ] chrs

let parse str =
  str |> String.trim |> explode |> exp2 20
  |> List.filter_map (function v, [] -> Some v | _, _ :: _ -> None)
