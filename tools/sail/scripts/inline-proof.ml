(* Expand an Arm proof driver's loads for native compilation, as HOL
   Light's inline_load.ml does, but leave out the load of BASE:
   check-proof.sh links BASE, compiled once by inline_load.ml, as the
   module Arm_common_base, whose initialization runs before the driver's
   code. The files that BASE loads are not marked as loaded here, so
   "needs" of one of them in the driver would run it a second time. *)
#load "unix.cma";;
#use "hol_loader.ml";;

let base, input, output =
  match Sys.argv with
  | [|_; base; input; output|] -> Unix.realpath base, input, output
  | _ -> prerr_endline "inline-proof.ml BASE INPUT OUTPUT"; exit 2;;

let read_lines filename =
  let channel = open_in filename in
  let rec loop lines =
    match input_line channel with
    | line -> loop(line::lines)
    | exception End_of_file -> close_in channel; List.rev lines in
  loop [];;

let parse_directive name line =
  let line = String.trim line in
  if not(String.starts_with ~prefix:name line) then None else
  let rest = String.trim(String.sub line (String.length name)
    (String.length line - String.length name)) in
  if rest = "" || rest.[0] <> '"' then None else
  try
    let finish = String.index_from rest 1 '"' in
    let path = String.sub rest 1 (finish - 1) in
    let suffix = String.trim(String.sub rest (finish + 1)
      (String.length rest - finish - 1)) in
    if not(String.starts_with ~prefix:";;" suffix) then None else
    Some(path,String.sub suffix 2 (String.length suffix - 2))
  with Not_found -> None;;

let channel = open_out output;;
Printf.fprintf channel "open Hol_lib;;\nopen Hol_loader;;\nopen Arm_common_base;;\n";;

file_loader := (fun filename ->
  let filename = Unix.realpath filename in
  if filename = base then true else begin
    let print_line number =
      Printf.fprintf channel "#%d %S\n" number filename in
    print_line 1;
    List.iteri (fun index line ->
      let rec directive = function
        | [] -> Printf.fprintf channel "%s\n" line
        | (name,loader)::rest ->
            match parse_directive name line with
            | None -> directive rest
            | Some(path,suffix) ->
                if name = "loads" && path = "update_database.ml" then ()
                else loader path;
                print_line(index + 1);
                Printf.fprintf channel "%s\n" suffix;
                print_line(index + 2) in
      directive["loadt",loadt;"loads",loads;"needs",needs])
      (read_lines filename);
    let digest = Digest.file filename in
    Printf.fprintf channel "loaded_files := (%S,%S)::!loaded_files;;\n"
      (Filename.basename filename) digest;
    true
  end);;

loadt input;;
close_out channel;;
