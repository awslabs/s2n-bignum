(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0 *)

(* One hol-d session: a native HOL process that runs the supervisor's
   commands and forks children that inherit its state. Each node connects
   to the supervisor's node socket (HOL_D_NODES) for its control channel
   and once more per request for that request's output. *)

let flush_output () =
  Format.pp_print_flush Format.std_formatter ();
  Format.pp_print_flush Format.err_formatter ();
  flush_all ()

let execute print tree =
  (* A loadt/needs item can install bindings used by the next item. Type
     and execute in order, as in the interactive toplevel. *)
  List.for_all (fun item ->
    Toploop.execute_phrase print Format.std_formatter (Parsetree.Ptop_def [item])) tree

(* Camlp5 runs as a new process for each parse, so a HOL lexer switch such
   as unset_jrh_lexer lasts only until the end of its phrase or file. *)
let parse file = Pparse.parse_implementation ~tool_name:"hol-d" file

let eval_file print file =
  (* HOL's native inliner also omits the optional theorem-search index.
     update_database.ml depends on the bytecode toplevel's getvalue. *)
  try
    if Filename.basename file = "update_database.ml" &&
       Unix.realpath file = Unix.realpath (Filename.concat (Sys.getenv "HOLLIGHT_DIR") "update_database.ml")
    then (prerr_endline "hol-d: skipping HOL's bytecode theorem-search index"; true)
    else execute print (parse file)
  with exn -> Location.report_exception Format.err_formatter exn; false

let eval print text =
  let file, out = Filename.open_temp_file "hol-d-" ".ml" in
  try
    (* Unlink before running the tactic, which can be killed at any time. *)
    let tree = Fun.protect ~finally:(fun () -> close_out_noerr out; Sys.remove file)
      (fun () -> output_string out text; close_out out; parse file) in
    execute print tree
  with exn -> Location.report_exception Format.err_formatter exn; false

let initialize () =
  Clflags.native_code := true;
  Clflags.noinit := true;
  Clflags.include_dirs := [Sys.getenv "HOLLIGHT_DIR"; "+unix"];
  Clflags.preprocessor := Some (Sys.getenv "HOL_D_PP");
  (* Items nested in a loadt phrase refer to earlier toplevel units, which
     have no .cmx file. Warning 58 says so on every load. *)
  ignore (Warnings.parse_options false "-58");
  Toploop.set_paths ();
  (* set_paths adds the current directory as "". A neighboring .cmx can
     inline values even if its plugin was never loaded. *)
  Load_path.remove_dir "";
  Toploop.initialize_toplevel_env ();
  Hol_loader.file_loader := eval_file false;
  Hol_loader.use_file_raise_failure := true;
  if not (eval false "open Hol_lib;; open Hol_loader;;") then
    failwith "could not initialize the HOL prompt";
  List.iter (fun name ->
    Topdirs.dir_install_printer Format.std_formatter (Longident.Lident name))
    ["pp_print_qterm"; "pp_print_qtype"; "pp_print_thm"; "pp_print_goal";
     "pp_print_goalstack"]

(* Forked nodes inherit the state of Filename's private random generator,
   so siblings draw the same temporary names. The native toplevel derives
   further names from them without O_EXCL (the phrase's .o next to its
   .so), and concurrent phrases in siblings then failed with "File
   exists". Give every node its own directory below the session's, which
   the supervisor removes with the node. *)
let session_temp = Filename.get_temp_dir_name ()
let temp_name = ref ""

let private_temp_dir () =
  (* A fresh seed: a PID can recur before the supervisor has removed the
     directory of the node that last had it. *)
  let nonce = Random.State.bits (Random.State.make_self_init ()) in
  temp_name := Printf.sprintf "node-%d-%x" (Unix.getpid ()) nonce;
  Unix.mkdir (Filename.concat session_temp !temp_name) 0o700;
  Filename.set_temp_dir_name (Filename.concat session_temp !temp_name)

let null = Unix.openfile "/dev/null" [Unix.O_RDWR; Unix.O_CLOEXEC] 0
let self = ref (Unix.getpid ())
let control = ref Unix.stdin
let children = ref []

let rec write_all fd s off =
  if off < String.length s then
    write_all fd s (off + Unix.write_substring fd s off (String.length s - off))

let report fmt = Printf.ksprintf (fun s -> write_all !control (s ^ "\n") 0) fmt

(* Every node leads its own process group, which also holds the compilers
   and commands it starts. A node always ends here: each child ends its
   own subtree on SIGTERM, then this node kills its group. *)
let die () =
  List.iter (fun pid -> try Unix.kill (-pid) Sys.sigterm with Unix.Unix_error _ -> ()) !children;
  Unix.kill 0 Sys.sigkill;
  Unix._exit 1

let reap _ =
  children := List.filter (fun pid ->
    match Unix.waitpid [Unix.WNOHANG] pid with
    | 0, _ -> true
    | _, status ->
        (* A child normally ends its own group. After a SIGKILL from outside
           or from the supervisor's fallback, end the commands it left
           behind. The child is already reaped, so if its group is empty a
           new process could in principle reuse the ID before this kill;
           Linux allocates IDs in order, which makes that negligible. *)
        (try Unix.kill (-pid) Sys.sigkill with Unix.Unix_error _ -> ());
        report "reaped %d %d" pid (match status with Unix.WEXITED n -> n | _ -> 255);
        false
    | exception Unix.Unix_error (Unix.ECHILD, _, _) -> false) !children

(* Introduce a new connection to the supervisor as "n" (control) or "o"
   (one request's output), followed by the supervisor's token. *)
let connect kind token =
  let s = Unix.socket ~cloexec:true Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  Unix.connect s (Unix.ADDR_UNIX (Sys.getenv "HOL_D_NODES"));
  write_all s (kind ^ token ^ "\n") 0;
  s

let run_request tag token text =
  let out = connect "o" token in
  Unix.dup2 out Unix.stdout;
  Unix.dup2 out Unix.stderr;
  Unix.close out;
  let ok =
    try match tag with
      | "E" -> eval true text
      | "P" ->
          (match String.split_on_char '\000' text with
           | [directory; plugin] -> Dynlink.loadfile plugin; Topdirs.dir_directory directory; true
           | _ -> failwith "invalid public load request")
      | "L" | "R" -> Dynlink.loadfile_private text; true
      | _ -> failwith "unknown request"
    with exn -> prerr_endline (Printexc.to_string exn); false in
  flush_output ();
  (* A one-shot child's exit handlers, such as a proof footer, still write
     to the request. *)
  if tag <> "R" then begin Unix.dup2 null Unix.stdout; Unix.dup2 null Unix.stderr end;
  ok

(* Requests arrive as "TAG TOKEN LENGTH\n" followed by LENGTH bytes. Control
   EOF means the supervisor removed this node or itself died. *)
let rec serve token =
  control := connect "n" token;
  let input = Unix.in_channel_of_descr !control in
  report "ready %d %s" (Unix.getpid ()) !temp_name;
  while true do
    let tag, token, size = Scanf.sscanf (input_line input) "%s %s %d" (fun a b c -> a, b, c) in
    let payload = really_input_string input size in
    if tag = "F" then begin
      flush_output ();
      (* Record the PID before SIGCHLD can report it. *)
      let mask = Unix.sigprocmask Unix.SIG_BLOCK [Sys.sigchld] in
      match Unix.fork () with
      | 0 ->
          self := Unix.getpid ();
          ignore (Unix.setsid ());
          children := [];
          Unix.close !control;
          ignore (Unix.sigprocmask Unix.SIG_SETMASK mask);
          (* Never unwind into the parent's loop. *)
          (try private_temp_dir (); serve token with _ -> ());
          die ()
      | pid ->
          children := pid :: !children;
          (* Report before unblocking, which runs a pending reap, so the
             supervisor knows the PID before any "reaped" line. *)
          report "forked %d" pid;
          ignore (Unix.sigprocmask Unix.SIG_SETMASK mask)
      | exception exn ->
          ignore (Unix.sigprocmask Unix.SIG_SETMASK mask);
          report "error %s" (Printexc.to_string exn)
    end else begin
      let ok = run_request tag token payload in
      report "%s" (if ok then "ok" else "error");
      (* The parent reports this exit status, including exit handlers. *)
      if tag = "R" then exit (if ok then 0 else 1);
      if not ok && tag <> "E" then die ()
    end
  done

(* A process that a plugin forks without exec inherits these handlers. It
   must not end the node, so it takes the signal's default action. *)
let ending signo =
  if Unix.getpid () = !self then die ();
  Sys.set_signal signo Sys.Signal_default;
  Unix.kill (Unix.getpid ()) signo

let () =
  Sys.set_signal Sys.sigterm (Sys.Signal_handle ending);
  (* Writing to a closed control channel after the daemon died must still
     end the subtree. A handler, unlike Signal_ignore, resets on exec. *)
  Sys.set_signal Sys.sigpipe (Sys.Signal_handle ending);
  Sys.set_signal Sys.sigchld (Sys.Signal_handle reap);
  Unix.dup2 null Unix.stdin;
  (try private_temp_dir (); initialize () with exn ->
     prerr_endline ("hol-d: " ^ Printexc.to_string exn); flush_output (); die ());
  flush_output ();
  Unix.dup2 null Unix.stdout;
  Unix.dup2 null Unix.stderr;
  (try serve Sys.argv.(1) with _ -> ());
  die ()
