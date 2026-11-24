(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0 *)

(* Hol_lib and Proof_base are linked before this module and have finished
   their initialization when we get here. No proof plugin runs in the parent. *)

let flush_output () =
  Format.pp_print_flush Format.std_formatter ();
  Format.pp_print_flush Format.err_formatter ();
  flush stdout;
  flush stderr

let run_plugin plugin =
  try
    Dynlink.loadfile_private plugin;
    flush_output ();
    print_endline "Proof batch plugin returned";
    0
  with exn ->
    Printf.eprintf "Exception: %s\n%!" (Printexc.to_string exn);
    1

let run_child artifact log =
  let fd = Unix.openfile log [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_EXCL] 0o600 in
  Unix.dup2 fd Unix.stdout;
  Unix.dup2 fd Unix.stderr;
  Unix.close fd;
  if Filename.check_suffix artifact ".native" then
    Unix.execv artifact [|artifact|]
  else
    exit (run_plugin artifact)

let describe_status = function
  | Unix.WEXITED n -> Printf.sprintf "exit %d" n
  | Unix.WSIGNALED n -> Printf.sprintf "signal %d" n
  | Unix.WSTOPPED n -> Printf.sprintf "stopped %d" n

let rec waitpid pid =
  try Unix.waitpid [] pid with Unix.Unix_error (Unix.EINTR, _, _) -> waitpid pid

(* runner.py reads "ready\t<seconds>\t-" once the base is initialized, then
   one "<status>\t<seconds>\t<log>" line per finished child, from
   PROOF_BATCH_STATUS (a /dev/fd path), to report progress live. *)
let status_channel =
  match Sys.getenv_opt "PROOF_BATCH_STATUS" with
  | None -> None
  | Some path ->
      let channel = open_out_gen [Open_wronly] 0 path in
      Unix.set_close_on_exec (Unix.descr_of_out_channel channel);
      Some channel

let run_pool jobs tasks =
  let active = Hashtbl.create jobs in
  let ok = ref true in
  let reap () =
    let pid, status = waitpid (-1) in
    let artifact, log, start = Hashtbl.find active pid in
    Hashtbl.remove active pid;
    if status = Unix.WEXITED 0 then
      (* Only the parent certifies a clean OS exit. The caller separately
         checks the shared log, proof log and plugin-return trailer. *)
      Sys.rename log (log ^ ".exited")
    else begin
      Printf.eprintf "%s: %s (log %s)\n%!" artifact (describe_status status) log;
      ok := false
    end;
    Option.iter (fun channel ->
      Printf.fprintf channel "%s\t%.3f\t%s\n%!"
        (if status = Unix.WEXITED 0 then "ok" else describe_status status)
        (Unix.gettimeofday () -. start) log) status_channel
  in
  (* No signal handling here (Hol_lib enables Sys.catch_break, so SIGINT
     raises Sys.Break). runner.py stops the children: it kills the whole
     process group when the worker ends, including after an exception here. *)
  List.iter (fun (artifact, log) ->
    if Hashtbl.length active >= jobs then reap ();
    match Unix.fork () with
    | 0 ->
        (* Never unwind into the parent's code in a child, including if log
           creation fails. Its inherited pid table belongs to the parent. *)
        (try run_child artifact log with exn ->
           Printf.eprintf "%s: %s\n%!" artifact (Printexc.to_string exn);
           Unix._exit 1)
    | pid -> Hashtbl.add active pid (artifact, log, Unix.gettimeofday ())) tasks;
  while Hashtbl.length active > 0 do reap () done;
  if !ok then 0 else 1

let () =
  let argv = Sys.argv in
  let elapsed = Unix.gettimeofday () -. float_of_string argv.(1) in
  Printf.printf "Proof batch base ready: %.3f sec\n%!" elapsed;
  Option.iter (fun channel -> Printf.fprintf channel "ready\t%.3f\t-\n%!" elapsed) status_channel;
  (* A fork copies OCaml buffers as well as the heap. Do not duplicate the
     parent's initialization output in each child's redirected log. *)
  flush_output ();
  (* worker <start unixtime> <jobs> (<artifact> <log>)... *)
  let pairs = List.init ((Array.length argv - 3) / 2)
    (fun i -> argv.(3 + 2*i), argv.(4 + 2*i)) in
  exit (run_pool (int_of_string argv.(2)) pairs)
