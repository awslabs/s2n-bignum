(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(*
 * Persistent external instruction-executor sessions for cosimulation tests.
 *
 * A successful session has the following shape:
 *
 * HOL client                                 executor
 *     |                                          |
 *     |<--- READY 1 aarch64 128 -----------------|
 *     |                                          |
 *     |--- RUN 1f2003d5 0 ... ------------------>|
 *     |                                          |
 *     |<--- OK 0 ... ----------------------------|
 *     |                                          |
 *     |--- QUIT -------------------------------->|
 *     |                                          |
 *
 * READY identifies the protocol version, architecture, and state-word count.
 * RUN carries hexadecimal instruction bytes followed by unsigned decimal
 * state words. OK returns the resulting state. TRAP reports an execution
 * trap, while ERROR reports a malformed request or executor failure.
 * The ellipses above abbreviate state words; they are not sent literally.
 *)

external cosim_process_exit : int -> 'a = "unix_exit";;

type cosim_response =
  | Cosim_ok of string list
  | Cosim_trap of string list;;

type cosim_executor =
 { cosim_command: string;
   cosim_arch: string;
   cosim_state_words: int;
   cosim_metadata: string list;
   cosim_pid: int;
   cosim_from_child: in_channel;
   cosim_to_child: out_channel;
   mutable cosim_closed: bool };;

let cosim_words s =
  List.filter (fun x -> x <> "") (String.split_on_char ' ' s);;

let cosim_getenv name =
  try Some (Sys.getenv name) with Not_found -> None;;

let cosim_timeout () =
  match cosim_getenv "S2N_BIGNUM_EXECUTOR_TIMEOUT" with
  | None -> 10.0
  | Some s ->
      let t = float_of_string s in
      if t <= 0.0 then failwith "S2N_BIGNUM_EXECUTOR_TIMEOUT must be positive"
      else t;;

let cosim_sleep seconds =
  ignore (Unix.select [] [] [] seconds);;

let cosim_kill_group executor signal =
  try Unix.kill (-executor.cosim_pid) signal with _ -> ();;

let cosim_kill executor signal =
  try Unix.kill (-executor.cosim_pid) signal with _ ->
  try Unix.kill executor.cosim_pid signal with _ -> ();;

let cosim_process_group_alive executor =
  try Unix.kill (-executor.cosim_pid) 0; true with
  | Unix.Unix_error (Unix.ESRCH,_,_) -> false
  | _ -> true;;

let cosim_waitpid pid =
  let rec wait () =
    try ignore (Unix.waitpid [] pid) with
    | Unix.Unix_error (Unix.EINTR,_,_) -> wait ()
    | Unix.Unix_error (Unix.ECHILD,_,_) -> () in
  wait ();;

let cosim_reap_or_kill executor =
  match try Some (Unix.fork ()) with _ -> None with
  | Some 0 ->
      let rec wait_for_exit retries =
        if cosim_process_group_alive executor then
          if retries = 0 then false
          else begin
            cosim_sleep 0.01;
            wait_for_exit (retries - 1)
          end
        else true in
      if not (wait_for_exit 50) then begin
        cosim_kill_group executor Sys.sigterm;
        if not (wait_for_exit 50) then
          cosim_kill_group executor Sys.sigkill
      end;
      cosim_process_exit 0
  | Some watchdog_pid ->
      cosim_waitpid executor.cosim_pid;
      cosim_waitpid watchdog_pid
  | None ->
      cosim_kill executor Sys.sigkill;
      cosim_waitpid executor.cosim_pid;
      if cosim_process_group_alive executor then
        cosim_kill_group executor Sys.sigkill;;

let abort_cosim_executor executor =
  if not executor.cosim_closed then begin
    executor.cosim_closed <- true;
    close_out_noerr executor.cosim_to_child;
    close_in_noerr executor.cosim_from_child;
    cosim_reap_or_kill executor
  end;;

let close_cosim_executor executor =
  if not executor.cosim_closed then begin
    executor.cosim_closed <- true;
    (try
       output_string executor.cosim_to_child "QUIT\n";
       flush executor.cosim_to_child
     with _ -> ());
    close_out_noerr executor.cosim_to_child;
    close_in_noerr executor.cosim_from_child;
    cosim_reap_or_kill executor
  end;;

let cosim_read_line executor =
  let fd = Unix.descr_of_in_channel executor.cosim_from_child in
  let deadline = Unix.gettimeofday () +. cosim_timeout () in
  let line = Buffer.create 256
  and byte = Bytes.create 1 in
  let fail reason =
      let command = executor.cosim_command in
      abort_cosim_executor executor;
      failwith ("instruction executor " ^ reason ^ ": " ^ command) in
  let rec read () =
    let remaining = deadline -. Unix.gettimeofday () in
    if remaining <= 0.0 then fail "timed out";
    match Unix.select [fd] [] [] remaining with
    | [],_,_ -> fail "timed out"
    | _ ->
        try
          match Unix.read fd byte 0 1 with
          | 0 -> fail "terminated"
          | _ ->
              let character = Bytes.get byte 0 in
              if character = '\n' then
                let result = Buffer.contents line in
                let length = String.length result in
                if length > 0 && result.[length - 1] = '\r' then
                  String.sub result 0 (length - 1)
                else result
              else begin
                Buffer.add_char line character;
                read ()
              end
        with
        | Unix.Unix_error (Unix.EINTR,_,_) -> read ()
        | Unix.Unix_error (Unix.EAGAIN,_,_) -> read ()
        | Unix.Unix_error (Unix.EWOULDBLOCK,_,_) -> read () in
  read ();;

let cosim_spawn command =
  let child_stdin,parent_to_child = Unix.pipe ()
  and parent_from_child,child_stdout = Unix.pipe () in
  Unix.set_close_on_exec parent_to_child;
  Unix.set_close_on_exec parent_from_child;
  match Unix.fork () with
  | 0 ->
      (try
         Unix.close parent_to_child;
         Unix.close parent_from_child;
         ignore (Unix.setsid ());
         Unix.dup2 child_stdin Unix.stdin;
         Unix.dup2 child_stdout Unix.stdout;
         Unix.close child_stdin;
         Unix.close child_stdout;
         Unix.execv "/bin/sh" [|"/bin/sh"; "-c"; "exec " ^ command|]
       with _ -> cosim_process_exit 127)
  | pid ->
      Unix.close child_stdin;
      Unix.close child_stdout;
      pid,Unix.in_channel_of_descr parent_from_child,
          Unix.out_channel_of_descr parent_to_child;;

let start_cosim_executor env_name default_command expected_arch expected_words =
  let command =
    match cosim_getenv env_name with
    | Some s when s <> "" -> s
    | Some _ -> failwith (env_name ^ " must not be empty")
    | None -> default_command in
  let pid,from_child,to_child = cosim_spawn command in
  let partial =
   { cosim_command = command;
     cosim_arch = expected_arch;
     cosim_state_words = expected_words;
     cosim_metadata = [];
     cosim_pid = pid;
     cosim_from_child = from_child;
     cosim_to_child = to_child;
     cosim_closed = false } in
  let fail message =
    abort_cosim_executor partial;
    failwith message in
  let ready = cosim_words (cosim_read_line partial) in
  let version,arch,state_words,metadata =
    match ready with
    | "READY"::version::arch::state_words::metadata ->
        let words =
          try int_of_string state_words with Failure _ ->
            fail ("malformed instruction-executor greeting from " ^ command) in
        version,arch,words,metadata
    | _ -> fail ("malformed instruction-executor greeting from " ^ command) in
  if version <> "1" then
    fail ("unsupported instruction-executor protocol: " ^ version);
  if arch <> expected_arch then
    fail ("instruction-executor architecture " ^ arch ^
          " does not match " ^ expected_arch);
  if state_words <> expected_words then
    fail ("instruction-executor state-word count " ^
          string_of_int state_words ^
          " does not match " ^ string_of_int expected_words);
  let executor = { partial with cosim_metadata = metadata } in
  at_exit (fun () -> close_cosim_executor executor);
  executor;;

let cosim_hex_of_bytes bytes =
  String.concat ""
    (List.map
      (fun b ->
        if b < 0 || b > 255 then failwith "instruction byte out of range";
        Printf.sprintf "%02x" b)
      bytes);;

let cosim_semtest_seconds default =
  match cosim_getenv "S2N_BIGNUM_SEMATEST_SECONDS" with
  | None -> default
  | Some s ->
      let seconds = float_of_string s in
      if seconds <= 0.0 then
        failwith "S2N_BIGNUM_SEMATEST_SECONDS must be positive";
      seconds;;

let cosim_semtest_case_limit () =
  match cosim_getenv "S2N_BIGNUM_SEMATEST_CASES" with
  | None -> None
  | Some s ->
      let cases = int_of_string s in
      if cases <= 0 then
        failwith "S2N_BIGNUM_SEMATEST_CASES must be positive";
      Some cases;;

let cosim_semtest_random_init () =
  match cosim_getenv "S2N_BIGNUM_SEMATEST_SEED" with
  | None -> Random.self_init ()
  | Some s -> Random.init (int_of_string s);;

let cosim_semtest_finished seconds cases start_time count =
  Unix.gettimeofday () -. start_time > seconds ||
  match cases with
  | None -> false
  | Some limit -> count >= limit;;

let cosim_execute executor code state =
  if executor.cosim_closed then failwith "instruction executor is closed";
  if code = "" then failwith "instruction executor received empty code";
  if List.length state <> executor.cosim_state_words then
    failwith ("instruction-executor input state has " ^
              string_of_int (List.length state) ^ " words, expected " ^
              string_of_int executor.cosim_state_words);
  output_string executor.cosim_to_child
    ("RUN " ^ code ^ " " ^ String.concat " " state ^ "\n");
  flush executor.cosim_to_child;
  match cosim_words (cosim_read_line executor) with
  | "OK"::words when List.length words = executor.cosim_state_words ->
      Cosim_ok words
  | "OK"::words ->
      failwith ("instruction-executor output state has " ^
                string_of_int (List.length words) ^ " words, expected " ^
                string_of_int executor.cosim_state_words)
  | "TRAP"::details -> Cosim_trap details
  | "ERROR"::details ->
      failwith ("instruction executor error: " ^ String.concat " " details)
  | _ -> failwith "malformed instruction-executor response";;
