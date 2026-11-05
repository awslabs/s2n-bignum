(* Prove the claims of one suite in several processes after shared setup.

   In the largest suites, loading the s2n-bignum base and the generated
   model takes a third of the run, and the claims that follow are
   independent. With SAIL_HOL_PROOF_FORKS=N for N > 1, a driver's call
   sail_hl_proof_fork marker forks N children where it stands. Child i
   runs the rest of the driver, where sail_hl_proof_shard key holds only
   for the claims assigned to i, with its output in a private file. The
   parent never returns: it waits for every child and prints all their
   output in child order. If each child's output ends with the completion
   marker and has it nowhere else, the parent prints the marker once and
   exits with status 0; otherwise with status 1.

   Each theorem is still proved by the kernel, in a child whose state is a
   fork of the kernel-checked setup; the parent receives only text. A
   child repeats any check the driver makes after the call, such as
   check_axioms, on its own state. Without SAIL_HOL_PROOF_FORKS, or with
   1, nothing forks and every claim is kept. ci/check.py audits the
   combined output exactly as it audits a single-process run. *)

let sail_hl_proof_forks =
  match Sys.getenv_opt "SAIL_HOL_PROOF_FORKS" with
  | None | Some "" | Some "1" -> 1
  | Some text ->
      (match int_of_string_opt text with
       | Some count when 1 <= count && count <= 64 -> count
       | _ -> failwith "SAIL_HOL_PROOF_FORKS must be between 1 and 64");;

(* This process's child index once forked, or None. *)
let sail_hl_proof_child = ref None;;

(* Keys go to children in turn, in the order they are first asked about.
   Every child runs the same code up to a filter, so all of them assign
   the same keys alike, and a key asked about again, such as the root of
   a theorem derived from two earlier claims, stays with its child. Call
   sail_hl_proof_shard only where every child runs, never inside a claim's
   proof. *)
let sail_hl_proof_owners = Hashtbl.create 64;;

let sail_hl_proof_shard key =
  match !sail_hl_proof_child with
  | None -> true
  | Some index ->
      let owner = match Hashtbl.find_opt sail_hl_proof_owners (key:string) with
        | Some owner -> owner
        | None ->
            let owner =
              Hashtbl.length sail_hl_proof_owners mod sail_hl_proof_forks in
            Hashtbl.add sail_hl_proof_owners key owner;
            owner in
      owner = index;;

(* For claims written as separate top-level proofs: Some theorem if this
   process proves the claim with this key, otherwise None. Only the
   process that proves a claim reports it. *)
let sail_hl_proof_claim key proof =
  if sail_hl_proof_shard key then begin
    let theorem = proof () in
    print_endline (key ^ " proved");
    Some theorem
  end else None;;

(* Whether this process proves every claim of its suite. Drivers check
   their own claim counts only then; ci/check.py checks the combined
   theorem inventory of a forked run. *)
let sail_hl_proof_whole () = !sail_hl_proof_child = None;;

(* Children write to files in the proof build directory, which
   check-proof.sh runs from the repository root. *)
let sail_hl_proof_directory () =
  let directory = "tools/sail/_build" in
  if Sys.file_exists directory then directory else Filename.get_temp_dir_name ();;

(* A child's output is complete if its last line is the marker, which the
   driver prints after check_axioms, and no earlier line is. A child that
   fails or dies prints no marker. HOL Light's syntax reads all-capital
   names such as WEXITED as values, so the exit status is not inspected. *)
let sail_hl_proof_complete marker lines =
  match List.rev lines with
  | last :: earlier -> last = marker && not (mem marker earlier)
  | [] -> false;;

let sail_hl_proof_fork marker =
  if sail_hl_proof_forks > 1 && !sail_hl_proof_child = None then begin
    (* Unflushed setup output must not reach a child's file as well. *)
    Format.pp_print_flush Format.std_formatter ();
    Format.pp_print_flush Format.err_formatter ();
    flush_all ();
    let files = List.init sail_hl_proof_forks (fun _ ->
      Filename.temp_file ~temp_dir:(sail_hl_proof_directory ())
        "proof-child-" ".log") in
    let started = ref [] in
    (* Only the parent forks; a child leaves the loop and goes on. *)
    (try
       List.iteri (fun index file ->
         if !sail_hl_proof_child = None then
           match Unix.fork () with
           | 0 ->
               let output = open_out_bin file in
               Unix.dup2 (Unix.descr_of_out_channel output) Unix.stdout;
               Unix.dup2 (Unix.descr_of_out_channel output) Unix.stderr;
               close_out output;
               sail_hl_proof_child := Some index
           | pid -> started := pid :: !started) files
     with error ->
       (* No child may outlive a parent that could not start them all. *)
       List.iter (fun pid ->
         (try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ());
         (try ignore (Unix.waitpid [] pid) with Unix.Unix_error _ -> ()))
         !started;
       List.iter (fun file -> try Sys.remove file with Sys_error _ -> ()) files;
       raise error);
    if !sail_hl_proof_child = None then begin
      List.iter (fun pid ->
        try ignore (Unix.waitpid [] pid) with Unix.Unix_error _ -> ()) !started;
      (* Read and remove every file before deciding, so that no output of
         a later child is lost after an earlier one failed. *)
      let complete = map (fun file ->
        let channel = open_in_bin file in
        let lines = ref [] in
        (try while true do lines := input_line channel :: !lines done
         with End_of_file -> ());
        close_in channel;
        Sys.remove file;
        let lines = rev !lines in
        let complete = sail_hl_proof_complete marker lines in
        List.iter print_endline
          (if complete then butlast lines else lines);
        complete) files in
      if forall (fun complete -> complete) complete then
        (print_endline marker; exit 0)
      else begin
        prerr_endline "a forked proof process failed";
        exit 1
      end
    end
  end;;
