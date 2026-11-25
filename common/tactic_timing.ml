(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Timing of tactics: where the time of a long proof goes.                   *)
(*                                                                           *)
(*   TIMED_TAC "name" tac                                                    *)
(*                                                                           *)
(* behaves as tac and, when timing is on, adds the time of each application  *)
(* (until tac returns its goalstate or fails; the justification, which runs  *)
(* when the proof is complete, is not included) to the totals of "name":     *)
(* the number of calls, the wall clock and the CPU time, both in seconds.    *)
(* Names may nest (a phase inside another): each total is inclusive.         *)
(*                                                                           *)
(*   tactic_timing_report "title"   prints the totals, the largest first,    *)
(*   tactic_timing_reset ()         clears them,                             *)
(*   timed_section "name" f x       times a plain function the same way,     *)
(*   timed_outcome "name" f x       the same, as "name.ok" if f x returns     *)
(*                                  and "name.fail" if it raises.            *)
(*                                                                           *)
(* Timing is on if the environment variable S2N_TACTIC_TIMING is set (to     *)
(* anything but 0) or after tactic_timing := true. With                      *)
(* S2N_TACTIC_TIMING_LOG=t (seconds), every application longer than t is    *)
(* also printed as "TIME name wall cpu" when it ends.                        *)
(*                                                                           *)
(* The wall clock is Unix.gettimeofday (the native builds of the proofs     *)
(* link the unix library); the CPU time (Sys.time) is that of the process,  *)
(* i.e. of all domains: run with one domain for per-phase CPU times. The     *)
(* totals are updated under par_locked (common/par.ml).                      *)
(* ========================================================================= *)

needs "common/par.ml";;

let tactic_timing =
  ref (match Sys.getenv_opt "S2N_TACTIC_TIMING" with
         None -> false | Some s -> s <> "" && s <> "0");;

let tactic_timing_log =
  ref (match Sys.getenv_opt "S2N_TACTIC_TIMING_LOG" with
         None -> infinity
       | Some s -> try float_of_string (String.trim s) with Failure _ -> infinity);;

let tactic_timing_table : (string, int * float * float) Hashtbl.t =
  Hashtbl.create 64;;

let tactic_timing_add name wall cpu =
  par_locked (fun () ->
    let n,w,c = try Hashtbl.find tactic_timing_table name
                with Not_found -> 0,0.0,0.0 in
    Hashtbl.replace tactic_timing_table name (n + 1,w +. wall,c +. cpu));
  if wall >= !tactic_timing_log then
    Printf.printf "TIME %s %.2f %.2f\n%!" name wall cpu;;

let timed_section name (f:'a -> 'b) (x:'a) : 'b =
  if not !tactic_timing then f x else
  let w0 = Unix.gettimeofday () and c0 = Sys.time () in
  let fin () = tactic_timing_add name (Unix.gettimeofday () -. w0)
                                 (Sys.time () -. c0) in
  let r = try f x with e -> (fin (); raise e) in
  fin (); r;;

let timed_outcome name (f:'a -> 'b) (x:'a) : 'b =
  if not !tactic_timing then f x else
  let w0 = Unix.gettimeofday () and c0 = Sys.time () in
  let fin k = tactic_timing_add (name ^ k) (Unix.gettimeofday () -. w0)
                                (Sys.time () -. c0) in
  let r = try f x with e -> (fin ".fail"; raise e) in
  fin ".ok"; r;;

let TIMED_TAC name (tac:tactic) : tactic =
  fun g -> timed_section name tac g;;

let tactic_timing_reset () =
  par_locked (fun () -> Hashtbl.reset tactic_timing_table);;

let tactic_timing_report title =
  if !tactic_timing then
   (let l = par_locked (fun () ->
              Hashtbl.fold (fun k v acc -> (k,v)::acc) tactic_timing_table []) in
    let l = List.sort (fun (_,(_,a,_)) (_,(_,b,_)) -> compare b a) l in
    Printf.printf "TIMING %s: %-36s %8s %10s %10s\n" title "phase" "calls" "wall" "cpu";
    List.iter (fun (k,(n,w,c)) ->
        Printf.printf "TIMING %s: %-36s %8d %10.1f %10.1f\n" title k n w c) l;
    Printf.printf "%!");;
