(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Parallel execution of proofs, with a serial default.                      *)
(*                                                                           *)
(* Many proofs have parts that do not depend on each other: separate         *)
(* theorems proved in one session, or the subgoals of a case split. With a   *)
(* HOL Light whose kernel and core are safe for it (see                      *)
(* common/par_domains.ml), such parts can run at the same time on several    *)
(* OCaml 5 domains of one process. This file is the interface for doing so,  *)
(* and its default backend runs everything on the calling domain, in order,  *)
(* as plain HOL Light does:                                                  *)
(*                                                                           *)
(*   par_spawn f      start f (); par_await gives its result or exception    *)
(*   prove_async p    par_spawn of prove p, with the term parsed before      *)
(*   PAR_THENL tac l  tac THENL l, with the branches run at the same time    *)
(*   par_run_jobs l   the named jobs of l, the costliest first, timed        *)
(*                                                                           *)
(* and for state that proofs share:                                          *)
(*                                                                           *)
(*   par_local f      a function giving the value f () made on first use:    *)
(*                    one value per domain with the parallel backend         *)
(*   par_local_ref f  par_local (fun () -> ref (f ())), whose value a task   *)
(*                    starts with is that of the domain that spawned it      *)
(*   par_locked f     f () while holding a lock (the same for all calls)     *)
(*   par_counter ()   a function giving 0, 1, 2, ... on successive calls,    *)
(*                    atomically with the parallel backend                   *)
(*                                                                           *)
(* common/par_domains.ml is the parallel backend; its header says how to     *)
(* enable it and what it needs of HOL Light. It is loaded first, before any  *)
(* file that makes such state, when proofs are built with HOL_PAR=1          *)
(* (tools/build-proof.sh); S2N_PAR_DOMAINS gives the number of domains.      *)
(* Without it this file is all there is, and the proofs run on one domain.   *)
(*                                                                           *)
(* The two backends run the same proof steps: the branches of PAR_THENL are  *)
(* independent in both (see PAR_THENL below), so a proof that works serially *)
(* works in parallel, unless it uses state that is shared without the        *)
(* functions above. Inside a task, do not make definitions that other tasks  *)
(* use, change the parser, the interface or the default rewrites, or use the *)
(* goal stack (see common/par_domains.ml).                                   *)
(*                                                                           *)
(* Only the names in the signature of the module Par below are visible; the  *)
(* file includes Par at the end.                                             *)
(* ========================================================================= *)

module Par : sig

  (* A backend. par_backend_spawn run arranges for run () to be called once, *)
  (* on some domain, and returns wait; run does not raise. wait () returns   *)
  (* once run () has returned (running it on the calling domain if no domain *)
  (* has started it) and may be called again; what run wrote is then visible *)
  (* to the caller. par_backend_local f returns a function giving the value  *)
  (* f () made on first use on each domain; par_backend_locked f runs f ()   *)
  (* holding one lock; par_backend_counter () returns a function giving 0,   *)
  (* 1, 2, ... atomically; par_backend_clock is the clock of par_run_jobs.   *)

  type par_backend =
    { par_backend_domains : int;
      par_backend_spawn : (unit -> unit) -> (unit -> unit);
      par_backend_local : 'a. (unit -> 'a) -> (unit -> 'a);
      par_backend_locked : 'a. (unit -> 'a) -> 'a;
      par_backend_counter : unit -> (unit -> int);
      par_backend_clock : unit -> float }

  (* par_set_backend b uses b from now on. It fails once par_local,         *)
  (* par_local_ref or par_counter has been called, since their state belongs *)
  (* to the backend that made it.                                            *)

  val par_set_backend : par_backend -> unit

  (* S2N_PAR_DOMAINS, 1 by default.                                          *)

  val par_requested_domains : unit -> int

  val par_local : (unit -> 'a) -> unit -> 'a
  val par_local_ref : (unit -> 'a) -> unit -> 'a ref
  val par_locked : (unit -> 'a) -> 'a
  val par_counter : unit -> unit -> int

  type 'a par_future
  val par_spawn : (unit -> 'a) -> 'a par_future
  val par_await : 'a par_future -> 'a

  (* The prove of prove_async: HOL Light's prove until relative.ml sets its  *)
  (* own.                                                                    *)

  val par_set_prove : (term * tactic -> thm) -> unit
  val prove_async : term * tactic -> thm par_future

  val PAR_THENL : tactic -> tactic list -> tactic

  val par_run_jobs : (string * float * (unit -> 'a)) list -> 'a list

end = struct

(* ------------------------------------------------------------------------- *)
(* The backend.                                                              *)
(* ------------------------------------------------------------------------- *)

type par_backend =
  { par_backend_domains : int;
    par_backend_spawn : (unit -> unit) -> (unit -> unit);
    par_backend_local : 'a. (unit -> 'a) -> (unit -> 'a);
    par_backend_locked : 'a. (unit -> 'a) -> 'a;
    par_backend_counter : unit -> (unit -> int);
    par_backend_clock : unit -> float };;

(* The result or exception of a computation, for par_await.                  *)

type 'a outcome =
    Value of 'a
  | Raised of exn * Printexc.raw_backtrace;;

let run_outcome f =
  try Value (f ())
  with e -> Raised (e, Printexc.get_raw_backtrace ());;

let outcome_value r =
  match r with
    Value v -> v
  | Raised (e, bt) -> Printexc.raise_with_backtrace e bt;;

(* The cells of par_local_ref, which a computation starts with the values    *)
(* of the domain that spawned it, and whose changes it does not pass back:   *)
(* each entry, called on the spawning domain, reads the value and returns a  *)
(* function that, called on the domain that runs the computation, sets the   *)
(* cell there and returns a function that restores the old value.            *)

let inherited_cells =
  ref ([] : (unit -> unit -> (unit -> unit)) list);;

let capture () = List.map (fun e -> e ()) !inherited_cells;;

let run_captured captured f =
  run_outcome (fun () ->
    let restore = List.map (fun i -> i ()) captured in
    let r = run_outcome f in
    List.iter (fun u -> u ()) restore;
    outcome_value r);;

let par_requested_domains () =
  match Sys.getenv_opt "S2N_PAR_DOMAINS" with
    None -> 1
  | Some s ->
      try max 1 (int_of_string (String.trim s))
      with Failure _ -> failwith ("S2N_PAR_DOMAINS: not a number: " ^ s);;

(* The serial backend runs a spawned computation at once, so that effects    *)
(* such as printing happen in the order of the program. S2N_PAR_DOMAINS      *)
(* above 1 with this backend is an error rather than a silent serial run.    *)

let serial_backend =
  let checked = ref false in
  let check () =
    if not !checked then
     (checked := true;
      if par_requested_domains () > 1 then
        failwith ("S2N_PAR_DOMAINS > 1, but these proofs are built for one " ^
                  "domain: build them with HOL_PAR=1 (see " ^
                  "common/par_domains.ml)")) in
  { par_backend_domains = 1;
    par_backend_spawn = (fun run -> check (); run (); fun () -> ());
    par_backend_local =
      (fun f -> let v = lazy (f ()) in fun () -> Lazy.force v);
    par_backend_locked = (fun f -> f ());
    par_backend_counter =
      (fun () -> let n = ref 0 in fun () -> let k = !n in n := k + 1; k);
    par_backend_clock = Sys.time };;

let backend = ref serial_backend;;

let state_made = ref false;;

let par_set_backend b =
  if !state_made then
    failwith ("par_set_backend: par_local, par_local_ref or par_counter " ^
              "was called before; load the backend before any file that " ^
              "uses them")
  else backend := b;;

(* ------------------------------------------------------------------------- *)
(* Shared state.                                                             *)
(* ------------------------------------------------------------------------- *)

let par_local f = state_made := true; (!backend).par_backend_local f;;

let par_locked f = (!backend).par_backend_locked f;;

let par_counter () = state_made := true; (!backend).par_backend_counter ();;

let par_local_ref (f : unit -> 'a) : unit -> 'a ref =
  let get = par_local (fun () -> ref (f ())) in
  let entry () =
    let v = !(get ()) in
    fun () -> let r = get () in
              let old = !r in
              r := v; fun () -> r := old in
  par_locked (fun () -> inherited_cells := entry :: !inherited_cells);
  get;;

(* ------------------------------------------------------------------------- *)
(* Computations. The result of a computation goes through a reference that   *)
(* the backend's wait makes visible to the domain that awaits it.            *)
(* ------------------------------------------------------------------------- *)

type 'a par_future = unit -> 'a;;

let par_domains () = (!backend).par_backend_domains;;

let par_spawn (f : unit -> 'a) : 'a par_future =
  let captured = capture () in
  let result = ref None in
  let wait = (!backend).par_backend_spawn
               (fun () -> result := Some (run_captured captured f)) in
  fun () ->
    wait ();
    match !result with
      Some r -> outcome_value r
    | None -> failwith "par_await: the backend returned before the result";;

let par_await (fu : 'a par_future) : 'a = fu ();;

let par_map (f : 'a -> 'b) (l : 'a list) : 'b list =
  let fs = List.map (fun x -> par_spawn (fun () -> f x)) l in
  List.map par_await fs;;

(* ------------------------------------------------------------------------- *)
(* Proofs. prove_async uses the prove in effect when it is called, which is  *)
(* relative.ml's after that file is loaded (it calls par_set_prove).         *)
(* ------------------------------------------------------------------------- *)

let par_prove_fn = ref (fun (t,tac) -> prove(t,tac));;

let par_set_prove p = par_prove_fn := p;;

let prove_async (t,tac) : thm par_future =
  let p = !par_prove_fn in
  par_spawn (fun () -> p (t,tac));;

(* ------------------------------------------------------------------------- *)
(* PAR_THENL tac [tac1; ...; tacn] is tac THENL [tac1; ...; tacn], except    *)
(* that the branches are independent: each tacj works on its subgoal as tac  *)
(* made it, without the metavariable instantiations of the other branches,   *)
(* so they can run at the same time. The branches must not instantiate a     *)
(* metavariable of their subgoals differently (it fails otherwise); their    *)
(* instantiations are then applied to the theorems and the remaining         *)
(* subgoals of the others, so the result is that of THENL whenever the       *)
(* branches do not depend on each other's instantiations. For example, after *)
(* CONCRETIZE_F_EVENTS_TAC and META_EXISTS_TAC, each case of a case split on *)
(* the alignment of the stack pointer instantiates the events of its own     *)
(* case. Metavariables that a branch introduces itself are its own.          *)
(* ------------------------------------------------------------------------- *)

let PAR_THENL =
  (* The part of an instantiation for the variables vs (the metavariables   *)
  (* free in the subgoals of the branches, as opposed to those that a       *)
  (* branch introduces and instantiates itself, which may have the same      *)
  (* names in several branches but are resolved in each branch's theorem).  *)
  let restrict vs ((hi,tmi,tyi):instantiation) : instantiation =
    filter (fun (_,v) -> mem v vs) hi,filter (fun (_,v) -> mem v vs) tmi,tyi in
  (* The variables that several branches instantiate differently.          *)
  let conflicts insts =
    let tms = flat (map (fun (_,tmi,_) -> tmi) insts)
    and tys = flat (map (fun (_,_,tyi) -> tyi) insts) in
    let bad_tm (t,v) = exists (fun (t',v') -> v' = v && not (aconv t t')) tms
    and bad_ty (t,v) = exists (fun (t',v') -> v' = v && t' <> t) tys in
    setify (map (string_of_term o snd) (filter bad_tm tms) @
            map (string_of_type o snd) (filter bad_ty tys)) in
  let compose_all insts = itlist compose_insts insts null_inst in
  let par_sequence ((mvs1,insts1),gls1,just1) tacl : goalstate =
    if length tacl <> length gls1 then failwith "PAR_THENL: Length mismatch"
    else
    let results = par_map (fun (tac,g) -> (tac g : goalstate))
                          (zip tacl gls1) in
    let shared_vars =
      itlist (fun (asl,w) acc -> union (freesl (w::map (concl o snd) asl)) acc)
             gls1 [] in
    let binsts = map (fun ((_,i),_,_) -> restrict shared_vars i) results in
    let shared = conflicts binsts in
    if shared <> [] then
     (Format.print_string ("PAR_THENL: instantiated differently by several " ^
                           "branches: " ^ String.concat ", " shared);
      Format.print_newline ();
      failwith "PAR_THENL: branches instantiate the same metavariable")
    else
    let insts2 = compose_all binsts in
    (* Branch k, with the instantiations of the other branches *)
    let others k = compose_all (map snd (filter (fun (j,_) -> j <> k)
                                  (zip (0--(length binsts - 1)) binsts))) in
    let branches = zip (0--(length results - 1)) results in
    let gls2 = flat (map (fun (k,(_,gls,_)) -> map (inst_goal (others k)) gls)
                         branches) in
    let mvs2 = itlist (fun ((mvs,_),_,_) acc -> union mvs acc) results [] in
    let just2 i ths =
      let rec go bs ths =
        match bs with
          [] -> []
        | (k,(_,gls,just))::obs ->
            let ths1,ths2 = chop_list (length gls) ths in
            just (compose_insts (others k) i) ths1 :: go obs ths2 in
      go branches ths in
    let jst i ths = just1 (compose_insts insts2 i) (just2 i ths) in
    let just = if gls2 = [] then
                 (let th = jst null_inst [] in
                  fun i _ -> INSTANTIATE_ALL i th)
               else jst in
    ((union mvs1 mvs2,compose_insts insts1 insts2),gls2,just) in
  fun (tac:tactic) (tacl:tactic list) : tactic ->
    fun g -> let gstate = tac g in
             let _,gls,_ = gstate in
             par_sequence gstate (if gls = [] then [] else tacl);;

(* ------------------------------------------------------------------------- *)
(* par_run_jobs [name,cost,f; ...] runs the jobs f (), the costliest first,  *)
(* and returns the results in the order of the list. It prints a line for    *)
(* each job with its time (wall clock), from which costs can be updated, and *)
(* one for all of them. A job that fails is reported and the others go on;   *)
(* par_run_jobs fails at the end if one did. For example, a session that     *)
(* loads many independent proof files can run each of them as a job.         *)
(* ------------------------------------------------------------------------- *)

(* The clock is the backend's: CPU time for the serial one, which needs only *)
(* the standard library, and the wall clock for the parallel one.            *)

let par_run_jobs (jobs : (string * float * (unit -> 'a)) list) : 'a list =
  let clock = (!backend).par_backend_clock in
  let t0 = clock () in
  let indexed = zip (0--(length jobs - 1)) jobs in
  let sorted = List.stable_sort (fun (_,(_,a,_)) (_,(_,b,_)) -> compare b a)
                                indexed in
  Printf.printf "par: %d jobs on %d domain(s)\n%!"
    (length jobs) (par_domains ());
  let futures =
    map (fun (i,(name,_,f)) ->
           i,par_spawn (fun () ->
             let s = clock () in
             let r = f () in
             let e = clock () in
             Printf.printf "par: job %s: %.1f s (%.1f-%.1f s)\n%!" name
               (e -. s) (s -. t0) (e -. t0);
             r)) sorted in
  let results = map (fun (i,fu) ->
      i,(try Value (par_await fu) with e ->
           let name,_,_ = el i jobs in
           Printf.printf "par: job %s FAILED: %s\n%!"
             name (Printexc.to_string e);
           Raised (e, Printexc.get_raw_backtrace ()))) futures in
  Printf.printf "par: all jobs: %.1f s\n%!" (clock () -. t0);
  let failed = filter (fun (_,r) -> match r with
                                      Raised _ -> true
                                    | Value _ -> false) results in
  if failed <> [] then
    failwith (Printf.sprintf "par_run_jobs: %d job(s) failed" (length failed))
  else map (fun i -> outcome_value (assoc i results))
           (0--(length jobs - 1));;

end;;

include Par;;
