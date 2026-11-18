(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The parallel backend of common/par.ml: OCaml 5 domains.                   *)
(*                                                                           *)
(* With this backend, the computations that common/par.ml spawns (the jobs   *)
(* of par_run_jobs, the branches of PAR_THENL, prove_async) run on several   *)
(* domains of one process. It needs only OCaml 5's standard library and the  *)
(* Unix library, but it relies on the HOL Light that it runs with, as stated *)
(* below; a build uses it only when asked to.                                *)
(*                                                                           *)
(* Enabling it. In s2n-bignum's arm or x86 directory, with a HOL Light built *)
(* for OCaml 5 with HOLLIGHT_USE_MODULE=1 that meets the requirements below  *)
(* (jrh13/hol-light PR 214 does):                                            *)
(*                                                                           *)
(*   make clean                                                              *)
(*   make HOLDIR=<hol-light> HOL_PAR=1 <target>.native                       *)
(*   S2N_PAR_DOMAINS=12 make HOLDIR=<hol-light> HOL_PAR=1 <target>.correct   *)
(*                                                                           *)
(* HOL_PAR=1 makes tools/build-proof.sh load this file first, before any     *)
(* other file makes state that proofs share. S2N_PAR_DOMAINS (default 1) is  *)
(* the number of domains, the calling one included; with 1, a spawned        *)
(* computation runs at once, as with the serial backend. The binaries do not *)
(* record the backend, hence make clean when changing HOL_PAR or HOLDIR.     *)
(* Every minor collection stops all domains, so each domain gets a minor     *)
(* heap of S2N_PAR_MINOR_HEAP words (default 32M words, 256 MB) unless       *)
(* OCAMLRUNPARAM sets one with s=: with the default of 256k words, proofs on *)
(* 8 domains each took about 3 times as long as on one.                      *)
(*                                                                           *)
(* What HOL Light must guarantee. HOL_PAR=1 asserts that the HOL Light used  *)
(* meets these requirements; nothing checks them. While several domains of   *)
(* one process call HOL Light functions at the same time, under the          *)
(* conditions below:                                                         *)
(*                                                                           *)
(* - (K) Every value of type thm made on any domain is a theorem, given the  *)
(*   axioms and definitions accepted. The kernel's tables (constants, types, *)
(*   axioms, definitions) change in single atomic steps: two definitions of  *)
(*   one name cannot both be accepted with different meanings.               *)
(* - (C) The functions of the core (inference rules, conversions, tactics,   *)
(*   rewriting and simplification, MESON, METIS and the other first-order    *)
(*   provers, the arithmetic decision procedures, Compute, the parser, the   *)
(*   type checker, the printer) give on any domain the results that they     *)
(*   give on one, for the same arguments and the same global settings. The   *)
(*   state that they keep from call to call (the counters of genvar and of   *)
(*   type-variable invention, the tables of the provers, the restriction of  *)
(*   Compute.EVAL_CONV, ...) is per domain or atomic, and fresh names are    *)
(*   distinct over all domains.                                              *)
(* - (D) The definitional rules (new_definition, define,                     *)
(*   new_type_definition, new_specification, new_inductive_definition,       *)
(*   define_type and the like, new_constant, new_type, new_axiom) may be     *)
(*   called on any domain; they take effect one at a time, and a definition  *)
(*   is visible to all domains once made.                                    *)
(* - (P) Printing on a domain uses its own Format formatter and settings;    *)
(*   the output of several domains may interleave, but printing does not     *)
(*   fail.                                                                   *)
(* - (L) (C) and (D) hold for the Library files that the proofs load (words, *)
(*   bitmatch, bitsize, iter, rstc, pocklington, prime, integer, floor,      *)
(*   isum, components, bdd, records, and ringtheory with the files it loads  *)
(*   for the FIPS 203 and 204 specifications), as far as their functions are *)
(*   called while proofs run; a cache in a reference to a list, where a race *)
(*   can only lose an entry, is fine.                                        *)
(*                                                                           *)
(* Only (K) bears on soundness. Every theorem comes from the kernel, so if   *)
(* (C), (D), (P) or (L) failed, proofs could fail, but what they prove would *)
(* still be theorems. A failure of (C) could change which statement a string *)
(* parses to, but s2n-bignum parses the statements of the theorems that it   *)
(* finally proves before it spawns any computation: a session that runs many *)
(* proof files as jobs loads their spec files first. HOL Light without such  *)
(* changes does not meet (K): races in its kernel tables can accept          *)
(* conflicting definitions.                                                  *)
(*                                                                           *)
(* What s2n-bignum does in return. While computations run on other domains,  *)
(* the parser, the interface, the overloads, the infixes, the type           *)
(* abbreviations and the default rewrites and conversions do not change      *)
(* (files that change them are loaded before computations are spawned or     *)
(* after they end); definitions made in a computation are used only by it;   *)
(* the goal stack is not used; one thread runs per domain; and the state     *)
(* that s2n-bignum's own tools share between calls goes through par_local,   *)
(* par_local_ref, par_locked and par_counter of common/par.ml.               *)
(*                                                                           *)
(* Checking. loadt "common/par_domains.ml" and then loadt                    *)
(* "tests/par/par_test.ml" (with S2N_PAR_DOMAINS=8) test this backend. The   *)
(* link files of mlkem-native and mldsa-native, which run all the proofs of  *)
(* a build in one session, fail unless every contract of the build is proved *)
(* and closed.                                                               *)
(*                                                                           *)
(* How it works. S2N_PAR_DOMAINS - 1 worker domains take spawned             *)
(* computations from one queue. A domain that waits for the result of a      *)
(* computation that no domain has started runs it itself, and otherwise runs *)
(* other queued computations while it waits, so that computations can spawn  *)
(* and wait for others at any depth (a case split inside a job of            *)
(* par_run_jobs) without deadlock.                                           *)
(* ========================================================================= *)

needs "common/par.ml";;

(* ------------------------------------------------------------------------- *)
(* The state of par.ml: one lock for par_locked, atomic counters, and cells  *)
(* per domain in an atomic list from domain ids to values (a domain adds its *)
(* own entry, once, so reading needs no lock).                               *)
(* ------------------------------------------------------------------------- *)

let par_domains_lock = Mutex.create ();;

let par_domains_locked (f : unit -> 'a) : 'a =
  Mutex.lock par_domains_lock;
  let r = try f () with e -> (Mutex.unlock par_domains_lock; raise e) in
  Mutex.unlock par_domains_lock; r;;

let par_domains_counter () : unit -> int =
  let c = Atomic.make 0 in
  fun () -> Atomic.fetch_and_add c 1;;

let par_domains_local (f : unit -> 'a) : unit -> 'a =
  let cells = Atomic.make ([] : (int * 'a) list) in
  fun () ->
    let id = (Domain.self () :> int) in
    match List.assoc_opt id (Atomic.get cells) with
      Some v -> v
    | None ->
        let v = f () in
        let rec add () =
          let l = Atomic.get cells in
          if Atomic.compare_and_set cells l ((id,v)::l) then v else add () in
        add ();;

let par_domains_count = par_requested_domains ();;

let par_domains_tune_gc () =
  let orp = match Sys.getenv_opt "OCAMLRUNPARAM" with
              Some s -> s | None -> "" in
  let given = List.exists
    (fun opt -> String.length opt >= 2 && String.sub opt 0 2 = "s=")
    (String.split_on_char ',' orp) in
  if not given then
    let w = match Sys.getenv_opt "S2N_PAR_MINOR_HEAP" with
              None -> 32 * 1024 * 1024
            | Some s ->
                try int_of_string (String.trim s) with Failure _ ->
                  failwith ("S2N_PAR_MINOR_HEAP: not a number: " ^ s) in
    if (Gc.get ()).Gc.minor_heap_size <> w then
      Gc.set { (Gc.get ()) with Gc.minor_heap_size = w };;

(* ------------------------------------------------------------------------- *)
(* The queue of computations not yet started, and the workers.               *)
(* ------------------------------------------------------------------------- *)

type par_task = { par_task_run : unit -> unit;
                  par_task_taken : bool Atomic.t };;

let par_queue = (Queue.create () : par_task Queue.t);;
let par_mutex = Mutex.create ();;
let par_cond = Condition.create ();;

(* A computation from the queue that no domain has taken yet, if any; the    *)
(* caller holds par_mutex.                                                   *)

let rec par_pop_locked () =
  match Queue.take_opt par_queue with
    None -> None
  | Some t -> if Atomic.compare_and_set t.par_task_taken false true
              then Some t else par_pop_locked ();;

let par_take () =
  Mutex.lock par_mutex;
  let t = par_pop_locked () in
  Mutex.unlock par_mutex; t;;

(* Each worker uses the Format settings of the domain that started the       *)
(* workers (HOL Light sets max_boxes, for example), and flushes its output   *)
(* after each computation.                                                   *)

let par_worker margin max_indent max_boxes () =
  par_domains_tune_gc ();
  Format.set_margin margin; Format.set_max_indent max_indent;
  Format.set_max_boxes max_boxes;
  let rec loop () =
    Mutex.lock par_mutex;
    let rec next () =
      match par_pop_locked () with
        Some t -> t
      | None -> Condition.wait par_cond par_mutex; next () in
    let t = next () in
    Mutex.unlock par_mutex;
    t.par_task_run ();
    loop () in
  loop ();;

let par_workers_started = Atomic.make false;;

let par_start_workers () =
  if par_domains_count > 1 &&
     Atomic.compare_and_set par_workers_started false true then
   (par_domains_tune_gc ();
    let margin = Format.get_margin () and max_indent = Format.get_max_indent ()
    and max_boxes = Format.get_max_boxes () in
    for _ = 2 to par_domains_count do
      ignore (Domain.spawn (par_worker margin max_indent max_boxes))
    done);;

(* ------------------------------------------------------------------------- *)
(* Spawning and waiting.                                                     *)
(* ------------------------------------------------------------------------- *)

(* par_domains_spawn run queues run and returns wait (see par_backend in     *)
(* common/par.ml). Setting finished (an atomic) after run () returns makes   *)
(* what run wrote visible to a domain that then reads finished.              *)

let par_domains_spawn (run : unit -> unit) : unit -> unit =
  if par_domains_count <= 1 then (run (); fun () -> ())
  else begin
    par_start_workers ();
    let finished = Atomic.make false in
    let task_run () =
      run ();
      Format.print_flush ();
      Atomic.set finished true;
      Mutex.lock par_mutex; Condition.broadcast par_cond;
      Mutex.unlock par_mutex in
    let task = { par_task_run = task_run;
                 par_task_taken = Atomic.make false } in
    Mutex.lock par_mutex; Queue.push task par_queue;
    Condition.broadcast par_cond; Mutex.unlock par_mutex;
    fun () ->
      if Atomic.compare_and_set task.par_task_taken false true then task_run ();
      let rec wait () =
        if not (Atomic.get finished) then
          match par_take () with
            Some t -> t.par_task_run (); wait ()
          | None ->
              Mutex.lock par_mutex;
              if not (Atomic.get finished) && Queue.is_empty par_queue
              then Condition.wait par_cond par_mutex;
              Mutex.unlock par_mutex;
              wait () in
      wait ()
  end;;

(* The clock is the wall clock: CPU time adds up over the domains.           *)

par_set_backend
  { par_backend_domains = par_domains_count;
    par_backend_spawn = par_domains_spawn;
    par_backend_local = par_domains_local;
    par_backend_locked = par_domains_locked;
    par_backend_counter = par_domains_counter;
    par_backend_clock = Unix.gettimeofday };;

Printf.printf "par: %d domain(s)\n%!" par_domains_count;;
