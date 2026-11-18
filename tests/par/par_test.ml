(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tests of common/par.ml, with either backend. From the repository root:    *)
(*                                                                           *)
(*   serial:    loadt "tests/par/par_test.ml";;                              *)
(*   parallel:  loadt "common/par_domains.ml";; (S2N_PAR_DOMAINS=8)          *)
(*              loadt "tests/par/par_test.ml";;                              *)
(*                                                                           *)
(* It prints "par_test: all passed" or fails.                                *)
(* ========================================================================= *)

needs "common/par.ml";;

let par_test_failures = ref ([]:string list);;

let par_check name cond =
  if not cond then
   (par_locked (fun () -> par_test_failures := name :: !par_test_failures);
    Printf.printf "par_test: FAILED: %s\n%!" name);;

(* map f l, with the calls of f spawned and then awaited in order.          *)

let par_map f l = map par_await (map (fun x -> par_spawn (fun () -> f x)) l);;

(* The results keep the order, also when nested.                             *)

let () =
  let l = 1--200 in
  par_check "par_map order"
    (par_map (fun n -> n * n) l = map (fun n -> n * n) l);
  let nested =
    par_map (fun i -> par_map (fun j -> i * 100 + j) (1--20)) (1--20) in
  par_check "nested par_map"
    (nested = map (fun i -> map (fun j -> i * 100 + j) (1--20)) (1--20));;

(* An exception of a computation is raised by par_await, so par_map raises   *)
(* the first in the order of the list.                                       *)

let () =
  let f = par_spawn (fun () -> failwith "boom") in
  par_check "exception at await"
    (try par_await f; false with Failure "boom" -> true);
  par_check "par_map exception"
    (try ignore(par_map (fun n -> if n = 3 || n = 7
                                  then failwith (string_of_int n) else n)
                        (1--10)); false
     with Failure "3" -> true);;

(* par_counter gives distinct numbers on all domains.                        *)

let () =
  let c = par_counter () in
  let ns = flat (par_map (fun _ -> map (fun _ -> c ()) (1--500)) (1--16)) in
  par_check "par_counter distinct" (length (setify ns) = 8000);;

(* par_local_ref: a task starts with the value of the spawning domain.       *)

let par_test_cell = par_local_ref (fun () -> 0);;

let () =
  par_test_cell () := 42;
  let vs = par_map (fun _ -> !(par_test_cell ())) (1--16) in
  par_check "par_local_ref inherited" (forall (fun v -> v = 42) vs);
  let ws =
    par_map (fun k -> par_test_cell () := k; !(par_test_cell ())) (1--16) in
  par_check "par_local_ref per task" (ws = 1--16);
  par_check "par_local_ref restored" (!(par_test_cell ()) = 42);;

(* Proofs at the same time with prove_async.                                 *)

let () =
  let goals = [`!x y z. x <= y /\ y <= z ==> x <= z + 0`,
               MESON_TAC[LE_TRANS; ADD_CLAUSES];
               `!a b. (a + b) * (a + b) = a * a + 2 * a * b + b * b`,
               ARITH_TAC;
               `!n. n + SUC m = SUC (n + m)`, ARITH_TAC] in
  let ths = map par_await (map prove_async (flat (replicate goals 20))) in
  par_check "prove_async" (map concl ths = map fst (flat (replicate goals 20)));
  par_check "prove_async failure"
    (try ignore (par_await (prove_async (`1 = 2`, ARITH_TAC))); false
     with Failure _ -> true);;

(* PAR_THENL gives the theorems of THENL.                                    *)

let () =
  let g = `!n. (n = 0 \/ ~(n = 0)) /\ n + 0 = n /\ 0 + n = n` in
  let th1 = prove(g, GEN_TAC THEN PAR_THENL (REPEAT CONJ_TAC)
                       [MESON_TAC[]; ARITH_TAC; ARITH_TAC]) in
  par_check "PAR_THENL" (concl th1 = g);
  let th2 = prove(`!n. n < 5 \/ 5 <= n`,
                  GEN_TAC THEN
                  PAR_THENL (ASM_CASES_TAC `n < 5`) [ARITH_TAC; ARITH_TAC]) in
  par_check "PAR_THENL cases" (concl th2 = `!n. n < 5 \/ 5 <= n`);
  let th3 = prove(`(1 = 1) /\ (2 = 2) /\ (3 = 3)`,
                  PAR_THENL (REPEAT CONJ_TAC) (replicate REFL_TAC 3)) in
  par_check "PAR_THENL conjuncts"
    (concl th3 = `(1 = 1) /\ (2 = 2) /\ (3 = 3)`);;

(* Metavariables: each branch instantiates its own; the result is closed.    *)

let () =
  let g = `?x y. x = 1 /\ y = 2` in
  let th = prove(g, META_EXISTS_TAC THEN META_EXISTS_TAC THEN
                    PAR_THENL CONJ_TAC
                     [UNIFY_ACCEPT_TAC [`x:num`] (REFL `1`);
                      UNIFY_ACCEPT_TAC [`y:num`] (REFL `2`)]) in
  par_check "PAR_THENL with metavariables" (concl th = g);
  par_check "PAR_THENL same instantiation accepted"
    (can prove(`?x. x = 1 /\ x = 1`,
               META_EXISTS_TAC THEN
               PAR_THENL CONJ_TAC
                [UNIFY_ACCEPT_TAC [`x:num`] (REFL `1`);
                 UNIFY_ACCEPT_TAC [`x:num`] (REFL `1`)]));
  par_check "PAR_THENL different instantiations rejected"
    (try ignore(TAC_PROOF(([],`?x. x = 1 /\ x = 2`),
                      META_EXISTS_TAC THEN
                      PAR_THENL CONJ_TAC
                       [UNIFY_ACCEPT_TAC [`x:num`] (REFL `1`);
                        UNIFY_ACCEPT_TAC [`x:num`] (REFL `2`)])); false
     with Failure s ->
       s = "PAR_THENL: branches instantiate the same metavariable");
  par_check "PAR_THENL metavariables of each branch"
    (can prove(`(?y. y = 1) /\ (?y. y = 2)`,
               PAR_THENL CONJ_TAC
                [META_EXISTS_TAC THEN UNIFY_ACCEPT_TAC [`y:num`] (REFL `1`);
                 META_EXISTS_TAC THEN
                 UNIFY_ACCEPT_TAC [`y:num`] (REFL `2`)]));;

(* A branch that fails makes PAR_THENL fail.                                 *)

let () =
  par_check "PAR_THENL failure"
    (not (can prove (`(1 = 1) /\ (1 = 2)`,
                     PAR_THENL CONJ_TAC [REFL_TAC; REFL_TAC])));;

(* Many proofs of the same tactics at once (MESON keeps state per call).     *)

let () =
  let n = 400 in
  let ths = par_map (fun i -> prove(`!x y z. x <= y /\ y <= z ==> x <= z + 0`,
                                    MESON_TAC[LE_TRANS; ADD_CLAUSES]))
                    (1--n) in
  par_check "stress MESON" (length ths = n);
  let vs = par_map (fun _ -> fst(dest_var(genvar `:num`))) (1--n) in
  par_check "genvar distinct" (length (setify vs) = n);;

(* A future can be awaited more than once.                                   *)

let () =
  let fu = par_spawn (fun () -> 6 * 7) in
  par_check "par_await twice" (par_await fu = 42 && par_await fu = 42);;

(* The backend cannot change once there is state that belongs to it.         *)

let () =
  let c = par_counter () in
  ignore (c ());
  let none _ = failwith "par_test: backend none" in
  par_check "par_set_backend after par_counter"
    (try par_set_backend
           { par_backend_domains = 1;
             par_backend_spawn = none; par_backend_local = none;
             par_backend_locked = none; par_backend_counter = none;
             par_backend_clock = none };
         false
     with Failure _ -> true);
  par_check "backend unchanged" (par_await (par_spawn (fun () -> 1)) = 1);;

let () =
  if !par_test_failures = [] then Printf.printf "par_test: all passed\n%!"
  else failwith ("par_test: " ^ string_of_int (length !par_test_failures) ^
                 " failed");;
