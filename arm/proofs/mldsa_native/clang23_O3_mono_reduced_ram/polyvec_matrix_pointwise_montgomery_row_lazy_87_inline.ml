(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the loops that clang 23 -O3 has inlined into               *)
(* mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy,                     *)
(* instantiated for its labels (see inline_rl.ml for the generators): the    *)
(* products of the entries of the matrix by the polynomials of the vector    *)
(* (the first into t, the others into the polynomial cur of the structure),  *)
(* the sums into t as the straight-line code that the function takes when    *)
(* the two do not overlap, and the reduction of t.                           *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_rl.ml";;

let RL87_FN = "mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy";;
let RL87_MC = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc";;

let RL87_PWM_OF (head,regs) =
  let l = RL87_FN ^ "_" ^ head and e = RL87_FN ^ "_" ^ head ^ "_exit" in
  RL_PWM1_LOOP RL87_MC (INLINE_LOOP_EXEC l e) l e regs;;

let RL87_PWM1 = RL87_PWM_OF ("loop1",["X19";"X21";"X8";"X24";"X9";"X10";"X11"]);;
let RL87_PWM2 = RL87_PWM_OF ("loop2",["X20";"X9";"X8";"X24";"X10";"X11";"X12"]);;
let RL87_PWM3 = RL87_PWM_OF ("loop4",["X20";"X9";"X8";"X24";"X10";"X11";"X12"]);;
let RL87_PWM4 = RL87_PWM_OF ("loop6",["X20";"X9";"X8";"X24";"X10";"X11";"X12"]);;
let RL87_PWM5 = RL87_PWM_OF ("loop8",["X20";"X9";"X8";"X24";"X10";"X11";"X12"]);;
let RL87_PWM6 = RL87_PWM_OF ("loop10",["X20";"X9";"X8";"X24";"X10";"X11";"X12"]);;
let RL87_PWM7 = RL87_PWM_OF ("loop12",["X20";"X9";"X8";"X24";"X10";"X11";"X12"]);;

(* the sums: from the instruction after the scalar loop to the join *)

let RL87_VADD_OF (after,join) =
  let st = layout(RL87_FN ^ "_" ^ after) + 4
  and sp = layout(RL87_FN ^ "_" ^ join) in
  RL_VADD_PROVE RL87_MC
   (INLINE_LOOP_EXEC (string_of_int st) (string_of_int sp))
   (string_of_int st) (string_of_int sp) ((sp - st) / 4);;

let RL87_ADD1 = RL87_VADD_OF ("loop3_exit","join1");;
let RL87_ADD2 = RL87_VADD_OF ("loop5_exit","join2");;
let RL87_ADD3 = RL87_VADD_OF ("loop7_exit","join3");;
let RL87_ADD4 = RL87_VADD_OF ("loop9_exit","join4");;
let RL87_ADD5 = RL87_VADD_OF ("loop11_exit","join5");;
let RL87_ADD6 = RL87_VADD_OF ("loop13_exit","join6");;

let RL87_RED =
  let l = RL87_FN ^ "_loop14" and e = RL87_FN ^ "_loop14_exit" in
  INLINE_REDUCE_LOOP "21" RL87_MC (INLINE_LOOP_EXEC l e) l e 0
   ["Q2";"Q3";"X8";"X9";"Q4";"Q0";"Q5";"Q1"];;
