(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the loops that clang 23 -O3 has inlined into               *)
(* mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy,                     *)
(* instantiated for its labels (see inline_rl.ml for the generators): the    *)
(* products of the entries of the matrix by the polynomials of the vector    *)
(* (the first into t, the others into the polynomial cur of the structure),  *)
(* the sums into t as the straight-line code that the function takes when    *)
(* the two do not overlap, and the reduction of t.                           *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_rl.ml";;

let RL65_FN = "mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy";;
let RL65_MC = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc";;

let RL65_PWM_OF (head,regs) =
  let l = RL65_FN ^ "_" ^ head and e = RL65_FN ^ "_" ^ head ^ "_exit" in
  RL_PWM1_LOOP RL65_MC (INLINE_LOOP_EXEC l e) l e regs;;

let RL65_PWM1 = RL65_PWM_OF ("loop1",["X19";"X21";"X8";"X24";"X9";"X10";"X11"]);;
let RL65_PWM2 = RL65_PWM_OF ("loop2",["X20";"X9";"X8";"X24";"X10";"X11";"X12"]);;
let RL65_PWM3 = RL65_PWM_OF ("loop4",["X20";"X9";"X8";"X24";"X10";"X11";"X12"]);;
let RL65_PWM4 = RL65_PWM_OF ("loop6",["X20";"X9";"X8";"X24";"X10";"X11";"X12"]);;
let RL65_PWM5 = RL65_PWM_OF ("loop8",["X20";"X9";"X8";"X24";"X10";"X11";"X12"]);;

(* the sums: from the instruction after the scalar loop to the join *)

let RL65_VADD_OF (after,join) =
  let st = layout(RL65_FN ^ "_" ^ after) + 4
  and sp = layout(RL65_FN ^ "_" ^ join) in
  RL_VADD_PROVE RL65_MC
   (INLINE_LOOP_EXEC (string_of_int st) (string_of_int sp))
   (string_of_int st) (string_of_int sp) ((sp - st) / 4);;

let RL65_ADD1 = RL65_VADD_OF ("loop3_exit","join1");;
let RL65_ADD2 = RL65_VADD_OF ("loop5_exit","join2");;
let RL65_ADD3 = RL65_VADD_OF ("loop7_exit","join3");;
let RL65_ADD4 = RL65_VADD_OF ("loop9_exit","join4");;

let RL65_RED =
  let l = RL65_FN ^ "_loop10" and e = RL65_FN ^ "_loop10_exit" in
  INLINE_REDUCE_LOOP "21" RL65_MC (INLINE_LOOP_EXEC l e) l e 0
   ["Q2";"Q3";"X8";"X9";"Q4";"Q0";"Q5";"Q1"];;
