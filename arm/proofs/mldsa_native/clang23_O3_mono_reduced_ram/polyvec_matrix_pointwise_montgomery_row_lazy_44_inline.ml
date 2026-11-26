(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the loops that clang 23 -O3 has inlined into               *)
(* mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy, instantiated for    *)
(* its labels (see inline_rl.ml for the generators): the products of the     *)
(* entries of the matrix by the polynomials of the vector (the first into t, *)
(* the others into the polynomial cur of the structure), the sums into t as  *)
(* the straight-line code that the function takes when the two do not        *)
(* overlap, and the reduction of t.                                          *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_rl.ml";;

let RL44_FN = "mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy";;
let RL44_MC = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc";;

let RL44_PWM_OF (head,regs) =
  let l = RL44_FN ^ "_" ^ head and e = RL44_FN ^ "_" ^ head ^ "_exit" in
  RL_PWM1_LOOP RL44_MC (INLINE_LOOP_EXEC l e) l e regs;;

let RL44_PWM1 = RL44_PWM_OF ("loop1",["X19";"X21";"X8";"X24";"X9";"X10";"X11"]);;
let RL44_PWM2 = RL44_PWM_OF ("loop2",["X20";"X9";"X8";"X24";"X10";"X11";"X12"]);;
let RL44_PWM3 = RL44_PWM_OF ("loop4",["X20";"X9";"X8";"X24";"X10";"X11";"X12"]);;
let RL44_PWM4 = RL44_PWM_OF ("loop6",["X20";"X9";"X8";"X24";"X10";"X11";"X12"]);;

(* the sums: from the instruction after the scalar loop to the join *)

let RL44_VADD_OF (after,join) =
  let st = layout(RL44_FN ^ "_" ^ after) + 4
  and sp = layout(RL44_FN ^ "_" ^ join) in
  RL_VADD_PROVE RL44_MC
   (INLINE_LOOP_EXEC (string_of_int st) (string_of_int sp))
   (string_of_int st) (string_of_int sp) ((sp - st) / 4);;

let RL44_ADD1 = RL44_VADD_OF ("loop3_exit","join1");;
let RL44_ADD2 = RL44_VADD_OF ("loop5_exit","join2");;
let RL44_ADD3 = RL44_VADD_OF ("loop7_exit","join3");;

let RL44_RED =
  let l = RL44_FN ^ "_loop8" and e = RL44_FN ^ "_loop8_exit" in
  INLINE_REDUCE_LOOP "21" RL44_MC (INLINE_LOOP_EXEC l e) l e 0
   ["Q2";"Q3";"X8";"X9";"Q4";"Q0";"Q5";"Q1"];;
