(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the loops that clang 23 -O3 has inlined into               *)
(* mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy,                                                                       *)
(* instantiated for its labels (see inline_rl.ml for the generators): the    *)
(* products of the entries of the matrix by the polynomials of the vector,   *)
(* in t at RBX (loop 1) or in the structure at R14, the sums into t (the     *)
(* SSE loops, as the code takes them when the two do not overlap), and the   *)
(* reduction of t (the last loop).                                           *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_rl.ml";;

let RL87_FN = "mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy";;

let RL87_PWM1 = PROVE_PWMPTR RL87_FN "loop1" "loop1_exit" "RBX" 0 1;;
let RL87_PWM2 = PROVE_PWMPTR RL87_FN "loop2" "loop2_exit" "R14" 1024 0;;
let RL87_PWM3 = PROVE_PWMPTR RL87_FN "loop5" "loop5_exit" "R14" 2048 0;;
let RL87_PWM4 = PROVE_PWMPTR RL87_FN "loop8" "loop8_exit" "R14" 3072 0;;
let RL87_PWM5 = PROVE_PWMPTR RL87_FN "loop11" "loop11_exit" "R14" 4096 0;;
let RL87_PWM6 = PROVE_PWMPTR RL87_FN "loop14" "loop14_exit" "R14" 5120 0;;
let RL87_PWM7 = PROVE_PWMPTR RL87_FN "loop17" "loop17_exit" "R14" 6144 0;;

let RL87_ADD2 = PROVE_SSEADD RL87_FN "loop4" "loop4_exit" "RBX" "R14";;
let RL87_ADD3 = PROVE_SSEADD RL87_FN "loop7" "loop7_exit" "RBX" "R14";;
let RL87_ADD4 = PROVE_SSEADD RL87_FN "loop10" "loop10_exit" "RBX" "R14";;
let RL87_ADD5 = PROVE_SSEADD RL87_FN "loop13" "loop13_exit" "RBX" "R14";;
let RL87_ADD6 = PROVE_SSEADD RL87_FN "loop16" "loop16_exit" "RBX" "R14";;
let RL87_ADD7 = PROVE_SSEADD RL87_FN "loop19" "loop19_exit" "RBX" "R14";;

let RL87_RED = PROVE_REDPTR RL87_FN "loop20" "loop20_exit" "RBX";;
