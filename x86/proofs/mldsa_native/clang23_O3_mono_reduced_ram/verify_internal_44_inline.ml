(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the loops and regions that clang 23 -O3 has inlined into   *)
(* mldsa44_verify_internal, instantiated for its labels (see inline_sign.ml  *)
(* for the generators and the form of the lemmas). Each is stated from the   *)
(* head of the code to its exit, with the frame at fixed offsets from the    *)
(* value rsp0 of RSP after the prologue:                                     *)
(*                                                                           *)
(*   z, y vector   rsp0 + 4320 + 1024 k, k = 0..3  (unpacking, 4 loops)      *)
(*   t1 (unpacked) rsp0 + 1248,  w (A z row, shifted, reduced)  rsp0 + 2272  *)
(*   cp (NTT of c) rsp0 + 3296                                               *)
(*                                                                           *)
(* The regions of inline_verify.ml follow: the packing of w1', the           *)
(* comparison of c~, the zeroing at the end, the absorption of the public    *)
(* key and the unpacking of the hints.                                       *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_verify.ml";;

let VI44_UNPACKZ_LOOPS = map
  (fun (l,x,rcx0) -> PROVE_UNPACKZ17 "mldsa44_verify_internal" l x rcx0)
  ["loop1","loop1_exit",12; "loop2","loop2_exit",1036;
   "loop3","loop3_exit",2060; "loop4","loop4_exit",3084];;

let VI44_UNPACKT1_LOOP =
  PROVE_UNPACKT1 "mldsa44_verify_internal" "loop5" "loop5_exit" 1248;;

let VI44_SHIFTL =
  PROVE_SHIFTL "mldsa44_verify_internal" "loop5_exit" 1248;;

let VI44_PWM_LOOP =
  PROVE_PWMLOOP "mldsa44_verify_internal" "loop6" "loop6_exit" 1244 3292;;

let VI44_SUB_LOOP =
  PROVE_SUBLOOP "mldsa44_verify_internal" "loop7" "loop7_exit" 2224 1200;;

let VI44_REDUCE_LOOP =
  PROVE_REDLOOP "mldsa44_verify_internal" "loop8" "loop8_exit" 2256;;

let VI44_CADDQ_LOOP =
  PROVE_CADDQ "mldsa44_verify_internal" "loop9" "loop9_exit" 2272 11;;

let VI44_USEHINT_LOOP =
  PROVE_USEHINT88 "mldsa44_verify_internal" "join11" "join12" 2272 1248 "join9";;

let VI44_PACKW1_LOOP =
  PROVE_PACKW1 "mldsa44_verify_internal" "loop11" "loop11_exit";;

let VI44_HINTS = PROVE_HINTS44 "mldsa44_verify_internal";;

let VI44_CMP = PROVE_CMP44 "mldsa44_verify_internal";;

let VI44_TR = PROVE_TR44 "mldsa44_verify_internal";;

let VI44_CLEANUP =
  PROVE_CL "mldsa44_verify_internal" 9216
   [0x40;0x50;0x60;0x70;0x4a0;0x4b0;0x4c0;0x4d0];;
