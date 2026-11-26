(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the loops and regions that clang 23 -O3 has inlined into   *)
(* mldsa87_verify_internal, instantiated for its labels (see inline_sign.ml, *)
(* inline_verify65.ml and inline_hintsk.ml for the generators). The frame:   *)
(*                                                                           *)
(*   the matrix, the Keccak state of tr   rsp0 + 256                         *)
(*   rho rsp0 + 1280, c~ rsp0 + 1344, mu rsp0 + 1408                         *)
(*   t1, hints rsp0 + 1536, w rsp0 + 2560, w1 (packed) and tr rsp0 + 3584    *)
(*   cp (NTT of c) rsp0 + 4608, z rsp0 + 5632 + 1024 k, k = 0..6             *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_hintsk.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_verify87.ml";;

let VI87_UNPACKZ_LOOPS = map
  (fun (l,x,rcx0,sc) -> PROVE_UNPACKZ19 "mldsa87_verify_internal" l x 5632 rcx0 sc)
  ["loop1","loop1_exit",0,"R8"; "loop2","loop2_exit",128,"R8";
   "loop3","loop3_exit",256,"R8"; "loop4","loop4_exit",384,"R8";
   "loop5","loop5_exit",512,"R8"; "loop6","loop6_exit",640,"R8";
   "loop7","loop7_exit",768,"RDI"];;

let VI87_UNPACKT1_LOOP =
  PROVE_UNPACKT1 "mldsa87_verify_internal" "loop8" "loop8_exit" 1536;;

let VI87_SHIFTL =
  PROVE_SHIFTL "mldsa87_verify_internal" "loop8_exit" 1536;;

let VI87_PWM_LOOP =
  PROVE_PWMLOOP "mldsa87_verify_internal" "loop9" "loop9_exit" 1532 4604;;

let VI87_SUB_LOOP =
  PROVE_SUBLOOP "mldsa87_verify_internal" "loop10" "loop10_exit" 2512 1488;;

let VI87_REDUCE_LOOP =
  PROVE_REDLOOP "mldsa87_verify_internal" "loop11" "loop11_exit" 2544;;

let VI87_CADDQ_LOOP =
  PROVE_CADDQ "mldsa87_verify_internal" "loop12" "loop12_exit" 2560 11;;

let VI87_USEHINT_LOOP =
  PROVE_USEHINT32 "mldsa87_verify_internal" "join12" 0x20e0 2560 1536 "join9";;

let VI87_PACKW1_LOOP =
  PROVE_W1PACK32 "mldsa87_verify_internal" "loop14" 0x20e0 "loop14_exit" 2560;;

let HK87 =
  {hk_fn = "mldsa87_verify_internal"; hk_om = 75; hk_k = 8; hk_sh = 4544;
   hk_cb = 1536; hk_fr = 2560; hk_sigslot = 248; hk_entry = "loop12_exit";
   hk_l1 = 0x21a0; hk_l1hd = "join15"; hk_l2 = "loop13"; hk_end = "join12";
   hk_sreg = "R14"; hk_ireg = "RBX";
   hk_frame = "read (memory :> bytes64 (word_add rsp0 (word 24))) s = t1p /\\
               read RBX s = word i";
   hk_inv_c = "";
   hk_post = "read RAX s = word 0 /\\ read R8 s = sig /\\ read R13 s = word i /\\
              read R14 s = word_add rsp0 (word 5632) /\\ read RBX s = t1p";
   hk_mc = "RSP; RBX; R13; R14";
   hk_memc = "memory :> bytes(word_add rsp0 (word 24),8); ";
   hk_c5 = 0x2009; hk_c5name = "mldsa87_verify_internal_const5";
   hk_n1 = 4; hk_n2 = 9; hk_n2a = 2};;

let VI87_HINTS = PROVE_HK HK87;;

let VI87_TR = PROVE_TR87 "mldsa87_verify_internal";;

let VI87_CLEANUP =
  PROVE_CL "mldsa87_verify_internal" 12832
   [0x540;0x550;0x560;0x570;0x580;0x590;0x5a0;0x5b0;0x5c0;0x5d0;0x5e0;0x5f0];;

let VI87_C2 = PROVE_C2_87 "mldsa87_verify_internal";;

let VI87_CMP = PROVE_CMP87 "mldsa87_verify_internal";;
