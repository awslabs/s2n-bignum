(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the loops and regions that clang 23 -O3 has inlined into   *)
(* mldsa65_verify_internal, instantiated for its labels (see inline_sign.ml  *)
(* and inline_verify65.ml for the generators). The frame is that of          *)
(* mldsa44_verify_internal moved by 64 bytes for c~, which has 48 bytes:     *)
(*                                                                           *)
(*   z, y vector   rsp0 + 5152 + 1024 k, k = 0..4  (unpacking, 5 loops)      *)
(*   t1 (unpacked) rsp0 + 1312,  w (A z row, shifted, reduced)  rsp0 + 2336  *)
(*   cp (NTT of c) rsp0 + 3360                                               *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_hintsk.ml";;

let VI65_UNPACKZ_LOOPS = map
  (fun (l,x,rcx0,sc) -> PROVE_UNPACKZ19 "mldsa65_verify_internal" l x 5152 rcx0 sc)
  ["loop1","loop1_exit",0,"R8"; "loop2","loop2_exit",128,"R8";
   "loop3","loop3_exit",256,"R8"; "loop4","loop4_exit",384,"R8";
   "loop5","loop5_exit",512,"RDI"];;

let VI65_UNPACKT1_LOOP =
  PROVE_UNPACKT1 "mldsa65_verify_internal" "loop6" "loop6_exit" 1312;;

let VI65_SHIFTL =
  PROVE_SHIFTL "mldsa65_verify_internal" "loop6_exit" 1312;;

let VI65_PWM_LOOP =
  PROVE_PWMLOOP "mldsa65_verify_internal" "loop7" "loop7_exit" 1308 3356;;

let VI65_SUB_LOOP =
  PROVE_SUBLOOP "mldsa65_verify_internal" "loop8" "loop8_exit" 2288 1264;;

let VI65_REDUCE_LOOP =
  PROVE_REDLOOP "mldsa65_verify_internal" "loop9" "loop9_exit" 2320;;

let VI65_CADDQ_LOOP =
  PROVE_CADDQ "mldsa65_verify_internal" "loop10" "loop10_exit" 2336 11;;

let VI65_USEHINT_LOOP =
  PROVE_USEHINT32 "mldsa65_verify_internal" "join12" 0x1a50 2336 1312 "join9";;

let VI65_PACKW1_LOOP =
  PROVE_W1PACK32 "mldsa65_verify_internal" "loop12" 0x1a50 "loop12_exit" 2336;;

let HK65 =
  {hk_fn = "mldsa65_verify_internal"; hk_om = 55; hk_k = 6; hk_sh = 3248;
   hk_cb = 1312; hk_fr = 2336; hk_sigslot = 40; hk_entry = "loop10_exit";
   hk_l1 = 0x1b00; hk_l1hd = "join14"; hk_l2 = "loop11"; hk_end = "join12";
   hk_sreg = "RBX"; hk_ireg = "R12";
   hk_frame = "read R14 s = t1p /\\ read R12 s = word i";
   hk_inv_c = "read RBX s = t1p /\\ ";
   hk_post = "read RAX s = word 0 /\\ read R8 s = sig /\\ read R13 s = word i /\\
              read R14 s = word_add rsp0 (word 5152) /\\
              read R12 s = word 0x0380200100000000 /\\ read RBX s = t1p";
   hk_mc = "RSP; RBX; R12; R13; R14"; hk_memc = "";
   hk_c5 = 0x1965; hk_c5name = "mldsa65_verify_internal_const5";
   hk_n1 = 4; hk_n2 = 9; hk_n2a = 3};;

let VI65_HINTS = PROVE_HK HK65;;

let VI65_CMP = PROVE_CMP65 "mldsa65_verify_internal";;

let VI65_TR = PROVE_TR65 "mldsa65_verify_internal";;

let VI65_CLEANUP =
  PROVE_CL "mldsa65_verify_internal" 10304
   [0x460;0x470;0x480;0x4a0;0x4b0;0x4c0;0x4e0;0x4f0;0x500;0x510];;
