(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The region lemmas of mldsa87_signature_internal (clang 23 -O3 mono        *)
(* reduced-RAM), as signature_internal_44_inline.ml does it for 44: the      *)
(* generators of inline_sign.ml, inline_attempt.ml and inline_verify65.ml,   *)
(* and those of inline_sign6587.ml for the loops whose registers or code     *)
(* differ from 44, by the labels of layout.ml. The buffers are at fixed     *)
(* offsets from the stack pointer rsp0 of the attempt (see the parameters).  *)
(*                                                                           *)
(* The decomposition and the packing of w1 (gamma2 = (q - 1) / 32), the row *)
(* loop that 87 keeps rolled around them, the unpacking of w1 for the hints *)
(* and the inlined H(mu || w1) of the challenge use the generators of       *)
(* inline_sign6587.ml that 44 has no counterpart for (DECOMP32, W1PACK4G,   *)
(* DW1R, W1UNPACK4, C2S).                                                   *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign6587.ml";;

let SI87_FN = "mldsa87_signature_internal";;

(* ------------------------------------------------------------------------- *)
(* The product with the matrix, column j: the sampling of y_j (the pointer   *)
(* to rho'' and kappa at rsp0 + 0xa0 and + 0xa8, G1AV), the entries of       *)
(* column j times its NTT (loops 2, 4, ..., 16 for j > 0, 18 to 25 for j =   *)
(* 0, the constant in RBX) and the sums of the rows (3, 5, ..., 17).        *)
(* ------------------------------------------------------------------------- *)

let SI87_G1A_Y_CFG =
  {ga_fn = SI87_FN; ga_start = "join4"; ga_end = "join7";
   ga_jreg = "R15"; ga_jsave = "bytes32"; ga_jslot = 0x38; ga_inb = 0x1360;
   ga_st = 0xb40; ga_pos = "R15"; ga_rem = "R12"; ga_off = "R13"};;

let SI87_SQZ_Y_CFG =
  {sq_fn = SI87_FN; sq_lo = "join5"; sq_head = "join7"; sq_exit = "join8";
   sq_pos = "R15"; sq_rem = "R12"; sq_off = "R13"; sq_len = "RBX";
   sq_sp = "R14"; sq_st = 0xb40; sq_buf = 0x740};;

let SI87_ZER_Y_CFG =
  {zr_fn = SI87_FN; zr_start = "loop1_exit"; zr_fin = 0x532; zr_st = 0xb40;
   zr_buf = 0x740; zr_inb = 0x1360; zr_breg = "RBX"; zr_post = 6};;

let SI87_G1A_Y = PROVE_G1AV SI87_G1A_Y_CFG 0xa0 true;;
let SI87_SQZ_Y = PROVE_SQZV SI87_SQZ_Y_CFG false;;
let SI87_UZ_Y = PROVE_UNPACKZ19 SI87_FN "loop1" "loop1_exit" 0x340 0 "RDI; R8; R9";;
let SI87_ZER_Y = PROVE_ZER SI87_ZER_Y_CFG;;

let SI87_PWM2 = PROVE_PWMLOOPQ "RBX" SI87_FN "loop2" "loop2_exit" 0xf3c 0x33c 1;;
let SI87_PWM4 = PROVE_PWMLOOPQ "RBX" SI87_FN "loop4" "loop4_exit" 0xf3c 0x33c 1;;
let SI87_PWM6 = PROVE_PWMLOOPQ "RBX" SI87_FN "loop6" "loop6_exit" 0xf3c 0x33c 1;;
let SI87_PWM8 = PROVE_PWMLOOPQ "RBX" SI87_FN "loop8" "loop8_exit" 0xf3c 0x33c 1;;
let SI87_PWM10 = PROVE_PWMLOOPQ "RBX" SI87_FN "loop10" "loop10_exit" 0xf3c 0x33c 1;;
let SI87_PWM12 = PROVE_PWMLOOPQ "RBX" SI87_FN "loop12" "loop12_exit" 0xf3c 0x33c 1;;
let SI87_PWM14 = PROVE_PWMLOOPQ "RBX" SI87_FN "loop14" "loop14_exit" 0xf3c 0x33c 1;;
let SI87_PWM16 = PROVE_PWMLOOPQ "RBX" SI87_FN "loop16" "loop16_exit" 0xf40 0x340 0;;
let SI87_ADD3 = PROVE_ADDLOOPG SI87_FN "loop3" "loop3_exit" 0xf10 0x19f0 12;;
let SI87_ADD5 = PROVE_ADDLOOPG SI87_FN "loop5" "loop5_exit" 0xf10 0x1df0 12;;
let SI87_ADD7 = PROVE_ADDLOOPG SI87_FN "loop7" "loop7_exit" 0xf40 0x2220 0;;
let SI87_ADD9 = PROVE_ADDLOOPG SI87_FN "loop9" "loop9_exit" 0xf40 0x2620 0;;
let SI87_ADD11 = PROVE_ADDLOOPG SI87_FN "loop11" "loop11_exit" 0xf40 0x2a20 0;;
let SI87_ADD13 = PROVE_ADDLOOPG SI87_FN "loop13" "loop13_exit" 0xf40 0x2e20 0;;
let SI87_ADD15 = PROVE_ADDLOOPG SI87_FN "loop15" "loop15_exit" 0xf40 0x3220 0;;
let SI87_ADD17 = PROVE_ADDLOOPG SI87_FN "loop17" "loop17_exit" 0xf40 0x3620 0;;
let SI87_PWM18 = PROVE_PWMLOOPQ "RBX" SI87_FN "loop18" "loop18_exit" 0x1a20 0x340 0;;
let SI87_PWM19 = PROVE_PWMLOOPQ "RBX" SI87_FN "loop19" "loop19_exit" 0x1e20 0x340 0;;
let SI87_PWM20 = PROVE_PWMLOOPQ "RBX" SI87_FN "loop20" "loop20_exit" 0x2220 0x340 0;;
let SI87_PWM21 = PROVE_PWMLOOPQ "RBX" SI87_FN "loop21" "loop21_exit" 0x2620 0x340 0;;
let SI87_PWM22 = PROVE_PWMLOOPQ "RBX" SI87_FN "loop22" "loop22_exit" 0x2a20 0x340 0;;
let SI87_PWM23 = PROVE_PWMLOOPQ "RBX" SI87_FN "loop23" "loop23_exit" 0x2e20 0x340 0;;
let SI87_PWM24 = PROVE_PWMLOOPQ "RBX" SI87_FN "loop24" "loop24_exit" 0x3220 0x340 0;;
let SI87_PWM25 = PROVE_PWMLOOPQ "RBX" SI87_FN "loop25" "loop25_exit" 0x3620 0x340 0;;

(* ------------------------------------------------------------------------- *)
(* w: the reduction (loops 26 to 33) and the caddq (34 to 41).               *)
(* ------------------------------------------------------------------------- *)

let SI87_RED26 = PROVE_REDLOOPG SI87_FN "loop26" "loop26_exit" 0x1a10 4;;
let SI87_RED27 = PROVE_REDLOOPG SI87_FN "loop27" "loop27_exit" 0x1a10 260;;
let SI87_RED28 = PROVE_REDLOOPG SI87_FN "loop28" "loop28_exit" 0x1a10 516;;
let SI87_RED29 = PROVE_REDLOOPG SI87_FN "loop29" "loop29_exit" 0x1a10 772;;
let SI87_RED30 = PROVE_REDLOOPG SI87_FN "loop30" "loop30_exit" 0x1a10 1028;;
let SI87_RED31 = PROVE_REDLOOPG SI87_FN "loop31" "loop31_exit" 0x1a10 1284;;
let SI87_RED32 = PROVE_REDLOOPG SI87_FN "loop32" "loop32_exit" 0x1a10 1540;;
let SI87_RED33 = PROVE_REDLOOPG SI87_FN "loop33" "loop33_exit" 0x1a10 1796;;
let SI87_CQ34 = PROVE_CADDQG SI87_FN "loop34" "loop34_exit" 0x1a20 0 11;;
let SI87_CQ35 = PROVE_CADDQG SI87_FN "loop35" "loop35_exit" 0x1e20 256 11;;
let SI87_CQ36 = PROVE_CADDQG SI87_FN "loop36" "loop36_exit" 0x2220 512 11;;
let SI87_CQ37 = PROVE_CADDQG SI87_FN "loop37" "loop37_exit" 0x2620 768 11;;
let SI87_CQ38 = PROVE_CADDQG SI87_FN "loop38" "loop38_exit" 0x2a20 1024 11;;
let SI87_CQ39 = PROVE_CADDQG SI87_FN "loop39" "loop39_exit" 0x2e20 1280 11;;
let SI87_CQ40 = PROVE_CADDQG SI87_FN "loop40" "loop40_exit" 0x3220 1536 11;;
let SI87_CQ41 = PROVE_CADDQG SI87_FN "loop41" "loop41_exit" 0x3620 1792 11;;

(* ------------------------------------------------------------------------- *)
(* w decomposed and w1 packed by the rolled row loop 42: the decomposition   *)
(* of row k through RCX (loop 43, the high parts at rsp0 + 0x340) and the   *)
(* packing through RAX to rsp0 + 0x1620 + 128 k (loop 44, the mask in XMM6), *)
(* as lemmas, and the whole loop (DW1R) about the vector at rsp0 + 0x1a20.   *)
(* Then c~ = H(mu || w1) as inlined (C2S): mu at rsp0 + 0x2c0, w1 at rsp0 +  *)
(* 0x1620, the state at rsp0 + 0x740, zeroed from XMM5.                      *)
(* ------------------------------------------------------------------------- *)

let SI87_DEC43_CFG =
  {dc_fn = SI87_FN; dc_loop = "loop43"; dc_exit = "loop43_exit"; dc_idx = "RSI"; dc_r0 = 0;
   dc_wd = None; dc_wreg = "RCX"; dc_w1d = 0x340;
   dc_val = "RDI"; dc_hi = "R8"; dc_lo = "RDI"; dc_regs = "RSI; RDI; R8; R9"};;

let SI87_W1P44_CFG =
  {wp_fn = SI87_FN; wp_start = "loop43_exit"; wp_loop = "loop44"; wp_exit = "loop44_exit";
   wp_idx = "RSI"; wp_r0 = 0; wp_ib = 0x340; wp_ob = None; wp_oreg = "RAX"; wp_mask = "XMM6"};;

let SI87_DEC43 = PROVE_DECOMP32 SI87_DEC43_CFG;;
let SI87_W1P44 = PROVE_W1PACK4G SI87_W1P44_CFG;;

let SI87_DW1R42 = PROVE_DW1R
  {dr_fn = SI87_FN; dr_start = "loop41_exit"; dr_loop = "loop42"; dr_exit = "loop42_exit";
   dr_wo = 0x1a20; dr_ho = 0x340; dr_oo = 0x1620; dr_dec = SI87_DEC43; dr_pack = SI87_W1P44};;

let SI87_C2 = PROVE_C2S
  {c2_fn = SI87_FN; c2_start = "loop42_exit"; c2_end = "after_mldsa_keccakf1600_permute_4";
   c2_so = 0x740; c2_mo = 0x2c0; c2_wo = 0x1620};;

(* ------------------------------------------------------------------------- *)
(* z_i: s1_i unpacked (loop 48) times the challenge (49, constant in R14),   *)
(* y_i sampled again (G1AV, SQZ, unpacking 50, ZER) and added (51), the      *)
(* reduction (52) and the norm check (53).                                   *)
(* ------------------------------------------------------------------------- *)

let SI87_G1A_Z_CFG =
  {ga_fn = SI87_FN; ga_start = "after_mldsa_poly_invntt_tomont_9";
   ga_end = "join16"; ga_jreg = "R12"; ga_jsave = "bytes64"; ga_jslot = 0xb8;
   ga_inb = 0x1a0; ga_st = 0xc0; ga_pos = "R13"; ga_rem = "R15"; ga_off = "R12"};;

let SI87_SQZ_Z_CFG =
  {sq_fn = SI87_FN; sq_lo = "join14"; sq_head = "join16"; sq_exit = "join17";
   sq_pos = "R13"; sq_rem = "R15"; sq_off = "R12"; sq_len = "RBX";
   sq_sp = "R14"; sq_st = 0xc0; sq_buf = 0x1360};;

let SI87_ZER_Z_CFG =
  {zr_fn = SI87_FN; zr_start = "loop50_exit"; zr_fin = 0x25b2; zr_st = 0xc0;
   zr_buf = 0x1360; zr_inb = 0x1a0; zr_breg = "RBX"; zr_post = 6};;

let SI87_ETA48 = PROVE_ETA2U SI87_FN "loop48" "loop48_exit" 0xb40 "RBX; R15";;
let SI87_PWM49 = PROVE_PWMLOOPQ "R14" SI87_FN "loop49" "loop49_exit" 0xb3c 0x73c 1;;
let SI87_G1A_Z = PROVE_G1AV SI87_G1A_Z_CFG 0xa0 false;;
let SI87_SQZ_Z = PROVE_SQZ SI87_SQZ_Z_CFG;;
let SI87_UZ_Z = PROVE_UNPACKZ19 SI87_FN "loop50" "loop50_exit" 0x340 0 "RDI; R8; R9";;
let SI87_ZER_Z = PROVE_ZER SI87_ZER_Z_CFG;;
let SI87_ADD51 = PROVE_ADDLOOPG SI87_FN "loop51" "loop51_exit" 0x310 0xb10 12;;
let SI87_RED52 = PROVE_REDLOOPX SI87_FN "loop52" "loop52_exit" 0xb30 4 6 7;;
let SI87_CHK53 = PROVE_CHKNORM SI87_FN "loop53" "loop53_exit" "RSP" 0xb40 524168;;

(* ------------------------------------------------------------------------- *)
(* Row j of w0 - c s2 + c t0 (RBX = w_j, as in 44): s2_j unpacked (loop 56)  *)
(* times the challenge (57, constant in RSI), subtracted (58), reduced (59)  *)
(* and checked (60); t0_j unpacked (61) times the challenge (62), reduced    *)
(* (63), checked (64) and added (65).                                        *)
(* ------------------------------------------------------------------------- *)

let SI87_ETA56 = PROVE_ETA2U SI87_FN "loop56" "loop56_exit" 0x340 "R12; R13";;
let SI87_PWM57 = PROVE_PWMLOOPQ "RSI" SI87_FN "loop57" "loop57_exit" 0x33c 0x73c 1;;
let SI87_SUB58 = PROVE_SUBLOOPB SI87_FN "loop58" "loop58_exit" 0x340;;
let SI87_RED59 = PROVE_REDLOOPB SI87_FN "loop59" "loop59_exit";;
let SI87_CHK60 = PROVE_CHKNORM SI87_FN "loop60" "loop60_exit" "RBX" 0 261768;;
let SI87_T0U61 = PROVE_T0UR ["R12","R15"; "R14","R12"; "R15","R13"] SI87_FN "loop61" "loop61_exit" 0x340;;
let SI87_PWM62 = PROVE_PWMLOOPQ "RSI" SI87_FN "loop62" "loop62_exit" 0x33c 0x73c 1;;
let SI87_RED63 = PROVE_REDLOOPG SI87_FN "loop63" "loop63_exit" 0x340 0;;
let SI87_CHK64 = PROVE_CHKNORM SI87_FN "loop64" "loop64_exit" "RSP" 0x340 261888;;
let SI87_ADD65 = PROVE_ADDLOOPB SI87_FN "loop65" "loop65_exit" 0x340;;

(* The packing of z (gamma1 = 2^19). *)

let SI87_ZP54 = PROVE_ZPACK19 SI87_FN "loop54" "loop54_exit" 0xb40;;

(* ------------------------------------------------------------------------- *)
(* The hints of rows 0 to 7 (mld_pack_sig_h, gamma2 = (q - 1) / 32), each    *)
(* from the head of its loop to the store of its count, or to the            *)
(* rejection at join22 (+0x30a8).                                            *)
(* ------------------------------------------------------------------------- *)

let HROW87_CFGS =
  let f k head store fin late lo =
    {hr_fn = SI87_FN; hr_k = k; hr_head = head;
     hr_store = store; hr_fin = fin; hr_rej = 0x30a8; hr_late = late; hr_lo = lo} in
  [f 0 0x3051 0x3183 0x318e true 0x21;
   f 1 0x320c 0x324c 0x3257 false 0xc;
   f 2 0x32dc 0x331c 0x3327 false 0xc;
   f 3 0x33ac 0x33ec 0x33f7 false 0xc;
   f 4 0x3491 0x34bc 0x34c7 true 0x21;
   f 5 0x354c 0x358c 0x3597 false 0xc;
   f 6 0x3631 0x365c 0x3667 true 0x21;
   f 7 0x3701 0x372c 0x3737 true 0x21];;

let SI87_HROW0 = PROVE_HROW32 HROW87_PSET (el 0 HROW87_CFGS);;
let SI87_HROW1 = PROVE_HROW32 HROW87_PSET (el 1 HROW87_CFGS);;
let SI87_HROW2 = PROVE_HROW32 HROW87_PSET (el 2 HROW87_CFGS);;
let SI87_HROW3 = PROVE_HROW32 HROW87_PSET (el 3 HROW87_CFGS);;
let SI87_HROW4 = PROVE_HROW32 HROW87_PSET (el 4 HROW87_CFGS);;
let SI87_HROW5 = PROVE_HROW32 HROW87_PSET (el 5 HROW87_CFGS);;
let SI87_HROW6 = PROVE_HROW32 HROW87_PSET (el 6 HROW87_CFGS);;
let SI87_HROW7 = PROVE_HROW32 HROW87_PSET (el 7 HROW87_CFGS);;

(* The unpacking of w1 (row r at rsp0 + 0x1620 + 128 r) to rsp0 + 0x340 for
   the hints of row r: loop 66 (index RAX, temporary RCX) and loops 68 to 74
   (RCX and RDX), with XMM4 = 0 and the nibble mask in XMM5. *)

let SI87_W1U66 = PROVE_W1UNPACK4 SI87_FN "loop66" "loop66_exit" "RAX" "RCX" 0x1620 0x340;;
let SI87_W1U68 = PROVE_W1UNPACK4 SI87_FN "loop68" "loop68_exit" "RCX" "RDX" 0x16a0 0x340;;
let SI87_W1U69 = PROVE_W1UNPACK4 SI87_FN "loop69" "loop69_exit" "RCX" "RDX" 0x1720 0x340;;
let SI87_W1U70 = PROVE_W1UNPACK4 SI87_FN "loop70" "loop70_exit" "RCX" "RDX" 0x17a0 0x340;;
let SI87_W1U71 = PROVE_W1UNPACK4 SI87_FN "loop71" "loop71_exit" "RCX" "RDX" 0x1820 0x340;;
let SI87_W1U72 = PROVE_W1UNPACK4 SI87_FN "loop72" "loop72_exit" "RCX" "RDX" 0x18a0 0x340;;
let SI87_W1U73 = PROVE_W1UNPACK4 SI87_FN "loop73" "loop73_exit" "RCX" "RDX" 0x1920 0x340;;
let SI87_W1U74 = PROVE_W1UNPACK4 SI87_FN "loop74" "loop74_exit" "RCX" "RDX" 0x19a0 0x340;;

(* ------------------------------------------------------------------------- *)
(* All the lemmas of this file. Those that call the permutation (the       *)
(* squeezes, and C2 in 87) rest on its specification, which the spec file   *)
(* assumes (assume_spec) until the link; no lemma may rest on another       *)
(* hypothesis.                                                              *)
(* ------------------------------------------------------------------------- *)

let SI87_ALL =
  [SI87_G1A_Y; SI87_SQZ_Y; SI87_UZ_Y; SI87_ZER_Y; SI87_PWM2; SI87_PWM4;
   SI87_PWM6; SI87_PWM8; SI87_PWM10; SI87_PWM12; SI87_PWM14; SI87_PWM16;
   SI87_ADD3; SI87_ADD5; SI87_ADD7; SI87_ADD9; SI87_ADD11; SI87_ADD13;
   SI87_ADD15; SI87_ADD17; SI87_PWM18; SI87_PWM19; SI87_PWM20; SI87_PWM21;
   SI87_PWM22; SI87_PWM23; SI87_PWM24; SI87_PWM25; SI87_RED26; SI87_RED27;
   SI87_RED28; SI87_RED29; SI87_RED30; SI87_RED31; SI87_RED32; SI87_RED33;
   SI87_CQ34; SI87_CQ35; SI87_CQ36; SI87_CQ37; SI87_CQ38; SI87_CQ39;
   SI87_CQ40; SI87_CQ41; SI87_DEC43; SI87_W1P44; SI87_DW1R42; SI87_C2;
   SI87_ETA48; SI87_PWM49; SI87_G1A_Z; SI87_SQZ_Z; SI87_UZ_Z; SI87_ZER_Z;
   SI87_ADD51; SI87_RED52; SI87_CHK53; SI87_ETA56; SI87_PWM57; SI87_SUB58;
   SI87_RED59; SI87_CHK60; SI87_T0U61; SI87_PWM62; SI87_RED63; SI87_CHK64;
   SI87_ADD65; SI87_ZP54; SI87_HROW0; SI87_HROW1; SI87_HROW2; SI87_HROW3;
   SI87_HROW4; SI87_HROW5; SI87_HROW6; SI87_HROW7; SI87_W1U66; SI87_W1U68;
   SI87_W1U69; SI87_W1U70; SI87_W1U71; SI87_W1U72; SI87_W1U73; SI87_W1U74];;

let () =
  let perm = concl MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600 in
  if exists (fun th -> exists (fun h -> h <> perm) (hyp th)) SI87_ALL
  then failwith "signature_internal_87_inline.ml: a lemma with another hypothesis"
  else Printf.printf "signature_internal_87_inline.ml: %d region lemmas\n%!" (length SI87_ALL);;
