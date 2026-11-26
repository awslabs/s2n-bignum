(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The region lemmas of mldsa65_signature_internal (clang 23 -O3 mono        *)
(* reduced-RAM), as signature_internal_44_inline.ml does it for 44: the      *)
(* generators of inline_sign.ml, inline_attempt.ml and inline_verify65.ml,   *)
(* and those of inline_sign6587.ml for the loops whose registers or code     *)
(* differ from 44, by the labels of layout.ml. The buffers are at fixed     *)
(* offsets from the stack pointer rsp0 of the attempt (see the parameters).  *)
(*                                                                           *)
(* The decomposition and the packing of w1 (gamma2 = (q - 1) / 32) and the  *)
(* unpacking of w1 for the hints use the generators of inline_sign6587.ml   *)
(* that 44 has no counterpart for (DECOMP32, W1PACK4G, W1UNPACK4).           *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign6587.ml";;

let SI65_FN = "mldsa65_signature_internal";;

(* ------------------------------------------------------------------------- *)
(* The product with the matrix, column j: the sampling of y_j, the entries   *)
(* of column j times its NTT (loops 2, 4, ..., 12 for j > 0, 14 to 19 for    *)
(* j = 0) and the sums of the rows (loops 3, 5, ..., 13). The constant       *)
(* q^-1 2^32 of the products is in RBX (R12 in 44), and the state is zeroed  *)
(* from XMM4 (G1AV).                                                         *)
(* ------------------------------------------------------------------------- *)

let SI65_G1A_Y_CFG =
  {ga_fn = SI65_FN; ga_start = "join4"; ga_end = "join7";
   ga_jreg = "R12"; ga_jsave = "bytes32"; ga_jslot = 0x18; ga_inb = 0xb20;
   ga_st = 0x720; ga_pos = "RBX"; ga_rem = "R15"; ga_off = "R12"};;

let SI65_SQZ_Y_CFG =
  {sq_fn = SI65_FN; sq_lo = "join5"; sq_head = "join7"; sq_exit = "join8";
   sq_pos = "RBX"; sq_rem = "R15"; sq_off = "R12"; sq_len = "R13";
   sq_sp = "R14"; sq_st = 0x720; sq_buf = 0x2d00};;

let SI65_ZER_Y_CFG =
  {zr_fn = SI65_FN; zr_start = "loop1_exit"; zr_fin = 0x532; zr_st = 0x720;
   zr_buf = 0x2d00; zr_inb = 0xb20; zr_breg = "RBX"; zr_post = 6};;

let SI65_G1A_Y = PROVE_G1AV SI65_G1A_Y_CFG 0x80 true;;
let SI65_SQZ_Y = PROVE_SQZ SI65_SQZ_Y_CFG;;
let SI65_UZ_Y = PROVE_UNPACKZ19 SI65_FN "loop1" "loop1_exit" 0x220 0 "RDI; R8; R9";;
let SI65_ZER_Y = PROVE_ZER SI65_ZER_Y_CFG;;

let SI65_PWM2 = PROVE_PWMLOOPQ "RBX" SI65_FN "loop2" "loop2_exit" 0xe1c 0x21c 1;;
let SI65_PWM4 = PROVE_PWMLOOPQ "RBX" SI65_FN "loop4" "loop4_exit" 0xe1c 0x21c 1;;
let SI65_PWM6 = PROVE_PWMLOOPQ "RBX" SI65_FN "loop6" "loop6_exit" 0xe1c 0x21c 1;;
let SI65_PWM8 = PROVE_PWMLOOPQ "RBX" SI65_FN "loop8" "loop8_exit" 0xe1c 0x21c 1;;
let SI65_PWM10 = PROVE_PWMLOOPQ "RBX" SI65_FN "loop10" "loop10_exit" 0xe1c 0x21c 1;;
let SI65_PWM12 = PROVE_PWMLOOPQ "RBX" SI65_FN "loop12" "loop12_exit" 0xe20 0x220 0;;
let SI65_ADD3 = PROVE_ADDLOOPG SI65_FN "loop3" "loop3_exit" 0xdf0 0x14d0 12;;
let SI65_ADD5 = PROVE_ADDLOOPG SI65_FN "loop5" "loop5_exit" 0xdf0 0x18d0 12;;
let SI65_ADD7 = PROVE_ADDLOOPG SI65_FN "loop7" "loop7_exit" 0xe20 0x1d00 0;;
let SI65_ADD9 = PROVE_ADDLOOPG SI65_FN "loop9" "loop9_exit" 0xe20 0x2100 0;;
let SI65_ADD11 = PROVE_ADDLOOPG SI65_FN "loop11" "loop11_exit" 0xe20 0x2500 0;;
let SI65_ADD13 = PROVE_ADDLOOPG SI65_FN "loop13" "loop13_exit" 0xe20 0x2900 0;;
let SI65_PWM14 = PROVE_PWMLOOPQ "RBX" SI65_FN "loop14" "loop14_exit" 0x1500 0x220 0;;
let SI65_PWM15 = PROVE_PWMLOOPQ "RBX" SI65_FN "loop15" "loop15_exit" 0x1900 0x220 0;;
let SI65_PWM16 = PROVE_PWMLOOPQ "RBX" SI65_FN "loop16" "loop16_exit" 0x1d00 0x220 0;;
let SI65_PWM17 = PROVE_PWMLOOPQ "RBX" SI65_FN "loop17" "loop17_exit" 0x2100 0x220 0;;
let SI65_PWM18 = PROVE_PWMLOOPQ "RBX" SI65_FN "loop18" "loop18_exit" 0x2500 0x220 0;;
let SI65_PWM19 = PROVE_PWMLOOPQ "RBX" SI65_FN "loop19" "loop19_exit" 0x2900 0x220 0;;

(* ------------------------------------------------------------------------- *)
(* w: the reduction (loops 20 to 25) and the caddq (26 to 31).               *)
(* ------------------------------------------------------------------------- *)

let SI65_RED20 = PROVE_REDLOOPG SI65_FN "loop20" "loop20_exit" 0x14f0 4;;
let SI65_RED21 = PROVE_REDLOOPG SI65_FN "loop21" "loop21_exit" 0x14f0 260;;
let SI65_RED22 = PROVE_REDLOOPG SI65_FN "loop22" "loop22_exit" 0x14f0 516;;
let SI65_RED23 = PROVE_REDLOOPG SI65_FN "loop23" "loop23_exit" 0x14f0 772;;
let SI65_RED24 = PROVE_REDLOOPG SI65_FN "loop24" "loop24_exit" 0x14f0 1028;;
let SI65_RED25 = PROVE_REDLOOPG SI65_FN "loop25" "loop25_exit" 0x14f0 1284;;
let SI65_CQ26 = PROVE_CADDQG SI65_FN "loop26" "loop26_exit" 0x1500 0 11;;
let SI65_CQ27 = PROVE_CADDQG SI65_FN "loop27" "loop27_exit" 0x1900 256 11;;
let SI65_CQ28 = PROVE_CADDQG SI65_FN "loop28" "loop28_exit" 0x1d00 512 11;;
let SI65_CQ29 = PROVE_CADDQG SI65_FN "loop29" "loop29_exit" 0x2100 768 11;;
let SI65_CQ30 = PROVE_CADDQG SI65_FN "loop30" "loop30_exit" 0x2500 1024 11;;
let SI65_CQ31 = PROVE_CADDQG SI65_FN "loop31" "loop31_exit" 0x2900 1280 11;;

(* ------------------------------------------------------------------------- *)
(* w decomposed row by row (loops 32, 34, ..., 42, RAX = 256 r ..., the high *)
(* parts at rsp0 + 0x220) and w1 packed after each row (loops 33, 35, ...,  *)
(* 43, from rsp0 + 0x220 to rsp0 + 0xb20 + 128 r; RAX from 4 in rows 0 and  *)
(* 1, from 0 in rows 2 to 5), the mask in XMM6.                              *)
(* ------------------------------------------------------------------------- *)

let SI65_DEC_CFG r =
  {dc_fn = SI65_FN; dc_loop = Printf.sprintf "loop%d" (32 + 2 * r);
   dc_exit = Printf.sprintf "loop%d_exit" (32 + 2 * r); dc_idx = "RAX"; dc_r0 = 256 * r;
   dc_wd = Some 0x1500; dc_wreg = "RSP"; dc_w1d = 0x220 - 1024 * r;
   dc_val = "RCX"; dc_hi = "RDX"; dc_lo = "RCX"; dc_regs = "RAX; RCX; RDX; RSI"};;

let SI65_W1P_CFG r =
  {wp_fn = SI65_FN; wp_start = Printf.sprintf "loop%d_exit" (32 + 2 * r);
   wp_loop = Printf.sprintf "loop%d" (33 + 2 * r);
   wp_exit = Printf.sprintf "loop%d_exit" (33 + 2 * r);
   wp_idx = "RAX"; wp_r0 = (if r < 2 then 4 else 0); wp_ib = 0x220;
   wp_ob = Some (0xb20 + 128 * r); wp_oreg = "RAX"; wp_mask = "XMM6"};;

let SI65_DEC32 = PROVE_DECOMP32 (SI65_DEC_CFG 0);;
let SI65_W1P33 = PROVE_W1PACK4G (SI65_W1P_CFG 0);;
let SI65_DEC34 = PROVE_DECOMP32 (SI65_DEC_CFG 1);;
let SI65_W1P35 = PROVE_W1PACK4G (SI65_W1P_CFG 1);;
let SI65_DEC36 = PROVE_DECOMP32 (SI65_DEC_CFG 2);;
let SI65_W1P37 = PROVE_W1PACK4G (SI65_W1P_CFG 2);;
let SI65_DEC38 = PROVE_DECOMP32 (SI65_DEC_CFG 3);;
let SI65_W1P39 = PROVE_W1PACK4G (SI65_W1P_CFG 3);;
let SI65_DEC40 = PROVE_DECOMP32 (SI65_DEC_CFG 4);;
let SI65_W1P41 = PROVE_W1PACK4G (SI65_W1P_CFG 4);;
let SI65_DEC42 = PROVE_DECOMP32 (SI65_DEC_CFG 5);;
let SI65_W1P43 = PROVE_W1PACK4G (SI65_W1P_CFG 5);;

(* ------------------------------------------------------------------------- *)
(* z_i: s1_i (unpacked by loop 44) times the challenge (45), y_i sampled     *)
(* again (G1A, SQZV: the pointer to the state in R14 from before the loop,   *)
(* unpacking 46, ZERV: 18 instructions before the memset) and added (47),    *)
(* the reduction (48) and the norm check (49).                               *)
(* ------------------------------------------------------------------------- *)

let SI65_G1A_Z_CFG =
  {ga_fn = SI65_FN; ga_start = "after_mldsa_poly_invntt_tomont_7";
   ga_end = "join14"; ga_jreg = "R15"; ga_jsave = "bytes64"; ga_jslot = 0xb8;
   ga_inb = 0xc0; ga_st = 0x110; ga_pos = "R12"; ga_rem = "R15"; ga_off = "RBX"};;

let SI65_SQZ_Z_CFG =
  {sq_fn = SI65_FN; sq_lo = "join12"; sq_head = "join14"; sq_exit = "join15";
   sq_pos = "R12"; sq_rem = "R15"; sq_off = "RBX"; sq_len = "R13";
   sq_sp = "R14"; sq_st = 0x110; sq_buf = 0x1240};;

let SI65_ZER_Z_CFG =
  {zr_fn = SI65_FN; zr_start = "loop46_exit"; zr_fin = 0x1fda; zr_st = 0x110;
   zr_buf = 0x1240; zr_inb = 0xc0; zr_breg = "R14"; zr_post = 6};;

let SI65_ETA44 = PROVE_ETA4U SI65_FN "loop44" "loop44_exit" 0x720;;
let SI65_PWM45 = PROVE_PWMLOOPQ "RBX" SI65_FN "loop45" "loop45_exit" 0x71c 0x2cfc 1;;
let SI65_G1A_Z = PROVE_G1A SI65_G1A_Z_CFG;;
let SI65_SQZ_Z = PROVE_SQZV SI65_SQZ_Z_CFG true;;
let SI65_UZ_Z = PROVE_UNPACKZ19 SI65_FN "loop46" "loop46_exit" 0x220 0 "RDI; R8; R9";;
let SI65_ZER_Z = PROVE_ZERV SI65_ZER_Z_CFG 18;;
let SI65_ADD47 = PROVE_ADDLOOPG SI65_FN "loop47" "loop47_exit" 0x1f0 0x6f0 12;;
let SI65_RED48 = PROVE_REDLOOPX SI65_FN "loop48" "loop48_exit" 0x710 4 6 7;;
let SI65_CHK49 = PROVE_CHKNORM SI65_FN "loop49" "loop49_exit" "RSP" 0x720 524092;;

(* ------------------------------------------------------------------------- *)
(* Row j of w0 - c s2 + c t0, with the row of w at R13 (RBX in 44): s2_j     *)
(* (unpacked by loop 52) times the challenge (53), subtracted (54), reduced  *)
(* (55) and checked (56); t0_j unpacked (57) times the challenge (58),       *)
(* reduced (59), checked (60) and added (61).                                *)
(* ------------------------------------------------------------------------- *)

let SI65_ETA52 = PROVE_ETA4U SI65_FN "loop52" "loop52_exit" 0x220;;
let SI65_PWM53 = PROVE_PWMLOOPQ "RBX" SI65_FN "loop53" "loop53_exit" 0x21c 0x2cfc 1;;
let SI65_SUB54 = PROVE_SUBLOOPBR "R13" SI65_FN "loop54" "loop54_exit" 0x220;;
let SI65_RED55 = PROVE_REDLOOPBR "R13" SI65_FN "loop55" "loop55_exit";;
let SI65_CHK56 = PROVE_CHKNORM SI65_FN "loop56" "loop56_exit" "R13" 0 261692;;
let SI65_T0U57 = PROVE_T0UR ["R12","RBX"; "R14","R15"; "R15","R12"] SI65_FN "loop57" "loop57_exit" 0x220;;
let SI65_PWM58 = PROVE_PWMLOOPQ "RBX" SI65_FN "loop58" "loop58_exit" 0x21c 0x2cfc 1;;
let SI65_RED59 = PROVE_REDLOOPG SI65_FN "loop59" "loop59_exit" 0x220 0;;
let SI65_CHK60 = PROVE_CHKNORM SI65_FN "loop60" "loop60_exit" "RSP" 0x220 261888;;
let SI65_ADD61 = PROVE_ADDLOOPBR "R13" SI65_FN "loop61" "loop61_exit" 0x220;;

(* The packing of z (gamma1 = 2^19). *)

let SI65_ZP50 = PROVE_ZPACK19 SI65_FN "loop50" "loop50_exit" 0x720;;

(* ------------------------------------------------------------------------- *)
(* The hints of rows 0 to 5 (mld_pack_sig_h, gamma2 = (q - 1) / 32), each    *)
(* from the head of its loop to the store of its count, or to the            *)
(* rejection at join35 (+0x2db0).                                            *)
(* ------------------------------------------------------------------------- *)

let HROW65_CFGS =
  let f k head store fin late lo =
    {hr_fn = SI65_FN; hr_k = k; hr_head = head;
     hr_store = store; hr_fin = fin; hr_rej = 0x2db0; hr_late = late; hr_lo = lo} in
  [f 0 0x294c 0x299a 0x29a5 false 0xc;
   f 1 0x2a41 0x2a6c 0x2a77 true 0x21;
   f 2 0x2afc 0x2b3c 0x2b47 false 0xc;
   f 3 0x2be1 0x2c0c 0x2c17 true 0x21;
   f 4 0x2c9c 0x2cdc 0x2ce7 false 0xc;
   f 5 0x2d70 0x2e7b 0x2e86 false 0x10];;

let SI65_HROW0 = PROVE_HROW32 HROW65_PSET (el 0 HROW65_CFGS);;
let SI65_HROW1 = PROVE_HROW32 HROW65_PSET (el 1 HROW65_CFGS);;
let SI65_HROW2 = PROVE_HROW32 HROW65_PSET (el 2 HROW65_CFGS);;
let SI65_HROW3 = PROVE_HROW32 HROW65_PSET (el 3 HROW65_CFGS);;
let SI65_HROW4 = PROVE_HROW32 HROW65_PSET (el 4 HROW65_CFGS);;
let SI65_HROW5 = PROVE_HROW32 HROW65_PSET (el 5 HROW65_CFGS);;

(* The unpacking of w1 (row r at rsp0 + 0xb20 + 128 r) to rsp0 + 0x220 for
   the hints of row r: loop 62 (index RAX, temporary RCX) and loops 63 to 67
   (RCX and RDX), with XMM4 = 0 and the nibble mask in XMM5. *)

let SI65_W1U62 = PROVE_W1UNPACK4 SI65_FN "loop62" "loop62_exit" "RAX" "RCX" 0xb20 0x220;;
let SI65_W1U63 = PROVE_W1UNPACK4 SI65_FN "loop63" "loop63_exit" "RCX" "RDX" 0xba0 0x220;;
let SI65_W1U64 = PROVE_W1UNPACK4 SI65_FN "loop64" "loop64_exit" "RCX" "RDX" 0xc20 0x220;;
let SI65_W1U65 = PROVE_W1UNPACK4 SI65_FN "loop65" "loop65_exit" "RCX" "RDX" 0xca0 0x220;;
let SI65_W1U66 = PROVE_W1UNPACK4 SI65_FN "loop66" "loop66_exit" "RCX" "RDX" 0xd20 0x220;;
let SI65_W1U67 = PROVE_W1UNPACK4 SI65_FN "loop67" "loop67_exit" "RCX" "RDX" 0xda0 0x220;;

(* ------------------------------------------------------------------------- *)
(* All the lemmas of this file. Those that call the permutation (the       *)
(* squeezes, and C2 in 87) rest on its specification, which the spec file   *)
(* assumes (assume_spec) until the link; no lemma may rest on another       *)
(* hypothesis.                                                              *)
(* ------------------------------------------------------------------------- *)

let SI65_ALL =
  [SI65_G1A_Y; SI65_SQZ_Y; SI65_UZ_Y; SI65_ZER_Y; SI65_PWM2; SI65_PWM4;
   SI65_PWM6; SI65_PWM8; SI65_PWM10; SI65_PWM12; SI65_ADD3; SI65_ADD5;
   SI65_ADD7; SI65_ADD9; SI65_ADD11; SI65_ADD13; SI65_PWM14; SI65_PWM15;
   SI65_PWM16; SI65_PWM17; SI65_PWM18; SI65_PWM19; SI65_RED20; SI65_RED21;
   SI65_RED22; SI65_RED23; SI65_RED24; SI65_RED25; SI65_CQ26; SI65_CQ27;
   SI65_CQ28; SI65_CQ29; SI65_CQ30; SI65_CQ31; SI65_DEC32; SI65_W1P33;
   SI65_DEC34; SI65_W1P35; SI65_DEC36; SI65_W1P37; SI65_DEC38; SI65_W1P39;
   SI65_DEC40; SI65_W1P41; SI65_DEC42; SI65_W1P43; SI65_ETA44; SI65_PWM45;
   SI65_G1A_Z; SI65_SQZ_Z; SI65_UZ_Z; SI65_ZER_Z; SI65_ADD47; SI65_RED48;
   SI65_CHK49; SI65_ETA52; SI65_PWM53; SI65_SUB54; SI65_RED55; SI65_CHK56;
   SI65_T0U57; SI65_PWM58; SI65_RED59; SI65_CHK60; SI65_ADD61; SI65_ZP50;
   SI65_HROW0; SI65_HROW1; SI65_HROW2; SI65_HROW3; SI65_HROW4; SI65_HROW5;
   SI65_W1U62; SI65_W1U63; SI65_W1U64; SI65_W1U65; SI65_W1U66; SI65_W1U67];;

let () =
  let perm = concl MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600 in
  if exists (fun th -> exists (fun h -> h <> perm) (hyp th)) SI65_ALL
  then failwith "signature_internal_65_inline.ml: a lemma with another hypothesis"
  else Printf.printf "signature_internal_65_inline.ml: %d region lemmas\n%!" (length SI65_ALL);;
