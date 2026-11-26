(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The region lemmas of mldsa44_signature_internal (clang 23 -O3 mono        *)
(* reduced-RAM), instances of the generators of inline_sign.ml and           *)
(* inline_attempt.ml for the loops that clang has inlined into the signing   *)
(* attempt, by the labels of layout.ml. The buffers are at fixed offsets     *)
(* from the stack pointer rsp0 of the attempt: the seed of the matrix        *)
(* entries at + 0xa0, the pointer to rho'' at + 0x80 and kappa at + 0x88, c~ *)
(* at + 0x200, rho'' at + 0x2e0, the polynomial of y (also scratch) at +     *)
(* 0x320, w1 packed at + 0x720, z at + 0xce0, the entries of the matrix at + *)
(* 0x10e0, w at + 0x1500 and the challenge at + 0x2500, with the Keccak      *)
(* state, the input and the buffer of the sampling of y at + 0x720, + 0xa20  *)
(* and + 0x2500 in the product with the matrix and at + 0xa0, + 0x1a0 and +  *)
(* 0xa20 in the computation of z.                                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_attempt.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_hrow.ml";;

let SI44_FN = "mldsa44_signature_internal";;

(* ------------------------------------------------------------------------- *)
(* The product with the matrix, column j: the sampling of y_j (absorbing,    *)
(* squeezing, unpacking, zeroing), the entries of column j times its NTT     *)
(* (loops 2, 4, 6, 8 for j > 0, 10 to 13 for j = 0) and the sums of the rows *)
(* (loops 3, 5, 7, 9).                                                       *)
(* ------------------------------------------------------------------------- *)

let SI44_G1A_Y_CFG =
  {ga_fn = SI44_FN; ga_start = "join4"; ga_end = "join7";
   ga_jreg = "R14"; ga_jsave = "bytes32"; ga_jslot = 16; ga_inb = 0xa20;
   ga_st = 0x720; ga_pos = "R13"; ga_rem = "R14"; ga_off = "R15"};;

let SI44_SQZ_Y_CFG =
  {sq_fn = SI44_FN; sq_lo = "join5"; sq_head = "join7"; sq_exit = "join8";
   sq_pos = "R13"; sq_rem = "R14"; sq_off = "R15"; sq_len = "RBX";
   sq_sp = "R12"; sq_st = 0x720; sq_buf = 0x2500};;

let SI44_ZER_Y_CFG =
  {zr_fn = SI44_FN; zr_start = "loop1_exit"; zr_fin = 0x590; zr_st = 0x720;
   zr_buf = 0x2500; zr_inb = 0xa20; zr_breg = "RBX"; zr_post = 6};;

let SI44_G1A_Y = PROVE_G1A SI44_G1A_Y_CFG;;
let SI44_SQZ_Y = PROVE_SQZ SI44_SQZ_Y_CFG;;
let SI44_UZ_Y = PROVE_UNPACKZ17B SI44_FN "loop1" "loop1_exit" 0x2500;;
let SI44_ZER_Y = PROVE_ZER SI44_ZER_Y_CFG;;

let SI44_PWM2 = PROVE_PWMLOOPG SI44_FN "loop2" "loop2_exit" 0x10dc 0x31c 1;;
let SI44_PWM4 = PROVE_PWMLOOPG SI44_FN "loop4" "loop4_exit" 0x10dc 0x31c 1;;
let SI44_PWM6 = PROVE_PWMLOOPG SI44_FN "loop6" "loop6_exit" 0x10dc 0x31c 1;;
let SI44_PWM8 = PROVE_PWMLOOPG SI44_FN "loop8" "loop8_exit" 0x10e0 0x320 0;;
let SI44_ADD3 = PROVE_ADDLOOPG SI44_FN "loop3" "loop3_exit" 0x10b0 0x14d0 12;;
let SI44_ADD5 = PROVE_ADDLOOPG SI44_FN "loop5" "loop5_exit" 0x10b0 0x18d0 12;;
let SI44_ADD7 = PROVE_ADDLOOPG SI44_FN "loop7" "loop7_exit" 0x10e0 0x1d00 0;;
let SI44_ADD9 = PROVE_ADDLOOPG SI44_FN "loop9" "loop9_exit" 0x10e0 0x2100 0;;
let SI44_PWM10 = PROVE_PWMLOOPG SI44_FN "loop10" "loop10_exit" 0x1500 0x320 0;;
let SI44_PWM11 = PROVE_PWMLOOPG SI44_FN "loop11" "loop11_exit" 0x1900 0x320 0;;
let SI44_PWM12 = PROVE_PWMLOOPG SI44_FN "loop12" "loop12_exit" 0x1d00 0x320 0;;
let SI44_PWM13 = PROVE_PWMLOOPG SI44_FN "loop13" "loop13_exit" 0x2100 0x320 0;;

(* ------------------------------------------------------------------------- *)
(* w: the reduction (loops 14 to 17), the caddq (18 to 21), the             *)
(* decomposition and the packing of w1 (22 to 29).                           *)
(* ------------------------------------------------------------------------- *)

let SI44_RED14 = PROVE_REDLOOPG SI44_FN "loop14" "loop14_exit" 0x14f0 4;;
let SI44_RED15 = PROVE_REDLOOPG SI44_FN "loop15" "loop15_exit" 0x14f0 260;;
let SI44_RED16 = PROVE_REDLOOPG SI44_FN "loop16" "loop16_exit" 0x14f0 516;;
let SI44_RED17 = PROVE_REDLOOPG SI44_FN "loop17" "loop17_exit" 0x14f0 772;;
let SI44_CQ18 = PROVE_CADDQG SI44_FN "loop18" "loop18_exit" 0x1500 0 11;;
let SI44_CQ19 = PROVE_CADDQG SI44_FN "loop19" "loop19_exit" 0x1900 256 11;;
let SI44_CQ20 = PROVE_CADDQG SI44_FN "loop20" "loop20_exit" 0x1d00 512 11;;
let SI44_CQ21 = PROVE_CADDQG SI44_FN "loop21" "loop21_exit" 0x2100 768 11;;
let SI44_DEC22 = PROVE_DECOMP88 SI44_FN "loop22" "loop22_exit" 0x1500 0x320 0;;
let SI44_DEC24 = PROVE_DECOMP88 SI44_FN "loop24" "loop24_exit" 0x1500 (-0xe0) 256;;
let SI44_DEC26 = PROVE_DECOMP88 SI44_FN "loop26" "loop26_exit" 0x1500 (-0x4e0) 512;;
let SI44_DEC28 = PROVE_DECOMP88 SI44_FN "loop28" "loop28_exit" 0x1500 (-0x8e0) 768;;
let SI44_W1P23 = PROVE_W1PACKS SI44_FN "loop23" "loop23_exit" 0x71e 0x2;;
let SI44_W1P25 = PROVE_W1PACKS SI44_FN "loop25" "loop25_exit" 0x71e 0xc2;;
let SI44_W1P27 = PROVE_W1PACKS SI44_FN "loop27" "loop27_exit" 0x71e 0x182;;
let SI44_W1P29 = PROVE_W1PACKS SI44_FN "loop29" "loop29_exit" 0x71e 0x242;;

(* ------------------------------------------------------------------------- *)
(* z_i: s1_i unpacked (loop 30) times the challenge (31), y_i sampled again  *)
(* (absorbing, squeezing, unpacking 32, zeroing) and added (33), the         *)
(* reduction (34, with the constants in XMM6 and XMM7), the norm check (35)  *)
(* and the packing (36).                                                     *)
(* ------------------------------------------------------------------------- *)

let SI44_G1A_Z_CFG =
  {ga_fn = SI44_FN; ga_start = "after_mldsa_poly_invntt_tomont_5";
   ga_end = "join14"; ga_jreg = "R13"; ga_jsave = "bytes64"; ga_jslot = 0x98;
   ga_inb = 0x1a0; ga_st = 0xa0; ga_pos = "R12"; ga_rem = "R13"; ga_off = "R14"};;

let SI44_SQZ_Z_CFG =
  {sq_fn = SI44_FN; sq_lo = "join12"; sq_head = "join14"; sq_exit = "join15";
   sq_pos = "R12"; sq_rem = "R13"; sq_off = "R14"; sq_len = "RBX";
   sq_sp = "R15"; sq_st = 0xa0; sq_buf = 0xa20};;

let SI44_ZER_Z_CFG =
  {zr_fn = SI44_FN; zr_start = "loop32_exit"; zr_fin = 0x1a24; zr_st = 0xa0;
   zr_buf = 0xa20; zr_inb = 0x1a0; zr_breg = "RBX"; zr_post = 7};;

let SI44_ETA30 = PROVE_ETA2U SI44_FN "loop30" "loop30_exit" 0xce0 "RBX; R14";;
let SI44_PWM31 = PROVE_PWMLOOPG SI44_FN "loop31" "loop31_exit" 0xcdc 0x24fc 1;;
let SI44_G1A_Z = PROVE_G1A SI44_G1A_Z_CFG;;
let SI44_SQZ_Z = PROVE_SQZ SI44_SQZ_Z_CFG;;
let SI44_UZ_Z = PROVE_UNPACKZ17B SI44_FN "loop32" "loop32_exit" 0xa20;;
let SI44_ZER_Z = PROVE_ZER SI44_ZER_Z_CFG;;
let SI44_ADD33 = PROVE_ADDLOOPG SI44_FN "loop33" "loop33_exit" 0x2f0 0xcb0 12;;
let SI44_RED34 = PROVE_REDLOOPX SI44_FN "loop34" "loop34_exit" 0xcd0 4 6 7;;
let SI44_CHK35 = PROVE_CHKNORM SI44_FN "loop35" "loop35_exit" "RSP" 0xce0 130994;;
let SI44_ZP36 = PROVE_ZPACK17 SI44_FN "loop36" "loop36_exit";;

(* ------------------------------------------------------------------------- *)
(* Row j of w0 - c s2 + c t0 (RBX = w_j): s2_j unpacked (loop 38) times the  *)
(* challenge (39), subtracted (40), reduced (41) and checked (42); t0_j      *)
(* unpacked (43) times the challenge (44), reduced (45), checked (46) and    *)
(* added (47).                                                               *)
(* ------------------------------------------------------------------------- *)

let SI44_ETA38 = PROVE_ETA2U SI44_FN "loop38" "loop38_exit" 0x320 "R14; R15";;
let SI44_PWM39 = PROVE_PWMLOOPG SI44_FN "loop39" "loop39_exit" 0x31c 0x24fc 1;;
let SI44_SUB40 = PROVE_SUBLOOPB SI44_FN "loop40" "loop40_exit" 0x320;;
let SI44_RED41 = PROVE_REDLOOPB SI44_FN "loop41" "loop41_exit";;
let SI44_CHK42 = PROVE_CHKNORM SI44_FN "loop42" "loop42_exit" "RBX" 0 95154;;
let SI44_T0U43 = PROVE_T0U SI44_FN "loop43" "loop43_exit" 0x320;;
let SI44_PWM44 = PROVE_PWMLOOPG SI44_FN "loop44" "loop44_exit" 0x31c 0x24fc 1;;
let SI44_RED45 = PROVE_REDLOOPG SI44_FN "loop45" "loop45_exit" 0x320 0;;
let SI44_CHK46 = PROVE_CHKNORM SI44_FN "loop46" "loop46_exit" "RSP" 0x320 95232;;
let SI44_ADD47 = PROVE_ADDLOOPB SI44_FN "loop47" "loop47_exit" 0x320;;

(* ------------------------------------------------------------------------- *)
(* The hints: w1 of row k unpacked from its packed bytes (loops 48, 49, 51,  *)
(* 53).                                                                      *)
(* ------------------------------------------------------------------------- *)

let SI44_W1U48 = PROVE_W1UNPACK SI44_FN "loop48" "loop48_exit" "RAX" 2 0x720 "RDX; RSI; RDI";;
let SI44_W1U49 = PROVE_W1UNPACK SI44_FN "loop49" "loop49_exit" "RDX" 0 0x7e0 "RSI; RDI; R8";;
let SI44_W1U51 = PROVE_W1UNPACK SI44_FN "loop51" "loop51_exit" "RDX" 0 0x8a0 "RSI; RDI; R8";;
let SI44_W1U53 = PROVE_W1UNPACK SI44_FN "loop53" "loop53_exit" "RDX" 0 0x960 "RSI; RDI; R8";;

(* ------------------------------------------------------------------------- *)
(* The hints of rows 0 to 3 (mld_pack_sig_h), each from the head of its loop *)
(* to the store of its count, or to the rejection at join26.                 *)
(* ------------------------------------------------------------------------- *)

let SI44_HROW0 = PROVE_HROW (el 0 HROW44_CFGS);;
let SI44_HROW1 = PROVE_HROW (el 1 HROW44_CFGS);;
let SI44_HROW2 = PROVE_HROW (el 2 HROW44_CFGS);;
let SI44_HROW3 = PROVE_HROW (el 3 HROW44_CFGS);;
