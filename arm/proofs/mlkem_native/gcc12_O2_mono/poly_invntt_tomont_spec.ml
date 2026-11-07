(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse number-theoretic transform from ML-KEM, with Montgomery           *)
(* scaling. This is the code for mlk_poly_invntt_tomont_c from               *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2 as   *)
(* one translation unit (see mlkem_native/README.md). It is the same as      *)
(* mlkem_poly_invntt_tomont of the separate -O2 build up to the allocation   *)
(* of registers and a NOP before the first loop. Unlike the hand-written     *)
(* kernel, it reads its own vectors of constants and table of zetas from     *)
(* the read-only data. It is verified in the whole image (see                *)
(* libmlkem.ml), with the proof for the separate -O2 build adapted to the    *)
(* image: the registers are renamed, and the constants and the table of      *)
(* zetas are in the image.                                                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;
needs "common/int_linear.ml";;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_ZETAS_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_DATA_RULE mlk_zetas_data (layout "rodata_mlk_zetas");;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_CONSTANTS =
  [MLKEM_NATIVE_IMAGE_CONST_RULE (layout "mlk_poly_invntt_tomont_c_const1") 128;
   MLKEM_NATIVE_IMAGE_CONST_RULE (layout "mlk_poly_invntt_tomont_c_const2") 128];;

(*** The code in the image:

    mlk_poly_invntt_tomont_c:
       +0x0: mov     x15, x0
       +0x4: adrp    x0, <page>
       +0x8: mvni    v3.8h, #0xd, lsl #8
       +0xc: add     x1, x15, #0x200
      +0x10: ldr     q4, [x0, #3184]
      +0x14: adrp    x0, <page>
      +0x18: stp     x19, x30, [sp, #-16]!
      +0x1c: ldr     q5, [x0, #3200]
      +0x20: mov     x0, x15
      +0x24: nop
      +0x28: ldr     q0, [x0]
      +0x2c: smull   v1.4s, v0.4h, v4.4h
      +0x30: smull2  v0.4s, v0.8h, v4.8h
      +0x34: uzp1    v2.8h, v1.8h, v0.8h
      +0x38: mul     v2.8h, v2.8h, v5.8h
      +0x3c: smlal   v1.4s, v2.4h, v3.4h
      +0x40: smlal2  v0.4s, v2.8h, v3.8h
      +0x44: uzp2    v1.8h, v1.8h, v0.8h
      +0x48: str     q1, [x0], #16
      +0x4c: cmp     x1, x0
      +0x50: b.ne    <mlk_poly_invntt_tomont_c+0x28>
      +0x54: adrp    x14, <page>
      +0x58: add     x16, x15, #0x2
      +0x5c: add     x14, x14, #0xd20
      +0x60: mov     w6, #0x65c
      +0x64: mov     w17, #0x7
      +0x68: mov     w30, #0x100
      +0x6c: mov     w18, #0x1
      +0x70: mov     w9, #0x4ebf
      +0x74: mov     w8, #0x2000000
      +0x78: mov     w4, #0xfffff2ff
      +0x7c: mov     w7, #0xfffff301
      +0x80: lsr     w10, w30, w17
      +0x84: mov     w11, #0x0
      +0x88: lsl     w12, w18, w17
      +0x8c: lsl     w13, w10, #1
      +0x90: sub     w12, w12, #0x1
      +0x94: nop
      +0x98: sub     w12, w12, #0x1                      <----+ |
      +0x9c: cmp     w11, w10                                 | |
      +0xa0: b.cs    <mlk_poly_invntt_tomont_c+0x114>                               ---+ | |
      +0xa4: sub     w5, w10, w11                           | | |
      +0xa8: mov     w0, w10                                | | |
      +0xac: sub     w5, w5, #0x1                           | | |
      +0xb0: mov     w3, w11                                | | |
      +0xb4: add     x5, x5, x0                             | | |
      +0xb8: sub     x3, x3, x0                             | | |
      +0xbc: add     x2, x15, w10, uxtw #1                  | | |
      +0xc0: add     x5, x16, x5, lsl #1                    | | |
      +0xc4: nop     | | |
      +0xc8: ldrsh   w19, [x2, x3, lsl #1]               <+ | | |
      +0xcc: ldrh    w0, [x2]                             | | | |
      +0xd0: add     w0, w19, w0                          | | | |
      +0xd4: sxth    w0, w0                               | | | |
      +0xd8: madd    w1, w0, w9, w8                       | | | |
      +0xdc: asr     w1, w1, #26                          | | | |
      +0xe0: madd    w0, w1, w4, w0                       | | | |
      +0xe4: strh    w0, [x2, x3, lsl #1]                 | | | |
      +0xe8: ldrh    w0, [x2]                             | | | |
      +0xec: sub     w0, w0, w19                          | | | |
      +0xf0: sxth    w0, w0                               | | | |
      +0xf4: mul     w0, w0, w6                           | | | |
      +0xf8: mul     w1, w0, w7                           | | | |
      +0xfc: sxth    w1, w1                               | | | |
     +0x100: madd    w0, w1, w4, w0                       | | | |
     +0x104: asr     w0, w0, #16                          | | | |
     +0x108: strh    w0, [x2], #2                         | | | |
     +0x10c: cmp     x2, x5                               | | | |
     +0x110: b.ne    <mlk_poly_invntt_tomont_c+0xc8>                               -+ | | |
     +0x114: add     w11, w11, w13                       <--+ | |
     +0x118: add     w10, w10, w13                            | |
     +0x11c: cmp     w11, #0xff                               | |
     +0x120: b.hi    <mlk_poly_invntt_tomont_c+0x12c>                          -+   | |
     +0x124: ldrsh   w6, [x14, w12, uxtw #1]              |   | |
     +0x128: b       <mlk_poly_invntt_tomont_c+0x98>                               -----+ |
     +0x12c: subs    w17, w17, #0x1
     +0x130: b.eq    <mlk_poly_invntt_tomont_c+0x144>
     +0x134: lsl     w0, w18, w17
     +0x138: sub     w0, w0, #0x1
     +0x13c: ldrsh   w6, [x14, x0, lsl #1]
     +0x140: b       <mlk_poly_invntt_tomont_c+0x80>
     +0x144: ldp     x19, x30, [sp], #16
     +0x148: ret
 ***)

(*** The equations that the vectors of constants and the table of zetas   ***)
(*** are at pc + mlk_poly_invntt_tomont_c_consts and pc + rodata_mlk_zetas ***)
(*** are only assumed where the addresses are used, since they would ruin ***)
(*** the matching of the other assumptions, which are about the variables.***)

let zeta_eq = ref TRUTH;;
let consts_eq = ref TRUTH;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlk_poly_invntt_tomont_c"];;

(* ------------------------------------------------------------------------- *)
(* The computation done by the C code, with its 16-bit and 32-bit integer    *)
(* arithmetic. The coefficients are first scaled by a Montgomery             *)
(* multiplication by 1441 = 2^25 mod 3329, in a loop that the compiler has   *)
(* vectorized. Then the inverse NTT is done in 7 layers, for l = 7 down to   *)
(* 1, layer l consisting of 2^(l-1) blocks of 2^(9-l) consecutive            *)
(* coefficients. A block uses one zeta to do butterflies on pairs of         *)
(* coefficients 2^(8-l) apart, independently, with a Barrett reduction of    *)
(* the sums.                                                                 *)
(* ------------------------------------------------------------------------- *)

let invntt_scale_c = define
 `invntt_scale_c (x:num->int16) i =
    montred_neon(word_mul (word_sx(x i)) (word 1441))`;;

let invntt_fqmul_c = define
 `invntt_fqmul_c (z:int16) (y:int16) =
    montred_scalar(word_mul (word_sx y) (word_sx z))`;;

let invntt_block_c = define
 `invntt_block_c (z:int16) start len (m:num->int16) i =
    if start <= i /\ i < start + len
    then barred(word_add (m i) (m(i + len)))
    else if start + len <= i /\ i < start + 2 * len
    then invntt_fqmul_c z (word_sub (m i) (m(i - len)))
    else m i`;;

let invntt_blocks_c = define
 `invntt_blocks_c l 0 (r:num->int16) = r /\
  invntt_blocks_c l (SUC b) r =
    invntt_block_c (iword(EL (2 EXP l - 1 - b) mlk_zetas))
                   (2 * 2 EXP (8 - l) * b) (2 EXP (8 - l))
                   (invntt_blocks_c l b r)`;;

let invntt_layers_c = define
 `invntt_layers_c 0 (x:num->int16) = x /\
  invntt_layers_c (SUC n) x =
    invntt_blocks_c (7 - n) (2 EXP (6 - n)) (invntt_layers_c n x)`;;

(* ------------------------------------------------------------------------- *)
(* Some word lemmas for the butterflies.                                     *)
(* ------------------------------------------------------------------------- *)

(*** The address of the lower coefficient, given relative to the upper one ***)

let WORD_2_VAL_STMT =
  `!x:int64. word(2 * val x) = word_mul (word 2) x`;;

let WORD_2_VAL = assume_spec WORD_2_VAL_STMT;;

(*** The sign-extension of the 16-bit sum or difference of coefficients ***)

let WORD_SXFROM_ADD_16_STMT =
  `!x y:int16.
      word_sxfrom 15 (word_subword (word_add (word_sx x) (word_zx y):int32)
                                   (0,16)):int32 =
      word_sx (word_add x y)`;;

let WORD_SXFROM_ADD_16 = assume_spec WORD_SXFROM_ADD_16_STMT;;

let WORD_SXFROM_SUB_16_STMT =
  `!x y:int16.
      word_sxfrom 15 (word_subword (word_sub (word_zx y) (word_sx x):int32)
                                   (0,16)):int32 =
      word_sx (word_sub y x)`;;

let WORD_SXFROM_SUB_16 = assume_spec WORD_SXFROM_SUB_16_STMT;;

(* ------------------------------------------------------------------------- *)
(* One block, from its setup through the inner loop.                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_BLOCK_STMT =
  `!a (consts:num) zetas pc z start len k m w17 w18 w30.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                   (word zetas,256)] /\
     1 <= len /\ start + 2 * len <= 256 /\ 1 <= k /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O2_mono_mc /\
               read PC s = word(pc + mlk_poly_invntt_tomont_c_loop3) /\
               read X10 s = word(start + len) /\ read X11 s = word start /\
               read X12 s = word k /\
               read X4 s = word 4294963967 /\
               read X6 s = word_zx(word_sx z:int32) /\
               read X13 s = word(2 * len) /\
               read X7 s = word 4294963969 /\
               read X8 s = word 33554432 /\ read X9 s = word 20159 /\
               read X14 s = word zetas /\ read X15 s = a /\
               read X16 s = word_add a (word 2) /\
               read X17 s = w17 /\ read X18 s = w18 /\ read X30 s = w30 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        m i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O2_mono_mc /\
               read PC s = word(pc + mlk_poly_invntt_tomont_c_loop3_test) /\
               read X10 s = word(start + 3 * len) /\
               read X11 s = word(start + 2 * len) /\
               read X12 s = word(k - 1) /\
               read X4 s = word 4294963967 /\
               read X6 s = word_zx(word_sx z:int32) /\
               read X13 s = word(2 * len) /\
               read X7 s = word 4294963969 /\
               read X8 s = word 33554432 /\ read X9 s = word 20159 /\
               read X14 s = word zetas /\ read X15 s = a /\
               read X16 s = word_add a (word 2) /\
               read X17 s = w17 /\ read X18 s = w18 /\ read X30 s = w30 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        invntt_block_c z start len m i))
          (MAYCHANGE [PC; X0; X1; X2; X5; X3; X10; X11; X12; X19] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_BLOCK =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_BLOCK_STMT;;

(* ------------------------------------------------------------------------- *)
(* One layer, with the blocks in a loop (except for the last layer).         *)
(* ------------------------------------------------------------------------- *)

(*** Prepare a load of zeta number n using UXTW indexing ***)

let ZETA_UXTW_TAC n =
  MP_TAC(SPEC n VAL_WORD_ZX_UXTW) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mlk_zetas` (concl th)
    then MP_TAC(SPEC n th) else failwith "") THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC];;

(*** Assertions at the block head and block end for layer l, block b ***)

let invntt_blockhead_tm,invntt_blockend_tm =
  let headtm =
   `\s. aligned_bytes_loaded s (word pc)
          mlkem_native_libmlkem_gcc12_O2_mono_mc /\
        read X10 s = word(2 * LEN * B + LEN) /\
        read X11 s = word(2 * LEN * B) /\
        read X12 s = word(2 EXP L - 1 - B) /\
        read X4 s = word 4294963967 /\
        read X6 s =
        word_zx(word_sx(iword(EL (2 EXP L - 1 - B) mlk_zetas):int16):int32) /\
        read X13 s = word(2 * LEN) /\
        read X7 s = word 4294963969 /\
        read X8 s = word 33554432 /\ read X9 s = word 20159 /\
        read X14 s = word zetas /\ read X15 s = a /\
        read X16 s = word_add a (word 2) /\
        read X17 s = word L /\ read X18 s = word 1 /\
        read X30 s = word 256 /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 invntt_blocks_c L B r i)`
  and endtm =
   `\s. aligned_bytes_loaded s (word pc)
          mlkem_native_libmlkem_gcc12_O2_mono_mc /\
        read X10 s = word(2 * LEN * B + LEN) /\
        read X11 s = word(2 * LEN * B) /\
        read X12 s = word(2 EXP L - 1 - B) /\
        read X4 s = word 4294963967 /\
        read X13 s = word(2 * LEN) /\
        read X7 s = word 4294963969 /\
        read X8 s = word 33554432 /\ read X9 s = word 20159 /\
        read X14 s = word zetas /\ read X15 s = a /\
        read X16 s = word_add a (word 2) /\
        read X17 s = word L /\ read X18 s = word 1 /\
        read X30 s = word 256 /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 invntt_blocks_c L B r i)` in
  let mk tm l b =
    let len = mk_small_numeral(1 lsl (8 - l)) in
    let tm' = subst [mk_small_numeral l,`L:num`; len,`LEN:num`; b,`B:num`]
                    tm in
    rhs(concl(NUM_REDUCE_CONV tm')) in
  (fun l b -> mk headtm l b),(fun l b -> mk endtm l b);;

(*** Apply the block lemma at the head of block b of layer l ***)

let INVNTT_BLOCK_TAC l b =
  let red t =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (8 - l)),`LEN:num`;
      b,`B:num`] t))) in
  let th = SPECL
   [`a:int64`; `consts:num`; `zetas:num`; `pc:num`;
    red `iword(EL (2 EXP L - 1 - B) mlk_zetas):int16`;
    red `2 * LEN * B`; red `LEN:num`; red `2 EXP L - 1 - B`;
    red `invntt_blocks_c L B r`; red `word L:int64`; `word 1:int64`;
    `word 256:int64`] MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_BLOCK in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral l,`l:num`; b,`b:num`]
          (SPEC_ALL(CONJUNCT2 invntt_blocks_c)))) in
  MP_TAC th THEN ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ENSURES_WEAKEN_TAC o CONV_RULE NUM_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[sth] THEN
    REPEAT CONJ_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;

(*** The layer head, setting up the registers for the first block ***)

let INVNTT_LAYERHEAD_TAC l =
  ENSURES_SEQUENCE_TAC `pc + mlk_poly_invntt_tomont_c_loop3` (invntt_blockhead_tm l
   `0`) THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[invntt_blocks_c] THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The exit from the block loop at the end of the layer ***)

let INVNTT_LAYEREXIT_TAC =
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The whole layer l (counting down from 7) ***)

let INVNTT_LAYER_TAC l =
  INVNTT_LAYERHEAD_TAC l THEN
  ENSURES_SEQUENCE_TAC
   `pc + mlk_poly_invntt_tomont_c_loop3_test` (invntt_blockend_tm l `1`) THEN
  CONJ_TAC THENL
   [INVNTT_BLOCK_TAC l `0`;
    if l = 1 then INVNTT_LAYEREXIT_TAC else
    ENSURES_WHILE_UP_TAC (mk_small_numeral(1 lsl (l - 1) - 1))
      `pc + mlk_poly_invntt_tomont_c_loop3_test` `pc + mlk_poly_invntt_tomont_c_loop3_test`
      (mk_abs(`i:num`,invntt_blockend_tm l `i + 1`)) THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ENSURES_SEQUENCE_TAC
       `pc + mlk_poly_invntt_tomont_c_loop3` (invntt_blockhead_tm l `i + 1`) THEN
      CONJ_TAC THENL
       [ENSURES_INIT_TAC "s0" THEN
        ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--1) THEN
        W32_DECIDE_FLAGS_TAC THEN
        ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (2--2) THEN
        ZETA_UXTW_TAC
         (rhs(concl(NUM_REDUCE_CONV
           (subst [mk_small_numeral l,`L:num`] `2 EXP L - 1 - (i + 1)`)))) THEN
        ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (3--4) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
        INVNTT_BLOCK_TAC l `i + 1`];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[];
      INVNTT_LAYEREXIT_TAC]];;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_LAYER_STMT =
  `!a (consts:num) zetas pc l r.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                   (word zetas,256)] /\
     l < 7
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O2_mono_mc /\
               read PC s = word(pc + mlk_poly_invntt_tomont_c_loop2) /\
               read X4 s = word 4294963967 /\
               read X6 s =
               word_zx(word_sx(iword(EL (2 EXP (l + 1) - 1) mlk_zetas)
                               :int16):int32) /\
               read X7 s = word 4294963969 /\
               read X8 s = word 33554432 /\ read X9 s = word 20159 /\
               read X14 s = word zetas /\ read X15 s = a /\
               read X16 s = word_add a (word 2) /\
               read X17 s = word(l + 1) /\ read X18 s = word 1 /\
               read X30 s = word 256 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        r i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O2_mono_mc /\
               read PC s = word(pc + mlk_poly_invntt_tomont_c_loop3_exit) /\
               read X4 s = word 4294963967 /\
               read X7 s = word 4294963969 /\
               read X8 s = word 33554432 /\ read X9 s = word 20159 /\
               read X14 s = word zetas /\ read X15 s = a /\
               read X16 s = word_add a (word 2) /\
               read X17 s = word(l + 1) /\ read X18 s = word 1 /\
               read X30 s = word 256 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        invntt_blocks_c (l + 1) (2 EXP l) r i))
          (MAYCHANGE [PC; X0; X1; X2; X5; X3; X10; X11; X12; X6; X13; X19] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_LAYER =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_LAYER_STMT;;

(* ------------------------------------------------------------------------- *)
(* All the layers, after the scaling of the coefficients.                    *)
(* ------------------------------------------------------------------------- *)

(*** Assertions at the layer head and layer end for layer l ***)

let invntt_layerhead_tm,invntt_layerend_tm =
  let headtm =
   `\s. aligned_bytes_loaded s (word pc)
          mlkem_native_libmlkem_gcc12_O2_mono_mc /\
        read X4 s = word 4294963967 /\
        read X6 s =
        word_zx(word_sx(iword(EL (2 EXP L - 1) mlk_zetas):int16):int32) /\
        read X7 s = word 4294963969 /\
        read X8 s = word 33554432 /\ read X9 s = word 20159 /\
        read X14 s = word zetas /\ read X15 s = a /\
        read X16 s = word_add a (word 2) /\
        read X17 s = word L /\ read X18 s = word 1 /\
        read X30 s = word 256 /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 invntt_layers_c (7 - L) x i)`
  and endtm =
   `\s. aligned_bytes_loaded s (word pc)
          mlkem_native_libmlkem_gcc12_O2_mono_mc /\
        read X4 s = word 4294963967 /\
        read X7 s = word 4294963969 /\
        read X8 s = word 33554432 /\ read X9 s = word 20159 /\
        read X14 s = word zetas /\ read X15 s = a /\
        read X16 s = word_add a (word 2) /\
        read X17 s = word L /\ read X18 s = word 1 /\
        read X30 s = word 256 /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 invntt_layers_c (8 - L) x i)` in
  let mk tm l =
    let tm' = subst [mk_small_numeral l,`L:num`] tm in
    rhs(concl(NUM_REDUCE_CONV tm')) in
  (fun l -> mk headtm l),(fun l -> mk endtm l);;

(*** Apply the lemma for layer l at its head ***)

let INVNTT_LAYER_APPLY_TAC l =
  let th = SPECL [`a:int64`; `consts:num`; `zetas:num`; `pc:num`;
                  mk_small_numeral(l - 1);
                  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`]
                     `invntt_layers_c (7 - L) x`)))]
                 MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_LAYER in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral(7 - l),`n:num`]
          (SPEC_ALL(CONJUNCT2 invntt_layers_c)))) in
  MP_TAC th THEN ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN ENSURES_WEAKEN_TAC THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[sth];
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;

(*** Going from the end of layer l to the head of the next layer ***)

let INVNTT_LAYERBACK_TAC l =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (2--4) THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mlk_zetas` (concl th)
    then MP_TAC(CONV_RULE NUM_REDUCE_CONV
                  (SPEC (mk_small_numeral(1 lsl (l - 1) - 1)) th))
    else failwith "") THEN
  REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (5--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_LAYERS_STMT =
  `!a (consts:num) zetas (x:num->int16) pc.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    zetas = pc + rodata_mlk_zetas /\
    ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                  (word zetas,256)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O2_mono_mc /\
           read PC s = word(pc + mlk_poly_invntt_tomont_c_loop1_exit) /\
           read X15 s = a /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = word(pc + mlk_poly_invntt_tomont_c_loop2_exit) /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    invntt_layers_c 7 x i))
      (MAYCHANGE [PC; X0; X1; X2; X5; X3; X10; X11; X12; X4; X6; X13; X7;
                  X8; X9; X14; X16; X17; X18; X19; X30] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_LAYERS =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_LAYERS_STMT;;

(* ------------------------------------------------------------------------- *)
(* The computation of the C code gives the inverse NTT, within the same      *)
(* bounds as the hand-written kernel. In fact all the coefficients stay      *)
(* below 3329 in absolute value, because of the reductions in every layer.   *)
(* ------------------------------------------------------------------------- *)

let INVNTT_BLOCKS_C_CLOSED_STMT =
  `!l b r i.
     invntt_blocks_c l b r i =
     if i < 2 * 2 EXP (8 - l) * b
     then let z = iword(EL (2 EXP l - 1 - i DIV (2 * 2 EXP (8 - l)))
                           mlk_zetas) in
          if i MOD (2 * 2 EXP (8 - l)) < 2 EXP (8 - l)
          then barred(word_add (r i) (r(i + 2 EXP (8 - l))))
          else invntt_fqmul_c z (word_sub (r i) (r(i - 2 EXP (8 - l))))
     else r i`;;

let INVNTT_BLOCKS_C_CLOSED = assume_spec INVNTT_BLOCKS_C_CLOSED_STMT;;

let INVNTT_LAYERS_C_STEP_STMT =
  `!n x i.
     n < 7 /\ i < 256
     ==> invntt_layers_c (SUC n) x i =
         let z = iword(EL (2 EXP (7 - n) - 1 -
                           i DIV (2 * 2 EXP (8 - (7 - n)))) mlk_zetas) in
         if i MOD (2 * 2 EXP (8 - (7 - n))) < 2 EXP (8 - (7 - n))
         then barred(word_add (invntt_layers_c n x i)
                        (invntt_layers_c n x (i + 2 EXP (8 - (7 - n)))))
         else invntt_fqmul_c z
                (word_sub (invntt_layers_c n x i)
                          (invntt_layers_c n x (i - 2 EXP (8 - (7 - n)))))`;;

let INVNTT_LAYERS_C_STEP = assume_spec INVNTT_LAYERS_C_STEP_STMT;;

let MLK_ZETAS_ELS =
  map (fun k -> (REWRITE_CONV[mlk_zetas] THENC EL_CONV)
                 (mk_comb(mk_comb(`EL:num->int list->int`,mk_small_numeral k),
                          `mlk_zetas`))) (0--127);;

(*** The equation for coefficient i after layer n + 1, starting from the ***)
(*** scaled coefficients.                                                ***)

let INVNTT_LAYER_EQUATION =
  let conv =
    NUM_REDUCE_CONV THENC TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV(CONJUNCT1 invntt_layers_c :: invntt_scale_c ::
                 MONTRED_NEON_SCALAR :: MLK_ZETAS_ELS) THENC
    ONCE_DEPTH_CONV WORD_IWORD_CONV THENC REWRITE_CONV[invntt_fqmul_c] THENC
    DEPTH_CONV WORD_RED_CONV in
  fun n i ->
    let th = SPECL [mk_small_numeral n; `invntt_scale_c x`;
                    mk_small_numeral i] INVNTT_LAYERS_C_STEP in
    let th' = MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))) in
    CONV_RULE(BINOP_CONV conv) th';;

(*** The congruences and bounds for all the layers, in order ***)

let INVNTT_LAYERS_CONGBOUND =
  MLKEM_NATIVE_LOCAL_CONGBOUND_RULE undefined
   (map (fun (n,i) -> SYM(INVNTT_LAYER_EQUATION n i))
        (List.concat (map (fun n -> map (fun i -> (n,i)) (0--255)) (0--6))));;

let INVNTT_FINAL_TAC =
  W(fun (asl,w) ->
    let tm = find_term
      (can (term_match [] `invntt_layers_c 7 (invntt_scale_c x) i`)) w in
    let th = apply INVNTT_LAYERS_CONGBOUND tm in
    if not(fst(dest_const(repeat rator w)) = "int_le") then
      MP_TAC(CONJUNCT1 th) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
      CONV_TAC(ONCE_DEPTH_CONV INVERSE_NTT_CONV) THEN
      REWRITE_TAC[GSYM INT_REM_EQ; o_THM] THEN CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC[INT_REM_EQ] THEN INT_LINEAR_CONG_TAC
    else
      MP_TAC(CONJUNCT2 th) THEN INT_ARITH_TAC);;

let INVNTT_LAYERS_C_CORRECT_STMT =
  `!x i. i < 256
         ==> (ival(invntt_layers_c 7 (invntt_scale_c x) i) ==
              inverse_ntt (ival o x) i) (mod &3329) /\
             abs(ival(invntt_layers_c 7 (invntt_scale_c x) i)) <= &26624`;;

let INVNTT_LAYERS_C_CORRECT = assume_spec INVNTT_LAYERS_C_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The scaling of the coefficients at the start, which also saves X19 and    *)
(* X30 on the stack.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_SCALE_STMT =
  `!a (x:num->int16) pc stackpointer x19 x30.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 stackpointer /\
    ALL (nonoverlapping (a,512))
        [(word pc,libmlkem_size); (word_sub stackpointer (word 16),16)] /\
    nonoverlapping (word_sub stackpointer (word 16),16) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O2_mono_mc /\
           read PC s = word (pc + mlk_poly_invntt_tomont_c) /\
           read X0 s = a /\ read SP s = stackpointer /\
           read X19 s = x19 /\ read X30 s = x30 /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = word(pc + mlk_poly_invntt_tomont_c_loop1_exit) /\
           read X15 s = a /\
           read SP s = word_sub stackpointer (word 16) /\
           read(memory :> bytes64(word_sub stackpointer (word 16))) s = x19 /\
           read(memory :> bytes64(word_add (word_sub stackpointer (word 16))
                                  (word 8))) s = x30 /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    invntt_scale_c x i))
      (MAYCHANGE [PC; X0; X1; X15; SP] ,,
       MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512);
                  memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_SCALE =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_SCALE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. Since X19 and X30 are saved after the start, this is   *)
(* stated directly for the whole subroutine, with the scaling and the layers *)
(* as big steps.                                                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_Z_STMT =
  `!a zetas x pc stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    zetas = pc + rodata_mlk_zetas /\
    aligned 16 stackpointer /\
    ALL (nonoverlapping (a,512))
        [(word pc,libmlkem_size); (word zetas,256);
         (word_sub stackpointer (word 16),16)] /\
    nonoverlapping (word_sub stackpointer (word 16),16) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O2_mono_mc /\
           read PC s = word (pc + mlk_poly_invntt_tomont_c) /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           !i. i < 256
               ==> let zi =
                     read(memory :> bytes16(word_add a (word(2 * i)))) s in
                   (ival zi == inverse_ntt (ival o x) i) (mod &3329) /\
                   abs(ival zi) <= &26624)
      (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                  X13; X14; X15; X16; X17; X18] ,,
       MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512);
                  memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_Z =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_Z_STMT;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a x pc stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 stackpointer /\
    ALL (nonoverlapping (a,512))
        [(word pc,libmlkem_size); (word_sub stackpointer (word 16),16)] /\
    nonoverlapping (word_sub stackpointer (word 16),16) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O2_mono_mc /\
           read PC s = word (pc + mlk_poly_invntt_tomont_c) /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           !i. i < 256
               ==> let zi =
                     read(memory :> bytes16(word_add a (word(2 * i)))) s in
                   (ival zi == inverse_ntt (ival o x) i) (mod &3329) /\
                   abs(ival zi) <= &26624)
      (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                  X13; X14; X15; X16; X17; X18] ,,
       MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512);
                  memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. This follows the structure of the  *)
(* correctness proof, with the events of a block and of each layer given by  *)
(* functions obtained from the corresponding lemmas. All the lemmas use the  *)
(* same regions as the whole subroutine, which also includes the stack.      *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** One block, from its setup through the inner loop ***)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_BLOCK_SAFE_STMT =
  `exists f_ev_blk.
   forall e a consts zetas pc sp start len k w17 w18 w30 returnaddress
          x19v.
     ALL (nonoverlapping (a,512))
         [(word pc,libmlkem_size); (word zetas,256); (sp,16)] /\
     1 <= len /\ start + 2 * len <= 256 /\ 1 <= k /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O2_mono_mc /\
               read PC s = word(pc + mlk_poly_invntt_tomont_c_loop3) /\
               read X10 s = word(start + len) /\ read X11 s = word start /\
               read X12 s = word k /\ read X13 s = word(2 * len) /\
               read X14 s = word zetas /\ read X15 s = a /\
               read X16 s = word_add a (word 2) /\
               read X17 s = w17 /\ read X18 s = w18 /\ read X30 s = w30 /\
               read SP s = sp /\
               read(memory :> bytes64(word_add sp (word 8))) s =
               returnaddress /\
               read(memory :> bytes64 sp) s = x19v /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O2_mono_mc /\
               read PC s = word(pc + mlk_poly_invntt_tomont_c_loop3_test) /\
               read X10 s = word(start + 3 * len) /\
               read X11 s = word(start + 2 * len) /\
               read X12 s = word(k - 1) /\ read X13 s = word(2 * len) /\
               read X14 s = word zetas /\ read X15 s = a /\
               read X16 s = word_add a (word 2) /\
               read X17 s = w17 /\ read X18 s = w18 /\ read X30 s = w30 /\
               read SP s = sp /\
               read(memory :> bytes64(word_add sp (word 8))) s =
               returnaddress /\
               read(memory :> bytes64 sp) s = x19v /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_blk a consts zetas pc start len /\
                 memaccess_inbounds e2
                  [a,512; sp,16; word consts,32; word zetas,256]
                  [a,512; sp,16])
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                      X12; X13; X14; X15; X16; X17; X18] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [X18; X19; X30] ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_BLOCK_SAFE =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_BLOCK_SAFE_STMT;;

let INVNTT_GCC12_O2_MONO_BLOCK_EVENTS =
  new_specification ["invntt_gcc12_O2_mono_block_events"]
                    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_BLOCK_SAFE;;

(*** One layer, for each of the seven layers ***)

let lsafe_goal l =
  let tm =
  `exists f_ev_lay.
    forall e a consts zetas pc sp returnaddress x19v.
     ALL (nonoverlapping (a,512))
         [(word pc,libmlkem_size); (word zetas,256); (sp,16)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O2_mono_mc /\
               read PC s = word(pc + mlk_poly_invntt_tomont_c_loop2) /\
               read X14 s = word zetas /\ read X15 s = a /\
               read X16 s = word_add a (word 2) /\
               read X17 s = word L /\ read X18 s = word 1 /\
               read X30 s = word 256 /\
               read SP s = sp /\
               read(memory :> bytes64(word_add sp (word 8))) s =
               returnaddress /\
               read(memory :> bytes64 sp) s = x19v /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O2_mono_mc /\
               read PC s = word(pc + mlk_poly_invntt_tomont_c_loop3_exit) /\
               read X14 s = word zetas /\ read X15 s = a /\
               read X16 s = word_add a (word 2) /\
               read X17 s = word L /\ read X18 s = word 1 /\
               read X30 s = word 256 /\
               read SP s = sp /\
               read(memory :> bytes64(word_add sp (word 8))) s =
               returnaddress /\
               read(memory :> bytes64 sp) s = x19v /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_lay a consts zetas pc /\
                 memaccess_inbounds e2
                  [a,512; sp,16; word consts,32; word zetas,256]
                  [a,512; sp,16])
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                      X12; X13; X14; X15; X16; X17; X18] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [X18; X19; X30] ,,
           MAYCHANGE [memory :> bytes(a,512)])` in
  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`] tm)));;

(*** The event template for layer l ***)

let lsafe_template l =
  let len = mk_small_numeral(1 lsl (8 - l)) in
  if l = 1 then
   subst [len,`LEN:num`]
   `\(a:int64) (consts:num) (zetas:num) (pc:num).
      APPEND (f_ev_ltest0 a consts zetas pc)
       (APPEND (invntt_gcc12_O2_mono_block_events a consts zetas pc 0 LEN)
               (f_ev_lhead a consts zetas pc))
     :(uarch_event)list`
  else
   subst [len,`LEN:num`; mk_small_numeral(1 lsl (l - 1) - 1),`K:num`]
   `\(a:int64) (consts:num) (zetas:num) (pc:num).
      APPEND (f_ev_lexit a consts zetas pc)
       (APPEND
         (ENUMERATEL K
           (\i. APPEND (f_ev_ltest a consts zetas pc i)
                 (APPEND (invntt_gcc12_O2_mono_block_events a consts zetas pc
                                           (2 * LEN * (i + 1)) LEN)
                         (f_ev_lzeta a consts zetas pc i))))
         (APPEND (f_ev_ltest0 a consts zetas pc)
           (APPEND (invntt_gcc12_O2_mono_block_events a consts zetas pc 0 LEN)
                   (f_ev_lhead a consts zetas pc))))
     :(uarch_event)list`;;

(*** The block lemma for block b of layer l ***)

let invntt_block_events_inst l b ev =
  let red t = rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (8 - l)),`LEN:num`;
      b,`B:num`] t))) in
  SPECL [ev; `a:int64`; `consts:num`; `zetas:num`; `pc:num`;
         `sp:int64`; red `2 * LEN * B`; red `LEN:num`;
         red `2 EXP L - 1 - B`; red `word L:int64`; `word 1:int64`;
         `word 256:int64`; `returnaddress:int64`; `x19v:int64`]
        INVNTT_GCC12_O2_MONO_BLOCK_EVENTS;;

(*** Register state at the block head and block end (b blocks done) ***)

let lsafe_blockhead_tm,lsafe_blockend_tm =
  let headtm =
   `\s. read X10 s = word(2 * LEN * B + LEN) /\
        read X11 s = word(2 * LEN * B) /\
        read X12 s = word(2 EXP L - 1 - B) /\ read X13 s = word(2 * LEN) /\
        read X14 s = word zetas /\ read X15 s = a /\
        read X16 s = word_add a (word 2) /\
        read X17 s = word L /\ read X18 s = word 1 /\
        read X30 s = word 256 /\
        read SP s = sp /\
        read(memory :> bytes64(word_add sp (word 8))) s = returnaddress /\
        read(memory :> bytes64 sp) s = x19v` in
  let mk l b =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (8 - l)),`LEN:num`;
      b,`B:num`] headtm))) in
  mk,mk;;

(*** The test at the end of a block, with K blocks after the first ***)

let LSAFE_TEST_TAC k =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (fun (asl,w) ->
     match find_terms is_cond w with
       [] -> ALL_TAC (asl,w)
     | tms ->
         let c = rand(rator(rator(hd(sort (fun a b -> free_in b a) tms)))) in
         if c = subst [k,`K:num`] `i + 1 < K` then ALL_TAC (asl,w) else
         (SUBGOAL_THEN (mk_eq(c,subst [k,`K:num`] `~(i + 1 < K)`))
          SUBST_ALL_TAC THENL [ARITH_TAC ORELSE ASM_ARITH_TAC; ALL_TAC])
         (asl,w)) THEN
  REPEAT(CONJ_TAC THENL
   [REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ((AP_TERM_TAC THEN ARITH_TAC) ORELSE ARITH_TAC ORELSE ASM_ARITH_TAC);
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** Simulation of a short piece of straight-line code with flags ***)

let LSAFE_SIM_TAC pre_tac n =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN pre_tac THEN
  MAP_EVERY (fun i ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC [i] THEN
    TRY W32_DECIDE_FLAGS_TAC) (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REPEAT(CONJ_TAC THENL
   [REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ((AP_TERM_TAC THEN ARITH_TAC) ORELSE ARITH_TAC ORELSE ASM_ARITH_TAC);
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The whole safety proof for layer l ***)

let INVNTT_LAYER_SAFE_TAC l =
  let k = mk_small_numeral(1 lsl (l - 1) - 1) in
  let blk0_tac =
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mlk_poly_invntt_tomont_c_loop3_test` (lsafe_blockend_tm l `1`) THEN
    CONJ_TAC THENL
     [ENSURES_EVENTS_SEQUENCE_TAC
      `pc + mlk_poly_invntt_tomont_c_loop3` (lsafe_blockhead_tm l `0`) THEN
      CONJ_TAC THENL
       [LSAFE_SIM_TAC ALL_TAC 6;
        EVENTS_LEMMA_TAC (invntt_block_events_inst l `0`)];
      LSAFE_SIM_TAC ALL_TAC 2] in
  CONCRETIZE_F_EVENTS_TAC (lsafe_template l) THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL;
              SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  if l = 1 then blk0_tac else
  ENSURES_EVENTS_WHILE_UP2_TAC k `pc + mlk_poly_invntt_tomont_c_loop3_next`
   `pc + mlk_poly_invntt_tomont_c_loop3_exit`
   (mk_abs(`i:num`,lsafe_blockend_tm l `i + 1`)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    REWRITE_TAC[ENUMERATEL; APPEND] THEN CONV_TAC NUM_REDUCE_CONV THEN
    blk0_tac;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mlk_poly_invntt_tomont_c_loop3_test`
      (lsafe_blockend_tm l `i + 1 + 1`) THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
      ENSURES_EVENTS_SEQUENCE_TAC `pc + mlk_poly_invntt_tomont_c_loop3`
        (lsafe_blockhead_tm l `i + 1`) THEN
      CONJ_TAC THENL
       [LSAFE_SIM_TAC
         (let n = rhs(concl(NUM_REDUCE_CONV
                   (subst [mk_small_numeral l,`L:num`]
                          `2 EXP L - 1 - (i + 1)`))) in
          MP_TAC(SPEC n VAL_WORD_ZX_UXTW) THEN
          ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC]) 2;
        EVENTS_LEMMA_TAC (invntt_block_events_inst l `i + 1`)];
      LSAFE_TEST_TAC k];
    LSAFE_SIM_TAC ALL_TAC 0];;

let INVNTT_GCC12_O2_MONO_LAYER_EVENTS = assuming_proofs (fun () ->
  map (fun l ->
        new_specification ["invntt_gcc12_O2_mono_layer_events_" ^ string_of_int l]
                          (prove(lsafe_goal l,INVNTT_LAYER_SAFE_TAC l)))
      (1--7));;

(*** The scaling at the start, including saving X19 and X30 ***)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_SCALE_SAFE_STMT =
  `exists f_ev_scale.
    forall e a consts zetas pc sp returnaddress x19v.
     aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
     consts = pc + mlk_poly_invntt_tomont_c_consts /\
     zetas = pc + rodata_mlk_zetas /\ aligned 16 sp /\
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size); (sp,16)] /\
     nonoverlapping (sp,16) (word pc,libmlkem_size)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O2_mono_mc /\
               read PC s = word (pc + mlk_poly_invntt_tomont_c) /\
               read X0 s = a /\ read SP s = word_add sp (word 16) /\
               read X30 s = returnaddress /\ read X19 s = x19v /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O2_mono_mc /\
               read PC s = word(pc + mlk_poly_invntt_tomont_c_loop1_exit) /\
               read X15 s = a /\
               read SP s = sp /\
               read(memory :> bytes64(word_add sp (word 8))) s =
               returnaddress /\
               read(memory :> bytes64 sp) s = x19v /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_scale a consts zetas pc sp /\
                 memaccess_inbounds e2
                  [a,512; sp,16; word consts,32; word zetas,256]
                  [a,512; sp,16])
          (MAYCHANGE [PC; X0; X1; X15; SP] ,,
           MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512); memory :> bytes(sp,16)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_SCALE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_SCALE_SAFE_STMT;;

let INVNTT_GCC12_O2_MONO_SCALE_EVENTS =
  new_specification ["invntt_gcc12_O2_mono_scale_events"]
                    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_SCALE_SAFE;;

(*** The whole code, which has the same signature as mlkem_reduce, with ***)
(*** the vectors of constants and table of zetas as read-only objects.  ***)
(*** The stack pointer after saving X19 and X30 is the parameter sp.    ***)

let invntt_top_template =
  let lay l = list_mk_comb
   (mk_const("invntt_gcc12_O2_mono_layer_events_" ^ string_of_int l,[]),
    [`a:int64`;`consts:num`;`zetas:num`;`pc:num`])
  and scale = `invntt_gcc12_O2_mono_scale_events a consts zetas pc sp`
  and fev n =
    list_mk_comb
     (mk_var(n,`:int64->num->num->num->int64->int64->(uarch_event)list`),
      [`a:int64`;`consts:num`;`zetas:num`;`pc:num`;`sp:int64`;
       `returnaddress:int64`]) in
  let app x y = list_mk_icomb "APPEND" [x;y] in
  let rec chain l acc =
    let acc' = app (lay l) acc in
    if l = 1 then acc' else
    chain (l - 1) (app (fev ("f_ev_back" ^ string_of_int l)) acc') in
  let body = app (fev "f_ev_fin") (chain 7 (app (fev "f_ev_init") scale)) in
  list_mk_abs([`a:int64`;`consts:num`;`zetas:num`;`pc:num`;`sp:int64`;
               `returnaddress:int64`],body);;

let invntt_safe_layer_tm,invntt_safe_scaleend_tm =
  let tm =
   `\s. read X14 s = word zetas /\ read X15 s = a /\
        read X16 s = word_add a (word 2) /\
        read X17 s = word L /\ read X18 s = word 1 /\
        read X30 s = word 256 /\ read SP s = stackpointer /\
        read(memory :> bytes64(word_add stackpointer (word 8))) s =
        returnaddress /\
        read(memory :> bytes64 stackpointer) s = x19_init`
  and stm =
   `\s. read X15 s = a /\ read SP s = stackpointer /\
        read(memory :> bytes64(word_add stackpointer (word 8))) s =
        returnaddress /\
        read(memory :> bytes64 stackpointer) s = x19_init` in
  (fun l -> rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`]
                                             tm)))),stm;;

let invntt_layer_events_inst l ev =
  SPECL [ev; `a:int64`; `consts:num`; `zetas:num`; `pc:num`;
         `stackpointer:int64`; `returnaddress:int64`; `x19_init:int64`]
        (el (l - 1) INVNTT_GCC12_O2_MONO_LAYER_EVENTS);;

let INVNTT_SAFE_TOP_TAC =
  CONCRETIZE_F_EVENTS_TAC invntt_top_template THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV NORMALIZE_ALIGNED_WORD_CONV)) THEN
  FIRST_X_ASSUM(fun eq ->
    if is_eq(concl eq) && lhand(concl eq) = `consts:num`
    then (consts_eq := eq; ALL_TAC) else failwith "") THEN
  FIRST_X_ASSUM(fun eq ->
    if is_eq(concl eq) && lhand(concl eq) = `zetas:num`
    then (zeta_eq := eq; ALL_TAC) else failwith "") THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN

  (*** Restoring X19 and X30 and returning after the last layer ***)

  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlk_poly_invntt_tomont_c_loop3_exit` (invntt_safe_layer_tm 1) THEN
  CONJ_TAC THENL [ALL_TAC; LSAFE_SIM_TAC ALL_TAC 4] THEN

  (*** The layers, with the code between them ***)

  MAP_EVERY (fun l ->
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mlk_poly_invntt_tomont_c_loop2` (invntt_safe_layer_tm l) THEN
    CONJ_TAC THENL
     [ALL_TAC; EVENTS_LEMMA_TAC (invntt_layer_events_inst l)] THEN
    if l = 7 then ALL_TAC else
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mlk_poly_invntt_tomont_c_loop3_exit`
      (invntt_safe_layer_tm (l + 1)) THEN
    CONJ_TAC THENL [ALL_TAC; LSAFE_SIM_TAC ALL_TAC 6]) (1--7) THEN

  (*** The scaling, and the setup for the first layer ***)

  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlk_poly_invntt_tomont_c_loop1_exit` invntt_safe_scaleend_tm THEN
  CONJ_TAC THENL
   [(fun g -> MAP_EVERY ASSUME_TAC [!consts_eq; !zeta_eq] g) THEN
    MP_TAC(SPECL [`e:(uarch_event)list`; `a:int64`; `consts:num`;
                  `zetas:num`; `pc:num`; `stackpointer:int64`;
                  `returnaddress:int64`; `x19_init:int64`]
                 INVNTT_GCC12_O2_MONO_SCALE_EVENTS) THEN
    ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
    DISCH_THEN ENSURES_WEAKEN_TAC THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[SOME_FLAGS; SOME_FLAGS] THEN
      SUBSUMED_MAYCHANGE_TAC];
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    (fun g -> ASSUME_TAC !zeta_eq g) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (2--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_SAFE_Z_STMT =
  `exists f_events.
     forall e a consts zetas pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       consts = pc + mlk_poly_invntt_tomont_c_consts /\
       zetas = pc + rodata_mlk_zetas /\
       aligned 16 stackpointer /\
       ALL (nonoverlapping (a,512))
           [word pc,libmlkem_size; word zetas,256;
            word_sub stackpointer (word 16),16] /\
       nonoverlapping (word_sub stackpointer (word 16),16)
         (word pc,libmlkem_size)
       ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                read PC s = word (pc + mlk_poly_invntt_tomont_c) /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a] s /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a consts zetas pc
                         (word_sub stackpointer (word 16)) returnaddress /\
                  memaccess_inbounds e2
                   [a,512; word_sub stackpointer (word 16),16;
                    word consts,32; word zetas,256]
                   [a,512; word_sub stackpointer (word 16),16])
           (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                       X12; X13; X14; X15; X16; X17; X18] ,,
            MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_SAFE_Z =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_SAFE_Z_STMT;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e a pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       ALL (nonoverlapping (a,512))
           [word pc,libmlkem_size; word_sub stackpointer (word 16),16] /\
       nonoverlapping (word_sub stackpointer (word 16),16)
         (word pc,libmlkem_size)
       ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                read PC s = word (pc + mlk_poly_invntt_tomont_c) /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a] s /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a pc
                         (word_sub stackpointer (word 16)) returnaddress /\
                  memaccess_inbounds e2
                   [a,512; word_sub stackpointer (word 16),16;
                    word (pc + mlk_poly_invntt_tomont_c_consts),32;
                    word (pc + rodata_mlk_zetas),256]
                   [a,512; word_sub stackpointer (word 16),16])
           (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                       X12; X13; X14; X15; X16; X17; X18] ,,
            MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT;;
