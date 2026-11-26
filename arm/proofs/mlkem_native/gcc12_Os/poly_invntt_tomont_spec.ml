(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* Inverse number-theoretic transform from ML-KEM.                         *)
(* This is the code for mlkem_poly_invntt_tomont from mlkem-native's       *)
(* portable C implementation compiled by gcc 12 with -Os (see              *)
(* mlkem_native/README.md), verified in the whole image (see libmlkem.ml). *)
(* The statements are those of the -O2 code, except that the safety        *)
(* theorem lists no read-only block of constants.                          *)
(*                                                                         *)
(* At -Os the code is not unrolled or vectorized. A loop over the 256      *)
(* coefficients scales them, with 16-bit loads and stores. Then it has the *)
(* three nested loops of the C code: the layers (X5 counts down from 7),   *)
(* the blocks of a layer (X6 is the start of the block, X3 the start of    *)
(* its upper half) and the butterflies of a block (X8 and X9 point at the  *)
(* coefficients of the lower and upper half). It loads the zeta of a block *)
(* from the table of zetas by its index (X7, counting down). It uses no    *)
(* stack and reads no constants other than that table, so the stack frame  *)
(* of 16 bytes in its statements, as at -O2, stays unchanged.              *)
(*                                                                         *)
(*      +0x0  mov     x2, #0x0                                             *)
(*      +0x4  mov     w6, #0x5a1                                           *)
(*      +0x8  mov     w5, #0xfffff301                                      *)
(*      +0xc  mov     w4, #0xfffff2ff                                      *)
(*   loop1:                                                                *)
(*     +0x10  ldrsh   w3, [x0, x2, lsl #1]                                 *)
(*     +0x14  mul     w3, w3, w6                                           *)
(*     +0x18  mul     w1, w3, w5                                           *)
(*     +0x1c  sxth    w1, w1                                               *)
(*     +0x20  madd    w1, w1, w4, w3                                       *)
(*     +0x24  asr     w1, w1, #16                                          *)
(*     +0x28  strh    w1, [x0, x2, lsl #1]                                 *)
(*     +0x2c  add     x2, x2, #0x1                                         *)
(*   loop1_test:                                                           *)
(*     +0x30  cmp     x2, #0x100                                           *)
(*   loop1_back:                                                           *)
(*     +0x34  b.ne    loop1                                                *)
(*   loop1_exit: adrp1:                                                    *)
(*     +0x38  adrp    x10, <page>                                          *)
(*     +0x3c  mov     w4, w2                                               *)
(*     +0x40  add     x10, x10, #0xb00                                     *)
(*                    // rodata_mlk_zetas                                  *)
(*     +0x44  mov     w5, #0x7                                             *)
(*     +0x48  mov     w13, #0x1                                            *)
(*     +0x4c  mov     w14, #0x4ebf                                         *)
(*     +0x50  mov     w15, #0x2000000                                      *)
(*     +0x54  mov     w11, #0xfffff2ff                                     *)
(*     +0x58  mov     w16, #0xfffff301                                     *)
(*   loop2:                                                                *)
(*     +0x5c  lsr     w3, w4, w5                                           *)
(*     +0x60  mov     w6, #0x0                                             *)
(*     +0x64  lsl     w7, w13, w5                                          *)
(*     +0x68  lsl     w12, w3, #1                                          *)
(*     +0x6c  sub     w7, w7, #0x1                                         *)
(*   loop3:                                                                *)
(*     +0x70  mov     w1, w7                                               *)
(*     +0x74  sub     w7, w7, #0x1                                         *)
(*     +0x78  ldrsh   w17, [x10, w1, uxtw #1]                              *)
(*     +0x7c  cmp     w6, w3                                               *)
(*     +0x80  b.cs    join1                                                *)
(*     +0x84  mov     w8, w6                                               *)
(*     +0x88  add     x9, x0, w3, uxtw #1                                  *)
(*   loop4:                                                                *)
(*     +0x8c  ldrsh   w18, [x0, x8, lsl #1]                                *)
(*     +0x90  ldrh    w1, [x9]                                             *)
(*     +0x94  add     w1, w18, w1                                          *)
(*     +0x98  sxth    w1, w1                                               *)
(*     +0x9c  madd    w2, w1, w14, w15                                     *)
(*     +0xa0  asr     w2, w2, #26                                          *)
(*     +0xa4  madd    w1, w2, w11, w1                                      *)
(*     +0xa8  strh    w1, [x0, x8, lsl #1]                                 *)
(*     +0xac  add     x8, x8, #0x1                                         *)
(*     +0xb0  ldrh    w1, [x9]                                             *)
(*     +0xb4  sub     w1, w1, w18                                          *)
(*     +0xb8  sxth    w1, w1                                               *)
(*     +0xbc  mul     w1, w1, w17                                          *)
(*     +0xc0  mul     w2, w1, w16                                          *)
(*     +0xc4  sxth    w2, w2                                               *)
(*     +0xc8  madd    w1, w2, w11, w1                                      *)
(*     +0xcc  asr     w1, w1, #16                                          *)
(*     +0xd0  strh    w1, [x9], #2                                         *)
(*   loop4_test:                                                           *)
(*     +0xd4  cmp     w3, w8                                               *)
(*   loop4_back:                                                           *)
(*     +0xd8  b.hi    loop4                                                *)
(*   join1: loop4_exit:                                                    *)
(*     +0xdc  add     w6, w6, w12                                          *)
(*     +0xe0  add     w3, w3, w12                                          *)
(*   loop3_test:                                                           *)
(*     +0xe4  cmp     w6, #0xff                                            *)
(*   loop3_back:                                                           *)
(*     +0xe8  b.ls    loop3                                                *)
(*   loop3_exit: loop2_test:                                               *)
(*     +0xec  subs    w5, w5, #0x1                                         *)
(*   loop2_back:                                                           *)
(*     +0xf0  b.ne    loop2                                                *)
(*   loop2_exit: ret:                                                      *)
(*     +0xf4  ret                                                          *)
(*                                                                         *)
(* The proof of correctness has a loop for the scaling, a loop for the     *)
(* layers, a loop for the blocks of a layer (for each of the seven layers) *)
(* and a loop for the butterflies of a block. The proof of memory safety   *)
(* does the seven layers one after the other, as at -O2.                   *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;
needs "common/int_linear.ml";;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_poly_invntt_tomont"];;

(* ------------------------------------------------------------------------- *)
(* The computation done by the C code, with its 16-bit and 32-bit integer    *)
(* arithmetic. The coefficients are first scaled by a Montgomery             *)
(* multiplication by 1441 = 2^25 mod 3329. Then the inverse NTT is done in 7 *)
(* layers, for l = 7 down to 1, layer l consisting of 2^(l-1) blocks of      *)
(* 2^(9-l) consecutive coefficients. A block uses one zeta to do butterflies *)
(* on pairs of coefficients 2^(8-l) apart, independently, with a Barrett     *)
(* reduction of the sums.                                                    *)
(* ------------------------------------------------------------------------- *)

let invntt_scale_c = define
 `invntt_scale_c (x:num->int16) i =
    montred_scalar(word_mul (word_sx(x i)) (word 1441))`;;

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

(*** Prepare a load of zeta number n using UXTW indexing ***)

let ZETA_UXTW_TAC n =
  MP_TAC(SPEC n VAL_WORD_ZX_UXTW) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mlk_zetas` (concl th)
    then MP_TAC(SPEC n th) else failwith "") THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* One block, from the load of its zeta through the inner loop and the       *)
(* update of the start and the end of the block.                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_BLOCK_STMT =
  `!a zetas pc start len k (m:num->int16) w4 w5 w13 w30.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                   (word zetas,256)] /\
     1 <= len /\ start + 2 * len <= 256 /\ 1 <= k /\ k < 128
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3) /\
               read X0 s = a /\ read X3 s = word(start + len) /\
               read X4 s = w4 /\ read X5 s = w5 /\ read X6 s = word start /\
               read X7 s = word k /\ read X10 s = word zetas /\
               read X11 s = word 4294963967 /\
               read X12 s = word(2 * len) /\ read X13 s = w13 /\
               read X14 s = word 20159 /\ read X15 s = word 33554432 /\
               read X16 s = word 4294963969 /\ read X30 s = w30 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        m i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3_test) /\
               read X0 s = a /\ read X3 s = word(start + 3 * len) /\
               read X4 s = w4 /\ read X5 s = w5 /\
               read X6 s = word(start + 2 * len) /\
               read X7 s = word(k - 1) /\ read X10 s = word zetas /\
               read X11 s = word 4294963967 /\
               read X12 s = word(2 * len) /\ read X13 s = w13 /\
               read X14 s = word 20159 /\ read X15 s = word 33554432 /\
               read X16 s = word 4294963969 /\ read X30 s = w30 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        invntt_block_c (iword(EL k mlk_zetas)) start len m i))
          (MAYCHANGE [PC; X1; X2; X3; X6; X7; X8; X9; X17; X18] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_BLOCK =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_BLOCK_STMT;;

(*** Rewrite the assumption that gives the value of register r ***)

let REG_REWRITE_TAC r ths =
  FIRST_X_ASSUM(fun th ->
    let l,t = dest_eq(concl th) in
    if is_comb l && is_comb(rator l) && rand(rator l) = r
    then ASSUME_TAC(REWRITE_RULE ths th)
    else failwith "REG_REWRITE_TAC");;

(* ------------------------------------------------------------------------- *)
(* One layer, with its blocks in a loop.                                     *)
(* ------------------------------------------------------------------------- *)

(*** Assertion at the head of the block loop, with b blocks of layer l done.
 *** At the test at its end it is the same assertion, with the number of
 *** the blocks done one higher.
 ***)

let invntt_blockhead_tm =
  let headtm =
   `\s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_Os_mc /\
        read X0 s = a /\ read X3 s = word(2 * LEN * B + LEN) /\
        read X4 s = word 256 /\ read X5 s = word L /\
        read X6 s = word(2 * LEN * B) /\
        read X7 s = word(2 EXP L - 1 - B) /\ read X10 s = word zetas /\
        read X11 s = word 4294963967 /\
        read X12 s = word(2 * LEN) /\ read X13 s = word 1 /\
        read X14 s = word 20159 /\ read X15 s = word 33554432 /\
        read X16 s = word 4294963969 /\ read X30 s = w30 /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 invntt_blocks_c L B r i)` in
  fun l b ->
    let len = mk_small_numeral(1 lsl (8 - l)) in
    let tm' = subst [mk_small_numeral l,`L:num`; len,`LEN:num`; b,`B:num`]
                    headtm in
    rhs(concl(NUM_REDUCE_CONV tm'));;

(*** The arithmetic side conditions: SIMPLE_ARITH_TAC, from the simple     ***)
(*** arithmetic facts, and only then ASM_ARITH_TAC, which is slow with the ***)
(*** many facts of the simulations; for an equation of words, also as the  ***)
(*** equation of their arguments (AP_TERM_TAC) before ASM_ARITH_TAC, which ***)
(*** fails slowly on it.                                                   ***)

let NTT_ARITH_TAC = SIMPLE_ARITH_TAC ORELSE ASM_ARITH_TAC;;

let NTT_EQ_ARITH_TAC =
  SIMPLE_ARITH_TAC ORELSE (AP_TERM_TAC THEN SIMPLE_ARITH_TAC) ORELSE
  ASM_ARITH_TAC ORELSE (AP_TERM_TAC THEN ASM_ARITH_TAC);;

(*** Apply the block lemma at the head of block b of layer l ***)

let INVNTT_BLOCK_TAC l b =
  let red t =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (8 - l)),`LEN:num`;
      b,`B:num`] t))) in
  let th = SPECL
   [`a:int64`; `zetas:num`; `pc:num`;
    red `2 * LEN * B`; red `LEN:num`; red `2 EXP L - 1 - B`;
    red `invntt_blocks_c L B r`; `word 256:int64`; red `word L:int64`;
    `word 1:int64`; `w30:int64`]
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_BLOCK in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral l,`l:num`; b,`b:num`]
          (SPEC_ALL(CONJUNCT2 invntt_blocks_c)))) in
  MP_TAC th THEN ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN NTT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ENSURES_WEAKEN_TAC o CONV_RULE NUM_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[sth] THEN
    REPEAT CONJ_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;

(*** The whole layer l (the value of the layer counter, from 7 down to 1) ***)

let INVNTT_LAYER_TAC l =
  let n = mk_small_numeral(1 lsl (l - 1)) in
  ENSURES_WHILE_UP_TAC n `pc + mlkem_poly_invntt_tomont_loop3`
    `pc + mlkem_poly_invntt_tomont_loop3_test`
    (mk_abs(`b:num`,invntt_blockhead_tm l `b:num`)) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    (*** The layer head, setting up the registers for the first block ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[invntt_blocks_c] THEN ASM_REWRITE_TAC[];

    (*** One block ***)

    X_GEN_TAC `b:num` THEN STRIP_TAC THEN INVNTT_BLOCK_TAC l `b:num`;

    (*** The back edge of the block loop ***)

    X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The exit from the block loop ***)

    ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_LAYER_STMT =
  `!a zetas pc l (r:num->int16) w30.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                   (word zetas,256)] /\
     l < 7
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop2) /\
               read X0 s = a /\ read X4 s = word 256 /\
               read X5 s = word(l + 1) /\ read X10 s = word zetas /\
               read X11 s = word 4294963967 /\ read X13 s = word 1 /\
               read X14 s = word 20159 /\ read X15 s = word 33554432 /\
               read X16 s = word 4294963969 /\ read X30 s = w30 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        r i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop2_test) /\
               read X0 s = a /\ read X4 s = word 256 /\
               read X5 s = word(l + 1) /\ read X10 s = word zetas /\
               read X11 s = word 4294963967 /\ read X13 s = word 1 /\
               read X14 s = word 20159 /\ read X15 s = word 33554432 /\
               read X16 s = word 4294963969 /\ read X30 s = w30 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        invntt_blocks_c (l + 1) (2 EXP l) r i))
          (MAYCHANGE [PC; X1; X2; X3; X6; X7; X8; X9; X12; X17; X18] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_LAYER =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_LAYER_STMT;;

(*** The loop over the seven layers ***)

let INVNTT_LAYERS_TAC =
  let sth = REWRITE_RULE[ADD1] (SPEC_ALL(CONJUNCT2 invntt_layers_c)) in
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `zetas:num`; `x:num->int16`; `pc:num`; `w30:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP2_TAC `7` `pc + mlkem_poly_invntt_tomont_loop2`
    `pc + mlkem_poly_invntt_tomont_loop2_exit`
   `\n s. aligned_bytes_loaded s (word pc)
            mlkem_native_libmlkem_gcc12_Os_mc /\
          read X0 s = a /\ read X4 s = word 256 /\
          read X5 s = word(7 - n) /\ read X10 s = word zetas /\
          read X11 s = word 4294963967 /\ read X13 s = word 1 /\
          read X14 s = word 20159 /\ read X15 s = word 33554432 /\
          read X16 s = word 4294963969 /\ read X30 s = w30 /\
          (!k. k < 128
               ==> read(memory :> bytes16(word_add (word zetas)
                                                   (word(2 * k)))) s =
                   iword(EL k mlk_zetas)) /\
          (!i. i < 256
               ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                   invntt_layers_c n x i)` THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    (*** The entry, with no layer done ***)

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[invntt_layers_c; SUB_0];

    (*** One layer and the decrement of the layer counter ***)

    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(6 - n) + 1 = 7 - n` ASSUME_TAC THENL
     [NTT_ARITH_TAC; ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC `pc + mlkem_poly_invntt_tomont_loop2_test`
     `\s. aligned_bytes_loaded s (word pc)
            mlkem_native_libmlkem_gcc12_Os_mc /\
          read X0 s = a /\ read X4 s = word 256 /\
          read X5 s = word(7 - n) /\ read X10 s = word zetas /\
          read X11 s = word 4294963967 /\ read X13 s = word 1 /\
          read X14 s = word 20159 /\ read X15 s = word 33554432 /\
          read X16 s = word 4294963969 /\ read X30 s = w30 /\
          (!k. k < 128
               ==> read(memory :> bytes16(word_add (word zetas)
                                                   (word(2 * k)))) s =
                   iword(EL k mlk_zetas)) /\
          (!i. i < 256
               ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                   invntt_layers_c (n + 1) x i)` THEN
    CONJ_TAC THENL
     [MP_TAC(SPECL [`a:int64`; `zetas:num`; `pc:num`; `6 - n`;
                    `invntt_layers_c n x`; `w30:int64`]
             MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_LAYER) THEN
      ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
      ANTS_TAC THENL [NTT_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(ENSURES_WEAKEN_TAC) THEN
      REPEAT CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[sth];
        REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (1--1) THEN
      W32_DECIDE_FLAGS_TAC THEN
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (2--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN NTT_ARITH_TAC;
        WORD_SMALL_TAC]];

    (*** The exit after the last layer ***)

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* The scaling of the coefficients at the start.                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_SCALE_STMT =
  `!a zetas (x:num->int16) pc w30.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                   (word zetas,256)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop1) /\
               read X0 s = a /\ read X2 s = word 0 /\
               read X4 s = word 4294963967 /\ read X5 s = word 4294963969 /\
               read X6 s = word 1441 /\ read X30 s = w30 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop1_exit) /\
               read X0 s = a /\ read X2 s = word 256 /\ read X30 s = w30 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        invntt_scale_c x i))
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_SCALE =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_SCALE_STMT;;

let INVNTT_SCALE_TAC =
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `zetas:num`; `x:num->int16`; `pc:num`; `w30:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC `256` `pc + mlkem_poly_invntt_tomont_loop1`
    `pc + mlkem_poly_invntt_tomont_loop1_test`
   `\i s. aligned_bytes_loaded s (word pc)
            mlkem_native_libmlkem_gcc12_Os_mc /\
          read X0 s = a /\ read X2 s = word i /\
          read X4 s = word 4294963967 /\ read X5 s = word 4294963969 /\
          read X6 s = word 1441 /\ read X30 s = w30 /\
          (!k. k < 128
               ==> read(memory :> bytes16(word_add (word zetas)
                                                   (word(2 * k)))) s =
                   iword(EL k mlk_zetas)) /\
          (!j. j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   if j < i then invntt_scale_c x j else x j)` THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    (*** The entry ***)

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[LT];

    (*** One coefficient ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `x:num->int16` (concl th)
      then MP_TAC(SPEC `i:num` th) THEN
           ASSUME_TAC(BETA_RULE(MATCH_MP (SPEC
             `\j:num. ~(j = (i:num))`
             (MESON[] `!R P Q. (!i:num. P i ==> Q i)
                               ==> (!i. P i /\ R i ==> Q i)`)) th))
      else failwith "") THEN
    ANTS_TAC THENL [NTT_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 256 ==> ~(i < i)`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `val(word i:int64) = i` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      NTT_ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `j:num = i` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `i < i + 1`] THEN
      MLKEM_NATIVE_W_SIMP_TAC THEN REWRITE_TAC[WORD_ADD_0] THEN
      REWRITE_TAC[invntt_scale_c; montred_scalar];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      is_forall(concl th) && free_in `x:num->int16` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN NTT_ARITH_TAC;

    (*** The back edge ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The exit ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `x:num->int16` (concl th))) THEN
    ASM_REWRITE_TAC[]];;


(* ------------------------------------------------------------------------- *)
(* All the layers, after the scaling of the coefficients, with the loop      *)
(* over them. The layer counter in X5 counts down from 7.                    *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_LAYERS_STMT =
  `!a zetas (x:num->int16) pc w30.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                   (word zetas,256)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop2) /\
               read X0 s = a /\ read X4 s = word 256 /\
               read X5 s = word 7 /\ read X10 s = word zetas /\
               read X11 s = word 4294963967 /\ read X13 s = word 1 /\
               read X14 s = word 20159 /\ read X15 s = word 33554432 /\
               read X16 s = word 4294963969 /\ read X30 s = w30 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_ret) /\
               read X30 s = w30 /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        invntt_layers_c 7 x i))
          (MAYCHANGE [PC; X1; X2; X3; X5; X6; X7; X8; X9; X12; X17; X18] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_LAYERS =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_LAYERS_STMT;;

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
                 MLK_ZETAS_ELS) THENC
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
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_ZETAS_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_DATA_RULE mlk_zetas_data (layout "rodata_mlk_zetas");;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a x pc stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 stackpointer /\
    ALL (nonoverlapping (a,512))
        [(word pc,libmlkem_size); (word_sub stackpointer (word 16),16)] /\
    nonoverlapping (word_sub stackpointer (word 16),16) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_Os_mc /\
           read PC s = word (pc + mlkem_poly_invntt_tomont) /\
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
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
       MAYCHANGE [memory :> bytes(a,512);
                  memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. This follows the structure of the  *)
(* correctness proof, with the events of the scaling loop, of a block and of *)
(* each layer given by functions obtained from the corresponding lemmas.     *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The scaling loop ***)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_SCALE_SAFE_STMT =
  `exists f_ev_scale.
   forall e a pc returnaddress.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop1) /\
               read X0 s = a /\ read X2 s = word 0 /\
               read X30 s = returnaddress /\ read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop1_exit) /\
               read X0 s = a /\ read X2 s = word 256 /\
               read X30 s = returnaddress /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_scale a pc /\
                 memaccess_inbounds e2 [a,512] [a,512])
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_SCALE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_SCALE_SAFE_STMT;;

let INVNTT_GCC12_OS_SCALE_EVENTS =
  new_specification ["invntt_gcc12_Os_scale_events"]
                    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_SCALE_SAFE;;

(*** One block, from the load of its zeta through the inner loop ***)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_BLOCK_SAFE_STMT =
  `exists f_ev_blk.
   forall e a zetas pc start len k w4 w5 w13 returnaddress.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                   (word zetas,256)] /\
     1 <= len /\ start + 2 * len <= 256 /\ 1 <= k /\ k < 128
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3) /\
               read X0 s = a /\ read X3 s = word(start + len) /\
               read X4 s = w4 /\ read X5 s = w5 /\ read X6 s = word start /\
               read X7 s = word k /\ read X10 s = word zetas /\
               read X12 s = word(2 * len) /\ read X13 s = w13 /\
               read X30 s = returnaddress /\ read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3_test) /\
               read X0 s = a /\ read X3 s = word(start + 3 * len) /\
               read X4 s = w4 /\ read X5 s = w5 /\
               read X6 s = word(start + 2 * len) /\
               read X7 s = word(k - 1) /\ read X10 s = word zetas /\
               read X12 s = word(2 * len) /\ read X13 s = w13 /\
               read X30 s = returnaddress /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_blk a zetas pc start len k /\
                 memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
          (MAYCHANGE [PC; X1; X2; X3; X6; X7; X8; X9; X17; X18] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_BLOCK_SAFE =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_BLOCK_SAFE_STMT;;

let INVNTT_GCC12_OS_BLOCK_EVENTS =
  new_specification ["invntt_gcc12_Os_block_events"]
                    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_BLOCK_SAFE;;

(*** The events of a layer or of the scaling are in bounds for the regions
 *** of the whole code, which include the stack frame
 ***)

let MEMACCESS_WIDEN_TAC =
  FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Comb(Const("memaccess_inbounds",_),e),rr),wr) ->
        (fun (asl,w) ->
          match w with
            Comb(Comb(Comb(Const("memaccess_inbounds",_),e'),rr'),wr')
            when e' = e ->
              (MP_TAC(ISPECL [e;rr;rr';wr;wr'] MEMACCESS_INBOUNDS_MEM) THEN
               REWRITE_TAC[ALL; MEM] THEN DISCH_THEN MATCH_MP_TAC THEN
               ACCEPT_TAC th) (asl,w)
          | _ -> failwith "MEMACCESS_WIDEN_TAC")
    | _ -> failwith "MEMACCESS_WIDEN_TAC");;

(*** One layer, for each of the seven layers ***)

let lsafe_goal l =
  let tm =
  `exists f_ev_lay.
    forall e a zetas pc returnaddress.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                   (word zetas,256)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop2) /\
               read X0 s = a /\ read X4 s = word 256 /\
               read X5 s = word L /\ read X10 s = word zetas /\
               read X13 s = word 1 /\
               read X30 s = returnaddress /\ read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop2_test) /\
               read X0 s = a /\ read X4 s = word 256 /\
               read X5 s = word L /\ read X10 s = word zetas /\
               read X13 s = word 1 /\
               read X30 s = returnaddress /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_lay a zetas pc /\
                 memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
          (MAYCHANGE [PC; X1; X2; X3; X6; X7; X8; X9; X12; X17; X18] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])` in
  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`] tm)));;

(*** The event template for layer l ***)

let lsafe_template l =
  let len = mk_small_numeral(1 lsl (8 - l)) in
  subst [len,`LEN:num`; mk_small_numeral(1 lsl (l - 1)),`N:num`;
         mk_small_numeral(1 lsl l - 1),`P:num`]
   `\(a:int64) (zetas:num) (pc:num).
      APPEND []
       (APPEND
         (ENUMERATEL N
           (\i. APPEND (f_ev_ltest a zetas pc i)
                       (invntt_gcc12_Os_block_events a zetas pc
                                                     (2 * LEN * i) LEN
                                                     (P - i))))
         (f_ev_lhead a zetas pc))
     :(uarch_event)list`;;

(*** The block lemma for block b of layer l ***)

let invntt_block_events_inst l b ev =
  let red t = rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (8 - l)),`LEN:num`;
      b,`B:num`] t))) in
  SPECL [ev; `a:int64`; `zetas:num`; `pc:num`;
         red `2 * LEN * B`; red `LEN:num`; red `2 EXP L - 1 - B`;
         `word 256:int64`; red `word L:int64`; `word 1:int64`;
         `returnaddress:int64`]
        INVNTT_GCC12_OS_BLOCK_EVENTS;;

(*** Register state at the block head and block end (b blocks done) ***)

let lsafe_blockhead_tm =
  let headtm =
   `\s. read X0 s = a /\ read X3 s = word(2 * LEN * B + LEN) /\
        read X4 s = word 256 /\ read X5 s = word L /\
        read X6 s = word(2 * LEN * B) /\
        read X7 s = word(2 EXP L - 1 - B) /\ read X10 s = word zetas /\
        read X12 s = word(2 * LEN) /\ read X13 s = word 1 /\
        read X30 s = returnaddress` in
  fun l b ->
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (8 - l)),`LEN:num`;
      b,`B:num`] headtm)));;

(*** The test at the end of a block of a layer with n blocks ***)

let LSAFE_TEST_TAC n =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (fun (asl,w) ->
     match find_terms is_cond w with
       [] -> ALL_TAC (asl,w)
     | tms ->
         let c = rand(rator(rator(hd(sort (fun a b -> free_in b a) tms)))) in
         (SUBGOAL_THEN (mk_eq(c,subst [n,`N:num`] `i + 1 < N`))
           SUBST_ALL_TAC THENL [NTT_ARITH_TAC; ALL_TAC]) (asl,w)) THEN
  REPEAT(CONJ_TAC THENL
   [REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    NTT_EQ_ARITH_TAC;
    ALL_TAC]) THEN
  REWRITE_TAC[APPEND_NIL] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let INVNTT_LAYER_SAFE_TAC l =
  let n = mk_small_numeral(1 lsl (l - 1)) in
  CONCRETIZE_F_EVENTS_TAC (lsafe_template l) THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC n `pc + mlkem_poly_invntt_tomont_loop3`
   `pc + mlkem_poly_invntt_tomont_loop3_exit`
   (mk_abs(`i:num`,lsafe_blockhead_tm l `i:num`)) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    (*** The layer head ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** One block and the test of the block loop ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_invntt_tomont_loop3_test`
      (lsafe_blockhead_tm l `(i:num) + 1`) THEN
    CONJ_TAC THENL
     [EVENTS_LEMMA_TAC (invntt_block_events_inst l `i:num`);
      LSAFE_TEST_TAC n];

    (*** The exit ***)

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND; APPEND_NIL]) THEN
    REWRITE_TAC[APPEND; APPEND_NIL] THEN
    FIRST_X_ASSUM ACCEPT_TAC];;

let INVNTT_GCC12_OS_LAYER_EVENTS = assuming_proofs (fun () ->
  map (fun l ->
        new_specification ["invntt_gcc12_Os_layer_events_" ^ string_of_int l]
                          (prove(lsafe_goal l,INVNTT_LAYER_SAFE_TAC l)))
      (1--7));;

(*** The whole code, with the events of the scaling, of the layers and of
 *** the steps between them
 ***)

let invntt_top_template =
  let lay l = list_mk_comb(
     mk_const("invntt_gcc12_Os_layer_events_" ^ string_of_int l,[]),
     [`a:int64`; `pc + rodata_mlk_zetas`; `pc:num`])
  and fev n =
    list_mk_comb(mk_var(n,`:int64->num->int64->int64->(uarch_event)list`),
                 [`a:int64`;`pc:num`;`sp:int64`;`returnaddress:int64`]) in
  let app x y = list_mk_icomb "APPEND" [x;y] in
  let rec chain l acc =
    if l < 1 then acc else
    let acc' = app (lay l) acc in
    if l = 1 then acc' else
    chain (l - 1) (app (fev ("f_ev_back" ^ string_of_int l)) acc') in
  let scale = list_mk_comb(mk_const("invntt_gcc12_Os_scale_events",[]),
                           [`a:int64`; `pc:num`]) in
  let body = app (fev "f_ev_fin")
              (chain 7 (app (fev "f_ev_mid") (app scale (fev "f_ev_init")))) in
  list_mk_abs([`a:int64`;`pc:num`;`sp:int64`;`returnaddress:int64`],body);;

(*** The state at the head of layer l, which is also its state at the end ***)

let invntt_safe_layerhead_tm =
  let headtm =
   `\s. read X0 s = a /\ read X4 s = word 256 /\ read X5 s = word L /\
        read X10 s = word(pc + rodata_mlk_zetas) /\ read X13 s = word 1 /\
        read X30 s = returnaddress` in
  fun l ->
    rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`] headtm)));;

let invntt_layer_events_inst l ev =
  SPECL [ev; `a:int64`; `pc + rodata_mlk_zetas`; `pc:num`;
         `returnaddress:int64`]
        (el (l - 1) INVNTT_GCC12_OS_LAYER_EVENTS);;

let invntt_scale_events_inst ev =
  SPECL [ev; `a:int64`; `pc:num`; `returnaddress:int64`]
        INVNTT_GCC12_OS_SCALE_EVENTS;;

let INVNTT_SAFE_SIM_TAC n =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY (fun i ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC [i] THEN
    TRY W32_DECIDE_FLAGS_TAC) (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let INVNTT_SAFE_TOP_TAC =
  CONCRETIZE_F_EVENTS_TAC invntt_top_template THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `nonoverlapping (a:int64,512)
                  (word(pc + rodata_mlk_zetas),256)` ASSUME_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlkem_poly_invntt_tomont_loop2_test` (invntt_safe_layerhead_tm 1) THEN
  CONJ_TAC THENL [ALL_TAC; INVNTT_SAFE_SIM_TAC 3] THEN
  MAP_EVERY (fun l ->
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mlkem_poly_invntt_tomont_loop2` (invntt_safe_layerhead_tm l) THEN
    CONJ_TAC THENL [ALL_TAC; EVENTS_LEMMA_TAC (invntt_layer_events_inst l) THEN
                  MEMACCESS_WIDEN_TAC] THEN
    if l = 7 then ALL_TAC else
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mlkem_poly_invntt_tomont_loop2_test`
     (invntt_safe_layerhead_tm (l + 1)) THEN
    CONJ_TAC THENL [ALL_TAC; INVNTT_SAFE_SIM_TAC 2]) (1--7) THEN

  (*** The setup of the layer loop, with the address of the zetas ***)

  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlkem_poly_invntt_tomont_loop1_exit`
   `\s. read X0 s = a /\ read X2 s = word 256 /\
        read X30 s = returnaddress` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (2--9) THEN
    REG_REWRITE_TAC `X10` [GSYM WORD_ADD] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  (*** The scaling and the setup of the constants ***)

  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlkem_poly_invntt_tomont_loop1`
   `\s. read X0 s = a /\ read X2 s = word 0 /\ read X30 s = returnaddress` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    EVENTS_LEMMA_TAC invntt_scale_events_inst THEN MEMACCESS_WIDEN_TAC] THEN
  INVNTT_SAFE_SIM_TAC 4;;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + rodata_mlk_zetas):int64`,`256`]
    ~keep_maychanges:true
    (assoc "mlkem_reduce" subroutine_signatures)
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
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
                  mlkem_native_libmlkem_gcc12_Os_mc /\
                read PC s = word (pc + mlkem_poly_invntt_tomont) /\
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
                    word (pc + rodata_mlk_zetas),256]
                   [a,512; word_sub stackpointer (word 16),16])
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
