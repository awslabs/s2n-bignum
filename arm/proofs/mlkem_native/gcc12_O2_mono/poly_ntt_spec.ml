(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform from ML-KEM. This is the code for      *)
(* mlk_poly_ntt_c from mlkem-native's portable C implementation compiled     *)
(* by gcc 12 with -O2 as one translation unit (see                           *)
(* mlkem_native/README.md). It is the same as mlkem_poly_ntt of the          *)
(* separate -O2 build up to the allocation of registers and a NOP before     *)
(* the first loop. Unlike the hand-written kernel, it reads its own table    *)
(* of zetas from the read-only data rather than taking tables as             *)
(* arguments. It is verified in the whole image (see libmlkem.ml), with      *)
(* the proof for the separate -O2 build adapted to the image: the            *)
(* registers are renamed, and the table of zetas is at pc +                  *)
(* rodata_mlk_zetas.                                                         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;
needs "common/int_linear.ml";;

(*** The equation that the table of zetas is at pc + rodata_mlk_zetas is ***)
(*** only assumed where the address is computed, since it would ruin the ***)
(*** matching of the other assumptions, which are about word zetas.      ***)

let zeta_eq = ref TRUTH;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_ZETAS_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_DATA_RULE mlk_zetas_data (layout "rodata_mlk_zetas");;

(*** The code in the image:

    mlk_poly_ntt_c:
       +0x0: adrp    x13, <page>
       +0x4: mov     x14, x0
       +0x8: add     x13, x13, #0xd20
       +0xc: add     x15, x0, #0x2
      +0x10: mov     w11, #0x0
      +0x14: mov     w6, #0xfffffd0a
      +0x18: mov     w17, #0x1
      +0x1c: mov     w18, #0x100
      +0x20: mov     w8, #0xfffff301
      +0x24: mov     w7, #0xfffff2ff
      +0x28: add     w16, w11, #0x1
      +0x2c: mov     w9, #0x0
      +0x30: lsl     w11, w17, w11
      +0x34: lsr     w10, w18, w16
      +0x38: lsl     w12, w10, #1
      +0x3c: nop
      +0x40: add     w11, w11, #0x1           <----+ |
      +0x44: cmp     w10, w9                       | |
      +0x48: b.ls    <mlk_poly_ntt_c+0xa8>                    ---+ | |
      +0x4c: sub     w5, w10, w9                 | | |
      +0x50: mov     w0, w9                      | | |
      +0x54: sub     w5, w5, #0x1                | | |
      +0x58: mov     w4, w10                     | | |
      +0x5c: add     x5, x5, x0                  | | |
      +0x60: sub     x4, x4, x0                  | | |
      +0x64: add     x1, x14, w9, uxtw #1        | | |
      +0x68: add     x5, x15, x5, lsl #1         | | |
      +0x6c: nop     | | |
      +0x70: ldrsh   w2, [x1, x4, lsl #1]     <+ | | |
      +0x74: ldrh    w3, [x1]                  | | | |
      +0x78: mul     w2, w2, w6                | | | |
      +0x7c: mul     w0, w2, w8                | | | |
      +0x80: sxth    w0, w0                    | | | |
      +0x84: madd    w0, w0, w7, w2            | | | |
      +0x88: asr     w0, w0, #16               | | | |
      +0x8c: sub     w2, w3, w0                | | | |
      +0x90: strh    w2, [x1, x4, lsl #1]      | | | |
      +0x94: ldrh    w2, [x1]                  | | | |
      +0x98: add     w0, w0, w2                | | | |
      +0x9c: strh    w0, [x1], #2              | | | |
      +0xa0: cmp     x5, x1                    | | | |
      +0xa4: b.ne    <mlk_poly_ntt_c+0x70>                    -+ | | |
      +0xa8: add     w9, w9, w12              <--+ | |
      +0xac: add     w10, w10, w12                 | |
      +0xb0: cmp     w9, #0xff                     | |
      +0xb4: b.hi    <mlk_poly_ntt_c+0xc0>               -+   | |
      +0xb8: ldrsh   w6, [x13, w11, uxtw #1]   |   | |
      +0xbc: b       <mlk_poly_ntt_c+0x40>                    -----+ |
      +0xc0: cmp     w16, #0x7
      +0xc4: b.eq    <mlk_poly_ntt_c+0xd8>
      +0xc8: lsl     w0, w17, w16
      +0xcc: mov     w11, w16
      +0xd0: ldrsh   w6, [x13, x0, lsl #1]
      +0xd4: b       <mlk_poly_ntt_c+0x28>
      +0xd8: ret
 ***)

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlk_poly_ntt_c"];;

(* ------------------------------------------------------------------------- *)
(* The computation done by the C code, with its 16-bit and 32-bit integer    *)
(* arithmetic. The NTT is done in 7 layers, layer l+1 consisting of 2^l      *)
(* blocks of 2^(8-l) consecutive coefficients. A block uses one zeta to do   *)
(* butterflies on pairs of coefficients 2^(7-l) apart, independently.        *)
(* ------------------------------------------------------------------------- *)

let ntt_fqmul_c = define
 `ntt_fqmul_c (z:int16) (y:int16) =
    montred_scalar(word_mul (word_sx y) (word_sx z))`;;

let ntt_block_c = define
 `ntt_block_c (z:int16) start len (m:num->int16) i =
    if start <= i /\ i < start + len
    then word_add (m i) (ntt_fqmul_c z (m(i + len)))
    else if start + len <= i /\ i < start + 2 * len
    then word_sub (m(i - len)) (ntt_fqmul_c z (m i))
    else m i`;;

let ntt_blocks_c = define
 `ntt_blocks_c l 0 (r:num->int16) = r /\
  ntt_blocks_c l (SUC b) r =
    ntt_block_c (iword(EL (2 EXP l + b) mlk_zetas))
                (2 * 2 EXP (7 - l) * b) (2 EXP (7 - l))
                (ntt_blocks_c l b r)`;;

let ntt_layers_c = define
 `ntt_layers_c 0 (x:num->int16) = x /\
  ntt_layers_c (SUC l) x = ntt_blocks_c l (2 EXP l) (ntt_layers_c l x)`;;

(* ------------------------------------------------------------------------- *)
(* One block, from its setup through the inner loop.                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_BLOCK_STMT =
  `!a zetas pc z start len k m w15 w16 w17.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                   (word zetas,256)] /\
     1 <= len /\ start + 2 * len <= 256 /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O2_mono_mc /\
               read PC s = word(pc + mlk_poly_ntt_c_loop2) /\
               read X9 s = word start /\ read X10 s = word(start + len) /\
               read X11 s = word k /\
               read X6 s = word_zx(word_sx z:int32) /\
               read X12 s = word(2 * len) /\
               read X7 s = word 4294963967 /\ read X8 s = word 4294963969 /\
               read X13 s = word zetas /\ read X14 s = a /\
               read X15 s = word_add a (word 2) /\
               read X16 s = w15 /\ read X17 s = w16 /\ read X18 s = w17 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        m i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O2_mono_mc /\
               read PC s = word(pc + mlk_poly_ntt_c_loop2_test) /\
               read X9 s = word(start + 2 * len) /\
               read X10 s = word(start + 3 * len) /\
               read X11 s = word(k + 1) /\
               read X6 s = word_zx(word_sx z:int32) /\
               read X12 s = word(2 * len) /\
               read X7 s = word 4294963967 /\ read X8 s = word 4294963969 /\
               read X13 s = word zetas /\ read X14 s = a /\
               read X15 s = word_add a (word 2) /\
               read X16 s = w15 /\ read X17 s = w16 /\ read X18 s = w17 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        ntt_block_c z start len m i))
          (MAYCHANGE [PC; X0; X1; X5; X4; X9; X2; X10; X11; X3] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_BLOCK =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_BLOCK_STMT;;

(* ------------------------------------------------------------------------- *)
(* One layer, with the blocks in a loop (except for the first layer).        *)
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

let ntt_blockhead_tm,ntt_blockend_tm =
  let headtm =
   `\s. aligned_bytes_loaded s (word pc)
          mlkem_native_libmlkem_gcc12_O2_mono_mc /\
        read X9 s = word(2 * LEN * B) /\
        read X10 s = word(2 * LEN * B + LEN) /\
        read X11 s = word(2 EXP L + B) /\
        read X6 s =
        word_zx(word_sx(iword(EL (2 EXP L + B) mlk_zetas):int16):int32) /\
        read X12 s = word(2 * LEN) /\
        read X7 s = word 4294963967 /\ read X8 s = word 4294963969 /\
        read X13 s = word zetas /\ read X14 s = a /\
        read X15 s = word_add a (word 2) /\
        read X16 s = word(L + 1) /\ read X17 s = word 1 /\
        read X18 s = word 256 /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 ntt_blocks_c L B r i)`
  and endtm =
   `\s. aligned_bytes_loaded s (word pc)
          mlkem_native_libmlkem_gcc12_O2_mono_mc /\
        read X9 s = word(2 * LEN * B) /\
        read X10 s = word(2 * LEN * B + LEN) /\
        read X11 s = word(2 EXP L + B) /\
        read X12 s = word(2 * LEN) /\
        read X7 s = word 4294963967 /\ read X8 s = word 4294963969 /\
        read X13 s = word zetas /\ read X14 s = a /\
        read X15 s = word_add a (word 2) /\
        read X16 s = word(L + 1) /\ read X17 s = word 1 /\
        read X18 s = word 256 /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 ntt_blocks_c L B r i)` in
  let mk tm l b =
    let len = mk_small_numeral(1 lsl (7 - l)) in
    let tm' = subst [mk_small_numeral l,`L:num`; len,`LEN:num`; b,`B:num`]
                    tm in
    rhs(concl(NUM_REDUCE_CONV tm')) in
  (fun l b -> mk headtm l b),(fun l b -> mk endtm l b);;

(*** Apply NTT_BLOCK at the head of block b of layer l ***)

let NTT_BLOCK_TAC l b =
  let red t =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (7 - l)),`LEN:num`;
      b,`B:num`] t))) in
  let th = SPECL
   [`a:int64`; `zetas:num`; `pc:num`;
    red `iword(EL (2 EXP L + B) mlk_zetas):int16`;
    red `2 * LEN * B`; red `LEN:num`; red `2 EXP L + B`;
    red `ntt_blocks_c L B r`; red `word(L + 1):int64`; `word 1:int64`;
    `word 256:int64`] MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_BLOCK in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral l,`l:num`; b,`b:num`]
          (SPEC_ALL(CONJUNCT2 ntt_blocks_c)))) in
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

let NTT_LAYERHEAD_TAC l =
  ENSURES_SEQUENCE_TAC `pc + mlk_poly_ntt_c_loop2` (ntt_blockhead_tm l `0`) THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[ntt_blocks_c] THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The exit from the block loop at the end of the layer ***)

let NTT_LAYEREXIT_TAC =
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The whole layer l (number of layers done before it) ***)

let NTT_LAYER_TAC l =
  NTT_LAYERHEAD_TAC l THEN
  ENSURES_SEQUENCE_TAC `pc + mlk_poly_ntt_c_loop2_test` (ntt_blockend_tm l `1`) THEN
  CONJ_TAC THENL
   [NTT_BLOCK_TAC l `0`;
    if l = 0 then NTT_LAYEREXIT_TAC else
    ENSURES_WHILE_UP_TAC (mk_small_numeral(1 lsl l - 1))
      `pc + mlk_poly_ntt_c_loop2_test` `pc + mlk_poly_ntt_c_loop2_test`
      (mk_abs(`i:num`,ntt_blockend_tm l `i + 1`)) THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ENSURES_SEQUENCE_TAC `pc + mlk_poly_ntt_c_loop2` (ntt_blockhead_tm l
       `i + 1`) THEN
      CONJ_TAC THENL
       [ENSURES_INIT_TAC "s0" THEN
        ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (1--1) THEN
        W32_DECIDE_FLAGS_TAC THEN
        ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (2--2) THEN
        ZETA_UXTW_TAC
         (rhs(concl(NUM_REDUCE_CONV
           (subst [mk_small_numeral l,`L:num`] `2 EXP L + i + 1`)))) THEN
        ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (3--4) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
        NTT_BLOCK_TAC l `i + 1`];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[];
      NTT_LAYEREXIT_TAC]];;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_LAYER_STMT =
  `!a zetas pc l r w8.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                   (word zetas,256)] /\
     l < 7
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O2_mono_mc /\
               read PC s = word(pc + mlk_poly_ntt_c_loop1) /\
               read X11 s = word l /\
               read X6 s =
               word_zx(word_sx(iword(EL (2 EXP l) mlk_zetas):int16):int32) /\
               read X7 s = word 4294963967 /\ read X8 s = word 4294963969 /\
               read X13 s = word zetas /\ read X14 s = a /\
               read X15 s = word_add a (word 2) /\
               read X17 s = word 1 /\ read X18 s = word 256 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        r i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O2_mono_mc /\
               read PC s = word(pc + mlk_poly_ntt_c_loop2_exit) /\
               read X16 s = word(l + 1) /\
               read X7 s = word 4294963967 /\ read X8 s = word 4294963969 /\
               read X13 s = word zetas /\ read X14 s = a /\
               read X15 s = word_add a (word 2) /\
               read X17 s = word 1 /\ read X18 s = word 256 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        ntt_blocks_c l (2 EXP l) r i))
          (MAYCHANGE [PC; X0; X1; X5; X4; X9; X2; X10; X11; X6; X12; X16; X3] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_LAYER =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_LAYER_STMT;;

(* ------------------------------------------------------------------------- *)
(* The computation of the C code gives the NTT, within the same bounds as    *)
(* the hand-written kernel.                                                  *)
(* ------------------------------------------------------------------------- *)

let NTT_BLOCKS_C_CLOSED_STMT =
  `!l b r i.
     ntt_blocks_c l b r i =
     if i < 2 * 2 EXP (7 - l) * b
     then let z = iword(EL (2 EXP l + i DIV (2 * 2 EXP (7 - l))) mlk_zetas) in
          if i MOD (2 * 2 EXP (7 - l)) < 2 EXP (7 - l)
          then word_add (r i) (ntt_fqmul_c z (r(i + 2 EXP (7 - l))))
          else word_sub (r(i - 2 EXP (7 - l))) (ntt_fqmul_c z (r i))
     else r i`;;

let NTT_BLOCKS_C_CLOSED = assume_spec NTT_BLOCKS_C_CLOSED_STMT;;

let NTT_LAYERS_C_STEP_STMT =
  `!l x i.
     l < 7 /\ i < 256
     ==> ntt_layers_c (SUC l) x i =
         let z = iword(EL (2 EXP l + i DIV (2 * 2 EXP (7 - l))) mlk_zetas) in
         if i MOD (2 * 2 EXP (7 - l)) < 2 EXP (7 - l)
         then word_add (ntt_layers_c l x i)
                       (ntt_fqmul_c z (ntt_layers_c l x (i + 2 EXP (7 - l))))
         else word_sub (ntt_layers_c l x (i - 2 EXP (7 - l)))
                       (ntt_fqmul_c z (ntt_layers_c l x i))`;;

let NTT_LAYERS_C_STEP = assume_spec NTT_LAYERS_C_STEP_STMT;;

let MLK_ZETAS_ELS =
  map (fun k -> (REWRITE_CONV[mlk_zetas] THENC EL_CONV)
                 (mk_comb(mk_comb(`EL:num->int list->int`,mk_small_numeral k),
                          `mlk_zetas`))) (0--127);;

let NTT_LAYER_EQUATION =
  let conv =
    NUM_REDUCE_CONV THENC TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV(CONJUNCT1 ntt_layers_c :: MLK_ZETAS_ELS) THENC
    ONCE_DEPTH_CONV WORD_IWORD_CONV THENC REWRITE_CONV[ntt_fqmul_c] THENC
    DEPTH_CONV WORD_RED_CONV in
  fun l i ->
    let th = SPECL [mk_small_numeral l; `x:num->int16`; mk_small_numeral i]
                   NTT_LAYERS_C_STEP in
    let th' = MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))) in
    CONV_RULE(BINOP_CONV conv) th';;

(*** All the layer equations, in the order of the layers ***)

let NTT_LAYER_EQUATIONS =
  map (fun (l,i) -> SYM(NTT_LAYER_EQUATION l i))
      (List.concat (map (fun l -> map (fun i -> (l,i)) (0--255)) (0--6)));;

let NTT_FINAL_TAC lfn =
  W(fun (asl,w) ->
    let tm = find_term (can (term_match [] `ntt_layers_c 7 x i`)) w in
    let th = apply lfn tm in
    if not(fst(dest_const(repeat rator w)) = "int_le") then
      MP_TAC(CONJUNCT1 th) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
      CONV_TAC(ONCE_DEPTH_CONV FORWARD_NTT_CONV) THEN
      REWRITE_TAC[GSYM INT_REM_EQ; o_THM] THEN CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC[INT_REM_EQ] THEN INT_LINEAR_CONG_TAC
    else
      MP_TAC(CONJUNCT2 th) THEN INT_ARITH_TAC);;

let NTT_LAYERS_C_CORRECT_STMT =
  `!x. (!i. i < 256 ==> abs(ival(x i)) <= &8191)
       ==> !i. i < 256
               ==> (ival(ntt_layers_c 7 x i) == forward_ntt (ival o x) i)
                   (mod &3329) /\
                   abs(ival(ntt_layers_c 7 x i)) <= &23594`;;

let NTT_LAYERS_C_CORRECT = assume_spec NTT_LAYERS_C_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The whole code computes the C version of the NTT.                         *)
(* ------------------------------------------------------------------------- *)

(*** Assertions at the layer head and layer end for layer l ***)

let ntt_layerhead_tm,ntt_layerend_tm =
  let headtm =
   `\s. aligned_bytes_loaded s (word pc)
          mlkem_native_libmlkem_gcc12_O2_mono_mc /\
        read X11 s = word L /\
        read X6 s =
        word_zx(word_sx(iword(EL (2 EXP L) mlk_zetas):int16):int32) /\
        read X7 s = word 4294963967 /\ read X8 s = word 4294963969 /\
        read X13 s = word zetas /\ read X14 s = a /\
        read X15 s = word_add a (word 2) /\
        read X17 s = word 1 /\ read X18 s = word 256 /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 ntt_layers_c L x i)`
  and endtm =
   `\s. aligned_bytes_loaded s (word pc)
          mlkem_native_libmlkem_gcc12_O2_mono_mc /\
        read X16 s = word(L + 1) /\
        read X7 s = word 4294963967 /\ read X8 s = word 4294963969 /\
        read X13 s = word zetas /\ read X14 s = a /\
        read X15 s = word_add a (word 2) /\
        read X17 s = word 1 /\ read X18 s = word 256 /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 ntt_layers_c (L + 1) x i)` in
  let mk tm l =
    let tm' = subst [mk_small_numeral l,`L:num`] tm in
    rhs(concl(NUM_REDUCE_CONV tm')) in
  (fun l -> mk headtm l),(fun l -> mk endtm l);;

(*** Apply the lemma for layer l at its head ***)

let NTT_LAYER_APPLY_TAC l =
  let th = SPECL [`a:int64`; `zetas:num`; `pc:num`; mk_small_numeral l;
                  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`]
                     `ntt_layers_c L x`)))]
                 MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_LAYER in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral l,`l:num`]
          (SPEC_ALL(CONJUNCT2 ntt_layers_c)))) in
  MP_TAC th THEN ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN ENSURES_WEAKEN_TAC THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[sth];
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;

(*** Going from the end of layer l to the head of the next layer ***)

let NTT_LAYERBACK_TAC l =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (2--4) THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mlk_zetas` (concl th)
    then MP_TAC(CONV_RULE NUM_REDUCE_CONV
                  (SPEC (mk_small_numeral(1 lsl (l + 1))) th))
    else failwith "") THEN
  REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (5--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_LAYERS_STMT =
  `!a zetas (x:num->int16) pc.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    zetas = pc + rodata_mlk_zetas /\
    ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size); (word zetas,256)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O2_mono_mc /\
           read PC s = word (pc + mlk_poly_ntt_c) /\
           C_ARGUMENTS [a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = word(pc + mlk_poly_ntt_c_ret) /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    ntt_layers_c 7 x i))
      (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                  X13; X14; X15; X16; X17; X18] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_LAYERS =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_LAYERS_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_CORRECT_STMT =
  `!a (x:num->int16) pc.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (a,512) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O2_mono_mc /\
           read PC s = word (pc + mlk_poly_ntt_c) /\
           C_ARGUMENTS [a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = word(pc + mlk_poly_ntt_c_ret) /\
           ((!i. i < 256 ==> abs(ival(x i)) <= &8191)
            ==> !i. i < 256
                    ==> let zi =
                          read(memory :> bytes16(word_add a (word(2 * i)))) s
                        in (ival zi == forward_ntt (ival o x) i) (mod &3329) /\
                           abs(ival zi) <= &23594))
      (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                  X13; X14; X15; X16; X17; X18] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a (x:num->int16) pc returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (a,512) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O2_mono_mc /\
           read PC s = word (pc + mlk_poly_ntt_c) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           ((!i. i < 256 ==> abs(ival(x i)) <= &8191)
            ==> !i. i < 256
                    ==> let zi =
                          read(memory :> bytes16(word_add a (word(2 * i)))) s
                        in (ival zi == forward_ntt (ival o x) i) (mod &3329) /\
                           abs(ival zi) <= &23594))
      (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                  X13; X14; X15; X16; X17; X18] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. This follows the structure of the  *)
(* correctness proof, with the events of a block and of each layer given by  *)
(* functions obtained from the corresponding lemmas.                         *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** One block, from its setup through the inner loop ***)

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_BLOCK_SAFE_STMT =
  `exists f_ev_blk.
   forall e a zetas pc start len k w15 w16 w17 returnaddress.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                   (word zetas,256)] /\
     1 <= len /\ start + 2 * len <= 256 /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O2_mono_mc /\
               read PC s = word(pc + mlk_poly_ntt_c_loop2) /\
               read X9 s = word start /\ read X10 s = word(start + len) /\
               read X11 s = word k /\ read X12 s = word(2 * len) /\
               read X13 s = word zetas /\ read X14 s = a /\
               read X15 s = word_add a (word 2) /\
               read X16 s = w15 /\ read X17 s = w16 /\ read X18 s = w17 /\
               read X30 s = returnaddress /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O2_mono_mc /\
               read PC s = word(pc + mlk_poly_ntt_c_loop2_test) /\
               read X9 s = word(start + 2 * len) /\
               read X10 s = word(start + 3 * len) /\
               read X11 s = word(k + 1) /\ read X12 s = word(2 * len) /\
               read X13 s = word zetas /\ read X14 s = a /\
               read X15 s = word_add a (word 2) /\
               read X16 s = w15 /\ read X17 s = w16 /\ read X18 s = w17 /\
               read X30 s = returnaddress /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_blk a zetas pc returnaddress start len /\
                 memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                      X12; X13; X14; X15; X16; X17; X18] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_BLOCK_SAFE =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_BLOCK_SAFE_STMT;;

let NTT_GCC12_O2_MONO_BLOCK_EVENTS =
  new_specification ["ntt_gcc12_O2_mono_block_events"]
                    MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_BLOCK_SAFE;;

(*** One layer, for each of the seven layers ***)

let lsafe_goal l =
  let tm =
  `exists f_ev_lay.
    forall e a zetas pc returnaddress.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size); (word zetas,256)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O2_mono_mc /\
               read PC s = word(pc + mlk_poly_ntt_c_loop1) /\
               read X11 s = word L /\ read X13 s = word zetas /\
               read X14 s = a /\ read X15 s = word_add a (word 2) /\
               read X17 s = word 1 /\ read X18 s = word 256 /\
               read X30 s = returnaddress /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O2_mono_mc /\
               read PC s = word(pc + mlk_poly_ntt_c_loop2_exit) /\
               read X16 s = word(L + 1) /\ read X13 s = word zetas /\
               read X14 s = a /\ read X15 s = word_add a (word 2) /\
               read X17 s = word 1 /\ read X18 s = word 256 /\
               read X30 s = returnaddress /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_lay a zetas pc returnaddress /\
                 memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                      X12; X13; X14; X15; X16; X17; X18] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])` in
  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`] tm)));;

(*** The event template for layer l ***)

let lsafe_template l =
  let len = mk_small_numeral(1 lsl (7 - l)) in
  if l = 0 then
   subst [len,`LEN:num`]
   `\(a:int64) (zetas:num) (pc:num) (returnaddress:int64).
      APPEND (f_ev_ltest0 a zetas pc returnaddress)
       (APPEND (ntt_gcc12_O2_mono_block_events a zetas pc returnaddress 0 LEN)
               (f_ev_lhead a zetas pc returnaddress))
     :(uarch_event)list`
  else
   subst [len,`LEN:num`; mk_small_numeral(1 lsl l - 1),`K:num`]
   `\(a:int64) (zetas:num) (pc:num) (returnaddress:int64).
      APPEND (f_ev_lexit a zetas pc returnaddress)
       (APPEND
         (ENUMERATEL K
           (\i. APPEND (f_ev_ltest a zetas pc returnaddress i)
                 (APPEND (ntt_gcc12_O2_mono_block_events a zetas pc returnaddress
                                           (2 * LEN * (i + 1)) LEN)
                         (f_ev_lzeta a zetas pc returnaddress i))))
         (APPEND (f_ev_ltest0 a zetas pc returnaddress)
           (APPEND (ntt_gcc12_O2_mono_block_events a zetas pc returnaddress 0 LEN)
                   (f_ev_lhead a zetas pc returnaddress))))
     :(uarch_event)list`;;

(*** The block lemma for block b of layer l ***)

let ntt_block_events_inst l b ev =
  let red t = rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (7 - l)),`LEN:num`;
      b,`B:num`] t))) in
  SPECL [ev; `a:int64`; `zetas:num`; `pc:num`;
         red `2 * LEN * B`; red `LEN:num`; red `2 EXP L + B`;
         red `word(L + 1):int64`; `word 1:int64`; `word 256:int64`;
         `returnaddress:int64`] NTT_GCC12_O2_MONO_BLOCK_EVENTS;;

(*** Register state at the block head and block end (b blocks done) ***)

let lsafe_blockhead_tm,lsafe_blockend_tm =
  let headtm =
   `\s. read X9 s = word(2 * LEN * B) /\
        read X10 s = word(2 * LEN * B + LEN) /\
        read X11 s = word(2 EXP L + B) /\ read X12 s = word(2 * LEN) /\
        read X13 s = word zetas /\ read X14 s = a /\
        read X15 s = word_add a (word 2) /\
        read X16 s = word(L + 1) /\ read X17 s = word 1 /\
        read X18 s = word 256 /\ read X30 s = returnaddress` in
  let mk l b =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (7 - l)),`LEN:num`;
      b,`B:num`] headtm))) in
  mk,mk;;

let LSAFE_TEST_TAC k =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (fun (asl,w) ->
     match find_terms is_cond w with
       [] -> ALL_TAC (asl,w)
     | tms ->
         let c = rand(rator(rator(hd(sort (fun a b -> free_in b a) tms)))) in
         if c = subst [k,`K:num`] `i + 1 < K` then ALL_TAC (asl,w) else
         (SUBGOAL_THEN (mk_eq(c,subst [k,`K:num`] `~(i + 1 < K)`))
          SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) (asl,w)) THEN
  REPEAT(CONJ_TAC THENL
   [REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    (ASM_ARITH_TAC ORELSE (AP_TERM_TAC THEN ASM_ARITH_TAC));
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;
(*** Simulation of a short piece of straight-line code with flags ***)

let LSAFE_SIM_TAC pre_tac n =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN pre_tac THEN
  MAP_EVERY (fun i ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC [i] THEN
    TRY W32_DECIDE_FLAGS_TAC) (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REPEAT(CONJ_TAC THENL
   [REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    (ASM_ARITH_TAC ORELSE (AP_TERM_TAC THEN ASM_ARITH_TAC));
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The whole safety proof for layer l ***)

let NTT_LAYER_SAFE_TAC l =
  let k = mk_small_numeral(1 lsl l - 1) in
  let blk0_tac =
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mlk_poly_ntt_c_loop2_test` (lsafe_blockend_tm l
     `1`) THEN
    CONJ_TAC THENL
     [ENSURES_EVENTS_SEQUENCE_TAC `pc + mlk_poly_ntt_c_loop2` (lsafe_blockhead_tm l
      `0`) THEN
      CONJ_TAC THENL
       [LSAFE_SIM_TAC ALL_TAC 6;
        EVENTS_LEMMA_TAC (ntt_block_events_inst l `0`)];
      LSAFE_SIM_TAC ALL_TAC 2] in
  CONCRETIZE_F_EVENTS_TAC (lsafe_template l) THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL;
              SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  if l = 0 then blk0_tac else
  ENSURES_EVENTS_WHILE_UP2_TAC k `pc + mlk_poly_ntt_c_loop2_next`
   `pc + mlk_poly_ntt_c_loop2_exit`
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
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mlk_poly_ntt_c_loop2_test`
      (lsafe_blockend_tm l `i + 1 + 1`) THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
      ENSURES_EVENTS_SEQUENCE_TAC `pc + mlk_poly_ntt_c_loop2`
        (lsafe_blockhead_tm l `i + 1`) THEN
      CONJ_TAC THENL
       [LSAFE_SIM_TAC
         (let n = rhs(concl(NUM_REDUCE_CONV
                   (subst [mk_small_numeral l,`L:num`] `2 EXP L + i + 1`))) in
          MP_TAC(SPEC n VAL_WORD_ZX_UXTW) THEN
          ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC]) 2;
        EVENTS_LEMMA_TAC (ntt_block_events_inst l `i + 1`)];
      LSAFE_TEST_TAC k];
    LSAFE_SIM_TAC ALL_TAC 0];;

let NTT_GCC12_O2_MONO_LAYER_EVENTS = assuming_proofs (fun () ->
  map (fun l ->
        new_specification ["ntt_gcc12_O2_mono_layer_events_" ^ string_of_int l]
                          (prove(lsafe_goal l,NTT_LAYER_SAFE_TAC l)))
      (0--6));;

(*** The whole code, which has the same signature as mlkem_reduce, with ***)
(*** the table of zetas as a read-only object                           ***)

let ntt_top_template =
  let lay l = mk_comb(mk_comb(mk_comb(mk_comb(
     mk_const("ntt_gcc12_O2_mono_layer_events_" ^ string_of_int l,[]),`a:int64`),
     `zetas:num`),`pc:num`),`returnaddress:int64`)
  and fev n =
    list_mk_comb(mk_var(n,`:int64->num->num->int64->(uarch_event)list`),
                 [`a:int64`;`zetas:num`;`pc:num`;`returnaddress:int64`]) in
  let app x y = list_mk_icomb "APPEND" [x;y] in
  let rec chain l acc =
    if l > 6 then acc else
    let acc' = app (lay l) acc in
    if l = 6 then acc' else
    chain (l + 1) (app (fev ("f_ev_back" ^ string_of_int l)) acc') in
  let body = app (fev "f_ev_fin") (chain 0 (fev "f_ev_init")) in
  list_mk_abs([`a:int64`;`zetas:num`;`pc:num`;`returnaddress:int64`],body);;

let ntt_safe_layerhead_tm,ntt_safe_layerend_tm =
  let headtm =
   `\s. read X11 s = word L /\ read X13 s = word zetas /\
        read X14 s = a /\ read X15 s = word_add a (word 2) /\
        read X17 s = word 1 /\ read X18 s = word 256 /\
        read X30 s = returnaddress`
  and endtm =
   `\s. read X16 s = word(L + 1) /\ read X13 s = word zetas /\
        read X14 s = a /\ read X15 s = word_add a (word 2) /\
        read X17 s = word 1 /\ read X18 s = word 256 /\
        read X30 s = returnaddress` in
  let mk tm l =
    rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`] tm))) in
  (fun l -> mk headtm l),(fun l -> mk endtm l);;

let ntt_layer_events_inst l ev =
  SPECL [ev; `a:int64`; `zetas:num`; `pc:num`; `returnaddress:int64`]
        (el l NTT_GCC12_O2_MONO_LAYER_EVENTS);;

let NTT_SAFE_TOP_TAC =
  CONCRETIZE_F_EVENTS_TAC ntt_top_template THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun eq ->
    if is_eq(concl eq) && lhand(concl eq) = `zetas:num`
    then (zeta_eq := eq; ALL_TAC) else failwith "") THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlk_poly_ntt_c_loop2_exit` (ntt_safe_layerend_tm 6) THEN
  CONJ_TAC THENL [ALL_TAC; LSAFE_SIM_TAC ALL_TAC 3] THEN
  MAP_EVERY (fun l ->
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mlk_poly_ntt_c_loop1` (ntt_safe_layerhead_tm l) THEN
    CONJ_TAC THENL [ALL_TAC; EVENTS_LEMMA_TAC (ntt_layer_events_inst l)] THEN
    if l = 0 then ALL_TAC else
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mlk_poly_ntt_c_loop2_exit` (ntt_safe_layerend_tm (l - 1)) THEN
    CONJ_TAC THENL [ALL_TAC; LSAFE_SIM_TAC ALL_TAC 6]) (rev(0--6)) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  (fun g -> ASSUME_TAC !zeta_eq g) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (1--1) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (2--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;


(*** The version with the table of zetas at a variable address, which ***)
(*** the image puts at pc + rodata_mlk_zetas                            ***)

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_SAFE_STMT =
  `exists f_events.
     forall e a zetas pc returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       zetas = pc + rodata_mlk_zetas /\
       ALL (nonoverlapping (a,512)) [word pc,libmlkem_size; word zetas,256]
       ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                read PC s = word (pc + mlk_poly_ntt_c) /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a] s /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a zetas pc returnaddress /\
                  memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
           (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                       X12; X13; X14; X15; X16; X17; X18] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_SAFE =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_SAFE_STMT;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e a pc returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       nonoverlapping (a,512) (word pc,libmlkem_size)
       ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                read PC s = word (pc + mlk_poly_ntt_c) /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a] s /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a pc returnaddress /\
                  memaccess_inbounds e2
                   [a,512; word (pc + rodata_mlk_zetas),256] [a,512])
           (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                       X12; X13; X14; X15; X16; X17; X18] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT;;
