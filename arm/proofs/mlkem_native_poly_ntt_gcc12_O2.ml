(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform from ML-KEM.                           *)
(* This is the code for mlkem_poly_ntt from mlkem-native's portable C        *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* Unlike the hand-written kernel, it reads its own table of zetas from the  *)
(* read-only data rather than taking tables as arguments.                    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "common/int_linear.ml";;

(**** print_literal_relocs_from_elf
        "arm/mlkem_native/mlkem_native_poly_ntt_gcc12_O2.o";;
 ****)

let mlkem_native_poly_ntt_gcc12_O2_mc,
    mlkem_native_poly_ntt_gcc12_O2_data =
  define_assert_relocs_from_elf
    ~map_symbol_name:(function
      | "WHOLE_READONLY" | "ltmp1" | "mlk_zetas" -> "mlk_zetas_data"
      | s -> failwith ("unknown symbol: " ^ s))
    "mlkem_native_poly_ntt_gcc12_O2_mc"
    "arm/mlkem_native/mlkem_native_poly_ntt_gcc12_O2.o"
(fun w BL ADR ADRP ADD_rri64 -> [
  ADRP (mk_var("mlk_zetas_data",`:num`),0,0,12);
  w 0xaa0003ed;         (* arm_MOV X13 X0 *)
  ADD_rri64 (mk_var("mlk_zetas_data",`:num`),0,12,12);
  w 0x9100080e;         (* arm_ADD X14 X0 (rvalue (word 2)) *)
  w 0x52800007;         (* arm_MOV W7 (rvalue (word 0)) *)
  w 0x12805ea8;         (* arm_MOVN W8 (word 757) 0 *)
  w 0x52800030;         (* arm_MOV W16 (rvalue (word 1)) *)
  w 0x52802011;         (* arm_MOV W17 (rvalue (word 256)) *)
  w 0x12819fcb;         (* arm_MOVN W11 (word 3326) 0 *)
  w 0x1281a00a;         (* arm_MOVN W10 (word 3328) 0 *)
  w 0xd503201f;         (* arm_NOP *)
  w 0x110004ef;         (* arm_ADD W15 W7 (rvalue (word 1)) *)
  w 0x52800004;         (* arm_MOV W4 (rvalue (word 0)) *)
  w 0x1ac72207;         (* arm_LSLV W7 W16 W7 *)
  w 0x1acf2626;         (* arm_LSRV W6 W17 W15 *)
  w 0x531f78c9;         (* arm_LSL W9 W6 1 *)
  w 0xd503201f;         (* arm_NOP *)
  w 0x110004e7;         (* arm_ADD W7 W7 (rvalue (word 1)) *)
  w 0x6b0400df;         (* arm_CMP W6 W4 *)
  w 0x54000309;         (* arm_BLS (word 96) *)
  w 0x4b0400c2;         (* arm_SUB W2 W6 W4 *)
  w 0x2a0403e0;         (* arm_MOV W0 W4 *)
  w 0x51000442;         (* arm_SUB W2 W2 (rvalue (word 1)) *)
  w 0x2a0603e3;         (* arm_MOV W3 W6 *)
  w 0x8b000042;         (* arm_ADD X2 X2 X0 *)
  w 0xcb000063;         (* arm_SUB X3 X3 X0 *)
  w 0x8b2445a1;         (* arm_ADD X1 X13
                           (Shiftedreg (Extendedreg W4 UXTW) LSL 1) *)
  w 0x8b0205c2;         (* arm_ADD X2 X14 (Shiftedreg X2 LSL 1) *)
  w 0xd503201f;         (* arm_NOP *)
  w 0x78e37825;         (* arm_LDRSH W5 X1 (Shiftreg_Offset X3 1) *)
  w 0x79400032;         (* arm_LDRH W18 X1 (Immediate_Offset (word 0)) *)
  w 0x1b087ca5;         (* arm_MUL W5 W5 W8 *)
  w 0x1b0b7ca0;         (* arm_MUL W0 W5 W11 *)
  w 0x13003c00;         (* arm_SBFM W0 W0 0 15 *)
  w 0x1b0a1400;         (* arm_MADD W0 W0 W10 W5 *)
  w 0x13107c00;         (* arm_ASR W0 W0 16 *)
  w 0x4b000245;         (* arm_SUB W5 W18 W0 *)
  w 0x78237825;         (* arm_STRH W5 X1 (Shiftreg_Offset X3 1) *)
  w 0x79400025;         (* arm_LDRH W5 X1 (Immediate_Offset (word 0)) *)
  w 0x0b050000;         (* arm_ADD W0 W0 W5 *)
  w 0x78002420;         (* arm_STRH W0 X1 (Postimmediate_Offset (word 2)) *)
  w 0xeb01005f;         (* arm_CMP X2 X1 *)
  w 0x54fffe61;         (* arm_BNE (word 2097100) *)
  w 0x0b090084;         (* arm_ADD W4 W4 W9 *)
  w 0x0b0900c6;         (* arm_ADD W6 W6 W9 *)
  w 0x7103fc9f;         (* arm_CMP W4 (rvalue (word 255)) *)
  w 0x54000068;         (* arm_BHI (word 12) *)
  w 0x78e75988;         (* arm_LDRSH W8 X12
                           (Shiftreg_Offset (Extendedreg W7 UXTW) 1) *)
  w 0x17ffffe1;         (* arm_B (word 268435332) *)
  w 0x71001dff;         (* arm_CMP W15 (rvalue (word 7)) *)
  w 0x540000a0;         (* arm_BEQ (word 20) *)
  w 0x1acf2200;         (* arm_LSLV W0 W16 W15 *)
  w 0x2a0f03e7;         (* arm_MOV W7 W15 *)
  w 0x78e07988;         (* arm_LDRSH W8 X12 (Shiftreg_Offset X0 1) *)
  w 0x17ffffd5;         (* arm_B (word 268435284) *)
  w 0xd65f03c0          (* arm_RET X30 *)
]);;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC =
  ARM_MK_EXEC_RULE mlkem_native_poly_ntt_gcc12_O2_mc;;

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

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_BLOCK = prove
 (`!a zetas pc z start len k m w15 w16 w17.
     ALL (nonoverlapping (a,512)) [(word pc,0xe0); (word zetas,256)] /\
     1 <= len /\ start + 2 * len <= 256 /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
               read PC s = word(pc + 0x44) /\
               read X4 s = word start /\ read X6 s = word(start + len) /\
               read X7 s = word k /\
               read X8 s = word_zx(word_sx z:int32) /\
               read X9 s = word(2 * len) /\
               read X10 s = word 4294963967 /\ read X11 s = word 4294963969 /\
               read X12 s = word zetas /\ read X13 s = a /\
               read X14 s = word_add a (word 2) /\
               read X15 s = w15 /\ read X16 s = w16 /\ read X17 s = w17 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        m i))
          (\s. aligned_bytes_loaded s (word pc)
                 (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
               read PC s = word(pc + 0xb4) /\
               read X4 s = word(start + 2 * len) /\
               read X6 s = word(start + 3 * len) /\
               read X7 s = word(k + 1) /\
               read X8 s = word_zx(word_sx z:int32) /\
               read X9 s = word(2 * len) /\
               read X10 s = word 4294963967 /\ read X11 s = word 4294963969 /\
               read X12 s = word zetas /\ read X13 s = a /\
               read X14 s = word_add a (word 2) /\
               read X15 s = w15 /\ read X16 s = w16 /\ read X17 s = w17 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        ntt_block_c z start len m i))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X18] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC `len:num` `pc + 0x74` `pc + 0xa4`
   `\jj s. aligned_bytes_loaded s (word pc)
             (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
           read X1 s = word_add a (word(2 * (start + jj))) /\
           read X2 s = word_add a (word(2 * (start + len))) /\
           read X3 s = word len /\
           read X4 s = word start /\ read X6 s = word(start + len) /\
           read X7 s = word(k + 1) /\
           read X8 s = word_zx(word_sx z:int32) /\
           read X9 s = word(2 * len) /\
           read X10 s = word 4294963967 /\ read X11 s = word 4294963969 /\
           read X12 s = word zetas /\ read X13 s = a /\
           read X14 s = word_add a (word 2) /\
           read X15 s = w15 /\ read X16 s = w16 /\ read X17 s = w17 /\
           (!k. k < 128
                ==> read(memory :> bytes16(word_add (word zetas)
                                                    (word(2 * k)))) s =
                    iword(EL k mlk_zetas)) /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    if start <= i /\ i < start + jj \/
                       start + len <= i /\ i < start + len + jj
                    then ntt_block_c z start len m i else m i)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** Setting up the pointers for the inner loop ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--2) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (3--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `~(a <= i /\ i < a:num)`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN WORD_SMALL_TAC;

    (*** The inner loop body, one butterfly ***)

    X_GEN_TAC `jj:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `m:num->int16` (concl th)
      then MP_TAC(SPEC `start + jj:num` th) THEN
           MP_TAC(SPEC `start + len + jj:num` th) THEN
           ASSUME_TAC(BETA_RULE(MATCH_MP (SPEC
             `\i. ~(i = start + jj) /\ ~(i = start + len + jj)`
             (MESON[] `!R P Q. (!i:num. P i ==> Q i)
                               ==> (!i. P i /\ R i ==> Q i)`)) th))
      else failwith "") THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `jj < len
      ==> ~(start <= start + len + jj /\ start + len + jj < start + jj) /\
          ~(start + len <= start + len + jj /\
            start + len + jj < start + len + jj)`] THEN
    REWRITE_TAC[ARITH_RULE
     `2 * (start + len + jj) = 2 * (start + jj) + 2 * len`] THEN
    DISCH_TAC THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `jj < len
      ==> ~(start <= start + jj /\ start + jj < start + jj) /\
          ~(start + len <= start + jj /\ start + jj < start + len + jj)`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `val(word len:int64) = len` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i = start + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LE_ADD; ARITH_RULE `start + jj < start + jj + 1`] THEN
      MLKEM_NATIVE_W_SIMP_TAC THEN REWRITE_TAC[WORD_ADD_0] THEN
      REWRITE_TAC[GSYM montred_scalar; WORD_ZX_ADD_ZX_16] THEN
      REWRITE_TAC[ntt_block_c; ntt_fqmul_c; LE_ADD] THEN
      ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN REWRITE_TAC[ADD_AC; WORD_ADD_SYM];
      ALL_TAC] THEN
    ASM_CASES_TAC `i = start + len + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN
      REWRITE_TAC[ARITH_RULE
       `2 * (start + len + jj) = 2 * (start + jj) + 2 * len`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `start + len + jj < start + len + jj + 1`;
                  ARITH_RULE `start + len <= start + len + jj`] THEN
      MLKEM_NATIVE_W_SIMP_TAC THEN REWRITE_TAC[WORD_ADD_0] THEN
      REWRITE_TAC[GSYM montred_scalar; WORD_ZX_SUB_ZX_16] THEN
      REWRITE_TAC[ntt_block_c; ntt_fqmul_c] THEN
      ASM_SIMP_TAC[ARITH_RULE
       `jj < len ==> ~(start <= start + len + jj /\
                       start + len + jj < start + len) /\
                     start + len <= start + len + jj /\
                     start + len + jj < start + 2 * len`] THEN
      REWRITE_TAC[ARITH_RULE `(start + len + jj) - len = start + jj`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `m:num->int16` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;

    (*** The inner loop back-edge ***)

    X_GEN_TAC `jj:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The inner loop exit and the end of the block ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [WORD_SMALL_TAC; WORD_SMALL_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `m:num->int16` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ntt_block_c] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC]);;

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
          (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
        read X4 s = word(2 * LEN * B) /\
        read X6 s = word(2 * LEN * B + LEN) /\
        read X7 s = word(2 EXP L + B) /\
        read X8 s =
        word_zx(word_sx(iword(EL (2 EXP L + B) mlk_zetas):int16):int32) /\
        read X9 s = word(2 * LEN) /\
        read X10 s = word 4294963967 /\ read X11 s = word 4294963969 /\
        read X12 s = word zetas /\ read X13 s = a /\
        read X14 s = word_add a (word 2) /\
        read X15 s = word(L + 1) /\ read X16 s = word 1 /\
        read X17 s = word 256 /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 ntt_blocks_c L B r i)`
  and endtm =
   `\s. aligned_bytes_loaded s (word pc)
          (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
        read X4 s = word(2 * LEN * B) /\
        read X6 s = word(2 * LEN * B + LEN) /\
        read X7 s = word(2 EXP L + B) /\
        read X9 s = word(2 * LEN) /\
        read X10 s = word 4294963967 /\ read X11 s = word 4294963969 /\
        read X12 s = word zetas /\ read X13 s = a /\
        read X14 s = word_add a (word 2) /\
        read X15 s = word(L + 1) /\ read X16 s = word 1 /\
        read X17 s = word 256 /\
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
    `word 256:int64`] MLKEM_NATIVE_POLY_NTT_GCC12_O2_BLOCK in
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
  ENSURES_SEQUENCE_TAC `pc + 0x44` (ntt_blockhead_tm l `0`) THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[ntt_blocks_c] THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The exit from the block loop at the end of the layer ***)

let NTT_LAYEREXIT_TAC =
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The whole layer l (number of layers done before it) ***)

let NTT_LAYER_TAC l =
  NTT_LAYERHEAD_TAC l THEN
  ENSURES_SEQUENCE_TAC `pc + 0xb4` (ntt_blockend_tm l `1`) THEN
  CONJ_TAC THENL
   [NTT_BLOCK_TAC l `0`;
    if l = 0 then NTT_LAYEREXIT_TAC else
    ENSURES_WHILE_UP_TAC (mk_small_numeral(1 lsl l - 1))
      `pc + 0xb4` `pc + 0xb4`
      (mk_abs(`i:num`,ntt_blockend_tm l `i + 1`)) THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ENSURES_SEQUENCE_TAC `pc + 0x44` (ntt_blockhead_tm l `i + 1`) THEN
      CONJ_TAC THENL
       [ENSURES_INIT_TAC "s0" THEN
        ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
        W32_DECIDE_FLAGS_TAC THEN
        ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--2) THEN
        ZETA_UXTW_TAC
         (rhs(concl(NUM_REDUCE_CONV
           (subst [mk_small_numeral l,`L:num`] `2 EXP L + i + 1`)))) THEN
        ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (3--4) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
        NTT_BLOCK_TAC l `i + 1`];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[];
      NTT_LAYEREXIT_TAC]];;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_LAYER = prove
 (`!a zetas pc l r w8.
     ALL (nonoverlapping (a,512)) [(word pc,0xe0); (word zetas,256)] /\
     l < 7
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
               read PC s = word(pc + 0x2c) /\
               read X7 s = word l /\
               read X8 s =
               word_zx(word_sx(iword(EL (2 EXP l) mlk_zetas):int16):int32) /\
               read X10 s = word 4294963967 /\ read X11 s = word 4294963969 /\
               read X12 s = word zetas /\ read X13 s = a /\
               read X14 s = word_add a (word 2) /\
               read X16 s = word 1 /\ read X17 s = word 256 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        r i))
          (\s. aligned_bytes_loaded s (word pc)
                 (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
               read PC s = word(pc + 0xc4) /\
               read X15 s = word(l + 1) /\
               read X10 s = word 4294963967 /\ read X11 s = word 4294963969 /\
               read X12 s = word zetas /\ read X13 s = a /\
               read X14 s = word_add a (word 2) /\
               read X16 s = word 1 /\ read X17 s = word 256 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        ntt_blocks_c l (2 EXP l) r i))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X15; X18] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) MP_TAC) THEN
  SPEC_TAC(`l:num`,`l:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
  (map NTT_LAYER_TAC (0--6)));;

(* ------------------------------------------------------------------------- *)
(* The computation of the C code gives the NTT, within the same bounds as    *)
(* the hand-written kernel.                                                  *)
(* ------------------------------------------------------------------------- *)

let NTT_BLOCKS_C_CLOSED = prove
 (`!l b r i.
     ntt_blocks_c l b r i =
     if i < 2 * 2 EXP (7 - l) * b
     then let z = iword(EL (2 EXP l + i DIV (2 * 2 EXP (7 - l))) mlk_zetas) in
          if i MOD (2 * 2 EXP (7 - l)) < 2 EXP (7 - l)
          then word_add (r i) (ntt_fqmul_c z (r(i + 2 EXP (7 - l))))
          else word_sub (r(i - 2 EXP (7 - l))) (ntt_fqmul_c z (r i))
     else r i`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ntt_blocks_c; MULT_CLAUSES; CONJUNCT1 LT] THEN
  REWRITE_TAC[ntt_block_c] THEN
  SUBGOAL_THEN `1 <= 2 EXP (7 - l)` MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `n = 2 EXP (7 - l)` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MULT_CLAUSES; LEFT_ADD_DISTRIB] THEN
  ASM_CASES_TAC `2 * n * b <= i /\ i < 2 * n * b + 2 * n` THENL
   [SUBGOAL_THEN `i DIV (2 * n) = b /\ i MOD (2 * n) = i - 2 * n * b`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC DIVMOD_UNIQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `2 * n * b <= i /\ i < 2 * n * b + 2 * n
      ==> ~(i < 2 * n * b) /\ ~(i + n < 2 * n * b) /\
          i < 2 * n * b + 2 * n`] THEN
    ASM_CASES_TAC `i < 2 * n * b + n` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `2 * n * b <= i /\ i < 2 * n * b + n ==> i - 2 * n * b < n`;
     ARITH_RULE `~(i < 2 * n * b + n) ==> ~(i - 2 * n * b < n)`;
     ARITH_RULE `~(i < 2 * n * b + n) ==> ~(i - n < 2 * n * b)`] THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE
     `~(p <= i /\ i < p + 2 * n)
      ==> ~(p <= i /\ i < p + n) /\ ~(p + n <= i /\ i < p + 2 * n)`] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;

let NTT_LAYERS_C_STEP = prove
 (`!l x i.
     l < 7 /\ i < 256
     ==> ntt_layers_c (SUC l) x i =
         let z = iword(EL (2 EXP l + i DIV (2 * 2 EXP (7 - l))) mlk_zetas) in
         if i MOD (2 * 2 EXP (7 - l)) < 2 EXP (7 - l)
         then word_add (ntt_layers_c l x i)
                       (ntt_fqmul_c z (ntt_layers_c l x (i + 2 EXP (7 - l))))
         else word_sub (ntt_layers_c l x (i - 2 EXP (7 - l)))
                       (ntt_fqmul_c z (ntt_layers_c l x i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ntt_layers_c; NTT_BLOCKS_C_CLOSED] THEN
  SUBGOAL_THEN `i < 2 * 2 EXP (7 - l) * 2 EXP l`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM MULT_ASSOC; GSYM EXP_ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE `l < 7 ==> 7 - l + l = 7`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

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

let NTT_LAYERS_C_CORRECT = prove
 (`!x. (!i. i < 256 ==> abs(ival(x i)) <= &8191)
       ==> !i. i < 256
               ==> (ival(ntt_layers_c 7 x i) == forward_ntt (ival o x) i)
                   (mod &3329) /\
                   abs(ival(ntt_layers_c 7 x i)) <= &23594`,
  GEN_TAC THEN CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  W(fun (asl,w) ->
    let lfn = MLKEM_NATIVE_LOCAL_CONGBOUND_RULE
                (PROCESS_BOUND_ASSUMPTIONS (map snd asl))
                NTT_LAYER_EQUATIONS in
    REPEAT CONJ_TAC THEN NTT_FINAL_TAC lfn));;

(* ------------------------------------------------------------------------- *)
(* The whole code computes the C version of the NTT.                         *)
(* ------------------------------------------------------------------------- *)

(*** Assertions at the layer head and layer end for layer l ***)

let ntt_layerhead_tm,ntt_layerend_tm =
  let headtm =
   `\s. aligned_bytes_loaded s (word pc)
          (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
        read X7 s = word L /\
        read X8 s =
        word_zx(word_sx(iword(EL (2 EXP L) mlk_zetas):int16):int32) /\
        read X10 s = word 4294963967 /\ read X11 s = word 4294963969 /\
        read X12 s = word zetas /\ read X13 s = a /\
        read X14 s = word_add a (word 2) /\
        read X16 s = word 1 /\ read X17 s = word 256 /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 ntt_layers_c L x i)`
  and endtm =
   `\s. aligned_bytes_loaded s (word pc)
          (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
        read X15 s = word(L + 1) /\
        read X10 s = word 4294963967 /\ read X11 s = word 4294963969 /\
        read X12 s = word zetas /\ read X13 s = a /\
        read X14 s = word_add a (word 2) /\
        read X16 s = word 1 /\ read X17 s = word 256 /\
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
                 MLKEM_NATIVE_POLY_NTT_GCC12_O2_LAYER in
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
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--4) THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mlk_zetas` (concl th)
    then MP_TAC(CONV_RULE NUM_REDUCE_CONV
                  (SPEC (mk_small_numeral(1 lsl (l + 1))) th))
    else failwith "") THEN
  REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (5--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_LAYERS = prove
 (`!a zetas (x:num->int16) pc.
    adrp_within_bounds (word zetas) (word pc) /\
    ALL (nonoverlapping (a,512)) [(word pc,0xe0); (word zetas,256)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
           read PC s = word pc /\
           C_ARGUMENTS [a] s /\
           bytes_loaded s (word zetas) mlk_zetas_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = word(pc + 0xdc) /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    ntt_layers_c 7 x i))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
       MAYCHANGE [memory :> bytes(a,512)])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `zetas:num`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Initialization, including the address of the table ***)

  ENSURES_SEQUENCE_TAC `pc + 0x2c` (ntt_layerhead_tm 0) THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLK_ZETAS_LOADED) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--3) THEN
    FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP ADRP_ADD_FOLD) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (4--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[CONJUNCT1 ntt_layers_c] THEN
    REWRITE_TAC[mlk_zetas] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_IWORD_CONV) THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV);
    ALL_TAC] THEN

  (*** The layers, with the loop back to the head between them ***)

  MAP_EVERY (fun l ->
    ENSURES_SEQUENCE_TAC `pc + 0xc4` (ntt_layerend_tm l) THEN
    CONJ_TAC THENL [NTT_LAYER_APPLY_TAC l; ALL_TAC] THEN
    if l = 6 then ALL_TAC else
    ENSURES_SEQUENCE_TAC `pc + 0x2c` (ntt_layerhead_tm (l + 1)) THEN
    CONJ_TAC THENL [NTT_LAYERBACK_TAC l; ALL_TAC]) (0--6) THEN

  (*** The exit after the last layer ***)

  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_CORRECT = prove
 (`!a zetas (x:num->int16) pc.
    adrp_within_bounds (word zetas) (word pc) /\
    ALL (nonoverlapping (a,512)) [(word pc,0xe0); (word zetas,256)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
           read PC s = word pc /\
           C_ARGUMENTS [a] s /\
           bytes_loaded s (word zetas) mlk_zetas_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = word(pc + 0xdc) /\
           ((!i. i < 256 ==> abs(ival(x i)) <= &8191)
            ==> !i. i < 256
                    ==> let zi =
                          read(memory :> bytes16(word_add a (word(2 * i)))) s
                        in (ival zi == forward_ntt (ival o x) i) (mod &3329) /\
                           abs(ival zi) <= &23594))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
       MAYCHANGE [memory :> bytes(a,512)])`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `x:num->int16` o
    MATCH_MP MLKEM_NATIVE_POLY_NTT_GCC12_O2_LAYERS) THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ_ALT] ENSURES_POSTCONDITION_THM)) THEN
  GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN DISCH_TAC THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  MP_TAC(SPEC `x:num->int16` NTT_LAYERS_C_CORRECT) THEN
  ASM_SIMP_TAC[]);;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_SUBROUTINE_CORRECT = prove
 (`!a zetas (x:num->int16) pc returnaddress.
    adrp_within_bounds (word zetas) (word pc) /\
    ALL (nonoverlapping (a,512)) [(word pc,0xe0); (word zetas,256)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
           read PC s = word pc /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [a] s /\
           bytes_loaded s (word zetas) mlk_zetas_data /\
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
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
       MAYCHANGE [memory :> bytes(a,512)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. This follows the structure of the  *)
(* correctness proof, with the events of a block and of each layer given by  *)
(* functions obtained from the corresponding lemmas.                         *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** One block, from its setup through the inner loop ***)

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_BLOCK_SAFE = prove
 (`exists f_ev_blk.
   forall e a zetas pc start len k w15 w16 w17 returnaddress.
     ALL (nonoverlapping (a,512)) [(word pc,0xe0); (word zetas,256)] /\
     1 <= len /\ start + 2 * len <= 256 /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
               read PC s = word(pc + 0x44) /\
               read X4 s = word start /\ read X6 s = word(start + len) /\
               read X7 s = word k /\ read X9 s = word(2 * len) /\
               read X12 s = word zetas /\ read X13 s = a /\
               read X14 s = word_add a (word 2) /\
               read X15 s = w15 /\ read X16 s = w16 /\ read X17 s = w17 /\
               read X30 s = returnaddress /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
               read PC s = word(pc + 0xb4) /\
               read X4 s = word(start + 2 * len) /\
               read X6 s = word(start + 3 * len) /\
               read X7 s = word(k + 1) /\ read X9 s = word(2 * len) /\
               read X12 s = word zetas /\ read X13 s = a /\
               read X14 s = word_add a (word 2) /\
               read X15 s = w15 /\ read X16 s = w16 /\ read X17 s = w17 /\
               read X30 s = returnaddress /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_blk a zetas pc returnaddress start len /\
                 memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
          (\s s'. true)`,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (zetas:num) (pc:num) (returnaddress:int64) (start:num)
     (len:num).
      APPEND (f_ev_blkend a zetas pc returnaddress start len)
        (APPEND (ENUMERATEL len
                   (\j. f_ev_bfly a zetas pc returnaddress start len j))
                (f_ev_blkhead a zetas pc returnaddress start len))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `len:num` `pc + 0x74` `pc + 0xac`
   `\j s. read X1 s = word_add a (word(2 * (start + j))) /\
          read X2 s = word_add a (word(2 * (start + len))) /\
          read X3 s = word len /\
          read X4 s = word start /\ read X6 s = word(start + len) /\
          read X7 s = word(k + 1) /\ read X9 s = word(2 * len) /\
          read X12 s = word zetas /\ read X13 s = a /\
          read X14 s = word_add a (word 2) /\
          read X15 s = w15 /\ read X16 s = w16 /\ read X17 s = w17 /\
          read X30 s = returnaddress` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** Setting up the pointers for the inner loop ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--2) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (3--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The inner loop body, one butterfly, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `val(word len:int64) = len` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--12) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_add (word_add a (word x)) (word y):int64 =
      word_add a (word(x + y))`]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (13--13) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (14--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(2 * (start + len) = 2 * (start + i) + 2) <=> i + 1 < len`
     SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The end of the block ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let NTT_GCC12_O2_BLOCK_EVENTS =
  new_specification ["ntt_gcc12_O2_block_events"]
                    MLKEM_NATIVE_POLY_NTT_GCC12_O2_BLOCK_SAFE;;

(*** One layer, for each of the seven layers ***)

let lsafe_goal l =
  let tm =
  `exists f_ev_lay.
    forall e a zetas pc returnaddress.
     ALL (nonoverlapping (a,512)) [(word pc,0xe0); (word zetas,256)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
               read PC s = word(pc + 0x2c) /\
               read X7 s = word L /\ read X12 s = word zetas /\
               read X13 s = a /\ read X14 s = word_add a (word 2) /\
               read X16 s = word 1 /\ read X17 s = word 256 /\
               read X30 s = returnaddress /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
               read PC s = word(pc + 0xc4) /\
               read X15 s = word(L + 1) /\ read X12 s = word zetas /\
               read X13 s = a /\ read X14 s = word_add a (word 2) /\
               read X16 s = word 1 /\ read X17 s = word 256 /\
               read X30 s = returnaddress /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_lay a zetas pc returnaddress /\
                 memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
          (\s s'. true)` in
  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`] tm)));;

(*** The event template for layer l ***)

let lsafe_template l =
  let len = mk_small_numeral(1 lsl (7 - l)) in
  if l = 0 then
   subst [len,`LEN:num`]
   `\(a:int64) (zetas:num) (pc:num) (returnaddress:int64).
      APPEND (f_ev_ltest0 a zetas pc returnaddress)
       (APPEND (ntt_gcc12_O2_block_events a zetas pc returnaddress 0 LEN)
               (f_ev_lhead a zetas pc returnaddress))
     :(uarch_event)list`
  else
   subst [len,`LEN:num`; mk_small_numeral(1 lsl l - 1),`K:num`]
   `\(a:int64) (zetas:num) (pc:num) (returnaddress:int64).
      APPEND (f_ev_lexit a zetas pc returnaddress)
       (APPEND
         (ENUMERATEL K
           (\i. APPEND (f_ev_ltest a zetas pc returnaddress i)
                 (APPEND (ntt_gcc12_O2_block_events a zetas pc returnaddress
                                           (2 * LEN * (i + 1)) LEN)
                         (f_ev_lzeta a zetas pc returnaddress i))))
         (APPEND (f_ev_ltest0 a zetas pc returnaddress)
           (APPEND (ntt_gcc12_O2_block_events a zetas pc returnaddress 0 LEN)
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
         `returnaddress:int64`] NTT_GCC12_O2_BLOCK_EVENTS;;

(*** Register state at the block head and block end (b blocks done) ***)

let lsafe_blockhead_tm,lsafe_blockend_tm =
  let headtm =
   `\s. read X4 s = word(2 * LEN * B) /\
        read X6 s = word(2 * LEN * B + LEN) /\
        read X7 s = word(2 EXP L + B) /\ read X9 s = word(2 * LEN) /\
        read X12 s = word zetas /\ read X13 s = a /\
        read X14 s = word_add a (word 2) /\
        read X15 s = word(L + 1) /\ read X16 s = word 1 /\
        read X17 s = word 256 /\ read X30 s = returnaddress` in
  let mk l b =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (7 - l)),`LEN:num`;
      b,`B:num`] headtm))) in
  mk,mk;;

let LSAFE_TEST_TAC k =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--2) THEN
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
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC [i] THEN
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
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xb4` (lsafe_blockend_tm l `1`) THEN
    CONJ_TAC THENL
     [ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x44` (lsafe_blockhead_tm l `0`) THEN
      CONJ_TAC THENL
       [LSAFE_SIM_TAC ALL_TAC 6;
        EVENTS_LEMMA_TAC (ntt_block_events_inst l `0`)];
      LSAFE_SIM_TAC ALL_TAC 2] in
  CONCRETIZE_F_EVENTS_TAC (lsafe_template l) THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN REPEAT STRIP_TAC THEN
  if l = 0 then blk0_tac else
  ENSURES_EVENTS_WHILE_UP2_TAC k `pc + 0xbc` `pc + 0xc4`
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
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xb4`
      (lsafe_blockend_tm l `i + 1 + 1`) THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
      ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x44`
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

let NTT_GCC12_O2_LAYER_EVENTS =
  map (fun l ->
        new_specification ["ntt_gcc12_O2_layer_events_" ^ string_of_int l]
                          (prove(lsafe_goal l,NTT_LAYER_SAFE_TAC l)))
      (0--6);;

(*** The whole code, which has the same signature as mlkem_reduce, with ***)
(*** the table of zetas as a read-only object                           ***)

let ntt_top_template =
  let lay l = mk_comb(mk_comb(mk_comb(mk_comb(
     mk_const("ntt_gcc12_O2_layer_events_" ^ string_of_int l,[]),`a:int64`),
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
   `\s. read X7 s = word L /\ read X12 s = word zetas /\
        read X13 s = a /\ read X14 s = word_add a (word 2) /\
        read X16 s = word 1 /\ read X17 s = word 256 /\
        read X30 s = returnaddress`
  and endtm =
   `\s. read X15 s = word(L + 1) /\ read X12 s = word zetas /\
        read X13 s = a /\ read X14 s = word_add a (word 2) /\
        read X16 s = word 1 /\ read X17 s = word 256 /\
        read X30 s = returnaddress` in
  let mk tm l =
    rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`] tm))) in
  (fun l -> mk headtm l),(fun l -> mk endtm l);;

let ntt_layer_events_inst l ev =
  SPECL [ev; `a:int64`; `zetas:num`; `pc:num`; `returnaddress:int64`]
        (el l NTT_GCC12_O2_LAYER_EVENTS);;

let NTT_SAFE_TOP_TAC =
  CONCRETIZE_F_EVENTS_TAC ntt_top_template THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xc4` (ntt_safe_layerend_tm 6) THEN
  CONJ_TAC THENL [ALL_TAC; LSAFE_SIM_TAC ALL_TAC 3] THEN
  MAP_EVERY (fun l ->
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x2c` (ntt_safe_layerhead_tm l) THEN
    CONJ_TAC THENL [ALL_TAC; EVENTS_LEMMA_TAC (ntt_layer_events_inst l)] THEN
    if l = 0 then ALL_TAC else
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xc4` (ntt_safe_layerend_tm (l - 1)) THEN
    CONJ_TAC THENL [ALL_TAC; LSAFE_SIM_TAC ALL_TAC 6]) (rev(0--6)) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--3) THEN
  FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP ADRP_ADD_FOLD) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC (4--11) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;


let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word zetas:int64`,`256`]
    ~keep_maychanges:false
    (assoc "mlkem_reduce" subroutine_signatures)
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e a zetas pc returnaddress.
       adrp_within_bounds (word zetas) (word pc) /\
       ALL (nonoverlapping (a,512)) [word pc,224; word zetas,256]
       ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  (mlkem_native_poly_ntt_gcc12_O2_mc pc zetas) /\
                read PC s = word pc /\
                bytes_loaded s (word zetas) mlk_zetas_data /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a] s /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a zetas pc returnaddress /\
                  memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
           (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN NTT_SAFE_TOP_TAC);;
