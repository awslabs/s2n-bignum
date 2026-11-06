(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse NTT: the proof (see poly_invntt_tomont_spec.ml). As for the       *)
(* forward NTT (poly_ntt_proof.ml), a lemma for one block covers the inner   *)
(* loop, a lemma for one layer the loop over its blocks, and the main proof  *)
(* the 8 layers one after the other, followed by the vectorized loop that    *)
(* scales the coefficients.                                                  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/poly_invntt_tomont_spec.ml";;

(*** Prepare a load of zeta number n using UXTW indexing ***)

let ZETA_UXTW4_TAC n =
  MP_TAC(SPEC n VAL_WORD_ZX4_UXTW) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mld_zeta` (concl th)
    then MP_TAC(SPEC n th) else failwith "") THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* One block, from the load of its zeta through the inner loop: the         *)
(* coefficients from start, in pairs len apart, with zeta number k, X4       *)
(* pointing at the upper coefficient and X3 = -len.                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_BLOCK = prove
 (`!a pc zt start len k m w12.
     aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
     nonoverlapping (a,1024) (word pc,libmldsa_size) /\
     nonoverlapping (a,1024) (zt,1024) /\
     1 <= len /\ start + 2 * len <= 256 /\ 1 <= k /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mldsa_native_libmldsa_gcc12_O2_mc /\
               read PC s = word(pc + mldsa_poly_invntt_tomont_loop2) /\
               read X5 s = word k /\
               read X2 s = word start /\ read X1 s = word(start + len) /\
               read X8 s = word(2 * len) /\
               read X7 s = a /\ read X10 s = zt /\
               read X11 s = word_add a (word 4) /\ read X12 s = w12 /\
               read X13 s = word 4286586879 /\ read X14 s = word 58728449 /\
               read X15 s = word 1 /\ read X16 s = word 256 /\
               (!k. k < 256
                    ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                        mld_zeta k) /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        m i))
          (\s. aligned_bytes_loaded s (word pc)
                 mldsa_native_libmldsa_gcc12_O2_mc /\
               read PC s = word(pc + mldsa_poly_invntt_tomont_loop2_test) /\
               read X5 s = word(k - 1) /\
               read X2 s = word(start + 2 * len) /\
               read X1 s = word(start + 3 * len) /\
               read X8 s = word(2 * len) /\
               read X7 s = a /\ read X10 s = zt /\
               read X11 s = word_add a (word 4) /\ read X12 s = w12 /\
               read X13 s = word 4286586879 /\ read X14 s = word 58728449 /\
               read X15 s = word 1 /\ read X16 s = word 256 /\
               (!k. k < 256
                    ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                        mld_zeta k) /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        mld_invntt_block (word_neg(mld_zeta k)) start len m i))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X9; X17] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,1024)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC `len:num` `pc + mldsa_poly_invntt_tomont_loop3`
   `pc + mldsa_poly_invntt_tomont_loop3_test`
   `\jj s. aligned_bytes_loaded s (word pc)
             mldsa_native_libmldsa_gcc12_O2_mc /\
           read X4 s = word_add a (word(4 * (start + len + jj))) /\
           read X0 s = word_add a (word(4 * (start + 2 * len))) /\
           read X3 s = word_neg(word len) /\
           read X6 s = word_zx(word_neg(mld_zeta k)) /\
           read X5 s = word(k - 1) /\
           read X2 s = word start /\ read X1 s = word(start + len) /\
           read X8 s = word(2 * len) /\
           read X7 s = a /\ read X10 s = zt /\
           read X11 s = word_add a (word 4) /\ read X12 s = w12 /\
           read X13 s = word 4286586879 /\ read X14 s = word 58728449 /\
           read X15 s = word 1 /\ read X16 s = word 256 /\
           (!k. k < 256
                ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                    mld_zeta k) /\
           (!i. i < 256
                ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                    if start <= i /\ i < start + jj \/
                       start + len <= i /\ i < start + len + jj
                    then mld_invntt_block (word_neg(mld_zeta k)) start len m i
                    else m i)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** Loading zeta and setting up the pointers for the inner loop ***)

    ENSURES_INIT_TAC "s0" THEN
    ZETA_UXTW4_TAC `k:num` THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--5) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (6--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    W32_SMALL_TAC THEN REWRITE_TAC[WORD_ZX_ZX_32_64_32; ADD_CLAUSES] THEN
    SUBGOAL_THEN `start < 2 EXP 32 /\ start + len < 2 EXP 32`
     (fun th -> REWRITE_TAC[MATCH_MP WORD_ZX_ZX_SMALL (CONJUNCT1 th);
                            MATCH_MP WORD_ZX_ZX_SMALL (CONJUNCT2 th)]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_SHL_WORD; ARITH_RULE `~(a <= i /\ i < a:num)`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [MATCH_MP_TAC WORD_ZX_SUB_1_SMALL THEN ASM_ARITH_TAC;
           REWRITE_TAC[WORD_RULE `word_neg x = word_sub (word 0) x`] THEN
           WORD_SMALL_TAC];

    (*** The inner loop body, one butterfly ***)

    X_GEN_TAC `jj:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `m:num->int32` (concl th)
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
    DISCH_TAC THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LT_REFL; ARITH_RULE
     `jj < len
      ==> ~(start <= start + jj /\ start + jj < start + jj) /\
          ~(start + len <= start + jj /\ start + jj < start + len + jj)`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `word_add (word_add a (word(4 * (start + len + jj))))
               (word(4 * val(word_neg(word len):int64))):int64 =
      word_add a (word(4 * (start + jj)))`
    ASSUME_TAC THENL
     [REWRITE_TAC[WORD_4_VAL] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i = start + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LE_ADD; ARITH_RULE `start + jj < start + jj + 1`] THEN
      REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN
      REWRITE_TAC[mld_invntt_block; LE_ADD; LT_ADD_LCANCEL] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[ADD_AC] THEN
      REWRITE_TAC[WORD_ADD_SYM];
      ALL_TAC] THEN
    ASM_CASES_TAC `i = start + len + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `start + len + jj < start + len + jj + 1`;
                  ARITH_RULE `start + len <= start + len + jj`] THEN
      FQMUL_SCALAR_SWAP_TAC THEN
      REWRITE_TAC[mld_invntt_block] THEN
      ASM_SIMP_TAC[ARITH_RULE
       `jj < len ==> ~(start <= start + len + jj /\
                       start + len + jj < start + len) /\
                     start + len <= start + len + jj /\
                     start + len + jj < start + 2 * len`] THEN
      REWRITE_TAC[ARITH_RULE `(start + len + jj) - len = start + jj`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `m:num->int32` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;

    (*** The inner loop back-edge ***)

    X_GEN_TAC `jj:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The inner loop exit and the end of the block ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (2--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [WORD_SMALL_TAC; WORD_SMALL_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `m:num->int32` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[mld_invntt_block] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* One layer m (from 8 down to 1), with the blocks in a loop (except for the *)
(* last layer, which has one block).                                         *)
(* ------------------------------------------------------------------------- *)

(*** The assertion at the head and at the end of block b of layer m,  ***)
(*** which differ only in the PC since each block loads its own zeta   ***)

let invntt_block_tm =
  let tm = mk_abs(`s:armstate`,list_mk_conj
   [`aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc`;
    `read X5 s = word(2 EXP M - 1 - B)`;
    `read X2 s = word(2 * LEN * B)`; `read X1 s = word(2 * LEN * B + LEN)`;
    `read X8 s = word(2 * LEN)`;
    `read X7 s = a`; `read X10 s = zt`;
    `read X11 s = word_add a (word 4)`; `read X12 s = word M`;
    `read X13 s = word 4286586879`; `read X14 s = word 58728449`;
    `read X15 s = word 1`; `read X16 s = word 256`;
    `!k. k < 256
         ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
             mld_zeta k`;
    `!i. i < 256
         ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
             mld_invntt_blocks M B r i`]) in
  fun m b ->
    let len = mk_small_numeral(1 lsl (8 - m)) in
    let tm' = subst [mk_small_numeral m,`M:num`; len,`LEN:num`; b,`B:num`]
                    tm in
    rhs(concl(NUM_REDUCE_CONV tm'));;

(*** Apply the block lemma at the head of block b of layer m ***)

let INVNTT_BLOCK_TAC m b =
  let red t =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral m,`M:num`; mk_small_numeral(1 lsl (8 - m)),`LEN:num`;
      b,`B:num`] t))) in
  let th = SPECL
   [`a:int64`; `pc:num`; `zt:int64`;
    red `2 * LEN * B`; red `LEN:num`; red `2 EXP M - 1 - B`;
    red `mld_invntt_blocks M B r`; red `word M:int64`]
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_BLOCK in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral m,`m:num`; b,`b:num`]
          (SPEC_ALL(CONJUNCT2 mld_invntt_blocks)))) in
  MP_TAC th THEN ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ENSURES_WEAKEN_TAC o CONV_RULE NUM_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[sth] THEN
    REPEAT CONJ_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;

(*** The whole layer m ***)

let INVNTT_LAYER_TAC m =
  let nb = 1 lsl (m - 1) in
  ENSURES_SEQUENCE_TAC `pc + mldsa_poly_invntt_tomont_loop2`
   (invntt_block_tm m `0`) THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[mld_invntt_blocks] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + mldsa_poly_invntt_tomont_loop2_test`
   (invntt_block_tm m `1`) THEN
  CONJ_TAC THENL [INVNTT_BLOCK_TAC m `0`; ALL_TAC] THEN
  (if nb = 1 then ALL_TAC else
   ENSURES_SEQUENCE_TAC `pc + mldsa_poly_invntt_tomont_loop2_test`
    (invntt_block_tm m (mk_small_numeral nb)) THEN
   CONJ_TAC THENL
    [ENSURES_WHILE_UP_TAC (mk_small_numeral(nb - 1))
      `pc + mldsa_poly_invntt_tomont_loop2_test`
      `pc + mldsa_poly_invntt_tomont_loop2_test`
      (mk_abs(`i:num`,invntt_block_tm m `i + 1`)) THEN
     REPEAT CONJ_TAC THENL
      [CONV_TAC NUM_REDUCE_CONV;
       ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
       CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
       X_GEN_TAC `i:num` THEN STRIP_TAC THEN
       ENSURES_SEQUENCE_TAC `pc + mldsa_poly_invntt_tomont_loop2`
        (invntt_block_tm m `i + 1`) THEN
       CONJ_TAC THENL
        [ENSURES_INIT_TAC "s0" THEN
         ARM_STEPS_TAC
          MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--1) THEN
         W32_DECIDE_FLAGS_TAC THEN
         ARM_STEPS_TAC
          MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (2--2) THEN
         ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
         INVNTT_BLOCK_TAC m `i + 1`];
       X_GEN_TAC `i:num` THEN STRIP_TAC THEN
       ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
       ASM_REWRITE_TAC[];
       ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
       RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[]];
     ALL_TAC]) THEN
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_LAYER = prove
 (`!a pc zt m r.
     0 < m /\ m < 9 /\
     aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
     nonoverlapping (a,1024) (word pc,libmldsa_size) /\
     nonoverlapping (a,1024) (zt,1024)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mldsa_native_libmldsa_gcc12_O2_mc /\
               read PC s = word(pc + mldsa_poly_invntt_tomont_loop1) /\
               read X7 s = a /\ read X10 s = zt /\
               read X11 s = word_add a (word 4) /\ read X12 s = word m /\
               read X13 s = word 4286586879 /\ read X14 s = word 58728449 /\
               read X15 s = word 1 /\ read X16 s = word 256 /\
               (!k. k < 256
                    ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                        mld_zeta k) /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        r i))
          (\s. aligned_bytes_loaded s (word pc)
                 mldsa_native_libmldsa_gcc12_O2_mc /\
               read PC s = word(pc + mldsa_poly_invntt_tomont_loop2_exit) /\
               read X7 s = a /\ read X10 s = zt /\
               read X11 s = word_add a (word 4) /\ read X12 s = word m /\
               read X13 s = word 4286586879 /\ read X14 s = word 58728449 /\
               read X15 s = word 1 /\ read X16 s = word 256 /\
               (!k. k < 256
                    ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                        mld_zeta k) /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        mld_invntt_blocks m (2 EXP (m - 1)) r i))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X8; X9; X17] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,1024)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN DISCH_TAC THEN
  REPEAT DISCH_TAC THEN
  UNDISCH_TAC `m < 9` THEN UNDISCH_TAC `0 < m` THEN
  REWRITE_TAC[IMP_IMP] THEN ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN
  SPEC_TAC(`m:num`,`m:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  (map INVNTT_LAYER_TAC (1--8)));;

(* ------------------------------------------------------------------------- *)
(* The 8 layers one after the other, then the scaling by mld_fqscale.        *)
(* ------------------------------------------------------------------------- *)

(*** The bytes of the table in the image, and the vectors of constants ***)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_ZETAS =
  MLDSA_NATIVE_IMAGE_DATA_RULE mld_zetas_data (layout "rodata_mld_zetas");;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_CONSTANTS =
  map (fun d -> MLDSA_NATIVE_IMAGE_CONST_RULE d 128)
   [layout "mldsa_poly_invntt_tomont_const1";
    layout "mldsa_poly_invntt_tomont_const2";
    layout "mldsa_poly_invntt_tomont_const3"];;

(*** Assertions at the layer head and layer end for layer m ***)

let invntt_layerhead_tm,invntt_layerend_tm =
  let common =
   `read X7 s = a /\
    read X10 s = word_add (word pc) (word rodata_mld_zetas) /\
    read X11 s = word_add a (word 4) /\
    read X13 s = word 4286586879 /\ read X14 s = word 58728449 /\
    read X15 s = word 1 /\ read X16 s = word 256 /\
    (!k. k < 256
         ==> read(memory :> bytes32(word_add
                (word_add (word pc) (word rodata_mld_zetas))
                (word(4 * k)))) s =
             mld_zeta k)` in
  let headtm = mk_abs(`s:armstate`,list_mk_conj
   [`aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc`;
    `read X12 s = word M`; common;
    `!i. i < 256
         ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
             mld_invntt_layers (8 - M) x i`])
  and endtm = mk_abs(`s:armstate`,list_mk_conj
   [`aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc`;
    `read X12 s = word M`; common;
    `!i. i < 256
         ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
             mld_invntt_layers (9 - M) x i`]) in
  let mk tm m =
    let tm' = subst [mk_small_numeral m,`M:num`] tm in
    rhs(concl(NUM_REDUCE_CONV tm')) in
  (fun m -> mk headtm m),(fun m -> mk endtm m);;

(*** Apply the lemma for layer m at its head ***)

let INVNTT_LAYER_APPLY_TAC m =
  let th = SPECL [`a:int64`; `pc:num`;
                  `word_add (word pc) (word rodata_mld_zetas):int64`;
                  mk_small_numeral m;
                  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral m,`M:num`]
                     `mld_invntt_layers (8 - M) x`)))]
                 MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_LAYER in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral(8 - m),`n:num`]
          (SPEC_ALL(CONJUNCT2 mld_invntt_layers)))) in
  MP_TAC th THEN ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN ENSURES_WEAKEN_TAC THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[sth];
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;

(*** Going from the end of layer m to the head of layer m - 1 ***)

let INVNTT_LAYERBACK_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_LAYERS = prove
 (`!a (x:num->int32) pc.
    aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
    nonoverlapping (a,1024) (word pc,libmldsa_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mldsa_native_libmldsa_gcc12_O2_mc /\
           read PC s = word(pc + mldsa_poly_invntt_tomont) /\
           C_ARGUMENTS [a] s /\
           (!i. i < 256
                ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                    x i))
      (\s. read PC s = word(pc + mldsa_poly_invntt_tomont_ret) /\
           (!i. i < 256
                ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                    mld_poly_invntt_tomont x i))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(a,1024)])`,
  let EXEC = MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC in
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; mld_poly_invntt_tomont] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `nonoverlapping (a:int64,1024)
                 (word_add (word pc) (word rodata_mld_zetas),1024)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN

  (*** Initialization, including the address of the table ***)

  ENSURES_SEQUENCE_TAC
   `pc + mldsa_poly_invntt_tomont_loop1` (invntt_layerhead_tm 8) THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MLD_ZETAS_LOADED o
      MATCH_MP MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_ZETAS) THEN
    REWRITE_TAC[WORD_ADD] THEN DISCH_TAC THEN
    ARM_STEPS_TAC EXEC (1--1) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC EXEC (2--10) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[CONJUNCT1 mld_invntt_layers] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[CONJUNCT1 mld_invntt_layers] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN

  (*** The layers, with the loop back to the head between them ***)

  MAP_EVERY (fun m ->
    ENSURES_SEQUENCE_TAC `pc + mldsa_poly_invntt_tomont_loop2_exit`
     (invntt_layerend_tm m) THEN
    CONJ_TAC THENL [INVNTT_LAYER_APPLY_TAC m; ALL_TAC] THEN
    if m = 1 then ALL_TAC else
    ENSURES_SEQUENCE_TAC `pc + mldsa_poly_invntt_tomont_loop1`
     (invntt_layerhead_tm (m - 1)) THEN
    CONJ_TAC THENL [INVNTT_LAYERBACK_TAC; ALL_TAC]) (rev(1--8)) THEN

  (*** The exit from the layers, and the scaling loop ***)

  ENSURES_SEQUENCE_TAC `pc + mldsa_poly_invntt_tomont_loop1_exit`
   (rhs(concl(NUM_REDUCE_CONV(subst [`9 - 1`,`L:num`]
     `\s. aligned_bytes_loaded s (word pc)
            mldsa_native_libmldsa_gcc12_O2_mc /\
          read X7 s = a /\
          (!i. i < 256
               ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                   mld_invntt_layers L x i)`)))) THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_WHILE_UP_TAC `64` `pc + mldsa_poly_invntt_tomont_loop4`
   `pc + mldsa_poly_invntt_tomont_loop4_test`
   `\i s. aligned_bytes_loaded s (word pc)
            mldsa_native_libmldsa_gcc12_O2_mc /\
          read X0 s = word_add a (word(16 * i)) /\
          read X1 s = word_add a (word 1024) /\
          read Q3 s = word 0xff801fffff801fffff801fffff801fff /\
          read Q4 s = word 0x0000a3fa0000a3fa0000a3fa0000a3fa /\
          read Q5 s = word 0x03802001038020010380200103802001 /\
          (!j. 4 * i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   mld_invntt_layers 8 x j) /\
          (!j. j < 4 * i
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   mld_fqscale(mld_invntt_layers 8 x j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization of the scaling loop ***)

    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th))
      MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_CONSTANTS THEN
    ARM_STEPS_TAC EXEC (1--2) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC EXEC (3--5) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC EXEC (6--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;

    (*** The body of the scaling loop ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    VEC4_LOOP_BODY_TAC EXEC 9 THEN
    VEC4_LOOP_FINAL_TAC [MONTRED_VEC_LANE] THEN
    REWRITE_TAC[mld_fqscale] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    REWRITE_TAC[WORD_MUL_SYM];

    (*** The loop-back branch and the exit ***)

    LOOP_BACK_TAC EXEC;
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC EXEC (1--1) THEN PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `mld_fqscale` (concl th)))]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  ARM_ADD_RETURN_NOSTACK_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_LAYERS);;
