(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward NTT: the proof (see poly_ntt_spec.ml). As for the C code compiled *)
(* from mlkem-native (proofs/mlkem_native/gcc12_O2/poly_ntt.ml), whose loop  *)
(* structure this follows, a lemma for one block covers the inner loop, a    *)
(* lemma for one layer the loop over its blocks, and the main proof the 8    *)
(* layers one after the other.                                               *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/poly_ntt_spec.ml";;

(*** The value of a 64-bit index word for a small number ***)

let NTT_IDX_VAL_TAC tm =
  SUBGOAL_THEN
   (mk_eq(mk_comb(`val:int64->num`,mk_comb(`word:num->int64`,tm)),tm))
   ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    ASM_ARITH_TAC;
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* One block, from its setup through the inner loop: the coefficients from   *)
(* start, in pairs len apart, with zeta z.                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_BLOCK = prove
 (`!a pc zt z start len k m w12.
     aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
     nonoverlapping (a,1024) (word pc,libmldsa_size) /\
     nonoverlapping (a,1024) (zt,1024) /\
     1 <= len /\ start + 2 * len <= 256 /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mldsa_native_libmldsa_gcc12_O2_mc /\
               read PC s = word(pc + mldsa_poly_ntt_loop2) /\
               read X0 s = word start /\ read X2 s = word(start + len) /\
               read X3 s = word k /\ read X5 s = word(2 * len) /\
               read X6 s = a /\ read X8 s = word_zx(z:int32) /\
               read X9 s = zt /\
               read X12 s = w12 /\ read X13 s = word 1 /\
               read X14 s = word 4286586879 /\ read X15 s = word 58728449 /\
               read X16 s = word 256 /\
               (!k. k < 256
                    ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                        mld_zeta k) /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        m i))
          (\s. aligned_bytes_loaded s (word pc)
                 mldsa_native_libmldsa_gcc12_O2_mc /\
               read PC s = word(pc + mldsa_poly_ntt_loop2_test) /\
               read X0 s = word(start + 2 * len) /\
               read X2 s = word(start + 3 * len) /\
               read X3 s = word(k + 1) /\ read X5 s = word(2 * len) /\
               read X6 s = a /\ read X8 s = word_zx z /\
               read X9 s = zt /\
               read X12 s = w12 /\ read X13 s = word 1 /\
               read X14 s = word 4286586879 /\ read X15 s = word 58728449 /\
               read X16 s = word 256 /\
               (!k. k < 256
                    ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                        mld_zeta k) /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        mld_ntt_block z start len m i))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X7; X10; X11] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,1024)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC `len:num` `pc + mldsa_poly_ntt_loop3`
   `pc + mldsa_poly_ntt_loop3_test`
   `\jj s. aligned_bytes_loaded s (word pc)
             mldsa_native_libmldsa_gcc12_O2_mc /\
           read X0 s = word start /\ read X2 s = word(start + len) /\
           read X1 s = word_add a (word(4 * len)) /\
           read X4 s = word(start + jj) /\
           read X3 s = word(k + 1) /\ read X5 s = word(2 * len) /\
           read X6 s = a /\ read X8 s = word_zx(z:int32) /\
           read X9 s = zt /\
           read X12 s = w12 /\ read X13 s = word 1 /\
           read X14 s = word 4286586879 /\ read X15 s = word 58728449 /\
           read X16 s = word 256 /\
           (!k. k < 256
                ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                    mld_zeta k) /\
           (!i. i < 256
                ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                    if start <= i /\ i < start + jj \/
                       start + len <= i /\ i < start + len + jj
                    then mld_ntt_block z start len m i else m i)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** Setting up the pointers for the inner loop ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--2) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (3--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `~(a <= i /\ i < a:num)`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `start < 2 EXP 32 /\ start + len < 2 EXP 32`
     (fun th -> REWRITE_TAC[MATCH_MP WORD_ZX_ZX_SMALL (CONJUNCT1 th);
                            MATCH_MP WORD_ZX_ZX_SMALL (CONJUNCT2 th)]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_SHL_WORD] THEN
    REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    WORD_SMALL_TAC;

    (*** The inner loop body, one butterfly ***)

    X_GEN_TAC `jj:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    NTT_IDX_VAL_TAC `start + jj:num` THEN
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
    REWRITE_TAC[ARITH_RULE
     `4 * (start + len + jj) = 4 * len + 4 * (start + jj)`] THEN
    DISCH_TAC THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `jj < len
      ==> ~(start <= start + jj /\ start + jj < start + jj) /\
          ~(start + len <= start + jj /\ start + jj < start + len + jj)`] THEN
    DISCH_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i = start + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LE_ADD; ARITH_RULE `start + jj < start + jj + 1`] THEN
      FQMUL_SCALAR_TAC THEN
      REWRITE_TAC[mld_ntt_block; LE_ADD] THEN
      ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN REWRITE_TAC[ADD_AC];
      ALL_TAC] THEN
    ASM_CASES_TAC `i = start + len + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN
      REWRITE_TAC[ARITH_RULE
       `4 * (start + len + jj) = 4 * len + 4 * (start + jj)`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `start + len + jj < start + len + jj + 1`;
                  ARITH_RULE `start + len <= start + len + jj`] THEN
      FQMUL_SCALAR_TAC THEN
      REWRITE_TAC[mld_ntt_block] THEN
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
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The inner loop exit and the end of the block ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [WORD_SMALL_TAC; WORD_SMALL_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `m:num->int32` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[mld_ntt_block] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* One layer, with the blocks in a loop (except for the first layer).        *)
(* ------------------------------------------------------------------------- *)

(*** Prepare a load of zeta number n using UXTW indexing ***)

let ZETA_UXTW_TAC n =
  MP_TAC(SPEC n VAL_WORD_ZX_UXTW) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mld_zeta` (concl th)
    then MP_TAC(SPEC n th) else failwith "") THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC];;

(*** Assertions at the block head and block end for layer l, block b ***)

let ntt_blockhead_tm,ntt_blockend_tm =
  let common =
   `read X5 s = word(2 * LEN) /\
    read X6 s = a /\
    read X9 s = zt /\
    read X12 s = word(L + 1) /\ read X13 s = word 1 /\
    read X14 s = word 4286586879 /\ read X15 s = word 58728449 /\
    read X16 s = word 256 /\
    (!k. k < 256
         ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
             mld_zeta k) /\
    (!i. i < 256
         ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
             mld_ntt_blocks L B r i)` in
  let headtm = mk_abs(`s:armstate`,list_mk_conj
   [`aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc`;
    `read X0 s = word(2 * LEN * B)`; `read X2 s = word(2 * LEN * B + LEN)`;
    `read X3 s = word(2 EXP L + B)`;
    `read X8 s = word_zx(mld_zeta(2 EXP L + B))`; common])
  and endtm = mk_abs(`s:armstate`,list_mk_conj
   [`aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc`;
    `read X0 s = word(2 * LEN * B)`; `read X2 s = word(2 * LEN * B + LEN)`;
    `read X3 s = word(2 EXP L + B)`; common]) in
  let mk tm l b =
    let len = mk_small_numeral(1 lsl (7 - l)) in
    let tm' = subst [mk_small_numeral l,`L:num`; len,`LEN:num`; b,`B:num`]
                    tm in
    rhs(concl(NUM_REDUCE_CONV tm')) in
  (fun l b -> mk headtm l b),(fun l b -> mk endtm l b);;

(*** Apply the lemma for one block at the head of block b of layer l ***)

let NTT_BLOCK_TAC l b =
  let red t =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (7 - l)),`LEN:num`;
      b,`B:num`] t))) in
  let th = SPECL
   [`a:int64`; `pc:num`; `zt:int64`; red `mld_zeta(2 EXP L + B)`;
    red `2 * LEN * B`; red `LEN:num`; red `2 EXP L + B`;
    red `mld_ntt_blocks L B r`; red `word(L + 1):int64`]
   MLDSA_NATIVE_POLY_NTT_GCC12_O2_BLOCK in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral l,`l:num`; b,`b:num`]
          (SPEC_ALL(CONJUNCT2 mld_ntt_blocks)))) in
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
  ENSURES_SEQUENCE_TAC `pc + mldsa_poly_ntt_loop2`
   (ntt_blockhead_tm l `0`) THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[mld_ntt_blocks] THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The exit from the block loop at the end of the layer ***)

let NTT_LAYEREXIT_TAC =
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The whole layer l (the number of layers done before it) ***)

let NTT_LAYER_TAC l =
  NTT_LAYERHEAD_TAC l THEN
  ENSURES_SEQUENCE_TAC `pc + mldsa_poly_ntt_loop2_test`
   (ntt_blockend_tm l `1`) THEN
  CONJ_TAC THENL
   [NTT_BLOCK_TAC l `0`;
    if l = 0 then NTT_LAYEREXIT_TAC else
    ENSURES_WHILE_UP_TAC (mk_small_numeral(1 lsl l - 1))
      `pc + mldsa_poly_ntt_loop2_test` `pc + mldsa_poly_ntt_loop2_test`
      (mk_abs(`i:num`,ntt_blockend_tm l `i + 1`)) THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ENSURES_SEQUENCE_TAC `pc + mldsa_poly_ntt_loop2`
       (ntt_blockhead_tm l `i + 1`) THEN
      CONJ_TAC THENL
       [ENSURES_INIT_TAC "s0" THEN
        ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
        W32_DECIDE_FLAGS_TAC THEN
        ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--2) THEN
        ZETA_UXTW_TAC
         (rhs(concl(NUM_REDUCE_CONV
           (subst [mk_small_numeral l,`L:num`] `2 EXP L + i + 1`)))) THEN
        ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (3--4) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
        NTT_BLOCK_TAC l `i + 1`];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[];
      NTT_LAYEREXIT_TAC]];;

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_LAYER = prove
 (`!a pc zt l r.
     l < 8 /\
     aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
     nonoverlapping (a,1024) (word pc,libmldsa_size) /\
     nonoverlapping (a,1024) (zt,1024)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mldsa_native_libmldsa_gcc12_O2_mc /\
               read PC s = word(pc + mldsa_poly_ntt_loop1) /\
               read X3 s = word l /\
               read X8 s = word_zx(mld_zeta(2 EXP l)) /\
               read X6 s = a /\ read X9 s = zt /\ read X13 s = word 1 /\
               read X14 s = word 4286586879 /\ read X15 s = word 58728449 /\
               read X16 s = word 256 /\
               (!k. k < 256
                    ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                        mld_zeta k) /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        r i))
          (\s. aligned_bytes_loaded s (word pc)
                 mldsa_native_libmldsa_gcc12_O2_mc /\
               read PC s = word(pc + mldsa_poly_ntt_loop2_exit) /\
               read X12 s = word(l + 1) /\
               read X6 s = a /\ read X9 s = zt /\ read X13 s = word 1 /\
               read X14 s = word 4286586879 /\ read X15 s = word 58728449 /\
               read X16 s = word 256 /\
               (!k. k < 256
                    ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                        mld_zeta k) /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        mld_ntt_blocks l (2 EXP l) r i))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X7; X8; X10; X11; X12] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,1024)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SPEC_TAC(`l:num`,`l:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
  (map NTT_LAYER_TAC (0--7)));;

(* ------------------------------------------------------------------------- *)
(* The whole code computes mld_poly_ntt, the 8 layers one after the other.   *)
(* ------------------------------------------------------------------------- *)

(*** The bytes of the table in the image, and the table as 32-bit entries ***)

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_ZETAS =
  MLDSA_NATIVE_IMAGE_DATA_RULE mld_zetas_data (layout "rodata_mld_zetas");;

(*** Assertions at the layer head and layer end for layer l ***)

let ntt_layerhead_tm,ntt_layerend_tm =
  let common =
   `read X6 s = a /\
    read X9 s = word_add (word pc) (word rodata_mld_zetas) /\
    read X13 s = word 1 /\
    read X14 s = word 4286586879 /\ read X15 s = word 58728449 /\
    read X16 s = word 256 /\
    (!k. k < 256
         ==> read(memory :> bytes32(word_add
                (word_add (word pc) (word rodata_mld_zetas))
                (word(4 * k)))) s =
             mld_zeta k)` in
  let headtm = mk_abs(`s:armstate`,list_mk_conj
   [`aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc`;
    `read X3 s = word L`; `read X8 s = word_zx(mld_zeta(2 EXP L))`; common;
    `!i. i < 256
         ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
             mld_ntt_layers L x i`])
  and endtm = mk_abs(`s:armstate`,list_mk_conj
   [`aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc`;
    `read X12 s = word(L + 1)`; common;
    `!i. i < 256
         ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
             mld_ntt_layers (L + 1) x i`]) in
  let mk tm l =
    let tm' = subst [mk_small_numeral l,`L:num`] tm in
    rhs(concl(NUM_REDUCE_CONV tm')) in
  (fun l -> mk headtm l),(fun l -> mk endtm l);;

(*** Apply the lemma for layer l at its head ***)

let NTT_LAYER_APPLY_TAC l =
  let th = SPECL [`a:int64`; `pc:num`;
                  `word_add (word pc) (word rodata_mld_zetas):int64`;
                  mk_small_numeral l;
                  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`]
                     `mld_ntt_layers L x`)))]
                 MLDSA_NATIVE_POLY_NTT_GCC12_O2_LAYER in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral l,`l:num`]
          (SPEC_ALL(CONJUNCT2 mld_ntt_layers)))) in
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
  ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--4) THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mld_zeta` (concl th)
    then MP_TAC(CONV_RULE (NUM_REDUCE_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                  (SPEC (mk_small_numeral(1 lsl (l + 1))) th))
    else failwith "") THEN
  REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (5--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);;

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_LAYERS = prove
 (`!a (x:num->int32) pc.
    aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
    nonoverlapping (a,1024) (word pc,libmldsa_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mldsa_native_libmldsa_gcc12_O2_mc /\
           read PC s = word(pc + mldsa_poly_ntt) /\
           C_ARGUMENTS [a] s /\
           (!i. i < 256
                ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                    x i))
      (\s. read PC s = word(pc + mldsa_poly_ntt_ret) /\
           (!i. i < 256
                ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                    mld_ntt_layers 8 x i))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(a,1024)])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `nonoverlapping (a:int64,1024)
                 (word_add (word pc) (word rodata_mld_zetas),1024)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN

  (*** Initialization, including the address of the table ***)

  ENSURES_SEQUENCE_TAC
   `pc + mldsa_poly_ntt_loop1` (ntt_layerhead_tm 0) THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MLD_ZETAS_LOADED o
      MATCH_MP MLDSA_NATIVE_POLY_NTT_GCC12_O2_ZETAS) THEN
    REWRITE_TAC[WORD_ADD] THEN DISCH_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--10) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[CONJUNCT1 mld_ntt_layers] THEN
    REWRITE_TAC[mld_zeta; mld_zetas] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN

  (*** The layers, with the loop back to the head between them ***)

  MAP_EVERY (fun l ->
    ENSURES_SEQUENCE_TAC `pc + mldsa_poly_ntt_loop2_exit`
     (ntt_layerend_tm l) THEN
    CONJ_TAC THENL [NTT_LAYER_APPLY_TAC l; ALL_TAC] THEN
    if l = 7 then ALL_TAC else
    ENSURES_SEQUENCE_TAC `pc + mldsa_poly_ntt_loop1`
     (ntt_layerhead_tm (l + 1)) THEN
    CONJ_TAC THENL [NTT_LAYERBACK_TAC l; ALL_TAC]) (0--7) THEN

  (*** The exit after the last layer ***)

  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REWRITE_TAC[mld_poly_ntt] THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC
    MLDSA_NATIVE_POLY_NTT_GCC12_O2_LAYERS);;
