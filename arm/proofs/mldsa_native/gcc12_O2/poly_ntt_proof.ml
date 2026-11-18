(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward NTT: the proof (see poly_ntt_spec.ml). As for the C code compiled *)
(* from mlkem-native (proofs/mlkem_native/gcc12_O2/poly_ntt_proof.ml), whose *)
(* loop structure this follows, a lemma for one block covers the inner loop, *)
(* a lemma for each layer the loop over its blocks, and the main proof the 8 *)
(* layers one after the other. Each of them states the values and the events *)
(* together, as the FULL theorem does; the events of a block and of a layer  *)
(* are named by new_specification, as functions of the addresses (and of the *)
(* position of the block), as in the safety proof for mlkem-native.          *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/poly_ntt_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

(*** The value of a 64-bit index word for a small number ***)

let NTT_IDX_VAL_TAC tm =
  SUBGOAL_THEN
   (mk_eq(mk_comb(`val:int64->num`,mk_comb(`word:num->int64`,tm)),tm))
   ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* One block, from its setup through the inner loop: the coefficients from   *)
(* start, in pairs len apart, with zeta z. The loop test is the end of the   *)
(* body of the inner loop, as ENSURES_EVENTS_WHILE_UP2_TAC requires, and the *)
(* events of the block depend on a, pc, start and len only.                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_BLOCK_FULL = prove
 (`exists f_ev_blk.
   forall e a pc zt z start len k m w12 returnaddress.
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
               read X16 s = word 256 /\ read X30 s = returnaddress /\
               (!k. k < 256
                    ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                        mld_zeta k) /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        m i) /\
               read events s = e)
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
               read X16 s = word 256 /\ read X30 s = returnaddress /\
               (!k. k < 256
                    ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                        mld_zeta k) /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        mld_ntt_block z start len m i) /\
               (exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_ev_blk a pc start len /\
                  memaccess_inbounds e2 [a,1024; zt,1024] [a,1024]))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X7; X10; X11] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,1024)])`,
  let EXEC = MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num) (start:num) (len:num).
      APPEND (f_ev_blkend a pc start len)
        (APPEND (ENUMERATEL len (\j. f_ev_bfly a pc start len j))
                (f_ev_blkhead a pc start len))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `pc:num`; `zt:int64`; `z:int32`;
    `start:num`; `len:num`; `k:num`; `m:num->int32`; `w12:int64`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `len:num` `pc + mldsa_poly_ntt_loop3`
   `pc + mldsa_poly_ntt_loop3_exit`
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
           read X16 s = word 256 /\ read X30 s = returnaddress /\
           (!k. k < 256
                ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                    mld_zeta k) /\
           (!i. i < 256
                ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                    if start <= i /\ i < start + jj \/
                       start + len <= i /\ i < start + len + jj
                    then mld_ntt_block z start len m i else m i)` THEN
  REPEAT CONJ_TAC THENL
   [SIMPLE_ARITH_TAC;

    (*** Setting up the pointers for the inner loop ***)

    FULL_INIT_TAC THEN
    ARM_STEPS_TAC EXEC (1--2) THEN W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC EXEC (3--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `~(a <= i /\ i < a:num)`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `start < 2 EXP 32 /\ start + len < 2 EXP 32`
     (fun th -> REWRITE_TAC[MATCH_MP WORD_ZX_ZX_SMALL (CONJUNCT1 th);
                            MATCH_MP WORD_ZX_ZX_SMALL (CONJUNCT2 th)]) THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_SHL_WORD] THEN
    REPEAT CONJ_TAC THEN
    W(fun (_,w) -> if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC
                   else CONV_TAC WORD_RULE ORELSE WORD_SMALL_TAC);

    (*** The inner loop body, one butterfly, and the loop test ***)

    X_GEN_TAC `jj:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN NTT_IDX_VAL_TAC `start + jj:num` THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `m:num->int32` (concl th)
      then MP_TAC(SPEC `start + jj:num` th) THEN
           MP_TAC(SPEC `start + len + jj:num` th) THEN
           ASSUME_TAC(BETA_RULE(MATCH_MP (SPEC
             `\i. ~(i = start + jj) /\ ~(i = start + len + jj)`
             (MESON[] `!R P Q. (!i:num. P i ==> Q i)
                               ==> (!i. P i /\ R i ==> Q i)`)) th))
      else failwith "") THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `jj < len
      ==> ~(start <= start + len + jj /\ start + len + jj < start + jj) /\
          ~(start + len <= start + len + jj /\
            start + len + jj < start + len + jj)`] THEN
    REWRITE_TAC[ARITH_RULE
     `4 * (start + len + jj) = 4 * len + 4 * (start + jj)`] THEN
    DISCH_TAC THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `jj < len
      ==> ~(start <= start + jj /\ start + jj < start + jj) /\
          ~(start + len <= start + jj /\ start + jj < start + len + jj)`] THEN
    DISCH_TAC THEN
    ARM_STEPS_TAC EXEC (1--13) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_add (word(start + jj)) (word 1):int64 = word(start + jj + 1)`]) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC EXEC (14--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    NTT_LOOP_COND_TAC `jj:num` `len:num` THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; DISCHARGE_SAFETY_PROPERTY_TAC] THEN
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
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;

    (*** The end of the block ***)

    FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [WORD_SMALL_TAC; WORD_SMALL_TAC; ALL_TAC;
      DISCHARGE_SAFETY_PROPERTY_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `m:num->int32` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[mld_ntt_block] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC]);;

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_BLOCK_EVENTS =
  new_specification ["mldsa_ntt_gcc12_O2_block_events"]
    MLDSA_NATIVE_POLY_NTT_GCC12_O2_BLOCK_FULL;;

(* ------------------------------------------------------------------------- *)
(* One layer, with the blocks in a loop (except for the first layer). The    *)
(* body of the loop loads the zeta of the next block, does the block and     *)
(* tests whether there is another one. Each layer has its own lemma, whose   *)
(* events are a function of a, pc and the address of the table.              *)
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
    read X16 s = word 256 /\ read X30 s = returnaddress /\
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

let NTT_BLOCK_FULL_TAC l b =
  let red t =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (7 - l)),`LEN:num`;
      b,`B:num`] t))) in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral l,`l:num`; b,`b:num`]
          (SPEC_ALL(CONJUNCT2 mld_ntt_blocks)))) in
  NTT_EVENTS_LEMMA_TAC [sth] (fun ev -> SPECL
   [ev; `a:int64`; `pc:num`; `zt:int64`; red `mld_zeta(2 EXP L + B)`;
    red `2 * LEN * B`; red `LEN:num`; red `2 EXP L + B`;
    red `mld_ntt_blocks L B r`; red `word(L + 1):int64`;
    `returnaddress:int64`]
   MLDSA_NATIVE_POLY_NTT_GCC12_O2_BLOCK_EVENTS);;

(*** The layer head, setting up the registers for the first block ***)

let NTT_LAYERHEAD_FULL_TAC =
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REWRITE_TAC[mld_ntt_blocks] THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The test after a block, the end of the body of the loop over the ***)
(*** k blocks after the first one, whose counter is i                 ***)

let NTT_BLOCKTEST_FULL_TAC k =
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  NTT_LOOP_COND_TAC `i:num` k THEN
  REPEAT CONJ_TAC THEN
  W(fun (_,w) -> if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC
                 else COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(*** The load of the zeta for block i + 1 of layer l ***)

let NTT_ZETA_FULL_TAC l =
  FULL_INIT_TAC THEN
  ZETA_UXTW_TAC
   (rhs(concl(NUM_REDUCE_CONV
     (subst [mk_small_numeral l,`L:num`] `2 EXP L + i + 1`)))) THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The statement for layer l (the number of layers done before it) ***)

let ntt_layer_full_goal l =
  subst [mk_small_numeral l,`L:num`; mk_small_numeral(l + 1),`L1:num`;
         mk_small_numeral(1 lsl l),`P:num`]
   `exists f_ev_lay.
     forall e a pc zt r returnaddress.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      nonoverlapping (a,1024) (word pc,libmldsa_size) /\
      nonoverlapping (a,1024) (zt,1024)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_O2_mc /\
                read PC s = word(pc + mldsa_poly_ntt_loop1) /\
                read X3 s = word L /\
                read X8 s = word_zx(mld_zeta P) /\
                read X6 s = a /\ read X9 s = zt /\ read X13 s = word 1 /\
                read X14 s = word 4286586879 /\ read X15 s = word 58728449 /\
                read X16 s = word 256 /\ read X30 s = returnaddress /\
                (!k. k < 256
                     ==> read(memory :> bytes32(word_add zt (word(4 * k))))
                           s = mld_zeta k) /\
                (!i. i < 256
                     ==> read(memory :> bytes32(word_add a (word(4 * i))))
                           s = r i) /\
                read events s = e)
           (\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_O2_mc /\
                read PC s = word(pc + mldsa_poly_ntt_loop2_exit) /\
                read X12 s = word L1 /\
                read X6 s = a /\ read X9 s = zt /\ read X13 s = word 1 /\
                read X14 s = word 4286586879 /\ read X15 s = word 58728449 /\
                read X16 s = word 256 /\ read X30 s = returnaddress /\
                (!k. k < 256
                     ==> read(memory :> bytes32(word_add zt (word(4 * k))))
                           s = mld_zeta k) /\
                (!i. i < 256
                     ==> read(memory :> bytes32(word_add a (word(4 * i))))
                           s = mld_ntt_blocks L P r i) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_ev_lay a pc zt /\
                   memaccess_inbounds e2 [a,1024; zt,1024] [a,1024]))
           (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X7; X8; X10; X11; X12] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(a,1024)])`;;

(*** The events of layer l: the head, the first block and its test, ***)
(*** then for each further block its zeta, the block and the test   ***)

let ntt_layer_template l =
  let len = mk_small_numeral(1 lsl (7 - l)) in
  if l = 0 then
   subst [len,`LEN:num`]
   `\(a:int64) (pc:num) (zt:int64).
      APPEND (f_ev_ltest0 a pc zt)
       (APPEND (mldsa_ntt_gcc12_O2_block_events a pc 0 LEN)
               (f_ev_lhead a pc zt))
     :(uarch_event)list`
  else
   subst [len,`LEN:num`; mk_small_numeral(1 lsl l - 1),`K:num`]
   `\(a:int64) (pc:num) (zt:int64).
      APPEND (f_ev_lexit a pc zt)
       (APPEND
         (ENUMERATEL K
           (\i. APPEND (f_ev_ltest a pc zt i)
                 (APPEND (mldsa_ntt_gcc12_O2_block_events a pc
                           (2 * LEN * (i + 1)) LEN)
                         (f_ev_lzeta a pc zt i))))
         (APPEND (f_ev_ltest0 a pc zt)
           (APPEND (mldsa_ntt_gcc12_O2_block_events a pc 0 LEN)
                   (f_ev_lhead a pc zt))))
     :(uarch_event)list`;;

(*** The proof for layer l ***)

let NTT_LAYER_FULL_TAC l =
  let k = mk_small_numeral(1 lsl l - 1) in
  let blk0_tac =
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_ntt_loop2_test`
     (ntt_blockend_tm l `1`) THEN
    CONJ_TAC THENL
     [ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_ntt_loop2`
       (ntt_blockhead_tm l `0`) THEN
      CONJ_TAC THENL [NTT_LAYERHEAD_FULL_TAC; NTT_BLOCK_FULL_TAC l `0`];
      NTT_BLOCKTEST_FULL_TAC k] in
  CONCRETIZE_F_EVENTS_TAC (ntt_layer_template l) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `pc:num`; `zt:int64`;
    `r:num->int32`; `returnaddress:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  if l = 0 then blk0_tac else
  ENSURES_EVENTS_WHILE_UP2_TAC k `pc + mldsa_poly_ntt_loop2_next`
   `pc + mldsa_poly_ntt_loop2_exit`
   (mk_abs(`i:num`,ntt_blockend_tm l `i + 1`)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    REWRITE_TAC[ENUMERATEL; APPEND] THEN CONV_TAC NUM_REDUCE_CONV THEN
    blk0_tac;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_ntt_loop2_test`
     (subst [`i + 1`,`i:num`] (ntt_blockend_tm l `i + 1`)) THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
      ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_ntt_loop2`
       (ntt_blockhead_tm l `i + 1`) THEN
      CONJ_TAC THENL [NTT_ZETA_FULL_TAC l; NTT_BLOCK_FULL_TAC l `i + 1`];
      NTT_BLOCKTEST_FULL_TAC k];
    FULL_INIT_TAC THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_LAYER_EVENTS =
  map (fun l ->
        new_specification ["mldsa_ntt_gcc12_O2_layer_events_" ^
                           string_of_int l]
         (prove(ntt_layer_full_goal l,NTT_LAYER_FULL_TAC l)))
      (0--7);;

(* ------------------------------------------------------------------------- *)
(* The whole code, the 8 layers one after the other: correctness, constant   *)
(* time and memory safety.                                                   *)
(* ------------------------------------------------------------------------- *)

(*** The bytes of the table in the image, and its address ***)

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_ZETAS =
  MLDSA_NATIVE_IMAGE_DATA_RULE mld_zetas_data (layout "rodata_mld_zetas");;

let ntt_zetas_tm = `word(pc + rodata_mld_zetas):int64`;;

(*** Assertions at the layer head and layer end for layer l ***)

let ntt_layerhead_tm,ntt_layerend_tm =
  let common =
   `read X6 s = a /\
    read X9 s = word(pc + rodata_mld_zetas) /\
    read X13 s = word 1 /\
    read X14 s = word 4286586879 /\ read X15 s = word 58728449 /\
    read X16 s = word 256 /\ read X30 s = returnaddress /\
    (!k. k < 256
         ==> read(memory :> bytes32(word_add (word(pc + rodata_mld_zetas))
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

(*** The events: the setup, the layers and the steps between them, and ***)
(*** the return                                                        ***)

let ntt_full_template =
  let lay l =
    list_mk_comb(mk_const("mldsa_ntt_gcc12_O2_layer_events_" ^
                          string_of_int l,[]),
                 [`a:int64`; `pc:num`; ntt_zetas_tm])
  and fev n =
    list_mk_comb(mk_var(n,`:int64->num->int64->(uarch_event)list`),
                 [`a:int64`; `pc:num`; `returnaddress:int64`]) in
  let app x y = list_mk_icomb "APPEND" [x;y] in
  let rec chain l acc =
    let acc' = app (lay l) acc in
    if l = 7 then acc' else
    chain (l + 1) (app (fev ("f_ev_back" ^ string_of_int l)) acc') in
  list_mk_abs([`a:int64`; `pc:num`; `returnaddress:int64`],
              app (fev "f_ev_fin") (chain 0 (fev "f_ev_init")));;

(*** Apply the lemma for layer l at its head ***)

let NTT_LAYER_APPLY_FULL_TAC l =
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral l,`l:num`]
          (SPEC_ALL(CONJUNCT2 mld_ntt_layers)))) in
  NTT_EVENTS_LEMMA_TAC [sth] (fun ev -> SPECL
   [ev; `a:int64`; `pc:num`; ntt_zetas_tm;
    rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`]
      `mld_ntt_layers L x`)));
    `returnaddress:int64`]
   (el l MLDSA_NATIVE_POLY_NTT_GCC12_O2_LAYER_EVENTS));;

(*** Going from the end of layer l to the head of the next layer ***)

let NTT_LAYERBACK_FULL_TAC l =
  let EXEC = MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC in
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC EXEC (1--1) THEN W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC EXEC (2--4) THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mld_zeta` (concl th)
    then MP_TAC(CONV_RULE (NUM_REDUCE_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                  (SPEC (mk_small_numeral(1 lsl (l + 1))) th))
    else failwith "") THEN
  REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  ARM_STEPS_TAC EXEC (5--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC ntt_full_template THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `x:num->int32`; `pc:num`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; mld_poly_ntt; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `nonoverlapping (a:int64,1024)
                 (word(pc + rodata_mld_zetas),1024)`
  MP_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN DISCH_TAC THEN

  (*** The exit after the last layer and the return ***)

  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_ntt_loop2_exit`
   (ntt_layerend_tm 7) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    FULL_INIT_TAC THEN
    ARM_STEPS_TAC EXEC (1--1) THEN W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC EXEC (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  (*** The layers, from the last, with the loop back to the head ***)

  MAP_EVERY (fun l ->
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_ntt_loop1`
     (ntt_layerhead_tm l) THEN
    CONJ_TAC THENL [ALL_TAC; NTT_LAYER_APPLY_FULL_TAC l] THEN
    if l = 0 then ALL_TAC else
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_ntt_loop2_exit`
     (ntt_layerend_tm (l - 1)) THEN
    CONJ_TAC THENL [ALL_TAC; NTT_LAYERBACK_FULL_TAC (l - 1)])
   (rev(0--7)) THEN

  (*** Initialization, including the address of the table ***)

  FULL_INIT_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_ZETAS_LOADED o
    MATCH_MP MLDSA_NATIVE_POLY_NTT_GCC12_O2_ZETAS) THEN
  ARM_STEPS_TAC EXEC (1--1) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EXEC (2--10) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[CONJUNCT1 mld_ntt_layers] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mld_zeta; mld_zetas] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV);
    REWRITE_TAC[WORD_ADD];
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
