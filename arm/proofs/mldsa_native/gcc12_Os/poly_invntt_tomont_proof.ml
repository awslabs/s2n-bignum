(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse NTT with the factor mont / 256: the proof (see                    *)
(* poly_invntt_tomont_spec.ml). A lemma for one block covers the inner loop, *)
(* a lemma for each layer the loop over its blocks, a lemma the scaling      *)
(* loop, and the main proof the 8 layers and the scaling after one another.  *)
(* Each of them states the values and the events together, as the FULL       *)
(* theorem does; the events of a block, of a layer and of the scaling are    *)
(* named by new_specification, as functions of the addresses (and of the     *)
(* position of the block).                                                   *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

(*** The value of a 64-bit index word for a small number ***)

let NTT_IDX_VAL_TAC tm =
  SUBGOAL_THEN
   (mk_eq(mk_comb(`val:int64->num`,mk_comb(`word:num->int64`,tm)),tm))
   ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC];;

(*** Prepare a load of zeta number n using UXTW indexing: the index is the ***)
(*** 32-bit register that mov copies, and the load extends it again        ***)

let ZETA_UXTW_TAC n =
  MP_TAC(SPEC n VAL_WORD_ZX4_UXTW) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mld_zeta` (concl th)
    then MP_TAC(SPEC n th) else failwith "") THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC];;

(*** The sum of two 32-bit words, as the code computes it ***)

let ADD32_ZX = prove
 (`!x y:int32.
     word_zx(word_zx(word_add (word_zx(word_zx x:int64):int32)
                              (word_zx(word_zx y:int64):int32)):int64):int32 =
     word_add x y`,
  BITBLAST_TAC);;

(*** The negated zeta as the code computes it, in a 32-bit register ***)

let NEG_ZX = prove
 (`!z:int32.
     word_zx(word_sub (word 0) (word_zx(word_zx z:int64):int32)):int64 =
     word_zx(word_neg z)`,
  BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* One block, from its head (the load of its zeta, the check that it is not  *)
(* empty and the setup of the pointers) through the inner loop to the test   *)
(* of the loop over the blocks: the coefficients from start, in pairs len    *)
(* apart, with the negated zeta of index k. The loop test is the end of the  *)
(* body of the inner loop, as ENSURES_EVENTS_WHILE_UP2_TAC requires, and the *)
(* events of the block depend on a, pc, zt, start, len and k only.           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_BLOCK_FULL = prove
 (`exists f_ev_blk.
   forall e a pc zt start len k m w3 returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
     nonoverlapping (a,1024) (word pc,libmldsa_size) /\
     nonoverlapping (a,1024) (zt,1024) /\
     1 <= len /\ start + 2 * len <= 256 /\ 1 <= k /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mldsa_native_libmldsa_gcc12_Os_mc /\
               read PC s = word(pc + mldsa_poly_invntt_tomont_loop2) /\
               read X0 s = a /\ read X2 s = word(start + len) /\
               read X3 s = w3 /\ read X4 s = word start /\
               read X5 s = word k /\ read X9 s = zt /\
               read X11 s = word(2 * len) /\ read X12 s = word 256 /\
               read X13 s = word 1 /\ read X14 s = word 58728449 /\
               read X15 s = word 4286586879 /\
               read X30 s = returnaddress /\
               (!k. k < 256
                    ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                        mld_zeta k) /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        m i) /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mldsa_native_libmldsa_gcc12_Os_mc /\
               read PC s = word(pc + mldsa_poly_invntt_tomont_loop2_test) /\
               read X0 s = a /\ read X2 s = word(start + 3 * len) /\
               read X3 s = w3 /\ read X4 s = word(start + 2 * len) /\
               read X5 s = word(k - 1) /\ read X9 s = zt /\
               read X11 s = word(2 * len) /\ read X12 s = word 256 /\
               read X13 s = word 1 /\ read X14 s = word 58728449 /\
               read X15 s = word 4286586879 /\
               read X30 s = returnaddress /\
               (!k. k < 256
                    ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                        mld_zeta k) /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        mld_invntt_block (word_neg(mld_zeta k)) start len m
                          i) /\
               (exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_ev_blk a pc zt start len k /\
                  memaccess_inbounds e2 [a,1024; zt,1024] [a,1024]))
          (MAYCHANGE [PC; X1; X2; X4; X5; X6; X7; X8; X10] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,1024)])`,
  let EXEC = MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC in
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num) (zt:int64) (start:num) (len:num) (k:num).
      APPEND (f_ev_blkend a pc zt start len k)
        (APPEND (ENUMERATEL len (\j. f_ev_bfly a pc zt start len k j))
                (f_ev_blkhead a pc zt start len k))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `pc:num`; `zt:int64`; `start:num`;
    `len:num`; `k:num`; `m:num->int32`; `w3:int64`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `len:num`
   `pc + mldsa_poly_invntt_tomont_loop3`
   `pc + mldsa_poly_invntt_tomont_loop3_exit`
   `\jj s. aligned_bytes_loaded s (word pc)
             mldsa_native_libmldsa_gcc12_Os_mc /\
           read X0 s = a /\ read X2 s = word(start + len) /\
           read X3 s = w3 /\ read X4 s = word start /\
           read X5 s = word(k - 1) /\
           read X6 s = word(start + jj) /\
           read X8 s = word_add a (word(4 * (start + len + jj))) /\
           read X10 s = word_zx(word_neg(mld_zeta k:int32)) /\
           read X9 s = zt /\
           read X11 s = word(2 * len) /\ read X12 s = word 256 /\
           read X13 s = word 1 /\ read X14 s = word 58728449 /\
           read X15 s = word 4286586879 /\
           read X30 s = returnaddress /\
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
   [SIMPLE_ARITH_TAC;

    (*** The head of the block: the zeta, the check and the pointers ***)

    FULL_INIT_TAC THEN ZETA_UXTW_TAC `k:num` THEN
    ARM_STEPS_TAC EXEC (1--5) THEN W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC EXEC (6--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `~(a <= i /\ i < a:num)`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `start < 2 EXP 32 /\ start + len < 2 EXP 32`
     (fun th -> REWRITE_TAC[MATCH_MP WORD_ZX_ZX_SMALL (CONJUNCT1 th);
                            MATCH_MP WORD_ZX_ZX_SMALL (CONJUNCT2 th)]) THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_SHL_WORD] THEN
    REPEAT CONJ_TAC THEN
    W(fun (_,w) ->
      if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC
      else FIRST
       [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN NO_TAC;
        MATCH_MP_TAC WORD_ZX_SUB_1_SMALL THEN SIMPLE_ARITH_TAC;
        REWRITE_TAC[NEG_ZX] THEN NO_TAC;
        REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN CONV_TAC WORD_RULE;
        CONV_TAC WORD_RULE; WORD_SMALL_TAC;
        ASM_REWRITE_TAC[] THEN NO_TAC]);

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
    REPEAT CONJ_TAC THEN
    W(fun (_,w) ->
      if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC
      else if is_forall w then
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        ASM_CASES_TAC `i = start + jj` THENL
         [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[LE_ADD; ARITH_RULE `start + jj < start + jj + 1`] THEN
          REWRITE_TAC[mld_invntt_block; LE_ADD] THEN
          ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
          REWRITE_TAC[ADD32_ZX;
                      ARITH_RULE `(start + jj) + len = start + jj + len`;
                      ARITH_RULE `start + len + jj = start + jj + len`] THEN
          CONV_TAC WORD_RULE;
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
        AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC
      else (COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) ORELSE
           (CONV_TAC WORD_RULE));

    (*** The end of the block ***)

    FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    W(fun (_,w) ->
      if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC
      else if is_forall w then
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
          is_forall(concl th) && free_in `m:num->int32` (concl th))) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[mld_invntt_block] THEN
        REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC
      else FIRST [WORD_SMALL_TAC; ASM_REWRITE_TAC[] THEN NO_TAC])]);;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_BLOCK_EVENTS =
  new_specification ["mldsa_invntt_gcc12_Os_block_events"]
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_BLOCK_FULL;;

(* ------------------------------------------------------------------------- *)
(* One layer, with the blocks in a loop: the body of the loop is the block   *)
(* from its head, which loads its zeta, and the test whether there is        *)
(* another block. The layer with the counter M of the code (8 for the first  *)
(* layer) has 2^(M - 1) blocks of 2 * 2^(8 - M) coefficients. Each layer has *)
(* its own lemma, whose events are a function of a, pc and the address of    *)
(* the table.                                                                *)
(* ------------------------------------------------------------------------- *)

(*** Assertions at the block head and block end for the counter M, block B ***)

let invntt_blockhead_tm,invntt_blockend_tm =
  let common =
   `read X0 s = a /\
    read X3 s = word M /\
    read X11 s = word(2 * LEN) /\
    read X9 s = zt /\
    read X12 s = word 256 /\ read X13 s = word 1 /\
    read X14 s = word 58728449 /\ read X15 s = word 4286586879 /\
    read X30 s = returnaddress /\
    (!k. k < 256
         ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
             mld_zeta k)` in
  let headtm = mk_abs(`s:armstate`,list_mk_conj
   [`aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_Os_mc`;
    `read X4 s = word(2 * LEN * B)`; `read X2 s = word(2 * LEN * B + LEN)`;
    `read X5 s = word(2 EXP M - 1 - B)`; common;
    `!i. i < 256
         ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
             mld_invntt_blocks M B r i`])
  and endtm = mk_abs(`s:armstate`,list_mk_conj
   [`aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_Os_mc`;
    `read X4 s = word(2 * LEN * (B + 1))`;
    `read X2 s = word(2 * LEN * (B + 1) + LEN)`;
    `read X5 s = word(2 EXP M - 1 - (B + 1))`; common;
    `!i. i < 256
         ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
             mld_invntt_blocks M (B + 1) r i`]) in
  let mk tm m b =
    let len = mk_small_numeral(1 lsl (8 - m)) in
    let tm' = subst [mk_small_numeral m,`M:num`; len,`LEN:num`; b,`B:num`]
                    tm in
    rhs(concl(NUM_REDUCE_CONV tm')) in
  (fun m b -> mk headtm m b),(fun m b -> mk endtm m b);;

(*** Apply the lemma for one block at the head of block b, counter m ***)

let INVNTT_BLOCK_FULL_TAC m b =
  let red t =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral m,`M:num`; mk_small_numeral(1 lsl (8 - m)),`LEN:num`;
      b,`B:num`] t))) in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral m,`m:num`; b,`b:num`]
          (SPEC_ALL(CONJUNCT2 mld_invntt_blocks)))) in
  NTT_EVENTS_LEMMA_TAC [sth] (fun ev -> SPECL
   [ev; `a:int64`; `pc:num`; `zt:int64`; red `2 * LEN * B`; red `LEN:num`;
    red `2 EXP M - 1 - B`; red `mld_invntt_blocks M B r`;
    red `word M:int64`; `returnaddress:int64`]
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_BLOCK_EVENTS);;

(*** The layer head, setting up the registers for the first block ***)

let INVNTT_LAYERHEAD_FULL_TAC =
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (1--5) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REWRITE_TAC[mld_invntt_blocks] THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The test after a block, the end of the body of the loop over the ***)
(*** k blocks, whose counter is i                                     ***)

let INVNTT_BLOCKTEST_FULL_TAC k =
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  NTT_LOOP_COND_TAC `i:num` k THEN
  REPEAT CONJ_TAC THEN
  W(fun (_,w) -> if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC
                 else COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(*** The statement for the layer with counter m ***)

let invntt_layer_full_goal m =
  subst [mk_small_numeral m,`M:num`; mk_small_numeral(1 lsl (m - 1)),`K:num`]
   `exists f_ev_lay.
     forall e a pc zt r returnaddress.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      nonoverlapping (a,1024) (word pc,libmldsa_size) /\
      nonoverlapping (a,1024) (zt,1024)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_Os_mc /\
                read PC s = word(pc + mldsa_poly_invntt_tomont_loop1) /\
                read X0 s = a /\ read X3 s = word M /\ read X9 s = zt /\
                read X12 s = word 256 /\ read X13 s = word 1 /\
                read X14 s = word 58728449 /\ read X15 s = word 4286586879 /\
                read X30 s = returnaddress /\
                (!k. k < 256
                     ==> read(memory :> bytes32(word_add zt (word(4 * k))))
                           s = mld_zeta k) /\
                (!i. i < 256
                     ==> read(memory :> bytes32(word_add a (word(4 * i))))
                           s = r i) /\
                read events s = e)
           (\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_Os_mc /\
                read PC s = word(pc + mldsa_poly_invntt_tomont_loop2_exit) /\
                read X0 s = a /\ read X3 s = word M /\ read X9 s = zt /\
                read X12 s = word 256 /\ read X13 s = word 1 /\
                read X14 s = word 58728449 /\ read X15 s = word 4286586879 /\
                read X30 s = returnaddress /\
                (!k. k < 256
                     ==> read(memory :> bytes32(word_add zt (word(4 * k))))
                           s = mld_zeta k) /\
                (!i. i < 256
                     ==> read(memory :> bytes32(word_add a (word(4 * i))))
                           s = mld_invntt_blocks M K r i) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_ev_lay a pc zt /\
                   memaccess_inbounds e2 [a,1024; zt,1024] [a,1024]))
           (MAYCHANGE [PC; X1; X2; X4; X5; X6; X7; X8; X10; X11] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(a,1024)])`;;

(*** The events of the layer: the head, then for each block the block ***)
(*** and its test                                                     ***)

let invntt_layer_template m =
  let len = mk_small_numeral(1 lsl (8 - m)) in
  subst [len,`LEN:num`; mk_small_numeral(1 lsl (m - 1)),`K:num`;
         mk_small_numeral((1 lsl m) - 1),`P:num`]
   `\(a:int64) (pc:num) (zt:int64).
      APPEND (f_ev_lexit a pc zt)
       (APPEND
         (ENUMERATEL K
           (\i. APPEND (f_ev_ltest a pc zt i)
                 (mldsa_invntt_gcc12_Os_block_events a pc zt (2 * LEN * i)
                    LEN (P - i))))
         (f_ev_lhead a pc zt))
     :(uarch_event)list`;;

(*** The proof for the layer with counter m ***)

let INVNTT_LAYER_FULL_TAC m =
  let k = mk_small_numeral(1 lsl (m - 1)) in
  CONCRETIZE_F_EVENTS_TAC (invntt_layer_template m) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `pc:num`; `zt:int64`;
    `r:num->int32`; `returnaddress:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC k `pc + mldsa_poly_invntt_tomont_loop2`
   `pc + mldsa_poly_invntt_tomont_loop2_exit`
   (mk_abs(`i:num`,invntt_blockhead_tm m `i:num`)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    INVNTT_LAYERHEAD_FULL_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_invntt_tomont_loop2_test`
     (invntt_blockend_tm m `i:num`) THEN
    CONJ_TAC THENL
     [INVNTT_BLOCK_FULL_TAC m `i:num`; INVNTT_BLOCKTEST_FULL_TAC k];
    FULL_INIT_TAC THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_LAYER_EVENTS =
  map (fun m ->
        new_specification ["mldsa_invntt_gcc12_Os_layer_events_" ^
                           string_of_int m]
         (prove(invntt_layer_full_goal m,INVNTT_LAYER_FULL_TAC m)))
      (1--8);;

(*** The product by 41978 and the Montgomery reduction, as the code does ***)
(*** them, are mld_fqscale                                              ***)

let FQSCALE_SCALAR = prove
 (`!a:int32.
     word_zx(word_ishr
      (iword(ival(iword(ival a * &41978):int64) +
             ival(word_mul (word_zx (iword(ival a * &41978):int64))
                           (word 58728449):int32) *
             -- &8380417):int64) 32):int32 =
     mld_fqscale a`,
  GEN_TAC THEN
  MP_TAC(SPECL [`a:int32`; `word 41978:int32`] FQMUL_SCALAR) THEN
  REWRITE_TAC[mld_fqmul; mld_fqscale] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[WORD_MUL_SYM]);;

(* ------------------------------------------------------------------------- *)
(* The scaling loop, from the end of the layers to the return: each          *)
(* coefficient is multiplied by 41978 = 2^56 mod q in the Montgomery sense,  *)
(* mld_fqscale. The loop test is the end of the body, as                     *)
(* ENSURES_EVENTS_WHILE_UP2_TAC requires, and the events of an iteration     *)
(* depend on its index only.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_SCALE_FULL = prove
 (`exists f_ev_scale.
   forall e a pc r returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
     nonoverlapping (a,1024) (word pc,libmldsa_size)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mldsa_native_libmldsa_gcc12_Os_mc /\
               read PC s = word(pc + mldsa_poly_invntt_tomont_loop1_exit) /\
               read X0 s = a /\ read X30 s = returnaddress /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        r i) /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        mld_fqscale (r i)) /\
               (exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_ev_scale a pc returnaddress /\
                  memaccess_inbounds e2 [a,1024] [a,1024]))
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,1024)])`,
  let EXEC = MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a pc returnaddress)
        (APPEND
          (ENUMERATEL 256 (\i. f_ev_loop a pc returnaddress i))
          (f_ev_prol a pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `pc:num`; `r:num->int32`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mldsa_poly_invntt_tomont_loop4`
   `pc + mldsa_poly_invntt_tomont_loop4_exit`
   `\i s. aligned_bytes_loaded s (word pc)
            mldsa_native_libmldsa_gcc12_Os_mc /\
          read X0 s = a /\ read X1 s = word i /\
          read X4 s = word 4286586879 /\ read X5 s = word 58728449 /\
          read X6 s = word 41978 /\ read X30 s = returnaddress /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   r j) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   mld_fqscale (r j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    FULL_INIT_TAC THEN
    ARM_STEPS_TAC EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `r:num->int32` (concl th) &&
        not(free_in `mld_fqscale` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `val(word i:int64) = i` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC EXEC (1--6) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; ADD_CLAUSES; INT_ADD_LID;
                                WORD_MUL_QINV_32; FQSCALE_SCALAR]) THEN
    ARM_STEPS_TAC EXEC (7--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
    LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The return ***)

    FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_SCALE_EVENTS =
  new_specification ["mldsa_invntt_gcc12_Os_scale_events"]
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_SCALE_FULL;;

(* ------------------------------------------------------------------------- *)
(* The whole code, the 8 layers and the scaling one after the other:         *)
(* correctness, constant time and memory safety. The layer n (n = 0, ..., 7  *)
(* layers done before it) has the counter 8 - n.                             *)
(* ------------------------------------------------------------------------- *)

(*** The bytes of the table in the image, and its address ***)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_ZETAS =
  MLDSA_NATIVE_IMAGE_DATA_RULE mld_zetas_data (layout "rodata_mld_zetas");;

let invntt_zetas_tm = `word(pc + rodata_mld_zetas):int64`;;

(*** Assertions at the head and the end of layer n, and before the scaling ***)

let invntt_layerhead_tm,invntt_layerend_tm,invntt_scalehead_tm =
  let common =
   `read X0 s = a /\
    read X9 s = word(pc + rodata_mld_zetas) /\
    read X12 s = word 256 /\ read X13 s = word 1 /\
    read X14 s = word 58728449 /\ read X15 s = word 4286586879 /\
    read X30 s = returnaddress /\
    (!k. k < 256
         ==> read(memory :> bytes32(word_add (word(pc + rodata_mld_zetas))
                                             (word(4 * k)))) s =
             mld_zeta k)` in
  let headtm = mk_abs(`s:armstate`,list_mk_conj
   [`aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_Os_mc`;
    `read X3 s = word(8 - N)`; common;
    `!i. i < 256
         ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
             mld_invntt_layers N x i`])
  and endtm = mk_abs(`s:armstate`,list_mk_conj
   [`aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_Os_mc`;
    `read X3 s = word(8 - N)`; common;
    `!i. i < 256
         ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
             mld_invntt_layers (N + 1) x i`])
  and scltm = mk_abs(`s:armstate`,list_mk_conj
   [`aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_Os_mc`;
    `read X0 s = a`; `read X30 s = returnaddress`;
    `!i. i < 256
         ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
             mld_invntt_layers 8 x i`]) in
  let mk tm n =
    let tm' = subst [mk_small_numeral n,`N:num`] tm in
    rhs(concl(NUM_REDUCE_CONV tm')) in
  (fun n -> mk headtm n),(fun n -> mk endtm n),scltm;;

(*** The events: the setup, the layers and the steps between them, the ***)
(*** scaling and the return                                           ***)

let invntt_full_template =
  let lay n =
    list_mk_comb(mk_const("mldsa_invntt_gcc12_Os_layer_events_" ^
                          string_of_int(8 - n),[]),
                 [`a:int64`; `pc:num`; invntt_zetas_tm])
  and fev n =
    list_mk_comb(mk_var(n,`:int64->num->int64->(uarch_event)list`),
                 [`a:int64`; `pc:num`; `returnaddress:int64`]) in
  let app x y = list_mk_icomb "APPEND" [x;y] in
  let rec chain n acc =
    let acc' = app (lay n) acc in
    if n = 7 then acc' else
    chain (n + 1) (app (fev ("f_ev_back" ^ string_of_int n)) acc') in
  let body = app (fev "f_ev_back7") (chain 0 (fev "f_ev_init")) in
  list_mk_abs([`a:int64`; `pc:num`; `returnaddress:int64`],
              app (list_mk_comb(
                    mk_const("mldsa_invntt_gcc12_Os_scale_events",[]),
                    [`a:int64`; `pc:num`; `returnaddress:int64`]))
                  body);;

(*** Apply the lemma for layer n at its head ***)

let INVNTT_LAYER_APPLY_FULL_TAC n =
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral n,`n:num`]
          (SPEC_ALL(CONJUNCT2 mld_invntt_layers)))) in
  NTT_EVENTS_LEMMA_TAC [sth] (fun ev -> SPECL
   [ev; `a:int64`; `pc:num`; invntt_zetas_tm;
    rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral n,`N:num`]
      `mld_invntt_layers N x`)));
    `returnaddress:int64`]
   (el (7 - n) MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_LAYER_EVENTS));;

(*** Going from the end of a layer to the head of the next layer, or to ***)
(*** the scaling after the last layer: the counter is decremented       ***)

let INVNTT_LAYERBACK_FULL_TAC =
  let EXEC = MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC in
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC EXEC (1--1) THEN W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC in
  CONCRETIZE_F_EVENTS_TAC invntt_full_template THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `x:num->int32`; `pc:num`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; mld_poly_invntt_tomont;
              fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `nonoverlapping (a:int64,1024)
                 (word(pc + rodata_mld_zetas),1024)`
  MP_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN DISCH_TAC THEN

  (*** The scaling and the return ***)

  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_invntt_tomont_loop1_exit`
   invntt_scalehead_tm THEN
  CONJ_TAC THENL
   [ALL_TAC;
    NTT_EVENTS_LEMMA_TAC [] (fun ev -> SPECL
     [ev; `a:int64`; `pc:num`; `mld_invntt_layers 8 x`;
      `returnaddress:int64`]
     MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_SCALE_EVENTS)] THEN

  (*** After the last layer ***)

  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_invntt_tomont_loop2_exit`
   (invntt_layerend_tm 7) THEN
  CONJ_TAC THENL [ALL_TAC; INVNTT_LAYERBACK_FULL_TAC] THEN

  (*** The layers, from the last, with the loop back to the head ***)

  MAP_EVERY (fun n ->
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_invntt_tomont_loop1`
     (invntt_layerhead_tm n) THEN
    CONJ_TAC THENL [ALL_TAC; INVNTT_LAYER_APPLY_FULL_TAC n] THEN
    if n = 0 then ALL_TAC else
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_invntt_tomont_loop2_exit`
     (invntt_layerend_tm (n - 1)) THEN
    CONJ_TAC THENL [ALL_TAC; INVNTT_LAYERBACK_FULL_TAC])
   (rev(0--7)) THEN

  (*** Initialization, including the address of the table ***)

  FULL_INIT_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_ZETAS_LOADED o
    MATCH_MP MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_ZETAS) THEN
  ARM_STEPS_TAC EXEC (1--1) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EXEC (2--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[CONJUNCT1 mld_invntt_layers] THEN
  REPEAT CONJ_TAC THEN
  W(fun (_,w) -> if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC
                 else REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE));;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_FULL);;
