(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse NTT: the proof (see poly_invntt_tomont_spec.ml). As for the       *)
(* forward NTT (poly_ntt_proof.ml), a lemma for one block covers the inner   *)
(* loop, a lemma for each layer the loop over its blocks, and the main proof *)
(* the 8 layers one after the other, followed by the vectorized loop that    *)
(* scales the coefficients. Each of them states the values and the events    *)
(* together, as the FULL theorem does; the events of a block and of a layer  *)
(* are named by new_specification, as functions of the addresses (and of the *)
(* position of the block and the number of its zeta).                        *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

(*** Prepare a load of zeta number n using UXTW indexing ***)

let ZETA_UXTW4_TAC n =
  MP_TAC(SPEC n VAL_WORD_ZX4_UXTW) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mld_zeta` (concl th)
    then MP_TAC(SPEC n th) else failwith "") THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* One block, from the load of its zeta through the inner loop: the          *)
(* coefficients from start, in pairs len apart, with zeta number k, X4       *)
(* pointing at the upper coefficient and X3 = -len. The loop test, which     *)
(* compares X4 with the end of the block, is the end of the body of the      *)
(* inner loop, and the events of the block depend on a, pc, zt, start, len   *)
(* and k only.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_BLOCK_FULL = prove
 (`exists f_ev_blk.
   forall e a pc zt start len k m w12 returnaddress.
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
               read X30 s = returnaddress /\
               (!k. k < 256
                    ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                        mld_zeta k) /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        m i) /\
               read events s = e)
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
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X9; X17] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,1024)])`,
  let EXEC = MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num) (zt:int64) (start:num) (len:num) (k:num).
      APPEND (f_ev_blkend a pc zt start len k)
        (APPEND (ENUMERATEL len (\j. f_ev_bfly a pc zt start len k j))
                (f_ev_blkhead a pc zt start len k))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `pc:num`; `zt:int64`;
    `start:num`; `len:num`; `k:num`; `m:num->int32`; `w12:int64`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `len:num`
   `pc + mldsa_poly_invntt_tomont_loop3`
   `pc + mldsa_poly_invntt_tomont_loop3_exit`
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

    (*** Loading zeta and setting up the pointers for the inner loop ***)

    FULL_INIT_TAC THEN ZETA_UXTW4_TAC `k:num` THEN
    ARM_STEPS_TAC EXEC (1--5) THEN W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC EXEC (6--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    W32_SMALL_TAC THEN REWRITE_TAC[WORD_ZX_ZX_32_64_32; ADD_CLAUSES] THEN
    SUBGOAL_THEN `start < 2 EXP 32 /\ start + len < 2 EXP 32`
     (fun th -> REWRITE_TAC[MATCH_MP WORD_ZX_ZX_SMALL (CONJUNCT1 th);
                            MATCH_MP WORD_ZX_ZX_SMALL (CONJUNCT2 th)]) THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_SHL_WORD; ARITH_RULE `~(a <= i /\ i < a:num)`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    W(fun (_,w) ->
      if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC else
      FIRST [MATCH_MP_TAC WORD_ZX_SUB_1_SMALL THEN SIMPLE_ARITH_TAC;
             REWRITE_TAC[WORD_RULE `word_neg x = word_sub (word 0) x`] THEN
             WORD_SMALL_TAC]);

    (*** The inner loop body, one butterfly, and the loop test ***)

    X_GEN_TAC `jj:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
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
    ARM_STEPS_TAC EXEC (1--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; DISCHARGE_SAFETY_PROPERTY_TAC] THEN
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
    REWRITE_TAC[mld_invntt_block] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC]);;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_BLOCK_EVENTS =
  new_specification ["mldsa_invntt_gcc12_O2_block_events"]
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_BLOCK_FULL;;

(* ------------------------------------------------------------------------- *)
(* One layer m (from 8 down to 1), with its blocks in a loop whose body does *)
(* a block and tests whether there is another one. Each layer has its own    *)
(* lemma, whose events are a function of a, pc and the address of the        *)
(* table.                                                                    *)
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
    `read X30 s = returnaddress`;
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

let INVNTT_BLOCK_FULL_TAC m b =
  let red t =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral m,`M:num`; mk_small_numeral(1 lsl (8 - m)),`LEN:num`;
      b,`B:num`] t))) in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral m,`m:num`; b,`b:num`]
          (SPEC_ALL(CONJUNCT2 mld_invntt_blocks)))) in
  NTT_EVENTS_LEMMA_TAC [sth] (fun ev -> SPECL
   [ev; `a:int64`; `pc:num`; `zt:int64`;
    red `2 * LEN * B`; red `LEN:num`; red `2 EXP M - 1 - B`;
    red `mld_invntt_blocks M B r`; red `word M:int64`;
    `returnaddress:int64`]
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_BLOCK_EVENTS);;

(*** The statement for layer m ***)

let invntt_layer_full_goal m =
  subst [mk_small_numeral m,`M:num`; mk_small_numeral(1 lsl (m - 1)),`P:num`]
   `exists f_ev_lay.
     forall e a pc zt r returnaddress.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      nonoverlapping (a,1024) (word pc,libmldsa_size) /\
      nonoverlapping (a,1024) (zt,1024)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_O2_mc /\
                read PC s = word(pc + mldsa_poly_invntt_tomont_loop1) /\
                read X7 s = a /\ read X10 s = zt /\
                read X11 s = word_add a (word 4) /\ read X12 s = word M /\
                read X13 s = word 4286586879 /\ read X14 s = word 58728449 /\
                read X15 s = word 1 /\ read X16 s = word 256 /\
                read X30 s = returnaddress /\
                (!k. k < 256
                     ==> read(memory :> bytes32(word_add zt (word(4 * k))))
                           s = mld_zeta k) /\
                (!i. i < 256
                     ==> read(memory :> bytes32(word_add a (word(4 * i))))
                           s = r i) /\
                read events s = e)
           (\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_gcc12_O2_mc /\
                read PC s = word(pc + mldsa_poly_invntt_tomont_loop2_exit) /\
                read X7 s = a /\ read X10 s = zt /\
                read X11 s = word_add a (word 4) /\ read X12 s = word M /\
                read X13 s = word 4286586879 /\ read X14 s = word 58728449 /\
                read X15 s = word 1 /\ read X16 s = word 256 /\
                read X30 s = returnaddress /\
                (!k. k < 256
                     ==> read(memory :> bytes32(word_add zt (word(4 * k))))
                           s = mld_zeta k) /\
                (!i. i < 256
                     ==> read(memory :> bytes32(word_add a (word(4 * i))))
                           s = mld_invntt_blocks M P r i) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_ev_lay a pc zt /\
                   memaccess_inbounds e2 [a,1024; zt,1024] [a,1024]))
           (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X8; X9; X17] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(a,1024)])`;;

(*** The events of layer m: the head, then for each block the block ***)
(*** and the test whether there is another one                      ***)

let invntt_layer_template m =
  rhs(concl(NUM_REDUCE_CONV(subst
   [mk_small_numeral m,`M:num`; mk_small_numeral(1 lsl (8 - m)),`LEN:num`;
    mk_small_numeral(1 lsl (m - 1)),`NB:num`]
   `\(a:int64) (pc:num) (zt:int64).
      APPEND (f_ev_lexit a pc zt)
       (APPEND
         (ENUMERATEL NB
           (\i. APPEND (f_ev_ltest a pc zt i)
                 (mldsa_invntt_gcc12_O2_block_events a pc zt
                   (2 * LEN * i) LEN (2 EXP M - 1 - i))))
         (f_ev_lhead a pc zt))
     :(uarch_event)list`)));;

(*** The proof for layer m ***)

let INVNTT_LAYER_FULL_TAC m =
  let EXEC = MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC in
  let nb = mk_small_numeral(1 lsl (m - 1)) in
  let inv = mk_abs(`i:num`,invntt_block_tm m `i:num`) in
  CONCRETIZE_F_EVENTS_TAC (invntt_layer_template m) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `pc:num`; `zt:int64`;
    `r:num->int32`; `returnaddress:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC nb `pc + mldsa_poly_invntt_tomont_loop2`
   `pc + mldsa_poly_invntt_tomont_loop2_exit` inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The layer head, setting up the registers for the first block ***)

    REWRITE_TAC[ENUMERATEL; APPEND] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[mld_invntt_blocks] THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** Block i and the test whether there is another one ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_invntt_tomont_loop2_test`
     (subst [`i + 1`,`i:num`] (invntt_block_tm m `i:num`)) THEN
    CONJ_TAC THENL
     [INVNTT_BLOCK_FULL_TAC m `i:num`;
      FULL_INIT_TAC THEN
      ARM_STEPS_TAC EXEC (1--1) THEN W32_DECIDE_FLAGS_TAC THEN
      ARM_STEPS_TAC EXEC (2--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      NTT_LOOP_COND_TAC `i:num` nb THEN
      REPEAT CONJ_TAC THEN
      W(fun (_,w) -> if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC
                     else COND_CASES_TAC THEN ASM_REWRITE_TAC[])];

    (*** The end of the layer ***)

    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_LAYER_EVENTS =
  map (fun m ->
        new_specification ["mldsa_invntt_gcc12_O2_layer_events_" ^
                           string_of_int m]
         (prove(invntt_layer_full_goal m,INVNTT_LAYER_FULL_TAC m)))
      (1--8);;

(* ------------------------------------------------------------------------- *)
(* The whole code, the 8 layers one after the other, then the scaling by     *)
(* mld_fqscale: correctness, constant time and memory safety.                *)
(* ------------------------------------------------------------------------- *)

(*** The bytes of the table in the image, its address, and the vectors ***)
(*** of constants                                                      ***)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_ZETAS =
  MLDSA_NATIVE_IMAGE_DATA_RULE mld_zetas_data (layout "rodata_mld_zetas");;

let invntt_zetas_tm = `word(pc + rodata_mld_zetas):int64`;;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_CONSTANTS =
  map (fun d -> MLDSA_NATIVE_IMAGE_CONST_RULE d 128)
   [layout "mldsa_poly_invntt_tomont_const1";
    layout "mldsa_poly_invntt_tomont_const2";
    layout "mldsa_poly_invntt_tomont_const3"];;

(*** Assertions at the layer head and layer end for layer m ***)

let invntt_layerhead_tm,invntt_layerend_tm =
  let common =
   `read X7 s = a /\
    read X10 s = word(pc + rodata_mld_zetas) /\
    read X11 s = word_add a (word 4) /\
    read X13 s = word 4286586879 /\ read X14 s = word 58728449 /\
    read X15 s = word 1 /\ read X16 s = word 256 /\
    read X30 s = returnaddress /\
    (!k. k < 256
         ==> read(memory :> bytes32(word_add (word(pc + rodata_mld_zetas))
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

(*** The events: the setup, the layers from 8 down to 1 and the steps ***)
(*** between them, then the scaling loop with its setup and the return ***)

let invntt_full_template =
  let lay m =
    list_mk_comb(mk_const("mldsa_invntt_gcc12_O2_layer_events_" ^
                          string_of_int m,[]),
                 [`a:int64`; `pc:num`; invntt_zetas_tm])
  and fev n =
    list_mk_comb(mk_var(n,`:int64->num->int64->(uarch_event)list`),
                 [`a:int64`; `pc:num`; `returnaddress:int64`]) in
  let app x y = list_mk_icomb "APPEND" [x;y] in
  let rec chain m acc =
    let acc' = app (lay m) acc in
    if m = 1 then acc' else
    chain (m - 1) (app (fev ("f_ev_back" ^ string_of_int m)) acc') in
  let scale =
    app (fev "f_ev_fin")
     (app (list_mk_icomb "ENUMERATEL"
            [`64`;
             mk_abs(`i:num`,
               list_mk_comb(mk_var("f_ev_scale",
                 `:int64->num->int64->num->(uarch_event)list`),
                 [`a:int64`; `pc:num`; `returnaddress:int64`; `i:num`]))])
          (fev "f_ev_sinit")) in
  list_mk_abs([`a:int64`; `pc:num`; `returnaddress:int64`],
              app scale (chain 8 (fev "f_ev_init")));;

(*** Apply the lemma for layer m at its head ***)

let INVNTT_LAYER_APPLY_FULL_TAC m =
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral(8 - m),`n:num`]
          (SPEC_ALL(CONJUNCT2 mld_invntt_layers)))) in
  NTT_EVENTS_LEMMA_TAC [sth] (fun ev -> SPECL
   [ev; `a:int64`; `pc:num`; invntt_zetas_tm;
    rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral m,`M:num`]
      `mld_invntt_layers (8 - M) x`)));
    `returnaddress:int64`]
   (el (m - 1) MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_LAYER_EVENTS));;

(*** Going from the end of layer m to the head of layer m - 1 ***)

let INVNTT_LAYERBACK_FULL_TAC =
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC in
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

  (*** The exit from the layers and the scaling loop ***)

  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_invntt_tomont_loop2_exit`
   (invntt_layerend_tm 1) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + mldsa_poly_invntt_tomont_loop4`
     `pc + mldsa_poly_invntt_tomont_loop4_exit`
     `\i s. aligned_bytes_loaded s (word pc)
              mldsa_native_libmldsa_gcc12_O2_mc /\
            read X0 s = word_add a (word(16 * i)) /\
            read X1 s = word_add a (word 1024) /\
            read X30 s = returnaddress /\
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

      (*** The exit from the loop over the layers, and the setup ***)

      FULL_INIT_TAC THEN
      MAP_EVERY (fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th))
        MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_CONSTANTS THEN
      ARM_STEPS_TAC EXEC (1--4) THEN MLKEM_NATIVE_ADRP_TAC THEN
      ARM_STEPS_TAC EXEC (5--7) THEN MLKEM_NATIVE_ADRP_TAC THEN
      ARM_STEPS_TAC EXEC (8--11) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      (*** The body of the scaling loop, with the loop test ***)

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      FULL_INIT_TAC THEN
      VEC4_LOOP_BODY_TAC EXEC 9 THEN
      ARM_STEPS_TAC EXEC (10--11) THEN
      VEC4_FULL_FINAL_TAC [MONTRED_VEC_LANE]
       (REWRITE_TAC[mld_fqscale] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
        REWRITE_TAC[WORD_MUL_SYM]);

      (*** The return ***)

      FULL_EXIT_TAC EXEC 1]] THEN

  (*** The layers, from the last, with the loop back to the head ***)

  MAP_EVERY (fun m ->
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_invntt_tomont_loop1`
     (invntt_layerhead_tm m) THEN
    CONJ_TAC THENL [ALL_TAC; INVNTT_LAYER_APPLY_FULL_TAC m] THEN
    if m = 8 then ALL_TAC else
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_invntt_tomont_loop2_exit`
     (invntt_layerend_tm (m + 1)) THEN
    CONJ_TAC THENL [ALL_TAC; INVNTT_LAYERBACK_FULL_TAC])
   (1--8) THEN

  (*** Initialization, including the address of the table ***)

  FULL_INIT_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_ZETAS_LOADED o
    MATCH_MP MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_ZETAS) THEN
  ARM_STEPS_TAC EXEC (1--1) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EXEC (2--10) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[CONJUNCT1 mld_invntt_layers] THEN
  REPEAT CONJ_TAC THEN
  W(fun (_,w) -> if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC
                 else REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE));;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
