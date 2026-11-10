(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward NTT: the proof (see poly_ntt_spec.ml), as for AArch64             *)
(* (arm/proofs/mldsa_native/gcc12_O2/poly_ntt_proof.ml), whose structure     *)
(* this follows: a lemma for one block covers the inner loop, a lemma for    *)
(* each layer the loop over its blocks, and the main proof the 8 layers one  *)
(* after the other. Each of them states the values and the events together,  *)
(* as the FULL theorem does; the events of a block and of a layer are named  *)
(* by new_specification, as functions of the addresses (and of the position  *)
(* of the block). The lemmas are about the code after the pushes, with the   *)
(* slot in the red zone where each butterfly keeps its product as a region   *)
(* rz of their own, and the main proof applies them with rz the lowest 8     *)
(* bytes of the stack frame, below the 6 registers saved.                    *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/poly_ntt_spec.ml";;
needs "x86/proofs/utils/mldsa_native_ntt.ml";;

(* ------------------------------------------------------------------------- *)
(* One block, from the increment of the index of the zetas through the inner *)
(* loop to the bounds of the next block: the coefficients from start, in     *)
(* pairs len apart, with zeta z, whose sign extension is in RDI. The loop    *)
(* test is the end of the body of the inner loop, as                         *)
(* ENSURES_EVENTS_WHILE_UP2_TAC requires, and the events of the block depend *)
(* on a, pc, rz, start and len only. Each butterfly keeps the product of the *)
(* zeta and a coefficient in the red zone, at rz, and reads its low 32 bits  *)
(* from there (see NTT_MONTRED_LANE).                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_BLOCK_FULL = prove
 (`exists f_ev_blk.
   forall e a pc zt rz z start len k m wbx.
     aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
     nonoverlapping (a,1024) (word pc,libmldsa_size) /\
     nonoverlapping (a,1024) (zt,1024) /\
     nonoverlapping (a,1024) (rz,8) /\
     nonoverlapping (rz,8) (word pc,libmldsa_size) /\
     nonoverlapping (rz,8) (zt,1024) /\
     1 <= len /\ start + 2 * len <= 256 /\ k < 256
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
               read RIP s = word(pc + mldsa_poly_ntt_loop1) /\
               read RAX s = word start /\ read RDX s = word(start + len) /\
               read RSI s = word k /\ read R9 s = word(2 * len) /\
               read RDI s = word_sx(z:int32) /\
               read R13 s = a /\ read R14 s = word_add a (word 4) /\
               read RBP s = zt /\ read RBX s = wbx /\
               read RSP s = word_add rz (word 8) /\
               (!k. k < 256
                    ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                        mld_zeta k) /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        m i) /\
               read events s = e)
          (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
               read RIP s = word(pc + mldsa_poly_ntt_loop1_test) /\
               read RAX s = word(start + 2 * len) /\
               read RDX s = word(start + 3 * len) /\
               read RSI s = word(k + 1) /\ read R9 s = word(2 * len) /\
               read RDI s = word_sx z /\
               read R13 s = a /\ read R14 s = word_add a (word 4) /\
               read RBP s = zt /\ read RBX s = wbx /\
               read RSP s = word_add rz (word 8) /\
               (!k. k < 256
                    ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                        mld_zeta k) /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        mld_ntt_block z start len m i) /\
               (exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_ev_blk a pc rz start len /\
                  memaccess_inbounds e2 [a,1024; zt,1024; rz,8]
                                        [a,1024; rz,8]))
          (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; R8; R10; R11; R12; R15] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,1024); memory :> bytes(rz,8)])`,
  let EXEC = MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num) (rz:int64) (start:num) (len:num).
      APPEND (f_ev_blkend a pc rz start len)
        (APPEND (ENUMERATEL len (\j. f_ev_bfly a pc rz start len j))
                (f_ev_blkhead a pc rz start len))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `pc:num`; `zt:int64`; `rz:int64`;
    `z:int32`; `start:num`; `len:num`; `k:num`; `m:num->int32`;
    `wbx:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `len:num` `pc + mldsa_poly_ntt_loop2`
   `pc + mldsa_poly_ntt_loop2_exit`
   `\jj s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
           read R8 s = word_add a (word(4 * (start + jj))) /\
           read R12 s = word_add a (word(4 * (start + len))) /\
           read RCX s = word len /\
           read RAX s = word start /\ read RDX s = word(start + len) /\
           read RSI s = word(k + 1) /\ read R9 s = word(2 * len) /\
           read RDI s = word_sx(z:int32) /\
           read R13 s = a /\ read R14 s = word_add a (word 4) /\
           read RBP s = zt /\ read RBX s = wbx /\
           read RSP s = word_add rz (word 8) /\
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
    X86_STEPS_TAC EXEC (1--2) THEN W32_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC EXEC (3--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `~(a <= i /\ i < a:num)`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `start < 2 EXP 32 /\ start + len < 2 EXP 32`
     (fun th -> REWRITE_TAC[MATCH_MP WORD_ZX_ZX_SMALL (CONJUNCT1 th);
                            MATCH_MP WORD_ZX_ZX_SMALL (CONJUNCT2 th)]) THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    W(fun (_,w) -> if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC
                   else CONV_TAC WORD_RULE ORELSE WORD_SMALL_TAC);

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
    REWRITE_TAC[ARITH_RULE
     `4 * (start + len + jj) = 4 * (start + jj) + 4 * len`] THEN
    DISCH_TAC THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `jj < len
      ==> ~(start <= start + jj /\ start + jj < start + jj) /\
          ~(start + len <= start + jj /\ start + jj < start + len + jj)`] THEN
    DISCH_TAC THEN VAL_INT64_TAC `len:num` THEN
    X86_STEPS_TAC EXEC (1--3) THEN READ_BYTES64_SPLIT_TAC THEN
    X86_STEPS_TAC EXEC (4--20) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NTT_MONTRED_LANE; GSYM mld_fqmul]) THEN
    X86_STEPS_TAC EXEC (21--22) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THENL
     [ALL_TAC; DISCHARGE_SAFETY_PROPERTY_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i = start + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LE_ADD; ARITH_RULE `start + jj < start + jj + 1`] THEN
      REWRITE_TAC[mld_ntt_block; LE_ADD] THEN
      ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN REWRITE_TAC[ADD_AC];
      ALL_TAC] THEN
    ASM_CASES_TAC `i = start + len + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN
      REWRITE_TAC[ARITH_RULE
       `4 * (start + len + jj) = 4 * (start + jj) + 4 * len`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `start + len + jj < start + len + jj + 1`;
                  ARITH_RULE `start + len <= start + len + jj`] THEN
      REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN
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

    FULL_INIT_TAC THEN X86_STEPS_TAC EXEC (1--2) THEN
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
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN NUM_ASM_ARITH_TAC]);;

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_BLOCK_EVENTS =
  new_specification ["mldsa_ntt_gcc12_O2_block_events"]
    MLDSA_NATIVE_POLY_NTT_GCC12_O2_BLOCK_FULL;;

(* ------------------------------------------------------------------------- *)
(* One layer, with the blocks in a loop (except for the first layer). The    *)
(* body of the loop loads the zeta of the next block, does the block and     *)
(* tests whether there is another one. Each layer has its own lemma, from    *)
(* the setup of the layer to the test whether there is another layer, whose  *)
(* events are a function of a, pc, the address zt of the table and rz. Its   *)
(* postcondition leaves out the code, which the main proof keeps when it     *)
(* goes through the lemma with EVENTS_BIGSTEP_TAC.                           *)
(* ------------------------------------------------------------------------- *)

(*** Assertions at the block head and block end for layer l, block b ***)

let ntt_blockhead_tm,ntt_blockend_tm =
  let common =
   `read R9 s = word(2 * LEN) /\
    read R13 s = a /\ read R14 s = word_add a (word 4) /\
    read RBP s = zt /\ read RBX s = word(L + 1) /\
    read RSP s = word_add rz (word 8) /\
    (!k. k < 256
         ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
             mld_zeta k) /\
    (!i. i < 256
         ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
             mld_ntt_blocks L B r i)` in
  let headtm = mk_abs(`s:x86state`,list_mk_conj
   [`bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc`;
    `read RAX s = word(2 * LEN * B)`; `read RDX s = word(2 * LEN * B + LEN)`;
    `read RSI s = word(2 EXP L + B)`;
    `read RDI s = word_sx(mld_zeta(2 EXP L + B))`; common])
  and endtm = mk_abs(`s:x86state`,list_mk_conj
   [`bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc`;
    `read RAX s = word(2 * LEN * B)`; `read RDX s = word(2 * LEN * B + LEN)`;
    `read RSI s = word(2 EXP L + B)`; common]) in
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
   [ev; `a:int64`; `pc:num`; `zt:int64`; `rz:int64`;
    red `mld_zeta(2 EXP L + B)`;
    red `2 * LEN * B`; red `LEN:num`; red `2 EXP L + B`;
    red `mld_ntt_blocks L B r`; red `word(L + 1):int64`]
   MLDSA_NATIVE_POLY_NTT_GCC12_O2_BLOCK_EVENTS);;

(*** The layer head, setting up the registers for the first block ***)

let NTT_LAYERHEAD_FULL_TAC =
  FULL_INIT_TAC THEN
  X86_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REWRITE_TAC[mld_ntt_blocks] THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The test after a block, the end of the body of the loop over the ***)
(*** k blocks after the first one, whose counter is i                 ***)

let NTT_BLOCKTEST_FULL_TAC k =
  FULL_INIT_TAC THEN
  X86_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  X86_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  NTT_LOOP_COND_TAC `i:num` k THEN
  REPEAT CONJ_TAC THEN
  W(fun (_,w) -> if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC
                 else COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(*** The load of the zeta for block i + 1 of layer l ***)

let NTT_ZETA_FULL_TAC l =
  let n = rhs(concl(NUM_REDUCE_CONV
            (subst [mk_small_numeral l,`L:num`] `2 EXP L + i + 1`))) in
  FULL_INIT_TAC THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mld_zeta` (concl th)
    then MP_TAC(SPEC n th) else failwith "") THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  X86_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (1--1) THEN
  SUBGOAL_THEN (mk_comb(mk_comb(`(<):num->num->bool`,n),`2 EXP 32`))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WORD_ZX_ZX_SMALL th])) THENL
   [SIMPLE_ARITH_TAC; VAL_INT64_TAC n] THEN
  X86_STEPS_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC (2--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The statement for layer l (the number of layers done before it) ***)

let ntt_layer_full_goal l =
  subst [mk_small_numeral l,`L:num`; mk_small_numeral(l + 1),`L1:num`;
         mk_small_numeral(1 lsl l),`P:num`]
   `exists f_ev_lay.
     forall e a pc zt rz r.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      nonoverlapping (a,1024) (word pc,libmldsa_size) /\
      nonoverlapping (a,1024) (zt,1024) /\
      nonoverlapping (a,1024) (rz,8) /\
      nonoverlapping (rz,8) (word pc,libmldsa_size) /\
      nonoverlapping (rz,8) (zt,1024)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                read RIP s = word(pc + mldsa_poly_ntt_join1) /\
                read RCX s = word L /\
                read RDI s = word_sx(mld_zeta P) /\
                read R13 s = a /\ read R14 s = word_add a (word 4) /\
                read RBP s = zt /\ read RSP s = word_add rz (word 8) /\
                (!k. k < 256
                     ==> read(memory :> bytes32(word_add zt (word(4 * k))))
                           s = mld_zeta k) /\
                (!i. i < 256
                     ==> read(memory :> bytes32(word_add a (word(4 * i))))
                           s = r i) /\
                read events s = e)
           (\s. read RIP s = word(pc + mldsa_poly_ntt_loop1_exit) /\
                read RBX s = word L1 /\
                read R13 s = a /\ read R14 s = word_add a (word 4) /\
                read RBP s = zt /\ read RSP s = word_add rz (word 8) /\
                (!k. k < 256
                     ==> read(memory :> bytes32(word_add zt (word(4 * k))))
                           s = mld_zeta k) /\
                (!i. i < 256
                     ==> read(memory :> bytes32(word_add a (word(4 * i))))
                           s = mld_ntt_blocks L P r i) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_ev_lay a pc zt rz /\
                   memaccess_inbounds e2 [a,1024; zt,1024; rz,8]
                                         [a,1024; rz,8]))
           (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; RSI; RDI; R8; R9; R10; R11;
                       R12; R15] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(a,1024); memory :> bytes(rz,8)])`;;

(*** The events of layer l: the head, the first block and its test, ***)
(*** then for each further block its zeta, the block and the test   ***)

let ntt_layer_template l =
  let len = mk_small_numeral(1 lsl (7 - l)) in
  if l = 0 then
   subst [len,`LEN:num`]
   `\(a:int64) (pc:num) (zt:int64) (rz:int64).
      APPEND (f_ev_ltest0 a pc zt rz)
       (APPEND (mldsa_ntt_gcc12_O2_block_events a pc rz 0 LEN)
               (f_ev_lhead a pc zt rz))
     :(uarch_event)list`
  else
   subst [len,`LEN:num`; mk_small_numeral(1 lsl l - 1),`K:num`]
   `\(a:int64) (pc:num) (zt:int64) (rz:int64).
      APPEND (f_ev_lexit a pc zt rz)
       (APPEND
         (ENUMERATEL K
           (\i. APPEND (f_ev_ltest a pc zt rz i)
                 (APPEND (mldsa_ntt_gcc12_O2_block_events a pc rz
                           (2 * LEN * (i + 1)) LEN)
                         (f_ev_lzeta a pc zt rz i))))
         (APPEND (f_ev_ltest0 a pc zt rz)
           (APPEND (mldsa_ntt_gcc12_O2_block_events a pc rz 0 LEN)
                   (f_ev_lhead a pc zt rz))))
     :(uarch_event)list`;;

(*** The proof for layer l ***)

let NTT_LAYER_FULL_TAC l =
  let k = mk_small_numeral(1 lsl l - 1) in
  let blk0_tac =
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_ntt_loop1_test`
     (ntt_blockend_tm l `1`) THEN
    CONJ_TAC THENL
     [ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_ntt_loop1`
       (ntt_blockhead_tm l `0`) THEN
      CONJ_TAC THENL [NTT_LAYERHEAD_FULL_TAC; NTT_BLOCK_FULL_TAC l `0`];
      NTT_BLOCKTEST_FULL_TAC k] in
  CONCRETIZE_F_EVENTS_TAC (ntt_layer_template l) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `pc:num`; `zt:int64`; `rz:int64`;
    `r:num->int32`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  if l = 0 then blk0_tac else
  ENSURES_EVENTS_WHILE_UP2_TAC k `pc + mldsa_poly_ntt_loop1_next`
   `pc + mldsa_poly_ntt_loop1_exit`
   (mk_abs(`i:num`,ntt_blockend_tm l `i + 1`)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    REWRITE_TAC[ENUMERATEL; APPEND] THEN CONV_TAC NUM_REDUCE_CONV THEN
    blk0_tac;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_ntt_loop1_test`
     (subst [`i + 1`,`i:num`] (ntt_blockend_tm l `i + 1`)) THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
      ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_ntt_loop1`
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
(* The whole code: the 13 instructions that save the registers and set up    *)
(* the first layer, then each layer, by the lemma for it, with the 8         *)
(* instructions between layers that set up the next one, and the 9           *)
(* instructions after the last layer that restore the registers and return.  *)
(* The simulation goes through each layer lemma at once                      *)
(* (EVENTS_BIGSTEP_TAC), keeping what the lemma does not change, in          *)
(* particular the saved registers and the return address on the stack.       *)
(* ------------------------------------------------------------------------- *)

(*** The bytes of the table in the image ***)

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_ZETAS =
  IMAGE_DATA_RULE_FOR mldsa_native_libmldsa_gcc12_O2_mc mld_zetas_data
    (layout "rodata_mld_zetas");;

(*** Simulate through the lemma for layer l at step n, with rz the lowest ***)
(*** 8 bytes of the stack frame and the coefficients after l layers       ***)

let NTT_LAYER_SIM_TAC l n =
  let th = el l MLDSA_NATIVE_POLY_NTT_GCC12_O2_LAYER_EVENTS
  and r = if l = 0 then `x:num->int32` else
          mk_comb(mk_comb(`mld_ntt_layers`,mk_small_numeral l),
                  `x:num->int32`)
  and sth = CONV_RULE NUM_REDUCE_CONV
   (REWRITE_RULE[ADD1; CONJUNCT1 mld_ntt_layers]
     (INST [mk_small_numeral l,`l:num`]
           (SPEC_ALL (CONJUNCT2 mld_ntt_layers)))) in
  EVENTS_BIGSTEP_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC th
   [`a:int64`; `pc:num`; `word(pc + rodata_mld_zetas):int64`;
    `stackpointer:int64`; r] n THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM sth]);;

(*** The 8 instructions from the end of layer l to the head of the next ***)
(*** layer, from step n, with the load of zeta number 2 EXP (l + 1)     ***)

let NTT_LAYERBACK_SIM_TAC l n =
  let EXEC = MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC in
  X86_STEPS_TAC EXEC (n--n) THEN W32_DECIDE_FLAGS_TAC THEN
  X86_STEPS_TAC EXEC ((n+1)--(n+5)) THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mld_zeta` (concl th)
    then MP_TAC(CONV_RULE (NUM_REDUCE_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                  (SPEC (mk_small_numeral(1 lsl (l + 1))) th))
    else failwith "") THEN
  REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  X86_STEPS_TAC EXEC ((n+6)--(n+7));;

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC in
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES; mld_poly_ntt;
              fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `nonoverlapping (stackpointer:int64,8) (word pc,libmldsa_size) /\
    nonoverlapping (stackpointer:int64,8)
                   (word(pc + rodata_mld_zetas),1024) /\
    nonoverlapping (a:int64,1024) (word(pc + rodata_mld_zetas),1024)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN STRIP_TAC] THEN
  MAP_EVERY (fun (n,c) -> ENSURES_PRESERVED_TAC n c)
   [("rbx_init",`RBX`); ("rbp_init",`RBP`); ("r12_init",`R12`);
    ("r13_init",`R13`); ("r14_init",`R14`); ("r15_init",`R15`)] THEN
  FULL_INIT_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_ZETAS_LOADED o
    MATCH_MP MLDSA_NATIVE_POLY_NTT_GCC12_O2_ZETAS) THEN

  (*** The saves and the setup, with the address of the table and ***)
  (*** the first zeta in the forms of the lemma for layer 0       ***)

  X86_STEPS_TAC EXEC (1--13) THEN
  FIRST_X_ASSUM(MP_TAC o check
   (can (term_match [] `read RBP s = x`) o concl)) THEN
  REWRITE_TAC[RIPREL_ADDR_LEMMA; GSYM ADD_ASSOC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN DISCH_TAC THEN
  SUBGOAL_THEN `word 25847:int64 = word_sx(mld_zeta 1)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[mld_zeta; mld_zetas] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV);
    ALL_TAC] THEN

  (*** The layers ***)

  MAP_EVERY (fun l ->
    NTT_LAYER_SIM_TAC l (14 + 9 * l) THEN
    (if l = 7 then ALL_TAC else NTT_LAYERBACK_SIM_TAC l (15 + 9 * l)))
   (0--7) THEN

  (*** The restores and the return ***)

  X86_STEPS_TAC EXEC (78--78) THEN W32_DECIDE_FLAGS_TAC THEN
  X86_STEPS_TAC EXEC (79--86) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EVENTS_APPEND_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
