(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse NTT: the proof (see poly_invntt_tomont_spec.ml), as for AArch64   *)
(* (arm/proofs/mldsa_native/gcc12_O2/poly_invntt_tomont_proof.ml) and the    *)
(* forward NTT (poly_ntt_proof.ml): a lemma for one block covers the inner   *)
(* loop, a lemma for each layer the loop over its blocks, a lemma the loop   *)
(* that scales the coefficients one at a time, and the main proof goes       *)
(* through the 8 layers and the scaling with them. Each of them states the   *)
(* values and the events together, as the FULL theorem does; the events of a *)
(* block, of a layer and of the scaling are named by new_specification, as   *)
(* functions of the addresses (and of the position of the block and the      *)
(* number of its zeta).                                                      *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/utils/mldsa_native_ntt.ml";;
needs "x86/proofs/utils/mldsa_native_pwacc.ml";;

(* ------------------------------------------------------------------------- *)
(* One block, from the load of its zeta through the inner loop to the bounds *)
(* of the next block: the coefficients from start, in pairs len apart, with  *)
(* zeta number k (RCX holds the sign extension of its negation). The loop    *)
(* test, which compares RBX with the end of the first half, is the end of    *)
(* the body of the inner loop, and the events of the block depend on a, pc,  *)
(* zt, rz, start, len and k only. Each butterfly keeps its product in the    *)
(* red zone at rz, as in the forward NTT (see NTT_MONTRED_LANE).             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_BLOCK_FULL = prove
 (`exists f_ev_blk.
   forall e a pc zt rz start len k m w15.
     aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
     nonoverlapping (a,1024) (word pc,libmldsa_size) /\
     nonoverlapping (a,1024) (zt,1024) /\
     nonoverlapping (a,1024) (rz,8) /\
     nonoverlapping (rz,8) (word pc,libmldsa_size) /\
     nonoverlapping (rz,8) (zt,1024) /\
     1 <= len /\ start + 2 * len <= 256 /\ 1 <= k /\ k < 256
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
               read RIP s = word(pc + mldsa_poly_invntt_tomont_loop2) /\
               read RDI s = word k /\
               read RDX s = word start /\ read RSI s = word(start + len) /\
               read R8 s = word(2 * len) /\
               read RAX s = a /\ read RBP s = word_add a (word 4) /\
               read R13 s = zt /\ read R15 s = w15 /\
               read RSP s = word_add rz (word 8) /\
               (!k. k < 256
                    ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                        mld_zeta k) /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        m i) /\
               read events s = e)
          (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
               read RIP s = word(pc + mldsa_poly_invntt_tomont_loop2_test) /\
               read RDI s = word(k - 1) /\
               read RDX s = word(start + 2 * len) /\
               read RSI s = word(start + 3 * len) /\
               read R8 s = word(2 * len) /\
               read RAX s = a /\ read RBP s = word_add a (word 4) /\
               read R13 s = zt /\ read R15 s = w15 /\
               read RSP s = word_add rz (word 8) /\
               (!k. k < 256
                    ==> read(memory :> bytes32(word_add zt (word(4 * k)))) s =
                        mld_zeta k) /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        mld_invntt_block (word_neg(mld_zeta k)) start len m
                                         i) /\
               (exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_ev_blk a pc zt rz start len k /\
                  memaccess_inbounds e2 [a,1024; zt,1024; rz,8]
                                        [a,1024; rz,8]))
          (MAYCHANGE [RIP; RBX; RCX; RDX; RSI; RDI; R9; R10; R11; R12; R14] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,1024); memory :> bytes(rz,8)])`,
  let EXEC = MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num) (zt:int64) (rz:int64) (start:num) (len:num) (k:num).
      APPEND (f_ev_blkend a pc zt rz start len k)
        (APPEND (ENUMERATEL len (\j. f_ev_bfly a pc zt rz start len k j))
                (f_ev_blkhead a pc zt rz start len k))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `pc:num`; `zt:int64`; `rz:int64`;
    `start:num`; `len:num`; `k:num`; `m:num->int32`; `w15:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `len:num`
   `pc + mldsa_poly_invntt_tomont_loop3`
   `pc + mldsa_poly_invntt_tomont_loop3_exit`
   `\jj s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
           read RBX s = word_add a (word(4 * (start + jj))) /\
           read R11 s = word_add a (word(4 * (start + len + jj))) /\
           read R14 s = word_add a (word(4 * (start + len))) /\
           read RCX s = word_sx(word_neg(mld_zeta k)) /\
           read RDI s = word(k - 1) /\
           read RDX s = word start /\ read RSI s = word(start + len) /\
           read R8 s = word(2 * len) /\
           read RAX s = a /\ read RBP s = word_add a (word 4) /\
           read R13 s = zt /\ read R15 s = w15 /\
           read RSP s = word_add rz (word 8) /\
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

    FULL_INIT_TAC THEN
    FIRST_ASSUM(fun th ->
      if is_forall(concl th) && free_in `mld_zeta` (concl th)
      then MP_TAC(SPEC `k:num` th) else failwith "") THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
    X86_STEPS_TAC EXEC (1--2) THEN
    SUBGOAL_THEN `k < 2 EXP 32`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WORD_ZX_ZX_SMALL th]))
    THENL [SIMPLE_ARITH_TAC; VAL_INT64_TAC `k:num`] THEN
    X86_STEPS_TAC EXEC (3--5) THEN W32_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC EXEC (6--17) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_ZX_ZX_32_64_32; ADD_CLAUSES;
                ARITH_RULE `~(a <= i /\ i < a:num)`] THEN
    SUBGOAL_THEN `start < 2 EXP 32 /\ start + len < 2 EXP 32`
     (fun th -> REWRITE_TAC[MATCH_MP WORD_ZX_ZX_SMALL (CONJUNCT1 th);
                            MATCH_MP WORD_ZX_ZX_SMALL (CONJUNCT2 th)]) THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    W(fun (_,w) -> if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC
                   else WORD_SMALL_TAC);

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
    X86_STEPS_TAC EXEC (1--10) THEN READ_BYTES64_SPLIT_TAC THEN
    X86_STEPS_TAC EXEC (11--23) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NTT_MONTRED_LANE; GSYM mld_fqmul]) THEN
    X86_STEPS_TAC EXEC (24--25) THEN
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
      REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN
      REWRITE_TAC[mld_invntt_block; LE_ADD; LT_ADD_LCANCEL] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[ADD_AC] THEN
      REWRITE_TAC[WORD_ADD_SYM];
      ALL_TAC] THEN
    ASM_CASES_TAC `i = start + len + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `start + len + jj < start + len + jj + 1`;
                  ARITH_RULE `start + len <= start + len + jj`] THEN
      REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN
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
    REWRITE_TAC[mld_invntt_block] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN NUM_ASM_ARITH_TAC]);;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_BLOCK_EVENTS =
  new_specification ["mldsa_invntt_gcc12_O2_block_events"]
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_BLOCK_FULL;;

(* ------------------------------------------------------------------------- *)
(* One layer m (from 8 down to 1), with its blocks in a loop whose body does *)
(* a block and tests whether there is another one. Each layer has its own    *)
(* lemma, from the setup of the layer to the end of its last block, whose    *)
(* events are a function of a, pc, the address zt of the table and rz. Its   *)
(* postcondition leaves out the code, which the main proof keeps when it     *)
(* goes through the lemma with EVENTS_BIGSTEP_TAC.                           *)
(* ------------------------------------------------------------------------- *)

(*** The assertion at the head and at the end of block b of layer m,  ***)
(*** which differ only in the PC since each block loads its own zeta   ***)

let invntt_block_tm =
  let tm = mk_abs(`s:x86state`,list_mk_conj
   [`bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc`;
    `read RDI s = word(2 EXP M - 1 - B)`;
    `read RDX s = word(2 * LEN * B)`; `read RSI s = word(2 * LEN * B + LEN)`;
    `read R8 s = word(2 * LEN)`;
    `read RAX s = a`; `read RBP s = word_add a (word 4)`;
    `read R13 s = zt`; `read R15 s = word M`;
    `read RSP s = word_add rz (word 8)`;
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
   [ev; `a:int64`; `pc:num`; `zt:int64`; `rz:int64`;
    red `2 * LEN * B`; red `LEN:num`; red `2 EXP M - 1 - B`;
    red `mld_invntt_blocks M B r`; red `word M:int64`]
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_BLOCK_EVENTS);;

(*** The statement for layer m ***)

let invntt_layer_full_goal m =
  subst [mk_small_numeral m,`M:num`; mk_small_numeral(1 lsl (m - 1)),`P:num`]
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
                read RIP s = word(pc + mldsa_poly_invntt_tomont_loop1) /\
                read RCX s = word M /\
                read RAX s = a /\ read RBP s = word_add a (word 4) /\
                read R13 s = zt /\ read RSP s = word_add rz (word 8) /\
                (!k. k < 256
                     ==> read(memory :> bytes32(word_add zt (word(4 * k))))
                           s = mld_zeta k) /\
                (!i. i < 256
                     ==> read(memory :> bytes32(word_add a (word(4 * i))))
                           s = r i) /\
                read events s = e)
           (\s. read RIP s = word(pc + mldsa_poly_invntt_tomont_loop2_exit) /\
                read R15 s = word M /\
                read RAX s = a /\ read RBP s = word_add a (word 4) /\
                read R13 s = zt /\ read RSP s = word_add rz (word 8) /\
                (!k. k < 256
                     ==> read(memory :> bytes32(word_add zt (word(4 * k))))
                           s = mld_zeta k) /\
                (!i. i < 256
                     ==> read(memory :> bytes32(word_add a (word(4 * i))))
                           s = mld_invntt_blocks M P r i) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_ev_lay a pc zt rz /\
                   memaccess_inbounds e2 [a,1024; zt,1024; rz,8]
                                         [a,1024; rz,8]))
           (MAYCHANGE [RIP; RBX; RCX; RDX; RSI; RDI; R8; R9; R10; R11; R12;
                       R14; R15] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(a,1024); memory :> bytes(rz,8)])`;;

(*** The events of layer m: the head, then for each block the block ***)
(*** and the test whether there is another one                      ***)

let invntt_layer_template m =
  rhs(concl(NUM_REDUCE_CONV(subst
   [mk_small_numeral m,`M:num`; mk_small_numeral(1 lsl (8 - m)),`LEN:num`;
    mk_small_numeral(1 lsl (m - 1)),`NB:num`]
   `\(a:int64) (pc:num) (zt:int64) (rz:int64).
      APPEND (f_ev_lexit a pc zt rz)
       (APPEND
         (ENUMERATEL NB
           (\i. APPEND (f_ev_ltest a pc zt rz i)
                 (mldsa_invntt_gcc12_O2_block_events a pc zt rz
                   (2 * LEN * i) LEN (2 EXP M - 1 - i))))
         (f_ev_lhead a pc zt rz))
     :(uarch_event)list`)));;

(*** The proof for layer m ***)

let INVNTT_LAYER_FULL_TAC m =
  let EXEC = MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC in
  let nb = mk_small_numeral(1 lsl (m - 1)) in
  let inv = mk_abs(`i:num`,invntt_block_tm m `i:num`) in
  CONCRETIZE_F_EVENTS_TAC (invntt_layer_template m) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `pc:num`; `zt:int64`; `rz:int64`;
    `r:num->int32`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC nb `pc + mldsa_poly_invntt_tomont_loop2`
   `pc + mldsa_poly_invntt_tomont_loop2_exit` inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The layer head, setting up the registers for the first block ***)

    REWRITE_TAC[ENUMERATEL; APPEND] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FULL_INIT_TAC THEN X86_STEPS_TAC EXEC (1--9) THEN
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
      X86_STEPS_TAC EXEC (1--1) THEN W32_DECIDE_FLAGS_TAC THEN
      X86_STEPS_TAC EXEC (2--2) THEN
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
(* The loop that scales the coefficients by mld_fqscale, one per iteration,  *)
(* from the setup of its pointers, with its own lemma whose events are a     *)
(* function of a and pc. The scaling is the Montgomery reduction of the      *)
(* product with 41978 as the code does it in registers, as for the pointwise *)
(* products (see PWACC_MONTRED_LANE).                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SCALE_FULL = prove
 (`exists f_ev_scale.
   forall e a pc r.
     aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
     nonoverlapping (a,1024) (word pc,libmldsa_size)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
               read RIP s = word(pc + mldsa_poly_invntt_tomont_loop1_exit) /\
               read RAX s = a /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        r i) /\
               read events s = e)
          (\s. read RIP s = word(pc + mldsa_poly_invntt_tomont_loop4_exit) /\
               (!i. i < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        mld_fqscale(r i)) /\
               (exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_ev_scale a pc /\
                  memaccess_inbounds e2 [a,1024] [a,1024]))
          (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,1024)])`,
  let EXEC = MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num).
      APPEND (f_ev_send a pc)
        (APPEND (ENUMERATEL 256 (\i. f_ev_sloop a pc i)) (f_ev_shead a pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `pc:num`; `r:num->int32`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mldsa_poly_invntt_tomont_loop4`
   `pc + mldsa_poly_invntt_tomont_loop4_exit`
   `\i s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
          read RAX s = word_add a (word(4 * i)) /\
          read R8 s = word_add a (word 1024) /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   r j) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   mld_fqscale(r j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The setup of the pointers ***)

    FULL_INIT_TAC THEN X86_STEPS_TAC EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `r:num->int32` (concl th) &&
        not(free_in `mld_fqscale` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    X86_STEPS_TAC EXEC (1--14) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PWACC_MONTRED_LANE; GSYM mld_fqscale]) THEN
    X86_STEPS_TAC EXEC (15--16) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
    PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The exit ***)

    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SCALE_EVENTS =
  new_specification ["mldsa_invntt_gcc12_O2_scale_events"]
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SCALE_FULL;;

(* ------------------------------------------------------------------------- *)
(* The whole code: the 11 instructions that save the registers and set up    *)
(* the first layer, then each layer from 8 down to 1, by the lemma for it,   *)
(* each followed by the 3 instructions that test whether there is another    *)
(* layer, then the scaling by its lemma, and the 7 instructions that restore *)
(* the registers and return. The simulation goes through each lemma at once  *)
(* (EVENTS_BIGSTEP_TAC), keeping what the lemma does not change, in          *)
(* particular the saved registers and the return address on the stack.       *)
(* ------------------------------------------------------------------------- *)

(*** The bytes of the table in the image ***)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_ZETAS =
  IMAGE_DATA_RULE_FOR mldsa_native_libmldsa_gcc12_O2_mc mld_zetas_data
    (layout "rodata_mld_zetas");;

(*** Go through the lemma for layer m at step n, with rz the lowest 8 ***)
(*** bytes of the stack frame and the coefficients after 8 - m layers ***)

let INVNTT_LAYER_SIM_TAC m n =
  let th = el (m - 1) MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_LAYER_EVENTS
  and r = if m = 8 then `x:num->int32` else
          mk_comb(mk_comb(`mld_invntt_layers`,mk_small_numeral(8 - m)),
                  `x:num->int32`)
  and sth = CONV_RULE NUM_REDUCE_CONV
   (REWRITE_RULE[ADD1; CONJUNCT1 mld_invntt_layers]
     (INST [mk_small_numeral(8 - m),`n:num`]
           (SPEC_ALL (CONJUNCT2 mld_invntt_layers)))) in
  EVENTS_BIGSTEP_TAC MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC th
   [`a:int64`; `pc:num`; `word(pc + rodata_mld_zetas):int64`;
    `stackpointer:int64`; r] n THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM sth]);;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC in
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES; mld_poly_invntt_tomont;
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
    MATCH_MP MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_ZETAS) THEN

  (*** The saves and the setup, with the address of the table in the ***)
  (*** form of the lemmas for the layers                             ***)

  X86_STEPS_TAC EXEC (1--11) THEN
  FIRST_X_ASSUM(MP_TAC o check
   (can (term_match [] `read R13 s = x`) o concl)) THEN
  REWRITE_TAC[RIPREL_ADDR_LEMMA; GSYM ADD_ASSOC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN DISCH_TAC THEN

  (*** The layers, each with the test whether there is another one ***)

  MAP_EVERY (fun m ->
    let n = 12 + 4 * (8 - m) in
    INVNTT_LAYER_SIM_TAC m n THEN
    X86_STEPS_TAC EXEC ((n+1)--(n+2)) THEN W32_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC EXEC ((n+3)--(n+3)))
   (rev(1--8)) THEN

  (*** The scaling, the restores and the return ***)

  EVENTS_BIGSTEP_TAC EXEC MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SCALE_EVENTS
   [`a:int64`; `pc:num`; `mld_invntt_layers 8 x`] 44 THEN
  X86_STEPS_TAC EXEC (45--51) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EVENTS_APPEND_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

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
