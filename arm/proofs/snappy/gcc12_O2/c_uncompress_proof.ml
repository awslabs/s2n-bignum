(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/c_uncompress_spec.ml";;
needs "arm/proofs/snappy/array_writer.ml";;

(*** Four cases, split before the simulation: the header invalid (status   ***)
(*** 1); valid but above *uncompressed_length (2); valid and the stream    ***)
(*** invalid (1); valid (0). The contracts of the callees are specialized  ***)
(*** by the case, so that their results are plain facts; the branches are  ***)
(*** decided by them (ARM_BSTEP_RUN_GEN_TAC with BSTEP_KILL_TAC). The       ***)
(*** header value is the local at sp + 56, a ghost r0 before the call.     ***)

let SNAPPY_C_UNCOMPRESS_GUL_TAC exec hth i =
  (W(fun (asl,w) ->
    let s = rand w in
    X_CHOOSE_TAC `r0:int64`
      (prove(vsubst [s,`s:armstate`]
        `?r0. read (memory :> bytes64 (word_add (word_sub sp (word 64))
                                                (word 56))) s = r0`,
        MESON_TAC[]))) THEN
   let cth = GENL [`e:(uarch_event)list`; `inp:int64`; `n:int64`; `res:int64`]
     (REWRITE_RULE[hth; option_DISTINCT; option_INJ; FORALL_UNWIND_THM1;
                   FORALL_UNWIND_THM2; BITVAL_CLAUSES]
       (SPECL [`e:(uarch_event)list`; `inp:int64`; `n:int64`; `res:int64`;
               `l:byte list`]
          SNAPPY_GET_UNCOMPRESSED_LENGTH_CHARP_ULONG_ULONGP_GCC12_O2_IMAGE_SUBROUTINE_SAFE)) in
   ARM_BSTEP_CONTRACT_TAC exec cth
    [`read events s`; `read X0 s`; `read X1 s`; `read X2 s`;
     `r0:int64`; `pc:num`; `read X30 s`] ("s" ^ string_of_int i)),1;;

let SNAPPY_C_UNCOMPRESS_RAW_TAC exec dth i =
  let cth = GENL [`e:(uarch_event)list`; `inp:int64`; `n:int64`]
    (REWRITE_RULE[dth; option_DISTINCT; option_INJ; FORALL_UNWIND_THM1;
                  FORALL_UNWIND_THM2; BITVAL_CLAUSES]
      (SPECL [`e:(uarch_event)list`; `inp:int64`; `n:int64`; `l:byte list`]
         SNAPPY_RAW_UNCOMPRESS_CHARP_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE)) in
  ARM_BSTEP_CONTRACT_TAC exec cth
   [`read events s`; `read X0 s`; `read X1 s`; `read X2 s`;
    `val(ulen:int64)`; `pc:num`; `rw:num`; `read SP s`; `read X30 s`;
    `read X19 s`; `read X20 s`; `read X21 s`; `read X22 s`; `read X23 s`;
    `read X24 s`; `read X25 s`; `read X26 s`; `read X27 s`; `read X28 s`;
    `read X29 s`;
    `ea:int64`; `el:num`; `ev:num`] ("s" ^ string_of_int i),1;;

let SNAPPY_C_UNCOMPRESS_LEAF_TAC : tactic =
  BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_RULE `word_add (word_sub sp (word 64)) (word 64):int64 = sp`] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  MEMACCESS_INSET_TAC;;

let SNAPPY_C_UNCOMPRESS_RUN_TAC hth dth =
  let exec = SNAPPY_C_UNCOMPRESS_GCC12_O2_EXEC in
  ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_RUN_GEN_TAC ~kill:BSTEP_KILL_TAC
    ~calls:([`word(pc + 13104):int64`, SNAPPY_C_UNCOMPRESS_GUL_TAC exec hth] @
            (match dth with
               Some d -> [`word(pc + 20852):int64`,
                          SNAPPY_C_UNCOMPRESS_RAW_TAC exec d]
             | None -> []))
    exec 1 SNAPPY_C_UNCOMPRESS_LEAF_TAC;;

let SNAPPY_C_UNCOMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_C_UNCOMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[snappy_uncompress_status] THEN
  MP_TAC(ISPEC `snappy_header (l:byte list)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC `m:num`)) THENL
   [(* the header is invalid *)
    SUBGOAL_THEN `snappy_decode (l:byte list) = NONE` ASSUME_TAC THENL
     [MP_TAC(ISPEC `snappy_decode (l:byte list)` (cases "option")) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP SNAPPY_DECODE_HEADER) THEN
      ASM_REWRITE_TAC[option_DISTINCT];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[snappy_uncompress_status_of; option_DISTINCT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SNAPPY_C_UNCOMPRESS_RUN_TAC
      (ASSUME `snappy_header (l:byte list) = NONE`) None;
    ALL_TAC] THEN
  SUBGOAL_THEN `m < 2 EXP 32` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SNAPPY_HEADER]) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:byte list`
      (ACCEPT_TAC o CONJUNCT1 o MATCH_MP SNAPPY_VARINT_SOME)); ALL_TAC] THEN
  SUBGOAL_THEN `!x. snappy_decode (l:byte list) = SOME x ==> LENGTH x = m`
    ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SNAPPY_DECODE_HEADER) THEN
    ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(ACCEPT_TAC o SYM); ALL_TAC] THEN
  SUBGOAL_THEN `val(word m:int64) = m` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `m < 2 EXP 32` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `val(ulen:int64) < m` THENL
   [(* the buffer is too small *)
    SUBGOAL_THEN
     `!x. (snappy_decode (l:byte list) = SOME x /\
           LENGTH x <= val(ulen:int64)) <=> F`
      (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:byte list` o check (fun th ->
        is_forall(concl th) && is_imp(snd(dest_forall(concl th))) &&
        can (term_match [] `snappy_decode l = SOME x`)
            (lhand(snd(dest_forall(concl th)))))) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`val(ulen:int64) < m`; `LENGTH(x:byte list) <= val(ulen:int64)`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[snappy_uncompress_status_of] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SNAPPY_C_UNCOMPRESS_RUN_TAC
      (ASSUME `snappy_header (l:byte list) = SOME m`) None;
    ALL_TAC] THEN
  SUBGOAL_THEN `!m'. snappy_header (l:byte list) = SOME m' ==> m' <= val(ulen:int64)`
    ASSUME_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `~(val(ulen:int64) < m)` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `snappy_decode (l:byte list)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC `x:byte list`)) THENL
   [(* the stream is invalid *)
    ASM_REWRITE_TAC[snappy_uncompress_status_of; option_DISTINCT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SNAPPY_C_UNCOMPRESS_RUN_TAC
      (ASSUME `snappy_header (l:byte list) = SOME m`)
      (Some (ASSUME `snappy_decode (l:byte list) = NONE`));
    ALL_TAC] THEN
  (* OK *)
  SUBGOAL_THEN `m <= val(ulen:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(val(ulen:int64) < m)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(x:byte list) = m` (SUBST_ALL_TAC o SYM) THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (term_match [] `snappy_decode l = SOME x`)
          (lhand(snd(dest_forall(concl th)))))) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[snappy_uncompress_status_of; option_DISTINCT; option_INJ;
                  IMP_CONJ; FORALL_UNWIND_THM1; FORALL_UNWIND_THM2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  ASSUME_TAC(MATCH_MP NONOVERLAPPING_PREFIX_RIGHT (CONJ
    (ASSUME `nonoverlapping (word_sub sp (word 704),704)
                            (out:int64,val(ulen:int64))`)
    (ASSUME `LENGTH(x:byte list) <= val(ulen:int64)`))) THEN
  ASSUME_TAC(MATCH_MP NONOVERLAPPING_PREFIX (CONJ
    (ASSUME `nonoverlapping (out:int64,val(ulen:int64)) (ulenp,8)`)
    (ASSUME `LENGTH(x:byte list) <= val(ulen:int64)`))) THEN
  SNAPPY_C_UNCOMPRESS_RUN_TAC
    (ASSUME `snappy_header (l:byte list) = SOME (LENGTH(x:byte list))`)
    (Some (ASSUME `snappy_decode (l:byte list) = SOME x`)));;

let SNAPPY_C_UNCOMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_C_UNCOMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  ENSURES_DROP_EVENTS_CONJ_TAC SNAPPY_C_UNCOMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE);;
