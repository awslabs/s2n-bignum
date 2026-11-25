(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/raw_uncompress_charp_ulong_charp_spec.ml";;
needs "arm/proofs/snappy/array_writer.ml";;

(*** The code: the vptr from the RELATIVE slot got_ztv_ByteArraySource    ***)
(*** (+ 16), the ByteArraySource at sp + 40, the call of                  ***)
(*** RawUncompress(Source* r, char* o) (its contract specialized by the   ***)
(*** case of snappy_decode l, so that the output is a plain fact that     ***)
(*** crosses the rest), ~ByteArraySource (stores the vptr, tail call of   ***)
(*** ~Source, a ret).                                                     ***)

let SNAPPY_RAW_UNCOMPRESS_CHARP_CALL_TAC exec dth =
  W(fun (asl,w) ->
    let s = rand w in
    let ev t = arm_bstep_eval asl s t in
    let args = [ev `read events s`; ev `read X0 s`; `inp:int64`; `l:byte list`;
                ev `read X1 s`; `outlen:num`; `pc:num`; `rw:num`;
                ev `read SP s`; ev `read X30 s`;
                ev `read X19 s`; ev `read X20 s`; ev `read X21 s`;
                ev `read X22 s`; ev `read X23 s`; ev `read X24 s`;
                ev `read X25 s`; ev `read X26 s`; ev `read X27 s`;
                ev `read X28 s`; ev `read X29 s`;
                `ea:int64`; `el:num`; `ev:num`] in
    let cth = CONV_RULE(DEPTH_CONV WORD_ADD_ADD_NUM_CONV)
                (REWRITE_RULE[dth; option_DISTINCT; option_INJ;
                              FORALL_UNWIND_THM1; FORALL_UNWIND_THM2;
                              BITVAL_CLAUSES]
                   (SPECL args
                     SNAPPY_RAW_UNCOMPRESS_SOURCEP_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE)) in
    ARM_BSTEP_CONTRACT_TAC exec cth [] "s14");;

let SNAPPY_RAW_UNCOMPRESS_CHARP_CASE_TAC dth =
  let exec = SNAPPY_RAW_UNCOMPRESS_CHARP_ULONG_CHARP_GCC12_O2_EXEC in
  ENSURES_INIT_TAC "s0" THEN
  ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
    ~select:(elf_slots_at [0x1ffd8]) THEN
  ARM_BSTEP_TAC exec (1--13) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word (pc + 130160)) (word 16):int64 =
     word_add (word pc) (word 130176)`]) THEN
  SNAPPY_RAW_UNCOMPRESS_CHARP_CALL_TAC exec dth THEN
  ARM_BSTEP_TAC exec (15--28) THEN
  BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_RULE `word_add (word_sub sp (word 64)) (word 64):int64 = sp`] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  MEMACCESS_INSET_TAC;;

let SNAPPY_RAW_UNCOMPRESS_CHARP_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_RAW_UNCOMPRESS_CHARP_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n:int64 = word(LENGTH(l:byte list))` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `val(n:int64) = LENGTH(l:byte list)`)) THEN
    REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC(ISPEC `snappy_decode (l:byte list)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC `x:byte list`)) THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ; FORALL_UNWIND_THM1;
                  FORALL_UNWIND_THM2; BITVAL_CLAUSES] THENL
   [SNAPPY_RAW_UNCOMPRESS_CHARP_CASE_TAC
      (ASSUME `snappy_decode (l:byte list) = NONE`);
    SUBGOAL_THEN `LENGTH(x:byte list) <= outlen` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
      MATCH_MP_TAC SNAPPY_DECODE_HEADER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASSUME_TAC(MATCH_MP NONOVERLAPPING_PREFIX (CONJ
      (ASSUME `nonoverlapping (out:int64,outlen) (word_sub sp (word 640),640)`)
      (ASSUME `LENGTH(x:byte list) <= outlen`))) THEN
    ASSUME_TAC(MATCH_MP NONOVERLAPPING_PREFIX (CONJ
      (ASSUME `nonoverlapping (out:int64,outlen) (word pc,129968 + 1120)`)
      (ASSUME `LENGTH(x:byte list) <= outlen`))) THEN
    SNAPPY_RAW_UNCOMPRESS_CHARP_CASE_TAC
      (ASSUME `snappy_decode (l:byte list) = SOME x`)]);;

let SNAPPY_RAW_UNCOMPRESS_CHARP_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_RAW_UNCOMPRESS_CHARP_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  ENSURES_DROP_EVENTS_TAC
    SNAPPY_RAW_UNCOMPRESS_CHARP_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE);;
