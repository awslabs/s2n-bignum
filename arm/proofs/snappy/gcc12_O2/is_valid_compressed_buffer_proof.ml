(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/is_valid_compressed_buffer_spec.ml";;
needs "arm/proofs/heap_plt.ml";;
needs "arm/proofs/snappy/validator_tactics.ml";;

(*** The construction of the source and the validator, the call of        ***)
(*** InternalUncompress<Validator> and the destructor of the source. The   ***)
(*** stack is split into the clauses of the objects written (the saved     ***)
(*** registers at sp - 80, the validator at sp - 48, the vptr at sp - 24,  ***)
(*** ptr_ and left_ at sp - 16; addressed from the SP of the frame as the  ***)
(*** stores are) and the 464 bytes of the callee, so that                   ***)
(*** the saved registers and the vptr cross the call. The vptr as the      ***)
(*** code makes it (the GOT slot of the vtable group plus 16) is rewritten  ***)
(*** to the form of the contract.                                          ***)

let SNAPPY_IS_VALID_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_IS_VALID_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  let exec = SNAPPY_IS_VALID_COMPRESSED_BUFFER_GCC12_O2_EXEC in
  let callee =
    SNAPPY_INTERNAL_UNCOMPRESS_VALIDATOR_GCC12_O2_IMAGE_SUBROUTINE_SAFE in
  let vptr = WORD_RULE
    `word_add (word(pc + 130160)) (word 16):int64 =
     word_add (word pc) (word 130176)` in
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n:int64 = word(LENGTH(l:byte list))` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
  ENSURES_FRAME_SPLIT_TAC
   `MAYCHANGE [memory :> bytes(word_sub sp (word 544),544)]`
   `MAYCHANGE [memory :> bytes(word_sub sp (word 80),32)] ,,
    MAYCHANGE [memory :> bytes(word_add (word_sub sp (word 80)) (word 32),16)] ,,
    MAYCHANGE [memory :> bytes(word_add (word_sub sp (word 80)) (word 56),8)] ,,
    MAYCHANGE [memory :> bytes(word_add (word_sub sp (word 80)) (word 64),16)] ,,
    MAYCHANGE [memory :> bytes(word_sub (word_sub sp (word 80)) (word 464),464)]` THEN
  SUBGOAL_THEN `464 <= val(word_sub sp (word 80):int64)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD_SUB_NOWRAP; ARITH_RULE `544 <= x ==> 80 <= x`;
                 VAL_WORD_NOWRAP; ARITH_RULE `80 < 2 EXP 64`] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `snappy_decode (l:byte list) = NONE` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  ENSURES_INIT_TAC "s0" THEN
  ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
    ~select:(elf_slots_at [0x1ffd8]) THEN
  ARM_BSTEP_TAC ~rewrites:[vptr] exec (1--14) THEN
  W(fun (asl,_) ->
    let hth = snd(find (fun (_,th) ->
      (is_eq(concl th) || is_neg(concl th)) &&
      can (find_term ((=) `snappy_decode (l:byte list)`)) (concl th)) asl) in
    let cth = REWRITE_RULE[hth; BITVAL_CLAUSES] callee in
    let il =
     [`read events s`; `read X0 s`; `read X1 s`; `inp:int64`; `l:byte list`;
      `pc:num`; `rw:num`; `read SP s`; `read X30 s`; `read X19 s`;
      `read X20 s`; `read X21 s`; `read X22 s`; `read X23 s`; `read X24 s`;
      `read X25 s`; `read X26 s`; `read X29 s`; `ea:int64`; `el:num`;
      `ev:num`] in
    VAL_PRE_FACTS_TAC cth il THEN ARM_BSTEP_CONTRACT_TAC exec cth il "s15") THEN
  ARM_BSTEP_TAC ~rewrites:[vptr] exec (16--29) THEN
  BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  MEMACCESS_INSET_TAC);;

let SNAPPY_IS_VALID_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_IS_VALID_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  ENSURES_DROP_EVENTS_TAC
    SNAPPY_IS_VALID_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_SAFE);;
