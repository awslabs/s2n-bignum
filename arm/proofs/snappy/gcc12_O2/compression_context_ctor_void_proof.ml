(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/compression_context_ctor_void_spec.ml";;

(*** new(48) for the object, then WorkingMemory(65536) on it with the heap  ***)
(*** (wm,48) :: H, whose room is the hypothesis for the address wm; the    ***)
(*** block of the second allocation is the value that the constructor      ***)
(*** stores at mem_.                                                        ***)

let SNAPPY_COMPRESSION_CONTEXT_CTOR_VOID_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_COMPRESSION_CONTEXT_CTOR_VOID_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  let exec = SNAPPY_COMPRESSION_CONTEXT_CTOR_VOID_GCC12_O2_EXEC in
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; ALL] THEN
  MAP_EVERY X_GEN_TAC
   [`heap_ok:(int64#num)list->(int64->byte)->bool`;
    `heap_fp:(int64#num)list->int64->bool`;
    `heap_room:(int64#num)list->num->bool`; `stk:num`] THEN
  DISCH_THEN(fun model ->
    ASSUME_TAC model THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
      ~select:(elf_slots_importing ["_Znwm"]) THEN
    (* the object *)
    ARM_BSTEP_TAC exec (1--6) THEN
    ARM_BSTEP_PLT_HEAP_NEW_TAC exec model "wm" "s7" THEN
    FIRST_X_ASSUM(ASSUME_TAC o SPEC `wm:int64` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t ->
                         t = `heap_room:(int64#num)list->num->bool`))
                           (concl th))) THEN
    (* its memory *)
    ARM_BSTEP_TAC exec (8--10) THEN
    ARM_BSTEP_CONTRACT_TAC exec
      (MATCH_MP SNAPPY_WORKING_MEMORY_CTOR_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE
                model)
      [`read events s`; `read X0 s`; `read X1 s`; `pc:num`; `rw:num`;
       `CONS (wm:int64,48) H`; `read SP s`; `read X30 s`; `read X19 s`;
       `read X20 s`; `read X21 s`; `read X29 s`] "s11" THEN
    SNAPPY_OBJECTS_EXPAND_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAP; MEM; FST; DE_MORGAN_THM]) THEN
    (* the context *)
    ARM_BSTEP_TAC exec (12--17) THEN
    BSTEP_FINAL_TAC THEN
    ASM_REWRITE_TAC[snappy_compression_context; BITVAL_CLAUSES] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    EXISTS_TAC `wm:int64` THEN
    W(fun (asl,w) ->
      let c = `memory :> bytes64 wm` in
      EXISTS_TAC(rand(concl(snd(find (fun (_,th) ->
        match concl th with
          Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c'),_)),_) ->
            compare c' c = 0
        | _ -> false) asl))))) THEN
    ASM_REWRITE_TAC[snappy_working_memory; BITVAL_CLAUSES] THEN
    REPEAT CONJ_TAC THEN
    FIRST [MEMACCESS_INSET_TAC; FIRST_ASSUM(ACCEPT_TAC o GSYM);
           FOOTPRINT_SUBSET_TAC]));;

let SNAPPY_COMPRESSION_CONTEXT_CTOR_VOID_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_COMPRESSION_CONTEXT_CTOR_VOID_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  ENSURES_DROP_EVENTS_TAC SNAPPY_COMPRESSION_CONTEXT_CTOR_VOID_GCC12_O2_IMAGE_SUBROUTINE_SAFE);;
