(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/raw_compress_options_spec.ml";;
needs "arm/proofs/bstep.ml";;
needs "common/snappy/snappy_roundtrip.ml";;
needs "arm/proofs/snappy/events_inset.ml";;

(*** As raw_compress_ctx_proof.ml: the prologue builds the                  ***)
(*** UncheckedByteArraySink at sp - 40 and the ByteArraySource at sp - 24,  ***)
(*** with the vptrs from the RELATIVE slots of their vtables; then Compress ***)
(*** by its contract (compress_options_spec.ml, the heap is H again after   ***)
(*** it); then the length dest - compressed is stored, and the two          ***)
(*** destructors (in the image) store their vptrs again and return.         ***)

let SNAPPY_RCO_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "RawCompress__charp_ulong_charp_ulongp_CompressionOptions";
    layout_range "UncheckedByteArraySink_dtor"; layout_range "Sink_dtor";
    layout_range "ByteArraySource_dtor"; layout_range "Source_dtor"];;

let SNAPPY_RCO_VPTR = prove
 (`!pc a. word_add (word(pc + a)) (word 16):int64 = word(pc + (a + 16))`,
  REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC]);;

let SNAPPY_RCO_PRESERVED_TAC pname ctm =
  MATCH_MP_TAC(ISPEC ctm ENSURES_MAYCHANGE_PRESERVED) THEN
  CONJ_TAC THENL [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV; ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_PRESERVED_KEEP_TAC;
    REWRITE_TAC[GSYM CONJ_ASSOC; GSYM SEQ_ASSOC] THEN
    W(fun (asl,w) -> X_GEN_TAC(mk_var(pname,type_of(fst(dest_forall w)))))];;

let SNAPPY_RAW_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_RAW_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let exec = SNAPPY_RCO_EXEC in
  MAP_EVERY X_GEN_TAC
   [`heap_ok:(int64#num)list->(int64->byte)->bool`;
    `heap_fp:(int64#num)list->int64->bool`;
    `heap_room:(int64#num)list->num->bool`; `stk:num`] THEN
  DISCH_THEN(fun model ->
    ASSUME_TAC model THEN
    REWRITE_TAC[C_ARGUMENTS; ALLPAIRS; ALL; PAIRWISE] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SNAPPY_RCO_PRESERVED_TAC "x19" `X19` THEN
    SNAPPY_RCO_PRESERVED_TAC "x20" `X20` THEN
    SNAPPY_RCO_PRESERVED_TAC "x21" `X21` THEN
    SNAPPY_RCO_PRESERVED_TAC "x22" `X22` THEN
    SNAPPY_RCO_PRESERVED_TAC "x29" `X29` THEN
    MATCH_MP_TAC(ISPECL [`SP`; `stackpointer:int64`]
      ENSURES_MAYCHANGE_EXISTING_PRESERVED) THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV;
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      ENSURES_PRESERVED_KEEP_TAC;
      SIMP_TAC[];
      REWRITE_TAC[GSYM SEQ_ASSOC]] THEN
    SUBGOAL_THEN `level <= 2` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
      ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`level:num`; `inp:byte list`] SNAPPY_COMPRESS_LENGTH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_INIT_TAC "s0" THEN
    ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
      ~select:(elf_slots_at [layout "got_ztv_ByteArraySource";
                             layout "got_ztv_UncheckedByteArraySink"]) THEN
    LABELLED_TAC "steps 1-23"
     (ARM_BSTEP_TAC exec (1--23)) THEN
    RULE_ASSUM_TAC(fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
          Comb(Comb(Const(":>",_),Const("memory",_)),
               Comb(Const("bytes64",_),_))),_)),
             Comb(Comb(Const("word_add",_),_),_)) ->
          CONV_RULE(RAND_CONV(TRY_CONV(REWR_CONV SNAPPY_RCO_VPTR) THENC
                              NUM_REDUCE_CONV)) th
      | _ -> th) THEN
    SUBGOAL_THEN `read X2 s23 = word level` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if lhs(concl th) = `read X2 s23` then
        GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
      REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
                  DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `l <= 2 ==> l < 2 EXP 32 /\ l < 2 EXP 64`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if lhs(concl th) = `read X2 s23` &&
                               not(rand(concl th) = `word level:int64`)
                            then ALL_TAC else NO_TAC) THEN
    LABELLED_TAC "Compress"
     (ARM_BSTEP_CONTRACT_SPECL_TAC exec
       (MATCH_MP SNAPPY_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT model)
       [`level:num`; `inp:byte list`; `src:int64`; `out:int64`;
        `read X0 s`; `read X1 s`; `H:(int64#num)list`; `pc:num`;
        `ea:int64`; `el:num`; `ev:num`; `rw:num`; `read SP s`;
        `read X30 s`] "s24") THEN
    RULE_ASSUM_TAC(fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),
          Const("memory",_)),Comb(Const("bytelist",_),Comb(Comb(Const(",",_),
          Var("out",_)),_)))),_)),_) ->
          let th' = REWRITE_RULE[READ_BYTELIST_EQ_BYTES] th in
          if is_conj(concl th') then CONJUNCT2 th' else th'
      | _ -> th) THEN
    LABELLED_TAC "steps 25-47"
     (ARM_BSTEP_TAC exec (25--47)) THEN
    LABELLED_TAC ~solved:true "final"
     (BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN
      REWRITE_TAC[WORD_RULE `word_sub (word_add a b) a = b`] THEN
      REWRITE_TAC[WORD_RULE
       `word_add (word_sub (sp:int64) (word 96)) (word 96) = sp`] THEN
      ASM_REWRITE_TAC[])));;

let SNAPPY_RAW_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_RAW_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  let exec = SNAPPY_RCO_EXEC in
  MAP_EVERY X_GEN_TAC
   [`heap_ok:(int64#num)list->(int64->byte)->bool`;
    `heap_fp:(int64#num)list->int64->bool`;
    `heap_room:(int64#num)list->num->bool`; `stk:num`] THEN
  DISCH_THEN(fun model ->
    ASSUME_TAC model THEN
    REWRITE_TAC[C_ARGUMENTS; ALLPAIRS; ALL; PAIRWISE] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SNAPPY_RCO_PRESERVED_TAC "x19" `X19` THEN
    SNAPPY_RCO_PRESERVED_TAC "x20" `X20` THEN
    SNAPPY_RCO_PRESERVED_TAC "x21" `X21` THEN
    SNAPPY_RCO_PRESERVED_TAC "x22" `X22` THEN
    SNAPPY_RCO_PRESERVED_TAC "x29" `X29` THEN
    MATCH_MP_TAC(ISPECL [`SP`; `stackpointer:int64`]
      ENSURES_MAYCHANGE_EXISTING_PRESERVED) THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV;
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      ENSURES_PRESERVED_KEEP_TAC;
      SIMP_TAC[];
      REWRITE_TAC[GSYM SEQ_ASSOC]] THEN
    SUBGOAL_THEN `level <= 2` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
      ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`level:num`; `inp:byte list`] SNAPPY_COMPRESS_LENGTH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_INIT_TAC "s0" THEN
    ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
      ~select:(elf_slots_at [layout "got_ztv_ByteArraySource";
                             layout "got_ztv_UncheckedByteArraySink"]) THEN
    LABELLED_TAC "steps 1-23"
     (ARM_BSTEP_TAC exec (1--23)) THEN
    RULE_ASSUM_TAC(fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
          Comb(Comb(Const(":>",_),Const("memory",_)),
               Comb(Const("bytes64",_),_))),_)),
             Comb(Comb(Const("word_add",_),_),_)) ->
          CONV_RULE(RAND_CONV(TRY_CONV(REWR_CONV SNAPPY_RCO_VPTR) THENC
                              NUM_REDUCE_CONV)) th
      | _ -> th) THEN
    SUBGOAL_THEN `read X2 s23 = word level` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if lhs(concl th) = `read X2 s23` then
        GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
      REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
                  DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `l <= 2 ==> l < 2 EXP 32 /\ l < 2 EXP 64`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if lhs(concl th) = `read X2 s23` &&
                               not(rand(concl th) = `word level:int64`)
                            then ALL_TAC else NO_TAC) THEN
    LABELLED_TAC "Compress"
     (ARM_BSTEP_CONTRACT_SPECL_TAC exec
       (MATCH_MP SNAPPY_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_SAFE model)
       [`read events s`; `level:num`; `inp:byte list`; `src:int64`; `out:int64`;
        `read X0 s`; `read X1 s`; `H:(int64#num)list`; `pc:num`;
        `ea:int64`; `el:num`; `ev:num`; `rw:num`; `read SP s`;
        `read X30 s`] "s24") THEN
    RULE_ASSUM_TAC(fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),
          Const("memory",_)),Comb(Const("bytelist",_),Comb(Comb(Const(",",_),
          Var("out",_)),_)))),_)),_) ->
          let th' = REWRITE_RULE[READ_BYTELIST_EQ_BYTES] th in
          if is_conj(concl th') then CONJUNCT2 th' else th'
      | _ -> th) THEN
    LABELLED_TAC "steps 25-47"
     (ARM_BSTEP_TAC exec (25--47)) THEN
    LABELLED_TAC ~solved:true "final"
     (BSTEP_FINAL_TAC THEN SNAPPY_INSET_FIRST_TAC THEN
      ASM_REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN
      REWRITE_TAC[WORD_RULE `word_sub (word_add a b) a = b`] THEN
      REWRITE_TAC[WORD_RULE
       `word_add (word_sub (sp:int64) (word 96)) (word 96) = sp`] THEN
      ASM_REWRITE_TAC[])));;
