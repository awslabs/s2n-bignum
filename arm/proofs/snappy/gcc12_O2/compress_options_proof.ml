(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/compress_options_spec.ml";;
needs "arm/proofs/bstep.ml";;
needs "common/snappy/snappy_roundtrip.ml";;
needs "arm/proofs/snappy/events_inset.ml";;

(*** Available() is run in place (two instructions, through the vtable     ***)
(*** slot in the relocated data); WorkingMemory(size_t), InternalCompress   ***)
(*** and ~WorkingMemory (OWNED) by their contracts. The block (p, size) of  ***)
(*** WorkingMemory(size_t) is live in the heap (p,size) :: H while          ***)
(*** InternalCompress runs, outside its footprint (heap_props), so          ***)
(*** heap_ok crosses the writes of InternalCompress to it; the destructor   ***)
(*** frees it and the heap is H again (HEAP_REMOVE_CONS).                   ***)

let SNAPPY_CO_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "Compress__Sourcep_Sinkp_CompressionOptions";
    layout_range "ByteArraySource_Available"];;

let SNAPPY_CO_VT_REWRITES =
  map (fun (b,k) ->
    let tm = subst [mk_small_numeral b,`b:num`; mk_small_numeral k,`k:num`;
                    mk_small_numeral (b+k),`bk:num`]
      `word_add (word (pc + b)) (word k):int64 = word_add (word pc) (word bk)` in
    prove(tm, REWRITE_TAC[GSYM WORD_ADD; GSYM ADD_ASSOC] THEN
              CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REFL_TAC))
  [layout "vtable_ByteArraySource",16];;

(* The callee-saved registers that the function saves and restores, and SP, *)
(* are taken out of the frame (as in raw_compress_ctx_proof.ml).           *)

let SNAPPY_CO_PRESERVED_TAC pname ctm =
  MATCH_MP_TAC(ISPEC ctm ENSURES_MAYCHANGE_PRESERVED) THEN
  CONJ_TAC THENL [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV; ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_PRESERVED_KEEP_TAC;
    REWRITE_TAC[GSYM CONJ_ASSOC; GSYM SEQ_ASSOC] THEN
    W(fun (asl,w) -> X_GEN_TAC(mk_var(pname,type_of(fst(dest_forall w)))))];;

(* The contract instances (ARM_BSTEP_CONTRACT_SPECL_TAC, heap_plt.ml) with  *)
(* their frames with one region per clause (MAYCHANGE_CONS_SEQ), so that the *)
(* stack regions of InternalCompress are weakened to the caller's.           *)

let snappy_co_rules = [BITVAL_CLAUSES; MAYCHANGE_CONS_SEQ];;

(* The address of the block of WorkingMemory(size_t), from ~MEM p (MAP FST H) *)

let snappy_co_block asl =
  let th = snd(find (fun (_,th) -> match concl th with
      Comb(Const("~",_),Comb(Comb(Const("MEM",_),_),
           Comb(Comb(Const("MAP",_),Const("FST",_)),Var("H",_)))) -> true
    | _ -> false) asl) in
  lhand(rand(concl th));;

let SNAPPY_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let exec = SNAPPY_CO_EXEC in
  MAP_EVERY X_GEN_TAC
   [`heap_ok:(int64#num)list->(int64->byte)->bool`;
    `heap_fp:(int64#num)list->int64->bool`;
    `heap_room:(int64#num)list->num->bool`; `stk:num`] THEN
  DISCH_THEN(fun model ->
    ASSUME_TAC model THEN
    REWRITE_TAC[C_ARGUMENTS; ALLPAIRS; ALL; PAIRWISE] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SNAPPY_CO_PRESERVED_TAC "x19" `X19` THEN
    SNAPPY_CO_PRESERVED_TAC "x20" `X20` THEN
    SNAPPY_CO_PRESERVED_TAC "x21" `X21` THEN
    SNAPPY_CO_PRESERVED_TAC "x22" `X22` THEN
    SNAPPY_CO_PRESERVED_TAC "x29" `X29` THEN
    MATCH_MP_TAC(ISPECL [`SP`; `stackpointer:int64`]
      ENSURES_MAYCHANGE_EXISTING_PRESERVED) THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV;
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      ENSURES_PRESERVED_KEEP_TAC;
      SIMP_TAC[];
      REWRITE_TAC[GSYM SEQ_ASSOC]] THEN
    SUBGOAL_THEN `val(word(LENGTH(inp:byte list)):int64) = LENGTH inp`
    ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN
      UNDISCH_TAC `LENGTH(inp:byte list) < 2 EXP 32` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `level <= 2` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
      ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`level:num`; `inp:byte list`] SNAPPY_COMPRESS_LENGTH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `DISJOINT (memrange(out:int64,LENGTH(snappy_compress level inp)))
               (heap_fp(H:(int64#num)list))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`out:int64`; `LENGTH(snappy_compress level inp)`;
                      `snappy_max_compressed_length (LENGTH(inp:byte list))`]
               MEMRANGE_PREFIX_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (memrange(out:int64,snappy_max_compressed_length
                     (LENGTH(inp:byte list)))) (heap_fp(H:(int64#num)list))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    (* the own frame outside the footprint, directly: its facts then cross  *)
    (* the frame of ~WorkingMemory (footprint (heap_fp ((p,n)::H)) and the  *)
    (* block) by the same rules as the output's                             *)
    SUBGOAL_THEN
     `DISJOINT (memrange(word_sub (stackpointer:int64) (word 96),96))
               (heap_fp(H:(int64#num)list))`
    ASSUME_TAC THENL
     [W(fun (asl,w) -> set_component_assumptions (map snd asl);
                       ACCEPT_TAC(footprint_disjoint_rule (lhand w) (rand w)));
      ALL_TAC] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_INIT_TAC "s0" THEN
    ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
      ~select:(elf_slots_at [layout "vtable_ByteArraySource" + 16]) THEN
    (* Available(), then WorkingMemory(n) *)
    LABELLED_TAC "steps 1-16"
     (ARM_BSTEP_TAC ~rewrites:SNAPPY_CO_VT_REWRITES exec (1--16)) THEN
    LABELLED_TAC "ctor"
     (ARM_BSTEP_CONTRACT_SPECL_TAC ~rules:snappy_co_rules exec
       (MATCH_MP SNAPPY_WORKING_MEMORY_CTOR_ULONG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
                 model)
       [`read X0 s`; `read X1 s`; `pc:num`; `rw:num`; `H:(int64#num)list`;
        `read SP s`; `read X30 s`; `read X19 s`; `read X20 s`; `read X21 s`;
        `read X29 s`] "s17") THEN
    SNAPPY_OBJECTS_EXPAND_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BITVAL_CLAUSES]) THEN
    W(fun (asl,w) ->
      let p = snappy_co_block asl in
      let blk = mk_pair(p,`snappy_working_memory_size (LENGTH(inp:byte list))`) in
      let h1 = mk_icomb(mk_icomb(`CONS:int64#num->(int64#num)list->(int64#num)list`,
                                 blk),`H:(int64#num)list`) in
      SUBGOAL_THEN (mk_icomb(mk_icomb(`MEM:int64#num->(int64#num)list->bool`,blk),h1))
        ASSUME_TAC THENL [REWRITE_TAC[MEM]; ALL_TAC]) THEN
    HEAP_BLOCK_DISJOINT_TAC model THEN
    W(fun (asl,w) ->
      let p = snappy_co_block asl in
      let blk = mk_pair(p,`snappy_working_memory_size (LENGTH(inp:byte list))`) in
      let h1 = mk_icomb(mk_icomb(`CONS:int64#num->(int64#num)list->(int64#num)list`,
                                 blk),`H:(int64#num)list`) in
      let fr = `memrange(word_sub (stackpointer:int64) (word 96),96)` in
      let t1 = mk_icomb(`heap_fp:(int64#num)list->int64->bool`,h1)
      and t2 = mk_icomb(`memrange:int64#num->int64->bool`,blk) in
      set_component_assumptions (map snd asl);
      LABELLED_TAC "frame disjoint"
       (MAP_EVERY (fun t -> ASSUME_TAC(footprint_disjoint_rule fr t)) [t1; t2])) THEN
    (* InternalCompress *)
    LABELLED_TAC "steps 18-22"
     (ARM_BSTEP_TAC exec (18--22)) THEN
    SUBGOAL_THEN `read X2 s22 = word level` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if lhs(concl th) = `read X2 s22` then
        GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
      REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
                  DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `l <= 2 ==> l < 2 EXP 32 /\ l < 2 EXP 64`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if lhs(concl th) = `read X2 s22` &&
                               not(rand(concl th) = `word level:int64`)
                            then ALL_TAC else NO_TAC) THEN
    W(fun (asl,w) ->
      let p = snappy_co_block asl in
      LABELLED_TAC "InternalCompress"
       (ARM_BSTEP_CONTRACT_SPECL_TAC ~rules:snappy_co_rules exec
         (REWRITE_RULE[snappy_working_memory; BITVAL_CLAUSES]
            SNAPPY_INTERNAL_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT)
         [`level:num`; `inp:byte list`; `src:int64`; `out:int64`;
          `read X0 s`; `read X1 s`; `read X3 s`; p;
          `LENGTH(inp:byte list)`; `T`; `pc:num`; `imp:string->int64`;
          `ea:int64`; `el:num`; `ev:num`; `rw:num`; `read SP s`;
          `read X30 s`] "s23")) THEN
    (* ~WorkingMemory *)
    LABELLED_TAC "steps 24-27"
     (ARM_BSTEP_TAC exec (24--27)) THEN
    W(fun (asl,w) ->
      let p = snappy_co_block asl in
      let blk = mk_pair(p,`snappy_working_memory_size (LENGTH(inp:byte list))`) in
      let h1 = mk_icomb(mk_icomb(`CONS:int64#num->(int64#num)list->(int64#num)list`,
                                 blk),`H:(int64#num)list`) in
      LABELLED_TAC "dtor"
       (ARM_BSTEP_CONTRACT_SPECL_TAC ~rules:snappy_co_rules exec
         (MATCH_MP
            SNAPPY_WORKING_MEMORY_DTOR_OWNED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
            model)
         [`read X0 s`; p;
          `snappy_working_memory_size (LENGTH(inp:byte list))`; `pc:num`;
          `rw:num`; h1; `read SP s`; `read X30 s`] "s28")) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HEAP_REMOVE_CONS]) THEN
    LABELLED_TAC "steps 29-33"
     (ARM_BSTEP_TAC exec (29--33)) THEN
    LABELLED_TAC ~solved:true "final"
     (BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[C_RETURN] THEN
      REWRITE_TAC[WORD_RULE
       `word_add (word_sub (sp:int64) (word 96)) (word 96) = sp`] THEN
      ASM_REWRITE_TAC[])));;

let SNAPPY_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  let exec = SNAPPY_CO_EXEC in
  MAP_EVERY X_GEN_TAC
   [`heap_ok:(int64#num)list->(int64->byte)->bool`;
    `heap_fp:(int64#num)list->int64->bool`;
    `heap_room:(int64#num)list->num->bool`; `stk:num`] THEN
  DISCH_THEN(fun model ->
    ASSUME_TAC model THEN
    REWRITE_TAC[C_ARGUMENTS; ALLPAIRS; ALL; PAIRWISE] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SNAPPY_CO_PRESERVED_TAC "x19" `X19` THEN
    SNAPPY_CO_PRESERVED_TAC "x20" `X20` THEN
    SNAPPY_CO_PRESERVED_TAC "x21" `X21` THEN
    SNAPPY_CO_PRESERVED_TAC "x22" `X22` THEN
    SNAPPY_CO_PRESERVED_TAC "x29" `X29` THEN
    MATCH_MP_TAC(ISPECL [`SP`; `stackpointer:int64`]
      ENSURES_MAYCHANGE_EXISTING_PRESERVED) THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV;
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      ENSURES_PRESERVED_KEEP_TAC;
      SIMP_TAC[];
      REWRITE_TAC[GSYM SEQ_ASSOC]] THEN
    SUBGOAL_THEN `val(word(LENGTH(inp:byte list)):int64) = LENGTH inp`
    ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN
      UNDISCH_TAC `LENGTH(inp:byte list) < 2 EXP 32` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `level <= 2` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
      ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`level:num`; `inp:byte list`] SNAPPY_COMPRESS_LENGTH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `DISJOINT (memrange(out:int64,LENGTH(snappy_compress level inp)))
               (heap_fp(H:(int64#num)list))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`out:int64`; `LENGTH(snappy_compress level inp)`;
                      `snappy_max_compressed_length (LENGTH(inp:byte list))`]
               MEMRANGE_PREFIX_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (memrange(out:int64,snappy_max_compressed_length
                     (LENGTH(inp:byte list)))) (heap_fp(H:(int64#num)list))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    (* the own frame outside the footprint, directly: its facts then cross  *)
    (* the frame of ~WorkingMemory (footprint (heap_fp ((p,n)::H)) and the  *)
    (* block) by the same rules as the output's                             *)
    SUBGOAL_THEN
     `DISJOINT (memrange(word_sub (stackpointer:int64) (word 96),96))
               (heap_fp(H:(int64#num)list))`
    ASSUME_TAC THENL
     [W(fun (asl,w) -> set_component_assumptions (map snd asl);
                       ACCEPT_TAC(footprint_disjoint_rule (lhand w) (rand w)));
      ALL_TAC] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_INIT_TAC "s0" THEN
    ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
      ~select:(elf_slots_at [layout "vtable_ByteArraySource" + 16]) THEN
    (* Available(), then WorkingMemory(n) *)
    LABELLED_TAC "steps 1-16"
     (ARM_BSTEP_TAC ~rewrites:SNAPPY_CO_VT_REWRITES exec (1--16)) THEN
    LABELLED_TAC "ctor"
     (ARM_BSTEP_CONTRACT_SPECL_TAC ~rules:snappy_co_rules exec
       (MATCH_MP SNAPPY_WORKING_MEMORY_CTOR_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE
                 model)
       [`read events s`; `read X0 s`; `read X1 s`; `pc:num`; `rw:num`; `H:(int64#num)list`;
        `read SP s`; `read X30 s`; `read X19 s`; `read X20 s`; `read X21 s`;
        `read X29 s`] "s17") THEN
    SNAPPY_OBJECTS_EXPAND_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BITVAL_CLAUSES]) THEN
    W(fun (asl,w) ->
      let p = snappy_co_block asl in
      let blk = mk_pair(p,`snappy_working_memory_size (LENGTH(inp:byte list))`) in
      let h1 = mk_icomb(mk_icomb(`CONS:int64#num->(int64#num)list->(int64#num)list`,
                                 blk),`H:(int64#num)list`) in
      SUBGOAL_THEN (mk_icomb(mk_icomb(`MEM:int64#num->(int64#num)list->bool`,blk),h1))
        ASSUME_TAC THENL [REWRITE_TAC[MEM]; ALL_TAC]) THEN
    HEAP_BLOCK_DISJOINT_TAC model THEN
    W(fun (asl,w) ->
      let p = snappy_co_block asl in
      let blk = mk_pair(p,`snappy_working_memory_size (LENGTH(inp:byte list))`) in
      let h1 = mk_icomb(mk_icomb(`CONS:int64#num->(int64#num)list->(int64#num)list`,
                                 blk),`H:(int64#num)list`) in
      let fr = `memrange(word_sub (stackpointer:int64) (word 96),96)` in
      let t1 = mk_icomb(`heap_fp:(int64#num)list->int64->bool`,h1)
      and t2 = mk_icomb(`memrange:int64#num->int64->bool`,blk) in
      set_component_assumptions (map snd asl);
      LABELLED_TAC "frame disjoint"
       (MAP_EVERY (fun t -> ASSUME_TAC(footprint_disjoint_rule fr t)) [t1; t2])) THEN
    (* InternalCompress *)
    LABELLED_TAC "steps 18-22"
     (ARM_BSTEP_TAC exec (18--22)) THEN
    SUBGOAL_THEN `read X2 s22 = word level` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if lhs(concl th) = `read X2 s22` then
        GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
      REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
                  DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `l <= 2 ==> l < 2 EXP 32 /\ l < 2 EXP 64`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if lhs(concl th) = `read X2 s22` &&
                               not(rand(concl th) = `word level:int64`)
                            then ALL_TAC else NO_TAC) THEN
    W(fun (asl,w) ->
      let p = snappy_co_block asl in
      LABELLED_TAC "InternalCompress"
       (ARM_BSTEP_CONTRACT_SPECL_TAC ~rules:snappy_co_rules exec
         (REWRITE_RULE[snappy_working_memory; BITVAL_CLAUSES]
            SNAPPY_INTERNAL_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE)
         [`read events s`; `level:num`; `inp:byte list`; `src:int64`; `out:int64`;
          `read X0 s`; `read X1 s`; `read X3 s`; p;
          `LENGTH(inp:byte list)`; `T`; `pc:num`; `imp:string->int64`;
          `ea:int64`; `el:num`; `ev:num`; `rw:num`; `read SP s`;
          `read X30 s`] "s23")) THEN
    (* ~WorkingMemory *)
    LABELLED_TAC "steps 24-27"
     (ARM_BSTEP_TAC exec (24--27)) THEN
    W(fun (asl,w) ->
      let p = snappy_co_block asl in
      let blk = mk_pair(p,`snappy_working_memory_size (LENGTH(inp:byte list))`) in
      let h1 = mk_icomb(mk_icomb(`CONS:int64#num->(int64#num)list->(int64#num)list`,
                                 blk),`H:(int64#num)list`) in
      LABELLED_TAC "dtor"
       (ARM_BSTEP_CONTRACT_SPECL_TAC ~rules:snappy_co_rules exec
         (MATCH_MP
            SNAPPY_WORKING_MEMORY_DTOR_OWNED_GCC12_O2_IMAGE_SUBROUTINE_SAFE
            model)
         [`read events s`; `read X0 s`; p;
          `snappy_working_memory_size (LENGTH(inp:byte list))`; `pc:num`;
          `rw:num`; h1; `read SP s`; `read X30 s`] "s28")) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HEAP_REMOVE_CONS]) THEN
    LABELLED_TAC "steps 29-33"
     (ARM_BSTEP_TAC exec (29--33)) THEN
    LABELLED_TAC ~solved:true "final"
     (BSTEP_FINAL_TAC THEN SNAPPY_INSET_FIRST_TAC THEN ASM_REWRITE_TAC[C_RETURN] THEN
      REWRITE_TAC[WORD_RULE
       `word_add (word_sub (sp:int64) (word 96)) (word 96) = sp`] THEN
      ASM_REWRITE_TAC[])));;
