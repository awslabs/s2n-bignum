(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/raw_compress_ctx_spec.ml";;
needs "arm/proofs/bstep.ml";;
needs "arm/proofs/snappy/events_inset.ml";;

(*** The prologue builds the UncheckedByteArraySink at sp - 40 (vptr, dest) ***)
(*** and the ByteArraySource at sp - 24 (vptr, pointer, length), with the   ***)
(*** vptrs from the RELATIVE slots of their vtables; then Compress(ctx) by ***)
(*** its contract; then the length dest - compressed is stored, and the    ***)
(*** two destructors (in the image) store their vptrs again and return.    ***)

let SNAPPY_RAW_COMPRESS_CTX_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "RawCompress__charp_ulong_charp_ulongp_CompressionOptions_CompressionContextp";
    layout_range "UncheckedByteArraySink_dtor"; layout_range "Sink_dtor";
    layout_range "ByteArraySource_dtor"; layout_range "Source_dtor"];;

let SNAPPY_RCC_VPTR = prove
 (`!pc a. word_add (word(pc + a)) (word 16):int64 = word(pc + (a + 16))`,
  REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC]);;

(* The callee-saved registers that the function saves and restores, and SP, *)
(* are taken out of the frame (as in compress_fragment_proof.ml).          *)

let SNAPPY_RCC_PRESERVED_TAC pname ctm =
  MATCH_MP_TAC(ISPEC ctm ENSURES_MAYCHANGE_PRESERVED) THEN
  CONJ_TAC THENL [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV; ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_PRESERVED_KEEP_TAC;
    REWRITE_TAC[GSYM CONJ_ASSOC; GSYM SEQ_ASSOC] THEN
    W(fun (asl,w) -> X_GEN_TAC(mk_var(pname,type_of(fst(dest_forall w)))))];;

let SNAPPY_RCC_START_TAC =
  REWRITE_TAC[C_ARGUMENTS; ALLPAIRS; ALL; PAIRWISE] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SNAPPY_RCC_PRESERVED_TAC "x19" `X19` THEN
  SNAPPY_RCC_PRESERVED_TAC "x20" `X20` THEN
  SNAPPY_RCC_PRESERVED_TAC "x21" `X21` THEN
  SNAPPY_RCC_PRESERVED_TAC "x22" `X22` THEN
  SNAPPY_RCC_PRESERVED_TAC "x29" `X29` THEN
  MATCH_MP_TAC(ISPECL [`SP`; `stackpointer:int64`]
    ENSURES_MAYCHANGE_EXISTING_PRESERVED) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV;
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_PRESERVED_KEEP_TAC;
    SIMP_TAC[];
    REWRITE_TAC[GSYM SEQ_ASSOC]] THEN
  REWRITE_TAC[snappy_compression_context; snappy_working_memory] THEN
  ENSURES_INIT_TAC "s0" THEN
  ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
    ~select:(elf_slots_at [layout "got_ztv_ByteArraySource";
                           layout "got_ztv_UncheckedByteArraySink"]) THEN
  ARM_BSTEP_TAC SNAPPY_RAW_COMPRESS_CTX_GCC12_O2_EXEC (1--24) THEN
  RULE_ASSUM_TAC(fun th -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
        Comb(Comb(Const(":>",_),Const("memory",_)),
             Comb(Const("bytes64",_),_))),_)),
           Comb(Comb(Const("word_add",_),_),_)) ->
        CONV_RULE(RAND_CONV(TRY_CONV(REWR_CONV SNAPPY_RCC_VPTR) THENC
                            NUM_REDUCE_CONV)) th
    | _ -> th);;

(* The stack addresses of the callee's regions, from the caller's SP.       *)

let SNAPPY_RCC_SP_THMS = map (fun t -> WORD_RULE t)
 [`word_add (word_sub (sp:int64) (word 96)) (word 72) = word_sub sp (word 24)`;
  `word_add (word_sub (sp:int64) (word 96)) (word 56) = word_sub sp (word 40)`;
  `word_sub (word_sub (sp:int64) (word 96)) (word 160) = word_sub sp (word 256)`;
  `word_sub (word_sub (sp:int64) (word 96)) (word 208) = word_sub sp (word 304)`];;

let SNAPPY_RCC_LEVEL_TAC =
  SUBGOAL_THEN `level <= 2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `read X2 s24 = word level` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if lhs(concl th) = `read X2 s24` then
      GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
                DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `l <= 2 ==> l < 2 EXP 32 /\ l < 2 EXP 64`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if lhs(concl th) = `read X2 s24` &&
                             not(rand(concl th) = `word level:int64`)
                          then ALL_TAC else NO_TAC);;

let SNAPPY_RCC_CALL_GEN_TAC (safe:bool) =
  W(fun (asl,w) ->
    let sp' = `word_sub stackpointer (word 96):int64` in
    let so = `word_add (word_sub stackpointer (word 96)) (word 72):int64`
    and sk = `word_add (word_sub stackpointer (word 96)) (word 56):int64` in
    let args = [`level:num`; `inp:byte list`; `src:int64`; `out:int64`;
                     so; sk; `cc:int64`; `wm:int64`; `owc:bool`; `mem:int64`;
                     `nw:num`; `owns:bool`; `pc:num`; `imp:string->int64`;
                     `ea:int64`; `el:num`; `ev:num`; `rw:num`; sp';
                     `word (pc + 19664):int64`] in
    let ev = `ev_call:uarch_event list` in
    let th0 =
      if safe then SPECL (ev :: args)
                     SNAPPY_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_SAFE
      else SPECL args SNAPPY_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_CORRECT in
    let th1 = CONV_RULE NUM_REDUCE_CONV
               (REWRITE_RULE[C_ARGUMENTS; ALLPAIRS; ALL; PAIRWISE;
                             snappy_compression_context; snappy_working_memory;
                             GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] th0) in
    let th1 = if safe then INST [snappy_current_events (asl,w),ev] th1 else th1 in
    let ant = lhand(concl th1) in
    let ath = TAC_PROOF((asl,ant),
      REPEAT CONJ_TAC THEN
      FIRST [FIRST_ASSUM ACCEPT_TAC;
             W(fun (asl,_) -> CONV_TAC(ALIGNED_WORD_CONV (map snd asl))) THEN
             NO_TAC;
             RULE_ASSUM_TAC(REWRITE_RULE SNAPPY_RCC_SP_THMS) THEN
             REWRITE_TAC SNAPPY_RCC_SP_THMS THEN NONOVERLAPPING_TAC THEN NO_TAC;
             ASM_ARITH_TAC]) in
    ARM_BSTEP_CALL_TAC SNAPPY_RAW_COMPRESS_CTX_GCC12_O2_EXEC (MP th1 ath) "s25");;

let SNAPPY_RCC_CALL_TAC = SNAPPY_RCC_CALL_GEN_TAC false;;

let SNAPPY_RAW_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_RAW_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  SNAPPY_RCC_START_TAC THEN SNAPPY_RCC_LEVEL_TAC THEN SNAPPY_RCC_CALL_TAC THEN
  RULE_ASSUM_TAC(fun th -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),
        Const("memory",_)),Comb(Const("bytelist",_),Comb(Comb(Const(",",_),
        Var("out",_)),_)))),_)),_) ->
        let th' = REWRITE_RULE[READ_BYTELIST_EQ_BYTES] th in
        if is_conj(concl th') then CONJUNCT2 th' else th'
    | _ -> th) THEN
  MP_TAC(SPECL [`level:num`; `inp:byte list`] SNAPPY_COMPRESS_LENGTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ARM_BSTEP_TAC SNAPPY_RAW_COMPRESS_CTX_GCC12_O2_EXEC (26--48) THEN
  BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add a b) a = b`] THEN
  REWRITE_TAC[WORD_RULE `word_add (word_sub (sp:int64) (word 96)) (word 96) = sp`] THEN
  ASM_REWRITE_TAC[]);;

let SNAPPY_RAW_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_RAW_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SNAPPY_RCC_START_TAC THEN SNAPPY_RCC_LEVEL_TAC THEN SNAPPY_RCC_CALL_GEN_TAC true THEN
  RULE_ASSUM_TAC(fun th -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),
        Const("memory",_)),Comb(Const("bytelist",_),Comb(Comb(Const(",",_),
        Var("out",_)),_)))),_)),_) ->
        let th' = REWRITE_RULE[READ_BYTELIST_EQ_BYTES] th in
        if is_conj(concl th') then CONJUNCT2 th' else th'
    | _ -> th) THEN
  MP_TAC(SPECL [`level:num`; `inp:byte list`] SNAPPY_COMPRESS_LENGTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ARM_BSTEP_TAC SNAPPY_RAW_COMPRESS_CTX_GCC12_O2_EXEC (26--48) THEN
  BSTEP_FINAL_TAC THEN SNAPPY_INSET_FIRST_TAC THEN ASM_REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add a b) a = b`] THEN
  REWRITE_TAC[WORD_RULE `word_add (word_sub (sp:int64) (word 96)) (word 96) = sp`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence the round trip and the bound: the output decodes to the input and   *)
(* fits in snappy_max_compressed_length n bytes.                             *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_RAW_COMPRESS_CTX_OUTPUT = prove
 (`!level inp. (level = 1 \/ level = 2) /\ LENGTH inp < 2 EXP 32
       ==> snappy_decode (snappy_compress level inp) = SOME inp /\
           LENGTH(snappy_compress level inp)
           <= snappy_max_compressed_length (LENGTH inp)`,
  MESON_TAC[SNAPPY_COMPRESS_ROUNDTRIP; SNAPPY_COMPRESS_LENGTH]);;
