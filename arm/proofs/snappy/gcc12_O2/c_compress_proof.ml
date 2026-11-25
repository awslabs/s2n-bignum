(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/c_compress_spec.ml";;
needs "arm/proofs/bstep.ml";;
needs "arm/proofs/snappy/decompressor_objects.ml";;
needs "common/snappy/snappy_roundtrip.ml";;
needs "arm/proofs/snappy/events_inset.ml";;

(*** snappy_max_compressed_length by its contract (its result is            ***)
(*** snappy_max_compressed_length n for every n); the branch on the         ***)
(*** comparison with *compressed_length is split (BSTEP_SPLIT_PC_TAC) and   ***)
(*** the case that the hypothesis contradicts is closed; RawCompress by its ***)
(*** contract; the length written is not 0.                                 ***)

let SNAPPY_CC_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "c_snappy_compress"];;

let SNAPPY_CC_MAX_COMPRESSED_LENGTH = prove
 (`!n. snappy_max_compressed_length_gcc12_O2_result n =
       snappy_max_compressed_length n`,
  REWRITE_TAC[snappy_max_compressed_length_gcc12_O2_result;
              snappy_max_compressed_length; GT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let SNAPPY_CC_VAL_MAX_COMPRESSED_LENGTH = prove
 (`!n. val(word(snappy_max_compressed_length n):int64) =
       snappy_max_compressed_length n`,
  REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64; SNAPPY_MAX_COMPRESSED_LENGTH_BOUND]);;

let SNAPPY_CC_CARRY = prove
 (`!x y:int64. (&(val x) - &(val y):int = &(val(word_sub x y))) <=>
               val y <= val x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_VAL_WORD_SUB_CASES; INT_OF_NUM_LE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC);;

let SNAPPY_COMPRESS_NONEMPTY = prove
 (`!level (src:byte list).
        LENGTH src < 2 EXP 32 ==> ~(LENGTH(snappy_compress level src) = 0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[snappy_compress; GSYM NOT_LT] THEN
  ONCE_REWRITE_TAC[snappy_varint_encode] THEN COND_CASES_TAC THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC);;

(* The output decodes to the input and fits in the buffer.                    *)

let SNAPPY_C_COMPRESS_OUTPUT = prove
 (`!inp. LENGTH inp < 2 EXP 32
         ==> snappy_decode (snappy_compress 1 inp) = SOME inp /\
             LENGTH(snappy_compress 1 inp)
             <= snappy_max_compressed_length (LENGTH inp)`,
  MESON_TAC[SNAPPY_COMPRESS_ROUNDTRIP; SNAPPY_COMPRESS_LENGTH]);;

let SNAPPY_CC_PRESERVED_TAC pname ctm =
  MATCH_MP_TAC(ISPEC ctm ENSURES_MAYCHANGE_PRESERVED) THEN
  CONJ_TAC THENL [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV; ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_PRESERVED_KEEP_TAC;
    REWRITE_TAC[GSYM CONJ_ASSOC; GSYM SEQ_ASSOC] THEN
    W(fun (asl,w) -> X_GEN_TAC(mk_var(pname,type_of(fst(dest_forall w)))))];;

let SNAPPY_CC_START_TAC =
  SNAPPY_CC_PRESERVED_TAC "x19" `X19` THEN
  SNAPPY_CC_PRESERVED_TAC "x20" `X20` THEN
  SNAPPY_CC_PRESERVED_TAC "x21" `X21` THEN
  SNAPPY_CC_PRESERVED_TAC "x22" `X22` THEN
  SNAPPY_CC_PRESERVED_TAC "x23" `X23` THEN
  SNAPPY_CC_PRESERVED_TAC "x29" `X29` THEN
  MATCH_MP_TAC(ISPECL [`SP`; `stackpointer:int64`]
    ENSURES_MAYCHANGE_EXISTING_PRESERVED) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV;
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_PRESERVED_KEEP_TAC;
    SIMP_TAC[];
    REWRITE_TAC[GSYM SEQ_ASSOC]] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI];;

(* Close the case of a split branch (its condition, the last assumption)     *)
(* that the facts without a state contradict.                               *)

let SNAPPY_CC_KILL_TAC rws : tactic = fun (asl,w) ->
  match asl with
    (_,c)::rest ->
      let nostate th = not(exists (fun v -> type_of v = `:armstate`)
                                  (frees(concl th))) in
      let facts = filter nostate (map snd rest) in
      let conv = REWRITE_CONV (rws @ facts) THENC WORD_REDUCE_CONV THENC
                 INT_REDUCE_CONV THENC NUM_REDUCE_CONV THENC
                 REWRITE_CONV facts in
      let th = CONV_RULE conv c in
      if concl th = `F` then CONTR_TAC th (asl,w)
      else failwith "SNAPPY_CC_KILL_TAC"
  | [] -> failwith "SNAPPY_CC_KILL_TAC";;

let SNAPPY_CC_BRANCH_TAC rws =
  TRY(BSTEP_SPLIT_PC_TAC THEN TRY(SNAPPY_CC_KILL_TAC rws));;

let SNAPPY_CC_MAXLEN_TAC exec =
  ARM_BSTEP_CONTRACT_SPECL_TAC exec
    SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    [`read X0 s`; `pc:num`; `read X30 s`] "s13" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SNAPPY_CC_MAX_COMPRESSED_LENGTH]);;

let SNAPPY_CC_MAXLEN_SAFE_TAC exec =
  ARM_BSTEP_CONTRACT_SPECL_TAC exec
    SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    [`read events s`; `read X0 s`; `pc:num`; `read X30 s`] "s13" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SNAPPY_CC_MAX_COMPRESSED_LENGTH]);;

let SNAPPY_C_COMPRESS_TOO_SMALL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_C_COMPRESS_TOO_SMALL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let exec = SNAPPY_CC_EXEC in
  REWRITE_TAC[C_ARGUMENTS; C_RETURN] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SNAPPY_CC_START_TAC THEN
  ASSUME_TAC(SPEC `val(n:int64)` SNAPPY_CC_VAL_MAX_COMPRESSED_LENGTH) THEN
  SUBGOAL_THEN `~(snappy_max_compressed_length (val(n:int64)) <= val(len:int64))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[NOT_LE]; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  LABELLED_TAC "steps 1-12" (ARM_BSTEP_TAC exec (1--12)) THEN
  LABELLED_TAC "maxlen" (SNAPPY_CC_MAXLEN_TAC exec) THEN
  LABELLED_TAC "steps 13-14"
   (ARM_BSTEP_TAC ~rewrites:[SNAPPY_CC_CARRY] exec (13--14)) THEN
  LABELLED_TAC "branch"
   (SNAPPY_CC_BRANCH_TAC [SNAPPY_CC_CARRY] THEN
    W(fun (asl,w) -> if is_cond(bstep_pc_value (asl,w))
                     then failwith "undecided" else ALL_TAC)) THEN
  LABELLED_TAC "steps 15-20" (ARM_BSTEP_TAC exec (15--20)) THEN
  LABELLED_TAC ~solved:true "final"
   (BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_RULE
     `word_add (word_sub (sp:int64) (word 64)) (word 64) = sp`] THEN
    ASM_REWRITE_TAC[]));;

let SNAPPY_C_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_C_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let exec = SNAPPY_CC_EXEC in
  MAP_EVERY X_GEN_TAC
   [`heap_ok:(int64#num)list->(int64->byte)->bool`;
    `heap_fp:(int64#num)list->int64->bool`;
    `heap_room:(int64#num)list->num->bool`; `stk:num`] THEN
  DISCH_THEN(fun model ->
    ASSUME_TAC model THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; ALLPAIRS; ALL; PAIRWISE] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SNAPPY_CC_START_TAC THEN
    SUBGOAL_THEN `val(word(LENGTH(inp:byte list)):int64) = LENGTH inp`
    ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN
      UNDISCH_TAC `LENGTH(inp:byte list) < 2 EXP 32` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASSUME_TAC(SPEC `LENGTH(inp:byte list)` SNAPPY_CC_VAL_MAX_COMPRESSED_LENGTH) THEN
    SUBGOAL_THEN `~(val(len:int64) < snappy_max_compressed_length
                                       (LENGTH(inp:byte list)))`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[NOT_LT]; ALL_TAC] THEN
    MP_TAC(SPECL [`1`; `inp:byte list`] SNAPPY_COMPRESS_NONEMPTY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPECL [`1`; `inp:byte list`] SNAPPY_COMPRESS_LENGTH) THEN
    ANTS_TAC THENL [REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `val(word(LENGTH(snappy_compress 1 inp)):int64) =
                  LENGTH(snappy_compress 1 inp)` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN
      MP_TAC(SPEC `LENGTH(inp:byte list)` SNAPPY_MAX_COMPRESSED_LENGTH_BOUND) THEN
      UNDISCH_TAC `LENGTH(snappy_compress 1 inp) <=
                   snappy_max_compressed_length (LENGTH(inp:byte list))` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(word(LENGTH(snappy_compress 1 inp)):int64 = word 0)`
      ASSUME_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    LABELLED_TAC "steps 1-12" (ARM_BSTEP_TAC exec (1--12)) THEN
    LABELLED_TAC "maxlen" (SNAPPY_CC_MAXLEN_TAC exec) THEN
    LABELLED_TAC "steps 13-14"
     (ARM_BSTEP_TAC ~rewrites:[SNAPPY_CC_CARRY] exec (13--14)) THEN
    LABELLED_TAC "branch"
     (SNAPPY_CC_BRANCH_TAC [SNAPPY_CC_CARRY] THEN
      W(fun (asl,w) -> if is_cond(bstep_pc_value (asl,w))
                       then failwith "undecided" else ALL_TAC)) THEN
    LABELLED_TAC "steps 15-19" (ARM_BSTEP_TAC exec (15--19)) THEN
    LABELLED_TAC "RawCompress"
     (ARM_BSTEP_CONTRACT_SPECL_TAC exec
       (MATCH_MP SNAPPY_RAW_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT model)
       [`inp:byte list`; `src:int64`; `out:int64`; `lenp:int64`;
        `H:(int64#num)list`; `pc:num`; `ea:int64`; `el:num`; `ev:num`;
        `rw:num`; `read SP s`; `read X30 s`] "s20") THEN
    RULE_ASSUM_TAC(fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),
          Const("memory",_)),Comb(Const("bytelist",_),Comb(Comb(Const(",",_),
          Var("out",_)),_)))),_)),_) ->
          let th' = REWRITE_RULE[READ_BYTELIST_EQ_BYTES] th in
          if is_conj(concl th') then CONJUNCT2 th' else th'
      | _ -> th) THEN
    LABELLED_TAC "steps 21-28" (ARM_BSTEP_TAC exec (21--28)) THEN
    LABELLED_TAC ~solved:true "final"
     (BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[READ_BYTELIST_EQ_BYTES; WORD_SUB_0] THEN
      CONV_TAC WORD_REDUCE_CONV THEN
      REWRITE_TAC[WORD_RULE
       `word_add (word_sub (sp:int64) (word 64)) (word 64) = sp`] THEN
      ASM_REWRITE_TAC[])));;

let SNAPPY_C_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_C_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  let exec = SNAPPY_CC_EXEC in
  MAP_EVERY X_GEN_TAC
   [`heap_ok:(int64#num)list->(int64->byte)->bool`;
    `heap_fp:(int64#num)list->int64->bool`;
    `heap_room:(int64#num)list->num->bool`; `stk:num`] THEN
  DISCH_THEN(fun model ->
    ASSUME_TAC model THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; ALLPAIRS; ALL; PAIRWISE] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SNAPPY_CC_START_TAC THEN
    SUBGOAL_THEN `val(word(LENGTH(inp:byte list)):int64) = LENGTH inp`
    ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN
      UNDISCH_TAC `LENGTH(inp:byte list) < 2 EXP 32` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASSUME_TAC(SPEC `LENGTH(inp:byte list)` SNAPPY_CC_VAL_MAX_COMPRESSED_LENGTH) THEN
    SUBGOAL_THEN `~(val(len:int64) < snappy_max_compressed_length
                                       (LENGTH(inp:byte list)))`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[NOT_LT]; ALL_TAC] THEN
    MP_TAC(SPECL [`1`; `inp:byte list`] SNAPPY_COMPRESS_NONEMPTY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPECL [`1`; `inp:byte list`] SNAPPY_COMPRESS_LENGTH) THEN
    ANTS_TAC THENL [REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `val(word(LENGTH(snappy_compress 1 inp)):int64) =
                  LENGTH(snappy_compress 1 inp)` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN
      MP_TAC(SPEC `LENGTH(inp:byte list)` SNAPPY_MAX_COMPRESSED_LENGTH_BOUND) THEN
      UNDISCH_TAC `LENGTH(snappy_compress 1 inp) <=
                   snappy_max_compressed_length (LENGTH(inp:byte list))` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(word(LENGTH(snappy_compress 1 inp)):int64 = word 0)`
      ASSUME_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    LABELLED_TAC "steps 1-12" (ARM_BSTEP_TAC exec (1--12)) THEN
    LABELLED_TAC "maxlen" (SNAPPY_CC_MAXLEN_SAFE_TAC exec) THEN
    LABELLED_TAC "steps 13-14"
     (ARM_BSTEP_TAC ~rewrites:[SNAPPY_CC_CARRY] exec (13--14)) THEN
    LABELLED_TAC "branch"
     (SNAPPY_CC_BRANCH_TAC [SNAPPY_CC_CARRY] THEN
      W(fun (asl,w) -> if is_cond(bstep_pc_value (asl,w))
                       then failwith "undecided" else ALL_TAC)) THEN
    LABELLED_TAC "steps 15-19" (ARM_BSTEP_TAC exec (15--19)) THEN
    LABELLED_TAC "RawCompress"
     (ARM_BSTEP_CONTRACT_SPECL_TAC exec
       (MATCH_MP SNAPPY_RAW_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE model)
       [`read events s`; `inp:byte list`; `src:int64`; `out:int64`; `lenp:int64`;
        `H:(int64#num)list`; `pc:num`; `ea:int64`; `el:num`; `ev:num`;
        `rw:num`; `read SP s`; `read X30 s`] "s20") THEN
    RULE_ASSUM_TAC(fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),
          Const("memory",_)),Comb(Const("bytelist",_),Comb(Comb(Const(",",_),
          Var("out",_)),_)))),_)),_) ->
          let th' = REWRITE_RULE[READ_BYTELIST_EQ_BYTES] th in
          if is_conj(concl th') then CONJUNCT2 th' else th'
      | _ -> th) THEN
    LABELLED_TAC "steps 21-28" (ARM_BSTEP_TAC exec (21--28)) THEN
    LABELLED_TAC ~solved:true "final"
     (BSTEP_FINAL_TAC THEN SNAPPY_INSET_FIRST_TAC THEN
      ASM_REWRITE_TAC[READ_BYTELIST_EQ_BYTES; WORD_SUB_0] THEN
      CONV_TAC WORD_REDUCE_CONV THEN
      REWRITE_TAC[WORD_RULE
       `word_add (word_sub (sp:int64) (word 64)) (word 64) = sp`] THEN
      ASM_REWRITE_TAC[])));;
