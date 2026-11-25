(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/c_compress_with_level_spec.ml";;
needs "arm/proofs/bstep.ml";;
needs "arm/proofs/snappy/decompressor_objects.ml";;
needs "common/snappy/snappy_roundtrip.ml";;
needs "arm/proofs/snappy/events_inset.ml";;

(*** As c_compress_proof.ml: snappy_max_compressed_length by its contract, ***)
(*** the branches split (BSTEP_SPLIT_PC_TAC) and the case that the          ***)
(*** hypotheses contradict closed; the level test is on the low 32 bits of  ***)
(*** x2, word_zx lv; RawCompress(..., options) by its contract.             ***)

let SNAPPY_CCL_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "c_snappy_compress_with_level"];;

let SNAPPY_CCL_MAX_COMPRESSED_LENGTH = prove
 (`!n. snappy_max_compressed_length_gcc12_O2_result n =
       snappy_max_compressed_length n`,
  REWRITE_TAC[snappy_max_compressed_length_gcc12_O2_result;
              snappy_max_compressed_length; GT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let SNAPPY_CCL_VAL_MAX_COMPRESSED_LENGTH = prove
 (`!n. val(word(snappy_max_compressed_length n):int64) =
       snappy_max_compressed_length n`,
  REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64; SNAPPY_MAX_COMPRESSED_LENGTH_BOUND]);;

let SNAPPY_CCL_CARRY = prove
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

let SNAPPY_C_COMPRESS_WITH_LEVEL_OUTPUT = prove
 (`!level inp. (level = 1 \/ level = 2) /\ LENGTH inp < 2 EXP 32
         ==> snappy_decode (snappy_compress level inp) = SOME inp /\
             LENGTH(snappy_compress level inp)
             <= snappy_max_compressed_length (LENGTH inp)`,
  MESON_TAC[SNAPPY_COMPRESS_ROUNDTRIP; SNAPPY_COMPRESS_LENGTH]);;

let SNAPPY_CCL_PRESERVED_TAC pname ctm =
  MATCH_MP_TAC(ISPEC ctm ENSURES_MAYCHANGE_PRESERVED) THEN
  CONJ_TAC THENL [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV; ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_PRESERVED_KEEP_TAC;
    REWRITE_TAC[GSYM CONJ_ASSOC; GSYM SEQ_ASSOC] THEN
    W(fun (asl,w) -> X_GEN_TAC(mk_var(pname,type_of(fst(dest_forall w)))))];;

let SNAPPY_CCL_START_TAC =
  SNAPPY_CCL_PRESERVED_TAC "x19" `X19` THEN
  SNAPPY_CCL_PRESERVED_TAC "x20" `X20` THEN
  SNAPPY_CCL_PRESERVED_TAC "x21" `X21` THEN
  SNAPPY_CCL_PRESERVED_TAC "x22" `X22` THEN
  SNAPPY_CCL_PRESERVED_TAC "x23" `X23` THEN
  SNAPPY_CCL_PRESERVED_TAC "x24" `X24` THEN
  SNAPPY_CCL_PRESERVED_TAC "x29" `X29` THEN
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

let SNAPPY_CCL_KILL_TAC rws : tactic = fun (asl,w) ->
  match asl with
    (_,c)::rest ->
      let nostate th = not(exists (fun v -> type_of v = `:armstate`)
                                  (frees(concl th))) in
      let facts = filter nostate (map snd rest) in
      let conv = REWRITE_CONV (rws @ facts) THENC WORD_REDUCE_CONV THENC
                 INT_REDUCE_CONV THENC NUM_REDUCE_CONV THENC
                 REWRITE_CONV (rws @ facts) THENC WORD_REDUCE_CONV THENC
                 REWRITE_CONV [] in
      let th = CONV_RULE conv c in
      if concl th = `F` then CONTR_TAC th (asl,w)
      else failwith "SNAPPY_CCL_KILL_TAC"
  | [] -> failwith "SNAPPY_CCL_KILL_TAC";;

let SNAPPY_CCL_BRANCH_TAC rws =
  TRY(BSTEP_SPLIT_PC_TAC THEN TRY(SNAPPY_CCL_KILL_TAC rws));;

(* With memcpy's correct_safe contract among the hypotheses (the _SAFE     *)
(* proof), the _SAFE contract of the callee.                                 *)

let SNAPPY_CCL_MAXLEN_CALL_TAC exec : tactic = fun (asl,w) ->
  if exists (fun (_,th) -> try fst(dest_const(fst(strip_comb(concl th)))) =
                               "memcpy_correct_safe_contract"
                           with Failure _ -> false) asl
  then ARM_BSTEP_CONTRACT_SPECL_TAC exec
         SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE
         [`read events s`; `read X0 s`; `pc:num`; `read X30 s`] "s14" (asl,w)
  else ARM_BSTEP_CONTRACT_SPECL_TAC exec
         SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
         [`read X0 s`; `pc:num`; `read X30 s`] "s14" (asl,w);;

let SNAPPY_CCL_MAXLEN_TAC exec =
  SNAPPY_CCL_MAXLEN_CALL_TAC exec THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SNAPPY_CCL_MAX_COMPRESSED_LENGTH]);;

(* The level test: sub w1, w21, #1; cmp w1, #1; b.ls is taken iff the int   *)
(* is 1 or 2.                                                                *)

let SNAPPY_CCL_CARRY32 = prove
 (`!x y:int32. (&(val x) - &(val y):int = &(val(word_sub x y))) <=>
               val y <= val x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_VAL_WORD_SUB_CASES; INT_OF_NUM_LE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC);;

let SNAPPY_CCL_CARRY32_1 = prove
 (`!x:int32. (&(val x) - &1:int = &(val(word_sub x (word 1)))) <=> 1 <= val x`,
  GEN_TAC THEN MP_TAC(ISPECL [`x:int32`; `word 1:int32`] SNAPPY_CCL_CARRY32) THEN
  REWRITE_TAC[VAL_WORD_1]);;

let SNAPPY_CCL_LEVEL_TEST = prove
 (`!x:int32. (1 <= val(word_sub x (word 1)) <=> ~(x = word 1)) /\
             (val(word_sub (word_sub x (word 1)) (word 1)) = 0 <=> x = word 2)`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; VAL_EQ_0] THEN
  REWRITE_TAC[WORD_RULE `word_sub x y = z <=> word_add y z = x`;
              WORD_RULE `z = word_sub x y <=> word_add y z = x`] THEN
  CONV_TAC WORD_REDUCE_CONV THEN MESON_TAC[]);;

let SNAPPY_CCL_ZX_ZX = prove
 (`!y:int32. word_zx(word_zx y:int64):int32 = y`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; DIMINDEX_32;
                           DIMINDEX_64] THEN
  MP_TAC(ISPEC `y:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
  DISCH_TAC THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 2 EXP 32 ==> n < 2 EXP 64`]);;

let SNAPPY_CCL_LEVEL_RWS =
  [SNAPPY_CCL_CARRY32; SNAPPY_CCL_CARRY32_1; SNAPPY_CCL_ZX_ZX; VAL_WORD_1;
   SNAPPY_CCL_LEVEL_TEST];;

let SNAPPY_C_COMPRESS_WITH_LEVEL_TOO_SMALL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_C_COMPRESS_WITH_LEVEL_TOO_SMALL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let exec = SNAPPY_CCL_EXEC in
  REWRITE_TAC[C_ARGUMENTS; C_RETURN] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SNAPPY_CCL_START_TAC THEN
  ASSUME_TAC(SPEC `val(n:int64)` SNAPPY_CCL_VAL_MAX_COMPRESSED_LENGTH) THEN
  SUBGOAL_THEN `~(snappy_max_compressed_length (val(n:int64)) <= val(len:int64))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[NOT_LE]; ALL_TAC] THEN
  LABELLED_TAC "init" (ENSURES_INIT_TAC "s0") THEN
  LABELLED_TAC "steps 1-13" (ARM_BSTEP_TAC exec (1--13)) THEN
  LABELLED_TAC "maxlen" (SNAPPY_CCL_MAXLEN_TAC exec) THEN
  LABELLED_TAC "steps 14-15"
   (ARM_BSTEP_TAC ~rewrites:[SNAPPY_CCL_CARRY] exec (14--15)) THEN
  LABELLED_TAC "branch"
   (SNAPPY_CCL_BRANCH_TAC [SNAPPY_CCL_CARRY] THEN
    W(fun (asl,w) -> if is_cond(bstep_pc_value (asl,w))
                     then failwith "undecided" else ALL_TAC)) THEN
  LABELLED_TAC "steps 16-21" (ARM_BSTEP_TAC exec (16--21)) THEN
  LABELLED_TAC ~solved:true "final"
   (BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_RULE
     `word_add (word_sub (sp:int64) (word 64)) (word 64) = sp`] THEN
    ASM_REWRITE_TAC[]));;

let SNAPPY_C_COMPRESS_WITH_LEVEL_INVALID_LEVEL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_C_COMPRESS_WITH_LEVEL_INVALID_LEVEL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let exec = SNAPPY_CCL_EXEC in
  REWRITE_TAC[C_ARGUMENTS; C_RETURN] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SNAPPY_CCL_START_TAC THEN
  ASSUME_TAC(SPEC `val(n:int64)` SNAPPY_CCL_VAL_MAX_COMPRESSED_LENGTH) THEN
  SUBGOAL_THEN `~(val(len:int64) < snappy_max_compressed_length (val(n:int64)))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[NOT_LT]; ALL_TAC] THEN
  LABELLED_TAC "init" (ENSURES_INIT_TAC "s0") THEN
  LABELLED_TAC "steps 1-13" (ARM_BSTEP_TAC exec (1--13)) THEN
  LABELLED_TAC "maxlen" (SNAPPY_CCL_MAXLEN_TAC exec) THEN
  LABELLED_TAC "steps 14-15"
   (ARM_BSTEP_TAC ~rewrites:[SNAPPY_CCL_CARRY] exec (14--15)) THEN
  LABELLED_TAC "branch"
   (SNAPPY_CCL_BRANCH_TAC [SNAPPY_CCL_CARRY] THEN
    W(fun (asl,w) -> if is_cond(bstep_pc_value (asl,w))
                     then failwith "undecided" else ALL_TAC)) THEN
  LABELLED_TAC "steps 16-19"
   (ARM_BSTEP_TAC ~rewrites:[SNAPPY_CCL_CARRY32] exec (16--19)) THEN
  LABELLED_TAC "level branch"
   (SNAPPY_CCL_BRANCH_TAC SNAPPY_CCL_LEVEL_RWS THEN
    W(fun (asl,w) -> if is_cond(bstep_pc_value (asl,w))
                     then failwith "undecided" else ALL_TAC)) THEN
  LABELLED_TAC "steps 20-24" (ARM_BSTEP_TAC exec (20--24)) THEN
  LABELLED_TAC ~solved:true "final"
   (BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_RULE
     `word_add (word_sub (sp:int64) (word 64)) (word 64) = sp`] THEN
    ASM_REWRITE_TAC[]));;

(* The level test for level = 1 \/ level = 2: the case of the branch to the *)
(* error return is closed in each of the two cases of the level.            *)

let SNAPPY_CCL_KILL_LEVEL_TAC : tactic =
  POP_ASSUM(fun c ->
    FIRST_ASSUM(DISJ_CASES_TAC o check (fun th ->
      concl th = `level = 1 \/ level = 2`)) THEN
    ASSUME_TAC c) THEN
  SNAPPY_CCL_KILL_TAC SNAPPY_CCL_LEVEL_RWS;;


let SNAPPY_CCL_CORRECT_TAC model =
  let exec = SNAPPY_CCL_EXEC in
    SUBGOAL_THEN `level <= 2` ASSUME_TAC THENL
     [FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(lv:int64) MOD 2 EXP 32 = level` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int32->num` o check (fun th ->
        is_eq(concl th) && type_of(lhs(concl th)) = `:int32`)) THEN
      REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32] THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `level <= 2` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `val(word(LENGTH(inp:byte list)):int64) = LENGTH inp`
    ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN
      UNDISCH_TAC `LENGTH(inp:byte list) < 2 EXP 32` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASSUME_TAC(SPEC `LENGTH(inp:byte list)` SNAPPY_CCL_VAL_MAX_COMPRESSED_LENGTH) THEN
    SUBGOAL_THEN `~(val(len:int64) < snappy_max_compressed_length
                                       (LENGTH(inp:byte list)))`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[NOT_LT]; ALL_TAC] THEN
    MP_TAC(SPECL [`level:num`; `inp:byte list`] SNAPPY_COMPRESS_NONEMPTY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPECL [`level:num`; `inp:byte list`] SNAPPY_COMPRESS_LENGTH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `val(word(LENGTH(snappy_compress level inp)):int64) =
                  LENGTH(snappy_compress level inp)` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN
      MP_TAC(SPEC `LENGTH(inp:byte list)` SNAPPY_MAX_COMPRESSED_LENGTH_BOUND) THEN
      UNDISCH_TAC `LENGTH(snappy_compress level inp) <=
                   snappy_max_compressed_length (LENGTH(inp:byte list))` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(word(LENGTH(snappy_compress level inp)):int64 = word 0)`
      ASSUME_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    LABELLED_TAC "init" (ENSURES_INIT_TAC "s0") THEN
    LABELLED_TAC "steps 1-13" (ARM_BSTEP_TAC exec (1--13)) THEN
    LABELLED_TAC "maxlen" (SNAPPY_CCL_MAXLEN_TAC exec) THEN
    LABELLED_TAC "steps 14-15"
     (ARM_BSTEP_TAC ~rewrites:[SNAPPY_CCL_CARRY] exec (14--15)) THEN
    LABELLED_TAC "branch"
     (SNAPPY_CCL_BRANCH_TAC [SNAPPY_CCL_CARRY] THEN
      W(fun (asl,w) -> if is_cond(bstep_pc_value (asl,w))
                       then failwith "undecided" else ALL_TAC)) THEN
    LABELLED_TAC "steps 16-19"
     (ARM_BSTEP_TAC ~rewrites:[SNAPPY_CCL_CARRY32] exec (16--19)) THEN
    LABELLED_TAC "level branch"
     (TRY(BSTEP_SPLIT_PC_TAC THEN TRY(SNAPPY_CCL_KILL_LEVEL_TAC)) THEN
      W(fun (asl,w) -> if is_cond(bstep_pc_value (asl,w))
                       then failwith "undecided" else ALL_TAC)) THEN
    LABELLED_TAC "steps 20-25" (ARM_BSTEP_TAC exec (20--25)) THEN
    SUBGOAL_THEN `read X4 s25 = word level` ASSUME_TAC THENL
     [LABELLED_TAC "level"
       (FIRST_ASSUM(fun th -> if lhs(concl th) = `read X4 s25` then
          GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
        REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
                    DIMINDEX_64] THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_SIMP_TAC[MOD_LT; ARITH_RULE
         `l <= 2 ==> l < 4294967296 /\ l < 18446744073709551616`]);
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if lhs(concl th) = `read X4 s25` &&
                               not(rand(concl th) = `word level:int64`)
                            then ALL_TAC else NO_TAC) THEN
    LABELLED_TAC "RawCompress"
     (ARM_BSTEP_CONTRACT_SPECL_TAC exec
       (MATCH_MP SNAPPY_RAW_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
                 model)
       [`level:num`; `inp:byte list`; `src:int64`; `out:int64`; `lenp:int64`;
        `H:(int64#num)list`; `pc:num`; `ea:int64`; `el:num`; `ev:num`;
        `rw:num`; `read SP s`; `read X30 s`] "s26") THEN
    RULE_ASSUM_TAC(fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),
          Const("memory",_)),Comb(Const("bytelist",_),Comb(Comb(Const(",",_),
          Var("out",_)),_)))),_)),_) ->
          let th' = REWRITE_RULE[READ_BYTELIST_EQ_BYTES] th in
          if is_conj(concl th') then CONJUNCT2 th' else th'
      | _ -> th) THEN
    LABELLED_TAC "steps 27-34" (ARM_BSTEP_TAC exec (27--34)) THEN
    LABELLED_TAC ~solved:true "final"
     (BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[READ_BYTELIST_EQ_BYTES; WORD_SUB_0] THEN
      CONV_TAC WORD_REDUCE_CONV THEN
      REWRITE_TAC[WORD_RULE
       `word_add (word_sub (sp:int64) (word 64)) (word 64) = sp`] THEN
      ASM_REWRITE_TAC[]);;

let SNAPPY_CCL_SAFE_TAC model =
  let exec = SNAPPY_CCL_EXEC in
    SUBGOAL_THEN `level <= 2` ASSUME_TAC THENL
     [FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(lv:int64) MOD 2 EXP 32 = level` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int32->num` o check (fun th ->
        is_eq(concl th) && type_of(lhs(concl th)) = `:int32`)) THEN
      REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32] THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `level <= 2` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `val(word(LENGTH(inp:byte list)):int64) = LENGTH inp`
    ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN
      UNDISCH_TAC `LENGTH(inp:byte list) < 2 EXP 32` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASSUME_TAC(SPEC `LENGTH(inp:byte list)` SNAPPY_CCL_VAL_MAX_COMPRESSED_LENGTH) THEN
    SUBGOAL_THEN `~(val(len:int64) < snappy_max_compressed_length
                                       (LENGTH(inp:byte list)))`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[NOT_LT]; ALL_TAC] THEN
    MP_TAC(SPECL [`level:num`; `inp:byte list`] SNAPPY_COMPRESS_NONEMPTY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPECL [`level:num`; `inp:byte list`] SNAPPY_COMPRESS_LENGTH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `val(word(LENGTH(snappy_compress level inp)):int64) =
                  LENGTH(snappy_compress level inp)` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN
      MP_TAC(SPEC `LENGTH(inp:byte list)` SNAPPY_MAX_COMPRESSED_LENGTH_BOUND) THEN
      UNDISCH_TAC `LENGTH(snappy_compress level inp) <=
                   snappy_max_compressed_length (LENGTH(inp:byte list))` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(word(LENGTH(snappy_compress level inp)):int64 = word 0)`
      ASSUME_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    LABELLED_TAC "init" (ENSURES_INIT_TAC "s0") THEN
    LABELLED_TAC "steps 1-13" (ARM_BSTEP_TAC exec (1--13)) THEN
    LABELLED_TAC "maxlen" (SNAPPY_CCL_MAXLEN_TAC exec) THEN
    LABELLED_TAC "steps 14-15"
     (ARM_BSTEP_TAC ~rewrites:[SNAPPY_CCL_CARRY] exec (14--15)) THEN
    LABELLED_TAC "branch"
     (SNAPPY_CCL_BRANCH_TAC [SNAPPY_CCL_CARRY] THEN
      W(fun (asl,w) -> if is_cond(bstep_pc_value (asl,w))
                       then failwith "undecided" else ALL_TAC)) THEN
    LABELLED_TAC "steps 16-19"
     (ARM_BSTEP_TAC ~rewrites:[SNAPPY_CCL_CARRY32] exec (16--19)) THEN
    LABELLED_TAC "level branch"
     (TRY(BSTEP_SPLIT_PC_TAC THEN TRY(SNAPPY_CCL_KILL_LEVEL_TAC)) THEN
      W(fun (asl,w) -> if is_cond(bstep_pc_value (asl,w))
                       then failwith "undecided" else ALL_TAC)) THEN
    LABELLED_TAC "steps 20-25" (ARM_BSTEP_TAC exec (20--25)) THEN
    SUBGOAL_THEN `read X4 s25 = word level` ASSUME_TAC THENL
     [LABELLED_TAC "level"
       (FIRST_ASSUM(fun th -> if lhs(concl th) = `read X4 s25` then
          GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
        REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
                    DIMINDEX_64] THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_SIMP_TAC[MOD_LT; ARITH_RULE
         `l <= 2 ==> l < 4294967296 /\ l < 18446744073709551616`]);
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if lhs(concl th) = `read X4 s25` &&
                               not(rand(concl th) = `word level:int64`)
                            then ALL_TAC else NO_TAC) THEN
    LABELLED_TAC "RawCompress"
     (ARM_BSTEP_CONTRACT_SPECL_TAC exec
       (MATCH_MP SNAPPY_RAW_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_SAFE
                 model)
       [`read events s`; `level:num`; `inp:byte list`; `src:int64`; `out:int64`; `lenp:int64`;
        `H:(int64#num)list`; `pc:num`; `ea:int64`; `el:num`; `ev:num`;
        `rw:num`; `read SP s`; `read X30 s`] "s26") THEN
    RULE_ASSUM_TAC(fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),
          Const("memory",_)),Comb(Const("bytelist",_),Comb(Comb(Const(",",_),
          Var("out",_)),_)))),_)),_) ->
          let th' = REWRITE_RULE[READ_BYTELIST_EQ_BYTES] th in
          if is_conj(concl th') then CONJUNCT2 th' else th'
      | _ -> th) THEN
    LABELLED_TAC "steps 27-34" (ARM_BSTEP_TAC exec (27--34)) THEN
    LABELLED_TAC ~solved:true "final"
     (BSTEP_FINAL_TAC THEN SNAPPY_INSET_FIRST_TAC THEN
      ASM_REWRITE_TAC[READ_BYTELIST_EQ_BYTES; WORD_SUB_0] THEN
      CONV_TAC WORD_REDUCE_CONV THEN
      REWRITE_TAC[WORD_RULE
       `word_add (word_sub (sp:int64) (word 64)) (word 64) = sp`] THEN
      ASM_REWRITE_TAC[]);;

let SNAPPY_C_COMPRESS_WITH_LEVEL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_C_COMPRESS_WITH_LEVEL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let exec = SNAPPY_CCL_EXEC in
  MAP_EVERY X_GEN_TAC
   [`heap_ok:(int64#num)list->(int64->byte)->bool`;
    `heap_fp:(int64#num)list->int64->bool`;
    `heap_room:(int64#num)list->num->bool`; `stk:num`] THEN
  DISCH_THEN(fun model ->
    ASSUME_TAC model THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; ALLPAIRS; ALL; PAIRWISE] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SNAPPY_CCL_START_TAC THEN
    SNAPPY_CCL_CORRECT_TAC model));;

let SNAPPY_C_COMPRESS_WITH_LEVEL_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_C_COMPRESS_WITH_LEVEL_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  let exec = SNAPPY_CCL_EXEC in
  MAP_EVERY X_GEN_TAC
   [`heap_ok:(int64#num)list->(int64->byte)->bool`;
    `heap_fp:(int64#num)list->int64->bool`;
    `heap_room:(int64#num)list->num->bool`; `stk:num`] THEN
  DISCH_THEN(fun model ->
    ASSUME_TAC model THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; ALLPAIRS; ALL; PAIRWISE] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SNAPPY_CCL_START_TAC THEN
    SNAPPY_CCL_SAFE_TAC model));;
