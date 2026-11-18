(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccakf1600x4_xor_bytes_spec.ml";;


let XOR_LOOP1 = prove
 (XOR_LOOP1_STMT,
  MAP_EVERY X_GEN_TAC [`a:int64`; `d:int64`; `off:num`; `len:num`;
                       `S:1600 word`; `m:num`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL;
              READ_MEMORY_WBYTES_VAL; fst X4X_EXEC] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP2_TAC `len:num` `pc + mlk_keccakf1600x4_xor_bytes_c_loop1`
   `pc + mlk_keccakf1600x4_xor_bytes_c_loop1_exit`
   `\i s. read X5 s = word_add a (word off) /\ read X1 s = d /\
          read X6 s = word len /\ read X7 s = word i /\
          (~(i = 0) ==> read X8 s = word (i - 1)) /\
          read (memory :> bytes(d,len)) s = m /\
          !j. j < 200
              ==> read (memory :> bytes8(word_add a (word j))) s =
                  word_subword
                   (word_xor (S:1600 word)
                     (word(2 EXP (8 * off) * m MOD 2 EXP (8 * i))))
                   (8 * j,8)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Entry: the argument registers, and the zero-extended off and len ***)

    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC X4X_EXEC (1--4) THEN
    ARGS_32_TAC [`off:num`; `len:num`] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; WORD_XOR_0; word_subword] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES8_OF_NUM THEN
    EXISTS_TAC `200` THEN ASM_REWRITE_TAC[];

    (*** The loop body, for byte off + i of the state, and the test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `off + i < 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `bytes8` (concl th) then
        ASSUME_TAC(MP (SPEC `off + i` th) (ASSUME `off + i < 200`)) THEN
        ASSUME_TAC(XOR_BYTES_RESTRICT_RULE `off + i` th)
      else failwith "XOR_BYTES_RESTRICT_RULE") THEN
    MP_TAC(SPECL [`d:int64`; `len:num`; `m:num`; `i:num`; `s0:armstate`]
                 READ_MEMORY_BYTES8_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC X4X_EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_sub (word len) (word_add (word i) (word 1)):int64) = 0) <=>
      i + 1 < len`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `len < 2 EXP 64 /\ i + 1 < 2 EXP 64` MP_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ADD_SUB; GSYM WORD_ADD] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[XOR_BYTES_STEP] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    W(fun (_,w) -> SPEC_TAC(lhand(rand w),`b1:byte`) THEN
                   SPEC_TAC(rand(rand w),`b2:byte`)) THEN
    REPEAT GEN_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));

    (*** The loop exit, with the whole state ***)

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`a:int64`; `S:1600 word`; `off:num`; `len:num`; `d:int64`;
                   `m:num`; `s0:armstate`] XOR_BYTES_FINAL) THEN
    ASM_REWRITE_TAC[READ_MEMORY_WBYTES_1600]]);;

let XOR_LOOP2 = xorB_prove XOR_LOOP2_STMT
  "mlk_keccakf1600x4_xor_bytes_c_loop2"
  "mlk_keccakf1600x4_xor_bytes_c_loop2_exit" "200"
  (fun i -> "read X7 s = word_add (word_add a (word off)) (word 200) /\\
             read X1 s = word "^i^" /\\ read X5 s = word_add a (word off) /\\
             read X2 s = d /\\ read X8 s = word (len - 1)") 3;;

let XOR_LOOP3 = xorB_prove XOR_LOOP3_STMT
  "mlk_keccakf1600x4_xor_bytes_c_loop3"
  "mlk_keccakf1600x4_xor_bytes_c_loop3_exit" "400"
  (fun i -> "read X6 s = word_add (word_add a (word off)) (word 400) /\\
             read X1 s = word "^i^" /\\ read X5 s = word_add a (word off) /\\
             read X3 s = d /\\ read X8 s = word (len - 1)") 3;;

let XOR_LOOP4 = xorB_prove XOR_LOOP4_STMT
  "mlk_keccakf1600x4_xor_bytes_c_loop4"
  "mlk_keccakf1600x4_xor_bytes_c_loop4_exit" "600"
  (fun i -> "read X5 s = word_add (word_add a (word off)) (word 600) /\\
             read X0 s = word "^i^" /\\ read X4 s = d /\\
             read X8 s = word (len - 1)") 0;;

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d0:int64`; `d1:int64`; `d2:int64`; `d3:int64`;
    `off:num`; `len:num`; `S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
    `S3:1600 word`; `m0:num`; `m1:num`; `m2:num`; `m3:num`; `pc:num`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[SOME_FLAGS; C_ARGUMENTS; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  X4X_LOOP_TAC XOR_LOOP1 1 `d0:int64` `S0:1600 word` `m0:num` THEN
  ARM_STEPS_TAC X4X_EXEC (2--3) THEN
  X4X_LOOP_TAC XOR_LOOP2 4 `d1:int64` `S1:1600 word` `m1:num` THEN
  X4X_LOOP_TAC XOR_LOOP3 5 `d2:int64` `S2:1600 word` `m2:num` THEN
  X4X_LOOP_TAC XOR_LOOP4 6 `d3:int64` `S3:1600 word` `m3:num` THEN
  ARM_STEPS_TAC X4X_EXEC (7--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let XOR_FULL2 = xorF_prove XOR_FULL2_STMT
  "mlk_keccakf1600x4_xor_bytes_c_loop2"
  "mlk_keccakf1600x4_xor_bytes_c_loop2_exit" "200"
  (fun i -> "read X7 s = word_add (word_add a (word off)) (word 200) /\\
             read X1 s = word "^i^" /\\ read X5 s = word_add a (word off) /\\
             read X2 s = d /\\ read X8 s = word (len - 1)") 3;;

let XOR_FULL3 = xorF_prove XOR_FULL3_STMT
  "mlk_keccakf1600x4_xor_bytes_c_loop3"
  "mlk_keccakf1600x4_xor_bytes_c_loop3_exit" "400"
  (fun i -> "read X6 s = word_add (word_add a (word off)) (word 400) /\\
             read X1 s = word "^i^" /\\ read X5 s = word_add a (word off) /\\
             read X3 s = d /\\ read X8 s = word (len - 1)") 3;;

let XOR_FULL4 = xorF_prove XOR_FULL4_STMT
  "mlk_keccakf1600x4_xor_bytes_c_loop4"
  "mlk_keccakf1600x4_xor_bytes_c_loop4_exit" "600"
  (fun i -> "read X5 s = word_add (word_add a (word off)) (word 600) /\\
             read X0 s = word "^i^" /\\ read X4 s = d /\\
             read X8 s = word (len - 1)") 0;;

let XOR_FULL1 = prove
 (XOR_FULL1_STMT,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (d:int64) (off:num) (len:num) (pc:num).
      APPEND (f_ev_epil a d off len pc)
        (APPEND (ENUMERATEL len (\i. f_ev_loop a d off len pc i))
                (f_ev_prol a d off len pc)):(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `d:int64`; `off:num`; `len:num`;
                       `S:1600 word`; `m:num`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL;
              READ_MEMORY_WBYTES_VAL; fst X4X_EXEC] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `len:num` `pc + mlk_keccakf1600x4_xor_bytes_c_loop1`
   `pc + mlk_keccakf1600x4_xor_bytes_c_loop1_exit`
   `\i s. read X5 s = word_add a (word off) /\ read X1 s = d /\
          read X6 s = word len /\ read X7 s = word i /\
          (~(i = 0) ==> read X8 s = word (i - 1)) /\
          read (memory :> bytes(d,len)) s = m /\
          !j. j < 200
              ==> read (memory :> bytes8(word_add a (word j))) s =
                  word_subword
                   (word_xor (S:1600 word)
                     (word(2 EXP (8 * off) * m MOD 2 EXP (8 * i))))
                   (8 * j,8)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Entry: the argument registers, and the zero-extended off and len ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC X4X_EXEC (1--4) THEN
    ARGS_32_TAC [`off:num`; `len:num`] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; WORD_XOR_0; word_subword] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES8_OF_NUM THEN
      EXISTS_TAC `200` THEN ASM_REWRITE_TAC[];
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The loop body, for byte off + i of the state, and the test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `off + i < 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `bytes8` (concl th) then
        ASSUME_TAC(MP (SPEC `off + i` th) (ASSUME `off + i < 200`)) THEN
        ASSUME_TAC(XOR_BYTES_RESTRICT_RULE `off + i` th)
      else failwith "XOR_BYTES_RESTRICT_RULE") THEN
    MP_TAC(SPECL [`d:int64`; `len:num`; `m:num`; `i:num`; `s0:armstate`]
                 READ_MEMORY_BYTES8_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC X4X_EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_sub (word len) (word_add (word i) (word 1)):int64) = 0) <=>
      i + 1 < len`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `len < 2 EXP 64 /\ i + 1 < 2 EXP 64` MP_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ADD_SUB; GSYM WORD_ADD] THEN
    REPEAT CONJ_TAC THEN
    FIRST
     [COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC;
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[XOR_BYTES_STEP] THEN
      COND_CASES_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
      FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      W(fun (_,w) -> SPEC_TAC(lhand(rand w),`b1:byte`) THEN
                     SPEC_TAC(rand(rand w),`b2:byte`)) THEN
      REPEAT GEN_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));
      ASM_REWRITE_TAC[ARITH_RULE `~(i + 1 = 0)`] THEN NO_TAC;
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The loop exit, with the whole state ***)

    REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MP_TAC(ISPECL [`a:int64`; `S:1600 word`; `off:num`; `len:num`; `d:int64`;
                     `m:num`; `s0:armstate`] XOR_BYTES_FINAL) THEN
      ASM_REWRITE_TAC[READ_MEMORY_WBYTES_1600];
      DISCHARGE_SAFETY_PROPERTY_TAC]]);;

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL = prove
 (MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC XOR_FULL1 "H_L1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC XOR_FULL2 "H_L2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC XOR_FULL3 "H_L3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC XOR_FULL4 "H_L4" THEN
  META_EXISTS_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SOME_FLAGS; C_ARGUMENTS; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  X4X_FULL_CALL_TAC "H_L1" `d0:int64` `S0:1600 word` `m0:num` 1 THEN
  ARM_STEPS_TAC X4X_EXEC (2--3) THEN
  X4X_FULL_CALL_TAC "H_L2" `d1:int64` `S1:1600 word` `m1:num` 4 THEN
  X4X_FULL_CALL_TAC "H_L3" `d2:int64` `S2:1600 word` `m2:num` 5 THEN
  X4X_FULL_CALL_TAC "H_L4" `d3:int64` `S3:1600 word` `m3:num` 6 THEN
  ARM_STEPS_TAC X4X_EXEC (7--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT,
  MP_TAC MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `S0:1600 word`
   `read (memory :> wbytes a):armstate->1600 word` THEN
  GHOST_INTRO_TAC `S1:1600 word`
   `read (memory :> wbytes (word_add a (word 200))):armstate->1600 word` THEN
  GHOST_INTRO_TAC `S2:1600 word`
   `read (memory :> wbytes (word_add a (word 400))):armstate->1600 word` THEN
  GHOST_INTRO_TAC `S3:1600 word`
   `read (memory :> wbytes (word_add a (word 600))):armstate->1600 word` THEN
  GHOST_INTRO_TAC `m0:num` `read (memory :> bytes(d0,len))` THEN
  GHOST_INTRO_TAC `m1:num` `read (memory :> bytes(d1,len))` THEN
  GHOST_INTRO_TAC `m2:num` `read (memory :> bytes(d2,len))` THEN
  GHOST_INTRO_TAC `m3:num` `read (memory :> bytes(d3,len))` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `d0:int64`; `d1:int64`; `d2:int64`;
    `d3:int64`; `off:num`; `len:num`; `S0:1600 word`; `S1:1600 word`;
    `S2:1600 word`; `S3:1600 word`; `m0:num`; `m1:num`; `m2:num`; `m3:num`;
    `pc:num`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;
