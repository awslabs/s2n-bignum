(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise Montgomery multiplication.                                      *)
(* ========================================================================= *)

needs "riscv/proofs/mldsa_objects.ml";;
needs "common/mlkem_mldsa.ml";;

let RV32_MLDSA_MONTMUL = prove
 (`!x y:int32.
    word_sub
      (word_subword
        (word_mul (word_sx x:int64) (word_sx y:int64))
        (32,32):int32)
      (word_subword
        (word_mul
          (word_sx
            (word_mul (word_mul x y) (word 58728449)):int64)
          (word 8380417:int64))
        (32,32):int32) =
    mldsa_montmul
      (word_sx y,
       word_sx (word_mul y (word 58728449))) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mldsa_montmul] THEN
  SUBGOAL_THEN
   `word_mul (word_mul x y) (word 58728449):int32 =
    word_subword
      (word_mul
        (word_sx x:int64)
        (word_sx (word_mul y (word 58728449)):int64))
      (0,32)`
  SUBST1_TAC THENL
   [SIMP_TAC[WORD_SUBWORD_MUL; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
    REWRITE_TAC[
      WORD_BLAST
       `word_subword (word_sx (z:int32):int64) (0,32):int32 = z`] THEN
    CONV_TAC WORD_RULE;
    REFL_TAC]);;

let MLDSA_POINTWISE_MONTGOMERY_CORE_EXACT = prove
 (`!a b:int32. !x y:num->int32. !pc:num.
    aligned 4 a /\
    aligned 4 b /\
    nonoverlapping
      ((word pc):int32,LENGTH mldsa_pointwise_montgomery_mc)
      (a,1024) /\
    nonoverlapping (a,1024) (b,1024)
    ==> ensures riscv
      (\s. aligned_bytes_loaded s (word pc)
             mldsa_pointwise_montgomery_mc /\
           read PC s = word (pc + 12) /\
           C_ARGUMENTS [a;b] s /\
           (!i. i < 256
                ==> read
                     (memory :>
                      bytes32 (word_add a (word (4 * i)))) s =
                    x i) /\
           (!i. i < 256
                ==> read
                     (memory :>
                      bytes32 (word_add b (word (4 * i)))) s =
                    y i))
      (\s. read PC s = word (pc + 76) /\
           !i. i < 256
               ==> read
                    (memory :>
                     bytes32 (word_add a (word (4 * i)))) s =
                   mldsa_montmul
                     (word_sx (y i),
                      word_sx
                       (word_mul (y i) (word 58728449)))
                     (x i))
      (MAYCHANGE
        [PC; S0; S1; T0; A0; A1; A2; A3; A4; A5; A6; A7] ,,
       MAYCHANGE [memory :> bytes(a,1024)] ,,
       MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `b:int32`; `x:num->int32`; `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[fst MLDSA_POINTWISE_MONTGOMERY_EXEC; C_ARGUMENTS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `256` `pc + 32` `pc + 72`
   `\i s.
      read S0 s = word 8380417 /\
      read S1 s = word 58728449 /\
      read T0 s = word_add a (word 1024) /\
      read A0 s = word_add a (word (4 * i)) /\
      read A1 s = word_add b (word (4 * i)) /\
      (!j. j < 256
           ==> read
                (memory :>
                 bytes32 (word_add a (word (4 * j)))) s =
               if j < i then
                 mldsa_montmul
                   (word_sx (y j),
                    word_sx
                     (word_mul (y j) (word 58728449)))
                   (x j)
               else x j) /\
      (!j. j < 256
           ==> read
                (memory :>
                 bytes32 (word_add b (word (4 * j)))) s =
               y j)` THEN
  CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    RISCV_STEPS_TAC MLDSA_POINTWISE_MONTGOMERY_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC
     [WORD_ADD_0; MULT_CLAUSES; ARITH_RULE `~(j < 0)`];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `aligned 4 (word_add a (word (4 * i)):int32)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[ALIGNED_WORD_ADD_EQ; ALIGNED_WORD; DIMINDEX_32] THEN
      CONJ_TAC THENL
       [CONV_TAC NUM_DIVIDES_CONV;
        MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[DIVIDES_REFL]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `aligned 4 (word_add b (word (4 * i)):int32)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[ALIGNED_WORD_ADD_EQ; ALIGNED_WORD; DIMINDEX_32] THEN
      CONJ_TAC THENL
       [CONV_TAC NUM_DIVIDES_CONV;
        MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[DIVIDES_REFL]];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM
     (fun th ->
       let th' =
         check
          (fun th ->
            is_forall (concl th) && vfree_in `a:int32` (concl th))
          th in
       ASSUME_TAC (MP (SPEC `i:num` th') (ASSUME `i < 256`))) THEN
    FIRST_ASSUM
     (fun th ->
       let th' =
         check
          (fun th ->
            is_forall (concl th) && vfree_in `b:int32` (concl th))
          th in
       ASSUME_TAC (MP (SPEC `i:num` th') (ASSUME `i < 256`))) THEN
    RISCV_VSTEPS_TAC MLDSA_POINTWISE_MONTGOMERY_EXEC (1--7) THEN
    RISCV_STEP_TAC MLDSA_POINTWISE_MONTGOMERY_EXEC [] "s8" None
     (fun th -> LABEL_TAC "store_update" th THEN STRIP_TAC) THEN
    SUBGOAL_THEN
     `!j. j < 256
          ==> read
               (memory :>
                bytes32 (word_add a (word (4 * j)))) s8 =
              if j < i + 1 then
                mldsa_montmul
                  (word_sx (y j:int32),
                   word_sx
                    (word_mul (y j:int32) (word 58728449)))
                  (x j:int32)
              else (x j:int32)`
    ASSUME_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
      ASM_CASES_TAC `j:num = i` THEN
      ASM_REWRITE_TAC[RV32_MLDSA_MONTMUL] THEN
      USE_THEN "store_update"
       (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
      CONV_TAC(ONCE_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      TRANS_TAC EQ_TRANS
       `read
         (memory :>
          bytes32 (word_add a (word (4 * j)))) s7` THEN
      CONJ_TAC THENL
       [READ_OVER_WRITE_TAC;
        FIRST_ASSUM
         (fun th ->
           let th' =
             check
              (fun th ->
                is_forall (concl th) &&
                vfree_in `a:int32` (concl th) &&
                vfree_in `s7:riscvstate` (concl th))
              th in
           ACCEPT_TAC
            (MP (SPEC `j:num` th') (ASSUME `j < 256`)))];
      ALL_TAC] THEN
    DISCARD_OLDSTATE_TAC "s8" THEN
    RISCV_STEPS_TAC MLDSA_POINTWISE_MONTGOMERY_EXEC (9--10) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[RV32_MLDSA_MONTMUL] THEN
    CONJ_TAC THEN CONV_TAC WORD_RULE;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    RISCV_STEPS_TAC MLDSA_POINTWISE_MONTGOMERY_EXEC [1] THEN
    SUBGOAL_THEN
     `~((4 * i) MOD 4294967296 = 1024)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `4 * i < 4294967296` ASSUME_TAC THENL
       [UNDISCH_TAC `i:num < 256` THEN ARITH_TAC;
        ASM_REWRITE_TAC[MOD_LT] THEN
        UNDISCH_TAC `i:num < 256` THEN ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~(word_add a (word (4 * i)):int32 =
        word_add a (word 1024))`
    ASSUME_TAC THENL
     [REWRITE_TAC[
        WORD_RULE
         `word_add a (word x):int32 = word_add a (word y) <=>
          (word x:int32) = word y`;
        WORD_EQ; DIMINDEX_32; CONG] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN
    RISCV_STEPS_TAC MLDSA_POINTWISE_MONTGOMERY_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[]]);;

let INT_ABS_LT_BOUNDS = prove
 (`!x k:int.
      &0 < k ==> (abs x < k <=> --k < x /\ x < k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&0:int`; `x:int`; `k:int`] INT_ABS_BETWEEN) THEN
  ASM_REWRITE_TAC[INT_SUB_RZERO; INT_SUB_LZERO; INT_ADD_LID] THEN
  MESON_TAC[]);;

let INT_ABS_LT_8380417 = prove
 (`!x:int.
      abs x < &8380417 <=> -- &8380417 < x /\ x < &8380417`,
  GEN_TAC THEN MATCH_MP_TAC INT_ABS_LT_BOUNDS THEN INT_ARITH_TAC);;

let RV32_MLDSA_MONTMUL_CORRECT = prove
 (`!x y:int32.
      abs(ival x) < &94279698 /\
      abs(ival y) < &94279698
      ==> (ival(mldsa_montmul
             (word_sx y,
              word_sx (word_mul y (word 58728449))) x) ==
           ival x * ival y *
           &(inverse_mod 8380417 4294967296))
          (mod &8380417) /\
          abs(ival(mldsa_montmul
            (word_sx y,
             word_sx (word_mul y (word 58728449))) x)) <
          &8380417`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
   (SPECL
     [`x:int32`; `ival(x:int32)`;
      `-- &94279697:int`; `&94279697:int`]
     CONGBOUND_MLDSA_MONTMUL_RUNTIME) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INTEGER_RULE `(z:int == z) (mod n)`] THEN
    REWRITE_TAC[INT_ABS_BOUNDS; INT_LT_DISCRETE] THEN
    ASM_INT_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `y:int32`)] THEN
  DISCH_THEN
   (CONJUNCTS_THEN2 (LABEL_TAC "congruence") STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
   [USE_THEN "congruence" MP_TAC THEN
    REWRITE_TAC[INT_MUL_AC];
    REWRITE_TAC[INT_ABS_LT_8380417] THEN
    SUBGOAL_THEN
     `-- &8888661266411809 <=
      min
       (ival(y:int32) * -- &94279697)
       (ival(y:int32) * &94279697) /\
      max
       (ival(y:int32) * -- &94279697)
       (ival(y:int32) * &94279697) <=
      &8888661266411809`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[INT_LE_MIN; INT_MAX_LE] THEN
      REWRITE_TAC[INT_ABS_BOUNDS; INT_LT_DISCRETE] THEN
      ASM_INT_ARITH_TAC;
      CONJ_TAC THENL
       [MATCH_MP_TAC INT_LTE_TRANS THEN
        EXISTS_TAC
         `(min
            (ival(y:int32) * -- &94279697)
            (ival(y:int32) * &94279697) -
           &17996808462540799) div &4294967296` THEN
        ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[INT_LT_DIV_EQ] THEN
        ASM_INT_ARITH_TAC;
        MATCH_MP_TAC INT_LET_TRANS THEN
        EXISTS_TAC
         `(max
            (ival(y:int32) * -- &94279697)
            (ival(y:int32) * &94279697) +
           &17996812765888511) div &2 pow 32` THEN
        ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[INT_DIV_LT_EQ; INT_OF_NUM_POW] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        ASM_INT_ARITH_TAC]]]);;

let MLDSA_POINTWISE_MONTGOMERY_CORE_CORRECT = prove
 (`!a b:int32. !x y:num->int32. !pc:num.
    aligned 4 a /\
    aligned 4 b /\
    nonoverlapping
      ((word pc):int32,LENGTH mldsa_pointwise_montgomery_mc)
      (a,1024) /\
    nonoverlapping (a,1024) (b,1024)
    ==> ensures riscv
      (\s. aligned_bytes_loaded s (word pc)
             mldsa_pointwise_montgomery_mc /\
           read PC s = word (pc + 12) /\
           C_ARGUMENTS [a;b] s /\
           (!i. i < 256 ==> abs(ival(x i)) < &94279698) /\
           (!i. i < 256 ==> abs(ival(y i)) < &94279698) /\
           (!i. i < 256
                ==> read
                     (memory :>
                      bytes32 (word_add a (word (4 * i)))) s =
                    x i) /\
           (!i. i < 256
                ==> read
                     (memory :>
                      bytes32 (word_add b (word (4 * i)))) s =
                    y i))
      (\s. read PC s = word (pc + 76) /\
           !i. i < 256
               ==> let zi =
                     read
                      (memory :>
                       bytes32 (word_add a (word (4 * i)))) s in
                   (ival zi ==
                    mldsa_pointwise (ival o x) (ival o y) i)
                   (mod &8380417) /\
                   abs(ival zi) < &8380417)
      (MAYCHANGE
        [PC; S0; S1; T0; A0; A1; A2; A3; A4; A5; A6; A7] ,,
       MAYCHANGE [memory :> bytes(a,1024)] ,,
       MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`a:int32`; `b:int32`; `x:num->int32`; `y:num->int32`; `pc:num`] THEN
  REPEAT STRIP_TAC THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  MP_TAC
   (SPECL
     [`a:int32`; `b:int32`; `x:num->int32`; `y:num->int32`; `pc:num`]
     MLDSA_POINTWISE_MONTGOMERY_CORE_EXACT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_POSTCONDITION_THM) THEN
  REWRITE_TAC[] THEN
  X_GEN_TAC `s:riscvstate` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "outputs")) THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  USE_THEN "outputs"
   (fun th ->
     ASSUME_TAC
      (MP (SPEC `i:num` th) (ASSUME `i < 256`))) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[o_THM; mldsa_pointwise] THEN
  CONV_TAC let_CONV THEN
  MP_TAC
   (SPECL [`(x:num->int32) i`; `(y:num->int32) i`]
     RV32_MLDSA_MONTMUL_CORRECT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[INT_CONG_RREM; INT_MUL_AC]);;

let MLDSA_POINTWISE_MONTGOMERY_SUBROUTINE_CORRECT = prove
 (`!a b:int32. !x y:num->int32. !pc:num.
    !stackpointer returnaddress:int32.
    aligned 4 a /\
    aligned 4 b /\
    aligned 16 stackpointer /\
    aligned 4 returnaddress /\
    ALLPAIRS nonoverlapping
      [(a,1024); (word_sub stackpointer (word 16),16)]
      [((word pc):int32,LENGTH mldsa_pointwise_montgomery_mc);
       (b,1024)] /\
    nonoverlapping
      (a,1024)
      (word_sub stackpointer (word 16),16)
    ==> ensures riscv
      (\s. aligned_bytes_loaded s (word pc)
             mldsa_pointwise_montgomery_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read RA s = returnaddress /\
           C_ARGUMENTS [a;b] s /\
           (!i. i < 256 ==> abs(ival(x i)) < &94279698) /\
           (!i. i < 256 ==> abs(ival(y i)) < &94279698) /\
           (!i. i < 256
                ==> read
                     (memory :>
                      bytes32 (word_add a (word (4 * i)))) s =
                    x i) /\
           (!i. i < 256
                ==> read
                     (memory :>
                      bytes32 (word_add b (word (4 * i)))) s =
                    y i))
      (\s. read PC s = returnaddress /\
           read SP s = stackpointer /\
           !i. i < 256
               ==> let zi =
                     read
                      (memory :>
                       bytes32 (word_add a (word (4 * i)))) s in
                   (ival zi ==
                    mldsa_pointwise (ival o x) (ival o y) i)
                   (mod &8380417) /\
                   abs(ival zi) < &8380417)
      (MAYCHANGE_REGS_PERMITTED_BY_ABI ,,
       MAYCHANGE
        [memory :> bytes(a,1024);
         memory :>
          bytes(word_sub stackpointer (word 16),16)])`,
  REWRITE_TAC[fst MLDSA_POINTWISE_MONTGOMERY_EXEC] THEN
  RISCV_ADD_RETURN_STACK_TAC
    MLDSA_POINTWISE_MONTGOMERY_EXEC
    (REWRITE_RULE[fst MLDSA_POINTWISE_MONTGOMERY_EXEC]
      MLDSA_POINTWISE_MONTGOMERY_CORE_CORRECT)
    `[S0; S1]` 16);;
