(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_Os/poly_decompress_d5_spec.ml";;

let D5_BYTES = prove
 (D5_BYTES_STMT,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `160`; `n:num`; `5 * i + j`; `s:armstate`]
                READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`] THEN
  REWRITE_TAC[ARITH_RULE `8 * (5 * i + j) = 40 * i + 8 * j`]);;

let D5D_FIELD = prove
 (D5D_FIELD_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 5 5 = 5`] THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `k < 8 ==> 5 * k + 5 <= 40`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `32 = 2 EXP 5`] THEN
  REWRITE_TAC[ARITH_RULE `40 * i + 5 * k = 5 * (8 * i + k)`]);;

let FORALL_WORD5 = prove
 (FORALL_WORD5_STMT,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `val(g:5 word)`) THEN
  REWRITE_TAC[WORD_VAL] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPEC `g:5 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let DEC_D5_INDEX_TAC k =
  let jt = if k = 0 then `8 * i` else
           mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k) in
  let wt = mk_comb(`word:num->int64`,jt) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read X7 s = x`) c then
      MP_TAC th THEN SUBGOAL_THEN (mk_eq(rand c,wt)) SUBST1_TAC THENL
       [WORD_SMALL_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,wt),jt)) ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        ALL_TAC]
    else failwith "DEC_D5_INDEX_TAC");;

let DEC_D5_ADDRESS_TAC =
  MAP_EVERY (fun k ->
    SUBGOAL_THEN
     (subst [mk_small_numeral k,`k:num`;
             mk_small_numeral(16 + k),`m:num`]
       `word_add (word k) (word (val (word_add stackpointer (word 16)))):int64 =
        word_add stackpointer (word m)`)
     ASSUME_TAC THENL
      [REWRITE_TAC[WORD_VAL] THEN CONV_TAC WORD_RULE; ALL_TAC]) (0--7);;

(*** The 5-bit values in the buffer on the stack, in terms of the 40 bits ***)

let DEC_D5_CLEAN_TAC k =
  let addr = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                     mk_comb(`word:num->int64`,mk_small_numeral(16 + k))) in
  let pat = vsubst [addr,`addr:int64`] `read (memory :> bytes8 addr) s = x` in
  let target = mk_comb(`word_zx:5 word->byte`,
    mk_comb(mk_comb(`word_subword:40 word->num#num->5 word`,`w:40 word`),
            mk_pair(mk_small_numeral(5 * k),`5`))) in
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] pat) (concl th)
    then ASSUME_TAC(TRANS th (BITBLAST_RULE(mk_eq(rand(concl th),target))))
    else failwith "DEC_D5_CLEAN_TAC");;

(*** The value stored for the coefficient from the 5-bit field k of w ***)

let dec_d5_lemmas = ref ([]:(term * thm) list);;

let DEC_D5_VALUE_TAC k =
  let fk = mk_comb(mk_comb(`word_subword:40 word->num#num->5 word`,`w:40 word`),
                   mk_pair(mk_small_numeral(5 * k),`5`)) in
  W(fun (asl,w) ->
    let l,r = dest_eq w in
    let g = genvar `:5 word` in
    let l' = subst [g,fk] l in
    let gl = mk_forall(g,
      mk_eq(l',mk_comb(`word:num->int16`,
                       vsubst [g,`g:5 word`]
                        `(3329 * val(g:5 word) + 16) DIV 32`))) in
    let lth =
      try snd(find (fun (t,_) -> aconv t (concl(ASSUME gl))) !dec_d5_lemmas)
      with Failure _ ->
        let th = prove(gl,
      MATCH_MP_TAC FORALL_WORD5 THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV))) in
        (dec_d5_lemmas := (gl,th) :: !dec_d5_lemmas; th) in
    let fth =
      REWRITE_RULE[ASSUME `word(n DIV 2 EXP (40 * i)) = (w:40 word)`;
                   ADD_CLAUSES]
       (CONV_RULE(DEPTH_CONV NUM_MULT_CONV)
        (MP (SPECL [`n:num`; `i:num`; mk_small_numeral k] D5D_FIELD)
            (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                          (mk_small_numeral k) `8`))))) in
    GEN_REWRITE_TAC LAND_CONV [SPEC fk lth] THEN
    REWRITE_TAC[fth] THEN CONV_TAC NUM_REDUCE_CONV);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `n:num`; `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN

  (*** The outer loop, over groups of 5 bytes and 8 coefficients ***)

  ENSURES_WHILE_UP_TAC `32` `pc + mlkem_poly_decompress_d5_loop1`
   `pc + mlkem_poly_decompress_d5_loop1_test`
   `\i s. read X0 s = r /\
          read X1 s = word_add a (word(5 * i)) /\
          read X4 s = word(8 * i) /\
          read X5 s = word_add stackpointer (word 16) /\
          read X6 s = word 3329 /\
          read SP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
          canary /\
          read (memory :> bytes64 (word_add (word pc) (word 131064))) s =
          guard /\
          read (memory :> bytes64 guard) s = canary /\
          read (memory :> bytes(a,160)) s = n /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((3329 * (n DIV 2 EXP (5 * j)) MOD 2 EXP 5 + 16)
                        DIV 32))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, saving the return address and the stack guard ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC (2--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; CONJUNCT1 LT];

    (*** The loop body, for five bytes and eight coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun j ->
      MP_TAC(REWRITE_RULE[ADD_CLAUSES]
       (CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
         (SPECL [`a:int64`; `n:num`; `i:num`; `s0:armstate`;
                 mk_small_numeral j] D5_BYTES))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC) (0--4) THEN
    ABBREV_TAC `w:40 word = word(n DIV 2 EXP (40 * i))` THEN
    DEC_D5_ADDRESS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC (1--30) THEN
    MAP_EVERY DEC_D5_CLEAN_TAC (0--7) THEN
    MAP_EVERY (fun k ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC
       [30 + 9 * k + 1; 30 + 9 * k + 2] THEN
      DEC_D5_INDEX_TAC k THEN
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC
       ((30 + 9 * k + 3)--(30 + 9 * k + 9))) (0--7) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC (103--104) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN WORD_SMALL_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE
     `j < 8 * (i + 1) <=>
      j < 8 * i \/ j = 8 * i \/ j = 8 * i + 1 \/ j = 8 * i + 2 \/
      j = 8 * i + 3 \/ j = 8 * i + 4 \/ j = 8 * i + 5 \/ j = 8 * i + 6 \/
      j = 8 * i + 7`] THEN
    REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
                FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL (map DEC_D5_VALUE_TAC (0--7));

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit, the check of the stack guard and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC (2--3) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC (4--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (guard:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil a r guard pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 32
            (\i. f_ev_loop a r guard pc stackpointer returnaddress i))
          (f_ev_prol a r guard pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS; PAIRWISE;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem_poly_decompress_d5_loop1`
   `pc + mlkem_poly_decompress_d5_loop1_exit`
    `\i s. read X0 s = r /\
           read X1 s = word_add a (word(5 * i)) /\
           read X4 s = word(8 * i) /\
           read X5 s = word_add stackpointer (word 16) /\
           read X6 s = word 3329 /\
           read SP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           read (memory :> bytes64 (word_add stackpointer (word 24))) s =
           canary /\
           read (memory :> bytes64 (word_add (word pc) (word 131064))) s =
           guard /\
           read (memory :> bytes64 guard) s = canary` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC (2--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC (2--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  DEC_D5_ADDRESS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC (1--30) THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC
     [30 + 9 * k + 1; 30 + 9 * k + 2] THEN
    DEC_D5_INDEX_TAC k THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC
     ((30 + 9 * k + 3)--(30 + 9 * k + 9))) (0--7) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC (103--106) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(val(word_sub
           (word_zx (word_zx (word_add (word_zx (word (8 * i):int64):int32)
                                       (word 8)):int64):int32)
           (word 256):int32) = 0) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
                DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 ==> 8 * i < 18446744073709551616 /\ 8 * i < 4294967296 /\
                 8 * i + 8 < 4294967296 /\
                 8 * i + 8 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN WORD_SMALL_TAC;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
