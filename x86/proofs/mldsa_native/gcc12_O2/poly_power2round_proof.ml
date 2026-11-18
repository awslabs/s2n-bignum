(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Splitting at 2^13: the proof (see poly_power2round_spec.ml).              *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/poly_power2round_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_scalar.ml";;

(*** The vectors of 2^12 - 1 = 0xfff and of ~(2^13 - 1) = 0xffffe000 in ***)
(*** each lane, from the read-only data                                 ***)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_CONSTANTS =
  map (fun d -> IMAGE_CONST_RULE_FOR mldsa_native_libmldsa_gcc12_O2_mc d 128)
   [layout "mldsa_poly_power2round_const1";
    layout "mldsa_poly_power2round_const2"];;

(*** The values computed in each lane: with y = a + 2^12 - 1, the high ***)
(*** part y >> 13 and the low part a - (y & ~(2^13 - 1))                ***)

let POWER2ROUND_LANES = prove
 (`!x:int32.
     word_ishr (word_add x (word 4095)) 13 = mld_power2round_hi x /\
     word_sub x (word_and (word_add x (word 4095)) (word 4294959104)) =
     mld_power2round_lo x`,
  REWRITE_TAC[mld_power2round_lo; mld_power2round_hi] THEN GEN_TAC THEN
  AP_TERM_TAC THEN SPEC_TAC(`word_add (x:int32) (word 4095)`,`y:int32`) THEN
  BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* The initialization, which loads the two vectors of constants into XMM4    *)
(* and XMM3 (the legacy SSE loads keep the upper halves of YMM4 and YMM3,    *)
(* whose initial values are ghost variables), and the loop body, for both    *)
(* theorems below. The body takes the four coefficients of the input at      *)
(* a + 16 * i (with the fact for the coefficients after them if the input    *)
(* is overwritten), as one 128-bit value, simulates the iteration, with the  *)
(* top halves of YMM3 and YMM4 unknown, splits the two 128-bit stores into   *)
(* 32-bit values again and proves the invariant for i + 1.                   *)
(* ------------------------------------------------------------------------- *)

let POWER2ROUND_INIT_TAC =
  let EXEC = MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_EXEC
  and ths = MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_CONSTANTS in
  GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
  GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
  FULL_INIT_TAC THEN
  IMAGE_RIPREL_TAC (el 0 ths) (layout "mldsa_poly_power2round" + 0x8) THEN
  IMAGE_RIPREL_TAC (el 1 ths) (layout "mldsa_poly_power2round" + 0x10) THEN
  X86_STEPS_TAC EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[XMM3; XMM4; READ_ZEROTOP_128] THEN
  REPEAT(CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let POWER2ROUND_BODY_TAC =
  let EXEC = MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_EXEC in
  let pat_rw = `!j. 4 * i <= j /\ j < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * j)))) s0 =
                        (x:num->int32) j`
  and pat_ro = `!j. j < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * j)))) s0 =
                        (x:num->int32) j`
  and pat_lane0 = `read (memory :> bytes32 (word_add a (word(16 * i)))) s0`
  and pat_al = `aligned 16 (a:int64)`
  and al_tm = `aligned 16 (word_add a (word(16 * i)):int64)`
  and merge_tm = `read (memory :> bytes128 (word_add a (word(16 * i)))) s0`
  and a_tm = `a:int64` in
  let lanes_tac =
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[CHUNK4_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
  FULL_INIT_TAC THEN
  XMM_EXISTSTOP_TAC "top3" `YMM3` THEN
  XMM_EXISTSTOP_TAC "top4" `YMM4` THEN
  W(fun (asl,w) ->
    let vs = mapfilter (fun (_,th) ->
      let v = rand(concl th) in
      if can (term_match [] pat_al) (concl th) && is_var v then v
      else failwith "") asl in
    MAP_EVERY (fun v ->
      SUBGOAL_THEN (subst [v,a_tm] al_tm) ASSUME_TAC THENL
       [MATCH_MP_TAC ALIGNED_WORD_ADD THEN
        ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
        ALL_TAC]) vs) THEN
  W(fun (asl,w) ->
    match filter (can (term_match [] pat_rw) o concl o snd) asl with
      (_,th)::_ ->
        UNDISCH_THEN (concl th) (fun th ->
          MP_TAC(GEN_REWRITE_RULE I
                  [MATCH_MP CHUNK4_INPUT_SPLIT (ASSUME `i < 64`)] th)) THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN lanes_tac
    | [] ->
        let th = snd(find (can (term_match [] pat_ro) o concl o snd) asl) in
        let eqn = rand(snd(dest_forall(concl th))) in
        let t = mk_forall(`k:num`,
                  mk_imp(`k < 4`,subst [`4 * i + k`,`j:num`] eqn)) in
        SUBGOAL_THEN t MP_TAC THENL
         [REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_ARITH_TAC;
          lanes_tac]) THEN
  W(fun (asl,w) ->
    let l = find (can (term_match [] pat_lane0))
                 (mapfilter (lhand o concl o snd) asl) in
    let a = lhand(rand(rand(rand(rator l)))) in
    MP_TAC(READ_MEMORY_MERGE_CONV 2 (subst [a,a_tm] merge_tm))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
  VAL_INT64_TAC `16 * i` THEN INDEX_ADDR_TAC THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC EXEC [n] THEN SIMD_SIMPLIFY_TAC[])
   (1--9) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE(SIMD_SIMPLIFY_CONV []) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
    check (can (term_match [] `read (memory :> bytes128 a) s = x`) o
           concl))) THEN
  X86_STEPS_TAC EXEC (10--12) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
  LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[XMM3; XMM4; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC WORD_BLAST THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CHUNK4_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      REWRITE_TAC[CHUNK4_ADDR; ADD_CLAUSES] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[POWER2ROUND_LANES] THEN
      NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. Each of the 64 iterations   *)
(* of the loop splits 4 coefficients, loaded and stored as 128-bit words;    *)
(* the loop test is the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC     *)
(* requires, and the events of an iteration depend on its index only.        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(a1:int64) (a0:int64) (a:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil a1 a0 a pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 64
            (\i. f_ev_loop a1 a0 a pc stackpointer returnaddress i))
          (f_ev_prol a1 a0 a pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a1:int64`; `a0:int64`; `a:int64`;
    `x:num->int32`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; PAIRWISE; ALL;
              mld_poly_power2round_hi; mld_poly_power2round_lo;
              fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + mldsa_poly_power2round_loop1`
   `pc + mldsa_poly_power2round_loop1_exit`
   `\i s. read RDI s = a1 /\ read RSI s = a0 /\ read RDX s = a /\
          read RAX s = word(16 * i) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress /\
          read XMM3 s = word 0xffffe000ffffe000ffffe000ffffe000 /\
          read XMM4 s = word 0x00000fff00000fff00000fff00000fff /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j) /\
          (!j. j < 4 * i
               ==> read(memory :> bytes32(word_add a1 (word(4 * j)))) s =
                   mld_power2round_hi (x j)) /\
          (!j. j < 4 * i
               ==> read(memory :> bytes32(word_add a0 (word(4 * j)))) s =
                   mld_power2round_lo (x j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, with the vectors of constants from the image ***)

    POWER2ROUND_INIT_TAC;

    (*** The loop body, with the loop test ***)

    POWER2ROUND_BODY_TAC;

    (*** The return ***)

    FULL_EXIT_TAC EXEC 1]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

(* ------------------------------------------------------------------------- *)
(* The same in place: the invariant states the input coefficients from 4 * i *)
(* on and the results before 4 * i at a0.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL_INPLACE =
  prove
 (MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL_INPLACE_STMT,
  let EXEC = MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(a1:int64) (a0:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil a1 a0 pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 64
            (\i. f_ev_loop a1 a0 pc stackpointer returnaddress i))
          (f_ev_prol a1 a0 pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a1:int64`; `a0:int64`;
    `x:num->int32`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; PAIRWISE; ALL;
              mld_poly_power2round_hi; mld_poly_power2round_lo;
              fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + mldsa_poly_power2round_loop1`
   `pc + mldsa_poly_power2round_loop1_exit`
   `\i s. read RDI s = a1 /\ read RSI s = a0 /\ read RDX s = a0 /\
          read RAX s = word(16 * i) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress /\
          read XMM3 s = word 0xffffe000ffffe000ffffe000ffffe000 /\
          read XMM4 s = word 0x00000fff00000fff00000fff00000fff /\
          (!j. 4 * i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add a0 (word(4 * j)))) s =
                   x j) /\
          (!j. j < 4 * i
               ==> read(memory :> bytes32(word_add a1 (word(4 * j)))) s =
                   mld_power2round_hi (x j)) /\
          (!j. j < 4 * i
               ==> read(memory :> bytes32(word_add a0 (word(4 * j)))) s =
                   mld_power2round_lo (x j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, with the vectors of constants from the image ***)

    POWER2ROUND_INIT_TAC;

    (*** The loop body, with the loop test ***)

    POWER2ROUND_BODY_TAC;

    (*** The return ***)

    FULL_EXIT_TAC EXEC 1]);;
