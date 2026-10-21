(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Counting trailing zero digits in a bignum.                                *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_ctd.o";;
 ****)

let bignum_ctd_mc = define_assert_from_elf "bignum_ctd_mc" "arm/generic/bignum_ctd.o"
[
  0xb4000100;       (* arm_CBZ X0 (word 32) *)
  0xaa0003e2;       (* arm_MOV X2 X0 *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xf8607823;       (* arm_LDR X3 X1 (Shiftreg_Offset X0 3) *)
  0xf100007f;       (* arm_CMP X3 (rvalue (word 0)) *)
  0x9a821002;       (* arm_CSEL X2 X0 X2 Condition_NE *)
  0xb5ffff80;       (* arm_CBNZ X0 (word 2097136) *)
  0xaa0203e0;       (* arm_MOV X0 X2 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_CTD_EXEC = ARM_MK_EXEC_RULE bignum_ctd_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_CTD_CORRECT = prove
 (`!k a x pc.
        ensures arm
         (\s. aligned_bytes_loaded s (word pc) bignum_ctd_mc /\
              read PC s = word pc /\
              C_ARGUMENTS [k;a] s /\
              bignum_from_memory(a,val k) s = x)
         (\s'. read PC s' = word (pc + 0x20) /\
               C_RETURN s' = if x = 0 then k else word(index 2 x DIV 64))
         (MAYCHANGE [PC; X0; X2; X3] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  BIGNUM_RANGE_TAC "k" "x" THEN

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_TAC `x < 2 EXP (64 * k)` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; EXP; ARITH_RULE `x < 1 <=> x = 0`] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CTD_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  ENSURES_WHILE_DOWN_TAC `k:num` `pc + 0x8` `pc + 0x18`
   `\i s. bignum_from_memory (a,k) s = x /\
          read X0 s = word i /\
          read X1 s = a /\
          bignum_from_memory
            (word_add a (word(8 * i)),val(read X2 s) - i) s = 0 /\
          (val(read X2 s) = k \/
           val(read X2 s) < k /\
           ~(bigdigit x (val(read X2 s)) = 0))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CTD_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; SUB_REFL] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL];
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    GHOST_INTRO_TAC `i:int64` `read X2` THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CTD_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
    GHOST_INTRO_TAC `i:num` `\s. val(read X2 s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    VAL_INT64_TAC `i:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CTD_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      COND_CASES_TAC THENL [ASM_REWRITE_TAC[]; ASM_MESON_TAC[]];
      STRIP_TAC] THEN
    ABBREV_TAC `d = bigdigit x i` THEN
    SUBGOAL_THEN `x = 2 EXP (64 * i) * highdigits x i + lowdigits x i`
    SUBST1_TAC THENL [REWRITE_TAC[HIGH_LOW_DIGITS]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[HIGHDIGITS_STEP] THEN
    ASM_REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    EXPAND_TAC "x" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[lowdigits; BIGNUM_FROM_MEMORY_MOD] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < k ==> MIN k i = i`] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[INDEX_MUL; INDEX_EXP; PRIME_2; INDEX_REFL; ARITH_LE;
                 ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ; MULT_CLAUSES] THEN
    AP_TERM_TAC THEN SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `i = i + n DIV 64 <=> n < 64`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) (CONJUNCT1 INDEX_MULT_ADD) o
        lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(ARITH_RULE
     `y < 64 ==> (y < 64 ==> x = y) ==> x < 64`) THEN
    MATCH_MP_TAC INDEX_LT THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "d" THEN REWRITE_TAC[BIGDIGIT_BOUND]] THEN

  X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
  ASSUME_TAC(WORD_RULE `word_sub (word (j + 1)) (word 1):int64 = word j`) THEN
  GHOST_INTRO_TAC `i:num` `\s. val(read X2 s)` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  VAL_INT64_TAC `i:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `read(memory :> bytes64(word_add a (word (8 * j)))) s0 =
    word(bigdigit x j)`
  ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    ASM_REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  ARM_STEPS_TAC BIGNUM_CTD_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_SUB_0; VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  ASM_CASES_TAC `bigdigit x j = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[WORD_EQ_IMP; DIMINDEX_64] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; SUB_REFL] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
  ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
  REWRITE_TAC[SUB_EQ_0] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_add a (word (8 * j))) (word 8) =
    word_add a (word (8 * (j + 1)))`] THEN
  REWRITE_TAC[ARITH_RULE `m - n - 1 = m - (n + 1)`] THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES]);;

let BIGNUM_CTD_SUBROUTINE_CORRECT = prove
 (`!k a x pc returnaddress.
        ensures arm
         (\s. aligned_bytes_loaded s (word pc) bignum_ctd_mc /\
              read PC s = word pc /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [k;a] s /\
              bignum_from_memory(a,val k) s = x)
         (\s'. read PC s' = returnaddress /\
               C_RETURN s' = if x = 0 then k else word(index 2 x DIV 64))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_CTD_EXEC BIGNUM_CTD_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "bignum_ctd" subroutine_signatures)
    BIGNUM_CTD_SUBROUTINE_CORRECT
    BIGNUM_CTD_EXEC;;

(* Containment of a word-indexed load a[w] (8 bytes) within [a, n * 8] when the
   index w is below n. *)
let BIGNUM_CTD_LOAD_CONTAINED = prove
 (`!(a:int64) (n:num) (m:num).
      m < n /\ n < 2 EXP 64
      ==> contained_modulo (2 EXP 64)
            (val(word_add a (word(8 * m))),8) (val a, n * 8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[contained_modulo] THEN
  X_GEN_TAC `d:num` THEN DISCH_TAC THEN EXISTS_TAC `8 * m + d` THEN
  CONJ_TAC THENL
   [ ASM_ARITH_TAC;
     REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN REWRITE_TAC[CONG] THEN
     CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC ]);;

let BIGNUM_CTD_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e k a pc returnaddress.
           ensures arm
           (\s.
                aligned_bytes_loaded s (word pc) bignum_ctd_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [k; a] s /\
                read events s = e)
           (\s.
                read PC s = returnaddress /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a k pc returnaddress /\
                     memaccess_inbounds e2 [a,val k * 8] []))
           MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`,
  ASSERT_CONCL_TAC full_spec THEN
  ARM_SAFETY_SKELETON_TAC ["k"]
   (Cases(`k = 0`,
     Leg("k0",
       ASM_REWRITE_TAC[] THEN
       ARM_SAFETY_SIM_TAC BIGNUM_CTD_EXEC (1--2) THEN DISCHARGE_SAFETY_PROPERTY_TAC),
     Loop(`k:num`, `pc + 0x8`, `pc + 0x1c`,
       `\i s. read X1 s = a /\ read X0 s = word(k - i) /\ read X30 s = returnaddress`,
       Leg("pre",
         (* prologue: CBZ not taken; MOV X2 -> loop head *)
         ARM_SAFETY_SIM_TAC BIGNUM_CTD_EXEC (1--2) THEN ASM_REWRITE_TAC[SUB_0] THEN
         DISCHARGE_SAFETY_PROPERTY_TAC),
       Leg("loop",
         (* main loop body: SUB; LDR; CMP; CSEL; CBNZ *)
         VAL_INT64_TAC `i:num` THEN REWRITE_TAC[] THEN
         ARM_SAFETY_SIM_TAC BIGNUM_CTD_EXEC (1--5) THEN
         (* the loop counter word k-i decrements to k-(i+1) *)
         SUBGOAL_THEN `word_sub (word(k - i)) (word 1):int64 = word(k - (i+1))` ASSUME_TAC THENL
         [ IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
         [ AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC ]; ALL_TAC ] THEN
         SUBGOAL_THEN `val(word(k - (i+1)):int64) = k - (i+1)` ASSUME_TAC THENL
         [ MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
         ASM_REWRITE_TAC[] THEN
         SUBGOAL_THEN `(~(k - (i + 1) = 0)) <=> i + 1 < k` SUBST1_TAC THENL
         [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
         CONJ_TAC THENL [ COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC ] THEN
         SAFE_META_EXISTS_TAC allowed_vars_e THEN
         CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
         W (fun (asl,w) ->
         (if is_conj w then (CONJ_TAC THENL [ FULL_UNIFY_F_EVENTS_TAC; ALL_TAC ]) else ALL_TAC)) THEN
         ASM_REWRITE_TAC[] THEN
         GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN CONJ_TAC THENL
         [ REWRITE_TAC[memaccess_inbounds; ALL; EX; FST; SND] THEN
         MATCH_MP_TAC BIGNUM_CTD_LOAD_CONTAINED THEN CONJ_TAC THEN SIMPLE_ARITH_TAC;
         DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC ]),
       Leg("post",
         (* epilogue: MOV X0; RET *)
         REWRITE_TAC[] THEN
         ARM_SAFETY_SIM_TAC BIGNUM_CTD_EXEC (1--2) THEN DISCHARGE_SAFETY_PROPERTY_TAC)))));;
