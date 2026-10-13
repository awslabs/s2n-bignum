(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Optional negation of bignums.                                             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_optneg.o";;
 ****)

let bignum_optneg_mc =
  define_assert_from_elf "bignum_optneg_mc" "arm/generic/bignum_optneg.o"
[
  0xb40001e0;       (* arm_CBZ X0 (word 60) *)
  0xeb1f005f;       (* arm_CMP X2 XZR *)
  0xda9f03e2;       (* arm_CSETM X2 Condition_NE *)
  0xab02005f;       (* arm_CMN X2 X2 *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xf8656864;       (* arm_LDR X4 X3 (Register_Offset X5) *)
  0xca020084;       (* arm_EOR X4 X4 X2 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xf8256824;       (* arm_STR X4 X1 (Register_Offset X5) *)
  0x910020a5;       (* arm_ADD X5 X5 (rvalue (word 8)) *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xb5ffff40;       (* arm_CBNZ X0 (word 2097128) *)
  0x9a1f03e0;       (* arm_ADC X0 XZR XZR *)
  0xcb0203e2;       (* arm_NEG X2 X2 *)
  0xca020000;       (* arm_EOR X0 X0 X2 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_OPTNEG_EXEC = ARM_MK_EXEC_RULE bignum_optneg_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_OPTNEG_CORRECT = prove
 (`!k z p x a pc.
       nonoverlapping (word pc,0x40) (z,8 * val k) /\
       (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k))
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_optneg_mc /\
                 read PC s = word pc /\
                 C_ARGUMENTS [k;z;p;x] s /\
                 bignum_from_memory (x,val k) s = a)
            (\s. read PC s = word(pc + 0x3c) /\
                 bignum_from_memory(z,val k) s =
                 (if p = word 0 \/ a = 0 then a else 2 EXP (64 * val k) - a) /\
                 C_RETURN s = word(bitval(~(p = word 0) /\ ~(a = 0))))
            (MAYCHANGE [PC; X0; X2; X4; X5] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `p:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `k:num` `a:num` THEN

  (*** The trivial k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN RULE_ASSUM_TAC
    (REWRITE_RULE[ARITH_RULE `a < 2 EXP (64 * 0) <=> a = 0`]) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_OPTNEG_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    REWRITE_TAC[BITVAL_CLAUSES];
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Main loop setup ***)

  ABBREV_TAC `m <=> ~(p:int64 = word 0)` THEN

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x14` `pc + 0x2c`
   `\i s. read X1 s = z /\
          read X3 s = x /\
          read X2 s = word_neg(word(bitval m)) /\
          read X0 s = word(k - i) /\
          read X5 s = word(8 * i) /\
          bignum_from_memory (word_add x (word(8 * i)),k - i) s =
          highdigits a i /\
          2 EXP (64 * i) * bitval(read CF s) + bignum_from_memory(z,i) s =
          (if p:int64 = word 0 then lowdigits a i
           else 2 EXP (64 * i) - lowdigits a i)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_OPTNEG_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; ADD_CLAUSES; MULT_CLAUSES;
                SUB_0; BITVAL_CLAUSES; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[WORD_SUB_0; VAL_EQ_0; bitval; COND_SWAP] THEN
    ASM_REWRITE_TAC[GSYM MSB_IVAL; DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
    ASM_CASES_TAC `p:int64 = word 0` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `k - i:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_OPTNEG_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_OPTNEG_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; WORD_SUB_LZERO; WORD_NEG_NEG] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o rand o concl)) THEN
    UNDISCH_THEN `~(p:int64 = word 0) <=> m` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; WORD_XOR_CONDITIONS] THEN DISCH_THEN(fun th ->
     MP_TAC(AP_TERM `\x. x DIV 2 EXP (64 * k)` th) THEN
     MP_TAC(AP_TERM `\x. x MOD 2 EXP (64 * k)` th)) THEN
    SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_SIMP_TAC[DIV_LT; MOD_LT; BIGNUM_FROM_MEMORY_BOUND; ADD_CLAUSES] THEN
    ASM_CASES_TAC `p:int64 = word 0` THEN
    ASM_SIMP_TAC[BITVAL_CLAUSES; MOD_LT; DIV_LT] THEN
    ASM_CASES_TAC `a = 0` THEN
    ASM_SIMP_TAC[SUB_0; BITVAL_CLAUSES; BITVAL_EQ_1; BITVAL_EQ_0;
                 DIV_LT; MOD_LT; DIV_REFL; MOD_REFL; EXP_EQ_0; ARITH_EQ;
                 ARITH_RULE `~(m = 0) /\ ~(n = 0) ==> m - n < m`]] THEN

  (*** Proof of the main invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  SUBGOAL_THEN `i:num < k` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  GHOST_INTRO_TAC `cin:bool` `read CF` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_ACCSTEPS_TAC BIGNUM_OPTNEG_EXEC [3] (1--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `k - (i + 1) = k - i - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= k - i <=> i < k`];
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o rand o concl)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; LOWDIGITS_BOUND; LT_IMP_LE] THEN
  REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_POW_ADD] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `c + s:real = x ==> s = x - c`)) THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[WORD_XOR_MASK] THEN
  UNDISCH_THEN `~(p:int64 = word 0) <=> m` (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM REAL_OF_NUM_CLAUSES] THEN
  ASM_CASES_TAC `p:int64 = word 0` THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64;
               REAL_VAL_WORD_NOT] THEN
  REAL_ARITH_TAC);;

let BIGNUM_OPTNEG_SUBROUTINE_CORRECT = prove
 (`!k z p x a pc returnaddress.
       nonoverlapping (word pc,0x40) (z,8 * val k) /\
       (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k))
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_optneg_mc /\
                 read PC s = word pc /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [k;z;p;x] s /\
                 bignum_from_memory (x,val k) s = a)
            (\s. read PC s = returnaddress /\
                 bignum_from_memory(z,val k) s =
                 (if p = word 0 \/ a = 0 then a else 2 EXP (64 * val k) - a) /\
                 C_RETURN s = word(bitval(~(p = word 0) /\ ~(a = 0))))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_OPTNEG_EXEC BIGNUM_OPTNEG_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "bignum_optneg" subroutine_signatures)
    BIGNUM_OPTNEG_SUBROUTINE_CORRECT
    BIGNUM_OPTNEG_EXEC;;

let BIGNUM_OPTNEG_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e k z p x pc returnaddress.
           nonoverlapping (word pc,64) (z,8 * val k) /\
           (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k))
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) bignum_optneg_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [k; z; p; x] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events x z k pc returnaddress /\
                         memaccess_inbounds e2 [x,val k * 8; z,val k * 8]
                         [z,val k * 8]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bignum (z,val k)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(x:int64) (z:int64) (k:int64) (pc:num) (returnaddress:int64).
      if val k = 0 then (f_ev_k0 x z k pc returnaddress)
      else
        (APPEND
          (f_ev_loop_post x z k pc returnaddress)
          (APPEND
            (ENUMERATEL (val k) (f_ev_loop x z k pc returnaddress))
            (f_ev_loop_pre x z k pc returnaddress)))
      :(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN
  STRIP_TAC (* event e *) THEN
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `b:int64`; `x:int64`; `pc:num`] THEN
  GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `k = 0` THENL
   [ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_OPTNEG_EXEC (1--2) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN

  (*** Main loop setup ***)

  ABBREV_TAC `p <=> ~(b:int64 = word 0)` THEN
  ASM_REWRITE_TAC[] THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0x14` `pc + 0x30`
   `\i s. read X1 s = z /\
          read X3 s = x /\
          read X2 s = word_neg(word(bitval p)) /\
          read X0 s = word(k - i) /\
          read X5 s = word (8 * i) /\
          read X30 s = returnaddress` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [
    (* pre *)
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_OPTNEG_EXEC (1--5) THEN
    ASM_REWRITE_TAC[SUB_0;MULT_0;WORD_SUB_0] THEN
    CONJ_TAC THENL [REWRITE_TAC[WORD_MASK] THEN EXPAND_TAC "p" THEN
      BITBLAST_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (* main loop *)
    ALL_TAC;

    (* post *)
    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_OPTNEG_EXEC (1--4) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC
  ] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false BIGNUM_OPTNEG_EXEC (1--7) THEN
  (* PC-target closes by cases on i+1<k *)
  SUBGOAL_THEN `(~(val(word_sub (word(k-i)) (word 1):int64) = 0)) <=> i + 1 < k`
    SUBST1_TAC THENL
   [ REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN IMP_REWRITE_TAC[VAL_WORD_EQ;DIMINDEX_64] THEN
     SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  CONJ_TAC THENL [ COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC ] THEN
  (* counter decrement *)
  CONJ_TAC THENL [ IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
    [ AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC ]; ALL_TAC ] THEN
  (* byte offset update *)
  CONJ_TAC THENL [ CONV_TAC WORD_RULE; ALL_TAC ] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
