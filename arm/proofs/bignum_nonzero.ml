(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Deduce if a bignum is nonzero.                                            *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_nonzero.o";;
 ****)

let bignum_nonzero_mc = define_assert_from_elf "bignum_nonzero_mc"
  "arm/generic/bignum_nonzero.o"
[
  0xaa1f03e3;       (* arm_MOV X3 XZR *)
  0xb40000e0;       (* arm_CBZ X0 (word 28) *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xf8607822;       (* arm_LDR X2 X1 (Shiftreg_Offset X0 3) *)
  0xaa020063;       (* arm_ORR X3 X3 X2 *)
  0xb5ffffa0;       (* arm_CBNZ X0 (word 2097140) *)
  0xeb1f007f;       (* arm_CMP X3 XZR *)
  0x9a9f07e0;       (* arm_CSET X0 Condition_NE *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_NONZERO_EXEC = ARM_MK_EXEC_RULE bignum_nonzero_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_NONZERO_CORRECT = prove
 (`!k a x pc.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_nonzero_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [k;a] s /\
               bignum_from_memory(a,val k) s = x)
          (\s'. read PC s' = word (pc + 0x20) /\
                C_RETURN s' = if ~(x = 0) then word 1 else word 0)
          (MAYCHANGE [PC; X0; X2; X3] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; fst BIGNUM_NONZERO_EXEC] THEN
  BIGNUM_RANGE_TAC "k" "x" THEN

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    ARM_SIM_TAC BIGNUM_NONZERO_EXEC (1--2);
    ALL_TAC] THEN

  ENSURES_WHILE_DOWN_TAC `k:num` `pc + 0x08` `pc + 0x14`
   `\i s. bignum_from_memory (a,i) s = lowdigits x i /\
          read X1 s = a /\
          read X0 s = word i /\
          (read X3 s = word 0 <=> highdigits x i = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO] THEN
    ARM_SIM_TAC BIGNUM_NONZERO_EXEC (1--2);
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `d:int64` `read X3` THEN ASSUME_TAC
     (WORD_RULE `word_sub (word (i + 1)) (word 1):int64 = word i`) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_LOWDIGITS] THEN
    ARM_SIM_TAC BIGNUM_NONZERO_EXEC (1--3) THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [HIGHDIGITS_STEP] THEN
    ASM_REWRITE_TAC[WORD_OR_EQ_0; ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_0; VAL_WORD_BIGDIGIT; CONJ_ACI];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_NONZERO_EXEC [1];
    GHOST_INTRO_TAC `d:int64` `read X3` THEN
    ARM_SIM_TAC BIGNUM_NONZERO_EXEC (1--3) THEN
    ASM_REWRITE_TAC[VAL_WORD_0; VAL_EQ_0; COND_SWAP; HIGHDIGITS_0]]);;

let BIGNUM_NONZERO_SUBROUTINE_CORRECT = prove
 (`!k a x pc returnaddress.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_nonzero_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [k;a] s /\
               bignum_from_memory(a,val k) s = x)
          (\s'. read PC s' = returnaddress /\
                C_RETURN s' = if ~(x = 0) then word 1 else word 0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_NONZERO_EXEC BIGNUM_NONZERO_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "bignum_nonzero" subroutine_signatures)
    BIGNUM_NONZERO_SUBROUTINE_CORRECT
    BIGNUM_NONZERO_EXEC;;

(* Containment of a word-indexed load a[w] (8 bytes) within [a, n * 8] when the
   index w is below n. *)
let BIGNUM_NONZERO_LOAD_CONTAINED = prove
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

let BIGNUM_NONZERO_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e k a pc returnaddress.
           ensures arm
           (\s.
                aligned_bytes_loaded s (word pc) bignum_nonzero_mc /\
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
           (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (k:int64) (pc:num) (returnaddress:int64).
      if val k = 0 then f_ev_k0 a k pc returnaddress
      else APPEND (f_ev_post a k pc returnaddress)
             (APPEND (ENUMERATEL (val k) (f_ev_loop a k pc returnaddress))
                     (f_ev_pre a k pc returnaddress)):(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `pc:num`] THEN GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  ASM_CASES_TAC `k = 0` THENL
   [ ASM_REWRITE_TAC[] THEN
     ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
       BIGNUM_NONZERO_EXEC (1--3) THEN DISCHARGE_SAFETY_PROPERTY_TAC;
     ALL_TAC ] THEN
  ASM_REWRITE_TAC[ASSUME `val(word k:int64) = k`] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0x8` `pc + 0x18`
   `\i s. read X1 s = a /\ read X0 s = word(k - i) /\ read X30 s = returnaddress` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ (* prologue: MOV; CBZ not taken -> loop head *)
     ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
       BIGNUM_NONZERO_EXEC (1--2) THEN ASM_REWRITE_TAC[SUB_0] THEN
     DISCHARGE_SAFETY_PROPERTY_TAC;

     (* main loop body: SUB; LDR; ORR; CBNZ *)
     ALL_TAC;

     (* epilogue: CMP; CSET; RET *)
     REWRITE_TAC[] THEN
     ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
       BIGNUM_NONZERO_EXEC (1--3) THEN DISCHARGE_SAFETY_PROPERTY_TAC ] THEN
  (* main loop body *)
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
    BIGNUM_NONZERO_EXEC (1--4) THEN
  (* the loop counter word k-i decrements to k-(i+1) *)
  SUBGOAL_THEN `word_sub (word(k - i)) (word 1):int64 = word(k - (i+1))` ASSUME_TAC THENL
   [ IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
      [ AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC ]; ALL_TAC ] THEN
  SUBGOAL_THEN `val(word(k - (i+1)):int64) = k - (i+1)` ASSUME_TAC THENL
   [ MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  (* rewrite the decremented counter to its value form everywhere, so the CBNZ
     branch condition ~(val .. = 0) becomes ~(k - (i+1) = 0) i.e. i+1 < k. *)
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(~(k - (i + 1) = 0)) <=> i + 1 < k` SUBST1_TAC THENL
   [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  (* the counter-update conjunct is now reflexivity; PC target closes by cases *)
  CONJ_TAC THENL [ COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC ] THEN
  (* events + memory safety *)
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  W (fun (asl,w) ->
    (if is_conj w then (CONJ_TAC THENL [ FULL_UNIFY_F_EVENTS_TAC; ALL_TAC ]) else ALL_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  (* Split the top APPEND ONCE (not recursively): the current iteration's
     [jump; load] events, and the accumulated ENUMERATEL prefix + prologue. *)
  GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN CONJ_TAC THENL
   [ (* the iteration's own jump (vacuous) and load *)
     REWRITE_TAC[memaccess_inbounds; ALL; EX; FST; SND] THEN
     MATCH_MP_TAC BIGNUM_NONZERO_LOAD_CONTAINED THEN CONJ_TAC THEN SIMPLE_ARITH_TAC;
     (* accumulated ENUMERATEL prefix + prologue: discharge from the
        strengthened loop-invariant assumption. *)
     DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC ]);;
