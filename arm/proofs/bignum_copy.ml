(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Copying (with truncation or extension) bignums                            *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_copy.o";;
 ****)

let bignum_copy_mc =
  define_assert_from_elf "bignum_copy_mc" "arm/generic/bignum_copy.o"
[
  0xeb02001f;       (* arm_CMP X0 X2 *)
  0x9a823002;       (* arm_CSEL X2 X0 X2 Condition_CC *)
  0xd2800004;       (* arm_MOV X4 (rvalue (word 0)) *)
  0xb40000c2;       (* arm_CBZ X2 (word 24) *)
  0xf8647865;       (* arm_LDR X5 X3 (Shiftreg_Offset X4 3) *)
  0xf8247825;       (* arm_STR X5 X1 (Shiftreg_Offset X4 3) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xeb02009f;       (* arm_CMP X4 X2 *)
  0x54ffff83;       (* arm_BCC (word 2097136) *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x540000a2;       (* arm_BCS (word 20) *)
  0xf824783f;       (* arm_STR XZR X1 (Shiftreg_Offset X4 3) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x54ffffa3;       (* arm_BCC (word 2097140) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_COPY_EXEC = ARM_MK_EXEC_RULE bignum_copy_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_COPY_CORRECT = prove
 (`!k z n x a pc.
     nonoverlapping (word pc,0x40) (z,8 * val k) /\
     (x = z \/ nonoverlapping (x,8 * MIN (val n) (val k)) (z,8 * val k))
     ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [k; z; n; x] s /\
                bignum_from_memory (x,val n) s = a)
           (\s. read PC s = word (pc + 0x3c) /\
                bignum_from_memory (z,val k) s = lowdigits a (val k))
          (MAYCHANGE [PC; X2; X4; X5] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; fst BIGNUM_COPY_EXEC] THEN
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `n:num` THEN X_GEN_TAC `x:int64` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `pc:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Simulate the initial computation of min(n,k) and then
   *** recast the problem with n' = min(n,k) so we can assume
   *** hereafter that n <= k. This makes life a bit easier since
   *** otherwise n can actually be any number < 2^64 without
   *** violating the preconditions.
   ***)

  ENSURES_SEQUENCE_TAC `pc + 0xc`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = word(MIN n k) /\
        read X3 s = x /\
        read X4 s = word 0 /\
        bignum_from_memory (x,MIN n k) s = lowdigits a k` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
    ARM_SIM_TAC BIGNUM_COPY_EXEC (1--3) THEN
    REWRITE_TAC[ARITH_RULE `MIN n k = if k < n then k else n`] THEN
    MESON_TAC[];
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (vfree_in `k:num` o concl))) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN MP_TAC(ARITH_RULE `MIN n k <= k`) THEN
    SPEC_TAC(`lowdigits a k`,`a:num`) THEN SPEC_TAC(`MIN n k`,`n:num`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    VAL_INT64_TAC `n:num` THEN BIGNUM_RANGE_TAC "n" "a"] THEN

  (*** Break at the start of the padding stage ***)

  ENSURES_SEQUENCE_TAC `pc + 0x24`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X4 s = word n /\
        bignum_from_memory(z,n) s = a` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `n = 0` THENL
     [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      REWRITE_TAC[MESON[] `0 = a <=> a = 0`] THEN
      ARM_SIM_TAC BIGNUM_COPY_EXEC [1];
      ALL_TAC] THEN

    FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
      NONOVERLAPPING_IMP_SMALL_2)) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN

    (*** The main copying loop, in the case when n is nonzero ***)

    ENSURES_WHILE_UP_TAC `n:num` `pc + 0x10` `pc + 0x1c`
     `\i s. read X0 s = word k /\
            read X1 s = z /\
            read X2 s = word n /\
            read X3 s = x /\
            read X4 s = word i /\
            bignum_from_memory(z,i) s = lowdigits a i /\
            bignum_from_memory(word_add x (word(8 * i)),n - i) s =
            highdigits a i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ARM_SIM_TAC BIGNUM_COPY_EXEC [1]  THEN
      REWRITE_TAC[SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; MULT_CLAUSES; WORD_ADD_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_0];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      ARM_SIM_TAC BIGNUM_COPY_EXEC (1--3) THEN
      ASM_REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_BIGDIGIT] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC BIGNUM_COPY_EXEC (1--2);
      ARM_SIM_TAC BIGNUM_COPY_EXEC (1--2) THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF]];
    ALL_TAC] THEN

  (*** Degenerate case of no padding (initial k <= n) ***)

  FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC o
    MATCH_MP (ARITH_RULE `n:num <= k ==> n = k \/ n < k`))
  THENL [ARM_SIM_TAC BIGNUM_COPY_EXEC (1--2); ALL_TAC] THEN

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
      NONOVERLAPPING_IMP_SMALL_2)) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN

  (*** Main padding loop ***)

  SUBGOAL_THEN `~(k:num <= n)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NOT_LE]; ALL_TAC] THEN

  ENSURES_WHILE_AUP_TAC `n:num` `k:num` `pc + 0x2c` `pc + 0x34`
   `\i s. read X0 s = word k /\
          read X1 s = z /\
          read X4 s = word i /\
          bignum_from_memory(z,i) s = a` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_COPY_EXEC (1--2);
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    ARM_SIM_TAC BIGNUM_COPY_EXEC (1--2) THEN
    REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_COPY_EXEC (1--2);
    ARM_SIM_TAC BIGNUM_COPY_EXEC (1--2)]);;

let BIGNUM_COPY_SUBROUTINE_CORRECT = prove
 (`!k z n x a pc returnaddress.
     nonoverlapping (word pc,0x40) (z,8 * val k) /\
     (x = z \/ nonoverlapping(x,8 * MIN (val n) (val k)) (z,8 * val k))
     ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc  /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [k; z; n; x] s /\
                bignum_from_memory (x,val n) s = a)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,val k) s =  lowdigits a (val k))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_COPY_EXEC BIGNUM_COPY_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let copy_full_spec,copy_public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "bignum_copy" subroutine_signatures)
    BIGNUM_COPY_SUBROUTINE_CORRECT
    BIGNUM_COPY_EXEC;;

(* Helper rewrites resolving the clamped-length CBZ/CSEL selectors. *)

let BIGNUM_COPY_CLAMP = prove
 (`(if k < n then word k else word n):int64 = word(MIN n k)`,
  REWRITE_TAC[ARITH_RULE `MIN n k = if k < n then k else n`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let BIGNUM_COPY_CLAMP0N = prove
 (`!n:num. (if 0 < n then word 0 else word n):int64 = word 0`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT; LE]) THEN ASM_REWRITE_TAC[]);;

let BIGNUM_COPY_CLAMPK0 = prove
 (`(if k < 0 then word k else word 0):int64 = word 0`, REWRITE_TAC[LT]);;

(* The safety proof splits on whether MIN (val n) (val k) is zero; each case
   is proved as its own lemma to avoid sharing the f_events metavariable
   across the branches, then the two are combined. *)

let BIGNUM_COPY_SAFE_MIN0 = prove
 (`exists f_events.
       forall e k z n x pc returnaddress.
           nonoverlapping (word pc,64) (z,8 * val k) /\
           (x = z \/ nonoverlapping (x,8 * MIN (val n) (val k)) (z,8 * val k)) /\
           MIN (val n) (val k) = 0
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [k; z; n; x] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2. read events s = APPEND e2 e /\
                        e2 = f_events x z k n pc returnaddress /\
                        memaccess_inbounds e2 [x,val n * 8; z,val k * 8]
                                              [z,val k * 8])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bignum (z,val k)])`,
  CONCRETIZE_F_EVENTS_TAC
   `\(x:int64) (z:int64) (k:int64) (n:int64) (pc:num) (returnaddress:int64).
      if val k = 0 then f_ev_min0k0 x z k n pc returnaddress
      else APPEND (f_ev_pad_post x z k n pc returnaddress)
             (APPEND (ENUMERATEL (val k) (f_ev_pad_loop x z k n pc returnaddress))
                     (f_ev_pad_pre x z k n pc returnaddress))
      :(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN
  X_GEN_TAC `e:(uarch_event)list` THEN
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `n:num` THEN X_GEN_TAC `x:int64` THEN
  MAP_EVERY X_GEN_TAC [`pc:num`;`returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst BIGNUM_COPY_EXEC; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `8 * k < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [EVERY_ASSUM(fun th -> try MP_TAC (MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
      NONOVERLAPPING_IMP_SMALL_2) th) with Failure _ -> ALL_TAC) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `MIN n k <= k /\ MIN n k <= n` STRIP_ASSUME_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `n:num` BIGNUM_COPY_CLAMP0N) THEN DISCH_TAC THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_COPY_EXEC (1--7) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `n = 0` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(k <= 0)` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0x2c` `pc + 0x3c`
   `\i s. read X0 s = word k /\ read X1 s = z /\ read X4 s = word i /\
          read X30 s = returnaddress` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN ASSUME_TAC BIGNUM_COPY_CLAMPK0 THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_COPY_EXEC (1--6) THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `i:num < k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    VAL_INT64_TAC `i:num` THEN REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_COPY_EXEC (1--4) THEN
    SUBGOAL_THEN `val(word_add (word i) (word 1):int64) = i + 1` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word k:int64) = k` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN
      REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ASM_REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_COPY_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let BIGNUM_COPY_SAFE_MINgt = prove
 (`exists f_events.
       forall e k z n x pc returnaddress.
           nonoverlapping (word pc,64) (z,8 * val k) /\
           (x = z \/ nonoverlapping (x,8 * MIN (val n) (val k)) (z,8 * val k)) /\
           ~(MIN (val n) (val k) = 0)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [k; z; n; x] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2. read events s = APPEND e2 e /\
                        e2 = f_events x z k n pc returnaddress /\
                        memaccess_inbounds e2 [x,val n * 8; z,val k * 8]
                                              [z,val k * 8])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bignum (z,val k)])`,
  CONCRETIZE_F_EVENTS_TAC
   `\(x:int64) (z:int64) (k:int64) (n:int64) (pc:num) (returnaddress:int64).
      APPEND
        (if MIN (val n) (val k) = val k then f_ev_padx0 x z k n pc returnaddress
         else APPEND (f_ev_padx_post x z k n pc returnaddress)
                (APPEND (ENUMERATEL (val k - MIN (val n) (val k)) (f_ev_padx_loop x z k n pc returnaddress))
                        (f_ev_padx_pre x z k n pc returnaddress)))
        (APPEND (f_ev_copy_post x z k n pc returnaddress)
           (APPEND (ENUMERATEL (MIN (val n) (val k)) (f_ev_copy_loop x z k n pc returnaddress))
                   (f_ev_copy_pre x z k n pc returnaddress)))
      :(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN
  X_GEN_TAC `e:(uarch_event)list` THEN
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `n:num` THEN X_GEN_TAC `x:int64` THEN
  MAP_EVERY X_GEN_TAC [`pc:num`;`returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst BIGNUM_COPY_EXEC; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `8 * k < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [EVERY_ASSUM(fun th -> try MP_TAC (MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
      NONOVERLAPPING_IMP_SMALL_2) th) with Failure _ -> ALL_TAC) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `MIN n k <= k /\ MIN n k <= n` STRIP_ASSUME_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `k = 0 ==> MIN n k = 0`]; ALL_TAC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x24`
   `\s. read X0 s = word k /\ read X1 s = z /\ read X4 s = word(MIN n k) /\
        read X30 s = returnaddress` THEN
  CONJ_TAC THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `MIN n k` `pc + 0x10` `pc + 0x24`
     `\i s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word(MIN n k) /\
            read X3 s = x /\ read X4 s = word i /\ read X30 s = returnaddress` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
      ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
        BIGNUM_COPY_EXEC (1--4) THEN
      REWRITE_TAC[BIGNUM_COPY_CLAMP] THEN
      SUBGOAL_THEN `~(val(word(MIN n k):int64) = 0)` ASSUME_TAC THENL
       [IMP_REWRITE_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN ASM_SIMP_TAC[] THEN
        SIMPLE_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
      ALL_TAC;
      ASM_REWRITE_TAC[] THEN
      ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
        BIGNUM_COPY_EXEC [] THEN DISCHARGE_SAFETY_PROPERTY_TAC] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `i:num < MIN n k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    VAL_INT64_TAC `i:num` THEN REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_COPY_EXEC (1--5) THEN
    SUBGOAL_THEN `val(word_add (word i) (word 1):int64) = i + 1` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word(MIN n k):int64) = MIN n k` ASSUME_TAC THENL
     [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN
      REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ASM_CASES_TAC `MIN n k = k` THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `val(word(MIN n k):int64) = MIN n k` ASSUME_TAC THENL
       [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `k <= MIN n k` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
      ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
        BIGNUM_COPY_EXEC (1--3) THEN
      RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(RAND_CONV(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV)))) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `MIN n k < k /\ 0 < k - MIN n k /\ k - MIN n k < 2 EXP 64`
      STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(k <= MIN n k)` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word(MIN n k):int64) = MIN n k` ASSUME_TAC THENL
     [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `k - MIN n k` `pc + 0x2c` `pc + 0x3c`
     `\i s. read X0 s = word k /\ read X1 s = z /\ read X4 s = word(MIN n k + i) /\
            read X30 s = returnaddress` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[SUB_0; ADD_0; ENUMERATEL_APPEND_ZERO] THEN
      ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
        BIGNUM_COPY_EXEC (1--2) THEN
      ASM_REWRITE_TAC[] THEN
      TRY(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
      RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(RAND_CONV(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV)))) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      ALL_TAC;
      ASM_SIMP_TAC[ARITH_RULE `MIN n k <= k ==> MIN n k + (k - MIN n k) = k`] THEN
      ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
        BIGNUM_COPY_EXEC (1--1) THEN
      RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(RAND_CONV(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV)))) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
      DISCHARGE_SAFETY_PROPERTY_TAC] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `MIN n k + i < k /\ i < k - MIN n k` STRIP_ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    VAL_INT64_TAC `MIN n k + i:num` THEN REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_COPY_EXEC (1--4) THEN
    SUBGOAL_THEN `val(word_add (word (MIN n k + i)) (word 1):int64) = MIN n k + i + 1`
      ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word k:int64) = k` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN
      REWRITE_TAC[ARITH_RULE `MIN n k + i + 1 < k <=> i + 1 < k - MIN n k`];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `MIN n k + (i + 1) = (MIN n k + i) + 1`] THEN
      CONV_TAC WORD_RULE; ALL_TAC] THEN
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(RAND_CONV(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV)))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let BIGNUM_COPY_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e k z n x pc returnaddress.
           nonoverlapping (word pc,64) (z,8 * val k) /\
           (x = z \/
            nonoverlapping (x,8 * MIN (val n) (val k)) (z,8 * val k))
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) bignum_copy_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [k; z; n; x] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events x z k n pc returnaddress /\
                         memaccess_inbounds e2 [x,val n * 8; z,val k * 8]
                         [z,val k * 8]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bignum (z,val k)])`,
  ASSERT_CONCL_TAC copy_full_spec THEN
  X_CHOOSE_TAC
    `fm0:int64->int64->int64->int64->num->int64->(uarch_event)list`
    BIGNUM_COPY_SAFE_MIN0 THEN
  X_CHOOSE_TAC
    `fmg:int64->int64->int64->int64->num->int64->(uarch_event)list`
    BIGNUM_COPY_SAFE_MINgt THEN
  EXISTS_TAC
   `\(x:int64) (z:int64) (k:int64) (n:int64) (pc:num) (returnaddress:int64).
      (if MIN (val n) (val k) = 0 then fm0 x z k n pc returnaddress
       else fmg x z k n pc returnaddress):(uarch_event)list` THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`;`k:int64`;`z:int64`;`n:int64`;`x:int64`;
    `pc:num`;`returnaddress:int64`] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `MIN (val(n:int64)) (val(k:int64)) = 0` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;
