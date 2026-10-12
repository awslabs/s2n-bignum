(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplexing for raw bignums with same length.                            *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_mux.o";;
 ****)

let bignum_mux_mc =
  define_assert_from_elf "bignum_mux_mc" "arm/generic/bignum_mux.o"
[
  0xb4000101;       (* arm_CBZ X1 (word 32) *)
  0xf100001f;       (* arm_CMP X0 (rvalue (word 0)) *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0xf8617865;       (* arm_LDR X5 X3 (Shiftreg_Offset X1 3) *)
  0xf8617880;       (* arm_LDR X0 X4 (Shiftreg_Offset X1 3) *)
  0x9a8010a5;       (* arm_CSEL X5 X5 X0 Condition_NE *)
  0xf8217845;       (* arm_STR X5 X2 (Shiftreg_Offset X1 3) *)
  0xb5ffff61;       (* arm_CBNZ X1 (word 2097132) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MUX_EXEC = ARM_MK_EXEC_RULE bignum_mux_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MUX_CORRECT = prove
 (`!b k x y z m n pc.
     nonoverlapping (word pc,0x24) (z,8 * val k) /\
     (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
     (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
     ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mux_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [b; k; z; x; y] s /\
                bignum_from_memory (x,val k) s = m /\
                bignum_from_memory (y,val k) s = n)
           (\s. read PC s =
                word (pc + 0x20) /\
                bignum_from_memory (z,val k) s =
                  if ~(b = word 0) then m else n)
          (MAYCHANGE [PC; X0; X1; X5] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; fst BIGNUM_MUX_EXEC] THEN
  MAP_EVERY W64_GEN_TAC [`b:num`; `k:num`] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (BIGNUM_RANGE_TAC "k") ["m"; "n"] THEN

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; COND_ID] THEN
    ARM_SIM_TAC BIGNUM_MUX_EXEC [1];
    ALL_TAC] THEN

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN

  ENSURES_WHILE_DOWN_TAC `k:num` `pc + 0x8` `pc + 0x1c`
   `\i s. read X3 s = x /\
          read X4 s = y /\
          read X2 s = z /\
          read X1 s = word i /\
          (read ZF s <=> b = 0) /\
          bignum_from_memory(x,i) s = lowdigits m i /\
          bignum_from_memory(y,i) s = lowdigits n i /\
          bignum_from_memory(word_add z (word(8 * i)),k - i) s =
          highdigits (if b = 0 then n else m) i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUB_REFL] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
    ONCE_REWRITE_TAC[COND_RATOR] THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; COND_ID] THEN
    ARM_SIM_TAC BIGNUM_MUX_EXEC (1--2) THEN REWRITE_TAC[VAL_WORD_0];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    MP_TAC(WORD_RULE `word_sub (word (i + 1)) (word 1):int64 = word i`) THEN
    DISCH_TAC THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_LOWDIGITS] THEN
    ARM_SIM_TAC BIGNUM_MUX_EXEC (1--5) THEN
    ONCE_REWRITE_TAC[REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
                        BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN MESON_TAC[];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_MUX_EXEC [1];

    ASM_REWRITE_TAC[HIGHDIGITS_0; MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    ARM_SIM_TAC BIGNUM_MUX_EXEC [1] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ_0; COND_SWAP]]);;

let BIGNUM_MUX_SUBROUTINE_CORRECT = prove
 (`!b k x y z m n pc returnaddress.
     nonoverlapping (word pc,0x24) (z,8 * val k) /\
     (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
     (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
     ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mux_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [b; k; z; x; y] s /\
                bignum_from_memory (x,val k) s = m /\
                bignum_from_memory (y,val k) s = n)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,val k) s =
                  if ~(b = word 0) then m else n)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MUX_EXEC BIGNUM_MUX_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(* The frame of the correctness theorem is kept (keep_maychanges:true), so
   that the safety theorem can be used for callers such as bignum_modexp. *)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "bignum_mux" subroutine_signatures)
    BIGNUM_MUX_SUBROUTINE_CORRECT
    BIGNUM_MUX_EXEC;;

(* The per-iteration store z[k-(i+1)] stays within the output buffer, hence
   disjoint from the (nonoverlapping) code region. *)
let BIGNUM_MUX_STORE_NONOV = prove
 (`!(pc:num) (z:int64) (k:num) (i:num).
     nonoverlapping (word pc,36) (z,8 * k) /\ i < k
     ==> nonoverlapping (word pc,36) (word_add z (word(8 * (k - (i + 1)))),8)`,
  REPEAT STRIP_TAC THEN NONOVERLAPPING_TAC);;

let BIGNUM_MUX_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e b k x y z pc returnaddress.
           nonoverlapping (word pc,36) (z,8 * val k) /\
           (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
           (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) bignum_mux_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [b; k; z; x; y] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events x y z k pc returnaddress /\
                         memaccess_inbounds e2
                         [x,val k * 8; y,val k * 8; z,val k * 8]
                         [z,val k * 8]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bignum (z,val k)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(x:int64) (y:int64) (z:int64) (k:int64) (pc:num) (returnaddress:int64).
      if val k = 0 then (f_ev_k0 x y z k pc returnaddress)
      else
        (APPEND
          (f_ev_loop_post x y z k pc returnaddress)
          (APPEND
            (ENUMERATEL (val k) (f_ev_loop x y z k pc returnaddress))
            (f_ev_loop_pre x y z k pc returnaddress)))
      :(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN
  STRIP_TAC (* event e *) THEN
  MAP_EVERY W64_GEN_TAC [`b:num`; `k:num`] THEN
  MAP_EVERY X_GEN_TAC [`x:int64`; `y:int64`; `z:int64`; `pc:num`] THEN
  GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_MUX_EXEC (1--2) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ASSUME `val(word k:int64) = k`] THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0x8` `pc + 0x20`
   `\i s. read X2 s = z /\
          read X3 s = x /\
          read X4 s = y /\
          read X1 s = word(k - i) /\
          read X30 s = returnaddress` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [
    (* pre *)
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_MUX_EXEC (1--2) THEN
    ASM_REWRITE_TAC[SUB_0] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (* main loop *)
    ALL_TAC;

    (* post *)
    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_MUX_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC
  ] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  (* pre-establish the counter decrement, so the store address canonicalizes to
     z + 8*(k-(i+1)), and the store's nonoverlapping with the code region. *)
  SUBGOAL_THEN `word_sub (word(k - i)) (word 1):int64 = word(k - (i+1))` ASSUME_TAC THENL
   [ IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
      [ AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC ]; ALL_TAC ] THEN
  MP_TAC(ISPECL [`pc:num`; `z:int64`; `k:num`; `i:num`] BIGNUM_MUX_STORE_NONOV) THEN
  ANTS_TAC THENL [ ASM_REWRITE_TAC[]; DISCH_TAC ] THEN
  REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false BIGNUM_MUX_EXEC (1--6) THEN
  SUBGOAL_THEN `val(word(k - (i+1)):int64) = k - (i+1)` ASSUME_TAC THENL
   [ MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(~(k - (i + 1) = 0)) <=> i + 1 < k` SUBST1_TAC THENL
   [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  CONJ_TAC THENL [ COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC ] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
