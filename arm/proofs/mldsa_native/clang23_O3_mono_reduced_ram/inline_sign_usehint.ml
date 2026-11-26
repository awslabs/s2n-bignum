(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemma for the loop of poly_use_hint that clang 23 -O3 has inlined     *)
(* into mldsa44_verify_internal (see inline_sign.ml for the conventions).    *)
(* One coefficient per iteration, in place: a[i] := use_hint(a[i], h[i]),    *)
(* with three paths (hint zero; low part positive; otherwise), entered at    *)
(* the loads (the back branch is B.EQ at the end of the stores), and the     *)
(* exit is at a place that is not in the range of the loop's code, so the    *)
(* EXEC theorem covers the code of the loop only.                            *)
(*                                                                           *)
(*   X24 = a, X27 = h, X8 = 4 * i, constants w14 = 11275, w15 = 2^23,        *)
(*   w16 = 43, w17 = -2 * gamma2, w18 = (q - 1) / 2, w13 = -q.               *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_arith.ml";;
needs "arm/proofs/utils/mldsa_native_scalar.ml";;

let INLINE_USEHINT44_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [(layout "mldsa44_verify_internal_in_poly_use_hint",
     layout "mldsa44_verify_internal_in_poly_use_hint_end")];;

let INLINE_USEHINT44_TERM =
  `exists f_events.
     forall e a h (x:num->int32) (y:num->int32) pc.
       aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
       ALL (nonoverlapping (a,1024)) [(word pc,libmldsa_size); (h,1024)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                 read PC s = word (pc + mldsa44_verify_internal_loop12) /\
                 read X24 s = a /\ read X27 s = h /\ read X8 s = word 0 /\
                 read X14 s = word 11275 /\ read X15 s = word 8388608 /\
                 read X16 s = word 43 /\ read X17 s = word 4294776832 /\
                 read X18 s = word 4190208 /\ read X13 s = word 4286586879 /\
                 (!i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                          x i) /\
                 (!i. i < 256
                      ==> read(memory :> bytes32(word_add h (word(4 * i)))) s =
                          y i) /\
                 read events s = e)
            (\s. read PC s = word (pc + mldsa44_verify_internal_loop12_exit) /\
                 read X8 s = word 1024 /\
                 (!i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                          mld_poly_use_hint_88 x y i) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a h x y pc /\
                    memaccess_inbounds e2 [a,1024; h,1024] [a,1024]))
            (MAYCHANGE [PC; X9; X10; X11; X12; X8] ,, MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,1024)])`;;

(*** The loop test, on the offset after its increment (compared with 1024  ***)
(*** as the sum with 2^64 - 1020)                                          ***)

let INLINE_USEHINT_LOOP_TEST = prove
 (`!i. i < 256
       ==> (val(word_add (word(4 * i))
                         (word 18446744073709550596):int64) = 0 <=>
            ~(i + 1 < 256))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `i = 255` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `4 * i < 1020` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `4 * i < 1020 ==> 4 * i < 18446744073709551616`;
    ARITH_RULE `4 * i < 1020
                ==> 4 * i + 18446744073709550596 < 18446744073709551616`] THEN
  ASM_ARITH_TAC);;

(*** The test of the low part (B.GE after CMP with 1) as a comparison ***)

let INLINE_USEHINT_GE_COND = prove
 (`!w:int32.
     ((ival(word_sub (word_zx (word_zx w:int64):int32) (word 1)) < &0 <=>
       ~(ival(word_zx (word_zx w:int64):int32) - &1 =
         ival(word_sub (word_zx (word_zx w:int64):int32) (word 1))))) <=>
     &0 < ival w`,
  GEN_TAC THEN REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN
  MP_TAC(ISPEC `w:int32` IVAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `ival (w:int32) = --(&2147483648)` THENL
   [SUBGOAL_THEN `w = word 2147483648:int32` SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[GSYM IWORD_IVAL] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV(GSYM WORD_IWORD))) THEN
      CONV_TAC WORD_REDUCE_CONV;
      ALL_TAC] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
    SUBGOAL_THEN `word_sub w (word 1:int32) = iword(ival w - &1)` SUBST1_TAC THENL
     [REWRITE_TAC[WORD_SUB; IWORD_INT_SUB; IWORD_IVAL; WORD_IWORD] THEN
      CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN `ival(iword(ival (w:int32) - &1):int32) = ival w - &1`
      SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[] THEN INT_ARITH_TAC]);;

(*** The end of one of the three paths through an iteration: the stored    ***)
(*** value equal to the spec under the conditions of the path, and the     ***)
(*** branch on the offset back to the loop or out of it.                   ***)

let INLINE_USEHINT_PATH_END_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` INLINE_USEHINT_LOOP_TEST) (ASSUME `i < 256`)]) THEN
  SCALAR_LANE2_TAC `word_add (a:int64) (word(4 * i))` `(x:num->int32) i`
    `(y:num->int32) i` `mld_use_hint_88` [mld_use_hint_88] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  PATH_DISCHARGE_TAC;;

let INLINE_USEHINT44_LOOP =
  let UX = INLINE_USEHINT44_EXEC in
  prove(INLINE_USEHINT44_TERM,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (h:int64) (x:num->int32) (y:num->int32) (pc:num).
      APPEND
        (f_ev_epil a h x y pc)
        (APPEND
          (ENUMERATEL 256
            (\i. if y i = word 0 then f_ev_zero a h x y pc i
                 else if &0 < ival(mld_decompose_lo_88 (x i))
                 then f_ev_pos a h x y pc i
                 else f_ev_neg a h x y pc i))
          (f_ev_prol a h x y pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `h:int64`; `x:num->int32`;
    `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; mld_poly_use_hint_88;
              fst UX] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mldsa44_verify_internal_loop12`
   `pc + mldsa44_verify_internal_loop12_exit`
   `\i s. read X24 s = a /\ read X27 s = h /\ read X8 s = word(4 * i) /\
          read X14 s = word 11275 /\ read X15 s = word 8388608 /\
          read X16 s = word 43 /\ read X17 s = word 4294776832 /\
          read X18 s = word 4190208 /\ read X13 s = word 4286586879 /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s = x j) /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add h (word(4 * j)))) s = y j) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   mld_use_hint_88 (x j) (y j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `mld_use_hint_88` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o C MP (ASSUME `i < 256`) o SPEC `i:num` o
      check (fun th -> is_forall(concl th) &&
        free_in `y:num->int32` (concl th) &&
        not(free_in `mld_use_hint_88` (concl th)))) THEN
    DISCH_TAC THEN
    ARM_STEPS_TAC UX (1--10) THEN
    REG_LANE_TAC `X9` `(x:num->int32) i` `mld_decompose_hi_88`
      [mld_decompose_hi_88; mld_ct_sel] THEN
    ARM_STEPS_TAC UX (11--15) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0]) THEN
    BRANCH_CASES_TAC THENL
     [ARM_STEPS_TAC UX (16--19) THEN INLINE_USEHINT_PATH_END_TAC;
      ARM_STEPS_TAC UX (16--19) THEN
      REG_LANE_TAC `X10` `(x:num->int32) i` `mld_decompose_lo_88`
        [DECOMPOSE_LO_88_ALT; mld_ct_sel] THEN
      ARM_STEPS_TAC UX (20--21) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INLINE_USEHINT_GE_COND]) THEN
      BRANCH_CASES_TAC THENL
       [ARM_STEPS_TAC UX (22--27) THEN INLINE_USEHINT_PATH_END_TAC;
        ARM_STEPS_TAC UX (22--29) THEN INLINE_USEHINT_PATH_END_TAC]];

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
          CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;
