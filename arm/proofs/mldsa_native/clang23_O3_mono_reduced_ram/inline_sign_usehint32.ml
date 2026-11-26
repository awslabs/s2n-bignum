(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The loop of poly_use_hint for gamma2 = (q - 1) / 32 that clang 23 -O3 has *)
(* inlined into mldsa65_verify_internal and mldsa87_verify_internal (see     *)
(* inline_sign_usehint.ml for gamma2 = (q - 1) / 88). One coefficient per    *)
(* iteration, in place: a[i] := use_hint(a[i], h[i]), with three paths (hint *)
(* zero; low part positive; otherwise), entered at the loads; the exit is    *)
(* the target of the B.EQ after the store, outside the range of the loop.    *)
(*                                                                           *)
(*   XA = a, X28 = h, X8 = 4 * i, constants w14 = -q, w15 = -2 * gamma2,     *)
(*   w16 = (q - 1) / 2.                                                      *)
(*                                                                           *)
(* The code computes a1 * 1025 as a1 + (a1 << 10) and a0 = a + a1 * w15 by   *)
(* MADD (DECOMPOSE_LO_32_MADD); the high part for the hint paths is taken    *)
(* again without the mask, which the AND with 15 after the increment or the  *)
(* decrement makes equal to the spec.                                        *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_usehint.ml";;

let DECOMPOSE_LO_32_MADD = prove
 (`!a:int32. mld_decompose_lo_32 a =
     let a0 = word_add a (word_mul (mld_decompose_hi_32 a)
                                   (word 4294443520)) in
     mld_ct_sel (word_sub a0 (word 8380417)) a0
                (mld_ct_cmask_neg (word_sub (word 4190208) a0))`,
  SUBGOAL_THEN
   `!a h:int32. word_sub a (word_mul (word_mul h (word 2)) (word 261888)) =
                word_add a (word_mul h (word 4294443520))`
   (fun th -> REWRITE_TAC[mld_decompose_lo_32; th]) THEN
  REWRITE_TAC[GSYM(WORD_REDUCE_CONV `word_neg(word 523776):int32`)] THEN
  CONV_TAC WORD_RULE);;

(*** The statement for the function fn with the loop head and exit and the ***)
(*** register of a                                                         ***)

let INLINE_USEHINT32_EXEC fn =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [(layout (fn ^ "_in_poly_use_hint"), layout (fn ^ "_in_poly_use_hint_end"))];;

let INLINE_USEHINT32_TERM fn loop xa =
  parse_term(Printf.sprintf
  "exists f_events.
     forall e a h (x:num->int32) (y:num->int32) pc.
       aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
       ALL (nonoverlapping (a,1024)) [(word pc,libmldsa_size); (h,1024)]
       ==> ensures arm
            (\\s. aligned_bytes_loaded s (word pc)
                   mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                 read PC s = word (pc + %s_%s) /\\
                 read %s s = a /\\ read X28 s = h /\\ read X8 s = word 0 /\\
                 read X14 s = word 4286586879 /\\ read X15 s = word 4294443520 /\\
                 read X16 s = word 4190208 /\\
                 (!i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                          x i) /\\
                 (!i. i < 256
                      ==> read(memory :> bytes32(word_add h (word(4 * i)))) s =
                          y i) /\\
                 read events s = e)
            (\\s. read PC s = word (pc + %s_%s_exit) /\\
                 read X8 s = word 1024 /\\
                 (!i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                          mld_poly_use_hint_32 x y i) /\\
                 (exists e2.
                    read events s = APPEND e2 e /\\
                    e2 = f_events a h x y pc /\\
                    memaccess_inbounds e2 [a,1024; h,1024] [a,1024]))
            (MAYCHANGE [PC; X9; X10; X11; X12; X13; X8] ,, MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,1024)])"
  fn loop xa fn loop);;

let INLINE_USEHINT32_PATH_END_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` INLINE_USEHINT_LOOP_TEST) (ASSUME `i < 256`)]) THEN
  SCALAR_LANE2_TAC `word_add (a:int64) (word(4 * i))` `(x:num->int32) i`
    `(y:num->int32) i` `mld_use_hint_32` [mld_use_hint_32; DECOMPOSE_HI_32_ALT] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  PATH_DISCHARGE_TAC;;

let INLINE_USEHINT32_LOOP fn loop xa =
  let UX = INLINE_USEHINT32_EXEC fn in
  let inv = parse_term(Printf.sprintf
   "\\i s. read %s s = a /\\ read X28 s = h /\\ read X8 s = word(4 * i) /\\
          read X14 s = word 4286586879 /\\ read X15 s = word 4294443520 /\\
          read X16 s = word 4190208 /\\
          (!j. i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s = x j) /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add h (word(4 * j)))) s = y j) /\\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   mld_use_hint_32 (x j) (y j))" xa) in
  prove(INLINE_USEHINT32_TERM fn loop xa,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (h:int64) (x:num->int32) (y:num->int32) (pc:num).
      APPEND
        (f_ev_epil a h x y pc)
        (APPEND
          (ENUMERATEL 256
            (\i. if y i = word 0 then f_ev_zero a h x y pc i
                 else if &0 < ival(mld_decompose_lo_32 (x i))
                 then f_ev_pos a h x y pc i
                 else f_ev_neg a h x y pc i))
          (f_ev_prol a h x y pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `h:int64`; `x:num->int32`;
    `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; mld_poly_use_hint_32;
              fst UX] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256`
   (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s_exit" fn loop)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `mld_use_hint_32` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o C MP (ASSUME `i < 256`) o SPEC `i:num` o
      check (fun th -> is_forall(concl th) &&
        free_in `y:num->int32` (concl th) &&
        not(free_in `mld_use_hint_32` (concl th)))) THEN
    DISCH_TAC THEN
    ARM_STEPS_TAC UX (1--7) THEN
    REG_LANE_TAC `X9` `(x:num->int32) i` `mld_decompose_hi_32`
      [DECOMPOSE_HI_32_ALT] THEN
    ARM_STEPS_TAC UX (8--12) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0]) THEN
    BRANCH_CASES_TAC THENL
     [ARM_STEPS_TAC UX (13--16) THEN INLINE_USEHINT32_PATH_END_TAC;
      ARM_STEPS_TAC UX (13--16) THEN
      REG_LANE_TAC `X11` `(x:num->int32) i` `mld_decompose_lo_32`
        [DECOMPOSE_LO_32_MADD; mld_ct_sel] THEN
      ARM_STEPS_TAC UX (17--19) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INLINE_USEHINT_GE_COND]) THEN
      BRANCH_CASES_TAC THENL
       [ARM_STEPS_TAC UX (20--25) THEN INLINE_USEHINT32_PATH_END_TAC;
        ARM_STEPS_TAC UX (20--26) THEN INLINE_USEHINT32_PATH_END_TAC]];

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
          CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(*** The instances: function, loop, register of a ***)

let INLINE_USEHINT32_INSTANCES =
  ["mldsa65_verify_internal", "loop13", "X25";
   "mldsa87_verify_internal", "loop15", "X23"];;

let INLINE_USEHINT32_OF_INSTANCE (fn,loop,xa) = INLINE_USEHINT32_LOOP fn loop xa;;
