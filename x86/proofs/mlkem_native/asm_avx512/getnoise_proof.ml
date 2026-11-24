(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/asm_avx512/getnoise_spec.ml";;

let MLKEM_GETNOISE_AVX512_ZERO_COUNTER = prove
 (MLKEM_GETNOISE_AVX512_ZERO_COUNTER_STMT,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)));;

let MLKEM_GETNOISE_AVX512_ZERO = prove
 (MLKEM_GETNOISE_AVX512_ZERO_STMT,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP2_TAC `12` `pc + mlkem_getnoise_zero`
   (pc_plus "mlkem_getnoise_zero" 30)
   `\i s. read RDI s = word_add stackpointer (word(128 * i)) /\
          read RCX s = word(12 - i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    X86_SIM_TAC MLKEM_GETNOISE_AVX512_EXEC (1--3) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X86_SIM_TAC MLKEM_GETNOISE_AVX512_EXEC (1--7) THEN
    ASM_SIMP_TAC[MLKEM_GETNOISE_AVX512_ZERO_COUNTER] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; CONV_TAC WORD_RULE];
    X86_SIM_TAC MLKEM_GETNOISE_AVX512_EXEC [1]]);;

let MLKEM_GETNOISE_AVX512_ZERO_SAFE = time prove
 (MLKEM_GETNOISE_AVX512_ZERO_SAFE_STMT,
  REWRITE_TAC[SOME_FLAGS] THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(stackpointer:int64) (pc:num).
      APPEND (f_ev_epil stackpointer pc)
             (APPEND (ENUMERATEL 12 (\i. f_ev_loop stackpointer pc i))
                     (f_ev_prol stackpointer pc)) :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `pc:num`] THEN
  DISCH_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `12` `pc + mlkem_getnoise_zero`
   (pc_plus "mlkem_getnoise_zero" 30)
   `\i s. read RDI s = word_add stackpointer (word(128 * i)) /\
          read RCX s = word(12 - i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_GETNOISE_AVX512_EXEC (1--3) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_GETNOISE_AVX512_EXEC (1--7) THEN
    ASM_SIMP_TAC[MLKEM_GETNOISE_AVX512_ZERO_COUNTER] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_GETNOISE_AVX512_EXEC [1] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let MLKEM_NATIVE_GETNOISE_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT = time prove
 (MLKEM_NATIVE_GETNOISE_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `sigma:int64`; `seed:byte list`; `nonce0:num`; `n:num`;
    `n1:num`; `eta1:num`; `c:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 2527 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN
    SUBST1_TAC)) THEN
  MLKEM_GETNOISE_AVX512_INSTANCE_TAC);;

let MLKEM_NATIVE_GETNOISE_ASM_AVX512_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_GETNOISE_ASM_AVX512_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
     SHA3_KECCAK4_F1600_AVX512_SUBROUTINE_SAFE_ALTFORM "H_K4" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
     SHA3_KECCAK_F1600_AVX512_IMAGE_SAFE "H_K1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
     MLKEM_CBD2_SUBROUTINE_SAFE_FRAMED "H_CBD2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
     MLKEM_CBD3_SUBROUTINE_SAFE_FRAMED "H_CBD3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC MLKEM_GETNOISE_AVX512_ZERO_SAFE "H_ZERO" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(r:int64) (sigma:int64) (n:num) (eta1:num) (c:int64) (pc:num)
     (stackpointer:int64) (returnaddress:int64).
      if eta1 = 2 then
        if n = 4 then f_ev_24 r sigma c pc stackpointer returnaddress
        else if n = 7 then f_ev_27 r sigma c pc stackpointer returnaddress
        else if n = 8 then f_ev_28 r sigma c pc stackpointer returnaddress
        else f_ev_29 r sigma c pc stackpointer returnaddress
      else if n = 4 then f_ev_34 r sigma c pc stackpointer returnaddress
      else f_ev_35 r sigma c pc stackpointer returnaddress
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `r:int64`; `sigma:int64`; `nonce0:num`; `n:num`;
    `n1:num`; `eta1:num`; `c:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 2527 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN
    SUBST1_TAC)) THEN
  MLKEM_GETNOISE_AVX512_INSTANCE_SAFE_TAC);;
