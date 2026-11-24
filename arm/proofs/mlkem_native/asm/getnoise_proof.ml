(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The noise sampling of ML-KEM, SamplePolyCBD_eta(PRF_eta(sigma, b)) of     *)
(* FIPS 203 for n consecutive nonces b, in the lanes of the x4 Keccak        *)
(* permutation, in the mlkem_native2 image, for the configurations used by   *)
(* the API functions.                                                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/asm/getnoise_spec.ml";;
needs "arm/proofs/utils/mlkem_native2_noise.ml";;

(**** The function's code is arm/mlkem_native/asm/mlkem_getnoise.S. Its frame
 **** of 1728 bytes has the saved registers at sp, the four 200-byte lanes
 **** at sp + 96, the four 192-byte buffers at sp + 896 and the index and
 **** block count of each lane's polynomial at sp + 1664 and sp + 1696; the
 **** x4 permutation uses 224 bytes below it. In the proofs stackpointer is
 **** the stack pointer less those 224 bytes, so that the lanes are at
 **** stackpointer + 320 + 200 * l and the buffers at stackpointer + 1120 +
 **** 192 * l.
 ****)

let MLKEM_GETNOISE_EXEC = MLKEM_NATIVE2_IMAGE_EXEC ["mlkem_getnoise"];;

(* ------------------------------------------------------------------------- *)
(* The zeroing of the lanes and buffers before the return, as one step.      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_GETNOISE_ZERO = prove
 (`!stackpointer pc.
     nonoverlapping (word_add stackpointer (word 96),1568)
                    (word pc,mlkem_native2_image_size)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem_getnoise_end) /\
               read SP s = stackpointer)
          (\s. read PC s = word(pc + 10916))
          (MAYCHANGE [PC; X0; X1] ,, MAYCHANGE [NF; ZF; CF; VF] ,,
           MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(word_add stackpointer (word 96),1568)])`,
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP2_TAC `98` `pc + mlkem_getnoise_zero` `pc + 10916`
   `\i s. read X0 s = word_add stackpointer (word(96 + 16 * i)) /\
          read X1 s = word(1568 - 16 * i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ARM_SIM_TAC MLKEM_GETNOISE_EXEC (1--2) THEN CONV_TAC NUM_REDUCE_CONV;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `word_sub (word(1568 - 16 * i)) (word 16):int64 =
      word(1568 - 16 * (i + 1)) /\
      val(word(1568 - 16 * (i + 1)):int64) = 1568 - 16 * (i + 1)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`1568 - 16 * i`; `16`]
          (INST_TYPE [`:64`,`:N`] WORD_SUB)) THEN
        ASM_SIMP_TAC[ARITH_RULE `i < 98 ==> 16 <= 1568 - 16 * i`] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ARITH_TAC;
        REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        ARITH_TAC];
      ALL_TAC] THEN
    ARM_SIM_TAC MLKEM_GETNOISE_EXEC (1--3) THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) < 1568 <=> i + 1 < 98`] THEN
      COND_CASES_TAC THEN REWRITE_TAC[];
      CONV_TAC WORD_RULE];
    ARM_SIM_TAC MLKEM_GETNOISE_EXEC []]);;

let MLKEM_GETNOISE_ZERO_SAFE = time prove
 (`exists f_events.
     forall e stackpointer pc.
       nonoverlapping (word_add stackpointer (word 96),1568)
                      (word pc,mlkem_native2_image_size)
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem_getnoise_end) /\
                 read SP s = stackpointer /\
                 read events s = e)
            (\s. read PC s = word(pc + 10916) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events stackpointer pc /\
                    memaccess_inbounds e2
                     [word_add stackpointer (word 96),1568]
                     [word_add stackpointer (word 96),1568]))
            (MAYCHANGE [PC; X0; X1] ,, MAYCHANGE [NF; ZF; CF; VF] ,,
             MAYCHANGE [events] ,,
             MAYCHANGE
              [memory :> bytes(word_add stackpointer (word 96),1568)])`,
  CONCRETIZE_F_EVENTS_TAC
   `\(stackpointer:int64) (pc:num).
      APPEND (f_ev_epil stackpointer pc)
             (APPEND (ENUMERATEL 98 (\i. f_ev_loop stackpointer pc i))
                     (f_ev_prol stackpointer pc)) :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `pc:num`] THEN
  DISCH_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `98` `pc + mlkem_getnoise_zero` `pc + 10916`
   `\i s. read X0 s = word_add stackpointer (word(96 + 16 * i)) /\
          read X1 s = word(1568 - 16 * i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_GETNOISE_EXEC (1--2) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `word_sub (word(1568 - 16 * i)) (word 16):int64 =
      word(1568 - 16 * (i + 1)) /\
      val(word(1568 - 16 * (i + 1)):int64) = 1568 - 16 * (i + 1)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`1568 - 16 * i`; `16`]
          (INST_TYPE [`:64`,`:N`] WORD_SUB)) THEN
        ASM_SIMP_TAC[ARITH_RULE `i < 98 ==> 16 <= 1568 - 16 * i`] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ARITH_TAC;
        REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        ARITH_TAC];
      ALL_TAC] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_GETNOISE_EXEC (1--3) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) < 1568 <=> i + 1 < 98`] THEN
      COND_CASES_TAC THEN REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_GETNOISE_EXEC [] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The facts added on the way, by the PC offset where they are needed:       *)
(*                                                                           *)
(*  - when the lane l in X27 has been set up for the nonce in X2, its state, *)
(*    mlkem_noise_state seed (word(nonce0 + i));                             *)
(*                                                                           *)
(*  - the selection of eta for the polynomial, which is 2 either way when    *)
(*    eta1 = 2 (and n1 is not known);                                        *)
(*                                                                           *)
(*  - for eta = 3, the words of the lane at X2 before it is copied to the    *)
(*    buffer at X3, 136 bytes after the first permutation and 56 after the   *)
(*    second, and the buffer as the PRF output after each copy.              *)
(* ------------------------------------------------------------------------- *)

let LANE_INIT_TAC k gl =
  let l = dest_small_numeral(rand(find_read_fact `X27` k gl)) in
  let y = find_read_fact `X2` k gl in
  let a = addr_plus `stackpointer:int64` (320 + 200 * l) in
  (MP_TAC(SPECL [a; `seed:byte list`; y; state_of k] MLKEM_NOISE_LANE) THEN
   ANTS_TAC THENL
    [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     CONV_TAC(DEPTH_CONV NUM_EXP_CONV) THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[GSYM WORD_ADD; WORD_ZX_BYTE_WORD;
                 READ_MEMORY_WBYTES_1600] THEN
     DISCH_TAC]) gl;;

let LANE_LOAD_TAC offs128 offs64 k gl =
  let a = find_read_fact `X2` k gl in
  let sv = state_of k in
  let th200 = bytes_fact a 200 k gl in
  let x = rand(concl th200) in
  let mk lemma len off =
    let th = SPECL [a; `200`; x; mk_small_numeral off; sv] lemma in
    let th' = MP th (CONJ th200 (ARITH_RULE(mk_binop `(<=):num->num->bool`
               (mk_binop `(+):num->num->num` (mk_small_numeral off)
                 (mk_small_numeral len)) `200`))) in
    CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THENC
              RAND_CONV(NUM_REDUCE_CONV)) (REWRITE_RULE[WORD_ADD_0] th') in
  let ths = map (mk READ_MEMORY_BYTES128_OF_NUM 16) offs128 @
            map (mk READ_MEMORY_BYTES64_OF_NUM 8) offs64 in
  MAP_EVERY (ASSUME_TAC o REWRITE_RULE[DIV_1]) ths gl;;

let BUF1_TAC k gl =
  let buf = find_read_fact `X3` k gl in
  let x = rand(concl(bytes_fact (find_read_fact `X2` k gl) 200 k gl)) in
  let sv = state_of k in
  let lhs64 = vsubst [addr_plus buf 128,`a:int64`; sv,`s:armstate`]
                `read (memory :> bytes64 a) s` in
  (RULE_ASSUM_TAC(fun th ->
     if (try lhand(concl th) = lhs64 with Failure _ -> false)
     then CONV_RULE(RAND_CONV NUM_REDUCE_CONV)
                   (REWRITE_RULE[WORD_ZX_64_128] th)
     else th) THEN
   MP_TAC(SPECL [buf; x; sv] READ_MEMORY_BYTES_136_OF_PIECES) THEN
   ANTS_TAC THENL
    [CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
     CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     REWRITE_TAC[DIV_1; WORD_ADD_0] THEN ASM_REWRITE_TAC[];
     DISCH_TAC]) gl;;

let BUF2_TAC k gl =
  let buf = find_read_fact `X3` k gl in
  let sv = state_of k in
  let b = rand(rand(rand(lhand(rand(concl(bytes_fact buf 136 k gl)))))) in
  (MP_TAC(SPECL [buf; `seed:byte list`; b; sv]
     READ_MEMORY_BYTES_192_PRF_3) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     REWRITE_TAC[DIV_1; WORD_ADD_0] THEN ASM_REWRITE_TAC[];
     DISCH_TAC]) gl;;

let getnoise_derive =
  [layout "mlkem_getnoise_assigned" - 4, LANE_INIT_TAC;
   layout "mlkem_getnoise_postloop" + 24, SIMP_REG_TAC `X1` [COND_ID];
   layout "mlkem_getnoise_eta3" + 28,
     LANE_LOAD_TAC [0;16;32;48;64;80;96;112] [128];
   layout "mlkem_getnoise_eta3" + 68, BUF1_TAC;
   layout "mlkem_getnoise_eta3_second", LANE_LOAD_TAC [0;16;32;48] [];
   layout "mlkem_getnoise_eta3_second" + 24, BUF2_TAC];;

let getnoise_calls =
  [layout "sha3_keccak4_f1600_alt2", KECCAK4_CALL_TAC MLKEM_GETNOISE_EXEC;
   layout "sha3_keccak_f1600", KECCAK1_CALL_TAC MLKEM_GETNOISE_EXEC;
   layout "mlkem_cbd2", CBD2_CALL_TAC MLKEM_GETNOISE_EXEC;
   layout "mlkem_cbd3", CBD3_CALL_TAC MLKEM_GETNOISE_EXEC;
   layout "mlkem_getnoise_end",
   (fun k -> ARM_SUBROUTINE_SIM_TAC
     (mlkem_native2_image_mc,MLKEM_GETNOISE_EXEC,0,mlkem_native2_image_mc,
      MLKEM_GETNOISE_ZERO)
     [`read SP s`; `pc:num`] (k+1))];;

(* ------------------------------------------------------------------------- *)
(* Correctness for the configurations (n,n1,eta1) used: eta1 = 2 for n = 4,  *)
(* 7, 8 or 9 polynomials (any n1, eta being 2 for all), and eta1 = 3 for n = *)
(* 4 with n1 = 4 or n = 5 with n1 = 2. The result is the coefficients of     *)
(* SamplePolyCBD_eta(PRF_eta(seed, word(nonce0 + i))) with eta = eta1 for i  *)
(* < n1 and 2 otherwise. The stack is the frame of 1728 bytes and the 224    *)
(* used by sha3_keccak4_f1600_alt2.                                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_GETNOISE_INSTANCE_TAC =
  REWRITE_TAC[COND_ID] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
              (mk_const("X"^string_of_int n,[]))) (19--29) THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`sigma:int64`; `32`; `num_of_bytelist(seed:byte list)`; `0`;
                `s0:armstate`] READ_MEMORY_BYTES128_OF_NUM) THEN
  MP_TAC(SPECL [`sigma:int64`; `32`; `num_of_bytelist(seed:byte list)`; `16`;
                `s0:armstate`] READ_MEMORY_BYTES128_OF_NUM) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 + 16 <= 32 /\ 16 + 16 <= 32`; WORD_ADD_0;
                  MULT_CLAUSES; EXP; DIV_1] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o
    REWRITE_RULE[WORDLIST_FROM_MEMORY_ROUND_CONSTANTS] o check (can
     (term_match [] `wordlist_from_memory(c,24) s = round_constants`) o
     concl)) THEN
  NATIVE2_RUN_TAC MLKEM_GETNOISE_EXEC getnoise_derive getnoise_calls 0 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;;

let MLKEM_NATIVE_GETNOISE_ASM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_GETNOISE_ASM_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `sigma:int64`; `seed:byte list`; `nonce0:num`; `n:num`;
    `n1:num`; `eta1:num`; `c:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 1952 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN
    SUBST1_TAC)) THEN
  MLKEM_GETNOISE_INSTANCE_TAC);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety, for the same configurations: the         *)
(* events depend only on the addresses and on n and eta1.                    *)
(* ------------------------------------------------------------------------- *)

let getnoise_safe_vars =
  [`r:int64`; `sigma:int64`; `c:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`];;

let getnoise_safe_calls =
  let call = NATIVE2_SAFE_CALL_TAC MLKEM_GETNOISE_EXEC getnoise_safe_vars in
  [layout "sha3_keccak4_f1600_alt2",
   call "H_K4" (layout "sha3_keccak4_f1600_alt2",sha3_keccak4_f1600_alt2_mc)
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`;
     `pc + sha3_keccak4_f1600_alt2`; `read SP s`; `read X30 s`];
   layout "sha3_keccak_f1600",
   call "H_K1" (layout "sha3_keccak_f1600",sha3_keccak_f1600_mc)
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`;
     `pc + sha3_keccak_f1600`; `read SP s`; `read X30 s`];
   layout "mlkem_cbd2",
   call "H_CBD2" (layout "mlkem_cbd2",mlkem_cbd2_mc)
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc + mlkem_cbd2`;
     `read X30 s`];
   layout "mlkem_cbd3",
   call "H_CBD3" (layout "mlkem_cbd3",mlkem_cbd3_mc)
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc + mlkem_cbd3`;
     `read X30 s`];
   layout "mlkem_getnoise_end",
   call "H_ZERO" (0,mlkem_native2_image_mc)
    [`e:(uarch_event)list`; `read SP s`; `pc:num`]];;

let MLKEM_GETNOISE_INSTANCE_SAFE_TAC =
  REWRITE_TAC[COND_ID; ARITH_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
              (mk_const("X"^string_of_int n,[]))) (19--29) THEN
  ENSURES_INIT_TAC "s0" THEN
  NATIVE2_SAFE_RUN_TAC MLKEM_GETNOISE_EXEC
   [layout "mlkem_getnoise_postloop" + 24, SIMP_REG_TAC `X1` [COND_ID]]
   getnoise_safe_calls 0 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MEMACCESS_NUMERALS_TAC THEN NATIVE2_DISCHARGE_SAFETY_TAC;;

let MLKEM_NATIVE_GETNOISE_ASM_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_GETNOISE_ASM_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
     SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_SAFE_FRAMED "H_K4" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
     SHA3_KECCAK_F1600_SUBROUTINE_SAFE_FRAMED "H_K1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
     MLKEM_CBD2_SUBROUTINE_SAFE_FRAMED "H_CBD2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
     MLKEM_CBD3_SUBROUTINE_SAFE_FRAMED "H_CBD3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC MLKEM_GETNOISE_ZERO_SAFE "H_ZERO" THEN
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
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN
    SUBST1_TAC)) THEN
  MLKEM_GETNOISE_INSTANCE_SAFE_TAC);;
