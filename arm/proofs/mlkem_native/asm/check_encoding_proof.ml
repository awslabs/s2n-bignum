(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proofs of the contracts of mlkem_check_encoding (see                      *)
(* check_encoding_spec.ml). The standalone proof of                          *)
(* arm/proofs/mlkem_check_encoding.ml runs here, in the job of this file, so *)
(* that it runs once: it proves the correctness theorem and the safety       *)
(* theorem of the library. From them the safety with the frame of the        *)
(* correctness theorem is made, as needed to use the function as a callee    *)
(* (the one of the library has a trivial frame), and the correctness and     *)
(* safety in one ("FULL"), for the callers whose events depend on its        *)
(* result.                                                                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/asm/check_encoding_spec.ml";;

loadt "arm/proofs/mlkem_check_encoding.ml";;

(* ------------------------------------------------------------------------- *)
(* The safety with the frame of the correctness theorem, without and with    *)
(* the BTI landing pad.                                                      *)
(* ------------------------------------------------------------------------- *)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_check_encoding" subroutine_signatures)
    MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_CORRECT
    MLKEM_CHECK_ENCODING_EXEC;;

let MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_SAFE_FRAMED = time prove
 (`exists f_events.
       forall e a k pc returnaddress.
           val k < 2 EXP 61
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_check_encoding_tmc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; k] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a k pc returnaddress /\
                        memaccess_inbounds e2 [a,(384 * val k) * 1] []))
               MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (k:int64) (pc:num) (returnaddress:int64).
      if val k = 0 then f_ev_zero a k pc returnaddress
      else APPEND (f_ev_epil a k pc returnaddress)
                  (APPEND (ENUMERATEL (8 * val k)
                             (\i. f_ev_loop a k pc returnaddress i))
                          (f_ev_prol a k pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `a:int64` THEN W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; fst MLKEM_CHECK_ENCODING_EXEC;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_CHECK_ENCODING_EXEC (1--31) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_shl (word k:int64) 3 = word(8 * k)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 3 * k = 8 * k`];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(8 * k):int64) = 8 * k /\ ~(8 * k = 0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `k < 2 EXP 61` THEN ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `8 * k` `pc + 0x4c` `pc + 0x98`
   `\i s. read X30 s = returnaddress /\
          read X0 s = word_add a (word(48 * i)) /\
          read X4 s = word(8 * k - i)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_CHECK_ENCODING_EXEC (1--19) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `word_sub (word (8 * k - i)) (word 1):int64 = word(8 * k - (i + 1)) /\
      val(word(8 * k - (i + 1)):int64) = 8 * k - (i + 1)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`8 * k - i`; `1`]
          (INST_TYPE [`:64`,`:N`] WORD_SUB)) THEN
        ASM_SIMP_TAC[ARITH_RULE `i < 8 * k ==> 1 <= 8 * k - i`] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ARITH_TAC;
        REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `k < 2 EXP 61` THEN ARITH_TAC];
      ALL_TAC] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_CHECK_ENCODING_EXEC (1--19) THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_CHECK_ENCODING_EXEC (1--12) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let MLKEM_CHECK_ENCODING_SUBROUTINE_SAFE_FRAMED = prove
 (MLKEM_CHECK_ENCODING_SUBROUTINE_SAFE_FRAMED_STMT,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_check_encoding_mc mlkem_check_encoding_tmc
    MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_SAFE_FRAMED));;

(* ------------------------------------------------------------------------- *)
(* The correctness and the events in one theorem, without and with the BTI   *)
(* landing pad.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_FULL = time prove
 (`exists f_events.
     forall e a k n pc returnaddress.
         val k < 2 EXP 61
         ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_check_encoding_tmc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; k] s /\
                  read (memory :> bytes(a,384 * val k)) s = n /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                  (if !i. i < 256 * val k
                          ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
                   then word 1 else word 0) /\
                  (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events a k pc returnaddress /\
                      memaccess_inbounds e2 [a,(384 * val k) * 1] []))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (k:int64) (pc:num) (returnaddress:int64).
      if val k = 0 then f_ev_zero a k pc returnaddress
      else APPEND (f_ev_epil a k pc returnaddress)
                  (APPEND (ENUMERATEL (8 * val k)
                             (\i. f_ev_loop a k pc returnaddress i))
                          (f_ev_prol a k pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `a:int64` THEN W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; fst MLKEM_CHECK_ENCODING_EXEC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; LT] THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_CHECK_ENCODING_EXEC [n] THEN
                        SIMD_SIMPLIFY_TAC[]) (1--31) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_shl (word k:int64) 3 = word(8 * k)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 3 * k = 8 * k`];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(8 * k):int64) = 8 * k /\ ~(8 * k = 0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `k < 2 EXP 61` THEN ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `8 * k` `pc + 0x4c` `pc + 0x98`
   `\i s. read X30 s = returnaddress /\
          read X0 s = word_add a (word(48 * i)) /\
          read X4 s = word(8 * k - i) /\
          read Q29 s = word 0xfff00ffffff00ffffff00ffffff00fff /\
          read Q31 s = word 0x0b0a0a09080707060504040302010100 /\
          read (memory :> bytes(a,384 * k)) s = n /\
          (!j. j < 32
               ==> (word_uge
                     (word_subword
                       (word_join
                         (word_join (read Q19 s) (read Q18 s):256 word)
                         (word_join (read Q17 s) (read Q16 s):256 word)
                        :512 word) (16 * j,16):int16)
                     (word(if EVEN j then 3329 else 53264)) <=>
                    ?t. t < i /\ cenc_bad n (32 * t + j)))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** The initialization, with all lanes 0 ***)

    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_CHECK_ENCODING_EXEC [n] THEN
                        SIMD_SIMPLIFY_TAC[]) (1--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; LT] THEN
    CONJ_TAC THENL
     [CONV_TAC WORD_REDUCE_CONV THEN
      REWRITE_TAC[word_subword; VAL_WORD_0; DIV_0; MOD_0; WORD_UGE] THEN
      GEN_TAC THEN COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN
      ARITH_TAC;
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The loop body, on the 384-bit chunk c of the input ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `word_sub (word (8 * k - i)) (word 1):int64 = word(8 * k - (i + 1)) /\
      val(word(8 * k - (i + 1)):int64) = 8 * k - (i + 1)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`8 * k - i`; `1`]
          (INST_TYPE [`:64`,`:N`] WORD_SUB)) THEN
        ASM_SIMP_TAC[ARITH_RULE `i < 8 * k ==> 1 <= 8 * k - i`] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ARITH_TAC;
        REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `k < 2 EXP 61` THEN ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC
     `c:384 word = word((n DIV 2 EXP (8 * (48 * i))) MOD 2 EXP 384)` THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MAP_EVERY ABBREV_TAC
     [`m0 = read Q16 s0`; `m1 = read Q17 s0`; `m2 = read Q18 s0`;
      `m3 = read Q19 s0`] THEN
    MP_TAC(SPECL [`a:int64`; `384 * k`; `n:num`; `48 * i`; `s0:armstate`]
      CHECK_ENCODING_LOADS) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [UNDISCH_TAC `i < 8 * k` THEN ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
    MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_CHECK_ENCODING_EXEC [n] THEN
                        SIMD_SIMPLIFY_TAC[]) (1--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      CONV_TAC WORD_RULE;
      FIRST_X_ASSUM(MP_TAC o check (can (term_match []
        `!j. j < 32 ==> (word_uge x y <=> ?t. t < i /\ P t j)`) o concl)) THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
                         SIMD_SIMPLIFY_CONV[])) THEN
      STRIP_TAC THEN
      MP_TAC(SPECL [`n:num`; `i:num`; `c:384 word`] CHECK_ENCODING_FIELD) THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
      STRIP_TAC THEN
      CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
               SIMD_SIMPLIFY_CONV[]) THEN
      REWRITE_TAC[WORD_UGE_UMAX; EXISTS_LT_ADD1] THEN ASM_REWRITE_TAC[] THEN
      LANE_ARGS_BITBLAST_TAC 8 [];
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The combination of the maxima, the comparison and the return ***)

    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MAP_EVERY ABBREV_TAC
     [`m0 = read Q16 s0`; `m1 = read Q17 s0`; `m2 = read Q18 s0`;
      `m3 = read Q19 s0`] THEN
    FIRST_X_ASSUM(MP_TAC o check (can (term_match []
      `!j. j < 32 ==> (word_uge x y <=> ?t. t < i /\ P t j)`) o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
                       SIMD_SIMPLIFY_CONV[])) THEN
    STRIP_TAC THEN
    MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_CHECK_ENCODING_EXEC [n] THEN
                        SIMD_SIMPLIFY_TAC[]) (1--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[WORD_UGE_UMAX] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CHECK_ENCODING_MASK_MAX; CHECK_ENCODING_ALL] THEN
      CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
                         NUM_REDUCE_CONV)) THEN
      W(fun (asl,w) ->
        let bv = find_term (fun t -> match t with
                     Comb(Const("bitval",_),_) -> true | _ -> false) w in
        let d = rand bv in
        SUBGOAL_THEN (mk_eq(lhand w,mk_cond(d,`word 0:int64`,`word 1:int64`)))
        SUBST1_TAC THENL
         [SPEC_TAC(d,`b:bool`) THEN GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
          REWRITE_TAC[BITVAL_CLAUSES] THEN
          CONV_TAC(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV) THEN REWRITE_TAC[];
          GEN_REWRITE_TAC LAND_CONV [GSYM COND_SWAP] THEN
          AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          REWRITE_TAC[DE_MORGAN_THM] THEN
          W(fun (_,w) -> ACCEPT_TAC(CONJ_ACI_RULE w))]);
      DISCHARGE_SAFETY_PROPERTY_TAC]]);;

let MLKEM_CHECK_ENCODING_SUBROUTINE_FULL = prove
 (MLKEM_CHECK_ENCODING_SUBROUTINE_FULL_STMT,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_check_encoding_mc mlkem_check_encoding_tmc
    MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_FULL));;
