(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing bytes from a Keccak state at a position: the proof (see         *)
(* keccak_squeeze_spec.ml).                                                  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/keccak_squeeze_spec.ml";;
needs "arm/proofs/utils/mldsa_native_squeeze.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The 32-bit arithmetic on the position, the rate and the lengths.          *)
(* ------------------------------------------------------------------------- *)

let SQZ_ZF_POS = prove
 (`!p r. p <= r /\ r <= 200
         ==> (val(word_sub (word_zx(word p:int64):int32)
                           (word_zx(word r:int64):int32)) = 0 <=> p = r)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `p < 4294967296 /\ r < 4294967296` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 4294967296 ==> x < 18446744073709551616`]);;

let SQZ_ZX_SUB = prove
 (`!r p. p <= r /\ r <= 200
         ==> word_zx(word_sub (word_zx(word r:int64):int32)
                              (word_zx(word p:int64):int32)):int64 =
             word(r - p)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_SUB_CASES;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `p < 4294967296 /\ r < 4294967296` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `r < 4294967296 ==> r < 18446744073709551616`;
    ARITH_RULE `r < 4294967296 ==> r - p < 4294967296`;
    ARITH_RULE `r < 4294967296 ==> r - p < 18446744073709551616`]);;

let SQZ_ZX_ADD = prove
 (`!p t. p + t < 2 EXP 32
         ==> word_zx(word_add (word_zx(word p:int64):int32)
                              (word_zx(word t:int64))):int64 = word(p + t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `p < 4294967296 /\ t < 4294967296` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `x < 4294967296 ==> x < 18446744073709551616`]);;

let SQZ_VAL_WORD_LE = prove
 (`!x n. x <= n /\ 200 + n <= 18446744073709551616
         ==> val(word x:int64) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

let SQZ_VAL_WORD_RATE = prove
 (`!x. x <= 200 ==> val(word x:int64) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

let SQZ_ZX2 = prove
 (`!p. p < 2 EXP 32 ==> word_zx(word_zx(word p:int64):int32):int64 = word p`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `p < 4294967296 ==> p < 18446744073709551616`]);;

(* ------------------------------------------------------------------------- *)
(* The position after the last block: the output ends at pos + outlen, at    *)
(* offset p + (outlen - w) of the block, or at its end.                      *)
(* ------------------------------------------------------------------------- *)

let SQZ_END = prove
 (`!pos outlen w p r X.
     pos + w = X + p /\ w + (r - p) = outlen /\ p < r
     ==> (pos + outlen) - X = r`,
  ARITH_TAC);;

let SQZ_END2 = prove
 (`!pos outlen w p X.
     pos + w = X + p /\ w < outlen
     ==> (pos + outlen) - X = p + (outlen - w)`,
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The blocks of the stream that the output touches: with b0 = pos DIV r     *)
(* the index of the block of the position (0, or 1 for pos = r), the output  *)
(* is in blocks b0 to b0 + nb, with nb = (pos + outlen - 1) DIV r - b0, and  *)
(* the last block holds r bytes of it exactly when (pos + outlen) MOD r = 0. *)
(* ------------------------------------------------------------------------- *)

let SQZ_BLOCKS = prove
 (`!pos outlen r.
        0 < r /\ pos <= r /\ ~(outlen = 0)
        ==> (pos DIV r = 0 /\ pos < r \/
             pos DIV r = 1 /\ ~(pos < r)) /\
            r * pos DIV r <= pos /\ pos - r * pos DIV r < r /\
            (pos + outlen - 1) DIV r =
            pos DIV r + ((pos + outlen - 1) DIV r - pos DIV r) /\
            r * (pos DIV r + ((pos + outlen - 1) DIV r - pos DIV r)) <
            pos + outlen /\
            pos + outlen <=
            r * (pos DIV r + ((pos + outlen - 1) DIV r - pos DIV r) + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pos DIV r = if pos < r then 0 else 1` SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_SIMP_TAC[DIV_LT] THEN
    SUBGOAL_THEN `pos:num = r` SUBST1_TAC THENL
     [ASM_ARITH_TAC;
      ASM_SIMP_TAC[DIV_REFL; ARITH_RULE `0 < r ==> ~(r = 0)`]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`pos + outlen - 1`; `r:num`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  SPEC_TAC(`(pos + outlen - 1) DIV r`,`q:num`) THEN
  SPEC_TAC(`(pos + outlen - 1) MOD r`,`t:num`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `pos < r` THENL
   [ASM_REWRITE_TAC[SUB_0; ADD_CLAUSES; MULT_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `r * (q + 1) = r * q + r`] THEN
    ASM_ARITH_TAC;
    SUBGOAL_THEN `~(q = 0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(q = 0) ==> 1 + (q - 1) = q`;
                 ARITH_RULE `~(q = 0) ==> (q - 1) + 1 = q`] THEN
    REWRITE_TAC[ARITH_RULE `r * (1 + q) = r * q + r`] THEN
    REWRITE_TAC[ARITH_RULE `r * (q + 1) = r * q + r`; MULT_CLAUSES] THEN
    ASM_ARITH_TAC]);;

let SQZ_LAST = prove
 (`!r q t. 0 < r /\ 0 < t /\ t <= r
           ==> ((r * q + t) MOD r = 0 <=> t = r)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `t:num = r` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[ARITH_RULE `r * q + r = r * (q + 1)`] THEN
    REWRITE_TAC[MOD_MULT];
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MULT_ADD] THEN
    SUBGOAL_THEN `t MOD r = t` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

let SQZ_KECCAK_SQUEEZE_1 = prove
 (`!S:1600 word. keccak_squeeze 1 S = keccak_f1600 S`,
  REWRITE_TAC[ONE; keccak_squeeze]);;

let SQZ_VAL_OUTLEN = prove
 (`200 + outlen <= 18446744073709551616 ==> val(word outlen:int64) = outlen`,
  DISCH_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The calls, with the FULL theorems of the callees assumed as "H_EXTRACT"   *)
(* and "H_PERMUTE".                                                          *)
(* ------------------------------------------------------------------------- *)

let SQZ_CALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
     (mldsa_native_libmldsa_gcc12_Os_mc,
      MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_EXEC,
      0x0,mldsa_native_libmldsa_gcc12_Os_mc,th)
     ilist n THENL
     [EXISTS_E2_FEV_TAC
       [`out:int64`; `outlen:num`; `ctx:int64`; `pos:num`; `r:num`; `pc:num`;
        `stackpointer:int64`; `returnaddress:int64`; `i:num`; `nb:num`;
        `b0:num`; `p:num`; `w:num`];
      LABEL_TAC name th]);;

(* ------------------------------------------------------------------------- *)
(* The events of a segment: unify them with the template (after expanding    *)
(* the abbreviations vs, which the template does not have), and prove the    *)
(* memory safety. The facts about the products of r with the number of the   *)
(* block, and about DIV, are removed before that: the arithmetic of          *)
(* CONTAINED_TAC takes all assumptions about numbers into account and        *)
(* needs about 40 seconds for each region that does not contain the one at   *)
(* hand, whereas the bounds that the regions need are linear in the          *)
(* abbreviations p and w. The assumptions about events stay.                 *)
(* ------------------------------------------------------------------------- *)

let SQZ_NONLINEAR c =
  let is_const_named n t = is_const t && name_of t = n in
  can (find_term (fun t -> is_binary "*" t && not(is_numeral(lhand t)) &&
                           not(is_numeral(rand t)))) c ||
  can (find_term (is_const_named "DIV")) c;;

let SQZ_CLEAR_TAC =
  let has_const n c = can (find_term (fun t -> is_const t && name_of t = n)) c in
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if SQZ_NONLINEAR c && not(has_const "memaccess_inbounds" c) &&
       not(has_const "APPEND" c)
    then ALL_TAC else NO_TAC));;

let SQZ_EVENTS_TAC vs =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY (fun v -> TRY(UNABBREV_VARS_TAC [v])) vs THEN
    (FULL_UNIFY_F_EVENTS_TAC ORELSE
     (REWRITE_TAC[GSYM APPEND_ASSOC] THEN FULL_UNIFY_F_EVENTS_TAC));
    ALL_TAC] THEN
  CONV_TAC(RATOR_CONV(RATOR_CONV(RAND_CONV APPEND_SPINE_CONV))) THEN
  TRY(UNABBREV_VARS_TAC [`b0:num`]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND_NIL; CONJUNCT1 APPEND] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC; APPEND_NIL;
                              CONJUNCT1 APPEND]) THEN
  SQZ_CLEAR_TAC THEN DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(* ------------------------------------------------------------------------- *)
(* The state at join1, before the extraction from block b0 + k (as the loop  *)
(* invariant, the state at the start of iteration k): w = 0 or               *)
(* r * (b0 + k) - pos bytes are written, and the next ones come from byte    *)
(* p = pos - r * b0 or 0 of the state after b0 + k permutations.             *)
(* ------------------------------------------------------------------------- *)

let SQZ_INV = parse_term
 "\\k s. read X23 s = ctx /\\ read X24 s = out /\\ read X22 s = word r /\\
        read X19 s = word(if k = 0 then pos - r * b0 else 0) /\\
        read X20 s =
        word(outlen - (if k = 0 then 0 else r * (b0 + k) - pos)) /\\
        read X25 s = word(if k = 0 then 0 else r * (b0 + k) - pos) /\\
        read SP s = word_add stackpointer (word 224) /\\
        read (memory :> bytes64 (word_add stackpointer (word 224))) s =
        x19_init /\\
        read (memory :> bytes64 (word_add stackpointer (word 232))) s =
        x20_init /\\
        read (memory :> bytes64 (word_add stackpointer (word 240))) s =
        x21_init /\\
        read (memory :> bytes64 (word_add stackpointer (word 248))) s =
        x22_init /\\
        read (memory :> bytes64 (word_add stackpointer (word 256))) s =
        x23_init /\\
        read (memory :> bytes64 (word_add stackpointer (word 264))) s =
        x24_init /\\
        read (memory :> bytes64 (word_add stackpointer (word 272))) s =
        x25_init /\\
        read (memory :> bytes64 (word_add stackpointer (word 280))) s =
        returnaddress /\\
        read (memory :> bytes(ctx,200)) s = val(keccak_squeeze (b0 + k) S) /\\
        read (memory :> bytes(out,if k = 0 then 0 else r * (b0 + k) - pos))
          s =
        num_of_bytelist
         (list_of_seq (mld_keccak_squeeze_byte r S pos)
                      (if k = 0 then 0 else r * (b0 + k) - pos))";;

let SQZ_INV_AT t = rand(concl(BETA_CONV(mk_comb(SQZ_INV,t))));;

let MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_OS_IMAGE_SUBROUTINE_FULL
    "H_EXTRACT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(out:int64) (outlen:num) (ctx:int64) (pos:num) (r:num) (pc:num)
     (stackpointer:int64) (returnaddress:int64).
      if outlen = 0
      then f_ev_zero out outlen ctx pos r pc stackpointer returnaddress
      else
       APPEND
        (if (pos + outlen) MOD r = 0
         then f_ev_lastf out outlen ctx pos r pc stackpointer returnaddress
         else f_ev_lastp out outlen ctx pos r pc stackpointer returnaddress)
        (APPEND
          (if (pos + outlen - 1) DIV r - pos DIV r = 0
           then f_ev_one out outlen ctx pos r pc stackpointer returnaddress
           else
            APPEND
             (f_ev_epil out outlen ctx pos r pc stackpointer returnaddress)
             (APPEND
               (ENUMERATEL ((pos + outlen - 1) DIV r - pos DIV r)
                 (\i. f_ev_loop out outlen ctx pos r pc stackpointer
                                returnaddress i))
               (f_ev_front out outlen ctx pos r pc stackpointer
                           returnaddress)))
          (if pos < r
           then f_ev_heada out outlen ctx pos r pc stackpointer returnaddress
           else f_ev_headb out outlen ctx pos r pc stackpointer
                           returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `out:int64`; `outlen:num`; `ctx:int64`;
    `pos:num`; `r:num`; `S:1600 word`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 288 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `200 + outlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(ctx:int64)`; `val(out:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN
  ASM_CASES_TAC `outlen = 0` THENL
   [(*** No output: nothing changes. The equation outlen = 0 is kept ***)
    (*** as outlen <= 0, so as not to rewrite the events template    ***)

    REWRITE_TAC[EQT_INTRO(ASSUME `outlen = 0`)] THEN
    FULL_INIT_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if concl th = `outlen = 0`
      then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
           ASSUME_TAC(MATCH_MP (ARITH_RULE `n = 0 ==> n <= 0`) th)
      else NO_TAC) THEN
    ARM_STEPS_TAC EXEC (1--17) THEN ARGS_32_TAC [`pos:num`] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(a /\ b /\ c) /\ d ==> a /\ b /\ c /\ d`) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `outlen = 0` SUBST1_TAC THENL
       [UNDISCH_TAC `outlen <= 0` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[mld_keccak_squeeze_state; list_of_seq; num_of_bytelist;
                      READ_MEMORY_BYTES_TRIVIAL];
      DISCHARGE_SAFETY_PROPERTY_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[EQF_INTRO(ASSUME `~(outlen = 0)`)] THEN

  (*** The blocks, and the state at join1 before the last block ***)

  MP_TAC(SPECL [`pos:num`; `outlen:num`; `r:num`] SQZ_BLOCKS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `nb = (pos + outlen - 1) DIV r - pos DIV r` THEN
  ABBREV_TAC `b0 = pos DIV r` THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + keccak_squeeze_fn_join1`
    (SQZ_INV_AT `nb:num`) THEN
  CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC `pc + keccak_squeeze_fn_join1`
      (SQZ_INV_AT `0`) THEN
    CONJ_TAC THENL
     [(*** To join1, with the permutation first if pos = r ***)

      FIRST_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
                  check (is_disj o concl)) THEN
      ASM_REWRITE_TAC[] THEN
      FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--11) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[UNDISCH SQZ_VAL_OUTLEN;
                                  ASSUME `~(outlen = 0)`]) THEN
      ARM_STEPS_TAC EXEC (12--12) THEN
      ARGS_32_TAC [`pos:num`; `r:num`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [MP (SPECL [`pos:num`; `r:num`] SQZ_ZF_POS)
           (CONJ (ASSUME `pos <= r`) (ASSUME `r <= 200`))]) THENL
       [SUBGOAL_THEN `~(pos:num = r)` (fun th ->
          RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
         [UNDISCH_TAC `pos < r` THEN ARITH_TAC; ALL_TAC] THEN
        ARM_STEPS_TAC EXEC (13--13) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; keccak_squeeze;
                        list_of_seq; num_of_bytelist;
                        READ_MEMORY_BYTES_TRIVIAL] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;
        SUBGOAL_THEN `pos:num = r` ASSUME_TAC THENL
         [UNDISCH_TAC `pos <= r` THEN UNDISCH_TAC `~(pos < r)` THEN
          ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `pos - r = 0` ASSUME_TAC THENL
         [UNDISCH_TAC `pos:num = r` THEN ARITH_TAC; ALL_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[EQT_INTRO(ASSUME `pos:num = r`)]) THEN
        ARM_STEPS_TAC EXEC (13--16) THEN
        KECCAK_STATE_AT_TAC `ctx:int64` THEN
        SQZ_CALL_TAC "H_PERMUTE"
         [`e:(uarch_event)list`; `read X0 s`; `S:1600 word`; `pc:num`;
          `read SP s`; `read X30 s`] 17 THEN
        RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0;
                        SQZ_KECCAK_SQUEEZE_1; list_of_seq;
                        num_of_bytelist; READ_MEMORY_BYTES_TRIVIAL] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC];

      (*** The nb blocks before the last, if any ***)

      ASM_CASES_TAC `nb = 0` THEN ASM_REWRITE_TAC[] THENL
       [FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        SQZ_EVENTS_TAC [`nb:num`; `b0:num`];
        ALL_TAC] THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `nb:num`
       `pc + keccak_squeeze_fn_join1` `pc + keccak_squeeze_fn_join1`
       SQZ_INV THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];

        FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        SQZ_EVENTS_TAC [`nb:num`; `b0:num`];

        (*** Block b0 + i: copy the bytes from p on, and permute ***)

        X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
        ABBREV_TAC `p = if i = 0 then pos - r * b0 else 0` THEN
        ABBREV_TAC `w = if i = 0 then 0 else r * (b0 + i) - pos` THEN
        SUBGOAL_THEN
         `p < r /\ pos + w = r * (b0 + i) + p /\
          w + (r - p) = r * (b0 + i + 1) - pos /\
          w + (r - p) < outlen /\
          (if i + 1 = 0 then 0 else r * (b0 + i + 1) - pos) = w + (r - p) /\
          (if i + 1 = 0 then pos - r * b0 else 0) = 0`
        STRIP_ASSUME_TAC THENL
         [MAP_EVERY EXPAND_TAC ["p"; "w"] THEN
          REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
          SUBGOAL_THEN `r * (b0 + i + 1) <= r * (b0 + nb)` MP_TAC THENL
           [REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `i < nb` THEN
            ARITH_TAC;
            ALL_TAC] THEN
          MAP_EVERY UNDISCH_TAC
           [`r * (b0 + nb) < pos + outlen`; `pos - r * b0 < r`;
            `r * b0 <= pos`; `pos <= r`] THEN
          COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
           [ARITH_TAC;
            SUBGOAL_THEN `r <= r * i` MP_TAC THENL
             [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `r = r * 1`] THEN
              REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `~(i = 0)` THEN
              ARITH_TAC;
              ARITH_TAC]];
          ALL_TAC] THEN
        FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--3) THEN
        SUBGOAL_THEN `p <= r /\ r - p <= 200` STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `p < r` THEN UNDISCH_TAC `r <= 200` THEN ARITH_TAC;
          ALL_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE
         [MP (SPECL [`r:num`; `p:num`] SQZ_ZX_SUB)
             (CONJ (ASSUME `p <= r`) (ASSUME `r <= 200`))]) THEN
        SUBGOAL_THEN `val(word(outlen - w):int64) = outlen - w /\
                      val(word(r - p):int64) = r - p`
         (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0; th])) THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC SQZ_VAL_WORD_LE THEN EXISTS_TAC `outlen:num` THEN
            REWRITE_TAC[ARITH_RULE `a - b <= a`] THEN FIRST_ASSUM ACCEPT_TAC;
            MATCH_MP_TAC SQZ_VAL_WORD_RATE THEN FIRST_ASSUM ACCEPT_TAC];
          ALL_TAC] THEN
        SUBGOAL_THEN
         `(outlen - w <= r - p <=> F) /\ (r - p = outlen - w <=> F)`
         (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
         [UNDISCH_TAC `w + (r - p) < outlen` THEN ARITH_TAC; ALL_TAC] THEN
        ARM_STEPS_TAC EXEC (4--12) THEN
        ARGS_32_TAC [`p:num`; `r - p`] THEN
        SUBGOAL_THEN `p + (r - p) <= 200 /\ w + (r - p) <= outlen`
        STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `p < r` THEN UNDISCH_TAC `r <= 200` THEN
          UNDISCH_TAC `w + (r - p) < outlen` THEN ARITH_TAC;
          ALL_TAC] THEN
        KECCAK_STATE_AT_TAC `ctx:int64` THEN
        SQZ_CALL_TAC "H_EXTRACT"
         [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `p:num`;
          `r - p`; `keccak_squeeze (b0 + i) (S:1600 word)`; `pc:num`;
          `read X30 s`] 13 THEN
        SUBGOAL_THEN
         `word_sub (word (outlen - w)) (word (r - p)):int64 =
          word(outlen - (w + (r - p)))`
         (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
         [REWRITE_TAC[ARITH_RULE `outlen - (w + d) = outlen - w - d`] THEN
          REWRITE_TAC[WORD_SUB] THEN
          SUBGOAL_THEN `r - p <= outlen - w` (fun th -> REWRITE_TAC[th]) THEN
          UNDISCH_TAC `w + (r - p) < outlen` THEN ARITH_TAC;
          ALL_TAC] THEN
        ARM_STEPS_TAC EXEC (14--15) THEN
        SUBGOAL_THEN
         `val(word(outlen - (r * (b0 + i + 1) - pos)):int64) =
          outlen - (r * (b0 + i + 1) - pos) /\
          ~(outlen - (r * (b0 + i + 1) - pos) = 0)`
         (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC SQZ_VAL_WORD_LE THEN EXISTS_TAC `outlen:num` THEN
            REWRITE_TAC[ARITH_RULE `a - b <= a`] THEN FIRST_ASSUM ACCEPT_TAC;
            UNDISCH_TAC `w + (r - p) < outlen` THEN
            UNDISCH_TAC `w + (r - p) = r * (b0 + i + 1) - pos` THEN
            ARITH_TAC];
          ALL_TAC] THEN
        SUBGOAL_THEN `p + (r - p) = r` ASSUME_TAC THENL
         [UNDISCH_TAC `p < r` THEN ARITH_TAC; ALL_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE
         [MP (SPECL [`p:num`; `r - p`] SQZ_ZX_ADD)
             (MP (ARITH_RULE `p + (r - p) = r /\ r <= 200
                              ==> p + (r - p) < 2 EXP 32`)
                 (CONJ (ASSUME `p + (r - p) = r`) (ASSUME `r <= 200`)));
          ASSUME `p + (r - p) = r`]) THEN
        ARM_STEPS_TAC EXEC (16--16) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_REFL; VAL_WORD_0]) THEN
        ARM_STEPS_TAC EXEC (17--20) THEN
        KECCAK_STATE_AT_TAC `ctx:int64` THEN
        SQZ_CALL_TAC "H_PERMUTE"
         [`e:(uarch_event)list`; `read X0 s`;
          `keccak_squeeze (b0 + i) (S:1600 word)`; `pc:num`; `read SP s`;
          `read X30 s`] 21 THEN
        RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
         [REWRITE_TAC[COND_ID];
          REWRITE_TAC[GSYM WORD_ADD] THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[ADD_ASSOC; GSYM ADD1; keccak_squeeze];
          REWRITE_TAC[GSYM(ASSUME
            `w + (r - p) = r * (b0 + i + 1) - pos`)] THEN
          REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
          REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
          REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
          MATCH_MP_TAC SQUEEZE_CHUNK THEN
          ASM_REWRITE_TAC[] THEN UNDISCH_TAC `p < r` THEN ARITH_TAC;
          SQZ_EVENTS_TAC [`p:num`; `w:num`; `nb:num`; `b0:num`]];

        (*** The exit of the loop, at join1 ***)

        ASM_REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[] THEN SQZ_EVENTS_TAC [`nb:num`; `b0:num`]]];

    (*** The last block, with the bytes from p on, up to its end or not ***)

    ABBREV_TAC `p = if nb = 0 then pos - r * b0 else 0` THEN
    ABBREV_TAC `w = if nb = 0 then 0 else r * (b0 + nb) - pos` THEN
    SUBGOAL_THEN
     `p < r /\ pos + w = r * (b0 + nb) + p /\ w < outlen /\
      p + (outlen - w) <= r /\ w + (outlen - w) = outlen`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["p"; "w"] THEN
      MAP_EVERY UNDISCH_TAC
       [`~(outlen = 0)`; `r * (b0 + nb) < pos + outlen`;
        `pos + outlen <= r * (b0 + nb + 1)`; `pos - r * b0 < r`;
        `r * b0 <= pos`; `pos <= r`] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
       [ARITH_TAC;
        SUBGOAL_THEN `r <= r * nb` MP_TAC THENL
         [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `r = r * 1`] THEN
          REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `~(nb = 0)` THEN
          ARITH_TAC;
          ARITH_TAC]];
      ALL_TAC] THEN
    MP_TAC(SPECL [`r:num`; `b0 + nb`; `p + (outlen - w)`] SQZ_LAST) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `w < outlen` THEN UNDISCH_TAC `p + (outlen - w) <= r` THEN
      UNDISCH_TAC `0 < r` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `r * (b0 + nb) + p + (outlen - w) = pos + outlen`
     SUBST1_TAC THENL
     [UNDISCH_TAC `pos + w = r * (b0 + nb) + p` THEN
      UNDISCH_TAC `w < outlen` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    ASM_CASES_TAC `(pos + outlen) MOD r = 0` THENL
     [(*** To the end of the block: the length is r - p ***)

      REWRITE_TAC[EQT_INTRO(ASSUME `(pos + outlen) MOD r = 0`)] THEN
      SUBGOAL_THEN `outlen - w = r - p` ASSUME_TAC THENL
       [UNDISCH_TAC `(pos + outlen) MOD r = 0 <=> p + (outlen - w) = r` THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `p + (outlen - w) <= r` THEN
        ARITH_TAC; ALL_TAC] THEN
      FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--3) THEN
      SUBGOAL_THEN `p <= r /\ r - p <= 200` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `p < r` THEN UNDISCH_TAC `r <= 200` THEN ARITH_TAC;
        ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [MP (SPECL [`r:num`; `p:num`] SQZ_ZX_SUB)
           (CONJ (ASSUME `p <= r`) (ASSUME `r <= 200`))]) THEN
      SUBGOAL_THEN `val(word(outlen - w):int64) = outlen - w /\
                    val(word(r - p):int64) = r - p`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0; th])) THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC SQZ_VAL_WORD_LE THEN EXISTS_TAC `outlen:num` THEN
          REWRITE_TAC[ARITH_RULE `a - b <= a`] THEN FIRST_ASSUM ACCEPT_TAC;
          MATCH_MP_TAC SQZ_VAL_WORD_RATE THEN FIRST_ASSUM ACCEPT_TAC];
        ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `outlen - w = r - p`; LE_REFL]) THEN
      ARM_STEPS_TAC EXEC (4--12) THEN
      ARGS_32_TAC [`p:num`; `r - p`] THEN
      SUBGOAL_THEN `p + (r - p) <= 200 /\ w + (r - p) <= outlen`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `p < r` THEN UNDISCH_TAC `r <= 200` THEN
        UNDISCH_TAC `w + (r - p) = outlen` THEN ARITH_TAC;
        ALL_TAC] THEN
      KECCAK_STATE_AT_TAC `ctx:int64` THEN
      SQZ_CALL_TAC "H_EXTRACT"
       [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `p:num`; `r - p`;
        `keccak_squeeze (b0 + nb) (S:1600 word)`; `pc:num`; `read X30 s`]
       13 THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `outlen - w = r - p`;
                                  WORD_SUB_REFL; VAL_WORD_0]) THEN
      ARM_STEPS_TAC EXEC (14--21) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `(a /\ b /\ c) /\ d ==> a /\ b /\ c /\ d`) THEN
      CONJ_TAC THENL
       [REPEAT CONJ_TAC THENL
         [SUBGOAL_THEN `outlen = w + (r - p)` SUBST1_TAC THENL
           [UNDISCH_TAC `w + (r - p) = outlen` THEN ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
          REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
          REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
          MATCH_MP_TAC SQUEEZE_CHUNK THEN
          ASM_REWRITE_TAC[] THEN UNDISCH_TAC `p < r` THEN ARITH_TAC;
          ASM_REWRITE_TAC[mld_keccak_squeeze_state] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];
          SUBGOAL_THEN `p + (r - p) = r` ASSUME_TAC THENL
           [UNDISCH_TAC `p < r` THEN ARITH_TAC; ALL_TAC] THEN
          MP_TAC(SPECL [`pos:num`; `outlen:num`; `w:num`; `p:num`; `r:num`;
                        `r * (b0 + nb)`] SQZ_END) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
          MP_TAC(SPECL [`p:num`; `r - p`] SQZ_ZX_ADD) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `r <= 200` THEN ARITH_TAC;
            DISCH_TAC] THEN
          MP_TAC(SPEC `r:num` SQZ_ZX2) THEN
          ANTS_TAC THENL
           [UNDISCH_TAC `r <= 200` THEN ARITH_TAC; DISCH_TAC] THEN
          ASM_REWRITE_TAC[mld_keccak_squeeze_state] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]];
        SQZ_EVENTS_TAC [`p:num`; `w:num`; `nb:num`; `b0:num`]];

      (*** Before the end of the block: the length is the rest ***)

      REWRITE_TAC[EQF_INTRO(ASSUME `~((pos + outlen) MOD r = 0)`)] THEN
      SUBGOAL_THEN `outlen - w < r - p` ASSUME_TAC THENL
       [UNDISCH_TAC `(pos + outlen) MOD r = 0 <=> p + (outlen - w) = r` THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `p + (outlen - w) <= r` THEN
        ARITH_TAC; ALL_TAC] THEN
      FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--3) THEN
      SUBGOAL_THEN `p <= r /\ r - p <= 200` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `p < r` THEN UNDISCH_TAC `r <= 200` THEN ARITH_TAC;
        ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [MP (SPECL [`r:num`; `p:num`] SQZ_ZX_SUB)
           (CONJ (ASSUME `p <= r`) (ASSUME `r <= 200`))]) THEN
      SUBGOAL_THEN `val(word(outlen - w):int64) = outlen - w /\
                    val(word(r - p):int64) = r - p`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0; th])) THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC SQZ_VAL_WORD_LE THEN EXISTS_TAC `outlen:num` THEN
          REWRITE_TAC[ARITH_RULE `a - b <= a`] THEN FIRST_ASSUM ACCEPT_TAC;
          MATCH_MP_TAC SQZ_VAL_WORD_RATE THEN FIRST_ASSUM ACCEPT_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `(outlen - w <= r - p <=> T) /\ (r - p = outlen - w <=> F)`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [UNDISCH_TAC `outlen - w < r - p` THEN ARITH_TAC; ALL_TAC] THEN
      ARM_STEPS_TAC EXEC (4--12) THEN
      ARGS_32_TAC [`p:num`; `outlen - w`] THEN
      SUBGOAL_THEN `p + (outlen - w) <= 200 /\ w + (outlen - w) <= outlen`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `p < r` THEN UNDISCH_TAC `r <= 200` THEN
        UNDISCH_TAC `outlen - w < r - p` THEN
        UNDISCH_TAC `w + (outlen - w) = outlen` THEN ARITH_TAC;
        ALL_TAC] THEN
      KECCAK_STATE_AT_TAC `ctx:int64` THEN
      SQZ_CALL_TAC "H_EXTRACT"
       [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `p:num`;
        `outlen - w`; `keccak_squeeze (b0 + nb) (S:1600 word)`; `pc:num`;
        `read X30 s`] 13 THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_REFL; VAL_WORD_0]) THEN
      ARM_STEPS_TAC EXEC (14--21) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `(a /\ b /\ c) /\ d ==> a /\ b /\ c /\ d`) THEN
      CONJ_TAC THENL
       [REPEAT CONJ_TAC THENL
         [FIRST_X_ASSUM(fun th ->
            if concl th = `w + (outlen - w) = outlen`
            then SUBST1_TAC(SYM th) else NO_TAC) THEN
          REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
          REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
          REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
          MATCH_MP_TAC SQUEEZE_CHUNK THEN
          ASM_REWRITE_TAC[] THEN UNDISCH_TAC `outlen - w < r - p` THEN
          ARITH_TAC;
          ASM_REWRITE_TAC[mld_keccak_squeeze_state] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];
          MP_TAC(SPECL [`pos:num`; `outlen:num`; `w:num`; `p:num`;
                        `r * (b0 + nb)`] SQZ_END2) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
          MP_TAC(SPECL [`p:num`; `outlen - w`] SQZ_ZX_ADD) THEN
          ANTS_TAC THENL
           [UNDISCH_TAC `outlen - w < r - p` THEN UNDISCH_TAC `r <= 200` THEN
            ARITH_TAC; DISCH_TAC] THEN
          MP_TAC(SPEC `p + (outlen - w)` SQZ_ZX2) THEN
          ANTS_TAC THENL
           [UNDISCH_TAC `outlen - w < r - p` THEN UNDISCH_TAC `r <= 200` THEN
            ARITH_TAC; DISCH_TAC] THEN
          ASM_REWRITE_TAC[mld_keccak_squeeze_state] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]];
        SQZ_EVENTS_TAC [`p:num`; `w:num`; `nb:num`; `b0:num`]]]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_FULL);;
