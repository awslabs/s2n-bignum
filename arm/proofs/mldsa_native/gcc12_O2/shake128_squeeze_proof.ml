(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing bytes from a SHAKE128 context: the proof (see                   *)
(* shake128_squeeze_spec.ml).                                                *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/shake128_squeeze_spec.ml";;
needs "arm/proofs/utils/mldsa_native_squeeze.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The 32-bit arithmetic on the position and the rate.                       *)
(* ------------------------------------------------------------------------- *)

let SQUEEZE_ZF_POS_LT = prove
 (`!p. p < 168
       ==> (val(word_sub (word_zx (word p:int64):int32) (word 168)) = 0
            <=> F)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `p < 168 ==> p < 4294967296 /\ p < 18446744073709551616`] THEN
  ASM_ARITH_TAC);;

let SQUEEZE_ZF_POS_EQ = prove
 (`!p. p = 168
       ==> (val(word_sub (word_zx (word p:int64):int32) (word 168)) = 0
            <=> T)`,
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_REDUCE_CONV);;

let SQUEEZE_ZX2_SMALL = prove
 (`!p. p < 2 EXP 32 ==> word_zx(word_zx(word p:int64):int32):int64 = word p`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `p < 4294967296 ==> p < 18446744073709551616`]);;

let SQUEEZE_ZX_ADD_SMALL = prove
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

let SQUEEZE_ZX_SUB_RATE = prove
 (`!p. p <= 168
       ==> word_zx(word_sub (word 168) (word_zx (word p:int64):int32)):int64 =
           word(168 - p)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_SUB_CASES;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `p <= 168 ==> p < 4294967296 /\ p < 18446744073709551616 /\
                168 - p < 4294967296 /\ 168 - p < 18446744073709551616`]);;

let SQUEEZE_ZX_SMALL = prove
 (`!x. x <= 168 ==> word_zx(word x:int64):int32 = word x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `x <= 168 ==> x < 4294967296 /\ x < 18446744073709551616`]);;

let SQUEEZE_VAL_WORD_RATE = prove
 (`!x. x <= 200 ==> val(word x:int64) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

let SQUEEZE_VAL_OUTLEN = prove
 (`204 + outlen <= 18446744073709551616 ==> val(word outlen:int64) = outlen`,
  DISCH_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The blocks of the stream that the output touches: with b0 = pos DIV 168   *)
(* the index of the block of the position (0, or 1 for pos = 168), the       *)
(* output is in blocks b0 to b0 + nb, with nb = (pos + outlen - 1) DIV 168 - *)
(* b0, and the last block holds 168 bytes of it exactly when                 *)
(* (pos + outlen) MOD 168 = 0.                                               *)
(* ------------------------------------------------------------------------- *)

let SHAKE_SQUEEZE_BLOCKS = prove
 (`!pos outlen.
        pos <= 168 /\ ~(outlen = 0)
        ==> (pos DIV 168 = 0 /\ pos < 168 \/
             pos DIV 168 = 1 /\ ~(pos < 168)) /\
            168 * pos DIV 168 <= pos /\ pos - 168 * pos DIV 168 < 168 /\
            (pos + outlen - 1) DIV 168 =
            pos DIV 168 + ((pos + outlen - 1) DIV 168 - pos DIV 168) /\
            168 * (pos DIV 168 + ((pos + outlen - 1) DIV 168 - pos DIV 168)) <
            pos + outlen /\
            pos + outlen <=
            168 * (pos DIV 168 + ((pos + outlen - 1) DIV 168 - pos DIV 168) +
                   1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pos DIV 168 = if pos < 168 then 0 else 1` SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_SIMP_TAC[DIV_LT] THEN
    SUBGOAL_THEN `pos = 168` SUBST1_TAC THENL
     [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(pos < 168) ==> 1 <= (pos + outlen - 1) DIV 168`
  MP_TAC THENL
   [SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`pos + outlen - 1`; `168`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(pos + outlen - 1) DIV 168`,`q:num`) THEN
  SPEC_TAC(`(pos + outlen - 1) MOD 168`,`r:num`) THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let SHAKE_SQUEEZE_LAST = prove
 (`!q t. 0 < t /\ t <= 168 ==> ((168 * q + t) MOD 168 = 0 <=> t = 168)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `t = 168` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[ARITH_RULE `168 * q + 168 = 168 * (q + 1)`] THEN
    REWRITE_TAC[MOD_MULT];
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MULT_ADD] THEN
    SUBGOAL_THEN `t MOD 168 = t` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

let SQUEEZE_KECCAK_SQUEEZE_1 = prove
 (`!S:1600 word. keccak_squeeze 1 S = keccak_f1600 S`,
  REWRITE_TAC[ONE; keccak_squeeze]);;

(* ------------------------------------------------------------------------- *)
(* The calls, with the FULL theorems of the callees assumed as "H_EXTRACT"   *)
(* and "H_PERMUTE".                                                          *)
(* ------------------------------------------------------------------------- *)

let SHAKE128_SQUEEZE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
     (mldsa_native_libmldsa_gcc12_O2_mc,
      MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_O2_EXEC,
      0x0,mldsa_native_libmldsa_gcc12_O2_mc,th)
     ilist n THENL
     [EXISTS_E2_FEV_TAC
       [`out:int64`; `outlen:num`; `ctx:int64`; `pos:num`; `pc:num`;
        `stackpointer:int64`; `returnaddress:int64`; `i:num`; `nb:num`;
        `b0:num`; `p:num`; `w:num`];
      LABEL_TAC name th]);;

(* ------------------------------------------------------------------------- *)
(* The state at join1, before the extraction from block b0 + k (as the       *)
(* loop invariant, the state at the start of iteration k): w = 0 or          *)
(* 168 * (b0 + k) - pos bytes are written, and the next ones come from byte  *)
(* p = pos - 168 * b0 or 0 of the state after b0 + k permutations.           *)
(* ------------------------------------------------------------------------- *)

let SQUEEZE_INV =
 `\k s. read X23 s = ctx /\ read X25 s = out /\ read X24 s = word 168 /\
        read X4 s = word(if k = 0 then pos - 168 * b0 else 0) /\
        read X20 s = word(168 - (if k = 0 then pos - 168 * b0 else 0)) /\
        read X3 s = word(168 - (if k = 0 then pos - 168 * b0 else 0)) /\
        read X22 s = word(if k = 0 then 0 else 168 * (b0 + k) - pos) /\
        read X19 s =
        word(outlen - (if k = 0 then 0 else 168 * (b0 + k) - pos)) /\
        read SP s = word_add stackpointer (word 192) /\
        read (memory :> bytes64 (word_add stackpointer (word 192))) s =
        x19_init /\
        read (memory :> bytes64 (word_add stackpointer (word 200))) s =
        x20_init /\
        read (memory :> bytes64 (word_add stackpointer (word 208))) s =
        x21_init /\
        read (memory :> bytes64 (word_add stackpointer (word 216))) s =
        x22_init /\
        read (memory :> bytes64 (word_add stackpointer (word 224))) s =
        x23_init /\
        read (memory :> bytes64 (word_add stackpointer (word 232))) s =
        x24_init /\
        read (memory :> bytes64 (word_add stackpointer (word 240))) s =
        x25_init /\
        read (memory :> bytes64 (word_add stackpointer (word 248))) s =
        returnaddress /\
        read (memory :> bytes32(word_add ctx (word 200))) s = word pos /\
        read (memory :> bytes(ctx,200)) s = val(keccak_squeeze (b0 + k) S) /\
        read (memory :> bytes(out,if k = 0 then 0 else 168 * (b0 + k) - pos))
          s =
        num_of_bytelist
         (list_of_seq (mld_keccak_squeeze_byte 168 S pos)
                      (if k = 0 then 0 else 168 * (b0 + k) - pos))`;;

let SQUEEZE_INV_AT t = rand(concl(BETA_CONV(mk_comb(SQUEEZE_INV,t))));;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. With no output nothing      *)
(* changes. Otherwise the code runs to join1, permuting first if pos = 168,  *)
(* then the loop at join1 copies the rest of the nb blocks before the last   *)
(* one and permutes after each (each iteration takes the same path, with     *)
(* arguments of the call that depend on the iteration and on pos), and the   *)
(* last block is copied, with the same path whether it is in the loop or     *)
(* not, except for the branch on whether the output ends with the block.     *)
(* The abbreviations are expanded before the events are unified with the     *)
(* template.                                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_O2_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_EXTRACT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(out:int64) (outlen:num) (ctx:int64) (pos:num) (pc:num)
     (stackpointer:int64) (returnaddress:int64).
      if outlen = 0
      then f_ev_zero out outlen ctx pos pc stackpointer returnaddress
      else
       APPEND
        (if (pos + outlen) MOD 168 = 0
         then f_ev_lastf out outlen ctx pos pc stackpointer returnaddress
         else f_ev_lastp out outlen ctx pos pc stackpointer returnaddress)
        (APPEND
          (if (pos + outlen - 1) DIV 168 - pos DIV 168 = 0
           then f_ev_one out outlen ctx pos pc stackpointer returnaddress
           else
            APPEND
             (f_ev_epil out outlen ctx pos pc stackpointer returnaddress)
             (APPEND
               (ENUMERATEL ((pos + outlen - 1) DIV 168 - pos DIV 168)
                 (\i. f_ev_loop out outlen ctx pos pc stackpointer
                                returnaddress i))
               (f_ev_front out outlen ctx pos pc stackpointer
                           returnaddress)))
          (if pos < 168
           then f_ev_heada out outlen ctx pos pc stackpointer returnaddress
           else f_ev_headb out outlen ctx pos pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `out:int64`; `outlen:num`; `ctx:int64`;
    `S:1600 word`; `pos:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 256 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `204 + outlen <= 18446744073709551616` ASSUME_TAC THENL
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
    ARM_STEPS_TAC EXEC (1--13) THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(a /\ b /\ c) /\ d ==> a /\ b /\ c /\ d`) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `outlen = 0` SUBST1_TAC THENL
       [UNDISCH_TAC `outlen <= 0` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[mld_keccak_squeeze_state; list_of_seq; num_of_bytelist;
                      READ_MEMORY_BYTES_TRIVIAL; WORD_ZX_ZX_32_64_32];
      DISCHARGE_SAFETY_PROPERTY_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[EQF_INTRO(ASSUME `~(outlen = 0)`)] THEN

  (*** The blocks, and the state at join1 before the last block ***)

  MP_TAC(SPECL [`pos:num`; `outlen:num`] SHAKE_SQUEEZE_BLOCKS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `nb = (pos + outlen - 1) DIV 168 - pos DIV 168` THEN
  ABBREV_TAC `b0 = pos DIV 168` THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_shake128_squeeze_join1`
    (SQUEEZE_INV_AT `nb:num`) THEN
  CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_shake128_squeeze_join1`
      (SQUEEZE_INV_AT `0`) THEN
    CONJ_TAC THENL
     [(*** To join1, with the permutation first if pos = 168 ***)

      FIRST_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
                  check (is_disj o concl)) THEN
      ASM_REWRITE_TAC[] THEN
      FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--7) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[UNDISCH SQUEEZE_VAL_OUTLEN;
                                  ASSUME `~(outlen = 0)`]) THEN
      ARM_STEPS_TAC EXEC (8--14) THEN ARGS_64_TAC [`pos:num`] THENL
       [RULE_ASSUM_TAC(REWRITE_RULE
         [MP (SPEC `pos:num` SQUEEZE_ZF_POS_LT) (ASSUME `pos < 168`)]) THEN
        ARM_STEPS_TAC EXEC (15--18) THEN
        RULE_ASSUM_TAC(REWRITE_RULE
         [MP (SPEC `pos:num` SQUEEZE_ZX_SUB_RATE) (ASSUME `pos <= 168`);
          MP (SPEC `pos:num` SQUEEZE_ZX2_SMALL)
             (MP (ARITH_RULE `pos <= 168 ==> pos < 2 EXP 32`)
                 (ASSUME `pos <= 168`))]) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; keccak_squeeze;
                        list_of_seq; num_of_bytelist;
                        READ_MEMORY_BYTES_TRIVIAL] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;
        RULE_ASSUM_TAC(REWRITE_RULE
         [MP (SPEC `pos:num` SQUEEZE_ZF_POS_EQ)
             (MP (ARITH_RULE `pos <= 168 /\ ~(pos < 168) ==> pos = 168`)
                 (CONJ (ASSUME `pos <= 168`) (ASSUME `~(pos < 168)`)))]) THEN
        ARM_STEPS_TAC EXEC (15--17) THEN
        KECCAK_STATE_AT_TAC `ctx:int64` THEN
        SHAKE128_SQUEEZE_CALL_TAC "H_PERMUTE"
         [`e:(uarch_event)list`; `read X0 s`; `S:1600 word`; `pc:num`;
          `read SP s`; `read X30 s`] 18 THEN
        RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
        ARM_STEPS_TAC EXEC (19--22) THEN
        SUBGOAL_THEN `word_zx(word_zx(word pos:int64):int32):int64 = word 168`
         (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
         [SUBST1_TAC(MP (ARITH_RULE `pos <= 168 /\ ~(pos < 168) ==> pos = 168`)
                        (CONJ (ASSUME `pos <= 168`)
                              (ASSUME `~(pos < 168)`))) THEN
          CONV_TAC WORD_REDUCE_CONV;
          ALL_TAC] THEN
        SUBGOAL_THEN `pos - 168 = 0` ASSUME_TAC THENL
         [UNDISCH_TAC `pos <= 168` THEN ARITH_TAC; ALL_TAC] THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0;
                        SQUEEZE_KECCAK_SQUEEZE_1; list_of_seq;
                        num_of_bytelist; READ_MEMORY_BYTES_TRIVIAL] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC];

      (*** The nb blocks before the last, if any ***)

      ASM_CASES_TAC `nb = 0` THEN ASM_REWRITE_TAC[] THENL
       [FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;
        ALL_TAC] THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `nb:num`
       `pc + mldsa_shake128_squeeze_join1` `pc + mldsa_shake128_squeeze_join1`
       SQUEEZE_INV THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];

        FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;

        (*** Block b0 + i: copy the bytes from p on, and permute ***)

        X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
        ABBREV_TAC `p = if i = 0 then pos - 168 * b0 else 0` THEN
        ABBREV_TAC `w = if i = 0 then 0 else 168 * (b0 + i) - pos` THEN
        SUBGOAL_THEN
         `p < 168 /\ pos + w = 168 * (b0 + i) + p /\
          w + (168 - p) = 168 * (b0 + i + 1) - pos /\
          w + (168 - p) < outlen /\
          (if i + 1 = 0 then 0 else 168 * (b0 + i + 1) - pos) =
          w + (168 - p) /\
          (if i + 1 = 0 then pos - 168 * b0 else 0) = 0`
        STRIP_ASSUME_TAC THENL
         [MAP_EVERY EXPAND_TAC ["p"; "w"] THEN
          REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
          SUBGOAL_THEN `168 * (b0 + i + 1) <= 168 * (b0 + nb)` MP_TAC THENL
           [REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `i < nb` THEN
            ARITH_TAC;
            ALL_TAC] THEN
          MAP_EVERY UNDISCH_TAC
           [`168 * (b0 + nb) < pos + outlen`; `pos - 168 * b0 < 168`;
            `168 * b0 <= pos`; `pos <= 168`] THEN
          COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
           [ARITH_TAC;
            SUBGOAL_THEN `168 <= 168 * i` MP_TAC THENL
             [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `168 = 168 * 1`] THEN
              REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `~(i = 0)` THEN
              ARITH_TAC;
              ARITH_TAC]];
          ALL_TAC] THEN
        FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--5) THEN
        RULE_ASSUM_TAC(REWRITE_RULE
         [MP (SPEC `p:num` SQUEEZE_ZX2_SMALL)
             (MP (ARITH_RULE `p < 168 ==> p < 2 EXP 32`)
                 (ASSUME `p < 168`))]) THEN
        SUBGOAL_THEN `val(word(outlen - w):int64) = outlen - w /\
                      val(word(168 - p):int64) = 168 - p`
         (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; VAL_WORD_SUB_EQ_0])) THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC SQUEEZE_VAL_WORD_LE THEN EXISTS_TAC `outlen:num` THEN
            ASM_REWRITE_TAC[] THEN ARITH_TAC;
            MATCH_MP_TAC SQUEEZE_VAL_WORD_RATE THEN ARITH_TAC];
          ALL_TAC] THEN
        SUBGOAL_THEN
         `(outlen - w <= 168 - p <=> F) /\ (168 - p = outlen - w <=> F)`
         (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
         [UNDISCH_TAC `w + (168 - p) < outlen` THEN ARITH_TAC; ALL_TAC] THEN
        ARM_STEPS_TAC EXEC (6--7) THEN
        SUBGOAL_THEN `p + (168 - p) <= 200 /\ w + (168 - p) <= outlen`
        STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `p < 168` THEN UNDISCH_TAC `w + (168 - p) < outlen` THEN
          ARITH_TAC;
          ALL_TAC] THEN
        KECCAK_STATE_AT_TAC `ctx:int64` THEN
        SHAKE128_SQUEEZE_CALL_TAC "H_EXTRACT"
         [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `p:num`;
          `168 - p`; `keccak_squeeze (b0 + i) (S:1600 word)`; `pc:num`;
          `read X30 s`] 8 THEN
        ARM_STEPS_TAC EXEC (9--10) THEN
        SUBGOAL_THEN `val(word(outlen - w):int64) = outlen - w /\
                      val(word(168 - p):int64) = 168 - p /\
                      (outlen - w = 168 - p <=> F)`
         (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0; th])) THENL
         [REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC SQUEEZE_VAL_WORD_LE THEN EXISTS_TAC `outlen:num` THEN
            ASM_REWRITE_TAC[] THEN ARITH_TAC;
            MATCH_MP_TAC SQUEEZE_VAL_WORD_RATE THEN ARITH_TAC;
            UNDISCH_TAC `w + (168 - p) < outlen` THEN ARITH_TAC];
          ALL_TAC] THEN
        ARM_STEPS_TAC EXEC (11--15) THEN
        KECCAK_STATE_AT_TAC `ctx:int64` THEN
        SHAKE128_SQUEEZE_CALL_TAC "H_PERMUTE"
         [`e:(uarch_event)list`; `read X0 s`;
          `keccak_squeeze (b0 + i) (S:1600 word)`; `pc:num`; `read SP s`;
          `read X30 s`] 16 THEN
        RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
        ARM_STEPS_TAC EXEC (17--20) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
         [REWRITE_TAC[COND_ID];
          REWRITE_TAC[SUB_0];
          REWRITE_TAC[SUB_0];
          REWRITE_TAC[GSYM WORD_ADD] THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[GSYM(ASSUME
            `w + (168 - p) = 168 * (b0 + i + 1) - pos`)] THEN
          REWRITE_TAC[ARITH_RULE `outlen - (w + d) = outlen - w - d`] THEN
          REWRITE_TAC[WORD_SUB] THEN
          SUBGOAL_THEN `168 - p <= outlen - w` (fun th -> REWRITE_TAC[th]) THEN
          UNDISCH_TAC `w + (168 - p) < outlen` THEN ARITH_TAC;
          REWRITE_TAC[ADD_ASSOC; GSYM ADD1; keccak_squeeze];
          REWRITE_TAC[GSYM(ASSUME
            `w + (168 - p) = 168 * (b0 + i + 1) - pos`)] THEN
          REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
          REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
          REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
          MATCH_MP_TAC SQUEEZE_CHUNK THEN
          ASM_REWRITE_TAC[ARITH_RULE `0 < 168 /\ 168 <= 200`] THEN
          UNDISCH_TAC `p < 168` THEN ARITH_TAC;
          UNABBREV_VARS_TAC [`p:num`; `w:num`; `nb:num`; `b0:num`] THEN
          DISCHARGE_SAFETY_PROPERTY_SPINE_TAC];

        (*** The exit of the loop, at join1 ***)

        ASM_REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_SPINE_TAC]];

    (*** The last block, with the bytes from p on, up to its end or not ***)

    ABBREV_TAC `p = if nb = 0 then pos - 168 * b0 else 0` THEN
    ABBREV_TAC `w = if nb = 0 then 0 else 168 * (b0 + nb) - pos` THEN
    SUBGOAL_THEN
     `p < 168 /\ pos + w = 168 * (b0 + nb) + p /\ w < outlen /\
      p + (outlen - w) <= 168 /\ w + (outlen - w) = outlen`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["p"; "w"] THEN
      MAP_EVERY UNDISCH_TAC
       [`~(outlen = 0)`; `168 * (b0 + nb) < pos + outlen`;
        `pos + outlen <= 168 * (b0 + nb + 1)`; `pos - 168 * b0 < 168`;
        `168 * b0 <= pos`; `pos <= 168`] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
       [ARITH_TAC;
        SUBGOAL_THEN `168 <= 168 * nb` MP_TAC THENL
         [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `168 = 168 * 1`] THEN
          REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `~(nb = 0)` THEN
          ARITH_TAC;
          ARITH_TAC]];
      ALL_TAC] THEN
    MP_TAC(SPECL [`b0 + nb`; `p + (outlen - w)`] SHAKE_SQUEEZE_LAST) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `w < outlen` THEN UNDISCH_TAC `p + (outlen - w) <= 168` THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `168 * (b0 + nb) + p + (outlen - w) = pos + outlen`
     SUBST1_TAC THENL
     [UNDISCH_TAC `pos + w = 168 * (b0 + nb) + p` THEN
      UNDISCH_TAC `w < outlen` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    ASM_CASES_TAC `(pos + outlen) MOD 168 = 0` THENL
     [(*** To the end of the block: the branch to the copy is taken ***)

      REWRITE_TAC[EQT_INTRO(ASSUME `(pos + outlen) MOD 168 = 0`)] THEN
      SUBGOAL_THEN `outlen - w = 168 - p` ASSUME_TAC THENL
       [UNDISCH_TAC `(pos + outlen) MOD 168 = 0 <=> p + (outlen - w) = 168` THEN
        ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--5) THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [MP (SPEC `p:num` SQUEEZE_ZX2_SMALL)
           (MP (ARITH_RULE `p < 168 ==> p < 2 EXP 32`)
               (ASSUME `p < 168`))]) THEN
      SUBGOAL_THEN `val(word(168 - p):int64) = 168 - p`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; VAL_WORD_SUB_EQ_0;
                                              WORD_SUB_REFL; VAL_WORD_0])) THENL
       [MATCH_MP_TAC SQUEEZE_VAL_WORD_RATE THEN ARITH_TAC; ALL_TAC] THEN
      ARM_STEPS_TAC EXEC (6--7) THEN
      SUBGOAL_THEN `p + (168 - p) <= 200 /\ w + (168 - p) <= outlen`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `p < 168` THEN UNDISCH_TAC `w + (outlen - w) = outlen` THEN
        UNDISCH_TAC `outlen - w = 168 - p` THEN ARITH_TAC; ALL_TAC] THEN
      KECCAK_STATE_AT_TAC `ctx:int64` THEN
      SHAKE128_SQUEEZE_CALL_TAC "H_EXTRACT"
       [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `p:num`; `168 - p`;
        `keccak_squeeze (b0 + nb) (S:1600 word)`; `pc:num`; `read X30 s`] 8 THEN
      ARM_STEPS_TAC EXEC (9--10) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_REFL; VAL_WORD_0]) THEN
      ARM_STEPS_TAC EXEC (11--18) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `(a /\ b /\ c) /\ d ==> a /\ b /\ c /\ d`) THEN
      CONJ_TAC THENL
       [REPEAT CONJ_TAC THENL
         [SUBGOAL_THEN `outlen = w + (168 - p)` SUBST1_TAC THENL
           [UNDISCH_TAC `w + (outlen - w) = outlen` THEN
            UNDISCH_TAC `outlen - w = 168 - p` THEN ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
          REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
          REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
          MATCH_MP_TAC SQUEEZE_CHUNK THEN
          ASM_REWRITE_TAC[ARITH_RULE `0 < 168 /\ 168 <= 200`] THEN
          UNDISCH_TAC `p < 168` THEN ARITH_TAC;
          ASM_REWRITE_TAC[mld_keccak_squeeze_state] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[mld_keccak_squeeze_state] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
          AP_TERM_TAC THEN
          UNDISCH_TAC `pos + w = 168 * (b0 + nb) + p` THEN
          UNDISCH_TAC `w + (outlen - w) = outlen` THEN
          UNDISCH_TAC `outlen - w = 168 - p` THEN UNDISCH_TAC `p < 168` THEN
          ARITH_TAC];
        UNABBREV_VARS_TAC [`p:num`; `w:num`; `nb:num`; `b0:num`] THEN
        DISCHARGE_SAFETY_PROPERTY_SPINE_TAC];

      (*** Before the end of the block: the length is the rest ***)

      REWRITE_TAC[EQF_INTRO(ASSUME `~((pos + outlen) MOD 168 = 0)`)] THEN
      SUBGOAL_THEN `outlen - w < 168 - p` ASSUME_TAC THENL
       [UNDISCH_TAC `(pos + outlen) MOD 168 = 0 <=> p + (outlen - w) = 168` THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `p + (outlen - w) <= 168` THEN
        ARITH_TAC; ALL_TAC] THEN
      FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--5) THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [MP (SPEC `p:num` SQUEEZE_ZX2_SMALL)
           (MP (ARITH_RULE `p < 168 ==> p < 2 EXP 32`)
               (ASSUME `p < 168`))]) THEN
      SUBGOAL_THEN
       `val(word(outlen - w):int64) = outlen - w /\
        val(word(168 - p):int64) = 168 - p /\
        (outlen - w <= 168 - p <=> T) /\ (168 - p = outlen - w <=> F)`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0; th])) THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC SQUEEZE_VAL_WORD_LE THEN EXISTS_TAC `outlen:num` THEN
          ASM_REWRITE_TAC[] THEN ARITH_TAC;
          MATCH_MP_TAC SQUEEZE_VAL_WORD_RATE THEN ARITH_TAC;
          UNDISCH_TAC `outlen - w < 168 - p` THEN ARITH_TAC;
          UNDISCH_TAC `outlen - w < 168 - p` THEN ARITH_TAC];
        ALL_TAC] THEN
      ARM_STEPS_TAC EXEC (6--9) THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [MP (SPEC `outlen - w` SQUEEZE_ZX2_SMALL)
           (MP (ARITH_RULE `outlen - w < 168 - p ==> outlen - w < 2 EXP 32`)
               (ASSUME `outlen - w < 168 - p`));
        MP (SPECL [`p:num`; `outlen - w`] SQUEEZE_ZX_ADD_SMALL)
           (MP (ARITH_RULE
                 `outlen - w < 168 - p ==> p + (outlen - w) < 2 EXP 32`)
               (ASSUME `outlen - w < 168 - p`))]) THEN
      SUBGOAL_THEN `p + (outlen - w) <= 200 /\ w + (outlen - w) <= outlen`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `outlen - w < 168 - p` THEN
        UNDISCH_TAC `w + (outlen - w) = outlen` THEN ARITH_TAC;
        ALL_TAC] THEN
      ARM_STEPS_TAC EXEC (10--10) THEN
      KECCAK_STATE_AT_TAC `ctx:int64` THEN
      SHAKE128_SQUEEZE_CALL_TAC "H_EXTRACT"
       [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `p:num`;
        `outlen - w`; `keccak_squeeze (b0 + nb) (S:1600 word)`; `pc:num`;
        `read X30 s`] 11 THEN
      ARM_STEPS_TAC EXEC (12--13) THEN
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
          ASM_REWRITE_TAC[ARITH_RULE `0 < 168 /\ 168 <= 200`] THEN
          UNDISCH_TAC `outlen - w < 168 - p` THEN ARITH_TAC;
          ASM_REWRITE_TAC[mld_keccak_squeeze_state] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[mld_keccak_squeeze_state] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `(pos + outlen) - 168 * (b0 + nb) = p + (outlen - w)`
           SUBST1_TAC THENL
           [UNDISCH_TAC `pos + w = 168 * (b0 + nb) + p` THEN
            UNDISCH_TAC `w + (outlen - w) = outlen` THEN ARITH_TAC;
            MATCH_MP_TAC SQUEEZE_ZX_SMALL THEN
            UNDISCH_TAC `outlen - w < 168 - p` THEN ARITH_TAC]];
        UNABBREV_VARS_TAC [`p:num`; `w:num`; `nb:num`; `b0:num`] THEN
        DISCHARGE_SAFETY_PROPERTY_SPINE_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
