(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing bytes from a SHAKE256 context: the proof (see                   *)
(* shake256_squeeze_spec.ml).                                                *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/shake256_squeeze_spec.ml";;
needs "x86/proofs/utils/mldsa_native_squeeze.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The 32-bit arithmetic on the position and the rate.                       *)
(* ------------------------------------------------------------------------- *)

let SQUEEZE_ZF_POS_LT = prove
 (`!p. p < 136
       ==> (val(word_sub (word_zx (word p:int64):int32) (word 136)) = 0
            <=> F)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `p < 136 ==> p < 4294967296 /\ p < 18446744073709551616`] THEN
  ASM_ARITH_TAC);;

let SQUEEZE_ZF_POS_EQ = prove
 (`!p. p = 136
       ==> (val(word_sub (word_zx (word p:int64):int32) (word 136)) = 0
            <=> T)`,
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_REDUCE_CONV);;

let SQUEEZE_ZX_SUB_RATE = prove
 (`!p. p <= 136
       ==> word_zx(word_sub (word 136) (word_zx (word p:int64):int32)):int64 =
           word(136 - p)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_SUB_CASES;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `p <= 136 ==> p < 4294967296 /\ p < 18446744073709551616 /\
                136 - p < 4294967296 /\ 136 - p < 18446744073709551616`]);;

let SQUEEZE_ZX_SMALL = prove
 (`!x. x <= 136 ==> word_zx(word x:int64):int32 = word x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `x <= 136 ==> x < 4294967296 /\ x < 18446744073709551616`]);;

let SQUEEZE_VAL_WORD_RATE = prove
 (`!x. x <= 200 ==> val(word x:int64) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

let SQUEEZE_VAL_OUTLEN = prove
 (`204 + outlen <= 18446744073709551616 ==> val(word outlen:int64) = outlen`,
  DISCH_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The blocks of the stream that the output touches: with b0 = pos DIV 136   *)
(* the index of the block of the position (0, or 1 for pos = 136), the       *)
(* output is in blocks b0 to b0 + nb, with nb = (pos + outlen - 1) DIV 136 - *)
(* b0, and the last block holds 136 bytes of it exactly when                 *)
(* (pos + outlen) MOD 136 = 0.                                               *)
(* ------------------------------------------------------------------------- *)

let SHAKE_SQUEEZE_BLOCKS = prove
 (`!pos outlen.
        pos <= 136 /\ ~(outlen = 0)
        ==> (pos DIV 136 = 0 /\ pos < 136 \/
             pos DIV 136 = 1 /\ ~(pos < 136)) /\
            136 * pos DIV 136 <= pos /\ pos - 136 * pos DIV 136 < 136 /\
            (pos + outlen - 1) DIV 136 =
            pos DIV 136 + ((pos + outlen - 1) DIV 136 - pos DIV 136) /\
            136 * (pos DIV 136 + ((pos + outlen - 1) DIV 136 - pos DIV 136)) <
            pos + outlen /\
            pos + outlen <=
            136 * (pos DIV 136 + ((pos + outlen - 1) DIV 136 - pos DIV 136) +
                   1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pos DIV 136 = if pos < 136 then 0 else 1` SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_SIMP_TAC[DIV_LT] THEN
    SUBGOAL_THEN `pos = 136` SUBST1_TAC THENL
     [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(pos < 136) ==> 1 <= (pos + outlen - 1) DIV 136`
  MP_TAC THENL
   [SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`pos + outlen - 1`; `136`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(pos + outlen - 1) DIV 136`,`q:num`) THEN
  SPEC_TAC(`(pos + outlen - 1) MOD 136`,`r:num`) THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let SHAKE_SQUEEZE_LAST = prove
 (`!q t. 0 < t /\ t <= 136 ==> ((136 * q + t) MOD 136 = 0 <=> t = 136)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `t = 136` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[ARITH_RULE `136 * q + 136 = 136 * (q + 1)`] THEN
    REWRITE_TAC[MOD_MULT];
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MULT_ADD] THEN
    SUBGOAL_THEN `t MOD 136 = t` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

let SQUEEZE_KECCAK_SQUEEZE_1 = prove
 (`!S:1600 word. keccak_squeeze 1 S = keccak_f1600 S`,
  REWRITE_TAC[ONE; keccak_squeeze]);;


(*** The new position computed by the 32-bit LEA, p plus the bytes left ***)

let SQUEEZE_LEA32_SMALL = prove
 (`!p x. p + x < 2 EXP 32
         ==> word_zx(word_sx(word_add (word p) (word x):int64):int32):int64 =
             word(p + x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!y:int64. word_sx y:int32 = word_zx y`
   (fun th -> REWRITE_TAC[th]) THENL [BITBLAST_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `x < 4294967296 ==> x < 18446744073709551616`]);;

(* ------------------------------------------------------------------------- *)
(* The calls, with the FULL theorems of the callees assumed as "H_EXTRACT"   *)
(* and "H_PERMUTE", and the rewriting of the flags of a comparison with      *)
(* facts that must not rewrite the assumptions of the same comparison.       *)
(* ------------------------------------------------------------------------- *)

let SHAKE256_SQUEEZE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
     (mldsa_native_libmldsa_gcc12_O2_mc,
      MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_EXEC,
      0x0,mldsa_native_libmldsa_gcc12_O2_mc,th)
     (`e:(uarch_event)list`::ilist) n THENL
     [EXISTS_E2_FEV_TAC
       [`out:int64`; `outlen:num`; `ctx:int64`; `pos:num`; `pc:num`;
        `stackpointer:int64`; `returnaddress:int64`; `i:num`; `nb:num`;
        `b0:num`; `p:num`; `w:num`];
      LABEL_TAC name th]);;

let FLAGS_REWRITE_TAC ths =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> t = `CF` || t = `ZF`)) (concl th)
    then REWRITE_RULE ths th else th);;

(* ------------------------------------------------------------------------- *)
(* The state at join2, before the extraction from block b0 + k (as the       *)
(* loop invariant, the state at the start of iteration k): w = 0 or          *)
(* 136 * (b0 + k) - pos bytes are written, and the next ones come from byte  *)
(* p = pos - 136 * b0 or 0 of the state after b0 + k permutations. The       *)
(* stack pointer is at the bottom of the 320 bytes of the stack, with the    *)
(* six registers saved at stackpointer + 272 to 312.                         *)
(* ------------------------------------------------------------------------- *)

let SQUEEZE_INV =
 `\k s. read R13 s = ctx /\ read R14 s = out /\
        read RDX s = word(if k = 0 then pos - 136 * b0 else 0) /\
        read RBP s = word(136 - (if k = 0 then pos - 136 * b0 else 0)) /\
        read RCX s = word(136 - (if k = 0 then pos - 136 * b0 else 0)) /\
        read R15 s = word(if k = 0 then 0 else 136 * (b0 + k) - pos) /\
        read RBX s =
        word(outlen - (if k = 0 then 0 else 136 * (b0 + k) - pos)) /\
        read RSP s = word_add stackpointer (word 264) /\
        read (memory :> bytes64 (word_add stackpointer (word 272))) s =
        rbx_init /\
        read (memory :> bytes64 (word_add stackpointer (word 280))) s =
        rbp_init /\
        read (memory :> bytes64 (word_add stackpointer (word 288))) s =
        r12_init /\
        read (memory :> bytes64 (word_add stackpointer (word 296))) s =
        r13_init /\
        read (memory :> bytes64 (word_add stackpointer (word 304))) s =
        r14_init /\
        read (memory :> bytes64 (word_add stackpointer (word 312))) s =
        r15_init /\
        read (memory :> bytes64 (word_add stackpointer (word 320))) s =
        returnaddress /\
        read (memory :> bytes32(word_add ctx (word 200))) s = word pos /\
        read (memory :> bytes(ctx,200)) s = val(keccak_squeeze (b0 + k) S) /\
        read (memory :> bytes(out,if k = 0 then 0 else 136 * (b0 + k) - pos))
          s =
        num_of_bytelist
         (list_of_seq (mld_keccak_squeeze_byte 136 S pos)
                      (if k = 0 then 0 else 136 * (b0 + k) - pos))`;;

let SQUEEZE_INV_AT t = rand(concl(BETA_CONV(mk_comb(SQUEEZE_INV,t))));;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. With no output nothing      *)
(* changes. Otherwise the code runs to join2, permuting first if pos = 136,  *)
(* then the loop at join2 copies the rest of the nb blocks before the last   *)
(* one and permutes after each (each iteration takes the same path, with     *)
(* arguments of the call that depend on the iteration and on pos), and the   *)
(* last block is copied, with the same path whether it is in the loop or     *)
(* not, except for the branch on whether the output ends with the block.     *)
(* The abbreviations are expanded before the events are unified with the     *)
(* template.                                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_EXEC in
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
        (if (pos + outlen) MOD 136 = 0
         then f_ev_lastf out outlen ctx pos pc stackpointer returnaddress
         else f_ev_lastp out outlen ctx pos pc stackpointer returnaddress)
        (APPEND
          (if (pos + outlen - 1) DIV 136 - pos DIV 136 = 0
           then f_ev_one out outlen ctx pos pc stackpointer returnaddress
           else
            APPEND
             (f_ev_epil out outlen ctx pos pc stackpointer returnaddress)
             (APPEND
               (ENUMERATEL ((pos + outlen - 1) DIV 136 - pos DIV 136)
                 (\i. f_ev_loop out outlen ctx pos pc stackpointer
                                returnaddress i))
               (f_ev_front out outlen ctx pos pc stackpointer
                           returnaddress)))
          (if pos < 136
           then f_ev_heada out outlen ctx pos pc stackpointer returnaddress
           else f_ev_headb out outlen ctx pos pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `204 + outlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(ctx:int64)`; `val(out:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun (n,c) -> ENSURES_PRESERVED_TAC n c)
   [("rbx_init",`RBX`); ("rbp_init",`RBP`); ("r12_init",`R12`);
    ("r13_init",`R13`); ("r14_init",`R14`); ("r15_init",`R15`)] THEN
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
    X86_STEPS_TAC EXEC (1--20) THEN ENSURES_FINAL_STATE_TAC THEN
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

  (*** The blocks, and the state at join2 before the last block ***)

  MP_TAC(SPECL [`pos:num`; `outlen:num`] SHAKE_SQUEEZE_BLOCKS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `nb = (pos + outlen - 1) DIV 136 - pos DIV 136` THEN
  ABBREV_TAC `b0 = pos DIV 136` THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_shake256_squeeze_join2`
    (SQUEEZE_INV_AT `nb:num`) THEN
  CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_shake256_squeeze_join2`
      (SQUEEZE_INV_AT `0`) THEN
    CONJ_TAC THENL
     [(*** To join2, with the permutation first if pos = 136 ***)

      FIRST_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
                  check (is_disj o concl)) THEN
      ASM_REWRITE_TAC[] THEN
      FULL_INIT_TAC THEN X86_STEPS_TAC EXEC (1--10) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[UNDISCH SQUEEZE_VAL_OUTLEN;
                                  ASSUME `~(outlen = 0)`]) THEN
      X86_STEPS_TAC EXEC (11--16) THEN ARGS_64_TAC [`pos:num`] THENL
       [RULE_ASSUM_TAC(REWRITE_RULE
         [MP (SPEC `pos:num` SQUEEZE_ZF_POS_LT) (ASSUME `pos < 136`)]) THEN
        X86_STEPS_TAC EXEC (17--21) THEN
        RULE_ASSUM_TAC(REWRITE_RULE
         [MP (SPEC `pos:num` SQUEEZE_ZX_SUB_RATE) (ASSUME `pos <= 136`)]) THEN
        ARGS_32_TAC [`136 - pos`; `pos:num`] THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; keccak_squeeze;
                        list_of_seq; num_of_bytelist;
                        READ_MEMORY_BYTES_TRIVIAL] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;
        RULE_ASSUM_TAC(REWRITE_RULE
         [MP (SPEC `pos:num` SQUEEZE_ZF_POS_EQ)
             (MP (ARITH_RULE `pos <= 136 /\ ~(pos < 136) ==> pos = 136`)
                 (CONJ (ASSUME `pos <= 136`) (ASSUME `~(pos < 136)`)))]) THEN
        X86_STEPS_TAC EXEC (17--20) THEN
        KECCAK_STATE_AT_TAC `ctx:int64` THEN
        SHAKE256_SQUEEZE_CALL_TAC "H_PERMUTE"
         [`read RDI s`; `S:1600 word`; `pc:num`;
          `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] 21 THEN
        RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
        X86_STEPS_TAC EXEC (22--24) THEN
        SUBGOAL_THEN `pos - 136 = 0` ASSUME_TAC THENL
         [UNDISCH_TAC `pos <= 136` THEN ARITH_TAC; ALL_TAC] THEN
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
       `pc + mldsa_shake256_squeeze_join2` `pc + mldsa_shake256_squeeze_join2`
       SQUEEZE_INV THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];

        FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;

        (*** Block b0 + i: copy the bytes from p on, and permute ***)

        X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
        ABBREV_TAC `p = if i = 0 then pos - 136 * b0 else 0` THEN
        ABBREV_TAC `w = if i = 0 then 0 else 136 * (b0 + i) - pos` THEN
        SUBGOAL_THEN
         `p < 136 /\ pos + w = 136 * (b0 + i) + p /\
          w + (136 - p) = 136 * (b0 + i + 1) - pos /\
          w + (136 - p) < outlen /\
          (if i + 1 = 0 then 0 else 136 * (b0 + i + 1) - pos) =
          w + (136 - p) /\
          (if i + 1 = 0 then pos - 136 * b0 else 0) = 0`
        STRIP_ASSUME_TAC THENL
         [MAP_EVERY EXPAND_TAC ["p"; "w"] THEN
          REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
          SUBGOAL_THEN `136 * (b0 + i + 1) <= 136 * (b0 + nb)` MP_TAC THENL
           [REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `i < nb` THEN
            ARITH_TAC;
            ALL_TAC] THEN
          MAP_EVERY UNDISCH_TAC
           [`136 * (b0 + nb) < pos + outlen`; `pos - 136 * b0 < 136`;
            `136 * b0 <= pos`; `pos <= 136`] THEN
          COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
           [ARITH_TAC;
            SUBGOAL_THEN `136 <= 136 * i` MP_TAC THENL
             [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `136 = 136 * 1`] THEN
              REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `~(i = 0)` THEN
              ARITH_TAC;
              ARITH_TAC]];
          ALL_TAC] THEN
        FULL_INIT_TAC THEN X86_STEPS_TAC EXEC (1--2) THEN
        SUBGOAL_THEN `val(word(outlen - w):int64) = outlen - w /\
                      val(word(136 - p):int64) = 136 - p`
         (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; VAL_WORD_SUB_EQ_0])) THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC SQUEEZE_VAL_WORD_LE THEN EXISTS_TAC `outlen:num` THEN
            ASM_REWRITE_TAC[] THEN ARITH_TAC;
            MATCH_MP_TAC SQUEEZE_VAL_WORD_RATE THEN ARITH_TAC];
          ALL_TAC] THEN
        SUBGOAL_THEN
         `(outlen - w < 136 - p <=> F) /\ (outlen - w = 136 - p <=> F)`
         (fun th -> FLAGS_REWRITE_TAC[th]) THENL
         [UNDISCH_TAC `w + (136 - p) < outlen` THEN ARITH_TAC; ALL_TAC] THEN
        X86_STEPS_TAC EXEC (3--7) THEN
        SUBGOAL_THEN `p + (136 - p) <= 200 /\ w + (136 - p) <= outlen`
        STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `p < 136` THEN UNDISCH_TAC `w + (136 - p) < outlen` THEN
          ARITH_TAC;
          ALL_TAC] THEN
        KECCAK_STATE_AT_TAC `ctx:int64` THEN
        SHAKE256_SQUEEZE_CALL_TAC "H_EXTRACT"
         [`read RDI s`; `read RSI s`; `p:num`;
          `136 - p`; `keccak_squeeze (b0 + i) (S:1600 word)`; `pc:num`;
          `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] 8 THEN
        SUBGOAL_THEN `val(word w:int64) = w` (fun th ->
          RULE_ASSUM_TAC(REWRITE_RULE[th; MULT_CLAUSES])) THENL
         [MATCH_MP_TAC SQUEEZE_VAL_WORD_LE THEN EXISTS_TAC `outlen:num` THEN
          ASM_REWRITE_TAC[] THEN UNDISCH_TAC `w + (136 - p) < outlen` THEN
          ARITH_TAC;
          ALL_TAC] THEN
        X86_STEPS_TAC EXEC (9--10) THEN
        SUBGOAL_THEN `val(word(outlen - w):int64) = outlen - w /\
                      val(word(136 - p):int64) = 136 - p /\
                      (outlen - w = 136 - p <=> F)`
         (fun th -> FLAGS_REWRITE_TAC[VAL_WORD_SUB_EQ_0; th] THEN
                    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0; th])) THENL
         [REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC SQUEEZE_VAL_WORD_LE THEN EXISTS_TAC `outlen:num` THEN
            ASM_REWRITE_TAC[] THEN ARITH_TAC;
            MATCH_MP_TAC SQUEEZE_VAL_WORD_RATE THEN ARITH_TAC;
            UNDISCH_TAC `w + (136 - p) < outlen` THEN ARITH_TAC];
          ALL_TAC] THEN
        X86_STEPS_TAC EXEC (11--15) THEN
        KECCAK_STATE_AT_TAC `ctx:int64` THEN
        SHAKE256_SQUEEZE_CALL_TAC "H_PERMUTE"
         [`read RDI s`; `keccak_squeeze (b0 + i) (S:1600 word)`; `pc:num`;
          `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] 16 THEN
        RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
        X86_STEPS_TAC EXEC (17--19) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
         [REWRITE_TAC[COND_ID];
          REWRITE_TAC[SUB_0];
          REWRITE_TAC[SUB_0];
          REWRITE_TAC[GSYM WORD_ADD] THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[GSYM(ASSUME
            `w + (136 - p) = 136 * (b0 + i + 1) - pos`)] THEN
          REWRITE_TAC[ARITH_RULE `outlen - (w + d) = outlen - w - d`] THEN
          REWRITE_TAC[WORD_SUB] THEN
          SUBGOAL_THEN `136 - p <= outlen - w` (fun th -> REWRITE_TAC[th]) THEN
          UNDISCH_TAC `w + (136 - p) < outlen` THEN ARITH_TAC;
          REWRITE_TAC[ADD_ASSOC; GSYM ADD1; keccak_squeeze];
          REWRITE_TAC[GSYM(ASSUME
            `w + (136 - p) = 136 * (b0 + i + 1) - pos`)] THEN
          REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
          REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
          REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
          MATCH_MP_TAC SQUEEZE_CHUNK THEN
          ASM_REWRITE_TAC[ARITH_RULE `0 < 136 /\ 136 <= 200`] THEN
          UNDISCH_TAC `p < 136` THEN ARITH_TAC;
          UNABBREV_VARS_TAC [`p:num`; `w:num`; `nb:num`; `b0:num`] THEN
          DISCHARGE_SAFETY_PROPERTY_SPINE_TAC];

        (*** The exit of the loop, at join2 ***)

        ASM_REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_SPINE_TAC]];

    (*** The last block, with the bytes from p on, up to its end or not ***)

    ABBREV_TAC `p = if nb = 0 then pos - 136 * b0 else 0` THEN
    ABBREV_TAC `w = if nb = 0 then 0 else 136 * (b0 + nb) - pos` THEN
    SUBGOAL_THEN
     `p < 136 /\ pos + w = 136 * (b0 + nb) + p /\ w < outlen /\
      p + (outlen - w) <= 136 /\ w + (outlen - w) = outlen`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["p"; "w"] THEN
      MAP_EVERY UNDISCH_TAC
       [`~(outlen = 0)`; `136 * (b0 + nb) < pos + outlen`;
        `pos + outlen <= 136 * (b0 + nb + 1)`; `pos - 136 * b0 < 136`;
        `136 * b0 <= pos`; `pos <= 136`] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
       [ARITH_TAC;
        SUBGOAL_THEN `136 <= 136 * nb` MP_TAC THENL
         [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `136 = 136 * 1`] THEN
          REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `~(nb = 0)` THEN
          ARITH_TAC;
          ARITH_TAC]];
      ALL_TAC] THEN
    MP_TAC(SPECL [`b0 + nb`; `p + (outlen - w)`] SHAKE_SQUEEZE_LAST) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `w < outlen` THEN UNDISCH_TAC `p + (outlen - w) <= 136` THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `136 * (b0 + nb) + p + (outlen - w) = pos + outlen`
     SUBST1_TAC THENL
     [UNDISCH_TAC `pos + w = 136 * (b0 + nb) + p` THEN
      UNDISCH_TAC `w < outlen` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    ASM_CASES_TAC `(pos + outlen) MOD 136 = 0` THENL
     [(*** To the end of the block: the jump to the copy is taken ***)

      REWRITE_TAC[EQT_INTRO(ASSUME `(pos + outlen) MOD 136 = 0`)] THEN
      SUBGOAL_THEN `outlen - w = 136 - p` ASSUME_TAC THENL
       [UNDISCH_TAC `(pos + outlen) MOD 136 = 0 <=> p + (outlen - w) = 136` THEN
        ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      FULL_INIT_TAC THEN X86_STEPS_TAC EXEC (1--7) THEN
      SUBGOAL_THEN `p + (136 - p) <= 200 /\ w + (136 - p) <= outlen`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `p < 136` THEN UNDISCH_TAC `w + (outlen - w) = outlen` THEN
        UNDISCH_TAC `outlen - w = 136 - p` THEN ARITH_TAC; ALL_TAC] THEN
      KECCAK_STATE_AT_TAC `ctx:int64` THEN
      SHAKE256_SQUEEZE_CALL_TAC "H_EXTRACT"
       [`read RDI s`; `read RSI s`; `p:num`; `136 - p`;
        `keccak_squeeze (b0 + nb) (S:1600 word)`; `pc:num`;
        `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] 8 THEN
      SUBGOAL_THEN `val(word w:int64) = w` (fun th ->
        RULE_ASSUM_TAC(REWRITE_RULE[th; MULT_CLAUSES])) THENL
       [MATCH_MP_TAC SQUEEZE_VAL_WORD_LE THEN EXISTS_TAC `outlen:num` THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `w < outlen` THEN ARITH_TAC;
        ALL_TAC] THEN
      X86_STEPS_TAC EXEC (9--19) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `(a /\ b /\ c) /\ d ==> a /\ b /\ c /\ d`) THEN
      CONJ_TAC THENL
       [REPEAT CONJ_TAC THENL
         [SUBGOAL_THEN `outlen = w + (136 - p)` SUBST1_TAC THENL
           [UNDISCH_TAC `w + (outlen - w) = outlen` THEN
            UNDISCH_TAC `outlen - w = 136 - p` THEN ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
          REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
          REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
          MATCH_MP_TAC SQUEEZE_CHUNK THEN
          ASM_REWRITE_TAC[ARITH_RULE `0 < 136 /\ 136 <= 200`] THEN
          UNDISCH_TAC `p < 136` THEN ARITH_TAC;
          ASM_REWRITE_TAC[mld_keccak_squeeze_state] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[mld_keccak_squeeze_state] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
          AP_TERM_TAC THEN
          UNDISCH_TAC `pos + w = 136 * (b0 + nb) + p` THEN
          UNDISCH_TAC `w + (outlen - w) = outlen` THEN
          UNDISCH_TAC `outlen - w = 136 - p` THEN UNDISCH_TAC `p < 136` THEN
          ARITH_TAC];
        UNABBREV_VARS_TAC [`p:num`; `w:num`; `nb:num`; `b0:num`] THEN
        DISCHARGE_SAFETY_PROPERTY_SPINE_TAC];

      (*** Before the end of the block: the length is the rest ***)

      REWRITE_TAC[EQF_INTRO(ASSUME `~((pos + outlen) MOD 136 = 0)`)] THEN
      SUBGOAL_THEN `outlen - w < 136 - p` ASSUME_TAC THENL
       [UNDISCH_TAC `(pos + outlen) MOD 136 = 0 <=> p + (outlen - w) = 136` THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `p + (outlen - w) <= 136` THEN
        ARITH_TAC; ALL_TAC] THEN
      FULL_INIT_TAC THEN X86_STEPS_TAC EXEC (1--2) THEN
      SUBGOAL_THEN
       `val(word(outlen - w):int64) = outlen - w /\
        val(word(136 - p):int64) = 136 - p /\
        (outlen - w < 136 - p <=> T) /\ (outlen - w = 136 - p <=> F)`
       (fun th -> FLAGS_REWRITE_TAC[VAL_WORD_SUB_EQ_0; th]) THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC SQUEEZE_VAL_WORD_LE THEN EXISTS_TAC `outlen:num` THEN
          ASM_REWRITE_TAC[] THEN ARITH_TAC;
          MATCH_MP_TAC SQUEEZE_VAL_WORD_RATE THEN ARITH_TAC;
          UNDISCH_TAC `outlen - w < 136 - p` THEN ARITH_TAC;
          UNDISCH_TAC `outlen - w < 136 - p` THEN ARITH_TAC];
        ALL_TAC] THEN
      X86_STEPS_TAC EXEC (3--9) THEN
      SUBGOAL_THEN `val(word w:int64) = w /\
                    val(word(outlen - w):int64) = outlen - w`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; MULT_CLAUSES])) THENL
       [CONJ_TAC THEN MATCH_MP_TAC SQUEEZE_VAL_WORD_LE THEN
        EXISTS_TAC `outlen:num` THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `w < outlen` THEN ARITH_TAC;
        ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [MP (SPECL [`p:num`; `outlen - w`] SQUEEZE_LEA32_SMALL)
           (MP (ARITH_RULE
                 `outlen - w < 136 - p ==> p + (outlen - w) < 2 EXP 32`)
               (ASSUME `outlen - w < 136 - p`))]) THEN
      ARGS_32_TAC [`outlen - w`] THEN
      SUBGOAL_THEN `p + (outlen - w) <= 200 /\ w + (outlen - w) <= outlen`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `outlen - w < 136 - p` THEN
        UNDISCH_TAC `w + (outlen - w) = outlen` THEN ARITH_TAC;
        ALL_TAC] THEN
      X86_STEPS_TAC EXEC (10--10) THEN
      KECCAK_STATE_AT_TAC `ctx:int64` THEN
      SHAKE256_SQUEEZE_CALL_TAC "H_EXTRACT"
       [`read RDI s`; `read RSI s`; `p:num`;
        `outlen - w`; `keccak_squeeze (b0 + nb) (S:1600 word)`; `pc:num`;
        `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] 11 THEN
      X86_STEPS_TAC EXEC (12--22) THEN
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
          ASM_REWRITE_TAC[ARITH_RULE `0 < 136 /\ 136 <= 200`] THEN
          UNDISCH_TAC `outlen - w < 136 - p` THEN ARITH_TAC;
          ASM_REWRITE_TAC[mld_keccak_squeeze_state] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[mld_keccak_squeeze_state] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `(pos + outlen) - 136 * (b0 + nb) = p + (outlen - w)`
           SUBST1_TAC THENL
           [UNDISCH_TAC `pos + w = 136 * (b0 + nb) + p` THEN
            UNDISCH_TAC `w + (outlen - w) = outlen` THEN ARITH_TAC;
            MATCH_MP_TAC SQUEEZE_ZX_SMALL THEN
            UNDISCH_TAC `outlen - w < 136 - p` THEN ARITH_TAC]];
        UNABBREV_VARS_TAC [`p:num`; `w:num`; `nb:num`; `b0:num`] THEN
        DISCHARGE_SAFETY_PROPERTY_SPINE_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
