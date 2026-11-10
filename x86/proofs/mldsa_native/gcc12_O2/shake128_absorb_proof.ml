(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing a message into a SHAKE128 context: the proof (see               *)
(* shake128_absorb_spec.ml).                                                 *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/shake128_absorb_spec.ml";;
needs "x86/proofs/utils/mldsa_native_absorb.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The blocks of the stream X = 2^(8 * pos) * M. Iteration k of the loop     *)
(* XORs r - p bytes of the message from offset c, at position p of the       *)
(* state, with p = pos and c = 0 for k = 0 and p = 0 and c = r * k - pos     *)
(* after that: that is block k of X. After the n = (pos + inlen) DIV r       *)
(* iterations, the rest of the message is the last, partial, block.          *)
(* ------------------------------------------------------------------------- *)


let SHAKE_ABSORB_CHUNK = prove
 (`!M pos r k.
        pos <= r
        ==> 2 EXP (8 * (if k = 0 then pos else 0)) *
            (M DIV 2 EXP (8 * (if k = 0 then 0 else r * k - pos))) MOD
            2 EXP (8 * (r - (if k = 0 then pos else 0))) =
            (2 EXP (8 * pos) * M) DIV 2 EXP (8 * r * k) MOD 2 EXP (8 * r)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
    SUBGOAL_THEN `2 EXP (8 * r) = 2 EXP (8 * pos) * 2 EXP (8 * (r - pos))`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      SIMP_TAC[MOD_MULT2; EXP_EQ_0; ARITH_EQ]];
    REWRITE_TAC[MULT_CLAUSES; EXP; SUB_0] THEN
    SUBGOAL_THEN
     `2 EXP (8 * r * k) = 2 EXP (8 * pos) * 2 EXP (8 * (r * k - pos))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `r <= r * k` MP_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `r = r * 1`] THEN
        REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
      SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ]]]);;

let SHAKE_ABSORB_TAIL = prove
 (`!M inlen pos r.
        0 < r /\ pos <= r /\ M < 2 EXP (8 * inlen)
        ==> let n = (pos + inlen) DIV r in
            let p = if n = 0 then pos else 0
            and c = if n = 0 then 0 else r * n - pos in
            2 EXP (8 * p) * (M DIV 2 EXP (8 * c)) MOD 2 EXP (8 * (inlen - c)) =
            (2 EXP (8 * pos) * M) DIV 2 EXP (8 * r * n) MOD 2 EXP (8 * r) /\
            p + (inlen - c) = (pos + inlen) MOD r /\
            c <= inlen`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPECL [`pos + inlen`; `r:num`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  ABBREV_TAC `n = (pos + inlen) DIV r` THEN
  ABBREV_TAC `t = (pos + inlen) MOD r` THEN STRIP_TAC THEN
  SUBGOAL_THEN `r <= r * n \/ n = 0` ASSUME_TAC THENL
   [ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `r = r * 1`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(if n = 0 then 0 else r * n - pos) <= inlen /\
                inlen - (if n = 0 then 0 else r * n - pos) +
                (if n = 0 then pos else 0) = t`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pos + inlen = n * r + t` THEN
    UNDISCH_TAC `r <= r * n \/ n = 0` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  SUBGOAL_THEN `(2 EXP (8 * pos) * M) DIV 2 EXP (8 * r * n) =
                2 EXP (8 * (if n = 0 then pos else 0)) *
                M DIV 2 EXP (8 * (if n = 0 then 0 else r * n - pos))`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
    SUBGOAL_THEN
     `2 EXP (8 * r * n) = 2 EXP (8 * pos) * 2 EXP (8 * (r * n - pos))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `r <= r * n \/ n = 0` THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ]];
    ALL_TAC] THEN
  ABBREV_TAC `c = if n = 0 then 0 else r * n - pos` THEN
  ABBREV_TAC `p = if n = 0 then pos else 0` THEN
  SUBGOAL_THEN `M DIV 2 EXP (8 * c) < 2 EXP (8 * (inlen - c))` ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM EXP_ADD; GSYM LEFT_ADD_DISTRIB] THEN
    ASM_SIMP_TAC[ARITH_RULE `c <= inlen ==> c + inlen - c = inlen`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  TRANS_TAC LTE_TRANS `2 EXP (8 * p) * 2 EXP (8 * (inlen - c))` THEN
  ASM_SIMP_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD; LE_EXP] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The values of r - pos and of the lengths in the 64-bit registers.         *)
(* ------------------------------------------------------------------------- *)

let SHAKE_WORD_ZX_SUB_RATE = prove
 (`!r p. p <= r /\ r < 2 EXP 32
         ==> word_zx(word_sub (word r)
                       (word_zx(word_zx(word p:int32):int64)):int32):int64 =
             word(r - p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_zx(word_zx(word p:int32):int64):int32 = word p`
  SUBST1_TAC THENL [REWRITE_TAC[WORD_ZX_ZX_32_64_32]; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_SUB_CASES;
              DIMINDEX_32; DIMINDEX_64] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `p < 4294967296 /\ r < 4294967296` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `r < 4294967296 ==> r - p < 4294967296`;
    ARITH_RULE `r < 4294967296 ==> r - p < 18446744073709551616`]);;

let SHAKE_VAL_WORD_LE = prove
 (`!x n. x <= n /\ 204 + n <= 18446744073709551616
         ==> val(word x:int64) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

let SHAKE_VAL_WORD_RATE = prove
 (`!x. x <= 200 ==> val(word x:int64) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

let SHAKE_MOD_RATE_SMALL = prove
 (`!x. x MOD 168 < 4294967296 /\ x MOD 168 < 18446744073709551616`,
  GEN_TAC THEN MP_TAC(SPECL [`x:num`; `168`] MOD_LT_EQ) THEN ARITH_TAC);;

let SHAKE_VAL_WORD_RATE_1 = prove
 (`val(word 167:int64) = 167`,
  CONV_TAC WORD_REDUCE_CONV);;

(*** The test at the end of iteration i: more than r - 1 bytes are left ***)

let SHAKE_ABSORB_LOOP_TEST = prove
 (`!pos inlen i.
        pos <= 168 /\ 168 * (i + 1) <= pos + inlen
        ==> (~(inlen - (168 * (i + 1) - pos) < 167 \/
               inlen - (168 * (i + 1) - pos) = 167) <=>
             i + 1 < (pos + inlen) DIV 168)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `i + 1 < q <=> i + 2 <= q`] THEN
  SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the calls, with the FULL theorems of the callees assumed as   *)
(* "H_XOR" and "H_PERMUTE", and for the comparisons with the rate.           *)
(* ------------------------------------------------------------------------- *)

let SHAKE128_ABSORB_CALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
     (mldsa_native_libmldsa_gcc12_O2_mc,
      MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_EXEC,
      0x0,mldsa_native_libmldsa_gcc12_O2_mc,th)
     (`e:(uarch_event)list`::ilist) n THENL
     [EXISTS_E2_FEV_TAC
       [`ctx:int64`; `src:int64`; `inlen:num`; `pos:num`; `pc:num`;
        `stackpointer:int64`; `returnaddress:int64`; `i:num`; `n:num`;
        `p:num`; `c:num`];
      LABEL_TAC name th]);;

(*** The flags of the comparison of inlen with r - pos, as arithmetic, with
 *** r - pos in RCX and R12 (the latter through its low 32 bits)
 ***)

let ABSORB_FIRST_FLAGS_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPECL [`168`; `pos:num`] SHAKE_WORD_ZX_SUB_RATE)
       (CONJ (ASSUME `pos <= 168`) (ARITH_RULE `168 < 2 EXP 32`))]) THEN
  ARGS_32_TAC [`168 - pos`] THEN ARGS_64_TAC [`pos:num`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0;
    MP (SPEC `168 - pos` SHAKE_VAL_WORD_RATE) (ARITH_RULE `168 - pos <= 200`);
    MP (SPECL [`inlen:num`; `inlen:num`] SHAKE_VAL_WORD_LE)
       (CONJ (ARITH_RULE `inlen <= inlen`)
             (ASSUME `204 + inlen <= 18446744073709551616`))]);;

(*** The flags of the comparison of the bytes left, x, with r - 1 ***)

let ABSORB_LOOP_FLAGS_TAC x =
  SUBGOAL_THEN (subst [x,`x:num`] `val(word x:int64) = x`) ASSUME_TAC THENL
   [MATCH_MP_TAC SHAKE_VAL_WORD_LE THEN EXISTS_TAC `inlen:num` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE
    [VAL_WORD_SUB_EQ_0; SHAKE_VAL_WORD_RATE_1; th]));;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The loop over the           *)
(* n = (pos + inlen) DIV 168 full blocks, if any, ends at join1 with the     *)
(* state after them; then the last call XORs the rest of the message. With   *)
(* the stack pointer at the bottom of the 320 bytes of the stack, the frame  *)
(* is the 56 bytes at stackpointer + 264, with the return address of the     *)
(* calls and the 256 bytes of the permutation below them. The events are     *)
(* those of the branch over the loop if n = 0, and otherwise of the start of *)
(* the loop and of its n iterations, each of which calls                     *)
(* mldsa_keccakf1600_xor_bytes with arguments that depend on the iteration   *)
(* and on pos, and then mldsa_keccakf1600_permute; the loop test is the end  *)
(* of the body, as ENSURES_EVENTS_WHILE_UP2_TAC requires. As the CALL writes *)
(* the stack, the state is kept as 200 bytes over the steps, and restated as *)
(* a 1600-bit word for each call. The abbreviations n, p and c are expanded  *)
(* before the events are unified with the template.                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(ctx:int64) (src:int64) (inlen:num) (pos:num) (pc:num)
     (stackpointer:int64) (returnaddress:int64).
      APPEND (f_ev_tail ctx src inlen pos pc stackpointer returnaddress)
       (if (pos + inlen) DIV 168 = 0
        then f_ev_short ctx src inlen pos pc stackpointer returnaddress
        else
         APPEND (f_ev_epil ctx src inlen pos pc stackpointer returnaddress)
          (APPEND
            (ENUMERATEL ((pos + inlen) DIV 168)
              (\i. f_ev_loop ctx src inlen pos pc stackpointer
                             returnaddress i))
            (f_ev_prol ctx src inlen pos pc stackpointer returnaddress)))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `204 + inlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(ctx:int64)`; `val(src:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun (n,c) -> ENSURES_PRESERVED_TAC n c)
   [("rbx_init",`RBX`); ("rbp_init",`RBP`); ("r12_init",`R12`);
    ("r13_init",`R13`)] THEN
  ABBREV_TAC `n = (pos + inlen) DIV 168` THEN

  (*** The state after the full blocks, at join1 ***)

  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_shake128_absorb_join1`
   `\s. read R13 s = ctx /\
        read RBX s = word(inlen - (if n = 0 then 0 else 168 * n - pos)) /\
        read RBP s =
        word_add src (word(if n = 0 then 0 else 168 * n - pos)) /\
        read RDX s = word(if n = 0 then pos else 0) /\
        read RSP s = word_add stackpointer (word 264) /\
        read (memory :> bytes64 (word_add stackpointer (word 288))) s =
        rbx_init /\
        read (memory :> bytes64 (word_add stackpointer (word 296))) s =
        rbp_init /\
        read (memory :> bytes64 (word_add stackpointer (word 304))) s =
        r12_init /\
        read (memory :> bytes64 (word_add stackpointer (word 312))) s =
        r13_init /\
        read (memory :> bytes64 (word_add stackpointer (word 320))) s =
        returnaddress /\
        read (memory :> bytes(src,inlen)) s = M /\
        read (memory :> bytes32(word_add ctx (word 200))) s = word pos /\
        read (memory :> bytes(ctx,200)) s =
        val(mld_keccak_absorb_blocks 168 S (2 EXP (8 * pos) * M) n)` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
     [(*** No full block: the branch over the loop ***)

      FULL_INIT_TAC THEN X86_STEPS_TAC EXEC (1--13) THEN
      ABSORB_FIRST_FLAGS_TAC THEN
      SUBGOAL_THEN `pos + inlen < 168` ASSUME_TAC THENL
       [UNDISCH_TAC `(pos + inlen) DIV 168 = n` THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[DIV_EQ_0; ARITH_EQ]; ALL_TAC] THEN
      SUBGOAL_THEN `inlen < 168 - pos <=> T`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [UNDISCH_TAC `pos + inlen < 168` THEN ARITH_TAC; ALL_TAC] THEN
      X86_STEPS_TAC EXEC (14--14) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[mld_keccak_absorb_blocks; WORD_ADD_0; SUB_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      ALL_TAC] THEN

    (*** The loop over the n full blocks ***)

    ENSURES_EVENTS_WHILE_UP2_TAC `n:num` `pc + mldsa_shake128_absorb_loop1`
     `pc + mldsa_shake128_absorb_loop1_exit`
     `\k s. read R13 s = ctx /\
            read RBX s =
            word(inlen - (if k = 0 then 0 else 168 * k - pos)) /\
            read RBP s =
            word_add src (word(if k = 0 then 0 else 168 * k - pos)) /\
            read R12 s = word(168 - (if k = 0 then pos else 0)) /\
            read RDX s = word(if k = 0 then pos else 0) /\
            read RCX s = word(168 - (if k = 0 then pos else 0)) /\
            read RSP s = word_add stackpointer (word 264) /\
            read (memory :> bytes64 (word_add stackpointer (word 288))) s =
            rbx_init /\
            read (memory :> bytes64 (word_add stackpointer (word 296))) s =
            rbp_init /\
            read (memory :> bytes64 (word_add stackpointer (word 304))) s =
            r12_init /\
            read (memory :> bytes64 (word_add stackpointer (word 312))) s =
            r13_init /\
            read (memory :> bytes64 (word_add stackpointer (word 320))) s =
            returnaddress /\
            read (memory :> bytes(src,inlen)) s = M /\
            read (memory :> bytes32(word_add ctx (word 200))) s =
            word pos /\
            read (memory :> bytes(ctx,200)) s =
            val(mld_keccak_absorb_blocks 168 S (2 EXP (8 * pos) * M) k)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];

      (*** Initialization: the branch over the loop is not taken ***)

      FULL_INIT_TAC THEN X86_STEPS_TAC EXEC (1--13) THEN
      ABSORB_FIRST_FLAGS_TAC THEN
      SUBGOAL_THEN `168 <= pos + inlen` ASSUME_TAC THENL
       [UNDISCH_TAC `(pos + inlen) DIV 168 = n` THEN
        UNDISCH_TAC `~(n = 0)` THEN
        SIMP_TAC[GSYM DIV_EQ_0; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `inlen < 168 - pos <=> F`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [UNDISCH_TAC `168 <= pos + inlen` THEN ARITH_TAC; ALL_TAC] THEN
      X86_STEPS_TAC EXEC (14--15) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[mld_keccak_absorb_blocks; WORD_ADD_0; SUB_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      (*** The body: XOR block i, permute, and the loop test ***)

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `168 * (i + 1) <= pos + inlen` ASSUME_TAC THENL
       [TRANS_TAC LE_TRANS `168 * n` THEN CONJ_TAC THENL
         [REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `i < n` THEN
          ARITH_TAC;
          EXPAND_TAC "n" THEN REWRITE_TAC[DIV_MUL_LE]];
        ALL_TAC] THEN
      ABBREV_TAC `p = if i = 0 then pos else 0` THEN
      ABBREV_TAC `c = if i = 0 then 0 else 168 * i - pos` THEN
      SUBGOAL_THEN
       `p <= 168 /\ c + (168 - p) = 168 * (i + 1) - pos /\
        c + (168 - p) <= inlen /\
        (if i + 1 = 0 then 0 else 168 * (i + 1) - pos) = c + (168 - p) /\
        (if i + 1 = 0 then pos else 0) = 0`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["p"; "c"] THEN
        REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
        UNDISCH_TAC `168 * (i + 1) <= pos + inlen` THEN
        UNDISCH_TAC `pos <= 168` THEN
        COND_CASES_TAC THENL
         [ASM_REWRITE_TAC[] THEN ARITH_TAC;
          SUBGOAL_THEN `168 <= 168 * i` MP_TAC THENL
           [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `168 = 168 * 1`] THEN
            REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `~(i = 0)` THEN
            ARITH_TAC;
            ARITH_TAC]];
        ALL_TAC] THEN
      FULL_INIT_TAC THEN
      X86_STEPS_TAC EXEC (1--5) THEN
      SUBGOAL_THEN
       `read (memory :> bytes(word_add src (word c),168 - p)) s5 =
        (M DIV 2 EXP (8 * c)) MOD 2 EXP (8 * (168 - p))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC READ_MEMORY_BYTES_SUB THEN EXISTS_TAC `inlen:num` THEN
        ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `p + (168 - p) <= 200` ASSUME_TAC THENL
       [UNDISCH_TAC `p <= 168` THEN ARITH_TAC; ALL_TAC] THEN
      KECCAK_STATE_AT_TAC `ctx:int64` THEN
      SHAKE128_ABSORB_CALL_TAC "H_XOR"
       [`read RDI s`; `read RSI s`; `p:num`; `168 - p`;
        `mld_keccak_absorb_blocks 168 S (2 EXP (8 * pos) * M) i`;
        `(M DIV 2 EXP (8 * c)) MOD 2 EXP (8 * (168 - p))`; `pc:num`;
        `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] 6 THEN
      SUBGOAL_THEN
       `2 EXP (8 * p) * (M DIV 2 EXP (8 * c)) MOD 2 EXP (8 * (168 - p)) =
        (2 EXP (8 * pos) * M) DIV 2 EXP (8 * 168 * i) MOD 2 EXP (8 * 168)`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [MAP_EVERY EXPAND_TAC ["p"; "c"] THEN
        MATCH_MP_TAC SHAKE_ABSORB_CHUNK THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
      X86_STEPS_TAC EXEC (7--9) THEN
      KECCAK_STATE_AT_TAC `ctx:int64` THEN
      SHAKE128_ABSORB_CALL_TAC "H_PERMUTE"
       [`read RDI s`;
        `mld_keccak_absorb_blocks 168 S (2 EXP (8 * pos) * M) i ^^
         word ((2 EXP (8 * pos) * M) DIV 2 EXP (8 * 168 * i) MOD
               2 EXP (8 * 168))`;
        `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
       10 THEN
      RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
      X86_STEPS_TAC EXEC (11--13) THEN
      SUBGOAL_THEN
       `word_sub (word (inlen - c)) (word (168 - p)):int64 =
        word(inlen - (168 * (i + 1) - pos))`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [REWRITE_TAC[GSYM(ASSUME `c + (168 - p) = 168 * (i + 1) - pos`)] THEN
        REWRITE_TAC[ARITH_RULE `inlen - (c + d) = inlen - c - d`] THEN
        REWRITE_TAC[WORD_SUB] THEN
        SUBGOAL_THEN `168 - p <= inlen - c` (fun th -> REWRITE_TAC[th]) THEN
        UNDISCH_TAC `c + (168 - p) <= inlen` THEN ARITH_TAC;
        ALL_TAC] THEN
      ABSORB_LOOP_FLAGS_TAC `inlen - (168 * (i + 1) - pos)` THEN
      X86_STEPS_TAC EXEC (14--14) THEN
      MP_TAC(SPECL [`pos:num`; `inlen:num`; `i:num`]
                   SHAKE_ABSORB_LOOP_TEST) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[GSYM ADD1; mld_keccak_absorb_blocks; SUB_0] THEN
      REWRITE_TAC[ADD1] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM(ASSUME `c + (168 - p) = 168 * (i + 1) - pos`)] THEN
        REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC];
        ALL_TAC] THEN
      UNABBREV_VARS_TAC [`p:num`; `c:num`; `n:num`] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      (*** The exit of the loop, at join1 ***)

      REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The rest of the message, and the new position ***)

    FULL_INIT_TAC THEN
    MP_TAC(ISPECL [`src:int64`; `inlen:num`; `read memory s0`]
                  READ_BYTES_BOUND) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`M:num`; `inlen:num`; `pos:num`; `168`]
                 SHAKE_ABSORB_TAIL) THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 < 168`] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `p = if n = 0 then pos else 0` THEN
    ABBREV_TAC `c = if n = 0 then 0 else 168 * n - pos` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `p + (inlen - c) < 168` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC;
      ALL_TAC] THEN
    X86_STEPS_TAC EXEC (1--5) THEN
    ARGS_32_TAC [`inlen - c`] THEN
    SUBGOAL_THEN
     `read (memory :> bytes(word_add src (word c),inlen - c)) s5 =
      (M DIV 2 EXP (8 * c)) MOD 2 EXP (8 * (inlen - c))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC READ_MEMORY_BYTES_SUB THEN EXISTS_TAC `inlen:num` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c <= inlen` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `p + (inlen - c) <= 200` ASSUME_TAC THENL
     [UNDISCH_TAC `p + (inlen - c) < 168` THEN ARITH_TAC; ALL_TAC] THEN
    KECCAK_STATE_AT_TAC `ctx:int64` THEN
    SHAKE128_ABSORB_CALL_TAC "H_XOR"
     [`read RDI s`; `read RSI s`; `p:num`; `inlen - c`;
      `mld_keccak_absorb_blocks 168 S (2 EXP (8 * pos) * M) n`;
      `(M DIV 2 EXP (8 * c)) MOD 2 EXP (8 * (inlen - c))`; `pc:num`;
      `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] 6 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    X86_STEPS_TAC EXEC (7--15) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
     [REWRITE_TAC[mld_keccak_absorb] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
                  DIMINDEX_32; DIMINDEX_64] THEN
      SUBGOAL_THEN `p < 168 /\ inlen - c < 168` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `p + (inlen - c) < 168` THEN ARITH_TAC; ALL_TAC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT;
        ARITH_RULE `p < 168 ==> p < 4294967296 /\ p < 18446744073709551616`;
        ARITH_RULE `x < 168 ==> x < 4294967296 /\ x < 18446744073709551616`;
        ARITH_RULE `p < 168 /\ x < 168 ==> p + x < 4294967296`] THEN
      ASM_SIMP_TAC[MOD_LT; SHAKE_MOD_RATE_SMALL];
      UNABBREV_VARS_TAC [`p:num`; `c:num`; `n:num`] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
