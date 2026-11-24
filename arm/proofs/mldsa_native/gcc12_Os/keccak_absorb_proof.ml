(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing a message into a Keccak state at a position: the proof (see     *)
(* keccak_absorb_spec.ml).                                                   *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/keccak_absorb_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

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
(* The values of r - p and of the lengths in the registers.                  *)
(* ------------------------------------------------------------------------- *)

let ABSORB_ZX_SUB = prove
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

let ABSORB_ZX_ADD = prove
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

let SHAKE_VAL_WORD_LE = prove
 (`!x n. x <= n /\ 200 + n <= 18446744073709551616
         ==> val(word x:int64) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

let SHAKE_VAL_WORD_RATE = prove
 (`!x. x <= 200 ==> val(word x:int64) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

(*** The test at the end of iteration i: at least r bytes are left ***)

let ABSORB_LOOP_TEST = prove
 (`!pos inlen i r.
        0 < r /\ pos <= r /\ r * (i + 1) <= pos + inlen
        ==> (r <= inlen - (r * (i + 1) - pos) <=>
             i + 1 < (pos + inlen) DIV r)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `i + 1 < q <=> i + 2 <= q`] THEN
  ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  SUBGOAL_THEN `r <= r * (i + 1)` MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `r = r * 1`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(*** The branch condition of the loop test, from the comparison of x and r ***)

let ABSORB_LS_FLAG = prove
 (`!x r q. (r <= x <=> q) ==> ((~(x <= r /\ ~(r = x))) <=> q)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ARITH_TAC);;

let ABSORB_VAL_SUB = prove
 (`!inlen y. 200 + inlen <= 18446744073709551616
             ==> val(word(inlen - y):int64) = inlen - y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SHAKE_VAL_WORD_LE THEN
  EXISTS_TAC `inlen:num` THEN ASM_REWRITE_TAC[ARITH_RULE `a - b <= a`]);;

(* ------------------------------------------------------------------------- *)
(* The calls, with the FULL theorems of the callees assumed as "H_XOR" and   *)
(* "H_PERMUTE".                                                              *)
(* ------------------------------------------------------------------------- *)

let ABSORB_CALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
     (mldsa_native_libmldsa_gcc12_Os_mc,
      MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_EXEC,
      0x0,mldsa_native_libmldsa_gcc12_Os_mc,th)
     ilist n THENL
     [EXISTS_E2_FEV_TAC
       [`ctx:int64`; `pos:num`; `r:num`; `src:int64`; `inlen:num`; `pc:num`;
        `stackpointer:int64`; `returnaddress:int64`; `i:num`; `n:num`;
        `p:num`; `c:num`];
      LABEL_TAC name th]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The loop over the           *)
(* n = (pos + inlen) DIV r full blocks, if any, ends at loop1_exit with the  *)
(* state after them; then the last call XORs the rest of the message. The   *)
(* frame is the 64 bytes at stackpointer + 224, with the 224 bytes of the    *)
(* permutation below them. The events are those of the branch over the loop  *)
(* if n = 0, and otherwise of the start of the loop and of its n iterations, *)
(* each of which calls mldsa_keccakf1600_xor_bytes with arguments that      *)
(* depend on the iteration and on pos, and then mldsa_keccakf1600_permute;   *)
(* the loop test is the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC     *)
(* requires. The abbreviations n, p and c are expanded before the events are *)
(* unified with the template.                                                *)
(* ------------------------------------------------------------------------- *)

(*** The flags of the comparison of r - pos with inlen, as arithmetic ***)

let ABSORB_FLAGS_TAC =
  ARGS_32_TAC [`r:num`; `pos:num`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPECL [`r:num`; `pos:num`] ABSORB_ZX_SUB)
       (CONJ (ASSUME `pos <= r`) (ASSUME `r <= 200`))]) THEN
  SUBGOAL_THEN `val(word(r - pos):int64) = r - pos /\
                val(word inlen:int64) = inlen`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0; th])) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SHAKE_VAL_WORD_RATE THEN ASM_ARITH_TAC;
      MATCH_MP_TAC SHAKE_VAL_WORD_LE THEN EXISTS_TAC `inlen:num` THEN
      ASM_REWRITE_TAC[LE_REFL]];
    ALL_TAC];;

let ABSORB_STACK_STR =
 "read SP s = word_add stackpointer (word 224) /\\
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
  returnaddress /\\
  read (memory :> bytes(src,inlen)) s = M";;

(*** The invariant at loop1_exit and the loop invariant at the start of ***)
(*** the XOR of block k, with the state after k blocks                  ***)

let ABSORB_MID_INV = parse_term
 ("\\s. read X22 s = ctx /\\ read X23 s = word r /\\
      read X19 s = word(if n = 0 then pos else 0) /\\
      read X20 s = word(inlen - (if n = 0 then 0 else r * n - pos)) /\\
      read X21 s = word_add src (word(if n = 0 then 0 else r * n - pos)) /\\
      " ^ ABSORB_STACK_STR ^ " /\\
      read (memory :> bytes(ctx,200)) s =
      val(mld_keccak_absorb_blocks r S (2 EXP (8 * pos) * M) n)");;

let ABSORB_LOOP_INV = parse_term
 ("\\k s. read X22 s = ctx /\\ read X23 s = word r /\\
         read X19 s = word(if k = 0 then pos else 0) /\\
         read X20 s = word(inlen - (if k = 0 then 0 else r * k - pos)) /\\
         read X21 s = word_add src (word(if k = 0 then 0 else r * k - pos)) /\\
         read X24 s = word(r - (if k = 0 then pos else 0)) /\\
         read X3 s = word(r - (if k = 0 then pos else 0)) /\\
         " ^ ABSORB_STACK_STR ^ " /\\
         read (memory :> bytes(ctx,200)) s =
         val(mld_keccak_absorb_blocks r S (2 EXP (8 * pos) * M) k)");;

let MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_OS_IMAGE_SUBROUTINE_FULL
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(ctx:int64) (pos:num) (r:num) (src:int64) (inlen:num) (pc:num)
     (stackpointer:int64) (returnaddress:int64).
      APPEND (f_ev_tail ctx pos r src inlen pc stackpointer returnaddress)
       (if (pos + inlen) DIV r = 0
        then f_ev_short ctx pos r src inlen pc stackpointer returnaddress
        else
         APPEND (f_ev_epil ctx pos r src inlen pc stackpointer returnaddress)
          (APPEND
            (ENUMERATEL ((pos + inlen) DIV r)
              (\i. f_ev_loop ctx pos r src inlen pc stackpointer
                             returnaddress i))
            (f_ev_prol ctx pos r src inlen pc stackpointer returnaddress)))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `ctx:int64`; `pos:num`; `r:num`; `src:int64`;
    `inlen:num`; `S:1600 word`; `M:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 288 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `200 + inlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(ctx:int64)`; `val(src:int64)`] THEN
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
  ABBREV_TAC `n = (pos + inlen) DIV r` THEN

  (*** The state after the full blocks, at loop1_exit ***)

  ENSURES_EVENTS_SEQUENCE_TAC `pc + keccak_absorb_fn_loop1_exit`
   ABSORB_MID_INV THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
     [(*** No full block: the branch over the loop ***)

      FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--12) THEN
      ABSORB_FLAGS_TAC THEN
      SUBGOAL_THEN `pos + inlen < r` ASSUME_TAC THENL
       [UNDISCH_TAC `(pos + inlen) DIV r = n` THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`]; ALL_TAC] THEN
      SUBGOAL_THEN `(inlen <= r - pos <=> T) /\ (r - pos = inlen <=> F)`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [UNDISCH_TAC `pos + inlen < r` THEN ARITH_TAC; ALL_TAC] THEN
      ARM_STEPS_TAC EXEC (13--13) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[mld_keccak_absorb_blocks; WORD_ADD_0; SUB_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      ALL_TAC] THEN

    (*** The loop over the n full blocks ***)

    ENSURES_EVENTS_WHILE_UP2_TAC `n:num` `pc + 3824`
     `pc + keccak_absorb_fn_loop1_exit` ABSORB_LOOP_INV THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];

      (*** Initialization: the branch into the loop ***)

      FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--12) THEN
      ABSORB_FLAGS_TAC THEN
      SUBGOAL_THEN `r <= pos + inlen` ASSUME_TAC THENL
       [SUBGOAL_THEN `~((pos + inlen) DIV r = 0)` MP_TAC THENL
         [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
        ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(inlen <= r - pos <=> r - pos = inlen)`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [UNDISCH_TAC `r <= pos + inlen` THEN ARITH_TAC; ALL_TAC] THEN
      ARM_STEPS_TAC EXEC (13--13) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[TAUT `(p /\ ~p) <=> F`]) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[mld_keccak_absorb_blocks; WORD_ADD_0; SUB_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      (*** The body: XOR block i, permute, and the loop test ***)

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `r * (i + 1) <= pos + inlen` ASSUME_TAC THENL
       [TRANS_TAC LE_TRANS `r * n` THEN CONJ_TAC THENL
         [REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `i < n` THEN
          ARITH_TAC;
          EXPAND_TAC "n" THEN REWRITE_TAC[DIV_MUL_LE]];
        ALL_TAC] THEN
      ABBREV_TAC `p = if i = 0 then pos else 0` THEN
      ABBREV_TAC `c = if i = 0 then 0 else r * i - pos` THEN
      SUBGOAL_THEN
       `p <= r /\ c + (r - p) = r * (i + 1) - pos /\
        c + (r - p) <= inlen /\
        (if i + 1 = 0 then 0 else r * (i + 1) - pos) = c + (r - p) /\
        (if i + 1 = 0 then pos else 0) = 0`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["p"; "c"] THEN
        REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
        UNDISCH_TAC `r * (i + 1) <= pos + inlen` THEN
        UNDISCH_TAC `pos <= r` THEN
        COND_CASES_TAC THENL
         [ASM_REWRITE_TAC[] THEN ARITH_TAC;
          SUBGOAL_THEN `r <= r * i` MP_TAC THENL
           [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `r = r * 1`] THEN
            REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `~(i = 0)` THEN
            ARITH_TAC;
            ARITH_TAC]];
        ALL_TAC] THEN
      FULL_INIT_TAC THEN
      ARM_STEPS_TAC EXEC (1--4) THEN
      ARGS_32_TAC [`p:num`] THEN
      SUBGOAL_THEN
       `read (memory :> bytes(word_add src (word c),r - p)) s4 =
        (M DIV 2 EXP (8 * c)) MOD 2 EXP (8 * (r - p))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC READ_MEMORY_BYTES_SUB THEN EXISTS_TAC `inlen:num` THEN
        ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `p + (r - p) <= 200` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      KECCAK_STATE_AT_TAC `ctx:int64` THEN
      ABSORB_CALL_TAC "H_XOR"
       [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `p:num`; `r - p`;
        `mld_keccak_absorb_blocks r S (2 EXP (8 * pos) * M) i`;
        `(M DIV 2 EXP (8 * c)) MOD 2 EXP (8 * (r - p))`; `pc:num`;
        `read X30 s`] 5 THEN
      SUBGOAL_THEN
       `2 EXP (8 * p) * (M DIV 2 EXP (8 * c)) MOD 2 EXP (8 * (r - p)) =
        (2 EXP (8 * pos) * M) DIV 2 EXP (8 * r * i) MOD 2 EXP (8 * r)`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [MAP_EVERY EXPAND_TAC ["p"; "c"] THEN
        MATCH_MP_TAC SHAKE_ABSORB_CHUNK THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ARM_STEPS_TAC EXEC (6--10) THEN
      ABSORB_CALL_TAC "H_PERMUTE"
       [`e:(uarch_event)list`; `read X0 s`;
        `mld_keccak_absorb_blocks r S (2 EXP (8 * pos) * M) i ^^
         word ((2 EXP (8 * pos) * M) DIV 2 EXP (8 * r * i) MOD
               2 EXP (8 * r))`;
        `pc:num`; `read SP s`; `read X30 s`] 11 THEN
      RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
      SUBGOAL_THEN
       `word_sub (word (inlen - c)) (word (r - p)):int64 =
        word(inlen - (r * (i + 1) - pos))`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [REWRITE_TAC[GSYM(ASSUME `c + (r - p) = r * (i + 1) - pos`)] THEN
        REWRITE_TAC[ARITH_RULE `inlen - (c + d) = inlen - c - d`] THEN
        REWRITE_TAC[WORD_SUB] THEN
        SUBGOAL_THEN `r - p <= inlen - c` (fun th -> REWRITE_TAC[th]) THEN
        UNDISCH_TAC `c + (r - p) <= inlen` THEN ARITH_TAC;
        ALL_TAC] THEN
      ARM_STEPS_TAC EXEC (12--14) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_0]) THEN
      ARGS_32_TAC [`r:num`] THEN
      ARM_STEPS_TAC EXEC (15--15) THEN
      SUBGOAL_THEN
       `val(word(inlen - (r * (i + 1) - pos)):int64) =
        inlen - (r * (i + 1) - pos) /\ val(word r:int64) = r`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0; th])) THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC ABSORB_VAL_SUB THEN FIRST_ASSUM ACCEPT_TAC;
          MATCH_MP_TAC SHAKE_VAL_WORD_RATE THEN FIRST_ASSUM ACCEPT_TAC];
        ALL_TAC] THEN
      ARM_STEPS_TAC EXEC (16--16) THEN
      SUBGOAL_THEN
       `(~(inlen - (r * (i + 1) - pos) <= r /\
           ~(r = inlen - (r * (i + 1) - pos)))) <=> i + 1 < n`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [MATCH_MP_TAC ABSORB_LS_FLAG THEN
        MP_TAC(SPECL [`pos:num`; `inlen:num`; `i:num`; `r:num`]
                     ABSORB_LOOP_TEST) THEN
        REWRITE_TAC[ASSUME `0 < r`; ASSUME `pos <= r`;
                    ASSUME `r * (i + 1) <= pos + inlen`;
                    ASSUME `(pos + inlen) DIV r = n`];
        ALL_TAC] THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[GSYM ADD1; mld_keccak_absorb_blocks; SUB_0] THEN
      REWRITE_TAC[ADD1] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM(ASSUME `c + (r - p) = r * (i + 1) - pos`)] THEN
        REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC];
        ALL_TAC] THEN
      SAFE_META_EXISTS_TAC allowed_vars_e THEN
      CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
      CONJ_TAC THENL
       [UNABBREV_VARS_TAC [`p:num`; `c:num`; `n:num`] THEN
        (FULL_UNIFY_F_EVENTS_TAC ORELSE
         (REWRITE_TAC[GSYM APPEND_ASSOC] THEN FULL_UNIFY_F_EVENTS_TAC));
        ALL_TAC] THEN
      CONV_TAC(RATOR_CONV(RATOR_CONV(RAND_CONV APPEND_SPINE_CONV))) THEN
      DISCHARGE_MEMACCESS_INBOUNDS_TAC;

      (*** The exit of the loop, at loop1_exit ***)

      REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[] THEN
      UNABBREV_VARS_TAC [`n:num`] THEN
      DISCHARGE_SAFETY_PROPERTY_SPINE_TAC];

    (*** The rest of the message, and the new position ***)

    FULL_INIT_TAC THEN
    MP_TAC(ISPECL [`src:int64`; `inlen:num`; `read memory s0`]
                  READ_BYTES_BOUND) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`M:num`; `inlen:num`; `pos:num`; `r:num`]
                 SHAKE_ABSORB_TAIL) THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `p = if n = 0 then pos else 0` THEN
    ABBREV_TAC `c = if n = 0 then 0 else r * n - pos` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(pos + inlen) MOD r < r` ASSUME_TAC THENL
     [MP_TAC(SPECL [`pos + inlen`; `r:num`] DIVISION) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `0 < r` THEN ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `p + (inlen - c) < r` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ARM_STEPS_TAC EXEC (1--5) THEN
    ARGS_32_TAC [`inlen - c`; `p:num`] THEN
    SUBGOAL_THEN
     `read (memory :> bytes(word_add src (word c),inlen - c)) s5 =
      (M DIV 2 EXP (8 * c)) MOD 2 EXP (8 * (inlen - c))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC READ_MEMORY_BYTES_SUB THEN EXISTS_TAC `inlen:num` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c <= inlen` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `p + (inlen - c) <= 200` ASSUME_TAC THENL
     [UNDISCH_TAC `p + (inlen - c) < r` THEN UNDISCH_TAC `r <= 200` THEN
      ARITH_TAC; ALL_TAC] THEN
    KECCAK_STATE_AT_TAC `ctx:int64` THEN
    ABSORB_CALL_TAC "H_XOR"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `p:num`; `inlen - c`;
      `mld_keccak_absorb_blocks r S (2 EXP (8 * pos) * M) n`;
      `(M DIV 2 EXP (8 * c)) MOD 2 EXP (8 * (inlen - c))`; `pc:num`;
      `read X30 s`] 6 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC EXEC (7--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[mld_keccak_absorb] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(SPECL [`p:num`; `inlen - c`] ABSORB_ZX_ADD) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `p + (inlen - c) < r` THEN UNDISCH_TAC `r <= 200` THEN
        ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[mld_keccak_absorb] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[SND] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNABBREV_VARS_TAC [`p:num`; `c:num`; `n:num`] THEN
    DISCHARGE_SAFETY_PROPERTY_SPINE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_FULL);;
