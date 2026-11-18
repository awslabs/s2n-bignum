(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the FULL proofs of the samplers of mldsa-native (the rejection  *)
(* sampling loops mld_rej_uniform_c and mld_rej_eta_c, and their callers).   *)
(*                                                                           *)
(* The loops keep small counters and positions in 32-bit registers and test  *)
(* them with CMP, CSET, CCMP and TST, so that a step leaves flags and        *)
(* registers that are conditionals on comparisons of numbers. The tactics    *)
(* here decide those conditionals from arithmetic facts where possible       *)
(* (SAMPLING_STEP_TAC simulates one step and does so), and put the test of   *)
(* the loop in the form i + 1 < k that ENSURES_EVENTS_WHILE_UP2_TAC          *)
(* expects. The events of an iteration depend on which candidates are        *)
(* accepted; each path of the iteration gets its own meta-variable in the    *)
(* template, as in mldsa_native_full.ml, and SAMPLING_PATH_DISCHARGE_TAC     *)
(* also handles a path that the simulation reaches in several ways.          *)
(* ========================================================================= *)

needs "common/fips204/properties/mldsa_native_full.ml";;
needs "common/fips204/properties/mldsa_native_absorb.ml";;
needs "common/mldsa_native_sampling.ml";;

(* ------------------------------------------------------------------------- *)
(* The incremental SHAKE functions of fips202.c on a short message (one      *)
(* partial block, as for the seeds of the samplers): absorbing it into the   *)
(* zero state and finalizing give the absorbed state of the 4-way functions, *)
(* so that the output of mld_shake256 is mld_shake256_stream; squeezing a    *)
(* whole number of blocks from position r, and the bytes of an output.       *)
(* ------------------------------------------------------------------------- *)

let MLD_WORD_XOR_DISJOINT = prove
 (`!a b k. a < 2 EXP k
           ==> word_xor (word a) (word(2 EXP k * b)):N word =
               word(a + 2 EXP k * b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_and (word a) (word(2 EXP k * b)):N word = word 0`
  ASSUME_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD; BIT_WORD_0] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i < k` THENL
     [SUBGOAL_THEN `~ODD((2 EXP k * b) DIV 2 EXP i)`
       (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `2 EXP k * b = 2 EXP i * (2 EXP (k - i) * b)` SUBST1_TAC
      THENL
       [REWRITE_TAC[MULT_ASSOC; GSYM EXP_ADD] THEN AP_THM_TAC THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[NOT_ODD; EVEN_MULT; EVEN_EXP; ARITH_EVEN] THEN
      ASM_ARITH_TAC;
      SUBGOAL_THEN `a DIV 2 EXP i = 0` (fun th -> REWRITE_TAC[th; ODD]) THEN
      MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2 EXP k` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
    ASM_SIMP_TAC[GSYM WORD_ADD_XOR; WORD_ADD]]);;

let MLD_NUM_OF_BYTELIST_LIST_OF_SEQ_DIGIT = prove
 (`!(f:num->byte) n j.
        j < n
        ==> (num_of_bytelist(list_of_seq f n) DIV 2 EXP (8 * j)) MOD 256 =
            val(f j)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LT] THEN
  X_GEN_TAC `j:num` THEN
  REWRITE_TAC[list_of_seq; NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ;
              num_of_bytelist; MULT_CLAUSES; ADD_CLAUSES] THEN
  MP_TAC(ISPEC `list_of_seq (f:num->byte) n` NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; ARITH_RULE `256 = 2 EXP 8`;
              GSYM EXP_MULT] THEN
  REWRITE_TAC[ARITH_RULE `8 * n = n * 8`] THEN
  ABBREV_TAC `x = num_of_bytelist(list_of_seq (f:num->byte) n)` THEN
  DISCH_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES] THEN
    MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `(f:num->byte) n` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; ARITH_RULE `8 * j = j * 8`]
    THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `2 EXP (n * 8) = 2 EXP (j * 8) * 2 EXP 8 * 2 EXP ((n - j - 1) * 8)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[GSYM MULT_ASSOC; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[MOD_MULT_ADD]]);;

let MLD_KECCAK_SQUEEZE_STATE_BLOCKS = prove
 (`!r (S:1600 word) n.
        0 < r /\ 0 < n
        ==> mld_keccak_squeeze_state r S r (r * n) = (keccak_squeeze n S,r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_keccak_squeeze_state] THEN
  ASM_SIMP_TAC[MULT_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `(r + r * n - 1) DIV r = n` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `r - 1` THEN
    MP_TAC(SPECL [`r:num`; `n:num`] LT_MULT) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `0 < r` THEN ARITH_TAC;
    REWRITE_TAC[PAIR_EQ] THEN ARITH_TAC]);;

let MLD_KECCAK_PAD_SHORT = prove
 (`!r p inlen.
        inlen + 2 <= r /\ p < 256
        ==> num_of_bytelist(keccak_pad r p inlen) =
            p + 2 EXP (8 * (r - inlen - 1)) * 128`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[keccak_pad] THEN
  SUBGOAL_THEN `inlen MOD r = inlen` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(inlen = r - 1)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[num_of_bytelist; NUM_OF_BYTELIST_APPEND; LENGTH_REPLICATE;
              NUM_OF_BYTELIST_REPLICATE_0; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  SUBGOAL_THEN `8 * (r - inlen - 1) = 8 + 8 * (r - inlen - 2)` SUBST1_TAC
  THENL [ASM_ARITH_TAC; REWRITE_TAC[EXP_ADD] THEN ARITH_TAC]);;

let MLD_KECCAK_ABSORB_ONCE_SHORT = prove
 (`!r p inlen M.
        inlen + 2 <= r /\ p < 128 /\ M < 2 EXP (8 * inlen)
        ==> mld_keccak_finalize r p
             (FST(mld_keccak_absorb r (word 0) 0 inlen M))
             (SND(mld_keccak_absorb r (word 0) 0 inlen M)) =
            mld_keccak_absorb_once r p inlen M`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mld_keccak_absorb; mld_keccak_finalize; mld_keccak_absorb_once;
              ADD_CLAUSES; MULT_CLAUSES; EXP; MULT_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `inlen DIV r = 0 /\ inlen MOD r = inlen` STRIP_ASSUME_TAC
  THENL [CONJ_TAC THENL [MATCH_MP_TAC DIV_LT; MATCH_MP_TAC MOD_LT] THEN
         ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[mld_keccak_absorb_blocks; keccak_absorb; MULT_CLAUSES; EXP;
                  DIV_1; WORD_XOR_0] THEN
  ASM_SIMP_TAC[MLD_KECCAK_PAD_SHORT; ARITH_RULE `p < 128 ==> p < 256`] THEN
  SUBGOAL_THEN `M < 2 EXP (8 * r)` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (8 * inlen)` THEN
    ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; MLD_WORD_XOR_DISJOINT] THEN
  SUBGOAL_THEN
   `2 EXP (8 * inlen) * (p + 2 EXP (8 * (r - inlen - 1)) * 128) =
    2 EXP (8 * inlen) * p + 2 EXP (8 * (r - 1)) * 128`
  SUBST1_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM EXP_ADD] THEN
    REWRITE_TAC[EQ_ADD_LCANCEL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `M + 2 EXP (8 * inlen) * p < 2 EXP (8 * (r - 1))` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (8 * inlen) + 2 EXP (8 * inlen) * 127` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `a < c /\ b <= d ==> a + b < c + d`) THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `a + a * 127 = 2 EXP 7 * a`; GSYM EXP_ADD] THEN
    REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MLD_WORD_XOR_DISJOINT; ADD_ASSOC] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  TRANS_TAC LTE_TRANS `2 EXP (8 * (r - 1)) + 2 EXP (8 * (r - 1)) * 128` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[LT_ADD_RCANCEL]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `a + a * 128 = 129 * a`] THEN
  TRANS_TAC LE_TRANS `2 EXP 8 * 2 EXP (8 * (r - 1))` THEN
  CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM EXP_ADD; LE_EXP] THEN ASM_ARITH_TAC);;

let SAMPLING_TST_CONDS = prove
 (`(!p q. (val(word_and (if p then word 0 else word 1)
                        (if q then word 0 else word 1):int32) = 0 <=>
           p \/ q)) /\
   (!q. (val(word_and (word 1) (if q then word 0 else word 1):int32) = 0 <=>
         q)) /\
   (!x. val(word_and (word 0) x:int32) = 0)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_AND_0; VAL_WORD_0] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[VAL_EQ_0] THEN
  CONV_TAC WORD_REDUCE_CONV);;

let SAMPLING_LENGTH_COND = prove
 (`!p (x:A). LENGTH(if p then [x] else []) = if p then 1 else 0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[LENGTH; ONE]);;

let SAMPLING_SELECT_TAC =
  W(fun (asl,w) ->
    let conds = map (fun t -> rand(rator(rator t))) (find_terms is_cond w) in
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if mem c conds then EQT_INTRO th
      else if is_neg c && mem (rand c) conds then EQF_INTRO th
      else failwith "") asl in
    REWRITE_TAC ths);;

let SAMPLING_CASES_TAC tm =
  let tac b =
    W(fun (asl,w) ->
      let iffs = filter (fun th -> is_iff(concl th) &&
                   can (term_match [] `EL k (l:bool list)`) (lhs(concl th)))
                 (map snd asl) in
      let c = if b then tm else mk_neg tm in
      let th = REWRITE_RULE iffs (ASSUME c) in
      if concl th = c then ALL_TAC else STRIP_ASSUME_TAC th) in
  ASM_CASES_TAC tm THENL [tac true; tac false];;

let SAMPLING_REGVAL r (asl,w) =
  rhs(concl(snd(find (fun (_,th) ->
    try rand(rator(lhs(concl th))) = r with Failure _ -> false) asl)));;

(*** Replacing the value of register reg by tm, proving them equal by      ***)
(*** rewriting with ths and bit-blasting                                    ***)

let SAMPLING_REG_TAC reg tm ths =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && (try rand(rator(lhs c)) = reg with Failure _ -> false)
    then ASSUME_TAC(TRANS th (prove(mk_eq(rhs c,tm),
                                    REWRITE_TAC ths THEN BITBLAST_TAC)))
    else failwith "SAMPLING_REG_TAC");;

(* ------------------------------------------------------------------------- *)
(* The test of the loop at the end of iteration i: SAMPLING_LOOP_PC_TAC k    *)
(* ths proves the condition of the branch equivalent to i + 1 < k, by        *)
(* rewriting i + 1 < k with ths and the assumptions i + 1 < m <=> .., and    *)
(* replaces it. When the simulation has decided that the loop exits,         *)
(* SAMPLING_LOOP_EXIT_TAC k ths pc1 shows ~(i + 1 < k) and puts the PC and   *)
(* the target of the last branch back as the conditional of the other paths. *)
(* ------------------------------------------------------------------------- *)

let SAMPLING_LOOP_EQ_TAC ths =
  REWRITE_TAC ths THEN
  W(fun (asl,w) ->
     let fs = mapfilter (fun (_,th) ->
       let c = concl th in
       if is_iff c && is_var(rand(lhand c)) &&
          lhand(lhand c) = mk_binop `(+):num->num->num` `i:num` `1`
       then th else failwith "") asl in
     REWRITE_TAC fs) THEN
  SAMPLING_SELECT_TAC THEN REPEAT COND_CASES_TAC THEN SIMPLE_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* The events of an iteration that takes one of several paths, as            *)
(* PATH_DISCHARGE_TAC of mldsa_native_full.ml, except that a path whose      *)
(* meta-variable another case has already instantiated (the same events,     *)
(* reached with other facts) is checked by beta-reduction instead.           *)
(* ------------------------------------------------------------------------- *)

let SAMPLING_PATH_DISCHARGE_TAC =
  let beta_all =
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) in
  REWRITE_TAC[ENUMERATEL_ADD1] THEN beta_all THEN SAMPLING_SELECT_TAC THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    if is_conj w then
      CONJ_TAC THENL
       [FULL_UNIFY_F_EVENTS_TAC ORELSE
        (CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
         REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC] THEN NO_TAC);
        ALL_TAC]
    else ALL_TAC) THEN
  beta_all THEN
  REWRITE_TAC[NOT_LT] THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(*** Elements of explicit lists ***)

let SAMPLING_EL_LIST_CONV =
  REWRITE_CONV[APPEND; EL; HD; TL; ONE; ADD_CLAUSES];;

(* ------------------------------------------------------------------------- *)
(* The 32-byte alignment of the buffers of the samplers within their stack   *)
(* frames: SAMPLING_ALIGN32_RULE k proves                                    *)
(*   !sp. aligned 16 sp ==> word_and (word_add sp (word k)) (word (2^64-32)) *)
(*                          = word_add sp (word(if aligned 32 sp then a      *)
(*                                              else b))                     *)
(* with the offsets a and b for the two cases.                               *)
(* ------------------------------------------------------------------------- *)

let SAMPLING_ALIGNED_16_32 = prove
 (`(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`,
  CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`x:int64`; `4`] (CONJUNCT1 WORD_AND_MASK_WORD));
    MP_TAC(ISPECL [`x:int64`; `5`] (CONJUNCT1 WORD_AND_MASK_WORD))] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16`; ARITH_RULE `x MOD 32 < 32`;
           ARITH_RULE `x < 16 ==> x < 2 EXP 64`;
           ARITH_RULE `x < 32 ==> x < 2 EXP 64`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT; MOD_LT_EQ; ARITH_EQ;
           ARITH_RULE `x MOD 16 < 18446744073709551616`;
           ARITH_RULE `x MOD 32 < 18446744073709551616`]);;

let SAMPLING_ALIGN32_RULE k =
  let a = (k / 32) * 32 and b = 16 + ((k - 16) / 32) * 32 in
  let tm = subst [mk_small_numeral k,`k:num`; mk_small_numeral a,`a:num`;
                  mk_small_numeral b,`b:num`]
   `!sptr:int64.
        aligned 16 sptr
        ==> word_and (word_add sptr (word k)) (word 18446744073709551584) =
            word_add sptr (word(if aligned 32 sptr then a else b))` in
  prove(tm,
    REWRITE_TAC[SAMPLING_ALIGNED_16_32] THEN
    GEN_TAC THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
    W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

(*** From the bytes of a buffer below m to those below n <= m ***)

let SAMPLING_BOUND_RULE n th =
  let j,bd = dest_forall(concl th) in
  let ant,_ = dest_imp bd in
  let ant' = mk_binop `(<):num->num->bool` j (mk_small_numeral n) in
  let lth = ARITH_RULE(mk_imp(ant',ant)) in
  GEN j (DISCH ant' (MP (SPEC j th) (MP lth (ASSUME ant'))));;

(* ------------------------------------------------------------------------- *)
(* The nonces of mldsa{44,65,87}_polyvecl_uniform_gamma1: the code computes  *)
(* kappa + k in 32 bits from the sign extension of the low 16 bits of kappa  *)
(* (sxth), and the callees use the low 16 bits of the result, as the casts   *)
(* (uint16_t)(kappa + k) of the C code do. SAMPLING_NONCE16_RULE k gives     *)
(* them as word_add (word_zx kappa) (word k), from the forms in which the    *)
(* simulation gives the 64-bit argument and the 16 bits stored on the stack, *)
(* and SAMPLING_NONCE16_0 does the same for kappa itself.                    *)
(* ------------------------------------------------------------------------- *)

let SAMPLING_NONCE16_RULE k =
  let tm = vsubst [mk_small_numeral k,`k:num`]
   `(word_zx(word_zx(word_add
       (word_zx(word_zx(word_sxfrom 15
         (word_subword (word_zx (kappa:int64):int32) (0,16):int32):int32)
          :int64):int32)
       (word k:int32)):int64):int16 =
     word_add (word_zx kappa) (word k)) /\
    (word_zx(word_zx(word_zx(word_add
       (word_zx(word_zx(word_sxfrom 15
         (word_subword (word_zx (kappa:int64):int32) (0,16):int32):int32)
          :int64):int32)
       (word k:int32)):int64):int32):int16 =
     word_add (word_zx kappa) (word k))` in
  GEN `kappa:int64` (BITBLAST_RULE tm);;

let SAMPLING_NONCE16_0 = prove
 (`!kappa:int64. word_zx(word_zx(word_zx kappa:int32):int64):int16 =
                 word_add (word_zx kappa) (word 0)`,
  GEN_TAC THEN BITBLAST_TAC);;
