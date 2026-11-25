(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* CompressFragment: the entry (to the first cut point, loop1 or join4), the *)
(* segment from loop1 (phase 1 of the model, the head of the main loop) and  *)
(* the segment from join4 (phase 5, emit_remainder) to the return.           *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_seg15_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_READ_BYTES16 = prove
 (`!(m:(S,int64->byte)component) x s.
        read (m :> bytes16 x) s = word(read (m :> bytes(x,2)) s)`,
  REWRITE_TAC[GSYM VAL_EQ; READ_COMPONENT_COMPOSE; BYTES16_WBYTES;
              VAL_READ_WBYTES; DIMINDEX_16; VAL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPECL [`x:int64`; `2`] READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let SNAPPY_TABLE_ZERO = prove
 (`!(m:(S,int64->byte)component) table ts s.
        read (m :> bytes(table,2 * ts)) s = 0
        ==> !j. j < ts
                ==> read (m :> bytes16 (word_add table (word(2 * j)))) s =
                    word 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SNAPPY_READ_BYTES16] THEN AP_TERM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  MP_TAC(ISPECL [`table:int64`; `2 * ts`; `2 * j`; `read (m:(S,int64->byte)component) (s:S)`]
    READ_BYTES_DIV) THEN
  ASM_REWRITE_TAC[DIV_0] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`word_add table (word(2 * j)):int64`; `2 * ts - 2 * j`; `2`;
                 `read (m:(S,int64->byte)component) (s:S)`] READ_BYTES_MOD) THEN
  ASM_REWRITE_TAC[MOD_0] THEN
  SUBGOAL_THEN `MIN (2 * ts - 2 * j) 2 = 2` (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

let snappy_cstate_CASES = prove_cases_thm snappy_cstate_INDUCT;;

let SNAPPY_READ_MEM_BYTES_0 = prove
 (`!a s. read (memory :> bytes(a,0)) (s:armstate) = 0`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]);;
let SNAPPY_CF1_MACH0_TAC =
  REWRITE_TAC[snappy_cf1_mach; snappy_cf1_ctx; snappy_phase; snappy_ip;
     snappy_ne; snappy_skip; snappy_cand; snappy_aux; snappy_t1; snappy_t2;
     snappy_out] THEN
  REWRITE_TAC[LENGTH; ADD_CLAUSES; num_of_bytelist; SNAPPY_READ_MEM_BYTES_0] THEN
  SNAPPY_CF1_MACH_TAC;;

let SNAPPY_SUBNUM_TAC =
  REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC(VAL_WORD_SUB_CASES :: SNAPPY_VAL_THMS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  (fun (asl,w) -> CONV_TAC (SNAPPY_MOD_ELIM_CONV (map snd asl)) (asl,w)) THEN
  REPEAT COND_CASES_TAC THEN
  (fun (asl,w) -> CONV_TAC (SNAPPY_MOD_ELIM_CONV (map snd asl)) (asl,w)) THEN
  SNAPPY_ARITH_TAC;;

(* The first cut point, from the call: the model state after 0 steps.        *)

let SNAPPY_CF1_CUT0_TAC =
  EXISTS_TAC `snappy_cf1_pot inp (snappy_cf1_init inp)` THEN
  REWRITE_TAC[snappy_cf1_cut] THEN EXISTS_TAC `0` THEN
  REWRITE_TAC[snappy_crun] THEN
  MP_TAC(SPEC `inp:byte list` SNAPPY_CF1_INIT) THEN
  ANTS_TAC THENL [SNAPPY_ARITH_TAC; SIMP_TAC[]] THEN
  DISCH_THEN(K ALL_TAC) THEN
  ASM_REWRITE_TAC[snappy_cf1_init; snappy_phase] THEN
  CONV_TAC NUM_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* The entry.                                                                *)
(* ------------------------------------------------------------------------- *)

(* SNAPPY_CF1_ENTRY_STMT: in compress_fragment_seg15_spec.ml. *)

let SNAPPY_CF1_ENTRY = prove
 (SNAPPY_CF1_ENTRY_STMT,
  REWRITE_TAC[ALLPAIRS; ALL; PAIRWISE; C_ARGUMENTS] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `snappy_max_compressed_length (LENGTH(inp:byte list)) =
                32 + LENGTH inp + LENGTH inp DIV 6`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC SNAPPY_MAX_COMPRESSED_LENGTH_32 THEN SNAPPY_ARITH_TAC;
    ALL_TAC] THEN
  SNAPPY_ABBREV_TAC `ts = snappy_table_size (LENGTH(inp:byte list))` THEN
  SUBGOAL_THEN `256 <= ts /\ ts <= 32768` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ts" THEN REWRITE_TAC[SNAPPY_TABLE_SIZE_BOUNDS]; ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP SNAPPY_TABLE_ZERO o check (fun th ->
    try rand(concl th) = `0` with Failure _ -> false)) THEN
  SUBGOAL_THEN `val(word(LENGTH(inp:byte list)):int64) = LENGTH inp`
   ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    SNAPPY_ARITH_TAC; ALL_TAC] THEN
  ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (1--6) THEN
  ARM_PC_REWRITE_TAC
   [ASSUME `val(word(LENGTH(inp:byte list)):int64) = LENGTH inp`] THEN
  SUBGOAL_THEN
   `(~(14 <= LENGTH(inp:byte list) /\
       ~(val (word_sub (word (LENGTH inp)) (word 14):int64) = 0))) <=>
    LENGTH inp < 15`
   (fun th -> ARM_PC_REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THEN SNAPPY_ARITH_TAC;
    ALL_TAC] THEN
  ARM_PC_CASES_TAC NO_TAC THENL
   [ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (7--9);
    SNAPPY_LOAD_TAC [32,`1`] THEN
    ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (7--12)] THEN
  BSTEP_FINAL_TAC THEN SNAPPY_CF1_CUT0_TAC THEN SNAPPY_CF1_MACH0_TAC THEN
  TRY SNAPPY_SUBNUM_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lemmas for emit_remainder: the length compare, sxtw, the literal tag and  *)
(* its length bytes (clz), the output region after the tag and memcpy.      *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_WORD_SUB_1_32 = prove
 (`!m. 1 <= m ==> word_sub (word m:int32) (word 1) = word (m - 1)`,
  SIMP_TAC[WORD_SUB]);;
let SNAPPY_CMP_LE_32 = prove
 (`!v k. v < 2 EXP 31 /\ k < 2 EXP 31
         ==> ((~(~(val (word_sub (word v:int32) (word k)) = 0) /\
                (ival (word_sub (word v:int32) (word k)) < &0 <=>
                 ~(ival (word v:int32) - &k = ival (word_sub (word v:int32) (word k))))))
              <=> v <= k)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[INT_IVAL; VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `v < 2147483648 ==> v < 4294967296`] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o REWRITE_RULE[LE_EXISTS]) THEN
    REWRITE_TAC[ADD_SUB2; GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_LT;
                GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_LE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_ADD]) THEN
    ASM_INT_ARITH_TAC;
    SUBGOAL_THEN `k <= v + 4294967296 /\ k <= 4294967296` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_LT;
                GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_LE] THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_ADD;
                                GSYM INT_OF_NUM_LE]) THEN
    REPEAT COND_CASES_TAC THEN ASM_INT_ARITH_TAC]);;
let SNAPPY_SXFROM_SUBWORD = prove
 (`!m. m < 2 EXP 31
       ==> word_sxfrom 31 (word_subword (word m:int64) (0,32):int64) = word m`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SXFROM; BIT_WORD_SUBWORD; BIT_WORD;
              DIMINDEX_64] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  ASM_CASES_TAC `i < 31` THENL
   [ASM_SIMP_TAC[ARITH_RULE `i < 31 ==> MIN 31 i = i`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 31 ==> i < 32`];
    ASM_SIMP_TAC[ARITH_RULE `~(i < 31) ==> MIN 31 i = 31`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `m DIV 2147483648 = 0 /\ m DIV 2 EXP i = 0`
     (fun th -> REWRITE_TAC[th; ARITH]) THEN
    CONJ_TAC THEN MATCH_MP_TAC DIV_LT THENL
     [UNDISCH_TAC `m < 2 EXP 31` THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 31` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_ARITH_TAC]]);;

let SNAPPY_CF1_FINAL = prove
 (`!(inp:byte list) k ip ne sk c x t1 t2 out.
        LENGTH inp <= 65536 /\
        snappy_crun (snappy_cf1_step inp) k (snappy_cf1_init inp) =
        SnappyCState 5 ip ne sk c x t1 t2 out
        ==> snappy_compress_fragment 1 inp =
            if ip < LENGTH inp
            then APPEND out (snappy_emit_literal (SUB_LIST(ip,LENGTH inp - ip) inp))
            else out`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`inp:byte list`; `k + 1`] SNAPPY_COMPRESS_FRAGMENT_1) THEN
  ASM_REWRITE_TAC[SNAPPY_CRUN_ADD; num_CONV `1`; snappy_crun] THEN
  REWRITE_TAC[snappy_cf1_step] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[snappy_phase; snappy_out]);;

let SNAPPY_READ_BYTES_1 = prove
 (`!(m:(S,int64->byte)component) a s.
        read (m :> bytes(a,1)) s = val(read (m :> bytes8 a) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SNAPPY_READ_BYTES8; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  MP_TAC(ISPECL [`a:int64`; `1`] READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let SNAPPY_READ_BYTES_CONS = prove
 (`!(m:(S,int64->byte)component) a (b:byte) d s.
        read (m :> bytes8 a) s = b /\
        read (m :> bytes(word_add a (word 1),LENGTH d)) s = num_of_bytelist d
        ==> read (m :> bytes(a,LENGTH(CONS b d))) s = num_of_bytelist(CONS b d)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `CONS (b:byte) d = APPEND [b] d` SUBST1_TAC THENL
   [REWRITE_TAC[APPEND]; ALL_TAC] THEN
  MATCH_MP_TAC SNAPPY_READ_BYTES_APPEND THEN
  REWRITE_TAC[LENGTH; GSYM ONE; SNAPPY_READ_BYTES_1; num_of_bytelist] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let SNAPPY_TAG_SHORT = prove
 (`!m. 1 <= m /\ m <= 60
       ==> word_zx (word_shl (word_subword (word_sub (word_zx (word m:int64):int32)
                                            (word 1)) (0,6):int32) 2):byte =
           word (4 * (m - 1))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SNAPPY_WORD_ZX_WORD_64_32; SNAPPY_WORD_SUB_1_32] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_SHL; VAL_WORD_SUBWORD;
              VAL_WORD; DIMINDEX_8; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  (fun (asl,w) -> CONV_TAC (SNAPPY_MOD_ELIM_CONV (map snd asl)) (asl,w)) THEN
  ARITH_TAC);;

let SNAPPY_CLZ_COUNT = prove
 (`!v. 60 <= v /\ v < 65536
       ==> word_xor (word_ishr (word (word_clz (word v:int32))) 3) (word 3):int32 =
           word (if v < 256 then 0 else 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word v:int32`] WORD_LE_CLZ_VAL) THEN
  REWRITE_TAC[DIMINDEX_32; VAL_WORD] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `v < 65536 ==> v < 2 EXP 32`] THEN
  ABBREV_TAC `c = word_clz(word v:int32)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `16 <= c /\ ~(27 <= c) /\ (24 <= c <=> v < 256)` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `c = 24 \/ c = 25 \/ c = 26` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC];
    SUBGOAL_THEN `c = 16 \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23`
     MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC]] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

let SNAPPY_STORE32_PREFIX = prove
 (`!(m:(S,int64->byte)component) a v k s.
        read (m :> bytes32 a) s = word v /\ v < 2 EXP 32 /\ k <= 4
        ==> read (m :> bytes(a,k)) s = num_of_bytelist(bytelist_of_num k v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(S,int64->byte)component`; `a:int64`; `word v:int32`; `k:num`; `s:S`]
    SNAPPY_READ_BYTES_OF_WORD) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BYTES32_WBYTES]) THEN
  ASM_REWRITE_TAC[DIMINDEX_32; VAL_WORD] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `k <= 4 ==> 8 * k <= 32`]);;

(* ------------------------------------------------------------------------- *)
(* Tactics for emit_remainder.                                               *)
(* ------------------------------------------------------------------------- *)

(* ARM_BSTEP_PLT_CALL_TAC (arm/proofs/libc.ml) with extra rewrites ths for   *)
(* the hypotheses of the contract instance and its pre/postcondition, e.g.   *)
(* val(word n) = n for a length n that is not a numeral.                     *)
let SNAPPY_PLT_CALL_TAC execth (th:thm) (ilist:term list) (ths:thm list) sname =
  W(fun (asl,w) ->
    let s' = rand w in
    let args = map (arm_bstep_eval asl s') ilist in
    let sth = SPECL args th in
    let sth = CONV_RULE(REWRITE_CONV([C_ARGUMENTS; C_RETURN; SOME_FLAGS;
                    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS;
                    MODIFIABLE_UPPER_SIMD_REGS; ALLPAIRS; ALL;
                    PAIRWISE] @ ths) THENC
                    DEPTH_CONV VAL_WORD_NUMERAL_CONV) sth in
    let cth =
      if not(is_imp(concl sth)) then sth else
      let hyp_tm = lhand(concl sth) in
      let hth = TAC_PROOF((asl,hyp_tm),
        CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
        REPEAT CONJ_TAC THEN
        TRY(CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN NO_TAC) THEN
        NONOVERLAPPING_TAC) in
      MP sth hth in
    ARM_BSTEP_CALL_TAC execth cth sname);;

let SNAPPY_CONV_FACTS_TAC (cs:term list) (cv:conv) : tactic =
  let is_c th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),_)),_) -> mem c cs
    | _ -> false in
  RULE_ASSUM_TAC(fun th -> if is_c th then CONV_RULE (RAND_CONV cv) th else th);;

let SNAPPY_LEN_TAC : tactic = fun (asl,w) ->
  let eqs = mapfilter (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var(_,_)) -> th | _ -> fail()) asl in
  (REWRITE_TAC([LENGTH_APPEND; LENGTH; LENGTH_SUB_LIST; LENGTH_BYTELIST_OF_NUM] @ eqs) THEN
   REWRITE_TAC[MIN; LE_REFL; ADD1]) (asl,w);;

let SNAPPY_COND_TAC : tactic = fun (asl,w) ->
  CONV_TAC(TOP_DEPTH_CONV (SNAPPY_DECIDE_CONV asl [])) (asl,w);;

let S5_DONE_TAC_GEN (safe:bool) : tactic =
  DISJ1_TAC THEN REWRITE_TAC[snappy_cf1_done_safe; snappy_cf1_done] THEN
  MP_TAC(SPECL [`inp:byte list`; `k:num`; `ip:num`; `ne:num`; `sk:num`; `c:num`; `x:num`;
                `t1:num->num`; `t2:num->num`; `out:byte list`] SNAPPY_CF1_FINAL) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [SNAPPY_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[snappy_emit_literal; LENGTH_SUB_LIST; MIN; LE_REFL] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SNAPPY_COND_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN
  FIRST
   [SNAPPY_CF1_EV_TAC;
    CONV_TAC WORD_RULE;
    SNAPPY_LEN_TAC THEN SNAPPY_WORD_NUM_TAC THEN NO_TAC;
    REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN SNAPPY_LEN_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN
    MATCH_MP_TAC SNAPPY_READ_BYTES_APPEND THEN CONJ_TAC THENL
     [SNAPPY_LEN_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC SNAPPY_READ_BYTES_CONS THEN CONJ_TAC THENL
       [SNAPPY_LEN_TAC THEN SNAPPY_FACT_TAC
         (FIRST [REFL_TAC; MATCH_MP_TAC SNAPPY_TAG_SHORT THEN SNAPPY_ARITH_TAC]);
        FIRST
         [SNAPPY_LEN_TAC THEN
          REWRITE_TAC[WORD_RULE `word_add (word_add (op:int64) (word ol)) (word 1) =
                                 word_add op (word (ol + 1))`] THEN
          FIRST_ASSUM ACCEPT_TAC;
          MATCH_MP_TAC SNAPPY_READ_BYTES_APPEND THEN CONJ_TAC THENL
           [REWRITE_TAC[LENGTH_BYTELIST_OF_NUM] THEN SNAPPY_LEN_TAC THEN
            REWRITE_TAC[WORD_RULE `word_add (word_add (op:int64) (word ol)) (word 1) =
                                   word_add op (word (ol + 1))`] THEN
            FIRST_ASSUM ACCEPT_TAC;
            REWRITE_TAC[LENGTH_BYTELIST_OF_NUM] THEN SNAPPY_LEN_TAC THEN
            REWRITE_TAC[WORD_RULE `word_add (word_add (word_add (op:int64) (word ol)) (word 1)) (word k) =
                                   word_add op (word (ol + 1 + k))`] THEN
            CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
            REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
            FIRST_ASSUM ACCEPT_TAC]]]]];;

let S5_MEMCPY_TAC_GEN (safe:bool) =
  SUBGOAL_THEN `LENGTH(inp:byte list) - ip < 2 EXP 31` (fun th -> SNAPPY_REWRITE_FACTS_TAC [`X2`; `X19`] [MATCH_MP SNAPPY_SXFROM_SUBWORD th]) THENL [SNAPPY_ARITH_TAC; ALL_TAC] THEN
  SNAPPY_REWRITE_FACTS_TAC [`X0`] [WORD_RULE `word_add (word_add (op:int64) (word ol)) (word 1) = word_add op (word (ol + 1))`] THEN
  SUBGOAL_THEN `val(word(LENGTH(inp:byte list) - ip):int64) = LENGTH inp - ip` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SNAPPY_ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) -> let s = rand w in
    MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; `src:int64`; `inp:byte list`; `ip:num`; `LENGTH(inp:byte list) - ip`; s] SNAPPY_READ_BYTES_SUB)) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SNAPPY_ARITH_TAC]; ALL_TAC] THEN
  DISCH_TAC THEN
  ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated] ~select:(elf_slots_importing ["memcpy"]) THEN
  ARM_BSTEP_PLT_STUB_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC THEN
  FIRST_ASSUM(fun th -> match concl th with
    Comb(Comb(Comb(Comb(Const("memcpy_contract",_),_),_),_),_) when not safe ->
     SNAPPY_PLT_CALL_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (REWRITE_RULE[memcpy_contract] th)
        [`read X0 s`; `read X1 s`; `read X2 s`;
         `num_of_bytelist(SUB_LIST(ip,LENGTH(inp:byte list) - ip) inp)`; `read X30 s`]
        [ASSUME `val(word(LENGTH(inp:byte list) - ip):int64) = LENGTH inp - ip`] "s20"
  | Comb(Comb(Comb(Comb(Const("memcpy_correct_safe_contract",_),_),_),_),_) when safe ->
     SNAPPY_PLT_CALL_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC
        (REWRITE_RULE[memcpy_correct_safe_contract] th)
        [`read events s`; `read X0 s`; `read X1 s`; `read X2 s`;
         `num_of_bytelist(SUB_LIST(ip,LENGTH(inp:byte list) - ip) inp)`; `read X30 s`]
        [ASSUME `val(word(LENGTH(inp:byte list) - ip):int64) = LENGTH inp - ip`] "s20"
   | _ -> NO_TAC) THEN
  ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (21--24) THEN BSTEP_FINAL_TAC;;

let S5_PREFIX_TAC (cnt:term) : tactic = fun (asl,w) ->
  let s = rand w in
  (MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; `word_add op (word (ol + 1)):int64`;
                 `LENGTH(inp:byte list) - ip - 1`; cnt; s] SNAPPY_STORE32_PREFIX) THEN
   ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SNAPPY_ARITH_TAC]; DISCH_TAC]) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* The segment from join4 (phase 5): emit_remainder and the return.          *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_CF1_SEG5_TAC (safe:bool) =
  let S5_MEMCPY_TAC = S5_MEMCPY_TAC_GEN safe
  and S5_DONE_TAC = S5_DONE_TAC_GEN safe in
  SNAPPY_CF1_SEG_START_TAC THEN
  SNAPPY_ABBREV_TAC `ol = LENGTH(out:byte list)` THEN
  ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (1--2) THEN SNAPPY_PC_NUM_TAC [] THEN
  ARM_PC_CASES_TAC NO_TAC THENL
   [ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (3--3) THEN
    SUBGOAL_THEN `word_sub (word_add src (word (LENGTH(inp:byte list))))
                           (word_add src (word ip)):int64 = word (LENGTH inp - ip)`
     (fun th -> SNAPPY_REWRITE_FACTS_TAC [`X13`] [th]) THENL
     [REWRITE_TAC[WORD_RULE `word_sub (word_add a (word b)) (word_add a (word c)):int64 =
                             word_sub (word b) (word c)`] THEN
      SNAPPY_SUBNUM_TAC; ALL_TAC] THEN
    ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (4--7) THEN
    ARM_PC_REWRITE_TAC[SNAPPY_WORD_ZX_WORD_64_32] THEN
    SUBGOAL_THEN `word_sub (word (LENGTH(inp:byte list) - ip):int32) (word 1) =
                  word (LENGTH inp - ip - 1)` ASSUME_TAC THENL
     [MATCH_MP_TAC SNAPPY_WORD_SUB_1_32 THEN SNAPPY_ARITH_TAC; ALL_TAC] THEN
    ARM_PC_REWRITE_TAC[ASSUME `word_sub (word (LENGTH(inp:byte list) - ip):int32) (word 1) =
                  word (LENGTH inp - ip - 1)`] THEN
    SUBGOAL_THEN `LENGTH(inp:byte list) - ip - 1 < 2 EXP 31 /\ 59 < 2 EXP 31`
     (fun th -> ARM_PC_REWRITE_TAC[MATCH_MP SNAPPY_CMP_LE_32 th]) THENL
     [SNAPPY_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `ol + 5 + (LENGTH(inp:byte list) - ip) <=
                  27 + LENGTH inp + LENGTH inp DIV 6` ASSUME_TAC THENL
     [SNAPPY_ARITH_TAC; ALL_TAC] THEN
    ARM_PC_CASES_TAC NO_TAC THENL
     [ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (8--15) THEN S5_MEMCPY_TAC THEN S5_DONE_TAC;
      ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (8--15) THEN
      SUBGOAL_THEN
       `word_xor (word_ishr (word (word_clz (word (LENGTH(inp:byte list) - ip - 1):int32))) 3)
                 (word 3):int32 = word (if LENGTH inp - ip - 1 < 256 then 0 else 1)`
       ASSUME_TAC THENL
       [MATCH_MP_TAC SNAPPY_CLZ_COUNT THEN SNAPPY_ARITH_TAC; ALL_TAC] THEN
      SNAPPY_REWRITE_FACTS_TAC [`X2`;`X3`;`X4`;`memory :> bytes32 (word_add op (word (ol + 1)))`]
       [SNAPPY_WORD_ZX_WORD_64_32;
        ASSUME `word_sub (word (LENGTH(inp:byte list) - ip):int32) (word 1) =
                word (LENGTH inp - ip - 1)`;
        ASSUME `word_xor (word_ishr (word (word_clz (word (LENGTH(inp:byte list) - ip - 1):int32))) 3)
                 (word 3):int32 = word (if LENGTH inp - ip - 1 < 256 then 0 else 1)`] THEN
      ASM_CASES_TAC `LENGTH(inp:byte list) - ip - 1 < 256` THEN
      FIRST_ASSUM(fun th -> SNAPPY_REWRITE_FACTS_TAC [`X2`;`X3`;`X4`] [th]) THEN
      SNAPPY_CONV_FACTS_TAC [`X2`;`X3`;`X4`] (DEPTH_CONV WORD_RED_CONV) THEN
      SNAPPY_REWRITE_FACTS_TAC [`X3`]
       [WORD_RULE `word_add (word_add (op:int64) (word ol)) (word k) = word_add op (word (ol + k))`] THENL
       [S5_PREFIX_TAC `1`; S5_PREFIX_TAC `2`] THEN
      ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (16--20) THEN S5_MEMCPY_TAC THEN S5_DONE_TAC];
    ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (3--4) THEN BSTEP_FINAL_TAC THEN S5_DONE_TAC];;

let SNAPPY_CF1_SEG5 = prove
 (SNAPPY_CF1_SEG5_STMT,
  SNAPPY_CF1_SEG5_TAC false);;

let SNAPPY_CF1_SEG5_SAFE = prove
 (SNAPPY_CF1_SEG5_SAFE_STMT,
  SNAPPY_CF1_SEG5_TAC true);;

(* ------------------------------------------------------------------------- *)
(* The segment from loop1 (phase 1): to loop3 (phase 6, the unrolled search) *)
(* when ip_limit - ip > 15 after next_emit = ip++, otherwise through join1   *)
(* to loop4 (phase 2) or, if already ip + 1 > ip_limit, to join4 (phase 5).  *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_IVAL_SUB = prove
 (`!a b. a < 2 EXP 62 /\ b < 2 EXP 62
         ==> ival(word_sub (word a:int64) (word b)) = &a - &b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_IWORD; GSYM IWORD_INT_SUB] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_INT_ARITH_TAC);;

(* cmp x, #15; b.le as a signed comparison.                                  *)

let SNAPPY_CMP_LE_15 = BITBLAST_RULE
 `!x:int64. (~(~(val (word_sub x (word 15)) = 0) /\
             (ival (word_sub x (word 15)) < &0 <=>
              ~(ival x - &15 = ival (word_sub x (word 15)))))) <=> ival x <= &15`;;

let SNAPPY_LOAD64_LOW32 = prove
 (`!(l:byte list) p. p + 8 <= LENGTH l
        ==> word_zx (word (snappy_load64 l p):int64):int32 =
            word (snappy_load32 l p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`l:byte list`; `p:num`; `0`] SNAPPY_LOAD64_SHIFT_LOW32) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1; ADD_CLAUSES; LE_0]);;

let SNAPPY_AND_65535 = prove
 (`!m. m < 65536 ==> val(word_and (word m:int32) (word 65535)) = m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word m:int32`; `16`] VAL_WORD_AND_MASK_WORD) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `m < 65536 ==> m < 4294967296`]);;

let SNAPPY_CF1_SEG1 = prove
 (SNAPPY_CF1_SEG1_STMT,
  SNAPPY_CF1_SEG_START_TAC THEN SNAPPY_LOAD_TAC [64,`ip + 1`] THEN
  ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (1--5) THEN
  ARM_PC_REWRITE_TAC[WORD_RULE
   `word_sub (word_add (s:int64) (word a)) (word_add (word_add s (word b)) (word 1)) =
    word_sub (word a) (word (b + 1))`] THEN
  ARM_PC_REWRITE_TAC[SNAPPY_CMP_LE_15] THEN
  SUBGOAL_THEN `LENGTH(inp:byte list) - 15 < 2 EXP 62 /\ ip + 1 < 2 EXP 62`
   (fun th -> ARM_PC_REWRITE_TAC[MATCH_MP SNAPPY_IVAL_SUB th]) THENL
   [SNAPPY_ARITH_TAC; ALL_TAC] THEN
  ARM_PC_REWRITE_TAC[INT_LE_SUB_RADD; INT_OF_NUM_ADD; INT_OF_NUM_LE] THEN
  ARM_PC_CASES_TAC NO_TAC THENL
   [SUBGOAL_THEN `word_zx (word (snappy_load64 inp (ip + 1)):int64):int32 =
                  word (snappy_load32 inp (ip + 1))` ASSUME_TAC THENL
     [MATCH_MP_TAC SNAPPY_LOAD64_LOW32 THEN SNAPPY_ARITH_TAC; ALL_TAC] THEN
    ARM_BSTEP_TAC ~rewrites:[ASSUME
      `word_zx (word (snappy_load64 inp (ip + 1)):int64):int32 =
       word (snappy_load32 inp (ip + 1))`]
      SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (6--15) THEN
    SNAPPY_REWRITE_FACTS_TAC [`X0`]
     [MATCH_MP SNAPPY_HASH1_WORD_ALT
        (ASSUME `snappy_table_size (LENGTH(inp:byte list)) = ts`);
      SNAPPY_VAL_WORD_LOAD32] THEN
    SNAPPY_PC_NUM_TAC [] THEN
    ARM_PC_CASES_TAC NO_TAC THENL
     [BSTEP_FINAL_TAC THEN SNAPPY_CF1_CUT_TAC 1 THEN SNAPPY_CF1_MACH_TAC;
      ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (16--18) THEN
      BSTEP_FINAL_TAC THEN SNAPPY_CF1_CUT_TAC 2 THEN SNAPPY_CF1_MACH_TAC];
    ARM_BSTEP_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC (6--14) THEN
    BSTEP_FINAL_TAC THEN SNAPPY_CF1_CUT_TAC 1 THEN SNAPPY_CF1_MACH_TAC THEN
    FIRST
     [REWRITE_TAC[ADD_CLAUSES; DIV_1] THEN NO_TAC;
      REWRITE_TAC[WORD_RULE
       `word_sub (word_add (word_add (s:int64) (word a)) (word 1)) s =
        word (a + 1)`; SNAPPY_WORD_ZX_WORD_64_32] THEN
      MP_TAC(SPEC `ip + 1` SNAPPY_AND_65535) THEN
      ANTS_TAC THENL [SNAPPY_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC MOD_LT THEN SNAPPY_ARITH_TAC]]);;
