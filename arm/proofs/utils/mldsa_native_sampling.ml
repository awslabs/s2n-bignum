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

needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_absorb.ml";;
needs "common/mldsa_native_sampling.ml";;

(* ------------------------------------------------------------------------- *)
(* The list of the values that mld_rej_eta_c declassifies: its length, its   *)
(* elements, and the number of T among its first n.                          *)
(* ------------------------------------------------------------------------- *)

let MLD_REJ_ETA_DECLASS = prove
 (`!eta target offset (b:num->byte) buflen.
     LENGTH(mld_rej_eta_declass eta target offset b buflen) =
     2 * mld_rej_eta_bytes eta target offset b buflen /\
     (!k. k < 2 * mld_rej_eta_bytes eta target offset b buflen
          ==> (EL k (mld_rej_eta_declass eta target offset b buflen) <=>
               mld_rej_eta_valid eta (mld_rej_eta_nibble b k))) /\
     (!n. n <= 2 * mld_rej_eta_bytes eta target offset b buflen
          ==> LENGTH(FILTER (\x. x)
                (SUB_LIST(0,n)
                  (mld_rej_eta_declass eta target offset b buflen))) =
              LENGTH(mld_rej_eta_list eta b n))`,
  REWRITE_TAC[mld_rej_eta_declass; LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; MLD_SUB_LIST_LIST_OF_SEQ;
           LENGTH_MLD_REJ_ETA_LIST]);;

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

let MLD_SHAKE256_BYTE_STREAM = prove
 (`!inlen M.
        inlen + 2 <= 136 /\ M < 2 EXP (8 * inlen)
        ==> mld_shake256_byte inlen M = mld_shake256_stream inlen M`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mld_shake256_byte; mld_shake256_stream; mld_shake256_state] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MLD_KECCAK_ABSORB_ONCE_SHORT THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The bytes of a buffer from its value as a number, or from a list of       *)
(* bytes, and the bytes of the blocks that mldsa_shake128x4_squeezeblocks    *)
(* and mldsa_shake256x4_squeezeblocks write as bytes of the stream from the  *)
(* state, for the precondition of the samplers.                              *)
(* ------------------------------------------------------------------------- *)

let MLD_READ_BYTES_BYTES8 = prove
 (`!a:int64 n x s:armstate.
        read (memory :> bytes(a,n)) s = x
        ==> !j. j < n
                ==> read (memory :> bytes8(word_add a (word j))) s =
                    word((x DIV 2 EXP (8 * j)) MOD 256)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `n:num`; `x:num`; `j:num`; `1`; `s:armstate`]
    READ_MEMORY_BYTES_SUB) THEN
  ASM_REWRITE_TAC[READ_MEMORY_BYTES_BYTES8] THEN
  ANTS_TAC THENL [UNDISCH_TAC `j < n` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(RAND_CONV NUM_REDUCE_CONV)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_VAL]);;

let MLD_READ_BYTES_LIST_OF_SEQ = prove
 (`!a:int64 n (f:num->byte) s:armstate.
        read (memory :> bytes(a,n)) s = num_of_bytelist(list_of_seq f n)
        ==> !j. j < n
                ==> read (memory :> bytes8(word_add a (word j))) s = f j`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP MLD_READ_BYTES_BYTES8) THEN
  ASM_SIMP_TAC[MLD_NUM_OF_BYTELIST_LIST_OF_SEQ_DIGIT; WORD_VAL]);;

let MLD_SQUEEZE_BLOCKS_BYTES8 = prove
 (`!a:int64 r n (S:1600 word) s:armstate.
        0 < r /\
        read (memory :> bytes(a,r * n)) s =
        nsum {i | i < n}
         (\i. 2 EXP (8 * r * i) *
              val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * r))
        ==> !j. j < r * n
                ==> read (memory :> bytes8(word_add a (word j))) s =
                    mld_keccak_squeeze_byte r S r j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP MLD_READ_BYTES_BYTES8) THEN
  ASM_SIMP_TAC[MLD_SQUEEZE_BLOCKS_BYTE]);;

(* ------------------------------------------------------------------------- *)
(* The values that the code computes in 32-bit registers: the nibbles of a   *)
(* byte loaded with LDRB, the position in the buffer from its distance to    *)
(* the base (w9 + w2 = (c - buf) + x2), small counters after an ADD, the     *)
(* result of a TST of two CSET results, and lengths of conditional lists.    *)
(* ------------------------------------------------------------------------- *)

let MLD_BYTE_NIBBLES = prove
 (`!y:byte.
     word_zx(word_and (word_zx(word_zx(word_zx y:int32):int64):int32)
                      (word 15)):int64 = word(val y MOD 16) /\
     word_zx(word_ushr (word_zx(word_zx(word_zx y:int32):int64):int32) 4)
       :int64 = word(val y DIV 16) /\
     word_and (word_zx y:int32) (word 15) = word(val y MOD 16) /\
     word_ushr (word_zx y:int32) 4 = word(val y DIV 16)`,
  GEN_TAC THEN REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_USHR;
              ARITH_RULE `15 = 2 EXP 4 - 1`; VAL_WORD_AND_MASK_WORD;
              DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  MP_TAC(ISPEC `y:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  SPEC_TAC(`val(y:byte)`,`n:num`) THEN CONV_TAC NUM_REDUCE_CONV THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `n MOD 4294967296 = n /\ n MOD 18446744073709551616 = n /\
                n MOD 16 MOD 4294967296 = n MOD 16 /\
                n MOD 16 MOD 18446744073709551616 = n MOD 16 /\
                (n DIV 16) MOD 4294967296 = n DIV 16 /\
                (n DIV 16) MOD 18446744073709551616 = n DIV 16`
   (fun th -> REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL [`n:num`; `16`] MOD_LT_EQ) THEN
  MP_TAC(SPECL [`n:num`; `16`] DIV_LE) THEN ASM_ARITH_TAC);;

let MLD_REJ_POS = prove
 (`!(buf:int64) k c.
        k + c < 4294967296
        ==> word_zx(word_add (word_sub (word c) (word_zx buf))
                             (word_zx(word_add buf (word k))):int32):int64 =
            word(k + c)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[WORD_ZX_ADD; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_sub c x) (word_add x y):int32 = word_add c y`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `k < 4294967296 /\ c < 4294967296 /\ c + k < 4294967296 /\
                k < 18446744073709551616 /\ k + c < 18446744073709551616 /\
                c + k < 18446744073709551616`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT; ADD_SYM]]);;

let SAMPLING_WORD_ZX_SMALL = prove
 (`(!m k. m + k < 2 EXP 32
          ==> word_zx(word_add (word_zx(word m:int64):int32) (word k)):int64 =
              word(m + k)) /\
   (!m k. m + k < 2 EXP 32
          ==> word_zx(word_add (word m:int32) (word k)):int64 = word(m + k)) /\
   (!m. m < 2 EXP 32 ==> word_zx(word m:int32):int64 = word m)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  TRY(SUBGOAL_THEN `m < 4294967296 /\ k < 4294967296 /\
                    m < 18446744073709551616 /\
                    m + k < 18446744073709551616` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC]) THEN
  TRY(SUBGOAL_THEN `m < 18446744073709551616` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC]) THEN
  ASM_SIMP_TAC[MOD_LT]);;

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

(*** The coefficient for eta = 2 as the code computes it, (t * 205) >> 10 ***)
(*** being t DIV 5 and multiplying by 5 being a shift and an add         ***)

let MLD_REJ_ETA2_COEFF = prove
 (`!t. t < 16
       ==> word_sub (word 2)
            (word_sub (word t)
              (word_add (word_ushr (word (0 + val(word t:int32) * 205)) 10)
                (word_shl (word_ushr (word (0 + val(word t:int32) * 205)) 10)
                          2))):int32 =
           word_sub (word 2)
            (word_sub (word t)
              (word_mul (word_ushr (word_mul (word 205) (word t)) 10)
                        (word 5)))`,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(REPEATC(CHANGED_CONV(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV))));;

(* ------------------------------------------------------------------------- *)
(* Deciding conditions: a proposition by arithmetic, keeping it as an        *)
(* assumption; the condition of a conditional branch; the conditions of the  *)
(* conditionals in the facts about the state (the flags after a CCMP, the    *)
(* results of CSET); and the conditionals of the goal, from assumptions that *)
(* are exactly their conditions or the negations. SAMPLING_CASES_TAC splits  *)
(* on a proposition about the declassified values and adds the instances of  *)
(* the assumptions EL k D <=> p that it implies.                             *)
(* ------------------------------------------------------------------------- *)

let SAMPLING_DECIDE_PROP_TAC c =
  (SUBGOAL_THEN c
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQT_INTRO th]) THEN
               ASSUME_TAC th) THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]) ORELSE
  (SUBGOAL_THEN (mk_neg c)
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQF_INTRO th]) THEN
               ASSUME_TAC th) THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]);;

let SAMPLING_DECIDE_BRANCH_TAC =
  FIRST_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if not (is_cond r) || not(can (term_match [] `read PC s`) l)
    then failwith "SAMPLING_DECIDE_BRANCH_TAC" else
    SAMPLING_DECIDE_PROP_TAC (lhand(rator r)));;

(*** The carry and zero flags of a 32-bit compare of small numbers, as     ***)
(*** W32_DECIDE_FLAGS_TAC but keeping the facts that decide them, so that ***)
(*** a case assumption that is one of them is not lost                    ***)

let SAMPLING_DECIDE_FLAGS_TAC =
  let pat = `word_sub (word x) (word y):int32` in
  W32_SMALL_TAC THEN
  W(fun (asl,w) ->
    let tms = setify (find_terms (can (term_match [] pat))
                                 (list_mk_conj(map (concl o snd) asl))) in
    MAP_EVERY (fun t ->
      let x = rand(lhand t) and y = rand(rand t) in
      MP_TAC(SPECL [x;y] WORD_CMP_32_FLAGS) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))]) tms) THEN
  W(fun (asl,w) ->
     let ps = mapfilter (fun (_,th) ->
       let l,r = dest_eq(concl th) in
       let f = rand(rator l) in
       if mem f [`CF`;`ZF`] && not(r = `T` || r = `F`) then r
       else failwith "") asl in
     MAP_EVERY (fun p -> TRY(SAMPLING_DECIDE_PROP_TAC p)) ps);;

let SAMPLING_DECIDE_CONDS_TAC =
  let has_read tm =
    can (find_term (fun t -> is_const t && fst(dest_const t) = "read")) tm in
  W(fun (asl,w) ->
    let rec conds bound tm acc =
      match tm with
        Comb(Comb(Comb(Const("COND",_),p),a),b) ->
          let acc' = if intersect (frees p) bound = [] && not (mem p acc)
                     then p::acc else acc in
          conds bound p (conds bound a (conds bound b acc'))
      | Comb(l,r) -> conds bound l (conds bound r acc)
      | Abs(v,bd) -> conds (v::bound) bd acc
      | _ -> acc in
    let ps = itlist (fun (_,th) acc ->
                if has_read (concl th) then conds [] (concl th) acc
                else acc) asl [] in
    MAP_EVERY (fun p -> TRY(SAMPLING_DECIDE_PROP_TAC p)) ps);;

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

(* ------------------------------------------------------------------------- *)
(* Simulation. SAMPLING_COND_REWRITE_TAC ths rewrites with the instances of  *)
(* the conditional equations ths whose conditions SIMPLE_ARITH_TAC proves;   *)
(* SAMPLING_W64_TAC so replaces the 64-bit zero extensions of small 32-bit   *)
(* sums and numbers by the numbers. SAMPLING_STEP_TAC execth n simulates     *)
(* step n with the facts about the indices in X0 and X1 that the address of  *)
(* a store with a UXTW register offset needs (SAMPLING_UXTW_THMS), for that  *)
(* step only, and then the normalizations and decisions above, and           *)
(* SAMPLING_RUN_TAC execth n stop simulates from step n until the PC is in   *)
(* the list stop or is undecided.                                            *)
(* ------------------------------------------------------------------------- *)

let SAMPLING_COND_REWRITE_TAC ths =
  let pats = map (fun th -> lhs(snd(dest_imp(snd(strip_forall(concl th))))),th)
                 (flat(map CONJUNCTS ths)) in
  W(fun (asl,w) ->
    let tml = list_mk_conj(w::map (concl o snd) asl) in
    let jobs = itlist (fun (pat,th) acc ->
       map (fun t -> t,th)
           (setify (find_terms (can (term_match [] pat)) tml)) @ acc)
       pats [] in
    MAP_EVERY (fun (t,th) ->
      let lth = PART_MATCH (lhs o rand) th t in
      MP_TAC lth THEN
      ANTS_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                             REWRITE_TAC[th])]) jobs);;

let SAMPLING_W64_TAC = SAMPLING_COND_REWRITE_TAC [SAMPLING_WORD_ZX_SMALL];;

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

let SAMPLING_UXTW_THMS (asl,w) =
  mapfilter (fun r ->
    let t = SAMPLING_REGVAL r (asl,w) in
    let e = rand t in
    if fst(dest_const(rator t)) <> "word" || is_numeral e then failwith ""
    else SPEC e VAL_WORD_ZX_UXTW) [`X0`; `X1`];;

let SAMPLING_STEP_TAC execth n (asl,w) =
  let ths = SAMPLING_UXTW_THMS (asl,w) in
  let ts = flat(map (fun th -> conjuncts(rand(concl th))) ths) in
  (MAP_EVERY (fun th ->
     TRY(MP_TAC th THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC])) ths THEN
   ARM_STEPS_TAC execth [n] THEN
   REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> mem (concl th) ts))) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
   TRY SAMPLING_W64_TAC THEN TRY SAMPLING_DECIDE_FLAGS_TAC THEN
   TRY SAMPLING_DECIDE_CONDS_TAC THEN TRY SAMPLING_DECIDE_BRANCH_TAC) (asl,w);;

let rec SAMPLING_RUN_TAC execth n stop (asl,w) =
  (SAMPLING_STEP_TAC execth n THEN
   (fun g -> let pcv = SAMPLING_REGVAL `PC` g in
             if is_cond pcv || mem pcv stop then ALL_TAC g
             else SAMPLING_RUN_TAC execth (n + 1) stop g)) (asl,w);;

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

let SAMPLING_LOOP_PC_TAC k ths =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; SAMPLING_TST_CONDS]) THEN
  let q = mk_binop `(<):num->num->bool`
              (mk_binop `(+):num->num->num` `i:num` `1`) k in
  W(fun g ->
    let pcv = SAMPLING_REGVAL `PC` g in
    if is_cond pcv then
      let p = lhand(rator pcv) in
      SUBGOAL_THEN (mk_eq(p,q)) (fun eth ->
         RULE_ASSUM_TAC(REWRITE_RULE[eth]) THEN REWRITE_TAC[eth]) THENL
       [SAMPLING_LOOP_EQ_TAC ths; ALL_TAC]
    else failwith "SAMPLING_LOOP_PC_TAC: decided");;

let SAMPLING_LOOP_EXIT_TAC k ths pc1 =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; SAMPLING_TST_CONDS]) THEN
  let q = mk_binop `(<):num->num->bool`
              (mk_binop `(+):num->num->num` `i:num` `1`) k in
  W(fun g ->
    let pcv = SAMPLING_REGVAL `PC` g in
    if is_cond pcv then failwith "SAMPLING_LOOP_EXIT_TAC: not decided" else
    let ct = mk_cond(q,pc1,pcv) in
    SUBGOAL_THEN (mk_eq(pcv,ct)) (fun eth ->
       let headconv = RAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
                       (GEN_REWRITE_CONV I [eth])))) in
       RULE_ASSUM_TAC(fun th ->
         let c = concl th in
         if is_eq c && can (term_match [] `read PC s`) (lhs c)
         then CONV_RULE(RAND_CONV(GEN_REWRITE_CONV I [eth])) th
         else if is_eq c && can (term_match [] `read events s`) (lhs c)
         then CONV_RULE headconv th
         else th)) THENL
     [SUBGOAL_THEN (mk_neg q) (fun nth -> REWRITE_TAC[nth]) THEN
      SAMPLING_LOOP_EQ_TAC ths;
      ALL_TAC]);;

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
   `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word k)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then a else b))` in
  prove(tm,
    REWRITE_TAC[SAMPLING_ALIGNED_16_32] THEN
    GEN_TAC THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
    W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

(* ------------------------------------------------------------------------- *)
(* The extended seeds of the SHAKE256 samplers: the seed of 64 bytes as four *)
(* 128-bit words, as the code loads and stores it, and the 66 bytes of the   *)
(* seed followed by a 16-bit nonce, or by a nonce byte and a zero byte. The  *)
(* nonces are stored from 32-bit registers, as the low 16 bits.              *)
(* ------------------------------------------------------------------------- *)

let MLD_READ_BYTES128 = prove
 (`!a:int64 s:armstate.
        read (memory :> bytes128 a) s = word(read (memory :> bytes(a,16)) s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPECL [`a:int64`; `16`; `read memory (s:armstate)`]
                READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let MLD_READ_BYTES_CHUNKS = prove
 (`!k (a:int64) n (s:armstate).
        read (memory :> bytes(a,16 * k)) s = n
        ==> !j. j < k
                ==> read (memory :> bytes128(word_add a (word(16 * j)))) s =
                    word((n DIV 2 EXP (128 * j)) MOD 2 EXP 128)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MLD_READ_BYTES128] THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`a:int64`; `16 * k`; `n:num`; `16 * j`; `16`; `s:armstate`]
    READ_MEMORY_BYTES_SUB) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `j < k` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `8 * 16 * j = 128 * j`; ARITH_RULE `8 * 16 = 128`]);;

let MLD_BYTES_OF_CHUNKS = prove
 (`!k (a:int64) n (s:armstate).
        n < 2 EXP (128 * k) /\
        (!j. j < k
             ==> read (memory :> bytes128(word_add a (word(16 * j)))) s =
                 word((n DIV 2 EXP (128 * j)) MOD 2 EXP 128))
        ==> read (memory :> bytes(a,16 * k)) s = n`,
  INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; EXP; ARITH_RULE `n < 1 <=> n = 0`] THEN
    SIMP_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `16 * SUC k = 16 + 16 * k`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`word_add a (word 16):int64`; `n DIV 2 EXP 128`; `s:armstate`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
      UNDISCH_TAC `n < 2 EXP (128 * SUC k)` THEN
      REWRITE_TAC[ARITH_RULE `128 * SUC k = 128 + 128 * k`];
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j + 1`) THEN
      ANTS_TAC THENL [UNDISCH_TAC `j < k` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                  ARITH_RULE `16 + 16 * j = 16 * (j + 1)`;
                  ARITH_RULE `128 + 128 * j = 128 * (j + 1)`]];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[LT_0; MULT_CLAUSES; EXP; DIV_1; WORD_ADD_0;
              MLD_READ_BYTES128] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_128; MOD_MOD_REFL] THEN
  MP_TAC(ISPECL [`a:int64`; `16`; `read memory (s:armstate)`]
                READ_BYTES_BOUND) THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; ARITH_RULE `8 * 16 = 128`] THEN
  SIMP_TAC[MOD_LT] THEN DISCH_THEN(K ALL_TAC) THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`n:num`; `2 EXP 128`] DIVISION) THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC);;

let MLD_READ_BYTES16 = prove
 (`!a:int64 s:armstate.
        read (memory :> bytes16 a) s = word(read (memory :> bytes(a,2)) s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPECL [`a:int64`; `2`; `read memory (s:armstate)`]
                READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let MLD_READ_BYTES66_NONCE16 = prove
 (`!a:int64 n (h:int16) s:armstate.
        read (memory :> bytes(a,64)) s = n /\
        read (memory :> bytes16(word_add a (word 64))) s = h
        ==> read (memory :> bytes(a,66)) s = n + 2 EXP 512 * val h`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[ARITH_RULE `66 = 64 + 2`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; MLD_READ_BYTES16; VAL_WORD;
              DIMINDEX_16] THEN
  AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPECL [`word_add a (word 64):int64`; `2`;
                 `read memory (s:armstate)`] READ_BYTES_BOUND) THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let MLD_READ_BYTES66_NONCE8 = prove
 (`!a:int64 n (b:byte) s:armstate.
        read (memory :> bytes(a,64)) s = n /\
        read (memory :> bytes8(word_add a (word 64))) s = b /\
        read (memory :> bytes8(word_add a (word 65))) s = word 0
        ==> read (memory :> bytes(a,66)) s = n + 2 EXP 512 * val b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `66 = (64 + 1) + 1`; READ_MEMORY_BYTES_SNOC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `64 + 1 = 65`; VAL_WORD_0] THEN ARITH_TAC);;

let SAMPLING_WORD_ZX_16 = prove
 (`(!x:int64. word_zx(word_zx x:int32):int16 = word_zx x) /\
   (!x:int16.
      word_zx(word_zx(word_zx(word_zx x:int32):int64):int32):int16 = x)`,
  CONJ_TAC THEN GEN_TAC THEN BITBLAST_TAC);;

let SAMPLING_WORD_ZX_8 = prove
 (`(!x:int64. word_zx(word_zx x:int32):byte = word_zx x) /\
   (!x:byte.
      word_zx(word_zx(word_zx(word_zx x:int32):int64):int32):byte = x)`,
  CONJ_TAC THEN GEN_TAC THEN BITBLAST_TAC);;

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
