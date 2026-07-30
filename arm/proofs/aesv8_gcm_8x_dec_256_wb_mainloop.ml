(* ========================================================================= *)
(* WB AES-256-GCM decrypt main loop (nblk > 8): ENSURES_WHILE proof.          *)
(*                                                                            *)
(* Extends the proven <=8-block WB chain (aesv8_gcm_8x_dec_256_wb.ml) to the  *)
(* software-pipelined 8-blocks-per-iteration main loop .L256_dec_main_loop    *)
(* (0x4a0..0x9ec), the GHASH catch-up prepretail (0x9f0..0xec0), and the tail *)
(* cascade (0xec0), so correctness holds for arbitrary nblk >= 1.             *)
(*                                                                            *)
(* Binary: arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.o (frozen).                    *)
(* Plan:   _docs/wb-main-loop-plan.md (sec 3b -> 4 -> 5), with the pipeline   *)
(*         correction from orchestrator/logs/plan-rationale.md baked in:      *)
(*         GHASH lags stores by one 8-block group, so the ENSURES_WHILE       *)
(*         invariant is the TWO-STREAM form (store/counter stream at 8(i+1),  *)
(*         GHASH stream at 8i, bridged by raw ciphertext regs q8..q15), NOT   *)
(*         a lag-free single fold.                                            *)
(*                                                                            *)
(* This file holds, in phase order:                                          *)
(*   Sec 1. Scalar rung lemmas (nblk>8 generalizations; pure word/arith).     *)
(*   Sec 2. Symbolic counter layer (gcm_ctr_add; closed form at symbolic k).  *)
(*   [later] FRONT-N capture (WBN_FRONT_BUF), ENSURES_WHILE loop, prepretail, *)
(*           recomposition, subroutine wrapper.                               *)
(*                                                                            *)
(* Lemmas in sec 1-2 were developed and committed in work.ml (commit          *)
(* 41f4953b) and are moved here verbatim (all proved; total < 2s).            *)
(* ========================================================================= *)

needs "arm/proofs/aesv8_gcm_8x_dec_256_wb.ml";;
(* aes_xts_common: IVAL_WORD_LT.  gcm_ctr_helpers: gcm_ctr_inc / _iter, the
   GCM_CTR_INC*_LANES lemmas.  Both are no-ops if wb.ml already pulled them. *)
needs "arm/proofs/utils/aes_xts_common.ml";;
needs "arm/proofs/utils/gcm_ctr_helpers.ml";;

(* ------------------------------------------------------------------------- *)
(* 1. Scalar rung lemmas (nblk > 8 generalizations of USHR_128NBLK /         *)
(*    AND_MASK_16NBLK).  All pure word/arith, no sim.                        *)
(*                                                                           *)
(* NOTE (signed pointer compares): the 0x42c/0x49c/0x9e4 cmp x0,x5 feed      *)
(* b.ge/b.lt = SIGNED conditions on pointers.  For nblk <= 8 x5 = in_p so    *)
(* the compare was reflexive; for nblk > 8 the exactness of                  *)
(* ival(x0) - ival(x5) needs the buffer to not straddle the 2^63 signed     *)
(* boundary: hypothesis WB_PTR_OK below (satisfied by all userspace bufs).   *)
(* ------------------------------------------------------------------------- *)

(* x9 := bit_len >> 3 = 16*nblk, now for ALL nblk with 128*nblk < 2^64 *)
let USHR_128NBLK_ANY = prove
 (`!nblk. 128 * nblk < 2 EXP 64
        ==> word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN AP_TERM_TAC THEN ARITH_TAC);;

(* the loop byte bound: (16*nblk - 1) AND ~127 = 128 * ((nblk-1) DIV 8) *)
let AND_MASK_16NBLK_ANY = prove
 (`!nblk. 1 <= nblk /\ 16 * nblk < 2 EXP 64
        ==> word_and (word_sub (word (16 * nblk)) (word 1))
                     (word 18446744073709551488):int64 =
            word (128 * ((nblk - 1) DIV 8))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word 18446744073709551488:int64 = word_not (word (2 EXP 7 - 1))`
    SUBST1_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD] THEN
  SUBGOAL_THEN `word_sub (word (16 * nblk)) (word 1):int64 = word (16 * nblk - 1)`
    SUBST1_TAC THENL
   [REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (16 * nblk - 1):int64) = 16 * nblk - 1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `(16 * nblk - 1) DIV 2 EXP 7 = (nblk - 1) DIV 8` SUBST1_TAC THENL
   [ALL_TAC; ARITH_TAC] THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d = (nblk - 1) DIV 8` THEN ABBREV_TAC `m = (nblk - 1) MOD 8` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `nblk = d * 8 + m + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `16 * m + 15` THEN ASM_ARITH_TAC);;

(* exact ival of an in-range pointer offset (for the signed pointer compares
   cmp x0,x5 at 0x3e0/0x440/0x9e4 feeding b.ge/b.lt) *)
let IVAL_PTR_ADD = prove
 (`!(p:int64) a. val p + a < 2 EXP 63 ==> ival (word_add p (word a)) = &(val p + a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_add p (word a):int64 = word (val p + a)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC IVAL_WORD_LT THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

(* NOTE: ival(word_neg(word d)) needs d <= 2^63 *)
let IVAL_NEG_SMALL = prove
 (`!d. d <= 2 EXP 63 ==> ival (word_neg (word d):int64) = -- &d`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_NEG] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[INT_ARITH `--(&9223372036854775808):int <= -- &d /\ -- &d < &9223372036854775808 <=> &d <= &9223372036854775808`] THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC);;

(* signed sub of two small words *)
let IVAL_WSUB_SMALL = prove
 (`!a d. a < 2 EXP 63 /\ d < 2 EXP 63
      ==> ival (word_sub (word a) (word d):int64) = &a - &d`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `a < d \/ d <= a:num`) THENL
   [SUBGOAL_THEN `word_sub (word a) (word d):int64 = word_neg (word (d - a))` SUBST1_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [WORD_RULE `word_sub (word a) (word d):int64 = word_neg (word_sub (word d) (word a))`] THEN
      AP_TERM_TAC THEN REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `ival (word_neg (word (d - a)):int64) = -- &(d - a)` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_NEG_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&(d - a):int = &d - &a` SUBST1_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_SUB] THEN ASM_ARITH_TAC; INT_ARITH_TAC];
    SUBGOAL_THEN `word_sub (word a) (word d):int64 = word (a - d)` SUBST1_TAC THENL
     [REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `ival (word (a - d):int64) = &(a - d)` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_WORD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&(a - d):int = &a - &d` SUBST1_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_SUB] THEN ASM_ARITH_TAC; INT_ARITH_TAC]]);;

(* small pointer has exact ival *)
let IVAL_SMALL_PTR = prove
 (`!(p:int64). val p < 2 EXP 63 ==> ival p = &(val p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IVAL_VAL; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SUBGOAL_THEN `bit 63 (p:int64) <=> F` SUBST1_TAC THENL
   [MP_TAC(ISPEC `p:int64` MSB_VAL) THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[BITVAL_CLAUSES] THEN INT_ARITH_TAC]);;

(* the generic signed pointer-compare flag resolver:
   cmp x0,x5 with x0 = p + a, x5 = (word d) + p; b.ge/b.lt read NF<=>VF,
   which under no-2^63-straddle collapses to a < d *)
let WB_PTRCMP_FLAGS = prove
 (`!(in_p:int64) a d.
      val in_p + a < 2 EXP 63 /\ val in_p + d < 2 EXP 63
      ==> (ival (word_sub (word_add in_p (word a)) (word_add (word d) in_p)) < &0 <=> a < d) /\
          ((ival (word_add in_p (word a)) - ival (word_add (word d) in_p) =
            ival (word_sub (word_add in_p (word a)) (word_add (word d) in_p))) <=> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_add (word d) in_p:int64 = word_add in_p (word d)` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `ival (word_add in_p (word a):int64) = &(val in_p + a) /\
                ival (word_add in_p (word d):int64) = &(val in_p + d)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC IVAL_PTR_ADD THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word_add in_p (word a)) (word_add in_p (word d)):int64 =
                word_sub (word a) (word d)` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `ival (word_sub (word a) (word d):int64) = &a - &d` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_WSUB_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  REWRITE_TAC[INT_ARITH `(&v + &a) - (&v + &d):int = &a - &d`] THEN
  REWRITE_TAC[INT_ARITH `&a - &d:int < &0 <=> &a:int < &d`; INT_OF_NUM_LT]);;

(* specialization for the 0x42c loop-entry b.ge with x0 = in_p (a = 0):
   in the nblk>8 regime the branch FALLS THROUGH (NF=T <=> VF=F test fails) *)
let WB_LOOPENTER_FLAGS = prove
 (`!(in_p:int64) nblk. 17 <= nblk /\ 128 * nblk < 2 EXP 62 /\
        val in_p + 16 * nblk < 2 EXP 63
    ==> (ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) < &0 <=> T) /\
        (ival in_p - ival (word_add (word (128 * (nblk - 1) DIV 8)) in_p) =
         ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) <=> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `d = 128 * (nblk - 1) DIV 8` THEN
  SUBGOAL_THEN `1 <= d /\ d <= 16 * nblk /\ d <= 2 EXP 63` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN
    MP_TAC(ASSUME `17 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 62`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub p (word_add (word d) p):int64 = word_neg (word d)`] THEN
  ASM_SIMP_TAC[IVAL_NEG_SMALL] THEN
  SUBGOAL_THEN `word_add (word d) in_p:int64 = word_add in_p (word d)` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `ival (word_add in_p (word d):int64) = &(val in_p + d)` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_PTR_ADD THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ival (in_p:int64) = &(val in_p)` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_SMALL_PTR THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `--(&d):int < &0 <=> &0:int < &d`; INT_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC]);;

(* d = 128*((nblk-1) DIV 8) > 128 iff nblk >= 17 (drives the 0x49c skip) *)
let D_GT_128 = prove
 (`!nblk. 17 <= nblk ==> (128 < 128 * (nblk - 1) DIV 8 <=> T)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `2 <= q ==> 128 < 128 * q`) THEN
  SUBGOAL_THEN `16 <= nblk - 1` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN ASM_ARITH_TAC);;

(* byte-level restatement (proved as warm-up; kept for the seam arithmetic) *)
let DIV128_16NBLK = prove
 (`!nblk. 1 <= nblk ==> (16 * nblk - 1) DIV 128 = (nblk - 1) DIV 8`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d = (nblk - 1) DIV 8` THEN ABBREV_TAC `m = (nblk - 1) MOD 8` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `nblk = d * 8 + m + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `16 * m + 15` THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 2. Symbolic counter layer: gcm_ctr_add w = "add w to the be-top-lane".    *)
(*    Gives the invariant a closed counter form at symbolic block index:     *)
(*    gcm_ctr_inc_iter k x = gcm_ctr_add (word k) x.                         *)
(*                                                                           *)
(*    OOM WARNING: do NOT prove GCM_CTR_ADD_LANES by direct BITBLAST -- the  *)
(*    symbolic 32-bit addend makes the BDD blow past 30GB (killed session    *)
(*    2026-07-24).  The factoring below keeps every BITBLAST wiring-only     *)
(*    (word_add never meets the BDD); whole layer proves in <1s.             *)
(* ------------------------------------------------------------------------- *)

let gcm_ctr_add = new_definition
 `gcm_ctr_add (w:32 word) (ivec:128 word) : 128 word =
   word_insert ivec (96,32)
     (word_bytereverse
        (word_add (word_bytereverse (word_subword ivec (96,32):(32)word)) w))`;;

let GCM_CTR_ADD_1 = prove
 (`gcm_ctr_add (word 1) = gcm_ctr_inc`,
  REWRITE_TAC[FUN_EQ_THM; gcm_ctr_add; gcm_ctr_inc]);;

(* wiring-only: byte decomposition of the byte-reversed top lane *)
let BREV_TOP_LANE = prove
 (`!ctr0:int128.
     word_bytereverse (word_subword ctr0 (96,32):32 word) =
     word_join
      (word_join (word_subword ctr0 (96,8):8 word) (word_subword ctr0 (104,8):8 word):16 word)
      (word_join (word_subword ctr0 (112,8):8 word) (word_subword ctr0 (120,8):8 word):16 word)`,
  GEN_TAC THEN BITBLAST_TAC);;

(* wiring-only: insert of brev s as the byte-join tower; s stays FREE so the
   abstract add never enters the BDD *)
let INSERT_BREV_WIRING = prove
 (`!(ctr0:int128) (s:32 word).
     word_insert ctr0 (96,32) (word_bytereverse s) : 128 word =
     word_join
      (word_join
       (word_join
        (word_join (word_subword s (0,8):8 word) (word_subword s (8,8):8 word):16 word)
        (word_join (word_subword s (16,8):8 word) (word_subword s (24,8):8 word):16 word)
        :32 word)
       (word_join
        (word_join (word_subword ctr0 (88,8):8 word) (word_subword ctr0 (80,8):8 word):16 word)
        (word_join (word_subword ctr0 (72,8):8 word) (word_subword ctr0 (64,8):8 word):16 word)
        :32 word) :64 word)
      (word_join
       (word_join
        (word_join (word_subword ctr0 (56,8):8 word) (word_subword ctr0 (48,8):8 word):16 word)
        (word_join (word_subword ctr0 (40,8):8 word) (word_subword ctr0 (32,8):8 word):16 word)
        :32 word)
       (word_join
        (word_join (word_subword ctr0 (24,8):8 word) (word_subword ctr0 (16,8):8 word):16 word)
        (word_join (word_subword ctr0 (8,8):8 word) (word_subword ctr0 (0,8):8 word):16 word)
        :32 word) :64 word)`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* the generic-w lanes lemma: RHS built programmatically from
   GCM_CTR_INC_LANES with `w` for `word 1` (exactly the harvested Q-lane
   shape from the front sim); proof is pure rewriting *)
let GCM_CTR_ADD_LANES =
  let lanes_w = subst [`w:32 word`,`word 1:32 word`]
    (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES)))) in
  let gl = list_mk_forall([`w:32 word`;`ctr0:int128`],
    mk_eq(list_mk_comb(`gcm_ctr_add`,[`w:32 word`;`ctr0:int128`]), lanes_w)) in
  prove(gl,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[gcm_ctr_add; BREV_TOP_LANE; INSERT_BREV_WIRING]);;

(* algebra of the symbolic add *)
let SUBWORD_INSERT_TOP = prove
 (`!(x:int128) (v:32 word). word_subword (word_insert x (96,32) v : int128) (96,32) = v`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let INSERT_INSERT_TOP = prove
 (`!(x:int128) (u:32 word) (v:32 word).
     word_insert (word_insert x (96,32) (u:32 word) : int128) (96,32) (v:32 word) : int128 =
     word_insert x (96,32) v`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let BREV_BREV_32 = prove
 (`!s:32 word. word_bytereverse (word_bytereverse s) = s`,
  GEN_TAC THEN BITBLAST_TAC);;

let INSERT_SELF_TOP = prove
 (`!x:int128. word_insert x (96,32) (word_subword x (96,32):32 word) : int128 = x`,
  GEN_TAC THEN BITBLAST_TAC);;

let GCM_CTR_ADD_COMPOSE = prove
 (`!(u:32 word) (v:32 word) (x:int128).
     gcm_ctr_add v (gcm_ctr_add u x) = gcm_ctr_add (word_add u v) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gcm_ctr_add] THEN
  REWRITE_TAC[SUBWORD_INSERT_TOP; INSERT_INSERT_TOP; BREV_BREV_32] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let GCM_CTR_ADD_0 = prove
 (`!x:int128. gcm_ctr_add (word 0) x = x`,
  GEN_TAC THEN REWRITE_TAC[gcm_ctr_add; WORD_ADD_0; BREV_BREV_32; INSERT_SELF_TOP]);;

(* the closed form the ENSURES_WHILE invariant needs: counter at symbolic
   block index k *)
let GCM_CTR_INC_ITER_ADD = prove
 (`!k x:int128. gcm_ctr_inc_iter k x = gcm_ctr_add (word k) x`,
  INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[gcm_ctr_inc_iter; GCM_CTR_ADD_0];
    ASM_REWRITE_TAC[gcm_ctr_inc_iter] THEN
    REWRITE_TAC[GSYM GCM_CTR_ADD_1; GCM_CTR_ADD_COMPOSE] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[ADD1; GSYM WORD_ADD] THEN
    CONV_TAC WORD_RULE]);;

(* the RAW counter accumulator kept in v30 (session-007 finding, session-008
   promoted here): byte-grouped rep with top 32-bit lane incremented by w.
   The body's first instr `rev32 v5,v30` reads it, so the Sec-4 invariant pins
   Q30 = gcm_ctr_raw (word (8*i+13)) ctr0 -- hence this definition must precede
   Sec 4.  Its algebra lemmas (SUBW_RAW_*, GCM_CTR_RAW_INCR, REV32_FOLD_TAC) are
   body-only and stay in Sec 9b.
   rev32(gcm_ctr_raw w ctr0) = gcm_ctr_add w ctr0 (the AES input for block w);
   word_add (gcm_ctr_raw w ctr0) (word 2^96) = gcm_ctr_raw (word_add w 1) ctr0. *)
let gcm_ctr_raw_def = new_definition
 `gcm_ctr_raw (w:32 word) (ctr0:int128) : int128 =
   word_join
    (word_join
      (word_add
        (word_join
          (word_join (word_subword ctr0 (96,8):8 word) (word_subword ctr0 (104,8):8 word):16 word)
          (word_join (word_subword ctr0 (112,8):8 word) (word_subword ctr0 (120,8):8 word):16 word):32 word)
        w)
      (word_join (word_join (word_subword ctr0 (64,8):8 word) (word_subword ctr0 (72,8):8 word):16 word)
        (word_join (word_subword ctr0 (80,8):8 word) (word_subword ctr0 (88,8):8 word):16 word):32 word):64 word)
    (word_join
      (word_join (word_join (word_subword ctr0 (32,8):8 word) (word_subword ctr0 (40,8):8 word):16 word)
        (word_join (word_subword ctr0 (48,8):8 word) (word_subword ctr0 (56,8):8 word):16 word):32 word)
      (word_join (word_join (word_subword ctr0 (0,8):8 word) (word_subword ctr0 (8,8):8 word):16 word)
        (word_join (word_subword ctr0 (16,8):8 word) (word_subword ctr0 (24,8):8 word):16 word):32 word):64 word):int128`;;

(* ------------------------------------------------------------------------- *)
(* 3. FRONT-N: capture the nblk>8 front (entry 0x20 -> loop head 0x4a0) as    *)
(*    WBN_FRONT_BUF.  Its harvested postcondition (state s288 at the loop     *)
(*    head) IS the i=0 instance of the ENSURES_WHILE loop invariant.          *)
(*                                                                            *)
(* Deltas vs wb.ml's <=8-block WB_FRONT_BUF (entry 0x20 -> 0x42c tail):       *)
(*  - hyps: 1<=nblk /\ nblk<=8  becomes  17<=nblk /\ 128*nblk<2^62 /\         *)
(*    val in_p + 16*nblk < 2^63 (the signed pointer-compare no-2^63-straddle).*)
(*  - prep uses the _ANY scalar rungs (X5 = word(128*((nblk-1)DIV8)) not 0).  *)
(*  - front steps 1..259 identical to WB_FRONT_STEP_TAC modulo mk_discard2[30]*)
(*    -> DISCARD_STALE_Q30_TAC, and STOPPING before the 0x42c branch (no <=8  *)
(*    INT_SUB_REFL / WORD_RULE collapse, since X5 != in_p here).              *)
(*  - the 0x42c b.ge (step 260) FALLS THROUGH via WB_LOOPENTER_FLAGS; then    *)
(*    bulk-8 segment 261..287; the 0x49c b.ge (step 288) FALLS THROUGH to     *)
(*    the loop head via WB_PTRCMP_FLAGS + D_GT_128.                           *)
(*                                                                            *)
(* Route A (as wb.ml WB_FRONT_BUF): the 8 in-flight keystream towers cannot   *)
(* be hand-written and the printed s288 term does not reparse, so we run the  *)
(* front once against a MINIMAL postcond, harvest the s288 assumptions with   *)
(* build_state_postcond_tms2 (folded to aes13 + gcm_ctr_inc^k lanes by        *)
(* wb_front_fold_tac), then prove.  The front therefore sims twice per cold   *)
(* load (once to harvest, once in the proof) -- the checkpoint hides this for *)
(* interactive work.                                                          *)
(* ------------------------------------------------------------------------- *)

(* nblk>8 front hypotheses: swap the (1<=nblk /\ nblk<=8) prefix of wb.ml's
   wb_front_hyps_tm for the nblk>=17 regime, KEEP every nonoverlapping/aligned/
   length conjunct.
   session-015: ALSO add nonoverlapping (out_p) (stackpointer,80).  wb.ml's
   wb_front_hyps_tm omits it, but the nblk>8 front's FRONT-0 group (0x430..0x498)
   does four `stp q,q,[x2],#32` stores to out_p BEFORE the loop head 0x4a0.
   Without out_p-vs-stack disjointness the stepper cannot prove those stores miss
   [sp+64], so it DROPS the reduction-constant fact
   read (memory :> bytes64 (sp+64)) s = word 0xc200000000000000 (needed by the
   body GHASH reduce; see the invariant [sp+64] conjunct + SESSION-014/015).
   VALIDATED (session-015): with this conjunct the fact survives the full front
   sim to s288 (=loop head 0x4a0) and is auto-harvested by
   build_state_postcond_tms2. *)
let wbn_front_hyps_tm =
  let _,rest1 = dest_conj wb_front_hyps_tm in
  let _,rest = dest_conj rest1 in
  mk_conj(`17 <= nblk /\ 128 * nblk < 2 EXP 62 /\ val (in_p:int64) + 16 * nblk < 2 EXP 63`,
          mk_conj(`nonoverlapping (out_p:int64,16 * nblk) (stackpointer:int64,80)`,
                  rest));;

let mk_wbn_front_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_tm, ens));;

(* pure-arith closer for the nblk>=17 side conditions *)
let NBLK_ARITH_TAC =
  MP_TAC(ASSUME `17 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 62`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

(* nblk>8 buffer prep: same shape as wb.ml WB_FRONT_PREP_BUF_TAC but with the
   _ANY rungs and the nblk>=17 arithmetic for the block-0 lane. *)
let WBN_FRONT_PREP_BUF_TAC =
  SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 in_p) s0 = bytes_to_int128 (SUB_LIST (0,16) ibytes)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`] INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
    ANTS_TAC THENL [NBLK_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)` ASSUME_TAC THENL
   [MATCH_MP_TAC USHR_128NBLK_ANY THEN NBLK_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word_sub (word (16 * nblk)) (word 1)) (word 18446744073709551488):int64 = word (128 * ((nblk - 1) DIV 8))` ASSUME_TAC THENL
   [MATCH_MP_TAC AND_MASK_16NBLK_ANY THEN NBLK_ARITH_TAC; ALL_TAC];;

(* input lanes 0..7 for the bulk-8 ldp at 0x430 *)
let WBN_LANES_TAC =
  SUBGOAL_THEN
   `!k. k < 8 ==> read (memory :> bytes128 (word_add in_p (word (16 * k)))) s0 =
                  bytes_to_int128 (SUB_LIST (16 * k, 16) (ibytes:byte list))`
   MP_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`]
      INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN(fun lth -> X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `k:num` lth) THEN ANTS_TAC THENL
       [MP_TAC(ASSUME `k < 8`) THEN NBLK_ARITH_TAC; REWRITE_TAC[]]);
    DISCH_THEN(fun lth ->
      EVERY(map (fun i ->
        ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)
          (MP (SPEC (mk_small_numeral i) lth)
              (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral i) `8`)))))
        (0--7)))];;

let wbn_init_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check(is_conj o concl)) THEN
  WBN_FRONT_PREP_BUF_TAC;;

(* keep only the latest read Q30 fact (the rev32 counter accumulator grows a
   big tower each step; older ones are dead) *)
let state_num_of_read_q30 th =
  let c = concl th in
  try (match lhs c with
       | Comb(Comb(Const("read",_),q),st) when string_of_term q = "Q30" ->
           let s = fst(dest_var st) in
           if String.length s > 1 && s.[0] = 's'
           then int_of_string (String.sub s 1 (String.length s - 1)) else (-1)
       | _ -> (-1))
  with _ -> (-1);;
let DISCARD_STALE_Q30_TAC : tactic = fun (asl,w) ->
  let nums = List.filter (fun n -> n >= 0)
    (List.map (fun (_,th) -> state_num_of_read_q30 th) asl) in
  if nums = [] then ALL_TAC (asl,w) else
  let mx = itlist max nums (-1) in
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let n = state_num_of_read_q30 th in n >= 0 && n < mx) (asl,w);;

(* front steps 1..259 (up to but NOT including the 0x42c branch at step 260) *)
let WBN_FRONT_STEP_TAC =
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--5) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC) (6--30)) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (31--84) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (85--173) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (174--177) THEN
  GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_STALE_Q30_TAC THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (178--189) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[Q19_BREVXI]) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (190--254) THEN
  DISCARD_STALE_Q30_TAC THEN GCM_SIMD_SIMPLIFY_TAC THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [255] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (256--259);;

(* 0x42c b.ge (step 260): nblk>=17 => X0=in_p, X5=in_p+d, NF=T VF=F, FALLS THRU *)
let WBN_RESOLVE_42C_TAC : tactic =
  MP_TAC(SPECL [`in_p:int64`; `nblk:num`] WB_LOOPENTER_FLAGS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]));;

(* 0x49c b.ge (step 288): X0=in_p+128, X5=in_p+d, 128<d for nblk>=17 => NF=T
   VF=F, FALLS THROUGH to loop head 0x4a0 *)
let WBN_RESOLVE_49C_TAC : tactic = fun (asl,w) ->
  (MP_TAC(SPECL [`in_p:int64`; `128`; `128 * (nblk - 1) DIV 8`] WB_PTRCMP_FLAGS) THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL
      [MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN NBLK_ARITH_TAC;
       MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN
       MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN NBLK_ARITH_TAC];
     ALL_TAC] THEN
   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
   MP_TAC(SPEC `nblk:num` D_GT_128) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) (asl,w);;

(* the complete front sim entry 0x20 -> loop head 0x4a0 (ends at s288) *)
let WBN_FRONT_FULL_TAC =
  wbn_init_tac THEN WBN_LANES_TAC THEN WBN_FRONT_STEP_TAC THEN
  WBN_RESOLVE_42C_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (260--260) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_STALE_Q30_TAC) (261--287)) THEN
  WBN_RESOLVE_49C_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (288--288);;

(* Harvest the s288 postcondition (the i=0 invariant), then prove WBN_FRONT_BUF.
   The harvest runs the front against a minimal postcond; wb_front_fold_tac
   compacts the 8 keystream towers to aes13 + gcm_ctr_inc^k lanes.  Reuses
   wb.ml's build_state_postcond_tms2 (keeps every read _ s288 fact + the
   aligned_bytes_loaded conjunct). *)
let wbn_front_postcond_i0 =
  let min_goal = mk_wbn_front_goal `\s:armstate. read PC s = word (pc + 0x4a0)` in
  let _ = g min_goal in
  let _ = e (WBN_FRONT_FULL_TAC THEN wb_front_fold_tac) in
  let (asl288,_) = top_goal() in
  let pc = build_state_postcond_tms2 "s288" asl288 in
  let _ = b() in pc;;

(* WBN_FRONT_BUF: the FRONT-N theorem.  Its postcond = the i=0 loop invariant
   (two-stream pipelined form): q8..q15 = RAW ct blocks 0..7 pending fold,
   Q19 = word_bytereverse xi (GHASH acc over blocks 0..-1 = tag only), stores
   done for blocks 0..7, counters at 8..12, X0=in_p+128, X2=out_p+128.
   Close = WB_FRONT_BUF's, plus one REWRITE_TAC[WORD_ADD_0] (the harvested Q30
   lower lanes carry a spurious word_add _ (word 0) vs the sim's assumption). *)
let WBN_FRONT_BUF = prove(mk_wbn_front_goal wbn_front_postcond_i0,
  WBN_FRONT_FULL_TAC THEN wb_front_fold_tac THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC);;

(* ------------------------------------------------------------------------- *)
(* 4. Phase 2: the TWO-STREAM ENSURES_WHILE loop invariant (FROZEN).          *)
(*                                                                            *)
(* Derived (session-003) by generalizing WBN_FRONT_BUF's harvested s288       *)
(* postcond to symbolic block index i.  The i=0 instance was VALIDATED to     *)
(* follow from WBN_FRONT_BUF: 44 of 47 conjuncts (all registers, counters,    *)
(* keystreams, GHASH acc, stores, pointers) close by                          *)
(*   CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN                                  *)
(*   RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN                *)
(*   REWRITE_TAC[GCM_CTR_INC_ITER_ADD; GCM_CTR_ADD_1; GSYM GCM_CTR_ADD_LANES] *)
(*     THEN REWRITE_TAC[list_of_seq; MAP; ghash_polyval_acc] THEN             *)
(*   RULE_ASSUM_TAC(REWRITE_RULE[GCM_CTR_INC_LANES;..;GCM_CTR_INC7_LANES])    *)
(*     THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN         *)
(*   REWRITE_TAC[GCM_CTR_ADD_0] THEN CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_   *)
(*     CONV) THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN                     *)
(*   REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[].                          *)
(*                                                                            *)
(* GAP (documented, sound): the remaining 3 conjuncts                         *)
(*   read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes       *)
(*   read (memory :> bytes128 key_p) s = k0                                   *)
(*   htable_mem_dec h htbl_p s                                                *)
(* are loop-CONSTANTS that hold at the loop head (they are in wb_front_pre_tm *)
(* and NOT in the front MAYCHANGE frame -> preserved) but are NOT in          *)
(* WBN_FRONT_BUF's harvested postcond (build_state_postcond_tms2 keeps only   *)
(* `read _ s = _` + aligned_bytes_loaded, so htable_mem_dec is dropped, and   *)
(* the in_p/key_p reads were s0 facts not re-stated at s288).  FIX for next   *)
(* session: extend the front postcond harvest to re-assert these 3 (add them  *)
(* to wbn_front_postcond_i0 / the keep-filter, OR carry them via a strengthen *)
(* step), then WBN_FRONT_BUF closes them from the precond (they are in the    *)
(* MAYCHANGE-preserved set).  With that, the ENSURES_WHILE_UP_TAC entry       *)
(* subgoal (i=0) closes by MATCH_MP_TAC WBN_FRONT_BUF + the tactic above.     *)
(*                                                                            *)
(* Two-stream reading of the invariant (VERIFIED off the i=0 goal):           *)
(*  - store/counter stream AHEAD at 8(i+1): X0=in_p+128(i+1), X2=out_p+128(i+1)*)
(*    Q0..Q4 = gcm_ctr_add (word (8i+8..12)) ctr0 (next group's counters),    *)
(*    Q5..Q7 = plaintext blocks at 8i+5..7 (in-flight keystream XOR),         *)
(*    stores done for all j < 8(i+1).                                         *)
(*  - GHASH stream LAGS at 8i: Q19 = ghash_polyval_acc (byteswap128 h)        *)
(*    (word_bytereverse xi) over reversed raw ct blocks 0..8i-1;              *)
(*    q8..q15 = RAW ct blocks 8i..8i+7 pending fold (the bridge).             *)
(*                                                                            *)
(* STEP-CASE TODO (Phase 4, plan-rationale risk #2): the +8*i offset on the   *)
(* Q5..Q7 keystream indices (5,6,7 at i=0, all < 8) must be READ OFF the      *)
(* loop-body sim goal, not trusted from this generalization.                  *)
(* loop control flow (objdump): head pc1=pc+0x4a0; back-edge cmp x0,x5 @0x9e4 *)
(* + b.lt 0x4a0 @0x9ec (SIGNED, so a P-variant / WB_PTRCMP_FLAGS handles it); *)
(* exit fall-through @0x9f0.  count q = (nblk-9) DIV 8.                        *)
(*                                                                            *)
(* session-011: Q26/Q27/Q28 (=k12/k13/k14) DROPPED from the invariant below   *)
(* — objdump-verified dead live-ins (loop head 0x4a4 ldp q26,q27,[x11] +      *)
(* 0x518 ldp q28,q26,[x11,#32]; prepretail seam 0x9f0 ldp q26,q27,[x11] — all *)
(* reload before first aese v_,v26/28 uses at 0x4d8/0x570).  Removal gated by *)
(* the alpha-shadow wbn_loop_invariant_v2 (ENTRY_V2 re-proved to hyps=0).      *)
(* CAUTION: do NOT put (* *) comments or backticks INSIDE the term backquote   *)
(* below — HOL's in-term comment token is //, and (* *) / ` break the parse   *)
(* (session-012 fix: the session-011 in-term note broke the cold-load).       *)
(* ------------------------------------------------------------------------- *)

let wbn_loop_invariant = new_definition
 `wbn_loop_invariant (pc:num) (ctr0:int128) (in_p:int64) (out_p:int64)
    (xi_p:int64) (ivec_p:int64) (key_p:int64) (htbl_p:int64) (stackpointer:int64)
    (nblk:num) (ibytes:byte list) (xi:int128) (h:int128)
    (k0:int128) k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 (k14:int128) =
  \(i:num) (s:armstate).
    aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
    read PC s = word (pc + 1184) /\
    read Q0 s = gcm_ctr_add (word (8 * i + 8)) ctr0 /\
    read Q1 s = gcm_ctr_add (word (8 * i + 9)) ctr0 /\
    read Q2 s = gcm_ctr_add (word (8 * i + 10)) ctr0 /\
    read Q3 s = gcm_ctr_add (word (8 * i + 11)) ctr0 /\
    read Q4 s = gcm_ctr_add (word (8 * i + 12)) ctr0 /\
    read Q5 s =
    word_xor
    (word_xor (bytes_to_int128 (SUB_LIST (16 * (8 * i + 5),16) ibytes))
    (aes13 (gcm_ctr_inc_iter (8 * i + 5) ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
     k10 k11 k12 k13)) k14 /\
    read Q6 s =
    word_xor
    (word_xor (bytes_to_int128 (SUB_LIST (16 * (8 * i + 6),16) ibytes))
    (aes13 (gcm_ctr_inc_iter (8 * i + 6) ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
     k10 k11 k12 k13)) k14 /\
    read Q7 s =
    word_xor
    (word_xor (bytes_to_int128 (SUB_LIST (16 * (8 * i + 7),16) ibytes))
    (aes13 (gcm_ctr_inc_iter (8 * i + 7) ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
     k10 k11 k12 k13)) k14 /\
    read Q8 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 0),16) ibytes) /\
    read Q9 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 1),16) ibytes) /\
    read Q10 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 2),16) ibytes) /\
    read Q11 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 3),16) ibytes) /\
    read Q12 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 4),16) ibytes) /\
    read Q13 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 5),16) ibytes) /\
    read Q14 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 6),16) ibytes) /\
    read Q15 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 7),16) ibytes) /\
    read Q19 s =
    ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
    (MAP word_bytereverse
    (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) (8 * i))) /\
    read X0 s = word_add in_p (word (128 * (i + 1))) /\
    read X2 s = word_add out_p (word (128 * (i + 1))) /\
    read X4 s = word_add in_p (word (16 * nblk)) /\
    read X5 s = word_add (word (128 * (nblk - 1) DIV 8)) in_p /\
    read X9 s = word (16 * nblk) /\
    read X10 s = word_add stackpointer (word 64) /\
    read X1 s = word (128 * nblk) /\
    read X15 s = word 4294967296 /\
    read Q31 s = word 79228162514264337593543950336 /\
    read Q30 s = gcm_ctr_raw (word (8 * i + 13)) ctr0 /\
    read X16 s = ivec_p /\
    read X6 s = htbl_p /\
    read X3 s = xi_p /\
    read X11 s = key_p /\
    read SP s = stackpointer /\
    read (memory :> bytes64 (word_add stackpointer (word 64))) s =
    word 13979173243358019584 /\
    (!j. j < 8 * (i + 1)
         ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
             word_xor
             (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16) ibytes))
             (aes13 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
              k10 k11 k12 k13)) k14) /\
    read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes /\
    read (memory :> bytes128 key_p) s = k0 /\
    read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
    read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
    read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
    read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
    read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
    read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
    read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
    read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
    read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
    read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
    read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
    read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
    read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
    read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
    htable_mem_dec h htbl_p s`;;

(* ---- Entry-subgoal recipe (validated interactively, session-003) ----------
   The ENSURES_WHILE_UP_TAC entry subgoal is  pre ==> (PC=pc1 /\ inv 0 s).
   Given WBN_FRONT_BUF establishes pre ==> (PC=pc+0x4a0 /\ <postcond s>), the
   i=0 invariant  (wbn_loop_invariant ... 0 s)  follows from <postcond s> PLUS
   the 3 loop-constants (in_p read-only, key_p=k0, htable_mem_dec) once those
   are added to WBN_FRONT_BUF's harvest.  The closing tactic (proves 44/47
   directly from the postcond hyps; the 3 come from the extended front):

     GEN_TAC THEN REWRITE_TAC[wbn_loop_invariant] THEN
     CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
     CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
     REWRITE_TAC[GCM_CTR_INC_ITER_ADD; GCM_CTR_ADD_1; GSYM GCM_CTR_ADD_LANES] THEN
     REWRITE_TAC[list_of_seq; MAP; ghash_polyval_acc] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES;
        GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES; GCM_CTR_INC5_LANES;
        GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES]) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
     REWRITE_TAC[GCM_CTR_ADD_0] THEN
     CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
     CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
     REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[]

   With the RAW WBN_FRONT_BUF postcond as the assumption set this reduces the
   goal to EXACTLY the 3 loop-constant conjuncts (confirmed session-003).  When
   packaging as a standalone lemma with the postcond as a `\s.`-abstraction
   antecedent, watch the beta step: STRIP_TAC must see the antecedent already
   beta-reduced (do CONV_TAC(TOP_DEPTH_CONV BETA_CONV) on the WHOLE goal, incl.
   the antecedent, before STRIP_TAC) — a naive `(\s.P) s /\ (\s.Q) s ==> ...`
   left unreduced makes STRIP_TAC give conjunct hyps still wrapped.

   NEXT-SESSION FIX to get a clean entry (no extra hyps):
   extend WBN_FRONT_BUF so its postcond re-asserts the 3 loop-constants.  Either
   (a) widen build_state_postcond_tms2's keep-filter to also retain
       `htable_mem_dec _ _ s` and the input/key `read _ s = _` facts (they are
       preserved: NOT in wb_front_frame_tm's MAYCHANGE), re-run the front sim,
       or (b) prove WBN_FRONT_BUF_EXT = WBN_FRONT_BUF strengthened with the 3
       (they hold in wb_front_pre_tm and survive the frame), via a framing/
       ENSURES_TRANS wrapper avoiding a full re-sim.  Then the entry subgoal of
       ENSURES_WHILE_UP_TAC closes by MATCH_MP_TAC WBN_FRONT_BUF_EXT + the tactic
       above (no leftover conjuncts). *)

(* ------------------------------------------------------------------------- *)
(* 5. Phase 3: GHASH 8-block extension algebra (pure list/field, no sim).     *)
(*                                                                            *)
(* The invariant's Q19 GHASH accumulator is                                   *)
(*   ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)                  *)
(*     (MAP word_bytereverse (list_of_seq blk (8 * i)))                       *)
(* where blk k = bytes_to_int128 (SUB_LIST (16*k,16) ibytes) is the raw ct    *)
(* block k.  The step case (i -> i+1) must extend this fold from 8*i to       *)
(* 8*(i+1) blocks.  The loop body performs exactly 8 Horner steps (one        *)
(* polyval_dot per fresh ciphertext block, each byte-reversed then XORed into *)
(* the accumulator), so we need the fold over 8*(i+1) blocks to equal the     *)
(* fold over 8*i blocks continued by 8 explicit steps over blocks            *)
(* 8*i .. 8*i+7.  This is pure algebra over GHASH_ACC_APPEND                   *)
(* (common/polyval_ghash.ml:62) + list_of_seq, provable BEFORE any sim.       *)
(* ------------------------------------------------------------------------- *)

(* list_of_seq splits at any offset (APPEND-at-end recursion, induct on n) *)
let LIST_OF_SEQ_SPLIT = prove
 (`!(f:num->int128) m n. list_of_seq f (m + n) =
     APPEND (list_of_seq f m) (list_of_seq (\j. f (m + j)) n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; list_of_seq; APPEND_NIL] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; list_of_seq; APPEND_ASSOC]);;

(* generic group-extension of the byte-reversed GHASH fold: split m+n *)
let GHASH_ACC_GROUP_EXTEND = prove
 (`!(g:num->int128) H acc m n.
    ghash_polyval_acc H acc (MAP word_bytereverse (list_of_seq g (m + n))) =
    ghash_polyval_acc H
      (ghash_polyval_acc H acc (MAP word_bytereverse (list_of_seq g m)))
      (MAP word_bytereverse (list_of_seq (\j. g (m + j)) n))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_OF_SEQ_SPLIT; MAP_APPEND; GHASH_ACC_APPEND]);;

(* clean 8-element unfold of list_of_seq (numerals, no SUC towers) *)
let LIST_OF_SEQ_8 = prove
 (`!f:num->int128. list_of_seq f 8 =
    [f 0; f 1; f 2; f 3; f 4; f 5; f 6; f 7]`,
  GEN_TAC THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[num_CONV `8`; num_CONV `7`; num_CONV `6`;
    num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`;
    LIST_OF_SEQ])) THEN
  REWRITE_TAC[o_THM] THEN CONV_TAC(DEPTH_CONV NUM_SUC_CONV) THEN REWRITE_TAC[]);;

(* THE Phase-3 deliverable: extend the invariant's GHASH fold by one 8-block  *)
(* group.  RHS = the 8*i fold, continued by a fold over the 8 concrete new    *)
(* raw-ct blocks (8*i .. 8*i+7).  Instantiate blk := \k. bytes_to_int128      *)
(* (SUB_LIST (16*k,16) ibytes) in the body; REWRITE_TAC[MAP; ghash_polyval_acc]*)
(* then unfolds the RHS to the nested polyval_dot/word_xor Horner chain the    *)
(* 8 body GHASH instructions produce. *)
let GHASH_ACC_8BLOCK_EXTEND = prove
 (`!(blk:num->int128) H acc i.
    ghash_polyval_acc H acc
      (MAP word_bytereverse (list_of_seq blk (8 * (i + 1)))) =
    ghash_polyval_acc H
      (ghash_polyval_acc H acc (MAP word_bytereverse (list_of_seq blk (8 * i))))
      (MAP word_bytereverse
        [blk (8 * i); blk (8 * i + 1); blk (8 * i + 2); blk (8 * i + 3);
         blk (8 * i + 4); blk (8 * i + 5); blk (8 * i + 6); blk (8 * i + 7)])`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `8 * (i + 1) = 8 * i + 8` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GHASH_ACC_GROUP_EXTEND] THEN
  REWRITE_TAC[LIST_OF_SEQ_8] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ADD_CLAUSES]);;

(* Body GHASH-close bridge (session-011): the generalization of wb.ml's         *)
(* spec_to_byteform_wb8 to an ARBITRARY incoming accumulator `acc` (the running *)
(* fold read Q19 at body entry) in place of the tail's hardwired                *)
(* `word_bytereverse xi`.  Same H-power hypotheses (supplied by the htable      *)
(* reduce steps during the sim), same machine byteform RHS.  Proof is verbatim  *)
(* the wb.ml one (STRIP; GHASH_POLYVAL_ACC_8; ASM_REWRITE; AP_TERM; WORD_RULE) — *)
(* it never depended on the acc being xi.  Composes with GHASH_ACC_8BLOCK_EXTEND *)
(* (acc := the invariant's 8*i fold) to close the loop body's Q19.              *)
let SPEC_TO_BYTEFORM_WB8_ACC = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 =
   polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 =
   polyval_dot
   (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h5 =
   polyval_dot
   (polyval_dot
    (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h6 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h7 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot
      (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
      (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h8 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot
      (polyval_dot
       (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
       (byteswap128 h))
      (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (acc:int128)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
        word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
        word_bytereverse cph6; word_bytereverse cph7] =
       polyval_reduce_prop3
       (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul (word_xor acc (word_bytereverse cph0)) (byteswap128 h8))
        (word_pmul (word_bytereverse cph1) (byteswap128 h7)))
        (word_pmul (word_bytereverse cph2) (byteswap128 h6)))
        (word_pmul (word_bytereverse cph3) (byteswap128 h5)))
        (word_pmul (word_bytereverse cph4) (byteswap128 h4)))
        (word_pmul (word_bytereverse cph5) (byteswap128 h3)))
        (word_pmul (word_bytereverse cph6) (byteswap128 h2)))
       (word_pmul (word_bytereverse cph7) (byteswap128 h)))`,
  STRIP_TAC THEN REWRITE_TAC[GHASH_POLYVAL_ACC_8] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* The COMPOSED body Q19-close (session-011): the invariant's Q19 conjunct at    *)
(* i+1 equals the machine 8-block byteform, with the incoming accumulator being  *)
(* the invariant's OWN 8*i fold.  = GHASH_ACC_8BLOCK_EXTEND (split the 8*(i+1)   *)
(* fold into [8 fresh blocks] on the 8*i fold) then SPEC_TO_BYTEFORM_WB8_ACC     *)
(* (acc := that 8*i fold).  This is exactly what the loop body's Q19 SUBGOAL     *)
(* must match once the store/GHASH window is simulated with the raw reduce       *)
(* preserved (H-power hyps `byteswap128 h2..h8 = polyval_dot..` are produced by  *)
(* the htable reduce steps during the sim).  Proved to hyps=0: the whole GHASH   *)
(* algebra of the body close is settled here, sim-free.                          *)
let BODY_Q19_CLOSE_ALGEBRA = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 =
   polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 =
   polyval_dot
   (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h5 =
   polyval_dot
   (polyval_dot
    (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h6 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h7 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot
      (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
      (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h8 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot
      (polyval_dot
       (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
       (byteswap128 h))
      (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        (MAP word_bytereverse
         (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes))
          (8 * (i+1)))) =
        polyval_reduce_prop3
        (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
         (word_pmul (word_xor (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
           (MAP word_bytereverse
            (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) (8 * i))))
           (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+0),16) ibytes)))) (byteswap128 h8))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+1),16) ibytes))) (byteswap128 h7)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+2),16) ibytes))) (byteswap128 h6)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+3),16) ibytes))) (byteswap128 h5)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+4),16) ibytes))) (byteswap128 h4)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+5),16) ibytes))) (byteswap128 h3)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+6),16) ibytes))) (byteswap128 h2)))
        (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+7),16) ibytes))) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[GHASH_ACC_8BLOCK_EXTEND; MAP] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * i = 16 * (8*i+0)`] THEN
  MATCH_MP_TAC SPEC_TO_BYTEFORM_WB8_ACC THEN ASM_REWRITE_TAC[]);;

(* --------------------------------------------------------------------------- *)
(* session-061 (Q19 R1' close, part 1 of 2): THE REDUCE-DATAFLOW value-equality *)
(* the reviewer flagged as the "real proof work".  The body's GHASH reduce      *)
(* window (asm 0x924..0x9b4) reads three separable 128-bit accumulators at s289 *)
(*   PL = Q17 = Sum_k karatsuba_block_pl,  PH = Q19 = Sum_k karatsuba_block_ph,  *)
(*   PM = Q18 = Sum_k karatsuba_block_pm,  Barrett modulus raw in Q16,          *)
(* then runs the shared Barrett W-reduction, landing read Q19 s326 in EXACTLY   *)
(* the byteform LHS below (over OPAQUE PL/PH/PM — the sim keeps them abbreviated *)
(* so the reduce window stays small).  This lemma says that byteform is         *)
(* polyval_reduce_prop3 (pack_corrected PL PH PM) — the pre-byte-reversal prop3  *)
(* on the Karatsuba-corrected packed value.  It is the machine analogue of      *)
(* common/ghash_nblock_karatsuba.ml's KARATSUBA_REDUCE_AS_PROP3 (same reduce,    *)
(* proven the same way: KARATSUBA_LIMB_* to reduce the pack lanes, then two      *)
(* pmul abbreviations (wa/wv) so the residual is a pure opaque-atom bit identity *)
(* closed by WORD_BLAST).  Reconciles s056 (the s326 OUTPUT is byteform, NOT a   *)
(* karatsuba_reduce_shared instance) with R1' (the krs INPUT triple lives at     *)
(* s289): here the OUTPUT = prop3 ∘ pack_corrected of the INPUT triple, no outer *)
(* word_reversefields — exactly matching BODY_Q19_CLOSE_ALGEBRA's prop3 RHS.     *)
(* NOTE: the 4 KARATSUBA_LIMB_* must be listed individually — the bundled CONJ   *)
(* KARATSUBA_LIMBS does NOT rewrite via REWRITE_TAC (nested-CONJ matcher).       *)
let WBN_MACHINE_REDUCE_IS_PROP3_PACK = prove
 (`!PL PH PM:int128.
     word_xor
      (word_xor PH
       (word_subword
        (word_join
         (word_xor
          (word_xor (word_xor (word_xor PM PL) PH)
          (word_pmul (word_subword PL (0,64) :64 word) (word 13979173243358019584 :64 word)))
         (word_subword (word_join PL PL :256 word) (64,128)))
        (word_xor
         (word_xor (word_xor (word_xor PM PL) PH)
         (word_pmul (word_subword PL (0,64) :64 word) (word 13979173243358019584 :64 word)))
        (word_subword (word_join PL PL :256 word) (64,128))) :256 word)
       (64,128)))
      (word_pmul
       (word_subword
        (word_xor
         (word_xor (word_xor (word_xor PM PL) PH)
         (word_pmul (word_subword PL (0,64) :64 word) (word 13979173243358019584 :64 word)))
        (word_subword (word_join PL PL :256 word) (64,128)))
       (0,64) :64 word)
      (word 13979173243358019584 :64 word)) =
     polyval_reduce_prop3 (pack_corrected PL PH PM)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pack_corrected; polyval_reduce_prop3; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  SUBGOAL_THEN
   `word_subword (word_join (PL:int128) (PL:int128) :256 word) (64,128) :128 word =
    word_join (word_subword PL (0,64):64 word) (word_subword PL (64,64):64 word)`
   SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[KARATSUBA_LIMB_0_63; KARATSUBA_LIMB_64_127;
              KARATSUBA_LIMB_128_191; KARATSUBA_LIMB_192_255] THEN
  ABBREV_TAC `wa:int128 = word_pmul (word_subword (PL:int128) (0,64):64 word)
                                    (word 13979173243358019584:64 word)` THEN
  SUBGOAL_THEN
   `word_subword
      (word_xor (word_xor (word_xor (word_xor PM PL) PH) (wa:int128))
                (word_join (word_subword (PL:int128) (0,64):64 word)
                           (word_subword PL (64,64):64 word)))
      (0,64) :64 word =
    word_xor (word_xor (word_subword (PL:int128) (64,64):64 word)
                       (word_subword (word_xor (word_xor PL PH) PM) (0,64):64 word))
             (word_subword (wa:int128) (0,64):64 word)`
   SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  ABBREV_TAC `wv:int128 = word_pmul
     (word_xor (word_xor (word_subword (PL:int128) (64,64):64 word)
                         (word_subword (word_xor (word_xor PL PH) PM) (0,64):64 word))
               (word_subword (wa:int128) (0,64):64 word))
     (word 13979173243358019584:64 word)` THEN
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* session-062 (Q19 R1' close, part 2 of 2): BLOCK-ALGEBRA reconciliation     *)
(* facts.  These bridge the machine s289 accumulators (Q17/Q19/Q18 = the       *)
(* separable Sigma-PL/PH/PM triple, in raw word_reversefields/word_join/       *)
(* byteswap128-tower form) to the abstract kara_acc projection of an 8-quad    *)
(* list, so KARA_ACC_PACK_HELPER + KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN can      *)
(* pack them to Sum_k word_pmul input_k h_k = BODY_Q19_CLOSE_ALGEBRA's prop3   *)
(* argument.  All are pure free-variable WORD_BLAST/WORD_RULE identities.      *)
(* --------------------------------------------------------------------------- *)

(* fact 1: the two byte-reversal spellings coincide (machine uses reversefields *)
(* 8, the spec/kara side uses word_bytereverse). *)
let WRF8_IS_BYTEREVERSE = prove
 (`!x:int128. word_reversefields 8 x = word_bytereverse x`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* fact 2: karatsuba_mid is byteswap-invariant (it XORs the two 64-halves, and *)
(* byteswap128 swaps them).  Lets the htable mid cell `karatsuba_mid h` satisfy *)
(* KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN's `subword hk (0,64) = karatsuba_mid     *)
(* (byteswap128 h)` precondition. *)
let KMID_BYTESWAP_INV = prove
 (`!h:int128. karatsuba_mid h = karatsuba_mid (byteswap128 h)`,
  GEN_TAC THEN REWRITE_TAC[karatsuba_mid; byteswap128] THEN CONV_TAC WORD_BLAST);;

(* fact 3 (block-0 SOFAR lane-collapse): block 0's operand enters via a rot64'd *)
(* word_join of the running accumulator SOFAR with the first ciphertext block.  *)
(* The reduce takes the (64,64) / (0,64) sub-lane of the XOR of the two joins,  *)
(* which collapses to the plain (0,64) / (64,64) sub-lane of `word_xor S X`.    *)
let LANE_COLLAPSE = prove
 (`(!S X:int128. word_subword (word_xor (word_subword (word_join S S:256 word) (64,128):128 word)
                            (word_subword (word_join X X:256 word) (64,128):128 word)) (64,64):64 word
    = word_subword (word_xor S X) (0,64):64 word) /\
   (!S X:int128. word_subword (word_xor (word_subword (word_join S S:256 word) (64,128):128 word)
                            (word_subword (word_join X X:256 word) (64,128):128 word)) (0,64):64 word
    = word_subword (word_xor S X) (64,64):64 word)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* fact 4 (pmull2/pmull PAIR mid-input lanes): the machine computes the PM mid  *)
(* products two blocks at a time (a pmull2 then pmull over the packed lanes of  *)
(* blocks A and B).  The (64,64)/(0,64) sub-lane of the XOR of the hi-join and  *)
(* lo-join recovers each single block's (lo XOR hi) mid-input. *)
let PM_LANE_HI = prove
 (`!A B:int128.
    word_subword (word_xor (word_join (word_subword (A:int128) (64,64):64 word) (word_subword (B:int128) (64,64):64 word):128 word)
                           (word_join (word_subword A (0,64):64 word) (word_subword B (0,64):64 word):128 word)) (64,64):64 word
    = word_xor (word_subword A (64,64):64 word) (word_subword A (0,64):64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let PM_LANE_LO = prove
 (`!A B:int128.
    word_subword (word_xor (word_join (word_subword (A:int128) (64,64):64 word) (word_subword (B:int128) (64,64):64 word):128 word)
                           (word_join (word_subword A (0,64):64 word) (word_subword B (0,64):64 word):128 word)) (0,64):64 word
    = word_xor (word_subword B (64,64):64 word) (word_subword B (0,64):64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* session-063: swapped-RHS variants of PM_LANE_HI/LO — same pmull2/pmull PAIR *)
(* form, but the extracted mid-input is spelled in the (0,64)^(64,64) lane      *)
(* order that karatsuba_block_pm produces (word_pmul's first arg is atomic to   *)
(* WORD_RULE, so the lane XOR must match SYNTACTICALLY, not just up to comm).   *)
let PM_LANE_HI' = prove
 (`!A B:int128.
    word_subword (word_xor (word_join (word_subword (A:int128) (64,64):64 word) (word_subword (B:int128) (64,64):64 word):128 word)
                           (word_join (word_subword A (0,64):64 word) (word_subword B (0,64):64 word):128 word)) (64,64):64 word
    = word_xor (word_subword A (0,64):64 word) (word_subword A (64,64):64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let PM_LANE_LO' = prove
 (`!A B:int128.
    word_subword (word_xor (word_join (word_subword (A:int128) (64,64):64 word) (word_subword (B:int128) (64,64):64 word):128 word)
                           (word_join (word_subword A (0,64):64 word) (word_subword B (0,64):64 word):128 word)) (0,64):64 word
    = word_xor (word_subword B (0,64):64 word) (word_subword B (64,64):64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* session-063 (block-0/block-1 SOFAR-pair PM mid-inputs): the FIRST pmull2/    *)
(* pmull PAIR folds in the running accumulator SOFAR, so block 0's operand      *)
(* enters as a rot64'd word_join of SOFAR with the first ciphertext block       *)
(* (not the plain packed pair the later blocks use).  These two lane lemmas     *)
(* recover the block-0 (outer (64,64), over word_xor SOFAR cph0) and block-1    *)
(* (outer (0,64), over cph1) mid-inputs, in karatsuba_block_pm's (0,64)^(64,64) *)
(* lane order.  Pure WORD_BLAST over free ss (=SOFAR), xx0 (=rev cph0), xx1     *)
(* (=rev cph1).  Together with PM_LANE'_HI/LO (the plain pairs {2,3}{4,5}{6,7}) *)
(* they reduce all 8 machine PM mid-inputs to kara form so PROJ_EQ PM closes.   *)
let LANE_COLLAPSE_PM_A = prove
 (`!ss xx0 xx1:int128.
    word_subword
     (word_xor
      (word_join
       (word_subword (word_xor (word_subword (word_join (ss:int128) ss:256 word) (64,128):128 word)
                               (word_subword (word_join (xx0:int128) xx0:256 word) (64,128):128 word)) (0,64):64 word)
       (word_subword xx1 (64,64):64 word):128 word)
      (word_join
       (word_subword (word_xor (word_subword (word_join (ss:int128) ss:256 word) (64,128):128 word)
                               (word_subword (word_join (xx0:int128) xx0:256 word) (64,128):128 word)) (64,64):64 word)
       (word_subword xx1 (0,64):64 word):128 word)) (64,64):64 word
    = word_xor (word_subword (word_xor ss xx0) (0,64):64 word)
               (word_subword (word_xor ss xx0) (64,64):64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let LANE_COLLAPSE_PM_B = prove
 (`!ss xx0 xx1:int128.
    word_subword
     (word_xor
      (word_join
       (word_subword (word_xor (word_subword (word_join (ss:int128) ss:256 word) (64,128):128 word)
                               (word_subword (word_join (xx0:int128) xx0:256 word) (64,128):128 word)) (0,64):64 word)
       (word_subword xx1 (64,64):64 word):128 word)
      (word_join
       (word_subword (word_xor (word_subword (word_join (ss:int128) ss:256 word) (64,128):128 word)
                               (word_subword (word_join (xx0:int128) xx0:256 word) (64,128):128 word)) (64,64):64 word)
       (word_subword xx1 (0,64):64 word):128 word)) (0,64):64 word
    = word_xor (word_subword xx1 (0,64):64 word) (word_subword xx1 (64,64):64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* --------------------------------------------------------------------------- *)
(* session-064 (Q19 R1' WIRE-IN): compose the value-equality + close the CHEAT. *)
(*                                                                             *)
(* build_q19_reduce_clean pl_t ph_t pm_t : given the three s289 accumulator     *)
(* terms (= read Q17/Q19/Q18 s289, over h/xi/ibytes/i), produces the CLEAN      *)
(* theorem  |- <machine reduce byteform> = ghash_polyval_acc (byteswap128 h)    *)
(*   (word_bytereverse xi) (MAP word_bytereverse (list_of_seq blk (8*(i+1))))   *)
(* hyps=0 — the invariant's Q19-at-(i+1) fold.  It chains:                      *)
(*   reduce_id  : byteform = polyval_reduce_prop3 (pack_corrected PL PH PM)     *)
(*                                        [WBN_MACHINE_REDUCE_IS_PROP3_PACK]     *)
(*   KARA_PACK_EQ (kqok): pack_corrected PL PH PM = SPEC_TOWERS                  *)
(*   body_ready2 : ghash..(8(i+1)) = polyval_reduce_prop3 SPEC_TOWERS           *)
(*                                        [BODY_Q19_CLOSE_ALGEBRA + involution]  *)
(* The 8 kqok side-conditions (subword hk_j (0,64) = karatsuba_mid ..) are      *)
(* discharged by choosing hk_j := word_join (word 0)(karatsuba_mid ..) so kqok  *)
(* holds unconditionally (SUBWORD_JOIN0 + KMID_BYTESWAP_INV) — a hyps-free      *)
(* lemma.  PROJ_PM is kept CONDITIONAL on kqok (hk free) then INST'd+MP'd — the *)
(* bake-hk-upfront variant fails PROJ_PM (subword(join 0 kmid) not plain kmid). *)
let SUBWORD_JOIN0 = prove
 (`!X:64 word. word_subword (word_join (word 0:64 word) X :128 word) (0,64):64 word = X`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let build_q19_reduce_clean pl_t ph_t pm_t =
  let bsh = `byteswap128 h` in
  let rec tower n = if n <= 1 then bsh else mk_comb(mk_comb(`polyval_dot`, tower(n-1)), bsh) in
  let inst_list = map (fun n -> (mk_comb(`byteswap128`, tower n), mk_var("h"^string_of_int n, `:int128`))) (2--8) in
  let body_inst2 = INST inst_list BODY_Q19_CLOSE_ALGEBRA in
  let body_ready2 = REWRITE_RULE[BYTESWAP128_INVOLUTION]
       (MP body_inst2 (prove(fst(dest_imp(concl body_inst2)), REWRITE_TAC[BYTESWAP128_INVOLUTION]))) in
  let spec_towers = rand(rhs(concl body_ready2)) in
  let rec strip_xor t = match t with Comb(Comb(Const("word_xor",_),a),b) -> strip_xor a @ strip_xor b | _ -> [t] in
  let spec_leaves = strip_xor spec_towers in
  let spec_input j = rand(rator (List.nth spec_leaves j)) in
  let mk_quadT j = let inp = spec_input j in let tw = tower(8-j) in
    mk_pair(inp, mk_pair(mk_comb(`byteswap128`, tw), mk_pair(mk_var("hk"^string_of_int j, `:int128`), tw))) in
  let quadsT = mk_list(map mk_quadT (0--7), `:int128#int128#int128#int128`) in
  let kqok_hyp j = mk_eq(mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, mk_var("hk"^string_of_int j,`:int128`)), `(0,64)`),
                  mk_comb(`karatsuba_mid`, mk_comb(`byteswap128`, tower (8-j)))) in
  let kqok_hyps = map kqok_hyp (0--7) in
  let projtac = REWRITE_TAC[project_triples; kara_acc; karatsuba_block_pl; karatsuba_block_ph; karatsuba_block_pm] THEN
      CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; SND] in
  let mk_proj sel concrete = mk_eq(mk_comb(sel, subst [quadsT, `QUADS:(int128#int128#int128#int128)list`]
              `kara_acc (project_triples QUADS) (word 0:int128) (word 0:int128) (word 0:int128)`), concrete) in
  let PROJ_PL = BETA_RULE(prove(mk_proj `FST:int128#int128#int128->int128` pl_t,
     projtac THEN REWRITE_TAC[WRF8_IS_BYTEREVERSE; LANE_COLLAPSE; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let PROJ_PH = BETA_RULE(prove(mk_proj `\t:int128#int128#int128. FST(SND t)` ph_t,
     projtac THEN REWRITE_TAC[WRF8_IS_BYTEREVERSE; LANE_COLLAPSE; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let PROJ_PM = BETA_RULE(prove(mk_imp(list_mk_conj kqok_hyps, mk_proj `\t:int128#int128#int128. SND(SND t)` pm_t),
     STRIP_TAC THEN projtac THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[WRF8_IS_BYTEREVERSE; LANE_COLLAPSE_PM_A; LANE_COLLAPSE_PM_B; PM_LANE_HI'; PM_LANE_LO'; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let kp = rand(lhs(concl PROJ_PL)) in
  let KARA_QUAD_OK_T = prove(mk_imp(list_mk_conj kqok_hyps, mk_comb(`kara_quad_ok`, quadsT)),
    STRIP_TAC THEN REWRITE_TAC[kara_quad_ok] THEN REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC KMID_BYTESWAP_INV) in
  let TESTQT = prove(mk_eq(subst [quadsT, `QUADS:(int128#int128#int128#int128)list`] `kara_quad_pmul QUADS (word 0:256 word)`, spec_towers),
    REWRITE_TAC[kara_quad_pmul; WORD_XOR_0_LEFT] THEN CONV_TAC WORD_RULE) in
  let helper = MP (SPECL [quadsT; `word 0:256 word`] KARA_ACC_PACK_HELPER)
                  (MP KARA_QUAD_OK_T (end_itlist CONJ (map ASSUME kqok_hyps))) in
  let KARA_PACK_EQ = prove(mk_imp(list_mk_conj kqok_hyps,
        mk_eq(list_mk_comb(`pack_corrected`, [pl_t; ph_t; pm_t]), spec_towers)),
    STRIP_TAC THEN
    (let pm_thm = MP PROJ_PM (end_itlist CONJ (map ASSUME kqok_hyps)) in
     let sndkp = mk_comb(`SND:int128#int128#int128->int128#int128`, kp) in
     let sndkp_eq = TRANS (GSYM(ISPEC sndkp PAIR)) (MK_COMB(AP_TERM `(,):int128->int128->int128#int128` PROJ_PH, pm_thm)) in
     let kp_triple = TRANS (GSYM(ISPEC kp PAIR)) (MK_COMB(AP_TERM `(,):int128->int128#int128->int128#int128#int128` PROJ_PL, sndkp_eq)) in
     REWRITE_TAC[GSYM TESTQT] THEN MP_TAC helper THEN
     REWRITE_TAC[LET_DEF; LET_END_DEF] THEN SUBST1_TAC kp_triple THEN
     CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[WORD_XOR_0_LEFT] THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC)) in
  let reduce_id = SPECL [pl_t;ph_t;pm_t] WBN_MACHINE_REDUCE_IS_PROP3_PACK in
  let q19_final = TRANS (TRANS reduce_id (AP_TERM `polyval_reduce_prop3` (UNDISCH_ALL KARA_PACK_EQ))) (SYM body_ready2) in
  let q19_disch = itlist DISCH (hyp q19_final) q19_final in
  let hk_inst = map (fun j ->
     let kmid = mk_comb(`karatsuba_mid`, mk_comb(`byteswap128`, tower (8-j))) in
     (mk_comb(mk_comb(`word_join:64 word->64 word->128 word`, `word 0:64 word`), kmid),
      mk_var("hk"^string_of_int j, `:int128`))) (0--7) in
  let inst_thm = INST hk_inst q19_disch in
  MP inst_thm (prove(fst(dest_imp(concl inst_thm)),
     REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST));;

(* Wire-in tactics.  The extract stashes pl/ph/pm@s289 into refs (before the      *)
(* ABBREV that makes the reduce window small); the close (run at the Q19 postcond  *)
(* conjunct) rebuilds the CLEAN thm from those refs and ACCEPTs it after mapping   *)
(* its concrete byteform LHS back to the goal's PL/PH/PM-abbreviated form + the    *)
(* 8*(i+1)=8*i+8 index normalization the postcond prep applied. *)
let wbn_q19_pl = ref `T` and wbn_q19_ph = ref `T` and wbn_q19_pm = ref `T`;;
let WBN_Q19_EXTRACT_ABBREV_TAC (sN:string) : tactic =
  fun (asl,w) ->
    let st = mk_var(sN,`:armstate`) in
    let get_rhs q =
      let c = find (fun c -> match c with
        | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),qc),s)),_) when qc=q && s=st -> true
        | _ -> false) (map (concl o snd) asl) in
      rand c in
    wbn_q19_pl := get_rhs `Q17`;
    wbn_q19_ph := get_rhs `Q19`;
    wbn_q19_pm := get_rhs `Q18`;
    (ABBREV_TAC (mk_eq(`PL:int128`, !wbn_q19_pl)) THEN
     ABBREV_TAC (mk_eq(`PH:int128`, !wbn_q19_ph)) THEN
     ABBREV_TAC (mk_eq(`PM:int128`, !wbn_q19_pm))) (asl,w);;
let WBN_Q19_CLOSE_TAC : tactic =
  fun (asl,w) ->
    let clean = build_q19_reduce_clean (!wbn_q19_pl) (!wbn_q19_ph) (!wbn_q19_pm) in
    let defthms = filter (fun th -> match concl th with
      | Comb(Comb(Const("=",_),_),Var(("PL"|"PH"|"PM"),_)) -> true | _ -> false) (map snd asl) in
    let clean' = REWRITE_RULE (ARITH_RULE `8 * (i + 1) = 8 * i + 8` :: defthms) clean in
    ACCEPT_TAC clean' (asl,w);;

(* ------------------------------------------------------------------------- *)
(* session-065: the k-indexed variant of build_q19_reduce_clean, for the      *)
(* PREPRETAIL Q19 close (index k = (nblk-9)DIV8, not the loop-body i).  The    *)
(* only delta is INST'ing BODY_Q19_CLOSE_ALGEBRA with i := idx first, so its   *)
(* spec fold reads ghash..(8*(idx+1)); everything else (the reduce identity    *)
(* + block algebra) is index-free.  The body could call this with `i:num`.     *)
let build_q19_reduce_clean_idx idx pl_t ph_t pm_t =
  let bsh = `byteswap128 h` in
  let rec tower n = if n <= 1 then bsh else mk_comb(mk_comb(`polyval_dot`, tower(n-1)), bsh) in
  let inst_list = map (fun n -> (mk_comb(`byteswap128`, tower n), mk_var("h"^string_of_int n, `:int128`))) (2--8) in
  let body_base = INST [idx, `i:num`] BODY_Q19_CLOSE_ALGEBRA in
  let body_inst2 = INST inst_list body_base in
  let body_ready2 = REWRITE_RULE[BYTESWAP128_INVOLUTION]
       (MP body_inst2 (prove(fst(dest_imp(concl body_inst2)), REWRITE_TAC[BYTESWAP128_INVOLUTION]))) in
  let spec_towers = rand(rhs(concl body_ready2)) in
  let rec strip_xor t = match t with Comb(Comb(Const("word_xor",_),a),b) -> strip_xor a @ strip_xor b | _ -> [t] in
  let spec_leaves = strip_xor spec_towers in
  let spec_input j = rand(rator (List.nth spec_leaves j)) in
  let mk_quadT j = let inp = spec_input j in let tw = tower(8-j) in
    mk_pair(inp, mk_pair(mk_comb(`byteswap128`, tw), mk_pair(mk_var("hk"^string_of_int j, `:int128`), tw))) in
  let quadsT = mk_list(map mk_quadT (0--7), `:int128#int128#int128#int128`) in
  let kqok_hyp j = mk_eq(mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, mk_var("hk"^string_of_int j,`:int128`)), `(0,64)`),
                  mk_comb(`karatsuba_mid`, mk_comb(`byteswap128`, tower (8-j)))) in
  let kqok_hyps = map kqok_hyp (0--7) in
  let projtac = REWRITE_TAC[project_triples; kara_acc; karatsuba_block_pl; karatsuba_block_ph; karatsuba_block_pm] THEN
      CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; SND] in
  let mk_proj sel concrete = mk_eq(mk_comb(sel, subst [quadsT, `QUADS:(int128#int128#int128#int128)list`]
              `kara_acc (project_triples QUADS) (word 0:int128) (word 0:int128) (word 0:int128)`), concrete) in
  let PROJ_PL = BETA_RULE(prove(mk_proj `FST:int128#int128#int128->int128` pl_t,
     projtac THEN REWRITE_TAC[WRF8_IS_BYTEREVERSE; LANE_COLLAPSE; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let PROJ_PH = BETA_RULE(prove(mk_proj `\t:int128#int128#int128. FST(SND t)` ph_t,
     projtac THEN REWRITE_TAC[WRF8_IS_BYTEREVERSE; LANE_COLLAPSE; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let PROJ_PM = BETA_RULE(prove(mk_imp(list_mk_conj kqok_hyps, mk_proj `\t:int128#int128#int128. SND(SND t)` pm_t),
     STRIP_TAC THEN projtac THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[WRF8_IS_BYTEREVERSE; LANE_COLLAPSE_PM_A; LANE_COLLAPSE_PM_B; PM_LANE_HI'; PM_LANE_LO'; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let kp = rand(lhs(concl PROJ_PL)) in
  let KARA_QUAD_OK_T = prove(mk_imp(list_mk_conj kqok_hyps, mk_comb(`kara_quad_ok`, quadsT)),
    STRIP_TAC THEN REWRITE_TAC[kara_quad_ok] THEN REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC KMID_BYTESWAP_INV) in
  let TESTQT = prove(mk_eq(subst [quadsT, `QUADS:(int128#int128#int128#int128)list`] `kara_quad_pmul QUADS (word 0:256 word)`, spec_towers),
    REWRITE_TAC[kara_quad_pmul; WORD_XOR_0_LEFT] THEN CONV_TAC WORD_RULE) in
  let helper = MP (SPECL [quadsT; `word 0:256 word`] KARA_ACC_PACK_HELPER)
                  (MP KARA_QUAD_OK_T (end_itlist CONJ (map ASSUME kqok_hyps))) in
  let KARA_PACK_EQ = prove(mk_imp(list_mk_conj kqok_hyps,
        mk_eq(list_mk_comb(`pack_corrected`, [pl_t; ph_t; pm_t]), spec_towers)),
    STRIP_TAC THEN
    (let pm_thm = MP PROJ_PM (end_itlist CONJ (map ASSUME kqok_hyps)) in
     let sndkp = mk_comb(`SND:int128#int128#int128->int128#int128`, kp) in
     let sndkp_eq = TRANS (GSYM(ISPEC sndkp PAIR)) (MK_COMB(AP_TERM `(,):int128->int128->int128#int128` PROJ_PH, pm_thm)) in
     let kp_triple = TRANS (GSYM(ISPEC kp PAIR)) (MK_COMB(AP_TERM `(,):int128->int128#int128->int128#int128#int128` PROJ_PL, sndkp_eq)) in
     REWRITE_TAC[GSYM TESTQT] THEN MP_TAC helper THEN
     REWRITE_TAC[LET_DEF; LET_END_DEF] THEN SUBST1_TAC kp_triple THEN
     CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[WORD_XOR_0_LEFT] THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC)) in
  let reduce_id = SPECL [pl_t;ph_t;pm_t] WBN_MACHINE_REDUCE_IS_PROP3_PACK in
  let q19_final = TRANS (TRANS reduce_id (AP_TERM `polyval_reduce_prop3` (UNDISCH_ALL KARA_PACK_EQ))) (SYM body_ready2) in
  let q19_disch = itlist DISCH (hyp q19_final) q19_final in
  let hk_inst = map (fun j ->
     let kmid = mk_comb(`karatsuba_mid`, mk_comb(`byteswap128`, tower (8-j))) in
     (mk_comb(mk_comb(`word_join:64 word->64 word->128 word`, `word 0:64 word`), kmid),
      mk_var("hk"^string_of_int j, `:int128`))) (0--7) in
  let inst_thm = INST hk_inst q19_disch in
  MP inst_thm (prove(fst(dest_imp(concl inst_thm)),
     REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST));;

(* WBN_Q19_PREPRETAIL_CLOSE_TAC idx : closes BOTH prepretail GHASH conjuncts     *)
(* (run per-conjunct after ENSURES_FINAL + REPEAT CONJ_TAC, guarded on           *)
(* ghash_polyval_acc).  idx = the prepretail index (`k:num`).  The Q19 conjunct  *)
(* (read Q19 = ghash..(8*(k+1))) and the Q16 staging conjunct                    *)
(* (read Q16 = word_subword(word_join <caught_up> <caught_up>)(64,128)) both     *)
(* reduce, after ASM_REWRITE substitutes the machine byteform + the CLEAN        *)
(* value-equality folds it to ghash..(8*k+8), to the pure index identity         *)
(* 8*k+8 = 8*(k+1), closed by ARITH + REFL.  session-065.                        *)
let WBN_Q19_PREPRETAIL_CLOSE_TAC (idx:term) : tactic =
  fun (asl,w) ->
    let clean = build_q19_reduce_clean_idx idx (!wbn_q19_pl) (!wbn_q19_ph) (!wbn_q19_pm) in
    let defthms = filter (fun th -> match concl th with
      | Comb(Comb(Const("=",_),_),Var(("PL"|"PH"|"PM"),_)) -> true | _ -> false) (map snd asl) in
    let clean' = REWRITE_RULE (ARITH_RULE `8 * (i + 1) = 8 * i + 8` :: defthms) clean in
    (ASM_REWRITE_TAC[] THEN REWRITE_TAC[clean'] THEN
     REWRITE_TAC[ARITH_RULE `8 * k + 8 = 8 * (k + 1)`] THEN
     TRY REFL_TAC) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* 6. Route-(b) tool: strengthen an ensures postcondition with a frame-       *)
(*    PRESERVED fact, with NO re-simulation.  Pure ensures/eventually logic.  *)
(*                                                                            *)
(* This is the clean combinator for WBN_FRONT_BUF_EXT (and reusable in the    *)
(* Phase-6 recompose): given `ensures step P Q C` and that the frame C, from  *)
(* precondition P, preserves R (i.e. !s s'. P s /\ C s s' ==> R s'), we get   *)
(* `ensures step P (\s. Q s /\ R s) C` for free.                              *)
(*                                                                            *)
(* Usage for WBN_FRONT_BUF_EXT: take R s = (the 3 loop-constants at s:         *)
(*   read (memory :> bytes (in_p,16*nblk)) s = num_of_bytelist ibytes /\      *)
(*   read (memory :> bytes128 key_p) s = k0 /\ htable_mem_dec h htbl_p s).     *)
(* The preservation obligation !s s'. wb_front_pre_tm s /\ wb_front_frame_tm  *)
(* s s' ==> R s' holds because none of in_p's input bytes, key_p, or htbl_p   *)
(* memory is in wb_front_frame_tm's MAYCHANGE (only out_p/xi_p/ivec_p/stack + *)
(* Q-regs are).  Discharge it by: STRIP the frame (MAYCHANGE ... ,, ...),     *)
(* then for each read-conjunct use the nonoverlapping hyps + the fact the     *)
(* frame's memory writes miss those regions (the standard READ_OVER_WRITE /   *)
(* MAYCHANGE-preservation reasoning; htable_mem_dec unfolds to bytes128 reads *)
(* off htbl_p that are likewise disjoint).                                    *)
(* ------------------------------------------------------------------------- *)

let ENSURES_ADD_PRESERVED = prove
 (`!(step:A->A->bool) P Q R C.
    ensures step P Q C /\ (!s s'. P s /\ C s s' ==> R s')
    ==> ensures step P (\s. Q s /\ R s) C`,
  REWRITE_TAC[ensures] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `s0:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!s':A. Q s' /\ C (s0:A) s' ==> (Q s' /\ R s') /\ C s0 s'`
    (MP_TAC o MATCH_MP EVENTUALLY_MONO) THENL
   [X_GEN_TAC `s1:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`s0:A`;`s1:A`] th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    DISCH_THEN(MP_TAC o SPECL [`step:A->A->bool`; `s0:A`]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 7. Phase 2 hyp-gap fix: WBN_FRONT_BUF_EXT (session-005).                   *)
(*                                                                            *)
(* The i=0 invariant instance needs 3 loop-CONSTANTS at the loop head that    *)
(* WBN_FRONT_BUF's harvested postcond drops (session-003/004 GAP note above): *)
(*   read (memory :> bytes (in_p,16*nblk)) s = num_of_bytelist ibytes         *)
(*   read (memory :> bytes128 key_p) s = k0                                   *)
(*   htable_mem_dec h htbl_p s                                                *)
(* These are preserved by the front MAYCHANGE frame (which writes only        *)
(* out_p/xi_p/ivec_p/stack + Q-regs), PROVIDED out_p is disjoint from in_p/   *)
(* key_p/htbl_p.  wbn_front_hyps_tm was missing exactly those 3 out_p         *)
(* disjointness conjuncts (they ARE in wb.ml's <=8 band hyps, wb.ml:3854-57). *)
(*                                                                            *)
(* ROUTE (b) (session-004's ENSURES_ADD_PRESERVED), NOT route (a): we DON'T   *)
(* re-run the front sim with widened hyps (the build_state_postcond_tms2      *)
(* re-harvest the reviewer flagged as risky).  Instead keep the proven        *)
(* WBN_FRONT_BUF verbatim and STRENGTHEN its postcond with the 3 constants    *)
(* via ENSURES_ADD_PRESERVED: leg1 = WBN_FRONT_BUF (narrow hyps <= wide hyps, *)
(* closed by MATCH_MP_TAC + ASM_REWRITE), leg2 = the pure frame-preservation  *)
(* obligation (no sim).  Whole thing proves in ~4s.                           *)
(* ------------------------------------------------------------------------- *)

(* widened front hyps = wbn_front_hyps_tm + the 3 out_p disjointness conjuncts *)
let wbn_front_hyps_wide_tm =
  mk_conj(wbn_front_hyps_tm,
    `nonoverlapping (out_p:int64,16 * nblk) (in_p:int64,16 * nblk) /\
     nonoverlapping (out_p:int64,16 * nblk) (key_p:int64,240) /\
     nonoverlapping (out_p:int64,16 * nblk) (htbl_p:int64,192)`);;

(* the WBN_FRONT_BUF pieces (P = precond, Q0 = harvested postcond, C = frame) *)
let wbn_front_P_tm, wbn_front_Q0_tm, wbn_front_C_tm =
  let ens = snd(dest_imp(snd(strip_forall(concl WBN_FRONT_BUF)))) in
  rand(rator(rator ens)), rand(rator ens), rand ens;;

(* R = the 3 loop-constants, taken verbatim from WBN_FRONT_BUF's precond so
   they match wbn_loop_invariant's conjuncts syntactically. *)
let wbn_front_R_tm =
  let sv = fst(dest_abs wbn_front_P_tm) in
  mk_abs(sv, list_mk_conj
    [`read (memory :> bytes (in_p:int64,16 * nblk)) s = num_of_bytelist ibytes`;
     `read (memory :> bytes128 (key_p:int64)) s = (k0:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 16))) s = (k1:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 32))) s = (k2:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 48))) s = (k3:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 64))) s = (k4:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 80))) s = (k5:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 96))) s = (k6:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 112))) s = (k7:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 128))) s = (k8:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 144))) s = (k9:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 160))) s = (k10:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 176))) s = (k11:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 192))) s = (k12:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 208))) s = (k13:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 224))) s = (k14:int128)`;
     `htable_mem_dec h (htbl_p:int64) s`]);;

(* EXT goal: wide hyps ==> ensures arm P (\s. Q0 s /\ R s) C *)
let wbn_front_ext_goal =
  let newQ = mk_abs(fst(dest_abs wbn_front_P_tm),
    mk_conj(rhs(concl(BETA_CONV(mk_comb(wbn_front_Q0_tm,fst(dest_abs wbn_front_P_tm))))),
            rhs(concl(BETA_CONV(mk_comb(wbn_front_R_tm,fst(dest_abs wbn_front_P_tm))))))) in
  let ens = list_mk_comb(`ensures arm`,[wbn_front_P_tm; newQ; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

(* leg2 helper: push a read through the whole MAYCHANGE write-chain to `read c s`
   using the goal's nonoverlapping assumptions (memory-vs-memory orthogonality),
   then close via the precond assumption `read c s = value`.  Uses the
   assumption-aware COMPONENTS_READ_OVER_WRITE_ORTHOGONAL_CONV (common/components).
   Applied once per R-conjunct (register writes fold away, memory writes need the
   nonoverlapping facts). *)
let WBN_PUSH_LHS_READ_TAC : tactic =
  W(fun (asl,w) ->
    let thl = map snd asl in
    let cxt = (NONOVERLAPPING_DRIVERS thl, FILTER_CANONIZE_ASSUMPTIONS thl) in
    CONV_TAC(LAND_CONV(COMPONENTS_READ_OVER_WRITE_ORTHOGONAL_CONV cxt))) THEN
  ASM_REWRITE_TAC[];;

let WBN_FRONT_BUF_EXT = prove(wbn_front_ext_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_ADD_PRESERVED THEN CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_BUF THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[htable_mem_dec] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC(REDEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    CONV_TAC(REDEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_eq(concl th) &&
        (match rhs(concl th) with Var("s'",_) -> true | _ -> false))) THEN
    WBN_PUSH_LHS_READ_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 8. Phase 2 CLOSE: WBN_LOOP_INVARIANT_ENTRY (session-005).                  *)
(*                                                                            *)
(* THE entry subgoal that ENSURES_WHILE_UP_TAC produces for the main loop:    *)
(*   ensures arm (\s. decodes /\ PC = pc+0x20 /\ precondition s)              *)
(*               (\s. decodes /\ PC = pc+0x4a0 /\ wbn_loop_invariant ... 0 s) *)
(*               frame                                                        *)
(* i.e. the front (entry -> loop head) establishes the i=0 invariant.  Proved *)
(* by weakening WBN_FRONT_BUF_EXT's postcond (Q0 /\ 3-loop-constants) down to *)
(* the i=0 invariant, via ENSURES_POSTCONDITION_THM.  The implication         *)
(* (Q0 s /\ R s) ==> inv 0 s is the session-003 Sec-4 closing recipe, PLUS a  *)
(* final numeral-normalization pass (session-005): after the recipe the goal  *)
(* is a conjunction of trivial `f (word n) = f (word (0+n))` /                 *)
(* `SUB_LIST(16*(0+k)..) = SUB_LIST(16*k..)` equalities + the j<8 store        *)
(* forall; ADD_CLAUSES + NUM_MULT_CONV + GCM_CTR_ADD_0 (block-0 = ctr0) close  *)
(* them against the postcond hyps.                                            *)
(* ------------------------------------------------------------------------- *)

(* i=0 invariant applied to all 27 loop params, as a (num->armstate->bool). *)
let wbn_inv_applied =
  list_mk_comb(`wbn_loop_invariant`,
    [`pc:num`;`ctr0:int128`;`in_p:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
     `key_p:int64`;`htbl_p:int64`;`stackpointer:int64`;`nblk:num`;`ibytes:byte list`;
     `xi:int128`;`h:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;
     `k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;
     `k12:int128`;`k13:int128`;`k14:int128`]);;

(* post = \s. decodes /\ PC = pc+0x4a0 /\ inv 0 s *)
let wbn_entry_post =
  subst [wbn_inv_applied,`INVAPP:num->armstate->bool`]
    `\s:armstate. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
                  read PC s = word (pc + 0x4a0) /\
                  INVAPP (0:num) s`;;

let wbn_entry_goal =
  let ens = list_mk_comb(`ensures arm`,[wbn_front_P_tm; wbn_entry_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

(* the Q to weaken from: WBN_FRONT_BUF_EXT's postcond = \s. Q0 s /\ R s *)
let wbn_extQ =
  let sv = fst(dest_abs wbn_front_P_tm) in
  mk_abs(sv, mk_conj(
    rhs(concl(BETA_CONV(mk_comb(wbn_front_Q0_tm,sv)))),
    rhs(concl(BETA_CONV(mk_comb(wbn_front_R_tm,sv)))))) ;;

let WBN_LOOP_INVARIANT_ENTRY = prove(wbn_entry_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC wbn_extQ THEN CONJ_TAC THENL
   [(* (Q0 x /\ R x) ==> decodes /\ PC=pc+0x4a0 /\ inv 0 x *)
    GEN_TAC THEN REWRITE_TAC[wbn_loop_invariant] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
    REWRITE_TAC[GCM_CTR_INC_ITER_ADD; GCM_CTR_ADD_1; GSYM GCM_CTR_ADD_LANES] THEN
    REWRITE_TAC[list_of_seq; MAP; ghash_polyval_acc] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES;
       GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES; GCM_CTR_INC5_LANES;
       GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
    REWRITE_TAC[GCM_CTR_ADD_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
    (* session-005 numeral-normalization tail: 0+n, 16*(0+k), block-0=ctr0 *)
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM GCM_CTR_ADD_LANES; GCM_CTR_ADD_0] THEN
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[GCM_CTR_ADD_0] THEN
    (* session-008 Q30 residual: the only conjunct the session-005 closer leaves
       open after the Q30 patch.  The i=0 raw tower (top lane += 12 then += 1)
       collapses to gcm_ctr_raw (word 13) ctr0 = the invariant's 8*0+13 value.
       VALIDATED (session-008, shadow wbn_loop_invariant_v2). *)
    REWRITE_TAC[gcm_ctr_raw_def;
      WORD_RULE `word_add (word_add (x:32 word) (word 12)) (word 1) =
                 word_add x (word 13)`;
      WORD_ADD_0];
    (* the ensures = WBN_FRONT_BUF_EXT *)
    MATCH_MP_TAC WBN_FRONT_BUF_EXT THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 9. Phase 4 launch: PC/decode-free CORE invariant + split (session-006).    *)
(*                                                                            *)
(* wbn_loop_invariant bakes in two conjuncts the ENSURES_WHILE tactics MUST   *)
(* own themselves:                                                            *)
(*   C1  aligned_bytes_loaded s (word pc) ...mc   (program_decodes)           *)
(*   C2  read PC s = word (pc + 1184)             (the loop-head PC)          *)
(* Every ENSURES_WHILE_* template threads `program_decodes` and `read PC =    *)
(* word pcX` around its OWN `loopinv i s`, applying loopinv at BOTH pc1 (head)*)
(* and pc2 (back-edge/exit).  A PC baked into the invariant is therefore      *)
(* redundant at pc1 and *contradictory* at pc2 (it would force PC=0x4a0 in a  *)
(* state whose PC is 0x9ec/0x9f0).  Standard s2n invariants (keccak,          *)
(* emontredc) are PC/decode-free for exactly this reason.                     *)
(*                                                                            *)
(* wbn_loop_inv_core = wbn_loop_invariant with C1,C2 removed (built by        *)
(* dropping the first two conjuncts, so it stays in sync with the frozen      *)
(* definition automatically).  WBN_INV_SPLIT is the bridge                    *)
(*   wbn_loop_invariant ... i s <=>                                           *)
(*     aligned_bytes_loaded s (word pc) mc /\ read PC s = word (pc+1184) /\   *)
(*     wbn_loop_inv_core ... i s                                              *)
(* so the ENTRY theorem (which yields the LHS at i=0) feeds any tactic that   *)
(* wants the RHS, and the loop body/exit can carry ONLY the core across the   *)
(* frame while the tactic supplies decode+PC.                                 *)
(* ------------------------------------------------------------------------- *)

let wbn_loop_inv_core =
  let eqn = snd(strip_forall(concl wbn_loop_invariant)) in
  let lhs_full, rhs_full = dest_eq eqn in
  let hd, params = strip_comb lhs_full in
  let ivars, body = strip_abs rhs_full in
  let cs = conjuncts body in
  (* C1 = aligned_bytes_loaded, C2 = read PC = word(pc+1184); drop both *)
  let core_body = list_mk_conj (List.tl (List.tl cs)) in
  let core_rhs = list_mk_abs(ivars, core_body) in
  let newhead = mk_var("wbn_loop_inv_core", type_of hd) in
  new_definition (mk_eq(list_mk_comb(newhead, params), core_rhs));;

let wbn_inv_args =
  snd(strip_comb(fst(dest_eq(snd(strip_forall(concl wbn_loop_invariant))))));;

let WBN_INV_SPLIT = prove
 (list_mk_forall(wbn_inv_args @ [`i:num`;`s:armstate`],
    mk_eq(
      list_mk_comb(`wbn_loop_invariant`, wbn_inv_args @ [`i:num`;`s:armstate`]),
      list_mk_conj[
        `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
        `read PC s = word (pc + 1184)`;
        list_mk_comb(`wbn_loop_inv_core`, wbn_inv_args @ [`i:num`;`s:armstate`])])),
  REWRITE_TAC[wbn_loop_invariant; wbn_loop_inv_core] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[CONJ_ACI]);;

(* ------------------------------------------------------------------------- *)
(* 9b. Phase 4 PREREQ: the RAW counter accumulator Q30 (session-007).          *)
(*                                                                            *)
(* CRITICAL FINDING (session-007): the frozen wbn_loop_invariant (Sec 4) is    *)
(* INCOMPLETE for the loop body.  The body's FIRST instruction                 *)
(*   0x4a0  rev32 v5, v30                                                       *)
(* reads Q30 -- the running CTR-block counter in its rev32-pending "raw" form  *)
(* -- but wbn_loop_invariant has NO Q30 conjunct, so Q5 immediately goes       *)
(* symbolic in `read Q30 s0` and the body cannot close.  Static live-in        *)
(* analysis of the whole body (0x4a0..0x9ec) shows Q30 is the ONLY vector      *)
(* register whose first use is a READ and which the invariant fails to pin     *)
(* (Q0..Q4, Q19, Q31 are live-in AND already pinned).                          *)
(*                                                                            *)
(* WBN_FRONT_BUF DID harvest a Q30 conjunct (its postcond conjunct 46), as a   *)
(* raw bit-tower; Sec 4's generalization to symbolic i simply dropped it.      *)
(* The value at the loop head (iteration i) is gcm_ctr_raw (word (8*i+13)) ctr0*)
(* -- CONFIRMED: WBN_FRONT_BUF's conjunct-46 term = gcm_ctr_raw (word 13) ctr0 *)
(* at i=0 (proved via gcm_ctr_raw_def + WORD_RULE add-merge + WORD_ADD_0).      *)
(*                                                                            *)
(* gcm_ctr_raw w ctr0 is the counter in the "byte-grouped, top-lane += w"      *)
(* representation the hardware keeps in v30: its top 32-bit lane is            *)
(* word_add (<brev of ctr0[96:128] bytes>) w, the low 96 bits are ctr0's low   *)
(* lanes byte-grouped.  The body does rev32(v30) -> AES keystream input for    *)
(* block 8i+13, then add v30,v30,v31 (v31 = word 2^96) to advance to 8i+14.    *)
(*                                                                            *)
(* THE FIX (next session): add a Q30 conjunct                                  *)
(*   read Q30 s = gcm_ctr_raw (word (8 * i + 13)) ctr0                          *)
(* to wbn_loop_invariant (and thus wbn_loop_inv_core auto-tracks it).  Then     *)
(* WBN_FRONT_BUF_EXT / WBN_LOOP_INVARIANT_ENTRY must re-establish it at i=0     *)
(* (from conjunct 46 via the gcm_ctr_raw (word 13) identity), and the step     *)
(* case advances it 8i+13 -> 8(i+1)+13 = 8i+21 over the 8 in-body increments.  *)
(* ------------------------------------------------------------------------- *)

(* gcm_ctr_raw_def moved to Sec 2 (session-008): the Sec-4 invariant now pins
   Q30 = gcm_ctr_raw (word (8*i+13)) ctr0, so the definition must precede Sec 4.
   Its body-only algebra lemmas remain here. *)

(* the 4 lane-extraction lemmas (used to prove GCM_CTR_RAW_INCR without a
   symbolic-w WORD_BLAST, which OOMs -- see Sec 2 AVOID note).  Each proves fast
   via WORD_SIMPLE_SUBWORD_CONV (extracts the lane) then WORD_BLAST (w appears
   only additively in the top lane, the addend never enters the BDD). *)
let SUBW_RAW_96 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (96,32):32 word =
   word_add (word_join (word_join (word_subword ctr0 (96,8):8 word) (word_subword ctr0 (104,8):8 word):16 word)
     (word_join (word_subword ctr0 (112,8):8 word) (word_subword ctr0 (120,8):8 word):16 word):32 word) w`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;
let SUBW_RAW_64 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (64,32):32 word =
   word_join (word_join (word_subword ctr0 (64,8):8 word) (word_subword ctr0 (72,8):8 word):16 word)
     (word_join (word_subword ctr0 (80,8):8 word) (word_subword ctr0 (88,8):8 word):16 word):32 word`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;
let SUBW_RAW_32 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (32,32):32 word =
   word_join (word_join (word_subword ctr0 (32,8):8 word) (word_subword ctr0 (40,8):8 word):16 word)
     (word_join (word_subword ctr0 (48,8):8 word) (word_subword ctr0 (56,8):8 word):16 word):32 word`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;
let SUBW_RAW_0 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (0,32):32 word =
   word_join (word_join (word_subword ctr0 (0,8):8 word) (word_subword ctr0 (8,8):8 word):16 word)
     (word_join (word_subword ctr0 (16,8):8 word) (word_subword ctr0 (24,8):8 word):16 word):32 word`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;

(* the increment: `add v30.4s,v30.4s,v31.4s` (v31 = word 2^96) is a lane-wise
   32-bit add; the model emits it as word_join of word_add(word_subword v30 lane)(word c)
   with c=1 on the top lane, 0 elsewhere.  This advances the raw counter by 1. *)
let GCM_CTR_RAW_INCR = prove
 (`word_join
    (word_join
     (word_add (word_subword (gcm_ctr_raw w ctr0) (96,32):32 word) (word 1))
     (word_add (word_subword (gcm_ctr_raw w ctr0) (64,32):32 word) (word 0)):64 word)
    (word_join
     (word_add (word_subword (gcm_ctr_raw w ctr0) (32,32):32 word) (word 0))
     (word_add (word_subword (gcm_ctr_raw w ctr0) (0,32):32 word) (word 0)):64 word):int128 =
    gcm_ctr_raw (word_add w (word 1)) ctr0`,
  REWRITE_TAC[SUBW_RAW_96; SUBW_RAW_64; SUBW_RAW_32; SUBW_RAW_0; WORD_ADD_0] THEN
  GEN_REWRITE_TAC RAND_CONV [gcm_ctr_raw_def] THEN
  REWRITE_TAC[WORD_RULE
    `!(x:32 word) w. word_add (word_add x w) (word 1) = word_add x (word_add w (word 1))`]);;

(* REV32 fold: `rev32 v_,v30` (esize=32) applied to gcm_ctr_raw w ctr0 yields
   gcm_ctr_add w ctr0 -- the proper AES keystream input for CTR block w.  The
   arm_REV32_VEC tower is auto-generated by the stepper (~8k chars, deterministic),
   so the reusable form is a TACTIC that folds `read Qd sN` after a rev32-of-v30 step.
   VALIDATED recipe (session-007, proves in ~2s):
     <capture the rev32 tower T = rhs of `read Qd sN`>, then prove `T = gcm_ctr_add w ctr0` by
       REWRITE_TAC[gcm_ctr_raw_def] THEN
       GEN_REWRITE_TAC RAND_CONV [GCM_CTR_ADD_LANES] THEN
       <SPEC_TAC the `word_add <topbytes> w` atom to a fresh 32-word> THEN
       GEN_TAC THEN CONV_TAC WORD_BLAST
   CRUCIAL: unfold gcm_ctr_raw EVERYWHERE (plain REWRITE_TAC[gcm_ctr_raw_def], NOT ONCE_DEPTH)
   and unfold the RHS via GCM_CTR_ADD_LANES so BOTH sides carry only the shared symbolic-add
   atom; THEN SPEC_TAC that atom away before WORD_BLAST (WORD_BLAST on a live symbolic
   `word_add _ w` OOMs -- see Sec 2 AVOID).  The GCM_SIMD_SIMPLIFY_TAC used per body step may
   already collapse part of the rev32 tower; adapt the captured-tower shape accordingly.

   REV32_FOLD_TAC qd sn wtm: rewrite the assumption `read qd sn = <rev32 tower>` so its
   rhs becomes `gcm_ctr_add wtm ctr0`.  Proves the fold equation on the fly via the recipe,
   generalizing over wtm so WORD_BLAST never meets the symbolic addend. *)
let REV32_FOLD_TAC (qd:string) (sn:string) (wtm:term) : tactic =
  fun (asl,gl) ->
    let tower = tryfind (fun (_,th) -> match concl th with
      | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),st)),r)
          when string_of_term c = qd && (try fst(dest_var st)=sn with _ -> false) -> r
      | _ -> fail()) asl in
    (* generalize wtm -> a fresh w:32 word, prove the fold for symbolic w, then re-specialize *)
    let tower_gen = subst [`w:32 word`, wtm] tower in
    let fold_thm = prove(mk_eq(tower_gen, `gcm_ctr_add w ctr0`),
      REWRITE_TAC[gcm_ctr_raw_def] THEN
      GEN_REWRITE_TAC RAND_CONV [GCM_CTR_ADD_LANES] THEN
      W(fun (_,gw) ->
         let atom = find_term (fun t -> match t with
           | Comb(Comb(Const("word_add",_),_),Var("w",_)) -> true | _ -> false) gw in
         SPEC_TAC(atom, `aa:32 word`)) THEN
      GEN_TAC THEN CONV_TAC WORD_BLAST) in
    let fold_spec = INST [wtm,`w:32 word`] fold_thm in
    RULE_ASSUM_TAC(REWRITE_RULE[fold_spec]) (asl,gl);;

(* CTR_RAW_INCR_FOLD_TAC qd sn wtm: the increment counterpart of REV32_FOLD_TAC.
   After `add v30,v30,v31` @0x4a8/0x4bc/... + GCM_SIMD_SIMPLIFY_TAC, the assumption
   `read Qd sn = <single-add tower over gcm_ctr_raw wtm ctr0>` (top lane
   word_add (word_subword (gcm_ctr_raw wtm ctr0)(96,32))(word 1), others +0) folds
   to `read Qd sn = gcm_ctr_raw (word_add wtm (word 1)) ctr0` via GCM_CTR_RAW_INCR
   instantiated at w:=wtm.  Fold ONCE PER add (before the next add re-nests the
   +1s) so only the single-+1 GCM_CTR_RAW_INCR LHS is ever matched.
   VALIDATED (session-008, self-test proved; MATCH_ACCEPT on the exact simplified
   single-add shape). *)
let CTR_RAW_INCR_FOLD_TAC (qd:string) (sn:string) (wtm:term) : tactic =
  let incr_spec = INST [wtm,`w:32 word`] GCM_CTR_RAW_INCR in
  RULE_ASSUM_TAC(fun th ->
    match concl th with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),st)),_)
        when string_of_term c = qd && (try fst(dest_var st)=sn with _ -> false) ->
        REWRITE_RULE[incr_spec] th
    | _ -> th);;

(* ------------------------------------------------------------------------- *)
(* 10. Phase 4: fire the ENSURES_WHILE skeleton -> WBN_MAIN_LOOP (session-006)*)
(*                                                                            *)
(* The back-edge of .L256_dec_main_loop is                                    *)
(*   cmp x0,x5 @0x9e4 ; stp q6,q7,[x2],#32 @0x9e8 ; b.lt 0x4a0 @0x9ec         *)
(* i.e. the SIGNED conditional branch b.lt is the LAST body instruction and   *)
(* its flag-setting cmp is two instructions earlier -- BOTH inside the body.  *)
(* That is the ENSURES_WHILE_UP2_TAC shape (branch folded into the body): the *)
(* body postcondition PC is word(if i+1<k then pc1 else pc2), the flag never  *)
(* crosses a frame boundary, and the exit lands at the fall-through pc2.       *)
(* Count k = (nblk-9) DIV 8; pc1 = pc+0x4a0 (head); pc2 = pc+0x9f0 (exit).     *)
(*                                                                            *)
(* PROBLEM: ENSURES_WHILE_UP2_TAC's internal `C ,, C = C` conjunct is         *)
(* discharged by MAYCHANGE_IDEMPOT_TAC, which THROWS ASSIGNS_SEQ_ABSORB_CONV  *)
(* on this 4-memory-region frame (the MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_  *)
(* ABI macro doesn't canonicalize into the ASSIGNS sequence ABSORB expects).  *)
(* FIX: expand the ABI macro FIRST, then MAYCHANGE_IDEMPOT_TAC succeeds (~2s). *)
(* up2_pth is a verbatim re-proof of ENSURES_WHILE_UP2_TAC's internal pth, and *)
(* UP2_ABI_TAC is the closure at common/relational.ml:2137 with the ABI       *)
(* expand spliced into the idempotence CONJ_TAC leg.                          *)
(* ------------------------------------------------------------------------- *)

(* the applied PC-free core, as a (num->armstate->bool) and as a \i s. abstr. *)
let wbn_core_applied =
  list_mk_comb(`wbn_loop_inv_core`,
    [`pc:num`;`ctr0:int128`;`in_p:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
     `key_p:int64`;`htbl_p:int64`;`stackpointer:int64`;`nblk:num`;`ibytes:byte list`;
     `xi:int128`;`h:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;
     `k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;
     `k12:int128`;`k13:int128`;`k14:int128`]);;

let wbn_core_iv = list_mk_abs([`i:num`;`s:armstate`],
  mk_comb(mk_comb(wbn_core_applied,`i:num`),`s:armstate`));;

(* ENSURES_WHILE_UP2_TAC's internal `pth` (common/relational.ml:1974), re-proved
   here so we can reach it with an ABI-aware idempotence discharge. *)
let up2_pth = prove(
  `forall k pc1 pc2 (loopinv:num->A->bool) C precond postcond
      (pcounter:(A,(N)word)component) step pc.
    C ,, C = C /\ ~(k = 0) /\
    ensures step
      (\s. program_decodes s /\ read pcounter s = word pc /\ precond s)
      (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinv 0 s)
      C /\
    (forall i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
      ==> ensures step
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinv i s)
        (\s. program_decodes s /\
             read pcounter s = word (if i + 1 < k then pc1 else pc2) /\
             loopinv (i + 1) s)
        C) /\
    ensures step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinv k s)
        postcond C
    ==>
    ensures step
      (\s. program_decodes s /\ read pcounter s = word pc /\ precond s)
      postcond C`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "HC HK HPRE HLOOP HPOST" THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
  META_EXISTS_TAC THEN CONJ_TAC THENL
  [ALL_TAC; USE_THEN "HPOST" (UNIFY_ACCEPT_TAC [`Q:A->bool`])] THEN
  REMOVE_THEN "HPOST" (K ALL_TAC) THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
  EXISTS_TAC `(\(s:A). program_decodes s /\
                       read pcounter s = (word pc1:(N)word) /\
                       loopinv (k - 1) s)` THEN
  CONJ_TAC THENL [
    ALL_TAC;
    USE_THEN "HLOOP" (fun th -> MP_TAC (SPEC `(k-1)` th)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `k - 1 + 1 = k` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC]
    THEN REWRITE_TAC[LT_REFL]
  ] THEN
  SUBGOAL_THEN `k - 1 < k` MP_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  SPEC_TAC (`k - 1`,`j:num`) THEN INDUCT_TAC THENL [
    ASM_REWRITE_TAC[] THEN NO_TAC;
    FIRST_X_ASSUM (fun th -> DISCH_TAC THEN MP_TAC th) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN (LABEL_TAC "HPREVLOOP") THEN
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
    META_EXISTS_TAC THEN CONJ_TAC THENL
    [USE_THEN "HPREVLOOP" (UNIFY_ACCEPT_TAC [`Q:A->bool`]); ALL_TAC] THEN
    USE_THEN "HLOOP" (fun th -> MP_TAC (SPEC `j:num` th)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM ADD1] THEN NO_TAC
  ]);;

(* ENSURES_WHILE_UP2_TAC caller with ABI-aware idempotence discharge. *)
let UP2_ABI_TAC k pc1 pc2 iv =
  MATCH_MP_TAC up2_pth THEN
  MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv] THEN
  BETA_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC];;

(* ---- body Q8..Q15 re-derivation (session-011) ----------------------------- *)
(* The next raw-ct group (blocks 8(i+1)+0..8(i+1)+7) is loaded fresh in the body *)
(* (ldp q8,q9,[x0],#32 @0x810 etc, x0 = in_p+128(i+1)).  The session-010 finding *)
(* is that the sim discards these read-facts — but they are RE-DERIVABLE at any  *)
(* body state from the surviving in_p loop-constant (read (memory :> bytes       *)
(* (in_p,16*nblk)) s = num_of_bytelist ibytes), which is preserved (in_p is      *)
(* read-only, out_p disjoint).  WBN_RAWCT_BOUND: the step-case bound i<(nblk-9)   *)
(* DIV 8 gives 8(i+1)+m < nblk for m<8.  WBN_RAWCT_READ: INPUT_BYTES_TO_BYTE128_ *)
(* LANES (wb.ml:2909) specialized so each block reads at in_p+16*(8(i+1)+m) =     *)
(* bytes_to_int128(SUB_LIST(16*(8(i+1)+m),16) ibytes) — exactly the invariant's  *)
(* read Q8..Q15 (i+1) values.  Prefer this to preserving the reg facts through   *)
(* 300+ steps (per the reviewer's "re-derive over preserve" note).               *)
let WBN_RAWCT_BOUND = prove
 (`i < (nblk - 9) DIV 8 /\ 9 <= nblk ==> !m. m < 8 ==> 8 * (i+1) + m < nblk`,
  STRIP_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN ASM_ARITH_TAC);;

let WBN_RAWCT_READ = prove
 (`i < (nblk - 9) DIV 8 /\ 9 <= nblk /\
   LENGTH (ibytes:byte list) = 16 * nblk /\
   read (memory :> bytes (in_p:int64, 16 * nblk)) s = num_of_bytelist ibytes
   ==> !m. m < 8
       ==> read (memory :> bytes128 (word_add in_p (word (16 * (8*(i+1)+m))))) s =
           bytes_to_int128 (SUB_LIST (16 * (8*(i+1)+m), 16) ibytes)`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s:armstate`]
    INPUT_BYTES_TO_BYTE128_LANES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL] THEN
    SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` SUBST1_TAC THENL
     [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC_ALL WBN_RAWCT_BOUND) THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 10a. Phase 4 body-sim machinery (session-009).                             *)
(*                                                                            *)
(* The loop body 0x4a0..0x9ec (340 instrs) is a software-pipelined 8-block     *)
(* group: 8 AES-256 keystreams (aese/aesmc towers), 8 GHASH Horner folds,      *)
(* the CTR-block counter advancing 8i+13 -> 8i+21 = 8(i+1)+13, 4 stp stores,   *)
(* next-group ldp loads, and the signed b.lt back-edge.  The sim is driven     *)
(* per-region (VALIDATED session-009, s0..s340 all clean, terms kept flat):    *)
(*   - counter-input rev32 v_,v30 folds:  REV32_FOLD_TAC "Qd" "sN" `word(8i+c)`*)
(*   - counter-increment add v30 folds:   CTR_INCR_NORM_TAC "sN" c  (fold once *)
(*       per add, THEN normalize word_add(word(8i+c))(word 1) -> word(8i+c+1)) *)
(*   - AES/GHASH bulk 14..317:  ARM_STEPS_FOLD_Q18LATEST_TAC (keeps only the    *)
(*       latest Q18 GHASH partial) + DISCARD_STALE_Q19_TAC + GCM_SIMD_SIMPLIFY  *)
(*       (folds the rev64 ct byte-trees); pile stays ~5-6k chars.              *)
(*   - store window 318..340:  Q18LATEST stepper (store read-backs self-        *)
(*       propagate; do NOT blanket-VSTEPS - a 781-hyp pile makes the stepper    *)
(*       throw `mk_comb: types do not agree` on the stp).                       *)
(*   - back-edge b.lt @0x9ec:  resolve NF/VF via WB_PTRCMP_FLAGS (a=128*(i+2),  *)
(*       d=128*((nblk-1)DIV8)) as STANDALONE flag theorems rewritten into the   *)
(*       assumptions (NOT MP_TAC'd into the goal - that pollution breaks the    *)
(*       stp step).  PC lands at if 128*(i+2)<128*((nblk-1)DIV8) then 0x4a0     *)
(*       else 0x9f0, bridged to if i+1<(nblk-9)DIV8 ... by WBN_PC_BRIDGE.       *)
(* ------------------------------------------------------------------------- *)

(* fold add-v30 increment then normalize the counter to word(8*i+(c+1)) *)
let CTR_INCR_NORM_TAC (sn:string) (c:int) : tactic =
  let cur = mk_comb(`word:num->32 word`,
    mk_binop `(+):num->num->num` `8*i` (mk_small_numeral c)) in
  let nrm = WORD_RULE (mk_eq(
    mk_binop `word_add:32 word->32 word->32 word` cur `word 1:32 word`,
    mk_comb(`word:num->32 word`,
      mk_binop `(+):num->num->num` `8*i` (mk_small_numeral (c+1))))) in
  CTR_RAW_INCR_FOLD_TAC "Q30" sn cur THEN RULE_ASSUM_TAC(REWRITE_RULE[nrm]);;

(* discard all-but-latest read Q19 s_ facts (the GHASH accumulator grows a big
   partial tower each step; older states are dead).  Mirror of the wb.ml
   DISCARD_STALE_Q18_TAC. *)
let state_num_of_q19_fact th =
  try let c = concl th in if not(is_eq c) then None else
    (match lhs c with
       Comb(Comb(Const("read",_),Const("Q19",_)),Var(sn,_))
         when String.length sn>1 && sn.[0]='s' ->
           Some(int_of_string(String.sub sn 1 (String.length sn-1)))
     | _ -> None) with _ -> None;;
let DISCARD_STALE_Q19_TAC : tactic = fun (asl,w) ->
  let nums = List.filter_map (fun (_,th) -> state_num_of_q19_fact th) asl in
  match nums with [] | [_] -> ALL_TAC (asl,w)
  | _ -> let mx = List.fold_left max 0 nums in
         DISCARD_ASSUMPTIONS_TAC (fun th ->
           (match state_num_of_q19_fact th with Some k -> k<mx | None -> false)) (asl,w);;

(* ---- session-015: body-close reduce-window infrastructure (SESSION-014 ADDENDUM) --------
   The final GHASH reduce (0x924..0x9b4) reloads Q16 = the [sp+64] modulus (now carried by
   the invariant) and feeds the pmull/eor3 chain via Q16/Q17/Q21/Q29.  Over that window we
   must KEEP Q16-Q19 (KEEPGH) yet not let their per-step towers pile up.  KEEPGH_LATEST =
   KEEPGH + keep only the LATEST read of each of Q16/Q17/Q18/Q19.  (KEEPGH lives in wb.ml;
   this generalizes DISCARD_STALE_Q19_TAC to all four GHASH regs.)  VALIDATED (session-015)
   to define+typecheck against the warm ckpt; the full-window behaviour is validated once
   the new invariant is cold-loaded (the body reaches this window only via wbn_loop_inv_core,
   which the warm ckpt still bakes WITHOUT the [sp+64] conjunct). *)
let state_num_of_qreg qn th =
  try let c = concl th in if not(is_eq c) then None else
    (match lhs c with
       Comb(Comb(Const("read",_),Const(n,_)),Var(sn,_))
         when n=qn && String.length sn>1 && sn.[0]='s' ->
           Some(int_of_string(String.sub sn 1 (String.length sn-1)))
     | _ -> None) with _ -> None;;
let DISCARD_STALE_QREG_TAC qn : tactic = fun (asl,w) ->
  let nums = List.filter_map (fun (_,th) -> state_num_of_qreg qn th) asl in
  match nums with [] | [_] -> ALL_TAC (asl,w)
  | _ -> let mx = List.fold_left max 0 nums in
         DISCARD_ASSUMPTIONS_TAC (fun th ->
           (match state_num_of_qreg qn th with Some k -> k<mx | None -> false)) (asl,w);;
let DISCARD_OLDSTATE_KEEPGH_LATEST_TAC s =
  DISCARD_OLDSTATE_KEEPGH_TAC s THEN
  DISCARD_STALE_QREG_TAC "Q16" THEN DISCARD_STALE_QREG_TAC "Q17" THEN
  DISCARD_STALE_QREG_TAC "Q18" THEN DISCARD_STALE_QREG_TAC "Q19";;
let ARM_STEPS_FOLD_KEEPGH_LATEST_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_TAC THEN
              DISCARD_OLDSTATE_KEEPGH_LATEST_TAC s THEN CLARIFY_TAC) (statenames "s" snums);;
(* NO-SIMPLIFY variant for the final GHASH reduce window (290..326): once Q16 is the
   CONCRETE [sp+64] modulus (word 0xc2..00), GCM_SIMD_SIMPLIFY on the reduce pmulls
   stack-overflows (session-014); step without it so the reduce stays symbolic and
   read Q19 lands self-contained.  Q18 is abbreviated as `midacc` before this window
   so the towers stay small. *)
let ARM_STEPS_FOLD_KEEPGH_LATEST_NOSIMP_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN
              DISCARD_OLDSTATE_KEEPGH_LATEST_TAC s THEN CLARIFY_TAC) (statenames "s" snums);;

(* WBN_NBLK_GE_9: moved here (session-024) from below the back-edge cluster so
   RAWCT_LEMMA_AT (Sec 10b) can reference it — the cold-load regression the
   e2386b15 commit introduced (Unbound value at the RAWCT_LEMMA_AT let). Depends
   only on DIVISION + ARITH_TAC, so it is safe to hoist. *)
let WBN_NBLK_GE_9 = prove
 (`0 < (nblk - 9) DIV 8 ==> 9 <= nblk`,
  MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 10b. Phase-4 postcond-MATCH machinery (session-023).                       *)
(*                                                                            *)
(* SESSION-023 finding: the 16 orthogonal postcond conjuncts (all but the      *)
(* escalated Q19 [11]) close CHEAT-free once three sub-problems are solved.    *)
(* These tactics are VALIDATED live end-to-end (body sim reaches s340; the     *)
(* counter conjunct [0] closes standalone via CTR_ADD_CLOSE_TAC in 0.8s).      *)
(*                                                                            *)
(* (A) Q8..Q15 raw-ct [3-10] (s017 Finding-2 part A — the 5-session blocker):  *)
(*   right after each ldp (steps 221 src s220, 273 src s272, 306 src s305,     *)
(*   309 src s308), the machine gives read Qk sN = read(mem:>bytes128 ADDR)    *)
(*   s(N-1) — an OLD-STATE read that is un-closeable once s(N-1) is discarded.  *)
(*   FIX: RAWCT_LEMMA_AT "s(N-1)" registers the WBN_RAWCT_READ !m form at the   *)
(*   source state, then RESOLVE_QREG_A "Qk" "sN" m rewrites read Qk sN into     *)
(*   the SPEC form bytes_to_int128 (SUB_LIST (16*(8*(i+1)+m),16) ibytes).       *)
(*   The stepper then PROPAGATES this state-independent RHS forward at the      *)
(*   current state (validated: read Q8 s225 already clean spec form) — so it    *)
(*   survives every later discard.  m = 0..7 for Q8..Q15 in load order.         *)
(*                                                                            *)
(* (B) Reduce-window hang (the s014 concrete-modulus blocker): since Q19 [11]   *)
(*   goes behind the scoped CHEAT, DISCARD Q16/Q17/Q18/Q19 BEFORE the reduce    *)
(*   window (before step 290).  The concrete [sp+64] modulus pmull that made    *)
(*   GCM_SIMD_SIMPLIFY stack-overflow is then gone — 290..305 steps in ~15s.    *)
(*   No midacc / Tier-2 machinery needed for the 16 conjuncts.                  *)
(*                                                                            *)
(* (C) Store window 310..340 + counter folds (s017 Finding-2 part B, PARTIAL):  *)
(*   the AES keystream Q0..Q7 is consumed by eor3 (steps 313..335) to make the  *)
(*   plaintext; KEEPGH-style stepping discards it, so store read-backs dangle.  *)
(*   ARM_STEPS_DATA_NOSIMP_TAC keeps Q0..Q15 + ALL memory reads current (no      *)
(*   GCM_SIMD_SIMPLIFY — SIMPLIFY + kept Q0..Q15 explodes on the eor3 towers)    *)
(*   and DOES land the plaintext eor3 results current (Q5 s320 present).  BUT    *)
(*   the counter regs Q0..Q4 then arrive as RAW rev32/incr towers: the SMALL    *)
(*   one [0] closes via CTR_ADD_CLOSE_TAC standalone, but the compound ones      *)
(*   [1][2] (10k/51k chars, many un-folded nested adds) OOM WORD_BLAST.  SO the  *)
(*   counter regs MUST be REV32_FOLD/CTR_INCR_NORM-folded DURING the store       *)
(*   window (as the committed sim does: REV32_FOLD "Q25" s326, "Q4" s336,        *)
(*   CTR_INCR_NORM s335/s337) — the OPEN piece for the next session is a store   *)
(*   window that keeps Q0..Q7 keystream + stores current AND folds Q0..Q4        *)
(*   counters per-step (hybrid of ARM_STEPS_DATA_NOSIMP_TAC + the fold points).  *)
(*                                                                            *)
(* (D) Verified trivial closers: [9][10] pointer advances = CONV_TAC WORD_RULE; *)
(*   [3-5] Q5-Q7 plaintext = GSYM AES256_XOR_ENCRYPT_RECONSTRUCT + GCM_CTR_INC* *)
(*   _LANES + WORD_RULE (tail closer wb.ml:2779); [store-forall] ASM_CASES      *)
(*   j<8*(i+1); [htable] REWRITE htable_mem_dec + let_CONV + ASM_REWRITE;        *)
(*   [MAYCHANGE] MONOTONE_MAYCHANGE_TAC.  [11] Q19 = scoped CHEAT (escalated).   *)
(* ------------------------------------------------------------------------- *)

(* RAWCT_LEMMA_AT sprev: register the WBN_RAWCT_READ !m raw-ct lemma at state
   sprev (needs 9<=nblk via WBN_NBLK_GE_9 + the in_p read-only loop-constant). *)
let RAWCT_LEMMA_AT sprev : tactic =
  SUBGOAL_THEN
    (subst[mk_var(sprev,`:armstate`),`s:armstate`]
      `!m. m < 8 ==> read (memory :> bytes128 (word_add in_p (word (16 * (8*(i+1)+m))))) s =
                     bytes_to_int128 (SUB_LIST (16 * (8*(i+1)+m), 16) ibytes)`)
    ASSUME_TAC THENL
   [MATCH_MP_TAC WBN_RAWCT_READ THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WBN_NBLK_GE_9 THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(* RESOLVE_QREG_A qreg scur m: rewrite read qreg scur (currently = read(mem@ADDR)
   s_prev for some ADDR = in_p+16*(8*(i+1)+m)) into the spec form via the raw !m
   lemma already in the assumptions (from RAWCT_LEMMA_AT).  Robust to any ADDR
   syntactic form: proves ADDR = canonical by WORD_RULE then rewrites+accepts. *)
let RESOLVE_QREG_A (qreg:string) (scur:string) (m:int) : tactic =
  fun (asl,w) ->
    let mnum = mk_small_numeral m in
    let th,addr = tryfind (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(n,_)),Var(sn,_))),
             Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),
               Comb(Const("bytes128",_),addr))),_))
          when n=qreg && sn=scur -> (th,addr)
      | _ -> fail()) asl in
    let raw = tryfind (fun (_,t) -> match concl t with
        Comb(Const("!",_),Abs(Var("m",_),Comb(Comb(Const("==>",_),_),
          Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),_)),
               Comb(Const("bytes_to_int128",_),_))))) -> t
      | _ -> fail()) asl in
    let canon = vsubst[mnum,`m:num`] `word_add in_p (word (16 * (8*(i+1)+m))):int64` in
    let addr_eq = WORD_RULE (mk_eq(addr,canon)) in
    let raw_inst = MATCH_MP raw (ARITH_RULE(mk_comb(mk_comb(`(<):num->num->bool`,mnum),`8`))) in
    let target = mk_eq((parse_term (Printf.sprintf "read %s %s :int128" qreg scur)),
      vsubst[mnum,`m:num`] `bytes_to_int128 (SUB_LIST (16 * (8*(i+1)+m), 16) ibytes)`) in
    (SUBGOAL_THEN target ASSUME_TAC THENL
      [GEN_REWRITE_TAC LAND_CONV [th] THEN REWRITE_TAC[addr_eq] THEN ACCEPT_TAC raw_inst;
       ALL_TAC]) (asl,w);;

(* DISCARD_KEEP_DATA_TAC / ARM_STEPS_DATA{,_NOSIMP}_TAC: store-window steppers that
   keep Q0..Q15 (data regs, incl. AES keystream) + ALL memory reads at the current
   state, discarding only stale/scratch old-state reads.  NOSIMP variant avoids the
   AES-tower explosion that GCM_SIMD_SIMPLIFY triggers when Q0..Q15 are kept. *)
let DISCARD_KEEP_DATA_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec is_mem_read t = match t with
      Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),_)),_) -> true
    | Comb(a,b) -> is_mem_read a || is_mem_read b | Abs(_,t2) -> is_mem_read t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if is_mem_read (concl thm) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else true);;
let ARM_STEPS_DATA_NOSIMP_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN
              DISCARD_KEEP_DATA_TAC s THEN CLARIFY_TAC) (statenames "s" snums);;

(* CTR_ADD_CLOSE_TAC: close a counter postcond conjunct whose LHS is the raw
   rev32-of-gcm_ctr_raw tower and RHS is gcm_ctr_add (word W) ctr0.  Same recipe
   as REV32_FOLD_TAC's fold proof.  VALIDATED on conjunct [0] (0.8s).  WARNING:
   only works when the LHS tower is SINGLE-rev32 (folded during stepping); a
   compound raw tower with many un-folded nested +1 adds OOMs WORD_BLAST — fold
   the counter DURING the store window instead. *)
let CTR_ADD_CLOSE_TAC : tactic =
  REWRITE_TAC[gcm_ctr_raw_def] THEN
  GEN_REWRITE_TAC RAND_CONV [GCM_CTR_ADD_LANES] THEN
  W(fun (_,gw) ->
    let atom = find_term (fun t -> match t with
      | Comb(Comb(Const("word_add",_),_),Comb(Const("word",_),Comb(Comb(Const("+",_),_),_))) -> true
      | _ -> false) gw in
    SPEC_TAC(atom, `aa:32 word`)) THEN
  GEN_TAC THEN CONV_TAC WORD_BLAST;;

(* ------------------------------------------------------------------------- *)
(* 10c. Phase-4 body-close machinery (session-027).                           *)
(*                                                                            *)
(* SESSION-027: the full body sim + 16-conjunct close, driven CHEAT-free      *)
(* (only [11]/Q19 keeps its scoped CHEAT).  The committed sim (below) uses a   *)
(* KEEPDATA stepper that keeps Q0..Q19 latest (incl. the AES keystream Q0-Q7,  *)
(* which the old Q18LATEST/KEEPGH_LATEST steppers discarded — the s025         *)
(* keystream-survival blocker).  Resolve-at-load for Q8-Q15 is done with       *)
(* RESOLVE_LDP2_TAC, which fixes the s023 RESOLVE_QREG_A latent bug: the ldp    *)
(* leaves  read Qk s(N) = read(mem@ADDR) s(N-1)  (memory read at the LOAD-INPUT *)
(* state s(N-1)), so the raw !m lemma must be matched AT s(N-1), not s(N).      *)
(* RESOLVE_QREG_C matches the raw lemma at the register-read's own memory-state *)
(* and uses PURE_ONCE_REWRITE (plain REWRITE collapses 8*(i+1)+0 -> 8*(i+1),    *)
(* breaking the m=0 ACCEPT).                                                    *)
(* ------------------------------------------------------------------------- *)

(* KEEPDATA steppers: keep the LATEST read of Q0..Q19 (data regs incl keystream)
   + all memory + loop constants; discard everything else old-state. *)
let wbn_datawords_0_19 =
  ["Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7";"Q8";"Q9";
   "Q10";"Q11";"Q12";"Q13";"Q14";"Q15";"Q16";"Q17";"Q18";"Q19"];;
let DISCARD_OLDSTATE_KEEPDATA_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec mentions_data t = match t with
      Comb(Comb(Const("read",_),cmp),_) ->
        (match cmp with Const(n,_) -> List.mem n wbn_datawords_0_19 | _ -> false)
    | Comb(a,b) -> mentions_data a || mentions_data b | Abs(_,t2) -> mentions_data t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if mentions_data (concl thm) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else true);;
let DISCARD_STALE_DATA_TAC = MAP_EVERY DISCARD_STALE_QREG_TAC wbn_datawords_0_19;;
let ARM_STEPS_FOLD_KEEPDATA_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_TAC THEN
              DISCARD_STALE_DATA_TAC THEN DISCARD_OLDSTATE_KEEPDATA_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;
(* NO-SIMPLIFY variant for the reduce + store windows: GCM_SIMD_SIMPLIFY on the
   concrete [sp+64] modulus pmull (reduce) or the kept eor3 keystream towers
   (store) explodes (session-014/024); step symbolic instead. *)
let ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN
              DISCARD_STALE_DATA_TAC THEN DISCARD_OLDSTATE_KEEPDATA_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;
(* outright drop reads of the listed regs at ANY state (Q19 is CHEATed, so the
   whole GHASH cluster Q16..Q19 goes before the reduce window; dead scratch
   Q29/Q21 dropped before the store-forall close to shrink the pile). *)
let DISCARD_QREGS_TAC qns : tactic =
  DISCARD_ASSUMPTIONS_TAC(fun th -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(n,_)),Var(_,_))),_) -> List.mem n qns
    | _ -> false);;

(* RESOLVE_QREG_C qreg scur m: like RESOLVE_QREG_A but matches the raw !m lemma AT
   the state of the register-read's embedded memory read (sload = s(N-1) for an
   ldp), not any state; and PURE_ONCE_REWRITE (not REWRITE) so the m=0 index
   8*(i+1)+0 is not collapsed to 8*(i+1) before ACCEPT.  (session-027: the s023
   RESOLVE_QREG_A fails on a recorded/cold run because the ldp memory read stays
   at s(N-1) while the raw lemma advances to s(N).) *)
let RESOLVE_QREG_C (qreg:string) (scur:string) (m:int) : tactic =
  fun (asl,w) ->
    let mnum = mk_small_numeral m in
    let th,addr,sload = tryfind (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(n,_)),Var(sn,_))),
             Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),
               Comb(Const("bytes128",_),addr))),Var(sl,_)))
          when n=qreg && sn=scur -> (th,addr,sl)
      | _ -> fail()) asl in
    let raw = tryfind (fun (_,t) -> match concl t with
        Comb(Const("!",_),Abs(Var("m",_),Comb(Comb(Const("==>",_),_),
          Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var(sl,_))),
               Comb(Const("bytes_to_int128",_),_))))) when sl=sload -> t
      | _ -> fail()) asl in
    let canon = vsubst[mnum,`m:num`] `word_add in_p (word (16 * (8*(i+1)+m))):int64` in
    let addr_eq = WORD_RULE (mk_eq(addr,canon)) in
    let raw_inst = MATCH_MP raw (ARITH_RULE(mk_comb(mk_comb(`(<):num->num->bool`,mnum),`8`))) in
    let target = mk_eq((parse_term (Printf.sprintf "read %s %s :int128" qreg scur)),
      vsubst[mnum,`m:num`] `bytes_to_int128 (SUB_LIST (16 * (8*(i+1)+m), 16) ibytes)`) in
    (SUBGOAL_THEN target ASSUME_TAC THENL
      [GEN_REWRITE_TAC LAND_CONV [th] THEN PURE_ONCE_REWRITE_TAC[addr_eq] THEN ACCEPT_TAC raw_inst;
       ALL_TAC]) (asl,w);;

(* RESOLVE_LDP2_TAC exec qa qb ma mb sload scur: resolve a pair of raw-ct regs
   loaded by one ldp.  At frontier sload register raw@sload, do a BARE verbose
   step to scur (no discard/clarify so raw@sload survives), resolve qa/qb, then
   drop the stale raw-form reads + old-state + clarify. *)
let RESOLVE_LDP2_TAC exec qa qb ma mb sload scur : tactic =
  RAWCT_LEMMA_AT sload THEN
  ARM_VERBOSE_STEP_TAC exec scur THEN
  RESOLVE_QREG_C qa scur ma THEN
  RESOLVE_QREG_C qb scur mb THEN
  DISCARD_ASSUMPTIONS_TAC(fun th -> match concl th with
     Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(n,_)),_)),
          Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),_)),_))
       -> n=qa || n=qb
   | _ -> false) THEN
  DISCARD_STALE_DATA_TAC THEN DISCARD_OLDSTATE_KEEPDATA_TAC scur THEN CLARIFY_TAC;;

(* NEWBLK_CLOSE_TAC: close one new-block leg of the store-forall (j = 8*(i+1)+m,
   0<=m<8).  Canonicalize block indices 8*(i+1)+m -> 8*i+(8+m), normalize both
   store-readback address forms (out_p+(128*(i+1)+16m) and (out_p+128*(i+1))+16m)
   to the flat goal form, fire the readback, then fold the plaintext
   (GSYM aes13 + GCM_CTR_INC_ITER_ADD) and bridge the SUB_LIST index. *)
let NEWBLK_CLOSE_TAC =
  let canon = [ARITH_RULE `16 * 8 * (i+1) = 128*(i+1)`;
    ARITH_RULE `8*(i+1)+0 = 8*i+8`; ARITH_RULE `8*(i+1)+1 = 8*i+9`;
    ARITH_RULE `8*(i+1)+2 = 8*i+10`; ARITH_RULE `8*(i+1)+3 = 8*i+11`;
    ARITH_RULE `8*(i+1)+4 = 8*i+12`; ARITH_RULE `8*(i+1)+5 = 8*i+13`;
    ARITH_RULE `8*(i+1)+6 = 8*i+14`; ARITH_RULE `8*(i+1)+7 = 8*i+15`;
    ARITH_RULE `8*(i+1) = 8*i+8`] in
  let subbr = [ARITH_RULE `128 * (i + 1) = 16 * (8 * i + 8)`;
    ARITH_RULE `128 * (i + 1) + 16 = 16 * (8 * i + 9)`;
    ARITH_RULE `128 * (i + 1) + 32 = 16 * (8 * i + 10)`;
    ARITH_RULE `128 * (i + 1) + 48 = 16 * (8 * i + 11)`;
    ARITH_RULE `128 * (i + 1) + 64 = 16 * (8 * i + 12)`;
    ARITH_RULE `128 * (i + 1) + 80 = 16 * (8 * i + 13)`;
    ARITH_RULE `128 * (i + 1) + 96 = 16 * (8 * i + 14)`;
    ARITH_RULE `128 * (i + 1) + 112 = 16 * (8 * i + 15)`] in
  let addrbr = map (fun m -> WORD_RULE(subst[mk_small_numeral(16*m),`OFF:num`; mk_small_numeral m,`M:num`]
      `word_add (word_add out_p (word (128*(i+1)))) (word OFF):int64 =
       word_add out_p (word (16*(8*(i+1)+M))):int64`)) (0--7) in
  RULE_ASSUM_TAC(REWRITE_RULE addrbr) THEN
  REWRITE_TAC canon THEN RULE_ASSUM_TAC(REWRITE_RULE (canon @ subbr)) THEN
  (* SESSION-028 FIX: fire the store-readback hyp (ASM_REWRITE) BEFORE folding
     the raw aese/aesmc tower.  The s027 order ran GSYM aes13 first, when the
     goal LHS was still `read(mem) s340` (tower not yet substituted), so the
     fold had nothing to match and REFL_TAC failed on the 8 new-block legs. *)
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM aes13] THEN REWRITE_TAC[GCM_CTR_INC_ITER_ADD] THEN
  REWRITE_TAC (canon @ subbr) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM aes13] THEN REWRITE_TAC[GCM_CTR_INC_ITER_ADD] THEN
  REWRITE_TAC (canon @ subbr) THEN REFL_TAC;;
(* fold the machine keystream tower to aes13 + bridge gcm_ctr_add/inc_iter, for
   the plaintext register conjuncts [0-2] (Q5,Q6,Q7). *)
let PLAINTEXT_CLOSE_TAC =
  REWRITE_TAC[GSYM aes13] THEN REWRITE_TAC[GCM_CTR_INC_ITER_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(8*i+8)+5 = 8*i+13`; ARITH_RULE `(8*i+8)+6 = 8*i+14`;
              ARITH_RULE `(8*i+8)+7 = 8*i+15`] THEN
  REFL_TAC;;

(* The htable H-power memory reads give  h_k = byteswap128 (polyval_dot ...)  (the ODD
   powers h3/h5/h7 and, after unfolding, h2), but BODY_Q19_CLOSE_ALGEBRA's antecedent wants
   byteswap128 h_k = polyval_dot ...  Bridge by byteswap128 involution: rewrite with the
   h_k=... fact then BYTESWAP128_INVOLUTION.  VALIDATED (session-015) on the h2 rung. *)
let BSWAP_INVOL_MASSAGE_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c &&
       (match rhs c with Comb(Const("byteswap128",_),_) -> true | _ -> false)
    then SUBST_ALL_TAC th else NO_TAC)) THEN
  REWRITE_TAC[BYTESWAP128_INVOLUTION];;

(* PC back-edge arithmetic bridge (session-009). *)
let WBN_DIV_SHIFT = prove
 (`9 <= nblk ==> (nblk - 1) DIV 8 = (nblk - 9) DIV 8 + 1`,
  STRIP_TAC THEN
  SUBGOAL_THEN `nblk - 1 = (nblk - 9) + 1 * 8` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIV_ADD_MOD] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC);;

let WBN_PC_BRIDGE = prove
 (`9 <= nblk
   ==> ((128 * (i + 2) < 128 * (nblk - 1) DIV 8) <=> (i + 1 < (nblk - 9) DIV 8))`,
  DISCH_TAC THEN ASM_SIMP_TAC[WBN_DIV_SHIFT] THEN ARITH_TAC);;

(* WBN_NBLK_GE_9 moved above Sec 10b (session-024 load-order fix). *)

(* premises of WB_PTRCMP_FLAGS at the back-edge: X0=in_p+128*(i+2) (a),
   X5=128*((nblk-1)DIV8)+in_p (d); both offsets < 2^63 from val in_p+16*nblk. *)
let WBN_PTRCMP_PREMS = prove
 (`val (in_p:int64) + 16 * nblk < 2 EXP 63 /\ i < (nblk - 9) DIV 8
   ==> val (in_p:int64) + 128 * (i + 2) < 2 EXP 63 /\
       val (in_p:int64) + 128 * (nblk - 1) DIV 8 < 2 EXP 63`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN
  MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN ASM_ARITH_TAC);;

(* word distributes over the back-edge if *)
let WBN_PC_IF = prove
 (`(if b then word (pc + 1184) else word (pc + 2544)):int64 =
   word (if b then pc + 1184 else pc + 2544)`,
  COND_CASES_TAC THEN REWRITE_TAC[]);;

(* the LOOP theorem: PC=0x4a0 /\ core 0  ==>  PC=0x9f0 /\ core k, over the front
   MAYCHANGE frame.  Entry/exit are trivial reflexive ensures (pre=post at the
   respective PC); count<>0 is DIVISION arithmetic (17<=nblk => (nblk-9)DIV8>=1).
   Body = the Phase-4 step case, CHEAT_TAC for now (see the big TODO below). *)
let wbn_main_loop_goal =
  let kk = `(nblk - 9) DIV 8` in
  let loop_pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0x4a0)`;
      mk_comb(mk_comb(wbn_core_applied,`0`),`s:armstate`)]) in
  let loop_post = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0x9f0)`;
      mk_comb(mk_comb(wbn_core_applied,kk),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[loop_pre; loop_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_MAIN_LOOP = prove(wbn_main_loop_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UP2_ABI_TAC `(nblk - 9) DIV 8` `pc + 0x4a0` `pc + 0x9f0` wbn_core_iv THEN
  REPEAT CONJ_TAC THENL
   [ (* 1. count <> 0 : 17<=nblk => (nblk-1) DIV 8 >= 2 > 0 *)
    SUBGOAL_THEN `1 <= nblk - 1` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN ASM_ARITH_TAC;
    (* 2. entry: PC=0x4a0 /\ core 0 -> same (0-step reflexive ensures) *)
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC;
    (* 3. ===================== PHASE 4 LOOP BODY (TODO) ===================== *)
    (* Goal after `REPEAT STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core] THEN   *)
    (* CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0"`:         *)
    (* state s0 at 0x4a0, iteration i, with (confirmed session-006, risk #2): *)
    (*   X0=in_p+128(i+1) X2=out_p+128(i+1) X4=in_p+16nblk                     *)
    (*   X5=128*((nblk-1)DIV8)+in_p X1=128nblk X9=16nblk X10=sp+64 X11=key_p   *)
    (*   X3=xi_p X6=htbl_p X16=ivec_p X15=word 4294967296 SP=stackpointer      *)
    (*   Q0..Q4 = gcm_ctr_add(8i+8..8i+12) ctr0   (store/counter stream ahead) *)
    (*   Q5,Q6,Q7 = plaintext(8i+5,8i+6,8i+7)     (+8i keystream, CONFIRMED)   *)
    (*   Q8..Q15 = raw ct blocks 8i+0..8i+7        (GHASH stream lags)         *)
    (*   Q19 = ghash_polyval_acc over blocks 0..8i-1                           *)
    (*   Q26=k12 Q27=k13 Q28=k14 Q31=word 79228162514264337593543950336        *)
    (*   Q30 = gcm_ctr_raw (word (8i+13)) ctr0  (session-008 patch; read by     *)
    (*         the body's first instr rev32 v5,v30; advances 8i+13 -> 8i+21).   *)
    (* Sim decodes cleanly.  340 instrs, body 0x4a0..0x9ec.  Target: core(i+1)  *)
    (* at PC=if i+1<k then 0x4a0 else 0x9f0.                                    *)
    (*                                                                          *)
    (* SESSION-008 body-entry recon (VALIDATED interactively against the        *)
    (* Q30-patched wbn_loop_inv_core_v2, s0..s10 stepped clean, 2.6s+3.5s):     *)
    (*  loop-head counter schedule (objdump 0x4a0..0x4d0), interleaved:         *)
    (*    0x4a0 rev32 v5,v30   : Q5  <- rev32(gcm_ctr_raw(8i+13)) = keystream   *)
    (*                            ctr @ 8i+13  [= block 8(i+1)+5 of the invt]   *)
    (*    0x4a8 add   v30,v31  : Q30 8i+13 -> 8i+14                             *)
    (*    0x4b8 rev32 v6,v30   : Q6  <- gcm_ctr_add(8i+14) [= 8(i+1)+6]          *)
    (*    0x4bc add   v30,v31  : Q30 8i+14 -> 8i+15                             *)
    (*    0x4d0 rev32 v7,v30   : Q7  <- gcm_ctr_add(8i+15) [= 8(i+1)+7]          *)
    (*  (further add v30 steps advance to 8i+21 = 8(i+1)+13 for the next head.) *)
    (*  Q8..Q15 get rev64'd (0x4ac,0x4c0,0x4c8,0x4cc,0x4d4,...) into byteswap   *)
    (*  towers -> the GHASH input stream (byteswap128 of the raw ct blocks).    *)
    (*                                                                          *)
    (*  TWO per-instruction folds are the crux (both keep terms flat):          *)
    (*  (a) COUNTER-INPUT rev32 v_,v30:  REV32_FOLD_TAC "Q<d>" "s<n>"           *)
    (*        `word (8*i+13+j):32 word`  (j=0,1,2,... per rev32).  VALIDATED:    *)
    (*        Q5@s5 folded 10466ch -> `gcm_ctr_add (word (8*i+13)) ctr0` in 1.9s.*)
    (*  (b) COUNTER INCREMENT add v30,v30,v31:  after GCM_SIMD_SIMPLIFY_TAC the  *)
    (*        stepper emits, on the TOP lane,                                   *)
    (*          word_add (word_add (word_subword (gcm_ctr_raw w ctr0)(96,32))    *)
    (*                             (word 1)) (word 1) ...   (N nested +1 for N   *)
    (*        adds since the last fold), NOT GCM_CTR_RAW_INCR's single-+1 LHS.   *)
    (*        => need a small INCR-fold tactic (REV32_FOLD_TAC-style): normalize *)
    (*        the k nested (word 1) to (word k), then apply GCM_CTR_RAW_INCR     *)
    (*        (generalized to +k, or iterated) to land Q30=gcm_ctr_raw(w+k).     *)
    (*        Simplest: fold Q30 back to gcm_ctr_raw ONCE PER add (before the    *)
    (*        next add re-nests), so only the single-+1 GCM_CTR_RAW_INCR fires.  *)
    (*                                                                          *)
    (* GHASH close via GHASH_ACC_8BLOCK_EXTEND (blk := \k. bytes_to_int128     *)
    (* (SUB_LIST(16*k,16) ibytes)).  Counter compose: GCM_CTR_ADD_COMPOSE /    *)
    (* GCM_CTR_INC_ITER_ADD.  Signed back-edge b.lt @0x9ec resolved inside the *)
    (* body by WB_PTRCMP_FLAGS (x0 vs x5).  Reach the body-init state via       *)
    (*   REPEAT STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core] THEN              *)
    (*   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0"          *)
    (* (VALIDATED session-008: yields hyps incl. read Q30 s0 = gcm_ctr_raw      *)
    (* (word(8*i+13)) ctr0 at asm 58).  Use per-step GCM_SIMD_SIMPLIFY_TAC to   *)
    (* control term growth (see WBN_FRONT_STEP_TAC pattern, Sec 3).             *)
    (* SESSION-009: full 340-instr sim below is VALIDATED end-to-end (s0..s340   *)
    (* clean, PC lands at if i+1<(nblk-9)DIV8 then 0x4a0 else 0x9f0 exactly).    *)
    (* Only the postcondition MATCH (27 conjuncts: 8 AES-reconstruct, GHASH Q19  *)
    (* close, store-forall) remains -> inner CHEAT_TAC (Phase-4 sub-split).      *)
    (* ===================================================================== *)
    (* SESSION-016: the 340-instr body re-sim, VALIDATED end-to-end with the   *)
    (* [sp+64]-carrying invariant (wb-dec-mainloop6).  Replaces the broken     *)
    (* session-009 Q18LATEST body (which discarded every read Qn sK, n<>18,    *)
    (* dropping the postcond facts — the s010 root cause).  Recipe:            *)
    (*  - htable unfold+split @s0 (s013): the H-power ldrs resolve, so Q17/18/  *)
    (*    19 stay self-contained.                                              *)
    (*  - front 1-13 (counter rev32/add folds) verbatim.                       *)
    (*  - Q18LATEST 14-212 (GHASH partial stays flat via keep-latest-Q18).     *)
    (*  - KEEPGH_LATEST 213-289 (keeps Q16-Q19; Q16 auto-resolves to the       *)
    (*    [sp+64] modulus word 13979173243358019584 the invariant now pins).   *)
    (*  - NO-SIMPLIFY KEEPGH_LATEST 290-326 (GCM_SIMD_SIMPLIFY on the CONCRETE  *)
    (*    Q16 pmull stack-overflows — s014); ABBREV midacc = read Q18 s301     *)
    (*    (last eor3 v18) so the reduce steps stay small.  RESULT: read Q19    *)
    (*    s326 is FULLY SELF-CONTAINED (len ~3786, no dangling reads) — the     *)
    (*    first time the body's GHASH acc closes (s014 breakthrough).          *)
    (*  - Then discard the DEAD reduce intermediates (Q16/Q17/Q29 + the giant  *)
    (*    midacc SYM tree) and fold Q25 to gcm_ctr_add(8i+19): this removes     *)
    (*    the concrete-modulus pmull that makes the store-window simplify hang. *)
    (*  - RESUME simplify (KEEPGH_LATEST) 327-337 with the Q30/Q4 counter folds *)
    (*    (fold Q30 at s335 for the skipped no-simplify add@317).              *)
    (*  - back-edge 338-340: WB_PTRCMP_FLAGS standalone-rewrite + WBN_PC_BRIDGE.*)
    (*    PC lands EXACTLY at if i+1<(nblk-9)DIV8 then pc+1184 else pc+2544.    *)
    (* ===================================================================== *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0" THEN
    (* htable unfold+split @s0 (s013): resolve the 13 H-power memory cells *)
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
    FIRST_X_ASSUM(fun th ->
      let c = concl th in
      if can (find_term (fun t->match t with Const("byteswap128",_)->true|_->false)) c &&
         can (find_term (fun t->match t with Const("karatsuba_mid",_)->true|_->false)) c
      then STRIP_ASSUME_TAC th else NO_TAC) THEN
    (* ===================================================================== *)
    (* SESSION-027: full body sim (KEEPDATA — keeps Q0..Q19 incl keystream) +   *)
    (* 16-conjunct close, CHEAT-free.  Only [11]/Q19 keeps its scoped CHEAT     *)
    (* (route DECIDED: tail FOLD_MID_HPOW port, separate follow-up).  Driven    *)
    (* live end-to-end this session (s0..s340, PC exact; all 8/8 store-forall   *)
    (* new-block legs + plaintext + pointers + htable + MAYCHANGE close).       *)
    (* Resolve-at-load via RESOLVE_LDP2_TAC (fixes the s023 RESOLVE_QREG_A       *)
    (* state-subscript bug: the ldp memory read stays at the LOAD-INPUT state). *)
    (* --- counter setup 1..13 (rev32/add folds) --- *)
    ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--1) THEN
    REV32_FOLD_TAC "Q5" "s1" `word (8*i+13):32 word` THEN
    ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (2--3) THEN GCM_SIMD_SIMPLIFY_TAC THEN
    CTR_INCR_NORM_TAC "s3" 13 THEN
    ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (4--7) THEN GCM_SIMD_SIMPLIFY_TAC THEN
    REV32_FOLD_TAC "Q6" "s7" `word (8*i+14):32 word` THEN
    ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (8--8) THEN GCM_SIMD_SIMPLIFY_TAC THEN
    CTR_INCR_NORM_TAC "s8" 14 THEN
    ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (9--13) THEN GCM_SIMD_SIMPLIFY_TAC THEN
    REV32_FOLD_TAC "Q7" "s13" `word (8*i+15):32 word` THEN
    (* --- AES/GHASH bulk 14..212 (KEEPDATA keeps Q0..Q19 incl keystream) --- *)
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (14--120) THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (121--211) THEN DISCARD_STALE_Q19_TAC THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (212--212) THEN DISCARD_STALE_Q19_TAC THEN
    CTR_INCR_NORM_TAC "s212" 15 THEN
    (* --- 213..289 KEEPDATA; ldp@221 loads Q8,Q9 (resolve-at-load), ctr folds --- *)
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (213--220) THEN
    RESOLVE_LDP2_TAC AESV8_GCM_8X_DEC_256_WB_EXEC "Q8" "Q9" 0 1 "s220" "s221" THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (222--258) THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (259--259) THEN
    REV32_FOLD_TAC "Q20" "s259" `word (8*i+16):32 word` THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (260--261) THEN
    CTR_INCR_NORM_TAC "s261" 16 THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (262--270) THEN
    REV32_FOLD_TAC "Q22" "s270" `word (8*i+17):32 word` THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (271--272) THEN
    (* ldp@273 loads Q10,Q11 *)
    RESOLVE_LDP2_TAC AESV8_GCM_8X_DEC_256_WB_EXEC "Q10" "Q11" 2 3 "s272" "s273" THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (274--279) THEN
    CTR_INCR_NORM_TAC "s279" 17 THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (280--288) THEN
    REV32_FOLD_TAC "Q23" "s288" `word (8*i+18):32 word` THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (289--289) THEN
    CTR_INCR_NORM_TAC "s289" 18 THEN
    (* --- session-064 Q19 R1' WIRE-IN: instead of DISCARDing the GHASH cluster,   *)
    (*     ABBREV the three s289 accumulators (Q17/Q19/Q18 = PL/PH/PM) opaque so    *)
    (*     the reduce byteform stays small (629ch), then KEEP Q16-Q19 through the   *)
    (*     reduce (KEEPDATA_NOSIMP keeps Q0-Q19 incl keystream AND the abbreviated  *)
    (*     Q19).  read Q19 s326 lands = WBN_MACHINE_REDUCE_IS_PROP3_PACK's LHS[PL,   *)
    (*     PH,PM]; the postcond Q19 conjunct then closes via WBN_Q19_CLOSE_TAC.     *)
    WBN_Q19_EXTRACT_ABBREV_TAC "s289" THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (290--305) THEN
    (* ldp@306 loads Q12,Q13 ; ldp@309 loads Q14,Q15 *)
    RESOLVE_LDP2_TAC AESV8_GCM_8X_DEC_256_WB_EXEC "Q12" "Q13" 4 5 "s305" "s306" THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (307--308) THEN
    RESOLVE_LDP2_TAC AESV8_GCM_8X_DEC_256_WB_EXEC "Q14" "Q15" 6 7 "s308" "s309" THEN
    (* --- store window 310..337 NOSIMP (keeps keystream Q0-Q7 + stores current); *)
    (*     fold the mov-source counters Q25@326, Q4@336, Q30 incr @335/337. --- *)
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (310--326) THEN
    REV32_FOLD_TAC "Q25" "s326" `word (8*i+19):32 word` THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (327--335) THEN
    CTR_INCR_NORM_TAC "s335" 19 THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (336--336) THEN
    REV32_FOLD_TAC "Q4" "s336" `word (8*i+20):32 word` THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (337--337) THEN
    CTR_INCR_NORM_TAC "s337" 20 THEN
    (* --- back-edge: normalize X0, cmp @338, resolve NF/VF, stp @339, b.lt @340 --- *)
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
      `word_add (word_add in_p (word (128 * (i + 1)))) (word 128):int64 =
       word_add in_p (word (128*(i+2)))`]) THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (338--338) THEN
    SUBGOAL_THEN `9 <= nblk` ASSUME_TAC THENL
     [MATCH_MP_TAC WBN_NBLK_GE_9 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    (* derive NF/VF flag equivalences as standalone theorems, rewrite into asms.
       (MUST rewrite into assumptions - MP_TAC'ing the implication into the goal
       pollutes the state and breaks the subsequent stp step, session-009.) *)
    (fun (asl,w) ->
       let prem = MATCH_MP WBN_PTRCMP_PREMS
         (CONJ (ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`)
               (ASSUME `i < (nblk - 9) DIV 8`)) in
       let flags = MATCH_MP (SPECL [`in_p:int64`; `128*(i+2)`; `128*((nblk-1) DIV 8)`]
                     WB_PTRCMP_FLAGS) prem in
       RULE_ASSUM_TAC(REWRITE_RULE[CONJUNCT1 flags; CONJUNCT2 flags]) (asl,w)) THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (339--340) THEN
    FIRST_X_ASSUM(fun th -> if can (find_term (fun t -> t = `read PC s340`)) (concl th)
      then ASSUME_TAC(REWRITE_RULE[MATCH_MP WBN_PC_BRIDGE (ASSUME `9 <= nblk`)] th)
      else NO_TAC) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (* postcondition match: PC (WBN_PC_IF), counter indices (8*(i+1)=8*i+8), then
       the plaintext + Q8-Q15 (already resolved) + Q19 (CHEAT) + store-forall. *)
    REWRITE_TAC[WBN_PC_IF] THEN
    REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN
    REWRITE_TAC[ARITH_RULE `(8*i+8)+8 = 8*i+16`; ARITH_RULE `(8*i+8)+9 = 8*i+17`;
      ARITH_RULE `(8*i+8)+10 = 8*i+18`; ARITH_RULE `(8*i+8)+11 = 8*i+19`;
      ARITH_RULE `(8*i+8)+12 = 8*i+20`; ARITH_RULE `(8*i+8)+13 = 8*i+21`] THEN
    (* ASM_REWRITE closes the already-resolved conjuncts (Q0-Q4 counters, Q8-Q15
       raw-ct); split the residual and close each remaining conjunct.  Drop the
       dead GHASH reduce-scratch (Q16..Q25/Q29) first so the pile is small. *)
    DISCARD_QREGS_TAC ["Q16";"Q17";"Q18";"Q19";"Q20";"Q21";"Q22";"Q23";"Q24";"Q25";"Q29"] THEN
    REPEAT CONJ_TAC THENL
     [ (* [0-2] plaintext Q5,Q6,Q7 *)
       PLAINTEXT_CLOSE_TAC; PLAINTEXT_CLOSE_TAC; PLAINTEXT_CLOSE_TAC;
       (* [3] Q19 GHASH acc — session-064 R1' close (was CHEAT): the goal is
          <machine reduce byteform over PL/PH/PM> = ghash..(8*i+8), closed by the
          CLEAN value-equality WBN_Q19_CLOSE_TAC builds from the stashed s289
          accumulators (WBN_MACHINE_REDUCE_IS_PROP3_PACK + block-algebra). *)
       WBN_Q19_CLOSE_TAC;
       (* [4-5] X0/X2 pointer advances *)
       CONV_TAC WORD_RULE; CONV_TAC WORD_RULE;
       (* [6] store-forall: old (j<8*(i+1)) from the invariant's own store-forall
          (preserved); new (8*(i+1)<=j<8*(i+1)+8) via the 8-way NEWBLK close. *)
       X_GEN_TAC `j:num` THEN DISCH_TAC THEN
       ASM_CASES_TAC `j < 8 * (i + 1)` THENL
        [ FIRST_ASSUM(fun th -> match concl th with
            Comb(Const("!",_),Abs(Var("j",_),Comb(Comb(Const("==>",_),
              Comb(Comb(Const("<",_),_),Comb(Comb(Const("*",_),_),
                Comb(Comb(Const("+",_),_),_)))),_))) ->
              MP_TAC(SPEC `j:num` th) | _ -> NO_TAC) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])];
          MP_TAC(ARITH_RULE
            `~(j < 8 * (i + 1)) /\ j < 8 * i + 16
             ==> j = 8*(i+1) \/ j = 8*(i+1)+1 \/ j = 8*(i+1)+2 \/ j = 8*(i+1)+3 \/
                 j = 8*(i+1)+4 \/ j = 8*(i+1)+5 \/ j = 8*(i+1)+6 \/ j = 8*(i+1)+7`) THEN
          ASM_REWRITE_TAC[] THEN
          DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
          NEWBLK_CLOSE_TAC ];
       (* [7] htable predicate *)
       REWRITE_TAC[htable_mem_dec] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
       ASM_REWRITE_TAC[];
       (* [8] MAYCHANGE frame *)
       REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
       REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC ];
    (* 4. exit: PC=0x9f0 /\ core k -> same (0-step reflexive ensures) *)
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC]);;

(* ========================================================================= *)
(* Section 11. PHASE 5 -- PREPRETAIL (0x9f0..0xed4 straight-line sim).         *)
(*                                                                            *)
(* The loop-exit state (WBN_MAIN_LOOP postcond: PC=pc+0x9f0, wbn_loop_inv_core *)
(* at k=(nblk-9)DIV8, GHASH lagging one 8-block group) is driven through the   *)
(* prepretail code (0x9f0..0xed4, 313 instrs) to the SHARED TAIL SEAM at       *)
(* pc+3796 (=0xed4), the exact state every wb.ml WB_TAIL_r_TAC consumes        *)
(* (ENSURES_INIT_TAC "s265" on q_at r = wb.ml's wb_front_postcond[nblk:=r]).   *)
(*                                                                            *)
(* SEAM CONTRACT (session-033, verified against wb.ml:3081-3803 + Explore):    *)
(*  - The tail seam is at pc+3796 (0xed4), NOT 0xec0.  The prepretail sims     *)
(*    THROUGH 0xec0..0xed0 (ext v16; sub x5,x4,x0; cmp; ldr q9,[x0],#16; ldp   *)
(*    q24,q25,[x6,#160]) to set up the tail's Q9/Q24/Q25/X0/X5 registers.      *)
(*  - In the <=8 band the FRONT folds 0 GHASH blocks (Q19=word_bytereverse xi) *)
(*    and the TAIL folds all r.  The prepretail is the pipelined analogue: it  *)
(*    folds the FINAL in-flight 8-block group (blocks 8k..8k+7) into Q19       *)
(*    (catching the lagging GHASH stream up), and computes AES keystreams for  *)
(*    the tail's Q0..Q7.                                                       *)
(*  - RECOMPOSE SUBSTITUTION (session-033, fully determined off the s313       *)
(*    harvest): the prepretail postcond = wb_front_postcond instantiated with  *)
(*      ctr0'   := gcm_ctr_add (word (8*(k+1))) ctr0   (tail's shifted counter) *)
(*      in_p'   := word_add in_p  (word (128*(k+1)))                            *)
(*      out_p'  := word_add out_p (word (128*(k+1)))                            *)
(*      nblk'   := r = nblk - 8*(k+1)   (1..8)                                  *)
(*      xi'     := the caught-up ghash acc over all 8*(k+1) processed blocks    *)
(*      ibytes' := the last r blocks of ibytes                                 *)
(*    Q0..Q7 reconcile via GCM_CTR_ADD_COMPOSE:                                 *)
(*      gcm_ctr_add(8k+8+i) ctr0 = gcm_ctr_inc^i (gcm_ctr_add(8(k+1)) ctr0).    *)
(*                                                                            *)
(* SIM RECIPE (session-033, VALIDATED interactively end-to-end on              *)
(* wb-dec-mainloop10, ~2min, no hang/OOM; reaches read PC s313 = word(pc+3796);*)
(* full state harvested -- see orchestrator/logs/session-033-prepretail-       *)
(* recipe.md and session-033-summary.md):                                      *)
(*                                                                            *)
(*   REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core] THEN     *)
(*   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0" THEN         *)
(*   RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN                          *)
(*   RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN                    *)
(*   FIRST_X_ASSUM(fun th -> ... strip the byteswap128/karatsuba_mid conj) THEN *)
(*   ABBREV_TAC for k := (nblk - 9) DIV 8, THEN                                 *)
(*   [counter setup 1..14: rev32 v5@2/v6@7/v7@14, add v30@3/9]                  *)
(*   ARM_STEPS_TAC EXEC (1--1) THEN               [ldp q26,q27 = keys k0,k1]    *)
(*   ARM_STEPS_TAC EXEC (2--2) THEN GCM_SIMD_SIMPLIFY_TAC THEN                  *)
(*   REV32_FOLD_TAC "Q5" "s2" [word (8*k+13):32 word] THEN                      *)
(*   ARM_STEPS_TAC EXEC (3--3) THEN GCM_SIMD_SIMPLIFY_TAC THEN CTR_INCR_NORM_TAC "s3" 13 THEN *)
(*   ARM_STEPS_TAC EXEC (4--7) THEN GCM_SIMD_SIMPLIFY_TAC THEN                  *)
(*   REV32_FOLD_TAC "Q6" "s7" [word (8*k+14):32 word] THEN                      *)
(*   ARM_STEPS_TAC EXEC (8--9) THEN GCM_SIMD_SIMPLIFY_TAC THEN CTR_INCR_NORM_TAC "s9" 14 THEN *)
(*   ARM_STEPS_TAC EXEC (10--14) THEN GCM_SIMD_SIMPLIFY_TAC THEN                *)
(*   REV32_FOLD_TAC "Q7" "s14" [word (8*k+15):32 word] THEN                     *)
(*   (* AES/GHASH bulk 15..240, KEEPDATA keeps Q0..Q19 *)                       *)
(*   ARM_STEPS_FOLD_KEEPDATA_TAC EXEC (15--120) THEN                            *)
(*   ARM_STEPS_FOLD_KEEPDATA_TAC EXEC (121--211) THEN                           *)
(*   ARM_STEPS_FOLD_KEEPDATA_TAC EXEC (212--240) THEN                           *)
(*   (* discard the GHASH cluster before the [sp+64] modulus reduce (Q19        *)
(*      CHEATed -- kills the s014 concrete-modulus hang) *)                     *)
(*   DISCARD_QREGS_TAC ["Q16";"Q17";"Q18";"Q19"] THEN                           *)
(*   ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC EXEC (241--306) THEN                    *)
(*   (* tail setup 307..313 -> pc+3796 *)                                       *)
(*   ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC EXEC (307--313) THEN                    *)
(*   ENSURES_FINAL_STATE_TAC THEN ...close per-conjunct...                      *)
(*                                                                            *)
(* Harvested s313 register facts (k=(nblk-9)DIV8; all CHEAT-free except Q19):   *)
(*   PC = pc+3796                                        [matches seam]         *)
(*   Q0..Q7 = aes13(gcm_ctr_add(8k+8..8k+15) ctr0) k0..k13   [ctr shift]        *)
(*   Q24 = karatsuba_mid h8 || karatsuba_mid h7 ; Q25 = h8   [reloaded @0xed0]  *)
(*   Q16/Q19 = GHASH acc staging   -> SCOPED CHEAT (= the [11] RINNER=LINNER)   *)
(*   X0 = in_p+128(k+1)+16 ; X2 = out_p+128(k+1) ; X4 = in_p+16nblk             *)
(*   X5 = (in_p+16nblk)-(in_p+128(k+1)) = word(16*r)                            *)
(*   X1=128nblk X9=16nblk X10=sp+64 X11=key_p X3=xi_p X6=htbl_p X16=ivec_p      *)
(*   X15=2^32 Q31=2^96 SP=stackpointer ; [sp+64]=0xC2..; keys k0..k14; htable;  *)
(*   store-forall j<8*(k+1); input buffer -- all preserved.                    *)
(*   NF/ZF/CF/VF on word_sub(in_p+16nblk)(in_p+128(k+1)) vs 112 [-> r=... calc] *)
(*                                                                            *)
(* NEXT SESSION deliverable: state WBN_PREPRETAIL as an ensures with post =     *)
(* wb_front_postcond[shifted params above] (so WB_TAIL_r applies verbatim),     *)
(* drive the recipe above, close every conjunct CHEAT-free EXCEPT the Q19       *)
(* caught-up GHASH (scoped CHEAT mirroring [11] at :2085 -- same identity),     *)
(* commit, cold-load gate.  The goal below is the current skeleton (post at     *)
(* pc+3796 minimal); it is CHEAT-stubbed so the file loads.  DO NOT ship the    *)
(* minimal post -- replace with the shifted wb_front_postcond before the        *)
(* Phase-6 recompose can use it.                                                *)
(* ========================================================================= *)

(* Counter-shift identity (session-034 GO/NO-GO, re-proved s035): the prepretail
   produces AES keystreams Q0..Q7 at absolute block indices 8*(k+1)+i (i=0..7),
   i.e. gcm_ctr_add(word(8*k+8+i))ctr0.  The shifted-front tail seam expects
   Q0..Q7 = aes13(gcm_ctr_inc^i ctr0') k0..k13 with ctr0' = gcm_ctr_add(8*(k+1))ctr0.
   This bridges the two forms so the recompose consumes wb_front_postcond verbatim. *)
let WBN_CTR_SHIFT = prove
 (`!(k:num) (i:num) (ctr0:int128).
     gcm_ctr_add (word (8*k+8+i)) ctr0 =
     gcm_ctr_inc_iter i (gcm_ctr_add (word (8*(k+1))) ctr0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GCM_CTR_INC_ITER_ADD; GCM_CTR_ADD_COMPOSE; WORD_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

(* SESSION-036 SOUNDNESS FIX: this raw harvested literal states Q16/Q19 at a FRESH
   unconstrained xi' (read Q19 s = word_bytereverse xi', Q16 = its staging).  As written
   that is FALSE (word_bytereverse is a bijection + the ARM model is deterministic, so
   `!xi'. hyps ==> ensures ... Q19 = word_bytereverse xi'` cannot hold) -- flagged by the
   s035 review.  It is kept verbatim as `_raw` only as the substitution source; the SOUND
   post `wbn_prepretail_post` below pins xi' to the real caught-up accumulator. *)
let wbn_prepretail_post_raw = parse_term {|\(s:armstate).
    (aligned_bytes_loaded:armstate->(64)word->((8)word)list->bool)
    (s:armstate)
    ((word:num->(64)word) (pc:num))
    (aesv8_gcm_8x_dec_256_wb_mc:((8)word)list) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (PC:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) ((pc:num) + 3796) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q24:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((polyval_dot:(128)word->(128)word->(128)word)
           ((byteswap128:(128)word->(128)word) (h:(128)word))
          ((byteswap128:(128)word->(128)word) (h:(128)word)))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((byteswap128:(128)word->(128)word) (h:(128)word))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q25:(armstate,(128)word)component)
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((polyval_dot:(128)word->(128)word->(128)word)
           ((byteswap128:(128)word->(128)word) (h:(128)word))
          ((byteswap128:(128)word->(128)word) (h:(128)word)))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    ((read:(armstate,bool)component->armstate->bool)
     (NF:(armstate,bool)component)
     (s:armstate) <=>
     (ival:(64)word->int)
     ((word_sub:(64)word->(64)word->(64)word)
      ((word_sub:(64)word->(64)word->(64)word)
       ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
       ((word:num->(64)word) (16 * (nblk:num))))
      ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
      ((word:num->(64)word) (128 * (((nblk:num) - 9) DIV 8 + 1)))))
     ((word:num->(64)word) 112)) <
     (int_of_num:num->int)0) /\
    ((read:(armstate,bool)component->armstate->bool)
     (ZF:(armstate,bool)component)
     (s:armstate) <=>
     (val:(64)word->num)
     ((word_sub:(64)word->(64)word->(64)word)
      ((word_sub:(64)word->(64)word->(64)word)
       ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
       ((word:num->(64)word) (16 * (nblk:num))))
      ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
      ((word:num->(64)word) (128 * (((nblk:num) - 9) DIV 8 + 1)))))
     ((word:num->(64)word) 112)) =
     0) /\
    ((read:(armstate,bool)component->armstate->bool)
     (CF:(armstate,bool)component)
     (s:armstate) <=>
     112 <=
     (val:(64)word->num)
     ((word_sub:(64)word->(64)word->(64)word)
      ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
      ((word:num->(64)word) (16 * (nblk:num))))
     ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
     ((word:num->(64)word) (128 * (((nblk:num) - 9) DIV 8 + 1)))))) /\
    ((read:(armstate,bool)component->armstate->bool)
     (VF:(armstate,bool)component)
     (s:armstate) <=>
     ~((ival:(64)word->int)
       ((word_sub:(64)word->(64)word->(64)word)
        ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
        ((word:num->(64)word) (16 * (nblk:num))))
       ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
       ((word:num->(64)word) (128 * (((nblk:num) - 9) DIV 8 + 1))))) -
       (int_of_num:num->int)112 =
       (ival:(64)word->int)
       ((word_sub:(64)word->(64)word->(64)word)
        ((word_sub:(64)word->(64)word->(64)word)
         ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
         ((word:num->(64)word) (16 * (nblk:num))))
        ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
        ((word:num->(64)word) (128 * (((nblk:num) - 9) DIV 8 + 1)))))
       ((word:num->(64)word) 112)))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q16:(armstate,(128)word)component)
    (s:armstate) =
    (word_subword:(256)word->num#num->(128)word)
    ((word_join:(128)word->(128)word->(256)word)
     ((word_bytereverse:(128)word->(128)word) (xi':(128)word))
    ((word_bytereverse:(128)word->(128)word) (xi':(128)word)))
    (64,128) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q7:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_add:(32)word->(128)word->(128)word)
     ((word:num->(32)word) (8 * ((nblk:num) - 9) DIV 8 + 15))
    (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q6:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_add:(32)word->(128)word->(128)word)
     ((word:num->(32)word) (8 * ((nblk:num) - 9) DIV 8 + 14))
    (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q0:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_add:(32)word->(128)word->(128)word)
     ((word:num->(32)word) (8 * ((nblk:num) - 9) DIV 8 + 8))
    (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q1:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_add:(32)word->(128)word->(128)word)
     ((word:num->(32)word) (8 * ((nblk:num) - 9) DIV 8 + 9))
    (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes64:(64)word->((64)word->(8)word,(64)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (word:num->(64)word) 13979173243358019584 /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X11:(armstate,(64)word)component)
    (s:armstate) =
    (key_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X9:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) (16 * (nblk:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (SP:(armstate,(64)word)component)
    (s:armstate) =
    (stackpointer:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X1:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) (128 * (nblk:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X2:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
    ((word:num->(64)word) (128 * (((nblk:num) - 9) DIV 8 + 1))) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X3:(armstate,(64)word)component)
    (s:armstate) =
    (xi_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X6:(armstate,(64)word)component)
    (s:armstate) =
    (htbl_p:(64)word) /\
    (read:(armstate,num)component->armstate->num)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes:(64)word#num->((64)word->(8)word,num)component)
     ((in_p:(64)word),16 * (nblk:num)))
    (s:armstate) =
    (num_of_bytelist:((8)word)list->num) (ibytes:((8)word)list) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (key_p:(64)word))
    (s:armstate) =
    (k0:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 16)))
    (s:armstate) =
    (k1:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 32)))
    (s:armstate) =
    (k2:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 48)))
    (s:armstate) =
    (k3:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (k4:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 80)))
    (s:armstate) =
    (k5:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 96)))
    (s:armstate) =
    (k6:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 112)))
    (s:armstate) =
    (k7:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 128)))
    (s:armstate) =
    (k8:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 144)))
    (s:armstate) =
    (k9:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 160)))
    (s:armstate) =
    (k10:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 176)))
    (s:armstate) =
    (k11:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 192)))
    (s:armstate) =
    (k12:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 208)))
    (s:armstate) =
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 224)))
    (s:armstate) =
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (htbl_p:(64)word))
    (s:armstate) =
    (h:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 16)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((byteswap128:(128)word->(128)word) (h:(128)word))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word) (h:(128)word)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 32)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((byteswap128:(128)word->(128)word) (h:(128)word))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 48)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((byteswap128:(128)word->(128)word) (h:(128)word))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((byteswap128:(128)word->(128)word) (h:(128)word))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((byteswap128:(128)word->(128)word) (h:(128)word))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 80)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((byteswap128:(128)word->(128)word) (h:(128)word))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 96)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((byteswap128:(128)word->(128)word) (h:(128)word))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 112)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((byteswap128:(128)word->(128)word) (h:(128)word))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((byteswap128:(128)word->(128)word) (h:(128)word))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 128)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((byteswap128:(128)word->(128)word) (h:(128)word))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 144)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((byteswap128:(128)word->(128)word) (h:(128)word))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 160)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((polyval_dot:(128)word->(128)word->(128)word)
           ((byteswap128:(128)word->(128)word) (h:(128)word))
          ((byteswap128:(128)word->(128)word) (h:(128)word)))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((byteswap128:(128)word->(128)word) (h:(128)word))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 176)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((polyval_dot:(128)word->(128)word->(128)word)
           ((byteswap128:(128)word->(128)word) (h:(128)word))
          ((byteswap128:(128)word->(128)word) (h:(128)word)))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X16:(armstate,(64)word)component)
    (s:armstate) =
    (ivec_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X10:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
    ((word:num->(64)word) 64) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X15:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) 4294967296 /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q31:(armstate,(128)word)component)
    (s:armstate) =
    (word:num->(128)word) 79228162514264337593543950336 /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q19:(armstate,(128)word)component)
    (s:armstate) =
    (word_bytereverse:(128)word->(128)word) (xi':(128)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X4:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) (16 * (nblk:num))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q27:(armstate,(128)word)component)
    (s:armstate) =
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q26:(armstate,(128)word)component)
    (s:armstate) =
    (k12:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q28:(armstate,(128)word)component)
    (s:armstate) =
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q5:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_add:(32)word->(128)word->(128)word)
     ((word:num->(32)word) (8 * ((nblk:num) - 9) DIV 8 + 13))
    (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q2:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_add:(32)word->(128)word->(128)word)
     ((word:num->(32)word) (8 * ((nblk:num) - 9) DIV 8 + 10))
    (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q4:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_add:(32)word->(128)word->(128)word)
     ((word:num->(32)word) (8 * ((nblk:num) - 9) DIV 8 + 12))
    (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q3:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_add:(32)word->(128)word->(128)word)
     ((word:num->(32)word) (8 * ((nblk:num) - 9) DIV 8 + 11))
    (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X5:(armstate,(64)word)component)
    (s:armstate) =
    (word_sub:(64)word->(64)word->(64)word)
    ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) (16 * (nblk:num))))
    ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) (128 * (((nblk:num) - 9) DIV 8 + 1)))) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X0:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word)
    ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) (128 * (((nblk:num) - 9) DIV 8 + 1))))
    ((word:num->(64)word) 16)|};;

(* SESSION-036 SOUNDNESS FIX (reviewer-specified recipe).  The caught-up GHASH tag: the
   loop invariant's Q19 shape (Sec 4, :623) at index i := k+1 = (nblk-9)DIV8 + 1, i.e. the
   fold over ALL 8*(k+1) processed blocks.  This IS the true machine value of Q19 at the
   prepretail seam (the loop exits with the GHASH stream lagging 8 blocks; the prepretail
   folds the final in-flight 8-block group, catching it up to 8*(k+1)).  It is a FUNCTION of
   the pinned inputs (xi/h/ibytes/nblk from wb_front_vars), NOT a fresh unconstrained var, so
   the Q16/Q19 conjuncts below become the SAME true-but-unproven RINNER=LINNER identity as
   [11] (:2085) -- masked by the same scoped disclosed CHEAT, not a falsehood. *)
let wbn_caught_up = `ghash_polyval_acc (byteswap128 (h:int128)) (word_bytereverse (xi:int128))
    (MAP word_bytereverse
    (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) (ibytes:byte list)))
                 (8 * (((nblk:num) - 9) DIV 8 + 1))))`;;

(* Replace the raw literal's fresh `word_bytereverse xi'` (which occurs ONLY in the Q16
   staging and Q19 conjuncts -- verified s036) with the caught-up accumulator.  This drops
   xi' entirely (so the post's frees are exactly wb_front_vars) and turns:
     Q19 = word_bytereverse xi'  -->  Q19 = wbn_caught_up   (matches the i:=k+1 invariant shape)
     Q16 = word_subword(word_join (word_bytereverse xi')(word_bytereverse xi'))(64,128)
        -->  Q16 = word_subword(word_join wbn_caught_up wbn_caught_up)(64,128)  (staging of Q19) *)
let wbn_prepretail_post =
  subst [wbn_caught_up, `word_bytereverse (xi':int128)`] wbn_prepretail_post_raw;;

(* SESSION-035: the shifted-front prepretail postcondition (VALIDATED end-to-end).
   Built by harvesting the s313 state after the 313-instr sim + wb_front_fold_tac,
   with the two loop-un-tracked memory cells DROPPED (sound; see below) and the two
   GHASH staging regs Q16/Q19 stated at a fresh caught-up tag var xi'.
   Deltas vs a naive vsubst of wb.ml's wb_front_postcond (session-035 findings):
    - Q0..Q7 = aes13 (gcm_ctr_add (word (8*k+8+i)) ctr0) k0..k13 (i=0..7, k=(nblk-9)DIV8);
      the shifted-front form aes13 (gcm_ctr_inc^i ctr0') with ctr0'=gcm_ctr_add(8(k+1))ctr0
      is bridged by WBN_CTR_SHIFT for the Phase-6 recompose.
    - X0=in_p+128(k+1)+16, X2=out_p+128(k+1), X5/flags on word_sub(in_p+16nblk)(in_p+128(k+1)).
    - DROPPED (loop invariant does not track them; objdump 0xed4..0x11b0 shows the tail
      only STORES ivec_p (str q30,[x16]@0x1144) and xi_p (st1 v19,[x3]@0x11ac) at the very
      end and never READS their pre-values):
        read (memory :> bytes128 xi_p) s = xi     (front seed; tail uses Q19, not this)
        read (memory :> bytes128 ivec_p) s = ctr0
        read (memory :> bytes64 (sp+72)) s = word 0   (only [sp+64] is the reduce const)
        read (memory :> bytes128 in_p) s = <block0>   (Q9; the tail re-loads via ldr q9,[x0])
      Also DROPPED Q9 = <first tail block> (tail reloads it).  Phase 6 re-proves the tail
      leg (WB_TAIL_r) from this weaker post -- WB_TAIL_r_TAC never consumes the dropped
      facts (verified: no xi_p/ivec_p reads, and it re-loads Q9).
    - Q16/Q19 caught-up tag: SESSION-036 pins it to `wbn_caught_up` (the i:=k+1 invariant
      Q19 shape, a function of the pinned inputs) -- NOT a fresh xi'.  The s035-committed
      form used a fresh unconstrained xi' (Q19 = word_bytereverse xi'), which the s035 review
      found FALSE-as-written (bijection + determinism); s036 corrected it (see the SOUNDNESS
      FIX note above `wbn_caught_up`).  Q19 = wbn_caught_up, Q16 = its staging.  These two
      close behind the scoped disclosed CHEAT below (= the [11] RINNER=LINNER identity at
      :2085; the prepretail's own final in-flight GHASH fold is the SAME identity). *)

let wbn_prepretail_goal =
  let kk = `(nblk - 9) DIV 8` in
  let pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0x9f0)`;
      mk_comb(mk_comb(wbn_core_applied,kk),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[pre; wbn_prepretail_post; wbn_front_C_tm]) in
  (* SESSION-036: quantify over wb_front_vars ONLY (xi' dropped -- the caught-up tag is now a
     function of the pinned inputs, not a fresh var).  wbn_prepretail_post is closed over
     wb_front_vars, so the goal is closed. *)
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

(* index bound for the first tail block lane (8*k+8 < nblk when nblk>=17). *)
let WBN_Q9_INDEX_LT = prove
 (`!nblk. 17 <= nblk /\ 128 * nblk < 2 EXP 62 ==> 8 * ((nblk - 9) DIV 8) + 8 < nblk`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL[`nblk - 9`;`8`] DIVISION) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = (nblk - 9) DIV 8` THEN ASM_ARITH_TAC);;

(* The prepretail proof.  Sim recipe VALIDATED end-to-end session-033/035 (~2min, no hang):
   init at the loop invariant (i:=k), counter folds 1..14, KEEPDATA bulk 15..240,
   DISCARD Q16-Q19 before the [sp+64] modulus reduce (Q19 CHEATed -> dodges the s014
   concrete-modulus hang), NOSIMP reduce+tail-setup 241..313 -> read PC s313 = pc+3796.
   wb_front_fold_tac folds the 8 aese/aesmc keystream towers to aes13(...).
   Close: ENSURES_FINAL_STATE_TAC + ASM_REWRITE for the 62 preserved/shifted conjuncts;
   the 2 GHASH conjuncts (Q16,Q19, on xi') behind the scoped disclosed CHEAT. *)
let WBN_PREPRETAIL = prove
 (wbn_prepretail_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (find_term (fun t->match t with Const("byteswap128",_)->true|_->false)) c &&
       can (find_term (fun t->match t with Const("karatsuba_mid",_)->true|_->false)) c
    then STRIP_ASSUME_TAC th else NO_TAC) THEN
  ABBREV_TAC `k = (nblk - 9) DIV 8` THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--1) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (2--2) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q5" "s2" `word (8*k+13):32 word` THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (3--3) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  CTR_INCR_NORM_TAC "s3" 13 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (4--7) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q6" "s7" `word (8*k+14):32 word` THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (8--9) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  CTR_INCR_NORM_TAC "s9" 14 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (10--14) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q7" "s14" `word (8*k+15):32 word` THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (15--120) THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (121--211) THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (212--240) THEN
  (* session-065 Q19 R1' WIRE-IN (was DISCARD_QREGS): step to s242 (the state
     where PL/PH/PM = Q17/Q19/Q18 are all COMPLETE -- PM's final eor3 @0xdb4 is
     instr 242; the s240 the discard used had PM incomplete), ABBREV them opaque,
     then run the reduce KEEPING Q16-Q19 (byteform stays small over PL/PH/PM). *)
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (241--242) THEN
  WBN_Q19_EXTRACT_ABBREV_TAC "s242" THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (243--306) THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (307--313) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM aes13]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE(map GSYM wb_ctr_lanes_thms)) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN
  (* Q16/Q19 caught-up GHASH = the [11] RINNER=LINNER identity: scoped disclosed CHEAT (same
     as :2085; closes when the human's Q19 route lands).  The sim DISCARDS Q16-Q19 before the
     [sp+64] reduce, so these two conjuncts have no supporting assumption -- they are the ONLY
     goals mentioning `ghash_polyval_acc` (verified s036: it occurs nowhere else in the post),
     so keying the guard on it fires on exactly Q16 and Q19.  Everything else is a verbatim
     harvested assumption (ASM_REWRITE) or the MAYCHANGE frame (MONOTONE). *)
  TRY(W(fun (asl,w) ->
        if can (find_term (fun t -> is_const t && fst(dest_const t) = "ghash_polyval_acc")) w
        then WBN_Q19_PREPRETAIL_CLOSE_TAC `k:num` else NO_TAC)) THEN
  TRY MONOTONE_MAYCHANGE_TAC THEN
  TRY (ASM_REWRITE_TAC[]));;

(* ------------------------------------------------------------------------- *)
(* Section 12. PHASE 6 -- recompose the nblk>8 chain.                         *)
(* ------------------------------------------------------------------------- *)

(* WBN_LOOP_PREP: LOOP ; PREPRETAIL, i.e. pc+0x4a0 (loop head, core 0) ->      *)
(* pc+3796 (tail entry, wbn_prepretail_post), over the shared front frame.     *)
(* Both legs share the SAME quantifier prefix (wb_front_vars), hyps            *)
(* (wbn_front_hyps_wide_tm) and frame (wbn_front_C_tm); WBN_MAIN_LOOP.post is  *)
(* aconv WBN_PREPRETAIL.pre (both = decodes /\ PC=pc+0x9f0 /\ wbn_core_applied  *)
(* k), so the two chain by ENSURES_TRANS_SIMPLE with no re-sim and no new       *)
(* CHEAT (the scoped Q19 CHEAT is sealed inside WBN_PREPRETAIL).  The           *)
(* C ,, C = C obligation is the same 4-region-frame idempotence UP2_ABI_TAC    *)
(* discharges (ABI expand THEN MAYCHANGE_IDEMPOT_TAC).  Validated hyps=0        *)
(* (session-037).                                                              *)
let wbn_loop_prep_goal =
  let loop_pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0x4a0)`;
      mk_comb(mk_comb(wbn_core_applied,`0`),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[loop_pre; wbn_prepretail_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_LOOP_PREP = prove(wbn_loop_prep_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC (rand(rator(snd(dest_imp(snd(strip_forall(concl WBN_MAIN_LOOP))))))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL wb_front_vars WBN_MAIN_LOOP) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
    MP_TAC(SPECL wb_front_vars WBN_PREPRETAIL) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC]]);;

(* WBN_FRONT_TO_PREP: FRONT ; (LOOP ; PREPRETAIL), i.e. the full nblk>8 straight *)
(* chain from function entry (pc+0x20) through the loop and prepretail to the    *)
(* tail entry (pc+3796).  Chains WBN_LOOP_INVARIANT_ENTRY (pc+0x20 -> pc+0x4a0,  *)
(* establishes wbn_loop_invariant...0) with WBN_LOOP_PREP by ENSURES_TRANS_      *)
(* SIMPLE at the intermediate wbn_entry_post.  The entry post carries the FULL   *)
(* wbn_loop_invariant...0 (PC+decode baked in) whereas WBN_LOOP_PREP's pre uses  *)
(* the PC-free wbn_loop_inv_core...0; ENSURES_PRECONDITION_THM bridges them via  *)
(* WBN_INV_SPLIT (the C1/C2 decode+PC conjuncts are duplicated, collapsed by     *)
(* TAUT after the pc+0x4a0 = pc+1184 numeral rewrite).  Validated hyps=0          *)
(* (session-037).  No new CHEAT (scoped Q19/Q16 stays sealed in WBN_PREPRETAIL). *)
let wbn_front_to_prep_goal =
  let ens = list_mk_comb(`ensures arm`,
    [wbn_front_P_tm; wbn_prepretail_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_FRONT_TO_PREP = prove(wbn_front_to_prep_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_entry_post THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL wb_front_vars WBN_LOOP_INVARIANT_ENTRY) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    (* ENSURES_PRECONDITION_THM needs the PRE (loop_pre = PC-free core at 0)   *)
    (* of WBN_LOOP_PREP, not its post; peel rator TWICE (s039 cold-load fix:    *)
    (* the committed single-rator picked the post, making the implication leg   *)
    (* entry_post ==> prepretail_post which is not a TAUT).                      *)
    EXISTS_TAC (rand(rator(rator(snd(dest_imp(snd(strip_forall(concl WBN_LOOP_PREP)))))))) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[WBN_INV_SPLIT] THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[ARITH_RULE `pc + 0x4a0 = pc + 1184`] THEN CONV_TAC TAUT;
      MP_TAC(SPECL wb_front_vars WBN_LOOP_PREP) THEN
      ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* SESSION-040 -- the OUTPUT-STORE-FORALL augmentation of the prepretail post. *)
(*                                                                            *)
(* GAP found session-040: wbn_prepretail_post (64 conjuncts) DROPS the loop   *)
(* invariant's quantified output-store conjunct                               *)
(*   !j. j < 8*((nblk-9)DIV8 + 1) ==>                                         *)
(*       read (memory :> bytes128 (word_add out_p (word (16*j)))) s =         *)
(*       word_xor (word_xor (bytes_to_int128 (SUB_LIST (16*j,16) ibytes))     *)
(*                (aes13 (gcm_ctr_inc_iter j ctr0) k0..k13)) k14              *)
(* (mainloop.ml:644).  Those are the first 8*(k+1) DECRYPTED output blocks.   *)
(* The Phase-6/7 final per-block output post needs stores for ALL nblk blocks;*)
(* the Phase-6 tail leg (WB_TAIL_r) produces only the last r = nblk-8*(k+1),   *)
(* so the first 8*(k+1) MUST be carried through the seam.  The prepretail      *)
(* region (0x9f0..0xed4) does ZERO output stores (objdump), so the forall      *)
(* passes through the KEEPDATA sim unchanged -- re-proving the prepretail with *)
(* the forall appended to its post closes it by ASM_REWRITE (a genuine         *)
(* preserved read-fact, NOT frame-preservation: ENSURES_ADD_PRESERVED cannot   *)
(* be used because the MAYCHANGE frame permits out_p writes).                  *)
(*                                                                            *)
(* wbn_out_forall = the invariant's output-store forall at i:=k, as a          *)
(* predicate on s (extracted from wbn_loop_inv_core to guarantee it is the     *)
(* SAME term the sim preserves).  wbn_prepretail_post_ext = the 65-conjunct    *)
(* post = wbn_prepretail_post /\ wbn_out_forall.                               *)
(* ------------------------------------------------------------------------- *)

let wbn_out_forall =
  let full = list_mk_comb(wbn_core_applied, [`(nblk - 9) DIV 8`; `s:armstate`]) in
  let inv_cs = conjuncts (rhs(concl (REWRITE_CONV[wbn_loop_inv_core] full))) in
  mk_abs(`s:armstate`, find is_forall inv_cs);;

let wbn_prepretail_post_ext =
  mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs wbn_prepretail_post),
            snd(dest_abs wbn_out_forall)));;

(* WBN_PREPRETAIL_EXT: identical sim to WBN_PREPRETAIL (validated session-040,  *)
(* ~131s) but with the output-store forall appended to the post -- it survives  *)
(* the KEEPDATA sim to s313 and closes by the same ASM_REWRITE tail.  The two   *)
(* Q16/Q19 GHASH conjuncts stay behind the same scoped disclosed CHEAT (the     *)
(* [11] RINNER=LINNER identity).  hyps=0.                                       *)
let wbn_prepretail_ext_goal =
  let kk = `(nblk - 9) DIV 8` in
  let pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0x9f0)`;
      mk_comb(mk_comb(wbn_core_applied,kk),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[pre; wbn_prepretail_post_ext; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_PREPRETAIL_EXT = prove(wbn_prepretail_ext_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (find_term (fun t->match t with Const("byteswap128",_)->true|_->false)) c &&
       can (find_term (fun t->match t with Const("karatsuba_mid",_)->true|_->false)) c
    then STRIP_ASSUME_TAC th else NO_TAC) THEN
  ABBREV_TAC `k = (nblk - 9) DIV 8` THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--1) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (2--2) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q5" "s2" `word (8*k+13):32 word` THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (3--3) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  CTR_INCR_NORM_TAC "s3" 13 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (4--7) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q6" "s7" `word (8*k+14):32 word` THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (8--9) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  CTR_INCR_NORM_TAC "s9" 14 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (10--14) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q7" "s14" `word (8*k+15):32 word` THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (15--120) THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (121--211) THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (212--240) THEN
  (* session-065 Q19 R1' WIRE-IN (was DISCARD_QREGS): step to s242 (the state
     where PL/PH/PM = Q17/Q19/Q18 are all COMPLETE -- PM's final eor3 @0xdb4 is
     instr 242; the s240 the discard used had PM incomplete), ABBREV them opaque,
     then run the reduce KEEPING Q16-Q19 (byteform stays small over PL/PH/PM). *)
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (241--242) THEN
  WBN_Q19_EXTRACT_ABBREV_TAC "s242" THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (243--306) THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (307--313) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM aes13]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE(map GSYM wb_ctr_lanes_thms)) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN
  TRY(W(fun (asl,w) ->
        if can (find_term (fun t -> is_const t && fst(dest_const t) = "ghash_polyval_acc")) w
        then WBN_Q19_PREPRETAIL_CLOSE_TAC `k:num` else NO_TAC)) THEN
  TRY MONOTONE_MAYCHANGE_TAC THEN
  TRY (ASM_REWRITE_TAC[]));;

(* WBN_LOOP_PREP_EXT / WBN_FRONT_TO_PREP_EXT: the EXT-post analogues of          *)
(* WBN_LOOP_PREP / WBN_FRONT_TO_PREP, chaining through WBN_PREPRETAIL_EXT.       *)
(* Same ENSURES_TRANS_SIMPLE / ENSURES_PRECONDITION_THM route (incl. the s039   *)
(* two-rator peel).  Both hyps=0 (validated session-040).                       *)
let wbn_loop_prep_ext_goal =
  let loop_pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0x4a0)`;
      mk_comb(mk_comb(wbn_core_applied,`0`),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[loop_pre; wbn_prepretail_post_ext; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_LOOP_PREP_EXT = prove(wbn_loop_prep_ext_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC (rand(rator(snd(dest_imp(snd(strip_forall(concl WBN_MAIN_LOOP))))))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL wb_front_vars WBN_MAIN_LOOP) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
    MP_TAC(SPECL wb_front_vars WBN_PREPRETAIL_EXT) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC]]);;

let wbn_front_to_prep_ext_goal =
  let ens = list_mk_comb(`ensures arm`,
    [wbn_front_P_tm; wbn_prepretail_post_ext; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_FRONT_TO_PREP_EXT = prove(wbn_front_to_prep_ext_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_entry_post THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL wb_front_vars WBN_LOOP_INVARIANT_ENTRY) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (rand(rator(rator(snd(dest_imp(snd(strip_forall(concl WBN_LOOP_PREP_EXT)))))))) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[WBN_INV_SPLIT] THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[ARITH_RULE `pc + 0x4a0 = pc + 1184`] THEN CONV_TAC TAUT;
      MP_TAC(SPECL wb_front_vars WBN_LOOP_PREP_EXT) THEN
      ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* SESSION-040 -- WBN_Q9_SPEC: the first-tail-block resolver for the seam.     *)
(*                                                                            *)
(* At the prepretail seam (pc+3796) the code has just executed                 *)
(*   ecc:  ldr q9, [x0], #16     (x0 = in_p + 128*(k+1) pre-increment)         *)
(* so the sim carries  read Q9 s313 = read (memory :> bytes128                 *)
(*   (word_add in_p (word (128*(k+1))))) s311  -- a RAW memory read (harvested  *)
(* session-040).  The tail's FIRST instruction eor3 v12,v9,v0,v29 @0xedc reads  *)
(* this Q9 (objdump-confirmed: incoming Q9 is consumed BEFORE any tail reload   *)
(* at 0xfa4), so it MUST reach the tail seam in spec form.  This lemma resolves  *)
(* that raw read to bytes_to_int128 (SUB_LIST (16*8*(k+1),16) ibytes) = the      *)
(* first tail block (global block 8*(k+1)) via INPUT_BYTES_TO_BYTE128_LANES at    *)
(* lane 8*(k+1), given 8*(k+1) < nblk (WBN_Q9_INDEX_LT) and the preserved        *)
(* whole-buffer input-bytes fact.  hyps=0 (session-040).                         *)
(* USE (next session): add read Q9 = <this RHS> to the prepretail post, resolve  *)
(* it in the sim right before ENSURES_FINAL_STATE via                           *)
(*   MP_TAC(SPECL[...] WBN_Q9_SPEC) using the s313 input-bytes fact + the raw    *)
(*   Q9 read (bridge s311->s313 memory equality: no stores 0xecc..0xed4).         *)
(* ------------------------------------------------------------------------- *)
let WBN_Q9_SPEC = prove
 (`!(nblk:num) (in_p:int64) (ibytes:byte list) (k:num) (s:armstate).
     LENGTH ibytes = 16 * nblk /\
     8 * (k + 1) < nblk /\
     read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes
     ==> read (memory :> bytes128 (word_add in_p (word (128 * (k + 1))))) s =
         bytes_to_int128 (SUB_LIST (16 * (8 * (k + 1)),16) ibytes)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s:armstate`]
    INPUT_BYTES_TO_BYTE128_LANES) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_ARITH_TAC;
      SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` SUBST1_TAC THENL
       [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `8 * (k + 1):num`) THEN
    ANTS_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `16 * (8 * (k + 1)) = 128 * (k + 1)`] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th])]]);;

(* ------------------------------------------------------------------------- *)
(* SESSION-043 -- EXT2: prepretail post carrying BOTH the output-store forall  *)
(* (from EXT) AND the incoming Q9 (first tail block, global block 8*(k+1)).    *)
(*                                                                            *)
(* GAP (session-040): besides the output forall (carried by EXT), the tail's   *)
(* FIRST instruction eor3 v12,v9,v0,v29 @0xedc consumes the INCOMING Q9 BEFORE  *)
(* any tail reload (WBN_Q9_SPEC comment) -- so Q9 must reach the seam in spec   *)
(* form.  wbn_prepretail_post_ext2 = wbn_prepretail_post_ext /\ the Q9 conjunct *)
(* (read Q9 s = bytes_to_int128 (SUB_LIST (16 * 8 * ((nblk-9) DIV 8 + 1),16)    *)
(* ibytes), aconv WBN_Q9_SPEC at k := (nblk-9) DIV 8).                          *)
(*                                                                            *)
(* Proof route (session-042 robust alternative, session-043 executed it):       *)
(* the ldr q9,[x0],#16 @0xecc (step 312) carries a RAW s311 memory read; the    *)
(* s311->s313 memory-equality bridge is awkward (no s311 MAYCHANGE -- the frame *)
(* is s0->s313 only).  Instead SPLIT the sim at s311 and resolve Q9 THERE: the  *)
(* whole-buffer input-bytes fact is live at s311 under KEEPDATA, x0@s311 =      *)
(* in_p+128*(k+1) confirmed, so MP_TAC'ing WBN_Q9_SPEC (ANTS by WBN_Q9_INDEX_LT *)
(* + ARITH) plants read(mem:>bytes128(in_p+128*(k+1))) s311 = <spec>; the ldr    *)
(* q9 then auto-resolves Q9 to that spec form via ASM_REWRITE.  Identical sim    *)
(* to WBN_PREPRETAIL_EXT (~131s) otherwise; same scoped Q16/Q19 CHEAT.  hyps=0.  *)
(* ------------------------------------------------------------------------- *)

let wbn_prepretail_post_ext2 =
  mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs wbn_prepretail_post_ext),
            `read Q9 (s:armstate) =
             bytes_to_int128 (SUB_LIST (16 * 8 * ((nblk - 9) DIV 8 + 1),16) ibytes)`));;

let wbn_prepretail_ext2_goal =
  let kk = `(nblk - 9) DIV 8` in
  let pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0x9f0)`;
      mk_comb(mk_comb(wbn_core_applied,kk),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[pre; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_PREPRETAIL_EXT2 = prove(wbn_prepretail_ext2_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (find_term (fun t->match t with Const("byteswap128",_)->true|_->false)) c &&
       can (find_term (fun t->match t with Const("karatsuba_mid",_)->true|_->false)) c
    then STRIP_ASSUME_TAC th else NO_TAC) THEN
  ABBREV_TAC `k = (nblk - 9) DIV 8` THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--1) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (2--2) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q5" "s2" `word (8*k+13):32 word` THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (3--3) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  CTR_INCR_NORM_TAC "s3" 13 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (4--7) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q6" "s7" `word (8*k+14):32 word` THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (8--9) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  CTR_INCR_NORM_TAC "s9" 14 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (10--14) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q7" "s14" `word (8*k+15):32 word` THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (15--120) THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (121--211) THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (212--240) THEN
  (* session-065 Q19 R1' WIRE-IN (was DISCARD_QREGS): step to s242 (the state
     where PL/PH/PM = Q17/Q19/Q18 are all COMPLETE -- PM's final eor3 @0xdb4 is
     instr 242; the s240 the discard used had PM incomplete), ABBREV them opaque,
     then run the reduce KEEPING Q16-Q19 (byteform stays small over PL/PH/PM). *)
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (241--242) THEN
  WBN_Q19_EXTRACT_ABBREV_TAC "s242" THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (243--306) THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (307--311) THEN
  (* Resolve the incoming Q9 at s311 (before the ldr q9 @0xecc = step 312) so   *)
  (* the load auto-resolves it to spec form.  The whole-buffer input-bytes fact  *)
  (* is live at s311 under KEEPDATA; WBN_Q9_INDEX_LT gives 8*(k+1) < nblk.        *)
  MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `k:num`; `s311:armstate`]
    WBN_Q9_SPEC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `nblk:num` WBN_Q9_INDEX_LT) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_TAC] THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (312--313) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM aes13]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE(map GSYM wb_ctr_lanes_thms)) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN
  TRY(W(fun (asl,w) ->
        if can (find_term (fun t -> is_const t && fst(dest_const t) = "ghash_polyval_acc")) w
        then WBN_Q19_PREPRETAIL_CLOSE_TAC `k:num` else NO_TAC)) THEN
  TRY MONOTONE_MAYCHANGE_TAC THEN
  TRY (ASM_REWRITE_TAC[]));;

(* WBN_LOOP_PREP_EXT2 / WBN_FRONT_TO_PREP_EXT2: the EXT2-post analogues,          *)
(* chaining through WBN_PREPRETAIL_EXT2.  Same ENSURES_TRANS_SIMPLE /             *)
(* ENSURES_PRECONDITION_THM route as the EXT versions (incl. the s039 two-rator  *)
(* peel that picks the PRE of WBN_LOOP_PREP_EXT2, not its post).  Both hyps=0.    *)
let wbn_loop_prep_ext2_goal =
  let loop_pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0x4a0)`;
      mk_comb(mk_comb(wbn_core_applied,`0`),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[loop_pre; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_LOOP_PREP_EXT2 = prove(wbn_loop_prep_ext2_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC (rand(rator(snd(dest_imp(snd(strip_forall(concl WBN_MAIN_LOOP))))))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL wb_front_vars WBN_MAIN_LOOP) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
    MP_TAC(SPECL wb_front_vars WBN_PREPRETAIL_EXT2) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC]]);;

let wbn_front_to_prep_ext2_goal =
  let ens = list_mk_comb(`ensures arm`,
    [wbn_front_P_tm; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_FRONT_TO_PREP_EXT2 = prove(wbn_front_to_prep_ext2_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_entry_post THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL wb_front_vars WBN_LOOP_INVARIANT_ENTRY) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (rand(rator(rator(snd(dest_imp(snd(strip_forall(concl WBN_LOOP_PREP_EXT2)))))))) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[WBN_INV_SPLIT] THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[ARITH_RULE `pc + 0x4a0 = pc + 1184`] THEN CONV_TAC TAUT;
      MP_TAC(SPECL wb_front_vars WBN_LOOP_PREP_EXT2) THEN
      ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC]]]);;

(* ========================================================================= *)
(* SESSION-044 -- PHASE 6 STEP 2: the tail leg (WBN_PREP_TO_END).            *)
(*                                                                           *)
(* KEY STRUCTURAL FACT (session-044): wb.ml's WB_TAIL_r_TAC tail proofs      *)
(* already START at pc+3796 -- EXACTLY the EXT2 seam PC -- and drive to      *)
(* pc+4528 (the whole-function exit) CHEAT-FREE (they discharge the r-block  *)
(* GHASH via GMULT{r}_FULL_CORRECT_BA).  prove_band k's back-leg is          *)
(* `WB_PREP_TAC k THEN WB_TAIL_k_TAC`, proving                               *)
(*   ensures arm (q_at k) (band_post k) (band_frame k)                       *)
(* where q_at k = wb_front_postcond @ nblk:=k.  So the tail leg we need is   *)
(* structurally wb.ml's OWN back-leg, in the shifted (post-loop) variables.  *)
(*                                                                           *)
(* STEP 2a -- WB_TAIL_GEN_r: package that back-leg as a standalone           *)
(* universally-quantified lemma, proven from the band precond MINUS the 4    *)
(* cells the EXT2 seam does NOT carry (xi_p, ivec_p, [sp+72], in_p block-0). *)
(* Proving it from the weakened precond DOES the in-proof dropped-cells      *)
(* audit (the human's owed check) AND yields a lemma the EXT2 post can feed  *)
(* by pure precondition-weakening (no re-simulation).                        *)
(* ------------------------------------------------------------------------- *)

(* the band goal split into (vars, hyps, pre, post, frame) *)
let wbn_dissect_band k =
  let g = mk_band_goal k in
  let vars, body = strip_forall g in
  let hyps, ens = dest_imp body in
  let _, args = strip_comb ens in
  (vars, hyps, el 1 args, el 2 args, el 3 args);;

(* the 4 seam cells EXT2 drops -- objdump-confirmed never read by the tail,  *)
(* re-confirmed in-proof by proving WB_TAIL_GEN_r from the precond without   *)
(* them (session-044).  [sp+72]=0 is a pinned artifact; xi_p/ivec_p are      *)
(* consumed only via the pre-seeded Q19/Q16 and Q0..Q7; in_p block-0 arrives *)
(* pre-loaded in Q9 (WBN_Q9_SPEC).                                           *)
let wbn_tail_drop_lhs = [
  `read (memory :> bytes64 (word_add stackpointer (word 72))) (s:armstate)`;
  `read (memory :> bytes128 xi_p) (s:armstate)`;
  `read (memory :> bytes128 ivec_p) (s:armstate)`;
  `read (memory :> bytes128 in_p) (s:armstate)`];;

(* q_at k with the 4 dropped cells removed *)
let wbn_weak_q_at k =
  let cs = conjuncts (snd(dest_abs (q_at k))) in
  let kept = filter (fun c -> not (is_eq c && mem (lhs c) wbn_tail_drop_lhs)) cs in
  mk_abs(`s:armstate`, end_itlist (curry mk_conj) kept);;

(* the generic tail back-leg goal: ensures (weak q_at r) (band_post r) frame *)
let wbn_tail_backleg_goal r =
  let (vars, hyps, pre0, post, frame) = wbn_dissect_band r in
  ignore pre0;
  let ens = list_mk_comb(`ensures arm`, [wbn_weak_q_at r; post; frame]) in
  list_mk_forall(vars, mk_imp(hyps, ens));;

(* r=1 (validated session-044, ~133s): confirms the r=1 tail reads none of   *)
(* the 4 dropped cells.  Tactic = the prove_band back-leg verbatim.          *)
let WB_TAIL_GEN_1 = prove(wbn_tail_backleg_goal 1,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 1 THEN WB_TAIL_1_TAC);;

(* r=8 (validated session-044, ~315s): the HARDEST tail (Q18LATEST window +  *)
(* full Karatsuba merge + WA_UNIFY_BB) -- proving it from the weakened       *)
(* precond confirms even the 8-block GHASH close needs none of the 4 cells.  *)
let WB_TAIL_GEN_8 = prove(wbn_tail_backleg_goal 8,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 8 THEN WB_TAIL_8_TAC);;

(* r=2..7 (validated session-044): same back-leg, all hyps=0.  Timings:      *)
(* r2~166s r3~132s r4~165s r5~200s r6~237s r7~277s.                          *)
let WB_TAIL_GEN_2 = prove(wbn_tail_backleg_goal 2,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 2 THEN WB_TAIL_2_TAC);;
let WB_TAIL_GEN_3 = prove(wbn_tail_backleg_goal 3,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 3 THEN WB_TAIL_3_TAC);;
let WB_TAIL_GEN_4 = prove(wbn_tail_backleg_goal 4,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 4 THEN WB_TAIL_4_TAC);;
let WB_TAIL_GEN_5 = prove(wbn_tail_backleg_goal 5,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 5 THEN WB_TAIL_5_TAC);;
let WB_TAIL_GEN_6 = prove(wbn_tail_backleg_goal 6,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 6 THEN WB_TAIL_6_TAC);;
let WB_TAIL_GEN_7 = prove(wbn_tail_backleg_goal 7,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 7 THEN WB_TAIL_7_TAC);;

(* ========================================================================= *)
(* SESSION-045 -- PHASE 6 STEP 2b: WBN_PREP_TO_END assembly infrastructure.  *)
(*                                                                           *)
(* SOUNDNESS FIX to the (uncommitted) session-044 STEP-2b recipe.  That      *)
(* recipe fed WB_TAIL_GEN_r (which keep X1,X9 in their weak precond) by      *)
(* ENSURES_PRECONDITION_THM from wbn_prepretail_post_ext2, claiming all 20   *)
(* non-aconv conjuncts reconcile "by pure ARITH".  Session-045 FOUND that 2  *)
(* of them are UNDERIVABLE, not ARITH:                                       *)
(*    ext2 delivers  read X1 s = word (128 * nblk),  read X9 s = word (16*nblk) *)
(*    but a SPECL'd tail (in_p:=in_p+128(k+1), nblk-role:=r) wants           *)
(*                    read X1 s = word (128 * r),    read X9 s = word (16*r).  *)
(* For nblk = 8*(k+1)+r >= 17 these differ, so ext2_post ==> shifted_weak_q_at_r *)
(* FAILS on X1/X9 exactly.  objdump: X1,X9 are DEAD in the tail range         *)
(* [0xed4,0x11b0) (0 reads), so the sound fix is to DROP X1,X9 from the tail  *)
(* precond too (6 dropped cells, not 4) and re-prove the tail leg from the    *)
(* 63-conjunct weak precond.  WB_TAIL_GEN2_1 below CONFIRMS the tail sim      *)
(* needs neither (hyps=0, ~133s, identical WB_PREP_TAC r THEN WB_TAIL_r_TAC). *)
(* ------------------------------------------------------------------------- *)

(* num_of_bytelist = num_of_wordlist on byte lists (needed by WBN_INPUT_SLICE). *)
let NUM_OF_BYTELIST_EQ_WORDLIST = prove
 (`!l:byte list. num_of_bytelist l = num_of_wordlist l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[num_of_bytelist; num_of_wordlist; DIMINDEX_8] THEN ARITH_TAC);;

(* Input-read restriction: the whole-buffer read restricts to any 16-byte    *)
(* block boundary 128*(k+1).  This discharges the shifted tail precond's      *)
(* `read (memory :> bytes (in_p+128(k+1),16)) s = num_of_bytelist (SUB_LIST...)` *)
(* conjunct from ext2's `read (memory :> bytes (in_p,16*nblk)) s = ... ibytes`.  *)
(* (session-045, hyps=0).                                                     *)
let WBN_INPUT_SLICE = prove
 (`!(nblk:num) (in_p:int64) (ibytes:byte list) (k:num) (s:armstate).
     LENGTH ibytes = 16 * nblk /\ 8 * (k + 1) < nblk /\
     read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes
     ==> read (memory :> bytes (word_add in_p (word (128 * (k + 1))),16)) s =
         num_of_bytelist (SUB_LIST (128 * (k + 1),16) ibytes)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`in_p:int64`; `16 * nblk`; `128 * (k+1)`; `read memory (s:armstate)`]
    READ_BYTES_DIV) THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes (word_add in_p (word (128 * (k + 1))),16)) s =
     (read (memory :> bytes (word_add in_p (word (128 * (k + 1))),
                             16 * nblk - 128 * (k + 1))) s) MOD 2 EXP (8 * 16)`
   SUBST1_TAC THENL
   [MP_TAC(ISPECL [`word_add in_p (word (128 * (k+1))):int64`;
                   `16 * nblk - 128 * (k+1)`; `16`; `read memory (s:armstate)`]
       READ_BYTES_MOD) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    SUBGOAL_THEN `MIN (16 * nblk - 128 * (k + 1)) 16 = 16` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NUM_OF_BYTELIST_EQ_WORDLIST] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST; DIMINDEX_8] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* Session-047 generalization of WBN_INPUT_SLICE to an arbitrary slice length  *)
(* m (= 16*r):  the r>1 shifted tail reads 16*r input bytes at 128*(k+1), not   *)
(* just 16.  Same proof, m kept symbolic under 128*(k+1)+m <= 16*nblk. hyps=0.  *)
let WBN_INPUT_SLICE_GEN = prove
 (`!(nblk:num) (in_p:int64) (ibytes:byte list) (k:num) (m:num) (s:armstate).
     LENGTH ibytes = 16 * nblk /\ 128 * (k + 1) + m <= 16 * nblk /\
     read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes
     ==> read (memory :> bytes (word_add in_p (word (128 * (k + 1))),m)) s =
         num_of_bytelist (SUB_LIST (128 * (k + 1),m) ibytes)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`in_p:int64`; `16 * nblk`; `128 * (k+1)`; `read memory (s:armstate)`]
    READ_BYTES_DIV) THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes (word_add in_p (word (128 * (k + 1))),m)) s =
     (read (memory :> bytes (word_add in_p (word (128 * (k + 1))),
                             16 * nblk - 128 * (k + 1))) s) MOD 2 EXP (8 * m)`
   SUBST1_TAC THENL
   [MP_TAC(ISPECL [`word_add in_p (word (128 * (k+1))):int64`;
                   `16 * nblk - 128 * (k+1)`; `m:num`; `read memory (s:armstate)`]
       READ_BYTES_MOD) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    SUBGOAL_THEN `MIN (16 * nblk - 128 * (k + 1)) m = m` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NUM_OF_BYTELIST_EQ_WORDLIST] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST; DIMINDEX_8] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* 6-cell drop: the 4 session-044 cells PLUS the dead X1,X9. *)
let wbn_tail_drop_lhs6 = wbn_tail_drop_lhs @
  [`read X1 (s:armstate)`; `read X9 (s:armstate)`];;
let wbn_weak_q_at6 k =
  let cs = conjuncts (snd(dest_abs (q_at k))) in
  let kept = filter (fun c -> not (is_eq c && mem (lhs c) wbn_tail_drop_lhs6)) cs in
  mk_abs(`s:armstate`, end_itlist (curry mk_conj) kept);;
let wbn_tail_backleg_goal6 r =
  let (vars, hyps, pre0, post, frame) = wbn_dissect_band r in
  ignore pre0;
  let ens = list_mk_comb(`ensures arm`, [wbn_weak_q_at6 r; post; frame]) in
  list_mk_forall(vars, mk_imp(hyps, ens));;

(* r=1 VALIDATED session-045 (hyps=0, ~133s): confirms the r=1 tail reads     *)
(* none of the 6 dropped cells (X1/X9 dead as objdump shows).  Same tactic.   *)
let WB_TAIL_GEN2_1 = prove(wbn_tail_backleg_goal6 1,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 1 THEN WB_TAIL_1_TAC);;

(* r=2..8: same back-leg from the 6-cell-drop weak precond (each ~130-315s;  *)
(* WB_TAIL_GEN2_2 validated session-047 at ~165s; the others share the        *)
(* WB_TAIL_r_TAC machinery).  Each hyps=0 IS the per-r X1/X9 dead-cell audit.  *)
let WB_TAIL_GEN2_2 = prove(wbn_tail_backleg_goal6 2,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 2 THEN WB_TAIL_2_TAC);;
let WB_TAIL_GEN2_3 = prove(wbn_tail_backleg_goal6 3,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 3 THEN WB_TAIL_3_TAC);;
let WB_TAIL_GEN2_4 = prove(wbn_tail_backleg_goal6 4,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 4 THEN WB_TAIL_4_TAC);;
let WB_TAIL_GEN2_5 = prove(wbn_tail_backleg_goal6 5,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 5 THEN WB_TAIL_5_TAC);;
let WB_TAIL_GEN2_6 = prove(wbn_tail_backleg_goal6 6,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 6 THEN WB_TAIL_6_TAC);;
let WB_TAIL_GEN2_7 = prove(wbn_tail_backleg_goal6 7,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 7 THEN WB_TAIL_7_TAC);;
let WB_TAIL_GEN2_8 = prove(wbn_tail_backleg_goal6 8,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 8 THEN WB_TAIL_8_TAC);;

(* ------------------------------------------------------------------------- *)
(* WBN_PREP_TO_END_r recipe (VALIDATED for r=1 down to a full close this       *)
(* session; the reconciliation tactic below took ext2_post ==>                *)
(* shifted_weak_q_at6_1 to exactly its 4 trivial residuals -- 3 flags + the    *)
(* input-read -- all now discharged by the helpers above + a per-subgoal       *)
(* WORD_RULE.  Assembly of the ensures theorem itself is owed next session).   *)
(*                                                                           *)
(* shift_vals r (SPECL order = wb_front_vars minus nblk, 27 terms):           *)
(*   [pc; stackpointer;                                                        *)
(*    word_add out_p (word (128*((nblk-9) DIV 8+1)));  xi_p; ivec_p;           *)
(*    word_add in_p (word (128*((nblk-9) DIV 8+1)));   key_p; htbl_p;          *)
(*    SUB_LIST (128*((nblk-9) DIV 8+1), 16*r) ibytes;             (:byte list) *)
(*    word_bytereverse wbn_caught_up;                             (:int128)    *)
(*    gcm_ctr_add (word (8*((nblk-9) DIV 8+1))) ctr0;             (:int128)    *)
(*    k0..k14; h]   -- annotate every ibytes/int128 or SPECL invents tyvars.   *)
(*                                                                           *)
(* WBN_PREP_TO_END_r : ensures arm wbn_prepretail_post_ext2                    *)
(*                       (shifted band_post r) wbn_front_C_tm                   *)
(*   under hyp  nblk = 8*((nblk-9) DIV 8 + 1) + r.  Build via:                  *)
(*   MATCH_MP_TAC ENSURES_FRAME_SUBSUMED (narrow tail frame -> wide ext2 frame  *)
(*     wbn_front_C_tm; SUBSUMED via SUBSUMED_ASSIGNS_BYTES on out_p sub-region  *)
(*     bytes(out_p+128(k+1),16) subsumed bytes(out_p,16*nblk))                  *)
(*   THEN MATCH_MP_TAC ENSURES_PRECONDITION_THM                                 *)
(*     EXISTS_TAC (shifted weak_q_at6 r) THEN CONJ_TAC THENL                     *)
(*     [ <the pre-implication, tactic below>;                                    *)
(*       MP_TAC(SPECL (shift_vals r) WB_TAIL_GEN2_r) THEN ANTS (nonoverlapping/  *)
(*         LENGTH from ext2 wide hyps; SUB_LIST_LENGTH + 16*r<=remaining) ].      *)
(*                                                                           *)
(* PRE-IMPLICATION tactic  (!s. ext2_post s ==> shifted_weak_q_at6_r s), r=1     *)
(* validated to 0 residuals with the helpers:                                   *)
(*   REPEAT GEN_TAC THEN STRIP_TAC THEN                                          *)
(*   ASM_REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE] THEN                          *)
(*   SUBGOAL_THEN `16 * nblk = 128 * ((nblk-9) DIV 8 + 1) + 16*r` ASSUME_TAC     *)
(*     THENL [UNDISCH_TAC `nblk = 8*((nblk-9) DIV 8+1)+r` THEN ARITH_TAC; ALL] THEN *)
(*   -- flags first, BEFORE any CONJ split, so the fact hits all of them:        *)
(*   SUBGOAL_THEN `word_sub (word_add in_p (word (128*((nblk-9)DIV8+1)+16*r)))    *)
(*      (word_add in_p (word (128*((nblk-9)DIV8+1)))):int64 = word (16*r)`        *)
(*     ASSUME_TAC THENL [CONV_TAC WORD_RULE; ALL] THEN  (* r=1: word 16 *)        *)
(*   REWRITE_TAC[GSYM GCM_CTR_ADD_1; GCM_CTR_ADD_COMPOSE] THEN                    *)
(*   REWRITE_TAC[SUB_LIST_MIN_RIGHT; ARITH_RULE `16*8*x=128*x`;                   *)
(*               ARITH_RULE `MIN 16 (16*r)=16` (r>=1)] THEN                       *)
(*   (for the input-read conjunct) MP_TAC(SPECL[...] WBN_INPUT_SLICE) + ANTS THEN *)
(*   UNDISCH `16*nblk=...` THEN DISCH_THEN(fun th->REWRITE_TAC[th]) THEN          *)
(*   ABBREV_TAC `q=(nblk-9) DIV 8` THEN                                          *)
(*   REWRITE_TAC[the `8*q+N=8*(q+1)+(N-8)` (N=8..15) + `((a+1)+..)=a+j` rules] THEN *)
(*   ASM_REWRITE_TAC[] THEN                                                       *)
(*   REPEAT CONJ_TAC THEN                                                         *)
(*   TRY(AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC) THEN      *)
(*   TRY(CONV_TAC WORD_RULE).                                                     *)
(*                                                                           *)
(* Then WBN_PREP_TO_END = 8-way case split on r = 1+(nblk-9) MOD 8 (VALIDATED    *)
(* r in 1..8 for nblk>=17); POST combines the shifted band_post (last r stores + *)
(* xi_p tag) with ext2's carried output forall [conjunct 64] and folds the tag   *)
(* caught_up ++ [last r blocks] = full-nblk GHASH via GHASH_ACC_APPEND           *)
(* (common/polyval_ghash.ml:62) -- the one genuinely NEW algebra step.  THEN     *)
(* chain onto WBN_FRONT_TO_PREP_EXT2 by ENSURES_TRANS_SIMPLE (EXISTS_TAC          *)
(* wbn_prepretail_post_ext2).                                                     *)
(* ------------------------------------------------------------------------- *)

(* ========================================================================= *)
(* SESSION-047 -- PHASE 6 STEP 2b: WBN_PREP_TO_END_r landed (r=1).           *)
(*                                                                           *)
(* The seam post `wbn_prepretail_post_ext2` (the loop/prepretail EXT2 exit    *)
(* at pc+3796) feeds the shifted r-block tail WB_TAIL_GEN2_r by precondition- *)
(* weakening.  WBN_PREP_TO_END_r : ensures arm wbn_prepretail_post_ext2       *)
(* (shifted band_post r) wbn_front_C_tm, under the length hyp                 *)
(*   nblk = 8*((nblk-9) DIV 8 + 1) + r.                                       *)
(*                                                                           *)
(* SOUNDNESS (session-046/047): the r-block tail's own ANTS (NONOVERLAPPING_  *)
(* TAC over the shifted out_p/xi_p/ivec_p regions) needs 3 disjointness       *)
(* clauses the ext2 wide hyps do NOT carry:                                   *)
(*    nonoverlapping (out_p,16*nblk) (xi_p,16)                                *)
(*    nonoverlapping (out_p,16*nblk) (ivec_p,16)                              *)
(*    nonoverlapping (xi_p,16)       (ivec_p,16)                              *)
(* These ARE genuine whole-function preconditions (the output buffer must be  *)
(* disjoint from the Xi accumulator and the ivec; xi_p disjoint from ivec_p)  *)
(* -- same class as the s004 in_p/out_p gap and s015 (out_p)(sp,80) gap.  In  *)
(* the real band contract q_at r, xi_p (out_p,16*r) ivec_p at the size-16     *)
(* (=16*nblk when nblk=1) granularity are present; at the whole-length        *)
(* 16*nblk granularity dissect_band 1 shows only xi_p (ivec_p,16) literally,  *)
(* so session-047 threads all 3 as SIDE-CONDITIONS on WBN_PREP_TO_END_r       *)
(* (reviewer's alternative to widening wbn_front_hyps_wide_tm -- lighter, no  *)
(* chain re-prove).  They flow up to the final theorem's precond and are      *)
(* supplied by the guard/subroutine wrapper (the band contract has them).     *)
(* ------------------------------------------------------------------------- *)

(* SPECL order = wb_front_vars minus nblk, 27 terms; splices the OCaml value  *)
(* wbn_caught_up (NOT a backtick literal -- that would introduce a free var). *)
let shift_vals r =
  let rt = mk_small_numeral r in
  let slice = subst [rt, `r_:num`]
                `SUB_LIST (128 * ((nblk - 9) DIV 8 + 1), 16 * r_) (ibytes:byte list)` in
  let xi_shifted = mk_comb(`word_bytereverse:int128->int128`, wbn_caught_up) in
  [ `pc:num`; `stackpointer:int64`;
    `word_add out_p (word (128 * ((nblk - 9) DIV 8 + 1))):int64`;
    `xi_p:int64`; `ivec_p:int64`;
    `word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1))):int64`;
    `key_p:int64`; `htbl_p:int64`;
    slice; xi_shifted;
    `gcm_ctr_add (word (8 * ((nblk - 9) DIV 8 + 1))) ctr0:int128`;
    `k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;`k5:int128`;`k6:int128`;`k7:int128`;
    `k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;`k12:int128`;`k13:int128`;`k14:int128`;`h:int128`];;

(* the 3 side-condition clauses (whole-length granularity). *)
let wbn_prep_to_end_extra_clauses =
  [`nonoverlapping (out_p:int64,16 * nblk) (xi_p:int64,16)`;
   `nonoverlapping (out_p:int64,16 * nblk) (ivec_p:int64,16)`;
   `nonoverlapping (xi_p:int64,16) (ivec_p:int64,16)`];;

(* WBN_PREP_TO_END_r goal: ext2 seam post -> shifted band_post r, under the   *)
(* length hyp + the 3 side conditions.  tail_r = the WB_TAIL_GEN2_r theorem.  *)
let wbn_prep_to_end_goal r tail_r =
  let tail = SPECL (shift_vals r) tail_r in
  let _,targs = strip_comb (snd(dest_imp(concl tail))) in
  let shifted_post = el 2 targs in
  let nblk_eq = subst[mk_small_numeral r,`r_:num`]
                  `nblk = 8 * ((nblk - 9) DIV 8 + 1) + r_` in
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_wide_tm :: nblk_eq :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_prepretail_post_ext2; shifted_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

(* Parametric reconciliation tactic (session-047, validated r=1..2 live, then  *)
(* r=3..8 by the same shape).  The r>1 cases read 16*r input bytes so use       *)
(* WBN_INPUT_SLICE_GEN (m=16*r) both for the SUB_LIST fold (Q9) and the direct  *)
(* input-read residual; the flags/X4/X5 close after SUBST word_sub=word(16*r);   *)
(* the counter reads fold via GCM_CTR_ADD_1/COMPOSE + a 14-deep AP peel.  Every  *)
(* pre-implication conjunct is closed order-independently by a per-goal FIRST    *)
(* [REFL; WORD_RULE; counter-peel; slice] so leaf count/order never matters.     *)
let WBN_PREP_TO_END_r_TAC r tail_r =
  let rt = mk_small_numeral r in
  let m16r = mk_binop `( * ):num->num->num` `16` rt in
  let mnum = mk_small_numeral (16 * r) in
  let sv = shift_vals r in
  let tail = SPECL sv tail_r in
  let _,targs = strip_comb (snd(dest_imp(concl tail))) in
  let tail_frame = el 3 targs and tail_pre = el 1 targs in
  let slice_close =
    MP_TAC(SPECL [`nblk:num`;`in_p:int64`;`ibytes:byte list`;`q:num`;mnum;`x:armstate`]
             WBN_INPUT_SLICE_GEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE(mk_eq(m16r,mnum))] THEN DISCH_THEN ACCEPT_TAC] in
  let counter_close =
    REPLICATE_TAC 14 AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC WORD_RULE in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC tail_frame THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC tail_pre THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE] THEN
    ABBREV_TAC `q = (nblk - 9) DIV 8` THEN
    SUBGOAL_THEN (subst[rt,`r_:num`] `16 * nblk = 128 * (q + 1) + 16 * r_`)
      ASSUME_TAC THENL
     [UNDISCH_TAC (subst[rt,`r_:num`] `nblk = 8 * (q + 1) + r_`) THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM GCM_CTR_ADD_1; GCM_CTR_ADD_COMPOSE] THEN
    MP_TAC(SPECL [`nblk:num`;`in_p:int64`;`ibytes:byte list`;`q:num`;m16r;`x:armstate`]
      WBN_INPUT_SLICE_GEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    REWRITE_TAC[SUB_LIST_MIN_RIGHT; ARITH_RULE(subst[rt,`r_:num`] `MIN 16 (16 * r_) = 16`);
                ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (subst[rt,`r_:num`]
      `word_sub (word_add in_p (word (128 * (q + 1) + 16 * r_)))
                (word_add in_p (word (128 * (q + 1)))):int64 = word (16 * r_)`)
      SUBST_ALL_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    FIRST [REFL_TAC; CONV_TAC WORD_RULE; counter_close; slice_close];
    MP_TAC tail THEN ANTS_TAC THENL
     [CONJ_TAC THENL
        [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
         ALL_TAC] THEN
      REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NONOVERLAPPING_TAC);
      DISCH_THEN ACCEPT_TAC]];;

let WBN_PREP_TO_END_1 = prove(wbn_prep_to_end_goal 1 WB_TAIL_GEN2_1,
  WBN_PREP_TO_END_r_TAC 1 WB_TAIL_GEN2_1);;
let WBN_PREP_TO_END_2 = prove(wbn_prep_to_end_goal 2 WB_TAIL_GEN2_2,
  WBN_PREP_TO_END_r_TAC 2 WB_TAIL_GEN2_2);;
let WBN_PREP_TO_END_3 = prove(wbn_prep_to_end_goal 3 WB_TAIL_GEN2_3,
  WBN_PREP_TO_END_r_TAC 3 WB_TAIL_GEN2_3);;
let WBN_PREP_TO_END_4 = prove(wbn_prep_to_end_goal 4 WB_TAIL_GEN2_4,
  WBN_PREP_TO_END_r_TAC 4 WB_TAIL_GEN2_4);;
let WBN_PREP_TO_END_5 = prove(wbn_prep_to_end_goal 5 WB_TAIL_GEN2_5,
  WBN_PREP_TO_END_r_TAC 5 WB_TAIL_GEN2_5);;
let WBN_PREP_TO_END_6 = prove(wbn_prep_to_end_goal 6 WB_TAIL_GEN2_6,
  WBN_PREP_TO_END_r_TAC 6 WB_TAIL_GEN2_6);;
let WBN_PREP_TO_END_7 = prove(wbn_prep_to_end_goal 7 WB_TAIL_GEN2_7,
  WBN_PREP_TO_END_r_TAC 7 WB_TAIL_GEN2_7);;
let WBN_PREP_TO_END_8 = prove(wbn_prep_to_end_goal 8 WB_TAIL_GEN2_8,
  WBN_PREP_TO_END_r_TAC 8 WB_TAIL_GEN2_8);;

(* ========================================================================= *)
(* SESSION-048 -- PHASE 6 STEP 2b: tag-fold + output-forall algebra.         *)
(*                                                                           *)
(* The per-r seam lemmas WBN_PREP_TO_END_r land a SHIFTED-band post:          *)
(*   - PC = pc+4528 (whole-function exit)                                     *)
(*   - the LAST r output stores at out_p + 128*(k+1) + 16*i (i<r)             *)
(*   - the tag at xi_p = word_bytereverse (ghash_polyval_acc bh (brev xi)     *)
(*       (MAP brev (list_of_seq cph (8*(k+1)))))  APPENDED with the r new     *)
(*       blocks (double-brev'd running acc + r cph blocks).                    *)
(* They DROP the first 8*(k+1) output stores (the ext2 seam post carries them *)
(* as its conjunct [64] forall).  To get the full-nblk contract we must       *)
(*   (a) carry the ext2 output forall through the r-block tail (its narrow    *)
(*       output frame writes only bytes(out_p+128(k+1),16*r), disjoint from   *)
(*       the first 128*(k+1) bytes -> ENSURES_ADD_PRESERVED, sound), and      *)
(*   (b) fold the tag: caught_up ++ [r new blocks] = list_of_seq cph nblk     *)
(*       via GHASH_ACC_APPEND (the one genuinely NEW algebra step).           *)
(* These helper lemmas do the sim-free list/tag algebra for (b).             *)
(* ------------------------------------------------------------------------- *)

(* list_of_seq splits at any point into a prefix + a shifted suffix. *)
let LIST_OF_SEQ_ADD = prove
 (`!m (f:num->A) n. list_of_seq f (m + n) =
        APPEND (list_of_seq f m) (list_of_seq (\i. f (m + i)) n)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; LIST_OF_SEQ; APPEND; ETA_AX];
    REWRITE_TAC[ADD_CLAUSES; LIST_OF_SEQ; APPEND] THEN
    AP_TERM_TAC THEN ASM_REWRITE_TAC[o_DEF]]);;

(* LIST_OF_SEQ_CLAUSES (in the base) only covers n=0..4; the r-block tag fold      *)
(* needs the explicit expansion up to n=8.  Each proved from the SUC recursion     *)
(* (num_CONV on the count down to a CLAUSES-known value, then APPEND).             *)
let LIST_OF_SEQ_CLAUSES_5_8 =
  let expand_los n =
    let suc_convs = map (fun k -> num_CONV (mk_small_numeral k)) (rev (5--n)) in
    prove(mk_forall(`f:num->A`,
       mk_eq(list_mk_comb(`list_of_seq:(num->A)->num->(A)list`,[`f:num->A`; mk_small_numeral n]),
             mk_list(map (fun i -> mk_comb(`f:num->A`, mk_small_numeral i)) (0--(n-1)), `:A`))),
      GEN_TAC THEN
      GEN_REWRITE_TAC TOP_DEPTH_CONV suc_convs THEN
      REWRITE_TAC[list_of_seq] THEN
      CONV_TAC(DEPTH_CONV NUM_SUC_CONV) THEN
      REWRITE_TAC[LIST_OF_SEQ_CLAUSES] THEN REWRITE_TAC[APPEND]) in
  end_itlist CONJ (map expand_los [5;6;7;8]);;

(* fold one gcm_ctr_inc into the running gcm_ctr_add offset (for the r>1 tail    *)
(* stores' inc^i towers in WBN_PREP_TO_END_FULL_r).                             *)
let GCM_CTR_INC_FOLD = prove
 (`!w x. gcm_ctr_inc (gcm_ctr_add w x) = gcm_ctr_add (word_add w (word 1)) x`,
  REWRITE_TAC[GSYM GCM_CTR_ADD_1; GCM_CTR_ADD_COMPOSE]);;

(* nesting: the shifted band's i-th cph block = the global (8*(k+1)+i)-th. *)
let WBN_SUBLIST_SHIFT = prove
 (`!(ibytes:byte list) k i r. i < r
   ==> SUB_LIST (16 * i,16) (SUB_LIST (128 * (k + 1),16 * r) ibytes) =
       SUB_LIST (16 * (8 * (k + 1) + i),16) ibytes`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUB_LIST_MIN_GENERAL] THEN
  SUBGOAL_THEN `MIN 16 (16 * r - 16 * i) = 16` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `128 * (k + 1) + 16 * i = 16 * (8 * (k + 1) + i)` SUBST1_TAC THENL
   [ARITH_TAC; REFL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* WBN_PREP_TO_END_FULL_r : the seam post fed to the shifted tail, delivering  *)
(* the FULL-nblk output/tag contract (not the r-block band_post).  Post =      *)
(* wbn_end_post: PC=pc+4528, the nblk-uniform output forall (aes13 XOR k14      *)
(* vocabulary, matching the ext2 seam's carried forall), the tag folded to      *)
(* list_of_seq cph nblk via GHASH_ACC_APPEND.                                   *)
(*                                                                             *)
(* Route (session-048): FRAME_SUBSUMED (narrow tail out-frame -> wide           *)
(* wbn_front_C_tm), THEN ENSURES_POSTCONDITION_THM with the intermediate        *)
(*   inter_post_r = \s. (shifted band_post r) s /\ (ext2 first-8(k+1) forall) s  *)
(* splitting into: (1) inter_post_r ==> wbn_end_post [the tag-fold + store       *)
(* re-index math], and (2) ensures ext2post inter_post_r narrow_frame, closed    *)
(* by ENSURES_ADD_PRESERVED [narrow tail leg via INNER_TAIL_FEED_TAC + the       *)
(* first-blocks forall carried by read-over-write through the narrow frame,      *)
(* sound because the tail writes only bytes(out_p+128(k+1),16*r), disjoint       *)
(* from the first 128(k+1) output bytes].                                        *)
(* ------------------------------------------------------------------------- *)

(* the nblk-uniform end post (PC + output forall over nblk + folded tag). *)
let wbn_end_post =
  let end_forall = `forall j. j < nblk
    ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
        word_xor (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16) ibytes))
        (aes13 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13)) k14` in
  let tag = `read (memory :> bytes128 xi_p) s =
    word_bytereverse (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      (MAP word_bytereverse
        (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) nblk)))` in
  mk_abs(`s:armstate`,
    list_mk_conj [`read PC s = word (pc + 4528)`; end_forall; tag]);;

(* full-post goal for a given r *)
let wbn_prep_to_end_full_goal r =
  let nblk_eq = subst[mk_small_numeral r,`r_:num`]
                  `nblk = 8 * ((nblk - 9) DIV 8 + 1) + r_` in
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_wide_tm :: nblk_eq :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_prepretail_post_ext2; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

(* the narrow tail out-frame (writes only the last r output blocks) for shift r. *)
let wbn_tail_gen2 r =
  if r=1 then WB_TAIL_GEN2_1 else if r=2 then WB_TAIL_GEN2_2
  else if r=3 then WB_TAIL_GEN2_3 else if r=4 then WB_TAIL_GEN2_4
  else if r=5 then WB_TAIL_GEN2_5 else if r=6 then WB_TAIL_GEN2_6
  else if r=7 then WB_TAIL_GEN2_7 else WB_TAIL_GEN2_8;;
let wbn_narrow_frame r =
  el 3 (snd(strip_comb(snd(dest_imp(concl(SPECL (shift_vals r) (wbn_tail_gen2 r)))))));;

(* INNER_TAIL_FEED_TAC r tail_r: the post-FRAME_SUBSUMED inner half of           *)
(* WBN_PREP_TO_END_r_TAC (PRECONDITION_THM + feed the shifted tail); proves      *)
(* `ensures ext2post (shifted band_post r) narrow_frame` on its own.            *)
let INNER_TAIL_FEED_TAC r tail_r =
  let rt = mk_small_numeral r in
  let m16r = mk_binop `( * ):num->num->num` `16` rt in
  let mnum = mk_small_numeral (16 * r) in
  let sv = shift_vals r in
  let tail = SPECL sv tail_r in
  let _,targs = strip_comb (snd(dest_imp(concl tail))) in
  let tail_pre = el 1 targs in
  let slice_close =
    MP_TAC(SPECL [`nblk:num`;`in_p:int64`;`ibytes:byte list`;`q:num`;mnum;`x:armstate`]
             WBN_INPUT_SLICE_GEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE(mk_eq(m16r,mnum))] THEN DISCH_THEN ACCEPT_TAC] in
  let counter_close =
    REPLICATE_TAC 14 AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC WORD_RULE in
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC tail_pre THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE] THEN
    ABBREV_TAC `q = (nblk - 9) DIV 8` THEN
    SUBGOAL_THEN (subst[rt,`r_:num`] `16 * nblk = 128 * (q + 1) + 16 * r_`)
      ASSUME_TAC THENL
     [UNDISCH_TAC (subst[rt,`r_:num`] `nblk = 8 * (q + 1) + r_`) THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM GCM_CTR_ADD_1; GCM_CTR_ADD_COMPOSE] THEN
    MP_TAC(SPECL [`nblk:num`;`in_p:int64`;`ibytes:byte list`;`q:num`;m16r;`x:armstate`]
      WBN_INPUT_SLICE_GEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    REWRITE_TAC[SUB_LIST_MIN_RIGHT; ARITH_RULE(subst[rt,`r_:num`] `MIN 16 (16 * r_) = 16`);
                ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (subst[rt,`r_:num`]
      `word_sub (word_add in_p (word (128 * (q + 1) + 16 * r_)))
                (word_add in_p (word (128 * (q + 1)))):int64 = word (16 * r_)`)
      SUBST_ALL_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    FIRST [REFL_TAC; CONV_TAC WORD_RULE; counter_close; slice_close];
    MP_TAC tail THEN ANTS_TAC THENL
     [CONJ_TAC THENL
        [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
         ALL_TAC] THEN
      REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NONOVERLAPPING_TAC);
      DISCH_THEN ACCEPT_TAC]];;

(* r=1 full-post: validated end-to-end interactively (session-048). *)
let WBN_PREP_TO_END_FULL_1 = prove(wbn_prep_to_end_full_goal 1,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC (wbn_narrow_frame 1) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs(el 2 (snd(strip_comb(snd(dest_imp(concl(SPECL (shift_vals 1) WB_TAIL_GEN2_1)))))))),
            el 64 (conjuncts (snd(dest_abs wbn_prepretail_post_ext2)))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ABBREV_TAC `q = (nblk - 9) DIV 8` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `j < 8 * (q + 1)` THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM ACCEPT_TAC;
        SUBGOAL_THEN `j = 8 * (q + 1)` SUBST_ALL_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`; GCM_CTR_INC_ITER_ADD] THEN
        FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
          (match lhs(concl th) with Comb(Comb(Const("read",_),_),_) ->
             (can (find_term (fun t -> t = `aes256_encrypt`)) (concl th)) | _ -> false)
          then SUBST1_TAC th else NO_TAC) THEN
        SUBGOAL_THEN `SUB_LIST (0,16) (SUB_LIST (128 * (q + 1),16 * 1) (ibytes:byte list)) =
                      SUB_LIST (128 * (q + 1),16) ibytes` SUBST1_TAC THENL
         [REWRITE_TAC[SUB_LIST_MIN_RIGHT] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN
        CONV_TAC WORD_RULE];
      REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE] THEN AP_TERM_TAC THEN
      SUBGOAL_THEN
        `list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) (ibytes:byte list))) nblk =
         list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) (8 * (q + 1) + 1)`
        SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[LIST_OF_SEQ_ADD; MAP_APPEND; GHASH_ACC_APPEND] THEN AP_TERM_TAC THEN
      REWRITE_TAC[LIST_OF_SEQ_CLAUSES; MAP; MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[SUB_LIST_MIN_RIGHT; ARITH_RULE `MIN 16 16 = 16`;
                  ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`]];
    MATCH_MP_TAC ENSURES_ADD_PRESERVED THEN CONJ_TAC THENL
     [INNER_TAIL_FEED_TAC 1 WB_TAIL_GEN2_1;
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE; SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
      CONV_TAC(REDEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM] THEN
      CONV_TAC(REDEPTH_CONV BETA_CONV) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
        (match rhs(concl th) with Var("s'",_) -> true | _ -> false))) THEN
      SUBGOAL_THEN `nonoverlapping (word_add out_p (word (16 * j)):int64,16)
         (word_add out_p (word (128 * ((nblk - 9) DIV 8 + 1))),16)` ASSUME_TAC THENL
       [NONOVERLAPPING_TAC; ALL_TAC] THEN
      WBN_PUSH_LHS_READ_TAC THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) then MATCH_MP_TAC th else NO_TAC) THEN
      FIRST_X_ASSUM ACCEPT_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* SESSION-049 -- r>1 generalization of WBN_PREP_TO_END_FULL_1, MECHANIZED.    *)
(*                                                                             *)
(* WBN_PREP_TO_END_FULL_r for r=2..8 has the IDENTICAL skeleton as FULL_1;     *)
(* the r-dependent hand-parts are packaged as OCaml `int -> tactic` closures   *)
(* below and driven by WBN_PREP_TO_END_FULL_r_TAC.  Validated r=2..8 hyps=0.   *)
(*                                                                             *)
(* KEY per-block algebra: for output block j = 8*(q+1)+i (0<=i<r), the         *)
(* seam-carried full-post value equals the r-block band store.  block_bridge   *)
(* proves that value identity STANDALONE (goal-form word_xor(word_xor cph      *)
(* aes13)k14 = store-form word_xor cph (aes256_encrypt ...)), reconciling:     *)
(*   - counter: gcm_ctr_inc_iter(8(q+1)+i) = gcm_ctr_add(word(8(q+1)+i)) =     *)
(*              gcm_ctr_inc^i (gcm_ctr_add(word 8(q+1)))  [GCM_CTR_INC_FOLD]    *)
(*   - cph slice: SUB_LIST(16*(8(q+1)+i),16) ibytes =                          *)
(*              SUB_LIST(16*i,16)(SUB_LIST(128(q+1),16*r) ibytes) [WBN_SUBLIST_SHIFT] *)
(*   - AES: GSYM AES256_XOR_ENCRYPT_RECONSTRUCT + WORD_RULE (XOR reassoc).     *)
(* block_close then reduces 16*i -> numeral (ARITH mul_red -- else the goal's  *)
(* SUB_LIST(16*i,..)/word(16*i) won't match the store's SUB_LIST(<16i>,..)/    *)
(* word <16i>) and reconciles the store address (i=0 flat, i>=1 nested).       *)
(* tag_fold folds the r-element explicit tag list to list_of_seq via           *)
(* LIST_OF_SEQ_ADD/GHASH_ACC_APPEND, closing each element by WBN_SUBLIST_SHIFT. *)
(* ------------------------------------------------------------------------- *)

(* the goal-side and store-side counter for output block i (0<=i<r). *)
let wbn_full_goal_ctr i =
  subst[mk_small_numeral i,`i_:num`]
    `gcm_ctr_add (word (8 * (q + 1) + i_)) ctr0 :int128`;;
let wbn_full_store_ctr i =
  funpow i (fun t -> mk_comb(`gcm_ctr_inc:int128->int128`, t))
    `gcm_ctr_add (word (8 * (q + 1))) ctr0 :int128`;;
(* the goal-side and store-side output addresses for block i. *)
let wbn_full_goal_addr i =
  subst[mk_small_numeral i,`i_:num`]
    `word_add out_p (word (16 * (8 * (q + 1) + i_))):int64`;;
let wbn_full_store_addr i =
  if i = 0 then `word_add out_p (word (128 * (q + 1))):int64`
  else mk_comb(mk_comb(`word_add:int64->int64->int64`,
                       `word_add out_p (word (128 * (q + 1))):int64`),
               mk_comb(`word:num->int64`, mk_small_numeral(16 * i)));;

(* the standalone per-block value bridge goal + tactic. *)
let wbn_block_bridge_goal r i =
  let it = mk_small_numeral i and rt = mk_small_numeral r in
  let gcph = subst[it,`i_:num`]
    `bytes_to_int128 (SUB_LIST (16 * (8 * (q + 1) + i_),16) (ibytes:byte list))` in
  let gval = list_mk_comb(`word_xor:int128->int128->int128`,
    [list_mk_comb(`word_xor:int128->int128->int128`,
       [gcph; list_mk_comb(`aes13`,[wbn_full_goal_ctr i;
          `k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;`k5:int128`;`k6:int128`;
          `k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;`k12:int128`;`k13:int128`])]);
     `k14:int128`]) in
  let scph = subst[it,`i_:num`;rt,`r_:num`]
    `bytes_to_int128 (SUB_LIST (16 * i_,16) (SUB_LIST (128 * (q + 1),16 * r_) (ibytes:byte list)))` in
  let sval = list_mk_comb(`word_xor:int128->int128->int128`,
    [scph; list_mk_comb(`aes256_encrypt`,
       [wbn_full_store_ctr i;
        `[k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]:(int128)list`])]) in
  mk_forall(`q:num`, mk_imp(subst[it,`i_:num`;rt,`r_:num`] `i_ < r_`, mk_eq(gval,sval)));;

let wbn_block_bridge_tac r i =
  let it = mk_small_numeral i and rt = mk_small_numeral r in
  let sublist_inst = SPECL [`ibytes:byte list`;`q:num`;it;rt] WBN_SUBLIST_SHIFT in
  let ctr_eq = mk_eq(wbn_full_goal_ctr i, wbn_full_store_ctr i) in
  GEN_TAC THEN DISCH_TAC THEN
  (MP_TAC sublist_inst THEN ANTS_TAC THENL [ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
  SUBGOAL_THEN ctr_eq SUBST1_TAC THENL
   [REWRITE_TAC[GCM_CTR_INC_FOLD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE;;

(* close one output block j = 8*(q+1)+i in the case-2 forall of FULL_r. *)
let wbn_block_close_tac r i =
  let brg = SPEC `q:num` (prove(wbn_block_bridge_goal r i, wbn_block_bridge_tac r i)) in
  let it = mk_small_numeral i in
  let mul_red = ARITH_RULE (mk_eq(mk_binop `( * ):num->num->num` `16` it,
                                  mk_small_numeral(16 * i))) in
  let common = REWRITE_TAC[GCM_CTR_INC_ITER_ADD] THEN
    MP_TAC brg THEN (ANTS_TAC THENL [ARITH_TAC; ALL_TAC]) THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[mul_red] in
  if i = 0 then
    common THEN
    REWRITE_TAC[ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`; MULT_CLAUSES; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[]
  else
    let addr_eq = mk_eq(wbn_full_goal_addr i, wbn_full_store_addr i) in
    let addr_arith = subst[it,`i_:num`]
      `16 * (8 * (q + 1) + i_) = 128 * (q + 1) + 16 * i_` in
    common THEN
    SUBGOAL_THEN addr_eq SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE addr_arith; mul_red] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    FIRST_X_ASSUM ACCEPT_TAC;;

(* (A) the case-2 output forall for shift r. *)
let wbn_case2_forall_tac r =
  let one_block i =
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> match concl th with
      Comb(Comb(Const("=",_),Var("j",_)),_) -> true | _ -> false)) THEN
    wbn_block_close_tac r i in
  let disj = end_itlist (fun a b -> mk_disj(a,b))
    (map (fun i -> subst[mk_small_numeral i,`i_:num`] `j = 8 * (q + 1) + i_`) (0--(r-1))) in
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_CASES_TAC `j < 8 * (q + 1)` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN disj STRIP_ASSUME_TAC THENL
     ((UNDISCH_TAC (subst[mk_small_numeral r,`r_:num`] `nblk = 8 * (q + 1) + r_`) THEN
       UNDISCH_TAC `~(j < 8 * (q + 1))` THEN UNDISCH_TAC `j < nblk` THEN ARITH_TAC) ::
      map one_block (0--(r-1)))];;

(* (B) the tag fold: r-element explicit tag list -> list_of_seq cph nblk. *)
let wbn_tag_elt_close r i =
  let mul_red = ARITH_RULE (mk_eq(mk_binop `( * ):num->num->num` `16` (mk_small_numeral i),
                                  mk_small_numeral(16 * i))) in
  MP_TAC(REWRITE_RULE[mul_red; MULT_CLAUSES]
           (SPECL [`ibytes:byte list`;`q:num`;mk_small_numeral i;mk_small_numeral r]
              WBN_SUBLIST_SHIFT)) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN MATCH_ACCEPT_TAC];;
let wbn_tag_fold_tac r =
  let rt = mk_small_numeral r in
  AP_TERM_TAC THEN
  SUBGOAL_THEN (subst[rt,`r_:num`]
     `list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) (ibytes:byte list))) nblk =
      list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) (8 * (q + 1) + r_)`)
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIST_OF_SEQ_ADD; MAP_APPEND; GHASH_ACC_APPEND] THEN
  REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE] THEN AP_TERM_TAC THEN
  REWRITE_TAC[LIST_OF_SEQ_CLAUSES; LIST_OF_SEQ_CLAUSES_5_8; MAP; o_DEF] THEN
  REWRITE_TAC[CONS_11] THEN
  (if r = 1 then ALL_TAC else REPEAT CONJ_TAC) THEN
  FIRST (map (fun i -> AP_TERM_TAC THEN AP_TERM_TAC THEN wbn_tag_elt_close r i) (0--(r-1)));;

(* the full FULL_r tactic (r>=1): FRAME_SUBSUMED -> POSTCONDITION_THM with        *)
(* intermediate (shifted band_post /\ ext2 first-8(k+1) forall), split into        *)
(* [ (A) case-2 forall + (B) tag fold ] and [ ADD_PRESERVED: INNER_TAIL_FEED +     *)
(* carry the forall through the narrow tail writes ].                              *)
(* the intermediate post: shifted band_post r (of the SPECL'd tail) conjoined     *)
(* with the ext2 seam's first-8(k+1)-out-blocks forall (conjunct 64).             *)
let wbn_full_inter_post r =
  let band_post_r =
    el 2 (snd(strip_comb(snd(dest_imp(concl(SPECL (shift_vals r) (wbn_tail_gen2 r))))))) in
  mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs band_post_r),
            el 64 (conjuncts (snd(dest_abs wbn_prepretail_post_ext2)))));;
let WBN_PREP_TO_END_FULL_r_TAC r =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC (wbn_narrow_frame r) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (wbn_full_inter_post r) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ABBREV_TAC `q = (nblk - 9) DIV 8` THEN
    CONJ_TAC THENL [wbn_case2_forall_tac r; wbn_tag_fold_tac r];
    MATCH_MP_TAC ENSURES_ADD_PRESERVED THEN CONJ_TAC THENL
     [INNER_TAIL_FEED_TAC r (wbn_tail_gen2 r);
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE; SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
      CONV_TAC(REDEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM] THEN
      CONV_TAC(REDEPTH_CONV BETA_CONV) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
        (match rhs(concl th) with Var("s'",_) -> true | _ -> false))) THEN
      SUBGOAL_THEN (subst[mk_small_numeral r,`r_:num`]
        `nonoverlapping (word_add out_p (word (16 * j)):int64,16)
         (word_add out_p (word (128 * ((nblk - 9) DIV 8 + 1))),16 * r_)`) ASSUME_TAC THENL
       [NONOVERLAPPING_TAC; ALL_TAC] THEN
      WBN_PUSH_LHS_READ_TAC THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) then MATCH_MP_TAC th else NO_TAC) THEN
      FIRST_X_ASSUM ACCEPT_TAC]];;

(* r=2..8 full-post legs (session-049, each hyps=0, ~49s).  r=1 is FULL_1 above. *)
let WBN_PREP_TO_END_FULL_2 = prove(wbn_prep_to_end_full_goal 2, WBN_PREP_TO_END_FULL_r_TAC 2);;
let WBN_PREP_TO_END_FULL_3 = prove(wbn_prep_to_end_full_goal 3, WBN_PREP_TO_END_FULL_r_TAC 3);;
let WBN_PREP_TO_END_FULL_4 = prove(wbn_prep_to_end_full_goal 4, WBN_PREP_TO_END_FULL_r_TAC 4);;
let WBN_PREP_TO_END_FULL_5 = prove(wbn_prep_to_end_full_goal 5, WBN_PREP_TO_END_FULL_r_TAC 5);;
let WBN_PREP_TO_END_FULL_6 = prove(wbn_prep_to_end_full_goal 6, WBN_PREP_TO_END_FULL_r_TAC 6);;
let WBN_PREP_TO_END_FULL_7 = prove(wbn_prep_to_end_full_goal 7, WBN_PREP_TO_END_FULL_r_TAC 7);;
let WBN_PREP_TO_END_FULL_8 = prove(wbn_prep_to_end_full_goal 8, WBN_PREP_TO_END_FULL_r_TAC 8);;

(* ------------------------------------------------------------------------- *)
(* WBN_PREP_TO_END (session-049): the 8-way case split on r = 1+(nblk-9) MOD 8. *)
(* From the ext2 seam post to the full nblk-uniform wbn_end_post, under         *)
(* 9 <= nblk + the 3 side-conditions.  Each residue rr in {0..7} dispatches to   *)
(* WBN_PREP_TO_END_FULL_(rr+1); the per-branch length hyp                        *)
(* nblk = 8*((nblk-9)DIV 8 + 1) + (rr+1) follows by ARITH from the DIVISION      *)
(* identity + 9 <= nblk.                                                         *)
(* ------------------------------------------------------------------------- *)

let wbn_full_thm = Array.of_list
  [WBN_PREP_TO_END_FULL_1;  (* index 0 unused-ish; use r directly 1..8 *)
   WBN_PREP_TO_END_FULL_1; WBN_PREP_TO_END_FULL_2; WBN_PREP_TO_END_FULL_3;
   WBN_PREP_TO_END_FULL_4; WBN_PREP_TO_END_FULL_5; WBN_PREP_TO_END_FULL_6;
   WBN_PREP_TO_END_FULL_7; WBN_PREP_TO_END_FULL_8];;

let wbn_prep_to_end_goal_final =
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_wide_tm :: `9 <= nblk` :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_prepretail_post_ext2; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

let WBN_PREP_TO_END = prove(wbn_prep_to_end_goal_final,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `nblk - 9` (MATCH_MP DIVISION (ARITH_RULE `~(8 = 0)`))) THEN
  ABBREV_TAC `rr = (nblk - 9) MOD 8` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `rr < 8` then MP_TAC th else NO_TAC) THEN
  REWRITE_TAC[ARITH_RULE
    `rr < 8 <=> rr = 0 \/ rr = 1 \/ rr = 2 \/ rr = 3 \/
                rr = 4 \/ rr = 5 \/ rr = 6 \/ rr = 7`] THEN
  STRIP_TAC THEN
  FIRST (map (fun r ->
    MATCH_MP_TAC wbn_full_thm.(r) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `nblk - 9 = (nblk - 9) DIV 8 * 8 + rr` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `9 <= nblk` THEN ARITH_TAC) (1--8)));;

(* ------------------------------------------------------------------------- *)
(* WBN_FRONT_TO_END (session-049): the full nblk>8 (nblk>=17) front->exit       *)
(* chain, pc+0x20 -> pc+4528.  WBN_FRONT_TO_PREP_EXT2 ; WBN_PREP_TO_END via     *)
(* ENSURES_TRANS_SIMPLE (both share frame wbn_front_C_tm, and the seam post      *)
(* wbn_prepretail_post_ext2 is aconv between them).  Precond = wbn_front_P_tm    *)
(* (the PC-free front core), post = wbn_end_post (nblk-uniform output forall +   *)
(* GHASH_ACC_APPEND-folded tag over list_of_seq cph nblk).  The 3 side-conds     *)
(* ride the antecedent outward (WBN_PREP_TO_END needs them; the front leg does   *)
(* not); 9<=nblk from 17<=nblk by ARITH.  hyps=0, no new CHEAT (the 2 scoped     *)
(* Q19/Q16 identity CHEATs remain buried in the loop body + prepretail).        *)
(* ------------------------------------------------------------------------- *)

let wbn_front_to_end_goal =
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_wide_tm :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_front_P_tm; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

let WBN_FRONT_TO_END = prove(wbn_front_to_end_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_prepretail_post_ext2 THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    MATCH_MP_TAC WBN_FRONT_TO_PREP_EXT2 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WBN_PREP_TO_END THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `17 <= nblk` THEN ARITH_TAC]);;

(* ========================================================================= *)
(* SESSION-050 -- the nblk 9..16 leg (the loop is NEVER entered).             *)
(*                                                                           *)
(* For 9 <= nblk <= 16: q = (nblk-9) DIV 8 = 0, and d = 128*((nblk-1) DIV 8) *)
(* = 128 (CONSTANT, since (nblk-1) DIV 8 = 1 across 9..16).  So at the loop- *)
(* skip branch 0x49c (b.ge 0x9f0) we have X0 = in_p+128 == X5 = in_p+128, so *)
(* the b.ge is TAKEN -> control goes STRAIGHT to prepretail 0x9f0; the main   *)
(* loop body is never executed.  (For nblk>=17, d>=256 so X0<X5 and the b.ge  *)
(* falls through into the loop head 0x4a0 -- that is WBN_FRONT_TO_END's path.) *)
(*                                                                           *)
(* The 9..16 leg is therefore a pure straight-line chain:                     *)
(*   FRONT (0x20 -> 0x9f0, b.ge@0x49c TAKEN)  [WBN_FRONT_TO_PREP_916]          *)
(*   ; PREPRETAIL (0x9f0 -> pc+3796, k:=0)    [WBN_PREPRETAIL_EXT2_916]        *)
(*   ; PREP_TO_END (pc+3796 -> pc+4528)       [WBN_PREP_TO_END_916]            *)
(* The FRONT and PREPRETAIL sims are the SAME code as the >=17 versions, only  *)
(* the hyp band (17<=nblk -> 9<=nblk /\ nblk<=16) and the 0x49c branch         *)
(* resolution differ; every register/memory read is IDENTICAL (the branch     *)
(* only changes PC).  PREP_TO_END is symbolic in q (covers q=0).              *)
(* ------------------------------------------------------------------------- *)

(* the 9..16 hyp band: wbn_front_hyps_wide_tm with 17<=nblk -> 9<=nblk/\nblk<=16 *)
let wbn_front_hyps_916_tm =
  let rec repl t = match t with
    | Comb(Comb(Const("/\\",_),a),b) -> mk_conj(repl a, repl b)
    | _ -> if t = `17 <= nblk` then `9 <= nblk /\ nblk <= 16` else t in
  repl wbn_front_hyps_wide_tm;;

(* (nblk-1) DIV 8 = 1 for 9..16  ->  the loop-skip pointer d = 128*1 = 128. *)
let DIV8_916 = prove
 (`!nblk. 9 <= nblk /\ nblk <= 16 ==> (nblk - 1) DIV 8 = 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL[`nblk - 1`;`8`] DIVISION) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* index bound for the first-tail-block lane, 9<= variant (8*k+8 < nblk, k=0 here). *)
let WBN_Q9_INDEX_LT_9 = prove
 (`!nblk. 9 <= nblk /\ 128 * nblk < 2 EXP 62 ==> 8 * ((nblk - 9) DIV 8) + 8 < nblk`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL[`nblk - 9`;`8`] DIVISION) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = (nblk - 9) DIV 8` THEN ASM_ARITH_TAC);;

(* 0x42c b.ge (loop-entry test, X0=in_p<X5): FALLS THROUGH for 9..16 too. *)
let WB_LOOPENTER_FLAGS_916 = prove
 (`!(in_p:int64) nblk. 9 <= nblk /\ nblk <= 16 /\ 128 * nblk < 2 EXP 62 /\
        val in_p + 16 * nblk < 2 EXP 63
    ==> (ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) < &0 <=> T) /\
        (ival in_p - ival (word_add (word (128 * (nblk - 1) DIV 8)) in_p) =
         ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) <=> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `nblk:num` DIV8_916) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
  ABBREV_TAC `d = 128` THEN
  SUBGOAL_THEN `1 <= d /\ d <= 16 * nblk /\ d <= 2 EXP 63` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MP_TAC(ASSUME `9 <= nblk`) THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub p (word_add (word d) p):int64 = word_neg (word d)`] THEN
  ASM_SIMP_TAC[IVAL_NEG_SMALL] THEN
  SUBGOAL_THEN `word_add (word d) in_p:int64 = word_add in_p (word d)` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `ival (word_add in_p (word d):int64) = &(val in_p + d)` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_PTR_ADD THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ival (in_p:int64) = &(val in_p)` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_SMALL_PTR THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `--(&d):int < &0 <=> &0:int < &d`; INT_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC]);;

(* 9..16 versions of the front-prefix arith/lane tactics (NBLK_ARITH_TAC hardcodes
   17<=nblk; these mirror the shape with the 9..16 band). *)
let NBLK_ARITH_916_TAC =
  MP_TAC(ASSUME `9 <= nblk`) THEN MP_TAC(ASSUME `nblk <= 16`) THEN
  MP_TAC(ASSUME `128 * nblk < 2 EXP 62`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

let WBN_FRONT_PREP_BUF_916_TAC =
  SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 in_p) s0 = bytes_to_int128 (SUB_LIST (0,16) ibytes)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`] INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
    ANTS_TAC THENL [NBLK_ARITH_916_TAC; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)` ASSUME_TAC THENL
   [MATCH_MP_TAC USHR_128NBLK_ANY THEN NBLK_ARITH_916_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word_sub (word (16 * nblk)) (word 1)) (word 18446744073709551488):int64 = word (128 * ((nblk - 1) DIV 8))` ASSUME_TAC THENL
   [MATCH_MP_TAC AND_MASK_16NBLK_ANY THEN NBLK_ARITH_916_TAC; ALL_TAC];;

let WBN_LANES_916_TAC =
  SUBGOAL_THEN
   `!k. k < 8 ==> read (memory :> bytes128 (word_add in_p (word (16 * k)))) s0 =
                  bytes_to_int128 (SUB_LIST (16 * k, 16) (ibytes:byte list))`
   MP_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`]
      INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN(fun lth -> X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `k:num` lth) THEN ANTS_TAC THENL
       [MP_TAC(ASSUME `k < 8`) THEN NBLK_ARITH_916_TAC; REWRITE_TAC[]]);
    DISCH_THEN(fun lth ->
      EVERY(map (fun i ->
        ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)
          (MP (SPEC (mk_small_numeral i) lth)
              (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral i) `8`)))))
        (0--7)))];;

let wbn_init_916_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check(is_conj o concl)) THEN
  WBN_FRONT_PREP_BUF_916_TAC;;

(* 0x42c resolve (fall-through) via WB_LOOPENTER_FLAGS_916. *)
let WBN_RESOLVE_42C_916_TAC : tactic =
  MP_TAC(SPECL [`in_p:int64`; `nblk:num`] WB_LOOPENTER_FLAGS_916) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]));;

(* 0x49c resolve (b.ge TAKEN, d=128): substitute (nblk-1)DIV8=1, then WB_PTRCMP_FLAGS
   with a=d=128 collapses 128<128 to F in the assumptions. *)
let WBN_RESOLVE_49C_916_TAC : tactic = fun (asl,w) ->
  (MP_TAC(SPEC `nblk:num` DIV8_916) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                        REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
   MP_TAC(SPECL [`in_p:int64`; `128`; `128`] WB_PTRCMP_FLAGS) THEN
   ANTS_TAC THENL
    [CONJ_TAC THEN MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN
     MP_TAC(ASSUME `9 <= nblk`) THEN ARITH_TAC;
     ALL_TAC] THEN
   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(128 < 128) <=> F`;
                               ARITH_RULE `128 * 1 = 128`])) (asl,w);;

(* the full front-916 sim: prefix IDENTICAL to WBN_FRONT_FULL_TAC to s287, then
   0x49c resolved TAKEN, step 288 lands at 0x9f0. *)
let WBN_FRONT_916_FULL_TAC =
  wbn_init_916_tac THEN WBN_LANES_916_TAC THEN WBN_FRONT_STEP_TAC THEN
  WBN_RESOLVE_42C_916_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (260--260) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_STALE_Q30_TAC) (261--287)) THEN
  WBN_RESOLVE_49C_916_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (288--288);;

(* invariant-establishment closer at s288 (mirror of WBN_LOOP_INVARIANT_ENTRY branch 1). *)
let ENTRY_CLOSER_916 =
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[wbn_loop_inv_core] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
  REWRITE_TAC[GCM_CTR_INC_ITER_ADD; GCM_CTR_ADD_1; GSYM GCM_CTR_ADD_LANES] THEN
  REWRITE_TAC[list_of_seq; MAP; ghash_polyval_acc] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES;
     GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES; GCM_CTR_INC5_LANES;
     GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
  REWRITE_TAC[GCM_CTR_ADD_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM GCM_CTR_ADD_LANES; GCM_CTR_ADD_0] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[GCM_CTR_ADD_0] THEN
  REWRITE_TAC[gcm_ctr_raw_def;
    WORD_RULE `word_add (word_add (x:32 word) (word 12)) (word 1) =
               word_add x (word 13)`;
    WORD_ADD_0];;

(* postcond target for the front-916 leg = wbn_core_applied 0 at PC 0x9f0. *)
let wbn_entry_post_916 =
  mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0x9f0)`;
      mk_comb(mk_comb(wbn_core_applied,`0:num`),`s:armstate`)]);;

let wbn_front_to_prep_916_goal =
  let ens = list_mk_comb(`ensures arm`,[wbn_front_P_tm; wbn_entry_post_916; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_916_tm, ens));;

(* FRONT-916: front sim 0x20 -> 0x9f0, b.ge@0x49c TAKEN, lands at wbn_core_applied 0. *)
let WBN_FRONT_TO_PREP_916 = prove(wbn_front_to_prep_916_goal,
  WBN_FRONT_916_FULL_TAC THEN
  wb_front_fold_tac THEN
  ENTRY_CLOSER_916 THEN
  MP_TAC(SPECL [`in_p:int64`; `128`; `128`] WB_PTRCMP_FLAGS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN
    MP_TAC(ASSUME `9 <= nblk`) THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ARITH_RULE `(128 < 128) <=> F`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[htable_mem_dec] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[];
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC]);;

(* PREPRETAIL-916: identical to WBN_PREPRETAIL_EXT2 but with the 9..16 band and
   WBN_Q9_INDEX_LT_9 (the only 17<=nblk step).  Same scoped Q16/Q19 CHEAT. *)
let wbn_prepretail_ext2_916_goal =
  let kk = `(nblk - 9) DIV 8` in
  let pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0x9f0)`;
      mk_comb(mk_comb(wbn_core_applied,kk),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[pre; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_916_tm, ens));;

let WBN_PREPRETAIL_EXT2_916 = prove(wbn_prepretail_ext2_916_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (find_term (fun t->match t with Const("byteswap128",_)->true|_->false)) c &&
       can (find_term (fun t->match t with Const("karatsuba_mid",_)->true|_->false)) c
    then STRIP_ASSUME_TAC th else NO_TAC) THEN
  ABBREV_TAC `k = (nblk - 9) DIV 8` THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--1) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (2--2) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q5" "s2" `word (8*k+13):32 word` THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (3--3) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  CTR_INCR_NORM_TAC "s3" 13 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (4--7) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q6" "s7" `word (8*k+14):32 word` THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (8--9) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  CTR_INCR_NORM_TAC "s9" 14 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (10--14) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q7" "s14" `word (8*k+15):32 word` THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (15--120) THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (121--211) THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (212--240) THEN
  (* session-065 Q19 R1' WIRE-IN (was DISCARD_QREGS): step to s242 (the state
     where PL/PH/PM = Q17/Q19/Q18 are all COMPLETE -- PM's final eor3 @0xdb4 is
     instr 242; the s240 the discard used had PM incomplete), ABBREV them opaque,
     then run the reduce KEEPING Q16-Q19 (byteform stays small over PL/PH/PM). *)
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (241--242) THEN
  WBN_Q19_EXTRACT_ABBREV_TAC "s242" THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (243--306) THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (307--311) THEN
  MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `k:num`; `s311:armstate`]
    WBN_Q9_SPEC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `nblk:num` WBN_Q9_INDEX_LT_9) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_TAC] THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (312--313) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM aes13]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE(map GSYM wb_ctr_lanes_thms)) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN
  TRY(W(fun (asl,w) ->
        if can (find_term (fun t -> is_const t && fst(dest_const t) = "ghash_polyval_acc")) w
        then WBN_Q19_PREPRETAIL_CLOSE_TAC `k:num` else NO_TAC)) THEN
  TRY MONOTONE_MAYCHANGE_TAC THEN
  TRY (ASM_REWRITE_TAC[]));;

(* FRONT-916 ; PREPRETAIL-916 composed to the ext2 seam (pc+0x20 -> pc+3796).       *)
(* The PRECONDITION bridge collapses (nblk-9)DIV8 to 0 (q=0 for 9..16), matching     *)
(* the front-916 postcond (wbn_core_applied 0) to the prepretail-916 precond.        *)
let wbn_front_to_prep_ext2_916_goal =
  let ens = list_mk_comb(`ensures arm`,
    [wbn_front_P_tm; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_916_tm, ens));;

let WBN_FRONT_TO_PREP_EXT2_916 = prove(wbn_front_to_prep_ext2_916_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_entry_post_916 THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_TO_PREP_916 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (rand(rator(rator(snd(dest_imp(snd(strip_forall(concl WBN_PREPRETAIL_EXT2_916)))))))) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      SUBGOAL_THEN `(nblk - 9) DIV 8 = 0` SUBST1_TAC THENL
       [MP_TAC(SPECL[`nblk - 9`;`8`] DIVISION) THEN ASM_ARITH_TAC;
        DISCH_THEN(fun th -> ACCEPT_TAC th)];
      MATCH_MP_TAC WBN_PREPRETAIL_EXT2_916 THEN ASM_REWRITE_TAC[]]]);;

(* WBN_PREP_TO_END_916: pc+3796 -> pc+4528 for the 9..16 band.  Same 8-way r split *)
(* as WBN_PREP_TO_END but with the 9..16 hyp band; dispatches to the FULL_916_r     *)
(* legs (r-block seam->band reconciliation, symbolic in q, q=0 here).               *)
(*                                                                                  *)
(* SESSION-051: CLOSED CHEAT-FREE (hyps=0).  s050's "warm 16*1 reduce quirk" was a  *)
(* MISDIAGNOSIS.  The real root cause: WBN_PREP_TO_END_FULL_r_TAC does NOT handle    *)
(* r=1 (it fails ACCEPT_TAC even on a COLD image) -- which is EXACTLY why the >=17    *)
(* build hand-writes WBN_PREP_TO_END_FULL_1 (:4011) and only applies the parametric  *)
(* tactic for r=2..8.  The 916 legs mirror that structure precisely:                 *)
(*   FULL_916_1 = the hand-written FULL_1 tactic body (band-agnostic: it works from  *)
(*     the nblk=8*(q+1)+1 equation + the ext2 seam post, not the 17<=/9<= band),      *)
(*   FULL_916_2..8 = WBN_PREP_TO_END_FULL_r_TAC r (unchanged; the band change is      *)
(*     confined to the goal hyps that STRIP_TAC consumes).                           *)
(* All 8 legs verified hyps=0; the dispatcher is the WBN_PREP_TO_END 8-way           *)
(* rr=(nblk-9)MOD 8 split over the FULL_916 array.                                    *)

(* 916-banded full-post goal (9..16 band; otherwise identical to *)
(* wbn_prep_to_end_full_goal). *)
let wbn_prep_to_end_full_916_goal r =
  let nblk_eq = subst[mk_small_numeral r,`r_:num`]
                  `nblk = 8 * ((nblk - 9) DIV 8 + 1) + r_` in
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_916_tm :: nblk_eq :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_prepretail_post_ext2; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

(* the r=1 leg tactic = body of WBN_PREP_TO_END_FULL_1 (:4011), hoisted as a named  *)
(* tactic.  Band-agnostic, so it serves both the >=17 and the 9..16 r=1 legs.  The  *)
(* parametric WBN_PREP_TO_END_FULL_r_TAC cannot do r=1 (case-2/tag close specialise *)
(* to r>=2 store re-indexing). *)
let WBN_PREP_TO_END_FULL_1_HAND_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC (wbn_narrow_frame 1) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs(el 2 (snd(strip_comb(snd(dest_imp(concl(SPECL (shift_vals 1) WB_TAIL_GEN2_1)))))))),
            el 64 (conjuncts (snd(dest_abs wbn_prepretail_post_ext2)))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ABBREV_TAC `q = (nblk - 9) DIV 8` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `j < 8 * (q + 1)` THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM ACCEPT_TAC;
        SUBGOAL_THEN `j = 8 * (q + 1)` SUBST_ALL_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`; GCM_CTR_INC_ITER_ADD] THEN
        FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
          (match lhs(concl th) with Comb(Comb(Const("read",_),_),_) ->
             (can (find_term (fun t -> t = `aes256_encrypt`)) (concl th)) | _ -> false)
          then SUBST1_TAC th else NO_TAC) THEN
        SUBGOAL_THEN `SUB_LIST (0,16) (SUB_LIST (128 * (q + 1),16 * 1) (ibytes:byte list)) =
                      SUB_LIST (128 * (q + 1),16) ibytes` SUBST1_TAC THENL
         [REWRITE_TAC[SUB_LIST_MIN_RIGHT] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN
        CONV_TAC WORD_RULE];
      REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE] THEN AP_TERM_TAC THEN
      SUBGOAL_THEN
        `list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) (ibytes:byte list))) nblk =
         list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) (8 * (q + 1) + 1)`
        SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[LIST_OF_SEQ_ADD; MAP_APPEND; GHASH_ACC_APPEND] THEN AP_TERM_TAC THEN
      REWRITE_TAC[LIST_OF_SEQ_CLAUSES; MAP; MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[SUB_LIST_MIN_RIGHT; ARITH_RULE `MIN 16 16 = 16`;
                  ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`]];
    MATCH_MP_TAC ENSURES_ADD_PRESERVED THEN CONJ_TAC THENL
     [INNER_TAIL_FEED_TAC 1 WB_TAIL_GEN2_1;
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE; SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
      CONV_TAC(REDEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM] THEN
      CONV_TAC(REDEPTH_CONV BETA_CONV) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
        (match rhs(concl th) with Var("s'",_) -> true | _ -> false))) THEN
      SUBGOAL_THEN `nonoverlapping (word_add out_p (word (16 * j)):int64,16)
         (word_add out_p (word (128 * ((nblk - 9) DIV 8 + 1))),16)` ASSUME_TAC THENL
       [NONOVERLAPPING_TAC; ALL_TAC] THEN
      WBN_PUSH_LHS_READ_TAC THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) then MATCH_MP_TAC th else NO_TAC) THEN
      FIRST_X_ASSUM ACCEPT_TAC]];;

let WBN_PREP_TO_END_FULL_916_1 = prove(wbn_prep_to_end_full_916_goal 1, WBN_PREP_TO_END_FULL_1_HAND_TAC);;
let WBN_PREP_TO_END_FULL_916_2 = prove(wbn_prep_to_end_full_916_goal 2, WBN_PREP_TO_END_FULL_r_TAC 2);;
let WBN_PREP_TO_END_FULL_916_3 = prove(wbn_prep_to_end_full_916_goal 3, WBN_PREP_TO_END_FULL_r_TAC 3);;
let WBN_PREP_TO_END_FULL_916_4 = prove(wbn_prep_to_end_full_916_goal 4, WBN_PREP_TO_END_FULL_r_TAC 4);;
let WBN_PREP_TO_END_FULL_916_5 = prove(wbn_prep_to_end_full_916_goal 5, WBN_PREP_TO_END_FULL_r_TAC 5);;
let WBN_PREP_TO_END_FULL_916_6 = prove(wbn_prep_to_end_full_916_goal 6, WBN_PREP_TO_END_FULL_r_TAC 6);;
let WBN_PREP_TO_END_FULL_916_7 = prove(wbn_prep_to_end_full_916_goal 7, WBN_PREP_TO_END_FULL_r_TAC 7);;
let WBN_PREP_TO_END_FULL_916_8 = prove(wbn_prep_to_end_full_916_goal 8, WBN_PREP_TO_END_FULL_r_TAC 8);;

let wbn_full_916_thm = Array.of_list
  [WBN_PREP_TO_END_FULL_916_1;  (* index 0 unused; use r directly 1..8 *)
   WBN_PREP_TO_END_FULL_916_1; WBN_PREP_TO_END_FULL_916_2; WBN_PREP_TO_END_FULL_916_3;
   WBN_PREP_TO_END_FULL_916_4; WBN_PREP_TO_END_FULL_916_5; WBN_PREP_TO_END_FULL_916_6;
   WBN_PREP_TO_END_FULL_916_7; WBN_PREP_TO_END_FULL_916_8];;

let wbn_prep_to_end_916_goal =
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_916_tm :: `9 <= nblk` :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_prepretail_post_ext2; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

let WBN_PREP_TO_END_916 = prove(wbn_prep_to_end_916_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `nblk - 9` (MATCH_MP DIVISION (ARITH_RULE `~(8 = 0)`))) THEN
  ABBREV_TAC `rr = (nblk - 9) MOD 8` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `rr < 8` then MP_TAC th else NO_TAC) THEN
  REWRITE_TAC[ARITH_RULE
    `rr < 8 <=> rr = 0 \/ rr = 1 \/ rr = 2 \/ rr = 3 \/
                rr = 4 \/ rr = 5 \/ rr = 6 \/ rr = 7`] THEN
  STRIP_TAC THEN
  FIRST (map (fun r ->
    MATCH_MP_TAC wbn_full_916_thm.(r) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `nblk - 9 = (nblk - 9) DIV 8 * 8 + rr` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `9 <= nblk` THEN ARITH_TAC) (1--8)));;

(* WBN_FRONT_TO_END_916: the full 9..16 front->exit chain, pc+0x20 -> pc+4528. *)
(* FRONT_TO_PREP_EXT2_916 ; PREP_TO_END_916 via ENSURES_TRANS_SIMPLE.          *)
let wbn_front_to_end_916_goal =
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_916_tm :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_front_P_tm; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

let WBN_FRONT_TO_END_916 = prove(wbn_front_to_end_916_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_prepretail_post_ext2 THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    MATCH_MP_TAC WBN_FRONT_TO_PREP_EXT2_916 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WBN_PREP_TO_END_916 THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* PHASE 6 IS COMPLETE (session-051): WBN_PREP_TO_END_916 is CHEAT-free, so     *)
(* the WHOLE nblk>8 chain (WBN_FRONT_TO_END for >=17, WBN_FRONT_TO_END_916 for  *)
(* 9..16) is CHEAT-free.  The former scoped Q19/Q16 RINNER=LINNER identity (once *)
(* at the loop body + the 4 guarded prepretail sites) was CLOSED by the Q19 R1'  *)
(* route in sessions 064-065 (WBN_MACHINE_REDUCE_IS_PROP3_PACK +                 *)
(* WBN_BODY_Q19_REDUCE_CLEAN, wired in).  No CHEAT, no new_axiom anywhere.        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* PHASE 7 tag-side bridge lemmas (session-051, sim-free, symbolic nblk).      *)
(* These reconcile wbn_end_post's tag conjunct to the NIST nist_ghash form at   *)
(* symbolic nblk (the fixed-N LIST_OF_SEQ_NIST_INPUT in wb.ml does not cover a   *)
(* symbolic count).  WBN_TAG_NIST_BRIDGE is the drop-in tag rewrite for the      *)
(* Phase-7 postcondition reconcile under the band identifications               *)
(* byteswap128 h = ghash_twist H and xi = word_reversefields 8 tag0.            *)
let MAP_LIST_OF_SEQ = prove
 (`!(g:A->B) f n. MAP g (list_of_seq f n) = list_of_seq (g o f) n`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN GEN_TAC THEN
  ASM_REWRITE_TAC[LIST_OF_SEQ; MAP; o_THM] THEN REWRITE_TAC[o_ASSOC]);;

let LIST_OF_SEQ_NIST_INPUT_SYM = prove
 (`!ibytes N.
     list_of_seq (nist_input_block ibytes) N =
     MAP word_bytereverse
       (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAP_LIST_OF_SEQ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; nist_input_block; BREV_RF8_128]);;

let WBN_TAG_NIST_BRIDGE = prove
 (`!(H:int128) h xi tag0 ibytes nblk.
     byteswap128 h = ghash_twist H /\ xi = word_reversefields 8 tag0
     ==> word_bytereverse
           (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
             (MAP word_bytereverse
               (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) nblk))) =
         word_reversefields 8
           (nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) nblk))`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[NIST_GHASH_IS_POLYVAL; LIST_OF_SEQ_NIST_INPUT_SYM; BREV_RF8_128] THEN
  REWRITE_TAC[GSYM BREV_RF8_128; WORD_BYTEREVERSE_BYTEREVERSE]);;

(* ------------------------------------------------------------------------- *)
(* PHASE 7 output-side bridge lemmas (session-052, sim-free, symbolic nblk).   *)
(* These are the symbolic-nblk analogues of the fixed-N GCM_DEC_PT_BYTES_WHOLE_k*)
(* + BYTE_LIST_AT_WHOLE_CTR machinery in wb.ml, reconciling wbn_end_post's      *)
(* nblk-uniform per-block output store forall to byte_list_at(gcm_dec_pt_bytes).*)

(* EL of gcm_dec_blocks_from at a symbolic index (analogue of build_aes_ctr_el).*)
let EL_GCM_DEC_BLOCKS_FROM = prove
 (`!m base i x. i < m
     ==> EL i (gcm_dec_blocks_from base m x) =
         bytes_to_int128 (SUB_LIST (16 * (base + i),16) x)`,
  INDUCT_TAC THEN REWRITE_TAC[LT] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[GCM_DEC_BLOCKS_FROM_STEP; EL; HD; TL] THENL
   [REWRITE_TAC[ADD_CLAUSES];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`base + 1`; `n:num`; `x:byte list`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(base + 1) + n = base + SUC n` SUBST1_TAC THENL
     [ARITH_TAC; REFL_TAC]]);;

(* Whole-blocks (tail=16) collapse of gcm_dec_pt_bytes at symbolic nblk:        *)
(*   nfull=(16*nblk-1)DIV 16=nblk-1, tail=16, so aes_ctr_full_tail_bytes -> ctr. *)
let GCM_DEC_PT_BYTES_WHOLE_SYM = prove
 (`!nblk ibytes ctr0 rk. 1 <= nblk
     ==> gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk =
         aes_ctr_bytes ctr0 (gcm_dec_blocks_from 0 nblk ibytes) rk`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_dec_pt_bytes] THEN
  SUBGOAL_THEN `(16 * nblk - 1) DIV 16 = nblk - 1` SUBST1_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `1 <= nblk ==> 16 * nblk - 1 = 16 * (nblk - 1) + 15`] THEN
    SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `nblk - 1 + 1 = nblk /\ 16 * nblk - 16 * (nblk - 1) = 16`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC AES_CTR_FULL_TAIL_BYTES_WHOLE THEN
  REWRITE_TAC[LENGTH_GCM_DEC_BLOCKS_FROM] THEN ASM_ARITH_TAC);;

(* Per-block value bridge: wbn_end_post's store form (word_xor(word_xor cph     *)
(* aes13..)k14) is exactly EL j of aes_ctr over the gcm_dec_blocks_from list     *)
(* with the 15-key list.  Standalone (keeps AES/counter algebra out of the       *)
(* ensures context) — analogue of wb.ml build_aes_ctr_el, at symbolic j.        *)
let WBN_ENDBLOCK_IS_AES_CTR = prove
 (`!nblk ibytes ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 j.
     j < nblk
     ==> word_xor
           (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16) ibytes))
             (aes13 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
                    k10 k11 k12 k13))
           k14 =
         EL j (aes_ctr ctr0 (gcm_dec_blocks_from 0 nblk ibytes)
                 [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`nblk:num`; `0`; `j:num`; `ibytes:byte list`]
    EL_GCM_DEC_BLOCKS_FROM) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`gcm_dec_blocks_from 0 nblk ibytes`; `ctr0:int128`;
    `[k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]:int128 list`; `j:num`]
    EL_AES_CTR) THEN
  ASM_REWRITE_TAC[LENGTH_GCM_DEC_BLOCKS_FROM] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE);;

(* The full L1 output bridge: wbn_end_post's per-block store forall            *)
(* (word_xor(word_xor cph aes13..)k14) collapses to                             *)
(* byte_list_at(gcm_dec_pt_bytes(16*nblk)..) over the whole buffer.  The        *)
(* symbolic-nblk analogue of prove_wb_wrapper's BYTE_LIST_AT_WHOLE_CTR leg.     *)
(* 128*nblk < 2 EXP 62 (from the chain hyps) gives val(word(16*nblk))=16*nblk.  *)
let WBN_END_OUTPUT_BYTE_LIST = prove
 (`!nblk ibytes ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 out_p s.
     1 <= nblk /\ 128 * nblk < 2 EXP 62 /\
     (!j. j < nblk
          ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
              word_xor
              (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16) ibytes))
              (aes13 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
               k10 k11 k12 k13))
              k14)
     ==> byte_list_at
           (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0
              [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])
           out_p (word (16 * nblk)) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GCM_DEC_PT_BYTES_WHOLE_SYM] THEN
  MATCH_MP_TAC BYTE_LIST_AT_WHOLE_CTR THEN EXISTS_TAC `nblk:num` THEN
  REWRITE_TAC[LENGTH_GCM_DEC_BLOCKS_FROM] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC WBN_ENDBLOCK_IS_AES_CTR THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* PHASE 7 (session-052): AESV8_GCM_8X_DEC_256_WB_CORRECT -- all nblk >= 1.     *)
(* 3-way ASM_CASES: nblk<=8 -> existing DISPATCH (NIST vocab already); 9..16 -> *)
(* WBN_FRONT_TO_END_916; >=17 -> WBN_FRONT_TO_END.  Each >8 chain ends in       *)
(* wbn_end_post (RAW per-block ext2 vocab) and begins at wbn_front_P_tm (raw xi, *)
(* individual k0..k14 reads, htable_mem_dec h).  WBN_CHAIN_TO_NIST_TAC bridges   *)
(* the raw chain to the NIST DISPATCH vocab under the band identifications       *)
(*   ki := EL i rk,  h := byteswap128 (ghash_twist H),  xi := word_reversefields *)
(*   8 tag0                                                                      *)
(* via ENSURES_PRECONDITION_THM (NIST pre -> raw pre: KEY_READS_FROM_WORDLIST +  *)
(* HTABLE_MEM_DEC_IS_HTABLE_MEM_8 + BYTESWAP128_INVOLUTION + BYTE_LIST_AT_TO_    *)
(* READ_BYTES) and ENSURES_POSTCONDITION_THM (raw post -> NIST post: RK_ETA_15 + *)
(* WBN_END_OUTPUT_BYTE_LIST for output, WBN_TAG_NIST_BRIDGE for tag).  The chain *)
(* hyps flatten from the DISPATCH ALLPAIRS/PAIRWISE/ALL form.                    *)
(*                                                                             *)
(* The unified statement is the DISPATCH statement with the `nblk<=8` bound      *)
(* DROPPED (just 1<=nblk) and the two size bounds 128*nblk<2 EXP 62 /            *)
(* val in_p+16*nblk<2 EXP 63 ADDED to the antecedent (genuine preconditions the  *)
(* Phase-8 wrapper/guard supplies -- for nblk<=8 they follow from small nblk;    *)
(* for symbolic large nblk they must be assumed to avoid pointer/length          *)
(* overflow).  CHEAT-FREE (the former Q19/[11] RINNER=LINNER identity was closed  *)
(* by the R1' route in sessions 064-065); no new_axiom anywhere.                  *)

let AESV8_GCM_8X_DEC_256_WB_CORRECT =
  (* identification substitution: raw chain vars -> DISPATCH NIST vars *)
  let idsub =
    [`word_reversefields 8 (tag0:int128)`,`xi:int128`;
     `byteswap128 (ghash_twist H)`,`h:int128`] @
    (map (fun i -> mk_comb(mk_comb(`EL:num->(int128)list->int128`,mk_small_numeral i),
                           `rk:int128 list`),
                   mk_var("k"^string_of_int i,`:int128`)) (0--14)) in
  let raw_pre'  = subst idsub wbn_front_P_tm
  and raw_post' = subst idsub wbn_end_post in
  (* the shared reconcile tactic, parameterized by the chain theorem *)
  let WBN_CHAIN_TO_NIST_TAC chain_thm =
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC raw_pre' THEN CONJ_TAC THENL
     [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[HTABLE_MEM_DEC_IS_HTABLE_MEM_8; BYTESWAP128_INVOLUTION] THEN
      MP_TAC(SPECL [`key_p:int64`; `rk:int128 list`; `s:armstate`]
        KEY_READS_FROM_WORDLIST) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`ibytes:byte list`; `in_p:int64`; `word (16 * nblk):int64`;
        `s:armstate`] BYTE_LIST_AT_TO_READ_BYTES) THEN
      SUBGOAL_THEN `val (word (16 * nblk):int64) = 16 * nblk` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC raw_post' THEN
      CONJ_TAC THENL
       [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN
           `gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk =
            gcm_dec_pt_bytes (16 * nblk) ibytes ctr0
              [EL 0 rk;EL 1 rk;EL 2 rk;EL 3 rk;EL 4 rk;EL 5 rk;EL 6 rk;EL 7 rk;
               EL 8 rk;EL 9 rk;EL 10 rk;EL 11 rk;EL 12 rk;EL 13 rk;EL 14 rk]`
           SUBST1_TAC THENL
           [AP_TERM_TAC THEN MATCH_MP_TAC RK_ETA_15 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
          MATCH_MP_TAC WBN_END_OUTPUT_BYTE_LIST THEN ASM_REWRITE_TAC[];
          MP_TAC(SPECL [`H:int128`; `byteswap128 (ghash_twist H)`;
            `word_reversefields 8 (tag0:int128)`; `tag0:int128`; `ibytes:byte list`;
            `nblk:num`] WBN_TAG_NIST_BRIDGE) THEN
          REWRITE_TAC[BYTESWAP128_INVOLUTION] THEN DISCH_THEN MATCH_ACCEPT_TAC];
        MATCH_MP_TAC chain_thm THEN
        RULE_ASSUM_TAC(REWRITE_RULE
          [ALLPAIRS; PAIRWISE; ALL; MAP; NONOVERLAPPING_CLAUSES]) THEN
        REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; MAP; NONOVERLAPPING_CLAUSES] THEN
        REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_ARITH_TAC) THEN
        ASM_MESON_TAC[NONOVERLAPPING_MODULO_SYM; nonoverlapping]]] in
  (* the unified goal: DISPATCH statement, `nblk<=8` dropped, size bounds added *)
  let correct_goal =
    let dvars, dbody = strip_forall (concl AESV8_GCM_8X_DEC_256_WB_DISPATCH) in
    let dhyps, dens = dest_imp dbody in
    let hyps0 = filter (fun c -> c <> `nblk <= 8`) (conjuncts dhyps) in
    let hyps' = `1 <= nblk` :: `128 * nblk < 2 EXP 62` ::
                `val (in_p:int64) + 16 * nblk < 2 EXP 63` ::
                (filter (fun c -> c <> `1 <= nblk`) hyps0) in
    list_mk_forall(dvars, mk_imp(list_mk_conj hyps', dens)) in
  prove(correct_goal,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_CASES_TAC `nblk <= 8` THENL
     [ASM_MESON_TAC[AESV8_GCM_8X_DEC_256_WB_DISPATCH]; ALL_TAC] THEN
    ASM_CASES_TAC `nblk <= 16` THENL
     [WBN_CHAIN_TO_NIST_TAC WBN_FRONT_TO_END_916;
      WBN_CHAIN_TO_NIST_TAC WBN_FRONT_TO_END]);;

(* ------------------------------------------------------------------------- *)
(* PHASE 8 (session-067): AESV8_GCM_8X_DEC_256_WB_SUBROUTINE_CORRECT.          *)
(* The ABI subroutine wrapper for the valid path (bit_len = 128*nblk).  Binary *)
(* layout (objdump): the entry GUARD (nop;cbz x1;ands zr,x1,#0x7f;b.ne, offs   *)
(* 0x0..0xc) precedes the d8-d15 callee-save spills (stp d8,d9,[sp,#-80]!;      *)
(* stp d10,d11;d12,d13;d14,d15, offs 0x10..0x1c); the core runs pc+0x20..pc+   *)
(* 0x11ac (= _CORRECT); the epilogue (mov x0,x9; ldp d10..d15; ldp d8,d9,[sp], *)
(* #80; ret, offs 0x11b0..0x11c4) restores.  X30 is NOT saved (returns via LR).*)
(*                                                                             *)
(* Stock ARM_ADD_RETURN_STACK_TAC does not apply: the guard's b.ne sits in the *)
(* prologue (its ARM_STEPS stalls on the symbolic conditional-PC) and the SP   *)
(* offset needs the core instantiated by hand.  So the wrapper is hand-rolled: *)
(*  - WB_CORE_INST = _CORRECT SPECL'd stackpointer := word_sub stackpointer     *)
(*    (word 80) (so the in-frame SP = the caller SP after the prologue's        *)
(*    stp ...,[sp,#-80]!);                                                      *)
(*  - WB_CORE_INST_UF2 unfolds the folded input mem predicates (byte_list_at /  *)
(*    wordlist_from_memory / htable_mem_8) AND concretizes val(word(16*nblk)) = *)
(*    16*nblk (from 128*nblk<2 EXP 62) so ARM_STEPS carries the quantified      *)
(*    input byte read past the disjoint stack stores (else it drops it);        *)
(*  - WB_GUARD_FALLTHROUGH_TAC injects the guard fall-through facts             *)
(*    (val(word(128*nblk))=128*nblk; ~(128*nblk=0); val(word_and .. 127)=0) so  *)
(*    the prologue steps clean; then ARM_STEPS 1--8 (guard+saves), ARM_BIGSTEP  *)
(*    s9 (crosses the core), ARM_STEPS 10--15 (epilogue), ENSURES_FINAL.        *)
(* The d8-d15 preservation now closes because the F1-narrowed core frame        *)
(* bytes(sp+64,16) is DISJOINT from the [sp,64) spill area (session-066).       *)
(* Inherits _CORRECT's soundness: CHEAT-free, no new_axiom.                     *)
(* ------------------------------------------------------------------------- *)

let AESV8_GCM_8X_DEC_256_WB_SUBROUTINE_CORRECT =
  let EXEC = AESV8_GCM_8X_DEC_256_WB_EXEC in
  (* the core, SP set to the post-prologue in-frame value *)
  let WB_CORE_INST =
    SPECL [`pc:num`; `word_sub stackpointer (word 80):int64`;
           `in_p:int64`; `out_p:int64`; `xi_p:int64`; `ivec_p:int64`;
           `key_p:int64`; `htbl_p:int64`; `nblk:num`; `ibytes:byte list`;
           `rk:int128 list`; `H:int128`; `tag0:int128`; `ctr0:int128`]
          AESV8_GCM_8X_DEC_256_WB_CORRECT in
  (* val(word(16*nblk))=16*nblk from 128*nblk<2 EXP 62 (so 16*nblk<2 EXP 64) *)
  let VAL16EQ = prove
   (`128 * nblk < 2 EXP 62 ==> val (word (16 * nblk):int64) = 16 * nblk`,
    DISCH_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    ASM_ARITH_TAC) in
  (* unfold folded input mem preds + concretize the byte bound in the core *)
  let WB_CORE_INST_UF2 =
    REWRITE_RULE[byte_list_at; wordlist_from_memory; htable_mem_8; DIMINDEX_128;
                 fst EXEC; UNDISCH VAL16EQ] WB_CORE_INST in
  (* guard fall-through: cbz/b.ne both fall through for bit_len = 128*nblk *)
  let WB_GUARD_FALLTHROUGH_TAC =
    SUBGOAL_THEN `val (word (128 * nblk):int64) = 128 * nblk` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(128 * nblk = 0)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val (word_and (word (128 * nblk):int64) (word 127)) = 0`
      ASSUME_TAC THENL
     [SUBGOAL_THEN `(127:num) = 2 EXP 7 - 1` SUBST1_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(2:num) EXP 7 = 128` SUBST1_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      REWRITE_TAC[MOD_MULT];
      ALL_TAC] in
  prove
   (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk ibytes rk H
      tag0 ctr0 returnaddress.
      1 <= nblk /\
      128 * nblk < 2 EXP 62 /\
      val in_p + 16 * nblk < 2 EXP 63 /\
      LENGTH ibytes = 16 * nblk /\
      LENGTH rk = 15 /\
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16]
      [word pc,4560; in_p,16 * nblk; key_p,240; htbl_p,192;
       word_sub stackpointer (word 80),80] /\
      PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
      ALL (nonoverlapping (word_sub stackpointer (word 80),80))
      [word pc,4560; in_p,16 * nblk; key_p,240; htbl_p,192]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
               read PC s = word pc /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS
               [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p]
               s /\
               byte_list_at ibytes in_p (word (16 * nblk)) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = returnaddress /\
               byte_list_at (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p
               (word (16 * nblk)) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
               (nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) nblk)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE
           [memory :> bytes (out_p,16 * nblk); memory :> bytes (xi_p,16);
            memory :> bytes (ivec_p,16);
            memory :> bytes (word_sub stackpointer (word 80),80)])`,
    REWRITE_TAC[byte_list_at; wordlist_from_memory; htable_mem_8; DIMINDEX_128;
                fst EXEC] THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; PAIRWISE; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `val (word (16 * nblk):int64) = 16 * nblk` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC WB_CORE_INST_UF2 THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; PAIRWISE; ALLPAIRS; ALL] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MATCH_MP_TAC ALIGNED_WORD_SUB THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[aligned; WORD_VAL] THEN CONV_TAC WORD_REDUCE_CONV THEN
      REWRITE_TAC[DIMINDEX_64] THEN CONJ_TAC THEN CONV_TAC NUM_DIVIDES_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
       MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS; fst EXEC] THEN
    DISCH_THEN(fun th ->
      (ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
       MAP_EVERY (fun c -> ENSURES_PRESERVED_DREG_TAC ("init_"^fst(dest_const c)) c)
         [`D8`;`D9`;`D10`;`D11`;`D12`;`D13`;`D14`;`D15`]) THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
      WB_GUARD_FALLTHROUGH_TAC THEN
      ARM_STEPS_TAC EXEC (1--8) THEN MP_TAC th) THEN
    ARM_BIGSTEP_TAC EXEC "s9" THENL
     [REWRITE_TAC[C_ARGUMENTS] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC(!simulation_precanon_thms) THEN ARM_STEPS_TAC EXEC (10--15) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_BLAST `(word_zx:int128->int64)(word_zx(x:int64)) = x`] THEN
      CONV_TAC WORD_RULE]);;

(* ------------------------------------------------------------------------- *)
(* THE COMPLETE WHOLE-FUNCTION CONTRACT.                                       *)
(*                                                                             *)
(* AESV8_GCM_8X_DEC_256_WB_SUBROUTINE_CORRECT (above, this file) together with  *)
(* AESV8_GCM_8X_DEC_256_WB_GUARD (arm/proofs/aesv8_gcm_8x_dec_256_wb.ml) form   *)
(* the complete AAPCS64 subroutine contract of the whole-blocks binary, for     *)
(* EVERY C-argument bit_len:                                                    *)
(*   - valid   bit_len = word (128*nblk), 1 <= nblk (a positive multiple of 128 *)
(*             bits): SUBROUTINE_CORRECT -- decrypts the 16*nblk-byte buffer to  *)
(*             gcm_dec_pt_bytes and updates the running GHASH tag to nist_ghash, *)
(*             preserving d8-d15/SP and restoring PC to the return address.      *)
(*   - invalid ~(val bit_len = 0) /\ ~(val bit_len MOD 128 = 0) (bit_len set but *)
(*             not a whole number of 128-bit blocks): GUARD -- the guard branch  *)
(*             (tst x1,#0x7f; b.ne) rejects, returns 0 in X0, touches no memory. *)
(* (The remaining bit_len = 0 case exits at the entry cbz x1 with the same       *)
(*  ret-0 behaviour; it is not separately stated as it carries no cryptographic  *)
(*  postcondition.)  This mirrors the nblk<=8 pairing DISPATCH + GUARD in        *)
(*  wb.ml:4643-4708.                                                             *)
(*                                                                             *)
(* Soundness gate: both whole-function theorems (and the underlying CORRECT      *)
(* for all nblk>=1) are hyps=0, and the file introduces NO new axiom -- the      *)
(* Q19/GHASH identity that was scoped behind a CHEAT for ~15 sessions is closed  *)
(* (sessions 061-065, R1' route).                                               *)
(* ------------------------------------------------------------------------- *)

let () =
  let whole_fn = [AESV8_GCM_8X_DEC_256_WB_CORRECT;
                  AESV8_GCM_8X_DEC_256_WB_SUBROUTINE_CORRECT;
                  AESV8_GCM_8X_DEC_256_WB_GUARD] in
  if exists (fun th -> hyp th <> []) whole_fn then
    failwith "WB dec whole-function theorems: unexpected hypotheses"
  else if List.length (axioms()) <> 3 then
    failwith "WB dec whole-function: unexpected axiom count (new_axiom introduced?)"
  else Format.print_string
    "WB dec whole-function: CORRECT + SUBROUTINE_CORRECT + GUARD hyps=0, axioms=3\n";;
