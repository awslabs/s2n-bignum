(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* XOR of bytes into a Keccak state: lemmas for the byte loops.              *)
(* In the monolithic gcc 12 -O2 build (see mlkem_native/README.md),          *)
(* mlkem_keccakf1600_xor_bytes has no code of its own: the compiler has      *)
(* inlined it into mlk_keccakf1600x4_xor_bytes_c and mlk_keccak_absorb_once  *)
(* as loops that XOR len bytes of data into the 200-byte state starting at   *)
(* byte off. The proofs of these functions prove each such loop with the     *)
(* specification of mlkem_keccakf1600_xor_bytes of the gcc12_O2 build: the   *)
(* state, as a 1600-bit word S, becomes word_xor S (word(2 EXP (8 * off) *   *)
(* m)) where m is the number that the len bytes of data form. The lemmas     *)
(* here are the ones about numbers and bytes that those proofs share.        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(* ------------------------------------------------------------------------- *)
(* The state after i of the bytes of the data m have been XORed into it, as  *)
(* bytes. Only byte off + i changes in the next step.                        *)
(* ------------------------------------------------------------------------- *)

let BYTE_UPDATE = prove
 (`!x c k j.
        x < 2 EXP (8 * k) /\ c < 256
        ==> ((x + 2 EXP (8 * k) * c) DIV 2 EXP (8 * j)) MOD 256 =
            if j = k then c else (x DIV 2 EXP (8 * j)) MOD 256`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN
    SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES; MOD_LT];
    FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
     `~(j = k) ==> j < k \/ k < j`))] THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o REWRITE_RULE[LT_EXISTS]) THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; LEFT_ADD_DISTRIB; EXP_ADD] THEN
    REWRITE_TAC[GSYM MULT_ASSOC] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `256 * y + z = y * 256 + z`] THEN
    REWRITE_TAC[MOD_MULT_ADD];
    SUBGOAL_THEN `x + 2 EXP (8 * k) * c < 2 EXP (8 * j) /\ x < 2 EXP (8 * j)`
     (fun th -> SIMP_TAC[th; DIV_LT; MOD_0]) THEN
    SUBGOAL_THEN `2 EXP (8 * k) * 256 <= 2 EXP (8 * j)` MP_TAC THENL
     [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM EXP_ADD; LE_EXP] THEN
      ASM_ARITH_TAC;
      UNDISCH_TAC `c < 256` THEN UNDISCH_TAC `x < 2 EXP (8 * k)` THEN
      SPEC_TAC(`2 EXP (8 * j)`,`q:num`) THEN
      SPEC_TAC(`2 EXP (8 * k)`,`p:num`) THEN
      REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `x + p * c < p * 256` MP_TAC THENL
       [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `p + p * c` THEN
        ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
        REWRITE_TAC[ARITH_RULE `p + p * c = p * (c + 1)`; LE_MULT_LCANCEL] THEN
        ASM_ARITH_TAC;
        MP_TAC(SPECL [`p:num`; `c:num`] LE_MULT_LCANCEL) THEN
        ASM_ARITH_TAC]]]);;

let XOR_BYTES_STEP = prove
 (`!(S:1600 word) m off i j.
        off + i < 200 /\ j < 200
        ==> word_subword
             (word_xor S (word(2 EXP (8 * off) *
                               m MOD 2 EXP (8 * (i + 1)))))
             (8 * j,8):byte =
            if j = off + i
            then word_xor
                  (word_subword
                    (word_xor S (word(2 EXP (8 * off) * m MOD 2 EXP (8 * i))))
                    (8 * j,8))
                  (word((m DIV 2 EXP (8 * i)) MOD 256))
            else word_subword
                  (word_xor S (word(2 EXP (8 * off) * m MOD 2 EXP (8 * i))))
                  (8 * j,8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
   `2 EXP (8 * off) * m MOD 2 EXP (8 * (i + 1)) =
    2 EXP (8 * off) * m MOD 2 EXP (8 * i) +
    2 EXP (8 * (off + i)) * (m DIV 2 EXP (8 * i)) MOD 256`
  SUBST1_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MULT_CLAUSES;
                ARITH_RULE `2 EXP 8 = 256`; MOD_MULT_MOD] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_SUBWORD_WORD; DIMINDEX_CONV `dimindex(:1600)`;
               DIMINDEX_8; ARITH_RULE `j < 200 ==> 8 * j + 8 <= 1600`] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) BYTE_UPDATE o
    rand o rand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; LT_MULT_LCANCEL] THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
    DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  SUBGOAL_THEN `2 EXP (8 * off) * m MOD 2 EXP (8 * i) < 2 EXP (8 * (off + i))`
   (fun th -> SIMP_TAC[th; DIV_LT; MOD_0; WORD_XOR_0]) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; LT_MULT_LCANCEL] THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ]);;

(*** The invariant for the bytes other than byte t ***)

let XOR_BYTES_RESTRICT_RULE t th =
  let j,bod = dest_forall(concl th) in
  let p,q = dest_imp bod in
  let p' = mk_conj(p,mk_neg(mk_eq(j,t))) in
  GEN j (DISCH p' (MP (SPEC j th) (CONJUNCT1(ASSUME p'))));;

(* ------------------------------------------------------------------------- *)
(* After the loop, the whole state from its bytes.                           *)
(* ------------------------------------------------------------------------- *)

let XOR_BYTES_FINAL = prove
 (`!(a:int64) (S:1600 word) off len d m s:armstate.
        off + len <= 200 /\
        read (memory :> bytes(d,len)) s = m /\
        (!j. j < 200
             ==> read (memory :> bytes8(word_add a (word j))) s =
                 word_subword
                  (word_xor S (word(2 EXP (8 * off) * m MOD 2 EXP (8 * len))))
                  (8 * j,8))
        ==> read (memory :> wbytes a) s = word_xor S (word(2 EXP (8 * off) * m))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `m MOD 2 EXP (8 * len) = m`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC MOD_LT THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (can (term_match []
      `read (memory :> bytes (d,len)) s = m`) o concl)) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
    ALL_TAC] THEN
  REWRITE_TAC[READ_MEMORY_WBYTES_VAL] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  W(fun (_,w) -> MP_TAC(ISPEC (rand(rand w)) VAL_BOUND)) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  DISCH_THEN(fun th -> SUBST1_TAC(SYM(MATCH_MP MOD_LT th))) THEN
  REWRITE_TAC[ARITH_RULE `1600 = 8 * 200`] THEN
  MATCH_MP_TAC READ_MEMORY_BYTES_OF_BYTES8 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_subword; ARITH_RULE `2 EXP 8 = 256`]) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The test of a loop that stops at the last index len - 1, which is kept in *)
(* a register, after counting from 0.                                        *)
(* ------------------------------------------------------------------------- *)

let XOR_LAST_FLAG = prove
 (`!len i. ~(len = 0) /\ i < len /\ len <= 200
           ==> (~(val(word_sub (word (len - 1)) (word i):int64) = 0) <=>
                i + 1 < len)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `(len - 1) MOD 2 EXP 64 = len - 1 /\ i MOD 2 EXP 64 = i`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;
