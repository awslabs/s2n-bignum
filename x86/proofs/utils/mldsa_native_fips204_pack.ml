(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas connecting the packing functions of mldsa-native's C code, as they *)
(* are specified in common/mldsa_native_packing.ml, mldsa_native_polyvec.ml  *)
(* and mldsa_native_hints.ml, to the bit packings of the FIPS 204            *)
(* specification in common/fips204.ml. The C code packs a polynomial into a  *)
(* byte array, a function of the byte index, and FIPS 204 into a byte list   *)
(* mldsa_encode c n f of the fields f(0), ..., f(n - 1) of c bits each; the  *)
(* unpacking functions give the coefficients as mldsa_field reads them. For  *)
(* the eight formats (t1, t0, s1 and s2 for eta = 2 and 4, z for gamma1 =    *)
(* 2^17 and 2^19, w1 for both gamma2), for single polynomials and vectors:   *)
(*                                                                           *)
(*  - list_of_seq of the packed bytes is mldsa_encode of the integer field   *)
(*    values (e.g. 4096 - a for t0), given that these are in [0,2^c), which  *)
(*    follows from the ranges in the contracts of the C functions;           *)
(*                                                                           *)
(*  - the integer value of coefficient i of the unpacked polynomial is that  *)
(*    of field i (e.g. 4096 - field i for t0), with no precondition;         *)
(*                                                                           *)
(*  - unpacking what was packed gives the coefficients back (for s1, s2      *)
(*    and w1, where the C code does that), and vectors can be taken at an    *)
(*    offset of l polynomials;                                               *)
(*                                                                           *)
(*  - the hints: mld_pack_hints is mldsa_hintbitpack of any predicate equal  *)
(*    to the hints at the positions below 256 * k, and mld_unpack_hints,     *)
(*    with its checks, is mldsa_hintbitunpack; and, only in terms of         *)
(*    fips204.ml, HintBitUnpack is the partial inverse of HintBitPack on the *)
(*    sets of hints below 256 * k with at most omega < 256 elements          *)
(*    (MLD_FIPS204_HINTBITUNPACK_INVERSE).                                   *)
(*                                                                           *)
(* The packings are proved bit by bit: bit s of byte j of the packing is bit *)
(* (8 * j + s) MOD c of the field of coefficient (8 * j + s) DIV c, and the  *)
(* C code computes each byte from one group of G coefficients and B bytes,   *)
(* with c * G = 8 * B, so only 8 * B cases (or 32 * G for unpacking) need to *)
(* be checked, by rewriting with the bits of the word operations.            *)
(* ========================================================================= *)

needs "common/fips204_theory.ml";;
needs "common/mldsa_native_packing.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "common/mldsa_native_hints.ml";;

(* ------------------------------------------------------------------------- *)
(* The bits of byte strings: bit a of the number of a byte string, and bit a *)
(* of a sum of fields of c bits, which is bit a MOD c of field a DIV c. So a *)
(* byte string is mldsa_encode of fields of c bits, or a field of c bits is  *)
(* a given word, if the bits agree (MLD_FIPS204_ENCODE_BITS and              *)
(* MLD_FIPS204_FIELD_BITS).                                                  *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_NUM_OF_BYTELIST_LIST_OF_SEQ = prove
 (`!(b:num->byte) m.
        num_of_bytelist(list_of_seq b m) =
        nsum {j | j < m} (\j. val(b j) * 2 EXP (8 * j))`,
  SUBGOAL_THEN
   `!l (x:byte). num_of_bytelist(APPEND l [x]) =
                 num_of_bytelist l + 2 EXP (8 * LENGTH l) * val x`
  ASSUME_TAC THENL
   [LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[APPEND; num_of_bytelist; LENGTH] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES; ARITH_RULE
     `8 * SUC n = 8 + 8 * n`; EXP_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[list_of_seq; NSUM_CLAUSES_NUMSEG_LT; num_of_bytelist;
                    LENGTH_LIST_OF_SEQ] THEN
    ARITH_TAC]);;

let MLD_FIPS204_ODD_MOD_EXP = prove
 (`!x c r. ODD((x MOD 2 EXP c) DIV 2 EXP r) <=> r < c /\ ODD(x DIV 2 EXP r)`,
  REWRITE_TAC[GSYM IN_BITS_OF_NUM; BITS_OF_NUM_MOD; IN_ELIM_THM] THEN
  CONV_TAC TAUT);;

let MLD_FIPS204_ODD_DIGITSUM = prove
 (`!c n (v:num->num) a.
        (!i. i < n ==> v i < 2 EXP c)
        ==> (ODD(nsum {i | i < n} (\i. v i * 2 EXP (c * i)) DIV 2 EXP a) <=>
             a < c * n /\ ODD(v(a DIV c) DIV 2 EXP (a MOD c)))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `c = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[EXP; ARITH_RULE `x < 1 <=> x = 0`]) THEN
    ASM_SIMP_TAC[NSUM_EQ_0; IN_ELIM_THM; MULT_CLAUSES; DIV_0; ODD; LT];
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:num`; `c:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = a DIV c` THEN ABBREV_TAC `r = a MOD c` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM EXP_EXP] THEN
  SUBGOAL_THEN
   `!x. ODD(x DIV 2 EXP r) <=> ODD((x MOD 2 EXP c) DIV 2 EXP r)`
   (fun th -> GEN_REWRITE_TAC LAND_CONV [th])
  THENL [ASM_REWRITE_TAC[MLD_FIPS204_ODD_MOD_EXP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`2 EXP c`; `v:num->num`; `{i:num | i < n}`; `q:num`]
     DIGITSUM_DIV_MOD) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `c * q + r < n * c <=> q < n` SUBST1_TAC THENL
   [EQ_TAC THEN DISCH_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `~(n <= q) ==> q < n`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `n * c <= q * c` MP_TAC THENL
       [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ASM_ARITH_TAC];
      SUBGOAL_THEN `(q + 1) * c <= n * c` MP_TAC THENL
       [ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC]];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[DIV_0; ODD]]);;

let MLD_FIPS204_ENCODE_BITS = prove
 (`!c n m (b:num->byte) (w:num->N word).
        c * n = 8 * m /\
        (!i. i < n ==> val(w i) < 2 EXP c) /\
        (!j s. j < m /\ s < 8
               ==> (bit s (b j) <=>
                    bit ((8 * j + s) MOD c) (w((8 * j + s) DIV c))))
        ==> list_of_seq b m = mldsa_encode c n (\i. &(val(w i)))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[mldsa_encode] THEN
  REWRITE_TAC[ARITH_RULE `(8 * m) DIV 8 = m`] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM BYTELIST_OF_NUM_OF_BYTELIST] THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `nsum {i | i < n}
         (\i. num_of_int(&(val((w:num->N word) i)) rem &2 pow c) *
              2 EXP (c * i)) =
    nsum {i | i < n} (\i. val(w i) * 2 EXP (c * i))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_REM; NUM_OF_INT_OF_NUM] THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  REWRITE_TAC[MLD_FIPS204_NUM_OF_BYTELIST_LIST_OF_SEQ] THEN
  REWRITE_TAC[GSYM BITS_OF_NUM_EQ; EXTENSION; IN_BITS_OF_NUM] THEN
  X_GEN_TAC `a:num` THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLD_FIPS204_ODD_DIGITSUM o
    lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM DIMINDEX_8; VAL_BOUND]; DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLD_FIPS204_ODD_DIGITSUM o
    rand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM BIT_VAL] THEN
  ASM_CASES_TAC `a < 8 * m` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a DIV 8`; `a MOD 8`]) THEN
  REWRITE_TAC[ARITH_RULE `8 * a DIV 8 + a MOD 8 = a`] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ; MOD_LT_EQ]);;

let MLD_FIPS204_FIELD_BITS = prove
 (`!c m i (b:num->byte) (u:N word).
        c * (i + 1) <= 8 * m /\
        (!r. bit r u <=>
             r < c /\ bit ((c * i + r) MOD 8) (b((c * i + r) DIV 8)))
        ==> mldsa_field c (list_of_seq b m) i = &(val u)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mldsa_field; INT_OF_NUM_EQ] THEN
  REWRITE_TAC[GSYM BITS_OF_NUM_EQ; EXTENSION; IN_BITS_OF_NUM] THEN
  X_GEN_TAC `r:num` THEN
  REWRITE_TAC[MLD_FIPS204_ODD_MOD_EXP; DIV_DIV; GSYM EXP_ADD] THEN
  ASM_REWRITE_TAC[GSYM BIT_VAL] THEN
  ASM_CASES_TAC `r < c` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MLD_FIPS204_NUM_OF_BYTELIST_LIST_OF_SEQ] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLD_FIPS204_ODD_DIGITSUM o
    lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM DIMINDEX_8; VAL_BOUND]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM BIT_VAL] THEN
  MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `c * (i + 1)` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bits of words: the bits at and above c of a word whose value is below     *)
(* 2^c are clear, and so are those at and above 8 of a byte extended to 32   *)
(* bits.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_BIT_BOUND = prove
 (`!(x:N word) c t. val x < 2 EXP c /\ c <= t ==> ~bit t x`,
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[BIT_VAL] THEN
  SUBGOAL_THEN `val(x:N word) DIV 2 EXP t = 0` (fun th -> REWRITE_TAC[th; ODD])
  THEN MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2 EXP c` THEN
  ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC);;

let MLD_FIPS204_BIT_BOUNDS = prove
 (`!(f:num->N word) n c.
        (!m. m < n ==> val(f m) < 2 EXP c)
        ==> !m. m < n ==> !t. c <= t ==> ~bit t (f m)`,
  MESON_TAC[MLD_FIPS204_BIT_BOUND]);;

let MLD_FIPS204_BIT_ZX_BYTE = prove
 (`!(x:byte) i. bit i (word_zx x:int32) <=> i < 8 /\ bit i x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_WORD_ZX; DIMINDEX_32] THEN
  ASM_CASES_TAC `i < 8` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[BIT_TRIVIAL; DIMINDEX_8; GSYM NOT_LT]]);;

let MLD_FIPS204_WORD_SUB_SUB = WORD_RULE
 `!a x:N word. word_sub a (word_sub a x) = x`;;

(* ------------------------------------------------------------------------- *)
(* The packings by groups: bytes t of the packed coefficients x that are     *)
(* computed by pk from the G coefficients x(G * t DIV B + m) of the group of *)
(* t, with c * G = 8 * B, as pk computes byte k < B of one group, give       *)
(* mldsa_encode of the field values f(x i) if each byte k of a group has the *)
(* bits of the fields W(x i) of the group (MLD_FIPS204_PACK_GEN, where R     *)
(* gives the range of the coefficients for which W(x i) is the field value   *)
(* f(x i) and below 2^c). Likewise, if the unpacking pk computes each        *)
(* coefficient k < G of a group from the B bytes of the group and has the    *)
(* bits of field k of these bytes (after U: for most formats the field is    *)
(* K - coefficient), the coefficients are the field values                   *)
(* (MLD_FIPS204_UNPACK_GEN). For vectors, the polynomials are packed one     *)
(* after the other into P = Q * B bytes each, with 256 = G * Q, so that the  *)
(* groups of the vector are those of its polynomials                         *)
(* (MLD_FIPS204_POLYVEC_PACK_REGROUP, MLD_FIPS204_POLYVEC_UNPACK_REGROUP).   *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_ENCODE_GROUPS = prove
 (`!c G B n (pk:(num->A)->num->byte) (W:A->N word) (b:num->byte) (x:num->A).
        c * G = 8 * B /\ ~(B = 0) /\
        (!y k s. (!m. m < G ==> val(W(y m)) < 2 EXP c) /\ k < B /\ s < 8
                 ==> (bit s (pk y k) <=>
                      bit ((8 * k + s) MOD c) (W(y((8 * k + s) DIV c))))) /\
        (!t. t < B * n
             ==> ?y. (!m. m < G ==> y m = x(G * t DIV B + m)) /\
                     b t = pk y (t MOD B)) /\
        (!i. i < G * n ==> val(W(x i)) < 2 EXP c)
        ==> list_of_seq b (B * n) =
            mldsa_encode c (G * n) (\i. &(val(W(x i))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~(c = 0) /\ ~(G = 0)` STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `c * G = 8 * B` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:num`; `G * n:num`; `B * n:num`; `b:num->byte`;
                 `\i. (W:A->N word)((x:num->A) i)`]
                MLD_FIPS204_ENCODE_BITS) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[MULT_ASSOC] THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `s:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (is_exists o rand o
    snd o strip_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `j DIV B < n` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `!m. m < G ==> G * j DIV B + m < G * n` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `G * (j DIV B + 1)` THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[LE_MULT_LCANCEL]] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `j MOD B < B` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOD_LT_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `(8 * j MOD B + s) DIV c < G` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `8 * j + s = (G * j DIV B) * c + (8 * j MOD B + s)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `j = j DIV B * B + j MOD B` MP_TAC THENL
     [ASM_MESON_TAC[DIVISION]; ALL_TAC] THEN
    UNDISCH_TAC `c * G = 8 * B` THEN
    SPEC_TAC(`j DIV B`,`q:num`) THEN SPEC_TAC(`j MOD B`,`r:num`) THEN
    CONV_TAC NUM_RING;
    ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:num->A`; `j MOD B`; `s:num`]) THEN
  ASM_SIMP_TAC[]);;

let MLD_FIPS204_FIELD_GROUPS = prove
 (`!c G B (pk:(num->byte)->num->A) (U:A->N word) (b:num->byte) m i.
        c * G = 8 * B /\ ~(G = 0) /\
        (!y k r. k < G
                 ==> (bit r (U(pk y k)) <=>
                      r < c /\
                      bit ((c * k + r) MOD 8) (y((c * k + r) DIV 8)))) /\
        c * (i + 1) <= 8 * m
        ==> mldsa_field c (list_of_seq b m) i =
            &(val(U(pk (\t. b(B * i DIV G + t)) (i MOD G))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC MLD_FIPS204_FIELD_BITS THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`\t. (b:num->byte)(B * i DIV G + t)`; `i MOD G`; `r:num`] o
   check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[MOD_LT_EQ] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `c * i + r = (B * i DIV G) * 8 + (c * i MOD G + r)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `i = i DIV G * G + i MOD G` MP_TAC THENL
     [ASM_MESON_TAC[DIVISION]; ALL_TAC] THEN
    UNDISCH_TAC `c * G = 8 * B` THEN
    SPEC_TAC(`i DIV G`,`q:num`) THEN SPEC_TAC(`i MOD G`,`p:num`) THEN
    CONV_TAC NUM_RING;
    SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_EQ]]);;

let MLD_FIPS204_POLYVEC_PACK_REGROUP = prove
 (`!P Q G B (pk:(num->int32)->num->byte) x t.
        P = Q * B /\ 256 = G * Q /\ ~(B = 0) /\
        (!a j. pk a j = pk (\m. a(G * j DIV B + m)) (j MOD B))
        ==> mld_polyvec_pack P pk x t = pk (\m. x(G * t DIV B + m)) (t MOD B)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[mld_polyvec_pack] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  REWRITE_TAC[mld_poly_of] THEN
  SUBGOAL_THEN `~(Q = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `256 = G * Q` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(t MOD P) MOD B = t MOD B /\
                256 * t DIV P + G * (t MOD P) DIV B = G * t DIV B`
  (fun th -> REWRITE_TAC[ADD_ASSOC; th]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `Q * B = B * Q` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MOD_MOD; GSYM DIV_DIV; GSYM DIV_MOD] THEN
  MP_TAC(SPECL [`t DIV B`; `Q:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`(t DIV B) DIV Q`,`a:num`) THEN
  SPEC_TAC(`(t DIV B) MOD Q`,`b:num`) THEN
  SPEC_TAC(`t DIV B`,`y:num`) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  CONV_TAC NUM_RING);;

let MLD_FIPS204_POLYVEC_UNPACK_REGROUP = prove
 (`!P Q G B (pk:(num->byte)->num->int32) b n.
        P = Q * B /\ 256 = G * Q /\ ~(G = 0) /\
        (!b i. pk b i = pk (\t. b(B * i DIV G + t)) (i MOD G))
        ==> mld_polyvec_unpack P pk b n =
            pk (\t. b(B * n DIV G + t)) (n MOD G)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[mld_polyvec_unpack; mld_polyvec] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  SUBGOAL_THEN `~(Q = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `256 = G * Q` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(n MOD 256) MOD G = n MOD G /\
                P * n DIV 256 + B * (n MOD 256) DIV G = B * n DIV G`
  (fun th -> REWRITE_TAC[ADD_ASSOC; th]) THEN
  ASM_REWRITE_TAC[MOD_MOD] THEN
  REWRITE_TAC[GSYM DIV_DIV; GSYM DIV_MOD] THEN
  MP_TAC(SPECL [`n DIV G`; `Q:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`(n DIV G) DIV Q`,`a:num`) THEN
  SPEC_TAC(`(n DIV G) MOD Q`,`b:num`) THEN
  SPEC_TAC(`n DIV G`,`y:num`) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  CONV_TAC NUM_RING);;

let MLD_FIPS204_PACK_GEN = prove
 (`!(W:A->N word) (R:A->bool) (f:A->int) c G B n (pk:(num->A)->num->byte)
    nb nc (b:num->byte) (x:num->A).
        c * G = 8 * B /\ ~(B = 0) /\ B * n = nb /\ G * n = nc /\
        (!y k s. (!m. m < G ==> val(W(y m)) < 2 EXP c) /\ k < B /\ s < 8
                 ==> (bit s (pk y k) <=>
                      bit ((8 * k + s) MOD c) (W(y((8 * k + s) DIV c))))) /\
        (!y. R y ==> val(W y) < 2 EXP c /\ &(val(W y)) = f y) /\
        (!t. t < nb ==> b t = pk (\m. x(G * t DIV B + m)) (t MOD B)) /\
        (!i. i < nc ==> R(x i))
        ==> list_of_seq b nb = mldsa_encode c nc (\i. f(x i))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
   (fun th -> is_var(rhs(concl th))))) THEN
  TRANS_TAC EQ_TRANS
   `mldsa_encode c (G * n) (\i. &(val((W:A->N word)(x i))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MLD_FIPS204_ENCODE_GROUPS THEN
    EXISTS_TAC `pk:(num->A)->num->byte` THEN ASM_SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `\m. (x:num->A)(G * t DIV B + m)` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC MLDSA_ENCODE_EQ THEN ASM_SIMP_TAC[]]);;

let MLD_FIPS204_UNPACK_GEN = prove
 (`!(U:int32->N word) (h:int->int) c G B (pk:(num->byte)->num->int32)
    (u:num->int32) (b:num->byte) nb i.
        c * G = 8 * B /\ ~(G = 0) /\ c * (i + 1) <= 8 * nb /\
        (!y k r. k < G
                 ==> (bit r (U(pk y k)) <=>
                      r < c /\
                      bit ((c * k + r) MOD 8) (y((c * k + r) DIV 8)))) /\
        (!z. val(U z) < 2 EXP c ==> ival z = h(&(val(U z)))) /\
        u i = pk (\t. b(B * i DIV G + t)) (i MOD G)
        ==> ival(u i) = h(mldsa_field c (list_of_seq b nb) i)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:num`; `G:num`; `B:num`; `pk:(num->byte)->num->int32`;
                 `U:int32->N word`; `b:num->byte`; `nb:num`; `i:num`]
         MLD_FIPS204_FIELD_GROUPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
  MP_TAC(ISPECL [`c:num`; `list_of_seq (b:num->byte) nb`; `i:num`]
         MLDSA_FIELD_BOUND) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LT] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The field values: a word with an integer value in [0,2^c) has that value  *)
(* (as val) below 2^c, and so does K - y as a word (and as a byte) when the  *)
(* integer K - y is in [0,2^c); conversely y is K minus the value of K - y.  *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_IVAL_VAL = prove
 (`!(x:N word) c. &0 <= ival x /\ ival x < &2 pow c
                  ==> val x < 2 EXP c /\ &(val x) = ival x`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `&0 <= ival(x:N word) ==> &(val x) = ival x` MP_TAC THENL
   [REWRITE_TAC[INT_IVAL] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPEC `x:N word` VAL_BOUND) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW] THEN INT_ARITH_TAC;
    REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW] THEN
    MESON_TAC[]]);;

let MLD_FIPS204_VAL_WORD_SUB = prove
 (`!(y:N word) K c.
        c < dimindex(:N) /\ &0 <= &K - ival y /\ &K - ival y < &2 pow c
        ==> val(word_sub (word K) y) < 2 EXP c /\
            &(val(word_sub (word K) y)) = &K - ival y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ival(word_sub (word K) (y:N word)) = &K - ival y`
  ASSUME_TAC THENL
   [REWRITE_TAC[WORD_IWORD] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM IWORD_IVAL] THEN
    REWRITE_TAC[GSYM IWORD_INT_SUB] THEN MATCH_MP_TAC IVAL_IWORD THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(INT_ARITH `&0 <= x:int /\ &0 <= y ==> --x <= y`) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[INT_POW_LE; INT_POS];
      TRANS_TAC INT_LTE_TRANS `(&2:int) pow c` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INT_POW_MONO THEN CONV_TAC INT_REDUCE_CONV THEN
      ASM_ARITH_TAC];
    MP_TAC(ISPECL [`word_sub (word K) (y:N word)`; `c:num`]
                  MLD_FIPS204_IVAL_VAL) THEN
    ASM_REWRITE_TAC[]]);;

let MLD_FIPS204_VAL_WORD_ZX_SUB = prove
 (`!(y:N word) K c.
        c <= 8 /\ c < dimindex(:N) /\
        &0 <= &K - ival y /\ &K - ival y < &2 pow c
        ==> val(word_zx(word_sub (word K) y):byte) < 2 EXP c /\
            &(val(word_zx(word_sub (word K) y):byte)) = &K - ival y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`y:N word`; `K:num`; `c:num`] MLD_FIPS204_VAL_WORD_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_8] THEN
  SUBGOAL_THEN `val(word_sub (word K) (y:N word)) MOD 2 EXP 8 =
                val(word_sub (word K) y)` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN TRANS_TAC LTE_TRANS `2 EXP c` THEN
    ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

let MLD_FIPS204_IVAL_WORD_SUB_VAL = prove
 (`!(v:N word) K.
        --(&2 pow (dimindex(:N) - 1)) <= &K - &(val v):int /\
        &K - &(val v):int < &2 pow (dimindex(:N) - 1)
        ==> ival(word_sub (word K) v) = &K - &(val v)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM WORD_VAL] THEN
  REWRITE_TAC[WORD_IWORD; GSYM IWORD_INT_SUB] THEN
  MATCH_MP_TAC IVAL_IWORD THEN ASM_REWRITE_TAC[]);;

let MLD_FIPS204_IVAL_SUB_INV = prove
 (`!(z:N word) K c.
        &K:int < &2 pow (dimindex(:N) - 1) /\
        (&2:int) pow c <= &K + &2 pow (dimindex(:N) - 1)
        ==> val(word_sub (word K) z) < 2 EXP c
            ==> ival z = &K - &(val(word_sub (word K) z))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
   [GSYM(ISPECL [`word K:N word`; `z:N word`] MLD_FIPS204_WORD_SUB_SUB)] THEN
  MATCH_MP_TAC MLD_FIPS204_IVAL_WORD_SUB_VAL THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW]) THEN
  ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the statements of each format below. The bits of the packing  *)
(* of one group (..._PACK_CORE): for each byte k < B and bit s < 8, rewrite  *)
(* with the bits of the word operations, the field words W(y m) of the       *)
(* group being made variables with their bits at and above c clear. The      *)
(* bits of the unpacking of one group (..._UNPACK_CORE): for each            *)
(* coefficient k < G and bit r < 32 likewise. The groups of a polynomial     *)
(* (..._REGROUP): the bytes or coefficients only depend on their group.      *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_PACK_CORE_TAC (defs:thm list) : tactic =
  let undisch v =
    FIRST_X_ASSUM(MP_TAC o check (fun th -> lhand(concl th) = v)) THEN
    SPEC_TAC(v,v) in
  let gen_tac (asl,w) =
    let ant = lhand w in
    let tms = map (fun c -> rand(rand(rand(snd(dest_forall c)))))
                  (conjuncts ant) in
    let vs = map (fun t -> genvar(type_of t)) tms in
    MAP_EVERY (fun (t,v) -> SPEC_TAC(t,v)) (zip tms vs) (asl,w) in
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP MLD_FIPS204_BIT_BOUNDS)
                             STRIP_ASSUME_TAC) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  undisch `s:num` THEN undisch `k:num` THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC defs THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN gen_tac THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[BIT_WORD_ZX; BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_USHR;
               BIT_WORD_ISHR; DIMINDEX_8; DIMINDEX_32; ARITH];;

let MLD_FIPS204_UNPACK_CORE_TAC (defs:thm list) : tactic =
  let undisch v =
    FIRST_X_ASSUM(MP_TAC o check (fun th -> lhand(concl th) = v)) THEN
    SPEC_TAC(v,v) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `r < 32` THENL
   [ALL_TAC;
    MATCH_MP_TAC(TAUT `~p /\ ~q ==> (p <=> q /\ r)`) THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[BIT_TRIVIAL; DIMINDEX_32; GSYM NOT_LT];
      ASM_ARITH_TAC]] THEN
  undisch `r:num` THEN undisch `k:num` THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC defs THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MLD_FIPS204_WORD_SUB_SUB] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[MLD_FIPS204_BIT_ZX_BYTE; BIT_WORD_OR; BIT_WORD_AND;
              BIT_WORD_SHL; BIT_WORD_USHR; BIT_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let MLD_FIPS204_MOD_DIV_SELF = prove
 (`!j n. ~(n = 0) ==> (j MOD n) DIV n = 0`,
  SIMP_TAC[DIV_LT; MOD_LT_EQ]);;

let MLD_FIPS204_REGROUP_TAC (defs:thm list) : tactic =
  REPEAT GEN_TAC THEN
  (fun (asl,w) ->
    let bt = rand(rand(rand w)) in
    let nz = EQT_ELIM(NUM_REDUCE_CONV(mk_neg(mk_eq(bt,`0`)))) in
    (REWRITE_TAC defs THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[MATCH_MP MLD_FIPS204_MOD_DIV_SELF nz; MOD_MOD_REFL;
                 MULT_CLAUSES; ADD_CLAUSES; DIV_1; MOD_1]) (asl,w));;

(* ------------------------------------------------------------------------- *)
(* The bits of the packing of one group, for each format.                    *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_POLYT1_PACK_CORE = prove
 (`!y k s. (!m. m < 4 ==> val(y m:int32) < 2 EXP 10) /\ k < 5 /\ s < 8
           ==> (bit s (mld_polyt1_pack y k) <=>
                bit ((8 * k + s) MOD 10) (y((8 * k + s) DIV 10)))`,
  MLD_FIPS204_PACK_CORE_TAC [mld_polyt1_pack]);;

let MLD_FIPS204_POLYT0_PACK_CORE = prove
 (`!y k s. (!m. m < 8
                ==> val(word_sub (word 4096) (y m):int32) < 2 EXP 13) /\
           k < 13 /\ s < 8
           ==> (bit s (mld_polyt0_pack y k) <=>
                bit ((8 * k + s) MOD 13)
                    (word_sub (word 4096) (y((8 * k + s) DIV 13))))`,
  MLD_FIPS204_PACK_CORE_TAC [mld_polyt0_pack]);;

let MLD_FIPS204_POLYETA_PACK_2_CORE = prove
 (`!y k s. (!m. m < 8
                ==> val(word_zx(word_sub (word 2) (y m:int32)):byte) <
                    2 EXP 3) /\
           k < 3 /\ s < 8
           ==> (bit s (mld_polyeta_pack_2 y k) <=>
                bit ((8 * k + s) MOD 3)
                    (word_zx(word_sub (word 2) (y((8 * k + s) DIV 3))):byte))`,
  MLD_FIPS204_PACK_CORE_TAC [mld_polyeta_pack_2]);;

let MLD_FIPS204_POLYETA_PACK_4_CORE = prove
 (`!y k s. (!m. m < 2
                ==> val(word_zx(word_sub (word 4) (y m:int32)):byte) <
                    2 EXP 4) /\
           k < 1 /\ s < 8
           ==> (bit s (mld_polyeta_pack_4 y k) <=>
                bit ((8 * k + s) MOD 4)
                    (word_zx(word_sub (word 4) (y((8 * k + s) DIV 4))):byte))`,
  MLD_FIPS204_PACK_CORE_TAC [mld_polyeta_pack_4]);;

let MLD_FIPS204_POLYZ_PACK_17_CORE = prove
 (`!y k s. (!m. m < 4
                ==> val(word_sub (word 131072) (y m):int32) < 2 EXP 18) /\
           k < 9 /\ s < 8
           ==> (bit s (mld_polyz_pack_17 y k) <=>
                bit ((8 * k + s) MOD 18)
                    (word_sub (word 131072) (y((8 * k + s) DIV 18))))`,
  MLD_FIPS204_PACK_CORE_TAC [mld_polyz_pack_17]);;

let MLD_FIPS204_POLYZ_PACK_19_CORE = prove
 (`!y k s. (!m. m < 2
                ==> val(word_sub (word 524288) (y m):int32) < 2 EXP 20) /\
           k < 5 /\ s < 8
           ==> (bit s (mld_polyz_pack_19 y k) <=>
                bit ((8 * k + s) MOD 20)
                    (word_sub (word 524288) (y((8 * k + s) DIV 20))))`,
  MLD_FIPS204_PACK_CORE_TAC [mld_polyz_pack_19]);;

let MLD_FIPS204_POLYW1_PACK_88_CORE = prove
 (`!y k s. (!m. m < 4 ==> val(y m:int32) < 2 EXP 6) /\ k < 3 /\ s < 8
           ==> (bit s (mld_polyw1_pack_88 y k) <=>
                bit ((8 * k + s) MOD 6) (y((8 * k + s) DIV 6)))`,
  MLD_FIPS204_PACK_CORE_TAC [mld_polyw1_pack_88]);;

let MLD_FIPS204_POLYW1_PACK_32_CORE = prove
 (`!y k s. (!m. m < 2 ==> val(y m:int32) < 2 EXP 4) /\ k < 1 /\ s < 8
           ==> (bit s (mld_polyw1_pack_32 y k) <=>
                bit ((8 * k + s) MOD 4) (y((8 * k + s) DIV 4)))`,
  MLD_FIPS204_PACK_CORE_TAC [mld_polyw1_pack_32]);;

(* ------------------------------------------------------------------------- *)
(* The bits of the unpacking of one group, for each format.                  *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_POLYT1_UNPACK_CORE = prove
 (`!y k r. k < 4
           ==> (bit r (mld_polyt1_unpack y k) <=>
                r < 10 /\ bit ((10 * k + r) MOD 8) (y((10 * k + r) DIV 8)))`,
  MLD_FIPS204_UNPACK_CORE_TAC [mld_polyt1_unpack]);;

let MLD_FIPS204_POLYT0_UNPACK_CORE = prove
 (`!y k r. k < 8
           ==> (bit r (word_sub (word 4096) (mld_polyt0_unpack y k)) <=>
                r < 13 /\ bit ((13 * k + r) MOD 8) (y((13 * k + r) DIV 8)))`,
  MLD_FIPS204_UNPACK_CORE_TAC [mld_polyt0_unpack]);;

let MLD_FIPS204_POLYETA_UNPACK_2_CORE = prove
 (`!y k r. k < 8
           ==> (bit r (word_sub (word 2) (mld_polyeta_unpack_2 y k)) <=>
                r < 3 /\ bit ((3 * k + r) MOD 8) (y((3 * k + r) DIV 8)))`,
  MLD_FIPS204_UNPACK_CORE_TAC [mld_polyeta_unpack_2]);;

let MLD_FIPS204_POLYETA_UNPACK_4_CORE = prove
 (`!y k r. k < 2
           ==> (bit r (word_sub (word 4) (mld_polyeta_unpack_4 y k)) <=>
                r < 4 /\ bit ((4 * k + r) MOD 8) (y((4 * k + r) DIV 8)))`,
  MLD_FIPS204_UNPACK_CORE_TAC [mld_polyeta_unpack_4]);;

let MLD_FIPS204_POLYZ_UNPACK_17_CORE = prove
 (`!y k r. k < 4
           ==> (bit r (word_sub (word 131072) (mld_polyz_unpack_17 y k)) <=>
                r < 18 /\ bit ((18 * k + r) MOD 8) (y((18 * k + r) DIV 8)))`,
  MLD_FIPS204_UNPACK_CORE_TAC [mld_polyz_unpack_17]);;

let MLD_FIPS204_POLYZ_UNPACK_19_CORE = prove
 (`!y k r. k < 2
           ==> (bit r (word_sub (word 524288) (mld_polyz_unpack_19 y k)) <=>
                r < 20 /\ bit ((20 * k + r) MOD 8) (y((20 * k + r) DIV 8)))`,
  MLD_FIPS204_UNPACK_CORE_TAC [mld_polyz_unpack_19]);;

let MLD_FIPS204_POLYW1_UNPACK_88_CORE = prove
 (`!y k r. k < 4
           ==> (bit r (mld_polyw1_unpack_88 y k) <=>
                r < 6 /\ bit ((6 * k + r) MOD 8) (y((6 * k + r) DIV 8)))`,
  MLD_FIPS204_UNPACK_CORE_TAC [mld_polyw1_unpack_88]);;

let MLD_FIPS204_POLYW1_UNPACK_32_CORE = prove
 (`!y k r. k < 2
           ==> (bit r (mld_polyw1_unpack_32 y k) <=>
                r < 4 /\ bit ((4 * k + r) MOD 8) (y((4 * k + r) DIV 8)))`,
  MLD_FIPS204_UNPACK_CORE_TAC [mld_polyw1_unpack_32]);;

(* ------------------------------------------------------------------------- *)
(* The groups of the packing and unpacking functions.                        *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_POLYT1_PACK_REGROUP = prove
 (`!a j. mld_polyt1_pack a j =
         mld_polyt1_pack (\m. a(4 * j DIV 5 + m)) (j MOD 5)`,
  MLD_FIPS204_REGROUP_TAC [mld_polyt1_pack]);;

let MLD_FIPS204_POLYT0_PACK_REGROUP = prove
 (`!a j. mld_polyt0_pack a j =
         mld_polyt0_pack (\m. a(8 * j DIV 13 + m)) (j MOD 13)`,
  MLD_FIPS204_REGROUP_TAC [mld_polyt0_pack]);;

let MLD_FIPS204_POLYETA_PACK_2_REGROUP = prove
 (`!a j. mld_polyeta_pack_2 a j =
         mld_polyeta_pack_2 (\m. a(8 * j DIV 3 + m)) (j MOD 3)`,
  MLD_FIPS204_REGROUP_TAC [mld_polyeta_pack_2]);;

let MLD_FIPS204_POLYETA_PACK_4_REGROUP = prove
 (`!a j. mld_polyeta_pack_4 a j =
         mld_polyeta_pack_4 (\m. a(2 * j DIV 1 + m)) (j MOD 1)`,
  MLD_FIPS204_REGROUP_TAC [mld_polyeta_pack_4]);;

let MLD_FIPS204_POLYZ_PACK_17_REGROUP = prove
 (`!a j. mld_polyz_pack_17 a j =
         mld_polyz_pack_17 (\m. a(4 * j DIV 9 + m)) (j MOD 9)`,
  MLD_FIPS204_REGROUP_TAC [mld_polyz_pack_17]);;

let MLD_FIPS204_POLYZ_PACK_19_REGROUP = prove
 (`!a j. mld_polyz_pack_19 a j =
         mld_polyz_pack_19 (\m. a(2 * j DIV 5 + m)) (j MOD 5)`,
  MLD_FIPS204_REGROUP_TAC [mld_polyz_pack_19]);;

let MLD_FIPS204_POLYW1_PACK_88_REGROUP = prove
 (`!a j. mld_polyw1_pack_88 a j =
         mld_polyw1_pack_88 (\m. a(4 * j DIV 3 + m)) (j MOD 3)`,
  MLD_FIPS204_REGROUP_TAC [mld_polyw1_pack_88]);;

let MLD_FIPS204_POLYW1_PACK_32_REGROUP = prove
 (`!a j. mld_polyw1_pack_32 a j =
         mld_polyw1_pack_32 (\m. a(2 * j DIV 1 + m)) (j MOD 1)`,
  MLD_FIPS204_REGROUP_TAC [mld_polyw1_pack_32]);;

let MLD_FIPS204_POLYT1_UNPACK_REGROUP = prove
 (`!b i. mld_polyt1_unpack b i =
         mld_polyt1_unpack (\t. b(5 * i DIV 4 + t)) (i MOD 4)`,
  MLD_FIPS204_REGROUP_TAC [mld_polyt1_unpack]);;

let MLD_FIPS204_POLYT0_UNPACK_REGROUP = prove
 (`!b i. mld_polyt0_unpack b i =
         mld_polyt0_unpack (\t. b(13 * i DIV 8 + t)) (i MOD 8)`,
  MLD_FIPS204_REGROUP_TAC [mld_polyt0_unpack]);;

let MLD_FIPS204_POLYETA_UNPACK_2_REGROUP = prove
 (`!b i. mld_polyeta_unpack_2 b i =
         mld_polyeta_unpack_2 (\t. b(3 * i DIV 8 + t)) (i MOD 8)`,
  MLD_FIPS204_REGROUP_TAC [mld_polyeta_unpack_2]);;

let MLD_FIPS204_POLYETA_UNPACK_4_REGROUP = prove
 (`!b i. mld_polyeta_unpack_4 b i =
         mld_polyeta_unpack_4 (\t. b(1 * i DIV 2 + t)) (i MOD 2)`,
  MLD_FIPS204_REGROUP_TAC [mld_polyeta_unpack_4]);;

let MLD_FIPS204_POLYZ_UNPACK_17_REGROUP = prove
 (`!b i. mld_polyz_unpack_17 b i =
         mld_polyz_unpack_17 (\t. b(9 * i DIV 4 + t)) (i MOD 4)`,
  MLD_FIPS204_REGROUP_TAC [mld_polyz_unpack_17]);;

let MLD_FIPS204_POLYZ_UNPACK_19_REGROUP = prove
 (`!b i. mld_polyz_unpack_19 b i =
         mld_polyz_unpack_19 (\t. b(5 * i DIV 2 + t)) (i MOD 2)`,
  MLD_FIPS204_REGROUP_TAC [mld_polyz_unpack_19]);;

let MLD_FIPS204_POLYW1_UNPACK_88_REGROUP = prove
 (`!b i. mld_polyw1_unpack_88 b i =
         mld_polyw1_unpack_88 (\t. b(3 * i DIV 4 + t)) (i MOD 4)`,
  MLD_FIPS204_REGROUP_TAC [mld_polyw1_unpack_88]);;

let MLD_FIPS204_POLYW1_UNPACK_32_REGROUP = prove
 (`!b i. mld_polyw1_unpack_32 b i =
         mld_polyw1_unpack_32 (\t. b(1 * i DIV 2 + t)) (i MOD 2)`,
  MLD_FIPS204_REGROUP_TAC [mld_polyw1_unpack_32]);;

(* ------------------------------------------------------------------------- *)
(* Tactics applying MLD_FIPS204_PACK_GEN and MLD_FIPS204_UNPACK_GEN with the *)
(* given instances of their first variables (W, R, f, c, G, B, n, pk and U,  *)
(* h, c, G, B, pk), the lemmas of the format, the tactic valtac for the      *)
(* field values and Q = P / B for vectors.                                   *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_PACK_TAC (core:thm) (regroup:thm) (valtac:tactic)
                         (inst:term list) (q:term) : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL inst MLD_FIPS204_PACK_GEN)) THEN
  REPEAT CONJ_TAC THEN
  FIRST [MATCH_ACCEPT_TAC core;
         FIRST_ASSUM MATCH_ACCEPT_TAC;
         GEN_TAC THEN DISCH_TAC THEN MATCH_ACCEPT_TAC regroup;
         GEN_TAC THEN DISCH_TAC THEN
         MATCH_MP_TAC MLD_FIPS204_POLYVEC_PACK_REGROUP THEN
         EXISTS_TAC q THEN CONV_TAC NUM_REDUCE_CONV THEN
         MATCH_ACCEPT_TAC regroup;
         GEN_TAC THEN DISCH_TAC THEN valtac;
         CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
         ARITH_TAC];;

let MLD_FIPS204_UNPACK_TAC (core:thm) (regroup:thm) (valtac:tactic)
                           (inst:term list) (q:term) : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL inst MLD_FIPS204_UNPACK_GEN)) THEN
  REPEAT CONJ_TAC THEN
  FIRST [MATCH_ACCEPT_TAC core;
         MATCH_ACCEPT_TAC regroup;
         MATCH_MP_TAC MLD_FIPS204_POLYVEC_UNPACK_REGROUP THEN
         EXISTS_TAC q THEN CONV_TAC NUM_REDUCE_CONV THEN
         MATCH_ACCEPT_TAC regroup;
         GEN_TAC THEN valtac;
         CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
         ASM_ARITH_TAC];;

let MLD_FIPS204_IVAL_VAL_TAC : tactic =
  MATCH_MP_TAC MLD_FIPS204_IVAL_VAL THEN CONV_TAC INT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[];;

let MLD_FIPS204_VAL_WORD_SUB_TAC : tactic =
  MATCH_MP_TAC MLD_FIPS204_VAL_WORD_SUB THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN ASM_REWRITE_TAC[];;

let MLD_FIPS204_VAL_WORD_ZX_SUB_TAC : tactic =
  MATCH_MP_TAC MLD_FIPS204_VAL_WORD_ZX_SUB THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN ASM_REWRITE_TAC[];;

let MLD_FIPS204_IVAL_EQ_VAL_TAC : tactic =
  DISCH_TAC THEN MATCH_MP_TAC IVAL_EQ_VAL THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;;

let MLD_FIPS204_IVAL_SUB_INV_TAC : tactic =
  MATCH_MP_TAC MLD_FIPS204_IVAL_SUB_INV THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Packing polynomials and vectors (FIPS 204 SimpleBitPack and BitPack in    *)
(* pkEncode, skEncode, sigEncode and w1Encode), given that the field values  *)
(* are in [0,2^c): for t1 (10 bits) and w1 (6 bits for gamma2 = (q - 1) /    *)
(* 88, 4 bits for gamma2 = (q - 1) / 32) the coefficients themselves, for t0 *)
(* (13 bits) 2^12 - t0, for s1 and s2 (3 bits for eta = 2, 4 bits for eta =  *)
(* 4) eta - s, and for z (18 bits for gamma1 = 2^17, 20 bits for gamma1 =    *)
(* 2^19) gamma1 - z. The contracts of the C functions give these ranges,     *)
(* tighter for s (|s| <= eta) and w1 (w1 < 44 for (q - 1) / 88). In a vector *)
(* of k polynomials, field 256 * i + j is coefficient j of polynomial i.     *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_POLYT1_PACK = prove
 (`!a. (!i. i < 256 ==> &0 <= ival(a i) /\ ival(a i) < &1024)
       ==> list_of_seq (mld_polyt1_pack a) 320 =
           mldsa_encode 10 256 (\i. ival(a i))`,
  MLD_FIPS204_PACK_TAC MLD_FIPS204_POLYT1_PACK_CORE
   MLD_FIPS204_POLYT1_PACK_REGROUP MLD_FIPS204_IVAL_VAL_TAC
   [`\y:int32. y`; `\y:int32. &0 <= ival y /\ ival y < &1024`;
    `\y:int32. ival y`; `10`; `4`; `5`; `64`; `mld_polyt1_pack`] `64`);;

let MLD_FIPS204_POLYVEC_T1_PACK = prove
 (`!k x. (!i. i < 256 * k ==> &0 <= ival(x i) /\ ival(x i) < &1024)
         ==> list_of_seq (mld_polyvec_pack 320 mld_polyt1_pack x) (320 * k) =
             mldsa_encode 10 (256 * k) (\i. ival(x i))`,
  MLD_FIPS204_PACK_TAC MLD_FIPS204_POLYT1_PACK_CORE
   MLD_FIPS204_POLYT1_PACK_REGROUP MLD_FIPS204_IVAL_VAL_TAC
   [`\y:int32. y`; `\y:int32. &0 <= ival y /\ ival y < &1024`;
    `\y:int32. ival y`; `10`; `4`; `5`; `64 * k`; `mld_polyt1_pack`]
   `64`);;

let MLD_FIPS204_POLYT0_PACK = prove
 (`!a. (!i. i < 256 ==> &0 <= &4096 - ival(a i) /\ &4096 - ival(a i) < &8192)
       ==> list_of_seq (mld_polyt0_pack a) 416 =
           mldsa_encode 13 256 (\i. &4096 - ival(a i))`,
  MLD_FIPS204_PACK_TAC MLD_FIPS204_POLYT0_PACK_CORE
   MLD_FIPS204_POLYT0_PACK_REGROUP MLD_FIPS204_VAL_WORD_SUB_TAC
   [`\y:int32. word_sub (word 4096) y`;
    `\y:int32. &0 <= &4096 - ival y /\ &4096 - ival y < &8192`;
    `\y:int32. &4096 - ival y`; `13`; `8`; `13`; `32`; `mld_polyt0_pack`]
   `32`);;

let MLD_FIPS204_POLYVEC_T0_PACK = prove
 (`!k x. (!i. i < 256 * k
              ==> &0 <= &4096 - ival(x i) /\ &4096 - ival(x i) < &8192)
         ==> list_of_seq (mld_polyvec_pack 416 mld_polyt0_pack x) (416 * k) =
             mldsa_encode 13 (256 * k) (\i. &4096 - ival(x i))`,
  MLD_FIPS204_PACK_TAC MLD_FIPS204_POLYT0_PACK_CORE
   MLD_FIPS204_POLYT0_PACK_REGROUP MLD_FIPS204_VAL_WORD_SUB_TAC
   [`\y:int32. word_sub (word 4096) y`;
    `\y:int32. &0 <= &4096 - ival y /\ &4096 - ival y < &8192`;
    `\y:int32. &4096 - ival y`; `13`; `8`; `13`; `32 * k`;
    `mld_polyt0_pack`]
   `32`);;

let MLD_FIPS204_POLYETA_PACK_2 = prove
 (`!a. (!i. i < 256 ==> &0 <= &2 - ival(a i) /\ &2 - ival(a i) < &8)
       ==> list_of_seq (mld_polyeta_pack_2 a) 96 =
           mldsa_encode 3 256 (\i. &2 - ival(a i))`,
  MLD_FIPS204_PACK_TAC MLD_FIPS204_POLYETA_PACK_2_CORE
   MLD_FIPS204_POLYETA_PACK_2_REGROUP MLD_FIPS204_VAL_WORD_ZX_SUB_TAC
   [`\y:int32. word_zx(word_sub (word 2) y):byte`;
    `\y:int32. &0 <= &2 - ival y /\ &2 - ival y < &8`;
    `\y:int32. &2 - ival y`; `3`; `8`; `3`; `32`; `mld_polyeta_pack_2`]
   `32`);;

let MLD_FIPS204_POLYVEC_ETA_PACK_2 = prove
 (`!k x. (!i. i < 256 * k ==> &0 <= &2 - ival(x i) /\ &2 - ival(x i) < &8)
         ==> list_of_seq (mld_polyvec_pack 96 mld_polyeta_pack_2 x) (96 * k) =
             mldsa_encode 3 (256 * k) (\i. &2 - ival(x i))`,
  MLD_FIPS204_PACK_TAC MLD_FIPS204_POLYETA_PACK_2_CORE
   MLD_FIPS204_POLYETA_PACK_2_REGROUP MLD_FIPS204_VAL_WORD_ZX_SUB_TAC
   [`\y:int32. word_zx(word_sub (word 2) y):byte`;
    `\y:int32. &0 <= &2 - ival y /\ &2 - ival y < &8`;
    `\y:int32. &2 - ival y`; `3`; `8`; `3`; `32 * k`; `mld_polyeta_pack_2`]
   `32`);;

let MLD_FIPS204_POLYETA_PACK_4 = prove
 (`!a. (!i. i < 256 ==> &0 <= &4 - ival(a i) /\ &4 - ival(a i) < &16)
       ==> list_of_seq (mld_polyeta_pack_4 a) 128 =
           mldsa_encode 4 256 (\i. &4 - ival(a i))`,
  MLD_FIPS204_PACK_TAC MLD_FIPS204_POLYETA_PACK_4_CORE
   MLD_FIPS204_POLYETA_PACK_4_REGROUP MLD_FIPS204_VAL_WORD_ZX_SUB_TAC
   [`\y:int32. word_zx(word_sub (word 4) y):byte`;
    `\y:int32. &0 <= &4 - ival y /\ &4 - ival y < &16`;
    `\y:int32. &4 - ival y`; `4`; `2`; `1`; `128`; `mld_polyeta_pack_4`]
   `128`);;

let MLD_FIPS204_POLYVEC_ETA_PACK_4 = prove
 (`!k x. (!i. i < 256 * k ==> &0 <= &4 - ival(x i) /\ &4 - ival(x i) < &16)
         ==> list_of_seq (mld_polyvec_pack 128 mld_polyeta_pack_4 x)
                         (128 * k) =
             mldsa_encode 4 (256 * k) (\i. &4 - ival(x i))`,
  MLD_FIPS204_PACK_TAC MLD_FIPS204_POLYETA_PACK_4_CORE
   MLD_FIPS204_POLYETA_PACK_4_REGROUP MLD_FIPS204_VAL_WORD_ZX_SUB_TAC
   [`\y:int32. word_zx(word_sub (word 4) y):byte`;
    `\y:int32. &0 <= &4 - ival y /\ &4 - ival y < &16`;
    `\y:int32. &4 - ival y`; `4`; `2`; `1`; `128 * k`;
    `mld_polyeta_pack_4`]
   `128`);;

let MLD_FIPS204_POLYZ_PACK_17 = prove
 (`!a. (!i. i < 256
            ==> &0 <= &131072 - ival(a i) /\ &131072 - ival(a i) < &262144)
       ==> list_of_seq (mld_polyz_pack_17 a) 576 =
           mldsa_encode 18 256 (\i. &131072 - ival(a i))`,
  MLD_FIPS204_PACK_TAC MLD_FIPS204_POLYZ_PACK_17_CORE
   MLD_FIPS204_POLYZ_PACK_17_REGROUP MLD_FIPS204_VAL_WORD_SUB_TAC
   [`\y:int32. word_sub (word 131072) y`;
    `\y:int32. &0 <= &131072 - ival y /\ &131072 - ival y < &262144`;
    `\y:int32. &131072 - ival y`; `18`; `4`; `9`; `64`;
    `mld_polyz_pack_17`]
   `64`);;

let MLD_FIPS204_POLYVEC_Z_PACK_17 = prove
 (`!k x. (!i. i < 256 * k
              ==> &0 <= &131072 - ival(x i) /\
                  &131072 - ival(x i) < &262144)
         ==> list_of_seq (mld_polyvec_pack 576 mld_polyz_pack_17 x)
                         (576 * k) =
             mldsa_encode 18 (256 * k) (\i. &131072 - ival(x i))`,
  MLD_FIPS204_PACK_TAC MLD_FIPS204_POLYZ_PACK_17_CORE
   MLD_FIPS204_POLYZ_PACK_17_REGROUP MLD_FIPS204_VAL_WORD_SUB_TAC
   [`\y:int32. word_sub (word 131072) y`;
    `\y:int32. &0 <= &131072 - ival y /\ &131072 - ival y < &262144`;
    `\y:int32. &131072 - ival y`; `18`; `4`; `9`; `64 * k`;
    `mld_polyz_pack_17`]
   `64`);;

let MLD_FIPS204_POLYZ_PACK_19 = prove
 (`!a. (!i. i < 256
            ==> &0 <= &524288 - ival(a i) /\ &524288 - ival(a i) < &1048576)
       ==> list_of_seq (mld_polyz_pack_19 a) 640 =
           mldsa_encode 20 256 (\i. &524288 - ival(a i))`,
  MLD_FIPS204_PACK_TAC MLD_FIPS204_POLYZ_PACK_19_CORE
   MLD_FIPS204_POLYZ_PACK_19_REGROUP MLD_FIPS204_VAL_WORD_SUB_TAC
   [`\y:int32. word_sub (word 524288) y`;
    `\y:int32. &0 <= &524288 - ival y /\ &524288 - ival y < &1048576`;
    `\y:int32. &524288 - ival y`; `20`; `2`; `5`; `128`;
    `mld_polyz_pack_19`]
   `128`);;

let MLD_FIPS204_POLYVEC_Z_PACK_19 = prove
 (`!k x. (!i. i < 256 * k
              ==> &0 <= &524288 - ival(x i) /\
                  &524288 - ival(x i) < &1048576)
         ==> list_of_seq (mld_polyvec_pack 640 mld_polyz_pack_19 x)
                         (640 * k) =
             mldsa_encode 20 (256 * k) (\i. &524288 - ival(x i))`,
  MLD_FIPS204_PACK_TAC MLD_FIPS204_POLYZ_PACK_19_CORE
   MLD_FIPS204_POLYZ_PACK_19_REGROUP MLD_FIPS204_VAL_WORD_SUB_TAC
   [`\y:int32. word_sub (word 524288) y`;
    `\y:int32. &0 <= &524288 - ival y /\ &524288 - ival y < &1048576`;
    `\y:int32. &524288 - ival y`; `20`; `2`; `5`; `128 * k`;
    `mld_polyz_pack_19`]
   `128`);;

let MLD_FIPS204_POLYW1_PACK_88 = prove
 (`!a. (!i. i < 256 ==> &0 <= ival(a i) /\ ival(a i) < &64)
       ==> list_of_seq (mld_polyw1_pack_88 a) 192 =
           mldsa_encode 6 256 (\i. ival(a i))`,
  MLD_FIPS204_PACK_TAC MLD_FIPS204_POLYW1_PACK_88_CORE
   MLD_FIPS204_POLYW1_PACK_88_REGROUP MLD_FIPS204_IVAL_VAL_TAC
   [`\y:int32. y`; `\y:int32. &0 <= ival y /\ ival y < &64`;
    `\y:int32. ival y`; `6`; `4`; `3`; `64`; `mld_polyw1_pack_88`] `64`);;

let MLD_FIPS204_POLYVEC_W1_PACK_88 = prove
 (`!k x. (!i. i < 256 * k ==> &0 <= ival(x i) /\ ival(x i) < &64)
         ==> list_of_seq (mld_polyvec_pack 192 mld_polyw1_pack_88 x)
                         (192 * k) =
             mldsa_encode 6 (256 * k) (\i. ival(x i))`,
  MLD_FIPS204_PACK_TAC MLD_FIPS204_POLYW1_PACK_88_CORE
   MLD_FIPS204_POLYW1_PACK_88_REGROUP MLD_FIPS204_IVAL_VAL_TAC
   [`\y:int32. y`; `\y:int32. &0 <= ival y /\ ival y < &64`;
    `\y:int32. ival y`; `6`; `4`; `3`; `64 * k`; `mld_polyw1_pack_88`]
   `64`);;

let MLD_FIPS204_POLYW1_PACK_32 = prove
 (`!a. (!i. i < 256 ==> &0 <= ival(a i) /\ ival(a i) < &16)
       ==> list_of_seq (mld_polyw1_pack_32 a) 128 =
           mldsa_encode 4 256 (\i. ival(a i))`,
  MLD_FIPS204_PACK_TAC MLD_FIPS204_POLYW1_PACK_32_CORE
   MLD_FIPS204_POLYW1_PACK_32_REGROUP MLD_FIPS204_IVAL_VAL_TAC
   [`\y:int32. y`; `\y:int32. &0 <= ival y /\ ival y < &16`;
    `\y:int32. ival y`; `4`; `2`; `1`; `128`; `mld_polyw1_pack_32`]
   `128`);;

let MLD_FIPS204_POLYVEC_W1_PACK_32 = prove
 (`!k x. (!i. i < 256 * k ==> &0 <= ival(x i) /\ ival(x i) < &16)
         ==> list_of_seq (mld_polyvec_pack 128 mld_polyw1_pack_32 x)
                         (128 * k) =
             mldsa_encode 4 (256 * k) (\i. ival(x i))`,
  MLD_FIPS204_PACK_TAC MLD_FIPS204_POLYW1_PACK_32_CORE
   MLD_FIPS204_POLYW1_PACK_32_REGROUP MLD_FIPS204_IVAL_VAL_TAC
   [`\y:int32. y`; `\y:int32. &0 <= ival y /\ ival y < &16`;
    `\y:int32. ival y`; `4`; `2`; `1`; `128 * k`; `mld_polyw1_pack_32`]
   `128`);;

(* The packing of a function of the coefficients, as in the packing of the   *)
(* high parts of w (mld_polyw1_pack_88 o mld_poly_decompose_hi_88).          *)

let MLD_FIPS204_POLYVEC_PACK_O = prove
 (`!P (pk:(num->int32)->num->byte) f (g:int32->int32) x.
        (!a i. f a i = g(a i))
        ==> mld_polyvec_pack P (pk o f) x = mld_polyvec_pack P pk (\n. g(x n))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; mld_polyvec_pack; o_THM; mld_poly_of] THEN
  GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[FUN_EQ_THM]);;

(* ------------------------------------------------------------------------- *)
(* Unpacking polynomials and vectors (FIPS 204 SimpleBitUnpack and           *)
(* BitUnpack in pkDecode, skDecode and sigDecode), for all byte arrays: the  *)
(* integer value of each coefficient is the field (t1, w1) or K - field      *)
(* (2^12 for t0, eta for s1 and s2, gamma1 for z). Also the slices of byte   *)
(* strings, where FIPS 204 reads the parts of keys and signatures.           *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_POLYT1_UNPACK = prove
 (`!b i. i < 256
         ==> ival(mld_polyt1_unpack b i) =
             mldsa_field 10 (list_of_seq b 320) i`,
  MLD_FIPS204_UNPACK_TAC MLD_FIPS204_POLYT1_UNPACK_CORE
   MLD_FIPS204_POLYT1_UNPACK_REGROUP MLD_FIPS204_IVAL_EQ_VAL_TAC
   [`\y:int32. y`; `\v:int. v`; `10`; `4`; `5`; `mld_polyt1_unpack`]
   `64`);;

let MLD_FIPS204_POLYVEC_T1_UNPACK = prove
 (`!k b n. n < 256 * k
           ==> ival(mld_polyvec_unpack 320 mld_polyt1_unpack b n) =
               mldsa_field 10 (list_of_seq b (320 * k)) n`,
  MLD_FIPS204_UNPACK_TAC MLD_FIPS204_POLYT1_UNPACK_CORE
   MLD_FIPS204_POLYT1_UNPACK_REGROUP MLD_FIPS204_IVAL_EQ_VAL_TAC
   [`\y:int32. y`; `\v:int. v`; `10`; `4`; `5`; `mld_polyt1_unpack`]
   `64`);;

let MLD_FIPS204_POLYT0_UNPACK = prove
 (`!b i. i < 256
         ==> ival(mld_polyt0_unpack b i) =
             &4096 - mldsa_field 13 (list_of_seq b 416) i`,
  MLD_FIPS204_UNPACK_TAC MLD_FIPS204_POLYT0_UNPACK_CORE
   MLD_FIPS204_POLYT0_UNPACK_REGROUP MLD_FIPS204_IVAL_SUB_INV_TAC
   [`\y:int32. word_sub (word 4096) y`; `\v:int. &4096 - v`; `13`; `8`;
    `13`; `mld_polyt0_unpack`]
   `32`);;

let MLD_FIPS204_POLYVEC_T0_UNPACK = prove
 (`!k b n. n < 256 * k
           ==> ival(mld_polyvec_unpack 416 mld_polyt0_unpack b n) =
               &4096 - mldsa_field 13 (list_of_seq b (416 * k)) n`,
  MLD_FIPS204_UNPACK_TAC MLD_FIPS204_POLYT0_UNPACK_CORE
   MLD_FIPS204_POLYT0_UNPACK_REGROUP MLD_FIPS204_IVAL_SUB_INV_TAC
   [`\y:int32. word_sub (word 4096) y`; `\v:int. &4096 - v`; `13`; `8`;
    `13`; `mld_polyt0_unpack`]
   `32`);;

let MLD_FIPS204_POLYETA_UNPACK_2 = prove
 (`!b i. i < 256
         ==> ival(mld_polyeta_unpack_2 b i) =
             &2 - mldsa_field 3 (list_of_seq b 96) i`,
  MLD_FIPS204_UNPACK_TAC MLD_FIPS204_POLYETA_UNPACK_2_CORE
   MLD_FIPS204_POLYETA_UNPACK_2_REGROUP MLD_FIPS204_IVAL_SUB_INV_TAC
   [`\y:int32. word_sub (word 2) y`; `\v:int. &2 - v`; `3`; `8`; `3`;
    `mld_polyeta_unpack_2`]
   `32`);;

let MLD_FIPS204_POLYVEC_ETA_UNPACK_2 = prove
 (`!k b n. n < 256 * k
           ==> ival(mld_polyvec_unpack 96 mld_polyeta_unpack_2 b n) =
               &2 - mldsa_field 3 (list_of_seq b (96 * k)) n`,
  MLD_FIPS204_UNPACK_TAC MLD_FIPS204_POLYETA_UNPACK_2_CORE
   MLD_FIPS204_POLYETA_UNPACK_2_REGROUP MLD_FIPS204_IVAL_SUB_INV_TAC
   [`\y:int32. word_sub (word 2) y`; `\v:int. &2 - v`; `3`; `8`; `3`;
    `mld_polyeta_unpack_2`]
   `32`);;

let MLD_FIPS204_POLYETA_UNPACK_4 = prove
 (`!b i. i < 256
         ==> ival(mld_polyeta_unpack_4 b i) =
             &4 - mldsa_field 4 (list_of_seq b 128) i`,
  MLD_FIPS204_UNPACK_TAC MLD_FIPS204_POLYETA_UNPACK_4_CORE
   MLD_FIPS204_POLYETA_UNPACK_4_REGROUP MLD_FIPS204_IVAL_SUB_INV_TAC
   [`\y:int32. word_sub (word 4) y`; `\v:int. &4 - v`; `4`; `2`; `1`;
    `mld_polyeta_unpack_4`]
   `128`);;

let MLD_FIPS204_POLYVEC_ETA_UNPACK_4 = prove
 (`!k b n. n < 256 * k
           ==> ival(mld_polyvec_unpack 128 mld_polyeta_unpack_4 b n) =
               &4 - mldsa_field 4 (list_of_seq b (128 * k)) n`,
  MLD_FIPS204_UNPACK_TAC MLD_FIPS204_POLYETA_UNPACK_4_CORE
   MLD_FIPS204_POLYETA_UNPACK_4_REGROUP MLD_FIPS204_IVAL_SUB_INV_TAC
   [`\y:int32. word_sub (word 4) y`; `\v:int. &4 - v`; `4`; `2`; `1`;
    `mld_polyeta_unpack_4`]
   `128`);;

let MLD_FIPS204_POLYZ_UNPACK_17 = prove
 (`!b i. i < 256
         ==> ival(mld_polyz_unpack_17 b i) =
             &131072 - mldsa_field 18 (list_of_seq b 576) i`,
  MLD_FIPS204_UNPACK_TAC MLD_FIPS204_POLYZ_UNPACK_17_CORE
   MLD_FIPS204_POLYZ_UNPACK_17_REGROUP MLD_FIPS204_IVAL_SUB_INV_TAC
   [`\y:int32. word_sub (word 131072) y`; `\v:int. &131072 - v`; `18`;
    `4`; `9`; `mld_polyz_unpack_17`]
   `64`);;

let MLD_FIPS204_POLYVEC_Z_UNPACK_17 = prove
 (`!k b n. n < 256 * k
           ==> ival(mld_polyvec_unpack 576 mld_polyz_unpack_17 b n) =
               &131072 - mldsa_field 18 (list_of_seq b (576 * k)) n`,
  MLD_FIPS204_UNPACK_TAC MLD_FIPS204_POLYZ_UNPACK_17_CORE
   MLD_FIPS204_POLYZ_UNPACK_17_REGROUP MLD_FIPS204_IVAL_SUB_INV_TAC
   [`\y:int32. word_sub (word 131072) y`; `\v:int. &131072 - v`; `18`;
    `4`; `9`; `mld_polyz_unpack_17`]
   `64`);;

let MLD_FIPS204_POLYZ_UNPACK_19 = prove
 (`!b i. i < 256
         ==> ival(mld_polyz_unpack_19 b i) =
             &524288 - mldsa_field 20 (list_of_seq b 640) i`,
  MLD_FIPS204_UNPACK_TAC MLD_FIPS204_POLYZ_UNPACK_19_CORE
   MLD_FIPS204_POLYZ_UNPACK_19_REGROUP MLD_FIPS204_IVAL_SUB_INV_TAC
   [`\y:int32. word_sub (word 524288) y`; `\v:int. &524288 - v`; `20`;
    `2`; `5`; `mld_polyz_unpack_19`]
   `128`);;

let MLD_FIPS204_POLYVEC_Z_UNPACK_19 = prove
 (`!k b n. n < 256 * k
           ==> ival(mld_polyvec_unpack 640 mld_polyz_unpack_19 b n) =
               &524288 - mldsa_field 20 (list_of_seq b (640 * k)) n`,
  MLD_FIPS204_UNPACK_TAC MLD_FIPS204_POLYZ_UNPACK_19_CORE
   MLD_FIPS204_POLYZ_UNPACK_19_REGROUP MLD_FIPS204_IVAL_SUB_INV_TAC
   [`\y:int32. word_sub (word 524288) y`; `\v:int. &524288 - v`; `20`;
    `2`; `5`; `mld_polyz_unpack_19`]
   `128`);;

let MLD_FIPS204_POLYW1_UNPACK_88 = prove
 (`!b i. i < 256
         ==> ival(mld_polyw1_unpack_88 b i) =
             mldsa_field 6 (list_of_seq b 192) i`,
  MLD_FIPS204_UNPACK_TAC MLD_FIPS204_POLYW1_UNPACK_88_CORE
   MLD_FIPS204_POLYW1_UNPACK_88_REGROUP MLD_FIPS204_IVAL_EQ_VAL_TAC
   [`\y:int32. y`; `\v:int. v`; `6`; `4`; `3`; `mld_polyw1_unpack_88`]
   `64`);;

let MLD_FIPS204_POLYVEC_W1_UNPACK_88 = prove
 (`!k b n. n < 256 * k
           ==> ival(mld_polyvec_unpack 192 mld_polyw1_unpack_88 b n) =
               mldsa_field 6 (list_of_seq b (192 * k)) n`,
  MLD_FIPS204_UNPACK_TAC MLD_FIPS204_POLYW1_UNPACK_88_CORE
   MLD_FIPS204_POLYW1_UNPACK_88_REGROUP MLD_FIPS204_IVAL_EQ_VAL_TAC
   [`\y:int32. y`; `\v:int. v`; `6`; `4`; `3`; `mld_polyw1_unpack_88`]
   `64`);;

let MLD_FIPS204_POLYW1_UNPACK_32 = prove
 (`!b i. i < 256
         ==> ival(mld_polyw1_unpack_32 b i) =
             mldsa_field 4 (list_of_seq b 128) i`,
  MLD_FIPS204_UNPACK_TAC MLD_FIPS204_POLYW1_UNPACK_32_CORE
   MLD_FIPS204_POLYW1_UNPACK_32_REGROUP MLD_FIPS204_IVAL_EQ_VAL_TAC
   [`\y:int32. y`; `\v:int. v`; `4`; `2`; `1`; `mld_polyw1_unpack_32`]
   `128`);;

let MLD_FIPS204_POLYVEC_W1_UNPACK_32 = prove
 (`!k b n. n < 256 * k
           ==> ival(mld_polyvec_unpack 128 mld_polyw1_unpack_32 b n) =
               mldsa_field 4 (list_of_seq b (128 * k)) n`,
  MLD_FIPS204_UNPACK_TAC MLD_FIPS204_POLYW1_UNPACK_32_CORE
   MLD_FIPS204_POLYW1_UNPACK_32_REGROUP MLD_FIPS204_IVAL_EQ_VAL_TAC
   [`\y:int32. y`; `\v:int. v`; `4`; `2`; `1`; `mld_polyw1_unpack_32`]
   `128`);;

let MLD_FIPS204_SLICE_LIST_OF_SEQ = prove
 (`!a n m (b:num->byte).
        a + n <= m
        ==> mldsa_slice a n (list_of_seq b m) = list_of_seq (\i. b(a + i)) n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mldsa_slice; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_LIST_OF_SEQ] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EL_LIST_OF_SEQ THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Unpacking what was packed (as the C code does for s2 in key generation    *)
(* and for w1 in the hints of signing), and the vectors at an offset of l    *)
(* polynomials, such as s2 after the l polynomials of s1.                    *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_UNPACK_PACK_TAC (unpackth:thm) (packth:thm) (p:term)
                                (pk:term) (c:term) (f:term) : tactic =
  let ls = vsubst [p,`P:num`; pk,`pk:(num->int32)->num->byte`]
   `list_of_seq (b:num->byte) (P * k) =
    list_of_seq (mld_polyvec_pack P pk (x:num->int32)) (P * k)` in
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IVAL_EQ] THEN
  ASM_SIMP_TAC[unpackth] THEN
  SUBGOAL_THEN ls SUBST1_TAC THENL
   [REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN SIMP_TAC[EL_LIST_OF_SEQ]
    THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[packth] THEN
  MP_TAC(ISPECL [c; `256 * k`; f; `n:num`] MLDSA_FIELD_ENCODE_SMALL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[divides] THEN EXISTS_TAC (mk_binop `( * ):num->num->num`
        c `32 * k`) THEN ARITH_TAC;
      ASM_REWRITE_TAC[];
      CONV_TAC INT_REDUCE_CONV THEN ASM_SIMP_TAC[];
      CONV_TAC INT_REDUCE_CONV THEN ASM_SIMP_TAC[]];
    DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC];;

let MLD_FIPS204_POLYVEC_ETA_UNPACK_PACK_2 = prove
 (`!k x b n.
        (!i. i < 256 * k ==> &0 <= &2 - ival(x i) /\ &2 - ival(x i) < &8) /\
        (!j. j < 96 * k ==> b j = mld_polyvec_pack 96 mld_polyeta_pack_2 x j) /\
        n < 256 * k
        ==> mld_polyvec_unpack 96 mld_polyeta_unpack_2 b n = x n`,
  MLD_FIPS204_UNPACK_PACK_TAC MLD_FIPS204_POLYVEC_ETA_UNPACK_2
   MLD_FIPS204_POLYVEC_ETA_PACK_2 `96` `mld_polyeta_pack_2` `3`
   `\i. &2 - ival((x:num->int32) i)`);;

let MLD_FIPS204_POLYVEC_ETA_UNPACK_PACK_4 = prove
 (`!k x b n.
        (!i. i < 256 * k ==> &0 <= &4 - ival(x i) /\ &4 - ival(x i) < &16) /\
        (!j. j < 128 * k
             ==> b j = mld_polyvec_pack 128 mld_polyeta_pack_4 x j) /\
        n < 256 * k
        ==> mld_polyvec_unpack 128 mld_polyeta_unpack_4 b n = x n`,
  MLD_FIPS204_UNPACK_PACK_TAC MLD_FIPS204_POLYVEC_ETA_UNPACK_4
   MLD_FIPS204_POLYVEC_ETA_PACK_4 `128` `mld_polyeta_pack_4` `4`
   `\i. &4 - ival((x:num->int32) i)`);;

let MLD_FIPS204_POLYVEC_W1_UNPACK_PACK_88 = prove
 (`!k x b n.
        (!i. i < 256 * k ==> &0 <= ival(x i) /\ ival(x i) < &64) /\
        (!j. j < 192 * k
             ==> b j = mld_polyvec_pack 192 mld_polyw1_pack_88 x j) /\
        n < 256 * k
        ==> mld_polyvec_unpack 192 mld_polyw1_unpack_88 b n = x n`,
  MLD_FIPS204_UNPACK_PACK_TAC MLD_FIPS204_POLYVEC_W1_UNPACK_88
   MLD_FIPS204_POLYVEC_W1_PACK_88 `192` `mld_polyw1_pack_88` `6`
   `\i. ival((x:num->int32) i)`);;

let MLD_FIPS204_POLYVEC_W1_UNPACK_PACK_32 = prove
 (`!k x b n.
        (!i. i < 256 * k ==> &0 <= ival(x i) /\ ival(x i) < &16) /\
        (!j. j < 128 * k
             ==> b j = mld_polyvec_pack 128 mld_polyw1_pack_32 x j) /\
        n < 256 * k
        ==> mld_polyvec_unpack 128 mld_polyw1_unpack_32 b n = x n`,
  MLD_FIPS204_UNPACK_PACK_TAC MLD_FIPS204_POLYVEC_W1_UNPACK_32
   MLD_FIPS204_POLYVEC_W1_PACK_32 `128` `mld_polyw1_pack_32` `4`
   `\i. ival((x:num->int32) i)`);;

let MLD_FIPS204_POLYVEC_PACK_SHIFT = prove
 (`!P (pk:(num->int32)->num->byte) x l j.
        ~(P = 0)
        ==> mld_polyvec_pack P pk x (P * l + j) =
            mld_polyvec_pack P pk (\n. x(256 * l + n)) j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyvec_pack; mld_poly_of] THEN
  SUBGOAL_THEN `(P * l + j) DIV P = l + j DIV P /\
                (P * l + j) MOD P = j MOD P`
  (fun th -> REWRITE_TAC[th]) THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD];
    REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC]]);;

let MLD_FIPS204_POLYVEC_UNPACK_SHIFT = prove
 (`!P (pk:(num->byte)->num->int32) b l n.
        mld_polyvec_unpack P pk (\t. b(P * l + t)) n =
        mld_polyvec_unpack P pk b (256 * l + n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_polyvec_unpack; mld_polyvec] THEN
  SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_EQ;
           ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT_ADD;
           ONCE_REWRITE_RULE[MULT_SYM] MOD_MULT_ADD] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* The counts of hints of fips204.ml: mldsa_hint_count h p grows by one at   *)
(* each hint, so the hint with count t < mldsa_hint_count h p is unique and  *)
(* below p, and a hint is below a position exactly when its count is below   *)
(* the count there. A strictly increasing sequence q of n positions has the  *)
(* counts CARD {t | t < n /\ q t < p}. The block of t for nondecreasing      *)
(* bounds S 0 = 0 <= S 1 <= ... <= S k is the i with S i <= t < S(i + 1).    *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_HINT_COUNT_CLAUSES = prove
 (`(!h. mldsa_hint_count h 0 = 0) /\
   (!h p. mldsa_hint_count h (SUC p) =
          mldsa_hint_count h p + (if h p then 1 else 0))`,
  REWRITE_TAC[mldsa_hint_count; LT; EMPTY_GSPEC; CARD_CLAUSES] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `{p' | (p' = p \/ p' < p) /\ h p'} =
    if h p then p INSERT {p' | p' < p /\ h p'} else {p' | p' < p /\ h p'}`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {p' | p' < p /\ (h:num->bool) p'}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p':num | p' < p}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[CARD_CLAUSES; IN_ELIM_THM; LT_REFL] THEN
  ARITH_TAC);;

let MLD_FIPS204_HINT_COUNT_MONO = prove
 (`!h p q. p <= q ==> mldsa_hint_count h p <= mldsa_hint_count h q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_hint_count] THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[LTE_TRANS];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p':num | p' < q}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]]);;

let MLD_FIPS204_HINT_COUNT_STRICT = prove
 (`!h p q. p < q /\ h p ==> mldsa_hint_count h p < mldsa_hint_count h q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`h:num->bool`; `SUC p`; `q:num`]
    MLD_FIPS204_HINT_COUNT_MONO) THEN
  ASM_REWRITE_TAC[MLD_FIPS204_HINT_COUNT_CLAUSES; LE_SUC_LT] THEN
  ARITH_TAC);;

let MLD_FIPS204_HINT_COUNT_LT = prove
 (`!h p q. h p ==> (p < q <=> mldsa_hint_count h p < mldsa_hint_count h q)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[MLD_FIPS204_HINT_COUNT_STRICT]
  THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_LT; MLD_FIPS204_HINT_COUNT_MONO]);;

let MLD_FIPS204_HINT_COUNT_INJ = prove
 (`!h p q. h p /\ h q /\ mldsa_hint_count h p = mldsa_hint_count h q
           ==> p = q`,
  REPEAT STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPECL [`p:num`; `q:num`] LT_CASES)
  THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MLD_FIPS204_HINT_COUNT_STRICT; LT_REFL]);;

let MLD_FIPS204_HINT_COUNT_IVT = prove
 (`!h p t. t < mldsa_hint_count h p
           ==> ?q. q < p /\ h q /\ mldsa_hint_count h q = t`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[MLD_FIPS204_HINT_COUNT_CLAUSES; LT] THEN
  X_GEN_TAC `t:num` THEN
  ASM_CASES_TAC `t < mldsa_hint_count h p` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_TAC THEN EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let MLD_FIPS204_HINT_COUNT_EQ = prove
 (`!h h' p. (!p'. p' < p ==> (h p' <=> h' p'))
            ==> mldsa_hint_count h p = mldsa_hint_count h' p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_hint_count] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

let MLD_FIPS204_HINT_COUNT_SEQ = prove
 (`!(q:num->num) n (h:num->bool) p.
        (!t t'. t < t' /\ t' < n ==> q t < q t') /\
        (!p. h p <=> ?t. t < n /\ q t = p)
        ==> mldsa_hint_count h p = CARD {t | t < n /\ q t < p}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_hint_count] THEN
  SUBGOAL_THEN `{p' | p' < p /\ h p'} = IMAGE q {t | t < n /\ q t < p}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CARD_IMAGE_INJ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`t:num`; `t':num`] THEN STRIP_TAC THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
       (SPECL [`t:num`; `t':num`] LT_CASES) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LT_REFL];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{t:num | t < n}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]]]);;

let MLD_FIPS204_STEP_MONO = prove
 (`!(S:num->num) k.
        (!i. i < k ==> S i <= S(i + 1))
        ==> !i j. i <= j /\ j <= k ==> S i <= S j`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC[LE; LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[LE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(S:num->num) j` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let MLD_FIPS204_BLOCK = prove
 (`!(S:num->num) k t.
        S 0 = 0 /\ (!i. i < k ==> S i <= S(i + 1)) /\ t < S k
        ==> (minimal i. t < S(i + 1)) < k /\
            S(minimal i. t < S(i + 1)) <= t /\
            t < S((minimal i. t < S(i + 1)) + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `t < (S:num->num) k` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `\i. t < (S:num->num)(i + 1)` MINIMAL) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `?i. t < (S:num->num)(i + 1)` (fun th -> REWRITE_TAC[th]) THENL
   [EXISTS_TAC `k - 1` THEN ASM_SIMP_TAC[SUB_ADD; LE_1]; ALL_TAC] THEN
  ABBREV_TAC `m = minimal i. t < (S:num->num)(i + 1)` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k - 1`) THEN
    ASM_SIMP_TAC[SUB_ADD; LE_1] THEN ASM_ARITH_TAC;
    ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[LE_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m - 1`) THEN
    ASM_SIMP_TAC[SUB_ADD; LE_1] THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; ARITH_TAC]]);;

let MLD_FIPS204_BLOCK_UNIQUE = prove
 (`!(S:num->num) k t i.
        (!i. i < k ==> S i <= S(i + 1)) /\
        i < k /\ S i <= t /\ t < S(i + 1)
        ==> (minimal i. t < S(i + 1)) = i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MINIMAL_UNIQUE THEN
  ASM_REWRITE_TAC[NOT_LT] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  TRANS_TAC LE_TRANS `(S:num->num) i` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`S:num->num`; `k:num`] MLD_FIPS204_STEP_MONO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let MLD_FIPS204_DIGIT256 = prove
 (`!b v. v < 256 ==> (256 * b + v) DIV 256 = b /\ (256 * b + v) MOD 256 = v`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT; ARITH_EQ;
           ADD_CLAUSES]);;

let MLD_FIPS204_HINTBITPACK_EL = prove
 (`!k omega h t.
        t < omega + k
        ==> EL t (mldsa_hintbitpack k omega h) =
            if t < omega then
              if t < mldsa_hint_count h (256 * k)
              then word((@p. p < 256 * k /\ h p /\ mldsa_hint_count h p = t)
                        MOD 256)
              else word 0
            else word(mldsa_hint_count h (256 * (t - omega + 1)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[mldsa_hintbitpack; EL_LIST_OF_SEQ] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MLD_FIPS204_HINT_COUNT_STRICT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[MLD_FIPS204_HINT_COUNT_IVT]]);;

(* ------------------------------------------------------------------------- *)
(* HintBitUnpack is the partial inverse of HintBitPack on the hint sets      *)
(* below 256 * k with at most omega < 256 hints: the packing of such a set   *)
(* passes the checks of Algorithm 21 (MLD_FIPS204_HINT_OK_HINTBITPACK), the  *)
(* hints that HintBitUnpack gives for a string that passes them are such a   *)
(* set and pack back to the string (MLD_FIPS204_HINTBITUNPACK_SOME), and the *)
(* packing is injective on these sets (MLD_FIPS204_HINTBITPACK_INJ). These   *)
(* only use the definitions of fips204.ml.                                   *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_HINT_OK_HINTBITPACK = prove
 (`!k omega h.
        omega < 256 /\ mldsa_hint_count h (256 * k) <= omega
        ==> mldsa_hint_ok k omega (mldsa_hintbitpack k omega h)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `y = mldsa_hintbitpack k omega h` THEN
  ABBREV_TAC `n = mldsa_hint_count h (256 * k)` THEN
  SUBGOAL_THEN `!i. i <= k ==> mldsa_hint_count h (256 * i) <= n`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "n" THEN
    MATCH_MP_TAC MLD_FIPS204_HINT_COUNT_MONO THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < k
        ==> val(EL (omega + i) (y:byte list)) =
            mldsa_hint_count h (256 * (i + 1))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "y" THEN
    SIMP_TAC[mldsa_hintbitpack; EL_LIST_OF_SEQ; LT_ADD_LCANCEL;
             ASSUME `i < k`] THEN
    REWRITE_TAC[ARITH_RULE `~(omega + i < omega)`; ADD_SUB2] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `n:num` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC; ALL_TAC] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i <= k ==> mldsa_hint_start omega y i = mldsa_hint_count h (256 * i)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_hint_start] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; MLD_FIPS204_HINT_COUNT_CLAUSES] THEN
    SUBGOAL_THEN `omega + i - 1 = omega + (i - 1) /\ i = (i - 1) + 1`
    (CONJUNCTS_THEN2 SUBST1_TAC (fun th -> GEN_REWRITE_TAC
       (RAND_CONV o RAND_CONV o RAND_CONV) [th]))
    THENL [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC
   `qh = \t. @p. p < 256 * k /\ h p /\ mldsa_hint_count h p = t` THEN
  SUBGOAL_THEN
   `!t. t < n ==> qh t < 256 * k /\ h(qh t) /\ mldsa_hint_count h (qh t) = t`
  (LABEL_TAC "qh") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "qh" THEN
    REWRITE_TAC[] THEN CONV_TAC SELECT_CONV THEN
    MATCH_MP_TAC MLD_FIPS204_HINT_COUNT_IVT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t < omega
        ==> EL t (y:byte list) =
            if t < n then word(qh t MOD 256) else word 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "y" THEN EXPAND_TAC "qh" THEN
    SIMP_TAC[mldsa_hintbitpack; EL_LIST_OF_SEQ; ASSUME `t < omega`;
             ARITH_RULE `t < omega ==> t < omega + k`] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN EXPAND_TAC "n" THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC MLD_FIPS204_HINT_COUNT_STRICT THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "n" THEN REWRITE_TAC[MLD_FIPS204_HINT_COUNT_IVT]];
    ALL_TAC] THEN
  REWRITE_TAC[mldsa_hint_ok] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[LT_IMP_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MLD_FIPS204_HINT_COUNT_MONO THEN ARITH_TAC;
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`i:num`; `t:num`] THEN REWRITE_TAC[IMP_CONJ] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[LT_IMP_LE] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `t < n` ASSUME_TAC THENL
     [MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC `mldsa_hint_count h (256 * (i + 1))` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `t < omega /\ t - 1 < omega /\ t - 1 < n`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
    USE_THEN "qh" (fun th ->
      MP_TAC(MP (SPEC `t - 1` th) (ASSUME `t - 1 < n`)) THEN
      MP_TAC(MP (SPEC `t:num` th) (ASSUME `t < n`))) THEN
    SPEC_TAC(`(qh:num->num)(t - 1)`,`a:num`) THEN
    SPEC_TAC(`(qh:num->num) t`,`b:num`) THEN REPEAT GEN_TAC THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `256 * i <= a /\ a < b /\ b < 256 * (i + 1)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LT] THEN
      ASM_SIMP_TAC[MLD_FIPS204_HINT_COUNT_LT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `a MOD 256 = a - 256 * i /\ b MOD 256 = b - 256 * i`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `i:num` THEN
      ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    X_GEN_TAC `t:num` THEN ASM_SIMP_TAC[LE_REFL] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM NOT_LE]]);;

let MLD_FIPS204_HINTBITUNPACK_SOME = prove
 (`!k omega y.
        LENGTH y = omega + k /\ mldsa_hint_ok k omega y
        ==> ?h. mldsa_hintbitunpack k omega y = SOME h /\
                (!p. h p ==> p < 256 * k) /\
                mldsa_hint_count h (256 * k) <= omega /\
                mldsa_hintbitpack k omega h = y`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[mldsa_hintbitunpack; option_INJ; UNWIND_THM1] THEN
  CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[mldsa_hint_ok]) THEN
  ABBREV_TAC `S = mldsa_hint_start omega y` THEN
  SUBGOAL_THEN `(S:num->num) 0 = 0` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[mldsa_hint_start]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < k ==> val(EL (omega + i) (y:byte list)) = (S:num->num)(i + 1)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[mldsa_hint_start; ADD_EQ_0; ARITH_EQ; ADD_SUB];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_CONJ] THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(LABEL_TAC "V1") THEN DISCH_THEN(LABEL_TAC "V2") THEN
  DISCH_THEN(LABEL_TAC "V3") THEN
  (fun (asl,w) ->
     let lam = rand(rator(lhand(lhand w))) in
     ABBREV_TAC (mk_eq(mk_var("H",type_of lam),lam)) (asl,w)) THEN
  SUBGOAL_THEN `!i. i < k ==> (S:num->num) i <= S(i + 1)` ASSUME_TAC THENL
   [USE_THEN "V1" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `!i j. i <= j /\ j <= k ==> (S:num->num) i <= S j`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MLD_FIPS204_STEP_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `n = (S:num->num) k` THEN
  SUBGOAL_THEN `n <= omega` ASSUME_TAC THENL
   [ASM_CASES_TAC `k = 0` THENL
     [UNDISCH_TAC `(S:num->num) k = n` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LE_0];
      USE_THEN "V1" (MP_TAC o C MP (UNDISCH(ARITH_RULE
        `~(k = 0) ==> k - 1 < k`)) o SPEC `k - 1`) THEN
      SIMP_TAC[SUB_ADD; LE_1; ASSUME `~(k = 0)`;
               ASSUME `(S:num->num) k = n`]];
    ALL_TAC] THEN
  ABBREV_TAC `B = \t. minimal i. t < (S:num->num)(i + 1)` THEN
  SUBGOAL_THEN
   `!t. t < n ==> B t < k /\ (S:num->num)(B t) <= t /\ t < S(B t + 1)`
  (LABEL_TAC "B1") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MLD_FIPS204_BLOCK THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t i. i < k /\ (S:num->num) i <= t /\ t < S(i + 1) ==> B t = i`
  (LABEL_TAC "B2") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MLD_FIPS204_BLOCK_UNIQUE THEN EXISTS_TAC `k:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i t t'. i < k /\ (S:num->num) i <= t /\ t < t' /\ t' < S(i + 1)
             ==> val(EL t (y:byte list)) < val(EL t' y)`
  (LABEL_TAC "V2'") THENL
   [GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LT] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    REMOVE_THEN "V2" (MP_TAC o SPECL [`i:num`; `SUC t'`]) THEN
    REWRITE_TAC[SUC_SUB1] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE `a < b ==> b < c ==> a < c`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q = \t. 256 * B t + val(EL t (y:byte list))` THEN
  SUBGOAL_THEN `!t. val(EL t (y:byte list)) < 256` (LABEL_TAC "v256") THENL
   [GEN_TAC THEN MP_TAC(ISPEC `EL t (y:byte list)` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t < n ==> (q:num->num) t < 256 * k /\ q t DIV 256 = B t /\
                  q t MOD 256 = val(EL t (y:byte list))`
  (LABEL_TAC "Q2") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "q" THEN REWRITE_TAC[] THEN
    USE_THEN "v256" (fun th -> SIMP_TAC[th; MLD_FIPS204_DIGIT256]) THEN
    USE_THEN "v256" (MP_TAC o SPEC `t:num`) THEN
    USE_THEN "B1" (MP_TAC o C MP (ASSUME `t < n`) o SPEC `t:num`) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t t'. t < t' /\ t' < n ==> (q:num->num) t < q t'`
  (LABEL_TAC "Q1") THENL
   [REPEAT STRIP_TAC THEN SUBGOAL_THEN `t < n` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "q" THEN REWRITE_TAC[] THEN
    USE_THEN "B1" (MP_TAC o C MP (ASSUME `t < n`) o SPEC `t:num`) THEN
    USE_THEN "B1" (MP_TAC o C MP (ASSUME `t' < n`) o SPEC `t':num`) THEN
    REPEAT STRIP_TAC THEN
    USE_THEN "v256" (MP_TAC o SPEC `t:num`) THEN
    USE_THEN "v256" (MP_TAC o SPEC `t':num`) THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [`(B:num->num) t`; `(B:num->num) t'`] LT_CASES) THENL
     [UNDISCH_TAC `(B:num->num) t < B t'` THEN ARITH_TAC;
      MP_TAC(SPECL [`(B:num->num) t' + 1`; `(B:num->num) t`]
        (ASSUME `!i j. i <= j /\ j <= k ==> (S:num->num) i <= S j`)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`t' < (S:num->num)((B:num->num) t' + 1)`;
        `(S:num->num)((B:num->num) t) <= t`; `t < t'`] THEN
      ARITH_TAC;
      USE_THEN "V2'" (MP_TAC o SPECL [`(B:num->num) t`; `t:num`; `t':num`])
      THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `t' < (S:num->num)((B:num->num) t' + 1)` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(B:num->num) t = B t'` THEN DISCH_THEN SUBST1_TAC THEN
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. H p <=> ?t. t < n /\ (q:num->num) t = p`
  (LABEL_TAC "HQ") THENL
   [X_GEN_TAC `p:num` THEN EXPAND_TAC "H" THEN REWRITE_TAC[] THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `t:num` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `p DIV 256 < k` ASSUME_TAC THENL
       [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
      SUBGOAL_THEN `t < (S:num->num)(p DIV 256 + 1)` ASSUME_TAC THENL
       [UNDISCH_TAC `t < val(EL (omega + p DIV 256) (y:byte list))` THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `t:num` THEN CONJ_TAC THENL
       [MATCH_MP_TAC LTE_TRANS THEN
        EXISTS_TAC `(S:num->num)(p DIV 256 + 1)` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(S:num->num) k = n` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC(ASSUME
         `!i j. i <= j /\ j <= k ==> (S:num->num) i <= S j`) THEN
        ASM_ARITH_TAC;
        EXPAND_TAC "q" THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `(B:num->num) t = p DIV 256` SUBST1_TAC THENL
         [USE_THEN "B2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `t:num`
       (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN
      USE_THEN "Q2" (STRIP_ASSUME_TAC o C MP (ASSUME `t < n`) o
                     SPEC `t:num`) THEN
      USE_THEN "B1" (STRIP_ASSUME_TAC o C MP (ASSUME `t < n`) o
                     SPEC `t:num`) THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `t:num` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. mldsa_hint_count H p = CARD {t | t < n /\ (q:num->num) t < p}`
  (LABEL_TAC "CQ") THENL
   [GEN_TAC THEN MATCH_MP_TAC MLD_FIPS204_HINT_COUNT_SEQ THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t < n ==> mldsa_hint_count H ((q:num->num) t) = t`
  (LABEL_TAC "CQT") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "CQ" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `{t' | t' < n /\ (q:num->num) t' < q t} = {t' | t' < t}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `t':num` THEN
      EQ_TAC THEN STRIP_TAC THENL
       [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
        UNDISCH_TAC `(q:num->num) t' < q t` THEN
        ASM_CASES_TAC `t':num = t` THEN ASM_REWRITE_TAC[LT_REFL] THEN
        REWRITE_TAC[NOT_LT] THEN MATCH_MP_TAC LT_IMP_LE THEN
        USE_THEN "Q1" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        USE_THEN "Q1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[CARD_NUMSEG_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < k ==> mldsa_hint_count H (256 * (i + 1)) = (S:num->num)(i + 1)`
  (LABEL_TAC "CQB") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "CQ" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN
     `{t | t < n /\ (q:num->num) t < 256 * (i + 1)} = {t | t < S(i + 1)}`
    SUBST1_TAC THENL [ALL_TAC; REWRITE_TAC[CARD_NUMSEG_LT]] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `t:num` THEN
    EQ_TAC THEN STRIP_TAC THENL
     [USE_THEN "Q2" (STRIP_ASSUME_TAC o C MP (ASSUME `t < n`) o
                     SPEC `t:num`) THEN
      USE_THEN "B1" (STRIP_ASSUME_TAC o C MP (ASSUME `t < n`) o
                     SPEC `t:num`) THEN
      SUBGOAL_THEN `(B:num->num) t < i + 1` ASSUME_TAC THENL
       [UNDISCH_TAC `(q:num->num) t DIV 256 = B t` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ];
        ALL_TAC] THEN
      MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC `(S:num->num)((B:num->num) t + 1)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ASSUME
       `!i j. i <= j /\ j <= k ==> (S:num->num) i <= S j`) THEN
      ASM_ARITH_TAC;
      SUBGOAL_THEN `t < n` ASSUME_TAC THENL
       [MATCH_MP_TAC LTE_TRANS THEN
        EXISTS_TAC `(S:num->num)(i + 1)` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(S:num->num) k = n` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC(ASSUME
         `!i j. i <= j /\ j <= k ==> (S:num->num) i <= S j`) THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "B1" (STRIP_ASSUME_TAC o C MP (ASSUME `t < n`) o
                     SPEC `t:num`) THEN
      SUBGOAL_THEN `(B:num->num) t <= i` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
        MP_TAC(SPECL [`i + 1`; `(B:num->num) t`]
         (ASSUME `!i j. i <= j /\ j <= k ==> (S:num->num) i <= S j`)) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC
         [`t < (S:num->num)(i + 1)`; `(S:num->num)((B:num->num) t) <= t`] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      EXPAND_TAC "q" THEN REWRITE_TAC[] THEN
      USE_THEN "v256" (MP_TAC o SPEC `t:num`) THEN
      UNDISCH_TAC `(B:num->num) t <= i` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mldsa_hint_count H (256 * k) = n` (LABEL_TAC "CQK") THENL
   [USE_THEN "CQ" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `{t | t < n /\ (q:num->num) t < 256 * k} = {t | t < n}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `t:num` THEN
      EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "Q2" (MP_TAC o C MP (ASSUME `t < n`) o SPEC `t:num`) THEN
      SIMP_TAC[];
      REWRITE_TAC[CARD_NUMSEG_LT]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "CQK" SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[LIST_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[mldsa_hintbitpack; LENGTH_LIST_OF_SEQ] THEN
    UNDISCH_TAC `LENGTH(y:byte list) = omega + k` THEN SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `x < omega + k` ASSUME_TAC THENL
   [UNDISCH_TAC `x < LENGTH(y:byte list)` THEN
    UNDISCH_TAC `LENGTH(y:byte list) = omega + k` THEN SIMP_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[MLD_FIPS204_HINTBITPACK_EL; ASSUME `x < omega + k`] THEN
  USE_THEN "CQK" (fun th -> REWRITE_TAC[th]) THEN
  COND_CASES_TAC THENL [COND_CASES_TAC; ALL_TAC] THENL
   [SUBGOAL_THEN
     `(@p. p < 256 * k /\ H p /\ mldsa_hint_count H p = x) = (q:num->num) x`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `p:num` THEN
      USE_THEN "HQ" (fun hq -> USE_THEN "CQT" (fun cqt ->
        USE_THEN "Q2" (fun q2 ->
          MESON_TAC[hq; cqt; q2; ASSUME `x < n`])));
      USE_THEN "Q2" (fun th -> REWRITE_TAC[MP (SPEC `x:num` th)
                                              (ASSUME `x < n`)]) THEN
      REWRITE_TAC[WORD_VAL]];
    REMOVE_THEN "V3" (MP_TAC o SPEC `x:num`) THEN
    ASM_REWRITE_TAC[GSYM NOT_LT] THEN MESON_TAC[];
    SUBGOAL_THEN `x - omega < k` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "CQB" (fun th -> REWRITE_TAC[MP (SPEC `x - omega` th)
       (ASSUME `x - omega < k`)]) THEN
    MP_TAC(MP (SPEC `x - omega`
     (ASSUME `!i. i < k ==> val(EL (omega + i) (y:byte list)) =
                            (S:num->num)(i + 1)`)) (ASSUME `x - omega < k`))
    THEN SUBGOAL_THEN `omega + (x - omega) = x` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_VAL]]);;

let MLD_FIPS204_HINTBITPACK_INJ = prove
 (`!k omega h1 h2.
        omega < 256 /\
        (!p. h1 p ==> p < 256 * k) /\ (!p. h2 p ==> p < 256 * k) /\
        mldsa_hint_count h1 (256 * k) <= omega /\
        mldsa_hint_count h2 (256 * k) <= omega /\
        mldsa_hintbitpack k omega h1 = mldsa_hintbitpack k omega h2
        ==> h1 = h2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!t. t < omega + k
        ==> EL t (mldsa_hintbitpack k omega h1) =
            EL t (mldsa_hintbitpack k omega h2)`
  MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SIMP_TAC[MLD_FIPS204_HINTBITPACK_EL] THEN DISCH_THEN(LABEL_TAC "bytes") THEN
  SUBGOAL_THEN
   `!i. i <= k
        ==> mldsa_hint_count h1 (256 * i) < 256 /\
            mldsa_hint_count h2 (256 * i) < 256`
  (LABEL_TAC "small") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `omega:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_TRANS THENL
     [EXISTS_TAC `mldsa_hint_count h1 (256 * k)`;
      EXISTS_TAC `mldsa_hint_count h2 (256 * k)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MLD_FIPS204_HINT_COUNT_MONO THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i <= k
        ==> mldsa_hint_count h1 (256 * i) = mldsa_hint_count h2 (256 * i)`
  (LABEL_TAC "counts") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i = 0` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; MLD_FIPS204_HINT_COUNT_CLAUSES] THEN
    USE_THEN "bytes" (MP_TAC o SPEC `omega + (i - 1)`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `~(omega + (i - 1) < omega)`] THEN
    SUBGOAL_THEN `(omega + (i - 1)) - omega + 1 = i` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `val:byte->num`) THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    USE_THEN "small" (MP_TAC o SPEC `i:num`) THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  ABBREV_TAC `n = mldsa_hint_count h1 (256 * k)` THEN
  SUBGOAL_THEN `mldsa_hint_count h2 (256 * k) = n` (LABEL_TAC "n2") THENL
   [EXPAND_TAC "n" THEN CONV_TAC SYM_CONV THEN
    USE_THEN "counts" MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  ABBREV_TAC
   `qh1 = \t. @p. p < 256 * k /\ h1 p /\ mldsa_hint_count h1 p = t` THEN
  ABBREV_TAC
   `qh2 = \t. @p. p < 256 * k /\ h2 p /\ mldsa_hint_count h2 p = t` THEN
  SUBGOAL_THEN
   `!t. t < n ==> qh1 t < 256 * k /\ h1(qh1 t) /\
                  mldsa_hint_count h1 (qh1 t) = t`
  (LABEL_TAC "q1") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "qh1" THEN
    REWRITE_TAC[] THEN CONV_TAC SELECT_CONV THEN
    MATCH_MP_TAC MLD_FIPS204_HINT_COUNT_IVT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t < n ==> qh2 t < 256 * k /\ h2(qh2 t) /\
                  mldsa_hint_count h2 (qh2 t) = t`
  (LABEL_TAC "q2") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "qh2" THEN
    REWRITE_TAC[] THEN CONV_TAC SELECT_CONV THEN
    MATCH_MP_TAC MLD_FIPS204_HINT_COUNT_IVT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t < n ==> (qh1:num->num) t MOD 256 = qh2 t MOD 256`
  (LABEL_TAC "idx") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "bytes" (MP_TAC o SPEC `t:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `t < omega` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "qh1" THEN EXPAND_TAC "qh2" THEN REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `val:byte->num`) THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t < n ==> (qh1:num->num) t DIV 256 = qh2 t DIV 256`
  (LABEL_TAC "blk") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "q1" (MP_TAC o C MP (ASSUME `t < n`) o SPEC `t:num`) THEN
    USE_THEN "q2" (MP_TAC o C MP (ASSUME `t < n`) o SPEC `t:num`) THEN
    SPEC_TAC(`(qh1:num->num) t`,`a:num`) THEN
    SPEC_TAC(`(qh2:num->num) t`,`b:num`) THEN REPEAT GEN_TAC THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `a DIV 256 < k` ASSUME_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
    ABBREV_TAC `i = a DIV 256` THEN
    SUBGOAL_THEN `256 * i <= a /\ a < 256 * (i + 1)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "i" THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `i <= k /\ i + 1 <= k` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(ARITH_RULE
     `256 * i <= x /\ x < 256 * (i + 1) ==> x DIV 256 = i`) THEN
    USE_THEN "counts" (MP_TAC o C MP (ASSUME `i <= k`) o SPEC `i:num`) THEN
    USE_THEN "counts" (MP_TAC o C MP (ASSUME `i + 1 <= k`) o SPEC `i + 1`) THEN
    MP_TAC(MP (SPECL [`h1:num->bool`; `a:num`; `256 * i`]
                MLD_FIPS204_HINT_COUNT_LT) (ASSUME `(h1:num->bool) a`)) THEN
    MP_TAC(MP (SPECL [`h1:num->bool`; `a:num`; `256 * (i + 1)`]
                MLD_FIPS204_HINT_COUNT_LT) (ASSUME `(h1:num->bool) a`)) THEN
    MP_TAC(MP (SPECL [`h2:num->bool`; `b:num`; `256 * i`]
                MLD_FIPS204_HINT_COUNT_LT) (ASSUME `(h2:num->bool) b`)) THEN
    MP_TAC(MP (SPECL [`h2:num->bool`; `b:num`; `256 * (i + 1)`]
                MLD_FIPS204_HINT_COUNT_LT) (ASSUME `(h2:num->bool) b`)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `256 * i <= a` THEN UNDISCH_TAC `a < 256 * (i + 1)` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t < n ==> (qh1:num->num) t = qh2 t` (LABEL_TAC "eq")
  THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE
     `a DIV 256 = b DIV 256 /\ a MOD 256 = b MOD 256 ==> a = b`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `p:num` THEN EQ_TAC THEN
  DISCH_TAC THENL
   [SUBGOAL_THEN `mldsa_hint_count h1 p < n` ASSUME_TAC THENL
     [UNDISCH_TAC `mldsa_hint_count h1 (256 * k) = n` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC MLD_FIPS204_HINT_COUNT_STRICT THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "q1" (STRIP_ASSUME_TAC o
      C MP (ASSUME `mldsa_hint_count h1 p < n`) o
      SPEC `mldsa_hint_count h1 p`) THEN
    SUBGOAL_THEN `p = (qh1:num->num)(mldsa_hint_count h1 p)` SUBST1_TAC THENL
     [MATCH_MP_TAC(ISPEC `h1:num->bool` MLD_FIPS204_HINT_COUNT_INJ) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "eq" (fun th -> REWRITE_TAC[MP
      (SPEC `mldsa_hint_count h1 p` th)
      (ASSUME `mldsa_hint_count h1 p < n`)]) THEN
    USE_THEN "q2" (MP_TAC o C MP (ASSUME `mldsa_hint_count h1 p < n`) o
                   SPEC `mldsa_hint_count h1 p`) THEN
    SIMP_TAC[];
    SUBGOAL_THEN `mldsa_hint_count h2 p < n` ASSUME_TAC THENL
     [REMOVE_THEN "n2" (SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC MLD_FIPS204_HINT_COUNT_STRICT THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "q2" (STRIP_ASSUME_TAC o
      C MP (ASSUME `mldsa_hint_count h2 p < n`) o
      SPEC `mldsa_hint_count h2 p`) THEN
    SUBGOAL_THEN `p = (qh2:num->num)(mldsa_hint_count h2 p)` SUBST1_TAC THENL
     [MATCH_MP_TAC(ISPEC `h2:num->bool` MLD_FIPS204_HINT_COUNT_INJ) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "eq" (fun th -> REWRITE_TAC[GSYM(MP
      (SPEC `mldsa_hint_count h2 p` th)
      (ASSUME `mldsa_hint_count h2 p < n`))]) THEN
    USE_THEN "q1" (MP_TAC o C MP (ASSUME `mldsa_hint_count h2 p < n`) o
                   SPEC `mldsa_hint_count h2 p`) THEN
    SIMP_TAC[]]);;

let MLD_FIPS204_HINTBITUNPACK_INVERSE = prove
 (`!k omega y.
        omega < 256 /\ LENGTH y = omega + k
        ==> mldsa_hintbitunpack k omega y =
            if ?h. (!p. h p ==> p < 256 * k) /\
                   mldsa_hint_count h (256 * k) <= omega /\
                   mldsa_hintbitpack k omega h = y
            then SOME(@h. (!p. h p ==> p < 256 * k) /\
                          mldsa_hint_count h (256 * k) <= omega /\
                          mldsa_hintbitpack k omega h = y)
            else NONE`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `mldsa_hint_ok k omega y` THENL
   [MP_TAC(SPECL [`k:num`; `omega:num`; `y:byte list`]
      MLD_FIPS204_HINTBITUNPACK_SOME) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `h0:num->bool`
     (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     `?h. (!p. h p ==> p < 256 * k) /\
          mldsa_hint_count h (256 * k) <= omega /\
          mldsa_hintbitpack k omega h = y`
     (fun th -> REWRITE_TAC[th])
    THENL [EXISTS_TAC `h0:num->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[option_INJ] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `h:num->bool` THEN
    BETA_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(SPECL [`k:num`; `omega:num`; `h:num->bool`; `h0:num->bool`]
        MLD_FIPS204_HINTBITPACK_INJ) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[mldsa_hintbitunpack] THEN
    COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `h:num->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~mldsa_hint_ok k omega y` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MLD_FIPS204_HINT_OK_HINTBITPACK THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Packing the hints (FIPS 204 HintBitPack, Algorithm 20): the counts of     *)
(* mldsa_native_hints.ml are those of fips204.ml, and the index bytes are    *)
(* the positions of the hints with the given counts, so the packed bytes are *)
(* mldsa_hintbitpack of any predicate h' that agrees with the hints h below  *)
(* 256 * k (for instance p < 256 * k /\ h p), whatever their number; the C   *)
(* code returns 0 exactly when there are at most omega of them.              *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_HINT_COUNT = prove
 (`!h p. mld_hint_count h p = mldsa_hint_count h p`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[mld_hint_count; MLD_FIPS204_HINT_COUNT_CLAUSES]);;

let MLD_FIPS204_HINT_INDEX = prove
 (`!h n t.
        mld_hint_index h n t =
        if ?p. p < n /\ h p /\ mld_hint_count h p = t
        then word((@p. p < n /\ h p /\ mld_hint_count h p = t) MOD 256)
        else word 0`,
  GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THEN
  ASM_REWRITE_TAC[mld_hint_index; LT] THEN
  ASM_CASES_TAC `(h:num->bool) n /\ t = mld_hint_count h n` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    SUBGOAL_THEN
     `!p. ((p = n \/ p < n) /\ h p /\
           mld_hint_count h p = mld_hint_count h n) <=> p = n`
    ASSUME_TAC THENL
     [GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`h:num->bool`; `p:num`; `n:num`]
        MLD_FIPS204_HINT_COUNT_STRICT) THEN
      ASM_REWRITE_TAC[GSYM MLD_FIPS204_HINT_COUNT] THEN ARITH_TAC;
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MESON[] `(?p:num. p = n) <=> T`; SELECT_REFL]];
    SUBGOAL_THEN
     `!p. ((p = n \/ p < n) /\ h p /\ mld_hint_count h p = t) <=>
          (p < n /\ h p /\ mld_hint_count h p = t)`
    (fun th -> REWRITE_TAC[th]) THEN
    GEN_TAC THEN ASM_CASES_TAC `p:num = n` THEN ASM_REWRITE_TAC[LT_REFL] THEN
    ASM_MESON_TAC[]]);;

let MLD_FIPS204_PACK_HINTS = prove
 (`!omega k (h:num->bool) h'.
        (!p. p < 256 * k ==> (h' p <=> h p))
        ==> list_of_seq (mld_pack_hints omega k h) (omega + k) =
            mldsa_hintbitpack k omega h'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!p. p <= 256 * k ==> mldsa_hint_count h' p = mld_hint_count h p`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[MLD_FIPS204_HINT_COUNT] THEN
    MATCH_MP_TAC MLD_FIPS204_HINT_COUNT_EQ THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[mldsa_hintbitpack; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_LIST_OF_SEQ] THEN
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[mld_pack_hints] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[MLD_FIPS204_HINT_INDEX] THEN
    SUBGOAL_THEN
     `!p. (p < 256 * k /\ h' p /\ mldsa_hint_count h' p = t) <=>
          (p < 256 * k /\ h p /\ mld_hint_count h p = t)`
     (fun th -> REWRITE_TAC[th]) THEN
    GEN_TAC THEN ASM_CASES_TAC `p < 256 * k` THEN ASM_SIMP_TAC[LT_IMP_LE];
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC]);;

let MLD_FIPS204_PACK_HINTS_RET = prove
 (`!omega k (h:num->bool) h'.
        (!p. p < 256 * k ==> (h' p <=> h p))
        ==> (mld_pack_hints_ret omega k h = word 0 <=>
             mldsa_hint_count h' (256 * k) <= omega)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_pack_hints_ret] THEN
  SUBGOAL_THEN `mldsa_hint_count h' (256 * k) = mld_hint_count h (256 * k)`
  SUBST1_TAC THENL
   [REWRITE_TAC[MLD_FIPS204_HINT_COUNT] THEN
    MATCH_MP_TAC MLD_FIPS204_HINT_COUNT_EQ THEN ASM_MESON_TAC[];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV]);;

(* ------------------------------------------------------------------------- *)
(* Unpacking the hints (FIPS 204 HintBitUnpack, Algorithm 21), from the      *)
(* omega + k bytes b of a vector of k > 0 polynomials: the checks of the C   *)
(* code for each polynomial are those of mldsa_hint_ok together, and the     *)
(* hint at position p < 256 * k is the nonzero coefficient p MOD 256 of      *)
(* polynomial p DIV 256 of mld_unpack_hints. When the checks pass, there are *)
(* at most omega of these hints and they pack back to the bytes.             *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_HINT_START = prove
 (`!omega k (b:num->byte) i.
        i <= k
        ==> mldsa_hint_start omega (list_of_seq b (omega + k)) i =
            mld_hints_start omega b i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_hint_start; mld_hints_start] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EL_LIST_OF_SEQ THEN ASM_ARITH_TAC);;

let MLD_FIPS204_UNPACK_HINTS_OK = prove
 (`!omega k (b:num->byte).
        ~(k = 0)
        ==> ((!i. i < k ==> mld_unpack_hints_ok omega k b i) <=>
             mldsa_hint_ok k omega (list_of_seq b (omega + k)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `y = list_of_seq (b:num->byte) (omega + k)` THEN
  SUBGOAL_THEN `!x. x < omega + k ==> EL x y = (b:num->byte) x`
  ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN SIMP_TAC[EL_LIST_OF_SEQ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i <= k ==> mldsa_hint_start omega y i = mld_hints_start omega b i`
  ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN SIMP_TAC[MLD_FIPS204_HINT_START]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < k ==> EL (omega + i) y = (b:num->byte)(omega + i)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x < omega ==> EL x y = (b:num->byte) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[mldsa_hint_ok; mld_unpack_hints_ok] THEN
  REWRITE_TAC[IMP_CONJ] THEN ASM_SIMP_TAC[LT_IMP_LE; LE_REFL] THEN
  ASM_REWRITE_TAC[mld_hints_start] THEN
  ABBREV_TAC `s = \i. if i = 0 then 0 else val((b:num->byte)(omega + i - 1))`
  THEN POP_ASSUM(fun th -> REWRITE_TAC[GSYM(BETA_RULE(AP_THM th `i:num`))])
  THEN EQ_TAC THENL
   [DISCH_THEN(LABEL_TAC "H") THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      REMOVE_THEN "H" (MP_TAC o C MP (ASSUME `i < k`) o SPEC `i:num`) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]);
      MAP_EVERY X_GEN_TAC [`i:num`; `t:num`] THEN REPEAT DISCH_TAC THEN
      REMOVE_THEN "H" (MP_TAC o C MP (ASSUME `i < k`) o SPEC `i:num`) THEN
      DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 (MP_TAC o SPEC `t:num`) (K ALL_TAC)))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `t - 1 < omega /\ t < omega` STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`t < val((b:num->byte)(omega + i))`;
          `val((b:num->byte)(omega + i)) <= omega`] THEN ARITH_TAC;
        ASM_SIMP_TAC[]];
      X_GEN_TAC `t:num` THEN REPEAT DISCH_TAC THEN
      REMOVE_THEN "H" (MP_TAC o SPEC `k - 1`) THEN
      ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> k - 1 < k`]];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "A")
     (CONJUNCTS_THEN2 (LABEL_TAC "B") (LABEL_TAC "C"))) THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REMOVE_THEN "A" (MP_TAC o C MP (ASSUME `i < k`) o SPEC `i:num`) THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [X_GEN_TAC `j:num` THEN REPEAT DISCH_TAC THEN
      REMOVE_THEN "B" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `j - 1 < omega /\ j < omega` STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`j < val((b:num->byte)(omega + i))`;
          `val((b:num->byte)(omega + i)) <= omega`] THEN ARITH_TAC;
        ASM_SIMP_TAC[]];
      DISCH_TAC THEN REMOVE_THEN "C" ACCEPT_TAC]]);;

let MLD_FIPS204_UNPACK_HINTS_RET = prove
 (`!omega k (b:num->byte) i.
        mld_unpack_hints_ret omega k b i = word 0 <=>
        mld_unpack_hints_ok omega k b i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_unpack_hints_ret] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

let MLD_FIPS204_HINTBITUNPACK = prove
 (`!omega k (b:num->byte).
        ~(k = 0)
        ==> mldsa_hintbitunpack k omega (list_of_seq b (omega + k)) =
            if !i. i < k ==> mld_unpack_hints_ret omega k b i = word 0
            then SOME(\p. p < 256 * k /\
                          ~(mld_unpack_hints omega b (p DIV 256) (p MOD 256) =
                            word 0))
            else NONE`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mldsa_hintbitunpack; MLD_FIPS204_UNPACK_HINTS_RET] THEN
  ASM_SIMP_TAC[GSYM MLD_FIPS204_UNPACK_HINTS_OK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `p:num` THEN
  ASM_CASES_TAC `p < 256 * k` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `i = p DIV 256` THEN
  SUBGOAL_THEN `i < k` ASSUME_TAC THENL
   [EXPAND_TAC "i" THEN ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  ASM_REWRITE_TAC[mld_unpack_hints_ok] THEN STRIP_TAC THEN
  REWRITE_TAC[mld_unpack_hints; MESON[]
   `~((if q then x else y:int32) = y) <=> q /\ ~(x = y)`] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MLD_FIPS204_HINT_START; LT_IMP_LE; EL_LIST_OF_SEQ;
               ARITH_RULE `i < k ==> omega + i < omega + k`] THEN
  MATCH_MP_TAC(MESON[]
   `(!t:num. P t ==> (Q t <=> R t))
    ==> ((?t. P t /\ Q t) <=> (?t. P t /\ R t))`)
  THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `t < val((b:num->byte)(omega + i))` THEN
  ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EL_LIST_OF_SEQ THEN ASM_ARITH_TAC);;

let MLD_FIPS204_HINTBITPACK_UNPACK_HINTS = prove
 (`!omega k (b:num->byte).
        ~(k = 0) /\ (!i. i < k ==> mld_unpack_hints_ret omega k b i = word 0)
        ==> mldsa_hint_count
             (\p. p < 256 * k /\
                  ~(mld_unpack_hints omega b (p DIV 256) (p MOD 256) = word 0))
             (256 * k) <= omega /\
            mldsa_hintbitpack k omega
             (\p. p < 256 * k /\
                  ~(mld_unpack_hints omega b (p DIV 256) (p MOD 256) =
                    word 0)) =
            list_of_seq b (omega + k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`omega:num`; `k:num`; `b:num->byte`]
    MLD_FIPS204_HINTBITUNPACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:num`; `omega:num`; `list_of_seq (b:num->byte) (omega + k)`]
    MLD_FIPS204_HINTBITUNPACK_SOME) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ; option_INJ] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[GSYM MLD_FIPS204_UNPACK_HINTS_OK;
                 GSYM MLD_FIPS204_UNPACK_HINTS_RET];
    DISCH_THEN(X_CHOOSE_THEN `h:num->bool`
     (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[]]);;
