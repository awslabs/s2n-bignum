(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Vector operations inlined into their callers. In a monolithic build the   *)
(* compiler inlines the polyvec wrappers of mlkem-native, which apply a      *)
(* kernel to each of the k polynomials of a vector, so that the caller       *)
(* calls the kernel k times itself, e.g. for k = 2 in mlkem512_check_pk:     *)
(*                                                                           *)
(*      bl   mlk_poly_frombytes_c     r = buffer,       a = pk               *)
(*      ...                                                                  *)
(*      bl   mlk_poly_frombytes_c     r = buffer + 512, a = pk + 384         *)
(*                                                                           *)
(* The proof of the caller then needs what the proof of the wrapper does in  *)
(* a build where it is a function of its own: the input of the vector as     *)
(* the inputs of the polynomials (the SPLIT lemmas below), and the results   *)
(* of the polynomials as the result of the vector (the JOIN lemmas), so that *)
(* the rest of the proof can use the specification of the wrapper. The       *)
(* lemmas are for any k; the coefficients of a vector are as in              *)
(* utils/mlkem_native_image.ml (POLYVEC_SPLIT_TAC and POLYVEC_JOIN_TAC).     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* polyvec_frombytes: 384 bytes per polynomial, 12 bits per coefficient.     *)
(* ------------------------------------------------------------------------- *)

let POLYVEC_FROMBYTES_SPLIT_GEN = prove
 (`!a k n s j.
        read (memory :> bytes(a,384 * k)) s = n /\ j < k
        ==> read (memory :> bytes(word_add a (word(384 * j)),384)) s =
            (n DIV 2 EXP (3072 * j)) MOD 2 EXP 3072`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE;
              ARITH_RULE `3072 * j = 8 * 384 * j`;
              ARITH_RULE `3072 = 8 * 384`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let POLYVEC_FROMBYTES_FIELD_GEN = prove
 (`!n k i.
        i < 256
        ==> ((n DIV 2 EXP k) MOD 2 EXP 3072 DIV 2 EXP (12 * i)) MOD 2 EXP 12 =
            (n DIV 2 EXP (k + 12 * i)) MOD 2 EXP 12`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [DIV_MOD] THEN
  REWRITE_TAC[GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `i < 256 ==> MIN 3072 (12 * i + 12) = 12 * i + 12`] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_MOD; DIV_DIV]);;

(* ------------------------------------------------------------------------- *)
(* polyvec_tobytes: 512 bytes of 16-bit coefficients per polynomial in, 384  *)
(* bytes out.                                                                *)
(* ------------------------------------------------------------------------- *)

let ALL_SUB_LIST_GEN = prove
 (`!P (l:A list) m n. ALL P l ==> ALL P (SUB_LIST(m,n) l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SUB_LIST_CLAUSES; ALL] THEN
  INDUCT_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[SUB_LIST_CLAUSES; ALL]);;

let POLYVEC_TOBYTES_SPLIT_GEN = prove
 (`!a k (l:int16 list) s j.
        read (memory :> bytes(a,512 * k)) s = num_of_wordlist l /\ j < k
        ==> read (memory :> bytes(word_add a (word(512 * j)),512)) s =
            num_of_wordlist (SUB_LIST(256 * j,256) l)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST; DIMINDEX_16] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE;
              ARITH_RULE `16 * 256 * j = 8 * 512 * j`;
              ARITH_RULE `16 * 256 = 8 * 512`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let POLYVEC_TOBYTES_JOIN_GEN = prove
 (`!r k (l:int16 list) s.
        LENGTH l = 256 * k /\
        (!j. j < k
             ==> read (memory :> bytes(word_add r (word(384 * j)),384)) s =
                 num_of_wordlist
                  (MAP word_zx (SUB_LIST(256 * j,256) l):(12 word)list))
        ==> read (memory :> bytes(r,384 * k)) s =
            num_of_wordlist (MAP word_zx l:(12 word)list)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!m. m <= k
        ==> read (memory :> bytes(r,384 * m)) s =
            num_of_wordlist
             (MAP word_zx (SUB_LIST(0,256 * m) (l:int16 list)):(12 word)list)`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; MAP; num_of_wordlist;
                  READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL];
      DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    REWRITE_TAC[ARITH_RULE `256 * SUC m = 256 * m + 256`;
                ARITH_RULE `384 * SUC m = 384 * m + 384`] THEN
    REWRITE_TAC[SUB_LIST_SPLIT; ADD_CLAUSES; MAP_APPEND;
                NUM_OF_WORDLIST_APPEND; LENGTH_MAP; LENGTH_SUB_LIST] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_REWRITE_TAC[SUB_0] THEN
    SUBGOAL_THEN `MIN (256 * m) (256 * k) = 256 * m`
    SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `12 * 256 * m = 8 * 384 * m`] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE];
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `LENGTH(l:int16 list) = 256 * k` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[SUB_LIST_LENGTH]]);;

(* ------------------------------------------------------------------------- *)
(* POLYVEC_INLINE_SPLIT_TAC split a k: from an assumption                    *)
(* read (memory :> bytes(a,m)) s = n, the facts of the lemma split (one of   *)
(* the SPLIT lemmas above) for j = 0, ..., k - 1, with the offsets           *)
(* evaluated.                                                                *)
(* ------------------------------------------------------------------------- *)

let POLYVEC_INLINE_SPLIT_TAC split a k =
  let kt = mk_small_numeral k in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(_,Comb(Const("bytes",_),aa))),_)),_)
        when fst(dest_pair aa) = a ->
        let sth = SPECL [a; kt] split in
        let sth' = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) sth in
        MAP_EVERY (fun j ->
          let jt = mk_small_numeral j in
          let lt = EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool` jt kt)) in
          ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC
                              REWRITE_CONV[WORD_ADD_0])
            (MATCH_MP sth' (CONJ th lt)))) (0--(k-1))
    | _ -> NO_TAC);;
