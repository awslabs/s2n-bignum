(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics for the proofs of mldsa44_signature_internal,          *)
(* mldsa65_signature_internal and mldsa87_signature_internal (sign.c), whose *)
(* FULL theorems are proved from lemmas for the parts of the code: the start *)
(* of an attempt, the loop over z with its early exit, the loop over the     *)
(* rows of w0 with its two early exits, the packing of c~ and the hints, the *)
(* cleanup of an attempt, and the whole attempt from them. The events of the *)
(* attempts are a function of what the C code declassifies                   *)
(* (mld_sign_declass of common/mldsa_native_sign.ml), from which also the    *)
(* number of attempts made follows (mld_sign_natt).                          *)
(* ========================================================================= *)

needs "common/mldsa_native_sign.ml";;
needs "common/fips204/properties/mldsa_native_full.ml";;
needs "common/fips204/properties/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* The number of attempts made, from what is declassified: one more than the *)
(* first attempt n < maxatt whose result is succ (l + 2 * k + 1), or maxatt  *)
(* if there is none. It is mld_sign_nattempts, since the result of attempt n *)
(* is declassified if n < mld_sign_nattempts and is 0 otherwise.             *)
(* ------------------------------------------------------------------------- *)

let mld_sign_natt = new_definition
 `mld_sign_natt maxatt succ (D:num->num#num#(num->int32)#(num->byte)) =
    if ?n. n < maxatt /\ FST(SND(D n)) = succ
    then (minimal n. n < maxatt /\ FST(SND(D n)) = succ) + 1
    else maxatt`;;

let SIGN_MINIMAL_EQ = prove
 (`!m. (minimal n. n = m) = m`,
  GEN_TAC THEN MP_TAC(ISPEC `\n:num. n = m` MINIMAL) THEN
  REWRITE_TAC[] THEN MESON_TAC[LT_REFL]);;

let SIGN_NATT_ABSTRACT = prove
 (`!maxatt succ (R:num->num) (D:num->num#num#(num->int32)#(num->byte)).
        ~(succ = 0) /\
        (!n. FST(SND(D n)) =
             if n < (if ?n. n < maxatt /\ R n = succ
                     then (minimal n. n < maxatt /\ R n = succ) + 1
                     else maxatt)
             then R n else 0)
        ==> mld_sign_natt maxatt succ D =
            (if ?n. n < maxatt /\ R n = succ
             then (minimal n. n < maxatt /\ R n = succ) + 1
             else maxatt)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mld_sign_natt] THEN
  ASM_CASES_TAC `?n. n < maxatt /\ (R:num->num) n = succ` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(?n. n < maxatt /\ FST(SND((D:num->num#num#(num->int32)#
                                              (num->byte)) n)) = succ)`
     (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MINIMAL]) THEN
  ABBREV_TAC `m = minimal n. n < maxatt /\ (R:num->num) n = succ` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. n < maxatt /\ FST(SND((D:num->num#num#(num->int32)#(num->byte)) n)) =
                      succ <=> n = m`
   (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN EQ_TAC THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `n < m + 1 /\ ~(n < m) ==> n = m`) THEN
      ASM_MESON_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `m < m + 1`]];
    ASM_REWRITE_TAC[SIGN_MINIMAL_EQ] THEN MESON_TAC[]]);;

let SIGN_ATTEMPT_DECLASS_REJ = prove
 (`!k l ctlen tau g1 bndz bndw bndh w1enc w1p dlo mkhint omega A s1hat s2hat
    t0hat mu rhoprime kappa.
        FST(SND(mld_sign_attempt_declass k l ctlen tau g1 bndz bndw bndh w1enc
                 w1p dlo mkhint omega A s1hat s2hat t0hat mu rhoprime kappa)) =
        mld_sign_attempt_rej k l ctlen tau g1 bndz bndw bndh w1enc w1p dlo
         mkhint omega A s1hat s2hat t0hat mu rhoprime kappa`,
  REWRITE_TAC[mld_sign_attempt_declass; mld_sign_attempt_rej] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FST; SND]);;

let SIGN_NATT_DECLASS = prove
 (`!k l unpack p ctlen tau g1 bndz bndw bndh w1enc w1p dlo mkhint omega
    maxatt sk mu rnd.
        mld_sign_natt maxatt (l + 2 * k + 1)
         (mld_sign_declass k l unpack p ctlen tau g1 bndz bndw bndh w1enc w1p
           dlo mkhint omega maxatt sk mu rnd) =
        mld_sign_nattempts k l unpack p ctlen tau g1 bndz bndw bndh w1enc w1p
         dlo mkhint omega maxatt sk mu rnd`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_sign_nattempts; mld_sign_ok] THEN
  MATCH_MP_TAC SIGN_NATT_ABSTRACT THEN
  REWRITE_TAC[ARITH_RULE `~(l + 2 * k + 1 = 0)`] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[mld_sign_declass] THEN
  REWRITE_TAC[mld_sign_nattempts; mld_sign_ok] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SIGN_ATTEMPT_DECLASS_REJ] THEN
  REWRITE_TAC[mld_sign_rejn]);;

(*** The properties of the number of attempts that the proofs use ***)

let SIGN_NATTEMPTS_PROPS = prove
 (`!k l unpack p ctlen tau g1 bndz bndw bndh w1enc w1p dlo mkhint omega
    maxatt sk mu rnd.
        ~(maxatt = 0)
        ==> 0 < mld_sign_nattempts k l unpack p ctlen tau g1 bndz bndw bndh
                  w1enc w1p dlo mkhint omega maxatt sk mu rnd /\
            mld_sign_nattempts k l unpack p ctlen tau g1 bndz bndw bndh
             w1enc w1p dlo mkhint omega maxatt sk mu rnd <= maxatt /\
            (!i. i + 1 < mld_sign_nattempts k l unpack p ctlen tau g1 bndz
                          bndw bndh w1enc w1p dlo mkhint omega maxatt sk mu rnd
                 ==> ~(mld_sign_rejn k l unpack p ctlen tau g1 bndz bndw bndh
                        w1enc w1p dlo mkhint omega sk mu rnd i =
                       l + 2 * k + 1)) /\
            (mld_sign_ok k l unpack p ctlen tau g1 bndz bndw bndh w1enc w1p dlo
              mkhint omega maxatt sk mu rnd <=>
             mld_sign_rejn k l unpack p ctlen tau g1 bndz bndw bndh w1enc w1p
              dlo mkhint omega sk mu rnd
              (mld_sign_nattempts k l unpack p ctlen tau g1 bndz bndw bndh
                w1enc w1p dlo mkhint omega maxatt sk mu rnd - 1) =
             l + 2 * k + 1) /\
            (~mld_sign_ok k l unpack p ctlen tau g1 bndz bndw bndh w1enc w1p
               dlo mkhint omega maxatt sk mu rnd
             ==> mld_sign_nattempts k l unpack p ctlen tau g1 bndz bndw bndh
                  w1enc w1p dlo mkhint omega maxatt sk mu rnd = maxatt)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[mld_sign_nattempts; mld_sign_ok] THEN
  ABBREV_TAC
   `R = \n. mld_sign_rejn k l unpack p ctlen tau g1 bndz bndw bndh w1enc w1p
             dlo mkhint omega sk mu rnd n` THEN
  SUBGOAL_THEN
   `!n. mld_sign_rejn k l unpack p ctlen tau g1 bndz bndw bndh w1enc w1p
         dlo mkhint omega sk mu rnd n = (R:num->num) n`
   (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MINIMAL]) THEN
    ABBREV_TAC
     `m = minimal n. n < maxatt /\ (R:num->num) n = l + 2 * k + 1` THEN
    STRIP_TAC THEN REWRITE_TAC[ADD_SUB] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      UNDISCH_TAC `m < maxatt` THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [UNDISCH_TAC `i + 1 < m + 1` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `i < maxatt` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `i + 1 < m + 1` THEN UNDISCH_TAC `m < maxatt` THEN
      ARITH_TAC];
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM]) THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `~(maxatt = 0)` THEN ARITH_TAC;
      REWRITE_TAC[LE_REFL];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
      SUBGOAL_THEN `i < maxatt` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `i + 1 < maxatt` THEN ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `maxatt - 1`) THEN
      SUBGOAL_THEN `maxatt - 1 < maxatt` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `~(maxatt = 0)` THEN ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The result r of the checks of an attempt (mld_sign_rej): the checks       *)
(* before the first that fails pass, and that one fails; and if all the norm *)
(* checks pass, r is the success value exactly if the number of hints is at  *)
(* most omega. A check j of the rows is that of w0 - c s2 of row j DIV 2 if  *)
(* j is even, and that of c t0 otherwise.                                    *)
(* ------------------------------------------------------------------------- *)

let SIGN_REJ_CASES = prove
 (`!k l bndz bndw bndh omega (mkhint:(num->int32)->(num->byte)->num->bool)
    z r0 ct0 x w1 r.
        mld_sign_rej k l bndz bndw bndh omega mkhint z r0 ct0 x w1 = r
        ==> r <= l + 2 * k + 1 /\
            (r < l
             ==> ~(mld_poly_chknorm (z r) (word bndz) = word 0) /\
                 (!i. i < r
                      ==> mld_poly_chknorm (z i) (word bndz) = word 0)) /\
            (l <= r
             ==> !i. i < l ==> mld_poly_chknorm (z i) (word bndz) = word 0) /\
            (l <= r /\ r < l + 2 * k
             ==> ~(mld_poly_chknorm
                    (if EVEN(r - l) then r0 ((r - l) DIV 2)
                     else ct0 ((r - l) DIV 2))
                    (word(if EVEN(r - l) then bndw else bndh)) = word 0)) /\
            (l <= r
             ==> !j. j < r - l /\ j < 2 * k
                     ==> mld_poly_chknorm
                          (if EVEN j then r0 (j DIV 2) else ct0 (j DIV 2))
                          (word(if EVEN j then bndw else bndh)) = word 0) /\
            (l + 2 * k <= r
             ==> (r = l + 2 * k + 1 <=>
                  ~(omega < mld_hint_count (mkhint x w1) (256 * k))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_sign_rej] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC
   `zb = \i. ~(mld_poly_chknorm ((z:num->num->int32) i) (word bndz) =
               word 0)` THEN
  ABBREV_TAC
   `wb = \j. ~(mld_poly_chknorm
                (if EVEN j then (r0:num->num->int32) (j DIV 2)
                 else ct0 (j DIV 2))
                (word(if EVEN j then bndw else bndh)) = word 0)` THEN
  SUBGOAL_THEN
   `(!i. (mld_poly_chknorm ((z:num->num->int32) i) (word bndz) = word 0) <=>
         ~zb i) /\
    (!j. (mld_poly_chknorm
           (if EVEN j then (r0:num->num->int32) (j DIV 2) else ct0 (j DIV 2))
           (word(if EVEN j then bndw else bndh)) = word 0) <=> ~wb j)`
   (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC ["zb"; "wb"] THEN REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `?i. i < l /\ (zb:num->bool) i` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MINIMAL]) THEN
    DISCH_THEN(fun th -> DISCH_THEN(fun eq -> MP_TAC(REWRITE_RULE[eq] th))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(l <= r) /\ r <= l + 2 * k + 1 /\ ~(l + 2 * k <= r)`
     STRIP_ASSUME_TAC THENL [UNDISCH_TAC `r < l` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `i < l` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `i < r` THEN UNDISCH_TAC `r < l` THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM]) THEN
  ASM_CASES_TAC `?j. j < 2 * k /\ (wb:num->bool) j` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MINIMAL]) THEN
    ABBREV_TAC `m = minimal j. j < 2 * k /\ (wb:num->bool) j` THEN
    STRIP_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[ADD_SUB2; LE_ADD; ARITH_RULE `~(l + m < l)`] THEN
    ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `m < 2 * k` THEN ARITH_TAC;
      ASM_MESON_TAC[];
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `m < 2 * k` THEN ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM]) THEN
  COND_CASES_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[ARITH_RULE `~(l + 2 * k + 1 < l) /\ ~(l + 2 * k < l)`;
              ARITH_RULE `~((l + 2 * k + 1) < l + 2 * k)`;
              ARITH_RULE `~((l + 2 * k) < l + 2 * k)`;
              ARITH_RULE `l + 2 * k <= l + 2 * k + 1`; LE_REFL;
              ARITH_RULE `l <= l + 2 * k + 1`; ARITH_RULE `l <= l + 2 * k`;
              ARITH_RULE `~(l + 2 * k = l + 2 * k + 1)`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(*** The rows below m pass both checks if the checks below 2 * m pass ***)

let SIGN_ROWS_GOOD = prove
 (`!(r0:num->num->int32) ct0 bw bhi n m.
        (!j. j < n
             ==> mld_poly_chknorm
                  (if EVEN j then r0 (j DIV 2) else ct0 (j DIV 2))
                  (word(if EVEN j then bw else bhi)) = word 0) /\
        2 * m <= n
        ==> !j. j < m
                ==> mld_poly_chknorm (r0 j) (word bw) = word 0 /\
                    mld_poly_chknorm (ct0 j) (word bhi) = word 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `2 * j`);
    FIRST_X_ASSUM(MP_TAC o SPEC `2 * j + 1`)] THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ; ARITH_RULE `(2 * j + 1) DIV 2 = j`] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `j < m` THEN UNDISCH_TAC `2 * m <= n` THEN ARITH_TAC);;

(*** For an odd check l + 2 * q + 1 of the rows, the check before it ***)

let SIGN_ODD_ROW = prove
 (`!l r. l <= r /\ ~EVEN(r - l)
         ==> r - (l + 1) < r - l /\ EVEN(r - (l + 1)) /\
             (r - (l + 1)) DIV 2 = (r - l) DIV 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?q. r - l = 2 * q + 1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[EVEN_OR_ODD; ODD_EXISTS; ADD1]; ALL_TAC] THEN
  SUBGOAL_THEN `r - (l + 1) = 2 * q` SUBST1_TAC THENL
   [UNDISCH_TAC `r - l = 2 * q + 1` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[EVEN_MULT; ARITH_EVEN] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ; ARITH_RULE `(2 * q + 1) DIV 2 = q`] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The value that the code returns for the hints (mld_pack_hints_ret as      *)
(* mld_pack_sig_h returns it, zero-extended), and its being 0, given the     *)
(* result r of the checks when they all pass.                                *)
(* ------------------------------------------------------------------------- *)

let SIGN_PACK_HINTS_RET_ZX = prove
 (`!omega k (h:num->bool) r R.
        (r = R <=> ~(omega < mld_hint_count h (256 * k)))
        ==> word_zx (mld_pack_hints_ret omega k h):int64 =
            (if r = R then word 0 else word 4294967295)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_pack_hints_ret; NOT_LT] THEN
  DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV);;

let SIGN_NUM_OF_BYTELIST_INJ = prove
 (`!(f:num->byte) g n.
        num_of_bytelist(list_of_seq f n) = num_of_bytelist(list_of_seq g n)
        ==> !j. j < n ==> f j = g j`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `bytelist_of_num n`) THEN
  MP_TAC(ISPEC `list_of_seq (f:num->byte) n` BYTELIST_OF_NUM_OF_BYTELIST) THEN
  MP_TAC(ISPEC `list_of_seq (g:num->byte) n` BYTELIST_OF_NUM_OF_BYTELIST) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `EL j:(byte)list->byte`) THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;

(* ------------------------------------------------------------------------- *)
(* The counter kappa that the code loads with LDRH and passes to the         *)
(* sampling of y, as the polynomials of mld_sign_y need it.                  *)
(* ------------------------------------------------------------------------- *)

let SIGN_WORD_ZX_16_32_64 = prove
 (`!x:int16. word_zx(word_zx x:int32):int64 = word_zx x`,
  CONV_TAC WORD_BLAST);;

let SIGN_WORD_ZX_ZX_16 = prove
 (`!x:int16. word_zx(word_zx x:int64):int16 = x`,
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* The update of kappa at the end of a rejected attempt: the code adds l to  *)
(* the 32-bit word at sp + 116, masks it to 16 bits, stores it back and      *)
(* compares its low 16 bits with the value c = maxatt * l at which it stops. *)
(* SIGN_RET_ZX is the return value, the low 32 bits of x22 zero-extended.    *)
(* ------------------------------------------------------------------------- *)

let SIGN_ZX16_MASK = prove
 (`!y:int32. word_zx(word_zx y:int16):int32 = word_and y (word 65535)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; DIMINDEX_16;
    DIMINDEX_32; MOD_MOD_EXP_MIN; ARITH_RULE `MIN 16 32 = 16`] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `65535 = 2 EXP 16 - 1`] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD]);;

let SIGN_KAPPA_ZX = prove
 (`!(x:int32) l.
     word_zx(word_zx(word_and
       (word_zx(word_zx(word_add (word_zx(word_zx x:int64):int32) (word l))
          :int64):int32)
       (word 65535)):int64):int32 =
     word_and (word_add x (word l)) (word 65535)`,
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH]);;

let SIGN_KAPPA_CMP = prove
 (`!(x:int32) l c.
     val(word_sub (word c:int32)
          (word_zx(word_zx(word_zx(word_zx(word_add
             (word_zx(word_zx x:int64):int32) (word l)):int64):int32)
             :int16):int32)) = 0 <=>
     word_and (word_add x (word l)) (word 65535) = word c`,
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; SIGN_ZX16_MASK] THEN
  MESON_TAC[]);;

let SIGN_KAPPA_NEXT = prove
 (`!k l c.
        k + l < 65536 /\ c < 65536
        ==> word_and (word_add (word k) (word l)) (word 65535):int32 =
            word (k + l) /\
            (word (k + l):int32 = word c <=> k + l = c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `k + l < 4294967296 /\ c < 4294967296` STRIP_ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN
    MP_TAC(ISPECL [`word(k + l):int32`; `16`]
     (CONJUNCT1 WORD_AND_MASK_WORD)) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT];
    REWRITE_TAC[WORD_EQ; DIMINDEX_32; CONG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT]]);;

let SIGN_RET_ZX = prove
 (`!b. word_zx(word_zx(if b then word 0 else word 4294967292:int64):int32) =
       (if b then word 0 else word 4294967292:int64)`,
  GEN_TAC THEN COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV);;

let SIGN_HINT_X_ROW = prove
 (`!k dlo (w:num->int32) s2h t0h cphat j i.
        j < k /\ i < 256
        ==> mld_sign_hint_x k dlo w s2h t0h cphat (256 * j + i) =
            mld_poly_add (mld_sign_r0 dlo w s2h cphat j)
                         (mld_sign_ct0 t0h cphat j) i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_sign_hint_x] THEN
  SUBGOAL_THEN `256 * j + i < 256 * k /\ (256 * j + i) DIV 256 = j /\
                (256 * j + i) MOD 256 = i`
   (fun th -> REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `j < k` THEN UNDISCH_TAC `i < 256` THEN ARITH_TAC;
    ASM_SIMP_TAC[DIV_MULT_ADD; DIV_LT; ARITH_EQ; ADD_CLAUSES];
    ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]]);;

(* ------------------------------------------------------------------------- *)
(* The packing of z: byte j of the packing of a polynomial depends only on   *)
(* its coefficients, so that the bytes that mld_pack_sig_z writes for z_i    *)
(* extend those of mld_polyvec_pack for the polynomials before it.           *)
(* ------------------------------------------------------------------------- *)

let SIGN_POLYZ_PACK_17_LOCAL = prove
 (`!(a:num->int32) b j.
        (!i. i < 256 ==> a i = b i) /\ j < 576
        ==> mld_polyz_pack_17 a j = mld_polyz_pack_17 b j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyz_pack_17] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `!m. m < 4 ==> (a:num->int32)(4 * j DIV 9 + m) =
                              b(4 * j DIV 9 + m)` MP_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `j DIV 9 < 64` MP_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN SIMPLE_ARITH_TAC;
      SIMPLE_ARITH_TAC];
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]]);;

let SIGN_POLYZ_PACK_19_LOCAL = prove
 (`!(a:num->int32) b j.
        (!i. i < 256 ==> a i = b i) /\ j < 640
        ==> mld_polyz_pack_19 a j = mld_polyz_pack_19 b j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyz_pack_19] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `!m. m < 2 ==> (a:num->int32)(2 * j DIV 5 + m) =
                              b(2 * j DIV 5 + m)` MP_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `j DIV 5 < 128` MP_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN SIMPLE_ARITH_TAC;
      SIMPLE_ARITH_TAC];
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]]);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the FULL proofs of the parts.                                 *)
(*                                                                           *)
(* SIGN_LIBC_CALL_TAC is LIBC_SAFE_CALL_TAC for a call of memset or memcpy   *)
(* where the events before it may contain those of the template (f_ev_...),  *)
(* as in a loop body. SIGN_LOOP_DISCHARGE_TAC ends the body of a loop of     *)
(* ENSURES_EVENTS_WHILE_UP2_TAC: it unifies the events of the iteration with *)
(* the function of the template (after reassociating the APPENDs so that the *)
(* events before the iteration are the same on both sides) and splits the    *)
(* memaccess_inbounds goal and those of the events so far, so that each part *)
(* is discharged on its own. SIGN_PATH_DISCHARGE_TAC does the same at the    *)
(* end of a path of the attempt, whose events are those of the path, given   *)
(* by a function of the template under conditionals that the case            *)
(* assumptions select, followed by those of its start. SIGN_PC_SIMP_TAC and  *)
(* SIGN_PC_COND_TAC put the PC after a lemma or a loop in the form that the  *)
(* simulation or the postcondition needs.                                    *)
(* ------------------------------------------------------------------------- *)

(* Atomic, for proofs on several domains (see common/par.ml) *)
let sign_meta_count = par_counter ();;

let SIGN_META_EXISTS_TAC (asl,w) =
  let v = fst(dest_exists w) in
  let k = 1 + sign_meta_count () in
  let v' = mk_var("sign_" ^ fst(dest_var v) ^ "_" ^
                  string_of_int k,type_of v) in
  (CONV_TAC(GEN_ALPHA_CONV v') THEN SAFE_META_EXISTS_TAC allowed_vars_e)
  (asl,w);;

let SIGN_BETA_ALL_TAC =
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV));;

let SIGN_LOOP_UNIFY_TAC =
  REWRITE_TAC[APPEND_NIL; CONJUNCT1 APPEND; ENUMERATEL_ADD1] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  GEN_REWRITE_TAC REDEPTH_CONV [APPEND_ASSOC] THEN
  REPEAT(AP_THM_TAC THEN AP_TERM_TAC) THEN UNIFY_F_EVENTS_TAC;;

let SIGN_SPLIT_LAST_CONV =
  let th = APPEND_ASSOC in
  let rec conv tm =
    match tm with
      Comb(Comb(Const("APPEND",_),_),Comb(Comb(Const("APPEND",_),_),_)) ->
        (REWR_CONV th THENC conv) tm
    | _ -> REFL tm in
  conv;;

let SIGN_APPEND_EQ = prove
 (`!(a:(uarch_event)list) b c d. a = c /\ b = d ==> APPEND a b = APPEND c d`,
  SIMP_TAC[]);;

let SIGN_PATH_UNIFY_TAC =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [APPEND_NIL; CONJUNCT1 APPEND] THEN
  CONV_TAC(LAND_CONV SIGN_SPLIT_LAST_CONV) THEN
  MATCH_MP_TAC SIGN_APPEND_EQ THEN
  CONJ_TAC THEN (REFL_TAC ORELSE UNIFY_F_EVENTS_TAC);;

let SIGN_SELECT_TAC =
  W(fun (asl,w) ->
    let conds = map (fun t -> rand(rator(rator t))) (find_terms is_cond w) in
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if mem c conds then EQT_INTRO th
      else if is_neg c && mem (rand c) conds then EQF_INTRO th
      else failwith "") asl in
    REWRITE_TAC ths);;

let SIGN_NUMERAL_CONV =
  DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV ORELSEC NUM_MOD_CONV);;

(*** The PC after the iteration i of a loop of m <= n iterations ***)

let SIGN_PREFIX_PC = prove
 (`!i m n a b.
        i < m /\ m <= n
        ==> (if ~(i + 1 = n) then word a else word b):int64 =
            word (if i + 1 < m then a else if m < n then a else b)`,
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMPLE_ARITH_TAC);;

let SIGN_LIST_CONV = REWRITE_CONV[APPEND; APPEND_NIL; GSYM APPEND_ASSOC];;

let rec SIGN_SUFFIX_CONV s tm =
  if aconv tm s then SYM(ISPEC s (CONJUNCT1 APPEND))
  else match tm with
    Comb(Comb(Const("CONS",_),h),t) ->
      let th = SIGN_SUFFIX_CONV s t in
      let p = lhand(rand(concl th)) in
      TRANS (AP_TERM (rator tm) th) (SYM(ISPECL [h;p;s] (CONJUNCT2 APPEND)))
  | Comb(Comb(Const("APPEND",_),a),t) ->
      let th = SIGN_SUFFIX_CONV s t in
      let p = lhand(rand(concl th)) in
      TRANS (AP_TERM (rator tm) th) (ISPECL [a;p;s] APPEND_ASSOC)
  | _ -> failwith "SIGN_SUFFIX_CONV";;

let SIGN_FOLD_E2_TAC =
  let isenum t = try fst(dest_const t) = "ENUMERATEL" with Failure _ -> false in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_var(lhs c) && is_uarch_event_list_ty(type_of(lhs c)) &&
       can (find_term isenum) (rhs c)
    then REWRITE_TAC[GSYM(CONV_RULE(RAND_CONV SIGN_LIST_CONV) th)]
    else NO_TAC);;

let SIGN_SUFFIX_UNIFY_TAC =
  CONV_TAC(BINOP_CONV SIGN_LIST_CONV) THEN SIGN_FOLD_E2_TAC THEN
  W(fun (asl,w) ->
    let s = rand(rand w) in
    CONV_TAC(LAND_CONV(SIGN_SUFFIX_CONV s)) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN UNIFY_F_EVENTS_TAC);;

let rec SIGN_MA_TAC (asl,w) =
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN CONJ_TAC THEN
    SIGN_MA_TAC) ORELSE
   W(fun (_,w) ->
     let l = lhand(rator w) in
     if is_cons l && not(is_const(rand l) && fst(dest_const(rand l)) = "NIL")
     then GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_CONS] THEN CONJ_TAC THEN
          SIGN_MA_TAC
     else NO_TAC) ORELSE
   DISCHARGE_MEMACCESS_INBOUNDS_TAC) (asl,w);;

let SIGN_SUFFIX_MEMACCESS_TAC =
  CONV_TAC(RATOR_CONV(RATOR_CONV(RAND_CONV SIGN_LIST_CONV))) THEN
  TRY SIGN_FOLD_E2_TAC THEN SIGN_MA_TAC;;

let SIGN_DROP_TAC pats =
  MAP_EVERY (fun p ->
    TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
      can (term_match [] p) (concl th))))) pats;;

let SIGN_NUM_ARITH_CONV = DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV);;

let SIGN_NUMS_TAC =
  CONV_TAC SIGN_NUM_ARITH_CONV THEN REWRITE_TAC[ADD_ASSOC] THEN
  CONV_TAC SIGN_NUM_ARITH_CONV;;
