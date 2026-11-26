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

(* The part that depends on AArch64; the rest is in                          *)
(* common/fips204/properties/mldsa_native_signing.ml.                        *)

needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;
needs "common/fips204/properties/mldsa_native_signing.ml";;
needs "common/fips202/properties/keccak_fips202.ml";;

(* ------------------------------------------------------------------------- *)
(* Bytes in memory: the bytes of n bytes as a number, and the converse, at a *)
(* (with the offset off from a base B in the _OFF forms, as the addresses of *)
(* the buffers in the frame are written).                                    *)
(* ------------------------------------------------------------------------- *)

let SIGN_READ_BYTES_LIST_OF_SEQ = prove
 (`!(a:int64) n (s:armstate).
        read (memory :> bytes(a,n)) s =
        num_of_bytelist
         (list_of_seq (\j. read (memory :> bytes8 (word_add a (word j))) s) n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[list_of_seq; num_of_bytelist; READ_COMPONENT_COMPOSE;
                READ_BYTES_TRIVIAL];
    ALL_TAC] THEN
  GEN_TAC THEN
  REWRITE_TAC[ADD1; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; GSYM ADD1; list_of_seq;
              NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[num_of_bytelist; READ_MEMORY_BYTES_BYTES8; MULT_CLAUSES;
              ADD_CLAUSES]);;

let SIGN_BYTES8_OF_READ_BYTES = prove
 (`!(a:int64) n (f:num->byte) (s:armstate).
        read (memory :> bytes(a,n)) s = num_of_bytelist(list_of_seq f n)
        ==> !j. j < n
                ==> read (memory :> bytes8 (word_add a (word j))) s = f j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SIGN_READ_BYTES_LIST_OF_SEQ] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SIGN_NUM_OF_BYTELIST_INJ) THEN
  REWRITE_TAC[]);;

let SIGN_READ_BYTES_OF_BYTES8 = prove
 (`!(a:int64) n (f:num->byte) (s:armstate).
        (!j. j < n
             ==> read (memory :> bytes8 (word_add a (word j))) s = f j)
        ==> read (memory :> bytes(a,n)) s = num_of_bytelist(list_of_seq f n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SIGN_READ_BYTES_LIST_OF_SEQ] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN ASM_SIMP_TAC[]);;

let SIGN_READ_BYTES_OF_BYTES8_OFF = prove
 (`!(B:int64) off n (f:num->byte) (s:armstate).
        (!j. j < n
             ==> read (memory :> bytes8 (word_add B (word (off + j)))) s = f j)
        ==> read (memory :> bytes(word_add B (word off),n)) s =
            num_of_bytelist(list_of_seq f n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIGN_READ_BYTES_OF_BYTES8 THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

let SIGN_BYTES8_OF_READ_BYTES_OFF = prove
 (`!(B:int64) off n (f:num->byte) (s:armstate).
        read (memory :> bytes(word_add B (word off),n)) s =
        num_of_bytelist(list_of_seq f n)
        ==> !j. j < n
                ==> read (memory :> bytes8 (word_add B (word (off + j)))) s =
                    f j`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP SIGN_BYTES8_OF_READ_BYTES) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

(*** Bytes as 128-bit words, as the inlined copies load and store them, and ***)
(*** a 16-bit word that is the low half of a 32-bit one                     ***)

let SIGN_BYTES128_OF_BYTES = prove
 (`!(a:int64) k x n (s:armstate).
        read (memory :> bytes(a,k)) s = x /\ 16 * n + 16 <= k
        ==> read (memory :> bytes128(word_add a (word(16 * n)))) s =
            word((x DIV 2 EXP (128 * n)) MOD 2 EXP 128)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
    ASSUME_TAC) THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_READ_WBYTES; VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `128 * n = 8 * 16 * n`;
              ARITH_RULE `340282366920938463463374607431768211456 =
                          2 EXP (8 * 16)`; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  SUBGOAL_THEN `MIN (k - 16 * n) 16 = 16` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; REFL_TAC]);;

let SIGN_BYTES_OF_BYTES128 = prove
 (`!(a:int64) x n (s:armstate).
        (!i. i < n
             ==> read (memory :> bytes128(word_add a (word(16 * i)))) s =
                 word((x DIV 2 EXP (128 * i)) MOD 2 EXP 128))
        ==> read (memory :> bytes(a,16 * n)) s = x MOD 2 EXP (128 * n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; READ_COMPONENT_COMPOSE;
                READ_BYTES_TRIVIAL];
    ALL_TAC] THEN
  X_GEN_TAC `s:armstate` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:armstate`) THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[ARITH_RULE `n < SUC n`] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `16 * SUC n = 16 * n + 16`; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 16 * n = 128 * n`] THEN
  REWRITE_TAC[ARITH_RULE `128 * SUC n = 128 * n + 128`; EXP_ADD;
              MOD_MULT_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let SIGN_BYTES16_OF_BYTES32 = prove
 (`!(a:int64) k (s:armstate).
        read (memory :> bytes32 a) s = word k /\ k < 65536
        ==> read (memory :> bytes16 a) s = word k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `4`; `k:num`; `0`; `s:armstate`]
         READ_MEMORY_BYTES16_OF_NUM) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int32->num`) THEN
    REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
                VAL_WORD; DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `k < 65536 ==> k < 4294967296`];
    REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; EXP; DIV_1] THEN
    ASM_SIMP_TAC[MOD_LT]]);;

let SIGN_Y_KAPPA = prove
 (`!(g:num->int16->num->int32) rhop k.
        mld_polyvec
         (\j. g rhop (word_add (word_zx(word_zx(word k:int16):int64))
                               (word j))) =
        mld_sign_y g rhop k`,
  REWRITE_TAC[SIGN_WORD_ZX_ZX_16; mld_sign_y; GSYM WORD_ADD]);;

(* ------------------------------------------------------------------------- *)
(* Polynomial i of a vector at off + 1024 * i from B, copied by memcpy to    *)
(* doff (the two regions have the same bytes zs after the call): the copy    *)
(* has the coefficients of mld_poly_of f i.                                  *)
(* ------------------------------------------------------------------------- *)

let SIGN_COPY_POLY = prove
 (`!(B:int64) doff soff i n (f:num->int32) zs (s:armstate).
        read (memory :> bytes (word_add B (word doff),1024)) s = zs /\
        read (memory :> bytes (word_add B (word (soff + 1024 * i)),1024)) s =
        zs /\
        (!j. j < n
             ==> read (memory :> bytes32 (word_add B (word (soff + 4 * j)))) s =
                 f j) /\
        256 * i + 256 <= n
        ==> !j. j < 256
                ==> read (memory :> bytes32 (word_add B (word (doff + 4 * j))))
                      s = mld_poly_of f i j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`word_add B (word doff):int64`;
                `word_add B (word (soff + 1024 * i)):int64`; `256`;
                `s:armstate`; `s:armstate`] VEC_BYTES_EQ_BYTES32) THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV NUM_MULT_CONV)) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[mld_poly_of] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `256 * i + j`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `j < 256` THEN UNDISCH_TAC `256 * i + 256 <= n` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; ADD_ASSOC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The rows of w0 as the loop over them leaves them: row j of the low part   *)
(* (for its first check), the rows after it, and the rows before j + 1 once  *)
(* row j holds w0_j - c s2_j + c t0_j, as mld_sign_hint_x gives it.          *)
(* ------------------------------------------------------------------------- *)

let SIGN_ROW_SLICE = prove
 (`!(B:int64) off n f (w:num->int32) j (s:armstate).
        (!k. 256 * j <= k /\ k < n
             ==> read (memory :> bytes32 (word_add B (word (off + 4 * k)))) s =
                 mld_polyvec_map f w k) /\
        256 * (j + 1) <= n
        ==> (!i. i < 256
                 ==> read (memory :> bytes32
                            (word_add B (word ((off + 1024 * j) + 4 * i)))) s =
                     f (mld_poly_of w j) i) /\
            (!k. 256 * (j + 1) <= k /\ k < n
                 ==> read (memory :> bytes32 (word_add B (word (off + 4 * k))))
                       s = mld_polyvec_map f w k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `256 * j + i`) THEN
    ASM_SIMP_TAC[MLD_POLYVEC_MAP_COEFF] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; ADD_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `i < 256` THEN UNDISCH_TAC `256 * (j + 1) <= n` THEN ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `256 * (j + 1) <= k` THEN UNDISCH_TAC `k < n` THEN
    ARITH_TAC]);;

let SIGN_ROW_JOIN = prove
 (`!(B:int64) off k dlo (w:num->int32) s2h t0h cphat j (s:armstate).
        j < k /\
        (!m. m < 256 * j
             ==> read (memory :> bytes32 (word_add B (word (off + 4 * m)))) s =
                 mld_sign_hint_x k dlo w s2h t0h cphat m) /\
        (!i. i < 256
             ==> read (memory :> bytes32
                        (word_add B (word ((off + 1024 * j) + 4 * i)))) s =
                 mld_poly_add (mld_sign_r0 dlo w s2h cphat j)
                              (mld_sign_ct0 t0h cphat j) i)
        ==> !m. m < 256 * (j + 1)
                ==> read (memory :> bytes32 (word_add B (word (off + 4 * m))))
                      s = mld_sign_hint_x k dlo w s2h t0h cphat m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `m < 256 * j` THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m - 256 * j`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `m < 256 * (j + 1)` THEN UNDISCH_TAC `~(m < 256 * j)` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(off + 1024 * j) + 4 * (m - 256 * j) = off + 4 * m`
   SUBST1_TAC THENL
   [UNDISCH_TAC `~(m < 256 * j)` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `m = 256 * j + (m - 256 * j)`
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
   [UNDISCH_TAC `~(m < 256 * j)` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SIGN_HINT_X_ROW THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `m < 256 * (j + 1)` THEN UNDISCH_TAC `~(m < 256 * j)` THEN
  ARITH_TAC);;

let SIGN_PACK_JOIN = prove
 (`!(f:(num->int32)->num->byte) P (z:num->num->int32) (sig:int64) off i
    (s:armstate).
        (!a b j. (!i. i < 256 ==> a i = b i) /\ j < P ==> f a j = f b j) /\
        (!t. t < P * i
             ==> read (memory :> bytes8 (word_add sig (word (off + t)))) s =
                 mld_polyvec_pack P f (mld_polyvec z) t) /\
        (!j. j < P
             ==> read (memory :> bytes8 (word_add sig (word (off + P * i + j))))
                   s = f (z i) j)
        ==> !t. t < P * (i + 1)
                ==> read (memory :> bytes8 (word_add sig (word (off + t)))) s =
                    mld_polyvec_pack P f (mld_polyvec z) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `t < P * i` THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t - P * i`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `t < P * (i + 1)` THEN UNDISCH_TAC `~(t < P * i)` THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `off + P * i + t - P * i = off + t` SUBST1_TAC THENL
   [UNDISCH_TAC `~(t < P * i)` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `t = P * i + (t - P * i)` (fun th ->
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [UNDISCH_TAC `~(t < P * i)` THEN ARITH_TAC; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLD_POLYVEC_PACK_COEFF o rand o snd) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `t < P * (i + 1)` THEN UNDISCH_TAC `~(t < P * i)` THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [SIMP_TAC[MLD_POLY_OF_POLYVEC];
    UNDISCH_TAC `t < P * (i + 1)` THEN UNDISCH_TAC `~(t < P * i)` THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The signature of a successful attempt, from its three parts: c~ (ctlen    *)
(* bytes), z (zlen bytes after it) and the hints (hlen bytes after that), in *)
(* the form of mld_sign_attempt_sig.                                         *)
(* ------------------------------------------------------------------------- *)

let SIGN_SIG_ASSEMBLE = prove
 (`!(sig:int64) (ct:num->byte) zz hh ctlen zlen hlen (s:armstate).
        (!j. j < ctlen
             ==> read (memory :> bytes8 (word_add sig (word j))) s = ct j) /\
        (!t. t < zlen
             ==> read (memory :> bytes8 (word_add sig (word (ctlen + t)))) s =
                 zz t) /\
        (!t. t < hlen
             ==> read (memory :> bytes8
                        (word_add sig (word ((ctlen + zlen) + t)))) s = hh t)
        ==> !t. t < (ctlen + zlen) + hlen
                ==> read (memory :> bytes8 (word_add sig (word t))) s =
                    (if t < ctlen then ct t
                     else if t < ctlen + zlen then zz (t - ctlen)
                     else hh (t - (ctlen + zlen)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `t - ctlen` o check (fun th ->
      can (term_match [`zlen:num`] `!t. t < zlen ==> P t`) (concl th)));
    FIRST_X_ASSUM(MP_TAC o SPEC `t - (ctlen + zlen)` o check (fun th ->
      can (term_match [`hlen:num`] `!t. t < hlen ==> P t`) (concl th)))] THEN
  (ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC EQ_IMP THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  SIMPLE_ARITH_TAC);;

let SIGN_LIBC_CALL_TAC name execth ilist allowed n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true execth th ilist n THENL
     [FULL_EXISTS_E2_TAC allowed; LABEL_TAC name th]);;

let SIGN_SPLIT_MEMACCESS_ASM_TAC =
  W(fun (asl,w) ->
    let is_ev_eq th =
      let c = concl th in
      is_eq c && is_var(lhs c) && is_uarch_event_list_ty(type_of(lhs c)) in
    let eths = map snd (filter (is_ev_eq o snd) asl) in
    let mas = filter (fun (_,th) ->
      match strip_comb(concl th) with
        (Const("memaccess_inbounds",_),[_;_;_]) -> true
      | _ -> false) asl in
    MAP_EVERY (fun (_,th) ->
      UNDISCH_THEN (concl th) (fun th' ->
        STRIP_ASSUME_TAC
         (REWRITE_RULE (MEMACCESS_INBOUNDS_APPEND::eths) th'))) mas);;

let SIGN_MEMACCESS_TAC =
  SIGN_BETA_ALL_TAC THEN SIGN_SPLIT_MEMACCESS_ASM_TAC THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN REPEAT CONJ_TAC THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

let SIGN_LOOP_DISCHARGE_TAC =
  SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_LOOP_UNIFY_TAC; SIGN_MEMACCESS_TAC];;

let SIGN_CONCRETE_DISCHARGE_TAC =
  SIGN_BETA_ALL_TAC THEN
  REWRITE_TAC[ENUMERATEL; APPEND; APPEND_NIL] THEN
  SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[APPEND; APPEND_NIL]; SIGN_MEMACCESS_TAC];;

let SIGN_NIL_EVENTS_TAC =
  EXISTS_TAC `[]:(uarch_event)list` THEN
  REWRITE_TAC[APPEND; memaccess_inbounds; ALL];;

let SIGN_PATH_DISCHARGE_TAC =
  SIGN_BETA_ALL_TAC THEN SIGN_SELECT_TAC THEN SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_PATH_UNIFY_TAC; SIGN_MEMACCESS_TAC];;

let SIGN_PC_SIMP_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `read PC s = x`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let SIGN_PC_COND_TAC =
  FIRST_X_ASSUM(MP_TAC o check (can (term_match []
    `read PC s = word (if b then x else y)`) o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COND_RAND] THEN DISCH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Tactics for the FULL proof of a whole function.                           *)
(*                                                                           *)
(* SIGN_SEL_DISCHARGE_TAC ends a path whose template is selected by the case *)
(* assumptions, as SIGN_PATH_DISCHARGE_TAC, with FULL_UNIFY_F_EVENTS_TAC for *)
(* the events. After calls of memset and memcpy the events so far are        *)
(* reassociated (FULL_EXISTS_E2_TAC), so that at the end of an iteration of  *)
(* the outer loop, or of its exit, those of the invariant are no longer a    *)
(* suffix of the events: SIGN_SUFFIX_UNIFY_TAC puts both sides in normal     *)
(* form (SIGN_LIST_CONV, under the lambdas and conditionals too), folds the  *)
(* normal form of the events e2 of the invariant back into e2 and unifies    *)
(* the part before it with the template (of the form APPEND f_ev e2), and    *)
(* SIGN_SUFFIX_MEMACCESS_TAC does the same for the memory safety, taking     *)
(* that of e2 from the assumptions and splitting the rest. SIGN_DROP_TAC     *)
(* drops the assumptions that match one of the patterns, e.g. equations      *)
(* that would rewrite the postcondition in the simulation of a call.         *)
(* SIGN_NUMS_TAC and SIGN_NUM_ARITH_CONV evaluate numeral sums and products, *)
(* and SIGN_PC_SIMP_RW_TAC rewrites the PC with the assumptions and ths.     *)
(* ------------------------------------------------------------------------- *)

let SIGN_SEL_DISCHARGE_TAC =
  SIGN_BETA_ALL_TAC THEN SIGN_SELECT_TAC THEN SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; SIGN_MEMACCESS_TAC];;

let SIGN_PC_SIMP_RW_TAC ths =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `read PC s = x`) (concl th))) THEN
  ASM_REWRITE_TAC ths THEN DISCH_TAC;;
