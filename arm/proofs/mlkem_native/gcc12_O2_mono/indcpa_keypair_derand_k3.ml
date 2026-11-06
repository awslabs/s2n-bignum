(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The key generation of K-PKE for ML-KEM-768 (FIPS 203 Algorithm 13). This  *)
(* is the code for mlkem768_indcpa_keypair_derand from mlkem-native's        *)
(* portable C implementation compiled by gcc 12 with -O2 as one translation  *)
(* unit (see mlkem_native/README.md). It hashes the 32-byte seed d followed  *)
(* by the byte 3 with SHA3-512 into the seeds rho and sigma, generates the   *)
(* matrix in NTT form from rho, samples the secret s and the error e from    *)
(* sigma and transforms them, computes t = A s + e in the NTT domain, and    *)
(* writes the encoding of t followed by rho as the public key and the        *)
(* encoding of s as the secret key, zeroing its buffers. It is verified in   *)
(* the whole image (see libmlkem.ml), using the theorems for mlkem_sha3_512, *)
(* mlkem768_gen_matrix, mlkem768_poly_getnoise_eta1_4x, mlk_poly_ntt_c,      *)
(* mlk_poly_mulcache_compute_c,                                              *)
(* mlk_polyvec_basemul_acc_montgomery_cached_c768, mlk_poly_reduce_c and     *)
(* mlk_poly_tobytes_c in the image, and the contracts for memset and         *)
(* memcpy.                                                                   *)
(*                                                                           *)
(* Differences from the gcc 12 -O2 proof. gcc has inlined all the polyvec    *)
(* functions:                                                                *)
(*                                                                           *)
(*  - polyvec_ntt, polyvec_mulcache_compute, polyvec_reduce and              *)
(*    polyvec_tobytes: the kernel is called for each polynomial, and the     *)
(*    postcondition of the polyvec function is proved from those of the      *)
(*    calls (mlkem_native/indcpa_inline.ml);                                 *)
(*  - polyvec_basemul: a loop over the rows calling the c768 kernel, which   *)
(*    is the gcc 12 -O2 mlkem768_polyvec_basemul_acc_montgomery_cached, as   *)
(*    the gcc 12 -O2 code does;                                              *)
(*  - polyvec_tomont and polyvec_add: two nested loops each, the inner one   *)
(*    the vector code of poly_tomont or poly_add for one polynomial. The     *)
(*    inner loops are proved as lemmas from their head to their exit, with   *)
(*    the events (mlkem_native/inline_loops.ml), and the outer loops, of     *)
(*    three iterations, are unrolled.                                        *)
(*                                                                           *)
(* The buffers are at the same offsets from each other as with gcc 12 -O2;   *)
(* the frame is the 10288 bytes of the function and the 4400 of              *)
(* mlkem768_gen_matrix below them, 14688 in all.                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/sha3_512.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/gen_matrix_k3.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_getnoise_eta1_4x_k3.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_ntt.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_mulcache_compute.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/basemul_k3.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_reduce.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_tobytes.ml";;
needs "arm/proofs/mlkem_native/indcpa_inline.ml";;
needs "arm/proofs/mlkem_native/inline_loops.ml";;

(*** The code in the image is listed at the end of layout.ml, with the
     labels of the inlined calls. ***)

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "plt_memset"; layout_range "mlkem768_indcpa_keypair_derand"];;

let KP3_EXEC = MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_GCC12_O2_MONO_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The key generation in FIPS 203 in terms of the coefficients computed by   *)
(* the code: those of the NTTs of s and e, those of the multiplication       *)
(* cache, those of the matrix-vector product in Montgomery form, and those   *)
(* of the final results after Montgomery conversion, addition and reduction. *)
(* The two lemmas on single coefficients relate the computation of the code  *)
(* to MultiplyNTTs and the addition of e in the NTT domain, for even and odd *)
(* coefficients.                                                             *)
(* ------------------------------------------------------------------------- *)

let KPKE_KEYGEN_COEFF_EVEN_K3 = prove
 (`!(A:num->num->int) (Y:num->num->int) (YT:num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 3 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329) /\
                    (YT j == Y j (2 * p + 1) *
                             &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (t == &169 * ((A 2 (2 * p + 1) * YT 2 + A 2 (2 * p) * Y 2 (2 * p)) +
                   (A 1 (2 * p + 1) * YT 1 + A 1 (2 * p) * Y 1 (2 * p)) +
                   (A 0 (2 * p + 1) * YT 0 + A 0 (2 * p) * Y 0 (2 * p))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 3}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p)))
          eh`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_3;
              FIPS203_MULTIPLY_NTTS_INT] THEN
  REWRITE_TAC[EVEN_DOUBLE; ARITH_RULE `(2 * p) DIV 2 = p`] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`(&17:int) pow (2 * bitreverse7 p + 1)`,`z:int`) THEN GEN_TAC THEN
  MP_TAC(prove(`(&65536 * &169:int == &1) (mod &3329)`,
               REWRITE_TAC[int_congruent] THEN EXISTS_TAC `&3327:int` THEN
               INT_ARITH_TAC)) THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&169:int`,`ri:int`) THEN
  SPEC_TAC(`&65536:int`,`r:int`) THEN REPEAT GEN_TAC THEN
  CONV_TAC INTEGER_RULE);;

let KPKE_KEYGEN_COEFF_ODD_K3 = prove
 (`!(A:num->num->int) (Y:num->num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 3 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329)) /\
     (t == &169 *
           ((A 2 (2 * p + 1) * Y 2 (2 * p) + A 2 (2 * p) * Y 2 (2 * p + 1)) +
            (A 1 (2 * p + 1) * Y 1 (2 * p) + A 1 (2 * p) * Y 1 (2 * p + 1)) +
            (A 0 (2 * p + 1) * Y 0 (2 * p) + A 0 (2 * p) * Y 0 (2 * p + 1))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 3}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p + 1)))
          eh`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_3;
              FIPS203_MULTIPLY_NTTS_INT] THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN; ADD_SUB] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  MP_TAC(prove(`(&65536 * &169:int == &1) (mod &3329)`,
               REWRITE_TAC[int_congruent] THEN EXISTS_TAC `&3327:int` THEN
               INT_ARITH_TAC)) THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&169:int`,`ri:int`) THEN
  SPEC_TAC(`&65536:int`,`r:int`) THEN REPEAT GEN_TAC THEN
  CONV_TAC INTEGER_RULE);;

let KPKE_KEYGEN_K3_RESULT = prove
 (`!d rho sigma (sh:num->int16) (eh:num->int16) (mc:num->int16)
    (pt:num->int16) (pt2:num->int16) (tr:num->int16) (sr:num->int16).
     mlkem_g(APPEND d [word 3]) = rho,sigma /\
     (!i j n. i < 3 /\ j < 3 /\ n < 256
              ==> mlkem_sample_ntt (APPEND rho [word j; word i]) n < &3329) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(sh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word j))) i)
                (mod &3329) /\
                abs(ival(sh(256 * j + i))) <= &23594) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(eh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(3 + j)))) i)
                (mod &3329) /\
                abs(ival(eh(256 * j + i))) <= &23594) /\
     (!j p. j < 3 /\ p < 128
            ==> (ival(mc(128 * j + p)) ==
                 ival(sh(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!r p. r < 3 /\ p < 128
            ==> (ival(pt(256 * r + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(mc(256 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(sh(512 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(mc(128 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(mc p) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p))))) (mod &3329) /\
                (ival(pt(256 * r + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(sh(512 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(sh(512 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(sh(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(sh(2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p + 1))))) (mod &3329)) /\
     (!i. i < 768 ==> (ival(pt2 i) == &65536 * ival(pt i)) (mod &3329) /\
                      abs(ival(pt2 i)) <= &3328) /\
     (!i. i < 768 ==> ival(tr i) = ival(word_add (pt2 i) (eh i)) rem &3329) /\
     (!i. i < 768 ==> ival(sr i) = ival(sh i) rem &3329)
     ==> num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq tr 768)) +
         2 EXP (8 * 1152) * num_of_bytelist rho =
         num_of_bytelist(FST(kpke_keygen mlkem768 d)) /\
         num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq sr 768)) =
         num_of_bytelist(SND(kpke_keygen mlkem768 d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem768] THEN
  MP_TAC(SPECL [`3`; `2`; `2`; `10`; `4`; `d:byte list`] KPKE_KEYGEN_FIPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; MLKEM_ENCODE_LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `256 * 3 = 768`;
              ARITH_RULE `(12 * 768) DIV 8 = 1152`] THEN
  W(fun (_,w) ->
    let encs = find_terms (fun t -> match strip_comb t with
       (Const("mlkem_encode",_),[_;_;_]) -> true | _ -> false) w in
    MAP_EVERY (fun enc ->
      MP_TAC(PART_MATCH (lhand o rand) MLKEM_ENCODE_12_LIST
              (mk_comb(`num_of_bytelist`,enc)))) encs) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ARITH_RULE `EVEN 768`; MLKEM_NTT_CBD_BOUNDS] THEN
  SIMP_TAC[GSYM IN_MLKEM_ZQ; RING_ADD; RING_SUM; MLKEM_NTT_CBD_IN_ZQ] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC;
    AP_TERM_TAC THEN AP_TERM_TAC] THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM IWORD_IVAL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[IWORD_IVAL] THEN
  MP_TAC(SPECL [`256`; `3`; `i:num`] EXISTS_DIV_MOD_LT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `256 * 3 = 768`] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `n:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[DIV_MOD_ADD_LT] THENL
   [ALL_TAC;
    TRANS_TAC EQ_TRANS
     `(mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word r))) n) rem &3329` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INT_REM_EQ] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC INT_REM_LT THEN REWRITE_TAC[MLKEM_NTT_CBD_BOUNDS]]] THEN
  SUBGOAL_THEN `?p. p < 128 /\ (n = 2 * p \/ n = 2 * p + 1)` MP_TAC THENL
   [MP_TAC(SPECL [`2`; `128`; `n:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 128 = 256`] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:num`; `m:num`] THEN
    REWRITE_TAC[ARITH_RULE `m < 2 <=> m = 0 \/ m = 1`] THEN
    STRIP_TAC THEN EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `p:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
  (SUBGOAL_THEN `2 * p < 256 /\ 2 * p + 1 < 256` STRIP_ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  W(fun (_,w) ->
    let t = find_term (fun t -> match t with
      Comb(Const("ival",_),Comb(Comb(Const("word_add",_),_),_)) -> true
      | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) IVAL_WORD_ADD_SMALL t)) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THENL
   [MP_TAC(SPECL
     [`\j. mlkem_sample_ntt (APPEND rho [word j; word r])`;
      `\j n. ival((sh:num->int16)(256 * j + n))`;
      `\j. ival((mc:num->int16)(128 * j + p))`;
      `\j. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word j)))`;
      `ival((pt:num->int16)(256 * r + 2 * p))`;
      `ival((pt2:num->int16)(256 * r + 2 * p))`;
      `ival((eh:num->int16)(256 * r + 2 * p))`;
      `mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(3 + r)))) (2 * p)`;
      `p:num`] KPKE_KEYGEN_COEFF_EVEN_K3);
    MP_TAC(SPECL
     [`\j. mlkem_sample_ntt (APPEND rho [word j; word r])`;
      `\j n. ival((sh:num->int16)(256 * j + n))`;
      `\j. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word j)))`;
      `ival((pt:num->int16)(256 * r + 2 * p + 1))`;
      `ival((pt2:num->int16)(256 * r + 2 * p + 1))`;
      `ival((eh:num->int16)(256 * r + 2 * p + 1))`;
      `mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(3 + r))))
                 (2 * p + 1)`;
      `p:num`] KPKE_KEYGEN_COEFF_ODD_K3)] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16. The input to SHA3-512 is the seed copied as two 128-bit words and  *)
(* the byte 3 (the parameter k), and its output is the two seeds rho and     *)
(* sigma as in mlkem_g.                                                      *)
(* ------------------------------------------------------------------------- *)

let KP3_ALIGNED_16_32 = prove
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
           ARITH_RULE `x < 32 ==> x < 2 EXP 64`]);;

let KP3_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 4591)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 4576 else 4560))`,
  REWRITE_TAC[KP3_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let KP3_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KP3_BUFFER_ADDRESS))
    else NO_TAC);;

let KP3_INPUT_TAC b s =
  MP_TAC(SPECL [INDCPA_SP(b + 10048); `d:byte list`; `3`; s]
               INLINE_SEED_INPUT) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV;
    STRIP_TAC];;

let KP3_G_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
             `read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 c)`)
           (concl th)
    then ASSUME_TAC th THEN
         MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                 (REWRITE_RULE
                   [ASSUME `FST(mlkem_g(APPEND d [word 3])) = rho`;
                    ASSUME `SND(mlkem_g(APPEND d [word 3])) = sigma`]
                   (MATCH_MP MLKEM_G_BYTES th))) THEN
         CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC
    else NO_TAC);;

(*** A seed of 32 bytes as two 128-bit words: the seed d at coins, and rho
     before it is copied into the public key ***)

let KP3_HALVES_TAC a v =
  let pat = subst [a,`a:int64`]
   (parse_term(Printf.sprintf
     "read (memory :> bytes(a,32)) s = num_of_bytelist %s" v)) in
  let avoid = subtract (frees pat) [`s:armstate`] in
  FIRST_ASSUM(MP_TAC o MATCH_MP INLINE_BYTES128_HALVES o check (fun th ->
    can (term_match avoid pat) (concl th))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC;;

let KP3_RHO_TAC s =
  MP_TAC(SPECL [`word_add pk (word 1152):int64`; `num_of_bytelist rho`;
                mk_var(s,`:armstate`)] INLINE_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `rho:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* The inner loops of polyvec_tomont and polyvec_add, the inlined vector     *)
(* code of poly_tomont and poly_add for one polynomial, as lemmas from their *)
(* head to their exit, with the events (mlkem_native/inline_loops.ml).       *)
(* ------------------------------------------------------------------------- *)

let KP3_TOMONT = INLINE_TOMONT_LOOP_REG
  "mlkem_native_libmlkem_gcc12_O2_mono_mc" KP3_EXEC
  "mlkem768_indcpa_keypair_derand_loop3"
  "mlkem768_indcpa_keypair_derand_loop3_exit" "X0" "X1";;

let KP3_ADD = INLINE_REG_IDX_LOOP "mlkem_native_libmlkem_gcc12_O2_mono_mc"
  KP3_EXEC "add" "mlkem768_indcpa_keypair_derand_loop5"
  "mlkem768_indcpa_keypair_derand_loop5_exit" "X28" "X1" "X0";;

(* ------------------------------------------------------------------------- *)
(* The callees, and the lemmas for the inlined loops, as for subroutines.    *)
(* The matrix is generated without transposition, and the fourth output of   *)
(* mlkem768_poly_getnoise_eta1_4x is a null pointer (its fourth nonce, at    *)
(* the bottom of the stack, is 255), so the theorems are specialized to      *)
(* those cases, as for gcc 12 -O2.                                           *)
(* ------------------------------------------------------------------------- *)

let KP3_SUB_TAC th =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,th);;

let LOCAL_SHA3_512_TAC =
  KP3_SUB_TAC MLKEM_NATIVE_SHA3_512_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_GEN_MATRIX_TAC =
  KP3_SUB_TAC
   (INDCPA_GEN_MATRIX_SPEC
     MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT
     `word 0:int64`);;

let LOCAL_GETNOISE_TAC =
  KP3_SUB_TAC
   (INDCPA_GETNOISE_NULL
     MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_NTT_TAC =
  KP3_SUB_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_MULCACHE_TAC =
  KP3_SUB_TAC
   MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_BASEMUL_TAC =
  KP3_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REDUCE_TAC =
  KP3_SUB_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_TOBYTES_TAC =
  KP3_SUB_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let KP3_LEMMA_TAC name ilist n =
  USE_THEN name (fun th -> KP3_SUB_TAC th ilist n);;

(*** The vectors of constants of the tomont loops, from the image ***)

let KP3_CONSTANTS =
  map (fun d -> MLKEM_NATIVE_IMAGE_CONST_RULE d 128)
   [layout "mlkem768_indcpa_keypair_derand_const2";
    layout "mlk_poly_invntt_tomont_c_const2"];;

let KP3_SP n = Printf.sprintf "word_add stackpointer (word %d)" n;;

(* ------------------------------------------------------------------------- *)
(* The facts about the stages of the computation other than those given by   *)
(* the tactics in mlkem_native_indcpa.ml: the coefficients of the matrix as  *)
(* given by SampleNTT, the bounds on the inputs of the multiplications, the  *)
(* rows of the matrix-vector product, and rho in the public key.             *)
(* ------------------------------------------------------------------------- *)

let KP3_MATRIX_TAC b s =
  let addr = parse_term(Printf.sprintf
    "word_add stackpointer (word (%d + 512 * (3 * r + j))):int64" b) in
  SUBGOAL_THEN
   `!r j n. r < 3 /\ j < 3 /\ n < 256
            ==> &0 <= mlkem_sample_ntt (APPEND rho [word j; word r]) n /\
                mlkem_sample_ntt (APPEND rho [word j; word r]) n < &3329`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC MLKEM_SAMPLE_NTT_REJ_BOUND THEN
    EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r j n. r < 3 /\ j < 3 /\ n < 256
            ==> ival((AM:num->int16)(768 * r + 256 * j + n)) =
                mlkem_sample_ntt (APPEND rho [word j; word r]) n`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    INDCPA_GHOST_SPEC_TAC "AM" `768 * r + 256 * j + n` THEN
    MP_TAC(SPECL [addr; s; `APPEND (rho:byte list) [word j; word r]`;
                  `k:num`; `n:num`]
                 MLKEM_NATIVE_SAMPLE_COEFF) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    MATCH_MP_TAC READ16_OFFSET_EQ THEN ARITH_TAC;
    ALL_TAC];;

let KP3_AM_INST r j =
  let th = SPECL [mk_small_numeral r; mk_small_numeral j]
    (ASSUME `!r j n. r < 3 /\ j < 3 /\ n < 256
                     ==> ival((AM:num->int16)(768 * r + 256 * j + n)) =
                         mlkem_sample_ntt (APPEND rho [word j; word r]) n`) in
  CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES; ADD_ASSOC] THENC
            NUM_REDUCE_CONV) th;;

let KP3_PT_GOAL = `!r p. r < 3 /\ p < 128
            ==> (ival((PT:num->int16)(256 * r + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival((MC:num->int16)(256 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival((SH:num->int16)(512 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(MC(128 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(SH(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(MC p) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(SH(2 * p))))) (mod &3329) /\
                (ival(PT(256 * r + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(SH(512 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(SH(512 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(SH(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(SH(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(SH(2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(SH(2 * p + 1))))) (mod &3329)`;;

let KP3_AM_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 2304 ==> abs(ival((AM:num->int16) m)) <= &2 pow 12`
  (LABEL_TAC "ambound") THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`768`; `3`; `m:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `768 * 3 = 2304`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:num`; `q:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`256`; `3`; `q:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 3 = 768`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(INT_ARITH
     `&0 <= x /\ x < &3329 ==> abs(x:int) <= &2 pow 12`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC];;

let KP3_BASEMUL_DEFS =
  [basemul3_even; basemul3_odd; pmul_acc3; pmull_acc3; pmull];;

let KP3_PT_TAC b s =
  INDCPA_GHOST_TAC "PT" (b + 6144) 768 s THEN
  SUBGOAL_THEN KP3_PT_GOAL ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THENL
     (map (fun r -> INDCPA_BASEMUL3_ROW_TAC "PT" (b + 6144 + 512 * r)
                     "ambound" (map (KP3_AM_INST r) [0;1;2])
                     KP3_BASEMUL_DEFS) [0;1;2]);
    ALL_TAC];;

let KP3_FINAL_TAC =
  REWRITE_TAC[ARITH_RULE `1184 = 1152 + 32`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`d:byte list`; `rho:byte list`; `sigma:byte list`;
                `SH:num->int16`; `EH:num->int16`; `MC:num->int16`;
                `PT:num->int16`; `PT2:num->int16`; `TR:num->int16`;
                `SR:num->int16`] KPKE_KEYGEN_K3_RESULT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `FST(mlkem_g(APPEND d [word 3])) = rho`);
                  GSYM(ASSUME `SND(mlkem_g(APPEND d [word 3])) = sigma`);
                  PAIR];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    SIMP_TAC[]];;


(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy (the      *)
(* latter for the callees), as for gcc 12 -O2, with the frame of this code:  *)
(* the 10288 bytes of the function and the 4400 of mlkem768_gen_matrix below *)
(* them. The proof is by cases on whether the stack pointer is a multiple of *)
(* 32, which gives the address b of the buffers, at offsets 0 (the matrix),  *)
(* 4608 (s), 6144 (t), 7680 (e), 9216 (the multiplication cache), 9984 (rho  *)
(* and sigma) and 10048 (the input of SHA3-512).                             *)
(* ------------------------------------------------------------------------- *)

let KP3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `sk:int64`; `coins:int64`; `d:byte list`; `guard:int64`;
    `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 14688 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 14688):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28) THEN
  UNDISCH_TAC
   `!i j. i < 3 /\ j < 3
          ==> mlkem_samplentt_terminates
               (APPEND (FST(mlkem_g(APPEND d [word 3])))
                       [word j; word i])` THEN
  ABBREV_TAC `rho = FST(mlkem_g(APPEND d [word 3]))` THEN
  ABBREV_TAC `sigma = SND(mlkem_g(APPEND d [word 3]))` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`3`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN `LENGTH(rho:byte list) = 32 /\ LENGTH(sigma:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rho"; "sigma"] THEN REWRITE_TAC[LENGTH_MLKEM_G];
    ALL_TAC] THEN
  X_CHOOSE_THEN `ft:int64->num->(uarch_event)list`
    (LABEL_TAC "H_TOMONT") KP3_TOMONT THEN
  X_CHOOSE_THEN `fa:int64->int64->num->(uarch_event)list`
    (LABEL_TAC "H_ADD") KP3_ADD;;

let KP3_CASE_TAC b =
  let st n = "s"^string_of_int n in
  let sp n = KP3_SP n in
  ENSURES_INIT_TAC "s0" THEN
  KP3_HALVES_TAC `coins:int64` "d" THEN

  (*** The setup, the input to SHA3-512 and the call ***)

  ARM_STEPS_TAC KP3_EXEC (1--9) THEN KP3_BUFFER_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (10--27) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (28--35) THEN
  KP3_INPUT_TAC b `s35:armstate` THEN INLINE_GOT_TAC THEN
  ARM_STEPS_TAC KP3_EXEC [36] THEN
  LOCAL_SHA3_512_TAC
   [`read X0 s`; `read X1 s`; `APPEND d [word 3]:byte list`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 37 THEN
  KP3_G_TAC THEN

  (*** The matrix ***)

  ARM_STEPS_TAC KP3_EXEC (38--41) THEN
  LOCAL_GEN_MATRIX_TAC
   [`read X0 s`; `read X1 s`; `rho:byte list`; `k:num`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 42 THEN
  INDCPA_GHOST_TAC "AM" b 2304 (st 42) THEN
  KP3_MATRIX_TAC b `s42:armstate` THEN

  (*** The noise ***)

  ARM_STEPS_TAC KP3_EXEC (43--54) THEN INDCPA_NONCE_TAC 255 THEN
  INLINE_GOT_TAC THEN
  LOCAL_GETNOISE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X4 s`;
    `sigma:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 255:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 55 THEN
  INDCPA_NOISE_TAC "S0" (b + 4608) 3 "sigma" "word j" (st 55) THEN
  ARM_STEPS_TAC KP3_EXEC (56--70) THEN INLINE_GOT_TAC THEN
  LOCAL_GETNOISE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X4 s`;
    `sigma:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 255:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 71 THEN
  INDCPA_NOISE_TAC "E0" (b + 7680) 3 "sigma" "word(3 + j)" (st 71) THEN
  INDCPA_DISCARD_LETS_TAC THEN

  (*** The NTTs of s and e ***)

  POLYVEC_GHOST_SPLIT_TAC "S0" (b + 4608) 3 (st 71) THEN
  POLYVEC_GHOST_SPLIT_TAC "E0" (b + 7680) 3 (st 71) THEN
  ARM_STEPS_TAC KP3_EXEC (72--73) THEN
  LOCAL_NTT_TAC [`read X0 s`; `S0:num->int16`; `pc:num`; `read X30 s`] 74 THEN
  ARM_STEPS_TAC KP3_EXEC (75--77) THEN
  LOCAL_NTT_TAC [`read X0 s`; `\i. (S0:num->int16)(256 + i)`; `pc:num`;
                 `read X30 s`] 78 THEN
  ARM_STEPS_TAC KP3_EXEC (79--83) THEN
  LOCAL_NTT_TAC [`read X0 s`; `\i. (S0:num->int16)(512 + i)`; `pc:num`;
                 `read X30 s`] 84 THEN
  POLYVEC_INLINE_JOIN_TAC 3 [] (PV_NTT_POST 3 (sp(b + 4608)) "S0" (st 84)) THEN
  INDCPA_NTT_TAC "SH" (b + 4608) 3 "S0" "sigma" "word j" (st 84) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "S0" 768 THEN
  ARM_STEPS_TAC KP3_EXEC (85--86) THEN
  LOCAL_NTT_TAC [`read X0 s`; `E0:num->int16`; `pc:num`; `read X30 s`] 87 THEN
  ARM_STEPS_TAC KP3_EXEC (88--89) THEN
  LOCAL_NTT_TAC [`read X0 s`; `\i. (E0:num->int16)(256 + i)`; `pc:num`;
                 `read X30 s`] 90 THEN
  ARM_STEPS_TAC KP3_EXEC (91--95) THEN
  LOCAL_NTT_TAC [`read X0 s`; `\i. (E0:num->int16)(512 + i)`; `pc:num`;
                 `read X30 s`] 96 THEN
  POLYVEC_INLINE_JOIN_TAC 3 [] (PV_NTT_POST 3 (sp(b + 7680)) "E0" (st 96)) THEN
  INDCPA_NTT_TAC "EH" (b + 7680) 3 "E0" "sigma" "word(3 + j)" (st 96) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "E0" 768 THEN

  (*** The multiplication cache ***)

  POLYVEC_GHOST_SPLIT_TAC "SH" (b + 4608) 3 (st 96) THEN
  ARM_STEPS_TAC KP3_EXEC (97--99) THEN
  LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; `SH:num->int16`; `pc:num`;
                      `read X30 s`] 100 THEN
  ARM_STEPS_TAC KP3_EXEC (101--103) THEN
  LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; `\i. (SH:num->int16)(256 + i)`;
                      `pc:num`; `read X30 s`] 104 THEN
  ARM_STEPS_TAC KP3_EXEC (105--107) THEN
  LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; `\i. (SH:num->int16)(512 + i)`;
                      `pc:num`; `read X30 s`] 108 THEN
  POLYVEC_INLINE_JOIN_TAC 3 []
   (PV_MULCACHE_POST 3 (sp(b + 9216)) "SH" (st 108)) THEN
  INDCPA_MULCACHE_TAC "MC" (b + 9216) 3 "SH" (st 108) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "SH" 768 THEN

  (*** The matrix-vector product, one row per iteration ***)

  MAP_EVERY (fun r ->
    let a = (b + 1536 * r,"AM",768 * r)
    and y = (b + 4608,"SH") and t = (b + 9216,"MC") in
    ARM_STEPS_TAC KP3_EXEC ((109 + 10 * r)--(113 + 10 * r)) THEN
    INDCPA_BASEMUL3_PRE_TAC a y t (st(113 + 10 * r)) THEN
    LOCAL_BASEMUL_TAC (INDCPA_BASEMUL3_ARGS ("AM",768 * r) "SH" "MC")
      (114 + 10 * r) THEN
    INDCPA_BASEMUL3_DROP_PRE_TAC a y t THEN
    ARM_STEPS_TAC KP3_EXEC ((115 + 10 * r)--(118 + 10 * r))) [0;1;2] THEN
  KP3_AM_BOUND_TAC THEN KP3_PT_TAC b (st 138) THEN

  (*** The Montgomery form of t, in the inlined loops, three iterations of
       the outer one ***)

  POLYVEC_GHOST_SPLIT_TAC "PT" (b + 6144) 3 (st 138) THEN
  MAP_EVERY (fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th))
    KP3_CONSTANTS THEN
  ARM_STEPS_TAC KP3_EXEC (139--139) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (140--144) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (145--146) THEN
  MAP_EVERY (fun r ->
    let x = if r = 0 then `PT:num->int16` else
            subst [mk_small_numeral(256 * r),`n:num`]
             `\i. (PT:num->int16)(n + i)` in
    ARM_STEPS_TAC KP3_EXEC ((147 + 6 * r)--(148 + 6 * r)) THEN
    KP3_LEMMA_TAC "H_TOMONT"
     [`read events s`; `read X0 s`; x; `pc:num`] (149 + 6 * r) THEN
    ARM_STEPS_TAC KP3_EXEC ((150 + 6 * r)--(152 + 6 * r))) [0;1;2] THEN
  POLYVEC_INLINE_JOIN_TAC 3 [tomont_3329; o_THM]
   (PV_TOMONT_POST 3 (sp(b + 6144)) "PT" (st 164)) THEN
  INDCPA_TOMONT_TAC "PT2" (b + 6144) 768 "PT" (st 164) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "PT" 768 THEN

  (*** Adding e, in the inlined loops, three iterations of the outer one ***)

  POLYVEC_GHOST_SPLIT_TAC "PT2" (b + 6144) 3 (st 164) THEN
  POLYVEC_GHOST_SPLIT_TAC "EH" (b + 7680) 3 (st 164) THEN
  ARM_STEPS_TAC KP3_EXEC (165--165) THEN
  MAP_EVERY (fun r ->
    let f v = if r = 0 then mk_var(v,`:num->int16`) else
              subst [mk_small_numeral(256 * r),`n:num`;
                     mk_var(v,`:num->int16`),`v:num->int16`]
               `\i. (v:num->int16)(n + i)` in
    let k0 = 166 + 9 * r in
    ARM_STEPS_TAC KP3_EXEC (k0--k0) THEN
    KP3_LEMMA_TAC "H_ADD"
     [`read events s`; `read X28 s`; `read X1 s`; f "PT2"; f "EH"; `pc:num`]
     (k0 + 1) THEN
    ARM_STEPS_TAC KP3_EXEC ((k0 + 2)--(if r = 2 then k0 + 6 else k0 + 8)))
   [0;1;2] THEN
  POLYVEC_GHOST_DROP_ALL_TAC "PT2" 768 THEN
  POLYVEC_GHOST_DROP_ALL_TAC "EH" 768 THEN

  (*** The reductions of t and s ***)

  ARM_STEPS_TAC KP3_EXEC (191--193) THEN
  LOCAL_REDUCE_TAC
   [`read X0 s`; `\i. word_add ((PT2:num->int16) i) ((EH:num->int16) i)`;
    `pc:num`; `read X30 s`] 194 THEN
  ARM_STEPS_TAC KP3_EXEC (195--197) THEN
  LOCAL_REDUCE_TAC
   [`read X0 s`;
    `\i. word_add ((PT2:num->int16)(256 + i)) ((EH:num->int16)(256 + i))`;
    `pc:num`; `read X30 s`] 198 THEN
  ARM_STEPS_TAC KP3_EXEC (199--200) THEN
  LOCAL_REDUCE_TAC
   [`read X0 s`;
    `\i. word_add ((PT2:num->int16)(512 + i)) ((EH:num->int16)(512 + i))`;
    `pc:num`; `read X30 s`] 201 THEN
  POLYVEC_INLINE_JOIN_TAC 3 []
   (PV_REDUCE_POST 3 (sp(b + 6144))
     "\\i. word_add ((PT2:num->int16) i) ((EH:num->int16) i)" (st 201)) THEN
  INDCPA_REDUCE_TAC "TR" (b + 6144) 768
    "word_add ((PT2:num->int16) i) ((EH:num->int16) i)" (st 201) THEN
  POLYVEC_GHOST_SPLIT_TAC "SH" (b + 4608) 3 (st 201) THEN
  ARM_STEPS_TAC KP3_EXEC (202--204) THEN
  LOCAL_REDUCE_TAC [`read X0 s`; `SH:num->int16`; `pc:num`; `read X30 s`]
    205 THEN
  ARM_STEPS_TAC KP3_EXEC (206--208) THEN
  LOCAL_REDUCE_TAC [`read X0 s`; `\i. (SH:num->int16)(256 + i)`; `pc:num`;
                    `read X30 s`] 209 THEN
  ARM_STEPS_TAC KP3_EXEC (210--211) THEN
  LOCAL_REDUCE_TAC [`read X0 s`; `\i. (SH:num->int16)(512 + i)`; `pc:num`;
                    `read X30 s`] 212 THEN
  POLYVEC_INLINE_JOIN_TAC 3 [] (PV_REDUCE_POST 3 (sp(b + 4608)) "SH" (st 212))
  THEN
  INDCPA_REDUCE_TAC "SR" (b + 4608) 768 "(SH:num->int16) i" (st 212) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "SH" 768 THEN

  (*** The encodings of the keys ***)

  INDCPA_TOBYTES_PRE_TAC "SR" (b + 4608) 768 (st 212) THEN
  POLYVEC_INLINE_SPLIT_TAC POLYVEC_TOBYTES_SPLIT_GEN (INDCPA_SP(b + 4608)) 3
  THEN INLINE_SP_NORMALIZE_TAC THEN
  MAP_EVERY (fun (j,k0,k1) ->
    ARM_STEPS_TAC KP3_EXEC (k0--k1) THEN
    LOCAL_TOBYTES_TAC
     [`read X0 s`; `read X1 s`;
      subst [mk_small_numeral(256 * j),`n:num`]
       `SUB_LIST(n,256) (list_of_seq (SR:num->int16) 768)`; `pc:num`;
      `read X30 s`] (k1 + 1)) [0,213,216; 1,218,220; 2,222,224] THEN
  POLYVEC_TOBYTES_JOIN_TAC 3 `sk:int64` `list_of_seq (SR:num->int16) 768`
    `s225:armstate` THEN
  INDCPA_TOBYTES_POST_TAC "SR" 768 `\i. ival((SH:num->int16) i)` THEN
  INDCPA_TOBYTES_PRE_TAC "TR" (b + 6144) 768 (st 225) THEN
  POLYVEC_INLINE_SPLIT_TAC POLYVEC_TOBYTES_SPLIT_GEN (INDCPA_SP(b + 6144)) 3
  THEN INLINE_SP_NORMALIZE_TAC THEN
  MAP_EVERY (fun (j,k0,k1) ->
    ARM_STEPS_TAC KP3_EXEC (k0--k1) THEN
    LOCAL_TOBYTES_TAC
     [`read X0 s`; `read X1 s`;
      subst [mk_small_numeral(256 * j),`n:num`]
       `SUB_LIST(n,256) (list_of_seq (TR:num->int16) 768)`; `pc:num`;
      `read X30 s`] (k1 + 1)) [0,226,229; 1,231,233; 2,235,238] THEN
  POLYVEC_TOBYTES_JOIN_TAC 3 `pk:int64` `list_of_seq (TR:num->int16) 768`
    `s239:armstate` THEN
  INDCPA_TOBYTES_POST_TAC "TR" 768
    `\i. ival(word_add ((PT2:num->int16) i) ((EH:num->int16) i))` THEN
  KP3_HALVES_TAC (INDCPA_SP(b + 9984)) "rho" THEN
  ARM_STEPS_TAC KP3_EXEC (240--244) THEN KP3_RHO_TAC (st 244) THEN

  (*** Zeroing the buffers, the stack guard, the return ***)

  INDCPA_MEMSET_LABEL_TAC THEN
  INDCPA_MEMSETS_TAC KP3_EXEC
   [245,245; 251,254; 260,263; 269,273; 279,282] THEN
  ARM_STEPS_TAC KP3_EXEC (288--294) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (295--310) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KP3_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!pk sk coins (d:byte list) guard mf mc ea el ev pc stackpointer
    returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH d = 32 /\
        (!i j. i < 3 /\ j < 3
               ==> mlkem_samplentt_terminates
                    (APPEND (FST(mlkem_g(APPEND d [word 3])))
                            [word j; word i])) /\
        PAIRWISE nonoverlapping
         [(pk,1184); (sk,1152); (word_sub stackpointer (word 14688),14688)] /\
        ALLPAIRS nonoverlapping
         [(pk,1184); (sk,1152); (word_sub stackpointer (word 14688),14688)]
         [(coins,32); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlkem768_indcpa_keypair_derand) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [pk; sk; coins] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(coins,32)) s = num_of_bytelist d)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(pk,1184)) s =
                  num_of_bytelist(FST(kpke_keygen mlkem768 d)) /\
                  read (memory :> bytes(sk,1152)) s =
                  num_of_bytelist(SND(kpke_keygen mlkem768 d)) /\
                  C_RETURN s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(pk,1184); memory :> bytes(sk,1152);
                memory :> bytes(word_sub stackpointer (word 14688),14688)])`,
  KP3_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [KP3_CASE_TAC 4576; KP3_CASE_TAC 4560]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset (for mlkem768_gen_matrix) and the safety contract for memcpy, as   *)
(* for gcc 12 -O2. The events depend only on the addresses and on rho. The   *)
(* inner loops use the same lemmas as the correctness proof, with the        *)
(* contents of the memory as the data, and the vectors of constants of the   *)
(* tomont loop are read-only objects.                                        *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let KP_SAFE_TEMPLATE =
 `\(pk:int64) (sk:int64) (coins:int64) (guard:int64) (mf:int64) (mc:int64)
   (pc:num) (stackpointer:int64) (returnaddress:int64) (rho:byte list).
   if aligned 32 stackpointer
   then f_ev_a pk sk coins guard mf mc pc stackpointer returnaddress rho
   else f_ev_u pk sk coins guard mf mc pc stackpointer returnaddress rho
   :(uarch_event)list`;;

let KP_SAFE_ALLOWED =
  [`pc:num`; `pk:int64`; `sk:int64`; `coins:int64`; `guard:int64`;
   `mf:int64`; `mc:int64`; `stackpointer:int64`; `returnaddress:int64`;
   `rho:byte list`];;

let KP3_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th)
    then ASSUME_CALLEE_SAFETY_TAILED_TAC
          (INDCPA_GEN_MATRIX_SAFE_SPEC
            (MATCH_MP
              MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
              th) `word 0:int64`) "H_GM" THEN
         ASSUME_TAC(CONJUNCT2(MATCH_MP MEMSET_FULL_CONTRACT th))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memset_safety_contract mf ea el ev`) (concl th)
    then ASSUME_CALLEE_SAFETY_TAILED_TAC
          (REWRITE_RULE[memset_safety_contract] th) "H_MEMSET"
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th1 ->
    if can (term_match [] `memset_safety_contract mf ea el ev`) (concl th1)
    then FIRST_X_ASSUM(fun th2 ->
      let gth = MATCH_MP
        MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
        (CONJ th1 th2) in
      ASSUME_CALLEE_SAFETY_TAILED_TAC (INDCPA_GETNOISE_NULL_SAFE gth)
       "H_GETNOISE")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHA3_512_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL "H_SHA3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_BASEMUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC KP3_TOMONT "H_TOMONT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC KP3_ADD "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_TOBYTES" THEN
  CONCRETIZE_F_EVENTS_TAC KP_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 14688):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28) THEN
  UNDISCH_TAC
   `!i j. i < 3 /\ j < 3
          ==> mlkem_samplentt_terminates
               (APPEND (FST(mlkem_g(APPEND d [word 3])))
                       [word j; word i])` THEN
  ABBREV_TAC `rho = FST(mlkem_g(APPEND d [word 3]))` THEN
  ABBREV_TAC `sigma = SND(mlkem_g(APPEND d [word 3]))` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`3`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN `LENGTH(rho:byte list) = 32 /\ LENGTH(sigma:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rho"; "sigma"] THEN REWRITE_TAC[LENGTH_MLKEM_G];
    ALL_TAC];;

let KP3_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,KP3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KP_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

(*** The contents of a polynomial at the address in a register, as the data
     of the lemmas for the loops ***)

let KP3_CONTENTS r =
  let a = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                          r),`s:armstate`) in
  vsubst [a,`a:int64`]
   `\i. read(memory :> bytes16(word_add a (word(2 * i)))) (s:armstate)`;;

let KP3_SAFE_CASE_TAC b =
  let e = `e:(uarch_event)list` in
  let x n = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            mk_const("X"^string_of_int n,[])),`s:armstate`) in
  let rest = [`pc:num`; `read SP s`; `read X30 s`] in
  let rest0 = [`pc:num`; `read X30 s`] in
  let call = KP3_SAFE_CALL_TAC in
  ENSURES_INIT_TAC "s0" THEN
  KP3_HALVES_TAC `coins:int64` "d" THEN
  ARM_STEPS_TAC KP3_EXEC (1--9) THEN KP3_BUFFER_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (10--27) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (28--35) THEN
  KP3_INPUT_TAC b `s35:armstate` THEN INLINE_GOT_TAC THEN
  ARM_STEPS_TAC KP3_EXEC [36] THEN
  call "H_SHA3"
   ([e; x 0; x 1; `APPEND d [word 3]:byte list`; `33`; `guard:int64`] @
    rest) 37 THEN
  KP3_G_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (38--41) THEN
  call "H_GM" ([e; x 0; x 1; `rho:byte list`; `k:num`; `guard:int64`] @ rest)
   42 THEN
  ARM_STEPS_TAC KP3_EXEC (43--54) THEN INLINE_GOT_TAC THEN
  call "H_GETNOISE" ([e; x 0; x 1; x 2; x 4; `guard:int64`] @ rest) 55 THEN
  ARM_STEPS_TAC KP3_EXEC (56--70) THEN INLINE_GOT_TAC THEN
  call "H_GETNOISE" ([e; x 0; x 1; x 2; x 4; `guard:int64`] @ rest) 71 THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC KP3_EXEC (k0--k1) THEN
    call "H_NTT" ([e; x 0] @ rest0) (k1 + 1))
   [72,73; 75,77; 79,83; 85,86; 88,89; 91,95] THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC KP3_EXEC (k0--k1) THEN
    call "H_MULCACHE" ([e; x 0; x 1] @ rest0) (k1 + 1))
   [97,99; 101,103; 105,107] THEN
  MAP_EVERY (fun r ->
    ARM_STEPS_TAC KP3_EXEC ((109 + 10 * r)--(113 + 10 * r)) THEN
    call "H_BASEMUL" ([e; x 1; x 2; x 3; x 0] @ rest0) (114 + 10 * r) THEN
    ARM_STEPS_TAC KP3_EXEC ((115 + 10 * r)--(118 + 10 * r))) [0;1;2] THEN
  MAP_EVERY (fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th))
    KP3_CONSTANTS THEN
  ARM_STEPS_TAC KP3_EXEC (139--139) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (140--144) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (145--146) THEN
  MAP_EVERY (fun r ->
    ARM_STEPS_TAC KP3_EXEC ((147 + 6 * r)--(148 + 6 * r)) THEN
    call "H_TOMONT" [e; x 0; KP3_CONTENTS `X0`; `pc:num`] (149 + 6 * r) THEN
    ARM_STEPS_TAC KP3_EXEC ((150 + 6 * r)--(152 + 6 * r))) [0;1;2] THEN
  ARM_STEPS_TAC KP3_EXEC (165--165) THEN
  MAP_EVERY (fun r ->
    let k0 = 166 + 9 * r in
    ARM_STEPS_TAC KP3_EXEC (k0--k0) THEN
    call "H_ADD"
     [e; x 28; x 1; KP3_CONTENTS `X28`; KP3_CONTENTS `X1`; `pc:num`]
     (k0 + 1) THEN
    ARM_STEPS_TAC KP3_EXEC ((k0 + 2)--(if r = 2 then k0 + 6 else k0 + 8)))
   [0;1;2] THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC KP3_EXEC (k0--k1) THEN
    call "H_REDUCE" ([e; x 0] @ rest0) (k1 + 1))
   [191,193; 195,197; 199,200; 202,204; 206,208; 210,211] THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC KP3_EXEC (k0--k1) THEN
    call "H_TOBYTES" ([e; x 0; x 1] @ rest0) (k1 + 1))
   [213,216; 218,220; 222,224; 226,229; 231,233; 235,238] THEN
  KP3_HALVES_TAC (INDCPA_SP(b + 9984)) "rho" THEN
  ARM_STEPS_TAC KP3_EXEC (240--244) THEN KP3_RHO_TAC "s244" THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC KP3_EXEC (k0--k) THEN LIBC_PLT_TAC KP3_EXEC k THEN
    LIBC_SAFE_CALL_TAC "H_MEMSET" KP3_EXEC
     [e; x 0; x 1; x 2; `read X30 s`] (ref KP_SAFE_ALLOWED) (k + 5))
   [245,245; 251,254; 260,263; 269,273; 279,282] THEN
  ARM_STEPS_TAC KP3_EXEC (288--294) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (295--310) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MEMACCESS_DROP_ZERO_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  prove
 (`!mf mc ea el ev.
   memset_full_contract mf ea el ev /\ memcpy_safety_contract mc ea el ev
   ==> exists f_events.
        forall e pk sk coins (d:byte list) guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH d = 32 /\
          (!i j. i < 3 /\ j < 3
                 ==> mlkem_samplentt_terminates
                      (APPEND (FST(mlkem_g(APPEND d [word 3])))
                              [word j; word i])) /\
          PAIRWISE nonoverlapping
           [(pk,1184); (sk,1152);
            (word_sub stackpointer (word 14688),14688)] /\
          ALLPAIRS nonoverlapping
           [(pk,1184); (sk,1152);
            (word_sub stackpointer (word 14688),14688)]
           [(coins,32); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlkem768_indcpa_keypair_derand) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk; coins] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(coins,32)) s = num_of_bytelist d /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    read (memory :> bytes(word_add pk (word 1152),32)) s =
                    num_of_bytelist(FST(mlkem_g(APPEND d [word 3]))) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk coins guard mf mc pc
                              (word_sub stackpointer (word 14688))
                              returnaddress
                              (FST(mlkem_g(APPEND d [word 3]))) /\
                       memaccess_inbounds e2
                        [coins,32; pk,1184; sk,1152;
                         word_sub stackpointer (word 14688),14688;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + mlkem_poly_cbd2_consts),64;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlkem768_indcpa_keypair_derand_const2),16;
                         word(pc + mlk_poly_invntt_tomont_c_const2),16]
                        [pk,1184; sk,1152;
                         word_sub stackpointer (word 14688),14688]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1184); memory :> bytes(sk,1152);
                  memory :> bytes(word_sub stackpointer (word 14688),14688)])`,
  KP3_SAFE_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [KP3_SAFE_CASE_TAC 4576; KP3_SAFE_CASE_TAC 4560]);;
