(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The key generation of K-PKE for ML-KEM-512 (FIPS 203 Algorithm 13). This  *)
(* is the code for mlkem512_indcpa_keypair_derand from mlkem-native's        *)
(* portable C implementation compiled by gcc 12 with -O2 as one translation  *)
(* unit (see mlkem_native/README.md). It hashes the 32-byte seed d followed  *)
(* by the byte 2 with SHA3-512 into the seeds rho and sigma, generates the   *)
(* matrix in NTT form from rho, samples the secret s and the error e from    *)
(* sigma (with eta = 3) and transforms them, computes t = A s + e in the NTT *)
(* domain, and writes the encoding of t followed by rho as the public key    *)
(* and the encoding of s as the secret key, zeroing its buffers. It is       *)
(* verified in the whole image (see libmlkem.ml), using the theorems for     *)
(* mlkem_sha3_512, mlkem512_gen_matrix, mlkem_shake256x4, mlkem_poly_cbd3,   *)
(* mlk_poly_ntt_c, mlk_poly_mulcache_compute_c,                              *)
(* mlk_polyvec_basemul_acc_montgomery_cached_c512, mlk_poly_reduce_c and     *)
(* mlk_poly_tobytes_c in the image, and the contracts for memset and         *)
(* memcpy.                                                                   *)
(*                                                                           *)
(* Differences from the gcc 12 -O2 proof. gcc has inlined                    *)
(* mlkem512_poly_getnoise_eta1_4x and all the polyvec functions:             *)
(*                                                                           *)
(*  - getnoise: the setup of its registers is interleaved with the prologue, *)
(*    and its body (from in_poly_getnoise_eta1_4x_part5, after the matrix,   *)
(*    to in_poly_getnoise_eta1_4x_end) copies sigma and the nonces into four *)
(*    inputs, calls mlkem_shake256x4 and mlkem_poly_cbd3 four times, and     *)
(*    zeroes its buffers. It is simulated in place, with the composition of  *)
(*    the proof of the gcc 12 -O2 getnoise, and its postcondition is then    *)
(*    restated, so that the rest of the proof is that of the gcc 12 -O2      *)
(*    code;                                                                  *)
(*  - polyvec_ntt, polyvec_mulcache_compute, polyvec_reduce and              *)
(*    polyvec_tobytes: the kernel is called for each polynomial, and the     *)
(*    postcondition of the polyvec function is proved from those of the      *)
(*    calls (mlkem_native/indcpa_inline.ml);                                 *)
(*  - polyvec_tomont and polyvec_add: the vector code of poly_tomont and     *)
(*    poly_add is inlined as four loops, two for each, which are proved as   *)
(*    lemmas from their head to their exit (with the events, so that the     *)
(*    same lemmas serve for constant time and memory safety). The vectors of *)
(*    constants of poly_tomont are loaded before each loop, interleaved with *)
(*    the setup of polyvec_basemul and polyvec_add.                          *)
(*                                                                           *)
(* The buffers are at the same offsets from each other as with gcc 12 -O2;   *)
(* the frame is the 5920 bytes of the function and the 3616 of               *)
(* mlkem512_gen_matrix below them, 9536 in all.                              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/sha3_512.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/gen_matrix_k2.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/shake256x4.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_cbd3.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_ntt.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_mulcache_compute.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/basemul_k2.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_reduce.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_tobytes.ml";;
needs "arm/proofs/mlkem_native/indcpa_inline.ml";;
needs "arm/proofs/mlkem_native/inline_loops.ml";;

(*** The code in the image is listed at the end of layout.ml, with the
     labels of the inlined calls. ***)

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K2_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "plt_memset"; layout_range "mlkem512_indcpa_keypair_derand"];;

let KP2_EXEC = MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K2_GCC12_O2_MONO_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The key generation in FIPS 203 in terms of the coefficients computed by   *)
(* the code, as for gcc 12 -O2.                                              *)
(* ------------------------------------------------------------------------- *)

let KPKE_KEYGEN_COEFF_EVEN_K2 = prove
 (`!(A:num->num->int) (Y:num->num->int) (YT:num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 2 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329) /\
                    (YT j == Y j (2 * p + 1) *
                             &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (t == &169 * ((A 1 (2 * p + 1) * YT 1 + A 1 (2 * p) * Y 1 (2 * p)) +
                   (A 0 (2 * p + 1) * YT 0 + A 0 (2 * p) * Y 0 (2 * p))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 2}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p)))
          eh`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_2;
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

let KPKE_KEYGEN_COEFF_ODD_K2 = prove
 (`!(A:num->num->int) (Y:num->num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 2 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329)) /\
     (t == &169 *
           ((A 1 (2 * p + 1) * Y 1 (2 * p) + A 1 (2 * p) * Y 1 (2 * p + 1)) +
            (A 0 (2 * p + 1) * Y 0 (2 * p) + A 0 (2 * p) * Y 0 (2 * p + 1))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 2}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p + 1)))
          eh`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_2;
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

let KPKE_KEYGEN_K2_RESULT = prove
 (`!d rho sigma (sh:num->int16) (eh:num->int16) (mc:num->int16)
    (pt:num->int16) (pt2:num->int16) (tr:num->int16) (sr:num->int16).
     mlkem_g(APPEND d [word 2]) = rho,sigma /\
     (!i j n. i < 2 /\ j < 2 /\ n < 256
              ==> mlkem_sample_ntt (APPEND rho [word j; word i]) n < &3329) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(sh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 sigma (word j))) i)
                (mod &3329) /\
                abs(ival(sh(256 * j + i))) <= &23594) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(eh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 sigma (word(2 + j)))) i)
                (mod &3329) /\
                abs(ival(eh(256 * j + i))) <= &23594) /\
     (!j p. j < 2 /\ p < 128
            ==> (ival(mc(128 * j + p)) ==
                 ival(sh(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!r p. r < 2 /\ p < 128
            ==> (ival(pt(256 * r + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(mc(128 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(mc p) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p))))) (mod &3329) /\
                (ival(pt(256 * r + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(sh(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(sh(2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p + 1))))) (mod &3329)) /\
     (!i. i < 512 ==> (ival(pt2 i) == &65536 * ival(pt i)) (mod &3329) /\
                      abs(ival(pt2 i)) <= &3328) /\
     (!i. i < 512 ==> ival(tr i) = ival(word_add (pt2 i) (eh i)) rem &3329) /\
     (!i. i < 512 ==> ival(sr i) = ival(sh i) rem &3329)
     ==> num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq tr 512)) +
         2 EXP (8 * 768) * num_of_bytelist rho =
         num_of_bytelist(FST(kpke_keygen mlkem512 d)) /\
         num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq sr 512)) =
         num_of_bytelist(SND(kpke_keygen mlkem512 d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem512] THEN
  MP_TAC(SPECL [`2`; `3`; `2`; `10`; `4`; `d:byte list`] KPKE_KEYGEN_FIPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; MLKEM_ENCODE_LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `256 * 2 = 512`;
              ARITH_RULE `(12 * 512) DIV 8 = 768`] THEN
  W(fun (_,w) ->
    let encs = find_terms (fun t -> match strip_comb t with
       (Const("mlkem_encode",_),[_;_;_]) -> true | _ -> false) w in
    MAP_EVERY (fun enc ->
      MP_TAC(PART_MATCH (lhand o rand) MLKEM_ENCODE_12_LIST
              (mk_comb(`num_of_bytelist`,enc)))) encs) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ARITH_RULE `EVEN 512`; MLKEM_NTT_CBD_BOUNDS] THEN
  SIMP_TAC[GSYM IN_MLKEM_ZQ; RING_ADD; RING_SUM; MLKEM_NTT_CBD_IN_ZQ] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC;
    AP_TERM_TAC THEN AP_TERM_TAC] THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM IWORD_IVAL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[IWORD_IVAL] THEN
  MP_TAC(SPECL [`256`; `2`; `i:num`] EXISTS_DIV_MOD_LT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `256 * 2 = 512`] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `n:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[DIV_MOD_ADD_LT] THENL
   [ALL_TAC;
    TRANS_TAC EQ_TRANS
     `(mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 sigma (word r))) n) rem &3329` THEN
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
      `\j. mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 sigma (word j)))`;
      `ival((pt:num->int16)(256 * r + 2 * p))`;
      `ival((pt2:num->int16)(256 * r + 2 * p))`;
      `ival((eh:num->int16)(256 * r + 2 * p))`;
      `mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 sigma (word(2 + r)))) (2 * p)`;
      `p:num`] KPKE_KEYGEN_COEFF_EVEN_K2);
    MP_TAC(SPECL
     [`\j. mlkem_sample_ntt (APPEND rho [word j; word r])`;
      `\j n. ival((sh:num->int16)(256 * j + n))`;
      `\j. mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 sigma (word j)))`;
      `ival((pt:num->int16)(256 * r + 2 * p + 1))`;
      `ival((pt2:num->int16)(256 * r + 2 * p + 1))`;
      `ival((eh:num->int16)(256 * r + 2 * p + 1))`;
      `mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 sigma (word(2 + r))))
                 (2 * p + 1)`;
      `p:num`] KPKE_KEYGEN_COEFF_ODD_K2)] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16. They are at the same offsets from each other as with gcc 12 -O2:   *)
(* 0 (the matrix), 2048 (s), 3072 (t), 4096 (e), 5120 (the multiplication    *)
(* cache), 5632 (rho and sigma) and 5696 (the input of SHA3-512). The four   *)
(* outputs of SHAKE256 for the noise are in the buffer of t, 192 bytes each, *)
(* and its four inputs in that of the cache, 64 bytes apart.                 *)
(* ------------------------------------------------------------------------- *)

let KP2_ALIGNED_16_32 = prove
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

let KP2_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 3791)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 3776 else 3760))`,
  REWRITE_TAC[KP2_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let KP2_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KP2_BUFFER_ADDRESS))
    else NO_TAC);;

(*** The inputs of SHA3-512 and SHAKE256: a seed of 32 bytes, stored as two
     128-bit words, and a byte (k for SHA3-512, the nonces for the noise) ***)

let KP2_SEED_INPUT_TAC a sd c s =
  MP_TAC(SPECL [a; sd; mk_small_numeral c; s] INLINE_SEED_INPUT) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV;
    STRIP_TAC];;

let KP2_INPUT_TAC b s = KP2_SEED_INPUT_TAC (INDCPA_SP(b + 5696))
  `d:byte list` 2 s;;

let KP2_G_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
             `read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 c)`)
           (concl th)
    then ASSUME_TAC th THEN
         MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                 (REWRITE_RULE
                   [ASSUME `FST(mlkem_g(APPEND d [word 2])) = rho`;
                    ASSUME `SND(mlkem_g(APPEND d [word 2])) = sigma`]
                   (MATCH_MP MLKEM_G_BYTES th))) THEN
         CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC
    else NO_TAC);;

(*** rho and sigma as two 128-bit words each ***)

let KP2_HALVES_TAC off v =
  FIRST_ASSUM(MP_TAC o MATCH_MP INLINE_BYTES128_HALVES o check (fun th ->
    can (term_match [] (subst [INDCPA_SP off,`a:int64`]
      (parse_term(Printf.sprintf
        "read (memory :> bytes(a,32)) s = num_of_bytelist %s" v))))
      (concl th))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC;;

let KP2_RHO_TAC s =
  MP_TAC(SPECL [`word_add pk (word 768):int64`; `num_of_bytelist rho`;
                mk_var(s,`:armstate`)] INLINE_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `rho:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

(*** The postcondition of mlkem512_poly_getnoise_eta1_4x in the gcc 12 -O2
     build, for the four outputs at off, from those of mlkem_poly_cbd3 on
     the outputs of SHAKE256 for the nonces 0, 1, 2 and 3 ***)

let KP2_NOISE_LET_TAC s =
  MAP_EVERY (fun (off,k) ->
    let tm = parse_term(Printf.sprintf
     "let n = num_of_bytelist
              (list_of_seq (shake256 (APPEND sigma [word %d:byte])) 192) in
      !i. i < 256
          ==> read(memory :> bytes16(word_add stackpointer
                                      (word(%d + 2 * i)))) (%s:armstate) =
              iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                      (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                      (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                    &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                      (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                      (n DIV 2 EXP (6 * i + 5)) MOD 2))" k off s) in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      FIRST_ASSUM MATCH_ACCEPT_TAC;
      ALL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The inlined loops of poly_tomont and poly_add, as lemmas from their head  *)
(* to their exit, with the events (mlkem_native/inline_loops.ml). The two    *)
(* tomont loops are the same code with the end of the polynomial in X25 and  *)
(* in X0; the first add loop increments pointers, the second an offset.      *)
(* ------------------------------------------------------------------------- *)

let KP2_TOMONT1 = INLINE_TOMONT_LOOP "mlkem_native_libmlkem_gcc12_O2_mono_mc"
  KP2_EXEC "mlkem512_indcpa_keypair_derand_loop1"
  "mlkem512_indcpa_keypair_derand_loop1_exit" "X25";;

let KP2_TOMONT2 = INLINE_TOMONT_LOOP "mlkem_native_libmlkem_gcc12_O2_mono_mc"
  KP2_EXEC "mlkem512_indcpa_keypair_derand_loop2"
  "mlkem512_indcpa_keypair_derand_loop2_exit" "X0";;

let KP2_ADD3 = INLINE_PTR_LOOP "mlkem_native_libmlkem_gcc12_O2_mono_mc"
  KP2_EXEC "add" "mlkem512_indcpa_keypair_derand_loop3"
  "mlkem512_indcpa_keypair_derand_loop3_exit" "X3" "X0" "X25";;

let KP2_ADD4 = INLINE_IDX_ADD_LOOP "mlkem_native_libmlkem_gcc12_O2_mono_mc"
  KP2_EXEC "mlkem512_indcpa_keypair_derand_loop4"
  "mlkem512_indcpa_keypair_derand_loop4_exit" "X26" "X27" "X8" "X2" "X0";;

(* ------------------------------------------------------------------------- *)
(* The callees, and the lemmas for the inlined loops, as for subroutines.    *)
(* The matrix is generated without transposition, so the theorem for        *)
(* mlkem512_gen_matrix is specialized to that case.                          *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SHA3_512_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,KP2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_SHA3_512_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GEN_MATRIX_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,KP2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    INDCPA_GEN_MATRIX_SPEC
      MLKEM_NATIVE_GEN_MATRIX_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT
      `word 0:int64`);;

let LOCAL_SHAKE256X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,KP2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_CBD3_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,KP2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_POLY_CBD3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_NTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,KP2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_MULCACHE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,KP2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_BASEMUL_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,KP2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,KP2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_TOBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,KP2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let KP2_LEMMA_TAC name ilist n =
  USE_THEN name (fun th ->
    ARM_SUBROUTINE_SIM_TAC
     (mlkem_native_libmlkem_gcc12_O2_mono_mc,KP2_EXEC,
      0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,th) ilist n);;

(*** The vectors of constants of the tomont loops, from the image ***)

let KP2_CONSTANTS =
  map (fun d -> MLKEM_NATIVE_IMAGE_CONST_RULE d 128)
   [layout "mlkem512_indcpa_keypair_derand_const2";
    layout "mlk_poly_invntt_tomont_c_const2"];;

(* ------------------------------------------------------------------------- *)
(* The facts about the stages of the computation other than those given by   *)
(* the tactics in mlkem_native_indcpa.ml, as for gcc 12 -O2.                 *)
(* ------------------------------------------------------------------------- *)

let KP2_SP n = Printf.sprintf "word_add stackpointer (word %d)" n;;

let KP2_MATRIX_TAC b s =
  let addr = parse_term(Printf.sprintf
    "word_add stackpointer (word (%d + 512 * (2 * r + j))):int64" b) in
  SUBGOAL_THEN
   `!r j n. r < 2 /\ j < 2 /\ n < 256
            ==> &0 <= mlkem_sample_ntt (APPEND rho [word j; word r]) n /\
                mlkem_sample_ntt (APPEND rho [word j; word r]) n < &3329`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC MLKEM_SAMPLE_NTT_REJ_BOUND THEN
    EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r j n. r < 2 /\ j < 2 /\ n < 256
            ==> ival((AM:num->int16)(512 * r + 256 * j + n)) =
                mlkem_sample_ntt (APPEND rho [word j; word r]) n`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    INDCPA_GHOST_SPEC_TAC "AM" `512 * r + 256 * j + n` THEN
    MP_TAC(SPECL [addr; s; `APPEND (rho:byte list) [word j; word r]`;
                  `k:num`; `n:num`]
                 MLKEM_NATIVE_SAMPLE_COEFF) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    MATCH_MP_TAC READ16_OFFSET_EQ THEN ARITH_TAC;
    ALL_TAC];;

let KP2_AM_INST r j =
  let th = SPECL [mk_small_numeral r; mk_small_numeral j]
    (ASSUME `!r j n. r < 2 /\ j < 2 /\ n < 256
                     ==> ival((AM:num->int16)(512 * r + 256 * j + n)) =
                         mlkem_sample_ntt (APPEND rho [word j; word r]) n`) in
  CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES; ADD_ASSOC] THENC
            NUM_REDUCE_CONV) th;;

let KP2_PT_GOAL = `!r p. r < 2 /\ p < 128
            ==> (ival((PT:num->int16)(256 * r + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival((MC:num->int16)(128 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival((SH:num->int16)(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(MC p) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(SH(2 * p))))) (mod &3329) /\
                (ival(PT(256 * r + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(SH(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(SH(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(SH(2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(SH(2 * p + 1))))) (mod &3329)`;;

let KP2_AM_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 1024 ==> abs(ival((AM:num->int16) m)) <= &2 pow 12`
  (LABEL_TAC "ambound") THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`512`; `2`; `m:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `512 * 2 = 1024`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:num`; `q:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`256`; `2`; `q:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 2 = 512`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(INT_ARITH
     `&0 <= x /\ x < &3329 ==> abs(x:int) <= &2 pow 12`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC];;

let KP2_BASEMUL_DEFS =
  [basemul2_even; basemul2_odd; pmul_acc2; pmull_acc2; pmull];;

let KP2_PT_TAC b s =
  INDCPA_GHOST_TAC "PT" (b + 3072) 512 s THEN
  SUBGOAL_THEN KP2_PT_GOAL ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THENL
     (map (fun r -> INDCPA_BASEMULK_ROW_TAC 2 "PT" (b + 3072 + 512 * r)
                     "ambound" (map (KP2_AM_INST r) [0;1])
                     KP2_BASEMUL_DEFS) [0;1]);
    ALL_TAC];;

let KP2_FINAL_TAC =
  REWRITE_TAC[ARITH_RULE `800 = 768 + 32`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`d:byte list`; `rho:byte list`; `sigma:byte list`;
                `SH:num->int16`; `EH:num->int16`; `MC:num->int16`;
                `PT:num->int16`; `PT2:num->int16`; `TR:num->int16`;
                `SR:num->int16`] KPKE_KEYGEN_K2_RESULT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `FST(mlkem_g(APPEND d [word 2])) = rho`);
                  GSYM(ASSUME `SND(mlkem_g(APPEND d [word 2])) = sigma`);
                  PAIR];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    SIMP_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy (the      *)
(* latter for mlkem_shake256x4). The statement is that of gcc 12 -O2 with    *)
(* the frame of this code. The proof is by cases on whether the stack        *)
(* pointer is a multiple of 32, which gives the address b of the buffers.    *)
(* ------------------------------------------------------------------------- *)

let KP2_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `sk:int64`; `coins:int64`; `d:byte list`; `guard:int64`;
    `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 9536 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 9536):int64)` THEN
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
   `!i j. i < 2 /\ j < 2
          ==> mlkem_samplentt_terminates
               (APPEND (FST(mlkem_g(APPEND d [word 2])))
                       [word j; word i])` THEN
  ABBREV_TAC `rho = FST(mlkem_g(APPEND d [word 2]))` THEN
  ABBREV_TAC `sigma = SND(mlkem_g(APPEND d [word 2]))` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN `LENGTH(rho:byte list) = 32 /\ LENGTH(sigma:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rho"; "sigma"] THEN REWRITE_TAC[LENGTH_MLKEM_G];
    ALL_TAC] THEN
  X_CHOOSE_THEN `ft1:int64->num->(uarch_event)list`
    (LABEL_TAC "H_TOMONT1") KP2_TOMONT1 THEN
  X_CHOOSE_THEN `ft2:int64->num->(uarch_event)list`
    (LABEL_TAC "H_TOMONT2") KP2_TOMONT2 THEN
  X_CHOOSE_THEN `fa3:int64->int64->num->(uarch_event)list`
    (LABEL_TAC "H_ADD3") KP2_ADD3 THEN
  X_CHOOSE_THEN `fa4:int64->int64->num->(uarch_event)list`
    (LABEL_TAC "H_ADD4") KP2_ADD4;;

let KP2_NOISE_N k = parse_term(Printf.sprintf
  "num_of_bytelist(list_of_seq (shake256 (APPEND sigma [word %d:byte])) 192)"
  k);;

let KP2_CASE_TAC b =
  let st n = "s"^string_of_int n in
  let sp n = KP2_SP n in
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INLINE_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(coins,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN

  (*** The setup (with that of getnoise), SHA3-512 of d and 2 ***)

  ARM_STEPS_TAC KP2_EXEC (1--8) THEN KP2_BUFFER_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (9--26) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (27--34) THEN
  KP2_INPUT_TAC b `s34:armstate` THEN INLINE_GOT_TAC THEN
  ARM_STEPS_TAC KP2_EXEC [35] THEN
  LOCAL_SHA3_512_TAC
   [`read X0 s`; `read X1 s`; `APPEND d [word 2]:byte list`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 36 THEN
  KP2_G_TAC THEN

  (*** The matrix ***)

  ARM_STEPS_TAC KP2_EXEC (37--40) THEN
  LOCAL_GEN_MATRIX_TAC
   [`read X0 s`; `read X1 s`; `rho:byte list`; `k:num`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 41 THEN
  INDCPA_GHOST_TAC "AM" b 1024 (st 41) THEN
  KP2_MATRIX_TAC b `s41:armstate` THEN

  (*** The inlined getnoise: the inputs (sigma and the nonces 0 to 3),
       SHAKE256, mlkem_poly_cbd3 for s and e, zeroing the buffers ***)

  KP2_HALVES_TAC (b + 5664) "sigma" THEN
  ARM_STEPS_TAC KP2_EXEC (42--66) THEN
  MAP_EVERY (fun k ->
    KP2_SEED_INPUT_TAC (INDCPA_SP(b + 5120 + 64 * k)) `sigma:byte list` k
      `s66:armstate`) [0;1;2;3] THEN
  INLINE_GOT_TAC THEN
  ARM_STEPS_TAC KP2_EXEC [67] THEN
  LOCAL_SHAKE256X4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `192`;
    `read X5 s`; `read X6 s`; `read X7 s`; INDCPA_SP(b + 5312); `33`;
    `APPEND sigma [word 0:byte]`; `APPEND sigma [word 1:byte]`;
    `APPEND sigma [word 2:byte]`; `APPEND sigma [word 3:byte]`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 68 THEN
  MAP_EVERY (fun (k,k0,k1) ->
    ARM_STEPS_TAC KP2_EXEC (k0--k1) THEN
    LOCAL_CBD3_TAC [`read X0 s`; `read X1 s`; KP2_NOISE_N k; `pc:num`;
                    `read X30 s`] (k1 + 1))
   [0,69,71; 1,73,76; 2,78,81; 3,83,86] THEN
  INDCPA_MEMSET_LABEL_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (88--91) THEN LIBC_PLT_TAC KP2_EXEC 91 THEN
  LIBC_CALL_TAC "H_MEMSET" KP2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 96 THEN
  INDCPA_DROP_MEMSET_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (97--105) THEN
  KP2_NOISE_LET_TAC (st 105)
   [b + 2048,0; b + 2560,1; b + 4096,2; b + 4608,3] THEN
  INDCPA_NOISE_ETA_TAC 3 "S0" (b + 2048) 2 "sigma" "word j" (st 105) THEN
  INDCPA_NOISE_ETA_TAC 3 "E0" (b + 4096) 2 "sigma" "word(2 + j)"
    (st 105) THEN
  INDCPA_DISCARD_LETS_TAC THEN

  (*** The NTTs of s and e, the multiplication cache ***)

  POLYVEC_GHOST_SPLIT_TAC "S0" (b + 2048) 2 (st 105) THEN
  POLYVEC_GHOST_SPLIT_TAC "E0" (b + 4096) 2 (st 105) THEN
  ARM_STEPS_TAC KP2_EXEC (106--108) THEN
  LOCAL_NTT_TAC [`read X0 s`; `S0:num->int16`; `pc:num`; `read X30 s`] 109 THEN
  ARM_STEPS_TAC KP2_EXEC (110--111) THEN
  LOCAL_NTT_TAC [`read X0 s`; `\i. (S0:num->int16)(256 + i)`; `pc:num`;
                 `read X30 s`] 112 THEN
  POLYVEC_INLINE_JOIN_TAC 2 [] (PV_NTT_POST 2 (sp(b + 2048)) "S0" (st 112)) THEN
  INDCPA_NTT_ETA_TAC 3 "SH" (b + 2048) 2 "S0" "sigma" "word j" (st 112) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "S0" 512 THEN
  ARM_STEPS_TAC KP2_EXEC (113--114) THEN
  LOCAL_NTT_TAC [`read X0 s`; `E0:num->int16`; `pc:num`; `read X30 s`] 115 THEN
  ARM_STEPS_TAC KP2_EXEC (116--117) THEN
  LOCAL_NTT_TAC [`read X0 s`; `\i. (E0:num->int16)(256 + i)`; `pc:num`;
                 `read X30 s`] 118 THEN
  POLYVEC_INLINE_JOIN_TAC 2 [] (PV_NTT_POST 2 (sp(b + 4096)) "E0" (st 118)) THEN
  INDCPA_NTT_ETA_TAC 3 "EH" (b + 4096) 2 "E0" "sigma" "word(2 + j)"
    (st 118) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "E0" 512 THEN
  POLYVEC_GHOST_SPLIT_TAC "SH" (b + 2048) 2 (st 118) THEN
  ARM_STEPS_TAC KP2_EXEC (119--121) THEN
  LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; `SH:num->int16`; `pc:num`;
                      `read X30 s`] 122 THEN
  ARM_STEPS_TAC KP2_EXEC (123--126) THEN
  LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; `\i. (SH:num->int16)(256 + i)`;
                      `pc:num`; `read X30 s`] 127 THEN
  POLYVEC_INLINE_JOIN_TAC 2 []
   (PV_MULCACHE_POST 2 (sp(b + 5120)) "SH" (st 127)) THEN
  INDCPA_MULCACHE_TAC "MC" (b + 5120) 2 "SH" (st 127) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "SH" 512 THEN

  (*** The matrix-vector product, one row per call ***)

  MAP_EVERY (fun (r,k0,k1) ->
    let a = (b + 1024 * r,"AM",512 * r)
    and y = (b + 2048,"SH") and t = (b + 5120,"MC") in
    ARM_STEPS_TAC KP2_EXEC (k0--k1) THEN
    INDCPA_BASEMULK_PRE_TAC 2 a y t (st k1) THEN
    LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 2 ("AM",512 * r) "SH" "MC")
      (k1 + 1) THEN
    INDCPA_BASEMULK_DROP_PRE_TAC 2 a y t) [0,128,132; 1,134,138] THEN
  KP2_AM_BOUND_TAC THEN KP2_PT_TAC b (st 139) THEN

  (*** The Montgomery form of t, in the two inlined loops ***)

  POLYVEC_GHOST_SPLIT_TAC "PT" (b + 3072) 2 (st 139) THEN
  MAP_EVERY (fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th))
    KP2_CONSTANTS THEN
  ARM_STEPS_TAC KP2_EXEC (140--140) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (141--144) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (145--146) THEN
  KP2_LEMMA_TAC "H_TOMONT1"
   [`read events s`; `read X2 s`; `PT:num->int16`; `pc:num`] 147 THEN
  ARM_STEPS_TAC KP2_EXEC (148--148) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (149--152) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (153--154) THEN
  KP2_LEMMA_TAC "H_TOMONT2"
   [`read events s`; `read X2 s`; `\i. (PT:num->int16)(256 + i)`;
    `pc:num`] 155 THEN
  POLYVEC_INLINE_JOIN_TAC 2 [tomont_3329; o_THM]
   (PV_TOMONT_POST 2 (sp(b + 3072)) "PT" (st 155)) THEN
  INDCPA_TOMONT_TAC "PT2" (b + 3072) 512 "PT" (st 155) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "PT" 512 THEN

  (*** Adding e, in the two inlined loops ***)

  POLYVEC_GHOST_SPLIT_TAC "PT2" (b + 3072) 2 (st 155) THEN
  POLYVEC_GHOST_SPLIT_TAC "EH" (b + 4096) 2 (st 155) THEN
  POLYVEC_GHOST_OFF_TAC "PT2" (b + 3072) 512 1 (st 155) THEN
  POLYVEC_GHOST_OFF_TAC "EH" (b + 4096) 512 1 (st 155) THEN
  ARM_STEPS_TAC KP2_EXEC (156--156) THEN
  KP2_LEMMA_TAC "H_ADD3"
   [`read events s`; `read X3 s`; `read X0 s`; `PT2:num->int16`;
    `EH:num->int16`; `pc:num`] 157 THEN
  ARM_STEPS_TAC KP2_EXEC (158--159) THEN
  KP2_LEMMA_TAC "H_ADD4"
   [`read events s`; `read X26 s`; `read X27 s`;
    `\i. (PT2:num->int16)(256 + i)`; `\i. (EH:num->int16)(256 + i)`;
    `pc:num`] 160 THEN
  INLINE_SP_FOLD_TAC THEN
  POLYVEC_GHOST_DROP_ALL_TAC "PT2" 512 THEN
  POLYVEC_GHOST_DROP_ALL_TAC "EH" 512 THEN

  (*** The reductions of t and s ***)

  ARM_STEPS_TAC KP2_EXEC (161--162) THEN
  LOCAL_REDUCE_TAC
   [`read X0 s`; `\i. word_add ((PT2:num->int16) i) ((EH:num->int16) i)`;
    `pc:num`; `read X30 s`] 163 THEN
  ARM_STEPS_TAC KP2_EXEC (164--165) THEN
  LOCAL_REDUCE_TAC
   [`read X0 s`;
    `\i. word_add ((PT2:num->int16)(256 + i)) ((EH:num->int16)(256 + i))`;
    `pc:num`; `read X30 s`] 166 THEN
  POLYVEC_INLINE_JOIN_TAC 2 []
   (PV_REDUCE_POST 2 (sp(b + 3072))
     "\\i. word_add ((PT2:num->int16) i) ((EH:num->int16) i)" (st 166)) THEN
  INDCPA_REDUCE_TAC "TR" (b + 3072) 512
    "word_add ((PT2:num->int16) i) ((EH:num->int16) i)" (st 166) THEN
  POLYVEC_GHOST_SPLIT_TAC "SH" (b + 2048) 2 (st 166) THEN
  ARM_STEPS_TAC KP2_EXEC (167--168) THEN
  LOCAL_REDUCE_TAC [`read X0 s`; `SH:num->int16`; `pc:num`; `read X30 s`]
    169 THEN
  ARM_STEPS_TAC KP2_EXEC (170--171) THEN
  LOCAL_REDUCE_TAC [`read X0 s`; `\i. (SH:num->int16)(256 + i)`; `pc:num`;
                    `read X30 s`] 172 THEN
  POLYVEC_INLINE_JOIN_TAC 2 [] (PV_REDUCE_POST 2 (sp(b + 2048)) "SH" (st 172))
  THEN
  INDCPA_REDUCE_TAC "SR" (b + 2048) 512 "(SH:num->int16) i" (st 172) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "SH" 512 THEN

  (*** The encodings of the keys ***)

  INDCPA_TOBYTES_PRE_TAC "SR" (b + 2048) 512 (st 172) THEN
  POLYVEC_INLINE_SPLIT_TAC POLYVEC_TOBYTES_SPLIT_GEN (INDCPA_SP(b + 2048)) 2
  THEN INLINE_SP_NORMALIZE_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (173--176) THEN
  LOCAL_TOBYTES_TAC
   [`read X0 s`; `read X1 s`;
    `SUB_LIST(0,256) (list_of_seq (SR:num->int16) 512)`; `pc:num`;
    `read X30 s`] 177 THEN
  ARM_STEPS_TAC KP2_EXEC (178--180) THEN
  LOCAL_TOBYTES_TAC
   [`read X0 s`; `read X1 s`;
    `SUB_LIST(256,256) (list_of_seq (SR:num->int16) 512)`; `pc:num`;
    `read X30 s`] 181 THEN
  POLYVEC_TOBYTES_JOIN_TAC 2 `sk:int64` `list_of_seq (SR:num->int16) 512`
    `s181:armstate` THEN
  INDCPA_TOBYTES_POST_TAC "SR" 512 `\i. ival((SH:num->int16) i)` THEN
  INDCPA_TOBYTES_PRE_TAC "TR" (b + 3072) 512 (st 181) THEN
  POLYVEC_INLINE_SPLIT_TAC POLYVEC_TOBYTES_SPLIT_GEN (INDCPA_SP(b + 3072)) 2
  THEN INLINE_SP_NORMALIZE_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (182--184) THEN
  LOCAL_TOBYTES_TAC
   [`read X0 s`; `read X1 s`;
    `SUB_LIST(0,256) (list_of_seq (TR:num->int16) 512)`; `pc:num`;
    `read X30 s`] 185 THEN
  ARM_STEPS_TAC KP2_EXEC (186--188) THEN
  LOCAL_TOBYTES_TAC
   [`read X0 s`; `read X1 s`;
    `SUB_LIST(256,256) (list_of_seq (TR:num->int16) 512)`; `pc:num`;
    `read X30 s`] 189 THEN
  POLYVEC_TOBYTES_JOIN_TAC 2 `pk:int64` `list_of_seq (TR:num->int16) 512`
    `s189:armstate` THEN
  INDCPA_TOBYTES_POST_TAC "TR" 512
    `\i. ival(word_add ((PT2:num->int16) i) ((EH:num->int16) i))` THEN
  KP2_HALVES_TAC (b + 5632) "rho" THEN
  ARM_STEPS_TAC KP2_EXEC (190--194) THEN KP2_RHO_TAC (st 194) THEN

  (*** Zeroing the buffers, the stack guard, the return ***)

  INDCPA_MEMSETS_TAC KP2_EXEC
   [195,195; 201,204; 210,213; 219,222; 228,231] THEN
  ARM_STEPS_TAC KP2_EXEC (237--243) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (244--259) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KP2_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!pk sk coins (d:byte list) guard mf mc ea el ev pc stackpointer
    returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH d = 32 /\
        (!i j. i < 2 /\ j < 2
               ==> mlkem_samplentt_terminates
                    (APPEND (FST(mlkem_g(APPEND d [word 2])))
                            [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 9536),9536) /\
        PAIRWISE nonoverlapping
         [(pk,800); (sk,768); (word_sub stackpointer (word 9536),9536)] /\
        ALLPAIRS nonoverlapping
         [(pk,800); (sk,768); (word_sub stackpointer (word 9536),9536)]
         [(coins,32); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlkem512_indcpa_keypair_derand) /\
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
                  read (memory :> bytes(pk,800)) s =
                  num_of_bytelist(FST(kpke_keygen mlkem512 d)) /\
                  read (memory :> bytes(sk,768)) s =
                  num_of_bytelist(SND(kpke_keygen mlkem512 d)) /\
                  C_RETURN s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(pk,800); memory :> bytes(sk,768);
                memory :> bytes(word_sub stackpointer (word 9536),9536)])`,
  KP2_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [KP2_CASE_TAC 3776; KP2_CASE_TAC 3760]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset (for mlkem512_gen_matrix) and the safety contract for memcpy, as   *)
(* for gcc 12 -O2. The events depend only on the addresses and on rho. The   *)
(* inlined loops use the same lemmas as the correctness proof, with the      *)
(* contents of the memory as the data, and the vectors of constants of the   *)
(* tomont loops are read-only objects.                                       *)
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

let KP2_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th)
    then ASSUME_CALLEE_SAFETY_TAILED_TAC
          (INDCPA_GEN_MATRIX_SAFE_SPEC
            (MATCH_MP
              MLKEM_NATIVE_GEN_MATRIX_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
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
        MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
        (CONJ th1 th2) in
      ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC gth "H_SHAKE")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHA3_512_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL "H_SHA3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_CBD3_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_CBD3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_BASEMUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC KP2_TOMONT1 "H_TOMONT1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC KP2_TOMONT2 "H_TOMONT2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC KP2_ADD3 "H_ADD3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC KP2_ADD4 "H_ADD4" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_TOBYTES" THEN
  CONCRETIZE_F_EVENTS_TAC KP_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 9536):int64)` THEN
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
   `!i j. i < 2 /\ j < 2
          ==> mlkem_samplentt_terminates
               (APPEND (FST(mlkem_g(APPEND d [word 2])))
                       [word j; word i])` THEN
  ABBREV_TAC `rho = FST(mlkem_g(APPEND d [word 2]))` THEN
  ABBREV_TAC `sigma = SND(mlkem_g(APPEND d [word 2]))` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN `LENGTH(rho:byte list) = 32 /\ LENGTH(sigma:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rho"; "sigma"] THEN REWRITE_TAC[LENGTH_MLKEM_G];
    ALL_TAC];;

let KP2_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,KP2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KP_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

(*** The contents of a polynomial at the address in a register, as the data
     of the lemmas for the loops ***)

let KP2_CONTENTS r =
  let a = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                          r),`s:armstate`) in
  vsubst [a,`a:int64`]
   `\i. read(memory :> bytes16(word_add a (word(2 * i)))) (s:armstate)`;;

let KP2_CONTENTS_OFF r =
  let a = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                          r),`s:armstate`) in
  vsubst [a,`a:int64`]
   `\i. read(memory :> bytes16(word_add (word_add a (word 512))
                                (word(2 * i)))) (s:armstate)`;;

let KP2_SAFE_CASE_TAC b =
  let e = `e:(uarch_event)list` in
  let x n = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            mk_const("X"^string_of_int n,[])),`s:armstate`) in
  let rest = [`pc:num`; `read SP s`; `read X30 s`] in
  let rest0 = [`pc:num`; `read X30 s`] in
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INLINE_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(coins,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (1--8) THEN KP2_BUFFER_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (9--26) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (27--34) THEN
  KP2_INPUT_TAC b `s34:armstate` THEN INLINE_GOT_TAC THEN
  ARM_STEPS_TAC KP2_EXEC [35] THEN
  KP2_SAFE_CALL_TAC "H_SHA3"
   ([e; x 0; x 1; `APPEND d [word 2]:byte list`; `33`; `guard:int64`] @
    rest) 36 THEN
  KP2_G_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (37--40) THEN
  KP2_SAFE_CALL_TAC "H_GM"
   ([e; x 0; x 1; `rho:byte list`; `k:num`; `guard:int64`] @ rest) 41 THEN
  ARM_STEPS_TAC KP2_EXEC (42--66) THEN INLINE_GOT_TAC THEN
  ARM_STEPS_TAC KP2_EXEC [67] THEN
  KP2_SAFE_CALL_TAC "H_SHAKE"
   ([e; x 0; x 1; x 2; x 3; `192`; x 5; x 6; x 7; INDCPA_SP(b + 5312);
     `33`; `guard:int64`] @ rest) 68 THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC KP2_EXEC (k0--k1) THEN
    KP2_SAFE_CALL_TAC "H_CBD3" ([e; x 0; x 1] @ rest0) (k1 + 1))
   [69,71; 73,76; 78,81; 83,86] THEN
  ARM_STEPS_TAC KP2_EXEC (88--91) THEN LIBC_PLT_TAC KP2_EXEC 91 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" KP2_EXEC
   [e; x 0; x 1; x 2; `read X30 s`] (ref KP_SAFE_ALLOWED) 96 THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC KP2_EXEC (k0--k1) THEN
    KP2_SAFE_CALL_TAC "H_NTT" ([e; x 0] @ rest0) (k1 + 1))
   [97,108; 110,111; 113,114; 116,117] THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC KP2_EXEC (k0--k1) THEN
    KP2_SAFE_CALL_TAC "H_MULCACHE" ([e; x 0; x 1] @ rest0) (k1 + 1))
   [119,121; 123,126] THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC KP2_EXEC (k0--k1) THEN
    KP2_SAFE_CALL_TAC "H_BASEMUL" ([e; x 1; x 2; x 3; x 0] @ rest0) (k1 + 1))
   [128,132; 134,138] THEN
  MAP_EVERY (fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th))
    KP2_CONSTANTS THEN
  ARM_STEPS_TAC KP2_EXEC (140--140) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (141--144) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (145--146) THEN
  KP2_SAFE_CALL_TAC "H_TOMONT1" [e; x 2; KP2_CONTENTS `X2`; `pc:num`] 147 THEN
  ARM_STEPS_TAC KP2_EXEC (148--148) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (149--152) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (153--154) THEN
  KP2_SAFE_CALL_TAC "H_TOMONT2" [e; x 2; KP2_CONTENTS `X2`; `pc:num`] 155 THEN
  ARM_STEPS_TAC KP2_EXEC (156--156) THEN
  KP2_SAFE_CALL_TAC "H_ADD3"
   [e; x 3; x 0; KP2_CONTENTS `X3`; KP2_CONTENTS `X0`; `pc:num`] 157 THEN
  ARM_STEPS_TAC KP2_EXEC (158--159) THEN
  KP2_SAFE_CALL_TAC "H_ADD4"
   [e; x 26; x 27; KP2_CONTENTS_OFF `X26`; KP2_CONTENTS_OFF `X27`;
    `pc:num`] 160 THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC KP2_EXEC (k0--k1) THEN
    KP2_SAFE_CALL_TAC "H_REDUCE" ([e; x 0] @ rest0) (k1 + 1))
   [161,162; 164,165; 167,168; 170,171] THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC KP2_EXEC (k0--k1) THEN
    KP2_SAFE_CALL_TAC "H_TOBYTES" ([e; x 0; x 1] @ rest0) (k1 + 1))
   [173,176; 178,180; 182,184; 186,188] THEN
  KP2_HALVES_TAC (b + 5632) "rho" THEN
  ARM_STEPS_TAC KP2_EXEC (190--194) THEN KP2_RHO_TAC "s194" THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC KP2_EXEC (k0--k) THEN LIBC_PLT_TAC KP2_EXEC k THEN
    LIBC_SAFE_CALL_TAC "H_MEMSET" KP2_EXEC
     [e; x 0; x 1; x 2; `read X30 s`] (ref KP_SAFE_ALLOWED) (k + 5))
   [195,195; 201,204; 210,213; 219,222; 228,231] THEN
  ARM_STEPS_TAC KP2_EXEC (237--243) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP2_EXEC (244--259) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  prove
 (`!mf mc ea el ev.
   memset_full_contract mf ea el ev /\ memcpy_safety_contract mc ea el ev
   ==> exists f_events.
        forall e pk sk coins (d:byte list) guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH d = 32 /\
          (!i j. i < 2 /\ j < 2
                 ==> mlkem_samplentt_terminates
                      (APPEND (FST(mlkem_g(APPEND d [word 2])))
                              [word j; word i])) /\
          nonoverlapping (word 0,1)
           (word_sub stackpointer (word 9536),9536) /\
          PAIRWISE nonoverlapping
           [(pk,800); (sk,768);
            (word_sub stackpointer (word 9536),9536)] /\
          ALLPAIRS nonoverlapping
           [(pk,800); (sk,768);
            (word_sub stackpointer (word 9536),9536)]
           [(coins,32); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlkem512_indcpa_keypair_derand) /\
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
                    read (memory :> bytes(word_add pk (word 768),32)) s =
                    num_of_bytelist(FST(mlkem_g(APPEND d [word 2]))) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk coins guard mf mc pc
                              (word_sub stackpointer (word 9536))
                              returnaddress
                              (FST(mlkem_g(APPEND d [word 2]))) /\
                       memaccess_inbounds e2
                        [coins,32; pk,800; sk,768;
                         word_sub stackpointer (word 9536),9536;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + mlkem_poly_cbd3_consts),32;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlkem512_indcpa_keypair_derand_const2),16;
                         word(pc + mlk_poly_invntt_tomont_c_const2),16]
                        [pk,800; sk,768;
                         word_sub stackpointer (word 9536),9536]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,800); memory :> bytes(sk,768);
                  memory :> bytes(word_sub stackpointer (word 9536),9536)])`,
  KP2_SAFE_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [KP2_SAFE_CASE_TAC 3776; KP2_SAFE_CASE_TAC 3760]);;
