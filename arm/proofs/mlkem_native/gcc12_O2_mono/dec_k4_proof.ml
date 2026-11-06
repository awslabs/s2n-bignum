(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decapsulation of ML-KEM-1024 (FIPS 203 Algorithm 18, with the input   *)
(* check of Algorithm 21). This is the code for mlkem1024_dec from mlkem-    *)
(* native's portable C implementation compiled by gcc 12 with -O2 as one     *)
(* translation unit (see mlkem_native/README.md). It checks the              *)
(* decapsulation key with mlkem1024_check_sk, and returns -5 if the check    *)
(* fails. Otherwise it decrypts the ciphertext into m' (the inlined          *)
(* mlkem1024_indcpa_dec), computes K' and r' as G of m' followed by the hash *)
(* h in the key with mlkem_sha3_512, encrypts m' with r' again by            *)
(* mlkem1024_indcpa_enc, compares the result with the ciphertext in          *)
(* constant time, computes J of z (in the key) followed by the ciphertext    *)
(* into the shared secret with mlkem_shake256, and replaces it by K' if the  *)
(* ciphertexts are equal, again in constant time. In both cases it zeroes    *)
(* its buffers. It is verified in the whole image (see libmlkem.ml), using   *)
(* the theorems for mlkem1024_check_sk, mlk_poly_frombytes_c,                *)
(* mlk_poly_ntt_c, mlk_poly_mulcache_compute_c,                              *)
(* mlk_polyvec_basemul_acc_montgomery_cached_c1024,                          *)
(* mlk_poly_invntt_tomont_c, mlk_poly_reduce_c, mlkem_poly_tomsg,            *)
(* mlkem_sha3_512, mlkem1024_indcpa_enc and mlkem_shake256 in the image and  *)
(* the contracts for memset and memcpy.                                      *)
(*                                                                           *)
(* Differences from the gcc 12 -O2 proof. gcc has inlined                    *)
(* mlkem1024_indcpa_dec, and in it the polyvec functions, poly_sub and the   *)
(* decompressions poly_decompress_d11 and poly_decompress_d5, which are      *)
(* calls for ML-KEM-512 and ML-KEM-768. Its code is contiguous (from         *)
(* in_indcpa_dec to in_indcpa_dec_end), so it is proved as a lemma with the  *)
(* postcondition of the gcc 12 -O2 indcpa_dec, from the proof of the gcc 12  *)
(* -O2 indcpa_dec with the glue for the polyvec functions, and the loops of  *)
(* poly_sub and of the two decompressions as lemmas themselves (those of the *)
(* decompressions redo the proofs of the gcc 12 -O2 kernels). The lemma also *)
(* saves X25 to X28, which this code saves only after the check of the key,  *)
(* and keeps the pointer to the ciphertext on the stack, from which the      *)
(* comparison loop loads it in each iteration. The rest is the gcc 12 -O2    *)
(* proof of mlkem1024_dec, with the buffers of indcpa_dec now in this frame. *)
(* The comparison of the ciphertexts keeps an XOR accumulator besides the OR *)
(* accumulator, from which the mask is computed in another way, with the     *)
(* same result.                                                              *)
(*                                                                           *)
(* The frame is the 8032 bytes of the function and the 22864 of              *)
(* mlkem1024_indcpa_enc below them, 30896 in all.                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/check_sk_k4_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/sha3_512_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/indcpa_enc_k4_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/shake256_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_frombytes_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_ntt_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_mulcache_compute_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/basemul_k4_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_invntt_tomont_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_reduce_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_tomsg_proof.ml";;
needs "arm/proofs/mlkem_native/indcpa_inline.ml";;
needs "arm/proofs/mlkem_native/inline_loops.ml";;
needs "arm/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image is listed at the end of layout.ml, with the
     labels of the inlined calls. ***)

let MLKEM_NATIVE_DEC_K4_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "plt_memcpy"; layout_range "plt_memset";
    layout_range "mlkem1024_dec"];;

let KD4_EXEC = MLKEM_NATIVE_DEC_K4_GCC12_O2_MONO_EXEC;;

(*** The vector of constants for the decompressions, from the image ***)

let KD4_CONSTANTS =
  MLKEM_NATIVE_IMAGE_CONST_RULE (layout "mlkem1024_dec_consts") 128;;

(* ------------------------------------------------------------------------- *)
(* The decryption in FIPS 203 in terms of the values computed by the code:   *)
(* the decompressed u and v, the 12-bit fields of the decryption key as      *)
(* decoded (which may be >= q), the NTT of u and its multiplication cache,   *)
(* the product with s in Montgomery form, its inverse NTT, and the result    *)
(* after the subtraction from v and the reduction, whose compression is the  *)
(* message.                                                                  *)
(* ------------------------------------------------------------------------- *)

let KPKE_DECRYPT_K4_RESULT = prove
 (`!dk ct (UD:num->int16) (VD:num->int16) (SS:num->int16) (UH:num->int16)
    (MC:num->int16) (WP:num->int16) (WI:num->int16) (VR:num->int16).
     (!i. i < 1024
          ==> UD i =
              word((3329 * (num_of_bytelist ct DIV 2 EXP (11 * i)) MOD
                    2 EXP 11 + 1024) DIV 2048)) /\
     (!i. i < 256
          ==> VD i =
              word((3329 * (num_of_bytelist(mlkem_slice 1408 160 ct) DIV
                            2 EXP (5 * i)) MOD 2 EXP 5 + 16) DIV 32)) /\
     (!i. i < 1024
          ==> SS i = word((num_of_bytelist dk DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(UH(256 * j + i)) ==
                 forward_ntt (\n. ival(UD(256 * j + n))) i) (mod &3329) /\
                abs(ival(UH(256 * j + i))) <= &23594) /\
     (!j p. j < 4 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(UH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(WP(2 * p)) ==
               &169 *
               ((ival(SS(768 + 2 * p + 1)) * ival(MC(384 + p)) +
                 ival(SS(768 + 2 * p)) * ival(UH(768 + 2 * p))) +
                (ival(SS(512 + 2 * p + 1)) * ival(MC(256 + p)) +
                 ival(SS(512 + 2 * p)) * ival(UH(512 + 2 * p))) +
                (ival(SS(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p))) +
                (ival(SS(2 * p + 1)) * ival(MC p) +
                 ival(SS(2 * p)) * ival(UH(2 * p))))) (mod &3329) /\
              (ival(WP(2 * p + 1)) ==
               &169 *
               ((ival(SS(768 + 2 * p + 1)) * ival(UH(768 + 2 * p)) +
                 ival(SS(768 + 2 * p)) * ival(UH(768 + 2 * p + 1))) +
                (ival(SS(512 + 2 * p + 1)) * ival(UH(512 + 2 * p)) +
                 ival(SS(512 + 2 * p)) * ival(UH(512 + 2 * p + 1))) +
                (ival(SS(256 + 2 * p + 1)) * ival(UH(256 + 2 * p)) +
                 ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p + 1))) +
                (ival(SS(2 * p + 1)) * ival(UH(2 * p)) +
                 ival(SS(2 * p)) * ival(UH(2 * p + 1))))) (mod &3329)) /\
     (!i. i < 256
          ==> (ival(WI i) == inverse_ntt (\n. ival(WP n)) i) (mod &3329) /\
              abs(ival(WI i)) <= &26624) /\
     (!i. i < 256 ==> ival(VR i) = ival(word_sub (VD i) (WI i)) rem &3329)
     ==> nsum {i | i < 256}
              (\i. ((4 * val(VR i) + 3329) DIV 6658) MOD 2 * 2 EXP i) =
         num_of_bytelist(kpke_decrypt mlkem1024 dk ct)`,
  let parity_tac =
    X_GEN_TAC `n':num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`2`; `128`; `n':num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 128 = 256`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `b:num`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o
      MATCH_MP(ARITH_RULE `b < 2 ==> b = 0 \/ b = 1`)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    (SUBGOAL_THEN `2 * p < 256 /\ 2 * p + 1 < 256` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `p < 128` THEN ARITH_TAC; ALL_TAC])
and row_tac =
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; INT_CONG_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem1024] THEN
  REWRITE_TAC[KPKE_DECRYPT_FIPS] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  W(fun (_,w) ->
    let enc = find_term (fun t -> match strip_comb t with
       (Const("mlkem_encode",_),[_;_;_]) -> true | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) NUM_OF_BYTELIST_MLKEM_ENCODE
            (mk_comb(`num_of_bytelist`,enc)))) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV THENC DIVIDES_CONV);
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[MULT_CLAUSES] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  W(fun (_,w) ->
    let pinv = find_term (fun t -> match t with
      Comb(Const("mlkem_ntt_inv",_),_) -> true | _ -> false) w in
    SUBGOAL_THEN
     (mk_comb(mk_comb(`(IN):((1->num)->int)->(((1->num)->int)->bool)->bool`,
                      pinv),`ring_carrier mlkem_rq`)) ASSUME_TAC THENL
     [MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
      REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
      ALL_TAC]) THEN
  W(fun (_,w) ->
    let wt = find_term (fun t -> match t with
      Comb(Comb(Comb(Const("ring_sub",_),_),_),_) -> true | _ -> false) w in
    SUBGOAL_THEN
     (mk_comb(mk_comb(`(IN):((1->num)->int)->(((1->num)->int)->bool)->bool`,
                      wt),`ring_carrier mlkem_rq`)) ASSUME_TAC THENL
     [MATCH_MP_TAC RING_SUB THEN ASM_REWRITE_TAC[MLKEM_POLY_IN_RQ];
      ALL_TAC]) THEN
  W(fun (_,w) ->
    let t = find_term (fun t -> match t with
      Comb(Const("num_of_int",_),
           Comb(Comb(Const("rem",_),
                Comb(Comb(Const("mlkem_compress",_),_),_)),_)) -> true
      | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) MLKEM_COMPRESS_DIGIT t)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MLKEM_COEFF_POS THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VAL_EQ_NUM_OF_INT_IVAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC MLKEM_COEFF_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MLKEM_RQ_COEFF_SUB; MLKEM_POLY_IN_RQ] THEN
  REWRITE_TAC[MLKEM_ZQ; INT_REM_EQ] THEN
  ABBREV_TAC `fv = (num_of_bytelist (mlkem_slice 1408 160 ct) DIV
                    2 EXP (5 * i)) MOD 2 EXP 5` THEN
  SUBGOAL_THEN `(3329 * fv + 16) DIV 32 < 3329` ASSUME_TAC THENL
   [SUBGOAL_THEN `fv < 32` MP_TAC THENL
     [EXPAND_TAC "fv" THEN
      REWRITE_TAC[ARITH_RULE `32 = 2 EXP 5`; MOD_LT_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ival(word((3329 * fv + 16) DIV 32):int16) =
                &((3329 * fv + 16) DIV 32)` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_SMALL THEN
    UNDISCH_TAC `(3329 * fv + 16) DIV 32 < 3329` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(ival((WI:num->int16) i)) <= &26624` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  W(fun (_,w) ->
    let t = find_term (fun t -> match t with
      Comb(Const("ival",_),Comb(Comb(Const("word_sub",_),_),_)) -> true
      | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) IVAL_WORD_SUB_BOUNDED t)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(3329 * fv + 16) DIV 32 < 3329` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
    UNDISCH_TAC `abs(ival((WI:num->int16) i)) <= &26624` THEN INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[COEFF_MLKEM_POLY] THEN
  SIMP_TAC[MLKEM_DECODE_SMALL; ARITH_RULE `5 < 12`] THEN
  ASM_SIMP_TAC[MLKEM_DECOMPRESS_NUM; ARITH_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&((3329 * fv + 16) DIV 32) rem &3329 = &((3329 * fv + 16) DIV 32)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INT_REM_LT THEN REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(b:int == d) (mod q) ==> (a - b == a - d) (mod q)`) THEN
  SUBGOAL_THEN
   `!j' n. j' < 4 /\ n < 256
           ==> (ival((UH:num->int16)(256 * j' + n)) ==
                mlkem_ntt (mlkem_poly
                  (\j''. mlkem_decompress 11
                          (mlkem_decode 11 ct (256 * j' + j'')))) n)
               (mod &3329)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MLKEM_NATIVE_NTT_CONG THEN
    EXISTS_TAC `\n. (UD:num->int16)(256 * j' + n)` THEN
    REWRITE_TAC[MLKEM_POLY_IN_RQ] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_SIMP_TAC[] THEN
    X_GEN_TAC `n':num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `256 * j' + n' < 1024` ASSUME_TAC THENL
     [UNDISCH_TAC `j' < 4` THEN UNDISCH_TAC `n' < 256` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[COEFF_MLKEM_POLY; MLKEM_DECODE_SMALL; ARITH_RULE `11 < 12`;
                 MLKEM_DECOMPRESS_NUM; ARITH_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[INT_CONG_RREM] THEN
    ABBREV_TAC `fu = (num_of_bytelist ct DIV 2 EXP (11 * (256 * j' + n'))) MOD
                     2048` THEN
    SUBGOAL_THEN `fu < 2048` MP_TAC THENL
     [EXPAND_TAC "fu" THEN REWRITE_TAC[MOD_LT_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV;
      DISCH_TAC] THEN
    SUBGOAL_THEN `ival(word((3329 * fu + 1024) DIV 2048):int16) =
                  &((3329 * fu + 1024) DIV 2048)` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_WORD_SMALL THEN UNDISCH_TAC `fu < 2048` THEN ARITH_TAC;
      REWRITE_TAC[INT_CONG_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n'. n' < 256
         ==> (ival((WP:num->int16) n') ==
              &169 * ring_sum mlkem_zq {j' | j' < 4}
                      (\j'. fips203_multiply_ntts
                             (\n. mlkem_decode 12 dk (256 * j' + n))
                             (mlkem_ntt (mlkem_poly
                               (\j''. mlkem_decompress 11
                                       (mlkem_decode 11 ct (256 * j' + j'')))))
                             n')) (mod &3329)`
  ASSUME_TAC THENL
   [parity_tac THEN
    (SUBGOAL_THEN
      `!j' x. j' < 4 /\ x < 256
              ==> (ival((SS:num->int16)(256 * j' + x)) ==
                   mlkem_decode 12 dk (256 * j' + x)) (mod &3329)`
     ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC TT_DECODE_CONG THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `j' < 4` THEN UNDISCH_TAC `x < 256` THEN ARITH_TAC;
       ALL_TAC])
    THENL
     [MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 dk (256 * j' + n)`;
        `\j' n. ival((SS:num->int16)(256 * j' + n))`;
        `\j' n. ival((UH:num->int16)(256 * j' + n))`;
        `\j'. ival((MC:num->int16)(128 * j' + p))`;
        `\j'. mlkem_ntt (mlkem_poly
                (\j''. mlkem_decompress 11
                        (mlkem_decode 11 ct (256 * j' + j''))))`;
        `ival((WP:num->int16)(2 * p))`; `p:num`] BASEMUL4_ROW_EVEN);
      MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 dk (256 * j' + n)`;
        `\j' n. ival((SS:num->int16)(256 * j' + n))`;
        `\j' n. ival((UH:num->int16)(256 * j' + n))`;
        `\j'. mlkem_ntt (mlkem_poly
                (\j''. mlkem_decompress 11
                        (mlkem_decode 11 ct (256 * j' + j''))))`;
        `ival((WP:num->int16)(2 * p + 1))`; `p:num`] BASEMUL4_ROW_ODD)] THEN
    row_tac;
    ALL_TAC] THEN
  W(fun (_,w) ->
    let pinv = find_term (fun t -> match t with
      Comb(Const("mlkem_ntt_inv",_),_) -> true | _ -> false) w in
    MP_TAC(ISPECL [rand pinv; `\n. ival((WP:num->int16) n)`; `&169:int`;
                   `i:num`] MLKEM_NTT_INV_CONG_MUL)) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_SIMP_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
    DISCH_TAC] THEN
  MATCH_MP_TAC INT_CONG_MONT_CANCEL THEN
  EXISTS_TAC `inverse_ntt (\n. ival((WP:num->int16) n)) i` THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The inlined decompressions. For each polynomial of u, poly_decompress_d11 *)
(* is the loop of the gcc 12 -O2 kernel over the 32 blocks of eleven bytes   *)
(* (from loop2 to its exit), and poly_decompress_d5 of v is the loop of the  *)
(* gcc 12 -O2 kernel over the 32 blocks of five bytes (loop3), with the same *)
(* vectors of constants in Q2 and Q3. Both are proved here as lemmas, by the *)
(* proofs of the gcc 12 -O2 kernels with the instructions of this code (the  *)
(* first load of a block is before the increment of the pointer, and the d5  *)
(* loop tests the output pointer), with the events.                          *)
(* ------------------------------------------------------------------------- *)

let KD4_D11_BYTES = prove
 (`!a n i s j.
        read (memory :> bytes(a,352)) s = n /\ i < 32 /\ j < 11
        ==> read (memory :> bytes8(word_add a (word(11 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (88 * i)):88 word) (8 * j,8)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `352`; `n:num`; `11 * i + j`; `s:armstate`]
                READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`] THEN
  REWRITE_TAC[ARITH_RULE `8 * (11 * i + j) = 88 * i + 8 * j`]);;

let KD4_D11_HALF = prove
 (`!a n i s.
        read (memory :> bytes(a,352)) s = n /\ i < 32
        ==> read (memory :> bytes16(word_add a (word(11 * i)))) s =
            word_subword (word(n DIV 2 EXP (88 * i)):88 word) (0,16)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `352`; `n:num`; `11 * i`; `s:armstate`]
                READ_MEMORY_BYTES16_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[EXP; DIV_1; ARITH_RULE `2 EXP 16 = 65536`] THEN
  REWRITE_TAC[ARITH_RULE `8 * 11 * i = 88 * i`]);;

let KD4_D11D_LANE = prove
 (`!f:11 word.
     word_subword
      (word_ushr
        (word_add
          (word_mul (word_zx (word_zx f:int16):int32) (word 3329))
          (word 1024)) 11) (0,16):int16 =
     word((3329 * val f + 1024) DIV 2048)`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_USHR; VAL_WORD_ADD;
              VAL_WORD_MUL; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_1] THEN
  MP_TAC(ISPEC `f:11 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(f:11 word)`,`v:num`) THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `v MOD 65536 = v /\ v MOD 4294967296 = v`
   (fun th -> REWRITE_TAC[th])
  THENL [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `v < 2048 ==> v * 3329 < 4294967296 /\ v * 3329 + 1024 < 4294967296`] THEN
  SUBGOAL_THEN `(v * 3329 + 1024) DIV 2048 < 65536 /\
                (3329 * v + 1024) DIV 2048 < 65536`
   (fun th -> SIMP_TAC[th; MOD_LT]) THENL
   [REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC]);;

let KD4_D11D_FIELD = prove
 (`!n i k. k < 8
     ==> val(word_subword (word(n DIV 2 EXP (88 * i)):88 word)
                          (11 * k,11):11 word) =
         (n DIV 2 EXP (11 * (8 * i + k))) MOD 2048`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 11 11 = 11`] THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `k < 8 ==> 11 * k + 11 <= 88`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2048 = 2 EXP 11`] THEN
  REWRITE_TAC[ARITH_RULE `88 * i + 11 * k = 11 * (8 * i + k)`]);;

let kd4_d11d_lanepat =
  `word_subword
    (word_ushr
      (word_add (word_mul (word_zx (t:int16):int32) (word 3329))
                (word 1024)) 11) (0,16):int16`;;

let KD4_D11D_LANE_RULE th =
  let v = rand(concl th) in
  let ls = find_terms (fun t -> can (term_match [] kd4_d11d_lanepat) t) v in
  let gs = map (fun t -> genvar(type_of t)) ls in
  let v' = subst (zip gs ls) v in
  let bth = tryfind (fun g -> BITBLAST_RULE(mk_eq(v',g))) gs in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]))
   (TRANS th (INST (zip ls gs) bth));;

let KD4_D11D_FIELD_TAC k =
  W(fun (asl,w) ->
     let lk = lhs w in
     let _,tmins,_ = term_match [] kd4_d11d_lanepat lk in
     let tk = rev_assoc `t:int16` tmins in
     let fth = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (MP (SPECL [`n:num`; `i:num`; mk_small_numeral k] KD4_D11D_FIELD)
          (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                         (mk_small_numeral k) `8`)))) in
     let st = rand(lhand(concl fth)) in
     let st' = subst [`w:88 word`,`word(n DIV 2 EXP (88 * i)):88 word`] st in
     SUBGOAL_THEN (mk_eq(tk,mk_comb(`word_zx:11 word->int16`,st')))
       SUBST1_TAC THENL
      [W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)); ALL_TAC] THEN
     REWRITE_TAC[KD4_D11D_LANE] THEN EXPAND_TAC "w" THEN REWRITE_TAC[fth] THEN
     REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

(*** The test of the loop over the blocks, a pointer against its end ***)

let KD4_LOOP_TEST = prove
 (`!a:int64 m n i.
        ~(m = 0) /\ i < n /\ m * n < 2 EXP 64
        ==> (val(word_sub (word_add (word_add a (word(m * i))) (word m))
                          (word_add a (word(m * n)))) = 0 <=>
             ~(i + 1 < n)) /\
            (val(word_sub (word_add a (word(m * n)))
                          (word_add (word_add a (word(m * i))) (word m))) =
             0 <=> ~(i + 1 < n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[WORD_RULE `word_add a x = word_add a y <=> x:int64 = y`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `m * i + m < 2 EXP 64 /\ m * n < 2 EXP 64`
   (fun th -> SIMP_TAC[th; MOD_LT]) THENL
   [ASM_REWRITE_TAC[] THEN
    TRANS_TAC LET_TRANS `m * n` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `m * i + m = m * (i + 1)`] THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `m * i + m = m * (i + 1)`] THEN
  ASM_SIMP_TAC[EQ_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let KD4_D11_GOAL = `exists f_events.
     forall e a r n pc.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       nonoverlapping (r,512) (word pc,libmlkem_size) /\
       nonoverlapping (r,512) (a,352)
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                 read PC s = word (pc + mlkem1024_dec_loop2) /\
                 read X1 s = a /\ read X7 s = r /\
                 read X8 s = word_add a (word 352) /\
                 read Q2 s = word 0x00000400000004000000040000000400 /\
                 read Q3 s = word 0x0d010d010d010d010d010d010d010d01 /\
                 read (memory :> bytes(a,352)) s = n /\
                 read events s = e)
            (\s. read PC s = word (pc + mlkem1024_dec_loop2_exit) /\
                 read X1 s = word_add a (word 352) /\
                 (!i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (11 * i)) MOD 2 EXP 11 +
                                1024) DIV 2048)) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a r pc /\
                    memaccess_inbounds e2 [a,352; r,512] [r,512]))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X11; X12] ,,
             MAYCHANGE [Q0; Q1; Q4] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes(r,512)])`;;

let KD4_D11_INV = `\i s. read X1 s = word_add a (word(11 * i)) /\
          read X7 s = word_add r (word(16 * i)) /\
          read X8 s = word_add a (word 352) /\
          read Q2 s = word 0x00000400000004000000040000000400 /\
          read Q3 s = word 0x0d010d010d010d010d010d010d010d01 /\
          read (memory :> bytes(a,352)) s = n /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((3329 * (n DIV 2 EXP (11 * j)) MOD 2 EXP 11 + 1024)
                        DIV 2048))`;;

let KD4_D11 = prove
 (KD4_D11_GOAL,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (r:int64) (pc:num).
      APPEND (f_ev_epil a r pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop a r pc i)) (f_ev_prol a r pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `r:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst KD4_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem1024_dec_loop2`
   `pc + mlkem1024_dec_loop2_exit` KD4_D11_INV THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC;
    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
        check (fun th -> is_forall(concl th) &&
                         free_in `bytes16` (concl th)));
      DISCHARGE_SAFETY_PROPERTY_TAC]] THEN

  (*** The loop body, for eleven bytes and eight coefficients ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY (fun j ->
    MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
       (SPECL [`a:int64`; `n:num`; `i:num`; `s0:armstate`;
               mk_small_numeral j] KD4_D11_BYTES)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC) (1--10) THEN
  MP_TAC(SPECL [`a:int64`; `n:num`; `i:num`; `s0:armstate`] KD4_D11_HALF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `w:88 word = word(n DIV 2 EXP (88 * i))` THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KD4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[]) (1--50) THEN
  FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (can (term_match [] `read (memory :> bytes128 a) s = x`) o
           concl)) THEN
  DISCH_THEN(fun th -> MAP_EVERY (ASSUME_TAC o KD4_D11D_LANE_RULE o
                       CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV [])))
                       (CONJUNCTS th)) THEN
  ARM_STEPS_TAC KD4_EXEC (51--52) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONV_RULE NUM_REDUCE_CONV
   (MP (SPECL [`a:int64`; `11`; `32`; `i:num`] KD4_LOOP_TEST)
       (CONJ (EQT_ELIM(NUM_REDUCE_CONV `~(11 = 0)`))
             (CONJ (ASSUME `i < 32`) (EQT_ELIM(NUM_REDUCE_CONV
                                         `11 * 32 < 2 EXP 64`)))))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `11 * (i + 1) = 11 * i + 11`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; DISCHARGE_SAFETY_PROPERTY_TAC] THEN
  REWRITE_TAC[ARITH_RULE
   `j < 8 * (i + 1) <=>
    j < 8 * i \/ j = 8 * i \/ j = 8 * i + 1 \/ j = 8 * i + 2 \/
    j = 8 * i + 3 \/ j = 8 * i + 4 \/ j = 8 * i + 5 \/ j = 8 * i + 6 \/
    j = 8 * i + 7`] THEN
  REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
              FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `2 * 8 * i = 16 * i`;
              ARITH_RULE `2 * (8 * i + 1) = 16 * i + 2`;
              ARITH_RULE `2 * (8 * i + 2) = 16 * i + 4`;
              ARITH_RULE `2 * (8 * i + 3) = 16 * i + 6`;
              ARITH_RULE `2 * (8 * i + 4) = 16 * i + 8`;
              ARITH_RULE `2 * (8 * i + 5) = 16 * i + 10`;
              ARITH_RULE `2 * (8 * i + 6) = 16 * i + 12`;
              ARITH_RULE `2 * (8 * i + 7) = 16 * i + 14`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL (map KD4_D11D_FIELD_TAC (0--7)));;

let KD4_D5_BYTES = prove
 (`!a n i s j.
        read (memory :> bytes(a,160)) s = n /\ i < 32 /\ j < 5
        ==> read (memory :> bytes8(word_add a (word(5 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (40 * i)):40 word) (8 * j,8)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `160`; `n:num`; `5 * i + j`; `s:armstate`]
                READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`] THEN
  REWRITE_TAC[ARITH_RULE `8 * (5 * i + j) = 40 * i + 8 * j`]);;

let KD4_D5D_LANE = prove
 (`!f:5 word.
     word_subword
      (word_ushr
        (word_add
          (word_mul (word_zx (word_shl (word_zx (word_zx f:byte):int16) 0):
                     int32)
                    (word 3329))
          (word 16)) 5) (0,16):int16 =
     word((3329 * val f + 16) DIV 32)`,
  GEN_TAC THEN REWRITE_TAC[WORD_SHL_ZERO] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_USHR; VAL_WORD_ADD;
              VAL_WORD_MUL; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_1] THEN
  MP_TAC(ISPEC `f:5 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(f:5 word)`,`v:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let KD4_D5D_FIELD = prove
 (`!n i k. k < 8
     ==> val(word_subword (word(n DIV 2 EXP (40 * i)):40 word)
                          (5 * k,5):5 word) =
         (n DIV 2 EXP (5 * (8 * i + k))) MOD 32`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 5 5 = 5`] THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `k < 8 ==> 5 * k + 5 <= 40`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `32 = 2 EXP 5`] THEN
  REWRITE_TAC[ARITH_RULE `40 * i + 5 * k = 5 * (8 * i + k)`]);;

let kd4_d5d_lanepat =
  `word_subword
    (word_ushr
      (word_add
        (word_mul (word_zx (word_shl (word_zx (t:byte):int16) 0):int32)
                  (word 3329))
        (word 16)) 5) (0,16):int16`;;

let KD4_D5D_LANE_RULE th =
  let v = rand(concl th) in
  let ls = find_terms (fun t -> can (term_match [] kd4_d5d_lanepat) t) v in
  let gs = map (fun t -> genvar(type_of t)) ls in
  let v' = subst (zip gs ls) v in
  let bth = tryfind (fun g -> BITBLAST_RULE(mk_eq(v',g))) gs in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]))
   (TRANS th (INST (zip ls gs) bth));;

let KD4_D5D_FIELD_TAC k =
  W(fun (asl,w) ->
     let lk = lhs w in
     let _,tmins,_ = term_match [] kd4_d5d_lanepat lk in
     let tk = rev_assoc `t:byte` tmins in
     let fth = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (MP (SPECL [`n:num`; `i:num`; mk_small_numeral k] KD4_D5D_FIELD)
          (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                         (mk_small_numeral k) `8`)))) in
     let st = rand(lhand(concl fth)) in
     let st' = subst [`w:40 word`,`word(n DIV 2 EXP (40 * i)):40 word`] st in
     SUBGOAL_THEN (mk_eq(tk,mk_comb(`word_zx:5 word->byte`,st')))
       SUBST1_TAC THENL
      [W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)); ALL_TAC] THEN
     REWRITE_TAC[KD4_D5D_LANE] THEN EXPAND_TAC "w" THEN REWRITE_TAC[fth] THEN
     REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let KD4_D5_GOAL = `exists f_events.
     forall e a r n pc.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       nonoverlapping (r,512) (word pc,libmlkem_size) /\
       nonoverlapping (r,512) (a,160)
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                 read PC s = word (pc + mlkem1024_dec_loop3) /\
                 read X2 s = a /\ read X8 s = r /\
                 read X27 s = word_add r (word 512) /\
                 read Q2 s = word 0x00000010000000100000001000000010 /\
                 read Q3 s = word 0x0d010d010d010d010d010d010d010d01 /\
                 read (memory :> bytes(a,160)) s = n /\
                 read events s = e)
            (\s. read PC s = word (pc + mlkem1024_dec_loop3_exit) /\
                 (!i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (5 * i)) MOD 2 EXP 5 +
                                16) DIV 32)) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a r pc /\
                    memaccess_inbounds e2 [a,160; r,512] [r,512]))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X6; X7; X8; X9; X10] ,,
             MAYCHANGE [Q0; Q1; Q4] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes(r,512)])`;;

let KD4_D5_INV = `\i s. read X2 s = word_add a (word(5 * i)) /\
          read X8 s = word_add r (word(16 * i)) /\
          read X27 s = word_add r (word 512) /\
          read Q2 s = word 0x00000010000000100000001000000010 /\
          read Q3 s = word 0x0d010d010d010d010d010d010d010d01 /\
          read (memory :> bytes(a,160)) s = n /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((3329 * (n DIV 2 EXP (5 * j)) MOD 2 EXP 5 + 16)
                        DIV 32))`;;

let KD4_D5 = prove
 (KD4_D5_GOAL,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (r:int64) (pc:num).
      APPEND (f_ev_epil a r pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop a r pc i)) (f_ev_prol a r pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `r:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst KD4_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem1024_dec_loop3`
   `pc + mlkem1024_dec_loop3_exit` KD4_D5_INV THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC;
    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
        check (fun th -> is_forall(concl th) &&
                         free_in `bytes16` (concl th)));
      DISCHARGE_SAFETY_PROPERTY_TAC]] THEN

  (*** The loop body, for five bytes and eight coefficients ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY (fun j ->
    MP_TAC(REWRITE_RULE[ADD_CLAUSES]
     (CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
       (SPECL [`a:int64`; `n:num`; `i:num`; `s0:armstate`;
               mk_small_numeral j] KD4_D5_BYTES))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC) (0--4) THEN
  ABBREV_TAC `w:40 word = word(n DIV 2 EXP (40 * i))` THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KD4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[]) (1--39) THEN
  FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (can (term_match [] `read (memory :> bytes128 a) s = x`) o
           concl)) THEN
  DISCH_THEN(fun th -> MAP_EVERY (ASSUME_TAC o KD4_D5D_LANE_RULE o
                       CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV [])))
                       (CONJUNCTS th)) THEN
  ARM_STEPS_TAC KD4_EXEC (40--41) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONV_RULE NUM_REDUCE_CONV
   (MP (SPECL [`r:int64`; `16`; `32`; `i:num`] KD4_LOOP_TEST)
       (CONJ (EQT_ELIM(NUM_REDUCE_CONV `~(16 = 0)`))
             (CONJ (ASSUME `i < 32`) (EQT_ELIM(NUM_REDUCE_CONV
                                         `16 * 32 < 2 EXP 64`)))))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; DISCHARGE_SAFETY_PROPERTY_TAC] THEN
  REWRITE_TAC[ARITH_RULE
   `j < 8 * (i + 1) <=>
    j < 8 * i \/ j = 8 * i \/ j = 8 * i + 1 \/ j = 8 * i + 2 \/
    j = 8 * i + 3 \/ j = 8 * i + 4 \/ j = 8 * i + 5 \/ j = 8 * i + 6 \/
    j = 8 * i + 7`] THEN
  REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
              FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `2 * 8 * i = 16 * i`;
              ARITH_RULE `2 * (8 * i + 1) = 16 * i + 2`;
              ARITH_RULE `2 * (8 * i + 2) = 16 * i + 4`;
              ARITH_RULE `2 * (8 * i + 3) = 16 * i + 6`;
              ARITH_RULE `2 * (8 * i + 4) = 16 * i + 8`;
              ARITH_RULE `2 * (8 * i + 5) = 16 * i + 10`;
              ARITH_RULE `2 * (8 * i + 6) = 16 * i + 12`;
              ARITH_RULE `2 * (8 * i + 7) = 16 * i + 14`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL (map KD4_D5D_FIELD_TAC (0--7)));;

(* ------------------------------------------------------------------------- *)
(* The inlined indcpa_dec, from in_indcpa_dec to in_indcpa_dec_end, as a     *)
(* lemma for each value of the offset b of the buffers (which the function   *)
(* aligns to 32 bytes), with the postcondition of the gcc 12 -O2             *)
(* indcpa_dec: the message m' at b + 7808. The buffers of indcpa_dec are at  *)
(* b (s), b + 2048 (u), b + 5696 (the multiplication cache), b + 6720 (the   *)
(* product) and b + 7232 (v), where the gcc 12 -O2 function had them at 0,   *)
(* 2048, 4096, 5120 and 5632 in its own frame. The lemma also saves X25 to   *)
(* X28 and the pointer c to the ciphertext at SP + 48 to SP + 72 and SP +    *)
(* 112, and leaves the pointer to the encapsulation key in the decapsulation *)
(* key in X26, as the code of the function does in it. The proof is that of  *)
(* the gcc 12 -O2 function, with the glue for the inlined polyvec functions, *)
(* the loops of the decompressions and of poly_sub as lemmas.                *)
(* ------------------------------------------------------------------------- *)

(*** The four parts of the 1408 bytes of the compressed u, and the 11-bit
     fields of each ***)

let KD4_DU_SPLIT = prove
 (`!a k n s j.
        read (memory :> bytes(a,352 * k)) s = n /\ j < k
        ==> read (memory :> bytes(word_add a (word(352 * j)),352)) s =
            (n DIV 2 EXP (2816 * j)) MOD 2 EXP 2816`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE;
              ARITH_RULE `2816 * j = 8 * 352 * j`;
              ARITH_RULE `2816 = 8 * 352`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let KD4_DU_FIELD = prove
 (`!n k i.
        i < 256
        ==> ((n DIV 2 EXP k) MOD 2 EXP 2816 DIV 2 EXP (11 * i)) MOD 2 EXP 11 =
            (n DIV 2 EXP (k + 11 * i)) MOD 2 EXP 11`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [DIV_MOD] THEN
  REWRITE_TAC[GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `i < 256 ==> MIN 2816 (11 * i + 11) = 11 * i + 11`] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_MOD; DIV_DIV]);;

let KD4_CT_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [`c:int64`; `ct:byte list`]
         `read (memory :> bytes(c,1568)) s = num_of_bytelist ct`) (concl th)
    then
      ASSUME_TAC(REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
       (REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_MOD;
                     ARITH_RULE `MIN 1568 1408 = 1408`]
        (AP_THM(AP_TERM `(MOD):num->num->num`
                 (REWRITE_RULE[READ_COMPONENT_COMPOSE] th))
           `2 EXP (8 * 1408)`))) THEN
      MP_TAC(SPECL [`c:int64`; `ct:byte list`; `1408`; `160`;
                    rand(lhand(concl th))] READ_MEMORY_BYTES_SLICE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC]
    else NO_TAC);;

(*** The pointers of the outer loop of polyvec_decompress_du, with the
     additions and subtractions of constants folded ***)

let KD4_WSUB_CONV tm =
  match tm with
    Comb(Comb(Const("word_sub",_),
              Comb(Comb(Const("word_add",_),x),Comb(Const("word",_),k))),
         Comb(Const("word",_),n))
      when is_numeral k && is_numeral n &&
           dest_numeral k >=/ dest_numeral n ->
      let d = dest_numeral k -/ dest_numeral n in
      let r = if d =/ Num.num_of_int 0 then x
              else mk_comb(mk_comb(`word_add:int64->int64->int64`,x),
                           mk_comb(`word:num->int64`,mk_numeral d)) in
      WORD_RULE(mk_eq(tm,r))
  | _ -> failwith "KD4_WSUB_CONV";;

(*** The tests of the loops over the polynomials compare two pointers
     with the same base, as x + m and x + n for numerals m and n ***)

let KD4_PTRCMP_CONV tm =
  match tm with
    Comb(Comb(Const("word_sub",_),
              Comb(Comb(Const("word_add",_),x),Comb(Const("word",_),m))),
         Comb(Comb(Const("word_add",_),y),Comb(Const("word",_),n)))
      when x = y && is_numeral m && is_numeral n ->
      let p64 = power_num (Num.num_of_int 2) (Num.num_of_int 64) in
      let d = mod_num (dest_numeral m -/ dest_numeral n +/ p64) p64 in
      WORD_RULE(mk_eq(tm,mk_comb(`word:num->int64`,mk_numeral d)))
  | _ -> failwith "KD4_PTRCMP_CONV";;

let KD4_TIDY_TAC =
  let pat = `read (r:(armstate,int64)component) (s:armstate)`
  and pcpat = `read PC (s:armstate) = if p then x else y`
  and conv = TOP_DEPTH_CONV KD4_WSUB_CONV THENC
             ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV
  and gconv = DEPTH_CONV KD4_PTRCMP_CONV THENC
              REWRITE_CONV[VAL_WORD; DIMINDEX_64] THENC NUM_REDUCE_CONV in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if can (term_match [] pcpat) c then
      REWRITE_RULE[COND_CLAUSES]
       (CONV_RULE(RAND_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV gconv)))) th)
    else if is_eq c && can (term_match [] pat) (lhand c)
    then CONV_RULE(RAND_CONV conv) th else th);;

(*** The stages, as for gcc 12 -O2 with the offsets of this frame and the
     state as a parameter ***)

let KD4_UD_TAC b s =
  INDCPA_GHOST_TAC "UD" (b + 2048) 1024 s THEN
  SUBGOAL_THEN
   `!i. i < 1024
        ==> (UD:num->int16) i =
            word((3329 * (num_of_bytelist ct DIV 2 EXP (11 * i)) MOD
                  2 EXP 11 + 1024) DIV 2048)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "UD" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem (mk_var(s,`:armstate`)) (frees(concl th)) && is_forall(concl th) &&
      free_in `ctt:num` (concl th) &&
      can (find_term ((=) `1024`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN EXPAND_TAC "ctt" THEN MATCH_MP_TAC DIV_MOD_EXP_LOW THEN
    UNDISCH_TAC `i < 1024` THEN ARITH_TAC;
    ALL_TAC];;

let KD4_VD_TAC b s =
  INDCPA_GHOST_TAC "VD" (b + 7232) 256 s THEN
  SUBGOAL_THEN
   `!i. i < 256
        ==> (VD:num->int16) i =
            word((3329 * (num_of_bytelist(mlkem_slice 1408 160 ct) DIV
                          2 EXP (5 * i)) MOD 2 EXP 5 + 16) DIV 32)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "VD" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem (mk_var(s,`:armstate`)) (frees(concl th)) && is_forall(concl th) &&
      can (find_term ((=) `num_of_bytelist(mlkem_slice 1408 160 ct)`))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

let KD4_SS_TAC b s =
  INDCPA_GHOST_TAC "SS" b 1024 s THEN
  SUBGOAL_THEN
   `!i. i < 1024
        ==> (SS:num->int16) i =
            word((num_of_bytelist dk DIV 2 EXP (12 * i)) MOD 2 EXP 12)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "SS" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem (mk_var(s,`:armstate`)) (frees(concl th)) && is_forall(concl th) &&
      can (find_term ((=) `num_of_bytelist dk`)) (concl th) &&
      can (find_term ((=) `1024`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

let KD4_UD_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 1024 ==> abs(ival((UD:num->int16) m)) <= &3328`
  (LABEL_TAC "udbound") THENL
   [X_GEN_TAC `m':num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(num_of_bytelist ct DIV 2 EXP (11 * m')) MOD 2 EXP 11 < 2048`
    MP_TAC THENL [REWRITE_TAC[ARITH_RULE `2048 = 2 EXP 11`; MOD_LT_EQ] THEN
                  CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    SPEC_TAC(`(num_of_bytelist ct DIV 2 EXP (11 * m')) MOD 2 EXP 11`,
             `f:num`) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `ival(word((3329 * f + 1024) DIV 2048):int16) =
                  &((3329 * f + 1024) DIV 2048)` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_WORD_SMALL THEN UNDISCH_TAC `f < 2048` THEN ARITH_TAC;
      REWRITE_TAC[INT_ABS_NUM; INT_OF_NUM_LE] THEN
      UNDISCH_TAC `f < 2048` THEN ARITH_TAC];
    ALL_TAC];;

let KD4_SS_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 1024 ==> abs(ival((SS:num->int16) m)) <= &2 pow 12`
  (LABEL_TAC "ssbound") THENL
   [X_GEN_TAC `m':num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(num_of_bytelist dk DIV 2 EXP (12 * m')) MOD 2 EXP 12 < 4096`
    MP_TAC THENL [REWRITE_TAC[ARITH_RULE `4096 = 2 EXP 12`; MOD_LT_EQ] THEN
                  CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    SPEC_TAC(`(num_of_bytelist dk DIV 2 EXP (12 * m')) MOD 2 EXP 12`,
             `f:num`) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `ival(word f:int16) = &f` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_WORD_SMALL THEN UNDISCH_TAC `f < 4096` THEN ARITH_TAC;
      REWRITE_TAC[INT_ABS_NUM; INT_OF_NUM_POW; INT_OF_NUM_LE] THEN
      UNDISCH_TAC `f < 4096` THEN ARITH_TAC];
    ALL_TAC];;

let KD4_UH_TAC b s =
  let st = mk_var(s,`:armstate`) and srct = `UD:num->int16` in
  INDCPA_GHOST_TAC "UH" (b + 2048) 1024 s THEN
  SUBGOAL_THEN
   `!j i. j < 4 /\ i < 256
          ==> (ival((UH:num->int16)(256 * j + i)) ==
               forward_ntt (\n. ival((UD:num->int16)(256 * j + n))) i)
              (mod &3329) /\
              abs(ival(UH(256 * j + i))) <= &23594`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN INDCPA_UNGHOST_TAC "UH" THEN
    INDCPA_POST_TAC st "forward_ntt" srct (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(INT_ARITH `abs(x:int) <= &3328 ==> abs x <= &8191`) THEN
      REMOVE_THEN "udbound" (fun th -> LABEL_TAC "udbound" th THEN
        MATCH_MP_TAC th) THEN INDCPA_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    INDCPA_DROP_POST_TAC st "forward_ntt" srct];;

let KD4_BASEMUL_DEFS =
  [basemul4_even; basemul4_odd; pmul_acc4; pmull_acc4; pmull];;

let KD4_WP_GOAL = `!p. p < 128
       ==> (ival((WP:num->int16)(2 * p)) ==
            &169 *
            ((ival((SS:num->int16)(768 + 2 * p + 1)) *
              ival((MC:num->int16)(384 + p)) +
              ival(SS(768 + 2 * p)) * ival((UH:num->int16)(768 + 2 * p))) +
             (ival(SS(512 + 2 * p + 1)) * ival(MC(256 + p)) +
              ival(SS(512 + 2 * p)) * ival(UH(512 + 2 * p))) +
             (ival(SS(256 + 2 * p + 1)) * ival(MC(128 + p)) +
              ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p))) +
             (ival(SS(2 * p + 1)) * ival(MC p) +
              ival(SS(2 * p)) * ival(UH(2 * p))))) (mod &3329) /\
           (ival(WP(2 * p + 1)) ==
            &169 *
            ((ival(SS(768 + 2 * p + 1)) * ival(UH(768 + 2 * p)) +
              ival(SS(768 + 2 * p)) * ival(UH(768 + 2 * p + 1))) +
             (ival(SS(512 + 2 * p + 1)) * ival(UH(512 + 2 * p)) +
              ival(SS(512 + 2 * p)) * ival(UH(512 + 2 * p + 1))) +
             (ival(SS(256 + 2 * p + 1)) * ival(UH(256 + 2 * p)) +
              ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p + 1))) +
             (ival(SS(2 * p + 1)) * ival(UH(2 * p)) +
              ival(SS(2 * p)) * ival(UH(2 * p + 1))))) (mod &3329)`;;

let KD4_WP_TAC b s =
  INDCPA_GHOST_TAC "WP" (b + 6720) 256 s THEN
  SUBGOAL_THEN KD4_WP_GOAL ASSUME_TAC THENL
   [INDCPA_BASEMULK_ROW_TAC 4 "WP" (b + 6720) "ssbound" [] KD4_BASEMUL_DEFS;
    ALL_TAC];;

let KD4_TOMSG_POST_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && mem `VR:num->int16` (frees(concl th)) &&
    INDCPA_HAS_CONST "nsum" (concl th))) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC VAL_LT_OF_IVAL_REM THEN
    EXISTS_TAC `ival(word_sub ((VD:num->int16) i) ((WI:num->int16) i))` THEN
    ASM_SIMP_TAC[];
    DISCH_TAC];;

let KD4_DEC_FINAL_TAC =
  MP_TAC(SPECL [`dk:byte list`; `ct:byte list`; `UD:num->int16`;
                `VD:num->int16`; `SS:num->int16`; `UH:num->int16`;
                `MC:num->int16`; `WP:num->int16`; `WI:num->int16`;
                `VR:num->int16`] KPKE_DECRYPT_K4_RESULT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
           REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
    SIMP_TAC[]];;

(*** The inlined loop of poly_sub, v -= the inverse NTT of the product ***)

let KD4_SUB = INLINE_PTR_LOOP "mlkem_native_libmlkem_gcc12_O2_mono_mc"
  KD4_EXEC "sub" "mlkem1024_dec_loop6" "mlkem1024_dec_loop6_exit"
  "X23" "X0" "X27";;

(*** The callees of the inlined indcpa_dec ***)

let KD4_SUB_TAC th =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,KD4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,th);;

let LOCAL_FROMBYTES_TAC =
  KD4_SUB_TAC
   MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_NTT_TAC =
  KD4_SUB_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_MULCACHE_TAC =
  KD4_SUB_TAC
   MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_BASEMUL_TAC =
  KD4_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_INVNTT_TAC =
  KD4_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REDUCE_TAC =
  KD4_SUB_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_TOMSG_TAC =
  KD4_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let KD4_SP n = Printf.sprintf "word_add stackpointer (word %d)" n;;

(*** The lemma, for the two values of b ***)

let KD4_DEC_GOAL b = parse_term(Printf.sprintf
 "!dk ct sk c mf ea el ev pc stackpointer x25 x26 x27 x28.
    memset_contract mf ea el ev /\\
    aligned 4096 (word pc:int64) /\\ pc + libmlkem_size <= 2 EXP 64 /\\
    aligned 16 stackpointer /\\ LENGTH dk = 1536 /\\ LENGTH ct = 1568 /\\
    nonoverlapping (c,1568) (word pc,libmlkem_size) /\\
    nonoverlapping (sk,1536) (word pc,libmlkem_size) /\\
    ALLPAIRS nonoverlapping
     [(word_add stackpointer (word %d),7840);
      (word_add stackpointer (word 22848),16);
      (word_add stackpointer (word 22912),32);
      (word_add stackpointer (word 22960),8);
      (word_add stackpointer (word 22976),8)]
     [(c,1568); (sk,1536); (word pc,libmlkem_size);
      (word(pc + got_memset),8); (ea,el)]
    ==> ensures arm
         (\\s. aligned_bytes_loaded s (word pc)
                mlkem_native_libmlkem_gcc12_O2_mono_mc /\\
              read PC s = word (pc + mlkem1024_dec_in_indcpa_dec) /\\
              read SP s = word_add stackpointer (word 22864) /\\
              read X0 s = c /\\
              read X19 s = word_add stackpointer (word %d) /\\
              read X21 s = sk /\\
              read X25 s = x25 /\\ read X26 s = x26 /\\
              read X27 s = x27 /\\ read X28 s = x28 /\\
              read (memory :> bytes64(word_add stackpointer (word 22968))) s =
              c /\\
              read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
              read (memory :> bytes(ea,el)) s = ev /\\
              read (memory :> bytes(c,1568)) s = num_of_bytelist ct /\\
              read (memory :> bytes(sk,1536)) s = num_of_bytelist dk)
         (\\s. read PC s = word (pc + mlkem1024_dec_in_indcpa_dec_end) /\\
              read X20 s = word_add stackpointer (word %d) /\\
              read X26 s = word_add sk (word 1536) /\\
              read (memory :> bytes64(word_add stackpointer (word 22912))) s =
              x25 /\\
              read (memory :> bytes64(word_add stackpointer (word 22920))) s =
              x26 /\\
              read (memory :> bytes64(word_add stackpointer (word 22928))) s =
              x27 /\\
              read (memory :> bytes64(word_add stackpointer (word 22936))) s =
              x28 /\\
              read (memory :> bytes64(word_add stackpointer (word 22976))) s =
              c /\\
              read (memory :> bytes(word_add stackpointer (word %d),32)) s =
              num_of_bytelist(kpke_decrypt mlkem1024 dk ct))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
          MAYCHANGE [X20; X22; X23; X24; X25; X26; X27; X28; X30] ,,
          MAYCHANGE [memory :> bytes(word_add stackpointer (word %d),7840);
                     memory :> bytes(word_add stackpointer (word 22848),16);
                     memory :> bytes(word_add stackpointer (word 22912),32);
                     memory :> bytes(word_add stackpointer (word 22960),8);
                     memory :> bytes(word_add stackpointer (word 22976),8)])"
  b b (b + 7808) (b + 7808) b);;

let KD4_DEC_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`dk:byte list`; `ct:byte list`; `sk:int64`; `c:int64`; `mf:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`; `stackpointer:int64`;
    `x25:int64`; `x26:int64`; `x27:int64`; `x28:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; ALLPAIRS] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memset:num`] WORD_ADD]);;

(*** One polynomial of u: the head of the outer loop, the decompression
     and the increments, k0 the first step ***)

let KD4_D11_STEP_TAC j k0 =
  let n = Printf.sprintf "(ctt DIV 2 EXP %d) MOD 2 EXP 2816" (2816 * j) in
  ARM_STEPS_TAC KD4_EXEC (k0--(k0+2)) THEN KD4_TIDY_TAC THEN
  USE_THEN "H_D11" (fun th -> KD4_SUB_TAC th
   [`read events s`; `read X1 s`; `read X7 s`; parse_term n; `pc:num`]
   (k0+3)) THEN
  ARM_STEPS_TAC KD4_EXEC ((k0+4)--(k0+8)) THEN KD4_TIDY_TAC;;

let KD4_DEC_TAC b =
  let st n = "s"^string_of_int n in
  let sp n = KD4_SP n in
  ENSURES_INIT_TAC "s0" THEN KD4_CT_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP KD4_CONSTANTS) THEN
  POLYVEC_INLINE_SPLIT_TAC KD4_DU_SPLIT `c:int64` 4 THEN
  ABBREV_TAC `ctt = num_of_bytelist ct MOD 2 EXP 11264` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  POLYVEC_INLINE_SPLIT_TAC POLYVEC_FROMBYTES_SPLIT_GEN `sk:int64` 4 THEN

  (*** The decompressed u, the decompressed v and the decoded s ***)

  ARM_STEPS_TAC KD4_EXEC (1--1) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (2--11) THEN
  MAP_EVERY (fun j -> KD4_D11_STEP_TAC j (12 + 9 * j)) (0--3) THEN
  POLYVEC_INLINE_JOIN_TAC 4
   [KD4_DU_FIELD; ADD_CLAUSES; ARITH_RULE `2048 = 2 EXP 11`]
   (parse_term(Printf.sprintf
     "!i. i < 1024
          ==> read(memory :> bytes16(word_add (%s:int64) (word(2 * i))))
               (s47:armstate) =
              word((3329 * (ctt DIV 2 EXP (11 * i)) MOD 2 EXP 11 + 1024) DIV
                   2048)" (sp(b + 2048)))) THEN
  KD4_UD_TAC b (st 47) THEN
  ARM_STEPS_TAC KD4_EXEC (48--52) THEN
  ARM_STEPS_TAC KD4_EXEC (53--53) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (54--58) THEN
  USE_THEN "H_D5" (fun th -> KD4_SUB_TAC th
   [`read events s`; `read X2 s`; `read X8 s`;
    `num_of_bytelist(mlkem_slice 1408 160 ct)`; `pc:num`] 59) THEN
  KD4_VD_TAC b (st 59) THEN
  ARM_STEPS_TAC KD4_EXEC (60--62) THEN
  MAP_EVERY (fun q ->
    let k0 = 63 + 8 * q in
    ARM_STEPS_TAC KD4_EXEC (k0--(k0+3)) THEN KD4_TIDY_TAC THEN
    LOCAL_FROMBYTES_TAC
     [`read X0 s`; `read X1 s`;
      parse_term(Printf.sprintf
        "(num_of_bytelist (dk:byte list) DIV 2 EXP %d) MOD 2 EXP 3072"
        (3072 * q));
      `pc:num`; `read X30 s`] (k0+4) THEN
    ARM_STEPS_TAC KD4_EXEC ((k0+5)--(k0+7)) THEN KD4_TIDY_TAC) (0--3) THEN
  POLYVEC_INLINE_JOIN_TAC 4
   [POLYVEC_FROMBYTES_FIELD_GEN; ADD_CLAUSES; ARITH_RULE `4096 = 2 EXP 12`]
   (PV_FROMBYTES_POST 4 (sp b) "num_of_bytelist dk" (st 94)) THEN
  KD4_SS_TAC b (st 94) THEN

  (*** The NTT of u and its multiplication cache, the product with s ***)

  KD4_UD_BOUND_TAC THEN
  POLYVEC_GHOST_SPLIT_TAC "UD" (b + 2048) 4 (st 94) THEN
  ARM_STEPS_TAC KD4_EXEC (95--98) THEN
  LOCAL_NTT_TAC [`read X0 s`; `UD:num->int16`; `pc:num`; `read X30 s`] 99 THEN
  ARM_STEPS_TAC KD4_EXEC (100--104) THEN
  LOCAL_NTT_TAC [`read X0 s`; `\i. (UD:num->int16)(256 + i)`; `pc:num`;
                 `read X30 s`] 105 THEN
  ARM_STEPS_TAC KD4_EXEC (106--107) THEN
  LOCAL_NTT_TAC [`read X0 s`; `\i. (UD:num->int16)(512 + i)`; `pc:num`;
                 `read X30 s`] 108 THEN
  ARM_STEPS_TAC KD4_EXEC (109--110) THEN
  LOCAL_NTT_TAC [`read X0 s`; `\i. (UD:num->int16)(768 + i)`; `pc:num`;
                 `read X30 s`] 111 THEN
  POLYVEC_INLINE_JOIN_TAC 4 []
   (PV_NTT_POST 4 (sp(b + 2048)) "UD" (st 111)) THEN
  KD4_UH_TAC b (st 111) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "UD" 1024 THEN
  POLYVEC_GHOST_SPLIT_TAC "UH" (b + 2048) 4 (st 111) THEN
  MAP_EVERY (fun q ->
    let k0 = 112 + 9 * q in
    let x = if q = 0 then `UH:num->int16` else
            parse_term(Printf.sprintf "\\i. (UH:num->int16)(%d + i)"
                                      (256 * q)) in
    ARM_STEPS_TAC KD4_EXEC (k0--(k0+2)) THEN KD4_TIDY_TAC THEN
    LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; x; `pc:num`;
                        `read X30 s`] (k0+3) THEN
    ARM_STEPS_TAC KD4_EXEC ((k0+4)--(k0+8)) THEN KD4_TIDY_TAC) (0--3) THEN
  POLYVEC_INLINE_JOIN_TAC 4 []
   (PV_MULCACHE_POST 4 (sp(b + 5696)) "UH" (st 147)) THEN
  INDCPA_MULCACHE_TAC "MC" (b + 5696) 4 "UH" (st 147) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "UH" 1024 THEN
  ARM_STEPS_TAC KD4_EXEC (148--154) THEN
  INDCPA_BASEMULK_PRE_TAC 4 (b,"SS",0) (b + 2048,"UH") (b + 5696,"MC")
    (st 154) THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 4 ("SS",0) "UH" "MC") 155 THEN
  INDCPA_BASEMULK_DROP_PRE_TAC 4 (b,"SS",0) (b + 2048,"UH")
    (b + 5696,"MC") THEN
  KD4_SS_BOUND_TAC THEN KD4_WP_TAC b (st 155) THEN

  (*** The inverse NTT, the subtraction from v, the reduction ***)

  ARM_STEPS_TAC KD4_EXEC (156--157) THEN
  LOCAL_INVNTT_TAC
   [`read X0 s`; `WP:num->int16`; `pc:num`; `read SP s`; `read X30 s`]
   158 THEN
  INDCPA_INVNTT1_TAC "WI" (b + 6720) "WP" (st 158) THEN
  ARM_STEPS_TAC KD4_EXEC (159--159) THEN
  USE_THEN "H_SUB" (fun th -> KD4_SUB_TAC th
   [`read events s`; `read X23 s`; `read X0 s`; `VD:num->int16`;
    `WI:num->int16`; `pc:num`] 160) THEN
  ARM_STEPS_TAC KD4_EXEC (161--164) THEN
  LOCAL_REDUCE_TAC
   [`read X0 s`; `\i. word_sub ((VD:num->int16) i) ((WI:num->int16) i)`;
    `pc:num`; `read X30 s`] 165 THEN
  INDCPA_REDUCE_TAC "VR" (b + 7232) 256
    "word_sub ((VD:num->int16) i) ((WI:num->int16) i)" (st 165) THEN

  (*** The message ***)

  ARM_STEPS_TAC KD4_EXEC (166--168) THEN
  LOCAL_TOMSG_TAC
   [`read X0 s`; `read X1 s`; `VR:num->int16`; `pc:num`; `read X30 s`]
   169 THEN
  KD4_TOMSG_POST_TAC THEN

  (*** Zeroing the buffers ***)

  INDCPA_MEMSET_LABEL_TAC THEN
  INDCPA_MEMSETS_TAC KD4_EXEC
   [170,173; 179,182; 188,191; 197,200; 206,209] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KD4_DEC_FINAL_TAC;;

let KD4_DEC_LEMMA b = prove
 (KD4_DEC_GOAL b,
  KD4_DEC_INTRO_TAC THEN
  X_CHOOSE_THEN `fd11:int64->int64->num->(uarch_event)list`
    (LABEL_TAC "H_D11") KD4_D11 THEN
  X_CHOOSE_THEN `fd5:int64->int64->num->(uarch_event)list`
    (LABEL_TAC "H_D5") KD4_D5 THEN
  X_CHOOSE_THEN `fs:int64->int64->num->(uarch_event)list`
    (LABEL_TAC "H_SUB") KD4_SUB THEN
  KD4_DEC_TAC b);;

let KD4_DEC_A = KD4_DEC_LEMMA 23008;;
let KD4_DEC_U = KD4_DEC_LEMMA 22992;;

(* ------------------------------------------------------------------------- *)
(* The lengths of the results of K-PKE for ML-KEM-1024, the input check of   *)
(* FIPS 203 in terms of the result of mlkem1024_check_sk, and the address of *)
(* the buffers, which are aligned to 32 bytes within the stack frame.        *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_LENGTH_1024 = prove
 (`!ek m r. LENGTH(kpke_encrypt mlkem1024 ek m r) = 1568`,
  REWRITE_TAC[mlkem1024; KPKE_ENCRYPT_LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let KPKE_DECRYPT_LENGTH_1024 = prove
 (`!dk c. LENGTH(kpke_decrypt mlkem1024 dk c) = 32`,
  REWRITE_TAC[mlkem1024; KPKE_DECRYPT_LENGTH]);;

let KD4_CHECK = prove
 (`!dk c. LENGTH dk = 3168 /\ LENGTH c = 1568
          ==> (mlkem_decaps_check mlkem1024 dk c <=>
               num_of_bytelist(mlkem_slice 3104 32 dk) =
               num_of_bytelist(sha3_256(mlkem_slice 1536 1568 dk)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem1024; mlkem_decaps_check] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[mlkem_h] THEN
  CONV_TAC(LAND_CONV SYM_CONV) THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC NUM_OF_BYTELIST_INJ THEN
  REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ; LENGTH_SHA3_256]);;

let KD4_ALIGNED_16_32 = prove
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

(*** SP + 159 rounded down, SP being stackpointer + 22864 ***)

let KD4_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 23023)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 23008 else 22992))`,
  REWRITE_TAC[KD4_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let KD4_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KD4_BUFFER_ADDRESS))
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The callees, the slices of the decapsulation key, and the failure of the  *)
(* check of the key, after which the function only zeroes its buffers.       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CHECK_SK_TAC =
  KD4_SUB_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_INDCPA_DEC_TAC b =
  KD4_SUB_TAC (if b = 23008 then KD4_DEC_A else KD4_DEC_U);;

let LOCAL_SHA3_512_TAC =
  KD4_SUB_TAC MLKEM_NATIVE_SHA3_512_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_INDCPA_ENC_TAC =
  KD4_SUB_TAC
   MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_SHAKE256_TAC =
  KD4_SUB_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let KD4_SK_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(sk,3168)) s = num_of_bytelist dk`) (concl th)
    then
      let s = rand(lhand(concl th)) in
      MAP_EVERY (fun (k,n) ->
        MP_TAC(SPECL [`sk:int64`; `dk:byte list`; mk_small_numeral k;
                      mk_small_numeral n; s] READ_MEMORY_BYTES_SLICE) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC)
       [0,1536; 1536,1568; 3104,32; 3136,32]
    else NO_TAC);;

let KD4_CHECK_TAC =
  LOCAL_CHECK_SK_TAC
   [`read X0 s`; `mlkem_slice 1536 1568 (dk:byte list)`;
    `num_of_bytelist(mlkem_slice 3104 32 (dk:byte list))`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 19;;

let KD4_FAIL_TAC =
  ARM_STEPS_TAC KD4_EXEC (20--30) THEN
  LIBC_PLT_TAC KD4_EXEC 30 THEN
  LIBC_CALL_TAC "H_MEMSET" KD4_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 35 THEN
  ARM_STEPS_TAC KD4_EXEC (36--41) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (42--55) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The values computed: m', G of m' and h, K' and r', the reencryption c' of *)
(* m', z, the result of J, and whether c' is the ciphertext, as for gcc 12   *)
(* -O2. The buffers of the function are at b + 4096 (c' and then z and the   *)
(* ciphertext), b + 7744 (K' and r') and b + 7808 (m' and h), over and after *)
(* those of the inlined indcpa_dec. The invariant of the comparison loop at  *)
(* iteration i states that the OR accumulator Q4 is zero if and only if the  *)
(* first 16 * i bytes of the ciphertext and of c' are equal (the code also   *)
(* keeps an XOR accumulator in Q0, whose value does not matter), with the    *)
(* pointer into the ciphertext at SP + 112, and the invariant of the         *)
(* conditional move at iteration i that the first i bytes at ss are those of *)
(* K' if the ciphertexts are equal and those of the result of J otherwise,   *)
(* and the others still those of the result of J. The frame has the facts    *)
(* needed after both loops, with X25 to X28 saved by the inlined indcpa_dec. *)
(* ------------------------------------------------------------------------- *)

let KD4_MP = `kpke_decrypt mlkem1024 (mlkem_slice 0 1536 dk) c`;;

let KD4_GG =
 `sha3_512 (APPEND (kpke_decrypt mlkem1024 (mlkem_slice 0 1536 dk) c)
                  (mlkem_slice 3104 32 dk))`;;

let KD4_KP = mk_comb(`mlkem_slice 0 32`,KD4_GG);;

let KD4_RR = mk_comb(`mlkem_slice 32 32`,KD4_GG);;

let KD4_CP = list_mk_comb(`kpke_encrypt mlkem1024`,
  [`mlkem_slice 1536 1568 (dk:byte list)`; KD4_MP; KD4_RR]);;

let KD4_ZZ = `mlkem_slice 3136 32 (dk:byte list)`;;

let KD4_KB = `list_of_seq (shake256 (APPEND (mlkem_slice 3136 32 dk) c)) 32`;;

let KD4_EQ = mk_eq(`num_of_bytelist c`,mk_comb(`num_of_bytelist`,KD4_CP));;

let KD4_SUBST tm =
  subst [mk_comb(`num_of_bytelist`,KD4_CP),`CP:num`;
         mk_comb(`num_of_bytelist`,KD4_KP),`KP:num`;
         mk_comb(`num_of_bytelist`,KD4_KB),`KB:num`;
         mk_comb(`num_of_bytelist`,KD4_ZZ),`ZZ:num`;
         KD4_EQ,`EQ:bool`] tm;;

let KD4_FRAME b = KD4_SUBST(parse_term(Printf.sprintf
 "read SP s = word_add stackpointer (word 22864) /\\
  read X19 s = word_add stackpointer (word %d) /\\
  read X20 s = word_add stackpointer (word %d) /\\
  read X22 s = word_add stackpointer (word %d) /\\
  read X24 s = word 0 /\\
  read (memory :> bytes64 (word_add stackpointer (word 22864))) s =
  x19_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22872))) s =
  x20_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22880))) s =
  x21_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22888))) s =
  x22_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22896))) s =
  x23_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22904))) s =
  x24_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22912))) s =
  x25_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22920))) s =
  x26_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22928))) s =
  x27_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22936))) s =
  x28_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 22944))) s =
  returnaddress /\\
  read (memory :> bytes64 (word_add stackpointer (word 22968))) s = ct /\\
  read (memory :> bytes64 (word_add stackpointer (word 22984))) s = ss /\\
  read (memory :> bytes64 (word_add stackpointer (word 30888))) s = canary /\\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard)))
   s = guard /\\
  read (memory :> bytes64 guard) s = canary /\\
  read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\\
  read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev /\\
  read (memory :> bytes(word_add stackpointer (word %d),32)) s = KP"
  (b + 4096) (b + 7808) (b + 7744) (b + 7744)));;

let KD4_INV b = KD4_SUBST(parse_term(Printf.sprintf
 "\\i s. read X0 s = word_add stackpointer (word(%d + 16 * i)) /\\
        read X1 s = word_add stackpointer (word %d) /\\
        read (memory :> bytes64 (word_add stackpointer (word 22976))) s =
        word_add ct (word(16 * i)) /\\
        read X21 s = sk /\\
        (read Q4 s = word 0 <=>
         num_of_bytelist c MOD 2 EXP (128 * i) = CP MOD 2 EXP (128 * i)) /\\
        read (memory :> bytes(ct,1568)) s = num_of_bytelist c /\\
        read (memory :> bytes(word_add stackpointer (word %d),1568)) s = CP /\\
        read (memory :> bytes128 (word_add sk (word 3136))) s =
        word(ZZ MOD 2 EXP 128) /\\
        read (memory :> bytes128 (word_add sk (word 3152))) s =
        word(ZZ DIV 2 EXP 128) /\\ FRAME"
  (b + 4096) (b + 5664) (b + 4096)));;

let KD4_INV_FRAME b =
  let inv = KD4_INV b in
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [KD4_FRAME b,`FRAME:bool`] bod);;

let KD4_CMOV_INV b = KD4_SUBST(parse_term(Printf.sprintf
 "\\i s. read X0 s = word(i + 1) /\\
        read X1 s = word_sub ss (word 1) /\\
        read X21 s = (if EQ then word 0 else word 4294967041) /\\
        read (memory :> bytes(ss,i)) s =
        (if EQ then KP else KB) MOD 2 EXP (8 * i) /\\
        read (memory :> bytes(word_add ss (word i),32 - i)) s =
        KB DIV 2 EXP (8 * i) /\\ FRAME"));;

let KD4_CMOV_INV_FRAME b =
  let inv = KD4_CMOV_INV b in
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [KD4_FRAME b,`FRAME:bool`] bod);;

(* ------------------------------------------------------------------------- *)
(* From the start to the comparison loop: the check of the key, the          *)
(* decryption (the lemma above), G of m' and h, and the reencryption.        *)
(* ------------------------------------------------------------------------- *)

let KD4_G_INPUT_TAC b s =
  let st = mk_var(s,`:armstate`) in
  SUBGOAL_THEN
   (subst [st,`s:armstate`; KEM_SP(b + 7808),`a:int64`;
           KD4_MP,`mm:byte list`]
     `read (memory :> bytes(a,64)) s =
      num_of_bytelist(APPEND (mm:byte list) (mlkem_slice 3104 32 dk))`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; KPKE_DECRYPT_LENGTH_1024];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (subst [KD4_MP,`mm:byte list`]
     `LENGTH(APPEND (mm:byte list) (mlkem_slice 3104 32 dk)) = 64`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; KPKE_DECRYPT_LENGTH_1024] THEN ARITH_TAC;
    ALL_TAC];;

let KD4_KR_TAC b s =
  let st = mk_var(s,`:armstate`) and a = KEM_SP(b + 7744) in
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [a,`a:int64`; st,`s:armstate`]
         `read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 x)`))
         (concl th)
    then
      MP_TAC(SPECL [a; KD4_GG; `0`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      MP_TAC(SPECL [a; KD4_GG; `32`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      ASM_REWRITE_TAC[LENGTH_SHA3_512] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      REPEAT DISCH_TAC
    else NO_TAC) THEN
  SUBGOAL_THEN
   (mk_conj(mk_eq(mk_comb(`LENGTH:byte list->num`,KD4_KP),`32`),
            mk_eq(mk_comb(`LENGTH:byte list->num`,KD4_RR),`32`)))
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC];;

let KD4_PART1_TAC b =
  let st n = "s"^string_of_int n in
  ENSURES_INIT_TAC "s0" THEN KD4_SK_TAC THEN
  KEM_HALVES_TAC `word_add sk (word 3104):int64` THEN
  KEM_HALVES_TAC `word_add sk (word 3136):int64` THEN
  ARM_STEPS_TAC KD4_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (4--10) THEN KD4_BUFFER_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (11--18) THEN INLINE_GOT_TAC THEN
  KD4_CHECK_TAC THEN

  (*** The decryption, G and the reencryption ***)

  ARM_STEPS_TAC KD4_EXEC (20--21) THEN INLINE_GOT_TAC THEN
  LOCAL_INDCPA_DEC_TAC b
   [`mlkem_slice 0 1536 (dk:byte list)`; `c:byte list`; `read X21 s`;
    `read X0 s`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `stackpointer:int64`; `read X25 s`; `read X26 s`; `read X27 s`;
    `read X28 s`] 22 THEN
  ARM_STEPS_TAC KD4_EXEC (23--32) THEN
  KEM_JOIN_TAC (KEM_SP(b + 7840)) `mlkem_slice 3104 32 (dk:byte list)`
    (st 32) THEN
  KD4_G_INPUT_TAC b (st 32) THEN INLINE_GOT_TAC THEN
  LOCAL_SHA3_512_TAC
   [`read X0 s`; `read X1 s`;
    mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,KD4_MP),
            `mlkem_slice 3104 32 (dk:byte list)`);
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 33 THEN
  KD4_KR_TAC b (st 33) THEN
  ARM_STEPS_TAC KD4_EXEC (34--38) THEN INLINE_GOT_TAC THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,KD4_MP),`32`))
  ASSUME_TAC THENL [REWRITE_TAC[KPKE_DECRYPT_LENGTH_1024]; ALL_TAC] THEN
  LOCAL_INDCPA_ENC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `mlkem_slice 1536 1568 (dk:byte list)`; KD4_MP; KD4_RR;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 39 THEN
  ARM_STEPS_TAC KD4_EXEC (40--45) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; MOD_1; WORD_ADD_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* One iteration of the comparison, with the loop test.                      *)
(* ------------------------------------------------------------------------- *)

let KD4_TEST = prove
 (`!sp:int64 b i.
        b <= 23008 /\ i < 98
        ==> (val(word_sub (word_add sp (word(b + 5664)))
                          (word_add (word_add sp (word((b + 4096) + 16 * i)))
                                    (word 16))) = 0 <=>
             ~(i + 1 < 98))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
              WORD_RULE `word_sub (word_add a x) (word_add a y):int64 =
                         word_sub x y`] THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `b + 5664 < 2 EXP 64 /\ ((b + 4096) + 16 * i) + 16 < 2 EXP 64`
   (fun th -> SIMP_TAC[th; MOD_LT]) THENL
   [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let KD4_CHUNK_TAC a v =
  let bth = MP (ARITH_RULE `i < 98 ==> 16 * i + 16 <= 1568`)
               (ASSUME `i < 98`) in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),Comb(_,Comb(Const("bytes",_),aa))),
                     s)),vv)
        when aa = mk_pair(a,`1568`) && vv = v ->
          let lth = SPECL [a; `1568`; `i:num`; v; s] KEM_BYTES128 in
          ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                      (MP lth (CONJ th bth)))
    | _ -> NO_TAC);;

let KD4_BODY_TAC b =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `q4:int128` `read Q4` THEN
  GHOST_INTRO_TAC `q0:int128` `read Q0` THEN
  ENSURES_INIT_TAC "s0" THEN
  KD4_CHUNK_TAC `ct:int64` `num_of_bytelist c` THEN
  KD4_CHUNK_TAC (KEM_SP(b + 4096)) (mk_comb(`num_of_bytelist`,KD4_CP)) THEN
  ARM_STEPS_TAC KD4_EXEC (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
     (MP (SPECL [`stackpointer:int64`; mk_small_numeral b; `i:num`]
                KD4_TEST)
         (CONJ (ARITH_RULE(mk_binop `(<=):num->num->bool`
                            (mk_small_numeral b) `23008`))
               (ASSUME `i < 98`)))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `i + 1 < 98` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ASM_REWRITE_TAC[KEM_OR_STEP; KEM_MOD_STEP] THEN
    REWRITE_TAC[CONJ_ACI; EQ_SYM_EQ]];;

(* ------------------------------------------------------------------------- *)
(* From the comparison loop to the conditional move: the result of the       *)
(* comparison as a mask of 0 or 255 (from the OR and the XOR accumulators,   *)
(* whose final value does not matter), J of z and the ciphertext copied      *)
(* after z with memcpy, and the mask for the bytes.                          *)
(* ------------------------------------------------------------------------- *)

let KD4_DONE_TAC =
  SUBGOAL_THEN (mk_iff(`q4:int128 = word 0`,KD4_EQ)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) && lhand(concl th) = `q4:int128 = word 0`
      then REWRITE_TAC[th] else NO_TAC) THEN
    MP_TAC(ISPEC `c:byte list` NUM_OF_BYTELIST_BOUND) THEN
    MP_TAC(ISPEC KD4_CP NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[KPKE_ENCRYPT_LENGTH_1024] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC];;

let KD4_MASK_TAC s =
  let x21 = mk_comb(`read X21`,mk_var(s,`:armstate`)) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = x21 then
      let e = rand c in
      let eth = BITBLAST_RULE
        (mk_eq(e,`if q4:int128 = word 0 then word 0:int64 else word 255`)) in
      ASSUME_TAC(TRANS th eth)
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = x21 then
      FIRST_ASSUM(fun th' ->
        if is_iff(concl th') && lhand(concl th') = `q4:int128 = word 0`
        then ASSUME_TAC(REWRITE_RULE[th'] th) else NO_TAC)
    else NO_TAC);;

let KD4_J_INPUT_TAC b s =
  let st = mk_var(s,`:armstate`) in
  SUBGOAL_THEN
   (subst [st,`s:armstate`; KEM_SP(b + 4096),`a:int64`]
     `read (memory :> bytes(a,1600)) s =
      num_of_bytelist(APPEND (mlkem_slice 3136 32 (dk:byte list)) c)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1600 = 32 + 1568`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(APPEND (mlkem_slice 3136 32 (dk:byte list)) c) = 1600`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC];;

let KD4_EXIT_A_TAC b =
  let st n = "s"^string_of_int n in
  GHOST_INTRO_TAC `q4:int128` `read Q4` THEN
  GHOST_INTRO_TAC `q0:int128` `read Q0` THEN
  ENSURES_INIT_TAC "s0" THEN KD4_DONE_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KD4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[]) (1--26) THEN
  KD4_MASK_TAC (st 26) THEN
  ARM_STEPS_TAC KD4_EXEC (27--31) THEN
  KEM_JOIN_TAC (KEM_SP(b + 4096)) KD4_ZZ (st 31) THEN
  LIBC_PLT_TAC KD4_EXEC 31 THEN
  LIBC_CALL_TAC "H_MEMCPY" KD4_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `num_of_bytelist(c:byte list)`;
    `read X30 s`] 36 THEN
  KD4_J_INPUT_TAC b (st 36) THEN
  ARM_STEPS_TAC KD4_EXEC (37--42) THEN INLINE_GOT_TAC THEN
  LOCAL_SHAKE256_TAC
   [`read X0 s`; `32`; `read X2 s`;
    `APPEND (mlkem_slice 3136 32 (dk:byte list)) c`; `guard:int64`;
    `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 43 THEN
  ARM_STEPS_TAC KD4_EXEC (44--45) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; DIV_1; SUB_0; WORD_ADD_0;
              READ_MEMORY_BYTES_TRIVIAL] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC KD4_EQ THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* One iteration of the conditional move, and the end: the zeroing of the    *)
(* buffers, the stack guard and the result in terms of FIPS 203.             *)
(* ------------------------------------------------------------------------- *)

let KD4_KP_ADDR2 = prove
 (`!sp:int64 a i.
        word_add (word_add (word (i + 1)) (word_add sp (word a)))
                 (word 18446744073709551615) =
        word_add sp (word (a + (i + 1) + 18446744073709551615))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let KD4_CMOV_BODY_TAC b =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [KEM_SP(b + 7744); `32`; mk_comb(`num_of_bytelist`,KD4_KP);
                `i:num`; `s0:armstate`] READ_MEMORY_BYTES8_OF_NUM) THEN
  ASM_REWRITE_TAC[KEM_KP_ADDR; GSYM KD4_KP_ADDR2] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   (KD4_SUBST `read (memory :> bytes(word_add ss (word i),(31 - i) + 1)) s0 =
               KB DIV 2 EXP (8 * i)`)
  MP_TAC THENL
   [SIMP_TAC[ARITH_RULE `i < 32 ==> (31 - i) + 1 = 32 - i`;
             ASSUME `i < 32`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th ->
      let th1,th2 = CONJ_PAIR(MATCH_MP KEM_SPLIT1 th) in
      ASSUME_TAC(ONCE_REWRITE_RULE
       [GSYM(SPECL [`ss:int64`; `i:num`] KEM_SS_ADDR)] th1) THEN
      ASSUME_TAC th2)] THEN
  ARM_STEPS_TAC KD4_EXEC (1--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [KEM_SS_ADDR; MP (SPEC `i:num` KEM_CMOV_TEST) (ASSUME `i < 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `i + 1 < 32` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM WORD_ADD];
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_1] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[KEM_MOD_BYTE] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_CASES_TAC KD4_EQ THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [KEM_VAL_BYTE] THEN
    SPEC_TAC(KD4_SUBST `word((KP DIV 2 EXP (8 * i)) MOD 256):byte`,
             `x:byte`) THEN
    SPEC_TAC(KD4_SUBST `word((KB DIV 2 EXP (8 * i)) MOD 256):byte`,
             `y:byte`) THEN
    REPEAT GEN_TAC THEN AP_TERM_TAC THEN BITBLAST_TAC;
    REWRITE_TAC[ARITH_RULE `32 - (i + 1) = 31 - i`; WORD_ADD; WORD_ADD_ASSOC;
                KEM_DIV_BYTE] THEN
    ASM_REWRITE_TAC[]];;

let KD4_FINAL_TAC =
  REWRITE_TAC[mlkem1024; MLKEM_DECAPS_ALT] THEN
  REWRITE_TAC[GSYM mlkem1024] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN (mk_iff(mk_eq(KD4_CP,`c:byte list`),KD4_EQ)) SUBST1_TAC THENL
   [CONV_TAC(LAND_CONV SYM_CONV) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC NUM_OF_BYTELIST_INJ THEN
    ASM_REWRITE_TAC[KPKE_ENCRYPT_LENGTH_1024];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOD_LT THEN
  W(fun (_,w) -> MP_TAC(ISPEC (rand(lhand w)) NUM_OF_BYTELIST_BOUND)) THEN
  REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let KD4_EXIT_B_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC KD4_EXEC (1--7) THEN
  LIBC_PLT_TAC KD4_EXEC 7 THEN
  LIBC_CALL_TAC "H_MEMSET" KD4_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 12 THEN
  ARM_STEPS_TAC KD4_EXEC (13--18) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (19--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KD4_FINAL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy, as for   *)
(* gcc 12 -O2, with the frame of this code: the 8032 bytes of the function   *)
(* and the 22864 of mlkem1024_indcpa_enc below them. The proof is by cases   *)
(* on whether the stack pointer is a multiple of 32, which gives the address *)
(* b of the buffers, and on the check of the key.                            *)
(* ------------------------------------------------------------------------- *)

let KD4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ss:int64`; `ct:int64`; `sk:int64`; `dk:byte list`; `c:byte list`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 30896 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 30896):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[KD4_CHECK; ASSUME `LENGTH(dk:byte list) = 3168`;
           ASSUME `LENGTH(c:byte list) = 1568`] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28) THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 1536 (dk:byte list)) = 1536 /\
    LENGTH(mlkem_slice 1536 1568 (dk:byte list)) = 1568 /\
    LENGTH(mlkem_slice 3104 32 (dk:byte list)) = 32 /\
    LENGTH(mlkem_slice 3136 32 (dk:byte list)) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE
   [SYM(CONV_RULE NUM_REDUCE_CONV
     (MP (SPECL [`1536`; `32`; `1536`; `1568`; `dk:byte list`]
                MLKEM_SLICE_SLICE)
         (ARITH_RULE `1536 + 32 <= 1568`)))] o
   check (fun th -> is_forall(concl th) &&
                    KEM_HAS_CONST "mlkem_samplentt_terminates"
                     (concl th)));;

let KD4_OK_TAC b =
  ENSURES_WHILE_UP2_TAC `98` `pc + mlkem1024_dec_loop7`
   `pc + mlkem1024_dec_loop7_exit`
   (KD4_INV_FRAME b) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; KD4_PART1_TAC b; KD4_BODY_TAC b;
    ENSURES_WHILE_UP2_TAC `32` `pc + mlkem1024_dec_loop8`
     `pc + mlkem1024_dec_loop8_exit`
     (KD4_CMOV_INV_FRAME b) THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC; KD4_EXIT_A_TAC b; KD4_CMOV_BODY_TAC b; KD4_EXIT_B_TAC]];;

let KD4_BAD_TAC =
  ENSURES_INIT_TAC "s0" THEN KD4_SK_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (4--10) THEN KD4_BUFFER_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (11--18) THEN INLINE_GOT_TAC THEN
  KD4_CHECK_TAC THEN KD4_FAIL_TAC;;

let KD4_CASE_TAC b =
  KEM_LABELS_TAC THEN
  ASM_CASES_TAC
   `num_of_bytelist(mlkem_slice 3104 32 (dk:byte list)) =
    num_of_bytelist(sha3_256(mlkem_slice 1536 1568 dk))` THEN
  ASM_REWRITE_TAC[] THENL [KD4_OK_TAC b; KD4_BAD_TAC];;

let MLKEM_NATIVE_DEC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!ss ct sk (dk:byte list) (c:byte list) guard mf mc ea el ev pc
    stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH dk = 3168 /\ LENGTH c = 1568 /\
        (!i j. i < 4 /\ j < 4
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 3072 32 dk) [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 30896),30896) /\
        nonoverlapping (ct,1568) (word pc,libmlkem_size) /\
        nonoverlapping (sk,3168) (word pc,libmlkem_size) /\
        nonoverlapping (ss,32) (word_sub stackpointer (word 30896),30896) /\
        ALLPAIRS nonoverlapping
         [(ss,32); (word_sub stackpointer (word 30896),30896)]
         [(ct,1568); (sk,3168); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
          (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlkem1024_dec) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ss; ct; sk] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(ct,1568)) s = num_of_bytelist c /\
                  read (memory :> bytes(sk,3168)) s = num_of_bytelist dk)
             (\s. read PC s = returnaddress /\
                  (mlkem_decaps_check mlkem1024 dk c
                   ==> read (memory :> bytes(ss,32)) s =
                       num_of_bytelist
                        (mlkem_decaps_internal mlkem1024 dk c)) /\
                  C_RETURN s =
                  (if mlkem_decaps_check mlkem1024 dk c then word 0
                   else word 0xfffffffb))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ss,32);
                memory :> bytes(word_sub stackpointer (word 30896),30896)])`,
  KD4_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [KD4_CASE_TAC 23008; KD4_CASE_TAC 22992]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset (for mlkem1024_indcpa_enc) and the safety contract for memcpy, as  *)
(* for gcc 12 -O2. The events depend only on the addresses and on the        *)
(* encapsulation key ek in the decapsulation key and the hash h stored with  *)
(* it, through the check of the hash and the reencryption. The buffers are   *)
(* kept at their offset from the stack pointer as a conditional, and the     *)
(* inlined indcpa_dec is a lemma with its events, as for its correctness.    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let KD4_SAFE_B =
 `if aligned 32 (stackpointer:int64) then 23008 else 22992`;;

(*** The addresses in the facts about the state as word_add stackpointer
     (word n), but not in those about events (the trace, its equations
     and memaccess_inbounds), which must stay as the unification of the
     events of the loops has fixed them ***)

let KD4_SAFE_NORMALIZE_TAC =
  let conv =
    REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
    DEPTH_CONV NUM_ADD_CONV
  and is_trace t = type_of t = `:(uarch_event)list` in
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th) &&
       not (can (find_term is_trace) (concl th))
    then CONV_RULE conv th else th);;

(*** In the lemma for the inlined indcpa_dec, without loops, all of them ***)

let KD4_DEC_NORMALIZE_TAC =
  let conv =
    REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
    DEPTH_CONV NUM_ADD_CONV in
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE conv th else th);;

let KD4_SAFE_BUFFER_TAC =
  SUBGOAL_THEN (subst [KD4_SAFE_B,`b:num`]
   `word_and (word_add stackpointer (word 23023))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word b)`)
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC KD4_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

(*** The inlined indcpa_dec with its events ***)

let KD4_DEC_ALLOWED =
  [`pc:num`; `c:int64`; `sk:int64`; `mf:int64`; `stackpointer:int64`];;

let KD4_DEC_SAFE_CALL_TAC name ilist n =
  KD4_DEC_NORMALIZE_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,KD4_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KD4_DEC_ALLOWED); LABEL_TAC name safety_th]);;

let KD4_DEC_SAFE_CALL0_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,KD4_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KD4_DEC_ALLOWED); LABEL_TAC name safety_th]);;

let KD4_DEC_SAFE_CONTENTS r =
  let a = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                          r),`s:armstate`) in
  vsubst [a,`a:int64`]
   `\i. read(memory :> bytes16(word_add a (word(2 * i)))) (s:armstate)`;;

let KD4_DEC_SAFE_BYTES r n =
  let a = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                          r),`s:armstate`) in
  vsubst [a,`a:int64`; mk_small_numeral n,`n:num`]
   `read(memory :> bytes(a,n)) (s:armstate)`;;

(*** The lemma for each value of b, and their combination for the offset
     as a conditional, as the main proof keeps it ***)

let KD4_DEC_SAFE_GOAL_GEN qb hb fb bs = parse_term(Printf.sprintf
 "!mf ea el ev.
     memset_safety_contract mf ea el ev
     ==> exists f_events.
          forall e sk c pc stackpointer x25 x26 x27 x28%s.
            %saligned 4096 (word pc:int64) /\\
            pc + libmlkem_size <= 2 EXP 64 /\\
            aligned 16 stackpointer /\\
            nonoverlapping (c,1568) (word pc,libmlkem_size) /\\
            nonoverlapping (sk,1536) (word pc,libmlkem_size) /\\
            ALLPAIRS nonoverlapping
             [(word_add stackpointer (word %s),7840);
              (word_add stackpointer (word 22848),16);
              (word_add stackpointer (word 22912),32);
              (word_add stackpointer (word 22960),8);
              (word_add stackpointer (word 22976),8)]
             [(c,1568); (sk,1536); (word pc,libmlkem_size);
              (word(pc + got_memset),8); (ea,el)]
            ==> ensures arm
                 (\\s. aligned_bytes_loaded s (word pc)
                        mlkem_native_libmlkem_gcc12_O2_mono_mc /\\
                      read PC s = word (pc + mlkem1024_dec_in_indcpa_dec) /\\
                      read SP s = word_add stackpointer (word 22864) /\\
                      read X0 s = c /\\
                      read X19 s = word_add stackpointer (word %s) /\\
                      read X21 s = sk /\\
                      read X25 s = x25 /\\ read X26 s = x26 /\\
                      read X27 s = x27 /\\ read X28 s = x28 /\\
                      read (memory :> bytes64
                             (word_add stackpointer (word 22968))) s = c /\\
                      read (memory :> bytes64(word(pc + got_memset))) s =
                      mf /\\
                      read (memory :> bytes(ea,el)) s = ev /\\
                      read events s = e)
                 (\\s. read PC s =
                      word (pc + mlkem1024_dec_in_indcpa_dec_end) /\\
                      read X20 s = word_add stackpointer (word(%s + 7808)) /\\
                      read X26 s = word_add sk (word 1536) /\\
                      read (memory :> bytes64
                             (word_add stackpointer (word 22912))) s = x25 /\\
                      read (memory :> bytes64
                             (word_add stackpointer (word 22920))) s = x26 /\\
                      read (memory :> bytes64
                             (word_add stackpointer (word 22928))) s = x27 /\\
                      read (memory :> bytes64
                             (word_add stackpointer (word 22936))) s = x28 /\\
                      read (memory :> bytes64
                             (word_add stackpointer (word 22976))) s = c /\\
                      (exists e2.
                         read events s = APPEND e2 e /\\
                         e2 = f_events sk c mf pc stackpointer%s /\\
                         memaccess_inbounds e2
                          [c,1568; sk,1536;
                           word_add stackpointer (word %s),7840;
                           word_add stackpointer (word 22848),16;
                           word_add stackpointer (word 22912),32;
                           word_add stackpointer (word 22960),24;
                           word(pc + got_memset),8; ea,el;
                           word(pc + mlkem1024_dec_consts),16;
                           word(pc + mlk_poly_invntt_tomont_c_consts),32;
                           word(pc + rodata_mlk_zetas),256]
                          [word_add stackpointer (word %s),7840;
                           word_add stackpointer (word 22848),16;
                           word_add stackpointer (word 22912),32;
                           word_add stackpointer (word 22960),8;
                           word_add stackpointer (word 22976),8]))
                 (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                  MAYCHANGE [X18] ,,
                  MAYCHANGE [X20; X22; X23; X24; X25; X26; X27; X28; X30] ,,
                  MAYCHANGE
                   [memory :> bytes(word_add stackpointer (word %s),7840);
                    memory :> bytes(word_add stackpointer (word 22848),16);
                    memory :> bytes(word_add stackpointer (word 22912),32);
                    memory :> bytes(word_add stackpointer (word 22960),8);
                    memory :> bytes(word_add stackpointer (word 22976),8)])"
  qb hb bs bs bs fb bs bs bs);;

let KD4_DEC_SAFE_GOAL = KD4_DEC_SAFE_GOAL_GEN "" "" "";;

let KD4_DEC_SAFE_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_safety_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC KD4_D11 "H_D11" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC KD4_D5 "H_D5" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_BASEMUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE)
    "H_INVNTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC KD4_SUB "H_SUB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_TOMSG" THEN
  META_EXISTS_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; ALLPAIRS;
              NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
  let e = `e:(uarch_event)list` in
  let x n = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            mk_const("X"^string_of_int n,[])),`s:armstate`) in
  let rest0 = [`pc:num`; `read X30 s`] in
  let call = KD4_DEC_SAFE_CALL_TAC in
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP KD4_CONSTANTS) THEN
  ARM_STEPS_TAC KD4_EXEC (1--1) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (2--11) THEN
  MAP_EVERY (fun j ->
    let k0 = 12 + 9 * j in
    ARM_STEPS_TAC KD4_EXEC (k0--(k0+2)) THEN KD4_TIDY_TAC THEN
    KD4_DEC_SAFE_CALL0_TAC "H_D11"
     [e; x 1; x 7; KD4_DEC_SAFE_BYTES `X1` 352; `pc:num`] (k0+3) THEN
    ARM_STEPS_TAC KD4_EXEC ((k0+4)--(k0+8)) THEN KD4_TIDY_TAC) (0--3) THEN
  ARM_STEPS_TAC KD4_EXEC (48--52) THEN
  ARM_STEPS_TAC KD4_EXEC (53--53) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (54--58) THEN
  KD4_DEC_SAFE_CALL0_TAC "H_D5"
   [e; x 2; x 8; KD4_DEC_SAFE_BYTES `X2` 160; `pc:num`] 59 THEN
  ARM_STEPS_TAC KD4_EXEC (60--62) THEN
  MAP_EVERY (fun q ->
    let k0 = 63 + 8 * q in
    ARM_STEPS_TAC KD4_EXEC (k0--(k0+3)) THEN KD4_TIDY_TAC THEN
    call "H_FROMBYTES" ([e; x 0; x 1] @ rest0) (k0+4) THEN
    ARM_STEPS_TAC KD4_EXEC ((k0+5)--(k0+7)) THEN KD4_TIDY_TAC) (0--3) THEN
  ARM_STEPS_TAC KD4_EXEC (95--98) THEN
  call "H_NTT" ([e; x 0] @ rest0) 99 THEN
  ARM_STEPS_TAC KD4_EXEC (100--104) THEN
  call "H_NTT" ([e; x 0] @ rest0) 105 THEN
  ARM_STEPS_TAC KD4_EXEC (106--107) THEN
  call "H_NTT" ([e; x 0] @ rest0) 108 THEN
  ARM_STEPS_TAC KD4_EXEC (109--110) THEN
  call "H_NTT" ([e; x 0] @ rest0) 111 THEN
  MAP_EVERY (fun q ->
    let k0 = 112 + 9 * q in
    ARM_STEPS_TAC KD4_EXEC (k0--(k0+2)) THEN KD4_TIDY_TAC THEN
    call "H_MULCACHE" ([e; x 0; x 1] @ rest0) (k0+3) THEN
    ARM_STEPS_TAC KD4_EXEC ((k0+4)--(k0+8)) THEN KD4_TIDY_TAC) (0--3) THEN
  ARM_STEPS_TAC KD4_EXEC (148--154) THEN
  call "H_BASEMUL" ([e; x 1; x 2; x 3; x 0] @ rest0) 155 THEN
  ARM_STEPS_TAC KD4_EXEC (156--157) THEN
  call "H_INVNTT" [e; x 0; `pc:num`; `read SP s`; `read X30 s`] 158 THEN
  ARM_STEPS_TAC KD4_EXEC (159--159) THEN
  KD4_DEC_SAFE_CALL0_TAC "H_SUB" [e; x 23; x 0; KD4_DEC_SAFE_CONTENTS `X23`;
                KD4_DEC_SAFE_CONTENTS `X0`; `pc:num`] 160 THEN
  ARM_STEPS_TAC KD4_EXEC (161--164) THEN
  call "H_REDUCE" ([e; x 0] @ rest0) 165 THEN
  ARM_STEPS_TAC KD4_EXEC (166--168) THEN
  call "H_TOMSG" ([e; x 0; x 1] @ rest0) 169 THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC KD4_EXEC (k0--k) THEN LIBC_PLT_TAC KD4_EXEC k THEN
    KD4_DEC_NORMALIZE_TAC THEN
    LIBC_SAFE_CALL_TAC "H_MEMSET" KD4_EXEC
     [e; x 0; x 1; x 2; `read X30 s`] (ref KD4_DEC_ALLOWED) (k + 5))
   [170,173; 179,182; 188,191; 197,200; 206,209] THEN
  KD4_DEC_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD4_DEC_SAFE_A = prove(KD4_DEC_SAFE_GOAL "23008", KD4_DEC_SAFE_TAC);;

let KD4_DEC_SAFE_U = prove(KD4_DEC_SAFE_GOAL "22992", KD4_DEC_SAFE_TAC);;

let KD4_DEC_SAFE = prove
 (KD4_DEC_SAFE_GOAL_GEN " b"
   "(b = 23008 \\/ b = 22992) /\\\n            " " b" "b",
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(UNDISCH(SPEC_ALL KD4_DEC_SAFE_A)) THEN
  DISCH_THEN(X_CHOOSE_TAC
   `fa:int64->int64->int64->num->int64->(uarch_event)list`) THEN
  MP_TAC(UNDISCH(SPEC_ALL KD4_DEC_SAFE_U)) THEN
  DISCH_THEN(X_CHOOSE_TAC
   `fu:int64->int64->int64->num->int64->(uarch_event)list`) THEN
  EXISTS_TAC
   `\(sk:int64) (c:int64) (mf:int64) (pc:num) (stackpointer:int64)
      (b:num).
       if b = 23008 then fa sk c mf pc stackpointer
       else fu sk c mf pc stackpointer:(uarch_event)list` THEN
  REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    DISJ_CASES_THEN (fun eq -> SUBST1_TAC eq THEN
                               MP_TAC(REWRITE_RULE[eq] (CONJUNCT2 th)))
     (CONJUNCT1 th)) THEN
  REWRITE_TAC[ARITH_EQ] THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

(*** The function ***)

let KD4_SAFE_TEMPLATE =
 `\(ss:int64) (ct:int64) (sk:int64) (guard:int64) (mf:int64) (mc:int64)
   (pc:num) (sp:int64) (ra:int64) (ek:byte list) (h:byte list).
   if num_of_bytelist h = num_of_bytelist(sha3_256 ek)
   then APPEND
         (APPEND (f_ev_exitb ss ct sk guard mf mc pc sp ra)
           (APPEND (ENUMERATEL 32
                     (\i. f_ev_cmov ss ct sk guard mf mc pc sp ra i))
                   (f_ev_exita ss ct sk guard mf mc pc sp ra)))
         (APPEND (ENUMERATEL 98 (\i. f_ev_cmp ss ct sk guard mf mc pc sp ra i))
                 (f_ev_prol ss ct sk guard mf mc pc sp ra ek h))
   else f_ev_bad ss ct sk guard mf mc pc sp ra ek h
   :(uarch_event)list`;;

let KD4_SAFE_ALLOWED =
  [`pc:num`; `ss:int64`; `ct:int64`; `sk:int64`; `guard:int64`;
   `mf:int64`; `mc:int64`; `stackpointer:int64`; `returnaddress:int64`;
   `ekk:byte list`; `hh:byte list`; `i:num`;
   `f_ev_cmp:int64->int64->int64->int64->int64->int64->num->int64->
              int64->num->(uarch_event)list`;
   `f_ev_cmov:int64->int64->int64->int64->int64->int64->num->int64->
              int64->num->(uarch_event)list`];;

let KD4_SAFE_CALL_TAC name ilist n =
  KD4_SAFE_NORMALIZE_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,KD4_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KD4_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KD4_SAFE_FRAME = subst [KD4_SAFE_B,`b:num`]
 `read SP s = word_add stackpointer (word 22864) /\
  read X19 s = word_add stackpointer (word(b + 4096)) /\
  read X20 s = word_add stackpointer (word(b + 7808)) /\
  read X22 s = word_add stackpointer (word(b + 7744)) /\
  read X24 s = word 0 /\
  read (memory :> bytes64 (word_add stackpointer (word 22864))) s =
  x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word 22872))) s =
  x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 22880))) s =
  x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 22888))) s =
  x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 22896))) s =
  x23_init /\
  read (memory :> bytes64 (word_add stackpointer (word 22904))) s =
  x24_init /\
  read (memory :> bytes64 (word_add stackpointer (word 22912))) s =
  x25_init /\
  read (memory :> bytes64 (word_add stackpointer (word 22920))) s =
  x26_init /\
  read (memory :> bytes64 (word_add stackpointer (word 22928))) s =
  x27_init /\
  read (memory :> bytes64 (word_add stackpointer (word 22936))) s =
  x28_init /\
  read (memory :> bytes64 (word_add stackpointer (word 22944))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 22968))) s = ct /\
  read (memory :> bytes64 (word_add stackpointer (word 22984))) s = ss /\
  read (memory :> bytes64 (word_add stackpointer (word 30888))) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard)))
   s = guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
  read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s = mc /\
  read (memory :> bytes(ea,el)) s = ev`;;

let KD4_SAFE_INV =
  let inv = subst [KD4_SAFE_B,`b:num`]
   `\i s. read X0 s = word_add stackpointer (word((b + 4096) + 16 * i)) /\
          read X1 s = word_add stackpointer (word(b + 5664)) /\
          read (memory :> bytes64 (word_add stackpointer (word 22976))) s =
          word_add ct (word(16 * i)) /\
          read X21 s = sk /\ FRAME` in
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [KD4_SAFE_FRAME,`FRAME:bool`] bod);;

let KD4_SAFE_CMOV_INV =
  let inv =
   `\i s. read X0 s = word(i + 1) /\
          read X1 s = word_sub ss (word 1) /\ FRAME` in
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [KD4_SAFE_FRAME,`FRAME:bool`] bod);;

let KD4_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th1 ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th1)
    then FIRST_X_ASSUM(fun th2 ->
      let sth = CONJUNCT2(MATCH_MP MEMSET_FULL_CONTRACT th1) in
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
                 (CONJ th1 th2)) "H_ENC" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP KD4_DEC_SAFE sth) "H_DEC" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (REWRITE_RULE[memset_safety_contract] sth) "H_MEMSET" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE th2)
       "H_SHAKE256" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (REWRITE_RULE[memcpy_safety_contract] th2) "H_MEMCPY")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_CHECK_SK_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL "H_CHECK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHA3_512_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_SHA3_512" THEN
  CONCRETIZE_F_EVENTS_TAC KD4_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 30896):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `22992 <= (if aligned 32 (stackpointer:int64) then 23008 else 22992) /\
    (if aligned 32 (stackpointer:int64) then 23008 else 22992) <= 23008`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(if aligned 32 (stackpointer:int64) then 23008 else 22992) = 23008 \/
    (if aligned 32 (stackpointer:int64) then 23008 else 22992) = 22992`
  ASSUME_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28) THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 1536 (dk:byte list)) = 1536 /\
    LENGTH(mlkem_slice 1536 1568 (dk:byte list)) = 1568 /\
    LENGTH(mlkem_slice 3104 32 (dk:byte list)) = 32 /\
    LENGTH(mlkem_slice 3136 32 (dk:byte list)) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE
   [SYM(CONV_RULE NUM_REDUCE_CONV
     (MP (SPECL [`1536`; `32`; `1536`; `1568`; `dk:byte list`]
                MLKEM_SLICE_SLICE)
         (ARITH_RULE `1536 + 32 <= 1568`)))] o
   check (fun th -> is_forall(concl th) &&
                    KEM_HAS_CONST "mlkem_samplentt_terminates"
                     (concl th))) THEN
  ABBREV_TAC `ekk = mlkem_slice 1536 1568 (dk:byte list)` THEN
  ABBREV_TAC `hh = mlkem_slice 3104 32 (dk:byte list)`;;

let KD4_SAFE_START_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  KD4_SK_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (4--10) THEN KD4_SAFE_BUFFER_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (11--18) THEN INLINE_GOT_TAC THEN
  KD4_SAFE_CALL_TAC "H_CHECK"
   [`e:(uarch_event)list`; `read X0 s`; `ekk:byte list`;
    `num_of_bytelist(hh:byte list)`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 19;;

let KD4_SAFE_PART1_TAC =
  KD4_SAFE_START_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EQT_INTRO(ASSUME
   `num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk)`)]) THEN
  ARM_STEPS_TAC KD4_EXEC (20--21) THEN INLINE_GOT_TAC THEN
  KD4_SAFE_CALL_TAC "H_DEC"
   [`e:(uarch_event)list`; `read X21 s`; `read X0 s`; `pc:num`;
    `stackpointer:int64`; `read X25 s`; `read X26 s`; `read X27 s`;
    `read X28 s`; KD4_SAFE_B] 22 THEN
  ARM_STEPS_TAC KD4_EXEC (23--32) THEN INLINE_GOT_TAC THEN
  KD4_SAFE_CALL_TAC "H_SHA3_512"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `64`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 33 THEN
  ARM_STEPS_TAC KD4_EXEC (34--38) THEN INLINE_GOT_TAC THEN
  KD4_SAFE_CALL_TAC "H_ENC"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `ekk:byte list`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 39 THEN
  ARM_STEPS_TAC KD4_EXEC (40--45) THEN
  KD4_SAFE_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD4_SAFE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPECL [`stackpointer:int64`; KD4_SAFE_B; `i:num`] KD4_TEST)
       (CONJ (ASSUME
         `(if aligned 32 (stackpointer:int64) then 23008 else 22992) <= 23008`)
             (ASSUME `i < 98`))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD4_SAFE_EXIT_A_TAC =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (1--31) THEN LIBC_PLT_TAC KD4_EXEC 31 THEN
  KD4_SAFE_NORMALIZE_TAC THEN LIBC_SAFE_CALL_TAC "H_MEMCPY" KD4_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KD4_SAFE_ALLOWED) 36 THEN
  ARM_STEPS_TAC KD4_EXEC (37--42) THEN INLINE_GOT_TAC THEN
  KD4_SAFE_CALL_TAC "H_SHAKE256"
   [`e:(uarch_event)list`; `read X0 s`; `32`; `read X2 s`; `1600`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 43 THEN
  ARM_STEPS_TAC KD4_EXEC (44--45) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `0 + 1 = 1`; APPEND_NIL; ENUMERATEL_APPEND_ZERO] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The address of byte i of K' in the selection loop ***)

let KD4_KBAR_ADDR = prove
 (`!sp:int64 a b i.
        word_add (word_add (word (i + 1)) (word_add sp (word (a + b))))
                 (word 18446744073709551615) =
        word_add sp (word (a + b + i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[KD4_KP_ADDR2] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[ARITH_RULE
   `(a + b) + (i + 1) + 18446744073709551615 =
    1 * 18446744073709551616 + (a + b + i)`; MOD_MULT_ADD]);;

let KD4_SAFE_CMOV_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (1--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [KEM_SS_ADDR; KD4_KBAR_ADDR;
    MP (SPEC `i:num` KEM_CMOV_TEST) (ASSUME `i < 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM WORD_ADD]; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD4_SAFE_EXIT_B_TAC =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (1--7) THEN LIBC_PLT_TAC KD4_EXEC 7 THEN
  KD4_SAFE_NORMALIZE_TAC THEN LIBC_SAFE_CALL_TAC "H_MEMSET" KD4_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KD4_SAFE_ALLOWED) 12 THEN
  ARM_STEPS_TAC KD4_EXEC (13--18) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (19--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD4_SAFE_BAD_TAC =
  KD4_SAFE_START_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EQF_INTRO(ASSUME
   `~(num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk))`)]) THEN
  ARM_STEPS_TAC KD4_EXEC (20--30) THEN LIBC_PLT_TAC KD4_EXEC 30 THEN
  KD4_SAFE_NORMALIZE_TAC THEN LIBC_SAFE_CALL_TAC "H_MEMSET" KD4_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KD4_SAFE_ALLOWED) 35 THEN
  ARM_STEPS_TAC KD4_EXEC (36--41) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD4_EXEC (42--55) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_DEC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  prove
 (`!mf mc ea el ev.
   memset_full_contract mf ea el ev /\ memcpy_safety_contract mc ea el ev
   ==> exists f_events.
        forall e ss ct sk (dk:byte list) guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH dk = 3168 /\
          (!i j. i < 4 /\ j < 4
                 ==> mlkem_samplentt_terminates
                      (APPEND (mlkem_slice 3072 32 dk) [word j; word i])) /\
          nonoverlapping (word 0,1)
           (word_sub stackpointer (word 30896),30896) /\
          nonoverlapping (ct,1568) (word pc,libmlkem_size) /\
          nonoverlapping (sk,3168) (word pc,libmlkem_size) /\
          nonoverlapping (ss,32)
           (word_sub stackpointer (word 30896),30896) /\
          ALLPAIRS nonoverlapping
           [(ss,32); (word_sub stackpointer (word 30896),30896)]
           [(ct,1568); (sk,3168); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlkem1024_dec) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [ss; ct; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sk,3168)) s = num_of_bytelist dk /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events ss ct sk guard mf mc pc
                              (word_sub stackpointer (word 30896))
                              returnaddress
                              (mlkem_slice 1536 1568 dk)
                              (mlkem_slice 3104 32 dk) /\
                       memaccess_inbounds e2
                        [ct,1568; sk,3168; ss,32;
                         word_sub stackpointer (word 30896),30896;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + mlkem_poly_cbd2_consts),64;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlk_poly_invntt_tomont_c_consts),32;
                         word(pc + mlkem1024_dec_consts),16]
                        [ss,32; word_sub stackpointer (word 30896),30896]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(ss,32);
                  memory :> bytes(word_sub stackpointer (word 30896),30896)])`,
  KD4_SAFE_INTRO_TAC THEN
  ASM_CASES_TAC
   `num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk)` THEN
  ASM_REWRITE_TAC[] THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `98` `pc + mlkem1024_dec_loop7`
    `pc + mlkem1024_dec_loop7_exit`
     KD4_SAFE_INV THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC; KD4_SAFE_PART1_TAC; KD4_SAFE_BODY_TAC;
      ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem1024_dec_loop8`
       `pc + mlkem1024_dec_loop8_exit`
       KD4_SAFE_CMOV_INV THEN
      REPEAT CONJ_TAC THENL
       [ARITH_TAC; KD4_SAFE_EXIT_A_TAC; KD4_SAFE_CMOV_BODY_TAC;
        KD4_SAFE_EXIT_B_TAC]];
    KD4_SAFE_BAD_TAC]);;
