(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The encryption of K-PKE for ML-KEM-1024 (FIPS 203 Algorithm 14). This is  *)
(* the code for mlkem1024_indcpa_enc from mlkem-native's portable C          *)
(* implementation compiled by gcc 12 with -O2 as one translation unit (see   *)
(* mlkem_native/README.md). It decodes the vector t in the NTT domain from   *)
(* the encryption key and the message m from its 32 bytes, generates the     *)
(* transposed matrix from rho (the last 32 bytes of the key), samples y, e1  *)
(* and e2 from the randomness r, and computes u = NTT^-1(A^T NTT(y)) + e1    *)
(* and v = NTT^-1(t^T NTT(y)) + e2 + mu, where mu is m decompressed. It      *)
(* writes the compressions of u and v as the ciphertext, zeroing its         *)
(* buffers. It is verified in the whole image (see libmlkem.ml), using the   *)
(* theorems for mlk_poly_frombytes_c, mlkem_poly_frommsg,                    *)
(* mlkem1024_gen_matrix, mlkem1024_poly_getnoise_eta1_4x,                    *)
(* mlkem1024_poly_getnoise_eta2, mlk_poly_ntt_c,                             *)
(* mlk_poly_mulcache_compute_c,                                              *)
(* mlk_polyvec_basemul_acc_montgomery_cached_c1024,                          *)
(* mlk_poly_invntt_tomont_c and mlk_poly_reduce_c in the image, and the      *)
(* contracts for memset and memcpy.                                          *)
(*                                                                           *)
(* Differences from the gcc 12 -O2 proof. gcc has inlined all the polyvec    *)
(* functions, poly_add and the compressions:                                 *)
(*                                                                           *)
(*  - polyvec_frombytes, polyvec_mulcache_compute and the products with the  *)
(*    rows of the matrix are loops of four kernel calls, polyvec_ntt,        *)
(*    polyvec_invntt_tomont and polyvec_reduce four calls each: the loops   *)
(*    are unrolled in the proof and the postconditions of the polyvec        *)
(*    functions are proved from those of the calls                           *)
(*    (mlkem_native/indcpa_inline.ml);                                       *)
(*  - polyvec_add and the two calls of poly_add: the vector code of poly_add *)
(*    is inlined, in a loop over the four polynomials of u (unrolled in the  *)
(*    proof) and twice for v. The inner loops are proved as lemmas from      *)
(*    their head to their exit, with the events                              *)
(*    (mlkem_native/inline_loops.ml);                                        *)
(*  - polyvec_compress_du is a loop over the four polynomials around the     *)
(*    inlined code of poly_compress_d11, and poly_compress_d5 is inlined     *)
(*    for v. The code of each is that of the gcc 12 -O2 kernel up to         *)
(*    registers and the address of its temporary array on the stack, so it  *)
(*    is proved again here as a lemma, from the head of its loop over the    *)
(*    blocks of eight coefficients to the exit, by the proof of the gcc 12   *)
(*    -O2 kernel (EN4_D11 for one polynomial of u, EN4_D5 for v).           *)
(*                                                                           *)
(* The buffers are at the same offsets from each other as with gcc 12 -O2;   *)
(* the frame is the 19184 bytes of the function and the 3680 of              *)
(* mlkem1024_gen_matrix below them, 22864 in all.                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_frombytes_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_frommsg_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/gen_matrix_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_getnoise_eta1_4x_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_getnoise_eta2_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_ntt_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_mulcache_compute_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/basemul_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_reduce_spec.ml";;
needs "arm/proofs/mlkem_native/indcpa_inline.ml";;
needs "arm/proofs/mlkem_native/inline_loops.ml";;

(*** The code in the image is listed at the end of layout.ml, with the
     labels of the inlined calls. ***)

let MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "plt_memset"; layout_range "mlkem1024_indcpa_enc"];;

let EN4_EXEC = MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_MONO_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The encryption in FIPS 203 in terms of the values computed by the code:   *)
(* the 12-bit fields of the encryption key as decoded (which may be >= q),   *)
(* the NTT of y and its multiplication cache, the noise e1 and e2, the       *)
(* decompressed message, the products with the transposed matrix and with t  *)
(* in Montgomery form, their inverse NTTs, and the results after adding the  *)
(* noise and the message and reducing, whose compressions are encoded in the *)
(* ciphertext.                                                               *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_K4_RESULT_STMT =
  `!ek m r (TT:num->int16) (YH:num->int16) (MC:num->int16) (E1:num->int16)
    (E2:num->int16) (MU:num->int16) (U0:num->int16) (V0:num->int16)
    (U1:num->int16) (V1:num->int16) (U3:num->int16) (V4:num->int16).
     (!i j n. i < 4 /\ j < 4 /\ n < 256
              ==> mlkem_sample_ntt
                   (APPEND (mlkem_slice 1536 32 ek) [word j; word i]) n
                  < &3329) /\
     (!i. i < 1024
          ==> TT i = word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(YH(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j))) i)
                (mod &3329) /\
                abs(ival(YH(256 * j + i))) <= &23594) /\
     (!j p. j < 4 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(YH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(E1(256 * j + i)) ==
                 coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word(4 + j)))))
                (mod &3329) /\
                abs(ival(E1(256 * j + i))) <= &2) /\
     (!i. i < 256
          ==> (ival(E2 i) == coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word 8))))
              (mod &3329) /\
              abs(ival(E2 i)) <= &2) /\
     (!i. i < 256
          ==> MU i = word((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1)
                          DIV 2)) /\
     (!q p. q < 4 /\ p < 128
            ==> (ival(U0(256 * q + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 3]) (2 * p + 1) *
                   ival(MC(384 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 3]) (2 * p) *
                   ival(YH(768 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 2]) (2 * p + 1) *
                   ival(MC(256 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 2]) (2 * p) *
                   ival(YH(512 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(MC(128 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(MC p) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p))))) (mod &3329) /\
                (ival(U0(256 * q + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 3]) (2 * p + 1) *
                   ival(YH(768 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 3]) (2 * p) *
                   ival(YH(768 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 2]) (2 * p + 1) *
                   ival(YH(512 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 2]) (2 * p) *
                   ival(YH(512 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(YH(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(YH(2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(V0(2 * p)) ==
               &169 *
               ((ival(TT(768 + 2 * p + 1)) * ival(MC(384 + p)) +
                 ival(TT(768 + 2 * p)) * ival(YH(768 + 2 * p))) +
                (ival(TT(512 + 2 * p + 1)) * ival(MC(256 + p)) +
                 ival(TT(512 + 2 * p)) * ival(YH(512 + 2 * p))) +
                (ival(TT(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p))) +
                (ival(TT(2 * p + 1)) * ival(MC p) +
                 ival(TT(2 * p)) * ival(YH(2 * p))))) (mod &3329) /\
              (ival(V0(2 * p + 1)) ==
               &169 *
               ((ival(TT(768 + 2 * p + 1)) * ival(YH(768 + 2 * p)) +
                 ival(TT(768 + 2 * p)) * ival(YH(768 + 2 * p + 1))) +
                (ival(TT(512 + 2 * p + 1)) * ival(YH(512 + 2 * p)) +
                 ival(TT(512 + 2 * p)) * ival(YH(512 + 2 * p + 1))) +
                (ival(TT(256 + 2 * p + 1)) * ival(YH(256 + 2 * p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p + 1))) +
                (ival(TT(2 * p + 1)) * ival(YH(2 * p)) +
                 ival(TT(2 * p)) * ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(U1(256 * j + i)) ==
                 inverse_ntt (\n. ival(U0(256 * j + n))) i) (mod &3329) /\
                abs(ival(U1(256 * j + i))) <= &26624) /\
     (!i. i < 256
          ==> (ival(V1 i) == inverse_ntt (\n. ival(V0 n)) i) (mod &3329) /\
              abs(ival(V1 i)) <= &26624) /\
     (!i. i < 1024
          ==> ival(U3 i) = ival(word_add (U1 i) (E1 i)) rem &3329) /\
     (!i. i < 256
          ==> ival(V4 i) =
              ival(word_add (word_add (V1 i) (E2 i)) (MU i)) rem &3329)
     ==> nsum {i | i < 1024}
              (\i. ((4096 * val(U3 i) + 3329) DIV 6658) MOD 2048 *
                   2 EXP (11 * i)) +
         2 EXP (8 * 1408) *
         nsum {i | i < 256}
              (\i. ((64 * val(V4 i) + 3329) DIV 6658) MOD 32 * 2 EXP (5 * i)) =
         num_of_bytelist(kpke_encrypt mlkem1024 ek m r)`;;

let KPKE_ENCRYPT_K4_RESULT = assume_spec KPKE_ENCRYPT_K4_RESULT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16. They are at the same offsets from each other as with gcc 12 -O2:   *)
(* 0 (the matrix), 8192 (u), 10240 (e1), 12288 (t), 14336 (y), 16384 (its    *)
(* multiplication cache), 17408 (e2), 17920 (the message), 18432 (v) and     *)
(* 18944 (rho). The temporary arrays of the compressions are at 19152 and    *)
(* 19168 from the stack pointer of the function.                             *)
(* ------------------------------------------------------------------------- *)

let EN4_ALIGNED_16_32_STMT =
  `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`;;

let EN4_ALIGNED_16_32 = assume_spec EN4_ALIGNED_16_32_STMT;;

let EN4_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 3871)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 3840 else 3856))`;;

let EN4_BUFFER_ADDRESS = assume_spec EN4_BUFFER_ADDRESS_STMT;;

let EN4_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` EN4_BUFFER_ADDRESS))
    else NO_TAC);;

let EN4_PK_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(pk,1568)) s = num_of_bytelist ek`) (concl th)
    then
      ASSUME_TAC(REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
       (REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_MOD;
                     ARITH_RULE `MIN 1568 1536 = 1536`]
        (AP_THM(AP_TERM `(MOD):num->num->num`
                 (REWRITE_RULE[READ_COMPONENT_COMPOSE] th))
           `2 EXP (8 * 1536)`))) THEN
      MP_TAC(SPECL [`pk:int64`; `ek:byte list`; `1536`; `32`;
                    rand(lhand(concl th))] READ_MEMORY_BYTES_SLICE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(fun th -> ASSUME_TAC th THEN
          STRIP_ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV
             NORMALIZE_RELATIVE_ADDRESS_CONV THENC
             ONCE_DEPTH_CONV NUM_ADD_CONV)
           (MATCH_MP INLINE_BYTES128_HALVES th)))]
    else NO_TAC);;

(*** The decoded t: the postcondition of polyvec_frombytes from the four
     calls of the kernel (with ekt the first 1536 bytes of the key as a
     number), then as for gcc 12 -O2 ***)

let EN4_TT_TAC b s =
  INDCPA_GHOST_TAC "TT" (b + 12288) 1024 s THEN
  SUBGOAL_THEN
   `!i. i < 1024
        ==> (TT:num->int16) i =
            word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "TT" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem (mk_var(s,`:armstate`)) (frees(concl th)) &&
      INDCPA_HAS_CONST "MOD" (concl th) && is_forall(concl th) &&
      can (find_term (fun t -> t = `1024`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "ekt" THEN
    MATCH_MP_TAC DIV_MOD_EXP_LOW THEN UNDISCH_TAC `i < 1024` THEN ARITH_TAC;
    ALL_TAC];;

let EN4_MU_TAC b s =
  INDCPA_GHOST_TAC "MU" (b + 17920) 256 s THEN
  SUBGOAL_THEN
   `!i. i < 256
        ==> (MU:num->int16) i =
            word((3329 * (num_of_bytelist msg DIV 2 EXP i) MOD 2 + 1) DIV 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "MU" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem (mk_var(s,`:armstate`)) (frees(concl th)) &&
      can (find_term (fun t -> t = `3329`)) (concl th) &&
      is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

let EN4_SEED_TAC b s =
  MP_TAC(SPECL [INDCPA_SP(b + 18944); `num_of_bytelist rho`;
                mk_var(s,`:armstate`)] INLINE_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `rho:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

(*** The pointers into the key and the buffers are incremented in the
     inlined loops: the stack-relative ones are normalized with the offsets
     folded, and the loop tests compare two of them ***)

let EN4_ADD_ASSOC_NUMERALS_CONV tm =
  match tm with
    Comb(Comb(Const("+",_),Comb(Comb(Const("+",_),x),m)),n)
      when is_numeral m && is_numeral n ->
      (GEN_REWRITE_CONV I [GSYM ADD_ASSOC] THENC RAND_CONV NUM_ADD_CONV) tm
  | _ -> failwith "EN4_ADD_ASSOC_NUMERALS_CONV";;

let EN4_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                   TOP_DEPTH_CONV EN4_ADD_ASSOC_NUMERALS_CONV) th
    else th);;

let EN4_PC_TAC s =
  let pcs = mk_comb(`read PC`,mk_var(s,`:armstate`)) in
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && lhand(concl th) = pcs then
      ASSUME_TAC(CONV_RULE(RAND_CONV
       (REWRITE_CONV
         [WORD_RULE `word_sub (word_add (s:int64) x) (word_add s y) =
                     word_sub x y`] THENC
        ONCE_DEPTH_CONV WORD_REDUCE_CONV THENC NUM_REDUCE_CONV THENC
        REWRITE_CONV[])) th)
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The inlined compressions. For each polynomial of u, poly_compress_d11 is  *)
(* the loop of the gcc 12 -O2 kernel over the 32 blocks of eight             *)
(* coefficients (from loop9 to its exit), with the index of the polynomial   *)
(* times 256 in X6 added to the index of the coefficient and eight 11-bit    *)
(* values in a temporary array at stackpointer + 19152; poly_compress_d5 of  *)
(* v is the whole loop of the gcc 12 -O2 kernel (from loop11 to its exit),   *)
(* with its temporary array at stackpointer + 19168. Both are proved here as *)
(* lemmas, by the proofs of the gcc 12 -O2 kernels with the instructions of  *)
(* this code, with the events, for the correctness and the safety proofs.    *)
(* As for the kernels, they rely on the coefficients being in [0,3329).      *)
(* ------------------------------------------------------------------------- *)

let EN4_D11_ARITH_STMT =
  `!v. v < 3329
       ==> (4294967296 + v * 5284526080) DIV 8589934592 =
           (4096 * v + 3329) DIV 6658`;;

let EN4_D11_ARITH = assume_spec EN4_D11_ARITH_STMT;;

let EN4_WORD_SX_SMALL_64_STMT =
  `!y:int16. val y < 32768 ==> (word_sx y:int64) = word_zx y`;;

let EN4_WORD_SX_SMALL_64 = assume_spec EN4_WORD_SX_SMALL_64_STMT;;

let EN4_D11_FIELD_STMT =
  `!y:int16.
        val y < 3329
        ==> val(word_subword
                 (word (4294967296 + val (word_sx y:int64) * 5284526080):
                  int64)
                 (33,11):11 word) =
            ((4096 * val y + 3329) DIV 6658) MOD 2048`;;

let EN4_D11_FIELD = assume_spec EN4_D11_FIELD_STMT;;

let EN4_VAL_JOIN_11X8_STMT =
  `!(u0:11 word) (u1:11 word) (u2:11 word) (u3:11 word)
    (u4:11 word) (u5:11 word) (u6:11 word) (u7:11 word).
     val(word_join u7 (word_join u6 (word_join u5 (word_join u4
          (word_join u3 (word_join u2 (word_join u1 u0:22 word):33 word):
           44 word):55 word):66 word):77 word):88 word) =
     val u0 + 2048 * val u1 + 4194304 * val u2 + 8589934592 * val u3 +
     17592186044416 * val u4 + 36028797018963968 * val u5 +
     73786976294838206464 * val u6 + 151115727451828646838272 * val u7`;;

let EN4_VAL_JOIN_11X8 = assume_spec EN4_VAL_JOIN_11X8_STMT;;

let EN4_WORD_SUBWORD_BYTE = prove
 (`!(w:N word) p.
        word_subword w (p,8):byte = word((val w DIV 2 EXP p) MOD 256)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

let en4_d11_indices = map (fun k ->
  if k = 0 then `8 * i` else
  mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k)) (0--8);;

let en4_d11_xatoms = map (fun j ->
  vsubst [j,`j:num`]
   `word (4294967296 + val (word_sx ((x:num->int16) j):int64) * 5284526080):
    int64`) (butlast en4_d11_indices);;

let en4_d11_join =
  vsubst (zip en4_d11_xatoms
              (map (fun k -> mk_var("w"^string_of_int k,`:int64`)) (0--7)))
  `word_join (word_subword (w7:int64) (33,11):11 word)
    (word_join (word_subword (w6:int64) (33,11):11 word)
     (word_join (word_subword (w5:int64) (33,11):11 word)
      (word_join (word_subword (w4:int64) (33,11):11 word)
       (word_join (word_subword (w3:int64) (33,11):11 word)
        (word_join (word_subword (w2:int64) (33,11):11 word)
         (word_join (word_subword (w1:int64) (33,11):11 word)
                    (word_subword (w0:int64) (33,11):11 word):22 word):
         33 word):44 word):55 word):66 word):77 word):88 word`;;

let EN4_D11_PACK_TAC m =
  let addr =
    if m = 0 then `word_add r (word (11 * i)):int64` else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`r:int64`),
            mk_comb(`word:num->int64`,
                    mk_binop `(+):num->num->num` `11 * i`
                             (mk_small_numeral m))) in
  let pat = vsubst [addr,`addr:int64`]
              `read (memory :> bytes8 addr) s = x` in
  let rule th =
    let v = rand(concl th) in
    let target = mk_comb(mk_comb(`word_subword:88 word->num#num->byte`,
                                 en4_d11_join),
                         mk_pair(mk_small_numeral(8 * m),`8`)) in
    let gvs = map (fun _ -> genvar `:int64`) en4_d11_xatoms in
    let eq = subst (zip gvs en4_d11_xatoms) (mk_eq(v,target)) in
    TRANS th (INST (zip en4_d11_xatoms gvs) (BITBLAST_RULE eq)) in
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] pat) (concl th)
    then ASSUME_TAC(rule th) else failwith "EN4_D11_PACK_TAC");;

let EN4_D11_SPLIT_TAC =
  FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (can (term_match []
      `read (memory :> bytes64 (word_add r (word(11 * i)))) s = x`) o
           concl)) THEN
  DISCH_THEN(fun th -> MAP_EVERY (ASSUME_TAC o
     CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD])))
     (CONJUNCTS th));;

let EN4_D11_GOAL = `exists f_events.
     forall e j r a (x:num->int16) pc stackpointer.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ j < 4 /\
       nonoverlapping (r,352) (word pc,libmlkem_size) /\
       nonoverlapping (word_add stackpointer (word 19152),16)
                      (word pc,libmlkem_size) /\
       nonoverlapping (r,352) (a,2048) /\
       nonoverlapping (r,352) (word_add stackpointer (word 19152),16) /\
       nonoverlapping (a,2048) (word_add stackpointer (word 19152),16)
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                 read PC s = word (pc + mlkem1024_indcpa_enc_loop9) /\
                 read SP s = stackpointer /\
                 read X9 s = r /\ read X3 s = word 8 /\
                 read X6 s = word(256 * j) /\
                 read X10 s = word_add stackpointer (word 19152) /\
                 read X25 s = a /\ read X8 s = word 5284526080 /\
                 read X7 s = word 4294967296 /\
                 (!i. i < 256
                      ==> read(memory :> bytes16
                                (word_add a (word(512 * j + 2 * i)))) s =
                          x i) /\
                 read events s = e)
            (\s. read PC s = word (pc + mlkem1024_indcpa_enc_loop9_exit) /\
                 ((!i. i < 256 ==> val(x i) < 3329)
                  ==> read(memory :> bytes(r,352)) s =
                      nsum {i | i < 256}
                           (\i. ((4096 * val(x i) + 3329) DIV 6658) MOD 2048 *
                                2 EXP (11 * i))) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events r a j pc stackpointer /\
                    memaccess_inbounds e2
                     [a,2048; r,352; word_add stackpointer (word 19152),16]
                     [r,352; word_add stackpointer (word 19152),16]))
            (MAYCHANGE [PC; X0; X1; X2; X3; X9; X13; X14; X15; X16; X17;
                        X18] ,, MAYCHANGE [Q0; Q1; Q2] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes(r,352);
                        memory :> bytes(word_add stackpointer (word 19152),16)])`;;

let EN4_D11_INV = `\i s. read SP s = stackpointer /\
          read X9 s = word_add r (word(11 * i)) /\
          read X3 s = word(8 * i + 8) /\
          read X6 s = word(256 * j) /\
          read X10 s = word_add stackpointer (word 19152) /\
          read X25 s = a /\ read X8 s = word 5284526080 /\
          read X7 s = word 4294967296 /\
          (!m. m < 256
               ==> read(memory :> bytes16
                         (word_add a (word(512 * j + 2 * m)))) s =
                   (x:num->int16) m) /\
          ((!m. m < 256 ==> val(x m) < 3329)
           ==> read(memory :> bytes(r,11 * i)) s =
               nsum {m | m < 8 * i}
                (\m. ((4096 * val(x m) + 3329) DIV 6658) MOD 2048 *
                     2 EXP (11 * m)))`;;

let EN4_D11_IDX_STMT =
  `!j n. j < 4 /\ n < 256
         ==> word_add (word(256 * j)) (word_zx (word_zx (word n:int64):int32))
             :int64 = word(256 * j + n) /\
             val(word(256 * j + n):int64) = 256 * j + n`;;

let EN4_D11_IDX = assume_spec EN4_D11_IDX_STMT;;

let EN4_TIDY_TAC reg tm tac =
  let pat = mk_eq(mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                                  reg),`s:armstate`),`x:int64`) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] pat) c then
      MP_TAC th THEN SUBGOAL_THEN (mk_eq(rand c,tm)) SUBST1_TAC THENL
       [tac; DISCH_TAC]
    else failwith "EN4_TIDY_TAC");;

let EN4_D11_X0_TAC k =
  let jt = el k en4_d11_indices in
  let lt = MP (ARITH_RULE(mk_imp(`i < 32`,mk_binop `(<):num->num->bool` jt `256`)))
              (ASSUME `i < 32`) in
  let th = MP (SPECL [`j:num`; jt] EN4_D11_IDX)
              (CONJ (ASSUME `j < 4`) lt) in
  RULE_ASSUM_TAC(REWRITE_RULE[CONJUNCT1 th]) THEN ASSUME_TAC(CONJUNCT2 th);;

let EN4_D11_BODY_TAC =
  ARM_STEPS_TAC EN4_EXEC (1--1) THEN
  EN4_TIDY_TAC `X1` `word(8 * i):int64` WORD_SMALL_TAC THEN
  ARM_STEPS_TAC EN4_EXEC (2--2) THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC EN4_EXEC [3 + 8 * k] THEN EN4_D11_X0_TAC k THEN
    ARM_STEPS_TAC EN4_EXEC [4 + 8 * k] THEN
    EN4_TIDY_TAC `X1` (mk_comb(`word:num->int64`, el (k+1) en4_d11_indices))
      WORD_SMALL_TAC THEN
    ARM_STEPS_TAC EN4_EXEC ((5 + 8 * k)--(9 + 8 * k)) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC EN4_EXEC [10 + 8 * k]) (0--7) THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC EN4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[]) (67--117);;
let EN4_D11_TEST_STMT =
  `!i. i < 32
       ==> (~(val(word_sub
                (word_zx (word_zx (word_add (word_zx (word (8 * i + 8):int64):
                                                     int32)
                                            (word 8)):int64):int32)
                (word 264):int32) = 0) <=>
            i + 1 < 32)`;;

let EN4_D11_TEST = assume_spec EN4_D11_TEST_STMT;;

let EN4_D11_STMT =
  EN4_D11_GOAL;;

let EN4_D11 = assume_spec EN4_D11_STMT;;

let EN4_D5_ARITH_STMT =
  `!v. v < 3329
       ==> (67108864 + v * 1290176) DIV 134217728 =
           (64 * v + 3329) DIV 6658`;;

let EN4_D5_ARITH = assume_spec EN4_D5_ARITH_STMT;;

let EN4_WORD_SX_SMALL_32_STMT =
  `!y:int16. val y < 32768 ==> (word_sx y:int32) = word_zx y`;;

let EN4_WORD_SX_SMALL_32 = assume_spec EN4_WORD_SX_SMALL_32_STMT;;

let EN4_D5_FIELD_STMT =
  `!y:int16.
        val y < 3329
        ==> val(word_subword
                 (word (67108864 +
                        val (word_zx (word_zx (word_sx y:int32):int64):
                             int32) * 1290176):int32)
                 (27,5):5 word) =
            ((64 * val y + 3329) DIV 6658) MOD 32`;;

let EN4_D5_FIELD = assume_spec EN4_D5_FIELD_STMT;;

let EN4_BYTES_OF_NUM_5_STMT =
  `!n. n < 2 EXP 40
       ==> n MOD 256 + 256 * (n DIV 256) MOD 256 +
           65536 * (n DIV 65536) MOD 256 +
           16777216 * (n DIV 16777216) MOD 256 +
           4294967296 * (n DIV 4294967296) MOD 256 = n`;;

let EN4_BYTES_OF_NUM_5 = assume_spec EN4_BYTES_OF_NUM_5_STMT;;

let EN4_VAL_JOIN_5X8_STMT =
  `!(u0:5 word) (u1:5 word) (u2:5 word) (u3:5 word)
    (u4:5 word) (u5:5 word) (u6:5 word) (u7:5 word).
     val(word_join u7 (word_join u6 (word_join u5 (word_join u4
          (word_join u3 (word_join u2 (word_join u1 u0:10 word):15 word):
           20 word):25 word):30 word):35 word):40 word) =
     val u0 + 32 * val u1 + 1024 * val u2 + 32768 * val u3 +
     1048576 * val u4 + 33554432 * val u5 + 1073741824 * val u6 +
     34359738368 * val u7`;;

let EN4_VAL_JOIN_5X8 = assume_spec EN4_VAL_JOIN_5X8_STMT;;

let en4_d5_indices = map (fun k ->
  if k = 0 then `8 * i` else
  mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k)) (0--7);;

let en4_d5_xatoms = map (fun j ->
  vsubst [j,`j:num`]
   `word (67108864 +
          val (word_zx (word_zx (word_sx ((x:num->int16) j):int32):int64):
               int32) * 1290176):int32`) en4_d5_indices;;

let en4_d5_join =
  vsubst (zip en4_d5_xatoms
              (map (fun k -> mk_var("w"^string_of_int k,`:int32`)) (0--7)))
  `word_join (word_subword (w7:int32) (27,5):5 word)
    (word_join (word_subword (w6:int32) (27,5):5 word)
     (word_join (word_subword (w5:int32) (27,5):5 word)
      (word_join (word_subword (w4:int32) (27,5):5 word)
       (word_join (word_subword (w3:int32) (27,5):5 word)
        (word_join (word_subword (w2:int32) (27,5):5 word)
         (word_join (word_subword (w1:int32) (27,5):5 word)
                    (word_subword (w0:int32) (27,5):5 word):10 word):
         15 word):20 word):25 word):30 word):35 word):40 word`;;

let EN4_D5_PACK_TAC m =
  let addr =
    if m = 0 then `word_add r (word (5 * i)):int64` else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`r:int64`),
            mk_comb(`word:num->int64`,
                    mk_binop `(+):num->num->num` `5 * i`
                             (mk_small_numeral m))) in
  let pat = vsubst [addr,`addr:int64`]
              `read (memory :> bytes8 addr) s = x` in
  let rule th =
    let v = rand(concl th) in
    let target = mk_comb(mk_comb(`word_subword:40 word->num#num->byte`,
                                 en4_d5_join),
                         mk_pair(mk_small_numeral(8 * m),`8`)) in
    let gvs = map (fun _ -> genvar `:int32`) en4_d5_xatoms in
    let eq = subst (zip gvs en4_d5_xatoms) (mk_eq(v,target)) in
    TRANS th (INST (zip en4_d5_xatoms gvs) (BITBLAST_RULE eq)) in
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] pat) (concl th)
    then ASSUME_TAC(rule th) else failwith "EN4_D5_PACK_TAC");;

(*** The index 8 * i + k of the coefficient, in X0 here ***)

let EN4_D5_INDEX_TAC k =
  let jt = el k en4_d5_indices in
  let wt = mk_comb(`word:num->int64`,jt) in
  let mt = mk_comb(`word_zx:int32->int64`,
            mk_comb(mk_comb(`word_add:int32->int32->int32`,
                            `word_zx(word(8 * i):int64):int32`),
                    mk_comb(`word:num->int32`,mk_small_numeral k))) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read X0 s = x`) c then
      MP_TAC th THEN SUBGOAL_THEN (mk_eq(rand c,wt)) SUBST1_TAC THENL
       [TRANS_TAC EQ_TRANS mt THEN CONJ_TAC THENL
         [AP_TERM_TAC THEN SPEC_TAC(`word(8 * i):int64`,`w:int64`) THEN
          GEN_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));
          WORD_SMALL_TAC];
        DISCH_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,wt),jt)) ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        ALL_TAC]
    else failwith "EN4_D5_INDEX_TAC");;

let EN4_D5_BODY_TAC =
  ARM_STEPS_TAC EN4_EXEC (1--4) THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC EN4_EXEC [5 + 9 * k] THEN
    EN4_D5_INDEX_TAC k THEN
    ARM_STEPS_TAC EN4_EXEC ((6 + 9 * k)--(13 + 9 * k))) (0--7) THEN
  ARM_STEPS_TAC EN4_EXEC (77--110);;

let EN4_D5_TEST_STMT =
  `!i. i < 32
       ==> (~(val(word_sub
                (word_zx (word_zx (word_add (word_zx (word (8 * i):int64):int32)
                                            (word 8)):int64):int32)
                (word 256):int32) = 0) <=>
            i + 1 < 32)`;;

let EN4_D5_TEST = assume_spec EN4_D5_TEST_STMT;;

let EN4_D5_STMT =
  `exists f_events.
     forall e r a (x:num->int16) pc stackpointer.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (r,160) (word pc,libmlkem_size) /\
       nonoverlapping (word_add stackpointer (word 19168),8)
                      (word pc,libmlkem_size) /\
       nonoverlapping (r,160) (a,512) /\
       nonoverlapping (r,160) (word_add stackpointer (word 19168),8) /\
       nonoverlapping (a,512) (word_add stackpointer (word 19168),8)
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                 read PC s = word (pc + mlkem1024_indcpa_enc_loop11) /\
                 read SP s = stackpointer /\
                 read X19 s = r /\ read X9 s = word 0 /\
                 read X8 s = word_add stackpointer (word 19168) /\
                 read X26 s = a /\ read X7 s = word 1290176 /\
                 read X6 s = word 67108864 /\
                 (!i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i))))
                           s = x i) /\
                 read events s = e)
            (\s. read PC s = word (pc + mlkem1024_indcpa_enc_loop11_exit) /\
                 ((!i. i < 256 ==> val(x i) < 3329)
                  ==> read(memory :> bytes(r,160)) s =
                      nsum {i | i < 256}
                           (\i. ((64 * val(x i) + 3329) DIV 6658) MOD 32 *
                                2 EXP (5 * i))) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events r a pc stackpointer /\
                    memaccess_inbounds e2
                     [a,512; r,160; word_add stackpointer (word 19168),8]
                     [r,160; word_add stackpointer (word 19168),8]))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X9; X10; X11; X12; X13; X14;
                        X15; X19] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes(r,160);
                        memory :> bytes(word_add stackpointer (word 19168),8)])`;;

let EN4_D5 = assume_spec EN4_D5_STMT;;

(*** The compressed u: the postcondition of polyvec_compress_du from those
     of the four inlined compressions of a polynomial ***)

let EN4_NSUM_SHIFT_EXP_STMT =
  `!f m n d. nsum {i | i < n} (\i. f(m + i) * 2 EXP (d * (m + i))) =
             2 EXP (d * m) * nsum {i | i < n} (\i. f(m + i) * 2 EXP (d * i))`;;

let EN4_NSUM_SHIFT_EXP = assume_spec EN4_NSUM_SHIFT_EXP_STMT;;

let EN4_COMPRESS_DU_STEP_STMT =
  `!r s (g:num->num) k.
     read (memory :> bytes(r,352 * k)) s =
     nsum {i | i < 256 * k} (\i. g i * 2 EXP (11 * i)) /\
     read (memory :> bytes(word_add r (word(352 * k)),352)) s =
     nsum {i | i < 256} (\i. g(256 * k + i) * 2 EXP (11 * i))
     ==> read (memory :> bytes(r,352 * (k + 1))) s =
         nsum {i | i < 256 * (k + 1)} (\i. g i * 2 EXP (11 * i))`;;

let EN4_COMPRESS_DU_STEP = assume_spec EN4_COMPRESS_DU_STEP_STMT;;

let EN4_COMPRESS_DU_JOIN_STMT =
  `!r s (g:num->num).
     read (memory :> bytes(r,352)) s =
     nsum {i | i < 256} (\i. g i * 2 EXP (11 * i)) /\
     read (memory :> bytes(word_add r (word 352),352)) s =
     nsum {i | i < 256} (\i. g(256 + i) * 2 EXP (11 * i)) /\
     read (memory :> bytes(word_add r (word 704),352)) s =
     nsum {i | i < 256} (\i. g(512 + i) * 2 EXP (11 * i)) /\
     read (memory :> bytes(word_add r (word 1056),352)) s =
     nsum {i | i < 256} (\i. g(768 + i) * 2 EXP (11 * i))
     ==> read (memory :> bytes(r,1408)) s =
         nsum {i | i < 1024} (\i. g i * 2 EXP (11 * i))`;;

let EN4_COMPRESS_DU_JOIN = assume_spec EN4_COMPRESS_DU_JOIN_STMT;;

let EN4_COMPRESS_DU_TAC s =
  SUBGOAL_THEN (subst [mk_var(s,`:armstate`),`s:armstate`]
   `(!i. i < 1024 ==> val((U3:num->int16) i) < 3329)
    ==> read(memory :> bytes(c,1408)) s =
        nsum {i | i < 1024}
             (\i. ((4096 * val(U3 i) + 3329) DIV 6658) MOD 2048 *
                  2 EXP (11 * i))`)
  ASSUME_TAC THENL
   [DISCH_THEN(fun hyp ->
      REPEAT(FIRST_X_ASSUM(fun th ->
        if is_imp(concl th) && INDCPA_HAS_CONST "nsum" (concl th) &&
           free_in `U3:num->int16` (concl th)
        then MP_TAC th THEN ANTS_TAC THENL
              [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC hyp THEN
               UNDISCH_TAC `i < 256` THEN ARITH_TAC;
               DISCH_TAC]
        else NO_TAC))) THEN
    MATCH_MP_TAC EN4_COMPRESS_DU_JOIN THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The inlined loops of poly_add, as lemmas from their head to their exit,   *)
(* with the events (mlkem_native/inline_loops.ml): u += e1 is a loop over    *)
(* the four polynomials around ADD1 (an index added to two bases), then v    *)
(* += e2 and v += mu (pointers).                                             *)
(* ------------------------------------------------------------------------- *)

let EN4_ADD1 = INLINE_REG_IDX_LOOP "mlkem_native_libmlkem_gcc12_O2_mono_mc"
  EN4_EXEC "add" "mlkem1024_indcpa_enc_loop5" "mlkem1024_indcpa_enc_loop5_exit"
  "X19" "X1" "X0";;

let EN4_ADD2 = INLINE_PTR_LOOP "mlkem_native_libmlkem_gcc12_O2_mono_mc"
  EN4_EXEC "add" "mlkem1024_indcpa_enc_loop6" "mlkem1024_indcpa_enc_loop6_exit"
  "X1" "X3" "X2";;

let EN4_ADD3 = INLINE_PTR_LOOP "mlkem_native_libmlkem_gcc12_O2_mono_mc"
  EN4_EXEC "add" "mlkem1024_indcpa_enc_loop7" "mlkem1024_indcpa_enc_loop7_exit"
  "X0" "X1" "X2";;

(* ------------------------------------------------------------------------- *)
(* The callees. The matrix is generated with transposition, the noise y and  *)
(* e1 by two calls of mlkem1024_poly_getnoise_eta1_4x with four outputs, as  *)
(* for gcc 12 -O2, and e2 by mlkem1024_poly_getnoise_eta2. The lemma for a   *)
(* compression of a polynomial of u is used with the index j of the          *)
(* polynomial reduced to a numeral.                                          *)
(* ------------------------------------------------------------------------- *)

let EN4_SUB_TAC th =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,EN4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,th);;

let LOCAL_FROMBYTES_TAC =
  EN4_SUB_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_POLY_FROMMSG_TAC =
  EN4_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GEN_MATRIX_TAC =
  EN4_SUB_TAC
   (INDCPA_GEN_MATRIX_SPEC
     MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT
     `word 1:int64`);;

let LOCAL_GETNOISE_TAC =
  EN4_SUB_TAC
   MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_GETNOISE_ETA2_TAC =
  EN4_SUB_TAC
   MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_NTT_TAC =
  EN4_SUB_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_MULCACHE_TAC =
  EN4_SUB_TAC
   MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_BASEMUL_TAC =
  EN4_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_INVNTT_TAC =
  EN4_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REDUCE_TAC =
  EN4_SUB_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let EN4_LEMMA_TAC name ilist n =
  USE_THEN name (fun th -> EN4_SUB_TAC th ilist n);;

let EN4_D11_INST j th =
  let e = fst(dest_forall(concl th)) in
  GEN e (CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_LT_CONV)
          (SPEC (mk_small_numeral j) (SPEC e th)));;

let EN4_D11_TAC j ilist n =
  USE_THEN "H_D11" (fun th -> EN4_SUB_TAC (EN4_D11_INST j th) ilist n);;

let EN4_SP n = Printf.sprintf "word_add stackpointer (word %d)" n;;

let EN4_PART v j = if j = 0 then mk_var(v,`:num->int16`) else
  subst [mk_small_numeral(256 * j),`n:num`; mk_var(v,`:num->int16`),
         `v:num->int16`] `\i. (v:num->int16)(n + i)`;;

(*** The coefficients of polynomial j of u for the compression lemma, in the
     form of its precondition after the normalization of the simulation,
     from the ghost for the whole vector ***)

let EN4_D11_PRE_TAC b j s =
  let base = b + 8192 in
  let idx = if j = 0 then "i" else Printf.sprintf "%d + i" (256 * j) in
  let raw = parse_term(Printf.sprintf
    "!i. i < 256 ==> read (memory :> bytes16 (word_add (word_add stackpointer \
     (word %d)) (word(%d + 2 * i)))) (%s:armstate) = (U3:num->int16)(%s)"
    base (512 * j) s idx) in
  let tm = rhs(concl(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV raw)) in
  let ghost = parse_term(Printf.sprintf
    "!i. i < 1024 ==> read (memory :> bytes16 (word_add stackpointer \
     (word(%d + 2 * i)))) (%s:armstate) = (U3:num->int16) i" base s) in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(SPEC (parse_term("("^idx^"):num")) (ASSUME ghost)) THEN
    ANTS_TAC THENL [UNDISCH_TAC `i < 256` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The facts about the stages of the computation other than those given by   *)
(* the tactics in mlkem_native_indcpa.ml: the coefficients of the transposed *)
(* matrix as given by SampleNTT, the bounds on the inputs of the             *)
(* multiplications, the products with the rows of the transposed matrix and  *)
(* with t, and the bounds on the inputs of the compressions.                 *)
(* ------------------------------------------------------------------------- *)

let EN4_MATRIX_TAC b s =
  let addr = parse_term(Printf.sprintf
    "word_add stackpointer (word (%d + 512 * (4 * q + j))):int64" b) in
  SUBGOAL_THEN
   `!q j n. q < 4 /\ j < 4 /\ n < 256
            ==> &0 <= mlkem_sample_ntt (APPEND rho [word q; word j]) n /\
                mlkem_sample_ntt (APPEND rho [word q; word j]) n < &3329`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC MLKEM_SAMPLE_NTT_REJ_BOUND THEN
    EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q j n. q < 4 /\ j < 4 /\ n < 256
            ==> ival((AM:num->int16)(1024 * q + 256 * j + n)) =
                mlkem_sample_ntt (APPEND rho [word q; word j]) n`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    INDCPA_GHOST_SPEC_TAC "AM" `1024 * q + 256 * j + n` THEN
    MP_TAC(SPECL [addr; s; `APPEND (rho:byte list) [word q; word j]`;
                  `k:num`; `n:num`] MLKEM_NATIVE_SAMPLE_COEFF) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    MATCH_MP_TAC READ16_OFFSET_EQ THEN ARITH_TAC;
    ALL_TAC];;

let EN4_AM_INST r j =
  let th = SPECL [mk_small_numeral r; mk_small_numeral j]
    (ASSUME `!q j n. q < 4 /\ j < 4 /\ n < 256
                     ==> ival((AM:num->int16)(1024 * q + 256 * j + n)) =
                         mlkem_sample_ntt (APPEND rho [word q; word j]) n`) in
  CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES; ADD_ASSOC] THENC
            NUM_REDUCE_CONV) th;;

let EN4_AM_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 4096 ==> abs(ival((AM:num->int16) m)) <= &2 pow 12`
  (LABEL_TAC "ambound") THENL
   [X_GEN_TAC `m':num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`1024`; `4`; `m':num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `1024 * 4 = 4096`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:num`; `x:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`256`; `4`; `x:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 4 = 1024`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(INT_ARITH
     `&0 <= x /\ x < &3329 ==> abs(x:int) <= &2 pow 12`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC];;

let EN4_BASEMUL_DEFS =
  [basemul4_even; basemul4_odd; pmul_acc4; pmull_acc4; pmull];;

let EN4_U0_GOAL = `!q p. q < 4 /\ p < 128
       ==> (ival((U0:num->int16)(256 * q + 2 * p)) ==
            &169 *
            ((mlkem_sample_ntt (APPEND rho [word q; word 3]) (2 * p + 1) *
              ival((MC:num->int16)(384 + p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 3]) (2 * p) *
              ival((YH:num->int16)(768 + 2 * p))) +
             (mlkem_sample_ntt (APPEND rho [word q; word 2]) (2 * p + 1) *
              ival(MC(256 + p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 2]) (2 * p) *
              ival(YH(512 + 2 * p))) +
             (mlkem_sample_ntt (APPEND rho [word q; word 1]) (2 * p + 1) *
              ival(MC(128 + p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 1]) (2 * p) *
              ival(YH(256 + 2 * p))) +
             (mlkem_sample_ntt (APPEND rho [word q; word 0]) (2 * p + 1) *
              ival(MC p) +
              mlkem_sample_ntt (APPEND rho [word q; word 0]) (2 * p) *
              ival(YH(2 * p))))) (mod &3329) /\
           (ival(U0(256 * q + 2 * p + 1)) ==
            &169 *
            ((mlkem_sample_ntt (APPEND rho [word q; word 3]) (2 * p + 1) *
              ival(YH(768 + 2 * p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 3]) (2 * p) *
              ival(YH(768 + 2 * p + 1))) +
             (mlkem_sample_ntt (APPEND rho [word q; word 2]) (2 * p + 1) *
              ival(YH(512 + 2 * p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 2]) (2 * p) *
              ival(YH(512 + 2 * p + 1))) +
             (mlkem_sample_ntt (APPEND rho [word q; word 1]) (2 * p + 1) *
              ival(YH(256 + 2 * p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 1]) (2 * p) *
              ival(YH(256 + 2 * p + 1))) +
             (mlkem_sample_ntt (APPEND rho [word q; word 0]) (2 * p + 1) *
              ival(YH(2 * p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 0]) (2 * p) *
              ival(YH(2 * p + 1))))) (mod &3329)`;;

let EN4_U0_TAC b s =
  INDCPA_GHOST_TAC "U0" (b + 8192) 1024 s THEN
  SUBGOAL_THEN EN4_U0_GOAL ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THENL
     (map (fun q -> INDCPA_BASEMULK_ROW_TAC 4 "U0" (b + 8192 + 512 * q)
                     "ambound" (map (EN4_AM_INST q) [0;1;2;3])
                     EN4_BASEMUL_DEFS) [0;1;2;3]);
    ALL_TAC];;

let EN4_TT_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 1024 ==> abs(ival((TT:num->int16) m)) <= &2 pow 12`
  (LABEL_TAC "ttbound") THENL
   [X_GEN_TAC `m':num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(num_of_bytelist ek DIV 2 EXP (12 * m')) MOD 2 EXP 12 < 4096`
    MP_TAC THENL [REWRITE_TAC[ARITH_RULE `4096 = 2 EXP 12`; MOD_LT_EQ] THEN
                  CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    SPEC_TAC(`(num_of_bytelist ek DIV 2 EXP (12 * m')) MOD 2 EXP 12`,
             `f:num`) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `ival(word f:int16) = &f` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_WORD_SMALL THEN UNDISCH_TAC `f < 4096` THEN ARITH_TAC;
      REWRITE_TAC[INT_ABS_NUM; INT_OF_NUM_POW; INT_OF_NUM_LE] THEN
      UNDISCH_TAC `f < 4096` THEN ARITH_TAC];
    ALL_TAC];;

let EN4_V0_GOAL = `!p. p < 128
       ==> (ival((V0:num->int16)(2 * p)) ==
            &169 *
            ((ival((TT:num->int16)(768 + 2 * p + 1)) *
              ival((MC:num->int16)(384 + p)) +
              ival(TT(768 + 2 * p)) * ival((YH:num->int16)(768 + 2 * p))) +
             (ival(TT(512 + 2 * p + 1)) * ival(MC(256 + p)) +
              ival(TT(512 + 2 * p)) * ival(YH(512 + 2 * p))) +
             (ival(TT(256 + 2 * p + 1)) * ival(MC(128 + p)) +
              ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p))) +
             (ival(TT(2 * p + 1)) * ival(MC p) +
              ival(TT(2 * p)) * ival(YH(2 * p))))) (mod &3329) /\
           (ival(V0(2 * p + 1)) ==
            &169 *
            ((ival(TT(768 + 2 * p + 1)) * ival(YH(768 + 2 * p)) +
              ival(TT(768 + 2 * p)) * ival(YH(768 + 2 * p + 1))) +
             (ival(TT(512 + 2 * p + 1)) * ival(YH(512 + 2 * p)) +
              ival(TT(512 + 2 * p)) * ival(YH(512 + 2 * p + 1))) +
             (ival(TT(256 + 2 * p + 1)) * ival(YH(256 + 2 * p)) +
              ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p + 1))) +
             (ival(TT(2 * p + 1)) * ival(YH(2 * p)) +
              ival(TT(2 * p)) * ival(YH(2 * p + 1))))) (mod &3329)`;;

let EN4_V0_TAC b s =
  INDCPA_GHOST_TAC "V0" (b + 18432) 256 s THEN
  SUBGOAL_THEN EN4_V0_GOAL ASSUME_TAC THENL
   [INDCPA_BASEMULK_ROW_TAC 4 "V0" (b + 18432) "ttbound" [] EN4_BASEMUL_DEFS;
    ALL_TAC];;

let EN4_COMPRESS_POST_TAC v y =
  let vt = mk_var(v,`:num->int16`) in
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && mem vt (frees(concl th)) &&
    INDCPA_HAS_CONST "nsum" (concl th))) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC VAL_LT_OF_IVAL_REM THEN EXISTS_TAC y THEN ASM_SIMP_TAC[];
    DISCH_TAC];;

let EN4_FINAL_TAC =
  REWRITE_TAC[ARITH_RULE `1568 = 1408 + 160`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`ek:byte list`; `msg:byte list`; `r:byte list`;
                `TT:num->int16`; `YH:num->int16`; `MC:num->int16`;
                `E1:num->int16`; `E2:num->int16`; `MU:num->int16`;
                `U0:num->int16`; `V0:num->int16`; `U1:num->int16`;
                `V1:num->int16`; `U3:num->int16`; `V4:num->int16`]
          (REWRITE_RULE[ASSUME `mlkem_slice 1536 32 ek = rho`]
            KPKE_ENCRYPT_K4_RESULT)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
           REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
    SIMP_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy (the      *)
(* latter for the callees), as for gcc 12 -O2, with the frame of this code:  *)
(* the 19184 bytes of the function and the 3680 of mlkem1024_gen_matrix      *)
(* below them. The proof is by cases on whether the stack pointer is a       *)
(* multiple of 32, which gives the address b of the buffers.                 *)
(* ------------------------------------------------------------------------- *)

let EN4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`c:int64`; `m:int64`; `pk:int64`; `coins:int64`; `ek:byte list`;
    `msg:byte list`; `r:byte list`; `guard:int64`; `mf:int64`; `mc:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 22864 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 22864):int64)` THEN
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
   `!i j. i < 4 /\ j < 4
          ==> mlkem_samplentt_terminates
               (APPEND (mlkem_slice 1536 32 ek) [word j; word i])` THEN
  ABBREV_TAC `rho = mlkem_slice 1536 32 ek` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`4`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN
   `!i j. i < 4 /\ j < 4
          ==> 256 <= LENGTH(FILTER (\x. val x < 3329)
                      (MAP (word_zx:12 word->16 word)
                        (wordlist_of_num (336 + 112 * k)
                          (num_of_bytelist
                            (list_of_seq
                              (shake128 (APPEND rho [word i; word j]))
                              (504 + 168 * k))))))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `i:num`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(rho:byte list) = 32` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ];
    ALL_TAC] THEN
  X_CHOOSE_THEN `fa1:int64->int64->num->(uarch_event)list`
    (LABEL_TAC "H_ADD1") EN4_ADD1 THEN
  X_CHOOSE_THEN `fa2:int64->int64->num->(uarch_event)list`
    (LABEL_TAC "H_ADD2") EN4_ADD2 THEN
  X_CHOOSE_THEN `fa3:int64->int64->num->(uarch_event)list`
    (LABEL_TAC "H_ADD3") EN4_ADD3 THEN
  X_CHOOSE_THEN `fd11:int64->int64->num->num->int64->(uarch_event)list`
    (LABEL_TAC "H_D11") EN4_D11 THEN
  X_CHOOSE_THEN `fd5:int64->int64->num->int64->(uarch_event)list`
    (LABEL_TAC "H_D5") EN4_D5;;

let EN4_CASE_TAC b =
  let st n = "s"^string_of_int n in
  let sp n = EN4_SP n in
  let part = EN4_PART in
  ENSURES_INIT_TAC "s0" THEN EN4_PK_TAC THEN
  POLYVEC_INLINE_SPLIT_TAC POLYVEC_FROMBYTES_SPLIT_GEN `pk:int64` 4 THEN
  ABBREV_TAC `ekt = num_of_bytelist ek MOD 2 EXP 12288` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN

  (*** The setup, the public vector t in a loop of four calls, the
       message ***)

  ARM_STEPS_TAC EN4_EXEC (1--5) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN4_EXEC (6--8) THEN EN4_BUFFER_TAC THEN
  ARM_STEPS_TAC EN4_EXEC (9--22) THEN
  MAP_EVERY (fun q ->
    ARM_STEPS_TAC EN4_EXEC ((23 + 8 * q)--(26 + 8 * q)) THEN
    EN4_NORMALIZE_TAC THEN
    LOCAL_FROMBYTES_TAC
     [`read X0 s`; `read X1 s`;
      subst [mk_small_numeral(3072 * q),`n:num`]
       `(ekt DIV 2 EXP n) MOD 2 EXP 3072`; `pc:num`; `read X30 s`]
     (27 + 8 * q) THEN
    ARM_STEPS_TAC EN4_EXEC ((28 + 8 * q)--(30 + 8 * q)) THEN
    EN4_PC_TAC (st(30 + 8 * q))) [0;1;2;3] THEN
  EN4_NORMALIZE_TAC THEN
  POLYVEC_INLINE_JOIN_TAC 4
   [POLYVEC_FROMBYTES_FIELD_GEN; ADD_CLAUSES; ARITH_RULE `4096 = 2 EXP 12`]
   (PV_FROMBYTES_POST 4 (sp(b + 12288)) "ekt" (st 54)) THEN
  EN4_TT_TAC b (st 54) THEN
  ARM_STEPS_TAC EN4_EXEC (55--68) THEN
  LOCAL_POLY_FROMMSG_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist msg`; `pc:num`;
    `read X30 s`] 69 THEN
  EN4_MU_TAC b (st 69) THEN

  (*** The transposed matrix ***)

  EN4_SEED_TAC b (st 69) THEN
  ARM_STEPS_TAC EN4_EXEC (70--74) THEN INLINE_GOT_TAC THEN
  LOCAL_GEN_MATRIX_TAC
   [`read X0 s`; `read X1 s`; `rho:byte list`; `k:num`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 75 THEN
  INDCPA_GHOST_TAC "AM" b 4096 (st 75) THEN
  EN4_MATRIX_TAC b `s75:armstate` THEN

  (*** The noise: y and e1 from two calls with four outputs, then e2 ***)

  ARM_STEPS_TAC EN4_EXEC (76--89) THEN
  INDCPA_NONZERO_TAC 22864 (b + 15872) THEN INDCPA_NONCE_TAC 3 THEN
  INLINE_GOT_TAC THEN
  LOCAL_GETNOISE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `r:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 3:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 90 THEN
  INDCPA_NOISE_TAC "YS" (b + 14336) 4 "r" "word j" (st 90) THEN
  INDCPA_DISCARD_LETS_TAC THEN
  ARM_STEPS_TAC EN4_EXEC (91--101) THEN
  INDCPA_NONZERO_TAC 22864 (b + 11776) THEN INDCPA_NONCE_TAC 7 THEN
  INLINE_GOT_TAC THEN
  LOCAL_GETNOISE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `r:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 7:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 102 THEN
  INDCPA_NOISE_TAC "E1" (b + 10240) 4 "r" "word(4 + j)" (st 102) THEN
  INDCPA_DISCARD_LETS_TAC THEN
  ARM_STEPS_TAC EN4_EXEC (103--109) THEN INLINE_GOT_TAC THEN
  LOCAL_GETNOISE_ETA2_TAC
   [`read X0 s`; `read X1 s`; `r:byte list`; `read X2 s`; `guard:int64`;
    `mc:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 110 THEN
  INDCPA_NOISE1_TAC "E2" (b + 17408) "r" "word 8" (st 110) THEN
  INDCPA_DISCARD_LETS_TAC THEN

  (*** The NTT of y and its multiplication cache, in a loop of four
       calls ***)

  POLYVEC_GHOST_SPLIT_TAC "YS" (b + 14336) 4 (st 110) THEN
  MAP_EVERY (fun (j,k0,k1) ->
    ARM_STEPS_TAC EN4_EXEC (k0--k1) THEN
    LOCAL_NTT_TAC [`read X0 s`; part "YS" j; `pc:num`; `read X30 s`]
      (k1 + 1)) [0,111,112; 1,114,115; 2,117,118; 3,120,125] THEN
  POLYVEC_INLINE_JOIN_TAC 4 [] (PV_NTT_POST 4 (sp(b + 14336)) "YS" (st 126))
  THEN
  INDCPA_NTT_TAC "YH" (b + 14336) 4 "YS" "r" "word j" (st 126) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "YS" 1024 THEN
  POLYVEC_GHOST_SPLIT_TAC "YH" (b + 14336) 4 (st 126) THEN
  MAP_EVERY (fun q ->
    ARM_STEPS_TAC EN4_EXEC ((127 + 8 * q)--(130 + 8 * q)) THEN
    EN4_NORMALIZE_TAC THEN
    LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; part "YH" q; `pc:num`;
                        `read X30 s`] (131 + 8 * q) THEN
    ARM_STEPS_TAC EN4_EXEC ((132 + 8 * q)--(134 + 8 * q)) THEN
    EN4_NORMALIZE_TAC THEN EN4_PC_TAC (st(134 + 8 * q))) [0;1;2;3] THEN
  POLYVEC_INLINE_JOIN_TAC 4 []
   (PV_MULCACHE_POST 4 (sp(b + 16384)) "YH" (st 158)) THEN
  INDCPA_MULCACHE_TAC "MC" (b + 16384) 4 "YH" (st 158) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "YH" 1024 THEN

  (*** The products with the transposed matrix, one row per iteration, and
       with t ***)

  ARM_STEPS_TAC EN4_EXEC (159--163) THEN
  MAP_EVERY (fun q ->
    let a = (b + 2048 * q,"AM",1024 * q)
    and y = (b + 14336,"YH") and t = (b + 16384,"MC") in
    ARM_STEPS_TAC EN4_EXEC ((164 + 10 * q)--(169 + 10 * q)) THEN
    EN4_NORMALIZE_TAC THEN
    INDCPA_BASEMULK_PRE_TAC 4 a y t (st(169 + 10 * q)) THEN
    LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 4 ("AM",1024 * q) "YH" "MC")
      (170 + 10 * q) THEN
    INDCPA_BASEMULK_DROP_PRE_TAC 4 a y t THEN
    ARM_STEPS_TAC EN4_EXEC ((171 + 10 * q)--(173 + 10 * q)) THEN
    EN4_NORMALIZE_TAC THEN EN4_PC_TAC (st(173 + 10 * q))) [0;1;2;3] THEN
  EN4_AM_BOUND_TAC THEN EN4_U0_TAC b (st 203) THEN
  ARM_STEPS_TAC EN4_EXEC (204--210) THEN
  INDCPA_BASEMULK_PRE_TAC 4 (b + 12288,"TT",0) (b + 14336,"YH")
    (b + 16384,"MC") (st 210) THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 4 ("TT",0) "YH" "MC") 211 THEN
  INDCPA_BASEMULK_DROP_PRE_TAC 4 (b + 12288,"TT",0) (b + 14336,"YH")
    (b + 16384,"MC") THEN
  EN4_TT_BOUND_TAC THEN EN4_V0_TAC b (st 211) THEN

  (*** The inverse NTTs ***)

  POLYVEC_GHOST_SPLIT_TAC "U0" (b + 8192) 4 (st 211) THEN
  MAP_EVERY (fun (j,k0,k1) ->
    ARM_STEPS_TAC EN4_EXEC (k0--k1) THEN
    LOCAL_INVNTT_TAC [`read X0 s`; part "U0" j; `pc:num`; `read SP s`;
                      `read X30 s`] (k1 + 1))
   [0,212,213; 1,215,216; 2,218,219; 3,221,222] THEN
  POLYVEC_INLINE_JOIN_TAC 4 [] (PV_INVNTT_POST 4 (sp(b + 8192)) "U0" (st 223))
  THEN
  INDCPA_INVNTT_TAC "U1" (b + 8192) 4 "U0" (st 223) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "U0" 1024 THEN
  ARM_STEPS_TAC EN4_EXEC (224--225) THEN
  LOCAL_INVNTT_TAC [`read X0 s`; `V0:num->int16`; `pc:num`; `read SP s`;
                    `read X30 s`] 226 THEN
  INDCPA_INVNTT1_TAC "V1" (b + 18432) "V0" (st 226) THEN

  (*** Adding the noise and the message, in the inlined loops ***)

  POLYVEC_GHOST_SPLIT_TAC "U1" (b + 8192) 4 (st 226) THEN
  POLYVEC_GHOST_SPLIT_TAC "E1" (b + 10240) 4 (st 226) THEN
  ARM_STEPS_TAC EN4_EXEC (227--227) THEN
  MAP_EVERY (fun j ->
    let k0 = 228 + 6 * j in
    ARM_STEPS_TAC EN4_EXEC (k0--k0) THEN EN4_NORMALIZE_TAC THEN
    EN4_LEMMA_TAC "H_ADD1"
     [`read events s`; `read X19 s`; `read X1 s`; part "U1" j; part "E1" j;
      `pc:num`] (k0 + 1) THEN
    ARM_STEPS_TAC EN4_EXEC ((k0 + 2)--(k0 + 5)) THEN
    EN4_NORMALIZE_TAC THEN EN4_PC_TAC (st(k0 + 5))) [0;1;2;3] THEN
  POLYVEC_GHOST_DROP_ALL_TAC "U1" 1024 THEN
  POLYVEC_GHOST_DROP_ALL_TAC "E1" 1024 THEN
  ARM_STEPS_TAC EN4_EXEC (252--256) THEN EN4_NORMALIZE_TAC THEN
  EN4_LEMMA_TAC "H_ADD2"
   [`read events s`; `read X1 s`; `read X3 s`; `V1:num->int16`;
    `E2:num->int16`; `pc:num`] 257 THEN
  ARM_STEPS_TAC EN4_EXEC (258--259) THEN EN4_NORMALIZE_TAC THEN
  EN4_LEMMA_TAC "H_ADD3"
   [`read events s`; `read X0 s`; `read X1 s`;
    `\i. word_add ((V1:num->int16) i) ((E2:num->int16) i)`;
    `MU:num->int16`; `pc:num`] 260 THEN

  (*** The reductions ***)

  MAP_EVERY (fun (j,k0,k1) ->
    let x = if j = 0 then
      `\i. word_add ((U1:num->int16) i) ((E1:num->int16) i)` else
      subst [mk_small_numeral(256 * j),`n:num`]
       `\i. word_add ((U1:num->int16)(n + i)) ((E1:num->int16)(n + i))` in
    ARM_STEPS_TAC EN4_EXEC (k0--k1) THEN
    LOCAL_REDUCE_TAC [`read X0 s`; x; `pc:num`; `read X30 s`] (k1 + 1))
   [0,261,262; 1,264,265; 2,267,268; 3,270,271] THEN
  POLYVEC_INLINE_JOIN_TAC 4 []
   (PV_REDUCE_POST 4 (sp(b + 8192))
     "\\i. word_add ((U1:num->int16) i) ((E1:num->int16) i)" (st 272)) THEN
  INDCPA_REDUCE_TAC "U3" (b + 8192) 1024
    "word_add ((U1:num->int16) i) ((E1:num->int16) i)" (st 272) THEN
  ARM_STEPS_TAC EN4_EXEC (273--275) THEN
  LOCAL_REDUCE_TAC
   [`read X0 s`;
    `\i. word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i)`;
    `pc:num`; `read X30 s`] 276 THEN
  INDCPA_REDUCE_TAC "V4" (b + 18432) 256
    "word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i)) \
     ((MU:num->int16) i)" (st 276) THEN

  (*** The compression and encoding of u, in the inlined loop over its
       polynomials, and of v ***)

  ARM_STEPS_TAC EN4_EXEC (277--283) THEN
  MAP_EVERY (fun j ->
    let k0 = 284 + 9 * j in
    ARM_STEPS_TAC EN4_EXEC (k0--(k0 + 3)) THEN
    EN4_NORMALIZE_TAC THEN
    EN4_D11_PRE_TAC b j (st(k0 + 3)) THEN
    EN4_D11_TAC j
     [`read events s`; `read X9 s`; INDCPA_SP(b + 8192); part "U3" j;
      `pc:num`; `read SP s`] (k0 + 4) THEN
    ARM_STEPS_TAC EN4_EXEC ((k0 + 5)--(k0 + 8)) THEN
    EN4_PC_TAC (st(k0 + 8))) [0;1;2;3] THEN
  EN4_COMPRESS_DU_TAC (st 319) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "U3" 1024 THEN
  EN4_COMPRESS_POST_TAC "U3"
   `ival(word_add ((U1:num->int16) i) ((E1:num->int16) i))` THEN
  ARM_STEPS_TAC EN4_EXEC (320--328) THEN
  EN4_LEMMA_TAC "H_D5"
   [`read events s`; `read X19 s`; `read X26 s`; `V4:num->int16`; `pc:num`;
    `read SP s`] 329 THEN
  EN4_COMPRESS_POST_TAC "V4"
   `ival(word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i))` THEN

  (*** Zeroing the buffers, the stack guard, the return ***)

  INDCPA_MEMSET_LABEL_TAC THEN
  INDCPA_MEMSETS_TAC EN4_EXEC
   [330,333; 339,343; 349,353; 359,362; 368,371; 377,380; 386,390;
    396,399; 405,408] THEN
  ARM_STEPS_TAC EN4_EXEC (414--416) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN4_EXEC (417--432) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN EN4_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!c m pk coins (ek:byte list) (msg:byte list) (r:byte list)
    guard mf mc ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        LENGTH ek = 1568 /\ LENGTH msg = 32 /\ LENGTH r = 32 /\
        (!i j. i < 4 /\ j < 4
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 1536 32 ek) [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 22864),22864) /\
        nonoverlapping (c,1568) (word_sub stackpointer (word 22864),22864) /\
        nonoverlapping (pk,1568) (word pc,libmlkem_size) /\
        ALLPAIRS nonoverlapping
         [(c,1568); (word_sub stackpointer (word 22864),22864)]
         [(m,32); (pk,1568); (coins,32); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8);
          (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlkem1024_indcpa_enc) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [c; m; pk; coins] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(m,32)) s = num_of_bytelist msg /\
                  read (memory :> bytes(pk,1568)) s = num_of_bytelist ek /\
                  read (memory :> bytes(coins,32)) s = num_of_bytelist r)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(c,1568)) s =
                  num_of_bytelist(kpke_encrypt mlkem1024 ek msg r) /\
                  C_RETURN s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(c,1568);
                memory :> bytes(word_sub stackpointer (word 22864),22864)])`;;

let MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset (for mlkem1024_gen_matrix) and the safety contract for memcpy, as  *)
(* for gcc 12 -O2. The events depend only on the addresses and on rho, the   *)
(* last 32 bytes of the public key, through the samples of SampleNTT for the *)
(* transposed matrix, but not on the message or the randomness. The inlined  *)
(* loops and compressions use the same lemmas as the correctness proof, with *)
(* the contents of the memory as the data.                                   *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let EN4_SAFE_TEMPLATE =
 `\(c:int64) (m:int64) (pk:int64) (coins:int64) (guard:int64) (mf:int64)
   (mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64)
   (rho:byte list).
   if aligned 32 stackpointer
   then f_ev_a c m pk coins guard mf mc pc stackpointer returnaddress rho
   else f_ev_u c m pk coins guard mf mc pc stackpointer returnaddress rho
   :(uarch_event)list`;;

let EN4_SAFE_ALLOWED =
  [`pc:num`; `c:int64`; `m:int64`; `pk:int64`; `coins:int64`;
   `guard:int64`; `mf:int64`; `mc:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `rho:byte list`];;

let EN4_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th)
    then ASSUME_CALLEE_SAFETY_TAILED_TAC
          (INDCPA_GEN_MATRIX_SAFE_SPEC
            (MATCH_MP
              MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
              th) `word 1:int64`) "H_GM" THEN
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
        MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
        (CONJ th1 th2) in
      ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC gth "H_GETNOISE" THEN
      ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC
       (MATCH_MP
         MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
         th2) "H_ETA2")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE)
    "H_FROMMSG" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_BASEMUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE)
    "H_INVNTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC EN4_ADD1 "H_ADD1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC EN4_ADD2 "H_ADD2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC EN4_ADD3 "H_ADD3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC EN4_D11 "H_D11" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC EN4_D5 "H_D5" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_REDUCE" THEN
  CONCRETIZE_F_EVENTS_TAC EN4_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 22864):int64)` THEN
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
   `!i j. i < 4 /\ j < 4
          ==> mlkem_samplentt_terminates
               (APPEND (mlkem_slice 1536 32 ek) [word j; word i])` THEN
  ABBREV_TAC `rho = mlkem_slice 1536 32 ek` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`4`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN
   `!i j. i < 4 /\ j < 4
          ==> 256 <= LENGTH(FILTER (\x. val x < 3329)
                      (MAP (word_zx:12 word->16 word)
                        (wordlist_of_num (336 + 112 * k)
                          (num_of_bytelist
                            (list_of_seq
                              (shake128 (APPEND rho [word i; word j]))
                              (504 + 168 * k))))))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `i:num`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(rho:byte list) = 32` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ];
    ALL_TAC];;

let EN4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,EN4_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref EN4_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

(*** The compression of polynomial j of u, with j reduced to a numeral ***)

let EN4_SAFE_D11_TAC j ilist n =
  REMOVE_THEN "H_D11" (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,EN4_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,EN4_D11_INST j safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref EN4_SAFE_ALLOWED); LABEL_TAC "H_D11" safety_th]);;

(*** The contents of a polynomial at the address in a register, as the data
     of the lemmas for the loops ***)

let EN4_CONTENTS r =
  let a = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                          r),`s:armstate`) in
  vsubst [a,`a:int64`]
   `\i. read(memory :> bytes16(word_add a (word(2 * i)))) (s:armstate)`;;

let EN4_CONTENTS_POLY b j =
  let a = INDCPA_SP(b + 8192) in
  subst [a,`a:int64`; mk_small_numeral(512 * j),`n:num`]
   `\i. read(memory :> bytes16(word_add a (word(n + 2 * i)))) (s:armstate)`;;

let EN4_SAFE_CASE_TAC b =
  let e = `e:(uarch_event)list` in
  let x n = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            mk_const("X"^string_of_int n,[])),`s:armstate`) in
  let rest = [`pc:num`; `read SP s`; `read X30 s`] in
  let rest0 = [`pc:num`; `read X30 s`] in
  let call = EN4_SAFE_CALL_TAC in
  ENSURES_INIT_TAC "s0" THEN EN4_PK_TAC THEN
  ARM_STEPS_TAC EN4_EXEC (1--5) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN4_EXEC (6--8) THEN EN4_BUFFER_TAC THEN
  ARM_STEPS_TAC EN4_EXEC (9--22) THEN
  MAP_EVERY (fun q ->
    ARM_STEPS_TAC EN4_EXEC ((23 + 8 * q)--(26 + 8 * q)) THEN
    EN4_NORMALIZE_TAC THEN
    call "H_FROMBYTES" ([e; x 0; x 1] @ rest0) (27 + 8 * q) THEN
    ARM_STEPS_TAC EN4_EXEC ((28 + 8 * q)--(30 + 8 * q)) THEN
    EN4_PC_TAC ("s"^string_of_int(30 + 8 * q))) [0;1;2;3] THEN
  ARM_STEPS_TAC EN4_EXEC (55--68) THEN
  call "H_FROMMSG" ([e; x 0; x 1] @ rest0) 69 THEN
  EN4_SEED_TAC b "s69" THEN
  ARM_STEPS_TAC EN4_EXEC (70--74) THEN INLINE_GOT_TAC THEN
  call "H_GM" ([e; x 0; x 1; `rho:byte list`; `k:num`; `guard:int64`] @ rest)
   75 THEN
  ARM_STEPS_TAC EN4_EXEC (76--89) THEN
  INDCPA_NONZERO_TAC 22864 (b + 15872) THEN INLINE_GOT_TAC THEN
  call "H_GETNOISE" ([e; x 0; x 1; x 2; x 3; x 4; `guard:int64`] @ rest)
   90 THEN
  ARM_STEPS_TAC EN4_EXEC (91--101) THEN
  INDCPA_NONZERO_TAC 22864 (b + 11776) THEN INLINE_GOT_TAC THEN
  call "H_GETNOISE" ([e; x 0; x 1; x 2; x 3; x 4; `guard:int64`] @ rest)
   102 THEN
  ARM_STEPS_TAC EN4_EXEC (103--109) THEN INLINE_GOT_TAC THEN
  call "H_ETA2" ([e; x 0; x 1; x 2; `guard:int64`] @ rest) 110 THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC EN4_EXEC (k0--k1) THEN
    call "H_NTT" ([e; x 0] @ rest0) (k1 + 1))
   [111,112; 114,115; 117,118; 120,125] THEN
  MAP_EVERY (fun q ->
    ARM_STEPS_TAC EN4_EXEC ((127 + 8 * q)--(130 + 8 * q)) THEN
    EN4_NORMALIZE_TAC THEN
    call "H_MULCACHE" ([e; x 0; x 1] @ rest0) (131 + 8 * q) THEN
    ARM_STEPS_TAC EN4_EXEC ((132 + 8 * q)--(134 + 8 * q)) THEN
    EN4_NORMALIZE_TAC THEN EN4_PC_TAC ("s"^string_of_int(134 + 8 * q)))
   [0;1;2;3] THEN
  ARM_STEPS_TAC EN4_EXEC (159--163) THEN
  MAP_EVERY (fun q ->
    ARM_STEPS_TAC EN4_EXEC ((164 + 10 * q)--(169 + 10 * q)) THEN
    EN4_NORMALIZE_TAC THEN
    call "H_BASEMUL" ([e; x 1; x 2; x 3; x 0] @ rest0) (170 + 10 * q) THEN
    ARM_STEPS_TAC EN4_EXEC ((171 + 10 * q)--(173 + 10 * q)) THEN
    EN4_NORMALIZE_TAC THEN EN4_PC_TAC ("s"^string_of_int(173 + 10 * q)))
   [0;1;2;3] THEN
  ARM_STEPS_TAC EN4_EXEC (204--210) THEN
  call "H_BASEMUL" ([e; x 1; x 2; x 3; x 0] @ rest0) 211 THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC EN4_EXEC (k0--k1) THEN
    call "H_INVNTT" ([e; x 0] @ rest) (k1 + 1))
   [212,213; 215,216; 218,219; 221,222; 224,225] THEN
  ARM_STEPS_TAC EN4_EXEC (227--227) THEN
  MAP_EVERY (fun j ->
    let k0 = 228 + 6 * j in
    ARM_STEPS_TAC EN4_EXEC (k0--k0) THEN EN4_NORMALIZE_TAC THEN
    call "H_ADD1"
     [e; x 19; x 1; EN4_CONTENTS `X19`; EN4_CONTENTS `X1`; `pc:num`]
     (k0 + 1) THEN
    ARM_STEPS_TAC EN4_EXEC ((k0 + 2)--(k0 + 5)) THEN
    EN4_NORMALIZE_TAC THEN EN4_PC_TAC ("s"^string_of_int(k0 + 5))) [0;1;2;3]
  THEN
  ARM_STEPS_TAC EN4_EXEC (252--256) THEN EN4_NORMALIZE_TAC THEN
  call "H_ADD2" [e; x 1; x 3; EN4_CONTENTS `X1`; EN4_CONTENTS `X3`; `pc:num`]
   257 THEN
  ARM_STEPS_TAC EN4_EXEC (258--259) THEN EN4_NORMALIZE_TAC THEN
  call "H_ADD3" [e; x 0; x 1; EN4_CONTENTS `X0`; EN4_CONTENTS `X1`; `pc:num`]
   260 THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC EN4_EXEC (k0--k1) THEN
    call "H_REDUCE" ([e; x 0] @ rest0) (k1 + 1))
   [261,262; 264,265; 267,268; 270,271; 273,275] THEN
  ARM_STEPS_TAC EN4_EXEC (277--283) THEN
  MAP_EVERY (fun j ->
    let k0 = 284 + 9 * j in
    ARM_STEPS_TAC EN4_EXEC (k0--(k0 + 3)) THEN EN4_NORMALIZE_TAC THEN
    EN4_SAFE_D11_TAC j
     [e; x 9; INDCPA_SP(b + 8192); EN4_CONTENTS_POLY b j; `pc:num`;
      `read SP s`] (k0 + 4) THEN
    ARM_STEPS_TAC EN4_EXEC ((k0 + 5)--(k0 + 8)) THEN
    EN4_PC_TAC ("s"^string_of_int(k0 + 8))) [0;1;2;3] THEN
  ARM_STEPS_TAC EN4_EXEC (320--328) THEN
  call "H_D5" [e; x 19; x 26; EN4_CONTENTS `X26`; `pc:num`;
               `read SP s`] 329 THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC EN4_EXEC (k0--k) THEN LIBC_PLT_TAC EN4_EXEC k THEN
    LIBC_SAFE_CALL_TAC "H_MEMSET" EN4_EXEC
     [e; x 0; x 1; x 2; `read X30 s`] (ref EN4_SAFE_ALLOWED) (k + 5))
   [330,333; 339,343; 349,353; 359,362; 368,371; 377,380; 386,390;
    396,399; 405,408] THEN
  ARM_STEPS_TAC EN4_EXEC (414--416) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN4_EXEC (417--432) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MEMACCESS_DROP_ZERO_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
   memset_full_contract mf ea el ev /\ memcpy_safety_contract mc ea el ev
   ==> exists f_events.
        forall e c m pk coins (ek:byte list) guard pc stackpointer
               returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH ek = 1568 /\
          (!i j. i < 4 /\ j < 4
                 ==> mlkem_samplentt_terminates
                      (APPEND (mlkem_slice 1536 32 ek) [word j; word i])) /\
          nonoverlapping (word 0,1)
           (word_sub stackpointer (word 22864),22864) /\
          nonoverlapping (c,1568)
           (word_sub stackpointer (word 22864),22864) /\
          nonoverlapping (pk,1568) (word pc,libmlkem_size) /\
          ALLPAIRS nonoverlapping
           [(c,1568); (word_sub stackpointer (word 22864),22864)]
           [(m,32); (pk,1568); (coins,32); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlkem1024_indcpa_enc) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [c; m; pk; coins] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(pk,1568)) s = num_of_bytelist ek /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events c m pk coins guard mf mc pc
                              (word_sub stackpointer (word 22864))
                              returnaddress (mlkem_slice 1536 32 ek) /\
                       memaccess_inbounds e2
                        [m,32; pk,1568; coins,32; c,1568;
                         word_sub stackpointer (word 22864),22864;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + mlkem_poly_cbd2_consts),64;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlk_poly_invntt_tomont_c_consts),32]
                        [c,1568; word_sub stackpointer (word 22864),22864]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(c,1568);
                  memory :> bytes(word_sub stackpointer (word 22864),22864)])`;;

let MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT;;
