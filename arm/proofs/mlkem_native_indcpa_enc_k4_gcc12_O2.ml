(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The encryption of K-PKE for ML-KEM-1024 (FIPS 203 Algorithm 14). This is  *)
(* the code for mlkem1024_indcpa_enc from mlkem-native's portable C          *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* It decodes the vector t in the NTT domain from the encryption key and the *)
(* message m from its 32 bytes, generates the transposed matrix from rho     *)
(* (the last 32 bytes of the key), samples y, e1 and e2 from the randomness  *)
(* r, and computes u = NTT^-1(A^T NTT(y)) + e1 (the products of the rows of  *)
(* A^T and NTT(y) in a loop) and v = NTT^-1(t^T NTT(y)) + e2 + mu, where mu  *)
(* is m decompressed. It writes the compressions of u and v as the           *)
(* ciphertext, zeroing its buffers. It is verified in the whole image (see   *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0xbe0, using   *)
(* the theorems for mlkem1024_polyvec_frombytes, mlkem_poly_frommsg,         *)
(* mlkem1024_gen_matrix, mlkem1024_poly_getnoise_eta1_4x,                    *)
(* mlkem1024_poly_getnoise_eta2, mlkem1024_polyvec_ntt,                      *)
(* mlkem1024_polyvec_mulcache_compute,                                       *)
(* mlkem1024_polyvec_basemul_acc_montgomery_cached,                          *)
(* mlkem1024_polyvec_invntt_tomont, mlkem_poly_invntt_tomont,                *)
(* mlkem1024_polyvec_add, mlkem_poly_add, mlkem1024_polyvec_reduce,          *)
(* mlkem_poly_reduce, mlkem1024_polyvec_compress_du and                      *)
(* mlkem_poly_compress_d5 in the image, and the contract for memset.         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_polyvec_frombytes_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_frommsg_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_gen_matrix_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_getnoise_eta1_4x_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_getnoise_eta2_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_ntt_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_mulcache_compute_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_basemul_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_invntt_tomont_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_invntt_tomont_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_add_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_add_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_reduce_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_reduce_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_compress_du_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_compress_d5_gcc12_O2.ml";;
needs "arm/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image:

    be0: mov     x12, #0x4ad0
    be4: sub     sp, sp, x12
    be8: mov     x5, #0x4400
    bec: stp     x19, x20, [sp, #16]
    bf0: add     x19, sp, #0xaf
    bf4: and     x19, x19, #0xffffffffffffffe0
    bf8: mov     x20, x2
    bfc: add     x4, x19, #0x3, lsl #12
    c00: adrp    x2, 1f000 <mlk_zetas+0x18c80>
    c04: ldr     x2, [x2, #4088]
    c08: stp     x21, x22, [sp, #32]
    c0c: mov     x21, x3
    c10: stp     x23, x24, [sp, #48]
    c14: mov     x3, #0x2800
    c18: add     x24, x19, x3
    c1c: stp     x25, x26, [sp, #64]
    c20: mov     x22, x1
    c24: mov     x1, x20
    c28: stp     x27, x28, [sp, #80]
    c2c: add     x28, x19, x5
    c30: add     x23, x19, #0x4, lsl #12
    c34: str     x30, [sp, #96]
    c38: mov     x26, x19
    c3c: stp     x0, x4, [sp, #120]
    c40: mov     x0, x4
    c44: ldr     x3, [x2]
    c48: str     x3, [sp, #19144]
    c4c: mov     x3, #0x0
    c50: bl      17b0 <mlkem1024_polyvec_frombytes>
    c54: ldr     q0, [x20, #1536]
    c58: mov     x6, #0x4a00
    c5c: ldr     q1, [x20, #1552]
    c60: add     x2, x19, x6
    c64: mov     x8, #0x3800
    c68: mov     x7, #0x4600
    c6c: add     x20, x19, x8
    c70: add     x0, x19, x7
    c74: mov     x1, x22
    c78: mov     x25, x2
    c7c: stp     q0, q1, [x2]
    c80: str     x0, [sp, #136]
    c84: bl      22e0 <mlkem_poly_frommsg>
    c88: mov     x1, x25
    c8c: mov     x0, x19
    c90: mov     w2, #0x1
    c94: bl      850 <mlkem1024_gen_matrix>
    c98: mov     w0, #0x3
    c9c: strb    w0, [sp]
    ca0: mov     x4, x21
    ca4: add     x3, x20, #0x600
    ca8: add     x2, x20, #0x400
    cac: add     x1, x20, #0x200
    cb0: mov     x0, x20
    cb4: mov     w7, #0x2
    cb8: mov     w6, #0x1
    cbc: mov     w5, #0x0
    cc0: bl      19e0 <mlkem1024_poly_getnoise_eta1_4x>
    cc4: mov     w0, #0x7
    cc8: strb    w0, [sp]
    ccc: mov     x4, x21
    cd0: add     x3, x24, #0x600
    cd4: mov     w7, #0x6
    cd8: mov     w6, #0x5
    cdc: mov     w5, #0x4
    ce0: add     x2, x24, #0x400
    ce4: add     x1, x24, #0x200
    ce8: mov     x0, x24
    cec: bl      19e0 <mlkem1024_poly_getnoise_eta1_4x>
    cf0: mov     x1, x21
    cf4: mov     w2, #0x8
    cf8: mov     x0, x28
    cfc: bl      1b40 <mlkem1024_poly_getnoise_eta2>
    d00: add     x21, x19, #0x2, lsl #12
    d04: mov     x0, x20
    d08: bl      17f0 <mlkem1024_polyvec_ntt>
    d0c: mov     x27, x21
    d10: add     x22, x21, #0x800
    d14: mov     x1, x20
    d18: mov     x0, x23
    d1c: bl      1900 <mlkem1024_polyvec_mulcache_compute>
    d20: mov     x1, x26
    d24: mov     x0, x27
    d28: mov     x3, x23
    d2c: mov     x2, x20
    d30: add     x27, x27, #0x200
    d34: bl      1850 <mlkem1024_polyvec_basemul_acc_montgomery_cached>
    d38: add     x26, x26, #0x800
    d3c: cmp     x27, x22
    d40: b.ne    d20 <mlkem1024_indcpa_enc+0x140>
    d44: ldr     x27, [sp, #128]
    d48: mov     x3, x23
    d4c: mov     x2, x20
    d50: mov     x0, #0x4800
    d54: mov     x1, x27
    d58: add     x22, x19, x0
    d5c: mov     x0, x22
    d60: bl      1850 <mlkem1024_polyvec_basemul_acc_montgomery_cached>
    d64: mov     x0, x21
    d68: bl      1820 <mlkem1024_polyvec_invntt_tomont>
    d6c: mov     x0, x22
    d70: bl      4394 <mlkem_poly_invntt_tomont>
    d74: mov     x1, x24
    d78: mov     x0, x21
    d7c: bl      1970 <mlkem1024_polyvec_add>
    d80: mov     x1, x28
    d84: mov     x0, x22
    d88: bl      41e0 <mlkem_poly_add>
    d8c: ldr     x26, [sp, #136]
    d90: mov     x0, x22
    d94: mov     x1, x26
    d98: bl      41e0 <mlkem_poly_add>
    d9c: mov     x0, x21
    da0: bl      1940 <mlkem1024_polyvec_reduce>
    da4: mov     x0, x22
    da8: bl      4190 <mlkem_poly_reduce>
    dac: ldr     x0, [sp, #120]
    db0: mov     x1, x21
    db4: bl      16f0 <mlkem1024_polyvec_compress_du>
    db8: ldr     x0, [sp, #120]
    dbc: mov     x1, x22
    dc0: add     x0, x0, #0x580
    dc4: bl      1e74 <mlkem_poly_compress_d5>
    dc8: mov     x0, x23
    dcc: mov     x2, #0x400
    dd0: mov     w1, #0x0
    dd4: bl      840 <memset@plt>
    dd8: mov     x2, #0x200
    ddc: mov     x0, x28
    de0: mov     w1, #0x0
    de4: bl      840 <memset@plt>
    de8: mov     x2, #0x200
    dec: mov     x0, x26
    df0: mov     w1, #0x0
    df4: bl      840 <memset@plt>
    df8: mov     x2, #0x200
    dfc: mov     x0, x22
    e00: mov     w1, #0x0
    e04: bl      840 <memset@plt>
    e08: mov     x2, #0x800
    e0c: mov     x0, x21
    e10: mov     w1, #0x0
    e14: bl      840 <memset@plt>
    e18: mov     x2, #0x800
    e1c: mov     x0, x24
    e20: mov     w1, #0x0
    e24: bl      840 <memset@plt>
    e28: mov     x2, #0x800
    e2c: mov     x0, x27
    e30: mov     w1, #0x0
    e34: bl      840 <memset@plt>
    e38: mov     x2, #0x800
    e3c: mov     x0, x20
    e40: mov     w1, #0x0
    e44: bl      840 <memset@plt>
    e48: mov     x2, #0x2000
    e4c: mov     x0, x19
    e50: mov     w1, #0x0
    e54: bl      840 <memset@plt>
    e58: stp     xzr, xzr, [x25]
    e5c: stp     xzr, xzr, [x25, #16]
    e60: adrp    x0, 1f000 <mlk_zetas+0x18c80>
    e64: ldr     x0, [x0, #4088]
    e68: ldr     x2, [sp, #19144]
    e6c: ldr     x1, [x0]
    e70: subs    x2, x2, x1
    e74: mov     x1, #0x0
    e78: b.ne    ea4 <mlkem1024_indcpa_enc+0x2c4>
    e7c: ldp     x19, x20, [sp, #16]
    e80: mov     w0, #0x0
    e84: ldp     x21, x22, [sp, #32]
    e88: mov     x12, #0x4ad0
    e8c: ldp     x23, x24, [sp, #48]
    e90: ldp     x25, x26, [sp, #64]
    e94: ldp     x27, x28, [sp, #80]
    e98: ldr     x30, [sp, #96]
    e9c: add     sp, sp, x12
    ea0: ret
    ea4: bl      830 <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x840,0x850; 0xbe0,0xea8];;

let EN4_EXEC = MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The encryption in FIPS 203 in terms of the values computed by the code:   *)
(* the 12-bit fields of the encryption key as decoded (which may be >= q),   *)
(* the NTT of y and its multiplication cache, the noise e1 and e2, the       *)
(* decompressed message, the products with the transposed matrix and with t  *)
(* in Montgomery form, their inverse NTTs, and the results after adding the  *)
(* noise and the message and reducing, whose compressions are encoded in the *)
(* ciphertext.                                                               *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_K4_RESULT = prove
 (`!ek m r (TT:num->int16) (YH:num->int16) (MC:num->int16) (E1:num->int16)
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
         num_of_bytelist(kpke_encrypt mlkem1024 ek m r)`,
  let inv_tac ui k =
    W(fun (_,w) ->
      let pinv = find_term (fun t -> match t with
        Comb(Const("mlkem_ntt_inv",_),_) -> true | _ -> false) w in
      SUBGOAL_THEN
       (mk_comb(mk_comb(`(IN):((1->num)->int)->(((1->num)->int)->bool)->bool`,
                        pinv),`ring_carrier mlkem_rq`)) ASSUME_TAC THENL
       [MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
        REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
        ALL_TAC] THEN
      MP_TAC(ISPECL [rand pinv; ui; `&169:int`; k] MLKEM_NTT_INV_CONG_MUL) THEN
      ANTS_TAC THENL
       [CONV_TAC(DEPTH_CONV BETA_CONV) THEN
        ASM_SIMP_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
        DISCH_TAC])
  and digit_tac =
    AP_THM_TAC THEN AP_TERM_TAC THEN
    W(fun (_,w) ->
      let t = find_term (fun t -> match t with
        Comb(Const("num_of_int",_),
             Comb(Comb(Const("rem",_),
                  Comb(Comb(Const("mlkem_compress",_),_),_)),_)) -> true
        | _ -> false) w in
      MP_TAC(PART_MATCH (lhand o rand) MLKEM_COMPRESS_DIGIT t)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MLKEM_COEFF_POS THEN
      REPEAT(MATCH_MP_TAC RING_ADD THEN
             REWRITE_TAC[MLKEM_CBD_IN_RQ; MLKEM_POLY_IN_RQ]) THEN
      MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
      REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
      DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VAL_EQ_NUM_OF_INT_IVAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC MLKEM_COEFF_POS THEN
      REPEAT(MATCH_MP_TAC RING_ADD THEN
             REWRITE_TAC[MLKEM_CBD_IN_RQ; MLKEM_POLY_IN_RQ]) THEN
      MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
      REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
      ALL_TAC]
  and parity_tac =
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
  MP_TAC(SPECL [`4`; `2`; `2`; `11`; `5`; `ek:byte list`; `m:byte list`;
                `r:byte list`] KPKE_ENCRYPT_FIPS) THEN
  REWRITE_TAC[ARITH_RULE `384 * 4 = 1536`] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; MLKEM_ENCODE_LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `256 * 4 = 1024`; ARITH_RULE `2 * 4 = 8`;
              ARITH_RULE `(11 * 1024) DIV 8 = 1408`] THEN
  W(fun (_,w) ->
    let encs = find_terms (fun t -> match strip_comb t with
       (Const("mlkem_encode",_),[_;_;_]) -> true | _ -> false) w in
    MAP_EVERY (fun enc ->
      MP_TAC(PART_MATCH (lhand o rand) NUM_OF_BYTELIST_MLKEM_ENCODE
              (mk_comb(`num_of_bytelist`,enc)))) encs) THEN
  REPEAT(ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV THENC DIVIDES_CONV);
    DISCH_THEN SUBST1_TAC]) THEN
  BINOP_TAC THENL [ALL_TAC; AP_TERM_TAC] THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  digit_tac THENL
   [MP_TAC(SPECL [`256`; `4`; `i:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 4 = 1024`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[DIV_MOD_ADD_LT] THEN
    SUBGOAL_THEN
     `!n'. n' < 256
           ==> (ival((U0:num->int16)(256 * j + n')) ==
                &169 * ring_sum mlkem_zq {j' | j' < 4}
                        (\j'. fips203_multiply_ntts
                               (mlkem_sample_ntt
                                 (APPEND (mlkem_slice 1536 32 ek)
                                         [word j; word j']))
                               (mlkem_ntt
                                 (mlkem_cbd 2 (mlkem_prf 2 r (word j'))))
                               n')) (mod &3329)`
    ASSUME_TAC THENL
     [parity_tac THENL
       [MP_TAC(SPECL
         [`\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1536 32 ek) [word j; word j'])`;
          `\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1536 32 ek) [word j; word j'])`;
          `\j' n. ival((YH:num->int16)(256 * j' + n))`;
          `\j'. ival((MC:num->int16)(128 * j' + p))`;
          `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
          `ival((U0:num->int16)(256 * j + 2 * p))`; `p:num`]
         BASEMUL4_ROW_EVEN);
        MP_TAC(SPECL
         [`\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1536 32 ek) [word j; word j'])`;
          `\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1536 32 ek) [word j; word j'])`;
          `\j' n. ival((YH:num->int16)(256 * j' + n))`;
          `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
          `ival((U0:num->int16)(256 * j + 2 * p + 1))`; `p:num`]
         BASEMUL4_ROW_ODD)] THEN
      row_tac;
      ALL_TAC] THEN
    W(fun (_,w) ->
      let t = find_term (fun t -> match t with
        Comb(Const("ival",_),Comb(Comb(Const("word_add",_),_),_)) -> true
        | _ -> false) w in
      MP_TAC(PART_MATCH (lhand o rand) IVAL_WORD_ADD_BOUNDED t)) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `abs(ival((U1:num->int16)(256 * j + n))) <= &26624 /\
                    abs(ival((E1:num->int16)(256 * j + n))) <= &2`
      MP_TAC THENL [ASM_SIMP_TAC[]; INT_ARITH_TAC];
      DISCH_THEN SUBST1_TAC] THEN
    inv_tac `\n'. ival((U0:num->int16)(256 * j + n'))` `n:num` THEN
    ASM_SIMP_TAC[MLKEM_RQ_COEFF_ADD; MLKEM_CBD_IN_RQ] THEN
    REWRITE_TAC[MLKEM_ZQ_ADD; INT_REM_EQ] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `(a:int == c) (mod q) /\ (b == d) (mod q)
      ==> (a + b == c + d) (mod q)`) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    MATCH_MP_TAC INT_CONG_MONT_CANCEL THEN
    EXISTS_TAC `inverse_ntt (\n'. ival((U0:num->int16)(256 * j + n'))) n` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n'. n' < 256
         ==> (ival((V0:num->int16) n') ==
              &169 * ring_sum mlkem_zq {j' | j' < 4}
                      (\j'. fips203_multiply_ntts
                             (\n. mlkem_decode 12 ek (256 * j' + n))
                             (mlkem_ntt
                               (mlkem_cbd 2 (mlkem_prf 2 r (word j'))))
                             n')) (mod &3329)`
  ASSUME_TAC THENL
   [parity_tac THEN
    (SUBGOAL_THEN
      `!j' x. j' < 4 /\ x < 256
              ==> (ival((TT:num->int16)(256 * j' + x)) ==
                   mlkem_decode 12 ek (256 * j' + x)) (mod &3329)`
     ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC TT_DECODE_CONG THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `j' < 4` THEN UNDISCH_TAC `x < 256` THEN ARITH_TAC;
       ALL_TAC])
    THENL
     [MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 ek (256 * j' + n)`;
        `\j' n. ival((TT:num->int16)(256 * j' + n))`;
        `\j' n. ival((YH:num->int16)(256 * j' + n))`;
        `\j'. ival((MC:num->int16)(128 * j' + p))`;
        `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
        `ival((V0:num->int16)(2 * p))`; `p:num`] BASEMUL4_ROW_EVEN);
      MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 ek (256 * j' + n)`;
        `\j' n. ival((TT:num->int16)(256 * j' + n))`;
        `\j' n. ival((YH:num->int16)(256 * j' + n))`;
        `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
        `ival((V0:num->int16)(2 * p + 1))`; `p:num`] BASEMUL4_ROW_ODD)] THEN
    row_tac;
    ALL_TAC] THEN
  SUBGOAL_THEN `(num_of_bytelist m DIV 2 EXP i) MOD 2 < 2` ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN
   `ival((MU:num->int16) i) =
    &((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MU_IVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(ival((V1:num->int16) i)) <= &26624 /\
                abs(ival((E2:num->int16) i)) <= &2`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(word_add ((V1:num->int16) i) ((E2:num->int16) i)) =
    ival(V1 i) + ival(E2 i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_ADD_BOUNDED THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o fst o chop_list 2) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i)) =
    ival(word_add (V1 i) (E2 i)) + ival(MU i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_ADD_BOUNDED THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ARITH_RULE
     `(3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2 <= 1665`) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    UNDISCH_TAC `abs(ival((V1:num->int16) i)) <= &26624` THEN
    UNDISCH_TAC `abs(ival((E2:num->int16) i)) <= &2` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  inv_tac `\n. ival((V0:num->int16) n)` `i:num` THEN
  ASM_SIMP_TAC[MLKEM_RQ_COEFF_ADD; MLKEM_CBD_IN_RQ; MLKEM_POLY_IN_RQ;
               RING_ADD] THEN
  ASM_REWRITE_TAC[COEFF_MLKEM_POLY; MLKEM_DECODE_1] THEN
  ASM_SIMP_TAC[MLKEM_DECOMPRESS_1] THEN
  REWRITE_TAC[MLKEM_ZQ_ADD; INT_REM_EQ] THEN
  MATCH_MP_TAC INT_CONG_ADD3_REM_ALT THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INT_CONG_MONT_CANCEL THEN
    EXISTS_TAC `inverse_ntt (\n. ival((V0:num->int16) n)) i` THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_LT THEN
    REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN
    MP_TAC(ARITH_RULE
     `(3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2 <= 1665`) THEN
    ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16. The first 1536 bytes of the encryption key are decoded by          *)
(* mlkem1024_polyvec_frombytes and its last 32, rho, are copied as two       *)
(* 128-bit words to the seed for mlkem1024_gen_matrix. The message is        *)
(* decoded and decompressed by mlkem_poly_frommsg.                           *)
(* ------------------------------------------------------------------------- *)

let EN4_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 3855)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 3840 else 3824))`,
  REWRITE_TAC[REJ_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

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
           (MATCH_MP GENMAT_BYTES128_HALVES th)))]
    else NO_TAC);;

let EN4_TT_TAC b =
  INDCPA_GHOST_TAC "TT" (b + 12288) 1024 "s30" THEN
  SUBGOAL_THEN
   `!i. i < 1024
        ==> (TT:num->int16) i =
            word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "TT" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s30:armstate` (frees(concl th)) &&
      INDCPA_HAS_CONST "MOD" (concl th) && is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC DIV_MOD_EXP_LOW THEN UNDISCH_TAC `i < 1024` THEN ARITH_TAC;
    ALL_TAC];;

let EN4_MU_TAC b =
  INDCPA_GHOST_TAC "MU" (b + 17920) 256 "s44" THEN
  SUBGOAL_THEN
   `!i. i < 256
        ==> (MU:num->int16) i =
            word((3329 * (num_of_bytelist msg DIV 2 EXP i) MOD 2 + 1) DIV 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "MU" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s44:armstate` (frees(concl th)) &&
      can (find_term (fun t -> t = `3329`)) (concl th) &&
      is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

let EN4_SEED_TAC b s =
  MP_TAC(SPECL [INDCPA_SP(b + 18944); `num_of_bytelist rho`;
                mk_var(s,`:armstate`)] GENMAT_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `rho:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* The callees. The matrix is generated with transposition, so the theorem   *)
(* for mlkem1024_gen_matrix is specialized to that case. The noise y and e1  *)
(* is sampled by two calls of mlkem1024_poly_getnoise_eta1_4x, whose fourth  *)
(* outputs are buffers in the stack frame, not null since the frame does not *)
(* contain address 0, and whose fourth nonces are at the bottom of the       *)
(* stack, and e2 by mlkem1024_poly_getnoise_eta2. The theorems with          *)
(* hypotheses of the form ALL P l are used with them as conjunctions.        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_POLYVEC_FROMBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_FROMMSG_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GEN_MATRIX_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    INDCPA_GEN_MATRIX_SPEC
      MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
      `word 1:int64`);;

let LOCAL_GETNOISE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GETNOISE_ETA2_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_NTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_MULCACHE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   );;

let LOCAL_BASEMUL_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_INVNTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_INVNTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_ADD_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_ADD_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_COMPRESS_DU_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_COMPRESS_D5_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* The facts about the stages of the computation other than those given by   *)
(* the tactics in mlkem_native_indcpa.ml: the coefficients of the transposed *)
(* matrix as given by SampleNTT, the bounds on the inputs of the             *)
(* multiplications, the products with the rows of the transposed matrix and  *)
(* with t, the test of the loop over the rows, whose pointers are at         *)
(* constant offsets from the stack pointer, so the loop is simply unrolled,  *)
(* and the bounds on the inputs of the compressions.                         *)
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

let EN4_U0_TAC b =
  INDCPA_GHOST_TAC "U0" (b + 8192) 1024 "s128" THEN
  SUBGOAL_THEN EN4_U0_GOAL ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THENL
     (map (fun q -> INDCPA_BASEMULK_ROW_TAC 4 "U0" (b + 8192 + 512 * q)
                     "ambound" (map (EN4_AM_INST q) [0;1;2;3])
                     EN4_BASEMUL_DEFS) [0;1;2;3]);
    ALL_TAC];;

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

let EN4_V0_TAC b =
  INDCPA_GHOST_TAC "V0" (b + 18432) 256 "s137" THEN
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
(* latter for the callees). The encryption key ek of 1568 bytes is at pk,    *)
(* the message msg of 32 bytes at m and the randomness r of 32 bytes at      *)
(* coins, and the ciphertext of 1568 bytes written at c is that of           *)
(* kpke_encrypt mlkem1024 ek msg r in common/fips203.ml, for any ek (FIPS    *)
(* 203 decodes t modulo q, while the code multiplies by the 12-bit fields,   *)
(* which are congruent). The theorem assumes that SampleNTT terminates for   *)
(* each entry of the matrix, as for mlkem1024_gen_matrix, and that the stack *)
(* does not contain address 0. The stack is the 19152 bytes of the function  *)
(* and the 3680 used by mlkem1024_gen_matrix below them. The proof is by     *)
(* cases on whether the stack pointer is a multiple of 32, which gives the   *)
(* address b of the buffers, at offsets 0 (the matrix), 8192 (u), 10240      *)
(* (e1), 12288 (t), 14336 (y), 16384 (its multiplication cache), 17408 (e2), *)
(* 17920 (the message), 18432 (v) and 18944 (rho).                           *)
(* ------------------------------------------------------------------------- *)

let EN4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`c:int64`; `m:int64`; `pk:int64`; `coins:int64`; `ek:byte list`;
    `msg:byte list`; `r:byte list`; `guard:int64`; `mf:int64`; `mc:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 22832 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 22832):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD;
              SPECL [`pc:num`; `0x1ffe8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD;
                              SPECL [`pc:num`; `0x1ffe8`] WORD_ADD]) THEN
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

let EN4_CASE_TAC b =
  let st n = "s"^string_of_int n in
  ENSURES_INIT_TAC "s0" THEN EN4_PK_TAC THEN

  (*** The setup, the public vector t and the message ***)

  ARM_STEPS_TAC EN4_EXEC (1--6) THEN EN4_BUFFER_TAC THEN
  ARM_STEPS_TAC EN4_EXEC (7--9) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN4_EXEC (10--29) THEN
  LOCAL_POLYVEC_FROMBYTES_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist ek MOD 2 EXP (8 * 1536)`;
    `pc:num`; `read SP s`; `read X30 s`] 30 THEN
  EN4_TT_TAC b THEN
  ARM_STEPS_TAC EN4_EXEC (31--43) THEN
  LOCAL_POLY_FROMMSG_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist msg`; `pc:num`;
    `read X30 s`] 44 THEN
  EN4_MU_TAC b THEN

  (*** The transposed matrix ***)

  EN4_SEED_TAC b (st 44) THEN
  ARM_STEPS_TAC EN4_EXEC (45--48) THEN INDCPA_GOT_TAC THEN
  LOCAL_GEN_MATRIX_TAC
   [`read X0 s`; `read X1 s`; `rho:byte list`; `k:num`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 49 THEN
  INDCPA_GHOST_TAC "AM" b 4096 (st 49) THEN
  EN4_MATRIX_TAC b `s49:armstate` THEN

  (*** The noise: y and e1 from two calls with four outputs, then e2 ***)

  ARM_STEPS_TAC EN4_EXEC (50--60) THEN
  INDCPA_NONZERO_TAC 22832 (b + 15872) THEN INDCPA_NONCE_TAC 3 THEN
  LOCAL_GETNOISE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `r:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 3:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 61 THEN
  INDCPA_NOISE_TAC "YS" (b + 14336) 4 "r" "word j" (st 61) THEN
  INDCPA_DISCARD_LETS_TAC THEN
  ARM_STEPS_TAC EN4_EXEC (62--72) THEN
  INDCPA_NONZERO_TAC 22832 (b + 11776) THEN INDCPA_NONCE_TAC 7 THEN
  LOCAL_GETNOISE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `r:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 7:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 73 THEN
  INDCPA_NOISE_TAC "E1" (b + 10240) 4 "r" "word(4 + j)" (st 73) THEN
  INDCPA_DISCARD_LETS_TAC THEN
  ARM_STEPS_TAC EN4_EXEC (74--77) THEN INDCPA_GOT_TAC THEN
  LOCAL_GETNOISE_ETA2_TAC
   [`read X0 s`; `read X1 s`; `r:byte list`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 78 THEN
  INDCPA_NOISE1_TAC "E2" (b + 17408) "r" "word 8" (st 78) THEN
  INDCPA_DISCARD_LETS_TAC THEN

  (*** The NTT of the noise and its multiplication cache ***)

  ARM_STEPS_TAC EN4_EXEC (79--81) THEN
  LOCAL_POLYVEC_NTT_TAC
   [`read X0 s`; `YS:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 82 THEN
  INDCPA_NTT_TAC "YH" (b + 14336) 4 "YS" "r" "word j" (st 82) THEN
  ARM_STEPS_TAC EN4_EXEC (83--87) THEN
  LOCAL_POLYVEC_MULCACHE_TAC
   [`read X0 s`; `read X1 s`; `YH:num->int16`; `pc:num`; `read SP s`;
    `read X30 s`] 88 THEN
  INDCPA_MULCACHE_TAC "MC" (b + 16384) 4 "YH" (st 88) THEN

  (*** The products with the transposed matrix, in a loop, and with t ***)

  MAP_EVERY (fun q ->
    let a = (b + 2048 * q,"AM",1024 * q)
    and y = (b + 14336,"YH") and t = (b + 16384,"MC") in
    ARM_STEPS_TAC EN4_EXEC ((89 + 10 * q)--(94 + 10 * q)) THEN
    INDCPA_BASEMULK_PRE_TAC 4 a y t (st(94 + 10 * q)) THEN
    LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 4 ("AM",1024 * q) "YH" "MC")
      (95 + 10 * q) THEN
    INDCPA_BASEMULK_DROP_PRE_TAC 4 a y t THEN
    ARM_STEPS_TAC EN4_EXEC ((96 + 10 * q)--(98 + 10 * q)) THEN
    EN4_PC_TAC (st(98 + 10 * q))) [0;1;2;3] THEN
  EN4_AM_BOUND_TAC THEN EN4_U0_TAC b THEN
  ARM_STEPS_TAC EN4_EXEC (129--136) THEN
  INDCPA_BASEMULK_PRE_TAC 4 (b + 12288,"TT",0) (b + 14336,"YH")
    (b + 16384,"MC") (st 136) THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 4 ("TT",0) "YH" "MC") 137 THEN
  INDCPA_BASEMULK_DROP_PRE_TAC 4 (b + 12288,"TT",0) (b + 14336,"YH")
    (b + 16384,"MC") THEN
  EN4_TT_BOUND_TAC THEN EN4_V0_TAC b THEN

  (*** The inverse NTTs, adding the noise and the message, reductions ***)

  ARM_STEPS_TAC EN4_EXEC (138--139) THEN
  LOCAL_POLYVEC_INVNTT_TAC
   [`read X0 s`; `U0:num->int16`; `pc:num`; `read SP s`; `read X30 s`]
   140 THEN
  INDCPA_INVNTT_TAC "U1" (b + 8192) 4 "U0" (st 140) THEN
  ARM_STEPS_TAC EN4_EXEC (141--142) THEN
  LOCAL_POLY_INVNTT_TAC
   [`read X0 s`; `V0:num->int16`; `pc:num`; `read SP s`; `read X30 s`]
   143 THEN
  INDCPA_INVNTT1_TAC "V1" (b + 18432) "V0" (st 143) THEN
  ARM_STEPS_TAC EN4_EXEC (144--146) THEN
  LOCAL_POLYVEC_ADD_TAC
   [`read X0 s`; `read X1 s`; `U1:num->int16`; `E1:num->int16`; `pc:num`;
    `read SP s`; `read X30 s`] 147 THEN
  ARM_STEPS_TAC EN4_EXEC (148--150) THEN
  LOCAL_POLY_ADD_TAC
   [`read X0 s`; `read X1 s`; `V1:num->int16`; `E2:num->int16`; `pc:num`;
    `read X30 s`] 151 THEN
  ARM_STEPS_TAC EN4_EXEC (152--155) THEN
  LOCAL_POLY_ADD_TAC
   [`read X0 s`; `read X1 s`;
    `\i. word_add ((V1:num->int16) i) ((E2:num->int16) i)`;
    `MU:num->int16`; `pc:num`; `read X30 s`] 156 THEN
  ARM_STEPS_TAC EN4_EXEC (157--158) THEN
  LOCAL_POLYVEC_REDUCE_TAC
   [`read X0 s`; `\i. word_add ((U1:num->int16) i) ((E1:num->int16) i)`;
    `pc:num`; `read SP s`; `read X30 s`] 159 THEN
  INDCPA_REDUCE_TAC "U3" (b + 8192) 1024
    "word_add ((U1:num->int16) i) ((E1:num->int16) i)" (st 159) THEN
  ARM_STEPS_TAC EN4_EXEC (160--161) THEN
  LOCAL_POLY_REDUCE_TAC
   [`read X0 s`;
    `\i. word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i)`;
    `pc:num`; `read X30 s`] 162 THEN
  INDCPA_REDUCE_TAC "V4" (b + 18432) 256
    "word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i)) \
     ((MU:num->int16) i)" (st 162) THEN

  (*** The compression and encoding of u and v ***)

  ARM_STEPS_TAC EN4_EXEC (163--165) THEN INDCPA_GOT_TAC THEN
  LOCAL_POLYVEC_COMPRESS_DU_TAC
   [`read X0 s`; `read X1 s`; `U3:num->int16`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 166 THEN
  EN4_COMPRESS_POST_TAC "U3"
   `ival(word_add ((U1:num->int16) i) ((E1:num->int16) i))` THEN
  ARM_STEPS_TAC EN4_EXEC (167--170) THEN
  LOCAL_POLY_COMPRESS_D5_TAC
   [`read X0 s`; `read X1 s`; `V4:num->int16`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 171 THEN
  EN4_COMPRESS_POST_TAC "V4"
   `ival(word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i))` THEN

  (*** Zeroing the buffers, the stack guard, the return ***)

  INDCPA_MEMSET_LABEL_TAC THEN
  INDCPA_MEMSETS_TAC EN4_EXEC
   [172,175; 181,184; 190,193; 199,202; 208,211; 217,220; 226,229;
    235,238; 244,247] THEN
  ARM_STEPS_TAC EN4_EXEC (253--255) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN4_EXEC (256--271) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN EN4_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!c m pk coins (ek:byte list) (msg:byte list) (r:byte list)
    guard mf mc ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        LENGTH ek = 1568 /\ LENGTH msg = 32 /\ LENGTH r = 32 /\
        (!i j. i < 4 /\ j < 4
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 1536 32 ek) [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 22832),22832) /\
        nonoverlapping (c,1568) (word_sub stackpointer (word 22832),22832) /\
        nonoverlapping (pk,1568) (word pc,0x6480) /\
        ALLPAIRS nonoverlapping
         [(c,1568); (word_sub stackpointer (word 22832),22832)]
         [(m,32); (pk,1568); (coins,32); (word pc,0x6480);
          (word(pc + 0x1fff8),8); (guard,8); (word(pc + 0x1ffe8),8);
          (word(pc + 0x1ffd0),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0xbe0) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [c; m; pk; coins] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                  read (memory :> bytes64(word(pc + 0x1ffd0))) s = mc /\
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
                memory :> bytes(word_sub stackpointer (word 22832),22832)])`,
  EN4_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [EN4_CASE_TAC 3840; EN4_CASE_TAC 3824]);;
