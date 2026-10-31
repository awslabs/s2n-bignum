(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The encryption of K-PKE for ML-KEM-768 (FIPS 203 Algorithm 14). This is   *)
(* the code for mlkem768_indcpa_enc from mlkem-native's portable C           *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* It decodes the vector t in the NTT domain from the encryption key and the *)
(* message m from its 32 bytes, generates the transposed matrix from rho     *)
(* (the last 32 bytes of the key), samples y, e1 and e2 from the randomness  *)
(* r, and computes u = NTT^-1(A^T NTT(y)) + e1 and v = NTT^-1(t^T NTT(y)) +  *)
(* e2 + mu, where mu is m decompressed. It writes the compressions of u and  *)
(* v as the ciphertext, zeroing its buffers. It is verified in the whole     *)
(* image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address     *)
(* 0x5310, using the theorems for mlkem768_polyvec_frombytes,                *)
(* mlkem_poly_frommsg, mlkem768_gen_matrix, mlkem768_poly_getnoise_eta1_4x,  *)
(* mlkem768_polyvec_ntt, mlkem768_polyvec_mulcache_compute,                  *)
(* mlkem768_polyvec_basemul_acc_montgomery_cached,                           *)
(* mlkem768_polyvec_invntt_tomont, mlkem_poly_invntt_tomont,                 *)
(* mlkem768_polyvec_add, mlkem_poly_add, mlkem768_polyvec_reduce,            *)
(* mlkem_poly_reduce, mlkem768_polyvec_compress_du and                       *)
(* mlkem_poly_compress_d4 in the image, and the contract for memset.         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_polyvec_frombytes_k3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_frommsg_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_gen_matrix_k3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_getnoise_eta1_4x_k3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_ntt_k3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_mulcache_compute_k3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_basemul_k3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_invntt_tomont_k3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_invntt_tomont_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_add_k3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_add_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_reduce_k3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_reduce_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_compress_du_k3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_compress_d4_gcc12_O2.ml";;
needs "arm/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image:

    5310: mov     x12, #0x33d0
    5314: sub     sp, sp, x12
    5318: mov     x4, #0x1e00
    531c: mov     x5, #0x2d00
    5320: mov     x6, #0x1800
    5324: mov     x7, #0x2a00
    5328: stp     x19, x20, [sp, #16]
    532c: add     x19, sp, #0xaf
    5330: and     x19, x19, #0xffffffffffffffe0
    5334: mov     x20, x2
    5338: add     x4, x19, x4
    533c: adrp    x2, 1f000 <mlk_zetas+0x18c80>
    5340: ldr     x2, [x2, #4088]
    5344: stp     x21, x22, [sp, #32]
    5348: mov     x21, x3
    534c: stp     x23, x24, [sp, #48]
    5350: mov     x22, x1
    5354: add     x24, x19, x6
    5358: stp     x25, x26, [sp, #64]
    535c: add     x23, x19, x7
    5360: mov     x1, x20
    5364: stp     x27, x28, [sp, #80]
    5368: add     x28, x19, x5
    536c: mov     x26, x19
    5370: str     x30, [sp, #96]
    5374: stp     x0, x4, [sp, #120]
    5378: mov     x0, x4
    537c: ldr     x3, [x2]
    5380: str     x3, [sp, #13256]
    5384: mov     x3, #0x0
    5388: bl      5ec4 <mlkem768_polyvec_frombytes>
    538c: ldr     q0, [x20, #1152]
    5390: mov     x8, #0x3300
    5394: ldr     q1, [x20, #1168]
    5398: add     x2, x19, x8
    539c: mov     x9, #0x2f00
    53a0: mov     x10, #0x1200
    53a4: mov     x11, #0x2400
    53a8: add     x0, x19, x9
    53ac: add     x20, x19, x11
    53b0: mov     x1, x22
    53b4: mov     x25, x2
    53b8: add     x22, x19, x10
    53bc: stp     q0, q1, [x2]
    53c0: mov     x27, x22
    53c4: str     x0, [sp, #136]
    53c8: bl      22e0 <mlkem_poly_frommsg>
    53cc: mov     x1, x25
    53d0: mov     x0, x19
    53d4: mov     w2, #0x1
    53d8: bl      4f50 <mlkem768_gen_matrix>
    53dc: mov     w0, #0xffffffff
    53e0: strb    w0, [sp]
    53e4: mov     x4, x21
    53e8: add     x2, x20, #0x400
    53ec: add     x1, x20, #0x200
    53f0: mov     x0, x20
    53f4: mov     w7, #0x2
    53f8: mov     w6, #0x1
    53fc: mov     w5, #0x0
    5400: mov     x3, #0x0
    5404: bl      60a0 <mlkem768_poly_getnoise_eta1_4x>
    5408: mov     x4, x21
    540c: add     x1, x24, #0x200
    5410: mov     x3, x28
    5414: add     x2, x24, #0x400
    5418: mov     w0, #0x6
    541c: strb    w0, [sp]
    5420: mov     w7, #0x5
    5424: mov     w6, #0x4
    5428: mov     w5, #0x3
    542c: mov     x0, x24
    5430: bl      60a0 <mlkem768_poly_getnoise_eta1_4x>
    5434: mov     w21, #0x0
    5438: mov     x0, x20
    543c: bl      5f00 <mlkem768_polyvec_ntt>
    5440: mov     x1, x20
    5444: mov     x0, x23
    5448: bl      5ff0 <mlkem768_polyvec_mulcache_compute>
    544c: mov     x1, x26
    5450: mov     x0, x27
    5454: mov     x3, x23
    5458: mov     x2, x20
    545c: add     w21, w21, #0x1
    5460: bl      5f40 <mlkem768_polyvec_basemul_acc_montgomery_cached>
    5464: add     x26, x26, #0x600
    5468: add     x27, x27, #0x200
    546c: cmp     w21, #0x3
    5470: b.ne    544c <mlkem768_indcpa_enc+0x13c>
    5474: ldr     x27, [sp, #128]
    5478: mov     x3, x23
    547c: mov     x2, x20
    5480: mov     x0, #0x3100
    5484: mov     x1, x27
    5488: add     x21, x19, x0
    548c: mov     x0, x21
    5490: bl      5f40 <mlkem768_polyvec_basemul_acc_montgomery_cached>
    5494: mov     x0, x22
    5498: bl      5f20 <mlkem768_polyvec_invntt_tomont>
    549c: mov     x0, x21
    54a0: bl      4394 <mlkem_poly_invntt_tomont>
    54a4: mov     x1, x24
    54a8: mov     x0, x22
    54ac: bl      6044 <mlkem768_polyvec_add>
    54b0: mov     x1, x28
    54b4: mov     x0, x21
    54b8: bl      41e0 <mlkem_poly_add>
    54bc: ldr     x26, [sp, #136]
    54c0: mov     x0, x21
    54c4: mov     x1, x26
    54c8: bl      41e0 <mlkem_poly_add>
    54cc: mov     x0, x22
    54d0: bl      6024 <mlkem768_polyvec_reduce>
    54d4: mov     x0, x21
    54d8: bl      4190 <mlkem_poly_reduce>
    54dc: ldr     x0, [sp, #120]
    54e0: mov     x1, x22
    54e4: bl      5e20 <mlkem768_polyvec_compress_du>
    54e8: ldr     x0, [sp, #120]
    54ec: mov     x1, x21
    54f0: add     x0, x0, #0x3c0
    54f4: bl      1bf0 <mlkem_poly_compress_d4>
    54f8: mov     x0, x23
    54fc: mov     x2, #0x300
    5500: mov     w1, #0x0
    5504: bl      840 <memset@plt>
    5508: mov     x2, #0x200
    550c: mov     x0, x28
    5510: mov     w1, #0x0
    5514: bl      840 <memset@plt>
    5518: mov     x2, #0x200
    551c: mov     x0, x26
    5520: mov     w1, #0x0
    5524: bl      840 <memset@plt>
    5528: mov     x2, #0x200
    552c: mov     x0, x21
    5530: mov     w1, #0x0
    5534: bl      840 <memset@plt>
    5538: mov     x2, #0x600
    553c: mov     x0, x22
    5540: mov     w1, #0x0
    5544: bl      840 <memset@plt>
    5548: mov     x2, #0x600
    554c: mov     x0, x24
    5550: mov     w1, #0x0
    5554: bl      840 <memset@plt>
    5558: mov     x2, #0x600
    555c: mov     x0, x27
    5560: mov     w1, #0x0
    5564: bl      840 <memset@plt>
    5568: mov     x2, #0x600
    556c: mov     x0, x20
    5570: mov     w1, #0x0
    5574: bl      840 <memset@plt>
    5578: mov     x2, #0x1200
    557c: mov     x0, x19
    5580: mov     w1, #0x0
    5584: bl      840 <memset@plt>
    5588: stp     xzr, xzr, [x25]
    558c: stp     xzr, xzr, [x25, #16]
    5590: adrp    x0, 1f000 <mlk_zetas+0x18c80>
    5594: ldr     x0, [x0, #4088]
    5598: ldr     x2, [sp, #13256]
    559c: ldr     x1, [x0]
    55a0: subs    x2, x2, x1
    55a4: mov     x1, #0x0
    55a8: b.ne    55d4 <mlkem768_indcpa_enc+0x2c4>
    55ac: ldp     x19, x20, [sp, #16]
    55b0: mov     w0, #0x0
    55b4: ldp     x21, x22, [sp, #32]
    55b8: mov     x12, #0x33d0
    55bc: ldp     x23, x24, [sp, #48]
    55c0: ldp     x25, x26, [sp, #64]
    55c4: ldp     x27, x28, [sp, #80]
    55c8: ldr     x30, [sp, #96]
    55cc: add     sp, sp, x12
    55d0: ret
    55d4: bl      830 <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x840,0x850; 0x5310,0x55d8];;

let EN3_EXEC = MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The encryption in FIPS 203 in terms of the values computed by the code:   *)
(* the 12-bit fields of the encryption key as decoded (which may be >= q),   *)
(* the NTT of y and its multiplication cache, the noise e1 and e2, the       *)
(* decompressed message, the products with the transposed matrix and with t  *)
(* in Montgomery form, their inverse NTTs, and the results after adding the  *)
(* noise and the message and reducing, whose compressions are encoded in the *)
(* ciphertext.                                                               *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_K3_RESULT = prove
 (`!ek m r (TT:num->int16) (YH:num->int16) (MC:num->int16) (E1:num->int16)
    (E2:num->int16) (MU:num->int16) (U0:num->int16) (V0:num->int16)
    (U1:num->int16) (V1:num->int16) (U3:num->int16) (V4:num->int16).
     (!i j n. i < 3 /\ j < 3 /\ n < 256
              ==> mlkem_sample_ntt
                   (APPEND (mlkem_slice 1152 32 ek) [word j; word i]) n
                  < &3329) /\
     (!i. i < 768
          ==> TT i = word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(YH(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j))) i)
                (mod &3329) /\
                abs(ival(YH(256 * j + i))) <= &23594) /\
     (!j p. j < 3 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(YH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(E1(256 * j + i)) ==
                 coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word(3 + j)))))
                (mod &3329) /\
                abs(ival(E1(256 * j + i))) <= &2) /\
     (!i. i < 256
          ==> (ival(E2 i) == coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word 6))))
              (mod &3329) /\
              abs(ival(E2 i)) <= &2) /\
     (!i. i < 256
          ==> MU i = word((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1)
                          DIV 2)) /\
     (!q p. q < 3 /\ p < 128
            ==> (ival(U0(256 * q + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 2]) (2 * p + 1) *
                   ival(MC(256 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 2]) (2 * p) *
                   ival(YH(512 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(MC(128 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(MC p) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p))))) (mod &3329) /\
                (ival(U0(256 * q + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 2]) (2 * p + 1) *
                   ival(YH(512 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 2]) (2 * p) *
                   ival(YH(512 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(YH(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(YH(2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(V0(2 * p)) ==
               &169 *
               ((ival(TT(512 + 2 * p + 1)) * ival(MC(256 + p)) +
                 ival(TT(512 + 2 * p)) * ival(YH(512 + 2 * p))) +
                (ival(TT(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p))) +
                (ival(TT(2 * p + 1)) * ival(MC p) +
                 ival(TT(2 * p)) * ival(YH(2 * p))))) (mod &3329) /\
              (ival(V0(2 * p + 1)) ==
               &169 *
               ((ival(TT(512 + 2 * p + 1)) * ival(YH(512 + 2 * p)) +
                 ival(TT(512 + 2 * p)) * ival(YH(512 + 2 * p + 1))) +
                (ival(TT(256 + 2 * p + 1)) * ival(YH(256 + 2 * p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p + 1))) +
                (ival(TT(2 * p + 1)) * ival(YH(2 * p)) +
                 ival(TT(2 * p)) * ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(U1(256 * j + i)) ==
                 inverse_ntt (\n. ival(U0(256 * j + n))) i) (mod &3329) /\
                abs(ival(U1(256 * j + i))) <= &26624) /\
     (!i. i < 256
          ==> (ival(V1 i) == inverse_ntt (\n. ival(V0 n)) i) (mod &3329) /\
              abs(ival(V1 i)) <= &26624) /\
     (!i. i < 768 ==> ival(U3 i) = ival(word_add (U1 i) (E1 i)) rem &3329) /\
     (!i. i < 256
          ==> ival(V4 i) =
              ival(word_add (word_add (V1 i) (E2 i)) (MU i)) rem &3329)
     ==> nsum {i | i < 768}
              (\i. ((2048 * val(U3 i) + 3329) DIV 6658) MOD 1024 *
                   2 EXP (10 * i)) +
         2 EXP (8 * 960) *
         nsum {i | i < 256}
              (\i. ((32 * val(V4 i) + 3329) DIV 6658) MOD 16 * 2 EXP (4 * i)) =
         num_of_bytelist(kpke_encrypt mlkem768 ek m r)`,
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
    REWRITE_TAC[ARITH_RULE `b < 2 <=> b = 0 \/ b = 1`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    (SUBGOAL_THEN `2 * p < 256 /\ 2 * p + 1 < 256` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `p < 128` THEN ARITH_TAC; ALL_TAC])
  and row_tac =
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; INT_CONG_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem768] THEN
  MP_TAC(SPECL [`3`; `2`; `2`; `10`; `4`; `ek:byte list`; `m:byte list`;
                `r:byte list`] KPKE_ENCRYPT_FIPS) THEN
  REWRITE_TAC[ARITH_RULE `384 * 3 = 1152`] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; MLKEM_ENCODE_LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `256 * 3 = 768`; ARITH_RULE `2 * 3 = 6`;
              ARITH_RULE `(10 * 768) DIV 8 = 960`] THEN
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
   [MP_TAC(SPECL [`256`; `3`; `i:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 3 = 768`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[DIV_MOD_ADD_LT] THEN
    SUBGOAL_THEN
     `!n'. n' < 256
           ==> (ival((U0:num->int16)(256 * j + n')) ==
                &169 * ring_sum mlkem_zq {j' | j' < 3}
                        (\j'. fips203_multiply_ntts
                               (mlkem_sample_ntt
                                 (APPEND (mlkem_slice 1152 32 ek)
                                         [word j; word j']))
                               (mlkem_ntt
                                 (mlkem_cbd 2 (mlkem_prf 2 r (word j'))))
                               n')) (mod &3329)`
    ASSUME_TAC THENL
     [parity_tac THENL
       [MP_TAC(SPECL
         [`\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1152 32 ek) [word j; word j'])`;
          `\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1152 32 ek) [word j; word j'])`;
          `\j' n. ival((YH:num->int16)(256 * j' + n))`;
          `\j'. ival((MC:num->int16)(128 * j' + p))`;
          `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
          `ival((U0:num->int16)(256 * j + 2 * p))`; `p:num`]
         BASEMUL3_ROW_EVEN);
        MP_TAC(SPECL
         [`\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1152 32 ek) [word j; word j'])`;
          `\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1152 32 ek) [word j; word j'])`;
          `\j' n. ival((YH:num->int16)(256 * j' + n))`;
          `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
          `ival((U0:num->int16)(256 * j + 2 * p + 1))`; `p:num`]
         BASEMUL3_ROW_ODD)] THEN
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
              &169 * ring_sum mlkem_zq {j' | j' < 3}
                      (\j'. fips203_multiply_ntts
                             (\n. mlkem_decode 12 ek (256 * j' + n))
                             (mlkem_ntt
                               (mlkem_cbd 2 (mlkem_prf 2 r (word j'))))
                             n')) (mod &3329)`
  ASSUME_TAC THENL
   [parity_tac THEN
    (SUBGOAL_THEN
      `!j' x. j' < 3 /\ x < 256
              ==> (ival((TT:num->int16)(256 * j' + x)) ==
                   mlkem_decode 12 ek (256 * j' + x)) (mod &3329)`
     ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC TT_DECODE_CONG THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `j' < 3` THEN UNDISCH_TAC `x < 256` THEN ARITH_TAC;
       ALL_TAC])
    THENL
     [MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 ek (256 * j' + n)`;
        `\j' n. ival((TT:num->int16)(256 * j' + n))`;
        `\j' n. ival((YH:num->int16)(256 * j' + n))`;
        `\j'. ival((MC:num->int16)(128 * j' + p))`;
        `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
        `ival((V0:num->int16)(2 * p))`; `p:num`] BASEMUL3_ROW_EVEN);
      MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 ek (256 * j' + n)`;
        `\j' n. ival((TT:num->int16)(256 * j' + n))`;
        `\j' n. ival((YH:num->int16)(256 * j' + n))`;
        `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
        `ival((V0:num->int16)(2 * p + 1))`; `p:num`] BASEMUL3_ROW_ODD)] THEN
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
(* of 16. The first 1152 bytes of the encryption key are decoded by          *)
(* mlkem768_polyvec_frombytes and its last 32, rho, are copied as two        *)
(* 128-bit words to the seed for mlkem768_gen_matrix. The message is decoded *)
(* and decompressed by mlkem_poly_frommsg.                                   *)
(* ------------------------------------------------------------------------- *)

let EN3_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 3807)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 3776 else 3792))`,
  REWRITE_TAC[REJ_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let EN3_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` EN3_BUFFER_ADDRESS))
    else NO_TAC);;

let EN3_PK_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(pk,1184)) s = num_of_bytelist ek`) (concl th)
    then
      ASSUME_TAC(REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
       (REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_MOD;
                     ARITH_RULE `MIN 1184 1152 = 1152`]
        (AP_THM(AP_TERM `(MOD):num->num->num`
                 (REWRITE_RULE[READ_COMPONENT_COMPOSE] th))
           `2 EXP (8 * 1152)`))) THEN
      MP_TAC(SPECL [`pk:int64`; `ek:byte list`; `1152`; `32`;
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

let EN3_TT_TAC b =
  INDCPA_GHOST_TAC "TT" (b + 7680) 768 "s32" THEN
  SUBGOAL_THEN
   `!i. i < 768
        ==> (TT:num->int16) i =
            word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "TT" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s32:armstate` (frees(concl th)) &&
      INDCPA_HAS_CONST "MOD" (concl th) && is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC DIV_MOD_EXP_LOW THEN UNDISCH_TAC `i < 768` THEN ARITH_TAC;
    ALL_TAC];;

let EN3_MU_TAC b =
  INDCPA_GHOST_TAC "MU" (b + 12032) 256 "s49" THEN
  SUBGOAL_THEN
   `!i. i < 256
        ==> (MU:num->int16) i =
            word((3329 * (num_of_bytelist msg DIV 2 EXP i) MOD 2 + 1) DIV 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "MU" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s49:armstate` (frees(concl th)) &&
      can (find_term (fun t -> t = `3329`)) (concl th) &&
      is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

let EN3_SEED_TAC b s =
  MP_TAC(SPECL [INDCPA_SP(b + 13056); `num_of_bytelist rho`;
                mk_var(s,`:armstate`)] GENMAT_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `rho:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* The callees. The matrix is generated with transposition, and the fourth   *)
(* output of the first call of mlkem768_poly_getnoise_eta1_4x is a null      *)
(* pointer (its fourth nonce, at the bottom of the stack, is 255), so the    *)
(* theorems are specialized to those cases. In the second call, the fourth   *)
(* output is e2, which is not null since the stack frame does not contain    *)
(* address 0. The theorems with hypotheses of the form ALL P l are used with *)
(* them as conjunctions.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_POLYVEC_FROMBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_FROMMSG_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GEN_MATRIX_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    INDCPA_GEN_MATRIX_SPEC
      MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
      `word 1:int64`);;

let LOCAL_GETNOISE3_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    INDCPA_GETNOISE_NULL
     MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GETNOISE4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_NTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_MULCACHE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   );;

let LOCAL_BASEMUL_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_INVNTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_INVNTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_ADD_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_ADD_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_REDUCE_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_COMPRESS_DU_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_COMPRESS_D4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* The facts about the stages of the computation other than those given by   *)
(* the tactics in mlkem_native_indcpa.ml: the coefficients of the transposed *)
(* matrix as given by SampleNTT, the bounds on the inputs of the             *)
(* multiplications, the products with the rows of the transposed matrix and  *)
(* with t, and the bounds on the inputs of the compressions.                 *)
(* ------------------------------------------------------------------------- *)

let EN3_MATRIX_TAC b s =
  let addr = parse_term(Printf.sprintf
    "word_add stackpointer (word (%d + 512 * (3 * q + j))):int64" b) in
  SUBGOAL_THEN
   `!q j n. q < 3 /\ j < 3 /\ n < 256
            ==> &0 <= mlkem_sample_ntt (APPEND rho [word q; word j]) n /\
                mlkem_sample_ntt (APPEND rho [word q; word j]) n < &3329`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC MLKEM_SAMPLE_NTT_REJ_BOUND THEN
    EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q j n. q < 3 /\ j < 3 /\ n < 256
            ==> ival((AM:num->int16)(768 * q + 256 * j + n)) =
                mlkem_sample_ntt (APPEND rho [word q; word j]) n`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    INDCPA_GHOST_SPEC_TAC "AM" `768 * q + 256 * j + n` THEN
    MP_TAC(SPECL [addr; s; `APPEND (rho:byte list) [word q; word j]`;
                  `k:num`; `n:num`] MLKEM_NATIVE_SAMPLE_COEFF) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    MATCH_MP_TAC READ16_OFFSET_EQ THEN ARITH_TAC;
    ALL_TAC];;

let EN3_AM_INST r j =
  let th = SPECL [mk_small_numeral r; mk_small_numeral j]
    (ASSUME `!q j n. q < 3 /\ j < 3 /\ n < 256
                     ==> ival((AM:num->int16)(768 * q + 256 * j + n)) =
                         mlkem_sample_ntt (APPEND rho [word q; word j]) n`) in
  CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES; ADD_ASSOC] THENC
            NUM_REDUCE_CONV) th;;

let EN3_AM_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 2304 ==> abs(ival((AM:num->int16) m)) <= &2 pow 12`
  (LABEL_TAC "ambound") THENL
   [X_GEN_TAC `m':num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`768`; `3`; `m':num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `768 * 3 = 2304`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:num`; `x:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`256`; `3`; `x:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 3 = 768`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(INT_ARITH
     `&0 <= x /\ x < &3329 ==> abs(x:int) <= &2 pow 12`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC];;

let EN3_BASEMUL_DEFS =
  [basemul3_even; basemul3_odd; pmul_acc3; pmull_acc3; pmull];;

let EN3_U0_GOAL = `!q p. q < 3 /\ p < 128
       ==> (ival((U0:num->int16)(256 * q + 2 * p)) ==
            &169 *
            ((mlkem_sample_ntt (APPEND rho [word q; word 2]) (2 * p + 1) *
              ival((MC:num->int16)(256 + p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 2]) (2 * p) *
              ival((YH:num->int16)(512 + 2 * p))) +
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
            ((mlkem_sample_ntt (APPEND rho [word q; word 2]) (2 * p + 1) *
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

let EN3_U0_TAC b =
  INDCPA_GHOST_TAC "U0" (b + 4608) 768 "s119" THEN
  SUBGOAL_THEN EN3_U0_GOAL ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THENL
     (map (fun q -> INDCPA_BASEMUL3_ROW_TAC "U0" (b + 4608 + 512 * q)
                     "ambound" (map (EN3_AM_INST q) [0;1;2])
                     EN3_BASEMUL_DEFS) [0;1;2]);
    ALL_TAC];;

let EN3_TT_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 768 ==> abs(ival((TT:num->int16) m)) <= &2 pow 12`
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

let EN3_V0_GOAL = `!p. p < 128
       ==> (ival((V0:num->int16)(2 * p)) ==
            &169 *
            ((ival((TT:num->int16)(512 + 2 * p + 1)) *
              ival((MC:num->int16)(256 + p)) +
              ival(TT(512 + 2 * p)) * ival((YH:num->int16)(512 + 2 * p))) +
             (ival(TT(256 + 2 * p + 1)) * ival(MC(128 + p)) +
              ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p))) +
             (ival(TT(2 * p + 1)) * ival(MC p) +
              ival(TT(2 * p)) * ival(YH(2 * p))))) (mod &3329) /\
           (ival(V0(2 * p + 1)) ==
            &169 *
            ((ival(TT(512 + 2 * p + 1)) * ival(YH(512 + 2 * p)) +
              ival(TT(512 + 2 * p)) * ival(YH(512 + 2 * p + 1))) +
             (ival(TT(256 + 2 * p + 1)) * ival(YH(256 + 2 * p)) +
              ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p + 1))) +
             (ival(TT(2 * p + 1)) * ival(YH(2 * p)) +
              ival(TT(2 * p)) * ival(YH(2 * p + 1))))) (mod &3329)`;;

let EN3_V0_TAC b =
  INDCPA_GHOST_TAC "V0" (b + 12544) 256 "s128" THEN
  SUBGOAL_THEN EN3_V0_GOAL ASSUME_TAC THENL
   [INDCPA_BASEMUL3_ROW_TAC "V0" (b + 12544) "ttbound" [] EN3_BASEMUL_DEFS;
    ALL_TAC];;

let EN3_COMPRESS_POST_TAC v y =
  let vt = mk_var(v,`:num->int16`) in
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && mem vt (frees(concl th)) &&
    INDCPA_HAS_CONST "nsum" (concl th))) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC VAL_LT_OF_IVAL_REM THEN EXISTS_TAC y THEN ASM_SIMP_TAC[];
    DISCH_TAC];;

let EN3_FINAL_TAC =
  REWRITE_TAC[ARITH_RULE `1088 = 960 + 128`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`ek:byte list`; `msg:byte list`; `r:byte list`;
                `TT:num->int16`; `YH:num->int16`; `MC:num->int16`;
                `E1:num->int16`; `E2:num->int16`; `MU:num->int16`;
                `U0:num->int16`; `V0:num->int16`; `U1:num->int16`;
                `V1:num->int16`; `U3:num->int16`; `V4:num->int16`]
          (REWRITE_RULE[ASSUME `mlkem_slice 1152 32 ek = rho`]
            KPKE_ENCRYPT_K3_RESULT)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
           REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
    SIMP_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy (the      *)
(* latter for the callees). The encryption key ek of 1184 bytes is at pk,    *)
(* the message msg of 32 bytes at m and the randomness r of 32 bytes at      *)
(* coins, and the ciphertext of 1088 bytes written at c is that of           *)
(* kpke_encrypt mlkem768 ek msg r in common/fips203.ml, for any ek (FIPS 203 *)
(* decodes t modulo q, while the code multiplies by the 12-bit fields, which *)
(* are congruent). The theorem assumes that SampleNTT terminates for each    *)
(* entry of the matrix, as for mlkem768_gen_matrix, and that the stack does  *)
(* not contain address 0. The stack is the 13264 bytes of the function and   *)
(* the 3632 used by mlkem768_gen_matrix below them. The proof is by cases on *)
(* whether the stack pointer is a multiple of 32, which gives the address b  *)
(* of the buffers, at offsets 0 (the matrix), 4608 (u), 6144 (e1), 7680 (t), *)
(* 9216 (y), 10752 (its multiplication cache), 11520 (e2), 12032 (the        *)
(* message), 12544 (v) and 13056 (rho).                                      *)
(* ------------------------------------------------------------------------- *)

let EN3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`c:int64`; `m:int64`; `pk:int64`; `coins:int64`; `ek:byte list`;
    `msg:byte list`; `r:byte list`; `guard:int64`; `mf:int64`; `mc:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 16896 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 16896):int64)` THEN
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
   `!i j. i < 3 /\ j < 3
          ==> mlkem_samplentt_terminates
               (APPEND (mlkem_slice 1152 32 ek) [word j; word i])` THEN
  ABBREV_TAC `rho = mlkem_slice 1152 32 ek` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`3`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN
   `!i j. i < 3 /\ j < 3
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

let EN3_CASE_TAC b =
  let st n = "s"^string_of_int n in
  ENSURES_INIT_TAC "s0" THEN EN3_PK_TAC THEN

  (*** The setup, the public vector t and the message ***)

  ARM_STEPS_TAC EN3_EXEC (1--9) THEN EN3_BUFFER_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (10--12) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (13--31) THEN
  LOCAL_POLYVEC_FROMBYTES_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist ek MOD 2 EXP (8 * 1152)`;
    `pc:num`; `read SP s`; `read X30 s`] 32 THEN
  EN3_TT_TAC b THEN
  ARM_STEPS_TAC EN3_EXEC (33--48) THEN
  LOCAL_POLY_FROMMSG_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist msg`; `pc:num`;
    `read X30 s`] 49 THEN
  EN3_MU_TAC b THEN

  (*** The transposed matrix ***)

  EN3_SEED_TAC b (st 49) THEN
  ARM_STEPS_TAC EN3_EXEC (50--53) THEN INDCPA_GOT_TAC THEN
  LOCAL_GEN_MATRIX_TAC
   [`read X0 s`; `read X1 s`; `rho:byte list`; `k:num`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 54 THEN
  INDCPA_GHOST_TAC "AM" b 2304 (st 54) THEN
  EN3_MATRIX_TAC b `s54:armstate` THEN

  (*** The noise ***)

  ARM_STEPS_TAC EN3_EXEC (55--65) THEN INDCPA_NONCE_TAC 255 THEN
  LOCAL_GETNOISE3_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X4 s`;
    `r:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 255:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 66 THEN
  INDCPA_NOISE_TAC "YS" (b + 9216) 3 "r" "word j" (st 66) THEN
  INDCPA_DISCARD_LETS_TAC THEN
  INDCPA_NONZERO_TAC 16896 (b + 11520) THEN
  ARM_STEPS_TAC EN3_EXEC (67--77) THEN INDCPA_NONCE_TAC 6 THEN
  LOCAL_GETNOISE4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `r:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 6:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 78 THEN
  INDCPA_NOISE_TAC "E1" (b + 6144) 3 "r" "word(3 + j)" (st 78) THEN
  INDCPA_NOISE1_TAC "E2" (b + 11520) "r" "word 6" (st 78) THEN
  INDCPA_DISCARD_LETS_TAC THEN

  (*** The NTT of the noise and its multiplication cache ***)

  ARM_STEPS_TAC EN3_EXEC (79--81) THEN
  LOCAL_POLYVEC_NTT_TAC
   [`read X0 s`; `YS:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 82 THEN
  INDCPA_NTT_TAC "YH" (b + 9216) 3 "YS" "r" "word j" (st 82) THEN
  ARM_STEPS_TAC EN3_EXEC (83--85) THEN
  LOCAL_POLYVEC_MULCACHE_TAC
   [`read X0 s`; `read X1 s`; `YH:num->int16`; `pc:num`; `read SP s`;
    `read X30 s`] 86 THEN
  INDCPA_MULCACHE_TAC "MC" (b + 10752) 3 "YH" (st 86) THEN

  (*** The products with the transposed matrix and with t ***)

  MAP_EVERY (fun q ->
    let a = (b + 1536 * q,"AM",768 * q)
    and y = (b + 9216,"YH") and t = (b + 10752,"MC") in
    ARM_STEPS_TAC EN3_EXEC ((87 + 11 * q)--(92 + 11 * q)) THEN
    INDCPA_BASEMUL3_PRE_TAC a y t (st(92 + 11 * q)) THEN
    LOCAL_BASEMUL_TAC (INDCPA_BASEMUL3_ARGS ("AM",768 * q) "YH" "MC")
      (93 + 11 * q) THEN
    INDCPA_BASEMUL3_DROP_PRE_TAC a y t THEN
    ARM_STEPS_TAC EN3_EXEC ((94 + 11 * q)--(97 + 11 * q))) [0;1;2] THEN
  EN3_AM_BOUND_TAC THEN EN3_U0_TAC b THEN
  ARM_STEPS_TAC EN3_EXEC (120--127) THEN
  INDCPA_BASEMUL3_PRE_TAC (b + 7680,"TT",0) (b + 9216,"YH")
    (b + 10752,"MC") (st 127) THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMUL3_ARGS ("TT",0) "YH" "MC") 128 THEN
  INDCPA_BASEMUL3_DROP_PRE_TAC (b + 7680,"TT",0) (b + 9216,"YH")
    (b + 10752,"MC") THEN
  EN3_TT_BOUND_TAC THEN EN3_V0_TAC b THEN

  (*** The inverse NTTs, adding the noise and the message, reductions ***)

  ARM_STEPS_TAC EN3_EXEC (129--130) THEN
  LOCAL_POLYVEC_INVNTT_TAC
   [`read X0 s`; `U0:num->int16`; `pc:num`; `read SP s`; `read X30 s`]
   131 THEN
  INDCPA_INVNTT_TAC "U1" (b + 4608) 3 "U0" (st 131) THEN
  ARM_STEPS_TAC EN3_EXEC (132--133) THEN
  LOCAL_POLY_INVNTT_TAC
   [`read X0 s`; `V0:num->int16`; `pc:num`; `read SP s`; `read X30 s`]
   134 THEN
  INDCPA_INVNTT1_TAC "V1" (b + 12544) "V0" (st 134) THEN
  ARM_STEPS_TAC EN3_EXEC (135--137) THEN
  LOCAL_POLYVEC_ADD_TAC
   [`read X0 s`; `read X1 s`; `U1:num->int16`; `E1:num->int16`; `pc:num`;
    `read SP s`; `read X30 s`] 138 THEN
  ARM_STEPS_TAC EN3_EXEC (139--141) THEN
  LOCAL_POLY_ADD_TAC
   [`read X0 s`; `read X1 s`; `V1:num->int16`; `E2:num->int16`; `pc:num`;
    `read X30 s`] 142 THEN
  ARM_STEPS_TAC EN3_EXEC (143--146) THEN
  LOCAL_POLY_ADD_TAC
   [`read X0 s`; `read X1 s`;
    `\i. word_add ((V1:num->int16) i) ((E2:num->int16) i)`;
    `MU:num->int16`; `pc:num`; `read X30 s`] 147 THEN
  ARM_STEPS_TAC EN3_EXEC (148--149) THEN
  LOCAL_POLYVEC_REDUCE_TAC
   [`read X0 s`; `\i. word_add ((U1:num->int16) i) ((E1:num->int16) i)`;
    `pc:num`; `read SP s`; `read X30 s`] 150 THEN
  INDCPA_REDUCE_TAC "U3" (b + 4608) 768
    "word_add ((U1:num->int16) i) ((E1:num->int16) i)" (st 150) THEN
  ARM_STEPS_TAC EN3_EXEC (151--152) THEN
  LOCAL_POLY_REDUCE_TAC
   [`read X0 s`;
    `\i. word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i)`;
    `pc:num`; `read X30 s`] 153 THEN
  INDCPA_REDUCE_TAC "V4" (b + 12544) 256
    "word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i)) \
     ((MU:num->int16) i)" (st 153) THEN

  (*** The compression and encoding of u and v ***)

  ARM_STEPS_TAC EN3_EXEC (154--156) THEN INDCPA_GOT_TAC THEN
  LOCAL_POLYVEC_COMPRESS_DU_TAC
   [`read X0 s`; `read X1 s`; `U3:num->int16`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 157 THEN
  EN3_COMPRESS_POST_TAC "U3"
   `ival(word_add ((U1:num->int16) i) ((E1:num->int16) i))` THEN
  ARM_STEPS_TAC EN3_EXEC (158--161) THEN
  LOCAL_POLY_COMPRESS_D4_TAC
   [`read X0 s`; `read X1 s`; `V4:num->int16`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 162 THEN
  EN3_COMPRESS_POST_TAC "V4"
   `ival(word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i))` THEN

  (*** Zeroing the buffers, the stack guard, the return ***)

  INDCPA_MEMSET_LABEL_TAC THEN
  INDCPA_MEMSETS_TAC EN3_EXEC
   [163,166; 172,175; 181,184; 190,193; 199,202; 208,211; 217,220;
    226,229; 235,238] THEN
  ARM_STEPS_TAC EN3_EXEC (244--246) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (247--262) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN EN3_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!c m pk coins (ek:byte list) (msg:byte list) (r:byte list)
    guard mf mc ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        LENGTH ek = 1184 /\ LENGTH msg = 32 /\ LENGTH r = 32 /\
        (!i j. i < 3 /\ j < 3
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 1152 32 ek) [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 16896),16896) /\
        nonoverlapping (c,1088) (word_sub stackpointer (word 16896),16896) /\
        nonoverlapping (pk,1184) (word pc,0x6480) /\
        ALLPAIRS nonoverlapping
         [(c,1088); (word_sub stackpointer (word 16896),16896)]
         [(m,32); (pk,1184); (coins,32); (word pc,0x6480);
          (word(pc + 0x1fff8),8); (guard,8); (word(pc + 0x1ffe8),8);
          (word(pc + 0x1ffd0),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x5310) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [c; m; pk; coins] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                  read (memory :> bytes64(word(pc + 0x1ffd0))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(m,32)) s = num_of_bytelist msg /\
                  read (memory :> bytes(pk,1184)) s = num_of_bytelist ek /\
                  read (memory :> bytes(coins,32)) s = num_of_bytelist r)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(c,1088)) s =
                  num_of_bytelist(kpke_encrypt mlkem768 ek msg r) /\
                  C_RETURN s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(c,1088);
                memory :> bytes(word_sub stackpointer (word 16896),16896)])`,
  EN3_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [EN3_CASE_TAC 3776; EN3_CASE_TAC 3792]);;
