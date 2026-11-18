(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The encryption of K-PKE for ML-KEM-768 (FIPS 203 Algorithm 14). This is   *)
(* the code for mlkem768_indcpa_enc from mlkem-native's portable C           *)
(* implementation compiled by gcc 12 with -Os (see mlkem_native/README.md).  *)
(* It decodes the vector t in the NTT domain from the encryption key and the *)
(* message m from its 32 bytes, generates the transposed matrix from rho     *)
(* (the last 32 bytes of the key), samples y, e1 and e2 from the randomness  *)
(* r, and computes u = NTT^-1(A^T NTT(y)) + e1 and v = NTT^-1(t^T NTT(y)) +  *)
(* e2 + mu, where mu is m decompressed. It writes the compressions of u and  *)
(* v as the ciphertext, zeroing its buffers. It is verified in the whole     *)
(* image (see libmlkem.ml), using the theorems for                           *)
(* mlkem768_polyvec_frombytes, mlkem_poly_frommsg, mlkem768_gen_matrix,      *)
(* mlkem768_poly_getnoise_eta1_4x, mlkem768_polyvec_ntt,                     *)
(* mlkem768_polyvec_mulcache_compute,                                        *)
(* mlkem768_polyvec_basemul_acc_montgomery_cached,                           *)
(* mlkem768_polyvec_invntt_tomont, mlkem_poly_invntt_tomont,                 *)
(* mlkem768_polyvec_add, mlkem_poly_add, mlkem768_polyvec_reduce,            *)
(* mlkem_poly_reduce, mlkem768_polyvec_compress_du and                       *)
(* mlkem_poly_compress_d4 in the image, mlk_zeroize_7 (zeroes a buffer       *)
(* with memset) and the contracts for memset and memcpy. Unlike the -O2      *)
(* build, the code zeroes its buffers, and the copy of rho, by calls to      *)
(* mlk_zeroize_7 instead of calls to memset and stores of zero.              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/polyvec_frombytes_k3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/poly_frommsg_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/gen_matrix_k3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/poly_getnoise_eta1_4x_k3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/polyvec_ntt_k3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/polyvec_mulcache_compute_k3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/basemul_k3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/polyvec_invntt_tomont_k3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/polyvec_add_k3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/poly_add_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/polyvec_reduce_k3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/poly_reduce_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/polyvec_compress_du_k3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/poly_compress_d4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/zeroize_7_spec.ml";;
needs "arm/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image:

    mlkem768_indcpa_enc:
        +0x0: mov     x12, #0x33d0
        +0x4: sub     sp, sp, x12
        +0x8: mov     x4, #0x2a00
        +0xc: stp     x25, x26, [sp, #64]
       +0x10: mov     x25, x0
       +0x14: adrp    x0, <page>
       +0x18: ldr     x0, [x0, #4088]  // got_stack_chk_guard
       +0x1c: stp     x19, x20, [sp, #16]
       +0x20: add     x19, sp, #0xaf
       +0x24: stp     x21, x22, [sp, #32]
       +0x28: and     x19, x19, #0xffffffffffffffe0
       +0x2c: mov     x20, x2
       +0x30: stp     x23, x24, [sp, #48]
       +0x34: mov     x21, x3
       +0x38: mov     x2, #0x2f00
       +0x3c: stp     x27, x28, [sp, #80]
       +0x40: mov     x3, #0x2d00
       +0x44: mov     x22, x1
       +0x48: str     x30, [sp, #96]
       +0x4c: mov     x1, #0x1e00
       +0x50: add     x26, x19, x1
       +0x54: add     x28, x19, x3
       +0x58: ldr     x1, [x0]
       +0x5c: str     x1, [sp, #13256]
       +0x60: mov     x1, #0x0
       +0x64: add     x24, x19, x4
       +0x68: add     x27, x19, x2
       +0x6c: mov     x1, x20
       +0x70: mov     x0, x26
       +0x74: bl      <mlkem768_polyvec_frombytes>
       +0x78: ldr     q0, [x20, #1152]
       +0x7c: mov     x5, #0x3300
       +0x80: ldr     q1, [x20, #1168]
       +0x84: add     x0, x19, x5
       +0x88: mov     x6, #0x1800
       +0x8c: mov     x1, x22
       +0x90: add     x22, x19, x6
       +0x94: stp     q0, q1, [x0]
       +0x98: mov     x0, x27
       +0x9c: bl      <mlkem_poly_frommsg>
       +0xa0: mov     x8, #0x2400
       +0xa4: mov     x7, #0x3300
       +0xa8: add     x0, x19, x7
       +0xac: add     x20, x19, x8
       +0xb0: mov     x1, x0
       +0xb4: mov     w2, #0x1
       +0xb8: str     x0, [sp, #120]
       +0xbc: mov     x0, x19
       +0xc0: bl      <mlkem768_gen_matrix>
       +0xc4: mov     w0, #0xffffffff
       +0xc8: strb    w0, [sp]
       +0xcc: mov     x4, x21
       +0xd0: add     x2, x20, #0x400
       +0xd4: add     x1, x20, #0x200
       +0xd8: mov     x0, x20
       +0xdc: mov     w7, #0x2
       +0xe0: mov     w6, #0x1
       +0xe4: mov     w5, #0x0
       +0xe8: mov     x3, #0x0
       +0xec: bl      <mlkem768_poly_getnoise_eta1_4x>
       +0xf0: mov     x4, x21
       +0xf4: mov     x3, x28
       +0xf8: add     x2, x22, #0x400
       +0xfc: add     x1, x22, #0x200
      +0x100: mov     w0, #0x6
      +0x104: strb    w0, [sp]
      +0x108: mov     w7, #0x5
      +0x10c: mov     w6, #0x4
      +0x110: mov     w5, #0x3
      +0x114: mov     x0, x22
      +0x118: bl      <mlkem768_poly_getnoise_eta1_4x>
      +0x11c: mov     x0, x20
      +0x120: bl      <mlkem768_polyvec_ntt>
      +0x124: mov     x1, x20
      +0x128: mov     x0, x24
      +0x12c: bl      <mlkem768_polyvec_mulcache_compute>
      +0x130: mov     x9, #0x1200
      +0x134: add     x21, x19, x9
      +0x138: mov     x1, x19
      +0x13c: mov     x23, x21
      +0x140: mov     w4, #0x0
      +0x144: mov     x0, x21
      +0x148: mov     x3, x24
      +0x14c: mov     x2, x20
      +0x150: str     x1, [sp, #128]
      +0x154: str     w4, [sp, #140]
      +0x158: bl      <mlkem768_polyvec_basemul_acc_montgomery_cached>
      +0x15c: ldr     x1, [sp, #128]
      +0x160: add     x21, x21, #0x200
      +0x164: ldr     w4, [sp, #140]
      +0x168: add     x1, x1, #0x600
      +0x16c: add     w4, w4, #0x1
      +0x170: cmp     w4, #0x3
      +0x174: b.ne    <mlkem768_indcpa_enc+0x144>
      +0x178: mov     x2, x20
      +0x17c: mov     x3, x24
      +0x180: mov     x1, x26
      +0x184: mov     x0, #0x3100
      +0x188: add     x21, x19, x0
      +0x18c: mov     x0, x21
      +0x190: bl      <mlkem768_polyvec_basemul_acc_montgomery_cached>
      +0x194: mov     x0, x23
      +0x198: bl      <mlkem768_polyvec_invntt_tomont>
      +0x19c: mov     x0, x21
      +0x1a0: bl      <mlkem_poly_invntt_tomont>
      +0x1a4: mov     x1, x22
      +0x1a8: mov     x0, x23
      +0x1ac: bl      <mlkem768_polyvec_add>
      +0x1b0: mov     x1, x28
      +0x1b4: mov     x0, x21
      +0x1b8: bl      <mlkem_poly_add>
      +0x1bc: mov     x1, x27
      +0x1c0: mov     x0, x21
      +0x1c4: bl      <mlkem_poly_add>
      +0x1c8: mov     x0, x23
      +0x1cc: bl      <mlkem768_polyvec_reduce>
      +0x1d0: mov     x0, x21
      +0x1d4: bl      <mlkem_poly_reduce>
      +0x1d8: mov     x1, x23
      +0x1dc: mov     x0, x25
      +0x1e0: bl      <mlkem768_polyvec_compress_du>
      +0x1e4: mov     x1, x21
      +0x1e8: add     x0, x25, #0x3c0
      +0x1ec: bl      <mlkem_poly_compress_d4>
      +0x1f0: mov     x0, x24
      +0x1f4: mov     x1, #0x300
      +0x1f8: bl      <mlk_zeroize_7>
      +0x1fc: mov     x0, x28
      +0x200: mov     x1, #0x200
      +0x204: bl      <mlk_zeroize_7>
      +0x208: mov     x0, x27
      +0x20c: mov     x1, #0x200
      +0x210: bl      <mlk_zeroize_7>
      +0x214: mov     x0, x21
      +0x218: mov     x1, #0x200
      +0x21c: bl      <mlk_zeroize_7>
      +0x220: mov     x0, x23
      +0x224: mov     x1, #0x600
      +0x228: bl      <mlk_zeroize_7>
      +0x22c: mov     x0, x22
      +0x230: mov     x1, #0x600
      +0x234: bl      <mlk_zeroize_7>
      +0x238: mov     x0, x26
      +0x23c: mov     x1, #0x600
      +0x240: bl      <mlk_zeroize_7>
      +0x244: mov     x0, x20
      +0x248: mov     x1, #0x600
      +0x24c: bl      <mlk_zeroize_7>
      +0x250: mov     x0, x19
      +0x254: mov     x1, #0x1200
      +0x258: bl      <mlk_zeroize_7>
      +0x25c: ldr     x0, [sp, #120]
      +0x260: mov     x1, #0x20
      +0x264: bl      <mlk_zeroize_7>
      +0x268: adrp    x0, <page>
      +0x26c: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x270: ldr     x2, [sp, #13256]
      +0x274: ldr     x1, [x0]
      +0x278: subs    x2, x2, x1
      +0x27c: mov     x1, #0x0
      +0x280: b.eq    <mlkem768_indcpa_enc+0x288>
      +0x284: bl      <__stack_chk_fail@plt>
      +0x288: ldp     x19, x20, [sp, #16]
      +0x28c: mov     w0, #0x0
      +0x290: ldp     x21, x22, [sp, #32]
      +0x294: mov     x12, #0x33d0
      +0x298: ldp     x23, x24, [sp, #48]
      +0x29c: ldp     x25, x26, [sp, #64]
      +0x2a0: ldp     x27, x28, [sp, #80]
      +0x2a4: ldr     x30, [sp, #96]
      +0x2a8: add     sp, sp, x12
      +0x2ac: ret
 ***)

let MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem768_indcpa_enc"];;

let EN3_EXEC = MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_OS_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The encryption in FIPS 203 in terms of the values computed by the code:   *)
(* the 12-bit fields of the encryption key as decoded (which may be >= q),   *)
(* the NTT of y and its multiplication cache, the noise e1 and e2, the       *)
(* decompressed message, the products with the transposed matrix and with t  *)
(* in Montgomery form, their inverse NTTs, and the results after adding the  *)
(* noise and the message and reducing, whose compressions are encoded in the *)
(* ciphertext.                                                               *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_K3_RESULT_STMT =
  `!ek m r (TT:num->int16) (YH:num->int16) (MC:num->int16) (E1:num->int16)
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
         num_of_bytelist(kpke_encrypt mlkem768 ek m r)`;;

let KPKE_ENCRYPT_K3_RESULT = assume_spec KPKE_ENCRYPT_K3_RESULT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16. The first 1152 bytes of the encryption key are decoded by          *)
(* mlkem768_polyvec_frombytes and its last 32, rho, are copied as two        *)
(* 128-bit words to the seed for mlkem768_gen_matrix. The message is decoded *)
(* and decompressed by mlkem_poly_frommsg.                                   *)
(* ------------------------------------------------------------------------- *)

let EN3_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 3855)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 3840 else 3824))`;;

let EN3_BUFFER_ADDRESS = assume_spec EN3_BUFFER_ADDRESS_STMT;;

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
  INDCPA_GHOST_TAC "TT" (b + 7680) 768 "s31" THEN
  SUBGOAL_THEN
   `!i. i < 768
        ==> (TT:num->int16) i =
            word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "TT" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s31:armstate` (frees(concl th)) &&
      INDCPA_HAS_CONST "MOD" (concl th) && is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC DIV_MOD_EXP_LOW THEN UNDISCH_TAC `i < 768` THEN ARITH_TAC;
    ALL_TAC];;

let EN3_MU_TAC b =
  INDCPA_GHOST_TAC "MU" (b + 12032) 256 "s42" THEN
  SUBGOAL_THEN
   `!i. i < 256
        ==> (MU:num->int16) i =
            word((3329 * (num_of_bytelist msg DIV 2 EXP i) MOD 2 + 1) DIV 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "MU" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s42:armstate` (frees(concl th)) &&
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
   (mlkem_native_libmlkem_gcc12_Os_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_FROMMSG_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLY_FROMMSG_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GEN_MATRIX_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    INDCPA_GEN_MATRIX_SPEC
      MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT
      `word 1:int64`);;

let LOCAL_GETNOISE3_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    INDCPA_GETNOISE_NULL
     MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GETNOISE4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_NTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_MULCACHE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT
   );;

let LOCAL_BASEMUL_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_BASEMUL_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_INVNTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_INVNTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_ADD_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_ADD_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLYVEC_REDUCE_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLY_REDUCE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_COMPRESS_DU_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_COMPRESS_D4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_ZEROIZE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_ZEROIZE_7_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

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
  INDCPA_GHOST_TAC "U0" (b + 4608) 768 "s130" THEN
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
  INDCPA_GHOST_TAC "V0" (b + 12544) 256 "s138" THEN
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
(* kpke_encrypt mlkem768 ek msg r in common/fips203/fips203.ml, for any ek   *)
(* (FIPS 203 decodes t modulo q, while the code multiplies by the 12-bit     *)
(* fields, which are congruent). The theorem assumes that SampleNTT          *)
(* terminates for each entry of the matrix, as for mlkem768_gen_matrix, and  *)
(* that the stack does not contain address 0. The stack is the 13264 bytes   *)
(* of the function and the 3680 used by mlkem768_gen_matrix below them. The  *)
(* proof is by cases on whether the stack pointer is a multiple of 32, which *)
(* gives the address b of the buffers, at offsets 0 (the matrix), 4608 (u),  *)
(* 6144 (e1), 7680 (t), 9216 (y), 10752 (its multiplication cache), 11520    *)
(* (e2), 12032 (the message), 12544 (v) and 13056 (rho).                     *)
(* ------------------------------------------------------------------------- *)

let EN3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`c:int64`; `m:int64`; `pk:int64`; `coins:int64`; `ek:byte list`;
    `msg:byte list`; `r:byte list`; `guard:int64`; `mf:int64`; `mc:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 16944 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 16944):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
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

let EN3_ZEROIZE_TAC (k0,k) n =
  ARM_STEPS_TAC EN3_EXEC (k0--k) THEN
  LOCAL_ZEROIZE_TAC
   [`read X0 s`; mk_small_numeral n; `mf:int64`; `ea:int64`; `el:num`;
    `ev:num`; `pc:num`; `read SP s`; `read X30 s`] (k + 1);;

let EN3_CASE_TAC b =
  let st n = "s"^string_of_int n in
  ENSURES_INIT_TAC "s0" THEN EN3_PK_TAC THEN

  (*** The setup, the public vector t and the message ***)

  ARM_STEPS_TAC EN3_EXEC (1--6) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (7--11) THEN EN3_BUFFER_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (12--30) THEN
  LOCAL_POLYVEC_FROMBYTES_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist ek MOD 2 EXP (8 * 1152)`;
    `pc:num`; `read SP s`; `read X30 s`] 31 THEN
  EN3_TT_TAC b THEN
  ARM_STEPS_TAC EN3_EXEC (32--41) THEN
  LOCAL_POLY_FROMMSG_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist msg`; `pc:num`;
    `read X30 s`] 42 THEN
  EN3_MU_TAC b THEN

  (*** The transposed matrix ***)

  EN3_SEED_TAC b (st 42) THEN
  ARM_STEPS_TAC EN3_EXEC (43--51) THEN INDCPA_GOT_TAC THEN
  LOCAL_GEN_MATRIX_TAC
   [`read X0 s`; `read X1 s`; `rho:byte list`; `k:num`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 52 THEN
  INDCPA_GHOST_TAC "AM" b 2304 (st 52) THEN
  EN3_MATRIX_TAC b `s52:armstate` THEN

  (*** The noise ***)

  ARM_STEPS_TAC EN3_EXEC (53--63) THEN INDCPA_NONCE_TAC 255 THEN
  LOCAL_GETNOISE3_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X4 s`;
    `r:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 255:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 64 THEN
  INDCPA_NOISE_TAC "YS" (b + 9216) 3 "r" "word j" (st 64) THEN
  INDCPA_DISCARD_LETS_TAC THEN
  INDCPA_NONZERO_TAC 16944 (b + 11520) THEN
  ARM_STEPS_TAC EN3_EXEC (65--75) THEN INDCPA_NONCE_TAC 6 THEN
  LOCAL_GETNOISE4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `r:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 6:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 76 THEN
  INDCPA_NOISE_TAC "E1" (b + 6144) 3 "r" "word(3 + j)" (st 76) THEN
  INDCPA_NOISE1_TAC "E2" (b + 11520) "r" "word 6" (st 76) THEN
  INDCPA_DISCARD_LETS_TAC THEN

  (*** The NTT of the noise and its multiplication cache ***)

  ARM_STEPS_TAC EN3_EXEC (77--78) THEN
  LOCAL_POLYVEC_NTT_TAC
   [`read X0 s`; `YS:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 79 THEN
  INDCPA_NTT_TAC "YH" (b + 9216) 3 "YS" "r" "word j" (st 79) THEN
  ARM_STEPS_TAC EN3_EXEC (80--82) THEN
  LOCAL_POLYVEC_MULCACHE_TAC
   [`read X0 s`; `read X1 s`; `YH:num->int16`; `pc:num`; `read SP s`;
    `read X30 s`] 83 THEN
  INDCPA_MULCACHE_TAC "MC" (b + 10752) 3 "YH" (st 83) THEN

  (*** The products with the transposed matrix and with t ***)

  MAP_EVERY (fun (q,pre1,pre2,post2) ->
    let a = (b + 1536 * q,"AM",768 * q)
    and y = (b + 9216,"YH") and t = (b + 10752,"MC") in
    ARM_STEPS_TAC EN3_EXEC (pre1--pre2) THEN
    INDCPA_BASEMUL3_PRE_TAC a y t (st pre2) THEN
    LOCAL_BASEMUL_TAC (INDCPA_BASEMUL3_ARGS ("AM",768 * q) "YH" "MC")
      (pre2 + 1) THEN
    INDCPA_BASEMUL3_DROP_PRE_TAC a y t THEN
    ARM_STEPS_TAC EN3_EXEC ((pre2 + 2)--post2))
   [0,84,94,102; 1,103,108,116; 2,117,122,130] THEN
  EN3_AM_BOUND_TAC THEN EN3_U0_TAC b THEN
  ARM_STEPS_TAC EN3_EXEC (131--137) THEN
  INDCPA_BASEMUL3_PRE_TAC (b + 7680,"TT",0) (b + 9216,"YH")
    (b + 10752,"MC") (st 137) THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMUL3_ARGS ("TT",0) "YH" "MC") 138 THEN
  INDCPA_BASEMUL3_DROP_PRE_TAC (b + 7680,"TT",0) (b + 9216,"YH")
    (b + 10752,"MC") THEN
  EN3_TT_BOUND_TAC THEN EN3_V0_TAC b THEN

  (*** The inverse NTTs, adding the noise and the message, reductions ***)

  ARM_STEPS_TAC EN3_EXEC (139--140) THEN
  LOCAL_POLYVEC_INVNTT_TAC
   [`read X0 s`; `U0:num->int16`; `pc:num`; `read SP s`; `read X30 s`]
   141 THEN
  INDCPA_INVNTT_TAC "U1" (b + 4608) 3 "U0" (st 141) THEN
  ARM_STEPS_TAC EN3_EXEC (142--143) THEN
  LOCAL_POLY_INVNTT_TAC
   [`read X0 s`; `V0:num->int16`; `pc:num`; `read SP s`; `read X30 s`]
   144 THEN
  INDCPA_INVNTT1_TAC "V1" (b + 12544) "V0" (st 144) THEN
  ARM_STEPS_TAC EN3_EXEC (145--147) THEN
  LOCAL_POLYVEC_ADD_TAC
   [`read X0 s`; `read X1 s`; `U1:num->int16`; `E1:num->int16`; `pc:num`;
    `read SP s`; `read X30 s`] 148 THEN
  ARM_STEPS_TAC EN3_EXEC (149--151) THEN
  LOCAL_POLY_ADD_TAC
   [`read X0 s`; `read X1 s`; `V1:num->int16`; `E2:num->int16`; `pc:num`;
    `read X30 s`] 152 THEN
  ARM_STEPS_TAC EN3_EXEC (153--155) THEN
  LOCAL_POLY_ADD_TAC
   [`read X0 s`; `read X1 s`;
    `\i. word_add ((V1:num->int16) i) ((E2:num->int16) i)`;
    `MU:num->int16`; `pc:num`; `read X30 s`] 156 THEN
  ARM_STEPS_TAC EN3_EXEC (157--158) THEN
  LOCAL_POLYVEC_REDUCE_TAC
   [`read X0 s`; `\i. word_add ((U1:num->int16) i) ((E1:num->int16) i)`;
    `pc:num`; `read SP s`; `read X30 s`] 159 THEN
  INDCPA_REDUCE_TAC "U3" (b + 4608) 768
    "word_add ((U1:num->int16) i) ((E1:num->int16) i)" (st 159) THEN
  ARM_STEPS_TAC EN3_EXEC (160--161) THEN
  LOCAL_POLY_REDUCE_TAC
   [`read X0 s`;
    `\i. word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i)`;
    `pc:num`; `read X30 s`] 162 THEN
  INDCPA_REDUCE_TAC "V4" (b + 12544) 256
    "word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i)) \
     ((MU:num->int16) i)" (st 162) THEN

  (*** The compression and encoding of u and v ***)

  ARM_STEPS_TAC EN3_EXEC (163--165) THEN INDCPA_GOT_TAC THEN
  LOCAL_POLYVEC_COMPRESS_DU_TAC
   [`read X0 s`; `read X1 s`; `U3:num->int16`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 166 THEN
  EN3_COMPRESS_POST_TAC "U3"
   `ival(word_add ((U1:num->int16) i) ((E1:num->int16) i))` THEN
  ARM_STEPS_TAC EN3_EXEC (167--169) THEN
  LOCAL_POLY_COMPRESS_D4_TAC
   [`read X0 s`; `read X1 s`; `V4:num->int16`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 170 THEN
  EN3_COMPRESS_POST_TAC "V4"
   `ival(word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i))` THEN

  (*** Zeroing the buffers, the stack guard, the return ***)

  EN3_ZEROIZE_TAC (171,173) 768 THEN
  EN3_ZEROIZE_TAC (175,177) 512 THEN
  EN3_ZEROIZE_TAC (179,181) 512 THEN
  EN3_ZEROIZE_TAC (183,185) 512 THEN
  EN3_ZEROIZE_TAC (187,189) 1536 THEN
  EN3_ZEROIZE_TAC (191,193) 1536 THEN
  EN3_ZEROIZE_TAC (195,197) 1536 THEN
  EN3_ZEROIZE_TAC (199,201) 1536 THEN
  EN3_ZEROIZE_TAC (203,205) 4608 THEN
  EN3_ZEROIZE_TAC (207,209) 32 THEN
  ARM_STEPS_TAC EN3_EXEC (211--211) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (212--227) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN EN3_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!c m pk coins (ek:byte list) (msg:byte list) (r:byte list)
    guard mf mc ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        LENGTH ek = 1184 /\ LENGTH msg = 32 /\ LENGTH r = 32 /\
        (!i j. i < 3 /\ j < 3
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 1152 32 ek) [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 16944),16944) /\
        nonoverlapping (c,1088) (word_sub stackpointer (word 16944),16944) /\
        nonoverlapping (pk,1184) (word pc,libmlkem_size) /\
        ALLPAIRS nonoverlapping
         [(c,1088); (word_sub stackpointer (word 16944),16944)]
         [(m,32); (pk,1184); (coins,32); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8);
          (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlkem768_indcpa_enc) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [c; m; pk; coins] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
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
                memory :> bytes(word_sub stackpointer (word 16944),16944)])`;;

let MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset (for mlkem768_gen_matrix) and the safety contract for memcpy. The  *)
(* events depend only on the addresses and on rho, the last 32 bytes of the  *)
(* public key, through the samples of SampleNTT for the transposed matrix,   *)
(* but not on the message or the randomness. As for the correctness proof,   *)
(* the proof is by cases on whether the stack pointer is a multiple of 32,   *)
(* with the events in the two cases as the two branches of the template.     *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let EN_SAFE_TEMPLATE =
 `\(c:int64) (m:int64) (pk:int64) (coins:int64) (guard:int64) (mf:int64)
   (mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64)
   (rho:byte list).
   if aligned 32 stackpointer
   then f_ev_a c m pk coins guard mf mc pc stackpointer returnaddress rho
   else f_ev_u c m pk coins guard mf mc pc stackpointer returnaddress rho
   :(uarch_event)list`;;

let EN_SAFE_ALLOWED =
  [`pc:num`; `c:int64`; `m:int64`; `pk:int64`; `coins:int64`;
   `guard:int64`; `mf:int64`; `mc:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `rho:byte list`];;

let EN3_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th)
    then ASSUME_CALLEE_SAFETY_TAILED_TAC
          (INDCPA_GEN_MATRIX_SAFE_SPEC
            (MATCH_MP MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_OS_IMAGE_SUBROUTINE_SAFE
                      th) `word 1:int64`) "H_GM" THEN
         ASSUME_TAC(CONJUNCT2(MATCH_MP MEMSET_FULL_CONTRACT th))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memset_safety_contract mf ea el ev`) (concl th)
    then ASSUME_CALLEE_SAFETY_TAILED_TAC
          (MATCH_MP MLKEM_NATIVE_ZEROIZE_7_GCC12_OS_IMAGE_SUBROUTINE_SAFE th)
          "H_ZEROIZE"
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th1 ->
    if can (term_match [] `memset_safety_contract mf ea el ev`) (concl th1)
    then FIRST_X_ASSUM(fun th2 ->
      let gth = MATCH_MP
        MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_OS_IMAGE_SUBROUTINE_SAFE
        (CONJ th1 th2) in
      ASSUME_CALLEE_SAFETY_TAILED_TAC (INDCPA_GETNOISE_NULL_SAFE gth)
       "H_GETNOISE3" THEN
      ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC gth "H_GETNOISE")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K3_GCC12_OS_IMAGE_SUBROUTINE_SAFE
    "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_FROMMSG_GCC12_OS_IMAGE_SUBROUTINE_SAFE)
    "H_FROMMSG" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_OS_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_OS_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_BASEMUL_K3_GCC12_OS_IMAGE_SUBROUTINE_SAFE "H_BASEMUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K3_GCC12_OS_IMAGE_SUBROUTINE_SAFE
    "H_INVNTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_SAFE)
    "H_POLY_INVNTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_OS_IMAGE_SUBROUTINE_SAFE "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_SAFE)
    "H_POLY_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_REDUCE_K3_GCC12_OS_IMAGE_SUBROUTINE_SAFE
    "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_REDUCE_GCC12_OS_IMAGE_SUBROUTINE_SAFE
    "H_POLY_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_OS_IMAGE_SUBROUTINE_SAFE
    "H_COMPRESS_DU" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_OS_IMAGE_SUBROUTINE_SAFE
    "H_COMPRESS_DV" THEN
  CONCRETIZE_F_EVENTS_TAC EN_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 16944):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
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

let EN3_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_Os_mc,EN3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_Os_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref EN_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let EN3_SAFE_CASE_TAC b =
  let e = `e:(uarch_event)list` in
  let x n = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            mk_const("X"^string_of_int n,[])),`s:armstate`) in
  let rest = [`pc:num`; `read SP s`; `read X30 s`] in
  let call = EN3_SAFE_CALL_TAC in
  ENSURES_INIT_TAC "s0" THEN EN3_PK_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (1--6) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (7--11) THEN EN3_BUFFER_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (12--30) THEN
  call "H_FROMBYTES" ([e; x 0; x 1] @ rest) 31 THEN
  ARM_STEPS_TAC EN3_EXEC (32--41) THEN
  call "H_FROMMSG" [e; x 0; x 1; `pc:num`; `read X30 s`] 42 THEN
  EN3_SEED_TAC b "s42" THEN
  ARM_STEPS_TAC EN3_EXEC (43--51) THEN INDCPA_GOT_TAC THEN
  call "H_GM" ([e; x 0; x 1; `rho:byte list`; `k:num`; `guard:int64`] @ rest)
   52 THEN
  ARM_STEPS_TAC EN3_EXEC (53--63) THEN
  call "H_GETNOISE3" ([e; x 0; x 1; x 2; x 4; `guard:int64`] @ rest) 64 THEN
  INDCPA_NONZERO_TAC 16944 (b + 11520) THEN
  ARM_STEPS_TAC EN3_EXEC (65--75) THEN
  call "H_GETNOISE" ([e; x 0; x 1; x 2; x 3; x 4; `guard:int64`] @ rest)
   76 THEN
  ARM_STEPS_TAC EN3_EXEC (77--78) THEN
  call "H_NTT" ([e; x 0] @ rest) 79 THEN
  ARM_STEPS_TAC EN3_EXEC (80--82) THEN
  call "H_MULCACHE" ([e; x 0; x 1] @ rest) 83 THEN
  MAP_EVERY (fun (pre1,pre2,post2) ->
    ARM_STEPS_TAC EN3_EXEC (pre1--pre2) THEN
    call "H_BASEMUL" [e; x 1; x 2; x 3; x 0; `pc:num`; `read X30 s`]
     (pre2 + 1) THEN
    ARM_STEPS_TAC EN3_EXEC ((pre2 + 2)--post2))
   [84,94,102; 103,108,116; 117,122,130] THEN
  ARM_STEPS_TAC EN3_EXEC (131--137) THEN
  call "H_BASEMUL" [e; x 1; x 2; x 3; x 0; `pc:num`; `read X30 s`] 138 THEN
  ARM_STEPS_TAC EN3_EXEC (139--140) THEN
  call "H_INVNTT" ([e; x 0] @ rest) 141 THEN
  ARM_STEPS_TAC EN3_EXEC (142--143) THEN
  call "H_POLY_INVNTT" ([e; x 0] @ rest) 144 THEN
  ARM_STEPS_TAC EN3_EXEC (145--147) THEN
  call "H_ADD" ([e; x 0; x 1] @ rest) 148 THEN
  ARM_STEPS_TAC EN3_EXEC (149--151) THEN
  call "H_POLY_ADD" [e; x 0; x 1; `pc:num`; `read X30 s`] 152 THEN
  ARM_STEPS_TAC EN3_EXEC (153--155) THEN
  call "H_POLY_ADD" [e; x 0; x 1; `pc:num`; `read X30 s`] 156 THEN
  ARM_STEPS_TAC EN3_EXEC (157--158) THEN
  call "H_REDUCE" ([e; x 0] @ rest) 159 THEN
  ARM_STEPS_TAC EN3_EXEC (160--161) THEN
  call "H_POLY_REDUCE" [e; x 0; `pc:num`; `read X30 s`] 162 THEN
  ARM_STEPS_TAC EN3_EXEC (163--165) THEN INDCPA_GOT_TAC THEN
  call "H_COMPRESS_DU" ([e; x 0; x 1; `guard:int64`] @ rest) 166 THEN
  ARM_STEPS_TAC EN3_EXEC (167--169) THEN
  call "H_COMPRESS_DV" ([e; x 0; x 1; `guard:int64`] @ rest) 170 THEN
  MAP_EVERY (fun (k0,k,n) ->
    ARM_STEPS_TAC EN3_EXEC (k0--k) THEN
    call "H_ZEROIZE" [e; x 0; mk_small_numeral n; `pc:num`; `read SP s`;
                      `read X30 s`] (k + 1))
   [171,173,768; 175,177,512; 179,181,512; 183,185,512; 187,189,1536;
    191,193,1536; 195,197,1536; 199,201,1536; 203,205,4608; 207,209,32] THEN
  ARM_STEPS_TAC EN3_EXEC (211--211) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (212--227) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MEMACCESS_DROP_ZERO_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
   memset_full_contract mf ea el ev /\ memcpy_safety_contract mc ea el ev
   ==> exists f_events.
        forall e c m pk coins (ek:byte list) guard pc stackpointer
               returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH ek = 1184 /\
          (!i j. i < 3 /\ j < 3
                 ==> mlkem_samplentt_terminates
                      (APPEND (mlkem_slice 1152 32 ek) [word j; word i])) /\
          nonoverlapping (word 0,1)
           (word_sub stackpointer (word 16944),16944) /\
          nonoverlapping (c,1088)
           (word_sub stackpointer (word 16944),16944) /\
          nonoverlapping (pk,1184) (word pc,libmlkem_size) /\
          ALLPAIRS nonoverlapping
           [(c,1088); (word_sub stackpointer (word 16944),16944)]
           [(m,32); (pk,1184); (coins,32); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_Os_mc /\
                    read PC s = word (pc + mlkem768_indcpa_enc) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [c; m; pk; coins] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(pk,1184)) s = num_of_bytelist ek /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events c m pk coins guard mf mc pc
                              (word_sub stackpointer (word 16944))
                              returnaddress (mlkem_slice 1152 32 ek) /\
                       memaccess_inbounds e2
                        [m,32; pk,1184; coins,32; c,1088;
                         word_sub stackpointer (word 16944),16944;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + rodata_mlk_zetas),256]
                        [c,1088; word_sub stackpointer (word 16944),16944]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(c,1088);
                  memory :> bytes(word_sub stackpointer (word 16944),16944)])`;;

let MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
