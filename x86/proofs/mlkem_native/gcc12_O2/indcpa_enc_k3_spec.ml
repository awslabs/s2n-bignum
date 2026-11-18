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
(* (the last 32 bytes of the key), samples y (with eta = 2), e1 and e2       *)
(* (with eta = 2) from the randomness r, and computes u = NTT^-1(A^T         *)
(* NTT(y)) + e1 and v = NTT^-1(t^T NTT(y)) + e2 + mu, where mu is m          *)
(* decompressed. It writes the compressions of u and v as the ciphertext,    *)
(* zeroing its buffers. It is verified in the whole image (see libmlkem.ml), *)
(* using the theorems for mlkem768_polyvec_frombytes, mlkem_poly_frommsg,    *)
(* mlkem768_gen_matrix, mlkem768_poly_getnoise_eta1_4x,                      *)
(* mlkem768_polyvec_ntt, mlkem768_polyvec_mulcache_compute,                  *)
(* mlkem768_polyvec_basemul_acc_montgomery_cached,                           *)
(* mlkem768_polyvec_invntt_tomont, mlkem_poly_invntt_tomont,                 *)
(* mlkem768_polyvec_add, mlkem_poly_add, mlkem768_polyvec_reduce,            *)
(* mlkem_poly_reduce, mlkem768_polyvec_compress_du and                       *)
(* mlkem_poly_compress_d4 in the image.                                      *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/polyvec_frombytes_k3_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_frommsg_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/gen_matrix_k3_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_getnoise_eta1_4x_k3_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/polyvec_ntt_k3_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/polyvec_mulcache_compute_k3_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/basemul_k3_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/polyvec_invntt_tomont_k3_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/polyvec_add_k3_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_add_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/polyvec_reduce_k3_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_reduce_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/polyvec_compress_du_k3_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_compress_d4_spec.ml";;
needs "x86/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image:

    mlkem768_indcpa_enc:
       +0x0: lea    r10,[rsp+0x8]
       +0x5: and    rsp,0xffffffffffffffe0
       +0x9: push   QWORD PTR [r10-0x8]
       +0xd: push   rbp
       +0xe: mov    rbp,rsp
      +0x11: push   r15
      +0x13: push   r14
      +0x15: lea    rax,[rbp-0x2430]
      +0x1c: lea    r14,[rbp-0x2d30]
      +0x23: push   r13
      +0x25: mov    r13,rdx
      +0x28: push   r12
      +0x2a: mov    r12,rcx
      +0x2d: push   r10
      +0x2f: push   rbx
      +0x30: mov    rbx,rsi
      +0x33: mov    rsi,rdx
      +0x36: sub    rsp,0x3360
      +0x3d: mov    QWORD PTR [rbp-0x3380],rdi
      +0x44: mov    rdi,rax
      +0x47: mov    QWORD PTR [rbp-0x3370],rax
      +0x4e: call   <mlkem768_polyvec_frombytes>
      +0x53: lea    rax,[rbp-0x3130]
      +0x5a: mov    rsi,rbx
      +0x5d: movdqu xmm1,XMMWORD PTR [r13+0x480]
      +0x66: movdqu xmm2,XMMWORD PTR [r13+0x490]
      +0x6f: mov    rdi,rax
      +0x72: mov    QWORD PTR [rbp-0x3378],rax
      +0x79: lea    rbx,[rbp-0x2a30]
      +0x80: movaps XMMWORD PTR [rbp-0x3350],xmm1
      +0x87: lea    r13,[rbp-0x1830]
      +0x8e: movaps XMMWORD PTR [rbp-0x3340],xmm2
      +0x95: call   <mlkem_poly_frommsg>
      +0x9a: lea    rax,[rbp-0x1230]
      +0xa1: mov    edx,0x1
      +0xa6: lea    rsi,[rbp-0x3350]
      +0xad: mov    rdi,rax
      +0xb0: mov    QWORD PTR [rbp-0x3360],rax
      +0xb7: mov    QWORD PTR [rbp-0x3388],rsi
      +0xbe: call   <mlkem768_gen_matrix>
      +0xc3: sub    rsp,0x8
      +0xc7: mov    r8,r12
      +0xca: xor    r9d,r9d
      +0xcd: push   0xff
      +0xd2: lea    rdx,[rbp-0x2630]
      +0xd9: xor    ecx,ecx
      +0xdb: mov    rdi,rbx
      +0xde: push   0x2
      +0xe0: lea    rsi,[rbp-0x2830]
      +0xe7: push   0x1
      +0xe9: call   <mlkem768_poly_getnoise_eta1_4x>
      +0xee: lea    rax,[rbp-0x1e30]
      +0xf5: add    rsp,0x18
      +0xf9: mov    r8,r12
      +0xfc: lea    rcx,[rbp-0x2f30]
     +0x103: mov    rdi,rax
     +0x106: mov    QWORD PTR [rbp-0x3368],rax
     +0x10d: lea    rdx,[rbp-0x1a30]
     +0x114: mov    QWORD PTR [rbp-0x3358],rcx
     +0x11b: lea    rsi,[rbp-0x1c30]
     +0x122: mov    r9d,0x3
     +0x128: push   0x6
     +0x12a: push   0x5
     +0x12c: push   0x4
     +0x12e: call   <mlkem768_poly_getnoise_eta1_4x>
     +0x133: add    rsp,0x20
     +0x137: mov    rdi,rbx
     +0x13a: call   <mlkem768_polyvec_ntt>
     +0x13f: mov    rsi,rbx
     +0x142: mov    rdi,r14
     +0x145: call   <mlkem768_polyvec_mulcache_compute>
     +0x14a: mov    QWORD PTR [rbp-0x3390],r13
     +0x151: lea    rax,[rbp-0x30]
     +0x155: mov    r12,QWORD PTR [rbp-0x3360]
     +0x15c: mov    r15,rax
     +0x15f: mov    rsi,r12
     +0x162: mov    rdi,r13
     +0x165: mov    rcx,r14
     +0x168: mov    rdx,rbx
     +0x16b: add    r12,0x600
     +0x172: add    r13,0x200
     +0x179: call   <mlkem768_polyvec_basemul_acc_montgomery_cached>
     +0x17e: cmp    r12,r15
     +0x181: jne    <mlkem768_indcpa_enc+0x15f>
     +0x183: lea    r12,[rbp-0x3330]
     +0x18a: mov    r13,QWORD PTR [rbp-0x3390]
     +0x191: mov    rcx,r14
     +0x194: mov    rdx,rbx
     +0x197: mov    rsi,QWORD PTR [rbp-0x3370]
     +0x19e: mov    rdi,r12
     +0x1a1: call   <mlkem768_polyvec_basemul_acc_montgomery_cached>
     +0x1a6: mov    rdi,r13
     +0x1a9: call   <mlkem768_polyvec_invntt_tomont>
     +0x1ae: mov    rdi,r12
     +0x1b1: call   <mlkem_poly_invntt_tomont>
     +0x1b6: mov    rsi,QWORD PTR [rbp-0x3368]
     +0x1bd: mov    rdi,r13
     +0x1c0: call   <mlkem768_polyvec_add>
     +0x1c5: mov    rsi,QWORD PTR [rbp-0x3358]
     +0x1cc: mov    rdi,r12
     +0x1cf: call   <mlkem_poly_add>
     +0x1d4: mov    rsi,QWORD PTR [rbp-0x3378]
     +0x1db: mov    rdi,r12
     +0x1de: call   <mlkem_poly_add>
     +0x1e3: mov    rdi,r13
     +0x1e6: call   <mlkem768_polyvec_reduce>
     +0x1eb: mov    rdi,r12
     +0x1ee: call   <mlkem_poly_reduce>
     +0x1f3: mov    r15,QWORD PTR [rbp-0x3380]
     +0x1fa: mov    rsi,r13
     +0x1fd: mov    rdi,r15
     +0x200: call   <mlkem768_polyvec_compress_du>
     +0x205: mov    rax,r15
     +0x208: mov    rsi,r12
     +0x20b: add    rax,0x3c0
     +0x211: mov    rdi,rax
     +0x214: call   <mlkem_poly_compress_d4>
     +0x219: xor    eax,eax
     +0x21b: mov    rdi,r14
     +0x21e: mov    ecx,0x60
     +0x223: rep    stos QWORD PTR es:[rdi],rax
     +0x226: mov    rdi,QWORD PTR [rbp-0x3358]
     +0x22d: mov    ecx,0x40
     +0x232: mov    rdx,QWORD PTR [rbp-0x3358]
     +0x239: rep    stos QWORD PTR es:[rdi],rax
     +0x23c: mov    rdi,QWORD PTR [rbp-0x3378]
     +0x243: mov    ecx,0x40
     +0x248: mov    rdx,QWORD PTR [rbp-0x3378]
     +0x24f: rep    stos QWORD PTR es:[rdi],rax
     +0x252: mov    ecx,0x40
     +0x257: mov    rdi,r12
     +0x25a: rep    stos QWORD PTR es:[rdi],rax
     +0x25d: mov    ecx,0xc0
     +0x262: mov    rdi,r13
     +0x265: rep    stos QWORD PTR es:[rdi],rax
     +0x268: mov    rdi,QWORD PTR [rbp-0x3368]
     +0x26f: mov    ecx,0xc0
     +0x274: mov    rdx,QWORD PTR [rbp-0x3368]
     +0x27b: rep    stos QWORD PTR es:[rdi],rax
     +0x27e: mov    rdi,QWORD PTR [rbp-0x3370]
     +0x285: mov    ecx,0xc0
     +0x28a: rep    stos QWORD PTR es:[rdi],rax
     +0x28d: mov    rdi,QWORD PTR [rbp-0x3370]
     +0x294: mov    ecx,0xc0
     +0x299: mov    rdi,rbx
     +0x29c: rep    stos QWORD PTR es:[rdi],rax
     +0x29f: mov    rdi,QWORD PTR [rbp-0x3360]
     +0x2a6: mov    ecx,0x240
     +0x2ab: rep    stos QWORD PTR es:[rdi],rax
     +0x2ae: mov    rdi,QWORD PTR [rbp-0x3360]
     +0x2b5: pxor   xmm0,xmm0
     +0x2b9: mov    rax,QWORD PTR [rbp-0x3388]
     +0x2c0: movaps XMMWORD PTR [rbp-0x3350],xmm0
     +0x2c7: movaps XMMWORD PTR [rbp-0x3340],xmm0
     +0x2ce: lea    rsp,[rbp-0x30]
     +0x2d2: xor    eax,eax
     +0x2d4: pop    rbx
     +0x2d5: pop    r10
     +0x2d7: pop    r12
     +0x2d9: pop    r13
     +0x2db: pop    r14
     +0x2dd: pop    r15
     +0x2df: pop    rbp
     +0x2e0: lea    rsp,[r10-0x8]
     +0x2e4: ret
 ***)

let MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem768_indcpa_enc"];;

let EN3_EXEC = MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The encryption in FIPS 203 in terms of the values computed by the code:   *)
(* the 12-bit fields of the encryption key as decoded (which may be >= q),   *)
(* the NTT of y and its multiplication cache, the noise e1 and e2, the       *)
(* decompressed message, the products with the transposed matrix and with t  *)
(* in Montgomery form, their inverse NTTs, and the results after adding the  *)
(* noise and the message and reducing, whose compressions are encoded in the *)
(* ciphertext. This is as for AArch64.                                       *)
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

let KPKE_ENCRYPT_K3_RESULT =
  assume_spec KPKE_ENCRYPT_K3_RESULT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, by AND with   *)
(* -32 before the pushes of a copy of the return address, RBP, R15, R14,     *)
(* R13, R12, R10 and RBX, with RBP as a frame pointer, and their addresses   *)
(* are offsets from the frame variable bot of INDCPA_BOT_TAC, the bottom of  *)
(* the stacks of the callees 3744 bytes below them: rho (the seed of the     *)
(* matrix) at bot + 3808, v at bot + 3840, the message at bot + 4352, e2 at  *)
(* bot + 4864, the multiplication cache of y at bot + 5376, y at bot + 6144, *)
(* t at bot + 7680, e1 at bot + 9216, u at bot + 10752 and the matrix at     *)
(* bot + 12288, with pointers to some of them saved below rho. The callees   *)
(* mlkem_poly_add and mlkem768_polyvec_add need some of them to be aligned   *)
(* to 16 bytes, as do the stores of rho by MOVAPS relative to RBP, which is  *)
(* bot + 16944, so that is given as aligned too (the simulation checks the   *)
(* alignment of RBP + d after removing the multiple of 16 d). The first 1152 *)
(* bytes of the encryption key are decoded by mlkem768_polyvec_frombytes and *)
(* its last 32, rho, are copied as two 128-bit words to the seed for         *)
(* mlkem768_gen_matrix by legacy SSE moves through XMM1 and XMM2, which keep *)
(* the upper halves of YMM1 and YMM2, so their values after the first call   *)
(* are named by INDCPA_YMM_TAC. The message is decoded and decompressed by   *)
(* mlkem_poly_frommsg.                                                       *)
(* ------------------------------------------------------------------------- *)

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

let EN3_TT_TAC =
  INDCPA_GHOST_TAC "TT" 7680 768 "s23" THEN
  SUBGOAL_THEN
   `!i. i < 768
        ==> (TT:num->int16) i =
            word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "TT" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s23:x86state` (frees(concl th)) &&
      INDCPA_HAS_CONST "MOD" (concl th) && is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC DIV_MOD_EXP_LOW THEN UNDISCH_TAC `i < 768` THEN ARITH_TAC;
    ALL_TAC];;

let EN3_MU_TAC =
  INDCPA_GHOST_TAC "MU" 4352 256 "s35" THEN
  SUBGOAL_THEN
   `!i. i < 256
        ==> (MU:num->int16) i =
            word((3329 * (num_of_bytelist msg DIV 2 EXP i) MOD 2 + 1) DIV 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "MU" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s35:x86state` (frees(concl th)) &&
      can (find_term (fun t -> t = `3329`)) (concl th) &&
      is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

let EN3_SEED_TAC s =
  MP_TAC(SPECL [INDCPA_SP 3808; `num_of_bytelist rho`;
                mk_var(s,`:x86state`)] GENMAT_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `rho:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* The facts about the stages of the computation other than those given by   *)
(* the tactics in mlkem_native_indcpa.ml: the coefficients of the transposed *)
(* matrix as given by SampleNTT, the bounds on the inputs of the             *)
(* multiplications, the products with the rows of the transposed matrix and  *)
(* with t, and the bounds on the inputs of the compressions. This is as for  *)
(* AArch64.                                                                  *)
(* ------------------------------------------------------------------------- *)

let EN3_MATRIX_TAC s =
  let addr = parse_term(Printf.sprintf
    "word_add bot (word (%d + 512 * (3 * q + j))):int64" 12288) in
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

let EN3_U0_TAC =
  INDCPA_GHOST_TAC "U0" 10752 768 "s112" THEN
  SUBGOAL_THEN EN3_U0_GOAL ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THENL
     (map (fun q -> INDCPA_BASEMUL3_ROW_TAC "U0" (10752 + 512 * q)
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

let EN3_V0_TAC =
  INDCPA_GHOST_TAC "V0" 3840 256 "s120" THEN
  SUBGOAL_THEN EN3_V0_GOAL ASSUME_TAC THENL
   [INDCPA_BASEMUL3_ROW_TAC "V0" 3840 "ttbound" [] EN3_BASEMUL_DEFS;
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
(* Correctness proof. The encryption key ek of 1184 bytes is at pk, the      *)
(* message msg of 32 bytes at m and the randomness r of 32 bytes at coins,   *)
(* and the ciphertext of 1088 bytes written at c is that of kpke_encrypt     *)
(* mlkem768 ek msg r in common/fips203/fips203.ml, for any ek (FIPS 203      *)
(* decodes t modulo q, while the code multiplies by the 12-bit fields, which *)
(* are congruent). The theorem assumes that SampleNTT terminates for each    *)
(* entry of the matrix, as for mlkem768_gen_matrix, and that the stack does  *)
(* not contain address 0. The stack is the 16992 bytes below the return      *)
(* address, for up to 31 bytes for the alignment, the 13216 bytes of the     *)
(* pushes and the buffers and the 3744 used by the callees below them. The   *)
(* matrix is generated with transposition, so the theorem for                *)
(* mlkem768_gen_matrix is specialized to that case. The fourth output of the *)
(* first call of mlkem768_poly_getnoise_eta1_4x is a null pointer (its       *)
(* fourth nonce is 255), so the theorem is specialized to that case; in the  *)
(* second call, the fourth output is e2, which is not null since the stack   *)
(* does not contain address 0. The products with the rows of the matrix are  *)
(* computed in a loop, which the simulation unrolls, the comparisons of the  *)
(* pointers in the frame deciding its branch (INDCPA_PTR_TAC).               *)
(* ------------------------------------------------------------------------- *)

let EN3_FRAME = (16992,0,3744,13216);;

let EN3_CALL th =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,REWRITE_RULE[ALL] th);;

let EN3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`c:int64`; `m:int64`; `pk:int64`; `coins:int64`; `ek:byte list`;
    `msg:byte list`; `r:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 16992 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
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

let EN3_SETUP_TAC =
  INDCPA_BOT_TAC EN3_FRAME
   [3808; 3824; 3840; 4352; 4864; 9216; 10752; 16944] THEN
  INDCPA_FRAME_TAC ["memory :> bytes(c:int64,1088)"] EN3_FRAME THEN
  INDCPA_NONOV_TAC 16960
   [`c:int64,1088`; `m:int64,32`; `pk:int64,1184`; `coins:int64,32`;
    `word pc:int64,libmlkem_size`; `word_add stackpointer (word 16992):int64,8`] THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   ["rbx_init",`RBX`; "rbp_init",`RBP`; "r12_init",`R12`;
    "r13_init",`R13`; "r14_init",`R14`; "r15_init",`R15`];;

let EN3_MAIN_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = EN3_CALL in
  ENSURES_INIT_TAC "s0" THEN EN3_PK_TAC THEN

  (*** The public vector t and the message ***)

  X86_STEPS_TAC EN3_EXEC (1--2) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC EN3_EXEC (3--22) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLYVEC_FROMBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `num_of_bytelist ek MOD 2 EXP (8 * 1152)`] @
    post) 23 THEN
  INDCPA_NORM_TAC THEN EN3_TT_TAC THEN INDCPA_YMM_TAC "s23" THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC EN3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (24--34) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `num_of_bytelist msg`] @ post) 35 THEN
  INDCPA_NORM_TAC THEN EN3_MU_TAC THEN

  (*** The transposed matrix ***)

  EN3_SEED_TAC "s35" THEN
  X86_STEPS_TAC EN3_EXEC (36--42) THEN INDCPA_NORM_TAC THEN
  call (INDCPA_GEN_MATRIX_SPEC
         MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
         `word 1:int64`)
   ([`read RDI s`; `read RSI s`; `rho:byte list`; `k:num`] @ post) 43 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_GHOST_TAC "AM" 12288 2304 "s43" THEN
  EN3_MATRIX_TAC `s43:x86state` THEN

  (*** The noise: y from a call with a null fourth output, then e1 and e2 ***)

  X86_STEPS_TAC EN3_EXEC (44--54) THEN INDCPA_NORM_TAC THEN
  call (INDCPA_GETNOISE_NULL
    MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT)
   ([`read RDI s`; `read RSI s`; `read RDX s`; `read R8 s`; `r:byte list`;
     `read R9 s`; `word 1:int64`; `word 2:int64`; `word 255:int64`] @
    post) 55 THEN
  INDCPA_NORM_TAC THEN INDCPA_NOISE_TAC "YS" 6144 3 "r" "word j" "s55" THEN
  INDCPA_DISCARD_LETS_TAC THEN INDCPA_NONZERO_TAC 17000 4864 THEN
  X86_STEPS_TAC EN3_EXEC (56--69) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
     `r:byte list`; `read R9 s`; `word 4:int64`; `word 5:int64`;
     `word 6:int64`] @ post) 70 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_NOISE_TAC "E1" 9216 3 "r" "word(3 + j)" "s70" THEN
  INDCPA_NOISE1_TAC "E2" 4864 "r" "word 6" "s70" THEN
  INDCPA_DISCARD_LETS_TAC THEN

  (*** The NTT of the noise and its multiplication cache ***)

  X86_STEPS_TAC EN3_EXEC (71--73) THEN
  call MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `YS:num->int16`] @ post) 74 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_NTT_TAC "YH" 6144 3 "YS" "r" "word j" "s74" THEN
  X86_STEPS_TAC EN3_EXEC (75--77) THEN
  call
   MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `YH:num->int16`] @ post) 78 THEN
  INDCPA_NORM_TAC THEN INDCPA_MULCACHE_TAC "MC" 5376 3 "YH" "s78" THEN

  (*** The products with the transposed matrix, in a loop, and with t ***)

  X86_STEPS_TAC EN3_EXEC (79--82) THEN
  MAP_EVERY (fun q ->
    let a = (12288 + 1536 * q,"AM",768 * q)
    and y = (6144,"YH") and t = (5376,"MC") in
    X86_STEPS_TAC EN3_EXEC ((83 + 10 * q)--(89 + 10 * q)) THEN
    INDCPA_NORM_TAC THEN
    INDCPA_BASEMULK_PRE_TAC 3 a y t ("s"^string_of_int(89 + 10 * q)) THEN
    call MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
     (INDCPA_BASEMULK_ARGS 3 ("AM",768 * q) "YH" "MC") (90 + 10 * q)
    THEN INDCPA_BASEMULK_DROP_PRE_TAC 3 a y t THEN INDCPA_NORM_TAC THEN
    X86_STEPS_TAC EN3_EXEC [91 + 10 * q] THEN INDCPA_PTR_TAC THEN
    X86_STEPS_TAC EN3_EXEC [92 + 10 * q])
   (0--2) THEN
  EN3_AM_BOUND_TAC THEN EN3_U0_TAC THEN
  X86_STEPS_TAC EN3_EXEC (113--119) THEN INDCPA_NORM_TAC THEN
  INDCPA_BASEMULK_PRE_TAC 3 (7680,"TT",0) (6144,"YH") (5376,"MC") "s119" THEN
  call MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   (INDCPA_BASEMULK_ARGS 3 ("TT",0) "YH" "MC") 120 THEN
  INDCPA_BASEMULK_DROP_PRE_TAC 3 (7680,"TT",0) (6144,"YH") (5376,"MC") THEN
  INDCPA_NORM_TAC THEN EN3_TT_BOUND_TAC THEN EN3_V0_TAC THEN

  (*** The inverse NTTs, adding the noise and the message, reductions ***)

  X86_STEPS_TAC EN3_EXEC (121--122) THEN
  call MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `U0:num->int16`] @ post) 123 THEN
  INDCPA_NORM_TAC THEN INDCPA_INVNTT_TAC "U1" 10752 3 "U0" "s123" THEN
  X86_STEPS_TAC EN3_EXEC (124--125) THEN
  call MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `V0:num->int16`] @ post) 126 THEN
  INDCPA_NORM_TAC THEN INDCPA_INVNTT1_TAC "V1" 3840 "V0" "s126" THEN
  X86_STEPS_TAC EN3_EXEC (127--129) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `U1:num->int16`; `E1:num->int16`] @ post)
   130 THEN
  X86_STEPS_TAC EN3_EXEC (131--133) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `V1:num->int16`; `E2:num->int16`] @ post)
   134 THEN
  X86_STEPS_TAC EN3_EXEC (135--137) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`;
     `\i. word_add ((V1:num->int16) i) ((E2:num->int16) i)`;
     `MU:num->int16`] @ post) 138 THEN
  X86_STEPS_TAC EN3_EXEC (139--140) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLYVEC_REDUCE_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `\i. word_add ((U1:num->int16) i) ((E1:num->int16) i)`] @
    post) 141 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_REDUCE_TAC "U3" 10752 768
    "word_add ((U1:num->int16) i) ((E1:num->int16) i)" "s141" THEN
  X86_STEPS_TAC EN3_EXEC (142--143) THEN
  call MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`;
     `\i. word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                   ((MU:num->int16) i)`] @ post) 144 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_REDUCE_TAC "V4" 3840 256
    "word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i)) \
     ((MU:num->int16) i)" "s144" THEN

  (*** The compression and encoding of u and v ***)

  X86_STEPS_TAC EN3_EXEC (145--148) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `U3:num->int16`] @ post) 149 THEN
  EN3_COMPRESS_POST_TAC "U3"
   `ival(word_add ((U1:num->int16) i) ((E1:num->int16) i))` THEN
  X86_STEPS_TAC EN3_EXEC (150--154) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `V4:num->int16`] @ post) 155 THEN
  EN3_COMPRESS_POST_TAC "V4"
   `ival(word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i))` THEN

  (*** Zeroing the buffers and the seed, the return ***)

  X86_STEPS_TAC EN3_EXEC (156--203) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN EN3_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!c m pk coins (ek:byte list) (msg:byte list) (r:byte list) pc
    stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    LENGTH ek = 1184 /\ LENGTH msg = 32 /\ LENGTH r = 32 /\
    (!i j. i < 3 /\ j < 3
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 1152 32 ek) [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 16992),17000) /\
    nonoverlapping (c,1088) (word_sub stackpointer (word 16992),17000) /\
    ALLPAIRS nonoverlapping
     [(c,1088); (word_sub stackpointer (word 16992),17000)]
     [(m,32); (pk,1184); (coins,32); (word pc,libmlkem_size)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + mlkem768_indcpa_enc) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [c; m; pk; coins] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(m,32)) s = num_of_bytelist msg /\
              read (memory :> bytes(pk,1184)) s = num_of_bytelist ek /\
              read (memory :> bytes(coins,32)) s = num_of_bytelist r)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              read (memory :> bytes(c,1088)) s =
              num_of_bytelist(kpke_encrypt mlkem768 ek msg r) /\
              C_RETURN s = word 0)
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(c,1088);
            memory :> bytes(word_sub stackpointer (word 16992),16992)])`;;

let MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend only on the      *)
(* addresses and on rho, the last 32 bytes of the public key, through the    *)
(* samples of SampleNTT for the transposed matrix, but not on the message or *)
(* the randomness. At the end the frame variables are expanded in them by    *)
(* INDCPA_UNBOT_TAC, since they are not arguments of f_events. The empty     *)
(* regions of the null fourth output of the first call of                    *)
(* mlkem768_poly_getnoise_eta1_4x are removed from the memory accesses by    *)
(* MEMACCESS_DROP_ZERO_TAC.                                                  *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let EN3_SAFE_ALLOWED =
  [`pc:num`; `c:int64`; `m:int64`; `pk:int64`; `coins:int64`;
   `stackpointer:int64`; `returnaddress:int64`; `rho:byte list`;
   `bot:int64`];;

let EN3_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,EN3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      (`e:(uarch_event)list`::ilist @
       [`pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`])
      n THENL
     [EXISTS_E2_TAC (ref EN3_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let EN3_SAFE_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (INDCPA_GEN_MATRIX_SAFE_SPEC
     MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE `word 1:int64`)
   "H_GM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (INDCPA_GETNOISE_NULL_SAFE
     MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE)
   "H_GETNOISE3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC
   MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE
   "H_GETNOISE" THEN
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [MLKEM_NATIVE_POLYVEC_FROMBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_FROMBYTES";
    MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_FROMMSG";
    MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_NTT";
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_MULCACHE";
    MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_BASEMUL";
    MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_INVNTT";
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_POLY_INVNTT";
    MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_ADD";
    MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_POLY_ADD";
    MLKEM_NATIVE_POLYVEC_REDUCE_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_REDUCE";
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_POLY_REDUCE";
    MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_COMPRESS_DU";
    MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_COMPRESS_DV"] THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `c:int64`; `m:int64`; `pk:int64`; `coins:int64`;
    `ek:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 16992 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
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

let EN3_SAFE_MAIN_TAC =
  let call = EN3_SAFE_CALL_TAC in
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  EN3_PK_TAC THEN
  X86_STEPS_TAC EN3_EXEC (1--2) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC EN3_EXEC (3--22) THEN INDCPA_NORM_TAC THEN
  call "H_FROMBYTES" [`read RDI s`; `read RSI s`] 23 THEN INDCPA_NORM_TAC THEN
  INDCPA_YMM_TAC "s23" THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC EN3_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (24--34) THEN INDCPA_NORM_TAC THEN
  call "H_FROMMSG" [`read RDI s`; `read RSI s`] 35 THEN INDCPA_NORM_TAC THEN
  EN3_SEED_TAC "s35" THEN
  X86_STEPS_TAC EN3_EXEC (36--42) THEN INDCPA_NORM_TAC THEN
  call "H_GM" [`read RDI s`; `read RSI s`; `rho:byte list`; `k:num`] 43 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN3_EXEC (44--54) THEN INDCPA_NORM_TAC THEN
  call "H_GETNOISE3"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read R8 s`] 55 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_NONZERO_TAC 17000 4864 THEN
  X86_STEPS_TAC EN3_EXEC (56--69) THEN INDCPA_NORM_TAC THEN
  call "H_GETNOISE"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`] 70
  THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN3_EXEC (71--73) THEN
  call "H_NTT" [`read RDI s`] 74 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN3_EXEC (75--77) THEN
  call "H_MULCACHE" [`read RDI s`; `read RSI s`] 78 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN3_EXEC (79--82) THEN
  MAP_EVERY (fun q ->
    X86_STEPS_TAC EN3_EXEC ((83 + 10 * q)--(89 + 10 * q)) THEN
    INDCPA_NORM_TAC THEN
    call "H_BASEMUL"
     [`read RSI s`; `read RDX s`; `read RCX s`; `read RDI s`]
     (90 + 10 * q) THEN INDCPA_NORM_TAC THEN
    X86_STEPS_TAC EN3_EXEC [91 + 10 * q] THEN INDCPA_PTR_TAC THEN
    X86_STEPS_TAC EN3_EXEC [92 + 10 * q])
   (0--2) THEN
  X86_STEPS_TAC EN3_EXEC (113--119) THEN INDCPA_NORM_TAC THEN
  call "H_BASEMUL"
   [`read RSI s`; `read RDX s`; `read RCX s`; `read RDI s`] 120 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN3_EXEC (121--122) THEN
  call "H_INVNTT" [`read RDI s`] 123 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN3_EXEC (124--125) THEN
  call "H_POLY_INVNTT" [`read RDI s`] 126 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN3_EXEC (127--129) THEN INDCPA_NORM_TAC THEN
  call "H_ADD" [`read RDI s`; `read RSI s`] 130 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN3_EXEC (131--133) THEN INDCPA_NORM_TAC THEN
  call "H_POLY_ADD" [`read RDI s`; `read RSI s`] 134 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN3_EXEC (135--137) THEN INDCPA_NORM_TAC THEN
  call "H_POLY_ADD" [`read RDI s`; `read RSI s`] 138 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN3_EXEC (139--140) THEN INDCPA_NORM_TAC THEN
  call "H_REDUCE" [`read RDI s`] 141 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN3_EXEC (142--143) THEN
  call "H_POLY_REDUCE" [`read RDI s`] 144 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN3_EXEC (145--148) THEN INDCPA_NORM_TAC THEN
  call "H_COMPRESS_DU" [`read RDI s`; `read RSI s`] 149 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN3_EXEC (150--154) THEN INDCPA_NORM_TAC THEN
  call "H_COMPRESS_DV" [`read RDI s`; `read RSI s`] 155 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN3_EXEC (156--203) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  INDCPA_UNBOT_TAC THEN MEMACCESS_DROP_ZERO_TAC THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
   forall e c m pk coins (ek:byte list) pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH ek = 1184 /\
    (!i j. i < 3 /\ j < 3
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 1152 32 ek) [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 16992),17000) /\
    nonoverlapping (c,1088) (word_sub stackpointer (word 16992),17000) /\
    ALLPAIRS nonoverlapping
     [(c,1088); (word_sub stackpointer (word 16992),17000)]
     [(m,32); (pk,1184); (coins,32); (word pc,libmlkem_size)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + mlkem768_indcpa_enc) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [c; m; pk; coins] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(pk,1184)) s = num_of_bytelist ek /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              C_RETURN s = word 0 /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events c m pk coins pc
                        (word_sub stackpointer (word 16992)) returnaddress
                        (mlkem_slice 1152 32 ek) /\
                 memaccess_inbounds e2
                  [m,32; pk,1184; coins,32; c,1088;
                   word_sub stackpointer (word 16992),17000;
                   word(pc + mlkem_poly_compress_d4_const1),8; word(pc + mlkem_poly_compress_d4_const2),8;
                   word(pc + mlkem_poly_invntt_tomont_consts),48; word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                   word(pc + mlkem768_gen_matrix_consts),4; word(pc + rodata_mlk_zetas),256]
                  [c,1088; word_sub stackpointer (word 16992),16992]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(c,1088);
            memory :> bytes(word_sub stackpointer (word 16992),16992)])`;;

let MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
