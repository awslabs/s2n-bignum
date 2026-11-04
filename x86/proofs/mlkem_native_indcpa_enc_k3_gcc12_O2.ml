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
(* (the last 32 bytes of the key), samples y (with eta = 2), e1 and e2 (with *)
(* eta = 2) from the randomness r, and computes u = NTT^-1(A^T NTT(y)) + e1  *)
(* and v = NTT^-1(t^T NTT(y)) + e2 + mu, where mu is m decompressed. It      *)
(* writes the compressions of u and v as the ciphertext, zeroing its         *)
(* buffers. It is verified in the whole image (see                           *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x68d0, using  *)
(* the theorems for mlkem768_polyvec_frombytes, mlkem_poly_frommsg,          *)
(* mlkem768_gen_matrix, mlkem768_poly_getnoise_eta1_4x,                      *)
(* mlkem768_polyvec_ntt, mlkem768_polyvec_mulcache_compute,                  *)
(* mlkem768_polyvec_basemul_acc_montgomery_cached,                           *)
(* mlkem768_polyvec_invntt_tomont, mlkem_poly_invntt_tomont,                 *)
(* mlkem768_polyvec_add, mlkem_poly_add, mlkem768_polyvec_reduce,            *)
(* mlkem_poly_reduce, mlkem768_polyvec_compress_du and                       *)
(* mlkem_poly_compress_d4 in the image.                                      *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_polyvec_frombytes_k3_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_poly_frommsg_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_gen_matrix_k3_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_poly_getnoise_eta1_4x_k3_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_ntt_k3_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_mulcache_compute_k3_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_basemul_k3_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_invntt_tomont_k3_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_poly_invntt_tomont_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_add_k3_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_poly_add_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_reduce_k3_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_poly_reduce_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_compress_du_k3_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_poly_compress_d4_gcc12_O2.ml";;
needs "x86/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image:

    68d0: lea    r10,[rsp+0x8]
    68d5: and    rsp,0xffffffffffffffe0
    68d9: push   QWORD PTR [r10-0x8]
    68dd: push   rbp
    68de: mov    rbp,rsp
    68e1: push   r15
    68e3: push   r14
    68e5: lea    rax,[rbp-0x2430]
    68ec: lea    r14,[rbp-0x2d30]
    68f3: push   r13
    68f5: mov    r13,rdx
    68f8: push   r12
    68fa: mov    r12,rcx
    68fd: push   r10
    68ff: push   rbx
    6900: mov    rbx,rsi
    6903: mov    rsi,rdx
    6906: sub    rsp,0x3360
    690d: mov    QWORD PTR [rbp-0x3380],rdi
    6914: mov    rdi,rax
    6917: mov    QWORD PTR [rbp-0x3370],rax
    691e: call   7530 <mlkem768_polyvec_frombytes>
    6923: lea    rax,[rbp-0x3130]
    692a: mov    rsi,rbx
    692d: movdqu xmm1,XMMWORD PTR [r13+0x480]
    6936: movdqu xmm2,XMMWORD PTR [r13+0x490]
    693f: mov    rdi,rax
    6942: mov    QWORD PTR [rbp-0x3378],rax
    6949: lea    rbx,[rbp-0x2a30]
    6950: movaps XMMWORD PTR [rbp-0x3350],xmm1
    6957: lea    r13,[rbp-0x1830]
    695e: movaps XMMWORD PTR [rbp-0x3340],xmm2
    6965: call   3210 <mlkem_poly_frommsg>
    696a: lea    rax,[rbp-0x1230]
    6971: mov    edx,0x1
    6976: lea    rsi,[rbp-0x3350]
    697d: mov    rdi,rax
    6980: mov    QWORD PTR [rbp-0x3360],rax
    6987: mov    QWORD PTR [rbp-0x3388],rsi
    698e: call   64b0 <mlkem768_gen_matrix>
    6993: sub    rsp,0x8
    6997: mov    r8,r12
    699a: xor    r9d,r9d
    699d: push   0xff
    69a2: lea    rdx,[rbp-0x2630]
    69a9: xor    ecx,ecx
    69ab: mov    rdi,rbx
    69ae: push   0x2
    69b0: lea    rsi,[rbp-0x2830]
    69b7: push   0x1
    69b9: call   7790 <mlkem768_poly_getnoise_eta1_4x>
    69be: lea    rax,[rbp-0x1e30]
    69c5: add    rsp,0x18
    69c9: mov    r8,r12
    69cc: lea    rcx,[rbp-0x2f30]
    69d3: mov    rdi,rax
    69d6: mov    QWORD PTR [rbp-0x3368],rax
    69dd: lea    rdx,[rbp-0x1a30]
    69e4: mov    QWORD PTR [rbp-0x3358],rcx
    69eb: lea    rsi,[rbp-0x1c30]
    69f2: mov    r9d,0x3
    69f8: push   0x6
    69fa: push   0x5
    69fc: push   0x4
    69fe: call   7790 <mlkem768_poly_getnoise_eta1_4x>
    6a03: add    rsp,0x20
    6a07: mov    rdi,rbx
    6a0a: call   7570 <mlkem768_polyvec_ntt>
    6a0f: mov    rsi,rbx
    6a12: mov    rdi,r14
    6a15: call   76b0 <mlkem768_polyvec_mulcache_compute>
    6a1a: mov    QWORD PTR [rbp-0x3390],r13
    6a21: lea    rax,[rbp-0x30]
    6a25: mov    r12,QWORD PTR [rbp-0x3360]
    6a2c: mov    r15,rax
    6a2f: mov    rsi,r12
    6a32: mov    rdi,r13
    6a35: mov    rcx,r14
    6a38: mov    rdx,rbx
    6a3b: add    r12,0x600
    6a42: add    r13,0x200
    6a49: call   75d0 <mlkem768_polyvec_basemul_acc_montgomery_cached>
    6a4e: cmp    r12,r15
    6a51: jne    6a2f <mlkem768_indcpa_enc+0x15f>
    6a53: lea    r12,[rbp-0x3330]
    6a5a: mov    r13,QWORD PTR [rbp-0x3390]
    6a61: mov    rcx,r14
    6a64: mov    rdx,rbx
    6a67: mov    rsi,QWORD PTR [rbp-0x3370]
    6a6e: mov    rdi,r12
    6a71: call   75d0 <mlkem768_polyvec_basemul_acc_montgomery_cached>
    6a76: mov    rdi,r13
    6a79: call   75a0 <mlkem768_polyvec_invntt_tomont>
    6a7e: mov    rdi,r12
    6a81: call   5860 <mlkem_poly_invntt_tomont>
    6a86: mov    rsi,QWORD PTR [rbp-0x3368]
    6a8d: mov    rdi,r13
    6a90: call   7720 <mlkem768_polyvec_add>
    6a95: mov    rsi,QWORD PTR [rbp-0x3358]
    6a9c: mov    rdi,r12
    6a9f: call   56b0 <mlkem_poly_add>
    6aa4: mov    rsi,QWORD PTR [rbp-0x3378]
    6aab: mov    rdi,r12
    6aae: call   56b0 <mlkem_poly_add>
    6ab3: mov    rdi,r13
    6ab6: call   76f0 <mlkem768_polyvec_reduce>
    6abb: mov    rdi,r12
    6abe: call   5660 <mlkem_poly_reduce>
    6ac3: mov    r15,QWORD PTR [rbp-0x3380]
    6aca: mov    rsi,r13
    6acd: mov    rdi,r15
    6ad0: call   7470 <mlkem768_polyvec_compress_du>
    6ad5: mov    rax,r15
    6ad8: mov    rsi,r12
    6adb: add    rax,0x3c0
    6ae1: mov    rdi,rax
    6ae4: call   2460 <mlkem_poly_compress_d4>
    6ae9: xor    eax,eax
    6aeb: mov    rdi,r14
    6aee: mov    ecx,0x60
    6af3: rep    stos QWORD PTR es:[rdi],rax
    6af6: mov    rdi,QWORD PTR [rbp-0x3358]
    6afd: mov    ecx,0x40
    6b02: mov    rdx,QWORD PTR [rbp-0x3358]
    6b09: rep    stos QWORD PTR es:[rdi],rax
    6b0c: mov    rdi,QWORD PTR [rbp-0x3378]
    6b13: mov    ecx,0x40
    6b18: mov    rdx,QWORD PTR [rbp-0x3378]
    6b1f: rep    stos QWORD PTR es:[rdi],rax
    6b22: mov    ecx,0x40
    6b27: mov    rdi,r12
    6b2a: rep    stos QWORD PTR es:[rdi],rax
    6b2d: mov    ecx,0xc0
    6b32: mov    rdi,r13
    6b35: rep    stos QWORD PTR es:[rdi],rax
    6b38: mov    rdi,QWORD PTR [rbp-0x3368]
    6b3f: mov    ecx,0xc0
    6b44: mov    rdx,QWORD PTR [rbp-0x3368]
    6b4b: rep    stos QWORD PTR es:[rdi],rax
    6b4e: mov    rdi,QWORD PTR [rbp-0x3370]
    6b55: mov    ecx,0xc0
    6b5a: rep    stos QWORD PTR es:[rdi],rax
    6b5d: mov    rdi,QWORD PTR [rbp-0x3370]
    6b64: mov    ecx,0xc0
    6b69: mov    rdi,rbx
    6b6c: rep    stos QWORD PTR es:[rdi],rax
    6b6f: mov    rdi,QWORD PTR [rbp-0x3360]
    6b76: mov    ecx,0x240
    6b7b: rep    stos QWORD PTR es:[rdi],rax
    6b7e: mov    rdi,QWORD PTR [rbp-0x3360]
    6b85: pxor   xmm0,xmm0
    6b89: mov    rax,QWORD PTR [rbp-0x3388]
    6b90: movaps XMMWORD PTR [rbp-0x3350],xmm0
    6b97: movaps XMMWORD PTR [rbp-0x3340],xmm0
    6b9e: lea    rsp,[rbp-0x30]
    6ba2: xor    eax,eax
    6ba4: pop    rbx
    6ba5: pop    r10
    6ba7: pop    r12
    6ba9: pop    r13
    6bab: pop    r14
    6bad: pop    r15
    6baf: pop    rbp
    6bb0: lea    rsp,[r10-0x8]
    6bb4: ret
 ***)

let MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x68d0,0x6bb5];;

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
(* mlkem768 ek msg r in common/fips203.ml, for any ek (FIPS 203 decodes t    *)
(* modulo q, while the code multiplies by the 12-bit fields, which are       *)
(* congruent). The theorem assumes that SampleNTT terminates for each entry  *)
(* of the matrix, as for mlkem768_gen_matrix, and that the stack does not    *)
(* contain address 0. The stack is the 16992 bytes below the return address, *)
(* for up to 31 bytes for the alignment, the 13216 bytes of the pushes and   *)
(* the buffers and the 3744 used by the callees below them. The matrix is    *)
(* generated with transposition, so the theorem for mlkem768_gen_matrix is   *)
(* specialized to that case. The fourth output of the first call of          *)
(* mlkem768_poly_getnoise_eta1_4x is a null pointer (its fourth nonce is     *)
(* 255), so the theorem is specialized to that case; in the second call, the *)
(* fourth output is e2, which is not null since the stack does not contain   *)
(* address 0. The products with the rows of the matrix are computed in a     *)
(* loop, which the simulation unrolls, the comparisons of the pointers in    *)
(* the frame deciding its branch (INDCPA_PTR_TAC).                           *)
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
    `word pc:int64,0x82a0`; `word_add stackpointer (word 16992):int64,8`] THEN
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

let MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = time prove
 (`!c m pk coins (ek:byte list) (msg:byte list) (r:byte list) pc
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
     [(m,32); (pk,1184); (coins,32); (word pc,0x82a0)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x68d0) /\
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
            memory :> bytes(word_sub stackpointer (word 16992),16992)])`,
  EN3_INTRO_TAC THEN EN3_SETUP_TAC THEN EN3_MAIN_TAC);;

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

let MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
   forall e c m pk coins (ek:byte list) pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH ek = 1184 /\
    (!i j. i < 3 /\ j < 3
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 1152 32 ek) [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 16992),17000) /\
    nonoverlapping (c,1088) (word_sub stackpointer (word 16992),17000) /\
    ALLPAIRS nonoverlapping
     [(c,1088); (word_sub stackpointer (word 16992),17000)]
     [(m,32); (pk,1184); (coins,32); (word pc,0x82a0)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x68d0) /\
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
                   word(pc + 0x8000),8; word(pc + 0x8008),8;
                   word(pc + 0x8080),48; word(pc + 0x80c0),192;
                   word(pc + 0x8180),4; word(pc + 0x81a0),256]
                  [c,1088; word_sub stackpointer (word 16992),16992]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(c,1088);
            memory :> bytes(word_sub stackpointer (word 16992),16992)])`,
  EN3_SAFE_INTRO_TAC THEN EN3_SETUP_TAC THEN EN3_SAFE_MAIN_TAC);;
