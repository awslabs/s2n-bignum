(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The encryption of K-PKE for ML-KEM-512 (FIPS 203 Algorithm 14). This is   *)
(* the code for mlkem512_indcpa_enc from mlkem-native's portable C           *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* It decodes the vector t in the NTT domain from the encryption key and the *)
(* message m from its 32 bytes, generates the transposed matrix from rho     *)
(* (the last 32 bytes of the key), samples y (with eta = 3), e1 and e2       *)
(* (with eta = 2) from the randomness r, and computes u = NTT^-1(A^T         *)
(* NTT(y)) + e1 and v = NTT^-1(t^T NTT(y)) + e2 + mu, where mu is m          *)
(* decompressed. It writes the compressions of u and v as the ciphertext,    *)
(* zeroing its buffers. It is verified in the whole image (see libmlkem.ml), *)
(* using the theorems for mlkem512_polyvec_frombytes, mlkem_poly_frommsg,    *)
(* mlkem512_gen_matrix, mlkem512_poly_getnoise_eta1122_4x,                   *)
(* mlkem512_poly_getnoise_eta2, mlkem512_polyvec_ntt,                        *)
(* mlkem512_polyvec_mulcache_compute,                                        *)
(* mlkem512_polyvec_basemul_acc_montgomery_cached,                           *)
(* mlkem512_polyvec_invntt_tomont, mlkem_poly_invntt_tomont,                 *)
(* mlkem512_polyvec_add, mlkem_poly_add, mlkem512_polyvec_reduce,            *)
(* mlkem_poly_reduce, mlkem512_polyvec_compress_du and                       *)
(* mlkem_poly_compress_d4 in the image.                                      *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/gcc12_O2/polyvec_frombytes_k2.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_frommsg.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/gen_matrix_k2.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_getnoise_eta1122_4x_k2.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_getnoise_eta2_k2.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/polyvec_ntt_k2.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/polyvec_mulcache_compute_k2.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/basemul_k2.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/polyvec_invntt_tomont_k2.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_invntt_tomont.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/polyvec_add_k2.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_add.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/polyvec_reduce_k2.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_reduce.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/polyvec_compress_du_k2.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_compress_d4.ml";;
needs "x86/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image:

    mlkem512_indcpa_enc:
       +0x0: lea    r10,[rsp+0x8]
       +0x5: and    rsp,0xffffffffffffffe0
       +0x9: push   QWORD PTR [r10-0x8]
       +0xd: push   rbp
       +0xe: mov    rbp,rsp
      +0x11: push   r15
      +0x13: push   r14
      +0x15: lea    r15,[rbp-0x1430]
      +0x1c: lea    r14,[rbp-0x1a30]
      +0x23: push   r13
      +0x25: mov    r13,rdx
      +0x28: push   r12
      +0x2a: mov    r12,rcx
      +0x2d: push   r10
      +0x2f: push   rbx
      +0x30: mov    rbx,rsi
      +0x33: mov    rsi,rdx
      +0x36: sub    rsp,0x2060
      +0x3d: mov    QWORD PTR [rbp-0x2068],rdi
      +0x44: mov    rdi,r15
      +0x47: call   <mlkem512_polyvec_frombytes>
      +0x4c: lea    r11,[rbp-0x1e30]
      +0x53: mov    rsi,rbx
      +0x56: movdqu xmm1,XMMWORD PTR [r13+0x300]
      +0x5f: movdqu xmm2,XMMWORD PTR [r13+0x310]
      +0x68: mov    rdi,r11
      +0x6b: mov    QWORD PTR [rbp-0x2088],r11
      +0x72: lea    rbx,[rbp-0x1830]
      +0x79: movaps XMMWORD PTR [rbp-0x2050],xmm1
      +0x80: lea    r13,[rbp-0xc30]
      +0x87: movaps XMMWORD PTR [rbp-0x2040],xmm2
      +0x8e: call   <mlkem_poly_frommsg>
      +0x93: lea    rax,[rbp-0x830]
      +0x9a: mov    edx,0x1
      +0x9f: lea    r10,[rbp-0x2050]
      +0xa6: mov    rsi,r10
      +0xa9: mov    rdi,rax
      +0xac: mov    QWORD PTR [rbp-0x2058],rax
      +0xb3: mov    QWORD PTR [rbp-0x2080],r10
      +0xba: call   <mlkem512_gen_matrix>
      +0xbf: sub    rsp,0x8
      +0xc3: xor    r9d,r9d
      +0xc6: mov    r8,r12
      +0xc9: push   0x3
      +0xcb: lea    rcx,[rbp-0xe30]
      +0xd2: mov    rdi,rbx
      +0xd5: lea    rdx,[rbp-0x1030]
      +0xdc: push   0x2
      +0xde: lea    rsi,[rbp-0x1630]
      +0xe5: push   0x1
      +0xe7: mov    QWORD PTR [rbp-0x2060],rdx
      +0xee: call   <mlkem512_poly_getnoise_eta1122_4x>
      +0xf3: lea    r8,[rbp-0x1c30]
      +0xfa: add    rsp,0x20
      +0xfe: mov    rsi,r12
     +0x101: mov    rdi,r8
     +0x104: mov    edx,0x4
     +0x109: mov    QWORD PTR [rbp-0x2070],r8
     +0x110: lea    r12,[rbp-0x2030]
     +0x117: call   <mlkem512_poly_getnoise_eta2>
     +0x11c: mov    rdi,rbx
     +0x11f: call   <mlkem512_polyvec_ntt>
     +0x124: mov    rsi,rbx
     +0x127: mov    rdi,r14
     +0x12a: call   <mlkem512_polyvec_mulcache_compute>
     +0x12f: mov    rcx,r14
     +0x132: mov    rdx,rbx
     +0x135: mov    rdi,r13
     +0x138: mov    rsi,QWORD PTR [rbp-0x2058]
     +0x13f: call   <mlkem512_polyvec_basemul_acc_montgomery_cached>
     +0x144: lea    rsi,[rbp-0x430]
     +0x14b: mov    rcx,r14
     +0x14e: mov    rdx,rbx
     +0x151: lea    rdi,[rbp-0xa30]
     +0x158: call   <mlkem512_polyvec_basemul_acc_montgomery_cached>
     +0x15d: mov    rcx,r14
     +0x160: mov    rdx,rbx
     +0x163: mov    rsi,r15
     +0x166: mov    rdi,r12
     +0x169: call   <mlkem512_polyvec_basemul_acc_montgomery_cached>
     +0x16e: mov    rdi,r13
     +0x171: call   <mlkem512_polyvec_invntt_tomont>
     +0x176: mov    rdi,r12
     +0x179: call   <mlkem_poly_invntt_tomont>
     +0x17e: mov    rsi,QWORD PTR [rbp-0x2060]
     +0x185: mov    rdi,r13
     +0x188: call   <mlkem512_polyvec_add>
     +0x18d: mov    r8,QWORD PTR [rbp-0x2070]
     +0x194: mov    rdi,r12
     +0x197: mov    rsi,r8
     +0x19a: mov    QWORD PTR [rbp-0x2078],r8
     +0x1a1: call   <mlkem_poly_add>
     +0x1a6: mov    r11,QWORD PTR [rbp-0x2088]
     +0x1ad: mov    rdi,r12
     +0x1b0: mov    rsi,r11
     +0x1b3: mov    QWORD PTR [rbp-0x2070],r11
     +0x1ba: call   <mlkem_poly_add>
     +0x1bf: mov    rdi,r13
     +0x1c2: call   <mlkem512_polyvec_reduce>
     +0x1c7: mov    rdi,r12
     +0x1ca: call   <mlkem_poly_reduce>
     +0x1cf: mov    rdi,QWORD PTR [rbp-0x2068]
     +0x1d6: mov    rsi,r13
     +0x1d9: call   <mlkem512_polyvec_compress_du>
     +0x1de: mov    rdi,QWORD PTR [rbp-0x2068]
     +0x1e5: mov    rsi,r12
     +0x1e8: add    rdi,0x280
     +0x1ef: call   <mlkem_poly_compress_d4>
     +0x1f4: xor    eax,eax
     +0x1f6: mov    rdi,r14
     +0x1f9: mov    ecx,0x40
     +0x1fe: rep    stos QWORD PTR es:[rdi],rax
     +0x201: mov    r8,QWORD PTR [rbp-0x2078]
     +0x208: mov    ecx,0x40
     +0x20d: mov    rdi,r8
     +0x210: rep    stos QWORD PTR es:[rdi],rax
     +0x213: mov    r11,QWORD PTR [rbp-0x2070]
     +0x21a: mov    ecx,0x40
     +0x21f: mov    rdi,r11
     +0x222: rep    stos QWORD PTR es:[rdi],rax
     +0x225: mov    ecx,0x40
     +0x22a: mov    rdi,r12
     +0x22d: rep    stos QWORD PTR es:[rdi],rax
     +0x230: mov    ecx,0x80
     +0x235: mov    rdi,r13
     +0x238: rep    stos QWORD PTR es:[rdi],rax
     +0x23b: mov    rdi,QWORD PTR [rbp-0x2060]
     +0x242: mov    ecx,0x80
     +0x247: mov    rdx,QWORD PTR [rbp-0x2060]
     +0x24e: rep    stos QWORD PTR es:[rdi],rax
     +0x251: mov    ecx,0x80
     +0x256: mov    rdi,r15
     +0x259: rep    stos QWORD PTR es:[rdi],rax
     +0x25c: mov    ecx,0x80
     +0x261: mov    rdi,rbx
     +0x264: rep    stos QWORD PTR es:[rdi],rax
     +0x267: mov    rdi,QWORD PTR [rbp-0x2058]
     +0x26e: mov    ecx,0x100
     +0x273: rep    stos QWORD PTR es:[rdi],rax
     +0x276: mov    rdi,QWORD PTR [rbp-0x2058]
     +0x27d: pxor   xmm0,xmm0
     +0x281: mov    r10,QWORD PTR [rbp-0x2080]
     +0x288: movaps XMMWORD PTR [rbp-0x2050],xmm0
     +0x28f: movaps XMMWORD PTR [rbp-0x2040],xmm0
     +0x296: lea    rsp,[rbp-0x30]
     +0x29a: pop    rbx
     +0x29b: pop    r10
     +0x29d: pop    r12
     +0x29f: pop    r13
     +0x2a1: pop    r14
     +0x2a3: pop    r15
     +0x2a5: pop    rbp
     +0x2a6: lea    rsp,[r10-0x8]
     +0x2aa: ret
 ***)

let MLKEM_NATIVE_INDCPA_ENC_K2_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem512_indcpa_enc"];;

let EN2_EXEC = MLKEM_NATIVE_INDCPA_ENC_K2_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The encryption in FIPS 203 in terms of the values computed by the code:   *)
(* the 12-bit fields of the encryption key as decoded (which may be >= q),   *)
(* the NTT of y and its multiplication cache, the noise e1 and e2, the       *)
(* decompressed message, the products with the transposed matrix and with t  *)
(* in Montgomery form, their inverse NTTs, and the results after adding the  *)
(* noise and the message and reducing, whose compressions are encoded in the *)
(* ciphertext. This is as for AArch64.                                       *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_K2_RESULT = prove
 (`!ek m r (TT:num->int16) (YH:num->int16) (MC:num->int16) (E1:num->int16)
    (E2:num->int16) (MU:num->int16) (U0:num->int16) (V0:num->int16)
    (U1:num->int16) (V1:num->int16) (U3:num->int16) (V4:num->int16).
     (!i j n. i < 2 /\ j < 2 /\ n < 256
              ==> mlkem_sample_ntt
                   (APPEND (mlkem_slice 768 32 ek) [word j; word i]) n
                  < &3329) /\
     (!i. i < 512
          ==> TT i = word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(YH(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 r (word j))) i)
                (mod &3329) /\
                abs(ival(YH(256 * j + i))) <= &23594) /\
     (!j p. j < 2 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(YH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(E1(256 * j + i)) ==
                 coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word(2 + j)))))
                (mod &3329) /\
                abs(ival(E1(256 * j + i))) <= &2) /\
     (!i. i < 256
          ==> (ival(E2 i) == coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word 4))))
              (mod &3329) /\
              abs(ival(E2 i)) <= &2) /\
     (!i. i < 256
          ==> MU i = word((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1)
                          DIV 2)) /\
     (!q p. q < 2 /\ p < 128
            ==> (ival(U0(256 * q + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(MC(128 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(MC p) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p))))) (mod &3329) /\
                (ival(U0(256 * q + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(YH(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(YH(2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(V0(2 * p)) ==
               &169 *
               ((ival(TT(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p))) +
                (ival(TT(2 * p + 1)) * ival(MC p) +
                 ival(TT(2 * p)) * ival(YH(2 * p))))) (mod &3329) /\
              (ival(V0(2 * p + 1)) ==
               &169 *
               ((ival(TT(256 + 2 * p + 1)) * ival(YH(256 + 2 * p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p + 1))) +
                (ival(TT(2 * p + 1)) * ival(YH(2 * p)) +
                 ival(TT(2 * p)) * ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(U1(256 * j + i)) ==
                 inverse_ntt (\n. ival(U0(256 * j + n))) i) (mod &3329) /\
                abs(ival(U1(256 * j + i))) <= &26624) /\
     (!i. i < 256
          ==> (ival(V1 i) == inverse_ntt (\n. ival(V0 n)) i) (mod &3329) /\
              abs(ival(V1 i)) <= &26624) /\
     (!i. i < 512 ==> ival(U3 i) = ival(word_add (U1 i) (E1 i)) rem &3329) /\
     (!i. i < 256
          ==> ival(V4 i) =
              ival(word_add (word_add (V1 i) (E2 i)) (MU i)) rem &3329)
     ==> nsum {i | i < 512}
              (\i. ((2048 * val(U3 i) + 3329) DIV 6658) MOD 1024 *
                   2 EXP (10 * i)) +
         2 EXP (8 * 640) *
         nsum {i | i < 256}
              (\i. ((32 * val(V4 i) + 3329) DIV 6658) MOD 16 * 2 EXP (4 * i)) =
         num_of_bytelist(kpke_encrypt mlkem512 ek m r)`,
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
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem512] THEN
  MP_TAC(SPECL [`2`; `3`; `2`; `10`; `4`; `ek:byte list`; `m:byte list`;
                `r:byte list`] KPKE_ENCRYPT_FIPS) THEN
  REWRITE_TAC[ARITH_RULE `384 * 2 = 768`] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; MLKEM_ENCODE_LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `256 * 2 = 512`; ARITH_RULE `2 * 2 = 4`;
              ARITH_RULE `(10 * 512) DIV 8 = 640`] THEN
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
   [MP_TAC(SPECL [`256`; `2`; `i:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 2 = 512`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[DIV_MOD_ADD_LT] THEN
    SUBGOAL_THEN
     `!n'. n' < 256
           ==> (ival((U0:num->int16)(256 * j + n')) ==
                &169 * ring_sum mlkem_zq {j' | j' < 2}
                        (\j'. fips203_multiply_ntts
                               (mlkem_sample_ntt
                                 (APPEND (mlkem_slice 768 32 ek)
                                         [word j; word j']))
                               (mlkem_ntt
                                 (mlkem_cbd 3 (mlkem_prf 3 r (word j'))))
                               n')) (mod &3329)`
    ASSUME_TAC THENL
     [parity_tac THENL
       [MP_TAC(SPECL
         [`\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 768 32 ek) [word j; word j'])`;
          `\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 768 32 ek) [word j; word j'])`;
          `\j' n. ival((YH:num->int16)(256 * j' + n))`;
          `\j'. ival((MC:num->int16)(128 * j' + p))`;
          `\j'. mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 r (word j')))`;
          `ival((U0:num->int16)(256 * j + 2 * p))`; `p:num`]
         BASEMUL2_ROW_EVEN);
        MP_TAC(SPECL
         [`\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 768 32 ek) [word j; word j'])`;
          `\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 768 32 ek) [word j; word j'])`;
          `\j' n. ival((YH:num->int16)(256 * j' + n))`;
          `\j'. mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 r (word j')))`;
          `ival((U0:num->int16)(256 * j + 2 * p + 1))`; `p:num`]
         BASEMUL2_ROW_ODD)] THEN
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
              &169 * ring_sum mlkem_zq {j' | j' < 2}
                      (\j'. fips203_multiply_ntts
                             (\n. mlkem_decode 12 ek (256 * j' + n))
                             (mlkem_ntt
                               (mlkem_cbd 3 (mlkem_prf 3 r (word j'))))
                             n')) (mod &3329)`
  ASSUME_TAC THENL
   [parity_tac THEN
    (SUBGOAL_THEN
      `!j' x. j' < 2 /\ x < 256
              ==> (ival((TT:num->int16)(256 * j' + x)) ==
                   mlkem_decode 12 ek (256 * j' + x)) (mod &3329)`
     ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC TT_DECODE_CONG THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `j' < 2` THEN UNDISCH_TAC `x < 256` THEN ARITH_TAC;
       ALL_TAC])
    THENL
     [MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 ek (256 * j' + n)`;
        `\j' n. ival((TT:num->int16)(256 * j' + n))`;
        `\j' n. ival((YH:num->int16)(256 * j' + n))`;
        `\j'. ival((MC:num->int16)(128 * j' + p))`;
        `\j'. mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 r (word j')))`;
        `ival((V0:num->int16)(2 * p))`; `p:num`] BASEMUL2_ROW_EVEN);
      MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 ek (256 * j' + n)`;
        `\j' n. ival((TT:num->int16)(256 * j' + n))`;
        `\j' n. ival((YH:num->int16)(256 * j' + n))`;
        `\j'. mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 r (word j')))`;
        `ival((V0:num->int16)(2 * p + 1))`; `p:num`] BASEMUL2_ROW_ODD)] THEN
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
(* the stacks of the callees 3736 bytes below them: rho (the seed of the     *)
(* matrix) at bot + 3800, v at bot + 3832, the message at bot + 4344, e2 at  *)
(* bot + 4856, the multiplication cache of y at bot + 5368, y at bot + 5880, *)
(* t at bot + 6904, e1 at bot + 7928, u at bot + 8952 and the matrix at      *)
(* bot + 9976, with pointers to some of them saved below rho. The callees    *)
(* mlkem_poly_add and mlkem512_polyvec_add need some of them to be aligned   *)
(* to 16 bytes, as do the stores of rho by MOVAPS relative to RBP, which is  *)
(* bot + 12072, so that is given as aligned too (the simulation checks the   *)
(* alignment of RBP + d after removing the multiple of 16 d). The first 768  *)
(* bytes of the encryption key are decoded by mlkem512_polyvec_frombytes and *)
(* its last 32, rho, are copied as two 128-bit words to the seed for         *)
(* mlkem512_gen_matrix by legacy SSE moves through XMM1 and XMM2, which keep *)
(* the upper halves of YMM1 and YMM2, so their values after the first call   *)
(* are named by INDCPA_YMM_TAC. The message is decoded and decompressed by   *)
(* mlkem_poly_frommsg.                                                       *)
(* ------------------------------------------------------------------------- *)

let EN2_PK_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(pk,800)) s = num_of_bytelist ek`) (concl th)
    then
      ASSUME_TAC(REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
       (REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_MOD;
                     ARITH_RULE `MIN 800 768 = 768`]
        (AP_THM(AP_TERM `(MOD):num->num->num`
                 (REWRITE_RULE[READ_COMPONENT_COMPOSE] th))
           `2 EXP (8 * 768)`))) THEN
      MP_TAC(SPECL [`pk:int64`; `ek:byte list`; `768`; `32`;
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

let EN2_TT_TAC =
  INDCPA_GHOST_TAC "TT" 6904 512 "s22" THEN
  SUBGOAL_THEN
   `!i. i < 512
        ==> (TT:num->int16) i =
            word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "TT" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s22:x86state` (frees(concl th)) &&
      INDCPA_HAS_CONST "MOD" (concl th) && is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC DIV_MOD_EXP_LOW THEN UNDISCH_TAC `i < 512` THEN ARITH_TAC;
    ALL_TAC];;

let EN2_MU_TAC =
  INDCPA_GHOST_TAC "MU" 4344 256 "s34" THEN
  SUBGOAL_THEN
   `!i. i < 256
        ==> (MU:num->int16) i =
            word((3329 * (num_of_bytelist msg DIV 2 EXP i) MOD 2 + 1) DIV 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "MU" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s34:x86state` (frees(concl th)) &&
      can (find_term (fun t -> t = `3329`)) (concl th) &&
      is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

let EN2_SEED_TAC s =
  MP_TAC(SPECL [INDCPA_SP 3800; `num_of_bytelist rho`;
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

let EN2_MATRIX_TAC s =
  let addr = parse_term(Printf.sprintf
    "word_add bot (word (%d + 512 * (2 * q + j))):int64" 9976) in
  SUBGOAL_THEN
   `!q j n. q < 2 /\ j < 2 /\ n < 256
            ==> &0 <= mlkem_sample_ntt (APPEND rho [word q; word j]) n /\
                mlkem_sample_ntt (APPEND rho [word q; word j]) n < &3329`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC MLKEM_SAMPLE_NTT_REJ_BOUND THEN
    EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q j n. q < 2 /\ j < 2 /\ n < 256
            ==> ival((AM:num->int16)(512 * q + 256 * j + n)) =
                mlkem_sample_ntt (APPEND rho [word q; word j]) n`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    INDCPA_GHOST_SPEC_TAC "AM" `512 * q + 256 * j + n` THEN
    MP_TAC(SPECL [addr; s; `APPEND (rho:byte list) [word q; word j]`;
                  `k:num`; `n:num`] MLKEM_NATIVE_SAMPLE_COEFF) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    MATCH_MP_TAC READ16_OFFSET_EQ THEN ARITH_TAC;
    ALL_TAC];;

let EN2_AM_INST r j =
  let th = SPECL [mk_small_numeral r; mk_small_numeral j]
    (ASSUME `!q j n. q < 2 /\ j < 2 /\ n < 256
                     ==> ival((AM:num->int16)(512 * q + 256 * j + n)) =
                         mlkem_sample_ntt (APPEND rho [word q; word j]) n`) in
  CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES; ADD_ASSOC] THENC
            NUM_REDUCE_CONV) th;;

let EN2_AM_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 1024 ==> abs(ival((AM:num->int16) m)) <= &2 pow 12`
  (LABEL_TAC "ambound") THENL
   [X_GEN_TAC `m':num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`512`; `2`; `m':num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `512 * 2 = 1024`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:num`; `x:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`256`; `2`; `x:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 2 = 512`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(INT_ARITH
     `&0 <= x /\ x < &3329 ==> abs(x:int) <= &2 pow 12`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC];;

let EN2_BASEMUL_DEFS =
  [basemul2_even; basemul2_odd; pmul_acc2; pmull_acc2; pmull];;

let EN2_U0_GOAL = `!q p. q < 2 /\ p < 128
       ==> (ival((U0:num->int16)(256 * q + 2 * p)) ==
            &169 *
            ((mlkem_sample_ntt (APPEND rho [word q; word 1]) (2 * p + 1) *
              ival((MC:num->int16)(128 + p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 1]) (2 * p) *
              ival((YH:num->int16)(256 + 2 * p))) +
             (mlkem_sample_ntt (APPEND rho [word q; word 0]) (2 * p + 1) *
              ival(MC p) +
              mlkem_sample_ntt (APPEND rho [word q; word 0]) (2 * p) *
              ival(YH(2 * p))))) (mod &3329) /\
           (ival(U0(256 * q + 2 * p + 1)) ==
            &169 *
            ((mlkem_sample_ntt (APPEND rho [word q; word 1]) (2 * p + 1) *
              ival(YH(256 + 2 * p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 1]) (2 * p) *
              ival(YH(256 + 2 * p + 1))) +
             (mlkem_sample_ntt (APPEND rho [word q; word 0]) (2 * p + 1) *
              ival(YH(2 * p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 0]) (2 * p) *
              ival(YH(2 * p + 1))))) (mod &3329)`;;

let EN2_U0_TAC =
  INDCPA_GHOST_TAC "U0" 8952 512 "s84" THEN
  SUBGOAL_THEN EN2_U0_GOAL ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THENL
     (map (fun q -> INDCPA_BASEMULK_ROW_TAC 2 "U0" (8952 + 512 * q)
                     "ambound" (map (EN2_AM_INST q) [0;1])
                     EN2_BASEMUL_DEFS) [0;1]);
    ALL_TAC];;

let EN2_TT_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 512 ==> abs(ival((TT:num->int16) m)) <= &2 pow 12`
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

let EN2_V0_GOAL = `!p. p < 128
       ==> (ival((V0:num->int16)(2 * p)) ==
            &169 *
            ((ival((TT:num->int16)(256 + 2 * p + 1)) *
              ival((MC:num->int16)(128 + p)) +
              ival(TT(256 + 2 * p)) * ival((YH:num->int16)(256 + 2 * p))) +
             (ival(TT(2 * p + 1)) * ival(MC p) +
              ival(TT(2 * p)) * ival(YH(2 * p))))) (mod &3329) /\
           (ival(V0(2 * p + 1)) ==
            &169 *
            ((ival(TT(256 + 2 * p + 1)) * ival(YH(256 + 2 * p)) +
              ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p + 1))) +
             (ival(TT(2 * p + 1)) * ival(YH(2 * p)) +
              ival(TT(2 * p)) * ival(YH(2 * p + 1))))) (mod &3329)`;;

let EN2_V0_TAC =
  INDCPA_GHOST_TAC "V0" 3832 256 "s90" THEN
  SUBGOAL_THEN EN2_V0_GOAL ASSUME_TAC THENL
   [INDCPA_BASEMULK_ROW_TAC 2 "V0" 3832 "ttbound" [] EN2_BASEMUL_DEFS;
    ALL_TAC];;

let EN2_COMPRESS_POST_TAC v y =
  let vt = mk_var(v,`:num->int16`) in
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && mem vt (frees(concl th)) &&
    INDCPA_HAS_CONST "nsum" (concl th))) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC VAL_LT_OF_IVAL_REM THEN EXISTS_TAC y THEN ASM_SIMP_TAC[];
    DISCH_TAC];;

let EN2_FINAL_TAC =
  REWRITE_TAC[ARITH_RULE `768 = 640 + 128`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`ek:byte list`; `msg:byte list`; `r:byte list`;
                `TT:num->int16`; `YH:num->int16`; `MC:num->int16`;
                `E1:num->int16`; `E2:num->int16`; `MU:num->int16`;
                `U0:num->int16`; `V0:num->int16`; `U1:num->int16`;
                `V1:num->int16`; `U3:num->int16`; `V4:num->int16`]
          (REWRITE_RULE[ASSUME `mlkem_slice 768 32 ek = rho`]
            KPKE_ENCRYPT_K2_RESULT)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
           REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
    SIMP_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The encryption key ek of 800 bytes is at pk, the       *)
(* message msg of 32 bytes at m and the randomness r of 32 bytes at coins,   *)
(* and the ciphertext of 768 bytes written at c is that of kpke_encrypt      *)
(* mlkem512 ek msg r in common/fips203/fips203.ml, for any ek (FIPS 203      *)
(* decodes t modulo q, while the code multiplies by the 12-bit fields, which *)
(* are congruent). The theorem assumes that SampleNTT terminates for each    *)
(* entry of the matrix, as for mlkem512_gen_matrix. The stack is the 12120   *)
(* bytes below the return address, for up to 31 bytes for the alignment, the *)
(* 8352 bytes of the pushes and the buffers and the 3736 used by the callees *)
(* below them. The matrix is generated with transposition, so the theorem    *)
(* for mlkem512_gen_matrix is specialized to that case. The noise y and e1   *)
(* is sampled by one call of mlkem512_poly_getnoise_eta1122_4x, and e2 by    *)
(* mlkem512_poly_getnoise_eta2.                                              *)
(* ------------------------------------------------------------------------- *)

let EN2_FRAME = (12120,0,3736,8352);;

let EN2_CALL th =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,EN2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,REWRITE_RULE[ALL] th);;

let EN2_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`c:int64`; `m:int64`; `pk:int64`; `coins:int64`; `ek:byte list`;
    `msg:byte list`; `r:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 12120 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  UNDISCH_TAC
   `!i j. i < 2 /\ j < 2
          ==> mlkem_samplentt_terminates
               (APPEND (mlkem_slice 768 32 ek) [word j; word i])` THEN
  ABBREV_TAC `rho = mlkem_slice 768 32 ek` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN
   `!i j. i < 2 /\ j < 2
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

let EN2_SETUP_TAC =
  INDCPA_BOT_TAC EN2_FRAME
   [3800; 3816; 3832; 4344; 4856; 7928; 8952; 12072] THEN
  INDCPA_FRAME_TAC ["memory :> bytes(c:int64,768)"] EN2_FRAME THEN
  INDCPA_NONOV_TAC 12088
   [`c:int64,768`; `m:int64,32`; `pk:int64,800`; `coins:int64,32`;
    `word pc:int64,libmlkem_size`; `word_add stackpointer (word 12120):int64,8`] THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   ["rbx_init",`RBX`; "rbp_init",`RBP`; "r12_init",`R12`;
    "r13_init",`R13`; "r14_init",`R14`; "r15_init",`R15`];;

let EN2_MAIN_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = EN2_CALL in
  ENSURES_INIT_TAC "s0" THEN EN2_PK_TAC THEN

  (*** The public vector t and the message ***)

  X86_STEPS_TAC EN2_EXEC (1--2) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC EN2_EXEC (3--21) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `num_of_bytelist ek MOD 2 EXP (8 * 768)`] @
    post) 22 THEN
  INDCPA_NORM_TAC THEN EN2_TT_TAC THEN INDCPA_YMM_TAC "s22" THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC EN2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (23--33) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `num_of_bytelist msg`] @ post) 34 THEN
  INDCPA_NORM_TAC THEN EN2_MU_TAC THEN

  (*** The transposed matrix ***)

  EN2_SEED_TAC "s34" THEN
  X86_STEPS_TAC EN2_EXEC (35--42) THEN INDCPA_NORM_TAC THEN
  call (INDCPA_GEN_MATRIX_SPEC
         MLKEM_NATIVE_GEN_MATRIX_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
         `word 1:int64`)
   ([`read RDI s`; `read RSI s`; `rho:byte list`; `k:num`] @ post) 43 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_GHOST_TAC "AM" 9976 1024 "s43" THEN
  EN2_MATRIX_TAC `s43:x86state` THEN

  (*** The noise: y and e1 from one call, then e2 ***)

  X86_STEPS_TAC EN2_EXEC (44--55) THEN INDCPA_NORM_TAC THEN
  call
   MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
     `r:byte list`; `read R9 s`; `word 1:int64`; `word 2:int64`;
     `word 3:int64`] @ post) 56 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_NOISE_ETA_TAC 3 "YS" 5880 2 "r" "word j" "s56" THEN
  INDCPA_NOISE_ETA_TAC 2 "E1" 7928 2 "r" "word(2 + j)" "s56" THEN
  INDCPA_DISCARD_LETS_TAC THEN
  X86_STEPS_TAC EN2_EXEC (57--64) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `r:byte list`; `read RDX s`] @ post) 65 THEN
  INDCPA_NORM_TAC THEN INDCPA_NOISE1_TAC "E2" 4856 "r" "word 4" "s65" THEN
  INDCPA_DISCARD_LETS_TAC THEN

  (*** The NTT of the noise and its multiplication cache ***)

  X86_STEPS_TAC EN2_EXEC (66--67) THEN
  call MLKEM_NATIVE_POLYVEC_NTT_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `YS:num->int16`] @ post) 68 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_NTT_ETA_TAC 3 "YH" 5880 2 "YS" "r" "word j" "s68" THEN
  X86_STEPS_TAC EN2_EXEC (69--71) THEN
  call
   MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `YH:num->int16`] @ post) 72 THEN
  INDCPA_NORM_TAC THEN INDCPA_MULCACHE_TAC "MC" 5368 2 "YH" "s72" THEN

  (*** The products with the transposed matrix and with t ***)

  MAP_EVERY (fun (q,k0,k1) ->
    let a = (9976 + 1024 * q,"AM",512 * q)
    and y = (5880,"YH") and t = (5368,"MC") in
    X86_STEPS_TAC EN2_EXEC (k0--k1) THEN INDCPA_NORM_TAC THEN
    INDCPA_BASEMULK_PRE_TAC 2 a y t ("s"^string_of_int k1) THEN
    call MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
     (INDCPA_BASEMULK_ARGS 2 ("AM",512 * q) "YH" "MC") (k1 + 1) THEN
    INDCPA_BASEMULK_DROP_PRE_TAC 2 a y t THEN INDCPA_NORM_TAC)
   [0,73,77; 1,79,83] THEN
  EN2_AM_BOUND_TAC THEN EN2_U0_TAC THEN
  X86_STEPS_TAC EN2_EXEC (85--89) THEN INDCPA_NORM_TAC THEN
  INDCPA_BASEMULK_PRE_TAC 2 (6904,"TT",0) (5880,"YH") (5368,"MC") "s89" THEN
  call MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   (INDCPA_BASEMULK_ARGS 2 ("TT",0) "YH" "MC") 90 THEN
  INDCPA_BASEMULK_DROP_PRE_TAC 2 (6904,"TT",0) (5880,"YH") (5368,"MC") THEN
  INDCPA_NORM_TAC THEN EN2_TT_BOUND_TAC THEN EN2_V0_TAC THEN

  (*** The inverse NTTs, adding the noise and the message, reductions ***)

  X86_STEPS_TAC EN2_EXEC (91--92) THEN
  call MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `U0:num->int16`] @ post) 93 THEN
  INDCPA_NORM_TAC THEN INDCPA_INVNTT_TAC "U1" 8952 2 "U0" "s93" THEN
  X86_STEPS_TAC EN2_EXEC (94--95) THEN
  call MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `V0:num->int16`] @ post) 96 THEN
  INDCPA_NORM_TAC THEN INDCPA_INVNTT1_TAC "V1" 3832 "V0" "s96" THEN
  X86_STEPS_TAC EN2_EXEC (97--99) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLYVEC_ADD_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `U1:num->int16`; `E1:num->int16`] @ post)
   100 THEN
  X86_STEPS_TAC EN2_EXEC (101--105) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `V1:num->int16`; `E2:num->int16`] @ post)
   106 THEN
  X86_STEPS_TAC EN2_EXEC (107--111) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`;
     `\i. word_add ((V1:num->int16) i) ((E2:num->int16) i)`;
     `MU:num->int16`] @ post) 112 THEN
  X86_STEPS_TAC EN2_EXEC (113--114) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `\i. word_add ((U1:num->int16) i) ((E1:num->int16) i)`] @
    post) 115 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_REDUCE_TAC "U3" 8952 512
    "word_add ((U1:num->int16) i) ((E1:num->int16) i)" "s115" THEN
  X86_STEPS_TAC EN2_EXEC (116--117) THEN
  call MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`;
     `\i. word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                   ((MU:num->int16) i)`] @ post) 118 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_REDUCE_TAC "V4" 3832 256
    "word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i)) \
     ((MU:num->int16) i)" "s118" THEN

  (*** The compression and encoding of u and v ***)

  X86_STEPS_TAC EN2_EXEC (119--121) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `U3:num->int16`] @ post) 122 THEN
  EN2_COMPRESS_POST_TAC "U3"
   `ival(word_add ((U1:num->int16) i) ((E1:num->int16) i))` THEN
  X86_STEPS_TAC EN2_EXEC (123--126) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `V4:num->int16`] @ post) 127 THEN
  EN2_COMPRESS_POST_TAC "V4"
   `ival(word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i))` THEN

  (*** Zeroing the buffers and the seed, the return ***)

  X86_STEPS_TAC EN2_EXEC (128--173) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN EN2_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_ENC_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = time prove
 (`!c m pk coins (ek:byte list) (msg:byte list) (r:byte list) pc
    stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    LENGTH ek = 800 /\ LENGTH msg = 32 /\ LENGTH r = 32 /\
    (!i j. i < 2 /\ j < 2
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 768 32 ek) [word j; word i])) /\
    nonoverlapping (c,768) (word_sub stackpointer (word 12120),12128) /\
    ALLPAIRS nonoverlapping
     [(c,768); (word_sub stackpointer (word 12120),12128)]
     [(m,32); (pk,800); (coins,32); (word pc,libmlkem_size)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + mlkem512_indcpa_enc) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [c; m; pk; coins] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(m,32)) s = num_of_bytelist msg /\
              read (memory :> bytes(pk,800)) s = num_of_bytelist ek /\
              read (memory :> bytes(coins,32)) s = num_of_bytelist r)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              read (memory :> bytes(c,768)) s =
              num_of_bytelist(kpke_encrypt mlkem512 ek msg r) /\
              C_RETURN s = word 0)
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(c,768);
            memory :> bytes(word_sub stackpointer (word 12120),12120)])`,
  EN2_INTRO_TAC THEN EN2_SETUP_TAC THEN EN2_MAIN_TAC);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend only on the      *)
(* addresses and on rho, the last 32 bytes of the public key, through the    *)
(* samples of SampleNTT for the transposed matrix, but not on the message or *)
(* the randomness. At the end the frame variables are expanded in them by    *)
(* INDCPA_UNBOT_TAC, since they are not arguments of f_events.               *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let EN2_SAFE_ALLOWED =
  [`pc:num`; `c:int64`; `m:int64`; `pk:int64`; `coins:int64`;
   `stackpointer:int64`; `returnaddress:int64`; `rho:byte list`;
   `bot:int64`];;

let EN2_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,EN2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      (`e:(uarch_event)list`::ilist @
       [`pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`])
      n THENL
     [EXISTS_E2_TAC (ref EN2_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let EN2_SAFE_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (INDCPA_GEN_MATRIX_SAFE_SPEC
     MLKEM_NATIVE_GEN_MATRIX_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE `word 1:int64`)
   "H_GM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC
   MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE
   "H_GETNOISE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC
   MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE
   "H_ETA2" THEN
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_FROMBYTES";
    MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_FROMMSG";
    MLKEM_NATIVE_POLYVEC_NTT_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_NTT";
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_MULCACHE";
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_BASEMUL";
    MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_INVNTT";
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_POLY_INVNTT";
    MLKEM_NATIVE_POLYVEC_ADD_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_ADD";
    MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_POLY_ADD";
    MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_REDUCE";
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_POLY_REDUCE";
    MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_COMPRESS_DU";
    MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_COMPRESS_DV"] THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `c:int64`; `m:int64`; `pk:int64`; `coins:int64`;
    `ek:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 12120 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  UNDISCH_TAC
   `!i j. i < 2 /\ j < 2
          ==> mlkem_samplentt_terminates
               (APPEND (mlkem_slice 768 32 ek) [word j; word i])` THEN
  ABBREV_TAC `rho = mlkem_slice 768 32 ek` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN
   `!i j. i < 2 /\ j < 2
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

let EN2_SAFE_MAIN_TAC =
  let call = EN2_SAFE_CALL_TAC in
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  EN2_PK_TAC THEN
  X86_STEPS_TAC EN2_EXEC (1--2) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC EN2_EXEC (3--21) THEN INDCPA_NORM_TAC THEN
  call "H_FROMBYTES" [`read RDI s`; `read RSI s`] 22 THEN INDCPA_NORM_TAC THEN
  INDCPA_YMM_TAC "s22" THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC EN2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (23--33) THEN INDCPA_NORM_TAC THEN
  call "H_FROMMSG" [`read RDI s`; `read RSI s`] 34 THEN INDCPA_NORM_TAC THEN
  EN2_SEED_TAC "s34" THEN
  X86_STEPS_TAC EN2_EXEC (35--42) THEN INDCPA_NORM_TAC THEN
  call "H_GM" [`read RDI s`; `read RSI s`; `rho:byte list`; `k:num`] 43 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN2_EXEC (44--55) THEN INDCPA_NORM_TAC THEN
  call "H_GETNOISE"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`] 56
  THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN2_EXEC (57--64) THEN INDCPA_NORM_TAC THEN
  call "H_ETA2" [`read RDI s`; `read RSI s`; `read RDX s`] 65 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN2_EXEC (66--67) THEN
  call "H_NTT" [`read RDI s`] 68 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN2_EXEC (69--71) THEN
  call "H_MULCACHE" [`read RDI s`; `read RSI s`] 72 THEN INDCPA_NORM_TAC THEN
  MAP_EVERY (fun (k0,k1) ->
    X86_STEPS_TAC EN2_EXEC (k0--k1) THEN INDCPA_NORM_TAC THEN
    call "H_BASEMUL"
     [`read RSI s`; `read RDX s`; `read RCX s`; `read RDI s`] (k1 + 1) THEN
    INDCPA_NORM_TAC)
   [73,77; 79,83; 85,89] THEN
  X86_STEPS_TAC EN2_EXEC (91--92) THEN
  call "H_INVNTT" [`read RDI s`] 93 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN2_EXEC (94--95) THEN
  call "H_POLY_INVNTT" [`read RDI s`] 96 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN2_EXEC (97--99) THEN INDCPA_NORM_TAC THEN
  call "H_ADD" [`read RDI s`; `read RSI s`] 100 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN2_EXEC (101--105) THEN INDCPA_NORM_TAC THEN
  call "H_POLY_ADD" [`read RDI s`; `read RSI s`] 106 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN2_EXEC (107--111) THEN INDCPA_NORM_TAC THEN
  call "H_POLY_ADD" [`read RDI s`; `read RSI s`] 112 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN2_EXEC (113--114) THEN INDCPA_NORM_TAC THEN
  call "H_REDUCE" [`read RDI s`] 115 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN2_EXEC (116--117) THEN
  call "H_POLY_REDUCE" [`read RDI s`] 118 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN2_EXEC (119--121) THEN INDCPA_NORM_TAC THEN
  call "H_COMPRESS_DU" [`read RDI s`; `read RSI s`] 122 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN2_EXEC (123--126) THEN INDCPA_NORM_TAC THEN
  call "H_COMPRESS_DV" [`read RDI s`; `read RSI s`] 127 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC EN2_EXEC (128--173) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_ENC_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
   forall e c m pk coins (ek:byte list) pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH ek = 800 /\
    (!i j. i < 2 /\ j < 2
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 768 32 ek) [word j; word i])) /\
    nonoverlapping (c,768) (word_sub stackpointer (word 12120),12128) /\
    ALLPAIRS nonoverlapping
     [(c,768); (word_sub stackpointer (word 12120),12128)]
     [(m,32); (pk,800); (coins,32); (word pc,libmlkem_size)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + mlkem512_indcpa_enc) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [c; m; pk; coins] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(pk,800)) s = num_of_bytelist ek /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              C_RETURN s = word 0 /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events c m pk coins pc
                        (word_sub stackpointer (word 12120)) returnaddress
                        (mlkem_slice 768 32 ek) /\
                 memaccess_inbounds e2
                  [m,32; pk,800; coins,32; c,768;
                   word_sub stackpointer (word 12120),12128;
                   word(pc + mlkem_poly_compress_d4_const1),8; word(pc + mlkem_poly_compress_d4_const2),8;
                   word(pc + mlkem_poly_invntt_tomont_consts),48; word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                   word(pc + mlkem512_gen_matrix_consts),2; word(pc + rodata_mlk_zetas),256]
                  [c,768; word_sub stackpointer (word 12120),12120]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(c,768);
            memory :> bytes(word_sub stackpointer (word 12120),12120)])`,
  EN2_SAFE_INTRO_TAC THEN EN2_SETUP_TAC THEN EN2_SAFE_MAIN_TAC);;
