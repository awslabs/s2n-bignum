(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The key generation of K-PKE for ML-KEM-1024 (FIPS 203 Algorithm 13). This *)
(* is the code for mlkem1024_indcpa_keypair_derand from mlkem-native's       *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md). It hashes the 32-byte seed d followed by the     *)
(* byte 4 with SHA3-512 into the seeds rho and sigma, generates the matrix   *)
(* in NTT form from rho, samples the secret s and the error e from sigma     *)
(* (with eta = 2) and transforms them, computes t = A s + e in the NTT       *)
(* domain, and writes the encoding of t followed by rho as the public key    *)
(* and the encoding of s as the secret key, zeroing its buffers. It is       *)
(* verified in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml),      *)
(* where it is at address 0x1110, using the theorems for mlkem_sha3_512,     *)
(* mlkem1024_gen_matrix, mlkem1024_poly_getnoise_eta1_4x,                    *)
(* mlkem1024_polyvec_ntt, mlkem1024_polyvec_mulcache_compute,                *)
(* mlkem1024_polyvec_basemul_acc_montgomery_cached,                          *)
(* mlkem1024_polyvec_tomont, mlkem1024_polyvec_add, mlkem1024_polyvec_reduce *)
(* and mlkem1024_polyvec_tobytes in the image.                               *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_sha3_512_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_gen_matrix_k4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_poly_getnoise_eta1_4x_k4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_ntt_k4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_mulcache_compute_k4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_basemul_k4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_tomont_k4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_add_k4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_reduce_k4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_tobytes_k4_gcc12_O2.ml";;
needs "x86/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image:

    1110: lea    r10,[rsp+0x8]
    1115: and    rsp,0xffffffffffffffe0
    1119: push   QWORD PTR [r10-0x8]
    111d: push   rbp
    111e: mov    rbp,rsp
    1121: push   r15
    1123: push   r14
    1125: lea    r14,[rbp-0x2030]
    112c: push   r13
    112e: lea    r13,[rbp-0x3c30]
    1135: push   r12
    1137: lea    r12,[rbp-0x3c50]
    113e: push   r10
    1140: push   rbx
    1141: lea    rbx,[rbp-0x3c70]
    1148: sub    rsp,0x3cc0
    114f: movdqu xmm1,XMMWORD PTR [rdx]
    1153: movdqu xmm2,XMMWORD PTR [rdx+0x10]
    1158: mov    QWORD PTR [rbp-0x3cc8],rdi
    115f: mov    QWORD PTR [rbp-0x3cd0],rsi
    1166: mov    rdi,rbx
    1169: lea    rsi,[rbp-0x3cb0]
    1170: mov    edx,0x21
    1175: movaps XMMWORD PTR [rbp-0x3cb0],xmm1
    117c: movaps XMMWORD PTR [rbp-0x3ca0],xmm2
    1183: mov    QWORD PTR [rbp-0x3ce0],rsi
    118a: mov    QWORD PTR [rbp-0x3cd8],rbx
    1191: mov    BYTE PTR [rbp-0x3c90],0x4
    1198: call   3570 <mlkem_sha3_512>
    119d: mov    rsi,rbx
    11a0: xor    edx,edx
    11a2: mov    rdi,r14
    11a5: mov    QWORD PTR [rbp-0x3cc0],r14
    11ac: lea    rbx,[rbp-0x2830]
    11b3: call   1020 <mlkem1024_gen_matrix>
    11b8: sub    rsp,0x8
    11bc: mov    r8,r12
    11bf: xor    r9d,r9d
    11c2: push   0x3
    11c4: lea    rcx,[rbp-0x2230]
    11cb: mov    rdi,rbx
    11ce: lea    rdx,[rbp-0x2430]
    11d5: push   0x2
    11d7: lea    rsi,[rbp-0x2630]
    11de: push   0x1
    11e0: call   2260 <mlkem1024_poly_getnoise_eta1_4x>
    11e5: lea    rax,[rbp-0x3830]
    11ec: add    rsp,0x18
    11f0: mov    r8,r12
    11f3: mov    QWORD PTR [rbp-0x3cb8],rax
    11fa: mov    rdi,rax
    11fd: lea    rcx,[rbp-0x3230]
    1204: lea    rdx,[rbp-0x3430]
    120b: push   0x7
    120d: lea    rsi,[rbp-0x3630]
    1214: mov    r9d,0x4
    121a: mov    r15,rax
    121d: push   0x6
    121f: lea    r12,[rbp-0x3030]
    1226: push   0x5
    1228: call   2260 <mlkem1024_poly_getnoise_eta1_4x>
    122d: add    rsp,0x20
    1231: mov    rdi,rbx
    1234: call   2040 <mlkem1024_polyvec_ntt>
    1239: mov    rdi,r15
    123c: mov    r15,r12
    123f: call   2040 <mlkem1024_polyvec_ntt>
    1244: mov    rsi,rbx
    1247: mov    rdi,r13
    124a: call   2190 <mlkem1024_polyvec_mulcache_compute>
    124f: mov    rsi,r14
    1252: mov    rdi,r15
    1255: mov    rcx,r13
    1258: mov    rdx,rbx
    125b: add    r15,0x200
    1262: add    r14,0x800
    1269: call   20a0 <mlkem1024_polyvec_basemul_acc_montgomery_cached>
    126e: cmp    r15,rbx
    1271: jne    124f <mlkem1024_indcpa_keypair_derand+0x13f>
    1273: mov    rdi,r12
    1276: call   2230 <mlkem1024_polyvec_tomont>
    127b: mov    r14,QWORD PTR [rbp-0x3cb8]
    1282: mov    rdi,r12
    1285: mov    rsi,r14
    1288: call   2200 <mlkem1024_polyvec_add>
    128d: mov    rdi,r12
    1290: call   21d0 <mlkem1024_polyvec_reduce>
    1295: mov    rdi,r15
    1298: call   21d0 <mlkem1024_polyvec_reduce>
    129d: mov    rdi,QWORD PTR [rbp-0x3cd0]
    12a4: mov    rsi,r15
    12a7: call   1fc0 <mlkem1024_polyvec_tobytes>
    12ac: mov    rbx,QWORD PTR [rbp-0x3cc8]
    12b3: mov    rsi,r12
    12b6: mov    rdi,rbx
    12b9: call   1fc0 <mlkem1024_polyvec_tobytes>
    12be: xor    eax,eax
    12c0: mov    rdi,r13
    12c3: mov    ecx,0x80
    12c8: movdqa xmm3,XMMWORD PTR [rbp-0x3c70]
    12d0: movdqa xmm4,XMMWORD PTR [rbp-0x3c60]
    12d8: rep    stos QWORD PTR es:[rdi],rax
    12db: movups XMMWORD PTR [rbx+0x600],xmm3
    12e2: movups XMMWORD PTR [rbx+0x610],xmm4
    12e9: mov    ecx,0x100
    12ee: mov    rdi,r15
    12f1: rep    stos QWORD PTR es:[rdi],rax
    12f4: mov    ecx,0x100
    12f9: mov    rdi,r12
    12fc: rep    stos QWORD PTR es:[rdi],rax
    12ff: mov    ecx,0x100
    1304: mov    rdi,r14
    1307: mov    QWORD PTR [rbp-0x3cb8],r14
    130e: rep    stos QWORD PTR es:[rdi],rax
    1311: mov    rdi,QWORD PTR [rbp-0x3cc0]
    1318: mov    ecx,0x400
    131d: rep    stos QWORD PTR es:[rdi],rax
    1320: mov    rdi,QWORD PTR [rbp-0x3cc0]
    1327: pxor   xmm0,xmm0
    132b: mov    BYTE PTR [rbp-0x3c90],0x0
    1332: mov    rax,QWORD PTR [rbp-0x3ce0]
    1339: movaps XMMWORD PTR [rbp-0x3cb0],xmm0
    1340: movaps XMMWORD PTR [rbp-0x3ca0],xmm0
    1347: mov    rax,QWORD PTR [rbp-0x3cd8]
    134e: movaps XMMWORD PTR [rbp-0x3c70],xmm0
    1355: movaps XMMWORD PTR [rbp-0x3c60],xmm0
    135c: movaps XMMWORD PTR [rbp-0x3c50],xmm0
    1363: movaps XMMWORD PTR [rbp-0x3c40],xmm0
    136a: lea    rsp,[rbp-0x30]
    136e: xor    eax,eax
    1370: pop    rbx
    1371: pop    r10
    1373: pop    r12
    1375: pop    r13
    1377: pop    r14
    1379: pop    r15
    137b: pop    rbp
    137c: lea    rsp,[r10-0x8]
    1380: ret
 ***)

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x1110,0x1381];;

let KP4_EXEC = MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The key generation in FIPS 203 in terms of the coefficients computed by   *)
(* the code: those of the NTTs of s and e, those of the multiplication       *)
(* cache, those of the matrix-vector product in Montgomery form, and those   *)
(* of the final results after Montgomery conversion, addition and reduction. *)
(* The two lemmas on single coefficients relate the computation of the code  *)
(* to MultiplyNTTs and the addition of e in the NTT domain, for even and odd *)
(* coefficients. This is as for AArch64.                                     *)
(* ------------------------------------------------------------------------- *)

let KPKE_KEYGEN_COEFF_EVEN_K4 = prove
 (`!(A:num->num->int) (Y:num->num->int) (YT:num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 4 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329) /\
                    (YT j == Y j (2 * p + 1) *
                             &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (t == &169 * ((A 3 (2 * p + 1) * YT 3 + A 3 (2 * p) * Y 3 (2 * p)) +
                   (A 2 (2 * p + 1) * YT 2 + A 2 (2 * p) * Y 2 (2 * p)) +
                   (A 1 (2 * p + 1) * YT 1 + A 1 (2 * p) * Y 1 (2 * p)) +
                   (A 0 (2 * p + 1) * YT 0 + A 0 (2 * p) * Y 0 (2 * p))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 4}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p)))
          eh`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_4;
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

let KPKE_KEYGEN_COEFF_ODD_K4 = prove
 (`!(A:num->num->int) (Y:num->num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 4 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329)) /\
     (t == &169 *
           ((A 3 (2 * p + 1) * Y 3 (2 * p) + A 3 (2 * p) * Y 3 (2 * p + 1)) +
            (A 2 (2 * p + 1) * Y 2 (2 * p) + A 2 (2 * p) * Y 2 (2 * p + 1)) +
            (A 1 (2 * p + 1) * Y 1 (2 * p) + A 1 (2 * p) * Y 1 (2 * p + 1)) +
            (A 0 (2 * p + 1) * Y 0 (2 * p) + A 0 (2 * p) * Y 0 (2 * p + 1))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 4}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p + 1)))
          eh`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_4;
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

let KPKE_KEYGEN_K4_RESULT = prove
 (`!d rho sigma (sh:num->int16) (eh:num->int16) (mc:num->int16)
    (pt:num->int16) (pt2:num->int16) (tr:num->int16) (sr:num->int16).
     mlkem_g(APPEND d [word 4]) = rho,sigma /\
     (!i j n. i < 4 /\ j < 4 /\ n < 256
              ==> mlkem_sample_ntt (APPEND rho [word j; word i]) n < &3329) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(sh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word j))) i)
                (mod &3329) /\
                abs(ival(sh(256 * j + i))) <= &23594) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(eh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(4 + j)))) i)
                (mod &3329) /\
                abs(ival(eh(256 * j + i))) <= &23594) /\
     (!j p. j < 4 /\ p < 128
            ==> (ival(mc(128 * j + p)) ==
                 ival(sh(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!r p. r < 4 /\ p < 128
            ==> (ival(pt(256 * r + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p + 1) *
                   ival(mc(384 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p) *
                   ival(sh(768 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
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
                 ((mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p + 1) *
                   ival(sh(768 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p) *
                   ival(sh(768 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
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
     (!i. i < 1024 ==> (ival(pt2 i) == &65536 * ival(pt i)) (mod &3329) /\
                      abs(ival(pt2 i)) <= &3328) /\
     (!i. i < 1024 ==> ival(tr i) = ival(word_add (pt2 i) (eh i)) rem &3329) /\
     (!i. i < 1024 ==> ival(sr i) = ival(sh i) rem &3329)
     ==> num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq tr 1024)) +
         2 EXP (8 * 1536) * num_of_bytelist rho =
         num_of_bytelist(FST(kpke_keygen mlkem1024 d)) /\
         num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq sr 1024)) =
         num_of_bytelist(SND(kpke_keygen mlkem1024 d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem1024] THEN
  MP_TAC(SPECL [`4`; `2`; `2`; `11`; `5`; `d:byte list`] KPKE_KEYGEN_FIPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; MLKEM_ENCODE_LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `256 * 4 = 1024`;
              ARITH_RULE `(12 * 1024) DIV 8 = 1536`] THEN
  W(fun (_,w) ->
    let encs = find_terms (fun t -> match strip_comb t with
       (Const("mlkem_encode",_),[_;_;_]) -> true | _ -> false) w in
    MAP_EVERY (fun enc ->
      MP_TAC(PART_MATCH (lhand o rand) MLKEM_ENCODE_12_LIST
              (mk_comb(`num_of_bytelist`,enc)))) encs) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ARITH_RULE `EVEN 1024`; MLKEM_NTT_CBD_BOUNDS] THEN
  SIMP_TAC[GSYM IN_MLKEM_ZQ; RING_ADD; RING_SUM; MLKEM_NTT_CBD_IN_ZQ] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC;
    AP_TERM_TAC THEN AP_TERM_TAC] THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM IWORD_IVAL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[IWORD_IVAL] THEN
  MP_TAC(SPECL [`256`; `4`; `i:num`] EXISTS_DIV_MOD_LT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `256 * 4 = 1024`] THEN
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
      `mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(4 + r)))) (2 * p)`;
      `p:num`] KPKE_KEYGEN_COEFF_EVEN_K4);
    MP_TAC(SPECL
     [`\j. mlkem_sample_ntt (APPEND rho [word j; word r])`;
      `\j n. ival((sh:num->int16)(256 * j + n))`;
      `\j. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word j)))`;
      `ival((pt:num->int16)(256 * r + 2 * p + 1))`;
      `ival((pt2:num->int16)(256 * r + 2 * p + 1))`;
      `ival((eh:num->int16)(256 * r + 2 * p + 1))`;
      `mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(4 + r))))
                 (2 * p + 1)`;
      `p:num`] KPKE_KEYGEN_COEFF_ODD_K4)] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, by AND with   *)
(* -32 before the pushes of a copy of the return address, RBP, R15, R14,     *)
(* R13, R12, R10 and RBX, with RBP as a frame pointer, and their addresses   *)
(* are offsets from the frame variable bot of INDCPA_BOT_TAC, the bottom of  *)
(* the stacks of the callees 3768 bytes below them: the input of SHA3-512 at *)
(* bot + 3832, its output (rho and sigma) at bot + 3896, the multiplication  *)
(* cache of s at bot + 3960, e at bot + 4984, t at bot + 7032, s at          *)
(* bot + 9080 and the matrix at bot + 11128, with pointers to some of them   *)
(* saved below the input. The callees mlkem1024_polyvec_tomont and           *)
(* mlkem1024_polyvec_add need t and e to be aligned to 16 bytes, and the SSE *)
(* moves relative to RBP, which is bot + 19368, need that to be aligned too. *)
(* The input to SHA3-512 is the seed copied as two 128-bit words by legacy   *)
(* SSE moves through XMM1 and XMM2, which keep the upper halves of YMM1 and  *)
(* YMM2, so their initial values are named by INDCPA_YMM_TAC, and the byte 4 *)
(* (the parameter k); its output is the two seeds rho and sigma as in        *)
(* mlkem_g.                                                                  *)
(* ------------------------------------------------------------------------- *)

let KP4_INPUT = prove
 (`!a:int64 (d:byte list) c s:x86state.
        LENGTH d = 32 /\ c < 256 /\
        read (memory :> bytes128 a) s =
        word(num_of_bytelist d MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(num_of_bytelist d DIV 2 EXP 128) /\
        read (memory :> bytes8(word_add a (word 32))) s = word c
        ==> LENGTH(APPEND d [word c:byte]) = 33 /\
            read (memory :> bytes(a,33)) s =
            num_of_bytelist(APPEND d [word c])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes(a,32)) s = num_of_bytelist d`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GENMAT_BYTES_32_OF_HALVES THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `d:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; NUM_OF_BYTELIST_APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `33 = 32 + 1`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_1] THEN
  ASM_REWRITE_TAC[num_of_bytelist; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

let KP4_INPUT_TAC s =
  MP_TAC(SPECL [INDCPA_SP 3832; `d:byte list`; `4`; s] KP4_INPUT) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    STRIP_TAC];;

let KP4_G_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
             `read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 c)`)
           (concl th)
    then ASSUME_TAC th THEN
         MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                 (REWRITE_RULE
                   [ASSUME `FST(mlkem_g(APPEND d [word 4])) = rho`;
                    ASSUME `SND(mlkem_g(APPEND d [word 4])) = sigma`]
                   (MATCH_MP MLKEM_G_BYTES th))) THEN
         CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The facts about the stages of the computation other than those given by   *)
(* the tactics in mlkem_native_indcpa.ml: the coefficients of the matrix as  *)
(* given by SampleNTT, the bounds on the inputs of the multiplications, the  *)
(* rows of the matrix-vector product, and rho in the public key, copied      *)
(* there through XMM3 and XMM4 after the last call, whose values there are   *)
(* named. This is as for AArch64.                                            *)
(* ------------------------------------------------------------------------- *)

let KP4_MATRIX_TAC s =
  let addr = parse_term(Printf.sprintf
    "word_add bot (word (%d + 512 * (4 * r + j))):int64" 11128) in
  SUBGOAL_THEN
   `!r j n. r < 4 /\ j < 4 /\ n < 256
            ==> &0 <= mlkem_sample_ntt (APPEND rho [word j; word r]) n /\
                mlkem_sample_ntt (APPEND rho [word j; word r]) n < &3329`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC MLKEM_SAMPLE_NTT_REJ_BOUND THEN
    EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r j n. r < 4 /\ j < 4 /\ n < 256
            ==> ival((AM:num->int16)(1024 * r + 256 * j + n)) =
                mlkem_sample_ntt (APPEND rho [word j; word r]) n`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    INDCPA_GHOST_SPEC_TAC "AM" `1024 * r + 256 * j + n` THEN
    MP_TAC(SPECL [addr; s; `APPEND (rho:byte list) [word j; word r]`;
                  `k:num`; `n:num`]
                 MLKEM_NATIVE_SAMPLE_COEFF) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    MATCH_MP_TAC READ16_OFFSET_EQ THEN ARITH_TAC;
    ALL_TAC];;

let KP4_AM_INST r j =
  let th = SPECL [mk_small_numeral r; mk_small_numeral j]
    (ASSUME `!r j n. r < 4 /\ j < 4 /\ n < 256
                     ==> ival((AM:num->int16)(1024 * r + 256 * j + n)) =
                         mlkem_sample_ntt (APPEND rho [word j; word r]) n`) in
  CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES; ADD_ASSOC] THENC
            NUM_REDUCE_CONV) th;;

let KP4_PT_GOAL = `!r p. r < 4 /\ p < 128
            ==> (ival((PT:num->int16)(256 * r + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p + 1) *
                   ival((MC:num->int16)(384 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p) *
                   ival((SH:num->int16)(768 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(MC(256 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(SH(512 + 2 * p))) +
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
                 ((mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p + 1) *
                   ival(SH(768 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p) *
                   ival(SH(768 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
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

let KP4_AM_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 4096 ==> abs(ival((AM:num->int16) m)) <= &2 pow 12`
  (LABEL_TAC "ambound") THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`1024`; `4`; `m:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `1024 * 4 = 4096`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:num`; `q:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`256`; `4`; `q:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 4 = 1024`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(INT_ARITH
     `&0 <= x /\ x < &3329 ==> abs(x:int) <= &2 pow 12`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC];;

let KP4_BASEMUL_DEFS =
  [basemul4_even; basemul4_odd; pmul_acc4; pmull_acc4; pmull];;

let KP4_PT_TAC =
  INDCPA_GHOST_TAC "PT" 7032 1024 "s117" THEN
  SUBGOAL_THEN KP4_PT_GOAL ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THENL
     (map (fun r -> INDCPA_BASEMULK_ROW_TAC 4 "PT" (7032 + 512 * r)
                     "ambound" (map (KP4_AM_INST r) [0;1;2;3])
                     KP4_BASEMUL_DEFS) [0;1;2;3]);
    ALL_TAC];;

let KP4_RHO_HALVES_TAC =
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check (fun th ->
    can (term_match [] (subst [INDCPA_SP 3896,`a:int64`]
      `read (memory :> bytes(a,32)) s = num_of_bytelist rho`))
      (concl th))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC;;

let KP4_RHO_TAC s =
  MP_TAC(SPECL [`word_add pk (word 1536):int64`; `num_of_bytelist rho`;
                mk_var(s,`:x86state`)] GENMAT_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `rho:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

let KP4_FINAL_TAC =
  REWRITE_TAC[ARITH_RULE `1568 = 1536 + 32`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`d:byte list`; `rho:byte list`; `sigma:byte list`;
                `SH:num->int16`; `EH:num->int16`; `MC:num->int16`;
                `PT:num->int16`; `PT2:num->int16`; `TR:num->int16`;
                `SR:num->int16`] KPKE_KEYGEN_K4_RESULT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `FST(mlkem_g(APPEND d [word 4])) = rho`);
                  GSYM(ASSUME `SND(mlkem_g(APPEND d [word 4])) = sigma`);
                  PAIR];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    SIMP_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The seed d is 32 bytes at coins, and the public key of *)
(* 1568 bytes at pk and the secret key of 1536 bytes at sk are those of      *)
(* kpke_keygen mlkem1024 d in common/fips203.ml. The theorem assumes that    *)
(* SampleNTT terminates for each entry of the matrix, which means that the   *)
(* output of SHAKE128 for it has 256 fields < q, as for                      *)
(* mlkem1024_gen_matrix, and that the stack does not contain address 0. The  *)
(* stack is the 19416 bytes below the return address, for up to 31 bytes for *)
(* the alignment, the 15616 bytes of the pushes and the buffers and the 3768 *)
(* used by the callees below them. The matrix is generated without           *)
(* transposition, so the theorem for mlkem1024_gen_matrix is specialized to  *)
(* that case. The fourth outputs of the two calls of                         *)
(* mlkem1024_poly_getnoise_eta1_4x, for s and for e, are buffers in the      *)
(* stack frame, which are not null since the stack does not contain address  *)
(* 0. The products with the rows of the matrix are computed in a loop, which *)
(* the simulation unrolls, the comparisons of the pointers in the frame      *)
(* deciding its branch (INDCPA_PTR_TAC).                                     *)
(* ------------------------------------------------------------------------- *)

let KP4_FRAME = (19416,0,3768,15616);;

let KP4_CALL th =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,REWRITE_RULE[ALL] th);;

let KP4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `sk:int64`; `coins:int64`; `d:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 19416 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  UNDISCH_TAC
   `!i j. i < 4 /\ j < 4
          ==> mlkem_samplentt_terminates
               (APPEND (FST(mlkem_g(APPEND d [word 4])))
                       [word j; word i])` THEN
  ABBREV_TAC `rho = FST(mlkem_g(APPEND d [word 4]))` THEN
  ABBREV_TAC `sigma = SND(mlkem_g(APPEND d [word 4]))` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`4`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN `LENGTH(rho:byte list) = 32 /\ LENGTH(sigma:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rho"; "sigma"] THEN REWRITE_TAC[LENGTH_MLKEM_G];
    ALL_TAC];;

let KP4_SETUP_TAC =
  INDCPA_BOT_TAC KP4_FRAME [4984; 7032; 19368] THEN
  INDCPA_FRAME_TAC
   ["memory :> bytes(pk:int64,1568)"; "memory :> bytes(sk:int64,1536)"]
   KP4_FRAME THEN
  INDCPA_NONOV_TAC 19384
   [`pk:int64,1568`; `sk:int64,1536`; `coins:int64,32`;
    `word pc:int64,0x82a0`; `word_add stackpointer (word 19416):int64,8`] THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   ["rbx_init",`RBX`; "rbp_init",`RBP`; "r12_init",`R12`;
    "r13_init",`R13`; "r14_init",`R14`; "r15_init",`R15`];;

let KP4_MAIN_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = KP4_CALL in
  ENSURES_INIT_TAC "s0" THEN INDCPA_YMM_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(coins,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN

  (*** The input to SHA3-512 and the call ***)

  X86_STEPS_TAC KP4_EXEC (1--2) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KP4_EXEC (3--16) THEN INDCPA_NORM_TAC THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KP4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (17--28) THEN
  INDCPA_NORM_TAC THEN KP4_INPUT_TAC `s28:x86state` THEN
  X86_STEPS_TAC KP4_EXEC [29] THEN
  call MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `APPEND d [word 4]:byte list`] @
    post) 30 THEN
  INDCPA_NORM_TAC THEN KP4_G_TAC THEN

  (*** The matrix ***)

  X86_STEPS_TAC KP4_EXEC (31--36) THEN INDCPA_NORM_TAC THEN
  call (INDCPA_GEN_MATRIX_SPEC
         MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
         `word 0:int64`)
   ([`read RDI s`; `read RSI s`; `rho:byte list`; `k:num`] @ post) 37 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_GHOST_TAC "AM" 11128 4096 "s37" THEN
  KP4_MATRIX_TAC `s37:x86state` THEN

  (*** The noise, s and e from two calls with four outputs ***)

  X86_STEPS_TAC KP4_EXEC (38--48) THEN INDCPA_NORM_TAC THEN
  INDCPA_NONZERO_TAC 19424 10616 THEN
  call MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
     `sigma:byte list`; `read R9 s`; `word 1:int64`; `word 2:int64`;
     `word 3:int64`] @ post) 49 THEN
  INDCPA_NORM_TAC THEN INDCPA_NOISE_TAC "S0" 9080 4 "sigma" "word j" "s49"
  THEN INDCPA_DISCARD_LETS_TAC THEN
  X86_STEPS_TAC KP4_EXEC (50--64) THEN INDCPA_NORM_TAC THEN
  INDCPA_NONZERO_TAC 19424 6520 THEN
  call MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
     `sigma:byte list`; `read R9 s`; `word 5:int64`; `word 6:int64`;
     `word 7:int64`] @ post) 65 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_NOISE_TAC "E0" 4984 4 "sigma" "word(4 + j)" "s65" THEN
  INDCPA_DISCARD_LETS_TAC THEN

  (*** The NTTs and the multiplication cache ***)

  X86_STEPS_TAC KP4_EXEC (66--68) THEN
  call MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `S0:num->int16`] @ post) 69 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_NTT_TAC "SH" 9080 4 "S0" "sigma" "word j" "s69" THEN
  X86_STEPS_TAC KP4_EXEC (70--72) THEN
  call MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `E0:num->int16`] @ post) 73 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_NTT_TAC "EH" 4984 4 "E0" "sigma" "word(4 + j)"
    "s73" THEN
  X86_STEPS_TAC KP4_EXEC (74--76) THEN
  call
   MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `SH:num->int16`] @ post) 77 THEN
  INDCPA_NORM_TAC THEN INDCPA_MULCACHE_TAC "MC" 3960 4 "SH" "s77" THEN

  (*** The matrix-vector product, one row per iteration of the loop ***)

  MAP_EVERY (fun r ->
    let a = (11128 + 2048 * r,"AM",1024 * r)
    and y = (9080,"SH") and t = (3960,"MC") in
    X86_STEPS_TAC KP4_EXEC ((78 + 10 * r)--(84 + 10 * r)) THEN
    INDCPA_NORM_TAC THEN
    INDCPA_BASEMULK_PRE_TAC 4 a y t ("s"^string_of_int(84 + 10 * r)) THEN
    call MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
     (INDCPA_BASEMULK_ARGS 4 ("AM",1024 * r) "SH" "MC") (85 + 10 * r)
    THEN INDCPA_BASEMULK_DROP_PRE_TAC 4 a y t THEN INDCPA_NORM_TAC THEN
    X86_STEPS_TAC KP4_EXEC [86 + 10 * r] THEN INDCPA_PTR_TAC THEN
    X86_STEPS_TAC KP4_EXEC [87 + 10 * r])
   (0--3) THEN
  KP4_AM_BOUND_TAC THEN KP4_PT_TAC THEN

  (*** Montgomery form, adding the noise, the reductions ***)

  X86_STEPS_TAC KP4_EXEC (118--119) THEN
  call MLKEM_NATIVE_POLYVEC_TOMONT_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `PT:num->int16`] @ post) 120 THEN
  INDCPA_NORM_TAC THEN INDCPA_TOMONT_TAC "PT2" 7032 1024 "PT" "s120" THEN
  X86_STEPS_TAC KP4_EXEC (121--124) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `PT2:num->int16`; `EH:num->int16`] @ post)
   125 THEN
  X86_STEPS_TAC KP4_EXEC (126--127) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`;
     `\i. word_add ((PT2:num->int16) i) ((EH:num->int16) i)`] @ post) 128 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_REDUCE_TAC "TR" 7032 1024
    "word_add ((PT2:num->int16) i) ((EH:num->int16) i)" "s128" THEN
  X86_STEPS_TAC KP4_EXEC (129--130) THEN
  call MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `SH:num->int16`] @ post) 131 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_REDUCE_TAC "SR" 9080 1024 "(SH:num->int16) i" "s131" THEN

  (*** The encodings of the keys, and rho at the end of the public key ***)

  X86_STEPS_TAC KP4_EXEC (132--134) THEN INDCPA_NORM_TAC THEN
  INDCPA_TOBYTES_PRE_TAC "SR" 9080 1024 "s134" THEN
  call MLKEM_NATIVE_POLYVEC_TOBYTES_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `list_of_seq (SR:num->int16) 1024`] @
    post) 135 THEN
  INDCPA_TOBYTES_POST_TAC "SR" 1024 `\i. ival((SH:num->int16) i)` THEN
  X86_STEPS_TAC KP4_EXEC (136--139) THEN INDCPA_NORM_TAC THEN
  INDCPA_TOBYTES_PRE_TAC "TR" 7032 1024 "s139" THEN
  call MLKEM_NATIVE_POLYVEC_TOBYTES_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `list_of_seq (TR:num->int16) 1024`] @
    post) 140 THEN
  INDCPA_TOBYTES_POST_TAC "TR" 1024
    `\i. ival(word_add ((PT2:num->int16) i) ((EH:num->int16) i))` THEN
  KP4_RHO_HALVES_TAC THEN INDCPA_YMMS_TAC "s140" [3; 4] THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KP4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (141--148) THEN
  KP4_RHO_TAC "s148" THEN

  (*** Zeroing the buffers and the seeds, the return ***)

  X86_STEPS_TAC KP4_EXEC (149--183) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KP4_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  time prove
 (`!pk sk coins (d:byte list) pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH d = 32 /\
    (!i j. i < 4 /\ j < 4
           ==> mlkem_samplentt_terminates
                (APPEND (FST(mlkem_g(APPEND d [word 4])))
                        [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 19416),19424) /\
    PAIRWISE nonoverlapping
     [(pk,1568); (sk,1536); (word_sub stackpointer (word 19416),19424)] /\
    ALLPAIRS nonoverlapping
     [(pk,1568); (sk,1536); (word_sub stackpointer (word 19416),19424)]
     [(coins,32); (word pc,0x82a0)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x1110) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [pk; sk; coins] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(coins,32)) s = num_of_bytelist d)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              read (memory :> bytes(pk,1568)) s =
              num_of_bytelist(FST(kpke_keygen mlkem1024 d)) /\
              read (memory :> bytes(sk,1536)) s =
              num_of_bytelist(SND(kpke_keygen mlkem1024 d)) /\
              C_RETURN s = word 0)
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(pk,1568); memory :> bytes(sk,1536);
            memory :> bytes(word_sub stackpointer (word 19416),19416)])`,
  KP4_INTRO_TAC THEN KP4_SETUP_TAC THEN KP4_MAIN_TAC);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend only on the      *)
(* addresses and on rho, the seed of the matrix, which is part of the public *)
(* key, through the samples of SampleNTT: they are given as a function of    *)
(* rho, which is the first half of the result of SHA3-512, given by its      *)
(* combined theorem, and the theorem also states that rho is the end of the  *)
(* public key. At the end the frame variables are expanded in the events by  *)
(* INDCPA_UNBOT_TAC, since they are not arguments of f_events.               *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let KP4_SAFE_ALLOWED =
  [`pc:num`; `pk:int64`; `sk:int64`; `coins:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `rho:byte list`; `bot:int64`];;

let KP4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,KP4_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      (`e:(uarch_event)list`::ilist @
       [`pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`])
      n THENL
     [EXISTS_E2_TAC (ref KP4_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KP4_SAFE_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (INDCPA_GEN_MATRIX_SAFE_SPEC
     MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE `word 0:int64`)
   "H_GM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC
   MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE
   "H_GETNOISE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_SHA3" THEN
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_NTT";
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_MULCACHE";
    MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_BASEMUL";
    MLKEM_NATIVE_POLYVEC_TOMONT_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_TOMONT";
    MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_ADD";
    MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_REDUCE";
    MLKEM_NATIVE_POLYVEC_TOBYTES_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_TOBYTES"] THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `pk:int64`; `sk:int64`; `coins:int64`;
    `d:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 19416 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  UNDISCH_TAC
   `!i j. i < 4 /\ j < 4
          ==> mlkem_samplentt_terminates
               (APPEND (FST(mlkem_g(APPEND d [word 4])))
                       [word j; word i])` THEN
  ABBREV_TAC `rho = FST(mlkem_g(APPEND d [word 4]))` THEN
  ABBREV_TAC `sigma = SND(mlkem_g(APPEND d [word 4]))` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`4`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN `LENGTH(rho:byte list) = 32 /\ LENGTH(sigma:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rho"; "sigma"] THEN REWRITE_TAC[LENGTH_MLKEM_G];
    ALL_TAC];;

let KP4_SAFE_MAIN_TAC =
  let call = KP4_SAFE_CALL_TAC in
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  INDCPA_YMM_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(coins,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  X86_STEPS_TAC KP4_EXEC (1--2) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KP4_EXEC (3--16) THEN INDCPA_NORM_TAC THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KP4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (17--28) THEN
  INDCPA_NORM_TAC THEN KP4_INPUT_TAC `s28:x86state` THEN
  X86_STEPS_TAC KP4_EXEC [29] THEN
  call "H_SHA3"
   [`read RDI s`; `read RSI s`; `APPEND d [word 4]:byte list`; `33`] 30 THEN
  INDCPA_NORM_TAC THEN
  KP4_G_TAC THEN
  X86_STEPS_TAC KP4_EXEC (31--36) THEN INDCPA_NORM_TAC THEN
  call "H_GM" [`read RDI s`; `read RSI s`; `rho:byte list`; `k:num`] 37 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP4_EXEC (38--48) THEN INDCPA_NORM_TAC THEN
  INDCPA_NONZERO_TAC 19424 10616 THEN
  call "H_GETNOISE"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`] 49
  THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP4_EXEC (50--64) THEN INDCPA_NORM_TAC THEN
  INDCPA_NONZERO_TAC 19424 6520 THEN
  call "H_GETNOISE"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`] 65
  THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP4_EXEC (66--68) THEN
  call "H_NTT" [`read RDI s`] 69 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP4_EXEC (70--72) THEN
  call "H_NTT" [`read RDI s`] 73 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP4_EXEC (74--76) THEN
  call "H_MULCACHE" [`read RDI s`; `read RSI s`] 77 THEN INDCPA_NORM_TAC THEN
  MAP_EVERY (fun r ->
    X86_STEPS_TAC KP4_EXEC ((78 + 10 * r)--(84 + 10 * r)) THEN
    INDCPA_NORM_TAC THEN
    call "H_BASEMUL"
     [`read RSI s`; `read RDX s`; `read RCX s`; `read RDI s`]
     (85 + 10 * r) THEN INDCPA_NORM_TAC THEN
    X86_STEPS_TAC KP4_EXEC [86 + 10 * r] THEN INDCPA_PTR_TAC THEN
    X86_STEPS_TAC KP4_EXEC [87 + 10 * r])
   (0--3) THEN
  X86_STEPS_TAC KP4_EXEC (118--119) THEN
  call "H_TOMONT" [`read RDI s`] 120 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP4_EXEC (121--124) THEN INDCPA_NORM_TAC THEN
  call "H_ADD" [`read RDI s`; `read RSI s`] 125 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP4_EXEC (126--127) THEN INDCPA_NORM_TAC THEN
  call "H_REDUCE" [`read RDI s`] 128 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP4_EXEC (129--130) THEN
  call "H_REDUCE" [`read RDI s`] 131 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP4_EXEC (132--134) THEN INDCPA_NORM_TAC THEN
  call "H_TOBYTES" [`read RDI s`; `read RSI s`] 135 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP4_EXEC (136--139) THEN INDCPA_NORM_TAC THEN
  call "H_TOBYTES" [`read RDI s`; `read RSI s`] 140 THEN INDCPA_NORM_TAC THEN
  KP4_RHO_HALVES_TAC THEN INDCPA_YMMS_TAC "s140" [3; 4] THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KP4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (141--148) THEN
  KP4_RHO_TAC "s148" THEN
  X86_STEPS_TAC KP4_EXEC (149--183) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
   forall e pk sk coins (d:byte list) pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH d = 32 /\
    (!i j. i < 4 /\ j < 4
           ==> mlkem_samplentt_terminates
                (APPEND (FST(mlkem_g(APPEND d [word 4])))
                        [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 19416),19424) /\
    PAIRWISE nonoverlapping
     [(pk,1568); (sk,1536); (word_sub stackpointer (word 19416),19424)] /\
    ALLPAIRS nonoverlapping
     [(pk,1568); (sk,1536); (word_sub stackpointer (word 19416),19424)]
     [(coins,32); (word pc,0x82a0)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x1110) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [pk; sk; coins] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(coins,32)) s = num_of_bytelist d /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              C_RETURN s = word 0 /\
              read (memory :> bytes(word_add pk (word 1536),32)) s =
              num_of_bytelist(FST(mlkem_g(APPEND d [word 4]))) /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events pk sk coins pc
                        (word_sub stackpointer (word 19416)) returnaddress
                        (FST(mlkem_g(APPEND d [word 4]))) /\
                 memaccess_inbounds e2
                  [coins,32; pk,1568; sk,1536;
                   word_sub stackpointer (word 19416),19424;
                   word(pc + 0x8070),48; word(pc + 0x80c0),192;
                   word(pc + 0x81a0),256]
                  [pk,1568; sk,1536;
                   word_sub stackpointer (word 19416),19416]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(pk,1568); memory :> bytes(sk,1536);
            memory :> bytes(word_sub stackpointer (word 19416),19416)])`,
  KP4_SAFE_INTRO_TAC THEN KP4_SETUP_TAC THEN KP4_SAFE_MAIN_TAC);;
