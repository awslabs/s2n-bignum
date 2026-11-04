(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The key generation of K-PKE for ML-KEM-512 (FIPS 203 Algorithm 13). This  *)
(* is the code for mlkem512_indcpa_keypair_derand from mlkem-native's        *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md). It hashes the 32-byte seed d followed by the     *)
(* byte 2 with SHA3-512 into the seeds rho and sigma, generates the matrix   *)
(* in NTT form from rho, samples the secret s and the error e from sigma     *)
(* (with eta = 3) and transforms them, computes t = A s + e in the NTT       *)
(* domain, and writes the encoding of t followed by rho as the public key    *)
(* and the encoding of s as the secret key, zeroing its buffers. It is       *)
(* verified in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml),      *)
(* where it is at address 0x4820, using the theorems for mlkem_sha3_512,     *)
(* mlkem512_gen_matrix, mlkem512_poly_getnoise_eta1_4x,                      *)
(* mlkem512_polyvec_ntt, mlkem512_polyvec_mulcache_compute,                  *)
(* mlkem512_polyvec_basemul_acc_montgomery_cached, mlkem512_polyvec_tomont,  *)
(* mlkem512_polyvec_add, mlkem512_polyvec_reduce and                         *)
(* mlkem512_polyvec_tobytes in the image.                                    *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_sha3_512_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_gen_matrix_k2_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_poly_getnoise_eta1_4x_k2_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_ntt_k2_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_mulcache_compute_k2_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_basemul_k2_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_tomont_k2_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_add_k2_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_reduce_k2_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_tobytes_k2_gcc12_O2.ml";;
needs "x86/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image:

    4820: lea    r10,[rsp+0x8]
    4825: and    rsp,0xffffffffffffffe0
    4829: push   QWORD PTR [r10-0x8]
    482d: push   rbp
    482e: mov    rbp,rsp
    4831: push   r15
    4833: push   r14
    4835: lea    rax,[rbp-0x1670]
    483c: lea    r11,[rbp-0x16b0]
    4843: push   r13
    4845: lea    r15,[rbp-0x830]
    484c: lea    r13,[rbp-0x1430]
    4853: push   r12
    4855: lea    r14,[rbp-0x1630]
    485c: lea    r12,[rbp-0x1030]
    4863: push   r10
    4865: push   rbx
    4866: mov    rbx,rax
    4869: sub    rsp,0x16a0
    4870: movdqu xmm1,XMMWORD PTR [rdx]
    4874: movdqu xmm2,XMMWORD PTR [rdx+0x10]
    4879: mov    QWORD PTR [rbp-0x16b8],rdi
    4880: mov    QWORD PTR [rbp-0x16c0],rsi
    4887: mov    rdi,rax
    488a: mov    rsi,r11
    488d: mov    edx,0x21
    4892: mov    QWORD PTR [rbp-0x16d0],r11
    4899: movaps XMMWORD PTR [rbp-0x16b0],xmm1
    48a0: movaps XMMWORD PTR [rbp-0x16a0],xmm2
    48a7: mov    BYTE PTR [rbp-0x1690],0x2
    48ae: call   3570 <mlkem_sha3_512>
    48b3: xor    edx,edx
    48b5: mov    rsi,rbx
    48b8: mov    rdi,r15
    48bb: mov    QWORD PTR [rbp-0x16c8],rbx
    48c2: lea    rbx,[rbp-0xc30]
    48c9: call   4770 <mlkem512_gen_matrix>
    48ce: sub    rsp,0x8
    48d2: xor    r9d,r9d
    48d5: mov    rdx,r13
    48d8: push   0x3
    48da: lea    r8,[rbp-0x1650]
    48e1: mov    rdi,rbx
    48e4: lea    rcx,[rbp-0x1230]
    48eb: push   0x2
    48ed: lea    rsi,[rbp-0xa30]
    48f4: push   0x1
    48f6: call   5cd0 <mlkem512_poly_getnoise_eta1_4x>
    48fb: add    rsp,0x20
    48ff: mov    rdi,rbx
    4902: call   5b10 <mlkem512_polyvec_ntt>
    4907: mov    rdi,r13
    490a: call   5b10 <mlkem512_polyvec_ntt>
    490f: mov    rsi,rbx
    4912: mov    rdi,r14
    4915: call   5c30 <mlkem512_polyvec_mulcache_compute>
    491a: mov    rcx,r14
    491d: mov    rdx,rbx
    4920: mov    rsi,r15
    4923: mov    rdi,r12
    4926: call   5b50 <mlkem512_polyvec_basemul_acc_montgomery_cached>
    492b: mov    rcx,r14
    492e: mov    rdx,rbx
    4931: lea    rsi,[rbp-0x430]
    4938: lea    rdi,[rbp-0xe30]
    493f: call   5b50 <mlkem512_polyvec_basemul_acc_montgomery_cached>
    4944: mov    rdi,r12
    4947: call   5cb0 <mlkem512_polyvec_tomont>
    494c: mov    rsi,r13
    494f: mov    rdi,r12
    4952: call   5c80 <mlkem512_polyvec_add>
    4957: mov    rdi,r12
    495a: call   5c60 <mlkem512_polyvec_reduce>
    495f: mov    rdi,rbx
    4962: call   5c60 <mlkem512_polyvec_reduce>
    4967: mov    rdi,QWORD PTR [rbp-0x16c0]
    496e: mov    rsi,rbx
    4971: call   5ab0 <mlkem512_polyvec_tobytes>
    4976: mov    rdi,QWORD PTR [rbp-0x16b8]
    497d: mov    rsi,r12
    4980: call   5ab0 <mlkem512_polyvec_tobytes>
    4985: xor    eax,eax
    4987: mov    rdi,r14
    498a: mov    ecx,0x40
    498f: mov    rdx,QWORD PTR [rbp-0x16b8]
    4996: movdqa xmm3,XMMWORD PTR [rbp-0x1670]
    499e: rep    stos QWORD PTR es:[rdi],rax
    49a1: movdqa xmm4,XMMWORD PTR [rbp-0x1660]
    49a9: movups XMMWORD PTR [rdx+0x300],xmm3
    49b0: movups XMMWORD PTR [rdx+0x310],xmm4
    49b7: mov    ecx,0x80
    49bc: mov    rdi,rbx
    49bf: rep    stos QWORD PTR es:[rdi],rax
    49c2: mov    ecx,0x80
    49c7: mov    rdi,r12
    49ca: rep    stos QWORD PTR es:[rdi],rax
    49cd: mov    ecx,0x80
    49d2: mov    rdi,r13
    49d5: rep    stos QWORD PTR es:[rdi],rax
    49d8: mov    ecx,0x100
    49dd: mov    rdi,r15
    49e0: rep    stos QWORD PTR es:[rdi],rax
    49e3: pxor   xmm0,xmm0
    49e7: mov    BYTE PTR [rbp-0x1690],0x0
    49ee: mov    r11,QWORD PTR [rbp-0x16d0]
    49f5: movaps XMMWORD PTR [rbp-0x16b0],xmm0
    49fc: movaps XMMWORD PTR [rbp-0x16a0],xmm0
    4a03: mov    rax,QWORD PTR [rbp-0x16c8]
    4a0a: movaps XMMWORD PTR [rbp-0x1670],xmm0
    4a11: movaps XMMWORD PTR [rbp-0x1660],xmm0
    4a18: movaps XMMWORD PTR [rbp-0x1650],xmm0
    4a1f: movaps XMMWORD PTR [rbp-0x1640],xmm0
    4a26: lea    rsp,[rbp-0x30]
    4a2a: xor    eax,eax
    4a2c: pop    rbx
    4a2d: pop    r10
    4a2f: pop    r12
    4a31: pop    r13
    4a33: pop    r14
    4a35: pop    r15
    4a37: pop    rbp
    4a38: lea    rsp,[r10-0x8]
    4a3c: ret
 ***)

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K2_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x4820,0x4a3d];;

let KP2_EXEC = MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K2_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The key generation in FIPS 203 in terms of the coefficients computed by   *)
(* the code: those of the NTTs of s and e, those of the multiplication       *)
(* cache, those of the matrix-vector product in Montgomery form, and those   *)
(* of the final results after Montgomery conversion, addition and reduction. *)
(* The two lemmas on single coefficients relate the computation of the code  *)
(* to MultiplyNTTs and the addition of e in the NTT domain, for even and odd *)
(* coefficients. This is as for AArch64.                                     *)
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
(* The buffers are aligned to 32 bytes within the stack frame, by AND with   *)
(* -32 before the pushes of a copy of the return address, RBP, R15, R14,     *)
(* R13, R12, R10 and RBX, with RBP as a frame pointer, and their addresses   *)
(* are offsets from the frame variable bot of INDCPA_BOT_TAC, the bottom of  *)
(* the stacks of the callees 3736 bytes below them: the input of SHA3-512 at *)
(* bot + 3768, its output (rho and sigma) at bot + 3832, the multiplication  *)
(* cache of s at bot + 3896, e at bot + 4408, t at bot + 5432, s at          *)
(* bot + 6456 and the matrix at bot + 7480, with pointers to some of them    *)
(* saved below the input. The callees mlkem512_polyvec_tomont and            *)
(* mlkem512_polyvec_add need t and e to be aligned to 16 bytes, and the SSE  *)
(* moves relative to RBP, which is bot + 9576, need that to be aligned too.  *)
(* The input to SHA3-512 is the seed copied as two 128-bit words by legacy   *)
(* SSE moves through XMM1 and XMM2, which keep the upper halves of YMM1 and  *)
(* YMM2, so their initial values are named by INDCPA_YMM_TAC, and the byte 2 *)
(* (the parameter k); its output is the two seeds rho and sigma as in        *)
(* mlkem_g.                                                                  *)
(* ------------------------------------------------------------------------- *)

let KP2_INPUT = prove
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

let KP2_INPUT_TAC s =
  MP_TAC(SPECL [INDCPA_SP 3768; `d:byte list`; `2`; s] KP2_INPUT) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    STRIP_TAC];;

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

(* ------------------------------------------------------------------------- *)
(* The facts about the stages of the computation other than those given by   *)
(* the tactics in mlkem_native_indcpa.ml: the coefficients of the matrix as  *)
(* given by SampleNTT, the bounds on the inputs of the multiplications, the  *)
(* rows of the matrix-vector product, and rho in the public key, copied      *)
(* there through XMM3 and XMM4 after the last call, whose values there are   *)
(* named. This is as for AArch64.                                            *)
(* ------------------------------------------------------------------------- *)

let KP2_MATRIX_TAC s =
  let addr = parse_term(Printf.sprintf
    "word_add bot (word (%d + 512 * (2 * r + j))):int64" 7480) in
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

let KP2_PT_TAC =
  INDCPA_GHOST_TAC "PT" 5432 512 "s74" THEN
  SUBGOAL_THEN KP2_PT_GOAL ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THENL
     (map (fun r -> INDCPA_BASEMULK_ROW_TAC 2 "PT" (5432 + 512 * r)
                     "ambound" (map (KP2_AM_INST r) [0;1])
                     KP2_BASEMUL_DEFS) [0;1]);
    ALL_TAC];;

let KP2_RHO_HALVES_TAC =
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check (fun th ->
    can (term_match [] (subst [INDCPA_SP 3832,`a:int64`]
      `read (memory :> bytes(a,32)) s = num_of_bytelist rho`))
      (concl th))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC;;

let KP2_RHO_TAC s =
  MP_TAC(SPECL [`word_add pk (word 768):int64`; `num_of_bytelist rho`;
                mk_var(s,`:x86state`)] GENMAT_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `rho:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

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
(* Correctness proof. The seed d is 32 bytes at coins, and the public key of *)
(* 800 bytes at pk and the secret key of 768 bytes at sk are those of        *)
(* kpke_keygen mlkem512 d in common/fips203.ml. The theorem assumes that     *)
(* SampleNTT terminates for each entry of the matrix, which means that the   *)
(* output of SHAKE128 for it has 256 fields < q, as for mlkem512_gen_matrix, *)
(* and that the stack does not contain address 0. The stack is the 9624      *)
(* bytes below the return address, for up to 31 bytes for the alignment, the *)
(* 5856 bytes of the pushes and the buffers and the 3736 used by the callees *)
(* below them. The matrix is generated without transposition, so the theorem *)
(* for mlkem512_gen_matrix is specialized to that case. The four outputs of  *)
(* mlkem512_poly_getnoise_eta1_4x (s and e) are buffers in the stack frame,  *)
(* so the fourth is not null since the stack does not contain address 0.     *)
(* ------------------------------------------------------------------------- *)

let KP2_FRAME = (9624,0,3736,5856);;

let KP2_CALL th =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KP2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,REWRITE_RULE[ALL] th);;

let KP2_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `sk:int64`; `coins:int64`; `d:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 9624 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
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

let KP2_SETUP_TAC =
  INDCPA_BOT_TAC KP2_FRAME [4408; 5432; 9576] THEN
  INDCPA_FRAME_TAC
   ["memory :> bytes(pk:int64,800)"; "memory :> bytes(sk:int64,768)"]
   KP2_FRAME THEN
  INDCPA_NONOV_TAC 9592
   [`pk:int64,800`; `sk:int64,768`; `coins:int64,32`;
    `word pc:int64,0x82a0`; `word_add stackpointer (word 9624):int64,8`] THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   ["rbx_init",`RBX`; "rbp_init",`RBP`; "r12_init",`R12`;
    "r13_init",`R13`; "r14_init",`R14`; "r15_init",`R15`];;

let KP2_MAIN_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = KP2_CALL in
  ENSURES_INIT_TAC "s0" THEN INDCPA_YMM_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(coins,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN

  (*** The input to SHA3-512 and the call ***)

  X86_STEPS_TAC KP2_EXEC (1--2) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KP2_EXEC (3--19) THEN INDCPA_NORM_TAC THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KP2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (20--30) THEN
  INDCPA_NORM_TAC THEN KP2_INPUT_TAC `s30:x86state` THEN
  X86_STEPS_TAC KP2_EXEC [31] THEN
  call MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `APPEND d [word 2]:byte list`] @
    post) 32 THEN
  INDCPA_NORM_TAC THEN KP2_G_TAC THEN

  (*** The matrix ***)

  X86_STEPS_TAC KP2_EXEC (33--38) THEN INDCPA_NORM_TAC THEN
  call (INDCPA_GEN_MATRIX_SPEC
         MLKEM_NATIVE_GEN_MATRIX_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
         `word 0:int64`)
   ([`read RDI s`; `read RSI s`; `rho:byte list`; `k:num`] @ post) 39 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_GHOST_TAC "AM" 7480 1024 "s39" THEN
  KP2_MATRIX_TAC `s39:x86state` THEN

  (*** The noise, all from one call with four outputs ***)

  X86_STEPS_TAC KP2_EXEC (40--50) THEN INDCPA_NORM_TAC THEN
  INDCPA_NONZERO_TAC 9632 4920 THEN
  call MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
     `sigma:byte list`; `read R9 s`; `word 1:int64`; `word 2:int64`;
     `word 3:int64`] @ post) 51 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_NOISE_ETA_TAC 3 "S0" 6456 2 "sigma" "word j" "s51" THEN
  INDCPA_NOISE_ETA_TAC 3 "E0" 4408 2 "sigma" "word(2 + j)" "s51" THEN
  INDCPA_DISCARD_LETS_TAC THEN

  (*** The NTTs and the multiplication cache ***)

  X86_STEPS_TAC KP2_EXEC (52--54) THEN
  call MLKEM_NATIVE_POLYVEC_NTT_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `S0:num->int16`] @ post) 55 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_NTT_ETA_TAC 3 "SH" 6456 2 "S0" "sigma" "word j" "s55" THEN
  X86_STEPS_TAC KP2_EXEC (56--57) THEN
  call MLKEM_NATIVE_POLYVEC_NTT_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `E0:num->int16`] @ post) 58 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_NTT_ETA_TAC 3 "EH" 4408 2 "E0" "sigma" "word(2 + j)"
    "s58" THEN
  X86_STEPS_TAC KP2_EXEC (59--61) THEN
  call
   MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `SH:num->int16`] @ post) 62 THEN
  INDCPA_NORM_TAC THEN INDCPA_MULCACHE_TAC "MC" 3896 2 "SH" "s62" THEN

  (*** The matrix-vector product, one row per call ***)

  MAP_EVERY (fun (r,k0,k1) ->
    let a = (7480 + 1024 * r,"AM",512 * r)
    and y = (6456,"SH") and t = (3896,"MC") in
    X86_STEPS_TAC KP2_EXEC (k0--k1) THEN INDCPA_NORM_TAC THEN
    INDCPA_BASEMULK_PRE_TAC 2 a y t ("s"^string_of_int k1) THEN
    call MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
     (INDCPA_BASEMULK_ARGS 2 ("AM",512 * r) "SH" "MC") (k1 + 1) THEN
    INDCPA_BASEMULK_DROP_PRE_TAC 2 a y t THEN INDCPA_NORM_TAC)
   [0,63,67; 1,69,73] THEN
  KP2_AM_BOUND_TAC THEN KP2_PT_TAC THEN

  (*** Montgomery form, adding the noise, the reductions ***)

  X86_STEPS_TAC KP2_EXEC (75--76) THEN
  call MLKEM_NATIVE_POLYVEC_TOMONT_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `PT:num->int16`] @ post) 77 THEN
  INDCPA_NORM_TAC THEN INDCPA_TOMONT_TAC "PT2" 5432 512 "PT" "s77" THEN
  X86_STEPS_TAC KP2_EXEC (78--80) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLYVEC_ADD_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `PT2:num->int16`; `EH:num->int16`] @ post)
   81 THEN
  X86_STEPS_TAC KP2_EXEC (82--83) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`;
     `\i. word_add ((PT2:num->int16) i) ((EH:num->int16) i)`] @ post) 84 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_REDUCE_TAC "TR" 5432 512
    "word_add ((PT2:num->int16) i) ((EH:num->int16) i)" "s84" THEN
  X86_STEPS_TAC KP2_EXEC (85--86) THEN
  call MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `SH:num->int16`] @ post) 87 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_REDUCE_TAC "SR" 6456 512 "(SH:num->int16) i" "s87" THEN

  (*** The encodings of the keys, and rho at the end of the public key ***)

  X86_STEPS_TAC KP2_EXEC (88--90) THEN INDCPA_NORM_TAC THEN
  INDCPA_TOBYTES_PRE_TAC "SR" 6456 512 "s90" THEN
  call MLKEM_NATIVE_POLYVEC_TOBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `list_of_seq (SR:num->int16) 512`] @
    post) 91 THEN
  INDCPA_TOBYTES_POST_TAC "SR" 512 `\i. ival((SH:num->int16) i)` THEN
  X86_STEPS_TAC KP2_EXEC (92--94) THEN INDCPA_NORM_TAC THEN
  INDCPA_TOBYTES_PRE_TAC "TR" 5432 512 "s94" THEN
  call MLKEM_NATIVE_POLYVEC_TOBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `list_of_seq (TR:num->int16) 512`] @
    post) 95 THEN
  INDCPA_TOBYTES_POST_TAC "TR" 512
    `\i. ival(word_add ((PT2:num->int16) i) ((EH:num->int16) i))` THEN
  KP2_RHO_HALVES_TAC THEN INDCPA_YMMS_TAC "s95" [3; 4] THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KP2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (96--104) THEN
  KP2_RHO_TAC "s104" THEN

  (*** Zeroing the buffers and the seeds, the return ***)

  X86_STEPS_TAC KP2_EXEC (105--137) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KP2_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  time prove
 (`!pk sk coins (d:byte list) pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH d = 32 /\
    (!i j. i < 2 /\ j < 2
           ==> mlkem_samplentt_terminates
                (APPEND (FST(mlkem_g(APPEND d [word 2])))
                        [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 9624),9632) /\
    PAIRWISE nonoverlapping
     [(pk,800); (sk,768); (word_sub stackpointer (word 9624),9632)] /\
    ALLPAIRS nonoverlapping
     [(pk,800); (sk,768); (word_sub stackpointer (word 9624),9632)]
     [(coins,32); (word pc,0x82a0)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x4820) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [pk; sk; coins] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(coins,32)) s = num_of_bytelist d)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              read (memory :> bytes(pk,800)) s =
              num_of_bytelist(FST(kpke_keygen mlkem512 d)) /\
              read (memory :> bytes(sk,768)) s =
              num_of_bytelist(SND(kpke_keygen mlkem512 d)) /\
              C_RETURN s = word 0)
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(pk,800); memory :> bytes(sk,768);
            memory :> bytes(word_sub stackpointer (word 9624),9624)])`,
  KP2_INTRO_TAC THEN KP2_SETUP_TAC THEN KP2_MAIN_TAC);;

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

let KP2_SAFE_ALLOWED =
  [`pc:num`; `pk:int64`; `sk:int64`; `coins:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `rho:byte list`; `bot:int64`];;

let KP2_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,KP2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      (`e:(uarch_event)list`::ilist @
       [`pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`])
      n THENL
     [EXISTS_E2_TAC (ref KP2_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KP2_SAFE_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (INDCPA_GEN_MATRIX_SAFE_SPEC
     MLKEM_NATIVE_GEN_MATRIX_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE `word 0:int64`)
   "H_GM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC
   MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE
   "H_GETNOISE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_SHA3" THEN
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [MLKEM_NATIVE_POLYVEC_NTT_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_NTT";
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_MULCACHE";
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_BASEMUL";
    MLKEM_NATIVE_POLYVEC_TOMONT_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_TOMONT";
    MLKEM_NATIVE_POLYVEC_ADD_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_ADD";
    MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_REDUCE";
    MLKEM_NATIVE_POLYVEC_TOBYTES_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_TOBYTES"] THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `pk:int64`; `sk:int64`; `coins:int64`;
    `d:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 9624 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
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

let KP2_SAFE_MAIN_TAC =
  let call = KP2_SAFE_CALL_TAC in
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  INDCPA_YMM_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(coins,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  X86_STEPS_TAC KP2_EXEC (1--2) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KP2_EXEC (3--19) THEN INDCPA_NORM_TAC THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KP2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (20--30) THEN
  INDCPA_NORM_TAC THEN KP2_INPUT_TAC `s30:x86state` THEN
  X86_STEPS_TAC KP2_EXEC [31] THEN
  call "H_SHA3"
   [`read RDI s`; `read RSI s`; `APPEND d [word 2]:byte list`; `33`] 32 THEN
  INDCPA_NORM_TAC THEN
  KP2_G_TAC THEN
  X86_STEPS_TAC KP2_EXEC (33--38) THEN INDCPA_NORM_TAC THEN
  call "H_GM" [`read RDI s`; `read RSI s`; `rho:byte list`; `k:num`] 39 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP2_EXEC (40--50) THEN INDCPA_NORM_TAC THEN
  INDCPA_NONZERO_TAC 9632 4920 THEN
  call "H_GETNOISE"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`] 51
  THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP2_EXEC (52--54) THEN
  call "H_NTT" [`read RDI s`] 55 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP2_EXEC (56--57) THEN
  call "H_NTT" [`read RDI s`] 58 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP2_EXEC (59--61) THEN
  call "H_MULCACHE" [`read RDI s`; `read RSI s`] 62 THEN INDCPA_NORM_TAC THEN
  MAP_EVERY (fun (k0,k1) ->
    X86_STEPS_TAC KP2_EXEC (k0--k1) THEN INDCPA_NORM_TAC THEN
    call "H_BASEMUL"
     [`read RSI s`; `read RDX s`; `read RCX s`; `read RDI s`] (k1 + 1) THEN
    INDCPA_NORM_TAC)
   [63,67; 69,73] THEN
  X86_STEPS_TAC KP2_EXEC (75--76) THEN
  call "H_TOMONT" [`read RDI s`] 77 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP2_EXEC (78--80) THEN INDCPA_NORM_TAC THEN
  call "H_ADD" [`read RDI s`; `read RSI s`] 81 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP2_EXEC (82--83) THEN INDCPA_NORM_TAC THEN
  call "H_REDUCE" [`read RDI s`] 84 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP2_EXEC (85--86) THEN
  call "H_REDUCE" [`read RDI s`] 87 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP2_EXEC (88--90) THEN INDCPA_NORM_TAC THEN
  call "H_TOBYTES" [`read RDI s`; `read RSI s`] 91 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KP2_EXEC (92--94) THEN INDCPA_NORM_TAC THEN
  call "H_TOBYTES" [`read RDI s`; `read RSI s`] 95 THEN INDCPA_NORM_TAC THEN
  KP2_RHO_HALVES_TAC THEN INDCPA_YMMS_TAC "s95" [3; 4] THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KP2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (96--104) THEN
  KP2_RHO_TAC "s104" THEN
  X86_STEPS_TAC KP2_EXEC (105--137) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
   forall e pk sk coins (d:byte list) pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH d = 32 /\
    (!i j. i < 2 /\ j < 2
           ==> mlkem_samplentt_terminates
                (APPEND (FST(mlkem_g(APPEND d [word 2])))
                        [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 9624),9632) /\
    PAIRWISE nonoverlapping
     [(pk,800); (sk,768); (word_sub stackpointer (word 9624),9632)] /\
    ALLPAIRS nonoverlapping
     [(pk,800); (sk,768); (word_sub stackpointer (word 9624),9632)]
     [(coins,32); (word pc,0x82a0)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x4820) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [pk; sk; coins] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(coins,32)) s = num_of_bytelist d /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              C_RETURN s = word 0 /\
              read (memory :> bytes(word_add pk (word 768),32)) s =
              num_of_bytelist(FST(mlkem_g(APPEND d [word 2]))) /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events pk sk coins pc
                        (word_sub stackpointer (word 9624)) returnaddress
                        (FST(mlkem_g(APPEND d [word 2]))) /\
                 memaccess_inbounds e2
                  [coins,32; pk,800; sk,768;
                   word_sub stackpointer (word 9624),9632;
                   word(pc + 0x8070),48; word(pc + 0x80c0),192;
                   word(pc + 0x8180),2; word(pc + 0x81a0),256]
                  [pk,800; sk,768;
                   word_sub stackpointer (word 9624),9624]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(pk,800); memory :> bytes(sk,768);
            memory :> bytes(word_sub stackpointer (word 9624),9624)])`,
  KP2_SAFE_INTRO_TAC THEN KP2_SETUP_TAC THEN KP2_SAFE_MAIN_TAC);;
