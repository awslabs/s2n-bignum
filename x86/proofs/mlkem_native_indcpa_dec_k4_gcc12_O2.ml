(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decryption of K-PKE for ML-KEM-1024 (FIPS 203 Algorithm 15). This is  *)
(* the code for mlkem1024_indcpa_dec from mlkem-native's portable C          *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* It decompresses u and v from the ciphertext, decodes the secret vector s  *)
(* in the NTT domain from the decryption key, and writes the compression     *)
(* with d = 1 of w = v - NTT^-1(s^T NTT(u)) as the message, zeroing its      *)
(* buffers. It is verified in the whole image (see                           *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x1690, using  *)
(* the theorems for mlkem1024_polyvec_decompress_du,                         *)
(* mlkem_poly_decompress_d5, mlkem1024_polyvec_frombytes,                    *)
(* mlkem1024_polyvec_ntt, mlkem1024_polyvec_mulcache_compute,                *)
(* mlkem1024_polyvec_basemul_acc_montgomery_cached,                          *)
(* mlkem_poly_invntt_tomont, mlkem_poly_sub, mlkem_poly_reduce and           *)
(* mlkem_poly_tomsg in the image.                                            *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_polyvec_decompress_du_k4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_poly_decompress_d5_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_frombytes_k4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_ntt_k4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_polyvec_mulcache_compute_k4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_basemul_k4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_poly_invntt_tomont_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_poly_sub_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_poly_reduce_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_poly_tomsg_gcc12_O2.ml";;
needs "x86/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image:

    1690: push   rbp
    1691: mov    rbp,rsp
    1694: push   r15
    1696: push   r14
    1698: push   r13
    169a: mov    r13,rdx
    169d: push   r12
    169f: mov    r12,rsi
    16a2: push   rbx
    16a3: and    rsp,0xffffffffffffffe0
    16a7: sub    rsp,0x1820
    16ae: lea    rbx,[rsp+0x820]
    16b6: mov    QWORD PTR [rsp+0x18],rdi
    16bb: lea    r15,[rsp+0x1020]
    16c3: mov    rdi,rbx
    16c6: lea    r14,[rsp+0x420]
    16ce: call   1f80 <mlkem1024_polyvec_decompress_du>
    16d3: lea    rsi,[r12+0x580]
    16db: lea    r12,[rsp+0x20]
    16e0: mov    rdi,r12
    16e3: call   2de0 <mlkem_poly_decompress_d5>
    16e8: mov    rsi,r13
    16eb: mov    rdi,r15
    16ee: lea    r13,[rsp+0x220]
    16f6: call   2000 <mlkem1024_polyvec_frombytes>
    16fb: mov    rdi,rbx
    16fe: call   2040 <mlkem1024_polyvec_ntt>
    1703: mov    rsi,rbx
    1706: mov    rdi,r14
    1709: call   2190 <mlkem1024_polyvec_mulcache_compute>
    170e: mov    rcx,r14
    1711: mov    rdx,rbx
    1714: mov    rsi,r15
    1717: mov    rdi,r13
    171a: call   20a0 <mlkem1024_polyvec_basemul_acc_montgomery_cached>
    171f: mov    rdi,r13
    1722: call   5860 <mlkem_poly_invntt_tomont>
    1727: mov    rsi,r13
    172a: mov    rdi,r12
    172d: call   56e0 <mlkem_poly_sub>
    1732: mov    rdi,r12
    1735: call   5660 <mlkem_poly_reduce>
    173a: mov    rdi,QWORD PTR [rsp+0x18]
    173f: mov    rsi,r12
    1742: call   3260 <mlkem_poly_tomsg>
    1747: xor    eax,eax
    1749: mov    rdi,r14
    174c: mov    ecx,0x80
    1751: rep    stos QWORD PTR es:[rdi],rax
    1754: mov    ecx,0x40
    1759: mov    rdi,r13
    175c: rep    stos QWORD PTR es:[rdi],rax
    175f: mov    ecx,0x40
    1764: mov    rdi,r12
    1767: rep    stos QWORD PTR es:[rdi],rax
    176a: mov    ecx,0x100
    176f: mov    rdi,r15
    1772: rep    stos QWORD PTR es:[rdi],rax
    1775: mov    ecx,0x100
    177a: mov    rdi,rbx
    177d: rep    stos QWORD PTR es:[rdi],rax
    1780: lea    rsp,[rbp-0x28]
    1784: pop    rbx
    1785: pop    r12
    1787: pop    r13
    1789: pop    r14
    178b: pop    r15
    178d: pop    rbp
    178e: ret
 ***)

let MLKEM_NATIVE_INDCPA_DEC_K4_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x1690,0x178f];;

let DE4_EXEC = MLKEM_NATIVE_INDCPA_DEC_K4_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The decryption in FIPS 203 in terms of the values computed by the code:   *)
(* the decompressed u and v, the 12-bit fields of the decryption key as      *)
(* decoded (which may be >= q), the NTT of u and its multiplication cache,   *)
(* the product with s in Montgomery form, its inverse NTT, and the result    *)
(* after the subtraction from v and the reduction, whose compression is the  *)
(* message. This is as for AArch64, with the decoded secret vector named SV. *)
(* ------------------------------------------------------------------------- *)

let KPKE_DECRYPT_K4_RESULT = prove
 (`!dk ct (UD:num->int16) (VD:num->int16) (SV:num->int16) (UH:num->int16)
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
          ==> SV i = word((num_of_bytelist dk DIV 2 EXP (12 * i)) MOD
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
               ((ival(SV(768 + 2 * p + 1)) * ival(MC(384 + p)) +
                 ival(SV(768 + 2 * p)) * ival(UH(768 + 2 * p))) +
                (ival(SV(512 + 2 * p + 1)) * ival(MC(256 + p)) +
                 ival(SV(512 + 2 * p)) * ival(UH(512 + 2 * p))) +
                (ival(SV(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(SV(256 + 2 * p)) * ival(UH(256 + 2 * p))) +
                (ival(SV(2 * p + 1)) * ival(MC p) +
                 ival(SV(2 * p)) * ival(UH(2 * p))))) (mod &3329) /\
              (ival(WP(2 * p + 1)) ==
               &169 *
               ((ival(SV(768 + 2 * p + 1)) * ival(UH(768 + 2 * p)) +
                 ival(SV(768 + 2 * p)) * ival(UH(768 + 2 * p + 1))) +
                (ival(SV(512 + 2 * p + 1)) * ival(UH(512 + 2 * p)) +
                 ival(SV(512 + 2 * p)) * ival(UH(512 + 2 * p + 1))) +
                (ival(SV(256 + 2 * p + 1)) * ival(UH(256 + 2 * p)) +
                 ival(SV(256 + 2 * p)) * ival(UH(256 + 2 * p + 1))) +
                (ival(SV(2 * p + 1)) * ival(UH(2 * p)) +
                 ival(SV(2 * p)) * ival(UH(2 * p + 1))))) (mod &3329)) /\
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
              ==> (ival((SV:num->int16)(256 * j' + x)) ==
                   mlkem_decode 12 dk (256 * j' + x)) (mod &3329)`
     ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC TT_DECODE_CONG THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `j' < 4` THEN UNDISCH_TAC `x < 256` THEN ARITH_TAC;
       ALL_TAC])
    THENL
     [MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 dk (256 * j' + n)`;
        `\j' n. ival((SV:num->int16)(256 * j' + n))`;
        `\j' n. ival((UH:num->int16)(256 * j' + n))`;
        `\j'. ival((MC:num->int16)(128 * j' + p))`;
        `\j'. mlkem_ntt (mlkem_poly
                (\j''. mlkem_decompress 11
                        (mlkem_decode 11 ct (256 * j' + j''))))`;
        `ival((WP:num->int16)(2 * p))`; `p:num`] BASEMUL4_ROW_EVEN);
      MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 dk (256 * j' + n)`;
        `\j' n. ival((SV:num->int16)(256 * j' + n))`;
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
(* The buffers are aligned to 32 bytes within the stack frame, by AND with   *)
(* -32 after the pushes of RBP, R15, R14, R13, R12 and RBX, with RBP as a    *)
(* frame pointer, and their addresses are offsets from the frame variable    *)
(* bot of INDCPA_BOT_TAC, the bottom of the stacks of the callees 76 bytes   *)
(* below them: v at bot + 108, the product at bot + 620, the multiplication  *)
(* cache at bot + 1132, u at bot + 2156 and s at bot + 4204, with the        *)
(* message pointer saved at bot + 100. The callees mlkem_poly_sub and        *)
(* mlkem1024_polyvec_decompress_du need some of them to be aligned to 16     *)
(* bytes. The first 1408 bytes of the ciphertext are the compressed u and    *)
(* its last 160 the compressed v. After the calls that decompress and decode *)
(* them, the results are named by ghosts with their values as given by the   *)
(* postconditions, and after the NTT of u, by a ghost with the congruence    *)
(* and the bound of the postcondition.                                       *)
(* ------------------------------------------------------------------------- *)

let DE4_CT_TAC =
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

let DE4_UD_TAC =
  INDCPA_GHOST_TAC "UD" 2156 1024 "s18" THEN
  SUBGOAL_THEN
   `!i. i < 1024
        ==> (UD:num->int16) i =
            word((3329 * (num_of_bytelist ct DIV 2 EXP (11 * i)) MOD
                  2 EXP 11 + 1024) DIV 2048)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "UD" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s18:x86state` (frees(concl th)) && is_forall(concl th) &&
      can (find_term ((=) `num_of_bytelist ct MOD 2 EXP (8 * 1408)`))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC DIV_MOD_EXP_LOW THEN
    UNDISCH_TAC `i < 1024` THEN ARITH_TAC;
    ALL_TAC];;

let DE4_VD_TAC =
  INDCPA_GHOST_TAC "VD" 108 256 "s23" THEN
  SUBGOAL_THEN
   `!i. i < 256
        ==> (VD:num->int16) i =
            word((3329 * (num_of_bytelist(mlkem_slice 1408 160 ct) DIV
                          2 EXP (5 * i)) MOD 2 EXP 5 + 16) DIV 32)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "VD" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s23:x86state` (frees(concl th)) && is_forall(concl th) &&
      can (find_term ((=) `num_of_bytelist(mlkem_slice 1408 160 ct)`))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

let DE4_SS_TAC =
  INDCPA_GHOST_TAC "SV" 4204 1024 "s28" THEN
  SUBGOAL_THEN
   `!i. i < 1024
        ==> (SV:num->int16) i =
            word((num_of_bytelist dk DIV 2 EXP (12 * i)) MOD 2 EXP 12)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "SV" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s28:x86state` (frees(concl th)) && is_forall(concl th) &&
      can (find_term ((=) `num_of_bytelist dk`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

let DE4_UD_BOUND_TAC =
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

let DE4_SS_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 1024 ==> abs(ival((SV:num->int16) m)) <= &2 pow 12`
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

let DE4_UH_TAC =
  let st = `s31:x86state` and srct = `UD:num->int16` in
  INDCPA_GHOST_TAC "UH" 2156 1024 "s31" THEN
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

(* ------------------------------------------------------------------------- *)
(* The product of s and the NTT of u, the message from the postcondition of  *)
(* mlkem_poly_tomsg, whose hypothesis that the coefficients are reduced      *)
(* follows from that of mlkem_poly_reduce, and the final combination.        *)
(* ------------------------------------------------------------------------- *)

let DE4_BASEMUL_DEFS =
  [basemul4_even; basemul4_odd; pmul_acc4; pmull_acc4; pmull];;

let DE4_WP_GOAL = `!p. p < 128
       ==> (ival((WP:num->int16)(2 * p)) ==
            &169 *
            ((ival((SV:num->int16)(768 + 2 * p + 1)) *
              ival((MC:num->int16)(384 + p)) +
              ival(SV(768 + 2 * p)) * ival((UH:num->int16)(768 + 2 * p))) +
             (ival(SV(512 + 2 * p + 1)) * ival(MC(256 + p)) +
              ival(SV(512 + 2 * p)) * ival(UH(512 + 2 * p))) +
             (ival(SV(256 + 2 * p + 1)) * ival(MC(128 + p)) +
              ival(SV(256 + 2 * p)) * ival(UH(256 + 2 * p))) +
             (ival(SV(2 * p + 1)) * ival(MC p) +
              ival(SV(2 * p)) * ival(UH(2 * p))))) (mod &3329) /\
           (ival(WP(2 * p + 1)) ==
            &169 *
            ((ival(SV(768 + 2 * p + 1)) * ival(UH(768 + 2 * p)) +
              ival(SV(768 + 2 * p)) * ival(UH(768 + 2 * p + 1))) +
             (ival(SV(512 + 2 * p + 1)) * ival(UH(512 + 2 * p)) +
              ival(SV(512 + 2 * p)) * ival(UH(512 + 2 * p + 1))) +
             (ival(SV(256 + 2 * p + 1)) * ival(UH(256 + 2 * p)) +
              ival(SV(256 + 2 * p)) * ival(UH(256 + 2 * p + 1))) +
             (ival(SV(2 * p + 1)) * ival(UH(2 * p)) +
              ival(SV(2 * p)) * ival(UH(2 * p + 1))))) (mod &3329)`;;

let DE4_WP_TAC =
  INDCPA_GHOST_TAC "WP" 620 256 "s41" THEN
  SUBGOAL_THEN DE4_WP_GOAL ASSUME_TAC THENL
   [INDCPA_BASEMULK_ROW_TAC 4 "WP" 620 "ssbound" [] DE4_BASEMUL_DEFS;
    ALL_TAC];;

let DE4_TOMSG_POST_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && mem `VR:num->int16` (frees(concl th)) &&
    INDCPA_HAS_CONST "nsum" (concl th))) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC VAL_LT_OF_IVAL_REM THEN
    EXISTS_TAC `ival(word_sub ((VD:num->int16) i) ((WI:num->int16) i))` THEN
    ASM_SIMP_TAC[];
    DISCH_TAC];;

let DE4_FINAL_TAC =
  MP_TAC(SPECL [`dk:byte list`; `ct:byte list`; `UD:num->int16`;
                `VD:num->int16`; `SV:num->int16`; `UH:num->int16`;
                `MC:num->int16`; `WP:num->int16`; `WI:num->int16`;
                `VR:num->int16`] KPKE_DECRYPT_K4_RESULT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
           REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
    SIMP_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The ciphertext ct of 1568 bytes is at c and the        *)
(* decryption key dk of 1536 bytes at sk, and the message of 32 bytes        *)
(* written at m is kpke_decrypt mlkem1024 dk ct in common/fips203.ml, for    *)
(* any dk (FIPS 203 decodes s modulo q, while the code multiplies by the     *)
(* 12-bit fields, which are congruent). The stack is the 6332 bytes below    *)
(* the return address, for the six saved registers, up to 31 bytes for the   *)
(* alignment, the 6176 bytes of the buffers and the 76 used by the callees   *)
(* below them.                                                               *)
(* ------------------------------------------------------------------------- *)

let DE4_FRAME = (6332,48,76,6176);;

let DE4_CALL th =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,DE4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,REWRITE_RULE[ALL] th);;

let DE4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`m:int64`; `c:int64`; `sk:int64`; `dk:byte list`; `ct:byte list`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 6332 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let DE4_SETUP_TAC =
  INDCPA_BOT_TAC DE4_FRAME [108; 620; 2156] THEN
  INDCPA_FRAME_TAC ["memory :> bytes(m:int64,32)"] DE4_FRAME THEN
  INDCPA_NONOV_TAC 6252
   [`c:int64,1568`; `sk:int64,1536`; `m:int64,32`; `word pc:int64,0x82a0`;
    `word_add stackpointer (word 6284):int64,56`] THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   ["rbx_init",`RBX`; "rbp_init",`RBP`; "r12_init",`R12`;
    "r13_init",`R13`; "r14_init",`R14`; "r15_init",`R15`];;

let DE4_MAIN_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  ENSURES_INIT_TAC "s0" THEN DE4_CT_TAC THEN

  (*** Decompressing u and v, decoding s ***)

  X86_STEPS_TAC DE4_EXEC (1--10) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC DE4_EXEC (11--17) THEN INDCPA_NORM_TAC THEN
  DE4_CALL
   MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`;
    `num_of_bytelist ct MOD 2 EXP (8 * 1408)`] @ post) 18 THEN
  INDCPA_NORM_TAC THEN DE4_UD_TAC THEN
  X86_STEPS_TAC DE4_EXEC (19--22) THEN
  DE4_CALL MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`;
    `num_of_bytelist(mlkem_slice 1408 160 ct)`] @ post) 23 THEN
  INDCPA_NORM_TAC THEN DE4_VD_TAC THEN
  X86_STEPS_TAC DE4_EXEC (24--27) THEN
  DE4_CALL MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `num_of_bytelist dk`] @ post) 28 THEN
  INDCPA_NORM_TAC THEN DE4_SS_TAC THEN DE4_UD_BOUND_TAC THEN

  (*** The NTT of u and its multiplication cache, the product with s ***)

  X86_STEPS_TAC DE4_EXEC (29--30) THEN
  DE4_CALL MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `UD:num->int16`] @ post) 31 THEN
  INDCPA_NORM_TAC THEN DE4_UH_TAC THEN
  X86_STEPS_TAC DE4_EXEC (32--34) THEN
  DE4_CALL
   MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `UH:num->int16`] @ post) 35 THEN
  INDCPA_NORM_TAC THEN INDCPA_MULCACHE_TAC "MC" 1132 4 "UH" "s35" THEN
  X86_STEPS_TAC DE4_EXEC (36--40) THEN
  INDCPA_BASEMULK_PRE_TAC 4 (4204,"SV",0) (2156,"UH") (1132,"MC") "s40"
  THEN
  DE4_CALL MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   (INDCPA_BASEMULK_ARGS 4 ("SV",0) "UH" "MC") 41 THEN
  INDCPA_BASEMULK_DROP_PRE_TAC 4 (4204,"SV",0) (2156,"UH") (1132,"MC")
  THEN INDCPA_NORM_TAC THEN DE4_SS_BOUND_TAC THEN DE4_WP_TAC THEN

  (*** The inverse NTT, the subtraction from v, the reduction ***)

  X86_STEPS_TAC DE4_EXEC (42--43) THEN
  DE4_CALL MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `WP:num->int16`] @ post) 44 THEN
  INDCPA_NORM_TAC THEN INDCPA_INVNTT1_TAC "WI" 620 "WP" "s44" THEN
  X86_STEPS_TAC DE4_EXEC (45--47) THEN
  DE4_CALL MLKEM_NATIVE_POLY_SUB_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `VD:num->int16`;
    `WI:num->int16`] @ post) 48 THEN
  INDCPA_NORM_TAC THEN X86_STEPS_TAC DE4_EXEC (49--50) THEN
  DE4_CALL MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`;
    `\i. word_sub ((VD:num->int16) i) ((WI:num->int16) i)`] @ post) 51 THEN
  INDCPA_NORM_TAC THEN
  INDCPA_REDUCE_TAC "VR" 108 256
    "word_sub ((VD:num->int16) i) ((WI:num->int16) i)" "s51" THEN

  (*** The message, zeroing the buffers and the return ***)

  X86_STEPS_TAC DE4_EXEC (52--54) THEN
  DE4_CALL MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `VR:num->int16`] @ post) 55 THEN
  DE4_TOMSG_POST_TAC THEN X86_STEPS_TAC DE4_EXEC (56--79) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DE4_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_DEC_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = time prove
 (`!m c sk (dk:byte list) (ct:byte list) pc stackpointer
    returnaddress.
    aligned 16 (word pc:int64) /\
    LENGTH dk = 1536 /\ LENGTH ct = 1568 /\
    nonoverlapping (m,32) (word_sub stackpointer (word 6332),6340) /\
    ALLPAIRS nonoverlapping
     [(m,32); (word_sub stackpointer (word 6332),6340)]
     [(c,1568); (sk,1536); (word pc,0x82a0)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x1690) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [m; c; sk] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(c,1568)) s = num_of_bytelist ct /\
              read (memory :> bytes(sk,1536)) s = num_of_bytelist dk)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              read (memory :> bytes(m,32)) s =
              num_of_bytelist(kpke_decrypt mlkem1024 dk ct) /\
              C_RETURN s = word 0)
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(m,32);
            memory :> bytes(word_sub stackpointer (word 6332),6332)])`,
  DE4_INTRO_TAC THEN DE4_SETUP_TAC THEN DE4_MAIN_TAC);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend only on the      *)
(* addresses of the arguments, the stack and the image, not on the           *)
(* ciphertext or the key. At the end the frame variables are expanded in     *)
(* them by INDCPA_UNBOT_TAC, since they are not arguments of f_events.       *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let DE4_SAFE_ALLOWED =
  [`pc:num`; `m:int64`; `c:int64`; `sk:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

let DE4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,DE4_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      (`e:(uarch_event)list`::ilist @
       [`pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`])
      n THENL
     [EXISTS_E2_TAC (ref DE4_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let DE4_SAFE_INTRO_TAC =
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_DECOMPRESS_DU";
    MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_DECOMPRESS_DV";
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_FROMBYTES";
    MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_NTT";
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_MULCACHE";
    MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_BASEMUL";
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_INVNTT";
    MLKEM_NATIVE_POLY_SUB_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_SUB";
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_REDUCE";
    MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_TOMSG"] THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `m:int64`; `c:int64`; `sk:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 6332 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let DE4_SAFE_MAIN_TAC =
  let call = DE4_SAFE_CALL_TAC in
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC DE4_EXEC (1--10) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC DE4_EXEC (11--17) THEN INDCPA_NORM_TAC THEN
  call "H_DECOMPRESS_DU" [`read RDI s`; `read RSI s`] 18 THEN
  INDCPA_NORM_TAC THEN X86_STEPS_TAC DE4_EXEC (19--22) THEN
  call "H_DECOMPRESS_DV" [`read RDI s`; `read RSI s`] 23 THEN
  INDCPA_NORM_TAC THEN X86_STEPS_TAC DE4_EXEC (24--27) THEN
  call "H_FROMBYTES" [`read RDI s`; `read RSI s`] 28 THEN
  INDCPA_NORM_TAC THEN X86_STEPS_TAC DE4_EXEC (29--30) THEN
  call "H_NTT" [`read RDI s`] 31 THEN
  INDCPA_NORM_TAC THEN X86_STEPS_TAC DE4_EXEC (32--34) THEN
  call "H_MULCACHE" [`read RDI s`; `read RSI s`] 35 THEN
  INDCPA_NORM_TAC THEN X86_STEPS_TAC DE4_EXEC (36--40) THEN
  call "H_BASEMUL"
   [`read RSI s`; `read RDX s`; `read RCX s`; `read RDI s`] 41 THEN
  INDCPA_NORM_TAC THEN X86_STEPS_TAC DE4_EXEC (42--43) THEN
  call "H_INVNTT" [`read RDI s`] 44 THEN
  INDCPA_NORM_TAC THEN X86_STEPS_TAC DE4_EXEC (45--47) THEN
  call "H_SUB" [`read RDI s`; `read RSI s`] 48 THEN
  INDCPA_NORM_TAC THEN X86_STEPS_TAC DE4_EXEC (49--50) THEN
  call "H_REDUCE" [`read RDI s`] 51 THEN
  INDCPA_NORM_TAC THEN X86_STEPS_TAC DE4_EXEC (52--54) THEN
  call "H_TOMSG" [`read RDI s`; `read RSI s`] 55 THEN
  INDCPA_NORM_TAC THEN X86_STEPS_TAC DE4_EXEC (56--79) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_DEC_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
   forall e m c sk pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    nonoverlapping (m,32) (word_sub stackpointer (word 6332),6340) /\
    ALLPAIRS nonoverlapping
     [(m,32); (word_sub stackpointer (word 6332),6340)]
     [(c,1568); (sk,1536); (word pc,0x82a0)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x1690) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [m; c; sk] s /\
              (read DF s <=> false) /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              C_RETURN s = word 0 /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events m c sk pc (word_sub stackpointer (word 6332))
                               returnaddress /\
                 memaccess_inbounds e2
                  [c,1568; sk,1536; m,32;
                   word_sub stackpointer (word 6332),6340;
                   word(pc + 0x8020),8; word(pc + 0x8050),16;
                   word(pc + 0x8060),16; word(pc + 0x8080),48;
                   word(pc + 0x81a0),256]
                  [m,32; word_sub stackpointer (word 6332),6332]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(m,32);
            memory :> bytes(word_sub stackpointer (word 6332),6332)])`,
  DE4_SAFE_INTRO_TAC THEN DE4_SETUP_TAC THEN DE4_SAFE_MAIN_TAC);;
