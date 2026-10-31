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
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0xeb0, using   *)
(* the theorems for mlkem1024_polyvec_decompress_du,                         *)
(* mlkem_poly_decompress_d5, mlkem1024_polyvec_frombytes,                    *)
(* mlkem1024_polyvec_ntt, mlkem1024_polyvec_mulcache_compute,                *)
(* mlkem1024_polyvec_basemul_acc_montgomery_cached,                          *)
(* mlkem_poly_invntt_tomont, mlkem_poly_sub, mlkem_poly_reduce and           *)
(* mlkem_poly_tomsg in the image, and the contract for memset.               *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_polyvec_decompress_du_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_decompress_d5_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_frombytes_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_ntt_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_mulcache_compute_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_basemul_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_invntt_tomont_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_sub_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_reduce_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_tomsg_gcc12_O2.ml";;
needs "arm/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image:

    eb0: mov     x12, #0x1860
    eb4: sub     sp, sp, x12
    eb8: adrp    x3, 1f000 <mlk_zetas+0x18c80>
    ebc: ldr     x3, [x3, #4088]
    ec0: stp     x19, x20, [sp]
    ec4: add     x19, sp, #0x5f
    ec8: and     x19, x19, #0xffffffffffffffe0
    ecc: stp     x21, x22, [sp, #16]
    ed0: mov     x22, x2
    ed4: mov     x2, #0x1600
    ed8: stp     x23, x24, [sp, #32]
    edc: add     x21, x19, x2
    ee0: add     x20, x19, #0x800
    ee4: str     x30, [sp, #48]
    ee8: mov     x24, x0
    eec: mov     x23, x1
    ef0: mov     x0, x20
    ef4: ldr     x2, [x3]
    ef8: str     x2, [sp, #6232]
    efc: mov     x2, #0x0
    f00: bl      1730 <mlkem1024_polyvec_decompress_du>
    f04: add     x1, x23, #0x580
    f08: mov     x0, x21
    f0c: bl      20b0 <mlkem_poly_decompress_d5>
    f10: add     x23, x19, #0x1, lsl #12
    f14: mov     x1, x22
    f18: mov     x0, x19
    f1c: bl      17b0 <mlkem1024_polyvec_frombytes>
    f20: mov     x0, x20
    f24: bl      17f0 <mlkem1024_polyvec_ntt>
    f28: mov     x3, #0x1400
    f2c: mov     x1, x20
    f30: add     x22, x19, x3
    f34: mov     x0, x23
    f38: bl      1900 <mlkem1024_polyvec_mulcache_compute>
    f3c: mov     x3, x23
    f40: mov     x2, x20
    f44: mov     x1, x19
    f48: mov     x0, x22
    f4c: bl      1850 <mlkem1024_polyvec_basemul_acc_montgomery_cached>
    f50: mov     x0, x22
    f54: bl      4394 <mlkem_poly_invntt_tomont>
    f58: mov     x1, x22
    f5c: mov     x0, x21
    f60: bl      4210 <mlkem_poly_sub>
    f64: mov     x0, x21
    f68: bl      4190 <mlkem_poly_reduce>
    f6c: mov     x1, x21
    f70: mov     x0, x24
    f74: bl      2340 <mlkem_poly_tomsg>
    f78: mov     x0, x23
    f7c: mov     x2, #0x400
    f80: mov     w1, #0x0
    f84: bl      840 <memset@plt>
    f88: mov     x2, #0x200
    f8c: mov     x0, x22
    f90: mov     w1, #0x0
    f94: bl      840 <memset@plt>
    f98: mov     x2, #0x200
    f9c: mov     x0, x21
    fa0: mov     w1, #0x0
    fa4: bl      840 <memset@plt>
    fa8: mov     x2, #0x800
    fac: mov     x0, x19
    fb0: mov     w1, #0x0
    fb4: bl      840 <memset@plt>
    fb8: mov     x2, #0x800
    fbc: mov     x0, x20
    fc0: mov     w1, #0x0
    fc4: bl      840 <memset@plt>
    fc8: adrp    x0, 1f000 <mlk_zetas+0x18c80>
    fcc: ldr     x0, [x0, #4088]
    fd0: ldr     x2, [sp, #6232]
    fd4: ldr     x1, [x0]
    fd8: subs    x2, x2, x1
    fdc: mov     x1, #0x0
    fe0: b.ne    1004 <mlkem1024_indcpa_dec+0x154>
    fe4: ldp     x19, x20, [sp]
    fe8: mov     w0, #0x0
    fec: ldp     x21, x22, [sp, #16]
    ff0: mov     x12, #0x1860
    ff4: ldp     x23, x24, [sp, #32]
    ff8: ldr     x30, [sp, #48]
    ffc: add     sp, sp, x12
    1000: ret
    1004: bl      830 <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_INDCPA_DEC_K4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x840,0x850; 0xeb0,0x1008];;

let DE4_EXEC = MLKEM_NATIVE_INDCPA_DEC_K4_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The decryption in FIPS 203 in terms of the values computed by the code:   *)
(* the decompressed u and v, the 12-bit fields of the decryption key as      *)
(* decoded (which may be >= q), the NTT of u and its multiplication cache,   *)
(* the product with s in Montgomery form, its inverse NTT, and the result    *)
(* after the subtraction from v and the reduction, whose compression is the  *)
(* message.                                                                  *)
(* ------------------------------------------------------------------------- *)

let KPKE_DECRYPT_K4_RESULT = prove
 (`!dk ct (UD:num->int16) (VD:num->int16) (SS:num->int16) (UH:num->int16)
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
          ==> SS i = word((num_of_bytelist dk DIV 2 EXP (12 * i)) MOD
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
               ((ival(SS(768 + 2 * p + 1)) * ival(MC(384 + p)) +
                 ival(SS(768 + 2 * p)) * ival(UH(768 + 2 * p))) +
                (ival(SS(512 + 2 * p + 1)) * ival(MC(256 + p)) +
                 ival(SS(512 + 2 * p)) * ival(UH(512 + 2 * p))) +
                (ival(SS(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p))) +
                (ival(SS(2 * p + 1)) * ival(MC p) +
                 ival(SS(2 * p)) * ival(UH(2 * p))))) (mod &3329) /\
              (ival(WP(2 * p + 1)) ==
               &169 *
               ((ival(SS(768 + 2 * p + 1)) * ival(UH(768 + 2 * p)) +
                 ival(SS(768 + 2 * p)) * ival(UH(768 + 2 * p + 1))) +
                (ival(SS(512 + 2 * p + 1)) * ival(UH(512 + 2 * p)) +
                 ival(SS(512 + 2 * p)) * ival(UH(512 + 2 * p + 1))) +
                (ival(SS(256 + 2 * p + 1)) * ival(UH(256 + 2 * p)) +
                 ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p + 1))) +
                (ival(SS(2 * p + 1)) * ival(UH(2 * p)) +
                 ival(SS(2 * p)) * ival(UH(2 * p + 1))))) (mod &3329)) /\
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
              ==> (ival((SS:num->int16)(256 * j' + x)) ==
                   mlkem_decode 12 dk (256 * j' + x)) (mod &3329)`
     ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC TT_DECODE_CONG THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `j' < 4` THEN UNDISCH_TAC `x < 256` THEN ARITH_TAC;
       ALL_TAC])
    THENL
     [MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 dk (256 * j' + n)`;
        `\j' n. ival((SS:num->int16)(256 * j' + n))`;
        `\j' n. ival((UH:num->int16)(256 * j' + n))`;
        `\j'. ival((MC:num->int16)(128 * j' + p))`;
        `\j'. mlkem_ntt (mlkem_poly
                (\j''. mlkem_decompress 11
                        (mlkem_decode 11 ct (256 * j' + j''))))`;
        `ival((WP:num->int16)(2 * p))`; `p:num`] BASEMUL4_ROW_EVEN);
      MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 dk (256 * j' + n)`;
        `\j' n. ival((SS:num->int16)(256 * j' + n))`;
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
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16. The first 1408 bytes of the ciphertext are the compressed u and    *)
(* its last 160 the compressed v. After the calls that decompress and decode *)
(* them, the results are named by ghosts with their values as given by the   *)
(* postconditions, and after the NTT of u, by a ghost with the congruence    *)
(* and the bound of the postcondition.                                       *)
(* ------------------------------------------------------------------------- *)

let DE4_ALIGNED_16_32 = prove
 (`(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`,
  CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`x:int64`; `4`] (CONJUNCT1 WORD_AND_MASK_WORD));
    MP_TAC(ISPECL [`x:int64`; `5`] (CONJUNCT1 WORD_AND_MASK_WORD))] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16`; ARITH_RULE `x MOD 32 < 32`;
           ARITH_RULE `x < 16 ==> x < 2 EXP 64`;
           ARITH_RULE `x < 32 ==> x < 2 EXP 64`]);;

let DE4_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 127)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 96 else 112))`,
  REWRITE_TAC[DE4_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let DE4_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` DE4_BUFFER_ADDRESS))
    else NO_TAC);;

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

let DE4_UD_TAC b =
  INDCPA_GHOST_TAC "UD" (b + 2048) 1024 "s22" THEN
  SUBGOAL_THEN
   `!i. i < 1024
        ==> (UD:num->int16) i =
            word((3329 * (num_of_bytelist ct DIV 2 EXP (11 * i)) MOD
                  2 EXP 11 + 1024) DIV 2048)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "UD" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s22:armstate` (frees(concl th)) && is_forall(concl th) &&
      can (find_term ((=) `num_of_bytelist ct MOD 2 EXP (8 * 1408)`))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC DIV_MOD_EXP_LOW THEN
    UNDISCH_TAC `i < 1024` THEN ARITH_TAC;
    ALL_TAC];;

let DE4_VD_TAC b =
  INDCPA_GHOST_TAC "VD" (b + 5632) 256 "s26" THEN
  SUBGOAL_THEN
   `!i. i < 256
        ==> (VD:num->int16) i =
            word((3329 * (num_of_bytelist(mlkem_slice 1408 160 ct) DIV
                          2 EXP (5 * i)) MOD 2 EXP 5 + 16) DIV 32)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "VD" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s26:armstate` (frees(concl th)) && is_forall(concl th) &&
      can (find_term ((=) `num_of_bytelist(mlkem_slice 1408 160 ct)`))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

let DE4_SS_TAC b =
  INDCPA_GHOST_TAC "SS" b 1024 "s31" THEN
  SUBGOAL_THEN
   `!i. i < 1024
        ==> (SS:num->int16) i =
            word((num_of_bytelist dk DIV 2 EXP (12 * i)) MOD 2 EXP 12)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "SS" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s31:armstate` (frees(concl th)) && is_forall(concl th) &&
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
  SUBGOAL_THEN `!m. m < 1024 ==> abs(ival((SS:num->int16) m)) <= &2 pow 12`
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

let DE4_UH_TAC b =
  let st = `s34:armstate` and srct = `UD:num->int16` in
  INDCPA_GHOST_TAC "UH" (b + 2048) 1024 "s34" THEN
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
            ((ival((SS:num->int16)(768 + 2 * p + 1)) *
              ival((MC:num->int16)(384 + p)) +
              ival(SS(768 + 2 * p)) * ival((UH:num->int16)(768 + 2 * p))) +
             (ival(SS(512 + 2 * p + 1)) * ival(MC(256 + p)) +
              ival(SS(512 + 2 * p)) * ival(UH(512 + 2 * p))) +
             (ival(SS(256 + 2 * p + 1)) * ival(MC(128 + p)) +
              ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p))) +
             (ival(SS(2 * p + 1)) * ival(MC p) +
              ival(SS(2 * p)) * ival(UH(2 * p))))) (mod &3329) /\
           (ival(WP(2 * p + 1)) ==
            &169 *
            ((ival(SS(768 + 2 * p + 1)) * ival(UH(768 + 2 * p)) +
              ival(SS(768 + 2 * p)) * ival(UH(768 + 2 * p + 1))) +
             (ival(SS(512 + 2 * p + 1)) * ival(UH(512 + 2 * p)) +
              ival(SS(512 + 2 * p)) * ival(UH(512 + 2 * p + 1))) +
             (ival(SS(256 + 2 * p + 1)) * ival(UH(256 + 2 * p)) +
              ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p + 1))) +
             (ival(SS(2 * p + 1)) * ival(UH(2 * p)) +
              ival(SS(2 * p)) * ival(UH(2 * p + 1))))) (mod &3329)`;;

let DE4_WP_TAC b =
  INDCPA_GHOST_TAC "WP" (b + 5120) 256 "s46" THEN
  SUBGOAL_THEN DE4_WP_GOAL ASSUME_TAC THENL
   [INDCPA_BASEMULK_ROW_TAC 4 "WP" (b + 5120) "ssbound" [] DE4_BASEMUL_DEFS;
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
                `VD:num->int16`; `SS:num->int16`; `UH:num->int16`;
                `MC:num->int16`; `WP:num->int16`; `WI:num->int16`;
                `VR:num->int16`] KPKE_DECRYPT_K4_RESULT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
           REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
    SIMP_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* The callees. The theorems with hypotheses of the form ALL P l are used    *)
(* with them as conjunctions.                                                *)
(* ------------------------------------------------------------------------- *)

let LOCAL_POLYVEC_DECOMPRESS_DU_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,DE4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_DECOMPRESS_D5_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,DE4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_FROMBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,DE4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_NTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,DE4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_MULCACHE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,DE4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   );;

let LOCAL_BASEMUL_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,DE4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_INVNTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,DE4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_SUB_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,DE4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_SUB_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,DE4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_TOMSG_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,DE4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset. The ciphertext ct of *)
(* 1568 bytes is at c and the decryption key dk of 1536 bytes at sk, and the *)
(* message of 32 bytes written at m is kpke_decrypt mlkem1024 dk ct in       *)
(* common/fips203.ml, for any dk (FIPS 203 decodes s modulo q, while the     *)
(* code multiplies by the 12-bit fields, which are congruent). The stack is  *)
(* the 6240 bytes of the function and the 32 used by its callees below them. *)
(* The proof is by cases on whether the stack pointer is a multiple of 32,   *)
(* which gives the address b of the buffers, at offsets 0 (s), 2048 (u),     *)
(* 4096 (the multiplication cache), 5120 (the product) and 5632 (v).         *)
(* ------------------------------------------------------------------------- *)

let DE4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`m:int64`; `c:int64`; `sk:int64`; `dk:byte list`; `ct:byte list`;
    `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 6272 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 6272):int64)` THEN
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
     (parse_term("X"^string_of_int n))) (19--28);;

let DE4_CASE_TAC b =
  let st n = "s"^string_of_int n in
  ENSURES_INIT_TAC "s0" THEN DE4_CT_TAC THEN

  (*** The setup, the ciphertext and the secret key ***)

  ARM_STEPS_TAC DE4_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC DE4_EXEC (4--7) THEN DE4_BUFFER_TAC THEN
  ARM_STEPS_TAC DE4_EXEC (8--21) THEN
  LOCAL_POLYVEC_DECOMPRESS_DU_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist ct MOD 2 EXP (8 * 1408)`;
    `pc:num`; `read SP s`; `read X30 s`] 22 THEN
  DE4_UD_TAC b THEN
  ARM_STEPS_TAC DE4_EXEC (23--25) THEN
  LOCAL_POLY_DECOMPRESS_D5_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist(mlkem_slice 1408 160 ct)`;
    `pc:num`; `read X30 s`] 26 THEN
  DE4_VD_TAC b THEN
  ARM_STEPS_TAC DE4_EXEC (27--30) THEN
  LOCAL_POLYVEC_FROMBYTES_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist dk`; `pc:num`; `read SP s`;
    `read X30 s`] 31 THEN
  DE4_SS_TAC b THEN

  (*** The NTT of u and its multiplication cache, the product with s ***)

  DE4_UD_BOUND_TAC THEN
  ARM_STEPS_TAC DE4_EXEC (32--33) THEN
  LOCAL_POLYVEC_NTT_TAC
   [`read X0 s`; `UD:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 34 THEN
  DE4_UH_TAC b THEN
  ARM_STEPS_TAC DE4_EXEC (35--39) THEN
  LOCAL_POLYVEC_MULCACHE_TAC
   [`read X0 s`; `read X1 s`; `UH:num->int16`; `pc:num`; `read SP s`;
    `read X30 s`] 40 THEN
  INDCPA_MULCACHE_TAC "MC" (b + 4096) 4 "UH" (st 40) THEN
  ARM_STEPS_TAC DE4_EXEC (41--45) THEN
  INDCPA_BASEMULK_PRE_TAC 4 (b,"SS",0) (b + 2048,"UH") (b + 4096,"MC")
    (st 45) THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 4 ("SS",0) "UH" "MC") 46 THEN
  INDCPA_BASEMULK_DROP_PRE_TAC 4 (b,"SS",0) (b + 2048,"UH")
    (b + 4096,"MC") THEN
  DE4_SS_BOUND_TAC THEN DE4_WP_TAC b THEN

  (*** The inverse NTT, the subtraction from v, the reduction ***)

  ARM_STEPS_TAC DE4_EXEC (47--48) THEN
  LOCAL_POLY_INVNTT_TAC
   [`read X0 s`; `WP:num->int16`; `pc:num`; `read SP s`; `read X30 s`]
   49 THEN
  INDCPA_INVNTT1_TAC "WI" (b + 5120) "WP" (st 49) THEN
  ARM_STEPS_TAC DE4_EXEC (50--52) THEN
  LOCAL_POLY_SUB_TAC
   [`read X0 s`; `read X1 s`; `VD:num->int16`; `WI:num->int16`; `pc:num`;
    `read X30 s`] 53 THEN
  ARM_STEPS_TAC DE4_EXEC (54--55) THEN
  LOCAL_POLY_REDUCE_TAC
   [`read X0 s`; `\i. word_sub ((VD:num->int16) i) ((WI:num->int16) i)`;
    `pc:num`; `read X30 s`] 56 THEN
  INDCPA_REDUCE_TAC "VR" (b + 5632) 256
    "word_sub ((VD:num->int16) i) ((WI:num->int16) i)" (st 56) THEN

  (*** The message ***)

  ARM_STEPS_TAC DE4_EXEC (57--59) THEN
  LOCAL_POLY_TOMSG_TAC
   [`read X0 s`; `read X1 s`; `VR:num->int16`; `pc:num`; `read X30 s`]
   60 THEN
  DE4_TOMSG_POST_TAC THEN

  (*** Zeroing the buffers, the stack guard, the return ***)

  INDCPA_MEMSET_LABEL_TAC THEN
  INDCPA_MEMSETS_TAC DE4_EXEC
   [61,64; 70,73; 79,82; 88,91; 97,100] THEN
  ARM_STEPS_TAC DE4_EXEC (106--106) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC DE4_EXEC (107--120) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DE4_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_DEC_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!m c sk (dk:byte list) (ct:byte list) guard mf ea el ev pc
    stackpointer returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        LENGTH dk = 1536 /\ LENGTH ct = 1568 /\
        nonoverlapping (m,32) (word_sub stackpointer (word 6272),6272) /\
        nonoverlapping (c,1568) (word pc,0x6480) /\
        nonoverlapping (sk,1536) (word pc,0x6480) /\
        ALLPAIRS nonoverlapping
         [(m,32); (word_sub stackpointer (word 6272),6272)]
         [(c,1568); (sk,1536); (word pc,0x6480); (word(pc + 0x1fff8),8);
          (guard,8); (word(pc + 0x1ffe8),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0xeb0) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [m; c; sk] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(c,1568)) s = num_of_bytelist ct /\
                  read (memory :> bytes(sk,1536)) s = num_of_bytelist dk)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(m,32)) s =
                  num_of_bytelist(kpke_decrypt mlkem1024 dk ct) /\
                  C_RETURN s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(m,32);
                memory :> bytes(word_sub stackpointer (word 6272),6272)])`,
  DE4_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [DE4_CASE_TAC 96; DE4_CASE_TAC 112]);;
