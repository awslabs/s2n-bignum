(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decryption of K-PKE for ML-KEM-512 (FIPS 203 Algorithm 15). This is   *)
(* the code for mlkem512_indcpa_dec from mlkem-native's portable C           *)
(* implementation compiled by gcc 12 with -O3 (see mlkem_native/README.md).  *)
(* It decompresses u and v from the ciphertext, decodes the secret vector s  *)
(* in the NTT domain from the decryption key, and writes the compression     *)
(* with d = 1 of w = v - NTT^-1(s^T NTT(u)) as the message, zeroing its      *)
(* buffers. It is verified in the whole image (see                           *)
(* libmlkem.ml), using the theorems for                                      *)
(* mlkem512_polyvec_decompress_du, mlkem_poly_decompress_d4,                 *)
(* mlkem512_polyvec_frombytes, mlkem512_polyvec_ntt,                         *)
(* mlkem512_polyvec_mulcache_compute,                                        *)
(* mlkem512_polyvec_basemul_acc_montgomery_cached, mlkem_poly_invntt_tomont, *)
(* mlkem_poly_sub, mlkem_poly_reduce and mlkem_poly_tomsg in the image, and  *)
(* the contract for memset.                                                  *)
(* At -O3 the code is the same, but the callees use more stack below the     *)
(* stack pointer (polyvec_frombytes and poly_tomsg 64 bytes, polyvec_ntt 48, *)
(* polyvec_mulcache_compute 48, poly_invntt_tomont 32), so this function and *)
(* its deepest callee use 3744 bytes below the stack pointer (3680 + 64),    *)
(* not 3712. The safety theorem lists the constant blocks that the -O3       *)
(* callees read, not the -O2 ones.                                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O3/polyvec_decompress_du_k2_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/poly_decompress_d4_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/polyvec_frombytes_k2_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/polyvec_ntt_k2_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/polyvec_mulcache_compute_k2_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/basemul_k2_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/poly_invntt_tomont_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/poly_sub_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/poly_reduce_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/poly_tomsg_proof.ml";;
needs "arm/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image:

    mlkem512_indcpa_dec:
        +0x0: sub     sp, sp, #0xe60
        +0x4: adrp    x3, <page>
        +0x8: ldr     x3, [x3, #4088]  // got_stack_chk_guard
        +0xc: stp     x19, x20, [sp]
       +0x10: add     x19, sp, #0x5f
       +0x14: and     x19, x19, #0xffffffffffffffe0
       +0x18: stp     x21, x22, [sp, #16]
       +0x1c: mov     x22, x2
       +0x20: add     x20, x19, #0x400
       +0x24: stp     x23, x24, [sp, #32]
       +0x28: add     x21, x19, #0xc00
       +0x2c: mov     x24, x0
       +0x30: str     x30, [sp, #48]
       +0x34: mov     x0, x20
       +0x38: mov     x23, x1
       +0x3c: ldr     x2, [x3]
       +0x40: str     x2, [sp, #3672]
       +0x44: mov     x2, #0x0
       +0x48: bl      <mlkem512_polyvec_decompress_du>
       +0x4c: add     x1, x23, #0x280
       +0x50: mov     x0, x21
       +0x54: bl      <mlkem_poly_decompress_d4>
       +0x58: add     x23, x19, #0x800
       +0x5c: mov     x1, x22
       +0x60: mov     x0, x19
       +0x64: bl      <mlkem512_polyvec_frombytes>
       +0x68: add     x22, x19, #0xa00
       +0x6c: mov     x0, x20
       +0x70: bl      <mlkem512_polyvec_ntt>
       +0x74: mov     x1, x20
       +0x78: mov     x0, x23
       +0x7c: bl      <mlkem512_polyvec_mulcache_compute>
       +0x80: mov     x3, x23
       +0x84: mov     x2, x20
       +0x88: mov     x1, x19
       +0x8c: mov     x0, x22
       +0x90: bl      <mlkem512_polyvec_basemul_acc_montgomery_cached>
       +0x94: mov     x0, x22
       +0x98: bl      <mlkem_poly_invntt_tomont>
       +0x9c: mov     x1, x22
       +0xa0: mov     x0, x21
       +0xa4: bl      <mlkem_poly_sub>
       +0xa8: mov     x0, x21
       +0xac: bl      <mlkem_poly_reduce>
       +0xb0: mov     x1, x21
       +0xb4: mov     x0, x24
       +0xb8: bl      <mlkem_poly_tomsg>
       +0xbc: mov     x0, x23
       +0xc0: mov     x2, #0x200
       +0xc4: mov     w1, #0x0
       +0xc8: bl      <memset@plt>
       +0xcc: mov     x2, #0x200
       +0xd0: mov     x0, x22
       +0xd4: mov     w1, #0x0
       +0xd8: bl      <memset@plt>
       +0xdc: mov     x2, #0x200
       +0xe0: mov     x0, x21
       +0xe4: mov     w1, #0x0
       +0xe8: bl      <memset@plt>
       +0xec: mov     x2, #0x400
       +0xf0: mov     x0, x19
       +0xf4: mov     w1, #0x0
       +0xf8: bl      <memset@plt>
       +0xfc: mov     x2, #0x400
      +0x100: mov     x0, x20
      +0x104: mov     w1, #0x0
      +0x108: bl      <memset@plt>
      +0x10c: adrp    x0, <page>
      +0x110: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x114: ldr     x2, [sp, #3672]
      +0x118: ldr     x1, [x0]
      +0x11c: subs    x2, x2, x1
      +0x120: mov     x1, #0x0
      +0x124: b.ne    <mlkem512_indcpa_dec+0x144>
      +0x128: ldp     x19, x20, [sp]
      +0x12c: mov     w0, #0x0
      +0x130: ldp     x21, x22, [sp, #16]
      +0x134: ldp     x23, x24, [sp, #32]
      +0x138: ldr     x30, [sp, #48]
      +0x13c: add     sp, sp, #0xe60
      +0x140: ret
      +0x144: bl      <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_INDCPA_DEC_K2_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "plt_memset"; layout_range "mlkem512_indcpa_dec"];;

let DE2_EXEC = MLKEM_NATIVE_INDCPA_DEC_K2_GCC12_O3_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The decryption in FIPS 203 in terms of the values computed by the code:   *)
(* the decompressed u and v, the 12-bit fields of the decryption key as      *)
(* decoded (which may be >= q), the NTT of u and its multiplication cache,   *)
(* the product with s in Montgomery form, its inverse NTT, and the result    *)
(* after the subtraction from v and the reduction, whose compression is the  *)
(* message.                                                                  *)
(* ------------------------------------------------------------------------- *)

let KPKE_DECRYPT_K2_RESULT = prove
 (`!dk ct (UD:num->int16) (VD:num->int16) (SS:num->int16) (UH:num->int16)
    (MC:num->int16) (WP:num->int16) (WI:num->int16) (VR:num->int16).
     (!i. i < 512
          ==> UD i =
              word((3329 * (num_of_bytelist ct DIV 2 EXP (10 * i)) MOD
                    2 EXP 10 + 512) DIV 1024)) /\
     (!i. i < 256
          ==> VD i =
              word((3329 * (num_of_bytelist(mlkem_slice 640 128 ct) DIV
                            2 EXP (4 * i)) MOD 2 EXP 4 + 8) DIV 16)) /\
     (!i. i < 512
          ==> SS i = word((num_of_bytelist dk DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(UH(256 * j + i)) ==
                 forward_ntt (\n. ival(UD(256 * j + n))) i) (mod &3329) /\
                abs(ival(UH(256 * j + i))) <= &23594) /\
     (!j p. j < 2 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(UH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(WP(2 * p)) ==
               &169 *
               ((ival(SS(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p))) +
                (ival(SS(2 * p + 1)) * ival(MC p) +
                 ival(SS(2 * p)) * ival(UH(2 * p))))) (mod &3329) /\
              (ival(WP(2 * p + 1)) ==
               &169 *
               ((ival(SS(256 + 2 * p + 1)) * ival(UH(256 + 2 * p)) +
                 ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p + 1))) +
                (ival(SS(2 * p + 1)) * ival(UH(2 * p)) +
                 ival(SS(2 * p)) * ival(UH(2 * p + 1))))) (mod &3329)) /\
     (!i. i < 256
          ==> (ival(WI i) == inverse_ntt (\n. ival(WP n)) i) (mod &3329) /\
              abs(ival(WI i)) <= &26624) /\
     (!i. i < 256 ==> ival(VR i) = ival(word_sub (VD i) (WI i)) rem &3329)
     ==> nsum {i | i < 256}
              (\i. ((4 * val(VR i) + 3329) DIV 6658) MOD 2 * 2 EXP i) =
         num_of_bytelist(kpke_decrypt mlkem512 dk ct)`,
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
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem512] THEN
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
  ABBREV_TAC `fv = (num_of_bytelist (mlkem_slice 640 128 ct) DIV
                    2 EXP (4 * i)) MOD 2 EXP 4` THEN
  SUBGOAL_THEN `(3329 * fv + 8) DIV 16 < 3329` ASSUME_TAC THENL
   [SUBGOAL_THEN `fv < 16` MP_TAC THENL
     [EXPAND_TAC "fv" THEN
      REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`; MOD_LT_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ival(word((3329 * fv + 8) DIV 16):int16) =
                &((3329 * fv + 8) DIV 16)` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_SMALL THEN
    UNDISCH_TAC `(3329 * fv + 8) DIV 16 < 3329` THEN ARITH_TAC;
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
    UNDISCH_TAC `(3329 * fv + 8) DIV 16 < 3329` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
    UNDISCH_TAC `abs(ival((WI:num->int16) i)) <= &26624` THEN INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[COEFF_MLKEM_POLY] THEN
  SIMP_TAC[MLKEM_DECODE_SMALL; ARITH_RULE `4 < 12`] THEN
  ASM_SIMP_TAC[MLKEM_DECOMPRESS_NUM; ARITH_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&((3329 * fv + 8) DIV 16) rem &3329 = &((3329 * fv + 8) DIV 16)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INT_REM_LT THEN REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(b:int == d) (mod q) ==> (a - b == a - d) (mod q)`) THEN
  SUBGOAL_THEN
   `!j' n. j' < 2 /\ n < 256
           ==> (ival((UH:num->int16)(256 * j' + n)) ==
                mlkem_ntt (mlkem_poly
                  (\j''. mlkem_decompress 10
                          (mlkem_decode 10 ct (256 * j' + j'')))) n)
               (mod &3329)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MLKEM_NATIVE_NTT_CONG THEN
    EXISTS_TAC `\n. (UD:num->int16)(256 * j' + n)` THEN
    REWRITE_TAC[MLKEM_POLY_IN_RQ] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_SIMP_TAC[] THEN
    X_GEN_TAC `n':num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `256 * j' + n' < 512` ASSUME_TAC THENL
     [UNDISCH_TAC `j' < 2` THEN UNDISCH_TAC `n' < 256` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[COEFF_MLKEM_POLY; MLKEM_DECODE_SMALL; ARITH_RULE `10 < 12`;
                 MLKEM_DECOMPRESS_NUM; ARITH_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[INT_CONG_RREM] THEN
    ABBREV_TAC `fu = (num_of_bytelist ct DIV 2 EXP (10 * (256 * j' + n'))) MOD
                     1024` THEN
    SUBGOAL_THEN `fu < 1024` MP_TAC THENL
     [EXPAND_TAC "fu" THEN REWRITE_TAC[MOD_LT_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV;
      DISCH_TAC] THEN
    SUBGOAL_THEN `ival(word((3329 * fu + 512) DIV 1024):int16) =
                  &((3329 * fu + 512) DIV 1024)` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_WORD_SMALL THEN UNDISCH_TAC `fu < 1024` THEN ARITH_TAC;
      REWRITE_TAC[INT_CONG_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n'. n' < 256
         ==> (ival((WP:num->int16) n') ==
              &169 * ring_sum mlkem_zq {j' | j' < 2}
                      (\j'. fips203_multiply_ntts
                             (\n. mlkem_decode 12 dk (256 * j' + n))
                             (mlkem_ntt (mlkem_poly
                               (\j''. mlkem_decompress 10
                                       (mlkem_decode 10 ct (256 * j' + j'')))))
                             n')) (mod &3329)`
  ASSUME_TAC THENL
   [parity_tac THEN
    (SUBGOAL_THEN
      `!j' x. j' < 2 /\ x < 256
              ==> (ival((SS:num->int16)(256 * j' + x)) ==
                   mlkem_decode 12 dk (256 * j' + x)) (mod &3329)`
     ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC TT_DECODE_CONG THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `j' < 2` THEN UNDISCH_TAC `x < 256` THEN ARITH_TAC;
       ALL_TAC])
    THENL
     [MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 dk (256 * j' + n)`;
        `\j' n. ival((SS:num->int16)(256 * j' + n))`;
        `\j' n. ival((UH:num->int16)(256 * j' + n))`;
        `\j'. ival((MC:num->int16)(128 * j' + p))`;
        `\j'. mlkem_ntt (mlkem_poly
                (\j''. mlkem_decompress 10
                        (mlkem_decode 10 ct (256 * j' + j''))))`;
        `ival((WP:num->int16)(2 * p))`; `p:num`] BASEMUL2_ROW_EVEN);
      MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 dk (256 * j' + n)`;
        `\j' n. ival((SS:num->int16)(256 * j' + n))`;
        `\j' n. ival((UH:num->int16)(256 * j' + n))`;
        `\j'. mlkem_ntt (mlkem_poly
                (\j''. mlkem_decompress 10
                        (mlkem_decode 10 ct (256 * j' + j''))))`;
        `ival((WP:num->int16)(2 * p + 1))`; `p:num`] BASEMUL2_ROW_ODD)] THEN
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
(* of 16. The first 640 bytes of the ciphertext are the compressed u and its *)
(* last 128 the compressed v. After the calls that decompress and decode     *)
(* them, the results are named by ghosts with their values as given by the   *)
(* postconditions, and after the NTT of u, by a ghost with the congruence    *)
(* and the bound of the postcondition.                                       *)
(* ------------------------------------------------------------------------- *)

let DE2_ALIGNED_16_32 = prove
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

let DE2_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 159)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 128 else 144))`,
  REWRITE_TAC[DE2_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let DE2_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` DE2_BUFFER_ADDRESS))
    else NO_TAC);;

let DE2_CT_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [`c:int64`; `ct:byte list`]
         `read (memory :> bytes(c,768)) s = num_of_bytelist ct`) (concl th)
    then
      ASSUME_TAC(REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
       (REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_MOD;
                     ARITH_RULE `MIN 768 640 = 640`]
        (AP_THM(AP_TERM `(MOD):num->num->num`
                 (REWRITE_RULE[READ_COMPONENT_COMPOSE] th))
           `2 EXP (8 * 640)`))) THEN
      MP_TAC(SPECL [`c:int64`; `ct:byte list`; `640`; `128`;
                    rand(lhand(concl th))] READ_MEMORY_BYTES_SLICE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC]
    else NO_TAC);;

let DE2_UD_TAC b =
  INDCPA_GHOST_TAC "UD" (b + 1024) 512 "s20" THEN
  SUBGOAL_THEN
   `!i. i < 512
        ==> (UD:num->int16) i =
            word((3329 * (num_of_bytelist ct DIV 2 EXP (10 * i)) MOD
                  2 EXP 10 + 512) DIV 1024)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "UD" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s20:armstate` (frees(concl th)) && is_forall(concl th) &&
      can (find_term ((=) `num_of_bytelist ct MOD 2 EXP (8 * 640)`))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC DIV_MOD_EXP_LOW THEN
    UNDISCH_TAC `i < 512` THEN ARITH_TAC;
    ALL_TAC];;

let DE2_VD_TAC b =
  INDCPA_GHOST_TAC "VD" (b + 3072) 256 "s24" THEN
  SUBGOAL_THEN
   `!i. i < 256
        ==> (VD:num->int16) i =
            word((3329 * (num_of_bytelist(mlkem_slice 640 128 ct) DIV
                          2 EXP (4 * i)) MOD 2 EXP 4 + 8) DIV 16)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "VD" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s24:armstate` (frees(concl th)) && is_forall(concl th) &&
      can (find_term ((=) `num_of_bytelist(mlkem_slice 640 128 ct)`))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

let DE2_SS_TAC b =
  INDCPA_GHOST_TAC "SS" b 512 "s29" THEN
  SUBGOAL_THEN
   `!i. i < 512
        ==> (SS:num->int16) i =
            word((num_of_bytelist dk DIV 2 EXP (12 * i)) MOD 2 EXP 12)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "SS" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s29:armstate` (frees(concl th)) && is_forall(concl th) &&
      can (find_term ((=) `num_of_bytelist dk`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

let DE2_UD_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 512 ==> abs(ival((UD:num->int16) m)) <= &3328`
  (LABEL_TAC "udbound") THENL
   [X_GEN_TAC `m':num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(num_of_bytelist ct DIV 2 EXP (10 * m')) MOD 2 EXP 10 < 1024`
    MP_TAC THENL [REWRITE_TAC[ARITH_RULE `1024 = 2 EXP 10`; MOD_LT_EQ] THEN
                  CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    SPEC_TAC(`(num_of_bytelist ct DIV 2 EXP (10 * m')) MOD 2 EXP 10`,
             `f:num`) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `ival(word((3329 * f + 512) DIV 1024):int16) =
                  &((3329 * f + 512) DIV 1024)` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_WORD_SMALL THEN UNDISCH_TAC `f < 1024` THEN ARITH_TAC;
      REWRITE_TAC[INT_ABS_NUM; INT_OF_NUM_LE] THEN
      UNDISCH_TAC `f < 1024` THEN ARITH_TAC];
    ALL_TAC];;

let DE2_SS_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 512 ==> abs(ival((SS:num->int16) m)) <= &2 pow 12`
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

let DE2_UH_TAC b =
  let st = `s33:armstate` and srct = `UD:num->int16` in
  INDCPA_GHOST_TAC "UH" (b + 1024) 512 "s33" THEN
  SUBGOAL_THEN
   `!j i. j < 2 /\ i < 256
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

let DE2_BASEMUL_DEFS =
  [basemul2_even; basemul2_odd; pmul_acc2; pmull_acc2; pmull];;

let DE2_WP_GOAL = `!p. p < 128
       ==> (ival((WP:num->int16)(2 * p)) ==
            &169 *
            ((ival((SS:num->int16)(256 + 2 * p + 1)) *
              ival((MC:num->int16)(128 + p)) +
              ival(SS(256 + 2 * p)) * ival((UH:num->int16)(256 + 2 * p))) +
             (ival(SS(2 * p + 1)) * ival(MC p) +
              ival(SS(2 * p)) * ival(UH(2 * p))))) (mod &3329) /\
           (ival(WP(2 * p + 1)) ==
            &169 *
            ((ival(SS(256 + 2 * p + 1)) * ival(UH(256 + 2 * p)) +
              ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p + 1))) +
             (ival(SS(2 * p + 1)) * ival(UH(2 * p)) +
              ival(SS(2 * p)) * ival(UH(2 * p + 1))))) (mod &3329)`;;

let DE2_WP_TAC b =
  INDCPA_GHOST_TAC "WP" (b + 2560) 256 "s43" THEN
  SUBGOAL_THEN DE2_WP_GOAL ASSUME_TAC THENL
   [INDCPA_BASEMULK_ROW_TAC 2 "WP" (b + 2560) "ssbound" [] DE2_BASEMUL_DEFS;
    ALL_TAC];;

let DE2_TOMSG_POST_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && mem `VR:num->int16` (frees(concl th)) &&
    INDCPA_HAS_CONST "nsum" (concl th))) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC VAL_LT_OF_IVAL_REM THEN
    EXISTS_TAC `ival(word_sub ((VD:num->int16) i) ((WI:num->int16) i))` THEN
    ASM_SIMP_TAC[];
    DISCH_TAC];;

let DE2_FINAL_TAC =
  MP_TAC(SPECL [`dk:byte list`; `ct:byte list`; `UD:num->int16`;
                `VD:num->int16`; `SS:num->int16`; `UH:num->int16`;
                `MC:num->int16`; `WP:num->int16`; `WI:num->int16`;
                `VR:num->int16`] KPKE_DECRYPT_K2_RESULT) THEN
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
   (mlkem_native_libmlkem_gcc12_O3_mc,DE2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_DECOMPRESS_D4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,DE2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_FROMBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,DE2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_NTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,DE2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLYVEC_NTT_K2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_MULCACHE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,DE2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
   );;

let LOCAL_BASEMUL_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,DE2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_BASEMUL_K2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_INVNTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,DE2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_SUB_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,DE2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_SUB_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,DE2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_TOMSG_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,DE2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset. The ciphertext ct of *)
(* 768 bytes is at c and the decryption key dk of 768 bytes at sk, and the   *)
(* message of 32 bytes written at m is kpke_decrypt mlkem512 dk ct in        *)
(* common/fips203.ml, for any dk (FIPS 203 decodes s modulo q, while the     *)
(* code multiplies by the 12-bit fields, which are congruent). The stack is  *)
(* the 3680 bytes of the function and the 64 used by its callees below them. *)
(* The proof is by cases on whether the stack pointer is a multiple of 32,   *)
(* which gives the address b of the buffers, at offsets 0 (s), 1024 (u),     *)
(* 2048 (the multiplication cache), 2560 (the product) and 3072 (v).         *)
(* ------------------------------------------------------------------------- *)

let DE2_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`m:int64`; `c:int64`; `sk:int64`; `dk:byte list`; `ct:byte list`;
    `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 3744 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 3744):int64)` THEN
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
     (parse_term("X"^string_of_int n))) (19--28);;

let DE2_CASE_TAC b =
  let st n = "s"^string_of_int n in
  ENSURES_INIT_TAC "s0" THEN DE2_CT_TAC THEN

  (*** The setup, the ciphertext and the secret key ***)

  ARM_STEPS_TAC DE2_EXEC (1--2) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC DE2_EXEC (3--6) THEN DE2_BUFFER_TAC THEN
  ARM_STEPS_TAC DE2_EXEC (7--19) THEN
  LOCAL_POLYVEC_DECOMPRESS_DU_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist ct MOD 2 EXP (8 * 640)`;
    `pc:num`; `read SP s`; `read X30 s`] 20 THEN
  DE2_UD_TAC b THEN
  ARM_STEPS_TAC DE2_EXEC (21--23) THEN
  LOCAL_POLY_DECOMPRESS_D4_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist(mlkem_slice 640 128 ct)`;
    `pc:num`; `read X30 s`] 24 THEN
  DE2_VD_TAC b THEN
  ARM_STEPS_TAC DE2_EXEC (25--28) THEN
  LOCAL_POLYVEC_FROMBYTES_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist dk`; `pc:num`; `read SP s`;
    `read X30 s`] 29 THEN
  DE2_SS_TAC b THEN

  (*** The NTT of u and its multiplication cache, the product with s ***)

  DE2_UD_BOUND_TAC THEN
  ARM_STEPS_TAC DE2_EXEC (30--32) THEN
  LOCAL_POLYVEC_NTT_TAC
   [`read X0 s`; `UD:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 33 THEN
  DE2_UH_TAC b THEN
  ARM_STEPS_TAC DE2_EXEC (34--36) THEN
  LOCAL_POLYVEC_MULCACHE_TAC
   [`read X0 s`; `read X1 s`; `UH:num->int16`; `pc:num`; `read SP s`;
    `read X30 s`] 37 THEN
  INDCPA_MULCACHE_TAC "MC" (b + 2048) 2 "UH" (st 37) THEN
  ARM_STEPS_TAC DE2_EXEC (38--42) THEN
  INDCPA_BASEMULK_PRE_TAC 2 (b,"SS",0) (b + 1024,"UH") (b + 2048,"MC")
    (st 42) THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 2 ("SS",0) "UH" "MC") 43 THEN
  INDCPA_BASEMULK_DROP_PRE_TAC 2 (b,"SS",0) (b + 1024,"UH")
    (b + 2048,"MC") THEN
  DE2_SS_BOUND_TAC THEN DE2_WP_TAC b THEN

  (*** The inverse NTT, the subtraction from v, the reduction ***)

  ARM_STEPS_TAC DE2_EXEC (44--45) THEN
  LOCAL_POLY_INVNTT_TAC
   [`read X0 s`; `WP:num->int16`; `pc:num`; `read SP s`; `read X30 s`]
   46 THEN
  INDCPA_INVNTT1_TAC "WI" (b + 2560) "WP" (st 46) THEN
  ARM_STEPS_TAC DE2_EXEC (47--49) THEN
  LOCAL_POLY_SUB_TAC
   [`read X0 s`; `read X1 s`; `VD:num->int16`; `WI:num->int16`; `pc:num`;
    `read X30 s`] 50 THEN
  ARM_STEPS_TAC DE2_EXEC (51--52) THEN
  LOCAL_POLY_REDUCE_TAC
   [`read X0 s`; `\i. word_sub ((VD:num->int16) i) ((WI:num->int16) i)`;
    `pc:num`; `read X30 s`] 53 THEN
  INDCPA_REDUCE_TAC "VR" (b + 3072) 256
    "word_sub ((VD:num->int16) i) ((WI:num->int16) i)" (st 53) THEN

  (*** The message ***)

  ARM_STEPS_TAC DE2_EXEC (54--56) THEN
  LOCAL_POLY_TOMSG_TAC
   [`read X0 s`; `read X1 s`; `VR:num->int16`; `pc:num`; `read SP s`;
    `read X30 s`]
   57 THEN
  DE2_TOMSG_POST_TAC THEN

  (*** Zeroing the buffers, the stack guard, the return ***)

  INDCPA_MEMSET_LABEL_TAC THEN
  INDCPA_MEMSETS_TAC DE2_EXEC
   [58,61; 67,70; 76,79; 85,88; 94,97] THEN
  ARM_STEPS_TAC DE2_EXEC (103--103) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC DE2_EXEC (104--116) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DE2_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_DEC_K2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!m c sk (dk:byte list) (ct:byte list) guard mf ea el ev pc
    stackpointer returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        LENGTH dk = 768 /\ LENGTH ct = 768 /\
        nonoverlapping (m,32) (word_sub stackpointer (word 3744),3744) /\
        nonoverlapping (c,768) (word pc,libmlkem_size) /\
        nonoverlapping (sk,768) (word pc,libmlkem_size) /\
        ALLPAIRS nonoverlapping
         [(m,32); (word_sub stackpointer (word 3744),3744)]
         [(c,768); (sk,768); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem512_indcpa_dec) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [m; c; sk] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(c,768)) s = num_of_bytelist ct /\
                  read (memory :> bytes(sk,768)) s = num_of_bytelist dk)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(m,32)) s =
                  num_of_bytelist(kpke_decrypt mlkem512 dk ct) /\
                  C_RETURN s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(m,32);
                memory :> bytes(word_sub stackpointer (word 3744),3744)])`,
  DE2_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [DE2_CASE_TAC 128; DE2_CASE_TAC 144]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contract for memset. The events depend only on the addresses of the       *)
(* arguments, the stack and the image, not on the ciphertext or the key. The *)
(* buffers are kept at stackpointer + b with b the conditional offset (128 or *)
(* 144), so the two cases need not be separated.                             *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let DE2_SAFE_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 159))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 128 else 144))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC DE2_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

(*** Stack addresses in the form word_add stackpointer (word n) ***)

let DE2_NORMALIZE_TAC =
  let conv =
    REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
    DEPTH_CONV NUM_ADD_CONV in
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE conv th else th);;

let DE2_ALLOWED =
  [`pc:num`; `m:int64`; `c:int64`; `sk:int64`; `guard:int64`; `mf:int64`;
   `stackpointer:int64`; `returnaddress:int64`];;

let DE2_SAFE_CALL_TAC name ilist n =
  DE2_NORMALIZE_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O3_mc,DE2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref DE2_ALLOWED); LABEL_TAC name safety_th]);;

let DE2_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_safety_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K2_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_DECOMPRESS_DU" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_DECOMPRESS_DV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_NTT_K2_GCC12_O3_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K2_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O3_IMAGE_SUBROUTINE_SAFE "H_BASEMUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_INVNTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_SUB_GCC12_O3_IMAGE_SUBROUTINE_SAFE "H_SUB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O3_IMAGE_SUBROUTINE_SAFE "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_IMAGE_SUBROUTINE_SAFE "H_TOMSG" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 3744):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `128 <= (if aligned 32 (stackpointer:int64) then 128 else 144) /\
    (if aligned 32 (stackpointer:int64) then 128 else 144) <= 144`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
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
     (parse_term("X"^string_of_int n))) (19--28);;

let DE2_SAFE_MAIN_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC DE2_EXEC (1--2) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC DE2_EXEC (3--6) THEN DE2_SAFE_BUFFER_TAC THEN
  ARM_STEPS_TAC DE2_EXEC (7--19) THEN
  DE2_SAFE_CALL_TAC "H_DECOMPRESS_DU"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read SP s`;
    `read X30 s`] 20 THEN
  ARM_STEPS_TAC DE2_EXEC (21--23) THEN
  DE2_SAFE_CALL_TAC "H_DECOMPRESS_DV"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read X30 s`]
   24 THEN
  ARM_STEPS_TAC DE2_EXEC (25--28) THEN
  DE2_SAFE_CALL_TAC "H_FROMBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read SP s`;
    `read X30 s`] 29 THEN
  ARM_STEPS_TAC DE2_EXEC (30--32) THEN
  DE2_SAFE_CALL_TAC "H_NTT"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`; `read X30 s`]
   33 THEN
  ARM_STEPS_TAC DE2_EXEC (34--36) THEN
  DE2_SAFE_CALL_TAC "H_MULCACHE"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read SP s`;
    `read X30 s`] 37 THEN
  ARM_STEPS_TAC DE2_EXEC (38--42) THEN
  DE2_SAFE_CALL_TAC "H_BASEMUL"
   [`e:(uarch_event)list`; `read X1 s`; `read X2 s`; `read X3 s`;
    `read X0 s`; `pc:num`; `read X30 s`] 43 THEN
  ARM_STEPS_TAC DE2_EXEC (44--45) THEN
  DE2_SAFE_CALL_TAC "H_INVNTT"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`; `read X30 s`]
   46 THEN
  ARM_STEPS_TAC DE2_EXEC (47--49) THEN
  DE2_SAFE_CALL_TAC "H_SUB"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read X30 s`]
   50 THEN
  ARM_STEPS_TAC DE2_EXEC (51--52) THEN
  DE2_SAFE_CALL_TAC "H_REDUCE"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read X30 s`] 53 THEN
  ARM_STEPS_TAC DE2_EXEC (54--56) THEN
  DE2_SAFE_CALL_TAC "H_TOMSG"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read SP s`;
    `read X30 s`]
   57 THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC DE2_EXEC (k0--k) THEN LIBC_PLT_TAC DE2_EXEC k THEN
    LIBC_SAFE_CALL_TAC "H_MEMSET" DE2_EXEC
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
      `read X30 s`] (ref DE2_ALLOWED) (k + 5))
   [58,61; 67,70; 76,79; 85,88; 94,97] THEN
  ARM_STEPS_TAC DE2_EXEC (103--103) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC DE2_EXEC (104--116) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_DEC_K2_GCC12_O3_IMAGE_SUBROUTINE_SAFE = prove
 (`!mf ea el ev.
     memset_safety_contract mf ea el ev
     ==> exists f_events.
          forall e m c sk guard pc stackpointer returnaddress.
            aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
            aligned 16 stackpointer /\
            nonoverlapping (m,32) (word_sub stackpointer (word 3744),3744) /\
            nonoverlapping (c,768) (word pc,libmlkem_size) /\
            nonoverlapping (sk,768) (word pc,libmlkem_size) /\
            ALLPAIRS nonoverlapping
             [(m,32); (word_sub stackpointer (word 3744),3744)]
             [(c,768); (sk,768); (word pc,libmlkem_size);
              (word(pc + got_stack_chk_guard),8);
              (guard,8); (word(pc + got_memset),8); (ea,el)]
            ==> ensures arm
                 (\s. aligned_bytes_loaded s (word pc)
                        mlkem_native_libmlkem_gcc12_O3_mc /\
                      read PC s = word (pc + mlkem512_indcpa_dec) /\
                      read SP s = stackpointer /\
                      read X30 s = returnaddress /\
                      C_ARGUMENTS [m; c; sk] s /\
                      read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                       s = guard /\
                      read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                      read (memory :> bytes(ea,el)) s = ev /\
                      read events s = e)
                 (\s. read PC s = returnaddress /\
                      C_RETURN s = word 0 /\
                      (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events m c sk guard mf pc
                                (word_sub stackpointer (word 3744))
                                returnaddress /\
                         memaccess_inbounds e2
                          [c,768; sk,768; m,32;
                           word_sub stackpointer (word 3744),3744;
                           word(pc + got_stack_chk_guard),8; guard,8;
                           word(pc + got_memset),8;
                           ea,el;
                           word(pc + mlkem_poly_decompress_d4_consts),16;
                           word(pc + rodata_mlk_zetas),256;
                           word(pc + mlkem_poly_ntt_consts),
                           mlkem_poly_ntt_consts_size:num;
                           word(pc + mlkem_poly_mulcache_compute_consts),
                           mlkem_poly_mulcache_compute_consts_size:num;
                           word(pc + mlkem512_polyvec_basemul_acc_montgomery_cached_consts),
                           mlkem512_polyvec_basemul_acc_montgomery_cached_consts_size:num;
                           word(pc + mlkem_poly_invntt_tomont_consts),
                           mlkem_poly_invntt_tomont_consts_size:num;
                           word(pc + mlkem_poly_tomsg_consts),16]
                          [m,32; word_sub stackpointer (word 3744),3744]))
                 (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                  MAYCHANGE [X18] ,,
                  MAYCHANGE
                   [memory :> bytes(m,32);
                    memory :> bytes(word_sub stackpointer (word 3744),3744)])`,
  DE2_SAFE_INTRO_TAC THEN DE2_SAFE_MAIN_TAC);;
