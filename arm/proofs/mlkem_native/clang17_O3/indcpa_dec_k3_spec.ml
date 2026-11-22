(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decryption of K-PKE for ML-KEM-768 (FIPS 203 Algorithm 15). This is   *)
(* the code for mlkem768_indcpa_dec from mlkem-native's portable C           *)
(* implementation compiled by clang 17 with -O3 (see mlkem_native/README.md). *)
(* It decompresses u and v from the ciphertext, decodes the secret vector s  *)
(* in the NTT domain from the decryption key, and writes the compression     *)
(* with d = 1 of w = v - NTT^-1(s^T NTT(u)) as the message, zeroing its      *)
(* buffers. It is verified in the whole image (see                           *)
(* libmlkem.ml), using the theorems for                                      *)
(* mlkem768_polyvec_decompress_du, mlkem_poly_decompress_d4,                 *)
(* mlkem768_polyvec_frombytes, mlkem768_polyvec_ntt,                         *)
(* mlkem768_polyvec_mulcache_compute,                                        *)
(* mlkem768_polyvec_basemul_acc_montgomery_cached, mlkem_poly_invntt_tomont, *)
(* mlkem_poly_sub, mlkem_poly_reduce and mlkem_poly_tomsg in the image, and  *)
(* the contract for memset.                                                  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/polyvec_decompress_du_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/poly_decompress_d4_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/polyvec_frombytes_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/polyvec_ntt_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/polyvec_mulcache_compute_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/basemul_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/poly_sub_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/poly_reduce_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/poly_tomsg_spec.ml";;
needs "arm/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mlkem768_indcpa_dec:
       +0x0: stp     x29, x30, [sp, #-80]!
       +0x4: str     x28, [sp, #16]
       +0x8: stp     x24, x23, [sp, #32]
       +0xc: stp     x22, x21, [sp, #48]
      +0x10: stp     x20, x19, [sp, #64]
      +0x14: mov     x29, sp
      +0x18: sub     x9, sp, #0x1, lsl #12
      +0x1c: sub     x9, x9, #0x310
      +0x20: and     sp, x9, #0xffffffffffffffe0
      +0x24: adrp    x8, <page>
      +0x28: mov     x21, x0
      +0x2c: add     x0, sp, #0xd00
      +0x30: mov     x19, x2
      +0x34: mov     x20, x1
      +0x38: add     x22, sp, #0xd00
      +0x3c: ldr     x8, [x8, #4088]
      +0x40: ldr     x8, [x8]
      +0x44: str     x8, [sp, #4872]
      +0x48: bl      <mlkem768_polyvec_decompress_du>
      +0x4c: add     x1, x20, #0x3c0
      +0x50: add     x0, sp, #0x500
      +0x54: add     x20, sp, #0x500
      +0x58: bl      <mlkem_poly_decompress_d4>
      +0x5c: add     x0, sp, #0x700
      +0x60: mov     x1, x19
      +0x64: add     x19, sp, #0x700
      +0x68: bl      <mlkem768_polyvec_frombytes>
      +0x6c: add     x0, sp, #0xd00
      +0x70: bl      <mlkem768_polyvec_ntt>
      +0x74: mov     x0, sp
      +0x78: add     x1, sp, #0xd00
      +0x7c: mov     x24, sp
      +0x80: bl      <mlkem768_polyvec_mulcache_compute>
      +0x84: add     x0, sp, #0x300
      +0x88: add     x1, sp, #0x700
      +0x8c: add     x2, sp, #0xd00
      +0x90: mov     x3, sp
      +0x94: add     x23, sp, #0x300
      +0x98: bl      <mlkem768_polyvec_basemul_acc_montgomery_cached>
      +0x9c: add     x0, sp, #0x300
      +0xa0: bl      <mlkem_poly_invntt_tomont>
      +0xa4: add     x0, sp, #0x500
      +0xa8: add     x1, sp, #0x300
      +0xac: bl      <mlkem_poly_sub>
      +0xb0: add     x0, sp, #0x500
      +0xb4: bl      <mlkem_poly_reduce>
      +0xb8: add     x1, sp, #0x500
      +0xbc: mov     x0, x21
      +0xc0: bl      <mlkem_poly_tomsg>
      +0xc4: mov     x0, sp
      +0xc8: mov     w1, wzr
      +0xcc: mov     w2, #0x300
      +0xd0: bl      <memset@plt>
      +0xd4: movi    v0.2d, #0x0
      +0xd8: add     x0, sp, #0x700
      +0xdc: mov     w1, wzr
      +0xe0: mov     w2, #0x600
      +0xe4: str     q0, [sp, #1264]
      +0xe8: str     q0, [sp, #1248]
      +0xec: str     q0, [sp, #1232]
      +0xf0: str     q0, [sp, #1216]
      +0xf4: str     q0, [sp, #1200]
      +0xf8: str     q0, [sp, #1184]
      +0xfc: str     q0, [sp, #1168]
     +0x100: str     q0, [sp, #1152]
     +0x104: str     q0, [sp, #1136]
     +0x108: str     q0, [sp, #1120]
     +0x10c: str     q0, [sp, #1104]
     +0x110: str     q0, [sp, #1088]
     +0x114: str     q0, [sp, #1072]
     +0x118: str     q0, [sp, #1056]
     +0x11c: str     q0, [sp, #1040]
     +0x120: stp     q0, q0, [sp, #784]
     +0x124: stp     q0, q0, [sp, #816]
     +0x128: stp     q0, q0, [sp, #848]
     +0x12c: stp     q0, q0, [sp, #880]
     +0x130: stp     q0, q0, [sp, #912]
     +0x134: stp     q0, q0, [sp, #944]
     +0x138: stp     q0, q0, [sp, #976]
     +0x13c: stp     q0, q0, [sp, #1008]
     +0x140: str     q0, [sp, #768]
     +0x144: str     q0, [sp, #1776]
     +0x148: str     q0, [sp, #1760]
     +0x14c: str     q0, [sp, #1744]
     +0x150: str     q0, [sp, #1728]
     +0x154: str     q0, [sp, #1712]
     +0x158: str     q0, [sp, #1696]
     +0x15c: str     q0, [sp, #1680]
     +0x160: str     q0, [sp, #1664]
     +0x164: str     q0, [sp, #1648]
     +0x168: str     q0, [sp, #1632]
     +0x16c: str     q0, [sp, #1616]
     +0x170: str     q0, [sp, #1600]
     +0x174: str     q0, [sp, #1584]
     +0x178: str     q0, [sp, #1568]
     +0x17c: str     q0, [sp, #1552]
     +0x180: str     q0, [sp, #1536]
     +0x184: str     q0, [sp, #1520]
     +0x188: str     q0, [sp, #1504]
     +0x18c: str     q0, [sp, #1488]
     +0x190: str     q0, [sp, #1472]
     +0x194: str     q0, [sp, #1456]
     +0x198: str     q0, [sp, #1440]
     +0x19c: str     q0, [sp, #1424]
     +0x1a0: str     q0, [sp, #1408]
     +0x1a4: str     q0, [sp, #1392]
     +0x1a8: str     q0, [sp, #1376]
     +0x1ac: str     q0, [sp, #1360]
     +0x1b0: str     q0, [sp, #1344]
     +0x1b4: str     q0, [sp, #1328]
     +0x1b8: str     q0, [sp, #1312]
     +0x1bc: str     q0, [sp, #1296]
     +0x1c0: str     q0, [sp, #1280]
     +0x1c4: bl      <memset@plt>
     +0x1c8: add     x0, sp, #0xd00
     +0x1cc: mov     w1, wzr
     +0x1d0: mov     w2, #0x600
     +0x1d4: bl      <memset@plt>
     +0x1d8: adrp    x8, <page>
     +0x1dc: ldr     x8, [x8, #4088]
     +0x1e0: ldr     x9, [sp, #4872]
     +0x1e4: ldr     x8, [x8]
     +0x1e8: cmp     x8, x9
     +0x1ec: b.ne    <mlkem768_indcpa_dec+0x210>
     +0x1f0: mov     w0, wzr
     +0x1f4: mov     sp, x29
     +0x1f8: ldp     x20, x19, [sp, #64]
     +0x1fc: ldp     x22, x21, [sp, #48]
     +0x200: ldp     x24, x23, [sp, #32]
     +0x204: ldr     x28, [sp, #16]
     +0x208: ldp     x29, x30, [sp], #80
     +0x20c: ret
     +0x210: bl      <__stack_chk_fail@plt>

    memset@plt:
      +0x0: adrp    x16, <page>
      +0x4: ldr     x17, [x16, #4072]  // got_memset
      +0x8: add     x16, x16, #0xfe8  // got_memset
      +0xc: br      x17
 ***)

let MLKEM_NATIVE_INDCPA_DEC_K3_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "plt_memset"; layout_range "mlkem768_indcpa_dec"];;

let DE3_EXEC = MLKEM_NATIVE_INDCPA_DEC_K3_CLANG17_O3_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The decryption in FIPS 203 in terms of the values computed by the code:   *)
(* the decompressed u and v, the 12-bit fields of the decryption key as      *)
(* decoded (which may be >= q), the NTT of u and its multiplication cache,   *)
(* the product with s in Montgomery form, its inverse NTT, and the result    *)
(* after the subtraction from v and the reduction, whose compression is the  *)
(* message.                                                                  *)
(* ------------------------------------------------------------------------- *)

let KPKE_DECRYPT_K3_RESULT_STMT =
  `!dk ct (UD:num->int16) (VD:num->int16) (SS:num->int16) (UH:num->int16)
    (MC:num->int16) (WP:num->int16) (WI:num->int16) (VR:num->int16).
     (!i. i < 768
          ==> UD i =
              word((3329 * (num_of_bytelist ct DIV 2 EXP (10 * i)) MOD
                    2 EXP 10 + 512) DIV 1024)) /\
     (!i. i < 256
          ==> VD i =
              word((3329 * (num_of_bytelist(mlkem_slice 960 128 ct) DIV
                            2 EXP (4 * i)) MOD 2 EXP 4 + 8) DIV 16)) /\
     (!i. i < 768
          ==> SS i = word((num_of_bytelist dk DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(UH(256 * j + i)) ==
                 forward_ntt (\n. ival(UD(256 * j + n))) i) (mod &3329) /\
                abs(ival(UH(256 * j + i))) <= &23594) /\
     (!j p. j < 3 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(UH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(WP(2 * p)) ==
               &169 *
               ((ival(SS(512 + 2 * p + 1)) * ival(MC(256 + p)) +
                 ival(SS(512 + 2 * p)) * ival(UH(512 + 2 * p))) +
                (ival(SS(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p))) +
                (ival(SS(2 * p + 1)) * ival(MC p) +
                 ival(SS(2 * p)) * ival(UH(2 * p))))) (mod &3329) /\
              (ival(WP(2 * p + 1)) ==
               &169 *
               ((ival(SS(512 + 2 * p + 1)) * ival(UH(512 + 2 * p)) +
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
         num_of_bytelist(kpke_decrypt mlkem768 dk ct)`;;

let KPKE_DECRYPT_K3_RESULT = assume_spec KPKE_DECRYPT_K3_RESULT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16. The first 960 bytes of the ciphertext are the compressed u and its *)
(* last 128 the compressed v. After the calls that decompress and decode     *)
(* them, the results are named by ghosts with their values as given by the   *)
(* postconditions, and after the NTT of u, by a ghost with the congruence    *)
(* and the bound of the postcondition.                                       *)
(* ------------------------------------------------------------------------- *)

let DE3_ALIGNED_16_32_STMT =
  `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`;;

let DE3_ALIGNED_16_32 = assume_spec DE3_ALIGNED_16_32_STMT;;

let DE3_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 704)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 704 else 688))`;;

let DE3_BUFFER_ADDRESS = assume_spec DE3_BUFFER_ADDRESS_STMT;;

let DE3_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` DE3_BUFFER_ADDRESS))
    else NO_TAC);;

let DE3_CT_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(c,1088)) s = num_of_bytelist ct`) (concl th)
    then
      ASSUME_TAC(REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
       (REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_MOD;
                     ARITH_RULE `MIN 1088 960 = 960`]
        (AP_THM(AP_TERM `(MOD):num->num->num`
                 (REWRITE_RULE[READ_COMPONENT_COMPOSE] th))
           `2 EXP (8 * 960)`))) THEN
      MP_TAC(SPECL [`c:int64`; `ct:byte list`; `960`; `128`;
                    rand(lhand(concl th))] READ_MEMORY_BYTES_SLICE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC]
    else NO_TAC);;

let DE3_UD_TAC b =
  INDCPA_GHOST_TAC "UD" (b + 3328) 768 "s20" THEN
  SUBGOAL_THEN
   `!i. i < 768
        ==> (UD:num->int16) i =
            word((3329 * (num_of_bytelist ct DIV 2 EXP (10 * i)) MOD
                  2 EXP 10 + 512) DIV 1024)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "UD" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s20:armstate` (frees(concl th)) && is_forall(concl th) &&
      can (find_term ((=) `num_of_bytelist ct MOD 2 EXP (8 * 960)`))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC DIV_MOD_EXP_LOW THEN
    UNDISCH_TAC `i < 768` THEN ARITH_TAC;
    ALL_TAC];;

let DE3_VD_TAC b =
  INDCPA_GHOST_TAC "VD" (b + 1280) 256 "s25" THEN
  SUBGOAL_THEN
   `!i. i < 256
        ==> (VD:num->int16) i =
            word((3329 * (num_of_bytelist(mlkem_slice 960 128 ct) DIV
                          2 EXP (4 * i)) MOD 2 EXP 4 + 8) DIV 16)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "VD" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s25:armstate` (frees(concl th)) && is_forall(concl th) &&
      can (find_term ((=) `num_of_bytelist(mlkem_slice 960 128 ct)`))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

let DE3_SS_TAC b =
  INDCPA_GHOST_TAC "SS" (b + 1792) 768 "s30" THEN
  SUBGOAL_THEN
   `!i. i < 768
        ==> (SS:num->int16) i =
            word((num_of_bytelist dk DIV 2 EXP (12 * i)) MOD 2 EXP 12)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "SS" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s30:armstate` (frees(concl th)) && is_forall(concl th) &&
      can (find_term ((=) `num_of_bytelist dk`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

let DE3_UD_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 768 ==> abs(ival((UD:num->int16) m)) <= &3328`
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

let DE3_SS_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 768 ==> abs(ival((SS:num->int16) m)) <= &2 pow 12`
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

let DE3_UH_TAC b =
  let st = `s33:armstate` and srct = `UD:num->int16` in
  INDCPA_GHOST_TAC "UH" (b + 3328) 768 "s33" THEN
  SUBGOAL_THEN
   `!j i. j < 3 /\ i < 256
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

let DE3_BASEMUL_DEFS =
  [basemul3_even; basemul3_odd; pmul_acc3; pmull_acc3; pmull];;

let DE3_WP_GOAL = `!p. p < 128
       ==> (ival((WP:num->int16)(2 * p)) ==
            &169 *
            ((ival((SS:num->int16)(512 + 2 * p + 1)) *
              ival((MC:num->int16)(256 + p)) +
              ival(SS(512 + 2 * p)) * ival((UH:num->int16)(512 + 2 * p))) +
             (ival(SS(256 + 2 * p + 1)) * ival(MC(128 + p)) +
              ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p))) +
             (ival(SS(2 * p + 1)) * ival(MC p) +
              ival(SS(2 * p)) * ival(UH(2 * p))))) (mod &3329) /\
           (ival(WP(2 * p + 1)) ==
            &169 *
            ((ival(SS(512 + 2 * p + 1)) * ival(UH(512 + 2 * p)) +
              ival(SS(512 + 2 * p)) * ival(UH(512 + 2 * p + 1))) +
             (ival(SS(256 + 2 * p + 1)) * ival(UH(256 + 2 * p)) +
              ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p + 1))) +
             (ival(SS(2 * p + 1)) * ival(UH(2 * p)) +
              ival(SS(2 * p)) * ival(UH(2 * p + 1))))) (mod &3329)`;;

let DE3_WP_TAC b =
  INDCPA_GHOST_TAC "WP" (b + 768) 256 "s45" THEN
  SUBGOAL_THEN DE3_WP_GOAL ASSUME_TAC THENL
   [INDCPA_BASEMUL3_ROW_TAC "WP" (b + 768) "ssbound" [] DE3_BASEMUL_DEFS;
    ALL_TAC];;

let DE3_TOMSG_POST_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && mem `VR:num->int16` (frees(concl th)) &&
    INDCPA_HAS_CONST "nsum" (concl th))) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC VAL_LT_OF_IVAL_REM THEN
    EXISTS_TAC `ival(word_sub ((VD:num->int16) i) ((WI:num->int16) i))` THEN
    ASM_SIMP_TAC[];
    DISCH_TAC];;

let DE3_FINAL_TAC =
  MP_TAC(SPECL [`dk:byte list`; `ct:byte list`; `UD:num->int16`;
                `VD:num->int16`; `SS:num->int16`; `UH:num->int16`;
                `MC:num->int16`; `WP:num->int16`; `WI:num->int16`;
                `VR:num->int16`] KPKE_DECRYPT_K3_RESULT) THEN
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
   (mlkem_native_libmlkem_clang17_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_DECOMPRESS_D4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_DECOMPRESS_D4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_FROMBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_NTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLYVEC_NTT_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_MULCACHE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
   );;

let LOCAL_BASEMUL_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_BASEMUL_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_INVNTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_SUB_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_SUB_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_TOMSG_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_TOMSG_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset. The ciphertext ct of *)
(* 1088 bytes is at c and the decryption key dk of 1152 bytes at sk, and the *)
(* message of 32 bytes written at m is kpke_decrypt mlkem768 dk ct in        *)
(* common/fips203/fips203.ml, for any dk (FIPS 203 decodes s modulo q, while *)
(* the code multiplies by the 12-bit fields, which are congruent). The stack *)
(* is the 5664 bytes of the frame: 80 of saved registers, 4880 for the       *)
(* buffers and the stack guard, which the code aligns to 32 bytes by "sub    *)
(* x9, sp, #4096; sub x9, x9, #0x310; and sp, x9, #~31", up to 16 of         *)
(* padding, and 688 for the largest callee, mlkem_poly_invntt_tomont. The    *)
(* proof is by cases on whether the stack pointer is a multiple of 32, which *)
(* gives the address b of the buffers, at offsets 0 (the multiplication      *)
(* cache), 768 (the product), 1280 (v), 1792 (s) and 3328 (u).               *)
(* ------------------------------------------------------------------------- *)

let DE3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`m:int64`; `c:int64`; `sk:int64`; `dk:byte list`; `ct:byte list`;
    `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 5664 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 5664):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 5584):int64)`
   ASSUME_TAC THENL
   [CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
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
     (parse_term("X"^string_of_int n))) (19--29);;

let DE3_CASE_TAC b =
  let st n = "s"^string_of_int n in
  SUBGOAL_THEN
   (subst [mk_small_numeral b,`n:num`]
     `aligned 16 (word_add (stackpointer:int64) (word n))`) ASSUME_TAC THENL
   [CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN DE3_CT_TAC THEN

  (*** The setup, the ciphertext and the secret key ***)

  ARM_STEPS_TAC DE3_EXEC (1--9) THEN DE3_BUFFER_TAC THEN
  ARM_STEPS_TAC DE3_EXEC (10--10) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC DE3_EXEC (11--19) THEN
  LOCAL_POLYVEC_DECOMPRESS_DU_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist ct MOD 2 EXP (8 * 960)`;
    `pc:num`; `read SP s`; `read X30 s`] 20 THEN
  DE3_UD_TAC b THEN
  ARM_STEPS_TAC DE3_EXEC (21--24) THEN
  LOCAL_POLY_DECOMPRESS_D4_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist(mlkem_slice 960 128 ct)`;
    `pc:num`; `read X30 s`] 25 THEN
  DE3_VD_TAC b THEN
  ARM_STEPS_TAC DE3_EXEC (26--29) THEN
  LOCAL_POLYVEC_FROMBYTES_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist dk`; `pc:num`; `read SP s`;
    `read X30 s`] 30 THEN
  DE3_SS_TAC b THEN

  (*** The NTT of u and its multiplication cache, the product with s ***)

  DE3_UD_BOUND_TAC THEN
  ARM_STEPS_TAC DE3_EXEC (31--32) THEN
  LOCAL_POLYVEC_NTT_TAC
   [`read X0 s`; `UD:num->int16`; `pc:num`; `read SP s`; `read X30 s`]
   33 THEN
  DE3_UH_TAC b THEN
  ARM_STEPS_TAC DE3_EXEC (34--37) THEN
  LOCAL_POLYVEC_MULCACHE_TAC
   [`read X0 s`; `read X1 s`; `UH:num->int16`; `pc:num`; `read SP s`;
    `read X30 s`] 38 THEN
  INDCPA_MULCACHE_TAC "MC" b 3 "UH" (st 38) THEN
  ARM_STEPS_TAC DE3_EXEC (39--44) THEN
  INDCPA_BASEMULK_PRE_TAC 3 (b + 1792,"SS",0) (b + 3328,"UH") (b,"MC")
    (st 44) THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 3 ("SS",0) "UH" "MC") 45 THEN
  INDCPA_BASEMULK_DROP_PRE_TAC 3 (b + 1792,"SS",0) (b + 3328,"UH") (b,"MC")
    THEN
  DE3_SS_BOUND_TAC THEN DE3_WP_TAC b THEN

  (*** The inverse NTT, the subtraction from v, the reduction ***)

  ARM_STEPS_TAC DE3_EXEC (46--47) THEN
  LOCAL_POLY_INVNTT_TAC
   [`read X0 s`; `WP:num->int16`; `pc:num`; `read SP s`; `read X30 s`]
   48 THEN
  INDCPA_INVNTT1_TAC "WI" (b + 768) "WP" (st 48) THEN
  ARM_STEPS_TAC DE3_EXEC (49--51) THEN
  LOCAL_POLY_SUB_TAC
   [`read X0 s`; `read X1 s`; `VD:num->int16`; `WI:num->int16`; `pc:num`;
    `read X30 s`] 52 THEN
  ARM_STEPS_TAC DE3_EXEC (53--54) THEN
  LOCAL_POLY_REDUCE_TAC
   [`read X0 s`; `\i. word_sub ((VD:num->int16) i) ((WI:num->int16) i)`;
    `pc:num`; `read X30 s`] 55 THEN
  INDCPA_REDUCE_TAC "VR" (b + 1280) 256
    "word_sub ((VD:num->int16) i) ((WI:num->int16) i)" (st 55) THEN

  (*** The message ***)

  ARM_STEPS_TAC DE3_EXEC (56--58) THEN
  LOCAL_POLY_TOMSG_TAC
   [`read X0 s`; `read X1 s`; `VR:num->int16`; `pc:num`; `read SP s`;
    `read X30 s`] 59 THEN
  DE3_TOMSG_POST_TAC THEN

  (*** Zeroing the buffers, the stack guard, the return ***)

  INDCPA_MEMSET_LABEL_TAC THEN
  INDCPA_MEMSETS_TAC DE3_EXEC [60,63; 69,129; 135,138] THEN
  ARM_STEPS_TAC DE3_EXEC (144--144) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC DE3_EXEC (145--157) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DE3_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_DEC_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!m c sk (dk:byte list) (ct:byte list) guard mf ea el ev pc
    stackpointer returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        LENGTH dk = 1152 /\ LENGTH ct = 1088 /\
        nonoverlapping (m,32) (word_sub stackpointer (word 5664),5664) /\
        nonoverlapping (c,1088) (word pc,libmlkem_size) /\
        nonoverlapping (sk,1152) (word pc,libmlkem_size) /\
        ALLPAIRS nonoverlapping
         [(m,32); (word_sub stackpointer (word 5664),5664)]
         [(c,1088); (sk,1152); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem768_indcpa_dec) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [m; c; sk] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(c,1088)) s = num_of_bytelist ct /\
                  read (memory :> bytes(sk,1152)) s = num_of_bytelist dk)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(m,32)) s =
                  num_of_bytelist(kpke_decrypt mlkem768 dk ct) /\
                  C_RETURN s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(m,32);
                memory :> bytes(word_sub stackpointer (word 5664),5664)])`;;

let MLKEM_NATIVE_INDCPA_DEC_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_INDCPA_DEC_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contract for memset. The events depend only on the addresses of the       *)
(* arguments, the stack and the image, not on the ciphertext or the key. As  *)
(* for the correctness proof, the proof is by cases on whether the stack     *)
(* pointer is a multiple of 32, with the events of the two cases as the two  *)
(* branches of the template DE3_SAFE_TEMPLATE.                               *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** Stack addresses in the form word_add stackpointer (word n) ***)

let DE3_NORMALIZE_TAC =
  let conv =
    REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
    DEPTH_CONV NUM_ADD_CONV in
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE conv th else th);;

let DE3_ALLOWED =
  [`pc:num`; `m:int64`; `c:int64`; `sk:int64`; `guard:int64`; `mf:int64`;
   `stackpointer:int64`; `returnaddress:int64`];;

let DE3_SAFE_CALL_TAC name ilist n =
  DE3_NORMALIZE_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,DE3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref DE3_ALLOWED); LABEL_TAC name safety_th]);;

let DE3_SAFE_TEMPLATE =
 `\(m:int64) (c:int64) (sk:int64) (guard:int64) (mf:int64) (pc:num)
   (stackpointer:int64) (returnaddress:int64).
   if aligned 32 stackpointer
   then f_ev_a m c sk guard mf pc stackpointer returnaddress
   else f_ev_u m c sk guard mf pc stackpointer returnaddress
   :(uarch_event)list`;;

let DE3_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_safety_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
    "H_DECOMPRESS_DU" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_DECOMPRESS_D4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
    "H_DECOMPRESS_DV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
    "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_NTT_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_BASEMUL_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE "H_BASEMUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
    "H_INVNTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_SUB_CLANG17_O3_IMAGE_SUBROUTINE_SAFE "H_SUB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_TOMSG_CLANG17_O3_IMAGE_SUBROUTINE_SAFE "H_TOMSG" THEN
  CONCRETIZE_F_EVENTS_TAC DE3_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 5664):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 5584):int64)`
   ASSUME_TAC THENL
   [CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
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
     (parse_term("X"^string_of_int n))) (19--29);;

let DE3_SAFE_CASE_TAC b =
  SUBGOAL_THEN
   (subst [mk_small_numeral b,`n:num`]
     `aligned 16 (word_add (stackpointer:int64) (word n))`) ASSUME_TAC THENL
   [CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC DE3_EXEC (1--9) THEN DE3_BUFFER_TAC THEN
  ARM_STEPS_TAC DE3_EXEC (10--10) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC DE3_EXEC (11--19) THEN
  DE3_SAFE_CALL_TAC "H_DECOMPRESS_DU"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read SP s`;
    `read X30 s`] 20 THEN
  ARM_STEPS_TAC DE3_EXEC (21--24) THEN
  DE3_SAFE_CALL_TAC "H_DECOMPRESS_DV"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read X30 s`]
   25 THEN
  ARM_STEPS_TAC DE3_EXEC (26--29) THEN
  DE3_SAFE_CALL_TAC "H_FROMBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read SP s`;
    `read X30 s`] 30 THEN
  ARM_STEPS_TAC DE3_EXEC (31--32) THEN
  DE3_SAFE_CALL_TAC "H_NTT"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`; `read X30 s`]
   33 THEN
  ARM_STEPS_TAC DE3_EXEC (34--37) THEN
  DE3_SAFE_CALL_TAC "H_MULCACHE"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read SP s`;
    `read X30 s`] 38 THEN
  ARM_STEPS_TAC DE3_EXEC (39--44) THEN
  DE3_SAFE_CALL_TAC "H_BASEMUL"
   [`e:(uarch_event)list`; `read X1 s`; `read X2 s`; `read X3 s`;
    `read X0 s`; `pc:num`; `read X30 s`] 45 THEN
  ARM_STEPS_TAC DE3_EXEC (46--47) THEN
  DE3_SAFE_CALL_TAC "H_INVNTT"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`; `read X30 s`]
   48 THEN
  ARM_STEPS_TAC DE3_EXEC (49--51) THEN
  DE3_SAFE_CALL_TAC "H_SUB"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read X30 s`]
   52 THEN
  ARM_STEPS_TAC DE3_EXEC (53--54) THEN
  DE3_SAFE_CALL_TAC "H_REDUCE"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read X30 s`] 55 THEN
  ARM_STEPS_TAC DE3_EXEC (56--58) THEN
  DE3_SAFE_CALL_TAC "H_TOMSG"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read SP s`;
    `read X30 s`] 59 THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC DE3_EXEC (k0--k) THEN LIBC_PLT_TAC DE3_EXEC k THEN
    DE3_NORMALIZE_TAC THEN
    LIBC_SAFE_CALL_TAC "H_MEMSET" DE3_EXEC
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
      `read X30 s`] (ref DE3_ALLOWED) (k + 5))
   [60,63; 69,129; 135,138] THEN
  ARM_STEPS_TAC DE3_EXEC (144--144) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC DE3_EXEC (145--157) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_DEC_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_safety_contract mf ea el ev
     ==> exists f_events.
          forall e m c sk guard pc stackpointer returnaddress.
            aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
            aligned 16 stackpointer /\
            nonoverlapping (m,32) (word_sub stackpointer (word 5664),5664) /\
            nonoverlapping (c,1088) (word pc,libmlkem_size) /\
            nonoverlapping (sk,1152) (word pc,libmlkem_size) /\
            ALLPAIRS nonoverlapping
             [(m,32); (word_sub stackpointer (word 5664),5664)]
             [(c,1088); (sk,1152); (word pc,libmlkem_size);
              (word(pc + got_stack_chk_guard),8);
              (guard,8); (word(pc + got_memset),8); (ea,el)]
            ==> ensures arm
                 (\s. aligned_bytes_loaded s (word pc)
                        mlkem_native_libmlkem_clang17_O3_mc /\
                      read PC s = word (pc + mlkem768_indcpa_dec) /\
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
                                (word_sub stackpointer (word 5664))
                                returnaddress /\
                         memaccess_inbounds e2
                          [c,1088; sk,1152; m,32;
                           word_sub stackpointer (word 5664),5664;
                           word(pc + got_stack_chk_guard),8; guard,8;
                           word(pc + got_memset),8;
                           ea,el;
                           word(pc + mlkem_poly_decompress_d10_consts),
                           mlkem_poly_decompress_d10_consts_size;
                           word(pc + mlkem_poly_ntt_consts),
                           mlkem_poly_ntt_consts_size;
                           word(pc + mlkem_poly_mulcache_compute_consts),
                           mlkem_poly_mulcache_compute_consts_size;
                           word(pc + mlkem_poly_invntt_tomont_consts),
                           mlkem_poly_invntt_tomont_consts_size;
                           word(pc + mlkem_poly_tomsg_consts),
                           mlkem_poly_tomsg_consts_size;
                           word(pc + rodata_mlk_zetas),256]
                          [m,32; word_sub stackpointer (word 5664),5664]))
                 (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                  MAYCHANGE [X18] ,,
                  MAYCHANGE
                   [memory :> bytes(m,32);
                    memory :> bytes(word_sub stackpointer (word 5664),5664)])`;;

let MLKEM_NATIVE_INDCPA_DEC_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_INDCPA_DEC_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
