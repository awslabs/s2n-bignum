(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decryption of K-PKE for ML-KEM-768 (FIPS 203 Algorithm 15). This is   *)
(* the code for mlkem768_indcpa_dec from mlkem-native's portable C           *)
(* implementation compiled by gcc 12 with -O3 (see mlkem_native/README.md).  *)
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
(* At -O3 the code is the same, but the callees use more stack below the     *)
(* stack pointer (polyvec_frombytes and poly_tomsg 64 bytes, basemul_k3 48,  *)
(* polyvec_ntt 48, polyvec_mulcache_compute 48, poly_invntt_tomont 32), so   *)
(* this function and its deepest callee use 5024 bytes below the stack       *)
(* pointer (4960 + 64), not 4992. The safety theorem lists the constant      *)
(* blocks that the -O3 callees read, not the -O2 ones.                       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/polyvec_decompress_du_k3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/poly_decompress_d4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/polyvec_frombytes_k3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/polyvec_ntt_k3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/polyvec_mulcache_compute_k3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/basemul_k3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/poly_sub_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/poly_reduce_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/poly_tomsg_spec.ml";;
needs "arm/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image:

    mlkem768_indcpa_dec:
        +0x0: mov     x12, #0x1360
        +0x4: sub     sp, sp, x12
        +0x8: adrp    x3, <page>
        +0xc: ldr     x3, [x3, #4088]  // got_stack_chk_guard
       +0x10: stp     x19, x20, [sp]
       +0x14: add     x19, sp, #0x5f
       +0x18: and     x19, x19, #0xffffffffffffffe0
       +0x1c: stp     x21, x22, [sp, #16]
       +0x20: mov     x22, x2
       +0x24: mov     x2, #0x1100
       +0x28: stp     x23, x24, [sp, #32]
       +0x2c: add     x21, x19, x2
       +0x30: add     x20, x19, #0x600
       +0x34: str     x30, [sp, #48]
       +0x38: mov     x24, x0
       +0x3c: mov     x23, x1
       +0x40: mov     x0, x20
       +0x44: ldr     x2, [x3]
       +0x48: str     x2, [sp, #4952]
       +0x4c: mov     x2, #0x0
       +0x50: bl      <mlkem768_polyvec_decompress_du>
       +0x54: add     x1, x23, #0x3c0
       +0x58: mov     x0, x21
       +0x5c: bl      <mlkem_poly_decompress_d4>
       +0x60: add     x23, x19, #0xc00
       +0x64: mov     x1, x22
       +0x68: mov     x0, x19
       +0x6c: bl      <mlkem768_polyvec_frombytes>
       +0x70: add     x22, x19, #0xf00
       +0x74: mov     x0, x20
       +0x78: bl      <mlkem768_polyvec_ntt>
       +0x7c: mov     x1, x20
       +0x80: mov     x0, x23
       +0x84: bl      <mlkem768_polyvec_mulcache_compute>
       +0x88: mov     x3, x23
       +0x8c: mov     x2, x20
       +0x90: mov     x1, x19
       +0x94: mov     x0, x22
       +0x98: bl      <mlkem768_polyvec_basemul_acc_montgomery_cached>
       +0x9c: mov     x0, x22
       +0xa0: bl      <mlkem_poly_invntt_tomont>
       +0xa4: mov     x1, x22
       +0xa8: mov     x0, x21
       +0xac: bl      <mlkem_poly_sub>
       +0xb0: mov     x0, x21
       +0xb4: bl      <mlkem_poly_reduce>
       +0xb8: mov     x1, x21
       +0xbc: mov     x0, x24
       +0xc0: bl      <mlkem_poly_tomsg>
       +0xc4: mov     x0, x23
       +0xc8: mov     x2, #0x300
       +0xcc: mov     w1, #0x0
       +0xd0: bl      <memset@plt>
       +0xd4: mov     x2, #0x200
       +0xd8: mov     x0, x22
       +0xdc: mov     w1, #0x0
       +0xe0: bl      <memset@plt>
       +0xe4: mov     x2, #0x200
       +0xe8: mov     x0, x21
       +0xec: mov     w1, #0x0
       +0xf0: bl      <memset@plt>
       +0xf4: mov     x2, #0x600
       +0xf8: mov     x0, x19
       +0xfc: mov     w1, #0x0
      +0x100: bl      <memset@plt>
      +0x104: mov     x2, #0x600
      +0x108: mov     x0, x20
      +0x10c: mov     w1, #0x0
      +0x110: bl      <memset@plt>
      +0x114: adrp    x0, <page>
      +0x118: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x11c: ldr     x2, [sp, #4952]
      +0x120: ldr     x1, [x0]
      +0x124: subs    x2, x2, x1
      +0x128: mov     x1, #0x0
      +0x12c: b.ne    <mlkem768_indcpa_dec+0x150>
      +0x130: ldp     x19, x20, [sp]
      +0x134: mov     w0, #0x0
      +0x138: ldp     x21, x22, [sp, #16]
      +0x13c: mov     x12, #0x1360
      +0x140: ldp     x23, x24, [sp, #32]
      +0x144: ldr     x30, [sp, #48]
      +0x148: add     sp, sp, x12
      +0x14c: ret
      +0x150: bl      <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_INDCPA_DEC_K3_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "plt_memset"; layout_range "mlkem768_indcpa_dec"];;

let DE3_EXEC = MLKEM_NATIVE_INDCPA_DEC_K3_GCC12_O3_EXEC;;

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
        ==> word_and (word_add sp (word 159)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 128 else 144))`;;

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
  INDCPA_GHOST_TAC "UD" (b + 1536) 768 "s22" THEN
  SUBGOAL_THEN
   `!i. i < 768
        ==> (UD:num->int16) i =
            word((3329 * (num_of_bytelist ct DIV 2 EXP (10 * i)) MOD
                  2 EXP 10 + 512) DIV 1024)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "UD" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s22:armstate` (frees(concl th)) && is_forall(concl th) &&
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
  INDCPA_GHOST_TAC "VD" (b + 4352) 256 "s26" THEN
  SUBGOAL_THEN
   `!i. i < 256
        ==> (VD:num->int16) i =
            word((3329 * (num_of_bytelist(mlkem_slice 960 128 ct) DIV
                          2 EXP (4 * i)) MOD 2 EXP 4 + 8) DIV 16)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "VD" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem `s26:armstate` (frees(concl th)) && is_forall(concl th) &&
      can (find_term ((=) `num_of_bytelist(mlkem_slice 960 128 ct)`))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

let DE3_SS_TAC b =
  INDCPA_GHOST_TAC "SS" b 768 "s31" THEN
  SUBGOAL_THEN
   `!i. i < 768
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
  let st = `s35:armstate` and srct = `UD:num->int16` in
  INDCPA_GHOST_TAC "UH" (b + 1536) 768 "s35" THEN
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
  INDCPA_GHOST_TAC "WP" (b + 3840) 256 "s45" THEN
  SUBGOAL_THEN DE3_WP_GOAL ASSUME_TAC THENL
   [INDCPA_BASEMUL3_ROW_TAC "WP" (b + 3840) "ssbound" [] DE3_BASEMUL_DEFS;
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
   (mlkem_native_libmlkem_gcc12_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K3_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_DECOMPRESS_D4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_FROMBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K3_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_NTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_MULCACHE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
   );;

(*** The arguments of basemul_k3 as INDCPA_BASEMUL3_ARGS, but with the
 *** stack pointer before the return address, since the theorems of
 *** basemul_k3 at -O3 quantify over it ***)

let INDCPA_BASEMUL3_SP_ARGS a b t =
  let r = List.rev (INDCPA_BASEMUL3_ARGS a b t) in
  List.rev (List.hd r :: `read SP s` :: List.tl r);;

let LOCAL_BASEMUL_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_INVNTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_SUB_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_SUB_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_TOMSG_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,DE3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset. The ciphertext ct of *)
(* 1088 bytes is at c and the decryption key dk of 1152 bytes at sk, and the *)
(* message of 32 bytes written at m is kpke_decrypt mlkem768 dk ct in        *)
(* common/fips203.ml, for any dk (FIPS 203 decodes s modulo q, while the     *)
(* code multiplies by the 12-bit fields, which are congruent). The stack is  *)
(* the 4960 bytes of the function and the 64 used by its callees below them. *)
(* The proof is by cases on whether the stack pointer is a multiple of 32,   *)
(* which gives the address b of the buffers, at offsets 0 (s), 1536 (u),     *)
(* 3072 (the multiplication cache), 3840 (the product) and 4352 (v).         *)
(* ------------------------------------------------------------------------- *)

let DE3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`m:int64`; `c:int64`; `sk:int64`; `dk:byte list`; `ct:byte list`;
    `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 5024 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 5024):int64)` THEN
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

let DE3_CASE_TAC b =
  let st n = "s"^string_of_int n in
  ENSURES_INIT_TAC "s0" THEN DE3_CT_TAC THEN

  (*** The setup, the ciphertext and the secret key ***)

  ARM_STEPS_TAC DE3_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC DE3_EXEC (4--7) THEN DE3_BUFFER_TAC THEN
  ARM_STEPS_TAC DE3_EXEC (8--21) THEN
  LOCAL_POLYVEC_DECOMPRESS_DU_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist ct MOD 2 EXP (8 * 960)`;
    `pc:num`; `read SP s`; `read X30 s`] 22 THEN
  DE3_UD_TAC b THEN
  ARM_STEPS_TAC DE3_EXEC (23--25) THEN
  LOCAL_POLY_DECOMPRESS_D4_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist(mlkem_slice 960 128 ct)`;
    `pc:num`; `read X30 s`] 26 THEN
  DE3_VD_TAC b THEN
  ARM_STEPS_TAC DE3_EXEC (27--30) THEN
  LOCAL_POLYVEC_FROMBYTES_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist dk`; `pc:num`; `read SP s`;
    `read X30 s`] 31 THEN
  DE3_SS_TAC b THEN

  (*** The NTT of u and its multiplication cache, the product with s ***)

  DE3_UD_BOUND_TAC THEN
  ARM_STEPS_TAC DE3_EXEC (32--34) THEN
  LOCAL_POLYVEC_NTT_TAC
   [`read X0 s`; `UD:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 35 THEN
  DE3_UH_TAC b THEN
  ARM_STEPS_TAC DE3_EXEC (36--38) THEN
  LOCAL_POLYVEC_MULCACHE_TAC
   [`read X0 s`; `read X1 s`; `UH:num->int16`; `pc:num`; `read SP s`;
    `read X30 s`] 39 THEN
  INDCPA_MULCACHE_TAC "MC" (b + 3072) 3 "UH" (st 39) THEN
  ARM_STEPS_TAC DE3_EXEC (40--44) THEN
  INDCPA_BASEMUL3_PRE_TAC (b,"SS",0) (b + 1536,"UH") (b + 3072,"MC")
    (st 44) THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMUL3_SP_ARGS ("SS",0) "UH" "MC") 45 THEN
  INDCPA_BASEMUL3_DROP_PRE_TAC (b,"SS",0) (b + 1536,"UH")
    (b + 3072,"MC") THEN
  DE3_SS_BOUND_TAC THEN DE3_WP_TAC b THEN

  (*** The inverse NTT, the subtraction from v, the reduction ***)

  ARM_STEPS_TAC DE3_EXEC (46--47) THEN
  LOCAL_POLY_INVNTT_TAC
   [`read X0 s`; `WP:num->int16`; `pc:num`; `read SP s`; `read X30 s`]
   48 THEN
  INDCPA_INVNTT1_TAC "WI" (b + 3840) "WP" (st 48) THEN
  ARM_STEPS_TAC DE3_EXEC (49--51) THEN
  LOCAL_POLY_SUB_TAC
   [`read X0 s`; `read X1 s`; `VD:num->int16`; `WI:num->int16`; `pc:num`;
    `read X30 s`] 52 THEN
  ARM_STEPS_TAC DE3_EXEC (53--54) THEN
  LOCAL_POLY_REDUCE_TAC
   [`read X0 s`; `\i. word_sub ((VD:num->int16) i) ((WI:num->int16) i)`;
    `pc:num`; `read X30 s`] 55 THEN
  INDCPA_REDUCE_TAC "VR" (b + 4352) 256
    "word_sub ((VD:num->int16) i) ((WI:num->int16) i)" (st 55) THEN

  (*** The message ***)

  ARM_STEPS_TAC DE3_EXEC (56--58) THEN
  LOCAL_POLY_TOMSG_TAC
   [`read X0 s`; `read X1 s`; `VR:num->int16`; `pc:num`; `read SP s`;
    `read X30 s`]
   59 THEN
  DE3_TOMSG_POST_TAC THEN

  (*** Zeroing the buffers, the stack guard, the return ***)

  INDCPA_MEMSET_LABEL_TAC THEN
  INDCPA_MEMSETS_TAC DE3_EXEC
   [60,63; 69,72; 78,81; 87,90; 96,99] THEN
  ARM_STEPS_TAC DE3_EXEC (105--105) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC DE3_EXEC (106--119) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DE3_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_DEC_K3_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!m c sk (dk:byte list) (ct:byte list) guard mf ea el ev pc
    stackpointer returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        LENGTH dk = 1152 /\ LENGTH ct = 1088 /\
        nonoverlapping (m,32) (word_sub stackpointer (word 5024),5024) /\
        nonoverlapping (c,1088) (word pc,libmlkem_size) /\
        nonoverlapping (sk,1152) (word pc,libmlkem_size) /\
        ALLPAIRS nonoverlapping
         [(m,32); (word_sub stackpointer (word 5024),5024)]
         [(c,1088); (sk,1152); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
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
                memory :> bytes(word_sub stackpointer (word 5024),5024)])`;;

let MLKEM_NATIVE_INDCPA_DEC_K3_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_INDCPA_DEC_K3_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contract for memset. The events depend only on the addresses of the       *)
(* arguments, the stack and the image, not on the ciphertext or the key. The *)
(* buffers are kept at stackpointer + b with b the conditional offset (128 or *)
(* 144), so the two cases need not be separated.                             *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let DE3_SAFE_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 159))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 128 else 144))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC DE3_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

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
      (mlkem_native_libmlkem_gcc12_O3_mc,DE3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref DE3_ALLOWED); LABEL_TAC name safety_th]);;

let DE3_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_safety_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_DECOMPRESS_DU_K3_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_DECOMPRESS_DU" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_DECOMPRESS_DV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K3_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O3_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_IMAGE_SUBROUTINE_SAFE "H_BASEMUL" THEN
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
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 5024):int64)` THEN
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

let DE3_SAFE_MAIN_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC DE3_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC DE3_EXEC (4--7) THEN DE3_SAFE_BUFFER_TAC THEN
  ARM_STEPS_TAC DE3_EXEC (8--21) THEN
  DE3_SAFE_CALL_TAC "H_DECOMPRESS_DU"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read SP s`;
    `read X30 s`] 22 THEN
  ARM_STEPS_TAC DE3_EXEC (23--25) THEN
  DE3_SAFE_CALL_TAC "H_DECOMPRESS_DV"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read X30 s`]
   26 THEN
  ARM_STEPS_TAC DE3_EXEC (27--30) THEN
  DE3_SAFE_CALL_TAC "H_FROMBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read SP s`;
    `read X30 s`] 31 THEN
  ARM_STEPS_TAC DE3_EXEC (32--34) THEN
  DE3_SAFE_CALL_TAC "H_NTT"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`; `read X30 s`]
   35 THEN
  ARM_STEPS_TAC DE3_EXEC (36--38) THEN
  DE3_SAFE_CALL_TAC "H_MULCACHE"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read SP s`;
    `read X30 s`] 39 THEN
  ARM_STEPS_TAC DE3_EXEC (40--44) THEN
  DE3_SAFE_CALL_TAC "H_BASEMUL"
   [`e:(uarch_event)list`; `read X1 s`; `read X2 s`; `read X3 s`;
    `read X0 s`; `pc:num`; `read SP s`; `read X30 s`] 45 THEN
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
    `read X30 s`]
   59 THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC DE3_EXEC (k0--k) THEN LIBC_PLT_TAC DE3_EXEC k THEN
    LIBC_SAFE_CALL_TAC "H_MEMSET" DE3_EXEC
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
      `read X30 s`] (ref DE3_ALLOWED) (k + 5))
   [60,63; 69,72; 78,81; 87,90; 96,99] THEN
  ARM_STEPS_TAC DE3_EXEC (105--105) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC DE3_EXEC (106--119) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_DEC_K3_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_safety_contract mf ea el ev
     ==> exists f_events.
          forall e m c sk guard pc stackpointer returnaddress.
            aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
            aligned 16 stackpointer /\
            nonoverlapping (m,32) (word_sub stackpointer (word 5024),5024) /\
            nonoverlapping (c,1088) (word pc,libmlkem_size) /\
            nonoverlapping (sk,1152) (word pc,libmlkem_size) /\
            ALLPAIRS nonoverlapping
             [(m,32); (word_sub stackpointer (word 5024),5024)]
             [(c,1088); (sk,1152); (word pc,libmlkem_size);
              (word(pc + got_stack_chk_guard),8);
              (guard,8); (word(pc + got_memset),8); (ea,el)]
            ==> ensures arm
                 (\s. aligned_bytes_loaded s (word pc)
                        mlkem_native_libmlkem_gcc12_O3_mc /\
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
                                (word_sub stackpointer (word 5024))
                                returnaddress /\
                         memaccess_inbounds e2
                          [c,1088; sk,1152; m,32;
                           word_sub stackpointer (word 5024),5024;
                           word(pc + got_stack_chk_guard),8; guard,8;
                           word(pc + got_memset),8;
                           ea,el;
                           word(pc + mlkem_poly_decompress_d4_consts),16;
                           word(pc + rodata_mlk_zetas),256;
                           word(pc + mlkem_poly_ntt_consts),
                           mlkem_poly_ntt_consts_size:num;
                           word(pc + mlkem_poly_mulcache_compute_consts),
                           mlkem_poly_mulcache_compute_consts_size:num;
                           word(pc + mlkem768_polyvec_basemul_acc_montgomery_cached_consts),
                           mlkem768_polyvec_basemul_acc_montgomery_cached_consts_size:num;
                           word(pc + mlkem_poly_invntt_tomont_consts),
                           mlkem_poly_invntt_tomont_consts_size:num;
                           word(pc + mlkem_poly_tomsg_consts),16]
                          [m,32; word_sub stackpointer (word 5024),5024]))
                 (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                  MAYCHANGE [X18] ,,
                  MAYCHANGE
                   [memory :> bytes(m,32);
                    memory :> bytes(word_sub stackpointer (word 5024),5024)])`;;

let MLKEM_NATIVE_INDCPA_DEC_K3_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_INDCPA_DEC_K3_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
