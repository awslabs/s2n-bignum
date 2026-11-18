(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decapsulation of ML-KEM-512 (FIPS 203 Algorithm 18, with the input    *)
(* check of Algorithm 21). This is the code for mlkem512_dec from mlkem-     *)
(* native's portable C implementation compiled by gcc 12 with -O2 as one     *)
(* translation unit (see mlkem_native/README.md). It checks the              *)
(* decapsulation key with mlkem512_check_sk, and returns -5 if the check     *)
(* fails. Otherwise it decrypts the ciphertext into m' (the inlined          *)
(* mlkem512_indcpa_dec), computes K' and r' as G of m' followed by the hash  *)
(* h in the key with mlkem_sha3_512, encrypts m' with r' again by            *)
(* mlkem512_indcpa_enc, compares the result with the ciphertext in constant  *)
(* time, computes J of z (in the key) followed by the ciphertext into the    *)
(* shared secret with mlkem_shake256, and replaces it by K' if the           *)
(* ciphertexts are equal, again in constant time. In both cases it zeroes    *)
(* its buffers. It is verified in the whole image (see libmlkem.ml), using   *)
(* the theorems for mlkem512_check_sk, mlk_poly_decompress_d10_c,            *)
(* mlk_poly_decompress_d4_c, mlk_poly_frombytes_c, mlk_poly_ntt_c,           *)
(* mlk_poly_mulcache_compute_c,                                              *)
(* mlk_polyvec_basemul_acc_montgomery_cached_c512,                           *)
(* mlk_poly_invntt_tomont_c, mlk_poly_reduce_c, mlkem_poly_tomsg,            *)
(* mlkem_sha3_512, mlkem512_indcpa_enc and mlkem_shake256 in the image and   *)
(* the contracts for memset and memcpy.                                      *)
(*                                                                           *)
(* Differences from the gcc 12 -O2 proof. gcc has inlined                    *)
(* mlkem512_indcpa_dec, and in it the polyvec functions and poly_sub. Its    *)
(* code is contiguous (from in_indcpa_dec to in_indcpa_dec_end), so it is    *)
(* proved as a lemma with the postcondition of the gcc 12 -O2 indcpa_dec,    *)
(* from the proof of the gcc 12 -O2 indcpa_dec with the glue for the         *)
(* polyvec functions and the poly_sub loop as a lemma itself; the rest is    *)
(* the gcc 12 -O2 proof of mlkem512_dec, with the buffers of indcpa_dec      *)
(* now in this frame. The comparison of the ciphertexts keeps an XOR         *)
(* accumulator besides the OR accumulator, from which the mask is computed   *)
(* in another way, with the same result.                                     *)
(*                                                                           *)
(* The frame is the 4624 bytes of the function and the 12016 of              *)
(* mlkem512_indcpa_enc below them, 16640 in all.                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/check_sk_k2_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/sha3_512_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/indcpa_enc_k2_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/shake256_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_decompress_d10_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_decompress_d4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_frombytes_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_ntt_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_mulcache_compute_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/basemul_k2_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_reduce_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_tomsg_spec.ml";;
needs "arm/proofs/mlkem_native/indcpa_inline.ml";;
needs "arm/proofs/mlkem_native/inline_loops.ml";;
needs "arm/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image is listed at the end of layout.ml, with the
     labels of the inlined calls. ***)

let MLKEM_NATIVE_DEC_K2_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "plt_memcpy"; layout_range "plt_memset";
    layout_range "mlkem512_dec"];;

let KD2_EXEC = MLKEM_NATIVE_DEC_K2_GCC12_O2_MONO_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The decryption in FIPS 203 in terms of the values computed by the code:   *)
(* the decompressed u and v, the 12-bit fields of the decryption key as      *)
(* decoded (which may be >= q), the NTT of u and its multiplication cache,   *)
(* the product with s in Montgomery form, its inverse NTT, and the result    *)
(* after the subtraction from v and the reduction, whose compression is the  *)
(* message.                                                                  *)
(* ------------------------------------------------------------------------- *)

let KPKE_DECRYPT_K2_RESULT_STMT =
  `!dk ct (UD:num->int16) (VD:num->int16) (SS:num->int16) (UH:num->int16)
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
         num_of_bytelist(kpke_decrypt mlkem512 dk ct)`;;

let KPKE_DECRYPT_K2_RESULT = assume_spec KPKE_DECRYPT_K2_RESULT_STMT;;


(* ------------------------------------------------------------------------- *)
(* The inlined mlkem512_indcpa_dec, from in_indcpa_dec to in_indcpa_dec_end, *)
(* as a lemma with the postcondition of the gcc 12 -O2 indcpa_dec: the       *)
(* message m' at stackpointer + b + 4448 (with X27 pointing to it) is        *)
(* kpke_decrypt mlkem512 dk ct, for the decryption key dk at sk (X20) and    *)
(* the ciphertext ct at c (X22). Its buffers are in the frame of             *)
(* mlkem512_dec, at offsets from b: 0 (s), 1024 (u), 2848 (the cache of the  *)
(* NTT of u), 3360 (the product), 3872 (v) and 4448 (m'); the gcc 12 -O2     *)
(* function had them at 0, 1024, 2048, 2560 and 3072 in its own frame. The   *)
(* proof is that of the gcc 12 -O2 function, with the glue for the inlined   *)
(* polyvec functions and the poly_sub loop as a lemma.                       *)
(* ------------------------------------------------------------------------- *)

(*** The two halves of the 640 bytes of the compressed u, and the 10-bit
     fields of each ***)

let KD2_DU_SPLIT_STMT =
  `!a k n s j.
        read (memory :> bytes(a,320 * k)) s = n /\ j < k
        ==> read (memory :> bytes(word_add a (word(320 * j)),320)) s =
            (n DIV 2 EXP (2560 * j)) MOD 2 EXP 2560`;;

let KD2_DU_SPLIT = assume_spec KD2_DU_SPLIT_STMT;;

let KD2_DU_FIELD_STMT =
  `!n k i.
        i < 256
        ==> ((n DIV 2 EXP k) MOD 2 EXP 2560 DIV 2 EXP (10 * i)) MOD 2 EXP 10 =
            (n DIV 2 EXP (k + 10 * i)) MOD 2 EXP 10`;;

let KD2_DU_FIELD = assume_spec KD2_DU_FIELD_STMT;;

let KD2_CT_TAC =
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

(*** The stages, as for gcc 12 -O2 with the offsets of this frame and the
     state as a parameter ***)

let KD2_UD_TAC b s =
  INDCPA_GHOST_TAC "UD" (b + 1024) 512 s THEN
  SUBGOAL_THEN
   `!i. i < 512
        ==> (UD:num->int16) i =
            word((3329 * (num_of_bytelist ct DIV 2 EXP (10 * i)) MOD
                  2 EXP 10 + 512) DIV 1024)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "UD" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem (mk_var(s,`:armstate`)) (frees(concl th)) && is_forall(concl th) &&
      free_in `ctt:num` (concl th) &&
      can (find_term ((=) `512`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN EXPAND_TAC "ctt" THEN MATCH_MP_TAC DIV_MOD_EXP_LOW THEN
    UNDISCH_TAC `i < 512` THEN ARITH_TAC;
    ALL_TAC];;

let KD2_VD_TAC b s =
  INDCPA_GHOST_TAC "VD" (b + 3872) 256 s THEN
  SUBGOAL_THEN
   `!i. i < 256
        ==> (VD:num->int16) i =
            word((3329 * (num_of_bytelist(mlkem_slice 640 128 ct) DIV
                          2 EXP (4 * i)) MOD 2 EXP 4 + 8) DIV 16)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "VD" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem (mk_var(s,`:armstate`)) (frees(concl th)) && is_forall(concl th) &&
      can (find_term ((=) `num_of_bytelist(mlkem_slice 640 128 ct)`))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

let KD2_SS_TAC b s =
  INDCPA_GHOST_TAC "SS" b 512 s THEN
  SUBGOAL_THEN
   `!i. i < 512
        ==> (SS:num->int16) i =
            word((num_of_bytelist dk DIV 2 EXP (12 * i)) MOD 2 EXP 12)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "SS" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem (mk_var(s,`:armstate`)) (frees(concl th)) && is_forall(concl th) &&
      can (find_term ((=) `num_of_bytelist dk`)) (concl th) &&
      can (find_term ((=) `512`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

let KD2_UD_BOUND_TAC =
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

let KD2_SS_BOUND_TAC =
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

let KD2_UH_TAC b s =
  let st = mk_var(s,`:armstate`) and srct = `UD:num->int16` in
  INDCPA_GHOST_TAC "UH" (b + 1024) 512 s THEN
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

let KD2_BASEMUL_DEFS =
  [basemul2_even; basemul2_odd; pmul_acc2; pmull_acc2; pmull];;

let KD2_WP_GOAL = `!p. p < 128
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

let KD2_WP_TAC b s =
  INDCPA_GHOST_TAC "WP" (b + 3360) 256 s THEN
  SUBGOAL_THEN KD2_WP_GOAL ASSUME_TAC THENL
   [INDCPA_BASEMULK_ROW_TAC 2 "WP" (b + 3360) "ssbound" [] KD2_BASEMUL_DEFS;
    ALL_TAC];;

let KD2_TOMSG_POST_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && mem `VR:num->int16` (frees(concl th)) &&
    INDCPA_HAS_CONST "nsum" (concl th))) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC VAL_LT_OF_IVAL_REM THEN
    EXISTS_TAC `ival(word_sub ((VD:num->int16) i) ((WI:num->int16) i))` THEN
    ASM_SIMP_TAC[];
    DISCH_TAC];;

let KD2_DEC_FINAL_TAC =
  MP_TAC(SPECL [`dk:byte list`; `ct:byte list`; `UD:num->int16`;
                `VD:num->int16`; `SS:num->int16`; `UH:num->int16`;
                `MC:num->int16`; `WP:num->int16`; `WI:num->int16`;
                `VR:num->int16`] KPKE_DECRYPT_K2_RESULT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
           REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
    SIMP_TAC[]];;

(*** The inlined loop of poly_sub, v -= the inverse NTT of the product ***)

let KD2_SUB = INLINE_PTR_LOOP "mlkem_native_libmlkem_gcc12_O2_mono_mc"
  KD2_EXEC "sub" "mlkem512_dec_loop1" "mlkem512_dec_loop1_exit"
  "X3" "X4" "X0";;

(*** The callees of the inlined indcpa_dec ***)

let KD2_SUB_TAC th =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,KD2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,th);;

let LOCAL_DECOMPRESS_D10_TAC =
  KD2_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_DECOMPRESS_D4_TAC =
  KD2_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_FROMBYTES_TAC =
  KD2_SUB_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_NTT_TAC =
  KD2_SUB_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_MULCACHE_TAC =
  KD2_SUB_TAC
   MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_BASEMUL_TAC =
  KD2_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_INVNTT_TAC =
  KD2_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REDUCE_TAC =
  KD2_SUB_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_TOMSG_TAC =
  KD2_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let KD2_SP n = Printf.sprintf "word_add stackpointer (word %d)" n;;

(*** The lemma, for the two values of b ***)

let KD2_DEC_GOAL b = parse_term(Printf.sprintf
 "!dk ct sk c mf ea el ev pc stackpointer.
    memset_contract mf ea el ev /\\
    aligned 4096 (word pc:int64) /\\ pc + libmlkem_size <= 2 EXP 64 /\\
    aligned 16 stackpointer /\\ LENGTH dk = 768 /\\ LENGTH ct = 768 /\\
    nonoverlapping (c,768) (word pc,libmlkem_size) /\\
    nonoverlapping (sk,768) (word pc,libmlkem_size) /\\
    ALLPAIRS nonoverlapping
     [(word_add stackpointer (word %d),4480);
      (word_add stackpointer (word 12000),16)]
     [(c,768); (sk,768); (word pc,libmlkem_size);
      (word(pc + got_memset),8); (ea,el)]
    ==> ensures arm
         (\\s. aligned_bytes_loaded s (word pc)
                mlkem_native_libmlkem_gcc12_O2_mono_mc /\\
              read PC s = word (pc + mlkem512_dec_in_indcpa_dec) /\\
              read SP s = word_add stackpointer (word 12016) /\\
              read X19 s = word_add stackpointer (word %d) /\\
              read X20 s = sk /\\ read X22 s = c /\\
              read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
              read (memory :> bytes(ea,el)) s = ev /\\
              read (memory :> bytes(c,768)) s = num_of_bytelist ct /\\
              read (memory :> bytes(sk,768)) s = num_of_bytelist dk)
         (\\s. read PC s = word (pc + mlkem512_dec_in_indcpa_dec_end) /\\
              read X27 s = word_add stackpointer (word %d) /\\
              read (memory :> bytes(word_add stackpointer (word %d),32)) s =
              num_of_bytelist(kpke_decrypt mlkem512 dk ct))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
          MAYCHANGE [X23; X24; X25; X26; X27; X30] ,,
          MAYCHANGE [memory :> bytes(word_add stackpointer (word %d),4480);
                     memory :> bytes(word_add stackpointer (word 12000),16)])"
  b b (b + 4448) (b + 4448) b);;

let KD2_DEC_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`dk:byte list`; `ct:byte list`; `sk:int64`; `c:int64`; `mf:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; ALLPAIRS] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memset:num`] WORD_ADD]);;

let KD2_DEC_TAC b =
  let st n = "s"^string_of_int n in
  let sp n = KD2_SP n in
  ENSURES_INIT_TAC "s0" THEN KD2_CT_TAC THEN
  POLYVEC_INLINE_SPLIT_TAC KD2_DU_SPLIT `c:int64` 2 THEN
  ABBREV_TAC `ctt = num_of_bytelist ct MOD 2 EXP 5120` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  POLYVEC_INLINE_SPLIT_TAC POLYVEC_FROMBYTES_SPLIT_GEN `sk:int64` 2 THEN

  (*** The decompressed u and v and the decoded s ***)

  ARM_STEPS_TAC KD2_EXEC (1--5) THEN
  LOCAL_DECOMPRESS_D10_TAC
   [`read X0 s`; `read X1 s`; `(ctt DIV 2 EXP 0) MOD 2 EXP 2560`; `pc:num`;
    `read X30 s`] 6 THEN
  ARM_STEPS_TAC KD2_EXEC (7--10) THEN
  LOCAL_DECOMPRESS_D10_TAC
   [`read X0 s`; `read X1 s`; `(ctt DIV 2 EXP 2560) MOD 2 EXP 2560`;
    `pc:num`; `read X30 s`] 11 THEN
  POLYVEC_INLINE_JOIN_TAC 2
   [KD2_DU_FIELD; ADD_CLAUSES; ARITH_RULE `1024 = 2 EXP 10`]
   (parse_term(Printf.sprintf
     "!i. i < 512
          ==> read(memory :> bytes16(word_add (%s:int64) (word(2 * i))))
               (s11:armstate) =
              word((3329 * (ctt DIV 2 EXP (10 * i)) MOD 2 EXP 10 + 512) DIV
                   1024)" (sp(b + 1024)))) THEN
  KD2_UD_TAC b (st 11) THEN
  ARM_STEPS_TAC KD2_EXEC (12--15) THEN
  LOCAL_DECOMPRESS_D4_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist(mlkem_slice 640 128 ct)`;
    `pc:num`; `read X30 s`] 16 THEN
  KD2_VD_TAC b (st 16) THEN
  ARM_STEPS_TAC KD2_EXEC (17--20) THEN
  LOCAL_FROMBYTES_TAC
   [`read X0 s`; `read X1 s`;
    `(num_of_bytelist dk DIV 2 EXP 0) MOD 2 EXP 3072`; `pc:num`;
    `read X30 s`] 21 THEN
  ARM_STEPS_TAC KD2_EXEC (22--24) THEN
  LOCAL_FROMBYTES_TAC
   [`read X0 s`; `read X1 s`;
    `(num_of_bytelist dk DIV 2 EXP 3072) MOD 2 EXP 3072`; `pc:num`;
    `read X30 s`] 25 THEN
  POLYVEC_INLINE_JOIN_TAC 2
   [POLYVEC_FROMBYTES_FIELD_GEN; ADD_CLAUSES; ARITH_RULE `4096 = 2 EXP 12`]
   (PV_FROMBYTES_POST 2 (sp b) "num_of_bytelist dk" (st 25)) THEN
  KD2_SS_TAC b (st 25) THEN

  (*** The NTT of u and its multiplication cache, the product with s ***)

  KD2_UD_BOUND_TAC THEN
  POLYVEC_GHOST_SPLIT_TAC "UD" (b + 1024) 2 (st 25) THEN
  ARM_STEPS_TAC KD2_EXEC (26--27) THEN
  LOCAL_NTT_TAC [`read X0 s`; `UD:num->int16`; `pc:num`; `read X30 s`] 28 THEN
  ARM_STEPS_TAC KD2_EXEC (29--30) THEN
  LOCAL_NTT_TAC [`read X0 s`; `\i. (UD:num->int16)(256 + i)`; `pc:num`;
                 `read X30 s`] 31 THEN
  POLYVEC_INLINE_JOIN_TAC 2 [] (PV_NTT_POST 2 (sp(b + 1024)) "UD" (st 31)) THEN
  KD2_UH_TAC b (st 31) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "UD" 512 THEN
  POLYVEC_GHOST_SPLIT_TAC "UH" (b + 1024) 2 (st 31) THEN
  ARM_STEPS_TAC KD2_EXEC (32--34) THEN
  LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; `UH:num->int16`; `pc:num`;
                      `read X30 s`] 35 THEN
  ARM_STEPS_TAC KD2_EXEC (36--38) THEN
  LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; `\i. (UH:num->int16)(256 + i)`;
                      `pc:num`; `read X30 s`] 39 THEN
  POLYVEC_INLINE_JOIN_TAC 2 []
   (PV_MULCACHE_POST 2 (sp(b + 2848)) "UH" (st 39)) THEN
  INDCPA_MULCACHE_TAC "MC" (b + 2848) 2 "UH" (st 39) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "UH" 512 THEN
  ARM_STEPS_TAC KD2_EXEC (40--44) THEN
  INDCPA_BASEMULK_PRE_TAC 2 (b,"SS",0) (b + 1024,"UH") (b + 2848,"MC")
    (st 44) THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 2 ("SS",0) "UH" "MC") 45 THEN
  INDCPA_BASEMULK_DROP_PRE_TAC 2 (b,"SS",0) (b + 1024,"UH")
    (b + 2848,"MC") THEN
  KD2_SS_BOUND_TAC THEN KD2_WP_TAC b (st 45) THEN

  (*** The inverse NTT, the subtraction from v, the reduction ***)

  ARM_STEPS_TAC KD2_EXEC (46--47) THEN
  LOCAL_INVNTT_TAC
   [`read X0 s`; `WP:num->int16`; `pc:num`; `read SP s`; `read X30 s`]
   48 THEN
  INDCPA_INVNTT1_TAC "WI" (b + 3360) "WP" (st 48) THEN
  ARM_STEPS_TAC KD2_EXEC (49--52) THEN
  USE_THEN "H_SUB" (fun th -> KD2_SUB_TAC th
   [`read events s`; `read X3 s`; `read X4 s`; `VD:num->int16`;
    `WI:num->int16`; `pc:num`] 53) THEN
  ARM_STEPS_TAC KD2_EXEC (54--57) THEN
  LOCAL_REDUCE_TAC
   [`read X0 s`; `\i. word_sub ((VD:num->int16) i) ((WI:num->int16) i)`;
    `pc:num`; `read X30 s`] 58 THEN
  INDCPA_REDUCE_TAC "VR" (b + 3872) 256
    "word_sub ((VD:num->int16) i) ((WI:num->int16) i)" (st 58) THEN

  (*** The message ***)

  ARM_STEPS_TAC KD2_EXEC (59--61) THEN
  LOCAL_TOMSG_TAC
   [`read X0 s`; `read X1 s`; `VR:num->int16`; `pc:num`; `read X30 s`]
   62 THEN
  KD2_TOMSG_POST_TAC THEN

  (*** Zeroing the buffers ***)

  INDCPA_MEMSET_LABEL_TAC THEN
  INDCPA_MEMSETS_TAC KD2_EXEC [63,66; 72,75; 81,84; 90,93; 99,102] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KD2_DEC_FINAL_TAC;;

let KD2_DEC_LEMMA b = prove
 (KD2_DEC_GOAL b,
  KD2_DEC_INTRO_TAC THEN
  X_CHOOSE_THEN `fs:int64->int64->num->(uarch_event)list`
    (LABEL_TAC "H_SUB") KD2_SUB THEN
  KD2_DEC_TAC b);;

let KD2_DEC_A = assuming_proofs (fun () -> KD2_DEC_LEMMA 12096);;
let KD2_DEC_U = assuming_proofs (fun () -> KD2_DEC_LEMMA 12112);;

(* ------------------------------------------------------------------------- *)
(* The lengths of the results of K-PKE for ML-KEM-512, the input check of    *)
(* FIPS 203 in terms of the result of mlkem512_check_sk, and the address of  *)
(* the buffers, which are aligned to 32 bytes within the stack frame.        *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_LENGTH_512_STMT =
  `!ek m r. LENGTH(kpke_encrypt mlkem512 ek m r) = 768`;;

let KPKE_ENCRYPT_LENGTH_512 = assume_spec KPKE_ENCRYPT_LENGTH_512_STMT;;

let KPKE_DECRYPT_LENGTH_512_STMT =
  `!dk c. LENGTH(kpke_decrypt mlkem512 dk c) = 32`;;

let KPKE_DECRYPT_LENGTH_512 = assume_spec KPKE_DECRYPT_LENGTH_512_STMT;;

let KD2_CHECK_STMT =
  `!dk c. LENGTH dk = 1632 /\ LENGTH c = 768
          ==> (mlkem_decaps_check mlkem512 dk c <=>
               num_of_bytelist(mlkem_slice 1568 32 dk) =
               num_of_bytelist(sha3_256(mlkem_slice 768 800 dk)))`;;

let KD2_CHECK = assume_spec KD2_CHECK_STMT;;

let KD2_ALIGNED_16_32_STMT =
  `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`;;

let KD2_ALIGNED_16_32 = assume_spec KD2_ALIGNED_16_32_STMT;;

let KD2_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 12127)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 12096 else 12112))`;;

let KD2_BUFFER_ADDRESS = assume_spec KD2_BUFFER_ADDRESS_STMT;;

let KD2_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KD2_BUFFER_ADDRESS))
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The callees, the slices of the decapsulation key, and the failure of the  *)
(* check of the key, after which the function only zeroes its buffers.       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CHECK_SK_TAC =
  KD2_SUB_TAC MLKEM_NATIVE_CHECK_SK_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_INDCPA_DEC_TAC b =
  KD2_SUB_TAC (if b = 12096 then KD2_DEC_A else KD2_DEC_U);;

let LOCAL_SHA3_512_TAC =
  KD2_SUB_TAC MLKEM_NATIVE_SHA3_512_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_INDCPA_ENC_TAC =
  KD2_SUB_TAC MLKEM_NATIVE_INDCPA_ENC_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_SHAKE256_TAC =
  KD2_SUB_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let KD2_SK_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(sk,1632)) s = num_of_bytelist dk`) (concl th)
    then
      let s = rand(lhand(concl th)) in
      MAP_EVERY (fun (k,n) ->
        MP_TAC(SPECL [`sk:int64`; `dk:byte list`; mk_small_numeral k;
                      mk_small_numeral n; s] READ_MEMORY_BYTES_SLICE) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC)
       [0,768; 768,800; 1568,32; 1600,32]
    else NO_TAC);;

let KD2_CHECK_TAC =
  LOCAL_CHECK_SK_TAC
   [`read X0 s`; `mlkem_slice 768 800 (dk:byte list)`;
    `num_of_bytelist(mlkem_slice 1568 32 (dk:byte list))`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 20;;

let KD2_FAIL_TAC =
  ARM_STEPS_TAC KD2_EXEC (21--31) THEN
  LIBC_PLT_TAC KD2_EXEC 31 THEN
  LIBC_CALL_TAC "H_MEMSET" KD2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 36 THEN
  ARM_STEPS_TAC KD2_EXEC (37--42) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (43--57) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The values computed: m', G of m' and h, K' and r', the reencryption c' of *)
(* m', z, the result of J, and whether c' is the ciphertext, as for gcc 12   *)
(* -O2. The buffers of the function are at b + 2048 (c' and then z and the   *)
(* ciphertext), b + 4384 (K' and r') and b + 4448 (m' and h), after those of *)
(* the inlined indcpa_dec. The invariant of the comparison loop at           *)
(* iteration i states that the OR accumulator Q2 is zero if and only if the  *)
(* first 16 * i bytes of the ciphertext and of c' are equal (the code also   *)
(* keeps an XOR accumulator in Q1, whose value does not matter), and the     *)
(* invariant of the conditional move at iteration i that the first i bytes   *)
(* at ss are those of K' if the ciphertexts are equal and those of the       *)
(* result of J otherwise, and the others still those of the result of J.     *)
(* The frame has the facts needed after both loops.                          *)
(* ------------------------------------------------------------------------- *)

let KD2_MP = `kpke_decrypt mlkem512 (mlkem_slice 0 768 dk) c`;;

let KD2_GG =
 `sha3_512 (APPEND (kpke_decrypt mlkem512 (mlkem_slice 0 768 dk) c)
                  (mlkem_slice 1568 32 dk))`;;

let KD2_KP = mk_comb(`mlkem_slice 0 32`,KD2_GG);;

let KD2_RR = mk_comb(`mlkem_slice 32 32`,KD2_GG);;

let KD2_CP = list_mk_comb(`kpke_encrypt mlkem512`,
  [`mlkem_slice 768 800 (dk:byte list)`; KD2_MP; KD2_RR]);;

let KD2_ZZ = `mlkem_slice 1600 32 (dk:byte list)`;;

let KD2_KB = `list_of_seq (shake256 (APPEND (mlkem_slice 1600 32 dk) c)) 32`;;

let KD2_EQ = mk_eq(`num_of_bytelist c`,mk_comb(`num_of_bytelist`,KD2_CP));;

let KD2_SUBST tm =
  subst [mk_comb(`num_of_bytelist`,KD2_CP),`CP:num`;
         mk_comb(`num_of_bytelist`,KD2_KP),`KP:num`;
         mk_comb(`num_of_bytelist`,KD2_KB),`KB:num`;
         mk_comb(`num_of_bytelist`,KD2_ZZ),`ZZ:num`;
         KD2_EQ,`EQ:bool`] tm;;

let KD2_FRAME b = KD2_SUBST(parse_term(Printf.sprintf
 "read SP s = word_add stackpointer (word 12016) /\\
  read X19 s = word_add stackpointer (word %d) /\\
  read X22 s = ct /\\
  read X23 s = word_add stackpointer (word %d) /\\
  read X24 s = word 0 /\\
  read X25 s = word_add stackpointer (word %d) /\\
  read X27 s = word_add stackpointer (word %d) /\\
  read X28 s = x28_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12016))) s =
  x19_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12024))) s =
  x20_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12032))) s =
  x21_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12040))) s =
  x22_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12048))) s =
  x23_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12056))) s =
  x24_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12064))) s =
  x25_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12072))) s =
  x26_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12080))) s =
  x27_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12088))) s =
  returnaddress /\\
  read (memory :> bytes64 (word_add stackpointer (word 16632))) s = canary /\\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard)))
   s = guard /\\
  read (memory :> bytes64 guard) s = canary /\\
  read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\\
  read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev /\\
  read (memory :> bytes(word_add stackpointer (word %d),32)) s = KP"
  b (b + 4384) (b + 2048) (b + 4448) (b + 4384)));;

let KD2_INV b = KD2_SUBST(parse_term(Printf.sprintf
 "\\i s. read X0 s = word_add stackpointer (word(%d + 16 * i)) /\\
        read X1 s = word_add ct (word(16 * i)) /\\
        read X2 s = word_add stackpointer (word %d) /\\
        read X20 s = sk /\\ read X21 s = ss /\\
        (read Q2 s = word 0 <=>
         num_of_bytelist c MOD 2 EXP (128 * i) = CP MOD 2 EXP (128 * i)) /\\
        read (memory :> bytes(ct,768)) s = num_of_bytelist c /\\
        read (memory :> bytes(word_add stackpointer (word %d),768)) s = CP /\\
        read (memory :> bytes128 (word_add sk (word 1600))) s =
        word(ZZ MOD 2 EXP 128) /\\
        read (memory :> bytes128 (word_add sk (word 1616))) s =
        word(ZZ DIV 2 EXP 128) /\\ FRAME"
  (b + 2048) (b + 2816) (b + 2048)));;

let KD2_INV_FRAME b =
  let inv = KD2_INV b in
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [KD2_FRAME b,`FRAME:bool`] bod);;

let KD2_CMOV_INV b = KD2_SUBST(parse_term(Printf.sprintf
 "\\i s. read X0 s = word(i + 1) /\\
        read X21 s = word_sub ss (word 1) /\\
        read X4 s = (if EQ then word 0 else word 4294967041) /\\
        read (memory :> bytes(ss,i)) s =
        (if EQ then KP else KB) MOD 2 EXP (8 * i) /\\
        read (memory :> bytes(word_add ss (word i),32 - i)) s =
        KB DIV 2 EXP (8 * i) /\\ FRAME"));;

let KD2_CMOV_INV_FRAME b =
  let inv = KD2_CMOV_INV b in
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [KD2_FRAME b,`FRAME:bool`] bod);;

(* ------------------------------------------------------------------------- *)
(* From the start to the comparison loop: the check of the key, the          *)
(* decryption (the lemma above), G of m' and h, and the reencryption.        *)
(* ------------------------------------------------------------------------- *)

let KD2_G_INPUT_TAC b s =
  let st = mk_var(s,`:armstate`) in
  SUBGOAL_THEN
   (subst [st,`s:armstate`; KEM_SP(b + 4448),`a:int64`;
           KD2_MP,`mm:byte list`]
     `read (memory :> bytes(a,64)) s =
      num_of_bytelist(APPEND (mm:byte list) (mlkem_slice 1568 32 dk))`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; KPKE_DECRYPT_LENGTH_512];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (subst [KD2_MP,`mm:byte list`]
     `LENGTH(APPEND (mm:byte list) (mlkem_slice 1568 32 dk)) = 64`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; KPKE_DECRYPT_LENGTH_512] THEN ARITH_TAC;
    ALL_TAC];;

let KD2_KR_TAC b s =
  let st = mk_var(s,`:armstate`) and a = KEM_SP(b + 4384) in
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [a,`a:int64`; st,`s:armstate`]
         `read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 x)`))
         (concl th)
    then
      MP_TAC(SPECL [a; KD2_GG; `0`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      MP_TAC(SPECL [a; KD2_GG; `32`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      ASM_REWRITE_TAC[LENGTH_SHA3_512] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      REPEAT DISCH_TAC
    else NO_TAC) THEN
  SUBGOAL_THEN
   (mk_conj(mk_eq(mk_comb(`LENGTH:byte list->num`,KD2_KP),`32`),
            mk_eq(mk_comb(`LENGTH:byte list->num`,KD2_RR),`32`)))
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC];;

let KD2_PART1_TAC b =
  let st n = "s"^string_of_int n in
  ENSURES_INIT_TAC "s0" THEN KD2_SK_TAC THEN
  KEM_HALVES_TAC `word_add sk (word 1568):int64` THEN
  KEM_HALVES_TAC `word_add sk (word 1600):int64` THEN
  ARM_STEPS_TAC KD2_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (4--13) THEN KD2_BUFFER_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (14--19) THEN INLINE_GOT_TAC THEN
  KD2_CHECK_TAC THEN

  (*** The decryption, G and the reencryption ***)

  ARM_STEPS_TAC KD2_EXEC (21--21) THEN INLINE_GOT_TAC THEN
  LOCAL_INDCPA_DEC_TAC b
   [`mlkem_slice 0 768 (dk:byte list)`; `c:byte list`; `read X20 s`;
    `read X22 s`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `stackpointer:int64`] 22 THEN
  ARM_STEPS_TAC KD2_EXEC (23--32) THEN
  KEM_JOIN_TAC (KEM_SP(b + 4480)) `mlkem_slice 1568 32 (dk:byte list)`
    (st 32) THEN
  KD2_G_INPUT_TAC b (st 32) THEN INLINE_GOT_TAC THEN
  LOCAL_SHA3_512_TAC
   [`read X0 s`; `read X1 s`;
    mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,KD2_MP),
            `mlkem_slice 1568 32 (dk:byte list)`);
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 33 THEN
  KD2_KR_TAC b (st 33) THEN
  ARM_STEPS_TAC KD2_EXEC (34--38) THEN INLINE_GOT_TAC THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,KD2_MP),`32`))
  ASSUME_TAC THENL [REWRITE_TAC[KPKE_DECRYPT_LENGTH_512]; ALL_TAC] THEN
  LOCAL_INDCPA_ENC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `mlkem_slice 768 800 (dk:byte list)`; KD2_MP; KD2_RR;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 39 THEN
  ARM_STEPS_TAC KD2_EXEC (40--46) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; MOD_1] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* One iteration of the comparison, with the loop test.                      *)
(* ------------------------------------------------------------------------- *)

let KD2_TEST_STMT =
  `!sp:int64 b i.
        b <= 12112 /\ i < 48
        ==> (val(word_sub (word_add sp (word(b + 2816)))
                          (word_add (word_add sp (word((b + 2048) + 16 * i)))
                                    (word 16))) = 0 <=>
             ~(i + 1 < 48))`;;

let KD2_TEST = assume_spec KD2_TEST_STMT;;

let KD2_CHUNK_TAC a v =
  let bth = MP (ARITH_RULE `i < 48 ==> 16 * i + 16 <= 768`)
               (ASSUME `i < 48`) in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),Comb(_,Comb(Const("bytes",_),aa))),
                     s)),vv)
        when aa = mk_pair(a,`768`) && vv = v ->
          let lth = SPECL [a; `768`; `i:num`; v; s] KEM_BYTES128 in
          ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                      (MP lth (CONJ th bth)))
    | _ -> NO_TAC);;

let KD2_BODY_TAC b =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  GHOST_INTRO_TAC `q1:int128` `read Q1` THEN
  ENSURES_INIT_TAC "s0" THEN
  KD2_CHUNK_TAC `ct:int64` `num_of_bytelist c` THEN
  KD2_CHUNK_TAC (KEM_SP(b + 2048)) (mk_comb(`num_of_bytelist`,KD2_CP)) THEN
  ARM_STEPS_TAC KD2_EXEC (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
     (MP (SPECL [`stackpointer:int64`; mk_small_numeral b; `i:num`]
                KD2_TEST)
         (CONJ (ARITH_RULE(mk_binop `(<=):num->num->bool`
                            (mk_small_numeral b) `12112`))
               (ASSUME `i < 48`)))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `i + 1 < 48` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ASM_REWRITE_TAC[KEM_OR_STEP; KEM_MOD_STEP] THEN
    REWRITE_TAC[CONJ_ACI; EQ_SYM_EQ]];;

(* ------------------------------------------------------------------------- *)
(* From the comparison loop to the conditional move: the result of the       *)
(* comparison as a mask of 0 or 255 (from the OR and the XOR accumulators,   *)
(* whose final value does not matter), J of z and the ciphertext copied      *)
(* after z with memcpy, and the mask for the bytes.                          *)
(* ------------------------------------------------------------------------- *)

let KD2_DONE_TAC =
  SUBGOAL_THEN (mk_iff(`q2:int128 = word 0`,KD2_EQ)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) && lhand(concl th) = `q2:int128 = word 0`
      then REWRITE_TAC[th] else NO_TAC) THEN
    MP_TAC(ISPEC `c:byte list` NUM_OF_BYTELIST_BOUND) THEN
    MP_TAC(ISPEC KD2_CP NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[KPKE_ENCRYPT_LENGTH_512] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC];;

let KD2_MASK_TAC s =
  let x20 = mk_comb(`read X20`,mk_var(s,`:armstate`)) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = x20 then
      let e = rand c in
      let eth = BITBLAST_RULE
        (mk_eq(e,`if q2:int128 = word 0 then word 0:int64 else word 255`)) in
      ASSUME_TAC(TRANS th eth)
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = x20 then
      FIRST_ASSUM(fun th' ->
        if is_iff(concl th') && lhand(concl th') = `q2:int128 = word 0`
        then ASSUME_TAC(REWRITE_RULE[th'] th) else NO_TAC)
    else NO_TAC);;

let KD2_J_INPUT_TAC b s =
  let st = mk_var(s,`:armstate`) in
  SUBGOAL_THEN
   (subst [st,`s:armstate`; KEM_SP(b + 2048),`a:int64`]
     `read (memory :> bytes(a,800)) s =
      num_of_bytelist(APPEND (mlkem_slice 1600 32 (dk:byte list)) c)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `800 = 32 + 768`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(APPEND (mlkem_slice 1600 32 (dk:byte list)) c) = 800`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC];;

let KD2_EXIT_A_TAC b =
  let st n = "s"^string_of_int n in
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  GHOST_INTRO_TAC `q1:int128` `read Q1` THEN
  ENSURES_INIT_TAC "s0" THEN KD2_DONE_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KD2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[]) (1--26) THEN
  KD2_MASK_TAC (st 26) THEN
  ARM_STEPS_TAC KD2_EXEC (27--30) THEN
  KEM_JOIN_TAC (KEM_SP(b + 2048)) KD2_ZZ (st 30) THEN
  LIBC_PLT_TAC KD2_EXEC 30 THEN
  LIBC_CALL_TAC "H_MEMCPY" KD2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `num_of_bytelist(c:byte list)`;
    `read X30 s`] 35 THEN
  KD2_J_INPUT_TAC b (st 35) THEN
  ARM_STEPS_TAC KD2_EXEC (36--40) THEN INLINE_GOT_TAC THEN
  LOCAL_SHAKE256_TAC
   [`read X0 s`; `32`; `read X2 s`;
    `APPEND (mlkem_slice 1600 32 (dk:byte list)) c`; `guard:int64`;
    `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 41 THEN
  ARM_STEPS_TAC KD2_EXEC (42--44) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; DIV_1; SUB_0; WORD_ADD_0;
              READ_MEMORY_BYTES_TRIVIAL] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC KD2_EQ THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* One iteration of the conditional move, and the end: the zeroing of the    *)
(* buffers, the stack guard and the result in terms of FIPS 203.             *)
(* ------------------------------------------------------------------------- *)

let KD2_KP_ADDR2_STMT =
  `!sp:int64 a i.
        word_add (word_add (word (i + 1)) (word_add sp (word a)))
                 (word 18446744073709551615) =
        word_add sp (word (a + (i + 1) + 18446744073709551615))`;;

let KD2_KP_ADDR2 = assume_spec KD2_KP_ADDR2_STMT;;

let KD2_CMOV_BODY_TAC b =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [KEM_SP(b + 4384); `32`; mk_comb(`num_of_bytelist`,KD2_KP);
                `i:num`; `s0:armstate`] READ_MEMORY_BYTES8_OF_NUM) THEN
  ASM_REWRITE_TAC[KEM_KP_ADDR; GSYM KD2_KP_ADDR2] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   (KD2_SUBST `read (memory :> bytes(word_add ss (word i),(31 - i) + 1)) s0 =
               KB DIV 2 EXP (8 * i)`)
  MP_TAC THENL
   [SIMP_TAC[ARITH_RULE `i < 32 ==> (31 - i) + 1 = 32 - i`;
             ASSUME `i < 32`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th ->
      let th1,th2 = CONJ_PAIR(MATCH_MP KEM_SPLIT1 th) in
      ASSUME_TAC(ONCE_REWRITE_RULE
       [GSYM(SPECL [`ss:int64`; `i:num`] KEM_SS_ADDR)] th1) THEN
      ASSUME_TAC th2)] THEN
  ARM_STEPS_TAC KD2_EXEC (1--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [KEM_SS_ADDR; MP (SPEC `i:num` KEM_CMOV_TEST) (ASSUME `i < 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `i + 1 < 32` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM WORD_ADD];
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_1] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[KEM_MOD_BYTE] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_CASES_TAC KD2_EQ THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [KEM_VAL_BYTE] THEN
    SPEC_TAC(KD2_SUBST `word((KP DIV 2 EXP (8 * i)) MOD 256):byte`,
             `x:byte`) THEN
    SPEC_TAC(KD2_SUBST `word((KB DIV 2 EXP (8 * i)) MOD 256):byte`,
             `y:byte`) THEN
    REPEAT GEN_TAC THEN AP_TERM_TAC THEN BITBLAST_TAC;
    REWRITE_TAC[ARITH_RULE `32 - (i + 1) = 31 - i`; WORD_ADD; WORD_ADD_ASSOC;
                KEM_DIV_BYTE] THEN
    ASM_REWRITE_TAC[]];;

let KD2_FINAL_TAC =
  REWRITE_TAC[mlkem512; MLKEM_DECAPS_ALT] THEN REWRITE_TAC[GSYM mlkem512] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN (mk_iff(mk_eq(KD2_CP,`c:byte list`),KD2_EQ)) SUBST1_TAC THENL
   [CONV_TAC(LAND_CONV SYM_CONV) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC NUM_OF_BYTELIST_INJ THEN
    ASM_REWRITE_TAC[KPKE_ENCRYPT_LENGTH_512];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOD_LT THEN
  W(fun (_,w) -> MP_TAC(ISPEC (rand(lhand w)) NUM_OF_BYTELIST_BOUND)) THEN
  REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let KD2_EXIT_B_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC KD2_EXEC (1--5) THEN
  LIBC_PLT_TAC KD2_EXEC 5 THEN
  LIBC_CALL_TAC "H_MEMSET" KD2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 10 THEN
  ARM_STEPS_TAC KD2_EXEC (11--16) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (17--31) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KD2_FINAL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy, as for   *)
(* gcc 12 -O2, with the frame of this code: the 4624 bytes of the function   *)
(* and the 12016 of mlkem512_indcpa_enc below them. The proof is by cases on *)
(* whether the stack pointer is a multiple of 32, which gives the address b  *)
(* of the buffers, and on the check of the key.                              *)
(* ------------------------------------------------------------------------- *)

let KD2_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ss:int64`; `ct:int64`; `sk:int64`; `dk:byte list`; `c:byte list`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 16640 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 16640):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[KD2_CHECK; ASSUME `LENGTH(dk:byte list) = 1632`;
           ASSUME `LENGTH(c:byte list) = 768`] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28) THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 768 (dk:byte list)) = 768 /\
    LENGTH(mlkem_slice 768 800 (dk:byte list)) = 800 /\
    LENGTH(mlkem_slice 1568 32 (dk:byte list)) = 32 /\
    LENGTH(mlkem_slice 1600 32 (dk:byte list)) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE
   [SYM(CONV_RULE NUM_REDUCE_CONV
     (MP (SPECL [`768`; `32`; `768`; `800`; `dk:byte list`]
                MLKEM_SLICE_SLICE)
         (ARITH_RULE `768 + 32 <= 800`)))] o
   check (fun th -> is_forall(concl th) &&
                    KEM_HAS_CONST "mlkem_samplentt_terminates"
                     (concl th)));;

let KD2_OK_TAC b =
  ENSURES_WHILE_UP2_TAC `48` `pc + mlkem512_dec_loop2`
   `pc + mlkem512_dec_loop2_exit`
   (KD2_INV_FRAME b) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; KD2_PART1_TAC b; KD2_BODY_TAC b;
    ENSURES_WHILE_UP2_TAC `32` `pc + mlkem512_dec_loop3`
     `pc + mlkem512_dec_loop3_exit`
     (KD2_CMOV_INV_FRAME b) THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC; KD2_EXIT_A_TAC b; KD2_CMOV_BODY_TAC b; KD2_EXIT_B_TAC]];;

let KD2_BAD_TAC =
  ENSURES_INIT_TAC "s0" THEN KD2_SK_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (4--13) THEN KD2_BUFFER_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (14--19) THEN INLINE_GOT_TAC THEN
  KD2_CHECK_TAC THEN KD2_FAIL_TAC;;

let KD2_CASE_TAC b =
  KEM_LABELS_TAC THEN
  ASM_CASES_TAC
   `num_of_bytelist(mlkem_slice 1568 32 (dk:byte list)) =
    num_of_bytelist(sha3_256(mlkem_slice 768 800 dk))` THEN
  ASM_REWRITE_TAC[] THENL [KD2_OK_TAC b; KD2_BAD_TAC];;

let MLKEM_NATIVE_DEC_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!ss ct sk (dk:byte list) (c:byte list) guard mf mc ea el ev pc
    stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH dk = 1632 /\ LENGTH c = 768 /\
        (!i j. i < 2 /\ j < 2
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 1536 32 dk) [word j; word i])) /\
        nonoverlapping (ct,768) (word pc,libmlkem_size) /\
        nonoverlapping (sk,1632) (word pc,libmlkem_size) /\
        nonoverlapping (ss,32) (word_sub stackpointer (word 16640),16640) /\
        ALLPAIRS nonoverlapping
         [(ss,32); (word_sub stackpointer (word 16640),16640)]
         [(ct,768); (sk,1632); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
          (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlkem512_dec) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ss; ct; sk] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(ct,768)) s = num_of_bytelist c /\
                  read (memory :> bytes(sk,1632)) s = num_of_bytelist dk)
             (\s. read PC s = returnaddress /\
                  (mlkem_decaps_check mlkem512 dk c
                   ==> read (memory :> bytes(ss,32)) s =
                       num_of_bytelist(mlkem_decaps_internal mlkem512 dk c)) /\
                  C_RETURN s =
                  (if mlkem_decaps_check mlkem512 dk c then word 0
                   else word 0xfffffffb))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ss,32);
                memory :> bytes(word_sub stackpointer (word 16640),16640)])`;;

let MLKEM_NATIVE_DEC_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_DEC_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset (for mlkem512_indcpa_enc) and the safety contract for memcpy, as   *)
(* for gcc 12 -O2. The events depend only on the addresses and on the        *)
(* encapsulation key ek in the decapsulation key and the hash h stored with  *)
(* it, through the check of the hash and the reencryption. The buffers are  *)
(* kept at their offset from the stack pointer as a conditional, and the     *)
(* inlined indcpa_dec is a lemma with its events, as for its correctness.    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let KD2_SAFE_B =
 `if aligned 32 (stackpointer:int64) then 12096 else 12112`;;

(*** The addresses in the facts about the state as word_add stackpointer
     (word n), but not in those about events (the trace, its equations
     and memaccess_inbounds), which must stay as the unification of the
     events of the loops has fixed them ***)

let KD2_SAFE_NORMALIZE_TAC =
  let conv =
    REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
    DEPTH_CONV NUM_ADD_CONV
  and is_trace t = type_of t = `:(uarch_event)list` in
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th) &&
       not (can (find_term is_trace) (concl th))
    then CONV_RULE conv th else th);;

(*** In the lemma for the inlined indcpa_dec, without loops, all of them ***)

let KD2_DEC_NORMALIZE_TAC =
  let conv =
    REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
    DEPTH_CONV NUM_ADD_CONV in
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE conv th else th);;

let KD2_SAFE_BUFFER_TAC =
  SUBGOAL_THEN (subst [KD2_SAFE_B,`b:num`]
   `word_and (word_add stackpointer (word 12127))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word b)`)
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC KD2_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

(*** The inlined indcpa_dec with its events ***)

let KD2_DEC_ALLOWED =
  [`pc:num`; `c:int64`; `sk:int64`; `mf:int64`; `stackpointer:int64`];;

let KD2_DEC_SAFE_CALL_TAC name ilist n =
  KD2_DEC_NORMALIZE_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,KD2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KD2_DEC_ALLOWED); LABEL_TAC name safety_th]);;

let KD2_DEC_SAFE_CALL0_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,KD2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KD2_DEC_ALLOWED); LABEL_TAC name safety_th]);;

let KD2_DEC_SAFE_CONTENTS r =
  let a = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                          r),`s:armstate`) in
  vsubst [a,`a:int64`]
   `\i. read(memory :> bytes16(word_add a (word(2 * i)))) (s:armstate)`;;


(*** The lemma for each value of b, and their combination for the offset
     as a conditional, as the main proof keeps it ***)

let KD2_DEC_SAFE_GOAL_GEN qb hb fb bs = parse_term(Printf.sprintf
 "!mf ea el ev.
     memset_safety_contract mf ea el ev
     ==> exists f_events.
          forall e sk c pc stackpointer%s.
            %saligned 4096 (word pc:int64) /\\ pc + libmlkem_size <= 2 EXP 64 /\\
            aligned 16 stackpointer /\\
            nonoverlapping (c,768) (word pc,libmlkem_size) /\\
            nonoverlapping (sk,768) (word pc,libmlkem_size) /\\
            ALLPAIRS nonoverlapping
             [(word_add stackpointer (word %s),4480);
              (word_add stackpointer (word 12000),16)]
             [(c,768); (sk,768); (word pc,libmlkem_size);
              (word(pc + got_memset),8); (ea,el)]
            ==> ensures arm
                 (\\s. aligned_bytes_loaded s (word pc)
                        mlkem_native_libmlkem_gcc12_O2_mono_mc /\\
                      read PC s = word (pc + mlkem512_dec_in_indcpa_dec) /\\
                      read SP s = word_add stackpointer (word 12016) /\\
                      read X19 s = word_add stackpointer (word %s) /\\
                      read X20 s = sk /\\ read X22 s = c /\\
                      read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                      read (memory :> bytes(ea,el)) s = ev /\\
                      read events s = e)
                 (\\s. read PC s = word (pc + mlkem512_dec_in_indcpa_dec_end) /\\
                      read X27 s = word_add stackpointer (word(%s + 4448)) /\\
                      (exists e2.
                         read events s = APPEND e2 e /\\
                         e2 = f_events sk c mf pc stackpointer%s /\\
                         memaccess_inbounds e2
                          [c,768; sk,768; word_add stackpointer (word %s),4480;
                           word_add stackpointer (word 12000),16;
                           word(pc + got_memset),8; ea,el;
                           word(pc + mlk_poly_decompress_d10_c_consts),16;
                           word(pc + mlk_poly_invntt_tomont_c_consts),32;
                           word(pc + rodata_mlk_zetas),256]
                          [word_add stackpointer (word %s),4480;
                           word_add stackpointer (word 12000),16]))
                 (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                  MAYCHANGE [X18] ,,
                  MAYCHANGE [X23; X24; X25; X26; X27; X30] ,,
                  MAYCHANGE
                   [memory :> bytes(word_add stackpointer (word %s),4480);
                    memory :> bytes(word_add stackpointer (word 12000),16)])"
  qb hb bs bs bs fb bs bs bs);;

let KD2_DEC_SAFE_GOAL = KD2_DEC_SAFE_GOAL_GEN "" "" "";;

let KD2_DEC_SAFE_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_safety_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_D10" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_D4" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_BASEMUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE)
    "H_INVNTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC KD2_SUB "H_SUB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_TOMSG" THEN
  META_EXISTS_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; ALLPAIRS;
              NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
  let e = `e:(uarch_event)list` in
  let x n = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            mk_const("X"^string_of_int n,[])),`s:armstate`) in
  let rest0 = [`pc:num`; `read X30 s`] in
  let call = KD2_DEC_SAFE_CALL_TAC in
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC KD2_EXEC (1--5) THEN
  call "H_D10" ([e; x 0; x 1] @ rest0) 6 THEN
  ARM_STEPS_TAC KD2_EXEC (7--10) THEN
  call "H_D10" ([e; x 0; x 1] @ rest0) 11 THEN
  ARM_STEPS_TAC KD2_EXEC (12--15) THEN
  call "H_D4" ([e; x 0; x 1] @ rest0) 16 THEN
  ARM_STEPS_TAC KD2_EXEC (17--20) THEN
  call "H_FROMBYTES" ([e; x 0; x 1] @ rest0) 21 THEN
  ARM_STEPS_TAC KD2_EXEC (22--24) THEN
  call "H_FROMBYTES" ([e; x 0; x 1] @ rest0) 25 THEN
  ARM_STEPS_TAC KD2_EXEC (26--27) THEN
  call "H_NTT" ([e; x 0] @ rest0) 28 THEN
  ARM_STEPS_TAC KD2_EXEC (29--30) THEN
  call "H_NTT" ([e; x 0] @ rest0) 31 THEN
  ARM_STEPS_TAC KD2_EXEC (32--34) THEN
  call "H_MULCACHE" ([e; x 0; x 1] @ rest0) 35 THEN
  ARM_STEPS_TAC KD2_EXEC (36--38) THEN
  call "H_MULCACHE" ([e; x 0; x 1] @ rest0) 39 THEN
  ARM_STEPS_TAC KD2_EXEC (40--44) THEN
  call "H_BASEMUL" ([e; x 1; x 2; x 3; x 0] @ rest0) 45 THEN
  ARM_STEPS_TAC KD2_EXEC (46--47) THEN
  call "H_INVNTT" [e; x 0; `pc:num`; `read SP s`; `read X30 s`] 48 THEN
  ARM_STEPS_TAC KD2_EXEC (49--52) THEN
  KD2_DEC_SAFE_CALL0_TAC "H_SUB" [e; x 3; x 4; KD2_DEC_SAFE_CONTENTS `X3`;
                KD2_DEC_SAFE_CONTENTS `X4`; `pc:num`] 53 THEN
  ARM_STEPS_TAC KD2_EXEC (54--57) THEN
  call "H_REDUCE" ([e; x 0] @ rest0) 58 THEN
  ARM_STEPS_TAC KD2_EXEC (59--61) THEN
  call "H_TOMSG" ([e; x 0; x 1] @ rest0) 62 THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC KD2_EXEC (k0--k) THEN LIBC_PLT_TAC KD2_EXEC k THEN
    KD2_DEC_NORMALIZE_TAC THEN
    LIBC_SAFE_CALL_TAC "H_MEMSET" KD2_EXEC
     [e; x 0; x 1; x 2; `read X30 s`] (ref KD2_DEC_ALLOWED) (k + 5))
   [63,66; 72,75; 81,84; 90,93; 99,102] THEN
  KD2_DEC_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD2_DEC_SAFE_A_STMT =
  KD2_DEC_SAFE_GOAL "12096";;

let KD2_DEC_SAFE_A = assume_spec KD2_DEC_SAFE_A_STMT;;

let KD2_DEC_SAFE_U_STMT =
  KD2_DEC_SAFE_GOAL "12112";;

let KD2_DEC_SAFE_U = assume_spec KD2_DEC_SAFE_U_STMT;;

let KD2_DEC_SAFE_STMT =
  KD2_DEC_SAFE_GOAL_GEN " b" "(b = 12096 \\/ b = 12112) /\\\n            " " b" "b";;

let KD2_DEC_SAFE = assume_spec KD2_DEC_SAFE_STMT;;


(*** The function ***)

let KD2_SAFE_TEMPLATE =
 `\(ss:int64) (ct:int64) (sk:int64) (guard:int64) (mf:int64) (mc:int64)
   (pc:num) (sp:int64) (ra:int64) (ek:byte list) (h:byte list).
   if num_of_bytelist h = num_of_bytelist(sha3_256 ek)
   then APPEND
         (APPEND (f_ev_exitb ss ct sk guard mf mc pc sp ra)
           (APPEND (ENUMERATEL 32
                     (\i. f_ev_cmov ss ct sk guard mf mc pc sp ra i))
                   (f_ev_exita ss ct sk guard mf mc pc sp ra)))
         (APPEND (ENUMERATEL 48 (\i. f_ev_cmp ss ct sk guard mf mc pc sp ra i))
                 (f_ev_prol ss ct sk guard mf mc pc sp ra ek h))
   else f_ev_bad ss ct sk guard mf mc pc sp ra ek h
   :(uarch_event)list`;;

let KD2_SAFE_ALLOWED =
  [`pc:num`; `ss:int64`; `ct:int64`; `sk:int64`; `guard:int64`;
   `mf:int64`; `mc:int64`; `stackpointer:int64`; `returnaddress:int64`;
   `ekk:byte list`; `hh:byte list`; `i:num`;
   `f_ev_cmp:int64->int64->int64->int64->int64->int64->num->int64->
              int64->num->(uarch_event)list`;
   `f_ev_cmov:int64->int64->int64->int64->int64->int64->num->int64->
              int64->num->(uarch_event)list`];;

let KD2_SAFE_CALL_TAC name ilist n =
  KD2_SAFE_NORMALIZE_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,KD2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KD2_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KD2_SAFE_FRAME = subst [KD2_SAFE_B,`b:num`]
 `read SP s = word_add stackpointer (word 12016) /\
  read X19 s = word_add stackpointer (word b) /\
  read X22 s = ct /\
  read X23 s = word_add stackpointer (word(b + 4384)) /\
  read X25 s = word_add stackpointer (word(b + 2048)) /\
  read X27 s = word_add stackpointer (word(b + 4448)) /\
  read X28 s = x28_init /\
  read (memory :> bytes64 (word_add stackpointer (word 12016))) s =
  x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word 12024))) s =
  x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 12032))) s =
  x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 12040))) s =
  x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 12048))) s =
  x23_init /\
  read (memory :> bytes64 (word_add stackpointer (word 12056))) s =
  x24_init /\
  read (memory :> bytes64 (word_add stackpointer (word 12064))) s =
  x25_init /\
  read (memory :> bytes64 (word_add stackpointer (word 12072))) s =
  x26_init /\
  read (memory :> bytes64 (word_add stackpointer (word 12080))) s =
  x27_init /\
  read (memory :> bytes64 (word_add stackpointer (word 12088))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 16632))) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard)))
   s = guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
  read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s = mc /\
  read (memory :> bytes(ea,el)) s = ev`;;

let KD2_SAFE_INV =
  let inv = subst [KD2_SAFE_B,`b:num`]
   `\i s. read X0 s = word_add stackpointer (word((b + 2048) + 16 * i)) /\
          read X1 s = word_add ct (word(16 * i)) /\
          read X2 s = word_add stackpointer (word(b + 2816)) /\
          read X20 s = sk /\ read X21 s = ss /\ FRAME` in
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [KD2_SAFE_FRAME,`FRAME:bool`] bod);;

let KD2_SAFE_CMOV_INV =
  let inv =
   `\i s. read X0 s = word(i + 1) /\
          read X21 s = word_sub ss (word 1) /\ FRAME` in
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [KD2_SAFE_FRAME,`FRAME:bool`] bod);;

let KD2_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th1 ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th1)
    then FIRST_X_ASSUM(fun th2 ->
      let sth = CONJUNCT2(MATCH_MP MEMSET_FULL_CONTRACT th1) in
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP MLKEM_NATIVE_INDCPA_ENC_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
                 (CONJ th1 th2)) "H_ENC" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP KD2_DEC_SAFE sth) "H_DEC" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (REWRITE_RULE[memset_safety_contract] sth) "H_MEMSET" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE th2)
       "H_SHAKE256" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (REWRITE_RULE[memcpy_safety_contract] th2) "H_MEMCPY")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_CHECK_SK_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL "H_CHECK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHA3_512_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_SHA3_512" THEN
  CONCRETIZE_F_EVENTS_TAC KD2_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 16640):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `12096 <= (if aligned 32 (stackpointer:int64) then 12096 else 12112) /\
    (if aligned 32 (stackpointer:int64) then 12096 else 12112) <= 12112`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(if aligned 32 (stackpointer:int64) then 12096 else 12112) = 12096 \/
    (if aligned 32 (stackpointer:int64) then 12096 else 12112) = 12112`
  ASSUME_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28) THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 768 (dk:byte list)) = 768 /\
    LENGTH(mlkem_slice 768 800 (dk:byte list)) = 800 /\
    LENGTH(mlkem_slice 1568 32 (dk:byte list)) = 32 /\
    LENGTH(mlkem_slice 1600 32 (dk:byte list)) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE
   [SYM(CONV_RULE NUM_REDUCE_CONV
     (MP (SPECL [`768`; `32`; `768`; `800`; `dk:byte list`]
                MLKEM_SLICE_SLICE)
         (ARITH_RULE `768 + 32 <= 800`)))] o
   check (fun th -> is_forall(concl th) &&
                    KEM_HAS_CONST "mlkem_samplentt_terminates"
                     (concl th))) THEN
  ABBREV_TAC `ekk = mlkem_slice 768 800 (dk:byte list)` THEN
  ABBREV_TAC `hh = mlkem_slice 1568 32 (dk:byte list)`;;

let KD2_SAFE_START_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  KD2_SK_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (4--13) THEN KD2_SAFE_BUFFER_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (14--19) THEN INLINE_GOT_TAC THEN
  KD2_SAFE_CALL_TAC "H_CHECK"
   [`e:(uarch_event)list`; `read X0 s`; `ekk:byte list`;
    `num_of_bytelist(hh:byte list)`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 20;;

let KD2_SAFE_PART1_TAC =
  KD2_SAFE_START_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EQT_INTRO(ASSUME
   `num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk)`)]) THEN
  ARM_STEPS_TAC KD2_EXEC (21--21) THEN INLINE_GOT_TAC THEN
  KD2_SAFE_CALL_TAC "H_DEC"
   [`e:(uarch_event)list`; `read X20 s`; `read X22 s`; `pc:num`;
    `stackpointer:int64`; KD2_SAFE_B] 22 THEN
  ARM_STEPS_TAC KD2_EXEC (23--32) THEN INLINE_GOT_TAC THEN
  KD2_SAFE_CALL_TAC "H_SHA3_512"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `64`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 33 THEN
  ARM_STEPS_TAC KD2_EXEC (34--38) THEN INLINE_GOT_TAC THEN
  KD2_SAFE_CALL_TAC "H_ENC"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `ekk:byte list`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 39 THEN
  ARM_STEPS_TAC KD2_EXEC (40--46) THEN
  KD2_SAFE_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD2_SAFE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPECL [`stackpointer:int64`; KD2_SAFE_B; `i:num`] KD2_TEST)
       (CONJ (ASSUME
         `(if aligned 32 (stackpointer:int64) then 12096 else 12112) <= 12112`)
             (ASSUME `i < 48`))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD2_SAFE_EXIT_A_TAC =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (1--30) THEN LIBC_PLT_TAC KD2_EXEC 30 THEN
  KD2_SAFE_NORMALIZE_TAC THEN LIBC_SAFE_CALL_TAC "H_MEMCPY" KD2_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KD2_SAFE_ALLOWED) 35 THEN
  ARM_STEPS_TAC KD2_EXEC (36--40) THEN INLINE_GOT_TAC THEN
  KD2_SAFE_CALL_TAC "H_SHAKE256"
   [`e:(uarch_event)list`; `read X0 s`; `32`; `read X2 s`; `800`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 41 THEN
  ARM_STEPS_TAC KD2_EXEC (42--44) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `0 + 1 = 1`; APPEND_NIL; ENUMERATEL_APPEND_ZERO] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The address of byte i of K' in the selection loop ***)

let KD2_KBAR_ADDR_STMT =
  `!sp:int64 a b i.
        word_add (word_add (word (i + 1)) (word_add sp (word (a + b))))
                 (word 18446744073709551615) =
        word_add sp (word (a + b + i))`;;

let KD2_KBAR_ADDR = assume_spec KD2_KBAR_ADDR_STMT;;

let KD2_SAFE_CMOV_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (1--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [KEM_SS_ADDR; KD2_KBAR_ADDR;
    MP (SPEC `i:num` KEM_CMOV_TEST) (ASSUME `i < 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM WORD_ADD]; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD2_SAFE_EXIT_B_TAC =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (1--5) THEN LIBC_PLT_TAC KD2_EXEC 5 THEN
  KD2_SAFE_NORMALIZE_TAC THEN LIBC_SAFE_CALL_TAC "H_MEMSET" KD2_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KD2_SAFE_ALLOWED) 10 THEN
  ARM_STEPS_TAC KD2_EXEC (11--16) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (17--31) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD2_SAFE_BAD_TAC =
  KD2_SAFE_START_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EQF_INTRO(ASSUME
   `~(num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk))`)]) THEN
  ARM_STEPS_TAC KD2_EXEC (21--31) THEN LIBC_PLT_TAC KD2_EXEC 31 THEN
  KD2_SAFE_NORMALIZE_TAC THEN LIBC_SAFE_CALL_TAC "H_MEMSET" KD2_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KD2_SAFE_ALLOWED) 36 THEN
  ARM_STEPS_TAC KD2_EXEC (37--42) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (43--57) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_DEC_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
   memset_full_contract mf ea el ev /\ memcpy_safety_contract mc ea el ev
   ==> exists f_events.
        forall e ss ct sk (dk:byte list) guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH dk = 1632 /\
          (!i j. i < 2 /\ j < 2
                 ==> mlkem_samplentt_terminates
                      (APPEND (mlkem_slice 1536 32 dk) [word j; word i])) /\
          nonoverlapping (ct,768) (word pc,libmlkem_size) /\
          nonoverlapping (sk,1632) (word pc,libmlkem_size) /\
          nonoverlapping (ss,32)
           (word_sub stackpointer (word 16640),16640) /\
          ALLPAIRS nonoverlapping
           [(ss,32); (word_sub stackpointer (word 16640),16640)]
           [(ct,768); (sk,1632); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlkem512_dec) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [ss; ct; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sk,1632)) s = num_of_bytelist dk /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events ss ct sk guard mf mc pc
                              (word_sub stackpointer (word 16640))
                              returnaddress
                              (mlkem_slice 768 800 dk)
                              (mlkem_slice 1568 32 dk) /\
                       memaccess_inbounds e2
                        [ct,768; sk,1632; ss,32;
                         word_sub stackpointer (word 16640),16640;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + mlkem_poly_cbd3_consts),32;
                         word(pc + mlkem_poly_cbd2_consts),64;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlk_poly_invntt_tomont_c_consts),32;
                         word(pc + mlk_poly_decompress_d10_c_consts),16]
                        [ss,32; word_sub stackpointer (word 16640),16640]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(ss,32);
                  memory :> bytes(word_sub stackpointer (word 16640),16640)])`;;

let MLKEM_NATIVE_DEC_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_DEC_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT;;
