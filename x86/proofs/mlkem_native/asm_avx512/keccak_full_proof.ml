(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/asm_avx512/keccak_full_spec.ml";;

let SHA3_KECCAK_F1600_AVX512_IMAGE_FULL = prove
 (SHA3_KECCAK_F1600_AVX512_IMAGE_FULL_STMT,
  X_CHOOSE_TAC
   `f:int64->int64->num->int64->int64->(uarch_event)list`
   SHA3_KECCAK_F1600_AVX512_SUBROUTINE_FULL THEN
  EXISTS_TAC
   `\(rc:int64) (a:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      (f:int64->int64->num->int64->int64->(uarch_event)list)
      rc a (pc + sha3_keccak_f1600_avx512) stackpointer returnaddress` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `rc:int64`; `A:int64 list`;
    `pc + sha3_keccak_f1600_avx512`;
    `stackpointer:int64`; `returnaddress:int64`]) THEN
  REWRITE_TAC[MLKEM_NATIVE2_AVX512_KECCAK_X1_MC] THEN
  ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
  X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
              MLKEM_NATIVE2_AVX512_KECCAK_X1_CODE_LOADED) THEN
  REWRITE_TAC[]);;

let SHA3_KECCAK_F1600_AVX512_IMAGE_FULL_F1600 = prove
 (SHA3_KECCAK_F1600_AVX512_IMAGE_FULL_F1600_STMT,
  MP_TAC SHA3_KECCAK_F1600_AVX512_IMAGE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `f:int64->int64->num->int64->int64->(uarch_event)list` THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `rc:int64`; `S:1600 word`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `rc:int64`;
    `wordlist_of_num 25 (val(S:1600 word)):int64 list`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[GSYM READ_MEMORY_WBYTES_KECCAK] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (ONCE_REWRITE_RULE[CONJ_SYM] ENSURES_POSTCONDITION_THM))) THEN
  MESON_TAC[KECCAK_F1600_MEMORY]);;

let SHA3_KECCAK4_F1600_AVX512_SUBROUTINE_FULL_F1600 = prove
 (SHA3_KECCAK4_F1600_AVX512_SUBROUTINE_FULL_F1600_STMT,
  X_CHOOSE_TAC
   `f:int64->int64->num->int64->int64->(uarch_event)list`
   SHA3_KECCAK4_F1600_AVX512_SUBROUTINE_FULL THEN
  EXISTS_TAC
   `\(rc:int64) (r8:int64) (r56:int64) (a:int64) (pc:num) (sp:int64)
     (ra:int64). (f:int64->int64->num->int64->int64->(uarch_event)list)
                 rc a pc sp ra` THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[PAIRWISE; ALL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `bitstate_in:int64`; `rc_pointer:int64`;
    `wordlist_of_num 25 (val(S1:1600 word)):int64 list`;
    `wordlist_of_num 25 (val(S2:1600 word)):int64 list`;
    `wordlist_of_num 25 (val(S3:1600 word)):int64 list`;
    `wordlist_of_num 25 (val(S4:1600 word)):int64 list`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  ANTS_TAC THENL [KECCAK4_ALTFORM_NONOVERLAPPING_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM READ_MEMORY_WBYTES_KECCAK] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_MONO_ALL) THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
            [MESON_TAC[KECCAK_F1600_MEMORY]; ALL_TAC]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
            [MESON_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC MEMACCESS_INBOUNDS_CONTAINED THEN
    REWRITE_TAC[ALL; EX] THEN
    REWRITE_TAC[contained; DIMINDEX_64; CONTAINED_MODULO_REFL; LE_REFL] THEN
    REPEAT DISJ2_TAC THEN
    SUBGOAL_THEN `stackpointer:int64 =
                  word_add (word_sub stackpointer (word 799)) (word 799)`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th])
    THENL [CONV_TAC WORD_RULE; CONTAINED_TAC];
    SUBSUMED_FRAME_TAC]);;
