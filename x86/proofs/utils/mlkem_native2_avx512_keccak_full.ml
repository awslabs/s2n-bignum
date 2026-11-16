(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Correctness and constant-time/memory safety in one theorem ("FULL") for   *)
(* the Keccak-f1600 permutations of the AVX-512 version of the x86           *)
(* mlkem_native2, sha3_keccak_f1600_avx512 (one state, in the image) and     *)
(* sha3_keccak4_f1600_avx512 (four states), for callers that need both facts *)
(* about the same final state, e.g. when their later control flow depends on *)
(* the permuted states: those of x86/proofs/utils/keccak_avx512_full.ml in   *)
(* the forms of utils/mlkem_native2_keccak_full.ml for the AVX2 version, the *)
(* x4 one in the form of the theorem for sha3_keccak4_f1600_alt as in        *)
(* utils/mlkem_native2_avx512_noise.ml.                                      *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native2_avx512_noise.ml";;
needs "x86/proofs/utils/keccak_avx512_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The events of the safety theorems split off the end of a goal that also   *)
(* has the facts of the correctness theorems, the latter proved by ctac, as  *)
(* in the AVX2 version.                                                      *)
(* ------------------------------------------------------------------------- *)

let EVENTS_SPLIT_TAC = KECCAK_AVX512_EVENTS_SPLIT_TAC;;

(* ------------------------------------------------------------------------- *)
(* The x1 permutation sha3_keccak_f1600_avx512 in the image, from            *)
(* SHA3_KECCAK_F1600_AVX512_SUBROUTINE_FULL as for                           *)
(* SHA3_KECCAK_F1600_AVX512_IMAGE_CORRECT and                                *)
(* SHA3_KECCAK_F1600_AVX512_IMAGE_SAFE, and with the state as a 1600-bit     *)
(* word as callers use it.                                                   *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK_F1600_AVX512_IMAGE_FULL = prove
 (`exists f_events.
    forall e a rc A pc stackpointer returnaddress.
       nonoverlapping (a,200) (word pc,mlkem_native2_avx512_image_size) /\
       nonoverlapping (a,200) (rc,192) /\
       nonoverlapping (a,200) (stackpointer,8)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
                 read RIP s = word(pc + sha3_keccak_f1600_avx512) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 wordlist_from_memory(a,25) s = A /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 wordlist_from_memory(a,25) s = keccak 24 A /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,200; rc,192; stackpointer,8]
                      [a,200]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,200)])`,
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
 (`exists f_events.
    forall e a rc (S:1600 word) pc stackpointer returnaddress.
       nonoverlapping (a,200) (word pc,mlkem_native2_avx512_image_size) /\
       nonoverlapping (a,200) (rc,192) /\
       nonoverlapping (a,200) (stackpointer,8)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
                 read RIP s = word(pc + sha3_keccak_f1600_avx512) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 read (memory :> wbytes a) s = S /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 read (memory :> wbytes a) s = keccak_f1600 S /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,200; rc,192; stackpointer,8]
                      [a,200]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,200)])`,
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

(* ------------------------------------------------------------------------- *)
(* The x4 permutation sha3_keccak4_f1600_avx512 on four states as 1600-bit   *)
(* words, from SHA3_KECCAK4_F1600_AVX512_SUBROUTINE_FULL in the form of the  *)
(* theorem for sha3_keccak4_f1600_alt (the two rho tables and its stack), as *)
(* SHA3_KECCAK4_F1600_AVX512_SUBROUTINE_CORRECT_F1600 and                    *)
(* _SUBROUTINE_SAFE_ALTFORM in utils/mlkem_native2_avx512_noise.ml.          *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK4_F1600_AVX512_SUBROUTINE_FULL_F1600 = prove
 (`exists f_events.
     forall e rc_pointer bitstate_in rho8_ptr rho56_ptr
            (S1:1600 word) (S2:1600 word) (S3:1600 word) (S4:1600 word)
            pc stackpointer returnaddress.
       PAIRWISE (nonoverlapping_modulo (2 EXP 64))
         [(pc, LENGTH sha3_keccak4_f1600_avx512_mc);
          (val (word_sub stackpointer (word 0x31f)), 0x31f);
          (val bitstate_in, 800);
          (val rc_pointer, 192);
          (val rho8_ptr, 32);
          (val rho56_ptr, 32)] /\
       nonoverlapping_modulo (2 EXP 64)
         (val bitstate_in, 800)
         (val (word_sub stackpointer (word 0x31f)), 0x31f + 8)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_avx512_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [bitstate_in; rc_pointer; rho8_ptr; rho56_ptr]
                             s /\
                 wordlist_from_memory(rc_pointer, 24) s = round_constants /\
                 wordlist_from_memory(rho8_ptr, 4) s = rho8_constant /\
                 wordlist_from_memory(rho56_ptr, 4) s = rho56_constant /\
                 read (memory :> wbytes bitstate_in) s = S1 /\
                 read (memory :> wbytes(word_add bitstate_in (word 200))) s =
                 S2 /\
                 read (memory :> wbytes(word_add bitstate_in (word 400))) s =
                 S3 /\
                 read (memory :> wbytes(word_add bitstate_in (word 600))) s =
                 S4 /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 read (memory :> wbytes bitstate_in) s = keccak_f1600 S1 /\
                 read (memory :> wbytes(word_add bitstate_in (word 200))) s =
                 keccak_f1600 S2 /\
                 read (memory :> wbytes(word_add bitstate_in (word 400))) s =
                 keccak_f1600 S3 /\
                 read (memory :> wbytes(word_add bitstate_in (word 600))) s =
                 keccak_f1600 S4 /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events rc_pointer rho8_ptr rho56_ptr bitstate_in pc
                                  stackpointer returnaddress /\
                    memaccess_inbounds e2
                      [bitstate_in,800; rc_pointer,192; rho8_ptr,32;
                       rho56_ptr,32; word_sub stackpointer (word 0x31f),0x327]
                      [bitstate_in,800;
                       word_sub stackpointer (word 0x31f),0x31f]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes (bitstate_in, 800);
                        memory :> bytes(word_sub stackpointer (word 0x31f),
                                        0x31f)])`,
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
