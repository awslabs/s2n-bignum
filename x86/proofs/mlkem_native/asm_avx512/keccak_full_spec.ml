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
(* the permuted states: those of                                             *)
(* x86/proofs/mlkem_native/asm_avx512/keccak_avx512_full.ml in the forms of  *)
(* utils/mlkem_native2_keccak_full.ml for the AVX2 version, the x4 one in    *)
(* the form of the theorem for sha3_keccak4_f1600_alt as in                  *)
(* utils/mlkem_native2_avx512_noise.ml.                                      *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/noise_spec.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/keccak_avx512_full_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The x1 permutation sha3_keccak_f1600_avx512 in the image, from            *)
(* SHA3_KECCAK_F1600_AVX512_SUBROUTINE_FULL as for                           *)
(* SHA3_KECCAK_F1600_AVX512_IMAGE_CORRECT and                                *)
(* SHA3_KECCAK_F1600_AVX512_IMAGE_SAFE, and with the state as a 1600-bit     *)
(* word as callers use it.                                                   *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK_F1600_AVX512_IMAGE_FULL_STMT =
  `exists f_events.
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
             MAYCHANGE [memory :> bytes(a,200)])`;;

let SHA3_KECCAK_F1600_AVX512_IMAGE_FULL = assume_spec SHA3_KECCAK_F1600_AVX512_IMAGE_FULL_STMT;;

let SHA3_KECCAK_F1600_AVX512_IMAGE_FULL_F1600_STMT =
  `exists f_events.
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
             MAYCHANGE [memory :> bytes(a,200)])`;;

let SHA3_KECCAK_F1600_AVX512_IMAGE_FULL_F1600 = assume_spec SHA3_KECCAK_F1600_AVX512_IMAGE_FULL_F1600_STMT;;

(* ------------------------------------------------------------------------- *)
(* The x4 permutation sha3_keccak4_f1600_avx512 on four states as 1600-bit   *)
(* words, from SHA3_KECCAK4_F1600_AVX512_SUBROUTINE_FULL in the form of the  *)
(* theorem for sha3_keccak4_f1600_alt (the two rho tables and its stack), as *)
(* SHA3_KECCAK4_F1600_AVX512_SUBROUTINE_CORRECT_F1600 and                    *)
(* _SUBROUTINE_SAFE_ALTFORM in utils/mlkem_native2_avx512_noise.ml.          *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK4_F1600_AVX512_SUBROUTINE_FULL_F1600_STMT =
  `exists f_events.
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
                                        0x31f)])`;;

let SHA3_KECCAK4_F1600_AVX512_SUBROUTINE_FULL_F1600 = assume_spec SHA3_KECCAK4_F1600_AVX512_SUBROUTINE_FULL_F1600_STMT;;
