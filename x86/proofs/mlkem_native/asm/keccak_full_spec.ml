(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Correctness and constant-time/memory safety in one theorem ("FULL") for   *)
(* the Keccak-f1600 permutations of the x86 mlkem_native2,                   *)
(* sha3_keccak_f1600_alt2 (one state, in the image) and                      *)
(* sha3_keccak4_f1600_alt (four states), for callers that need both facts    *)
(* about the same final state, e.g. when their later control flow depends on *)
(* the permuted states. As arm/proofs/utils/mlkem_native2_keccak_full.ml for *)
(* AArch64, with the x86 forms of the code and the simulation.               *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm/noise_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The x1 permutation sha3_keccak_f1600_alt2: SHA3_KECCAK_F1600_ALT2_FULL is *)
(* proved in ../sha3_keccak_f1600_alt2.ml, its correctness theorem following *)
(* from it.                                                                  *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the IBT landing pad, as for        *)
(* SHA3_KECCAK_F1600_ALT2_NOIBT_SUBROUTINE_CORRECT and _SUBROUTINE_SAFE but  *)
(* with the frame of the former.                                             *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK_F1600_ALT2_NOIBT_SUBROUTINE_FULL_STMT =
  `exists f_events.
    forall e a rc A pc tab stackpointer returnaddress.
        riprel32_within_bounds tab (pc + 7) /\
        nonoverlapping (a,200) (word pc,998) /\
        nonoverlapping (a,200) (word tab,384) /\
        nonoverlapping (a,200) (rc,192) /\
        nonoverlapping (a,200) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   (sha3_keccak_f1600_alt2_tmc pc tab) /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 bytes_loaded s (word tab) sha3_keccak_f1600_alt2_data /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 wordlist_from_memory(a,25) s = A /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 wordlist_from_memory(a,25) s = keccak 24 A /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a tab pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,200; rc,192; word tab,384; stackpointer,8]
                      [a,200; stackpointer,8]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,200)])`;;

let SHA3_KECCAK_F1600_ALT2_NOIBT_SUBROUTINE_FULL = assume_spec SHA3_KECCAK_F1600_ALT2_NOIBT_SUBROUTINE_FULL_STMT;;

let SHA3_KECCAK_F1600_ALT2_SUBROUTINE_FULL_STMT =
  `exists f_events.
    forall e a rc A pc tab stackpointer returnaddress.
        riprel32_within_bounds tab (pc + 11) /\
        nonoverlapping (a,200) (word pc,1002) /\
        nonoverlapping (a,200) (word tab,384) /\
        nonoverlapping (a,200) (rc,192) /\
        nonoverlapping (a,200) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) (sha3_keccak_f1600_alt2_mc pc tab) /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 bytes_loaded s (word tab) sha3_keccak_f1600_alt2_data /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 wordlist_from_memory(a,25) s = A /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 wordlist_from_memory(a,25) s = keccak 24 A /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a tab pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,200; rc,192; word tab,384; stackpointer,8]
                      [a,200; stackpointer,8]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,200)])`;;

let SHA3_KECCAK_F1600_ALT2_SUBROUTINE_FULL = assume_spec SHA3_KECCAK_F1600_ALT2_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* In the image, as for SHA3_KECCAK_F1600_ALT2_IMAGE_CORRECT and             *)
(* SHA3_KECCAK_F1600_ALT2_IMAGE_SAFE, and with the state as a 1600-bit word  *)
(* as callers use it.                                                        *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK_F1600_ALT2_IMAGE_FULL_STMT =
  `exists f_events.
    forall e a rc A pc stackpointer returnaddress.
       nonoverlapping (a,200) (word pc,mlkem_native2_image_size) /\
       nonoverlapping (a,200) (rc,192) /\
       nonoverlapping (a,200) (stackpointer,8)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + sha3_keccak_f1600_alt2) /\
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
                      [a,200; rc,192;
                       word(pc + sha3_keccak_f1600_alt2_rotations),384;
                       stackpointer,8]
                      [a,200; stackpointer,8]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,200)])`;;

let SHA3_KECCAK_F1600_ALT2_IMAGE_FULL = assume_spec SHA3_KECCAK_F1600_ALT2_IMAGE_FULL_STMT;;

let SHA3_KECCAK_F1600_ALT2_IMAGE_FULL_F1600_STMT =
  `exists f_events.
    forall e a rc (S:1600 word) pc stackpointer returnaddress.
       nonoverlapping (a,200) (word pc,mlkem_native2_image_size) /\
       nonoverlapping (a,200) (rc,192) /\
       nonoverlapping (a,200) (stackpointer,8)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + sha3_keccak_f1600_alt2) /\
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
                      [a,200; rc,192;
                       word(pc + sha3_keccak_f1600_alt2_rotations),384;
                       stackpointer,8]
                      [a,200; stackpointer,8]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,200)])`;;

let SHA3_KECCAK_F1600_ALT2_IMAGE_FULL_F1600 = assume_spec SHA3_KECCAK_F1600_ALT2_IMAGE_FULL_F1600_STMT;;

(* ------------------------------------------------------------------------- *)
(* The x4 permutation sha3_keccak4_f1600_alt: SHA3_KECCAK4_F1600_ALT_FULL is *)
(* proved in ../sha3_keccak4_f1600_alt.ml, its correctness theorem following *)
(* from it.                                                                  *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the IBT landing pad, as for        *)
(* SHA3_KECCAK4_F1600_ALT_NOIBT_SUBROUTINE_CORRECT and _SUBROUTINE_SAFE: the *)
(* core runs with the stack pointer aligned down to a multiple of 32, at     *)
(* some offset delta <= 31 within the 0x31f bytes below the return address;  *)
(* and with the states as 1600-bit words as callers use them.                *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK4_F1600_ALT_NOIBT_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e rc_pointer bitstate_in rho8_ptr rho56_ptr A1 A2 A3 A4 pc
            stackpointer returnaddress.
       PAIRWISE (nonoverlapping_modulo (2 EXP 64))
         [(pc, LENGTH sha3_keccak4_f1600_alt_tmc);
          (val (word_sub stackpointer (word 0x31f)), 0x31f);
          (val bitstate_in, 800);
          (val rc_pointer, 192);
          (val rho8_ptr, 32);
          (val rho56_ptr, 32)] /\
       nonoverlapping_modulo (2 EXP 64)
         (val bitstate_in, 800)
         (val (word_sub stackpointer (word 0x31f)), 0x31f + 8)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_alt_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [bitstate_in; rc_pointer; rho8_ptr; rho56_ptr]
                             s /\
                 wordlist_from_memory(rc_pointer, 24) s = round_constants /\
                 wordlist_from_memory(rho8_ptr, 4) s = rho8_constant /\
                 wordlist_from_memory(rho56_ptr, 4) s = rho56_constant /\
                 wordlist_from_memory(bitstate_in, 25) s = A1 /\
                 wordlist_from_memory(word_add bitstate_in (word 200), 25) s =
                 A2 /\
                 wordlist_from_memory(word_add bitstate_in (word 400), 25) s =
                 A3 /\
                 wordlist_from_memory(word_add bitstate_in (word 600), 25) s =
                 A4 /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 wordlist_from_memory(bitstate_in, 25) s = keccak 24 A1 /\
                 wordlist_from_memory(word_add bitstate_in (word 200), 25) s =
                 keccak 24 A2 /\
                 wordlist_from_memory(word_add bitstate_in (word 400), 25) s =
                 keccak 24 A3 /\
                 wordlist_from_memory(word_add bitstate_in (word 600), 25) s =
                 keccak 24 A4 /\
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

let SHA3_KECCAK4_F1600_ALT_NOIBT_SUBROUTINE_FULL = assume_spec SHA3_KECCAK4_F1600_ALT_NOIBT_SUBROUTINE_FULL_STMT;;

let SHA3_KECCAK4_F1600_ALT_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e rc_pointer bitstate_in rho8_ptr rho56_ptr A1 A2 A3 A4 pc
            stackpointer returnaddress.
       PAIRWISE (nonoverlapping_modulo (2 EXP 64))
         [(pc, LENGTH sha3_keccak4_f1600_alt_mc);
          (val (word_sub stackpointer (word 0x31f)), 0x31f);
          (val bitstate_in, 800);
          (val rc_pointer, 192);
          (val rho8_ptr, 32);
          (val rho56_ptr, 32)] /\
       nonoverlapping_modulo (2 EXP 64)
         (val bitstate_in, 800)
         (val (word_sub stackpointer (word 0x31f)), 0x31f + 8)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_alt_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [bitstate_in; rc_pointer; rho8_ptr; rho56_ptr]
                             s /\
                 wordlist_from_memory(rc_pointer, 24) s = round_constants /\
                 wordlist_from_memory(rho8_ptr, 4) s = rho8_constant /\
                 wordlist_from_memory(rho56_ptr, 4) s = rho56_constant /\
                 wordlist_from_memory(bitstate_in, 25) s = A1 /\
                 wordlist_from_memory(word_add bitstate_in (word 200), 25) s =
                 A2 /\
                 wordlist_from_memory(word_add bitstate_in (word 400), 25) s =
                 A3 /\
                 wordlist_from_memory(word_add bitstate_in (word 600), 25) s =
                 A4 /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 wordlist_from_memory(bitstate_in, 25) s = keccak 24 A1 /\
                 wordlist_from_memory(word_add bitstate_in (word 200), 25) s =
                 keccak 24 A2 /\
                 wordlist_from_memory(word_add bitstate_in (word 400), 25) s =
                 keccak 24 A3 /\
                 wordlist_from_memory(word_add bitstate_in (word 600), 25) s =
                 keccak 24 A4 /\
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

let SHA3_KECCAK4_F1600_ALT_SUBROUTINE_FULL = assume_spec SHA3_KECCAK4_F1600_ALT_SUBROUTINE_FULL_STMT;;

let SHA3_KECCAK4_F1600_ALT_SUBROUTINE_FULL_F1600_STMT =
  `exists f_events.
     forall e rc_pointer bitstate_in rho8_ptr rho56_ptr
            (S1:1600 word) (S2:1600 word) (S3:1600 word) (S4:1600 word)
            pc stackpointer returnaddress.
       PAIRWISE (nonoverlapping_modulo (2 EXP 64))
         [(pc, LENGTH sha3_keccak4_f1600_alt_mc);
          (val (word_sub stackpointer (word 0x31f)), 0x31f);
          (val bitstate_in, 800);
          (val rc_pointer, 192);
          (val rho8_ptr, 32);
          (val rho56_ptr, 32)] /\
       nonoverlapping_modulo (2 EXP 64)
         (val bitstate_in, 800)
         (val (word_sub stackpointer (word 0x31f)), 0x31f + 8)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_alt_mc /\
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

let SHA3_KECCAK4_F1600_ALT_SUBROUTINE_FULL_F1600 = assume_spec SHA3_KECCAK4_F1600_ALT_SUBROUTINE_FULL_F1600_STMT;;
