(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Correctness and constant-time/memory safety in one theorem ("FULL") for   *)
(* the AVX-512VL Keccak-f1600 permutations sha3_keccak_f1600_avx512 and      *)
(* sha3_keccak4_f1600_avx512, as utils/mlkem_native2_keccak_full.ml has them *)
(* for the AVX2 ones, for callers that need both facts about the same final  *)
(* state. Each is the proof of correctness with the events: the loop taken   *)
(* from the start of an iteration to the end of the branch back, as in the   *)
(* proof of safety, and an iteration split at its rounds, the events of an   *)
(* iteration being those of its four rounds.                                 *)
(* ========================================================================= *)

needs "x86/proofs/sha3_keccak_f1600_avx512.ml";;
needs "x86/proofs/sha3_keccak4_f1600_avx512.ml";;

(* ------------------------------------------------------------------------- *)
(* The cores, SHA3_KECCAK_F1600_AVX512_FULL and                              *)
(* SHA3_KECCAK4_F1600_AVX512_FULL, are proved in                             *)
(* ../sha3_keccak_f1600_avx512.ml and ../sha3_keccak4_f1600_avx512.ml (their *)
(* correctness theorems follow from them); here are their subroutine forms.  *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK_F1600_AVX512_NOIBT_SUBROUTINE_FULL = time prove
 (`exists f_events.
    forall e a rc A pc stackpointer returnaddress.
        nonoverlapping (a,200) (word pc,0xd0d) /\
        nonoverlapping (a,200) (rc,192) /\
        nonoverlapping (a,200) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) sha3_keccak_f1600_avx512_tmc /\
                 read RIP s = word pc /\
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
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  X86_ADD_RETURN_NOSTACK_TAC SHA3_KECCAK_F1600_AVX512_TMC_EXEC
   (CONV_RULE TWEAK_CONV SHA3_KECCAK_F1600_AVX512_FULL) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let SHA3_KECCAK_F1600_AVX512_SUBROUTINE_FULL = time prove
 (`exists f_events.
    forall e a rc A pc stackpointer returnaddress.
        nonoverlapping (a,200) (word pc,0xd11) /\
        nonoverlapping (a,200) (rc,192) /\
        nonoverlapping (a,200) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) sha3_keccak_f1600_avx512_mc /\
                 read RIP s = word pc /\
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
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   (CONV_RULE TWEAK_CONV SHA3_KECCAK_F1600_AVX512_NOIBT_SUBROUTINE_FULL)));;

let SHA3_KECCAK4_F1600_AVX512_NOIBT_SUBROUTINE_FULL = time prove
 (`exists f_events.
    forall e a rc A1 A2 A3 A4 pc stackpointer returnaddress.
        nonoverlapping (a,800) (word pc,0x1065) /\
        nonoverlapping (a,800) (rc,192) /\
        nonoverlapping (a,800) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_avx512_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 wordlist_from_memory(a,25) s = A1 /\
                 wordlist_from_memory(word_add a (word 200),25) s = A2 /\
                 wordlist_from_memory(word_add a (word 400),25) s = A3 /\
                 wordlist_from_memory(word_add a (word 600),25) s = A4 /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 wordlist_from_memory(a,25) s = keccak 24 A1 /\
                 wordlist_from_memory(word_add a (word 200),25) s =
                 keccak 24 A2 /\
                 wordlist_from_memory(word_add a (word 400),25) s =
                 keccak 24 A3 /\
                 wordlist_from_memory(word_add a (word 600),25) s =
                 keccak 24 A4 /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,800; rc,192; stackpointer,8]
                      [a,800]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,800)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  X86_ADD_RETURN_NOSTACK_TAC SHA3_KECCAK4_F1600_AVX512_TMC_EXEC
   (CONV_RULE TWEAK_CONV SHA3_KECCAK4_F1600_AVX512_FULL) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let SHA3_KECCAK4_F1600_AVX512_SUBROUTINE_FULL = time prove
 (`exists f_events.
    forall e a rc A1 A2 A3 A4 pc stackpointer returnaddress.
        nonoverlapping (a,800) (word pc,0x1069) /\
        nonoverlapping (a,800) (rc,192) /\
        nonoverlapping (a,800) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_avx512_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 wordlist_from_memory(a,25) s = A1 /\
                 wordlist_from_memory(word_add a (word 200),25) s = A2 /\
                 wordlist_from_memory(word_add a (word 400),25) s = A3 /\
                 wordlist_from_memory(word_add a (word 600),25) s = A4 /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 wordlist_from_memory(a,25) s = keccak 24 A1 /\
                 wordlist_from_memory(word_add a (word 200),25) s =
                 keccak 24 A2 /\
                 wordlist_from_memory(word_add a (word 400),25) s =
                 keccak 24 A3 /\
                 wordlist_from_memory(word_add a (word 600),25) s =
                 keccak 24 A4 /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,800; rc,192; stackpointer,8]
                      [a,800]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,800)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   (CONV_RULE TWEAK_CONV SHA3_KECCAK4_F1600_AVX512_NOIBT_SUBROUTINE_FULL)));;
