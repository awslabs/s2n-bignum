(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* Proofs of the contracts of sha3_keccak4_f1600_alt2 (see                 *)
(* keccak4_f1600_alt2_spec.ml). The standalone proof of                    *)
(* arm/proofs/sha3_keccak4_f1600_alt2.ml runs here, in the job of this     *)
(* file, so that it runs once: it proves the safety with the frame of the  *)
(* correctness theorem, and the core of the events, from which the two in  *)
(* one follow here. The correctness theorem with the states as 1600-bit    *)
(* words is made from its correctness theorem.                             *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/asm/keccak4_f1600_alt2_spec.ml";;
needs "arm/proofs/utils/keccak_fips202.ml";;

loadt "arm/proofs/sha3_keccak4_f1600_alt2.ml";;

let SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_CORRECT_F1600 = prove
 (`!a rc (S1:1600 word) (S2:1600 word) (S3:1600 word) (S4:1600 word)
    pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (a,800) (word_sub stackpointer (word 224),224) /\
      ALLPAIRS nonoverlapping
               [(a,800); (word_sub stackpointer (word 224),224)]
               [(word pc,0xda0); (rc,192)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) sha3_keccak4_f1600_alt2_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a; rc] s /\
                read (memory :> wbytes a) s = S1 /\
                read (memory :> wbytes(word_add a (word 200))) s = S2 /\
                read (memory :> wbytes(word_add a (word 400))) s = S3 /\
                read (memory :> wbytes(word_add a (word 600))) s = S4 /\
                wordlist_from_memory(rc,24) s = round_constants)
           (\s. read PC s = returnaddress /\
                read (memory :> wbytes a) s = keccak_f1600 S1 /\
                read (memory :> wbytes(word_add a (word 200))) s =
                keccak_f1600 S2 /\
                read (memory :> wbytes(word_add a (word 400))) s =
                keccak_f1600 S3 /\
                read (memory :> wbytes(word_add a (word 600))) s =
                keccak_f1600 S4)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(a,800);
              memory :> bytes(word_sub stackpointer (word 224),224)])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:int64`; `rc:int64`;
                `wordlist_of_num 25 (val(S1:1600 word)):int64 list`;
                `wordlist_of_num 25 (val(S2:1600 word)):int64 list`;
                `wordlist_of_num 25 (val(S3:1600 word)):int64 list`;
                `wordlist_of_num 25 (val(S4:1600 word)):int64 list`;
                `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
               SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_CORRECT) THEN
  ASM_REWRITE_TAC[GSYM READ_MEMORY_WBYTES_KECCAK] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (ONCE_REWRITE_RULE[CONJ_SYM] ENSURES_POSTCONDITION_THM))) THEN
  MESON_TAC[KECCAK_F1600_MEMORY]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine, with the saving of registers and the return, as for       *)
(* SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_CORRECT and _SUBROUTINE_SAFE_FRAMED.   *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_FULL = time prove
 (`exists f_events.
     forall e a rc A1 A2 A3 A4 pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (a,800) (word_sub stackpointer (word 224),224) /\
      ALLPAIRS nonoverlapping
               [(a,800); (word_sub stackpointer (word 224),224)]
               [(word pc,0xda0); (rc,192)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) sha3_keccak4_f1600_alt2_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a; rc] s /\
                wordlist_from_memory(a,25) s = A1 /\
                wordlist_from_memory(word_add a (word 200),25) s = A2 /\
                wordlist_from_memory(word_add a (word 400),25) s = A3 /\
                wordlist_from_memory(word_add a (word 600),25) s = A4 /\
                wordlist_from_memory(rc,24) s = round_constants /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                wordlist_from_memory(a,25) s = keccak 24 A1 /\
                wordlist_from_memory(word_add a (word 200),25) s =
                keccak 24 A2 /\
                wordlist_from_memory(word_add a (word 400),25) s =
                keccak 24 A3 /\
                wordlist_from_memory(word_add a (word 600),25) s =
                keccak 24 A4 /\
                (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events rc a pc
                           (word_sub stackpointer (word 224))
                           returnaddress /\
                    memaccess_inbounds e2
                    [a,800; rc,192; word_sub stackpointer (word 224),224]
                    [a,800; word_sub stackpointer (word 224),224]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(a,800);
              memory :> bytes(word_sub stackpointer (word 224),224)])`,
  let TWEAK_CONV =
   ONCE_DEPTH_CONV
    (WORDLIST_FROM_MEMORY_CONV THENC
     ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) in
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(11,11)
    SHA3_KECCAK4_F1600_ALT2_EXEC
    (CONV_RULE TWEAK_CONV SHA3_KECCAK4_F1600_ALT2_FULL)
    `[D8; D9; D10; D11; D12; D13; D14; D15;
      X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30]` 224 THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The form callers use, the states as 1600-bit words as for                 *)
(* SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_CORRECT_F1600, with the events of      *)
(* SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_SAFE_FRAMED.                           *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_FULL_F1600 = prove
 (`exists f_events.
     forall e a rc (S1:1600 word) (S2:1600 word) (S3:1600 word)
            (S4:1600 word) pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (a,800) (word_sub stackpointer (word 224),224) /\
      ALLPAIRS nonoverlapping
               [(a,800); (word_sub stackpointer (word 224),224)]
               [(word pc,0xda0); (rc,192)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) sha3_keccak4_f1600_alt2_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a; rc] s /\
                read (memory :> wbytes a) s = S1 /\
                read (memory :> wbytes(word_add a (word 200))) s = S2 /\
                read (memory :> wbytes(word_add a (word 400))) s = S3 /\
                read (memory :> wbytes(word_add a (word 600))) s = S4 /\
                wordlist_from_memory(rc,24) s = round_constants /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                read (memory :> wbytes a) s = keccak_f1600 S1 /\
                read (memory :> wbytes(word_add a (word 200))) s =
                keccak_f1600 S2 /\
                read (memory :> wbytes(word_add a (word 400))) s =
                keccak_f1600 S3 /\
                read (memory :> wbytes(word_add a (word 600))) s =
                keccak_f1600 S4 /\
                (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events rc a pc
                           (word_sub stackpointer (word 224))
                           returnaddress /\
                    memaccess_inbounds e2
                    [a,800; rc,192; word_sub stackpointer (word 224),224]
                    [a,800; word_sub stackpointer (word 224),224]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(a,800);
              memory :> bytes(word_sub stackpointer (word 224),224)])`,
  MP_TAC SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `f:int64->int64->num->int64->int64->(uarch_event)list` THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `rc:int64`; `S1:1600 word`;
    `S2:1600 word`; `S3:1600 word`; `S4:1600 word`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `rc:int64`;
    `wordlist_of_num 25 (val(S1:1600 word)):int64 list`;
    `wordlist_of_num 25 (val(S2:1600 word)):int64 list`;
    `wordlist_of_num 25 (val(S3:1600 word)):int64 list`;
    `wordlist_of_num 25 (val(S4:1600 word)):int64 list`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[GSYM READ_MEMORY_WBYTES_KECCAK] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (ONCE_REWRITE_RULE[CONJ_SYM] ENSURES_POSTCONDITION_THM))) THEN
  MESON_TAC[KECCAK_F1600_MEMORY]);;
