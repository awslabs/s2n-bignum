(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of sha3_keccak4_f1600_alt2 that the proofs of the         *)
(* callers in the image of the ML-KEM API in assembly use: the             *)
(* permutation of four Keccak states in memory, with the states as         *)
(* 1600-bit words, and with the events together with the results. They     *)
(* are stated about the code of the standalone proof,                      *)
(* sha3_keccak4_f1600_alt2_mc, which is also in the image, where           *)
(* ARM_SUBROUTINE_SIM_TAC uses them for it (see                            *)
(* arm/mlkem_native/asm/README.md). The proof file proves them from the    *)
(* standalone proof of the library.                                        *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/keccak_spec.ml";;
needs "common/fips202/fips202.ml";;

let sha3_keccak4_f1600_alt2_mc = define_from_elf
 "sha3_keccak4_f1600_alt2_mc" "arm/sha3/sha3_keccak4_f1600_alt2.o";;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_CORRECT_F1600_STMT =
 `!a rc (S1:1600 word) (S2:1600 word) (S3:1600 word) (S4:1600 word)
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
              memory :> bytes(word_sub stackpointer (word 224),224)])`;;

let SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_CORRECT_F1600 =
  assume_spec SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_CORRECT_F1600_STMT;;

let SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_SAFE_FRAMED_STMT =
 `exists f_events.
       forall e a rc pc stackpointer returnaddress.
           aligned 16 stackpointer /\
           nonoverlapping (a,800) (word_sub stackpointer (word 224),224) /\
           ALLPAIRS nonoverlapping
           [a,800; word_sub stackpointer (word 224),224]
           [word pc,0xda0; rc,192]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      sha3_keccak4_f1600_alt2_mc /\
                    read PC s = word pc /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; rc] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
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
                  memory :> bytes(word_sub stackpointer (word 224),224)])`;;

let SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_SAFE_FRAMED =
  assume_spec SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_SAFE_FRAMED_STMT;;

let SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_FULL_F1600_STMT =
 `exists f_events.
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
              memory :> bytes(word_sub stackpointer (word 224),224)])`;;

let SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_FULL_F1600 =
  assume_spec SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_FULL_F1600_STMT;;
