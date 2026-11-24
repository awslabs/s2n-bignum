(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of mlkem_tobytes_alt that the proofs of the callers in    *)
(* the image of the ML-KEM API in assembly use: the correctness theorem    *)
(* of arm/proofs/mlkem_tobytes_alt.ml, and the safety theorem of that      *)
(* file with the frame of the correctness theorem. They are stated about   *)
(* the code of that file, mlkem_tobytes_alt_mc, which is also in the       *)
(* image, where ARM_SUBROUTINE_SIM_TAC uses them for it (see               *)
(* arm/mlkem_native/asm/README.md). The proof file loads the standalone    *)
(* proof, which proves the first, and makes the second from its safety     *)
(* theorem.                                                                *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "common/mlkem_mldsa.ml";;

let mlkem_tobytes_alt_mc = define_from_elf
 "mlkem_tobytes_alt_mc" "arm/mlkem/mlkem_tobytes_alt.o";;

let MLKEM_TOBYTES_ALT_SUBROUTINE_CORRECT_STMT =
 `!r a (l:int16 list) pc returnaddress.
        ALL (nonoverlapping (r,384)) [(word pc,0x10c); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_tobytes_alt_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = returnaddress /\
                  (LENGTH l = 256
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_TOBYTES_ALT_SUBROUTINE_CORRECT =
  assume_spec MLKEM_TOBYTES_ALT_SUBROUTINE_CORRECT_STMT;;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_TOBYTES_ALT_SUBROUTINE_SAFE_FRAMED_STMT =
 `exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,384)) [word pc,0x10c; a,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) mlkem_tobytes_alt_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,384] [r,384])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_TOBYTES_ALT_SUBROUTINE_SAFE_FRAMED =
  assume_spec MLKEM_TOBYTES_ALT_SUBROUTINE_SAFE_FRAMED_STMT;;
