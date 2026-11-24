(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of mlkem_frombytes that the proofs of the callers in the  *)
(* image of the ML-KEM API in assembly use: the correctness theorem of     *)
(* arm/proofs/mlkem_frombytes.ml, and the safety theorem of that file      *)
(* with the frame of the correctness theorem. They are stated about the    *)
(* code of that file, mlkem_frombytes_mc, which is also in the image,      *)
(* where ARM_SUBROUTINE_SIM_TAC uses them for it (see                      *)
(* arm/mlkem_native/asm/README.md). The proof file loads the standalone    *)
(* proof, which proves the first, and makes the second from its safety     *)
(* theorem.                                                                *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;

let mlkem_frombytes_mc = define_from_elf
 "mlkem_frombytes_mc" "arm/mlkem/mlkem_frombytes.o";;

let MLKEM_FROMBYTES_SUBROUTINE_CORRECT_STMT =
 `!r a n pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0x9c); (a,384)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_frombytes_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,384)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_FROMBYTES_SUBROUTINE_CORRECT =
  assume_spec MLKEM_FROMBYTES_SUBROUTINE_CORRECT_STMT;;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_FROMBYTES_SUBROUTINE_SAFE_FRAMED_STMT =
 `exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [(word pc,0x9c); (a,384)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_frombytes_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,384; r,512] [r,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_FROMBYTES_SUBROUTINE_SAFE_FRAMED =
  assume_spec MLKEM_FROMBYTES_SUBROUTINE_SAFE_FRAMED_STMT;;
