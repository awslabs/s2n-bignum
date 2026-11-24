(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of mlkem_tomsg that the proofs of the callers in the      *)
(* image of the ML-KEM API in assembly use: the correctness theorem of     *)
(* arm/proofs/mlkem_tomsg.ml, and the safety theorem of that file with     *)
(* the frame of the correctness theorem. They are stated about the code    *)
(* of that file, mlkem_tomsg_mc, which is also in the image, where         *)
(* ARM_SUBROUTINE_SIM_TAC uses them for it (see                            *)
(* arm/mlkem_native/asm/README.md). The proof file loads the standalone    *)
(* proof, which proves the first, and makes the second from its safety     *)
(* theorem.                                                                *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;

let mlkem_tomsg_mc = define_from_elf
 "mlkem_tomsg_mc" "arm/mlkem/mlkem_tomsg.o";;

let MLKEM_TOMSG_SUBROUTINE_CORRECT_STMT =
 `!r a x pc returnaddress.
        ALL (nonoverlapping (r,32)) [(word pc,0xe0); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_tomsg_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,32)) s =
                       nsum {i | i < 256}
                            (\i. ((4 * val(x i) + 3329) DIV 6658) MOD 2 *
                                 2 EXP i)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,32)])`;;

let MLKEM_TOMSG_SUBROUTINE_CORRECT =
  assume_spec MLKEM_TOMSG_SUBROUTINE_CORRECT_STMT;;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_TOMSG_SUBROUTINE_SAFE_FRAMED_STMT =
 `exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,32)) [(word pc,0xe0); (a,512)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_tomsg_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,32] [r,32])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,32)])`;;

let MLKEM_TOMSG_SUBROUTINE_SAFE_FRAMED =
  assume_spec MLKEM_TOMSG_SUBROUTINE_SAFE_FRAMED_STMT;;
