(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of mlkem_reduce that the proofs of the callers in the     *)
(* image of the ML-KEM API in assembly use: the correctness theorem of     *)
(* arm/proofs/mlkem_reduce.ml, and the safety theorem of that file with    *)
(* the frame of the correctness theorem. They are stated about the code    *)
(* of that file, mlkem_reduce_mc, which is also in the image, where        *)
(* ARM_SUBROUTINE_SIM_TAC uses them for it (see                            *)
(* arm/mlkem_native/asm/README.md). The proof file loads the standalone    *)
(* proof, which proves the first, and makes the second from its safety     *)
(* theorem.                                                                *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "common/mlkem_mldsa.ml";;

let mlkem_reduce_mc = define_from_elf
 "mlkem_reduce_mc" "arm/mlkem/mlkem_reduce.o";;

let MLKEM_REDUCE_SUBROUTINE_CORRECT_STMT =
 `!a x pc returnaddress.
        nonoverlapping (word pc,0x124) (a,512)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_reduce_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_REDUCE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_REDUCE_SUBROUTINE_CORRECT_STMT;;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_REDUCE_SUBROUTINE_SAFE_FRAMED_STMT =
 `exists f_events.
       forall e a pc returnaddress.
           nonoverlapping (word pc,292) (a,512)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) mlkem_reduce_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a pc returnaddress /\
                        memaccess_inbounds e2 [a,512] [a,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_REDUCE_SUBROUTINE_SAFE_FRAMED =
  assume_spec MLKEM_REDUCE_SUBROUTINE_SAFE_FRAMED_STMT;;
