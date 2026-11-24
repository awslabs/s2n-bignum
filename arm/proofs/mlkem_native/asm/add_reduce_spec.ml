(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of mlkem_add_reduce that the proofs of the callers in     *)
(* the image of the ML-KEM API in assembly use: the correctness theorem    *)
(* of arm/proofs/mlkem_add_reduce.ml, and the safety theorem of that file  *)
(* with the frame of the correctness theorem. They are stated about the    *)
(* code of that file, mlkem_add_reduce_mc, which is also in the image,     *)
(* where ARM_SUBROUTINE_SIM_TAC uses them for it (see                      *)
(* arm/mlkem_native/asm/README.md). The proof file loads the standalone    *)
(* proof, which proves the first, and makes the second from its safety     *)
(* theorem.                                                                *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "common/mlkem_mldsa.ml";;

let mlkem_add_reduce_mc = define_from_elf
 "mlkem_add_reduce_mc" "arm/mlkem/mlkem_add_reduce.o";;

let MLKEM_ADD_REDUCE_SUBROUTINE_CORRECT_STMT =
 `!r a x y pc returnaddress.
        ALL (nonoverlapping (word pc,0xac)) [(r,512); (a,512)] /\
        nonoverlapping (r,512) (a,512)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_add_reduce_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                 (word_add r (word(2 * i)))) s =
                           x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s =
                           y i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add r (word(2 * i)))) s) =
                          ival(word_add (x i) (y i)) rem &3329)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_ADD_REDUCE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_ADD_REDUCE_SUBROUTINE_CORRECT_STMT;;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_ADD_REDUCE_SUBROUTINE_SAFE_FRAMED_STMT =
 `exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (word pc,0xac)) [(r,512); (a,512)] /\
           nonoverlapping (r,512) (a,512)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_add_reduce_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [r,512; a,512] [r,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_ADD_REDUCE_SUBROUTINE_SAFE_FRAMED =
  assume_spec MLKEM_ADD_REDUCE_SUBROUTINE_SAFE_FRAMED_STMT;;
