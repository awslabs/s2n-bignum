(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of mlkem_tomont that the proofs of the callers in the     *)
(* image of the ML-KEM API in assembly use: the correctness theorem of     *)
(* arm/proofs/mlkem_tomont.ml, and the safety theorem of that file with    *)
(* the frame of the correctness theorem. They are stated about the code    *)
(* of that file, mlkem_tomont_mc, which is also in the image, where        *)
(* ARM_SUBROUTINE_SIM_TAC uses them for it (see                            *)
(* arm/mlkem_native/asm/README.md). The proof file loads the standalone    *)
(* proof, which proves the first, and makes the second from its safety     *)
(* theorem.                                                                *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "common/mlkem_mldsa.ml";;

let mlkem_tomont_mc = define_from_elf
 "mlkem_tomont_mc" "arm/mlkem/mlkem_tomont.o";;

let MLKEM_TOMONT_SUBROUTINE_CORRECT_STMT =
 `!ptr x pc returnaddress.
    nonoverlapping (word pc, LENGTH mlkem_tomont_mc) (ptr, 512)
    ==>
    ensures arm
      (\s. // Assert that poly_tomont is loaded at PC
           aligned_bytes_loaded s (word pc) mlkem_tomont_mc /\
           read PC s = word pc  /\
           // Remember LR as point-to-stop
           read X30 s = returnaddress /\
           // poly_tomont takes one argument, the base pointer
           C_ARGUMENTS [ptr] s  /\
           // Give name to 16-bit coefficients stored at ptr to be
           // able to refer to them in the post-condition
           (!i. i < 256
                ==> read(memory :> bytes16(word_add ptr (word (2 * i)))) s =
                    x i)
          )
      (\s. // We have reached the LR
           read PC s = returnaddress /\
           // Coefficients have changed according to tomont_3329 and
           // are < MLKEM_Q in absolute value.
           (!i. i < 256
                ==> let z_i = read(memory :> bytes16
                                       (word_add ptr (word (2 * i)))) s in
                    (ival z_i == (tomont_3329 (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
          )
      // Register and memory footprint
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(ptr, 512)])`;;

let MLKEM_TOMONT_SUBROUTINE_CORRECT =
  assume_spec MLKEM_TOMONT_SUBROUTINE_CORRECT_STMT;;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_TOMONT_SUBROUTINE_SAFE_FRAMED_STMT =
 `exists f_events.
       forall e ptr pc returnaddress.
           nonoverlapping (word pc,LENGTH mlkem_tomont_mc) (ptr,512)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) mlkem_tomont_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [ptr] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events ptr pc returnaddress /\
                        memaccess_inbounds e2 [ptr,512] [ptr,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(ptr, 512)])`;;

let MLKEM_TOMONT_SUBROUTINE_SAFE_FRAMED =
  assume_spec MLKEM_TOMONT_SUBROUTINE_SAFE_FRAMED_STMT;;
