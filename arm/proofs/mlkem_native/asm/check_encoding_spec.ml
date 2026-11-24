(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of mlkem_check_encoding that the proofs of the callers    *)
(* in the image of the ML-KEM API in assembly use: the check that the      *)
(* 12-bit fields of an encoding are below q, with the events alone and     *)
(* together with the result. They are stated about the code of the         *)
(* standalone proof, mlkem_check_encoding_mc, which is also in the image,  *)
(* where ARM_SUBROUTINE_SIM_TAC uses them for it (see                      *)
(* arm/mlkem_native/asm/README.md). The proof file proves them from the    *)
(* standalone proof of the library.                                        *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;

let mlkem_check_encoding_mc = define_from_elf
 "mlkem_check_encoding_mc" "arm/mlkem/mlkem_check_encoding.o";;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_CHECK_ENCODING_SUBROUTINE_CORRECT_STMT =
 `!a k n pc returnaddress.
        val k < 2 EXP 61
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_check_encoding_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; k] s /\
                  read (memory :> bytes(a,384 * val k)) s = n)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                  if !i. i < 256 * val k
                         ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
                  then word 1 else word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`;;

let MLKEM_CHECK_ENCODING_SUBROUTINE_CORRECT =
  assume_spec MLKEM_CHECK_ENCODING_SUBROUTINE_CORRECT_STMT;;

let MLKEM_CHECK_ENCODING_SUBROUTINE_SAFE_FRAMED_STMT =
 `exists f_events.
       forall e a k pc returnaddress.
           val k < 2 EXP 61
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_check_encoding_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; k] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a k pc returnaddress /\
                        memaccess_inbounds e2 [a,(384 * val k) * 1] []))
               MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`;;

let MLKEM_CHECK_ENCODING_SUBROUTINE_SAFE_FRAMED =
  assume_spec MLKEM_CHECK_ENCODING_SUBROUTINE_SAFE_FRAMED_STMT;;

let MLKEM_CHECK_ENCODING_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a k n pc returnaddress.
         val k < 2 EXP 61
         ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_check_encoding_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; k] s /\
                  read (memory :> bytes(a,384 * val k)) s = n /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                  (if !i. i < 256 * val k
                          ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
                   then word 1 else word 0) /\
                  (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events a k pc returnaddress /\
                      memaccess_inbounds e2 [a,(384 * val k) * 1] []))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`;;

let MLKEM_CHECK_ENCODING_SUBROUTINE_FULL =
  assume_spec MLKEM_CHECK_ENCODING_SUBROUTINE_FULL_STMT;;
