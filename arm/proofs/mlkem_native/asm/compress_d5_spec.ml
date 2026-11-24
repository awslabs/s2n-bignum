(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of mlkem_compress_d5 that the proofs of the callers in    *)
(* the image of the ML-KEM API in assembly use: the correctness theorem    *)
(* of arm/proofs/mlkem_compress_d5.ml, and the safety theorem of that      *)
(* file with the frame of the correctness theorem. They are stated about   *)
(* the code of that file, mlkem_compress_d5_mc, which is also in the       *)
(* image, where ARM_SUBROUTINE_SIM_TAC uses them for it (see               *)
(* arm/mlkem_native/asm/README.md). The proof file loads the standalone    *)
(* proof, which proves the first, and makes the second from its safety     *)
(* theorem.                                                                *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;

let mlkem_compress_d5_mc = define_from_elf
 "mlkem_compress_d5_mc" "arm/mlkem/mlkem_compress_d5.o";;

let MLKEM_COMPRESS_D5_SUBROUTINE_CORRECT_STMT =
 `!r a x pc returnaddress.
        ALL (nonoverlapping (r,160)) [(word pc,0x1c0); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d5_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,160)) s =
                       nsum {i | i < 256}
                            (\i. ((64 * val(x i) + 3329) DIV 6658) MOD 32 *
                                 2 EXP (5 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,160)])`;;

let MLKEM_COMPRESS_D5_SUBROUTINE_CORRECT =
  assume_spec MLKEM_COMPRESS_D5_SUBROUTINE_CORRECT_STMT;;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_COMPRESS_D5_SUBROUTINE_SAFE_FRAMED_STMT =
 `exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,160)) [(word pc,0x1c0); (a,512)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d5_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,160] [r,160])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,160)])`;;

let MLKEM_COMPRESS_D5_SUBROUTINE_SAFE_FRAMED =
  assume_spec MLKEM_COMPRESS_D5_SUBROUTINE_SAFE_FRAMED_STMT;;
