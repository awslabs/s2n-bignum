(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of mlkem_cbd2 that the proofs of the callers in the       *)
(* image of the ML-KEM API in assembly use: the sampling of a polynomial   *)
(* from 128 bytes by CBD with eta = 2, with the coefficients of            *)
(* SamplePolyCBD. They are stated about the code of the standalone proof,  *)
(* mlkem_cbd2_mc, which is also in the image, where                        *)
(* ARM_SUBROUTINE_SIM_TAC uses them for it (see                            *)
(* arm/mlkem_native/asm/README.md). The proof file proves them from the    *)
(* standalone proof of the library.                                        *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;
needs "arm/proofs/utils/mlkem_native2_cbd.ml";;

let mlkem_cbd2_mc = define_from_elf
 "mlkem_cbd2_mc" "arm/mlkem/mlkem_cbd2.o";;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_CBD2_SUBROUTINE_CORRECT_COEFF_STMT =
 `!r a (b:byte list) pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0x10c); (a,128)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_cbd2_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = num_of_bytelist b)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(mlkem_cbd_coeff 2 b i))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_CBD2_SUBROUTINE_CORRECT_COEFF =
  assume_spec MLKEM_CBD2_SUBROUTINE_CORRECT_COEFF_STMT;;

let MLKEM_CBD2_SUBROUTINE_SAFE_FRAMED_STMT =
 `exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [word pc,0x10c; a,128]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_cbd2_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,128; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_CBD2_SUBROUTINE_SAFE_FRAMED =
  assume_spec MLKEM_CBD2_SUBROUTINE_SAFE_FRAMED_STMT;;
