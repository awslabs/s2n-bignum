(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of the function mlkem768_check_pk of ML-KEM-768           *)
(* (arm/mlkem_native/asm/mlkem768.S) in the image of the ML-KEM API in     *)
(* assembly: the modulus check of an encapsulation key, its correctness    *)
(* and its constant-time and memory safety, stated as in the proofs of     *)
(* the compiled C of mlkem-native (see arm/mlkem_native/asm/README.md).    *)
(* The proofs are in check_pk_k3_proof.ml.                                 *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/asm/layout.ml";;
needs "arm/proofs/mlkem_native/asm/check_encoding_spec.ml";;
needs "common/fips203/fips203.ml";;
needs "arm/proofs/utils/mlkem_native2_cbd.ml";;
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(* ------------------------------------------------------------------------- *)
(* The modulus check of an encapsulation key pk: 0 if the 768 12-bit fields  *)
(* of its polynomial vector are all < q, else -4 (MLK_ERR_INVALID_PK).       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_CHECK_PK_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!pk n pc stackpointer returnaddress.
     aligned 16 stackpointer /\
     ALL (nonoverlapping (word_sub stackpointer (word 16),16))
         [(word pc,mlkem_native2_image_size); (pk,1152)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem768_check_pk) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [pk] s /\
               read (memory :> bytes(pk,1152)) s = n)
          (\s. read PC s = returnaddress /\
               C_RETURN s =
               if !i. i < 768 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
               then word 0 else word 0xfffffffc)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLKEM_NATIVE_CHECK_PK_K3_ASM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_CHECK_PK_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_CHECK_PK_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e pk pc stackpointer returnaddress.
       aligned 16 stackpointer /\
       ALL (nonoverlapping (word_sub stackpointer (word 16),16))
           [(word pc,mlkem_native2_image_size); (pk,1152)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem768_check_pk) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [pk] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events pk pc (word_sub stackpointer (word 16))
                                  returnaddress /\
                    memaccess_inbounds e2
                     [pk,1152; word_sub stackpointer (word 16),16]
                     [word_sub stackpointer (word 16),16]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLKEM_NATIVE_CHECK_PK_K3_ASM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_CHECK_PK_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;
