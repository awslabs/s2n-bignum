(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of the function mlkem512_check_sk of ML-KEM-512           *)
(* (arm/mlkem_native/asm/mlkem512.S) in the image of the ML-KEM API in     *)
(* assembly: the hash check of a decapsulation key, its correctness and    *)
(* its constant-time and memory safety, stated as in the proofs of the     *)
(* compiled C of mlkem-native (see arm/mlkem_native/asm/README.md). The    *)
(* proofs are in check_sk_k2_proof.ml.                                     *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/asm/layout.ml";;
needs "arm/proofs/mlkem_native/asm/hash_h_spec.ml";;
needs "common/fips203/fips203.ml";;
needs "arm/proofs/utils/mlkem_native2_cbd.ml";;
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(* ------------------------------------------------------------------------- *)
(* The hash check of a decapsulation key sk, with ek at offset 768 and the   *)
(* hash h of ek at offset 1568: 0 if h = H(ek), else -5                      *)
(* (MLK_ERR_INVALID_SK). The stack is the 64 bytes of the frame and the 384  *)
(* used by mlkem_hash_h. As for all the API functions, the image must be at  *)
(* a multiple of 4096, for the address of the constants block by ADRP.       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_CHECK_SK_K2_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!sk (ek:byte list) h pc stackpointer returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + mlkem_native2_image_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH ek = 800 /\
     ALL (nonoverlapping (word_sub stackpointer (word 448),448))
         [(word pc,mlkem_native2_image_size); (sk,1632)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem512_check_sk) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [sk] s /\
               read (memory :> bytes(word_add sk (word 768),800)) s =
               num_of_bytelist ek /\
               read (memory :> bytes(word_add sk (word 1568),32)) s = h)
          (\s. read PC s = returnaddress /\
               C_RETURN s =
               if h = num_of_bytelist(sha3_256 ek) then word 0
               else word 0xfffffffb)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 448),448)])`;;

let MLKEM_NATIVE_CHECK_SK_K2_ASM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_CHECK_SK_K2_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_CHECK_SK_K2_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e sk pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\
       pc + mlkem_native2_image_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       ALL (nonoverlapping (word_sub stackpointer (word 448),448))
           [(word pc,mlkem_native2_image_size); (sk,1632)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem512_check_sk) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [sk] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events sk pc (word_sub stackpointer (word 448))
                                  returnaddress /\
                    memaccess_inbounds e2
                     [sk,1632; word(pc + mlkem_native2_constants),192;
                      word_sub stackpointer (word 448),448]
                     [word_sub stackpointer (word 448),448]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(word_sub stackpointer (word 448),448)])`;;

let MLKEM_NATIVE_CHECK_SK_K2_ASM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_CHECK_SK_K2_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;
