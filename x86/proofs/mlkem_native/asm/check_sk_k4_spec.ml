(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The function mlkem1024_check_sk of the build asm: the hash check of a     *)
(* decapsulation key, with its correctness and its constant-time and         *)
(* memory safety.                                                            *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm/api_spec.ml";;
needs "x86/proofs/mlkem_native/asm/kem_spec.ml";;
needs "x86/proofs/mlkem_native/asm/gen_matrix_k4_spec.ml";;
needs "x86/proofs/mlkem_native/asm/kem_safe_spec.ml";;
needs "x86/proofs/mlkem_native/asm/gen_matrix_k4_safe_spec.ml";;



(* ------------------------------------------------------------------------- *)
(* The hash check of a decapsulation key sk, with ek at offset 1536 and      *)
(* the hash h of ek at offset 3104: 0 if h = H(ek), else -5                  *)
(* (MLK_ERR_INVALID_SK). The stack is the 320 bytes of the frame and         *)
(* those used by mlkem_hash_h.                                               *)
(* ------------------------------------------------------------------------- *)

let MLKEM1024_CHECK_SK_EXEC = MLKEM_NATIVE2_IMAGE_EXEC ["mlkem1024_check_sk"];;



let MLKEM_NATIVE_CHECK_SK_K4_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!sk (ek:byte list) h pc stackpointer returnaddress.
     LENGTH ek = 1568 /\
     ALL (nonoverlapping (word_sub stackpointer (word 320),320))
         [(word pc,mlkem_native2_image_size); (sk,3168)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read RIP s = word(pc + mlkem1024_check_sk) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [sk] s /\
               read (memory :> bytes(word_add sk (word 1536),1568)) s =
               num_of_bytelist ek /\
               read (memory :> bytes(word_add sk (word 3104),32)) s = h)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s =
               if h = num_of_bytelist(sha3_256 ek) then word 0
               else word 0xfffffffb)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLKEM_NATIVE_CHECK_SK_K4_ASM_IMAGE_SUBROUTINE_CORRECT = assume_spec MLKEM_NATIVE_CHECK_SK_K4_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;



let MLKEM_NATIVE_CHECK_SK_K4_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e sk pc stackpointer returnaddress.
       ALL (nonoverlapping (word_sub stackpointer (word 320),320))
           [(word pc,mlkem_native2_image_size); (sk,3168)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + mlkem1024_check_sk) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [sk] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events sk pc (word_sub stackpointer (word 320))
                                  returnaddress /\
                    memaccess_inbounds e2
                     [sk,3168; word(pc + mlkem_native2_constants),192;
                      word(pc + sha3_keccak_f1600_alt2_rotations),384;
                      word_sub stackpointer (word 320),328]
                     [word_sub stackpointer (word 320),320]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLKEM_NATIVE_CHECK_SK_K4_ASM_IMAGE_SUBROUTINE_SAFE = assume_spec MLKEM_NATIVE_CHECK_SK_K4_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;
