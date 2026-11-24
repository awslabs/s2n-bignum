(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The function mlkem1024_pke_decrypt of the build asm: K-PKE.Decrypt,       *)
(* with its correctness and its constant-time and memory safety.             *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm/api_spec.ml";;
needs "x86/proofs/mlkem_native/asm/kem_spec.ml";;
needs "x86/proofs/mlkem_native/asm/gen_matrix_k4_spec.ml";;
needs "x86/proofs/mlkem_native/asm/kem_safe_spec.ml";;
needs "x86/proofs/mlkem_native/asm/gen_matrix_k4_safe_spec.ml";;



(* ------------------------------------------------------------------------- *)
(* K-PKE.Decrypt (FIPS 203 Algorithm 15) as the internal function            *)
(* mlkem1024_pke_decrypt(m, ct, sk): the message of the ciphertext c at ct   *)
(* under the decryption key dk at sk.                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM1024_PKE_DECRYPT_EXEC =
  MLKEM_NATIVE2_IMAGE_EXEC ["mlkem1024_pke_decrypt"];;



let MLKEM_NATIVE_PKE_DECRYPT_K4_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mp ct sk (c:byte list) (dk:byte list) pc stackpointer returnaddress.
     aligned 32 (word pc:int64) /\ LENGTH c = 1568 /\ LENGTH dk = 1536 /\
     nonoverlapping (sk,1536) (word pc,mlkem_native2_image_size) /\
     PAIRWISE nonoverlapping
      [(mp,32); (word_sub stackpointer (word 6231),6239)] /\
     ALLPAIRS nonoverlapping
      [(mp,32); (word_sub stackpointer (word 6231),6239)]
      [(word pc,mlkem_native2_image_size); (ct,1568); (sk,1536)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read RIP s = word(pc + mlkem1024_pke_decrypt) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [mp; ct; sk] s /\
               read (memory :> bytes(ct,1568)) s = num_of_bytelist c /\
               read (memory :> bytes(sk,1536)) s = num_of_bytelist dk)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               read (memory :> bytes(mp,32)) s =
               num_of_bytelist(kpke_decrypt mlkem1024 dk c))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(mp,32);
                      memory :> bytes(word_sub stackpointer (word 6231),
                                      6231)])`;;

let MLKEM_NATIVE_PKE_DECRYPT_K4_ASM_IMAGE_SUBROUTINE_CORRECT = assume_spec MLKEM_NATIVE_PKE_DECRYPT_K4_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;



(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of the K-PKE decryption: the          *)
(* events depend only on the addresses.                                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_PKE_DECRYPT_K4_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e mp ct sk pc stackpointer returnaddress.
       aligned 32 (word pc:int64) /\
       nonoverlapping (sk,1536) (word pc,mlkem_native2_image_size) /\
       PAIRWISE nonoverlapping
        [(mp,32); (word_sub stackpointer (word 6231),6239)] /\
       ALLPAIRS nonoverlapping
        [(mp,32); (word_sub stackpointer (word 6231),6239)]
        [(word pc,mlkem_native2_image_size); (ct,1568); (sk,1536)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + mlkem1024_pke_decrypt) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [mp; ct; sk] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events mp ct sk pc
                           (word_sub stackpointer (word 6231)) returnaddress /\
                    memaccess_inbounds e2
                     [mp,32; ct,1568; sk,1536;
                      word(pc + mlkem_native2_constants),6048;
                      word_sub stackpointer (word 6231),6239]
                     [mp,32; word_sub stackpointer (word 6231),6231]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(mp,32);
                        memory :> bytes(word_sub stackpointer (word 6231),
                                        6231)])`;;

let MLKEM_NATIVE_PKE_DECRYPT_K4_ASM_IMAGE_SUBROUTINE_SAFE = assume_spec MLKEM_NATIVE_PKE_DECRYPT_K4_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;
