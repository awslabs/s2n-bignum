(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The function mlkem768_check_pk of the build asm: the modulus check of     *)
(* an encapsulation key, with its correctness and its constant-time and      *)
(* memory safety.                                                            *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm/api_spec.ml";;
needs "x86/proofs/mlkem_native/asm/kem_spec.ml";;
needs "x86/proofs/mlkem_native/asm/gen_matrix_k3_spec.ml";;
needs "x86/proofs/mlkem_native/asm/kem_safe_spec.ml";;
needs "x86/proofs/mlkem_native/asm/gen_matrix_k3_safe_spec.ml";;



(* ------------------------------------------------------------------------- *)
(* The modulus check of an encapsulation key pk: 0 if the 768 12-bit         *)
(* fields of its polynomial vector are all < q, else -4                      *)
(* (MLK_ERR_INVALID_PK).                                                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM768_CHECK_PK_EXEC = MLKEM_NATIVE2_IMAGE_EXEC ["mlkem768_check_pk"];;



let MLKEM_NATIVE_CHECK_PK_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!pk n pc stackpointer returnaddress.
     ALL (nonoverlapping (word_sub stackpointer (word 16),16))
         [(word pc,mlkem_native2_image_size); (pk,1152)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read RIP s = word(pc + mlkem768_check_pk) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [pk] s /\
               read (memory :> bytes(pk,1152)) s = n)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s =
               if !i. i < 768 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
               then word 0 else word 0xfffffffc)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLKEM_NATIVE_CHECK_PK_K3_ASM_IMAGE_SUBROUTINE_CORRECT = assume_spec MLKEM_NATIVE_CHECK_PK_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;



let MLKEM_NATIVE_CHECK_PK_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e pk pc stackpointer returnaddress.
       ALL (nonoverlapping (word_sub stackpointer (word 16),16))
           [(word pc,mlkem_native2_image_size); (pk,1152)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + mlkem768_check_pk) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [pk] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events pk pc (word_sub stackpointer (word 16))
                                  returnaddress /\
                    memaccess_inbounds e2
                     [pk,1152; word_sub stackpointer (word 16),24]
                     [word_sub stackpointer (word 16),16]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLKEM_NATIVE_CHECK_PK_K3_ASM_IMAGE_SUBROUTINE_SAFE = assume_spec MLKEM_NATIVE_CHECK_PK_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;
