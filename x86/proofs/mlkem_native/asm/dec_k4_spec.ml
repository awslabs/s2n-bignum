(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The function mlkem1024_dec of the build asm: decapsulation, with its      *)
(* correctness and its constant-time and memory safety.                      *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm/api_spec.ml";;
needs "x86/proofs/mlkem_native/asm/kem_spec.ml";;
needs "x86/proofs/mlkem_native/asm/gen_matrix_k4_spec.ml";;
needs "x86/proofs/mlkem_native/asm/kem_safe_spec.ml";;
needs "x86/proofs/mlkem_native/asm/gen_matrix_k4_safe_spec.ml";;
needs "x86/proofs/mlkem_native/asm/pke_decrypt_k4_spec.ml";;
needs "x86/proofs/mlkem_native/asm/pke_encrypt_k4_spec.ml";;



(* ------------------------------------------------------------------------- *)
(* ML-KEM.Decaps_internal (FIPS 203 Algorithm 18), after the hash check      *)
(* of the decapsulation key (FIPS 203 section 7.3): if the check             *)
(* passes, the shared secret at ss and the return value 0, else -5           *)
(* (MLK_ERR_INVALID_SK).                                                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM1024_DEC_EXEC = MLKEM_NATIVE2_IMAGE_EXEC ["mlkem1024_dec"];;



let MLKEM_NATIVE_DEC_K4_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!ss ct sk (dk:byte list) (c:byte list) pc stackpointer returnaddress.
     aligned 32 (word pc:int64) /\ LENGTH dk = 3168 /\ LENGTH c = 1568 /\
     nonoverlapping (ct,1568) (word pc,mlkem_native2_image_size) /\
     nonoverlapping (sk,3168) (word pc,mlkem_native2_image_size) /\
     nonoverlapping (ss,32) (word_sub stackpointer (word 22606),22614) /\
     ALLPAIRS nonoverlapping
      [(ss,32); (word_sub stackpointer (word 22606),22614)]
      [(ct,1568); (sk,3168); (word pc,mlkem_native2_image_size)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read RIP s = word(pc + mlkem1024_dec) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [ss; ct; sk] s /\
               read (memory :> bytes(ct,1568)) s = num_of_bytelist c /\
               read (memory :> bytes(sk,3168)) s = num_of_bytelist dk)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (mlkem_decaps_check mlkem1024 dk c
                ==> read (memory :> bytes(ss,32)) s =
                    num_of_bytelist(mlkem_decaps_internal mlkem1024 dk c)) /\
               C_RETURN s =
               (if mlkem_decaps_check mlkem1024 dk c then word 0
                else word 0xfffffffb))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(ss,32);
                      memory :> bytes(word_sub stackpointer (word 22606),
                                      22606)])`;;

let MLKEM_NATIVE_DEC_K4_ASM_IMAGE_SUBROUTINE_CORRECT = assume_spec MLKEM_NATIVE_DEC_K4_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;



(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of decapsulation: the events          *)
(* depend only on the addresses and on ek and h in dk, which are             *)
(* public, and on whether h = H(ek) (the hash check). As in the proofs       *)
(* of the compiled C, there are no results in the postcondition.             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_DEC_K4_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e ss ct sk (dk:byte list) pc stackpointer returnaddress.
       aligned 32 (word pc:int64) /\ LENGTH dk = 3168 /\
       nonoverlapping (ct,1568) (word pc,mlkem_native2_image_size) /\
       nonoverlapping (sk,3168) (word pc,mlkem_native2_image_size) /\
       nonoverlapping (ss,32) (word_sub stackpointer (word 22606),22614) /\
       ALLPAIRS nonoverlapping
        [(ss,32); (word_sub stackpointer (word 22606),22614)]
        [(ct,1568); (sk,3168); (word pc,mlkem_native2_image_size)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + mlkem1024_dec) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [ss; ct; sk] s /\
                 read (memory :> bytes(sk,3168)) s = num_of_bytelist dk /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events ss ct sk pc
                           (word_sub stackpointer (word 22606)) returnaddress
                           (mlkem_slice 1536 1568 dk)
                           (mlkem_slice 3104 32 dk) /\
                    memaccess_inbounds e2
                     [ct,1568; sk,3168; ss,32;
                      word(pc + mlkem_native2_constants),6048;
                      word(pc + sha3_keccak_f1600_alt2_rotations),384;
                      word_sub stackpointer (word 22606),22614]
                     [ss,32; word_sub stackpointer (word 22606),22606]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(ss,32);
                        memory :> bytes(word_sub stackpointer (word 22606),
                                        22606)])`;;

let MLKEM_NATIVE_DEC_K4_ASM_IMAGE_SUBROUTINE_SAFE = assume_spec MLKEM_NATIVE_DEC_K4_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;
