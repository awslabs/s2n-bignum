(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The function mlkem768_enc_derand of the build asm: encapsulation, with    *)
(* its correctness and its constant-time and memory safety.                  *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm/api_spec.ml";;
needs "x86/proofs/mlkem_native/asm/kem_spec.ml";;
needs "x86/proofs/mlkem_native/asm/gen_matrix_k3_spec.ml";;
needs "x86/proofs/mlkem_native/asm/kem_safe_spec.ml";;
needs "x86/proofs/mlkem_native/asm/gen_matrix_k3_safe_spec.ml";;
needs "x86/proofs/mlkem_native/asm/pke_encrypt_k3_spec.ml";;



(* ------------------------------------------------------------------------- *)
(* ML-KEM.Encaps_internal (FIPS 203 Algorithm 17), after the modulus         *)
(* check of the encapsulation key (FIPS 203 section 7.2): if the check       *)
(* passes, the shared secret at ss, the ciphertext at ct and the return      *)
(* value 0, else -4 (MLK_ERR_INVALID_PK).                                    *)
(* ------------------------------------------------------------------------- *)

let MLKEM768_ENC_DERAND_EXEC =
  MLKEM_NATIVE2_IMAGE_EXEC ["mlkem768_enc_derand"];;



let MLKEM_NATIVE_ENC_DERAND_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!ct ss pk coins (ek:byte list) (m:byte list) pc stackpointer
    returnaddress.
     aligned 32 (word pc:int64) /\ LENGTH ek = 1184 /\ LENGTH m = 32 /\
     nonoverlapping (pk,1184) (word pc,mlkem_native2_image_size) /\
     PAIRWISE nonoverlapping
      [(ct,1088); (ss,32); (word_sub stackpointer (word 13454),13462)] /\
     ALLPAIRS nonoverlapping
      [(ct,1088); (ss,32); (word_sub stackpointer (word 13454),13462)]
      [(pk,1184); (coins,32); (word pc,mlkem_native2_image_size)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read RIP s = word(pc + mlkem768_enc_derand) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [ct; ss; pk; coins] s /\
               read (memory :> bytes(pk,1184)) s = num_of_bytelist ek /\
               read (memory :> bytes(coins,32)) s = num_of_bytelist m)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (mlkem_ek_check mlkem768 ek
                ==> read (memory :> bytes(ss,32)) s =
                    num_of_bytelist
                     (FST(mlkem_encaps_internal mlkem768 ek m)) /\
                    read (memory :> bytes(ct,1088)) s =
                    num_of_bytelist
                     (SND(mlkem_encaps_internal mlkem768 ek m))) /\
               C_RETURN s =
               (if mlkem_ek_check mlkem768 ek then word 0
                else word 0xfffffffc))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(ct,1088); memory :> bytes(ss,32);
                      memory :> bytes(word_sub stackpointer (word 13454),
                                      13454)])`;;

let MLKEM_NATIVE_ENC_DERAND_K3_ASM_IMAGE_SUBROUTINE_CORRECT = assume_spec MLKEM_NATIVE_ENC_DERAND_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;



(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of encapsulation: the events          *)
(* depend only on the addresses and on ek, which is public, and on           *)
(* whether it passes the modulus check. As in the proofs of the              *)
(* compiled C, the postcondition also gives the return value.                *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_ENC_DERAND_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e ct ss pk coins (ek:byte list) pc stackpointer returnaddress.
       aligned 32 (word pc:int64) /\ LENGTH ek = 1184 /\
       nonoverlapping (pk,1184) (word pc,mlkem_native2_image_size) /\
       PAIRWISE nonoverlapping
        [(ct,1088); (ss,32); (word_sub stackpointer (word 13454),13462)] /\
       ALLPAIRS nonoverlapping
        [(ct,1088); (ss,32); (word_sub stackpointer (word 13454),13462)]
        [(pk,1184); (coins,32); (word pc,mlkem_native2_image_size)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + mlkem768_enc_derand) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [ct; ss; pk; coins] s /\
                 read (memory :> bytes(pk,1184)) s = num_of_bytelist ek /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 C_RETURN s =
                 (if mlkem_ek_check mlkem768 ek then word 0
                  else word 0xfffffffc) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events ct ss pk coins pc
                           (word_sub stackpointer (word 13454))
                           returnaddress ek /\
                    memaccess_inbounds e2
                     [pk,1184; coins,32; ct,1088; ss,32;
                      word(pc + mlkem_native2_constants),6048;
                      word(pc + sha3_keccak_f1600_alt2_rotations),384;
                      word_sub stackpointer (word 13454),13462]
                     [ct,1088; ss,32;
                      word_sub stackpointer (word 13454),13454]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(ct,1088); memory :> bytes(ss,32);
                        memory :> bytes(word_sub stackpointer (word 13454),
                                        13454)])`;;

let MLKEM_NATIVE_ENC_DERAND_K3_ASM_IMAGE_SUBROUTINE_SAFE = assume_spec MLKEM_NATIVE_ENC_DERAND_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;
