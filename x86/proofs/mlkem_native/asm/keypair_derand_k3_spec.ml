(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The function mlkem768_keypair_derand of the build asm: key generation,    *)
(* with its correctness and its constant-time and memory safety.             *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm/api_spec.ml";;
needs "x86/proofs/mlkem_native/asm/kem_spec.ml";;
needs "x86/proofs/mlkem_native/asm/gen_matrix_k3_spec.ml";;
needs "x86/proofs/mlkem_native/asm/kem_safe_spec.ml";;
needs "x86/proofs/mlkem_native/asm/gen_matrix_k3_safe_spec.ml";;



(* ------------------------------------------------------------------------- *)
(* ML-KEM.KeyGen_internal (FIPS 203 Algorithm 16) from d and z at            *)
(* coins, the keys at pk and sk; the return value is 0.                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM768_KEYPAIR_DERAND_EXEC =
  MLKEM_NATIVE2_IMAGE_EXEC ["mlkem768_keypair_derand"];;



let MLKEM_NATIVE_KEYPAIR_DERAND_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!pk sk coins (d:byte list) (z:byte list) pc stackpointer returnaddress.
     aligned 32 (word pc:int64) /\ LENGTH d = 32 /\ LENGTH z = 32 /\
     PAIRWISE nonoverlapping
      [(pk,1184); (sk,2400); (word_sub stackpointer (word 14214),14222)] /\
     ALLPAIRS nonoverlapping
      [(pk,1184); (sk,2400); (word_sub stackpointer (word 14214),14222)]
      [(coins,64); (word pc,mlkem_native2_image_size)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read RIP s = word(pc + mlkem768_keypair_derand) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [pk; sk; coins] s /\
               read (memory :> bytes(coins,32)) s = num_of_bytelist d /\
               read (memory :> bytes(word_add coins (word 32),32)) s =
               num_of_bytelist z)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               read (memory :> bytes(pk,1184)) s =
               num_of_bytelist(FST(mlkem_keygen_internal mlkem768 d z)) /\
               read (memory :> bytes(sk,2400)) s =
               num_of_bytelist(SND(mlkem_keygen_internal mlkem768 d z)) /\
               C_RETURN s = word 0)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(pk,1184); memory :> bytes(sk,2400);
                      memory :> bytes(word_sub stackpointer (word 14214),
                                      14214)])`;;

let MLKEM_NATIVE_KEYPAIR_DERAND_K3_ASM_IMAGE_SUBROUTINE_CORRECT = assume_spec MLKEM_NATIVE_KEYPAIR_DERAND_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;



(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of key generation: the events         *)
(* depend only on the addresses and on rho, which is public although         *)
(* computed from d (rho is at the end of pk). As in the proofs of the        *)
(* compiled C, the postcondition also gives rho in pk and the return         *)
(* value.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KEYPAIR_DERAND_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e pk sk coins (d:byte list) pc stackpointer returnaddress.
       aligned 32 (word pc:int64) /\ LENGTH d = 32 /\
       PAIRWISE nonoverlapping
        [(pk,1184); (sk,2400); (word_sub stackpointer (word 14214),14222)] /\
       ALLPAIRS nonoverlapping
        [(pk,1184); (sk,2400); (word_sub stackpointer (word 14214),14222)]
        [(coins,64); (word pc,mlkem_native2_image_size)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + mlkem768_keypair_derand) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [pk; sk; coins] s /\
                 read (memory :> bytes(coins,32)) s = num_of_bytelist d /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 C_RETURN s = word 0 /\
                 read (memory :> bytes(word_add pk (word 1152),32)) s =
                 num_of_bytelist(FST(mlkem_g(APPEND d [word 3]))) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events pk sk coins pc
                           (word_sub stackpointer (word 14214)) returnaddress
                           (FST(mlkem_g(APPEND d [word 3]))) /\
                    memaccess_inbounds e2
                     [coins,64; pk,1184; sk,2400;
                      word(pc + mlkem_native2_constants),6048;
                      word(pc + sha3_keccak_f1600_alt2_rotations),384;
                      word_sub stackpointer (word 14214),14222]
                     [pk,1184; sk,2400;
                      word_sub stackpointer (word 14214),14214]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(pk,1184); memory :> bytes(sk,2400);
                        memory :> bytes(word_sub stackpointer (word 14214),
                                        14214)])`;;

let MLKEM_NATIVE_KEYPAIR_DERAND_K3_ASM_IMAGE_SUBROUTINE_SAFE = assume_spec MLKEM_NATIVE_KEYPAIR_DERAND_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;
