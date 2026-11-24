(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of the function mlkem768_keypair_derand of ML-KEM-768     *)
(* (arm/mlkem_native/asm/mlkem768.S) in the image of the ML-KEM API in     *)
(* assembly: key generation, its correctness and its constant-time and     *)
(* memory safety, stated as in the proofs of the compiled C of mlkem-      *)
(* native (see arm/mlkem_native/asm/README.md). The proofs are in          *)
(* keypair_derand_k3_proof.ml.                                             *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/asm/layout.ml";;
needs "arm/proofs/mlkem_native/asm/hash_g_spec.ml";;
needs "arm/proofs/mlkem_native/asm/hash_h_spec.ml";;
needs "arm/proofs/mlkem_native/asm/getnoise_spec.ml";;
needs "arm/proofs/mlkem_native/asm/gen_matrix_k3_spec.ml";;
needs "arm/proofs/mlkem_native/asm/gen_matrix_k3_safe_spec.ml";;
needs "arm/proofs/mlkem_native/asm/ntt_alt_spec.ml";;
needs "arm/proofs/mlkem_native/asm/intt_alt_spec.ml";;
needs "arm/proofs/mlkem_native/asm/mulcache_compute_spec.ml";;
needs "arm/proofs/mlkem_native/asm/tomont_spec.ml";;
needs "arm/proofs/mlkem_native/asm/reduce_spec.ml";;
needs "arm/proofs/mlkem_native/asm/add_reduce_spec.ml";;
needs "arm/proofs/mlkem_native/asm/sub_reduce_spec.ml";;
needs "arm/proofs/mlkem_native/asm/tobytes_alt_spec.ml";;
needs "arm/proofs/mlkem_native/asm/frombytes_spec.ml";;
needs "arm/proofs/mlkem_native/asm/frommsg_spec.ml";;
needs "arm/proofs/mlkem_native/asm/tomsg_spec.ml";;
needs "arm/proofs/mlkem_native/asm/basemul_k3_alt_spec.ml";;
needs "arm/proofs/mlkem_native/asm/compress_d10_spec.ml";;
needs "arm/proofs/mlkem_native/asm/compress_d4_spec.ml";;
needs "arm/proofs/mlkem_native/asm/decompress_d10_spec.ml";;
needs "arm/proofs/mlkem_native/asm/decompress_d4_spec.ml";;
needs "common/fips203/fips203.ml";;
needs "arm/proofs/utils/mlkem_native2_cbd.ml";;
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(* ------------------------------------------------------------------------- *)
(* ML-KEM.KeyGen_internal (FIPS 203 Algorithm 16) with coins = d || z: the   *)
(* encapsulation key at pk, the decapsulation key at sk and the return value *)
(* 0.                                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KEYPAIR_DERAND_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!pk sk coins (d:byte list) (z:byte list) pc stackpointer returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + mlkem_native2_image_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH d = 32 /\ LENGTH z = 32 /\
     PAIRWISE nonoverlapping
      [(pk,1184); (sk,2400); (word_sub stackpointer (word 13552),13552)] /\
     ALLPAIRS nonoverlapping
      [(pk,1184); (sk,2400); (word_sub stackpointer (word 13552),13552)]
      [(coins,64); (word pc,mlkem_native2_image_size)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem768_keypair_derand) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [pk; sk; coins] s /\
               read (memory :> bytes(coins,32)) s = num_of_bytelist d /\
               read (memory :> bytes(word_add coins (word 32),32)) s =
               num_of_bytelist z)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(pk,1184)) s =
               num_of_bytelist(FST(mlkem_keygen_internal mlkem768 d z)) /\
               read (memory :> bytes(sk,2400)) s =
               num_of_bytelist(SND(mlkem_keygen_internal mlkem768 d z)) /\
               C_RETURN s = word 0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(pk,1184); memory :> bytes(sk,2400);
                      memory :> bytes(word_sub stackpointer (word 13552),
                                      13552)])`;;

let MLKEM_NATIVE_KEYPAIR_DERAND_K3_ASM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_KEYPAIR_DERAND_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of key generation: the events depend  *)
(* only on the addresses and on rho, which is public although computed from  *)
(* d (rho is at the end of pk). As in the proofs of the compiled C, the      *)
(* postcondition also gives rho in pk and the return value.                  *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KEYPAIR_DERAND_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e pk sk coins (d:byte list) pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\
       pc + mlkem_native2_image_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ LENGTH d = 32 /\
       PAIRWISE nonoverlapping
        [(pk,1184); (sk,2400); (word_sub stackpointer (word 13552),13552)] /\
       ALLPAIRS nonoverlapping
        [(pk,1184); (sk,2400); (word_sub stackpointer (word 13552),13552)]
        [(coins,64); (word pc,mlkem_native2_image_size)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem768_keypair_derand) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [pk; sk; coins] s /\
                 read (memory :> bytes(coins,32)) s = num_of_bytelist d /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 C_RETURN s = word 0 /\
                 read (memory :> bytes(word_add pk (word 1152),32)) s =
                 num_of_bytelist(FST(mlkem_g(APPEND d [word 3]))) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events pk sk coins pc
                           (word_sub stackpointer (word 13552)) returnaddress
                           (FST(mlkem_g(APPEND d [word 3]))) /\
                    memaccess_inbounds e2
                     [coins,64; pk,1184; sk,2400;
                      word(pc + mlkem_native2_constants),6656;
                      word_sub stackpointer (word 13552),13552]
                     [pk,1184; sk,2400;
                      word_sub stackpointer (word 13552),13552]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(pk,1184); memory :> bytes(sk,2400);
                        memory :> bytes(word_sub stackpointer (word 13552),
                                        13552)])`;;

let MLKEM_NATIVE_KEYPAIR_DERAND_K3_ASM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_KEYPAIR_DERAND_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;
