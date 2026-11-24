(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of the function mlkem768_pke_decrypt of ML-KEM-768        *)
(* (arm/mlkem_native/asm/mlkem768.S) in the image of the ML-KEM API in     *)
(* assembly: K-PKE.Decrypt, the internal function, its correctness and     *)
(* its constant-time and memory safety, stated as in the proofs of the     *)
(* compiled C of mlkem-native (see arm/mlkem_native/asm/README.md). The    *)
(* proofs are in pke_decrypt_k3_proof.ml.                                  *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/asm/layout.ml";;
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
(* K-PKE.Decrypt (FIPS 203 Algorithm 15) as the internal function            *)
(* mlkem768_pke_decrypt(m, ct, sk): the message of the ciphertext c at ct    *)
(* under the decryption key dk in the first 1152 bytes at sk.                *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_PKE_DECRYPT_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mp ct sk (c:byte list) (dk:byte list) pc stackpointer returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + mlkem_native2_image_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH c = 1088 /\ LENGTH dk = 1152 /\
     PAIRWISE nonoverlapping
      [(mp,32); (word_sub stackpointer (word 5024),5024)] /\
     ALLPAIRS nonoverlapping
      [(mp,32); (word_sub stackpointer (word 5024),5024)]
      [(word pc,mlkem_native2_image_size); (ct,1088); (sk,1152)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem768_pke_decrypt) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [mp; ct; sk] s /\
               read (memory :> bytes(ct,1088)) s = num_of_bytelist c /\
               read (memory :> bytes(sk,1152)) s = num_of_bytelist dk)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(mp,32)) s =
               num_of_bytelist(kpke_decrypt mlkem768 dk c))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(mp,32);
                      memory :> bytes(word_sub stackpointer (word 5024),
                                      5024)])`;;

let MLKEM_NATIVE_PKE_DECRYPT_K3_ASM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_PKE_DECRYPT_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of the K-PKE decryption: the events   *)
(* depend only on the addresses.                                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_PKE_DECRYPT_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e mp ct sk pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\
       pc + mlkem_native2_image_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [(mp,32); (word_sub stackpointer (word 5024),5024)] /\
       ALLPAIRS nonoverlapping
        [(mp,32); (word_sub stackpointer (word 5024),5024)]
        [(word pc,mlkem_native2_image_size); (ct,1088); (sk,1152)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem768_pke_decrypt) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [mp; ct; sk] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events mp ct sk pc
                           (word_sub stackpointer (word 5024)) returnaddress /\
                    memaccess_inbounds e2
                     [mp,32; ct,1088; sk,1152;
                      word(pc + mlkem_native2_constants),6656;
                      word_sub stackpointer (word 5024),5024]
                     [mp,32; word_sub stackpointer (word 5024),5024]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(mp,32);
                        memory :> bytes(word_sub stackpointer (word 5024),
                                        5024)])`;;

let MLKEM_NATIVE_PKE_DECRYPT_K3_ASM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_PKE_DECRYPT_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;
