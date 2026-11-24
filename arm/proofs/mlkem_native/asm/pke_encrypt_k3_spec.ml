(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of the function mlkem768_pke_encrypt of ML-KEM-768        *)
(* (arm/mlkem_native/asm/mlkem768.S) in the image of the ML-KEM API in     *)
(* assembly: K-PKE.Encrypt, the internal function, its correctness and     *)
(* its constant-time and memory safety, stated as in the proofs of the     *)
(* compiled C of mlkem-native (see arm/mlkem_native/asm/README.md). The    *)
(* proofs are in pke_encrypt_k3_proof.ml.                                  *)
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
(* K-PKE.Encrypt (FIPS 203 Algorithm 14) as the internal function            *)
(* mlkem768_pke_encrypt(ct, at, pk, m, noise): the ciphertext of the message *)
(* m under the encryption key ek at pk with randomness r, given the          *)
(* transposed matrix at (row i, column j sampled from rho || i || j) and the *)
(* noise y, e1, e2 sampled from r as 16-bit coefficients at noise, which are *)
(* overwritten.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_PKE_ENCRYPT_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!ct at pk mp noise (ek:byte list) (m:byte list) (r:byte list)
    pc stackpointer returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + mlkem_native2_image_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH ek = 1184 /\ LENGTH m = 32 /\
     PAIRWISE nonoverlapping
      [(ct,1088); (noise,3584); (word_sub stackpointer (word 5024),5024)] /\
     ALLPAIRS nonoverlapping
      [(ct,1088); (noise,3584); (word_sub stackpointer (word 5024),5024)]
      [(word pc,mlkem_native2_image_size); (at,4608); (pk,1184); (mp,32)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem768_pke_encrypt) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [ct; at; pk; mp; noise] s /\
               (!i j t. i < 3 /\ j < 3 /\ t < 256
                        ==> read(memory :> bytes16(word_add at
                                 (word(512 * (3 * i + j) + 2 * t)))) s =
                            iword(mlkem_sample_ntt
                                   (APPEND (mlkem_slice 1152 32 ek)
                                           [word i; word j]) t)) /\
               read (memory :> bytes(pk,1184)) s = num_of_bytelist ek /\
               read (memory :> bytes(mp,32)) s = num_of_bytelist m /\
               (!i t. i < 7 /\ t < 256
                      ==> read(memory :> bytes16(word_add noise
                                 (word(512 * i + 2 * t)))) s =
                          iword(mlkem_cbd_coeff 2
                                (mlkem_prf 2 r (word i))
                                t)))
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(ct,1088)) s =
               num_of_bytelist(kpke_encrypt mlkem768 ek m r))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(ct,1088); memory :> bytes(noise,3584);
                      memory :> bytes(word_sub stackpointer (word 5024),
                                      5024)])`;;

let MLKEM_NATIVE_PKE_ENCRYPT_K3_ASM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_PKE_ENCRYPT_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of the K-PKE encryption: the events   *)
(* depend only on the addresses.                                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_PKE_ENCRYPT_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e ct at pk mp noise pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\
       pc + mlkem_native2_image_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [(ct,1088); (noise,3584); (word_sub stackpointer (word 5024),5024)] /\
       ALLPAIRS nonoverlapping
        [(ct,1088); (noise,3584); (word_sub stackpointer (word 5024),5024)]
        [(word pc,mlkem_native2_image_size); (at,4608); (pk,1184); (mp,32)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem768_pke_encrypt) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [ct; at; pk; mp; noise] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events ct at pk mp noise pc
                           (word_sub stackpointer (word 5024)) returnaddress /\
                    memaccess_inbounds e2
                     [ct,1088; at,4608; pk,1184; mp,32; noise,3584;
                      word(pc + mlkem_native2_constants),6656;
                      word_sub stackpointer (word 5024),5024]
                     [ct,1088; noise,3584;
                      word_sub stackpointer (word 5024),5024]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(ct,1088); memory :> bytes(noise,3584);
                        memory :> bytes(word_sub stackpointer (word 5024),
                                        5024)])`;;

let MLKEM_NATIVE_PKE_ENCRYPT_K3_ASM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_PKE_ENCRYPT_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;
