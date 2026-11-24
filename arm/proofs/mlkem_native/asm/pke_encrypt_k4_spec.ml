(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of the function mlkem1024_pke_encrypt of ML-KEM-1024      *)
(* (arm/mlkem_native/asm/mlkem1024.S) in the image of the ML-KEM API in    *)
(* assembly: K-PKE.Encrypt, the internal function, its correctness and     *)
(* its constant-time and memory safety, stated as in the proofs of the     *)
(* compiled C of mlkem-native (see arm/mlkem_native/asm/README.md). The    *)
(* proofs are in pke_encrypt_k4_proof.ml.                                  *)
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
needs "arm/proofs/mlkem_native/asm/basemul_k4_alt_spec.ml";;
needs "arm/proofs/mlkem_native/asm/compress_d11_spec.ml";;
needs "arm/proofs/mlkem_native/asm/compress_d5_spec.ml";;
needs "arm/proofs/mlkem_native/asm/decompress_d11_spec.ml";;
needs "arm/proofs/mlkem_native/asm/decompress_d5_spec.ml";;
needs "common/fips203/fips203.ml";;
needs "arm/proofs/utils/mlkem_native2_cbd.ml";;
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(* ------------------------------------------------------------------------- *)
(* K-PKE.Encrypt (FIPS 203 Algorithm 14) as the internal function            *)
(* mlkem1024_pke_encrypt(ct, at, pk, m, noise): the ciphertext of the        *)
(* message m under the encryption key ek at pk with randomness r, given the  *)
(* transposed matrix at (row i, column j sampled from rho || i || j) and the *)
(* noise y, e1, e2 sampled from r as 16-bit coefficients at noise, which are *)
(* overwritten.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_PKE_ENCRYPT_K4_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!ct at pk mp noise (ek:byte list) (m:byte list) (r:byte list)
    pc stackpointer returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + mlkem_native2_image_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH ek = 1568 /\ LENGTH m = 32 /\
     PAIRWISE nonoverlapping
      [(ct,1568); (noise,4608); (word_sub stackpointer (word 6304),6304)] /\
     ALLPAIRS nonoverlapping
      [(ct,1568); (noise,4608); (word_sub stackpointer (word 6304),6304)]
      [(word pc,mlkem_native2_image_size); (at,8192); (pk,1568); (mp,32)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem1024_pke_encrypt) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [ct; at; pk; mp; noise] s /\
               (!i j t. i < 4 /\ j < 4 /\ t < 256
                        ==> read(memory :> bytes16(word_add at
                                 (word(512 * (4 * i + j) + 2 * t)))) s =
                            iword(mlkem_sample_ntt
                                   (APPEND (mlkem_slice 1536 32 ek)
                                           [word i; word j]) t)) /\
               read (memory :> bytes(pk,1568)) s = num_of_bytelist ek /\
               read (memory :> bytes(mp,32)) s = num_of_bytelist m /\
               (!i t. i < 9 /\ t < 256
                      ==> read(memory :> bytes16(word_add noise
                                 (word(512 * i + 2 * t)))) s =
                          iword(mlkem_cbd_coeff 2
                                (mlkem_prf 2 r (word i))
                                t)))
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(ct,1568)) s =
               num_of_bytelist(kpke_encrypt mlkem1024 ek m r))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(ct,1568); memory :> bytes(noise,4608);
                      memory :> bytes(word_sub stackpointer (word 6304),
                                      6304)])`;;

let MLKEM_NATIVE_PKE_ENCRYPT_K4_ASM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_PKE_ENCRYPT_K4_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of the K-PKE encryption: the events   *)
(* depend only on the addresses.                                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_PKE_ENCRYPT_K4_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e ct at pk mp noise pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\
       pc + mlkem_native2_image_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [(ct,1568); (noise,4608); (word_sub stackpointer (word 6304),6304)] /\
       ALLPAIRS nonoverlapping
        [(ct,1568); (noise,4608); (word_sub stackpointer (word 6304),6304)]
        [(word pc,mlkem_native2_image_size); (at,8192); (pk,1568); (mp,32)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem1024_pke_encrypt) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [ct; at; pk; mp; noise] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events ct at pk mp noise pc
                           (word_sub stackpointer (word 6304)) returnaddress /\
                    memaccess_inbounds e2
                     [ct,1568; at,8192; pk,1568; mp,32; noise,4608;
                      word(pc + mlkem_native2_constants),6656;
                      word_sub stackpointer (word 6304),6304]
                     [ct,1568; noise,4608;
                      word_sub stackpointer (word 6304),6304]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(ct,1568); memory :> bytes(noise,4608);
                        memory :> bytes(word_sub stackpointer (word 6304),
                                        6304)])`;;

let MLKEM_NATIVE_PKE_ENCRYPT_K4_ASM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_PKE_ENCRYPT_K4_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;
