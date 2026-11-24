(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The function mlkem1024_pke_encrypt_avx512 of the build asm_avx512:        *)
(* K-PKE.Encrypt, with its correctness and its constant-time and memory      *)
(* safety.                                                                   *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/api_spec.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/kem_spec.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/gen_matrix_k4_spec.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/kem_safe_spec.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/gen_matrix_k4_safe_spec.ml";;



(* ------------------------------------------------------------------------- *)
(* K-PKE.Encrypt (FIPS 203 Algorithm 14) as the internal function            *)
(* mlkem1024_pke_encrypt_avx512(ct, at, pk, m, noise): the ciphertext of the *)
(* message m under the encryption key ek at pk with randomness r, given the  *)
(* transposed matrix at (row i, column j sampled from rho || i || j, in the  *)
(* order of the coefficients of the x86 NTT domain) and the noise y, e1, e2  *)
(* sampled from r as 16-bit coefficients at noise, which are overwritten.    *)
(* The buffers at and noise are 32-byte aligned.                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM1024_PKE_ENCRYPT_AVX512_EXEC =
  MLKEM_NATIVE2_AVX512_IMAGE_EXEC ["mlkem1024_pke_encrypt_avx512"];;



let MLKEM_NATIVE_PKE_ENCRYPT_K4_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!ct at pk mp noise (ek:byte list) (m:byte list) (r:byte list)
    pc stackpointer returnaddress.
     aligned 32 (word pc:int64) /\ aligned 32 at /\ aligned 32 noise /\
     LENGTH ek = 1568 /\ LENGTH m = 32 /\
     nonoverlapping (pk,1568) (word pc,mlkem_native2_avx512_image_size) /\
     PAIRWISE nonoverlapping
      [(ct,1568); (noise,4608); (word_sub stackpointer (word 6231),6239)] /\
     ALLPAIRS nonoverlapping
      [(ct,1568); (noise,4608); (word_sub stackpointer (word 6231),6239)]
      [(word pc,mlkem_native2_avx512_image_size); (at,8192); (pk,1568);
       (mp,32)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
               read RIP s = word(pc + mlkem1024_pke_encrypt_avx512) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [ct; at; pk; mp; noise] s /\
               (!i j t. i < 4 /\ j < 4 /\ t < 256
                        ==> read(memory :> bytes16(word_add at
                                 (word(512 * (4 * i + j) + 2 * t)))) s =
                            iword(mlkem_sample_ntt
                                   (APPEND (mlkem_slice 1536 32 ek)
                                           [word i; word j])
                                   (avx_unorder t))) /\
               read (memory :> bytes(pk,1568)) s = num_of_bytelist ek /\
               read (memory :> bytes(mp,32)) s = num_of_bytelist m /\
               (!i t. i < 9 /\ t < 256
                      ==> read(memory :> bytes16(word_add noise
                                 (word(512 * i + 2 * t)))) s =
                          iword(mlkem_cbd_coeff 2
                                 (mlkem_prf 2 r (word i)) t)))
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               read (memory :> bytes(ct,1568)) s =
               num_of_bytelist(kpke_encrypt mlkem1024 ek m r))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(ct,1568); memory :> bytes(noise,4608);
                      memory :> bytes(word_sub stackpointer (word 6231),
                                      6231)])`;;

let MLKEM_NATIVE_PKE_ENCRYPT_K4_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT = assume_spec MLKEM_NATIVE_PKE_ENCRYPT_K4_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT_STMT;;



(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of the K-PKE encryption: the          *)
(* events depend only on the addresses.                                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_PKE_ENCRYPT_K4_ASM_AVX512_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e ct at pk mp noise pc stackpointer returnaddress.
       aligned 32 (word pc:int64) /\ aligned 32 at /\ aligned 32 noise /\
       nonoverlapping (pk,1568) (word pc,mlkem_native2_avx512_image_size) /\
       PAIRWISE nonoverlapping
        [(ct,1568); (noise,4608); (word_sub stackpointer (word 6231),6239)] /\
       ALLPAIRS nonoverlapping
        [(ct,1568); (noise,4608); (word_sub stackpointer (word 6231),6239)]
        [(word pc,mlkem_native2_avx512_image_size); (at,8192); (pk,1568);
         (mp,32)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
                 read RIP s = word(pc + mlkem1024_pke_encrypt_avx512) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [ct; at; pk; mp; noise] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events ct at pk mp noise pc
                           (word_sub stackpointer (word 6231)) returnaddress /\
                    memaccess_inbounds e2
                     [ct,1568; at,8192; pk,1568; mp,32; noise,4608;
                      word(pc + mlkem_native2_constants),6048;
                      word_sub stackpointer (word 6231),6239]
                     [ct,1568; noise,4608;
                      word_sub stackpointer (word 6231),6231]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(ct,1568); memory :> bytes(noise,4608);
                        memory :> bytes(word_sub stackpointer (word 6231),
                                        6231)])`;;

let MLKEM_NATIVE_PKE_ENCRYPT_K4_ASM_AVX512_IMAGE_SUBROUTINE_SAFE = assume_spec MLKEM_NATIVE_PKE_ENCRYPT_K4_ASM_AVX512_IMAGE_SUBROUTINE_SAFE_STMT;;
