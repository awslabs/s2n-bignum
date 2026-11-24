(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The function mlkem768_pke_encrypt of the build asm: K-PKE.Encrypt, with   *)
(* its correctness and its constant-time and memory safety.                  *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm/api_spec.ml";;
needs "x86/proofs/mlkem_native/asm/kem_spec.ml";;
needs "x86/proofs/mlkem_native/asm/gen_matrix_k3_spec.ml";;
needs "x86/proofs/mlkem_native/asm/kem_safe_spec.ml";;
needs "x86/proofs/mlkem_native/asm/gen_matrix_k3_safe_spec.ml";;



(* ------------------------------------------------------------------------- *)
(* K-PKE.Encrypt (FIPS 203 Algorithm 14) as the internal function            *)
(* mlkem768_pke_encrypt(ct, at, pk, m, noise): the ciphertext of the         *)
(* message m under the encryption key ek at pk with randomness r, given      *)
(* the transposed matrix at (row i, column j sampled from rho || i || j,     *)
(* in the order of the coefficients of the x86 NTT domain) and the noise     *)
(* y, e1, e2 sampled from r as 16-bit coefficients at noise, which are       *)
(* overwritten. The buffers at and noise are 32-byte aligned.                *)
(* ------------------------------------------------------------------------- *)

let MLKEM768_PKE_ENCRYPT_EXEC =
  MLKEM_NATIVE2_IMAGE_EXEC ["mlkem768_pke_encrypt"];;



let MLKEM_NATIVE_PKE_ENCRYPT_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!ct at pk mp noise (ek:byte list) (m:byte list) (r:byte list)
    pc stackpointer returnaddress.
     aligned 32 (word pc:int64) /\ aligned 32 at /\ aligned 32 noise /\
     LENGTH ek = 1184 /\ LENGTH m = 32 /\
     nonoverlapping (pk,1184) (word pc,mlkem_native2_image_size) /\
     PAIRWISE nonoverlapping
      [(ct,1088); (noise,3584); (word_sub stackpointer (word 4951),4959)] /\
     ALLPAIRS nonoverlapping
      [(ct,1088); (noise,3584); (word_sub stackpointer (word 4951),4959)]
      [(word pc,mlkem_native2_image_size); (at,4608); (pk,1184); (mp,32)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read RIP s = word(pc + mlkem768_pke_encrypt) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [ct; at; pk; mp; noise] s /\
               (!i j t. i < 3 /\ j < 3 /\ t < 256
                        ==> read(memory :> bytes16(word_add at
                                 (word(512 * (3 * i + j) + 2 * t)))) s =
                            iword(mlkem_sample_ntt
                                   (APPEND (mlkem_slice 1152 32 ek)
                                           [word i; word j])
                                   (avx_unorder t))) /\
               read (memory :> bytes(pk,1184)) s = num_of_bytelist ek /\
               read (memory :> bytes(mp,32)) s = num_of_bytelist m /\
               (!i t. i < 7 /\ t < 256
                      ==> read(memory :> bytes16(word_add noise
                                 (word(512 * i + 2 * t)))) s =
                          iword(mlkem_cbd_coeff 2
                                 (mlkem_prf 2 r (word i)) t)))
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               read (memory :> bytes(ct,1088)) s =
               num_of_bytelist(kpke_encrypt mlkem768 ek m r))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(ct,1088); memory :> bytes(noise,3584);
                      memory :> bytes(word_sub stackpointer (word 4951),
                                      4951)])`;;

let MLKEM_NATIVE_PKE_ENCRYPT_K3_ASM_IMAGE_SUBROUTINE_CORRECT = assume_spec MLKEM_NATIVE_PKE_ENCRYPT_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;



(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of the K-PKE encryption: the          *)
(* events depend only on the addresses.                                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_PKE_ENCRYPT_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e ct at pk mp noise pc stackpointer returnaddress.
       aligned 32 (word pc:int64) /\ aligned 32 at /\ aligned 32 noise /\
       nonoverlapping (pk,1184) (word pc,mlkem_native2_image_size) /\
       PAIRWISE nonoverlapping
        [(ct,1088); (noise,3584); (word_sub stackpointer (word 4951),4959)] /\
       ALLPAIRS nonoverlapping
        [(ct,1088); (noise,3584); (word_sub stackpointer (word 4951),4959)]
        [(word pc,mlkem_native2_image_size); (at,4608); (pk,1184); (mp,32)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + mlkem768_pke_encrypt) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [ct; at; pk; mp; noise] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events ct at pk mp noise pc
                           (word_sub stackpointer (word 4951)) returnaddress /\
                    memaccess_inbounds e2
                     [ct,1088; at,4608; pk,1184; mp,32; noise,3584;
                      word(pc + mlkem_native2_constants),6048;
                      word_sub stackpointer (word 4951),4959]
                     [ct,1088; noise,3584;
                      word_sub stackpointer (word 4951),4951]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(ct,1088); memory :> bytes(noise,3584);
                        memory :> bytes(word_sub stackpointer (word 4951),
                                        4951)])`;;

let MLKEM_NATIVE_PKE_ENCRYPT_K3_ASM_IMAGE_SUBROUTINE_SAFE = assume_spec MLKEM_NATIVE_PKE_ENCRYPT_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;
