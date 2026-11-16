(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The API of ML-KEM-1024 in the AVX-512 version of the x86 mlkem_native2    *)
(* (x86/mlkem_native2_avx512/mlkem1024_avx512.S), in the image: the key      *)
(* checks of FIPS 203 (section 7), the internal functions for K-PKE          *)
(* encryption and decryption, and key generation, encapsulation and          *)
(* decapsulation, with the results, and their constant-time and memory       *)
(* safety, stated as in the proofs of the compiled C of mlkem-native. A copy *)
(* of x86/proofs/mlkem1024.ml for the AVX2 version, with the same bounds on  *)
(* the stack (see utils/mlkem_native2_avx512_noise.ml).                      *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native2_avx512_api.ml";;
needs "x86/proofs/utils/mlkem_native2_avx512_kem.ml";;
needs "x86/proofs/mlkem_gen_matrix_k4_avx512.ml";;
needs "x86/proofs/utils/mlkem_native2_avx512_kem_safe.ml";;
needs "x86/proofs/mlkem_gen_matrix_k4_safe_avx512.ml";;

(* ------------------------------------------------------------------------- *)
(* The modulus check of an encapsulation key pk: 0 if the 1024 12-bit        *)
(* fields of its polynomial vector are all < q, else -4                      *)
(* (MLK_ERR_INVALID_PK).                                                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM1024_CHECK_PK_AVX512_EXEC =
  MLKEM_NATIVE2_AVX512_IMAGE_EXEC ["mlkem1024_check_pk_avx512"];;

let MLKEM1024_CHECK_PK_AVX512_SUBROUTINE_CORRECT = prove
 (`!pk n pc stackpointer returnaddress.
     ALL (nonoverlapping (word_sub stackpointer (word 16),16))
         [(word pc,mlkem_native2_avx512_image_size); (pk,1536)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
               read RIP s = word(pc + mlkem1024_check_pk_avx512) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [pk] s /\
               read (memory :> bytes(pk,1536)) s = n)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s =
               if !i. i < 1024 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
               then word 0 else word 0xfffffffc)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MLKEM_NATIVE2_CHECK_PK_CORRECT_TAC MLKEM1024_CHECK_PK_AVX512_EXEC 4);;

let MLKEM1024_CHECK_PK_AVX512_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e pk pc stackpointer returnaddress.
       ALL (nonoverlapping (word_sub stackpointer (word 16),16))
           [(word pc,mlkem_native2_avx512_image_size); (pk,1536)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
                 read RIP s = word(pc + mlkem1024_check_pk_avx512) /\
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
                     [pk,1536; word_sub stackpointer (word 16),24]
                     [word_sub stackpointer (word 16),16]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MLKEM_NATIVE2_CHECK_PK_SAFE_TAC MLKEM1024_CHECK_PK_AVX512_EXEC);;

(* ------------------------------------------------------------------------- *)
(* The hash check of a decapsulation key sk, with ek at offset 1536 and the  *)
(* hash h of ek at offset 3104: 0 if h = H(ek), else -5                      *)
(* (MLK_ERR_INVALID_SK). The stack is the 320 bytes of the frame and those   *)
(* used by mlkem_hash_h_avx512.                                              *)
(* ------------------------------------------------------------------------- *)

let MLKEM1024_CHECK_SK_AVX512_EXEC =
  MLKEM_NATIVE2_AVX512_IMAGE_EXEC ["mlkem1024_check_sk_avx512"];;

let MLKEM1024_CHECK_SK_AVX512_SUBROUTINE_CORRECT = prove
 (`!sk (ek:byte list) h pc stackpointer returnaddress.
     LENGTH ek = 1568 /\
     ALL (nonoverlapping (word_sub stackpointer (word 320),320))
         [(word pc,mlkem_native2_avx512_image_size); (sk,3168)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
               read RIP s = word(pc + mlkem1024_check_sk_avx512) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [sk] s /\
               read (memory :> bytes(word_add sk (word 1536),1568)) s =
               num_of_bytelist ek /\
               read (memory :> bytes(word_add sk (word 3104),32)) s = h)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s =
               if h = num_of_bytelist(sha3_256 ek) then word 0
               else word 0xfffffffb)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 320),320)])`,
  MLKEM_NATIVE2_CHECK_SK_CORRECT_TAC MLKEM1024_CHECK_SK_AVX512_EXEC 3104);;

let MLKEM1024_CHECK_SK_AVX512_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e sk pc stackpointer returnaddress.
       ALL (nonoverlapping (word_sub stackpointer (word 320),320))
           [(word pc,mlkem_native2_avx512_image_size); (sk,3168)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
                 read RIP s = word(pc + mlkem1024_check_sk_avx512) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [sk] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events sk pc (word_sub stackpointer (word 320))
                                  returnaddress /\
                    memaccess_inbounds e2
                     [sk,3168; word(pc + mlkem_native2_constants),192;
                      word_sub stackpointer (word 320),328]
                     [word_sub stackpointer (word 320),320]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(word_sub stackpointer (word 320),320)])`,
  MLKEM_NATIVE2_CHECK_SK_SAFE_TAC MLKEM1024_CHECK_SK_AVX512_EXEC 1568);;

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

let MLKEM1024_PKE_ENCRYPT_AVX512_SUBROUTINE_CORRECT = prove
 (`!ct at pk mp noise (ek:byte list) (m:byte list) (r:byte list)
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
                                      6231)])`,
  MLKEM_NATIVE2_PKE_ENCRYPT_CORRECT_TAC 4 MLKEM1024_PKE_ENCRYPT_AVX512_EXEC);;

(* ------------------------------------------------------------------------- *)
(* K-PKE.Decrypt (FIPS 203 Algorithm 15) as the internal function            *)
(* mlkem1024_pke_decrypt_avx512(m, ct, sk): the message of the ciphertext c  *)
(* at ct under the decryption key dk at sk.                                  *)
(* ------------------------------------------------------------------------- *)

let MLKEM1024_PKE_DECRYPT_AVX512_EXEC =
  MLKEM_NATIVE2_AVX512_IMAGE_EXEC ["mlkem1024_pke_decrypt_avx512"];;

let MLKEM1024_PKE_DECRYPT_AVX512_SUBROUTINE_CORRECT = prove
 (`!mp ct sk (c:byte list) (dk:byte list) pc stackpointer returnaddress.
     aligned 32 (word pc:int64) /\ LENGTH c = 1568 /\ LENGTH dk = 1536 /\
     nonoverlapping (sk,1536) (word pc,mlkem_native2_avx512_image_size) /\
     PAIRWISE nonoverlapping
      [(mp,32); (word_sub stackpointer (word 6231),6239)] /\
     ALLPAIRS nonoverlapping
      [(mp,32); (word_sub stackpointer (word 6231),6239)]
      [(word pc,mlkem_native2_avx512_image_size); (ct,1568); (sk,1536)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
               read RIP s = word(pc + mlkem1024_pke_decrypt_avx512) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [mp; ct; sk] s /\
               read (memory :> bytes(ct,1568)) s = num_of_bytelist c /\
               read (memory :> bytes(sk,1536)) s = num_of_bytelist dk)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               read (memory :> bytes(mp,32)) s =
               num_of_bytelist(kpke_decrypt mlkem1024 dk c))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(mp,32);
                      memory :> bytes(word_sub stackpointer (word 6231),
                                      6231)])`,
  MLKEM_NATIVE2_PKE_DECRYPT_CORRECT_TAC 4 MLKEM1024_PKE_DECRYPT_AVX512_EXEC);;

(* ------------------------------------------------------------------------- *)
(* ML-KEM.KeyGen_internal (FIPS 203 Algorithm 16) from d and z at            *)
(* coins, the keys at pk and sk; the return value is 0.                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM1024_KEYPAIR_DERAND_AVX512_EXEC =
  MLKEM_NATIVE2_AVX512_IMAGE_EXEC ["mlkem1024_keypair_derand_avx512"];;

let MLKEM1024_KEYPAIR_DERAND_AVX512_SUBROUTINE_CORRECT = prove
 (`!pk sk coins (d:byte list) (z:byte list) pc stackpointer returnaddress.
     aligned 32 (word pc:int64) /\ LENGTH d = 32 /\ LENGTH z = 32 /\
     PAIRWISE nonoverlapping
      [(pk,1568); (sk,3168); (word_sub stackpointer (word 21334),21342)] /\
     ALLPAIRS nonoverlapping
      [(pk,1568); (sk,3168); (word_sub stackpointer (word 21334),21342)]
      [(coins,64); (word pc,mlkem_native2_avx512_image_size)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
               read RIP s = word(pc + mlkem1024_keypair_derand_avx512) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [pk; sk; coins] s /\
               read (memory :> bytes(coins,32)) s = num_of_bytelist d /\
               read (memory :> bytes(word_add coins (word 32),32)) s =
               num_of_bytelist z)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               read (memory :> bytes(pk,1568)) s =
               num_of_bytelist(FST(mlkem_keygen_internal mlkem1024 d z)) /\
               read (memory :> bytes(sk,3168)) s =
               num_of_bytelist(SND(mlkem_keygen_internal mlkem1024 d z)) /\
               C_RETURN s = word 0)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(pk,1568); memory :> bytes(sk,3168);
                      memory :> bytes(word_sub stackpointer (word 21334),
                                      21334)])`,
  MLKEM_NATIVE2_KEYPAIR_DERAND_CORRECT_TAC 4
    MLKEM1024_KEYPAIR_DERAND_AVX512_EXEC
   MLKEM_GEN_MATRIX_AVX512_K4_NOISE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* ML-KEM.Encaps_internal (FIPS 203 Algorithm 17), after the modulus         *)
(* check of the encapsulation key (FIPS 203 section 7.2): if the check       *)
(* passes, the shared secret at ss, the ciphertext at ct and the return      *)
(* value 0, else -4 (MLK_ERR_INVALID_PK).                                    *)
(* ------------------------------------------------------------------------- *)

let MLKEM1024_ENC_DERAND_AVX512_EXEC =
  MLKEM_NATIVE2_AVX512_IMAGE_EXEC ["mlkem1024_enc_derand_avx512"];;

let MLKEM1024_ENC_DERAND_AVX512_SUBROUTINE_CORRECT = prove
 (`!ct ss pk coins (ek:byte list) (m:byte list) pc stackpointer
    returnaddress.
     aligned 32 (word pc:int64) /\ LENGTH ek = 1568 /\ LENGTH m = 32 /\
     nonoverlapping (pk,1568) (word pc,mlkem_native2_avx512_image_size) /\
     PAIRWISE nonoverlapping
      [(ct,1568); (ss,32); (word_sub stackpointer (word 19342),19350)] /\
     ALLPAIRS nonoverlapping
      [(ct,1568); (ss,32); (word_sub stackpointer (word 19342),19350)]
      [(pk,1568); (coins,32); (word pc,mlkem_native2_avx512_image_size)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
               read RIP s = word(pc + mlkem1024_enc_derand_avx512) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [ct; ss; pk; coins] s /\
               read (memory :> bytes(pk,1568)) s = num_of_bytelist ek /\
               read (memory :> bytes(coins,32)) s = num_of_bytelist m)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (mlkem_ek_check mlkem1024 ek
                ==> read (memory :> bytes(ss,32)) s =
                    num_of_bytelist
                     (FST(mlkem_encaps_internal mlkem1024 ek m)) /\
                    read (memory :> bytes(ct,1568)) s =
                    num_of_bytelist
                     (SND(mlkem_encaps_internal mlkem1024 ek m))) /\
               C_RETURN s =
               (if mlkem_ek_check mlkem1024 ek then word 0
                else word 0xfffffffc))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(ct,1568); memory :> bytes(ss,32);
                      memory :> bytes(word_sub stackpointer (word 19342),
                                      19342)])`,
  MLKEM_NATIVE2_ENC_DERAND_CORRECT_TAC 4 MLKEM1024_ENC_DERAND_AVX512_EXEC
   MLKEM_GEN_MATRIX_AVX512_K4_HASH_SUBROUTINE_CORRECT
   MLKEM1024_PKE_ENCRYPT_AVX512_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* ML-KEM.Decaps_internal (FIPS 203 Algorithm 18), after the hash check      *)
(* of the decapsulation key (FIPS 203 section 7.3): if the check             *)
(* passes, the shared secret at ss and the return value 0, else -5           *)
(* (MLK_ERR_INVALID_SK).                                                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM1024_DEC_AVX512_EXEC =
  MLKEM_NATIVE2_AVX512_IMAGE_EXEC ["mlkem1024_dec_avx512"];;

let MLKEM1024_DEC_AVX512_SUBROUTINE_CORRECT = prove
 (`!ss ct sk (dk:byte list) (c:byte list) pc stackpointer returnaddress.
     aligned 32 (word pc:int64) /\ LENGTH dk = 3168 /\ LENGTH c = 1568 /\
     nonoverlapping (ct,1568) (word pc,mlkem_native2_avx512_image_size) /\
     nonoverlapping (sk,3168) (word pc,mlkem_native2_avx512_image_size) /\
     nonoverlapping (ss,32) (word_sub stackpointer (word 22606),22614) /\
     ALLPAIRS nonoverlapping
      [(ss,32); (word_sub stackpointer (word 22606),22614)]
      [(ct,1568); (sk,3168); (word pc,mlkem_native2_avx512_image_size)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
               read RIP s = word(pc + mlkem1024_dec_avx512) /\
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
                                      22606)])`,
  MLKEM_NATIVE2_DEC_CORRECT_TAC 4 MLKEM1024_DEC_AVX512_EXEC
   MLKEM_GEN_MATRIX_AVX512_K4_HASHES_NOISE_SUBROUTINE_CORRECT
   (MLKEM1024_PKE_DECRYPT_AVX512_SUBROUTINE_CORRECT,
    MLKEM1024_PKE_ENCRYPT_AVX512_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of the K-PKE encryption: the          *)
(* events depend only on the addresses.                                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM1024_PKE_ENCRYPT_AVX512_SUBROUTINE_SAFE = time prove
 (`exists f_events.
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
                                        6231)])`,
  MLKEM_NATIVE2_PKE_ENCRYPT_SAFE_TAC 4 MLKEM1024_PKE_ENCRYPT_AVX512_EXEC);;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of the K-PKE decryption: the          *)
(* events depend only on the addresses.                                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM1024_PKE_DECRYPT_AVX512_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e mp ct sk pc stackpointer returnaddress.
       aligned 32 (word pc:int64) /\
       nonoverlapping (sk,1536) (word pc,mlkem_native2_avx512_image_size) /\
       PAIRWISE nonoverlapping
        [(mp,32); (word_sub stackpointer (word 6231),6239)] /\
       ALLPAIRS nonoverlapping
        [(mp,32); (word_sub stackpointer (word 6231),6239)]
        [(word pc,mlkem_native2_avx512_image_size); (ct,1568); (sk,1536)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
                 read RIP s = word(pc + mlkem1024_pke_decrypt_avx512) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [mp; ct; sk] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events mp ct sk pc
                           (word_sub stackpointer (word 6231)) returnaddress /\
                    memaccess_inbounds e2
                     [mp,32; ct,1568; sk,1536;
                      word(pc + mlkem_native2_constants),6048;
                      word_sub stackpointer (word 6231),6239]
                     [mp,32; word_sub stackpointer (word 6231),6231]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(mp,32);
                        memory :> bytes(word_sub stackpointer (word 6231),
                                        6231)])`,
  MLKEM_NATIVE2_PKE_DECRYPT_SAFE_TAC 4 MLKEM1024_PKE_DECRYPT_AVX512_EXEC);;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of key generation: the events         *)
(* depend only on the addresses and on rho, which is public although         *)
(* computed from d (rho is at the end of pk). As in the proofs of the        *)
(* compiled C, the postcondition also gives rho in pk and the return         *)
(* value.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLKEM1024_KEYPAIR_DERAND_AVX512_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e pk sk coins (d:byte list) pc stackpointer returnaddress.
       aligned 32 (word pc:int64) /\ LENGTH d = 32 /\
       PAIRWISE nonoverlapping
        [(pk,1568); (sk,3168); (word_sub stackpointer (word 21334),21342)] /\
       ALLPAIRS nonoverlapping
        [(pk,1568); (sk,3168); (word_sub stackpointer (word 21334),21342)]
        [(coins,64); (word pc,mlkem_native2_avx512_image_size)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
                 read RIP s = word(pc + mlkem1024_keypair_derand_avx512) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [pk; sk; coins] s /\
                 read (memory :> bytes(coins,32)) s = num_of_bytelist d /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 C_RETURN s = word 0 /\
                 read (memory :> bytes(word_add pk (word 1536),32)) s =
                 num_of_bytelist(FST(mlkem_g(APPEND d [word 4]))) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events pk sk coins pc
                           (word_sub stackpointer (word 21334)) returnaddress
                           (FST(mlkem_g(APPEND d [word 4]))) /\
                    memaccess_inbounds e2
                     [coins,64; pk,1568; sk,3168;
                      word(pc + mlkem_native2_constants),6048;
                      word_sub stackpointer (word 21334),21342]
                     [pk,1568; sk,3168;
                      word_sub stackpointer (word 21334),21334]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(pk,1568); memory :> bytes(sk,3168);
                        memory :> bytes(word_sub stackpointer (word 21334),
                                        21334)])`,
  MLKEM_NATIVE2_KEYPAIR_DERAND_SAFE_TAC 4 MLKEM1024_KEYPAIR_DERAND_AVX512_EXEC
   MLKEM_GEN_MATRIX_AVX512_K4_NOISE_SUBROUTINE_SAFE);;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of encapsulation: the events          *)
(* depend only on the addresses and on ek, which is public, and on           *)
(* whether it passes the modulus check. As in the proofs of the              *)
(* compiled C, the postcondition also gives the return value.                *)
(* ------------------------------------------------------------------------- *)

let MLKEM1024_ENC_DERAND_AVX512_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e ct ss pk coins (ek:byte list) pc stackpointer returnaddress.
       aligned 32 (word pc:int64) /\ LENGTH ek = 1568 /\
       nonoverlapping (pk,1568) (word pc,mlkem_native2_avx512_image_size) /\
       PAIRWISE nonoverlapping
        [(ct,1568); (ss,32); (word_sub stackpointer (word 19342),19350)] /\
       ALLPAIRS nonoverlapping
        [(ct,1568); (ss,32); (word_sub stackpointer (word 19342),19350)]
        [(pk,1568); (coins,32); (word pc,mlkem_native2_avx512_image_size)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
                 read RIP s = word(pc + mlkem1024_enc_derand_avx512) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [ct; ss; pk; coins] s /\
                 read (memory :> bytes(pk,1568)) s = num_of_bytelist ek /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 C_RETURN s =
                 (if mlkem_ek_check mlkem1024 ek then word 0
                  else word 0xfffffffc) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events ct ss pk coins pc
                           (word_sub stackpointer (word 19342))
                           returnaddress ek /\
                    memaccess_inbounds e2
                     [pk,1568; coins,32; ct,1568; ss,32;
                      word(pc + mlkem_native2_constants),6048;
                      word_sub stackpointer (word 19342),19350]
                     [ct,1568; ss,32;
                      word_sub stackpointer (word 19342),19342]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(ct,1568); memory :> bytes(ss,32);
                        memory :> bytes(word_sub stackpointer (word 19342),
                                        19342)])`,
  MLKEM_NATIVE2_ENC_DERAND_SAFE_TAC 4 MLKEM1024_ENC_DERAND_AVX512_EXEC
   MLKEM_GEN_MATRIX_AVX512_K4_HASH_SUBROUTINE_SAFE
   MLKEM1024_PKE_ENCRYPT_AVX512_SUBROUTINE_SAFE);;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of decapsulation: the events          *)
(* depend only on the addresses and on ek and h in dk, which are             *)
(* public, and on whether h = H(ek) (the hash check). As in the proofs       *)
(* of the compiled C, there are no results in the postcondition.             *)
(* ------------------------------------------------------------------------- *)

let MLKEM1024_DEC_AVX512_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e ss ct sk (dk:byte list) pc stackpointer returnaddress.
       aligned 32 (word pc:int64) /\ LENGTH dk = 3168 /\
       nonoverlapping (ct,1568) (word pc,mlkem_native2_avx512_image_size) /\
       nonoverlapping (sk,3168) (word pc,mlkem_native2_avx512_image_size) /\
       nonoverlapping (ss,32) (word_sub stackpointer (word 22606),22614) /\
       ALLPAIRS nonoverlapping
        [(ss,32); (word_sub stackpointer (word 22606),22614)]
        [(ct,1568); (sk,3168); (word pc,mlkem_native2_avx512_image_size)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
                 read RIP s = word(pc + mlkem1024_dec_avx512) /\
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
                      word_sub stackpointer (word 22606),22614]
                     [ss,32; word_sub stackpointer (word 22606),22606]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(ss,32);
                        memory :> bytes(word_sub stackpointer (word 22606),
                                        22606)])`,
  MLKEM_NATIVE2_DEC_SAFE_TAC 4 MLKEM1024_DEC_AVX512_EXEC
   MLKEM_GEN_MATRIX_AVX512_K4_HASHES_NOISE_SUBROUTINE_SAFE
   (MLKEM1024_PKE_DECRYPT_AVX512_SUBROUTINE_SAFE,
    MLKEM1024_PKE_ENCRYPT_AVX512_SUBROUTINE_SAFE));;
