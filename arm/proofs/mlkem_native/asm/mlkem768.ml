(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The API of ML-KEM-768 in mlkem_native2 (arm/mlkem_native/asm/mlkem768.S), *)
(* in the image: the key checks of FIPS 203 (section 7), the internal        *)
(* functions for K-PKE encryption and decryption, and key generation,        *)
(* encapsulation and decapsulation, with the results, and their              *)
(* constant-time and memory safety, stated as in the proofs of the compiled  *)
(* C of mlkem-native.                                                        *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native2_api.ml";;
needs "arm/proofs/utils/mlkem_native2_kem.ml";;
needs "arm/proofs/mlkem_native/asm/mlkem_gen_matrix_k3.ml";;
needs "arm/proofs/utils/mlkem_native2_kem_safe.ml";;
needs "arm/proofs/mlkem_native/asm/mlkem_gen_matrix_k3_safe.ml";;
needs "arm/proofs/mlkem_basemul_k3_alt.ml";;
needs "arm/proofs/mlkem_compress_d4.ml";;
needs "arm/proofs/mlkem_compress_d10.ml";;
needs "arm/proofs/mlkem_decompress_d4.ml";;
needs "arm/proofs/mlkem_decompress_d10.ml";;

(* ------------------------------------------------------------------------- *)
(* The kernels of ML-KEM-768 that depend on the parameter set (decompress_d  *)
(* and compress_d for du = 10 and dv = 4, and basemul_k3_alt), loaded here   *)
(* and not by the tools, so that the proof of each parameter set proves only *)
(* its own, added to the kernels that the tools call: their correctness      *)
(* theorems for utils/mlkem_native2_kem.ml, and their safety with the frames *)
(* as in utils/mlkem_native2_kem_safe.ml. The names of the theorems of       *)
(* safety are bound in parentheses, so that tools/collect-specs.sh does not  *)
(* take them for specifications of this file.                                *)
(* ------------------------------------------------------------------------- *)

api_add_kernels
 ["mlkem_decompress_d4",mlkem_decompress_d4_mc,
  MLKEM_DECOMPRESS_D4_SUBROUTINE_CORRECT;
  "mlkem_decompress_d10",mlkem_decompress_d10_mc,
  MLKEM_DECOMPRESS_D10_SUBROUTINE_CORRECT;
  "mlkem_compress_d4",mlkem_compress_d4_mc,
  MLKEM_COMPRESS_D4_SUBROUTINE_CORRECT;
  "mlkem_compress_d10",mlkem_compress_d10_mc,
  MLKEM_COMPRESS_D10_SUBROUTINE_CORRECT;
  "mlkem_basemul_k3_alt",mlkem_basemul_k3_alt_mc,
  MLKEM_BASEMUL_K3_ALT_SUBROUTINE_CORRECT];;

api_add_basemul_defs 3 pmull
 [basemul3_even; basemul3_odd; pmul_acc3; pmull_acc3];;

let (MLKEM_BASEMUL_K3_ALT_CORE_SAFE_FRAMED,
     MLKEM_BASEMUL_K3_ALT_NOIBT_SUBROUTINE_SAFE_FRAMED,
     MLKEM_BASEMUL_K3_ALT_SUBROUTINE_SAFE_FRAMED) =
  FRAMED_STACK_KERNEL MLKEM_BASEMUL_K3_ALT_CORRECT
    MLKEM_BASEMUL_K3_ALT_NOIBT_SUBROUTINE_SAFE
    MLKEM_BASEMUL_K3_ALT_NOIBT_SUBROUTINE_CORRECT
    MLKEM_BASEMUL_K3_ALT_EXEC (5,5)
    mlkem_basemul_k3_alt_mc mlkem_basemul_k3_alt_tmc;;

let (MLKEM_COMPRESS_D4_NOIBT_SUBROUTINE_SAFE_FRAMED:thm) =
  framed_kernel_safe "mlkem_compress_d4"
    MLKEM_COMPRESS_D4_NOIBT_SUBROUTINE_CORRECT
    MLKEM_COMPRESS_D4_EXEC;;

let (MLKEM_COMPRESS_D4_SUBROUTINE_SAFE_FRAMED:thm) =
  ARM_ADD_IBT_RULE mlkem_compress_d4_mc mlkem_compress_d4_tmc
    MLKEM_COMPRESS_D4_NOIBT_SUBROUTINE_SAFE_FRAMED;;

let (MLKEM_COMPRESS_D10_CORE_SAFE_FRAMED,
     MLKEM_COMPRESS_D10_NOIBT_SUBROUTINE_SAFE_FRAMED,
     MLKEM_COMPRESS_D10_SUBROUTINE_SAFE_FRAMED) =
  FRAMED_STACK_KERNEL MLKEM_COMPRESS_D10_CORRECT
    MLKEM_COMPRESS_D10_NOIBT_SUBROUTINE_SAFE
    MLKEM_COMPRESS_D10_NOIBT_SUBROUTINE_CORRECT
    MLKEM_COMPRESS_D10_EXEC (4,4)
    mlkem_compress_d10_mc mlkem_compress_d10_tmc;;

let (MLKEM_DECOMPRESS_D4_NOIBT_SUBROUTINE_SAFE_FRAMED:thm) =
  framed_kernel_safe "mlkem_decompress_d4"
    MLKEM_DECOMPRESS_D4_NOIBT_SUBROUTINE_CORRECT
    MLKEM_DECOMPRESS_D4_EXEC;;

let (MLKEM_DECOMPRESS_D4_SUBROUTINE_SAFE_FRAMED:thm) =
  ARM_ADD_IBT_RULE mlkem_decompress_d4_mc mlkem_decompress_d4_tmc
    MLKEM_DECOMPRESS_D4_NOIBT_SUBROUTINE_SAFE_FRAMED;;

let (MLKEM_DECOMPRESS_D10_NOIBT_SUBROUTINE_SAFE_FRAMED:thm) =
  framed_kernel_safe "mlkem_decompress_d10"
    MLKEM_DECOMPRESS_D10_NOIBT_SUBROUTINE_CORRECT
    MLKEM_DECOMPRESS_D10_EXEC;;

let (MLKEM_DECOMPRESS_D10_SUBROUTINE_SAFE_FRAMED:thm) =
  ARM_ADD_IBT_RULE mlkem_decompress_d10_mc mlkem_decompress_d10_tmc
    MLKEM_DECOMPRESS_D10_NOIBT_SUBROUTINE_SAFE_FRAMED;;

api_add_safe_kernels
 ["mlkem_basemul_k3_alt","H_BASEMUL3",
  MLKEM_BASEMUL_K3_ALT_SUBROUTINE_SAFE_FRAMED,mlkem_basemul_k3_alt_mc;
  "mlkem_compress_d4","H_COMPRESS4",
  MLKEM_COMPRESS_D4_SUBROUTINE_SAFE_FRAMED,mlkem_compress_d4_mc;
  "mlkem_compress_d10","H_COMPRESS10",
  MLKEM_COMPRESS_D10_SUBROUTINE_SAFE_FRAMED,mlkem_compress_d10_mc;
  "mlkem_decompress_d4","H_DECOMPRESS4",
  MLKEM_DECOMPRESS_D4_SUBROUTINE_SAFE_FRAMED,mlkem_decompress_d4_mc;
  "mlkem_decompress_d10","H_DECOMPRESS10",
  MLKEM_DECOMPRESS_D10_SUBROUTINE_SAFE_FRAMED,mlkem_decompress_d10_mc];;

(* ------------------------------------------------------------------------- *)
(* The modulus check of an encapsulation key pk: 0 if the 768 12-bit fields  *)
(* of its polynomial vector are all < q, else -4 (MLK_ERR_INVALID_PK).       *)
(* ------------------------------------------------------------------------- *)

let MLKEM768_CHECK_PK_EXEC = MLKEM_NATIVE2_IMAGE_EXEC ["mlkem768_check_pk"];;

let MLKEM768_CHECK_PK_SUBROUTINE_CORRECT = prove
 (`!pk n pc stackpointer returnaddress.
     aligned 16 stackpointer /\
     ALL (nonoverlapping (word_sub stackpointer (word 16),16))
         [(word pc,mlkem_native2_image_size); (pk,1152)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem768_check_pk) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [pk] s /\
               read (memory :> bytes(pk,1152)) s = n)
          (\s. read PC s = returnaddress /\
               C_RETURN s =
               if !i. i < 768 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
               then word 0 else word 0xfffffffc)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MLKEM_NATIVE2_CHECK_PK_CORRECT_TAC MLKEM768_CHECK_PK_EXEC 3);;

let MLKEM768_CHECK_PK_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e pk pc stackpointer returnaddress.
       aligned 16 stackpointer /\
       ALL (nonoverlapping (word_sub stackpointer (word 16),16))
           [(word pc,mlkem_native2_image_size); (pk,1152)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem768_check_pk) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [pk] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events pk pc (word_sub stackpointer (word 16))
                                  returnaddress /\
                    memaccess_inbounds e2
                     [pk,1152; word_sub stackpointer (word 16),16]
                     [word_sub stackpointer (word 16),16]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MLKEM_NATIVE2_CHECK_PK_SAFE_TAC MLKEM768_CHECK_PK_EXEC);;

(* ------------------------------------------------------------------------- *)
(* The hash check of a decapsulation key sk, with ek at offset 1152 and the  *)
(* hash h of ek at offset 2336: 0 if h = H(ek), else -5                      *)
(* (MLK_ERR_INVALID_SK). The stack is the 64 bytes of the frame and the 384  *)
(* used by mlkem_hash_h. As for all the API functions, the image must be at  *)
(* a multiple of 4096, for the address of the constants block by ADRP.       *)
(* ------------------------------------------------------------------------- *)

let MLKEM768_CHECK_SK_EXEC = MLKEM_NATIVE2_IMAGE_EXEC ["mlkem768_check_sk"];;

let MLKEM768_CHECK_SK_SUBROUTINE_CORRECT = prove
 (`!sk (ek:byte list) h pc stackpointer returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + mlkem_native2_image_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH ek = 1184 /\
     ALL (nonoverlapping (word_sub stackpointer (word 448),448))
         [(word pc,mlkem_native2_image_size); (sk,2400)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem768_check_sk) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [sk] s /\
               read (memory :> bytes(word_add sk (word 1152),1184)) s =
               num_of_bytelist ek /\
               read (memory :> bytes(word_add sk (word 2336),32)) s = h)
          (\s. read PC s = returnaddress /\
               C_RETURN s =
               if h = num_of_bytelist(sha3_256 ek) then word 0
               else word 0xfffffffb)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 448),448)])`,
  MLKEM_NATIVE2_CHECK_SK_CORRECT_TAC MLKEM768_CHECK_SK_EXEC 2336);;

let MLKEM768_CHECK_SK_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e sk pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\
       pc + mlkem_native2_image_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       ALL (nonoverlapping (word_sub stackpointer (word 448),448))
           [(word pc,mlkem_native2_image_size); (sk,2400)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem768_check_sk) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [sk] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events sk pc (word_sub stackpointer (word 448))
                                  returnaddress /\
                    memaccess_inbounds e2
                     [sk,2400; word(pc + mlkem_native2_constants),192;
                      word_sub stackpointer (word 448),448]
                     [word_sub stackpointer (word 448),448]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(word_sub stackpointer (word 448),448)])`,
  MLKEM_NATIVE2_CHECK_SK_SAFE_TAC MLKEM768_CHECK_SK_EXEC 1184);;

(* ------------------------------------------------------------------------- *)
(* K-PKE.Encrypt (FIPS 203 Algorithm 14) as the internal function            *)
(* mlkem768_pke_encrypt(ct, at, pk, m, noise): the ciphertext of the message *)
(* m under the encryption key ek at pk with randomness r, given the          *)
(* transposed matrix at (row i, column j sampled from rho || i || j) and the *)
(* noise y, e1, e2 sampled from r as 16-bit coefficients at noise, which are *)
(* overwritten.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLKEM768_PKE_ENCRYPT_EXEC =
  MLKEM_NATIVE2_IMAGE_EXEC ["mlkem768_pke_encrypt"];;

let MLKEM768_PKE_ENCRYPT_SUBROUTINE_CORRECT = prove
 (`!ct at pk mp noise (ek:byte list) (m:byte list) (r:byte list)
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
                                      5024)])`,
  MLKEM_NATIVE2_PKE_ENCRYPT_CORRECT_TAC 3 MLKEM768_PKE_ENCRYPT_EXEC);;

(* ------------------------------------------------------------------------- *)
(* K-PKE.Decrypt (FIPS 203 Algorithm 15) as the internal function            *)
(* mlkem768_pke_decrypt(m, ct, sk): the message of the ciphertext c at ct    *)
(* under the decryption key dk in the first 1152 bytes at sk.                *)
(* ------------------------------------------------------------------------- *)

let MLKEM768_PKE_DECRYPT_EXEC =
  MLKEM_NATIVE2_IMAGE_EXEC ["mlkem768_pke_decrypt"];;

let MLKEM768_PKE_DECRYPT_SUBROUTINE_CORRECT = prove
 (`!mp ct sk (c:byte list) (dk:byte list) pc stackpointer returnaddress.
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
                                      5024)])`,
  MLKEM_NATIVE2_PKE_DECRYPT_CORRECT_TAC 3 MLKEM768_PKE_DECRYPT_EXEC);;

(* ------------------------------------------------------------------------- *)
(* ML-KEM.KeyGen_internal (FIPS 203 Algorithm 16) with coins = d || z: the   *)
(* encapsulation key at pk, the decapsulation key at sk and the return value *)
(* 0.                                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM768_KEYPAIR_DERAND_EXEC =
  MLKEM_NATIVE2_IMAGE_EXEC ["mlkem768_keypair_derand"];;

let MLKEM768_KEYPAIR_DERAND_SUBROUTINE_CORRECT = prove
 (`!pk sk coins (d:byte list) (z:byte list) pc stackpointer returnaddress.
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
                                      13552)])`,
  MLKEM_NATIVE2_KEYPAIR_DERAND_CORRECT_TAC 3 MLKEM768_KEYPAIR_DERAND_EXEC
   MLKEM_GEN_MATRIX_K3_NOISE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* ML-KEM.Encaps_internal (FIPS 203 Algorithm 17) with coins = m, after the  *)
(* modulus check of the encapsulation key (FIPS 203 section 7.2): if the     *)
(* check passes, the shared secret at ss, the ciphertext at ct and the       *)
(* return value 0, else -4 (MLK_ERR_INVALID_PK).                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM768_ENC_DERAND_EXEC =
  MLKEM_NATIVE2_IMAGE_EXEC ["mlkem768_enc_derand"];;

let MLKEM768_ENC_DERAND_SUBROUTINE_CORRECT = prove
 (`!ct ss pk coins (ek:byte list) (m:byte list) pc stackpointer
    returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + mlkem_native2_image_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH ek = 1184 /\ LENGTH m = 32 /\
     nonoverlapping (pk,1184) (word pc,mlkem_native2_image_size) /\
     PAIRWISE nonoverlapping
      [(ct,1088); (ss,32); (word_sub stackpointer (word 13504),13504)] /\
     ALLPAIRS nonoverlapping
      [(ct,1088); (ss,32); (word_sub stackpointer (word 13504),13504)]
      [(pk,1184); (coins,32); (word pc,mlkem_native2_image_size)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem768_enc_derand) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [ct; ss; pk; coins] s /\
               read (memory :> bytes(pk,1184)) s = num_of_bytelist ek /\
               read (memory :> bytes(coins,32)) s = num_of_bytelist m)
          (\s. read PC s = returnaddress /\
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
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(ct,1088); memory :> bytes(ss,32);
                      memory :> bytes(word_sub stackpointer (word 13504),
                                      13504)])`,
  MLKEM_NATIVE2_ENC_DERAND_CORRECT_TAC 3 MLKEM768_ENC_DERAND_EXEC
   MLKEM_GEN_MATRIX_K3_HASH_SUBROUTINE_CORRECT
   MLKEM768_PKE_ENCRYPT_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* ML-KEM.Decaps_internal (FIPS 203 Algorithm 18), after the hash check of   *)
(* the decapsulation key (FIPS 203 section 7.3): if the check passes, the    *)
(* shared secret at ss and the return value 0, else -5 (MLK_ERR_INVALID_SK). *)
(* ------------------------------------------------------------------------- *)

let MLKEM768_DEC_EXEC = MLKEM_NATIVE2_IMAGE_EXEC ["mlkem768_dec"];;

let MLKEM768_DEC_SUBROUTINE_CORRECT = prove
 (`!ss ct sk (dk:byte list) (c:byte list) pc stackpointer returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + mlkem_native2_image_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH dk = 2400 /\ LENGTH c = 1088 /\
     nonoverlapping (ct,1088) (word pc,mlkem_native2_image_size) /\
     nonoverlapping (sk,2400) (word pc,mlkem_native2_image_size) /\
     nonoverlapping (ss,32) (word_sub stackpointer (word 15824),15824) /\
     ALLPAIRS nonoverlapping
      [(ss,32); (word_sub stackpointer (word 15824),15824)]
      [(ct,1088); (sk,2400); (word pc,mlkem_native2_image_size)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem768_dec) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [ss; ct; sk] s /\
               read (memory :> bytes(ct,1088)) s = num_of_bytelist c /\
               read (memory :> bytes(sk,2400)) s = num_of_bytelist dk)
          (\s. read PC s = returnaddress /\
               (mlkem_decaps_check mlkem768 dk c
                ==> read (memory :> bytes(ss,32)) s =
                    num_of_bytelist(mlkem_decaps_internal mlkem768 dk c)) /\
               C_RETURN s =
               (if mlkem_decaps_check mlkem768 dk c then word 0
                else word 0xfffffffb))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(ss,32);
                      memory :> bytes(word_sub stackpointer (word 15824),
                                      15824)])`,
  MLKEM_NATIVE2_DEC_CORRECT_TAC 3 MLKEM768_DEC_EXEC
   MLKEM_GEN_MATRIX_K3_HASHES_NOISE_SUBROUTINE_CORRECT
   (MLKEM768_PKE_DECRYPT_SUBROUTINE_CORRECT,
    MLKEM768_PKE_ENCRYPT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of the K-PKE encryption: the events   *)
(* depend only on the addresses.                                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM768_PKE_ENCRYPT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
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
                                        5024)])`,
  MLKEM_NATIVE2_PKE_ENCRYPT_SAFE_TAC 3 MLKEM768_PKE_ENCRYPT_EXEC);;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of the K-PKE decryption: the events   *)
(* depend only on the addresses.                                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM768_PKE_DECRYPT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
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
                                        5024)])`,
  MLKEM_NATIVE2_PKE_DECRYPT_SAFE_TAC 3 MLKEM768_PKE_DECRYPT_EXEC);;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of key generation: the events depend  *)
(* only on the addresses and on rho, which is public although computed from  *)
(* d (rho is at the end of pk). As in the proofs of the compiled C, the      *)
(* postcondition also gives rho in pk and the return value.                  *)
(* ------------------------------------------------------------------------- *)

let MLKEM768_KEYPAIR_DERAND_SUBROUTINE_SAFE = time prove
 (`exists f_events.
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
                                        13552)])`,
  MLKEM_NATIVE2_KEYPAIR_DERAND_SAFE_TAC 3 MLKEM768_KEYPAIR_DERAND_EXEC
   MLKEM_GEN_MATRIX_K3_NOISE_SUBROUTINE_SAFE);;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of encapsulation: the events depend   *)
(* only on the addresses and on ek, which is public, and on whether it       *)
(* passes the modulus check. As in the proofs of the compiled C, the         *)
(* postcondition also gives the return value.                                *)
(* ------------------------------------------------------------------------- *)

let MLKEM768_ENC_DERAND_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e ct ss pk coins (ek:byte list) pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\
       pc + mlkem_native2_image_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ LENGTH ek = 1184 /\
       nonoverlapping (pk,1184) (word pc,mlkem_native2_image_size) /\
       PAIRWISE nonoverlapping
        [(ct,1088); (ss,32); (word_sub stackpointer (word 13504),13504)] /\
       ALLPAIRS nonoverlapping
        [(ct,1088); (ss,32); (word_sub stackpointer (word 13504),13504)]
        [(pk,1184); (coins,32); (word pc,mlkem_native2_image_size)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem768_enc_derand) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [ct; ss; pk; coins] s /\
                 read (memory :> bytes(pk,1184)) s = num_of_bytelist ek /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 C_RETURN s =
                 (if mlkem_ek_check mlkem768 ek then word 0
                  else word 0xfffffffc) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events ct ss pk coins pc
                           (word_sub stackpointer (word 13504))
                           returnaddress ek /\
                    memaccess_inbounds e2
                     [pk,1184; coins,32; ct,1088; ss,32;
                      word(pc + mlkem_native2_constants),6656;
                      word_sub stackpointer (word 13504),13504]
                     [ct,1088; ss,32;
                      word_sub stackpointer (word 13504),13504]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(ct,1088); memory :> bytes(ss,32);
                        memory :> bytes(word_sub stackpointer (word 13504),
                                        13504)])`,
  MLKEM_NATIVE2_ENC_DERAND_SAFE_TAC 3 MLKEM768_ENC_DERAND_EXEC
   MLKEM_GEN_MATRIX_K3_HASH_SUBROUTINE_SAFE
   MLKEM768_PKE_ENCRYPT_SUBROUTINE_SAFE);;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of decapsulation: the events depend   *)
(* only on the addresses and on ek and h in dk, which are public, and on     *)
(* whether h = H(ek) (the hash check). As in the proofs of the compiled C,   *)
(* there are no results in the postcondition.                                *)
(* ------------------------------------------------------------------------- *)

let MLKEM768_DEC_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e ss ct sk (dk:byte list) pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\
       pc + mlkem_native2_image_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ LENGTH dk = 2400 /\
       nonoverlapping (ct,1088) (word pc,mlkem_native2_image_size) /\
       nonoverlapping (sk,2400) (word pc,mlkem_native2_image_size) /\
       nonoverlapping (ss,32) (word_sub stackpointer (word 15824),15824) /\
       ALLPAIRS nonoverlapping
        [(ss,32); (word_sub stackpointer (word 15824),15824)]
        [(ct,1088); (sk,2400); (word pc,mlkem_native2_image_size)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem768_dec) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [ss; ct; sk] s /\
                 read (memory :> bytes(sk,2400)) s = num_of_bytelist dk /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events ss ct sk pc
                           (word_sub stackpointer (word 15824)) returnaddress
                           (mlkem_slice 1152 1184 dk)
                           (mlkem_slice 2336 32 dk) /\
                    memaccess_inbounds e2
                     [ct,1088; sk,2400; ss,32;
                      word(pc + mlkem_native2_constants),6656;
                      word_sub stackpointer (word 15824),15824]
                     [ss,32; word_sub stackpointer (word 15824),15824]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(ss,32);
                        memory :> bytes(word_sub stackpointer (word 15824),
                                        15824)])`,
  MLKEM_NATIVE2_DEC_SAFE_TAC 3 MLKEM768_DEC_EXEC
   MLKEM_GEN_MATRIX_K3_HASHES_NOISE_SUBROUTINE_SAFE
   (MLKEM768_PKE_DECRYPT_SUBROUTINE_SAFE,
    MLKEM768_PKE_ENCRYPT_SUBROUTINE_SAFE));;
