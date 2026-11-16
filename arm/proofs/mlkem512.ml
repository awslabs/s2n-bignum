(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The API of ML-KEM-512 in mlkem_native2 (arm/mlkem_native2/mlkem512.S), in *)
(* the image: the key checks of FIPS 203 (section 7), the internal functions *)
(* for K-PKE encryption and decryption, and key generation, encapsulation    *)
(* and decapsulation, with the results, and their constant-time and memory   *)
(* safety, stated as in the proofs of the compiled C of mlkem-native.        *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native2_api.ml";;
needs "arm/proofs/utils/mlkem_native2_kem.ml";;
needs "arm/proofs/mlkem_gen_matrix_k2.ml";;
needs "arm/proofs/utils/mlkem_native2_kem_safe.ml";;
needs "arm/proofs/mlkem_gen_matrix_k2_safe.ml";;

(* ------------------------------------------------------------------------- *)
(* The modulus check of an encapsulation key pk: 0 if the 512 12-bit fields  *)
(* of its polynomial vector are all < q, else -4 (MLK_ERR_INVALID_PK).       *)
(* ------------------------------------------------------------------------- *)

let MLKEM512_CHECK_PK_EXEC = MLKEM_NATIVE2_IMAGE_EXEC ["mlkem512_check_pk"];;

let MLKEM512_CHECK_PK_SUBROUTINE_CORRECT = prove
 (`!pk n pc stackpointer returnaddress.
     aligned 16 stackpointer /\
     ALL (nonoverlapping (word_sub stackpointer (word 16),16))
         [(word pc,mlkem_native2_image_size); (pk,768)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem512_check_pk) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [pk] s /\
               read (memory :> bytes(pk,768)) s = n)
          (\s. read PC s = returnaddress /\
               C_RETURN s =
               if !i. i < 512 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
               then word 0 else word 0xfffffffc)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MLKEM_NATIVE2_CHECK_PK_CORRECT_TAC MLKEM512_CHECK_PK_EXEC 2);;

let MLKEM512_CHECK_PK_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e pk pc stackpointer returnaddress.
       aligned 16 stackpointer /\
       ALL (nonoverlapping (word_sub stackpointer (word 16),16))
           [(word pc,mlkem_native2_image_size); (pk,768)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem512_check_pk) /\
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
                     [pk,768; word_sub stackpointer (word 16),16]
                     [word_sub stackpointer (word 16),16]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MLKEM_NATIVE2_CHECK_PK_SAFE_TAC MLKEM512_CHECK_PK_EXEC);;

(* ------------------------------------------------------------------------- *)
(* The hash check of a decapsulation key sk, with ek at offset 768 and the   *)
(* hash h of ek at offset 1568: 0 if h = H(ek), else -5                      *)
(* (MLK_ERR_INVALID_SK). The stack is the 64 bytes of the frame and the 384  *)
(* used by mlkem_hash_h. As for all the API functions, the image must be at  *)
(* a multiple of 4096, for the address of the constants block by ADRP.       *)
(* ------------------------------------------------------------------------- *)

let MLKEM512_CHECK_SK_EXEC = MLKEM_NATIVE2_IMAGE_EXEC ["mlkem512_check_sk"];;

let MLKEM512_CHECK_SK_SUBROUTINE_CORRECT = prove
 (`!sk (ek:byte list) h pc stackpointer returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + mlkem_native2_image_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH ek = 800 /\
     ALL (nonoverlapping (word_sub stackpointer (word 448),448))
         [(word pc,mlkem_native2_image_size); (sk,1632)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem512_check_sk) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [sk] s /\
               read (memory :> bytes(word_add sk (word 768),800)) s =
               num_of_bytelist ek /\
               read (memory :> bytes(word_add sk (word 1568),32)) s = h)
          (\s. read PC s = returnaddress /\
               C_RETURN s =
               if h = num_of_bytelist(sha3_256 ek) then word 0
               else word 0xfffffffb)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 448),448)])`,
  MLKEM_NATIVE2_CHECK_SK_CORRECT_TAC MLKEM512_CHECK_SK_EXEC 1568);;

let MLKEM512_CHECK_SK_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e sk pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\
       pc + mlkem_native2_image_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       ALL (nonoverlapping (word_sub stackpointer (word 448),448))
           [(word pc,mlkem_native2_image_size); (sk,1632)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem512_check_sk) /\
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
                     [sk,1632; word(pc + mlkem_native2_constants),192;
                      word_sub stackpointer (word 448),448]
                     [word_sub stackpointer (word 448),448]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(word_sub stackpointer (word 448),448)])`,
  MLKEM_NATIVE2_CHECK_SK_SAFE_TAC MLKEM512_CHECK_SK_EXEC 800);;

(* ------------------------------------------------------------------------- *)
(* K-PKE.Encrypt (FIPS 203 Algorithm 14) as the internal function            *)
(* mlkem512_pke_encrypt(ct, at, pk, m, noise): the ciphertext of the message *)
(* m under the encryption key ek at pk with randomness r, given the          *)
(* transposed matrix at (row i, column j sampled from rho || i || j) and the *)
(* noise y, e1, e2 sampled from r as 16-bit coefficients at noise, which are *)
(* overwritten.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLKEM512_PKE_ENCRYPT_EXEC =
  MLKEM_NATIVE2_IMAGE_EXEC ["mlkem512_pke_encrypt"];;

let MLKEM512_PKE_ENCRYPT_SUBROUTINE_CORRECT = prove
 (`!ct at pk mp noise (ek:byte list) (m:byte list) (r:byte list)
    pc stackpointer returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + mlkem_native2_image_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH ek = 800 /\ LENGTH m = 32 /\
     PAIRWISE nonoverlapping
      [(ct,768); (noise,2560); (word_sub stackpointer (word 3744),3744)] /\
     ALLPAIRS nonoverlapping
      [(ct,768); (noise,2560); (word_sub stackpointer (word 3744),3744)]
      [(word pc,mlkem_native2_image_size); (at,2048); (pk,800); (mp,32)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem512_pke_encrypt) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [ct; at; pk; mp; noise] s /\
               (!i j t. i < 2 /\ j < 2 /\ t < 256
                        ==> read(memory :> bytes16(word_add at
                                 (word(512 * (2 * i + j) + 2 * t)))) s =
                            iword(mlkem_sample_ntt
                                   (APPEND (mlkem_slice 768 32 ek)
                                           [word i; word j]) t)) /\
               read (memory :> bytes(pk,800)) s = num_of_bytelist ek /\
               read (memory :> bytes(mp,32)) s = num_of_bytelist m /\
               (!i t. i < 5 /\ t < 256
                      ==> read(memory :> bytes16(word_add noise
                                 (word(512 * i + 2 * t)))) s =
                          iword(mlkem_cbd_coeff (if i < 2 then 3 else 2)
                                (mlkem_prf (if i < 2 then 3 else 2) r (word i))
                                t)))
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(ct,768)) s =
               num_of_bytelist(kpke_encrypt mlkem512 ek m r))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(ct,768); memory :> bytes(noise,2560);
                      memory :> bytes(word_sub stackpointer (word 3744),
                                      3744)])`,
  MLKEM_NATIVE2_PKE_ENCRYPT_CORRECT_TAC 2 MLKEM512_PKE_ENCRYPT_EXEC);;

(* ------------------------------------------------------------------------- *)
(* K-PKE.Decrypt (FIPS 203 Algorithm 15) as the internal function            *)
(* mlkem512_pke_decrypt(m, ct, sk): the message of the ciphertext c at ct    *)
(* under the decryption key dk in the first 768 bytes at sk.                 *)
(* ------------------------------------------------------------------------- *)

let MLKEM512_PKE_DECRYPT_EXEC =
  MLKEM_NATIVE2_IMAGE_EXEC ["mlkem512_pke_decrypt"];;

let MLKEM512_PKE_DECRYPT_SUBROUTINE_CORRECT = prove
 (`!mp ct sk (c:byte list) (dk:byte list) pc stackpointer returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + mlkem_native2_image_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH c = 768 /\ LENGTH dk = 768 /\
     PAIRWISE nonoverlapping
      [(mp,32); (word_sub stackpointer (word 3744),3744)] /\
     ALLPAIRS nonoverlapping
      [(mp,32); (word_sub stackpointer (word 3744),3744)]
      [(word pc,mlkem_native2_image_size); (ct,768); (sk,768)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem512_pke_decrypt) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [mp; ct; sk] s /\
               read (memory :> bytes(ct,768)) s = num_of_bytelist c /\
               read (memory :> bytes(sk,768)) s = num_of_bytelist dk)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(mp,32)) s =
               num_of_bytelist(kpke_decrypt mlkem512 dk c))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(mp,32);
                      memory :> bytes(word_sub stackpointer (word 3744),
                                      3744)])`,
  MLKEM_NATIVE2_PKE_DECRYPT_CORRECT_TAC 2 MLKEM512_PKE_DECRYPT_EXEC);;

(* ------------------------------------------------------------------------- *)
(* ML-KEM.KeyGen_internal (FIPS 203 Algorithm 16) with coins = d || z: the   *)
(* encapsulation key at pk, the decapsulation key at sk and the return value *)
(* 0.                                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM512_KEYPAIR_DERAND_EXEC =
  MLKEM_NATIVE2_IMAGE_EXEC ["mlkem512_keypair_derand"];;

let MLKEM512_KEYPAIR_DERAND_SUBROUTINE_CORRECT = prove
 (`!pk sk coins (d:byte list) (z:byte list) pc stackpointer returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + mlkem_native2_image_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH d = 32 /\ LENGTH z = 32 /\
     PAIRWISE nonoverlapping
      [(pk,800); (sk,1632); (word_sub stackpointer (word 9200),9200)] /\
     ALLPAIRS nonoverlapping
      [(pk,800); (sk,1632); (word_sub stackpointer (word 9200),9200)]
      [(coins,64); (word pc,mlkem_native2_image_size)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem512_keypair_derand) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [pk; sk; coins] s /\
               read (memory :> bytes(coins,32)) s = num_of_bytelist d /\
               read (memory :> bytes(word_add coins (word 32),32)) s =
               num_of_bytelist z)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(pk,800)) s =
               num_of_bytelist(FST(mlkem_keygen_internal mlkem512 d z)) /\
               read (memory :> bytes(sk,1632)) s =
               num_of_bytelist(SND(mlkem_keygen_internal mlkem512 d z)) /\
               C_RETURN s = word 0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(pk,800); memory :> bytes(sk,1632);
                      memory :> bytes(word_sub stackpointer (word 9200),
                                      9200)])`,
  MLKEM_NATIVE2_KEYPAIR_DERAND_CORRECT_TAC 2 MLKEM512_KEYPAIR_DERAND_EXEC
   MLKEM_GEN_MATRIX_K2_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* ML-KEM.Encaps_internal (FIPS 203 Algorithm 17) with coins = m, after the  *)
(* modulus check of the encapsulation key (FIPS 203 section 7.2): if the     *)
(* check passes, the shared secret at ss, the ciphertext at ct and the       *)
(* return value 0, else -4 (MLK_ERR_INVALID_PK).                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM512_ENC_DERAND_EXEC =
  MLKEM_NATIVE2_IMAGE_EXEC ["mlkem512_enc_derand"];;

let MLKEM512_ENC_DERAND_SUBROUTINE_CORRECT = prove
 (`!ct ss pk coins (ek:byte list) (m:byte list) pc stackpointer
    returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + mlkem_native2_image_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH ek = 800 /\ LENGTH m = 32 /\
     nonoverlapping (pk,800) (word pc,mlkem_native2_image_size) /\
     PAIRWISE nonoverlapping
      [(ct,768); (ss,32); (word_sub stackpointer (word 8640),8640)] /\
     ALLPAIRS nonoverlapping
      [(ct,768); (ss,32); (word_sub stackpointer (word 8640),8640)]
      [(pk,800); (coins,32); (word pc,mlkem_native2_image_size)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem512_enc_derand) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [ct; ss; pk; coins] s /\
               read (memory :> bytes(pk,800)) s = num_of_bytelist ek /\
               read (memory :> bytes(coins,32)) s = num_of_bytelist m)
          (\s. read PC s = returnaddress /\
               (mlkem_ek_check mlkem512 ek
                ==> read (memory :> bytes(ss,32)) s =
                    num_of_bytelist
                     (FST(mlkem_encaps_internal mlkem512 ek m)) /\
                    read (memory :> bytes(ct,768)) s =
                    num_of_bytelist
                     (SND(mlkem_encaps_internal mlkem512 ek m))) /\
               C_RETURN s =
               (if mlkem_ek_check mlkem512 ek then word 0
                else word 0xfffffffc))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(ct,768); memory :> bytes(ss,32);
                      memory :> bytes(word_sub stackpointer (word 8640),
                                      8640)])`,
  MLKEM_NATIVE2_ENC_DERAND_CORRECT_TAC 2 MLKEM512_ENC_DERAND_EXEC
   MLKEM_GEN_MATRIX_K2_TRANSPOSED_SUBROUTINE_CORRECT
   MLKEM512_PKE_ENCRYPT_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* ML-KEM.Decaps_internal (FIPS 203 Algorithm 18), after the hash check of   *)
(* the decapsulation key (FIPS 203 section 7.3): if the check passes, the    *)
(* shared secret at ss and the return value 0, else -5 (MLK_ERR_INVALID_SK). *)
(* ------------------------------------------------------------------------- *)

let MLKEM512_DEC_EXEC = MLKEM_NATIVE2_IMAGE_EXEC ["mlkem512_dec"];;

let MLKEM512_DEC_SUBROUTINE_CORRECT = prove
 (`!ss ct sk (dk:byte list) (c:byte list) pc stackpointer returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + mlkem_native2_image_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH dk = 1632 /\ LENGTH c = 768 /\
     nonoverlapping (ct,768) (word pc,mlkem_native2_image_size) /\
     nonoverlapping (sk,1632) (word pc,mlkem_native2_image_size) /\
     nonoverlapping (ss,32) (word_sub stackpointer (word 10304),10304) /\
     ALLPAIRS nonoverlapping
      [(ss,32); (word_sub stackpointer (word 10304),10304)]
      [(ct,768); (sk,1632); (word pc,mlkem_native2_image_size)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem512_dec) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [ss; ct; sk] s /\
               read (memory :> bytes(ct,768)) s = num_of_bytelist c /\
               read (memory :> bytes(sk,1632)) s = num_of_bytelist dk)
          (\s. read PC s = returnaddress /\
               (mlkem_decaps_check mlkem512 dk c
                ==> read (memory :> bytes(ss,32)) s =
                    num_of_bytelist(mlkem_decaps_internal mlkem512 dk c)) /\
               C_RETURN s =
               (if mlkem_decaps_check mlkem512 dk c then word 0
                else word 0xfffffffb))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(ss,32);
                      memory :> bytes(word_sub stackpointer (word 10304),
                                      10304)])`,
  MLKEM_NATIVE2_DEC_CORRECT_TAC 2 MLKEM512_DEC_EXEC
   MLKEM_GEN_MATRIX_K2_HASHES_SUBROUTINE_CORRECT
   (MLKEM512_PKE_DECRYPT_SUBROUTINE_CORRECT,
    MLKEM512_PKE_ENCRYPT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of the K-PKE encryption: the events   *)
(* depend only on the addresses.                                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM512_PKE_ENCRYPT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e ct at pk mp noise pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\
       pc + mlkem_native2_image_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [(ct,768); (noise,2560); (word_sub stackpointer (word 3744),3744)] /\
       ALLPAIRS nonoverlapping
        [(ct,768); (noise,2560); (word_sub stackpointer (word 3744),3744)]
        [(word pc,mlkem_native2_image_size); (at,2048); (pk,800); (mp,32)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem512_pke_encrypt) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [ct; at; pk; mp; noise] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events ct at pk mp noise pc
                           (word_sub stackpointer (word 3744)) returnaddress /\
                    memaccess_inbounds e2
                     [ct,768; at,2048; pk,800; mp,32; noise,2560;
                      word(pc + mlkem_native2_constants),6656;
                      word_sub stackpointer (word 3744),3744]
                     [ct,768; noise,2560;
                      word_sub stackpointer (word 3744),3744]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(ct,768); memory :> bytes(noise,2560);
                        memory :> bytes(word_sub stackpointer (word 3744),
                                        3744)])`,
  MLKEM_NATIVE2_PKE_ENCRYPT_SAFE_TAC 2 MLKEM512_PKE_ENCRYPT_EXEC);;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of the K-PKE decryption: the events   *)
(* depend only on the addresses.                                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM512_PKE_DECRYPT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e mp ct sk pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\
       pc + mlkem_native2_image_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [(mp,32); (word_sub stackpointer (word 3744),3744)] /\
       ALLPAIRS nonoverlapping
        [(mp,32); (word_sub stackpointer (word 3744),3744)]
        [(word pc,mlkem_native2_image_size); (ct,768); (sk,768)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem512_pke_decrypt) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [mp; ct; sk] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events mp ct sk pc
                           (word_sub stackpointer (word 3744)) returnaddress /\
                    memaccess_inbounds e2
                     [mp,32; ct,768; sk,768;
                      word(pc + mlkem_native2_constants),6656;
                      word_sub stackpointer (word 3744),3744]
                     [mp,32; word_sub stackpointer (word 3744),3744]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(mp,32);
                        memory :> bytes(word_sub stackpointer (word 3744),
                                        3744)])`,
  MLKEM_NATIVE2_PKE_DECRYPT_SAFE_TAC 2 MLKEM512_PKE_DECRYPT_EXEC);;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of key generation: the events depend  *)
(* only on the addresses and on rho, which is public although computed from  *)
(* d (rho is at the end of pk). As in the proofs of the compiled C, the      *)
(* postcondition also gives rho in pk and the return value.                  *)
(* ------------------------------------------------------------------------- *)

let MLKEM512_KEYPAIR_DERAND_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e pk sk coins (d:byte list) pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\
       pc + mlkem_native2_image_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ LENGTH d = 32 /\
       PAIRWISE nonoverlapping
        [(pk,800); (sk,1632); (word_sub stackpointer (word 9200),9200)] /\
       ALLPAIRS nonoverlapping
        [(pk,800); (sk,1632); (word_sub stackpointer (word 9200),9200)]
        [(coins,64); (word pc,mlkem_native2_image_size)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem512_keypair_derand) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [pk; sk; coins] s /\
                 read (memory :> bytes(coins,32)) s = num_of_bytelist d /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 C_RETURN s = word 0 /\
                 read (memory :> bytes(word_add pk (word 768),32)) s =
                 num_of_bytelist(FST(mlkem_g(APPEND d [word 2]))) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events pk sk coins pc
                           (word_sub stackpointer (word 9200)) returnaddress
                           (FST(mlkem_g(APPEND d [word 2]))) /\
                    memaccess_inbounds e2
                     [coins,64; pk,800; sk,1632;
                      word(pc + mlkem_native2_constants),6656;
                      word_sub stackpointer (word 9200),9200]
                     [pk,800; sk,1632;
                      word_sub stackpointer (word 9200),9200]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(pk,800); memory :> bytes(sk,1632);
                        memory :> bytes(word_sub stackpointer (word 9200),
                                        9200)])`,
  MLKEM_NATIVE2_KEYPAIR_DERAND_SAFE_TAC 2 MLKEM512_KEYPAIR_DERAND_EXEC
   MLKEM_GEN_MATRIX_K2_SUBROUTINE_SAFE);;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of encapsulation: the events depend   *)
(* only on the addresses and on ek, which is public, and on whether it       *)
(* passes the modulus check. As in the proofs of the compiled C, the         *)
(* postcondition also gives the return value.                                *)
(* ------------------------------------------------------------------------- *)

let MLKEM512_ENC_DERAND_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e ct ss pk coins (ek:byte list) pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\
       pc + mlkem_native2_image_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ LENGTH ek = 800 /\
       nonoverlapping (pk,800) (word pc,mlkem_native2_image_size) /\
       PAIRWISE nonoverlapping
        [(ct,768); (ss,32); (word_sub stackpointer (word 8640),8640)] /\
       ALLPAIRS nonoverlapping
        [(ct,768); (ss,32); (word_sub stackpointer (word 8640),8640)]
        [(pk,800); (coins,32); (word pc,mlkem_native2_image_size)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem512_enc_derand) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [ct; ss; pk; coins] s /\
                 read (memory :> bytes(pk,800)) s = num_of_bytelist ek /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 C_RETURN s =
                 (if mlkem_ek_check mlkem512 ek then word 0
                  else word 0xfffffffc) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events ct ss pk coins pc
                           (word_sub stackpointer (word 8640))
                           returnaddress ek /\
                    memaccess_inbounds e2
                     [pk,800; coins,32; ct,768; ss,32;
                      word(pc + mlkem_native2_constants),6656;
                      word_sub stackpointer (word 8640),8640]
                     [ct,768; ss,32;
                      word_sub stackpointer (word 8640),8640]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(ct,768); memory :> bytes(ss,32);
                        memory :> bytes(word_sub stackpointer (word 8640),
                                        8640)])`,
  MLKEM_NATIVE2_ENC_DERAND_SAFE_TAC 2 MLKEM512_ENC_DERAND_EXEC
   MLKEM_GEN_MATRIX_K2_TRANSPOSED_SUBROUTINE_SAFE
   MLKEM512_PKE_ENCRYPT_SUBROUTINE_SAFE);;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of decapsulation: the events depend   *)
(* only on the addresses and on ek and h in dk, which are public, and on     *)
(* whether h = H(ek) (the hash check). As in the proofs of the compiled C,   *)
(* there are no results in the postcondition.                                *)
(* ------------------------------------------------------------------------- *)

let MLKEM512_DEC_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e ss ct sk (dk:byte list) pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\
       pc + mlkem_native2_image_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ LENGTH dk = 1632 /\
       nonoverlapping (ct,768) (word pc,mlkem_native2_image_size) /\
       nonoverlapping (sk,1632) (word pc,mlkem_native2_image_size) /\
       nonoverlapping (ss,32) (word_sub stackpointer (word 10304),10304) /\
       ALLPAIRS nonoverlapping
        [(ss,32); (word_sub stackpointer (word 10304),10304)]
        [(ct,768); (sk,1632); (word pc,mlkem_native2_image_size)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem512_dec) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [ss; ct; sk] s /\
                 read (memory :> bytes(sk,1632)) s = num_of_bytelist dk /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events ss ct sk pc
                           (word_sub stackpointer (word 10304)) returnaddress
                           (mlkem_slice 768 800 dk)
                           (mlkem_slice 1568 32 dk) /\
                    memaccess_inbounds e2
                     [ct,768; sk,1632; ss,32;
                      word(pc + mlkem_native2_constants),6656;
                      word_sub stackpointer (word 10304),10304]
                     [ss,32; word_sub stackpointer (word 10304),10304]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(ss,32);
                        memory :> bytes(word_sub stackpointer (word 10304),
                                        10304)])`,
  MLKEM_NATIVE2_DEC_SAFE_TAC 2 MLKEM512_DEC_EXEC
   MLKEM_GEN_MATRIX_K2_HASHES_SUBROUTINE_SAFE
   (MLKEM512_PKE_DECRYPT_SUBROUTINE_SAFE,
    MLKEM512_PKE_ENCRYPT_SUBROUTINE_SAFE));;
