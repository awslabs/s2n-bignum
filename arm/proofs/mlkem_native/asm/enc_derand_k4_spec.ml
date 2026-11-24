(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of the function mlkem1024_enc_derand of ML-KEM-1024       *)
(* (arm/mlkem_native/asm/mlkem1024.S) in the image of the ML-KEM API in    *)
(* assembly: encapsulation, its correctness and its constant-time and      *)
(* memory safety, stated as in the proofs of the compiled C of mlkem-      *)
(* native (see arm/mlkem_native/asm/README.md). The proofs are in          *)
(* enc_derand_k4_proof.ml.                                                 *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/asm/layout.ml";;
needs "arm/proofs/mlkem_native/asm/check_encoding_spec.ml";;
needs "arm/proofs/mlkem_native/asm/hash_h_spec.ml";;
needs "arm/proofs/mlkem_native/asm/hash_g_spec.ml";;
needs "arm/proofs/mlkem_native/asm/getnoise_spec.ml";;
needs "arm/proofs/mlkem_native/asm/gen_matrix_k4_spec.ml";;
needs "arm/proofs/mlkem_native/asm/gen_matrix_k4_safe_spec.ml";;
needs "arm/proofs/mlkem_native/asm/pke_encrypt_k4_spec.ml";;
needs "common/fips203/fips203.ml";;
needs "arm/proofs/utils/mlkem_native2_cbd.ml";;
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(* ------------------------------------------------------------------------- *)
(* ML-KEM.Encaps_internal (FIPS 203 Algorithm 17) with coins = m, after the  *)
(* modulus check of the encapsulation key (FIPS 203 section 7.2): if the     *)
(* check passes, the shared secret at ss, the ciphertext at ct and the       *)
(* return value 0, else -4 (MLK_ERR_INVALID_PK).                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_ENC_DERAND_K4_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!ct ss pk coins (ek:byte list) (m:byte list) pc stackpointer
    returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + mlkem_native2_image_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH ek = 1568 /\ LENGTH m = 32 /\
     nonoverlapping (pk,1568) (word pc,mlkem_native2_image_size) /\
     PAIRWISE nonoverlapping
      [(ct,1568); (ss,32); (word_sub stackpointer (word 19392),19392)] /\
     ALLPAIRS nonoverlapping
      [(ct,1568); (ss,32); (word_sub stackpointer (word 19392),19392)]
      [(pk,1568); (coins,32); (word pc,mlkem_native2_image_size)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem1024_enc_derand) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [ct; ss; pk; coins] s /\
               read (memory :> bytes(pk,1568)) s = num_of_bytelist ek /\
               read (memory :> bytes(coins,32)) s = num_of_bytelist m)
          (\s. read PC s = returnaddress /\
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
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(ct,1568); memory :> bytes(ss,32);
                      memory :> bytes(word_sub stackpointer (word 19392),
                                      19392)])`;;

let MLKEM_NATIVE_ENC_DERAND_K4_ASM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_ENC_DERAND_K4_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of encapsulation: the events depend   *)
(* only on the addresses and on ek, which is public, and on whether it       *)
(* passes the modulus check. As in the proofs of the compiled C, the         *)
(* postcondition also gives the return value.                                *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_ENC_DERAND_K4_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e ct ss pk coins (ek:byte list) pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\
       pc + mlkem_native2_image_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ LENGTH ek = 1568 /\
       nonoverlapping (pk,1568) (word pc,mlkem_native2_image_size) /\
       PAIRWISE nonoverlapping
        [(ct,1568); (ss,32); (word_sub stackpointer (word 19392),19392)] /\
       ALLPAIRS nonoverlapping
        [(ct,1568); (ss,32); (word_sub stackpointer (word 19392),19392)]
        [(pk,1568); (coins,32); (word pc,mlkem_native2_image_size)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem1024_enc_derand) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [ct; ss; pk; coins] s /\
                 read (memory :> bytes(pk,1568)) s = num_of_bytelist ek /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 C_RETURN s =
                 (if mlkem_ek_check mlkem1024 ek then word 0
                  else word 0xfffffffc) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events ct ss pk coins pc
                           (word_sub stackpointer (word 19392))
                           returnaddress ek /\
                    memaccess_inbounds e2
                     [pk,1568; coins,32; ct,1568; ss,32;
                      word(pc + mlkem_native2_constants),6656;
                      word_sub stackpointer (word 19392),19392]
                     [ct,1568; ss,32;
                      word_sub stackpointer (word 19392),19392]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(ct,1568); memory :> bytes(ss,32);
                        memory :> bytes(word_sub stackpointer (word 19392),
                                        19392)])`;;

let MLKEM_NATIVE_ENC_DERAND_K4_ASM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_ENC_DERAND_K4_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;
