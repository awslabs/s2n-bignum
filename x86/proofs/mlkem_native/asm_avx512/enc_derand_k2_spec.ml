(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The function mlkem512_enc_derand_avx512 of the build asm_avx512:          *)
(* encapsulation, with its correctness and its constant-time and memory      *)
(* safety.                                                                   *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/api_spec.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/kem_spec.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/gen_matrix_k2_spec.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/kem_safe_spec.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/gen_matrix_k2_safe_spec.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/pke_encrypt_k2_spec.ml";;



(* ------------------------------------------------------------------------- *)
(* ML-KEM.Encaps_internal (FIPS 203 Algorithm 17), after the modulus         *)
(* check of the encapsulation key (FIPS 203 section 7.2): if the check       *)
(* passes, the shared secret at ss, the ciphertext at ct and the return      *)
(* value 0, else -4 (MLK_ERR_INVALID_PK).                                    *)
(* ------------------------------------------------------------------------- *)

let MLKEM512_ENC_DERAND_AVX512_EXEC =
  MLKEM_NATIVE2_AVX512_IMAGE_EXEC ["mlkem512_enc_derand_avx512"];;



let MLKEM_NATIVE_ENC_DERAND_K2_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!ct ss pk coins (ek:byte list) (m:byte list) pc stackpointer
    returnaddress.
     aligned 32 (word pc:int64) /\ LENGTH ek = 800 /\ LENGTH m = 32 /\
     nonoverlapping (pk,800) (word pc,mlkem_native2_avx512_image_size) /\
     PAIRWISE nonoverlapping
      [(ct,768); (ss,32); (word_sub stackpointer (word 8806),8814)] /\
     ALLPAIRS nonoverlapping
      [(ct,768); (ss,32); (word_sub stackpointer (word 8806),8814)]
      [(pk,800); (coins,32); (word pc,mlkem_native2_avx512_image_size)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
               read RIP s = word(pc + mlkem512_enc_derand_avx512) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [ct; ss; pk; coins] s /\
               read (memory :> bytes(pk,800)) s = num_of_bytelist ek /\
               read (memory :> bytes(coins,32)) s = num_of_bytelist m)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
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
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(ct,768); memory :> bytes(ss,32);
                      memory :> bytes(word_sub stackpointer (word 8806),
                                      8806)])`;;

let MLKEM_NATIVE_ENC_DERAND_K2_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT = assume_spec MLKEM_NATIVE_ENC_DERAND_K2_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT_STMT;;



(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of encapsulation: the events          *)
(* depend only on the addresses and on ek, which is public, and on           *)
(* whether it passes the modulus check. As in the proofs of the              *)
(* compiled C, the postcondition also gives the return value.                *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_ENC_DERAND_K2_ASM_AVX512_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e ct ss pk coins (ek:byte list) pc stackpointer returnaddress.
       aligned 32 (word pc:int64) /\ LENGTH ek = 800 /\
       nonoverlapping (pk,800) (word pc,mlkem_native2_avx512_image_size) /\
       PAIRWISE nonoverlapping
        [(ct,768); (ss,32); (word_sub stackpointer (word 8806),8814)] /\
       ALLPAIRS nonoverlapping
        [(ct,768); (ss,32); (word_sub stackpointer (word 8806),8814)]
        [(pk,800); (coins,32); (word pc,mlkem_native2_avx512_image_size)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
                 read RIP s = word(pc + mlkem512_enc_derand_avx512) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [ct; ss; pk; coins] s /\
                 read (memory :> bytes(pk,800)) s = num_of_bytelist ek /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 C_RETURN s =
                 (if mlkem_ek_check mlkem512 ek then word 0
                  else word 0xfffffffc) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events ct ss pk coins pc
                           (word_sub stackpointer (word 8806))
                           returnaddress ek /\
                    memaccess_inbounds e2
                     [pk,800; coins,32; ct,768; ss,32;
                      word(pc + mlkem_native2_constants),6048;
                      word_sub stackpointer (word 8806),8814]
                     [ct,768; ss,32;
                      word_sub stackpointer (word 8806),8806]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(ct,768); memory :> bytes(ss,32);
                        memory :> bytes(word_sub stackpointer (word 8806),
                                        8806)])`;;

let MLKEM_NATIVE_ENC_DERAND_K2_ASM_AVX512_IMAGE_SUBROUTINE_SAFE = assume_spec MLKEM_NATIVE_ENC_DERAND_K2_ASM_AVX512_IMAGE_SUBROUTINE_SAFE_STMT;;
