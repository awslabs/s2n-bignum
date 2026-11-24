(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The hash G of ML-KEM, SHA3-512 of FIPS 202, with the x1 Keccak          *)
(* permutation sha3_keccak_f1600, in the image of the ML-KEM API in        *)
(* assembly: the theorems of correctness and of constant-time and memory   *)
(* safety of mlkem_hash_g that its callers use, and its correctness and    *)
(* safety in one for messages of less than 72 bytes. The proofs are in     *)
(* hash_g_proof.ml.                                                        *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/asm/layout.ml";;
needs "arm/proofs/mlkem_native/asm/keccak_f1600_spec.ml";;
needs "common/fips202/fips202.ml";;

let MLKEM_NATIVE_HASH_G_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!out inp (m:byte list) c pc stackpointer returnaddress.
     aligned 16 stackpointer /\
     ALL (nonoverlapping (word_sub stackpointer (word 384),384))
         [(word pc,mlkem_native2_image_size); (out,64); (inp,LENGTH m);
          (c,192)] /\
     nonoverlapping (out,64) (word pc,mlkem_native2_image_size)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem_hash_g) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [out; inp; word(LENGTH m); c] s /\
               read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
               wordlist_from_memory(c,24) s = round_constants)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(out,64)) s = num_of_bytelist(sha3_512 m))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out,64);
                      memory :> bytes(word_sub stackpointer (word 384),384)])`;;

let MLKEM_NATIVE_HASH_G_ASM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_HASH_G_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_HASH_G_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e out inp len c pc stackpointer returnaddress.
       aligned 16 stackpointer /\
       ALL (nonoverlapping (word_sub stackpointer (word 384),384))
           [(word pc,mlkem_native2_image_size); (out,64); (inp,len);
            (c,192)] /\
       nonoverlapping (out,64) (word pc,mlkem_native2_image_size)
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem_hash_g) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; inp; word len; c] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events inp len c out pc
                           (word_sub stackpointer (word 384)) returnaddress /\
                    memaccess_inbounds e2
                     [inp,len; c,192; out,64;
                      word_sub stackpointer (word 384),384]
                     [out,64; word_sub stackpointer (word 384),384]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(out,64);
               memory :> bytes(word_sub stackpointer (word 384),384)])`;;

let MLKEM_NATIVE_HASH_G_ASM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_HASH_G_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;

let MLKEM_NATIVE_HASH_G_SHORT_ASM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e out inp (m:byte list) len c pc stackpointer returnaddress.
       aligned 16 stackpointer /\ LENGTH m = len /\ len < 72 /\
       ALL (nonoverlapping (word_sub stackpointer (word 384),384))
           [(word pc,mlkem_native2_image_size); (out,64); (inp,len);
            (c,192)] /\
       nonoverlapping (out,64) (word pc,mlkem_native2_image_size)
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem_hash_g) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; inp; word len; c] s /\
                 read (memory :> bytes(inp,len)) s = num_of_bytelist m /\
                 wordlist_from_memory(c,24) s = round_constants /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> bytes(out,64)) s =
                 num_of_bytelist(sha3_512 m) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events inp len c out pc
                           (word_sub stackpointer (word 384)) returnaddress /\
                    memaccess_inbounds e2
                     [inp,len; c,192; out,64;
                      word_sub stackpointer (word 384),384]
                     [out,64; word_sub stackpointer (word 384),384]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(out,64);
               memory :> bytes(word_sub stackpointer (word 384),384)])`;;

let MLKEM_NATIVE_HASH_G_SHORT_ASM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_HASH_G_SHORT_ASM_IMAGE_SUBROUTINE_FULL_STMT;;
