(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The noise sampling of ML-KEM, SamplePolyCBD_eta(PRF_eta(sigma, b)) of   *)
(* FIPS 203 for n consecutive nonces b, in the lanes of the x4 Keccak      *)
(* permutation, in the image of the ML-KEM API in assembly, for the        *)
(* configurations used by the API functions: the theorems of correctness   *)
(* and of constant-time and memory safety of mlkem_getnoise that its       *)
(* callers use. The proofs are in getnoise_proof.ml.                       *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/asm/layout.ml";;
needs "arm/proofs/mlkem_native/asm/keccak4_f1600_alt2_spec.ml";;
needs "arm/proofs/mlkem_native/asm/keccak_f1600_spec.ml";;
needs "arm/proofs/mlkem_native/asm/cbd2_spec.ml";;
needs "arm/proofs/mlkem_native/asm/cbd3_spec.ml";;
needs "arm/proofs/utils/mlkem_native2_cbd.ml";;
needs "common/fips203/fips203.ml";;

let MLKEM_NATIVE_GETNOISE_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r sigma (seed:byte list) nonce0 n n1 eta1 c pc stackpointer returnaddress.
     (eta1 = 2 /\ n = 4 \/ eta1 = 2 /\ n = 7 \/ eta1 = 2 /\ n = 8 \/
      eta1 = 2 /\ n = 9 \/ eta1 = 3 /\ n = 4 /\ n1 = 4 \/
      eta1 = 3 /\ n = 5 /\ n1 = 2) /\
     aligned 16 stackpointer /\ LENGTH seed = 32 /\
     ALL (nonoverlapping (word_sub stackpointer (word 1952),1952))
         [(word pc,mlkem_native2_image_size); (r,512 * n); (sigma,32);
          (c,192)] /\
     ALL (nonoverlapping (r,512 * n))
         [(word pc,mlkem_native2_image_size); (sigma,32); (c,192)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem_getnoise) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [r; sigma; word nonce0; word n; word n1; word eta1;
                            c] s /\
               read (memory :> bytes(sigma,32)) s = num_of_bytelist seed /\
               wordlist_from_memory(c,24) s = round_constants)
          (\s. read PC s = returnaddress /\
               !i j. i < n /\ j < 256
                     ==> read(memory :> bytes16(word_add r
                                                  (word(512 * i + 2 * j)))) s =
                         iword(mlkem_cbd_coeff (if i < n1 then eta1 else 2)
                                (mlkem_prf (if i < n1 then eta1 else 2) seed
                                           (word(nonce0 + i))) j))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE
            [memory :> bytes(r,512 * n);
             memory :> bytes(word_sub stackpointer (word 1952),1952)])`;;

let MLKEM_NATIVE_GETNOISE_ASM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_GETNOISE_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_GETNOISE_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r sigma nonce0 n n1 eta1 c pc stackpointer returnaddress.
       (eta1 = 2 /\ n = 4 \/ eta1 = 2 /\ n = 7 \/ eta1 = 2 /\ n = 8 \/
        eta1 = 2 /\ n = 9 \/ eta1 = 3 /\ n = 4 /\ n1 = 4 \/
        eta1 = 3 /\ n = 5 /\ n1 = 2) /\
       aligned 16 stackpointer /\
       ALL (nonoverlapping (word_sub stackpointer (word 1952),1952))
           [(word pc,mlkem_native2_image_size); (r,512 * n); (sigma,32);
            (c,192)] /\
       ALL (nonoverlapping (r,512 * n))
           [(word pc,mlkem_native2_image_size); (sigma,32); (c,192)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem_getnoise) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [r; sigma; word nonce0; word n; word n1;
                              word eta1; c] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events r sigma n eta1 c pc
                                  (word_sub stackpointer (word 1952))
                                  returnaddress /\
                    memaccess_inbounds e2
                     [r,512 * n; sigma,32; c,192;
                      word_sub stackpointer (word 1952),1952]
                     [r,512 * n; word_sub stackpointer (word 1952),1952]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,512 * n);
                        memory :> bytes(word_sub stackpointer (word 1952),
                                        1952)])`;;

let MLKEM_NATIVE_GETNOISE_ASM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_GETNOISE_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;
