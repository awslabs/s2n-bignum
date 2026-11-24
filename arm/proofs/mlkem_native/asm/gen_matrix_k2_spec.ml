(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The correctness of mlkem_gen_matrix                                     *)
(* (arm/mlkem_native/asm/mlkem_gen_matrix.S) in the image for k = 2, in    *)
(* the configurations that the API uses. The code and the parts of the     *)
(* proofs are in gen_matrix_common_spec.ml.                                *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/asm/layout.ml";;
needs "arm/proofs/mlkem_native/asm/getnoise_spec.ml";;
needs "arm/proofs/mlkem_native/asm/keccak_f1600_spec.ml";;
needs "arm/proofs/mlkem_native/asm/keccak4_f1600_alt2_spec.ml";;
needs "arm/proofs/mlkem_native/asm/cbd2_spec.ml";;
needs "arm/proofs/mlkem_native/asm/rej_uniform_alt_variable_time_spec.ml";;
needs "arm/proofs/utils/mlkem_native_fips203.ml";;



(* ------------------------------------------------------------------------- *)
(* Correctness for the configurations used by the API. The matrix polynomial *)
(* a[i][j] is SampleNTT(rho || j || i), or SampleNTT(rho || i || j) when     *)
(* transposed; the digest of a job with ds = 6 is SHA3-256 of its message    *)
(* and with ds = 0x1f the first 32 bytes of SHAKE256 of it; noise polynomial *)
(* i (with nonce0 = 0) has the coefficients of SamplePolyCBD_2(PRF_2(seed,   *)
(* i)). The stack is the frame of 3088 bytes and 224 below it for            *)
(* sha3_keccak4_f1600_alt2, or 1952 when mlkem_getnoise is called. A job     *)
(* that is not used has ds = 0, and its other fields and the pointers not    *)
(* used (jobs, noise) are arbitrary.                                         *)
(* ------------------------------------------------------------------------- *)

(* k = 2, not transposed, with no hash jobs and no noise (key generation of  *)
(* ML-KEM-512).                                                              *)
let MLKEM_NATIVE_GEN_MATRIX_K2_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a rhop (rho:byte list) jobs noise c pc stackpointer returnaddress.
     aligned 16 stackpointer /\ LENGTH rho = 32 /\
     (!i j. i < 2 /\ j < 2
            ==> mlkem_samplentt_terminates (APPEND rho [word j; word i])) /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 3312),3312); (a,2048)] /\
     ALLPAIRS nonoverlapping
      [(word_sub stackpointer (word 3312),3312); (a,2048)]
      [(word pc,mlkem_native2_image_size); (rhop,32); (c,6656)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem_gen_matrix) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [a; rhop; word 2; word 0; jobs; noise; c] s /\
               read (memory :> bytes(rhop,32)) s = num_of_bytelist rho /\
               read (memory :> bytes(c,192)) s =
               num_of_wordlist round_constants /\
               read (memory :> bytes(word_add c (word 2560),4096)) s =
               num_of_wordlist mlkem_rej_uniform_table)
          (\s. read PC s = returnaddress /\
               (!i j t. i < 2 /\ j < 2 /\ t < 256
                        ==> read(memory :> bytes16(word_add a
                                 (word(512 * (2 * i + j) + 2 * t)))) s =
                            iword(mlkem_sample_ntt
                                   (APPEND rho [word j; word i]) t)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,2048);
                      memory :> bytes(word_sub stackpointer
                                       (word 3312),3312)])`;;

let MLKEM_NATIVE_GEN_MATRIX_K2_ASM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_GEN_MATRIX_K2_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;



(* k = 2, transposed, with no hash jobs and no noise (encapsulation of       *)
(* ML-KEM-512).                                                              *)
let MLKEM_NATIVE_GEN_MATRIX_K2_TRANSPOSED_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a rhop (rho:byte list) jobs noise c pc stackpointer returnaddress.
     aligned 16 stackpointer /\ LENGTH rho = 32 /\
     (!i j. i < 2 /\ j < 2
            ==> mlkem_samplentt_terminates (APPEND rho [word i; word j])) /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 3312),3312); (a,2048)] /\
     ALLPAIRS nonoverlapping
      [(word_sub stackpointer (word 3312),3312); (a,2048)]
      [(word pc,mlkem_native2_image_size); (rhop,32); (c,6656)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem_gen_matrix) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [a; rhop; word 2; word 1; jobs; noise; c] s /\
               read (memory :> bytes(rhop,32)) s = num_of_bytelist rho /\
               read (memory :> bytes(c,192)) s =
               num_of_wordlist round_constants /\
               read (memory :> bytes(word_add c (word 2560),4096)) s =
               num_of_wordlist mlkem_rej_uniform_table)
          (\s. read PC s = returnaddress /\
               (!i j t. i < 2 /\ j < 2 /\ t < 256
                        ==> read(memory :> bytes16(word_add a
                                 (word(512 * (2 * i + j) + 2 * t)))) s =
                            iword(mlkem_sample_ntt
                                   (APPEND rho [word i; word j]) t)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,2048);
                      memory :> bytes(word_sub stackpointer
                                       (word 3312),3312)])`;;

let MLKEM_NATIVE_GEN_MATRIX_K2_TRANSPOSED_ASM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_GEN_MATRIX_K2_TRANSPOSED_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;



(* k = 2, transposed, with H(ek) for the 800 bytes of ek as job 0 and J(z || *)
(* c) for the 800 bytes of z || c as job 1, and no noise (decapsulation of   *)
(* ML-KEM-512).                                                              *)
let MLKEM_NATIVE_GEN_MATRIX_K2_HASHES_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a rhop (rho:byte list) jobs msg0 (m0:byte list) out0 msg1 (m1:byte list)
    out1 noise c pc stackpointer returnaddress.
     aligned 16 stackpointer /\ LENGTH rho = 32 /\ LENGTH m0 = 800 /\
     LENGTH m1 = 800 /\
     (!i j. i < 2 /\ j < 2
            ==> mlkem_samplentt_terminates (APPEND rho [word i; word j])) /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 3312),3312); (a,2048); (out0,32);
       (out1,32)] /\
     ALLPAIRS nonoverlapping
      [(word_sub stackpointer (word 3312),3312); (a,2048); (out0,32);
       (out1,32)]
      [(word pc,mlkem_native2_image_size); (rhop,32); (jobs,64); (msg0,800);
       (msg1,800); (c,6656)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem_gen_matrix) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [a; rhop; word 2; word 3; jobs; noise; c] s /\
               read (memory :> bytes(rhop,32)) s = num_of_bytelist rho /\
               read (memory :> bytes64 jobs) s = msg0 /\
               read (memory :> bytes64 (word_add jobs (word 8))) s =
               word 800 /\
               read (memory :> bytes64 (word_add jobs (word 16))) s = word 6 /\
               read (memory :> bytes64 (word_add jobs (word 24))) s = out0 /\
               read (memory :> bytes(msg0,800)) s = num_of_bytelist m0 /\
               read (memory :> bytes64 (word_add jobs (word 32))) s = msg1 /\
               read (memory :> bytes64 (word_add jobs (word 40))) s =
               word 800 /\
               read (memory :> bytes64 (word_add jobs (word 48))) s =
               word 31 /\
               read (memory :> bytes64 (word_add jobs (word 56))) s = out1 /\
               read (memory :> bytes(msg1,800)) s = num_of_bytelist m1 /\
               read (memory :> bytes(c,192)) s =
               num_of_wordlist round_constants /\
               read (memory :> bytes(word_add c (word 2560),4096)) s =
               num_of_wordlist mlkem_rej_uniform_table)
          (\s. read PC s = returnaddress /\
               (!i j t. i < 2 /\ j < 2 /\ t < 256
                        ==> read(memory :> bytes16(word_add a
                                 (word(512 * (2 * i + j) + 2 * t)))) s =
                            iword(mlkem_sample_ntt
                                   (APPEND rho [word i; word j]) t)) /\
               read (memory :> bytes(out0,32)) s =
               num_of_bytelist(sha3_256 m0) /\
               read (memory :> bytes(out1,32)) s =
               num_of_bytelist(list_of_seq (shake256 m1) 32))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,2048); memory :> bytes(out0,32);
                      memory :> bytes(out1,32);
                      memory :> bytes(word_sub stackpointer
                                       (word 3312),3312)])`;;

let MLKEM_NATIVE_GEN_MATRIX_K2_HASHES_ASM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_GEN_MATRIX_K2_HASHES_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;
