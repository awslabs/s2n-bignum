(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The correctness of mlkem_gen_matrix                                     *)
(* (arm/mlkem_native/asm/mlkem_gen_matrix.S) in the image for k = 3, in    *)
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

(* k = 3, not transposed, with the 6 noise polynomials of key generation     *)
(* (ML-KEM-768), all sampled in lanes left idle by the matrix.               *)
let MLKEM_NATIVE_GEN_MATRIX_K3_NOISE_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a rhop (rho:byte list) noise sigma (seed:byte list) nout jobs c pc
    stackpointer returnaddress.
     aligned 16 stackpointer /\ LENGTH rho = 32 /\ LENGTH seed = 32 /\
     (!i j. i < 3 /\ j < 3
            ==> mlkem_samplentt_terminates (APPEND rho [word j; word i])) /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 3312),3312); (a,4608); (nout,3072)] /\
     ALLPAIRS nonoverlapping
      [(word_sub stackpointer (word 3312),3312); (a,4608); (nout,3072)]
      [(word pc,mlkem_native2_image_size); (rhop,32); (noise,32); (sigma,32);
       (c,6656)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem_gen_matrix) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [a; rhop; word 3; word 4; jobs; noise; c] s /\
               read (memory :> bytes(rhop,32)) s = num_of_bytelist rho /\
               read (memory :> bytes64 noise) s = sigma /\
               read (memory :> bytes64 (word_add noise (word 8))) s = word 0 /\
               read (memory :> bytes64 (word_add noise (word 16))) s =
               word 6 /\
               read (memory :> bytes64 (word_add noise (word 24))) s = nout /\
               read (memory :> bytes(sigma,32)) s = num_of_bytelist seed /\
               read (memory :> bytes(c,192)) s =
               num_of_wordlist round_constants /\
               read (memory :> bytes(word_add c (word 2560),4096)) s =
               num_of_wordlist mlkem_rej_uniform_table)
          (\s. read PC s = returnaddress /\
               (!i j t. i < 3 /\ j < 3 /\ t < 256
                        ==> read(memory :> bytes16(word_add a
                                 (word(512 * (3 * i + j) + 2 * t)))) s =
                            iword(mlkem_sample_ntt
                                   (APPEND rho [word j; word i]) t)) /\
               (!i t. i < 6 /\ t < 256
                      ==> read(memory :> bytes16(word_add nout
                                 (word(512 * i + 2 * t)))) s =
                          iword(mlkem_cbd_coeff 2
                                 (mlkem_prf 2 seed (word i)) t)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,4608); memory :> bytes(nout,3072);
                      memory :> bytes(word_sub stackpointer
                                       (word 3312),3312)])`;;

let MLKEM_NATIVE_GEN_MATRIX_K3_NOISE_ASM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_GEN_MATRIX_K3_NOISE_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;



(* k = 3, transposed, with H(pk) for the 1184 bytes of pk as job 1 and no    *)
(* noise (encapsulation of ML-KEM-768).                                      *)
let MLKEM_NATIVE_GEN_MATRIX_K3_HASH_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a rhop (rho:byte list) jobs msg0 len0 out0 msg1 (m1:byte list) out1 noise
    c pc stackpointer returnaddress.
     aligned 16 stackpointer /\ LENGTH rho = 32 /\ LENGTH m1 = 1184 /\
     (!i j. i < 3 /\ j < 3
            ==> mlkem_samplentt_terminates (APPEND rho [word i; word j])) /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 3312),3312); (a,4608); (out1,32)] /\
     ALLPAIRS nonoverlapping
      [(word_sub stackpointer (word 3312),3312); (a,4608); (out1,32)]
      [(word pc,mlkem_native2_image_size); (rhop,32); (jobs,64); (msg1,1184);
       (c,6656)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem_gen_matrix) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [a; rhop; word 3; word 3; jobs; noise; c] s /\
               read (memory :> bytes(rhop,32)) s = num_of_bytelist rho /\
               read (memory :> bytes64 jobs) s = msg0 /\
               read (memory :> bytes64 (word_add jobs (word 8))) s = len0 /\
               read (memory :> bytes64 (word_add jobs (word 16))) s = word 0 /\
               read (memory :> bytes64 (word_add jobs (word 24))) s = out0 /\
               read (memory :> bytes64 (word_add jobs (word 32))) s = msg1 /\
               read (memory :> bytes64 (word_add jobs (word 40))) s =
               word 1184 /\
               read (memory :> bytes64 (word_add jobs (word 48))) s = word 6 /\
               read (memory :> bytes64 (word_add jobs (word 56))) s = out1 /\
               read (memory :> bytes(msg1,1184)) s = num_of_bytelist m1 /\
               read (memory :> bytes(c,192)) s =
               num_of_wordlist round_constants /\
               read (memory :> bytes(word_add c (word 2560),4096)) s =
               num_of_wordlist mlkem_rej_uniform_table)
          (\s. read PC s = returnaddress /\
               (!i j t. i < 3 /\ j < 3 /\ t < 256
                        ==> read(memory :> bytes16(word_add a
                                 (word(512 * (3 * i + j) + 2 * t)))) s =
                            iword(mlkem_sample_ntt
                                   (APPEND rho [word i; word j]) t)) /\
               read (memory :> bytes(out1,32)) s =
               num_of_bytelist(sha3_256 m1))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,4608); memory :> bytes(out1,32);
                      memory :> bytes(word_sub stackpointer
                                       (word 3312),3312)])`;;

let MLKEM_NATIVE_GEN_MATRIX_K3_HASH_ASM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_GEN_MATRIX_K3_HASH_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;



(* k = 3, transposed, with H(ek) as job 0, J(z || c) for 1120 bytes as job 1 *)
(* and the 7 noise polynomials of the re-encryption (decapsulation of        *)
(* ML-KEM-768), the last 4 by mlkem_getnoise.                                *)
let MLKEM_NATIVE_GEN_MATRIX_K3_HASHES_NOISE_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a rhop (rho:byte list) jobs msg0 (m0:byte list) out0 msg1 (m1:byte list)
    out1 noise sigma (seed:byte list) nout c pc stackpointer returnaddress.
     aligned 16 stackpointer /\ LENGTH rho = 32 /\ LENGTH m0 = 1184 /\
     LENGTH m1 = 1120 /\ LENGTH seed = 32 /\
     (!i j. i < 3 /\ j < 3
            ==> mlkem_samplentt_terminates (APPEND rho [word i; word j])) /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 5040),5040); (a,4608); (out0,32);
       (out1,32); (nout,3584)] /\
     ALLPAIRS nonoverlapping
      [(word_sub stackpointer (word 5040),5040); (a,4608); (out0,32);
       (out1,32); (nout,3584)]
      [(word pc,mlkem_native2_image_size); (rhop,32); (jobs,64); (msg0,1184);
       (msg1,1120); (noise,32); (sigma,32); (c,6656)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem_gen_matrix) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [a; rhop; word 3; word 7; jobs; noise; c] s /\
               read (memory :> bytes(rhop,32)) s = num_of_bytelist rho /\
               read (memory :> bytes64 jobs) s = msg0 /\
               read (memory :> bytes64 (word_add jobs (word 8))) s =
               word 1184 /\
               read (memory :> bytes64 (word_add jobs (word 16))) s = word 6 /\
               read (memory :> bytes64 (word_add jobs (word 24))) s = out0 /\
               read (memory :> bytes(msg0,1184)) s = num_of_bytelist m0 /\
               read (memory :> bytes64 (word_add jobs (word 32))) s = msg1 /\
               read (memory :> bytes64 (word_add jobs (word 40))) s =
               word 1120 /\
               read (memory :> bytes64 (word_add jobs (word 48))) s =
               word 31 /\
               read (memory :> bytes64 (word_add jobs (word 56))) s = out1 /\
               read (memory :> bytes(msg1,1120)) s = num_of_bytelist m1 /\
               read (memory :> bytes64 noise) s = sigma /\
               read (memory :> bytes64 (word_add noise (word 8))) s = word 0 /\
               read (memory :> bytes64 (word_add noise (word 16))) s =
               word 7 /\
               read (memory :> bytes64 (word_add noise (word 24))) s = nout /\
               read (memory :> bytes(sigma,32)) s = num_of_bytelist seed /\
               read (memory :> bytes(c,192)) s =
               num_of_wordlist round_constants /\
               read (memory :> bytes(word_add c (word 2560),4096)) s =
               num_of_wordlist mlkem_rej_uniform_table)
          (\s. read PC s = returnaddress /\
               (!i j t. i < 3 /\ j < 3 /\ t < 256
                        ==> read(memory :> bytes16(word_add a
                                 (word(512 * (3 * i + j) + 2 * t)))) s =
                            iword(mlkem_sample_ntt
                                   (APPEND rho [word i; word j]) t)) /\
               read (memory :> bytes(out0,32)) s =
               num_of_bytelist(sha3_256 m0) /\
               read (memory :> bytes(out1,32)) s =
               num_of_bytelist(list_of_seq (shake256 m1) 32) /\
               (!i t. i < 7 /\ t < 256
                      ==> read(memory :> bytes16(word_add nout
                                 (word(512 * i + 2 * t)))) s =
                          iword(mlkem_cbd_coeff 2
                                 (mlkem_prf 2 seed (word i)) t)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,4608); memory :> bytes(out0,32);
                      memory :> bytes(out1,32); memory :> bytes(nout,3584);
                      memory :> bytes(word_sub stackpointer
                                       (word 5040),5040)])`;;

let MLKEM_NATIVE_GEN_MATRIX_K3_HASHES_NOISE_ASM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_GEN_MATRIX_K3_HASHES_NOISE_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;
