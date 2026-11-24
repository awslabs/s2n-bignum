(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The correctness of mlkem_gen_matrix_avx512                                *)
(* (x86/mlkem_native/asm_avx512/mlkem_gen_matrix_avx512.S) in the image for  *)
(* k = 3, in the configurations that the API uses: key generation,           *)
(* encapsulation and decapsulation of ML-KEM-768. The code and the parts of  *)
(* the proofs are in mlkem_gen_matrix_avx512.ml. A copy of                   *)
(* mlkem_gen_matrix_k3.ml for the AVX2 version.                              *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/gen_matrix_common_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness for the configurations used by the API. The matrix polynomial *)
(* a[i][j] is SampleNTT(rho || j || i), or SampleNTT(rho || i || j) when     *)
(* transposed, its coefficient t being coefficient avx_unorder t of          *)
(* SampleNTT's, as mlkem_unpack puts them; the digest of a job with ds = 6   *)
(* is SHA3-256 of its message and with ds = 0x1f the first 32 bytes of       *)
(* SHAKE256 of it; noise polynomial i (with nonce0 = 0) has the coefficients *)
(* of SamplePolyCBD_2(PRF_2(seed, i)). The stack used is within the 3887     *)
(* bytes below the return address (the saved registers, the frame and the    *)
(* 807 bytes below it that sha3_keccak4_f1600_alt uses in the AVX2 version,  *)
(* of which sha3_keccak4_f1600_avx512 uses only the 8 of its return          *)
(* address), or 5631 when mlkem_getnoise_avx512 is called, and the return    *)
(* address and the pointer to the constants block above it are read. A job   *)
(* that is not used has ds = 0, and its other fields and the pointers not    *)
(* used (jobs, noise) are arbitrary.                                         *)
(* ------------------------------------------------------------------------- *)

(* k = 3, not transposed, with the 6 noise polynomials of key generation     *)
(* (ML-KEM-768), all sampled in lanes left idle by the matrix.               *)

let MLKEM_NATIVE_GEN_MATRIX_K3_NOISE_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a rhop (rho:byte list) noise sigma (seed:byte list) nout jobs c pc
    stackpointer returnaddress.
     aligned 32 a /\ LENGTH rho = 32 /\ LENGTH seed = 32 /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 3887),3903); (a,4608); (nout,3072)] /\
     ALLPAIRS nonoverlapping
      [(word_sub stackpointer (word 3887),3903); (a,4608); (nout,3072)]
      [(word pc,mlkem_native2_avx512_image_size); (rhop,32); (noise,32);
       (sigma,32);
       (c,6048)] /\
     nonoverlapping (c,256)
       (word(pc + sha3_keccak4_f1600_avx512),sha3_keccak4_f1600_avx512_size)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
               read RIP s = word(pc + mlkem_gen_matrix_avx512) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a; rhop; word 3; word 4; jobs; noise] s /\
               read (memory :> bytes64 (word_add stackpointer (word 8))) s =
               c /\
               read (memory :> bytes(rhop,32)) s = num_of_bytelist rho /\
               read (memory :> bytes64 noise) s = sigma /\
               read (memory :> bytes64 (word_add noise (word 8))) s = word 0 /\
               read (memory :> bytes64 (word_add noise (word 16))) s =
               word 6 /\
               read (memory :> bytes64 (word_add noise (word 24))) s = nout /\
               read (memory :> bytes(sigma,32)) s = num_of_bytelist seed /\
               wordlist_from_memory(c,24) s = round_constants /\
               wordlist_from_memory(word_add c (word 192),4) s =
               rho8_constant /\
               wordlist_from_memory(word_add c (word 224),4) s =
               rho56_constant /\
               read (memory :> bytes(word_add c (word 1952),4096)) s =
               num_of_wordlist mlkem_rej_uniform_table)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (!i j t. i < 3 /\ j < 3 /\ t < 256
                        ==> read(memory :> bytes16(word_add a
                                 (word(512 * (3 * i + j) + 2 * t)))) s =
                            iword(mlkem_sample_ntt
                                   (APPEND rho [word j; word i])
                                   (avx_unorder t))) /\
               (!i t. i < 6 /\ t < 256
                      ==> read(memory :> bytes16(word_add nout
                                 (word(512 * i + 2 * t)))) s =
                          iword(mlkem_cbd_coeff 2
                                 (mlkem_prf 2 seed (word i)) t)))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,4608); memory :> bytes(nout,3072);
                      memory :> bytes(word_sub stackpointer
                                       (word 3887),3887)])`;;

let MLKEM_NATIVE_GEN_MATRIX_K3_NOISE_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT = assume_spec MLKEM_NATIVE_GEN_MATRIX_K3_NOISE_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* k = 3, transposed, with H(pk) for the 1184 bytes of pk as job 1 and no    *)
(* noise (encapsulation of ML-KEM-768).                                      *)

let MLKEM_NATIVE_GEN_MATRIX_K3_HASH_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a rhop (rho:byte list) jobs msg0 len0 out0 msg1 (m1:byte list) out1 noise
    c pc stackpointer returnaddress.
     aligned 32 a /\ LENGTH rho = 32 /\ LENGTH m1 = 1184 /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 3887),3903); (a,4608); (out1,32)] /\
     ALLPAIRS nonoverlapping
      [(word_sub stackpointer (word 3887),3903); (a,4608); (out1,32)]
      [(word pc,mlkem_native2_avx512_image_size); (rhop,32); (jobs,64);
       (msg1,1184);
       (c,6048)] /\
     nonoverlapping (c,256)
       (word(pc + sha3_keccak4_f1600_avx512),sha3_keccak4_f1600_avx512_size)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
               read RIP s = word(pc + mlkem_gen_matrix_avx512) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a; rhop; word 3; word 3; jobs; noise] s /\
               read (memory :> bytes64 (word_add stackpointer (word 8))) s =
               c /\
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
               wordlist_from_memory(c,24) s = round_constants /\
               wordlist_from_memory(word_add c (word 192),4) s =
               rho8_constant /\
               wordlist_from_memory(word_add c (word 224),4) s =
               rho56_constant /\
               read (memory :> bytes(word_add c (word 1952),4096)) s =
               num_of_wordlist mlkem_rej_uniform_table)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (!i j t. i < 3 /\ j < 3 /\ t < 256
                        ==> read(memory :> bytes16(word_add a
                                 (word(512 * (3 * i + j) + 2 * t)))) s =
                            iword(mlkem_sample_ntt
                                   (APPEND rho [word i; word j])
                                   (avx_unorder t))) /\
               read (memory :> bytes(out1,32)) s =
               num_of_bytelist(sha3_256 m1))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,4608); memory :> bytes(out1,32);
                      memory :> bytes(word_sub stackpointer
                                       (word 3887),3887)])`;;

let MLKEM_NATIVE_GEN_MATRIX_K3_HASH_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT = assume_spec MLKEM_NATIVE_GEN_MATRIX_K3_HASH_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* k = 3, transposed, with H(ek) as job 0, J(z || c) for 1120 bytes as job 1 *)
(* and the 7 noise polynomials of the re-encryption (decapsulation of        *)
(* ML-KEM-768), the last 4 by mlkem_getnoise_avx512.                         *)

let MLKEM_NATIVE_GEN_MATRIX_K3_HASHES_NOISE_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a rhop (rho:byte list) jobs msg0 (m0:byte list) out0 msg1 (m1:byte list)
    out1 noise sigma (seed:byte list) nout c pc stackpointer returnaddress.
     aligned 32 a /\ LENGTH rho = 32 /\ LENGTH m0 = 1184 /\
     LENGTH m1 = 1120 /\ LENGTH seed = 32 /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 5631),5647); (a,4608); (out0,32);
       (out1,32); (nout,3584)] /\
     ALLPAIRS nonoverlapping
      [(word_sub stackpointer (word 5631),5647); (a,4608); (out0,32);
       (out1,32); (nout,3584)]
      [(word pc,mlkem_native2_avx512_image_size); (rhop,32); (jobs,64);
       (msg0,1184);
       (msg1,1120); (noise,32); (sigma,32); (c,6048)] /\
     nonoverlapping (c,256)
       (word(pc + sha3_keccak4_f1600_avx512),sha3_keccak4_f1600_avx512_size)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
               read RIP s = word(pc + mlkem_gen_matrix_avx512) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a; rhop; word 3; word 7; jobs; noise] s /\
               read (memory :> bytes64 (word_add stackpointer (word 8))) s =
               c /\
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
               wordlist_from_memory(c,24) s = round_constants /\
               wordlist_from_memory(word_add c (word 192),4) s =
               rho8_constant /\
               wordlist_from_memory(word_add c (word 224),4) s =
               rho56_constant /\
               read (memory :> bytes(word_add c (word 1952),4096)) s =
               num_of_wordlist mlkem_rej_uniform_table)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (!i j t. i < 3 /\ j < 3 /\ t < 256
                        ==> read(memory :> bytes16(word_add a
                                 (word(512 * (3 * i + j) + 2 * t)))) s =
                            iword(mlkem_sample_ntt
                                   (APPEND rho [word i; word j])
                                   (avx_unorder t))) /\
               read (memory :> bytes(out0,32)) s =
               num_of_bytelist(sha3_256 m0) /\
               read (memory :> bytes(out1,32)) s =
               num_of_bytelist(list_of_seq (shake256 m1) 32) /\
               (!i t. i < 7 /\ t < 256
                      ==> read(memory :> bytes16(word_add nout
                                 (word(512 * i + 2 * t)))) s =
                          iword(mlkem_cbd_coeff 2
                                 (mlkem_prf 2 seed (word i)) t)))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,4608); memory :> bytes(out0,32);
                      memory :> bytes(out1,32); memory :> bytes(nout,3584);
                      memory :> bytes(word_sub stackpointer
                                       (word 5631),5631)])`;;

let MLKEM_NATIVE_GEN_MATRIX_K3_HASHES_NOISE_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT = assume_spec MLKEM_NATIVE_GEN_MATRIX_K3_HASHES_NOISE_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT_STMT;;
