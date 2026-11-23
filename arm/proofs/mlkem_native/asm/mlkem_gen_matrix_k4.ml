(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The correctness of mlkem_gen_matrix                                       *)
(* (arm/mlkem_native/asm/mlkem_gen_matrix.S) in the image for k = 4, in the  *)
(* configurations that the API uses: key generation, encapsulation and       *)
(* decapsulation of ML-KEM-1024. The code and the parts of the proofs are in *)
(* mlkem_gen_matrix.ml.                                                      *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/asm/mlkem_gen_matrix.ml";;

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

(* k = 4, not transposed, with the 8 noise polynomials of key generation     *)
(* (ML-KEM-1024), all by mlkem_getnoise after the matrix.                    *)

let MLKEM_GEN_MATRIX_K4_NOISE_SUBROUTINE_CORRECT = prove
 (`!a rhop (rho:byte list) noise sigma (seed:byte list) nout jobs c pc
    stackpointer returnaddress.
     aligned 16 stackpointer /\ LENGTH rho = 32 /\ LENGTH seed = 32 /\
     (!i j. i < 4 /\ j < 4
            ==> mlkem_samplentt_terminates (APPEND rho [word j; word i])) /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 5040),5040); (a,8192); (nout,4096)] /\
     ALLPAIRS nonoverlapping
      [(word_sub stackpointer (word 5040),5040); (a,8192); (nout,4096)]
      [(word pc,mlkem_native2_image_size); (rhop,32); (noise,32); (sigma,32);
       (c,6656)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem_gen_matrix) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [a; rhop; word 4; word 4; jobs; noise; c] s /\
               read (memory :> bytes(rhop,32)) s = num_of_bytelist rho /\
               read (memory :> bytes64 noise) s = sigma /\
               read (memory :> bytes64 (word_add noise (word 8))) s = word 0 /\
               read (memory :> bytes64 (word_add noise (word 16))) s =
               word 8 /\
               read (memory :> bytes64 (word_add noise (word 24))) s = nout /\
               read (memory :> bytes(sigma,32)) s = num_of_bytelist seed /\
               read (memory :> bytes(c,192)) s =
               num_of_wordlist round_constants /\
               read (memory :> bytes(word_add c (word 2560),4096)) s =
               num_of_wordlist mlkem_rej_uniform_table)
          (\s. read PC s = returnaddress /\
               (!i j t. i < 4 /\ j < 4 /\ t < 256
                        ==> read(memory :> bytes16(word_add a
                                 (word(512 * (4 * i + j) + 2 * t)))) s =
                            iword(mlkem_sample_ntt
                                   (APPEND rho [word j; word i]) t)) /\
               (!i t. i < 8 /\ t < 256
                      ==> read(memory :> bytes16(word_add nout
                                 (word(512 * i + 2 * t)))) s =
                          iword(mlkem_cbd_coeff 2
                                 (mlkem_prf 2 seed (word i)) t)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,8192); memory :> bytes(nout,4096);
                      memory :> bytes(word_sub stackpointer
                                       (word 5040),5040)])`,
  GM_INSTANCE_TAC 5040);;

(* k = 4, transposed, with H(pk) for the 1568 bytes of pk as job 1 and no    *)
(* noise (encapsulation of ML-KEM-1024).                                     *)

let MLKEM_GEN_MATRIX_K4_HASH_SUBROUTINE_CORRECT = prove
 (`!a rhop (rho:byte list) jobs msg0 len0 out0 msg1 (m1:byte list) out1 noise
    c pc stackpointer returnaddress.
     aligned 16 stackpointer /\ LENGTH rho = 32 /\ LENGTH m1 = 1568 /\
     (!i j. i < 4 /\ j < 4
            ==> mlkem_samplentt_terminates (APPEND rho [word i; word j])) /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 3312),3312); (a,8192); (out1,32)] /\
     ALLPAIRS nonoverlapping
      [(word_sub stackpointer (word 3312),3312); (a,8192); (out1,32)]
      [(word pc,mlkem_native2_image_size); (rhop,32); (jobs,64); (msg1,1568);
       (c,6656)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem_gen_matrix) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [a; rhop; word 4; word 3; jobs; noise; c] s /\
               read (memory :> bytes(rhop,32)) s = num_of_bytelist rho /\
               read (memory :> bytes64 jobs) s = msg0 /\
               read (memory :> bytes64 (word_add jobs (word 8))) s = len0 /\
               read (memory :> bytes64 (word_add jobs (word 16))) s = word 0 /\
               read (memory :> bytes64 (word_add jobs (word 24))) s = out0 /\
               read (memory :> bytes64 (word_add jobs (word 32))) s = msg1 /\
               read (memory :> bytes64 (word_add jobs (word 40))) s =
               word 1568 /\
               read (memory :> bytes64 (word_add jobs (word 48))) s = word 6 /\
               read (memory :> bytes64 (word_add jobs (word 56))) s = out1 /\
               read (memory :> bytes(msg1,1568)) s = num_of_bytelist m1 /\
               read (memory :> bytes(c,192)) s =
               num_of_wordlist round_constants /\
               read (memory :> bytes(word_add c (word 2560),4096)) s =
               num_of_wordlist mlkem_rej_uniform_table)
          (\s. read PC s = returnaddress /\
               (!i j t. i < 4 /\ j < 4 /\ t < 256
                        ==> read(memory :> bytes16(word_add a
                                 (word(512 * (4 * i + j) + 2 * t)))) s =
                            iword(mlkem_sample_ntt
                                   (APPEND rho [word i; word j]) t)) /\
               read (memory :> bytes(out1,32)) s =
               num_of_bytelist(sha3_256 m1))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,8192); memory :> bytes(out1,32);
                      memory :> bytes(word_sub stackpointer
                                       (word 3312),3312)])`,
  GM_INSTANCE_TAC 3312);;

(* k = 4, transposed, with H(ek) as job 0, J(z || c) for 1600 bytes as job 1 *)
(* and the 9 noise polynomials of the re-encryption (decapsulation of        *)
(* ML-KEM-1024), all by mlkem_getnoise after the matrix.                     *)

let MLKEM_GEN_MATRIX_K4_HASHES_NOISE_SUBROUTINE_CORRECT = prove
 (`!a rhop (rho:byte list) jobs msg0 (m0:byte list) out0 msg1 (m1:byte list)
    out1 noise sigma (seed:byte list) nout c pc stackpointer returnaddress.
     aligned 16 stackpointer /\ LENGTH rho = 32 /\ LENGTH m0 = 1568 /\
     LENGTH m1 = 1600 /\ LENGTH seed = 32 /\
     (!i j. i < 4 /\ j < 4
            ==> mlkem_samplentt_terminates (APPEND rho [word i; word j])) /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 5040),5040); (a,8192); (out0,32);
       (out1,32); (nout,4608)] /\
     ALLPAIRS nonoverlapping
      [(word_sub stackpointer (word 5040),5040); (a,8192); (out0,32);
       (out1,32); (nout,4608)]
      [(word pc,mlkem_native2_image_size); (rhop,32); (jobs,64); (msg0,1568);
       (msg1,1600); (noise,32); (sigma,32); (c,6656)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem_gen_matrix) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [a; rhop; word 4; word 7; jobs; noise; c] s /\
               read (memory :> bytes(rhop,32)) s = num_of_bytelist rho /\
               read (memory :> bytes64 jobs) s = msg0 /\
               read (memory :> bytes64 (word_add jobs (word 8))) s =
               word 1568 /\
               read (memory :> bytes64 (word_add jobs (word 16))) s = word 6 /\
               read (memory :> bytes64 (word_add jobs (word 24))) s = out0 /\
               read (memory :> bytes(msg0,1568)) s = num_of_bytelist m0 /\
               read (memory :> bytes64 (word_add jobs (word 32))) s = msg1 /\
               read (memory :> bytes64 (word_add jobs (word 40))) s =
               word 1600 /\
               read (memory :> bytes64 (word_add jobs (word 48))) s =
               word 31 /\
               read (memory :> bytes64 (word_add jobs (word 56))) s = out1 /\
               read (memory :> bytes(msg1,1600)) s = num_of_bytelist m1 /\
               read (memory :> bytes64 noise) s = sigma /\
               read (memory :> bytes64 (word_add noise (word 8))) s = word 0 /\
               read (memory :> bytes64 (word_add noise (word 16))) s =
               word 9 /\
               read (memory :> bytes64 (word_add noise (word 24))) s = nout /\
               read (memory :> bytes(sigma,32)) s = num_of_bytelist seed /\
               read (memory :> bytes(c,192)) s =
               num_of_wordlist round_constants /\
               read (memory :> bytes(word_add c (word 2560),4096)) s =
               num_of_wordlist mlkem_rej_uniform_table)
          (\s. read PC s = returnaddress /\
               (!i j t. i < 4 /\ j < 4 /\ t < 256
                        ==> read(memory :> bytes16(word_add a
                                 (word(512 * (4 * i + j) + 2 * t)))) s =
                            iword(mlkem_sample_ntt
                                   (APPEND rho [word i; word j]) t)) /\
               read (memory :> bytes(out0,32)) s =
               num_of_bytelist(sha3_256 m0) /\
               read (memory :> bytes(out1,32)) s =
               num_of_bytelist(list_of_seq (shake256 m1) 32) /\
               (!i t. i < 9 /\ t < 256
                      ==> read(memory :> bytes16(word_add nout
                                 (word(512 * i + 2 * t)))) s =
                          iword(mlkem_cbd_coeff 2
                                 (mlkem_prf 2 seed (word i)) t)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,8192); memory :> bytes(out0,32);
                      memory :> bytes(out1,32); memory :> bytes(nout,4608);
                      memory :> bytes(word_sub stackpointer
                                       (word 5040),5040)])`,
  GM_INSTANCE_TAC 5040);;
