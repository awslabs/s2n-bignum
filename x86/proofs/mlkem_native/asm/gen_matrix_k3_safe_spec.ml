(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The constant-time and memory safety of mlkem_gen_matrix                   *)
(* (x86/mlkem_native/asm/mlkem_gen_matrix.S) in the image for k = 3, in the  *)
(* configurations that the API uses, as for MLKEM_GEN_MATRIX_K3_*: the       *)
(* events are a function of the addresses and of rho, which is public (they  *)
(* depend on the matrix through the rejection sampling), and not of the      *)
(* messages of the hash jobs or the noise seed; for decapsulation, whose     *)
(* caller branches on H(ek), the digest of job 0 is also a result.           *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm/gm_safe_spec.ml";;

(* k = 3, not transposed, with the 6 noise polynomials of key generation     *)
(* (ML-KEM-768), all sampled in lanes left idle by the matrix.               *)

let MLKEM_NATIVE_GEN_MATRIX_K3_NOISE_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e a rhop (rho:byte list) noise sigma nout jobs c pc stackpointer
            returnaddress.
       aligned 32 a /\ LENGTH rho = 32 /\
       PAIRWISE nonoverlapping
        [(word_sub stackpointer (word 3887),3903); (a,4608); (nout,3072)] /\
       ALLPAIRS nonoverlapping
        [(word_sub stackpointer (word 3887),3903); (a,4608); (nout,3072)]
        [(word pc,mlkem_native2_image_size); (rhop,32); (noise,32); (sigma,32);
         (c,6048)] /\
       nonoverlapping (c,256)
         (word(pc + sha3_keccak4_f1600_alt),sha3_keccak4_f1600_alt_size)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + mlkem_gen_matrix) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rhop; word 3; word 4; jobs; noise] s /\
                 read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                 c /\
                 read (memory :> bytes(rhop,32)) s = num_of_bytelist rho /\
                 read (memory :> bytes64 noise) s = sigma /\
                 read (memory :> bytes64 (word_add noise (word 8))) s =
                 word 0 /\
                 read (memory :> bytes64 (word_add noise (word 16))) s =
                 word 6 /\
                 read (memory :> bytes64 (word_add noise (word 24))) s =
                 nout /\
                 wordlist_from_memory(c,24) s = round_constants /\
                 wordlist_from_memory(word_add c (word 192),4) s =
                 rho8_constant /\
                 wordlist_from_memory(word_add c (word 224),4) s =
                 rho56_constant /\
                 read (memory :> bytes(word_add c (word 1952),4096)) s =
                 num_of_wordlist mlkem_rej_uniform_table /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a rhop rho noise sigma nout jobs c pc
                           (word_sub stackpointer (word 3887)) returnaddress /\
                    memaccess_inbounds e2
                     [rhop,32; noise,32; sigma,32; c,6048;
                      word(pc + sha3_keccak_f1600_alt2_rotations),384;
                      a,4608; nout,3072;
                      word_sub stackpointer (word 3887),3903]
                     [a,4608; nout,3072;
                      word_sub stackpointer (word 3887),3887]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,4608); memory :> bytes(nout,3072);
                        memory :> bytes(word_sub stackpointer
                                         (word 3887),3887)])`;;

let MLKEM_NATIVE_GEN_MATRIX_K3_NOISE_ASM_IMAGE_SUBROUTINE_SAFE = assume_spec MLKEM_NATIVE_GEN_MATRIX_K3_NOISE_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;

(* k = 3, transposed, with H(pk) for the 1184 bytes of pk as job 1 and no    *)
(* noise (encapsulation of ML-KEM-768).                                      *)

let MLKEM_NATIVE_GEN_MATRIX_K3_HASH_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e a rhop (rho:byte list) jobs msg0 len0 out0 msg1 out1 noise c pc
            stackpointer returnaddress.
       aligned 32 a /\ LENGTH rho = 32 /\
       PAIRWISE nonoverlapping
        [(word_sub stackpointer (word 3887),3903); (a,4608); (out1,32)] /\
       ALLPAIRS nonoverlapping
        [(word_sub stackpointer (word 3887),3903); (a,4608); (out1,32)]
        [(word pc,mlkem_native2_image_size); (rhop,32); (jobs,64); (msg1,1184);
         (c,6048)] /\
       nonoverlapping (c,256)
         (word(pc + sha3_keccak4_f1600_alt),sha3_keccak4_f1600_alt_size)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + mlkem_gen_matrix) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rhop; word 3; word 3; jobs; noise] s /\
                 read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                 c /\
                 read (memory :> bytes(rhop,32)) s = num_of_bytelist rho /\
                 read (memory :> bytes64 jobs) s = msg0 /\
                 read (memory :> bytes64 (word_add jobs (word 8))) s = len0 /\
                 read (memory :> bytes64 (word_add jobs (word 16))) s =
                 word 0 /\
                 read (memory :> bytes64 (word_add jobs (word 24))) s = out0 /\
                 read (memory :> bytes64 (word_add jobs (word 32))) s = msg1 /\
                 read (memory :> bytes64 (word_add jobs (word 40))) s =
                 word 1184 /\
                 read (memory :> bytes64 (word_add jobs (word 48))) s =
                 word 6 /\
                 read (memory :> bytes64 (word_add jobs (word 56))) s = out1 /\
                 wordlist_from_memory(c,24) s = round_constants /\
                 wordlist_from_memory(word_add c (word 192),4) s =
                 rho8_constant /\
                 wordlist_from_memory(word_add c (word 224),4) s =
                 rho56_constant /\
                 read (memory :> bytes(word_add c (word 1952),4096)) s =
                 num_of_wordlist mlkem_rej_uniform_table /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a rhop rho jobs msg0 len0 out0 msg1 out1
                           noise c pc (word_sub stackpointer (word 3887))
                           returnaddress /\
                    memaccess_inbounds e2
                     [rhop,32; jobs,64; msg1,1184; c,6048;
                      word(pc + sha3_keccak_f1600_alt2_rotations),384;
                      a,4608; out1,32; word_sub stackpointer (word 3887),3903]
                     [a,4608; out1,32;
                      word_sub stackpointer (word 3887),3887]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,4608); memory :> bytes(out1,32);
                        memory :> bytes(word_sub stackpointer
                                         (word 3887),3887)])`;;

let MLKEM_NATIVE_GEN_MATRIX_K3_HASH_ASM_IMAGE_SUBROUTINE_SAFE = assume_spec MLKEM_NATIVE_GEN_MATRIX_K3_HASH_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;

(* k = 3, transposed, with H(ek) as job 0, J(z || c) for 1120 bytes as job 1 *)
(* and the 7 noise polynomials of the re-encryption (decapsulation of        *)
(* ML-KEM-768), the last 4 by mlkem_getnoise.                                *)

let MLKEM_NATIVE_GEN_MATRIX_K3_HASHES_NOISE_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e a rhop (rho:byte list) jobs msg0 (m0:byte list) out0 msg1 out1
            noise sigma nout c pc stackpointer returnaddress.
       aligned 32 a /\ LENGTH rho = 32 /\ LENGTH m0 = 1184 /\
       PAIRWISE nonoverlapping
        [(word_sub stackpointer (word 5631),5647); (a,4608); (out0,32);
         (out1,32); (nout,3584)] /\
       ALLPAIRS nonoverlapping
        [(word_sub stackpointer (word 5631),5647); (a,4608); (out0,32);
         (out1,32); (nout,3584)]
        [(word pc,mlkem_native2_image_size); (rhop,32); (jobs,64); (msg0,1184);
         (msg1,1120); (noise,32); (sigma,32); (c,6048)] /\
       nonoverlapping (c,256)
         (word(pc + sha3_keccak4_f1600_alt),sha3_keccak4_f1600_alt_size)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + mlkem_gen_matrix) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rhop; word 3; word 7; jobs; noise] s /\
                 read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                 c /\
                 read (memory :> bytes(rhop,32)) s = num_of_bytelist rho /\
                 read (memory :> bytes64 jobs) s = msg0 /\
                 read (memory :> bytes64 (word_add jobs (word 8))) s =
                 word 1184 /\
                 read (memory :> bytes64 (word_add jobs (word 16))) s =
                 word 6 /\
                 read (memory :> bytes64 (word_add jobs (word 24))) s = out0 /\
                 read (memory :> bytes(msg0,1184)) s = num_of_bytelist m0 /\
                 read (memory :> bytes64 (word_add jobs (word 32))) s = msg1 /\
                 read (memory :> bytes64 (word_add jobs (word 40))) s =
                 word 1120 /\
                 read (memory :> bytes64 (word_add jobs (word 48))) s =
                 word 31 /\
                 read (memory :> bytes64 (word_add jobs (word 56))) s = out1 /\
                 read (memory :> bytes64 noise) s = sigma /\
                 read (memory :> bytes64 (word_add noise (word 8))) s =
                 word 0 /\
                 read (memory :> bytes64 (word_add noise (word 16))) s =
                 word 7 /\
                 read (memory :> bytes64 (word_add noise (word 24))) s =
                 nout /\
                 wordlist_from_memory(c,24) s = round_constants /\
                 wordlist_from_memory(word_add c (word 192),4) s =
                 rho8_constant /\
                 wordlist_from_memory(word_add c (word 224),4) s =
                 rho56_constant /\
                 read (memory :> bytes(word_add c (word 1952),4096)) s =
                 num_of_wordlist mlkem_rej_uniform_table /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 read (memory :> bytes(out0,32)) s =
                 num_of_bytelist(sha3_256 m0) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a rhop rho jobs msg0 out0 msg1 out1 noise
                           sigma nout c pc (word_sub stackpointer (word 5631))
                           returnaddress /\
                    memaccess_inbounds e2
                     [rhop,32; jobs,64; msg0,1184; msg1,1120; noise,32;
                      sigma,32; c,6048;
                      word(pc + sha3_keccak_f1600_alt2_rotations),384;
                      a,4608; out0,32; out1,32; nout,3584;
                      word_sub stackpointer (word 5631),5647]
                     [a,4608; out0,32; out1,32; nout,3584;
                      word_sub stackpointer (word 5631),5631]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,4608); memory :> bytes(out0,32);
                        memory :> bytes(out1,32); memory :> bytes(nout,3584);
                        memory :> bytes(word_sub stackpointer
                                         (word 5631),5631)])`;;

let MLKEM_NATIVE_GEN_MATRIX_K3_HASHES_NOISE_ASM_IMAGE_SUBROUTINE_SAFE = assume_spec MLKEM_NATIVE_GEN_MATRIX_K3_HASHES_NOISE_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;
