(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The constant-time and memory safety of mlkem_gen_matrix                   *)
(* (x86/mlkem_native2/mlkem_gen_matrix.S) in the image for k = 2, in the     *)
(* configurations that the API uses, as for MLKEM_GEN_MATRIX_K2_*: the       *)
(* events are a function of the addresses and of rho, which is public (they  *)
(* depend on the matrix through the rejection sampling), and not of the      *)
(* messages of the hash jobs or the noise seed; for decapsulation, whose     *)
(* caller branches on H(ek), the digest of job 0 is also a result.           *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native2_gm_safe.ml";;

(* k = 2, not transposed, with no hash jobs and no noise (key generation of  *)
(* ML-KEM-512).                                                              *)

let MLKEM_GEN_MATRIX_K2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e a rhop (rho:byte list) jobs noise c pc stackpointer
            returnaddress.
       aligned 32 a /\ LENGTH rho = 32 /\
       PAIRWISE nonoverlapping
        [(word_sub stackpointer (word 3887),3903); (a,2048)] /\
       ALLPAIRS nonoverlapping
        [(word_sub stackpointer (word 3887),3903); (a,2048)]
        [(word pc,mlkem_native2_image_size); (rhop,32); (c,6048)] /\
       nonoverlapping (c,256)
         (word(pc + sha3_keccak4_f1600_alt),sha3_keccak4_f1600_alt_size)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + mlkem_gen_matrix) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rhop; word 2; word 0; jobs; noise] s /\
                 read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                 c /\
                 read (memory :> bytes(rhop,32)) s = num_of_bytelist rho /\
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
                    e2 = f_events a rhop rho jobs noise c pc
                           (word_sub stackpointer (word 3887)) returnaddress /\
                    memaccess_inbounds e2
                     [rhop,32; c,6048;
                      word(pc + sha3_keccak_f1600_alt2_rotations),384;
                      a,2048; word_sub stackpointer (word 3887),3903]
                     [a,2048; word_sub stackpointer (word 3887),3887]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,2048);
                        memory :> bytes(word_sub stackpointer
                                         (word 3887),3887)])`,
  GM_SAFE_INSTANCE_TAC 3887);;

(* k = 2, transposed, with H(pk) for the 800 bytes of pk as job 1 and no     *)
(* noise (encapsulation of ML-KEM-512).                                      *)

let MLKEM_GEN_MATRIX_K2_HASH_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e a rhop (rho:byte list) jobs msg0 len0 out0 msg1 out1 noise c pc
            stackpointer returnaddress.
       aligned 32 a /\ LENGTH rho = 32 /\
       PAIRWISE nonoverlapping
        [(word_sub stackpointer (word 3887),3903); (a,2048); (out1,32)] /\
       ALLPAIRS nonoverlapping
        [(word_sub stackpointer (word 3887),3903); (a,2048); (out1,32)]
        [(word pc,mlkem_native2_image_size); (rhop,32); (jobs,64); (msg1,800);
         (c,6048)] /\
       nonoverlapping (c,256)
         (word(pc + sha3_keccak4_f1600_alt),sha3_keccak4_f1600_alt_size)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + mlkem_gen_matrix) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rhop; word 2; word 3; jobs; noise] s /\
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
                 word 800 /\
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
                     [rhop,32; jobs,64; msg1,800; c,6048;
                      word(pc + sha3_keccak_f1600_alt2_rotations),384;
                      a,2048; out1,32; word_sub stackpointer (word 3887),3903]
                     [a,2048; out1,32;
                      word_sub stackpointer (word 3887),3887]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,2048); memory :> bytes(out1,32);
                        memory :> bytes(word_sub stackpointer
                                         (word 3887),3887)])`,
  GM_SAFE_INSTANCE_TAC 3887);;

(* k = 2, transposed, with H(ek) for the 800 bytes of ek as job 0 and J(z || *)
(* c) for the 800 bytes of z || c as job 1, and no noise (decapsulation of   *)
(* ML-KEM-512).                                                              *)

let MLKEM_GEN_MATRIX_K2_HASHES_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e a rhop (rho:byte list) jobs msg0 (m0:byte list) out0 msg1 out1
            noise c pc stackpointer returnaddress.
       aligned 32 a /\ LENGTH rho = 32 /\ LENGTH m0 = 800 /\
       PAIRWISE nonoverlapping
        [(word_sub stackpointer (word 3887),3903); (a,2048); (out0,32);
         (out1,32)] /\
       ALLPAIRS nonoverlapping
        [(word_sub stackpointer (word 3887),3903); (a,2048); (out0,32);
         (out1,32)]
        [(word pc,mlkem_native2_image_size); (rhop,32); (jobs,64); (msg0,800);
         (msg1,800); (c,6048)] /\
       nonoverlapping (c,256)
         (word(pc + sha3_keccak4_f1600_alt),sha3_keccak4_f1600_alt_size)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + mlkem_gen_matrix) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rhop; word 2; word 3; jobs; noise] s /\
                 read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                 c /\
                 read (memory :> bytes(rhop,32)) s = num_of_bytelist rho /\
                 read (memory :> bytes64 jobs) s = msg0 /\
                 read (memory :> bytes64 (word_add jobs (word 8))) s =
                 word 800 /\
                 read (memory :> bytes64 (word_add jobs (word 16))) s =
                 word 6 /\
                 read (memory :> bytes64 (word_add jobs (word 24))) s = out0 /\
                 read (memory :> bytes(msg0,800)) s = num_of_bytelist m0 /\
                 read (memory :> bytes64 (word_add jobs (word 32))) s = msg1 /\
                 read (memory :> bytes64 (word_add jobs (word 40))) s =
                 word 800 /\
                 read (memory :> bytes64 (word_add jobs (word 48))) s =
                 word 31 /\
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
                 read (memory :> bytes(out0,32)) s =
                 num_of_bytelist(sha3_256 m0) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a rhop rho jobs msg0 out0 msg1 out1 noise c
                           pc (word_sub stackpointer (word 3887))
                           returnaddress /\
                    memaccess_inbounds e2
                     [rhop,32; jobs,64; msg0,800; msg1,800; c,6048;
                      word(pc + sha3_keccak_f1600_alt2_rotations),384;
                      a,2048; out0,32; out1,32;
                      word_sub stackpointer (word 3887),3903]
                     [a,2048; out0,32; out1,32;
                      word_sub stackpointer (word 3887),3887]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,2048); memory :> bytes(out0,32);
                        memory :> bytes(out1,32);
                        memory :> bytes(word_sub stackpointer
                                         (word 3887),3887)])`,
  GM_SAFE_INSTANCE_TAC 3887);;
