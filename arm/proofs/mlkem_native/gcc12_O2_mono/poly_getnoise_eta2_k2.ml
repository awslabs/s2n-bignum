(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of a noise polynomial with eta = 2 from a seed and a nonce for   *)
(* ML-KEM-512. In the gcc 12 -O2 monolithic build, the functions             *)
(* mlkem512_poly_getnoise_eta2 and mlkem1024_poly_getnoise_eta2 are the same *)
(* code (the compiler has folded them), so the theorems of                   *)
(* poly_getnoise_eta2_k4.ml are also those of this function: the statements  *)
(* here only differ in the name of the function, which is the same address   *)
(* in the image.                                                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_getnoise_eta2_k4.ml";;

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r seed (sd:byte list) nonce guard mc ea el ev pc stackpointer
   returnaddress.
        memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH sd = 32 /\
        PAIRWISE nonoverlapping
         [(r,512); (seed,32); (word_sub stackpointer (word 816),816)] /\
        ALLPAIRS nonoverlapping
         [(r,512); (word_sub stackpointer (word 816),816)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlkem512_poly_getnoise_eta2) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; seed; nonce] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,32)) s = num_of_bytelist sd)
             (\s. read PC s = returnaddress /\
                  let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce])) 128) in
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 3)) MOD 2)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(r,512);
                memory :> bytes(word_sub stackpointer (word 816),816)])`,
  ACCEPT_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;
