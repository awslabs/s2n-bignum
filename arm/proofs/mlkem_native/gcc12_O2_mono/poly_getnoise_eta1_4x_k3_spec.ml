(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of four noise polynomials with eta = 2 from a seed and nonces    *)
(* for ML-KEM-768. In the gcc 12 -O2 monolithic build, the functions         *)
(* mlkem768_poly_getnoise_eta1_4x and mlkem1024_poly_getnoise_eta1_4x are    *)
(* the same code (the compiler has folded them), so the theorem of           *)
(* poly_getnoise_eta1_4x_k4.ml is also that of this function: the statement  *)
(* here only differs in the name of the function, which is the same address  *)
(* in the image.                                                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_getnoise_eta1_4x_k4_spec.ml";;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r0 r1 r2 r3 seed (sd:byte list) nonce0 nonce1 nonce2 nonce3
    guard mf mc ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH sd = 32 /\
        PAIRWISE nonoverlapping
         [(r0,512); (r1,512); (r2,512);
          (r3,if r3 = word 0 then 0 else 512);
          (word_sub stackpointer (word 2672),2672)] /\
        ALLPAIRS nonoverlapping
         [(r0,512); (r1,512); (r2,512);
          (r3,if r3 = word 0 then 0 else 512);
          (word_sub stackpointer (word 2672),2672)]
         [(seed,32); (stackpointer,1); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8);
          (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlkem768_poly_getnoise_eta1_4x) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS
                   [r0; r1; r2; r3; seed; nonce0; nonce1; nonce2] s /\
                  read (memory :> bytes8 stackpointer) s =
                  word_zx(nonce3:int64) /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,32)) s = num_of_bytelist sd)
             (\s. read PC s = returnaddress /\
                  (let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce0])) 128) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r0 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                 &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 3)) MOD 2))) /\
                  (let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce1])) 128) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r1 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                 &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 3)) MOD 2))) /\
                  (let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce2])) 128) in
                   !i. i < 256
                       ==> read(memory :> bytes16(word_add r2 (word(2 * i))))
                                s =
                           iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                 &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                   (n DIV 2 EXP (4 * i + 3)) MOD 2))) /\
                  (~(r3 = word 0) ==>
                   (let n = num_of_bytelist
                            (list_of_seq
                              (shake256 (APPEND sd [word_zx nonce3])) 128) in
                    !i. i < 256
                        ==> read(memory :> bytes16(word_add r3 (word(2 * i))))
                                 s =
                            iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                    (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                  &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                    (n DIV 2 EXP (4 * i + 3)) MOD 2)))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(r0,512); memory :> bytes(r1,512);
                memory :> bytes(r2,512);
                memory :> bytes(r3,if r3 = word 0 then 0 else 512);
                memory :> bytes(word_sub stackpointer (word 2672),2672)])`;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_safety_contract mf ea el ev /\
     memcpy_safety_contract mc ea el ev
     ==> exists f_events.
          forall e r0 r1 r2 r3 seed guard pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
            [r0,512; r1,512; r2,512; r3,(if r3 = word 0 then 0 else 512);
             word_sub stackpointer (word 2672),2672] /\
           ALLPAIRS nonoverlapping
            [r0,512; r1,512; r2,512; r3,(if r3 = word 0 then 0 else 512);
             word_sub stackpointer (word 2672),2672]
            [seed,32; stackpointer,1; word pc,libmlkem_size;
             word(pc + got_stack_chk_guard),8;
             guard,8; word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                     read PC s = word (pc + mlkem768_poly_getnoise_eta1_4x) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [r0; r1; r2; r3; seed] s /\
                     read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                      = guard /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events r0 r1 r2 r3 seed guard mf mc pc
                               (word_sub stackpointer (word 2672))
                               returnaddress /\
                        memaccess_inbounds e2
                         [seed,32; stackpointer,1; r0,512; r1,512; r2,512;
                          r3,(if r3 = word 0 then 0 else 512);
                          word_sub stackpointer (word 2672),2672;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                          word(pc + mlkem_poly_cbd2_consts),64;
                          word(pc + got_memset),8; word(pc + got_memcpy),8;
                          ea,el]
                         [r0,512; r1,512; r2,512;
                          r3,(if r3 = word 0 then 0 else 512);
                          word_sub stackpointer (word 2672),2672]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(r0,512); memory :> bytes(r1,512);
                   memory :> bytes(r2,512);
                   memory :> bytes(r3,if r3 = word 0 then 0 else 512);
                   memory :> bytes(word_sub stackpointer (word 2672),2672)])`;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT;;
