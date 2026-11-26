(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The challenge polynomial (SampleInBall) of mldsa87_poly_challenge: the    *)
(* proof (see poly_challenge_87_spec.ml), in the stages of                   *)
(* inline_challenge.ml. Stage A is the code of this function: it zeroes the  *)
(* state at fr + 16 with thirteen 16-byte stores, copies the seed of 64      *)
(* bytes into it with four, and XORs the padding bytes 0x1F into byte 64 and *)
(* 0x80 into byte 135. The facts for the pieces of the state, split where    *)
(* stores overlap, are assembled into the 200 bytes of the state             *)
(* (PC_CHAIN_TAC).                                                           *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_challenge_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_challenge.ml";;

let PC87_EXEC = MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;
let pc87_off k = layout "mldsa87_poly_challenge" + k;;

let PC87_A_TM = PC_A_TM "mldsa87_poly_challenge" 0x18 0xb4 64 0;;

let PC87_PIECES =
  map (fun j -> j,16) [0;16;32;48] @ map (fun j -> j,1) (64--79) @
  map (fun j -> j,16) [80;96;112] @ map (fun j -> j,1) (128--143) @
  map (fun j -> j,16) [144;160;176] @ map (fun j -> j,1) (192--199);;

let PC_STATE_WORD_64 = PC_STATE_WORD 64;;

let PC87_A = prove(PC87_A_TM,
  PC_A_PRE PC87_EXEC 64 [0,16; 16,16; 32,16; 48,16] THEN
  PC_SSE_STEPS_TAC PC87_EXEC (1--3) THEN
  MAP_EVERY (fun k -> pc_zfact "s3" 204 k 1) (208--215) THEN
  PC_SSE_STEPS_TAC PC87_EXEC (4--15) THEN
  MAP_EVERY (fun k -> pc_zfact "s15" 80 k 1) (80--95) THEN
  MAP_EVERY (fun k -> pc_zfact "s15" 144 k 1) (144--159) THEN
  PC_SSE_STEPS_TAC PC87_EXEC (16--28) THEN
  PC_CHAIN_TAC (PC_SW 64) PC87_PIECES "s28" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(SPEC `C:num` PC_STATE_WORD_64) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PC_MODLEMMA];
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let PC87_B = PC_B_PROVE PC87_EXEC "mldsa87_poly_challenge" 0xb4 0xf3 64;;

let PC87_C = PC_C_PROVE PC87_EXEC "mldsa87_poly_challenge" 0xf3 0x111 0x166 64 60;;

let PC87_MAIN = PC_MAIN_PROVE PC87_EXEC "mldsa87_poly_challenge" 0x18 0x228 64 60 0 PC87_A PC87_B PC87_C;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the prologue, MAIN *)
(* and the epilogue.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  PC_TOP_TAC PC87_EXEC 64 PC87_MAIN);;

let MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    CORRECT_OF_FULL_TAC
     (MP (SPEC_ALL
       MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    SAFE_OF_FULL_TAC
     (MP (SPEC_ALL
       MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
