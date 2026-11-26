(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The challenge polynomial (SampleInBall) of mldsa65_poly_challenge: the    *)
(* proof (see poly_challenge_65_spec.ml), in the stages of                   *)
(* inline_challenge.ml. Stage A is the code of this function: it zeroes the  *)
(* state at fr + 16 with eleven 16-byte stores and puts the seed of 48 bytes *)
(* and the padding byte 0x1F into it with 16-byte and smaller stores, the    *)
(* last 16 of which the SSE code assembles from parts of the seed with three *)
(* constants of the function, and XORs 0x80 into byte 135. The facts for the *)
(* pieces of the state, split where stores overlap, are assembled into the   *)
(* 200 bytes of the state (PC_CHAIN_TAC).                                    *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_challenge_65_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_challenge.ml";;

let PC65_EXEC = MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;
let pc65_off k = layout "mldsa65_poly_challenge" + k;;

let PC65_A_TM = PC_A_TM "mldsa65_poly_challenge" 0x18 0x11c 48 48;;

let PC65_PIECES =
  [0,16; 16,1; 17,16; 33,16] @ map (fun j -> j,1) (49--55) @
  map (fun j -> j,16) [56;72;88;104] @ map (fun j -> j,1) (120--135) @
  map (fun j -> j,16) [136;152;168;184];;


let PC_STATE_WORD_48 = PC_STATE_WORD 48;;

let PC65_A = prove(PC65_A_TM,
  PC_A_PRE PC65_EXEC 48 [0,16; 16,1; 25,8; 17,8; 41,4; 46,2; 45,1; 33,8] THEN
  PC_SSE_STEPS_TAC PC65_EXEC (1--13) THEN
  pc_zfact "s13" 40 41 8 THEN MAP_EVERY (fun k -> pc_zfact "s13" 40 k 1) (49--55) THEN
  MAP_EVERY (fun k -> pc_zfact "s13" 56 k 1) (56--71) THEN
  MAP_EVERY (fun k -> pc_zfact "s13" 136 k 1) (136--151) THEN
  PC_SSE_STEPS_TAC PC65_EXEC (14--27) THEN
  pc_zld "s27" 49 THEN
  PC_SSE_STEPS_TAC PC65_EXEC (28--29) THEN
  IMAGE_RIPREL_TAC (PC_CONST 0x25310) (pc65_off 0xbb) THEN PC_SSE_STEPS_TAC PC65_EXEC (30--33) THEN
  IMAGE_RIPREL_TAC (PC_CONST 0x25320) (pc65_off 0xd0) THEN PC_SSE_STEPS_TAC PC65_EXEC (34--37) THEN
  IMAGE_RIPREL_TAC (PC_CONST 0x25330) (pc65_off 0xe4) THEN PC_SSE_STEPS_TAC PC65_EXEC (38--49) THEN
  PC_CHAIN_TAC (PC_SW 48) PC65_PIECES "s49" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(SPEC `C:num` PC_STATE_WORD_48) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PC_MODLEMMA];
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let PC65_B = PC_B_PROVE PC65_EXEC "mldsa65_poly_challenge" 0x11c 0x15b 48;;

let PC65_C = PC_C_PROVE PC65_EXEC "mldsa65_poly_challenge" 0x15b 0x181 0x1d6 48 49;;

let PC65_MAIN = PC_MAIN_PROVE PC65_EXEC "mldsa65_poly_challenge" 0x18 0x298 48 49 48 PC65_A PC65_B PC65_C;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the prologue, MAIN *)
(* and the epilogue.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  PC_TOP_TAC PC65_EXEC 48 PC65_MAIN);;

let MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    CORRECT_OF_FULL_TAC
     (MP (SPEC_ALL
       MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    SAFE_OF_FULL_TAC
     (MP (SPEC_ALL
       MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
