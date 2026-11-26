(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The challenge polynomial (SampleInBall) of mldsa44_poly_challenge: the    *)
(* proof (see poly_challenge_44_spec.ml), in the stages of                   *)
(* inline_challenge.ml. Stage A is the code of this function: it zeroes the  *)
(* state at fr + 16 with eleven 16-byte stores and puts the seed of 32 bytes *)
(* and the padding byte 0x1F into it with 16-byte and smaller stores, the    *)
(* bytes 25 to 32 of the state as a 64-bit word that the SSE code assembles  *)
(* from parts of the seed with four constants of the function, and XORs 0x80 *)
(* into byte 135. The facts for the pieces of the state, split where stores  *)
(* overlap, are assembled into the 200 bytes of the state (PC_CHAIN_TAC).    *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_challenge_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_challenge.ml";;

let PC44_EXEC = MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;
let pc44_off k = layout "mldsa44_poly_challenge" + k;;

let PC44_A_TM = parse_term(Printf.sprintf
 "exists f_events.
    forall e (c:int64) (seed:int64) (C:num) (fr:int64) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fr /\\
      ALLPAIRS nonoverlapping [(fr,384)]
        [(seed,32); (word pc,libmldsa_size)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read RIP s = word (pc + %d) /\\
                read RSP s = fr /\\
                read RDI s = c /\\ read RSI s = seed /\\
                read (memory :> bytes(seed,32)) s = C /\\
                read events s = e)
           (\\s. read RIP s = word (pc + %d) /\\
                read RSP s = fr /\\ read RBX s = c /\\
                read RDI s = word_add fr (word 16) /\\
                read R14 s = word_add fr (word 16) /\\
                read (memory :> bytes(word_add fr (word 16),200)) s =
                  val(mld_shake256_state 32 C) /\\
                read (memory :> bytes32(word_add fr (word 216))) s = word 136 /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events c seed C pc fr /\\
                   memaccess_inbounds e2
                    [seed,32; fr,384; word(pc + mldsa44_poly_challenge_consts),64]
                    [fr,384]))
           (MAYCHANGE [RIP; RAX; RBX; RDI; R14] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5] ,, MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(fr,384)])" (pc44_off 0x18) (pc44_off 0x10a));;

let PC44_PIECES =
  [0,16; 16,1; 17,16] @ map (fun j -> j,1) (33--39) @
  map (fun j -> j,16) [40;56;72;88;104] @ map (fun j -> j,1) (120--135) @
  map (fun j -> j,16) [136;152;168;184];;

let PC44_CONST k = IMAGE_CONST_RULE_FOR mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc k 128;;

let PC44_A_PRE =
  CONCRETIZE_F_EVENTS_TAC `\(c:int64) (seed:int64) (C:num) (pc:num) (fr:int64). f_ev_a c seed C pc fr:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `c:int64`; `seed:int64`; `C:num`; `fr:int64`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS; PAIRWISE; fst PC44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun n -> GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" n,`:int256`)) (parse_term(Printf.sprintf "read YMM%d" n))) [0;1;2;3;4;5] THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `C < 2 EXP 256` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`seed:int64`; `32`; `read memory (s0:x86state)`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MAP_EVERY (fun (j,nb) -> ASSUME_TAC(pc_seed_fact 256 j nb))
    [0,16; 16,1; 17,8; 25,4; 30,2; 29,1];;

let PC_STATE_WORD_32 = PC_STATE_WORD 32;;

let PC44_A = prove(PC44_A_TM,
  PC44_A_PRE THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV)) THEN
  PC_SSE_STEPS_TAC PC44_EXEC (1--13) THEN
  pc_zfact "s13" 40 41 8 THEN MAP_EVERY (fun k -> pc_zfact "s13" 40 k 1) (49--55) THEN
  MAP_EVERY (fun k -> pc_zfact "s13" 136 k 1) (136--151) THEN
  PC_SSE_STEPS_TAC PC44_EXEC (14--23) THEN
  IMAGE_RIPREL_TAC (PC44_CONST 0x25060) (0x77f0+0x9f) THEN PC_SSE_STEPS_TAC PC44_EXEC (24--30) THEN
  IMAGE_RIPREL_TAC (PC44_CONST 0x25070) (0x77f0+0xc0) THEN PC_SSE_STEPS_TAC PC44_EXEC (31--31) THEN
  IMAGE_RIPREL_TAC (PC44_CONST 0x25080) (0x77f0+0xc8) THEN PC_SSE_STEPS_TAC PC44_EXEC (32--32) THEN
  IMAGE_RIPREL_TAC (PC44_CONST 0x25090) (0x77f0+0xd0) THEN PC_SSE_STEPS_TAC PC44_EXEC (33--44) THEN
  PC_CHAIN_TAC (PC_SW 32) PC44_PIECES "s44" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(SPEC `C:num` PC_STATE_WORD_32) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PC_MODLEMMA];
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let PC44_B = PC_B_PROVE PC44_EXEC "mldsa44_poly_challenge" 0x10a 0x149 32;;

let PC44_C = PC_C_PROVE PC44_EXEC "mldsa44_poly_challenge" 0x149 0x171 0x1c6 32 39;;

let PC44_MAIN = PC_MAIN_PROVE PC44_EXEC "mldsa44_poly_challenge" 0x18 0x29e 32 39 64 PC44_A PC44_B PC44_C;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the prologue, MAIN *)
(* and the epilogue.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  PC_TOP_TAC PC44_EXEC 32 PC44_MAIN);;

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    CORRECT_OF_FULL_TAC
     (MP (SPEC_ALL
       MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    SAFE_OF_FULL_TAC
     (MP (SPEC_ALL
       MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
