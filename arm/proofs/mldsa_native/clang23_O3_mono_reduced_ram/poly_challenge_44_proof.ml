(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The challenge polynomial (SampleInBall) of mldsa44_poly_challenge: the   *)
(* proof (see poly_challenge_44_spec.ml), in the stages of the code between *)
(* the calls and loops, with the lemmas and tactics of inline_challenge.ml: *)
(*   A: the zeroing of the Keccak state and the absorbing of the seed (the  *)
(*      straight-line code before the first call of mldsa_keccakf1600_      *)
(*      permute), at the aligned stack pointer sp of the frame;             *)
(*   B: the call, the copy of the first block of the state to the buffer,   *)
(*      the load of the sign bits and the call of memset, to the head of    *)
(*      the loop over the bytes;                                            *)
(*   C: the loop over the bytes of the SHAKE256 output from position 8 on,  *)
(*      with a call of mldsa_keccakf1600_permute and a copy of the next     *)
(*      block when the buffer is used up;                                   *)
(*   MAIN: A, B, C and the zeroing of the state and the buffer, with the    *)
(*      frame fr = sp - 240 (the callee permute is below sp);               *)
(*   the function: the realignment of the stack pointer (two cases), MAIN,  *)
(*      the stack check and the epilogue.                                   *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_challenge_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_challenge.ml";;

let PC44_EXEC = MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let PC44_A_TM = parse_term
 "exists f_events.
    forall e (c:int64) (seed:int64) (C:num) (guard:int64) (canary:int64) (sp:int64) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 sp /\\ aligned 32 sp /\\
      ALLPAIRS nonoverlapping [(sp,384)]
        [(seed,32); (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8); (guard,8)]
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa44_poly_challenge_adrp1) /\\
                read SP s = sp /\\
                C_ARGUMENTS [c; seed] s /\\
                read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
                read (memory :> bytes64 guard) s = canary /\\
                read (memory :> bytes(seed,32)) s = C /\\
                read events s = e)
           (\\s. read PC s = word (pc + 53644) /\\
                read SP s = sp /\\ read X0 s = word_add sp (word 16) /\\
                read X19 s = c /\\ read X20 s = word_add sp (word 16) /\\
                read X21 s = word 136 /\\
                read (memory :> bytes(word_add sp (word 16),200)) s =
                  val(mld_shake256_state 32 C) /\\
                read (memory :> bytes32(word_add sp (word 216))) s = word 136 /\\
                read (memory :> bytes64(word_add sp (word 376))) s = canary /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events c seed C guard pc sp /\\
                   memaccess_inbounds e2
                    [seed,32; sp,384; word(pc + got_stack_chk_guard),8; guard,8]
                    [sp,384]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [X19; X20; X21] ,,
            MAYCHANGE [memory :> bytes(sp,384)])";;

let PC44_PIECES =
  [0,16; 16,16; 32,1] @ map (fun j -> j,1) (33--39) @
  map (fun j -> j,16) [40;56;72;88;104] @ map (fun j -> j,1) (120--135) @
  map (fun j -> j,16) [136;152;168;184];;

let PC44_A_TAC =
  CONCRETIZE_F_EVENTS_TAC `\(c:int64) (seed:int64) (C:num) (guard:int64) (pc:num) (sp:int64). f_ev_a c seed C guard pc sp:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `c:int64`; `seed:int64`; `C:num`; `guard:int64`; `canary:int64`; `sp:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst PC44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD]) THEN
  FULL_INIT_TAC THEN
  MP_TAC(ISPECL [`seed:int64`; `32`; `read memory (s0:armstate)`] READ_BYTES_BOUND) THEN REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; ASSUME `read (memory :> bytes(seed,32)) s0 = C`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `C < 2 EXP 256` ASSUME_TAC THENL [FIRST_X_ASSUM(MP_TAC o check (fun th -> try concl th = `C < 2 EXP (8 * 32)` with _ -> false)) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(MATCH_MP MLD_READ_BYTES_BYTES8 (ASSUME `read (memory :> bytes(seed,32)) s0 = C`)) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(REWRITE_RULE[GEN `j:num` (MP (SPECL [`C:num`;`j:num`] (PC_BYTE_SUB 32)) (ASSUME `C < 2 EXP 256`))] th)) THEN
  MAP_EVERY (fun (sz,k) -> let th = PC_SEED_FACT 32 sz k in ASSUME_TAC(MP th (ASSUME (PC_SEED_HYP 32)))) [16,0; 8,16; 4,28] THEN
  MAP_EVERY (PC_SEED_BYTE 32) [24;25;26;27] THEN
  ARM_STEPS_TAC PC44_EXEC (1--1) THEN MLKEM_NATIVE_ADRP_TAC THEN ARM_STEPS_TAC PC44_EXEC (2--19) THEN
  PC_ZSPLIT "s19" 40 THEN PC_ZLD_TAC "s19" 4 44 THEN PC_ZSPLIT "s19" 136 THEN
  ARM_STEPS_TAC PC44_EXEC (20--52) THEN
  PC_CHAIN_TAC 32 PC44_PIECES "s52" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC;;


let PC44_A = prove(PC44_A_TM,
  PC44_A_TAC THENL
   [MP_TAC(SPEC `C:num` (PC_STATE_WORD 32)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PC_MODLEMMA];
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let PC44_B_TM = parse_term
 "!mf ea el ev.
    memset_full_contract mf ea el ev
    ==> exists f_events.
      forall e (c:int64) (C:num) (canary:int64) (fr:int64) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 (word_add fr (word 240)) /\\ aligned 32 (word_add fr (word 240)) /\\
        nonoverlapping (c,1024) (fr,624) /\\
        ALLPAIRS nonoverlapping [(c,1024); (fr,624)]
          [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
          (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + 53644) /\\
                read SP s = word_add fr (word 240) /\\
                read X0 s = word_add fr (word 256) /\\
                read X19 s = c /\\ read X20 s = word_add fr (word 256) /\\
                read X21 s = word 136 /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes(word_add fr (word 256),200)) s =
                  val(mld_shake256_state 32 C) /\\
                read (memory :> bytes32(word_add fr (word 456))) s = word 136 /\\
                read (memory :> bytes64(word_add fr (word 616))) s = canary /\\
                read events s = e)
          (\\s. read PC s = word (pc + mldsa44_poly_challenge_loop1) /\\
                read SP s = word_add fr (word 240) /\\
                read X19 s = c /\\ read X20 s = word_add fr (word 256) /\\
                read X21 s = word 136 /\\ read X24 s = word_add fr (word 464) /\\
                read X25 s = word 1 /\\ read X23 s = word 217 /\\
                read X8 s = word 8 /\\
                read X22 s = mld_poly_challenge_signs (mld_shake256_byte 32 C) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes(word_add fr (word 256),200)) s =
                  val(keccak_squeeze 1 (mld_shake256_state 32 C)) /\\
                read (memory :> bytes32(word_add fr (word 456))) s = word 136 /\\
                read (memory :> bytes64(word_add fr (word 616))) s = canary /\\
                read (memory :> bytes(word_add fr (word 464),136)) s =
                  num_of_bytelist(list_of_seq (mld_shake256_byte 32 C) 136) /\\
                (!t. t < 256
                     ==> read (memory :> bytes32(word_add c (word(4 * t)))) s =
                         word 0) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events c C mf pc fr /\\
                   memaccess_inbounds e2
                    [c,1024; fr,624; word(pc + got_memset),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192]
                    [c,1024; fr,624]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
           MAYCHANGE [X22; X23; X24; X25] ,,
           MAYCHANGE [memory :> bytes(c,1024); memory :> bytes(fr,624)])";;

let PC44_B_ALLOWED = [`c:int64`; `C:num`; `mf:int64`; `pc:num`; `fr:int64`];;
let PC_SQ1 = prove(`!S:1600 word. keccak_f1600 S = keccak_squeeze 1 S`,
  REWRITE_TAC[keccak_squeeze; ARITH_RULE `1 = SUC 0`] THEN REWRITE_TAC[keccak_squeeze]);;
let PC44_NOV tm = SUBGOAL_THEN tm (fun th -> ASSUME_TAC th THEN ASSUME_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES] th)) THENL [NONOVERLAPPING_TAC; ALL_TAC];;

let PC44_B_PRE =
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600 "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC `\(c:int64) (C:num) (mf:int64) (pc:num) (fr:int64). f_ev_b c C mf pc fr:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `c:int64`; `C:num`; `canary:int64`; `fr:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(fun th -> (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) th THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)(REWRITE_RULE[NONOVERLAPPING_CLAUSES; fst PC44_EXEC] th)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
  FULL_INIT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600]);;

let PC44_B_REST =
  ARM_STEPS_TAC PC44_EXEC [1] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc PC44_EXEC "H_PERM"
    [`read X0 s`; `mld_shake256_state 32 C`; `pc:num`; `read SP s`; `read X30 s`] PC44_B_ALLOWED 2 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PC_SQ1; READ_MEMORY_WBYTES_1600]) THEN
  PC_LOAD_FACTS_TAC "word_add fr (word 256)" "s2" [16,64; 16,80; 8,128; 16,96; 16,112; 16,0; 16,16; 16,32; 16,48] THEN
  ARM_STEPS_TAC PC44_EXEC (3--15) THEN
  PC_SPLIT64_TAC "word_add fr (word 464)" "s15" THEN
  ARM_STEPS_TAC PC44_EXEC (16--18) THEN
  LIBC_PLT_TAC PC44_EXEC 18 THEN
  PC_LIBC_CALL_TAC "H_MEMSET" PC44_EXEC [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] PC44_B_ALLOWED 23 THEN
  MEMSET_ZERO_BYTES_TAC THEN
  ARM_STEPS_TAC PC44_EXEC (24--28) THEN
  PC_CHAIN_GEN "fr" "fr" 464 "val(keccak_squeeze 1 (mld_shake256_state 32 C))" "s28" ([0,16;16,16;32,16;48,16;64,16;80,16;96,16;112,16;128,8]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_CHALLENGE_ZERO_POLY o check (fun th -> can (term_match [] `read (memory :> bytes(c,1024)) s = 0`) (concl th))) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CONV_RULE(DEPTH_CONV NUM_RED_CONV) PC_SIGNS; mld_poly_challenge_signs] THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`32`;`C:num`;`8`] PC_BLOCK0) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
    MP_TAC(SPECL [`32`; `C:num`; `136`] PC_BLOCK0) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(fun th -> ASM_REWRITE_TAC[th]);
    PC_SAFETY_TAC];;

let PC44_B = prove(PC44_B_TM, PC44_B_PRE THEN PC44_B_REST);;

let PC44_C_ALLOWED =
  [`c:int64`; `C:num`; `pc:num`; `fr:int64`; `n:num`];;

let PC44_C_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc PC44_EXEC name
    ilist PC44_C_ALLOWED n;;

let PC44_C_FRAME =
 `read X19 s = c /\
  read X20 s = word_add fr (word 256) /\
  read X21 s = word 136 /\
  read X24 s = word_add fr (word 464) /\
  read X25 s = word 1 /\
  read SP s = word_add fr (word 240) /\
  read (memory :> bytes32(word_add fr (word 456))) s = word 136 /\
  read (memory :> bytes64(word_add fr (word 616))) s = canary`;;

let PC44_C_BODY =
   `read X23 s =
    word(217 + FST(mld_poly_challenge_step 39 (mld_shake256_byte 32 C) n)) /\
    read X8 s = word((7 + n) MOD 136 + 1) /\
    read (memory :> bytes(word_add fr (word 464),136)) s =
    num_of_bytelist(list_of_seq
     (\t. mld_shake256_byte 32 C (136 * ((7 + n) DIV 136) + t)) 136) /\
    read (memory :> bytes(word_add fr (word 256),200)) s =
    val(keccak_squeeze ((7 + n) DIV 136 + 1) (mld_shake256_state 32 C)) /\
    (!t. t < 256
         ==> read (memory :> bytes32(word_add c (word(4 * t)))) s =
             SND(mld_poly_challenge_step 39 (mld_shake256_byte 32 C) n) t) /\
    read X22 s =
    word_ushr (mld_poly_challenge_signs (mld_shake256_byte 32 C))
              (FST(mld_poly_challenge_step 39 (mld_shake256_byte 32 C) n))`;;

let PC44_C_INV =
  list_mk_abs([`n:num`; `s:armstate`],
              list_mk_conj(conjuncts PC44_C_BODY @ conjuncts PC44_C_FRAME));;

let PC44_C_A2 =
  let t = subst [`mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C)`,
                 `n:num`]
                (snd(dest_abs(snd(dest_abs PC44_C_INV)))) in
  mk_abs(`s:armstate`,t);;

let PC44_C_PCF =
  `\n. if (8 + n) MOD 136 = 0 then pc + mldsa44_poly_challenge_loop1
       else pc + mldsa44_poly_challenge_join1`;;

let PC44_C_TEMPLATE =
 `\(c:int64) (C:num) (pc:num) (fr:int64).
   APPEND
      (ENUMERATEL (mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C))
        (\n. if (8 + n) MOD 136 = 0
             then if mld_poly_challenge_accept 39 (mld_shake256_byte 32 C) n
                  then if n + 1 <
                          mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C)
                       then f_ev_sa c C pc fr n
                       else f_ev_sx c C pc fr n
                  else f_ev_sr c C pc fr n
             else if mld_poly_challenge_accept 39 (mld_shake256_byte 32 C) n
                  then if n + 1 <
                          mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C)
                       then if (8 + (n + 1)) MOD 136 = 0
                            then f_ev_ab c C pc fr n
                            else f_ev_ac c C pc fr n
                       else f_ev_ax c C pc fr n
                  else if (8 + (n + 1)) MOD 136 = 0
                       then f_ev_rb c C pc fr n
                       else f_ev_rc c C pc fr n))
      (f_ev_pro c C pc fr:(uarch_event)list)`;;

let PC44_C_TM = parse_term
 "exists f_events.
    forall e (c:int64) (C:num) (canary:int64) (fr:int64) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 (word_add fr (word 240)) /\\ aligned 32 (word_add fr (word 240)) /\\
      mld_poly_challenge_terminates 39 32 C /\\
      nonoverlapping (c,1024) (fr,624) /\\
      ALLPAIRS nonoverlapping [(c,1024); (fr,624)]
        [(word pc,libmldsa_size)]
      ==> ensures arm
          (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa44_poly_challenge_loop1) /\\
                read SP s = word_add fr (word 240) /\\
                read X19 s = c /\\ read X20 s = word_add fr (word 256) /\\
                read X21 s = word 136 /\\ read X24 s = word_add fr (word 464) /\\
                read X25 s = word 1 /\\ read X23 s = word 217 /\\
                read X8 s = word 8 /\\
                read X22 s = mld_poly_challenge_signs (mld_shake256_byte 32 C) /\\
                read (memory :> bytes(word_add fr (word 256),200)) s =
                  val(keccak_squeeze 1 (mld_shake256_state 32 C)) /\\
                read (memory :> bytes32(word_add fr (word 456))) s = word 136 /\\
                read (memory :> bytes64(word_add fr (word 616))) s = canary /\\
                read (memory :> bytes(word_add fr (word 464),136)) s =
                  num_of_bytelist(list_of_seq (mld_shake256_byte 32 C) 136) /\\
                (!t. t < 256
                     ==> read (memory :> bytes32(word_add c (word(4 * t)))) s =
                         word 0) /\\
                read events s = e)
          (\\s. read PC s = word (pc + mldsa44_poly_challenge_loop1_exit) /\\
                read SP s = word_add fr (word 240) /\\
                read X19 s = c /\\ read X20 s = word_add fr (word 256) /\\
                read X21 s = word 136 /\\ read X24 s = word_add fr (word 464) /\\
                read (memory :> bytes64(word_add fr (word 616))) s = canary /\\
                (!i. i < 256
                     ==> read(memory :> bytes32(word_add c (word(4 * i)))) s =
                         mld_poly_challenge 39 32 C i) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events c C pc fr /\\
                   memaccess_inbounds e2
                    [c,1024; fr,624; word(pc + rodata_mld_KeccakF_RoundConstants),192]
                    [c,1024; fr,624]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
           MAYCHANGE [X22; X23] ,,
           MAYCHANGE [memory :> bytes(c,1024); memory :> bytes(fr,624)])";;

let PC44_C_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600 "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC PC44_C_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `c:int64`; `C:num`; `canary:int64`; `fr:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst PC44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(fun th ->
    if concl th = `mld_poly_challenge_terminates 39 32 C`
    then ASSUME_TAC(REWRITE_RULE[mld_poly_challenge_terminates] th)
    else NO_TAC);;

let PC44_C_START_TAC =
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC PC44_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[CONJUNCT1 ENUMERATEL; CONJUNCT1 APPEND;
              CONJUNCT1 mld_poly_challenge_step; WORD_USHR_ZERO] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; ETA_AX] THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  MLD_PREFIX_DISCHARGE_TAC ALL_TAC;;

let PC44_C_WHILE_TAC =
  MLD_CHALLENGE_WHILE_TAC `mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C)` PC44_C_PCF `pc + mldsa44_poly_challenge_loop1_exit` PC44_C_INV THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MLD_POLY_CHALLENGE_BYTES_POS THEN ASM_REWRITE_TAC[ARITH_EQ];
    PC44_C_START_TAC;
    ALL_TAC; ALL_TAC];;

let PC44_C_BUF = `word_add fr (word 464):int64`;;

let PC44_C_SETUP_TAC =
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    if is_exists(concl th) then
      let nth = ASSUME
        `n < mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C)` in
      ASSUME_TAC(MP (SPEC `n:num` (CONJUNCT2
                   (MATCH_MP MLD_POLY_CHALLENGE_BYTES th))) nth) THEN
      ASSUME_TAC(MP (SPEC `n:num` (MATCH_MP (REWRITE_RULE[IMP_CONJ]
                   MLD_POLY_CHALLENGE_BYTES_NEXT) th)) nth)
    else NO_TAC) THEN
  SUBGOAL_THEN
   `mld_poly_challenge_accept 39 (mld_shake256_byte 32 C) n <=>
    val(mld_shake256_byte 32 C (8 + n)) <=
    217 + FST(mld_poly_challenge_step 39 (mld_shake256_byte 32 C) n)`
  ASSUME_TAC THENL
   [REWRITE_TAC[mld_poly_challenge_accept] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

let PC44_C_ABBREV_TAC =
  ABBREV_TAC
   `k = FST (mld_poly_challenge_step 39 (mld_shake256_byte 32 C) n)` THEN
  ABBREV_TAC `j = val(mld_shake256_byte 32 C (8 + n))` THEN
  SUBGOAL_THEN `j < 256` ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN
    MP_TAC(ISPEC `mld_shake256_byte 32 C (8 + n)` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(217 + k):int64) = 217 + k /\
                val(word j:int64) = j /\
                val(word_zx(word_zx(word_zx(word(217 + k):int64):int32):byte):int32) = 217 + k`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SIMPLE_ARITH_TAC;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SIMPLE_ARITH_TAC;
      MATCH_MP_TAC PC_UXTB THEN SIMPLE_ARITH_TAC];
    ALL_TAC];;

let PC44_C_UNABBREV_TAC =
  MLD_CHALLENGE_UNABBREV_TAC
   [`val(mld_shake256_byte 32 C (8 + n))`,`j:num`;
    `FST (mld_poly_challenge_step 39 (mld_shake256_byte 32 C) n)`,`k:num`;
    `(7 + n) DIV 136`,`b:num`;
    `(7 + n) MOD 136 + 1`,`p:num`];;

let PC44_C_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN
  (REWRITE_TAC[MLD_POLY_CHALLENGE_STEP_ADD1] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  (TRY(CONJ_TAC THENL [MLD_CHALLENGE_POLY_TAC `217 + k`; ALL_TAC])) THEN
  PC44_C_UNABBREV_TAC THEN
  (CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
              RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))) THEN
  (MLD_CHALLENGE_DISCHARGE_TAC
   (TRY(ABBREV_TAC `jj = val(mld_shake256_byte 32 C (8 + n))`)));;

let PC44_C_NORMAL_PRE =
  REWRITE_TAC[ASSUME `~((8 + n) MOD 136 = 0)`] THEN
  SUBGOAL_THEN `(7 + n) MOD 136 < 135` ASSUME_TAC THENL
   [MP_TAC(SPEC `7 + n` MLD_CHALLENGE_POS_ZERO) THEN
    REWRITE_TAC[ARITH_RULE `(7 + n) + 1 = 8 + n`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`7 + n`; `136`] MOD_LT_EQ) THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_CHALLENGE_POS_SUC) THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN STRIP_ASSUME_TAC th) THEN
  SUBGOAL_THEN `(8 + (n + 1)) MOD 136 = 0 <=> (7 + n) MOD 136 + 1 = 135`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `7 + (n + 1)` MLD_CHALLENGE_POS_ZERO) THEN
    REWRITE_TAC[ARITH_RULE `(7 + (n + 1)) + 1 = 8 + (n + 1)`] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `7 + n` MLD_CHALLENGE_POS_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `(7 + n) + 1 = 8 + n`] THEN DISCH_TAC THEN
  ABBREV_TAC `p = (7 + n) MOD 136 + 1` THEN
  ABBREV_TAC `b = (7 + n) DIV 136` THEN
  SUBGOAL_THEN `p < 136` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word(p + 1):int64) = p + 1` ASSUME_TAC THENL [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  PC44_C_ABBREV_TAC THEN
  FULL_INIT_TAC THEN
  MLD_CHALLENGE_LOAD_TAC PC44_C_BUF `p:num`
   [ASSUME `136 * b + p = 8 + n`] THEN
  ARM_STEPS_TAC PC44_EXEC (1--4);;

let PC44_C_ACCEPT_TAC m pnext =
  let rest =
    (ARM_STEPS_TAC PC44_EXEC ((m+1)--(m+8))) THEN
    MLD_CHALLENGE_EXIT_TEST_TAC THEN PC_SIGN_FIX_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_USHR_COMPOSE]) THEN
    MLD_CHALLENGE_FIX_TAC (mld_challenge_is_read_reg `X23`) [GSYM WORD_ADD; GSYM ADD_ASSOC] THEN
    (SUBGOAL_THEN `mld_poly_challenge_accept 39 (mld_shake256_byte 32 C) n` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    (ASM_CASES_TAC `k + 1 = 39` THENL
      [(SUBGOAL_THEN `~(n + 1 < mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C))` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
       MLD_CHALLENGE_BRANCH_TAC THEN PC44_C_FINAL_TAC;
       (SUBGOAL_THEN `n + 1 < mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
       MLD_CHALLENGE_BRANCH_TAC THEN (pnext (m + 9))]) in
  MLD_CHALLENGE_FIX_TAC (mld_challenge_is_read_reg `X9`) [MLD_CHALLENGE_ZX_BYTE; ASSUME `val(mld_shake256_byte 32 C (8 + n)) = j`] THEN
  (FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes32` (concl th) then ASSUME_TAC(MP (SPEC `j:num` th) (ASSUME `j < 256`)) else NO_TAC)) THEN
  (MLD_CHALLENGE_UXTW_TAC `j:num`) THEN
  (ARM_STEPS_TAC PC44_EXEC (m--m)) THEN
  (MLD_CHALLENGE_EXCLUDE_TAC `217 + k` `j:num`) THEN
  ASM_CASES_TAC `j < 217 + k` THEN rest;;

let PC44_C_NORMAL_TAC =
  PC44_C_NORMAL_PRE THEN
  MLD_CHALLENGE_FIX_TAC (mld_challenge_is_read_reg `X8`) [GSYM WORD_ADD] THEN
  let next m =
    ASM_CASES_TAC `~(p = 135)` THENL
     [(SUBGOAL_THEN `~((8 + (n + 1)) MOD 136 = 0)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      ARM_STEPS_TAC PC44_EXEC (m--(m+1)) THEN
      MLD_CHALLENGE_BRANCH_TAC THEN PC44_C_FINAL_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[NOT_CLAUSES]) THEN
      (SUBGOAL_THEN `(8 + (n + 1)) MOD 136 = 0` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      PC44_C_FINAL_TAC] in
  (ASM_CASES_TAC `j <= 217 + k` THENL
   [MLD_CHALLENGE_BRANCH_TAC THEN PC44_C_ACCEPT_TAC 5 next;
    MLD_CHALLENGE_BRANCH_TAC THEN
    (SUBGOAL_THEN `~mld_poly_challenge_accept 39 (mld_shake256_byte 32 C) n` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    (SUBGOAL_THEN `n + 1 < mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    next 5]);;

let PC44_C_SQUEEZE_PRE0 =
  REWRITE_TAC[ASSUME `(8 + n) MOD 136 = 0`] THEN
  SUBGOAL_THEN `(7 + n) MOD 136 = 135` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MLD_CHALLENGE_POS_ZERO] THEN
    REWRITE_TAC[ARITH_RULE `(7 + n) + 1 = 8 + n`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_CHALLENGE_POS_WRAP) THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN STRIP_ASSUME_TAC th) THEN
  SUBGOAL_THEN `~((8 + (n + 1)) MOD 136 = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8 + (n + 1) = (7 + (n + 1)) + 1`] THEN
    REWRITE_TAC[MLD_CHALLENGE_POS_ZERO] THEN ASM_REWRITE_TAC[ARITH_EQ];
    ALL_TAC] THEN
  MP_TAC(SPEC `7 + n` MLD_CHALLENGE_POS_SPLIT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(7 + n) + 1 = 8 + n`] THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ABBREV_TAC `b = (7 + n) DIV 136` THEN
  PC44_C_ABBREV_TAC THEN
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC PC44_EXEC (1--4) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600]) THEN
  PC44_C_CALL_TAC "H_PERM"
   [`read X0 s`; `keccak_squeeze (b + 1) (mld_shake256_state 32 C)`; `pc:num`; `read SP s`; `read X30 s`] 5 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PC_SQ_SUC2; READ_MEMORY_WBYTES_1600]) THEN
  PC_LOAD_FACTS_TAC "word_add fr (word 256)" "s5" [16,64; 16,80; 8,128; 16,96; 16,112; 16,0; 16,16; 16,32; 16,48] THEN
  ARM_STEPS_TAC PC44_EXEC (6--18);;

let PC44_C_SQUEEZE_CHAIN =
  PC_CHAIN_GEN "fr" "fr" 464 "val(keccak_squeeze (b + 2) (mld_shake256_state 32 C))" "s18" ([0,16;16,16;32,16;48,16;64,16;80,16;96,16;112,16;128,8]);;

let PC44_C_SQUEEZE_PRE = PC44_C_SQUEEZE_PRE0 THEN PC44_C_SQUEEZE_CHAIN;;

let PC44_C_BLOCK_FACT_TAC =
  MP_TAC(SPECL [`32`; `C:num`; `b + 1`; `136`] PC_BLOCK) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(b + 1) + 1 = b + 2`; ARITH_RULE `8 * 136 = 1088`] THEN
  DISCH_THEN(fun th1 ->
    FIRST_X_ASSUM(fun chain ->
      if is_eq(concl chain) && rhs(concl chain) = rhs(concl th1) &&
         can (term_match [] `read (memory :> bytes(a,136)) s`) (lhs(concl chain))
      then ASSUME_TAC(REWRITE_RULE[GSYM th1] chain) else NO_TAC));;

let PC44_C_SQUEEZE_TAC =
  PC44_C_SQUEEZE_PRE THEN
  SUBGOAL_THEN `136 * (b + 1) + 0 = 8 + n` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  PC44_C_BLOCK_FACT_TAC THEN
  MLD_CHALLENGE_LOAD_TAC PC44_C_BUF `0` [ASSUME `136 * (b + 1) + 0 = 8 + n`] THEN
  ARM_STEPS_TAC PC44_EXEC (19--22) THEN
  MLD_CHALLENGE_FIX_TAC (mld_challenge_is_read_reg `X8`) [GSYM WORD_ADD] THEN
  let next m =
    ARM_STEPS_TAC PC44_EXEC (m--(m+1)) THEN
    MLD_CHALLENGE_BRANCH_TAC THEN PC44_C_FINAL_TAC in
  (ASM_CASES_TAC `j <= 217 + k` THENL
   [MLD_CHALLENGE_BRANCH_TAC THEN PC44_C_ACCEPT_TAC 23 next;
    MLD_CHALLENGE_BRANCH_TAC THEN
    (SUBGOAL_THEN `~mld_poly_challenge_accept 39 (mld_shake256_byte 32 C) n` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    (SUBGOAL_THEN `n + 1 < mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    next 23]);;

let PC44_C_BODY_TAC =
  PC44_C_SETUP_TAC THEN
  ASM_CASES_TAC `(8 + n) MOD 136 = 0` THENL
   [PC44_C_SQUEEZE_TAC; PC44_C_NORMAL_TAC];;

let PC44_C_EXIT_TAC =
  FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[mld_poly_challenge] THEN
  EXISTS_TAC `e2:(uarch_event)list` THEN ASM_REWRITE_TAC[];;

let PC44_C_MAIN_TAC =
  PC44_C_INTRO_TAC THEN
  MLD_CHALLENGE_WHILE_TAC `mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C)` PC44_C_PCF `pc + mldsa44_poly_challenge_loop1_exit` PC44_C_INV THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MLD_POLY_CHALLENGE_BYTES_POS THEN ASM_REWRITE_TAC[ARITH_EQ];
    PC44_C_START_TAC;
    PC44_C_BODY_TAC;
    PC44_C_EXIT_TAC];;

let PC44_C = prove(PC44_C_TM, PC44_C_MAIN_TAC);;

(* The main lemma: from the stack check of the prologue to the end of the
   release of the state; fr = sp - 240 *)

let PC44_MAIN_TM = parse_term
 "!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e (c:int64) (seed:int64) (C:num) (guard:int64) (canary:int64) (fp:int64) (fr:int64) pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 16 (word_add fr (word 240)) /\\ aligned 32 (word_add fr (word 240)) /\\
          mld_poly_challenge_terminates 39 32 C /\\
          nonoverlapping (c,1024) (fr,624) /\\
          nonoverlapping (seed,32) (fr,624) /\\
          ALLPAIRS nonoverlapping
           [(c,1024); (fr,624)]
           [(word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                    read PC s = word (pc + mldsa44_poly_challenge_adrp1) /\\
                    read SP s = word_add fr (word 240) /\\ read X29 s = fp /\\
                    C_ARGUMENTS [c; seed] s /\\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\\
                    read (memory :> bytes64 guard) s = canary /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    read (memory :> bytes(seed,32)) s = C /\\
                    read events s = e)
               (\\s. read PC s = word (pc + mldsa44_poly_challenge_adrp2) /\\
                    read SP s = word_add fr (word 240) /\\ read X29 s = fp /\\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\\
                    read (memory :> bytes64 guard) s = canary /\\
                    read (memory :> bytes64(word_add fr (word 616))) s = canary /\\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add c (word(4 * i))))
                               s = mld_poly_challenge 39 32 C i) /\\
                    (exists e2.
                       read events s = APPEND e2 e /\\
                       e2 = f_events c seed C guard mf pc fr /\\
                       memaccess_inbounds e2
                        [seed,32; c,1024; fr,624;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [c,1024; fr,624]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
                MAYCHANGE [X19; X20; X21; X22; X23; X24; X25] ,,
                MAYCHANGE [memory :> bytes(c,1024); memory :> bytes(fr,624)])";;

let PC44_MAIN_ALLOWED = [`c:int64`; `seed:int64`; `C:num`; `guard:int64`; `mf:int64`; `pc:num`; `fr:int64`];;
let PC44_MAIN_CALL name ilist n =
  REMOVE_THEN name (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true (mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,PC44_EXEC,0x0,mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,th) (`e:(uarch_event)list`::ilist) n THENL
     [(FULL_EXISTS_E2_TAC (ref PC44_MAIN_ALLOWED) ORELSE PC_E2_TAC (ref PC44_MAIN_ALLOWED)); LABEL_TAC name th]);;

let PC44_MAIN_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPECL [`mf:int64`;`ea:int64`;`el:num`;`ev:num`] PC44_B) th) "H_B") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC PC44_A "H_A" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC PC44_C "H_C" THEN
  CONCRETIZE_F_EVENTS_TAC `\(c:int64) (seed:int64) (C:num) (guard:int64) (mf:int64) (pc:num) (fr:int64). f_ev_main c seed C guard mf pc fr:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `c:int64`; `seed:int64`; `C:num`; `guard:int64`; `canary:int64`; `fp:int64`; `fr:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(fun th -> (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) th THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)(REWRITE_RULE[NONOVERLAPPING_CLAUSES; fst PC44_EXEC] th)) THEN
  MAP_EVERY (fun g -> REWRITE_TAC[SPECL [`pc:num`; g] WORD_ADD] THEN RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; g] WORD_ADD])) [`got_stack_chk_guard:num`; `got_memset:num`] THEN
  FULL_INIT_TAC THEN
  PC44_MAIN_CALL "H_A" [`c:int64`; `seed:int64`; `C:num`; `guard:int64`; `canary:int64`; `word_add fr (word 240):int64`; `pc:num`] 1 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600]) THEN
  PC44_MAIN_CALL "H_B" [`c:int64`; `C:num`; `canary:int64`; `fr:int64`; `pc:num`] 2 THEN
  PC44_MAIN_CALL "H_C" [`c:int64`; `C:num`; `canary:int64`; `fr:int64`; `pc:num`] 3 THEN
  ARM_STEPS_TAC PC44_EXEC (4--21) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN PC_SAFETY_TAC;;

let PC44_MAIN = prove(PC44_MAIN_TM, PC44_MAIN_TAC);;

(* The whole function: the prologue realigns the stack pointer to 32 bytes,
   which gives two cases *)

let PC44_TOP_ALLOWED =
  [`c:int64`; `seed:int64`; `C:num`; `guard:int64`; `mf:int64`;
   `pc:num`; `stackpointer:int64`; `returnaddress:int64`];;

let PC44_TOP_TEMPLATE = parse_term
 "\\(c:int64) (seed:int64) (C:num) (guard:int64) (mf:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
    if aligned 32 stackpointer
    then f_ev_a c seed C guard mf pc stackpointer returnaddress
    else f_ev_u c seed C guard mf pc stackpointer returnaddress:(uarch_event)list";;

let PC44_NOV tm = SUBGOAL_THEN tm (fun th -> ASSUME_TAC th THEN ASSUME_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES] th)) THENL [NONOVERLAPPING_TAC; ALL_TAC];;

let PC44_TOP_PREFIX_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPECL [`mf:int64`;`ea:int64`;`el:num`;`ev:num`] PC44_MAIN) th) "H_MAIN") THEN
  CONCRETIZE_F_EVENTS_TAC PC44_TOP_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst PC44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 768):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun g -> REWRITE_TAC[SPECL [`pc:num`; g] WORD_ADD] THEN RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; g] WORD_ADD])) [`got_stack_chk_guard:num`; `got_memset:num`] THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init") (mk_const("X"^string_of_int n,[]))) ((19--25) @ [28;29]) THEN
  FULL_INIT_TAC;;

let PC44_TOP_CASE_TAC off =
  let mk s = parse_term(Printf.sprintf s off) in
  ARM_STEPS_TAC PC44_EXEC (1--8) THEN
  RULE_ASSUM_TAC(fun th -> if find_substring (string_of_term (concl th)) "18446744073709551584" <> None then th else th) THEN
  ALL_TAC;;

let PC44_TOP_ALIGNED_TAC =
  ARM_STEPS_TAC PC44_EXEC (1--8) THEN
  RULE_ASSUM_TAC(fun th -> if find_substring (string_of_term (concl th)) "18446744073709551584" <> None then REWRITE_RULE[] (REWRITE_RULE[MP (SPEC `stackpointer:int64` PC_ALIGN288) (ASSUME `aligned 16 (stackpointer:int64)`); ASSUME `aligned 32 (stackpointer:int64)`] th) else th) THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 288):int64)` ASSUME_TAC THENL [CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `aligned 32 (word_add stackpointer (word 288):int64)` ASSUME_TAC THENL [CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY PC44_NOV
   [`nonoverlapping (c:int64,1024) (word_add stackpointer (word 48):int64,624)`;
    `nonoverlapping (seed:int64,32) (word_add stackpointer (word 48):int64,624)`;
    `nonoverlapping (word_add stackpointer (word 48):int64,624) (word pc:int64,libmldsa_size)`;
    `nonoverlapping (word_add stackpointer (word 48):int64,624) (word_add (word pc) (word 327672):int64,8)`;
    `nonoverlapping (word_add stackpointer (word 48):int64,624) (guard:int64,8)`;
    `nonoverlapping (word_add stackpointer (word 48):int64,624) (word_add (word pc) (word 327656):int64,8)`;
    `nonoverlapping (word_add stackpointer (word 48):int64,624) (ea:int64,el)`;
    `nonoverlapping (c:int64,1024) (word_add (word pc) (word 327672):int64,8)`;
    `nonoverlapping (c:int64,1024) (word_add (word pc) (word 327656):int64,8)`] THEN
  REMOVE_THEN "H_MAIN" (fun th -> ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true (mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,PC44_EXEC,0x0,mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,th) [`e:(uarch_event)list`; `c:int64`; `seed:int64`; `C:num`; `guard:int64`; `canary:int64`; `read X29 s`; `word_sub (read SP s) (word 240)`; `pc:num`] 9 THENL [(FULL_EXISTS_E2_TAC (ref PC44_TOP_ALLOWED) ORELSE PC_E2_TAC (ref PC44_TOP_ALLOWED)); LABEL_TAC "H_MAIN" th]) THEN
  ARM_STEPS_TAC PC44_EXEC (10--10) THEN MLKEM_NATIVE_ADRP_TAC THEN ARM_STEPS_TAC PC44_EXEC (11--28) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN PC_SAFETY_TAC;;

let PC44_TOP_UNALIGNED_TAC =
  ARM_STEPS_TAC PC44_EXEC (1--8) THEN
  RULE_ASSUM_TAC(fun th -> if find_substring (string_of_term (concl th)) "18446744073709551584" <> None then REWRITE_RULE[] (REWRITE_RULE[MP (SPEC `stackpointer:int64` PC_ALIGN288) (ASSUME `aligned 16 (stackpointer:int64)`); EQF_INTRO(ASSUME `~aligned 32 (stackpointer:int64)`)] th) else th) THEN
  MP_TAC(MATCH_MP PC_ALIGN272 (CONJ (ASSUME `aligned 16 (stackpointer:int64)`) (ASSUME `~aligned 32 (stackpointer:int64)`))) THEN STRIP_TAC THEN
  MAP_EVERY PC44_NOV
   [`nonoverlapping (c:int64,1024) (word_add stackpointer (word 32):int64,624)`;
    `nonoverlapping (seed:int64,32) (word_add stackpointer (word 32):int64,624)`;
    `nonoverlapping (word_add stackpointer (word 32):int64,624) (word pc:int64,libmldsa_size)`;
    `nonoverlapping (word_add stackpointer (word 32):int64,624) (word_add (word pc) (word 327672):int64,8)`;
    `nonoverlapping (word_add stackpointer (word 32):int64,624) (guard:int64,8)`;
    `nonoverlapping (word_add stackpointer (word 32):int64,624) (word_add (word pc) (word 327656):int64,8)`;
    `nonoverlapping (word_add stackpointer (word 32):int64,624) (ea:int64,el)`;
    `nonoverlapping (c:int64,1024) (word_add (word pc) (word 327672):int64,8)`;
    `nonoverlapping (c:int64,1024) (word_add (word pc) (word 327656):int64,8)`] THEN
  REMOVE_THEN "H_MAIN" (fun th -> ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true (mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,PC44_EXEC,0x0,mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,th) [`e:(uarch_event)list`; `c:int64`; `seed:int64`; `C:num`; `guard:int64`; `canary:int64`; `read X29 s`; `word_sub (read SP s) (word 240)`; `pc:num`] 9 THENL [(FULL_EXISTS_E2_TAC (ref PC44_TOP_ALLOWED) ORELSE PC_E2_TAC (ref PC44_TOP_ALLOWED)); LABEL_TAC "H_MAIN" th]) THEN
  ARM_STEPS_TAC PC44_EXEC (10--10) THEN MLKEM_NATIVE_ADRP_TAC THEN ARM_STEPS_TAC PC44_EXEC (11--28) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN PC_SAFETY_TAC;;

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  PC44_TOP_PREFIX_TAC THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [PC44_TOP_ALIGNED_TAC; PC44_TOP_UNALIGNED_TAC]);;

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;
