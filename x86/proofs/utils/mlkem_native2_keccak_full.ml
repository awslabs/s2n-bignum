(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Correctness and constant-time/memory safety in one theorem ("FULL") for   *)
(* the Keccak-f1600 permutations of the x86 mlkem_native2,                   *)
(* sha3_keccak_f1600_alt2 (one state, in the image) and                      *)
(* sha3_keccak4_f1600_alt (four states), for callers that need both facts    *)
(* about the same final state, e.g. when their later control flow depends on *)
(* the permuted states. As arm/proofs/utils/mlkem_native2_keccak_full.ml for *)
(* AArch64, with the x86 forms of the code and the simulation.               *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native2_noise.ml";;

(* ------------------------------------------------------------------------- *)
(* The events of the safety theorems split off the end of a goal that also   *)
(* has the facts of the correctness theorems, the latter proved by ctac.     *)
(* ------------------------------------------------------------------------- *)

let EVENTS_SPLIT_TAC ctac (asl,w as gl) =
  let cs = conjuncts w in
  let ev = last cs in
  if not (is_exists ev) then failwith "EVENTS_SPLIT_TAC" else
  let rest = list_mk_conj(butlast cs) in
  let th = CONJ_ACI_RULE(mk_eq(w,mk_conj(rest,ev))) in
  (GEN_REWRITE_TAC I [th] THEN
   CONJ_TAC THENL
    [ctac; ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC]) gl;;

(* ------------------------------------------------------------------------- *)
(* The x1 permutation sha3_keccak_f1600_alt2: the proof of                   *)
(* SHA3_KECCAK_F1600_ALT2_CORRECT with the events of                         *)
(* SHA3_KECCAK_F1600_ALT2_SAFE added, the loop taken as in the latter, with  *)
(* the branch back in the body.                                              *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK_F1600_ALT2_FULL = time prove
 (`exists f_events.
    forall e a rc A pc tab.
        riprel32_within_bounds tab (pc + 7) /\
        nonoverlapping (a,200) (word pc,998) /\
        nonoverlapping (a,200) (word tab,384) /\
        nonoverlapping (a,200) (rc,192)
        ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   (sha3_keccak_f1600_alt2_tmc pc tab) /\
                 read RIP s = word pc /\
                 bytes_loaded s (word tab) sha3_keccak_f1600_alt2_data /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 wordlist_from_memory(a,25) s = A /\
                 read events s = e)
            (\s. read RIP s = word (pc + 997) /\
                 wordlist_from_memory(a,25) s = keccak 24 A /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a tab pc /\
                      memaccess_inbounds e2 [a,200; rc,192; word tab,384]
                      [a,200]))
            (MAYCHANGE [RIP; RAX; RCX; RSI] ,,
             MAYCHANGE
             [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9;
              ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
             MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes (a,200)])`,
  CONCRETIZE_F_EVENTS_TAC
   `\(rc:int64) (a:int64) (tab:num) (pc:num).
      APPEND (f_ev_epil rc a tab pc)
             (APPEND (ENUMERATEL 24 (\i. f_ev_loop rc a tab pc i))
                     (f_ev_prol rc a tab pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `rc:int64`; `A:int64 list`; `pc:num`; `tab:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SHA3_KECCAK_F1600_ALT2_DATA;
              SHA3_KECCAK_F1600_ALT2_DATA_NUM] THEN
  ASM_CASES_TAC `LENGTH(A:int64 list) = 25` THENL
   [ALL_TAC;
    ENSURES_INIT_TAC "s0" THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:int64 list->num`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[LENGTH; ARITH] THEN ASM_MESON_TAC[]] THEN

  (*** The invariant: the state after i rounds in the registers ***)

  ENSURES_EVENTS_WHILE_UP2_TAC `24` `pc + 0xdc` `pc + 0x328`
   `\i s. read RDI s = a /\
          read RSI s = word_add rc (word(8 * i)) /\
          read RAX s = word tab /\
          read RCX s = word(24 - i) /\
          read (memory :> bytes (word tab,384)) s =
          num_of_bytelist sha3_keccak_f1600_alt2_data /\
          wordlist_from_memory(rc,24) s = round_constants /\
          [read YMM0 s; read YMM1 s; read YMM2 s; read YMM3 s;
           read YMM4 s; read YMM5 s; read YMM6 s] =
          keccak_alt2_regs (keccak i A)` THEN
  REWRITE_TAC[SHA3_KECCAK_F1600_ALT2_DATA_NUM] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    (*** The initialization: the gathering of the state ***)

    REWRITE_TAC[round_constants;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(a,25) s:int64 list`] THEN
    MP_TAC(ISPEC `A:int64 list` LENGTH_EQ_25) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [th]) THEN
    REWRITE_TAC[CONS_11; GSYM CONJ_ASSOC; keccak] THEN
    ENSURES_INIT_TAC "s0" THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 2
      `read (memory :> bytes256(word_add a (word 8))) s0`) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MAP_EVERY (fun n -> X86_STEPS_TAC SHA3_KECCAK_F1600_ALT2_TMC_EXEC [n] THEN
                        KECCAK_AVX2_SIMPLIFY_TAC) (1--31) THEN
    ENSURES_FINAL_STATE_TAC THEN
    EVENTS_SPLIT_TAC
     (ASM_REWRITE_TAC[keccak_alt2_regs; CONS_11] THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
      REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
      IMP_REWRITE_TAC[RIP_REL_ADDR_FOLD] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[WORD_ADD] THEN
      REPEAT CONJ_TAC THEN BITBLAST_TAC);

    (*** A round, with the branch back or out ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[CONS_11; GSYM CONJ_ASSOC; keccak] THEN
    MP_TAC(ISPECL [`A:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[keccak_alt2_regs; keccak_round] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[CONS_11] THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[round_constants; CONS_11] o
      CONV_RULE(LAND_CONV WORDLIST_FROM_MEMORY_CONV) o
      check (can (term_match [] `wordlist_from_memory(rc,24) s = l`) o
             concl)) THEN
    SUBGOAL_THEN
     `read (memory :> bytes64(word_add rc (word(8 * i)))) s0 =
      EL i round_constants`
    ASSUME_TAC THENL
     [UNDISCH_TAC `i < 24` THEN SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[round_constants; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    KECCAK_AVX2_TABLE_TAC THEN
    MAP_EVERY (fun k ->
      ABBREV_TAC(mk_eq(mk_var("x"^string_of_int k,`:int64`),
        vsubst [mk_small_numeral k,`k:num`] `EL k (keccak i A):int64`)))
     (0--24) THEN
    (fun gl -> keccak_avx2_lanes := 0; ALL_TAC gl) THEN
    MAP_EVERY (fun n -> X86_STEPS_TAC SHA3_KECCAK_F1600_ALT2_TMC_EXEC [n] THEN
                        KECCAK_AVX2_SIMPLIFY_TAC THEN
                        KECCAK_AVX2_LANE_ABBREV_TAC n) (1--107) THEN
    ENSURES_FINAL_STATE_TAC THEN
    EVENTS_SPLIT_TAC
     (ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[round_constants; CONS_11;
        WORDLIST_FROM_MEMORY_CONV
         `wordlist_from_memory(rc,24) s107:int64 list`] THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
      ASM_SIMP_TAC[KECCAK_AVX2_COUNTER; KECCAK_AVX2_BRANCH] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < 24 ==> (~(i + 1 = 24) <=> i + 1 < 24)`] THEN
      CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      REWRITE_TAC[KECCAK_AVX2_JOIN_EQ; GSYM CONJ_ASSOC] THEN
      KECCAK_AVX2_EXPAND_TAC THEN
      REPEAT CONJ_TAC THEN KECCAK_BITBLAST_TAC);

    (*** The scattering of the state ***)

    REWRITE_TAC[keccak_alt2_regs; round_constants; CONS_11;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(a,25) s:int64 list`] THEN
    MP_TAC(ISPECL [`A:int64 list`; `24`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[CONS_11] THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC SHA3_KECCAK_F1600_ALT2_TMC_EXEC (1--28) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN
    ENSURES_FINAL_STATE_TAC THEN
    EVENTS_SPLIT_TAC
     (ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN BITBLAST_TAC)]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the IBT landing pad, as for        *)
(* SHA3_KECCAK_F1600_ALT2_NOIBT_SUBROUTINE_CORRECT and _SUBROUTINE_SAFE but  *)
(* with the frame of the former.                                             *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK_F1600_ALT2_NOIBT_SUBROUTINE_FULL = time prove
 (`exists f_events.
    forall e a rc A pc tab stackpointer returnaddress.
        riprel32_within_bounds tab (pc + 7) /\
        nonoverlapping (a,200) (word pc,998) /\
        nonoverlapping (a,200) (word tab,384) /\
        nonoverlapping (a,200) (rc,192) /\
        nonoverlapping (a,200) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   (sha3_keccak_f1600_alt2_tmc pc tab) /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 bytes_loaded s (word tab) sha3_keccak_f1600_alt2_data /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 wordlist_from_memory(a,25) s = A /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 wordlist_from_memory(a,25) s = keccak 24 A /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a tab pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,200; rc,192; word tab,384; stackpointer,8]
                      [a,200; stackpointer,8]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,200)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  REWRITE_TAC[SHA3_KECCAK_F1600_ALT2_DATA] THEN CONV_TAC TWEAK_CONV THEN
  X86_ADD_RETURN_NOSTACK_TAC SHA3_KECCAK_F1600_ALT2_TMC_EXEC
   (CONV_RULE TWEAK_CONV
     (REWRITE_RULE[SHA3_KECCAK_F1600_ALT2_DATA]
       SHA3_KECCAK_F1600_ALT2_FULL)) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let SHA3_KECCAK_F1600_ALT2_SUBROUTINE_FULL = time prove
 (`exists f_events.
    forall e a rc A pc tab stackpointer returnaddress.
        riprel32_within_bounds tab (pc + 11) /\
        nonoverlapping (a,200) (word pc,1002) /\
        nonoverlapping (a,200) (word tab,384) /\
        nonoverlapping (a,200) (rc,192) /\
        nonoverlapping (a,200) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) (sha3_keccak_f1600_alt2_mc pc tab) /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 bytes_loaded s (word tab) sha3_keccak_f1600_alt2_data /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 wordlist_from_memory(a,25) s = A /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 wordlist_from_memory(a,25) s = keccak 24 A /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a tab pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,200; rc,192; word tab,384; stackpointer,8]
                      [a,200; stackpointer,8]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,200)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   ~bridge:(Some SHA3_KECCAK_F1600_ALT2_MC_BRIDGE)
   (CONV_RULE TWEAK_CONV SHA3_KECCAK_F1600_ALT2_NOIBT_SUBROUTINE_FULL)));;

(* ------------------------------------------------------------------------- *)
(* In the image, as for SHA3_KECCAK_F1600_ALT2_IMAGE_CORRECT and             *)
(* SHA3_KECCAK_F1600_ALT2_IMAGE_SAFE, and with the state as a 1600-bit word  *)
(* as callers use it.                                                        *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK_F1600_ALT2_IMAGE_FULL = prove
 (`exists f_events.
    forall e a rc A pc stackpointer returnaddress.
       nonoverlapping (a,200) (word pc,mlkem_native2_image_size) /\
       nonoverlapping (a,200) (rc,192) /\
       nonoverlapping (a,200) (stackpointer,8)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + sha3_keccak_f1600_alt2) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 wordlist_from_memory(a,25) s = A /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 wordlist_from_memory(a,25) s = keccak 24 A /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,200; rc,192;
                       word(pc + sha3_keccak_f1600_alt2_rotations),384;
                       stackpointer,8]
                      [a,200; stackpointer,8]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,200)])`,
  X_CHOOSE_TAC
   `f:int64->int64->num->num->int64->int64->(uarch_event)list`
   SHA3_KECCAK_F1600_ALT2_SUBROUTINE_FULL THEN
  EXISTS_TAC
   `\(rc:int64) (a:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      (f:int64->int64->num->num->int64->int64->(uarch_event)list)
      rc a (pc + sha3_keccak_f1600_alt2_rotations)
      (pc + sha3_keccak_f1600_alt2) stackpointer returnaddress` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `rc:int64`; `A:int64 list`;
    `pc + sha3_keccak_f1600_alt2`; `pc + sha3_keccak_f1600_alt2_rotations`;
    `stackpointer:int64`; `returnaddress:int64`]) THEN
  REWRITE_TAC[MLKEM_NATIVE2_KECCAK_X1_MC; MLKEM_NATIVE2_KECCAK_X1_TABLES] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[riprel32_within_bounds; GSYM INT_OF_NUM_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_RED_CONV) THEN
    REPEAT CONJ_TAC THEN TRY INT_ARITH_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
  X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MLKEM_NATIVE2_KECCAK_X1_CODE_LOADED) THEN
    REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP MLKEM_NATIVE2_KECCAK_X1_TABLES_LOADED) THEN
    REWRITE_TAC[]]);;

let SHA3_KECCAK_F1600_ALT2_IMAGE_FULL_F1600 = prove
 (`exists f_events.
    forall e a rc (S:1600 word) pc stackpointer returnaddress.
       nonoverlapping (a,200) (word pc,mlkem_native2_image_size) /\
       nonoverlapping (a,200) (rc,192) /\
       nonoverlapping (a,200) (stackpointer,8)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + sha3_keccak_f1600_alt2) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 read (memory :> wbytes a) s = S /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 read (memory :> wbytes a) s = keccak_f1600 S /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,200; rc,192;
                       word(pc + sha3_keccak_f1600_alt2_rotations),384;
                       stackpointer,8]
                      [a,200; stackpointer,8]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,200)])`,
  MP_TAC SHA3_KECCAK_F1600_ALT2_IMAGE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `f:int64->int64->num->int64->int64->(uarch_event)list` THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `rc:int64`; `S:1600 word`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `rc:int64`;
    `wordlist_of_num 25 (val(S:1600 word)):int64 list`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[GSYM READ_MEMORY_WBYTES_KECCAK] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (ONCE_REWRITE_RULE[CONJ_SYM] ENSURES_POSTCONDITION_THM))) THEN
  MESON_TAC[KECCAK_F1600_MEMORY]);;

(* ------------------------------------------------------------------------- *)
(* The x4 permutation sha3_keccak4_f1600_alt: the proof of                   *)
(* SHA3_KECCAK4_F1600_ALT_CORRECT with the events, the loop taken from the   *)
(* start of a round to the end of the branch back, the flag of the branch    *)
(* being given by its counter in KECCAK4_BRANCH.                             *)
(* ------------------------------------------------------------------------- *)

let KECCAK4_BRANCH = prove
 (`!i. i < 24
       ==> (~(val(word_add (word i) (word 18446744073709551593):int64) = 0) <=>
            i + 1 < 24)`,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)));;

let SHA3_KECCAK4_F1600_ALT_FULL = time prove
 (`exists f_events.
   forall e rc_pointer:int64 bitstate_in:int64 rho8_ptr:int64 rho56_ptr:int64
          A1 A2 A3 A4 pc:num stackpointer:int64.
  PAIRWISE (nonoverlapping_modulo (2 EXP 64))
  [(pc, 0x9d9);
   (val stackpointer, 0x300);
   (val bitstate_in, 800);
   (val rc_pointer, 192);
   (val rho8_ptr, 32);
   (val rho56_ptr, 32)]
  ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST sha3_keccak4_f1600_alt_tmc) /\
              read RIP s = word (pc + 0xe) /\
              read RSP s = stackpointer /\
              read RDI s = bitstate_in /\
              C_ARGUMENTS [bitstate_in; rc_pointer; rho8_ptr; rho56_ptr] s /\
              wordlist_from_memory(rc_pointer,24) s = round_constants /\
              wordlist_from_memory(rho8_ptr,4) s = rho8_constant /\
              wordlist_from_memory(rho56_ptr,4) s = rho56_constant /\
              wordlist_from_memory(bitstate_in,25) s = A1 /\
              wordlist_from_memory(word_add bitstate_in (word 200),25) s =
              A2 /\
              wordlist_from_memory(word_add bitstate_in (word 400),25) s =
              A3 /\
              wordlist_from_memory(word_add bitstate_in (word 600),25) s =
              A4 /\
              read events s = e)
         (\s. read RIP s = word(pc + 0x9d5) /\
              wordlist_from_memory(bitstate_in,25) s = keccak 24 A1 /\
              wordlist_from_memory(word_add bitstate_in (word 200),25) s =
              keccak 24 A2 /\
              wordlist_from_memory(word_add bitstate_in (word 400),25) s =
              keccak 24 A3 /\
              wordlist_from_memory(word_add bitstate_in (word 600),25) s =
              keccak 24 A4 /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events rc_pointer rho8_ptr rho56_ptr bitstate_in pc
                               stackpointer /\
                 memaccess_inbounds e2
                   [bitstate_in,800; rc_pointer,192; rho8_ptr,32;
                    rho56_ptr,32; stackpointer,768]
                   [bitstate_in,800; stackpointer,768]))
         (MAYCHANGE [RIP; R10; RSI] ,,
          MAYCHANGE[ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8;
                    ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes (stackpointer, 0x300)] ,,
          MAYCHANGE [memory :> bytes (bitstate_in, 800)])`,
  REWRITE_TAC[SOME_FLAGS] THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rc_pointer:int64) (rho8_ptr:int64) (rho56_ptr:int64)
     (bitstate_in:int64) (pc:num) (stackpointer:int64).
      APPEND (f_ev_epil rc_pointer rho8_ptr rho56_ptr bitstate_in pc
                        stackpointer)
       (APPEND (ENUMERATEL 24 (\i. f_ev_loop rc_pointer rho8_ptr rho56_ptr
                                    bitstate_in pc stackpointer i))
               (f_ev_prol rc_pointer rho8_ptr rho56_ptr bitstate_in pc
                          stackpointer)) :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`rc_pointer:int64`; `bitstate_in:int64`; `rho8_ptr:int64`;
    `rho56_ptr:int64`; `A1:int64 list`; `A2:int64 list`; `A3:int64 list`;
    `A4:int64 list`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[PAIRWISE; C_ARGUMENTS; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `LENGTH(A1:int64 list) = 25 /\
                 LENGTH(A2:int64 list) = 25 /\
                 LENGTH(A3:int64 list) = 25 /\
                 LENGTH(A4:int64 list) = 25` THENL
   [ALL_TAC;
    ENSURES_INIT_TAC "s0" THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:int64 list->num`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[LENGTH; ARITH] THEN ASM_MESON_TAC[]] THEN

  (*** The invariant of the correctness proof but for the flag ***)

  ENSURES_EVENTS_WHILE_UP2_TAC `24` `pc + 0x26f` `pc + 0x771`
  `\i s.
      read R10 s = word i /\
      read RDI s = bitstate_in /\
      read RSP s = stackpointer /\
      read RDX s = rho8_ptr /\
      read RCX s = rho56_ptr /\
      read RSI s = word_add rc_pointer (word (8 * i)) /\
      wordlist_from_memory(rho8_ptr,4) s = rho8_constant /\
      wordlist_from_memory(rho56_ptr,4) s = rho56_constant /\
      wordlist_from_memory(rc_pointer,24) s = round_constants /\
      (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND
       (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND
       (wordlist_from_memory(word_add stackpointer (word 0x0),7) s)
       (CONS (read YMM10 s) []))
       (CONS (read YMM14 s) []))
       (wordlist_from_memory(word_add stackpointer (word 0xe0),2) s))
       (CONS (read YMM8 s) []))
       (CONS (read YMM15 s) []))
       (wordlist_from_memory(word_add stackpointer (word 0x120),2) s))
       (CONS (read YMM9 s) []))
       (wordlist_from_memory(word_add stackpointer (word 0x160),2) s))
       (CONS (read YMM13 s) []))
       (wordlist_from_memory(word_add stackpointer (word 0x1a0),2) s))
       (CONS (read YMM3 s) []))
       (CONS (read YMM7 s) []))
       (wordlist_from_memory(word_add stackpointer (word 0x1e0),1) s))
       (CONS (read YMM2 s) [])) =
      (MAP2 word_join
        ((MAP2 word_join (keccak i A4) (keccak i A3)):int128 list)
        ((MAP2 word_join (keccak i A2) (keccak i A1)):int128 list))
      :int256 list` THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    (*** The initialization ***)

    REWRITE_TAC[rho56_constant; rho8_constant; round_constants;
                GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV
                  `wordlist_from_memory(rc_pointer,24) s:int64 list`;
                WORDLIST_FROM_MEMORY_CONV
                  `wordlist_from_memory(bitstate_in,100) s:int64 list`;
                WORDLIST_FROM_MEMORY_CONV
                  `wordlist_from_memory(rho8_ptr,4) s:int64 list`;
                WORDLIST_FROM_MEMORY_CONV
                  `wordlist_from_memory(rho56_ptr,4) s:int64 list`] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[APPEND] THEN
    ENSURES_INIT_TAC "s0" THEN
    BIGNUM_DIGITIZE_TAC "A_"
     `read (memory :> bytes (bitstate_in,8 * 100)) s0` THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 0 25 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 200 25 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 400 25 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 600 25 THEN
    MEMORY_256_FROM_64_TAC "rho8_ptr" 0 4 THEN
    MEMORY_256_FROM_64_TAC "rho56_ptr" 0 4 THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN
    REPEAT STRIP_TAC THEN
    X86_STEPS_TAC SHA3_KECCAK4_F1600_ALT_EXEC (1--96) THEN
    ENSURES_FINAL_STATE_TAC THEN
    EVENTS_SPLIT_TAC
     (ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [PURE_ONCE_REWRITE_TAC[ARITH_RULE `8 * 0 = 0`] THEN
        REWRITE_TAC[WORD_ADD_0];
        ASM_REWRITE_TAC [WORD_SUBWORD_JOIN_EXTRACT_64] THEN
        ASM_REWRITE_TAC [WORD_SUBWORD_JOIN_EXTRACT_128] THEN
        EXPAND_TAC "A1" THEN EXPAND_TAC "A2" THEN
        EXPAND_TAC "A3" THEN EXPAND_TAC "A4" THEN
        REWRITE_TAC[keccak] THEN REWRITE_TAC[MAP2] THEN
        REWRITE_TAC[CONS_11] THEN CONV_TAC WORD_BLAST]);

    (*** A round, with the branch back or out ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[rho56_constant; rho8_constant; round_constants;
                GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV
                  `wordlist_from_memory(rc_pointer,24) s:int64 list`;
                WORDLIST_FROM_MEMORY_CONV
                  `wordlist_from_memory(bitstate_in,100) s:int64 list`;
                WORDLIST_FROM_MEMORY_CONV
                  `wordlist_from_memory(rho8_ptr,1) s:int256 list`;
                WORDLIST_FROM_MEMORY_CONV
                  `wordlist_from_memory(rho56_ptr,1) s:int256 list`] THEN
    REWRITE_TAC[APPEND] THEN
    MP_TAC(ISPECL [`A1:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A2:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A3:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A4:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[MAP2; CONS_11; GSYM CONJ_ASSOC] THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN
     `read (memory :> bytes64(word_add rc_pointer (word(8 * i)))) s0 =
      EL i round_constants`
    ASSUME_TAC THENL
     [UNDISCH_TAC `i < 24` THEN SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[round_constants; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC [WORD_SUBWORD_JOIN_EXTRACT_64] THEN
    ASM_REWRITE_TAC [WORD_SUBWORD_JOIN_EXTRACT_128] THEN
    BIGNUM_DIGITIZE_TAC "A_"
     `read (memory :> bytes (bitstate_in,8 * 100)) s0` THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 0 25 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 200 25 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 400 25 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 600 25 THEN
    MEMORY_256_FROM_64_TAC "rho8_ptr" 0 4 THEN
    MEMORY_256_FROM_64_TAC "rho56_ptr" 0 4 THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN REPEAT STRIP_TAC THEN
    X86_STEPS_TAC SHA3_KECCAK4_F1600_ALT_EXEC (1--224) THEN
    ENSURES_FINAL_STATE_TAC THEN
    EVENTS_SPLIT_TAC
     (ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[KECCAK4_BRANCH] THEN
      REPEAT CONJ_TAC THENL
       [COND_CASES_TAC THEN REWRITE_TAC[];
        REWRITE_TAC[WORD_ADD];
        CONV_TAC WORD_BLAST;
        REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE]) THEN
        REWRITE_TAC[keccak; keccak_round] THEN
        CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        REWRITE_TAC[MAP2; CONS_11] THEN
        CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THEN BITBLAST_TAC]);

    (*** The tail of logical not operation and writeback ***)

    REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV
                  `wordlist_from_memory(rc_pointer,24) s:int64 list`;
                WORDLIST_FROM_MEMORY_CONV
                  `wordlist_from_memory(bitstate_in,100) s:int64 list`;
                WORDLIST_FROM_MEMORY_CONV
                  `wordlist_from_memory(rho8_ptr,1) s:int256 list`;
                WORDLIST_FROM_MEMORY_CONV
                  `wordlist_from_memory(rho56_ptr,1) s:int256 list`] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[APPEND] THEN
    MP_TAC(ISPECL [`A1:int64 list`; `24:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A2:int64 list`; `24:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A3:int64 list`; `24:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A4:int64 list`; `24:num`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[MAP2; CONS_11; GSYM CONJ_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC [keccak; keccak_round] THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC SHA3_KECCAK4_F1600_ALT_EXEC (1--95) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ENSURES_FINAL_STATE_TAC THEN
    EVENTS_SPLIT_TAC
     (ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN BITBLAST_TAC)]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the IBT landing pad, as for        *)
(* SHA3_KECCAK4_F1600_ALT_NOIBT_SUBROUTINE_CORRECT and _SUBROUTINE_SAFE: the *)
(* core runs with the stack pointer aligned down to a multiple of 32, at     *)
(* some offset delta <= 31 within the 0x31f bytes below the return address;  *)
(* and with the states as 1600-bit words as callers use them.                *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK4_F1600_ALT_NOIBT_SUBROUTINE_FULL = time prove
 (`exists f_events.
     forall e rc_pointer bitstate_in rho8_ptr rho56_ptr A1 A2 A3 A4 pc
            stackpointer returnaddress.
       PAIRWISE (nonoverlapping_modulo (2 EXP 64))
         [(pc, LENGTH sha3_keccak4_f1600_alt_tmc);
          (val (word_sub stackpointer (word 0x31f)), 0x31f);
          (val bitstate_in, 800);
          (val rc_pointer, 192);
          (val rho8_ptr, 32);
          (val rho56_ptr, 32)] /\
       nonoverlapping_modulo (2 EXP 64)
         (val bitstate_in, 800)
         (val (word_sub stackpointer (word 0x31f)), 0x31f + 8)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_alt_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [bitstate_in; rc_pointer; rho8_ptr; rho56_ptr]
                             s /\
                 wordlist_from_memory(rc_pointer, 24) s = round_constants /\
                 wordlist_from_memory(rho8_ptr, 4) s = rho8_constant /\
                 wordlist_from_memory(rho56_ptr, 4) s = rho56_constant /\
                 wordlist_from_memory(bitstate_in, 25) s = A1 /\
                 wordlist_from_memory(word_add bitstate_in (word 200), 25) s =
                 A2 /\
                 wordlist_from_memory(word_add bitstate_in (word 400), 25) s =
                 A3 /\
                 wordlist_from_memory(word_add bitstate_in (word 600), 25) s =
                 A4 /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 wordlist_from_memory(bitstate_in, 25) s = keccak 24 A1 /\
                 wordlist_from_memory(word_add bitstate_in (word 200), 25) s =
                 keccak 24 A2 /\
                 wordlist_from_memory(word_add bitstate_in (word 400), 25) s =
                 keccak 24 A3 /\
                 wordlist_from_memory(word_add bitstate_in (word 600), 25) s =
                 keccak 24 A4 /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events rc_pointer rho8_ptr rho56_ptr bitstate_in pc
                                  stackpointer returnaddress /\
                    memaccess_inbounds e2
                      [bitstate_in,800; rc_pointer,192; rho8_ptr,32;
                       rho56_ptr,32; word_sub stackpointer (word 0x31f),0x327]
                      [bitstate_in,800;
                       word_sub stackpointer (word 0x31f),0x31f]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes (bitstate_in, 800);
                        memory :> bytes(word_sub stackpointer (word 0x31f),
                                        0x31f)])`,
  let execth = SHA3_KECCAK4_F1600_ALT_FULL_EXEC in
  X_CHOOSE_THEN
   `inner_f_events:int64->int64->int64->int64->num->int64->uarch_event list`
   (LABEL_TAC "INNER_FULL") SHA3_KECCAK4_F1600_ALT_FULL THEN
  EXISTS_TAC
   `\(rc_pointer:int64) (rho8_ptr:int64) (rho56_ptr:int64)
     (bitstate_in:int64) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
       CONS (EventJump (word(pc + 0x9d9):int64,returnaddress))
        (CONS (EventLoad (stackpointer,8))
          (inner_f_events rc_pointer rho8_ptr rho56_ptr bitstate_in pc
             (word_sub (word_and stackpointer (word 0xffffffffffffffe0))
                       (word 0x300)))):uarch_event list` THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              fst execth] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  STRIP_TAC THEN

  (*** The alignment, and the core with the aligned stack pointer ***)

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC execth (1--3) THEN
  SUBGOAL_THEN
   `?delta. delta <= 31 /\
            word_sub (word_and stackpointer (word 0xffffffffffffffe0))
                     (word 0x300):int64 =
            word_add (word_sub stackpointer (word 0x31f)) (word delta)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC
     `val(word_sub (word 31) (word_and stackpointer (word 31)):int64)` THEN
    CONJ_TAC THEN CONV_TAC BITBLAST_RULE;
    ALL_TAC] THEN
  FIRST_ASSUM SUBST_ALL_TAC THEN
  USE_THEN "INNER_FULL" (fun th ->
    MP_TAC(SPECL
     [`e:uarch_event list`; `rc_pointer:int64`; `bitstate_in:int64`;
      `rho8_ptr:int64`; `rho56_ptr:int64`;
      `A1:int64 list`; `A2:int64 list`; `A3:int64 list`; `A4:int64 list`;
      `pc:num`;
      `word_add (word_sub stackpointer (word 0x31f)) (word delta):int64`]
     th)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
    REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if (try lhand(concl th) = `read events s3:uarch_event list`
        with Failure _ -> false)
    then SUBST1_TAC th else NO_TAC) THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  X86_BIGSTEP_TAC execth "s4" THENL
   [REWRITE_TAC[C_ARGUMENTS] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BYTES_LOADED_BUTLAST THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X86_STEPS_TAC execth (5--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** The memory accesses: the load of the return address, within the
   *** region of the stack, and those of the core, within the frame
   ***)

  EXISTS_TAC
   `CONS (EventJump (word (pc + 0x9d9):int64,returnaddress:int64))
     (CONS (EventLoad (stackpointer:int64,8))
       ((inner_f_events:int64->int64->int64->int64->num->int64->
                        uarch_event list)
          rc_pointer rho8_ptr rho56_ptr bitstate_in pc
          (word_add (word_sub stackpointer (word 0x31f)) (word delta))))` THEN
  REWRITE_TAC[APPEND] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhand(concl th) = `e2:uarch_event list` with Failure _ -> false)
    then SUBST_ALL_TAC th else NO_TAC) THEN
  REWRITE_TAC[memaccess_inbounds; ALL] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`word_sub stackpointer (word 0x31f):int64`; `0x31f`; `8`;
                   `0x327`] KECCAK4_FRAME_CONTAINED) THEN
    REWRITE_TAC[contained; DIMINDEX_64; WORD_RULE
      `word_add (word_sub x (word 0x31f)) (word 0x31f):int64 = x`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN ASM_REWRITE_TAC[EX];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM memaccess_inbounds] THEN
  MATCH_MP_TAC(REWRITE_RULE[GSYM IMP_CONJ_ALT]
    MEMACCESS_INBOUNDS_CONTAINED) THEN
  MAP_EVERY EXISTS_TAC
   [`[bitstate_in:int64,800; rc_pointer,192; rho8_ptr,32; rho56_ptr,32;
      word_add (word_sub stackpointer (word 0x31f)) (word delta),768]`;
    `[bitstate_in:int64,800;
      word_add (word_sub stackpointer (word 0x31f)) (word delta),768]`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `contained
     (word_add (word_sub stackpointer (word 0x31f)) (word delta):int64,768)
     (word_sub stackpointer (word 0x31f),0x327) /\
    contained
     (word_add (word_sub stackpointer (word 0x31f)) (word delta):int64,768)
     (word_sub stackpointer (word 0x31f),0x31f)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC KECCAK4_FRAME_CONTAINED THEN
    UNDISCH_TAC `delta <= 31` THEN ARITH_TAC;
    ASM_REWRITE_TAC[ALL; EX; KECCAK4_CONTAINED_REFL]]);;

let SHA3_KECCAK4_F1600_ALT_SUBROUTINE_FULL = time prove
 (`exists f_events.
     forall e rc_pointer bitstate_in rho8_ptr rho56_ptr A1 A2 A3 A4 pc
            stackpointer returnaddress.
       PAIRWISE (nonoverlapping_modulo (2 EXP 64))
         [(pc, LENGTH sha3_keccak4_f1600_alt_mc);
          (val (word_sub stackpointer (word 0x31f)), 0x31f);
          (val bitstate_in, 800);
          (val rc_pointer, 192);
          (val rho8_ptr, 32);
          (val rho56_ptr, 32)] /\
       nonoverlapping_modulo (2 EXP 64)
         (val bitstate_in, 800)
         (val (word_sub stackpointer (word 0x31f)), 0x31f + 8)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_alt_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [bitstate_in; rc_pointer; rho8_ptr; rho56_ptr]
                             s /\
                 wordlist_from_memory(rc_pointer, 24) s = round_constants /\
                 wordlist_from_memory(rho8_ptr, 4) s = rho8_constant /\
                 wordlist_from_memory(rho56_ptr, 4) s = rho56_constant /\
                 wordlist_from_memory(bitstate_in, 25) s = A1 /\
                 wordlist_from_memory(word_add bitstate_in (word 200), 25) s =
                 A2 /\
                 wordlist_from_memory(word_add bitstate_in (word 400), 25) s =
                 A3 /\
                 wordlist_from_memory(word_add bitstate_in (word 600), 25) s =
                 A4 /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 wordlist_from_memory(bitstate_in, 25) s = keccak 24 A1 /\
                 wordlist_from_memory(word_add bitstate_in (word 200), 25) s =
                 keccak 24 A2 /\
                 wordlist_from_memory(word_add bitstate_in (word 400), 25) s =
                 keccak 24 A3 /\
                 wordlist_from_memory(word_add bitstate_in (word 600), 25) s =
                 keccak 24 A4 /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events rc_pointer rho8_ptr rho56_ptr bitstate_in pc
                                  stackpointer returnaddress /\
                    memaccess_inbounds e2
                      [bitstate_in,800; rc_pointer,192; rho8_ptr,32;
                       rho56_ptr,32; word_sub stackpointer (word 0x31f),0x327]
                      [bitstate_in,800;
                       word_sub stackpointer (word 0x31f),0x31f]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes (bitstate_in, 800);
                        memory :> bytes(word_sub stackpointer (word 0x31f),
                                        0x31f)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV NUM_ADD_CONV THENC
                   REWRITE_CONV[PAIRWISE; ALL] THENC
                   ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
    (CONV_RULE TWEAK_CONV SHA3_KECCAK4_F1600_ALT_NOIBT_SUBROUTINE_FULL)));;

let SHA3_KECCAK4_F1600_ALT_SUBROUTINE_FULL_F1600 = prove
 (`exists f_events.
     forall e rc_pointer bitstate_in rho8_ptr rho56_ptr
            (S1:1600 word) (S2:1600 word) (S3:1600 word) (S4:1600 word)
            pc stackpointer returnaddress.
       PAIRWISE (nonoverlapping_modulo (2 EXP 64))
         [(pc, LENGTH sha3_keccak4_f1600_alt_mc);
          (val (word_sub stackpointer (word 0x31f)), 0x31f);
          (val bitstate_in, 800);
          (val rc_pointer, 192);
          (val rho8_ptr, 32);
          (val rho56_ptr, 32)] /\
       nonoverlapping_modulo (2 EXP 64)
         (val bitstate_in, 800)
         (val (word_sub stackpointer (word 0x31f)), 0x31f + 8)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_alt_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [bitstate_in; rc_pointer; rho8_ptr; rho56_ptr]
                             s /\
                 wordlist_from_memory(rc_pointer, 24) s = round_constants /\
                 wordlist_from_memory(rho8_ptr, 4) s = rho8_constant /\
                 wordlist_from_memory(rho56_ptr, 4) s = rho56_constant /\
                 read (memory :> wbytes bitstate_in) s = S1 /\
                 read (memory :> wbytes(word_add bitstate_in (word 200))) s =
                 S2 /\
                 read (memory :> wbytes(word_add bitstate_in (word 400))) s =
                 S3 /\
                 read (memory :> wbytes(word_add bitstate_in (word 600))) s =
                 S4 /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 read (memory :> wbytes bitstate_in) s = keccak_f1600 S1 /\
                 read (memory :> wbytes(word_add bitstate_in (word 200))) s =
                 keccak_f1600 S2 /\
                 read (memory :> wbytes(word_add bitstate_in (word 400))) s =
                 keccak_f1600 S3 /\
                 read (memory :> wbytes(word_add bitstate_in (word 600))) s =
                 keccak_f1600 S4 /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events rc_pointer rho8_ptr rho56_ptr bitstate_in pc
                                  stackpointer returnaddress /\
                    memaccess_inbounds e2
                      [bitstate_in,800; rc_pointer,192; rho8_ptr,32;
                       rho56_ptr,32; word_sub stackpointer (word 0x31f),0x327]
                      [bitstate_in,800;
                       word_sub stackpointer (word 0x31f),0x31f]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes (bitstate_in, 800);
                        memory :> bytes(word_sub stackpointer (word 0x31f),
                                        0x31f)])`,
  MP_TAC SHA3_KECCAK4_F1600_ALT_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC
   `f:int64->int64->int64->int64->num->int64->int64->(uarch_event)list` THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `rc_pointer:int64`; `bitstate_in:int64`;
    `rho8_ptr:int64`; `rho56_ptr:int64`; `S1:1600 word`; `S2:1600 word`;
    `S3:1600 word`; `S4:1600 word`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `rc_pointer:int64`; `bitstate_in:int64`;
    `rho8_ptr:int64`; `rho56_ptr:int64`;
    `wordlist_of_num 25 (val(S1:1600 word)):int64 list`;
    `wordlist_of_num 25 (val(S2:1600 word)):int64 list`;
    `wordlist_of_num 25 (val(S3:1600 word)):int64 list`;
    `wordlist_of_num 25 (val(S4:1600 word)):int64 list`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[GSYM READ_MEMORY_WBYTES_KECCAK] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (ONCE_REWRITE_RULE[CONJ_SYM] ENSURES_POSTCONDITION_THM))) THEN
  MESON_TAC[KECCAK_F1600_MEMORY]);;
