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
(* The x1 permutation sha3_keccak_f1600_alt2: SHA3_KECCAK_F1600_ALT2_FULL is *)
(* proved in ../sha3_keccak_f1600_alt2.ml, its correctness theorem following *)
(* from it.                                                                  *)
(* ------------------------------------------------------------------------- *)

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
(* The x4 permutation sha3_keccak4_f1600_alt: SHA3_KECCAK4_F1600_ALT_FULL is *)
(* proved in ../sha3_keccak4_f1600_alt.ml, its correctness theorem following *)
(* from it.                                                                  *)
(* ------------------------------------------------------------------------- *)

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
       CONS (EventJump (word(pc + 0x9ca):int64,returnaddress))
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
   `CONS (EventJump (word (pc + 0x9ca):int64,returnaddress:int64))
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
