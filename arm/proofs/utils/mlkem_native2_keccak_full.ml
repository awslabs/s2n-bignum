(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Correctness and constant-time/memory safety in one theorem ("FULL") for   *)
(* the Keccak-f1600 permutations sha3_keccak_f1600 (one state) and           *)
(* sha3_keccak4_f1600_alt2 (four states), for callers that need both facts   *)
(* about the same final state, e.g. when their later control flow depends on *)
(* the permuted states.                                                      *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native2_noise.ml";;

(* ------------------------------------------------------------------------- *)
(* The tactics for the events in the loop proofs (BRANCH_COND_TAC,           *)
(* KECCAK_EVENTS_INIT_TAC and KECCAK_EVENTS_BODY_TAC) are in                 *)
(* ../sha3_keccak4_f1600_alt2.ml, with the proof of                          *)
(* SHA3_KECCAK4_F1600_ALT2_FULL, the core of the x4 code, from which its     *)
(* correctness theorem follows.                                              *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The core, from SHA3_KECCAK_F1600_CORRECT with the events of               *)
(* SHA3_KECCAK_F1600_SAFE_FRAMED. Unlike the correctness proof, the loop     *)
(* body ends after the branch back, whose event would otherwise make the     *)
(* invariant differ between the two ends of the loop-back step.              *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK_F1600_FULL = time prove
 (`exists f_events.
     forall e a rc A pc stackpointer.
      aligned 16 stackpointer /\
      nonoverlapping (a,200) (stackpointer,32) /\
      ALLPAIRS nonoverlapping
               [(a,200); (stackpointer,32)]
               [(word pc,0x480); (rc,192)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) sha3_keccak_f1600_mc /\
                read PC s = word (pc + 0x1c) /\
                read SP s = stackpointer /\
                C_ARGUMENTS [a; rc] s /\
                wordlist_from_memory(a,25) s = A /\
                wordlist_from_memory(rc,24) s = round_constants /\
                read events s = e)
           (\s. read PC s = word(pc + 0x460) /\
                wordlist_from_memory(a,25) s = keccak 24 A /\
                (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events rc a pc stackpointer /\
                    memaccess_inbounds e2
                    [a,200; rc,192; stackpointer,32]
                    [a,200; stackpointer,32]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [X19; X20; X21; X22; X23; X24;
                       X25; X26; X27; X28; X29; X30] ,,
            MAYCHANGE [memory :> bytes(a,200);
                       memory :> bytes(stackpointer,32)])`,
  CONCRETIZE_F_EVENTS_TAC
   `\(rc:int64) (a:int64) (pc:num) (stackpointer:int64).
      APPEND (f_ev_tail rc a pc stackpointer)
       (APPEND (ENUMERATEL 23 (\i. f_ev_body rc a pc stackpointer i))
               (f_ev_init rc a pc stackpointer)) :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `rc:int64`; `A:int64 list`; `pc:num`;
    `stackpointer:int64`] THEN
  REWRITE_TAC[fst SHA3_KECCAK_F1600_EXEC] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Set up the loop invariant ***)

  ENSURES_WHILE_AUP2_TAC `1` `24` `pc + 0x208` `pc + 0x3cc`
   `\i s.
      (read SP s = stackpointer /\
       wordlist_from_memory(rc,24) s = round_constants /\
       read (memory :> bytes64 stackpointer) s = a /\
       read (memory :> bytes64(word_add stackpointer (word 8))) s = rc /\
       read (memory :> bytes64(word_add stackpointer (word 16))) s = word i /\
       MAP2 word_rol
        [read X1 s; read X6 s; read X11 s; read X16 s; read X21 s;
         read X2 s; read X7 s; read X12 s; read X17 s; read X22 s;
         read X3 s; read X8 s; read X13 s; read X28 s; read X23 s;
         read X4 s; read X9 s; read X14 s; read X19 s; read X24 s;
         read X5 s; read X10 s; read X15 s; read X20 s; read X25 s]
        deferred_rotates = keccak i A) /\
      (exists e2.
         read events s = APPEND e2 e /\
         e2 = APPEND (ENUMERATEL (i - 1)
                       (\i. f_ev_body rc a (pc:num) stackpointer i))
                     (f_ev_init rc a pc stackpointer) /\
         memaccess_inbounds e2
          [a,200; rc,192; stackpointer,32] [a,200; stackpointer,32])` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial holding of the invariant ***)

    REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC;
     WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`] THEN
    ENSURES_INIT_TAC "s0" THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (a,8 * 25)) s0` THEN
    FIRST_ASSUM(MP_TAC o CONV_RULE(LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC SHA3_KECCAK_F1600_EXEC (1--123) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "A" THEN
      SUBST1_TAC(MESON[ADD_CLAUSES] `keccak 1 = keccak (0 + 1)`) THEN
      REWRITE_TAC[keccak; round_constants; EL; HD] THEN
      REWRITE_TAC[keccak_round] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[deferred_rotates; MAP2] THEN REWRITE_TAC[CONS_11] THEN
      REPEAT CONJ_TAC THEN KECCAK_BITBLAST_TAC;
      KECCAK_EVENTS_INIT_TAC];

    (*** Preservation of the invariant, with the branch back or out ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ABBREV_TAC `j = i - 1` THEN
    SUBGOAL_THEN `(i + 1) - 1 = j + 1` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`i - 1 = j`; `1 <= i`] THEN ARITH_TAC;
      ALL_TAC] THEN
    VAL_INT64_TAC `i:num` THEN
    GHOST_REGLIST_TAC THEN
    REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC;
     WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`] THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN

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

    ARM_STEPS_TAC SHA3_KECCAK_F1600_EXEC (1--113) THEN
    BRANCH_COND_TAC `s113:armstate` `i + 1 < 24`
     (UNDISCH_TAC `i < 24` THEN SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN REFL_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_ARITH; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[keccak] THEN FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[deferred_rotates; MAP2] THEN
      REWRITE_TAC[keccak_round] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[deferred_rotates; MAP2] THEN REWRITE_TAC[CONS_11] THEN
      REPEAT CONJ_TAC THEN KECCAK_BITBLAST_TAC;
      KECCAK_EVENTS_BODY_TAC];

    (*** The tail of deferred rotations and writeback ***)

    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    GHOST_REGLIST_TAC THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      SHA3_KECCAK_F1600_EXEC (1--37) THEN
    CONJ_TAC THENL
     [CONV_TAC(LAND_CONV WORDLIST_FROM_MEMORY_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      REWRITE_TAC[deferred_rotates; MAP2; CONS_11] THEN
      REPEAT CONJ_TAC THEN KECCAK_BITBLAST_TAC;
      DISCHARGE_SAFETY_PROPERTY_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine, with the saving of registers and the return, as for       *)
(* SHA3_KECCAK_F1600_SUBROUTINE_CORRECT and _SAFE_FRAMED.                    *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK_F1600_SUBROUTINE_FULL = time prove
 (`exists f_events.
     forall e a rc A pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (a,200) (word_sub stackpointer (word 128),128) /\
      ALLPAIRS nonoverlapping
               [(a,200); (word_sub stackpointer (word 128),128)]
               [(word pc,0x480); (rc,192)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) sha3_keccak_f1600_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a; rc] s /\
                wordlist_from_memory(a,25) s = A /\
                wordlist_from_memory(rc,24) s = round_constants /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                wordlist_from_memory(a,25) s = keccak 24 A /\
                (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events rc a pc
                           (word_sub stackpointer (word 128))
                           returnaddress /\
                    memaccess_inbounds e2
                    [a,200; rc,192; word_sub stackpointer (word 128),128]
                    [a,200; word_sub stackpointer (word 128),128]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(a,200);
              memory :> bytes(word_sub stackpointer (word 128),128)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(7,7) SHA3_KECCAK_F1600_EXEC
    (CONV_RULE TWEAK_CONV SHA3_KECCAK_F1600_FULL)
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30]` 128 THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The form callers use, the state as a 1600-bit word as for                 *)
(* SHA3_KECCAK_F1600_SUBROUTINE_CORRECT_F1600, with the events of            *)
(* SHA3_KECCAK_F1600_SUBROUTINE_SAFE_FRAMED.                                 *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK_F1600_SUBROUTINE_FULL_F1600 = prove
 (`exists f_events.
     forall e a rc (S:1600 word) pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (a,200) (word_sub stackpointer (word 128),128) /\
      ALLPAIRS nonoverlapping
               [(a,200); (word_sub stackpointer (word 128),128)]
               [(word pc,0x480); (rc,192)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) sha3_keccak_f1600_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a; rc] s /\
                read (memory :> wbytes a) s = S /\
                wordlist_from_memory(rc,24) s = round_constants /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                read (memory :> wbytes a) s = keccak_f1600 S /\
                (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events rc a pc
                           (word_sub stackpointer (word 128))
                           returnaddress /\
                    memaccess_inbounds e2
                    [a,200; rc,192; word_sub stackpointer (word 128),128]
                    [a,200; word_sub stackpointer (word 128),128]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(a,200);
              memory :> bytes(word_sub stackpointer (word 128),128)])`,
  MP_TAC SHA3_KECCAK_F1600_SUBROUTINE_FULL THEN
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
(* The subroutine, with the saving of registers and the return, as for       *)
(* SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_CORRECT and _SUBROUTINE_SAFE_FRAMED.   *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_FULL = time prove
 (`exists f_events.
     forall e a rc A1 A2 A3 A4 pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (a,800) (word_sub stackpointer (word 224),224) /\
      ALLPAIRS nonoverlapping
               [(a,800); (word_sub stackpointer (word 224),224)]
               [(word pc,0xda0); (rc,192)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) sha3_keccak4_f1600_alt2_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a; rc] s /\
                wordlist_from_memory(a,25) s = A1 /\
                wordlist_from_memory(word_add a (word 200),25) s = A2 /\
                wordlist_from_memory(word_add a (word 400),25) s = A3 /\
                wordlist_from_memory(word_add a (word 600),25) s = A4 /\
                wordlist_from_memory(rc,24) s = round_constants /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                wordlist_from_memory(a,25) s = keccak 24 A1 /\
                wordlist_from_memory(word_add a (word 200),25) s =
                keccak 24 A2 /\
                wordlist_from_memory(word_add a (word 400),25) s =
                keccak 24 A3 /\
                wordlist_from_memory(word_add a (word 600),25) s =
                keccak 24 A4 /\
                (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events rc a pc
                           (word_sub stackpointer (word 224))
                           returnaddress /\
                    memaccess_inbounds e2
                    [a,800; rc,192; word_sub stackpointer (word 224),224]
                    [a,800; word_sub stackpointer (word 224),224]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(a,800);
              memory :> bytes(word_sub stackpointer (word 224),224)])`,
  let TWEAK_CONV =
   ONCE_DEPTH_CONV
    (WORDLIST_FROM_MEMORY_CONV THENC
     ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) in
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(11,11)
    SHA3_KECCAK4_F1600_ALT2_EXEC
    (CONV_RULE TWEAK_CONV SHA3_KECCAK4_F1600_ALT2_FULL)
    `[D8; D9; D10; D11; D12; D13; D14; D15;
      X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30]` 224 THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The form callers use, the states as 1600-bit words as for                 *)
(* SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_CORRECT_F1600, with the events of      *)
(* SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_SAFE_FRAMED.                           *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_FULL_F1600 = prove
 (`exists f_events.
     forall e a rc (S1:1600 word) (S2:1600 word) (S3:1600 word)
            (S4:1600 word) pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (a,800) (word_sub stackpointer (word 224),224) /\
      ALLPAIRS nonoverlapping
               [(a,800); (word_sub stackpointer (word 224),224)]
               [(word pc,0xda0); (rc,192)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) sha3_keccak4_f1600_alt2_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a; rc] s /\
                read (memory :> wbytes a) s = S1 /\
                read (memory :> wbytes(word_add a (word 200))) s = S2 /\
                read (memory :> wbytes(word_add a (word 400))) s = S3 /\
                read (memory :> wbytes(word_add a (word 600))) s = S4 /\
                wordlist_from_memory(rc,24) s = round_constants /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                read (memory :> wbytes a) s = keccak_f1600 S1 /\
                read (memory :> wbytes(word_add a (word 200))) s =
                keccak_f1600 S2 /\
                read (memory :> wbytes(word_add a (word 400))) s =
                keccak_f1600 S3 /\
                read (memory :> wbytes(word_add a (word 600))) s =
                keccak_f1600 S4 /\
                (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events rc a pc
                           (word_sub stackpointer (word 224))
                           returnaddress /\
                    memaccess_inbounds e2
                    [a,800; rc,192; word_sub stackpointer (word 224),224]
                    [a,800; word_sub stackpointer (word 224),224]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE
             [memory :> bytes(a,800);
              memory :> bytes(word_sub stackpointer (word 224),224)])`,
  MP_TAC SHA3_KECCAK4_F1600_ALT2_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `f:int64->int64->num->int64->int64->(uarch_event)list` THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `rc:int64`; `S1:1600 word`;
    `S2:1600 word`; `S3:1600 word`; `S4:1600 word`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `rc:int64`;
    `wordlist_of_num 25 (val(S1:1600 word)):int64 list`;
    `wordlist_of_num 25 (val(S2:1600 word)):int64 list`;
    `wordlist_of_num 25 (val(S3:1600 word)):int64 list`;
    `wordlist_of_num 25 (val(S4:1600 word)):int64 list`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[GSYM READ_MEMORY_WBYTES_KECCAK] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (ONCE_REWRITE_RULE[CONJ_SYM] ENSURES_POSTCONDITION_THM))) THEN
  MESON_TAC[KECCAK_F1600_MEMORY]);;
