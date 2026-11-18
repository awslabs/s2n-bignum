(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 of up to three inputs: the proof (see H_44_spec.ml).             *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/H_44_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_hash.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls, with the FULL theorems of the callees assumed as "H_INIT",     *)
(* "H_ABSORB", "H_FINALIZE", "H_SQUEEZE" and "H_RELEASE". The events before  *)
(* a call are functions of the public arguments, of the events of the        *)
(* callees and of the functions f_ev_... of the template. MLD_H44_ABSORB_TAC *)
(* absorbs the len bytes m into the context at stackpointer + 344, in state  *)
(* st at position pos.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLD_H44_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
    MLDSA_NATIVE_H_44_GCC12_O2_EXEC name
    (ilist @ [`pc:num`; `read RSP s`;
              `read (memory :> bytes64 (read RSP s)) s`])
   [`out:int64`; `outlen:num`; `in1:int64`; `in1len:num`; `in2:int64`;
    `in2len:num`; `in3:int64`; `in3len:num`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`] n;;

let MLD_H44_ABSORB_TAC len st pos m n =
  KECCAK_STATE_AT_TAC `word_add stackpointer (word 344):int64` THEN
  MLD_H44_CALL_TAC "H_ABSORB" [`read RDI s`; `read RSI s`; len; st; pos; m] n;;

(* ------------------------------------------------------------------------- *)
(* The state at join1, after the absorbs: the frame of 280 bytes is at       *)
(* stackpointer + 328, with the saved registers above it and the context at  *)
(* stackpointer + 344 (the state, and the position at + 544).                *)
(* ------------------------------------------------------------------------- *)

let MLD_H44_MID =
 `\s. read RBX s = word_add stackpointer (word 344) /\
      read RBP s = out /\ read R12 s = word outlen /\
      read RSP s = word_add stackpointer (word 328) /\
      read (memory :> bytes64 (word_add stackpointer (word 560))) s =
      rbx_init /\
      read (memory :> bytes64 (word_add stackpointer (word 568))) s =
      rbp_init /\
      read (memory :> bytes64 (word_add stackpointer (word 576))) s =
      r12_init /\
      read (memory :> bytes64 (word_add stackpointer (word 584))) s =
      r13_init /\
      read (memory :> bytes64 (word_add stackpointer (word 592))) s =
      r14_init /\
      read (memory :> bytes64 (word_add stackpointer (word 600))) s =
      r15_init /\
      read (memory :> bytes64 (word_add stackpointer (word 608))) s =
      returnaddress /\
      (read DF s <=> false) /\
      read (memory :> bytes (word_add stackpointer (word 344),200)) s =
      val(FST(mld_keccak_absorb 136 (word 0) 0 (in1len + in2len + in3len)
               (M1 + 2 EXP (8 * in1len) * (M2 + 2 EXP (8 * in2len) * M3)))) /\
      read (memory :> bytes32 (word_add stackpointer (word 544))) s =
      word((in1len + in2len + in3len) MOD 136)`;;

(* ------------------------------------------------------------------------- *)
(* To join1: the prologue, init and the absorb of in1, common to the four    *)
(* cases of MLD_H_CASES_TAC (where M2 = 0 if in2len = 0, M3 = 0 if           *)
(* in3len = 0), then the absorbs of in2 and in3 if their lengths are not 0.  *)
(* Each absorb after the first appends its input to the message.             *)
(* ------------------------------------------------------------------------- *)

let MLD_H44_HEAD_TAC =
  FULL_INIT_TAC THEN
  MLD_H_BOUND_TAC `in1:int64` THEN MLD_H_BOUND_TAC `in2:int64` THEN
  MLD_H_BOUND_TAC `in3:int64` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; EXP;
                              ARITH_RULE `x < 1 <=> x = 0`]) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `M2 = 0` || concl th = `M3 = 0`))) THEN
  (SUBGOAL_THEN `in1len MOD 136 <= 136` ASSUME_TAC THENL
    [MP_TAC(SPECL [`in1len:num`; `136`] MOD_LT_EQ) THEN ARITH_TAC;
     ALL_TAC]) THEN
  X86_STEPS_TAC MLDSA_NATIVE_H_44_GCC12_O2_EXEC (1--16) THEN
  MLD_H44_CALL_TAC "H_INIT" [`read RDI s`] 17 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC MLDSA_NATIVE_H_44_GCC12_O2_EXEC (18--21) THEN
  MLD_H44_ABSORB_TAC `in1len:num` `word 0:1600 word` `0` `M1:num` 22 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES;
                              READ_MEMORY_WBYTES_1600]);;

let MLD_H44_APPEND_TAC l2 m2 =
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPECL [`in1len:num`; l2; `M1:num`; m2] MLD_SHAKE256_ABSORB_APPEND)
       (ASSUME `M1 < 2 EXP (8 * in1len)`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; MLD_KECCAK_POS_ADD;
                              ADD_CLAUSES; READ_MEMORY_WBYTES_1600]);;

let MLD_H44_JOIN_TAC =
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; EXP] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* From join1: finalize, squeeze, release, the zeroing of the context with   *)
(* REP STOSQ and the return. S1 is the state after absorbing.                *)
(* ------------------------------------------------------------------------- *)

let MLD_H44_TAIL_TAC =
  REWRITE_TAC[mld_shake256_byte; mld_shake256_state; MLD_KECCAK_ABSORB_SND;
              ADD_CLAUSES] THEN
  ABBREV_TAC `S1 = FST(mld_keccak_absorb 136 (word 0) 0
                        (in1len + in2len + in3len)
                        (M1 + 2 EXP (8 * in1len) *
                              (M2 + 2 EXP (8 * in2len) * M3)))` THEN
  SUBGOAL_THEN `(in1len + in2len + in3len) MOD 136 <= 136` ASSUME_TAC THENL
   [MP_TAC(SPECL [`in1len + in2len + in3len`; `136`] MOD_LT_EQ) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC MLDSA_NATIVE_H_44_GCC12_O2_EXEC (1--2) THEN
  KECCAK_STATE_AT_TAC `word_add stackpointer (word 344):int64` THEN
  MLD_H44_CALL_TAC "H_FINALIZE"
   [`read RDI s`; `S1:1600 word`; `(in1len + in2len + in3len) MOD 136`] 3 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC MLDSA_NATIVE_H_44_GCC12_O2_EXEC (4--7) THEN
  KECCAK_STATE_AT_TAC `word_add stackpointer (word 344):int64` THEN
  MLD_H44_CALL_TAC "H_SQUEEZE"
   [`read RDI s`; `outlen:num`; `read RDX s`;
    `mld_keccak_finalize 136 31 S1 ((in1len + in2len + in3len) MOD 136)`;
    `136`] 8 THEN
  X86_STEPS_TAC MLDSA_NATIVE_H_44_GCC12_O2_EXEC (9--10) THEN
  MLD_H44_CALL_TAC "H_RELEASE" [`read RDI s`] 11 THEN
  X86_STEPS_TAC MLDSA_NATIVE_H_44_GCC12_O2_EXEC (12--23) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MLD_H_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The template of the events  *)
(* has one function for the part from join1 and one for each case of the     *)
(* lengths before it, whose arguments do not include the zero lengths.       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_INIT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_FINALIZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_SQUEEZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_RELEASE" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(out:int64) (outlen:num) (in1:int64) (in1len:num) (in2:int64)
     (in2len:num) (in3:int64) (in3len:num) (pc:num)
     (stackpointer:int64) (returnaddress:int64).
      APPEND
       (f_ev_tail out outlen in1 in1len in2 in2len in3 in3len pc
                  stackpointer returnaddress)
       (if in2len = 0 then
          if in3len = 0
          then f_ev_h00 out outlen in1 in1len pc stackpointer returnaddress
          else f_ev_h01 out outlen in1 in1len in3 in3len pc stackpointer
                        returnaddress
        else
          if in3len = 0
          then f_ev_h10 out outlen in1 in1len in2 in2len pc stackpointer
                        returnaddress
          else f_ev_h11 out outlen in1 in1len in2 in2len in3 in3len pc
                        stackpointer returnaddress)
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLDSA_NATIVE_H_44_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mld_H44_join1` MLD_H44_MID THEN
  CONJ_TAC THENL
   [MLD_H_CASES_TAC THEN MLD_H44_HEAD_TAC THENL
     [(*** in2len = 0, in3len = 0 ***)

      X86_STEPS_TAC MLDSA_NATIVE_H_44_GCC12_O2_EXEC (23--26) THEN
      MLD_H44_JOIN_TAC;

      (*** in2len = 0, in3len <> 0 ***)

      MLD_H_VAL_LEN_TAC `608` `in3:int64` `in3len:num` THEN
      X86_STEPS_TAC MLDSA_NATIVE_H_44_GCC12_O2_EXEC (23--26) THEN
      MLD_H_BRANCH_TAC THEN
      X86_STEPS_TAC MLDSA_NATIVE_H_44_GCC12_O2_EXEC (27--30) THEN
      MLD_H44_ABSORB_TAC `in3len:num`
       `FST(mld_keccak_absorb 136 (word 0) 0 in1len M1)` `in1len MOD 136`
       `M3:num` 31 THEN
      MLD_H44_APPEND_TAC `in3len:num` `M3:num` THEN
      X86_STEPS_TAC MLDSA_NATIVE_H_44_GCC12_O2_EXEC (32--32) THEN
      MLD_H44_JOIN_TAC;

      (*** in2len <> 0, in3len = 0 ***)

      MLD_H_VAL_LEN_TAC `608` `in2:int64` `in2len:num` THEN
      X86_STEPS_TAC MLDSA_NATIVE_H_44_GCC12_O2_EXEC (23--24) THEN
      MLD_H_BRANCH_TAC THEN
      X86_STEPS_TAC MLDSA_NATIVE_H_44_GCC12_O2_EXEC (25--28) THEN
      MLD_H44_ABSORB_TAC `in2len:num`
       `FST(mld_keccak_absorb 136 (word 0) 0 in1len M1)` `in1len MOD 136`
       `M2:num` 29 THEN
      MLD_H44_APPEND_TAC `in2len:num` `M2:num` THEN
      X86_STEPS_TAC MLDSA_NATIVE_H_44_GCC12_O2_EXEC (30--31) THEN
      MLD_H_BRANCH_TAC THEN
      MLD_H44_JOIN_TAC;

      (*** in2len <> 0, in3len <> 0 ***)

      MLD_H_VAL_LEN_TAC `608` `in2:int64` `in2len:num` THEN
      MLD_H_VAL_LEN_TAC `608` `in3:int64` `in3len:num` THEN
      X86_STEPS_TAC MLDSA_NATIVE_H_44_GCC12_O2_EXEC (23--24) THEN
      MLD_H_BRANCH_TAC THEN
      X86_STEPS_TAC MLDSA_NATIVE_H_44_GCC12_O2_EXEC (25--28) THEN
      MLD_H44_ABSORB_TAC `in2len:num`
       `FST(mld_keccak_absorb 136 (word 0) 0 in1len M1)` `in1len MOD 136`
       `M2:num` 29 THEN
      MLD_H44_APPEND_TAC `in2len:num` `M2:num` THEN
      X86_STEPS_TAC MLDSA_NATIVE_H_44_GCC12_O2_EXEC (30--31) THEN
      MLD_H_BRANCH_TAC THEN
      X86_STEPS_TAC MLDSA_NATIVE_H_44_GCC12_O2_EXEC (32--35) THEN
      SUBGOAL_THEN `(in1len + in2len) MOD 136 <= 136` ASSUME_TAC THENL
       [MP_TAC(SPECL [`in1len + in2len:num`; `136`] MOD_LT_EQ) THEN
        ARITH_TAC;
        ALL_TAC] THEN
      MLD_H44_ABSORB_TAC `in3len:num`
       `FST(mld_keccak_absorb 136 (word 0) 0 (in1len + in2len)
              (M1 + 2 EXP (8 * in1len) * M2))`
       `(in1len + in2len) MOD 136` `M3:num` 36 THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [MP (SPECL [`in1len:num`; `in2len:num`; `in3len:num`;
                   `M1:num`; `M2:num`; `M3:num`]
                  MLD_SHAKE256_ABSORB_APPEND3)
           (CONJ (ASSUME `M1 < 2 EXP (8 * in1len)`)
                 (ASSUME `M2 < 2 EXP (8 * in2len)`))]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_POS_ADD; GSYM ADD_ASSOC;
                                  READ_MEMORY_WBYTES_1600]) THEN
      X86_STEPS_TAC MLDSA_NATIVE_H_44_GCC12_O2_EXEC (37--37) THEN
      MLD_H44_JOIN_TAC];

    MLD_H44_TAIL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
