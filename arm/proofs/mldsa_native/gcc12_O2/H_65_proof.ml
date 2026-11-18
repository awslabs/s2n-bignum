(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 of up to three inputs: the proof (see H_65_spec.ml).             *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/H_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_hash.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls, with the FULL theorems of the callees assumed as "H_INIT",     *)
(* "H_ABSORB", "H_FINALIZE", "H_SQUEEZE" and "H_RELEASE". The events before  *)
(* a call are functions of the public arguments, of the events of the        *)
(* callees and of the functions f_ev_... of the template. MLD_H65_ABSORB_TAC *)
(* absorbs the len bytes m into the context at stackpointer + 344, in state  *)
(* st at position pos.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLD_H65_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
    MLDSA_NATIVE_H_65_GCC12_O2_EXEC name ilist
   [`out:int64`; `outlen:num`; `in1:int64`; `in1len:num`; `in2:int64`;
    `in2len:num`; `in3:int64`; `in3len:num`; `guard:int64`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`] n;;

let MLD_H65_ABSORB_TAC len st pos m n =
  KECCAK_STATE_AT_TAC `word_add stackpointer (word 344):int64` THEN
  MLD_H65_CALL_TAC "H_ABSORB"
   [`read X0 s`; `read X1 s`; len; st; pos; m; `pc:num`; `read SP s`;
    `read X30 s`] n;;

(* ------------------------------------------------------------------------- *)
(* The state at join1, after the absorbs: the frame of 304 bytes is at       *)
(* stackpointer + 256, with the saved registers, the context at              *)
(* stackpointer + 344 (the state, and the position at + 544) and the canary  *)
(* at + 552.                                                                 *)
(* ------------------------------------------------------------------------- *)

let MLD_H65_MID =
 `\s. read X19 s = word_add stackpointer (word 344) /\
      read X22 s = out /\ read X23 s = word outlen /\
      read SP s = word_add stackpointer (word 256) /\
      read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard)))
           s = guard /\
      read (memory :> bytes64 guard) s = canary /\
      read (memory :> bytes64 (word_add stackpointer (word 256))) s =
      x19_init /\
      read (memory :> bytes64 (word_add stackpointer (word 264))) s =
      x20_init /\
      read (memory :> bytes64 (word_add stackpointer (word 272))) s =
      x21_init /\
      read (memory :> bytes64 (word_add stackpointer (word 280))) s =
      x22_init /\
      read (memory :> bytes64 (word_add stackpointer (word 288))) s =
      x23_init /\
      read (memory :> bytes64 (word_add stackpointer (word 296))) s =
      x24_init /\
      read (memory :> bytes64 (word_add stackpointer (word 304))) s =
      x25_init /\
      read (memory :> bytes64 (word_add stackpointer (word 312))) s =
      x26_init /\
      read (memory :> bytes64 (word_add stackpointer (word 320))) s =
      x27_init /\
      read (memory :> bytes64 (word_add stackpointer (word 328))) s =
      returnaddress /\
      read (memory :> bytes64 (word_add stackpointer (word 552))) s =
      canary /\
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

let MLD_H65_HEAD_TAC =
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
  ARM_STEPS_TAC MLDSA_NATIVE_H_65_GCC12_O2_EXEC (1--3) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_H_65_GCC12_O2_EXEC (4--21) THEN
  MLD_H65_CALL_TAC "H_INIT" [`read X0 s`; `pc:num`; `read X30 s`] 22 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC MLDSA_NATIVE_H_65_GCC12_O2_EXEC (23--26) THEN
  MLD_H65_ABSORB_TAC `in1len:num` `word 0:1600 word` `0` `M1:num` 27 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES;
                              READ_MEMORY_WBYTES_1600]);;

let MLD_H65_APPEND_TAC l2 m2 =
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPECL [`in1len:num`; l2; `M1:num`; m2] MLD_SHAKE256_ABSORB_APPEND)
       (ASSUME `M1 < 2 EXP (8 * in1len)`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; MLD_KECCAK_POS_ADD;
                              ADD_CLAUSES; READ_MEMORY_WBYTES_1600]);;

let MLD_H65_JOIN_TAC =
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; EXP] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* From join1: finalize, squeeze, release, the zeroing of the context and    *)
(* the check of the canary. S1 is the state after absorbing.                 *)
(* ------------------------------------------------------------------------- *)

let MLD_H65_TAIL_TAC =
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
  ARM_STEPS_TAC MLDSA_NATIVE_H_65_GCC12_O2_EXEC (1--2) THEN
  KECCAK_STATE_AT_TAC `word_add stackpointer (word 344):int64` THEN
  MLD_H_GUARD_ADDR_TAC THEN
  MLD_H65_CALL_TAC "H_FINALIZE"
   [`read X0 s`; `S1:1600 word`; `(in1len + in2len + in3len) MOD 136`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 3 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC MLDSA_NATIVE_H_65_GCC12_O2_EXEC (4--7) THEN
  KECCAK_STATE_AT_TAC `word_add stackpointer (word 344):int64` THEN
  MLD_H65_CALL_TAC "H_SQUEEZE"
   [`read X0 s`; `outlen:num`; `read X2 s`;
    `mld_keccak_finalize 136 31 S1 ((in1len + in2len + in3len) MOD 136)`;
    `136`; `pc:num`; `read SP s`; `read X30 s`] 8 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_H_65_GCC12_O2_EXEC (9--10) THEN
  MLD_H65_CALL_TAC "H_RELEASE" [`read X0 s`; `pc:num`; `read X30 s`] 11 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_H_65_GCC12_O2_EXEC (12--20) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_H_65_GCC12_O2_EXEC (21--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MLD_H_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The template of the events  *)
(* has one function for the part from join1 and one for each case of the     *)
(* lengths before it, whose arguments do not include the zero lengths.       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_65_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_H_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
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
     (in2len:num) (in3:int64) (in3len:num) (guard:int64) (pc:num)
     (stackpointer:int64) (returnaddress:int64).
      APPEND
       (f_ev_tail out outlen in1 in1len in2 in2len in3 in3len guard pc
                  stackpointer returnaddress)
       (if in2len = 0 then
          if in3len = 0
          then f_ev_h00 out outlen in1 in1len guard pc stackpointer
                        returnaddress
          else f_ev_h01 out outlen in1 in1len in3 in3len guard pc
                        stackpointer returnaddress
        else
          if in3len = 0
          then f_ev_h10 out outlen in1 in1len in2 in2len guard pc
                        stackpointer returnaddress
          else f_ev_h11 out outlen in1 in1len in2 in2len in3 in3len guard pc
                        stackpointer returnaddress)
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `out:int64`; `outlen:num`; `in1:int64`;
    `in1len:num`; `in2:int64`; `in2len:num`; `in3:int64`; `in3len:num`;
    `M1:num`; `M2:num`; `M3:num`; `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 560 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLDSA_NATIVE_H_65_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN
  ENSURES_PRESERVED_TAC "x26_init" `X26` THEN
  ENSURES_PRESERVED_TAC "x27_init" `X27` THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mld_H65_join1` MLD_H65_MID THEN
  CONJ_TAC THENL
   [MLD_H_CASES_TAC THEN MLD_H65_HEAD_TAC THENL
     [(*** in2len = 0, in3len = 0 ***)

      ARM_STEPS_TAC MLDSA_NATIVE_H_65_GCC12_O2_EXEC (28--29) THEN
      MLD_H65_JOIN_TAC;

      (*** in2len = 0, in3len <> 0 ***)

      MLD_H_VAL_LEN_TAC `560` `in3:int64` `in3len:num` THEN
      ARM_STEPS_TAC MLDSA_NATIVE_H_65_GCC12_O2_EXEC (28--33) THEN
      MLD_H65_ABSORB_TAC `in3len:num`
       `FST(mld_keccak_absorb 136 (word 0) 0 in1len M1)` `in1len MOD 136`
       `M3:num` 34 THEN
      MLD_H65_APPEND_TAC `in3len:num` `M3:num` THEN
      ARM_STEPS_TAC MLDSA_NATIVE_H_65_GCC12_O2_EXEC (35--35) THEN
      MLD_H65_JOIN_TAC;

      (*** in2len <> 0, in3len = 0 ***)

      MLD_H_VAL_LEN_TAC `560` `in2:int64` `in2len:num` THEN
      ARM_STEPS_TAC MLDSA_NATIVE_H_65_GCC12_O2_EXEC (28--32) THEN
      MLD_H65_ABSORB_TAC `in2len:num`
       `FST(mld_keccak_absorb 136 (word 0) 0 in1len M1)` `in1len MOD 136`
       `M2:num` 33 THEN
      MLD_H65_APPEND_TAC `in2len:num` `M2:num` THEN
      ARM_STEPS_TAC MLDSA_NATIVE_H_65_GCC12_O2_EXEC (34--34) THEN
      MLD_H65_JOIN_TAC;

      (*** in2len <> 0, in3len <> 0 ***)

      MLD_H_VAL_LEN_TAC `560` `in2:int64` `in2len:num` THEN
      MLD_H_VAL_LEN_TAC `560` `in3:int64` `in3len:num` THEN
      ARM_STEPS_TAC MLDSA_NATIVE_H_65_GCC12_O2_EXEC (28--32) THEN
      MLD_H65_ABSORB_TAC `in2len:num`
       `FST(mld_keccak_absorb 136 (word 0) 0 in1len M1)` `in1len MOD 136`
       `M2:num` 33 THEN
      MLD_H65_APPEND_TAC `in2len:num` `M2:num` THEN
      ARM_STEPS_TAC MLDSA_NATIVE_H_65_GCC12_O2_EXEC (34--38) THEN
      SUBGOAL_THEN `(in1len + in2len) MOD 136 <= 136` ASSUME_TAC THENL
       [MP_TAC(SPECL [`in1len + in2len:num`; `136`] MOD_LT_EQ) THEN
        ARITH_TAC;
        ALL_TAC] THEN
      MLD_H65_ABSORB_TAC `in3len:num`
       `FST(mld_keccak_absorb 136 (word 0) 0 (in1len + in2len)
              (M1 + 2 EXP (8 * in1len) * M2))`
       `(in1len + in2len) MOD 136` `M3:num` 39 THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [MP (SPECL [`in1len:num`; `in2len:num`; `in3len:num`;
                   `M1:num`; `M2:num`; `M3:num`]
                  MLD_SHAKE256_ABSORB_APPEND3)
           (CONJ (ASSUME `M1 < 2 EXP (8 * in1len)`)
                 (ASSUME `M2 < 2 EXP (8 * in2len)`))]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_POS_ADD; GSYM ADD_ASSOC;
                                  READ_MEMORY_WBYTES_1600]) THEN
      ARM_STEPS_TAC MLDSA_NATIVE_H_65_GCC12_O2_EXEC (40--40) THEN
      MLD_H65_JOIN_TAC];

    MLD_H65_TAIL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_H_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC MLDSA_NATIVE_H_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_H_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_H_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC MLDSA_NATIVE_H_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
