(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The challenge polynomial (SampleInBall): the proof (see                   *)
(* poly_challenge_65_spec.ml), with the tools of                             *)
(* utils/mldsa_native_challenge.ml, as for AArch64, with the x86 code and    *)
(* its stack frame aligned to 32 bytes (see utils/mldsa_native_realign.ml).  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/poly_challenge_65_spec.ml";;
needs "x86/proofs/utils/mldsa_native_challenge.ml";;
needs "x86/proofs/utils/mldsa_native_memset.ml";;

let POLY_CHALLENGE_65_EXEC = MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The events: those to the head of the loop over the bytes from position 8  *)
(* on (pro), those of byte n for each of the mld_poly_challenge_bytes bytes  *)
(* read, and those from the end of the loop to the return (epi). Byte n      *)
(* starts a block when (8 + n) MOD 136 = 0 and is then read after squeezing  *)
(* the block (sa, sx, sr); otherwise it is read from the buffer (ab, ac, ax, *)
(* rb, rc). It is accepted (sa, sx, ab, ac, ax) or rejected (sr, rb, rc); an *)
(* accepted byte ends the loop if it sets the last coefficient (sx, ax), and *)
(* otherwise the iteration ends at the head for the next byte: the squeeze   *)
(* if that byte starts a block (ab, rb), the read from the buffer if not     *)
(* (sa, ac, sr, rc). The events before a call may also mention bot, the      *)
(* bottom of the aligned frame (see POLY_CHALLENGE_65_INTRO_TAC), which      *)
(* REALIGN_UNBOT_TAC expands before the events are matched with the          *)
(* template.                                                                 *)
(* ------------------------------------------------------------------------- *)

let POLY_CHALLENGE_65_TEMPLATE =
 `\(c:int64) (seed:int64) (C:num) (pc:num) (stackpointer:int64)
   (returnaddress:int64).
   APPEND (f_ev_epi c seed C pc stackpointer returnaddress)
    (APPEND
      (ENUMERATEL (mld_poly_challenge_bytes 49 (mld_shake256_byte 48 C))
        (\n. if (8 + n) MOD 136 = 0
             then if mld_poly_challenge_accept 49 (mld_shake256_byte 48 C) n
                  then if n + 1 <
                          mld_poly_challenge_bytes 49 (mld_shake256_byte 48 C)
                       then f_ev_sa c C pc stackpointer n
                       else f_ev_sx c C pc stackpointer n
                  else f_ev_sr c C pc stackpointer n
             else if mld_poly_challenge_accept 49 (mld_shake256_byte 48 C) n
                  then if n + 1 <
                          mld_poly_challenge_bytes 49 (mld_shake256_byte 48 C)
                       then if (8 + (n + 1)) MOD 136 = 0
                            then f_ev_ab c C pc stackpointer n
                            else f_ev_ac c C pc stackpointer n
                       else f_ev_ax c C pc stackpointer n
                  else if (8 + (n + 1)) MOD 136 = 0
                       then f_ev_rb c C pc stackpointer n
                       else f_ev_rc c C pc stackpointer n))
      (f_ev_pro c seed C pc stackpointer returnaddress))
   :(uarch_event)list`;;

let POLY_CHALLENGE_65_ALLOWED =
  [`c:int64`; `seed:int64`; `C:num`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`; `n:num`; `bot:int64`];;

let POLY_CHALLENGE_65_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc POLY_CHALLENGE_65_EXEC name
    (ilist @ [`pc:num`; `read RSP s`;
              `read (memory :> bytes64 (read RSP s)) s`])
    POLY_CHALLENGE_65_ALLOWED n;;

(* ------------------------------------------------------------------------- *)
(* The setup: the callee theorems, the template, the stack frame, which the  *)
(* code aligns to 32 bytes after pushing six registers (48 bytes, so that    *)
(* the AND is of stackpointer + 743, and the aligned frame and the stacks of *)
(* the callees are the 712 bytes at bot = stackpointer + delta, delta <= 31, *)
(* with the registers at stackpointer + 743 to 783), the saved registers,    *)
(* and the termination hypothesis as an existence.                           *)
(* ------------------------------------------------------------------------- *)

let POLY_CHALLENGE_65_INTRO_TAC =
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
  CONCRETIZE_F_EVENTS_TAC POLY_CHALLENGE_65_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst POLY_CHALLENGE_65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 743 THEN REALIGN_FRAME_TAC 791 743 THEN
  REALIGN_NONOV_TAC 712
   [`c:int64,1024`; `seed:int64,48`; `word pc:int64,51232`;
    `word_add stackpointer (word 743):int64,48`;
    `word_add stackpointer (word 791):int64,8`] THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   [("rbx_init",`RBX`); ("rbp_init",`RBP`); ("r12_init",`R12`);
    ("r13_init",`R13`); ("r14_init",`R14`); ("r15_init",`R15`)] THEN
  FIRST_ASSUM(fun th ->
    if concl th = `mld_poly_challenge_terminates 49 48 C`
    then ASSUME_TAC(REWRITE_RULE[mld_poly_challenge_terminates] th)
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The state at the head of the loop for byte n, in the aligned frame (RSP = *)
(* bot + 328 after the AND and SUB): the index i = 207 + k in R15, with k    *)
(* the number of coefficients set so far, the position p = (7 + n) MOD 136 + *)
(* 1, in RAX at the read from the buffer at join2 and in RCX at the test of  *)
(* the position at join3 before the squeeze when byte n starts a block (and  *)
(* in RCX at the end of the loop, after the last byte), block (7 + n) DIV    *)
(* 136 of the output in the buffer at bot + 360, the context at bot + 504    *)
(* permuted once more, its position 136 at bot + 704, the polynomial so far  *)
(* at c, the sign bits not used yet at bot + 352, and the saved registers.   *)
(* The loop ends at +0x13f, which has no label.                              *)
(* ------------------------------------------------------------------------- *)

let POLY_CHALLENGE_65_BUF = `word_add bot (word 360):int64`;;

let POLY_CHALLENGE_65_FRAME =
 `read RBX s = word_add bot (word 360) /\
  read R12 s = word_add bot (word 504) /\
  read R13 s = word 1 /\
  read R14 s = c /\
  read RSP s = word_add bot (word 328) /\
  read RBP s = word_add stackpointer (word 783) /\
  read (memory :> bytes32(word_add bot (word 704))) s = word 136 /\
  read (memory :> bytes64(word_add stackpointer (word 743))) s = rbx_init /\
  read (memory :> bytes64(word_add stackpointer (word 751))) s = r12_init /\
  read (memory :> bytes64(word_add stackpointer (word 759))) s = r13_init /\
  read (memory :> bytes64(word_add stackpointer (word 767))) s = r14_init /\
  read (memory :> bytes64(word_add stackpointer (word 775))) s = r15_init /\
  read (memory :> bytes64(word_add stackpointer (word 783))) s = rbp_init /\
  read (memory :> bytes64(word_add stackpointer (word 791))) s =
  returnaddress /\
  (read DF s <=> false)`;;

let POLY_CHALLENGE_65_INV =
  let body =
   `read R15 s =
    word(207 + FST(mld_poly_challenge_step 49 (mld_shake256_byte 48 C) n)) /\
    (if (8 + n) MOD 136 = 0 \/
        n = mld_poly_challenge_bytes 49 (mld_shake256_byte 48 C)
     then read RCX s else read RAX s) =
    word((7 + n) MOD 136 + 1) /\
    read (memory :> bytes(word_add bot (word 360),136)) s =
    num_of_bytelist(list_of_seq
     (\t. mld_shake256_byte 48 C (136 * ((7 + n) DIV 136) + t)) 136) /\
    read (memory :> bytes(word_add bot (word 504),200)) s =
    val(keccak_squeeze ((7 + n) DIV 136 + 1) (mld_shake256_state 48 C)) /\
    (!t. t < 256
         ==> read (memory :> bytes32(word_add c (word(4 * t)))) s =
             SND(mld_poly_challenge_step 49 (mld_shake256_byte 48 C) n) t) /\
    read (memory :> bytes64(word_add bot (word 352))) s =
    word_ushr (mld_poly_challenge_signs (mld_shake256_byte 48 C))
              (FST(mld_poly_challenge_step 49 (mld_shake256_byte 48 C) n))` in
  list_mk_abs([`n:num`; `s:x86state`],
              list_mk_conj(conjuncts body @
                           conjuncts POLY_CHALLENGE_65_FRAME));;

let POLY_CHALLENGE_65_A2 =
  let t = subst [`mld_poly_challenge_bytes 49 (mld_shake256_byte 48 C)`,
                 `n:num`]
                (snd(dest_abs(snd(dest_abs POLY_CHALLENGE_65_INV)))) in
  mk_abs(`s:x86state`,t);;

let POLY_CHALLENGE_65_PCF =
  `\n. if (8 + n) MOD 136 = 0 then pc + mldsa65_poly_challenge_join3
       else pc + mldsa65_poly_challenge_join2`;;

let POLY_CHALLENGE_65_PC2 =
  mk_binop `(+):num->num->num` `pc:num`
   (mk_small_numeral(layout "mldsa65_poly_challenge" + 0x13f));;

(* ------------------------------------------------------------------------- *)
(* To the head of the loop for byte 0: the prologue, init, absorbing the     *)
(* seed, finalizing, squeezing the first block (block 0 of the output), the  *)
(* sign bits from its first 8 bytes by the loop, simulated through with the  *)
(* decisions of its tests, the zeroing of the polynomial by the inlined      *)
(* memset (see MEMSET_PREP_TAC in utils/mldsa_native_keccak.ml), and the     *)
(* jump to join1 and join2 with RAX = 8.                                     *)
(* ------------------------------------------------------------------------- *)

let POLY_CHALLENGE_65_PROLOGUE_TAC =
  SUBGOAL_THEN
   `~(mld_poly_challenge_bytes 49 (mld_shake256_byte 48 C) = 0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MLD_POLY_CHALLENGE_BYTES_POS THEN ASM_REWRITE_TAC[ARITH_EQ];
    ALL_TAC] THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC POLY_CHALLENGE_65_EXEC (1--10) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC POLY_CHALLENGE_65_EXEC (11--14) THEN
  POLY_CHALLENGE_65_CALL_TAC "H_INIT" [`read RDI s`] 15 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC POLY_CHALLENGE_65_EXEC (16--19) THEN
  KECCAK_STATE_AT_TAC `word_add bot (word 504):int64` THEN
  POLY_CHALLENGE_65_CALL_TAC "H_ABSORB"
   [`read RDI s`; `read RSI s`; `48`; `word 0:1600 word`; `0`; `C:num`] 20
  THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES;
                              READ_MEMORY_WBYTES_1600;
                              NUM_REDUCE_CONV `48 MOD 136`]) THEN
  X86_STEPS_TAC POLY_CHALLENGE_65_EXEC (21--23) THEN
  KECCAK_STATE_AT_TAC `word_add bot (word 504):int64` THEN
  POLY_CHALLENGE_65_CALL_TAC "H_FINALIZE"
   [`read RDI s`; `FST(mld_keccak_absorb 136 (word 0) 0 48 C)`; `48`] 24 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600;
    MATCH_MP MLD_CHALLENGE_STATE (ARITH_RULE `48 < 136`)]) THEN
  X86_STEPS_TAC POLY_CHALLENGE_65_EXEC (25--28) THEN
  KECCAK_STATE_AT_TAC `word_add bot (word 504):int64` THEN
  POLY_CHALLENGE_65_CALL_TAC "H_SQUEEZE"
   [`read RDI s`; `136`; `read RDX s`; `mld_shake256_state 48 C`; `136`] 29
  THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600;
    MLD_CHALLENGE_SQUEEZE_STATE; GSYM mld_shake256_byte]) THEN
  MLD_CHALLENGE_BYTES_TAC POLY_CHALLENGE_65_BUF (map mk_small_numeral (0--7))
  THEN
  X86_STEPS_TAC POLY_CHALLENGE_65_EXEC (30--34) THEN
  MAP_EVERY (fun i ->
    X86_STEPS_TAC POLY_CHALLENGE_65_EXEC ((35+7*i)--(41+7*i)) THEN
    MLD_CHALLENGE_BRANCH_TAC) (0--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_CHALLENGE_SIGNS_WORD; ETA_AX]) THEN
  X86_STEPS_TAC POLY_CHALLENGE_65_EXEC (91--102) THEN
  MEMSET_PREP_TAC THEN
  MEMSET_STEP_TAC POLY_CHALLENGE_65_EXEC 103 THEN
  MEMSET_DONE_TAC `c:int64` 1024 "s103" THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_CHALLENGE_ZERO_POLY o check (fun th ->
    can (term_match [] `read (memory :> bytes(c,1024)) s = 0`) (concl th))) THEN
  X86_STEPS_TAC POLY_CHALLENGE_65_EXEC (104--108) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[CONJUNCT1 ENUMERATEL; CONJUNCT1 APPEND;
              CONJUNCT1 mld_poly_challenge_step; WORD_USHR_ZERO] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; ETA_AX] THEN
  ASM_REWRITE_TAC[ETA_AX; GSYM(ONCE_REWRITE_RULE[EQ_SYM_EQ]
   (ASSUME `~(mld_poly_challenge_bytes 49 (mld_shake256_byte 48 C) = 0)`))]
  THEN
  REALIGN_UNBOT_TAC THEN MLD_PREFIX_DISCHARGE_TAC ALL_TAC;;

(* ------------------------------------------------------------------------- *)
(* The iteration for byte n. The proof abbreviates k (the number of          *)
(* coefficients set before) and j (the byte), and in the cases of the        *)
(* position p and the block b, and puts them back before matching the events *)
(* with the template (POLY_CHALLENGE_65_FINAL_TAC, which also proves the new *)
(* polynomial for an accepted byte). Whether the next byte is the last one   *)
(* is assumed as an equivalence with T or F, so that it does not rewrite n + *)
(* 1 in the events, and so is p = 135 (so that the events keep the position  *)
(* as a function of n, which the simulation of the later iterations does not *)
(* change).                                                                  *)
(* ------------------------------------------------------------------------- *)

let POLY_CHALLENGE_65_SETUP_TAC =
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    if is_exists(concl th) then
      let nth = ASSUME
        `n < mld_poly_challenge_bytes 49 (mld_shake256_byte 48 C)` in
      ASSUME_TAC(MP (SPEC `n:num` (CONJUNCT2
                   (MATCH_MP MLD_POLY_CHALLENGE_BYTES th))) nth) THEN
      ASSUME_TAC(MP (SPEC `n:num` (MATCH_MP (REWRITE_RULE[IMP_CONJ]
                   MLD_POLY_CHALLENGE_BYTES_NEXT) th)) nth)
    else NO_TAC) THEN
  SUBGOAL_THEN
   `mld_poly_challenge_accept 49 (mld_shake256_byte 48 C) n <=>
    val(mld_shake256_byte 48 C (8 + n)) <=
    207 + FST(mld_poly_challenge_step 49 (mld_shake256_byte 48 C) n)`
  ASSUME_TAC THENL
   [REWRITE_TAC[mld_poly_challenge_accept] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(n = mld_poly_challenge_bytes 49 (mld_shake256_byte 48 C))`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `n < mld_poly_challenge_bytes 49 (mld_shake256_byte 48 C)` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ASSUME
   `~(n = mld_poly_challenge_bytes 49 (mld_shake256_byte 48 C))`];;

let POLY_CHALLENGE_65_ABBREV_TAC =
  ABBREV_TAC
   `k = FST (mld_poly_challenge_step 49 (mld_shake256_byte 48 C) n)` THEN
  ABBREV_TAC `j = val(mld_shake256_byte 48 C (8 + n))` THEN
  SUBGOAL_THEN `j < 256` ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN
    MP_TAC(ISPEC `mld_shake256_byte 48 C (8 + n)` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_zx(word(207 + k):int64):int32) = 207 + k /\
                val(word(207 + k):int64) = 207 + k /\
                val(word j:int64) = j`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MLD_CHALLENGE_VAL_ZX_WORD;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64];
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64]] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC];;

let POLY_CHALLENGE_65_UNABBREV_TAC =
  MLD_CHALLENGE_UNABBREV_TAC
   [`val(mld_shake256_byte 48 C (8 + n))`,`j:num`;
    `FST (mld_poly_challenge_step 49 (mld_shake256_byte 48 C) n)`,`k:num`;
    `(7 + n) DIV 136`,`b:num`;
    `(7 + n) MOD 136 + 1`,`p:num`];;

let POLY_CHALLENGE_65_LAST_TAC =
  let tm = `n + 1 = mld_poly_challenge_bytes 49 (mld_shake256_byte 48 C)` in
  (SUBGOAL_THEN tm (ASSUME_TAC o EQT_INTRO) THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]) ORELSE
  (SUBGOAL_THEN (mk_neg tm) ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC]);;

let POLY_CHALLENGE_65_FINAL_TAC =
  POLY_CHALLENGE_65_LAST_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MLD_POLY_CHALLENGE_STEP_ADD1] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  TRY(CONJ_TAC THENL [MLD_CHALLENGE_POLY_TAC `207 + k`; ALL_TAC]) THEN
  POLY_CHALLENGE_65_UNABBREV_TAC THEN
  REALIGN_UNBOT_TAC THEN
  MLD_CHALLENGE_DISCHARGE_TAC
   (TRY(ABBREV_TAC `jj = val(mld_shake256_byte 48 C (8 + n))`));;

(*** The code for an accepted byte, from join4 at step m to the jump to  ***)
(*** join3 or the end of the loop at step m + 13                         ***)

let POLY_CHALLENGE_65_ACCEPT_TAC m pnext =
  let rest =
    X86_STEPS_TAC POLY_CHALLENGE_65_EXEC ((m+2)--(m+13)) THEN
    MLD_CHALLENGE_EXIT_TEST_TAC THEN
    MLD_CHALLENGE_FIX_TAC mld_challenge_is_bytes32
     [MLD_CHALLENGE_SIGN_WORD; BIT_WORD_USHR; ADD_CLAUSES;
      GSYM mld_poly_challenge_sign] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_USHR_COMPOSE]) THEN
    MLD_CHALLENGE_FIX_TAC (mld_challenge_is_read_reg `R15`)
     [GSYM WORD_ADD; GSYM ADD_ASSOC] THEN
    (SUBGOAL_THEN
      `mld_poly_challenge_accept 49 (mld_shake256_byte 48 C) n`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    (ASM_CASES_TAC `k + 1 = 49` THENL
      [(SUBGOAL_THEN
         `~(n + 1 < mld_poly_challenge_bytes 49 (mld_shake256_byte 48 C))`
        ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
       MLD_CHALLENGE_BRANCH_TAC THEN POLY_CHALLENGE_65_FINAL_TAC;
       (SUBGOAL_THEN
         `n + 1 < mld_poly_challenge_bytes 49 (mld_shake256_byte 48 C)`
        ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
       MLD_CHALLENGE_BRANCH_TAC THEN pnext (m + 14)]) in
  MLD_CHALLENGE_FIX_TAC (mld_challenge_is_read_reg `RDX`)
   [MLD_CHALLENGE_ZX_BYTE;
    ASSUME `val(mld_shake256_byte 48 C (8 + n)) = j`] THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `bytes32` (concl th)
    then ASSUME_TAC(MP (SPEC `j:num` th) (ASSUME `j < 256`)) else NO_TAC) THEN
  X86_STEPS_TAC POLY_CHALLENGE_65_EXEC (m--(m+1)) THEN
  MLD_CHALLENGE_EXCLUDE_TAC `207 + k` `j:num` THEN
  ASM_CASES_TAC `j < 207 + k` THEN rest;;

(*** A byte read from the buffer at p < 136: at join3 after it, with  ***)
(*** RCX = p + 1, the head of the next byte if that starts a block    ***)
(*** (p = 135), and otherwise on to join2 with RAX = p + 1            ***)

let POLY_CHALLENGE_65_NORMAL_PREP_TAC =
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
  SUBGOAL_THEN `val(word p:int64) = p` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  POLY_CHALLENGE_65_ABBREV_TAC THEN
  FULL_INIT_TAC THEN
  MLD_CHALLENGE_LOAD_TAC POLY_CHALLENGE_65_BUF `p:num`
   [ASSUME `136 * b + p = 8 + n`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_CHALLENGE_BUF_ADDR]);;

let POLY_CHALLENGE_65_NORMAL_NEXT_TAC m =
  ASM_CASES_TAC `p = 135` THENL
   [(SUBGOAL_THEN `(8 + (n + 1)) MOD 136 = 0` ASSUME_TAC THENL
      [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    FIRST_X_ASSUM(fun th ->
      if concl th = `p = 135` then ASSUME_TAC(EQT_INTRO th) else NO_TAC) THEN
    POLY_CHALLENGE_65_FINAL_TAC;
    (SUBGOAL_THEN `~((8 + (n + 1)) MOD 136 = 0)` ASSUME_TAC THENL
      [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    X86_STEPS_TAC POLY_CHALLENGE_65_EXEC (m--(m+1)) THEN
    MLD_CHALLENGE_BRANCH_TAC THEN
    X86_STEPS_TAC POLY_CHALLENGE_65_EXEC ((m+2)--(m+2)) THEN
    MLD_CHALLENGE_ZX_ZX_TAC `p + 1` THEN
    POLY_CHALLENGE_65_FINAL_TAC];;

let POLY_CHALLENGE_65_NORMAL_TAC =
  POLY_CHALLENGE_65_NORMAL_PREP_TAC THEN
  X86_STEPS_TAC POLY_CHALLENGE_65_EXEC (1--4) THEN
  MP_TAC(SPEC `p:num` MLD_CHALLENGE_LEA_ADD1) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  MLD_CHALLENGE_FIX_TAC (mld_challenge_is_read_reg `RCX`)
   [ASSUME `word_zx(word_sx(word_add (word p) (word 1):int64):int32):int64 =
            word(p + 1)`] THEN
  SUBGOAL_THEN `val(word_zx(word(p + 1):int64):int32) = p + 1` ASSUME_TAC
  THENL [MATCH_MP_TAC MLD_CHALLENGE_VAL_ZX_WORD THEN SIMPLE_ARITH_TAC;
         ALL_TAC] THEN
  ASM_CASES_TAC `j <= 207 + k` THEN MLD_CHALLENGE_BRANCH_TAC THENL
   [POLY_CHALLENGE_65_ACCEPT_TAC 5 POLY_CHALLENGE_65_NORMAL_NEXT_TAC;
    (SUBGOAL_THEN
      `~mld_poly_challenge_accept 49 (mld_shake256_byte 48 C) n`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    (SUBGOAL_THEN
      `n + 1 < mld_poly_challenge_bytes 49 (mld_shake256_byte 48 C)`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    POLY_CHALLENGE_65_NORMAL_NEXT_TAC 5];;

(*** A byte that starts a block, read after squeezing the block, with ***)
(*** the next byte read from the buffer at position 1                 ***)

let POLY_CHALLENGE_65_SQUEEZE_NEXT_TAC m =
  X86_STEPS_TAC POLY_CHALLENGE_65_EXEC (m--(m+2)) THEN
  MLD_CHALLENGE_BRANCH_TAC THEN POLY_CHALLENGE_65_FINAL_TAC;;

let POLY_CHALLENGE_65_SQUEEZE_TAC =
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
  POLY_CHALLENGE_65_ABBREV_TAC THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC POLY_CHALLENGE_65_EXEC (1--6) THEN
  KECCAK_STATE_AT_TAC `word_add bot (word 504):int64` THEN
  POLY_CHALLENGE_65_CALL_TAC "H_SQUEEZE"
   [`read RDI s`; `136`; `read RDX s`;
    `keccak_squeeze (b + 1) (mld_shake256_state 48 C)`; `136`] 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600;
    MLD_CHALLENGE_SQUEEZE_STATE; MLD_CHALLENGE_SQUEEZE_ADD;
    MLD_CHALLENGE_SQUEEZE_BYTE_FUN; ARITH_RULE `1 + b + 1 = (b + 1) + 1`])
  THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_shake256_byte]) THEN
  (SUBGOAL_THEN `136 * (b + 1) + 0 = 8 + n` ASSUME_TAC THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]) THEN
  MLD_CHALLENGE_LOAD_TAC POLY_CHALLENGE_65_BUF `0`
   [ASSUME `136 * (b + 1) + 0 = 8 + n`] THEN
  X86_STEPS_TAC POLY_CHALLENGE_65_EXEC (8--11) THEN
  ASM_CASES_TAC `j <= 207 + k` THEN MLD_CHALLENGE_BRANCH_TAC THENL
   [X86_STEPS_TAC POLY_CHALLENGE_65_EXEC (12--12) THEN
    POLY_CHALLENGE_65_ACCEPT_TAC 13 POLY_CHALLENGE_65_SQUEEZE_NEXT_TAC;
    (SUBGOAL_THEN
      `~mld_poly_challenge_accept 49 (mld_shake256_byte 48 C) n`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    (SUBGOAL_THEN
      `n + 1 < mld_poly_challenge_bytes 49 (mld_shake256_byte 48 C)`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    POLY_CHALLENGE_65_FINAL_TAC];;

let POLY_CHALLENGE_65_BODY_TAC =
  POLY_CHALLENGE_65_SETUP_TAC THEN
  ASM_CASES_TAC `(8 + n) MOD 136 = 0` THENL
   [POLY_CHALLENGE_65_SQUEEZE_TAC; POLY_CHALLENGE_65_NORMAL_TAC];;

(* ------------------------------------------------------------------------- *)
(* After the last byte: releasing the context, zeroing the buffer (with REP  *)
(* STOSQ) and the sign bits, and the return, with the polynomial after the   *)
(* mld_poly_challenge_bytes bytes, which is mld_poly_challenge.              *)
(* ------------------------------------------------------------------------- *)

let POLY_CHALLENGE_65_EPILOGUE_TAC =
  FULL_INIT_TAC THEN
  X86_STEPS_TAC POLY_CHALLENGE_65_EXEC (1--2) THEN
  POLY_CHALLENGE_65_CALL_TAC "H_RELEASE" [`read RDI s`] 3 THEN
  X86_STEPS_TAC POLY_CHALLENGE_65_EXEC (4--17) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[mld_poly_challenge] THEN
  REALIGN_UNBOT_TAC THEN MLD_PREFIX_DISCHARGE_TAC ALL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  POLY_CHALLENGE_65_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC POLY_CHALLENGE_65_PC2
    POLY_CHALLENGE_65_A2 THEN
  CONJ_TAC THENL
   [MLD_CHALLENGE_WHILE_TAC
     `mld_poly_challenge_bytes 49 (mld_shake256_byte 48 C)`
     POLY_CHALLENGE_65_PCF POLY_CHALLENGE_65_PC2
     POLY_CHALLENGE_65_INV THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MLD_POLY_CHALLENGE_BYTES_POS THEN
      ASM_REWRITE_TAC[ARITH_EQ];
      POLY_CHALLENGE_65_PROLOGUE_TAC;
      POLY_CHALLENGE_65_BODY_TAC;
      FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `e2:(uarch_event)list` THEN ASM_REWRITE_TAC[]];
    POLY_CHALLENGE_65_EPILOGUE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
