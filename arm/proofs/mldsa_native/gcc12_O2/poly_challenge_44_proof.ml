(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The challenge polynomial (SampleInBall): the proof (see                   *)
(* poly_challenge_44_spec.ml), with the tools of                             *)
(* utils/mldsa_native_challenge.ml.                                          *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/poly_challenge_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_challenge.ml";;

let POLY_CHALLENGE_44_EXEC = MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_EXEC;;

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
(* (sa, ac, sr, rc).                                                         *)
(* ------------------------------------------------------------------------- *)

let POLY_CHALLENGE_44_TEMPLATE =
 `\(c:int64) (seed:int64) (C:num) (guard:int64) (mf:int64) (pc:num)
   (stackpointer:int64) (returnaddress:int64).
   APPEND (f_ev_epi c seed C guard mf pc stackpointer returnaddress)
    (APPEND
      (ENUMERATEL (mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C))
        (\n. if (8 + n) MOD 136 = 0
             then if mld_poly_challenge_accept 39 (mld_shake256_byte 32 C) n
                  then if n + 1 <
                          mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C)
                       then f_ev_sa c C pc stackpointer n
                       else f_ev_sx c C pc stackpointer n
                  else f_ev_sr c C pc stackpointer n
             else if mld_poly_challenge_accept 39 (mld_shake256_byte 32 C) n
                  then if n + 1 <
                          mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C)
                       then if (8 + (n + 1)) MOD 136 = 0
                            then f_ev_ab c C pc stackpointer n
                            else f_ev_ac c C pc stackpointer n
                       else f_ev_ax c C pc stackpointer n
                  else if (8 + (n + 1)) MOD 136 = 0
                       then f_ev_rb c C pc stackpointer n
                       else f_ev_rc c C pc stackpointer n))
      (f_ev_pro c seed C guard mf pc stackpointer returnaddress))
   :(uarch_event)list`;;

let POLY_CHALLENGE_44_ALLOWED =
  [`c:int64`; `seed:int64`; `C:num`; `guard:int64`; `mf:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`; `n:num`];;

let POLY_CHALLENGE_44_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc POLY_CHALLENGE_44_EXEC name
    ilist POLY_CHALLENGE_44_ALLOWED n;;

(* ------------------------------------------------------------------------- *)
(* The state at the head of the loop for byte n, with the frame of 448 bytes *)
(* at stackpointer + 256: the index i = 217 + k in X19, with k the number of *)
(* coefficients set so far, the position p = (7 + n) MOD 136 + 1 in X0,      *)
(* block (7 + n) DIV 136 of the output in the buffer, the context at         *)
(* stackpointer + 488 permuted once more, the polynomial so far at c, the    *)
(* sign bits not used yet at stackpointer + 312, the saved registers and the *)
(* canary at stackpointer + 696. The head is the read from the buffer at     *)
(* +0xac, or the test of the position at +0xbc before the squeeze when byte  *)
(* n starts a block; the loop ends at +0x110.                                *)
(* ------------------------------------------------------------------------- *)

let POLY_CHALLENGE_44_BUF =
  `word_add stackpointer
    (word(if aligned 32 stackpointer then 320 else 336)):int64`;;

let POLY_CHALLENGE_44_FRAME =
 `read X20 s = word_add stackpointer
                (word(if aligned 32 stackpointer then 320 else 336)) /\
  read X21 s = word_add stackpointer (word 488) /\
  read X22 s = word 1 /\
  read X23 s = c /\
  read SP s = word_add stackpointer (word 256) /\
  read (memory :> bytes32(word_add stackpointer (word 688))) s = word 136 /\
  read (memory :> bytes64(word_add stackpointer (word 256))) s = x19_init /\
  read (memory :> bytes64(word_add stackpointer (word 264))) s = x20_init /\
  read (memory :> bytes64(word_add stackpointer (word 272))) s = x21_init /\
  read (memory :> bytes64(word_add stackpointer (word 280))) s = x22_init /\
  read (memory :> bytes64(word_add stackpointer (word 288))) s = x23_init /\
  read (memory :> bytes64(word_add stackpointer (word 296))) s =
  returnaddress /\
  read (memory :> bytes64(word_add stackpointer (word 696))) s = canary /\
  read (memory :> bytes64(word_add (word pc) (word got_stack_chk_guard))) s =
  guard /\
  read (memory :> bytes64 guard) s = canary`;;

let POLY_CHALLENGE_44_INV =
  let body =
   `read X19 s =
    word(217 + FST(mld_poly_challenge_step 39 (mld_shake256_byte 32 C) n)) /\
    read X0 s = word((7 + n) MOD 136 + 1) /\
    read (memory :> bytes(word_add stackpointer
                           (word(if aligned 32 stackpointer then 320
                                 else 336)),136)) s =
    num_of_bytelist(list_of_seq
     (\t. mld_shake256_byte 32 C (136 * ((7 + n) DIV 136) + t)) 136) /\
    read (memory :> bytes(word_add stackpointer (word 488),200)) s =
    val(keccak_squeeze ((7 + n) DIV 136 + 1) (mld_shake256_state 32 C)) /\
    (!t. t < 256
         ==> read (memory :> bytes32(word_add c (word(4 * t)))) s =
             SND(mld_poly_challenge_step 39 (mld_shake256_byte 32 C) n) t) /\
    read (memory :> bytes64(word_add stackpointer (word 312))) s =
    word_ushr (mld_poly_challenge_signs (mld_shake256_byte 32 C))
              (FST(mld_poly_challenge_step 39 (mld_shake256_byte 32 C) n))` in
  list_mk_abs([`n:num`; `s:armstate`],
              list_mk_conj(conjuncts body @
                           conjuncts POLY_CHALLENGE_44_FRAME));;

let POLY_CHALLENGE_44_A2 =
  let t = subst [`mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C)`,
                 `n:num`]
                (snd(dest_abs(snd(dest_abs POLY_CHALLENGE_44_INV)))) in
  mk_abs(`s:armstate`,t);;

let POLY_CHALLENGE_44_PCF =
  `\n. if (8 + n) MOD 136 = 0 then pc + mldsa44_poly_challenge_loop2
       else pc + mldsa44_poly_challenge_join1`;;

(* ------------------------------------------------------------------------- *)
(* The setup: the callee theorems, the template, the stack frame, the saved  *)
(* registers, the stack guard as canary, the bounds of the offset of the     *)
(* buffer, and the termination hypothesis as an existence.                   *)
(* ------------------------------------------------------------------------- *)

let POLY_CHALLENGE_44_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th)
     "H_MEMSET") THEN
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
  CONCRETIZE_F_EVENTS_TAC POLY_CHALLENGE_44_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `c:int64`; `seed:int64`; `C:num`; `guard:int64`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 704 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst POLY_CHALLENGE_44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 704):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--23) THEN
  SUBGOAL_THEN
   `320 <= (if aligned 32 (stackpointer:int64) then 320 else 336) /\
    (if aligned 32 (stackpointer:int64) then 320 else 336) <= 336`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if concl th = `mld_poly_challenge_terminates 39 32 C`
    then ASSUME_TAC(REWRITE_RULE[mld_poly_challenge_terminates] th)
    else NO_TAC);;

let POLY_CHALLENGE_44_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 351))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 320 else 336))`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC MLD_CHALLENGE_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* To the head of the loop for byte 0: the prologue, init, absorbing the     *)
(* seed, finalizing, squeezing the first block (block 0 of the output), the  *)
(* sign bits from its first 8 bytes by the loop, simulated through, and the  *)
(* zeroing of the polynomial by memset.                                      *)
(* ------------------------------------------------------------------------- *)

let POLY_CHALLENGE_44_PROLOGUE_TAC =
  FULL_INIT_TAC THEN ARM_STEPS_TAC POLY_CHALLENGE_44_EXEC (1--3) THEN
  MLKEM_NATIVE_ADRP_TAC THEN ARM_STEPS_TAC POLY_CHALLENGE_44_EXEC (4--15) THEN
  POLY_CHALLENGE_44_BUFFER_TAC THEN
  POLY_CHALLENGE_44_CALL_TAC "H_INIT" [`read X0 s`; `pc:num`; `read X30 s`] 16
  THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC POLY_CHALLENGE_44_EXEC (17--20) THEN
  KECCAK_STATE_AT_TAC `word_add stackpointer (word 488):int64` THEN
  POLY_CHALLENGE_44_CALL_TAC "H_ABSORB"
   [`read X0 s`; `read X1 s`; `32`; `word 0:1600 word`; `0`; `C:num`;
    `pc:num`; `read SP s`; `read X30 s`] 21 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES;
                              READ_MEMORY_WBYTES_1600;
                              NUM_REDUCE_CONV `32 MOD 136`]) THEN
  ARM_STEPS_TAC POLY_CHALLENGE_44_EXEC (22--23) THEN
  KECCAK_STATE_AT_TAC `word_add stackpointer (word 488):int64` THEN
  MLD_CHALLENGE_GOT_TAC [`got_stack_chk_guard:num`; `got_memset:num`]
  THEN
  POLY_CHALLENGE_44_CALL_TAC "H_FINALIZE"
   [`read X0 s`; `FST(mld_keccak_absorb 136 (word 0) 0 32 C)`; `32`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 24 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600;
    MATCH_MP MLD_CHALLENGE_STATE (ARITH_RULE `32 < 136`)]) THEN
  ARM_STEPS_TAC POLY_CHALLENGE_44_EXEC (25--28) THEN
  KECCAK_STATE_AT_TAC `word_add stackpointer (word 488):int64` THEN
  POLY_CHALLENGE_44_CALL_TAC "H_SQUEEZE"
   [`read X0 s`; `136`; `read X2 s`; `mld_shake256_state 32 C`; `136`;
    `pc:num`; `read SP s`; `read X30 s`] 29 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600;
    MLD_CHALLENGE_SQUEEZE_STATE; GSYM mld_shake256_byte]) THEN
  MLD_CHALLENGE_BYTES_TAC POLY_CHALLENGE_44_BUF (map mk_small_numeral (0--7))
  THEN
  ARM_STEPS_TAC POLY_CHALLENGE_44_EXEC (30--80) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_CHALLENGE_SIGNS_WORD; ETA_AX]) THEN
  ARM_STEPS_TAC POLY_CHALLENGE_44_EXEC (81--85) THEN
  LIBC_PLT_TAC POLY_CHALLENGE_44_EXEC 85 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" POLY_CHALLENGE_44_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref POLY_CHALLENGE_44_ALLOWED) 90 THEN
  MEMSET_ZERO_BYTES_TAC THEN ARM_STEPS_TAC POLY_CHALLENGE_44_EXEC (91--96) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_CHALLENGE_ZERO_POLY o check (fun th ->
    can (term_match [] `read (memory :> bytes(c,1024)) s = 0`) (concl th))) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[CONJUNCT1 ENUMERATEL; CONJUNCT1 APPEND;
              CONJUNCT1 mld_poly_challenge_step; WORD_USHR_ZERO] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; ETA_AX] THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  MLD_PREFIX_DISCHARGE_TAC ALL_TAC;;

(* ------------------------------------------------------------------------- *)
(* The iteration for byte n. The proof abbreviates k (the number of          *)
(* coefficients set before) and j (the byte), and in the cases of the        *)
(* position p and the block b, and puts them back before matching the events *)
(* with the template (POLY_CHALLENGE_44_FINAL_TAC, which also proves the new *)
(* polynomial for an accepted byte).                                         *)
(* ------------------------------------------------------------------------- *)

let POLY_CHALLENGE_44_ABBREV_TAC =
  ABBREV_TAC
   `k = FST (mld_poly_challenge_step 39 (mld_shake256_byte 32 C) n)` THEN
  ABBREV_TAC `j = val(mld_shake256_byte 32 C (8 + n))` THEN
  SUBGOAL_THEN `j < 256` ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN
    MP_TAC(ISPEC `mld_shake256_byte 32 C (8 + n)` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_zx(word(217 + k):int64):int32) = 217 + k /\
                val(word(217 + k):int64) = 217 + k /\
                val(word j:int64) = j`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MLD_CHALLENGE_VAL_ZX_WORD;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64];
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64]] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC];;

let POLY_CHALLENGE_44_UNABBREV_TAC =
  MLD_CHALLENGE_UNABBREV_TAC
   [`val(mld_shake256_byte 32 C (8 + n))`,`j:num`;
    `FST (mld_poly_challenge_step 39 (mld_shake256_byte 32 C) n)`,`k:num`;
    `(7 + n) DIV 136`,`b:num`;
    `(7 + n) MOD 136 + 1`,`p:num`];;

let POLY_CHALLENGE_44_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MLD_POLY_CHALLENGE_STEP_ADD1] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  TRY(CONJ_TAC THENL [MLD_CHALLENGE_POLY_TAC `217 + k`; ALL_TAC]) THEN
  POLY_CHALLENGE_44_UNABBREV_TAC THEN
  MLD_CHALLENGE_DISCHARGE_TAC
   (TRY(ABBREV_TAC `jj = val(mld_shake256_byte 32 C (8 + n))`));;

(*** The code for an accepted byte, from +0xe4 at step m to +0x110 or +0xbc ***)

let POLY_CHALLENGE_44_ACCEPT_TAC m pnext =
  let rest =
    ARM_STEPS_TAC POLY_CHALLENGE_44_EXEC ((m+2)--(m+10)) THEN
    MLD_CHALLENGE_EXIT_TEST_TAC THEN
    MLD_CHALLENGE_FIX_TAC mld_challenge_is_bytes32
     [MLD_CHALLENGE_SIGN_WORD; BIT_WORD_USHR; ADD_CLAUSES;
      GSYM mld_poly_challenge_sign] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_USHR_COMPOSE]) THEN
    MLD_CHALLENGE_FIX_TAC (mld_challenge_is_read_reg `X19`)
     [GSYM WORD_ADD; GSYM ADD_ASSOC] THEN
    (SUBGOAL_THEN
      `mld_poly_challenge_accept 39 (mld_shake256_byte 32 C) n`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    (ASM_CASES_TAC `k + 1 = 39` THENL
      [(SUBGOAL_THEN
         `~(n + 1 < mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C))`
        ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
       MLD_CHALLENGE_BRANCH_TAC THEN POLY_CHALLENGE_44_FINAL_TAC;
       (SUBGOAL_THEN
         `n + 1 < mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C)`
        ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
       MLD_CHALLENGE_BRANCH_TAC THEN pnext (m + 11)]) in
  MLD_CHALLENGE_FIX_TAC (mld_challenge_is_read_reg `X1`)
   [MLD_CHALLENGE_ZX_BYTE;
    ASSUME `val(mld_shake256_byte 32 C (8 + n)) = j`] THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `bytes32` (concl th)
    then ASSUME_TAC(MP (SPEC `j:num` th) (ASSUME `j < 256`)) else NO_TAC) THEN
  ARM_STEPS_TAC POLY_CHALLENGE_44_EXEC (m--(m+1)) THEN
  MLD_CHALLENGE_EXCLUDE_TAC `217 + k` `j:num` THEN
  ASM_CASES_TAC `j < 217 + k` THEN rest;;

(*** The termination facts for byte n, and acceptance as a comparison ***)

let POLY_CHALLENGE_44_SETUP_TAC =
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

(*** A byte read from the buffer, at p < 136 ***)

let POLY_CHALLENGE_44_NORMAL_TAC =
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
  POLY_CHALLENGE_44_ABBREV_TAC THEN
  FULL_INIT_TAC THEN
  MLD_CHALLENGE_LOAD_TAC POLY_CHALLENGE_44_BUF `p:num`
   [ASSUME `136 * b + p = 8 + n`] THEN
  MLD_CHALLENGE_UXTW_TAC `p:num` THEN
  ARM_STEPS_TAC POLY_CHALLENGE_44_EXEC (1--4) THEN
  MLD_CHALLENGE_ZX_ZX_TAC `p:num` THEN
  MP_TAC(SPEC `p:num` MLD_PREFIX_ZX_ADD1) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  MLD_CHALLENGE_FIX_TAC (mld_challenge_is_read_reg `X0`) [ASSUME
     `word_zx (word_add (word_zx (word p:int64):int32) (word 1)):int64 =
      word (p + 1)`] THEN
  SUBGOAL_THEN `val(word_zx(word(p + 1):int64):int32) = p + 1` ASSUME_TAC
  THENL [MATCH_MP_TAC MLD_CHALLENGE_VAL_ZX_WORD THEN SIMPLE_ARITH_TAC;
         ALL_TAC] THEN
  let next m =
    ASM_CASES_TAC `p = 135` THENL
     [(SUBGOAL_THEN `(8 + (n + 1)) MOD 136 = 0` ASSUME_TAC THENL
        [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      POLY_CHALLENGE_44_FINAL_TAC;
      (SUBGOAL_THEN `~((8 + (n + 1)) MOD 136 = 0)` ASSUME_TAC THENL
        [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      ARM_STEPS_TAC POLY_CHALLENGE_44_EXEC (m--(m+1)) THEN
      MLD_CHALLENGE_BRANCH_TAC THEN POLY_CHALLENGE_44_FINAL_TAC] in
  (ASM_CASES_TAC `j <= 217 + k` THENL
   [MLD_CHALLENGE_BRANCH_TAC THEN POLY_CHALLENGE_44_ACCEPT_TAC 5 next;
    MLD_CHALLENGE_BRANCH_TAC THEN
    (SUBGOAL_THEN
      `~mld_poly_challenge_accept 39 (mld_shake256_byte 32 C) n`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    (SUBGOAL_THEN
      `n + 1 < mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C)`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    next 5]);;

(*** A byte that starts a block, read after squeezing the block ***)

let POLY_CHALLENGE_44_SQUEEZE_TAC =
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
  POLY_CHALLENGE_44_ABBREV_TAC THEN
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC POLY_CHALLENGE_44_EXEC (1--6) THEN
  KECCAK_STATE_AT_TAC `word_add stackpointer (word 488):int64` THEN
  POLY_CHALLENGE_44_CALL_TAC "H_SQUEEZE"
   [`read X0 s`; `136`; `read X2 s`;
    `keccak_squeeze (b + 1) (mld_shake256_state 32 C)`; `136`; `pc:num`;
    `read SP s`; `read X30 s`] 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600;
    MLD_CHALLENGE_SQUEEZE_STATE; MLD_CHALLENGE_SQUEEZE_ADD;
    MLD_CHALLENGE_SQUEEZE_BYTE_FUN; ARITH_RULE `1 + b + 1 = (b + 1) + 1`])
  THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_shake256_byte]) THEN
  (SUBGOAL_THEN `136 * (b + 1) + 0 = 8 + n` ASSUME_TAC THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]) THEN
  MLD_CHALLENGE_LOAD_TAC POLY_CHALLENGE_44_BUF `0`
   [ASSUME `136 * (b + 1) + 0 = 8 + n`] THEN
  ARM_STEPS_TAC POLY_CHALLENGE_44_EXEC (8--11) THEN
  let next m =
    ARM_STEPS_TAC POLY_CHALLENGE_44_EXEC (m--(m+1)) THEN
    MLD_CHALLENGE_BRANCH_TAC THEN POLY_CHALLENGE_44_FINAL_TAC in
  (ASM_CASES_TAC `j <= 217 + k` THENL
   [MLD_CHALLENGE_BRANCH_TAC THEN POLY_CHALLENGE_44_ACCEPT_TAC 12 next;
    MLD_CHALLENGE_BRANCH_TAC THEN
    (SUBGOAL_THEN
      `~mld_poly_challenge_accept 39 (mld_shake256_byte 32 C) n`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    (SUBGOAL_THEN
      `n + 1 < mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C)`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    POLY_CHALLENGE_44_FINAL_TAC]);;

let POLY_CHALLENGE_44_BODY_TAC =
  POLY_CHALLENGE_44_SETUP_TAC THEN
  ASM_CASES_TAC `(8 + n) MOD 136 = 0` THENL
   [POLY_CHALLENGE_44_SQUEEZE_TAC; POLY_CHALLENGE_44_NORMAL_TAC];;

(* ------------------------------------------------------------------------- *)
(* After the last byte: releasing the context, zeroing the buffer and the    *)
(* sign bits, the stack guard and the return, with the polynomial after the  *)
(* mld_poly_challenge_bytes bytes, which is mld_poly_challenge.              *)
(* ------------------------------------------------------------------------- *)

let POLY_CHALLENGE_44_EPILOGUE_TAC =
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC POLY_CHALLENGE_44_EXEC (1--2) THEN
  POLY_CHALLENGE_44_CALL_TAC "H_RELEASE" [`read X0 s`; `pc:num`; `read X30 s`] 3
  THEN
  ARM_STEPS_TAC POLY_CHALLENGE_44_EXEC (4--12) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC POLY_CHALLENGE_44_EXEC (13--22) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[mld_poly_challenge] THEN
  MLD_PREFIX_DISCHARGE_TAC ALL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  POLY_CHALLENGE_44_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa44_poly_challenge_loop2_exit`
    POLY_CHALLENGE_44_A2 THEN
  CONJ_TAC THENL
   [MLD_CHALLENGE_WHILE_TAC
     `mld_poly_challenge_bytes 39 (mld_shake256_byte 32 C)`
     POLY_CHALLENGE_44_PCF `pc + mldsa44_poly_challenge_loop2_exit`
     POLY_CHALLENGE_44_INV THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MLD_POLY_CHALLENGE_BYTES_POS THEN
      ASM_REWRITE_TAC[ARITH_EQ];
      POLY_CHALLENGE_44_PROLOGUE_TAC;
      POLY_CHALLENGE_44_BODY_TAC;
      FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `e2:(uarch_event)list` THEN ASM_REWRITE_TAC[]];
    POLY_CHALLENGE_44_EPILOGUE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
