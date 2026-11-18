(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Rejection sampling of coefficients in [-4,4]: the proof (see              *)
(* rej_eta_65_spec.ml).                                                      *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/rej_eta_65_spec.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;

let REJ_ETA_65_EXEC = MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The events. With D the list of the declassified values, two for each of   *)
(* the M = LENGTH D DIV 2 bytes that the loop reads, iteration i takes one   *)
(* of five paths: the first nibble accepted and stored, and then the second  *)
(* stored too if it is accepted and there is room (vv), not stored as there  *)
(* is no room (vf, which the x86 code tests with another jump than a         *)
(* rejected nibble, so with other events) or rejected (vx); or the first     *)
(* rejected, and the second accepted and stored (xv) or rejected (xx). The   *)
(* number of coefficients before iteration i, offset plus the number of T    *)
(* among the first 2 * i elements of D, gives the addresses of the stores.   *)
(* With offset = 256 the function returns at once.                           *)
(* ------------------------------------------------------------------------- *)

let REJ_ETA_65_TEMPLATE =
 `\(a:int64) (offset:num) (buf:int64) (buflen:num) (D:bool list) (pc:num)
   (stackpointer:int64) (returnaddress:int64).
   if offset = 256
   then f_ev_full a offset buf buflen D pc stackpointer returnaddress
   else
    APPEND (f_ev_epil a offset buf buflen D pc stackpointer returnaddress)
     (APPEND
       (ENUMERATEL (LENGTH D DIV 2)
         (\i. if EL (2 * i) D
              then if EL (2 * i + 1) D
                   then if offset +
                           LENGTH(FILTER (\x. x) (SUB_LIST(0,2 * i) D)) +
                           1 < 256
                        then f_ev_vv a offset buf buflen D pc stackpointer
                                     returnaddress i
                        else f_ev_vf a offset buf buflen D pc stackpointer
                                     returnaddress i
                   else f_ev_vx a offset buf buflen D pc stackpointer
                                returnaddress i
              else if EL (2 * i + 1) D
                   then f_ev_xv a offset buf buflen D pc stackpointer
                                returnaddress i
                   else f_ev_xx a offset buf buflen D pc stackpointer
                                returnaddress i))
       (f_ev_prol a offset buf buflen D pc stackpointer returnaddress))
   :(uarch_event)list`;;

(* ------------------------------------------------------------------------- *)
(* The invariant at the head of the loop after i bytes: the position in RDX, *)
(* the count in RSI and the coefficients stored so far, with RBX saved below *)
(* the return address.                                                       *)
(* ------------------------------------------------------------------------- *)

let REJ_ETA_65_INV =
 `\i s. read R8 s = a /\ read R9 s = word buflen /\ read R11 s = word 4 /\
        read R10 s = word_zx(word_sub (word 1) (word_zx buf):int32):int64 /\
        read RSP s = stackpointer /\
        read (memory :> bytes64 stackpointer) s = rbx_init /\
        read (memory :> bytes64 (word_add stackpointer (word 8))) s =
        returnaddress /\
        read RDX s = word_add buf (word i) /\
        read RSI s = word(offset + MIN (256 - offset)
                           (LENGTH(FILTER (\x. x) (SUB_LIST(0,2 * i) D)))) /\
        (!j. j < buflen
             ==> read(memory :> bytes8(word_add buf (word j))) s = b j) /\
        (!j. offset <= j /\
             j < offset + MIN (256 - offset)
                           (LENGTH(FILTER (\x. x) (SUB_LIST(0,2 * i) D)))
             ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                 EL (j - offset) (mld_rej_eta_list 4 b (2 * i)))`;;

(* ------------------------------------------------------------------------- *)
(* The facts for iteration i: the count c and the byte value nb (n in the    *)
(* AArch64 proofs, a name that the x86 simulation cannot use: see            *)
(* utils/mldsa_native_sampling.ml), with the acceptance of its two nibbles,  *)
(* the count after it, and whether the loop goes on after it.                *)
(* ------------------------------------------------------------------------- *)

let REJ_ETA_65_BODY_SETUP_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < M` ASSUME_TAC THENL
   [UNDISCH_TAC `i < LENGTH (D:bool list) DIV 2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i < M`) o
    check (fun th -> is_forall(concl th) &&
                     can (term_match [] `!m. m < M ==> P m`) (concl th))) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * i` o
    check (fun th -> is_forall(concl th) &&
                     can (term_match [] `!n. n <= 2 * M ==> P n`)
                         (concl th))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < M` THEN ARITH_TAC; DISCH_TAC] THEN
  FULL_INIT_TAC THEN
  ABBREV_TAC
   `c = LENGTH(FILTER (\x. x) (SUB_LIST (0,2 * i) (D:bool list)))` THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `c:num`)) THEN
  SUBGOAL_THEN `offset + c < 256` ASSUME_TAC THENL
   [UNDISCH_TAC `offset + LENGTH (mld_rej_eta_list 4 b (2 * i)) < 256` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `MIN (256 - offset) c = c`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `offset + c < 256` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i < buflen`) o SPEC `i:num` o
    check (fun th -> is_forall(concl th) && free_in `bytes8` (concl th))) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * (i + 1)` o
    check (fun th -> is_forall(concl th) &&
                     can (term_match [] `!n. n <= 2 * M ==> P n`)
                         (concl th))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < M` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP MLD_REJ_ETA_BYTES_NEXT
   (CONJ (ASSUME `mld_rej_eta_bytes 4 256 offset (b:num->byte) buflen = M`)
         (ASSUME `i < M`))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * i + 1` o
    check (fun th -> is_forall(concl th) &&
                     can (term_match [] `!k. k < 2 * M ==> P k`)
                         (concl th))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * i` o
    check (fun th -> is_forall(concl th) &&
                     can (term_match [] `!k. k < 2 * M ==> P k`)
                         (concl th))) THEN
  REWRITE_TAC[ARITH_RULE `2 * i < 2 * M <=> i < M`;
              ARITH_RULE `2 * i + 1 < 2 * M <=> i < M`; ASSUME `i < M`] THEN
  REWRITE_TAC[MLD_REJ_ETA_LIST_BYTE; LENGTH_APPEND; SAMPLING_LENGTH_COND;
              MLD_REJ_ETA_VALID_BYTE; mld_rej_eta_coeff;
              ASSUME `LENGTH (mld_rej_eta_list 4 b (2 * i)) = c`] THEN
  MP_TAC(ISPEC `(b:num->byte) i` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `nb = val((b:num->byte) i)` THEN REPEAT DISCH_TAC;;

(*** The first steps: the byte, its nibbles and the first compare ***)

let REJ_ETA_65_SIM1_TAC =
  X86_STEPS_TAC REJ_ETA_65_EXEC (1--4) THEN
  SAMPLING_REG_TAC `RCX` `word_zx(word_and ((b:num->byte) i) (word 15)):int64`
    [] THEN
  SAMPLING_REG_TAC `RAX` `word_zx(word_ushr ((b:num->byte) i) 4):int64`
    [SAMPLING_WORD_MOD_256; GSYM word_zx] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_BYTE_NIBBLES]) THEN
  RULE_ASSUM_TAC(fun th ->
    if concl th = `val((b:num->byte) i) = nb` then th
    else REWRITE_RULE[ASSUME `val((b:num->byte) i) = nb`] th) THEN
  SAMPLING_STEP_TAC REJ_ETA_65_EXEC 5;;

(*** The coefficients after iteration i: those before, and the new ones ***)

let REJ_ETA_65_STORE_TAC =
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[APPEND] THEN
  ASM_CASES_TAC `j < offset + c` THENL
   [REWRITE_TAC[EL_APPEND;
                ASSUME `LENGTH (mld_rej_eta_list 4 b (2 * i)) = c`] THEN
    SUBGOAL_THEN `j - offset < c` (fun th -> REWRITE_TAC[th]) THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && free_in `bytes32` (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `j = (offset + c) + 0 \/ j = (offset + c) + 1`
   (DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [SIMPLE_ARITH_TAC; ALL_TAC; ALL_TAC] THEN
  TRY(SUBGOAL_THEN `F` CONTR_TAC THEN SIMPLE_ARITH_TAC THEN NO_TAC) THEN
  REWRITE_TAC[EL_APPEND; ASSUME `LENGTH (mld_rej_eta_list 4 b (2 * i)) = c`;
              ARITH_RULE `((offset + c) + k) - offset = c + k`;
              ARITH_RULE `~(c + k < c)`; ARITH_RULE `(c + k) - c = k`] THEN
  CONV_TAC(RAND_CONV SAMPLING_EL_LIST_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[];;

(*** One path of the iteration, from the first branch to the loop test ***)

let REJ_ETA_65_PATH_TAC =
  SAMPLING_RUN_TAC REJ_ETA_65_EXEC 6
   [`word(pc + mld_rej_eta_c65_loop1):int64`;
    `word(pc + mld_rej_eta_c65_loop1_exit):int64`] THEN
  (SAMPLING_LOOP_PC_TAC `LENGTH (D:bool list) DIV 2`
     [SYM(ASSUME `M = LENGTH (D:bool list) DIV 2`)] ORELSE
   SAMPLING_LOOP_EXIT_TAC `LENGTH (D:bool list) DIV 2`
     [SYM(ASSUME `M = LENGTH (D:bool list) DIV 2`)]
     `word(pc + mld_rej_eta_c65_loop1):int64`) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_iff(concl th) && lhand(concl th) = `i + 1 < M`)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SAMPLING_W64_TAC THEN SAMPLING_SELECT_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(AP_TERM_TAC THEN SIMPLE_ARITH_TAC THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REJ_ETA_65_STORE_TAC THEN NO_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `c:num` &&
    can (term_match [] `LENGTH(FILTER (\x:bool. x) l)`) (lhs(concl th)))) THEN
  SAMPLING_PATH_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  CONCRETIZE_F_EVENTS_TAC REJ_ETA_65_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `offset:num`; `buf:int64`;
    `buflen:num`; `b:num->byte`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 8 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[SOME_FLAGS; C_ARGUMENTS;
              C_RETURN; NONOVERLAPPING_CLAUSES; ALL; fst REJ_ETA_65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN

  (*** The declassified values D, the number M of bytes read ***)

  REWRITE_TAC[MLD_REJ_ETA_CTR] THEN
  MP_TAC(SPECL [`4`; `256`; `offset:num`; `b:num->byte`; `buflen:num`]
    MLD_REJ_ETA_DECLASS) THEN
  MP_TAC(SPECL [`4`; `256`; `offset:num`; `b:num->byte`; `buflen:num`;
    `mld_rej_eta_bytes 4 256 offset (b:num->byte) buflen`]
    MLD_REJ_ETA_BYTES) THEN REWRITE_TAC[] THEN
  ABBREV_TAC `D = mld_rej_eta_declass 4 256 offset (b:num->byte) buflen` THEN
  ABBREV_TAC `M = mld_rej_eta_bytes 4 256 offset (b:num->byte) buflen` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `offset = 256` THENL
   [SUBGOAL_THEN `M = 0` ASSUME_TAC THENL
     [EXPAND_TAC "M" THEN MATCH_MP_TAC MLD_REJ_ETA_BYTES_0 THEN
      ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[SUB_REFL; ARITH_RULE `MIN 0 x = 0`; ADD_CLAUSES;
                    ARITH_RULE `~(i < n /\ n <= i)`; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC REJ_ETA_65_EXEC (1--4) THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MESON_TAC[NOT_LT]; DISCHARGE_SAFETY_PROPERTY_TAC];
    ALL_TAC] THEN

  (*** The loop over the bytes ***)

  REWRITE_TAC[ASSUME `~(offset = 256)`] THEN
  SUBGOAL_THEN `offset < 256` ASSUME_TAC THENL
   [UNDISCH_TAC `offset <= 256` THEN UNDISCH_TAC `~(offset = 256)` THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `0 < M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC MLD_REJ_ETA_BYTES_POS THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `l = 2 * M ==> M = l DIV 2`) o
    check (fun th -> concl th = `LENGTH (D:bool list) = 2 * M`)) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `LENGTH (D:bool list) DIV 2`
   `pc + mld_rej_eta_c65_loop1` `pc + mld_rej_eta_c65_loop1_exit`
   REJ_ETA_65_INV THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `M = LENGTH (D:bool list) DIV 2`)) THEN
    UNDISCH_TAC `0 < M` THEN ARITH_TAC;

    (*** Initialization, with RBX saved ***)

    FULL_INIT_TAC THEN X86_STEPS_TAC REJ_ETA_65_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC REJ_ETA_65_EXEC (2--2) THEN SAMPLING_DECIDE_BRANCH_TAC THEN
    X86_STEPS_TAC REJ_ETA_65_EXEC (3--9) THEN
    W32_SMALL_TAC THEN SAMPLING_W64_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; FILTER; LENGTH;
                ARITH_RULE `MIN a 0 = 0`; ADD_CLAUSES; WORD_ADD_0;
                ARITH_RULE `~(a <= j /\ j < a)`] THEN
    TRY(CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, in the paths of the two nibbles of the byte ***)

    REJ_ETA_65_BODY_SETUP_TAC THEN REJ_ETA_65_SIM1_TAC THEN
    SAMPLING_CASES_TAC `EL (2 * i) (D:bool list)` THENL
     [SAMPLING_CASES_TAC `EL (2 * i + 1) (D:bool list)` THENL
       [ASM_CASES_TAC `offset + c + 1 < 256` THEN REJ_ETA_65_PATH_TAC;
        REJ_ETA_65_PATH_TAC];
      SAMPLING_CASES_TAC `EL (2 * i + 1) (D:bool list)` THEN
      REJ_ETA_65_PATH_TAC];

    (*** The return, with RBX restored ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    X86_STEPS_TAC REJ_ETA_65_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `2 * M` o
      check (fun th -> is_forall(concl th) &&
                       can (term_match [] `!n. n <= 2 * M ==> P n`)
                           (concl th))) THEN
    REWRITE_TAC[LE_REFL; ASSUME `M = LENGTH (D:bool list) DIV 2`] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                         REWRITE_TAC[th]) THEN
    REPEAT CONJ_TAC THENL
     [W32_SMALL_TAC THEN SAMPLING_W64_TAC;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      MP_TAC(SPECL [`4`; `b:num->byte`; `2 * LENGTH (D:bool list) DIV 2`;
                    `2 * buflen`; `j - offset`] EL_MLD_REJ_ETA_LIST_PREFIX) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `M <= buflen` THEN
          REWRITE_TAC[ASSUME `M = LENGTH (D:bool list) DIV 2`] THEN ARITH_TAC;
          SIMPLE_ARITH_TAC];
        DISCH_THEN SUBST1_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCHARGE_SAFETY_PROPERTY_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
