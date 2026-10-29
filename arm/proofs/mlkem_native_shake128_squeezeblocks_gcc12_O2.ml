(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing whole blocks from a SHAKE128 state. This is the code for        *)
(* mlkem_shake128_squeezeblocks from mlkem-native's portable C               *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which for each of nblocks blocks permutes the state and then extracts the *)
(* first 168 bytes of it, the rate of SHAKE128. It is verified in the whole  *)
(* image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address     *)
(* 0x24e4, using the theorems for mlkem_keccakf1600_permute at 0x2dd0 and    *)
(* mlkem_keccakf1600_extract_bytes at 0x2c60 in the image.                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_keccakf1600_permute_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_keccakf1600_extract_bytes_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    24e4: cbz     x1, 2534 <mlkem_shake128_squeezeblocks+0x50>
    24e8: stp     x19, x20, [sp, #-32]!
    24ec: mov     x20, x0
    24f0: mov     x19, x1
    24f4: stp     x21, x30, [sp, #16]
    24f8: mov     x21, x2
    24fc: nop
    2500: mov     x0, x21
    2504: bl      2dd0 <mlkem_keccakf1600_permute>
    2508: mov     x1, x20
    250c: mov     x0, x21
    2510: mov     w3, #0xa8
    2514: mov     w2, #0x0
    2518: bl      2c60 <mlkem_keccakf1600_extract_bytes>
    251c: add     x20, x20, #0xa8
    2520: subs    x19, x19, #0x1
    2524: b.ne    2500 <mlkem_shake128_squeezeblocks+0x1c>
    2528: ldp     x21, x30, [sp, #16]
    252c: ldp     x19, x20, [sp], #32
    2530: ret
    2534: ret
 ***)

let MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x24e4,0x2538];;

(* ------------------------------------------------------------------------- *)
(* Tactics for the calls, and for the number of blocks as a 64-bit word.     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_PERMUTE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600);;

let LOCAL_EXTRACT_BYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

(*** The bound on nblocks from the nonoverlapping, and its 64-bit word ***)

let SQUEEZEBLOCKS_BOUND_TAC =
  SUBGOAL_THEN `200 + 168 * nblocks <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(out:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word nblocks:int64) = nblocks` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

(*** The test of nblocks = 0 at the start, when it is known to be false ***)

let SQUEEZEBLOCKS_NONZERO_TAC =
  let t1 = `val(word nblocks:int64) = nblocks` and t2 = `~(nblocks = 0)` in
  RULE_ASSUM_TAC(fun th ->
    if concl th = t1 || concl th = t2 then th
    else REWRITE_RULE[ASSUME t1; ASSUME t2] th);;

(*** The loop counter nblocks - i after the subtraction, and its test ***)

let SQUEEZEBLOCKS_COUNTER_TAC =
  SUBGOAL_THEN `word_sub (word (nblocks - i)) (word 1):int64 =
                word(nblocks - (i + 1))` SUBST_ALL_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
    ANTS_TAC THENL [UNDISCH_TAC `i < nblocks` THEN ARITH_TAC;
                    DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(nblocks - (i + 1)):int64) = nblocks - (i + 1)`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(nblocks - (i + 1) = 0) <=> i + 1 < nblocks`
  SUBST_ALL_TAC THENL [ARITH_TAC; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The state is a 1600-bit word S, as in                  *)
(* common/fips202.ml and for mlk_keccak_absorb_once. Block i of the output,  *)
(* as a number, is the first 168 bytes of keccak_squeeze (i + 1) S, the      *)
(* state after i + 1 permutations, and the final state is                    *)
(* keccak_squeeze nblocks S. When S is the result of                         *)
(* mlkem_shake128_absorb_once, these are the bytes of the output of shake128 *)
(* in common/fips202.ml.                                                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!out nblocks st (S:1600 word) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(out,168 * nblocks); (st,200);
          (word_sub stackpointer (word 224),224)] /\
        ALL (nonoverlapping (word pc,0x6480))
         [(out,168 * nblocks); (st,200);
          (word_sub stackpointer (word 224),224)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x24e4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word nblocks; st] s /\
                  read (memory :> wbytes st) s = S)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,168 * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * 168 * i) *
                        val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 168)) /\
                  read (memory :> wbytes st) s = keccak_squeeze nblocks S)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,168 * nblocks); memory :> bytes(st,200);
                memory :> bytes(word_sub stackpointer (word 224),224)])`,
  MAP_EVERY X_GEN_TAC
   [`out:int64`; `nblocks:num`; `st:int64`; `S:1600 word`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 224 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The case nblocks = 0, where nothing is done ***)

  ASM_CASES_TAC `nblocks = 0` THENL
   [ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze];
    ALL_TAC] THEN
  SQUEEZEBLOCKS_BOUND_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN

  (*** The loop, with i blocks done ***)

  ENSURES_WHILE_UP2_TAC `nblocks:num` `pc + 0x2500` `pc + 0x2528`
   `\i s. read X19 s = word(nblocks - i) /\
          read X20 s = word_add out (word(168 * i)) /\
          read X21 s = st /\
          read SP s = word_add stackpointer (word 192) /\
          read (memory :> bytes64 (word_add stackpointer (word 192))) s =
          x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 200))) s =
          x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 208))) s =
          x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 216))) s =
          returnaddress /\
          read (memory :> bytes(out,168 * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * 168 * j) *
                val(keccak_squeeze (j + 1) S) MOD 2 EXP (8 * 168)) /\
          read (memory :> bytes(st,200)) s =
          val(keccak_squeeze i (S:1600 word))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC (1--1) THEN
    SQUEEZEBLOCKS_NONZERO_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC (2--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze];

    (*** The loop body: permute, extract a block, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `168 * i + 168 <= 168 * nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `i < nblocks` THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC (1--2) THEN
    KECCAK_STATE_WBYTES_TAC `keccak_squeeze i (S:1600 word)` THEN
    LOCAL_PERMUTE_TAC
     [`read X0 s`; `keccak_squeeze i (S:1600 word)`; `pc:num`; `read SP s`;
      `read X30 s`] 3 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC (4--8) THEN
    KECCAK_STATE_WBYTES_TAC `keccak_f1600(keccak_squeeze i (S:1600 word))` THEN
    LOCAL_EXTRACT_BYTES_TAC
     [`read X0 s`; `read X1 s`; `0`; `168`;
      `keccak_f1600(keccak_squeeze i (S:1600 word))`; `pc:num`;
      `read X30 s`] 9 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (10--12) THEN
    SQUEEZEBLOCKS_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[];
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      REWRITE_TAC[ARITH_RULE `168 * (i + 1) = 168 * i + 168`];
      REWRITE_TAC[ARITH_RULE `168 * (i + 1) = 168 * i + 168`] THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM ADD1; NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
      REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1];
      REWRITE_TAC[GSYM ADD1; keccak_squeeze]];

    (*** The return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let SQUEEZEBLOCKS_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref
       [`out:int64`; `nblocks:num`; `st:int64`; `pc:num`;
        `stackpointer:int64`; `returnaddress:int64`;
        (* inside the loop... *)
        `i:num`;
        `f_ev_loop:int64->num->int64->num->int64->int64->num->
                   (uarch_event)list`]);
      LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e out nblocks st pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [out,168 * nblocks; st,200; word_sub stackpointer (word 224),224] /\
       ALL (nonoverlapping (word pc,0x6480))
        [out,168 * nblocks; st,200; word_sub stackpointer (word 224),224]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + 0x24e4) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; word nblocks; st] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events out nblocks st pc
                           (word_sub stackpointer (word 224)) returnaddress /\
                    memaccess_inbounds e2
                     [out,168 * nblocks; st,200;
                      word_sub stackpointer (word 224),224;
                      word(pc + 0x62b0),192]
                     [out,168 * nblocks; st,200;
                      word_sub stackpointer (word 224),224]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,168 * nblocks); memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 224),224)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_EXTRACT" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(out:int64) (nblocks:num) (st:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      if nblocks = 0
      then f_ev_zero out nblocks st pc stackpointer returnaddress
      else APPEND (f_ev_epil out nblocks st pc stackpointer returnaddress)
            (APPEND
              (ENUMERATEL nblocks
                (\i. f_ev_loop out nblocks st pc stackpointer returnaddress i))
              (f_ev_prol out nblocks st pc stackpointer returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SQUEEZEBLOCKS_BOUND_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ASM_CASES_TAC `nblocks = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `nblocks:num` `pc + 0x2500` `pc + 0x2528`
   `\i s. read X19 s = word(nblocks - i) /\
          read X20 s = word_add out (word(168 * i)) /\
          read X21 s = st /\
          read SP s = word_add stackpointer (word 192) /\
          read (memory :> bytes64 (word_add stackpointer (word 192))) s =
          x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 200))) s =
          x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 208))) s =
          x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 216))) s =
          returnaddress` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC (1--1) THEN
    SQUEEZEBLOCKS_NONZERO_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC (2--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `168 * i + 168 <= 168 * nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `i < nblocks` THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC (1--2) THEN
    SQUEEZEBLOCKS_SAFE_CALL_TAC "H_PERMUTE"
      [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
       `read X30 s`] 3 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC (4--8) THEN
    SQUEEZEBLOCKS_SAFE_CALL_TAC "H_EXTRACT"
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `0`; `168`;
       `pc:num`; `read X30 s`] 9 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (10--12) THEN
    SQUEEZEBLOCKS_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      REWRITE_TAC[ARITH_RULE `168 * (i + 1) = 168 * i + 168`];
      ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;
