(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing whole blocks from four SHAKE128 states. This is the code for    *)
(* mlkem_shake128x4_squeezeblocks from mlkem-native's portable C             *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which for each of nblocks blocks permutes the four states with            *)
(* mlkem_keccakf1600x4_permute and then extracts the first 168 bytes of      *)
(* each with mlkem_keccakf1600x4_extract_bytes. It is verified in the whole  *)
(* image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address     *)
(* 0x2974, using the theorems for those functions at 0x33a0 and 0x2cd0.      *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_keccakf1600x4_permute_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_keccakf1600x4_extract_bytes_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    2974: cbz     x4, 29f4 <mlkem_shake128x4_squeezeblocks+0x80>
    2978: stp     x19, x20, [sp, #-64]!
    297c: mov     x20, x2
    2980: mov     x19, x3
    2984: stp     x21, x22, [sp, #16]
    2988: mov     x22, x0
    298c: mov     x21, x1
    2990: stp     x23, x24, [sp, #32]
    2994: mov     x23, x4
    2998: mov     x24, x5
    299c: str     x30, [sp, #48]
    29a0: mov     x0, x24
    29a4: bl      33a0 <mlkem_keccakf1600x4_permute>
    29a8: mov     x4, x19
    29ac: mov     x3, x20
    29b0: mov     x2, x21
    29b4: mov     x1, x22
    29b8: mov     x0, x24
    29bc: mov     w6, #0xa8
    29c0: mov     w5, #0x0
    29c4: bl      2cd0 <mlkem_keccakf1600x4_extract_bytes>
    29c8: add     x19, x19, #0xa8
    29cc: add     x20, x20, #0xa8
    29d0: add     x21, x21, #0xa8
    29d4: add     x22, x22, #0xa8
    29d8: subs    x23, x23, #0x1
    29dc: b.ne    29a0 <mlkem_shake128x4_squeezeblocks+0x2c>
    29e0: ldp     x21, x22, [sp, #16]
    29e4: ldp     x23, x24, [sp, #32]
    29e8: ldr     x30, [sp, #48]
    29ec: ldp     x19, x20, [sp], #64
    29f0: ret
    29f4: ret
 ***)

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x2974,0x29f8];;

(* ------------------------------------------------------------------------- *)
(* Tactics for the four states, the number of blocks and the loop counter.   *)
(* ------------------------------------------------------------------------- *)

let SQX4_STATES_TAC =
  MAP_EVERY KECCAK_STATE_AT_TAC
   [`st:int64`; `word_add (st:int64) (word 200)`;
    `word_add (st:int64) (word 400)`; `word_add (st:int64) (word 600)`];;

let SQX4_BOUND_TAC =
  SUBGOAL_THEN `800 + 168 * nblocks <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(out0:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word nblocks:int64) = nblocks` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

let SQX4_PRESERVED_TAC =
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24`;;

let SQX4_NONZERO_TAC =
  let t1 = `val(word nblocks:int64) = nblocks` and t2 = `~(nblocks = 0)` in
  RULE_ASSUM_TAC(fun th ->
    if concl th = t1 || concl th = t2 then th
    else REWRITE_RULE[ASSUME t1; ASSUME t2] th);;

let SQX4_COUNTER_TAC =
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
(* Correctness proof. As for mlkem_shake128_squeezeblocks, for each of the   *)
(* four states S, block i of its output, as a number, is the first 168       *)
(* bytes of keccak_squeeze (i + 1) S, and the state becomes                  *)
(* keccak_squeeze nblocks S.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!out0 out1 out2 out3 nblocks st
    (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
    pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(out0,168 * nblocks); (out1,168 * nblocks); (out2,168 * nblocks);
          (out3,168 * nblocks); (st,800);
          (word_sub stackpointer (word 272),272)] /\
        ALL (nonoverlapping (word pc,0x6480))
         [(out0,168 * nblocks); (out1,168 * nblocks); (out2,168 * nblocks);
          (out3,168 * nblocks); (st,800);
          (word_sub stackpointer (word 272),272)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x2974) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st] s /\
                  read (memory :> wbytes st) s = S0 /\
                  read (memory :> wbytes (word_add st (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add st (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add st (word 600))) s = S3)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out0,168 * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * 168 * i) *
                        val(keccak_squeeze (i + 1) S0) MOD 2 EXP (8 * 168)) /\
                  read (memory :> bytes(out1,168 * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * 168 * i) *
                        val(keccak_squeeze (i + 1) S1) MOD 2 EXP (8 * 168)) /\
                  read (memory :> bytes(out2,168 * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * 168 * i) *
                        val(keccak_squeeze (i + 1) S2) MOD 2 EXP (8 * 168)) /\
                  read (memory :> bytes(out3,168 * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * 168 * i) *
                        val(keccak_squeeze (i + 1) S3) MOD 2 EXP (8 * 168)) /\
                  read (memory :> wbytes st) s = keccak_squeeze nblocks S0 /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  keccak_squeeze nblocks S1 /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  keccak_squeeze nblocks S2 /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  keccak_squeeze nblocks S3)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out0,168 * nblocks);
                memory :> bytes(out1,168 * nblocks);
                memory :> bytes(out2,168 * nblocks);
                memory :> bytes(out3,168 * nblocks);
                memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 272),272)])`,
  MAP_EVERY X_GEN_TAC
   [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`; `nblocks:num`;
    `st:int64`; `S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
    `S3:1600 word`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 272 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The case nblocks = 0, where nothing is done ***)

  ASM_CASES_TAC `nblocks = 0` THENL
   [ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze];
    ALL_TAC] THEN
  SQX4_BOUND_TAC THEN SQX4_PRESERVED_TAC THEN

  (*** The loop, with i blocks done ***)

  ENSURES_WHILE_UP2_TAC `nblocks:num` `pc + 0x29a0` `pc + 0x29e0`
   `\i s. read X19 s = word_add out3 (word(168 * i)) /\
          read X20 s = word_add out2 (word(168 * i)) /\
          read X21 s = word_add out1 (word(168 * i)) /\
          read X22 s = word_add out0 (word(168 * i)) /\
          read X23 s = word(nblocks - i) /\
          read X24 s = st /\
          read SP s = word_add stackpointer (word 208) /\
          read (memory :> bytes64 (word_add stackpointer (word 208))) s =
          x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 216))) s =
          x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 224))) s =
          x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 232))) s =
          x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 240))) s =
          x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 248))) s =
          x24_init /\
          read (memory :> bytes64 (word_add stackpointer (word 256))) s =
          returnaddress /\
          read (memory :> bytes(out0,168 * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * 168 * j) *
                val(keccak_squeeze (j + 1) S0) MOD 2 EXP (8 * 168)) /\
          read (memory :> bytes(out1,168 * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * 168 * j) *
                val(keccak_squeeze (j + 1) S1) MOD 2 EXP (8 * 168)) /\
          read (memory :> bytes(out2,168 * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * 168 * j) *
                val(keccak_squeeze (j + 1) S2) MOD 2 EXP (8 * 168)) /\
          read (memory :> bytes(out3,168 * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * 168 * j) *
                val(keccak_squeeze (j + 1) S3) MOD 2 EXP (8 * 168)) /\
          read (memory :> bytes(st,200)) s =
          val(keccak_squeeze i (S0:1600 word)) /\
          read (memory :> bytes(word_add st (word 200),200)) s =
          val(keccak_squeeze i (S1:1600 word)) /\
          read (memory :> bytes(word_add st (word 400),200)) s =
          val(keccak_squeeze i (S2:1600 word)) /\
          read (memory :> bytes(word_add st (word 600),200)) s =
          val(keccak_squeeze i (S3:1600 word))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--1) THEN
    SQX4_NONZERO_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (2--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze];

    (*** The loop body: permute, extract a block of each, the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `168 * i + 168 <= 168 * nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `i < nblocks` THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--2) THEN
    SQX4_STATES_TAC THEN
    ARM_SUBROUTINE_SIM_TAC
     (mlkem_native_libmlkem_gcc12_O2_mc,
      MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC,
      0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600)
     [`read X0 s`; `keccak_squeeze i (S0:1600 word)`;
      `keccak_squeeze i (S1:1600 word)`; `keccak_squeeze i (S2:1600 word)`;
      `keccak_squeeze i (S3:1600 word)`; `pc:num`; `read SP s`;
      `read X30 s`] 3 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (4--11) THEN
    SQX4_STATES_TAC THEN
    ARM_SUBROUTINE_SIM_TAC
     (mlkem_native_libmlkem_gcc12_O2_mc,
      MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC,
      0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT)
     [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`; `0`;
      `168`; `keccak_f1600(keccak_squeeze i (S0:1600 word))`;
      `keccak_f1600(keccak_squeeze i (S1:1600 word))`;
      `keccak_f1600(keccak_squeeze i (S2:1600 word))`;
      `keccak_f1600(keccak_squeeze i (S3:1600 word))`; `pc:num`;
      `read SP s`; `read X30 s`] 12 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (13--18) THEN
    SQX4_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        REWRITE_TAC[ARITH_RULE `168 * (i + 1) = 168 * i + 168`] THEN
        NO_TAC) THEN
    TRY(REWRITE_TAC[GSYM ADD1; keccak_squeeze] THEN NO_TAC) THEN
    REWRITE_TAC[ARITH_RULE `168 * (i + 1) = 168 * i + 168`] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM ADD1; NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1];

    (*** The return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let SQX4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref
       [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`;
        `nblocks:num`; `st:int64`; `pc:num`; `stackpointer:int64`;
        `returnaddress:int64`;
        (* inside the loop... *)
        `i:num`;
        `f_ev_loop:int64->int64->int64->int64->num->int64->num->int64->
                   int64->num->(uarch_event)list`]);
      LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e out0 out1 out2 out3 nblocks st pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [out0,168 * nblocks; out1,168 * nblocks; out2,168 * nblocks;
         out3,168 * nblocks; st,800; word_sub stackpointer (word 272),272] /\
       ALL (nonoverlapping (word pc,0x6480))
        [out0,168 * nblocks; out1,168 * nblocks; out2,168 * nblocks;
         out3,168 * nblocks; st,800; word_sub stackpointer (word 272),272]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + 0x2974) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events out0 out1 out2 out3 nblocks st pc
                           (word_sub stackpointer (word 272)) returnaddress /\
                    memaccess_inbounds e2
                     [out0,168 * nblocks; out1,168 * nblocks;
                      out2,168 * nblocks; out3,168 * nblocks; st,800;
                      word_sub stackpointer (word 272),272;
                      word(pc + 0x62b0),192]
                     [out0,168 * nblocks; out1,168 * nblocks;
                      out2,168 * nblocks; out3,168 * nblocks; st,800;
                      word_sub stackpointer (word 272),272]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out0,168 * nblocks);
               memory :> bytes(out1,168 * nblocks);
               memory :> bytes(out2,168 * nblocks);
               memory :> bytes(out3,168 * nblocks);
               memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 272),272)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_EXTRACT" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(out0:int64) (out1:int64) (out2:int64) (out3:int64) (nblocks:num)
      (st:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      if nblocks = 0
      then f_ev_zero out0 out1 out2 out3 nblocks st pc stackpointer
                     returnaddress
      else APPEND (f_ev_epil out0 out1 out2 out3 nblocks st pc stackpointer
                             returnaddress)
            (APPEND
              (ENUMERATEL nblocks
                (\i. f_ev_loop out0 out1 out2 out3 nblocks st pc stackpointer
                               returnaddress i))
              (f_ev_prol out0 out1 out2 out3 nblocks st pc stackpointer
                         returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SQX4_BOUND_TAC THEN SQX4_PRESERVED_TAC THEN
  ASM_CASES_TAC `nblocks = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `nblocks:num` `pc + 0x29a0` `pc + 0x29e0`
   `\i s. read X19 s = word_add out3 (word(168 * i)) /\
          read X20 s = word_add out2 (word(168 * i)) /\
          read X21 s = word_add out1 (word(168 * i)) /\
          read X22 s = word_add out0 (word(168 * i)) /\
          read X23 s = word(nblocks - i) /\
          read X24 s = st /\
          read SP s = word_add stackpointer (word 208) /\
          read (memory :> bytes64 (word_add stackpointer (word 208))) s =
          x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 216))) s =
          x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 224))) s =
          x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 232))) s =
          x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 240))) s =
          x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 248))) s =
          x24_init /\
          read (memory :> bytes64 (word_add stackpointer (word 256))) s =
          returnaddress` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--1) THEN
    SQX4_NONZERO_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (2--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `168 * i + 168 <= 168 * nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `i < nblocks` THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--2) THEN
    SQX4_SAFE_CALL_TAC "H_PERMUTE"
      [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
       `read X30 s`] 3 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (4--11) THEN
    SQX4_SAFE_CALL_TAC "H_EXTRACT"
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `read X3 s`; `read X4 s`; `0`; `168`; `pc:num`; `read SP s`;
       `read X30 s`] 12 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (13--18) THEN
    SQX4_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      REWRITE_TAC[ARITH_RULE `168 * (i + 1) = 168 * i + 168`];
      ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;
