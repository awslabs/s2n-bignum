(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing whole blocks from a SHAKE128 state. This is the code for        *)
(* mlkem_shake128_squeezeblocks from mlkem-native's portable C               *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which for each of nblocks blocks permutes the state and extracts its      *)
(* first 168 bytes. It is verified in the whole image (see                   *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x33e0, using  *)
(* the theorems for mlkem_keccakf1600_permute at 0x3e70 and                  *)
(* mlkem_keccakf1600_extract_bytes at 0x3d10 in the image.                   *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_keccakf1600_permute_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_keccakf1600_extract_bytes_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    33e0: test   rsi,rsi
    33e3: je     3428 <mlkem_shake128_squeezeblocks+0x48>
    33e5: push   r12
    33e7: mov    r12,rdx
    33ea: push   rbp
    33eb: mov    rbp,rdi
    33ee: push   rbx
    33ef: mov    rbx,rsi
    33f2: nop    WORD PTR [rax+rax*1+0x0]
    33f8: mov    rdi,r12
    33fb: call   3e70 <mlkem_keccakf1600_permute>
    3400: mov    rsi,rbp
    3403: mov    ecx,0xa8
    3408: xor    edx,edx
    340a: mov    rdi,r12
    340d: add    rbp,0xa8
    3414: call   3d10 <mlkem_keccakf1600_extract_bytes>
    3419: sub    rbx,0x1
    341d: jne    33f8 <mlkem_shake128_squeezeblocks+0x18>
    341f: pop    rbx
    3420: pop    rbp
    3421: pop    r12
    3423: ret
    3424: nop    DWORD PTR [rax+0x0]
    3428: ret
 ***)

let MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x33e0,0x3429];;

(* ------------------------------------------------------------------------- *)
(* Tactics for the number of blocks as a 64-bit word.                        *)
(* ------------------------------------------------------------------------- *)

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
(* Combined correctness, constant-time and memory safety proof, using those  *)
(* of mlkem_keccakf1600_permute and mlkem_keccakf1600_extract_bytes. The     *)
(* state is a 1600-bit word S, as in common/fips202.ml and for               *)
(* mlk_keccak_absorb_once. Block i of the output, as a number, is the first  *)
(* 168 bytes of keccak_squeeze (i + 1) S, the state after i + 1              *)
(* permutations, and the final state is keccak_squeeze nblocks S. When S is  *)
(* the result of mlkem_shake128_absorb_once, these are the bytes of the      *)
(* output of shake128 in common/fips202.ml.                                  *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let SQUEEZE_CS_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref
       [`out:int64`; `nblocks:num`; `st:int64`; `pc:num`;
        `stackpointer:int64`; `returnaddress:int64`; `i:num`;
        `f_ev_loop:int64->num->int64->num->int64->int64->num->
                   (uarch_event)list`]);
      LABEL_TAC name safety_th]);;

let SQUEEZE_BYTES_STEP_TAC =
  REWRITE_TAC[ARITH_RULE `168 * (i + 1) = 168 * i + 168`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ADD1; NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1];;

let SQUEEZE_PTR_STEP_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `168 * (i + 1) = 168 * i + 168`];;

let MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (`exists f_events.
     forall e out nblocks st (S:1600 word) pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       PAIRWISE nonoverlapping
        [out,168 * nblocks; st,200; word_sub stackpointer (word 288),296] /\
       ALL (nonoverlapping (word pc,0x82a0))
        [out,168 * nblocks; st,200; word_sub stackpointer (word 288),296]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + 0x33e0) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [out; word nblocks; st] s /\
                 read (memory :> wbytes st) s = S /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 read (memory :> bytes(out,168 * nblocks)) s =
                 nsum {i | i < nblocks}
                  (\i. 2 EXP (8 * 168 * i) *
                       val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 168)) /\
                 read (memory :> wbytes st) s = keccak_squeeze nblocks S /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events out nblocks st pc
                           (word_sub stackpointer (word 288)) returnaddress /\
                    memaccess_inbounds e2
                     [out,168 * nblocks; st,200;
                      word_sub stackpointer (word 288),296;
                      word(pc + 0x80c0),192]
                     [out,168 * nblocks; st,200;
                      word_sub stackpointer (word 288),288]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(out,168 * nblocks); memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 288),288)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL
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
  MAP_EVERY X_GEN_TAC
   [`out:int64`; `nblocks:num`; `st:int64`; `S:1600 word`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 288 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600;
              fst MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `nblocks = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  SQUEEZEBLOCKS_BOUND_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `nblocks:num` `pc + 0x33f8` `pc + 0x341f`
   `\i s. read RBX s = word(nblocks - i) /\
          read RBP s = word_add out (word(168 * i)) /\
          read R12 s = st /\
          read RSP s = word_add stackpointer (word 264) /\
          read (memory :> bytes64 (word_add stackpointer (word 264))) s =
          rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 272))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 280))) s =
          r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 288))) s =
          returnaddress /\
          read (memory :> bytes(out,168 * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * 168 * j) *
                val(keccak_squeeze (j + 1) S) MOD 2 EXP (8 * 168)) /\
          read (memory :> bytes(st,200)) s =
          val(keccak_squeeze i (S:1600 word))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Initialization, with the pushes ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC (1--1) THEN
    SQUEEZEBLOCKS_NONZERO_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC (2--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body: permute, extract a block, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `168 * i + 168 <= 168 * nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `i < nblocks` THEN ARITH_TAC; ALL_TAC] THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC (1--2) THEN
    KECCAK_STATE_WBYTES_TAC `keccak_squeeze i (S:1600 word)` THEN
    SQUEEZE_CS_CALL_TAC "H_PERMUTE"
      [`e:(uarch_event)list`; `read RDI s`;
       `keccak_squeeze i (S:1600 word)`; `pc:num`; `read RSP s`;
       `read (memory :> bytes64(read RSP s)) s`] 3 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC (4--9) THEN
    KECCAK_STATE_WBYTES_TAC `keccak_f1600(keccak_squeeze i (S:1600 word))` THEN
    SQUEEZE_CS_CALL_TAC "H_EXTRACT"
      [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `0`; `168`;
       `keccak_f1600(keccak_squeeze i (S:1600 word))`; `pc:num`;
       `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 10 THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (11--12) THEN
    SQUEEZEBLOCKS_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [SQUEEZE_PTR_STEP_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [SQUEEZE_BYTES_STEP_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[GSYM ADD1; keccak_squeeze]; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The return, with the pops ***)

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The correctness and safety theorems alone, from the combined one.         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!out nblocks st (S:1600 word) pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        PAIRWISE nonoverlapping
         [(out,168 * nblocks); (st,200);
          (word_sub stackpointer (word 288),296)] /\
        ALL (nonoverlapping (word pc,0x82a0))
         [(out,168 * nblocks); (st,200);
          (word_sub stackpointer (word 288),296)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x33e0) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; word nblocks; st] s /\
                  read (memory :> wbytes st) s = S)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(out,168 * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * 168 * i) *
                        val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 168)) /\
                  read (memory :> wbytes st) s = keccak_squeeze nblocks S)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out,168 * nblocks); memory :> bytes(st,200);
                memory :> bytes(word_sub stackpointer (word 288),288)])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  MP_TAC
   MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL THEN
  DISCH_THEN(CHOOSE_THEN (MP_TAC o SPECL
   [`e:(uarch_event)list`; `out:int64`; `nblocks:num`; `st:int64`;
    `S:1600 word`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`])) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_RULE) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (`exists f_events.
     forall e out nblocks st pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       PAIRWISE nonoverlapping
        [out,168 * nblocks; st,200; word_sub stackpointer (word 288),296] /\
       ALL (nonoverlapping (word pc,0x82a0))
        [out,168 * nblocks; st,200; word_sub stackpointer (word 288),296]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + 0x33e0) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [out; word nblocks; st] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events out nblocks st pc
                           (word_sub stackpointer (word 288)) returnaddress /\
                    memaccess_inbounds e2
                     [out,168 * nblocks; st,200;
                      word_sub stackpointer (word 288),296;
                      word(pc + 0x80c0),192]
                     [out,168 * nblocks; st,200;
                      word_sub stackpointer (word 288),288]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(out,168 * nblocks); memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 288),288)])`,
  MP_TAC
   MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `out:int64`; `nblocks:num`; `st:int64`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`] THEN
  DISCH_TAC THEN
  GHOST_INTRO_TAC `S:1600 word`
   `read (memory :> wbytes st):x86state->1600 word` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `out:int64`; `nblocks:num`; `st:int64`;
    `S:1600 word`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_RULE) THEN
  SIMP_TAC[]);;
