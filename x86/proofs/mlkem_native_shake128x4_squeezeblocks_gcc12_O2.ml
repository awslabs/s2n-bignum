(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing whole blocks from four SHAKE128 states. This is the code for    *)
(* mlkem_shake128x4_squeezeblocks from mlkem-native's portable C             *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which for each of nblocks blocks permutes the four states with            *)
(* mlkem_keccakf1600x4_permute and then extracts the first 168 bytes of each *)
(* with mlkem_keccakf1600x4_extract_bytes, passing its seventh argument on   *)
(* the stack. It is verified in the whole image (see                         *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x3780, using  *)
(* the theorems for those functions at 0x4740 and 0x3d70 in the image.       *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_keccakf1600x4_permute_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_keccakf1600x4_extract_bytes_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    3780: test   r8,r8
    3783: je     3810 <mlkem_shake128x4_squeezeblocks+0x90>
    3789: push   r15
    378b: mov    r15,r9
    378e: push   r14
    3790: mov    r14,r8
    3793: push   r13
    3795: mov    r13,rdi
    3798: push   r12
    379a: mov    r12,rsi
    379d: push   rbp
    379e: mov    rbp,rdx
    37a1: push   rbx
    37a2: mov    rbx,rcx
    37a5: sub    rsp,0x8
    37a9: nop    DWORD PTR [rax+0x0]
    37b0: mov    rdi,r15
    37b3: call   4740 <mlkem_keccakf1600x4_permute>
    37b8: sub    rsp,0x8
    37bc: mov    rdx,r12
    37bf: mov    r8,rbx
    37c2: push   0xa8
    37c7: mov    rcx,rbp
    37ca: mov    rsi,r13
    37cd: xor    r9d,r9d
    37d0: mov    rdi,r15
    37d3: add    r13,0xa8
    37da: add    r12,0xa8
    37e1: add    rbp,0xa8
    37e8: add    rbx,0xa8
    37ef: call   3d70 <mlkem_keccakf1600x4_extract_bytes>
    37f4: pop    rax
    37f5: pop    rdx
    37f6: sub    r14,0x1
    37fa: jne    37b0 <mlkem_shake128x4_squeezeblocks+0x30>
    37fc: add    rsp,0x8
    3800: pop    rbx
    3801: pop    rbp
    3802: pop    r12
    3804: pop    r13
    3806: pop    r14
    3808: pop    r15
    380a: ret
    380b: nop    DWORD PTR [rax+rax*1+0x0]
    3810: ret
 ***)

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x3780,0x3811];;

(* ------------------------------------------------------------------------- *)
(* Tactics for the four states, the number of blocks and the loop counter.   *)
(* ------------------------------------------------------------------------- *)

let SQX4_STATES_TAC =
  MAP_EVERY KECCAK_STATE_AT_TAC
   [`st:int64`; `word_add (st:int64) (word 200)`;
    `word_add (st:int64) (word 400)`; `word_add (st:int64) (word 600)`];;

let SQX4_STATES_THEN (ttac:term->term->term->term->tactic) =
  KECCAK_STATE_THEN `st:int64` (fun v0 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 200)` (fun v1 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 400)` (fun v2 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 600)` (fun v3 ->
    ttac v0 v1 v2 v3))));;

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
(* Combined correctness, constant-time and memory safety proof, using those  *)
(* of mlkem_keccakf1600x4_permute and mlkem_keccakf1600x4_extract_bytes. As  *)
(* for mlkem_shake128_squeezeblocks, for each of the four states S, block i  *)
(* of its output, as a number, is the first 168 bytes of keccak_squeeze (i + *)
(* 1) S, and the state becomes keccak_squeeze nblocks S. The events depend   *)
(* only on the addresses and nblocks.                                        *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let SQX4_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref
       [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`;
        `nblocks:num`; `st:int64`; `pc:num`;
        `stackpointer:int64`; `returnaddress:int64`; `i:num`;
        `f_ev_loop:int64->int64->int64->int64->num->int64->num->int64->
                   int64->num->(uarch_event)list`]);
      LABEL_TAC name safety_th]);;

let SQX4_BYTES_STEP_TAC =
  REWRITE_TAC[ARITH_RULE `168 * (i + 1) = 168 * i + 168`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ADD1; NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1];;

let SQX4_PTR_STEP_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `168 * (i + 1) = 168 * i + 168`];;

let SQX4_INV =
 `\i s. read R14 s = word(nblocks - i) /\
        read R13 s = word_add out0 (word(168 * i)) /\
        read R12 s = word_add out1 (word(168 * i)) /\
        read RBP s = word_add out2 (word(168 * i)) /\
        read RBX s = word_add out3 (word(168 * i)) /\
        read R15 s = st /\
        read RSP s = word_add stackpointer (word 280) /\
        read (memory :> bytes64 (word_add stackpointer (word 288))) s =
        rbx_init /\
        read (memory :> bytes64 (word_add stackpointer (word 296))) s =
        rbp_init /\
        read (memory :> bytes64 (word_add stackpointer (word 304))) s =
        r12_init /\
        read (memory :> bytes64 (word_add stackpointer (word 312))) s =
        r13_init /\
        read (memory :> bytes64 (word_add stackpointer (word 320))) s =
        r14_init /\
        read (memory :> bytes64 (word_add stackpointer (word 328))) s =
        r15_init /\
        read (memory :> bytes64 (word_add stackpointer (word 336))) s =
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
        val(keccak_squeeze i (S3:1600 word))`;;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  time prove
 (`exists f_events.
     forall e out0 out1 out2 out3 nblocks st
            (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
            pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       PAIRWISE nonoverlapping
        [out0,168 * nblocks; out1,168 * nblocks; out2,168 * nblocks;
         out3,168 * nblocks; st,800; word_sub stackpointer (word 336),344] /\
       ALL (nonoverlapping (word pc,0x82a0))
        [out0,168 * nblocks; out1,168 * nblocks; out2,168 * nblocks;
         out3,168 * nblocks; st,800; word_sub stackpointer (word 336),344]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + 0x3780) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st] s /\
                 read (memory :> wbytes st) s = S0 /\
                 read (memory :> wbytes (word_add st (word 200))) s = S1 /\
                 read (memory :> wbytes (word_add st (word 400))) s = S2 /\
                 read (memory :> wbytes (word_add st (word 600))) s = S3 /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
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
                 keccak_squeeze nblocks S3 /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events out0 out1 out2 out3 nblocks st pc
                           (word_sub stackpointer (word 336)) returnaddress /\
                    memaccess_inbounds e2
                     [out0,168 * nblocks; out1,168 * nblocks;
                      out2,168 * nblocks; out3,168 * nblocks; st,800;
                      word_sub stackpointer (word 336),344;
                      word(pc + 0x80c0),192]
                     [out0,168 * nblocks; out1,168 * nblocks;
                      out2,168 * nblocks; out3,168 * nblocks; st,800;
                      word_sub stackpointer (word 336),336]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(out0,168 * nblocks);
               memory :> bytes(out1,168 * nblocks);
               memory :> bytes(out2,168 * nblocks);
               memory :> bytes(out3,168 * nblocks);
               memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 336),336)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_EXTRACT" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(out0:int64) (out1:int64) (out2:int64) (out3:int64) (nblocks:num)
      (st:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      if nblocks = 0
      then f_ev_zero out0 out1 out2 out3 nblocks st pc stackpointer
                     returnaddress
      else APPEND
            (f_ev_epil out0 out1 out2 out3 nblocks st pc stackpointer
                       returnaddress)
            (APPEND
              (ENUMERATEL nblocks
                (\i. f_ev_loop out0 out1 out2 out3 nblocks st pc
                               stackpointer returnaddress i))
              (f_ev_prol out0 out1 out2 out3 nblocks st pc stackpointer
                         returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`; `nblocks:num`;
    `st:int64`; `S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
    `S3:1600 word`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 336 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600;
              fst MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `nblocks = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  SQX4_BOUND_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `nblocks:num` `pc + 0x37b0` `pc + 0x37fc`
   SQX4_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Initialization, with the pushes ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--1) THEN
    SQX4_NONZERO_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (2--16) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body: permute, extract a block from each state ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `168 * i + 168 <= 168 * nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `i < nblocks` THEN ARITH_TAC; ALL_TAC] THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--2) THEN
    SQX4_STATES_TAC THEN
    SQX4_STATES_THEN (fun v0 v1 v2 v3 ->
      SQX4_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read RDI s`; v0; v1; v2; v3; `pc:num`;
         `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 3) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (4--16) THEN
    STACK_ARG32_TAC `word_add stackpointer (word 264):int64` THEN
    SQX4_STATES_TAC THEN
    SQX4_STATES_THEN (fun v0 v1 v2 v3 ->
      SQX4_CALL_TAC "H_EXTRACT"
        [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
         `read RCX s`; `read R8 s`; `0`; `168`; v0; v1; v2; v3;
         `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]
        17) THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (18--21) THEN
    SQX4_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY (fun _ -> CONJ_TAC THENL [SQX4_PTR_STEP_TAC; ALL_TAC])
     (1--4) THEN
    MAP_EVERY (fun _ -> CONJ_TAC THENL [SQX4_BYTES_STEP_TAC; ALL_TAC])
     (1--4) THEN
    MAP_EVERY (fun _ -> CONJ_TAC THENL
      [REWRITE_TAC[GSYM ADD1; keccak_squeeze]; ALL_TAC]) (1--4) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The return, with the pops ***)

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The correctness and safety theorems alone, from the combined one.         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!out0 out1 out2 out3 nblocks st
    (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
    pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        PAIRWISE nonoverlapping
         [(out0,168 * nblocks); (out1,168 * nblocks); (out2,168 * nblocks);
          (out3,168 * nblocks); (st,800);
          (word_sub stackpointer (word 336),344)] /\
        ALL (nonoverlapping (word pc,0x82a0))
         [(out0,168 * nblocks); (out1,168 * nblocks); (out2,168 * nblocks);
          (out3,168 * nblocks); (st,800);
          (word_sub stackpointer (word 336),344)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x3780) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st] s /\
                  read (memory :> wbytes st) s = S0 /\
                  read (memory :> wbytes (word_add st (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add st (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add st (word 600))) s = S3)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
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
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out0,168 * nblocks);
                memory :> bytes(out1,168 * nblocks);
                memory :> bytes(out2,168 * nblocks);
                memory :> bytes(out3,168 * nblocks);
                memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 336),336)])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  MP_TAC
   MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL THEN
  DISCH_THEN(CHOOSE_THEN (MP_TAC o SPECL
   [`e:(uarch_event)list`; `out0:int64`; `out1:int64`; `out2:int64`;
    `out3:int64`; `nblocks:num`; `st:int64`; `S0:1600 word`;
    `S1:1600 word`; `S2:1600 word`; `S3:1600 word`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`])) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_RULE) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (`exists f_events.
     forall e out0 out1 out2 out3 nblocks st pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       PAIRWISE nonoverlapping
        [out0,168 * nblocks; out1,168 * nblocks; out2,168 * nblocks;
         out3,168 * nblocks; st,800; word_sub stackpointer (word 336),344] /\
       ALL (nonoverlapping (word pc,0x82a0))
        [out0,168 * nblocks; out1,168 * nblocks; out2,168 * nblocks;
         out3,168 * nblocks; st,800; word_sub stackpointer (word 336),344]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + 0x3780) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events out0 out1 out2 out3 nblocks st pc
                           (word_sub stackpointer (word 336)) returnaddress /\
                    memaccess_inbounds e2
                     [out0,168 * nblocks; out1,168 * nblocks;
                      out2,168 * nblocks; out3,168 * nblocks; st,800;
                      word_sub stackpointer (word 336),344;
                      word(pc + 0x80c0),192]
                     [out0,168 * nblocks; out1,168 * nblocks;
                      out2,168 * nblocks; out3,168 * nblocks; st,800;
                      word_sub stackpointer (word 336),336]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(out0,168 * nblocks);
               memory :> bytes(out1,168 * nblocks);
               memory :> bytes(out2,168 * nblocks);
               memory :> bytes(out3,168 * nblocks);
               memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 336),336)])`,
  MP_TAC
   MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `out0:int64`; `out1:int64`; `out2:int64`;
    `out3:int64`; `nblocks:num`; `st:int64`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`] THEN
  DISCH_TAC THEN
  MAP_EVERY (fun (a,v) ->
    GHOST_INTRO_TAC v (subst [a,`a:int64`]
     `read (memory :> wbytes a):x86state->1600 word`))
   [`st:int64`,`S0:1600 word`;
    `word_add st (word 200):int64`,`S1:1600 word`;
    `word_add st (word 400):int64`,`S2:1600 word`;
    `word_add st (word 600):int64`,`S3:1600 word`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `out0:int64`; `out1:int64`; `out2:int64`;
    `out3:int64`; `nblocks:num`; `st:int64`; `S0:1600 word`;
    `S1:1600 word`; `S2:1600 word`; `S3:1600 word`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_RULE) THEN
  SIMP_TAC[]);;
