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
(* the stack. It is verified in the whole image (see libmlkem.ml), using the *)
(* theorems for those functions in the image.                                *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/keccakf1600x4_permute_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/keccakf1600x4_extract_bytes_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_shake128x4_squeezeblocks:
       +0x0: test   r8,r8
       +0x3: je     <mlkem_shake128x4_squeezeblocks+0x90>
       +0x9: push   r15
       +0xb: mov    r15,r9
       +0xe: push   r14
      +0x10: mov    r14,r8
      +0x13: push   r13
      +0x15: mov    r13,rdi
      +0x18: push   r12
      +0x1a: mov    r12,rsi
      +0x1d: push   rbp
      +0x1e: mov    rbp,rdx
      +0x21: push   rbx
      +0x22: mov    rbx,rcx
      +0x25: sub    rsp,0x8
      +0x29: nop    DWORD PTR [rax+0x0]
      +0x30: mov    rdi,r15
      +0x33: call   <mlkem_keccakf1600x4_permute>
      +0x38: sub    rsp,0x8
      +0x3c: mov    rdx,r12
      +0x3f: mov    r8,rbx
      +0x42: push   0xa8
      +0x47: mov    rcx,rbp
      +0x4a: mov    rsi,r13
      +0x4d: xor    r9d,r9d
      +0x50: mov    rdi,r15
      +0x53: add    r13,0xa8
      +0x5a: add    r12,0xa8
      +0x61: add    rbp,0xa8
      +0x68: add    rbx,0xa8
      +0x6f: call   <mlkem_keccakf1600x4_extract_bytes>
      +0x74: pop    rax
      +0x75: pop    rdx
      +0x76: sub    r14,0x1
      +0x7a: jne    <mlkem_shake128x4_squeezeblocks+0x30>
      +0x7c: add    rsp,0x8
      +0x80: pop    rbx
      +0x81: pop    rbp
      +0x82: pop    r12
      +0x84: pop    r13
      +0x86: pop    r14
      +0x88: pop    r15
      +0x8a: ret
      +0x8b: nop    DWORD PTR [rax+rax*1+0x0]
      +0x90: ret
 ***)

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_shake128x4_squeezeblocks"];;

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

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e out0 out1 out2 out3 nblocks st
            (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
            pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       PAIRWISE nonoverlapping
        [out0,168 * nblocks; out1,168 * nblocks; out2,168 * nblocks;
         out3,168 * nblocks; st,800; word_sub stackpointer (word 336),344] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [out0,168 * nblocks; out1,168 * nblocks; out2,168 * nblocks;
         out3,168 * nblocks; st,800; word_sub stackpointer (word 336),344]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + mlkem_shake128x4_squeezeblocks) /\
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
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
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
               memory :> bytes(word_sub stackpointer (word 336),336)])`;;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* The correctness and safety theorems alone, from the combined one.         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!out0 out1 out2 out3 nblocks st
    (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
    pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        PAIRWISE nonoverlapping
         [(out0,168 * nblocks); (out1,168 * nblocks); (out2,168 * nblocks);
          (out3,168 * nblocks); (st,800);
          (word_sub stackpointer (word 336),344)] /\
        ALL (nonoverlapping (word pc,libmlkem_size))
         [(out0,168 * nblocks); (out1,168 * nblocks); (out2,168 * nblocks);
          (out3,168 * nblocks); (st,800);
          (word_sub stackpointer (word 336),344)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem_shake128x4_squeezeblocks) /\
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
                memory :> bytes(word_sub stackpointer (word 336),336)])`;;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e out0 out1 out2 out3 nblocks st pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       PAIRWISE nonoverlapping
        [out0,168 * nblocks; out1,168 * nblocks; out2,168 * nblocks;
         out3,168 * nblocks; st,800; word_sub stackpointer (word 336),344] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [out0,168 * nblocks; out1,168 * nblocks; out2,168 * nblocks;
         out3,168 * nblocks; st,800; word_sub stackpointer (word 336),344]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + mlkem_shake128x4_squeezeblocks) /\
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
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
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
               memory :> bytes(word_sub stackpointer (word 336),336)])`;;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
