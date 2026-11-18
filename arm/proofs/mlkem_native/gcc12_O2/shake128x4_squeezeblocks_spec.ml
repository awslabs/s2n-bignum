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
(* with mlkem_keccakf1600x4_extract_bytes. It is verified in the whole image *)
(* (see libmlkem.ml), using the theorems for those                           *)
(* functions.                                                                *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/keccakf1600x4_permute_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/keccakf1600x4_extract_bytes_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_shake128x4_squeezeblocks:
       +0x0: cbz     x4, <mlkem_shake128x4_squeezeblocks+0x80>
       +0x4: stp     x19, x20, [sp, #-64]!
       +0x8: mov     x20, x2
       +0xc: mov     x19, x3
      +0x10: stp     x21, x22, [sp, #16]
      +0x14: mov     x22, x0
      +0x18: mov     x21, x1
      +0x1c: stp     x23, x24, [sp, #32]
      +0x20: mov     x23, x4
      +0x24: mov     x24, x5
      +0x28: str     x30, [sp, #48]
      +0x2c: mov     x0, x24
      +0x30: bl      <mlkem_keccakf1600x4_permute>
      +0x34: mov     x4, x19
      +0x38: mov     x3, x20
      +0x3c: mov     x2, x21
      +0x40: mov     x1, x22
      +0x44: mov     x0, x24
      +0x48: mov     w6, #0xa8
      +0x4c: mov     w5, #0x0
      +0x50: bl      <mlkem_keccakf1600x4_extract_bytes>
      +0x54: add     x19, x19, #0xa8
      +0x58: add     x20, x20, #0xa8
      +0x5c: add     x21, x21, #0xa8
      +0x60: add     x22, x22, #0xa8
      +0x64: subs    x23, x23, #0x1
      +0x68: b.ne    <mlkem_shake128x4_squeezeblocks+0x2c>
      +0x6c: ldp     x21, x22, [sp, #16]
      +0x70: ldp     x23, x24, [sp, #32]
      +0x74: ldr     x30, [sp, #48]
      +0x78: ldp     x19, x20, [sp], #64
      +0x7c: ret
      +0x80: ret
 ***)

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem_shake128x4_squeezeblocks"];;

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

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!out0 out1 out2 out3 nblocks st
    (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
    pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(out0,168 * nblocks); (out1,168 * nblocks); (out2,168 * nblocks);
          (out3,168 * nblocks); (st,800);
          (word_sub stackpointer (word 272),272)] /\
        ALL (nonoverlapping (word pc,libmlkem_size))
         [(out0,168 * nblocks); (out1,168 * nblocks); (out2,168 * nblocks);
          (out3,168 * nblocks); (st,800);
          (word_sub stackpointer (word 272),272)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + mlkem_shake128x4_squeezeblocks) /\
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
                memory :> bytes(word_sub stackpointer (word 272),272)])`;;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

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

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e out0 out1 out2 out3 nblocks st pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [out0,168 * nblocks; out1,168 * nblocks; out2,168 * nblocks;
         out3,168 * nblocks; st,800; word_sub stackpointer (word 272),272] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [out0,168 * nblocks; out1,168 * nblocks; out2,168 * nblocks;
         out3,168 * nblocks; st,800; word_sub stackpointer (word 272),272]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + mlkem_shake128x4_squeezeblocks) /\
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
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
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
               memory :> bytes(word_sub stackpointer (word 272),272)])`;;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using those  *)
(* of mlkem_keccakf1600x4_permute and mlkem_keccakf1600x4_extract_bytes.     *)
(* ------------------------------------------------------------------------- *)

let SQX4_CS_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref
       [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`;
        `nblocks:num`; `st:int64`; `pc:num`; `stackpointer:int64`;
        `returnaddress:int64`; `i:num`;
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

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e out0 out1 out2 out3 nblocks st
            (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
            pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [out0,168 * nblocks; out1,168 * nblocks; out2,168 * nblocks;
         out3,168 * nblocks; st,800; word_sub stackpointer (word 272),272] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [out0,168 * nblocks; out1,168 * nblocks; out2,168 * nblocks;
         out3,168 * nblocks; st,800; word_sub stackpointer (word 272),272]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + mlkem_shake128x4_squeezeblocks) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st] s /\
                 read (memory :> wbytes st) s = S0 /\
                 read (memory :> wbytes (word_add st (word 200))) s = S1 /\
                 read (memory :> wbytes (word_add st (word 400))) s = S2 /\
                 read (memory :> wbytes (word_add st (word 600))) s = S3 /\
                 read events s = e)
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
                 keccak_squeeze nblocks S3 /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events out0 out1 out2 out3 nblocks st pc
                           (word_sub stackpointer (word 272)) returnaddress /\
                    memaccess_inbounds e2
                     [out0,168 * nblocks; out1,168 * nblocks;
                      out2,168 * nblocks; out3,168 * nblocks; st,800;
                      word_sub stackpointer (word 272),272;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
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
               memory :> bytes(word_sub stackpointer (word 272),272)])`;;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;
