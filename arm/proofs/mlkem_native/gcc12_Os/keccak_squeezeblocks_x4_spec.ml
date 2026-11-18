(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing whole blocks from four Keccak states. This is the code for the  *)
(* static function mlk_keccak_squeezeblocks_x4 from mlkem-native's portable  *)
(* C implementation compiled by gcc 12 with -Os (see mlkem_native/README.md),*)
(* which is used by its fourfold SHAKE128 and SHAKE256 functions. For each   *)
(* of nblocks blocks it permutes the four states and then extracts the first *)
(* r bytes of each. It is verified in the whole image (see libmlkem.ml),     *)
(* using the theorems for mlkem_keccakf1600x4_permute and                    *)
(* mlkem_keccakf1600x4_extract_bytes in the image.                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/keccakf1600x4_permute_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/keccakf1600x4_extract_bytes_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The code in the image:

    mlk_keccak_squeezeblocks_x4:
       +0x0: stp     x19, x20, [sp, #-80]!
       +0x4: mov     x20, x4
       +0x8: mov     x19, #0x0
       +0xc: stp     x27, x30, [sp, #64]
      +0x10: mov     w27, w6
      +0x14: stp     x21, x22, [sp, #16]
      +0x18: mov     x21, x5
      +0x1c: mov     x22, x27
      +0x20: stp     x23, x24, [sp, #32]
      +0x24: mov     x23, x0
      +0x28: mov     x24, x1
      +0x2c: stp     x25, x26, [sp, #48]
      +0x30: mov     x25, x2
      +0x34: mov     x26, x3
      +0x38: cbnz    x20, <mlk_keccak_squeezeblocks_x4+0x54>
      +0x3c: ldp     x21, x22, [sp, #16]
      +0x40: ldp     x23, x24, [sp, #32]
      +0x44: ldp     x25, x26, [sp, #48]
      +0x48: ldp     x27, x30, [sp, #64]
      +0x4c: ldp     x19, x20, [sp], #80
      +0x50: ret
      +0x54: mov     x0, x21
      +0x58: bl      <mlkem_keccakf1600x4_permute>
      +0x5c: add     x4, x26, x19
      +0x60: add     x3, x25, x19
      +0x64: add     x2, x24, x19
      +0x68: add     x1, x23, x19
      +0x6c: mov     w6, w22
      +0x70: mov     x0, x21
      +0x74: mov     w5, #0x0
      +0x78: add     x19, x19, x27
      +0x7c: sub     x20, x20, #0x1
      +0x80: bl      <mlkem_keccakf1600x4_extract_bytes>
      +0x84: b       <mlk_keccak_squeezeblocks_x4+0x38>
 ***)

let MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlk_keccak_squeezeblocks_x4"];;

(* ------------------------------------------------------------------------- *)
(* Tactics for the four states, the number of blocks, the rate and the loop  *)
(* counter.                                                                  *)
(* ------------------------------------------------------------------------- *)

let KSQX4_STATES_TAC =
  MAP_EVERY KECCAK_STATE_AT_TAC
   [`st:int64`; `word_add (st:int64) (word 200)`;
    `word_add (st:int64) (word 400)`; `word_add (st:int64) (word 600)`];;

(*** The bounds on nblocks and r from the nonoverlapping, and their words ***)

let KSQX4_BOUND_TAC =
  SUBGOAL_THEN `800 + r * nblocks <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(out0:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `nblocks <= r * nblocks` ASSUME_TAC THENL
   [MP_TAC(SPECL [`1`; `r:num`; `nblocks:num`] LE_MULT_RCANCEL) THEN
    REWRITE_TAC[MULT_CLAUSES] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word nblocks:int64) = nblocks /\ val(word r:int64) = r`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

(*** The test of nblocks = 0 at the start, when it is known to be false ***)

let KSQX4_NONZERO_TAC =
  let t1 = `val(word nblocks:int64) = nblocks` and t2 = `~(nblocks = 0)` in
  RULE_ASSUM_TAC(fun th ->
    if concl th = t1 || concl th = t2 then th
    else REWRITE_RULE[ASSUME t1; ASSUME t2] th);;

let KSQX4_PRESERVED_TAC =
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
  ENSURES_PRESERVED_TAC "x27_init" `X27`;;

(*** The loop counter nblocks - i after the subtraction, and its test ***)

let KSQX4_COUNTER_TAC =
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

let KSQX4_CS_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_Os_mc,
       MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_Os_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref
       [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`;
        `nblocks:num`; `st:int64`; `r:num`; `pc:num`; `stackpointer:int64`;
        `returnaddress:int64`; `i:num`;
        `f_ev_loop:int64->int64->int64->int64->num->int64->num->num->int64->
                   int64->num->(uarch_event)list`]);
      LABEL_TAC name safety_th]);;

let KSQX4_BYTES_STEP_TAC =
  REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ADD1; NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1];;

let KSQX4_PTR_STEP_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The states are 1600-bit words, as in                   *)
(* common/fips202/fips202.ml. Block i of the output for a state, as a        *)
(* number, is the first r bytes of keccak_squeeze (i + 1) S, the state after *)
(* i + 1 permutations, and the final state is keccak_squeeze nblocks S.      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!out0 out1 out2 out3 nblocks st r
    (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
    pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\
        PAIRWISE nonoverlapping
         [(out0,r * nblocks); (out1,r * nblocks); (out2,r * nblocks);
          (out3,r * nblocks); (st,800);
          (word_sub stackpointer (word 320),320)] /\
        ALL (nonoverlapping (word pc,libmlkem_size))
         [(out0,r * nblocks); (out1,r * nblocks); (out2,r * nblocks);
          (out3,r * nblocks); (st,800);
          (word_sub stackpointer (word 320),320)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlk_keccak_squeezeblocks_x4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st;
                               word r] s /\
                  read (memory :> wbytes st) s = S0 /\
                  read (memory :> wbytes (word_add st (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add st (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add st (word 600))) s = S3)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out0,r * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * r * i) *
                        val(keccak_squeeze (i + 1) S0) MOD 2 EXP (8 * r)) /\
                  read (memory :> bytes(out1,r * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * r * i) *
                        val(keccak_squeeze (i + 1) S1) MOD 2 EXP (8 * r)) /\
                  read (memory :> bytes(out2,r * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * r * i) *
                        val(keccak_squeeze (i + 1) S2) MOD 2 EXP (8 * r)) /\
                  read (memory :> bytes(out3,r * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * r * i) *
                        val(keccak_squeeze (i + 1) S3) MOD 2 EXP (8 * r)) /\
                  read (memory :> wbytes st) s = keccak_squeeze nblocks S0 /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  keccak_squeeze nblocks S1 /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  keccak_squeeze nblocks S2 /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  keccak_squeeze nblocks S3)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out0,r * nblocks);
                memory :> bytes(out1,r * nblocks);
                memory :> bytes(out2,r * nblocks);
                memory :> bytes(out3,r * nblocks);
                memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)


let MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e out0 out1 out2 out3 nblocks st r pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\
       PAIRWISE nonoverlapping
        [out0,r * nblocks; out1,r * nblocks; out2,r * nblocks;
         out3,r * nblocks; st,800; word_sub stackpointer (word 320),320] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [out0,r * nblocks; out1,r * nblocks; out2,r * nblocks;
         out3,r * nblocks; st,800; word_sub stackpointer (word 320),320]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlk_keccak_squeezeblocks_x4) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st;
                              word r] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events out0 out1 out2 out3 nblocks st r pc
                           (word_sub stackpointer (word 320)) returnaddress /\
                    memaccess_inbounds e2
                     [out0,r * nblocks; out1,r * nblocks;
                      out2,r * nblocks; out3,r * nblocks; st,800;
                      word_sub stackpointer (word 320),320;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out0,r * nblocks; out1,r * nblocks;
                      out2,r * nblocks; out3,r * nblocks; st,800;
                      word_sub stackpointer (word 320),320]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out0,r * nblocks);
               memory :> bytes(out1,r * nblocks);
               memory :> bytes(out2,r * nblocks);
               memory :> bytes(out3,r * nblocks);
               memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using those  *)
(* of mlkem_keccakf1600x4_permute and mlkem_keccakf1600x4_extract_bytes.     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e out0 out1 out2 out3 nblocks st r
            (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
            pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\
       PAIRWISE nonoverlapping
        [out0,r * nblocks; out1,r * nblocks; out2,r * nblocks;
         out3,r * nblocks; st,800; word_sub stackpointer (word 320),320] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [out0,r * nblocks; out1,r * nblocks; out2,r * nblocks;
         out3,r * nblocks; st,800; word_sub stackpointer (word 320),320]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlk_keccak_squeezeblocks_x4) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st;
                              word r] s /\
                  read (memory :> wbytes st) s = S0 /\
                  read (memory :> wbytes (word_add st (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add st (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add st (word 600))) s = S3 /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out0,r * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * r * i) *
                        val(keccak_squeeze (i + 1) S0) MOD 2 EXP (8 * r)) /\
                  read (memory :> bytes(out1,r * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * r * i) *
                        val(keccak_squeeze (i + 1) S1) MOD 2 EXP (8 * r)) /\
                  read (memory :> bytes(out2,r * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * r * i) *
                        val(keccak_squeeze (i + 1) S2) MOD 2 EXP (8 * r)) /\
                  read (memory :> bytes(out3,r * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * r * i) *
                        val(keccak_squeeze (i + 1) S3) MOD 2 EXP (8 * r)) /\
                  read (memory :> wbytes st) s = keccak_squeeze nblocks S0 /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  keccak_squeeze nblocks S1 /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  keccak_squeeze nblocks S2 /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  keccak_squeeze nblocks S3 /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events out0 out1 out2 out3 nblocks st r pc
                           (word_sub stackpointer (word 320)) returnaddress /\
                    memaccess_inbounds e2
                     [out0,r * nblocks; out1,r * nblocks;
                      out2,r * nblocks; out3,r * nblocks; st,800;
                      word_sub stackpointer (word 320),320;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out0,r * nblocks; out1,r * nblocks;
                      out2,r * nblocks; out3,r * nblocks; st,800;
                      word_sub stackpointer (word 320),320]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out0,r * nblocks);
               memory :> bytes(out1,r * nblocks);
               memory :> bytes(out2,r * nblocks);
               memory :> bytes(out3,r * nblocks);
               memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;
