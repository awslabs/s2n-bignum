(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing whole blocks from a SHAKE128 state. This is the code for        *)
(* mlkem_shake128_squeezeblocks from mlkem-native's portable C               *)
(* implementation compiled by gcc 12 with -O3 (see mlkem_native/README.md),  *)
(* which for each of nblocks blocks permutes the state and then extracts the *)
(* first 168 bytes of it, the rate of SHAKE128. It is verified in the whole  *)
(* image (see libmlkem.ml), using the theorems for                           *)
(* mlkem_keccakf1600_permute and mlkem_keccakf1600_extract_bytes in the      *)
(* image.                                                                    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/keccakf1600_permute_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/keccakf1600_extract_bytes_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_shake128_squeezeblocks:
       +0x0: cbz     x1, <mlkem_shake128_squeezeblocks+0x4c>
       +0x4: stp     x19, x20, [sp, #-32]!
       +0x8: mov     x20, x0
       +0xc: mov     x19, x1
      +0x10: stp     x21, x30, [sp, #16]
      +0x14: mov     x21, x2
      +0x18: mov     x0, x21
      +0x1c: bl      <mlkem_keccakf1600_permute>
      +0x20: mov     x1, x20
      +0x24: mov     x0, x21
      +0x28: mov     w3, #0xa8
      +0x2c: mov     w2, #0x0
      +0x30: bl      <mlkem_keccakf1600_extract_bytes>
      +0x34: add     x20, x20, #0xa8
      +0x38: subs    x19, x19, #0x1
      +0x3c: b.ne    <mlkem_shake128_squeezeblocks+0x18>
      +0x40: ldp     x21, x30, [sp, #16]
      +0x44: ldp     x19, x20, [sp], #32
      +0x48: ret
      +0x4c: ret
 ***)

let MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_shake128_squeezeblocks"];;

(* ------------------------------------------------------------------------- *)
(* Tactics for the calls, and for the number of blocks as a 64-bit word.     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_PERMUTE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_F1600);;

let LOCAL_EXTRACT_BYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

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

let MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!out nblocks st (S:1600 word) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(out,168 * nblocks); (st,200);
          (word_sub stackpointer (word 224),224)] /\
        ALL (nonoverlapping (word pc,libmlkem_size))
         [(out,168 * nblocks); (st,200);
          (word_sub stackpointer (word 224),224)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_shake128_squeezeblocks) /\
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
                memory :> bytes(word_sub stackpointer (word 224),224)])`;;

let MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let SQUEEZEBLOCKS_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O3_mc,
       MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref
       [`out:int64`; `nblocks:num`; `st:int64`; `pc:num`;
        `stackpointer:int64`; `returnaddress:int64`;
        (* inside the loop... *)
        `i:num`;
        `f_ev_loop:int64->num->int64->num->int64->int64->num->
                   (uarch_event)list`]);
      LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e out nblocks st pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [out,168 * nblocks; st,200; word_sub stackpointer (word 224),224] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [out,168 * nblocks; st,200; word_sub stackpointer (word 224),224]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O3_mc /\
                 read PC s = word (pc + mlkem_shake128_squeezeblocks) /\
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
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out,168 * nblocks; st,200;
                      word_sub stackpointer (word 224),224]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,168 * nblocks); memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 224),224)])`;;

let MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using those  *)
(* of mlkem_keccakf1600_permute and mlkem_keccakf1600_extract_bytes.         *)
(* ------------------------------------------------------------------------- *)

let SQUEEZE_CS_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O3_mc,
       MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
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

let MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O3_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e out nblocks st (S:1600 word) pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [out,168 * nblocks; st,200; word_sub stackpointer (word 224),224] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [out,168 * nblocks; st,200; word_sub stackpointer (word 224),224]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O3_mc /\
                 read PC s = word (pc + mlkem_shake128_squeezeblocks) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; word nblocks; st] s /\
                 read (memory :> wbytes st) s = S /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> bytes(out,168 * nblocks)) s =
                 nsum {i | i < nblocks}
                  (\i. 2 EXP (8 * 168 * i) *
                       val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 168)) /\
                 read (memory :> wbytes st) s = keccak_squeeze nblocks S /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events out nblocks st pc
                           (word_sub stackpointer (word 224)) returnaddress /\
                    memaccess_inbounds e2
                     [out,168 * nblocks; st,200;
                      word_sub stackpointer (word 224),224;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out,168 * nblocks; st,200;
                      word_sub stackpointer (word 224),224]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,168 * nblocks); memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 224),224)])`;;

let MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O3_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_SHAKE128_SQUEEZEBLOCKS_GCC12_O3_IMAGE_SUBROUTINE_FULL_STMT;;
