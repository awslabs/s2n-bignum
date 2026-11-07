(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 with an output of any length. This is the code for               *)
(* mlkem_shake256 from mlkem-native's portable C implementation compiled by  *)
(* clang 17 with -O3 (see mlkem_native/README.md), which absorbs the input   *)
(* into a state on the stack with mlk_keccak_absorb_once, and then for each  *)
(* block of the output permutes the state and extracts up to 136 bytes of    *)
(* it, the rate of SHAKE256, before zeroing the state. It is verified in the *)
(* whole image (see libmlkem.ml), using the theorems for                     *)
(* mlk_keccak_absorb_once, mlkem_keccakf1600_permute and                     *)
(* mlkem_keccakf1600_extract_bytes in the image. The result is shake256 of   *)
(* common/fips202.ml.                                                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/keccak_absorb_once_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/keccakf1600_extract_bytes_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_shake256:
      +0x0: stp     x29, x30, [sp, #-64]!
      +0x4: str     x28, [sp, #16]
      +0x8: stp     x22, x21, [sp, #32]
      +0xc: stp     x20, x19, [sp, #48]
     +0x10: mov     x29, sp
     +0x14: sub     x9, sp, #0x100
     +0x18: and     sp, x9, #0xffffffffffffffe0
     +0x1c: adrp    x8, <page>
     +0x20: mov     x19, x1
     +0x24: mov     x20, x0
     +0x28: mov     x0, sp
     +0x2c: mov     w1, #0x88
     +0x30: mov     w4, #0x1f
     +0x34: ldr     x8, [x8, #4088]  // got_stack_chk_guard
     +0x38: ldr     x8, [x8]
     +0x3c: str     x8, [sp, #248]
     +0x40: bl      mlk_keccak_absorb_once
     +0x44: cbz     x19, join1
     +0x48: mov     w22, #0x88
     loop1:
     +0x4c: mov     x0, sp
     +0x50: bl      mlkem_keccakf1600_permute
     +0x54: cmp     x19, #0x88
     +0x58: mov     x0, sp
     +0x5c: csel    x21, x19, x22, cc
     +0x60: mov     x1, x20
     +0x64: mov     w2, wzr
     +0x68: mov     w3, w21
     +0x6c: bl      mlkem_keccakf1600_extract_bytes
     +0x70: add     x20, x20, x21
     +0x74: subs    x19, x19, x21
     +0x78: b.ne    loop1
     join1:
     +0x7c: movi    v0.2d, #0x0
     +0x80: mov     x8, sp
     +0x84: stp     q0, q0, [sp]
     +0x88: stp     q0, q0, [sp, #32]
     +0x8c: stp     q0, q0, [sp, #64]
     +0x90: stp     q0, q0, [sp, #96]
     +0x94: stp     q0, q0, [sp, #128]
     +0x98: stp     q0, q0, [sp, #160]
     +0x9c: stp     q0, q0, [sp, #192]
     +0xa0: adrp    x8, <page>
     +0xa4: ldr     x8, [x8, #4088]  // got_stack_chk_guard
     +0xa8: ldr     x9, [sp, #248]
     +0xac: ldr     x8, [x8]
     +0xb0: cmp     x8, x9
     +0xb4: b.ne    +0xd0
     +0xb8: mov     sp, x29
     +0xbc: ldp     x20, x19, [sp, #48]
     +0xc0: ldp     x22, x21, [sp, #32]
     +0xc4: ldr     x28, [sp, #16]
     +0xc8: ldp     x29, x30, [sp], #64
     +0xcc: ret
     +0xd0: bl      __stack_chk_fail
 ***)

let MLKEM_NATIVE_SHAKE256_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_shake256"];;

(* ------------------------------------------------------------------------- *)
(* The state is aligned to 32 bytes within the stack frame, so its address   *)
(* depends on whether the stack pointer is a multiple of 32 or just of 16.   *)
(* ------------------------------------------------------------------------- *)

let ALIGNED_16_32_WORD_AND_STMT =
  `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`;;

let ALIGNED_16_32_WORD_AND = assume_spec ALIGNED_16_32_WORD_AND_STMT;;


let SHAKE256_STATE_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 304)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 288 else 304))`;;

let SHAKE256_STATE_ADDRESS = assume_spec SHAKE256_STATE_ADDRESS_STMT;;

let SHAKE256_STATE_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 304))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 288 else 304))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC SHAKE256_STATE_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let SHAKE256_ST = `word_add (stackpointer:int64)
                    (word(if aligned 32 stackpointer then 288 else 304))`;;

(*** The setup for both proofs, with the bounds on the offset of the state ***)

let SHAKE256_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 624):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `288 <= (if aligned 32 (stackpointer:int64) then 288 else 304) /\
    (if aligned 32 (stackpointer:int64) then 288 else 304) <= 304`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `aligned 16 (word_add (stackpointer:int64)
                         (word(if aligned 32 stackpointer then 288 else 304)))`
  ASSUME_TAC THENL
   [COND_CASES_TAC THEN CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_sub (word (if aligned 32 (stackpointer:int64) then 288 else 304))
             (word 288):int64 =
    word((if aligned 32 stackpointer then 288 else 304) - 288)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WORD_SUB2 THEN COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(if aligned 32 (stackpointer:int64) then 288 else 304) - 288 <= 16`
  ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_sub (word (if aligned 32 (stackpointer:int64) then 288 else 304))
             (word 208):int64 =
    word((if aligned 32 stackpointer then 288 else 304) - 208)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WORD_SUB2 THEN COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(if aligned 32 (stackpointer:int64) then 288 else 304) - 208 <= 96`
  ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x28_init" `X28` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29`;;

(*** The region below the state for the callee, in the form word(x - 288) ***)

let SHAKE256_FIX_TAC =
  RULE_ASSUM_TAC(fun th ->
    if maychange_term (concl th)
    then REWRITE_RULE[ASSUME
     `word_sub (word (if aligned 32 (stackpointer:int64) then 288 else 304))
               (word 288):int64 =
      word((if aligned 32 stackpointer then 288 else 304) - 288)`;
     ASSUME
     `word_sub (word (if aligned 32 (stackpointer:int64) then 288 else 304))
               (word 208):int64 =
      word((if aligned 32 stackpointer then 288 else 304) - 208)`] th
    else th);;

(*** The bound on outlen from the nonoverlapping, and its 64-bit word ***)

let SHAKE256_BOUND_TAC =
  SUBGOAL_THEN `624 + outlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(stackpointer:int64)`; `val(out:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word outlen:int64) = outlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

(*** The test of outlen = 0 at the start, when it is known to be false ***)

let SHAKE256_NONZERO_TAC =
  let t1 = `val(word outlen:int64) = outlen` and t2 = `~(outlen = 0)` in
  RULE_ASSUM_TAC(fun th ->
    if concl th = t1 || concl th = t2 then th
    else REWRITE_RULE[ASSUME t1; ASSUME t2] th);;


(*** The number of bytes extracted in each iteration, MIN x 136 ***)

let SHAKE256_CSEL_LEMMA_STMT =
  `!x. x < 2 EXP 64
       ==> (if val (word x:int64) < 136 then word x else word 136):int64 =
           word(MIN x 136)`;;

let SHAKE256_CSEL_LEMMA = assume_spec SHAKE256_CSEL_LEMMA_STMT;;

(*** Iteration i of the loop, with 136 * i bytes done ***)

let SHAKE256_ITERATION_TAC tac =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN tac THEN
  SUBGOAL_THEN `136 * i < outlen` ASSUME_TAC THENL
   [UNDISCH_TAC `i < (outlen + 135) DIV 136` THEN
    REWRITE_TAC[ARITH_RULE `i < q <=> i + 1 <= q`] THEN
    SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `MIN outlen (136 * i) = 136 * i` SUBST1_TAC THENL
   [UNDISCH_TAC `136 * i < outlen` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `0 < MIN (outlen - 136 * i) 136 /\ MIN (outlen - 136 * i) 136 <= 136 /\
    0 + MIN (outlen - 136 * i) 136 <= 200 /\
    136 * i + MIN (outlen - 136 * i) 136 <= outlen /\
    MIN outlen (136 * (i + 1)) = 136 * i + MIN (outlen - 136 * i) 136 /\
    (outlen - 136 * i - MIN (outlen - 136 * i) 136 = 0 <=>
     ~(i + 1 < (outlen + 135) DIV 136))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `i + 1 < q <=> i + 2 <= q`] THEN
    SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN
    UNDISCH_TAC `136 * i < outlen` THEN ARITH_TAC;
    ALL_TAC];;

(*** The block length after the csel, and the counter after the subs ***)

let SHAKE256_LENGTH_TAC =
  MP_TAC(SPEC `outlen - 136 * i` SHAKE256_CSEL_LEMMA) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  ARGS_32_TAC [`MIN (outlen - 136 * i) 136`];;

let SHAKE256_COUNTER_TAC =
  SUBGOAL_THEN
   `word_sub (word (outlen - 136 * i))
             (word(MIN (outlen - 136 * i) 136)):int64 =
    word(outlen - 136 * i - MIN (outlen - 136 * i) 136)` SUBST_ALL_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val(word(outlen - 136 * i - MIN (outlen - 136 * i) 136):int64) =
    outlen - 136 * i - MIN (outlen - 136 * i) 136`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `outlen - 136 * i - MIN (outlen - 136 * i) 136 = 0 <=>
    ~(i + 1 < (outlen + 135) DIV 136)`]);;

(*** The done count at the end of the loop ***)

let SHAKE256_EXIT_TAC =
  SUBGOAL_THEN `MIN outlen (136 * (outlen + 135) DIV 136) = outlen`
   SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN
    MP_TAC(SPECL [`outlen + 135`; `136`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUB_REFL];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The input is a list of bytes, and the outlen bytes of  *)
(* the output, as a number, are the first outlen bytes of shake256 in        *)
(* common/fips202.ml. Each iteration of the loop extracts                    *)
(* MIN (outlen - 136 * i) 136 bytes. As for mlkem_poly_compress_d4, the      *)
(* address of the stack guard is read from the GOT, and the stack is the 304 *)
(* bytes of the function and the 256 used by mlk_keccak_absorb_once below    *)
(* them.                                                                     *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The input is a list of bytes, and the outlen bytes of  *)
(* the output, as a number, are the first outlen bytes of shake256 in        *)
(* common/fips202.ml. Each iteration of the loop extracts                    *)
(* MIN (outlen - 136 * i) 136 bytes. As for mlkem_poly_compress_d4, the      *)
(* address of the stack guard is read from the GOT. The stack is the 64      *)
(* bytes of the saved registers, 256 bytes aligned to 32 bytes for the state *)
(* and the canary (within a block of 272 bytes, since the stack pointer is   *)
(* only a multiple of 16), and the 288 used by mlk_keccak_absorb_once below  *)
(* them.                                                                     *)
(* ------------------------------------------------------------------------- *)

(*** The callee mlk_keccak_absorb_once has the GOT entry of the stack guard ***)
(*** as a precondition, in the form word(pc + got_stack_chk_guard), but    ***)
(*** the code reads it as word_add (word pc) (word got_stack_chk_guard)    ***)

let SHAKE256_GUARD_TAC =
  W(fun (asl,_) ->
    MAP_EVERY (fun (_,th) ->
      if can (term_match []
        `read (memory :> bytes64 (word_add (word pc) (word n))) s = guard`)
        (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else ALL_TAC) asl);;

let MLKEM_NATIVE_SHAKE256_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!out outlen m (inp:byte list) guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(out,outlen); (m,LENGTH inp);
          (word_sub stackpointer (word 624),624)] /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 624),624)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_shake256) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; m; word(LENGTH inp)] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(m,LENGTH inp)) s =
                  num_of_bytelist inp)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist(list_of_seq (shake256 inp) outlen))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 624),624)])`;;

let MLKEM_NATIVE_SHAKE256_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHAKE256_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* guard, read from the GOT.                                                 *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;


let SHAKE256_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,MLKEM_NATIVE_SHAKE256_CLANG17_O3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      ilist n THENL
     [ABSORB_EXISTS_E2_TAC (ref
       [`pc:num`; `m:int64`; `out:int64`; `outlen:num`; `inlen:num`;
        `guard:int64`; `stackpointer:int64`; `returnaddress:int64`;
        `i:num`]);
      LABEL_TAC name safety_th]);;


let MLKEM_NATIVE_SHAKE256_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e out outlen m inlen guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [out,outlen; m,inlen; word_sub stackpointer (word 624),624] /\
       ALLPAIRS nonoverlapping
        [out,outlen; word_sub stackpointer (word 624),624]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O3_mc /\
                 read PC s = word (pc + mlkem_shake256) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; word outlen; m; word inlen] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m out outlen inlen guard pc
                           (word_sub stackpointer (word 624)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,outlen;
                      word_sub stackpointer (word 624),624;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out,outlen; word_sub stackpointer (word 624),624]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,outlen);
               memory :> bytes(word_sub stackpointer (word 624),624)])`;;

let MLKEM_NATIVE_SHAKE256_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHAKE256_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
