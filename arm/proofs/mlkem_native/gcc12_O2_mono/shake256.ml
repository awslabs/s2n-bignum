(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 with an output of any length. This is the code for               *)
(* mlkem_shake256 from mlkem-native's portable C implementation compiled by  *)
(* gcc 12 with -O2 as one translation unit (see mlkem_native/README.md),     *)
(* which absorbs the input into a state on the stack with                    *)
(* mlk_keccak_absorb_once, and then for each block of the output permutes    *)
(* the state with mlk_keccakf1600_permute_c and copies up to 136 bytes of    *)
(* it, the rate of SHAKE256, to the output, before zeroing the state. The   *)
(* inlined extraction of mlkem_keccakf1600_extract_bytes is here a call of   *)
(* memcpy through its PLT stub, so the theorem assumes the contract for      *)
(* memcpy of utils/mlkem_native_libc.ml, as the theorems about functions     *)
(* that call it do. It has the specification of the gcc12_O2 build with      *)
(* three differences: that contract, and the length of the input and the     *)
(* output must be nonzero (0 < LENGTH inp since mlk_keccak_absorb_once       *)
(* requires it; 0 < outlen since the loop is a do-while, which would copy a  *)
(* byte for outlen = 0). It is verified in the whole image (see              *)
(* libmlkem.ml). The result is shake256 of common/fips202.ml.                *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccak_absorb_once.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccakf1600_permute.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(*** The code in the image:

    mlkem_shake256:
     +0x0  stp     x19, x20, [sp, #-320]!
     +0x4  mov     x20, x1
  adrp1:
     +0x8  adrp    x4, <page>
     +0xc  ldr     x4, [x4, #4088]    // got_stack_chk_guard
    +0x10  stp     x21, x22, [sp, #16]
    +0x14  add     x21, sp, #0x5f
    +0x18  stp     x23, x24, [sp, #32]
    +0x1c  and     x21, x21, #0xffffffffffffffe0
    +0x20  mov     x22, x0
    +0x24  str     x30, [sp, #48]
    +0x28  mov     x0, x21
    +0x2c  mov     x24, #0x88
    +0x30  mov     x23, #0x1
    +0x34  ldr     x1, [x4]
    +0x38  str     x1, [sp, #312]
    +0x3c  mov     x1, #0x0
    +0x40  mov     w4, #0x1f
    +0x44  mov     w1, #0x88
    +0x48  bl      mlk_keccak_absorb_once
    +0x4c  nop
  loop1:
    +0x50  mov     x0, x21
    +0x54  bl      mlk_keccakf1600_permute_c
    +0x58  cmp     x20, #0x88
    +0x5c  mov     x0, x22
    +0x60  csel    x19, x20, x24, ls
    +0x64  mov     x1, x21
    +0x68  cmp     w19, #0x0
    +0x6c  add     x22, x22, x19
    +0x70  csel    x2, x19, x23, ne
    +0x74  bl      memcpy (through plt_memcpy)
  loop1_test:
    +0x78  subs    x20, x20, x19
  loop1_back:
    +0x7c  b.ne    loop1
  loop1_exit:
    +0x80  movi    v0.4s, #0x0
    +0x84  stp     q0, q0, [x21]
    +0x88  stp     q0, q0, [x21, #32]
    +0x8c  stp     q0, q0, [x21, #64]
    +0x90  stp     q0, q0, [x21, #96]
    +0x94  stp     q0, q0, [x21, #128]
    +0x98  stp     q0, q0, [x21, #160]
    +0x9c  stp     q0, q0, [x21, #192]
  adrp2:
    +0xa0  adrp    x0, <page>
    +0xa4  ldr     x0, [x0, #4088]    // got_stack_chk_guard
    +0xa8  ldr     x2, [sp, #312]
    +0xac  ldr     x1, [x0]
    +0xb0  subs    x2, x2, x1
    +0xb4  mov     x1, #0x0
    +0xb8  b.ne    stack_chk_fail
    +0xbc  ldp     x21, x22, [sp, #16]
    +0xc0  ldp     x23, x24, [sp, #32]
    +0xc4  ldr     x30, [sp, #48]
    +0xc8  ldp     x19, x20, [sp], #320
  ret:
    +0xcc  ret
    +0xd0  bl      stack_chk_fail
 ***)

let MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlkem_shake256"; layout_range "plt_memcpy"];;


(* ------------------------------------------------------------------------- *)
(* The state is aligned to 32 bytes within the stack frame, so its address   *)
(* depends on whether the stack pointer is a multiple of 32 or just of 16.   *)
(* ------------------------------------------------------------------------- *)

let ALIGNED_16_32_WORD_AND = prove
 (`(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`,
  CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`x:int64`; `4`] (CONJUNCT1 WORD_AND_MASK_WORD));
    MP_TAC(ISPECL [`x:int64`; `5`] (CONJUNCT1 WORD_AND_MASK_WORD))] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16`; ARITH_RULE `x MOD 32 < 32`;
           ARITH_RULE `x < 16 ==> x < 2 EXP 64`;
           ARITH_RULE `x < 32 ==> x < 2 EXP 64`]);;

let SHAKE256_STATE_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 351)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 320 else 336))`,
  REWRITE_TAC[ALIGNED_16_32_WORD_AND] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let SHAKE256_STATE_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 351))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 320 else 336))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC SHAKE256_STATE_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let SHAKE256_ST = `word_add (stackpointer:int64)
                    (word(if aligned 32 stackpointer then 320 else 336))`;;

(*** The setup for both proofs, with the bounds on the offset of the state ***)


(*** The bound on outlen from the nonoverlapping, and its 64-bit word ***)

let SHAKE256_BOUND_TAC =
  SUBGOAL_THEN `576 + outlen <= 18446744073709551616` ASSUME_TAC THENL
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


(*** The number of bytes extracted in each iteration, MIN x 136 ***)

let SHAKE256_CSEL_LEMMA = prove
 (`!x. x < 2 EXP 64
       ==> (if ~(136 <= val (word x:int64) /\
                 ~(val (word_sub (word x) (word 136):int64) = 0))
            then word x else word 136):int64 = word(MIN x 136)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
  SUBGOAL_THEN `val(word x:int64) = x /\ val(word 136:int64) = 136`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `x < 2 EXP 64` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    COND_CASES_TAC THEN AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC]);;

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

let READ_MEMORY_BYTES_PREFIX = prove
 (`!a:int64 n x l s:armstate.
        read (memory :> bytes(a,n)) s = x /\ l <= n
        ==> read (memory :> bytes(a,l)) s = x MOD 2 EXP (8 * l)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;


let SHAKE256_X2_LEMMA = prove
 (`!k. 0 < k /\ k <= 136
       ==> (if ~(val (word_sub (word_zx (word k:int64):int32) (word 0)) = 0)
            then word k:int64 else word 1) = word k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SUB_0] THEN
  SUBGOAL_THEN `~(val (word_zx (word k:int64):int32) = 0)`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `k MOD 18446744073709551616 = k` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k MOD 4294967296 = k` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;


(*** The setup: the registers saved in the frame, the stack guard, the GOT ***)

let SHAKE256_MONO_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 576):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `320 <= (if aligned 32 (stackpointer:int64) then 320 else 336) /\
    (if aligned 32 (stackpointer:int64) then 320 else 336) <= 336`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24`;;

let SHAKE256_MONO_FRAME =
 "read SP s = word_add stackpointer (word 256) /\\
  read (memory :> bytes64 (word_add stackpointer (word 256))) s = x19_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 264))) s = x20_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 272))) s = x21_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 280))) s = x22_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 288))) s = x23_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 296))) s = x24_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 304))) s =
  returnaddress /\\
  read (memory :> bytes64 (word_add stackpointer (word 568))) s = canary /\\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
  guard /\\
  read (memory :> bytes64 guard) s = canary /\\
  read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev";;

let SHAKE256_MONO_ST =
 "word_add (stackpointer:int64)
   (word(if aligned 32 stackpointer then 320 else 336))";;

let SHAKE256_MONO_STATE =
 "val(word_xor
         (keccak_absorb 136
           (num_of_bytelist inp +
            2 EXP (8 * LENGTH inp) *
            num_of_bytelist(keccak_pad 136 31 (LENGTH inp)))
           (LENGTH(inp:byte list) DIV 136))
         (word((num_of_bytelist inp +
                2 EXP (8 * LENGTH inp) *
                num_of_bytelist(keccak_pad 136 31 (LENGTH inp))) DIV
               2 EXP (8 * 136 * LENGTH inp DIV 136) MOD
               2 EXP (8 * 136))):1600 word)";;

let SHAKE256_MONO_MID = parse_term
 ("\\s. read X20 s = word outlen /\\
        read X21 s = " ^ SHAKE256_MONO_ST ^ " /\\
        read X22 s = out /\\ read X23 s = word 1 /\\ read X24 s = word 136 /\\ " ^
  SHAKE256_MONO_FRAME ^ " /\\
        read (memory :> bytes(" ^ SHAKE256_MONO_ST ^ ",200)) s = " ^
  SHAKE256_MONO_STATE);;

let SHAKE256_MONO_INV = parse_term
 ("\\i s. read X20 s = word(outlen - MIN outlen (136 * i)) /\\
          read X21 s = " ^ SHAKE256_MONO_ST ^ " /\\
          read X22 s = word_add out (word(MIN outlen (136 * i))) /\\
          read X23 s = word 1 /\\ read X24 s = word 136 /\\ " ^
  SHAKE256_MONO_FRAME ^ " /\\
          read (memory :> bytes(out,MIN outlen (136 * i))) s =
          num_of_bytelist
           (list_of_seq (shake256 inp) (MIN outlen (136 * i))) /\\
          read (memory :> bytes(" ^ SHAKE256_MONO_ST ^ ",200)) s =
          val(keccak_squeeze i
           (word_xor
             (keccak_absorb 136
               (num_of_bytelist inp +
                2 EXP (8 * LENGTH inp) *
                num_of_bytelist(keccak_pad 136 31 (LENGTH inp)))
               (LENGTH(inp:byte list) DIV 136))
             (word((num_of_bytelist inp +
                    2 EXP (8 * LENGTH inp) *
                    num_of_bytelist(keccak_pad 136 31 (LENGTH inp))) DIV
                   2 EXP (8 * 136 * LENGTH inp DIV 136) MOD
                   2 EXP (8 * 136))):1600 word))");;


let SHAKE256_MEMCPY_TAC n =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c &&
       can (term_match [] `read (memory :> bytes(word_add (stackpointer:int64) (word(if aligned 32 stackpointer then 320 else 336)),200)) s`) (lhand c)
    then
      let pf = MATCH_MP READ_MEMORY_BYTES_PREFIX
           (CONJ th (ASSUME `MIN (outlen - 136 * i) 136 <= 200`)) in
      ASSUME_TAC pf THEN
      LIBC_CALL_TAC "H_MEMCPY" MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC
       [`read X0 s`; `read X1 s`; `read X2 s`; rand(concl pf); `read X30 s`] n
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The input is a list of bytes, and the outlen bytes of  *)
(* the output, as a number, are the first outlen bytes of shake256 in        *)
(* common/fips202.ml. Each iteration of the loop extracts                    *)
(* MIN (outlen - 136 * i) 136 bytes. The address of the stack guard is read  *)
(* from the GOT, and the stack is the 320 bytes of the function and the 256  *)
(* used by mlk_keccak_absorb_once below them.                                *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT = prove
 (`!out outlen m (inp:byte list) guard mc ea el ev pc stackpointer
   returnaddress.
        memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < outlen /\ 0 < LENGTH inp /\
        PAIRWISE nonoverlapping
         [(out,outlen); (m,LENGTH inp);
          (word_sub stackpointer (word 576),576)] /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 576),576)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlkem_shake256) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; m; word(LENGTH inp)] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(m,LENGTH inp)) s =
                  num_of_bytelist inp)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist(list_of_seq (shake256 inp) outlen))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 576),576)])`,
  MAP_EVERY X_GEN_TAC
   [`out:int64`; `outlen:num`; `m:int64`; `inp:byte list`; `guard:int64`;
    `mc:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 576 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H_MEMCPY" o
                              REWRITE_RULE[memcpy_contract])
                             (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SHAKE256_MONO_SETUP_TAC THEN

  (*** The absorption, up to the loop ***)

  ENSURES_SEQUENCE_TAC `pc + mlkem_shake256_after_mlk_keccak_absorb_once`
   SHAKE256_MONO_MID THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (1--3) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (4--8) THEN
    SHAKE256_STATE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (9--19) THEN
    ARM_SUBROUTINE_SIM_TAC
     (mlkem_native_libmlkem_gcc12_O2_mono_mc,
      MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC,
      0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
      MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT)
     [`read X0 s`; `136`; `read X2 s`; `LENGTH(inp:byte list)`; `31`;
      `num_of_bytelist(inp:byte list)`; `pc:num`; `read SP s`; `read X30 s`]
     20 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The loop, with MIN outlen (136 * i) bytes done ***)

  SUBGOAL_THEN `~(outlen = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SHAKE256_BOUND_TAC THEN
  ENSURES_WHILE_UP2_TAC `(outlen + 135) DIV 136` `pc + mlkem_shake256_loop1`
   `pc + mlkem_shake256_loop1_exit` SHAKE256_MONO_INV THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[DIV_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC;

    (*** Initialization: the nop ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `MIN n 0 = 0`; SUB_0; WORD_ADD_0;
                READ_MEMORY_BYTES_TRIVIAL; list_of_seq; num_of_bytelist;
                keccak_squeeze];

    (*** The loop body: permute, then copy the next block with memcpy ***)

    SHAKE256_ITERATION_TAC ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (1--2) THEN
    KECCAK_STATE_AT_TAC SHAKE256_ST THEN
    KECCAK_STATE_THEN SHAKE256_ST (fun v ->
      ARM_SUBROUTINE_SIM_TAC
       (mlkem_native_libmlkem_gcc12_O2_mono_mc,
        MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC,
        0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
      MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_F1600)
       [`read X0 s`; v; `pc:num`; `read SP s`; `read X30 s`] 3) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (4--10) THEN
    SHAKE256_LENGTH_TAC THEN
    MP_TAC(SPEC `MIN (outlen - 136 * i) 136` SHAKE256_X2_LEMMA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
    SUBGOAL_THEN `MIN (outlen - 136 * i) 136 <= 200` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word (MIN (outlen - 136 * i) 136):int64) =
                  MIN (outlen - 136 * i) 136` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (11--11) THEN
    LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC 11 THEN
    SHAKE256_MEMCPY_TAC 16 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (17--18) THEN
    SHAKE256_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[];
      AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[shake256] THEN CONV_TAC SYM_CONV THEN
      REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 keccak_squeeze); ADD1] THEN
      MATCH_MP_TAC KECCAK_SPONGE_BLOCK THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[GSYM ADD1; keccak_squeeze]];

    (*** Zeroing the state, the check of the stack guard and the return ***)

    SHAKE256_EXIT_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (1--9) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (10--20) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend on the address   *)
(* of the stack guard, read from the GOT, and on the address mc of memcpy,   *)
(* so the theorem is stated directly, with the safety contract for memcpy.   *)
(* There is no theorem with the correctness statement together with the      *)
(* events, as in gcc12_O2.                                                   *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let SHAKE256_SAFE_VARS =
  [`pc:num`; `m:int64`; `out:int64`; `outlen:num`; `inlen:num`;
   `guard:int64`; `mc:int64`; `ea:int64`; `el:num`; `stackpointer:int64`;
   `returnaddress:int64`; `i:num`];;

let SHAKE256_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,
       MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [ABS_EXISTS_E2_TAC (ref SHAKE256_SAFE_VARS); LABEL_TAC name safety_th]);;

let SHAKE256_LIBC_SAFE_CALL_TAC name n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true
      MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC th
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `read X30 s`] n THENL
     [ABS_EXISTS_E2_TAC (ref SHAKE256_SAFE_VARS); LABEL_TAC name th]);;

let SHAKE256_SAFE_MID = parse_term
 ("\\s. read X20 s = word outlen /\\
        read X21 s = " ^ SHAKE256_MONO_ST ^ " /\\
        read X22 s = out /\\ read X23 s = word 1 /\\ read X24 s = word 136 /\\ " ^
  SHAKE256_MONO_FRAME);;

let SHAKE256_SAFE_INV = parse_term
 ("\\i s. read X20 s = word(outlen - MIN outlen (136 * i)) /\\
          read X21 s = " ^ SHAKE256_MONO_ST ^ " /\\
          read X22 s = word_add out (word(MIN outlen (136 * i))) /\\
          read X23 s = word 1 /\\ read X24 s = word 136 /\\ " ^
  SHAKE256_MONO_FRAME);;

let SHAKE256_SAFE_TEMPLATE =
 `\(m:int64) (out:int64) (outlen:num) (inlen:num) (guard:int64) (mc:int64)
   (pc:num) (stackpointer:int64) (returnaddress:int64).
   APPEND
    (APPEND
      (f_ev_epil m out outlen inlen guard mc pc stackpointer returnaddress)
      (APPEND
        (ENUMERATEL ((outlen + 135) DIV 136)
          (\i. f_ev_loop m out outlen inlen guard mc pc stackpointer
                         returnaddress i))
        (f_ev_prol m out outlen inlen guard mc pc stackpointer
                   returnaddress)))
    (f_ev_absorb m out outlen inlen guard mc pc stackpointer returnaddress)
   :(uarch_event)list`;;

let SHAKE256_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[memcpy_safety_contract] THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMCPY") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC SHAKE256_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SHAKE256_MONO_SETUP_TAC;;

let MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`!mc ea el ev.
     memcpy_safety_contract mc ea el ev
     ==> exists f_events.
          forall e out outlen m inlen guard pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\ 0 < outlen /\ 0 < inlen /\
           PAIRWISE nonoverlapping
            [out,outlen; m,inlen; word_sub stackpointer (word 576),576] /\
           ALLPAIRS nonoverlapping
            [out,outlen; word_sub stackpointer (word 576),576]
            [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8;
             word(pc + got_memcpy),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                     read PC s = word (pc + mlkem_shake256) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [out; word outlen; m; word inlen] s /\
                     read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                          s = guard /\
                     read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events m out outlen inlen guard mc pc
                               (word_sub stackpointer (word 576))
                               returnaddress /\
                        memaccess_inbounds e2
                         [m,inlen; out,outlen;
                          word_sub stackpointer (word 576),576;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                          word(pc + got_memcpy),8; ea,el]
                         [out,outlen; word_sub stackpointer (word 576),576]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(out,outlen);
                   memory :> bytes(word_sub stackpointer (word 576),576)])`,
  SHAKE256_SAFE_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_shake256_after_mlk_keccak_absorb_once`
   SHAKE256_SAFE_MID THEN CONJ_TAC THENL
   [(*** The absorption, up to the loop ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (1--3) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (4--8) THEN
    SHAKE256_STATE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (9--19) THEN
    SHAKE256_SAFE_CALL_TAC "H_ABSORB"
     [`e:(uarch_event)list`; `read X0 s`; `136`; `read X2 s`; `inlen:num`;
      `31`; `pc:num`; `read SP s`; `read X30 s`] 20 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ABS_DISCHARGE_TAC;

    (*** The loop, with MIN outlen (136 * i) bytes done ***)

    SUBGOAL_THEN `~(outlen = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SHAKE256_BOUND_TAC THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `(outlen + 135) DIV 136`
     `pc + mlkem_shake256_loop1` `pc + mlkem_shake256_loop1_exit`
     SHAKE256_SAFE_INV THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[DIV_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC;

      (*** Initialization: the nop ***)

      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (1--1) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `MIN n 0 = 0`; SUB_0;
                  WORD_ADD_0] THEN
      ABS_DISCHARGE_TAC;

      (*** The loop body: permute, then copy the next block with memcpy ***)

SHAKE256_ITERATION_TAC (REWRITE_TAC[]) THEN
        REWRITE_TAC(!simulation_precanon_thms) THEN
        ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
        ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (1--2) THEN
        SHAKE256_SAFE_CALL_TAC "H_PERMUTE"
         [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
          `read X30 s`] 3 THEN
        ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (4--10) THEN
        SHAKE256_LENGTH_TAC THEN
        MP_TAC(SPEC `MIN (outlen - 136 * i) 136` SHAKE256_X2_LEMMA) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[];
          DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
        SUBGOAL_THEN `val(word (MIN (outlen - 136 * i) 136):int64) =
                      MIN (outlen - 136 * i) 136` ASSUME_TAC THENL
         [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
          CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
        ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (11--11) THEN
        LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC 11 THEN
        SHAKE256_LIBC_SAFE_CALL_TAC "H_MEMCPY" 16 THEN
        ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (17--18) THEN
        SHAKE256_COUNTER_TAC THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL
         [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]; ALL_TAC] THEN
        ABS_DISCHARGE_TAC;

      (*** Zeroing the state, the check of the stack guard and the return ***)

    SHAKE256_EXIT_TAC THEN
        REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
        ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
        ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (1--9) THEN
        MLKEM_NATIVE_ADRP_TAC THEN
        ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_MONO_EXEC (10--20) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        ABS_DISCHARGE_TAC]]);;
