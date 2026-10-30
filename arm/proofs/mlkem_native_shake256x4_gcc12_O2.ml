(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 of four inputs of the same length, with four outputs of any      *)
(* length. This is the code for mlkem_shake256x4 from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which zeroes a context of four states on the     *)
(* stack with memset, absorbs the inputs into it with                        *)
(* mlk_keccak_absorb_once_x4, squeezes the whole blocks of 136 bytes, the    *)
(* rate of SHAKE256, directly into the outputs, and the rest of the outputs  *)
(* through four buffers on the stack with memcpy, before zeroing the context *)
(* with memset and the buffers. It is verified in the whole image (see       *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x2a20, using  *)
(* the theorems for mlk_keccak_absorb_once_x4 at 0x27a0,                     *)
(* mlkem_keccakf1600x4_permute at 0x33a0 and                                 *)
(* mlkem_keccakf1600x4_extract_bytes at 0x2cd0 in the image and assuming the *)
(* contracts for memset and memcpy in utils/mlkem_native_libc.ml. The result *)
(* is shake256 of common/fips202.ml for each input.                          *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native_keccak_absorb_once_x4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_keccakf1600x4_permute_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_keccakf1600x4_extract_bytes_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image, and the PLT stubs for memcpy and memset:

    2a20: sub     sp, sp, #0x5d0
    2a24: adrp    x8, 1f000 <mlk_zetas+0x18c80>
    2a28: ldr     x8, [x8, #4088]
    2a2c: stp     x25, x26, [sp, #48]
    2a30: mov     x26, #0xf0f0f0f0f0f0f0f0
    2a34: movk    x26, #0xf0f1
    2a38: stp     x19, x20, [sp]
    2a3c: add     x20, sp, #0x8f
    2a40: and     x20, x20, #0xffffffffffffffe0
    2a44: stp     x21, x22, [sp, #16]
    2a48: umulh   x26, x4, x26
    2a4c: mov     x19, x5
    2a50: stp     x23, x24, [sp, #32]
    2a54: mov     x21, x6
    2a58: mov     x22, x3
    2a5c: stp     x27, x28, [sp, #64]
    2a60: mov     x25, x0
    2a64: mov     x27, x4
    2a68: str     x30, [sp, #80]
    2a6c: mov     x24, x1
    2a70: str     x7, [sp, #104]
    2a74: mov     x23, x2
    2a78: ldr     x28, [sp, #1488]
    2a7c: ldr     x1, [x8]
    2a80: str     x1, [sp, #1480]
    2a84: mov     x1, #0x0
    2a88: mov     x2, #0x320
    2a8c: mov     x0, x20
    2a90: bl      840 <memset@plt>
    2a94: lsr     x26, x26, #7
    2a98: ldr     x4, [sp, #104]
    2a9c: mov     x5, x28
    2aa0: ldr     x6, [sp, #1496]
    2aa4: mov     x3, x21
    2aa8: mov     x2, x19
    2aac: mov     x0, x20
    2ab0: mov     w1, #0x88
    2ab4: bl      27a0 <mlk_keccak_absorb_once_x4.constprop.0>
    2ab8: cmp     x27, #0x87
    2abc: b.ls    2afc <mlkem_shake256x4+0xdc>
    2ac0: mov     x21, x26
    2ac4: mov     x19, #0x0
    2ac8: mov     x0, x20
    2acc: bl      33a0 <mlkem_keccakf1600x4_permute>
    2ad0: add     x4, x22, x19
    2ad4: add     x3, x23, x19
    2ad8: add     x2, x24, x19
    2adc: add     x1, x25, x19
    2ae0: mov     x0, x20
    2ae4: mov     w6, #0x88
    2ae8: mov     w5, #0x0
    2aec: bl      2cd0 <mlkem_keccakf1600x4_extract_bytes>
    2af0: add     x19, x19, #0x88
    2af4: subs    x21, x21, #0x1
    2af8: b.ne    2ac8 <mlkem_shake256x4+0xa8>
    2afc: mov     x19, #0xf0f0f0f0f0f0f0f0
    2b00: movk    x19, #0xf0f1
    2b04: umulh   x19, x27, x19
    2b08: lsr     x19, x19, #7
    2b0c: add     x19, x19, x19, lsl #4
    2b10: subs    x19, x27, x19, lsl #3
    2b14: b.ne    2bc8 <mlkem_shake256x4+0x1a8>
    2b18: add     x21, sp, #0x540
    2b1c: add     x27, sp, #0x4b8
    2b20: add     x26, sp, #0x430
    2b24: add     x28, sp, #0x3a8
    2b28: mov     x0, x20
    2b2c: mov     x2, #0x320
    2b30: mov     w1, #0x0
    2b34: bl      840 <memset@plt>
    2b38: movi    v0.4s, #0x0
    2b3c: str     xzr, [x28, #128]
    2b40: stp     q0, q0, [x28]
    2b44: stp     q0, q0, [x28, #32]
    2b48: stp     q0, q0, [x28, #64]
    2b4c: stp     q0, q0, [x28, #96]
    2b50: stp     q0, q0, [x26]
    2b54: stp     q0, q0, [x26, #32]
    2b58: stp     q0, q0, [x26, #64]
    2b5c: stp     q0, q0, [x26, #96]
    2b60: str     xzr, [x26, #128]
    2b64: stp     q0, q0, [x27]
    2b68: stp     q0, q0, [x27, #32]
    2b6c: stp     q0, q0, [x27, #64]
    2b70: stp     q0, q0, [x27, #96]
    2b74: str     xzr, [x27, #128]
    2b78: stp     q0, q0, [x21]
    2b7c: stp     q0, q0, [x21, #32]
    2b80: stp     q0, q0, [x21, #64]
    2b84: stp     q0, q0, [x21, #96]
    2b88: str     xzr, [x21, #128]
    2b8c: adrp    x0, 1f000 <mlk_zetas+0x18c80>
    2b90: ldr     x0, [x0, #4088]
    2b94: ldr     x2, [sp, #1480]
    2b98: ldr     x1, [x0]
    2b9c: subs    x2, x2, x1
    2ba0: mov     x1, #0x0
    2ba4: b.ne    2c58 <mlkem_shake256x4+0x238>
    2ba8: ldp     x19, x20, [sp]
    2bac: ldp     x21, x22, [sp, #16]
    2bb0: ldp     x23, x24, [sp, #32]
    2bb4: ldp     x25, x26, [sp, #48]
    2bb8: ldp     x27, x28, [sp, #64]
    2bbc: ldr     x30, [sp, #80]
    2bc0: add     sp, sp, #0x5d0
    2bc4: ret
    2bc8: add     x26, x26, x26, lsl #4
    2bcc: mov     x0, x20
    2bd0: add     x21, sp, #0x540
    2bd4: add     x27, sp, #0x4b8
    2bd8: lsl     x1, x26, #3
    2bdc: add     x28, sp, #0x3a8
    2be0: add     x26, sp, #0x430
    2be4: str     x1, [sp, #104]
    2be8: bl      33a0 <mlkem_keccakf1600x4_permute>
    2bec: mov     x4, x21
    2bf0: mov     x3, x27
    2bf4: mov     w6, #0x88
    2bf8: mov     w5, #0x0
    2bfc: mov     x2, x26
    2c00: mov     x1, x28
    2c04: mov     x0, x20
    2c08: bl      2cd0 <mlkem_keccakf1600x4_extract_bytes>
    2c0c: ldr     x0, [sp, #104]
    2c10: mov     x2, x19
    2c14: mov     x1, x28
    2c18: add     x0, x25, x0
    2c1c: bl      810 <memcpy@plt>
    2c20: ldr     x25, [sp, #104]
    2c24: mov     x2, x19
    2c28: mov     x1, x26
    2c2c: add     x0, x24, x25
    2c30: bl      810 <memcpy@plt>
    2c34: mov     x2, x19
    2c38: mov     x1, x27
    2c3c: add     x0, x23, x25
    2c40: bl      810 <memcpy@plt>
    2c44: mov     x2, x19
    2c48: mov     x1, x21
    2c4c: add     x0, x22, x25
    2c50: bl      810 <memcpy@plt>
    2c54: b       2b28 <mlkem_shake256x4+0x108>
    2c58: bl      830 <__stack_chk_fail@plt>

    810: adrp    x16, 1f000 <mlk_zetas+0x18c80>
    814: ldr     x17, [x16, #4048]
    818: add     x16, x16, #0xfd0
    81c: br      x17

    840: adrp    x16, 1f000 <mlk_zetas+0x18c80>
    844: ldr     x17, [x16, #4072]
    848: add     x16, x16, #0xfe8
    84c: br      x17
 ***)

let MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x2a20,0x2c5c; 0x810,0x820; 0x840,0x850];;

(* ------------------------------------------------------------------------- *)
(* The context is aligned to 32 bytes within the stack frame, so its address *)
(* depends on whether the stack pointer is a multiple of 32 or just of 16.   *)
(* The four states in it are at offsets 0, 200, 400 and 600, in the form in  *)
(* which their addresses are normalized by the simulation.                   *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_ALIGNED_16_32 = prove
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

let SHAKE256X4_CTX_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 447)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 416 else 432))`,
  REWRITE_TAC[SHAKE256X4_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let SHAKE256X4_CTX_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 447))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 416 else 432))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC SHAKE256X4_CTX_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let SHAKE256X4_ST =
  [`word_add stackpointer
     (word(if aligned 32 stackpointer then 416 else 432)):int64`;
   `word_add stackpointer
     (word((if aligned 32 stackpointer then 416 else 432) + 200)):int64`;
   `word_add stackpointer
     (word((if aligned 32 stackpointer then 416 else 432) + 400)):int64`;
   `word_add stackpointer
     (word((if aligned 32 stackpointer then 416 else 432) + 600)):int64`];;

let SHAKE256X4_STATES_TAC = MAP_EVERY KECCAK_STATE_AT_TAC SHAKE256X4_ST;;

(* ------------------------------------------------------------------------- *)
(* The number of whole blocks, outlen DIV 136, is computed by multiplying by *)
(* a constant (umulh and lsr), and multiplied back by 136 with shifts, to    *)
(* get the number of remaining bytes, outlen MOD 136. The loop is skipped    *)
(* if outlen <= 135, that is if there are no whole blocks.                   *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_NBLOCKS = prove
 (`!x. x < 2 EXP 64
       ==> (x * 17361641481138401521) DIV 2 EXP 64 DIV 2 EXP 7 = x DIV 136`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`x:num`; `136`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`x MOD 136`,`r:num`) THEN SPEC_TAC(`x DIV 136`,`q:num`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `8 * q + r * 17361641481138401521` THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;

let SHAKE256X4_NBLOCKS_WORD = prove
 (`!n. n < 2 EXP 64
       ==> word_ushr (word((n * 17361641481138401521) DIV 2 EXP 64):int64) 7 =
           word(n DIV 136)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `val(word((n * 17361641481138401521) DIV 2 EXP 64):int64) =
    (n * 17361641481138401521) DIV 2 EXP 64`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LTE_TRANS `2 EXP 64 * 17361641481138401521` THEN
    ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN CONV_TAC NUM_REDUCE_CONV;
    MATCH_MP_TAC SHAKE256X4_NBLOCKS THEN ASM_REWRITE_TAC[]]);;

let SHAKE256X4_MUL136 = prove
 (`!n. word_shl (word_add (word n) (word_shl (word n) 4)) 3:int64 =
       word(136 * n)`,
  GEN_TAC THEN REWRITE_TAC[word_shl; VAL_WORD; DIMINDEX_64; GSYM WORD_ADD] THEN
  REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let SHAKE256X4_LS_LEMMA = prove
 (`!n. n < 2 EXP 64
       ==> (135 <= n /\ ~(val(word_sub (word n) (word 135):int64) = 0) <=>
            ~(n DIV 136 = 0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
  SUBGOAL_THEN `val(word n:int64) = n /\ val(word 135:int64) = 135`
   (fun th -> REWRITE_TAC[th])
  THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
    ASM_REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[DIV_EQ_0; ARITH_EQ] THEN ARITH_TAC]);;

(*** The bound on outlen, nb whole blocks and rest remaining bytes ***)

let SHAKE256X4_BOUND_TAC =
  SUBGOAL_THEN `outlen < 2 EXP 64` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1792 + n <= 2 EXP 64 ==> n < 2 EXP 64`) THEN
    MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(stackpointer:int64)`; `val(out0:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word outlen:int64) = outlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  SUBGOAL_THEN
   `136 * outlen DIV 136 + outlen MOD 136 = outlen /\ outlen MOD 136 < 136`
  MP_TAC THENL
   [MP_TAC(SPECL [`outlen:num`; `136`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `nb = outlen DIV 136` THEN ABBREV_TAC `rest = outlen MOD 136` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `rest <= 136 /\ val(word rest:int64) = rest` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC VAL_WORD_EQ] THEN
    REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `rest < 136` THEN ARITH_TAC;
    ALL_TAC];;

(*** The number of blocks, the branch round the loop and the remainder ***)

let SHAKE256X4_NBLOCKS_TAC =
  let th = REWRITE_RULE[ASSUME `outlen DIV 136 = nb`]
            (MP (SPEC `outlen:num` SHAKE256X4_NBLOCKS_WORD)
                (ASSUME `outlen < 2 EXP 64`)) in
  RULE_ASSUM_TAC(REWRITE_RULE[th]);;

let SHAKE256X4_BRANCH_TAC th tm =
  RULE_ASSUM_TAC(fun th' ->
    if is_eq(concl th') && is_cond(rand(concl th'))
    then REWRITE_RULE[th; ASSUME tm] th' else th');;

let SHAKE256X4_LS_TAC tm =
  SHAKE256X4_BRANCH_TAC
   (REWRITE_RULE[ASSUME `outlen DIV 136 = nb`]
     (MP (SPEC `outlen:num` SHAKE256X4_LS_LEMMA)
         (ASSUME `outlen < 2 EXP 64`))) tm;;

let SHAKE256X4_REST_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[SHAKE256X4_MUL136]) THEN
  SUBGOAL_THEN `word_sub (word outlen) (word(136 * nb)):int64 = word rest`
   (fun th ->
      let t = `val(word rest:int64) = rest` in
      RULE_ASSUM_TAC(fun th' ->
        if concl th' = t then th' else REWRITE_RULE[th; ASSUME t] th')) THENL
   [FIRST_ASSUM(fun th ->
      if concl th = `136 * nb + rest = outlen` then SUBST1_TAC(SYM th)
      else NO_TAC) THEN
    REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
    ALL_TAC];;

(*** The loop counter, nb - i, after the subs ***)

let SHAKE256X4_COUNTER_TAC =
  SUBGOAL_THEN `word_sub (word (nb - i)) (word 1):int64 = word(nb - (i + 1))`
  SUBST_ALL_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
    ANTS_TAC THENL [UNDISCH_TAC `i < nb` THEN ARITH_TAC;
                    DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(nb - (i + 1)):int64) = nb - (i + 1)`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY UNDISCH_TAC
     [`outlen < 2 EXP 64`; `136 * nb + rest = outlen`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(nb - (i + 1) = 0) <=> i + 1 < nb`
  SUBST_ALL_TAC THENL [ARITH_TAC; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The setup for both proofs, the GOT entry for the stack guard in the form  *)
(* needed by mlk_keccak_absorb_once_x4, and the facts holding at all the     *)
(* intermediate points: the saved registers, the stack guard and the GOT.    *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 1792):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `416 <= (if aligned 32 (stackpointer:int64) then 416 else 432) /\
    (if aligned 32 (stackpointer:int64) then 416 else 432) <= 432`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD;
              SPECL [`pc:num`; `0x1ffe8`] WORD_ADD;
              SPECL [`pc:num`; `0x1ffd0`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD;
                              SPECL [`pc:num`; `0x1ffe8`] WORD_ADD;
                              SPECL [`pc:num`; `0x1ffd0`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--28);;

let SHAKE256X4_GOT_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes64 (word_add (word pc) (word 131064))) s =
          g:int64`)
         (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC);;

let SHAKE256X4_FRAME =
 `read SP s = word_add stackpointer (word 304) /\
  read (memory :> bytes64 (word_add stackpointer (word 304))) s = x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word 312))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 320))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 328))) s = x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 336))) s = x23_init /\
  read (memory :> bytes64 (word_add stackpointer (word 344))) s = x24_init /\
  read (memory :> bytes64 (word_add stackpointer (word 352))) s = x25_init /\
  read (memory :> bytes64 (word_add stackpointer (word 360))) s = x26_init /\
  read (memory :> bytes64 (word_add stackpointer (word 368))) s = x27_init /\
  read (memory :> bytes64 (word_add stackpointer (word 376))) s = x28_init /\
  read (memory :> bytes64 (word_add stackpointer (word 384))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 1784))) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word 131064))) s = guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word 131048))) s = mf /\
  read (memory :> bytes64 (word_add (word pc) (word 131024))) s = mc /\
  read (memory :> bytes(ea,el)) s = ev`;;

let SHAKE256X4_AT t =
  let vs,bod = strip_abs t in list_mk_abs(vs,mk_conj(bod,SHAKE256X4_FRAME));;

(*** The subroutines ***)

let LOCAL_ABSORB_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_PERMUTE_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
  MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600);;

let LOCAL_EXTRACT_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
  MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* The output of SHAKE256 in blocks, as in mlkem_shake256, in terms of the   *)
(* state after absorbing the input as by mlk_keccak_absorb_once_x4, and the  *)
(* first n bytes of one of the buffers holding a block.                      *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_SPONGE = prove
 (`!(m:byte list) k n.
        n <= 136
        ==> num_of_bytelist(list_of_seq (\j. shake256 m (136 * k + j)) n) =
            val(keccak_squeeze (k + 1)
                 (word_xor
                   (keccak_absorb 136
                     (num_of_bytelist m +
                      2 EXP (8 * LENGTH m) *
                      num_of_bytelist(keccak_pad 136 0x1F (LENGTH m)))
                     (LENGTH m DIV 136))
                   (word((num_of_bytelist m +
                          2 EXP (8 * LENGTH m) *
                          num_of_bytelist(keccak_pad 136 0x1F (LENGTH m))) DIV
                         2 EXP (8 * 136 * LENGTH m DIV 136) MOD
                         2 EXP (8 * 136))))) MOD 2 EXP (8 * n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[shake256] THEN
  MATCH_MP_TAC KECCAK_SPONGE_BLOCK THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let SHAKE256X4_TMP_LEMMA = prove
 (`!a (S:1600 word) n s:armstate.
        read (memory :> bytes(a,136)) s =
        (val S DIV 2 EXP (8 * 0)) MOD 2 EXP (8 * 136) /\ n <= 136
        ==> read (memory :> bytes(a,n)) s = val S MOD 2 EXP (8 * n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `136`; `n:num`; `read memory s`]
                READ_BYTES_MOD) THEN
  ASM_REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `n <= 136 ==> MIN 136 n = n /\ MIN (8 * 136) (8 * n) = 8 * n`]);;

(*** The four absorbed states as S0, ..., S3, with their outputs ***)

let SHAKE256X4_ABSORBED =
 `\M. word_xor
       (keccak_absorb 136
         (M + 2 EXP (8 * inlen) * num_of_bytelist(keccak_pad 136 0x1F inlen))
         (inlen DIV 136))
       (word((M + 2 EXP (8 * inlen) *
                  num_of_bytelist(keccak_pad 136 0x1F inlen)) DIV
             2 EXP (8 * 136 * inlen DIV 136) MOD 2 EXP (8 * 136))):1600 word`;;

let SHAKE256X4_ABSORBED_TAC =
  MAP_EVERY (fun (inp,sv) ->
    let t = rhs(concl(BETA_CONV
             (mk_comb(SHAKE256X4_ABSORBED,
                      mk_comb(`num_of_bytelist:byte list->num`,inp))))) in
    let len = ASSUME(mk_eq(mk_comb(`LENGTH:byte list->num`,inp),
                           `inlen:num`)) in
    ABBREV_TAC(mk_eq(sv,t)) THEN
    ASSUME_TAC(REWRITE_RULE[len; ASSUME(mk_eq(t,sv))]
                (SPEC inp SHAKE256X4_SPONGE)))
   (zip [`inp0:byte list`; `inp1:byte list`; `inp2:byte list`;
         `inp3:byte list`]
        [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`]);;

(*** The first rest bytes of the buffer at a, before the memcpy ***)

let SHAKE256X4_TMP_TAC a =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes",_),aa))),_)),_)
        when aa = mk_pair(a,`136`) ->
          ASSUME_TAC(MATCH_MP SHAKE256X4_TMP_LEMMA
                      (CONJ th (ASSUME `rest <= 136`)))
    | _ -> NO_TAC);;

(*** The intermediate points: after absorbing, after the whole blocks ***)

let SHAKE256X4_A1 = SHAKE256X4_AT
 `\s. read X20 s =
      word_add stackpointer
       (word(if aligned 32 stackpointer then 416 else 432)) /\
      read X22 s = out3 /\ read X23 s = out2 /\
      read X24 s = out1 /\ read X25 s = out0 /\
      read X26 s = word nb /\ read X27 s = word outlen /\
      read (memory :> bytes(word_add stackpointer
              (word(if aligned 32 stackpointer then 416 else 432)),200)) s =
      val(S0:1600 word) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 416 else 432) + 200)),
              200)) s =
      val(S1:1600 word) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 416 else 432) + 400)),
              200)) s =
      val(S2:1600 word) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 416 else 432) + 600)),
              200)) s =
      val(S3:1600 word)`;;

let SHAKE256X4_A2 = SHAKE256X4_AT
 `\s. read X20 s =
      word_add stackpointer
       (word(if aligned 32 stackpointer then 416 else 432)) /\
      read X22 s = out3 /\ read X23 s = out2 /\
      read X24 s = out1 /\ read X25 s = out0 /\
      read X26 s = word nb /\ read X27 s = word outlen /\
      read (memory :> bytes(out0,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp0) (136 * nb)) /\
      read (memory :> bytes(out1,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp1) (136 * nb)) /\
      read (memory :> bytes(out2,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp2) (136 * nb)) /\
      read (memory :> bytes(out3,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp3) (136 * nb)) /\
      read (memory :> bytes(word_add stackpointer
              (word(if aligned 32 stackpointer then 416 else 432)),200)) s =
      val(keccak_squeeze nb (S0:1600 word)) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 416 else 432) + 200)),
              200)) s =
      val(keccak_squeeze nb (S1:1600 word)) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 416 else 432) + 400)),
              200)) s =
      val(keccak_squeeze nb (S2:1600 word)) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 416 else 432) + 600)),
              200)) s =
      val(keccak_squeeze nb (S3:1600 word))`;;

(*** The loop invariant, with i blocks done ***)

let SHAKE256X4_INV = SHAKE256X4_AT
 `\i s. read X19 s = word(136 * i) /\ read X21 s = word(nb - i) /\
        read X20 s =
        word_add stackpointer
         (word(if aligned 32 stackpointer then 416 else 432)) /\
        read X22 s = out3 /\ read X23 s = out2 /\
        read X24 s = out1 /\ read X25 s = out0 /\
        read X26 s = word nb /\ read X27 s = word outlen /\
        read (memory :> bytes(out0,136 * i)) s =
        num_of_bytelist(list_of_seq (shake256 inp0) (136 * i)) /\
        read (memory :> bytes(out1,136 * i)) s =
        num_of_bytelist(list_of_seq (shake256 inp1) (136 * i)) /\
        read (memory :> bytes(out2,136 * i)) s =
        num_of_bytelist(list_of_seq (shake256 inp2) (136 * i)) /\
        read (memory :> bytes(out3,136 * i)) s =
        num_of_bytelist(list_of_seq (shake256 inp3) (136 * i)) /\
        read (memory :> bytes(word_add stackpointer
                (word(if aligned 32 stackpointer then 416 else 432)),200)) s =
        val(keccak_squeeze i (S0:1600 word)) /\
        read (memory :> bytes(word_add stackpointer
                (word((if aligned 32 stackpointer then 416 else 432) + 200)),
                200)) s =
        val(keccak_squeeze i (S1:1600 word)) /\
        read (memory :> bytes(word_add stackpointer
                (word((if aligned 32 stackpointer then 416 else 432) + 400)),
                200)) s =
        val(keccak_squeeze i (S2:1600 word)) /\
        read (memory :> bytes(word_add stackpointer
                (word((if aligned 32 stackpointer then 416 else 432) + 600)),
                200)) s =
        val(keccak_squeeze i (S3:1600 word))`;;

(*** After the remaining bytes, with the addresses of the buffers ***)

let SHAKE256X4_A3 = SHAKE256X4_AT
 `\s. read X20 s =
      word_add stackpointer
       (word(if aligned 32 stackpointer then 416 else 432)) /\
      read X28 s = word_add stackpointer (word 1240) /\
      read X26 s = word_add stackpointer (word 1376) /\
      read X27 s = word_add stackpointer (word 1512) /\
      read X21 s = word_add stackpointer (word 1648) /\
      read (memory :> bytes(out0,outlen)) s =
      num_of_bytelist(list_of_seq (shake256 inp0) outlen) /\
      read (memory :> bytes(out1,outlen)) s =
      num_of_bytelist(list_of_seq (shake256 inp1) outlen) /\
      read (memory :> bytes(out2,outlen)) s =
      num_of_bytelist(list_of_seq (shake256 inp2) outlen) /\
      read (memory :> bytes(out3,outlen)) s =
      num_of_bytelist(list_of_seq (shake256 inp3) outlen)`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy at the    *)
(* addresses mf and mc in the GOT entries at 0x1ffe8 and 0x1ffd0, with their *)
(* code and data in the region (ea,el). The inputs are four lists of bytes   *)
(* of the same length inlen, at in0, ..., in3, the last given on the stack   *)
(* with inlen, and the outlen bytes of each output, as a number, are the     *)
(* first outlen bytes of shake256 of the corresponding input. The stack is   *)
(* the 1488 bytes of the function and the 304 used by                        *)
(* mlk_keccak_absorb_once_x4 below them, and the two 8-byte stack arguments  *)
(* are just above it.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE256X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!out0 out1 out2 out3 outlen in0 in1 in2 in3 inlen
   (inp0:byte list) (inp1:byte list) (inp2:byte list) (inp3:byte list)
   guard mf mc ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        LENGTH inp0 = inlen /\ LENGTH inp1 = inlen /\
        LENGTH inp2 = inlen /\ LENGTH inp3 = inlen /\
        PAIRWISE nonoverlapping
         [(out0,outlen); (out1,outlen); (out2,outlen); (out3,outlen);
          (word_sub stackpointer (word 1792),1792)] /\
        ALLPAIRS nonoverlapping
         [(out0,outlen); (out1,outlen); (out2,outlen); (out3,outlen);
          (word_sub stackpointer (word 1792),1792)]
         [(in0,inlen); (in1,inlen); (in2,inlen); (in3,inlen);
          (stackpointer,16); (word pc,0x6480); (word(pc + 0x1fff8),8);
          (guard,8); (word(pc + 0x1ffe8),8); (word(pc + 0x1ffd0),8);
          (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x2a20) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS
                   [out0; out1; out2; out3; word outlen; in0; in1; in2] s /\
                  read (memory :> bytes64 stackpointer) s = in3 /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  word inlen /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                  read (memory :> bytes64(word(pc + 0x1ffd0))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(in0,inlen)) s = num_of_bytelist inp0 /\
                  read (memory :> bytes(in1,inlen)) s = num_of_bytelist inp1 /\
                  read (memory :> bytes(in2,inlen)) s = num_of_bytelist inp2 /\
                  read (memory :> bytes(in3,inlen)) s = num_of_bytelist inp3)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out0,outlen)) s =
                  num_of_bytelist(list_of_seq (shake256 inp0) outlen) /\
                  read (memory :> bytes(out1,outlen)) s =
                  num_of_bytelist(list_of_seq (shake256 inp1) outlen) /\
                  read (memory :> bytes(out2,outlen)) s =
                  num_of_bytelist(list_of_seq (shake256 inp2) outlen) /\
                  read (memory :> bytes(out3,outlen)) s =
                  num_of_bytelist(list_of_seq (shake256 inp3) outlen))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out0,outlen); memory :> bytes(out1,outlen);
                memory :> bytes(out2,outlen); memory :> bytes(out3,outlen);
                memory :> bytes(word_sub stackpointer (word 1792),1792)])`,
  MAP_EVERY X_GEN_TAC
   [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`; `outlen:num`;
    `in0:int64`; `in1:int64`; `in2:int64`; `in3:int64`; `inlen:num`;
    `inp0:byte list`; `inp1:byte list`; `inp2:byte list`; `inp3:byte list`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 1792 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (LABEL_TAC "H_MEMSET" o REWRITE_RULE[memset_contract])
   (CONJUNCTS_THEN2
    (LABEL_TAC "H_MEMCPY" o REWRITE_RULE[memcpy_contract])
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  SHAKE256X4_SETUP_TAC THEN SHAKE256X4_BOUND_TAC THEN
  SHAKE256X4_ABSORBED_TAC THEN

  (*** Zeroing the context with memset, and the absorption ***)

  ENSURES_SEQUENCE_TAC `pc + 0x2ab8` SHAKE256X4_A1 THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--2) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (3--9) THEN
    SHAKE256X4_CTX_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (10--29) THEN
    LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC 29 THEN
    LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC
     [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 34 THEN
    MEMSET_ZERO_BYTES_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (35--43) THEN
    SHAKE256X4_NBLOCKS_TAC THEN SHAKE256X4_GOT_TAC THEN
    LOCAL_ABSORB_X4_TAC
     [`read X0 s`; `136`; `read X2 s`; `read X3 s`; `read X4 s`;
      `read X5 s`; `inlen:num`; `num_of_bytelist(inp0:byte list)`;
      `num_of_bytelist(inp1:byte list)`; `num_of_bytelist(inp2:byte list)`;
      `num_of_bytelist(inp3:byte list)`; `guard:int64`; `pc:num`;
      `read SP s`; `read X30 s`] 44 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The whole blocks, in a loop unless there are none ***)

  ENSURES_SEQUENCE_TAC `pc + 0x2afc` SHAKE256X4_A2 THEN CONJ_TAC THENL
   [ASM_CASES_TAC `nb = 0` THENL
     [ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--2) THEN
      SHAKE256X4_LS_TAC `nb = 0` THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_TRIVIAL; list_of_seq;
                  num_of_bytelist; keccak_squeeze];
      ALL_TAC] THEN
    ENSURES_WHILE_UP2_TAC `nb:num` `pc + 0x2ac8` `pc + 0x2afc`
      SHAKE256X4_INV THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];

      (*** Initialization ***)

      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--2) THEN
      SHAKE256X4_LS_TAC `~(nb = 0)` THEN
      ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (3--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MULT_CLAUSES; SUB_0; READ_MEMORY_BYTES_TRIVIAL;
                  list_of_seq; num_of_bytelist; keccak_squeeze];

      (*** The loop body: permute, extract a block of each, the test ***)

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `136 * i + 136 <= outlen` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i < nb`; `136 * nb + rest = outlen`] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--2) THEN
      SHAKE256X4_STATES_TAC THEN
      LOCAL_PERMUTE_X4_TAC
       [`read X0 s`; `keccak_squeeze i (S0:1600 word)`;
        `keccak_squeeze i (S1:1600 word)`;
        `keccak_squeeze i (S2:1600 word)`;
        `keccak_squeeze i (S3:1600 word)`; `pc:num`; `read SP s`;
        `read X30 s`] 3 THEN
      RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
      ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (4--11) THEN
      SHAKE256X4_STATES_TAC THEN
      LOCAL_EXTRACT_X4_TAC
       [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
        `0`; `136`; `keccak_f1600(keccak_squeeze i (S0:1600 word))`;
        `keccak_f1600(keccak_squeeze i (S1:1600 word))`;
        `keccak_f1600(keccak_squeeze i (S2:1600 word))`;
        `keccak_f1600(keccak_squeeze i (S3:1600 word))`; `pc:num`;
        `read SP s`; `read X30 s`] 12 THEN
      ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (13--15) THEN
      SHAKE256X4_COUNTER_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN
      TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
      TRY(REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
          REWRITE_TAC[ARITH_RULE `136 * (i + 1) = 136 * i + 136`] THEN
          NO_TAC) THEN
      TRY(REWRITE_TAC[GSYM ADD1; keccak_squeeze] THEN NO_TAC) THEN
      REWRITE_TAC[ARITH_RULE `136 * (i + 1) = 136 * i + 136`] THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[LE_REFL] THEN
      REWRITE_TAC[GSYM ADD1; keccak_squeeze; MULT_CLAUSES; EXP; DIV_1];

      (*** The exit from the loop ***)

      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN

  (*** The remaining bytes, if any, through the buffers on the stack ***)

  ENSURES_SEQUENCE_TAC `pc + 0x2b28` SHAKE256X4_A3 THEN CONJ_TAC THENL
   [ASM_CASES_TAC `rest = 0` THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--4) THEN
    SHAKE256X4_NBLOCKS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (5--6) THEN
    SHAKE256X4_REST_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (7--7) THENL
     [SHAKE256X4_BRANCH_TAC TRUTH `rest = 0` THEN
      ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (8--11) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `outlen = 136 * nb` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`rest = 0`; `136 * nb + rest = outlen`] THEN
        ARITH_TAC;
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN

    (*** Otherwise one more block into the buffers, and the memcpys ***)

    SHAKE256X4_BRANCH_TAC TRUTH `~(rest = 0)` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (8--16) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SHAKE256X4_MUL136]) THEN
    SHAKE256X4_STATES_TAC THEN
    LOCAL_PERMUTE_X4_TAC
     [`read X0 s`; `keccak_squeeze nb (S0:1600 word)`;
      `keccak_squeeze nb (S1:1600 word)`; `keccak_squeeze nb (S2:1600 word)`;
      `keccak_squeeze nb (S3:1600 word)`; `pc:num`; `read SP s`;
      `read X30 s`] 17 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (18--25) THEN
    SHAKE256X4_STATES_TAC THEN
    LOCAL_EXTRACT_X4_TAC
     [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`; `0`;
      `136`; `keccak_f1600(keccak_squeeze nb (S0:1600 word))`;
      `keccak_f1600(keccak_squeeze nb (S1:1600 word))`;
      `keccak_f1600(keccak_squeeze nb (S2:1600 word))`;
      `keccak_f1600(keccak_squeeze nb (S3:1600 word))`; `pc:num`;
      `read SP s`; `read X30 s`] 26 THEN
    MAP_EVERY (fun (a,sv,k0,k) ->
      SHAKE256X4_TMP_TAC a THEN
      ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (k0--k) THEN
      LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC k THEN
      LIBC_CALL_TAC "H_MEMCPY" MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC
       [`read X0 s`; `read X1 s`; `read X2 s`;
        vsubst [sv,`S:1600 word`]
         `val(keccak_f1600(keccak_squeeze nb (S:1600 word))) MOD
          2 EXP (8 * rest)`;
        `read X30 s`] (k + 5))
     [`word_add (stackpointer:int64) (word 1240)`,`S0:1600 word`,27,31;
      `word_add (stackpointer:int64) (word 1376)`,`S1:1600 word`,37,41;
      `word_add (stackpointer:int64) (word 1512)`,`S2:1600 word`,47,50;
      `word_add (stackpointer:int64) (word 1648)`,`S3:1600 word`,56,59] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (65--65) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `outlen = 136 * nb + rest` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE;
                NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM ADD1; keccak_squeeze];
    ALL_TAC] THEN

  (*** Zeroing the context and the buffers, the stack guard, the return ***)

  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--4) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC 4 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 9 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (10--31) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (32--45) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contracts for memset and memcpy. The events depend on the address of the  *)
(* stack guard and on the input in3 given on the stack, and the number of    *)
(* iterations of the loop and whether there is a remainder depend on outlen. *)
(* The events are split at the intermediate points of the correctness proof, *)
(* from the end, with the public parts of the same assertions, and when the  *)
(* events so far consist of several parts they are kept as a variable e2 in  *)
(* the simulation.                                                           *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let SHAKE256X4_F_EVENTS =
 `\(in0:int64) (in1:int64) (in2:int64) (in3:int64)
   (out0:int64) (out1:int64) (out2:int64) (out3:int64) (outlen:num)
   (inlen:num) (guard:int64) (mf:int64) (mc:int64) (pc:num)
   (stackpointer:int64) (returnaddress:int64).
   APPEND
    (f_ev_end in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen guard mf mc
              pc stackpointer returnaddress)
    (APPEND
      (if outlen MOD 136 = 0
       then f_ev_rest0 in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen
                       guard mf mc pc stackpointer returnaddress
       else f_ev_rest in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen guard
                      mf mc pc stackpointer returnaddress)
      (APPEND
        (if outlen DIV 136 = 0
         then f_ev_skip in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen
                        guard mf mc pc stackpointer returnaddress
         else APPEND
               (f_ev_epil in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen
                          guard mf mc pc stackpointer returnaddress)
               (APPEND
                 (ENUMERATEL (outlen DIV 136)
                   (\i. f_ev_loop in0 in1 in2 in3 out0 out1 out2 out3 outlen
                                  inlen guard mf mc pc stackpointer
                                  returnaddress i))
                 (f_ev_prol in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen
                            guard mf mc pc stackpointer returnaddress)))
        (f_ev_absorb in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen guard
                     mf mc pc stackpointer returnaddress)))
   :(uarch_event)list`;;

let SHAKE256X4_PUBLIC t =
  let vs,bod = strip_abs t
  and priv = [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
              `S3:1600 word`; `inp0:byte list`; `inp1:byte list`;
              `inp2:byte list`; `inp3:byte list`] in
  list_mk_abs(vs,list_mk_conj
   (filter (fun c -> not(exists (fun v -> vfree_in v c) priv))
           (conjuncts bod)));;

let SHAKE256X4_ALLOWED =
  [`pc:num`; `in0:int64`; `in1:int64`; `in2:int64`; `in3:int64`;
   `out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`; `outlen:num`;
   `inlen:num`; `guard:int64`; `mf:int64`; `mc:int64`;
   `stackpointer:int64`; `returnaddress:int64`; `i:num`;
   `e2:(uarch_event)list`];;

(*** EXISTS_E2_TAC with nb and rest expanded, allowing the f_ev_... ***)

let SHAKE256X4_EXISTS_E2_TAC =
  let pfx = ref ["f_events_callee"; "f_ev_"] in
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if c = `outlen DIV 136 = nb` || c = `outlen MOD 136 = rest`
      then SYM th else failwith "") asl in
    if ths = [] then ALL_TAC else REWRITE_TAC ths) THEN
  ((MATCH_MP_TAC NIL_IMPLIES_APPEND_EQ THEN CONJ_TAC THENL
     [REFL_TAC; SAFE_UNIFY_REFL_TAC (ref SHAKE256X4_ALLOWED) pfx]) ORELSE
   (CONV_TAC(TRY_CONV(LAND_CONV CONS_TO_APPEND_CONV)) THEN
    TRY(GEN_REWRITE_TAC LAND_CONV [APPEND_ASSOC]) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SAFE_UNIFY_REFL_TAC (ref SHAKE256X4_ALLOWED) pfx) ORELSE
   (CONV_TAC(TRY_CONV(LAND_CONV(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
    CONV_TAC(TRY_CONV(LAND_CONV(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
    GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV) [APPEND_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SAFE_UNIFY_REFL_TAC (ref SHAKE256X4_ALLOWED) pfx));;

let SHAKE256X4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [SHAKE256X4_EXISTS_E2_TAC; LABEL_TAC name safety_th]);;

let SHAKE256X4_LIBC_SAFE_CALL_TAC name n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true
      MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC th
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `read X30 s`] n THENL
     [SHAKE256X4_EXISTS_E2_TAC; LABEL_TAC name th]);;

(*** The start of a part, where the events e2 so far may be given ***)

let SHAKE256X4_SAFE_INIT_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC;;

(*** The same keeping e2 as a variable, when given in several parts ***)

let SHAKE256X4_SAFE_INIT_OPAQUE_TAC =
  SHAKE256X4_SAFE_INIT_TAC THEN
  TRY(FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if is_var l && name_of l = "e2" && not(is_var r)
    then ASSUME_TAC(SYM th) THEN PURE_REWRITE_TAC[SYM th]
    else NO_TAC));;

(*** The final step of a part, with nb and rest expanded in the events, ***)
(*** and if needed the events reassociated to the right                ***)

let SHAKE256X4_UNABBREV_TAC =
  MAP_EVERY (fun t ->
    TRY(FIRST_X_ASSUM(fun th ->
      if concl th = t then SUBST_ALL_TAC(SYM th) else NO_TAC)))
   [`outlen DIV 136 = nb`; `outlen MOD 136 = rest`];;

let SHAKE256X4_DISCHARGE_TAC =
  SHAKE256X4_UNABBREV_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let SHAKE256X4_DISCHARGE_ASSOC_TAC =
  SHAKE256X4_UNABBREV_TAC THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; APPEND_NIL] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(*** Zeroing the context and the absorption ***)

let SHAKE256X4_SAFE_ABSORB_TAC =
  SHAKE256X4_SAFE_INIT_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--2) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (3--9) THEN
  SHAKE256X4_CTX_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (10--29) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC 29 THEN
  SHAKE256X4_LIBC_SAFE_CALL_TAC "H_MEMSET" 34 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (35--43) THEN
  SHAKE256X4_NBLOCKS_TAC THEN SHAKE256X4_GOT_TAC THEN
  SHAKE256X4_SAFE_CALL_TAC "H_ABSORB"
   [`e:(uarch_event)list`; `read X0 s`; `136`; `read X2 s`; `read X3 s`;
    `read X4 s`; `read X5 s`; `inlen:num`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 44 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_DISCHARGE_TAC;;

(*** The whole blocks ***)

let SHAKE256X4_SAFE_BLOCKS_TAC =
  ASM_CASES_TAC `nb = 0` THEN ASM_REWRITE_TAC[] THENL
   [SHAKE256X4_SAFE_INIT_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--2) THEN
    SHAKE256X4_LS_TAC `nb = 0` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SHAKE256X4_DISCHARGE_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `nb:num` `pc + 0x2ac8` `pc + 0x2afc`
    (SHAKE256X4_PUBLIC SHAKE256X4_INV) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    SHAKE256X4_SAFE_INIT_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--2) THEN
    SHAKE256X4_LS_TAC `~(nb = 0)` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (3--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0] THEN
    SHAKE256X4_DISCHARGE_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SHAKE256X4_SAFE_INIT_TAC THEN
    SUBGOAL_THEN `136 * i + 136 <= outlen` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`i < nb`; `136 * nb + rest = outlen`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--2) THEN
    SHAKE256X4_SAFE_CALL_TAC "H_PERMUTE"
     [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
      `read X30 s`] 3 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (4--11) THEN
    SHAKE256X4_SAFE_CALL_TAC "H_EXTRACT"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
      `read X3 s`; `read X4 s`; `0`; `136`; `pc:num`; `read SP s`;
      `read X30 s`] 12 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (13--15) THEN
    SHAKE256X4_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      REWRITE_TAC[ARITH_RULE `136 * (i + 1) = 136 * i + 136`];
      ALL_TAC] THEN
    SHAKE256X4_DISCHARGE_TAC;

    REWRITE_TAC[] THEN SHAKE256X4_SAFE_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SHAKE256X4_DISCHARGE_TAC];;

(*** The remaining bytes ***)

let SHAKE256X4_SAFE_REST_TAC =
  ASM_CASES_TAC `rest = 0` THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_SAFE_INIT_OPAQUE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--4) THEN
  SHAKE256X4_NBLOCKS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (5--6) THEN
  SHAKE256X4_REST_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (7--7) THENL
   [SHAKE256X4_BRANCH_TAC TRUTH `rest = 0` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (8--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SHAKE256X4_DISCHARGE_TAC;
    ALL_TAC] THEN
  SHAKE256X4_BRANCH_TAC TRUTH `~(rest = 0)` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (8--16) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SHAKE256X4_MUL136]) THEN
  SHAKE256X4_SAFE_CALL_TAC "H_PERMUTE"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
    `read X30 s`] 17 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (18--25) THEN
  SHAKE256X4_SAFE_CALL_TAC "H_EXTRACT"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `read X4 s`; `0`; `136`; `pc:num`; `read SP s`;
    `read X30 s`] 26 THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (k0--k) THEN
    LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC k THEN
    SHAKE256X4_LIBC_SAFE_CALL_TAC "H_MEMCPY" (k + 5))
   [27,31; 37,41; 47,50; 56,59] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (65--65) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_DISCHARGE_ASSOC_TAC;;

(*** Zeroing, the stack guard and the return ***)

let SHAKE256X4_SAFE_END_TAC =
  SHAKE256X4_SAFE_INIT_OPAQUE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (1--4) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC 4 THEN
  SHAKE256X4_LIBC_SAFE_CALL_TAC "H_MEMSET" 9 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (10--31) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC (32--45) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_DISCHARGE_TAC;;

let MLKEM_NATIVE_SHAKE256X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`!mf mc ea el ev.
     memset_safety_contract mf ea el ev /\
     memcpy_safety_contract mc ea el ev
     ==> exists f_events.
          forall e out0 out1 out2 out3 outlen in0 in1 in2 in3 inlen guard
                 pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
            [out0,outlen; out1,outlen; out2,outlen; out3,outlen;
             word_sub stackpointer (word 1792),1792] /\
           ALLPAIRS nonoverlapping
            [out0,outlen; out1,outlen; out2,outlen; out3,outlen;
             word_sub stackpointer (word 1792),1792]
            [in0,inlen; in1,inlen; in2,inlen; in3,inlen; stackpointer,16;
             word pc,0x6480; word(pc + 0x1fff8),8; guard,8;
             word(pc + 0x1ffe8),8; word(pc + 0x1ffd0),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_native_libmlkem_gcc12_O2_mc /\
                     read PC s = word (pc + 0x2a20) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS
                      [out0; out1; out2; out3; word outlen; in0; in1; in2] s /\
                     read (memory :> bytes64 stackpointer) s = in3 /\
                     read (memory :> bytes64(word_add stackpointer (word 8)))
                          s =
                     word inlen /\
                     read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                     read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                     read (memory :> bytes64(word(pc + 0x1ffd0))) s = mc /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events in0 in1 in2 in3 out0 out1 out2 out3
                               outlen inlen guard mf mc pc
                               (word_sub stackpointer (word 1792))
                               returnaddress /\
                        memaccess_inbounds e2
                         [in0,inlen; in1,inlen; in2,inlen; in3,inlen;
                          out0,outlen; out1,outlen; out2,outlen; out3,outlen;
                          stackpointer,16;
                          word_sub stackpointer (word 1792),1792;
                          word(pc + 0x1fff8),8; guard,8;
                          word(pc + 0x62b0),192; word(pc + 0x1ffe8),8;
                          word(pc + 0x1ffd0),8; ea,el]
                         [out0,outlen; out1,outlen; out2,outlen; out3,outlen;
                          word_sub stackpointer (word 1792),1792]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(out0,outlen); memory :> bytes(out1,outlen);
                   memory :> bytes(out2,outlen); memory :> bytes(out3,outlen);
                   memory :> bytes(word_sub stackpointer (word 1792),1792)])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[memset_safety_contract; memcpy_safety_contract] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMSET")
   (fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMCPY")) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_EXTRACT" THEN
  CONCRETIZE_F_EVENTS_TAC SHAKE256X4_F_EVENTS THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_SHAKE256X4_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SHAKE256X4_SETUP_TAC THEN SHAKE256X4_BOUND_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x2b28`
   (SHAKE256X4_PUBLIC SHAKE256X4_A3) THEN
  CONJ_TAC THENL [ALL_TAC; SHAKE256X4_SAFE_END_TAC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x2afc`
   (SHAKE256X4_PUBLIC SHAKE256X4_A2) THEN
  CONJ_TAC THENL [ALL_TAC; SHAKE256X4_SAFE_REST_TAC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x2ab8`
   (SHAKE256X4_PUBLIC SHAKE256X4_A1) THEN
  CONJ_TAC THENL [SHAKE256X4_SAFE_ABSORB_TAC; SHAKE256X4_SAFE_BLOCKS_TAC]);;
