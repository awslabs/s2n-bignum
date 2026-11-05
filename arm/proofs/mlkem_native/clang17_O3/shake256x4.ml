(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 of four inputs of the same length, with four outputs of any      *)
(* length. This is the code for mlkem_shake256x4 from mlkem-native's         *)
(* portable C implementation compiled by clang 17 with -O3 (see              *)
(* mlkem_native/README.md), which zeroes a context of four states on the     *)
(* stack with memset, absorbs the inputs into it with                        *)
(* mlk_keccak_absorb_once_x4, squeezes the whole blocks of 136 bytes, the    *)
(* rate of SHAKE256, directly into the outputs, and the rest of the outputs  *)
(* through four buffers on the stack with memcpy, before zeroing the context *)
(* with memset and the buffers. It is verified in the whole image (see       *)
(* libmlkem.ml), using the theorems for                                      *)
(* mlk_keccak_absorb_once_x4, mlkem_keccakf1600x4_permute and                *)
(* mlkem_keccakf1600x4_extract_bytes in the image and assuming the contracts *)
(* for memset and memcpy in utils/mlkem_native_libc.ml. The result is        *)
(* shake256 of common/fips202.ml for each input.                             *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/keccak_absorb_once_x4.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/keccakf1600x4_permute.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/keccakf1600x4_extract_bytes.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image, and the PLT stubs for memcpy and memset:

    mlkem_shake256x4:
      +0x0: stp     x29, x30, [sp, #-96]!
      +0x4: stp     x28, x27, [sp, #16]
      +0x8: stp     x26, x25, [sp, #32]
      +0xc: stp     x24, x23, [sp, #48]
     +0x10: stp     x22, x21, [sp, #64]
     +0x14: stp     x20, x19, [sp, #80]
     +0x18: mov     x29, sp
     +0x1c: sub     x9, sp, #0x5a0
     +0x20: and     sp, x9, #0xffffffffffffffe0
     +0x24: adrp    x9, <page>
     +0x28: str     x2, [sp, #24]
     +0x2c: mov     x8, #0xf0f0f0f0f0f0f0f0
     +0x30: mov     x22, x1
     +0x34: movk    x8, #0xf0f1
     +0x38: mov     x20, x0
     +0x3c: ldr     x9, [x9, #4088]  // got_stack_chk_guard
     +0x40: add     x0, sp, #0x260
     +0x44: ldp     x27, x28, [x29, #96]
     +0x48: mov     w1, wzr
     +0x4c: mov     w2, #0x320
     +0x50: ldr     x9, [x9]
     +0x54: umulh   x8, x4, x8
     +0x58: mov     x24, x7
     +0x5c: mov     x25, x6
     +0x60: mov     x23, x4
     +0x64: mov     x26, x5
     +0x68: mov     x21, x3
     +0x6c: lsr     x19, x8, #7
     +0x70: str     x9, [sp, #1432]
     +0x74: bl      memset
     +0x78: add     x0, sp, #0x260
     +0x7c: mov     w1, #0x88
     +0x80: mov     x2, x26
     +0x84: mov     x3, x25
     +0x88: mov     x4, x24
     +0x8c: mov     x5, x27
     +0x90: mov     x6, x28
     +0x94: bl      mlk_keccak_absorb_once_x4
     +0x98: cmp     x23, #0x88
     +0x9c: b.cc    join1
     +0xa0: mov     x24, x20
     +0xa4: mov     x25, x22
     +0xa8: ldr     x26, [sp, #24]
     +0xac: mov     x27, x21
     +0xb0: mov     x28, x19
     +0xb4: add     x0, sp, #0x260
     +0xb8: bl      mlkem_keccakf1600x4_permute
     +0xbc: add     x0, sp, #0x260
     +0xc0: mov     x1, x24
     +0xc4: mov     x2, x25
     +0xc8: mov     x3, x26
     +0xcc: mov     x4, x27
     +0xd0: mov     w5, wzr
     +0xd4: mov     w6, #0x88
     +0xd8: bl      mlkem_keccakf1600x4_extract_bytes
     +0xdc: subs    x28, x28, #0x1
     +0xe0: add     x27, x27, #0x88
     +0xe4: add     x26, x26, #0x88
     +0xe8: add     x25, x25, #0x88
     +0xec: add     x24, x24, #0x88
     +0xf0: b.ne    loop1
     +0xf4: add     x8, x19, x19, lsl #4
     +0xf8: lsl     x24, x8, #3
     +0xfc: subs    x23, x23, x24
    +0x100: b.eq    join2
    +0x104: add     x0, sp, #0x260
    +0x108: add     x21, x21, x24
    +0x10c: add     x22, x22, x24
    +0x110: bl      mlkem_keccakf1600x4_permute
    +0x114: add     x0, sp, #0x260
    +0x118: add     x1, sp, #0x1d0
    +0x11c: add     x2, sp, #0x140
    +0x120: add     x3, sp, #0xb0
    +0x124: add     x4, sp, #0x20
    +0x128: mov     w5, wzr
    +0x12c: mov     w6, #0x88
    +0x130: bl      mlkem_keccakf1600x4_extract_bytes
    +0x134: ldr     x8, [sp, #24]
    +0x138: add     x0, x20, x24
    +0x13c: add     x1, sp, #0x1d0
    +0x140: mov     x2, x23
    +0x144: add     x19, x8, x24
    +0x148: bl      memcpy
    +0x14c: add     x1, sp, #0x140
    +0x150: mov     x0, x22
    +0x154: mov     x2, x23
    +0x158: bl      memcpy
    +0x15c: add     x1, sp, #0xb0
    +0x160: mov     x0, x19
    +0x164: mov     x2, x23
    +0x168: bl      memcpy
    +0x16c: add     x1, sp, #0x20
    +0x170: mov     x0, x21
    +0x174: mov     x2, x23
    +0x178: bl      memcpy
    +0x17c: add     x0, sp, #0x260
    +0x180: mov     w1, wzr
    +0x184: mov     w2, #0x320
    +0x188: add     x19, sp, #0x260
    +0x18c: bl      memset
    +0x190: movi    v0.2d, #0x0
    +0x194: str     xzr, [sp, #592]
    +0x198: add     x8, sp, #0x1d0
    +0x19c: stp     q0, q0, [sp, #464]
    +0x1a0: stp     q0, q0, [sp, #496]
    +0x1a4: stp     q0, q0, [sp, #528]
    +0x1a8: stp     q0, q0, [sp, #560]
    +0x1ac: str     xzr, [sp, #448]
    +0x1b0: stp     q0, q0, [sp, #352]
    +0x1b4: add     x8, sp, #0x140
    +0x1b8: stp     q0, q0, [sp, #320]
    +0x1bc: stp     q0, q0, [sp, #384]
    +0x1c0: stp     q0, q0, [sp, #416]
    +0x1c4: str     xzr, [sp, #304]
    +0x1c8: stp     q0, q0, [sp, #208]
    +0x1cc: add     x8, sp, #0xb0
    +0x1d0: stp     q0, q0, [sp, #176]
    +0x1d4: stp     q0, q0, [sp, #240]
    +0x1d8: stp     q0, q0, [sp, #272]
    +0x1dc: str     xzr, [sp, #160]
    +0x1e0: stp     q0, q0, [sp, #64]
    +0x1e4: add     x8, sp, #0x20
    +0x1e8: stp     q0, q0, [sp, #32]
    +0x1ec: stp     q0, q0, [sp, #96]
    +0x1f0: stp     q0, q0, [sp, #128]
    +0x1f4: adrp    x8, <page>
    +0x1f8: ldr     x8, [x8, #4088]  // got_stack_chk_guard
    +0x1fc: ldr     x9, [sp, #1432]
    +0x200: ldr     x8, [x8]
    +0x204: cmp     x8, x9
    +0x208: b.ne    +0x22c
    +0x20c: mov     sp, x29
    +0x210: ldp     x20, x19, [sp, #80]
    +0x214: ldp     x22, x21, [sp, #64]
    +0x218: ldp     x24, x23, [sp, #48]
    +0x21c: ldp     x26, x25, [sp, #32]
    +0x220: ldp     x28, x27, [sp, #16]
    +0x224: ldp     x29, x30, [sp], #96
    +0x228: ret
    +0x22c: bl      stack_chk_fail

    memcpy@plt:
      +0x0: adrp    x16, <page>
      +0x4: ldr     x17, [x16, #4048]  // got_memcpy
      +0x8: add     x16, x16, #0xfd0  // got_memcpy
      +0xc: br      x17

    memset@plt:
      +0x0: adrp    x16, <page>
      +0x4: ldr     x17, [x16, #4072]  // got_memset
      +0x8: add     x16, x16, #0xfe8  // got_memset
      +0xc: br      x17
 ***)

let MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_shake256x4"; layout_range "plt_memcpy";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* The frame is aligned to 32 bytes: after saving 12 registers in the top 96 *)
(* bytes, with the frame pointer X29 pointing to them, the code subtracts    *)
(* 1440 from the stack pointer and clears its low 5 bits. So the stack       *)
(* pointer in the body is 320 or 336 bytes above the bottom of the 1872      *)
(* bytes used, depending on whether the stack pointer on entry is a multiple *)
(* of 32 or just of 16, and the 320 bytes below it are those used by         *)
(* mlk_keccak_absorb_once_x4. The frame is addressed from that stack         *)
(* pointer: out2 at 24, the four buffers at 464, 320, 176 and 32 (for out0,  *)
(* ..., out3), the context at 608 with the states at 608, 808, 1008 and      *)
(* 1208, and the stack guard at 1432. In the terms below b stands for the    *)
(* offset of the stack pointer, if aligned 32 stackpointer then 320 else     *)
(* 336, with stackpointer the bottom of the 1872 bytes.                      *)
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

let SHAKE256X4_SP_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 336)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 320 else 336))`,
  REWRITE_TAC[SHAKE256X4_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let SHAKE256X4_B = `if aligned 32 (stackpointer:int64) then 320 else 336`;;

let SHAKE256X4_SUBST = vsubst [SHAKE256X4_B,`b:num`];;

let SHAKE256X4_SP_TAC =
  SUBGOAL_THEN
   (SHAKE256X4_SUBST
     `word_and (word_add stackpointer (word 336))
               (word 18446744073709551584):int64 =
      word_add stackpointer (word b)`)
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC SHAKE256X4_SP_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let SHAKE256X4_ST = map SHAKE256X4_SUBST
  [`word_add stackpointer (word(b + 608)):int64`;
   `word_add stackpointer (word((b + 608) + 200)):int64`;
   `word_add stackpointer (word((b + 608) + 400)):int64`;
   `word_add stackpointer (word((b + 608) + 600)):int64`];;

let SHAKE256X4_STATES_TAC = MAP_EVERY KECCAK_STATE_AT_TAC SHAKE256X4_ST;;

(*** Addresses computed from the stack pointer, such as the argument of  ***)
(*** add x0, sp, #0x260, are word_add (word_add stackpointer (word b))  ***)
(*** (word 608) in the registers, normalized to word(b + 608) as in the ***)
(*** addresses of the memory accesses, but not in the events           ***)

let SHAKE256X4_WORD_ADD_ADD = prove
 (`!a:int64 m n. word_add (word_add a (word m)) (word n) =
                 word_add a (word(m + n))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

let SHAKE256X4_NORM_TAC =
  RULE_ASSUM_TAC(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(c,_)),_)),_)
        when c <> "events" -> REWRITE_RULE[SHAKE256X4_WORD_ADD_ADD] th
    | _ -> th);;

(*** The regions of the callees below the stack pointer, as word(b - n) ***)

let SHAKE256X4_BELOW =
  map (fun n -> SHAKE256X4_SUBST
         (subst [n,`n:num`] `word_sub (word b) (word n):int64 = word(b - n)`))
      [`320`; `224`];;

let SHAKE256X4_FIX_TAC =
  RULE_ASSUM_TAC(fun th ->
    if maychange_term (concl th)
    then REWRITE_RULE (map ASSUME SHAKE256X4_BELOW) th else th);;

(* ------------------------------------------------------------------------- *)
(* The number of whole blocks, outlen DIV 136, is computed by multiplying by *)
(* a constant (umulh and lsr), and multiplied back by 136 with shifts, to    *)
(* get the number of remaining bytes, outlen MOD 136. The loop is skipped    *)
(* if outlen < 136, that is if there are no whole blocks.                    *)
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

(*** The bound on outlen, nb whole blocks and rest remaining bytes ***)

let SHAKE256X4_BOUND_TAC =
  SUBGOAL_THEN `outlen < 2 EXP 64` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1872 + n <= 2 EXP 64 ==> n < 2 EXP 64`) THEN
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
    ALL_TAC] THEN
  SUBGOAL_THEN `(outlen < 136 <=> nb = 0) /\ (136 <= outlen <=> ~(nb = 0))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`136 * nb + rest = outlen`; `rest < 136`] THEN
    ARITH_TAC;
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

let SHAKE256X4_CC_TAC tm =
  SHAKE256X4_BRANCH_TAC
   (CONJ (ASSUME `val(word outlen:int64) = outlen`)
     (CONJ (ASSUME `outlen < 136 <=> nb = 0`)
           (ASSUME `136 <= outlen <=> ~(nb = 0)`))) tm;;

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
(* intermediate points: the stack pointer, the frame pointer, the saved      *)
(* registers, the stack guard and the GOT.                                   *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 1872):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN (SHAKE256X4_SUBST `320 <= b /\ b <= 336`) STRIP_ASSUME_TAC
  THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   (SHAKE256X4_SUBST `aligned 16 (word_add (stackpointer:int64) (word b))`)
  ASSUME_TAC THENL
   [COND_CASES_TAC THEN CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun t ->
    SUBGOAL_THEN t ASSUME_TAC THENL
     [MATCH_MP_TAC WORD_SUB2 THEN COND_CASES_TAC THEN ARITH_TAC; ALL_TAC])
   SHAKE256X4_BELOW THEN
  SUBGOAL_THEN
   (SHAKE256X4_SUBST `b - 320 <= 16 /\ b - 224 <= 112`) STRIP_ASSUME_TAC
  THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--29);;

let SHAKE256X4_GOT_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes64 (word_add (word pc)
                                    (word got_stack_chk_guard))) s =
          g:int64`)
         (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC);;

let SHAKE256X4_FRAME =
 `read SP s = word_add stackpointer (word b) /\
  read X29 s = word_add stackpointer (word 1776) /\
  read (memory :> bytes64 (word_add stackpointer (word 1776))) s = x29_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1784))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 1792))) s = x28_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1800))) s = x27_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1808))) s = x26_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1816))) s = x25_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1824))) s = x24_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1832))) s = x23_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1840))) s = x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1848))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1856))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1864))) s = x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word(b + 1432)))) s =
  canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
  guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
  read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s = mc /\
  read (memory :> bytes(ea,el)) s = ev`;;

let SHAKE256X4_AT t =
  let vs,bod = strip_abs t in
  SHAKE256X4_SUBST(list_mk_abs(vs,mk_conj(bod,SHAKE256X4_FRAME)));;

(*** The subroutines ***)

let LOCAL_ABSORB_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_PERMUTE_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
 MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_F1600);;

let LOCAL_EXTRACT_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
 MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

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

(*** The intermediate points: after absorbing, at the loop and after it ***)

let SHAKE256X4_A1 = SHAKE256X4_AT
 `\s. read X19 s = word nb /\ read X20 s = out0 /\ read X21 s = out3 /\
      read X22 s = out1 /\ read X23 s = word outlen /\
      read (memory :> bytes64 (word_add stackpointer (word(b + 24)))) s =
      out2 /\
      read (memory :> bytes(word_add stackpointer (word(b + 608)),200)) s =
      val(S0:1600 word) /\
      read (memory :> bytes(word_add stackpointer
                             (word((b + 608) + 200)),200)) s =
      val(S1:1600 word) /\
      read (memory :> bytes(word_add stackpointer
                             (word((b + 608) + 400)),200)) s =
      val(S2:1600 word) /\
      read (memory :> bytes(word_add stackpointer
                             (word((b + 608) + 600)),200)) s =
      val(S3:1600 word)`;;

let SHAKE256X4_A2 = SHAKE256X4_AT
 `\s. read X19 s = word nb /\ read X20 s = out0 /\ read X21 s = out3 /\
      read X22 s = out1 /\ read X23 s = word outlen /\
      read (memory :> bytes64 (word_add stackpointer (word(b + 24)))) s =
      out2 /\
      read (memory :> bytes(out0,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp0) (136 * nb)) /\
      read (memory :> bytes(out1,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp1) (136 * nb)) /\
      read (memory :> bytes(out2,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp2) (136 * nb)) /\
      read (memory :> bytes(out3,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp3) (136 * nb)) /\
      read (memory :> bytes(word_add stackpointer (word(b + 608)),200)) s =
      val(keccak_squeeze nb (S0:1600 word)) /\
      read (memory :> bytes(word_add stackpointer
                             (word((b + 608) + 200)),200)) s =
      val(keccak_squeeze nb (S1:1600 word)) /\
      read (memory :> bytes(word_add stackpointer
                             (word((b + 608) + 400)),200)) s =
      val(keccak_squeeze nb (S2:1600 word)) /\
      read (memory :> bytes(word_add stackpointer
                             (word((b + 608) + 600)),200)) s =
      val(keccak_squeeze nb (S3:1600 word))`;;

(*** The loop invariant, with i blocks done ***)

let SHAKE256X4_INV = SHAKE256X4_AT
 `\i s. read X24 s = word_add out0 (word(136 * i)) /\
        read X25 s = word_add out1 (word(136 * i)) /\
        read X26 s = word_add out2 (word(136 * i)) /\
        read X27 s = word_add out3 (word(136 * i)) /\
        read X28 s = word(nb - i) /\
        read X19 s = word nb /\ read X20 s = out0 /\ read X21 s = out3 /\
        read X22 s = out1 /\ read X23 s = word outlen /\
        read (memory :> bytes64 (word_add stackpointer (word(b + 24)))) s =
        out2 /\
        read (memory :> bytes(out0,136 * i)) s =
        num_of_bytelist(list_of_seq (shake256 inp0) (136 * i)) /\
        read (memory :> bytes(out1,136 * i)) s =
        num_of_bytelist(list_of_seq (shake256 inp1) (136 * i)) /\
        read (memory :> bytes(out2,136 * i)) s =
        num_of_bytelist(list_of_seq (shake256 inp2) (136 * i)) /\
        read (memory :> bytes(out3,136 * i)) s =
        num_of_bytelist(list_of_seq (shake256 inp3) (136 * i)) /\
        read (memory :> bytes(word_add stackpointer (word(b + 608)),200)) s =
        val(keccak_squeeze i (S0:1600 word)) /\
        read (memory :> bytes(word_add stackpointer
                               (word((b + 608) + 200)),200)) s =
        val(keccak_squeeze i (S1:1600 word)) /\
        read (memory :> bytes(word_add stackpointer
                               (word((b + 608) + 400)),200)) s =
        val(keccak_squeeze i (S2:1600 word)) /\
        read (memory :> bytes(word_add stackpointer
                               (word((b + 608) + 600)),200)) s =
        val(keccak_squeeze i (S3:1600 word))`;;

(*** After the remaining bytes ***)

let SHAKE256X4_A3 = SHAKE256X4_AT
 `\s. read (memory :> bytes(out0,outlen)) s =
      num_of_bytelist(list_of_seq (shake256 inp0) outlen) /\
      read (memory :> bytes(out1,outlen)) s =
      num_of_bytelist(list_of_seq (shake256 inp1) outlen) /\
      read (memory :> bytes(out2,outlen)) s =
      num_of_bytelist(list_of_seq (shake256 inp2) outlen) /\
      read (memory :> bytes(out3,outlen)) s =
      num_of_bytelist(list_of_seq (shake256 inp3) outlen)`;;

(*** The buffers on the stack for out0, ..., out3 ***)

let SHAKE256X4_BUF = map SHAKE256X4_SUBST
  [`word_add stackpointer (word(b + 464)):int64`;
   `word_add stackpointer (word(b + 320)):int64`;
   `word_add stackpointer (word(b + 176)):int64`;
   `word_add stackpointer (word(b + 32)):int64`];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy at the    *)
(* addresses mf and mc in the GOT entries, with their code and data in the   *)
(* region (ea,el). The inputs are four lists of bytes of the same length     *)
(* inlen, at in0, ..., in3, the last given on the stack with inlen, and the  *)
(* outlen bytes of each output, as a number, are the first outlen bytes of   *)
(* shake256 of the corresponding input. The stack is the 1552 bytes of the   *)
(* function, at most, and the 320 used by mlk_keccak_absorb_once_x4 below    *)
(* them, and the two 8-byte stack arguments are just above it.               *)
(* ------------------------------------------------------------------------- *)

(*** Zeroing the context with memset, and the absorption ***)

let SHAKE256X4_ABSORB_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (1--9) THEN
  SHAKE256X4_SP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (10--10) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (11--30) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC 30 THEN
  SHAKE256X4_NORM_TAC THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 35 THEN
  MEMSET_ZERO_BYTES_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (36--43) THEN
  SHAKE256X4_NBLOCKS_TAC THEN SHAKE256X4_GOT_TAC THEN SHAKE256X4_NORM_TAC THEN
  LOCAL_ABSORB_X4_TAC
   [`read X0 s`; `136`; `read X2 s`; `read X3 s`; `read X4 s`;
    `read X5 s`; `inlen:num`; `num_of_bytelist(inp0:byte list)`;
    `num_of_bytelist(inp1:byte list)`; `num_of_bytelist(inp2:byte list)`;
    `num_of_bytelist(inp3:byte list)`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 44 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  SHAKE256X4_FIX_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The whole blocks, in a loop unless there are none ***)

let SHAKE256X4_BLOCKS_TAC =
  ASM_CASES_TAC `nb = 0` THENL
   [ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (1--2) THEN
    SHAKE256X4_CC_TAC `nb = 0` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_TRIVIAL; list_of_seq;
                num_of_bytelist; keccak_squeeze];
    ALL_TAC] THEN
  ENSURES_WHILE_UP2_TAC `nb:num` `pc + mlkem_shake256x4_loop1`
   `pc + mlkem_shake256x4_loop1_exit`
    SHAKE256X4_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (1--2) THEN
    SHAKE256X4_CC_TAC `~(nb = 0)` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (3--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; READ_MEMORY_BYTES_TRIVIAL;
                list_of_seq; num_of_bytelist; keccak_squeeze];

    (*** The loop body: permute, extract a block of each, the test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `136 * i + 136 <= outlen` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`i < nb`; `136 * nb + rest = outlen`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (1--2) THEN
    SHAKE256X4_NORM_TAC THEN SHAKE256X4_STATES_TAC THEN
    LOCAL_PERMUTE_X4_TAC
     [`read X0 s`; `keccak_squeeze i (S0:1600 word)`;
      `keccak_squeeze i (S1:1600 word)`;
      `keccak_squeeze i (S2:1600 word)`;
      `keccak_squeeze i (S3:1600 word)`; `pc:num`; `read SP s`;
      `read X30 s`] 3 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    SHAKE256X4_FIX_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (4--11) THEN
    SHAKE256X4_NORM_TAC THEN SHAKE256X4_STATES_TAC THEN
    LOCAL_EXTRACT_X4_TAC
     [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
      `0`; `136`; `keccak_f1600(keccak_squeeze i (S0:1600 word))`;
      `keccak_f1600(keccak_squeeze i (S1:1600 word))`;
      `keccak_f1600(keccak_squeeze i (S2:1600 word))`;
      `keccak_f1600(keccak_squeeze i (S3:1600 word))`; `pc:num`;
      `read X30 s`] 12 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (13--18) THEN
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
    ASM_REWRITE_TAC[]];;

(*** The remaining bytes, if any, through the buffers on the stack ***)

let SHAKE256X4_REST_PART_TAC =
  ASM_CASES_TAC `rest = 0` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (1--3) THEN
  SHAKE256X4_REST_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (4--4) THENL
   [SHAKE256X4_BRANCH_TAC TRUTH `rest = 0` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `outlen = 136 * nb` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`rest = 0`; `136 * nb + rest = outlen`] THEN
      ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN

  (*** Otherwise one more block into the buffers, and the memcpys ***)

  SHAKE256X4_BRANCH_TAC TRUTH `~(rest = 0)` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (5--8) THEN
  SHAKE256X4_NORM_TAC THEN SHAKE256X4_STATES_TAC THEN
  LOCAL_PERMUTE_X4_TAC
   [`read X0 s`; `keccak_squeeze nb (S0:1600 word)`;
    `keccak_squeeze nb (S1:1600 word)`; `keccak_squeeze nb (S2:1600 word)`;
    `keccak_squeeze nb (S3:1600 word)`; `pc:num`; `read SP s`;
    `read X30 s`] 9 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  SHAKE256X4_FIX_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (10--17) THEN
  SHAKE256X4_NORM_TAC THEN SHAKE256X4_STATES_TAC THEN
  LOCAL_EXTRACT_X4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`; `0`;
    `136`; `keccak_f1600(keccak_squeeze nb (S0:1600 word))`;
    `keccak_f1600(keccak_squeeze nb (S1:1600 word))`;
    `keccak_f1600(keccak_squeeze nb (S2:1600 word))`;
    `keccak_f1600(keccak_squeeze nb (S3:1600 word))`; `pc:num`;
    `read X30 s`] 18 THEN
  MAP_EVERY (fun (a,sv,k0,k) ->
    SHAKE256X4_TMP_TAC a THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (k0--k) THEN
    LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC k THEN
    SHAKE256X4_NORM_TAC THEN
    LIBC_CALL_TAC "H_MEMCPY" MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC
     [`read X0 s`; `read X1 s`; `read X2 s`;
      vsubst [sv,`S:1600 word`]
       `val(keccak_f1600(keccak_squeeze nb (S:1600 word))) MOD
        2 EXP (8 * rest)`;
      `read X30 s`] (k + 5))
   (map (fun j ->
      el j SHAKE256X4_BUF,
      el j [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`],
      el j [19; 30; 39; 48], el j [24; 33; 42; 51]) (0--3)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `outlen = 136 * nb + rest` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE;
              NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[GSYM ADD1; keccak_squeeze];;

(*** Zeroing the context and the buffers, the stack guard, the return ***)

let SHAKE256X4_END_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (1--5) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC 5 THEN
  SHAKE256X4_NORM_TAC THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (11--36) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (37--49) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!out0 out1 out2 out3 outlen in0 in1 in2 in3 inlen
   (inp0:byte list) (inp1:byte list) (inp2:byte list) (inp3:byte list)
   guard mf mc ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        LENGTH inp0 = inlen /\ LENGTH inp1 = inlen /\
        LENGTH inp2 = inlen /\ LENGTH inp3 = inlen /\
        PAIRWISE nonoverlapping
         [(out0,outlen); (out1,outlen); (out2,outlen); (out3,outlen);
          (word_sub stackpointer (word 1872),1872)] /\
        ALLPAIRS nonoverlapping
         [(out0,outlen); (out1,outlen); (out2,outlen); (out3,outlen);
          (word_sub stackpointer (word 1872),1872)]
         [(in0,inlen); (in1,inlen); (in2,inlen); (in3,inlen);
          (stackpointer,16); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
          (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_shake256x4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS
                   [out0; out1; out2; out3; word outlen; in0; in1; in2] s /\
                  read (memory :> bytes64 stackpointer) s = in3 /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  word inlen /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
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
                memory :> bytes(word_sub stackpointer (word 1872),1872)])`,
  MAP_EVERY X_GEN_TAC
   [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`; `outlen:num`;
    `in0:int64`; `in1:int64`; `in2:int64`; `in3:int64`; `inlen:num`;
    `inp0:byte list`; `inp1:byte list`; `inp2:byte list`; `inp3:byte list`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 1872 THEN
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
  ENSURES_SEQUENCE_TAC
   `pc + mlkem_shake256x4_after_mlk_keccak_absorb_once_x4` SHAKE256X4_A1 THEN
  CONJ_TAC THENL [SHAKE256X4_ABSORB_TAC; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC
   `pc + mlkem_shake256x4_loop1_exit` SHAKE256X4_A2 THEN
  CONJ_TAC THENL [SHAKE256X4_BLOCKS_TAC; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC
   `pc + mlkem_shake256x4_join2` SHAKE256X4_A3 THEN
  CONJ_TAC THENL [SHAKE256X4_REST_PART_TAC; SHAKE256X4_END_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contracts for memset and memcpy. The events depend on the address of the  *)
(* stack guard, on the input in3 given on the stack and on whether the stack *)
(* pointer is a multiple of 32, and the number of iterations of the loop and *)
(* whether there is a remainder depend on outlen. The events are split at    *)
(* the intermediate points of the correctness proof, from the end, with the  *)
(* public parts of the same assertions, and when the events so far consist   *)
(* of several parts they are kept as a variable e2 in the simulation.        *)
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
      (mlkem_native_libmlkem_clang17_O3_mc,
       MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      ilist n THENL
     [SHAKE256X4_EXISTS_E2_TAC; LABEL_TAC name safety_th]);;

let SHAKE256X4_LIBC_SAFE_CALL_TAC name n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true
      MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC th
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
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (1--9) THEN
  SHAKE256X4_SP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (10--10) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (11--30) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC 30 THEN
  SHAKE256X4_NORM_TAC THEN
  SHAKE256X4_LIBC_SAFE_CALL_TAC "H_MEMSET" 35 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (36--43) THEN
  SHAKE256X4_NBLOCKS_TAC THEN SHAKE256X4_GOT_TAC THEN SHAKE256X4_NORM_TAC THEN
  SHAKE256X4_SAFE_CALL_TAC "H_ABSORB"
   [`e:(uarch_event)list`; `read X0 s`; `136`; `read X2 s`; `read X3 s`;
    `read X4 s`; `read X5 s`; `inlen:num`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 44 THEN
  SHAKE256X4_FIX_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_DISCHARGE_TAC;;

(*** The whole blocks ***)

let SHAKE256X4_SAFE_BLOCKS_TAC =
  ASM_CASES_TAC `nb = 0` THEN ASM_REWRITE_TAC[] THENL
   [SHAKE256X4_SAFE_INIT_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (1--2) THEN
    SHAKE256X4_CC_TAC `nb = 0` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SHAKE256X4_DISCHARGE_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `nb:num` `pc + mlkem_shake256x4_loop1`
   `pc + mlkem_shake256x4_loop1_exit`
    (SHAKE256X4_PUBLIC SHAKE256X4_INV) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    SHAKE256X4_SAFE_INIT_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (1--2) THEN
    SHAKE256X4_CC_TAC `~(nb = 0)` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (3--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
    SHAKE256X4_DISCHARGE_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SHAKE256X4_SAFE_INIT_TAC THEN
    SUBGOAL_THEN `136 * i + 136 <= outlen` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`i < nb`; `136 * nb + rest = outlen`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (1--2) THEN
    SHAKE256X4_NORM_TAC THEN
    SHAKE256X4_SAFE_CALL_TAC "H_PERMUTE"
     [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
      `read X30 s`] 3 THEN
    SHAKE256X4_FIX_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (4--11) THEN
    SHAKE256X4_NORM_TAC THEN
    SHAKE256X4_SAFE_CALL_TAC "H_EXTRACT"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
      `read X3 s`; `read X4 s`; `0`; `136`; `pc:num`; `read X30 s`] 12 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (13--18) THEN
    SHAKE256X4_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        REWRITE_TAC[ARITH_RULE `136 * (i + 1) = 136 * i + 136`] THEN
        NO_TAC) THEN
    SHAKE256X4_DISCHARGE_TAC;

    REWRITE_TAC[] THEN SHAKE256X4_SAFE_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SHAKE256X4_DISCHARGE_TAC];;

(*** The remaining bytes ***)

let SHAKE256X4_SAFE_REST_TAC =
  ASM_CASES_TAC `rest = 0` THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_SAFE_INIT_OPAQUE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (1--3) THEN
  SHAKE256X4_REST_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (4--4) THENL
   [SHAKE256X4_BRANCH_TAC TRUTH `rest = 0` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SHAKE256X4_DISCHARGE_TAC;
    ALL_TAC] THEN
  SHAKE256X4_BRANCH_TAC TRUTH `~(rest = 0)` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (5--8) THEN
  SHAKE256X4_NORM_TAC THEN
  SHAKE256X4_SAFE_CALL_TAC "H_PERMUTE"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
    `read X30 s`] 9 THEN
  SHAKE256X4_FIX_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (10--17) THEN
  SHAKE256X4_NORM_TAC THEN
  SHAKE256X4_SAFE_CALL_TAC "H_EXTRACT"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `read X4 s`; `0`; `136`; `pc:num`; `read X30 s`] 18 THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (k0--k) THEN
    LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC k THEN
    SHAKE256X4_NORM_TAC THEN
    SHAKE256X4_LIBC_SAFE_CALL_TAC "H_MEMCPY" (k + 5))
   [19,24; 30,33; 39,42; 48,51] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_DISCHARGE_ASSOC_TAC;;

(*** Zeroing, the stack guard and the return ***)

let SHAKE256X4_SAFE_END_TAC =
  SHAKE256X4_SAFE_INIT_OPAQUE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (1--5) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC 5 THEN
  SHAKE256X4_NORM_TAC THEN
  SHAKE256X4_LIBC_SAFE_CALL_TAC "H_MEMSET" 10 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (11--36) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC (37--49) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_DISCHARGE_TAC;;

let MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`!mf mc ea el ev.
     memset_safety_contract mf ea el ev /\
     memcpy_safety_contract mc ea el ev
     ==> exists f_events.
          forall e out0 out1 out2 out3 outlen in0 in1 in2 in3 inlen guard
                 pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
            [out0,outlen; out1,outlen; out2,outlen; out3,outlen;
             word_sub stackpointer (word 1872),1872] /\
           ALLPAIRS nonoverlapping
            [out0,outlen; out1,outlen; out2,outlen; out3,outlen;
             word_sub stackpointer (word 1872),1872]
            [in0,inlen; in1,inlen; in2,inlen; in3,inlen; stackpointer,16;
             word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8;
             word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_native_libmlkem_clang17_O3_mc /\
                     read PC s = word (pc + mlkem_shake256x4) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS
                      [out0; out1; out2; out3; word outlen; in0; in1; in2] s /\
                     read (memory :> bytes64 stackpointer) s = in3 /\
                     read (memory :> bytes64(word_add stackpointer (word 8)))
                          s =
                     word inlen /\
                     read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                      = guard /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events in0 in1 in2 in3 out0 out1 out2 out3
                               outlen inlen guard mf mc pc
                               (word_sub stackpointer (word 1872))
                               returnaddress /\
                        memaccess_inbounds e2
                         [in0,inlen; in1,inlen; in2,inlen; in3,inlen;
                          out0,outlen; out1,outlen; out2,outlen; out3,outlen;
                          stackpointer,16;
                          word_sub stackpointer (word 1872),1872;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                          word(pc + got_memset),8;
                          word(pc + got_memcpy),8; ea,el]
                         [out0,outlen; out1,outlen; out2,outlen; out3,outlen;
                          word_sub stackpointer (word 1872),1872]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(out0,outlen); memory :> bytes(out1,outlen);
                   memory :> bytes(out2,outlen); memory :> bytes(out3,outlen);
                   memory :> bytes(word_sub stackpointer (word 1872),1872)])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[memset_safety_contract; memcpy_safety_contract] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMSET")
   (fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMCPY")) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
    "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
    "H_EXTRACT" THEN
  CONCRETIZE_F_EVENTS_TAC SHAKE256X4_F_EVENTS THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_SHAKE256X4_CLANG17_O3_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SHAKE256X4_SETUP_TAC THEN SHAKE256X4_BOUND_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_shake256x4_join2`
   (SHAKE256X4_PUBLIC SHAKE256X4_A3) THEN
  CONJ_TAC THENL [ALL_TAC; SHAKE256X4_SAFE_END_TAC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_shake256x4_loop1_exit`
   (SHAKE256X4_PUBLIC SHAKE256X4_A2) THEN
  CONJ_TAC THENL [ALL_TAC; SHAKE256X4_SAFE_REST_TAC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlkem_shake256x4_after_mlk_keccak_absorb_once_x4`
   (SHAKE256X4_PUBLIC SHAKE256X4_A1) THEN
  CONJ_TAC THENL [SHAKE256X4_SAFE_ABSORB_TAC; SHAKE256X4_SAFE_BLOCKS_TAC]);;
