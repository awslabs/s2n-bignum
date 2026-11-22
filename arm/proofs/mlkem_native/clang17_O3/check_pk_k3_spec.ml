(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The modulus check of an ML-KEM-768 encapsulation key. This is the code    *)
(* for mlkem768_check_pk from mlkem-native's portable C implementation       *)
(* compiled by clang 17 with -O3 (see mlkem_native/README.md). It decodes    *)
(* the vector of the key from its first 1152 bytes into a buffer on the      *)
(* stack, reduces it, encodes it again into another buffer, compares the     *)
(* result in constant time with the key, and zeroes the buffers with memset. *)
(* The comparison is a loop over 32 bytes per iteration with two             *)
(* accumulators. The function saves its registers, realigns the stack        *)
(* pointer to 32 bytes, and keeps the buffers above the 32 bytes of the      *)
(* callees; the statements use the stack frame below the incoming stack      *)
(* pointer. It is verified in the whole image (see libmlkem.ml), using the   *)
(* theorems for mlkem768_polyvec_frombytes, mlkem768_polyvec_reduce and      *)
(* mlkem768_polyvec_tobytes in the image and assuming the contracts for      *)
(* memset in utils/mlkem_native_libc.ml.                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/polyvec_frombytes_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/polyvec_reduce_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/polyvec_tobytes_k3_spec.ml";;

(*** The code in the image, and the PLT stub for memset:

    mlkem768_check_pk:
       +0x0: stp     x29, x30, [sp, #-48]!
       +0x4: stp     x28, x21, [sp, #16]
       +0x8: stp     x20, x19, [sp, #32]
       +0xc: mov     x29, sp
      +0x10: sub     x9, sp, #0xa90
      +0x14: and     sp, x9, #0xffffffffffffffe0
      +0x18: adrp    x8, <page>
      +0x1c: mov     x19, x0
      +0x20: add     x0, sp, #0x480
      +0x24: mov     x1, x19
      +0x28: ldr     x8, [x8, #4088]
      +0x2c: ldr     x8, [x8]
      +0x30: str     x8, [sp, #2696]
      +0x34: bl      <mlkem768_polyvec_frombytes>
      +0x38: add     x0, sp, #0x480
      +0x3c: bl      <mlkem768_polyvec_reduce>
      +0x40: mov     x0, sp
      +0x44: add     x1, sp, #0x480
      +0x48: mov     x20, sp
      +0x4c: bl      <mlkem768_polyvec_tobytes>
      +0x50: movi    v0.2d, #0x0
      +0x54: mov     x8, xzr
      +0x58: movi    v1.2d, #0x0
      +0x5c: movi    v2.2d, #0x0
      +0x60: movi    v3.2d, #0x0
      +0x64: add     x9, x19, x8
      +0x68: add     x10, x20, x8
      +0x6c: add     x8, x8, #0x20
      +0x70: cmp     x8, #0x480
      +0x74: ldp     q4, q5, [x9]
      +0x78: ldp     q6, q7, [x10]
      +0x7c: eor     v4.16b, v6.16b, v4.16b
      +0x80: orr     v2.16b, v4.16b, v2.16b
      +0x84: eor     v5.16b, v7.16b, v5.16b
      +0x88: orr     v3.16b, v5.16b, v3.16b
      +0x8c: eor     v0.16b, v4.16b, v0.16b
      +0x90: eor     v1.16b, v5.16b, v1.16b
      +0x94: b.ne    <mlkem768_check_pk+0x64>
      +0x98: orr     v2.16b, v3.16b, v2.16b
      +0x9c: mov     w20, wzr
      +0xa0: ext     v3.16b, v2.16b, v2.16b, #8
      +0xa4: mov     x0, sp
      +0xa8: eor     v0.16b, v1.16b, v0.16b
      +0xac: mov     w1, w20
      +0xb0: mov     w2, #0x480
      +0xb4: mov     w8, #0xfffffffc
      +0xb8: mov     x21, sp
      +0xbc: orr     v1.8b, v2.8b, v3.8b
      +0xc0: ext     v2.16b, v0.16b, v0.16b, #8
      +0xc4: fmov    x9, d1
      +0xc8: orr     x9, x9, x9, lsr #32
      +0xcc: lsr     x10, x9, #16
      +0xd0: eor     v0.8b, v0.8b, v2.8b
      +0xd4: orr     w9, w9, w10
      +0xd8: fmov    x10, d0
      +0xdc: orr     w9, w9, w9, lsr #8
      +0xe0: eor     x10, x10, x10, lsr #32
      +0xe4: sub     w9, w20, w9, uxtb
      +0xe8: eor     x10, x10, x10, lsr #16
      +0xec: lsr     x11, x10, #8
      +0xf0: eor     w10, w10, w11
      +0xf4: eor     w9, w10, w9, lsr #16
      +0xf8: and     w9, w9, #0xff
      +0xfc: cmp     w9, w10, uxtb
     +0x100: csel    w19, w20, w8, eq
     +0x104: bl      <memset@plt>
     +0x108: add     x0, sp, #0x480
     +0x10c: mov     w1, w20
     +0x110: mov     w2, #0x600
     +0x114: add     x20, sp, #0x480
     +0x118: bl      <memset@plt>
     +0x11c: adrp    x8, <page>
     +0x120: ldr     x8, [x8, #4088]
     +0x124: ldr     x9, [sp, #2696]
     +0x128: ldr     x8, [x8]
     +0x12c: cmp     x8, x9
     +0x130: b.ne    <mlkem768_check_pk+0x14c>
     +0x134: mov     w0, w19
     +0x138: mov     sp, x29
     +0x13c: ldp     x20, x19, [sp, #32]
     +0x140: ldp     x28, x21, [sp, #16]
     +0x144: ldp     x29, x30, [sp], #48
     +0x148: ret
     +0x14c: bl      <__stack_chk_fail@plt>

    memset@plt:
      +0x0: adrp    x16, <page>
      +0x4: ldr     x17, [x16, #4072]  // got_memset
      +0x8: add     x16, x16, #0xfe8  // got_memset
      +0xc: br      x17
 ***)

let MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem768_check_pk"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* The reduced vector, as a list of 16-bit coefficients for the encoding,    *)
(* and the equivalence of its encoding with the key with the 12-bit fields   *)
(* of the key being below 3329.                                              *)
(* ------------------------------------------------------------------------- *)

let CHECKPK_BYTES16_LIST_STMT =
  `!a n (f:num->int16) s:armstate.
        (!i. i < n
             ==> read (memory :> bytes16(word_add a (word(2 * i)))) s = f i)
        ==> read (memory :> bytes(a,2 * n)) s =
            num_of_wordlist(list_of_seq f n)`;;

let CHECKPK_BYTES16_LIST = assume_spec CHECKPK_BYTES16_LIST_STMT;;

let CHECKPK_IVAL_WORD_STMT =
  `!f. f < 32768 ==> ival(word f:int16) = &f`;;

let CHECKPK_IVAL_WORD = assume_spec CHECKPK_IVAL_WORD_STMT;;

let CHECKPK_REDUCED_STMT =
  `!(x:int16) f.
        f < 2 EXP 12 /\ ival x = ival(word f:int16) rem &3329
        ==> x = word(f MOD 3329)`;;

let CHECKPK_REDUCED = assume_spec CHECKPK_REDUCED_STMT;;

let CHECKPK_LIST_PROPS_STMT =
  `!(g:num->num) l.
        LENGTH(list_of_seq (\i. word(g i MOD 3329):int16) l) = l /\
        ALL (\x. val x < 4096) (list_of_seq (\i. word(g i MOD 3329):int16) l)`;;

let CHECKPK_LIST_PROPS = assume_spec CHECKPK_LIST_PROPS_STMT;;

let CHECKPK_REENCODE_STMT =
  `!l n. n < 2 EXP (12 * l)
         ==> (n = num_of_wordlist(MAP (word_zx:int16->12 word)
                    (list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD
                                            2 EXP 12) MOD 3329):int16) l)) <=>
              !i. i < l ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329)`;;

let CHECKPK_REENCODE = assume_spec CHECKPK_REENCODE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The comparison, 16 bytes at a time: the bytes of the key and of the       *)
(* encoding XORed together are ORed into one accumulator (and XORed into     *)
(* another), which is zero if and only if the prefixes so far are equal. The *)
(* loop test compares the pointers.                                          *)
(* ------------------------------------------------------------------------- *)

let CHECKPK_BYTES128_STMT =
  `!a l k n s:armstate.
        read (memory :> bytes(a,l)) s = n /\ 16 * k + 16 <= l
        ==> read (memory :> bytes128(word_add a (word(16 * k)))) s =
            word((n DIV 2 EXP (128 * k)) MOD 2 EXP 128)`;;

let CHECKPK_BYTES128 = assume_spec CHECKPK_BYTES128_STMT;;

let CHECKPK_MOD_STEP_STMT =
  `!n m k. n MOD 2 EXP (128 * (k + 1)) = m MOD 2 EXP (128 * (k + 1)) <=>
           n MOD 2 EXP (128 * k) = m MOD 2 EXP (128 * k) /\
           (n DIV 2 EXP (128 * k)) MOD 2 EXP 128 =
           (m DIV 2 EXP (128 * k)) MOD 2 EXP 128`;;

let CHECKPK_MOD_STEP = assume_spec CHECKPK_MOD_STEP_STMT;;

let CHECKPK_OR_STEP_STMT =
  `!q:int128 a b.
        word_or
         (word_xor (word(a MOD 340282366920938463463374607431768211456))
                   (word(b MOD 340282366920938463463374607431768211456)))
         q = word 0 <=>
        q = word 0 /\ b MOD 2 EXP 128 = a MOD 2 EXP 128`;;

let CHECKPK_OR_STEP = assume_spec CHECKPK_OR_STEP_STMT;;

let CHECKPK_OR_STEP2_STMT =
  `!q:int128 a b.
        word_or q
         (word_xor (word(a MOD 340282366920938463463374607431768211456))
                   (word(b MOD 340282366920938463463374607431768211456))) =
        word 0 <=>
        q = word 0 /\ a MOD 2 EXP 128 = b MOD 2 EXP 128`;;

let CHECKPK_OR_STEP2 = assume_spec CHECKPK_OR_STEP2_STMT;;

let CHECKPK_MOD_STEP2_STMT =
  `!n m i. n MOD 2 EXP (256 * (i + 1)) = m MOD 2 EXP (256 * (i + 1)) <=>
           n MOD 2 EXP (256 * i) = m MOD 2 EXP (256 * i) /\
           (n DIV 2 EXP (256 * i)) MOD 2 EXP 128 =
           (m DIV 2 EXP (256 * i)) MOD 2 EXP 128 /\
           (n DIV 2 EXP (256 * i + 128)) MOD 2 EXP 128 =
           (m DIV 2 EXP (256 * i + 128)) MOD 2 EXP 128`;;

let CHECKPK_MOD_STEP2 = assume_spec CHECKPK_MOD_STEP2_STMT;;

let CHECKPK3_TEST_STMT =
  `!i. i < 36
       ==> (val(word_add (word(32 * i)) (word 18446744073709550496):int64) = 0
            <=> ~(i + 1 < 36))`;;

let CHECKPK3_TEST = assume_spec CHECKPK3_TEST_STMT;;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* address depends on whether the stack pointer is a multiple of 32 or just  *)
(* of 16. The proof uses a variable boff for the offset of the first one.    *)
(* ------------------------------------------------------------------------- *)

let CHECKPK_ALIGNED_16_32_STMT =
  `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`;;

let CHECKPK_ALIGNED_16_32 = assume_spec CHECKPK_ALIGNED_16_32_STMT;;

let CHECKPK3_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 48)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 32 else 48)) /\
            aligned 16 (word_add sp (word(if aligned 32 sp then 32 else 48)))`;;

let CHECKPK3_BUFFER_ADDRESS = assume_spec CHECKPK3_BUFFER_ADDRESS_STMT;;

let CHECKPK_BUFFER_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) &&
       can (term_match [] `word_and (word_add stackpointer (word n))
                                    (word m):int64`) (lhs(concl th))
    then SUBST_ALL_TAC th else NO_TAC);;

let CHECKPK_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset as in               *)
(* mlkem_native_libc.ml. The first 1152 bytes of the key at pk are a       *)
(* number n, and the result is 0 if all the 768 12-bit fields of n are     *)
(* below 3329, which is the modulus check of FIPS 203, and -4 otherwise.   *)
(* The loop of the comparison has an invariant stating the value of the    *)
(* accumulators in terms of the prefixes of the key and of the encoding.   *)
(* The stack is the 2752 bytes of the function, with the buffers aligned   *)
(* within them, and the 32 bytes used by the callees below them, plus up   *)
(* to 16 bytes of padding.                                                 *)
(* ------------------------------------------------------------------------- *)

let LOCAL_FROMBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLYVEC_REDUCE_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_TOBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLYVEC_TOBYTES_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

(*** The setup, with the offset of the buffers as boff ***)

let CHECKPK3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `n:num`; `guard:int64`; `mf:int64`; `ea:int64`; `el:num`;
    `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 2800 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (LABEL_TAC "H_MEMSET" o REWRITE_RULE[memset_contract])
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 2800):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP CHECKPK3_BUFFER_ADDRESS
          (ASSUME `aligned 16 (stackpointer:int64)`)) THEN
  SUBGOAL_THEN
   `32 <= (if aligned 32 (stackpointer:int64) then 32 else 48) /\
    (if aligned 32 (stackpointer:int64) then 32 else 48) <= 48`
  MP_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`if aligned 32 (stackpointer:int64) then 32 else 48`,
           `boff:num`) THEN
  GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word boff) (word 32):int64 = word(boff - 32)`
  ASSUME_TAC THENL [MATCH_MP_TAC WORD_SUB2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word boff) (word 16):int64 = word(boff - 16)`
  ASSUME_TAC THENL [MATCH_MP_TAC WORD_SUB2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x28_init" `X28` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29`;;

(*** The regions of the callees, in the form word_add stackpointer (word _) ***)

let CHECKPK_FIX_TAC =
  RULE_ASSUM_TAC(fun th ->
    if maychange_term (concl th)
    then REWRITE_RULE
          [ASSUME `word_sub (word boff) (word 32):int64 = word(boff - 32)`;
           ASSUME `word_sub (word boff) (word 16):int64 = word(boff - 16)`] th
    else th);;

(*** A call of a callee, whose buffer address is word_add (word_add sp b) c ***)

let CHECKPK_CALL_TAC tac args n =
  tac args n THENL [CONV_TAC WORD_RULE; ALL_TAC];;

(*** The facts in the loop, with the saved registers and the stack guard ***)

let CHECKPK_L =
 `list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329):int16)
              768`;;

let CHECKPK_M =
 `num_of_wordlist(MAP (word_zx:int16->12 word)
   (list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329))
                768))`;;

let CHECKPK3_FRAME = vsubst [CHECKPK_M,`M:num`]
 `read SP s = word_add stackpointer (word boff) /\
  read X29 s = word_add stackpointer (word 2752) /\
  read (memory :> bytes64 (word_add stackpointer (word 2752))) s = x29_init /\
  read (memory :> bytes64 (word_add stackpointer (word 2760))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 2768))) s = x28_init /\
  read (memory :> bytes64 (word_add stackpointer (word 2776))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 2784))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 2792))) s = x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word(boff + 2696)))) s =
  canary /\
  read (memory :> bytes64 (word_add (word pc) (word 196600))) s = guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word 196584))) s = mf /\
  read (memory :> bytes(ea,el)) s = ev /\
  read X19 s = pk /\
  read X20 s = word_add stackpointer (word boff) /\
  read (memory :> bytes(pk,1152)) s = n /\
  read (memory :> bytes(word_add stackpointer (word boff),1152)) s = M`;;

let CHECKPK3_INV = vsubst [CHECKPK_M,`M:num`]
 `\i s. read X8 s = word(32 * i) /\
        (read Q2 s = word 0 /\ read Q3 s = word 0 <=>
         n MOD 2 EXP (256 * i) = M MOD 2 EXP (256 * i))`;;

let CHECKPK3_INV_FRAME =
  let vs,bod = strip_abs CHECKPK3_INV in
  list_mk_abs(vs,mk_conj(bod,CHECKPK3_FRAME));;

(*** Decoding, reducing and encoding the vector, up to the loop ***)

let CHECKPK_LIST_TAC s =
  SUBGOAL_THEN (vsubst [s,`s:armstate`]
   `read (memory :> bytes(word_add (word_add stackpointer (word boff))
                          (word 1152),1536)) s =
    num_of_wordlist(list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD
                                           2 EXP 12) MOD 3329):int16) 768)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1536 = 2 * 768`] THEN
    MATCH_MP_TAC CHECKPK_BYTES16_LIST THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CHECKPK_REDUCED THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add stackpointer (word boff)) (word 1152))
               (word (2 * i)):int64 =
      word_add (word_add stackpointer (word boff)) (word (1152 + 2 * i))`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let CHECKPK3_PART1_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (1--6) THEN
  CHECKPK_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (7--7) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (8--14) THEN
  CHECKPK_CALL_TAC LOCAL_FROMBYTES_TAC [`read X0 s`; `read X1 s`; `n:num`;
                       `pc:num`; `read SP s`; `read X30 s`] 15 THEN
  CHECKPK_FIX_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (16--17) THEN
  CHECKPK_CALL_TAC LOCAL_REDUCE_TAC [`read X0 s`;
    `\i. word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12):int16`;
    `pc:num`; `read SP s`; `read X30 s`] 18 THEN
  CHECKPK_FIX_TAC THEN
  CHECKPK_LIST_TAC `s18:armstate` THEN CHECKPK_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (19--22) THEN
  CHECKPK_CALL_TAC LOCAL_TOBYTES_TAC [`read X0 s`; `read X1 s`; CHECKPK_L;
                     `pc:num`; `read SP s`; `read X30 s`] 23 THEN
  CHECKPK_FIX_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CHECKPK_LIST_PROPS]) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (24--28) THEN
  CHECKPK_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; EXP; MOD_1] THEN
  ASM_REWRITE_TAC[];;

(*** The loop body, comparing 32 more bytes as two 128-bit words. The      ***)
(*** address of the second one in the stack buffer is not normalized.      ***)

let CHECKPK_CHUNK_TAC norm a v k =
  let bth = MP (ARITH_RULE (subst [k,`k:num`]
                  `i < 36 ==> 16 * k + 16 <= 1152`))
               (ASSUME `i < 36`) in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),Comb(_,Comb(Const("bytes",_),aa))),
                     s)),vv)
        when aa = mk_pair(a,`1152`) && vv = v ->
          let lth = SPECL [a; `1152`; k; v; s] CHECKPK_BYTES128 in
          let fth = REWRITE_RULE
                      [ARITH_RULE `16 * (2 * i) = 32 * i`;
                       ARITH_RULE `16 * (2 * i + 1) = 32 * i + 16`;
                       ARITH_RULE `128 * (2 * i) = 256 * i`;
                       ARITH_RULE `128 * (2 * i + 1) = 256 * i + 128`]
                      (MP lth (CONJ th bth)) in
          ASSUME_TAC(if norm then CONV_RULE(ONCE_DEPTH_CONV
                                    NORMALIZE_RELATIVE_ADDRESS_CONV) fth
                     else fth)
    | _ -> NO_TAC);;

let CHECKPK3_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ABBREV_TAC(mk_eq(`mm:num`,CHECKPK_M)) THEN
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  ENSURES_INIT_TAC "s0" THEN
  CHECKPK_CHUNK_TAC true `pk:int64` `n:num` `2 * i` THEN
  CHECKPK_CHUNK_TAC true `pk:int64` `n:num` `2 * i + 1` THEN
  CHECKPK_CHUNK_TAC true `word_add stackpointer (word boff):int64` `mm:num`
                    `2 * i` THEN
  CHECKPK_CHUNK_TAC false `word_add stackpointer (word boff):int64` `mm:num`
                    `2 * i + 1` THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (1--13) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` CHECKPK3_TEST) (ASSUME `i < 36`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[];
    REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_iff(concl th) &&
      lhand(concl th) = `q2:int128 = word 0 /\ q3:int128 = word 0`)) THEN
    REWRITE_TAC[CHECKPK_OR_STEP2; CHECKPK_MOD_STEP2] THEN
    CONV_TAC TAUT];;

(*** The final result from the accumulators, the zeroing, the return ***)

let CHECKPK_BOUND a s =
  REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
   (ISPECL [a; `1152`; mk_comb(`read memory:armstate->int64->byte`,s)]
           READ_BYTES_BOUND);;

let CHECKPK3_DONE_TAC =
  SUBGOAL_THEN
   `(q2:int128 = word 0 /\ q3:int128 = word 0) <=>
    !i. i < 768 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) && lhand(concl th) = `q2:int128 = word 0 /\
                                                q3:int128 = word 0`
      then REWRITE_TAC[th] else NO_TAC) THEN
    MP_TAC(CHECKPK_BOUND `pk:int64` `s0:armstate`) THEN
    MP_TAC(CHECKPK_BOUND `word_add stackpointer (word boff):int64`
                         `s0:armstate`) THEN
    ASM_REWRITE_TAC[ARITH_RULE `8 * 1152 = 256 * 36`] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> concl th = mk_eq(CHECKPK_M,`mm:num`))) THEN
    MATCH_MP_TAC CHECKPK_REENCODE THEN
    ASM_REWRITE_TAC[ARITH_RULE `12 * 768 = 256 * 36`];
    ALL_TAC];;

let CHECKPK3_EXIT_TAC =
  ABBREV_TAC(mk_eq(`mm:num`,CHECKPK_M)) THEN
  GHOST_INTRO_TAC `q1:int128` `read Q1` THEN
  GHOST_INTRO_TAC `q0:int128` `read Q0` THEN
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  ENSURES_INIT_TAC "s0" THEN CHECKPK3_DONE_TAC THEN

  (*** The comparison of the hashes and the zeroing of the buffers ***)

  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (1--27) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (28--28) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC 28 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 33 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (34--38) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC 38 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 43 THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN

  (*** The stack guard and the return ***)

  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (44--44) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (45--55) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th ->
    if is_iff(concl th) &&
       lhand(concl th) = `q2:int128 = word 0 /\ q3:int128 = word 0`
    then REWRITE_TAC[SYM th] else NO_TAC) THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));;

let MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!pk n guard mf ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (pk,1152) (word pc,libmlkem_size) /\
        ALLPAIRS nonoverlapping
         [(word_sub stackpointer (word 2800),2800)]
         [(pk,1152); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem768_check_pk) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [pk] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(pk,1152)) s = n)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                  (if !i. i < 768
                          ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
                   then word 0 else word 0xfffffffc))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 2800),2800)])`;;

let MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contract for memset. The events depend only on the address of the key,    *)
(* the stack and the image: the comparison is in constant time and the       *)
(* result is selected without a branch. The buffers are kept at their offset *)
(* from the stack pointer as a conditional (32 or 48), and the loop          *)
(* invariant has only the pointers and the frame.                            *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let CHECKPK_ALLOWED =
  [`pc:num`; `pk:int64`; `guard:int64`; `mf:int64`;
   `stackpointer:int64`; `returnaddress:int64`; `i:num`;
   `f_ev_loop:int64->int64->int64->num->int64->int64->num->
              (uarch_event)list`; `boff:num`];;

let CHECKPK_EV_CONV =
  REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
  DEPTH_CONV NUM_ADD_CONV;;

let CHECKPK_EV_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE CHECKPK_EV_CONV th else th);;

(*** The events of the loop in the assumptions have the addresses in the
     normalized form, as those in the goal after the loop invariant is
     normalized in the same way. At the exit, the events of the goal are
     normalized before f_ev_epil is unified ***)

let CHECKPK_DISCHARGE_EXIT_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [CONV_TAC(RAND_CONV CHECKPK_EV_CONV) THEN FULL_UNIFY_F_EVENTS_TAC;
    ALL_TAC] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

let CHECKPK_UNABBREV_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
   (fun th -> is_eq(concl th) && rhs(concl th) = `boff:num`));;

let CHECKPK3_EV_CALL_TAC name ilist n =
  CHECKPK_NORMALIZE_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,
       MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref CHECKPK_ALLOWED); LABEL_TAC name safety_th]);;

(*** The reduced vector as a list, with the address of its buffer in the
     normalized form of the events ***)

let CHECKPK_LIST_FLAT_TAC s =
  SUBGOAL_THEN (vsubst [s,`s:armstate`]
   `read (memory :> bytes(word_add stackpointer (word (boff + 1152)),1536))
         s =
    num_of_wordlist(list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD
                                           2 EXP 12) MOD 3329):int16) 768)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1536 = 2 * 768`] THEN
    MATCH_MP_TAC CHECKPK_BYTES16_LIST THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CHECKPK_REDUCED THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN
     `word_add (word_add stackpointer (word (boff + 1152))) (word (2 * i)):int64 =
      word_add stackpointer (word ((boff + 1152) + 2 * i))`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The setup of the proofs with events: the callees, the form of the events
     as the concatenation of those of the prologue, the loop and the epilogue,
     and the offset of the buffers as the abbreviation boff ***)

let CHECKPK3_EV_INTRO_TAC thms =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_safety_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (el 0 thms) "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (el 1 thms) "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (el 2 thms) "H_TOBYTES" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(pk:int64) (guard:int64) (mf:int64) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
     APPEND (f_ev_epil pk guard mf pc stackpointer returnaddress)
      (APPEND
        (ENUMERATEL 36
          (\i. f_ev_loop pk guard mf pc stackpointer returnaddress i))
        (f_ev_prol pk guard mf pc stackpointer returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 2800):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP CHECKPK3_BUFFER_ADDRESS
          (ASSUME `aligned 16 (stackpointer:int64)`)) THEN
  SUBGOAL_THEN
   `32 <= (if aligned 32 (stackpointer:int64) then 32 else 48) /\
    (if aligned 32 (stackpointer:int64) then 32 else 48) <= 48`
  MP_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `boff = if aligned 32 (stackpointer:int64) then 32 else 48` THEN
  STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word boff) (word 32):int64 = word(boff - 32)`
  ASSUME_TAC THENL [MATCH_MP_TAC WORD_SUB2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word boff) (word 16):int64 = word(boff - 16)`
  ASSUME_TAC THENL [MATCH_MP_TAC WORD_SUB2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x28_init" `X28` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29`;;

(*** The events of SAFE with the offset of the buffers as the conditional ***)

let CHECKPK_SAFE_ALLOWED =
  filter (fun t -> t <> `boff:num`) CHECKPK_ALLOWED;;

let CHECKPK3_SAFE_CALL_TAC name ilist n =
  CHECKPK_NORMALIZE_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,
       MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref CHECKPK_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let CHECKPK_SAFE_FIX_TAC =
  RULE_ASSUM_TAC(fun th ->
    if maychange_term (concl th)
    then REWRITE_RULE
          [ASSUME `word_sub (word (if aligned 32 (stackpointer:int64) then 32 else 48)) (word 32):int64 =
                   word((if aligned 32 (stackpointer:int64) then 32 else 48) - 32)`;
           ASSUME `word_sub (word (if aligned 32 (stackpointer:int64) then 32 else 48)) (word 16):int64 =
                   word((if aligned 32 (stackpointer:int64) then 32 else 48) - 16)`] th
    else th);;

let CHECKPK3_SAFE_INTRO_TAC thms =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_safety_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (el 0 thms) "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (el 1 thms) "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (el 2 thms) "H_TOBYTES" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(pk:int64) (guard:int64) (mf:int64) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
     APPEND (f_ev_epil pk guard mf pc stackpointer returnaddress)
      (APPEND
        (ENUMERATEL 36
          (\i. f_ev_loop pk guard mf pc stackpointer returnaddress i))
        (f_ev_prol pk guard mf pc stackpointer returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 2800):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP CHECKPK3_BUFFER_ADDRESS
          (ASSUME `aligned 16 (stackpointer:int64)`)) THEN
  SUBGOAL_THEN
   `32 <= (if aligned 32 (stackpointer:int64) then 32 else 48) /\
    (if aligned 32 (stackpointer:int64) then 32 else 48) <= 48`
  MP_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word (if aligned 32 (stackpointer:int64) then 32 else 48)) (word 32):int64 =
    word((if aligned 32 (stackpointer:int64) then 32 else 48) - 32)`
  ASSUME_TAC THENL [MATCH_MP_TAC WORD_SUB2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (if aligned 32 (stackpointer:int64) then 32 else 48)) (word 16):int64 =
    word((if aligned 32 (stackpointer:int64) then 32 else 48) - 16)`
  ASSUME_TAC THENL [MATCH_MP_TAC WORD_SUB2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x28_init" `X28` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29`;;

(*** The facts in the loop, as for the correctness proof without the values ***)

let CHECKPK3_SAFE_FRAME =
 `read SP s = word_add stackpointer (word (if aligned 32 (stackpointer:int64) then 32 else 48)) /\
  read X29 s = word_add stackpointer (word 2752) /\
  read (memory :> bytes64 (word_add stackpointer (word 2752))) s = x29_init /\
  read (memory :> bytes64 (word_add stackpointer (word 2760))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 2768))) s = x28_init /\
  read (memory :> bytes64 (word_add stackpointer (word 2776))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 2784))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 2792))) s = x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word((if aligned 32 (stackpointer:int64) then 32 else 48) + 2696)))) s =
  canary /\
  read (memory :> bytes64 (word_add (word pc) (word 196600))) s = guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word 196584))) s = mf /\
  read (memory :> bytes(ea,el)) s = ev /\
  read X19 s = pk /\
  read X20 s = word_add stackpointer (word (if aligned 32 (stackpointer:int64) then 32 else 48))`;;

let CHECKPK3_SAFE_INV =
  mk_abs(`i:num`,mk_abs(`s:armstate`,
   mk_conj(`read X8 s = word(32 * i)`,CHECKPK3_SAFE_FRAME)));;

let CHECKPK3_SAFE_PART1_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (1--6) THEN
  CHECKPK_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (7--7) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (8--14) THEN
  CHECKPK3_SAFE_CALL_TAC "H_FROMBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read SP s`;
    `read X30 s`] 15 THEN
  CHECKPK_SAFE_FIX_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (16--17) THEN
  CHECKPK3_SAFE_CALL_TAC "H_REDUCE"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
    `read X30 s`] 18 THEN
  CHECKPK_SAFE_FIX_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (19--22) THEN
  CHECKPK3_SAFE_CALL_TAC "H_TOBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read SP s`;
    `read X30 s`] 23 THEN
  CHECKPK_SAFE_FIX_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (24--28) THEN
  CHECKPK_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let CHECKPK3_SAFE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (1--13) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` CHECKPK3_TEST) (ASSUME `i < 36`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let CHECKPK3_SAFE_EXIT_TAC =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (1--27) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (28--28) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC 28 THEN
  CHECKPK_EV_NORMALIZE_TAC THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref CHECKPK_SAFE_ALLOWED) 33 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (34--38) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC 38 THEN
  CHECKPK_EV_NORMALIZE_TAC THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref CHECKPK_SAFE_ALLOWED) 43 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (44--44) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (45--55) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CHECKPK_DISCHARGE_EXIT_TAC;;

let MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
   memset_safety_contract mf ea el ev
   ==> exists f_events.
        forall e pk guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          nonoverlapping (pk,1152) (word pc,libmlkem_size) /\
          ALLPAIRS nonoverlapping
           [(word_sub stackpointer (word 2800),2800)]
           [(pk,1152); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem768_check_pk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk guard mf pc
                              (word_sub stackpointer (word 2800))
                              returnaddress /\
                       memaccess_inbounds e2
                        [pk,1152; word_sub stackpointer (word 2800),2800;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         ea,el]
                        [word_sub stackpointer (word 2800),2800]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 2800),2800)])`;;

let MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof: the result   *)
(* of the check together with the events. It uses the combined theorems for  *)
(* the callees and the invariant of the correctness proof with the events.   *)
(* The offset boff of the buffers is an abbreviation of the conditional,     *)
(* which is restored before the events are matched, so that they are a       *)
(* function of the stack pointer.                                            *)
(* ------------------------------------------------------------------------- *)

let CHECKPK3_FULL_PART1_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (1--6) THEN
  CHECKPK_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (7--7) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (8--14) THEN
  CHECKPK3_EV_CALL_TAC "H_FROMBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `n:num`; `pc:num`;
    `read SP s`; `read X30 s`] 15 THEN
  CHECKPK_FIX_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (16--17) THEN
  CHECKPK3_EV_CALL_TAC "H_REDUCE"
   [`e:(uarch_event)list`; `read X0 s`;
    `\i. word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12):int16`;
    `pc:num`; `read SP s`; `read X30 s`] 18 THEN
  CHECKPK_FIX_TAC THEN
  CHECKPK_LIST_FLAT_TAC `s18:armstate` THEN CHECKPK_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (19--22) THEN
  CHECKPK3_EV_CALL_TAC "H_TOBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; CHECKPK_L; `pc:num`;
    `read SP s`; `read X30 s`] 23 THEN
  CHECKPK_FIX_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CHECKPK_LIST_PROPS]) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (24--28) THEN
  CHECKPK_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; EXP; MOD_1] THEN
  ASM_REWRITE_TAC[] THEN CHECKPK_UNABBREV_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let CHECKPK3_FULL_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ABBREV_TAC(mk_eq(`mm:num`,CHECKPK_M)) THEN
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  CHECKPK_CHUNK_TAC true `pk:int64` `n:num` `2 * i` THEN
  CHECKPK_CHUNK_TAC true `pk:int64` `n:num` `2 * i + 1` THEN
  CHECKPK_CHUNK_TAC true `word_add stackpointer (word boff):int64` `mm:num`
                    `2 * i` THEN
  CHECKPK_CHUNK_TAC false `word_add stackpointer (word boff):int64` `mm:num`
                    `2 * i + 1` THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (1--13) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` CHECKPK3_TEST) (ASSUME `i < 36`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_iff(concl th) &&
      lhand(concl th) = `q2:int128 = word 0 /\ q3:int128 = word 0`)) THEN
    REWRITE_TAC[CHECKPK_OR_STEP2; CHECKPK_MOD_STEP2] THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
   (fun th -> is_eq(concl th) && rhs(concl th) = `mm:num`)) THEN
  CHECKPK_UNABBREV_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let CHECKPK3_FULL_EXIT_TAC =
  REWRITE_TAC[] THEN
  ABBREV_TAC(mk_eq(`mm:num`,CHECKPK_M)) THEN
  GHOST_INTRO_TAC `q1:int128` `read Q1` THEN
  GHOST_INTRO_TAC `q0:int128` `read Q0` THEN
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  CHECKPK3_DONE_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (1--27) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (28--28) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC 28 THEN
  CHECKPK_EV_NORMALIZE_TAC THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref CHECKPK_ALLOWED) 33 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (34--38) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC 38 THEN
  CHECKPK_EV_NORMALIZE_TAC THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref CHECKPK_ALLOWED) 43 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (44--44) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_EXEC (45--55) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) &&
         lhand(concl th) = `q2:int128 = word 0 /\ q3:int128 = word 0`
      then REWRITE_TAC[SYM th] else NO_TAC) THEN
    W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
     (fun th -> is_eq(concl th) && rhs(concl th) = `mm:num`)) THEN
    CHECKPK_UNABBREV_TAC THEN CHECKPK_DISCHARGE_EXIT_TAC];;

let MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
   memset_safety_contract mf ea el ev
   ==> exists f_events.
        forall e pk n guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          nonoverlapping (pk,1152) (word pc,libmlkem_size) /\
          ALLPAIRS nonoverlapping
           [(word_sub stackpointer (word 2800),2800)]
           [(pk,1152); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem768_check_pk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(pk,1152)) s = n /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if !i. i < 768
                            ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
                     then word 0 else word 0xfffffffc) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk guard mf pc
                              (word_sub stackpointer (word 2800))
                              returnaddress /\
                       memaccess_inbounds e2
                        [pk,1152; word_sub stackpointer (word 2800),2800;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         ea,el]
                        [word_sub stackpointer (word 2800),2800]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 2800),2800)])`;;

let MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_CHECK_PK_K3_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT;;
