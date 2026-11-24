(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 of four inputs of the same length, with four outputs of any      *)
(* length. This is the code for mlkem_shake256x4 from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -Os (see                *)
(* mlkem_native/README.md), which zeroes a context of four states on the     *)
(* stack with memset, absorbs the inputs into it with                        *)
(* mlk_keccak_absorb_once_x4, squeezes the whole blocks of 136 bytes, the    *)
(* rate of SHAKE256, directly into the outputs with                          *)
(* mlk_keccak_squeezeblocks_x4, and the rest of the outputs through four     *)
(* buffers on the stack with one more call of it and memcpy, before zeroing  *)
(* the context and the buffers with mlk_zeroize_3. The number of whole       *)
(* blocks is computed by a division (udiv). It is verified in the whole      *)
(* image (see libmlkem.ml), using the theorems for                           *)
(* mlk_keccak_absorb_once_x4, mlk_keccak_squeezeblocks_x4 and mlk_zeroize_3  *)
(* in the image and assuming the contracts for memset and memcpy in          *)
(* utils/mlkem_native_libc.ml. The result is shake256 of                     *)
(* common/fips202/fips202.ml for each input.                                 *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/keccak_absorb_once_x4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/keccak_squeezeblocks_x4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/zeroize_3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image, and the PLT stubs for memcpy and memset:

    mlkem_shake256x4:
       +0x0: sub     sp, sp, #0x5d0
       +0x4: stp     x23, x24, [sp, #32]
       +0x8: mov     x24, x0
       +0xc: mov     x23, x1
      +0x10: adrp    x0, <page>
      +0x14: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x18: stp     x19, x20, [sp]
      +0x1c: mov     x19, x4
      +0x20: stp     x21, x22, [sp, #16]
      +0x24: mov     x22, #0x88
      +0x28: add     x21, sp, #0x8f
      +0x2c: stp     x25, x26, [sp, #48]
      +0x30: and     x21, x21, #0xffffffffffffffe0
      +0x34: mov     x25, x5
      +0x38: stp     x27, x28, [sp, #64]
      +0x3c: mov     x26, x6
      +0x40: mov     x27, x7
      +0x44: str     x30, [sp, #80]
      +0x48: stp     x2, x3, [sp, #96]
      +0x4c: mov     x2, #0x320
      +0x50: ldr     x28, [sp, #1488]
      +0x54: ldr     x1, [x0]
      +0x58: str     x1, [sp, #1480]
      +0x5c: mov     x1, #0x0
      +0x60: udiv    x20, x4, x22
      +0x64: mov     x0, x21
      +0x68: bl      <memset@plt>
      +0x6c: ldr     x6, [sp, #1496]
      +0x70: mov     x5, x28
      +0x74: mov     x4, x27
      +0x78: mov     x3, x26
      +0x7c: mov     x2, x25
      +0x80: mov     w1, w22
      +0x84: mov     x0, x21
      +0x88: bl      <mlk_keccak_absorb_once_x4>
      +0x8c: ldp     x2, x3, [sp, #96]
      +0x90: mov     x4, x20
      +0x94: mul     x20, x20, x22
      +0x98: mov     w6, w22
      +0x9c: mov     x5, x21
      +0xa0: mov     x1, x23
      +0xa4: mov     x0, x24
      +0xa8: add     x25, sp, #0x540
      +0xac: add     x26, sp, #0x4b8
      +0xb0: add     x27, sp, #0x430
      +0xb4: bl      <mlk_keccak_squeezeblocks_x4>
      +0xb8: add     x28, sp, #0x3a8
      +0xbc: subs    x19, x19, x20
      +0xc0: b.eq    <mlkem_shake256x4+0x12c>
      +0xc4: mov     w6, w22
      +0xc8: mov     x5, x21
      +0xcc: mov     x3, x25
      +0xd0: mov     x4, #0x1
      +0xd4: mov     x2, x26
      +0xd8: mov     x1, x27
      +0xdc: mov     x0, x28
      +0xe0: bl      <mlk_keccak_squeezeblocks_x4>
      +0xe4: mov     x2, x19
      +0xe8: mov     x1, x28
      +0xec: add     x0, x24, x20
      +0xf0: bl      <memcpy@plt>
      +0xf4: mov     x2, x19
      +0xf8: mov     x1, x27
      +0xfc: add     x0, x23, x20
     +0x100: bl      <memcpy@plt>
     +0x104: ldr     x0, [sp, #96]
     +0x108: mov     x2, x19
     +0x10c: mov     x1, x26
     +0x110: add     x0, x0, x20
     +0x114: bl      <memcpy@plt>
     +0x118: ldr     x0, [sp, #104]
     +0x11c: mov     x2, x19
     +0x120: mov     x1, x25
     +0x124: add     x0, x0, x20
     +0x128: bl      <memcpy@plt>
     +0x12c: mov     x0, x21
     +0x130: mov     x1, #0x320
     +0x134: bl      <mlk_zeroize>
     +0x138: mov     x0, x28
     +0x13c: mov     x1, #0x88
     +0x140: bl      <mlk_zeroize>
     +0x144: mov     x0, x27
     +0x148: mov     x1, #0x88
     +0x14c: bl      <mlk_zeroize>
     +0x150: mov     x0, x26
     +0x154: mov     x1, #0x88
     +0x158: bl      <mlk_zeroize>
     +0x15c: mov     x0, x25
     +0x160: mov     x1, #0x88
     +0x164: bl      <mlk_zeroize>
     +0x168: adrp    x0, <page>
     +0x16c: ldr     x0, [x0, #4088]  // got_stack_chk_guard
     +0x170: ldr     x2, [sp, #1480]
     +0x174: ldr     x1, [x0]
     +0x178: subs    x2, x2, x1
     +0x17c: mov     x1, #0x0
     +0x180: b.eq    <mlkem_shake256x4+0x188>
     +0x184: bl      <__stack_chk_fail@plt>
     +0x188: ldp     x19, x20, [sp]
     +0x18c: ldp     x21, x22, [sp, #16]
     +0x190: ldp     x23, x24, [sp, #32]
     +0x194: ldp     x25, x26, [sp, #48]
     +0x198: ldp     x27, x28, [sp, #64]
     +0x19c: ldr     x30, [sp, #80]
     +0x1a0: add     sp, sp, #0x5d0
     +0x1a4: ret

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

let MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_shake256x4"; layout_range "plt_memcpy";
    layout_range "plt_memset"];;


(* ------------------------------------------------------------------------- *)
(* The context is aligned to 32 bytes within the stack frame, so its address *)
(* depends on whether the stack pointer is a multiple of 32 or just of 16.   *)
(* The four states in it are at offsets 0, 200, 400 and 600, in the form in  *)
(* which their addresses are normalized by the simulation.                   *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_ALIGNED_16_32_STMT =
  `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`;;

let SHAKE256X4_ALIGNED_16_32 = assume_spec SHAKE256X4_ALIGNED_16_32_STMT;;

let SHAKE256X4_CTX_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 479)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 448 else 464))`;;

let SHAKE256X4_CTX_ADDRESS = assume_spec SHAKE256X4_CTX_ADDRESS_STMT;;

let SHAKE256X4_CTX_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 479))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 448 else 464))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC SHAKE256X4_CTX_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let SHAKE256X4_ST =
  [`word_add stackpointer
     (word(if aligned 32 stackpointer then 448 else 464)):int64`;
   `word_add stackpointer
     (word((if aligned 32 stackpointer then 448 else 464) + 200)):int64`;
   `word_add stackpointer
     (word((if aligned 32 stackpointer then 448 else 464) + 400)):int64`;
   `word_add stackpointer
     (word((if aligned 32 stackpointer then 448 else 464) + 600)):int64`];;

let SHAKE256X4_STATES_TAC = MAP_EVERY KECCAK_STATE_AT_TAC SHAKE256X4_ST;;

(* ------------------------------------------------------------------------- *)
(* The number of whole blocks, outlen DIV 136, is computed by udiv, and      *)
(* multiplied back by 136 with mul, to get the number of remaining bytes,    *)
(* outlen MOD 136. The second call of mlk_keccak_squeezeblocks_x4 and the    *)
(* copies are skipped if there are none.                                     *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_MUL136_STMT =
  `!n. word(0 + val(word n:int64) * 136):int64 = word(136 * n)`;;

let SHAKE256X4_MUL136 = assume_spec SHAKE256X4_MUL136_STMT;;

let SHAKE256X4_VAL136_STMT =
  `val(word 136:int64) = 136`;;

let SHAKE256X4_VAL136 = assume_spec SHAKE256X4_VAL136_STMT;;

(*** The bound on outlen, nb whole blocks and rest remaining bytes ***)

let SHAKE256X4_BOUND_TAC =
  SUBGOAL_THEN `outlen < 2 EXP 64` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1824 + n <= 2 EXP 64 ==> n < 2 EXP 64`) THEN
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


(*** The number of blocks, the test of the remainder, and the remainder ***)

let SHAKE256X4_NBLOCKS_TAC =
  RULE_ASSUM_TAC(fun th ->
    if concl th = `outlen DIV 136 = nb` ||
       concl th = `val(word outlen:int64) = outlen`
    then th
    else REWRITE_RULE[SHAKE256X4_VAL136;
                      ASSUME `val(word outlen:int64) = outlen`;
                      ASSUME `outlen DIV 136 = nb`] th);;

let SHAKE256X4_BRANCH_TAC th tm =
  RULE_ASSUM_TAC(fun th' ->
    if is_eq(concl th') && is_cond(rand(concl th'))
    then REWRITE_RULE[th; ASSUME tm] th' else th');;

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


(* ------------------------------------------------------------------------- *)
(* The setup for both proofs, the GOT entry for the stack guard in the form  *)
(* needed by mlk_keccak_absorb_once_x4, and the facts holding at all the     *)
(* intermediate points: the saved registers, the stack guard and the GOT,    *)
(* and the two outputs given on the stack.                                   *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 1824):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `448 <= (if aligned 32 (stackpointer:int64) then 448 else 464) /\
    (if aligned 32 (stackpointer:int64) then 448 else 464) <= 464`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
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
     (mk_const(r,[]))) (19--28);;


let SHAKE256X4_GOT_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
          g:int64`)
         (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC);;


(*** The same for the GOT entry at the offset n from the page, for memset ***)

let SHAKE256X4_GOT_AT_TAC n =
  let pat = parse_term
    (Printf.sprintf
      "read (memory :> bytes64 (word_add (word pc) (word %d))) s = g:int64" n) in
  FIRST_ASSUM(fun th ->
    if can (term_match [] pat) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC);;


let SHAKE256X4_FRAME =
 `read SP s = word_add stackpointer (word 336) /\
  read (memory :> bytes64 (word_add stackpointer (word 336))) s = x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word 344))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 352))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 360))) s = x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 368))) s = x23_init /\
  read (memory :> bytes64 (word_add stackpointer (word 376))) s = x24_init /\
  read (memory :> bytes64 (word_add stackpointer (word 384))) s = x25_init /\
  read (memory :> bytes64 (word_add stackpointer (word 392))) s = x26_init /\
  read (memory :> bytes64 (word_add stackpointer (word 400))) s = x27_init /\
  read (memory :> bytes64 (word_add stackpointer (word 408))) s = x28_init /\
  read (memory :> bytes64 (word_add stackpointer (word 416))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 432))) s = out2 /\
  read (memory :> bytes64 (word_add stackpointer (word 440))) s = out3 /\
  read (memory :> bytes64 (word_add stackpointer (word 1816))) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s = guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
  read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s = mc /\
  read (memory :> bytes(ea,el)) s = ev`;;

let SHAKE256X4_AT t =
  let vs,bod = strip_abs t in list_mk_abs(vs,mk_conj(bod,SHAKE256X4_FRAME));;

(*** The subroutines ***)

let LOCAL_ABSORB_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SQUEEZE_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_ZEROIZE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_ZEROIZE_3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;


(* ------------------------------------------------------------------------- *)
(* The output of SHAKE256 in blocks, as in mlkem_shake256, in terms of the   *)
(* state after absorbing the input as by mlk_keccak_absorb_once_x4, and the  *)
(* first n bytes of one of the buffers holding a block.                      *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_SPONGE_STMT =
  `!(m:byte list) k n.
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
                         2 EXP (8 * 136))))) MOD 2 EXP (8 * n)`;;

let SHAKE256X4_SPONGE = assume_spec SHAKE256X4_SPONGE_STMT;;

let SHAKE256X4_TMP_LEMMA_STMT =
  `!a (S:1600 word) n s:armstate.
        read (memory :> bytes(a,136)) s =
        val S MOD 2 EXP (8 * 136) /\ n <= 136
        ==> read (memory :> bytes(a,n)) s = val S MOD 2 EXP (8 * n)`;;

let SHAKE256X4_TMP_LEMMA = assume_spec SHAKE256X4_TMP_LEMMA_STMT;;


let SHAKE256X4_NSUM_ONE_STMT =
  `!(S:1600 word).
        nsum {i | i < 1}
         (\i. 2 EXP (8 * 136 * i) *
              val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 136)) =
        val(keccak_f1600 S) MOD 2 EXP (8 * 136)`;;

let SHAKE256X4_NSUM_ONE = assume_spec SHAKE256X4_NSUM_ONE_STMT;;


(*** The output of nb whole blocks from mlk_keccak_squeezeblocks_x4 ***)

let SHAKE256X4_NSUM_STMT =
  `!(m:byte list) (S:1600 word) nb.
        (!k n. n <= 136
               ==> num_of_bytelist(list_of_seq (\j. shake256 m (136 * k + j)) n) =
                   val(keccak_squeeze (k + 1) S) MOD 2 EXP (8 * n))
        ==> nsum {i | i < nb}
             (\i. 2 EXP (8 * 136 * i) *
                  val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 136)) =
            num_of_bytelist(list_of_seq (shake256 m) (136 * nb))`;;

let SHAKE256X4_NSUM = assume_spec SHAKE256X4_NSUM_STMT;;

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


(*** The intermediate points: after absorbing, after the whole blocks, ***)
(*** and at the join after the remaining bytes                         ***)

let SHAKE256X4_A1 = SHAKE256X4_AT
 `\s. read X19 s = word outlen /\ read X20 s = word nb /\
      read X21 s =
      word_add stackpointer
       (word(if aligned 32 stackpointer then 448 else 464)) /\
      read X22 s = word 136 /\ read X23 s = out1 /\ read X24 s = out0 /\
      read X25 s = in0 /\ read X26 s = in1 /\ read X27 s = in2 /\
      read X28 s = in3 /\
      read (memory :> bytes(word_add stackpointer
              (word(if aligned 32 stackpointer then 448 else 464)),200)) s =
      val(S0:1600 word) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 448 else 464) + 200)),
              200)) s =
      val(S1:1600 word) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 448 else 464) + 400)),
              200)) s =
      val(S2:1600 word) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 448 else 464) + 600)),
              200)) s =
      val(S3:1600 word)`;;

let SHAKE256X4_A2 = SHAKE256X4_AT
 `\s. read X19 s = word outlen /\ read X20 s = word(136 * nb) /\
      read X21 s =
      word_add stackpointer
       (word(if aligned 32 stackpointer then 448 else 464)) /\
      read X22 s = word 136 /\ read X23 s = out1 /\ read X24 s = out0 /\
      read X25 s = word_add stackpointer (word 1680) /\
      read X26 s = word_add stackpointer (word 1544) /\
      read X27 s = word_add stackpointer (word 1408) /\
      read X28 s = in3 /\
      read (memory :> bytes(out0,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp0) (136 * nb)) /\
      read (memory :> bytes(out1,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp1) (136 * nb)) /\
      read (memory :> bytes(out2,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp2) (136 * nb)) /\
      read (memory :> bytes(out3,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp3) (136 * nb)) /\
      read (memory :> bytes(word_add stackpointer
              (word(if aligned 32 stackpointer then 448 else 464)),200)) s =
      val(keccak_squeeze nb (S0:1600 word)) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 448 else 464) + 200)),
              200)) s =
      val(keccak_squeeze nb (S1:1600 word)) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 448 else 464) + 400)),
              200)) s =
      val(keccak_squeeze nb (S2:1600 word)) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 448 else 464) + 600)),
              200)) s =
      val(keccak_squeeze nb (S3:1600 word))`;;

let SHAKE256X4_A3 = SHAKE256X4_AT
 `\s. read X21 s =
      word_add stackpointer
       (word(if aligned 32 stackpointer then 448 else 464)) /\
      read X28 s = word_add stackpointer (word 1272) /\
      read X27 s = word_add stackpointer (word 1408) /\
      read X26 s = word_add stackpointer (word 1544) /\
      read X25 s = word_add stackpointer (word 1680) /\
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
(* addresses mf and mc in the GOT entries, with their code and data in the   *)
(* region (ea,el). The inputs are four lists of bytes of the same length     *)
(* inlen, at in0, ..., in3, the last given on the stack with inlen, and the  *)
(* outlen bytes of each output, as a number, are the first outlen bytes of   *)
(* shake256 of the corresponding input. The stack is the 1488 bytes of the   *)
(* function and the 336 used by mlk_keccak_absorb_once_x4 below them, and    *)
(* the two 8-byte stack arguments are just above it.                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE256X4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!out0 out1 out2 out3 outlen in0 in1 in2 in3 inlen
   (inp0:byte list) (inp1:byte list) (inp2:byte list) (inp3:byte list)
   guard mf mc ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        LENGTH inp0 = inlen /\ LENGTH inp1 = inlen /\
        LENGTH inp2 = inlen /\ LENGTH inp3 = inlen /\
        PAIRWISE nonoverlapping
         [(out0,outlen); (out1,outlen); (out2,outlen); (out3,outlen);
          (word_sub stackpointer (word 1824),1824)] /\
        ALLPAIRS nonoverlapping
         [(out0,outlen); (out1,outlen); (out2,outlen); (out3,outlen);
          (word_sub stackpointer (word 1824),1824)]
         [(in0,inlen); (in1,inlen); (in2,inlen); (in3,inlen);
          (stackpointer,16); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
          (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
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
                memory :> bytes(word_sub stackpointer (word 1824),1824)])`;;

let MLKEM_NATIVE_SHAKE256X4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHAKE256X4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;


(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contracts for memset and memcpy. The events depend on the address of the  *)
(* stack guard and on the input in3 given on the stack, and whether there    *)
(* is a remainder depends on outlen. The events are split at the             *)
(* intermediate points of the correctness proof, from the end, with the      *)
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
        (f_ev_blocks in0 in1 in2 in3 out0 out1 out2 out3 outlen inlen guard
                     mf mc pc stackpointer returnaddress)
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
   `stackpointer:int64`; `returnaddress:int64`;
   `e2:(uarch_event)list`];;

(*** EXISTS_E2_TAC with nb and rest expanded, allowing the f_ev_... ***)

let SHAKE256X4_EXISTS_E2_TAC0 =
  let pfx = ref ["f_events_callee"; "f_ev_"] in
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if c = `outlen DIV 136 = nb` || c = `outlen MOD 136 = rest`
      then SYM th else failwith "") asl in
    if ths = [] then ALL_TAC
    else REWRITE_TAC ths THEN
         RULE_ASSUM_TAC(fun th ->
           let c = concl th in
           if is_eq c && is_var(lhand c) && String.sub (name_of(lhand c)) 0 2 = "e2"
           then REWRITE_RULE ths th else th)) THEN
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

let SHAKE256X4_EXISTS_E2_TAC = SHAKE256X4_EXISTS_E2_TAC0;;

let SHAKE256X4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_Os_mc,MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_Os_mc,safety_th)
      ilist n THENL
     [SHAKE256X4_EXISTS_E2_TAC; LABEL_TAC name safety_th]);;

let SHAKE256X4_LIBC_SAFE_CALL_TAC name n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true
      MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC th
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
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC (1--5) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC (6--13) THEN
  SHAKE256X4_CTX_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC (14--27) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC 27 THEN
  SHAKE256X4_LIBC_SAFE_CALL_TAC "H_MEMSET" 32 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC (33--40) THEN
  SHAKE256X4_NBLOCKS_TAC THEN SHAKE256X4_GOT_TAC THEN
  SHAKE256X4_SAFE_CALL_TAC "H_ABSORB"
   [`e:(uarch_event)list`; `read X0 s`; `136`; `read X2 s`; `read X3 s`;
    `read X4 s`; `read X5 s`; `inlen:num`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 41 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_DISCHARGE_ASSOC_TAC;;

(*** The whole blocks ***)

let SHAKE256X4_SAFE_BLOCKS_TAC =
  SHAKE256X4_SAFE_INIT_TAC THEN
  SUBGOAL_THEN `136 * nb <= outlen` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`136 * nb + rest = outlen`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC (1--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SHAKE256X4_MUL136]) THEN
  SHAKE256X4_SAFE_CALL_TAC "H_SQUEEZE"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `nb:num`; `read X5 s`; `136`; `pc:num`; `read SP s`;
    `read X30 s`] 12 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_DISCHARGE_TAC;;

(*** The remaining bytes ***)

let SHAKE256X4_SAFE_REST_TAC =
  ASM_CASES_TAC `rest = 0` THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_SAFE_INIT_OPAQUE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC (1--2) THEN
  SHAKE256X4_NBLOCKS_TAC THEN
  SHAKE256X4_REST_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC (3--3) THENL
   [SHAKE256X4_BRANCH_TAC TRUTH `rest = 0` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SHAKE256X4_DISCHARGE_TAC;
    ALL_TAC] THEN
  SHAKE256X4_BRANCH_TAC TRUTH `~(rest = 0)` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC (4--11) THEN
  SHAKE256X4_SAFE_CALL_TAC "H_SQUEEZE"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `1`; `read X5 s`; `136`; `pc:num`; `read SP s`;
    `read X30 s`] 12 THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC (k0--k) THEN
    LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC k THEN
    SHAKE256X4_LIBC_SAFE_CALL_TAC "H_MEMCPY" (k + 5))
   [13,16; 22,25; 31,35; 41,45] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_DISCHARGE_ASSOC_TAC;;

(*** Zeroing the context and the buffers, the stack guard and the return ***)

let SHAKE256X4_SAFE_END_TAC =
  SHAKE256X4_SAFE_INIT_OPAQUE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC (1--3) THEN
  SHAKE256X4_GOT_AT_TAC 131048 THEN
  SHAKE256X4_SAFE_CALL_TAC "H_ZEROIZE"
   [`e:(uarch_event)list`; `read X0 s`; `800`; `pc:num`; `read SP s`;
    `read X30 s`] 4 THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC (k0--k) THEN
    SHAKE256X4_GOT_AT_TAC 131048 THEN
    SHAKE256X4_SAFE_CALL_TAC "H_ZEROIZE"
     [`e:(uarch_event)list`; `read X0 s`; `136`; `pc:num`; `read SP s`;
      `read X30 s`] (k + 1))
   [5,7; 9,11; 13,15; 17,19] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC (21--21) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_OS_EXEC (22--35) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHAKE256X4_DISCHARGE_ASSOC_TAC;;

let MLKEM_NATIVE_SHAKE256X4_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_safety_contract mf ea el ev /\
     memcpy_safety_contract mc ea el ev
     ==> exists f_events.
          forall e out0 out1 out2 out3 outlen in0 in1 in2 in3 inlen guard
                 pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
            [out0,outlen; out1,outlen; out2,outlen; out3,outlen;
             word_sub stackpointer (word 1824),1824] /\
           ALLPAIRS nonoverlapping
            [out0,outlen; out1,outlen; out2,outlen; out3,outlen;
             word_sub stackpointer (word 1824),1824]
            [in0,inlen; in1,inlen; in2,inlen; in3,inlen; stackpointer,16;
             word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8;
             word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_native_libmlkem_gcc12_Os_mc /\
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
                               (word_sub stackpointer (word 1824))
                               returnaddress /\
                        memaccess_inbounds e2
                         [in0,inlen; in1,inlen; in2,inlen; in3,inlen;
                          out0,outlen; out1,outlen; out2,outlen; out3,outlen;
                          stackpointer,16;
                          word_sub stackpointer (word 1824),1824;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                          word(pc + got_memset),8;
                          word(pc + got_memcpy),8; ea,el]
                         [out0,outlen; out1,outlen; out2,outlen; out3,outlen;
                          word_sub stackpointer (word 1824),1824]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(out0,outlen); memory :> bytes(out1,outlen);
                   memory :> bytes(out2,outlen); memory :> bytes(out3,outlen);
                   memory :> bytes(word_sub stackpointer (word 1824),1824)])`;;

let MLKEM_NATIVE_SHAKE256X4_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHAKE256X4_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
