(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 of four inputs of the same length, with four outputs of any      *)
(* length. This is the code for mlkem_shake256x4 from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 as one translation *)
(* unit (see mlkem_native/README.md), which zeroes a context of four states  *)
(* on the stack with memset, absorbs the inputs into it with                 *)
(* mlk_keccak_absorb_once_x4, squeezes the whole blocks of 136 bytes, the    *)
(* rate of SHAKE256, directly into the outputs with                          *)
(* mlk_keccak_squeezeblocks_x4, and the rest of the outputs through four     *)
(* buffers on the stack (one more call of mlk_keccak_squeezeblocks_x4 and    *)
(* four calls of memcpy), before zeroing the context with memset and the     *)
(* buffers with stores. It has the specification of the gcc12_O2 build, with *)
(* these differences: the compiler specialized the function to the input     *)
(* length 33 (it passes the constant to mlk_keccak_absorb_once_x4 and does   *)
(* not read the length from the stack), so inlen = 33 here and only the      *)
(* input in3 is on the stack; the stack is the 1488 bytes of the function    *)
(* and the 288 used by mlk_keccak_squeezeblocks_x4 below them. It is         *)
(* verified in the whole image (see libmlkem.ml), assuming the contracts for *)
(* memset and memcpy in utils/mlkem_native_libc.ml. The result is shake256   *)
(* of common/fips202.ml for each input.                                      *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccak_absorb_once_x4.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccak_squeezeblocks_x4.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(*** The code in the image, and the PLT stubs for memcpy and memset:

    mlkem_shake256x4:
     +0x0  sub     sp, sp, #0x5d0
  adrp1:
     +0x4  adrp    x8, <page>
     +0x8  ldr     x8, [x8, #4088]    // got_stack_chk_guard
     +0xc  stp     x19, x20, [sp]
    +0x10  mov     x19, #0xf0f0f0f0f0f0f0f0
    +0x14  movk    x19, #0xf0f1
    +0x18  stp     x21, x22, [sp, #16]
    +0x1c  mov     x20, x5
    +0x20  umulh   x19, x4, x19
    +0x24  ldr     x22, [sp, #1488]
    +0x28  stp     x23, x24, [sp, #32]
    +0x2c  add     x23, sp, #0x8f
    +0x30  stp     x25, x26, [sp, #48]
    +0x34  and     x23, x23, #0xffffffffffffffe0
    +0x38  mov     x25, x7
    +0x3c  stp     x27, x28, [sp, #64]
    +0x40  mov     x24, x4
    +0x44  mov     x21, x6
    +0x48  str     x30, [sp, #80]
    +0x4c  mov     x28, x0
    +0x50  str     x3, [sp, #104]
    +0x54  mov     x27, x1
    +0x58  mov     x26, x2
    +0x5c  mov     x0, x23
    +0x60  ldr     x1, [x8]
    +0x64  str     x1, [sp, #1480]
    +0x68  mov     x1, #0x0
    +0x6c  mov     x2, #0x320
    +0x70  bl      memset (through plt_memset)
  after_memset_1:
    +0x74  lsr     x19, x19, #7
    +0x78  mov     x4, x25
    +0x7c  mov     x3, x21
    +0x80  mov     x2, x20
    +0x84  mov     x5, x22
    +0x88  mov     x0, x23
    +0x8c  mov     x6, #0x21
    +0x90  mov     w1, #0x88
    +0x94  bl      mlk_keccak_absorb_once_x4
  after_mlk_keccak_absorb_once_x4:
    +0x98  ldr     x3, [sp, #104]
    +0x9c  mov     x4, x19
    +0xa0  add     x19, x19, x19, lsl #4
    +0xa4  mov     x5, x23
    +0xa8  mov     x2, x26
    +0xac  mov     x1, x27
    +0xb0  lsl     x25, x19, #3
    +0xb4  mov     x0, x28
    +0xb8  mov     w6, #0x88
    +0xbc  bl      mlk_keccak_squeezeblocks_x4
  after_mlk_keccak_squeezeblocks_x4_1:
    +0xc0  add     x19, sp, #0x540
    +0xc4  subs    x24, x24, x25
    +0xc8  b.ne    +0x178
    +0xcc  add     x20, sp, #0x4b8
    +0xd0  add     x21, sp, #0x430
    +0xd4  add     x22, sp, #0x3a8
  join1:
    +0xd8  mov     x0, x23
    +0xdc  mov     x2, #0x320
    +0xe0  mov     w1, #0x0
    +0xe4  bl      memset (through plt_memset)
  after_memset_2:
    +0xe8  movi    v0.4s, #0x0
    +0xec  str     xzr, [x22, #128]
    +0xf0  stp     q0, q0, [x22]          ... (x22 to x22 + 96)
           (and the same for x21, x20, x19: 136 bytes of each)
  adrp2:
   +0x13c  adrp    x0, <page>
   +0x140  ldr     x0, [x0, #4088]        // got_stack_chk_guard
   +0x144  ldr     x2, [sp, #1480]
   +0x148  ldr     x1, [x0]
   +0x14c  subs    x2, x2, x1
   +0x150  mov     x1, #0x0
   +0x154  b.ne    stack_chk_fail
   +0x158  ldp     x19, x20, [sp]
           ... (restores the registers)
   +0x170  add     sp, sp, #0x5d0
  ret:
   +0x174  ret
   +0x178  mov     x5, x23                (the remaining bytes, if any)
   +0x17c  mov     x3, x19
   +0x180  mov     w6, #0x88
   +0x184  mov     x4, #0x1
   +0x188  add     x20, sp, #0x4b8
   +0x18c  add     x21, sp, #0x430
   +0x190  add     x22, sp, #0x3a8
   +0x194  mov     x2, x20
   +0x198  mov     x1, x21
   +0x19c  mov     x0, x22
   +0x1a0  bl      mlk_keccak_squeezeblocks_x4
  after_mlk_keccak_squeezeblocks_x4_2:
   +0x1a4  mov     x2, x24
   +0x1a8  mov     x1, x22
   +0x1ac  add     x0, x28, x25
   +0x1b0  bl      memcpy (through plt_memcpy)
           ... (the same for x21 and x27, x20 and x26, x19 and the out3
           saved at [sp, #104])
   +0x1e8  b       join1
   +0x1ec  bl      stack_chk_fail
 ***)

let MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlkem_shake256x4"; layout_range "plt_memcpy";
    layout_range "plt_memset"];;


let READ_MEMORY_BYTES_PREFIX = prove
 (`!a:int64 n x l s:armstate.
        read (memory :> bytes(a,n)) s = x /\ l <= n
        ==> read (memory :> bytes(a,l)) s = x MOD 2 EXP (8 * l)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

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
        ==> word_and (word_add sp (word 431)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 416 else 400))`,
  REWRITE_TAC[SHAKE256X4_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let SHAKE256X4_CTX_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 431))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 416 else 400))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC SHAKE256X4_CTX_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;


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


(*** The bound on outlen, nb whole blocks and rest remaining bytes ***)

let SHAKE256X4_BOUND_TAC =
  SUBGOAL_THEN `outlen < 2 EXP 64` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1776 + n <= 2 EXP 64 ==> n < 2 EXP 64`) THEN
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


(*** The output of SHAKE256 in blocks, as numbers: the first 136 * k bytes
     from the blocks squeezed from the state S after absorbing ***)

let SHAKE256X4_NSUM = prove
 (`!(m:byte list) k.
        num_of_bytelist(list_of_seq (shake256 m) (136 * k)) =
        nsum {i | i < k}
         (\i. 2 EXP (8 * 136 * i) *
              val(keccak_squeeze (i + 1)
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
                           2 EXP (8 * 136))))) MOD 2 EXP (8 * 136))`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; NSUM_CLAUSES_NUMSEG_LT; list_of_seq;
                num_of_bytelist];
    REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; ARITH_RULE `136 * SUC k = 136 * k + 136`;
                NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
    ASM_REWRITE_TAC[GSYM ADD1] THEN
    MP_TAC(SPECL [`m:byte list`; `k:num`; `136`] SHAKE256X4_SPONGE) THEN
    REWRITE_TAC[LE_REFL] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ADD1; MULT_ASSOC] THEN REWRITE_TAC[ADD_SYM]]);;


(*** The four states of the context, at offsets 0, 200, 400 and 600 ***)

let SHAKE256X4_ST =
  [`word_add stackpointer
     (word(if aligned 32 stackpointer then 416 else 400)):int64`;
   `word_add stackpointer
     (word((if aligned 32 stackpointer then 416 else 400) + 200)):int64`;
   `word_add stackpointer
     (word((if aligned 32 stackpointer then 416 else 400) + 400)):int64`;
   `word_add stackpointer
     (word((if aligned 32 stackpointer then 416 else 400) + 600)):int64`];;

let SHAKE256X4_STATES_TAC = MAP_EVERY KECCAK_STATE_AT_TAC SHAKE256X4_ST;;

(*** The first n bytes of a block squeezed into a buffer ***)

let KECCAK_SQUEEZE_1 = prove
 (`!S:1600 word. keccak_squeeze 1 S = keccak_f1600 S`,
  REWRITE_TAC[ONE; keccak_squeeze]);;
let SHAKE256X4_BUF_LEMMA = prove
 (`!a (S:1600 word) n s:armstate.
        read (memory :> bytes(a,136 * 1)) s =
        nsum {i | i < 1}
         (\i. 2 EXP (8 * 136 * i) *
              val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 136)) /\ n <= 136
        ==> read (memory :> bytes(a,n)) s =
            val(keccak_f1600 S) MOD 2 EXP (8 * n)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{i | i < 1} = {i | i < SUC 0}` SUBST1_TAC THENL
   [REWRITE_TAC[ONE]; ALL_TAC] THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; MULT_CLAUSES; EXP; ADD_CLAUSES;
              keccak_squeeze; KECCAK_SQUEEZE_1] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `136`; `val(keccak_f1600 (S:1600 word)) MOD 2 EXP (8 * 136)`;
                 `n:num`; `s:armstate`] READ_MEMORY_BYTES_PREFIX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 136 ==> MIN (8 * 136) (8 * n) = 8 * n`]);;

(* ------------------------------------------------------------------------- *)
(* The setup for the proof: the saved registers, the stack guard and the GOT *)
(* entries for memset and memcpy, and the facts holding at all the           *)
(* intermediate points.                                                      *)
(* ------------------------------------------------------------------------- *)

let SHAKE256X4_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 1776):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `400 <= (if aligned 32 (stackpointer:int64) then 416 else 400) /\
    (if aligned 32 (stackpointer:int64) then 416 else 400) <= 416`
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

let SHAKE256X4_FRAME =
 `read SP s = word_add stackpointer (word 288) /\
  read (memory :> bytes64 (word_add stackpointer (word 288))) s = x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word 296))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 304))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 312))) s = x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 320))) s = x23_init /\
  read (memory :> bytes64 (word_add stackpointer (word 328))) s = x24_init /\
  read (memory :> bytes64 (word_add stackpointer (word 336))) s = x25_init /\
  read (memory :> bytes64 (word_add stackpointer (word 344))) s = x26_init /\
  read (memory :> bytes64 (word_add stackpointer (word 352))) s = x27_init /\
  read (memory :> bytes64 (word_add stackpointer (word 360))) s = x28_init /\
  read (memory :> bytes64 (word_add stackpointer (word 368))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 392))) s = out3 /\
  read (memory :> bytes64 (word_add stackpointer (word 1768))) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
  guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
  read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s = mc /\
  read (memory :> bytes(ea,el)) s = ev`;;

let SHAKE256X4_AT t =
  let vs,bod = strip_abs t in list_mk_abs(vs,mk_conj(bod,SHAKE256X4_FRAME));;

let SHAKE256X4_BRANCH_TAC th tm =
  RULE_ASSUM_TAC(fun th' ->
    if is_eq(concl th') && is_cond(rand(concl th'))
    then REWRITE_RULE[th; ASSUME tm] th' else th');;


(*** The first rest bytes of a buffer holding one block ***)

let SHAKE256X4_BUF_TAC a =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes",_),aa))),_)),_)
        when aa = mk_pair(a,`136 * 1`) ->
          ASSUME_TAC(MATCH_MP SHAKE256X4_BUF_LEMMA
                      (CONJ th (ASSUME `rest <= 136`)))
    | _ -> NO_TAC);;

(*** The input length, 33, in the assumptions about the inputs ***)

let SHAKE256X4_INLEN_TAC =
  let t = `inlen = 33` in
  RULE_ASSUM_TAC(fun th -> if concl th = t then th else REWRITE_RULE[ASSUME t] th);;

(*** The blocks squeezed from each absorbed state, in two forms ***)

let SHAKE256X4_NSUM_TAC =
  MAP_EVERY (fun (inp,sv) ->
    let t = rhs(concl(BETA_CONV
             (mk_comb(SHAKE256X4_ABSORBED,
                      mk_comb(`num_of_bytelist:byte list->num`,inp))))) in
    let len = ASSUME(mk_eq(mk_comb(`LENGTH:byte list->num`,inp),
                           `inlen:num`)) in
    ASSUME_TAC(REWRITE_RULE[len; ASSUME(mk_eq(t,sv))]
                (SPEC inp SHAKE256X4_NSUM)))
   (zip [`inp0:byte list`; `inp1:byte list`; `inp2:byte list`;
         `inp3:byte list`]
        [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`]);;

(*** The subroutines ***)

let LOCAL_ABSORB_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SQUEEZE_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

(*** The intermediate points: after absorbing, after the whole blocks, and
     at the end of the outputs ***)

let SHAKE256X4_A1 = SHAKE256X4_AT
 `\s. read X19 s = word nb /\ read X24 s = word outlen /\
      read X23 s =
      word_add stackpointer
       (word(if aligned 32 stackpointer then 416 else 400)) /\
      read X26 s = out2 /\ read X27 s = out1 /\ read X28 s = out0 /\
      read (memory :> bytes(word_add stackpointer
              (word(if aligned 32 stackpointer then 416 else 400)),200)) s =
      val(S0:1600 word) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 416 else 400) + 200)),
              200)) s =
      val(S1:1600 word) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 416 else 400) + 400)),
              200)) s =
      val(S2:1600 word) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 416 else 400) + 600)),
              200)) s =
      val(S3:1600 word)`;;

let SHAKE256X4_A2 = SHAKE256X4_AT
 `\s. read X24 s = word outlen /\ read X25 s = word(136 * nb) /\
      read X23 s =
      word_add stackpointer
       (word(if aligned 32 stackpointer then 416 else 400)) /\
      read X26 s = out2 /\ read X27 s = out1 /\ read X28 s = out0 /\
      read (memory :> bytes(out0,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp0) (136 * nb)) /\
      read (memory :> bytes(out1,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp1) (136 * nb)) /\
      read (memory :> bytes(out2,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp2) (136 * nb)) /\
      read (memory :> bytes(out3,136 * nb)) s =
      num_of_bytelist(list_of_seq (shake256 inp3) (136 * nb)) /\
      read (memory :> bytes(word_add stackpointer
              (word(if aligned 32 stackpointer then 416 else 400)),200)) s =
      val(keccak_squeeze nb (S0:1600 word)) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 416 else 400) + 200)),
              200)) s =
      val(keccak_squeeze nb (S1:1600 word)) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 416 else 400) + 400)),
              200)) s =
      val(keccak_squeeze nb (S2:1600 word)) /\
      read (memory :> bytes(word_add stackpointer
              (word((if aligned 32 stackpointer then 416 else 400) + 600)),
              200)) s =
      val(keccak_squeeze nb (S3:1600 word))`;;

let SHAKE256X4_A3 = SHAKE256X4_AT
 `\s. read X19 s = word_add stackpointer (word 1632) /\
      read X20 s = word_add stackpointer (word 1496) /\
      read X21 s = word_add stackpointer (word 1360) /\
      read X22 s = word_add stackpointer (word 1224) /\
      read X23 s =
      word_add stackpointer
       (word(if aligned 32 stackpointer then 416 else 400)) /\
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
(* region (ea,el). The inputs are four lists of bytes of length 33, at in0,  *)
(* ..., in3, the last given on the stack, and the outlen bytes of each       *)
(* output, as a number, are the first outlen bytes of shake256 of the        *)
(* corresponding input. The stack is the 1488 bytes of the function and the  *)
(* 288 used by mlk_keccak_squeezeblocks_x4 below them, and the 8-byte stack  *)
(* argument is just above it.                                                *)
(* ------------------------------------------------------------------------- *)


let MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT = prove
 (`!out0 out1 out2 out3 outlen in0 in1 in2 in3 inlen
   (inp0:byte list) (inp1:byte list) (inp2:byte list) (inp3:byte list)
   guard mf mc ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ inlen = 33 /\
        LENGTH inp0 = inlen /\ LENGTH inp1 = inlen /\
        LENGTH inp2 = inlen /\ LENGTH inp3 = inlen /\
        PAIRWISE nonoverlapping
         [(out0,outlen); (out1,outlen); (out2,outlen); (out3,outlen);
          (word_sub stackpointer (word 1776),1776)] /\
        ALLPAIRS nonoverlapping
         [(out0,outlen); (out1,outlen); (out2,outlen); (out3,outlen);
          (word_sub stackpointer (word 1776),1776)]
         [(in0,inlen); (in1,inlen); (in2,inlen); (in3,inlen);
          (stackpointer,8); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
          (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlkem_shake256x4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS
                   [out0; out1; out2; out3; word outlen; in0; in1; in2] s /\
                  read (memory :> bytes64 stackpointer) s = in3 /\
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
                memory :> bytes(word_sub stackpointer (word 1776),1776)])`,
  MAP_EVERY X_GEN_TAC
   [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`; `outlen:num`;
    `in0:int64`; `in1:int64`; `in2:int64`; `in3:int64`; `inlen:num`;
    `inp0:byte list`; `inp1:byte list`; `inp2:byte list`; `inp3:byte list`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 1776 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (LABEL_TAC "H_MEMSET" o REWRITE_RULE[memset_contract])
   (CONJUNCTS_THEN2
    (LABEL_TAC "H_MEMCPY" o REWRITE_RULE[memcpy_contract])
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  SHAKE256X4_SETUP_TAC THEN SHAKE256X4_BOUND_TAC THEN
  SHAKE256X4_ABSORBED_TAC THEN SHAKE256X4_NSUM_TAC THEN

  (*** Zeroing the context with memset, and the absorption ***)

  ENSURES_SEQUENCE_TAC
   `pc + mlkem_shake256x4_after_mlk_keccak_absorb_once_x4` SHAKE256X4_A1 THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC (1--2) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC (3--14) THEN
    SHAKE256X4_CTX_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC (15--29) THEN
    LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC 29 THEN
    LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC
     [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 34 THEN
    MEMSET_ZERO_BYTES_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC (35--43) THEN
    SHAKE256X4_NBLOCKS_TAC THEN SHAKE256X4_GOT_TAC THEN
    SHAKE256X4_INLEN_TAC THEN
    LOCAL_ABSORB_X4_TAC
     [`read X0 s`; `136`; `read X2 s`; `read X3 s`; `read X4 s`;
      `read X5 s`; `inlen:num`; `num_of_bytelist(inp0:byte list)`;
      `num_of_bytelist(inp1:byte list)`; `num_of_bytelist(inp2:byte list)`;
      `num_of_bytelist(inp3:byte list)`; `guard:int64`; `pc:num`;
      `read SP s`; `read X30 s`] 44 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The whole blocks ***)

  ENSURES_SEQUENCE_TAC
   `pc + mlkem_shake256x4_after_mlk_keccak_squeezeblocks_x4_1`
   SHAKE256X4_A2 THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    SHAKE256X4_STATES_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC (1--10) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SHAKE256X4_MUL136]) THEN
    LOCAL_SQUEEZE_X4_TAC
     [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `nb:num`;
      `read X5 s`; `136`; `S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
      `S3:1600 word`; `pc:num`; `read SP s`; `read X30 s`] 11 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The remaining bytes, if any, through the buffers on the stack ***)

  ENSURES_SEQUENCE_TAC
   `pc + mlkem_shake256x4_join1` SHAKE256X4_A3 THEN CONJ_TAC THENL
   [ASM_CASES_TAC `rest = 0` THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC (1--2) THEN
    SHAKE256X4_REST_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC (3--3) THENL
     [SHAKE256X4_BRANCH_TAC TRUTH `rest = 0` THEN
      ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC (4--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `outlen = 136 * nb` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`rest = 0`; `136 * nb + rest = outlen`] THEN
        ARITH_TAC;
        ASM_REWRITE_TAC[]];
      (SHAKE256X4_BRANCH_TAC TRUTH `~(rest = 0)` THEN
       ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC (4--14) THEN
       SHAKE256X4_STATES_TAC THEN
       LOCAL_SQUEEZE_X4_TAC
        [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `1`;
         `read X5 s`; `136`; `keccak_squeeze nb (S0:1600 word)`;
         `keccak_squeeze nb (S1:1600 word)`;
         `keccak_squeeze nb (S2:1600 word)`;
         `keccak_squeeze nb (S3:1600 word)`; `pc:num`; `read SP s`;
         `read X30 s`] 15 THEN
       RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
       MAP_EVERY (fun (a,sv,k0,k) ->
         SHAKE256X4_BUF_TAC a THEN
         ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC (k0--k) THEN
         LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC k THEN
         LIBC_CALL_TAC "H_MEMCPY" MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC
          [`read X0 s`; `read X1 s`; `read X2 s`;
           vsubst [sv,`S:1600 word`]
            `val(keccak_f1600(keccak_squeeze nb (S:1600 word))) MOD
             2 EXP (8 * rest)`;
           `read X30 s`] (k + 5))
        [`word_add (stackpointer:int64) (word 1224)`,`S0:1600 word`,16,19;
         `word_add (stackpointer:int64) (word 1360)`,`S1:1600 word`,25,28;
         `word_add (stackpointer:int64) (word 1496)`,`S2:1600 word`,34,37;
         `word_add (stackpointer:int64) (word 1632)`,`S3:1600 word`,43,47] THEN
       ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC (53--53) THEN
       ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
       SUBGOAL_THEN `outlen = 136 * nb + rest` SUBST1_TAC THENL
        [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       REPEAT CONJ_TAC THEN
       REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE;
                   NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
       REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
       AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[] THEN
       REWRITE_TAC[GSYM ADD1; keccak_squeeze])];
    ALL_TAC] THEN

  (*** Zeroing the context and the buffers, the stack guard, the return ***)

  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC (1--4) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC 4 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 9 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC (10--31) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_EXEC (32--45) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;
