(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  Prove a property of a program that stores through an AVX-512 write mask.
******************************************************************************)

needs "x86/proofs/base.ml";;

(* The following program, 'avx512_mask.S',

  0:   c5 fc 46 c8             kxnorw    %k0,%k0,%k1
  4:   c4 e3 f9 30 c9 0d       kshiftrw  $0xd,%k1,%k1
  a:   62 f1 fe 49 7f 07       vmovdqu64 %zmm0,(%rdi) with write mask k1
 10:   62 f2 ed 49 64 cb       vpblendmq %zmm3,%zmm2,%zmm1 with mask k1

  .. sets the low 16 bits of the 64-bit opmask register k1 to ones and the
  other bits to zero (kxnorw of k0 with itself), shifts those 16 bits right
  by 13 so that only the low three bits are left (k1 = 7), and then stores
  zmm0 to the 64 bytes at rdi under the write mask k1. A masked store
  writes quadword i (bytes 8*i .. 8*i+7) only if bit i of the mask is set.
  So only the first three quadwords, the low 24 bytes of zmm0, are written,
  and the other 40 bytes of memory keep their old values. Finally it
  blends zmm2 and zmm3 into zmm1 under the same mask: a masked instruction
  with register operands only.

  Let's prove this. We also prove what the program leaves in the list of
  events (read events s), which records the memory accesses and other
  observable behaviour of the program, for the safety and constant-time
  proofs; see safety.ml. *)

let avx512_mask_mc = define_assert_from_elf "avx512_mask_mc"
  "x86/tutorial/avx512_mask.o"
[
  0xc5; 0xfc; 0x46; 0xc8;        (* KXNORW (%_% k1) (%_% k0) (%_% k0) *)
  0xc4; 0xe3; 0xf9; 0x30; 0xc9; 0x0d;
                                 (* KSHIFTRW (%_% k1) (%_% k1) (word 13) *)
  0x62; 0xf1; 0xfe; 0x49; 0x7f; 0x07;
                                 (* VMOVDQU64 (Memop ..) (%_% zmm0) .. *)
  0x62; 0xf2; 0xed; 0x49; 0x64; 0xcb
                       (* VPBLENDMQ (%_% zmm1) (%_% zmm2) (%_% zmm3) .. *)
];;

let EXEC = X86_MK_EXEC_RULE avx512_mask_mc;;

(* The proof differs from the earlier tutorials in three ways.

   1. zmm0 is a 512-bit register. X86_STEPS_TAC records what it learns
      about the vector registers in one of two equivalent forms, called
      views, chosen by the flag x86_zmm_view. In the default YMM view, a
      vector operand becomes YMMn or XMMn: YMMn is the low 256 bits of
      the 512-bit register ZMMn, and writing YMMn clears bits 256..511.
      The facts then say nothing about bits 256..511, so this view
      refuses 512-bit operands. In the ZMM view, every vector operand is
      a part of ZMMn, so the facts are about whole 512-bit registers.
      The existing AVX2 proofs use the YMM view. X86_ZMM_VIEW_TAC tac
      runs the tactic tac in the ZMM view and then restores the previous
      view.

   2. The opmask registers k0..k7 are components like RAX or ZMM0, called
      K0..K7 in the model. Here we only need K1.

   3. A masked store records two events: the value of the mask,
      EventX86Opmask (word 7), then the store, EventStore (rdi,64). On
      the hardware the store writes only the bytes that the mask selects,
      and the other bytes cannot fault. The model records a store of all
      64 bytes, which over-approximates the access, and it records the
      mask, so that a constant-time proof must show that the mask is
      public. New events go in front of the old list e, so the newest
      event comes first.

   4. The blend, which only has register operands, records no event:
      its mask stays out of the events. On the hardware the timing of a
      masked operation that does not access memory does not depend on
      the mask, so a constant-time proof may use a secret mask there,
      for example to select between two values. *)

(* After the four steps, the symbolic simulator knows the 512-bit memory
   value at rdi. The write mask k1 = 7 has been read from K1, and the model
   expands it to a 512-bit mask in which bit i is set if bit (i DIV 64) of
   the opmask is set (one opmask bit per quadword). So we first show that for
   k1 = 7 this is the set of the lowest 192 bits (3 quadwords). *)

let DIMINDEX_192 = DIMINDEX_CONV `dimindex(:192)`;;
let DIMINDEX_320 = DIMINDEX_CONV `dimindex(:320)`;;

let BIT_WORD7 = prove
 (`!j. j < 8 ==> (bit j (word 7:64 word) <=> j < 3)`,
  REWRITE_TAC[BIT_WORD; DIMINDEX_64] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let MASK7_BITS = prove
 (`{i | i < 512 /\ bit (i DIV 64) (word 7:64 word)} = {i | i < 192}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i < 512` THENL
   [MP_TAC(SPEC `i DIV 64` BIT_WORD7) THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN ARITH_TAC]);;

(* Merging masking keeps the masked bits from the new value z and the
   others from the old value. With the mask of the low 192 bits, the
   result is the low 192 bits of z on top of bits 192..511 of the old
   value. *)

let MERGE_192 = prove
 (`!z old:512 word.
     word_or (word_and (word_of_bits {i | i < 192}) z)
             (word_and (word_not (word_of_bits {i | i < 192})) old) =
     word_join (word_subword old (192,320):320 word) (word_zx z:192 word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_AND; BIT_WORD_NOT; BIT_WORD_OF_BITS;
              IN_ELIM_THM; BIT_WORD_JOIN; BIT_WORD_SUBWORD; BIT_WORD_ZX;
              DIMINDEX_512; DIMINDEX_320; DIMINDEX_192] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i < 192` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `192 + (i - 192) = i` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i - 192 < MIN 320 320` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[MIN] THEN ASM_ARITH_TAC);;

(* Memory reads are numbers, so we also need to go from the 512-bit word
   that was written to the numbers stored in the first 24 bytes and the
   last 40 bytes. If the number n is the word hi:lo, then n MOD 2^192 is lo
   and n DIV 2^192 is hi. *)

let SPLIT_512 = prove
 (`!(n:num) (hi:320 word) (lo:192 word).
      n < 2 EXP 512 /\ word n = (word_join hi lo:512 word)
      ==> n MOD 2 EXP 192 = val lo /\ n DIV 2 EXP 192 = val hi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n = val(word_join (hi:320 word) (lo:192 word):512 word)`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) then SUBST1_TAC (SYM th) else NO_TAC) THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_512] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `n = 2 EXP 192 * val(hi:320 word) + val(lo:192 word)`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && lhs(concl th) = `n:num` then MP_TAC th
      else NO_TAC) THEN
    SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_192; DIMINDEX_320; DIMINDEX_512;
             ARITH];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `2 EXP 192`; `val(hi:320 word)`; `val(lo:192 word)`]
               DIVMOD_UNIQ) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [POP_ASSUM MP_TAC THEN CONV_TAC(DEPTH_CONV NUM_EXP_CONV) THEN ARITH_TAC;
      MP_TAC(ISPEC `lo:192 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_192]];
    DISCH_THEN(fun th -> ACCEPT_TAC(CONJ (CONJUNCT2 th) (CONJUNCT1 th)))]);;


let AVX512_MASK_SPEC = prove(
  `forall pc a (z:512 word) (old:512 word) (e:(uarch_event)list).
    // The store target does not overlap the program ..
    nonoverlapping (word pc:int64, LENGTH avx512_mask_mc) (word a:int64, 64)
    ==> ensures x86
      // Precondition: the 64 bytes at rdi hold the 512-bit value old
      (\s. bytes_loaded s (word pc) avx512_mask_mc /\
           read RIP s = word pc /\
           read RDI s = word a /\
           read ZMM0 s = z /\
           read (memory :> bytes512 (word a)) s = old /\
           read events s = e)
      // Postcondition
      (\s. read RIP s = word (pc + 22) /\
           // k1 = 7
           read K1 s = word 7 /\
           // The low 24 bytes of zmm0 were stored
           read (memory :> bytes(word a,24)) s = val (word_zx z:192 word) /\
           // The remaining 40 bytes are unchanged
           read (memory :> bytes(word (a + 24),40)) s =
             val (word_subword old (192,320):320 word) /\
           // Store event, then mask event, on top of the old events;
           // the blend adds no event
           read events s = CONS (EventStore (word a,64))
                                (CONS (EventX86Opmask (word 7)) e))
      // Registers and memory that may change; the model may change the
      // whole 64 bytes (it writes back the old value to the unmasked part)
      (MAYCHANGE [RIP] ,, MAYCHANGE [K1] ,, MAYCHANGE [ZMM1] ,,
       MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word a,64)])`,
  REWRITE_TAC[fst EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Run the four instructions in the ZMM view. After the first two, K1
     is word 7, and the store and the blend read K1 to build their mask. *)
  X86_ZMM_VIEW_TAC (X86_STEPS_TAC EXEC (1--4)) THEN

  ENSURES_FINAL_STATE_TAC THEN

  (* The facts about RIP, K1 and the events are already in the right
     form. The memory fact is about the 512-bit value at rdi. Simplify its
     mask and merge with the lemmas above. *)
  RULE_ASSUM_TAC(REWRITE_RULE[MASK7_BITS; MERGE_192]) THEN

  (* Turn the 512-bit fact into a fact about the number stored in the 64
     bytes at rdi, split that number into 24 + 40 bytes, and finish. *)
  FIRST_X_ASSUM(fun th ->
    if can (find_term (fun t -> t = `word_join:320 word->192 word->512 word`))
           (concl th)
    then MP_TAC (REWRITE_RULE[bytes512; asword; READ_COMPONENT_COMPOSE;
                              through; read] th)
    else NO_TAC) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`read (bytes (word a:int64,64)) (read memory s4)`;
                 `word_subword (old:512 word) (192,320):320 word`;
                 `word_zx (z:512 word):192 word`] SPLIT_512) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`word a:int64`; `64`; `read memory s4`]
                    READ_BYTES_BOUND) THEN
      REWRITE_TAC[ARITH_RULE `8 * 64 = 512`];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`word a:int64`; `64`; `24`; `read memory s4`]
                READ_BYTES_MOD) THEN
  MP_TAC(ISPECL [`word a:int64`; `64`; `24`; `read memory s4`]
                READ_BYTES_DIV) THEN
  REWRITE_TAC[MIN; ARITH; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `8 * 24 = 192`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN ASM_MESON_TAC[]);;
