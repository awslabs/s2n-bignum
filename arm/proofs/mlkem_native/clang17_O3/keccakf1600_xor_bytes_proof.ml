(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* XOR of bytes into a Keccak state. This is the code for                    *)
(* mlkem_keccakf1600_xor_bytes from mlkem-native's portable C implementation *)
(* compiled by clang 17 with -O3 (see mlkem_native/README.md), which XORs    *)
(* len bytes of data into the 200-byte state starting at byte off. As in     *)
(* mlkem_keccakf1600_extract_bytes at clang -O3, the XOR is vectorized with  *)
(* loops: if len >= 8 and the data does not overlap the bytes of the state   *)
(* that it is XORed into (two tests of the end of one against the start of   *)
(* the other), it XORs blocks of 32 bytes with Q registers, then blocks of 8 *)
(* bytes with a D register, and finally single bytes; otherwise it XORs one  *)
(* byte at a time. The specifications are those for gcc at -O2. It is        *)
(* verified in the whole image (see libmlkem.ml).                            *)
(* ========================================================================= *)


needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_keccakf1600_xor_bytes"];;


(*** The code in the image:

    mlkem_keccakf1600_xor_bytes:
      +0x0: cbz     w3, ret
      +0x4: mov     w8, w2
      +0x8: mov     w9, w3
      +0xc: cmp     w3, #0x8
     +0x10: b.cc    join1
     +0x14: add     x10, x0, x8
     +0x18: add     x11, x1, x9
     +0x1c: cmp     x10, x11
     +0x20: b.cs    join4
     +0x24: add     x10, x9, x8
     +0x28: add     x10, x0, x10
     +0x2c: cmp     x10, x1
     +0x30: b.ls    join4
     join1:
     +0x34: mov     x10, xzr
     join2:
     +0x38: add     x12, x0, x10
     +0x3c: add     x11, x1, x10
     +0x40: add     x8, x12, x8
     +0x44: sub     x9, x9, x10
     loop1:
     +0x48: ldrb    w10, [x11], #1
     +0x4c: ldrb    w12, [x8]
     +0x50: subs    x9, x9, #0x1
     +0x54: eor     w10, w12, w10
     +0x58: strb    w10, [x8], #1
     +0x5c: b.ne    loop1
     ret:
     +0x60: ret
     join4:
     +0x64: cmp     w3, #0x20
     +0x68: b.cs    +0x74
     +0x6c: mov     x10, xzr
     +0x70: b       join5
     +0x74: and     x10, x9, #0xffffffe0
     +0x78: add     x12, x8, x0
     +0x7c: add     x11, x1, #0x10
     +0x80: add     x12, x12, #0x10
     +0x84: mov     x13, x10
     loop2:
     +0x88: ldp     q0, q1, [x11, #-16]
     +0x8c: add     x11, x11, #0x20
     +0x90: subs    x13, x13, #0x20
     +0x94: ldp     q2, q3, [x12, #-16]
     +0x98: eor     v0.16b, v2.16b, v0.16b
     +0x9c: eor     v1.16b, v3.16b, v1.16b
     +0xa0: stp     q0, q1, [x12, #-16]
     +0xa4: add     x12, x12, #0x20
     +0xa8: b.ne    loop2
     +0xac: cmp     x10, x9
     +0xb0: b.eq    ret
     +0xb4: tst     x9, #0x18
     +0xb8: b.eq    join2
     join5:
     +0xbc: mov     x13, x10
     +0xc0: and     x10, x9, #0xfffffff8
     +0xc4: add     x12, x0, x13
     +0xc8: add     x11, x1, x13
     +0xcc: add     x12, x12, x8
     +0xd0: sub     x13, x13, x10
     loop3:
     +0xd4: ldr     d0, [x11], #8
     +0xd8: ldr     d1, [x12]
     +0xdc: adds    x13, x13, #0x8
     +0xe0: eor     v0.8b, v1.8b, v0.8b
     +0xe4: str     d0, [x12], #8
     +0xe8: b.ne    loop3
     +0xec: cmp     x10, x9
     +0xf0: b.eq    ret
     +0xf4: b       join2
 ***)


(* ------------------------------------------------------------------------- *)
(* Reading 8 and 16 bytes of an array given as a number.                     *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES64_OF_NUM = prove
 (`!a:int64 m n k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ k + 8 <= m
        ==> read (memory :> bytes64(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 64)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP (8 * 8)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES128_OF_NUM = prove
 (`!a:int64 m n k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ k + 16 <= m
        ==> read (memory :> bytes128(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 128)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE
   `340282366920938463463374607431768211456 = 2 EXP (8 * 16)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

(*** A block of k bytes after the first j, both as numbers ***)

let READ_MEMORY_BYTES_EXTEND = prove
 (`!d:int64 j k x s:armstate.
        read (memory :> bytes(d,j)) s = x MOD 2 EXP (8 * j) /\
        read (memory :> bytes(word_add d (word j),k)) s =
        (x DIV 2 EXP (8 * j)) MOD 2 EXP (8 * k)
        ==> read (memory :> bytes(d,j + k)) s = x MOD 2 EXP (8 * (j + k))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MOD_MULT_MOD] THEN
  ARITH_TAC);;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** Weakening the pre- and postconditions of an ensures ***)

let ENSURES_PREPOST_WEAKEN = MESON[ENSURES_PREPOSTCONDITION_THM]
 `ensures step P Q C
  ==> (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x)
      ==> ensures step P' Q' C`;;


(* ------------------------------------------------------------------------- *)
(* The state after the first i bytes of the data m have been XORed into it,  *)
(* as numbers. The bytes of the state from byte off + i on are those of S,   *)
(* and the bytes before byte off + i are those of the final state            *)
(* word_xor S (word(2 EXP (8 * off) * m)). A block of k bytes of the final   *)
(* state is the XOR of the blocks of S and of m, as a word of 8 * k bits.    *)
(* ------------------------------------------------------------------------- *)

let XOR_CHUNK = prove
 (`!(S:1600 word) m off j k.
        dimindex(:N) = 8 * k /\ off + j + k <= 200
        ==> (val(word_xor S (word(2 EXP (8 * off) * m))) DIV
             2 EXP (8 * (off + j))) MOD 2 EXP (8 * k) =
            val(word_xor
                 (word((val S DIV 2 EXP (8 * (off + j))) MOD 2 EXP (8 * k)))
                 (word((m DIV 2 EXP (8 * j)) MOD 2 EXP (8 * k))):N word)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`8 * (off + j)`; `8 * k`;
                 `word_xor S (word(2 EXP (8 * off) * m)):1600 word`]
         (INST_TYPE [`:N`,`:N`] VAL_WORD_SUBWORD)) THEN
  ASM_REWRITE_TAC[ARITH_RULE `MIN x x = x`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN BINOP_TAC THENL
   [REWRITE_TAC[word_subword]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; GSYM DIV_DIV] THEN
  SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ]);;

let XOR_CHUNK_1 = prove
 (`!(S:1600 word) m off j.
        off + j + 1 <= 200
        ==> (val(word_xor S (word(2 EXP (8 * off) * m))) DIV
             2 EXP (8 * (off + j))) MOD 2 EXP (8 * 1) =
            val(word_xor (word((val S DIV 2 EXP (8 * (off + j))) MOD 256))
                         (word((m DIV 2 EXP (8 * j)) MOD 256)):byte)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`S:1600 word`; `m:num`; `off:num`; `j:num`; `1`]
         (INST_TYPE [`:8`,`:N`] XOR_CHUNK)) THEN
  ASM_REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let XOR_CHUNK_8 = prove
 (`!(S:1600 word) m off j.
        off + j + 8 <= 200
        ==> (val(word_xor S (word(2 EXP (8 * off) * m))) DIV
             2 EXP (8 * (off + j))) MOD 2 EXP (8 * 8) =
            val(word_xor
                 (word((val S DIV 2 EXP (8 * (off + j))) MOD 2 EXP 64))
                 (word((m DIV 2 EXP (8 * j)) MOD 2 EXP 64)):int64)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`S:1600 word`; `m:num`; `off:num`; `j:num`; `8`]
         (INST_TYPE [`:64`,`:N`] XOR_CHUNK)) THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let XOR_CHUNK_16 = prove
 (`!(S:1600 word) m off j.
        off + j + 16 <= 200
        ==> (val(word_xor S (word(2 EXP (8 * off) * m))) DIV
             2 EXP (8 * (off + j))) MOD 2 EXP (8 * 16) =
            val(word_xor
                 (word((val S DIV 2 EXP (8 * (off + j))) MOD 2 EXP 128))
                 (word((m DIV 2 EXP (8 * j)) MOD 2 EXP 128)):int128)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`S:1600 word`; `m:num`; `off:num`; `j:num`; `16`]
         (INST_TYPE [`:128`,`:N`] XOR_CHUNK)) THEN
  ASM_REWRITE_TAC[DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

(*** The bytes before byte off are those of S ***)

let XOR_LOW = prove
 (`!(S:1600 word) m off.
        off <= 200
        ==> val(word_xor S (word(2 EXP (8 * off) * m))) MOD 2 EXP (8 * off) =
            val S MOD 2 EXP (8 * off)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `8 * off`;
                 `word_xor S (word(2 EXP (8 * off) * m)):1600 word`]
         (INST_TYPE [`:1600`,`:N`] VAL_WORD_SUBWORD)) THEN
  MP_TAC(ISPECL [`0`; `8 * off`; `S:1600 word`]
         (INST_TYPE [`:1600`,`:N`] VAL_WORD_SUBWORD)) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`; EXP; DIV_1] THEN
  ASM_SIMP_TAC[ARITH_RULE `off <= 200 ==> MIN (8 * off) 1600 = 8 * off`] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM(CONJUNCT1 WORD_XOR_0)] THEN AP_TERM_TAC THEN
  REWRITE_TAC[word_subword; EXP; DIV_1; VAL_WORD;
              DIMINDEX_CONV `dimindex(:1600)`] THEN
  ASM_SIMP_TAC[MOD_MOD_EXP_MIN;
               ARITH_RULE `off <= 200 ==> MIN 1600 (8 * off) = 8 * off`] THEN
  AP_TERM_TAC THEN SIMP_TAC[MOD_MULT; EXP_EQ_0; ARITH_EQ]);;

(*** The bytes from byte off + len on are those of S ***)

let XOR_HIGH = prove
 (`!(S:1600 word) m off len.
        m < 2 EXP (8 * len) /\ off + len <= 200
        ==> val(word_xor S (word(2 EXP (8 * off) * m))) DIV
            2 EXP (8 * (off + len)) =
            val S DIV 2 EXP (8 * (off + len))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`8 * (off + len)`; `1600`;
                 `word_xor S (word(2 EXP (8 * off) * m)):1600 word`]
         (INST_TYPE [`:1600`,`:N`] VAL_WORD_SUBWORD)) THEN
  MP_TAC(ISPECL [`8 * (off + len)`; `1600`; `S:1600 word`]
         (INST_TYPE [`:1600`,`:N`] VAL_WORD_SUBWORD)) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`; ARITH_RULE `MIN x x = x`] THEN
  SIMP_TAC[MOD_LT; RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ;
           VAL_BOUND_64] THEN
  W(fun (asl,w) ->
    let ts = find_terms (fun t -> can (term_match [] `val(x:1600 word)`) t) w in
    MAP_EVERY (fun t -> MP_TAC(ISPEC (rand t) VAL_BOUND)) ts) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:1600 word. (val x DIV 2 EXP (8 * (off + len))) MOD 2 EXP 1600 =
                  val x DIV 2 EXP (8 * (off + len))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
  THENL
   [GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `val(x:1600 word)` THEN
    REWRITE_TAC[DIV_LE] THEN MP_TAC(ISPEC `x:1600 word` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl))) THEN
  AP_TERM_TAC THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM(CONJUNCT1 WORD_XOR_0)] THEN AP_TERM_TAC THEN
  REWRITE_TAC[word_subword; VAL_WORD; DIMINDEX_CONV `dimindex(:1600)`] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `(2 EXP (8 * off) * m) MOD 2 EXP 1600 < 2 EXP (8 * (off + len))`
   (fun th -> SIMP_TAC[th; DIV_LT; MOD_0]) THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `2 EXP (8 * off) * m` THEN
  REWRITE_TAC[MOD_LE; LEFT_ADD_DISTRIB; EXP_ADD; LT_MULT_LCANCEL] THEN
  ASM_REWRITE_TAC[EXP_EQ_0; ARITH_EQ]);;

(*** The final state from the bytes up to off + len and those after ***)

let XOR_FINAL = prove
 (`!a d (S:1600 word) m off len s:armstate.
        off + len <= 200 /\
        read (memory :> bytes(d,len)) s = m /\
        read (memory :> bytes(a,off + len)) s =
        val(word_xor S (word(2 EXP (8 * off) * m))) MOD
        2 EXP (8 * (off + len)) /\
        read (memory :> bytes(word_add a (word(off + len)),200 - (off + len)))
          s = val S DIV 2 EXP (8 * (off + len))
        ==> read (memory :> bytes(a,200)) s =
            val(word_xor S (word(2 EXP (8 * off) * m)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `m < 2 EXP (8 * len)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `m:num`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
    ALL_TAC] THEN
  MP_TAC(SPECL [`S:1600 word`; `m:num`; `off:num`; `len:num`] XOR_HIGH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `200 = (off + len) + (200 - (off + len))` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && is_binary "DIV" (lhs(concl th)) &&
    can (find_term ((=) `word_xor:1600 word->1600 word->1600 word`))
        (lhs(concl th)))) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[DIVISION_SIMP]);;

(*** The first state, at the start of the code ***)

let XOR_START = prove
 (`!a (S:1600 word) m off s:armstate.
        off <= 200 /\ read (memory :> bytes(a,200)) s = val S
        ==> read (memory :> bytes(a,off + 0)) s =
            val(word_xor S (word(2 EXP (8 * off) * m))) MOD
            2 EXP (8 * (off + 0)) /\
            read (memory :> bytes(word_add a (word(off + 0)),200 - (off + 0)))
              s = val S DIV 2 EXP (8 * (off + 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[XOR_LOW] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
  ASM_SIMP_TAC[ARITH_RULE `off <= 200 ==> MIN 200 off = off`]);;

(*** The rest of the state from byte p' on, from that from byte p on ***)

let XOR_REST = prove
 (`!a v p p' s:armstate.
        read (memory :> bytes(word_add a (word p),200 - p)) s =
        v DIV 2 EXP (8 * p) /\ p <= p'
        ==> read (memory :> bytes(word_add a (word p'),200 - p')) s =
            v DIV 2 EXP (8 * p')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
    (CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS])) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\x. x DIV 2 EXP (8 * d)`) THEN
  REWRITE_TAC[READ_BYTES_DIV; DIV_DIV; GSYM EXP_ADD; GSYM LEFT_ADD_DISTRIB;
              GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `200 - p - d = 200 - (p + d)`]);;

(*** Reading 1, 8 and 16 bytes of the rest of the state ***)

let XOR_LOAD8 = prove
 (`!a v p q s:armstate.
        read (memory :> bytes(word_add a (word p),200 - p)) s =
        v DIV 2 EXP (8 * p) /\ p <= q /\ q < 200
        ==> read (memory :> bytes8(word_add a (word q))) s =
            word((v DIV 2 EXP (8 * q)) MOD 256)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `v:num`; `p:num`; `q:num`; `s:armstate`]
         XOR_REST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`word_add a (word q):int64`; `200 - q`; `v DIV 2 EXP (8 * q)`;
                `0`; `s:armstate`] READ_MEMORY_BYTES8_OF_NUM) THEN
  ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; EXP; DIV_1] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let XOR_LOAD64 = prove
 (`!a v p q s:armstate.
        read (memory :> bytes(word_add a (word p),200 - p)) s =
        v DIV 2 EXP (8 * p) /\ p <= q /\ q + 8 <= 200
        ==> read (memory :> bytes64(word_add a (word q))) s =
            word((v DIV 2 EXP (8 * q)) MOD 2 EXP 64)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `v:num`; `p:num`; `q:num`; `s:armstate`]
         XOR_REST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`word_add a (word q):int64`; `200 - q`; `v DIV 2 EXP (8 * q)`;
                `0`; `s:armstate`] READ_MEMORY_BYTES64_OF_NUM) THEN
  ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; EXP; DIV_1] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let XOR_LOAD128 = prove
 (`!a v p q s:armstate.
        read (memory :> bytes(word_add a (word p),200 - p)) s =
        v DIV 2 EXP (8 * p) /\ p <= q /\ q + 16 <= 200
        ==> read (memory :> bytes128(word_add a (word q))) s =
            word((v DIV 2 EXP (8 * q)) MOD 2 EXP 128)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `v:num`; `p:num`; `q:num`; `s:armstate`]
         XOR_REST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`word_add a (word q):int64`; `200 - q`; `v DIV 2 EXP (8 * q)`;
                `0`; `s:armstate`] READ_MEMORY_BYTES128_OF_NUM) THEN
  ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; EXP; DIV_1] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(*** The bytes of stored 1-, 8- and 16-byte words as numbers ***)

let READ_MEMORY_BYTES_OF_WORD8 = prove
 (`!a:int64 (w:byte) s:armstate.
        read (memory :> bytes8 a) s = w
        ==> read (memory :> bytes(a,1)) s = val w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BYTES8] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let READ_MEMORY_BYTES_OF_WORD64 = prove
 (`!a:int64 (w:int64) s:armstate.
        read (memory :> bytes64 a) s = w
        ==> read (memory :> bytes(a,8)) s = val w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  REWRITE_TAC[VAL_READ_WBYTES; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let READ_MEMORY_BYTES_OF_WORD128 = prove
 (`!a:int64 (w:int128) s:armstate.
        read (memory :> bytes128 a) s = w
        ==> read (memory :> bytes(a,16)) s = val w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
  REWRITE_TAC[VAL_READ_WBYTES; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas and tactics for the 32-bit arithmetic of the code on small         *)
(* numbers, and for the addresses with a 32-bit index register (UXTW).       *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_WORD_SMALL = prove
 (`!n. n < 2 EXP dimindex(:M)
       ==> (word_zx:M word->N word) (word n) = word n`,
  SIMP_TAC[WORD_ZX_WORD; MOD_LT]);;

let WORD_ZX_UXTW_SMALL = prove
 (`!n. n < 2 EXP 32
       ==> word_zx(word_zx(word n:int64):int32):int64 = word n /\
           word_zx(word_zx(word_zx(word n:int64):int32):int32):int64 = word n`,
  REWRITE_TAC[WORD_ZX_TRIVIAL] THEN SIMP_TAC[WORD_ZX_32_SMALL]);;

let WORD_AND_FFFFFFF0_32 = prove
 (`!n. n < 2 EXP 32
       ==> word_and (word n:int32) (word 4294967280) = word(16 * n DIV 16)`,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(SYM((NUM_REDUCE_CONV THENC WORD_REDUCE_CONV)
    `word_not(word(2 EXP 4 - 1)):int32`)) THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD; VAL_WORD; DIMINDEX_32] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_AND_FFFFFFF8_32 = prove
 (`!n. n < 2 EXP 32
       ==> word_and (word n:int32) (word 4294967288) = word(8 * n DIV 8)`,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(SYM((NUM_REDUCE_CONV THENC WORD_REDUCE_CONV)
    `word_not(word(2 EXP 3 - 1)):int32`)) THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD; VAL_WORD; DIMINDEX_32] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_AND_FFFFFFF0_64 = prove
 (`!n. n < 2 EXP 32
       ==> word_and (word n:int64) (word 4294967280) = word(16 * n DIV 16)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word n:int64 = word_zx(word n:int32) /\
                word(16 * n DIV 16):int64 = word_zx(word(16 * n DIV 16):int32)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[WORD_ZX_WORD; DIMINDEX_32] THEN CONJ_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `n < 2 EXP 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM WORD_AND_FFFFFFF0_32] THEN
  SPEC_TAC(`word n:int32`,`x:int32`) THEN BITBLAST_TAC);;

let VAL_WORD_AND_15 = prove
 (`!n. val(word_and (word n:int64) (word 15)) = (n MOD 2 EXP 64) MOD 16`,
  GEN_TAC THEN
  SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 EXP 4 - 1`)) THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let VAL_WORD_AND_7 = prove
 (`!n. val(word_and (word n:int64) (word 7)) = (n MOD 2 EXP 64) MOD 8`,
  GEN_TAC THEN
  SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 EXP 3 - 1`)) THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV);;
(*** Normalize word arithmetic on small numbers in the register values:  ***)
(*** word_zx (word n) = word n, word_sub (word x) (word y) = word(x - y) ***)
(*** and word_add (word x) (word y) = word(x + y), with the side          ***)
(*** conditions proved by arithmetic from the assumptions, then the       ***)
(*** masks of the length and simple quotients.                            ***)

let W_NORM_TAC =
  let zx_pat = `(word_zx:M word->N word) (word n)`
  and sub_pat = `word_sub (word x) (word y):N word`
  and add_pat = `word_add (word x) (word y):N word`
  and reg_pat = `read (r:(armstate,int64)component) s = x` in
  let is_reg th = can (term_match [] reg_pat) (concl th) in
  let cands (asl,w) =
    let tms = mapfilter (fun (_,th) -> if is_reg th then rand(concl th)
                                       else failwith "") asl in
    let fnd p = setify(itlist (fun t acc -> find_terms p t @ acc) tms []) in
    fnd (can (term_match [] add_pat)) @
    fnd (can (term_match [] sub_pat)) @
    fnd (can (term_match [] zx_pat)) in
  let side_tac =
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
    SIMPLE_ARITH_TAC in
  let rule th = RULE_ASSUM_TAC(fun a -> if is_reg a then REWRITE_RULE[th] a
                                        else a) in
  let one_tac t =
    if can (term_match [] zx_pat) t then
      let n = rand(rand t) in
      let ity = type_of(rand t) and oty = type_of t in
      let th = SPEC n (INST_TYPE [hd(snd(dest_type ity)),`:M`;
                                  hd(snd(dest_type oty)),`:N`]
                       WORD_ZX_WORD_SMALL) in
      SUBGOAL_THEN (lhand(concl th)) (fun c -> rule(MP th c)) THENL
       [side_tac; ALL_TAC]
    else if can (term_match [] sub_pat) t then
      let x = rand(lhand t) and y = rand(rand t) in
      let th = ISPECL [x; y] (INST_TYPE [hd(snd(dest_type(type_of t))),`:N`]
                              (GEN_ALL WORD_SUB2)) in
      SUBGOAL_THEN (lhand(concl th)) (fun c -> rule(MP th c)) THENL
       [side_tac; ALL_TAC]
    else rule(GSYM WORD_ADD) in
  let pass = W(fun g -> MAP_EVERY (fun t -> TRY(one_tac t)) (cands g)) in
  pass THEN pass THEN pass THEN pass;;

let XOR_NORM_TAC =
  let mask_pats =
   [`word_and (word n:int32) (word 4294967280)`, WORD_AND_FFFFFFF0_32;
    `word_and (word n:int32) (word 4294967288)`, WORD_AND_FFFFFFF8_32;
    `word_and (word n:int64) (word 4294967280)`, WORD_AND_FFFFFFF0_64] in
  W_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_SUB2]) THEN
  W(fun (asl,w) ->
    let tms = setify(itlist (fun (_,th) acc ->
      find_terms (fun t -> exists (fun (p,_) -> can (term_match [] p) t)
                                  mask_pats) (concl th) @ acc) asl []) in
    MAP_EVERY (fun t ->
      let lth = snd(find (fun (p,_) -> can (term_match [] p) t) mask_pats) in
      let th = SPEC (rand(lhand t)) lth in
      TRY(SUBGOAL_THEN (lhand(concl th))
            (fun c -> RULE_ASSUM_TAC(REWRITE_RULE[MP th c])) THENL
          [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC])) tms) THEN
  W(fun (asl,w) ->
    let tms = setify(itlist (fun (_,th) acc ->
      find_terms (fun t -> can (term_match [] `(m * n + p) DIV m`) t &&
                           is_numeral(lhand(lhand(lhand t))))
        (concl th) @ acc) asl []) in
    MAP_EVERY (fun t ->
      let eq = mk_eq(t,rand(lhand(lhand t))) in
      TRY(SUBGOAL_THEN eq (fun c -> RULE_ASSUM_TAC(REWRITE_RULE[c])) THENL
       [ARITH_TAC; ALL_TAC])) tms) THEN
  W_NORM_TAC;;

(*** The tests of the length with TST ***)

let XOR_TST_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_AND_15; VAL_WORD_AND_7]) THEN
  W(fun (asl,w) ->
    let tms = setify(itlist (fun (_,th) acc ->
      find_terms (fun t -> can (term_match [] `n MOD 2 EXP 64`) t)
        (concl th) @ acc) asl []) in
    MAP_EVERY (fun t ->
      TRY(SUBGOAL_THEN (mk_eq(t,lhand t))
            (fun c -> RULE_ASSUM_TAC(REWRITE_RULE[c])) THENL
          [MATCH_MP_TAC MOD_LT THEN CONV_TAC NUM_REDUCE_CONV THEN
           SIMPLE_ARITH_TAC; ALL_TAC])) tms) THEN
  DECIDE_FLAGS_TAC;;

(*** A branch on a comparison, decided by arithmetic ***)

let XOR_BRANCH_TAC =
  TRY(FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),l),Comb(Comb(Comb(Const("COND",_),c),_),_))
        when can (term_match [] `read PC s`) l ->
        (SUBGOAL_THEN c (fun cth -> ASSUME_TAC(REWRITE_RULE[cth] th)) THENL
          [FIRST_ASSUM ACCEPT_TAC ORELSE SIMPLE_ARITH_TAC; ALL_TAC]) ORELSE
        (SUBGOAL_THEN (mk_neg c)
          (fun cth -> ASSUME_TAC(REWRITE_RULE[cth] th)) THENL
          [FIRST_ASSUM ACCEPT_TAC ORELSE SIMPLE_ARITH_TAC; ALL_TAC])
    | _ -> NO_TAC));;

(*** The equations removing the extensions of 32-bit indices j ***)

let XOR_ZX_FACTS_TAC js =
  MAP_EVERY (fun j ->
    MP_TAC(SPEC j WORD_ZX_UXTW_SMALL) THEN
    ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
                    STRIP_TAC]) js;;

(*** Fold sums of numerals in the register values ***)

let XOR_FOLD_TAC =
  let reg_pat = `read (r:(armstate,int64)component) s = x` in
  let conv t =
    match t with
      Comb(Comb(Const("+",_),Comb(Comb(Const("+",_),x),m)),n)
        when is_numeral m && is_numeral n ->
        (REWR_CONV (GSYM ADD_ASSOC) THENC RAND_CONV NUM_ADD_CONV) t
    | _ -> failwith "XOR_FOLD_TAC" in
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] reg_pat) (concl th)
    then CONV_RULE(RAND_CONV(DEPTH_CONV conv)) th else th);;

(*** W32_DECIDE_FLAGS_TAC, but rewriting only the flags, so that the ***)
(*** equations for the extended indices are kept                        ***)

let XOR_W32_DECIDE_TAC =
  let flag_pat = `read (f:(armstate,bool)component) s <=> p` in
  let is_flag th = can (term_match [] flag_pat) (concl th) in
  W(fun (asl,w) ->
    let tms = setify (itlist (fun (_,th) acc ->
      if is_flag th then
        find_terms (can (term_match [] `word_zx(word n:int64):int32`))
                   (concl th) @ acc
      else acc) asl []) in
    MAP_EVERY (fun t ->
      MP_TAC(SPEC (rand(rand t)) WORD_ZX_64_32_SMALL) THEN
      ANTS_TAC THENL
       [SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(fun a ->
          if is_flag a then REWRITE_RULE[th] a else a))]) tms) THEN
  CMP_FLAGS_TAC `word_sub (word x) (word y):int32` WORD_CMP_32_FLAGS;;


(*** A step of the code, with the normalization of the register values ***)
(*** and the decision of a branch                                       ***)

let XOR_STEP_TAC n =
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_CLANG17_O3_EXEC [n] THEN
  XOR_NORM_TAC THEN XOR_FOLD_TAC THEN
  TRY XOR_W32_DECIDE_TAC THEN XOR_BRANCH_TAC;;

(*** The blocks of the state still to be updated at byte off + j, from the ***)
(*** rest of the state from byte p on, and those of the data at byte j, of ***)
(*** 1, 8 or 16 bytes, in all the forms of the addresses in the code. The  ***)
(*** length of the data is lt.                                            ***)

let XOR_LOAD_FACTS_TAC sname p lt js8 js64 js128 =
  let s = mk_var(sname,`:armstate`) in
  let ix j = mk_binop `(+):num->num->num` `off:num` j in
  let flat j = mk_comb(`word_add (a:int64)`,mk_comb(`word:num->int64`,ix j))
  and nested j = mk_comb(`word_add (word_add (a:int64) (word off))`,
                         mk_comb(`word:num->int64`,j)) in
  let alts j =
    let n = prove(mk_eq(flat j,nested j),
                  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) in
    if j = `0` then
      [n; prove(mk_eq(flat j,`word_add (a:int64) (word off)`),
                REWRITE_TAC[ADD_CLAUSES])]
    else [n] in
  let dalts j =
    if j = `0` then [prove(`word_add (d:int64) (word 0) = d`,
                           REWRITE_TAC[WORD_ADD_0])]
    else [] in
  let assume_alts eqs th =
    ASSUME_TAC th THEN
    MAP_EVERY (fun eq -> ASSUME_TAC(ONCE_REWRITE_RULE[eq] th)) eqs in
  let side_tac = ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC in
  let one lth dth j =
    MP_TAC(SPECL [`a:int64`; `val(S:1600 word)`; p; ix j; s] lth) THEN
    ANTS_TAC THENL [side_tac; DISCH_THEN(assume_alts (alts j))] THEN
    MP_TAC(SPECL [`d:int64`; lt; `m:num`; j; s] dth) THEN
    ANTS_TAC THENL [side_tac; DISCH_THEN(assume_alts (dalts j))] in
  MAP_EVERY (one XOR_LOAD8 READ_MEMORY_BYTES8_OF_NUM) js8 THEN
  MAP_EVERY (one XOR_LOAD64 READ_MEMORY_BYTES64_OF_NUM) js64 THEN
  MAP_EVERY (one XOR_LOAD128 READ_MEMORY_BYTES128_OF_NUM) js128;;

(*** The rest of the state from byte p' on, before the stores ***)

let XOR_REST_TAC sname p p' =
  let s = mk_var(sname,`:armstate`) in
  MP_TAC(SPECL [`a:int64`; `val(S:1600 word)`; p; p'; s] XOR_REST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; DISCH_TAC];;

(*** The words that the code stores are the XOR of those it loads ***)

let WORD_ZX_MOD_64 = prove
 (`!t. word (t MOD 2 EXP 64):int128 = word_zx(word (t MOD 2 EXP 64):int64)`,
  REWRITE_TAC[WORD_ZX_WORD; DIMINDEX_64; MOD_MOD_REFL]);;

let WORD_ZX_MOD_8 =
  let th = prove
   (`!t. word (t MOD 256):N word = word_zx(word (t MOD 256):byte)`,
    REWRITE_TAC[WORD_ZX_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_REFL]) in
  CONJ (INST_TYPE [`:32`,`:N`] th) (INST_TYPE [`:64`,`:N`] th);;

let XOR_WORD_TAC =
  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  REWRITE_TAC[WORD_ZX_MOD_64; WORD_ZX_MOD_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  W(fun (asl,w) ->
    let ts = setify(find_terms (fun t ->
      match t with
        Comb(Const("word",_),n) -> not(is_numeral n)
      | _ -> false) w) in
    MAP_EVERY (fun t -> SPEC_TAC(t,genvar(type_of t))) ts) THEN
  BITBLAST_TAC;;

(*** After a store of k bytes at byte off + j of the state, those bytes as ***)
(*** a number, as the bytes of the final state                            ***)

let XOR_STORE_TAC j k =
  let flat = mk_comb(`word_add (a:int64)`,
    mk_comb(`word:num->int64`,mk_binop `(+):num->num->num` `off:num` j)) in
  let pat,bth,cth =
    match k with
      1 -> `read (memory :> bytes8 x) s = y`,
           READ_MEMORY_BYTES_OF_WORD8,XOR_CHUNK_1
    | 8 -> `read (memory :> bytes64 x) s = y`,
           READ_MEMORY_BYTES_OF_WORD64,XOR_CHUNK_8
    | _ -> `read (memory :> bytes128 x) s = y`,
           READ_MEMORY_BYTES_OF_WORD128,XOR_CHUNK_16 in
  let target = subst [j,`j:num`; mk_small_numeral k,`k:num`]
   `(val(word_xor (S:1600 word) (word(2 EXP (8 * off) * m))) DIV
     2 EXP (8 * (off + j))) MOD 2 EXP (8 * k)` in
  let addr_eq x =
    if x = flat then REFL x else
    prove(mk_eq(x,flat),
          REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_CLAUSES] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) in
  let is_xor t = can (find_term (fun u -> is_const u &&
                                          fst(dest_const u) = "word_xor")) t in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if not(can (term_match [] pat) c) || not(is_xor(rand c)) then NO_TAC else
    let x = rand(rand(rand(rator(lhand c)))) in
    match (try Some(addr_eq x) with Failure _ -> None) with
      None -> NO_TAC
    | Some eq ->
        let th1 = MATCH_MP bth th in
        let th2 = if x = flat then th1 else ONCE_REWRITE_RULE[eq] th1 in
        let w = rand c in
        let vw = mk_icomb(`val:N word->num`,w) in
        SUBGOAL_THEN (mk_eq(vw,target))
         (fun eth -> ASSUME_TAC(REWRITE_RULE[eth] th2)) THENL
         [MP_TAC(SPECL [`S:1600 word`; `m:num`; `off:num`; j] cth) THEN
          ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
          AP_TERM_TAC THEN XOR_WORD_TAC;
          ALL_TAC]);;

(*** The bytes of the state up to byte off + jn, after those up to off + j ***)
(*** and the k bytes from off + j                                         ***)

let XOR_EXTEND_TAC j k jn =
  let ix j = mk_binop `(+):num->num->num` `off:num` j in
  let kt = mk_small_numeral k in
  let pcomp = subst [ix j,`P:num`] `memory :> bytes(a:int64,P)`
  and ccomp = subst [ix j,`P:num`; kt,`k:num`]
    `memory :> bytes(word_add (a:int64) (word P),k)` in
  let eth = ARITH_RULE(mk_eq(mk_binop `(+):num->num->num` (ix j) kt,ix jn)) in
  let comp_of th =
    let c = concl th in
    if is_eq c && is_comb(lhs c) && is_comb(rator(lhs c))
    then rand(rator(lhs c)) else `F` in
  FIRST_ASSUM(fun pth ->
    if comp_of pth <> pcomp then NO_TAC else
    FIRST_ASSUM(fun cth ->
      if comp_of cth <> ccomp then NO_TAC else
      ASSUME_TAC(REWRITE_RULE[eth]
        (MATCH_MP READ_MEMORY_BYTES_EXTEND (CONJ pth cth)))));;

(*** The final state, from the bytes up to off + lt and those after ***)

let XOR_FINISH_TAC lt =
  let ix = mk_binop `(+):num->num->num` `off:num` lt in
  let pcomp = subst [ix,`P:num`] `memory :> bytes(a:int64,P)` in
  let comp_of th =
    let c = concl th in
    if is_eq c && is_comb(lhs c) && is_comb(rator(lhs c))
    then rand(rator(lhs c)) else `F` in
  FIRST_ASSUM(fun pth ->
    if comp_of pth <> pcomp then NO_TAC else
    let s = rand(lhs(concl pth)) in
    MP_TAC(SPECL [`a:int64`; `d:int64`; `S:1600 word`; `m:num`; `off:num`;
                  lt; s] XOR_FINAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; DISCH_TAC]);;

(*** The steps of the stores of the bytes after the first c0, k of them, ***)
(*** from step s on, with the blocks (j,k,jn) they write                  ***)

let BYTE_CNT_LEMMA = prove
 (`!cnt i. i < cnt /\ cnt < 2 EXP 64
           ==> (val(word_sub (word (cnt - i)) (word 1):int64) = 0 <=>
                i + 1 = cnt) /\
               word_sub (word (cnt - i)) (word 1):int64 =
               word (cnt - (i + 1))`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `cnt - i < 18446744073709551616` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `1 < 18446744073709551616`] THEN
    ASM_ARITH_TAC;
    W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC]);;

(*** The test of the loop counter cnt - i, and its decrement ***)

let BYTE_CNT_TAC cnt =
  MP_TAC(SPECL [cnt; `i:num`] BYTE_CNT_LEMMA) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `len < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN
      ARITH_TAC];
    DISCH_THEN(CONJUNCTS_THEN2
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]))];;

let LOOP2_CNT_LEMMA = prove
 (`!q i. i < q /\ q < 2 EXP 32
         ==> (val(word_sub (word (32 * (q - i))) (word 32):int64) = 0 <=>
              i + 1 = q) /\
             word_sub (word (32 * (q - i))) (word 32):int64 =
             word (32 * (q - (i + 1)))`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `32 * (q - i) < 18446744073709551616` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `32 < 18446744073709551616`] THEN
    ASM_ARITH_TAC;
    W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC]);;

let WORD_AND_FFFFFFE0_32 = prove
 (`!n. n < 2 EXP 32
       ==> word_and (word n:int32) (word 4294967264) = word(32 * n DIV 32)`,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(SYM((NUM_REDUCE_CONV THENC WORD_REDUCE_CONV)
    `word_not(word(2 EXP 5 - 1)):int32`)) THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD; VAL_WORD; DIMINDEX_32] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_AND_FFFFFFE0_64 = prove
 (`!n. n < 2 EXP 32
       ==> word_and (word n:int64) (word 4294967264) = word(32 * n DIV 32)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word n:int64 = word_zx(word n:int32) /\
                word(32 * n DIV 32):int64 = word_zx(word(32 * n DIV 32):int32)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[WORD_ZX_WORD; DIMINDEX_32] THEN CONJ_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `n < 2 EXP 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM WORD_AND_FFFFFFE0_32] THEN
  SPEC_TAC(`word n:int32`,`x:int32`) THEN BITBLAST_TAC);;

let LOOP2_CNT_TAC =
  MP_TAC(SPECL [`len DIV 32`; `i:num`] LOOP2_CNT_LEMMA) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `len < 2 EXP 32` THEN ARITH_TAC];
    DISCH_THEN(CONJUNCTS_THEN2
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]))];;

let TAIL_CMP_LEMMA = prove
 (`!len. len < 2 EXP 32
         ==> (val(word_sub (word (32 * len DIV 32)) (word len):int64) = 0 <=>
              len MOD 32 = 0)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `32 * len DIV 32 < 18446744073709551616 /\ len < 18446744073709551616`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `len < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

let TAIL_CMP_TAC =
  MP_TAC(SPEC `len:num` TAIL_CMP_LEMMA) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN XOR_BRANCH_TAC;;

let VAL_WORD_AND_31 = prove
 (`!n. val(word_and (word n:int64) (word 31)) = (n MOD 2 EXP 64) MOD 32`,
  GEN_TAC THEN
  SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 EXP 5 - 1`)) THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let TST24_BLAST = BITBLAST_RULE
 `!y:int64. word_and y (word 24) = word 0 <=>
            word_ult (word_and y (word 31)) (word 8)`;;

let TST24_LEMMA = prove
 (`!n. n < 2 EXP 32
       ==> (val(word_and (word n:int64) (word 24)) = 0 <=> n MOD 32 < 8)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `word n:int64` TST24_BLAST) THEN
  REWRITE_TAC[GSYM VAL_EQ_0; word_ult; relational2; VAL_WORD_AND_31] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `n MOD 2 EXP 64 = n` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `n < 2 EXP 32` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let TAIL_TST_TAC =
  MP_TAC(SPEC `len:num` TST24_LEMMA) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN XOR_BRANCH_TAC;;


let WORD_SUB_MOD32 = prove
 (`!len. word_sub (word len) (word (32 * len DIV 32)):int64 = word (len MOD 32)`,
  GEN_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let WORD_ADD_PTR = prove
 (`!a:int64 m n. word_add (word_add a (word m)) (word n) = word_add a (word (n + m))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let WORD_AND_FFFFFFF8_64 = prove
 (`!n. n < 2 EXP 32
       ==> word_and (word n:int64) (word 4294967288) = word(8 * n DIV 8)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word n:int64 = word_zx(word n:int32) /\
                word(8 * n DIV 8):int64 = word_zx(word(8 * n DIV 8):int32)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[WORD_ZX_WORD; DIMINDEX_32] THEN CONJ_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `n < 2 EXP 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM WORD_AND_FFFFFFF8_32] THEN
  SPEC_TAC(`word n:int32`,`x:int32`) THEN BITBLAST_TAC);;

let LOOP3_SUB = prove
 (`!n0 k i. word_add (word_sub (word (n0 + 8 * i)) (word (n0 + 8 * k)))
                     (word 8):int64 =
            word_sub (word (n0 + 8 * (i + 1))) (word (n0 + 8 * k))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `n0 + 8 * (i + 1) = (n0 + 8 * i) + 8` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let LOOP3_ZERO = prove
 (`!n0 k i. i < k /\ n0 + 8 * k < 2 EXP 64
            ==> (val(word_sub (word (n0 + 8 * (i + 1)))
                              (word (n0 + 8 * k)):int64) = 0
                 <=> i + 1 = k)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n0 + 8 * (i + 1) < 18446744073709551616 /\
                n0 + 8 * k < 18446744073709551616` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC);;

let LOOP3_CNT_TAC n0 k3 =
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [n0; k3; `i:num`] LOOP3_SUB]) THEN
  MP_TAC(SPECL [n0; k3; `i:num`] LOOP3_ZERO) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC (subst [n0,`n0:num`; k3,`k3:num`] `n0 + 8 * k3 <= len`) THEN
      UNDISCH_TAC `len < 2 EXP 32` THEN
      SPEC_TAC(k3,`k:num`) THEN SPEC_TAC(n0,`m:num`) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC];
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                         REWRITE_TAC[th])];;

let DIV8_AUX = prove
 (`!q r. 8 * ((32 * q + r) DIV 8) = 32 * q + 8 * (r DIV 8)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `32 * q + r = (4 * q) * 8 + r` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC);;
let DIV8_SPLIT = prove
 (`!len. 8 * (len DIV 8) = 32 * (len DIV 32) + 8 * ((len MOD 32) DIV 8)`,
  GEN_TAC THEN
  SUBGOAL_THEN `32 * (len DIV 32) + len MOD 32 = len`
    (fun th -> MP_TAC(SPECL [`len DIV 32`; `len MOD 32`] DIV8_AUX) THEN
               REWRITE_TAC[th]) THEN
  ARITH_TAC);;


let ZX64_128 = BITBLAST_RULE `!w:int64. word_zx(word_zx w:int128):int64 = w`;;

let LOOP3_ASSOC = prove
 (`!n i. n + 8 * (i + 1) = (n + 8 * i) + 8`,
  REPEAT GEN_TAC THEN ARITH_TAC);;

let TAIL3_CMP_LEMMA = prove
 (`!len. len < 2 EXP 32
         ==> (val(word_sub (word (8 * len DIV 8)) (word len):int64) = 0 <=>
              len MOD 8 = 0)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `8 * len DIV 8 < 18446744073709551616 /\ len < 18446744073709551616`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `len < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

let TAIL3_CMP_TAC =
  MP_TAC(SPEC `len:num` TAIL3_CMP_LEMMA) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN XOR_BRANCH_TAC;;

let WORD_SUB_MOD8 = prove
 (`!len. word_sub (word len) (word (8 * len DIV 8)):int64 = word (len MOD 8)`,
  GEN_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The code by the paths taken: the byte loop (loop1), entered directly for  *)
(* len < 8, and after the tests of the overlap of the data with the target   *)
(* if len >= 8 (the arrays are disjoint, so these tests always succeed, but  *)
(* the proof does not use this); otherwise the loop over blocks of 32 bytes  *)
(* (loop2) if len >= 32, and the loop over blocks of 8 bytes (loop3), each   *)
(* followed by the loops after it.                                          *)
(* ------------------------------------------------------------------------- *)

let XOR_EXEC = MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_CLANG17_O3_EXEC;;

let XOR_C1 = `val(word_add d (word len):int64) <= val(word_add a (word off):int64)`;;
let XOR_C2 = `val(word_add a (word(len + off)):int64) <= val(d:int64)`;;

let XOR_EVENTS_TERM =
  let ev nm args = "f_ev_" ^ nm ^ " " ^ args in
  let full = "a d off len pc returnaddress" in
  let byteloop pfx cnt =
    "APPEND (" ^ ev (pfx ^ "e") full ^ ") (APPEND (ENUMERATEL (" ^ cnt ^
    ") (\\i. " ^ ev (pfx ^ "l") full ^ " i)) (" ^ ev (pfx ^ "p") full ^ "))" in
  let tail3 pfx =
    "(if len MOD 8 = 0 then " ^ ev (pfx ^ "0") full ^ " else " ^
    byteloop (pfx ^ "1") "len MOD 8" ^ ")" in
  let loop3 pfx cnt =
    "APPEND " ^ tail3 (pfx ^ "t") ^ " (APPEND (" ^ ev (pfx ^ "e") full ^
    ") (APPEND (ENUMERATEL (" ^ cnt ^
    ") (\\i. " ^ ev (pfx ^ "l") full ^ " i)) (" ^ ev (pfx ^ "p") full ^ ")))" in
  let tail2 =
    "(if len MOD 32 = 0 then " ^ ev "t20" full ^
    " else if len MOD 32 < 8 then " ^ byteloop "t21" "len MOD 32" ^
    " else " ^ loop3 "t3" "(len MOD 32) DIV 8" ^ ")" in
  let c1 = "val(word_add d (word len):int64) <= val(word_add a (word off):int64)"
  and c2 = "val(word_add a (word(len + off)):int64) <= val(d:int64)" in
  parse_term
   ("\\(a:int64) (d:int64) (off:num) (len:num) (pc:num) " ^
    "(returnaddress:int64). " ^
    "if len = 0 then " ^ ev "len0" full ^
    " else if len <= 7 then " ^ byteloop "b1" "len" ^
    " else if ~(" ^ c1 ^ " \\/ " ^ c2 ^ ") then " ^ byteloop "b2" "len" ^
    " else APPEND (if len < 32 then " ^ loop3 "a3" "len DIV 8" ^
    " else APPEND " ^ tail2 ^
    " (APPEND (" ^ ev "v2e" full ^ ") (APPEND (ENUMERATEL (len DIV 32) (\\i. " ^
    ev "v2l" full ^ " i)) (" ^ ev "v2p" full ^ ")))) " ^
    "(if " ^ c1 ^ " then " ^ ev "j1" full ^ " else " ^ ev "j2" full ^
    ") :(uarch_event)list");;

let XOR_INTRO_TAC =
  CONCRETIZE_F_EVENTS_TAC XOR_EVENTS_TERM THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d:int64`; `off:num`; `len:num`; `S:1600 word`; `m:num`;
    `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              READ_MEMORY_WBYTES_VAL;
              fst MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_CLANG17_O3_EXEC] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `len < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `off + len <= 200` THEN ARITH_TAC; ALL_TAC];;

let XOR_ARGS_TAC =
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  FIRST_ASSUM(fun th ->
    if concl th <> `~(len = 0)` then NO_TAC else
    RULE_ASSUM_TAC(fun th' ->
      if concl th' = concl th then th' else REWRITE_RULE[th] th'));;

let XOR_LEN0_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] o
    check (fun th -> is_eq(concl th) && rand(concl th) = `m:num`)) THEN
  ARM_STEPS_TAC XOR_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; WORD_XOR_0] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The state at the start, as the bytes before byte off + 0 and from it ***)

let XOR_START_TAC =
  MP_TAC(SPECL [`a:int64`; `S:1600 word`; `m:num`; `off:num`; `s0:armstate`]
               XOR_START) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]);;

let XOR_PTR_EQ_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;;

(*** The final state, from the bytes up to off + lt and those after ***)

let XOR_END_TAC lt =
  XOR_FINISH_TAC lt THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ((CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCHARGE_SAFETY_PROPERTY_TAC])
   ORELSE DISCHARGE_SAFETY_PROPERTY_TAC);;

(*** The condition of b.ls after a comparison ***)

let XOR_LS_LEMMA = prove
 (`!x y:int64. ~(val y <= val x /\ ~(val(word_sub x y) = 0)) <=> val x <= val y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The memory at progress p: the bytes of the state before byte p are those  *)
(* of the final state, and those from byte p on are those of the state S.    *)
(* ------------------------------------------------------------------------- *)

let XOR_FS = `val(word_xor (S:1600 word) (word(2 EXP (8 * off) * m)))`;;

let XOR_MEM p =
  subst [p,`P:num`]
  `read (memory :> bytes(a,P)) s =
   val(word_xor (S:1600 word) (word(2 EXP (8 * off) * m))) MOD 2 EXP (8 * P) /\
   read (memory :> bytes(word_add a (word P),200 - P)) s =
   val S DIV 2 EXP (8 * P)`;;

(*** The invariant of the loop over single bytes, after n0 + i bytes ***)

let XOR_INV1 n0 cnt =
  subst [n0,`n0:num`; cnt,`cnt:num`]
  `\i s. read X8 s = word_add a (word(off + (n0 + i))) /\
         read X9 s = word(cnt - i) /\
         read X11 s = word_add d (word(n0 + i)) /\
         read X30 s = returnaddress /\
         read (memory :> bytes(d,len)) s = m /\
         read (memory :> bytes(a,off + (n0 + i))) s =
         val(word_xor (S:1600 word) (word(2 EXP (8 * off) * m))) MOD
         2 EXP (8 * (off + (n0 + i))) /\
         read (memory :> bytes(word_add a (word(off + (n0 + i))),
                               200 - (off + (n0 + i)))) s =
         val S DIV 2 EXP (8 * (off + (n0 + i)))`;;

let XOR_BYTELOOP_TAC n0 cnt (pos:tactic) (pro:tactic) =
  let sb = subst [n0,`n0:num`; cnt,`cnt:num`] in
  ENSURES_EVENTS_WHILE_UP2_TAC cnt
   `pc + mlkem_keccakf1600_xor_bytes_loop1`
   `pc + mlkem_keccakf1600_xor_bytes_loop1_exit` (XOR_INV1 n0 cnt) THEN
  REPEAT CONJ_TAC THENL
   [pos;

    pro;

    (*** The loop body, XORing in one byte, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    XOR_LOAD_FACTS_TAC "s0" (sb `off + (n0 + i)`) `len:num`
      [sb `n0 + i`] [] [] THEN
    XOR_REST_TAC "s0" (sb `off + (n0 + i)`) (sb `off + (n0 + (i + 1))`) THEN
    ARM_STEPS_TAC XOR_EXEC (1--6) THEN
    BYTE_CNT_TAC cnt THEN
    XOR_STORE_TAC (sb `n0 + i`) 1 THEN
    XOR_EXTEND_TAC (sb `n0 + i`) 1 (sb `n0 + (i + 1)`) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (subst [cnt,`cnt:num`] `~(i + 1 = cnt) <=> i + 1 < cnt`)
      (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC (subst [cnt,`cnt:num`] `i < cnt`) THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [XOR_PTR_EQ_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [XOR_PTR_EQ_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The return ***)

    REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN (sb `n0 + cnt = len`)
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC XOR_EXEC (1--1) THEN XOR_END_TAC `len:num`];;

(*** Reassociate the events in the postcondition only (not the precondition) ***)

let XOR_POST_ASSOC_TAC =
  CONV_TAC(RATOR_CONV(RAND_CONV(ONCE_DEPTH_CONV(REWR_CONV(GSYM APPEND_ASSOC)))));;

(* ------------------------------------------------------------------------- *)
(* The loads of the state and of the data, of 1, 8 and 16 bytes, at byte q   *)
(* of the state and byte j of the data, given the state from byte p on.      *)
(* ------------------------------------------------------------------------- *)

let XOR_LD sname kind p q j =
  let s = mk_var(sname,`:armstate`) in
  let lth,dth =
    match kind with
      1 -> XOR_LOAD8,READ_MEMORY_BYTES8_OF_NUM
    | 8 -> XOR_LOAD64,READ_MEMORY_BYTES64_OF_NUM
    | _ -> XOR_LOAD128,READ_MEMORY_BYTES128_OF_NUM in
  MP_TAC(SPECL [`a:int64`; `val(S:1600 word)`; p; q; s] lth) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`d:int64`; `len:num`; `m:num`; j; s] dth) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* The loop over blocks of 32 bytes, q = len DIV 32 iterations               *)
(* ------------------------------------------------------------------------- *)

let XOR_INV2 =
 `\i s. read X0 s = a /\ read X1 s = d /\
        read X8 s = word off /\ read X9 s = word len /\
        read X10 s = word(32 * (len DIV 32)) /\
        read X11 s = word_add (word_add d (word(32 * i))) (word 16) /\
        read X12 s = word_add (word_add a (word(off + 32 * i))) (word 16) /\
        read X13 s = word(32 * (len DIV 32 - i)) /\
        read X30 s = returnaddress /\
        read (memory :> bytes(d,len)) s = m /\
        read (memory :> bytes(a,off + 32 * i)) s =
        val(word_xor (S:1600 word) (word(2 EXP (8 * off) * m))) MOD
        2 EXP (8 * (off + 32 * i)) /\
        read (memory :> bytes(word_add a (word(off + 32 * i)),
                              200 - (off + 32 * i))) s =
        val S DIV 2 EXP (8 * (off + 32 * i))`;;

let XOR_MIDV =
 `\s. read X0 s = a /\ read X1 s = d /\
      read X8 s = word off /\ read X9 s = word len /\
      read X10 s = word(32 * (len DIV 32)) /\ read X30 s = returnaddress /\
      read (memory :> bytes(d,len)) s = m /\
      read (memory :> bytes(a,off + 32 * (len DIV 32))) s =
      val(word_xor (S:1600 word) (word(2 EXP (8 * off) * m))) MOD
      2 EXP (8 * (off + 32 * (len DIV 32))) /\
      read (memory :> bytes(word_add a (word(off + 32 * (len DIV 32))),
                            200 - (off + 32 * (len DIV 32)))) s =
      val S DIV 2 EXP (8 * (off + 32 * (len DIV 32)))`;;

let XOR_V2_PRO =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  XOR_START_TAC THEN
  MAP_EVERY XOR_STEP_TAC (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[WORD_AND_FFFFFFE0_64] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; SUB_0] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; DISCHARGE_SAFETY_PROPERTY_TAC];;

let XOR_V2_BODY =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `32 * i + 32 <= len` ASSUME_TAC THENL
   [UNDISCH_TAC `i < len DIV 32` THEN ARITH_TAC; ALL_TAC] THEN
  XOR_LD "s0" 16 `off + 32 * i` `off + 32 * i` `32 * i` THEN
  XOR_LD "s0" 16 `off + 32 * i` `(off + 32 * i) + 16` `32 * i + 16` THEN
  XOR_REST_TAC "s0" `off + 32 * i` `off + 32 * (i + 1)` THEN
  ARM_STEPS_TAC XOR_EXEC (1--9) THEN
  LOOP2_CNT_TAC THEN
  XOR_STORE_TAC `32 * i` 16 THEN
  XOR_STORE_TAC `32 * i + 16` 16 THEN
  XOR_EXTEND_TAC `32 * i` 16 `32 * i + 16` THEN
  XOR_EXTEND_TAC `32 * i + 16` 16 `32 * (i + 1)` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(i + 1 = len DIV 32) <=> i + 1 < len DIV 32`
    (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `i < len DIV 32` THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`; WORD_ADD] THEN
    CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `off + 32 * (i + 1) = (off + 32 * i) + 32`;
                WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let XOR_V2_EXIT =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The loop over blocks of 8 bytes, k3 iterations after n0 bytes             *)
(* ------------------------------------------------------------------------- *)

let XOR_INV3 n0 k3 =
  subst [n0,`n0:num`; k3,`k3:num`]
  `\i s. read X0 s = a /\ read X1 s = d /\
         read X8 s = word off /\ read X9 s = word len /\
         read X10 s = word(n0 + 8 * k3) /\
         read X11 s = word_add d (word(n0 + 8 * i)) /\
         read X12 s = word_add a (word(off + (n0 + 8 * i))) /\
         read X13 s = word_sub (word(n0 + 8 * i)) (word(n0 + 8 * k3)) /\
         read X30 s = returnaddress /\
         read (memory :> bytes(d,len)) s = m /\
         read (memory :> bytes(a,off + (n0 + 8 * i))) s =
         val(word_xor (S:1600 word) (word(2 EXP (8 * off) * m))) MOD
         2 EXP (8 * (off + (n0 + 8 * i))) /\
         read (memory :> bytes(word_add a (word(off + (n0 + 8 * i))),
                               200 - (off + (n0 + 8 * i)))) s =
         val S DIV 2 EXP (8 * (off + (n0 + 8 * i)))`;;

let XOR_MID3 =
 `\s. read X0 s = a /\ read X1 s = d /\
      read X8 s = word off /\ read X9 s = word len /\
      read X10 s = word(8 * (len DIV 8)) /\ read X30 s = returnaddress /\
      read (memory :> bytes(d,len)) s = m /\
      read (memory :> bytes(a,off + 8 * (len DIV 8))) s =
      val(word_xor (S:1600 word) (word(2 EXP (8 * off) * m))) MOD
      2 EXP (8 * (off + 8 * (len DIV 8))) /\
      read (memory :> bytes(word_add a (word(off + 8 * (len DIV 8))),
                            200 - (off + 8 * (len DIV 8)))) s =
      val S DIV 2 EXP (8 * (off + 8 * (len DIV 8)))`;;

let XOR_LOOP3_BODY n0 k3 =
  let sb = subst [n0,`n0:num`; k3,`k3:num`] in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN (sb `n0 + 8 * k3 <= len`) ASSUME_TAC THENL
   [SUBGOAL_THEN (sb `n0 + 8 * k3 = 8 * (len DIV 8)`) SUBST1_TAC THENL
     [FIRST [ACCEPT_TAC(SYM(SPEC `len:num` DIV8_SPLIT));
             REWRITE_TAC[ADD_CLAUSES]]; ALL_TAC] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (sb `n0 + 8 * i + 8 <= len`) ASSUME_TAC THENL
   [UNDISCH_TAC (sb `n0 + 8 * k3 <= len`) THEN
    UNDISCH_TAC (sb `i < k3`) THEN
    SPEC_TAC(k3,`k:num`) THEN SPEC_TAC(n0,`m:num`) THEN ARITH_TAC;
    ALL_TAC] THEN
  XOR_LD "s0" 8 (sb `off + (n0 + 8 * i)`) (sb `off + (n0 + 8 * i)`)
    (sb `n0 + 8 * i`) THEN
  XOR_REST_TAC "s0" (sb `off + (n0 + 8 * i)`) (sb `off + (n0 + 8 * (i + 1))`) THEN
  ARM_STEPS_TAC XOR_EXEC (1--6) THEN
  LOOP3_CNT_TAC n0 k3 THEN
  XOR_STORE_TAC (sb `n0 + 8 * i`) 8 THEN
  XOR_EXTEND_TAC (sb `n0 + 8 * i`) 8 (sb `n0 + 8 * (i + 1)`) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (sb `~(i + 1 = k3) <=> i + 1 < k3`)
    (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC (sb `i < k3`) THEN SPEC_TAC(k3,`k:num`) THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[WORD_ADD_PTR] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SPEC_TAC(n0,`m:num`) THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[WORD_ADD_PTR] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SPEC_TAC(n0,`m:num`) THEN ARITH_TAC; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let XOR_LOOP3_EXIT n0 k3 =
  let sb = subst [n0,`n0:num`; k3,`k3:num`] in
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN (sb `n0 + 8 * k3 = 8 * (len DIV 8)`)
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [FIRST [ACCEPT_TAC(SYM(SPEC `len:num` DIV8_SPLIT));
           REWRITE_TAC[ADD_CLAUSES]]; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let XOR_LOOP3_PHASE nested n0 k3 (pos:tactic) (pro:tactic) (tail:tactic) =
  XOR_POST_ASSOC_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_keccakf1600_xor_bytes_loop3_exit`
    XOR_MID3 THEN CONJ_TAC THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC k3
      `pc + mlkem_keccakf1600_xor_bytes_loop3`
      `pc + mlkem_keccakf1600_xor_bytes_loop3_exit` (XOR_INV3 n0 k3) THEN
    REPEAT CONJ_TAC THENL
     [pos; pro; XOR_LOOP3_BODY n0 k3; XOR_LOOP3_EXIT n0 k3];
    tail];;

(*** The prologue to loop3 for len < 32, from join4 ***)

let XOR_A3_PRO =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  XOR_START_TAC THEN
  MAP_EVERY XOR_STEP_TAC (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[WORD_AND_FFFFFFF8_64] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The tails                                                                 *)
(* ------------------------------------------------------------------------- *)

(*** After loop3: nothing if len MOD 8 = 0, else bytes ***)

let XOR_T30_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `8 * (len DIV 8) = len`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `len MOD 8 = 0` THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY XOR_STEP_TAC (1--2) THEN
  ARM_STEPS_TAC XOR_EXEC (3--3) THEN
  XOR_END_TAC `len:num`;;

let XOR_T31_PRO =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC XOR_EXEC (1--1) THEN TAIL3_CMP_TAC THEN
  ARM_STEPS_TAC XOR_EXEC (2--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_0; SUB_0; WORD_SUB_MOD8; WORD_ADD_PTR] THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let XOR_TAIL3_TAC =
  ASM_CASES_TAC `len MOD 8 = 0` THEN ASM_REWRITE_TAC[] THENL
   [XOR_T30_TAC;
    XOR_BYTELOOP_TAC `8 * (len DIV 8)` `(len MOD 8):num`
     (UNDISCH_TAC `~(len MOD 8 = 0)` THEN ARITH_TAC) XOR_T31_PRO];;

(*** After loop2 ***)

let XOR_T21_PRO =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC XOR_EXEC (1--1) THEN TAIL_CMP_TAC THEN
  ARM_STEPS_TAC XOR_EXEC (2--3) THEN TAIL_TST_TAC THEN
  ARM_STEPS_TAC XOR_EXEC (4--8) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; SUB_0; WORD_SUB_MOD32; WORD_ADD_PTR] THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let XOR_T3_PRO =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC XOR_EXEC (1--1) THEN TAIL_CMP_TAC THEN
  ARM_STEPS_TAC XOR_EXEC (2--3) THEN TAIL_TST_TAC THEN
  ARM_STEPS_TAC XOR_EXEC (4--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[WORD_AND_FFFFFFF8_64] THEN
  SUBST1_TAC(SPEC `len:num` DIV8_SPLIT) THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0; WORD_ADD_PTR] THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let XOR_T20_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `32 * (len DIV 32) = len`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `len MOD 32 = 0` THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY XOR_STEP_TAC (1--2) THEN
  ARM_STEPS_TAC XOR_EXEC (3--3) THEN
  XOR_END_TAC `len:num`;;

let XOR_TAIL2_TAC =
  ASM_CASES_TAC `len MOD 32 = 0` THEN ASM_REWRITE_TAC[] THENL
   [XOR_T20_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `len MOD 32 < 8` THEN ASM_REWRITE_TAC[] THENL
   [XOR_BYTELOOP_TAC `32 * (len DIV 32)` `(len MOD 32):num`
      (UNDISCH_TAC `~(len MOD 32 = 0)` THEN ARITH_TAC) XOR_T21_PRO;
    XOR_LOOP3_PHASE true `32 * (len DIV 32)` `(len MOD 32) DIV 8`
      (UNDISCH_TAC `~(len MOD 32 < 8)` THEN SPEC_TAC(`len MOD 32`,`r:num`) THEN
       ARITH_TAC)
      XOR_T3_PRO XOR_TAIL3_TAC];;

(*** The segment from join4, by the length ***)

let XOR_PATH_A_TAC =
  XOR_LOOP3_PHASE false `0` `len DIV 8` (UNDISCH_TAC `~(len <= 7)` THEN ARITH_TAC)
    XOR_A3_PRO XOR_TAIL3_TAC;;

let XOR_PATH_B_TAC =
  XOR_POST_ASSOC_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_keccakf1600_xor_bytes_loop2_exit`
    XOR_MIDV THEN CONJ_TAC THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `len DIV 32`
      `pc + mlkem_keccakf1600_xor_bytes_loop2`
      `pc + mlkem_keccakf1600_xor_bytes_loop2_exit` XOR_INV2 THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `~(len < 32)` THEN ARITH_TAC;
      XOR_V2_PRO; XOR_V2_BODY; XOR_V2_EXIT];
    XOR_TAIL2_TAC];;

let XOR_POS0_TAC = UNDISCH_TAC `~(len = 0)` THEN ARITH_TAC;;

(*** The prologues of the byte loop from the start ***)

let XOR_B1_PRO =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  XOR_START_TAC THEN
  ARM_STEPS_TAC XOR_EXEC (1--1) THEN XOR_ARGS_TAC THEN
  ARM_STEPS_TAC XOR_EXEC (2--3) THEN
  MAP_EVERY XOR_STEP_TAC (4--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let XOR_B2_PRO =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  XOR_START_TAC THEN
  ARM_STEPS_TAC XOR_EXEC (1--1) THEN XOR_ARGS_TAC THEN
  ARM_STEPS_TAC XOR_EXEC (2--3) THEN
  MAP_EVERY XOR_STEP_TAC (4--12) THEN
  ARM_STEPS_TAC XOR_EXEC [13] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[XOR_LS_LEMMA]) THEN XOR_BRANCH_TAC THEN
  MAP_EVERY XOR_STEP_TAC (14--18) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The segment up to join4 ***)

let XOR_MIDJ =
 `\s. read X0 s = a /\ read X1 s = d /\
      read X3 s = word len /\ read X8 s = word off /\ read X9 s = word len /\
      read X30 s = returnaddress /\
      read (memory :> bytes(d,len)) s = m /\
      read (memory :> bytes(a,200)) s = val(S:1600 word)`;;

let XOR_J4_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC XOR_EXEC (1--1) THEN XOR_ARGS_TAC THEN
  ARM_STEPS_TAC XOR_EXEC (2--3) THEN
  MAP_EVERY XOR_STEP_TAC (4--8) THEN
  ASM_CASES_TAC XOR_C1 THEN ASM_REWRITE_TAC[] THENL
   [XOR_STEP_TAC 9 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    SUBGOAL_THEN XOR_C2 ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY XOR_STEP_TAC (9--12) THEN
    ARM_STEPS_TAC XOR_EXEC [13] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[XOR_LS_LEMMA]) THEN XOR_BRANCH_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let XOR_MAIN_TAC =
  XOR_INTRO_TAC THEN
  ASM_CASES_TAC `len = 0` THEN ASM_REWRITE_TAC[] THENL
   [XOR_LEN0_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `len <= 7` THEN ASM_REWRITE_TAC[] THENL
   [XOR_BYTELOOP_TAC `0` `len:num` XOR_POS0_TAC XOR_B1_PRO; ALL_TAC] THEN
  ASM_CASES_TAC (mk_disj(XOR_C1,XOR_C2)) THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    FIRST_X_ASSUM(fun th ->
      if concl th = mk_neg(mk_disj(XOR_C1,XOR_C2))
      then STRIP_ASSUME_TAC(REWRITE_RULE[DE_MORGAN_THM] th) else NO_TAC) THEN
    XOR_BYTELOOP_TAC `0` `len:num` XOR_POS0_TAC XOR_B2_PRO] THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_keccakf1600_xor_bytes_join4`
    XOR_MIDJ THEN CONJ_TAC THENL
   [XOR_J4_TAC;
    ASM_CASES_TAC `len < 32` THEN ASM_REWRITE_TAC[] THENL
     [XOR_PATH_A_TAC; XOR_PATH_B_TAC]];;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof. As in        *)
(* keccak_absorb in common/fips202.ml, the state is a 1600-bit word S. The   *)
(* len bytes of data, as a number m, are XORed into it starting at byte off, *)
(* giving word_xor S (word(2 EXP (8 * off) * m)). In all the paths the state *)
(* is kept as the bytes before the next one to update, which are those of    *)
(* the final state, and the bytes from it on, which are those of S. The      *)
(* events are given by the path: the byte loop (entered directly for len < 8 *)
(* or after the two tests of overlap), or the segment up to join4 (which     *)
(* depends on which of the two tests succeeded) followed by the loop over    *)
(* the blocks of 32 bytes and the loops after it, or just the loop over the  *)
(* blocks of 8 bytes, as for mlkem_keccakf1600_extract_bytes. The theorems   *)
(* of correctness and of constant time and memory safety are derived from    *)
(* this one.                                                                 *)
(* ------------------------------------------------------------------------- *)


let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL =
  prove
 (`exists f_events.
       forall e a d off len (S:1600 word) m pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           off + len <= 200 /\
           ALL (nonoverlapping (a,200)) [word pc,libmlkem_size; d,len]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_keccakf1600_xor_bytes) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read (memory :> wbytes a) s = S /\
                    read (memory :> bytes(d,len)) s = m /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    read (memory :> wbytes a) s =
                    word_xor S (word(2 EXP (8 * off) * m)) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc returnaddress /\
                         memaccess_inbounds e2 [a,200; d,len] [a,200]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (a,200)])`,
  XOR_MAIN_TAC);;

(* ------------------------------------------------------------------------- *)
(* The theorems of correctness and of constant time and memory safety, from  *)
(* the combined one.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!a d off len (S:1600 word) m pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        off + len <= 200 /\
        ALL (nonoverlapping (a,200)) [(word pc,libmlkem_size); (d,len)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_keccakf1600_xor_bytes) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; d; word off; word len] s /\
                  read (memory :> wbytes a) s = S /\
                  read (memory :> bytes(d,len)) s = m)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes a) s =
                  word_xor S (word(2 EXP (8 * off) * m)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,200)])`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC `f:int64->int64->num->num->num->int64->(uarch_event)list`
   MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `d:int64`; `off:num`; `len:num`;
    `S:1600 word`; `m:num`; `pc:num`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  prove
 (`exists f_events.
       forall e a d off len pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           off + len <= 200 /\
           ALL (nonoverlapping (a,200)) [word pc,libmlkem_size; d,len]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_keccakf1600_xor_bytes) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc returnaddress /\
                         memaccess_inbounds e2 [a,200; d,len] [a,200]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (a,200)])`,
  MP_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `S:1600 word`
   `read (memory :> wbytes a):armstate->1600 word` THEN
  GHOST_INTRO_TAC `m:num` `read (memory :> bytes(d,len))` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `d:int64`; `off:num`; `len:num`;
    `S:1600 word`; `m:num`; `pc:num`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;
