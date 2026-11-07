(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* XOR of bytes into a Keccak state. This is the code for                    *)
(* mlkem_keccakf1600_xor_bytes from mlkem-native's portable C implementation *)
(* compiled by gcc 12 with -O3 (see mlkem_native/README.md), which XORs len  *)
(* bytes of data into the 200-byte state starting at byte off. Unlike at     *)
(* -O2, where it is a loop over the bytes, gcc has vectorized it as in       *)
(* mlkem_keccakf1600_extract_bytes: if len >= 8 and byte off of the state    *)
(* does not start within 15 bytes after byte 1 of the data, it XORs blocks   *)
(* of 16 bytes with Q registers, then possibly a block of 8 bytes with D     *)
(* registers, and then the last bytes one at a time; otherwise it XORs one   *)
(* byte at a time as at -O2. The specifications are those for -O2. It is     *)
(* verified in the whole image (see libmlkem.ml).                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_keccakf1600_xor_bytes:
       +0x0: mov     w2, w2
       +0x4: cbz     w3, <mlkem_keccakf1600_xor_bytes+0x4c>
       +0x8: sub     w6, w3, #0x1
       +0xc: add     x4, x0, x2
      +0x10: cmp     w6, #0x6
      +0x14: b.ls    <mlkem_keccakf1600_xor_bytes+0x28>
      +0x18: add     x5, x1, #0x1
      +0x1c: sub     x5, x4, x5
      +0x20: cmp     x5, #0xe
      +0x24: b.hi    <mlkem_keccakf1600_xor_bytes+0x50>
      +0x28: mov     w3, w3
      +0x2c: mov     x0, #0x0
      +0x30: ldrb    w2, [x4, x0]
      +0x34: ldrb    w5, [x1, x0]
      +0x38: eor     w2, w2, w5
      +0x3c: strb    w2, [x4, x0]
      +0x40: add     x0, x0, #0x1
      +0x44: cmp     x0, x3
      +0x48: b.ne    <mlkem_keccakf1600_xor_bytes+0x30>
      +0x4c: ret
      +0x50: cmp     w6, #0xe
      +0x54: b.ls    <mlkem_keccakf1600_xor_bytes+0x194>
      +0x58: and     x6, x3, #0xfffffff0
      +0x5c: mov     x5, #0x0
      +0x60: ldr     q0, [x4, x5]
      +0x64: ldr     q1, [x1, x5]
      +0x68: eor     v0.16b, v0.16b, v1.16b
      +0x6c: str     q0, [x4, x5]
      +0x70: add     x5, x5, #0x10
      +0x74: cmp     x5, x6
      +0x78: b.ne    <mlkem_keccakf1600_xor_bytes+0x60>
      +0x7c: and     w4, w3, #0xfffffff0
      +0x80: tst     x3, #0xf
      +0x84: b.eq    <mlkem_keccakf1600_xor_bytes+0x4c>
      +0x88: sub     w5, w3, w4
      +0x8c: sub     w6, w5, #0x1
      +0x90: cmp     w6, #0x6
      +0x94: b.ls    <mlkem_keccakf1600_xor_bytes+0xbc>
      +0x98: add     x6, x2, w4, uxtw
      +0x9c: ldr     d0, [x1, w4, uxtw]
      +0xa0: and     w7, w5, #0xfffffff8
      +0xa4: add     w4, w4, w7
      +0xa8: ldr     d1, [x0, x6]
      +0xac: eor     v0.8b, v0.8b, v1.8b
      +0xb0: str     d0, [x0, x6]
      +0xb4: tst     x5, #0x7
      +0xb8: b.eq    <mlkem_keccakf1600_xor_bytes+0x4c>
      +0xbc: add     x5, x2, w4, uxtw
      +0xc0: ldrb    w6, [x1, w4, uxtw]
      +0xc4: add     w7, w4, #0x1
      +0xc8: ldrb    w8, [x0, x5]
      +0xcc: eor     w6, w6, w8
      +0xd0: strb    w6, [x0, x5]
      +0xd4: cmp     w3, w7
      +0xd8: b.ls    <mlkem_keccakf1600_xor_bytes+0x4c>
      +0xdc: add     x8, x2, w7, uxtw
      +0xe0: ldrb    w5, [x1, w7, uxtw]
      +0xe4: add     w6, w4, #0x2
      +0xe8: ldrb    w7, [x0, x8]
      +0xec: eor     w5, w5, w7
      +0xf0: strb    w5, [x0, x8]
      +0xf4: cmp     w3, w6
      +0xf8: b.ls    <mlkem_keccakf1600_xor_bytes+0x4c>
      +0xfc: add     x7, x2, w6, uxtw
     +0x100: ldrb    w5, [x1, w6, uxtw]
     +0x104: add     w6, w4, #0x3
     +0x108: ldrb    w8, [x0, x7]
     +0x10c: eor     w5, w5, w8
     +0x110: strb    w5, [x0, x7]
     +0x114: cmp     w3, w6
     +0x118: b.ls    <mlkem_keccakf1600_xor_bytes+0x4c>
     +0x11c: add     x7, x2, w6, uxtw
     +0x120: ldrb    w5, [x1, w6, uxtw]
     +0x124: add     w6, w4, #0x4
     +0x128: ldrb    w8, [x0, x7]
     +0x12c: eor     w5, w5, w8
     +0x130: strb    w5, [x0, x7]
     +0x134: cmp     w3, w6
     +0x138: b.ls    <mlkem_keccakf1600_xor_bytes+0x4c>
     +0x13c: add     x7, x2, w6, uxtw
     +0x140: ldrb    w5, [x1, w6, uxtw]
     +0x144: add     w6, w4, #0x5
     +0x148: ldrb    w8, [x0, x7]
     +0x14c: eor     w5, w5, w8
     +0x150: strb    w5, [x0, x7]
     +0x154: cmp     w3, w6
     +0x158: b.ls    <mlkem_keccakf1600_xor_bytes+0x4c>
     +0x15c: add     x7, x2, w6, uxtw
     +0x160: ldrb    w5, [x1, w6, uxtw]
     +0x164: add     w4, w4, #0x6
     +0x168: ldrb    w6, [x0, x7]
     +0x16c: eor     w5, w5, w6
     +0x170: strb    w5, [x0, x7]
     +0x174: cmp     w3, w4
     +0x178: b.ls    <mlkem_keccakf1600_xor_bytes+0x4c>
     +0x17c: add     x2, x2, w4, uxtw
     +0x180: ldrb    w1, [x1, w4, uxtw]
     +0x184: ldrb    w3, [x0, x2]
     +0x188: eor     w1, w1, w3
     +0x18c: strb    w1, [x0, x2]
     +0x190: ret
     +0x194: mov     w5, w3
     +0x198: mov     w4, #0x0
     +0x19c: b       <mlkem_keccakf1600_xor_bytes+0x98>
 ***)

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_keccakf1600_xor_bytes"];;

(* ------------------------------------------------------------------------- *)
(* Reading 8 and 16 bytes of an array given as a number.                     *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES64_OF_NUM_STMT =
  `!a:int64 m n k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ k + 8 <= m
        ==> read (memory :> bytes64(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 64)`;;

let READ_MEMORY_BYTES64_OF_NUM = assume_spec READ_MEMORY_BYTES64_OF_NUM_STMT;;

let READ_MEMORY_BYTES128_OF_NUM_STMT =
  `!a:int64 m n k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ k + 16 <= m
        ==> read (memory :> bytes128(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 128)`;;

let READ_MEMORY_BYTES128_OF_NUM =
  assume_spec READ_MEMORY_BYTES128_OF_NUM_STMT;;

(*** A block of k bytes after the first j, both as numbers ***)

let READ_MEMORY_BYTES_EXTEND_STMT =
  `!d:int64 j k x s:armstate.
        read (memory :> bytes(d,j)) s = x MOD 2 EXP (8 * j) /\
        read (memory :> bytes(word_add d (word j),k)) s =
        (x DIV 2 EXP (8 * j)) MOD 2 EXP (8 * k)
        ==> read (memory :> bytes(d,j + k)) s = x MOD 2 EXP (8 * (j + k))`;;

let READ_MEMORY_BYTES_EXTEND = assume_spec READ_MEMORY_BYTES_EXTEND_STMT;;

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

let XOR_CHUNK_1_STMT =
  `!(S:1600 word) m off j.
        off + j + 1 <= 200
        ==> (val(word_xor S (word(2 EXP (8 * off) * m))) DIV
             2 EXP (8 * (off + j))) MOD 2 EXP (8 * 1) =
            val(word_xor (word((val S DIV 2 EXP (8 * (off + j))) MOD 256))
                         (word((m DIV 2 EXP (8 * j)) MOD 256)):byte)`;;

let XOR_CHUNK_1 = assume_spec XOR_CHUNK_1_STMT;;

let XOR_CHUNK_8_STMT =
  `!(S:1600 word) m off j.
        off + j + 8 <= 200
        ==> (val(word_xor S (word(2 EXP (8 * off) * m))) DIV
             2 EXP (8 * (off + j))) MOD 2 EXP (8 * 8) =
            val(word_xor
                 (word((val S DIV 2 EXP (8 * (off + j))) MOD 2 EXP 64))
                 (word((m DIV 2 EXP (8 * j)) MOD 2 EXP 64)):int64)`;;

let XOR_CHUNK_8 = assume_spec XOR_CHUNK_8_STMT;;

let XOR_CHUNK_16_STMT =
  `!(S:1600 word) m off j.
        off + j + 16 <= 200
        ==> (val(word_xor S (word(2 EXP (8 * off) * m))) DIV
             2 EXP (8 * (off + j))) MOD 2 EXP (8 * 16) =
            val(word_xor
                 (word((val S DIV 2 EXP (8 * (off + j))) MOD 2 EXP 128))
                 (word((m DIV 2 EXP (8 * j)) MOD 2 EXP 128)):int128)`;;

let XOR_CHUNK_16 = assume_spec XOR_CHUNK_16_STMT;;

(*** The bytes before byte off are those of S ***)

let XOR_LOW_STMT =
  `!(S:1600 word) m off.
        off <= 200
        ==> val(word_xor S (word(2 EXP (8 * off) * m))) MOD 2 EXP (8 * off) =
            val S MOD 2 EXP (8 * off)`;;

let XOR_LOW = assume_spec XOR_LOW_STMT;;

(*** The bytes from byte off + len on are those of S ***)

let XOR_HIGH_STMT =
  `!(S:1600 word) m off len.
        m < 2 EXP (8 * len) /\ off + len <= 200
        ==> val(word_xor S (word(2 EXP (8 * off) * m))) DIV
            2 EXP (8 * (off + len)) =
            val S DIV 2 EXP (8 * (off + len))`;;

let XOR_HIGH = assume_spec XOR_HIGH_STMT;;

(*** The final state from the bytes up to off + len and those after ***)

let XOR_FINAL_STMT =
  `!a d (S:1600 word) m off len s:armstate.
        off + len <= 200 /\
        read (memory :> bytes(d,len)) s = m /\
        read (memory :> bytes(a,off + len)) s =
        val(word_xor S (word(2 EXP (8 * off) * m))) MOD
        2 EXP (8 * (off + len)) /\
        read (memory :> bytes(word_add a (word(off + len)),200 - (off + len)))
          s = val S DIV 2 EXP (8 * (off + len))
        ==> read (memory :> bytes(a,200)) s =
            val(word_xor S (word(2 EXP (8 * off) * m)))`;;

let XOR_FINAL = assume_spec XOR_FINAL_STMT;;

(*** The first state, at the start of the code ***)

let XOR_START_STMT =
  `!a (S:1600 word) m off s:armstate.
        off <= 200 /\ read (memory :> bytes(a,200)) s = val S
        ==> read (memory :> bytes(a,off + 0)) s =
            val(word_xor S (word(2 EXP (8 * off) * m))) MOD
            2 EXP (8 * (off + 0)) /\
            read (memory :> bytes(word_add a (word(off + 0)),200 - (off + 0)))
              s = val S DIV 2 EXP (8 * (off + 0))`;;

let XOR_START = assume_spec XOR_START_STMT;;

(*** The rest of the state from byte p' on, from that from byte p on ***)

let XOR_REST_STMT =
  `!a v p p' s:armstate.
        read (memory :> bytes(word_add a (word p),200 - p)) s =
        v DIV 2 EXP (8 * p) /\ p <= p'
        ==> read (memory :> bytes(word_add a (word p'),200 - p')) s =
            v DIV 2 EXP (8 * p')`;;

let XOR_REST = assume_spec XOR_REST_STMT;;

(*** Reading 1, 8 and 16 bytes of the rest of the state ***)

let XOR_LOAD8_STMT =
  `!a v p q s:armstate.
        read (memory :> bytes(word_add a (word p),200 - p)) s =
        v DIV 2 EXP (8 * p) /\ p <= q /\ q < 200
        ==> read (memory :> bytes8(word_add a (word q))) s =
            word((v DIV 2 EXP (8 * q)) MOD 256)`;;

let XOR_LOAD8 = assume_spec XOR_LOAD8_STMT;;

let XOR_LOAD64_STMT =
  `!a v p q s:armstate.
        read (memory :> bytes(word_add a (word p),200 - p)) s =
        v DIV 2 EXP (8 * p) /\ p <= q /\ q + 8 <= 200
        ==> read (memory :> bytes64(word_add a (word q))) s =
            word((v DIV 2 EXP (8 * q)) MOD 2 EXP 64)`;;

let XOR_LOAD64 = assume_spec XOR_LOAD64_STMT;;

let XOR_LOAD128_STMT =
  `!a v p q s:armstate.
        read (memory :> bytes(word_add a (word p),200 - p)) s =
        v DIV 2 EXP (8 * p) /\ p <= q /\ q + 16 <= 200
        ==> read (memory :> bytes128(word_add a (word q))) s =
            word((v DIV 2 EXP (8 * q)) MOD 2 EXP 128)`;;

let XOR_LOAD128 = assume_spec XOR_LOAD128_STMT;;

(*** The bytes of stored 1-, 8- and 16-byte words as numbers ***)

let READ_MEMORY_BYTES_OF_WORD8_STMT =
  `!a:int64 (w:byte) s:armstate.
        read (memory :> bytes8 a) s = w
        ==> read (memory :> bytes(a,1)) s = val w`;;

let READ_MEMORY_BYTES_OF_WORD8 = assume_spec READ_MEMORY_BYTES_OF_WORD8_STMT;;

let READ_MEMORY_BYTES_OF_WORD64_STMT =
  `!a:int64 (w:int64) s:armstate.
        read (memory :> bytes64 a) s = w
        ==> read (memory :> bytes(a,8)) s = val w`;;

let READ_MEMORY_BYTES_OF_WORD64 =
  assume_spec READ_MEMORY_BYTES_OF_WORD64_STMT;;

let READ_MEMORY_BYTES_OF_WORD128_STMT =
  `!a:int64 (w:int128) s:armstate.
        read (memory :> bytes128 a) s = w
        ==> read (memory :> bytes(a,16)) s = val w`;;

let READ_MEMORY_BYTES_OF_WORD128 =
  assume_spec READ_MEMORY_BYTES_OF_WORD128_STMT;;

(* ------------------------------------------------------------------------- *)
(* Lemmas and tactics for the 32-bit arithmetic of the code on small         *)
(* numbers, and for the addresses with a 32-bit index register (UXTW).       *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_WORD_SMALL = prove
 (`!n. n < 2 EXP dimindex(:M)
       ==> (word_zx:M word->N word) (word n) = word n`,
  SIMP_TAC[WORD_ZX_WORD; MOD_LT]);;

let WORD_ZX_UXTW_SMALL_STMT =
  `!n. n < 2 EXP 32
       ==> word_zx(word_zx(word n:int64):int32):int64 = word n /\
           word_zx(word_zx(word_zx(word n:int64):int32):int32):int64 = word n`;;

let WORD_ZX_UXTW_SMALL = assume_spec WORD_ZX_UXTW_SMALL_STMT;;

let WORD_AND_FFFFFFF0_32_STMT =
  `!n. n < 2 EXP 32
       ==> word_and (word n:int32) (word 4294967280) = word(16 * n DIV 16)`;;

let WORD_AND_FFFFFFF0_32 = assume_spec WORD_AND_FFFFFFF0_32_STMT;;

let WORD_AND_FFFFFFF8_32_STMT =
  `!n. n < 2 EXP 32
       ==> word_and (word n:int32) (word 4294967288) = word(8 * n DIV 8)`;;

let WORD_AND_FFFFFFF8_32 = assume_spec WORD_AND_FFFFFFF8_32_STMT;;

let WORD_AND_FFFFFFF0_64_STMT =
  `!n. n < 2 EXP 32
       ==> word_and (word n:int64) (word 4294967280) = word(16 * n DIV 16)`;;

let WORD_AND_FFFFFFF0_64 = assume_spec WORD_AND_FFFFFFF0_64_STMT;;

let VAL_WORD_AND_15_STMT =
  `!n. val(word_and (word n:int64) (word 15)) = (n MOD 2 EXP 64) MOD 16`;;

let VAL_WORD_AND_15 = assume_spec VAL_WORD_AND_15_STMT;;

let VAL_WORD_AND_7_STMT =
  `!n. val(word_and (word n:int64) (word 7)) = (n MOD 2 EXP 64) MOD 8`;;

let VAL_WORD_AND_7 = assume_spec VAL_WORD_AND_7_STMT;;

(*** The test of the distance of the state from the data ***)

let XOR_NEAR_LEMMA_STMT =
  `!x:int64. (14 <= val x /\ ~(val(word_sub x (word 14)) = 0)) <=> 14 < val x`;;

let XOR_NEAR_LEMMA = assume_spec XOR_NEAR_LEMMA_STMT;;

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
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_EXEC [n] THEN
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

let WORD_ZX_MOD_64_STMT =
  `!t. word (t MOD 2 EXP 64):int128 = word_zx(word (t MOD 2 EXP 64):int64)`;;

let WORD_ZX_MOD_64 = assume_spec WORD_ZX_MOD_64_STMT;;

let WORD_ZX_MOD_8 =
  let th = prove
   (`!t. word (t MOD 256):N word = word_zx(word (t MOD 256):byte)`,
    REWRITE_TAC[WORD_ZX_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_REFL]) in
  CONJ (INST_TYPE [`:32`,`:N`] th) (INST_TYPE [`:64`,`:N`] th);;

let XOR_WORD_TAC =
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

let XOR_BYTE_STEPS ix c0 k s =
  if k = 0 then [] else
  let blk t = Some(ix(c0 + t),1,ix(c0 + t + 1)) in
  let rec go t s =
    if t = k then [] else
    if t = 6 then
      [s+1,None; s+2,None; s+3,None; s+4,None; s+5,blk t; s+6,None]
    else
      [s+1,None; s+2,None; s+3,None; s+4,None; s+5,None; s+6,blk t;
       s+7,None; s+8,None] @ go (t + 1) (s + 8) in
  let l = go 0 s in
  if k <= 6 then l @ [s + 8 * k + 1,None] else l;;

(*** The nonoverlapping of the stores with the code ***)

let XOR_CODE_NONOVERLAP_TAC blocks =
  MAP_EVERY (fun (j,k,_) ->
    SUBGOAL_THEN (subst [j,`j:num`; mk_small_numeral k,`k:num`]
      `nonoverlapping (word_add a (word(off + j)):int64,k)
                      (word pc,libmlkem_size)`)
    ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC]) blocks;;

(*** The steps, then the final state ***)

let XOR_RUN_TAC lt steps =
  MAP_EVERY (fun (n,st) ->
    (if n < 0 then
       ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_EXEC [-n] THEN
       XOR_TST_TAC
     else XOR_STEP_TAC n) THEN
    (match st with
       None -> ALL_TAC
     | Some(j,k,jn) -> XOR_STORE_TAC j k THEN XOR_EXTEND_TAC j k jn)) steps THEN
  XOR_FINISH_TAC lt THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ((CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCHARGE_SAFETY_PROPERTY_TAC])
   ORELSE DISCHARGE_SAFETY_PROPERTY_TAC);;

(*** The rest of the data after the blocks of 16 bytes, for ***)
(*** len = 16 * q + r, from the exit of the loop            ***)

let XOR_VTAIL_TAC r =
  let k = if r >= 8 then r - 8 else r and c0 = if r >= 8 then 8 else 0 in
  let ix c = if c = 0 then `16 * q` else
             mk_binop `(+):num->num->num` `16 * q` (mk_small_numeral c) in
  let lt = ix r in
  let byte_js = map (fun t -> ix (c0 + t)) (0--(k-1)) in
  let d_js = if r >= 8 then [ix 0] else [] in
  let dblk = if r >= 8 then [ix 0,8,ix 8] else [] in
  let bsteps = XOR_BYTE_STEPS ix c0 k in
  let plain = map (fun n -> n,None) in
  let dsteps = plain(8--13) @ map (fun b -> 14,Some b) dblk @ plain(15--16) in
  let steps =
    if r = 0 then [1,None; -2,None] @ plain(3--4) else
    if r <= 7 then [1,None; -2,None] @ plain(3--7) @ bsteps 7 else
    if r = 8 then [1,None; -2,None] @ plain(3--7) @ dsteps @ [17,None] else
    [1,None; -2,None] @ plain(3--7) @ dsteps @ bsteps 16 in
  let blocks = dblk @ map (fun t -> ix(c0 + t),1,ix(c0 + t + 1)) (0--(k-1)) in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  XOR_ZX_FACTS_TAC (d_js @ byte_js) THEN
  XOR_LOAD_FACTS_TAC "s0" `off + 16 * q` lt byte_js d_js [] THEN
  XOR_REST_TAC "s0" `off + 16 * q`
   (mk_binop `(+):num->num->num` `off:num` lt) THEN
  XOR_CODE_NONOVERLAP_TAC blocks THEN
  XOR_RUN_TAC lt steps;;

(*** The events, by the path taken: nothing for len = 0; the byte loop,   ***)
(*** entered after one or two tests; for 8 <= len < 16 a straight line;   ***)
(*** otherwise the loop over blocks of 16 bytes and then the rest, by     ***)
(*** len MOD 16. The straight lines have len (or len DIV 16) as argument  ***)
(*** only through the number of whole blocks, so that len can be          ***)
(*** replaced by its value in them.                                       ***)

let XOR_EVENTS_TERM =
  let ev nm args = "f_ev_" ^ nm ^ " " ^ args in
  let full = "a d off len pc returnaddress"
  and short = "a d off pc returnaddress"
  and tailargs = "a d off (len DIV 16) pc returnaddress" in
  let rec cases var lo hi pfx args =
    if lo = hi then ev (pfx ^ string_of_int lo) args else
    "(if " ^ var ^ " = " ^ string_of_int lo ^ " then " ^
    ev (pfx ^ string_of_int lo) args ^ " else " ^
    cases var (lo + 1) hi pfx args ^ ")" in
  let byteloop k =
    "APPEND (" ^ ev ("be" ^ k) full ^ ") (APPEND (ENUMERATEL len (\\i. " ^
    ev ("bl" ^ k) full ^ " i)) (" ^ ev ("bp" ^ k) full ^ "))" in
  parse_term
   ("\\(a:int64) (d:int64) (off:num) (len:num) (pc:num) " ^
    "(returnaddress:int64). " ^
    "if len = 0 then " ^ ev "len0" full ^
    " else if len <= 7 then " ^ byteloop "1" ^
    " else if ~(14 < val(word_sub (word_add a (word off))" ^
    " (word_add d (word 1)):int64))" ^
    " then " ^ byteloop "2" ^
    " else if len < 16 then " ^ cases "len" 8 15 "s" short ^
    " else APPEND " ^ cases "len MOD 16" 0 15 "r" tailargs ^
    " (APPEND (" ^ ev "ve" full ^ ") (APPEND (ENUMERATEL (len DIV 16) (\\i. " ^
    ev "vl" full ^ " i)) (" ^ ev "vp" full ^ "))) :(uarch_event)list");;


(*** The prologue up to the test of the distance and after it ***)

let XOR_BYTES_ARGS_TAC =
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  FIRST_ASSUM(fun th ->
    if concl th <> `~(len = 0)` then NO_TAC else
    RULE_ASSUM_TAC(fun th' ->
      if concl th' = concl th then th' else REWRITE_RULE[th] th'));;

let XOR_PROLOGUE_TAC n =
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_EXEC (1--2) THEN
  TRY XOR_BYTES_ARGS_TAC THEN TRY(ARGS_32_TAC [`off:num`]) THEN
  MAP_EVERY (fun i ->
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_EXEC [i] THEN
    W_NORM_TAC THEN TRY XOR_W32_DECIDE_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[XOR_NEAR_LEMMA]) THEN XOR_BRANCH_TAC)
   (3--n);;

(*** The state at the start, as the bytes before byte off + 0 and from it ***)

let XOR_START_TAC =
  MP_TAC(SPECL [`a:int64`; `S:1600 word`; `m:num`; `off:num`; `s0:armstate`]
               XOR_START) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; STRIP_TAC];;

(*** The invariant of the loop over the bytes ***)

let XOR_INV1 =
 `\i s. read X0 s = word i /\ read X1 s = d /\ read X3 s = word len /\
        read X4 s = word_add a (word off) /\
        read X30 s = returnaddress /\
        read (memory :> bytes(d,len)) s = m /\
        read (memory :> bytes(a,off + i)) s =
        val(word_xor (S:1600 word) (word(2 EXP (8 * off) * m))) MOD
        2 EXP (8 * (off + i)) /\
        read (memory :> bytes(word_add a (word(off + i)),200 - (off + i))) s =
        val S DIV 2 EXP (8 * (off + i))`;;

let XOR_BYTELOOP_TAC n =
  ENSURES_EVENTS_WHILE_UP2_TAC `len:num`
   `pc + mlkem_keccakf1600_xor_bytes_loop1`
   `pc + mlkem_keccakf1600_xor_bytes_loop1_exit` XOR_INV1 THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** The prologue to the loop ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    XOR_START_TAC THEN XOR_PROLOGUE_TAC n THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, for one byte, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    XOR_LOAD_FACTS_TAC "s0" `off + i` `len:num` [`i:num`] [] [] THEN
    XOR_REST_TAC "s0" `off + i` `off + (i + 1)` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_EXEC (1--5) THEN
    W_NORM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_EXEC (6--6) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_EXEC (7--7) THEN
    XOR_STORE_TAC `i:num` 1 THEN XOR_EXTEND_TAC `i:num` 1 `i + 1` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(i + 1 = len) <=> i + 1 < len` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `i < len` THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The return ***)

    REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    XOR_RUN_TAC `len:num` [1,None]];;

(*** The blocks of 16 bytes, up to the exit of their loop ***)

let XOR_INV2 =
 `\i s. read X5 s = word(16 * i) /\ read X0 s = a /\ read X1 s = d /\
        read X2 s = word off /\ read X3 s = word len /\
        read X4 s = word_add a (word off) /\
        read X6 s = word(16 * len DIV 16) /\ read X30 s = returnaddress /\
        read (memory :> bytes(d,len)) s = m /\
        read (memory :> bytes(a,off + 16 * i)) s =
        val(word_xor (S:1600 word) (word(2 EXP (8 * off) * m))) MOD
        2 EXP (8 * (off + 16 * i)) /\
        read (memory :> bytes(word_add a (word(off + 16 * i)),
                              200 - (off + 16 * i))) s =
        val S DIV 2 EXP (8 * (off + 16 * i))`;;

let XOR_MIDV =
 `\s. read X0 s = a /\ read X1 s = d /\
      read X2 s = word off /\ read X3 s = word len /\
      read X30 s = returnaddress /\
      read (memory :> bytes(d,len)) s = m /\
      read (memory :> bytes(a,off + 16 * len DIV 16)) s =
      val(word_xor (S:1600 word) (word(2 EXP (8 * off) * m))) MOD
      2 EXP (8 * (off + 16 * len DIV 16)) /\
      read (memory :> bytes(word_add a (word(off + 16 * len DIV 16)),
                            200 - (off + 16 * len DIV 16))) s =
      val S DIV 2 EXP (8 * (off + 16 * len DIV 16))`;;

let XOR_LOOP2_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `len DIV 16`
   `pc + mlkem_keccakf1600_xor_bytes_loop2`
   `pc + mlkem_keccakf1600_xor_bytes_loop2_exit` XOR_INV2 THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_EQ];

    (*** The prologue to the loop ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    XOR_START_TAC THEN XOR_PROLOGUE_TAC 12 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_EXEC
     (13--13) THEN
    XOR_NORM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_EXEC
     (14--14) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, for 16 bytes, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `16 * i + 16 <= len` ASSUME_TAC THENL
     [UNDISCH_TAC `i < len DIV 16` THEN
      REWRITE_TAC[ARITH_RULE `i < q <=> i + 1 <= q`] THEN
      SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ARITH_TAC;
      ALL_TAC] THEN
    XOR_LOAD_FACTS_TAC "s0" `off + 16 * i` `len:num` [] [] [`16 * i`] THEN
    XOR_REST_TAC "s0" `off + 16 * i` `off + 16 * (i + 1)` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_EXEC (1--5) THEN
    W_NORM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_EXEC (6--6) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_EXEC (7--7) THEN
    XOR_STORE_TAC `16 * i` 16 THEN
    XOR_EXTEND_TAC `16 * i` 16 `16 * (i + 1)` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(16 * i + 16 = 16 * len DIV 16) <=> i + 1 < len DIV 16`
     SUBST_ALL_TAC THENL
     [UNDISCH_TAC `i < len DIV 16` THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The exit of the loop ***)

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

(*** The case len MOD 16 = r after the blocks of 16 bytes ***)

let XOR_RCASE_TAC r =
  let rt = mk_small_numeral r in
  ASM_REWRITE_TAC[ARITH_EQ] THEN
  ABBREV_TAC `q = len DIV 16` THEN
  SUBGOAL_THEN (mk_eq(`len:num`,
     if r = 0 then `16 * q` else mk_binop `(+):num->num->num` `16 * q` rt))
    SUBST_ALL_TAC THENL
   [EXPAND_TAC "q" THEN
    FIRST_X_ASSUM(MP_TAC o check
      (fun th -> concl th = mk_eq(`len MOD 16`,rt))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  XOR_VTAIL_TAC r;;

(*** Case splits on the value of a numeric term x < n ***)

let XOR_NUM_CASES_TAC x n ttac =
  let disj = list_mk_disj(map (fun i -> mk_eq(x,mk_small_numeral i))
                              (0--(n-1))) in
  MP_TAC(ARITH_RULE(mk_imp(mk_binop `(<):num->num->bool` x
                                    (mk_small_numeral n),disj))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ttac);;

let XOR_RCASES_TAC =
  XOR_NUM_CASES_TAC `len MOD 16` 16 (fun th ->
    ASSUME_TAC th THEN XOR_RCASE_TAC (dest_small_numeral(rand(concl th))));;

(*** The cases 8 <= len < 16, as straight-line code with len known ***)

let XOR_SHORT_CASE_TAC l =
  let k = l - 8 in
  let ix c = mk_small_numeral c in
  let lt = ix l in
  let byte_js = map (fun t -> ix (8 + t)) (0--(k-1)) in
  let dblk = (`0`,8,ix 8) in
  let plain = map (fun n -> n,None) in
  let steps =
    plain(13--21) @ [22,Some dblk] @ plain(23--24) @
    (if k = 0 then [25,None] else XOR_BYTE_STEPS ix 8 k 24) in
  let blocks = dblk :: map (fun t -> ix(8 + t),1,ix(9 + t)) (0--(k-1)) in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  XOR_START_TAC THEN
  XOR_LOAD_FACTS_TAC "s0" `off + 0` lt byte_js [`0`] [] THEN
  XOR_REST_TAC "s0" `off + 0` (mk_binop `(+):num->num->num` `off:num` lt) THEN
  XOR_CODE_NONOVERLAP_TAC blocks THEN
  XOR_PROLOGUE_TAC 12 THEN
  XOR_RUN_TAC lt steps;;

let XOR_SHORT_TAC =
  SUBGOAL_THEN `len - 8 < 8` ASSUME_TAC THENL
   [UNDISCH_TAC `len < 16` THEN ARITH_TAC; ALL_TAC] THEN
  XOR_NUM_CASES_TAC `len - 8` 8 (fun th ->
    let l = dest_small_numeral(rand(concl th)) + 8 in
    SUBGOAL_THEN (mk_eq(`len:num`,mk_small_numeral l)) SUBST_ALL_TAC THENL
     [MP_TAC th THEN UNDISCH_TAC `~(len <= 7)` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_EQ] THEN XOR_SHORT_CASE_TAC l);;

(*** The case len = 0, where the data is 0 ***)

let XOR_LEN0_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] o
    check (fun th -> is_eq(concl th) && rand(concl th) = `m:num`)) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_EXEC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; WORD_XOR_0] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;


(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof. As in        *)
(* keccak_absorb in common/fips202.ml, the state is a 1600-bit word S. The   *)
(* len bytes of data, as a number m, are XORed into it starting at byte off, *)
(* giving word_xor S (word(2 EXP (8 * off) * m)). In all the paths the state *)
(* is kept as the bytes before the next one to update, which are those of    *)
(* the final state, and the bytes from it on, which are those of S. The      *)
(* events are given by the path: the byte loop (entered after one or two     *)
(* tests), a straight line for 8 <= len < 16, or the loop over the blocks of *)
(* 16 bytes and a straight line depending on len MOD 16. The theorems of     *)
(* correctness and of constant time and memory safety are derived from this  *)
(* one.                                                                      *)
(* ------------------------------------------------------------------------- *)

let XOR_INTRO_TAC =
  CONCRETIZE_F_EVENTS_TAC XOR_EVENTS_TERM THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d:int64`; `off:num`; `len:num`; `S:1600 word`; `m:num`;
    `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              READ_MEMORY_WBYTES_VAL;
              fst MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_EXEC] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `len < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `off + len <= 200` THEN ARITH_TAC; ALL_TAC];;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e a d off len (S:1600 word) m pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           off + len <= 200 /\
           ALL (nonoverlapping (a,200)) [word pc,libmlkem_size; d,len]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O3_mc /\
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
                MAYCHANGE [memory :> bytes (a,200)])`;;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* The theorems of correctness and of constant time and memory safety, from  *)
(* the combined one.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a d off len (S:1600 word) m pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        off + len <= 200 /\
        ALL (nonoverlapping (a,200)) [(word pc,libmlkem_size); (d,len)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_keccakf1600_xor_bytes) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; d; word off; word len] s /\
                  read (memory :> wbytes a) s = S /\
                  read (memory :> bytes(d,len)) s = m)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes a) s =
                  word_xor S (word(2 EXP (8 * off) * m)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,200)])`;;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a d off len pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           off + len <= 200 /\
           ALL (nonoverlapping (a,200)) [word pc,libmlkem_size; d,len]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O3_mc /\
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
                MAYCHANGE [memory :> bytes (a,200)])`;;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
