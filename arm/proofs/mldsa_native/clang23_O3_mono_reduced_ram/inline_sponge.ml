(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Shared lemmas and tactics for the SHAKE sponge code that clang 23 inlined *)
(* into the functions of the clang23_O3_mono_reduced_ram image: XORing of    *)
(* bytes into the Keccak state and extraction of bytes from it.              *)
(* Part 1: the arithmetic of the state as a number and as bytes, and the     *)
(* tactics for stepping code that XORs, copied from the proof of             *)
(* mlkem_keccakf1600_xor_bytes of mlkem-native's clang17_O3 build            *)
(* (proofs/mlkem_native/clang17_O3/keccakf1600_xor_bytes_*.ml).              *)
(* Part 2: lemmas, from the head of a loop to its exit, for the four shapes  *)
(* of loop that clang 23 -O3 generates for XORing bytes of data into the     *)
(* state (the byte loops with a post-incremented pointer and with an index,  *)
(* the loop over blocks of 8 bytes with D registers and the loop over blocks *)
(* of 32 bytes with Q registers), as generators of the lemma and its proof   *)
(* for the loop labels and registers of an instance, like inline_loops.ml of *)
(* mlkem_native. Each lemma has the correctness and the events.              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(* ------------------------------------------------------------------------- *)
(* Reading 8 and 16 bytes of an array given as a number.                     *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES64_OF_NUM_STMT =
  `!a:int64 m n k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ k + 8 <= m
        ==> read (memory :> bytes64(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 64)`;;

let READ_MEMORY_BYTES64_OF_NUM = prove
 (READ_MEMORY_BYTES64_OF_NUM_STMT,
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

let READ_MEMORY_BYTES128_OF_NUM_STMT =
  `!a:int64 m n k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ k + 16 <= m
        ==> read (memory :> bytes128(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 128)`;;

let READ_MEMORY_BYTES128_OF_NUM = prove
 (READ_MEMORY_BYTES128_OF_NUM_STMT,
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

let READ_MEMORY_BYTES_EXTEND_STMT =
  `!d:int64 j k x s:armstate.
        read (memory :> bytes(d,j)) s = x MOD 2 EXP (8 * j) /\
        read (memory :> bytes(word_add d (word j),k)) s =
        (x DIV 2 EXP (8 * j)) MOD 2 EXP (8 * k)
        ==> read (memory :> bytes(d,j + k)) s = x MOD 2 EXP (8 * (j + k))`;;

let READ_MEMORY_BYTES_EXTEND = prove
 (READ_MEMORY_BYTES_EXTEND_STMT,
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

let XOR_CHUNK_1_STMT =
  `!(S:1600 word) m off j.
        off + j + 1 <= 200
        ==> (val(word_xor S (word(2 EXP (8 * off) * m))) DIV
             2 EXP (8 * (off + j))) MOD 2 EXP (8 * 1) =
            val(word_xor (word((val S DIV 2 EXP (8 * (off + j))) MOD 256))
                         (word((m DIV 2 EXP (8 * j)) MOD 256)):byte)`;;

let XOR_CHUNK_1 = prove
 (XOR_CHUNK_1_STMT,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`S:1600 word`; `m:num`; `off:num`; `j:num`; `1`]
         (INST_TYPE [`:8`,`:N`] XOR_CHUNK)) THEN
  ASM_REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let XOR_CHUNK_8_STMT =
  `!(S:1600 word) m off j.
        off + j + 8 <= 200
        ==> (val(word_xor S (word(2 EXP (8 * off) * m))) DIV
             2 EXP (8 * (off + j))) MOD 2 EXP (8 * 8) =
            val(word_xor
                 (word((val S DIV 2 EXP (8 * (off + j))) MOD 2 EXP 64))
                 (word((m DIV 2 EXP (8 * j)) MOD 2 EXP 64)):int64)`;;

let XOR_CHUNK_8 = prove
 (XOR_CHUNK_8_STMT,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`S:1600 word`; `m:num`; `off:num`; `j:num`; `8`]
         (INST_TYPE [`:64`,`:N`] XOR_CHUNK)) THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let XOR_CHUNK_16_STMT =
  `!(S:1600 word) m off j.
        off + j + 16 <= 200
        ==> (val(word_xor S (word(2 EXP (8 * off) * m))) DIV
             2 EXP (8 * (off + j))) MOD 2 EXP (8 * 16) =
            val(word_xor
                 (word((val S DIV 2 EXP (8 * (off + j))) MOD 2 EXP 128))
                 (word((m DIV 2 EXP (8 * j)) MOD 2 EXP 128)):int128)`;;

let XOR_CHUNK_16 = prove
 (XOR_CHUNK_16_STMT,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`S:1600 word`; `m:num`; `off:num`; `j:num`; `16`]
         (INST_TYPE [`:128`,`:N`] XOR_CHUNK)) THEN
  ASM_REWRITE_TAC[DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

(*** The bytes before byte off are those of S ***)

let XOR_LOW_STMT =
  `!(S:1600 word) m off.
        off <= 200
        ==> val(word_xor S (word(2 EXP (8 * off) * m))) MOD 2 EXP (8 * off) =
            val S MOD 2 EXP (8 * off)`;;

let XOR_LOW = prove
 (XOR_LOW_STMT,
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

let XOR_HIGH_STMT =
  `!(S:1600 word) m off len.
        m < 2 EXP (8 * len) /\ off + len <= 200
        ==> val(word_xor S (word(2 EXP (8 * off) * m))) DIV
            2 EXP (8 * (off + len)) =
            val S DIV 2 EXP (8 * (off + len))`;;

let XOR_HIGH = prove
 (XOR_HIGH_STMT,
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

let XOR_FINAL = prove
 (XOR_FINAL_STMT,
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

let XOR_START_STMT =
  `!a (S:1600 word) m off s:armstate.
        off <= 200 /\ read (memory :> bytes(a,200)) s = val S
        ==> read (memory :> bytes(a,off + 0)) s =
            val(word_xor S (word(2 EXP (8 * off) * m))) MOD
            2 EXP (8 * (off + 0)) /\
            read (memory :> bytes(word_add a (word(off + 0)),200 - (off + 0)))
              s = val S DIV 2 EXP (8 * (off + 0))`;;

let XOR_START = prove
 (XOR_START_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[XOR_LOW] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
  ASM_SIMP_TAC[ARITH_RULE `off <= 200 ==> MIN 200 off = off`]);;

(*** The rest of the state from byte p' on, from that from byte p on ***)

let XOR_REST_STMT =
  `!a v p p' s:armstate.
        read (memory :> bytes(word_add a (word p),200 - p)) s =
        v DIV 2 EXP (8 * p) /\ p <= p'
        ==> read (memory :> bytes(word_add a (word p'),200 - p')) s =
            v DIV 2 EXP (8 * p')`;;

let XOR_REST = prove
 (XOR_REST_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
    (CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS])) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\x. x DIV 2 EXP (8 * d)`) THEN
  REWRITE_TAC[READ_BYTES_DIV; DIV_DIV; GSYM EXP_ADD; GSYM LEFT_ADD_DISTRIB;
              GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `200 - p - d = 200 - (p + d)`]);;

(*** Reading 1, 8 and 16 bytes of the rest of the state ***)

let XOR_LOAD8_STMT =
  `!a v p q s:armstate.
        read (memory :> bytes(word_add a (word p),200 - p)) s =
        v DIV 2 EXP (8 * p) /\ p <= q /\ q < 200
        ==> read (memory :> bytes8(word_add a (word q))) s =
            word((v DIV 2 EXP (8 * q)) MOD 256)`;;

let XOR_LOAD8 = prove
 (XOR_LOAD8_STMT,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `v:num`; `p:num`; `q:num`; `s:armstate`]
         XOR_REST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`word_add a (word q):int64`; `200 - q`; `v DIV 2 EXP (8 * q)`;
                `0`; `s:armstate`] READ_MEMORY_BYTES8_OF_NUM) THEN
  ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; EXP; DIV_1] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let XOR_LOAD64_STMT =
  `!a v p q s:armstate.
        read (memory :> bytes(word_add a (word p),200 - p)) s =
        v DIV 2 EXP (8 * p) /\ p <= q /\ q + 8 <= 200
        ==> read (memory :> bytes64(word_add a (word q))) s =
            word((v DIV 2 EXP (8 * q)) MOD 2 EXP 64)`;;

let XOR_LOAD64 = prove
 (XOR_LOAD64_STMT,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `v:num`; `p:num`; `q:num`; `s:armstate`]
         XOR_REST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`word_add a (word q):int64`; `200 - q`; `v DIV 2 EXP (8 * q)`;
                `0`; `s:armstate`] READ_MEMORY_BYTES64_OF_NUM) THEN
  ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; EXP; DIV_1] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let XOR_LOAD128_STMT =
  `!a v p q s:armstate.
        read (memory :> bytes(word_add a (word p),200 - p)) s =
        v DIV 2 EXP (8 * p) /\ p <= q /\ q + 16 <= 200
        ==> read (memory :> bytes128(word_add a (word q))) s =
            word((v DIV 2 EXP (8 * q)) MOD 2 EXP 128)`;;

let XOR_LOAD128 = prove
 (XOR_LOAD128_STMT,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `v:num`; `p:num`; `q:num`; `s:armstate`]
         XOR_REST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`word_add a (word q):int64`; `200 - q`; `v DIV 2 EXP (8 * q)`;
                `0`; `s:armstate`] READ_MEMORY_BYTES128_OF_NUM) THEN
  ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; EXP; DIV_1] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(*** The bytes of stored 1-, 8- and 16-byte words as numbers ***)

let READ_MEMORY_BYTES_OF_WORD8_STMT =
  `!a:int64 (w:byte) s:armstate.
        read (memory :> bytes8 a) s = w
        ==> read (memory :> bytes(a,1)) s = val w`;;

let READ_MEMORY_BYTES_OF_WORD8 = prove
 (READ_MEMORY_BYTES_OF_WORD8_STMT,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BYTES8] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let READ_MEMORY_BYTES_OF_WORD64_STMT =
  `!a:int64 (w:int64) s:armstate.
        read (memory :> bytes64 a) s = w
        ==> read (memory :> bytes(a,8)) s = val w`;;

let READ_MEMORY_BYTES_OF_WORD64 = prove
 (READ_MEMORY_BYTES_OF_WORD64_STMT,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  REWRITE_TAC[VAL_READ_WBYTES; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let READ_MEMORY_BYTES_OF_WORD128_STMT =
  `!a:int64 (w:int128) s:armstate.
        read (memory :> bytes128 a) s = w
        ==> read (memory :> bytes(a,16)) s = val w`;;

let READ_MEMORY_BYTES_OF_WORD128 = prove
 (READ_MEMORY_BYTES_OF_WORD128_STMT,
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

let WORD_ZX_UXTW_SMALL_STMT =
  `!n. n < 2 EXP 32
       ==> word_zx(word_zx(word n:int64):int32):int64 = word n /\
           word_zx(word_zx(word_zx(word n:int64):int32):int32):int64 = word n`;;

let WORD_ZX_UXTW_SMALL = prove
 (WORD_ZX_UXTW_SMALL_STMT,
  REWRITE_TAC[WORD_ZX_TRIVIAL] THEN SIMP_TAC[WORD_ZX_32_SMALL]);;

let WORD_AND_FFFFFFF0_32_STMT =
  `!n. n < 2 EXP 32
       ==> word_and (word n:int32) (word 4294967280) = word(16 * n DIV 16)`;;

let WORD_AND_FFFFFFF0_32 = prove
 (WORD_AND_FFFFFFF0_32_STMT,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(SYM((NUM_REDUCE_CONV THENC WORD_REDUCE_CONV)
    `word_not(word(2 EXP 4 - 1)):int32`)) THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD; VAL_WORD; DIMINDEX_32] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_AND_FFFFFFF8_32_STMT =
  `!n. n < 2 EXP 32
       ==> word_and (word n:int32) (word 4294967288) = word(8 * n DIV 8)`;;

let WORD_AND_FFFFFFF8_32 = prove
 (WORD_AND_FFFFFFF8_32_STMT,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(SYM((NUM_REDUCE_CONV THENC WORD_REDUCE_CONV)
    `word_not(word(2 EXP 3 - 1)):int32`)) THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD; VAL_WORD; DIMINDEX_32] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_AND_FFFFFFF0_64_STMT =
  `!n. n < 2 EXP 32
       ==> word_and (word n:int64) (word 4294967280) = word(16 * n DIV 16)`;;

let WORD_AND_FFFFFFF0_64 = prove
 (WORD_AND_FFFFFFF0_64_STMT,
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

let VAL_WORD_AND_15_STMT =
  `!n. val(word_and (word n:int64) (word 15)) = (n MOD 2 EXP 64) MOD 16`;;

let VAL_WORD_AND_15 = prove
 (VAL_WORD_AND_15_STMT,
  GEN_TAC THEN
  SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 EXP 4 - 1`)) THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let VAL_WORD_AND_7_STMT =
  `!n. val(word_and (word n:int64) (word 7)) = (n MOD 2 EXP 64) MOD 8`;;

let VAL_WORD_AND_7 = prove
 (VAL_WORD_AND_7_STMT,
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

let XOR_STEP_TAC_EXEC exec n =
  ARM_STEPS_TAC exec [n] THEN
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

let WORD_ZX_MOD_64 = prove
 (WORD_ZX_MOD_64_STMT,
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

let BYTE_CNT_LEMMA_STMT =
  `!cnt i. i < cnt /\ cnt < 2 EXP 64
           ==> (val(word_sub (word (cnt - i)) (word 1):int64) = 0 <=>
                i + 1 = cnt) /\
               word_sub (word (cnt - i)) (word 1):int64 =
               word (cnt - (i + 1))`;;

let BYTE_CNT_LEMMA = prove
 (BYTE_CNT_LEMMA_STMT,
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

let LOOP2_CNT_LEMMA_STMT =
  `!q i. i < q /\ q < 2 EXP 32
         ==> (val(word_sub (word (32 * (q - i))) (word 32):int64) = 0 <=>
              i + 1 = q) /\
             word_sub (word (32 * (q - i))) (word 32):int64 =
             word (32 * (q - (i + 1)))`;;

let LOOP2_CNT_LEMMA = prove
 (LOOP2_CNT_LEMMA_STMT,
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

let WORD_AND_FFFFFFE0_32_STMT =
  `!n. n < 2 EXP 32
       ==> word_and (word n:int32) (word 4294967264) = word(32 * n DIV 32)`;;

let WORD_AND_FFFFFFE0_32 = prove
 (WORD_AND_FFFFFFE0_32_STMT,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(SYM((NUM_REDUCE_CONV THENC WORD_REDUCE_CONV)
    `word_not(word(2 EXP 5 - 1)):int32`)) THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD; VAL_WORD; DIMINDEX_32] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_AND_FFFFFFE0_64_STMT =
  `!n. n < 2 EXP 32
       ==> word_and (word n:int64) (word 4294967264) = word(32 * n DIV 32)`;;

let WORD_AND_FFFFFFE0_64 = prove
 (WORD_AND_FFFFFFE0_64_STMT,
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

let TAIL_CMP_LEMMA_STMT =
  `!len. len < 2 EXP 32
         ==> (val(word_sub (word (32 * len DIV 32)) (word len):int64) = 0 <=>
              len MOD 32 = 0)`;;

let TAIL_CMP_LEMMA = prove
 (TAIL_CMP_LEMMA_STMT,
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

let VAL_WORD_AND_31_STMT =
  `!n. val(word_and (word n:int64) (word 31)) = (n MOD 2 EXP 64) MOD 32`;;

let VAL_WORD_AND_31 = prove
 (VAL_WORD_AND_31_STMT,
  GEN_TAC THEN
  SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 EXP 5 - 1`)) THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let TST24_BLAST = BITBLAST_RULE
 `!y:int64. word_and y (word 24) = word 0 <=>
            word_ult (word_and y (word 31)) (word 8)`;;

let TST24_LEMMA_STMT =
  `!n. n < 2 EXP 32
       ==> (val(word_and (word n:int64) (word 24)) = 0 <=> n MOD 32 < 8)`;;

let TST24_LEMMA = prove
 (TST24_LEMMA_STMT,
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


let WORD_SUB_MOD32_STMT =
  `!len. word_sub (word len) (word (32 * len DIV 32)):int64 = word (len MOD 32)`;;

let WORD_SUB_MOD32 = prove
 (WORD_SUB_MOD32_STMT,
  GEN_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let WORD_ADD_PTR_STMT =
  `!a:int64 m n. word_add (word_add a (word m)) (word n) = word_add a (word (n + m))`;;

let WORD_ADD_PTR = prove
 (WORD_ADD_PTR_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let WORD_AND_FFFFFFF8_64_STMT =
  `!n. n < 2 EXP 32
       ==> word_and (word n:int64) (word 4294967288) = word(8 * n DIV 8)`;;

let WORD_AND_FFFFFFF8_64 = prove
 (WORD_AND_FFFFFFF8_64_STMT,
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

let LOOP3_SUB_STMT =
  `!n0 k i. word_add (word_sub (word (n0 + 8 * i)) (word (n0 + 8 * k)))
                     (word 8):int64 =
            word_sub (word (n0 + 8 * (i + 1))) (word (n0 + 8 * k))`;;

let LOOP3_SUB = prove
 (LOOP3_SUB_STMT,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `n0 + 8 * (i + 1) = (n0 + 8 * i) + 8` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let LOOP3_ZERO_STMT =
  `!n0 k i. i < k /\ n0 + 8 * k < 2 EXP 64
            ==> (val(word_sub (word (n0 + 8 * (i + 1)))
                              (word (n0 + 8 * k)):int64) = 0
                 <=> i + 1 = k)`;;

let LOOP3_ZERO = prove
 (LOOP3_ZERO_STMT,
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

let DIV8_AUX_STMT =
  `!q r. 8 * ((32 * q + r) DIV 8) = 32 * q + 8 * (r DIV 8)`;;

let DIV8_AUX = prove
 (DIV8_AUX_STMT,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `32 * q + r = (4 * q) * 8 + r` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC);;
let DIV8_SPLIT_STMT =
  `!len. 8 * (len DIV 8) = 32 * (len DIV 32) + 8 * ((len MOD 32) DIV 8)`;;

let DIV8_SPLIT = prove
 (DIV8_SPLIT_STMT,
  GEN_TAC THEN
  SUBGOAL_THEN `32 * (len DIV 32) + len MOD 32 = len`
    (fun th -> MP_TAC(SPECL [`len DIV 32`; `len MOD 32`] DIV8_AUX) THEN
               REWRITE_TAC[th]) THEN
  ARITH_TAC);;


let ZX64_128 = BITBLAST_RULE `!w:int64. word_zx(word_zx w:int128):int64 = w`;;

let LOOP3_ASSOC_STMT =
  `!n i. n + 8 * (i + 1) = (n + 8 * i) + 8`;;

let LOOP3_ASSOC = prove
 (LOOP3_ASSOC_STMT,
  REPEAT GEN_TAC THEN ARITH_TAC);;

let TAIL3_CMP_LEMMA_STMT =
  `!len. len < 2 EXP 32
         ==> (val(word_sub (word (8 * len DIV 8)) (word len):int64) = 0 <=>
              len MOD 8 = 0)`;;

let TAIL3_CMP_LEMMA = prove
 (TAIL3_CMP_LEMMA_STMT,
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

let WORD_SUB_MOD8_STMT =
  `!len. word_sub (word len) (word (8 * len DIV 8)):int64 = word (len MOD 8)`;;

let WORD_SUB_MOD8 = prove
 (WORD_SUB_MOD8_STMT,
  GEN_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN ARITH_TAC);;


(* ========================================================================= *)
(* Part 2: loops that XOR bytes of data into the state, from the head of the *)
(* loop to its exit, as lemmas for a caller to use as it uses the theorem    *)
(* for a subroutine. The state is a 200-byte array at a, S as a 1600-bit     *)
(* word, and the loop continues the XORing of the data m (len bytes at d)    *)
(* into it starting at byte off, from the byte j0 of the data on, so that    *)
(* the invariant is that of the standalone proof: the bytes of the state     *)
(* before byte off + j are those of the final state (the XOR of S and        *)
(* 2^(8 off) * m), and the bytes from there on are those of S.               *)
(*                                                                           *)
(*  INLINE_XOR_BYTES_PTR_LOOP: pointers in both arrays, post-incremented,    *)
(*  and a down-counter that the loop decrements with SUBS:                   *)
(*     ldrb T1, [D], #1; ldrb T2, [P]; subs C, C, #1; eor T1, T2, T1;        *)
(*     strb T1, [P], #1; b.ne                                                *)
(* ========================================================================= *)

let XOR_PTR_EQ_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;;

(*** The invariant of the loop over single bytes with pointers: after i of  ***)
(*** the len - j0 iterations, j = j0 + i bytes are done                      ***)

let XOR_PTR_LOOP_INV dreg preg creg =
  parse_term(Printf.sprintf
   "\\i s. read %s s = word_add d (word(j0 + i)) /\\
          read %s s = word_add a (word(off + (j0 + i))) /\\
          read %s s = word((len - j0) - i) /\\
          read (memory :> bytes(d,len)) s = m /\\
          read (memory :> bytes(a,off + (j0 + i))) s =
          val(word_xor (S:1600 word) (word(2 EXP (8 * off) * m))) MOD
          2 EXP (8 * (off + (j0 + i))) /\\
          read (memory :> bytes(word_add a (word(off + (j0 + i))),
                                200 - (off + (j0 + i)))) s =
          val S DIV 2 EXP (8 * (off + (j0 + i)))" dreg preg creg);;

let INLINE_XOR_BYTES_PTR_LOOP_TERM mc loop exit dreg preg creg t1 t2 =
  parse_term(Printf.sprintf
   "exists f_events.
      forall e a d off len j0 (S:1600 word) m pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        j0 < len /\\ off + len <= 200 /\\
        nonoverlapping (a,200) (word pc,libmldsa_size) /\\
        nonoverlapping (a,200) (d,len)
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = word_add d (word j0) /\\
                  read %s s = word_add a (word(off + j0)) /\\
                  read %s s = word(len - j0) /\\
                  read (memory :> bytes(d,len)) s = m /\\
                  read (memory :> bytes(a,off + j0)) s =
                  val(word_xor S (word(2 EXP (8 * off) * m))) MOD
                  2 EXP (8 * (off + j0)) /\\
                  read (memory :> bytes(word_add a (word(off + j0)),
                                        200 - (off + j0))) s =
                  val S DIV 2 EXP (8 * (off + j0)) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  read %s s = word_add d (word len) /\\
                  read %s s = word_add a (word(off + len)) /\\
                  read %s s = word 0 /\\
                  read (memory :> bytes(a,off + len)) s =
                  val(word_xor S (word(2 EXP (8 * off) * m))) MOD
                  2 EXP (8 * (off + len)) /\\
                  read (memory :> bytes(word_add a (word(off + len)),
                                        200 - (off + len))) s =
                  val S DIV 2 EXP (8 * (off + len)) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a d off len j0 pc /\\
                     memaccess_inbounds e2 [a,200; d,len] [a,200]))
             (MAYCHANGE [PC; %s; %s; %s; %s; %s] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,200)])"
   mc loop dreg preg creg exit dreg preg creg dreg preg creg t1 t2);;

let INLINE_XOR_BYTES_PTR_LOOP_TAC exec loop exit dreg preg creg =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (d:int64) (off:num) (len:num) (j0:num) (pc:num).
      APPEND (f_ev_epil a d off len j0 pc)
       (APPEND (ENUMERATEL (len - j0) (\i. f_ev_loop a d off len j0 pc i))
               (f_ev_prol a d off len j0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d:int64`; `off:num`; `len:num`; `j0:num`; `S:1600 word`;
    `m:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst exec] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `len < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `off + len <= 200` THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `len - j0` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) (XOR_PTR_LOOP_INV dreg preg creg) THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** The head of the loop: the precondition is the invariant for i = 0 ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The body: one byte, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    XOR_LOAD_FACTS_TAC "s0" `off + (j0 + i)` `len:num` [`j0 + i`] [] [] THEN
    XOR_REST_TAC "s0" `off + (j0 + i)` `off + (j0 + (i + 1))` THEN
    ARM_STEPS_TAC exec (1--6) THEN
    BYTE_CNT_TAC `len - j0` THEN
    XOR_STORE_TAC `j0 + i` 1 THEN
    XOR_EXTEND_TAC `j0 + i` 1 `j0 + (i + 1)` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(i + 1 = len - j0) <=> i + 1 < len - j0`
      (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `i < len - j0` THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [XOR_PTR_EQ_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [XOR_PTR_EQ_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The exit: the invariant for i = len - j0 is the postcondition ***)

    REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `j0 + (len - j0) = len` MP_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[SUB_REFL] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let INLINE_XOR_BYTES_PTR_LOOP mc exec loop exit dreg preg creg t1 t2 =
  prove(INLINE_XOR_BYTES_PTR_LOOP_TERM mc loop exit dreg preg creg t1 t2,
        INLINE_XOR_BYTES_PTR_LOOP_TAC exec loop exit dreg preg creg);;

(*** The loads of 1, 8 and 16 bytes of the state and the data, given the ***)
(*** state from byte p on (as in the standalone proof)                  ***)

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
(* The loops over blocks of 8 and of 32 bytes, k iterations after j0 bytes:  *)
(*                                                                           *)
(*  INLINE_XOR_BYTES_D_LOOP: pointers D, P, post-incremented by 8, and the   *)
(*  counter C that counts up to 0:                                           *)
(*     ldr d0, [D], #8; ldr d1, [P]; adds C, C, #8;                          *)
(*     eor v0.8b, v1.8b, v0.8b; str d0, [P], #8; b.ne                        *)
(*  with C = j0 + 8 * i - (j0 + 8 * k) (word_sub of the two numbers)         *)
(*                                                                           *)
(*  INLINE_XOR_BYTES_Q_LOOP: pointers D, P to 16 bytes before the block:     *)
(*     ldp q0, q3, [P, #-16]; subs C, C, #0x20; ldp q1, q2, [D, #-16];       *)
(*     add D, D, #0x20; eor v0.16b, v0.16b, v1.16b;                          *)
(*     eor v1.16b, v3.16b, v2.16b; stp q0, q1, [P, #-16];                    *)
(*     add P, P, #0x20; b.ne                                                 *)
(*  with C = 32 * (k - i)                                                    *)
(* The registers of the two vectors (D) or four (Q) that the loops change    *)
(* are in the list qs (e.g. ["Q0";"Q1"]).                                    *)
(* ------------------------------------------------------------------------- *)

let XOR_BLOCK_MEM j =
  Printf.sprintf
   "read (memory :> bytes(d,len)) s = m /\\
    read (memory :> bytes(a,off + (%s))) s =
    val(word_xor (S:1600 word) (word(2 EXP (8 * off) * m))) MOD
    2 EXP (8 * (off + (%s))) /\\
    read (memory :> bytes(word_add a (word(off + (%s))),
                          200 - (off + (%s)))) s =
    val S DIV 2 EXP (8 * (off + (%s)))" j j j j j;;

let XOR_BLOCK_LOOP_TERM mc loop exit dreg preg creg qs ~bytes ~dbias ~pbias
                        ~cnt_pre ~cnt_post =
  let ptr r base bias =
    if bias = 0 then Printf.sprintf "read %s s = word_add %s" r base
    else Printf.sprintf "read %s s = word_add (word_add %s) (word %d)"
                        r base bias in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e a d off len j0 k (S:1600 word) m pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        0 < k /\\ j0 + %d * k <= len /\\ off + len <= 200 /\\
        nonoverlapping (a,200) (word pc,libmldsa_size) /\\
        nonoverlapping (a,200) (d,len)
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  %s /\\ %s /\\ read %s s = %s /\\
                  %s /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  %s /\\ %s /\\ read %s s = word 0 /\\
                  %s /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a d off len j0 k pc /\\
                     memaccess_inbounds e2 [a,200; d,len] [a,200]))
             (MAYCHANGE [PC; %s; %s; %s] ,, MAYCHANGE [%s] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,200)])"
   bytes mc loop
   (ptr dreg "d (word j0)" dbias)
   (ptr preg "a (word(off + j0))" pbias)
   creg (cnt_pre "j0")
   (XOR_BLOCK_MEM "j0")
   exit
   (ptr dreg (Printf.sprintf "d (word(j0 + %d * k))" bytes) dbias)
   (ptr preg (Printf.sprintf "a (word(off + (j0 + %d * k)))" bytes) pbias)
   creg
   (XOR_BLOCK_MEM (Printf.sprintf "j0 + %d * k" bytes))
   dreg preg creg (String.concat "; " qs));;

let XOR_BLOCK_LOOP_INV dreg preg creg ~bytes ~dbias ~pbias ~cnt =
  let ptr r base bias =
    if bias = 0 then Printf.sprintf "read %s s = word_add %s" r base
    else Printf.sprintf "read %s s = word_add (word_add %s) (word %d)"
                        r base bias in
  parse_term(Printf.sprintf
   "\\i s. %s /\\ %s /\\ read %s s = %s /\\ %s"
   (ptr dreg (Printf.sprintf "d (word(j0 + %d * i))" bytes) dbias)
   (ptr preg (Printf.sprintf "a (word(off + (j0 + %d * i)))" bytes) pbias)
   creg (cnt "i")
   (XOR_BLOCK_MEM (Printf.sprintf "j0 + %d * i" bytes)));;

(*** The loop over blocks of 8 bytes ***)

let INLINE_XOR_BYTES_D_LOOP_TERM mc loop exit dreg preg creg qs =
  XOR_BLOCK_LOOP_TERM mc loop exit dreg preg creg qs ~bytes:8 ~dbias:0
   ~pbias:0 ~cnt_pre:(fun _ -> "word_sub (word j0) (word (j0 + 8 * k))")
   ~cnt_post:(fun _ -> "word 0");;

let XOR_D_LOOP_INV dreg preg creg =
  XOR_BLOCK_LOOP_INV dreg preg creg ~bytes:8 ~dbias:0 ~pbias:0
   ~cnt:(fun i -> "word_sub (word (j0 + 8 * " ^ i ^ ")) (word (j0 + 8 * k))");;

let INLINE_XOR_BYTES_D_LOOP_TAC exec loop exit dreg preg creg =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (d:int64) (off:num) (len:num) (j0:num) (k:num) (pc:num).
      APPEND (f_ev_epil a d off len j0 k pc)
       (APPEND (ENUMERATEL k (\i. f_ev_loop a d off len j0 k pc i))
               (f_ev_prol a d off len j0 k pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d:int64`; `off:num`; `len:num`; `j0:num`; `k:num`;
    `S:1600 word`; `m:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst exec] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `len < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `off + len <= 200` THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k:num` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) (XOR_D_LOOP_INV dreg preg creg) THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** The head of the loop: the precondition is the invariant for i = 0 ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The body: 8 bytes, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `j0 + 8 * i + 8 <= len` ASSUME_TAC THENL
     [UNDISCH_TAC `j0 + 8 * k <= len` THEN UNDISCH_TAC `i < k` THEN
      SPEC_TAC(`k:num`,`k:num`) THEN SPEC_TAC(`j0:num`,`j0:num`) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    XOR_LD "s0" 8 `off + (j0 + 8 * i)` `off + (j0 + 8 * i)` `j0 + 8 * i` THEN
    XOR_REST_TAC "s0" `off + (j0 + 8 * i)` `off + (j0 + 8 * (i + 1))` THEN
    ARM_STEPS_TAC exec (1--6) THEN
    LOOP3_CNT_TAC `j0:num` `k:num` THEN
    XOR_STORE_TAC `j0 + 8 * i` 8 THEN
    XOR_EXTEND_TAC `j0 + 8 * i` 8 `j0 + 8 * (i + 1)` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(i + 1 = k) <=> i + 1 < k`
      (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `i < k` THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[WORD_ADD_PTR] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[WORD_ADD_PTR] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      ARITH_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The exit: the invariant for i = k is the postcondition ***)

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_SUB_REFL] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let INLINE_XOR_BYTES_D_LOOP mc exec loop exit dreg preg creg qs =
  prove(INLINE_XOR_BYTES_D_LOOP_TERM mc loop exit dreg preg creg qs,
        INLINE_XOR_BYTES_D_LOOP_TAC exec loop exit dreg preg creg);;

(*** The loop over blocks of 32 bytes ***)

let INLINE_XOR_BYTES_Q_LOOP_TERM mc loop exit dreg preg creg qs =
  XOR_BLOCK_LOOP_TERM mc loop exit dreg preg creg qs ~bytes:32 ~dbias:16
   ~pbias:16 ~cnt_pre:(fun _ -> "word (32 * k)")
   ~cnt_post:(fun _ -> "word 0");;

let XOR_Q_LOOP_INV dreg preg creg =
  XOR_BLOCK_LOOP_INV dreg preg creg ~bytes:32 ~dbias:16 ~pbias:16
   ~cnt:(fun i -> "word (32 * (k - " ^ i ^ "))");;

let XOR_Q_CNT_TAC =
  MP_TAC(SPECL [`k:num`; `i:num`] LOOP2_CNT_LEMMA) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `j0 + 32 * k <= len` THEN UNDISCH_TAC `len < 2 EXP 32` THEN
      ARITH_TAC];
    DISCH_THEN(CONJUNCTS_THEN2
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]))];;

let INLINE_XOR_BYTES_Q_LOOP_TAC exec loop exit dreg preg creg =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (d:int64) (off:num) (len:num) (j0:num) (k:num) (pc:num).
      APPEND (f_ev_epil a d off len j0 k pc)
       (APPEND (ENUMERATEL k (\i. f_ev_loop a d off len j0 k pc i))
               (f_ev_prol a d off len j0 k pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d:int64`; `off:num`; `len:num`; `j0:num`; `k:num`;
    `S:1600 word`; `m:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst exec] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `len < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `off + len <= 200` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `j0 + 32 * k <= len` THEN UNDISCH_TAC `len < 2 EXP 32` THEN
    ARITH_TAC; ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k:num` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) (XOR_Q_LOOP_INV dreg preg creg) THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** The head of the loop: the precondition is the invariant for i = 0 ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The body: 32 bytes, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `j0 + 32 * i + 32 <= len` ASSUME_TAC THENL
     [UNDISCH_TAC `j0 + 32 * k <= len` THEN UNDISCH_TAC `i < k` THEN
      SPEC_TAC(`k:num`,`k:num`) THEN SPEC_TAC(`j0:num`,`j0:num`) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    XOR_LD "s0" 16 `off + (j0 + 32 * i)` `off + (j0 + 32 * i)`
      `j0 + 32 * i` THEN
    XOR_LD "s0" 16 `off + (j0 + 32 * i)` `(off + (j0 + 32 * i)) + 16`
      `(j0 + 32 * i) + 16` THEN
    XOR_REST_TAC "s0" `off + (j0 + 32 * i)` `off + (j0 + 32 * (i + 1))` THEN
    ARM_STEPS_TAC exec (1--9) THEN
    XOR_Q_CNT_TAC THEN
    XOR_STORE_TAC `j0 + 32 * i` 16 THEN
    XOR_STORE_TAC `(j0 + 32 * i) + 16` 16 THEN
    XOR_EXTEND_TAC `j0 + 32 * i` 16 `(j0 + 32 * i) + 16` THEN
    XOR_EXTEND_TAC `(j0 + 32 * i) + 16` 16 `j0 + 32 * (i + 1)` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(i + 1 = k) <=> i + 1 < k`
      (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `i < k` THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`; WORD_ADD] THEN
      CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `off + (j0 + 32 * (i + 1)) =
                              (off + (j0 + 32 * i)) + 32`; WORD_ADD] THEN
      CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The exit: the invariant for i = k is the postcondition ***)

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[SUB_REFL; MULT_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let INLINE_XOR_BYTES_Q_LOOP mc exec loop exit dreg preg creg qs =
  prove(INLINE_XOR_BYTES_Q_LOOP_TERM mc loop exit dreg preg creg qs,
        INLINE_XOR_BYTES_Q_LOOP_TAC exec loop exit dreg preg creg);;

(* ------------------------------------------------------------------------- *)
(*  INLINE_XOR_BYTES_IDX_LOOP: the data pointer D and the state pointer P    *)
(*  (to byte off of the state) stay fixed, the index I counts up from j0 to  *)
(*  len, held in L:                                                          *)
(*     ldrb T1, [D, I]; ldrb T2, [P, I]; eor T1, T2, T1;                     *)
(*     strb T1, [P, I]; add I, I, #1; cmp L, I; b.ne                         *)
(* ------------------------------------------------------------------------- *)

let XOR_IDX_CNT_LEMMA = prove
 (`!j len. j < len /\ len < 2 EXP 64
           ==> (val(word_sub (word len) (word_add (word j) (word 1)):int64) =
                0 <=> j + 1 = len)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `j + 1 < 2 EXP 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

let XOR_IDX_LOOP_INV dreg preg ireg lreg =
  parse_term(Printf.sprintf
   "\\i s. read %s s = d /\\ read %s s = word_add a (word off) /\\
          read %s s = word(j0 + i) /\\ read %s s = word len /\\
          read (memory :> bytes(d,len)) s = m /\\
          read (memory :> bytes(a,off + (j0 + i))) s =
          val(word_xor (S:1600 word) (word(2 EXP (8 * off) * m))) MOD
          2 EXP (8 * (off + (j0 + i))) /\\
          read (memory :> bytes(word_add a (word(off + (j0 + i))),
                                200 - (off + (j0 + i)))) s =
          val S DIV 2 EXP (8 * (off + (j0 + i)))" dreg preg ireg lreg);;

let INLINE_XOR_BYTES_IDX_LOOP_TERM mc loop exit dreg preg ireg lreg t1 t2 =
  parse_term(Printf.sprintf
   "exists f_events.
      forall e a d off len j0 (S:1600 word) m pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        j0 < len /\\ off + len <= 200 /\\
        nonoverlapping (a,200) (word pc,libmldsa_size) /\\
        nonoverlapping (a,200) (d,len)
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = d /\\ read %s s = word_add a (word off) /\\
                  read %s s = word j0 /\\ read %s s = word len /\\
                  read (memory :> bytes(d,len)) s = m /\\
                  read (memory :> bytes(a,off + j0)) s =
                  val(word_xor S (word(2 EXP (8 * off) * m))) MOD
                  2 EXP (8 * (off + j0)) /\\
                  read (memory :> bytes(word_add a (word(off + j0)),
                                        200 - (off + j0))) s =
                  val S DIV 2 EXP (8 * (off + j0)) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  read %s s = d /\\ read %s s = word_add a (word off) /\\
                  read %s s = word len /\\ read %s s = word len /\\
                  read (memory :> bytes(d,len)) s = m /\\
                  read (memory :> bytes(a,off + len)) s =
                  val(word_xor S (word(2 EXP (8 * off) * m))) MOD
                  2 EXP (8 * (off + len)) /\\
                  read (memory :> bytes(word_add a (word(off + len)),
                                        200 - (off + len))) s =
                  val S DIV 2 EXP (8 * (off + len)) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a d off len j0 pc /\\
                     memaccess_inbounds e2 [a,200; d,len] [a,200]))
             (MAYCHANGE [PC; %s; %s; %s] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,200)])"
   mc loop dreg preg ireg lreg exit dreg preg ireg lreg ireg t1 t2);;

let INLINE_XOR_BYTES_IDX_LOOP_TAC exec loop exit dreg preg ireg lreg =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (d:int64) (off:num) (len:num) (j0:num) (pc:num).
      APPEND (f_ev_epil a d off len j0 pc)
       (APPEND (ENUMERATEL (len - j0) (\i. f_ev_loop a d off len j0 pc i))
               (f_ev_prol a d off len j0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d:int64`; `off:num`; `len:num`; `j0:num`; `S:1600 word`;
    `m:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst exec] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `len < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `off + len <= 200` THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `len - j0` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) (XOR_IDX_LOOP_INV dreg preg ireg lreg) THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The body: one byte, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    XOR_LOAD_FACTS_TAC "s0" `off + (j0 + i)` `len:num` [`j0 + i`] [] [] THEN
    XOR_REST_TAC "s0" `off + (j0 + i)` `off + (j0 + (i + 1))` THEN
    ARM_STEPS_TAC exec (1--7) THEN
    MP_TAC(SPECL [`j0 + i`; `len:num`] XOR_IDX_CNT_LEMMA) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `i < len - j0` THEN UNDISCH_TAC `len < 2 EXP 32` THEN
      ARITH_TAC;
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
    XOR_STORE_TAC `j0 + i` 1 THEN
    XOR_EXTEND_TAC `j0 + i` 1 `j0 + (i + 1)` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((j0 + i) + 1 = len) <=> i + 1 < len - j0`
      (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `i < len - j0` THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `j0 + (len - j0) = len` MP_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let INLINE_XOR_BYTES_IDX_LOOP mc exec loop exit dreg preg ireg lreg t1 t2 =
  prove(INLINE_XOR_BYTES_IDX_LOOP_TERM mc loop exit dreg preg ireg lreg t1 t2,
        INLINE_XOR_BYTES_IDX_LOOP_TAC exec loop exit dreg preg ireg lreg);;
