(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the Keccak code that clang 23 -O3 inlines into the callers of   *)
(* mldsa-native's sponge functions in the monolithic reduced-RAM build. It   *)
(* reads and writes the state of 200 bytes in chunks of 8 or 16 bytes with   *)
(* SSE instructions, but the permutation and the model see it as a 1600-bit  *)
(* word. For the chunk sizes N = 64 and 128 bits (and 32), the lemmas here   *)
(* convert between the two:                                                  *)
(*                                                                           *)
(*  - READ_MEMORY_BYTES<N>_OF_NUM: the chunk k of a byte array that is given *)
(*    as a number;                                                           *)
(*  - READ_MEMORY_BYTES<N>_OF_WBYTES: the chunk k of a state given as a word;*)
(*  - READ_MEMORY_WBYTES_OF_CHUNKS: a state as a word from its 12 chunks of  *)
(*    128 bits and its last lane.                                            *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign.ml";;

(* ------------------------------------------------------------------------- *)
(* A chunk of N bits at the byte offset N / 8 * k of a byte array that is a  *)
(* number, and the chunk of the state as a word.                             *)
(* ------------------------------------------------------------------------- *)

let SPONGE_CHUNK_OF_NUM n =
  let sub = subst_tokens ["@N@",string_of_int n; "@NB@",string_of_int (n/8);
                          "@P@",(match n with 16 -> "65536" | 32 -> "4294967296" | 64 -> "18446744073709551616" | _ -> "340282366920938463463374607431768211456");
                          "@BN@",Printf.sprintf "bytes%d" n] in
  let wth = (match n with 16 -> BYTES16_WBYTES | 32 -> BYTES32_WBYTES
             | 64 -> BYTES64_WBYTES | _ -> BYTES128_WBYTES) in
  prove(parse_term(sub
   "!(a:int64) m x k (s:x86state).
        read (memory :> bytes(a,m)) s = x /\\ @NB@ * k + @NB@ <= m
        ==> read (memory :> @BN@ (word_add a (word (@NB@ * k)))) s =
            word((x DIV 2 EXP (@N@ * k)) MOD 2 EXP @N@)"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[wth; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) then SUBST1_TAC(SYM th)
                        else NO_TAC) THEN
  REWRITE_TAC[ARITH_RULE(parse_term(sub "@N@ * k = 8 * (@NB@ * k)"))] THEN
  REWRITE_TAC[ARITH_RULE(parse_term(sub "@P@ = 2 EXP (8 * @NB@)"))] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD;
              MOD_MOD_REFL] THEN
  SUBGOAL_THEN(parse_term(sub "MIN (m - @NB@ * k) @NB@ = @NB@")) SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[]);;

let READ_MEMORY_BYTES32_OF_NUM = SPONGE_CHUNK_OF_NUM 32;;
let READ_MEMORY_BYTES64_OF_NUM = SPONGE_CHUNK_OF_NUM 64;;
let READ_MEMORY_BYTES128_OF_NUM = SPONGE_CHUNK_OF_NUM 128;;

let SPONGE_CHUNK_OF_WBYTES n kmax =
  let sub = subst_tokens ["@N@",string_of_int n; "@NB@",string_of_int (n/8);
                          "@BN@",Printf.sprintf "bytes%d" n;
                          "@K@",string_of_int kmax] in
  let nth = SPONGE_CHUNK_OF_NUM n in
  prove(parse_term(sub
   "!(a:int64) (X:1600 word) k (s:x86state).
        read (memory :> wbytes a) s = X /\\ k < @K@
        ==> read (memory :> @BN@ (word_add a (word (@NB@ * k)))) s =
            word_subword X (@N@ * k,@N@)"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `200`; `val(X:1600 word)`; `k:num`; `s:x86state`] nth) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
      CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE];
      ASM_ARITH_TAC];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[word_subword] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_REFL]]);;

let READ_MEMORY_BYTES32_OF_WBYTES = SPONGE_CHUNK_OF_WBYTES 32 50;;
let READ_MEMORY_BYTES64_OF_WBYTES = SPONGE_CHUNK_OF_WBYTES 64 25;;
let READ_MEMORY_BYTES128_OF_WBYTES = SPONGE_CHUNK_OF_WBYTES 128 12;;

(* ------------------------------------------------------------------------- *)
(* The state as a word from its 25 lanes of 64 bits.                         *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES_OF_BYTES64 = prove
 (`!(a:int64) n x (s:x86state).
        (!j. j < n
             ==> read (memory :> bytes64 (word_add a (word (8 * j)))) s =
                 word((x DIV 2 EXP (64 * j)) MOD 2 EXP 64))
        ==> read (memory :> bytes(a,8 * n)) s = x MOD 2 EXP (64 * n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; MULT_CLAUSES; READ_BYTES_TRIVIAL;
                EXP; MOD_1];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ARITH_RULE `8 * SUC n = 8 * n + 8`;
              ARITH_RULE `64 * SUC n = 64 * n + 64`;
              READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `s:x86state`]) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `8 * 8 * n = 64 * n`; EXP_ADD] THEN
  GEN_REWRITE_TAC (RAND_CONV) [MOD_MULT_MOD] THEN
  ARITH_TAC);;

let READ_MEMORY_WBYTES_OF_LANES = prove
 (`!(a:int64) (X:1600 word) (s:x86state).
        (!j. j < 25
             ==> read (memory :> bytes64 (word_add a (word (8 * j)))) s =
                 word_subword X (64 * j,64))
        ==> read (memory :> wbytes a) s = X`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `25`; `val(X:1600 word)`; `s:x86state`]
         READ_MEMORY_BYTES_OF_BYTES64) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[word_subword; GSYM VAL_EQ; VAL_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_REFL];
    REWRITE_TAC[ARITH_RULE `8 * 25 = 200`; ARITH_RULE `64 * 25 = 1600`] THEN
    SUBGOAL_THEN `val(X:1600 word) MOD 2 EXP 1600 = val X` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `X:1600 word` VAL_BOUND) THEN
      REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`];
      ALL_TAC] THEN
    DISCH_TAC THEN
    REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A chunk of a number below 2^1600 as a subword of the number as a word,    *)
(* and the two lanes of a chunk of 128 bits in memory.                       *)
(* ------------------------------------------------------------------------- *)

let SPONGE_NUM_SUBWORD n =
  let sub = subst_tokens ["@N@",string_of_int n] in
  prove(parse_term(sub
   "!x p. x < 2 EXP 1600
        ==> (word((x DIV 2 EXP p) MOD 2 EXP @N@):(@N@)word) =
            word_subword (word x:1600 word) (p,@N@)"),
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_subword] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  SUBGOAL_THEN `(x MOD 2 EXP 1600) = x` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MOD_MOD_REFL]);;

let SPONGE_NUM_SUBWORD64 = SPONGE_NUM_SUBWORD 64;;
let SPONGE_NUM_SUBWORD128 = SPONGE_NUM_SUBWORD 128;;

let READ_MEMORY_BYTES64_OF_BYTES128 = prove
 (`!(a:int64) (v:int128) (s:x86state).
        read (memory :> bytes128 a) s = v
        ==> read (memory :> bytes64 a) s = word_subword v (0,64) /\
            read (memory :> bytes64 (word_add a (word 8))) s =
            word_subword v (64,64)`,
  REPEAT GEN_TAC THEN
  MP_TAC(READ_MEMORY_MERGE_CONV 1 `read (memory :> bytes128 a) (s:x86state)`) THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  CONV_TAC WORD_BLAST);;

(* The high lanes of a number below 2^1088 are zero. *)

let SPONGE_SUBWORD_HI = prove
 (`!(x:num) j.
        x < 2 EXP 1088 /\ 17 <= j
        ==> word_subword (word x:1600 word) (64 * j,64):int64 = word 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x < 2 EXP 1600` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP 1088` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP SPONGE_NUM_SUBWORD64 th)]) THEN
  SUBGOAL_THEN `x DIV 2 EXP (64 * j) = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2 EXP 1088` THEN
    ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    REWRITE_TAC[MOD_0]]);;

(* ------------------------------------------------------------------------- *)
(* The test cmp r13, 0x87; ja at the end of the loop over the blocks of 136  *)
(* bytes: r13 has been decreased by 136 from mlen - 136 i.                   *)
(* ------------------------------------------------------------------------- *)

let SPONGE_LOOP_JA = prove
 (`!mlen i n.
        mlen < 2 EXP 64 /\ mlen DIV 136 = n /\ i + 1 <= n
        ==> (~(val(word_add (word (mlen - 136 * i)) (word 18446744073709551480)
                     :int64) < 135 \/
               val(word_add (word (mlen - 136 * i)) (word 18446744073709551345)
                     :int64) = 0) <=>
             i + 1 < n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`mlen:num`; `136`] DIVISION) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `mlen - 136 * i < 18446744073709551616` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  SUBGOAL_THEN
   `(mlen - 136 * i + 18446744073709551480) MOD 18446744073709551616 =
    mlen - 136 * i - 136`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `mlen - 136 * i + 18446744073709551480 =
                  1 * 18446744073709551616 + (mlen - 136 * i - 136)`
    SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `271 <= mlen - 136 * i` THENL
   [SUBGOAL_THEN
     `(mlen - 136 * i + 18446744073709551345) MOD 18446744073709551616 =
      mlen - 136 * i - 271`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `mlen - 136 * i + 18446744073709551345 =
                    1 * 18446744073709551616 + (mlen - 136 * i - 271)`
      SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_ARITH_TAC;
    SUBGOAL_THEN
     `(mlen - 136 * i + 18446744073709551345) MOD 18446744073709551616 =
      mlen - 136 * i + 18446744073709551345`
    SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_ARITH_TAC]);;

let SPONGE_LOOP_R13 = prove
 (`!mlen i.
        mlen < 2 EXP 64 /\ 136 * (i + 1) <= mlen
        ==> word_add (word (mlen - 136 * i)) (word 18446744073709551480):int64 =
            word (mlen - 136 * (i + 1))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `mlen - 136 * i < 18446744073709551616 /\
                mlen - 136 * (i + 1) < 18446744073709551616` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN UNDISCH_TAC `mlen < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  SUBGOAL_THEN `mlen - 136 * i + 18446744073709551480 =
                1 * 18446744073709551616 + mlen - 136 * (i + 1)` SUBST1_TAC THENL
   [UNDISCH_TAC `136 * (i + 1) <= mlen` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `1 * 18446744073709551616 + a - b = 1 * 18446744073709551616 + (a - b)`] THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN ASM_SIMP_TAC[MOD_LT]);;
