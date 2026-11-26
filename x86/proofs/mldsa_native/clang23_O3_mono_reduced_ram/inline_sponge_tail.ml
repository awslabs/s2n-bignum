(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the loops that XOR the last r = mlen MOD 136 bytes of the      *)
(* message into the state in the SHAKE256 that clang 23 inlines into         *)
(* mldsa{44,65,87}_signature_pre_hash_shake256 and _verify_... (the loops    *)
(* loop2, loop4 and loop5 there, which handle one byte, 32 bytes and 4       *)
(* bytes per iteration). As in the proof of keccakf1600_xor_bytes of the     *)
(* gcc12_O2_reduced_ram build, the invariant of each loop gives the bytes    *)
(* of the state one by one, and the facts for the bytes that an iteration    *)
(* does not write are restricted so that the simulator keeps them over the   *)
(* stores. This file has the arithmetic of one iteration for a chunk of w    *)
(* bytes, and the conversions between the state in memory as one word, in    *)
(* chunks and in bytes.                                                      *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sponge_b.ml";;

(* ------------------------------------------------------------------------- *)
(* The state after the first i bytes of the data m have been XORed into it:  *)
(* only byte i changes in the next step (XOR_BYTES_STEP of the proof of      *)
(* keccakf1600_xor_bytes in gcc12_O2_reduced_ram, for offset 0).             *)
(* ------------------------------------------------------------------------- *)

let SPONGE_BYTE_UPDATE = prove
 (`!x c k j.
        x < 2 EXP (8 * k) /\ c < 256
        ==> ((x + 2 EXP (8 * k) * c) DIV 2 EXP (8 * j)) MOD 256 =
            if j = k then c else (x DIV 2 EXP (8 * j)) MOD 256`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN
    SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES; MOD_LT];
    FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
     `~(j = k) ==> j < k \/ k < j`))] THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o REWRITE_RULE[LT_EXISTS]) THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; LEFT_ADD_DISTRIB; EXP_ADD] THEN
    REWRITE_TAC[GSYM MULT_ASSOC] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `256 * y + z = y * 256 + z`] THEN
    REWRITE_TAC[MOD_MULT_ADD];
    SUBGOAL_THEN `x + 2 EXP (8 * k) * c < 2 EXP (8 * j) /\ x < 2 EXP (8 * j)`
     (fun th -> SIMP_TAC[th; DIV_LT; MOD_0]) THEN
    SUBGOAL_THEN `2 EXP (8 * k) * 256 <= 2 EXP (8 * j)` MP_TAC THENL
     [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM EXP_ADD; LE_EXP] THEN
      ASM_ARITH_TAC;
      UNDISCH_TAC `c < 256` THEN UNDISCH_TAC `x < 2 EXP (8 * k)` THEN
      SPEC_TAC(`2 EXP (8 * j)`,`q:num`) THEN
      SPEC_TAC(`2 EXP (8 * k)`,`p:num`) THEN
      REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `x + p * c < p * 256` MP_TAC THENL
       [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `p + p * c` THEN
        ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
        REWRITE_TAC[ARITH_RULE `p + p * c = p * (c + 1)`; LE_MULT_LCANCEL] THEN
        ASM_ARITH_TAC;
        MP_TAC(SPECL [`p:num`; `c:num`] LE_MULT_LCANCEL) THEN
        ASM_ARITH_TAC]]]);;

let SPONGE_XOR_BYTE_STEP = prove
 (`!(S:1600 word) m i j.
        i < 200 /\ j < 200
        ==> word_subword (word_xor S (word(m MOD 2 EXP (8 * (i + 1)))))
                         (8 * j,8):byte =
            if j = i
            then word_xor
                  (word_subword (word_xor S (word(m MOD 2 EXP (8 * i))))
                                (8 * j,8))
                  (word((m DIV 2 EXP (8 * i)) MOD 256))
            else word_subword (word_xor S (word(m MOD 2 EXP (8 * i))))
                              (8 * j,8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
   `m MOD 2 EXP (8 * (i + 1)) =
    m MOD 2 EXP (8 * i) + 2 EXP (8 * i) * (m DIV 2 EXP (8 * i)) MOD 256`
  SUBST1_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MULT_CLAUSES;
                ARITH_RULE `2 EXP 8 = 256`; MOD_MULT_MOD] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_SUBWORD_WORD; DIMINDEX_CONV `dimindex(:1600)`;
               DIMINDEX_8; ARITH_RULE `j < 200 ==> 8 * j + 8 <= 1600`] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`] THEN
  MP_TAC(SPECL [`m MOD 2 EXP (8 * i)`; `(m DIV 2 EXP (8 * i)) MOD 256`;
                `i:num`; `j:num`] SPONGE_BYTE_UPDATE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
    DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(m MOD 2 EXP (8 * i)) DIV 2 EXP (8 * i) = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_LT THEN REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[MOD_0; WORD_XOR_0; WORD_XOR_ASSOC; ARITH_RULE `0 MOD 256 = 0`]);;

(*** The same for a chunk of w bytes at offset p ***)

let SPONGE_XOR_CHUNK_STEP = prove
 (`!(S:1600 word) m p w j.
        p + w <= 200 /\ j < 200
        ==> word_subword (word_xor S (word(m MOD 2 EXP (8 * (p + w)))))
                         (8 * j,8):byte =
            if p <= j /\ j < p + w
            then word_xor
                  (word_subword (word_xor S (word(m MOD 2 EXP (8 * p))))
                                (8 * j,8))
                  (word((m DIV 2 EXP (8 * j)) MOD 256))
            else word_subword (word_xor S (word(m MOD 2 EXP (8 * p))))
                              (8 * j,8)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `p + SUC w = (p + w) + 1`] THEN
  MP_TAC(SPECL [`S:1600 word`; `m:num`; `p + w`; `j:num`]
         SPONGE_XOR_BYTE_STEP) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ARITH_RULE
   `(p <= j /\ j < (p + w) + 1) <=> (p <= j /\ j < p + w) \/ j = p + w`] THEN
  ASM_CASES_TAC `j = p + w` THENL
   [ASM_REWRITE_TAC[ARITH_RULE `~(p + w < p + w)`; LE_REFL;
                    ARITH_RULE `p <= p + w`;
                    ARITH_RULE `~(p <= p + w /\ p + w < p + w)`];
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The state in memory as one word and as its bytes, and a chunk as bytes.   *)
(* ------------------------------------------------------------------------- *)

let SPONGE_BYTES8_OF_WBYTES = prove
 (`!(a:int64) (X:1600 word) k (s:x86state).
        read (memory :> wbytes a) s = X /\ k < 200
        ==> read (memory :> bytes8 (word_add a (word k))) s =
            word_subword X (8 * k,8)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `200`; `val(X:1600 word)`; `k:num`; `s:x86state`]
         READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[word_subword] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

(*** All the bytes of the state, from the state as one word and back ***)

let SPONGE_ALL_BYTES_OF_WBYTES = prove
 (`!(a:int64) (X:1600 word) (s:x86state).
        read (memory :> wbytes a) s = X
        ==> !j. j < 200
                ==> read (memory :> bytes8 (word_add a (word j))) s =
                    word_subword X (8 * j,8)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SPONGE_BYTES8_OF_WBYTES THEN
  ASM_REWRITE_TAC[]);;

let SPONGE_WBYTES_OF_ALL_BYTES = prove
 (`!(a:int64) (X:1600 word) (s:x86state).
        (!j. j < 200
             ==> read (memory :> bytes8 (word_add a (word j))) s =
                 word_subword X (8 * j,8))
        ==> read (memory :> wbytes a) s = X`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN
  SUBGOAL_THEN `val(X:1600 word) = val(X:1600 word) MOD 2 EXP (8 * 200)`
    SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `X:1600 word` VAL_BOUND) THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC READ_MEMORY_BYTES_OF_BYTES8 THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[word_subword] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

(*** The bytes of a chunk of N bits in memory ***)

let SPONGE_BYTES8_OF_CHUNK32 = prove
 (`!(a:int64) (v:int32) k (s:x86state).
        read (memory :> bytes32 a) s = v /\ k < 4
        ==> read (memory :> bytes8 (word_add a (word k))) s =
            word_subword v (8 * k,8)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `4`; `val(v:int32)`; `k:num`; `s:x86state`]
         READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[word_subword] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL]);;

let SPONGE_BYTES8_OF_CHUNK128 = prove
 (`!(a:int64) (v:int128) k (s:x86state).
        read (memory :> bytes128 a) s = v /\ k < 16
        ==> read (memory :> bytes8 (word_add a (word k))) s =
            word_subword v (8 * k,8)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `16`; `val(v:int128)`; `k:num`; `s:x86state`]
         READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[word_subword] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL]);;

(* The state at rsp0 + 32: the offsets of the bytes are j + 32 from rsp0,    *)
(* as the simulation writes them, so that the facts about the bytes and the  *)
(* stores have the same base.                                                *)

let SPONGE_BYTES32_ADDR = prove
 (`!(a:int64) j. word_add (word_add a (word 32)) (word j) =
                 word_add a (word (j + 32))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_RULE);;

let SPONGE_ALL_BYTES_OF_WBYTES32 = prove
 (`!(a:int64) (X:1600 word) (s:x86state).
        read (memory :> wbytes (word_add a (word 32))) s = X
        ==> !j. j < 200
                ==> read (memory :> bytes8 (word_add a (word (j + 32)))) s =
                    word_subword X (8 * j,8)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SPONGE_BYTES32_ADDR] THEN
  MATCH_MP_TAC SPONGE_BYTES8_OF_WBYTES THEN ASM_REWRITE_TAC[]);;

let SPONGE_WBYTES32_OF_ALL_BYTES = prove
 (`!(a:int64) (X:1600 word) (s:x86state).
        (!j. j < 200
             ==> read (memory :> bytes8 (word_add a (word (j + 32)))) s =
                 word_subword X (8 * j,8))
        ==> read (memory :> wbytes (word_add a (word 32))) s = X`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SPONGE_WBYTES_OF_ALL_BYTES THEN
  REWRITE_TAC[SPONGE_BYTES32_ADDR] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A byte of a chunk of N bits of the state, the chunk XORed with the chunk  *)
(* of the data, as a byte of the state XORed with a byte of the data.        *)
(* ------------------------------------------------------------------------- *)

let SPONGE_MODDIV_BYTE = prove
 (`!X n k. 8 * k + 8 <= n
     ==> ((X MOD 2 EXP n) DIV 2 EXP (8 * k)) MOD 2 EXP 8 =
         (X DIV 2 EXP (8 * k)) MOD 2 EXP 8`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP n = 2 EXP (8 * k) * 2 EXP (n - 8 * k)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_MOD; MOD_MOD_EXP_MIN] THEN
  SUBGOAL_THEN `MIN (n - 8 * k) 8 = 8` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[]]);;
let SPONGE_SUBSUB n = 
  let sub = subst_tokens ["@N@",string_of_int n; "@NB@",string_of_int (n/8)] in
  prove(parse_term(sub
 "!(Y:1600 word) c k. k < @NB@
     ==> word_subword (word_subword Y (@N@ * c,@N@):(@N@)word) (8 * k,8):byte =
         word_subword Y (@N@ * c + 8 * k,8)"),
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Y:1600 word`; parse_term(sub "@N@ * c"); parse_term(sub "@N@"); `8 * k`; `8`]
    (INST_TYPE [parse_type(sub "(@N@)"),`:N`; `:1600`,`:M`; `:8`,`:P`] WORD_SUBWORD_SUBWORD)) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`; DIMINDEX_32; DIMINDEX_128] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN (parse_term(sub "MIN 8 (@N@ - 8 * k) = 8")) SUBST1_TAC THENL
   [UNDISCH_TAC (parse_term(sub "k < @NB@")) THEN ARITH_TAC; REWRITE_TAC[]]);;
let SPONGE_SUBSUB32 = SPONGE_SUBSUB 32;;
let SPONGE_SUBSUB128 = SPONGE_SUBSUB 128;;

let SPONGE_CHUNK_BYTE n =
  let sub = subst_tokens ["@N@",string_of_int n; "@NB@",string_of_int (n/8)] in
  prove(parse_term(sub
 "!(Y:1600 word) Tm c k. k < @NB@
     ==> word_subword (word_xor (word_subword Y (@N@ * c,@N@):(@N@)word)
                                (word((Tm DIV 2 EXP (@N@ * c)) MOD 2 EXP @N@))) (8 * k,8):byte =
         word_xor (word_subword Y (@N@ * c + 8 * k,8))
                  (word((Tm DIV 2 EXP (@N@ * c + 8 * k)) MOD 256))"),
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  MATCH_MP_TAC(MESON[] `a = a' /\ b = b' ==> word_xor a b:byte = word_xor a' b'`) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[SPONGE_SUBSUB n];
    ASM_SIMP_TAC[WORD_SUBWORD_WORD; DIMINDEX_32; DIMINDEX_128; DIMINDEX_8;
                 ARITH_RULE(parse_term(sub "k < @NB@ ==> 8 * k + 8 <= @N@"))] THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`] THEN
    AP_TERM_TAC THEN
    MP_TAC(SPECL [parse_term(sub "Tm DIV 2 EXP (@N@ * c)"); parse_term(sub "@N@"); `k:num`] SPONGE_MODDIV_BYTE) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; DIV_DIV; GSYM EXP_ADD] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;
let SPONGE_CHUNK_BYTE32 = SPONGE_CHUNK_BYTE 32;;
let SPONGE_CHUNK_BYTE128 = SPONGE_CHUNK_BYTE 128;;
