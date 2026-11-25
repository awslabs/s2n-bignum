(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Memory as byte lists, and the byte shuffles of the decompressor, for the  *)
(* machine-code proofs of the snappy decompressor (ISA-independent).         *)
(*                                                                           *)
(*  - bytelist regions: split, length, element, and the bytes of a word read *)
(*    (bytes8 .. bytes128) as elements;                                      *)
(*  - the pattern masks of snappy.cc (pattern_generation_masks and           *)
(*    pattern_reshuffle_masks): snappy_pattern_mask k j is the mask whose    *)
(*    byte i is (16 * j + i) MOD (k + 1); a table lookup (TBL, PSHUFB) of a *)
(*    16-byte word q with snappy_pattern_mask (off - 1) 0, followed by j     *)
(*    lookups with snappy_pattern_mask (off - 1) 1, has byte i equal to the  *)
(*    byte (16 * j + i) MOD off of q (SNAPPY_PATTERN_ITER_BYTE);             *)
(*  - a copy built in memory chunk by chunk, as IncrementalCopy and the      *)
(*    fast path do: bytelist(base,LENGTH out + c) holds snappy_copy off c    *)
(*    out, and a chunk of k <= off bytes equal to the k bytes off before it  *)
(*    (SNAPPY_COPY_CHUNK_STEP) or 16 bytes of the pattern                    *)
(*    (SNAPPY_COPY_PATTERN_STEP) extends it; SNAPPY_COPY_TRUNC takes the     *)
(*    prefix of the first n bytes.                                           *)
(* ========================================================================= *)

(* Loaded after the base of an ISA (common/components.ml).                   *)

needs "common/snappy/snappy_decompress.ml";;

(* ------------------------------------------------------------------------- *)
(* Byte lists in memory.                                                     *)
(* ------------------------------------------------------------------------- *)

let READ_BYTELIST_SPLIT = prove
 (`!(m:(S,N word->byte)component) a j k s.
        read (m :> bytelist(a,j + k)) s =
        APPEND (read (m :> bytelist(a,j)) s)
               (read (m :> bytelist(word_add a (word j),k)) s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN GEN_TAC THEN
  SUBGOAL_THEN
   `!j (a:N word) k (t:N word->byte).
      read (bytelist(a,j + k)) t =
      APPEND (read (bytelist(a,j)) t) (read (bytelist(word_add a (word j),k)) t)`
   (fun th -> REWRITE_TAC[th]) THEN
  INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; bytelist_clauses; APPEND; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[CONS_11] THEN
  REWRITE_TAC[ADD1; WORD_RULE
   `word_add (word_add (a:N word) (word 1)) (word j) = word_add a (word(j + 1))`]);;

let LENGTH_READ_BYTELIST = prove
 (`!(m:(S,N word->byte)component) a k s.
        LENGTH(read (m :> bytelist(a,k)) s) = k`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bytelist; through; read;
              LENGTH_BYTELIST_OF_NUM]);;

let EL_READ_BYTELIST = prove
 (`!(m:(S,N word->byte)component) a k i s.
        i < k
        ==> EL i (read (m :> bytelist(a,k)) s) =
            read (m :> bytes8 (word_add a (word i))) s`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN GEN_TAC THEN
  REWRITE_TAC[BYTES8_ELEMENT; READ_ELEMENT] THEN
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC[CONJUNCT1 LT] THEN
  REWRITE_TAC[bytelist_clauses] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[EL; HD; TL; WORD_ADD_0; LT_SUC] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN REWRITE_TAC[ADD1] THEN
  CONV_TAC WORD_RULE);;

(* Two lists equal by their elements, for a list read from memory.           *)

let READ_BYTELIST_EQ_EL = prove
 (`!(m:(S,N word->byte)component) a k s l.
        read (m :> bytelist(a,k)) s = l <=>
        LENGTH l = k /\
        !i. i < k ==> read (m :> bytes8 (word_add a (word i))) s = EL i l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_READ_BYTELIST] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[EL_READ_BYTELIST]);;

(* The bytes of a word read from memory.                                     *)

let READ_BYTES8_OF_BYTES128 = prove
 (`!(m:(S,N word->byte)component) a i s.
        i < 16
        ==> read (m :> bytes8 (word_add a (word i))) s =
            word_subword (read (m :> bytes128 a) s) (8 * i,8)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[bytes8; bytes128; READ_COMPONENT_COMPOSE; asword; through;
              read] THEN
  REWRITE_TAC[word_subword] THEN AP_TERM_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_128] THEN
  SIMP_TAC[MOD_LT; REWRITE_RULE[ARITH_RULE `8 * 16 = 128`]
                    (ISPECL [`a:N word`; `16`] READ_BYTES_BOUND)] THEN
  REWRITE_TAC[READ_BYTES_DIV; ARITH_RULE `2 EXP 8 = 2 EXP (8 * 1)`;
              READ_BYTES_MOD] THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 16 ==> MIN (16 - i) 1 = 1`]);;

let READ_BYTES8_OF_BYTES64 = prove
 (`!(m:(S,N word->byte)component) a i s.
        i < 8
        ==> read (m :> bytes8 (word_add a (word i))) s =
            word_subword (read (m :> bytes64 a) s) (8 * i,8)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[bytes8; bytes64; READ_COMPONENT_COMPOSE; asword; through;
              read] THEN
  REWRITE_TAC[word_subword] THEN AP_TERM_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; REWRITE_RULE[ARITH_RULE `8 * 8 = 64`]
                    (ISPECL [`a:N word`; `8`] READ_BYTES_BOUND)] THEN
  REWRITE_TAC[READ_BYTES_DIV; ARITH_RULE `2 EXP 8 = 2 EXP (8 * 1)`;
              READ_BYTES_MOD] THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 8 ==> MIN (8 - i) 1 = 1`]);;

(* ------------------------------------------------------------------------- *)
(* The pattern masks and table lookups.                                      *)
(* ------------------------------------------------------------------------- *)

let snappy_pattern_mask = new_definition
 `snappy_pattern_mask k j : int128 =
    word(nsum (0..15) (\i. 2 EXP (8 * i) * ((16 * j + i) MOD (k + 1))))`;;

(* A table lookup of 16 bytes (TBL Vd.16B, {Vn.16B}, Vm.16B in the model of  *)
(* arm/proofs/instruction.ml) with the table q and the mask m.               *)

let snappy_tbl = new_definition
 `snappy_tbl (q:int128) (m:int128) : int128 =
    usimd16 (\x:byte. word_subword q (8 * val x,8):byte) m`;;

let SNAPPY_TBL_BYTE = prove
 (`!q m i. i < 16
           ==> word_subword (snappy_tbl q m) (8 * i,8):byte =
               word_subword q (8 * val(word_subword m (8 * i,8):byte),8)`,
  REWRITE_TAC[snappy_tbl; usimd16; usimd8; usimd4; usimd2] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  GEN_TAC THEN GEN_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let SNAPPY_PATTERN_MASK_BYTE_CASES = prove
 (`!k. k < 16 ==> !j. j < 2 ==> !i. i < 16
           ==> val(word_subword (snappy_pattern_mask k j) (8 * i,8):byte) =
               (16 * j + i) MOD (k + 1)`,
  REWRITE_TAC[snappy_pattern_mask] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)) THEN
  REWRITE_TAC[]);;

let SNAPPY_PATTERN_MASK_BYTE = prove
 (`!k j i. k < 16 /\ j <= 1 /\ i < 16
           ==> val(word_subword (snappy_pattern_mask k j) (8 * i,8):byte) =
               (16 * j + i) MOD (k + 1)`,
  MESON_TAC[SNAPPY_PATTERN_MASK_BYTE_CASES; ARITH_RULE `j <= 1 <=> j < 2`]);;

(* Byte i of the pattern after j reshuffles: the byte (16 j + i) MOD off.   *)

let snappy_pattern_iter = define
 `(snappy_pattern_iter (q:int128) off 0 =
     snappy_tbl q (snappy_pattern_mask (off - 1) 0)) /\
  (snappy_pattern_iter q off (SUC j) =
     snappy_tbl (snappy_pattern_iter q off j) (snappy_pattern_mask (off - 1) 1))`;;

let SNAPPY_PATTERN_ITER_BYTE = prove
 (`!q off j i.
        1 <= off /\ off <= 16 /\ i < 16
        ==> word_subword (snappy_pattern_iter q off j) (8 * i,8):byte =
            word_subword q (8 * ((16 * j + i) MOD off),8)`,
  let offs = [ARITH_RULE `1 <= off /\ off <= 16 ==> off - 1 < 16`;
              ARITH_RULE `1 <= off ==> off - 1 + 1 = off`;
              ARITH_RULE `0 <= 1 /\ 1 <= 1`] in
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[snappy_pattern_iter] THEN ASM_SIMP_TAC[SNAPPY_TBL_BYTE] THEN
  ASM_SIMP_TAC([SNAPPY_PATTERN_MASK_BYTE; MULT_CLAUSES; ADD_CLAUSES] @ offs) THEN
  SUBGOAL_THEN `(16 + i) MOD off < 16` ASSUME_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `off:num` THEN
    ASM_SIMP_TAC[MOD_LT_EQ; LE_1; ARITH_RULE `1 <= off ==> ~(off = 0)`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(16 * j + (16 + i)) MOD off` THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC BINOP_CONV [GSYM MOD_ADD_MOD] THEN
    REWRITE_TAC[MOD_MOD_REFL];
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A copy built in memory chunk by chunk: bytelist(base,L + c) holds         *)
(* snappy_copy off c out (L = LENGTH out), and a chunk of k bytes stored at  *)
(* base + L + c, equal to the k bytes off positions before it.               *)
(* ------------------------------------------------------------------------- *)

let READ_BYTELIST_SUB_LIST = prove
 (`!(m:(S,N word->byte)component) a j k p s.
        j + k <= p
        ==> read (m :> bytelist(word_add a (word j),k)) s =
            SUB_LIST(j,k) (read (m :> bytelist(a,p)) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[READ_BYTELIST_EQ_EL] THEN
  REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_READ_BYTELIST] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SNAPPY_EL_SUB_LIST o rand o snd) THEN
  REWRITE_TAC[LENGTH_READ_BYTELIST] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[EL_READ_BYTELIST; ARITH_RULE `i < k /\ j + k <= p ==> j + i < p`] THEN
  REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;

let READ_BYTELIST_OF_WBYTES = prove
 (`!(m:(S,N word->byte)component) a b s t.
        read (m :> wbytes a) s:M word = read (m :> wbytes b) t
        ==> read (m :> bytelist(a,dimindex(:M) DIV 8)) s =
            read (m :> bytelist(b,dimindex(:M) DIV 8)) t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:M word->num`) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[bytelist; READ_COMPONENT_COMPOSE; through; read] THEN
  SIMP_TAC[]);;

let READ_BYTELIST_OF_BYTES8 = prove
 (`!(m:(S,N word->byte)component) a b s t.
        read (m :> bytes8 a) s = read (m :> bytes8 b) t
        ==> read (m :> bytelist(a,1)) s = read (m :> bytelist(b,1)) t`,
  REWRITE_TAC[BYTES8_WBYTES] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP READ_BYTELIST_OF_WBYTES) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let READ_BYTELIST_OF_BYTES64 = prove
 (`!(m:(S,N word->byte)component) a b s t.
        read (m :> bytes64 a) s = read (m :> bytes64 b) t
        ==> read (m :> bytelist(a,8)) s = read (m :> bytelist(b,8)) t`,
  REWRITE_TAC[BYTES64_WBYTES] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP READ_BYTELIST_OF_WBYTES) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let READ_BYTELIST_OF_BYTES128 = prove
 (`!(m:(S,N word->byte)component) a b s t.
        read (m :> bytes128 a) s = read (m :> bytes128 b) t
        ==> read (m :> bytelist(a,16)) s = read (m :> bytelist(b,16)) t`,
  REWRITE_TAC[BYTES128_WBYTES] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP READ_BYTELIST_OF_WBYTES) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let READ_BYTELIST_OF_BYTES64_PAIR = prove
 (`!(m:(S,N word->byte)component) a b s t.
        read (m :> bytes64 a) s = read (m :> bytes64 b) t /\
        read (m :> bytes64 (word_add a (word 8))) s =
        read (m :> bytes64 (word_add b (word 8))) t
        ==> read (m :> bytelist(a,16)) s = read (m :> bytelist(b,16)) t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN (MP_TAC o MATCH_MP READ_BYTELIST_OF_BYTES64)) THEN
  ONCE_REWRITE_TAC[ARITH_RULE `16 = 8 + 8`] THEN
  REWRITE_TAC[READ_BYTELIST_SPLIT] THEN MESON_TAC[]);;

(* The copy so far, then a chunk of k <= off bytes: the k bytes off before. *)

let SNAPPY_COPY_CHUNK_STEP = prove
 (`!(m:(S,N word->byte)component) s t base out c k off.
        1 <= off /\ off <= LENGTH out /\ k <= off /\
        read (m :> bytelist(base,LENGTH out + c)) s = snappy_copy off c out /\
        read (m :> bytelist(base,LENGTH out + c)) t = snappy_copy off c out /\
        read (m :> bytelist(word_add base (word(LENGTH out + c)),k)) t =
        read (m :> bytelist(word_add base (word((LENGTH out + c) - off)),k)) s
        ==> read (m :> bytelist(base,LENGTH out + c + k)) t =
            snappy_copy off (c + k) out`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ADD_ASSOC] THEN
  MP_TAC(ISPECL [`m:(S,N word->byte)component`; `base:N word`;
                 `LENGTH(out:byte list) + c`; `k:num`; `t:S`]
    READ_BYTELIST_SPLIT) THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`m:(S,N word->byte)component`; `base:N word`;
                 `(LENGTH(out:byte list) + c) - off`; `k:num`;
                 `LENGTH(out:byte list) + c`; `s:S`]
    READ_BYTELIST_SUB_LIST) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC RAND_CONV [SNAPPY_COPY_ADD] THEN
  MP_TAC(ISPECL [`off:num`; `k:num`; `snappy_copy off c (out:byte list)`]
    SNAPPY_COPY_NONOVERLAP) THEN
  REWRITE_TAC[LENGTH_SNAPPY_COPY] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN REFL_TAC);;

let SNAPPY_APPEND_EQ_PREFIX = prove
 (`!(a:A list) b c d. LENGTH a = LENGTH c /\ APPEND a b = APPEND c d ==> a = c`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; APPEND] THEN MESON_TAC[LENGTH_EQ_NIL];
    GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC[LENGTH; NOT_SUC; APPEND; SUC_INJ; CONS_11] THEN
    ASM_MESON_TAC[]]);;

(* A copy of c >= n bytes has the copy of n bytes as its prefix.             *)

let SNAPPY_COPY_TRUNC = prove
 (`!(m:(S,N word->byte)component) s base out c n off.
        n <= c /\
        read (m :> bytelist(base,LENGTH out + c)) s = snappy_copy off c out
        ==> read (m :> bytelist(base,LENGTH out + n)) s = snappy_copy off n out`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`off:num`; `c - n:num`; `snappy_copy off n (out:byte list)`]
    SNAPPY_COPY_PREFIX) THEN
  REWRITE_TAC[GSYM SNAPPY_COPY_ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= c ==> n + c - n = c`] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:byte list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`m:(S,N word->byte)component`; `base:N word`;
                 `LENGTH(out:byte list) + n`; `c - n:num`; `s:S`]
    READ_BYTELIST_SPLIT) THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= c ==> (l + n) + c - n = l + c`] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  MATCH_MP_TAC SNAPPY_APPEND_EQ_PREFIX THEN
  MAP_EVERY EXISTS_TAC
   [`read ((m:(S,N word->byte)component) :>
           bytelist(word_add (base:N word) (word(LENGTH(out:byte list) + n)),
                    c - n)) (s:S)`; `d:byte list`] THEN
  ASM_REWRITE_TAC[LENGTH_READ_BYTELIST; LENGTH_SNAPPY_COPY]);;

(* The bytes of a 16-byte load q at op - off, off <= 16, that the pattern    *)
(* uses are those of the output.                                             *)

let SNAPPY_PATTERN_SOURCE = prove
 (`!(m:(S,N word->byte)component) s base out off q.
        off <= 16 /\ off <= LENGTH out /\
        read (m :> bytelist(base,LENGTH out)) s = out /\
        read (m :> bytes128 (word_add base (word(LENGTH out - off)))) s = q
        ==> !i. i < off
                ==> word_subword q (8 * i,8):byte = EL (LENGTH out - off + i) out`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(S,N word->byte)component`;
                 `word_add base (word(LENGTH(out:byte list) - off)):N word`;
                 `i:num`; `s:S`] READ_BYTES8_OF_BYTES128) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(fun th ->
    if can (find_term ((=) `bytelist:N word#num->((N word->byte),byte list)component`)) (concl th)
    then GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th] else NO_TAC) THEN
  MP_TAC(ISPECL [`m:(S,N word->byte)component`; `base:N word`;
                 `LENGTH(out:byte list)`; `LENGTH(out:byte list) - off + i`;
                 `s:S`] EL_READ_BYTELIST) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;

(* A pattern chunk: 16 bytes of the pattern at off <= 16 after j shuffles.  *)

let SNAPPY_COPY_PATTERN_STEP = prove
 (`!(m:(S,N word->byte)component) t base out j off q.
        1 <= off /\ off <= 16 /\ off <= LENGTH out /\
        (!i. i < off
             ==> word_subword q (8 * i,8):byte = EL (LENGTH out - off + i) out) /\
        read (m :> bytelist(base,LENGTH out + 16 * j)) t =
          snappy_copy off (16 * j) out /\
        read (m :> bytes128 (word_add base (word(LENGTH out + 16 * j)))) t =
          snappy_pattern_iter q off j
        ==> read (m :> bytelist(base,LENGTH out + 16 * j + 16)) t =
            snappy_copy off (16 * j + 16) out`,
  REWRITE_TAC[READ_BYTELIST_EQ_EL; LENGTH_SNAPPY_COPY] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRY(CONJ_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i < LENGTH(out:byte list) + 16 * j` THENL
   [FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
       can (find_term ((=) `snappy_copy off (16 * j) (out:byte list)`)) (concl th)
       then MP_TAC(SPEC `i:num` th) else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SNAPPY_COPY_ADD] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC EL_SNAPPY_COPY_PREFIX THEN
    ASM_REWRITE_TAC[LENGTH_SNAPPY_COPY];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_SNAPPY_COPY_PERIODIC o rand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC `u = i - (LENGTH(out:byte list) + 16 * j)` THEN
  SUBGOAL_THEN `i = (LENGTH(out:byte list) + 16 * j) + u /\ u < 16`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  SUBGOAL_THEN `word_add (base:N word) (word((LENGTH(out:byte list) + 16 * j) + u)) =
                word_add (word_add base (word(LENGTH out + 16 * j))) (word u)`
  SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_SIMP_TAC[READ_BYTES8_OF_BYTES128; SNAPPY_PATTERN_ITER_BYTE] THEN
  SUBGOAL_THEN `(16 * j + u) MOD off < off` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `1 <= off ==> ~(off = 0)`]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;
