(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The block loop of the compressor (snappy_compress_blocks) one fragment at *)
(* a time, as the loop of InternalCompress runs it: the blocks of the first  *)
(* 65536 * k bytes, then the next fragment; the length of the output so far; *)
(* and the bound that keeps the output region of each fragment (its         *)
(* MaxCompressedLength bytes after the output so far) in the output buffer   *)
(* of MaxCompressedLength of the whole input.                                *)
(* ========================================================================= *)

needs "common/snappy/snappy_roundtrip.ml";;

(* ------------------------------------------------------------------------- *)
(* Sublists of sublists.                                                     *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_SUB_LIST_SUB_LIST = prove
 (`!(l:A list) a b c d.
        a + c <= d
        ==> SUB_LIST(a,c) (SUB_LIST(b,d) l) = SUB_LIST(b + a,c) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[SUB_LIST_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `c:num`; `d:num`] THEN
  MAP_EVERY (fun v -> STRUCT_CASES_TAC(SPEC v num_CASES))
   [`a:num`; `b:num`; `c:num`; `d:num`] THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; ADD_CLAUSES; LE_0;
              ARITH_RULE `~(SUC n <= 0) /\ ~(a + SUC n <= 0)`] THEN
  DISCH_TAC THEN
  TRY(MATCH_MP_TAC(MESON[] `x = y ==> CONS (h:A) x = CONS h y`)) THEN
  FIRST_X_ASSUM(fun th ->
    W(fun (_,w) ->
      let l,r = dest_eq w in
      let ac = rand(rator l) and bd = rand(rator(rand l)) in
      MP_TAC(SPECL [lhand ac; lhand bd; rand ac; rand bd] th))) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The blocks of a prefix of 65536 * k bytes, then the next fragment.        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_BLOCKS_NIL = prove
 (`!level. snappy_compress_blocks level [] = []`,
  ONCE_REWRITE_TAC[SNAPPY_COMPRESS_BLOCKS] THEN REWRITE_TAC[]);;

let SNAPPY_BLOCKS_SHORT = prove
 (`!level (l:byte list).
        ~(l = []) /\ LENGTH l <= 65536
        ==> snappy_compress_blocks level l = snappy_compress_fragment level l`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SNAPPY_COMPRESS_BLOCKS] THEN
  ASM_SIMP_TAC[SUB_LIST_TRIVIAL; ARITH_RULE `l <= 65536 ==> l - 65536 = 0`;
               SUB_LIST_CLAUSES; SNAPPY_BLOCKS_NIL; APPEND_NIL; SUB_LIST_REFL]);;

let SNAPPY_BLOCKS_STEP = prove
 (`!level k (l:byte list).
        65536 * k < LENGTH l
        ==> snappy_compress_blocks level
              (SUB_LIST(0,65536 * k + MIN 65536 (LENGTH l - 65536 * k)) l) =
            APPEND (snappy_compress_blocks level (SUB_LIST(0,65536 * k) l))
                   (snappy_compress_fragment level
                      (SUB_LIST(65536 * k,MIN 65536 (LENGTH l - 65536 * k)) l))`,
  GEN_TAC THEN INDUCT_TAC THEN X_GEN_TAC `l:byte list` THEN DISCH_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; SUB_LIST_CLAUSES;
                SNAPPY_BLOCKS_NIL; APPEND] THEN
    MATCH_MP_TAC SNAPPY_BLOCKS_SHORT THEN
    REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_SUB_LIST] THEN
    UNDISCH_TAC `65536 * 0 < LENGTH(l:byte list)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m = MIN 65536 (LENGTH(l:byte list) - 65536 * SUC k)` THEN
  SUBGOAL_THEN `65536 * SUC k + m <= LENGTH(l:byte list) /\ 0 < m`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "m" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[SNAPPY_COMPRESS_BLOCKS] THEN
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_SUB_LIST] THEN
  REPEAT(COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[SUB_0] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `65536 * SUC k + m <= l
    ==> MIN (65536 * SUC k + m) l = 65536 * SUC k + m /\
        MIN (65536 * SUC k) l = 65536 * SUC k`] THEN
  ABBREV_TAC `l1 = SUB_LIST(65536,LENGTH l - 65536) (l:byte list)` THEN
  SUBGOAL_THEN
   `!a c. a + c <= LENGTH(l:byte list) - 65536
          ==> SUB_LIST(a,c) l1 = SUB_LIST(65536 + a,c) l`
  (LABEL_TAC "h8") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "l1" THEN
    MATCH_MP_TAC SNAPPY_SUB_LIST_SUB_LIST THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a c d. a + c <= d
            ==> SUB_LIST(a,c) (SUB_LIST(0,d) (l:byte list)) = SUB_LIST(a,c) l`
  (LABEL_TAC "h9") THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SNAPPY_SUB_LIST_SUB_LIST; ADD_CLAUSES];
    ALL_TAC] THEN
  let u9 a c d = USE_THEN "h9" (fun th -> MP_TAC(SPECL [a;c;d] th)) THEN
                 ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC]
  and u8 a c = USE_THEN "h8" (fun th -> MP_TAC(SPECL [a;c] th)) THEN
               ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC]
  and eq_tac = AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
               ARITH_TAC in
  SUBGOAL_THEN
   `SUB_LIST (0,65536) (SUB_LIST (0,65536 * SUC k + m) l) =
    SUB_LIST(0,65536) (l:byte list) /\
    SUB_LIST (0,65536) (SUB_LIST (0,65536 * SUC k) l) =
    SUB_LIST(0,65536) (l:byte list) /\
    SUB_LIST (65536,(65536 * SUC k + m) - 65536)
      (SUB_LIST (0,65536 * SUC k + m) l) = SUB_LIST(0,65536 * k + m) l1 /\
    SUB_LIST (65536,65536 * SUC k - 65536) (SUB_LIST (0,65536 * SUC k) l) =
    SUB_LIST(0,65536 * k) l1 /\
    SUB_LIST (65536 * SUC k,m) l = SUB_LIST(65536 * k,m) l1`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THENL
     [u9 `0` `65536` `65536 * SUC k + m` THEN REFL_TAC;
      u9 `0` `65536` `65536 * SUC k` THEN REFL_TAC;
      u9 `65536` `(65536 * SUC k + m) - 65536` `65536 * SUC k + m` THEN
      u8 `0` `65536 * k + m` THEN eq_tac;
      u9 `65536` `65536 * SUC k - 65536` `65536 * SUC k` THEN
      u8 `0` `65536 * k` THEN eq_tac;
      u8 `65536 * k` `m:num` THEN eq_tac];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l1:byte list`) THEN
  SUBGOAL_THEN `LENGTH(l1:byte list) = LENGTH(l:byte list) - 65536`
  SUBST1_TAC THENL
   [EXPAND_TAC "l1" THEN REWRITE_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `MIN 65536 (LENGTH(l:byte list) - 65536 - 65536 * k) = m`
  SUBST1_TAC THENL
   [EXPAND_TAC "m" THEN AP_TERM_TAC THEN ARITH_TAC; REWRITE_TAC[]]);;

let SNAPPY_BLOCKS_PREFIX_LENGTH = prove
 (`!level k (l:byte list).
        (level = 1 \/ level = 2) /\ 65536 * k <= LENGTH l
        ==> LENGTH(snappy_compress_blocks level (SUB_LIST(0,65536 * k) l))
            <= 67721 * k`,
  GEN_TAC THEN INDUCT_TAC THEN X_GEN_TAC `l:byte list` THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THENL
   [REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; SNAPPY_BLOCKS_NIL; LENGTH;
                LE_REFL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`level:num`; `k:num`; `l:byte list`] SNAPPY_BLOCKS_STEP) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `MIN 65536 (LENGTH(l:byte list) - 65536 * k) = 65536`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `65536 * k + 65536 = 65536 * SUC k`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LENGTH_APPEND] THEN
  MATCH_MP_TAC(ARITH_RULE
   `a <= 67721 * k /\ b <= 67721 ==> a + b <= 67721 * SUC k`) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`level:num`; `SUB_LIST(65536 * k,65536) (l:byte list)`]
    SNAPPY_FRAGMENT_CORRECT) THEN
  ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `MIN 65536 (LENGTH(l:byte list) - 65536 * k) = 65536`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ARITH_TAC]);;

let SNAPPY_BLOCKS_REGION = prove
 (`!n k v b.
        n < 2 EXP 32 /\ 65536 * k < n /\ v <= 5 /\ b <= 67721 * k
        ==> v + b + snappy_max_compressed_length (MIN 65536 (n - 65536 * k))
            <= snappy_max_compressed_length n + 5`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MIN 65536 (n - 65536 * k) < 2 EXP 32` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[SNAPPY_MAX_COMPRESSED_LENGTH_32]] THEN
  ABBREV_TAC `m = MIN 65536 (n - 65536 * k)` THEN
  SUBGOAL_THEN `65536 * k + m <= n` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `10922 * k + m DIV 6 <= n DIV 6` ASSUME_TAC THENL
   [SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN
    MP_TAC(SPECL [`m:num`; `6`] DIVISION) THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let SNAPPY_BLOCKS_ALL = prove
 (`!level (l:byte list).
        snappy_compress_blocks level (SUB_LIST(0,LENGTH l) l) =
        snappy_compress_blocks level l`,
  SIMP_TAC[SUB_LIST_REFL; LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The varint of the length (Varint::Encode32), byte by byte.               *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_VARINT_ENCODE_1 = prove
 (`!n. n < 128 ==> snappy_varint_encode n = [word n]`,
  GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[snappy_varint_encode] THEN
  ASM_REWRITE_TAC[]);;

let SNAPPY_VARINT_ENCODE_STEP = prove
 (`!n. 128 <= n ==> snappy_varint_encode n =
                    CONS (word(n MOD 128 + 128)) (snappy_varint_encode (n DIV 128))`,
  GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [snappy_varint_encode] THEN
  ASM_REWRITE_TAC[GSYM NOT_LE]);;

let SNAPPY_VARINT_ENCODE_CASES = prove
 (`!n. n < 2 EXP 32
       ==> snappy_varint_encode n =
           if n < 128 then [word n]
           else if n < 16384 then [word(n MOD 128 + 128); word(n DIV 128)]
           else if n < 2097152
           then [word(n MOD 128 + 128); word((n DIV 128) MOD 128 + 128);
                 word(n DIV 16384)]
           else if n < 268435456
           then [word(n MOD 128 + 128); word((n DIV 128) MOD 128 + 128);
                 word((n DIV 16384) MOD 128 + 128); word(n DIV 2097152)]
           else [word(n MOD 128 + 128); word((n DIV 128) MOD 128 + 128);
                 word((n DIV 16384) MOD 128 + 128);
                 word((n DIV 2097152) MOD 128 + 128); word(n DIV 268435456)]`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `n < 128` THEN ASM_SIMP_TAC[SNAPPY_VARINT_ENCODE_1] THEN
  ASM_CASES_TAC `n < 16384` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `128 <= n /\ n DIV 128 < 128` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[SNAPPY_VARINT_ENCODE_1; SNAPPY_VARINT_ENCODE_STEP]];
    ALL_TAC] THEN
  ASM_CASES_TAC `n < 2097152` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `128 <= n /\ 128 <= n DIV 128 /\ n DIV 128 DIV 128 < 128`
    STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ASM_SIMP_TAC[SNAPPY_VARINT_ENCODE_1; SNAPPY_VARINT_ENCODE_STEP] THEN
      REWRITE_TAC[DIV_DIV] THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  ASM_CASES_TAC `n < 268435456` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `128 <= n /\ 128 <= n DIV 128 /\ 128 <= n DIV 128 DIV 128 /\
                  n DIV 128 DIV 128 DIV 128 < 128`
    STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ASM_SIMP_TAC[SNAPPY_VARINT_ENCODE_1; SNAPPY_VARINT_ENCODE_STEP] THEN
      REWRITE_TAC[DIV_DIV] THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `128 <= n /\ 128 <= n DIV 128 /\ 128 <= n DIV 128 DIV 128 /\
                128 <= n DIV 128 DIV 128 DIV 128 /\
                n DIV 128 DIV 128 DIV 128 DIV 128 < 128`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `n < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[SNAPPY_VARINT_ENCODE_1; SNAPPY_VARINT_ENCODE_STEP] THEN
    REWRITE_TAC[DIV_DIV] THEN CONV_TAC NUM_REDUCE_CONV]);;
let SNAPPY_TABLE_SIZE_MONO = prove
 (`!a b. a <= b ==> snappy_table_size a <= snappy_table_size b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[snappy_table_size] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* The same with the output region of the fragment contracts,                *)
(* MaxCompressedLength(m) - 5 bytes (arm/snappy/DESIGN.md section 5.1).      *)

let SNAPPY_MAX_COMPRESSED_LENGTH_GE_32 = prove
 (`!n. 32 <= snappy_max_compressed_length n`,
  GEN_TAC THEN REWRITE_TAC[snappy_max_compressed_length] THEN
  COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let SNAPPY_BLOCKS_REGION5 = prove
 (`!n k v b.
        n < 2 EXP 32 /\ 65536 * k < n /\ v <= 5 /\ b <= 67721 * k
        ==> v + b +
            (snappy_max_compressed_length (MIN 65536 (n - 65536 * k)) - 5)
            <= snappy_max_compressed_length n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `k:num`; `v:num`; `b:num`] SNAPPY_BLOCKS_REGION) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `MIN 65536 (n - 65536 * k)` SNAPPY_MAX_COMPRESSED_LENGTH_GE_32) THEN
  ARITH_TAC);;

let SNAPPY_FRAGMENT_LENGTH5 = prove
 (`!level (src:byte list).
        (level = 1 \/ level = 2) /\ LENGTH src <= 65536
        ==> LENGTH(snappy_compress_fragment level src) <=
            snappy_max_compressed_length (LENGTH src) - 5`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MP_TAC(SPECL [`level:num`; `src:byte list`] SNAPPY_FRAGMENT_CORRECT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH(src:byte list) < 2 EXP 32` (fun th ->
    SIMP_TAC[SNAPPY_MAX_COMPRESSED_LENGTH_32; th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`LENGTH(src:byte list)`; `30`] DIVISION) THEN
  MP_TAC(SPECL [`LENGTH(src:byte list)`; `6`] DIVISION) THEN ARITH_TAC);;
