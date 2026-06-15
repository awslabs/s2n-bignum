(*
 * Copyright (c) The mldsa-native project authors
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Rejection sampling with eta=4 for ML-DSA AArch64.                         *)
(*                                                                           *)
(* Filters 4-bit nibbles < 9, maps accepted values n to (4 - n) as int32.    *)
(* Uses a 256-entry TBL lookup indexed by 8-bit masks (16 bytes each).       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/mldsa_rej_uniform_eta_table.ml";;

(* ========================================================================= *)
(* ML-DSA rejection sampling specification, eta variants.                    *)
(*                                                                           *)
(* The top-level spec takes a list of 4-bit nibbles and is a plain           *)
(* filter+map -- mirroring REJ_SAMPLE for the q-filter case.                 *)
(*   eta=2: keep nibble n if n < 15, then map to (2 - n MOD 5) :int32        *)
(*   eta=4: keep nibble n if n <  9, then map to (4 - n)        :int32       *)
(* ========================================================================= *)

let REJ_SAMPLE_ETA2 = define
  `REJ_SAMPLE_ETA2 (l:(4 word) list) =
   MAP (\x:4 word.
          word_sx (word_sub (word 2:4 word)
                            (word_umod x (word 5:4 word))):int32)
       (FILTER (\x:4 word. val x < 15) l)`;;

let REJ_SAMPLE_ETA4 = define
  `REJ_SAMPLE_ETA4 (l:(4 word) list) =
   MAP (\x:4 word. word_sx (word_sub (word 4:4 word) x):int32)
       (FILTER (\x:4 word. val x < 9) l)`;;

(* ========================================================================= *)
(* Shared lemmas for eta rejection sampling proofs.                          *)
(* ========================================================================= *)

(* Internal byte->nibble decomposition stored in int16 lanes (matching the   *)
(* SIMD register layout used by the loop body). The public spec uses        *)
(* BYTES_TO_NIBBLES at the natural 4-word bitwidth instead; this view is    *)
(* bridged to the public one via NIBBLES_OF_BYTES_EQ_BYTES_TO_NIBBLES.       *)
let NIBBLE_PAIR = define
  `NIBBLE_PAIR (b:byte) =
   [word(val b MOD 16):int16; word(val b DIV 16):int16]`;;

let NIBBLES_OF_BYTES = define
  `NIBBLES_OF_BYTES [] = ([]:(int16)list) /\
   NIBBLES_OF_BYTES (CONS (b:byte) t) =
   APPEND (NIBBLE_PAIR b) (NIBBLES_OF_BYTES t)`;;

let NIBBLES_OF_BYTES_APPEND = prove
 (`!l1 l2. NIBBLES_OF_BYTES(APPEND l1 l2) =
           APPEND (NIBBLES_OF_BYTES l1) (NIBBLES_OF_BYTES l2)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[NIBBLES_OF_BYTES; APPEND; APPEND_ASSOC]);;

let NIBBLES_OF_BYTES_4 = prove
 (`!b0 b1 b2 b3:byte.
   NIBBLES_OF_BYTES [b0;b1;b2;b3] =
   [word(val b0 MOD 16); word(val b0 DIV 16);
    word(val b1 MOD 16); word(val b1 DIV 16);
    word(val b2 MOD 16); word(val b2 DIV 16);
    word(val b3 MOD 16); word(val b3 DIV 16):int16]`,
  REWRITE_TAC[NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND]);;

let DIMINDEX_16 = DIMINDEX_CONV `dimindex(:16)`;;

let VAL_WORD_NIBBLE_LT = prove
 (`!b:byte.
   val(word(val b MOD 16):int16) = val b MOD 16 /\
   val(word(val b DIV 16):int16) = val b DIV 16`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let BYTE_AND_15_MOD = BITBLAST_RULE
  `val(word_and (b:byte) (word 15):byte) = val b MOD 16`;;

(* Splits each input byte into its low and high 4-bit nibbles, expressed at *)
(* the natural 4-bit width consumed by the REJ_SAMPLE_ETA{2,4} spec. The    *)
(* output is twice the length of the input. Used at the proof boundary to   *)
(* bridge the byte-shaped internal proof view to the nibble-shaped public   *)
(* spec.                                                                    *)
let BYTES_TO_NIBBLES = define
  `BYTES_TO_NIBBLES [] = ([]:(4 word) list) /\
   BYTES_TO_NIBBLES (CONS (b:byte) t) =
   APPEND [word(val b MOD 16):4 word; word(val b DIV 16):4 word]
          (BYTES_TO_NIBBLES t)`;;

(* Bridge: little-endian bit-content of a byte list equals little-endian    *)
(* bit-content of its nibble decomposition.                                 *)
let NUM_OF_BYTES_TO_NIBBLES = prove
 (`!l:byte list. num_of_wordlist (BYTES_TO_NIBBLES l) = num_of_wordlist l`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[BYTES_TO_NIBBLES; num_of_wordlist; NUM_OF_WORDLIST_APPEND;
              LENGTH; DIMINDEX_4; DIMINDEX_8; VAL_WORD; MOD_MOD_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `val(h:byte) DIV 16 MOD 16 = val h DIV 16` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(h:byte) MOD 16 MOD 16 = val h MOD 16` SUBST1_TAC THENL
   [REWRITE_TAC[MOD_MOD_REFL]; ALL_TAC] THEN
  MP_TAC(SPECL [`val(h:byte)`; `16`] DIVISION) THEN ARITH_TAC);;

let LENGTH_BYTES_TO_NIBBLES = prove
 (`!l:byte list. LENGTH(BYTES_TO_NIBBLES l) = 2 * LENGTH l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[BYTES_TO_NIBBLES; LENGTH; LENGTH_APPEND] THEN ARITH_TAC);;

(* Surjectivity onto even-length nibble lists: any nibble list of even      *)
(* length is the BYTES_TO_NIBBLES image of some byte list (twice as short). *)
let BYTES_TO_NIBBLES_SURJ = prove
 (`!l:(4 word) list. EVEN(LENGTH l)
                     ==> ?bs:byte list. BYTES_TO_NIBBLES bs = l /\
                                        LENGTH bs = LENGTH l DIV 2`,
  GEN_TAC THEN WF_INDUCT_TAC `LENGTH(l:(4 word) list)` THEN
  DISCH_TAC THEN ASM_CASES_TAC `l:(4 word) list = []` THENL
   [EXISTS_TAC `[]:byte list` THEN ASM_REWRITE_TAC[BYTES_TO_NIBBLES; LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(ISPEC `l:(4 word) list` list_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:4 word`
              (X_CHOOSE_THEN `t0:(4 word) list` SUBST_ALL_TAC)) THEN
  ASM_CASES_TAC `t0:(4 word) list = []` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `EVEN (LENGTH (CONS (n0:4 word) []))` THEN
    REWRITE_TAC[LENGTH; EVEN; ARITH_RULE `~(SUC 0 = 0)`]; ALL_TAC] THEN
  MP_TAC(ISPEC `t0:(4 word) list` list_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:4 word`
              (X_CHOOSE_THEN `t:(4 word) list` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:(4 word) list`) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `n < SUC(SUC n)`] THEN
  UNDISCH_TAC `EVEN (LENGTH (CONS (n0:4 word) (CONS n1 t)))` THEN
  REWRITE_TAC[LENGTH; EVEN] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `bs:byte list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `CONS (word(val(n0:4 word) + 16 * val(n1:4 word)):byte) bs` THEN
  ASM_REWRITE_TAC[BYTES_TO_NIBBLES; LENGTH; APPEND; CONS_11] THEN
  MP_TAC(ISPEC `n0:4 word` VAL_BOUND) THEN
  MP_TAC(ISPEC `n1:4 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_4] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT DISCH_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
    `(val(n0:4 word) + 16 * val(n1:4 word)) MOD 256 = val n0 + 16 * val n1`
    SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `val(n0:4 word) + 16 * val(n1:4 word) = val n1 * 16 + val n0` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ; MOD_LT; DIV_LT;
               ADD_CLAUSES] THEN
  REWRITE_TAC[WORD_VAL] THEN
  UNDISCH_TAC `EVEN (LENGTH (t:(4 word) list))` THEN
  REWRITE_TAC[EVEN_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
  REWRITE_TAC[ARITH_RULE `2 * m = m * 2`; DIV_MULT; ARITH_EQ] THEN ARITH_TAC);;

(* Relate the two byte->nibble views: NIBBLES_OF_BYTES carries nibbles in    *)
(* int16 lanes (matching SIMD storage), whereas BYTES_TO_NIBBLES uses the   *)
(* natural 4-bit width consumed by the public REJ_SAMPLE_ETA{2,4} spec.     *)
let NIBBLES_OF_BYTES_EQ_BYTES_TO_NIBBLES = prove
 (`!l:byte list.
     NIBBLES_OF_BYTES l = MAP (\x:4 word. word_zx x:int16) (BYTES_TO_NIBBLES l)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[NIBBLES_OF_BYTES; BYTES_TO_NIBBLES; MAP]; ALL_TAC] THEN
  REWRITE_TAC[NIBBLES_OF_BYTES; BYTES_TO_NIBBLES; MAP; APPEND] THEN
  ASM_REWRITE_TAC[NIBBLE_PAIR] THEN
  REWRITE_TAC[CONS_11; word_zx; VAL_WORD; DIMINDEX_4; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[APPEND; CONS_11; MOD_MOD_REFL] THEN
  REPEAT DISCH_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  MP_TAC(SPECL [`val (h:byte) DIV 16`; `16`] MOD_LT) THEN ARITH_TAC);;

(* Splits a contiguous 8-byte chunk of a byte-list-shape memory contract     *)
(* into the 8 byte-subwords of the int64 read at that offset. Used in the   *)
(* main loop of rej_uniform_eta_{2,4}, where each iteration consumes 8      *)
(* bytes from the input via LDR Q0,[buf,...]; this lemma exposes those 8   *)
(* bytes as the components of the SUB_LIST(8*i, 8) of the abstract list.    *)
let SUB_LIST_8_BYTES_FROM_INT64 = prove
 (`!buf:int64 buflen inlist i s.
    8 * (i + 1) <= buflen /\
    LENGTH (inlist:byte list) = buflen /\
    read (memory :> bytes (buf, buflen)) s = num_of_wordlist inlist
    ==> SUB_LIST (8 * i, 8) inlist =
        [word_subword
           (read (memory :> bytes64 (word_add buf (word (8 * i)))) s) (0,8):byte;
         word_subword
           (read (memory :> bytes64 (word_add buf (word (8 * i)))) s) (8,8);
         word_subword
           (read (memory :> bytes64 (word_add buf (word (8 * i)))) s) (16,8);
         word_subword
           (read (memory :> bytes64 (word_add buf (word (8 * i)))) s) (24,8);
         word_subword
           (read (memory :> bytes64 (word_add buf (word (8 * i)))) s) (32,8);
         word_subword
           (read (memory :> bytes64 (word_add buf (word (8 * i)))) s) (40,8);
         word_subword
           (read (memory :> bytes64 (word_add buf (word (8 * i)))) s) (48,8);
         word_subword
           (read (memory :> bytes64 (word_add buf (word (8 * i)))) s) (56,8)]`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
    `loaded_d = read (memory :> bytes64 (word_add buf (word (8 * i)))) s` THEN
  CONV_TAC SYM_CONV THEN
  REWRITE_TAC[LISTS_NUM_OF_WORDLIST_EQ] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LENGTH; LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST; DIMINDEX_8] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM
    `\x. x DIV 2 EXP (8 * 8 * i) MOD 2 EXP (8 * 8)`) THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  SUBGOAL_THEN `MIN (buflen - 8 * i) 8 = 8` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
    [`word_add buf (word (8 * i)):int64`; `read memory s`]
    (INST_TYPE[`:64`,`:N`] VAL_READ_WBYTES)) THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM BYTES64_WBYTES; GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[num_of_wordlist; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST);;

let BYTE_SPLIT_AND = map (fun k ->
    BITBLAST_RULE(parse_term(Printf.sprintf
     "!x:int128 b:byte. \
       word_subword x (%d,16):int16 = word_zx(word_and b (word 15):byte):int16 \
       ==> word_subword x (%d,8):byte = word_and b (word 15):byte /\\ \
           word_subword x (%d,8):byte = word 0:byte"
     (k*16) (k*16) (k*16+8))))
  (0--7);;

let BYTE_SPLIT_USHR = map (fun k ->
    BITBLAST_RULE(parse_term(Printf.sprintf
     "!x:int128 b:byte. \
       word_subword x (%d,16):int16 = word_zx(word_ushr b 4:byte):int16 \
       ==> word_subword x (%d,8):byte = word_ushr b 4:byte /\\ \
           word_subword x (%d,8):byte = word 0:byte"
     (k*16) (k*16) (k*16+8))))
  (0--7);;

let BYTE_USHR4_DIV = WORD_BLAST
  `val(word_ushr (b:byte) 4:byte) = val b DIV 16`;;

let POPCOUNT_AND_POWERS = BITBLAST_RULE
  `word_popcount(word_and (word 1) x:byte) = bitval(bit 0 x) /\
   word_popcount(word_and (word 2) x:byte) = bitval(bit 1 x) /\
   word_popcount(word_and (word 4) x:byte) = bitval(bit 2 x) /\
   word_popcount(word_and (word 8) x:byte) = bitval(bit 3 x) /\
   word_popcount(word_and (word 16) x:byte) = bitval(bit 4 x) /\
   word_popcount(word_and (word 32) x:byte) = bitval(bit 5 x) /\
   word_popcount(word_and (word 64) x:byte) = bitval(bit 6 x) /\
   word_popcount(word_and (word 128) x:byte) = bitval(bit 7 x)`;;

let UADDLV_BOUND_LEMMA = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7.
   val(word_zx(word_subword
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b0):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b1):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b2):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b3):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b4):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b5):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b6):byte):int16)(0,16):int128)
     (word_subword(word_join (word 0:byte) (word(bitval b7):byte):int16)(0,16):int128))))))))(0,32):int32):int64) <= 8`,
  REPEAT GEN_TAC THEN
  MAP_EVERY BOOL_CASES_TAC [`b0:bool`;`b1:bool`;`b2:bool`;`b3:bool`;
    `b4:bool`;`b5:bool`;`b6:bool`;`b7:bool`] THEN
  REWRITE_TAC[bitval] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

let UADDLV_COUNT_LEMMA = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7.
   val(word_zx(word_subword
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b0):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b1):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b2):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b3):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b4):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b5):byte):int16)(0,16):int128)
     (word_add (word_subword(word_join (word 0:byte) (word(bitval b6):byte):int16)(0,16):int128)
     (word_subword(word_join (word 0:byte) (word(bitval b7):byte):int16)(0,16):int128))))))))(0,32):int32):int64) =
   bitval b0 + bitval b1 + bitval b2 + bitval b3 +
   bitval b4 + bitval b5 + bitval b6 + bitval b7`,
  REPEAT GEN_TAC THEN
  MAP_EVERY BOOL_CASES_TAC [`b0:bool`;`b1:bool`;`b2:bool`;`b3:bool`;
    `b4:bool`;`b5:bool`;`b6:bool`;`b7:bool`] THEN
  REWRITE_TAC[bitval] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

let VAL_WORD_ZX_BYTE16 = WORD_BLAST
  `val(word_zx (b:byte):int16) = val b`;;

let VAL_BYTE_NIB_MOD_65536 = prove(
  `!b:byte. (val b DIV 16) MOD 65536 = val b DIV 16 /\
            val b MOD 16 MOD 65536 = val b MOD 16`,
  GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let WORD_ADD_SHL1 = WORD_BLAST
 `!sp (x:int64) k.
    word_add (word_add sp (word(2 * k):int64))
             (word_shl x 1:int64) =
    word_add sp (word(2 * (k + val(x:int64))):int64)`;;

let LENGTH_FILTER = prove
 (`!P l:A list. LENGTH(FILTER P l) <= LENGTH l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; LE_REFL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC);;

let SUB_LIST_MAP = prove(
  `!f (l:A list) n.
     SUB_LIST(0,n)(MAP f l) = MAP f (SUB_LIST(0,n) l):B list`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; SUB_LIST_CLAUSES]);;

let EL_SUB_LIST = prove
 (`!l:(A)list. !m n i:num.
     i < n /\ m + i < LENGTH l
     ==> EL i (SUB_LIST (m,n) l) = EL (m + i) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; LT] THEN
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
     [REWRITE_TAC[LT];
      X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
      X_GEN_TAC `i:num` THEN REWRITE_TAC[SUB_LIST; ADD_CLAUSES] THEN
      STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THENL
       [REWRITE_TAC[EL; HD];
        REWRITE_TAC[EL; TL; LT_SUC; LENGTH; ADD_CLAUSES] THEN
        STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `n:num`; `n':num`]) THEN
        ASM_REWRITE_TAC[ADD_CLAUSES] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    X_GEN_TAC `m:num` THEN DISCH_THEN(K ALL_TAC) THEN
    X_GEN_TAC `n:num` THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[SUB_LIST; LENGTH; ADD_CLAUSES; EL; TL] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`; `i:num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let SUB_LIST_4_EL = prove
 (`!l:(A)list. !k:num.
     k + 4 <= LENGTH l
     ==> SUB_LIST(k, 4) l =
         [EL k l; EL (k+1) l; EL (k+2) l; EL (k+3) l]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST; LENGTH] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC(SUC(SUC 0))) = 4`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(A)list`; `k:num`; `4`; `i:num`] EL_SUB_LIST) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
    `!P (a:A) b c d.
       (i = 0 ==> P a) /\ (i = 1 ==> P b) /\
       (i = 2 ==> P c) /\ (i = 3 ==> P d)
       ==> P(EL i [a;b;c;d])`
    (fun th -> MATCH_MP_TAC th) THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN UNDISCH_TAC `i < 4` THEN
    REWRITE_TAC[ARITH_RULE
      `i < 4 <=> i = 0 \/ i = 1 \/ i = 2 \/ i = 3`] THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `3 = SUC 2 /\ 2 = SUC 1 /\ 1 = SUC 0`;
                 EL; HD; TL];
    REPEAT CONJ_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ADD_CLAUSES]]);;

let SUB_LIST_SPLIT_AT = prove
 (`!(l:A list) i.
     i <= LENGTH l
     ==> l = APPEND (SUB_LIST(0, i) l) (SUB_LIST(i, LENGTH l - i) l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:A list`; `i:num`] SUB_LIST_TOPSPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
  REFL_TAC);;

let SUB_LIST_8nn_INLIST = prove
 (`!inlist:byte list. !nn:num. !buflen:num.
     8 divides buflen /\
     buflen < 8 * (nn + 1) /\
     LENGTH inlist = buflen
     ==>
     SUB_LIST(0, 8 * nn) inlist = inlist`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUB_LIST_REFL THEN
  UNDISCH_TAC `8 divides buflen` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
  UNDISCH_TAC `LENGTH(inlist:byte list) = 8 * k` THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LE_MULT_LCANCEL] THEN
  UNDISCH_TAC `8 * k < 8 * (nn + 1)` THEN
  REWRITE_TAC[LT_MULT_LCANCEL] THEN ARITH_TAC);;

let STACK_CONTENT = define
 `STACK_CONTENT (niblist:int16 list) =
    SUB_LIST(0, 256) (APPEND niblist (REPLICATE 256 (word 0:int16)))`;;

let STACK_CONTENT_LARGE = prove
 (`!niblist:int16 list.
     256 <= LENGTH niblist
     ==> STACK_CONTENT niblist = SUB_LIST(0, 256) niblist`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STACK_CONTENT] THEN
  MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN ASM_REWRITE_TAC[]);;

let BYTES8_INT16S_TO_BYTES64 = prove
 (`!s:armstate (a:int64) (ws:int16 list).
    LENGTH ws = 4 /\
    read (memory :> bytes (a, 8)) s = num_of_wordlist ws
    ==>
    read (memory :> bytes64 a) s = word(num_of_wordlist ws)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `num_of_wordlist (ws:int16 list) < 2 EXP 64` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ws:int16 list`; `64:num`] NUM_OF_WORDLIST_BOUND_GEN) THEN
    REWRITE_TAC[DIMINDEX_16] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; READ_COMPONENT_COMPOSE; BYTES64_WBYTES;
              VAL_READ_WBYTES; DIMINDEX_64; ARITH_RULE `64 DIV 8 = 8`;
              VAL_WORD; DIMINDEX_64] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]);;

let BK_FROM_STACK = prove
 (`!s:armstate. !sp:int64. !niblist:int16 list. !k:num.
    4 * (k + 1) <= LENGTH niblist /\
    read (memory :> bytes (sp, 2 * LENGTH niblist)) s = num_of_wordlist niblist
    ==>
    read (memory :> bytes64 (word_add sp (word (8 * k)))) s =
    word(num_of_wordlist (SUB_LIST(4*k, 4) niblist))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BYTES8_INT16S_TO_BYTES64 THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `read (memory :> bytes (sp, 2 * LENGTH(niblist:int16 list))) s =
     num_of_wordlist (APPEND (SUB_LIST(0, 4 * k) niblist)
                             (SUB_LIST(4 * k, LENGTH niblist - 4 * k) niblist))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`niblist:int16 list`; `4 * k:num`] SUB_LIST_SPLIT_AT) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC
      (RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * LENGTH(niblist:int16 list) = 8 * k + (2 * LENGTH niblist - 8 * k)`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`memory:(armstate,(64)word->(8)word)component`;
                 `sp:int64`; `s:armstate`;
                 `SUB_LIST(0, 4 * k) (niblist:int16 list)`;
                 `SUB_LIST(4 * k, LENGTH(niblist:int16 list) - 4 * k) (niblist:int16 list)`;
                 `8 * k:num`; `2 * LENGTH(niblist:int16 list) - 8 * k:num`]
                BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
  REWRITE_TAC[LENGTH_SUB_LIST; SUB_0; DIMINDEX_16] THEN
  SUBGOAL_THEN `MIN (4 * k) (LENGTH(niblist:int16 list)) = 4 * k` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o (REWRITE_RULE[th]))) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN
    `SUB_LIST(4 * k, LENGTH(niblist:int16 list) - 4 * k) niblist =
     APPEND (SUB_LIST(4 * k, 4) niblist)
            (SUB_LIST(4 * k + 4, LENGTH niblist - 4 * k - 4) niblist)`
  (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [MP_TAC(ISPECL [`niblist:int16 list`; `4:num`; `LENGTH(niblist:int16 list) - 4 * k - 4`;
                   `4 * k:num`] SUB_LIST_SPLIT) THEN
    SUBGOAL_THEN `4 + LENGTH(niblist:int16 list) - 4 * k - 4 = LENGTH niblist - 4 * k`
      SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * LENGTH(niblist:int16 list) - 8 * k = 8 + (2 * LENGTH niblist - 8 * k - 8)`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`memory:(armstate,(64)word->(8)word)component`;
                 `word_add sp (word (8 * k)):int64`; `s:armstate`;
                 `SUB_LIST(4 * k, 4) (niblist:int16 list)`;
                 `SUB_LIST(4 * k + 4, LENGTH(niblist:int16 list) - 4 * k - 4) niblist`;
                 `8:num`; `2 * LENGTH(niblist:int16 list) - 8 * k - 8:num`]
                BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
  REWRITE_TAC[LENGTH_SUB_LIST; DIMINDEX_16] THEN
  SUBGOAL_THEN `MIN 4 (LENGTH(niblist:int16 list) - 4 * k) = 4` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o (REWRITE_RULE[th]))) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[]);;

let BK_FROM_STACK_GE256 = prove
 (`!s:armstate. !sp:int64. !niblist:int16 list. !k:num.
    k < 64 /\ 256 <= LENGTH niblist /\
    read (memory :> bytes (sp, 2 * LENGTH niblist)) s = num_of_wordlist niblist
    ==>
    read (memory :> bytes64 (word_add sp (word (8 * k)))) s =
    word(num_of_wordlist (SUB_LIST(4*k, 4) niblist))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BK_FROM_STACK THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let BYTES_EXISTS_WORDLIST = prove
 (`!(a:int64) n s.
    ?(L:int16 list). LENGTH L = n /\
    read (memory :> bytes (a, 2 * n)) s = num_of_wordlist L`,
  GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THENL
   [EXISTS_TAC `[]:int16 list` THEN
    REWRITE_TAC[LENGTH; MULT_CLAUSES; num_of_wordlist;
                READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:armstate`) THEN
  DISCH_THEN(X_CHOOSE_THEN `L:int16 list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `APPEND (L:int16 list)
                [word (read (memory :> bytes (word_add a (word (2*n)), 2)) s):int16]` THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
  ASM_REWRITE_TAC[ARITH_RULE `n + 1 = SUC n`] THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC n = 2 * n + 2`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[NUM_OF_WORDLIST_APPEND; DIMINDEX_16; num_of_wordlist;
                  MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `8 * 2 * n = 16 * n`] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPECL [`word_add (a:int64) (word (2*n)):int64`; `2`;
                 `read memory s`] READ_BYTES_BOUND) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let PREFIX_FROM_STACK = prove
 (`!stackpointer:int64 (niblist:int16 list) (L:int16 list) s:armstate niblen.
    LENGTH niblist = niblen /\
    LENGTH L = 256 /\
    niblen <= 256 /\
    read (memory :> bytes (stackpointer, 2 * niblen)) s = num_of_wordlist niblist /\
    read (memory :> bytes (stackpointer, 512)) s = num_of_wordlist L
    ==> SUB_LIST(0, niblen) L = niblist`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`memory:(armstate,(64)word->(8)word)component`;
                 `stackpointer:int64`; `s:armstate`;
                 `SUB_LIST(0, niblen) (L:int16 list)`;
                 `SUB_LIST(niblen, 256 - niblen) (L:int16 list)`;
                 `2 * niblen:num`; `512 - 2 * niblen:num`]
                BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
  REWRITE_TAC[DIMINDEX_16; LENGTH_SUB_LIST; SUB_0] THEN
  SUBGOAL_THEN `MIN niblen (LENGTH(L:int16 list)) = niblen` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 * niblen + 512 - 2 * niblen = 512` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
     `APPEND (SUB_LIST(0, niblen) (L:int16 list))
             (SUB_LIST(niblen, 256 - niblen) L) = L`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L:int16 list`; `niblen:num`] SUB_LIST_SPLIT_AT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
    REFL_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`SUB_LIST(0, niblen) (L:int16 list)`; `niblist:int16 list`]
                LISTS_NUM_OF_WORDLIST_EQ) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN
  ASM_ARITH_TAC);;

let BIGNUM_OF_WORDLIST_EQ_NUM_OF_WORDLIST = prove
 (`!l:int64 list. bignum_of_wordlist l = num_of_wordlist l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[bignum_of_wordlist; num_of_wordlist; DIMINDEX_64]);;

let BIGNUM_CONS_WORDJOIN = prove
 (`!a:int32. !b:int32. !t:int64 list.
     bignum_of_wordlist (CONS (word_join a b:int64) t) =
     num_of_wordlist [b; a] + 2 EXP 64 * bignum_of_wordlist t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bignum_of_wordlist; num_of_wordlist;
              DIMINDEX_32; MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_JOIN; DIMINDEX_64; DIMINDEX_32] THEN
  MP_TAC(ISPEC `a:int32` VAL_BOUND) THEN
  MP_TAC(ISPEC `b:int32` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_32] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(2 EXP 32 * val(a:int32) + val(b:int32)) MOD 2 EXP 64 =
                2 EXP 32 * val a + val b` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ARITH_TAC]);;

let VAL_WORD_JOIN_INT32_INT64 = prove
 (`!a:int32. !b:int32.
     val (word_join (a:int32) (b:int32):int64) = 2 EXP 32 * val a + val b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_JOIN; DIMINDEX_64; DIMINDEX_32] THEN
  MP_TAC(ISPEC `a:int32` VAL_BOUND) THEN
  MP_TAC(ISPEC `b:int32` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_32] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let BIGNUM_WORDJOIN_PAIRS_EXISTS = prove
 (`!n l:int32 list. LENGTH l = 2 * n
   ==> ?pairs:int64 list.
         LENGTH pairs = n /\
         bignum_of_wordlist pairs = num_of_wordlist l /\
         (!i. i < n ==> EL i pairs = word_join (EL (2*i+1) l) (EL (2*i) l))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; LENGTH_EQ_NIL] THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `[]:int64 list` THEN
    REWRITE_TAC[LENGTH; bignum_of_wordlist; num_of_wordlist; LT];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  STRUCT_CASES_TAC (ISPEC `t:int32 list` list_CASES) THENL
   [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LENGTH;
    ARITH_RULE `SUC(SUC(LENGTH(t':int32 list))) = 2 * SUC n <=>
                LENGTH t' = 2 * n`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t':int32 list`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `pairs:int64 list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `CONS (word_join (h':int32) (h:int32):int64) pairs` THEN
  ASM_REWRITE_TAC[LENGTH] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`h':int32`; `h:int32`; `pairs:int64 list`]
                 BIGNUM_CONS_WORDJOIN) THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[num_of_wordlist; DIMINDEX_32] THEN ARITH_TAC;
    X_GEN_TAC `i:num` THEN
    STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THENL
     [REWRITE_TAC[EL; HD; MULT_CLAUSES; ADD_CLAUSES; TL] THEN
      REWRITE_TAC[ARITH_RULE `1 = SUC 0`; EL; TL; HD];
      REWRITE_TAC[EL; TL; LT_SUC] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n':num`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ARITH_RULE `2 * SUC n' + 1 = SUC(SUC(2 * n' + 1)) /\
                               2 * SUC n' = SUC(SUC(2 * n'))`] THEN
      REWRITE_TAC[EL; TL; HD]]]);;

let SUB_LIST_EQ_LIST_OF_SEQ = prove
 (`!n l:A list. n <= LENGTH l ==> SUB_LIST (0,n) l = list_of_seq (\i. EL i l) n`,
  INDUCT_TAC THENL
   [REWRITE_TAC[SUB_LIST_CLAUSES; LIST_OF_SEQ]; ALL_TAC] THEN
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; LIST_OF_SEQ; LENGTH; LE_SUC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:A list`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[EL; HD; TL; o_THM] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; EL; TL]);;

let WORD_OF_NUM_4INT16 = prove
 (`!h0 h1 h2 h3:int16.
     word (num_of_wordlist [h0;h1;h2;h3]):int64 =
     word_join (word_join h3 h2:int32) (word_join h1 h0:int32)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_wordlist; DIMINDEX_16; MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_JOIN; DIMINDEX_64; DIMINDEX_32;
              DIMINDEX_16; VAL_WORD] THEN
  MP_TAC(ISPEC `h0:int16` VAL_BOUND) THEN
  MP_TAC(ISPEC `h1:int16` VAL_BOUND) THEN
  MP_TAC(ISPEC `h2:int16` VAL_BOUND) THEN
  MP_TAC(ISPEC `h3:int16` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_16] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(2 EXP 16 * val(h3:int16) + val(h2:int16)) MOD 2 EXP 32 =
                2 EXP 16 * val h3 + val h2` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(2 EXP 16 * val(h1:int16) + val(h0:int16)) MOD 2 EXP 32 =
                2 EXP 16 * val h1 + val h0` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let WORD_SUBWORD_JOIN_SUB_LIST_H = prove
 (`!niblist:int16 list. !a:num.
     a + 8 <= LENGTH niblist
     ==>
     word_subword (word_join
       (word(num_of_wordlist(SUB_LIST(a+4,4) niblist)):int64)
       (word(num_of_wordlist(SUB_LIST(a,4) niblist)):int64):int128) (0,16):int16 =
       EL a niblist /\
     word_subword (word_join
       (word(num_of_wordlist(SUB_LIST(a+4,4) niblist)):int64)
       (word(num_of_wordlist(SUB_LIST(a,4) niblist)):int64):int128) (16,16):int16 =
       EL (a+1) niblist /\
     word_subword (word_join
       (word(num_of_wordlist(SUB_LIST(a+4,4) niblist)):int64)
       (word(num_of_wordlist(SUB_LIST(a,4) niblist)):int64):int128) (32,16):int16 =
       EL (a+2) niblist /\
     word_subword (word_join
       (word(num_of_wordlist(SUB_LIST(a+4,4) niblist)):int64)
       (word(num_of_wordlist(SUB_LIST(a,4) niblist)):int64):int128) (48,16):int16 =
       EL (a+3) niblist /\
     word_subword (word_join
       (word(num_of_wordlist(SUB_LIST(a+4,4) niblist)):int64)
       (word(num_of_wordlist(SUB_LIST(a,4) niblist)):int64):int128) (64,16):int16 =
       EL (a+4) niblist /\
     word_subword (word_join
       (word(num_of_wordlist(SUB_LIST(a+4,4) niblist)):int64)
       (word(num_of_wordlist(SUB_LIST(a,4) niblist)):int64):int128) (80,16):int16 =
       EL (a+5) niblist /\
     word_subword (word_join
       (word(num_of_wordlist(SUB_LIST(a+4,4) niblist)):int64)
       (word(num_of_wordlist(SUB_LIST(a,4) niblist)):int64):int128) (96,16):int16 =
       EL (a+6) niblist /\
     word_subword (word_join
       (word(num_of_wordlist(SUB_LIST(a+4,4) niblist)):int64)
       (word(num_of_wordlist(SUB_LIST(a,4) niblist)):int64):int128) (112,16):int16 =
       EL (a+7) niblist`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `a + 4 <= LENGTH(niblist:int16 list) /\
                (a + 4) + 4 <= LENGTH(niblist:int16 list)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`niblist:int16 list`; `a:num`] SUB_LIST_4_EL) THEN
  MP_TAC(ISPECL [`niblist:int16 list`; `a+4:num`] SUB_LIST_4_EL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `(a+4)+1 = a+5 /\ (a+4)+2 = a+6 /\ (a+4)+3 = a+7`] THEN
  REWRITE_TAC[WORD_OF_NUM_4INT16] THEN CONV_TAC WORD_BLAST);;

let WORD_INSERT_Q31 = prove(
  `word_insert ((word_insert:int128->num#num->int64->int128) q (0,64)
    (word 2251816993685505)) (64,64) (word 36029071898968080:int64) =
    (word 664619068533544770747334646890102785:int128)`,
  CONV_TAC WORD_BLAST);;

let FILTER_EL_SATISFIES = prove(
 `!(P:A->bool) l i. i < LENGTH(FILTER P l) ==> P(EL i (FILTER P l))`,
 GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; LENGTH; LT] THEN
 GEN_TAC THEN COND_CASES_TAC THENL
  [STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
   REWRITE_TAC[EL; HD; TL; LENGTH; LT_SUC] THENL
    [ASM_REWRITE_TAC[]; ASM_MESON_TAC[]];
   ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* Bound lemmas for closing val(idx0)/val(idx1) < 256 in MEMSAFE Subgoal 3   *)
(* of rejection sampling proofs. idx0/idx1 are X12/X13 popcount-accumulator  *)
(* values; their formal shape is word_zx (word_subword (sum-of-8) (0,32)).   *)
(*                                                                           *)
(* These four lemmas have no dependency on consttime symbols and are safe    *)
(* to load at the top of any proof file. The MEMSAFE-discharge tactical      *)
(* helpers (DISCHARGE_MEMSAFE_TAC etc.) depend on consttime symbols and are  *)
(* therefore kept inline in eta2/eta4, where consttime is loaded mid-file.   *)
(* ========================================================================= *)

let WORD_ZX_INT32_INT64 = prove
 (`!w:int32. val(word_zx w:int64) = val w`,
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_64] THEN
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPEC `w:int32` (INST_TYPE [`:32`,`:N`] VAL_BOUND)) THEN
  REWRITE_TAC[DIMINDEX_32] THEN ARITH_TAC);;

let VAL_WORD_SUBWORD_0_32 = prove
 (`!X:M word. val(word_subword X (0,32):int32) = val X MOD 2 EXP 32`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_32] THEN
  REWRITE_TAC[ARITH_RULE `MIN 32 32 = 32`; EXP; DIV_1]);;

(* Polymorphic version: works for any word width N where 256 <= 2^dimindex(:N). *)
let SUM_8_BIT_BOUND_POLY = prove
 (`!a1 a2 a3 a4 a5 a6 a7 a8:N word.
     256 <= 2 EXP dimindex(:N) /\
     val a1 <= 1 /\ val a2 <= 2 /\ val a3 <= 4 /\ val a4 <= 8 /\
     val a5 <= 16 /\ val a6 <= 32 /\ val a7 <= 64 /\ val a8 <= 128
     ==> val(word_add a1 (word_add a2 (word_add a3 (word_add a4
              (word_add a5 (word_add a6 (word_add a7 a8))))))) <= 255`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD] THEN
  REPEAT(W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o lhand o snd) THEN
         (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
         DISCH_THEN SUBST1_TAC) THEN
  ASM_ARITH_TAC);;

(* Polymorphic SBND for any (k, N): val(word_and (word k:N word) X) <= k for k <= 128. *)
let SBND_K_POLY = prove
 (`!k:num B:bool X.
     k <= 128 /\ 8 <= dimindex(:N)
     ==> val((word_and (word k:N word) X):N word) <= k`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LE_TRANS `val(word k:N word)` THEN
  REWRITE_TAC[VAL_WORD_AND_LE] THEN
  REWRITE_TAC[VAL_WORD] THEN
  W(MP_TAC o PART_MATCH lhand MOD_LE o lhand o snd) THEN
  REWRITE_TAC[]);;

(* Generic version of BIGNUM_LIST_OF_SEQ_EQ_NUM_SUB_LIST: relate a paired   *)
(* int64 list-of-seq built from a per-element function `f` to the          *)
(* num_of_wordlist of MAP f over a 2*n-element prefix of niblist. Used by  *)
(* rej_uniform_eta_{2,4} with f instantiated to the per-element decode.    *)
let BIGNUM_LIST_OF_SEQ_EQ_NUM_SUB_LIST_POLY = prove
 (`!(f:int16 -> int32) (niblist:int16 list) n.
     2 * n <= LENGTH niblist
     ==>
     bignum_of_wordlist
       (list_of_seq (\i:num. word_join
           (f (EL (2*i+1) niblist)) (f (EL (2*i) niblist)):int64) n) =
     num_of_wordlist (MAP f (SUB_LIST(0, 2*n) niblist))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; list_of_seq; bignum_of_wordlist;
                SUB_LIST_CLAUSES; MAP; num_of_wordlist];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[list_of_seq;
              BIGNUM_OF_WORDLIST_APPEND; LENGTH_LIST_OF_SEQ;
              bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_JOIN_INT32_INT64] THEN
  SUBGOAL_THEN
    `SUB_LIST(0, 2 + 2 * n) (niblist:int16 list) =
     APPEND (SUB_LIST(0, 2 * n) niblist) (SUB_LIST(2 * n, 2) niblist)`
    SUBST1_TAC THENL
   [MP_TAC(ISPECL [`niblist:int16 list`; `2*n:num`; `2`; `0`] SUB_LIST_SPLIT) THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `2 * n + 2 = 2 + 2 * n`] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MAP_APPEND; NUM_OF_WORDLIST_APPEND; DIMINDEX_32;
              LENGTH_MAP; LENGTH_SUB_LIST] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `MIN (2 * n) (LENGTH(niblist:int16 list) - 0) = 2 * n`
    SUBST1_TAC THENL
   [REWRITE_TAC[SUB_0] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `64 * n = 32 * 2 * n`] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `SUB_LIST(2 * n, 2) (niblist:int16 list) =
                [EL (2*n) niblist; EL (2*n+1) niblist]` SUBST1_TAC THENL
   [REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST; LENGTH] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[ARITH_RULE `SUC(SUC 0) = 2`] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`niblist:int16 list`; `2*n:num`; `2`; `i:num`]
                  EL_SUB_LIST) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `i = 0 \/ i = 1` MP_TAC THENL
     [ASM_ARITH_TAC;
      STRIP_TAC THEN ASM_REWRITE_TAC[EL; HD; TL; ADD_CLAUSES; num_CONV `1`]];
    REWRITE_TAC[MAP; num_of_wordlist; DIMINDEX_32; MULT_CLAUSES;
                ADD_CLAUSES] THEN ARITH_TAC]);;

(**** print_literal_from_elf "arm/mldsa/mldsa_rej_uniform_eta4_VARIABLE_TIME.o";;
 ****)

let mldsa_rej_uniform_eta4_mc = define_assert_from_elf
  "mldsa_rej_uniform_eta4_mc" "arm/mldsa/mldsa_rej_uniform_eta4_VARIABLE_TIME.o"
(*** BYTECODE START ***)
[
  0xd10903ff;       (* arm_SUB SP SP (rvalue (word 576)) *)
  0xd2800027;       (* arm_MOV X7 (rvalue (word 1)) *)
  0xf2a00047;       (* arm_MOVK X7 (word 2) 16 *)
  0xf2c00087;       (* arm_MOVK X7 (word 4) 32 *)
  0xf2e00107;       (* arm_MOVK X7 (word 8) 48 *)
  0x4e081cff;       (* arm_INS_GEN Q31 X7 0 64 *)
  0xd2800207;       (* arm_MOV X7 (rvalue (word 16)) *)
  0xf2a00407;       (* arm_MOVK X7 (word 32) 16 *)
  0xf2c00807;       (* arm_MOVK X7 (word 64) 32 *)
  0xf2e01007;       (* arm_MOVK X7 (word 128) 48 *)
  0x4e181cff;       (* arm_INS_GEN Q31 X7 64 64 *)
  0x4f00853e;       (* arm_MOVI Q30 (word 2533313445691401) *)
  0x4f008487;       (* arm_MOVI Q7 (word 1125917086973956) *)
  0x910003e8;       (* arm_ADD X8 SP (rvalue (word 0)) *)
  0xaa0803e7;       (* arm_MOV X7 X8 *)
  0xd280000b;       (* arm_MOV X11 (rvalue (word 0)) *)
  0x6e301e10;       (* arm_EOR_VEC Q16 Q16 Q16 128 *)
  0x3c8404f0;       (* arm_STR Q16 X7 (Postimmediate_Offset (word 64)) *)
  0x3c9d00f0;       (* arm_STR Q16 X7 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9e00f0;       (* arm_STR Q16 X7 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9f00f0;       (* arm_STR Q16 X7 (Immediate_Offset (word 18446744073709551600)) *)
  0x9100816b;       (* arm_ADD X11 X11 (rvalue (word 32)) *)
  0xf104017f;       (* arm_CMP X11 (rvalue (word 256)) *)
  0x54ffff4b;       (* arm_BLT (word 2097128) *)
  0xaa0803e7;       (* arm_MOV X7 X8 *)
  0xd2800009;       (* arm_MOV X9 (rvalue (word 0)) *)
  0xd2802004;       (* arm_MOV X4 (rvalue (word 256)) *)
  0xeb04013f;       (* arm_CMP X9 X4 *)
  0x54000482;       (* arm_BCS (word 144) *)
  0xd1002042;       (* arm_SUB X2 X2 (rvalue (word 8)) *)
  0x0cdf7020;       (* arm_LDR D0 X1 (Postimmediate_Offset (word 8)) *)
  0x0f00e5fa;       (* arm_MOVI D26 (word 1085102592571150095) *)
  0x0e3a1c1b;       (* arm_AND_VEC Q27 Q0 Q26 64 *)
  0x2f0c041c;       (* arm_USHR_VEC Q28 Q0 4 8 64 *)
  0x0e1c3b7a;       (* arm_ZIP1 Q26 Q27 Q28 8 64 *)
  0x0e1c7b7d;       (* arm_ZIP2 Q29 Q27 Q28 8 64 *)
  0x2f08a750;       (* arm_USHLL_VEC Q16 Q26 0 8 *)
  0x2f08a7b1;       (* arm_USHLL_VEC Q17 Q29 0 8 *)
  0x6e7037c4;       (* arm_CMHI_VEC Q4 Q30 Q16 16 128 *)
  0x6e7137c5;       (* arm_CMHI_VEC Q5 Q30 Q17 16 128 *)
  0x4e3f1c84;       (* arm_AND_VEC Q4 Q4 Q31 128 *)
  0x4e3f1ca5;       (* arm_AND_VEC Q5 Q5 Q31 128 *)
  0x6e703894;       (* arm_UADDLV Q20 Q4 8 16 *)
  0x6e7038b5;       (* arm_UADDLV Q21 Q5 8 16 *)
  0x1e26028c;       (* arm_FMOV_FtoI W12 Q20 0 32 *)
  0x1e2602ad;       (* arm_FMOV_FtoI W13 Q21 0 32 *)
  0x3cec7878;       (* arm_LDR Q24 X3 (Shiftreg_Offset X12 4) *)
  0x3ced7879;       (* arm_LDR Q25 X3 (Shiftreg_Offset X13 4) *)
  0x4e205884;       (* arm_CNT Q4 Q4 128 *)
  0x4e2058a5;       (* arm_CNT Q5 Q5 128 *)
  0x6e703894;       (* arm_UADDLV Q20 Q4 8 16 *)
  0x6e7038b5;       (* arm_UADDLV Q21 Q5 8 16 *)
  0x1e26028c;       (* arm_FMOV_FtoI W12 Q20 0 32 *)
  0x1e2602ad;       (* arm_FMOV_FtoI W13 Q21 0 32 *)
  0x4e180210;       (* arm_TBL Q16 [Q16] Q24 128 *)
  0x4e190231;       (* arm_TBL Q17 [Q17] Q25 128 *)
  0x4c0074f0;       (* arm_STR Q16 X7 No_Offset *)
  0x8b0c04e7;       (* arm_ADD X7 X7 (Shiftedreg X12 LSL 1) *)
  0x4c0074f1;       (* arm_STR Q17 X7 No_Offset *)
  0x8b0d04e7;       (* arm_ADD X7 X7 (Shiftedreg X13 LSL 1) *)
  0x8b0d018c;       (* arm_ADD X12 X12 X13 *)
  0x8b0c0129;       (* arm_ADD X9 X9 X12 *)
  0xf100205f;       (* arm_CMP X2 (rvalue (word 8)) *)
  0x54fffb82;       (* arm_BCS (word 2097008) *)
  0xeb04013f;       (* arm_CMP X9 X4 *)
  0x9a843129;       (* arm_CSEL X9 X9 X4 Condition_CC *)
  0xd280000b;       (* arm_MOV X11 (rvalue (word 0)) *)
  0xaa0803e7;       (* arm_MOV X7 X8 *)
  0x3cc204f0;       (* arm_LDR Q16 X7 (Postimmediate_Offset (word 32)) *)
  0x3cdf00f2;       (* arm_LDR Q18 X7 (Immediate_Offset (word 18446744073709551600)) *)
  0x6e7084f0;       (* arm_SUB_VEC Q16 Q7 Q16 16 128 *)
  0x6e7284f2;       (* arm_SUB_VEC Q18 Q7 Q18 16 128 *)
  0x4f10a611;       (* arm_SSHLL2_VEC Q17 Q16 0 16 *)
  0x0f10a610;       (* arm_SSHLL_VEC Q16 Q16 0 16 *)
  0x4f10a653;       (* arm_SSHLL2_VEC Q19 Q18 0 16 *)
  0x0f10a652;       (* arm_SSHLL_VEC Q18 Q18 0 16 *)
  0x3c840410;       (* arm_STR Q16 X0 (Postimmediate_Offset (word 64)) *)
  0x3c9d0011;       (* arm_STR Q17 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9e0012;       (* arm_STR Q18 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9f0013;       (* arm_STR Q19 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x9100416b;       (* arm_ADD X11 X11 (rvalue (word 16)) *)
  0xf104017f;       (* arm_CMP X11 (rvalue (word 256)) *)
  0x54fffe4b;       (* arm_BLT (word 2097096) *)
  0xaa0903e0;       (* arm_MOV X0 X9 *)
  0x910903ff;       (* arm_ADD SP SP (rvalue (word 576)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLDSA_REJ_UNIFORM_ETA4_EXEC = ARM_MK_EXEC_RULE mldsa_rej_uniform_eta4_mc;;

let LENGTH_MLDSA_REJ_UNIFORM_ETA4_MC =
  REWRITE_CONV[mldsa_rej_uniform_eta4_mc] `LENGTH mldsa_rej_uniform_eta4_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

(* Named preamble/postamble lengths and core-loop pc range. The preamble is *)
(* one MOV setting up the eta-table sentinel constant in W4; the postamble  *)
(* is MOV X0,X9 + ADD SP,SP,#576 + RET. *)
let MLDSA_REJ_UNIFORM_ETA4_PREAMBLE_LENGTH = new_definition
  `MLDSA_REJ_UNIFORM_ETA4_PREAMBLE_LENGTH = 4`;;

let MLDSA_REJ_UNIFORM_ETA4_POSTAMBLE_LENGTH = new_definition
  `MLDSA_REJ_UNIFORM_ETA4_POSTAMBLE_LENGTH = 8`;;

let MLDSA_REJ_UNIFORM_ETA4_CORE_START = new_definition
  `MLDSA_REJ_UNIFORM_ETA4_CORE_START = MLDSA_REJ_UNIFORM_ETA4_PREAMBLE_LENGTH`;;

let MLDSA_REJ_UNIFORM_ETA4_CORE_END = new_definition
  `MLDSA_REJ_UNIFORM_ETA4_CORE_END =
   LENGTH mldsa_rej_uniform_eta4_mc - MLDSA_REJ_UNIFORM_ETA4_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLDSA_REJ_UNIFORM_ETA4_MC;
               MLDSA_REJ_UNIFORM_ETA4_CORE_START;
               MLDSA_REJ_UNIFORM_ETA4_CORE_END;
               MLDSA_REJ_UNIFORM_ETA4_PREAMBLE_LENGTH;
               MLDSA_REJ_UNIFORM_ETA4_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

(* ------------------------------------------------------------------------- *)
(* Supporting lemmas.                                                        *)
(*                                                                           *)
(* The public spec REJ_SAMPLE_ETA4 (in common/mldsa_specs.ml) takes a       *)
(* nibble list. The proof below is naturally written against the byte-list  *)
(* shape, since the loop invariant peels off 8 bytes / 16 nibbles per       *)
(* iteration, so we introduce private byte-shape aliases below and bridge   *)
(* to the public spec at the subroutine spec.                               *)
(* ------------------------------------------------------------------------- *)

let REJ_NIBBLES_ETA4 = define
  `REJ_NIBBLES_ETA4 (l:byte list) =
   FILTER (\x:int16. val x < 9) (NIBBLES_OF_BYTES l)`;;

let REJ_SAMPLE_ETA4_BYTES = define
  `REJ_SAMPLE_ETA4_BYTES (l:byte list) =
   MAP (\x:int16. word_sx(word_sub (word 4:int16) x):int32)
       (REJ_NIBBLES_ETA4 l)`;;

(* Bridge: byte-shape composition equals the public nibble-list spec        *)
(* applied to BYTES_TO_NIBBLES. Used only at the subroutine-spec boundary.  *)
let REJ_SAMPLE_ETA4_BYTES_EQ = prove
 (`!l:byte list. REJ_SAMPLE_ETA4_BYTES l =
                 REJ_SAMPLE_ETA4 (BYTES_TO_NIBBLES l)`,
  GEN_TAC THEN
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; REJ_NIBBLES_ETA4; REJ_SAMPLE_ETA4;
              NIBBLES_OF_BYTES_EQ_BYTES_TO_NIBBLES] THEN
  REWRITE_TAC[FILTER_MAP; o_DEF; GSYM MAP_o] THEN
  (* Reduce val(word_zx x:int16) to val x in the FILTER predicate. *)
  SUBGOAL_THEN `!x:4 word. val (word_zx x:int16) = val x`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC VAL_WORD_ZX THEN
    REWRITE_TAC[DIMINDEX_4; DIMINDEX_16] THEN ARITH_TAC;
    ALL_TAC] THEN
  (* Per-element equivalence between the int16-stored and native (4 word)   *)
  (* forms, gated by the val<9 filter predicate.                             *)
  SPEC_TAC(`BYTES_TO_NIBBLES (l:byte list)`,`xs:(4 word) list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM(K ALL_TAC) THEN
  BITBLAST_TAC);;

let REJ_NIBBLES_ETA4_EMPTY = prove
 (`REJ_NIBBLES_ETA4 [] = []`,
  REWRITE_TAC[REJ_NIBBLES_ETA4; NIBBLES_OF_BYTES; FILTER]);;

let REJ_NIBBLES_ETA4_APPEND = prove
 (`!l1 l2. REJ_NIBBLES_ETA4(APPEND l1 l2) =
           APPEND (REJ_NIBBLES_ETA4 l1) (REJ_NIBBLES_ETA4 l2)`,
  REWRITE_TAC[REJ_NIBBLES_ETA4; NIBBLES_OF_BYTES_APPEND; FILTER_APPEND]);;

let REJ_NIBBLES_ETA4_STEP = prove
 (`!inlist:byte list. !i:num.
   8 * (i + 1) <= LENGTH inlist
   ==> REJ_NIBBLES_ETA4(SUB_LIST(0, 8 * (i + 1)) inlist) =
       APPEND (REJ_NIBBLES_ETA4(SUB_LIST(0, 8 * i) inlist))
              (REJ_NIBBLES_ETA4(SUB_LIST(8 * i, 8) inlist))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REJ_NIBBLES_ETA4_APPEND] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `8 * (i + 1) = 0 + 8 * i + 8` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUB_LIST_SPLIT; SUB_LIST_CLAUSES; APPEND; ADD_CLAUSES]);;

(* FILTER length = sum of bitvals for 8 elements *)
let FILTER_LENGTH_BITVAL = prove(
  `!a b c d e f g h:int16.
   LENGTH(FILTER (\x:int16. val x < 9) [a;b;c;d;e;f;g;h]) =
   bitval(val a < 9) + bitval(val b < 9) + bitval(val c < 9) +
   bitval(val d < 9) + bitval(val e < 9) + bitval(val f < 9) +
   bitval(val g < 9) + bitval(val h < 9)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FILTER] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; bitval]) THEN
  ARITH_TAC);;

let REJ_NIBBLES_COUNT_4 = prove
 (`!b0 b1 b2 b3:byte.
   LENGTH(FILTER (\x:int16. val x < 9) (NIBBLES_OF_BYTES [b0;b1;b2;b3])) =
   bitval(val b0 MOD 16 < 9) + bitval(val b0 DIV 16 < 9) +
   bitval(val b1 MOD 16 < 9) + bitval(val b1 DIV 16 < 9) +
   bitval(val b2 MOD 16 < 9) + bitval(val b2 DIV 16 < 9) +
   bitval(val b3 MOD 16 < 9) + bitval(val b3 DIV 16 < 9)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NIBBLES_OF_BYTES_4] THEN
  REWRITE_TAC[ISPECL [`word(val(b0:byte) MOD 16):int16`;
    `word(val(b0:byte) DIV 16):int16`;
    `word(val(b1:byte) MOD 16):int16`;
    `word(val(b1:byte) DIV 16):int16`;
    `word(val(b2:byte) MOD 16):int16`;
    `word(val(b2:byte) DIV 16):int16`;
    `word(val(b3:byte) MOD 16):int16`;
    `word(val(b3:byte) DIV 16):int16`] FILTER_LENGTH_BITVAL] THEN
  REWRITE_TAC[VAL_WORD_NIBBLE_LT]);;

let LENGTH_REJ_NIBBLES_ETA4 = prove
 (`!l:byte list. LENGTH(REJ_NIBBLES_ETA4 l) <= 2 * LENGTH l`,
  GEN_TAC THEN REWRITE_TAC[REJ_NIBBLES_ETA4] THEN
  TRANS_TAC LE_TRANS `LENGTH(NIBBLES_OF_BYTES l:int16 list)` THEN
  CONJ_TAC THENL [REWRITE_TAC[LENGTH_FILTER]; ALL_TAC] THEN
  SPEC_TAC(`l:byte list`,`l:byte list`) THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[NIBBLES_OF_BYTES; LENGTH; NIBBLE_PAIR;
                  APPEND; LENGTH_APPEND; LE_0] THEN
  UNDISCH_TAC `LENGTH(NIBBLES_OF_BYTES t:int16 list) <=
               2 * LENGTH(t:byte list)` THEN ARITH_TAC);;

let NIBLEN_BOUND_FROM_WOP = prove
 (`!inlist:byte list. !N.
   0 < N /\
   (!m. m < N ==> 8 * (m + 1) <= LENGTH inlist /\
        LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,8*m) inlist)) < 256)
   ==> LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,8*N) inlist):int16 list) < 272`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN
  ASM_REWRITE_TAC[ARITH_RULE `N - 1 < N <=> 0 < N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `8 * N = 0 + 8 * (N - 1) + 8` SUBST1_TAC THENL
   [UNDISCH_TAC `0 < N` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUB_LIST_SPLIT; SUB_LIST_CLAUSES; APPEND; ADD_CLAUSES] THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND] THEN
  MP_TAC(ISPEC `SUB_LIST(8*(N-1),8) inlist:byte list`
    LENGTH_REJ_NIBBLES_ETA4) THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN
  UNDISCH_TAC
   `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,8*(N-1)) inlist):int16 list) < 256` THEN
  ARITH_TAC);;

let COUNT_BRIDGE_ABSTRACT_4 = prove(
  `!x0:int128. !b0 b1 b2 b3:byte.
      word_subword x0 (0,16):int16 = word_zx(word_and b0 (word 15):byte):int16 /\
      word_subword x0 (16,16):int16 = word_zx(word_ushr b0 4:byte):int16 /\
      word_subword x0 (32,16):int16 = word_zx(word_and b1 (word 15):byte):int16 /\
      word_subword x0 (48,16):int16 = word_zx(word_ushr b1 4:byte):int16 /\
      word_subword x0 (64,16):int16 = word_zx(word_and b2 (word 15):byte):int16 /\
      word_subword x0 (80,16):int16 = word_zx(word_ushr b2 4:byte):int16 /\
      word_subword x0 (96,16):int16 = word_zx(word_and b3 (word 15):byte):int16 /\
      word_subword x0 (112,16):int16 = word_zx(word_ushr b3 4:byte):int16
      ==>
      bitval(val(word_subword x0 (0,16):int16) < 9) +
      bitval(val(word_subword x0 (16,16):int16) < 9) +
      bitval(val(word_subword x0 (32,16):int16) < 9) +
      bitval(val(word_subword x0 (48,16):int16) < 9) +
      bitval(val(word_subword x0 (64,16):int16) < 9) +
      bitval(val(word_subword x0 (80,16):int16) < 9) +
      bitval(val(word_subword x0 (96,16):int16) < 9) +
      bitval(val(word_subword x0 (112,16):int16) < 9) =
      LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3])`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4; REJ_NIBBLES_COUNT_4] THEN
  REWRITE_TAC[VAL_WORD_ZX_BYTE16; BYTE_AND_15_MOD; BYTE_USHR4_DIV] THEN
  ARITH_TAC);;

let REJ_NIBBLES_ETA4_LENGTH_4 = prove
 (`!b0 b1 b2 b3:byte.
     LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3]:int16 list) <= 8`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REJ_NIBBLES_ETA4] THEN
  W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
  REWRITE_TAC[NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND; LENGTH] THEN
  ARITH_TAC);;

let REJ_SAMPLE_ETA4_SUB_LIST_PREFIX = prove
 (`!k (l:byte list).
     k <= LENGTH l
     ==> ?rest:int32 list.
         APPEND (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,k) l)) rest =
         REJ_SAMPLE_ETA4_BYTES l`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `REJ_SAMPLE_ETA4_BYTES (SUB_LIST(k, LENGTH l - k) l):int32 list` THEN
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; GSYM MAP_APPEND] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4; GSYM FILTER_APPEND] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[GSYM NIBBLES_OF_BYTES_APPEND] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`l:byte list`; `k:num`] SUB_LIST_TOPSPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  REFL_TAC);;

let SUB_LIST_256_PREFIX_LARGE = prove
 (`!inlist:byte list. !nn:num.
     256 <= LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 8*nn) inlist):int16 list)
     ==>
     SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist) =
     SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES (SUB_LIST(0, 8*nn) inlist))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `8 * nn <= LENGTH(inlist:byte list)` THENL
   [MP_TAC(ISPECL [`8 * nn:num`; `inlist:byte list`]
                REJ_SAMPLE_ETA4_SUB_LIST_PREFIX) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `rest:int32 list` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th])) THEN
    MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN
    REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; LENGTH_MAP] THEN ASM_REWRITE_TAC[];

    SUBGOAL_THEN `SUB_LIST(0, 8 * nn) (inlist:byte list) = inlist` SUBST1_TAC THENL
     [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_ARITH_TAC;
      REFL_TAC]]);;

(* canonical word(num_of_wordlist [4 int32s]) form. *)

let SSHLL_CHUNK_WORD_SUBWORD_LO_INT64 = BITBLAST_RULE
 `word_subword
  (word_join
   (word_join
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword (c:int128) (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (48,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (32,16):int16):int32) 0):int64)
   (word_join
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (16,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (0,16):int16):int32) 0):int64):int128) (0,64):int64 =
  word_join (word_sx(word_sub (word 4:int16) (word_subword c (16,16):int16)):int32)
            (word_sx(word_sub (word 4:int16) (word_subword c (0,16):int16)):int32):int64`;;

let SSHLL_CHUNK_WORD_SUBWORD_HI_INT64 = BITBLAST_RULE
 `word_subword
  (word_join
   (word_join
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword (c:int128) (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (48,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (32,16):int16):int32) 0):int64)
   (word_join
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (16,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (0,64):int64) (0,16):int16):int32) 0):int64):int128) (64,64):int64 =
  word_join (word_sx(word_sub (word 4:int16) (word_subword c (48,16):int16)):int32)
            (word_sx(word_sub (word 4:int16) (word_subword c (32,16):int16)):int32):int64`;;

let SSHLL_CHUNK_WORD_SUBWORD_LO_INT64_HIINNER = BITBLAST_RULE
 `word_subword
  (word_join
   (word_join
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword (c:int128) (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (48,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (32,16):int16):int32) 0):int64)
   (word_join
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (16,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (0,16):int16):int32) 0):int64):int128) (0,64):int64 =
  word_join (word_sx(word_sub (word 4:int16) (word_subword c (80,16):int16)):int32)
            (word_sx(word_sub (word 4:int16) (word_subword c (64,16):int16)):int32):int64`;;

let BIGNUM_LIST_OF_SEQ_EQ_NUM_SUB_LIST =
  ISPEC `\x:int16. word_sx (word_sub (word 4:int16) x):int32`
        BIGNUM_LIST_OF_SEQ_EQ_NUM_SUB_LIST_POLY;;

let PAIR_MAP_IDX_128 =
  let pairs_str = String.concat ";\n      "
    (List.map (fun k ->
       Printf.sprintf
         "word_join (word_sx (word_sub (word 4:int16) (EL %d l)):int32) (word_sx (word_sub (word 4:int16) (EL %d l)):int32)"
         (2*k+1) (2*k)) (0--127)) in
  let goal_str = Printf.sprintf
    "!l:int16 list. 256 <= LENGTH l ==> \
     bignum_of_wordlist [%s] = \
     num_of_wordlist (MAP (\\x:int16. word_sx (word_sub (word 4) x):int32) (SUB_LIST (0,256) l))"
    pairs_str in
  prove
   (parse_term goal_str,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ_NUM_OF_WORDLIST] THEN
    SUBGOAL_THEN `[]:int64 list = pair_wordlist ([]:int32 list)` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
     [REWRITE_TAC[pair_wordlist]; ALL_TAC] THEN
    REWRITE_TAC[GSYM(el 0 (CONJUNCTS pair_wordlist))] THEN
    REWRITE_TAC[NUM_OF_PAIR_WORDLIST] THEN
    MP_TAC(ISPECL [`256`; `l:int16 list`] SUB_LIST_EQ_LIST_OF_SEQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    CONV_TAC(RAND_CONV(RAND_CONV(RAND_CONV LIST_OF_SEQ_CONV))) THEN
    REWRITE_TAC[MAP]);;

let SSHLL_CHUNK_WORD_SUBWORD_HI_INT64_HIINNER = BITBLAST_RULE
 `word_subword
  (word_join
   (word_join
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword (c:int128) (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (48,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (32,16):int16):int32) 0):int64)
   (word_join
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (16,16):int16):int32) 0)
    (word_shl (word_sx (word_subword (word_subword
      (word_join (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (112,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (96,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (80,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (64,16):int16):int16):int32):int64)
       (word_join (word_join
         (word_sub (word 4:int16) (word_subword c (48,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (32,16):int16):int16):int32)
        (word_join (word_sub (word 4:int16) (word_subword c (16,16):int16):int16)
         (word_sub (word 4:int16) (word_subword c (0,16):int16):int16):int32):int64)
       :int128) (64,64):int64) (0,16):int16):int32) 0):int64):int128) (64,64):int64 =
  word_join (word_sx(word_sub (word 4:int16) (word_subword c (112,16):int16)):int32)
            (word_sx(word_sub (word 4:int16) (word_subword c (96,16):int16)):int32):int64`;;

let REJ_NIBBLES_ETA4_SPLIT_8 = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7:byte.
     REJ_NIBBLES_ETA4 [b0;b1;b2;b3;b4;b5;b6;b7] =
     APPEND (REJ_NIBBLES_ETA4 [b0;b1;b2;b3])
            (REJ_NIBBLES_ETA4 [b4;b5;b6;b7]:int16 list)`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(EQT_ELIM(REWRITE_CONV[APPEND]
    `APPEND [b0:byte;b1;b2;b3] [b4;b5;b6;b7] =
     [b0;b1;b2;b3;b4;b5;b6;b7]`))) THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4_APPEND]);;

let CASE_B_TRUNCATE_L = prove
 (`!res:int64 niblen:num niblist:int16 list (L:int16 list) s:armstate.
    niblen <= 256 /\
    LENGTH niblist = niblen /\
    LENGTH L = 256 /\
    SUB_LIST(0, niblen) L = niblist /\
    read (memory :> bytes (res, 1024)) s =
    num_of_wordlist (MAP (\x:int16. word_sx(word_sub (word 4:int16) x):int32) L)
    ==>
    read (memory :> bytes (res, 4 * niblen)) s =
    num_of_wordlist (MAP (\x:int16. word_sx(word_sub (word 4:int16) x):int32) niblist)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `(\n:num. n MOD 2 EXP (8 * (4 * niblen)))`) THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD] THEN
  SUBGOAL_THEN `MIN 1024 (4 * niblen) = 4 * niblen` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `8 * 4 * niblen = dimindex(:32) * niblen` SUBST1_TAC THENL
   [REWRITE_TAC[DIMINDEX_32] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM NUM_OF_WORDLIST_SUB_LIST_0] THEN
  SUBGOAL_THEN
    `SUB_LIST(0, niblen)
       (MAP (\x:int16. word_sx(word_sub (word 4:int16) x):int32) L) =
     MAP (\x:int16. word_sx(word_sub (word 4:int16) x):int32) niblist`
    SUBST1_TAC THENL
   [REWRITE_TAC[SUB_LIST_MAP] THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(*                                                                           *)
(* Strategy: WOP-based loop count N, ENSURES_WHILE_UP_TAC over main loop,    *)
(* split computation + writeback at pc+256, then Case A (niblen>=256) and    *)
(* Case B (niblen<256) closures.                                             *)
(* ------------------------------------------------------------------------- *)


let MLDSA_REJ_UNIFORM_ETA4_CORRECT = prove
 (`!res buf buflen table (inlist:byte list) pc stackpointer.
      8 divides val buflen /\
      8 <= val buflen /\
      LENGTH inlist = val buflen /\
      ALL (nonoverlapping (stackpointer,576))
          [(word pc,LENGTH mldsa_rej_uniform_eta4_mc);
           (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (res,1024))
          [(word pc,LENGTH mldsa_rej_uniform_eta4_mc);
           (stackpointer,576)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
                read PC s = word(pc + MLDSA_REJ_UNIFORM_ETA4_CORE_START) /\
                read SP s = stackpointer /\
                C_ARGUMENTS [res;buf;buflen;table] s /\
                read(memory :> bytes(table,4096)) s =
                num_of_wordlist mldsa_rej_uniform_eta_table /\
                read(memory :> bytes(buf,val buflen)) s =
                num_of_wordlist inlist)
           (\s. read PC s = word(pc + MLDSA_REJ_UNIFORM_ETA4_CORE_END) /\
                let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES inlist) in
                let outlen = LENGTH outlist in
                C_RETURN s = word outlen /\
                read(memory :> bytes(res,4 * outlen)) s =
                num_of_wordlist outlist)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,1024);
                       memory :> bytes(stackpointer,576)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  REWRITE_TAC[fst MLDSA_REJ_UNIFORM_ETA4_EXEC;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    C_ARGUMENTS; ALL; C_RETURN] THEN
 MAP_EVERY X_GEN_TAC [`res:int64`; `buf:int64`] THEN
 W64_GEN_TAC `buflen:num` THEN
 MAP_EVERY X_GEN_TAC
  [`table:int64`; `inlist:byte list`; `pc:num`; `stackpointer:int64`] THEN
 DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

 ENSURES_SEQUENCE_TAC `pc + 256`
  `\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
       read PC s = word(pc + 256) /\
       read X0 s = res /\ read X4 s = word 256 /\
       read X8 s = stackpointer /\
       read Q7 s = word 20769504351625144638033088116686852 /\
       ALL (nonoverlapping (res,1024)) [(word pc,344); (stackpointer,576)] /\
       ?n. let niblist = REJ_NIBBLES_ETA4(SUB_LIST(0,8*n) inlist) in
           let niblen = LENGTH niblist in
           niblen < 272 /\
           (buflen < 8 * (n + 1) \/ 256 <= niblen) /\
           read X9 s = word niblen /\
           read (memory :> bytes (stackpointer,2 * niblen)) s =
           num_of_wordlist niblist` THEN
 CONJ_TAC THENL
  [ALL_TAC;

   ENSURES_INIT_TAC "s0" THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `nn:num` MP_TAC) THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ABBREV_TAC `niblist = REJ_NIBBLES_ETA4
     (SUB_LIST(0,8*nn) inlist):int16 list` THEN
   ABBREV_TAC `niblen = LENGTH(niblist:int16 list)` THEN
   DISCH_THEN(fun th ->
     MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
   SUBGOAL_THEN `val(word niblen:int64) = niblen` ASSUME_TAC THENL
    [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
     UNDISCH_TAC `niblen < 272` THEN ARITH_TAC; ALL_TAC] THEN
   BIGNUM_LDIGITIZE_TAC "b_"
     `read (memory :> bytes(stackpointer,8 * 64)) s0` THEN
   MEMORY_128_FROM_64_TAC "stackpointer" 0 32 THEN
   ASM_REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--245) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN
     `LENGTH(SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist):int32 list) =
      MIN 256 niblen`
   ASSUME_TAC THENL
    [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN
     FIRST_X_ASSUM DISJ_CASES_TAC THENL
      [(* Case A: buflen < 8*(nn+1). Together with 8 divides buflen,
          forces either 8*nn = buflen (SUB_LIST = inlist) or 8*nn > buflen
          (also SUB_LIST = inlist). Either way niblist = REJ_NIBBLES_ETA4 inlist. *)
       SUBGOAL_THEN `SUB_LIST(0, 8 * nn) (inlist:byte list) = inlist`
         SUBST_ALL_TAC THENL
        [MATCH_MP_TAC SUB_LIST_REFL THEN
         UNDISCH_TAC `8 divides buflen` THEN REWRITE_TAC[divides] THEN
         DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
         UNDISCH_TAC `LENGTH(inlist:byte list) = 8 * k` THEN
         DISCH_THEN SUBST1_TAC THEN
         REWRITE_TAC[LE_MULT_LCANCEL] THEN
         UNDISCH_TAC `8 * k < 8 * (nn + 1)` THEN
         REWRITE_TAC[LT_MULT_LCANCEL] THEN ARITH_TAC;
         ALL_TAC] THEN
       SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = niblen`
         SUBST1_TAC THENL
        [REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; LENGTH_MAP] THEN ASM_REWRITE_TAC[];
         REFL_TAC];

       ASM_CASES_TAC `8 * nn <= LENGTH(inlist:byte list)` THENL
        [(* 8*nn <= buflen: prefix lemma gives APPEND niblist rest = REJ_SAMPLE *)
         MP_TAC(ISPECL [`8 * nn`; `inlist:byte list`]
                REJ_SAMPLE_ETA4_SUB_LIST_PREFIX) THEN
         ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
         DISCH_THEN(X_CHOOSE_THEN `rest:int32 list` ASSUME_TAC) THEN
         SUBGOAL_THEN
           `LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) =
            niblen + LENGTH(rest:int32 list)`
          SUBST1_TAC THENL
          [FIRST_X_ASSUM(fun th ->
             GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[SYM th]) THEN
           REWRITE_TAC[LENGTH_APPEND; REJ_SAMPLE_ETA4_BYTES; LENGTH_MAP] THEN
           ASM_REWRITE_TAC[];
           ALL_TAC] THEN
         UNDISCH_TAC `256 <= niblen` THEN ARITH_TAC;

         SUBGOAL_THEN `SUB_LIST(0, 8 * nn) (inlist:byte list) = inlist`
           SUBST_ALL_TAC THENL
          [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_ARITH_TAC;
           ALL_TAC] THEN
         SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = niblen`
           SUBST1_TAC THENL
          [REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; LENGTH_MAP] THEN ASM_REWRITE_TAC[];
           REFL_TAC]]]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
    [(* Conjunct 1: word(MIN 256 niblen) = if niblen < 256 then word niblen else word 256 *)
     COND_CASES_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;

     FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC) THENL
      [(* Case B: buflen < 8*(nn+1). SUB_LIST(0, 8*nn) inlist = inlist,
          so niblist = REJ_NIBBLES_ETA4 inlist. *)
       SUBGOAL_THEN `SUB_LIST(0, 8 * nn) (inlist:byte list) = inlist`
         ASSUME_TAC THENL
        [MATCH_MP_TAC SUB_LIST_8nn_INLIST THEN EXISTS_TAC `buflen:num` THEN
         ASM_REWRITE_TAC[];
         ALL_TAC] THEN

       SUBGOAL_THEN
        `REJ_SAMPLE_ETA4_BYTES (inlist:byte list) =
         MAP (\x. word_sx(word_sub (word 4:int16) x):int32) niblist`
       ASSUME_TAC THENL
        [REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES] THEN AP_TERM_TAC THEN
         UNDISCH_TAC
           `REJ_NIBBLES_ETA4 (SUB_LIST(0,8 * nn) (inlist:byte list)) =
            (niblist:int16 list)` THEN
         ASM_REWRITE_TAC[];
         ALL_TAC] THEN

       ASM_CASES_TAC `256 <= niblen` THENL
        [(* niblen >= 256 sub-branch: reuses Case A closure verbatim.        *)
         SUBGOAL_THEN `MIN 256 niblen = 256` SUBST1_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
         REWRITE_TAC[ARITH_RULE `4 * 256 = 1024`] THEN
         SUBGOAL_THEN
          `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES (inlist:byte list)) =
           SUB_LIST(0,256)(MAP (\x. word_sx(word_sub (word 4:int16) x):int32)
                             (niblist:int16 list))`
         SUBST1_TAC THENL
          [ASM_REWRITE_TAC[];
           ALL_TAC] THEN
         REWRITE_TAC[SUB_LIST_MAP] THEN
         SUBGOAL_THEN
           `SUB_LIST(0, 256) (niblist:int16 list) = STACK_CONTENT niblist`
         SUBST1_TAC THENL
          [CONV_TAC SYM_CONV THEN MATCH_MP_TAC STACK_CONTENT_LARGE THEN
           UNDISCH_TAC `LENGTH(niblist:int16 list) = niblen` THEN
           DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
           ALL_TAC] THEN
         MP_TAC(GEN `k:num` (ISPECL [`s245:armstate`; `stackpointer:int64`;
                                      `niblist:int16 list`; `k:num`]
                                     BK_FROM_STACK_GE256)) THEN
         ASM_REWRITE_TAC[] THEN
         DISCH_THEN(fun bk_univ ->
           MAP_EVERY (fun i ->
             let inst = SPEC (mk_small_numeral i) bk_univ in
             let premise = EQT_ELIM (NUM_LT_CONV (lhand(concl inst))) in
             ASSUME_TAC (MP inst premise)) (0--63)) THEN
         RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV)) THEN
         RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
         (fun (asl, _ as gl) ->
           let bk_trans_thms = List.filter_map (fun (_, th) ->
             let c = concl th in
             if is_eq c then
               let rhs = rand c in
               if is_var rhs && String.length (fst (dest_var rhs)) >= 2 &&
                  String.sub (fst (dest_var rhs)) 0 2 = "b_" then
                 let lhs = lhand c in
                 let bk_fact = List.find_opt (fun (_, th2) ->
                   let c2 = concl th2 in
                   is_eq c2 && lhs = lhand c2 && rhs <> rand c2) asl in
                 (match bk_fact with
                  | Some (_, bk_th) -> Some (TRANS (SYM th) bk_th)
                  | None -> None)
               else None
             else None) asl in
           MAP_EVERY ASSUME_TAC bk_trans_thms gl) THEN
         REWRITE_TAC[ARITH_RULE `1024 = 8 * 128`] THEN
         CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
         RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(READ_MEMORY_SPLIT_CONV 1))) THEN
         ASM_REWRITE_TAC[] THEN
         REWRITE_TAC[SSHLL_CHUNK_WORD_SUBWORD_LO_INT64;
                     SSHLL_CHUNK_WORD_SUBWORD_HI_INT64;
                     SSHLL_CHUNK_WORD_SUBWORD_LO_INT64_HIINNER;
                     SSHLL_CHUNK_WORD_SUBWORD_HI_INT64_HIINNER] THEN
         SUBGOAL_THEN `256 <= LENGTH (niblist:int16 list)` ASSUME_TAC THENL
          [UNDISCH_TAC `LENGTH(niblist:int16 list) = niblen` THEN
           DISCH_THEN SUBST1_TAC THEN
           UNDISCH_TAC `256 <= niblen` THEN REWRITE_TAC[];
           ALL_TAC] THEN
         MP_TAC(GEN `a:num` (ISPECL [`niblist:int16 list`; `a:num`]
                                    WORD_SUBWORD_JOIN_SUB_LIST_H)) THEN
         DISCH_THEN(fun univ_th ->
           MAP_EVERY (fun i ->
             let inst = SPEC (mk_small_numeral i) univ_th in
             let prem_term = lhand(concl inst) in
             let prem_thm = ARITH_RULE(mk_imp(
               `256 <= LENGTH (niblist:int16 list)`, prem_term)) in
             let raw = MATCH_MP inst
               (MP prem_thm (ASSUME `256 <= LENGTH (niblist:int16 list)`)) in
             let discharged = CONV_RULE (REWRITE_CONV[ARITH]) raw in
             REWRITE_TAC[discharged])
             (List.map (fun k -> 8 * k) (0--31))) THEN
         SUBGOAL_THEN `STACK_CONTENT (niblist:int16 list) = SUB_LIST(0, 256) niblist`
           SUBST1_TAC THENL
          [MATCH_MP_TAC STACK_CONTENT_LARGE THEN ASM_REWRITE_TAC[];
           ALL_TAC] THEN
         MP_TAC(ISPECL
           [`128`;
            `MAP (\x. word_sx (word_sub (word 4:int16) x):int32)
                 (SUB_LIST(0, 256) (niblist:int16 list))`]
           BIGNUM_WORDJOIN_PAIRS_EXISTS) THEN
         ANTS_TAC THENL
          [REWRITE_TAC[LENGTH_MAP; LENGTH_SUB_LIST] THEN
           UNDISCH_TAC `256 <= LENGTH (niblist:int16 list)` THEN ARITH_TAC;
           ALL_TAC] THEN
         DISCH_THEN(X_CHOOSE_THEN `pairs:int64 list` STRIP_ASSUME_TAC) THEN
         MP_TAC(ISPECL [`niblist:int16 list`; `128`]
                       BIGNUM_LIST_OF_SEQ_EQ_NUM_SUB_LIST) THEN
         ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
         REWRITE_TAC[ARITH_RULE `2 * 128 = 256`] THEN
         DISCH_THEN(SUBST1_TAC o SYM) THEN
         AP_TERM_TAC THEN
         CONV_TAC SYM_CONV THEN
         CONV_TAC(LAND_CONV (
           REWRITE_CONV (list_of_seq :: APPEND ::
             List.map (fun k -> num_CONV (mk_small_numeral k)) (1--128))
           THENC TOP_DEPTH_CONV BETA_CONV
           THENC NUM_REDUCE_CONV)) THEN
         REFL_TAC;

         SUBGOAL_THEN `niblen < 256` ASSUME_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
         SUBGOAL_THEN `MIN 256 niblen = niblen` SUBST1_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
         SUBGOAL_THEN
           `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES (inlist:byte list)) =
            MAP (\x. word_sx(word_sub (word 4:int16) x):int32) niblist`
           SUBST1_TAC THENL
          [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUB_LIST_REFL THEN
           REWRITE_TAC[LENGTH_MAP] THEN ASM_ARITH_TAC;
           ALL_TAC] THEN
         MP_TAC(ISPECL [`stackpointer:int64`; `256`; `s245:armstate`]
                       BYTES_EXISTS_WORDLIST) THEN
         REWRITE_TAC[ARITH_RULE `2 * 256 = 512`] THEN
         DISCH_THEN(X_CHOOSE_THEN `L:int16 list` STRIP_ASSUME_TAC) THEN
         SUBGOAL_THEN `SUB_LIST(0, niblen) (L:int16 list) = niblist`
           ASSUME_TAC THENL
          [MATCH_MP_TAC PREFIX_FROM_STACK THEN
           MAP_EVERY EXISTS_TAC
             [`stackpointer:int64`; `s245:armstate`] THEN
           ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
           ALL_TAC] THEN
         MATCH_MP_TAC CASE_B_TRUNCATE_L THEN
         EXISTS_TAC `L:int16 list` THEN
         ASM_REWRITE_TAC[] THEN
         CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
         SUBGOAL_THEN `256 <= LENGTH (L:int16 list)` ASSUME_TAC THENL
          [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
         MP_TAC(GEN `k:num` (ISPECL [`s245:armstate`; `stackpointer:int64`;
                                      `L:int16 list`; `k:num`]
                                     BK_FROM_STACK_GE256)) THEN
         ASM_REWRITE_TAC[ARITH_RULE `2 * 256 = 512`] THEN
         DISCH_THEN(fun bk_univ ->
           MAP_EVERY (fun i ->
             let inst = SPEC (mk_small_numeral i) bk_univ in
             let premise = EQT_ELIM (NUM_LT_CONV (lhand(concl inst))) in
             ASSUME_TAC (MP inst premise)) (0--63)) THEN
         RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV)) THEN
         RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
         (fun (asl, _ as gl) ->
           let bk_trans_thms = List.filter_map (fun (_, th) ->
             let c = concl th in
             if is_eq c then
               let rhs = rand c in
               if is_var rhs && String.length (fst (dest_var rhs)) >= 2 &&
                  String.sub (fst (dest_var rhs)) 0 2 = "b_" then
                 let lhs = lhand c in
                 let bk_fact = List.find_opt (fun (_, th2) ->
                   let c2 = concl th2 in
                   is_eq c2 && lhs = lhand c2 && rhs <> rand c2) asl in
                 (match bk_fact with
                  | Some (_, bk_th) -> Some (TRANS (SYM th) bk_th)
                  | None -> None)
               else None
             else None) asl in
             (List.length bk_trans_thms);
           MAP_EVERY ASSUME_TAC bk_trans_thms gl) THEN
         REWRITE_TAC[ARITH_RULE `1024 = 8 * 128`] THEN
         CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
         RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(READ_MEMORY_SPLIT_CONV 1))) THEN
         ASM_REWRITE_TAC[] THEN
         REWRITE_TAC[SSHLL_CHUNK_WORD_SUBWORD_LO_INT64;
                     SSHLL_CHUNK_WORD_SUBWORD_HI_INT64;
                     SSHLL_CHUNK_WORD_SUBWORD_LO_INT64_HIINNER;
                     SSHLL_CHUNK_WORD_SUBWORD_HI_INT64_HIINNER] THEN
         MP_TAC(GEN `a:num` (ISPECL [`L:int16 list`; `a:num`]
                                    WORD_SUBWORD_JOIN_SUB_LIST_H)) THEN
         DISCH_THEN(fun univ_th ->
           MAP_EVERY (fun i ->
             let inst = SPEC (mk_small_numeral i) univ_th in
             let prem_term = lhand(concl inst) in
             let prem_thm = ARITH_RULE(mk_imp(
               `256 <= LENGTH (L:int16 list)`, prem_term)) in
             let raw = MATCH_MP inst
               (MP prem_thm (ASSUME `256 <= LENGTH (L:int16 list)`)) in
             let discharged = CONV_RULE (REWRITE_CONV[ARITH]) raw in
             REWRITE_TAC[discharged])
             (List.map (fun k -> 8 * k) (0--31))) THEN

         SUBGOAL_THEN `SUB_LIST(0, 256) (L:int16 list) = L` SUBST1_TAC THENL
          [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_REWRITE_TAC[LE_REFL];
           ALL_TAC] THEN
         MP_TAC(SPEC `L:int16 list` PAIR_MAP_IDX_128) THEN
         ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
         SUBGOAL_THEN `SUB_LIST(0, 256) (L:int16 list) = L` SUBST1_TAC THENL
          [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_REWRITE_TAC[LE_REFL];
           DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC]];
       SUBGOAL_THEN `MIN 256 niblen = 256` SUBST1_TAC THENL
        [ASM_ARITH_TAC; ALL_TAC] THEN
       REWRITE_TAC[ARITH_RULE `4 * 256 = 1024`] THEN
       SUBGOAL_THEN
        `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES (inlist:byte list)) =
         SUB_LIST(0,256)(MAP (\x. word_sx(word_sub (word 4:int16) x):int32)
                           (niblist:int16 list))`
       SUBST1_TAC THENL
        [MP_TAC(SPECL [`inlist:byte list`; `nn:num`] SUB_LIST_256_PREFIX_LARGE) THEN
         ANTS_TAC THENL
          [(* 256 <= LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 8*nn) inlist)) *)
           UNDISCH_TAC
             `REJ_NIBBLES_ETA4 (SUB_LIST(0,8 * nn) (inlist:byte list)) =
              (niblist:int16 list)` THEN
           DISCH_THEN SUBST1_TAC THEN
           UNDISCH_TAC `LENGTH(niblist:int16 list) = niblen` THEN
           DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
           ALL_TAC] THEN
         DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
         ASM_REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES];
         ALL_TAC] THEN

       REWRITE_TAC[SUB_LIST_MAP] THEN
       SUBGOAL_THEN
         `SUB_LIST(0, 256) (niblist:int16 list) = STACK_CONTENT niblist`
       SUBST1_TAC THENL
        [CONV_TAC SYM_CONV THEN MATCH_MP_TAC STACK_CONTENT_LARGE THEN
         UNDISCH_TAC `LENGTH(niblist:int16 list) = niblen` THEN
         DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       MP_TAC(GEN `k:num` (ISPECL [`s245:armstate`; `stackpointer:int64`;
                                    `niblist:int16 list`; `k:num`]
                                   BK_FROM_STACK_GE256)) THEN
       ASM_REWRITE_TAC[] THEN
       DISCH_THEN(fun bk_univ ->
         MAP_EVERY (fun i ->
           let inst = SPEC (mk_small_numeral i) bk_univ in
           let premise = EQT_ELIM (NUM_LT_CONV (lhand(concl inst))) in
           ASSUME_TAC (MP inst premise)) (0--63)) THEN
       RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV)) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
       (fun (asl, _ as gl) ->
         let bk_trans_thms = List.filter_map (fun (_, th) ->
           let c = concl th in
           if is_eq c then
             let rhs = rand c in
             if is_var rhs && String.length (fst (dest_var rhs)) >= 2 &&
                String.sub (fst (dest_var rhs)) 0 2 = "b_" then
               let lhs = lhand c in
               let bk_fact = List.find_opt (fun (_, th2) ->
                 let c2 = concl th2 in
                 is_eq c2 && lhs = lhand c2 && rhs <> rand c2) asl in
               (match bk_fact with
                | Some (_, bk_th) ->
                  Some (TRANS (SYM th) bk_th)
                | None -> None)
             else None
           else None) asl in
           (List.length bk_trans_thms);
         MAP_EVERY ASSUME_TAC bk_trans_thms gl) THEN

       REWRITE_TAC[ARITH_RULE `1024 = 8 * 128`] THEN
       CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
       RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(READ_MEMORY_SPLIT_CONV 1))) THEN
       ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[SSHLL_CHUNK_WORD_SUBWORD_LO_INT64;
                   SSHLL_CHUNK_WORD_SUBWORD_HI_INT64;
                   SSHLL_CHUNK_WORD_SUBWORD_LO_INT64_HIINNER;
                   SSHLL_CHUNK_WORD_SUBWORD_HI_INT64_HIINNER] THEN

       SUBGOAL_THEN `256 <= LENGTH (niblist:int16 list)` ASSUME_TAC THENL
        [UNDISCH_TAC `LENGTH(niblist:int16 list) = niblen` THEN
         DISCH_THEN SUBST1_TAC THEN
         UNDISCH_TAC `256 <= niblen` THEN REWRITE_TAC[];
         ALL_TAC] THEN
       MP_TAC(GEN `a:num` (ISPECL [`niblist:int16 list`; `a:num`]
                                  WORD_SUBWORD_JOIN_SUB_LIST_H)) THEN
       DISCH_THEN(fun univ_th ->
         MAP_EVERY (fun i ->
           let inst = SPEC (mk_small_numeral i) univ_th in
           let prem_term = lhand(concl inst) in
           let prem_thm = ARITH_RULE(mk_imp(
             `256 <= LENGTH (niblist:int16 list)`, prem_term)) in
           let raw = MATCH_MP inst
             (MP prem_thm (ASSUME `256 <= LENGTH (niblist:int16 list)`)) in
           let discharged = CONV_RULE
             (REWRITE_CONV[ARITH]) raw in
           REWRITE_TAC[discharged])
           (List.map (fun k -> 8 * k) (0--31))) THEN

       SUBGOAL_THEN `STACK_CONTENT (niblist:int16 list) = SUB_LIST(0, 256) niblist`
         SUBST1_TAC THENL
        [MATCH_MP_TAC STACK_CONTENT_LARGE THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       MATCH_MP_TAC PAIR_MAP_IDX_128 THEN
       ASM_REWRITE_TAC[]]]] THEN

 SUBGOAL_THEN
  `?N. buflen < 8 * (N + 1) \/
       256 <= LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,8*N) inlist):int16 list)`
 MP_TAC THENL
  [EXISTS_TAC `buflen:num` THEN DISJ1_TAC THEN ARITH_TAC;
   GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
 DISCH_THEN(X_CHOOSE_THEN `N:num`
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
 REWRITE_TAC[DE_MORGAN_THM; NOT_LT; NOT_LE] THEN STRIP_TAC THEN

 SUBGOAL_THEN `0 < N` ASSUME_TAC THENL
  [(* ASM_ARITH_TAC times out on many irrelevant hyps; use MP_TAC + ARITH *)
   MP_TAC(ASSUME `buflen < 8 * (N + 1) \/
     256 <= LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,8*N) inlist):int16 list)`) THEN
   UNDISCH_TAC `8 <= buflen` THEN
   STRUCT_CASES_TAC (ARITH_RULE `N = 0 \/ 0 < N`) THEN
   ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES;
                   REJ_NIBBLES_ETA4_EMPTY; LENGTH] THEN
   ARITH_TAC;
   ALL_TAC] THEN

 ENSURES_WHILE_UP_TAC `N:num` `pc + 108` `pc + 248`
  `\i s. read (memory :> bytes (table,4096)) s =
         num_of_wordlist mldsa_rej_uniform_eta_table /\
         read (memory :> bytes (buf,buflen)) s = num_of_wordlist inlist /\
         aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
         read Q7 s = word 20769504351625144638033088116686852 /\
         read Q30 s = word 46731384791156575435574448262545417 /\
         read Q31 s = word 664619068533544770747334646890102785 /\
         let niblist = REJ_NIBBLES_ETA4(SUB_LIST(0,8 * i) inlist) in
         let niblen = LENGTH niblist in
         read X0 s = res /\
         read X1 s = word_add buf (word(8 * i)) /\
         read X2 s = word_sub (word buflen) (word(8 * i)) /\
         read X3 s = table /\ read X4 s = word 256 /\
         read X7 s = word_add stackpointer (word(2 * niblen)) /\
         read X8 s = stackpointer /\ read X9 s = word niblen /\
         read (memory :> bytes (stackpointer,2 * niblen)) s =
         num_of_wordlist niblist` THEN
 REPEAT CONJ_TAC THENL
  [(*** Subgoal 1: 0 < N ***)
   ASM_ARITH_TAC;

   GHOST_INTRO_TAC `q31_init:int128` `read Q31` THEN
   ENSURES_INIT_TAC "s0" THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--75) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL [REWRITE_TAC[WORD_INSERT_Q31]; ALL_TAC] THEN
   REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_NIBBLES_ETA4_EMPTY] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH] THEN
   REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_SUB_0] THEN
   REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; num_of_wordlist];

   X_GEN_TAC `i:num` THEN STRIP_TAC THEN
   ABBREV_TAC `curlist = REJ_NIBBLES_ETA4(SUB_LIST(0,8 * i) inlist)` THEN
   ABBREV_TAC `curlen = LENGTH(curlist:int16 list)` THEN
   SUBGOAL_THEN `curlen < 256` ASSUME_TAC THENL
    [EXPAND_TAC "curlen" THEN EXPAND_TAC "curlist" THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
     UNDISCH_TAC `i < N:num` THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `8 * (i + 1) <= buflen` ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
     UNDISCH_TAC `i < N:num` THEN ARITH_TAC; ALL_TAC] THEN
   CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
   ASM_REWRITE_TAC[] THEN

   ENSURES_SEQUENCE_TAC `pc + 0xe0`
    `\s. read (memory :> bytes (table,4096)) s =
         num_of_wordlist mldsa_rej_uniform_eta_table /\
         read (memory :> bytes (buf,buflen)) s = num_of_wordlist (inlist:byte list) /\
         aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
         read Q7 s = word 20769504351625144638033088116686852 /\
         read Q30 s = word 46731384791156575435574448262545417 /\
         read Q31 s = word 664619068533544770747334646890102785 /\
         read X0 s = res /\
         read X1 s = word_add buf (word(8 * (i + 1))) /\
         read X2 s = word_sub (word buflen) (word(8 * (i + 1))) /\
         read X3 s = table /\ read X4 s = word 256 /\
         read X7 s = word_add stackpointer (word(2 * curlen)) /\
         read X8 s = stackpointer /\ read X9 s = word curlen /\
         read (memory :> bytes (stackpointer,2 * curlen)) s =
         num_of_wordlist (curlist:int16 list) /\
         (?lis0 lis1:int16 list.
            LENGTH lis0 <= 8 /\ LENGTH lis1 <= 8 /\
            val(read X12 s:int64) = LENGTH lis0 /\
            val(read X13 s:int64) = LENGTH lis1 /\
            APPEND lis0 lis1 =
              REJ_NIBBLES_ETA4(SUB_LIST(8 * i,8) inlist) /\
            read Q16 s = word(num_of_wordlist lis0):int128 /\
            read Q17 s = word(num_of_wordlist lis1):int128) /\
         curlen < 256 /\
         nonoverlapping (stackpointer,576) (word pc,344)` THEN
   CONJ_TAC THENL
    [(* First half: SIMD compute chain — 29 steps *)
     GHOST_INTRO_TAC `nibbles1:int128` `read Q17` THEN
     ENSURES_INIT_TAC "s0" THEN
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
     SUBGOAL_THEN `~(256 <= val(word curlen:int64))` ASSUME_TAC THENL
      [REWRITE_TAC[NOT_LE; VAL_WORD; DIMINDEX_64] THEN
       CONV_TAC NUM_REDUCE_CONV THEN
       SUBGOAL_THEN `curlen MOD 18446744073709551616 = curlen`
        SUBST1_TAC THENL
        [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `curlen < 256` THEN
         ARITH_TAC; UNDISCH_TAC `curlen < 256` THEN ARITH_TAC];
       ALL_TAC] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(256 <= val(word curlen:int64))`]) THEN

     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC [3] THEN

     ABBREV_TAC `loaded_d:int64 = read (memory :> bytes64 (word_add buf (word (8 * i)))) s3` THEN

     ARM_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (4--11) THEN
     REABBREV_TAC `nibbles0:int128 = read Q16 s11` THEN
     REABBREV_TAC `nibbles1b:int128 = read Q17 s11` THEN
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (12--19) THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
     RULE_ASSUM_TAC(REWRITE_RULE
      [word_ugt; relational2; GT; WORD_AND_MASK]) THEN
     RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
     RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
     MAP_EVERY REABBREV_TAC
      [`idx0 = read X12 s19`; `idx1 = read X13 s19`] THEN
     MAP_EVERY ABBREV_TAC
      [`tab0 = read(memory :> bytes128(word_add table
                   (word(16 * val(idx0:int64))))) s19`;
       `tab1 = read(memory :> bytes128(word_add table
                   (word(16 * val(idx1:int64))))) s19`] THEN
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (20--27) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_AND]) THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
     RULE_ASSUM_TAC(REWRITE_RULE
      [word_ugt; relational2; GT; WORD_AND_MASK]) THEN
     RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
     RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (28--29) THEN
     SUBGOAL_THEN
       `read Q16 s29 = word(num_of_wordlist
                            (REJ_NIBBLES_ETA4
                              [word_subword (loaded_d:int64) (0,8):byte;
                               word_subword loaded_d (8,8);
                               word_subword loaded_d (16,8);
                               word_subword loaded_d (24,8)])) /\
        read Q17 s29 = word(num_of_wordlist
                            (REJ_NIBBLES_ETA4
                              [word_subword (loaded_d:int64) (32,8):byte;
                               word_subword loaded_d (40,8);
                               word_subword loaded_d (48,8);
                               word_subword loaded_d (56,8)]))`
     MP_TAC THENL
      [(* Establish the 16 halfword identities inline: nibbles_k halfwords
           are word_zx of byte-nibble expressions. *)
       REWRITE_TAC[UADDLV_COUNT_LEMMA] THEN
       REWRITE_TAC(List.map (fun k -> BITBLAST_RULE
         (vsubst [mk_small_numeral k, `k:num`]
         `bit k (word_subword (word_neg (word (bitval b):16 word))
                 (0,8):8 word) <=> b`)) (0--7)) THEN
       ASM_REWRITE_TAC[] THEN
       (let prove_hw name pos byte_pos op =
          let rhs_inner = if op = "and"
            then Printf.sprintf
              "(word_and (word_subword (loaded_d:int64) (%d,8):byte) (word 15):byte)"
              byte_pos
            else Printf.sprintf
              "(word_ushr (word_subword (loaded_d:int64) (%d,8):byte) 4:byte)"
              byte_pos in
          let goal_str = Printf.sprintf
            "(word_subword (%s:int128) (%d,16)):int16 = word_zx %s :int16"
            name pos rhs_inner in
          SUBGOAL_THEN (parse_term goal_str) ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SYM o check
              (fun th -> let c = concl th in is_eq c &&
                (try fst(dest_var(rhs c)) = name with _ -> false))) THEN
            DISCH_THEN(fun th -> SUBST1_TAC th THEN ASSUME_TAC(SYM th)) THEN
            CONV_TAC WORD_BLAST;
            ALL_TAC] in
        prove_hw "nibbles0" 0 0 "and" THEN
        prove_hw "nibbles0" 16 0 "ushr" THEN
        prove_hw "nibbles0" 32 8 "and" THEN
        prove_hw "nibbles0" 48 8 "ushr" THEN
        prove_hw "nibbles0" 64 16 "and" THEN
        prove_hw "nibbles0" 80 16 "ushr" THEN
        prove_hw "nibbles0" 96 24 "and" THEN
        prove_hw "nibbles0" 112 24 "ushr" THEN
        prove_hw "nibbles1b" 0 32 "and" THEN
        prove_hw "nibbles1b" 16 32 "ushr" THEN
        prove_hw "nibbles1b" 32 40 "and" THEN
        prove_hw "nibbles1b" 48 40 "ushr" THEN
        prove_hw "nibbles1b" 64 48 "and" THEN
        prove_hw "nibbles1b" 80 48 "ushr" THEN
        prove_hw "nibbles1b" 96 56 "and" THEN
        prove_hw "nibbles1b" 112 56 "ushr") THEN
       (fun (asl, w) ->
          let halfword_hyps =
            List.filter (fun (_,th) ->
              let c = concl th in
              is_eq c &&
              (try let l = lhand c in
                   match l with
                   | Comb(Comb(Const("word_subword",_), v),
                          Comb(Comb(Const(",",_), _), len_tm)) ->
                       is_var v &&
                       (let nm = fst(dest_var v) in
                        nm = "nibbles0" || nm = "nibbles1b") &&
                       (try dest_small_numeral len_tm = 16 with _ -> false)
                   | _ -> false
               with _ -> false)) asl in
          let byte_lemmas = BYTE_SPLIT_AND @ BYTE_SPLIT_USHR in
          let new_facts = List.concat (List.map (fun (_, h) ->
            List.concat (List.map (fun lem ->
              try CONJUNCTS(MATCH_MP lem h)
              with _ -> []) byte_lemmas)) halfword_hyps) in
          (MAP_EVERY ASSUME_TAC new_facts) (asl, w)) THEN
       UNDISCH_TAC
        `read(memory :> bytes(table,4096)) s29 =
         num_of_wordlist mldsa_rej_uniform_eta_table` THEN
       REPLICATE_TAC 4
        (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
              [GSYM NUM_OF_PAIR_WORDLIST]) THEN
       REWRITE_TAC[mldsa_rej_uniform_eta_table; pair_wordlist] THEN
       CONV_TAC WORD_REDUCE_CONV THEN
       CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
       REWRITE_TAC[GSYM BYTES128_WBYTES] THEN REPEAT STRIP_TAC THEN
       DISCARD_MATCHING_ASSUMPTIONS
        [`read Q24 s = x`; `read Q25 s = x`] THEN
       REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
         (fun th -> is_var(rhs(concl th)) &&
                    let n = fst(dest_var(rhs(concl th))) in
                    n = "tab0" || n = "tab1"))) THEN
       DISCARD_MATCHING_ASSUMPTIONS
        [`read X12 s = x`; `read X13 s = x`] THEN
       REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
         (fun th -> is_var(rhs(concl th)) &&
                    let n = fst(dest_var(rhs(concl th))) in
                    n = "idx0" || n = "idx1"))) THEN
       ASM_REWRITE_TAC[] THEN
       DISCARD_MATCHING_ASSUMPTIONS
        [`read Q16 s = x`; `read Q17 s = x`] THEN
       REWRITE_TAC[REJ_NIBBLES_ETA4; NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND] THEN
       REWRITE_TAC[FILTER] THEN
       REWRITE_TAC[VAL_WORD_ZX_BYTE16; BYTE_AND_15_MOD; BYTE_USHR4_DIV;
                   VAL_WORD_NIBBLE_LT] THEN
       REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
       REWRITE_TAC[BITVAL_CLAUSES] THEN
       CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
       CONV_TAC NUM_REDUCE_CONV THEN
       REWRITE_TAC[WORD_ADD_0] THEN
       ASM_REWRITE_TAC[] THEN
       CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
       CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
       CONV_TAC NUM_REDUCE_CONV THEN
       REWRITE_TAC[num_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
       CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[BYTE_AND_15_MOD; BYTE_USHR4_DIV;
                                   VAL_WORD_ZX_BYTE16; VAL_WORD_NIBBLE_LT]) THEN
       ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
       CONV_TAC NUM_REDUCE_CONV THEN
       REWRITE_TAC[VAL_BYTE_NIB_MOD_65536] THEN
       CONV_TAC WORD_BLAST;
       STRIP_TAC] THEN
     DISCARD_MATCHING_ASSUMPTIONS
      [`read Q16 s = word_join (x:int64) (y:int64):int128`;
       `read Q17 s = word_join (x:int64) (y:int64):int128`] THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[WORD_SUBWORD_AND] THEN
     CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
     CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
     REWRITE_TAC[WORD_AND_0; WORD_POPCOUNT_0; ADD_CLAUSES] THEN
     REWRITE_TAC[POPCOUNT_AND_POWERS] THEN
     REPEAT CONJ_TAC THEN
     TRY(CONV_TAC WORD_RULE) THEN
     TRY(NONOVERLAPPING_TAC) THEN
     TRY(REWRITE_TAC[UADDLV_BOUND_LEMMA] THEN NO_TAC) THEN
     TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
     TRY(ASM_ARITH_TAC) THEN
     EXISTS_TAC
       `REJ_NIBBLES_ETA4
          [word_subword (loaded_d:int64) (0,8):byte;
           word_subword loaded_d (8,8);
           word_subword loaded_d (16,8);
           word_subword loaded_d (24,8)]` THEN
     EXISTS_TAC
       `REJ_NIBBLES_ETA4
          [word_subword (loaded_d:int64) (32,8):byte;
           word_subword loaded_d (40,8);
           word_subword loaded_d (48,8);
           word_subword loaded_d (56,8)]` THEN
     REWRITE_TAC[REJ_NIBBLES_ETA4_LENGTH_4] THEN
     MP_TAC(SPECL [`buf:int64`; `buflen:num`; `inlist:byte list`;
                   `i:num`; `s29:armstate`] SUB_LIST_8_BYTES_FROM_INT64) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
     ASM_REWRITE_TAC[REJ_NIBBLES_ETA4_SPLIT_8] THEN
     REWRITE_TAC[UADDLV_COUNT_LEMMA] THEN
     REWRITE_TAC(List.map (fun k -> BITBLAST_RULE
       (vsubst [mk_small_numeral k, `k:num`]
       `bit k (word_subword (word_neg (word (bitval b):16 word))
               (0,8):8 word) <=> b`)) (0--7)) THEN
     ASM_REWRITE_TAC[] THEN
     (let prove_hw name pos byte_pos op =
        let rhs_inner = if op = "and"
          then Printf.sprintf
            "(word_and (word_subword (loaded_d:int64) (%d,8):byte) (word 15):byte)"
            byte_pos
          else Printf.sprintf
            "(word_ushr (word_subword (loaded_d:int64) (%d,8):byte) 4:byte)"
            byte_pos in
        let goal_str = Printf.sprintf
          "(word_subword (%s:int128) (%d,16)):int16 = word_zx %s :int16"
          name pos rhs_inner in
        SUBGOAL_THEN (parse_term goal_str) ASSUME_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SYM o check
            (fun th -> let c = concl th in is_eq c &&
              (try fst(dest_var(rhs c)) = name with _ -> false))) THEN
          DISCH_THEN(fun th -> SUBST1_TAC th THEN ASSUME_TAC(SYM th)) THEN
          CONV_TAC WORD_BLAST;
          ALL_TAC] in
      prove_hw "nibbles0" 0 0 "and" THEN
      prove_hw "nibbles0" 16 0 "ushr" THEN
      prove_hw "nibbles0" 32 8 "and" THEN
      prove_hw "nibbles0" 48 8 "ushr" THEN
      prove_hw "nibbles0" 64 16 "and" THEN
      prove_hw "nibbles0" 80 16 "ushr" THEN
      prove_hw "nibbles0" 96 24 "and" THEN
      prove_hw "nibbles0" 112 24 "ushr" THEN
      prove_hw "nibbles1b" 0 32 "and" THEN
      prove_hw "nibbles1b" 16 32 "ushr" THEN
      prove_hw "nibbles1b" 32 40 "and" THEN
      prove_hw "nibbles1b" 48 40 "ushr" THEN
      prove_hw "nibbles1b" 64 48 "and" THEN
      prove_hw "nibbles1b" 80 48 "ushr" THEN
      prove_hw "nibbles1b" 96 56 "and" THEN
      prove_hw "nibbles1b" 112 56 "ushr") THEN

     REPEAT CONJ_TAC THEN
     FIRST
      [(* X12/X13 val-to-LENGTH: COUNT_BRIDGE_ABSTRACT_4 on nibbles0 *)
       MP_TAC(SPECL
        [`nibbles0:int128`;
         `word_subword (loaded_d:int64) (0,8):byte`;
         `word_subword (loaded_d:int64) (8,8):byte`;
         `word_subword (loaded_d:int64) (16,8):byte`;
         `word_subword (loaded_d:int64) (24,8):byte`] COUNT_BRIDGE_ABSTRACT_4) THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       DISCH_THEN SUBST1_TAC THEN REFL_TAC;
       MP_TAC(SPECL
        [`nibbles1b:int128`;
         `word_subword (loaded_d:int64) (32,8):byte`;
         `word_subword (loaded_d:int64) (40,8):byte`;
         `word_subword (loaded_d:int64) (48,8):byte`;
         `word_subword (loaded_d:int64) (56,8):byte`] COUNT_BRIDGE_ABSTRACT_4) THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       DISCH_THEN SUBST1_TAC THEN REFL_TAC;
       FIRST_ASSUM(fun my_hyp ->
         FIRST_ASSUM(fun arm_hyp ->
           try ACCEPT_TAC(TRANS (SYM arm_hyp) my_hyp)
           with _ -> NO_TAC))];
     ALL_TAC] THEN

   ENSURES_INIT_TAC "s0" THEN

   FIRST_X_ASSUM(X_CHOOSE_THEN `lis0:int16 list` MP_TAC o check
     (fun th -> try fst(dest_var(fst(dest_exists(concl th)))) = "lis0"
                with _ -> false)) THEN
   DISCH_THEN(X_CHOOSE_THEN `lis1:int16 list` STRIP_ASSUME_TAC) THEN
   ABBREV_TAC `len0 = LENGTH(lis0:int16 list)` THEN
   ABBREV_TAC `len1 = LENGTH(lis1:int16 list)` THEN

   SUBGOAL_THEN `val(read X12 s0:int64) = len0 /\ val(read X13 s0:int64) = len1`
     STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC [1] THEN

   SUBGOAL_THEN
    `read (memory :> bytes (stackpointer, 2 * (curlen + len0))) s1 =
     num_of_wordlist(APPEND curlist lis0:int16 list)`
   ASSUME_TAC THENL
    [REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
     SUBGOAL_THEN `LENGTH(curlist:int16 list) = curlen` ASSUME_TAC THENL
      [EXPAND_TAC "curlen" THEN REFL_TAC; ALL_TAC] THEN
     W(MP_TAC o PART_MATCH (lhand o rand)
       BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
     ANTS_TAC THENL
      [REWRITE_TAC[DIMINDEX_16] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
       ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN
     CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       SUBGOAL_THEN
        `read (memory :> bytes128
               (word_add stackpointer (word (2 * curlen)))) s1 =
         word(num_of_wordlist(lis0:int16 list)):int128`
       MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
       REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES;
                   VAL_READ_WBYTES;
                   DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
       SUBGOAL_THEN `2 * len0 = MIN 16 (2 * len0)` SUBST1_TAC THENL
        [UNDISCH_TAC `len0:num <= 8` THEN ARITH_TAC;
         REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
       DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
       REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
       MATCH_MP_TAC MOD_LT THEN
       MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
       ASM_REWRITE_TAC[DIMINDEX_16] THEN
       UNDISCH_TAC `len0:num <= 8` THEN ARITH_TAC];
     ALL_TAC] THEN
   SUBGOAL_THEN `read X12 s1:int64 = word len0` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
     CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
     UNDISCH_TAC `len0:num <= 8` THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `read X13 s1:int64 = word len1` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
     CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
     UNDISCH_TAC `len1:num <= 8` THEN ARITH_TAC; ALL_TAC] THEN
   ARM_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC "s2" THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_ADD_SHL1]) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN
    `nonoverlapping (word_add stackpointer (word(2 * (curlen + len0))):int64,
                     16) (word pc:int64, 344)`
   ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `val(word len0:int64) = len0` ASSUME_TAC THENL
    [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
     UNDISCH_TAC `len0:num <= 8` THEN ARITH_TAC; ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word len0:int64) = len0`]) THEN

   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC [3] THEN

   RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word len0:int64) = len0`]) THEN

   SUBGOAL_THEN
    `read (memory :> bytes (stackpointer, 2 * ((curlen + len0) + len1))) s3 =
     num_of_wordlist(APPEND (APPEND curlist lis0) lis1:int16 list)`
   ASSUME_TAC THENL
    [REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
     SUBGOAL_THEN
       `LENGTH(APPEND curlist lis0:int16 list) = curlen + len0`
     ASSUME_TAC THENL
      [REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     W(MP_TAC o PART_MATCH (lhand o rand)
       BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
     ANTS_TAC THENL
      [REWRITE_TAC[DIMINDEX_16] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
       ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN

     SUBGOAL_THEN
       `word_add stackpointer (word (2 * curlen + 2 * len0):int64) =
        word_add stackpointer (word (2 * (curlen + len0)))`
      (fun th -> REWRITE_TAC[th]) THENL
      [CONV_TAC WORD_RULE; ALL_TAC] THEN
     SUBGOAL_THEN `2 * curlen + 2 * len0 = 2 * (curlen + len0)`
      SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
     CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       SUBGOAL_THEN
        `read (memory :> bytes128
               (word_add stackpointer (word (2 * (curlen + len0))))) s3 =
         word(num_of_wordlist(lis1:int16 list)):int128`
       MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
       REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES;
                   VAL_READ_WBYTES;
                   DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
       SUBGOAL_THEN `2 * len1 = MIN 16 (2 * len1)` SUBST1_TAC THENL
        [UNDISCH_TAC `len1:num <= 8` THEN ARITH_TAC;
         REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
       DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
       REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
       MATCH_MP_TAC MOD_LT THEN
       MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
       ASM_REWRITE_TAC[DIMINDEX_16] THEN
       UNDISCH_TAC `len1:num <= 8` THEN ARITH_TAC];
     ALL_TAC] THEN
   ARM_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC "s4" THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_ADD_SHL1]) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (5--6) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   SUBGOAL_THEN `8 * (i + 1) <= LENGTH(inlist:byte list)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     MP_TAC(ASSUME `8 * (i + 1) <= buflen`) THEN ARITH_TAC;
     ALL_TAC] THEN
   MP_TAC(SPECL [`inlist:byte list`; `i:num`] REJ_NIBBLES_ETA4_STEP) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   ABBREV_TAC `newbatch = REJ_NIBBLES_ETA4(SUB_LIST(8*i, 8) inlist):int16 list` THEN

   SUBGOAL_THEN `APPEND (lis0:int16 list) lis1 = newbatch` ASSUME_TAC THENL
    [EXPAND_TAC "newbatch" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `LENGTH(newbatch:int16 list) = len0 + len1` ASSUME_TAC THENL
    [UNDISCH_TAC `APPEND (lis0:int16 list) lis1 = newbatch` THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN
     REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN

   SUBGOAL_THEN `val(word len0:int64) = len0 /\ val(word len1:int64) = len1`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
     REWRITE_TAC[DIMINDEX_64] THENL
      [UNDISCH_TAC `len0:num <= 8` THEN ARITH_TAC;
       UNDISCH_TAC `len1:num <= 8` THEN ARITH_TAC];
     ALL_TAC] THEN
   REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THEN
   TRY(CONV_TAC WORD_RULE) THEN
   TRY(AP_TERM_TAC THEN AP_TERM_TAC THEN
       ASM_REWRITE_TAC[] THEN ARITH_TAC) THEN
   SUBGOAL_THEN
     `2 * (curlen + len0 + len1) = 2 * ((curlen + len0) + len1)`
    SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
     `APPEND curlist (newbatch:int16 list) =
      APPEND (APPEND curlist lis0) lis1`
    SUBST1_TAC THENL
     [UNDISCH_TAC `APPEND (lis0:int16 list) lis1 = newbatch` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[APPEND_ASSOC]; ALL_TAC] THEN
   ASM_REWRITE_TAC[];

   X_GEN_TAC `i:num` THEN STRIP_TAC THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ENSURES_INIT_TAC "s0" THEN
   SUBGOAL_THEN `8 <= val(word_sub (word buflen:int64) (word(8 * i)))`
   ASSUME_TAC THENL
    [SUBGOAL_THEN `8 * (i + 1) <= buflen` ASSUME_TAC THENL
      [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
       UNDISCH_TAC `i < N:num` THEN ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `8 * i < 2 EXP 64` ASSUME_TAC THENL
      [UNDISCH_TAC `buflen < 2 EXP 64` THEN
       UNDISCH_TAC `8 * (i + 1) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
     VAL_INT64_TAC `8 * i` THEN ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
     UNDISCH_TAC `8 * (i + 1) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
   ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ABBREV_TAC `niblen = LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,8*N) inlist):int16 list)` THEN
   SUBGOAL_THEN `niblen < 272` ASSUME_TAC THENL
    [EXPAND_TAC "niblen" THEN
     MATCH_MP_TAC NIBLEN_BOUND_FROM_WOP THEN
     ASM_REWRITE_TAC[] THEN
     X_GEN_TAC `mm:num` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `mm:num`) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   VAL_INT64_TAC `niblen:num` THEN
   ASM_CASES_TAC `256 <= niblen` THENL
    [(* Case: 256 <= niblen — enough samples *)
     ASM_CASES_TAC `8 <= val(word_sub (word buflen:int64) (word(8 * N)))` THENL
      [(* Subcase: X2 >= 8 — back edge branches to pc+108, then CMP X9>=X4 *)

       ENSURES_SEQUENCE_TAC `pc + 108`
        `\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
             read PC s = word(pc + 108) /\
             read X0 s = res /\ read X4 s = word 256 /\
             read X8 s = stackpointer /\
             read Q7 s = word 20769504351625144638033088116686852 /\
             read X9 s = word niblen /\
             read (memory :> bytes (stackpointer,2 * niblen)) s =
             num_of_wordlist (REJ_NIBBLES_ETA4(SUB_LIST(0,8*N) inlist):int16 list) /\
             ALL (nonoverlapping (res,1024)) [(word pc,344); (stackpointer,576)]` THEN
       CONJ_TAC THENL
        [(* pc+248 -> pc+108: CMP X2,8; BCS back *)
         ENSURES_INIT_TAC "s0" THEN
         ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
         ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
         REWRITE_TAC[ALL] THEN ASM_REWRITE_TAC[] THEN
         CONJ_TAC THENL [NONOVERLAPPING_TAC; NONOVERLAPPING_TAC];

         ENSURES_INIT_TAC "s0" THEN
         SUBGOAL_THEN `256 <= val(word niblen:int64)` ASSUME_TAC THENL
          [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
           SUBGOAL_THEN `niblen MOD 2 EXP 64 = niblen` SUBST1_TAC THENL
            [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `niblen < 272` THEN
             ARITH_TAC;
             ASM_REWRITE_TAC[]];
           ALL_TAC] THEN
         ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
         ENSURES_FINAL_STATE_TAC THEN
         REWRITE_TAC[ALL] THEN ASM_REWRITE_TAC[] THEN
         EXISTS_TAC `N:num` THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
         UNDISCH_TAC `niblen < 272` THEN EXPAND_TAC "niblen" THEN
         ARITH_TAC];

       ENSURES_INIT_TAC "s0" THEN
       ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
       ENSURES_FINAL_STATE_TAC THEN
       REWRITE_TAC[ALL] THEN ASM_REWRITE_TAC[] THEN
       EXISTS_TAC `N:num` THEN
       CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `niblen < 272` THEN EXPAND_TAC "niblen" THEN
       ARITH_TAC];

     SUBGOAL_THEN `buflen < 8 * (N + 1)` ASSUME_TAC THENL
      [FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `~(256 <= niblen)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `8 * N <= buflen` ASSUME_TAC THENL
      [FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN
       UNDISCH_TAC `0 < N` THEN ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `8 * N = buflen` ASSUME_TAC THENL
      [MP_TAC(ASSUME `8 divides buflen`) THEN
       REWRITE_TAC[divides] THEN
       DISCH_THEN(X_CHOOSE_TAC `d:num`) THEN ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `buflen < 8 * (N + 1)` THEN ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `8 * N <= buflen` THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[GSYM MULT_ASSOC; LT_MULT_LCANCEL; LE_MULT_LCANCEL] THEN
       CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `SUB_LIST(0,buflen) inlist = inlist:byte list`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
      [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `~(8 <= val(word_sub (word buflen:int64) (word buflen)))`
       ASSUME_TAC THENL
      [REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0] THEN ARITH_TAC; ALL_TAC] THEN
     ENSURES_INIT_TAC "s0" THEN
     ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
     ENSURES_FINAL_STATE_TAC THEN
     REWRITE_TAC[ALL] THEN ASM_REWRITE_TAC[] THEN
     EXISTS_TAC `N:num` THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL
      [UNDISCH_TAC `niblen < 272` THEN EXPAND_TAC "niblen" THEN
       ARITH_TAC; ALL_TAC] THEN
     CONJ_TAC THENL
      [DISJ1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     ASM_REWRITE_TAC[]]]);;


(* ------------------------------------------------------------------------- *)
(* Strengthened correctness: per-coefficient bound matching CBMC contract     *)
(* ensures(array_abs_bound(r, 0, return_value, MLDSA_ETA + 1)).              *)
(* ------------------------------------------------------------------------- *)

let REJ_SAMPLE_ETA4_ELEMENT_BOUND = BITBLAST_RULE
 `!x:int16. val x < 9
    ==> ival(word_sx(word_sub (word 4:int16) x):int32) < &5 /\
        -- &5 < ival(word_sx(word_sub (word 4:int16) x):int32)`;;

let REJ_SAMPLE_ETA4_ALL_BOUND = prove
 (`!l:byte list i. i < LENGTH(REJ_SAMPLE_ETA4_BYTES l)
    ==> ival(EL i (REJ_SAMPLE_ETA4_BYTES l):int32) < &5 /\
        -- &5 < ival(EL i (REJ_SAMPLE_ETA4_BYTES l):int32)`,
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; LENGTH_MAP] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `EL i (MAP (\x:int16. word_sx(word_sub (word 4:int16) x):int32)
              (REJ_NIBBLES_ETA4 (l:byte list))) =
     word_sx(word_sub (word 4) (EL i (REJ_NIBBLES_ETA4 l)))` SUBST1_TAC THENL
   [MATCH_MP_TAC EL_MAP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REJ_SAMPLE_ETA4_ELEMENT_BOUND THEN
  MP_TAC(ISPECL [`\x:int16. val x < 9`;
                 `NIBBLES_OF_BYTES(l:byte list)`; `i:num`]
    FILTER_EL_SATISFIES) THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4] THEN BETA_TAC THEN
  DISCH_THEN MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_NIBBLES_ETA4]) THEN ASM_REWRITE_TAC[]);;

(* Bridge from EL i of the SUB_LIST(0,256) prefix to EL i of the full         *)
(* REJ_SAMPLE_ETA4_BYTES list, used to apply REJ_SAMPLE_ETA4_ALL_BOUND in the       *)
(* subroutine postcondition.                                                  *)

let EL_REJ_SAMPLE_ETA4_SUB_LIST_256 = prove
 (`!l:byte list i.
        i < LENGTH(SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES l):int32 list)
        ==> EL i (SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES l):int32 list) =
            EL i (REJ_SAMPLE_ETA4_BYTES l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
    [`REJ_SAMPLE_ETA4_BYTES (l:byte list)`; `0`; `256`; `i:num`]
    EL_SUB_LIST) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `i < MIN 256 (LENGTH(REJ_SAMPLE_ETA4_BYTES (l:byte list)))` THEN
    ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine correctness with array_abs_bound matching CBMC contract        *)
(* ensures(array_abs_bound(r, 0, return_value, MLDSA_ETA + 1)) for eta = 4.  *)
(* ------------------------------------------------------------------------- *)

(* NOTE: This must be kept in sync with the CBMC specification
 * in mldsa/src/native/aarch64/src/arith_native_aarch64.h *)

let MLDSA_REJ_UNIFORM_ETA4_SUBROUTINE_CORRECT = prove
 (`!res buf buflen table (inlist:(4 word) list) pc stackpointer returnaddress.
        8 divides val buflen /\
        8 <= val buflen /\
        LENGTH inlist = 2 * val buflen /\
        ALL (nonoverlapping (word_sub stackpointer (word 576),576))
            [(word pc,LENGTH mldsa_rej_uniform_eta4_mc);
             (buf,val buflen); (table,4096)] /\
        ALL (nonoverlapping (res,1024))
            [(word pc,LENGTH mldsa_rej_uniform_eta4_mc);
             (word_sub stackpointer (word 576),576)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [res;buf;buflen;table] s /\
                  read(memory :> bytes(table,4096)) s =
                  num_of_wordlist mldsa_rej_uniform_eta_table /\
                  read(memory :> bytes(buf,val buflen)) s =
                  num_of_wordlist inlist)
             (\s. read PC s = returnaddress /\
                  let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4 inlist) in
                  let outlen = LENGTH outlist in
                  outlen <= 256 /\
                  C_RETURN s = word outlen /\
                  read(memory :> bytes(res,4 * outlen)) s =
                  num_of_wordlist outlist /\
                  (!i. i < outlen
                       ==> ival(EL i outlist:int32) < &5 /\
                           -- &5 < ival(EL i outlist:int32)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(res,1024);
                         memory :> bytes(word_sub stackpointer (word 576),576)])`,
  (* See eta2 _SUBROUTINE_CORRECT for the bridge rationale. *)
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPEC `inlist:(4 word) list` BYTES_TO_NIBBLES_SURJ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[EVEN_EXISTS] THEN EXISTS_TAC `val(buflen:int64)` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `bs:byte list` STRIP_ASSUME_TAC) THEN
  UNDISCH_THEN `BYTES_TO_NIBBLES (bs:byte list) = inlist`
    (SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_BYTES_TO_NIBBLES;
                              ARITH_RULE `2 * a = 2 * b <=> a = b`]) THEN
  REWRITE_TAC[NUM_OF_BYTES_TO_NIBBLES; GSYM REJ_SAMPLE_ETA4_BYTES_EQ] THEN
  MP_TAC(SPECL
   [`res:int64`; `buf:int64`; `buflen:int64`; `table:int64`;
    `bs:byte list`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
   (prove
    (`!res buf buflen table (inlist:byte list) pc stackpointer returnaddress.
        8 divides val buflen /\
        8 <= val buflen /\
        LENGTH inlist = val buflen /\
        ALL (nonoverlapping (word_sub stackpointer (word 576),576))
            [(word pc,LENGTH mldsa_rej_uniform_eta4_mc);
             (buf,val buflen); (table,4096)] /\
        ALL (nonoverlapping (res,1024))
            [(word pc,LENGTH mldsa_rej_uniform_eta4_mc);
             (word_sub stackpointer (word 576),576)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [res;buf;buflen;table] s /\
                  read(memory :> bytes(table,4096)) s =
                  num_of_wordlist mldsa_rej_uniform_eta_table /\
                  read(memory :> bytes(buf,val buflen)) s =
                  num_of_wordlist inlist)
             (\s. read PC s = returnaddress /\
                  let outlist = SUB_LIST(0,256)
                      (REJ_SAMPLE_ETA4_BYTES inlist) in
                  let outlen = LENGTH outlist in
                  outlen <= 256 /\
                  C_RETURN s = word outlen /\
                  read(memory :> bytes(res,4 * outlen)) s =
                  num_of_wordlist outlist /\
                  (!i. i < outlen
                       ==> ival(EL i outlist:int32) < &5 /\
                           -- &5 < ival(EL i outlist:int32)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(res,1024);
                         memory :> bytes(word_sub stackpointer (word 576),576)])`,
     ARM_ADD_RETURN_STACK_TAC
       ~pre_post_nsteps:(1,1)
       MLDSA_REJ_UNIFORM_ETA4_EXEC
       (REWRITE_RULE[fst MLDSA_REJ_UNIFORM_ETA4_EXEC]
          (CONV_RULE LENGTH_SIMPLIFY_CONV MLDSA_REJ_UNIFORM_ETA4_CORRECT))
       `[]:((armstate,int64)component)list` 576 THEN
     REPEAT STRIP_TAC THEN
     POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL
      [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN ARITH_TAC; ALL_TAC] THEN
     X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     SUBGOAL_THEN
       `EL i (SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES (inlist:byte list)):int32 list) =
        EL i (REJ_SAMPLE_ETA4_BYTES inlist)`
      SUBST1_TAC THENL
      [MATCH_MP_TAC EL_REJ_SAMPLE_ETA4_SUB_LIST_256 THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     MATCH_MP_TAC REJ_SAMPLE_ETA4_ALL_BOUND THEN
     UNDISCH_TAC `i < LENGTH(SUB_LIST(0,256)
       (REJ_SAMPLE_ETA4_BYTES (inlist:byte list)):int32 list)` THEN
     REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN ARITH_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;


(* ========================================================================= *)
(* Memory safety proof (variable-time: rejection sampling depends on data).  *)
(*                                                                           *)
(* Memory safety alone (not constant-time). The standard _SAFE_ proof        *)
(* pattern (exists f_events. forall ... e2 = f_events <public_params>)      *)
(* cannot be used here because the microarchitectural events depend on       *)
(* private data (which nibbles pass the < 9 filter).                         *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(* Helper: discharge the memsafe postcondition
     exists e2. read events s = APPEND e2 e /\ memaccess_inbounds e2 R W
   after symbolic simulation, using accumulated events from the invariant. *)
let DISCHARGE_MEMSAFE_TAC:tactic =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(* Like SIMPLE_ARITH_TAC but allows `val` in assumptions since
   contained_modulo bounds may involve val terms. *)
let (MEMSAFE_ARITH_TAC:tactic) =
  let numty = `:num` in
  let is_num_relop tm =
    exists (fun op -> is_binary op tm &&
                      (let x,_ = dest_binary op tm in type_of x = numty))
           ["=";"<";"<=";">";">="]
  and avoiders = ["lowdigits"; "highdigits"; "bigdigit";
                  "read"; "write"; "word"] in
  let avoiderp tm =
    match tm with Const(n,_) -> mem n avoiders | _ -> false in
  let filtered tm =
    (is_num_relop tm || (is_neg tm && is_num_relop (dest_neg tm))) &&
    not(can (find_term avoiderp) tm) in
  let tweak = GEN_REWRITE_RULE TRY_CONV [ARITH_RULE `~(n = 0) <=> 1 <= n`] in
  W(fun (asl,w) ->
    let asl' = filter (fun (_,th) -> filtered(concl th)) asl in
    MAP_EVERY (MP_TAC o tweak o snd) asl' THEN CONV_TAC ARITH_RULE);;

(* ASM-aware version of CONTAINED_TAC for loop-body proofs with
   symbolic memory address bounds. *)
let CONTAINED_ASM_TAC =
  GEN_REWRITE_TAC I [GSYM CONTAINED_MODULO_MOD2] THEN
  GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o LAND_CONV o TOP_DEPTH_CONV)
   [VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC(BINOP_CONV(LAND_CONV MOD_DOWN_CONV)) THEN
  GEN_REWRITE_TAC I [CONTAINED_MODULO_MOD2] THEN
  ((GEN_REWRITE_TAC I [CONTAINED_MODULO_REFL] THEN
    MEMSAFE_ARITH_TAC) ORELSE
   (MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN
    MEMSAFE_ARITH_TAC) ORELSE
   (MATCH_MP_TAC CONTAINED_MODULO_SIMPLE THEN MEMSAFE_ARITH_TAC));;

(* ASM-aware version of DISCHARGE_MEMSAFE_TAC for loop-body proofs. *)
let DISCHARGE_MEMSAFE_ASM_TAC:tactic =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[memaccess_inbounds; ALL; EX; FST; SND] THEN
    REPEAT CONJ_TAC THEN
    TRY(REPEAT ((DISJ1_TAC THEN CONTAINED_ASM_TAC) ORELSE DISJ2_TAC ORELSE
                CONTAINED_ASM_TAC) THEN NO_TAC);
    REWRITE_TAC[APPEND; APPEND_NIL] THEN
    FIRST_ASSUM ACCEPT_TAC];;

(* Strip an existential `?e_acc. read events s = APPEND e_acc e /\ ...` *)
let STRIP_EXISTS_ASSUM_TAC =
  FIRST_X_ASSUM(CHOOSE_THEN
   (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC)));;

(* ========================================================================= *)
(* The main memory safety theorem.                                           *)
(* ========================================================================= *)


let MLDSA_REJ_UNIFORM_ETA4_MEMSAFE = prove
 (`!res buf buflen table (inlist:byte list) pc e stackpointer.
      8 divides val buflen /\
      8 <= val buflen /\
      LENGTH inlist = val buflen /\
      ALL (nonoverlapping (stackpointer,576))
          [(word pc,LENGTH mldsa_rej_uniform_eta4_mc);
           (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (res,1024))
          [(word pc,LENGTH mldsa_rej_uniform_eta4_mc);
           (stackpointer,576)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
                read PC s = word(pc + MLDSA_REJ_UNIFORM_ETA4_CORE_START) /\
                read SP s = stackpointer /\
                C_ARGUMENTS [res;buf;buflen;table] s /\
                read(memory :> bytes(table,4096)) s =
                num_of_wordlist mldsa_rej_uniform_eta_table /\
                read(memory :> bytes(buf,val buflen)) s =
                num_of_wordlist inlist /\
                read events s = e)
           (\s. read PC s = word(pc + MLDSA_REJ_UNIFORM_ETA4_CORE_END) /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                       [buf,val buflen; table,4096; stackpointer,576]
                       [stackpointer,576; res,1024]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(res,1024);
                       memory :> bytes(stackpointer,576)])`,
  (* ---- Phase 0: setup ---- *)
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  REWRITE_TAC[fst MLDSA_REJ_UNIFORM_ETA4_EXEC;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    C_ARGUMENTS; ALL; C_RETURN] THEN
  MAP_EVERY X_GEN_TAC [`res:int64`; `buf:int64`] THEN
  W64_GEN_TAC `buflen:num` THEN
  MAP_EVERY X_GEN_TAC
   [`table:int64`; `inlist:byte list`; `pc:num`;
    `e:(uarch_event)list`; `stackpointer:int64`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (* ---- Intermediate sequence point at pc+256 ---- *)
  ENSURES_SEQUENCE_TAC `pc + 256`
   `\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
        read PC s = word(pc + 256) /\
        read X0 s = res /\ read X4 s = word 256 /\
        read X8 s = stackpointer /\
        read Q7 s = word 20769504351625144638033088116686852 /\
        ALL (nonoverlapping (res,1024)) [(word pc,344); (stackpointer,576)] /\
        ?n. let niblist = REJ_NIBBLES_ETA4(SUB_LIST(0,8*n) inlist) in
            let niblen = LENGTH niblist in
            niblen < 272 /\
            (buflen < 8 * (n + 1) \/ 256 <= niblen) /\
            read X9 s = word niblen /\
            read (memory :> bytes (stackpointer,2 * niblen)) s =
            num_of_wordlist niblist /\
            (exists e_acc.
              read events s = APPEND e_acc e /\
              memaccess_inbounds e_acc
                [buf,buflen; table,4096; stackpointer,576]
                [stackpointer,576; res,1024])` THEN
  CONJ_TAC THENL
   [ALL_TAC;

    (* ---- Writeback branch (pc+256 -> pc+336) ----
       Skip BIGNUM_LDIGITIZE_TAC and MEMORY_128_FROM_64_TAC: they introduce
       ~100 stack bytes64/bytes128 reads needed for CORRECT to derive nibble
       values, but irrelevant to memory safety (only events + PC + memaccess
       bounds matter). Keeping them inflates per-step ARM_STEPS_TAC cost. *)
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `nn:num` MP_TAC) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ABBREV_TAC `niblist = REJ_NIBBLES_ETA4
      (SUB_LIST(0,8*nn) inlist):int16 list` THEN
    ABBREV_TAC `niblen = LENGTH(niblist:int16 list)` THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `val(word niblen:int64) = niblen` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      UNDISCH_TAC `niblen < 272` THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--245) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY DISCHARGE_MEMSAFE_TAC THEN
    ALL_TAC] THEN

  (* ---- WOP: find smallest N ---- *)
  SUBGOAL_THEN
   `?N. buflen < 8 * (N + 1) \/
        256 <= LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,8*N) inlist):int16 list)`
  MP_TAC THENL
   [EXISTS_TAC `buflen:num` THEN DISJ1_TAC THEN ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num`
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_LT; NOT_LE] THEN STRIP_TAC THEN

  SUBGOAL_THEN `0 < N` ASSUME_TAC THENL
   [MP_TAC(ASSUME `buflen < 8 * (N + 1) \/
      256 <= LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,8*N) inlist):int16 list)`) THEN
    UNDISCH_TAC `8 <= buflen` THEN
    STRUCT_CASES_TAC (ARITH_RULE `N = 0 \/ 0 < N`) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES;
                    REJ_NIBBLES_ETA4_EMPTY; LENGTH] THEN
    ARITH_TAC; ALL_TAC] THEN

  ENSURES_WHILE_UP_TAC `N:num` `pc + 108` `pc + 248`
   `\i s. read (memory :> bytes (table,4096)) s =
          num_of_wordlist mldsa_rej_uniform_eta_table /\
          read (memory :> bytes (buf,buflen)) s = num_of_wordlist inlist /\
          aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
          read Q7 s = word 20769504351625144638033088116686852 /\
          read Q30 s = word 46731384791156575435574448262545417 /\
          read Q31 s = word 664619068533544770747334646890102785 /\
          (let niblist = REJ_NIBBLES_ETA4(SUB_LIST(0,8 * i) inlist) in
           let niblen = LENGTH niblist in
           read X0 s = res /\
           read X1 s = word_add buf (word(8 * i)) /\
           read X2 s = word_sub (word buflen) (word(8 * i)) /\
           read X3 s = table /\ read X4 s = word 256 /\
           read X7 s = word_add stackpointer (word(2 * niblen)) /\
           read X8 s = stackpointer /\ read X9 s = word niblen /\
           read (memory :> bytes (stackpointer,2 * niblen)) s =
           num_of_wordlist niblist /\
           (exists e_acc.
             read events s = APPEND e_acc e /\
             memaccess_inbounds e_acc
               [buf,buflen; table,4096; stackpointer,576]
               [stackpointer,576; res,1024]))` THEN
  REPEAT CONJ_TAC THENL
   [(*** Subgoal 1: 0 < N ***)
    ASM_ARITH_TAC;

    (*** Subgoal 2: Pre-loop init (75 ARM steps) ***)
    GHOST_INTRO_TAC `q31_init:int128` `read Q31` THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--75) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[WORD_INSERT_Q31]; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_NIBBLES_ETA4_EMPTY] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_SUB_0] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; num_of_wordlist] THEN
    TRY DISCHARGE_MEMSAFE_TAC THEN
    ALL_TAC;

    (*** Subgoal 3: Loop body ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ABBREV_TAC `curlist = REJ_NIBBLES_ETA4(SUB_LIST(0,8 * i) inlist)` THEN
    ABBREV_TAC `curlen = LENGTH(curlist:int16 list)` THEN
    SUBGOAL_THEN `curlen < 256` ASSUME_TAC THENL
     [EXPAND_TAC "curlen" THEN EXPAND_TAC "curlist" THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
      UNDISCH_TAC `i < N:num` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `8 * (i + 1) <= buflen` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
      UNDISCH_TAC `i < N:num` THEN ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
    ASM_REWRITE_TAC[] THEN
    ENSURES_SEQUENCE_TAC `pc + 0xe0`
     `\s. read (memory :> bytes (table,4096)) s =
          num_of_wordlist mldsa_rej_uniform_eta_table /\
          read (memory :> bytes (buf,buflen)) s =
            num_of_wordlist (inlist:byte list) /\
          aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
          read Q7 s = word 20769504351625144638033088116686852 /\
          read Q30 s = word 46731384791156575435574448262545417 /\
          read Q31 s = word 664619068533544770747334646890102785 /\
          read X0 s = res /\
          read X1 s = word_add buf (word(8 * (i + 1))) /\
          read X2 s = word_sub (word buflen) (word(8 * (i + 1))) /\
          read X3 s = table /\ read X4 s = word 256 /\
          read X7 s = word_add stackpointer (word(2 * curlen)) /\
          read X8 s = stackpointer /\ read X9 s = word curlen /\
          read (memory :> bytes (stackpointer,2 * curlen)) s =
          num_of_wordlist (curlist:int16 list) /\
          (?lis0 lis1:int16 list.
             LENGTH lis0 <= 8 /\ LENGTH lis1 <= 8 /\
             val(read X12 s:int64) = LENGTH lis0 /\
             val(read X13 s:int64) = LENGTH lis1 /\
             APPEND lis0 lis1 =
               REJ_NIBBLES_ETA4(SUB_LIST(8 * i,8) inlist) /\
             read Q16 s = word(num_of_wordlist lis0):int128 /\
             read Q17 s = word(num_of_wordlist lis1):int128) /\
          curlen < 256 /\
          nonoverlapping (stackpointer,576) (word pc,344) /\
          (exists e_acc.
            read events s = APPEND e_acc e /\
            memaccess_inbounds e_acc
              [buf,buflen; table,4096; stackpointer,576]
              [stackpointer,576; res,1024])` THEN
    CONJ_TAC THENL
     [(* First half (pc+108 -> pc+0xe0): SIMD compute chain *)
      GHOST_INTRO_TAC `nibbles1:int128` `read Q17` THEN
      ENSURES_INIT_TAC "s0" THEN
      STRIP_EXISTS_ASSUM_TAC THEN
      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
      SUBGOAL_THEN `~(256 <= val(word curlen:int64))` ASSUME_TAC THENL
       [REWRITE_TAC[NOT_LE; VAL_WORD; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        SUBGOAL_THEN `curlen MOD 18446744073709551616 = curlen` SUBST1_TAC THENL
         [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `curlen < 256` THEN ARITH_TAC;
          UNDISCH_TAC `curlen < 256` THEN ARITH_TAC]; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(256 <= val(word curlen:int64))`]) THEN
      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC [3] THEN
      ABBREV_TAC
       `loaded_d:int64 = read (memory :> bytes64 (word_add buf (word (8 * i)))) s3` THEN
      ARM_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (4--11) THEN
      REABBREV_TAC `nibbles0:int128 = read Q16 s11` THEN
      REABBREV_TAC `nibbles1b:int128 = read Q17 s11` THEN
      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (12--19) THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
      RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [word_ugt; relational2; GT; WORD_AND_MASK]) THEN
      RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
      RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
      MAP_EVERY REABBREV_TAC
       [`idx0 = read X12 s19`; `idx1 = read X13 s19`] THEN
      MAP_EVERY ABBREV_TAC
       [`tab0 = read(memory :> bytes128(word_add table
                    (word(16 * val(idx0:int64))))) s19`;
        `tab1 = read(memory :> bytes128(word_add table
                    (word(16 * val(idx1:int64))))) s19`] THEN
      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (20--27) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_AND]) THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
      RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [word_ugt; relational2; GT; WORD_AND_MASK]) THEN
      RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
      RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (28--29) THEN
      SUBGOAL_THEN
        `read Q16 s29 = word(num_of_wordlist
                             (REJ_NIBBLES_ETA4
                               [word_subword (loaded_d:int64) (0,8):byte;
                                word_subword loaded_d (8,8);
                                word_subword loaded_d (16,8);
                                word_subword loaded_d (24,8)])) /\
         read Q17 s29 = word(num_of_wordlist
                             (REJ_NIBBLES_ETA4
                               [word_subword (loaded_d:int64) (32,8):byte;
                                word_subword loaded_d (40,8);
                                word_subword loaded_d (48,8);
                                word_subword loaded_d (56,8)]))`
      MP_TAC THENL
       [(fun (asl, w) ->
          FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
            let c = concl th in
            is_eq c &&
            (match lhs c with
             | Comb(Comb(Const("read",_), Const("events",_)), _) -> true
             | _ -> false))) (asl, w)) THEN
        REWRITE_TAC[UADDLV_COUNT_LEMMA] THEN
        REWRITE_TAC(List.map (fun k -> BITBLAST_RULE
          (vsubst [mk_small_numeral k, `k:num`]
          `bit k (word_subword (word_neg (word (bitval b):16 word))
                  (0,8):8 word) <=> b`)) (0--7)) THEN
        ASM_REWRITE_TAC[] THEN
        (let prove_hw name pos byte_pos op =
           let rhs_inner = if op = "and"
             then Printf.sprintf
               "(word_and (word_subword (loaded_d:int64) (%d,8):byte) (word 15):byte)"
               byte_pos
             else Printf.sprintf
               "(word_ushr (word_subword (loaded_d:int64) (%d,8):byte) 4:byte)"
               byte_pos in
           let goal_str = Printf.sprintf
             "(word_subword (%s:int128) (%d,16)):int16 = word_zx %s :int16"
             name pos rhs_inner in
           SUBGOAL_THEN (parse_term goal_str) ASSUME_TAC THENL
            [FIRST_X_ASSUM(MP_TAC o SYM o check
               (fun th -> let c = concl th in is_eq c &&
                 (try fst(dest_var(rhs c)) = name with _ -> false))) THEN
             DISCH_THEN(fun th -> SUBST1_TAC th THEN ASSUME_TAC(SYM th)) THEN
             CONV_TAC WORD_BLAST;
             ALL_TAC] in
         prove_hw "nibbles0" 0 0 "and" THEN
         prove_hw "nibbles0" 16 0 "ushr" THEN
         prove_hw "nibbles0" 32 8 "and" THEN
         prove_hw "nibbles0" 48 8 "ushr" THEN
         prove_hw "nibbles0" 64 16 "and" THEN
         prove_hw "nibbles0" 80 16 "ushr" THEN
         prove_hw "nibbles0" 96 24 "and" THEN
         prove_hw "nibbles0" 112 24 "ushr" THEN
         prove_hw "nibbles1b" 0 32 "and" THEN
         prove_hw "nibbles1b" 16 32 "ushr" THEN
         prove_hw "nibbles1b" 32 40 "and" THEN
         prove_hw "nibbles1b" 48 40 "ushr" THEN
         prove_hw "nibbles1b" 64 48 "and" THEN
         prove_hw "nibbles1b" 80 48 "ushr" THEN
         prove_hw "nibbles1b" 96 56 "and" THEN
         prove_hw "nibbles1b" 112 56 "ushr") THEN
        (fun (asl, w) ->
          let halfword_hyps =
            List.filter (fun (_,th) ->
              let c = concl th in
              is_eq c &&
              (try let l = lhand c in
                   match l with
                   | Comb(Comb(Const("word_subword",_), v),
                          Comb(Comb(Const(",",_), _), len_tm)) ->
                       is_var v &&
                       (let nm = fst(dest_var v) in
                        nm = "nibbles0" || nm = "nibbles1b") &&
                       (try dest_small_numeral len_tm = 16 with _ -> false)
                   | _ -> false
               with _ -> false)) asl in
          let byte_lemmas = BYTE_SPLIT_AND @ BYTE_SPLIT_USHR in
          let new_facts = List.concat (List.map (fun (_, h) ->
            List.concat (List.map (fun lem ->
              try CONJUNCTS(MATCH_MP lem h)
              with _ -> []) byte_lemmas)) halfword_hyps) in
          (MAP_EVERY ASSUME_TAC new_facts) (asl, w)) THEN
        UNDISCH_TAC
         `read(memory :> bytes(table,4096)) s29 =
          num_of_wordlist mldsa_rej_uniform_eta_table` THEN
        REPLICATE_TAC 4
         (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
               [GSYM NUM_OF_PAIR_WORDLIST]) THEN
        REWRITE_TAC[mldsa_rej_uniform_eta_table; pair_wordlist] THEN
        CONV_TAC WORD_REDUCE_CONV THEN
        CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
        REWRITE_TAC[GSYM BYTES128_WBYTES] THEN REPEAT STRIP_TAC THEN
        DISCARD_MATCHING_ASSUMPTIONS
         [`read Q24 s = x`; `read Q25 s = x`] THEN
        REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
          (fun th -> is_var(rhs(concl th)) &&
                     let n = fst(dest_var(rhs(concl th))) in
                     n = "tab0" || n = "tab1"))) THEN
        DISCARD_MATCHING_ASSUMPTIONS
         [`read X12 s = x`; `read X13 s = x`] THEN
        REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
          (fun th -> is_var(rhs(concl th)) &&
                     let n = fst(dest_var(rhs(concl th))) in
                     n = "idx0" || n = "idx1"))) THEN
        ASM_REWRITE_TAC[] THEN
        DISCARD_MATCHING_ASSUMPTIONS
         [`read Q16 s = x`; `read Q17 s = x`] THEN
        REWRITE_TAC[REJ_NIBBLES_ETA4; NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND] THEN
        REWRITE_TAC[FILTER] THEN
        REWRITE_TAC[VAL_WORD_ZX_BYTE16; BYTE_AND_15_MOD; BYTE_USHR4_DIV;
                    VAL_WORD_NIBBLE_LT] THEN
        REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
        REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD_0] THEN
        ASM_REWRITE_TAC[] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[num_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[BYTE_AND_15_MOD; BYTE_USHR4_DIV;
                                    VAL_WORD_ZX_BYTE16; VAL_WORD_NIBBLE_LT]) THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[VAL_BYTE_NIB_MOD_65536] THEN
        CONV_TAC WORD_BLAST;
        STRIP_TAC] THEN
      DISCARD_MATCHING_ASSUMPTIONS
       [`read Q16 s = word_join (x:int64) (y:int64):int128`;
        `read Q17 s = word_join (x:int64) (y:int64):int128`] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[WORD_SUBWORD_AND] THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      REWRITE_TAC[WORD_AND_0; WORD_POPCOUNT_0; ADD_CLAUSES] THEN
      REWRITE_TAC[POPCOUNT_AND_POWERS] THEN
      REPEAT CONJ_TAC THEN
      TRY(CONV_TAC WORD_RULE) THEN
      TRY(NONOVERLAPPING_TAC) THEN
      TRY(REWRITE_TAC[UADDLV_BOUND_LEMMA] THEN NO_TAC) THEN
      TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      TRY(ASM_ARITH_TAC) THEN
      TRY (
      (* Two remaining goals (per subgoal arm):
         (a) `?e_acc'. ... = APPEND e_acc' e /\ memaccess_inbounds e_acc' ...`
             — discharge with DISCHARGE_MEMSAFE_ASM_TAC.
         (b) `?lis0 lis1. ...` — same existential as the parent CORRECT proof's
             post-TBL closure (line ~3250); reuse that pattern.
         Use FIRST so each subgoal picks its appropriate closer. *)
      FIRST
       [(* Establish table index bounds for memory safety: idx0/idx1 < 256.
           Required so DISCHARGE_MEMSAFE_ASM_TAC can prove the table access
           at word_add table (word(16 * val idx)) is contained in the table
           region (4096 bytes).

           idx0/idx1 are the X12/X13 popcount-accumulator values at s19,
           with shape word_zx (word_subword X (0,32)):int64 where X is the
           int128 word_add of 8 summands word_and (word 2^k) (mask) for
           k = 0..7. Each summand is 0 or 2^k, so the sum is bounded by
           1+2+...+128 = 255. The two helper lemmas below close the bound
           generically over any word width with dimindex >= 8:
             SUM_8_BIT_BOUND_POLY: sum of 8 bounded summands is <= 255
             SBND_K_POLY:         val(word_and (word k) X) <= k for k <= 128
           SUBST1_TAC the popcount equation, REWRITE val(word_zx ...) and
           val(word_subword (...,0,32)), then MATCH_MP_TAC each lemma. *)
        SUBGOAL_THEN `val(idx0:int64) < 256 /\ val(idx1:int64) < 256`
          STRIP_ASSUME_TAC THENL
         [          (let close_idx name =
             FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
               let c = concl th in
               is_eq c &&
               (try fst(dest_var(rhs c)) = name with _ -> false))) THEN
             REWRITE_TAC[WORD_ZX_INT32_INT64; VAL_WORD_SUBWORD_0_32] THEN
             MATCH_MP_TAC(ARITH_RULE `n <= 255 ==> n MOD 2 EXP 32 < 256`) THEN
             MATCH_MP_TAC SUM_8_BIT_BOUND_POLY THEN
             REWRITE_TAC[DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64;
                         DIMINDEX_128] THEN
             CONV_TAC NUM_REDUCE_CONV THEN
             REPEAT CONJ_TAC THEN
             MATCH_MP_TAC SBND_K_POLY THEN
             REWRITE_TAC[DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64;
                         DIMINDEX_128] THEN
             CONV_TAC NUM_REDUCE_CONV in
           CONJ_TAC THENL
            [close_idx "idx0";
             close_idx "idx1"]);
          ALL_TAC] THEN
        DISCHARGE_MEMSAFE_ASM_TAC;
        (* lis0/lis1 existential closure — copied verbatim from the parent
           CORRECT proof. *)
        EXISTS_TAC
          `REJ_NIBBLES_ETA4
             [word_subword (loaded_d:int64) (0,8):byte;
              word_subword loaded_d (8,8);
              word_subword loaded_d (16,8);
              word_subword loaded_d (24,8)]` THEN
        EXISTS_TAC
          `REJ_NIBBLES_ETA4
             [word_subword (loaded_d:int64) (32,8):byte;
              word_subword loaded_d (40,8);
              word_subword loaded_d (48,8);
              word_subword loaded_d (56,8)]` THEN
        REWRITE_TAC[REJ_NIBBLES_ETA4_LENGTH_4] THEN
      MP_TAC(SPECL [`buf:int64`; `buflen:num`; `inlist:byte list`;
                    `i:num`; `s29:armstate`] SUB_LIST_8_BYTES_FROM_INT64) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[REJ_NIBBLES_ETA4_SPLIT_8] THEN
      REWRITE_TAC[UADDLV_COUNT_LEMMA] THEN
      REWRITE_TAC(List.map (fun k -> BITBLAST_RULE
        (vsubst [mk_small_numeral k, `k:num`]
        `bit k (word_subword (word_neg (word (bitval b):16 word))
                (0,8):8 word) <=> b`)) (0--7)) THEN
      ASM_REWRITE_TAC[] THEN
      (let prove_hw name pos byte_pos op =
         let rhs_inner = if op = "and"
           then Printf.sprintf
             "(word_and (word_subword (loaded_d:int64) (%d,8):byte) (word 15):byte)"
             byte_pos
           else Printf.sprintf
             "(word_ushr (word_subword (loaded_d:int64) (%d,8):byte) 4:byte)"
             byte_pos in
         let goal_str = Printf.sprintf
           "(word_subword (%s:int128) (%d,16)):int16 = word_zx %s :int16"
           name pos rhs_inner in
         SUBGOAL_THEN (parse_term goal_str) ASSUME_TAC THENL
          [FIRST_X_ASSUM(MP_TAC o SYM o check
             (fun th -> let c = concl th in is_eq c &&
               (try fst(dest_var(rhs c)) = name with _ -> false))) THEN
           DISCH_THEN(fun th -> SUBST1_TAC th THEN ASSUME_TAC(SYM th)) THEN
           CONV_TAC WORD_BLAST;
           ALL_TAC] in
       prove_hw "nibbles0" 0 0 "and" THEN
       prove_hw "nibbles0" 16 0 "ushr" THEN
       prove_hw "nibbles0" 32 8 "and" THEN
       prove_hw "nibbles0" 48 8 "ushr" THEN
       prove_hw "nibbles0" 64 16 "and" THEN
       prove_hw "nibbles0" 80 16 "ushr" THEN
       prove_hw "nibbles0" 96 24 "and" THEN
       prove_hw "nibbles0" 112 24 "ushr" THEN
       prove_hw "nibbles1b" 0 32 "and" THEN
       prove_hw "nibbles1b" 16 32 "ushr" THEN
       prove_hw "nibbles1b" 32 40 "and" THEN
       prove_hw "nibbles1b" 48 40 "ushr" THEN
       prove_hw "nibbles1b" 64 48 "and" THEN
       prove_hw "nibbles1b" 80 48 "ushr" THEN
       prove_hw "nibbles1b" 96 56 "and" THEN
       prove_hw "nibbles1b" 112 56 "ushr") THEN
      REPEAT CONJ_TAC THEN
      FIRST
       [MP_TAC(SPECL
         [`nibbles0:int128`;
          `word_subword (loaded_d:int64) (0,8):byte`;
          `word_subword (loaded_d:int64) (8,8):byte`;
          `word_subword (loaded_d:int64) (16,8):byte`;
          `word_subword (loaded_d:int64) (24,8):byte`] COUNT_BRIDGE_ABSTRACT_4) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REFL_TAC;
        MP_TAC(SPECL
         [`nibbles1b:int128`;
          `word_subword (loaded_d:int64) (32,8):byte`;
          `word_subword (loaded_d:int64) (40,8):byte`;
          `word_subword (loaded_d:int64) (48,8):byte`;
          `word_subword (loaded_d:int64) (56,8):byte`] COUNT_BRIDGE_ABSTRACT_4) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REFL_TAC;
        FIRST_ASSUM(fun my_hyp ->
          FIRST_ASSUM(fun arm_hyp ->
            try ACCEPT_TAC(TRANS (SYM arm_hyp) my_hyp)
            with _ -> NO_TAC))]]) THEN
      ALL_TAC;
            (* Second half (pc+0xe0 -> pc+248): stores *)
      ENSURES_INIT_TAC "s0" THEN
      STRIP_EXISTS_ASSUM_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `lis0:int16 list` MP_TAC o check
        (fun th -> try fst(dest_var(fst(dest_exists(concl th)))) = "lis0"
                   with _ -> false)) THEN
      DISCH_THEN(X_CHOOSE_THEN `lis1:int16 list` STRIP_ASSUME_TAC) THEN
      ABBREV_TAC `len0 = LENGTH(lis0:int16 list)` THEN
      ABBREV_TAC `len1 = LENGTH(lis1:int16 list)` THEN
      SUBGOAL_THEN `val(read X12 s0:int64) = len0 /\ val(read X13 s0:int64) = len1`
        STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC [1] THEN
      SUBGOAL_THEN
       `read (memory :> bytes (stackpointer, 2 * (curlen + len0))) s1 =
        num_of_wordlist(APPEND curlist lis0:int16 list)`
      ASSUME_TAC THENL
       [REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
        SUBGOAL_THEN `LENGTH(curlist:int16 list) = curlen` ASSUME_TAC THENL
         [EXPAND_TAC "curlen" THEN REFL_TAC; ALL_TAC] THEN
        W(MP_TAC o PART_MATCH (lhand o rand)
          BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[DIMINDEX_16] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
          ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          SUBGOAL_THEN
           `read (memory :> bytes128
                  (word_add stackpointer (word (2 * curlen)))) s1 =
            word(num_of_wordlist(lis0:int16 list)):int128`
          MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
          REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES;
                      VAL_READ_WBYTES;
                      DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
          SUBGOAL_THEN `2 * len0 = MIN 16 (2 * len0)` SUBST1_TAC THENL
           [UNDISCH_TAC `len0:num <= 8` THEN ARITH_TAC;
            REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
          REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
          MATCH_MP_TAC MOD_LT THEN
          MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
          ASM_REWRITE_TAC[DIMINDEX_16] THEN
          UNDISCH_TAC `len0:num <= 8` THEN ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `read X12 s1:int64 = word len0` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `len0:num <= 8` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `read X13 s1:int64 = word len1` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `len1:num <= 8` THEN ARITH_TAC; ALL_TAC] THEN
      ARM_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC "s2" THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_ADD_SHL1]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `nonoverlapping (word_add stackpointer (word(2 * (curlen + len0))):int64,
                        16) (word pc:int64, 344)`
      ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `val(word len0:int64) = len0` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        UNDISCH_TAC `len0:num <= 8` THEN ARITH_TAC; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word len0:int64) = len0`]) THEN
      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC [3] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word len0:int64) = len0`]) THEN
      SUBGOAL_THEN
       `read (memory :> bytes (stackpointer, 2 * ((curlen + len0) + len1))) s3 =
        num_of_wordlist(APPEND (APPEND curlist lis0) lis1:int16 list)`
      ASSUME_TAC THENL
       [REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
        SUBGOAL_THEN
          `LENGTH(APPEND curlist lis0:int16 list) = curlen + len0`
        ASSUME_TAC THENL
         [REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        W(MP_TAC o PART_MATCH (lhand o rand)
          BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[DIMINDEX_16] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
          ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN
          `word_add stackpointer (word (2 * curlen + 2 * len0):int64) =
           word_add stackpointer (word (2 * (curlen + len0)))`
         (fun th -> REWRITE_TAC[th]) THENL
         [CONV_TAC WORD_RULE; ALL_TAC] THEN
        SUBGOAL_THEN `2 * curlen + 2 * len0 = 2 * (curlen + len0)`
         SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          SUBGOAL_THEN
           `read (memory :> bytes128
                  (word_add stackpointer (word (2 * (curlen + len0))))) s3 =
            word(num_of_wordlist(lis1:int16 list)):int128`
          MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
          REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES;
                      VAL_READ_WBYTES;
                      DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
          SUBGOAL_THEN `2 * len1 = MIN 16 (2 * len1)` SUBST1_TAC THENL
           [UNDISCH_TAC `len1:num <= 8` THEN ARITH_TAC;
            REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
          REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
          MATCH_MP_TAC MOD_LT THEN
          MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
          ASM_REWRITE_TAC[DIMINDEX_16] THEN
          UNDISCH_TAC `len1:num <= 8` THEN ARITH_TAC];
        ALL_TAC] THEN
      ARM_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC "s4" THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_ADD_SHL1]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (5--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `8 * (i + 1) <= LENGTH(inlist:byte list)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MP_TAC(ASSUME `8 * (i + 1) <= buflen`) THEN ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPECL [`inlist:byte list`; `i:num`] REJ_NIBBLES_ETA4_STEP) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ABBREV_TAC `newbatch = REJ_NIBBLES_ETA4(SUB_LIST(8*i, 8) inlist):int16 list` THEN
      SUBGOAL_THEN `APPEND (lis0:int16 list) lis1 = newbatch` ASSUME_TAC THENL
       [EXPAND_TAC "newbatch" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `LENGTH(newbatch:int16 list) = len0 + len1` ASSUME_TAC THENL
       [UNDISCH_TAC `APPEND (lis0:int16 list) lis1 = newbatch` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `val(word len0:int64) = len0 /\ val(word len1:int64) = len1`
        STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
        REWRITE_TAC[DIMINDEX_64] THENL
         [UNDISCH_TAC `len0:num <= 8` THEN ARITH_TAC;
          UNDISCH_TAC `len1:num <= 8` THEN ARITH_TAC];
        ALL_TAC] THEN
      REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN
      TRY(CONV_TAC WORD_RULE) THEN
      TRY(AP_TERM_TAC THEN AP_TERM_TAC THEN
          ASM_REWRITE_TAC[] THEN ARITH_TAC) THEN
      TRY(SUBGOAL_THEN
           `2 * (curlen + len0 + len1) = 2 * ((curlen + len0) + len1)`
         SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
         SUBGOAL_THEN
          `APPEND curlist (newbatch:int16 list) =
           APPEND (APPEND curlist lis0) lis1`
         SUBST1_TAC THENL
          [UNDISCH_TAC `APPEND (lis0:int16 list) lis1 = newbatch` THEN
           DISCH_THEN(SUBST1_TAC o SYM) THEN
           REWRITE_TAC[APPEND_ASSOC]; ALL_TAC] THEN
         ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      (* e_acc existential at end: reuse the loop-entry e_acc with 6 new events *)
      TRY(W(fun (_,w) ->
        if (try fst(dest_var(fst(dest_exists w))) = "e_acc" with _ -> false)
        then DISCHARGE_MEMSAFE_ASM_TAC
        else NO_TAC)) THEN
      (* Remaining goal is the `?e_acc'.` existential for the 2 stack stores;
         DISCHARGE_MEMSAFE_ASM_TAC handles the CONS_TO_APPEND + memaccess_inbounds. *)
      TRY DISCHARGE_MEMSAFE_ASM_TAC THEN
      ALL_TAC];

    (*** Subgoal 4: Backedge ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ENSURES_INIT_TAC "s0" THEN
    STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `8 <= val(word_sub (word buflen:int64) (word(8 * i)))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `8 * (i + 1) <= buflen` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
        UNDISCH_TAC `i < N:num` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `8 * i < 2 EXP 64` ASSUME_TAC THENL
       [UNDISCH_TAC `buflen < 2 EXP 64` THEN
        UNDISCH_TAC `8 * (i + 1) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `8 * i` THEN ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
      UNDISCH_TAC `8 * (i + 1) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY DISCHARGE_MEMSAFE_ASM_TAC THEN
    ALL_TAC;

    (*** Subgoal 5: Post-loop ***)
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ABBREV_TAC `niblen = LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,8*N) inlist):int16 list)` THEN
    SUBGOAL_THEN `niblen < 272` ASSUME_TAC THENL
     [EXPAND_TAC "niblen" THEN
      MATCH_MP_TAC NIBLEN_BOUND_FROM_WOP THEN
      ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `mm:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `mm:num`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    VAL_INT64_TAC `niblen:num` THEN
    ASM_CASES_TAC `256 <= niblen` THENL
     [      ASM_CASES_TAC `8 <= val(word_sub (word buflen:int64) (word(8 * N)))` THENL
       [        ENSURES_SEQUENCE_TAC `pc + 108`
         `\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
              read PC s = word(pc + 108) /\
              read X0 s = res /\ read X4 s = word 256 /\
              read X8 s = stackpointer /\
              read Q7 s = word 20769504351625144638033088116686852 /\
              read X9 s = word niblen /\
              read (memory :> bytes (stackpointer,2 * niblen)) s =
              num_of_wordlist (REJ_NIBBLES_ETA4(SUB_LIST(0,8*N) inlist):int16 list) /\
              ALL (nonoverlapping (res,1024)) [(word pc,344); (stackpointer,576)] /\
              (exists e_acc.
                read events s = APPEND e_acc e /\
                memaccess_inbounds e_acc
                  [buf,buflen; table,4096; stackpointer,576]
                  [stackpointer,576; res,1024])` THEN
        CONJ_TAC THENL
         [          ENSURES_INIT_TAC "s0" THEN
          STRIP_EXISTS_ASSUM_TAC THEN
          ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[ALL] THEN ASM_REWRITE_TAC[] THEN
          REPEAT CONJ_TAC THEN
          TRY(NONOVERLAPPING_TAC) THEN
          TRY DISCHARGE_MEMSAFE_ASM_TAC THEN
          ALL_TAC;
          ENSURES_INIT_TAC "s0" THEN
          STRIP_EXISTS_ASSUM_TAC THEN
          SUBGOAL_THEN `256 <= val(word niblen:int64)` ASSUME_TAC THENL
           [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
            SUBGOAL_THEN `niblen MOD 2 EXP 64 = niblen` SUBST1_TAC THENL
             [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `niblen < 272` THEN
              ARITH_TAC;
              ASM_REWRITE_TAC[]];
            ALL_TAC] THEN
          ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
          ENSURES_FINAL_STATE_TAC THEN
          REWRITE_TAC[ALL] THEN ASM_REWRITE_TAC[] THEN
          EXISTS_TAC `N:num` THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
          REPEAT CONJ_TAC THEN
          TRY(UNDISCH_TAC `niblen < 272` THEN EXPAND_TAC "niblen" THEN
              ARITH_TAC) THEN
          TRY DISCHARGE_MEMSAFE_ASM_TAC THEN
          ALL_TAC];
        ENSURES_INIT_TAC "s0" THEN
        STRIP_EXISTS_ASSUM_TAC THEN
        ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
        ENSURES_FINAL_STATE_TAC THEN
        REWRITE_TAC[ALL] THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `N:num` THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THEN
        TRY(UNDISCH_TAC `niblen < 272` THEN EXPAND_TAC "niblen" THEN
            ARITH_TAC) THEN
        TRY DISCHARGE_MEMSAFE_ASM_TAC THEN
        ALL_TAC];
      SUBGOAL_THEN `buflen < 8 * (N + 1)` ASSUME_TAC THENL
       [FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~(256 <= niblen)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `8 * N <= buflen` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN
        UNDISCH_TAC `0 < N` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `8 * N = buflen` ASSUME_TAC THENL
       [MP_TAC(ASSUME `8 divides buflen`) THEN
        REWRITE_TAC[divides] THEN
        DISCH_THEN(X_CHOOSE_TAC `d:num`) THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `buflen < 8 * (N + 1)` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `8 * N <= buflen` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM MULT_ASSOC; LT_MULT_LCANCEL; LE_MULT_LCANCEL] THEN
        CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `SUB_LIST(0,buflen) inlist = inlist:byte list`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(8 <= val(word_sub (word buflen:int64) (word buflen)))`
        ASSUME_TAC THENL
       [REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0] THEN ARITH_TAC; ALL_TAC] THEN
      ENSURES_INIT_TAC "s0" THEN
      STRIP_EXISTS_ASSUM_TAC THEN
      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN
      REWRITE_TAC[ALL] THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `N:num` THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN
      TRY(UNDISCH_TAC `niblen < 272` THEN EXPAND_TAC "niblen" THEN
          ARITH_TAC) THEN
      TRY(DISJ1_TAC THEN ASM_REWRITE_TAC[]) THEN
      TRY DISCHARGE_MEMSAFE_ASM_TAC THEN
      ALL_TAC]]);;


(* ------------------------------------------------------------------------- *)
(* Memory safety of the subroutine form.                                      *)
(*                                                                            *)
(* This proves memory safety only (all accesses in-bounds), not the full       *)
(* secret-independence (f_events) clause of the other AArch64 _SUBROUTINE_SAFE *)
(* theorems. That is intentional: rej_uniform_eta{2,4} produce the secret      *)
(* vectors s1/s2, but the rejection decision itself is not secret, so control  *)
(* flow and timing may depend on it. See pq-code-package/mldsa-native#1160.    *)
(* ------------------------------------------------------------------------- *)


let MLDSA_REJ_UNIFORM_ETA4_SUBROUTINE_SAFE = time prove
 (`!res buf buflen table (inlist:byte list) pc e stackpointer returnaddress.
      8 divides val buflen /\
      8 <= val buflen /\
      LENGTH inlist = val buflen /\
      ALL (nonoverlapping (word_sub stackpointer (word 576),576))
          [(word pc,LENGTH mldsa_rej_uniform_eta4_mc);
           (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (res,1024))
          [(word pc,LENGTH mldsa_rej_uniform_eta4_mc);
           (word_sub stackpointer (word 576),576)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [res;buf;buflen;table] s /\
                read(memory :> bytes(table,4096)) s =
                num_of_wordlist mldsa_rej_uniform_eta_table /\
                read(memory :> bytes(buf,val buflen)) s =
                num_of_wordlist inlist /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                       [buf,val buflen; table,4096;
                        word_sub stackpointer (word 576),576]
                       [word_sub stackpointer (word 576),576; res,1024]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(res,1024);
                       memory :> bytes(word_sub stackpointer (word 576),576)])`,
  ARM_ADD_RETURN_STACK_TAC
    ~pre_post_nsteps:(1,1)
    MLDSA_REJ_UNIFORM_ETA4_EXEC
    (REWRITE_RULE[fst MLDSA_REJ_UNIFORM_ETA4_EXEC]
       (CONV_RULE LENGTH_SIMPLIFY_CONV MLDSA_REJ_UNIFORM_ETA4_MEMSAFE))
    `[]:int64 list` 576 THEN
  DISCHARGE_MEMSAFE_TAC);;

