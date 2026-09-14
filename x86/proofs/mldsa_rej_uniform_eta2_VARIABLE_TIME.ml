(*
 * Copyright (c) The mldsa-native project authors
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA Rejection uniform sampling for eta=2 (x86_64 AVX2).                *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(* Make silent type-variable invention an error (avoids nondeterministic     *)
(* "seqapply: Length mismatch" failures from fresh tyvars across subgoals).  *)
type_invention_error := true;;


(* Lookup table used by rejection sampling in the x86_64 AVX2 impl.          *)
(* Shared with the base mldsa_rej_uniform proof (same 2048-byte VPSHUFB      *)
(* table); defined once in x86/proofs/mldsa_rej_uniform_table.ml.            *)
needs "x86/proofs/mldsa_rej_uniform_table.ml";;

(* ------------------------------------------------------------------------- *)
(* Helper definitions/lemmas inlined from mldsa-native's                     *)
(* common/mldsa_specs.ml and x86_64/proofs/mldsa_utils.ml.                   *)
(* Inlined (not added to common/mlkem_mldsa.ml) because that file is SHARED  *)
(* with the AArch64 build; several of these are typed over x86state.         *)
(* ------------------------------------------------------------------------- *)

(* [from mldsa-native mldsa_specs.ml] *)
let EL_SUB_LIST = prove(
 `!l:'a list. !i k n. i < n /\ k + n <= LENGTH l
   ==> EL i (SUB_LIST (k, n) l) = EL (k + i) l`,
  LIST_INDUCT_TAC THENL [
    REWRITE_TAC[LENGTH; LE; ADD_EQ_0] THEN ARITH_TAC;
    REWRITE_TAC[LENGTH] THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC (SPEC `k:num` num_CASES) THEN
    STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
    REWRITE_TAC[LT; SUB_LIST_CLAUSES; ADD_CLAUSES] THENL [
      STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
      REWRITE_TAC[EL; HD; TL; ADD_CLAUSES] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [`n:num`; `0`; `n':num`]) THEN
      REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[EL; TL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [`i:num`; `n':num`; `SUC n''`]) THEN
      ASM_REWRITE_TAC[LT_SUC] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

(* [from mldsa-native mldsa_specs.ml] *)
let LENGTH_SUB_LIST_0 = prove
 (`!n (l:'a list). n <= LENGTH l ==> LENGTH (SUB_LIST (0, n) l) = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN ASM_ARITH_TAC);;

(* [from mldsa-native mldsa_specs.ml] *)
let WORD_SUBWORD_NUM_OF_WORDLIST = prove
 (`!(ls:(L word)list) k.
    dimindex(:KL) = dimindex(:L) * LENGTH ls /\
    k < LENGTH ls
    ==> word_subword (word (num_of_wordlist ls) : KL word) (dimindex(:L)*k, dimindex(:L)) : L word = EL k ls`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD] THEN
  REWRITE_TAC[ARITH_RULE `MIN n n = n`] THEN
  SUBGOAL_THEN `val (word (num_of_wordlist (ls:(L word)list)) : KL word) = num_of_wordlist ls` SUBST1_TAC THENL
  [W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_EQ o lhand o snd) THEN
   ANTS_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (dimindex(:L) * LENGTH (ls:(L word)list))` THEN
    REWRITE_TAC[NUM_OF_WORDLIST_BOUND; LE_EXP; LE_REFL] THEN ASM_ARITH_TAC;
    SIMP_TAC[]];
   MP_TAC(ISPECL [`ls:(L word)list`; `k:num`] NUM_OF_WORDLIST_EL) THEN
   ASM_REWRITE_TAC[]]);;

(* [from mldsa-native mldsa_specs.ml] *)
let REJ_SAMPLE = define
 `REJ_SAMPLE l = FILTER (\x:int32. val x < 8380417)
    (MAP (\x:24 word. word(val x MOD 2 EXP 23):int32) l)`;;

(* [from mldsa-native mldsa_specs.ml] *)
let REJ_SAMPLE_ETA2 = define
  `REJ_SAMPLE_ETA2 (l:(4 word) list) =
   MAP (\x:4 word.
          word_sx (word_sub (word 2:4 word)
                            (word_umod x (word 5:4 word))):int32)
       (FILTER (\x:4 word. val x < 15) l)`;;

(* [from mldsa-native mldsa_utils.ml] *)
let NIBBLE_PAIR = define
  `NIBBLE_PAIR (b:byte) =
   [word(val b MOD 16):int16; word(val b DIV 16):int16]`;;

(* [from mldsa-native mldsa_utils.ml] *)
let NIBBLES_OF_BYTES = define
  `NIBBLES_OF_BYTES [] = ([]:(int16)list) /\
   NIBBLES_OF_BYTES (CONS (b:byte) t) =
   APPEND (NIBBLE_PAIR b) (NIBBLES_OF_BYTES t)`;;

(* [from mldsa-native mldsa_utils.ml] *)
let NIBBLES_OF_BYTES_APPEND = prove
 (`!l1 l2. NIBBLES_OF_BYTES(APPEND l1 l2) =
           APPEND (NIBBLES_OF_BYTES l1) (NIBBLES_OF_BYTES l2)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[NIBBLES_OF_BYTES; APPEND; APPEND_ASSOC]);;

(* Splits each input byte into its low and high 4-bit nibbles at the natural *)
(* 4-bit width consumed by the REJ_SAMPLE_ETA{2,4} spec. The output is twice *)
(* the length of the input.                                                  *)

(* [from mldsa-native mldsa_utils.ml] *)
let BYTES_TO_NIBBLES = define
  `BYTES_TO_NIBBLES [] = ([]:(4 word) list) /\
   BYTES_TO_NIBBLES (CONS (b:byte) t) =
   APPEND [word(val b MOD 16):4 word; word(val b DIV 16):4 word]
          (BYTES_TO_NIBBLES t)`;;

(* Bridge lemmas relating the byte-list and nibble-list views, used at the    *)
(* subroutine-spec boundary to state the public spec over a (4 word) list.    *)

(* [from mldsa-native mldsa_utils.ml] *)
let LENGTH_BYTES_TO_NIBBLES = prove
 (`!l:byte list. LENGTH(BYTES_TO_NIBBLES l) = 2 * LENGTH l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[BYTES_TO_NIBBLES; LENGTH; LENGTH_APPEND] THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
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

(* [from mldsa-native mldsa_utils.ml] *)
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

(* ========================================================================= *)
(* Lemmas shared by the AVX2 rejection-sampling proofs (rej_uniform_eta2 and  *)
(* rej_uniform_eta4): popcount / accepted-count bounds, byte/nibble value     *)
(* lemmas, word-slice and sub-list helpers, and modular-split arithmetic.     *)
(* ========================================================================= *)

(* [from mldsa-native mldsa_utils.ml] *)
let VAL_WORD_ZX_64_32 = prove
 (`!a. a < 2 EXP 32 ==> val(word_zx(word a:int64):int32) = a`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `a MOD 2 EXP 64 = a` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]);;

(* Loop-guard fall-through bridge: after `cmp $k, %e_x` with the 64-bit      *)
(* register holding `word a` (a <= k <= 2^32-1), the `ja` (jump-if-above,    *)
(* unsigned >) is NOT taken. The x86 model emits the taken-condition as      *)
(* `~(~EQ \/ ZF)` where EQ is the CF-via-int-equality and ZF the zero test;  *)
(* this lemma proves `~EQ \/ ZF` holds so the taken-condition is false and   *)
(* execution falls through. Stated with `word a:int64` (the register width)  *)
(* and `&`:int (int_of_num) to match the model's flag terms EXACTLY, so      *)
(* X86_STEPS_TAC resolves the conditional RIP automatically when this lemma  *)
(* (instantiated for the right a,k) is in the assumptions. Used at all five  *)
(* cmp/ja sites in the SIMD loop body (the two loop-head guards on ctr<=248  *)
(* and pos<=256, plus the three mid-iteration early-exit checks).            *)

(* [from mldsa-native mldsa_utils.ml] *)
let NIBBLES_OF_BYTES_EQ_BYTES_TO_NIBBLES = prove
 (`!l:byte list.
     NIBBLES_OF_BYTES l = MAP (\x:4 word. word_zx x:int16) (BYTES_TO_NIBBLES l)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[NIBBLES_OF_BYTES; BYTES_TO_NIBBLES; MAP]; ALL_TAC] THEN
  REWRITE_TAC[NIBBLES_OF_BYTES; BYTES_TO_NIBBLES; MAP; APPEND] THEN
  ASM_REWRITE_TAC[NIBBLE_PAIR; MAP; APPEND] THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_4; DIMINDEX_16; word_zx] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REPEAT AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(GSYM MOD_LT) THEN MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

(* Bridge: byte-shape composition equals the public nibble-list spec         *)
(* applied to BYTES_TO_NIBBLES. Used only at the subroutine-spec boundary.   *)

(* [from mldsa-native mldsa_utils.ml] *)
let RB64 = prove
 (`!(a:int64) (s:x86state). read(memory:>bytes64 a) s = word(read(memory:>bytes(a,8)) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bytes64; READ_COMPONENT_COMPOSE; asword; through; read]);;

(* Read an n-byte window at offset k of a byte region known to hold num_of_wordlist L:
   the window holds num_of_wordlist(SUB_LIST(k,n) L).  (NB: HOL parses `k + LENGTH L - k`
   as `k + (LENGTH L - k)` since `-` binds tighter than `+`; the SUB_ADD-style reductions
   here go through ASM_ARITH_TAC with the k+n<=LENGTH L hypothesis.) *)

(* [from mldsa-native mldsa_utils.ml] *)
let BYTES256_PREFIX_WORDLIST = prove
 (`!(A:int64) (V:int256) k (s:x86state).
      read(memory:>bytes256 A) s = V /\ k <= 8
      ==> read(memory:>bytes(A, 4*k)) s = num_of_wordlist(wordlist_of_num k (val V):int32 list)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NUM_OF_WORDLIST_OF_NUM; DIMINDEX_32; READ_COMPONENT_COMPOSE] THEN
  SUBGOAL_THEN `read (bytes(A,32)) (read memory (s:x86state)) = val(V:int256)` ASSUME_TAC THENL
   [UNDISCH_TAC `read(memory:>bytes256 A) s = V` THEN
    REWRITE_TAC[bytes256; READ_COMPONENT_COMPOSE; asword; through; read] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[VAL_WORD; DIMINDEX_256] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[GSYM DIMINDEX_256] THEN
    MP_TAC(ISPECL[`A:int64`;`32`;`read memory (s:x86state)`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[DIMINDEX_256] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:int64`; `32`; `4*k`; `read memory (s:x86state)`] READ_BYTES_MOD) THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 4 * k = 32 * k`] THEN
  SUBGOAL_THEN `MIN 32 (4*k) = 4*k` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

(* The j-th lane (j<k<=8) of wordlist_of_num k (val V) is word_subword V (32j,32). *)

(* [from mldsa-native mldsa_utils.ml] *)
let EL_WORDLIST_OF_NUM_VAL = prove
 (`!(V:int256) k j. j < k
     ==> EL j (wordlist_of_num k (val V):int32 list) = word_subword V (32*j,32)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`wordlist_of_num k (val(V:int256)):int32 list`; `j:num`] EL_NUM_OF_WORDLIST) THEN
  REWRITE_TAC[LENGTH_WORDLIST_OF_NUM; NUM_OF_WORDLIST_OF_NUM; DIMINDEX_32] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[word_subword; DIMINDEX_32; DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC(MESON[] `(word x:int32) = word y ==> word x:int32 = word y`) THEN
  ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN REWRITE_TAC[DIMINDEX_32] THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`; MOD_MOD_REFL] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  SUBGOAL_THEN `MIN (32 * k) (32 * j + 32) = 32 * j + 32` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[]]);;

(* If V's first k lanes match L's elements (and LENGTH L = k <= 8), the low-k-lane digit
   list of V is exactly L. *)

(* [from mldsa-native mldsa_utils.ml] *)
let WORDLIST_OF_NUM_VAL_EQ = prove
 (`!(V:int256) (L:int32 list) k.
      LENGTH L = k /\ (!j. j < k ==> word_subword V (32*j,32) = EL j L)
      ==> wordlist_of_num k (val V) = L`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[LIST_EQ] THEN
  REWRITE_TAC[LENGTH_WORDLIST_OF_NUM] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[EL_WORDLIST_OF_NUM_VAL] THEN ASM_MESON_TAC[]);;

(* Full-width subword identity (used to close the per-lane vpmovsxbd extraction:
   word_subword (word_sx b:int32) (0,32) = word_sx b, with the word_sx(..) taken as W). *)

(* [from mldsa-native mldsa_utils.ml] *)
let SUB_LIST_0_MAP = prove
 (`!(f:A->B) n l. SUB_LIST(0,n) (MAP f l) = MAP f (SUB_LIST(0,n) l)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[SUB_LIST_CLAUSES; MAP] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_LIST_CLAUSES; MAP]);;

(* Nesting/composition of SUB_LIST: a window of width n starting at a, taken from
   a window of width m starting at b, equals the width-n window starting at b+a in
   the original list (provided the inner window covers it and lies inside the list).
   Used to slice the 4-byte sub-iter block SUB_LIST(16i,4) out of the 16-byte chunk
   SUB_LIST(16i,16) when threading per-block facts in the clean loop body. *)

(* [from mldsa-native mldsa_utils.ml] *)
let MAP_FILTER_WORD_NIB = prove
 (`!(f:int16->int32) P (L:num list).
     (!v. MEM v L ==> v < 16)
     ==> MAP f (FILTER P (MAP (word:num->int16) L)) =
         MAP (\v. f(word v)) (FILTER (\v. P(word v)) L)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; FILTER] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASM_CASES_TAC `(P:int16->bool)(word h)` THEN
    ASM_REWRITE_TAC[MAP; th]));;

(* For a list of nibble values (< 16), the int16-word accept predicate         *)
(* val(word v) < 9 agrees with the numeric v < 9, so the two FILTERs coincide. *)

(* [from mldsa-native mldsa_utils.ml] *)
let WZZ_LOW = prove
 (`!(p:int256) j. j < 8
    ==> word_subword (word_zx (word_zx p:int128):int64) (8*j,8):byte = word_subword p (8*j,8)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_zx (p:int256):int128`;`8*j`;`8`]
    (INST_TYPE[`:64`,`:N`;`:128`,`:M`;`:8`,`:P`] WORD_SUBWORD_ZX)) THEN
  MP_TAC(ISPECL [`p:int256`;`8*j`;`8`]
    (INST_TYPE[`:128`,`:N`;`:256`,`:M`;`:8`,`:P`] WORD_SUBWORD_ZX)) THEN
  REWRITE_TAC[DIMINDEX_8;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
  SUBGOAL_THEN `MIN (8*j+8) 128 <= 256 /\ MIN (8*j+8) 256 <= 128 /\ MIN(8*j+8) 128 <= 64` MP_TAC THENL
   [POP_ASSUM MP_TAC THEN ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 -> REWRITE_TAC[th2;th1]))]);;

(* ZZCOLLAPSE: strip word_zx 128<-256<-128 on a low-lane byte subword (j<8); used in    *)
(* the sub-iter store gather subgoal (the vpmovsxbd source g = word_zx(word_zx(...))).  *)

(* [from mldsa-native mldsa_utils.ml] *)
let WORD_BYTE_MOD = prove
 (`!n. word(n MOD 256):byte = word n`,
  GEN_TAC THEN SUBGOAL_THEN `256 = 2 EXP dimindex(:8)` SUBST1_TAC THENL
   [REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV; REWRITE_TAC[WORD_MOD_SIZE]]);;

(* [from mldsa-native mldsa_utils.ml] *)
let WORD_ADD_256_BYTE = prove
 (`!a x. word(a + 256 * x):byte = word a`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM WORD_BYTE_MOD] THEN
  AP_TERM_TAC THEN REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE `256 * x = x * 256`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

(* [from mldsa-native mldsa_utils.ml] *)
let WORD_ZX_BYTE_TO_INT16 = prove
 (`!n. n < 256 ==> word_zx (word n:byte):int16 = word n`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_8; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 256 ==> n < 65536`]);;

(* LENGTH FILTER (val<9) commutes with MAP word_zx (byte->int16).            *)

(* [from mldsa-native mldsa_utils.ml] *)
let ENSURES_STRENGTHEN_POST_X86 = prove
 (`!P (Q:x86state->bool) Q' R.
     ensures x86 P Q' R /\ (!s. Q' s ==> Q s) ==> ensures x86 P Q R`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[ensures] THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `s0:x86state` THEN MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MP_TAC(BETA_RULE(ISPECL [`x86`;
    `\s':x86state. (Q':x86state->bool) s' /\
                   (R:x86state->x86state->bool) (s0:x86state) s'`;
    `\s':x86state. (Q:x86state->bool) s' /\
                   (R:x86state->x86state->bool) (s0:x86state) s'`]
    EVENTUALLY_MONO)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]]);;

(* SUB_LIST length cap: outlist length <= 256, used for SUBROUTINE_CORRECT   *)
(* `outlen <= 256` postcondition.                                            *)

(* [from mldsa-native mldsa_utils.ml] *)
let ADD256_MOD = prove
 (`!a b. a < 256 ==> (a + 256 * b) MOD 256 = a`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]);;

(* [from mldsa-native mldsa_utils.ml] *)
let LOW8_LT = prove
 (`!p:num->bool. bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) < 256`,
  GEN_TAC THEN
  MAP_EVERY (fun k -> MP_TAC(ISPEC (mk_comb(`p:num->bool`,mk_small_numeral k)) BITVAL_BOUND))
    [0;1;2;3;4;5;6;7] THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let MOD_RED = prove
 (`!p:num->bool.
    (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
     16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
     268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) MOD 256 =
    bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
    16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `(bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
     16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
     268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) =
    (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7)) +
    256 * (bitval(p 8) + 2*bitval(p 9) + 4*bitval(p 10) + 8*bitval(p 11) +
     16*bitval(p 12) + 32*bitval(p 13) + 64*bitval(p 14) + 128*bitval(p 15) +
     256*bitval(p 16) + 512*bitval(p 17) + 1024*bitval(p 18) + 2048*bitval(p 19) +
     4096*bitval(p 20) + 8192*bitval(p 21) + 16384*bitval(p 22) + 32768*bitval(p 23) +
     65536*bitval(p 24) + 131072*bitval(p 25) + 262144*bitval(p 26) + 524288*bitval(p 27) +
     1048576*bitval(p 28) + 2097152*bitval(p 29) + 4194304*bitval(p 30) + 8388608*bitval(p 31))`
   SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ADD256_MOD THEN REWRITE_TAC[LOW8_LT]);;

(* [from mldsa-native mldsa_utils.ml] *)
let RAX_NEST_REDUCE = prove
 (`!a b. a + b < 2 EXP 32
     ==> word_zx (word_add (word_zx (word a:int64):int32)
                           (word_zx (word_zx (word b:int32):int64):int32):int32):int64 =
         word(a + b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a < 2 EXP 32 /\ b < 2 EXP 32 /\ a + b < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 2 EXP 32 ==> x < 2 EXP 64`] THEN
  ASM_SIMP_TAC[MOD_LT]);;

(* [from mldsa-native mldsa_utils.ml] *)
let JA_NOT_TAKEN_LE = prove
 (`!a k:num. a <= k /\ k < 2 EXP 32
     ==> ~(&(val(word_zx(word a:int64):int32)):int - &k =
           &(val(word_sub (word_zx(word a:int64):int32) (word k:int32)))) \/
         val(word_sub (word_zx(word a:int64):int32) (word k:int32)) = 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx(word a:int64):int32) = a` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX_64_32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word k:int32) = k` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `a = k:num` THEN ASM_REWRITE_TAC[] THENL
   [DISJ2_TAC THEN
    SUBGOAL_THEN `word_zx(word k:int64):int32 = word k` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[VAL_WORD_ZX_64_32] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC VAL_WORD_EQ THEN
      REWRITE_TAC[DIMINDEX_32] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0]];
    DISJ1_TAC THEN
    SUBGOAL_THEN `a < k` ASSUME_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word_sub (word_zx(word a:int64):int32) (word k:int32)) =
                  a + 2 EXP 32 - k` SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THENL
       [REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC; REFL_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&a:int < &k` MP_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SPEC_TAC(`a + 2 EXP 32 - k`,`m:num`) THEN INT_ARITH_TAC]);;

(* word_add evaluation when both summands are bounded by 248 (and thus the   *)
(* sum is also bounded). Used to compute exact RAX value after `add eax, r9d`*)
(* in sub-iter 1 of the body proof.                                          *)

(* [from mldsa-native mldsa_utils.ml] *)
let NUM_OF_WORDLIST_SINGLETON_INT32 = prove
 (`!(x:int32). num_of_wordlist [x] = val x`,
  REWRITE_TAC[num_of_wordlist] THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let SUB_LIST_256_LE = prove
 (`!(l:int32 list). LENGTH l <= 256 ==> SUB_LIST(0, 256) l = l`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `m = LENGTH (l:int32 list)` THEN
  MP_TAC(ISPECL [`l:int32 list`; `m:num`; `256 - m`; `0`] SUB_LIST_SPLIT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 + a = a`] THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= 256 ==> m + (256 - m) = 256`] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[SUB_LIST_LENGTH; SUB_LIST_TRIVIAL; LE_REFL; APPEND_NIL] THEN
  UNDISCH_TAC `LENGTH (l:int32 list) = m` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[SUB_LIST_LENGTH] THEN
  MP_TAC(ISPECL [`l:int32 list`; `LENGTH (l:int32 list)`;
                 `256 - LENGTH (l:int32 list)`] SUB_LIST_TRIVIAL) THEN
  REWRITE_TAC[LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[APPEND_NIL]);;

(* When the input has its full known length, SUB_LIST(0, that length) is a   *)
(* no-op: applies to LENGTH inlist = 272.                                    *)

(* [from mldsa-native mldsa_utils.ml] *)
let PURGE_STALE_STATES_TAC names =
  let rec refs_stale tm = match tm with
    | Comb(Comb(Const("read",_),_),Var(nm,_)) when List.mem nm names -> true
    | Comb(a,b) -> refs_stale a || refs_stale b | Abs(_,b) -> refs_stale b | _ -> false in
  REPEAT(FIRST_X_ASSUM(fun th -> if refs_stale (concl th) then ALL_TAC else failwith "keep"));;

(* [from mldsa-native mldsa_utils.ml] *)
let DROP_WORDJOIN_TAC : tactic = fun (asl,w) ->
  (REPEAT(FIRST_X_ASSUM(fun th ->
     if can (find_term (fun u -> match u with Const("word_join",_) -> true | _ -> false)) (concl th)
     then ALL_TAC else failwith "keep"))) (asl,w);;

(* [from mldsa-native mldsa_utils.ml] *)
let VAL_WORD_BYTE_LT256 = prove
 (`!n. n < 256 ==> val(word n:byte) = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]);;

(* [from mldsa-native mldsa_utils.ml] *)
let BYTE_DIV16_LT = prove
 (`!b:byte. val b DIV 16 < 256`,
  GEN_TAC THEN MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC `b:byte` VAL_BOUND)) THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let BYTE_MOD16_LT = prove
 (`!b:byte. val b MOD 16 < 256`,
  GEN_TAC THEN MP_TAC(SPECL[`val(b:byte)`;`16`] MOD_LT_EQ) THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let MM64_256 = prove
 (`!a. a MOD 18446744073709551616 MOD 256 = a MOD 256`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
    [ARITH_RULE `18446744073709551616 = 256 * 72057594037927936`] THEN
  REWRITE_TAC[MOD_MOD]);;

(* a MOD 2^32 MOD 2^64 = a MOD 2^32                                          *)

(* [from mldsa-native mldsa_utils.ml] *)
let MM32_64 = prove
 (`!a. a MOD 4294967296 MOD 18446744073709551616 = a MOD 4294967296`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL[`a:num`;`4294967296`] MOD_LT_EQ) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* (x DIV 2^8) MOD 2^8 = (x MOD 2^16) DIV 2^8                                *)

(* [from mldsa-native mldsa_utils.ml] *)
let divmod_swap = prove
 (`!x. (x DIV 2 EXP 8) MOD 2 EXP 8 = (x MOD 2 EXP 16) DIV 2 EXP 8`,
  GEN_TAC THEN REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV);;

(* (S MOD 2^32 DIV 256) MOD 256 = (S DIV 256) MOD 256                        *)

(* [from mldsa-native mldsa_utils.ml] *)
let MM32_DIV256 = prove
 (`!S. (S MOD 4294967296 DIV 256) MOD 256 = (S DIV 256) MOD 256`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`; ARITH_RULE `256 = 2 EXP 8`] THEN
  REWRITE_TAC[divmod_swap] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* mask8b = word_zx(word_ushr(word_zx(word_zx(word S:int32):int64):int32) 8):int64,
   the R8-shifted-by-8 value at the start of sub-iter 2.  Its low byte = byte 1 of S. *)

(* [from mldsa-native mldsa_utils.ml] *)
let LOW16_LT = prove
 (`!p:num->bool. bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) < 65536`,
  GEN_TAC THEN
  MAP_EVERY (fun k -> MP_TAC(ISPEC (mk_comb(`p:num->bool`,mk_small_numeral k)) BITVAL_BOUND))
    [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15] THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let MASK_USHR8_STEP = prove
 (`!m:int64. val(word_zx(word_ushr(word_zx m:int32) 8):int64) MOD 256 = (val m DIV 256) MOD 256`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[MM64_256; MM32_DIV256]);;

(* [from mldsa-native mldsa_utils.ml] *)
let DIVLT = prove(`!a k e. a < e ==> a DIV k < e`,
  REPEAT STRIP_TAC THEN TRANS_TAC LET_TRANS `a:num` THEN ASM_REWRITE_TAC[DIV_LE]);;

(* [from mldsa-native mldsa_utils.ml] *)
let divmod_swap16 = prove(`!x. (x DIV 2 EXP 16) MOD 2 EXP 8 = (x MOD 2 EXP 24) DIV 2 EXP 16`,
  GEN_TAC THEN REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV);;

(* [from mldsa-native mldsa_utils.ml] *)
let divmod_swap24 = prove(`!x. (x DIV 2 EXP 24) MOD 2 EXP 8 = (x MOD 2 EXP 32) DIV 2 EXP 24`,
  GEN_TAC THEN REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV);;

(* full val of the byte-1 / byte-2 masks (mask8b = ushr8 once; mask8c = ushr8 twice) *)

(* [from mldsa-native mldsa_utils.ml] *)
let VAL_MASK8B = prove
 (`!S. val(word_zx(word_ushr(word_zx(word_zx(word S:int32):int64):int32) 8):int64) = (S MOD 4294967296) DIV 256`,
  GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`; ARITH_RULE `256 = 2 EXP 8`] THEN
  MP_TAC(SPECL[`S:num`;`2 EXP 32`] MOD_LT_EQ) THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  ABBREV_TAC `q = S MOD 2 EXP 32` THEN DISCH_TAC THEN
  SUBGOAL_THEN `q < 2 EXP 64` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP 32` THEN ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `q MOD 2 EXP 64 MOD 2 EXP 32 = q` SUBST1_TAC THENL
   [ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN TRANS_TAC LET_TRANS `q:num` THEN REWRITE_TAC[DIV_LE] THEN ASM_REWRITE_TAC[]);;

(* [from mldsa-native mldsa_utils.ml] *)
let VAL_MASK8C = prove
 (`!S. val(word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word S:int32):int64):int32) 8):int64):int32) 8):int64) =
       (S MOD 4294967296) DIV 65536`,
  GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`] THEN
  MP_TAC(SPECL[`S:num`;`2 EXP 32`] MOD_LT_EQ) THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  ABBREV_TAC `q = S MOD 2 EXP 32` THEN DISCH_TAC THEN
  SUBGOAL_THEN `q < 2 EXP 64 /\ q DIV 2 EXP 8 < 2 EXP 64 /\ q DIV 2 EXP 8 < 2 EXP 32 /\
                q DIV 2 EXP 8 DIV 2 EXP 8 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `q < 2 EXP 64 /\ q < 2 EXP 32` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN TRANS_TAC LTE_TRANS `2 EXP 32` THEN ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DIVLT]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV);;

(* mask byte for sub-iter 3 (double ushr) = byte 2 ; sub-iter 4 (triple ushr) = byte 3 *)

(* [from mldsa-native mldsa_utils.ml] *)
let SUMTERM_BYTE23 = `(bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
   16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
   256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
   4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
   65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
   1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
   16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
   268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31))`;;

(* [from mldsa-native mldsa_utils.ml] *)
let R_EQ = prove(`val (word_zx (word_zx (word (val (mask8:int64) MOD 256):byte):int32):int64):num = val (mask8:int64) MOD 256`,
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* [from mldsa-native mldsa_utils.ml] *)
let RLT = prove(`val (mask8:int64) MOD 256 < 256`, REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let SUBWORD_ZX_LOW = prove
 (`!(y:(M)word) lo wid. lo + wid <= dimindex(:P)
     ==> word_subword (word_zx y:(P)word) (lo,wid):(N)word = word_subword y (lo,wid)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_ZX] THEN
  ASM_CASES_TAC `k < MIN wid (dimindex(:N))` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[ARITH_RULE `k < MIN a b <=> k < a /\ k < b`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `lo + k < dimindex(:P)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let ZX_128_256_128 = prove(`!(x:(128)word). word_zx(word_zx x:(256)word):(128)word = x`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_128] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[BIT_WORD_ZX; DIMINDEX_128; DIMINDEX_256] THEN
  SUBGOAL_THEN `k < 128 /\ k < 256` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let SUBWORD_USHR = prove
 (`!(x:(M)word) n lo wid. word_subword (word_ushr x n) (lo,wid):(N)word = word_subword x (lo+n,wid)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_USHR] THEN
  REWRITE_TAC[ARITH_RULE `(lo + k) + n = (lo + n) + k`]);;


(* --- prefix_g_full_tac ---                                                 *)

(* [from mldsa-native mldsa_utils.ml] *)
let DIVMOD256_SPLIT = prove
 (`!a b c. a < 256 /\ b < 256 ==> (a + 256 * b + 65536 * c) DIV 256 MOD 256 = b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a + 256 * b + 65536 * c) DIV 256 = b + 256 * c` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `a:num` THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `b + 256 * c = c * 256 + b`; MOD_MULT_ADD] THEN
    ASM_SIMP_TAC[MOD_LT]]);;

(* [from mldsa-native mldsa_utils.ml] *)
let R_EQ_B = prove(`val (word_zx (word_zx (word (val (mask8b:int64) MOD 256):byte):int32):int64):num = val (mask8b:int64) MOD 256`,
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* [from mldsa-native mldsa_utils.ml] *)
let RLT_B = prove(`val (mask8b:int64) MOD 256 < 256`, REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let DIVMOD65536_SPLIT = prove
 (`!a b c. a < 65536 /\ b < 256 ==> (a + 65536 * b + 16777216 * c) DIV 65536 MOD 256 = b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a + 65536 * b + 16777216 * c) DIV 65536 = b + 256 * c` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `a:num` THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `b + 256 * c = c * 256 + b`; MOD_MULT_ADD] THEN ASM_SIMP_TAC[MOD_LT]]);;

(* [from mldsa-native mldsa_utils.ml] *)
let R_EQ_C = prove(`val (word_zx (word_zx (word (val (mask8c:int64) MOD 256):byte):int32):int64):num = val (mask8c:int64) MOD 256`,
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* [from mldsa-native mldsa_utils.ml] *)
let RLT_C = prove(`val (mask8c:int64) MOD 256 < 256`, REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let DIVMOD16777216_SPLIT = prove
 (`!a b. a < 16777216 ==> (a + 16777216 * b) DIV 16777216 MOD 256 = b MOD 256`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a + 16777216 * b) DIV 16777216 = b` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `a:num` THEN ASM_ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let R_EQ_D = prove(`val (word_zx (word_zx (word (val (mask8d:int64) MOD 256):byte):int32):int64):num = val (mask8d:int64) MOD 256`,
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* [from mldsa-native mldsa_utils.ml] *)
let RLT_D = prove(`val (mask8d:int64) MOD 256 < 256`, REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let MM64_32 = prove(`!a. a MOD 2 EXP 64 MOD 2 EXP 32 = a MOD 2 EXP 32`,
  GEN_TAC THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* [from mldsa-native mldsa_utils.ml] *)
let LENGTH_BUTLAST_GEN = prove
 (`!l:A list. ~(l = []) ==> LENGTH l = LENGTH(BUTLAST l) + 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `l:A list` APPEND_BUTLAST_LAST) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC);;


let mldsa_rej_uniform_eta2_mc = define_assert_from_elf
  "mldsa_rej_uniform_eta2_mc" "x86/mldsa/mldsa_rej_uniform_eta2_VARIABLE_TIME.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x41; 0xb8; 0x0f; 0x0f; 0x0f; 0x0f;
                           (* MOV (% r8d) (Imm32 (word 252645135)) *)
  0xc4; 0xc1; 0x79; 0x6e; 0xd8;
                           (* VMOVD (%_% xmm3) (% r8d) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xdb;
                           (* VPBROADCASTD (%_% ymm3) (%_% xmm3) *)
  0x41; 0xb8; 0x02; 0x02; 0x02; 0x02;
                           (* MOV (% r8d) (Imm32 (word 33686018)) *)
  0xc4; 0xc1; 0x79; 0x6e; 0xe0;
                           (* VMOVD (%_% xmm4) (% r8d) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xe4;
                           (* VPBROADCASTD (%_% ymm4) (%_% xmm4) *)
  0x41; 0xb8; 0x0f; 0x0f; 0x0f; 0x0f;
                           (* MOV (% r8d) (Imm32 (word 252645135)) *)
  0xc4; 0xc1; 0x79; 0x6e; 0xe8;
                           (* VMOVD (%_% xmm5) (% r8d) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xed;
                           (* VPBROADCASTD (%_% ymm5) (%_% xmm5) *)
  0x41; 0xb8; 0x60; 0xe6; 0xff; 0xff;
                           (* MOV (% r8d) (Imm32 (word 4294960736)) *)
  0xc4; 0xc1; 0x49; 0xc4; 0xf0; 0x00;
                           (* VPINSRW (%_% xmm6) (%_% xmm6) (% r8d) (Imm8 (word 0)) *)
  0xc4; 0xe2; 0x7d; 0x79; 0xf6;
                           (* VPBROADCASTW (%_% ymm6) (%_% xmm6) *)
  0x41; 0xb8; 0x05; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 5)) *)
  0xc4; 0xc1; 0x41; 0xc4; 0xf8; 0x00;
                           (* VPINSRW (%_% xmm7) (%_% xmm7) (% r8d) (Imm8 (word 0)) *)
  0xc4; 0xe2; 0x7d; 0x79; 0xff;
                           (* VPBROADCASTW (%_% ymm7) (%_% xmm7) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x3d; 0xf8; 0x00; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 248)) *)
  0x0f; 0x87; 0x2e; 0x01; 0x00; 0x00;
                           (* JA (Imm32 (word 302)) *)
  0x83; 0xf9; 0x78;        (* CMP (% ecx) (Imm8 (word 120)) *)
  0x0f; 0x87; 0x25; 0x01; 0x00; 0x00;
                           (* JA (Imm32 (word 293)) *)
  0xc4; 0xe2; 0x7d; 0x30; 0x04; 0x0e;
                           (* VPMOVZXBW (%_% ymm0) (Memop Word128 (%%% (rsi,0,rcx))) *)
  0xc5; 0xf5; 0x71; 0xf0; 0x04;
                           (* VPSLLW (%_% ymm1) (%_% ymm0) (Imm8 (word 4)) *)
  0xc5; 0xfd; 0xeb; 0xc1;  (* VPOR (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xfd; 0xf8; 0xcd;  (* VPSUBB (%_% ymm1) (%_% ymm0) (%_% ymm5) *)
  0xc5; 0xdd; 0xf8; 0xc0;  (* VPSUBB (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0x7d; 0xd7; 0xc1;  (* VPMOVMSKB (% r8d) (%_% ymm1) *)
  0xc4; 0xc3; 0x7d; 0x39; 0xc0; 0x00;
                           (* VEXTRACTI128 (%_% xmm8) (%_% ymm0) (Imm8 (word 0)) *)
  0x45; 0x0f; 0xb6; 0xd0;  (* MOVZX (% r10d) (% r8b) *)
  0xc4; 0x21; 0x7a; 0x7e; 0x0c; 0xd2;
                           (* VMOVQ (%_% xmm9) (Memop Quadword (%%% (rdx,3,r10))) *)
  0xc4; 0x42; 0x39; 0x00; 0xc9;
                           (* VPSHUFB (%_% xmm9) (%_% xmm8) (%_% xmm9) *)
  0xc4; 0xc2; 0x7d; 0x21; 0xc9;
                           (* VPMOVSXBD (%_% ymm1) (%_% xmm9) *)
  0xc4; 0xe2; 0x75; 0x0b; 0xd6;
                           (* VPMULHRSW (%_% ymm2) (%_% ymm1) (%_% ymm6) *)
  0xc5; 0xed; 0xd5; 0xd7;  (* VPMULLW (%_% ymm2) (%_% ymm2) (%_% ymm7) *)
  0xc5; 0xf5; 0xfe; 0xca;  (* VPADDD (%_% ymm1) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0xfe; 0x7f; 0x0c; 0x87;
                           (* VMOVDQU (Memop Word256 (%%% (rdi,2,rax))) (%_% ymm1) *)
  0xf3; 0x45; 0x0f; 0xb8; 0xca;
                           (* POPCNT (% r9d) (% r10d) *)
  0x44; 0x01; 0xc8;        (* ADD (% eax) (% r9d) *)
  0x41; 0xc1; 0xe8; 0x08;  (* SHR (% r8d) (Imm8 (word 8)) *)
  0x83; 0xc1; 0x04;        (* ADD (% ecx) (Imm8 (word 4)) *)
  0x3d; 0xf8; 0x00; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 248)) *)
  0x0f; 0x87; 0xc0; 0x00; 0x00; 0x00;
                           (* JA (Imm32 (word 192)) *)
  0xc4; 0xc1; 0x39; 0x73; 0xd8; 0x08;
                           (* VPSRLDQ (%_% xmm8) (%_% xmm8) (Imm8 (word 8)) *)
  0x45; 0x0f; 0xb6; 0xd0;  (* MOVZX (% r10d) (% r8b) *)
  0xc4; 0x21; 0x7a; 0x7e; 0x0c; 0xd2;
                           (* VMOVQ (%_% xmm9) (Memop Quadword (%%% (rdx,3,r10))) *)
  0xc4; 0x42; 0x39; 0x00; 0xc9;
                           (* VPSHUFB (%_% xmm9) (%_% xmm8) (%_% xmm9) *)
  0xc4; 0xc2; 0x7d; 0x21; 0xc9;
                           (* VPMOVSXBD (%_% ymm1) (%_% xmm9) *)
  0xc4; 0xe2; 0x75; 0x0b; 0xd6;
                           (* VPMULHRSW (%_% ymm2) (%_% ymm1) (%_% ymm6) *)
  0xc5; 0xed; 0xd5; 0xd7;  (* VPMULLW (%_% ymm2) (%_% ymm2) (%_% ymm7) *)
  0xc5; 0xf5; 0xfe; 0xca;  (* VPADDD (%_% ymm1) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0xfe; 0x7f; 0x0c; 0x87;
                           (* VMOVDQU (Memop Word256 (%%% (rdi,2,rax))) (%_% ymm1) *)
  0xf3; 0x45; 0x0f; 0xb8; 0xca;
                           (* POPCNT (% r9d) (% r10d) *)
  0x44; 0x01; 0xc8;        (* ADD (% eax) (% r9d) *)
  0x41; 0xc1; 0xe8; 0x08;  (* SHR (% r8d) (Imm8 (word 8)) *)
  0x83; 0xc1; 0x04;        (* ADD (% ecx) (Imm8 (word 4)) *)
  0x3d; 0xf8; 0x00; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 248)) *)
  0x77; 0x7e;              (* JA (Imm8 (word 126)) *)
  0xc4; 0xc3; 0x7d; 0x39; 0xc0; 0x01;
                           (* VEXTRACTI128 (%_% xmm8) (%_% ymm0) (Imm8 (word 1)) *)
  0x45; 0x0f; 0xb6; 0xd0;  (* MOVZX (% r10d) (% r8b) *)
  0xc4; 0x21; 0x7a; 0x7e; 0x0c; 0xd2;
                           (* VMOVQ (%_% xmm9) (Memop Quadword (%%% (rdx,3,r10))) *)
  0xc4; 0x42; 0x39; 0x00; 0xc9;
                           (* VPSHUFB (%_% xmm9) (%_% xmm8) (%_% xmm9) *)
  0xc4; 0xc2; 0x7d; 0x21; 0xc9;
                           (* VPMOVSXBD (%_% ymm1) (%_% xmm9) *)
  0xc4; 0xe2; 0x75; 0x0b; 0xd6;
                           (* VPMULHRSW (%_% ymm2) (%_% ymm1) (%_% ymm6) *)
  0xc5; 0xed; 0xd5; 0xd7;  (* VPMULLW (%_% ymm2) (%_% ymm2) (%_% ymm7) *)
  0xc5; 0xf5; 0xfe; 0xca;  (* VPADDD (%_% ymm1) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0xfe; 0x7f; 0x0c; 0x87;
                           (* VMOVDQU (Memop Word256 (%%% (rdi,2,rax))) (%_% ymm1) *)
  0xf3; 0x45; 0x0f; 0xb8; 0xca;
                           (* POPCNT (% r9d) (% r10d) *)
  0x44; 0x01; 0xc8;        (* ADD (% eax) (% r9d) *)
  0x41; 0xc1; 0xe8; 0x08;  (* SHR (% r8d) (Imm8 (word 8)) *)
  0x83; 0xc1; 0x04;        (* ADD (% ecx) (Imm8 (word 4)) *)
  0x3d; 0xf8; 0x00; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 248)) *)
  0x77; 0x3c;              (* JA (Imm8 (word 60)) *)
  0xc4; 0xc1; 0x39; 0x73; 0xd8; 0x08;
                           (* VPSRLDQ (%_% xmm8) (%_% xmm8) (Imm8 (word 8)) *)
  0x45; 0x0f; 0xb6; 0xd0;  (* MOVZX (% r10d) (% r8b) *)
  0xc4; 0x21; 0x7a; 0x7e; 0x0c; 0xd2;
                           (* VMOVQ (%_% xmm9) (Memop Quadword (%%% (rdx,3,r10))) *)
  0xc4; 0x42; 0x39; 0x00; 0xc9;
                           (* VPSHUFB (%_% xmm9) (%_% xmm8) (%_% xmm9) *)
  0xc4; 0xc2; 0x7d; 0x21; 0xc9;
                           (* VPMOVSXBD (%_% ymm1) (%_% xmm9) *)
  0xc4; 0xe2; 0x75; 0x0b; 0xd6;
                           (* VPMULHRSW (%_% ymm2) (%_% ymm1) (%_% ymm6) *)
  0xc5; 0xed; 0xd5; 0xd7;  (* VPMULLW (%_% ymm2) (%_% ymm2) (%_% ymm7) *)
  0xc5; 0xf5; 0xfe; 0xca;  (* VPADDD (%_% ymm1) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0xfe; 0x7f; 0x0c; 0x87;
                           (* VMOVDQU (Memop Word256 (%%% (rdi,2,rax))) (%_% ymm1) *)
  0xf3; 0x45; 0x0f; 0xb8; 0xca;
                           (* POPCNT (% r9d) (% r10d) *)
  0x44; 0x01; 0xc8;        (* ADD (% eax) (% r9d) *)
  0x83; 0xc1; 0x04;        (* ADD (% ecx) (Imm8 (word 4)) *)
  0xe9; 0xc7; 0xfe; 0xff; 0xff;
                           (* JMP (Imm32 (word 4294966983)) *)
  0x3d; 0x00; 0x01; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 256)) *)
  0x0f; 0x83; 0x84; 0x00; 0x00; 0x00;
                           (* JAE (Imm32 (word 132)) *)
  0x81; 0xf9; 0x88; 0x00; 0x00; 0x00;
                           (* CMP (% ecx) (Imm32 (word 136)) *)
  0x73; 0x7c;              (* JAE (Imm8 (word 124)) *)
  0x44; 0x0f; 0xb6; 0x1c; 0x0e;
                           (* MOVZX (% r11d) (Memop Byte (%%% (rsi,0,rcx))) *)
  0xff; 0xc1;              (* INC (% ecx) *)
  0x45; 0x89; 0xda;        (* MOV (% r10d) (% r11d) *)
  0x41; 0x83; 0xe2; 0x0f;  (* AND (% r10d) (Imm8 (word 15)) *)
  0x41; 0x83; 0xfa; 0x0f;  (* CMP (% r10d) (Imm8 (word 15)) *)
  0x73; 0x2b;              (* JAE (Imm8 (word 43)) *)
  0x45; 0x89; 0xd3;        (* MOV (% r11d) (% r10d) *)
  0x45; 0x69; 0xdb; 0xcd; 0x00; 0x00; 0x00;
                           (* IMUL3 (% r11d) (% r11d,Imm32 (word 205)) *)
  0x41; 0xc1; 0xeb; 0x0a;  (* SHR (% r11d) (Imm8 (word 10)) *)
  0x45; 0x6b; 0xdb; 0x05;  (* IMUL3 (% r11d) (% r11d,Imm8 (word 5)) *)
  0x45; 0x29; 0xda;        (* SUB (% r10d) (% r11d) *)
  0x41; 0xbb; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% r11d) (Imm32 (word 2)) *)
  0x45; 0x29; 0xd3;        (* SUB (% r11d) (% r10d) *)
  0x44; 0x89; 0x1c; 0x87;  (* MOV (Memop Doubleword (%%% (rdi,2,rax))) (% r11d) *)
  0xff; 0xc0;              (* INC (% eax) *)
  0x3d; 0x00; 0x01; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 256)) *)
  0x73; 0x3d;              (* JAE (Imm8 (word 61)) *)
  0x44; 0x0f; 0xb6; 0x5c; 0x0e; 0xff;
                           (* MOVZX (% r11d) (Memop Byte (%%%% (rsi,0,rcx,-- &1))) *)
  0x41; 0xc1; 0xeb; 0x04;  (* SHR (% r11d) (Imm8 (word 4)) *)
  0x41; 0x83; 0xe3; 0x0f;  (* AND (% r11d) (Imm8 (word 15)) *)
  0x41; 0x83; 0xfb; 0x0f;  (* CMP (% r11d) (Imm8 (word 15)) *)
  0x73; 0x9a;              (* JAE (Imm8 (word 154)) *)
  0x45; 0x89; 0xda;        (* MOV (% r10d) (% r11d) *)
  0x45; 0x69; 0xd2; 0xcd; 0x00; 0x00; 0x00;
                           (* IMUL3 (% r10d) (% r10d,Imm32 (word 205)) *)
  0x41; 0xc1; 0xea; 0x0a;  (* SHR (% r10d) (Imm8 (word 10)) *)
  0x45; 0x6b; 0xd2; 0x05;  (* IMUL3 (% r10d) (% r10d,Imm8 (word 5)) *)
  0x45; 0x29; 0xd3;        (* SUB (% r11d) (% r10d) *)
  0x41; 0xba; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 2)) *)
  0x45; 0x29; 0xda;        (* SUB (% r10d) (% r11d) *)
  0x44; 0x89; 0x14; 0x87;  (* MOV (Memop Doubleword (%%% (rdi,2,rax))) (% r10d) *)
  0xff; 0xc0;              (* INC (% eax) *)
  0xe9; 0x71; 0xff; 0xff; 0xff;
                           (* JMP (Imm32 (word 4294967153)) *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

let mldsa_rej_uniform_eta2_tmc = define_trimmed
  "mldsa_rej_uniform_eta2_tmc" mldsa_rej_uniform_eta2_mc;;

(* ========================================================================= *)
(* Supporting spec lemmas + byte-shape interior aliases (CORRECT).           *)
(* ========================================================================= *)
(* The public spec REJ_SAMPLE_ETA2 (common/mldsa_specs.ml) takes a nibble list. *)
(* The proof below is written against the byte-list shape, so we introduce a *)
(* byte-shape alias REJ_SAMPLE_ETA2_BYTES and bridge to the public spec at the *)
(* subroutine-spec boundary via REJ_SAMPLE_ETA2_BYTES_EQ.                    *)

(* ------------------------------------------------------------------------- *)
(* Model of the AVX2 VPMULHRSW (packed multiply high with round-and-scale)   *)
(* on a single int16 lane: (x*y >> 14) + 1, taking the high 16 bits.  Used to *)
(* express the eta=2 mod-5 reduction (vpmulhrsw/vpmullw/vpaddd) at the store. *)
(* ------------------------------------------------------------------------- *)
let mulhrs_eta2 = new_definition
  `mulhrs_eta2 (x:int16) (y:int16) : int16 =
     word_subword
       (word_add (word_ushr (word_mul (word_sx x) (word_sx y):int32) 14)
                 (word 1:int32))
       (1,16)`;;

(* ========================================================================= *)
(* eta2 CORRECT: spec/algebra lemmas.                                        *)
(* Accept threshold is nibble < 15; the coefficient map is eta2's mod-5 form. *)
(* The int16-nibble path is developed as REJ_SAMPLE_ETA2_BYTES, with the     *)
(* shortcut form (REJ_SAMPLE_ETA2 (BYTES_TO_NIBBLES l)) recovered as         *)
(* REJ_SAMPLE_ETA2_BYTES_EQ.                                                 *)
(* ========================================================================= *)

(* Internal byte->nibble decomposition stored in int16 lanes (matching the   *)
(* SIMD register layout used by the loop body). Accept nibble n iff n < 15.  *)
let REJ_NIBBLES_ETA2 = define
  `REJ_NIBBLES_ETA2 (l:byte list) =
   FILTER (\x:int16. val x < 15) (NIBBLES_OF_BYTES l)`;;

(* int16-nibble-path sample: map each accepted nibble to its eta=2           *)
(* coefficient  2 - (n MOD 5)  in [-2,2], stored sign-extended into int32.   *)
let REJ_SAMPLE_ETA2_BYTES = define
  `REJ_SAMPLE_ETA2_BYTES (l:byte list) =
   MAP (\x:int16. word_sx(word_sub (word 2:int16) (word_umod x (word 5))):int32)
       (REJ_NIBBLES_ETA2 l)`;;

(* Conversion lemma: NIBBLES_OF_BYTES (int16 list) =                         *)
(* MAP word_zx of BYTES_TO_NIBBLES (4 word list).                            *)
let REJ_SAMPLE_ETA2_BYTES_EQ = prove
 (`!l:byte list. REJ_SAMPLE_ETA2_BYTES l =
                 REJ_SAMPLE_ETA2 (BYTES_TO_NIBBLES l)`,
  GEN_TAC THEN
  REWRITE_TAC[REJ_SAMPLE_ETA2_BYTES; REJ_NIBBLES_ETA2; REJ_SAMPLE_ETA2;
              NIBBLES_OF_BYTES_EQ_BYTES_TO_NIBBLES] THEN
  REWRITE_TAC[FILTER_MAP; o_DEF; GSYM MAP_o] THEN
  SUBGOAL_THEN `!x:4 word. val (word_zx x:int16) = val x`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC VAL_WORD_ZX THEN
    REWRITE_TAC[DIMINDEX_4; DIMINDEX_16] THEN ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`BYTES_TO_NIBBLES (l:byte list)`,`xs:(4 word) list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `!x:4 word. val x < 15
      ==> word_sx (word_sub (word 2:int16)
                             (word_umod (word_zx x:int16) (word 5))):int32 =
          word_sx (word_sub (word 2:4 word)
                             (word_umod x (word 5:4 word))):int32`
   (fun th -> ASM_MESON_TAC[th]) THEN
  SUBGOAL_THEN
   `!n. n < 15
      ==> word_sx (word_sub (word 2:int16)
                             (word_umod (word_zx (word n:4 word):int16)
                                        (word 5))):int32 =
          word_sx (word_sub (word 2:4 word)
                             (word_umod (word n:4 word) (word 5:4 word))):int32`
   MP_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM WORD_VAL] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `val (x:4 word):num`) THEN
  ANTS_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_4] THEN
    MP_TAC(ISPEC `x:4 word` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_4] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(SPECL [`val(x:4 word):num`; `16`] MOD_LT) THEN
    ASM_SIMP_TAC[LT_TRANS] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_VAL]);;

(* ========================================================================= *)
(* Shared rejection-sampling lemmas (gather / table / store-compaction),     *)
(* independent of the eta parameter.                                         *)
(* ========================================================================= *)

let TABLE_ENTRY = define
 `TABLE_ENTRY (m:byte) = SUB_LIST(8 * val m, 8) (mldsa_rej_uniform_table:byte list)`;;

(* bytes64 read = word of the 8-byte little-endian value.                    *)

let READ_BYTES_SLICE = prove
 (`!(a:int64) k n (L:byte list) (s:x86state).
      read(memory:>bytes(a,LENGTH L)) s = num_of_wordlist L /\ k + n <= LENGTH L
      ==> read(memory:>bytes(word_add a (word k), n)) s = num_of_wordlist(SUB_LIST(k,n) L)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k + (LENGTH(L:byte list) - k) = LENGTH L` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `n + (LENGTH(L:byte list) - (k+n)) = LENGTH L - k` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `read(memory:>bytes(word_add a (word k), LENGTH(L:byte list) - k)) s =
                num_of_wordlist(SUB_LIST(k, LENGTH L - k) L)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `a:int64`; `s:x86state`;
       `SUB_LIST(0,k) (L:byte list)`; `SUB_LIST(k, LENGTH(L:byte list) - k) L`;
       `k:num`; `LENGTH(L:byte list) - k`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
    REWRITE_TAC[DIMINDEX_8; LENGTH_SUB_LIST; SUB_0] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[SUB_LIST_TOPSPLIT] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `word_add a (word k):int64`; `s:x86state`;
     `SUB_LIST(k,n) (L:byte list)`; `SUB_LIST(k+n, LENGTH(L:byte list) - (k+n)) L`;
     `n:num`; `LENGTH(L:byte list) - (k + n)`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
  REWRITE_TAC[DIMINDEX_8; LENGTH_SUB_LIST] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:byte list`; `n:num`; `LENGTH(L:byte list) - (k+n)`; `k:num`] SUB_LIST_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* NOTE: in the clean loop body, the stepped vpmovsxbd output `read YMM1 sN` (a word_join
   nest of word_sx over the low-8 bytes of word_zx(word_zx pshuf)) is rewritten to the
   canonical `usimd8 (\b. word_sx b) (word_zx(word_zx pshuf))` form in-context (where the
   term is fully typed by the simulator) via `REWRITE_TAC[usimd8;usimd4;usimd2] THEN
   SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_*;ARITH] THEN CONV_TAC NUM_REDUCE_CONV`, after which
   the committed VPMOVSXBD_LANE_EXTRACT gives each int32 lane = word_sx of the pshuf byte.
   (Kept as an in-body step rather than a standalone lemma because the
   word_join associativity/widths are simulator-determined.) *)

(* Store-value memory lemma: the first k int32 lanes of a 256-bit store at A read back as
   num_of_wordlist L, where L is the int32 list whose elements are V's lanes.  This is the
   bridge from the vmovdqu writeback to the REJ_SAMPLE block: with V = vpmovsxbd output and
   L = REJ_SAMPLE_ETA2_BYTES block (via SUBITER1_VALUE + VPMOVSXBD_LANE_EXTRACT giving
   word_subword V (32j,32) = EL j L), this yields the sub-iter store memory postcondition. *)

let STORE_BYTES256_NUM_OF_WORDLIST = prove
 (`!(A:int64) (V:int256) (L:int32 list) k (s:x86state).
      read(memory:>bytes256 A) s = V /\ LENGTH L = k /\ k <= 8 /\
      (!j. j < k ==> word_subword V (32*j,32):int32 = EL j L)
      ==> read(memory:>bytes(A, 4*k)) s = num_of_wordlist L`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:int64`; `V:int256`; `k:num`; `s:x86state`] BYTES256_PREFIX_WORDLIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC WORDLIST_OF_NUM_VAL_EQ THEN ASM_REWRITE_TAC[]);;

(* The vmovq table load: with the table memory invariant, reading the 8-byte entry at
   index r (byte offset 8r) yields word(num_of_wordlist(TABLE_ENTRY(word r))) — i.e. the
   gather-control word for mask r.  Bridge (1) of the sub-iter store value. *)

let TABLE_VMOVQ_READ = prove
 (`!(table:int64) r (s:x86state).
      read(memory:>bytes(table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\ r < 256
      ==> read(memory:>bytes64(word_add table (word(8*r)))) s =
          word(num_of_wordlist(TABLE_ENTRY(word r:byte)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RB64; TABLE_ENTRY] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `LENGTH(mldsa_rej_uniform_table:byte list) = 2048` ASSUME_TAC THENL
   [REWRITE_TAC[mldsa_rej_uniform_table; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `val(word r:byte) = r` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_8] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`table:int64`; `8*r`; `8`; `mldsa_rej_uniform_table:byte list`; `s:x86state`]
    READ_BYTES_SLICE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_ACCEPT_TAC]);;

let ACC_IDX = define
 `ACC_IDX (m:byte) = FILTER (\i. bit i m) [0;1;2;3;4;5;6;7]`;;

(* Keystone table-correspondence lemma: for every mask m, the first          *)
(* |ACC_IDX m| bytes of the table entry table[m] are exactly the accepted    *)
(* (set-bit) positions of m, in increasing order. This is what makes the     *)
(* pshufb gather compact the accepted nibbles to the front: gathering the    *)
(* source vector at these table indices reads precisely the accepted lanes.  *)
(* Proved by exhaustive 256-mask evaluation: each case evaluates             *)
(* ACC_IDX(word m) and table[m] concretely and checks the prefix. There is   *)
(* no closed form for the literal 256x8 table, so the case split is honest.  *)

let TABLE_PREFIX_ACC = prove
 (`!m. m < 256 ==>
    SUB_LIST(0, LENGTH(ACC_IDX(word m:byte))) (TABLE_ENTRY(word m)) =
    MAP word (ACC_IDX(word m:byte)):byte list`,
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[ACC_IDX; TABLE_ENTRY; FILTER] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[mldsa_rej_uniform_table] THEN
  CONV_TAC(DEPTH_CONV SUB_LIST_CONV) THEN
  REWRITE_TAC[MAP] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV));;

(* Per-byte VPSHUFB gather behavior: a control byte c with c < 8 (top bit    *)
(* clear, so the byte is selected not zeroed; low nibble = c since c < 8)    *)
(* selects source byte c. This is the building block for the table-driven    *)
(* compaction: the rej_uniform table stores accepted-nibble indices < 8 in   *)
(* each control lane, and this lemma reduces VPSHUFB's f8 selector to a      *)
(* plain source-byte pick. Matches the f8 in x86_VPSHUFB exactly.            *)

let PSHUFB_GATHER_BYTE = prove
 (`!(w:int128) (c:byte). val c < 8
     ==> (if bit 7 c then word 0:byte
          else word_subword w (8 * val (word_subword c (0,4):byte),8)) =
         word_subword w (8 * val c,8)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(bit 7 (c:byte))` ASSUME_TAC THENL
   [REWRITE_TAC[BIT_VAL] THEN
    SUBGOAL_THEN `val(c:byte) DIV 2 EXP 7 = 0` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC DIV_LT THEN UNDISCH_TAC `val(c:byte) < 8` THEN ARITH_TAC;
      CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(word_subword (c:byte) (0,4):byte) = val c` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
    MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `val(c:byte) < 8` THEN ARITH_TAC;
    REFL_TAC]);;

(* Per-lane extraction of a VPSHUFB low-128 result. For any byte->byte lane  *)
(* function ff (the f8 selector in x86_VPSHUFB) and a 64-bit control c       *)
(* lifted to 128 by word_zx, the k-th low output byte (k<8) is               *)
(* ff(control-byte k). Proved by unfolding usimd16/8/4/2, routing the        *)
(* word_subword through the nested word_joins with WORD_SUBWORD_JOIN_LOWER/  *)
(* UPPER (the control side is a fixed bit-routing -> WORD_BLAST), and        *)
(* collapsing the outer byte-subword via WORD_SUBWORD_TRIVIAL. Composing     *)
(* this with PSHUFB_GATHER_BYTE (when each control byte < 8) gives the       *)
(* gather g.byte(c.byte k); with TABLE_BYTES_LT_8 the < 8 side condition is  *)
(* automatic for table-sourced controls.                                     *)

let PSHUFB_LANE_EXTRACT = prove
 (`!(ff:byte->byte) (c:int64).
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (0,8):byte = ff(word_subword c (0,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (8,8):byte = ff(word_subword c (8,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (16,8):byte = ff(word_subword c (16,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (24,8):byte = ff(word_subword c (24,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (32,8):byte = ff(word_subword c (32,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (40,8):byte = ff(word_subword c (40,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (48,8):byte = ff(word_subword c (48,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (56,8):byte = ff(word_subword c (56,8))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[usimd16; usimd8; usimd4; usimd2] THEN
  SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
           DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128; ARITH] THEN
  REPEAT CONJ_TAC THEN
  (SIMP_TAC[WORD_SUBWORD_TRIVIAL; DIMINDEX_8; LE_REFL] THEN
   AP_TERM_TAC THEN CONV_TAC WORD_BLAST));;

(* The pshufb control bytes come from the rej_uniform table; every table     *)
(* byte is < 8 (the table stores 8-element index permutations of {0..7}      *)
(* with the unused tail zeroed). Hence in the compaction step every pshufb   *)
(* control lane has its top bit clear and PSHUFB_GATHER_BYTE applies -- the  *)
(* shuffle never zeroes, it always gathers. Proved via ALL over the literal  *)
(* table (fast:) then specialised to EL form.                                *)

let ALL_TABLE_LT_8 = prove
 (`ALL (\b:byte. val b < 8) mldsa_rej_uniform_table`,
  REWRITE_TAC[mldsa_rej_uniform_table; ALL] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let TABLE_BYTES_LT_8 = prove
 (`!j. j < 2048 ==> val(EL j (mldsa_rej_uniform_table:byte list)) < 8`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\b:byte. val b < 8`; `mldsa_rej_uniform_table:byte list`]
                ALL_EL) THEN
  REWRITE_TAC[ALL_TABLE_LT_8] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH(mldsa_rej_uniform_table:byte list) = 2048`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[mldsa_rej_uniform_table; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_REWRITE_TAC[]]);;

let PSHUFB_TABLE_GATHER_8 = prove
 (`!(g:int128) (c:int64).
     (!k. k < 8 ==> val(word_subword c (8*k,8):byte) < 8)
     ==> (!k. k < 8 ==>
            word_subword (usimd16
              (\(i:byte). if bit 7 i then word 0:byte
                  else word_subword g (8 * val(word_subword i (0,4):byte),8))
              (word_zx (word_zx c:int128):int128):int128) (8*k,8):byte =
            word_subword g (8 * val(word_subword c (8*k,8):byte),8))`,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[PSHUFB_LANE_EXTRACT] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC PSHUFB_GATHER_BYTE THEN
  ASM_SIMP_TAC[ARITH] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN
    MP_TAC(SPEC `3` th) THEN MP_TAC(SPEC `4` th) THEN MP_TAC(SPEC `5` th) THEN
    MP_TAC(SPEC `6` th) THEN MP_TAC(SPEC `7` th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* The vmovq load puts table[m] into an int64 register as                    *)
(* word(num_of_wordlist(TABLE_ENTRY m)); its k-th byte is EL k (TABLE_ENTRY  *)
(* m). (Inverse of the little-endian num_of_wordlist packing.)               *)

let CTRL_BYTE_TABLE = prove
 (`!m k. k < 8
     ==> word_subword (word(num_of_wordlist(TABLE_ENTRY m)):int64) (8*k,8):byte
         = EL k (TABLE_ENTRY m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`TABLE_ENTRY m:byte list`; `k:num`]
    (INST_TYPE[`:64`,`:KL`; `:8`,`:L`] WORD_SUBWORD_NUM_OF_WORDLIST)) THEN
  REWRITE_TAC[DIMINDEX_64; DIMINDEX_8] THEN
  SUBGOAL_THEN `LENGTH(TABLE_ENTRY m:byte list) = 8` SUBST1_TAC THENL
   [REWRITE_TAC[TABLE_ENTRY; LENGTH_SUB_LIST] THEN
    SUBGOAL_THEN `LENGTH(mldsa_rej_uniform_table:byte list) = 2048`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[mldsa_rej_uniform_table; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Every byte of any table entry is < 8 (from TABLE_BYTES_LT_8 via the       *)
(* SUB_LIST offset arithmetic). So all pshufb control lanes gather.          *)

let TABLE_ENTRY_BYTES_LT_8 = prove
 (`!m k. k < 8 ==> val(EL k (TABLE_ENTRY m):byte) < 8`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[TABLE_ENTRY] THEN
  MP_TAC(ISPECL [`mldsa_rej_uniform_table:byte list`; `k:num`; `8 * val(m:byte)`; `8`]
    EL_SUB_LIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `LENGTH(mldsa_rej_uniform_table:byte list) = 2048`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[mldsa_rej_uniform_table; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC TABLE_BYTES_LT_8 THEN
  MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ASM_ARITH_TAC);;

(* Full per-output-byte compaction for a table-driven VPSHUFB control: the   *)
(* k-th output byte (k<8) is the source byte g at index EL k (TABLE_ENTRY    *)
(* m). Combines PSHUFB_TABLE_GATHER_8 (gather) + CTRL_BYTE_TABLE (control    *)
(* byte = table entry) + TABLE_ENTRY_BYTES_LT_8 (< 8 side condition). With   *)
(* TABLE_PREFIX_ACC, the first popcount(m) of these are exactly g's bytes    *)
(* at the accepted nibble positions -- i.e. the accepted nibbles compacted.  *)

let PSHUFB_OUT_BYTE = prove
 (`!(g:int128) (m:byte) k. k < 8
     ==> word_subword (usimd16
            (\(i:byte). if bit 7 i then word 0:byte
                else word_subword g (8 * val(word_subword i (0,4):byte),8))
            (word_zx (word_zx (word(num_of_wordlist(TABLE_ENTRY m)):int64):int128):int128):int128)
            (8*k,8):byte =
         word_subword g (8 * val(EL k (TABLE_ENTRY m):byte), 8)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g:int128`; `word(num_of_wordlist(TABLE_ENTRY m)):int64`]
    PSHUFB_TABLE_GATHER_8) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CTRL_BYTE_TABLE] THEN
    ASM_SIMP_TAC[TABLE_ENTRY_BYTES_LT_8];
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CTRL_BYTE_TABLE]]);;

(* The 8 low output bytes of the table-driven VPSHUFB, as an explicit list,  *)
(* and its identification with the gather MAP over the table entry.          *)

let PSHUFB_OUT_LIST = define
 `PSHUFB_OUT_LIST (g:int128) (m:byte) =
    [word_subword g (8 * val(EL 0 (TABLE_ENTRY m):byte),8):byte;
     word_subword g (8 * val(EL 1 (TABLE_ENTRY m):byte),8);
     word_subword g (8 * val(EL 2 (TABLE_ENTRY m):byte),8);
     word_subword g (8 * val(EL 3 (TABLE_ENTRY m):byte),8);
     word_subword g (8 * val(EL 4 (TABLE_ENTRY m):byte),8);
     word_subword g (8 * val(EL 5 (TABLE_ENTRY m):byte),8);
     word_subword g (8 * val(EL 6 (TABLE_ENTRY m):byte),8);
     word_subword g (8 * val(EL 7 (TABLE_ENTRY m):byte),8)]`;;

let PSHUFB_OUT_LIST_AS_MAP = prove
 (`!g m. PSHUFB_OUT_LIST g m =
         MAP (\b:byte. word_subword g (8 * val b,8):byte) (TABLE_ENTRY m)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?a0 a1 a2 a3 a4 a5 a6 a7:byte.
       TABLE_ENTRY m = [a0;a1;a2;a3;a4;a5;a6;a7]` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `LENGTH(TABLE_ENTRY m:byte list) = 8` MP_TAC THENL
     [REWRITE_TAC[TABLE_ENTRY; LENGTH_SUB_LIST] THEN
      SUBGOAL_THEN `LENGTH(mldsa_rej_uniform_table:byte list) = 2048`
        (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[mldsa_rej_uniform_table; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
      ALL_TAC] THEN
    SPEC_TAC(`TABLE_ENTRY m:byte list`,`l:byte list`) THEN
    REWRITE_TAC[ARITH_RULE `8 = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC 0)))))))`] THEN
    REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[];
    ASM_REWRITE_TAC[PSHUFB_OUT_LIST; MAP] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]]);;

let SUB_LIST_NEST = prove
 (`!a n b m l:A list. a + n <= m /\ b + m <= LENGTH l
     ==> SUB_LIST(a,n)(SUB_LIST(b,m) l) = SUB_LIST(b+a,n) l`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[LIST_EQ] THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN CONJ_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `j < n` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(b,m) (l:A list)) = m` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `EL j (SUB_LIST(a,n)(SUB_LIST(b,m) (l:A list))) = EL (a+j) (SUB_LIST(b,m) l)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC EL_SUB_LIST THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `EL (a+j) (SUB_LIST(b,m) (l:A list)) = EL (b+(a+j)) l`
    SUBST1_TAC THENL
   [MATCH_MP_TAC EL_SUB_LIST THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `EL j (SUB_LIST(b+a,n) (l:A list)) = EL ((b+a)+j) l`
    SUBST1_TAC THENL
   [MATCH_MP_TAC EL_SUB_LIST THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* From the 16-byte chunk decomposition SUB_LIST(16i,16) inlist = [chunk0 bytes 0..15],
   extract the four 4-byte sub-iter blocks SUB_LIST(16i+4k,4) inlist (k=0,1,2,3) as the
   corresponding 4-byte slices of chunk0. One application yields all four blocks; the
   clean loop body uses these as the [b0;b1;b2;b3] argument to the per-block popcount /
   REJ_SAMPLE bridges. *)

let SUBITER_BLOCK_BYTES = prove
 (`!inlist i chunk0:int128.
      16 * i + 16 <= LENGTH(inlist:byte list) /\
      SUB_LIST(16*i,16) inlist =
        [word_subword chunk0 (0,8); word_subword chunk0 (8,8);
         word_subword chunk0 (16,8); word_subword chunk0 (24,8);
         word_subword chunk0 (32,8); word_subword chunk0 (40,8);
         word_subword chunk0 (48,8); word_subword chunk0 (56,8);
         word_subword chunk0 (64,8); word_subword chunk0 (72,8);
         word_subword chunk0 (80,8); word_subword chunk0 (88,8);
         word_subword chunk0 (96,8); word_subword chunk0 (104,8);
         word_subword chunk0 (112,8); word_subword chunk0 (120,8)]
      ==> SUB_LIST(16*i,4) inlist =
            [word_subword chunk0 (0,8); word_subword chunk0 (8,8);
             word_subword chunk0 (16,8); word_subword chunk0 (24,8)] /\
          SUB_LIST(16*i+4,4) inlist =
            [word_subword chunk0 (32,8); word_subword chunk0 (40,8);
             word_subword chunk0 (48,8); word_subword chunk0 (56,8)] /\
          SUB_LIST(16*i+8,4) inlist =
            [word_subword chunk0 (64,8); word_subword chunk0 (72,8);
             word_subword chunk0 (80,8); word_subword chunk0 (88,8)] /\
          SUB_LIST(16*i+12,4) inlist =
            [word_subword chunk0 (96,8); word_subword chunk0 (104,8);
             word_subword chunk0 (112,8); word_subword chunk0 (120,8)]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL[`0`;`4`;`16*i:num`;`16`;`inlist:byte list`] SUB_LIST_NEST);
    MP_TAC(ISPECL[`4`;`4`;`16*i:num`;`16`;`inlist:byte list`] SUB_LIST_NEST);
    MP_TAC(ISPECL[`8`;`4`;`16*i:num`;`16`;`inlist:byte list`] SUB_LIST_NEST);
    MP_TAC(ISPECL[`12`;`4`;`16*i:num`;`16`;`inlist:byte list`] SUB_LIST_NEST)] THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[ARITH_RULE `16*i+0 = 16*i`] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV SUB_LIST_CONV) THEN REFL_TAC));;

let ACC_IDX_LT_8 = prove
 (`!m x. MEM x (ACC_IDX m) ==> x < 8`,
  REWRITE_TAC[ACC_IDX] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MEM_FILTER; MEM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* LENGTH_ACC_IDX_BITSUM: the accept count = sum of the 8 mask bits. Bridges *)
(* LENGTH(ACC_IDX m) to the bitval-sum used by the popcount / maskbit chain, hence to *)
(* LENGTH(REJ_NIBBLES block) = LENGTH(REJ_SAMPLE block) for the SUBITER_STORE_EXTEND *)
(* width reconciliation.                                                     *)

let LENGTH_ACC_IDX_BITSUM = prove
 (`!m:byte. LENGTH(ACC_IDX m) =
            bitval(bit 0 m) + bitval(bit 1 m) + bitval(bit 2 m) + bitval(bit 3 m) +
            bitval(bit 4 m) + bitval(bit 5 m) + bitval(bit 6 m) + bitval(bit 7 m)`,
  GEN_TAC THEN REWRITE_TAC[ACC_IDX] THEN
  MAP_EVERY ASM_CASES_TAC
   [`bit 0 (m:byte)`;`bit 1 (m:byte)`;`bit 2 (m:byte)`;`bit 3 (m:byte)`;
    `bit 4 (m:byte)`;`bit 5 (m:byte)`;`bit 6 (m:byte)`;`bit 7 (m:byte)`] THEN
  ASM_REWRITE_TAC[FILTER; LENGTH; BITVAL_CLAUSES] THEN ARITH_TAC);;

(* (STORE_LANE_MATCH and its table-dependent deps PSHUF1_BYTE_EQ_OUTLIST /   *)
(*  LENGTH_TABLE_ENTRY are defined later, just after                         *)
(*  LENGTH_MLDSA_REJ_UNIFORM_TABLE, since they need the table length.)       *)

(* Gather-at-accepted-positions = filter: gathering an 8-element list at the *)
(* positions where a predicate holds equals filtering the list by that       *)
(* predicate.                                                                *)

let GATHER_FILTERED_IDX_8 = prove
 (`!(P:A->bool) a0 a1 a2 a3 a4 a5 a6 a7.
     MAP (\j. EL j [a0;a1;a2;a3;a4;a5;a6;a7])
         (FILTER (\j. P (EL j [a0;a1;a2;a3;a4;a5;a6;a7])) [0;1;2;3;4;5;6;7]) =
     FILTER P [a0;a1;a2;a3;a4;a5;a6;a7]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FILTER; MAP] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP; FILTER]) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* Per-sub-iter value bridge: gathering source bytes g at the accepted       *)
(* positions ACC_IDX m (mask m) equals FILTERing the 8 source bytes by the   *)
(* accept predicate val(.) < 15, PROVIDED the mask bit j agrees with that    *)
(* predicate on byte j. This connects the pshufb-compaction output (indexed  *)
(* by ACC_IDX m) to the functional spec's FILTER over byte values. The       *)
(* hypothesis is discharged at the call site from the vpsubb/vpmovmskb mask  *)
(* construction (bit j of the mask = sign bit of nibble_j - 15 = (nibble<15)).*)

let GATHER_FILTER_MAP_IDX_8 = prove
 (`!(f:byte->A) (P:byte->bool) n0 n1 n2 n3 n4 n5 n6 n7.
     MAP (\j. f (EL j [n0;n1;n2;n3;n4;n5;n6;n7]:byte))
         (FILTER (\j. P (EL j [n0;n1;n2;n3;n4;n5;n6;n7])) [0;1;2;3;4;5;6;7]) =
     MAP f (FILTER P [n0;n1;n2;n3;n4;n5;n6;n7])`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`P:byte->bool`; `n0:byte`;`n1:byte`;`n2:byte`;`n3:byte`;
                 `n4:byte`;`n5:byte`;`n6:byte`;`n7:byte`] GATHER_FILTERED_IDX_8) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[GSYM MAP_o; o_DEF]);;

(* The full abstract pshufb-compaction-correctness statement: the first      *)
(* popcount(m) = |ACC_IDX m| output bytes of the table-driven VPSHUFB are    *)
(* exactly the source bytes g at the accepted nibble positions ACC_IDX m,    *)
(* in order. This closes item (d): combined with the nibble-extraction and   *)
(* popcount bridges it shows each sub-iter writes the accepted (4-nibble)    *)
(* values compacted to the front. _NUM form maps over num positions.         *)

let PSHUFB_ACCEPTED_PREFIX = prove
 (`!(g:int128) m. m < 256 ==>
     SUB_LIST(0, LENGTH(ACC_IDX(word m:byte))) (PSHUFB_OUT_LIST g (word m)) =
     MAP (\b:byte. word_subword g (8 * val b,8):byte)
         (MAP word (ACC_IDX(word m:byte)):byte list)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[PSHUFB_OUT_LIST_AS_MAP] THEN
  REWRITE_TAC[SUB_LIST_0_MAP] THEN
  AP_TERM_TAC THEN
  ASM_SIMP_TAC[TABLE_PREFIX_ACC]);;

let PSHUFB_ACCEPTED_PREFIX_NUM = prove
 (`!(g:int128) m. m < 256 ==>
     SUB_LIST(0, LENGTH(ACC_IDX(word m:byte))) (PSHUFB_OUT_LIST g (word m)) =
     MAP (\j:num. word_subword g (8 * j,8):byte) (ACC_IDX(word m:byte))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PSHUFB_ACCEPTED_PREFIX] THEN
  REWRITE_TAC[GSYM MAP_o; o_DEF] THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word x:byte) = x` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_8] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ACC_IDX_LT_8) THEN ARITH_TAC);;

(* word_subword of a byte at (0,8) is the identity — closes the byte-of-byte *)
(* wrapper left by the lane extraction.                                      *)

let WORD_SUBWORD_BYTE_ID = prove
 (`!x:byte. word_subword x (0,8):byte = x`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* MASK_LOW_BIT: bit j (j<8) of the packed 8-bit mask word                   *)
(* `word(Sum_k 2^k * bitval(p k))` equals the predicate p j.                 *)

let MASK_LOW_BIT = prove
 (`!(p:num->bool) j. j < 8
     ==> (bit j (word(bitval(p 0) + 2 * bitval(p 1) + 4 * bitval(p 2) + 8 * bitval(p 3) +
                       16 * bitval(p 4) + 32 * bitval(p 5) + 64 * bitval(p 6) +
                       128 * bitval(p 7)):byte) <=> p j)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
    `j < 8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
  POP_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  MAP_EVERY BOOL_CASES_TAC [`(p:num->bool) 0`;`(p:num->bool) 1`;`(p:num->bool) 2`;`(p:num->bool) 3`;
                            `(p:num->bool) 4`;`(p:num->bool) 5`;`(p:num->bool) 6`;`(p:num->bool) 7`] THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV BIT_WORD_CONV) THEN REWRITE_TAC[]);;

(* SUB_LIST_16_BYTES_FROM_INT128: the 16 byte-subwords of the bytes128 load  *)
(* at buf + 16*i equal SUB_LIST(16*i,16) inlist, given the buffer contract.  *)

let SUB_LIST_16_BYTES_FROM_INT128 = prove
 (`!buf:int64 buflen inlist i s.
    16 * (i + 1) <= buflen /\
    LENGTH (inlist:byte list) = buflen /\
    read (memory :> bytes (buf, buflen)) s = num_of_wordlist inlist
    ==> SUB_LIST (16 * i, 16) inlist =
        [word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (0,8):byte;
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (8,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (16,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (24,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (32,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (40,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (48,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (56,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (64,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (72,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (80,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (88,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (96,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (104,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (112,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (120,8)]`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
    `loaded_d = read (memory :> bytes128 (word_add buf (word (16 * i)))) s` THEN
  CONV_TAC SYM_CONV THEN
  REWRITE_TAC[LISTS_NUM_OF_WORDLIST_EQ] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LENGTH; LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST; DIMINDEX_8] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM
    `\x. x DIV 2 EXP (8 * 16 * i) MOD 2 EXP (8 * 16)`) THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  SUBGOAL_THEN `MIN (buflen - 16 * i) 16 = 16` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
    [`word_add buf (word (16 * i)):int64`; `read memory s`]
    (INST_TYPE[`:128`,`:N`] VAL_READ_WBYTES)) THEN
  REWRITE_TAC[DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM BYTES128_WBYTES; GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[num_of_wordlist; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST);;

(* OP8_R8B_READ: the r8b sub-register read = word(val(read R8 s) MOD 256).   *)

let OP8_R8B_READ = prove
 (`!s:x86state. read (OPERAND8 (% r8b) s) s = word(val(read R8 s) MOD 256)`,
  GEN_TAC THEN REWRITE_TAC[OPERAND8; r8b; GPR8; register_size; regsize] THEN
  REWRITE_TAC[GSYM(NUM_EXP_CONV `2 EXP 8`)] THEN
  ONCE_REWRITE_TAC[MESON[EXP; DIV_1] `x MOD 2 EXP n = x DIV 2 EXP 0 MOD 2 EXP n`] THEN
  REWRITE_TAC[GSYM word_subword; READ_COMPONENT_COMPOSE; R8] THEN
  REWRITE_TAC[bottom_32; bottom_16; bottom_8; bottomhalf; READ_SUBWORD] THEN
  ONCE_REWRITE_TAC [WORD_EQ_BITS_ALT] THEN REWRITE_TAC[BIT_WORD_SUBWORD] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let MOVZBL_R10_CAPTURE_TAC : tactic =
  RULE_ASSUM_TAC(CONV_RULE(REWRITE_CONV[OP8_R8B_READ] THENC ONCE_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV));;

(* ZZCOLLAPSE / LACC8: reproved inline (the main-file let-names aren't in session scope). *)

let LACC8 = prove(`!m:byte. LENGTH(ACC_IDX m) <= 8`,
  GEN_TAC THEN REWRITE_TAC[ACC_IDX] THEN
  MP_TAC(ISPECL [`\i. bit i (m:byte)`; `[0;1;2;3;4;5;6;7]:num list`] LENGTH_FILTER) THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* SUBITER_STORE_EXTEND: fold a freshly-stored int32 block onto the running  *)
(* output prefix (both int32 lists; the new block sits at res + 4*|prefix|). *)

let SUBITER_STORE_EXTEND = prove
 (`!res s (prefix:int32 list) (block:int32 list).
     read (memory :> bytes(res, 4 * LENGTH prefix)) s = num_of_wordlist prefix /\
     read (memory :> bytes(word_add res (word (4 * LENGTH prefix)), 4 * LENGTH block)) s
       = num_of_wordlist block
     ==> read (memory :> bytes(res, 4 * LENGTH prefix + 4 * LENGTH block)) s
         = num_of_wordlist (APPEND prefix block)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s:x86state`;
                 `prefix:int32 list`; `block:int32 list`;
                 `4 * LENGTH(prefix:int32 list)`; `4 * LENGTH(block:int32 list)`]
        (INST_TYPE [`:32`,`:N`] BYTES_EQ_NUM_OF_WORDLIST_APPEND)) THEN
  REWRITE_TAC[DIMINDEX_32] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[]);;

(* VPMOVSXBD_LANE_EXTRACT: each 32-bit lane of `usimd8 word_sx x` is the     *)
(* sign-extend of the corresponding source byte.                             *)

let VPMOVSXBD_LANE_EXTRACT = prove
 (`!(x:int64).
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (0,32):int32 = word_sx(word_subword x (0,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (32,32):int32 = word_sx(word_subword x (8,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (64,32):int32 = word_sx(word_subword x (16,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (96,32):int32 = word_sx(word_subword x (24,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (128,32):int32 = word_sx(word_subword x (32,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (160,32):int32 = word_sx(word_subword x (40,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (192,32):int32 = word_sx(word_subword x (48,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (224,32):int32 = word_sx(word_subword x (56,8):byte))`,
  GEN_TAC THEN
  REWRITE_TAC[usimd8; usimd4; usimd2] THEN
  SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
           DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128;
           DIMINDEX_256; ARITH] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(* ========================================================================= *)
(* STORE-VALUE LANE BRIDGE.                                                  *)
(* These compose the full sub-iter SIMD store value: vpshufb (compacts       *)
(* accepted nibbles via the precomputed table) then vpmovsxbd (sign-         *)
(* extends each byte to int32). STORE_LANE_MATCH gives lane j of the         *)
(* YMM store value = word_sx of the j-th PSHUFB-gathered table byte,         *)
(* feeding STORE_BYTES256_NUM_OF_WORDLIST's lane-match hypothesis.           *)
(* pshuf1 is int256 (vpshufb operates on the full YMM); the store reads      *)
(* only the low 64 bits = low 128-lane = exactly the PSHUFB_OUT_BYTE         *)
(* form (j<8), so the outer word_zx 256<-128 is transparent (WSZ_OK).        *)
(* ========================================================================= *)

(* VPMOVSXBD_LANE_J: the j<8 quantified form of VPMOVSXBD_LANE_EXTRACT.      *)

let VPMOVSXBD_LANE_J = prove
 (`!(x:int64) j. j < 8
    ==> word_subword (usimd8 (\b:byte. word_sx b:int32) x) (32*j,32):int32
        = word_sx (word_subword x (8*j,8):byte)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `j < 8 <=> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VPMOVSXBD_LANE_EXTRACT]);;

(* WSZ_OK: outer word_zx 256<-128 is transparent for low-lane bytes (j<8).   *)

let WSZ_OK = prove
 (`!(x:int128) j. j < 8
    ==> word_subword (word_zx x:int256) (8 * j,8):byte = word_subword x (8 * j,8)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (ISPECL [`x:int128`; `8*j`; `8`]
    (INST_TYPE [`:256`,`:N`; `:128`,`:M`; `:8`,`:P`] WORD_SUBWORD_ZX)) THEN
  REWRITE_TAC[DIMINDEX_8;DIMINDEX_128;DIMINDEX_256] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

(* LENGTH_MLDSA_REJ_UNIFORM_TABLE: the shuffle-control table is 2048 bytes.  *)
(* The store-value lemmas below are table-length-dependent, so they live here. *)

let LENGTH_MLDSA_REJ_UNIFORM_TABLE = prove
 (`LENGTH (mldsa_rej_uniform_table:byte list) = 2048`,
  REWRITE_TAC[mldsa_rej_uniform_table; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* LENGTH_TABLE_ENTRY: a table entry is always 8 bytes (val m < 256 always). *)

let LENGTH_TABLE_ENTRY = prove
 (`!m:byte. LENGTH(TABLE_ENTRY m) = 8`,
  GEN_TAC THEN REWRITE_TAC[TABLE_ENTRY; LENGTH_SUB_LIST; LENGTH_MLDSA_REJ_UNIFORM_TABLE] THEN
  MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

(* VAL4EQ8: structural pshuf1 F uses (4)word index extraction; PSHUFB_OUT_BYTE *)
(* uses (8)word -- same low 4 bits, so the vals agree.                       *)

let VAL4EQ8 = prove
 (`!i:byte. val(word_subword i (0,4):4 word) = val(word_subword i (0,4):8 word)`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD] THEN
  SIMP_TAC[DIMINDEX_4;DIMINDEX_8;DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* PSHUF1_LOWLANE_BYTE: byte j of the int256 pshuf result (low lane, j<8)    *)
(* reduces to PSHUFB_OUT_BYTE.                                               *)

let PSHUF1_LOWLANE_BYTE = prove
 (`!g m j. j < 8
    ==> word_subword
          (word_zx
            (usimd16 (\i. if bit 7 i then word 0:byte
                          else word_subword (g:int128) (8 * val (word_subword i (0,4):4 word),8))
              (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256)
          (8 * j,8):byte
        = word_subword g (8 * val (EL j (TABLE_ENTRY m)),8)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WSZ_OK] THEN
  REWRITE_TAC[VAL4EQ8] THEN ASM_SIMP_TAC[PSHUFB_OUT_BYTE]);;

(* LENGTH_PSHUFB_OUT_LIST: the gathered table-byte list is always 8 long.    *)

let LENGTH_PSHUFB_OUT_LIST = prove
 (`!g:int128. !m:byte. LENGTH(PSHUFB_OUT_LIST g m) = 8`,
  REWRITE_TAC[PSHUFB_OUT_LIST_AS_MAP; LENGTH_MAP; LENGTH_TABLE_ENTRY]);;

(* PSHUF1_BYTE_EQ_OUTLIST: byte j of the pshuf result = EL j (PSHUFB_OUT_LIST). *)

let PSHUF1_BYTE_EQ_OUTLIST = prove
 (`!g m j. j < 8
    ==> word_subword
          (word_zx
            (usimd16 (\i. if bit 7 i then word 0:byte
                          else word_subword (g:int128) (8 * val (word_subword i (0,4):4 word),8))
              (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256)
          (8 * j,8):byte
        = EL j (PSHUFB_OUT_LIST g m)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PSHUF1_LOWLANE_BYTE] THEN
  ASM_SIMP_TAC[PSHUFB_OUT_LIST_AS_MAP; EL_MAP; LENGTH_TABLE_ENTRY]);;

(* STORE_LANE_MATCH: the capstone -- lane j (j<8) of the full vpshufb->vpmovsxbd *)
(* store value equals word_sx of the j-th PSHUFB-gathered table byte.        *)

let STORE_LANE_MATCH = prove
 (`!(g:int128) m j. j < 8
    ==> word_subword
          (usimd8 (\b:byte. word_sx b:int32)
            (word_zx (word_zx
              (word_zx
                (usimd16 (\i. if bit 7 i then word 0:byte
                              else word_subword g (8 * val (word_subword i (0,4):4 word),8))
                  (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256)
              :int128):int64))
          (32*j,32):int32
        = word_sx (EL j (PSHUFB_OUT_LIST g m))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VPMOVSXBD_LANE_J] THEN ASM_SIMP_TAC[WZZ_LOW] THEN
  ASM_SIMP_TAC[PSHUF1_BYTE_EQ_OUTLIST]);;

(* SUBWORD_ZX_LOW_CONV: discharge the SUBWORD_ZX_LOW side-condition by       *)
(* dimindex reduction.                                                       *)

let SUBWORD_ZX_LOW_CONV : conv =
  fun tm ->
      let inst = PART_MATCH (lhs o snd o dest_imp) SUBWORD_ZX_LOW tm in
      let ant = REWRITE_RULE[DIMINDEX_4;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] inst in
      MP ant (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl ant))));;

(* MASK_SHIFT8_MOD256: (SUM32 DIV 256) MOD 256 = the shifted low-byte mask.  *)

let MASK_SHIFT8_MOD256 = prove
 (`!S. val(word_zx(word_ushr(word_zx(word_zx(word S:int32):int64):int32) 8):int64) MOD 256 =
       (S DIV 256) MOD 256`,
  GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[MM32_64; MOD_MOD_REFL; MM64_256; MM32_DIV256]);;

(* LOW24_LT: the weighted sum of mask bits 0..23 is < 16777216.              *)

let LOW24_LT = prove
 (`!p:num->bool. bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) < 16777216`,
  GEN_TAC THEN
  MAP_EVERY (fun k -> MP_TAC(ISPEC (mk_comb(`p:num->bool`,mk_small_numeral k)) BITVAL_BOUND))
    [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23] THEN ARITH_TAC);;

(* BYTE1_DIVMOD: (SUM32 DIV 256) MOD 256 = the lanes-8..15 weighted sum.     *)

let BYTE1_DIVMOD = prove
 (`!p:num->bool.
    ((bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
      16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
      256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
      4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
      65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
      1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
      16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
      268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) DIV 256) MOD 256 =
    bitval(p 8) + 2*bitval(p 9) + 4*bitval(p 10) + 8*bitval(p 11) +
    16*bitval(p 12) + 32*bitval(p 13) + 64*bitval(p 14) + 128*bitval(p 15)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `(bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
     16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
     268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) =
    (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7)) +
    256 * (bitval(p 8) + 2*bitval(p 9) + 4*bitval(p 10) + 8*bitval(p 11) +
     16*bitval(p 12) + 32*bitval(p 13) + 64*bitval(p 14) + 128*bitval(p 15) +
     256*(bitval(p 16) + 2*bitval(p 17) + 4*bitval(p 18) + 8*bitval(p 19) +
     16*bitval(p 20) + 32*bitval(p 21) + 64*bitval(p 22) + 128*bitval(p 23) +
     256*(bitval(p 24) + 2*bitval(p 25) + 4*bitval(p 26) + 8*bitval(p 27) +
     16*bitval(p 28) + 32*bitval(p 29) + 64*bitval(p 30) + 128*bitval(p 31))))`
   SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ; LOW8_LT; DIV_LT; ADD_CLAUSES] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ARITH_RULE
   `bitval (p 8) + 2 * bitval (p 9) + 4 * bitval (p 10) + 8 * bitval (p 11) +
    16 * bitval (p 12) + 32 * bitval (p 13) + 64 * bitval (p 14) + 128 * bitval (p 15) + Z =
    (bitval (p 8) + 2 * bitval (p 9) + 4 * bitval (p 10) + 8 * bitval (p 11) +
     16 * bitval (p 12) + 32 * bitval (p 13) + 64 * bitval (p 14) + 128 * bitval (p 15)) + Z`] THEN
  MATCH_MP_TAC ADD256_MOD THEN
  MAP_EVERY (fun k -> MP_TAC(ISPEC (mk_comb(`p:num->bool`,mk_small_numeral k)) BITVAL_BOUND))
    [8;9;10;11;12;13;14;15] THEN ARITH_TAC);;

(* BYTE2_DIVMOD: (SUM32 DIV 65536) MOD 256 = the lanes-16..23 weighted sum.  *)

let BYTE2_DIVMOD = prove
 (`!p:num->bool.
    ((bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
      16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
      256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
      4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
      65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
      1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
      16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
      268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) DIV 65536) MOD 256 =
    bitval(p 16) + 2*bitval(p 17) + 4*bitval(p 18) + 8*bitval(p 19) +
    16*bitval(p 20) + 32*bitval(p 21) + 64*bitval(p 22) + 128*bitval(p 23)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `(bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
     16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
     268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) =
    (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15)) +
    65536 * ((bitval(p 16) + 2*bitval(p 17) + 4*bitval(p 18) + 8*bitval(p 19) +
     16*bitval(p 20) + 32*bitval(p 21) + 64*bitval(p 22) + 128*bitval(p 23)) +
     256*(bitval(p 24) + 2*bitval(p 25) + 4*bitval(p 26) + 8*bitval(p 27) +
     16*bitval(p 28) + 32*bitval(p 29) + 64*bitval(p 30) + 128*bitval(p 31)))`
   SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ; LOW16_LT; DIV_LT; ADD_CLAUSES] THEN
  MATCH_MP_TAC ADD256_MOD THEN
  MAP_EVERY (fun k -> MP_TAC(ISPEC (mk_comb(`p:num->bool`,mk_small_numeral k)) BITVAL_BOUND))
    [16;17;18;19;20;21;22;23] THEN ARITH_TAC);;

let BYTE3_DIVMOD = prove
 (`!p:num->bool.
    ((bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
      16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
      256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
      4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
      65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
      1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
      16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
      268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) DIV 16777216) MOD 256 =
    bitval(p 24) + 2*bitval(p 25) + 4*bitval(p 26) + 8*bitval(p 27) +
    16*bitval(p 28) + 32*bitval(p 29) + 64*bitval(p 30) + 128*bitval(p 31)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `(bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
     16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
     268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) =
    (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23)) +
    16777216 * (bitval(p 24) + 2*bitval(p 25) + 4*bitval(p 26) + 8*bitval(p 27) +
     16*bitval(p 28) + 32*bitval(p 29) + 64*bitval(p 30) + 128*bitval(p 31))`
   SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ; LOW24_LT; DIV_LT; ADD_CLAUSES] THEN
  MATCH_MP_TAC MOD_LT THEN
  MAP_EVERY (fun k -> MP_TAC(ISPEC (mk_comb(`p:num->bool`,mk_small_numeral k)) BITVAL_BOUND))
    [24;25;26;27;28;29;30;31] THEN ARITH_TAC);;

(* --- subiter_byte23_lemmas ---                                             *)
(* ========================================================================= *)
(* Sub-iters 3,4 popcount->length keystones. Load AFTER                      *)
(* .subiter_k_lemmas.ml (needs BYTE2_DIVMOD/BYTE3_DIVMOD/divmod_swap/MM* etc.). *)
(* These give POPCNT_BYTE2/BYTE3 = the unweighted lanes-16..23 / 24..31 bitval sums, *)
(* over the double/triple word_ushr mask forms produced by the simulator at sub-iters *)
(* 3,4 (mask = R8 after 2 / 3 ushr-by-8). Analogous to POPCNT_BYTE1.         *)
(* ========================================================================= *)

(* peel one ushr-8 layer of a 64-bit mask through the i32 round-trip         *)

let MASK_SHIFT16_MOD256 = prove
 (`!S. val(word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word S:int32):int64):int32) 8):int64):int32) 8):int64) MOD 256 =
       (S DIV 65536) MOD 256`,
  GEN_TAC THEN
  REWRITE_TAC[MASK_USHR8_STEP; VAL_MASK8B; DIV_DIV] THEN
  REWRITE_TAC[ARITH_RULE `256 * 256 = 65536`] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`; ARITH_RULE `65536 = 2 EXP 16`; ARITH_RULE `256 = 2 EXP 8`] THEN
  REWRITE_TAC[divmod_swap16] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

let MASK_SHIFT24_MOD256 = prove
 (`!S. val(word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word S:int32):int64):int32) 8):int64):int32) 8):int64):int32) 8):int64) MOD 256 =
       (S DIV 16777216) MOD 256`,
  GEN_TAC THEN
  REWRITE_TAC[MASK_USHR8_STEP; VAL_MASK8C; DIV_DIV] THEN
  REWRITE_TAC[ARITH_RULE `65536 * 256 = 16777216`] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`; ARITH_RULE `16777216 = 2 EXP 24`; ARITH_RULE `256 = 2 EXP 8`] THEN
  REWRITE_TAC[divmod_swap24] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Sub-iter k outlen bound: outlen + sum of popcnts up to sub-iter k <= 248. *)
(* Used to prove JA-not-taken at each sub-iter's `cmp eax, 0xf8`.            *)

(* Unweighted bitval sum = filter-length: the clean-body counter chain leaves R9/RAX
   carrying word_popcount(...) = Σ_{k<8} bitval(bit 7 (f1bnd byte k)) (after the
   POPCNT_VPMOVMSKB low-byte reduction; see the movzbl/popcnt recipe).  With the maskbit
   fact bit 7 (f1bnd byte k) <=> val(nibble_k) < 15, this rewrites the sum to
   LENGTH(FILTER (\x. val x < 15) [nibbles]) = LENGTH(REJ_NIBBLES_ETA2 block) — the block
   accept count = the RAX advance for the mid-guard. *)
(* Collapse the stepped RAX add-nest word_zx(word_add(word_zx(word a))(word_zx(word_zx(word b))))
   to word(a+b) when a+b < 2^32.  After the popcnt+add the clean-body RAX has exactly this
   shape (a = outlen0, b = block accept count); with a+b <= 248 it folds to word(outlen0+count),
   from which the niblen bound + JA_NOT_TAKEN_LE discharges the mid-guard ja. *)

let POPCNT_BYTE1 = prove
 (`!p:num->bool.
     word_popcount
       (word_zx (word_zx (word_zx
          (word (val (word_zx (word_ushr (word_zx (word_zx
             (word (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
              16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
              256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
              4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
              65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
              1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
              16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
              268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)):int32):int64):int32) 8):int64)
            MOD 256):int32):int32):int32):int32) =
     bitval(p 8) + bitval(p 9) + bitval(p 10) + bitval(p 11) +
     bitval(p 12) + bitval(p 13) + bitval(p 14) + bitval(p 15)`,
  GEN_TAC THEN
  REWRITE_TAC[MASK_SHIFT8_MOD256; BYTE1_DIVMOD] THEN
  MAP_EVERY (fun k -> BOOL_CASES_TAC (mk_comb(`p:num->bool`, mk_small_numeral k)))
    [8;9;10;11;12;13;14;15] THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* POPCNT_BYTE2: popcount of the byte-2 mask slice = the lanes-16..23 sum.   *)

let POPCNT_BYTE2 =
  let arg = subst [SUMTERM_BYTE23, `SUMV:num`]
    (subst [`word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word SUMV:int32):int64):int32) 8):int64):int32) 8):int64`, `MASKC:int64`]
       `word_zx(word_zx(word_zx(word(val (MASKC:int64) MOD 256):byte):int32):int64):int32`) in
  prove(mk_forall(`p:num->bool`, mk_eq(mk_comb(`word_popcount:int32->num`, arg),
     `bitval(p 16) + bitval(p 17) + bitval(p 18) + bitval(p 19) +
      bitval(p 20) + bitval(p 21) + bitval(p 22) + bitval(p 23)`)),
    GEN_TAC THEN REWRITE_TAC[MASK_SHIFT16_MOD256; BYTE2_DIVMOD] THEN
    MAP_EVERY (fun k -> BOOL_CASES_TAC (mk_comb(`p:num->bool`, mk_small_numeral k)))
      [16;17;18;19;20;21;22;23] THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;

let POPCNT_BYTE3 =
  let arg = subst [SUMTERM_BYTE23, `SUMV:num`]
    (subst [`word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word SUMV:int32):int64):int32) 8):int64):int32) 8):int64):int32) 8):int64`, `MASKC:int64`]
       `word_zx(word_zx(word_zx(word(val (MASKC:int64) MOD 256):byte):int32):int64):int32`) in
  prove(mk_forall(`p:num->bool`, mk_eq(mk_comb(`word_popcount:int32->num`, arg),
     `bitval(p 24) + bitval(p 25) + bitval(p 26) + bitval(p 27) +
      bitval(p 28) + bitval(p 29) + bitval(p 30) + bitval(p 31)`)),
    GEN_TAC THEN REWRITE_TAC[MASK_SHIFT24_MOD256; BYTE3_DIVMOD] THEN
    MAP_EVERY (fun k -> BOOL_CASES_TAC (mk_comb(`p:num->bool`, mk_small_numeral k)))
      [24;25;26;27;28;29;30;31] THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;

(* cumulative outlen bound through sub-iter 4 (4th block), for the final RAX/store-safety. *)

let zxbyte_eq = prove
 (`!v. v < 256 ==>
     word_zx(word_zx(word_zx(word v:byte):int32):int64):int32 =
     word_zx(word_zx(word_zx(word v:int32):int32):int32):int32`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `v < 256 ==> v < 2 EXP 8 /\ v < 2 EXP 32 /\ v < 2 EXP 64`] THEN
  CONV_TAC(DEPTH_CONV NUM_REDUCE_CONV) THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `v < 256 ==> v < 2 EXP 8 /\ v < 2 EXP 32`]);;

(* Sub-iters 3,4: BYTE2_DIVMOD / BYTE3_DIVMOD ((SUM32 DIV 65536) MOD 256 etc.) +
   MASK_SHIFT16/24_MOD256 (double/triple word_ushr by 8) + POPCNT_BYTE2/BYTE3.  Same
   shape as BYTE1; the SUBST1_TAC reassociation peels one more 256* factor each. *)

let MASKBIT_TGT_TAC : tactic =
  W(fun (asl,w) ->
    let m8 = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8:int64` &&
        can(find_term(fun u->match u with Const("bitval",_)->true|_->false))(concl th)) (map snd asl) in
    let sum32 = rand(rand(lhand(concl m8))) in
    let summands = striplist (dest_binop `(+):num->num->num`) sum32 in
    let getbitval s = if is_binop `( * ):num->num->num` s then rand s else s in
    let bvs = map getbitval summands in
    let sum8 = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
      (List.map2 (fun wt bv -> if wt=1 then bv else mk_binop `( * ):num->num->num` (mk_small_numeral wt) bv) [1;2;4;8;16;32;64;128] (map (fun i->List.nth bvs i) (0--7))) in
    let high = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
      (map (fun i -> let wt = 1 lsl (i-8) in if wt=1 then List.nth bvs i else mk_binop `( * ):num->num->num` (mk_small_numeral wt) (List.nth bvs i)) (8--31)) in
    let splitth = prove(mk_eq(sum32, mk_binop `(+):num->num->num` sum8 (mk_binop `( * ):num->num->num` `256` high)), ARITH_TAC) in
    let byteeq32 = TRANS (AP_TERM `word:num->byte` splitth) (SPECL [sum8; high] WORD_ADD_256_BYTE) in
    let beq = mk_eq(`word (val (mask8:int64) MOD 256):byte`, mk_comb(`word:num->byte`, sum8)) in
    let preds8 = map (fun i -> rand (List.nth bvs i)) (0--7) in
    let plist = mk_abs(`k:num`, mk_comb(mk_comb(`EL:num->(bool)list->bool`,`k:num`),
       (end_itlist (fun a b -> mk_binop `CONS:bool->(bool)list->(bool)list` a b) (preds8 @ [`[]:(bool)list`])))) in
    let mb0 = find (fun th -> let c=concl th in is_forall c &&
        can(find_term(fun u->u=`f1bnd:int256`))c &&
        can(find_term(fun u->match u with Comb(Const("bit",_),_)->true|_->false))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (24,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (32,8):byte`))c)) (map snd asl) in
    let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mb0 in
       CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
    SUBGOAL_THEN beq ASSUME_TAC THENL
     [SUBGOAL_THEN (mk_eq(`val (mask8:int64)`, mk_binop `MOD` sum32 `2 EXP 32`)) SUBST1_TAC THENL
       [SUBST1_TAC(SYM m8) THEN REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_64; DIMINDEX_32] THEN
        MATCH_MP_TAC MOD_LT THEN MP_TAC(SPECL [sum32; `2 EXP 32`] MOD_LT_EQ) THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_binop `MOD` (mk_binop `MOD` sum32 `2 EXP 32`) `256`, mk_binop `MOD` sum32 `256`)) SUBST1_TAC THENL
       [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV); ALL_TAC] THEN
      REWRITE_TAC[WORD_BYTE_MOD] THEN ACCEPT_TAC byteeq32;
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun beqth -> if is_eq(concl beqth) && lhand(concl beqth)=`word (val (mask8:int64) MOD 256):byte` then REWRITE_TAC[beqth] else NO_TAC) THEN
    MP_TAC(SPECL [plist; `j:num`] MASK_LOW_BIT) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
      (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC mbs THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC);;

(* --- tab1_teq_tac ---                                                      *)
(* Table-load bridge: derive teq `tab1 = word_zx(word_zx(word(nwl(TABLE_ENTRY(word(val mask8 MOD 256))))))`
   at s14 from the raw vmovq read, via TABLE_VMOVQ_READ + R_EQ (zx-collapse) + RLT (r<256). This is
   the genuine table-correspondence that the earlier fold left unproven. After REABBREV tab1, ASSUMEd fact's lhand
   read YMM6 s14 -> tab1, giving the teq the pf_target proof needs. *)

let F0NIB_CHUNK0 =
  `word_and (word_or (usimd16 (\b:byte. word_zx b:int16) chunk0:int256)
                     (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) chunk0:int256):int256))
            (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)`;;

(* STORE_LANE_EQ_REJBLOCK: for j<k<=8, lane j of the usimd8 word_sx store over *)
(* the vpshufb-gathered TABLE_ENTRY equals EL j (MAP word_sx (SUB_LIST(0,k)  *)
(* (PSHUFB_OUT_LIST g m))) — the lane-match hypothesis of the store bridge.  *)

let STORE_LANE_EQ_REJBLOCK = prove
 (`!(g:int128) m k j. j < k /\ k <= 8
    ==> word_subword
          (usimd8 (\b:byte. word_sx b:int32)
            (word_zx (word_zx
              (word_zx
                (usimd16 (\i. if bit 7 i then word 0:byte
                              else word_subword g (8 * val (word_subword i (0,4):4 word),8))
                  (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256)
              :int128):int64))
          (32*j,32):int32
        = EL j (MAP (\b:byte. word_sx b:int32) (SUB_LIST(0,k) (PSHUFB_OUT_LIST g m)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `j < 8` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[STORE_LANE_MATCH] THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(0,k)(PSHUFB_OUT_LIST (g:int128) m)) = k` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_PSHUFB_OUT_LIST] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[EL_MAP] THEN
    ASM_SIMP_TAC[EL_SUB_LIST; LENGTH_PSHUFB_OUT_LIST; ADD_CLAUSES] THEN
    ASM_ARITH_TAC]);;

(* pf_target: the sub-iter-1 pshufb lane-gather form (= read YMM6 s15),      *)
(* matching the usimd16/TABLE_ENTRY control of the store bridge.             *)

let pf_target =
  `pshuf1:int256 =
   word_zx
   (usimd16
    (\i:byte. if bit 7 i
         then word 0:byte
         else word_subword (word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128)
              (8 * val (word_subword i (0,4):4 word),8):byte)
   (word_zx
   (word_zx (word (num_of_wordlist (TABLE_ENTRY (word (val (mask8:int64) MOD 256):byte))):int64):int128):int128):int128)`;;

let MASKBIT_TGT_2_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let m8b = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8b:int64` &&
        can(find_term(fun u->match u with Const("bitval",_)->true|_->false))(concl th)) asms in
    let sum32 = find_term (fun u -> match u with
       Comb(Comb(Const("+",_),_),_) -> can(find_term(fun v->match v with Const("bitval",_)->true|_->false)) u | _ -> false) (concl m8b) in
    let summands = striplist (dest_binop `(+):num->num->num`) sum32 in
    let getbitval s = if is_binop `( * ):num->num->num` s then rand s else s in
    let bvs = map getbitval summands in
    let mksum idxs wts = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
       (List.map2 (fun wt i -> let bv = List.nth bvs i in if wt=1 then bv else mk_binop `( * ):num->num->num` (mk_small_numeral wt) bv) wts idxs) in
    let sum_low8 = mksum [0;1;2;3;4;5;6;7] [1;2;4;8;16;32;64;128] in
    let sum8' = mksum [8;9;10;11;12;13;14;15] [1;2;4;8;16;32;64;128] in
    let sum_high16 = mksum (16--31) (map (fun i->1 lsl (i-16)) (16--31)) in
    let regroup = prove(mk_eq(sum32, mk_binop `(+):num->num->num` sum_low8
       (mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` `256` sum8')
                                      (mk_binop `( * ):num->num->num` `65536` sum_high16))), ARITH_TAC) in
    let low8lt = prove(mk_binop `(<):num->num->bool` sum_low8 `256`,
       MP_TAC(end_itlist CONJ (map (fun b -> SPEC b BITVAL_BOUND) (map (fun i->rand(List.nth bvs i)) (0--7)))) THEN ARITH_TAC) in
    let s8lt = prove(mk_binop `(<):num->num->bool` sum8' `256`,
       MP_TAC(end_itlist CONJ (map (fun b -> SPEC b BITVAL_BOUND) (map (fun i->rand(List.nth bvs i)) (8--15)))) THEN ARITH_TAC) in
    let vshift = SPEC sum32 MASK_SHIFT8_MOD256 in
    let dms = MP (SPECL [sum_low8; sum8'; sum_high16] DIVMOD256_SPLIT) (CONJ low8lt s8lt) in
    let valeq = REWRITE_RULE[m8b] (TRANS vshift (TRANS (AP_THM (AP_TERM `(MOD)` (AP_THM (AP_TERM `(DIV)` regroup) `256`)) `256`) dms)) in
    let beq = mk_eq(`word (val (mask8b:int64) MOD 256):byte`, mk_comb(`word:num->byte`, sum8')) in
    let preds8 = map (fun i -> rand (List.nth bvs i)) (8--15) in
    let plist = mk_abs(`k:num`, mk_comb(mk_comb(`EL:num->(bool)list->bool`,`k:num`),
       (end_itlist (fun a b -> mk_binop `CONS:bool->(bool)list->(bool)list` a b) (preds8 @ [`[]:(bool)list`])))) in
    let mb2 = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f1bnd:int256`))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (32,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (64,8):byte`))c) &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (24,8):byte`))c)) asms in
    let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mb2 in
       CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
    SUBGOAL_THEN beq ASSUME_TAC THENL
     [REWRITE_TAC[AP_TERM `word:num->byte` valeq];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun beqth -> if is_eq(concl beqth) && lhand(concl beqth)=`word (val (mask8b:int64) MOD 256):byte` then REWRITE_TAC[beqth] else NO_TAC) THEN
    MP_TAC(SPECL [plist; `j:num`] MASK_LOW_BIT) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
      (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC mbs THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC);;

(* --- tab2_teq_tac ---                                                      *)
(* Sub-iter-2 table-load bridge: R_EQ_B/RLT_B (mask8b zx-collapse + bound) + TAB2_TEQ_TAC.
   At s26 (after the vmovq table load), read YMM6 s26 = word_zx(word_zx(read(bytes64(table+8*r)) s25))
   with r = val(word_zx(word_zx(word(val mask8b MOD 256)))). Same shape as si1's tab1 but mask8b/s25/s26.
   After REABBREV tab2, gives teq2: word_zx(word_zx(word(nwl(TABLE_ENTRY(word(val mask8b MOD 256)))))) = tab2. *)

let pf_target_2 =
  let g1 = `word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128` in
  let g2 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128) 64):int128):int128` in
  subst [g2,g1; `mask8b:int64`,`mask8:int64`; `pshuf2:int256`,`pshuf1:int256`] pf_target;;

(* PF_PROOF_2 : discharges `pshuf2 = pf_target_2` (genuine table bridge for sub-iter 2). *)

let MASKBIT_TGT_3_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let m8c_def = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8c:int64` &&
        can(find_term(fun u->u=`mask8b:int64`))(concl th)) asms in
    let m8b_def = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8b:int64` &&
        can(find_term(fun u->match u with Const("bitval",_)->true|_->false))(concl th)) asms in
    let sum32 = find_term (fun u -> match u with
       Comb(Comb(Const("+",_),_),_) -> can(find_term(fun v->match v with Const("bitval",_)->true|_->false)) u | _ -> false) (concl m8b_def) in
    let summands = striplist (dest_binop `(+):num->num->num`) sum32 in
    let getbitval s = if is_binop `( * ):num->num->num` s then rand s else s in
    let bvs = map getbitval summands in
    let mksum idxs wts = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
       (List.map2 (fun wt i -> let bv = List.nth bvs i in if wt=1 then bv else mk_binop `( * ):num->num->num` (mk_small_numeral wt) bv) wts idxs) in
    let low16 = mksum (0--15) (map (fun i->1 lsl i) (0--15)) in
    let sum8'' = mksum [16;17;18;19;20;21;22;23] [1;2;4;8;16;32;64;128] in
    let high8 = mksum (24--31) (map (fun i->1 lsl (i-24)) (24--31)) in
    let regroup = prove(mk_eq(sum32, mk_binop `(+):num->num->num` low16
       (mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` `65536` sum8'')
                                      (mk_binop `( * ):num->num->num` `16777216` high8))), ARITH_TAC) in
    let low16lt = prove(mk_binop `(<):num->num->bool` low16 `65536`,
       MP_TAC(end_itlist CONJ (map (fun b -> SPEC b BITVAL_BOUND) (map (fun i->rand(List.nth bvs i)) (0--15)))) THEN ARITH_TAC) in
    let s8lt = prove(mk_binop `(<):num->num->bool` sum8'' `256`,
       MP_TAC(end_itlist CONJ (map (fun b -> SPEC b BITVAL_BOUND) (map (fun i->rand(List.nth bvs i)) (16--23)))) THEN ARITH_TAC) in
    let m8c_over_sum = REWRITE_RULE[SYM m8b_def] m8c_def in
    let vshift = SPEC sum32 MASK_SHIFT16_MOD256 in
    let dms = MP (SPECL [low16; sum8''; high8] DIVMOD65536_SPLIT) (CONJ low16lt s8lt) in
    let valeq = TRANS (REWRITE_RULE[m8c_over_sum] vshift) (TRANS (AP_THM (AP_TERM `(MOD)` (AP_THM (AP_TERM `(DIV)` regroup) `65536`)) `256`) dms) in
    let beq = mk_eq(`word (val (mask8c:int64) MOD 256):byte`, mk_comb(`word:num->byte`, sum8'')) in
    let preds8 = map (fun i -> rand (List.nth bvs i)) (16--23) in
    let plist = mk_abs(`k:num`, mk_comb(mk_comb(`EL:num->(bool)list->bool`,`k:num`),
       (end_itlist (fun a b -> mk_binop `CONS:bool->(bool)list->(bool)list` a b) (preds8 @ [`[]:(bool)list`])))) in
    let mb3 = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f1bnd:int256`))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (64,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (96,8):byte`))c) &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (56,8):byte`))c)) asms in
    let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mb3 in
       CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
    SUBGOAL_THEN beq ASSUME_TAC THENL
     [REWRITE_TAC[AP_TERM `word:num->byte` valeq];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun beqth -> if is_eq(concl beqth) && lhand(concl beqth)=`word (val (mask8c:int64) MOD 256):byte` then REWRITE_TAC[beqth] else NO_TAC) THEN
    MP_TAC(SPECL [plist; `j:num`] MASK_LOW_BIT) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
      (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC mbs THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC);;

let pf_target_3 =
  let g1 = `word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128` in
  let g3 = `word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128` in
  subst [g3,g1; `mask8c:int64`,`mask8:int64`; `pshuf3:int256`,`pshuf1:int256`] pf_target;;

let MASKBIT_TGT_4_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let m8d_def = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8d:int64` && can(find_term(fun u->u=`mask8c:int64`))(concl th)) asms in
    let m8c_def = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8c:int64` && can(find_term(fun u->u=`mask8b:int64`))(concl th)) asms in
    let m8b_def = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8b:int64` && can(find_term(fun u->match u with Const("bitval",_)->true|_->false))(concl th)) asms in
    let sum32 = find_term (fun u -> match u with
       Comb(Comb(Const("+",_),_),_) -> can(find_term(fun v->match v with Const("bitval",_)->true|_->false)) u | _ -> false) (concl m8b_def) in
    let summands = striplist (dest_binop `(+):num->num->num`) sum32 in
    let getbitval s = if is_binop `( * ):num->num->num` s then rand s else s in
    let bvs = map getbitval summands in
    let mksum idxs wts = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
       (List.map2 (fun wt i -> let bv = List.nth bvs i in if wt=1 then bv else mk_binop `( * ):num->num->num` (mk_small_numeral wt) bv) wts idxs) in
    let low24 = mksum (0--23) (map (fun i->1 lsl i) (0--23)) in
    let sum8''' = mksum [24;25;26;27;28;29;30;31] [1;2;4;8;16;32;64;128] in
    let regroup = prove(mk_eq(sum32, mk_binop `(+):num->num->num` low24
       (mk_binop `( * ):num->num->num` `16777216` sum8''')), ARITH_TAC) in
    let low24lt = prove(mk_binop `(<):num->num->bool` low24 `16777216`,
       MP_TAC(end_itlist CONJ (map (fun b -> SPEC b BITVAL_BOUND) (map (fun i->rand(List.nth bvs i)) (0--23)))) THEN ARITH_TAC) in
    let s8lt = prove(mk_binop `(<):num->num->bool` sum8''' `256`,
       MP_TAC(end_itlist CONJ (map (fun b -> SPEC b BITVAL_BOUND) (map (fun i->rand(List.nth bvs i)) (24--31)))) THEN ARITH_TAC) in
    (* mask8d over SUM32: subst mask8c def (over mask8b) then mask8b def (over SUM32) *)
    let m8d_over_sum = REWRITE_RULE[SYM m8b_def] (REWRITE_RULE[SYM m8c_def] m8d_def) in
    let vshift = SPEC sum32 MASK_SHIFT24_MOD256 in
    let dms = MP (SPECL [low24; sum8'''] DIVMOD16777216_SPLIT) low24lt in
    let s8mod = prove(mk_eq(mk_binop `MOD` sum8''' `256`, sum8'''), MATCH_MP_TAC MOD_LT THEN ACCEPT_TAC s8lt) in
    let valeq = TRANS (REWRITE_RULE[m8d_over_sum] vshift)
                  (TRANS (AP_THM (AP_TERM `(MOD)` (AP_THM (AP_TERM `(DIV)` regroup) `16777216`)) `256`) (TRANS dms s8mod)) in
    let beq = mk_eq(`word (val (mask8d:int64) MOD 256):byte`, mk_comb(`word:num->byte`, sum8''')) in
    let preds8 = map (fun i -> rand (List.nth bvs i)) (24--31) in
    let plist = mk_abs(`k:num`, mk_comb(mk_comb(`EL:num->(bool)list->bool`,`k:num`),
       (end_itlist (fun a b -> mk_binop `CONS:bool->(bool)list->(bool)list` a b) (preds8 @ [`[]:(bool)list`])))) in
    let mb4 = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f1bnd:int256`))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (96,8):byte`))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (120,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (64,8):byte`))c)) asms in
    let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mb4 in
       CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
    SUBGOAL_THEN beq ASSUME_TAC THENL
     [REWRITE_TAC[AP_TERM `word:num->byte` valeq];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun beqth -> if is_eq(concl beqth) && lhand(concl beqth)=`word (val (mask8d:int64) MOD 256):byte` then REWRITE_TAC[beqth] else NO_TAC) THEN
    MP_TAC(SPECL [plist; `j:num`] MASK_LOW_BIT) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
      (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC mbs THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC);;

let pf_target_4 =
  let g1 = `word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128` in
  let g4 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128) 64):int128):int128` in
  subst [g4,g1; `mask8d:int64`,`mask8:int64`; `pshuf4:int256`,`pshuf1:int256`] pf_target;;

let SL16_4WAY = prove
 (`SUB_LIST(16*i,16) (inlist:byte list) =
   APPEND (SUB_LIST(16*i,4) inlist)
   (APPEND (SUB_LIST(16*i+4,4) inlist)
   (APPEND (SUB_LIST(16*i+8,4) inlist) (SUB_LIST(16*i+12,4) inlist)))`,
  MP_TAC(ISPECL[`inlist:byte list`;`4`;`12`;`16*i`] SUB_LIST_SPLIT) THEN
  MP_TAC(ISPECL[`inlist:byte list`;`4`;`8`;`16*i+4`] SUB_LIST_SPLIT) THEN
  MP_TAC(ISPECL[`inlist:byte list`;`4`;`4`;`16*i+8`] SUB_LIST_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `(16*i+4)+4=16*i+8`; ARITH_RULE `(16*i+8)+4=16*i+12`;
    ARITH_RULE `4+8=12`; ARITH_RULE `4+4=8`; ARITH_RULE `4+12=16`] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC);;

let MM_4G_4G = prove(`!a. a MOD 4294967296 MOD 4294967296 = a MOD 4294967296`, REWRITE_TAC[MOD_MOD_REFL]);;

let MM_4G_18 = prove(`!a. a MOD 4294967296 MOD 18446744073709551616 = a MOD 4294967296`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL[`a:num`;`4294967296`] MOD_LT_EQ) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* STORE4_FROM_SPEC: derive `read(bytes(addr,4)) sN = val(word_sx ...)` from a *)
(* spec-form bytes32 store hypothesis.                                       *)

let STORE4_FROM_SPEC sN addrt =
  REWRITE_TAC[bytes32; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN REWRITE_TAC[VAL_WORD] THEN
  SUBGOAL_THEN (subst[sN,`s:x86state`;addrt,`a:int64`]
     `read (bytes (a:int64,4)) (read memory (s:x86state)) < 2 EXP dimindex(:32)`) ASSUME_TAC THENL
   [REWRITE_TAC[DIMINDEX_32] THEN
    MP_TAC(ISPECL[addrt;`4`;mk_comb(`read memory:x86state->int64->byte`,sN)] READ_BYTES_BOUND) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;;

let JA_TAKEN_GT = prove
 (`!a k:num. k < a /\ a < 2 EXP 32
     ==> ~(~(&(val(word_zx(word a:int64):int32)):int - &k =
             &(val(word_sub(word_zx(word a:int64):int32) (word k):int32))) \/
           val(word_sub(word_zx(word a:int64):int32) (word k):int32) = 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx(word a:int64):int32) = a` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX_64_32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (word_zx(word a:int64):int32) (word k:int32)) = a - k` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val(word k:int32) = k` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL [REFL_TAC; REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(a - k = 0) <=> F` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MP_TAC(SPECL[`k:num`;`a:num`] INT_OF_NUM_SUB) THEN ANTS_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC) THEN REWRITE_TAC[]]);;

(* RCX4_COLLAPSE: collapse the stepped RCX +4 nest word_zx(word_add(word_zx  *)
(* (word a))(word 4)) to word(a+4) when a+4 < 2^32.                          *)

let RCX4_COLLAPSE = prove
 (`!a:num. a + 4 < 2 EXP 32 ==> word_zx(word_add(word_zx(word a:int64):int32)(word 4:int32)):int64 = word(a + 4)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_64; DIMINDEX_32; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  SUBGOAL_THEN `a MOD 2 EXP 64 = a` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  SUBGOAL_THEN `(a + 4) MOD 2 EXP 32 = a + 4` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; REFL_TAC]);;

(*** Bytecode extracted from rej_uniform_eta2_avx2_asm.o (.text section) ***)

let REJ_NIBBLES_ETA2_EMPTY = prove
 (`REJ_NIBBLES_ETA2 [] = []`,
  REWRITE_TAC[REJ_NIBBLES_ETA2; NIBBLES_OF_BYTES; FILTER]);;

let REJ_NIBBLES_ETA2_APPEND = prove
 (`!l1 l2. REJ_NIBBLES_ETA2(APPEND l1 l2) =
           APPEND (REJ_NIBBLES_ETA2 l1) (REJ_NIBBLES_ETA2 l2)`,
  REWRITE_TAC[REJ_NIBBLES_ETA2; NIBBLES_OF_BYTES_APPEND; FILTER_APPEND]);;

(* Loop step: peel off 16 bytes per iteration. Used in loop body.            *)
let REJ_NIBBLES_ETA2_STEP_16 = prove
 (`!inlist:byte list. !i:num.
   16 * (i + 1) <= LENGTH inlist
   ==> REJ_NIBBLES_ETA2(SUB_LIST(0, 16 * (i + 1)) inlist) =
       APPEND (REJ_NIBBLES_ETA2(SUB_LIST(0, 16 * i) inlist))
              (REJ_NIBBLES_ETA2(SUB_LIST(16 * i, 16) inlist))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REJ_NIBBLES_ETA2_APPEND] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `16 * (i + 1) = 0 + 16 * i + 16` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUB_LIST_SPLIT; SUB_LIST_CLAUSES; APPEND; ADD_CLAUSES]);;

(* Length bound on filtered nibbles - used for ABBREV bounds                 *)
let LENGTH_REJ_NIBBLES_ETA2 = prove
 (`!l:byte list. LENGTH(REJ_NIBBLES_ETA2 l) <= 2 * LENGTH l`,
  GEN_TAC THEN REWRITE_TAC[REJ_NIBBLES_ETA2] THEN
  TRANS_TAC LE_TRANS `LENGTH(NIBBLES_OF_BYTES l:int16 list)` THEN
  CONJ_TAC THENL [REWRITE_TAC[LENGTH_FILTER]; ALL_TAC] THEN
  SPEC_TAC(`l:byte list`,`l:byte list`) THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[NIBBLES_OF_BYTES; LENGTH; NIBBLE_PAIR;
                  APPEND; LENGTH_APPEND; LE_0] THEN
  UNDISCH_TAC `LENGTH(NIBBLES_OF_BYTES t:int16 list) <=
               2 * LENGTH(t:byte list)` THEN ARITH_TAC);;

(* General prefix monotonicity of the accepted-nibble count.                 *)
let NIBLEN_PREFIX_MONO = prove
 (`!l:byte list a b. a <= b
     ==> LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(0,a) l):int16 list) <=
         LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(0,b) l):int16 list)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `SUB_LIST(0,b) (l:byte list) =
                APPEND (SUB_LIST(0,a) l) (SUB_LIST(a,b-a) l)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`l:byte list`; `a:num`; `b - a`; `0`] SUB_LIST_SPLIT) THEN
    ASM_SIMP_TAC[ARITH_RULE `a <= b ==> a + (b - a) = b`; ADD_CLAUSES];
    REWRITE_TAC[REJ_NIBBLES_ETA2_APPEND; LENGTH_APPEND] THEN ARITH_TAC]);;

(* ========================================================================= *)
(* eta2 CORRECT: sub-iter list decomposition + coefficient bounds.           *)
(* The eta2 coefficient bound is [-2,2] (ival in (-3,3)).                    *)
(* Uses REJ_NIBBLES_ETA2, REJ_SAMPLE_ETA2_BYTES.                             *)
(* ========================================================================= *)

(* REJ_SAMPLE_ETA2_BYTES decomposition: append on lists.                     *)
let REJ_SAMPLE_ETA2_BYTES_APPEND = prove
 (`!l1 l2:byte list. REJ_SAMPLE_ETA2_BYTES (APPEND l1 l2) =
                     APPEND (REJ_SAMPLE_ETA2_BYTES l1)
                            (REJ_SAMPLE_ETA2_BYTES l2)`,
  REWRITE_TAC[REJ_SAMPLE_ETA2_BYTES; REJ_NIBBLES_ETA2_APPEND; MAP_APPEND]);;

(* int32-list length = int16-nibble-list length (MAP preserves length).      *)
let LENGTH_REJ_SAMPLE_ETA2_BYTES = prove
 (`!l:byte list.
     LENGTH(REJ_SAMPLE_ETA2_BYTES l:int32 list) =
     LENGTH(REJ_NIBBLES_ETA2 l:int16 list)`,
  REWRITE_TAC[REJ_SAMPLE_ETA2_BYTES; LENGTH_MAP]);;

let LENGTH_REJ_SAMPLE_ETA2_BYTES_BOUND = prove
 (`!l:byte list. LENGTH(REJ_SAMPLE_ETA2_BYTES l:int32 list) <= 2 * LENGTH l`,
  GEN_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES; LENGTH_REJ_NIBBLES_ETA2]);;

(* Generic prefix monotonicity for the int32 form.                           *)
let LENGTH_REJ_SAMPLE_ETA2_BYTES_APPEND_LE = prove
 (`!l1 l2:byte list.
     LENGTH(REJ_SAMPLE_ETA2_BYTES l1:int32 list) <=
     LENGTH(REJ_SAMPLE_ETA2_BYTES (APPEND l1 l2):int32 list)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REJ_SAMPLE_ETA2_BYTES_APPEND; LENGTH_APPEND] THEN ARITH_TAC);;

(* SUB_LIST length cap: outlist length <= 256.                               *)
let LENGTH_SUB_LIST_REJ_SAMPLE_ETA2_BYTES = prove
 (`!(l:byte list).
     LENGTH(SUB_LIST(0,256) (REJ_SAMPLE_ETA2_BYTES l):int32 list) <= 256`,
  GEN_TAC THEN REWRITE_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Coefficient bound: each accepted eta2 coefficient is in [-2,2], i.e.      *)
(* ival in (-3,3). Ported from arm-eta2 REJ_SAMPLE_ETA2_ELEMENT_BOUND.       *)
(* ------------------------------------------------------------------------- *)

let REJ_SAMPLE_ETA2_ELEMENT_BOUND = prove
 (`!x:int16. val x < 15
    ==> ival(word_sx(word_sub (word 2:int16) (word_umod x (word 5:int16))):int32) < &3 /\
        -- &3 < ival(word_sx(word_sub (word 2:int16) (word_umod x (word 5:int16))):int32)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`x:int16`; `word 5:int16`] VAL_WORD_UMOD) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `word_umod (x:int16) (word 5) = word(val x MOD 5):int16`
    SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(x:int16) < 15` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(x:int16) MOD 5 = 0 \/ val x MOD 5 = 1 \/
                val x MOD 5 = 2 \/ val x MOD 5 = 3 \/ val x MOD 5 = 4` MP_TAC THENL
   [MP_TAC(SPECL [`val(x:int16)`; `5`] MOD_LT_EQ) THEN ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

(* Per-element form over the int32 sample list (for SUBROUTINE array_bound). *)
let REJ_SAMPLE_ETA2_BYTES_COEFF_BOUND = prove
 (`!(l:byte list) c:int32.
     MEM c (REJ_SAMPLE_ETA2_BYTES l)
     ==> --(&3):int < ival c /\ ival c < &3`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REJ_SAMPLE_ETA2_BYTES; REJ_NIBBLES_ETA2; MEM_MAP; MEM_FILTER] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `x:int16` REJ_SAMPLE_ETA2_ELEMENT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let REJ_SAMPLE_ETA2_BYTES_EL_BOUND = prove
 (`!(l:byte list) i.
     i < LENGTH(SUB_LIST(0,256) (REJ_SAMPLE_ETA2_BYTES l):int32 list)
     ==> ival(EL i (SUB_LIST(0,256) (REJ_SAMPLE_ETA2_BYTES l):int32 list)) < &3 /\
         -- &3 < ival(EL i (SUB_LIST(0,256) (REJ_SAMPLE_ETA2_BYTES l):int32 list))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`l:byte list`;
                 `EL i (SUB_LIST(0,256) (REJ_SAMPLE_ETA2_BYTES (l:byte list)):int32 list):int32`]
                REJ_SAMPLE_ETA2_BYTES_COEFF_BOUND) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`REJ_SAMPLE_ETA2_BYTES (l:byte list):int32 list`; `256`]
                  SUB_LIST_TOPSPLIT) THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THEN
    REWRITE_TAC[MEM_APPEND] THEN DISJ1_TAC THEN
    MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[];
    INT_ARITH_TAC]);;

(* Strengthen-post lemma: ensures with implied stronger post. (Generic.)     *)
let VAL_WORD_ZX_BYTE_LT_15 = prove
 (`!b:byte. (val (word_zx b:int16) < 15) <=> (val b < 15)`,
  GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VAL_WORD_ZX THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_16] THEN ARITH_TAC);;

(* popcnt low-byte bound <= 8.                                               *)
let VPSUBB_SIGN_BIT_LT_15 = prove
 (`!a:byte. val a < 16
     ==> (bit 7 (word_sub a (word 15):byte) <=> val a < 15)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_VAL; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VAL_WORD_SUB; DIMINDEX_8; VAL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `val(a:byte) < 15` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(val(a:byte) + 241) MOD 256 = val a + 241`
    SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[ODD; ARITH_RULE `ODD 1`] `n = 1 ==> ODD n`) THEN
    MATCH_MP_TAC DIV_UNIQ THEN
    EXISTS_TAC `val(a:byte) + 113` THEN ASM_ARITH_TAC;
    REWRITE_TAC[NOT_ODD] THEN
    SUBGOAL_THEN `(val(a:byte) + 241) MOD 256 = val a - 15`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `val(a:byte) + 241 = (val a - 15) + 1 * 256`
      SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[DIV_LT; EVEN] THEN ASM_ARITH_TAC]);;

(* Nibble-extraction helpers (threshold-independent).                        *)
let LENGTH_FILTER_LT_15_MAP_WORD_ZX = prove
 (`!l:byte list. LENGTH(FILTER (\x:int16. val x < 15) (MAP word_zx l)) =
                  LENGTH(FILTER (\x:byte. val x < 15) l)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; FILTER; LENGTH; VAL_WORD_ZX_BYTE_LT_15] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH]);;

(* Byte-form LENGTH FILTER for the 8 nibbles of 4 bytes = REJ_NIBBLES_ETA2.  *)
let LENGTH_FILTER_BYTE_NIBBLES_4_BYTES = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte).
     LENGTH(FILTER (\x:byte. val x < 15)
             [word(val b0 MOD 16); word(val b0 DIV 16);
              word(val b1 MOD 16); word(val b1 DIV 16);
              word(val b2 MOD 16); word(val b2 DIV 16);
              word(val b3 MOD 16); word(val b3 DIV 16)]) =
     LENGTH(REJ_NIBBLES_ETA2 [b0;b1;b2;b3]:int16 list)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REJ_NIBBLES_ETA2; NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND] THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(SPEC
   `[word(val(b0:byte) MOD 16); word(val(b0:byte) DIV 16);
     word(val(b1:byte) MOD 16); word(val(b1:byte) DIV 16);
     word(val(b2:byte) MOD 16); word(val(b2:byte) DIV 16);
     word(val(b3:byte) MOD 16); word(val(b3:byte) DIV 16)]:byte list`
   LENGTH_FILTER_LT_15_MAP_WORD_ZX) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MAP] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[CONS_11; PAIR_EQ] THEN
  REPEAT CONJ_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC WORD_ZX_BYTE_TO_INT16 THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

(* ========================================================================= *)
(* eta2 CORRECT: table-gather / VPSHUFB compaction lemmas.                   *)
(* These operate on the shared mldsa_rej_uniform_table + VPSHUFB gather      *)
(* semantics, so they are coefficient- and threshold-independent, EXCEPT     *)
(* the accept predicate is n < 15 (eta2 accepts n<15).                       *)
(* From SUBITER_STORE on, the store VALUE is eta2-specific (mod-5 reduction, *)
(* composing the per-lane red_lane chain).                                   *)
(* NB TABLE_PREFIX_ACC is a 256-mask eval.                                   *)
(* ========================================================================= *)

(* SUBITER_STORE (byte form), eta2 centering 2-n and accept <15.             *)
let SUBITER_STORE = prove
 (`!(g:int128) (m:byte) (n0:byte) n1 n2 n3 n4 n5 n6 n7.
    val n0 < 16 /\ val n1 < 16 /\ val n2 < 16 /\ val n3 < 16 /\
    val n4 < 16 /\ val n5 < 16 /\ val n6 < 16 /\ val n7 < 16 /\
    (!j. j < 8 ==> (bit j m <=> val(EL j [n0;n1;n2;n3;n4;n5;n6;n7]:byte) < 15)) /\
    (!j. j < 8 ==> word_subword g (8*j,8):byte =
                   word_sub (word 2) (EL j [n0;n1;n2;n3;n4;n5;n6;n7]))
    ==> SUB_LIST(0, LENGTH(ACC_IDX m)) (PSHUFB_OUT_LIST g m) =
        MAP (\x:byte. word_sub (word 2) x)
            (FILTER (\x:byte. val x < 15) [n0;n1;n2;n3;n4;n5;n6;n7])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g:int128`; `val(m:byte)`] PSHUFB_ACCEPTED_PREFIX_NUM) THEN
  REWRITE_TAC[WORD_VAL] THEN
  ANTS_TAC THENL
   [MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ACC_IDX] THEN
  MP_TAC(ISPECL [`\x:byte. word_sub (word 2) x:byte`; `\x:byte. val x < 15`;
                 `n0:byte`;`n1:byte`;`n2:byte`;`n3:byte`;`n4:byte`;`n5:byte`;`n6:byte`;`n7:byte`]
                GATHER_FILTER_MAP_IDX_8) THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `(!j. MEM j [0;1;2;3;4;5;6;7] ==> (bit j (m:byte) <=> val(EL j [n0;n1;n2;n3;n4;n5;n6;n7]:byte) < 15)) /\
    (!j. MEM j [0;1;2;3;4;5;6;7] ==> word_subword (g:int128) (8*j,8):byte =
                   word_sub (word 2) (EL j [n0;n1;n2;n3;n4;n5;n6;n7]))`
   MP_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[MEM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN
  REWRITE_TAC[FILTER; MAP; MEM] THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then
      (MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN
       MP_TAC(SPEC `3` th) THEN MP_TAC(SPEC `4` th) THEN MP_TAC(SPEC `5` th) THEN
       MP_TAC(SPEC `6` th) THEN MP_TAC(SPEC `7` th))
    else NO_TAC)) THEN
  REWRITE_TAC[MEM] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV EL_CONV)) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN ASM_REWRITE_TAC[]);;

(* Byte vs int16 centered value sign-extend to the same int32, for n<15.     *)
(* eta2 15-way blast.                                                        *)
let SX_SUB2_BYTE_EQ_INT16 = prove
 (`!n. n < 15
       ==> word_sx(word_sub (word 2:byte) (word n:byte)):int32 =
           word_sx(word_sub (word 2:int16) (word n:int16)):int32`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
    `n < 15 ==> n=0\/n=1\/n=2\/n=3\/n=4\/n=5\/n=6\/n=7\/n=8\/
                n=9\/n=10\/n=11\/n=12\/n=13\/n=14`)) THEN
  POP_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  CONV_TAC WORD_BLAST);;

(* SUBITER_STORE (int32 form), eta2: the sign-extended centered store value. *)
(* This is BEFORE the mod-5 reduction — lanes are word_sx(word_sub 2 v).     *)
let SUBITER_STORE_INT32 = prove
 (`!(g:int128) (m:byte) v0 v1 v2 v3 v4 v5 v6 v7.
    v0<16/\v1<16/\v2<16/\v3<16/\v4<16/\v5<16/\v6<16/\v7<16 /\
    (!j. j < 8 ==> (bit j m <=> EL j [v0;v1;v2;v3;v4;v5;v6;v7] < 15)) /\
    (!j. j < 8 ==> word_subword g (8*j,8):byte =
                   word_sub (word 2) (word(EL j [v0;v1;v2;v3;v4;v5;v6;v7]):byte))
    ==> MAP (\b:byte. word_sx b:int32)
            (SUB_LIST(0, LENGTH(ACC_IDX m)) (PSHUFB_OUT_LIST g m)) =
        MAP (\v. word_sx(word_sub (word 2:int16) (word v)):int32)
            (FILTER (\v. v < 15) [v0;v1;v2;v3;v4;v5;v6;v7])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g:int128`; `m:byte`;
    `word v0:byte`;`word v1:byte`;`word v2:byte`;`word v3:byte`;
    `word v4:byte`;`word v5:byte`;`word v6:byte`;`word v7:byte`] SUBITER_STORE) THEN
  SUBGOAL_THEN `val(word v0:byte)=v0/\val(word v1:byte)=v1/\val(word v2:byte)=v2/\
                val(word v3:byte)=v3/\val(word v4:byte)=v4/\val(word v5:byte)=v5/\
                val(word v6:byte)=v6/\val(word v7:byte)=v7`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN
      `!j. j < 8 ==> val(EL j [word v0;word v1;word v2;word v3;
                               word v4;word v5;word v6;word v7]:byte) =
                     EL j [v0;v1;v2;v3;v4;v5;v6;v7]`
      ASSUME_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`
        (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THENL
       [ASM_ARITH_TAC; ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC] THEN
      CONV_TAC(DEPTH_CONV EL_CONV) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        let s=string_of_term(concl th) in
        let h n=let nl=String.length n and hl=String.length s in
          let rec go i=if i+nl>hl then false else if String.sub s i nl=n then true else go(i+1) in go 0 in
        h "bit j")) THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        let s=string_of_term(concl th) in
        let h n=let nl=String.length n and hl=String.length s in
          let rec go i=if i+nl>hl then false else if String.sub s i nl=n then true else go(i+1) in go 0 in
        h "word_subword")) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`
        (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THENL
       [ASM_ARITH_TAC; ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC] THEN
      CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM MAP_o; o_DEF] THEN
  REWRITE_TAC[FILTER; MAP] THEN ASM_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP]) THEN
  ASM_SIMP_TAC[SX_SUB2_BYTE_EQ_INT16]);;

(* ========================================================================= *)
(* eta2 CORRECT: the SUBITER_STORE_SPEC crux.                                *)
(*                                                                           *)
(* After the pre-gather centering (2 - nibble), the table gather (vpshufb),  *)
(* and the sign-extend (vpmovsxbd), the eta2 body runs the int32-lane mod-5  *)
(* reduction                                                                 *)
(*   vpmulhrsw ymm6,ymm1,ymm2 ; vpmullw ymm7,ymm2,ymm2 ; vpaddd ymm2,ymm1,ymm1 *)
(* (asm 0xa7-0xb0) before the vmovdqu store.  The store lane j is            *)
(*   word_add (word_subword v (32j,32))                                      *)
(*            (word_subword <mullw(mulhrs(v,0xe660),5)> (32j,32))            *)
(* with v = the vpmovsxbd output (word_sx of the gathered centered byte).    *)
(* This is exactly the eta2 per-lane mod-5 reduction chain, captured here as *)
(* red_lane : int32 -> int32.  We then compose it through the gather         *)
(* compaction to give the full                                               *)
(* sub-iter store value = REJ_SAMPLE_ETA2_BYTES [b0;b1;b2;b3].               *)
(* ========================================================================= *)

(* The int32-lane reduction, as a function of the vpmovsxbd output lane v.   *)
(* red_lane v = word_add v (mullw-join-of-mulhrs), matching the stepper form. *)
let red_lane = new_definition
  `red_lane (v:int32):int32 =
     word_add v
       (word_join
          (word_mul (mulhrs_eta2 (word_subword v (16,16)) (word 0xe660:int16))
                    (word 5:int16))
          (word_mul (mulhrs_eta2 (word_subword v (0,16)) (word 0xe660:int16))
                    (word 5:int16))
        : int32)`;;

(* Per-lane spec: for an accepted nibble n (< 15), applying red_lane to the  *)
(* sign-extend of the centered byte (2 - n) recovers the eta=2 coefficient   *)
(*   2 - (n MOD 5)  as a sign-extended int32 (int16-umod form, matching      *)
(* REJ_SAMPLE_ETA2_BYTES's element).  This is the per-lane mod-5 reduction   *)
(* with the RHS restated in the int16-word-umod shape; proven directly by 15-way *)
(* WORD_REDUCE so it can slot straight into the composition below.           *)
let RED_LANE_SPEC = prove
 (`!n. n < 15
       ==> red_lane (word_sx (word_sub (word 2:byte) (word n:byte)):int32)
           = word_sx (word_sub (word 2:int16)
                               (word_umod (word n:int16) (word 5:int16))):int32`,
  REWRITE_TAC[red_lane; mulhrs_eta2] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* Same, on the int16-centered form (word_sub (word 2:int16) (word v)) that  *)
(* SUBITER_STORE_INT32 actually produces. Bridged from RED_LANE_SPEC         *)
(* by SX_SUB2_BYTE_EQ_INT16 which equates the byte- and int16-centered       *)
(* sign-extensions for v < 15.                                               *)
let RED_LANE_SPEC_I16 = prove
 (`!v. v < 15
       ==> red_lane (word_sx (word_sub (word 2:int16) (word v)):int32)
           = word_sx (word_sub (word 2:int16)
                               (word_umod (word v:int16) (word 5:int16))):int32`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `v:num` RED_LANE_SPEC) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `v:num` SX_SUB2_BYTE_EQ_INT16) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* Push a num->int16 word-cast through MAP/FILTER.                           *)
let FILTER_VAL_WORD_NIB = prove
 (`!L:num list. (!v. MEM v L ==> v < 16)
     ==> FILTER (\v. val(word v:int16) < 15) L = FILTER (\v. v < 15) L`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MEM] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word h:int16) = h` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_16] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `h:num`) THEN REWRITE_TAC[MEM] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FILTER (\v. val(word v:int16) < 15) t = FILTER (\v. v < 15) t`
    SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* THE CRUX: SUBITER_STORE_SPEC (eta2 spec form).                            *)
(*                                                                           *)
(* The full sub-iter SIMD store value — MAP red_lane over the sign-extended  *)
(* gather (i.e. the vpmulhrsw/vpmullw/vpaddd int32-lane mod-5 reduction      *)
(* applied to each vpmovsxbd lane) — equals REJ_SAMPLE_ETA2_BYTES on the     *)
(* 4-byte block [b0;b1;b2;b3].  The two hypotheses (accept mask m, and the   *)
(* gather source g holding the centered (2 - nibble) bytes) are discharged in *)
(* the loop body from the proven nibble-extract, VPSUBB_SIGN_BIT_LT_15 and   *)
(* VPMOVMSKB lane lemmas.  Composed 4x per iteration and stitched via the    *)
(* 16-as-4 decomposition.                                                    *)
let SUBITER_STORE_SPEC = prove
 (`!(g:int128) (m:byte) (b0:byte) b1 b2 b3.
    (!j. j < 8 ==> (bit j m <=>
        EL j [val b0 MOD 16; val b0 DIV 16; val b1 MOD 16; val b1 DIV 16;
              val b2 MOD 16; val b2 DIV 16; val b3 MOD 16; val b3 DIV 16] < 15)) /\
    (!j. j < 8 ==> word_subword g (8*j,8):byte =
        word_sub (word 2) (word(EL j [val b0 MOD 16; val b0 DIV 16; val b1 MOD 16; val b1 DIV 16;
              val b2 MOD 16; val b2 DIV 16; val b3 MOD 16; val b3 DIV 16]):byte))
    ==> MAP red_lane
            (MAP (\b:byte. word_sx b:int32)
                 (SUB_LIST(0, LENGTH(ACC_IDX m)) (PSHUFB_OUT_LIST g m))) =
        REJ_SAMPLE_ETA2_BYTES [b0;b1;b2;b3]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g:int128`; `m:byte`;
    `val(b0:byte) MOD 16`; `val(b0:byte) DIV 16`; `val(b1:byte) MOD 16`; `val(b1:byte) DIV 16`;
    `val(b2:byte) MOD 16`; `val(b2:byte) DIV 16`; `val(b3:byte) MOD 16`; `val(b3:byte) DIV 16`]
    SUBITER_STORE_INT32) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
    MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN
    SIMP_TAC[MOD_LT_EQ; ARITH_EQ; RDIV_LT_EQ] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM MAP_o] THEN
  REWRITE_TAC[REJ_SAMPLE_ETA2_BYTES; REJ_NIBBLES_ETA2] THEN
  SUBGOAL_THEN
   `NIBBLES_OF_BYTES [b0;b1;b2;b3] =
    MAP (word:num->int16)
        [val b0 MOD 16; val b0 DIV 16; val b1 MOD 16; val b1 DIV 16;
         val b2 MOD 16; val b2 DIV 16; val b3 MOD 16; val b3 DIV 16]`
   SUBST1_TAC THENL
   [REWRITE_TAC[NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND; MAP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:int16. word_sx(word_sub (word 2) (word_umod x (word 5))):int32`;
    `\x:int16. val x < 15`;
    `[val(b0:byte) MOD 16; val b0 DIV 16; val(b1:byte) MOD 16; val b1 DIV 16;
      val(b2:byte) MOD 16; val b2 DIV 16; val(b3:byte) MOD 16; val b3 DIV 16]`]
    MAP_FILTER_WORD_NIB) THEN
  SUBGOAL_THEN
   `!v. MEM v [val(b0:byte) MOD 16; val b0 DIV 16; val(b1:byte) MOD 16; val b1 DIV 16;
               val(b2:byte) MOD 16; val b2 DIV 16; val(b3:byte) MOD 16; val b3 DIV 16]
        ==> v < 16`
   ASSUME_TAC THENL
   [REWRITE_TAC[MEM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
    MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN
    SIMP_TAC[MOD_LT_EQ; ARITH_EQ; RDIV_LT_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[o_DEF] THEN
  ASM_SIMP_TAC[FILTER_VAL_WORD_NIB] THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  X_GEN_TAC `v:num` THEN REWRITE_TAC[MEM_FILTER] THEN STRIP_TAC THEN
  MP_TAC(SPEC `v:num` RED_LANE_SPEC_I16) THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* eta2 CORRECT: EXEC rule + LENGTH lemma.                                   *)
(*                                                                           *)
(* The core exec rule that drives every X86_STEPS_TAC in the body/scalar-tail *)
(* proof, plus the trimmed-mc LENGTH.                                        *)
(* ========================================================================= *)

let MLDSA_REJ_UNIFORM_ETA2_EXEC =
  X86_MK_CORE_EXEC_RULE mldsa_rej_uniform_eta2_tmc;;

let LENGTH_MLDSA_REJ_UNIFORM_ETA2_TMC =
  REWRITE_CONV[mldsa_rej_uniform_eta2_tmc] `LENGTH mldsa_rej_uniform_eta2_tmc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

(* ========================================================================= *)
(* eta2 CORRECT: prologue stepping to loop-top, all 5 constants.             *)
(*                                                                           *)
(* eta2 loads FIVE vector constants and, for the two mod-5 int16 constants   *)
(* (0xe660 and 5), the asm uses  vpinsrw $0,r8d,xmm,xmm ; vpbroadcastw.      *)
(* vpinsrw reads the PRIOR (ghost, uninitialised) xmm register for lanes 1..7, *)
(* so the stepper's auto-simplifier leaves                                   *)
(*   read YMM6 s = word_duplicate (word_subword (word_zx (word_zx            *)
(*        (word_insert (word_zx (read YMM6 s_ghost)) (0,16) (word 58976))))) *)
(* which references the ghost state and is therefore DISCARDED by            *)
(* DISCARD_OLDSTATE_TAC — so a plain X86_STEPS_TAC through the prologue      *)
(* yields NO read YMM6 / read YMM7 fact at all.                              *)
(*                                                                           *)
(* The fix: vpbroadcastw broadcasts lane 0 (which vpinsrw fully set to the   *)
(* immediate) across all 16 int16 lanes, so the ghost dependence is vacuous  *)
(* and WORD_BLAST collapses the whole form to word_duplicate(word imm:int16). *)
(* We step the two vpinsrw/vpbroadcastw pairs VERBOSELY (no auto-discard),   *)
(* rewrite each YMMk with its WORD_BLAST-collapsed constant, then discard the *)
(* ghost states.  The two int16-broadcast constants are:                     *)
(*   YMM6 = word_duplicate (word 0xe660:int16) = word 104203162506446325...  *)
(*   YMM7 = word_duplicate (word 5:int16)      = word 8834370125682169483... *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* The two int16-broadcast constants, as word_duplicate <-> numeral bridges. *)
(* Kept as named lemmas so the prologue tactic (and later the loop-invariant *)
(* discharge) can rewrite YMM6/YMM7 to a canonical numeral form.             *)
let YMM6_CONST_ETA2 = prove
 (`word_duplicate (word 58976:int16):int256 =
   word 104203162506446325494781756494581186443189907921581107878096444258040508638816`,
  CONV_TAC WORD_REDUCE_CONV);;

let YMM7_CONST_ETA2 = prove
 (`word_duplicate (word 5:int16):int256 =
   word 8834370125682169483754557489027840684616615904908870377619408255734579205`,
  CONV_TAC WORD_REDUCE_CONV);;

(* The vpbroadcastw-collapse: the raw stepper form for YMM6/YMM7 after the   *)
(* vpinsrw ; vpbroadcastw pair collapses (by WORD_BLAST) to the constant,    *)
(* INDEPENDENT of the ghost prior register value.  The intermediate word_zx  *)
(* widths are simulator-determined (do NOT hand-type them — that invents type *)
(* variables that WORD_REDUCE cannot close), so we apply the collapse as an  *)
(* IN-CONTEXT step on whatever `read <ymm> sN = <form>` assumption the stepper *)
(* actually produced.                                                        *)
(*                                                                           *)
(* COLLAPSE_VPBW_TAC ymmread bridge: given the ghost-carrying assumption     *)
(*   read <ymm> sN = rhs   (rhs contains word_insert of the ghost register), *)
(* and a bridge  |- word_duplicate (word imm:int16):int256 = word <const>,   *)
(* prove  rhs = word_duplicate(word imm)  by WORD_BLAST on the CONCRETE rhs  *)
(* (fully typed, ghost atomic -> no type invention), TRANS with the bridge to *)
(* get  rhs = word <const>, and rewrite the assumption to  read <ymm> sN =   *)
(* word <const>.  The constant fact then propagates through the remaining    *)
(* plain steps like YMM3/4/5 do.                                             *)
let COLLAPSE_VPBW_TAC (ymmread:term) (bridge:thm) : tactic =
  W(fun (asl,w) ->
    let tgt = find (fun t -> is_eq t && lhand t = ymmread)
                   (map (fun (_,th) -> concl th) asl) in
    let rhs = rand tgt in
    let dup = lhand(concl bridge) in
    let blast_eq = WORD_BLAST (mk_eq(rhs, dup)) in    (* |- rhs = word_duplicate(word imm) *)
    let full = TRANS blast_eq bridge in                (* |- rhs = word <const> *)
    RULE_ASSUM_TAC(REWRITE_RULE[full]));;

(* ========================================================================= *)
(* eta2 CORRECT: the CLEAN_BODY goal statement.                              *)
(*                                                                           *)
(* The per-iteration SIMD body obligation: from the loop top (pc+86) at      *)
(* position 16*i with outlen accepted coeffs stored, run one 16-byte block   *)
(* (4 sub-iters) back to the loop top at position 16*(i+1).                  *)
(*                                                                           *)
(* Key eta2 facts:                                                           *)
(*   - pc-length 543, buf 136, loop top pc+86.                               *)
(*   - FIVE YMM consts: YMM6 (0xe660 x16) + YMM7 (5 x16) are the mod-5       *)
(*     reduction constants the in-body vpmulhrsw/vpmullw consume.            *)
(*   - MAYCHANGE ZMM set = body-touched regs [ZMM0;ZMM1;ZMM2;ZMM8;ZMM9]:     *)
(*     ymm0 vpmovzxbw, ymm1 shift/shuffle/sxbd/paddd, ymm2 mulhrsw/mullw     *)
(*     reduction temp, ymm8 gather-source (vextracti128/vpsrldq), ymm9 table *)
(*     lane (vmovq/vpshufb).                                                 *)
(*   - niblen bound 248: head-guard cmp eax,0xf8 (=248).                     *)
(*                                                                           *)
(* Body offset map (trimmed mc, read off MLDSA_REJ_UNIFORM_ETA2_EXEC):       *)
(*   loop top pc+86 cmp eax,0xf8 ; pc+91 ja scalar ; pc+97 cmp ecx,0x78 ;    *)
(*   pc+100 ja scalar ; SIMD sub-iter-1 pc+106 vpmovzxbw .. pc+176 vmovdqu   *)
(*   store (incl mod-5 vpmulhrsw@163/vpmullw@168/vpaddd@172), pc+181 popcnt .. *)
(*   pc+196 cmp eax,0xf8 ; pc+201 ja (mid-guard) ; sub-iters 2/3/4 similar.  *)
(* ========================================================================= *)

let clean_body_eta2_tm = `
   !res buf table (inlist:byte list) pc N (i:num) stackpointer.
        LENGTH inlist = 136 /\
        nonoverlapping_modulo (2 EXP 64) (pc, 543) (val res,1024) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 543) (val buf, 136) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 543) (val table,2048) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 136) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table,2048) /\
        ~(N = 0) /\ i + 1 < N /\ 16 * (i + 1) <= 136 /\
        LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(0, 16 * (i+1)) inlist)) <= 248
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
                  read RIP s = word(pc + 86) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  read YMM3 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
                  read YMM4 s = word 908173248920127022929968509872062022378588115024631874819275168689514742274 /\
                  read YMM5 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
                  read YMM6 s = word 104203162506446325494781756494581186443189907921581107878096444258040508638816 /\
                  read YMM7 s = word 8834370125682169483754557489027840684616615904908870377619408255734579205 /\
                  read RAX s = word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list)) /\
                  read RCX s = word(16*i) /\
                  read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list))) s = num_of_wordlist(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist)))
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
                  read RIP s = word(pc + 86) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  read YMM3 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
                  read YMM4 s = word 908173248920127022929968509872062022378588115024631874819275168689514742274 /\
                  read YMM5 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
                  read YMM6 s = word 104203162506446325494781756494581186443189907921581107878096444258040508638816 /\
                  read YMM7 s = word 8834370125682169483754557489027840684616615904908870377619408255734579205 /\
                  read RAX s = word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*(i+1)) inlist):int32 list)) /\
                  read RCX s = word(16*(i+1)) /\
                  read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*(i+1)) inlist):int32 list))) s = num_of_wordlist(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*(i+1)) inlist)))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM8; ZMM9] ,,
              MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`;;

(* ========================================================================= *)
(* eta2 CORRECT: the nibble-extraction / gather / mask lemma family.         *)
(*                                                                           *)
(* These are the byte-structure lemmas the CLEAN_BODY prefix (PREFIX_G) and  *)
(* the sub-iter store folds depend on.  They describe, purely at the word    *)
(* level (no ISA stepping), the SIMD nibble-extraction chain and the two     *)
(* vpsubb constants of the eta2 body:                                        *)
(*                                                                           *)
(*   nibchain(q) = vpand (vpor (vpmovzxbw q) (vpsllw $4 ...)) 0x0f0f0f0f     *)
(*     -> byte 2j = val(q byte j) MOD 16, byte 2j+1 = val(q byte j) DIV 16   *)
(*        (F0NIB_BYTES_ETA2 / _HI).                                          *)
(*   center vpsubb ymm4,ymm0,ymm0  (ymm4 = 0x02020202 broadcast)             *)
(*     -> byte j = word_sub (word 2) (nibchain byte j).                      *)
(*        eta2 centres with 0x02.                                            *)
(*   accept vpsubb ymm5,ymm0,ymm1  (ymm5 = 0x0f0f0f0f broadcast)             *)
(*     -> byte j = word_sub (nibchain byte j) (word 15).                     *)
(*        eta2 subtracts 0x0f (accept nibble < 15).                          *)
(*                                                                           *)
(* Composed:                                                                 *)
(*   the centred gather source byte j = word_sub (word 2) (word nibble_j)    *)
(*       — SUBITER_STORE_SPEC's gather hyp.                                  *)
(*   the accept byte: bit 7 <=> nibble_j < 15 — the vpmovmskb input, giving  *)
(*       SUBITER_STORE_SPEC's mask hyp.                                      *)
(*   MASK_LOW_BIT : the vpmovmskb bit-packing bridge                         *)
(*       (bit j of the packed mask byte <=> nibble_j < 15).                  *)
(*                                                                           *)
(* All statements are built programmatically from lane-base generators, so   *)
(* the 16-conjunct forms cannot drift from a hand-transcription error, and   *)
(* LO (bytes 0..15) / HI (bytes 16..31 = input bytes 8..15) share one        *)
(* generator.                                                                *)
(*                                                                           *)
(* Uses: VPSUBB_SIGN_BIT_LT_15 (accept-bit lemma) + the usimd/simd           *)
(* definitions.                                                              *)
(* ========================================================================= *)

(* eta2 broadcast constants:
     0x0f0f0f0f broadcast (nibble mask ymm3, accept ymm5):
       6811299366900952671974763824040465167839410862684739061144563765171360567055
     0x02020202 broadcast (centre const ymm4):
       908173248920127022929968509872062022378588115024631874819275168689514742274 *)

(* ETA2_NIBCHAIN: the eta2 nibble-extraction chain                           *)
(* vpand(vpor(vpmovzxbw q)(vpsllw $4 ...)) 0x0f0f0f0f.                       *)
let ETA2_NIBCHAIN =
 `word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
            (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
      (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)`;;

let wsw256 = `word_subword:int256->num#num->byte`;;
let wsw128 = `word_subword:int128->num#num->byte`;;

(* ------------------------------------------------------------------------- *)
(* F0NIB: the vpand-nibble bytes (0x0f mask).                                *)
let gen_f0nib obase qoffbase =
  let mk bi =
    let off = obase + 8*bi and qoff = qoffbase + 8*(bi/2) and hi = (bi mod 2 = 1) in
    let lhs = mk_comb(mk_comb(wsw256, ETA2_NIBCHAIN), mk_pair(mk_small_numeral off, `8`)) in
    let v = mk_comb(`val:byte->num`,
              mk_comb(mk_comb(wsw128,`q:int128`), mk_pair(mk_small_numeral qoff, `8`))) in
    let nib = if hi then mk_binop `DIV` v `16` else mk_binop `MOD` v `16` in
    mk_eq(lhs, mk_comb(`word:num->byte`, nib)) in
  mk_forall(`q:int128`, end_itlist (curry mk_conj) (map mk (0--15)));;

let f0nib_tac =
  GEN_TAC THEN
  REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST;;

let F0NIB_BYTES_ETA2    = prove(gen_f0nib 0 0,   f0nib_tac);;
let F0NIB_BYTES_HI_ETA2 = prove(gen_f0nib 128 64, f0nib_tac);;

(* ------------------------------------------------------------------------- *)
(* SIGN_NIB (accept-bit at nibble granularity): for n<16, bit 7 of           *)
(* word_sub (word n) (word 15) <=> n < 15.  eta4 used (word 9)/(n<9).        *)
let SIGN_NIB_ETA2 = prove
 (`!n. n < 16 ==> (bit 7 (word_sub (word n:byte) (word 15)) <=> n < 15)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word n:byte) = n` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_8] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `word n:byte` VPSUBB_SIGN_BIT_LT_15) THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* eta2 CORRECT: PREFIX_G opening-dependency scalar lemmas.                  *)
(*                                                                           *)
(* The small word-level / loop-guard helper lemmas that eta2's PREFIX_G tactic *)
(* (the CLEAN_BODY prefix stepping) needs before it can step the body.  They *)
(* are constant-independent (they concern the 32-bit register / loop-guard   *)
(* arithmetic, not the eta constant): VAL_WORD_ZX_64_32, JA_NOT_TAKEN_LE, and *)
(* the buffer-chunk lemma SUB_LIST_16_BYTES_FROM_INT128 (parametric in the   *)
(* buffer length).                                                           *)
(*                                                                           *)
(* Head-guard facts these support:                                           *)
(*   loop top pc+86; steps 1--2 (cmp eax,0xf8=248 + ja) -> RIP pc+97;        *)
(*   steps 3--4 (cmp ecx,0x78=120 + ja) -> RIP pc+106 (= 0x6e, SIMD start);  *)
(*   scalar target (ja taken) = pc+399 (0x18f).  eta2's ecx guard is 120 (buf *)
(*   136), so the second JA_NOT_TAKEN_LE is instantiated at 120.             *)
(* ========================================================================= *)

(* word_zx of a 64-bit register holding a value < 2^32, read back at 32 bits, *)
(* recovers the value (constant-independent).                                *)
let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

let mk_eta2_prefix_open (memsafe:bool) : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `16 * i <= 120` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i + 1) <= 136` THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  (if memsafe then STRIP_EXISTS_ASSUM_TAC else ALL_TAC) THEN
  MP_TAC(SPECL [`buf:int64`;`136`;`inlist:byte list`;`i:num`;`s0:x86state`] SUB_LIST_16_BYTES_FROM_INT128) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `16 * (i + 1) <= 136` THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `chunk0 = read(memory:>bytes128(word_add buf (word(16*i)))) s0` THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) <= 248` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN
    TRANS_TAC LE_TRANS `LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(0, 16 * (i+1)) inlist):int16 list)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NIBLEN_PREFIX_MONO THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `outlen0 = LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list)` THEN
  FIRST_ASSUM(fun th -> if concl th =
      `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) = outlen0`
    then (RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) else NO_TAC) THEN
  MP_TAC(SPECL [`outlen0:num`;`248`] JA_NOT_TAKEN_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`16*i`;`120`] JA_NOT_TAKEN_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  VAL_INT64_TAC `outlen0:num` THEN
  X86_STEPS_TAC EXEC (1--2) THEN
  SUBGOAL_THEN `read RIP s2 = word(pc + 97):int64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can(find_term((=)`&248:int`))(concl th)
                           then ASSUME_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if can(find_term((=)`pc + 399`))(concl th) then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC; ALL_TAC] THEN
  X86_STEPS_TAC EXEC (3--4) THEN
  SUBGOAL_THEN `read RIP s4 = word(pc + 106):int64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can(find_term((=)`&120:int`))(concl th)
                           then ASSUME_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if can(find_term((=)`pc + 399`))(concl th) then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC; ALL_TAC];;

let ETA2_PREFIX_OPEN_TAC : tactic = mk_eta2_prefix_open false;;

(* ========================================================================= *)
(* eta2 CORRECT: the constant-independent helper substrate.                  *)
(*                                                                           *)
(* The pure word / arithmetic / popcount / pshufb-gather lemmas and the two  *)
(* stepping utility tactics that the CLEAN_BODY chain (PREFIX_G + SI1-4 folds *)
(* + RAX/RCX finals) depends on.  None of them mention the eta constant, the *)
(* accept threshold, the buffer length, or the ZMM register choice — they are *)
(* about the SIMD structure (vpmovsxbd sign-extend, vpshufb table gather,    *)
(* vpmovmskb bit-packing, the R8 ushr-by-8 mask peel, the 32-bit register    *)
(* nesting).                                                                 *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* Accept-count = filter-length lemmas: the 8-bit bitval sum (resp. ACC_IDX  *)
(* length) equals LENGTH(FILTER (val<15) [bytes]).                           *)
let BITVAL_SUM_8_EQ_LENGTH_FILTER_ETA2 = prove
 (`!a0 a1 a2 a3 a4 a5 a6 a7:byte.
     bitval(val a0 < 15) + bitval(val a1 < 15) + bitval(val a2 < 15) + bitval(val a3 < 15) +
     bitval(val a4 < 15) + bitval(val a5 < 15) + bitval(val a6 < 15) + bitval(val a7 < 15) =
     LENGTH(FILTER (\x:byte. val x < 15) [a0;a1;a2;a3;a4;a5;a6;a7])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FILTER; LENGTH] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; BITVAL_CLAUSES]) THEN ARITH_TAC);;

let ACC_LENGTH_EQ_FILTER_ETA2 = prove
 (`!(m:byte) (n0:byte) (n1:byte) (n2:byte) (n3:byte) (n4:byte) (n5:byte) (n6:byte) (n7:byte).
     (bit 0 m <=> val n0 < 15) /\ (bit 1 m <=> val n1 < 15) /\ (bit 2 m <=> val n2 < 15) /\
     (bit 3 m <=> val n3 < 15) /\ (bit 4 m <=> val n4 < 15) /\ (bit 5 m <=> val n5 < 15) /\
     (bit 6 m <=> val n6 < 15) /\ (bit 7 m <=> val n7 < 15)
     ==> LENGTH(ACC_IDX m) = LENGTH(FILTER (\x:byte. val x < 15) [n0;n1;n2;n3;n4;n5;n6;n7])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_ACC_IDX_BITSUM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BITVAL_SUM_8_EQ_LENGTH_FILTER_ETA2]);;

(* LEN_RECONCILE: accept count = LENGTH(REJ_SAMPLE block) (accept < 15).     *)
let LEN_RECONCILE = prove
 (`!(m:byte) (chunk0:int128).
     (!j. j < 8 ==> (bit j m <=>
        EL j [val(word_subword chunk0 (0,8):byte) MOD 16; val(word_subword chunk0 (0,8):byte) DIV 16;
              val(word_subword chunk0 (8,8):byte) MOD 16; val(word_subword chunk0 (8,8):byte) DIV 16;
              val(word_subword chunk0 (16,8):byte) MOD 16; val(word_subword chunk0 (16,8):byte) DIV 16;
              val(word_subword chunk0 (24,8):byte) MOD 16; val(word_subword chunk0 (24,8):byte) DIV 16] < 15))
     ==> LENGTH(ACC_IDX m) =
         LENGTH(REJ_SAMPLE_ETA2_BYTES [word_subword chunk0 (0,8); word_subword chunk0 (8,8);
                                       word_subword chunk0 (16,8); word_subword chunk0 (24,8)]:int32 list)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:byte`;
    `word(val(word_subword (chunk0:int128) (0,8):byte) MOD 16):byte`;
    `word(val(word_subword (chunk0:int128) (0,8):byte) DIV 16):byte`;
    `word(val(word_subword (chunk0:int128) (8,8):byte) MOD 16):byte`;
    `word(val(word_subword (chunk0:int128) (8,8):byte) DIV 16):byte`;
    `word(val(word_subword (chunk0:int128) (16,8):byte) MOD 16):byte`;
    `word(val(word_subword (chunk0:int128) (16,8):byte) DIV 16):byte`;
    `word(val(word_subword (chunk0:int128) (24,8):byte) MOD 16):byte`;
    `word(val(word_subword (chunk0:int128) (24,8):byte) DIV 16):byte`] ACC_LENGTH_EQ_FILTER_ETA2) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    W(fun (asl,gw) -> let n = rand(rator(lhand gw)) in
       MP_TAC(SPEC n (find (fun th -> is_forall(concl th) && can(find_term(fun u->match u with Const("EL",_)->true|_->false))(concl th)) (map snd asl)))) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN
    W(fun (asl,gw) -> let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" && type_of u=`:byte` with _->false) gw in
       MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN STRIP_TAC THEN
       SUBGOAL_THEN (mk_eq(mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,mk_binop `MOD` (mk_comb(`val:byte->num`,bt)) `16`)), mk_binop `MOD` (mk_comb(`val:byte->num`,bt)) `16`)) SUBST1_TAC THENL
        [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
       SUBGOAL_THEN (mk_eq(mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,mk_binop `DIV` (mk_comb(`val:byte->num`,bt)) `16`)), mk_binop `DIV` (mk_comb(`val:byte->num`,bt)) `16`)) SUBST1_TAC THENL
        [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
       REFL_TAC);
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LENGTH_FILTER_BYTE_NIBBLES_4_BYTES; LENGTH_REJ_SAMPLE_ETA2_BYTES]]);;

(* SUBITER_FOLD_STEP: fold one sub-iter's REJ block onto the running prefix. *)
let SUBITER_FOLD_STEP = prove
 (`!res s (m:byte) (blk:byte list) (prefixbytes:byte list).
     LENGTH(ACC_IDX m) = LENGTH(REJ_SAMPLE_ETA2_BYTES blk:int32 list) /\
     read(memory:>bytes(res, 4*LENGTH(REJ_SAMPLE_ETA2_BYTES prefixbytes:int32 list))) s =
       num_of_wordlist(REJ_SAMPLE_ETA2_BYTES prefixbytes) /\
     read(memory:>bytes(word_add res (word(4*LENGTH(REJ_SAMPLE_ETA2_BYTES prefixbytes:int32 list))),
                        4*LENGTH(ACC_IDX m))) s =
       num_of_wordlist(REJ_SAMPLE_ETA2_BYTES blk)
     ==> read(memory:>bytes(res, 4*LENGTH(REJ_SAMPLE_ETA2_BYTES(APPEND prefixbytes blk):int32 list))) s =
         num_of_wordlist(REJ_SAMPLE_ETA2_BYTES(APPEND prefixbytes blk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`res:int64`; `s:x86state`;
                 `REJ_SAMPLE_ETA2_BYTES prefixbytes:int32 list`;
                 `REJ_SAMPLE_ETA2_BYTES blk:int32 list`] SUBITER_STORE_EXTEND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> if can(find_term(fun u->u=`ACC_IDX (m:byte)`)) (concl th)
                            then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[REJ_SAMPLE_ETA2_BYTES_APPEND; LENGTH_APPEND;
                ARITH_RULE `4*a+4*b = 4*(a+b)`]]);;

(* ------------------------------------------------------------------------- *)
(* Cumulative outlen bounds through sub-iters 1-4.  Buffer length stays      *)
(* symbolic (LENGTH inlist).                                                 *)
let SUBITER_OUTLEN_BOUND_1 = prove
 (`!(inlist:byte list) i.
     16*(i+1) <= LENGTH inlist /\
     LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(0, 16*(i+1)) inlist):int16 list) <= 248
     ==> LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) +
         LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16*i, 4) inlist):int16 list) <= 248`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN
  MP_TAC(SPECL [`inlist:byte list`; `i:num`] REJ_NIBBLES_ETA2_STEP_16) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; LENGTH_APPEND])) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `4 + 12 = 16`]
                     (ISPECL [`inlist:byte list`; `4`; `12`; `16*i`] SUB_LIST_SPLIT)) THEN
  DISCH_THEN(fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th; REJ_NIBBLES_ETA2_APPEND; LENGTH_APPEND])) THEN
  ASM_ARITH_TAC);;

let SUBITER_OUTLEN_BOUND_2 = prove
 (`!(inlist:byte list) i.
     16*(i+1) <= LENGTH inlist /\
     LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(0, 16*(i+1)) inlist):int16 list) <= 248
     ==> LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) +
         LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16*i, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16*i + 4, 4) inlist):int16 list)
         <= 248`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN
  MP_TAC(SPECL [`inlist:byte list`; `i:num`] REJ_NIBBLES_ETA2_STEP_16) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; LENGTH_APPEND])) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `8 + 8 = 16`]
                     (ISPECL [`inlist:byte list`; `8`; `8`; `16*i`] SUB_LIST_SPLIT)) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `4 + 4 = 8`]
                     (ISPECL [`inlist:byte list`; `4`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 ->
    RULE_ASSUM_TAC(REWRITE_RULE[th2; REJ_NIBBLES_ETA2_APPEND; LENGTH_APPEND;
                                th1]))) THEN
  ASM_ARITH_TAC);;

let SUBITER_OUTLEN_BOUND_3 = prove
 (`!(inlist:byte list) i.
     16*(i+1) <= LENGTH inlist /\
     LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(0, 16*(i+1)) inlist):int16 list) <= 248
     ==> LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) +
         LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16*i, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16*i + 4, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16*i + 8, 4) inlist):int16 list)
         <= 248`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN
  MP_TAC(SPECL [`inlist:byte list`; `i:num`] REJ_NIBBLES_ETA2_STEP_16) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; LENGTH_APPEND])) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `12 + 4 = 16`]
                     (ISPECL [`inlist:byte list`; `12`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `8 + 4 = 12`]
                     (ISPECL [`inlist:byte list`; `8`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `4 + 4 = 8`]
                     (ISPECL [`inlist:byte list`; `4`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 -> DISCH_THEN(fun th3 ->
    RULE_ASSUM_TAC(REWRITE_RULE[th3; th2; th1; REJ_NIBBLES_ETA2_APPEND;
                                LENGTH_APPEND])))) THEN
  ASM_ARITH_TAC);;

let SUBITER_OUTLEN_BOUND_4 = prove
 (`!(inlist:byte list) i.
     16*(i+1) <= LENGTH inlist /\
     LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(0, 16*(i+1)) inlist):int16 list) <= 248
     ==> LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) +
         LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16*i, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16*i + 4, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16*i + 8, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16*i + 12, 4) inlist):int16 list)
         <= 248`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN
  MP_TAC(SPECL [`inlist:byte list`; `i:num`] REJ_NIBBLES_ETA2_STEP_16) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; LENGTH_APPEND])) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `12 + 4 = 16`]
                     (ISPECL [`inlist:byte list`; `12`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `8 + 4 = 12`]
                     (ISPECL [`inlist:byte list`; `8`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `4 + 4 = 8`]
                     (ISPECL [`inlist:byte list`; `4`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 -> DISCH_THEN(fun th3 ->
    RULE_ASSUM_TAC(REWRITE_RULE[th3; th2; th1; REJ_NIBBLES_ETA2_APPEND;
                                LENGTH_APPEND])))) THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* maskbit_tgt: the mask8-byte <-> chunk0-nibble<15 EL-list correspondence   *)
(* that LEN_RECONCILE consumes.                                              *)
let maskbit_tgt =
  `!j. j < 8 ==> (bit j (word (val (mask8:int64) MOD 256):byte) <=>
       EL j [val(word_subword (chunk0:int128) (0,8):byte) MOD 16;
         val(word_subword chunk0 (0,8):byte) DIV 16; val(word_subword chunk0 (8,8):byte) MOD 16;
         val(word_subword chunk0 (8,8):byte) DIV 16; val(word_subword chunk0 (16,8):byte) MOD 16;
         val(word_subword chunk0 (16,8):byte) DIV 16; val(word_subword chunk0 (24,8):byte) MOD 16;
         val(word_subword chunk0 (24,8):byte) DIV 16] < 15)`;;

let maskbit_tgt_2 =
  `!j. j < 8 ==> (bit j (word (val (mask8b:int64) MOD 256):byte) <=>
       EL j [val(word_subword (chunk0:int128) (32,8):byte) MOD 16;
         val(word_subword chunk0 (32,8):byte) DIV 16; val(word_subword chunk0 (40,8):byte) MOD 16;
         val(word_subword chunk0 (40,8):byte) DIV 16; val(word_subword chunk0 (48,8):byte) MOD 16;
         val(word_subword chunk0 (48,8):byte) DIV 16; val(word_subword chunk0 (56,8):byte) MOD 16;
         val(word_subword chunk0 (56,8):byte) DIV 16] < 15)`;;

let maskbit_tgt_3 =
  `!j. j < 8 ==> (bit j (word (val (mask8c:int64) MOD 256):byte) <=>
       EL j [val(word_subword (chunk0:int128) (64,8):byte) MOD 16;
         val(word_subword chunk0 (64,8):byte) DIV 16; val(word_subword chunk0 (72,8):byte) MOD 16;
         val(word_subword chunk0 (72,8):byte) DIV 16; val(word_subword chunk0 (80,8):byte) MOD 16;
         val(word_subword chunk0 (80,8):byte) DIV 16; val(word_subword chunk0 (88,8):byte) MOD 16;
         val(word_subword chunk0 (88,8):byte) DIV 16] < 15)`;;

let maskbit_tgt_4 =
  `!j. j < 8 ==> (bit j (word (val (mask8d:int64) MOD 256):byte) <=>
       EL j [val(word_subword (chunk0:int128) (96,8):byte) MOD 16;
         val(word_subword chunk0 (96,8):byte) DIV 16; val(word_subword chunk0 (104,8):byte) MOD 16;
         val(word_subword chunk0 (104,8):byte) DIV 16; val(word_subword chunk0 (112,8):byte) MOD 16;
         val(word_subword chunk0 (112,8):byte) DIV 16; val(word_subword chunk0 (120,8):byte) MOD 16;
         val(word_subword chunk0 (120,8):byte) DIV 16] < 15)`;;

(* DIVMOD256_SPLIT: for the sub-iters 2-4 maskbit derivation.                *)
let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* Opening + the nibble chain s5-s8. Leaves `read YMM0 s8 =                  *)
(* F0NIB_CHUNK0` ASSUMEd, chunk0/outlen0 abbreviated, both head guards done, *)
(* s4/s5/s6/s7 word_join equalities purged.  Ready for the s9 accept-vpsubb. *)
let mk_eta2_prefix_to_s8 (memsafe:bool) : tactic =
  mk_eta2_prefix_open memsafe THEN
  X86_VSTEPS_TAC EXEC (5--5) THEN
  SUBGOAL_THEN `val(word(16*i):int64) = 16*i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `16*i <= 120` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word(16*i):int64) = 16*i`; ARITH_RULE `1 * x = x`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read (memory :> bytes128 (word_add buf (word (16 * i)))) s4 = chunk0`]) THEN
  SUBGOAL_THEN `read YMM0 s5 = usimd16 (\b:byte. word_zx b:int16) chunk0:int256` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can(find_term((=)`read YMM0 s5`))(lhand(concl th)) then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DROP_WORDJOIN_TAC THEN PURGE_STALE_STATES_TAC ["s4"] THEN
  X86_VSTEPS_TAC EXEC (6--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s5 = usimd16 (\b:byte. word_zx b:int16) chunk0:int256`]) THEN
  X86_VSTEPS_TAC EXEC (7--7) THEN X86_VSTEPS_TAC EXEC (8--8) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM3 s5 =
    word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256`]) THEN
  SUBGOAL_THEN (mk_eq(`read YMM0 s8:int256`, F0NIB_CHUNK0)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can(find_term((=)`read YMM0 s8`))(lhand(concl th)) then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DROP_WORDJOIN_TAC THEN PURGE_STALE_STATES_TAC ["s5";"s6";"s7"];;

let ETA2_PREFIX_TO_S8_TAC : tactic = mk_eta2_prefix_to_s8 false;;

(* ========================================================================= *)
(* eta2 CORRECT: PREFIX_G extension through s9 (accept-vpsubb) +             *)
(* the four vpmovmskb maskbit foralls.                                       *)
(*                                                                           *)
(* ETA2_PREFIX_TO_S9_TAC extends ETA2_PREFIX_TO_S8_TAC with the accept-vpsubb *)
(* step and the four "maskbit" foralls that the popcount stage (post-        *)
(* vpmovmskb) will consume.  eta2 does the ACCEPT vpsubb (ymm5) at s9 and    *)
(* centres LATER (s11).                                                      *)
(*                                                                           *)
(*   s9  vpsubb ymm5,ymm0,ymm1  (ymm5 = 0x0f0f0f0f broadcast)                *)
(*       -> read YMM1 s9 = word_join tree of                                 *)
(*            word_sub (word_subword <F0NIB explicit> (8j,8)) (word 15), j<32 *)
(*          = the ACCEPT form f1bnd (nibble - 15; bit 7 <=> nibble < 15).    *)
(*       RIP s9 = pc+129.                                                    *)
(*                                                                           *)
(* Because ETA2_PREFIX_TO_S8_TAC leaves YMM0 s8 as the EXPLICIT F0NIB_CHUNK0, *)
(* the accept tree carries the explicit nibble chain, so each maskbit lane   *)
(* reduces via F0NIB_BYTES_ETA2 / _HI + SIGN_NIB_ETA2 (accept threshold 15)  *)
(* directly.                                                                 *)
(*                                                                           *)
(* The four foralls (lane groups 0/8/16/24 of the 32-byte f1bnd) match the   *)
(* maskbit_tgt targets at chunk0 nibble bases 0/32/64/96.  They are ASSUMEd  *)
(* BEFORE the vpmovmskb (s10) so the popcount at s21 is over the OPAQUE f1bnd. *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* Build the maskbit forall term for f1bnd lane group g (g in {0,8,16,24}),  *)
(* over chunk0 nibble base b = 4*g. Shape matches 's maskbit_tgt list.       *)
let eta2_mk_maskbit_forall g =
  let b = 4*g in
  let nib off hi =
    let v = subst [mk_small_numeral off, `OFF:num`] `val(word_subword (chunk0:int128) (OFF,8):byte)` in
    if hi then mk_binop `DIV` v `16` else mk_binop `MOD` v `16` in
  let ellist = end_itlist (fun a b -> mk_binop `CONS:num->(num)list->(num)list` a b)
     ([nib b false; nib b true; nib (b+8) false; nib (b+8) true;
       nib (b+16) false; nib (b+16) true; nib (b+24) false; nib (b+24) true] @ [`[]:num list`]) in
  (* build the LHS via subst into a fully-typed template (avoids mk_comb on the *)
  (* polymorphic `bit 7`, whose word type won't unify against :byte).        *)
  let bitapp = subst [mk_small_numeral g, `G:num`]
                 `bit 7 (word_subword (f1bnd:int256) (8*(k+G),8):byte)` in
  mk_forall(`k:num`,
    mk_imp(`k < 8`,
      mk_eq(bitapp,
            mk_binop `(<):num->num->bool` (mk_comb(mk_comb(`EL:num->(num)list->num`,`k:num`), ellist)) `15`)));;

(* Prove & ASSUME the maskbit forall for lane group g, given the f1bnd def   *)
(* (`f1bnd = <accept tree>`) is in context.  Constant-independent mechanism. *)
let ETA2_MASKBIT_ASSUME_TAC (g:int) : tactic =
  W(fun (asl,w) ->
    let f1d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f1bnd:int256`) (map snd asl) in
    let tgt = eta2_mk_maskbit_forall g in
    let mb_imp = prove(mk_imp(concl f1d, tgt),
      DISCH_THEN(fun f1eq -> REPEAT STRIP_TAC THEN
        FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
          (ARITH_RULE `k<8 ==> k=0\/k=1\/k=2\/k=3\/k=4\/k=5\/k=6\/k=7`)) THEN
        CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
        REWRITE_TAC[f1eq] THEN
        REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                 DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
          CONV_TAC NUM_REDUCE_CONV)) THEN
        REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN
        REWRITE_TAC[SPEC `chunk0:int128` F0NIB_BYTES_ETA2;
                    SPEC `chunk0:int128` F0NIB_BYTES_HI_ETA2] THEN
        W(fun (a2,w2) ->
           let nibarg = find_term (fun u -> match u with
              Comb(Comb(Const("MOD",_),_),_) | Comb(Comb(Const("DIV",_),_),_) -> true | _ -> false) w2 in
           let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" &&
             type_of u = `:byte` && can(find_term(fun v->v=`chunk0:int128`)) u with _->false) w2 in
           let nlt16 = prove(mk_binop `(<):num->num->bool` nibarg `16`,
              MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
           ACCEPT_TAC (MP (SPEC nibarg SIGN_NIB_ETA2) nlt16)))) in
    ASSUME_TAC (MP mb_imp f1d));;

(* Full opening through s9 + the four maskbit foralls, f1bnd abbreviated.    *)
let mk_eta2_prefix_to_s9 (memsafe:bool) : tactic =
  mk_eta2_prefix_to_s8 memsafe THEN
  X86_VSTEPS_TAC EXEC (9--9) THEN
  ABBREV_TAC `f1bnd:int256 = read YMM1 s9` THEN
  ETA2_MASKBIT_ASSUME_TAC 0 THEN
  ETA2_MASKBIT_ASSUME_TAC 8 THEN
  ETA2_MASKBIT_ASSUME_TAC 16 THEN
  ETA2_MASKBIT_ASSUME_TAC 24;;

let ETA2_PREFIX_TO_S9_TAC : tactic = mk_eta2_prefix_to_s9 false;;

(* ========================================================================= *)
(* eta2 CORRECT: PREFIX_G through s10 (vpmovmskb) + s11 (centre              *)
(* vpsubb) + the four gather foralls.                                        *)
(*                                                                           *)
(* ETA2_PREFIX_TO_S11_TAC extends the s9-accept + 4-maskbit-foralls state    *)
(* through the eta2 ORDER: vpmovmskb FIRST (s10), then the centre vpsubb     *)
(* (s11):                                                                    *)
(*   eta2: s9 accept, s10 MSKB (R8, over opaque f1bnd), s11 CENTRE (f0sub).  *)
(*                                                                           *)
(* Control flow:                                                             *)
(*   read RIP s10 = pc+133 ; read RIP s11 = pc+137 ; read YMM4 s10 = 0x02020202 *)
(*   read R8 s10  = word_zx(word(SUM32 over bit 7 of word_subword f1bnd (8k,8))) *)
(*                  — the packed 32-bit popcount MASK over the OPAQUE f1bnd  *)
(*                    (requires the f1bnd def DROPPED before s10).           *)
(*   read YMM0 s11 = word_join tree of                                       *)
(*                     word_sub (word 2) (word_subword <explicit F0NIB> (8j,8)) *)
(*                  = the CENTRE form f0sub (2 - nibble).                    *)
(*                                                                           *)
(* The DROP of the f1bnd word_join def before s10 keeps R8/popcount over the *)
(* opaque `f1bnd` var (via the read YMM1 s9 = f1bnd fold that ABBREV_TAC left). *)
(* f0sub is then abbreviated at s11 and the four gather foralls (lane groups *)
(* over the low/high 128 halves, +/- the >>64 shift) are ASSUMEd in the      *)
(* SUBITER_STORE_SPEC gather-hypothesis shape (centre value word 2), so SI1..SI4 *)
(* fold by MATCH_ACCEPT.  Because YMM0 s8 is kept explicit, each lane reduces *)
(* via F0NIB_BYTES_ETA2/_HI directly.                                        *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* Prove+ASSUME the gather forall for one lane block, given f0sub def, the   *)
(* extraction term `gsub` (word_subword f0sub (..,128) possibly ushr'd) and the *)
(* 8-nibble EL list `ellist`.  `shifted` toggles the SUBWORD_USHR rewrite.   *)
let eta2_gather_block (gsub:term) (ellist:term) (shifted:bool) : tactic =
  W(fun (asl,w) ->
    let f0d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f0sub:int256`) (map snd asl) in
    let jbody =
      mk_eq(mk_comb(mk_comb(`word_subword:int128->num#num->byte`, gsub), `(8*j,8)`),
            mk_comb(mk_comb(`word_sub:byte->byte->byte`,`word 2:byte`),
                    mk_comb(`word:num->byte`, mk_comb(mk_comb(`EL:num->(num)list->num`,`j:num`), ellist)))) in
    let tgt = mk_forall(`j:num`, mk_imp(`j < 8`, jbody)) in
    let core_tac f0eq =
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
        (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      (if shifted then REWRITE_TAC[WORD_ZX_TRIVIAL] THEN REWRITE_TAC[SUBWORD_USHR] THEN CONV_TAC NUM_REDUCE_CONV
       else REWRITE_TAC[WORD_ZX_TRIVIAL]) THEN
      SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
      REWRITE_TAC[f0eq] THEN
      REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
               DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
        CONV_TAC NUM_REDUCE_CONV)) THEN
      REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN
      REWRITE_TAC[SPEC `chunk0:int128` F0NIB_BYTES_ETA2;
                  SPEC `chunk0:int128` F0NIB_BYTES_HI_ETA2] THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC in
    let gather_imp = prove(mk_imp(concl f0d, tgt), DISCH_THEN core_tac) in
    ASSUME_TAC (MP gather_imp f0d));;

(* The four nibble EL lists (chunk0 byte bases 0/32/64/96).                  *)
let eta2_ellist nbase =
  let nib off hi =
    let v = subst [mk_small_numeral off, `OFF:num`] `val(word_subword (chunk0:int128) (OFF,8):byte)` in
    if hi then mk_binop `DIV` v `16` else mk_binop `MOD` v `16` in
  end_itlist (fun a b -> mk_binop `CONS:num->(num)list->(num)list` a b)
    ([nib nbase false; nib nbase true; nib (nbase+8) false; nib (nbase+8) true;
      nib (nbase+16) false; nib (nbase+16) true; nib (nbase+24) false; nib (nbase+24) true]
     @ [`[]:num list`]);;

(* The four gather sources off f0sub.                                        *)
let g1_eta2 = `word_subword (f0sub:int256) (0,128):int128`;;
let g2_eta2 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128) 64):int128):int128`;;
let g3_eta2 = `word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128`;;
let g4_eta2 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128) 64):int128):int128`;;

let mk_eta2_prefix_to_s11 (memsafe:bool) : tactic =
  mk_eta2_prefix_to_s9 memsafe THEN
  (* DROP the f1bnd word_join def so the vpmovmskb reads the opaque f1bnd.   *)
  REPEAT(FIRST_X_ASSUM(fun th ->
     if is_eq(concl th) && lhand(concl th) = `f1bnd:int256`
     then ALL_TAC else failwith "keep")) THEN
  X86_VSTEPS_TAC EXEC (10--10) THEN
  X86_VSTEPS_TAC EXEC (11--11) THEN
  ABBREV_TAC `f0sub:int256 = read YMM0 s11` THEN
  (* four gather foralls (bg1 direct low-128; bg2 low-128>>64; bg3 high-128; bg4 high-128>>64) *)
  eta2_gather_block g1_eta2 (eta2_ellist 0)  false THEN
  eta2_gather_block g2_eta2 (eta2_ellist 32) true THEN
  eta2_gather_block g3_eta2 (eta2_ellist 64) false THEN
  eta2_gather_block g4_eta2 (eta2_ellist 96) true;;

let ETA2_PREFIX_TO_S11_TAC : tactic = mk_eta2_prefix_to_s11 false;;

(* ========================================================================= *)
(* eta2 CORRECT: the red_lane store-fold bridges.                            *)
(*                                                                           *)
(* eta2 stores the mod-5 reduced value `red_lane(word_sx(...))` (asm         *)
(* 0xa7-0xb0 vpmulhrsw/vpmullw/vpaddd), so the SI1 fold composes red_lane    *)
(* over the word_sx store substrate (STORE_LANE_EQ_REJBLOCK, defined above)  *)
(* and then applies SUBITER_STORE_SPEC.  The _RL bridges here are the        *)
(* red_lane-wrapped analogues that feed that fold.                           *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* The per-int32-lane reduction bridge: red_lane v = the exact stepper expr.
   The multiply constant `word 4294960736:int32` is `word_sx(word 0xe660:int16)`;
   red_lane holds it as `word 0xe660` sign-extended, so one WORD_REDUCE closes it. *)
let RED_LANE_STEPFORM = prove
 (`!v:int32. red_lane v =
     word_add v
       (word_join
          (word_mul (word_subword (word_add (word_ushr (word_mul (word_sx (word_subword v (16,16):int16)) (word 4294960736:int32)) 14) (word 1)) (1,16):int16) (word 5:int16))
          (word_mul (word_subword (word_add (word_ushr (word_mul (word_sx (word_subword v (0,16):int16)) (word 4294960736:int32)) 14) (word 1)) (1,16):int16) (word 5:int16))
        :int32)`,
  GEN_TAC THEN REWRITE_TAC[red_lane; mulhrs_eta2] THEN
  REWRITE_TAC[WORD_REDUCE_CONV `word_sx (word 58976:int16):int32`]);;

(* Collapse word_subword(word_subword x (p1,l1))(p2,l2) with concrete numerals:
   the usimd8 expansion of `usimd8 red_lane sx1` produces
   word_subword(word_subword sx1 (32k,32))(16,16), which the flat stepper tree
   has as word_subword sx1 (32k+16,16). *)
let SUBWORD_SUBWORD_CONV : conv =
  fun tm ->
    let inst = PART_MATCH (lhs o snd o dest_imp) WORD_SUBWORD_SUBWORD tm in
    let ant = REWRITE_RULE[DIMINDEX_4;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;
                           DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] inst in
    let solved = MP ant (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl ant)))) in
    CONV_RULE(RAND_CONV(RAND_CONV(NUM_REDUCE_CONV))) solved;;

(* ========================================================================= *)
(* eta2 CORRECT: the red_lane-composed store postcond.                       *)
(*                                                                           *)
(* The eta2 store value is `usimd8 red_lane (<word_sx gather pipeline>)` (the *)
(* s17-19 mod-5 reduction wraps red_lane over the vpmovsxbd output).  These  *)
(* three lemmas lift the word_sx-level store bridges through that extra      *)
(* `usimd8 red_lane`, giving a SUBITER_STORE_POSTCOND_RL whose RHS carries the *)
(* `MAP red_lane` that SUBITER_STORE_SPEC then rewrites to                   *)
(* REJ_SAMPLE_ETA2_BYTES.                                                    *)
(*                                                                           *)
(*   USIMD8_LANE : generic int32-lane extract for an OPAQUE per-lane fn f:   *)
(*     j<8 ==> word_subword (usimd8 f Y) (32j,32) = f (word_subword Y (32j,32)). *)
(*     (The red_lane wrap needs the opaque-f version.  Proved by usimd8      *)
(*     expansion + the WORD_SUBWORD_JOIN lane pick + SUBWORD_SUBWORD_CONV    *)
(*     collapse + the trivial word_subword x (0,32)=x for int32.)            *)
(*                                                                           *)
(*   STORE_LANE_EQ_REJBLOCK_RL : lane j of the red_lane-wrapped store =      *)
(*     EL j (MAP red_lane (MAP word_sx (SUB_LIST(0,k)(PSHUFB_OUT_LIST g m)))). *)
(*                                                                           *)
(*   SUBITER_STORE_POSTCOND_RL : the capstone.  Given the bytes256 dest holds *)
(*     usimd8 red_lane (<word_sx pipeline>) and k<=8, the 4k stored bytes =  *)
(*     num_of_wordlist(MAP red_lane (MAP word_sx (SUB_LIST(0,k)(PSHUFB_OUT_LIST *)
(*     g m)))).  Proved by the same STORE_BYTES256_NUM_OF_WORDLIST MP, lane-match *)
(*     via STORE_LANE_EQ_REJBLOCK_RL.                                        *)
(*                                                                           *)
(* SI1 fold plan: after the reduction refold rewrites the s20 store as       *)
(* usimd8 red_lane (pf_target gather), MP SUBITER_STORE_POSTCOND_RL at       *)
(* k = LENGTH(ACC_IDX mask8) to get the store =                              *)
(* num_of_wordlist(MAP red_lane (MAP word_sx ...)); then MP SUBITER_STORE_SPEC *)
(* (its LHS is exactly that MAP red_lane form) to fold to                    *)
(* REJ_SAMPLE_ETA2_BYTES [b0..b3], and SUBITER_FOLD_STEP appends the block.  *)
(* ========================================================================= *)

(* Generic int32-lane extract for an opaque per-lane fn (red_lane, here).    *)
let USIMD8_LANE = prove
 (`!(f:int32->int32) (Y:int256) j. j < 8
     ==> word_subword (usimd8 f Y) (32*j,32):int32 = f (word_subword Y (32*j,32))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `j < 8 <=> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[usimd8;usimd4;usimd2;
     DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
           DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
    CONV_TAC NUM_REDUCE_CONV)) THEN
  CONV_TAC(DEPTH_CONV SUBWORD_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_BLAST `!x:int32. word_subword x (0,32):int32 = x`]);;

(* Lane j of the red_lane-wrapped store = the red_lane-mapped gather element. *)
let STORE_LANE_EQ_REJBLOCK_RL = prove
 (`!(g:int128) m k j. j < k /\ k <= 8
    ==> word_subword
          (usimd8 red_lane
            (usimd8 (\b:byte. word_sx b:int32)
              (word_zx (word_zx
                (word_zx
                  (usimd16 (\i. if bit 7 i then word 0:byte
                                else word_subword g (8 * val (word_subword i (0,4):4 word),8))
                    (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256)
                :int128):int64)))
          (32*j,32):int32
        = EL j (MAP red_lane (MAP (\b:byte. word_sx b:int32) (SUB_LIST(0,k) (PSHUFB_OUT_LIST g m))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `j < 8` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[USIMD8_LANE] THEN
  ASM_SIMP_TAC[STORE_LANE_EQ_REJBLOCK] THEN
  SUBGOAL_THEN `LENGTH(MAP (\b:byte. word_sx b:int32) (SUB_LIST(0,k)(PSHUFB_OUT_LIST (g:int128) m))) = k` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_MAP; LENGTH_SUB_LIST; LENGTH_PSHUFB_OUT_LIST] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[EL_MAP]]);;

(* Capstone: the eta2 red_lane store postcond.                               *)
let SUBITER_STORE_POSTCOND_RL = prove
 (`!A s (g:int128) m k.
     k <= 8 /\
     read (memory :> bytes256 A) s =
       usimd8 red_lane
         (usimd8 (\b:byte. word_sx b:int32)
            (word_zx (word_zx (word_zx (usimd16 (\i. if bit 7 i then word 0:byte
                else word_subword g (8 * val (word_subword i (0,4):4 word),8))
              (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256):int128):int64))
     ==> read (memory :> bytes(A, 4 * k)) s =
         num_of_wordlist (MAP red_lane (MAP (\b:byte. word_sx b:int32) (SUB_LIST(0,k) (PSHUFB_OUT_LIST g m))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A:int64`;
    `usimd8 red_lane
       (usimd8 (\b:byte. word_sx b:int32)
          (word_zx (word_zx (word_zx (usimd16 (\i. if bit 7 i then word 0:byte
              else word_subword (g:int128) (8 * val (word_subword i (0,4):4 word),8))
            (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256):int128):int64))`;
    `MAP red_lane (MAP (\b:byte. word_sx b:int32) (SUB_LIST(0,k) (PSHUFB_OUT_LIST (g:int128) m)))`;
    `k:num`; `s:x86state`] STORE_BYTES256_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_MAP; LENGTH_SUB_LIST; LENGTH_PSHUFB_OUT_LIST] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC STORE_LANE_EQ_REJBLOCK_RL THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

(* ========================================================================= *)
(* eta2 CORRECT: the SI1 table-load bridge (TAB1_TEQ) + pf_target.           *)
(*                                                                           *)
(* The table-correspondence bridge for sub-iter 1.  eta2 uses YMM9 for the   *)
(* table/vpshufb lane, and the state indices are: vmovq at s14, reading the  *)
(* movzbl-captured index from s13.  The gather source `g` inside pf_target is *)
(* g = word_zx(word_zx(word_subword f0sub (0,128))) (xmm8 =                  *)
(* word_zx(word_subword f0sub (0,128)); the vpshufb adds one more word_zx).  *)
(*                                                                           *)
(*   ETA2_TAB1_TEQ_TAC : from the table memory invariant (clean_body precond) + *)
(*     r<256, derive `tab1 = word_zx(word_zx(word(nwl(TABLE_ENTRY(word(val mask8 *)
(*     MOD 256))))))` at s14 via TABLE_VMOVQ_READ + R_EQ + RLT, then         *)
(*     ASSUME (after REABBREV tab1 = read YMM9 s14 leaves the raw vmovq read). *)
(*   pf_target : pshuf1 = the table-indexed gather form.                     *)
(*   ETA2_PF_PROOF : discharges `pshuf1 = pf_target`.                        *)
(*   ETA2_FOLD_F0SUB_INTO_PSHUF1_TAC : PERF-CRITICAL preamble — folds the expanded *)
(*     f0sub subtree in the pshuf1 def back to the `f0sub` var (the vpshufb inlined *)
(*     f0sub's VALUE, so PF_PROOF's SIMP would otherwise churn the 189938-char tree *)
(*     for >10 min).  ETA2_ESTABLISH_PF_TARGET_TAC = this + the pf_target SUBGOAL *)
(*     via ETA2_PF_PROOF (closes in seconds).                                *)
(*                                                                           *)
(* SI1 fold (next): keep the `read YMM0 s11 = f0sub` / `read YMM1 s9 = f1bnd` *)
(* folds through the stepping (do NOT purge before vpshufb, else pshuf1 re-  *)
(* expands), step s12-s20 with sx1 opaque, refold the reduction, SUBGOAL     *)
(* pf_target via ETA2_PF_PROOF, rewrite the store fact, MP                   *)
(* SUBITER_STORE_POSTCOND_RL then SUBITER_STORE_SPEC, SUBITER_FOLD_STEP.     *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* ETA2_TAB1_TEQ_TAC: derive+ASSUME the s14 table-load teq (YMM9, s13/s14).  *)
(* Generator for the four per-sub-iter table-load teq tactics: read the vmovq  *)
(* table load at state `rds`, MP TABLE_VMOVQ_READ with the mask<256 bound, then *)
(* rewrite the YMM9 read at state `ymms` by the zx-collapse lemma.  Varies only *)
(* in the two state indices, the mask var, and the RLT/R_EQ support lemmas.     *)
let ETA2_TAB_TEQ_GEN (rds:int) (ymms:int) (maskv:term) (rlt:thm) (req:thm) : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let rdst = mk_var("s"^string_of_int rds,`:x86state`)
    and ymmst = mk_var("s"^string_of_int ymms,`:x86state`) in
    let tblinv = find (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),v)),_) ->
         v=rdst && can(find_term(fun u->u=`mldsa_rej_uniform_table:byte list`)) (concl th) | _ -> false) asms in
    let mmod = mk_binop `MOD` (mk_comb(`val:int64->num`,maskv)) `256` in
    let tvr = MP (ISPECL[`table:int64`; mmod; rdst] TABLE_VMOVQ_READ) (CONJ tblinv rlt) in
    let ymm9 = find (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("YMM9",_)),v)),_)-> v=ymmst |_->false) asms in
    ASSUME_TAC (REWRITE_RULE[req; tvr] ymm9));;

let ETA2_TAB1_TEQ_TAC : tactic = ETA2_TAB_TEQ_GEN 13 14 `mask8:int64` RLT R_EQ;;

(* pf_target discharge (gather source g, table via mask8).                   *)
(* Generator for the four per-sub-iter pshufb gather-target discharge tactics: *)
(* find the `pshuf` word_join def + the `tab` TABLE_ENTRY eq by shape, then run *)
(* the fixed rewrite/conv pipeline.  ETA2_PF_PROOF{,_2,_3,_4} are instances.    *)
let mk_eta2_pf_proof (pshuf:term) (tab:term) : tactic =
  W(fun (asl,w) ->
    let pdef = find (fun th -> is_eq(concl th) && rand(concl th)=pshuf && can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
    let teq0 = find (fun th -> is_eq(concl th) &&
        (lhand(concl th)=tab || rand(concl th)=tab) &&
        can(find_term(fun u->match u with Const("TABLE_ENTRY",_)->true|_->false))(concl th) &&
        not(can(find_term(fun u->u=`f1bnd:int256`))(concl th))) (map snd asl) in
    let teq = if lhand(concl teq0)=tab then teq0 else SYM teq0 in
    SUBST1_TAC(SYM pdef) THEN REWRITE_TAC[teq] THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;DIMINDEX_4;ARITH] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ZX_TRIVIAL; VAL_WORD_ZX_GEN; DIMINDEX_64; DIMINDEX_32; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(TOP_DEPTH_CONV SUBWORD_ZX_LOW_CONV) THEN REWRITE_TAC[ZX_128_256_128]);;

let ETA2_PF_PROOF : tactic = mk_eta2_pf_proof `pshuf1:int256` `tab1:int256`;;

(* ETA2_FOLD_F0SUB_INTO_PSHUF1_TAC : PERF-CRITICAL preamble to ETA2_PF_PROOF. *)
(* The eta2 vpshufb (s15) inlines the EXPANDED f0sub value from xmm8 into the *)
(* pshuf1 def's gather source (189938 chars), NOT the `f0sub` var.  pf_target holds *)
(* the folded `f0sub`, so running ETA2_PF_PROOF directly forces its          *)
(* SIMP_TAC[WORD_SUBWORD_SUBWORD;..] to churn the whole tree .               *)
(* This tactic folds the expanded f0sub subtree back to the `f0sub` var in the *)
(* pshuf1 def first, after which ETA2_PF_PROOF closes in seconds.            *)
let ETA2_FOLD_F0SUB_INTO_PSHUF1_TAC : tactic =
  W(fun (asl,w) ->
    let f0d = find (fun th -> is_eq(concl th) &&
        (lhand(concl th)=`f0sub:int256` || rand(concl th)=`f0sub:int256`) &&
        can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
    let f0fold = if rand(concl f0d)=`f0sub:int256` then f0d else SYM f0d in
    RULE_ASSUM_TAC(fun th ->
      if is_eq(concl th) && rand(concl th)=`pshuf1:int256`
      then REWRITE_RULE[f0fold] th else th));;

(* Convenience: fold f0sub then discharge the pf_target subgoal.             *)
(* Generator for the four ETA2_ESTABLISH_PF_TARGET*_TAC: fold the f0sub        *)
(* word_join def into the `pshuf` assumption, then establish pf_target via the *)
(* matching PF_PROOF tactic.  Instances differ only in pshuf/pf_target/pfproof.*)
let mk_eta2_establish_pf_target (pshuf:term) (pft:term) (pfproof:tactic) : tactic =
  W(fun (asl,w) ->
    let f0d = find (fun th -> is_eq(concl th) &&
        (lhand(concl th)=`f0sub:int256` || rand(concl th)=`f0sub:int256`) &&
        can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
    let f0fold = if rand(concl f0d)=`f0sub:int256` then f0d else SYM f0d in
    RULE_ASSUM_TAC(fun th ->
      if is_eq(concl th) && rand(concl th)=pshuf
      then REWRITE_RULE[f0fold] th else th)) THEN
  SUBGOAL_THEN pft ASSUME_TAC THENL [pfproof; ALL_TAC];;

let ETA2_ESTABLISH_PF_TARGET_TAC : tactic =
  mk_eta2_establish_pf_target `pshuf1:int256` pf_target ETA2_PF_PROOF;;

(* ========================================================================= *)
(* eta2 CORRECT: the sub-iter-1 store fold.                                  *)
(*                                                                           *)
(* Runs after ETA2_PREFIX_TO_S11_TAC, which leaves f0sub abbreviated, the    *)
(* four gather foralls (centre word 2) assumed, mask8 at R8, and the four    *)
(* maskbit foralls (<15).  Step map:                                         *)
(*   s12 vextracti128 $0 -> XMM8 (gather source = word_zx(subword f0sub))    *)
(*   s13 movzbl r8b -> r10d                                                  *)
(*   s14 vmovq (rdx,r10,8) -> YMM9 (table lane)                              *)
(*   s15 vpshufb -> YMM9                                                     *)
(*   s16 vpmovsxbd -> YMM1 (sx1)                                             *)
(*   s17 vpmulhrsw ymm6 / s18 vpmullw ymm7 / s19 vpaddd (the mod-5 reduction, *)
(*       absent in eta4; store value = red_lane(word_sx(2-nibble)))          *)
(*   s20 vmovdqu STORE to word_add res (word (4 * outlen0))                  *)
(*                                                                           *)
(* Ordering matters: keep sx1 opaque through the reduction and step the      *)
(* store raw (s20) first with the raw word_join tree present, since the      *)
(* store simulator needs the raw stepper form (injecting the usimd8 red_lane *)
(* form before s20 makes X86_STEPS fail with a mk_comb type mismatch).       *)
(* Only after the store do we refold the store fact to usimd8 red_lane sx1   *)
(* and rewrite it into the SUBITER_STORE_POSTCOND_RL shape, then apply       *)
(* SUBITER_STORE_SPEC to fold to REJ_SAMPLE_ETA2_BYTES and append the block  *)
(* onto the running prefix store SUB_LIST(0,16i) -> SUB_LIST(0,16i+4).       *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* Step s12 through the raw store s20, sx1 kept opaque, no refold yet.       *)
let ETA2_SI1_STEP_TO_STORE_TAC : tactic =
  PURGE_STALE_STATES_TAC ["s10"] THEN
  X86_VSTEPS_TAC EXEC (12--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s11 = f0sub:int256`]) THEN
  PURGE_STALE_STATES_TAC ["s11"] THEN
  REABBREV_TAC `mask8 = read R8 s12` THEN
  X86_VERBOSE_STEP_TAC EXEC "s13" THEN MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s12 = mask8:int64`]) THEN
  (SUBGOAL_THEN maskbit_tgt ASSUME_TAC THENL [MASKBIT_TGT_TAC; ALL_TAC]) THEN
  X86_VSTEPS_TAC EXEC (14--14) THEN ETA2_TAB1_TEQ_TAC THEN
  REABBREV_TAC `tab1 = read YMM9 s14` THEN
  X86_VSTEPS_TAC EXEC (15--15) THEN REABBREV_TAC `pshuf1 = read YMM9 s15` THEN
  PURGE_STALE_STATES_TAC ["s14"] THEN
  X86_VSTEPS_TAC EXEC (16--16) THEN REABBREV_TAC `sx1 = read YMM1 s16` THEN
  PURGE_STALE_STATES_TAC ["s15"] THEN
  X86_VSTEPS_TAC EXEC (17--17) THEN X86_VSTEPS_TAC EXEC (18--18) THEN
  X86_VSTEPS_TAC EXEC (19--19) THEN
  PURGE_STALE_STATES_TAC ["s16";"s17";"s18"] THEN
  X86_STEPS_TAC EXEC (20--20);;

(* Refold the store fact (bytes256 dest, s20) to `usimd8 red_lane sx1`, using
 the same per-lane mechanism as ETA2_SI1_REDUCE_REFOLD_TAC but with
   the store fact as the target/rewrite source (read YMM1 s19 is gone).  The
   raw-tree store fact is matched by requiring `word_join` in the RHS (the raw
   stepper form) — this disambiguates it from the MAYCHANGE frame (which also
   carries a bytes256 component and a trailing s20) and from any later refolded
   copy.  It ASSUMEs `read(mem:>bytes256 A) s20 = usimd8 red_lane sx1`. *)
(* Generator for the per-sub-iter store-refold tactic: find the bytes256 store *)
(* fact at state `store_st`, then prove its LHS equals `usimd8 red_lane sx` by  *)
(* rewriting the store word_join tree and reducing both sides (SUBWORD_SUBWORD + *)
(* WORD_SIMPLE_SUBWORD collapse the vpaddd/vpmullw packing so REFL_TAC closes).  *)
let mk_eta2_store_refold (store_st:string) (sx:term) : tactic =
  W(fun (asl,w) ->
    let stv = mk_var(store_st,`:x86state`) in
    let storef = find (fun th -> is_eq(concl th) &&
        can(find_term(fun u->match u with Const("bytes256",_)->true|_->false))(lhand(concl th)) &&
        can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(rand(concl th)) &&
        (match concl th with
           Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),v)),_)-> v=stv|_->false))
       (map snd asl) in
    let memlhs = lhand(concl storef) in
    let rhs = subst [sx,`sx1:int256`] `usimd8 red_lane (sx1:int256)` in
    SUBGOAL_THEN (mk_eq(memlhs, rhs)) ASSUME_TAC THENL
     [REWRITE_TAC[storef] THEN
      REWRITE_TAC[usimd8;usimd4;usimd2;
         DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
      CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[RED_LANE_STEPFORM] THEN
      CONV_TAC(DEPTH_CONV SUBWORD_SUBWORD_CONV) THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REFL_TAC;
      ALL_TAC]);;

let ETA2_STORE_REFOLD_TAC : tactic = mk_eta2_store_refold "s20" `sx1:int256`;;

(* sx1 clean form (the vpmovsxbd lane form).                                 *)
(* Generator for the per-sub-iter sx-clean tactic: prove `sx = usimd8 word_sx  *)
(* (word_zx(word_zx pshuf))` by substituting the sx word_join def and WORD_BLAST.*)
(* The goal term is built by substituting sx/pshuf into sub-iter 1's literal so *)
(* the shape/types are guaranteed identical to the hand-written original.        *)
let mk_eta2_sx_clean (sx:term) (pshuf:term) : tactic =
  let goal = subst [sx,`sx1:int256`; pshuf,`pshuf1:int256`]
    `sx1:int256 = usimd8 (\b:byte. word_sx b:int32) (word_zx(word_zx (pshuf1:int256):int128):int64)` in
  SUBGOAL_THEN goal ASSUME_TAC THENL
   [W(fun (asl,w) ->
       let sxdef = find (fun th -> is_eq(concl th) && rand(concl th)=sx &&
           can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
       SUBST1_TAC(SYM sxdef) THEN
       REWRITE_TAC[usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
       CONV_TAC WORD_BLAST);
    ALL_TAC];;

let ETA2_SX1_CLEAN_TAC : tactic = mk_eta2_sx_clean `sx1:int256` `pshuf1:int256`;;

(* The full SI1 store fold: from post-ETA2_PREFIX_TO_S11_TAC to the folded
   running-prefix store fact ASSUMEd at s20. *)
let ETA2_SI1_FOLD : tactic =
  ETA2_SI1_STEP_TO_STORE_TAC THEN
  ETA2_STORE_REFOLD_TAC THEN
  ETA2_SX1_CLEAN_TAC THEN
  ETA2_ESTABLISH_PF_TARGET_TAC THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
    (* the store refold: read(mem:>bytes256 A) s20 = usimd8 red_lane sx1.  Match loosely
       (bytes256 in LHS + red_lane in RHS) so a perturbed sx1 form still matches. *)
    let storerf = find (fun th -> is_eq(concl th) &&
         can(find_term(fun u->match u with Const("bytes256",_)->true|_->false)) (lhand(concl th)) &&
         can(find_term(fun u->match u with Const("red_lane",_)->true|_->false)) (rand(concl th)) &&
         not(can(find_term(fun u->match u with Const("word_mul",_)->true|_->false)) (rand(concl th)))) asms in
    (* sx1 clean form                                                        *)
    let sx1clean = find (fun th -> is_eq(concl th) && lhand(concl th)=`sx1:int256` &&
         can(find_term(fun u->match u with Const("usimd8",_)->true|_->false)) (rand(concl th))) asms in
    (* pf_target: pshuf1 = <gather form>                                     *)
    let pfth = find (fun th -> concl th = pf_target) asms in
    (* the gather forall (bg1) for lane block 0, ASSUMEd by ETA2_PREFIX_TO_S11 *)
    let bg = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f0sub:int256`))c &&
        can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))c &&
        not(can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))c) &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (24,8):byte`))c) asms in
    let mthm = find (fun th -> concl th = maskbit_tgt) asms in
    (* store fact in the SUBITER_STORE_POSTCOND_RL LHS shape                 *)
    let store_full = REWRITE_RULE[pfth] (REWRITE_RULE[sx1clean] storerf) in
    let g = `word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128` in
    let m = `word (val (mask8:int64) MOD 256):byte` in
    let pc = ISPECL [`word_add res (word (4 * outlen0)):int64`; `s20:x86state`; g; m;
                     `LENGTH(ACC_IDX (word (val (mask8:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND_RL in
    let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
    (* SUBITER_STORE_SPEC: MAP red_lane (MAP word_sx (SUB_LIST(0,k)(PSHUFB_OUT_LIST g m)))
       = REJ_SAMPLE_ETA2_BYTES [b0..b3] *)
    let spec = ISPECL [g; m; `word_subword (chunk0:int128) (0,8):byte`;
        `word_subword (chunk0:int128) (8,8):byte`; `word_subword (chunk0:int128) (16,8):byte`;
        `word_subword (chunk0:int128) (24,8):byte`] SUBITER_STORE_SPEC in
    let gather_hyp = List.nth (conjuncts(lhand(concl spec))) 1 in
    let gthm = EQ_MP (SYM(REWRITE_CONV[WORD_ZX_TRIVIAL] gather_hyp)) bg in
    let specres = MP spec (CONJ mthm gthm) in
    let rej_store = REWRITE_RULE[specres] res_th0 in
    (* fold onto the running prefix (SUB_LIST(0,16i) -> SUB_LIST(0,16i+4))   *)
    let blk = `[word_subword (chunk0:int128) (0,8); word_subword chunk0 (8,8);
                word_subword chunk0 (16,8); word_subword chunk0 (24,8)]:byte list` in
    let prefixbytes = `SUB_LIST(0,16*i) (inlist:byte list)` in
    let prefix_store = find (fun th ->
         (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s20",_))),_) -> true | _ -> false) &&
         hasC "num_of_wordlist" th && hasC "SUB_LIST" th &&
         can(find_term(fun u->u=`res:int64`))(lhand(concl th)) &&
         can(find_term(fun u->u=`outlen0:num`))(lhand(concl th)) &&
         not(hasC "ACC_IDX" th)) asms in
    let len_eq = find (fun th -> match concl th with
         Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) asms in
    let blk16 = find (fun th -> is_eq(concl th) && hasC "SUB_LIST" th &&
         (try length(dest_list(rand(concl th))) = 16 with _ -> false)) asms in
    let leninl = find (fun th -> match concl th with
         Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Var("inlist",_))),_) -> true | _ -> false) asms in
    let i116 = find (fun th -> match concl th with
         Comb(Comb(Const("<=",_),Comb(Comb(Const("*",_),_),Comb(Comb(Const("+",_),Var("i",_)),_))),_) -> true | _ -> false) asms in
    let lenle = REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*(i+1) <= 136 ==> 16*i+16 <= 136`) i116) in
    let lr = MP (ISPECL [m; `chunk0:int128`] LEN_RECONCILE) mthm in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES) (CONJ lenle blk16) in
    let blk_bytes = CONJUNCT1 bb in
    let rej_store2 = REWRITE_RULE[SYM len_eq] rej_store in
    let prefix_store2 = REWRITE_RULE[SYM len_eq] prefix_store in
    let fold = MP (ISPECL [`res:int64`;`s20:x86state`;m;blk;prefixbytes] SUBITER_FOLD_STEP)
                  (CONJ lr (CONJ prefix_store2 rej_store2)) in
    let split0 = REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i`;`4`;`0`] SUB_LIST_SPLIT) in
    let clean = REWRITE_RULE[GSYM blk_bytes; GSYM split0] fold in
    ASSUME_TAC clean);;

(* ========================================================================= *)
(* eta2 CORRECT: the SI1 counter+branch block (s21-26).                      *)
(*                                                                           *)
(* Runs AFTER ETA2_SI1_FOLD, which leaves the running-prefix store fact      *)
(* ASSUMEd at s20 (prefix SUB_LIST(0,16i+4)) with the SIMD sub-iter-1 store  *)
(* folded.  This block advances the accept-count accumulator (RAX), the buffer *)
(* index (RCX), and the mask register (R8), then resolves the mid-iteration ja *)
(* back to the sub-iter-2 entry.  State indices are +3 relative to the store *)
(* (eta2 stores at s20, due to the 3 inserted mod-5 reduction ops s17-19).   *)
(*                                                                           *)
(* Control flow:                                                             *)
(*   s21 popcnt %r10d,%r9d  (0xb9)   -> R9 = word_popcount of the mask byte  *)
(*   s22 add   %r9d,%eax    (0xbe)   -> RAX = outlen0 + popcount             *)
(*   s23 shr   $0x8,%r8d    (0xc1)   -> R8 = mask8 >> 8                      *)
(*   s24 add   $0x4,%ecx    (0xc5)   -> RCX = 16i + 4                        *)
(*   s25 cmp   $0xf8,%eax   (0xc8)   (248 head guard for sub-iter 2)         *)
(*   s26 ja    scalar       (0xcd)   -> RIP s26 = if <ja> then pc+399 else   *)
(*                                       pc+207  (fall-through = SI2 entry)  *)
(* Forms at s24:                                                             *)
(*   read RIP s24 = word(pc + 196)                                           *)
(*   read RCX s24 = word_zx(word_add(word_zx(word(16*i)))(word 4))           *)
(*   read RAX s24 = word_zx(word_add(word_zx(word outlen0))                  *)
(*                    (word_zx(word_zx(word(word_popcount(word_zx^3          *)
(*                      (word(val mask8 MOD 256))))))))                      *)
(*   read R9  s24 = word_zx(word(word_popcount(word_zx^3(word(val mask8 MOD  *)
(*                    256)))))                                               *)
(*   read R8  s24 = word_zx(word_ushr(word_zx mask8) 8)                      *)
(*                                                                           *)
(* popcount->length bridge: popeq (popcount -> low-8 bitsum) + bsum (bitsum -> *)
(* LENGTH(REJ_NIBBLES block0)) two-step, because the RAX/JA collapse needs the *)
(* intermediate `word_popcount(...) = LENGTH(...)` equality (via             *)
(* BITVAL_SUM_8_EQ_LENGTH_FILTER_ETA2 + LENGTH_FILTER_BYTE_NIBBLES_4_BYTES). *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

let ETA2_SI1_COUNTER_TAC : tactic =
  (* Counters: popcnt / add / shr / add.  RAX/RCX/R8/R9 advance; RIP -> pc+196. *)
  X86_STEPS_TAC EXEC (21--24) THEN
  (* Establish the 16-byte block's byte decomposition (SUB_LIST(16i,4)=...). *)
  MP_TAC(ISPECL[`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `LENGTH(inlist:byte list) = 136` THEN
    UNDISCH_TAC `16 * i <= 120` THEN ARITH_TAC; STRIP_TAC] THEN
  (* Fold mask8's bitsum def back into the popcount-bearing assumptions (but NOT
     into maskbit_tgt or the TABLE_ENTRY facts). *)
  W(fun (asl,w) ->
     let m8def = find (fun th -> match concl th with Comb(Comb(Const("=",_),_),Var("mask8",_)) -> true | _ -> false) (map snd asl) in
     RULE_ASSUM_TAC(fun th -> if concl th = maskbit_tgt ||
        can(find_term(fun u->match u with Const("TABLE_ENTRY",_)->true|_->false))(concl th)
        then th else REWRITE_RULE[GSYM m8def] th)) THEN
  (* === REORDERED branch resolution (NO RULE_ASSUM over s25 state) ===      *)
  W(fun (asl,w) ->
    (* 1. popeq: word_popcount(word_zx^3(word(val mask8 MOD 256))) = bitsum8(low8 of f1bnd) *)
    let r9 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("R9",_)),Var("s24",_))),_) -> true | _ -> false) asl in
    let goal_pc = find_term (fun t -> match t with Comb(Const("word_popcount",_),_) -> true | _ -> false) (concl(snd r9)) in
    let low8 = `bitval(bit 7 (word_subword (f1bnd:int256) (0,8):byte)) + bitval(bit 7 (word_subword f1bnd (8,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (16,8):byte)) + bitval(bit 7 (word_subword f1bnd (24,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (32,8):byte)) + bitval(bit 7 (word_subword f1bnd (40,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (48,8):byte)) + bitval(bit 7 (word_subword f1bnd (56,8):byte))` in
    let mr = CONV_RULE(DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV)
               (SPEC `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` MOD_RED) in
    let popeq = prove(mk_eq(goal_pc, low8),
      REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; MOD_MOD_EXP_MIN] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; mr] THEN
      MAP_EVERY (fun b -> BOOL_CASES_TAC b)
        [`bit 7 (word_subword (f1bnd:int256) (0,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (8,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (16,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (24,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (32,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (40,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (48,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (56,8):byte)`] THEN
      REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV) in
    (* 2. bitsum8 = LENGTH(REJ_NIBBLES_ETA2 block0) via maskbit forall + block byte facts *)
    let maskbit = snd(find (fun (_,th) -> let c=concl th in is_forall c &&
        can(find_term(fun u->u=`f1bnd:int256`))c && can(find_term(fun u->match u with Comb(Const("bit",_),_)->true|_->false))c &&
        not(can(find_term(fun u->match u with Const("word_zx",_)->true|_->false))c) &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (24,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (32,8):byte`))c)) asl) in
    let mb_tm = concl maskbit in
    let blk0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
           (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
    let blkeq = mk_eq(low8, `LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i,4) inlist):int16 list)`) in
    let blk0_tm = concl(snd blk0) in
    let bsum_raw = prove(mk_imp(mb_tm, mk_imp(blk0_tm, blkeq)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN DISCH_THEN(fun b -> REWRITE_TAC[b]) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER_ETA2] THEN
      ASM_SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let bsum = MP (MP bsum_raw maskbit) (snd blk0) in
    (* combined: word_popcount(...) = LENGTH(REJ_NIBBLES_ETA2 block0)        *)
    let pop_len = TRANS popeq bsum in
    (* 3. bound: outlen0 + LENGTH(REJ_NIBBLES_ETA2 block0) <= 248            *)
    let leninl = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Var("inlist",_))),_) -> true | _ -> false) asl in
    let i116 = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("<=",_),Comb(Comb(Const("*",_),_),Comb(Comb(Const("+",_),Var("i",_)),_))),_) -> true | _ -> false) asl in
    let nible = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("<=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_NIBBLES_ETA2",_),_))),_) -> true | _ -> false) asl in
    let len_eq = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) asl in
    let a1 = MP (MP (ARITH_RULE `16*(i+1)<=136 ==> (LENGTH(inlist:byte list)=136 ==> 16*(i+1)<=LENGTH inlist)`)
                    (snd i116)) (snd leninl) in
    let bnd0 = MP (ISPECL[`inlist:byte list`;`i:num`] SUBITER_OUTLEN_BOUND_1) (CONJ a1 (snd nible)) in
    let bnd = REWRITE_RULE[snd len_eq] bnd0 in  (* outlen0 + LENGTH(REJ_NIBBLES_ETA2 block0) <= 248 *)
    (* 4. RAX collapse: word_zx(word_add(word_zx(word outlen0))(word_zx(word_zx(word popcount)))) = word(outlen0+block0len) *)
    let block0len = `LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i,4) inlist):int16 list)` in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in  (* word_zx(...word outlen0...word block0len...) = word(outlen0+block0len) *)
    (* but RAX has popcount, not block0len; rewrite popcount->block0len first via pop_len *)
    let rax_red = REWRITE_RULE[pop_len] (GSYM(REWRITE_RULE[GSYM pop_len] (SYM rax_red0))) in
    (* JA_NOT_TAKEN: outlen0+block0len <= 248                                *)
    let ja = MP (ISPECL[mk_binop `(+):num->num->num` `outlen0:num` block0len; `248`] JA_NOT_TAKEN_LE)
                (CONJ bnd (ARITH_RULE `248 < 2 EXP 32`)) in
    (* stash these as assumptions for the step                               *)
    ASSUME_TAC pop_len THEN ASSUME_TAC bnd THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja) THEN
  X86_STEPS_TAC EXEC (25--26) THEN
  (* resolve the ja branch: RIP s26 = pc+207 (fall through to sub-iter 2)    *)
  SUBGOAL_THEN `read RIP s26 = word (pc + 207):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let blk0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
             (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
      let rax_red0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
      let ja = find (fun (_,th) -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th)) asl in
      FIRST_ASSUM(fun th -> if can(find_term(fun u->u=`pc + 207`))(concl th) then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[GSYM(snd blk0)] THEN REWRITE_TAC[snd rax_red0] THEN
      REWRITE_TAC[snd ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  (* fold RAX read clean using the assumed pop_len + rax_red0 (now in asl)   *)
  W(fun (asl,w) ->
    let pl = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
    let rr = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
    RULE_ASSUM_TAC(REWRITE_RULE[snd pl]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd rr])) THEN
  ALL_TAC;;

(* ========================================================================= *)
(* eta2 CORRECT: SI2+ constant-independent substrate.                        *)
(*                                                                           *)
(* The two eta2-generalized helpers the sub-iter 2/3/4 store folds need.  Both *)
(* are pure list/word algebra.                                               *)
(*                                                                           *)
(* LEN_RECONCILE_GEN: LEN_RECONCILE generalized to arbitrary 4 block bytes   *)
(*   b0..b3 (LEN_RECONCILE hardcoded chunk0 lanes 0/8/16/24).  Needed because *)
(*   sub-iter k's block bytes are chunk0 (32,40,48,56) for SI2, (64,72,80,88) *)
(*   for SI3, etc.                                                           *)
let LEN_RECONCILE_GEN = prove
 (`!(m:byte) (b0:byte) (b1:byte) (b2:byte) (b3:byte).
     (!j. j < 8 ==> (bit j m <=>
        EL j [val b0 MOD 16; val b0 DIV 16; val b1 MOD 16; val b1 DIV 16;
              val b2 MOD 16; val b2 DIV 16; val b3 MOD 16; val b3 DIV 16] < 15))
     ==> LENGTH(ACC_IDX m) =
         LENGTH(REJ_SAMPLE_ETA2_BYTES [b0;b1;b2;b3]:int32 list)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:byte`;
    `word(val(b0:byte) MOD 16):byte`; `word(val(b0:byte) DIV 16):byte`;
    `word(val(b1:byte) MOD 16):byte`; `word(val(b1:byte) DIV 16):byte`;
    `word(val(b2:byte) MOD 16):byte`; `word(val(b2:byte) DIV 16):byte`;
    `word(val(b3:byte) MOD 16):byte`; `word(val(b3:byte) DIV 16):byte`] ACC_LENGTH_EQ_FILTER_ETA2) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    W(fun (asl,gw) -> let n = rand(rator(lhand gw)) in
       MP_TAC(SPEC n (find (fun th -> is_forall(concl th) && can(find_term(fun u->match u with Const("EL",_)->true|_->false))(concl th)) (map snd asl)))) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN
    W(fun (asl,gw) -> let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="val" && type_of(rand u)=`:byte` with _->false) gw in
       let bt = rand bt in
       MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN STRIP_TAC THEN
       SUBGOAL_THEN (mk_eq(mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,mk_binop `MOD` (mk_comb(`val:byte->num`,bt)) `16`)), mk_binop `MOD` (mk_comb(`val:byte->num`,bt)) `16`)) SUBST1_TAC THENL
        [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
       SUBGOAL_THEN (mk_eq(mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,mk_binop `DIV` (mk_comb(`val:byte->num`,bt)) `16`)), mk_binop `DIV` (mk_comb(`val:byte->num`,bt)) `16`)) SUBST1_TAC THENL
        [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
       REFL_TAC);
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LENGTH_FILTER_BYTE_NIBBLES_4_BYTES; LENGTH_REJ_SAMPLE_ETA2_BYTES]]);;

(* ACC1_IDENT_TAC.  acc1 must be ABBREV'd as
   outlen0 + LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16i,4))), with the outlen0 def in
   asl.  Proves & ASSUMEs LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16i+4)))=acc1. *)
let ACC1_IDENT_TAC : tactic =
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) = acc1` ASSUME_TAC THENL
  [ONCE_REWRITE_TAC[REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i`;`4`;`0`] SUB_LIST_SPLIT)] THEN
   REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES; REJ_NIBBLES_ETA2_APPEND; LENGTH_APPEND] THEN
   FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_))->true|_->false)
       then ASSUME_TAC(REWRITE_RULE[LENGTH_REJ_SAMPLE_ETA2_BYTES] th) else NO_TAC) THEN
   FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_NIBBLES_ETA2",_),_))),Var("outlen0",_))->true|_->false)
       then REWRITE_TAC[th] else NO_TAC) THEN
   FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),_),Var("acc1",_))->can(find_term(fun u->u=`outlen0:num`))(concl th)|_->false) then (MP_TAC th THEN ARITH_TAC) else NO_TAC); ALL_TAC];;

(* ========================================================================= *)
(* eta2 CORRECT: SI2 gather-side bridge (maskbit_tgt_2 tactic,               *)
(* pf_target_2, PF_PROOF_2, TAB2_TEQ).                                       *)
(*                                                                           *)
(* The sub-iter-2 analogues of the SI1 gather machinery.  All are            *)
(* constant-independent of the mod-5 reduction (they concern the vpshufb     *)
(* table gather and the vpmovmskb mask byte-1 popcount).  eta2 specifics:    *)
(* - pf_target base uses the YMM9 table lane                                 *)
(*   - SI2 state indices: mask8b = R8 s26; vmovq table at s29                *)
(* - maskbit_tgt_2 already <15, DIVMOD256_SPLIT                              *)
(*                                                                           *)
(* Control flow:                                                             *)
(*   read RIP s26 = pc+207 (SI2 entry); read R8 s26 = word_zx(word_ushr(mask8 *)
(*     bitsum) 8) (= mask8b before reabbrev).                                *)
(*   SI2 opener s27 = vpsrldq $8 (0xd3) -> XMM8, RIP s27 = pc+213.  The gather *)
(*   source at s27 is word_zx(word_ushr(word_zx(word_zx(word_subword <F0SUB  *)
(*   VALUE> (0,128)))) 64) — f0sub is EXPANDED here (the SI1 counter block   *)
(*   did not carry the f0sub fold onto XMM8), so the SI2 tactic must RE-FOLD *)
(*   f0sub (its ABBREV def `<value> = f0sub` survives in the asl) before the *)
(*   gather forall / pf_target_2 match.                                      *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* ETA2_TAB2_TEQ_TAC: derive the sub-iter-2 table-load bridge teq (tab2) at s28. *)
let ETA2_TAB2_TEQ_TAC : tactic = ETA2_TAB_TEQ_GEN 28 29 `mask8b:int64` RLT_B R_EQ_B;;

(* ETA2_PF_PROOF_2: discharge the sub-iter-2 `pshuf2 = pf_target_2` subgoal. *)
let ETA2_PF_PROOF_2 : tactic = mk_eta2_pf_proof `pshuf2:int256` `tab2:int256`;;

(* ========================================================================= *)
(* eta2 CORRECT: the SI2 store fold.                                         *)
(*                                                                           *)
(* The sub-iter-2 analogue of ETA2_SI1_FOLD.  Runs AFTER ETA2_SI1_COUNTER_TAC, *)
(* which leaves s26 (RIP=pc+207 = SI2 entry), R8 s26 = mask8>>8 (the         *)
(* sub-iter-2 mask byte, bits 8-15 of the packed 32-bit popcount mask), and  *)
(* the running-prefix store fact folded to SUB_LIST(0,16i+4) present.  It    *)
(* advances the SIMD store for block1 (chunk0 lanes 32/40/48/56) and folds the *)
(* prefix to SUB_LIST(0,16i+8).  Uses the red_lane store wrap                *)
(* (SUBITER_STORE_POSTCOND_RL), the >>64-shifted gather source g2, and the   *)
(* f0sub RE-FOLD on XMM8 (the SI1 counter block does NOT carry the           *)
(* `read YMM0 s11 = f0sub` fold onto XMM8, so f0sub is EXPANDED at s27; its  *)
(* ABBREV def survives in the asl, so RULE_ASSUM re-folds it).               *)
(*                                                                           *)
(* eta2 SI2 step map:                                                        *)
(*   s27 vpsrldq $8 xmm8 (0xd3) -> XMM8 (gather src, f0sub EXPANDED),        *)
(*       RIP s27 = pc+213                                                    *)
(*   s28 movzbl r8b -> r10d (REX-byte shim; MOVZBL_R10_CAPTURE_TAC)          *)
(*   s29 vmovq (rdx,r10,8) -> YMM9 (table lane; ETA2_TAB2_TEQ_TAC)           *)
(*   s30 vpshufb -> YMM9 (pshuf2)                                            *)
(*   s31 vpmovsxbd -> YMM1 (sx2)                                             *)
(*   s32 vpmulhrsw ymm6 / s33 vpmullw ymm7 / s34 vpaddd — the mod-5 reduction *)
(*   s35 vmovdqu STORE to word_add res (word (4 * acc1))                     *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* Setup + step s27..s35 (raw store, sx2 opaque).  From s26 (post-SI1-counter). *)
let ETA2_SI2_STEP_TO_STORE_TAC : tactic =
  REABBREV_TAC `mask8b = read R8 s26` THEN
  ABBREV_TAC `acc1 = outlen0 + LENGTH (REJ_NIBBLES_ETA2 (SUB_LIST(16*i,4) inlist):int16 list)` THEN
  ACC1_IDENT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) = acc1`]) THEN
  (* s27 vpsrldq -> XMM8; f0sub is EXPANDED here.  Its surviving ABBREV def (the
     s11 stepper assumption, with `read YMM0 s11` abstracted to f0sub) is
     `f0sub = <word_join tree>` (f0sub on LHS).  Fold the expanded tree back to
     `f0sub` via `<tree> = f0sub` (= SYM of the def).  Skip the def itself so it
     survives for pf_target_2's fold. *)
  X86_VSTEPS_TAC EXEC (27--27) THEN
  W(fun (asl,w) ->
     let f0d = find (fun th -> is_eq(concl th) &&
        (lhand(concl th) = `f0sub:int256` || rand(concl th) = `f0sub:int256`) &&
        can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
     let f0fold = if rand(concl f0d) = `f0sub:int256` then f0d else SYM f0d in
     RULE_ASSUM_TAC(fun th -> if concl th = concl f0d then th else REWRITE_RULE[f0fold] th)) THEN
  X86_VERBOSE_STEP_TAC EXEC "s28" THEN MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s27 = mask8b:int64`]) THEN
  (SUBGOAL_THEN maskbit_tgt_2 ASSUME_TAC THENL [MASKBIT_TGT_2_TAC; ALL_TAC]) THEN
  X86_VSTEPS_TAC EXEC (29--29) THEN ETA2_TAB2_TEQ_TAC THEN
  REABBREV_TAC `tab2 = read YMM9 s29` THEN
  X86_VSTEPS_TAC EXEC (30--30) THEN REABBREV_TAC `pshuf2 = read YMM9 s30` THEN
  PURGE_STALE_STATES_TAC ["s29"] THEN
  X86_VSTEPS_TAC EXEC (31--31) THEN REABBREV_TAC `sx2 = read YMM1 s31` THEN
  PURGE_STALE_STATES_TAC ["s30"] THEN
  X86_VSTEPS_TAC EXEC (32--32) THEN X86_VSTEPS_TAC EXEC (33--33) THEN
  X86_VSTEPS_TAC EXEC (34--34) THEN
  PURGE_STALE_STATES_TAC ["s31";"s32";"s33"] THEN
  VAL_INT64_TAC `acc1:num` THEN
  X86_STEPS_TAC EXEC (35--35);;

(* Refold the s35 store fact (bytes256) to `usimd8 red_lane sx2` — 
   ETA2_STORE_REFOLD_TAC with s20->s35, sx1->sx2 (constant-independent). *)
let ETA2_STORE_REFOLD_2_TAC : tactic = mk_eta2_store_refold "s35" `sx2:int256`;;

(* sx2 clean form (vpmovsxbd lane form) — ETA2_SX1_CLEAN_TAC, sx1->sx2.      *)
let ETA2_SX2_CLEAN_TAC : tactic = mk_eta2_sx_clean `sx2:int256` `pshuf2:int256`;;

(* PERF: fold the expanded f0sub subtree back to the var in the pshuf2 def, then
 discharge pf_target_2 — ETA2_ESTABLISH_PF_TARGET_TAC for pshuf2. *)
let ETA2_ESTABLISH_PF_TARGET_2_TAC : tactic =
  mk_eta2_establish_pf_target `pshuf2:int256` pf_target_2 ETA2_PF_PROOF_2;;

(* The full SI2 store fold: from post-ETA2_SI1_COUNTER (s26) to the folded
   running-prefix store fact ASSUMEd at s35 (prefix SUB_LIST(0,16i+8)). *)
let ETA2_SI2_FOLD : tactic =
  ETA2_SI2_STEP_TO_STORE_TAC THEN
  ETA2_STORE_REFOLD_2_TAC THEN
  ETA2_SX2_CLEAN_TAC THEN
  ETA2_ESTABLISH_PF_TARGET_2_TAC THEN
  ACC1_IDENT_TAC THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
    (* store refold: read(mem:>bytes256 A) s35 = usimd8 red_lane sx2         *)
    let storerf = find (fun th -> is_eq(concl th) &&
         can(find_term(fun u->match u with Const("bytes256",_)->true|_->false)) (lhand(concl th)) &&
         can(find_term(fun u->match u with Const("red_lane",_)->true|_->false)) (rand(concl th)) &&
         not(can(find_term(fun u->match u with Const("word_mul",_)->true|_->false)) (rand(concl th)))) asms in
    let sx2clean = find (fun th -> is_eq(concl th) && lhand(concl th)=`sx2:int256` &&
         can(find_term(fun u->match u with Const("usimd8",_)->true|_->false)) (rand(concl th))) asms in
    let pfth = find (fun th -> concl th = pf_target_2) asms in
    (* the >>64-shifted gather forall (bg2) for lane block 32, ASSUMEd by ETA2_PREFIX_TO_S11 *)
    let bg = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f0sub:int256`))c &&
        can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (32,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (64,8):byte`))c)) asms in
    let mthm = find (fun th -> concl th = maskbit_tgt_2) asms in
    let store_full = REWRITE_RULE[pfth] (REWRITE_RULE[sx2clean] storerf) in
    let g2 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128) 64):int128):int128` in
    let m = `word (val (mask8b:int64) MOD 256):byte` in
    let pc = ISPECL [`word_add res (word (4 * acc1)):int64`; `s35:x86state`; g2; m;
                     `LENGTH(ACC_IDX (word (val (mask8b:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND_RL in
    let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
    (* SUBITER_STORE_SPEC on the block1 lanes (chunk0 32/40/48/56)           *)
    let spec = ISPECL [g2; m; `word_subword (chunk0:int128) (32,8):byte`;
        `word_subword (chunk0:int128) (40,8):byte`; `word_subword (chunk0:int128) (48,8):byte`;
        `word_subword (chunk0:int128) (56,8):byte`] SUBITER_STORE_SPEC in
    let specres = MP spec (CONJ mthm bg) in
    let rej_store = REWRITE_RULE[specres] res_th0 in
    (* block1 bytes, fold onto the running prefix SUB_LIST(0,16i+4) -> SUB_LIST(0,16i+8) *)
    let leninl = find (fun th -> match concl th with
         Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Var("inlist",_))),_) -> true | _ -> false) asms in
    let i116 = find (fun th -> match concl th with
         Comb(Comb(Const("<=",_),Comb(Comb(Const("*",_),_),Comb(Comb(Const("+",_),Var("i",_)),_))),_) -> true | _ -> false) asms in
    let blk16 = find (fun th -> is_eq(concl th) && hasC "SUB_LIST" th &&
         (try length(dest_list(rand(concl th))) = 16 with _ -> false)) asms in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*(i+1)<=136 ==> 16*i+16<=136`) i116)) blk16) in
    let blk1_eq = el 1 (CONJUNCTS bb) in    (* SUB_LIST(16i+4,4) = [lanes 32,40,48,56] *)
    (* LEN_RECONCILE_GEN over the block1 bytes                               *)
    let lr0 = MP (ISPECL [m;`word_subword (chunk0:int128) (32,8):byte`;`word_subword (chunk0:int128) (40,8):byte`;
        `word_subword (chunk0:int128) (48,8):byte`;`word_subword (chunk0:int128) (56,8):byte`] LEN_RECONCILE_GEN) mthm in
    let lr = REWRITE_RULE[GSYM blk1_eq] lr0 in
    let rej_store1 = REWRITE_RULE[GSYM blk1_eq] rej_store in
    (* restate store addresses/prefix via acc1_ident                         *)
    let acc1_ident = find (fun th -> match concl th with
         Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA2_BYTES",_),_))),Var("acc1",_)) -> true | _ -> false) asms in
    let prefix_store0 = find (fun th -> (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s35",_))),_) -> true | _ -> false) &&
         hasC "num_of_wordlist" th && hasC "SUB_LIST" th && can(find_term(fun u->u=`acc1:num`))(lhand(concl th)) &&
         not(hasC "ACC_IDX" th) && not(hasC "bytes256" th)) asms in
    let prefix_store = REWRITE_RULE[GSYM acc1_ident] prefix_store0 in
    let rej_store2 = REWRITE_RULE[GSYM acc1_ident] rej_store1 in
    let fold = MP (ISPECL [`res:int64`;`s35:x86state`;m;`SUB_LIST(16*i+4,4) (inlist:byte list)`;`SUB_LIST(0,16*i+4) (inlist:byte list)`] SUBITER_FOLD_STEP)
                  (CONJ lr (CONJ prefix_store rej_store2)) in
    let split = REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i+4`;`4`;`0`] SUB_LIST_SPLIT) in
    let clean = REWRITE_RULE[GSYM split; ARITH_RULE `(16*i+4)+4 = 16*i+8`] fold in
    ASSUME_TAC clean);;

(* ========================================================================= *)
(* eta2 CORRECT: the SI2 counter+branch block (s36-41).                      *)
(*                                                                           *)
(* The sub-iter-2 counter, using POPCNT_BYTE1 because the SI2 mask byte is   *)
(* byte-1 of the packed 32-bit popcount sum: mask8b = R8 s26 =               *)
(* word_zx(word_ushr(word_zx(word(SUM32 over f1bnd lanes 0-31))) 8) (the SUM32 *)
(* survives inside the mask8b ABBREV def).  POPCNT_BYTE1 (which encodes the >>8 *)
(* + MOD 256 internally) extracts bits 8-15 = f1bnd lanes 8-15 = block1      *)
(* (chunk0 lanes 32-56).                                                     *)
(*                                                                           *)
(* Runs AFTER ETA2_SI2_FOLD from s35 (running prefix store folded to         *)
(* SUB_LIST(0,16i+8), mask8b + acc1 abbreviated, maskbit_tgt_2 ASSUMEd).  It *)
(* advances RAX (acc1 -> acc1 + block1len), RCX (16i+4 -> 16i+8), R8 (mask8b -> *)
(* mask8b>>8 = mask8c), and resolves the mid-iteration ja to the SI3 entry.  *)
(*                                                                           *)
(* Control flow:                                                             *)
(*   s36 popcnt %r10d,%r9d ; s37 add %r9d,%eax ; s38 shr $0x8,%r8d ;         *)
(*   s39 add $0x4,%ecx (RIP s39 = pc+266) ; s40 cmp $0xf8,%eax ; s41 ja scalar *)
(*   -> RIP s41 = if <ja> then pc+399 else pc+273  (fall-through = SI3 entry). *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* SI2_MG: build pop_len2 (popcount = block1len), bnd2c (acc1+block1len<=248),
   rax_red0 (RAX collapse), ja (JA_NOT_TAKEN). *)
let ETA2_SI2_MG_TAC : tactic =
  X86_STEPS_TAC EXEC (36--39) THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
    let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
    let popcnt2 = REWRITE_RULE[m8b_def]
       (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE1)) in
    let lanesum8 = rand(concl popcnt2) in
    (* the f1bnd-lane maskbit forall for lanes 8-15 (the `8*(k+8)` one)      *)
    let mb2 = find_a (fun th -> let c=concl th in is_forall c &&
       can(find_term(fun u->u=`f1bnd:int256`))c &&
       can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),c) -> c=`8` | _ -> false))c) in
    let mb2_tm = concl mb2 in
    let i_le = find_a (fun th -> concl th = `16 * i <= 120`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
    let blk16 = find_a (fun th -> is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" &&
            length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=120 ==> 16*i+16<=136`) i_le))
                      blk16) in
    let blk1_eq = el 1 (CONJUNCTS bb) in
    let block1 = `[word_subword (chunk0:int128) (32,8); word_subword chunk0 (40,8);
                   word_subword chunk0 (48,8); word_subword chunk0 (56,8)]:byte list` in
    let block1len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA2`, block1)) in
    let bsum2_raw = prove(mk_imp(mb2_tm, mk_eq(lanesum8, block1len_x)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV)
            (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER_ETA2] THEN
      SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    (* fold explicit block1 -> SUB_LIST(16i+4,4) via blk1_eq (GSYM)          *)
    let pop_len2 = REWRITE_RULE[GSYM blk1_eq] (TRANS popcnt2 (MP bsum2_raw mb2)) in
    (* bound: acc1 + block1len <= 248, via SUBITER_OUTLEN_BOUND_2 rewritten to acc1 *)
    let i116 = find_a (fun th -> concl th = `16 * (i + 1) <= 136`) in
    let nibbnd = find_a (fun th -> concl th = `LENGTH (REJ_NIBBLES_ETA2 (SUB_LIST (0,16 * (i + 1)) inlist):int16 list) <= 248`) in
    let a1 = MP (MP (ARITH_RULE `16*(i+1)<=136 ==> (LENGTH(inlist:byte list)=136 ==> 16*(i+1)<=LENGTH inlist)`) i116) leninl in
    let bnd2 = MP (ISPECL[`inlist:byte list`;`i:num`] SUBITER_OUTLEN_BOUND_2) (CONJ a1 nibbnd) in
    let outlen0_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) in
    let acc1_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),_),_)),Var("acc1",_)) -> true | _ -> false) in
    let bnd2a = REWRITE_RULE[outlen0_def; ADD_ASSOC] bnd2 in
    let bnd2c = REWRITE_RULE[acc1_def] bnd2a in   (* acc1 + block1len <= 248 *)
    let block1len = `LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i+4,4) inlist):int16 list)` in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd2c in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let ja = MP (ISPECL[mk_binop `(+):num->num->num` `acc1:num` block1len; `248`] JA_NOT_TAKEN_LE)
                (CONJ bnd2c (ARITH_RULE `248 < 2 EXP 32`)) in
    ASSUME_TAC pop_len2 THEN ASSUME_TAC bnd2c THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja);;

(* SI2_RESOLVE: step s40-41, resolve RIP s41 = pc+273.                       *)
let ETA2_SI2_RESOLVE_TAC : tactic =
  X86_STEPS_TAC EXEC (40--41) THEN
  SUBGOAL_THEN `read RIP s41 = word (pc + 273):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let asms = map snd asl in
      let pop_len2_old = find (fun th -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asms in
      let zbe = MP (SPEC `val (mask8b:int64) MOD 256` zxbyte_eq) (ARITH_RULE `val (mask8b:int64) MOD 256 < 256`) in
      let pop_len2_typed = TRANS (AP_TERM `word_popcount:int32->num` zbe) pop_len2_old in
      let rax_red0 = find (fun th -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asms in
      let ja = find (fun th -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`acc1:num`))(concl th)) asms in
      let ifrip = find (fun th -> match concl th with
         Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s41",_))),r) ->
           (match r with Comb(Comb(Comb(Const("COND",_),_),_),_) -> true | _ -> false) | _ -> false) asms in
      MP_TAC ifrip THEN REWRITE_TAC[pop_len2_typed] THEN REWRITE_TAC[rax_red0] THEN
      REWRITE_TAC[ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  (* fold RAX read clean using pop_len2 + rax_red0 (now in asl)              *)
  W(fun (asl,w) ->
    let pl = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
    let rr = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
    let zbe = MP (SPEC `val (mask8b:int64) MOD 256` zxbyte_eq) (ARITH_RULE `val (mask8b:int64) MOD 256 < 256`) in
    let pl_typed = TRANS (AP_TERM `word_popcount:int32->num` zbe) (snd pl) in
    RULE_ASSUM_TAC(REWRITE_RULE[pl_typed]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd rr])) THEN
  ALL_TAC;;

let ETA2_SI2_COUNTER_TAC : tactic =
  ETA2_SI2_MG_TAC THEN ETA2_SI2_RESOLVE_TAC;;

(* ========================================================================= *)
(* eta2 CORRECT: SI3 constant-independent gather substrate.                  *)
(*                                                                           *)
(* The sub-iter-3 analogues of the SI2 gather machinery.  All are            *)
(* constant-independent of the mod-5 reduction (they concern the vpshufb     *)
(* table gather and the vpmovmskb mask byte-2 popcount).  eta2 SI3 state     *)
(* indices: table-mem invariant at s43, vmovq YMM9 at s44.                   *)
(*                                                                           *)
(* Control flow (from the SI2-done state s41): SI3 opener s42 =              *)
(* vextracti128 $1,%ymm0,%xmm8 (raw 0x115 = tmc pc+273), RIP s42 = pc+279.   *)
(* XMM8 s42 = the HIGH-128 of the EXPANDED f0sub (ymm0), so the SI3 fold must *)
(* RE-FOLD f0sub (surviving ABBREV def); then the gather source is           *)
(* g3 = word_zx(word_zx(word_subword f0sub (128,128))) (HIGH 128, NO >>64    *)
(* shift — matches g3_eta2 / bg3 directly).                                  *)
(*   s43 movzbl r8b->r10d ; s44 vmovq (rdx,r10,8)->YMM9 ; s45 vpshufb ;      *)
(*   s46 vpmovsxbd ; s47-49 mod-5 reduction ; s50 store ; s51-56 counter.    *)
(*                                                                           *)
(* mask8c = R8 s41 = mask8b>>8 (byte 2 of the packed 32-bit popcount sum =   *)
(* f1bnd lanes 16-23 = block2 = chunk0 lanes 64-88).                         *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* DIVMOD65536_SPLIT / R_EQ_C / RLT_C.                                       *)
let ETA2_TAB3_TEQ_TAC : tactic = ETA2_TAB_TEQ_GEN 43 44 `mask8c:int64` RLT_C R_EQ_C;;

(* ETA2_PF_PROOF_3: discharge the sub-iter-3 `pshuf3 = pf_target_3` subgoal. *)
let ETA2_PF_PROOF_3 : tactic = mk_eta2_pf_proof `pshuf3:int256` `tab3:int256`;;

(* ACC2_IDENT_TAC.  acc2 = acc1 + LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16i+4,4)));
   needs acc1_ident (LENGTH REJ_SAMPLE form) + acc2 ABBREV def in asl.  Proves &
   ASSUMEs LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16i+8)))=acc2. *)
let ACC2_IDENT_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let acc1_ident = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA2_BYTES",_),_))),Var("acc1",_))->true|_->false) asms in
    let acc2_def = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),Var("acc2",_))->true|_->false) asms in
    let split = REWRITE_RULE[ADD_CLAUSES; ARITH_RULE `(16*i+4)+4 = 16*i+8`] (ISPECL[`inlist:byte list`;`16*i+4`;`4`;`0`] SUB_LIST_SPLIT) in
    let step1 = (REWRITE_CONV[LENGTH_REJ_SAMPLE_ETA2_BYTES] THENC ONCE_DEPTH_CONV(REWR_CONV split) THENC REWRITE_CONV[REJ_NIBBLES_ETA2_APPEND; LENGTH_APPEND])
                  `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)` in
    let acc1_nib = REWRITE_RULE[LENGTH_REJ_SAMPLE_ETA2_BYTES] acc1_ident in
    let final = TRANS step1 (TRANS (AP_THM (AP_TERM `(+):num->num->num` acc1_nib) `LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16*i+4,4) inlist):int16 list)`) acc2_def) in
    ASSUME_TAC final);;

(* ========================================================================= *)
(* eta2 CORRECT: the SI3 store fold.                                         *)
(*                                                                           *)
(* The sub-iter-3 analogue of ETA2_SI2_FOLD.  Runs AFTER ETA2_SI2_COUNTER_TAC, *)
(* which leaves s41 (RIP=pc+273 = SI3 entry), R8 s41 = mask8b>>8 (= mask8c,  *)
(* byte 2 of the packed sum), RAX s41 = word(acc1 + block1len) [ALREADY folded *)
(* by the SI2 counter], and the running-prefix store fact folded to          *)
(* SUB_LIST(0,16i+8).  It advances the SIMD store for block2 (chunk0 lanes   *)
(* 64/72/80/88) and folds the prefix to SUB_LIST(0,16i+12).                  *)
(*                                                                           *)
(* eta2 SI3 step map:                                                        *)
(*   s42 vextracti128 $1 xmm8 (0x115) -> XMM8 (HIGH-128 of f0sub, EXPANDED), *)
(*       RIP s42 = pc+279                                                    *)
(*   s43 movzbl r8b -> r10d (shim; MOVZBL_R10_CAPTURE_TAC)                   *)
(*   s44 vmovq (rdx,r10,8) -> YMM9 (ETA2_TAB3_TEQ_TAC)                       *)
(*   s45 vpshufb -> YMM9 (pshuf3)                                            *)
(*   s46 vpmovsxbd -> YMM1 (sx3)                                             *)
(*   s47 vpmulhrsw / s48 vpmullw / s49 vpaddd — the mod-5 reduction          *)
(*   s50 vmovdqu STORE to word_add res (word (4 * acc2))                     *)
(*                                                                           *)
(* Differences vs the SI2 fold: opener is vextracti128 $1 (not vpsrldq),     *)
(* extracting the HIGH 128 of f0sub -> gather source g3 = word_zx(word_zx    *)
(* (word_subword f0sub (128,128))) (NO >>64 shift), so the bg3 gather forall is *)
(* used DIRECTLY (no WORD_ZX_TRIVIAL massage); acc1->acc2 base; block1->block2 *)
(* (chunk0 lanes 64-88, `el 2` of SUBITER_BLOCK_BYTES); mask8b->mask8c;      *)
(* prefix SUB_LIST(0,16i+8) -> SUB_LIST(0,16i+12).  RAX is already folded by the *)
(* SI2 counter, so SI3_PRE only abbrevs acc2 + reabbrevs mask8c + bounds.    *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* SI3_PRE: abbrev acc2, reabbrev mask8c, bounds acc2<=248, VAL_INT64.  eta2's
   SI2 counter ALREADY folded RAX to word(acc1+block1len), so the acc2 ABBREV
   makes RAX = word acc2 directly (no pop_len/rax_red RULE_ASSUM). *)
let ETA2_SI3_PRE_TAC : tactic =
  ABBREV_TAC `acc2 = acc1 + LENGTH (REJ_NIBBLES_ETA2 (SUB_LIST (16*i+4,4) inlist):int16 list)` THEN
  REABBREV_TAC `mask8c = read R8 s41` THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
    let i116 = find_a (fun th -> concl th = `16 * (i + 1) <= 136`) in
    let nibbnd = find_a (fun th -> concl th = `LENGTH (REJ_NIBBLES_ETA2 (SUB_LIST (0,16 * (i + 1)) inlist):int16 list) <= 248`) in
    let a1 = MP (MP (ARITH_RULE `16*(i+1)<=136 ==> (LENGTH(inlist:byte list)=136 ==> 16*(i+1)<=LENGTH inlist)`) i116) leninl in
    let bnd3 = MP (ISPECL[`inlist:byte list`;`i:num`] SUBITER_OUTLEN_BOUND_3) (CONJ a1 nibbnd) in
    let outlen0_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) in
    let acc1_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),Var("acc1",_)) -> true | _ -> false) in
    let acc2_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),Var("acc2",_)) -> true | _ -> false) in
    let bnd3a = REWRITE_RULE[outlen0_def; ADD_ASSOC] bnd3 in
    let bnd3b = REWRITE_RULE[acc1_def] bnd3a in
    let bnd3c = REWRITE_RULE[acc2_def] (REWRITE_RULE[ADD_ASSOC] bnd3b) in
    ASSUME_TAC bnd3c THEN
    ASSUME_TAC (MATCH_MP (ARITH_RULE `acc2 + x <= 248 ==> acc2 <= 248`) bnd3c)) THEN
  VAL_INT64_TAC `acc2:num`;;

(* Setup + step s42..s50 (raw store, sx3 opaque).  From s41 (post-SI2-counter). *)
let ETA2_SI3_STEP_TO_STORE_TAC : tactic =
  ETA2_SI3_PRE_TAC THEN
  ACC2_IDENT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) = acc2`]) THEN
  (* s42 vextracti128 $1 -> XMM8 (HIGH-128 of EXPANDED f0sub); re-fold f0sub. *)
  X86_VSTEPS_TAC EXEC (42--42) THEN
  W(fun (asl,w) ->
     let f0d = find (fun th -> is_eq(concl th) &&
        (lhand(concl th) = `f0sub:int256` || rand(concl th) = `f0sub:int256`) &&
        can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
     let f0fold = if rand(concl f0d) = `f0sub:int256` then f0d else SYM f0d in
     RULE_ASSUM_TAC(fun th -> if concl th = concl f0d then th else REWRITE_RULE[f0fold] th)) THEN
  X86_VERBOSE_STEP_TAC EXEC "s43" THEN MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s42 = mask8c:int64`]) THEN
  (SUBGOAL_THEN maskbit_tgt_3 ASSUME_TAC THENL [MASKBIT_TGT_3_TAC; ALL_TAC]) THEN
  X86_VSTEPS_TAC EXEC (44--44) THEN ETA2_TAB3_TEQ_TAC THEN
  REABBREV_TAC `tab3 = read YMM9 s44` THEN
  X86_VSTEPS_TAC EXEC (45--45) THEN REABBREV_TAC `pshuf3 = read YMM9 s45` THEN
  PURGE_STALE_STATES_TAC ["s44"] THEN
  X86_VSTEPS_TAC EXEC (46--46) THEN REABBREV_TAC `sx3 = read YMM1 s46` THEN
  PURGE_STALE_STATES_TAC ["s45"] THEN
  X86_VSTEPS_TAC EXEC (47--47) THEN X86_VSTEPS_TAC EXEC (48--48) THEN
  X86_VSTEPS_TAC EXEC (49--49) THEN
  PURGE_STALE_STATES_TAC ["s46";"s47";"s48"] THEN
  VAL_INT64_TAC `acc2:num` THEN
  X86_STEPS_TAC EXEC (50--50);;

(* Refold the s50 store fact (bytes256) to `usimd8 red_lane sx3`.            *)
let ETA2_STORE_REFOLD_3_TAC : tactic = mk_eta2_store_refold "s50" `sx3:int256`;;

(* sx3 clean form.                                                           *)
let ETA2_SX3_CLEAN_TAC : tactic = mk_eta2_sx_clean `sx3:int256` `pshuf3:int256`;;

(* PERF: fold expanded f0sub in the pshuf3 def, then discharge pf_target_3.  *)
let ETA2_ESTABLISH_PF_TARGET_3_TAC : tactic =
  mk_eta2_establish_pf_target `pshuf3:int256` pf_target_3 ETA2_PF_PROOF_3;;

(* The full SI3 store fold: from post-SI2-counter (s41) to the folded
   running-prefix store fact ASSUMEd at s50 (prefix SUB_LIST(0,16i+12)). *)
let ETA2_SI3_FOLD : tactic =
  ETA2_SI3_STEP_TO_STORE_TAC THEN
  ETA2_STORE_REFOLD_3_TAC THEN
  ETA2_SX3_CLEAN_TAC THEN
  ETA2_ESTABLISH_PF_TARGET_3_TAC THEN
  ACC2_IDENT_TAC THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
    let storerf = find (fun th -> is_eq(concl th) &&
         can(find_term(fun u->match u with Const("bytes256",_)->true|_->false)) (lhand(concl th)) &&
         can(find_term(fun u->match u with Const("red_lane",_)->true|_->false)) (rand(concl th)) &&
         not(can(find_term(fun u->match u with Const("word_mul",_)->true|_->false)) (rand(concl th)))) asms in
    let sx3clean = find (fun th -> is_eq(concl th) && lhand(concl th)=`sx3:int256` &&
         can(find_term(fun u->match u with Const("usimd8",_)->true|_->false)) (rand(concl th))) asms in
    let pfth = find (fun th -> concl th = pf_target_3) asms in
    (* the HIGH-128 gather forall (bg3): f0sub, chunk0 lane 64, NO word_ushr, has f0sub (128,128) *)
    let bg = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f0sub:int256`))c &&
        not(can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))c) &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (64,8):byte`))c &&
        can(find_term(fun u->u=`word_subword (f0sub:int256) (128,128):int128`))c) asms in
    let mthm = find (fun th -> concl th = maskbit_tgt_3) asms in
    let store_full = REWRITE_RULE[pfth] (REWRITE_RULE[sx3clean] storerf) in
    let g3 = `word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128` in
    let m = `word (val (mask8c:int64) MOD 256):byte` in
    let pc = ISPECL [`word_add res (word (4 * acc2)):int64`; `s50:x86state`; g3; m;
                     `LENGTH(ACC_IDX (word (val (mask8c:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND_RL in
    let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
    let spec = ISPECL [g3; m; `word_subword (chunk0:int128) (64,8):byte`;
        `word_subword (chunk0:int128) (72,8):byte`; `word_subword (chunk0:int128) (80,8):byte`;
        `word_subword (chunk0:int128) (88,8):byte`] SUBITER_STORE_SPEC in
    let specres = MP spec (CONJ mthm bg) in
    let rej_store = REWRITE_RULE[specres] res_th0 in
    (* block2 bytes (el 2), fold onto the running prefix SUB_LIST(0,16i+8) -> SUB_LIST(0,16i+12) *)
    let leninl = find (fun th -> match concl th with
         Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Var("inlist",_))),_) -> true | _ -> false) asms in
    let i116 = find (fun th -> match concl th with
         Comb(Comb(Const("<=",_),Comb(Comb(Const("*",_),_),Comb(Comb(Const("+",_),Var("i",_)),_))),_) -> true | _ -> false) asms in
    let blk16 = find (fun th -> is_eq(concl th) && hasC "SUB_LIST" th &&
         (try length(dest_list(rand(concl th))) = 16 with _ -> false)) asms in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*(i+1)<=136 ==> 16*i+16<=136`) i116)) blk16) in
    let blk2_eq = el 2 (CONJUNCTS bb) in    (* SUB_LIST(16i+8,4) = [lanes 64,72,80,88] *)
    let lr0 = MP (ISPECL [m;`word_subword (chunk0:int128) (64,8):byte`;`word_subword (chunk0:int128) (72,8):byte`;
        `word_subword (chunk0:int128) (80,8):byte`;`word_subword (chunk0:int128) (88,8):byte`] LEN_RECONCILE_GEN) mthm in
    let lr = REWRITE_RULE[GSYM blk2_eq] lr0 in
    let rej_store1 = REWRITE_RULE[GSYM blk2_eq] rej_store in
    let acc2_ident = find (fun th -> match concl th with
         Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA2_BYTES",_),_))),Var("acc2",_)) -> true | _ -> false) asms in
    let prefix_store0 = find (fun th -> (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s50",_))),_) -> true | _ -> false) &&
         hasC "num_of_wordlist" th && hasC "SUB_LIST" th && can(find_term(fun u->u=`acc2:num`))(lhand(concl th)) &&
         not(hasC "ACC_IDX" th) && not(hasC "bytes256" th)) asms in
    let prefix_store = REWRITE_RULE[GSYM acc2_ident] prefix_store0 in
    let rej_store2 = REWRITE_RULE[GSYM acc2_ident] rej_store1 in
    let fold = MP (ISPECL [`res:int64`;`s50:x86state`;m;`SUB_LIST(16*i+8,4) (inlist:byte list)`;`SUB_LIST(0,16*i+8) (inlist:byte list)`] SUBITER_FOLD_STEP)
                  (CONJ lr (CONJ prefix_store rej_store2)) in
    let split = REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i+8`;`4`;`0`] SUB_LIST_SPLIT) in
    let clean = REWRITE_RULE[GSYM split; ARITH_RULE `(16*i+8)+4 = 16*i+12`] fold in
    ASSUME_TAC clean);;

(* ========================================================================= *)
(* eta2 CORRECT: the SI3 counter+branch block (s51-56).                      *)
(*                                                                           *)
(* The sub-iter-3 analogue of ETA2_SI2_COUNTER_TAC.  Runs AFTER ETA2_SI3_FOLD, *)
(* which leaves s50 (running prefix store folded to SUB_LIST(0,16i+12), mask8c *)
(* + acc2 abbreviated, maskbit_tgt_3 ASSUMEd).  It advances RAX (acc2 -> acc2 + *)
(* block2len), RCX (16i+8 -> 16i+12), R8 (mask8c -> mask8c>>8 = mask8d), and *)
(* resolves the mid-iteration ja to the SI4 entry.                           *)
(*                                                                           *)
(* Control flow:                                                             *)
(*   s51 popcnt %r10d,%r9d ; s52 add %r9d,%eax ; s53 shr $0x8,%r8d ;         *)
(*   s54 add $0x4,%ecx (RIP s54 = pc+332) ; s55 cmp $0xf8,%eax ; s56 ja scalar *)
(*   -> RIP s56 = if <ja> then pc+399 else pc+339  (fall-through = SI4 entry; *)
(*      SI4 opener raw 0x157 = vpsrldq $8 %xmm8 = tmc pc+339).               *)
(*   RAX s54 = word_zx(word_add(word_zx(word acc2))(word_zx^2(word(word_popcount *)
(*     (word_zx^3(word(val mask8c MOD 256))))))) ; R8 s54 = mask8c>>8.       *)
(*                                                                           *)
(* Uses POPCNT_BYTE2 (byte 2 of the packed 32-bit popcount sum = f1bnd lanes *)
(* 16-23), the mb3 f1bnd-lane maskbit forall (`8*(k+16)`), SUBITER_OUTLEN_   *)
(* BOUND_3 (rewritten to acc2 base), and zxbyte_eq for the RAX-fold type bridge. *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* SI3_MG: build pop_len3 (popcount = block2len), bnd3c (acc2+block2len<=248),
   rax_red0 (RAX collapse), ja (JA_NOT_TAKEN). *)
let ETA2_SI3_MG_TAC : tactic =
  X86_STEPS_TAC EXEC (51--54) THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let m8c_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8c:int64` | _ -> false) in
    let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
    let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
    (* BOTH defs: mask8c = mask8b>>8, so folding the SUM32 needs m8b_def first
       (SUM32 -> mask8b) then m8c_def (mask8b>>8 -> mask8c).  Using only m8c_def
       leaves the popcount over the expanded SUM32. *)
    let popcnt3 = REWRITE_RULE[m8b_def; m8c_def]
       (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE2)) in
    let lanesum8 = rand(concl popcnt3) in
    (* the f1bnd-lane maskbit forall for lanes 16-23 (the `8*(k+16)` one)    *)
    let mb3 = find_a (fun th -> let c=concl th in is_forall c &&
       can(find_term(fun u->u=`f1bnd:int256`))c &&
       can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),c) -> c=`16` | _ -> false))c) in
    let mb3_tm = concl mb3 in
    let i_le = find_a (fun th -> concl th = `16 * i <= 120`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
    let blk16 = find_a (fun th -> is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" &&
            length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=120 ==> 16*i+16<=136`) i_le))
                      blk16) in
    let blk2_eq = el 2 (CONJUNCTS bb) in
    let block2 = `[word_subword (chunk0:int128) (64,8); word_subword chunk0 (72,8);
                   word_subword chunk0 (80,8); word_subword chunk0 (88,8)]:byte list` in
    let block2len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA2`, block2)) in
    let bsum3_raw = prove(mk_imp(mb3_tm, mk_eq(lanesum8, block2len_x)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV)
            (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER_ETA2] THEN
      SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let pop_len3 = REWRITE_RULE[GSYM blk2_eq] (TRANS popcnt3 (MP bsum3_raw mb3)) in
    (* bound: acc2 + block2len <= 248, via SUBITER_OUTLEN_BOUND_3 rewritten to acc2 *)
    let i116 = find_a (fun th -> concl th = `16 * (i + 1) <= 136`) in
    let nibbnd = find_a (fun th -> concl th = `LENGTH (REJ_NIBBLES_ETA2 (SUB_LIST (0,16 * (i + 1)) inlist):int16 list) <= 248`) in
    let a1 = MP (MP (ARITH_RULE `16*(i+1)<=136 ==> (LENGTH(inlist:byte list)=136 ==> 16*(i+1)<=LENGTH inlist)`) i116) leninl in
    let bnd3 = MP (ISPECL[`inlist:byte list`;`i:num`] SUBITER_OUTLEN_BOUND_3) (CONJ a1 nibbnd) in
    let outlen0_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) in
    let acc1_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),Var("acc1",_)) -> true | _ -> false) in
    let acc2_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),Var("acc2",_)) -> true | _ -> false) in
    let bnd3a = REWRITE_RULE[outlen0_def; ADD_ASSOC] bnd3 in
    let bnd3b = REWRITE_RULE[acc1_def] bnd3a in
    let bnd3c = REWRITE_RULE[acc2_def] (REWRITE_RULE[ADD_ASSOC] bnd3b) in  (* acc2 + block2len <= 248 *)
    let block2len = `LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i+8,4) inlist):int16 list)` in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd3c in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let ja = MP (ISPECL[mk_binop `(+):num->num->num` `acc2:num` block2len; `248`] JA_NOT_TAKEN_LE)
                (CONJ bnd3c (ARITH_RULE `248 < 2 EXP 32`)) in
    ASSUME_TAC pop_len3 THEN ASSUME_TAC bnd3c THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja);;

(* SI3_RESOLVE (zxbyte_eq bridge): step s55-56, resolve RIP s56 = pc+339.  The
   COND's popcount arg is byte-zx-typed (byte->i32->i64->i32) while pop_len3
   (POPCNT_BYTE2) is all-int32 — they print identically but aconv=false, so we
   MUST bridge via zbe before REWRITE (as SI2 does), else REFL_TAC fails.
   Disambiguate pop_len3 (mask8c / SUB_LIST(16i+8,4)) from the leftover
   SI2 pop_len2 (mask8b / SUB_LIST(16i+4,4)) via the SUB_LIST(16i+8,4) marker. *)
let ETA2_SI3_RESOLVE_TAC : tactic =
  X86_STEPS_TAC EXEC (55--56) THEN
  SUBGOAL_THEN `read RIP s56 = word (pc + 339):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let asms = map snd asl in
      let find_a p = find p asms in
      (* The counter step already folded popcnt->LENGTH(REJ_NIBBLES[EXPLICIT block2]) into the
         COND (not SUB_LIST); convert explicit block2 -> SUB_LIST(16i+8,4) via GSYM blk2_eq so
         rax_red0/ja match. *)
      let i_le = find_a (fun th -> concl th = `16 * i <= 120`) in
      let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
      let blk16 = find_a (fun th -> is_eq(concl th) &&
         (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
      let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                  (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=120 ==> 16*i+16<=136`) i_le)) blk16) in
      let blk2_eq = el 2 (CONJUNCTS bb) in
      let rax_red0 = find (fun th -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) ->
            can(find_term(fun u->u=`acc2:num`))(concl th) | _ -> false) asms in
      let ja = find (fun th -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`acc2:num`))(concl th)) asms in
      let ifrip = find (fun th -> match concl th with
         Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s56",_))),r) ->
           (match r with Comb(Comb(Comb(Const("COND",_),_),_),_) -> true | _ -> false) | _ -> false) asms in
      MP_TAC ifrip THEN REWRITE_TAC[GSYM blk2_eq] THEN REWRITE_TAC[rax_red0] THEN
      REWRITE_TAC[ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  (* fold RAX read clean: the RAX read carries popcnt folded to LENGTH(REJ_NIBBLES[EXPLICIT
     block2]); convert -> SUB_LIST(16i+8,4) via GSYM blk2_eq, then rax_red0 collapses it to
     word(acc2 + block2len).  (Same explicit->SUB_LIST issue as the RIP resolution.) *)
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let i_le = find_a (fun th -> concl th = `16 * i <= 120`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
    let blk16 = find_a (fun th -> is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=120 ==> 16*i+16<=136`) i_le)) blk16) in
    let blk2_eq = el 2 (CONJUNCTS bb) in
    let rr = find_a (fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) ->
          can(find_term(fun u->u=`acc2:num`))(concl th) | _ -> false) in
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM blk2_eq]) THEN RULE_ASSUM_TAC(REWRITE_RULE[rr])) THEN
  ALL_TAC;;

let ETA2_SI3_COUNTER_TAC : tactic =
  ETA2_SI3_MG_TAC THEN ETA2_SI3_RESOLVE_TAC;;

(* ========================================================================= *)
(* eta2 CORRECT: SI4 constant-independent gather substrate.                  *)
(*                                                                           *)
(* The sub-iter-4 analogues of the SI3 gather machinery.  All are            *)
(* constant-independent of the mod-5 reduction (they concern the vpshufb     *)
(* table gather and the vpmovmskb mask byte-3 popcount).  eta2 SI4 state     *)
(* indices: table-mem invariant at s58, vmovq YMM9 at s59.                   *)
(*                                                                           *)
(* Control flow (from the SI3-done state s56): SI4 opener s57 =              *)
(* vpsrldq $0x8,%xmm8 (raw 0x157 = tmc pc+339), RIP s56 = pc+339 (from SI3   *)
(* counter).  XMM8 s56 holds the HIGH-128 of f0sub (SI3 left the vextracti128 *)
(* $1 result in xmm8); vpsrldq $8 shifts it right 8 bytes, so the SI4 gather *)
(* source is g4 = the >>64 (high 64 bits) of that high-128 =                 *)
(* word_ushr(word_subword f0sub (128,128)) 64 — the SI2-style >>64 shift but *)
(* off the HIGH half.                                                        *)
(*   s58 movzbl r8b->r10d ; s59 vmovq (rdx,r10,8)->YMM9 ; s60 vpshufb ;      *)
(*   s61 vpmovsxbd ; s62-64 mod-5 reduction ; s65 store (0x17e) ;            *)
(*   s66-69 counter popcnt/add/add/JMP (NO shr/cmp/ja — SI4 has no mid-guard, *)
(*   flows unconditionally to loop top pc+86).                               *)
(*                                                                           *)
(* mask8d = R8 s56 = mask8c>>8 (byte 3 of the packed 32-bit popcount sum =   *)
(* f1bnd lanes 24-31 = block3 = chunk0 lanes 96-120).                        *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* DIVMOD16777216_SPLIT / R_EQ_D / RLT_D.                                    *)
let ETA2_TAB4_TEQ_TAC : tactic = ETA2_TAB_TEQ_GEN 58 59 `mask8d:int64` RLT_D R_EQ_D;;

(* ETA2_PF_PROOF_4: discharge the sub-iter-4 `pshuf4 = pf_target_4` subgoal. *)
let ETA2_PF_PROOF_4 : tactic = mk_eta2_pf_proof `pshuf4:int256` `tab4:int256`;;

(* ACC3_IDENT_TAC.  acc3 = acc2 + LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16i+8,4)));
   needs acc2_ident (LENGTH REJ_SAMPLE form) + acc3 ABBREV def in asl.  Proves &
   ASSUMEs LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16i+12)))=acc3. *)
let ACC3_IDENT_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let acc2_ident = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA2_BYTES",_),_))),Var("acc2",_))->true|_->false) asms in
    let acc3_def = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),Var("acc3",_))->true|_->false) asms in
    let split = REWRITE_RULE[ADD_CLAUSES; ARITH_RULE `(16*i+8)+4 = 16*i+12`] (ISPECL[`inlist:byte list`;`16*i+8`;`4`;`0`] SUB_LIST_SPLIT) in
    let step1 = (REWRITE_CONV[LENGTH_REJ_SAMPLE_ETA2_BYTES] THENC ONCE_DEPTH_CONV(REWR_CONV split) THENC REWRITE_CONV[REJ_NIBBLES_ETA2_APPEND; LENGTH_APPEND])
                  `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)` in
    let acc2_nib = REWRITE_RULE[LENGTH_REJ_SAMPLE_ETA2_BYTES] acc2_ident in
    let final = TRANS step1 (TRANS (AP_THM (AP_TERM `(+):num->num->num` acc2_nib) `LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16*i+8,4) inlist):int16 list)`) acc3_def) in
    ASSUME_TAC final);;

(* ========================================================================= *)
(* eta2 CORRECT: the SI4 store fold.                                         *)
(*                                                                           *)
(* The sub-iter-4 (LAST) analogue of ETA2_SI3_FOLD.  Runs AFTER              *)
(* ETA2_SI3_COUNTER_TAC, which leaves s56 (RIP=pc+339 = SI4 entry), R8 s56 = *)
(* mask8c>>8 (= mask8d, byte 3 of the packed sum), RAX s56 = word(acc2 +     *)
(* block2len) [ALREADY folded by the SI3 counter], and the running-prefix    *)
(* store fact folded to SUB_LIST(0,16i+12).  It advances the SIMD store for  *)
(* block3 (chunk0 lanes 96/104/112/120) and folds the prefix to              *)
(* SUB_LIST(0,16i+16) = SUB_LIST(0,16(i+1)).                                 *)
(*                                                                           *)
(* eta2 SI4 step map:                                                        *)
(*   s57 vpsrldq $0x8 xmm8 (0x157) -> XMM8, RIP s56 = pc+339                 *)
(*       (SI3 left the vextracti128 $1 HIGH-128 of f0sub in xmm8; vpsrldq $8 *)
(*        shifts it right 8 bytes -> gather source g4 = the >>64 (high 64) of *)
(*        that high-128 = word_ushr(word_subword f0sub (128,128)) 64; f0sub is *)
(*        EXPANDED on XMM8, must be RE-FOLDED like SI2/SI3 fold).            *)
(*   s58 movzbl r8b -> r10d (shim; MOVZBL_R10_CAPTURE_TAC)                   *)
(*   s59 vmovq (rdx,r10,8) -> YMM9 (ETA2_TAB4_TEQ_TAC)                       *)
(*   s60 vpshufb -> YMM9 (pshuf4)                                            *)
(*   s61 vpmovsxbd -> YMM1 (sx4)                                             *)
(*   s62 vpmulhrsw / s63 vpmullw / s64 vpaddd — the mod-5 reduction          *)
(*   s65 vmovdqu STORE (0x17e) to word_add res (word (4 * acc3))             *)
(*                                                                           *)
(* Differences vs the SI3 fold: opener is vpsrldq $8 (like SI2, NOT          *)
(* vextracti128 $1) extracting the >>64 of the HIGH 128 of f0sub -> gather   *)
(* source g4 has the word_ushr(...)64 shift (like SI2's g2, but off the HIGH *)
(* half); acc2->acc3 base; block2->block3 (chunk0 lanes 96-120, `el 3` of    *)
(* SUBITER_BLOCK_BYTES); mask8c->mask8d; prefix SUB_LIST(0,16i+12) ->        *)
(* SUB_LIST(0,16i+16).  RAX is already folded by the SI3 counter, so SI4_PRE *)
(* only abbrevs acc3 + reabbrevs mask8d + bounds.                            *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* SI4_PRE.  UNLIKE the SI2->SI3 boundary (where the SI2 counter pre-folds the
   RAX read), the SI3 counter leaves RAX at s56 as the RAW popcount nest
     word_zx(word_add(word_zx(word acc2))(word_zx^2(word(word_popcount(...mask8c...)))))
   and leaves pop_len3 (word_popcount(...mask8c...) = LENGTH(REJ_NIBBLES_ETA2
   (SUB_LIST(16i+8,4)))) in the asl, but NO standalone rax_red0 fact.  So we
   FIRST rewrite RAX with pop_len3 (popcount->block2len), then BUILD rax_red0 via
   RAX_NEST_REDUCE from the acc2+block2len<2^32 bound (rebuilt with SUBITER_OUTLEN_
   BOUND_3, as SI3_PRE does), then rewrite RAX -> word(acc2+block2len), THEN abbrev
   acc3.  This is the key SI4-vs-SI3 difference: SI3_PRE could skip the fold (SI2
   counter did it), SI4_PRE cannot. *)
let ETA2_SI4_PRE_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    (* pop_len3: identify via the mask8c popcount arg (SI3's; not the SI1/SI2 leftovers). *)
    let pop_len3 = find_a (fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) ->
          can(find_term(fun u->u=`mask8c:int64`))(concl th) | _ -> false) in
    (* rebuild acc2 + block2len <= 248 via SUBITER_OUTLEN_BOUND_3 (as SI3_PRE does),
       collapsing outlen0/acc1/acc2 defs so the bound reads over acc2. *)
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
    let i116 = find_a (fun th -> concl th = `16 * (i + 1) <= 136`) in
    let nibbnd = find_a (fun th -> concl th = `LENGTH (REJ_NIBBLES_ETA2 (SUB_LIST (0,16 * (i + 1)) inlist):int16 list) <= 248`) in
    let a1 = MP (MP (ARITH_RULE `16*(i+1)<=136 ==> (LENGTH(inlist:byte list)=136 ==> 16*(i+1)<=LENGTH inlist)`) i116) leninl in
    let bnd3 = MP (ISPECL[`inlist:byte list`;`i:num`] SUBITER_OUTLEN_BOUND_3) (CONJ a1 nibbnd) in
    let outlen0_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) in
    let acc1_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),Var("acc1",_)) -> true | _ -> false) in
    let acc2_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),Var("acc2",_)) -> true | _ -> false) in
    let bnd3a = REWRITE_RULE[outlen0_def; ADD_ASSOC] bnd3 in
    let bnd3b = REWRITE_RULE[acc1_def] bnd3a in
    let bnd3c = REWRITE_RULE[acc2_def] (REWRITE_RULE[ADD_ASSOC] bnd3b) in  (* acc2 + block2len <= 248 *)
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd3c in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    RULE_ASSUM_TAC(REWRITE_RULE[pop_len3]) THEN RULE_ASSUM_TAC(REWRITE_RULE[rax_red0])) THEN
  ABBREV_TAC `acc3 = acc2 + LENGTH (REJ_NIBBLES_ETA2 (SUB_LIST (16*i+8,4) inlist):int16 list)` THEN
  REABBREV_TAC `mask8d = read R8 s56` THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
    let i116 = find_a (fun th -> concl th = `16 * (i + 1) <= 136`) in
    let nibbnd = find_a (fun th -> concl th = `LENGTH (REJ_NIBBLES_ETA2 (SUB_LIST (0,16 * (i + 1)) inlist):int16 list) <= 248`) in
    let a1 = MP (MP (ARITH_RULE `16*(i+1)<=136 ==> (LENGTH(inlist:byte list)=136 ==> 16*(i+1)<=LENGTH inlist)`) i116) leninl in
    let bnd4 = MP (ISPECL[`inlist:byte list`;`i:num`] SUBITER_OUTLEN_BOUND_4) (CONJ a1 nibbnd) in
    let outlen0_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) in
    let acc1_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),Var("acc1",_)) -> true | _ -> false) in
    let acc2_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),Var("acc2",_)) -> true | _ -> false) in
    let acc3_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),Var("acc3",_)) -> true | _ -> false) in
    let bnd4a = REWRITE_RULE[outlen0_def; ADD_ASSOC] bnd4 in
    let bnd4b = REWRITE_RULE[acc1_def] bnd4a in
    let bnd4c = REWRITE_RULE[acc2_def] (REWRITE_RULE[ADD_ASSOC] bnd4b) in
    let bnd4d = REWRITE_RULE[acc3_def] (REWRITE_RULE[ADD_ASSOC] bnd4c) in
    ASSUME_TAC bnd4d THEN
    ASSUME_TAC (MATCH_MP (ARITH_RULE `acc3 + x <= 248 ==> acc3 <= 248`) bnd4d)) THEN
  VAL_INT64_TAC `acc3:num`;;

(* Setup + step s57..s65 (raw store, sx4 opaque).  From s56 (post-SI3-counter). *)
let ETA2_SI4_STEP_TO_STORE_TAC : tactic =
  ETA2_SI4_PRE_TAC THEN
  ACC3_IDENT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) = acc3`]) THEN
  (* s57 vpsrldq $8 -> XMM8 (>>64 of the HIGH-128 of EXPANDED f0sub); re-fold f0sub. *)
  X86_VSTEPS_TAC EXEC (57--57) THEN
  W(fun (asl,w) ->
     let f0d = find (fun th -> is_eq(concl th) &&
        (lhand(concl th) = `f0sub:int256` || rand(concl th) = `f0sub:int256`) &&
        can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
     let f0fold = if rand(concl f0d) = `f0sub:int256` then f0d else SYM f0d in
     RULE_ASSUM_TAC(fun th -> if concl th = concl f0d then th else REWRITE_RULE[f0fold] th)) THEN
  X86_VERBOSE_STEP_TAC EXEC "s58" THEN MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s57 = mask8d:int64`]) THEN
  (SUBGOAL_THEN maskbit_tgt_4 ASSUME_TAC THENL [MASKBIT_TGT_4_TAC; ALL_TAC]) THEN
  X86_VSTEPS_TAC EXEC (59--59) THEN ETA2_TAB4_TEQ_TAC THEN
  REABBREV_TAC `tab4 = read YMM9 s59` THEN
  X86_VSTEPS_TAC EXEC (60--60) THEN REABBREV_TAC `pshuf4 = read YMM9 s60` THEN
  PURGE_STALE_STATES_TAC ["s59"] THEN
  X86_VSTEPS_TAC EXEC (61--61) THEN REABBREV_TAC `sx4 = read YMM1 s61` THEN
  PURGE_STALE_STATES_TAC ["s60"] THEN
  X86_VSTEPS_TAC EXEC (62--62) THEN X86_VSTEPS_TAC EXEC (63--63) THEN
  X86_VSTEPS_TAC EXEC (64--64) THEN
  PURGE_STALE_STATES_TAC ["s61";"s62";"s63"] THEN
  VAL_INT64_TAC `acc3:num` THEN
  X86_STEPS_TAC EXEC (65--65);;

(* Refold the s65 store fact (bytes256) to `usimd8 red_lane sx4`.            *)
let ETA2_STORE_REFOLD_4_TAC : tactic = mk_eta2_store_refold "s65" `sx4:int256`;;

(* sx4 clean form.                                                           *)
let ETA2_SX4_CLEAN_TAC : tactic = mk_eta2_sx_clean `sx4:int256` `pshuf4:int256`;;

(* PERF: fold expanded f0sub in the pshuf4 def, then discharge pf_target_4.  *)
let ETA2_ESTABLISH_PF_TARGET_4_TAC : tactic =
  mk_eta2_establish_pf_target `pshuf4:int256` pf_target_4 ETA2_PF_PROOF_4;;

(* The full SI4 store fold: from post-SI3-counter (s56) to the folded
   running-prefix store fact ASSUMEd at s65 (prefix SUB_LIST(0,16i+16)). *)
let ETA2_SI4_FOLD : tactic =
  ETA2_SI4_STEP_TO_STORE_TAC THEN
  ETA2_STORE_REFOLD_4_TAC THEN
  ETA2_SX4_CLEAN_TAC THEN
  ETA2_ESTABLISH_PF_TARGET_4_TAC THEN
  ACC3_IDENT_TAC THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
    let storerf = find (fun th -> is_eq(concl th) &&
         can(find_term(fun u->match u with Const("bytes256",_)->true|_->false)) (lhand(concl th)) &&
         can(find_term(fun u->match u with Const("red_lane",_)->true|_->false)) (rand(concl th)) &&
         not(can(find_term(fun u->match u with Const("word_mul",_)->true|_->false)) (rand(concl th)))) asms in
    let sx4clean = find (fun th -> is_eq(concl th) && lhand(concl th)=`sx4:int256` &&
         can(find_term(fun u->match u with Const("usimd8",_)->true|_->false)) (rand(concl th))) asms in
    let pfth = find (fun th -> concl th = pf_target_4) asms in
    (* the >>64-shifted HIGH-128 gather forall (bg4): f0sub, chunk0 lane 96, HAS word_ushr,
       has f0sub (128,128) *)
    let bg = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f0sub:int256`))c &&
        can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (96,8):byte`))c &&
        can(find_term(fun u->u=`word_subword (f0sub:int256) (128,128):int128`))c) asms in
    let mthm = find (fun th -> concl th = maskbit_tgt_4) asms in
    let store_full = REWRITE_RULE[pfth] (REWRITE_RULE[sx4clean] storerf) in
    let g4 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128) 64):int128):int128` in
    let m = `word (val (mask8d:int64) MOD 256):byte` in
    let pc = ISPECL [`word_add res (word (4 * acc3)):int64`; `s65:x86state`; g4; m;
                     `LENGTH(ACC_IDX (word (val (mask8d:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND_RL in
    let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
    let spec = ISPECL [g4; m; `word_subword (chunk0:int128) (96,8):byte`;
        `word_subword (chunk0:int128) (104,8):byte`; `word_subword (chunk0:int128) (112,8):byte`;
        `word_subword (chunk0:int128) (120,8):byte`] SUBITER_STORE_SPEC in
    let specres = MP spec (CONJ mthm bg) in
    let rej_store = REWRITE_RULE[specres] res_th0 in
    (* block3 bytes (el 3), fold onto the running prefix SUB_LIST(0,16i+12) -> SUB_LIST(0,16i+16) *)
    let leninl = find (fun th -> match concl th with
         Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Var("inlist",_))),_) -> true | _ -> false) asms in
    let i116 = find (fun th -> match concl th with
         Comb(Comb(Const("<=",_),Comb(Comb(Const("*",_),_),Comb(Comb(Const("+",_),Var("i",_)),_))),_) -> true | _ -> false) asms in
    let blk16 = find (fun th -> is_eq(concl th) && hasC "SUB_LIST" th &&
         (try length(dest_list(rand(concl th))) = 16 with _ -> false)) asms in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*(i+1)<=136 ==> 16*i+16<=136`) i116)) blk16) in
    let blk3_eq = el 3 (CONJUNCTS bb) in    (* SUB_LIST(16i+12,4) = [lanes 96,104,112,120] *)
    let lr0 = MP (ISPECL [m;`word_subword (chunk0:int128) (96,8):byte`;`word_subword (chunk0:int128) (104,8):byte`;
        `word_subword (chunk0:int128) (112,8):byte`;`word_subword (chunk0:int128) (120,8):byte`] LEN_RECONCILE_GEN) mthm in
    let lr = REWRITE_RULE[GSYM blk3_eq] lr0 in
    let rej_store1 = REWRITE_RULE[GSYM blk3_eq] rej_store in
    let acc3_ident = find (fun th -> match concl th with
         Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA2_BYTES",_),_))),Var("acc3",_)) -> true | _ -> false) asms in
    let prefix_store0 = find (fun th -> (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s65",_))),_) -> true | _ -> false) &&
         hasC "num_of_wordlist" th && hasC "SUB_LIST" th && can(find_term(fun u->u=`acc3:num`))(lhand(concl th)) &&
         not(hasC "ACC_IDX" th) && not(hasC "bytes256" th)) asms in
    let prefix_store = REWRITE_RULE[GSYM acc3_ident] prefix_store0 in
    let rej_store2 = REWRITE_RULE[GSYM acc3_ident] rej_store1 in
    let fold = MP (ISPECL [`res:int64`;`s65:x86state`;m;`SUB_LIST(16*i+12,4) (inlist:byte list)`;`SUB_LIST(0,16*i+12) (inlist:byte list)`] SUBITER_FOLD_STEP)
                  (CONJ lr (CONJ prefix_store rej_store2)) in
    let split = REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i+12`;`4`;`0`] SUB_LIST_SPLIT) in
    let clean = REWRITE_RULE[GSYM split; ARITH_RULE `(16*i+12)+4 = 16*i+16`] fold in
    ASSUME_TAC clean);;

(* ========================================================================= *)
(* eta2 CORRECT: SI4 counter + finals.                                       *)
(*                                                                           *)
(* The LAST piece of the CLEAN_BODY body port.  Runs AFTER ETA2_SI4_FOLD,    *)
(* which leaves s65 (store folded to SUB_LIST(0,16i+16) = SUB_LIST(0,16(i+1))), *)
(* RAX s65 = word acc3, R8 s65 = mask8d).                                    *)
(*                                                                           *)
(* Control flow:                                                             *)
(*   s66 popcnt %r10d,%r9d (0x183) ; s67 add %r9d,%eax (0x188) ;             *)
(*   s68 add $0x4,%ecx (0x18b) ; s69 jmp 5a (0x18e, UNCONDITIONAL to loop top *)
(*   pc+86).  The SI4 counter is SIMPLER than SI1-3: only 4 steps, NO shr, NO *)
(*   cmp, NO conditional ja/mid-guard (SI4 is the last sub-iter — it always  *)
(*   loops back).  So the jmp lands RIP directly at pc+86; no COND to resolve. *)
(*                                                                           *)
(* We step s66-69 straight through, leaving RAX as the raw popcount nest     *)
(*   word_zx(word_add(word_zx(word acc3))(word_zx^2(word(word_popcount(...))))) *)
(* and RCX = word_zx(word_add(word_zx(word(16*i+12)))(word_zx(word 4))).  The *)
(* RAX/RCX collapse to the CLEAN_BODY postcondition forms is deferred to     *)
(* ETA2_RAX_FINAL_TAC / ETA2_RCX_FINAL_TAC (which run after                  *)
(* ENSURES_FINAL_STATE_TAC).                                                 *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* SI4 counter: step s66-69 (popcnt/add/add/jmp).  jmp is unconditional so RIP
   lands at pc+86 (loop top) directly.  Leaves RAX/RCX as raw stepper nests for
   the finals to collapse. *)
let ETA2_SI4_COUNTER_TAC : tactic =
  X86_STEPS_TAC EXEC (66--69);;

(* ACC_FULL_LEN: the 5-term niblen sum (prefix + 4 sub-iter blocks) telescopes *)
(* to niblen(16*(i+1)).                                                      *)
let ACC_FULL_LEN = prove
 (`!inlist:byte list. !i:num. 16*i+16 <= LENGTH inlist ==>
     LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(0,16*i) inlist):int16 list) +
     LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16*i,4) inlist):int16 list) +
     LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16*i+4,4) inlist):int16 list) +
     LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16*i+8,4) inlist):int16 list) +
     LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(16*i+12,4) inlist):int16 list) =
     LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(0,16*(i+1)) inlist):int16 list)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `16*(i+1) = 16*i+16`] THEN
  ONCE_REWRITE_TAC[ISPECL[`inlist:byte list`;`16*i`;`16`;`0`] SUB_LIST_SPLIT] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[SL16_4WAY] THEN
  REWRITE_TAC[REJ_NIBBLES_ETA2_APPEND; LENGTH_APPEND] THEN ARITH_TAC);;

(* ETA2_RAX_FINAL_TAC: discharge the RAX final-state subgoal (goal 0):
   word_zx(word_add(word_zx(word acc3))(word_zx^2(word(word_popcount(mask8d-arg))))) =
     word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16(i+1))))). *)
let ETA2_RAX_FINAL_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let m8c_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8c:int64` | _ -> false) in
    let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
    let m8d_val = find_a (fun th -> match concl th with
        Comb(Comb(Const("=",_),_),r) -> r = `mask8d:int64` &&
          can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))(concl th) | _ -> false) in
    let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
    (* popcnt4: fold SUM->mask8b->mask8c (forward), then mask8c-ushr-form -> mask8d via m8d_val *)
    let popcnt4 = REWRITE_RULE[m8d_val] (REWRITE_RULE[m8b_def; m8c_def]
       (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE3))) in
    let lanesum = rand(concl popcnt4) in
    (* lanes-24..31 maskbit                                                  *)
    let mb4 = find_a (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f1bnd:int256`))c &&
       can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),n) -> n=`24` | _ -> false))c) in
    let mb4_tm = concl mb4 in
    let i_le = find_a (fun th -> concl th = `16 * i <= 120`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
    let blk16 = find_a (fun th -> is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=120 ==> 16*i+16<=136`) i_le)) blk16) in
    let blk3_eq = el 3 (CONJUNCTS bb) in   (* SUB_LIST(16*i+12,4) = [chunk0 96,104,112,120] *)
    let block3 = `[word_subword (chunk0:int128) (96,8); word_subword chunk0 (104,8);
                   word_subword chunk0 (112,8); word_subword chunk0 (120,8)]:byte list` in
    let block3len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA2`, block3)) in
    let bsum4_raw = prove(mk_imp(mb4_tm, mk_eq(lanesum, block3len_x)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV)
            (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER_ETA2] THEN
      SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let pop_len4 = REWRITE_RULE[GSYM blk3_eq] (TRANS popcnt4 (MP bsum4_raw mb4)) in
    (* bound acc3 + block3len < 2^32                                         *)
    let bnd4d = find_a (fun th -> match concl th with
       Comb(Comb(Const("<=",_),Comb(Comb(Const("+",_),Var("acc3",_)),_)),_) -> true | _ -> false) in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd4d in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    (* rewrite goal: popcnt -> block3len, then rax_red0 -> word(acc3+block3len) *)
    REWRITE_TAC[pop_len4] THEN REWRITE_TAC[rax_red0]) THEN
  (* now goal: word(acc3 + block3len) = word(LENGTH(REJ_SAMPLE(SUB_LIST(0,16(i+1))))) *)
  AP_TERM_TAC THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let outlen0_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) in
    let acc1_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),Var("acc1",_)) -> true | _ -> false) in
    let acc2_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),Var("acc2",_)) -> true | _ -> false) in
    let acc3_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),Var("acc3",_)) -> true | _ -> false) in
    let i_le = find_a (fun th -> concl th = `16 * i <= 120`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
    let af = MP (ISPECL [`inlist:byte list`; `i:num`] ACC_FULL_LEN)
                (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=120 ==> 16*i+16<=136`) i_le)) in
    REWRITE_TAC[SYM acc3_def; SYM acc2_def; SYM acc1_def] THEN
    REWRITE_TAC[SYM outlen0_def] THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN
    MP_TAC af THEN ARITH_TAC);;

(* RCX final helpers.                                                        *)
let ETA2_RCX_FINAL_TAC : tactic =
  SUBGOAL_THEN `16 * (i + 1) = 16 * i + 4 + 4 + 4 + 4` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[MM64_32] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[MM_4G_4G; MM_4G_18] THEN
  SUBGOAL_THEN `16 * i < 4294967296 /\ 16*i+4 < 4294967296 /\ 16*i+4+4 < 4294967296 /\
                16*i+4+4+4 < 4294967296 /\ 16*i+16 < 18446744073709551616 /\
                (16*i+4)+4 < 4294967296 /\ ((16*i+4)+4)+4 < 4294967296 /\ (((16*i+4)+4)+4)+4 < 4294967296`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN UNDISCH_TAC `16 * (i + 1) <= 136` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;;

(* ========================================================================= *)
(* eta2 CORRECT: assemble CLEAN_BODY_FULL_TAC + prove CLEAN_BODY.            *)
(*                                                                           *)
(* Composes the full body proof from the per-sub-iter tactics:               *)
(* ETA2_PREFIX_TO_S11_TAC                                                    *)
(* SI1: ETA2_SI1_FOLD + ETA2_SI1_COUNTER_TAC                                 *)
(* SI2: ETA2_SI2_FOLD + ETA2_SI2_COUNTER_TAC                                 *)
(* SI3: ETA2_SI3_FOLD + ETA2_SI3_COUNTER_TAC                                 *)
(* SI4: ETA2_SI4_FOLD + ETA2_SI4_COUNTER_TAC                                 *)
(*   finals: ENSURES_FINAL_STATE + ETA2_RAX_FINAL_TAC / ETA2_RCX_FINAL_TAC.  *)
(*                                                                           *)
(* Each sub-iter is split into FOLD (gather+store) + COUNTER (advance/branch), *)
(* so we chain the 8 pieces explicitly.  SI4_COUNTER's jmp lands RIP at pc+86 *)
(* (loop top) so the postcondition RIP matches directly.                     *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

let ETA2_CLEAN_BODY_FULL_TAC : tactic =
  ETA2_PREFIX_TO_S11_TAC THEN
  ETA2_SI1_FOLD THEN ETA2_SI1_COUNTER_TAC THEN
  ETA2_SI2_FOLD THEN ETA2_SI2_COUNTER_TAC THEN
  ETA2_SI3_FOLD THEN ETA2_SI3_COUNTER_TAC THEN
  ETA2_SI4_FOLD THEN ETA2_SI4_COUNTER_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16*i+16 = 16*(i+1)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ETA2_RAX_FINAL_TAC; ETA2_RCX_FINAL_TAC];;

(* ========================================================================= *)
(* eta2 CORRECT: CLEAN_BLOCK.                                                *)
(*                                                                           *)
(* The SIMD 16-byte block body pc+86 -> pc+86, WITHOUT the `~(N=0)` and      *)
(* `i+1<N` hyps of clean_body_eta2_tm (the gather tactics never use them), and *)
(* with the relaxed bound `16*(i+1)<=136` (so it covers BOTH interior clean  *)
(* blocks AND the exit block at i=N-1 where 16*N=136).  Proved by the SAME   *)
(* ETA2_CLEAN_BODY_FULL_TAC.                                                 *)
(*                                                                           *)
(* This is the asset for the exit-block OFFSET arm: CLEAN_BLOCK @ i=N-1 takes *)
(* pc+86/pos=16(N-1) -> pc+86/pos=16N, then the head guard fires and control *)
(* drops to the scalar tail, handled by SCALAR_TAIL_AT_P@136.                *)
(* ========================================================================= *)

let clean_block_eta2_tm =
  let hs = conjuncts(fst(dest_imp(snd(strip_forall clean_body_eta2_tm)))) in
  let hs' = filter (fun h -> h <> `~(N = 0)` && h <> `i + 1 < N`) hs in
  list_mk_forall(fst(strip_forall clean_body_eta2_tm),
    mk_imp(list_mk_conj hs', snd(dest_imp(snd(strip_forall clean_body_eta2_tm)))));;

let ETA2_CLEAN_BLOCK = prove(clean_block_eta2_tm, ETA2_CLEAN_BODY_FULL_TAC);;

(* CLEAN_BODY is CLEAN_BLOCK with two EXTRA hypotheses (`~(N=0)`, `i+1<N`) and *)
(* an identical conclusion, so it follows by weakening — no re-simulation.    *)
let MLDSA_REJ_UNIFORM_ETA2_CLEAN_BODY = prove(clean_body_eta2_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC ETA2_CLEAN_BLOCK THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* eta2 CORRECT: scalar-tail spec/algebra lemmas.                            *)
(*                                                                           *)
(* The pure spec-level per-byte step lemmas that drive the byte-at-a-time    *)
(* scalar tail loop at pc+399 (0x193).  Each scalar iteration consumes 1     *)
(* input byte = 2 nibbles (low then high), accepting each if < 15, matching  *)
(* REJ_SAMPLE_ETA2_BYTES.  The eta2 coefficient is                           *)
(*   word_sx(word_sub (word 2:int16) (word_umod (word n) (word 5:int16))).   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Per-byte spec: REJ_SAMPLE_ETA2_BYTES [b] as an APPEND of the two          *)
(* nibble contributions.                                                     *)
(* ------------------------------------------------------------------------- *)
let REJ_SAMPLE_ETA2_BYTES_1 = prove
 (`!b:byte.
     REJ_SAMPLE_ETA2_BYTES [b] =
     APPEND
      (if val b MOD 16 < 15
       then [word_sx(word_sub (word 2:int16)
                              (word_umod (word(val b MOD 16)) (word 5:int16))):int32]
       else [])
      (if val b DIV 16 < 15
       then [word_sx(word_sub (word 2:int16)
                              (word_umod (word(val b DIV 16)) (word 5:int16))):int32]
       else [])`,
  GEN_TAC THEN
  REWRITE_TAC[REJ_SAMPLE_ETA2_BYTES; REJ_NIBBLES_ETA2;
              NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND; FILTER; MAP] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `val(b:byte) MOD 16 MOD 65536 = val b MOD 16 /\
    val(b:byte) DIV 16 MOD 65536 = val b DIV 16`
   (fun th -> REWRITE_TAC[th]) THENL
   [MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP; APPEND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP; APPEND]);;

(* ------------------------------------------------------------------------- *)
(* Per-byte length.                                                          *)
(* ------------------------------------------------------------------------- *)
let LENGTH_REJ_SAMPLE_ETA2_BYTES_1 = prove
 (`!b:byte. LENGTH(REJ_SAMPLE_ETA2_BYTES [b] :int32 list) =
            (if val b MOD 16 < 15 then 1 else 0) +
            (if val b DIV 16 < 15 then 1 else 0)`,
  GEN_TAC THEN REWRITE_TAC[REJ_SAMPLE_ETA2_BYTES_1; LENGTH_APPEND] THEN
  COND_CASES_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Per-byte case lemmas (one per acceptance combination).                    *)
(* ------------------------------------------------------------------------- *)
let REJ_SAMPLE_ETA2_BYTES_1_REJECT_BOTH = prove
 (`!b:byte. ~(val b MOD 16 < 15) /\ ~(val b DIV 16 < 15)
            ==> REJ_SAMPLE_ETA2_BYTES [b] = []`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REJ_SAMPLE_ETA2_BYTES_1; APPEND]);;

let REJ_SAMPLE_ETA2_BYTES_1_LOW_ONLY = prove
 (`!b:byte. val b MOD 16 < 15 /\ ~(val b DIV 16 < 15)
            ==> REJ_SAMPLE_ETA2_BYTES [b] =
                [word_sx(word_sub (word 2:int16)
                                  (word_umod (word(val b MOD 16)) (word 5:int16))):int32]`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REJ_SAMPLE_ETA2_BYTES_1; APPEND]);;

let REJ_SAMPLE_ETA2_BYTES_1_HIGH_ONLY = prove
 (`!b:byte. ~(val b MOD 16 < 15) /\ val b DIV 16 < 15
            ==> REJ_SAMPLE_ETA2_BYTES [b] =
                [word_sx(word_sub (word 2:int16)
                                  (word_umod (word(val b DIV 16)) (word 5:int16))):int32]`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REJ_SAMPLE_ETA2_BYTES_1; APPEND]);;

let REJ_SAMPLE_ETA2_BYTES_1_BOTH = prove
 (`!b:byte. val b MOD 16 < 15 /\ val b DIV 16 < 15
            ==> REJ_SAMPLE_ETA2_BYTES [b] =
                [word_sx(word_sub (word 2:int16)
                                  (word_umod (word(val b MOD 16)) (word 5:int16))):int32;
                 word_sx(word_sub (word 2:int16)
                                  (word_umod (word(val b DIV 16)) (word 5:int16))):int32]`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REJ_SAMPLE_ETA2_BYTES_1; APPEND]);;

(* ------------------------------------------------------------------------- *)
(* SUB_LIST prefix-extension step (arch-generic).                            *)
(* ------------------------------------------------------------------------- *)
let SUB_LIST_STEP_BYTE_ETA2 = prove
 (`!(l:byte list) (k:num).
     k < LENGTH l
     ==> SUB_LIST(0, k+1) l = APPEND (SUB_LIST(0, k) l) [EL k l]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:byte list`; `k:num`; `1`; `0`] SUB_LIST_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `0 + k = k`] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN ASM_REWRITE_TAC[SUB_LIST_1]);;

(* REJ prefix step: REJ(SUB(0,k+1)) = APPEND (REJ(SUB(0,k))) (REJ [EL k]).   *)
let REJ_SAMPLE_ETA2_BYTES_STEP_1 = prove
 (`!(l:byte list) (k:num).
     k < LENGTH l
     ==> REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, k+1) l) =
         APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, k) l))
                (REJ_SAMPLE_ETA2_BYTES [EL k l])`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SUB_LIST_STEP_BYTE_ETA2; REJ_SAMPLE_ETA2_BYTES_APPEND]);;

let LENGTH_REJ_SAMPLE_ETA2_BYTES_STEP_1 = prove
 (`!(inlist:byte list) k.
     k < LENGTH inlist
     ==> LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, k+1) inlist):int32 list) =
         LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, k) inlist):int32 list) +
         (if val(EL k inlist) MOD 16 < 15 then 1 else 0) +
         (if val(EL k inlist) DIV 16 < 15 then 1 else 0)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REJ_SAMPLE_ETA2_BYTES_STEP_1; LENGTH_APPEND;
               LENGTH_REJ_SAMPLE_ETA2_BYTES_1] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Per-byte length step lemmas (drive the RAX update; grow by 0/1/2).        *)
(* ------------------------------------------------------------------------- *)
let LEN_STEP_BOTH_ETA2 = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ val(EL p inlist) MOD 16 < 15 /\ val(EL p inlist) DIV 16 < 15
   ==> LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+1) inlist):int32 list) =
       LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) + 2`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_ETA2_BYTES_STEP_1) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;
let LEN_STEP_LO_ETA2 = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ val(EL p inlist) MOD 16 < 15 /\ ~(val(EL p inlist) DIV 16 < 15)
   ==> LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+1) inlist):int32 list) =
       LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) + 1`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_ETA2_BYTES_STEP_1) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;
let LEN_STEP_HI_ETA2 = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ ~(val(EL p inlist) MOD 16 < 15) /\ val(EL p inlist) DIV 16 < 15
   ==> LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+1) inlist):int32 list) =
       LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) + 1`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_ETA2_BYTES_STEP_1) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;
let LEN_STEP_NONE_ETA2 = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ ~(val(EL p inlist) MOD 16 < 15) /\ ~(val(EL p inlist) DIV 16 < 15)
   ==> LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+1) inlist):int32 list) =
       LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_ETA2_BYTES_STEP_1) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Per-byte output-list APPEND step (drive the memory fold).                 *)
(* ------------------------------------------------------------------------- *)
let REJ_STEP_BOTH_ETA2 = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ val(EL p inlist) MOD 16 < 15 /\ val(EL p inlist) DIV 16 < 15
   ==> REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+1) inlist) =
       APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist))
              [word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p inlist) MOD 16)) (word 5:int16))):int32;
               word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p inlist) DIV 16)) (word 5:int16))):int32]`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_SAMPLE_ETA2_BYTES_STEP_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REJ_SAMPLE_ETA2_BYTES_1_BOTH THEN ASM_REWRITE_TAC[]);;
let REJ_STEP_LO_ETA2 = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ val(EL p inlist) MOD 16 < 15 /\ ~(val(EL p inlist) DIV 16 < 15)
   ==> REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+1) inlist) =
       APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist))
              [word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p inlist) MOD 16)) (word 5:int16))):int32]`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_SAMPLE_ETA2_BYTES_STEP_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REJ_SAMPLE_ETA2_BYTES_1_LOW_ONLY THEN ASM_REWRITE_TAC[]);;
let REJ_STEP_HI_ETA2 = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ ~(val(EL p inlist) MOD 16 < 15) /\ val(EL p inlist) DIV 16 < 15
   ==> REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+1) inlist) =
       APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist))
              [word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p inlist) DIV 16)) (word 5:int16))):int32]`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_SAMPLE_ETA2_BYTES_STEP_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REJ_SAMPLE_ETA2_BYTES_1_HIGH_ONLY THEN ASM_REWRITE_TAC[]);;
let REJ_STEP_NONE_ETA2 = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ ~(val(EL p inlist) MOD 16 < 15) /\ ~(val(EL p inlist) DIV 16 < 15)
   ==> REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+1) inlist) = REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_SAMPLE_ETA2_BYTES_STEP_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `REJ_SAMPLE_ETA2_BYTES [EL p (inlist:byte list)] = []` SUBST1_TAC THENL
   [MATCH_MP_TAC REJ_SAMPLE_ETA2_BYTES_1_REJECT_BOTH THEN ASM_REWRITE_TAC[]; REWRITE_TAC[APPEND_NIL]]);;

(* ------------------------------------------------------------------------- *)
(* num_of_wordlist for a singleton int32.                                    *)
(* ------------------------------------------------------------------------- *)
let JAE_NOT_TAKEN_LT_ETA2 = prove
 (`!a k:num. a < k /\ k < 2 EXP 32
     ==> ~(&(val(word_zx(word a:int64):int32)):int - &k =
           &(val(word_sub(word_zx(word a:int64):int32) (word k):int32)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx(word a:int64):int32) = a` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX_64_32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (word_zx(word a:int64):int32) (word k:int32)) = a + 2 EXP 32 - k` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val(word k:int32) = k` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL [REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC; REFL_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a + 2 EXP 32 - k = (a + 2 EXP 32) - k /\ k <= a + 2 EXP 32` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&((a + 2 EXP 32) - k):int = &(a + 2 EXP 32) - &k` SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM INT_OF_NUM_SUB) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ARITH_RULE `0 < 2 EXP 32`) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC);;

let JAE_TAKEN_GE_ETA2 = prove
 (`!a k:num. k <= a /\ a < 2 EXP 32
     ==> (&(val(word_zx(word a:int64):int32)):int - &k =
          &(val(word_sub(word_zx(word a:int64):int32) (word k):int32)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx(word a:int64):int32) = a` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX_64_32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (word_zx(word a:int64):int32) (word k:int32)) = a - k` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val(word k:int32) = k` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL [REFL_TAC; REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&(a - k):int = &a - &k` SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM INT_OF_NUM_SUB) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* READ_1BYTE_EL (arch-generic).                                             *)
(* Read one input byte at offset p from the buffer's num_of_wordlist contract. *)
(* ------------------------------------------------------------------------- *)
let READ_1BYTE_EL_ETA2 = prove
 (`!(inlist:byte list) (buf:int64) (s:x86state) p n.
     LENGTH inlist = n /\ p < n /\
     read(memory :> bytes(buf, n)) s = num_of_wordlist inlist
     ==> read(memory :> bytes8 (word_add buf (word p))) s = EL p inlist`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`inlist:byte list`; `p:num`] EL_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[DIMINDEX_8] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[bytes8; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  SUBGOAL_THEN
   `read (bytes (word_add buf (word p),1)) (read memory s) =
    read (bytes (buf,n)) (read memory s) DIV 2 EXP (8 * p) MOD 256`
   SUBST1_TAC THENL
   [REWRITE_TAC[READ_BYTES_DIV] THEN
    MP_TAC(ISPECL [`word_add buf (word p):int64`; `n - p`; `1`; `read memory s:int64->byte`] READ_BYTES_MOD) THEN
    SUBGOAL_THEN `MIN (n - p) 1 = 1` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `MIN a 1 = 1 <=> 1 <= a`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `read (memory :> bytes (buf,n)) s = num_of_wordlist (inlist:byte list)` THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(256:num) = 2 EXP dimindex(:8)` SUBST1_TAC THENL
   [REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[WORD_MOD_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* RAX_INC (arch-generic).                                                   *)
(* ------------------------------------------------------------------------- *)
let RAX_INC_ETA2 = prove
 (`!L. L < 256 ==> word_zx(word_add (word_zx (word L:int64):int32) (word 1:int32)):int64 = word(L+1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx(word L:int64):int32) = L` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX_64_32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `val(word_zx(word_add (word_zx (word L:int64):int32) (word 1:int32)):int64) = L+1` SUBST1_TAC THENL
   [SUBGOAL_THEN `val(word_add (word_zx (word L:int64):int32) (word 1:int32)) = L + 1` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_32] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
      CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `val(word_add (word_zx (word L:int64):int32) (word 1:int32))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC VAL_WORD_ZX THEN REWRITE_TAC[DIMINDEX_32;DIMINDEX_64] THEN ARITH_TAC; ASM_REWRITE_TAC[]];
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]);;

(* ========================================================================= *)
(* eta2 CORRECT: scalar-tail store-value bridge.                             *)
(*                                                                           *)
(* The eta2 scalar tail store value is the scalar Barrett mod-5 reduction    *)
(* 2-(n MOD5).  After                                                        *)
(*   mov r10d,r11d; imul 0xcd(=205),r11d; shr 0xa,r11d; imul 5,r11d;         *)
(*   sub r11d,r10d; mov 2,r11d; sub r10d,r11d; mov r11d,(rdi,rax,4)          *)
(* the model stores at res+4*outlen0 the int32 (n = nibble val b MOD/DIV 16): *)
(*   word_zx(word_zx(word_sub (word 2)                                       *)
(*     (word_zx(word_zx(word_sub (word_zx(word n))                           *)
(*       (word_zx(word_zx(word_mul (word_zx(word_zx(word_ushr                *)
(*         (word_zx(word_zx(word_mul (word_zx(word_zx(word_zx(word n))))     *)
(*           (word 205)))) 10))) (word 5)))))))))                            *)
(* and this = word_sx(word_sub (word 2:int16) (word_umod (word n) (word 5))) *)
(* :int32 for n < 15.                                                        *)
(*                                                                           *)
(* NOTE: stating this equality as a STANDALONE n-parametrized lemma is fragile *)
(* — the deeply-nested word_zx tower's intermediate widths are simulator-    *)
(* determined and a hand-written term triggers "inventing type variables"    *)
(* (a polymorphic word) that WORD_REDUCE cannot reduce.  The reliable route is *)
(* to apply the reduction as an IN-BODY SUBGOAL_THEN whose LHS is COPIED from *)
(* the store hypothesis at that point (fully typed by the read-context),     *)
(* closed by                                                                 *)
(*   SUBGOAL_THEN `n=0 \/ ... \/ n=14` MP_TAC + ASM_ARITH_TAC,               *)
(*   then STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV.   *)
(* SCALAR_STORE_REDUCE_TAC below packages that.                              *)
(* ========================================================================= *)

(* Scalar Barrett core: n - 5*((205*n) DIV 1024) = n MOD 5 for n < 15.
 
   Underpins the store-value reduction; a standalone numeric identity, robust. *)

(* In-body store-value reducer: given a goal/hyp mentioning the (typed) store
   term for nibble value `nib`, prove the store-value = spec coefficient by
   15-way enumeration + WORD_REDUCE.  `nib` is the num term (val b MOD 16 or
   val b DIV 16); `lt15` is the accept hypothesis `nib < 15` in the assumptions.
   Usage in the body: MP_TAC the store hyp, then
     SCALAR_STORE_REDUCE_TAC `val(EL p inlist) MOD 16`
   after asserting the equality as a SUBGOAL_THEN copied from the store term. *)
let SCALAR_STORE_REDUCE_TAC nib : tactic =
  SUBGOAL_THEN (subst [nib,`nn:num`]
     `nn = 0 \/ nn = 1 \/ nn = 2 \/ nn = 3 \/ nn = 4 \/ nn = 5 \/ nn = 6 \/ nn = 7 \/
      nn = 8 \/ nn = 9 \/ nn = 10 \/ nn = 11 \/ nn = 12 \/ nn = 13 \/ nn = 14`)
    MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;;

(* ========================================================================= *)
(* eta2 CORRECT: SCALAR_TAIL_BODY (per-byte scalar-tail trip).               *)
(*                                                                           *)
(* One trip pc+399 -> pc+399 consuming input byte at position p, extending   *)
(* the output list by REJ_SAMPLE_ETA2_BYTES [EL p inlist].  Entry            *)
(* generalized to arbitrary p.  The ~(L=255 /\ low<15) hyp rules out the     *)
(* mid-byte exit (handled by the RUN wrapper's mid-exit case, not this body). *)
(*                                                                           *)
(* eta2 specifics: entry pc+399, buf 136, accept <15, store value Barrett    *)
(* 2-(n MOD5) (SCALAR_STORE_REDUCE_TAC).  The HIGH-nibble block (raw 0x1e5)  *)
(* RELOADS the input byte from -1(rsi,rcx) (rcx = p+1) because the low Barrett *)
(* clobbers r11d, so the high path needs a fresh READ_1BYTE_EL_ETA2 fact + a *)
(* WORD_RULE address rewrite before its movzbl step.  The high block is SHARED *)
(* by low-accept-fallthrough and low-reject (jae 0x1e5), so cases are        *)
(* structured (low<15?) x (high<15?).                                        *)
(*                                                                           *)
(* Step map:                                                                 *)
(*   SETUP: 1--8  -> s8 R10=low nibble, RIP=pc+432 (raw 0x1b4 cmp)           *)
(*   s9 cmp 0xf,r10d ; s10 jae 0x1e5(high)                                   *)
(*   low-accept (jae not taken): s11 mov ; s12 imul 0xcd ; s13 shr 0xa ;     *)
(*     s14 imul 5 ; s15 sub ; s16 mov 2 ; s17 sub ; s18 store(res+4*outlen0) ; *)
(*     s19 inc eax ; s20 cmp 0x100 ; s21 jae 0x222(done)                     *)
(*   HIGH block (raw 0x1e5): reload movzbl -1(rsi,rcx) ; shr 4 ; and 0xf ;   *)
(*     cmp 0xf ; jae 0x193(loop top=pc+399) ; then high Barrett + store + inc + *)
(*     jmp 0x193(pc+399).                                                    *)
(*                                                                           *)
(* Requires type_invention_error := true.                                    *)
(* ========================================================================= *)

let EXEC_ETA2 = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* Low-nibble bridge: r10d after `mov r11d,r10d; and 0xf,r10d` collapses to  *)
(* word(val b MOD 16).                                                       *)
(* ------------------------------------------------------------------------- *)
let R10_NIBBLE_VAL_ETA2 = prove
 (`!b:byte. word_zx(word_and (word_zx (word_zx (word_zx (word_zx (word_zx b:int32):int64):int32):int64):int32) (word 15:int32)):int64 = word(val b MOD 16)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `(word 15:int32) = word(2 EXP 4 - 1)` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SIMP_TAC[VAL_WORD_ZX_GEN; VAL_WORD_AND_MASK_WORD; DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64;
           VAL_WORD; ARITH] THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val(b:byte) MOD 4294967296 = val b /\ val(b:byte) MOD 18446744073709551616 = val b`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(b:byte) MOD 16 < 18446744073709551616` ASSUME_TAC THENL
   [MP_TAC(SPECL[`val(b:byte)`;`16`] MOD_LT_EQ) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV);;

(* High-nibble bridge: r11d after `movzbl(reload); shr 4; and 0xf` collapses to *)
(* word(val b DIV 16) (reload gives the byte through the movzbl zx tower, then *)
(* ushr 4, then and 15).                                                     *)
let R11_NIBBLE_VAL_ETA2 = prove
 (`!b:byte. word_zx (word_and (word_zx (word_zx (word_ushr (word_zx (word_zx (word_zx (b:byte) :int32) :int64) :int32) 4) :int64) :int32) (word 15 :int32)) :int64 = word (val b DIV 16)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `(word 15:int32) = word(2 EXP 4 - 1)` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SIMP_TAC[VAL_WORD_ZX_GEN; VAL_WORD_AND_MASK_WORD; VAL_WORD_USHR; DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64;
           VAL_WORD; ARITH] THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val(b:byte) MOD 4294967296 = val b /\ val(b:byte) MOD 18446744073709551616 = val b /\ (val(b:byte) DIV 16) MOD 18446744073709551616 = val b DIV 16 /\ (val(b:byte) DIV 16) MOD 4294967296 = val b DIV 16 /\ (val(b:byte) DIV 16) MOD 16 = val b DIV 16`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN MP_TAC(SPECL[`val(b:byte)`;`16`] DIV_LT) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Common RCX closer: word_zx(word_add(word_zx(word p))(word 1)):int64 = word(p+1) for p<136. *)
let RCX_INC_TAC =
  REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `val(word_zx(word p:int64):int32) = p` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX_64_32 THEN MP_TAC(ASSUME `p<136`) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_zx(word_add (word_zx (word p:int64):int32) (word 1:int32)):int64) = p+1` SUBST1_TAC THENL
   [SUBGOAL_THEN `val(word_add (word_zx (word p:int64):int32) (word 1:int32)) = p + 1` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_32] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
      CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN MP_TAC(ASSUME `p<136`) THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `val(word_add (word_zx (word p:int64):int32) (word 1:int32))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC VAL_WORD_ZX THEN REWRITE_TAC[DIMINDEX_32;DIMINDEX_64] THEN ARITH_TAC; ASM_REWRITE_TAC[]];
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ASSUME `p<136`) THEN ARITH_TAC];;

(* prove read(bytes(addr,4)) sN = val(word_sx ...) from a spec-form bytes32 store hyp. *)
let SCALAR_BODY_SETUP_ETA2 =
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(ISPECL [`inlist:byte list`; `buf:int64`; `s0:x86state`; `p:num`; `136`] READ_1BYTE_EL_ETA2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `outlen0 = LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list)` THEN
  FIRST_X_ASSUM(fun th -> if concl th = `L:num = outlen0` then SUBST_ALL_TAC th else NO_TAC) THEN
  SUBGOAL_THEN `~(&(val(word_zx(word outlen0:int64):int32)):int - &256 = &(val(word_sub(word_zx(word outlen0:int64):int32) (word 256):int32)))` ASSUME_TAC THENL
   [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(&(val(word_zx(word p:int64):int32)):int - &136 = &(val(word_sub(word_zx(word p:int64):int32) (word 136):int32)))` ASSUME_TAC THENL
   [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  X86_VSTEPS_TAC EXEC_ETA2 (1--8) THEN
  SUBGOAL_THEN `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64` ASSUME_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
    MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `p < 136`) THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64`;
                              ASSUME `read (memory :> bytes8 (word_add buf (word p))) s4 = EL p (inlist:byte list)`;
                              R10_NIBBLE_VAL_ETA2]) THEN
  DISCARD_OLDSTATE_TAC "s8";;

(* ------------------------------------------------------------------------- *)
(* RELOAD_PREP_ETA2 sN : establish the high-nibble reload byte fact + address. *)
(* At state sN (RCX = word_zx(word_add(word_zx(word p))(word 1))), before the *)
(* movzbl -1(rsi,rcx), prove read RCX sN = word(p+1), the reload READ_1BYTE  *)
(* fact, and the address equality word_add buf (word(1*val(word(p+1))+0xF..F)) *)
(* = word_add buf (word p).  (Fold happens after the movzbl step.)           *)
(* ------------------------------------------------------------------------- *)
let RELOAD_PREP_ETA2 sN : tactic =
  (* Collapse the (unique) read RCX sN = word_zx(word_add(word_zx(word p))(word 1))
     assumption to = word(p+1) IN PLACE via RAX_INC_ETA2.  This leaves exactly one
     RCX assumption (canonical word(p+1) form) — the stepper needs one unambiguous
     RCX value to evaluate the movzbl -1(rsi,rcx) address, and a duplicate (both
     inc-form and word(p+1)) makes its lookup `tryfind` fail. *)
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP RAX_INC_ETA2
     (MATCH_MP (ARITH_RULE `p<136 ==> p<256`) (ASSUME `p<136`))]) THEN
  MP_TAC(ISPECL [`inlist:byte list`; `buf:int64`; sN; `p:num`; `136`] READ_1BYTE_EL_ETA2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `word_add buf (word(1 * val(word(p+1):int64) + 18446744073709551615)):int64 = word_add buf (word p)` ASSUME_TAC THENL
   [AP_TERM_TAC THEN
    SUBGOAL_THEN `val(word(p+1):int64) = p+1` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `p<136`) THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `1 * (p+1) + 18446744073709551615 = p + 2 EXP 64`] THEN
    REWRITE_TAC[WORD_ADD] THEN
    SUBGOAL_THEN `word(2 EXP 64):int64 = word 0` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    CONV_TAC WORD_RULE; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* NB: the ACCEPT-* paths step a low store to res+4*outlen0 (s18), THEN the  *)
(* high-nibble reload movzbl -1(rsi,rcx) at s22.  The stepper's read-over-write *)
(* resolution for read(buf+p) THROUGH the store to res+4*outlen0 needs the   *)
(* store-frame nonoverlap discharged before the movzbl.  RELOAD_PREP_ETA2 is *)
(* the reload-address helper; the LOW-REJECT path (reload with NO prior store) *)
(* uses it directly.                                                         *)
(* ------------------------------------------------------------------------- *)

(* ========================================================================= *)
(* eta2 CORRECT: SCALAR_TAIL_BODY (the per-byte scalar trip).                *)
(*                                                                           *)
(* One trip pc+399 -> pc+399 consuming input byte at position p, extending   *)
(* the output list by REJ_SAMPLE_ETA2_BYTES [EL p inlist].  Entry pc+399 ;   *)
(* buf 136 ; accept <15 ; store 2-(n MOD5) via Barrett.                      *)
(*                                                                           *)
(* KEY STRUCTURAL NOTES:                                                     *)
(*  (1) eta2's HIGH-nibble block RELOADS the byte from -1(rsi,rcx) (raw 0x1e5) *)
(*      via RELOAD_PREP_ETA2 (the low Barrett clobbers r11d).                *)
(*  (2) STEP-MAP ORDER: store(s18) -> inc eax(s19) -> cmp(s20) -> jae(s21) -> *)
(*      movzbl(s22).  RAX MUST be folded to word(outlen0+1) at s19 so the s21 *)
(*      jae resolves to a concrete RIP; else the s22 movzbl DECODE fails     *)
(*      `tryfind`.                                                           *)
(*  (3) HIGH store (s34 accept-accept / s23 hi-only) has RAX = word(outlen0+1) *)
(*      resp word(outlen0): establish val(word ..)=.. BEFORE the store step so *)
(*      the stepper proves the store addr non-code-overlapping.              *)
(*  (4) Store value is the deep Barrett word_zx tower; bridge it to spec form *)
(*      via ETA2_STORE_SPEC_TAC (clean-subgoal SCALAR_STORE_REDUCE_TAC) — the *)
(*      tower is simulator-typed so no standalone lemma (memory lesson).     *)
(*                                                                           *)
(* Full step maps (objdump rej_uniform_eta2_avx2_asm.o, tmc offsets=raw-4):  *)
(*   SETUP 1-8 -> s8 RIP pc+432 (0x1b4 cmp), R10 = low nibble.               *)
(*   s9 cmp 0xf,r10d ; s10 jae 0x1e5 (high).                                 *)
(*   ACCEPT-LOW (s10 not taken): s11..s18 low Barrett+store(pc+472);         *)
(*     s19 inc eax ; s20 cmp 0x100 ; s21 jae done (not taken) -> s22 movzbl. *)
(*     HIGH: s22 movzbl reload ; s23 shr4 ; s24 and0xf -> R11=high nibble ;  *)
(*       s25 cmp 0xf ; s26 jae loop.                                         *)
(*       ACCEPT-ACCEPT (s26 not taken): s27..s34 high Barrett+store ; s35 inc ; *)
(*         s36 jmp -> pc+399.                                                *)
(*       LO-only (s26 taken): -> pc+399.                                     *)
(*   REJECT-LOW (s10 taken): s11 movzbl reload ; s12 shr4 ; s13 and0xf ->    *)
(*     R11=high nibble ; s14 cmp 0xf ; s15 jae loop.                         *)
(*       HI-only (s15 not taken): s16..s23 high Barrett+store ; s24 inc ;    *)
(*         s25 jmp -> pc+399.                                                *)
(*       NONE (s15 taken): -> pc+399.                                        *)
(*                                                                           *)
(* Requires type_invention_error := true.                                    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* ETA2_STORE_SPEC_TAC sN nibt : bridge the tower-valued bytes32 store fact at *)
(* state sN, nibble `nibt` (= `val(EL p inlist) MOD 16` or `... DIV 16`), to *)
(* spec form `word_sx(word_sub 2 (word_umod (word nibt) 5)):int32`, on a     *)
(* CLEANED subgoal (accept hyp `nibt < 15` + the store fact only) so the     *)
(* 15-way WORD_REDUCE is fast (~1min) rather than >4min with all ensures asms. *)
(* ------------------------------------------------------------------------- *)
let ETA2_SPECRHS_OF nibt =
  subst [nibt,`nn:num`]
   `word_sx(word_sub (word 2:int16) (word_umod (word nn) (word 5:int16))):int32`;;

let ETA2_STORE_SPEC_TAC (sN:term) (nibt:term) : tactic =
  let acc = mk_binary "<" (nibt,`15`) in
  let specrhs = ETA2_SPECRHS_OF nibt in
  FIRST_ASSUM (fun ath ->
    if concl ath <> acc then NO_TAC else
    FIRST_X_ASSUM (fun th ->
      let c = concl th in
      if is_eq c
         && can (find_term (fun t -> try fst(dest_const t)="bytes32" with _->false)) c
         && can (find_term (fun t -> t=sN)) c
         && can (find_term (fun t -> t=nibt)) c
         && not (can (find_term is_cond) c)
      then
        SUBGOAL_THEN (mk_eq (lhand c, specrhs)) ASSUME_TAC THENL
         [MP_TAC th THEN POP_ASSUM_LIST (K ALL_TAC) THEN
          MP_TAC ath THEN DISCH_TAC THEN
          DISCH_THEN SUBST1_TAC THEN SCALAR_STORE_REDUCE_TAC nibt;
          ALL_TAC]
      else NO_TAC));;

let EXEC_ETA2 = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

let SCALAR_TAIL_BODY_ETA2 = prove
 (`!res buf table (inlist:byte list) pc (p:num) (L:num) stackpointer.
        LENGTH inlist = 136 /\
        nonoverlapping_modulo (2 EXP 64) (pc, 543) (val res,1024) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 543) (val buf, 136) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 136) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table, 2048) /\
        p < 136 /\ L < 256 /\
        L = LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) /\
        ~(L = 255 /\ val(EL p (inlist:byte list)) MOD 16 < 15)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
                  read RIP s = word(pc + 399) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  read RAX s = word L /\ read RCX s = word p /\
                  read(memory :> bytes(res, 4 * L)) s =
                    num_of_wordlist(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist)))
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
                  read RIP s = word(pc + 399) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  (let outlist = REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+1) inlist) in
                   read RAX s = word(LENGTH outlist) /\ read RCX s = word(p+1) /\
                   read(memory :> bytes(res, 4 * LENGTH outlist)) s = num_of_wordlist outlist))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
  SCALAR_BODY_SETUP_ETA2 THEN
  ASM_CASES_TAC `val(EL p (inlist:byte list)) MOD 16 < 15` THENL
   [(* ============ ACCEPT-LOW (low<15): jae s10 NOT taken ============ *)
    SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32)):int - &15 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32) (word 15):int32)))` ASSUME_TAC THENL
     [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    (* low Barrett + store(s18) + inc eax(s19)                               *)
    X86_VSTEPS_TAC EXEC_ETA2 (9--19) THEN
    (* FOLD RAX at s19 -> word(outlen0+1) so the s21 jae resolves            *)
    FIRST_X_ASSUM(fun th -> let c=concl th in
       if is_eq c && can(find_term(fun t->t=`RAX`))c && can(find_term(fun t->t=`s19:x86state`))c
       then ASSUME_TAC(REWRITE_RULE[MATCH_MP RAX_INC_ETA2 (ASSUME `outlen0<256`)] th) else NO_TAC) THEN
    SUBGOAL_THEN `outlen0 + 1 < 256` ASSUME_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o check(fun th->let c=concl th in c=`outlen0<256`||c=`val(EL p (inlist:byte list)) MOD 16 < 15`||c=`~(outlen0=255/\val(EL p (inlist:byte list)) MOD 16 < 15)`))) THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(&(val(word_zx(word(outlen0+1):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(outlen0+1):int64):int32) (word 256):int32)))` ASSUME_TAC THENL
     [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    (* cmp(s20) + jae done(s21) NOT taken -> movzbl(s22)                     *)
    X86_VSTEPS_TAC EXEC_ETA2 (20--21) THEN
    RELOAD_PREP_ETA2 `s21:x86state` THEN
    (* reload movzbl(s22) + shr(s23) + and(s24) -> R11=high nibble           *)
    X86_VSTEPS_TAC EXEC_ETA2 (22--24) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[R11_NIBBLE_VAL_ETA2]) THEN DISCARD_OLDSTATE_TAC "s24" THEN
    ASM_CASES_TAC `val(EL p (inlist:byte list)) DIV 16 < 15` THENL
     [(* ===== ACCEPT-ACCEPT (high<15): jae s26 NOT taken ===== *)
      SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &15 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 15):int32)))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      (* val(word(outlen0+1)) needed BEFORE the high store s34               *)
      SUBGOAL_THEN `val(word(outlen0+1):int64) = outlen0+1` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0+1<256`) THEN ARITH_TAC; ALL_TAC] THEN
      X86_VSTEPS_TAC EXEC_ETA2 (25--35) THEN
      X86_VSTEPS_TAC EXEC_ETA2 (36--36) THEN DISCARD_OLDSTATE_TAC "s36" THEN
      FIRST_X_ASSUM(fun th -> let c=concl th in
         if is_eq c && can(find_term(fun t->t=`RAX`))c && can(find_term(fun t->t=`s36:x86state`))c
         then ASSUME_TAC(REWRITE_RULE[MATCH_MP RAX_INC_ETA2 (ASSUME `outlen0+1<256`)] th) else NO_TAC) THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0 + 2` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_BOTH_ETA2) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      ASM_REWRITE_TAC[ARITH_RULE `(outlen0+1)+1 = outlen0+2`] THEN
      TRY(CONJ_TAC THENL [RCX_INC_TAC; ALL_TAC]) THEN
      SUBGOAL_THEN `REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p+1) inlist) =
         APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist))
                [word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32;
                 word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) DIV 16)) (word 5:int16))):int32]` SUBST1_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_BOTH_ETA2) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `4 * (outlen0 + 2) = 4 * outlen0 + 8` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s36:x86state`;
         `REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list`;
         `[word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32;
           word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) DIV 16)) (word 5:int16))):int32]`;
         `4*outlen0`; `8`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[DIMINDEX_32] THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC) THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM(REWRITE_CONV[APPEND] `APPEND [a:int32] [b:int32]`)] THEN
        SUBGOAL_THEN `(8:num) = 4 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `word_add res (word(4*outlen0)):int64`; `s36:x86state`;
           `[word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]`;
           `[word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) DIV 16)) (word 5:int16))):int32]`;
           `4`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
        ANTS_TAC THENL [REWRITE_TAC[DIMINDEX_32; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
        SUBGOAL_THEN `val(word outlen0:int64) = outlen0` ASSUME_TAC THENL
         [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0<256`) THEN ARITH_TAC; ALL_TAC] THEN
        ETA2_STORE_SPEC_TAC `s36:x86state` `val(EL p (inlist:byte list)) MOD 16` THEN
        ETA2_STORE_SPEC_TAC `s36:x86state` `val(EL p (inlist:byte list)) DIV 16` THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c && not(can(find_term is_cond)c)
             then MP_TAC th else NO_TAC) THEN
          ASM_REWRITE_TAC[] THEN
          STORE4_FROM_SPEC `s36:x86state` `word_add res (word(4 * outlen0)):int64`;
          SUBGOAL_THEN `word_add (word_add res (word (4 * outlen0))) (word 4):int64 = word_add res (word (4 * (outlen0+1)))` SUBST1_TAC THENL
           [CONV_TAC WORD_RULE; ALL_TAC] THEN
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) DIV 16`))c && not(can(find_term is_cond)c)
             then MP_TAC th else NO_TAC) THEN
          ASM_REWRITE_TAC[] THEN
          STORE4_FROM_SPEC `s36:x86state` `word_add res (word(4 * (outlen0+1))):int64`]];
      (* ===== LO-only (low<15, high>=15): jae s26 TAKEN -> pc+399 =====     *)
      SUBGOAL_THEN `&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &15 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 15):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE_ETA2 THEN CONJ_TAC THENL
         [MP_TAC(ASSUME `~(val(EL p (inlist:byte list)) DIV 16 < 15)`) THEN ARITH_TAC;
          MP_TAC(ISPEC `EL p (inlist:byte list)` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
          MP_TAC(SPECL[`val(EL p (inlist:byte list))`;`16`] DIV_LE) THEN ARITH_TAC]; ALL_TAC] THEN
      X86_VSTEPS_TAC EXEC_ETA2 (25--26) THEN DISCARD_OLDSTATE_TAC "s26" THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0 + 1` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_LO_ETA2) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      TRY(CONJ_TAC THENL [RCX_INC_TAC; ALL_TAC]) THEN
      SUBGOAL_THEN `REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p+1) inlist) =
         APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist))
                [word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]` SUBST1_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_LO_ETA2) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `4 * (outlen0 + 1) = 4 * outlen0 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s26:x86state`;
         `REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list`;
         `[word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]`;
         `4*outlen0`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[DIMINDEX_32] THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC) THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
      CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        SUBGOAL_THEN `val(word outlen0:int64) = outlen0` ASSUME_TAC THENL
         [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0<256`) THEN ARITH_TAC; ALL_TAC] THEN
        ETA2_STORE_SPEC_TAC `s26:x86state` `val(EL p (inlist:byte list)) MOD 16` THEN
        FIRST_X_ASSUM(fun th -> let c=concl th in
           if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c && not(can(find_term is_cond)c)
           then MP_TAC th else NO_TAC) THEN
        ASM_REWRITE_TAC[] THEN
        STORE4_FROM_SPEC `s26:x86state` `word_add res (word(4 * outlen0)):int64`]];
    (* ============ REJECT-LOW (low>=15): jae s10 TAKEN -> movzbl s11 ============ *)
    SUBGOAL_THEN `&(val(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32)):int - &15 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32) (word 15):int32))` ASSUME_TAC THENL
     [MATCH_MP_TAC JAE_TAKEN_GE_ETA2 THEN CONJ_TAC THENL
       [MP_TAC(ASSUME `~(val(EL p (inlist:byte list)) MOD 16 < 15)`) THEN ARITH_TAC;
        MP_TAC(SPECL[`val(EL p (inlist:byte list))`;`16`] MOD_LT_EQ) THEN ARITH_TAC]; ALL_TAC] THEN
    (* jae taken(s10) -> movzbl reload(s11) : NO prior store, RELOAD_PREP at s10 *)
    X86_VSTEPS_TAC EXEC_ETA2 (9--10) THEN
    RELOAD_PREP_ETA2 `s10:x86state` THEN
    X86_VSTEPS_TAC EXEC_ETA2 (11--13) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[R11_NIBBLE_VAL_ETA2]) THEN DISCARD_OLDSTATE_TAC "s13" THEN
    ASM_CASES_TAC `val(EL p (inlist:byte list)) DIV 16 < 15` THENL
     [(* ===== HI-only (low>=15, high<15): jae s15 NOT taken -> store ===== *)
      SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &15 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 15):int32)))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `val(word outlen0:int64) = outlen0` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0<256`) THEN ARITH_TAC; ALL_TAC] THEN
      X86_VSTEPS_TAC EXEC_ETA2 (14--23) THEN
      X86_VSTEPS_TAC EXEC_ETA2 (24--25) THEN DISCARD_OLDSTATE_TAC "s25" THEN
      FIRST_X_ASSUM(fun th -> let c=concl th in
         if is_eq c && can(find_term(fun t->t=`RAX`))c && can(find_term(fun t->t=`s25:x86state`))c
         then ASSUME_TAC(REWRITE_RULE[MATCH_MP RAX_INC_ETA2 (ASSUME `outlen0<256`)] th) else NO_TAC) THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0 + 1` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_HI_ETA2) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      TRY(CONJ_TAC THENL [RCX_INC_TAC; ALL_TAC]) THEN
      SUBGOAL_THEN `REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p+1) inlist) =
         APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist))
                [word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) DIV 16)) (word 5:int16))):int32]` SUBST1_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_HI_ETA2) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `4 * (outlen0 + 1) = 4 * outlen0 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s25:x86state`;
         `REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list`;
         `[word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) DIV 16)) (word 5:int16))):int32]`;
         `4*outlen0`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[DIMINDEX_32] THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC) THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
      CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        ETA2_STORE_SPEC_TAC `s25:x86state` `val(EL p (inlist:byte list)) DIV 16` THEN
        FIRST_X_ASSUM(fun th -> let c=concl th in
           if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) DIV 16`))c && not(can(find_term is_cond)c)
           then MP_TAC th else NO_TAC) THEN
        ASM_REWRITE_TAC[] THEN
        STORE4_FROM_SPEC `s25:x86state` `word_add res (word(4 * outlen0)):int64`];
      (* ===== NONE (low>=15, high>=15): jae s15 TAKEN -> pc+399, no store ===== *)
      SUBGOAL_THEN `&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &15 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 15):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE_ETA2 THEN CONJ_TAC THENL
         [MP_TAC(ASSUME `~(val(EL p (inlist:byte list)) DIV 16 < 15)`) THEN ARITH_TAC;
          MP_TAC(ISPEC `EL p (inlist:byte list)` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
          MP_TAC(SPECL[`val(EL p (inlist:byte list))`;`16`] DIV_LE) THEN ARITH_TAC]; ALL_TAC] THEN
      X86_VSTEPS_TAC EXEC_ETA2 (14--15) THEN DISCARD_OLDSTATE_TAC "s15" THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_NONE_ETA2) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      SUBGOAL_THEN `REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p+1) inlist):int32 list = REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist)` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_NONE_ETA2) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN RCX_INC_TAC]]);;

(* ========================================================================= *)
(* eta2 CORRECT: SCALAR_TAIL_RUN substrate (pure list algebra).              *)
(*                                                                           *)
(* The buf-length / output-cap list lemmas the SCALAR_TAIL_RUN induction     *)
(* needs (buf 136, tmc-length, REJ_SAMPLE_ETA2_BYTES).  All pure             *)
(* list/arithmetic (no ISA stepping).                                        *)
(* ========================================================================= *)

(* Generic: LENGTH l = LENGTH(BUTLAST l) + 1 for nonempty l.                 *)
let LENGTH_BUTLAST_TMC_ETA2 = prove
 (`LENGTH(BUTLAST mldsa_rej_uniform_eta2_tmc) = 542`,
  MP_TAC(ISPEC `mldsa_rej_uniform_eta2_tmc` LENGTH_BUTLAST_GEN) THEN
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_MLDSA_REJ_UNIFORM_ETA2_TMC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* SUB_LIST(0,136) inlist = inlist when LENGTH inlist = 136.                 *)
let SUB_LIST_BYTE_136 = prove
 (`!(l:byte list). LENGTH l = 136 ==> SUB_LIST(0, 136) l = l`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `LENGTH (l:byte list) = 136` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC SUB_LIST_LENGTH);;

(* Output cap is the identity when the list is short.                        *)
let REJ_SAMPLE_ETA2_SUB_LIST_PREFIX = prove
 (`!k (l:byte list).
     k <= LENGTH l
     ==> ?rest:int32 list.
         APPEND (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,k) l)) rest =
         REJ_SAMPLE_ETA2_BYTES l`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `REJ_SAMPLE_ETA2_BYTES (SUB_LIST(k, LENGTH l - k) l):int32 list` THEN
  REWRITE_TAC[REJ_SAMPLE_ETA2_BYTES; GSYM MAP_APPEND] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[REJ_NIBBLES_ETA2; GSYM FILTER_APPEND] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[GSYM NIBBLES_OF_BYTES_APPEND] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`l:byte list`; `k:num`] SUB_LIST_TOPSPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  REFL_TAC);;

(* Capped full-input output = capped partial output once the partial reaches *)
(* 256.                                                                      *)
let SUB_LIST_256_PREFIX_GE = prove
 (`!(inlist:byte list) k.
     k <= LENGTH inlist /\
     256 <= LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,k) inlist):int32 list)
     ==> SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist :int32 list) =
         SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,k) inlist))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `inlist:byte list`] REJ_SAMPLE_ETA2_SUB_LIST_PREFIX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ext:int32 list` (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th])) THEN
  MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* eta2 CORRECT: SCALAR_TAIL_RUN (byte-loop-to-exit by strong.               *)
(* induction on byte-budget d).                                              *)
(*                                                                           *)
(* eta2 specifics: entry pc+399 ; buf 136 ; tmc-length 543 ; BUTLAST-tmc exit *)
(* 542 ; accept <15 ; store Barrett 2-(n MOD5) (ETA2_STORE_SPEC_TAC).        *)
(*                                                                           *)
(* 4-way per step:                                                           *)
(*   count-exit  : outlen>=256 (=256) : cmp eax,256 jae taken -> pc+542.     *)
(*   offset-exit : p=136 : cmp eax,256 not-taken + cmp ecx,136 jae taken.    *)
(*   mid-byte-exit : outlen=255 /\ low<15 (last low-accept hits 256) : inline *)
(*     re-step SETUP 1-8, low Barrett+store+inc 9-19, fold RAX@s19,          *)
(*     cmp+jae-TAKEN 20-21 -> pc+542 (the 6-insn Barrett makes mid-exit 21   *)
(*     steps).                                                               *)
(*   clean-recursive : SCALAR_TAIL_BODY_ETA2 @ (p, outlen(p)) via            *)
(*     ENSURES_SEQUENCE_TAC pc+399 + IH @ p+1.                               *)
(*                                                                           *)
(* Requires type_invention_error := true.                                    *)
(* ========================================================================= *)

let EXEC_ETA2 = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

let SCALAR_TAIL_RUN_ETA2 = prove
 (`!d res buf table (inlist:byte list) pc (p:num) stackpointer.
        136 - p <= d /\
        LENGTH inlist = 136 /\
        nonoverlapping_modulo (2 EXP 64) (pc, 543) (val res,1024) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 543) (val buf, 136) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 543) (val table,2048) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 136) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table,2048) /\
        p <= 136 /\
        LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) <= 256
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
                  read RIP s = word(pc + 399) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  read RAX s = word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list)) /\
                  read RCX s = word p /\
                  read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list))) s =
                    num_of_wordlist(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist)))
             (\s. read RIP s = word(pc + LENGTH(BUTLAST mldsa_rej_uniform_eta2_tmc)) /\
                  (let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA2_BYTES inlist) in
                   read RAX s = word(LENGTH outlist) /\
                   read(memory :> bytes(res, 4 * LENGTH outlist)) s = num_of_wordlist outlist))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
  INDUCT_TAC THENL
   [(* ================= BASE CASE: d = 0 => p = 136 ================= *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `p = 136` SUBST_ALL_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> let c=concl th in c=`136 - p <= 0` || c=`p <= 136`))) THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `inlist:byte list` SUB_LIST_BYTE_136) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `SUB_LIST(0,136) (inlist:byte list) = inlist`]) THEN
    REWRITE_TAC[ASSUME `SUB_LIST(0,136) (inlist:byte list) = inlist`] THEN
    ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) = 256` THENL
     [(* --- BASE COUNT-EXIT: outlen = 256 --- *)
      MP_TAC(SPEC `REJ_SAMPLE_ETA2_BYTES inlist:int32 list` SUB_LIST_256_LE) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) = 256`] THEN
      REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) = REJ_SAMPLE_ETA2_BYTES inlist`] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `&(val(word_zx(word 256:int64):int32)):int - &256 = &(val(word_sub(word_zx(word 256:int64):int32) (word 256):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE_ETA2 THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
      X86_VSTEPS_TAC EXEC_ETA2 (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) = 256`] THEN
      REWRITE_TAC[LENGTH_BUTLAST_TMC_ETA2] THEN ASM_REWRITE_TAC[];
      (* --- BASE OFFSET-EXIT: outlen < 256, p = 136 ---                     *)
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) < 256` ASSUME_TAC THENL
       [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> let c=concl th in c=`LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) <= 256` || c=`~(LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) = 256)`))) THEN ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `REJ_SAMPLE_ETA2_BYTES inlist:int32 list` SUB_LIST_256_LE) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) = REJ_SAMPLE_ETA2_BYTES inlist`] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `~(&(val(word_zx(word(LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list)):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list)):int64):int32) (word 256):int32)))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      SUBGOAL_THEN `&(val(word_zx(word 136:int64):int32)):int - &136 = &(val(word_sub(word_zx(word 136:int64):int32) (word 136):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE_ETA2 THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
      X86_VSTEPS_TAC EXEC_ETA2 (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[LENGTH_BUTLAST_TMC_ETA2] THEN ASM_REWRITE_TAC[]];
    (* ================= STEP CASE: SUC d =================                  *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_CASES_TAC `256 <= LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list)` THENL
     [(* --- STEP COUNT-EXIT: outlen >= 256 (=256 by invariant) --- *)
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) = 256` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`inlist:byte list`; `p:num`] SUB_LIST_256_PREFIX_GE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      MP_TAC(SPEC `REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list` SUB_LIST_256_LE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN DISCH_TAC THEN
      SUBGOAL_THEN `SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) = REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) = REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist)`;
                  ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) = 256`] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `&(val(word_zx(word 256:int64):int32)):int - &256 = &(val(word_sub(word_zx(word 256:int64):int32) (word 256):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE_ETA2 THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
      X86_VSTEPS_TAC EXEC_ETA2 (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) = 256`; LENGTH_BUTLAST_TMC_ETA2] THEN
      ASM_REWRITE_TAC[];
      (* --- not count-exit: outlen < 256 ---                                *)
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) < 256` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `p = 136` THENL
       [(* --- STEP OFFSET-EXIT: p = 136 --- *)
        FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `p = 136`)) THEN
        MP_TAC(SPEC `inlist:byte list` SUB_LIST_BYTE_136) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `SUB_LIST(0,136) (inlist:byte list) = inlist`]) THEN
        REWRITE_TAC[ASSUME `SUB_LIST(0,136) (inlist:byte list) = inlist`] THEN
        MP_TAC(SPEC `REJ_SAMPLE_ETA2_BYTES inlist:int32 list` SUB_LIST_256_LE) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
        REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) = REJ_SAMPLE_ETA2_BYTES inlist`] THEN
        ENSURES_INIT_TAC "s0" THEN
        SUBGOAL_THEN `~(&(val(word_zx(word(LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list)):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list)):int64):int32) (word 256):int32)))` ASSUME_TAC THENL
         [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
        SUBGOAL_THEN `&(val(word_zx(word 136:int64):int32)):int - &136 = &(val(word_sub(word_zx(word 136:int64):int32) (word 136):int32))` ASSUME_TAC THENL
         [MATCH_MP_TAC JAE_TAKEN_GE_ETA2 THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
        X86_VSTEPS_TAC EXEC_ETA2 (1--4) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        REWRITE_TAC[LENGTH_BUTLAST_TMC_ETA2] THEN ASM_REWRITE_TAC[];
        (* --- p < 136 ---                                                   *)
        SUBGOAL_THEN `p < 136` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) = 255 /\ val(EL p (inlist:byte list)) MOD 16 < 15` THENL
         [(* --- STEP MID-BYTE EXIT: outlen=255, low<15 (accept low pushes to 256) --- *)
          FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th -> is_conj(concl th) && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))(concl th))) THEN
          SUBGOAL_THEN `256 <= LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+1) inlist):int32 list)` ASSUME_TAC THENL
           [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_ETA2_BYTES_STEP_1) THEN
            ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `?rest. REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+1) inlist):int32 list =
             APPEND (APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist))
                            [word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]) rest`
           STRIP_ASSUME_TAC THENL
           [ASM_CASES_TAC `val(EL p (inlist:byte list)) DIV 16 < 15` THENL
             [EXISTS_TAC `[word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) DIV 16)) (word 5:int16))):int32]` THEN
              MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_BOTH_ETA2) THEN
              ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
              DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[APPEND; GSYM APPEND_ASSOC];
              EXISTS_TAC `[]:int32 list` THEN
              MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_LO_ETA2) THEN
              ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
              DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[APPEND_NIL]]; ALL_TAC] THEN
          MP_TAC(SPECL [`inlist:byte list`; `p+1`] SUB_LIST_256_PREFIX_GE) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
          SUBGOAL_THEN `LENGTH(APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist))
                            [word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]:int32 list) = 256` ASSUME_TAC THENL
           [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) =
               APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist))
                      [word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]` ASSUME_TAC THENL
           [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && (try lhs(concl th) = `SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist:int32 list)` with _->false) then SUBST1_TAC th else NO_TAC) THEN
            FIRST_X_ASSUM(fun th -> if is_eq(concl th) && (try lhs(concl th) = `REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+1) inlist):int32 list` with _->false) then SUBST1_TAC th else NO_TAC) THEN
            W(fun (asl,gl) -> let lt = rhs gl in
               MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (mk_comb(`SUB_LIST(0,256):(int32)list->(int32)list`, lt)) THEN
               CONJ_TAC THENL
                [MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN ASM_REWRITE_TAC[LE_REFL];
                 MATCH_MP_TAC SUB_LIST_256_LE THEN ASM_REWRITE_TAC[LE_REFL]]); ALL_TAC] THEN
          REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) =
                APPEND (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist))
                [word_sx (word_sub (word 2:int16) (word_umod (word (val (EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]`] THEN
          REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) = 255`] THEN
          ENSURES_INIT_TAC "s0" THEN
          MP_TAC(ISPECL [`inlist:byte list`; `buf:int64`; `s0:x86state`; `p:num`; `136`] READ_1BYTE_EL_ETA2) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
          SUBGOAL_THEN `~(&(val(word_zx(word 255:int64):int32)):int - &256 = &(val(word_sub(word_zx(word 255:int64):int32) (word 256):int32)))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
          SUBGOAL_THEN `~(&(val(word_zx(word p:int64):int32)):int - &136 = &(val(word_sub(word_zx(word p:int64):int32) (word 136):int32)))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
          X86_VSTEPS_TAC EXEC_ETA2 (1--8) THEN
          SUBGOAL_THEN `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64` ASSUME_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
            MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `p < 136`) THEN ARITH_TAC; ALL_TAC] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64`;
                                      ASSUME `read (memory :> bytes8 (word_add buf (word p))) s4 = EL p (inlist:byte list)`;
                                      R10_NIBBLE_VAL_ETA2]) THEN
          DISCARD_OLDSTATE_TAC "s8" THEN
          SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32)):int - &15 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32) (word 15):int32)))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `val(word 255:int64) = 255` ASSUME_TAC THENL
           [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC; ALL_TAC] THEN
          X86_VSTEPS_TAC EXEC_ETA2 (9--19) THEN
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->t=`RAX`))c && can(find_term(fun t->t=`s19:x86state`))c
             then ASSUME_TAC(REWRITE_RULE[MATCH_MP RAX_INC_ETA2 (ARITH_RULE `255<256`)] th) else NO_TAC) THEN
          SUBGOAL_THEN `&(val(word_zx(word(255+1):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(255+1):int64):int32) (word 256):int32))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_TAKEN_GE_ETA2 THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
          X86_VSTEPS_TAC EXEC_ETA2 (20--21) THEN
          ENSURES_FINAL_STATE_TAC THEN
          REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) =
                APPEND (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist))
                [word_sx (word_sub (word 2:int16) (word_umod (word (val (EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]`] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
          REWRITE_TAC[ASSUME `LENGTH(APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist))
                [word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]:int32 list) = 256`] THEN
          REWRITE_TAC[LENGTH_BUTLAST_TMC_ETA2] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
          (* memory fold: bytes(res,4*256) = APPEND prefix [lo]              *)
          SUBGOAL_THEN `4 * 256 = 4 * 255 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
          MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s21:x86state`;
             `REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list`;
             `[word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]`;
             `4*255`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
          ANTS_TAC THENL [REWRITE_TAC[DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
          CONJ_TAC THENL
           [ASM_REWRITE_TAC[];
            SUBGOAL_THEN `word(4 * 255):int64 = word 1020` SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
            ETA2_STORE_SPEC_TAC `s21:x86state` `val(EL p (inlist:byte list)) MOD 16` THEN
            FIRST_X_ASSUM(fun th -> let c=concl th in
               if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c && not(can(find_term is_cond)c)
               then MP_TAC th else NO_TAC) THEN
            ASM_REWRITE_TAC[] THEN
            STORE4_FROM_SPEC `s21:x86state` `word_add res (word 1020):int64`];
          (* --- STEP CLEAN-RECURSIVE: body trip then IH at p+1 ---          *)
          SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+1) inlist):int32 list) <= 256` ASSUME_TAC THENL
           [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_ETA2_BYTES_STEP_1) THEN ASM_REWRITE_TAC[] THEN
            DISCH_THEN SUBST1_TAC THEN
            REPEAT(FIRST_X_ASSUM(MP_TAC o check(fun th -> let c=concl th in
               c = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) < 256` ||
               c = `~(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) = 255 /\ val(EL p (inlist:byte list)) MOD 16 < 15)`))) THEN
            REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ARITH_TAC; ALL_TAC] THEN
          (* body lemma instance at (p, outlen(p))                           *)
          MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`p:num`;
             `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list)`;`stackpointer:int64`] SCALAR_TAIL_BODY_ETA2) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(fun body_th ->
            let bodyQ = rand(rator(concl body_th)) in
            ENSURES_SEQUENCE_TAC `pc + 399` bodyQ THEN
            CONJ_TAC THENL
             [(* leg1: P -> bodyQ via the body lemma (precond/postcond weaken) *)
              MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
              EXISTS_TAC (rand(rator(concl body_th))) THEN CONJ_TAC THENL
               [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
                MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
                EXISTS_TAC (rand(rator(rator(concl body_th)))) THEN CONJ_TAC THENL
                 [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
                  ACCEPT_TAC body_th]];
              (* leg2: bodyQ -> R = IH at p+1                                *)
              ALL_TAC]) THEN
          (* leg2: weaken pre to IH's expanded pre, then apply IH@(p+1)      *)
          FIRST_X_ASSUM(fun ih -> if is_forall(concl ih) then
            (let ih_inst = SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`p+1`;`stackpointer:int64`] ih in
             let ih_pre = rand(rator(rator(snd(dest_imp(concl ih_inst))))) in
             MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC ih_pre THEN CONJ_TAC THENL
              [GEN_TAC THEN BETA_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
               MP_TAC ih_inst THEN ANTS_TAC THENL
                [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]])
            else NO_TAC)]]]]);;

(* ========================================================================= *)
(* eta2 CORRECT: SCALAR_TAIL_FROM_RUN + SCALAR_TAIL_AT_P.                    *)
(*                                                                           *)
(* Corollaries of SCALAR_TAIL_RUN_ETA2 :                                     *)
(*  - FROM_RUN: instantiate d := 136 - 16*N, p := 16*N.  The scalar-tail     *)
(*    contract in the form the main SIMD loop hands off to (entry at a 16-byte *)
(*    block boundary 16*N).                                                  *)
(*  - AT_P: instantiate d := 136 - p.  The scalar-tail contract at an        *)
(*    ARBITRARY exit position p (the form CORRECT's mid-exit legs use).      *)
(* ========================================================================= *)

let MLDSA_REJ_UNIFORM_ETA2_SCALAR_TAIL_AT_P = prove
 (`!res buf table (inlist:byte list) pc p stackpointer.
        LENGTH inlist = 136 /\
        nonoverlapping_modulo (2 EXP 64) (pc, 543) (val res,1024) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 543) (val buf, 136) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 543) (val table,2048) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 136) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table,2048) /\
        p <= 136 /\
        LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) <= 256
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
                  read RIP s = word(pc + 399) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  read RAX s = word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list)) /\
                  read RCX s = word p /\
                  read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list))) s =
                    num_of_wordlist(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist)))
             (\s. read RIP s = word(pc + LENGTH(BUTLAST mldsa_rej_uniform_eta2_tmc)) /\
                  (let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA2_BYTES inlist) in
                   read RAX s = word(LENGTH outlist) /\
                   read(memory :> bytes(res, 4 * LENGTH outlist)) s = num_of_wordlist outlist))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(res,1024)])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`136 - p`; `res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`p:num`;`stackpointer:int64`] SCALAR_TAIL_RUN_ETA2) THEN
  ASM_REWRITE_TAC[LE_REFL]);;

(* ========================================================================= *)
(* eta2 CORRECT: goal statement and proof scaffold.                          *)
(*                                                                           *)
(* Control flow (from the .o; tmc offset = raw - 4):                         *)
(*                                                                           *)
(*  PROLOGUE  raw 0x00..0x59 (tmc pc..pc+85): 17 insns, 5 vector consts      *)
(*    (YMM3=YMM5 nibble mask 0x0f, YMM4 eta2 broadcast 0x02, YMM6 0xe660 x16, *)
(*    YMM7 5 x16), xor eax/ecx.                                              *)
(*                                                                           *)
(*  SIMD LOOP TOP  raw 0x5a (tmc pc+86):                                     *)
(*     0x5a cmp eax,248 ; 0x5f ja scalar    0x65 cmp ecx,120 ; 0x68 ja scalar *)
(*     0x6e.. sub-iter-1 (store 0xb4, mid-guard 0xc8 cmp eax,248/ja)         *)
(*     0xd3.. sub-iter-2 (store 0xfa, mid-guard 0x10e)                       *)
(*     0x115.. sub-iter-3 (store 0x14c, mid-guard 0x150)                     *)
(*     0x157.. sub-iter-4 (store 0x17e; 0x183 popcnt/add; 0x18e jmp top).    *)
(*             SI4 has no mid-guard (unconditional back-edge).               *)
(*                                                                           *)
(*  SCALAR TAIL  raw 0x193 (tmc pc+399):                                     *)
(*     0x193 cmp eax,256 ; jae done    0x19e cmp ecx,136 ; jae done          *)
(*     0x1a6.. byte-at-a-time.                                               *)
(*                                                                           *)
(*  DONE  raw 0x222 (tmc pc+542).                                            *)
(*                                                                           *)
(* The SIMD head guard is cmp ecx,120 (not 136): the SIMD loop exits once    *)
(* 16*i > 120 (first at i=8, pos 128), and the scalar tail (guard cmp        *)
(* ecx,136) consumes the last 8 bytes.  Hence the scalar tail does real      *)
(* work here, unlike eta4 where the SIMD loop consumes all 16 blocks.        *)
(*                                                                           *)
(* WOP predicate: `120 < 16*i \/ 248 < niblen(SUB(0,16i))`.  N=0 and N=1 are *)
(* both impossible; the exit block is at i=N-1.  The scaffold runs:          *)
(*   1. WOP to choose least N, ruling out N=0,1.                             *)
(*   2. Init pc -> pc+86 (prologue): RAX=RCX=0, 5 YMM consts = loop inv i=0. *)
(*   3. ENSURES_WHILE_UP_TAC over N-1 iters with body CLEAN_BODY @ i.        *)
(*   4. Exit block at i=N-1 splits on niblen(16N)<=248:                      *)
(*      - OFFSET arm: head guard cmp ecx,120 fires at pos 16N; CLEAN_BLOCK   *)
(*        finishes the block, then SCALAR_TAIL_AT_P @ 16N runs the tail.     *)
(*      - MID-EXIT arm: a sub-iter mid-guard cmp eax,248 fires inside the    *)
(*        block at the first offset p where niblen(p)>248, then              *)
(*        SCALAR_TAIL_AT_P @ p.                                              *)
(* ========================================================================= *)

(* The eta2 CORRECT goal.  MAYCHANGE ZMM set = full ZMM0..9; CLEAN_BODY's    *)
(* tighter [0;1;2;8;9] is subsumed in the loop-body scaffold step.           *)
let correct_eta2_tm = `
   !res buf table (inlist:byte list) pc.
        LENGTH inlist = 136 /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (res, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (buf, 136) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (table, 2048) /\
        nonoverlapping (res, 1024) (buf, 136) /\
        nonoverlapping (res, 1024) (table, 2048)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [res; buf; table] s /\
                  read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table)
             (\s. read RIP s = word(pc + LENGTH (BUTLAST mldsa_rej_uniform_eta2_tmc)) /\
                  let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA2_BYTES inlist) in
                  let outlen = LENGTH outlist in
                  C_RETURN s = word outlen /\
                  read(memory :> bytes(res,4 * outlen)) s =
                    num_of_wordlist outlist)
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`;;

(* The strengthened loop invariant (adds the 5 YMM broadcast constants).     *)
let CORRECT_LOOPINV_ETA2 =
 `\i s. read RSP s = stackpointer /\
        read (memory :> bytes (buf, 136)) s = num_of_wordlist inlist /\
        read (memory :> bytes (table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
        read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
        read YMM3 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
        read YMM4 s = word 908173248920127022929968509872062022378588115024631874819275168689514742274 /\
        read YMM5 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
        read YMM6 s = word 104203162506446325494781756494581186443189907921581107878096444258040508638816 /\
        read YMM7 s = word 8834370125682169483754557489027840684616615904908870377619408255734579205 /\
        read RAX s = word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list)) /\
        read RCX s = word(16*i) /\
        read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list))) s =
          num_of_wordlist(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist))`;;

(* ========================================================================= *)
(* eta2 CORRECT: CORRECT_SCAFFOLD_TAC.                                       *)
(*                                                                           *)
(* Reduces the CORRECT goal to the single exit-block obligation:             *)
(*   from the loop top pc+86 at pos=16(N-1) (niblen(16(N-1))<=248) reach the *)
(*   done PC pc+LENGTH(BUTLAST tmc) with the CORRECT postcondition.          *)
(*                                                                           *)
(* Phases:                                                                   *)
(*   1. WOP on the eta2 predicate `120 < 16*i \/ 248 < niblen(SUB(0,16i))`.  *)
(*      (120 = eta2 SIMD head guard `cmp ecx,0x78`.)                         *)
(*   2. Rule out N=0 (both disjuncts false at i=0) and N=1 (120<16 false;    *)
(*      niblen(16)<=32<248).                                                 *)
(*   3. Init pc -> pc+86 via the 17-insn prologue (inline; the two int16     *)
(*      vpinsrw/vpbroadcastw pairs need the COLLAPSE_VPBW_TAC dance, so we   *)
(*      inline rather than X86_STEPS straight).                              *)
(*      Establishes CORRECT_LOOPINV_ETA2 @ i=0.                              *)
(*   4. ENSURES_WHILE_UP_TAC (N-1) pc+86 pc+86 CORRECT_LOOPINV_ETA2:         *)
(*      body = MLDSA_REJ_UNIFORM_ETA2_CLEAN_BODY @ i + frame subsumption     *)
(*      (CLEAN_BODY frame ZMM0;1;2;8;9 subsumed by CORRECT frame ZMM0..9).   *)
(*   5. Leaves the exit-block obligation open + establishes its entry facts  *)
(*      (16*(N-1)<=120, niblen(16(N-1))<=248, outlen0<=248).                 *)
(*                                                                           *)
(* NOTE: for eta2 the least N is ALWAYS 8 (16*8=128>120 fires at N=8, and    *)
(* nothing fires before: 16*7=112<120 and niblen(112)<=224<248).  But the    *)
(* scaffold stays generic over N — the exit-block OFFSET arm collapses       *)
(* niblen(16N)<=248 to 16N=128.                                              *)
(* ========================================================================= *)

(* SUB_LIST-prefix length bound, used to rule out N=1.                       *)
let LENGTH_REJ_SAMPLE_ETA2_BYTES_SUB_LIST_BOUND = prove
 (`!(inlist:byte list) k.
     k <= LENGTH inlist
     ==> LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,k) inlist):int32 list) <= 2 * k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `SUB_LIST(0, k) (inlist:byte list):byte list`
              LENGTH_REJ_SAMPLE_ETA2_BYTES_BOUND) THEN
  ASM_SIMP_TAC[LENGTH_SUB_LIST_0]);;

(* Phase 0/1/2 scaffold. After this, ONE goal remains = the exit-block       *)
(* obligation at pc+86, pos=16(N-1), niblen(16(N-1))<=248.                   *)
let CORRECT_SCAFFOLD_TAC : tactic =
  MAP_EVERY X_GEN_TAC [`res:int64`; `buf:int64`; `table:int64`; `inlist:byte list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES; LENGTH_MLDSA_REJ_UNIFORM_ETA2_TMC] THEN
  STRIP_TAC THEN GHOST_INTRO_TAC `stackpointer:int64` `read RSP` THEN
  (* Phase 1: WOP on the eta2 exit predicate (120 not 256).                  *)
  SUBGOAL_THEN `?i. 120 < 16 * i \/ 248 < LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(0, 16 * i) inlist):int16 list)` MP_TAC THENL
   [EXISTS_TAC `8:num` THEN ARITH_TAC; GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LT] th)) THEN
  SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES] THEN
    REWRITE_TAC[REJ_NIBBLES_ETA2_EMPTY; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  (* N=1 impossible: niblen(16)<=32<248 and 120<16 false                     *)
  ASM_CASES_TAC `N = 1` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = 1`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    REWRITE_TAC[ARITH_RULE `~(120 < 16 * 1)`] THEN
    MP_TAC(ISPECL [`inlist:byte list`; `16`] LENGTH_REJ_SAMPLE_ETA2_BYTES_SUB_LIST_BOUND) THEN
    ASM_REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN
    REWRITE_TAC[ARITH_RULE `16 * 1 = 16`] THEN ARITH_TAC; ALL_TAC] THEN
  (* Phase 2: clean-block loop over N-1 iterations                           *)
  ENSURES_WHILE_UP_TAC `N - 1` `pc + 86` `pc + 86` CORRECT_LOOPINV_ETA2 THEN
  REPEAT CONJ_TAC THENL
   [(* G0 ~(N-1=0) *)
    REPEAT(FIRST_X_ASSUM(MP_TAC o check(fun th->concl th=`~(N=0)`||concl th=`~(N=1)`))) THEN ARITH_TAC;
    (* G1 init pc -> pc+86 (17-insn prologue, vpbroadcastw collapse for YMM6/YMM7) *)
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA2_EXEC (1--10) THEN
    X86_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA2_EXEC "s11" THEN
    X86_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA2_EXEC "s12" THEN
    COLLAPSE_VPBW_TAC `read YMM6 s12` YMM6_CONST_ETA2 THEN
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA2_EXEC (13--13) THEN
    X86_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA2_EXEC "s14" THEN
    X86_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA2_EXEC "s15" THEN
    COLLAPSE_VPBW_TAC `read YMM7 s15` YMM7_CONST_ETA2 THEN
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA2_EXEC (16--17) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_ETA2_BYTES; REJ_NIBBLES_ETA2;
                NIBBLES_OF_BYTES; FILTER; MAP; LENGTH; num_of_wordlist] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_TRIVIAL] THEN CONV_TAC WORD_REDUCE_CONV;
    (* G2 body: CLEAN_BODY @ i + frame subsumption                           *)
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`N:num`;`i:num`;`stackpointer:int64`] MLDSA_REJ_UNIFORM_ETA2_CLEAN_BODY) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `i + 1 < N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i+1` o check(is_forall o concl)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN STRIP_TAC THEN
      REPEAT CONJ_TAC THEN (FIRST [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]); ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_FRAME_SUBSUMED) THEN
    REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN SUBSUMED_MAYCHANGE_TAC;
    (* G3 back-edge: refl                                                    *)
    REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    (* G4 exit obligation -- LEFT OPEN for the exit-block proof              *)
    ALL_TAC] THEN
  (* exit-block entry facts (hyp @ N-1). eta2: 256 -> 120.                   *)
  SUBGOAL_THEN `16 * (N-1) <= 120 /\ LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(0,16*(N-1)) inlist):int16 list) <= 248` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `N-1` o check(is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(N-1)) inlist):int32 list) <= 248` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES]; ALL_TAC];;

(* ========================================================================= *)
(* eta2 CORRECT: EXIT_OFFSET + OFFSET_ARM_TAC (offset arm of the             *)
(* exit block).                                                              *)
(*                                                                           *)
(* After CORRECT_SCAFFOLD_TAC the single remaining goal is the exit block:   *)
(* from the loop top pc+86 at pos=16(N-1) (with niblen(16(N-1))<=248) reach  *)
(* done (pc+542) with the CORRECT postcondition.  The offset arm handles the *)
(* case niblen(16N)<=248.                                                    *)
(*                                                                           *)
(* eta2 control flow:                                                        *)
(*   niblen(16N)<=248 + WOP-disjunct1 (120<16N) + 16(N-1)<=120  =>  16N=128  *)
(*   (128 is the only multiple of 16 in (120,136]) => N=8.  So the offset arm *)
(*   forces 16N=128.                                                         *)
(*                                                                           *)
(*   leg1 (pc+86 pos16(N-1) -> pc+399 pos16N=128):                           *)
(*     leg1a: CLEAN_BLOCK@(N-1) advances pos 16(N-1)->16N (= q56@N).         *)
(*            frame subsumption: CLEAN_BLOCK [ZMM0;1;2;8;9] c CORRECT frame  *)
(*            ZMM0..9, so EXIT_OFFSET's frame is ZMM0..9.                    *)
(*     leg1b: q56@N (pos128) -> head guards: cmp eax,0xf8 (s1, not taken,    *)
(*            niblen(128)<=248) ; ja (s2) ; cmp ecx,0x78=120 (s3, TAKEN,     *)
(*            128>120) ; ja (s4) -> pc+399.                                  *)
(*   leg2 (pc+399 pos128 -> pc+542): SCALAR_TAIL_AT_P @ p=16N=128.           *)
(* ========================================================================= *)

(* The "guard TAKEN, a>k" flag lemma (needed for the eta2 ecx head guard     *)
(* cmp ecx,120 firing at pos 128>120).                                       *)
let exit_offset_eta2_tm = `
  !res buf table (inlist:byte list) pc N stackpointer.
       LENGTH inlist = 136 /\
       nonoverlapping_modulo (2 EXP 64) (pc, 543) (val res,1024) /\
       nonoverlapping_modulo (2 EXP 64) (pc, 543) (val buf, 136) /\
       nonoverlapping_modulo (2 EXP 64) (pc, 543) (val table,2048) /\
       nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 136) /\
       nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table,2048) /\
       16 * N = 128 /\
       LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(0,16*N) inlist):int16 list) <= 248
       ==> ensures x86
            (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
                 read RIP s = word(pc + 86) /\ read RSP s = stackpointer /\
                 read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
                 read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                 read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                 read YMM3 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
                 read YMM4 s = word 908173248920127022929968509872062022378588115024631874819275168689514742274 /\
                 read YMM5 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
                 read YMM6 s = word 104203162506446325494781756494581186443189907921581107878096444258040508638816 /\
                 read YMM7 s = word 8834370125682169483754557489027840684616615904908870377619408255734579205 /\
                 read RAX s = word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*(N-1)) inlist):int32 list)) /\
                 read RCX s = word(16*(N-1)) /\
                 read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*(N-1)) inlist):int32 list))) s =
                   num_of_wordlist(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*(N-1)) inlist)))
            (\s. read RIP s = word(pc + LENGTH(BUTLAST mldsa_rej_uniform_eta2_tmc)) /\
                 (let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA2_BYTES inlist) in
                  read RAX s = word(LENGTH outlist) /\
                  read(memory :> bytes(res, 4 * LENGTH outlist)) s = num_of_wordlist outlist))
            (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
             MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9] ,,
             MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(res,1024)])`;;

(* Q399: post-head-guard state at pc+399, pos=16N=128.                       *)
let q399_eta2 = `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
      read RIP s = word(pc + 399) /\ read RSP s = stackpointer /\
      read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
      read(memory :> bytes(table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
      read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
      read RAX s = word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*N) inlist):int32 list)) /\
      read RCX s = word(16*N) /\
      read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*N) inlist):int32 list))) s =
        num_of_wordlist(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*N) inlist))`;;

(* Q86: loop-top state at pc+86, pos=16N (5 YMM consts).                     *)
let q86_eta2 = `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
      read RIP s = word(pc + 86) /\ read RSP s = stackpointer /\
      read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
      read(memory :> bytes(table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
      read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
      read YMM3 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
      read YMM4 s = word 908173248920127022929968509872062022378588115024631874819275168689514742274 /\
      read YMM5 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
      read YMM6 s = word 104203162506446325494781756494581186443189907921581107878096444258040508638816 /\
      read YMM7 s = word 8834370125682169483754557489027840684616615904908870377619408255734579205 /\
      read RAX s = word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*N) inlist):int32 list)) /\
      read RCX s = word(16*N) /\
      read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*N) inlist):int32 list))) s =
        num_of_wordlist(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*N) inlist))`;;

let EXIT_OFFSET_ETA2 = prove(exit_offset_eta2_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(0,16*N) inlist):int16 list) <= 248` then ACCEPT_TAC th else NO_TAC); ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC q399_eta2 THEN
  CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [(* leg1: pc+86 -> Q399 : CLEAN_BLOCK@(N-1) then head guards *)
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC q86_eta2 THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [(* leg1a: CLEAN_BLOCK@(N-1), post pos=16N = q86 (modulo N-1+1 -> N). *)
      SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL [UNDISCH_TAC `16 * N = 128` THEN ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`N:num`;`N-1`;`stackpointer:int64`] ETA2_CLEAN_BLOCK) THEN
      SUBGOAL_THEN `N - 1 + 1 = N` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN (FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]); ALL_TAC] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_FRAME_SUBSUMED) THEN
      REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN SUBSUMED_MAYCHANGE_TAC;
      (* leg1b: q86 (pc+86 pos16N=128) -> Q399 via head guards.
         Guards stated in 128-form (16*N=128) since the stepper rewrites the flag
         predicates to that form.  cmp eax,248 (s1) not taken [niblen(128)<=248];
         ja (s2); cmp ecx,120 (s3) TAKEN [128>120]; ja (s4) -> pc+399. *)
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,128) inlist):int32 list) <= 248` ASSUME_TAC THENL
       [UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THEN
        SUBST1_TAC(ASSUME `16 * N = 128`) THEN REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~(&(val(word_zx(word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,128) inlist):int32 list)):int64):int32)):int - &248 = &(val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,128) inlist):int32 list)):int64):int32) (word 248):int32))) \/ val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,128) inlist):int32 list)):int64):int32) (word 248):int32) = 0` ASSUME_TAC THENL
       [MATCH_MP_TAC JA_NOT_TAKEN_LE THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(~(&(val(word_zx(word(128):int64):int32)):int - &120 = &(val(word_sub(word_zx(word(128):int64):int32) (word 120):int32))) \/ val(word_sub(word_zx(word(128):int64):int32) (word 120):int32) = 0)` ASSUME_TAC THENL
       [MATCH_MP_TAC JA_TAKEN_GT THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA2_EXEC (1--4) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `16 * N = 128`]) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];
    (* leg2: Q399 -> pc+542 : SCALAR_TAIL_AT_P @ p=16N=128. Weaken precond to AT_P's pre.
       eta2 divergence: AT_P frame is ZMM0..6 but the CORRECT/EXIT_OFFSET frame is ZMM0..9,
       so leg2 closes with ENSURES_FRAME_SUBSUMED (ZMM0..6 c ZMM0..9), not eta4's bare
       ACCEPT_TAC (eta4's frames all coincide at ZMM0..6). *)
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (rand(rator(rator(snd(dest_imp(concl(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`16*N`;`stackpointer:int64`] MLDSA_REJ_UNIFORM_ETA2_SCALAR_TAIL_AT_P))))))) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`16*N`;`stackpointer:int64`]
                   MLDSA_REJ_UNIFORM_ETA2_SCALAR_TAIL_AT_P) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN
        (FIRST [FIRST_ASSUM ACCEPT_TAC;
                ASM_ARITH_TAC;
                (FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` then MP_TAC th else NO_TAC) THEN ARITH_TAC)]);
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_FRAME_SUBSUMED) THEN
        REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN SUBSUMED_MAYCHANGE_TAC]]]);;

(* let-free EXIT_OFFSET so its post matches the scaffold goal post.          *)
let EXIT_OFFSET_ETA2_NOLET = CONV_RULE(TOP_DEPTH_CONV let_CONV) EXIT_OFFSET_ETA2;;

(* OFFSET arm: niblen(16N)<=248 in assumptions -> 16N=128 -> EXIT_OFFSET_ETA2. *)
(* eta2: 256<16N (from WOP disjunct1 + niblen<=248) + 16(N-1)<=120 => 16N=128. *)
let OFFSET_ARM_TAC : tactic =
  SUBGOAL_THEN `16 * N = 128` ASSUME_TAC THENL
   [SUBGOAL_THEN `120 < 16 * N` ASSUME_TAC THENL
     [UNDISCH_TAC `120 < 16 * N \/ 248 < LENGTH (REJ_NIBBLES_ETA2 (SUB_LIST (0,16 * N) inlist):int16 list)` THEN
      REWRITE_TAC[GSYM LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN
      UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THEN
      ARITH_TAC; ALL_TAC] THEN
    (* Reason about N (not 16*N): 120<16*N => N>=8 (16*7=112<=120); 16*(N-1)<=120 with
       N>=1 => 16*N<=136 => N<=8 (16*9=144>136).  So N=8 and 16*N=128.  Deriving N=8 first
       gives ARITH_TAC the divisibility that `16*N in (120,136]` alone lacks over the reals. *)
    SUBGOAL_THEN `N = 8` (fun th -> REWRITE_TAC[th] THEN CONV_TAC NUM_REDUCE_CONV) THEN
    SUBGOAL_THEN `16 * N <= 136` ASSUME_TAC THENL
     [UNDISCH_TAC `16 * (N-1) <= 120` THEN UNDISCH_TAC `~(N=0)` THEN
      SPEC_TAC(`N:num`,`N:num`) THEN INDUCT_TAC THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `120 < 16 * N` THEN UNDISCH_TAC `16 * N <= 136` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MATCH_MP_TAC EXIT_OFFSET_ETA2_NOLET THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THEN
  SUBST1_TAC(ASSUME `16 * N = 128`) THEN REWRITE_TAC[];;

(* ========================================================================= *)
(* eta2 CORRECT: MID-EXIT substrate (pure arith / list algebra) +            *)
(* the 4 MID_EXIT lemma STATEMENTS.                                          *)
(*                                                                           *)
(* The MID-EXIT arm of the exit block (the FALSE branch of ASM_CASES         *)
(* niblen(16N)<=248) needs 4 MID_EXIT lemmas (real-stepping the i=N-1 block  *)
(* up to whichever sub-iter mid-guard fires TAKEN) + MIDEXIT_ARM_TAC (dispatch *)
(* by crossover offset).  This section front-loads everything that needs NO  *)
(* stepping:                                                                 *)
(*                                                                           *)
(*  - RCX4_COLLAPSE: word_zx(word_add(word_zx(word a))(word 4)) = word(a+4). *)
(*    Architecture-generic; the +4 RCX advance the mid-guard counter blocks  *)
(*    emit.                                                                  *)
(*  - REJ_SAMPLE_ETA2_PREFIX_MONO: a<=b => outlen(SUB(0,a))<=outlen(SUB(0,b)). *)
(*  - SUBITER_STEP_BOUND_8_ETA2 / SUBITER_BRIDGE_ETA2:                       *)
(*    processing 4 more bytes appends <=8 samples.                           *)
(*  - OUTLEN0_LE_256_FROM_SUBITER_ETA2: outlen(SUB(0,p))<=248 =>             *)
(*    outlen(SUB(0,p+4))<=256, discharges SCALAR_TAIL_AT_P's <=256 hyp on the *)
(*    mid-exit legs.                                                         *)
(*  - the clean-block guard bound: a clean block's 3 internal guards are all *)
(*    <=248 (used by MID_EXIT_CASE4 setup).                                  *)
(* ========================================================================= *)

(* ---- pure word arithmetic: the RCX +4 collapse ----                       *)
let REJ_SAMPLE_ETA2_PREFIX_MONO = prove
 (`!(inlist:byte list) a b.
     a <= b
     ==> LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,a) inlist):int32 list) <=
         LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,b) inlist):int32 list)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `SUB_LIST(0,b) (inlist:byte list) = APPEND (SUB_LIST(0,a) inlist) (SUB_LIST(a,b-a) inlist)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`inlist:byte list`;`a:num`;`b-a`;`0`] SUB_LIST_SPLIT) THEN
    ASM_SIMP_TAC[ADD_CLAUSES; ARITH_RULE `a <= b ==> a + (b - a) = b`];
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES_APPEND_LE]]);;

(* ---- per-4-byte sample count <= 8 ----                                    *)
let SUBITER_STEP_BOUND_8_ETA2 = prove
 (`!(inlist:byte list) k.
     LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(k,4) inlist):int32 list) <= 8`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `SUB_LIST(k,4) (inlist:byte list)` LENGTH_REJ_SAMPLE_ETA2_BYTES_BOUND) THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC);;

(* ---- 4-byte sub-iter bridge: append + length + <=8 ----                   *)
let SUBITER_BRIDGE_ETA2 = prove
 (`!(inlist:byte list) p.
     p + 4 <= LENGTH inlist
     ==> REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+4) inlist):int32 list =
           APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist))
                  (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(p,4) inlist)) /\
         LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+4) inlist):int32 list) =
           LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) +
           LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(p,4) inlist):int32 list) /\
         LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(p,4) inlist):int32 list) <= 8`,
  REPEAT STRIP_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `p + 4 = 0 + (p + 4)`] THEN
    MP_TAC(ISPECL [`inlist:byte list`;`p:num`;`4`;`0`] SUB_LIST_SPLIT) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REJ_SAMPLE_ETA2_BYTES_APPEND];
    ONCE_REWRITE_TAC[ARITH_RULE `p + 4 = 0 + (p + 4)`] THEN
    MP_TAC(ISPECL [`inlist:byte list`;`p:num`;`4`;`0`] SUB_LIST_SPLIT) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REJ_SAMPLE_ETA2_BYTES_APPEND; LENGTH_APPEND];
    REWRITE_TAC[SUBITER_STEP_BOUND_8_ETA2]]);;

(* ---- tight <=256 after one more sub-iter ----                             *)
let OUTLEN0_LE_256_FROM_SUBITER_ETA2 = prove
 (`!(inlist:byte list) p.
     p + 4 <= LENGTH inlist /\
     LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) <= 248
     ==> LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+4) inlist):int32 list) <= 256`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`inlist:byte list`;`p:num`] SUBITER_BRIDGE_ETA2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> let c=concl th in
    can (find_term (fun t -> t = `REJ_SAMPLE_ETA2_BYTES(SUB_LIST(p,4) inlist):int32 list`)) c
    || c = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) <= 248`))) THEN
  ARITH_TAC);;

(* ========================================================================= *)
(* The 4 MID_EXIT lemma STATEMENTS.                                          *)
(* Shared pre/cframe (eta2 form: pc+86 loop top, 5 YMM consts, ZMM0..9 frame). *)
(* ========================================================================= *)

let midexit_eta2_cframe =
  `MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
   MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9] ,,
   MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes (res,1024)]`;;

let midexit_eta2_pre =
  `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
       read RIP s = word(pc + 86) /\ read RSP s = stackpointer /\
       read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
       read(memory :> bytes(table,2048)) s = num_of_wordlist (mldsa_rej_uniform_table:byte list) /\
       read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
       read YMM3 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
       read YMM4 s = word 908173248920127022929968509872062022378588115024631874819275168689514742274 /\
       read YMM5 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
       read YMM6 s = word 104203162506446325494781756494581186443189907921581107878096444258040508638816 /\
       read YMM7 s = word 8834370125682169483754557489027840684616615904908870377619408255734579205 /\
       read RAX s = word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list)) /\
       read RCX s = word(16*i) /\
       read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list))) s =
         num_of_wordlist(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist))`;;

(* post at a mid-guard-taken exit position pexpr (pc+399, scalar tail entry). *)
let midexit_eta2_post_at pexpr =
  subst [pexpr,`PP:num`]
  `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
       read RIP s = word(pc + 399) /\ read RSP s = stackpointer /\
       read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
       read(memory :> bytes(table,2048)) s = num_of_wordlist (mldsa_rej_uniform_table:byte list) /\
       read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
       read RAX s = word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, PP) inlist):int32 list)) /\
       read RCX s = word(PP) /\
       read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, PP) inlist):int32 list))) s =
         num_of_wordlist(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, PP) inlist))`;;

(* shared nonoverlapping+length hyps (eta2: 543, 136).                       *)
let midexit_eta2_hyps =
  [`LENGTH (inlist:byte list) = 136`;
   `nonoverlapping_modulo (2 EXP 64) (pc, 543) (val(res:int64),1024)`;
   `nonoverlapping_modulo (2 EXP 64) (pc, 543) (val(buf:int64), 136)`;
   `nonoverlapping_modulo (2 EXP 64) (pc, 543) (val(table:int64),2048)`;
   `nonoverlapping_modulo (2 EXP 64) (val(res:int64),1024) (val(buf:int64), 136)`;
   `nonoverlapping_modulo (2 EXP 64) (val(res:int64),1024) (val(table:int64),2048)`;
   `16 * (i + 1) <= 136`];;

let mk_midexit_tm extra_hyps pexpr =
  list_mk_forall([`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`i:num`;`stackpointer:int64`],
   mk_imp(list_mk_conj(midexit_eta2_hyps @ extra_hyps),
     list_mk_comb(`ensures x86`,[midexit_eta2_pre; midexit_eta2_post_at pexpr; midexit_eta2_cframe])));;

(* SUBITER1: mid-guard-1 fires taken at pos 16i+4.                           *)
let midexit1_eta2_tm = mk_midexit_tm
  [`LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i) inlist):int32 list) <= 248`;
   `248 < LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list)`]
  `16*i+4`;;

(* SUBITER2: mid-guard-2 fires taken at pos 16i+8.                           *)
let midexit2_eta2_tm = mk_midexit_tm
  [`LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) <= 248`;
   `248 < LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)`]
  `16*i+8`;;

(* SUBITER3: mid-guard-3 fires taken at pos 16i+12.                          *)
let midexit3_eta2_tm = mk_midexit_tm
  [`LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) <= 248`;
   `248 < LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)`]
  `16*i+12`;;

(* CASE4: all 3 internal guards clean, head-guard1 fires taken at back-edge pos 16(i+1). *)
let midexit4_eta2_tm = mk_midexit_tm
  [`LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) <= 248`;
   `248 < LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list)`]
  `16*(i+1)`;;

(* ========================================================================= *)
(* eta2 CORRECT: the bound-flexible MID-EXIT prefix.                         *)
(*                                                                           *)
(* ETA2_MIDEXIT_PREFIX_TAC opens the i-th SIMD loop iteration from the loop  *)
(* top (pc+86) and reaches the post-SI1-store state (s20), same as           *)
(* `ETA2_PREFIX_TO_S11_TAC THEN ETA2_SI1_FOLD` — BUT with a BOUND-FLEXIBLE   *)
(* derivation of `niblen_sample(16i) <= 248`.                                *)
(*                                                                           *)
(* WHY a duplicate opening: the clean-body opening (ETA2_PREFIX_OPEN_TAC)    *)
(* derives `niblen_sample(16i) <= 248` FROM `niblen(16(i+1)) <= 248` via     *)
(* NIBLEN_PREFIX_MONO.  The MID_EXIT goals do NOT have that hyp — instead they *)
(* carry `niblen_sample(16i+4k) <= 248` DIRECTLY (k depends on which sub-iter *)
(* mid-guard fires).  So we replace that one SUBGOAL_THEN's proof with       *)
(* FIRST[ ACCEPT ; REJ_SAMPLE_ETA2_PREFIX_MONO from a later <=248 bound ].   *)
(* Everything else in the opening + the s5-s11 SIMD chain is bound-independent *)
(* and reuses the already-bound helpers.                                     *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* Flexible opening: loop top pc+86 -> s4 = pc+106 (both head guards not taken),
   with chunk0/outlen0 abbreviated, both JA-not-taken facts established.  Copy of
   ETA2_PREFIX_OPEN_TAC with the ONE bound subgoal made flexible. *)
let ETA2_MIDEXIT_OPEN_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `16 * i <= 120` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i + 1) <= 136` THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`buf:int64`;`136`;`inlist:byte list`;`i:num`;`s0:x86state`] SUB_LIST_16_BYTES_FROM_INT128) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `16 * (i + 1) <= 136` THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `chunk0 = read(memory:>bytes128(word_add buf (word(16*i)))) s0` THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) <= 248` ASSUME_TAC THENL
   [FIRST [FIRST_ASSUM ACCEPT_TAC;
           (* mid-exit cases 2/3/4: derive from a later sample bound niblen(16i+4k)<=248 *)
           (FIRST_X_ASSUM(fun th -> match concl th with
              Comb(Comb(Const("<=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA2_BYTES",_),_))),k) when k=`248`
                -> MP_TAC th | _ -> NO_TAC) THEN
            MATCH_MP_TAC(ARITH_RULE `a <= b ==> b <= 248 ==> a <= 248`) THEN
            MATCH_MP_TAC REJ_SAMPLE_ETA2_PREFIX_MONO THEN ARITH_TAC)]; ALL_TAC] THEN
  ABBREV_TAC `outlen0 = LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list)` THEN
  FIRST_ASSUM(fun th -> if concl th =
      `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) = outlen0`
    then (RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) else NO_TAC) THEN
  MP_TAC(SPECL [`outlen0:num`;`248`] JA_NOT_TAKEN_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`16*i`;`120`] JA_NOT_TAKEN_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  VAL_INT64_TAC `outlen0:num` THEN
  X86_STEPS_TAC EXEC (1--2) THEN
  SUBGOAL_THEN `read RIP s2 = word(pc + 97):int64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can(find_term((=)`&248:int`))(concl th)
                           then ASSUME_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if can(find_term((=)`pc + 399`))(concl th) then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC; ALL_TAC] THEN
  X86_STEPS_TAC EXEC (3--4) THEN
  SUBGOAL_THEN `read RIP s4 = word(pc + 106):int64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can(find_term((=)`&120:int`))(concl th)
                           then ASSUME_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if can(find_term((=)`pc + 399`))(concl th) then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC; ALL_TAC];;

(* s5-s8 SIMD nibble chain (copy of ETA2_PREFIX_TO_S8_TAC tail — the
   part after ETA2_PREFIX_OPEN_TAC).  Lands read YMM0 s8 = F0NIB_CHUNK0. *)
let ETA2_MIDEXIT_S5_S8_TAC : tactic =
  X86_VSTEPS_TAC EXEC (5--5) THEN
  SUBGOAL_THEN `val(word(16*i):int64) = 16*i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `16*i <= 120` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word(16*i):int64) = 16*i`; ARITH_RULE `1 * x = x`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read (memory :> bytes128 (word_add buf (word (16 * i)))) s4 = chunk0`]) THEN
  SUBGOAL_THEN `read YMM0 s5 = usimd16 (\b:byte. word_zx b:int16) chunk0:int256` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can(find_term((=)`read YMM0 s5`))(lhand(concl th)) then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DROP_WORDJOIN_TAC THEN PURGE_STALE_STATES_TAC ["s4"] THEN
  X86_VSTEPS_TAC EXEC (6--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s5 = usimd16 (\b:byte. word_zx b:int16) chunk0:int256`]) THEN
  X86_VSTEPS_TAC EXEC (7--7) THEN X86_VSTEPS_TAC EXEC (8--8) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM3 s5 =
    word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256`]) THEN
  SUBGOAL_THEN (mk_eq(`read YMM0 s8:int256`, F0NIB_CHUNK0)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can(find_term((=)`read YMM0 s8`))(lhand(concl th)) then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DROP_WORDJOIN_TAC THEN PURGE_STALE_STATES_TAC ["s5";"s6";"s7"];;

(* Full bound-flexible prefix, reaching the post-SI1-store state s20.        *)
let ETA2_MIDEXIT_PREFIX_TAC : tactic =
  ETA2_MIDEXIT_OPEN_TAC THEN
  ETA2_MIDEXIT_S5_S8_TAC THEN
 (* s9 accept-vpsubb + 4 maskbit foralls                                     *)
  X86_VSTEPS_TAC EXEC (9--9) THEN
  ABBREV_TAC `f1bnd:int256 = read YMM1 s9` THEN
  ETA2_MASKBIT_ASSUME_TAC 0 THEN
  ETA2_MASKBIT_ASSUME_TAC 8 THEN
  ETA2_MASKBIT_ASSUME_TAC 16 THEN
  ETA2_MASKBIT_ASSUME_TAC 24 THEN
  (* drop f1bnd def, s10 vpmovmskb + s11 centre-vpsubb + 4 gather foralls
 *)
  REPEAT(FIRST_X_ASSUM(fun th ->
     if is_eq(concl th) && lhand(concl th) = `f1bnd:int256`
     then ALL_TAC else failwith "keep")) THEN
  X86_VSTEPS_TAC EXEC (10--10) THEN
  X86_VSTEPS_TAC EXEC (11--11) THEN
  ABBREV_TAC `f0sub:int256 = read YMM0 s11` THEN
  eta2_gather_block g1_eta2 (eta2_ellist 0)  false THEN
  eta2_gather_block g2_eta2 (eta2_ellist 32) true THEN
  eta2_gather_block g3_eta2 (eta2_ellist 64) false THEN
  eta2_gather_block g4_eta2 (eta2_ellist 96) true THEN
  (* SI1 store fold (bound-independent), reaching folded store at s20        *)
  ETA2_SI1_FOLD;;

(* ========================================================================= *)
(* eta2 CORRECT: MID_EXIT_SUBITER1 (sub-iter-1 mid-guard TAKEN).             *)
(*                                                                           *)
(* Proves: from the loop top (pc+86) at pos 16i, when sub-iter-1's accept-count *)
(* push takes niblen_sample past 248 (mid-guard-1 fires TAKEN), control jumps *)
(* to the scalar tail (pc+399) with RCX=16i+4, RAX=niblen(16i+4), and the res *)
(* buffer holding REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16i+4)).                  *)
(*                                                                           *)
(* Structure:                                                                *)
(* ETA2_MIDEXIT_PREFIX_TAC -> s20, SI1 store folded to SUB_LIST(0,16i+4)     *)
(*   count facts: 16i+4<=LENGTH, niblen(16i+4)<=256, <2^32                   *)
(*   pop_len: word_popcount(mask byte0) = LENGTH(REJ_NIBBLES_ETA2 block0)    *)
(*   bridge: outlen0 + block0len = niblen_sample(16i+4)                      *)
(*   rax_red0 + ja_taken (JA_TAKEN_GT, since niblen(16i+4) > 248)            *)
(*   X86_STEPS (21--26); resolve RIP s26 = pc+399 (mid-guard-1 TAKEN)        *)
(*   ENSURES_FINAL + RAX collapse (bridge) + RCX collapse (RCX4_COLLAPSE)    *)
(*                                                                           *)
(* eta2 counter block s21-26: popcnt(s21)/add(s22)/shr(s23)/add(s24)/cmp(s25)/ *)
(* ja(s26).  The SI1 store is ALREADY folded by the prefix (ETA2_SI1_FOLD is *)
(* inside ETA2_MIDEXIT_PREFIX_TAC), so the store fact is in place before the *)
(* counter.  The mid-guard ja is s26; TAKEN target = pc+399.                 *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

let MID_EXIT_SUBITER1_ETA2 = prove(midexit1_eta2_tm,
  ETA2_MIDEXIT_PREFIX_TAC THEN
  (* count facts                                                             *)
  SUBGOAL_THEN `16 * i + 4 <= LENGTH(inlist:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i+1) <= 136` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=136` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) <= 256` ASSUME_TAC THENL
   [MATCH_MP_TAC OUTLEN0_LE_256_FROM_SUBITER_ETA2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) <= 256` THEN ARITH_TAC; ALL_TAC] THEN
  (* pop_len: word_popcount(mask byte0) = LENGTH(REJ_NIBBLES_ETA2 block0).
     Run the popcnt/add/shr/add first (s21-24) to expose R9's popcount term. *)
  X86_STEPS_TAC EXEC (21--24) THEN
  MP_TAC(ISPECL[`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `LENGTH(inlist:byte list) = 136` THEN
    UNDISCH_TAC `16 * i <= 120` THEN ARITH_TAC; STRIP_TAC] THEN
  (* fold mask8's bitsum def into the popcount-bearing assumptions (but not into
     maskbit_tgt or TABLE_ENTRY facts). *)
  W(fun (asl,w) ->
     let m8def = find (fun th -> match concl th with Comb(Comb(Const("=",_),_),Var("mask8",_)) -> true | _ -> false) (map snd asl) in
     RULE_ASSUM_TAC(fun th -> if concl th = maskbit_tgt ||
        can(find_term(fun u->match u with Const("TABLE_ENTRY",_)->true|_->false))(concl th)
        then th else REWRITE_RULE[GSYM m8def] th)) THEN
  W(fun (asl,w) ->
    let r9 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("R9",_)),Var("s24",_))),_) -> true | _ -> false) asl in
    let goal_pc = find_term (fun t -> match t with Comb(Const("word_popcount",_),_) -> true | _ -> false) (concl(snd r9)) in
    let low8 = `bitval(bit 7 (word_subword (f1bnd:int256) (0,8):byte)) + bitval(bit 7 (word_subword f1bnd (8,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (16,8):byte)) + bitval(bit 7 (word_subword f1bnd (24,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (32,8):byte)) + bitval(bit 7 (word_subword f1bnd (40,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (48,8):byte)) + bitval(bit 7 (word_subword f1bnd (56,8):byte))` in
    let mr = CONV_RULE(DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV)
               (SPEC `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` MOD_RED) in
    let popeq = prove(mk_eq(goal_pc, low8),
      REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; MOD_MOD_EXP_MIN] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; mr] THEN
      MAP_EVERY (fun b -> BOOL_CASES_TAC b)
        [`bit 7 (word_subword (f1bnd:int256) (0,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (8,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (16,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (24,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (32,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (40,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (48,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (56,8):byte)`] THEN
      REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV) in
    let maskbit = snd(find (fun (_,th) -> let c=concl th in is_forall c &&
        can(find_term(fun u->u=`f1bnd:int256`))c && can(find_term(fun u->match u with Comb(Const("bit",_),_)->true|_->false))c &&
        not(can(find_term(fun u->match u with Const("word_zx",_)->true|_->false))c) &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (24,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (32,8):byte`))c)) asl) in
    let mb_tm = concl maskbit in
    let blk0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
           (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
    let blkeq = mk_eq(low8, `LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i,4) inlist):int16 list)`) in
    let blk0_tm = concl(snd blk0) in
    let bsum_raw = prove(mk_imp(mb_tm, mk_imp(blk0_tm, blkeq)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN DISCH_THEN(fun b -> REWRITE_TAC[b]) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER_ETA2] THEN
      ASM_SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let bsum = MP (MP bsum_raw maskbit) (snd blk0) in
    let pop_len = TRANS popeq bsum in
    ASSUME_TAC pop_len) THEN
  (* bridge: outlen0 + niblen(SUB(16i,4)) = niblen_sample(16i+4)             *)
  SUBGOAL_THEN `outlen0 + LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i`] SUBITER_BRIDGE_ETA2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN
    UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i) inlist):int32 list) = outlen0` THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  (* lt32 + rax_red0 + ja_taken                                              *)
  SUBGOAL_THEN `outlen0 + LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i,4) inlist):int16 list) < 2 EXP 32` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),_)->true|_->false) then SUBST1_TAC th else NO_TAC) THEN
    UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) < 2 EXP 32` THEN REWRITE_TAC[]; ALL_TAC] THEN
  W(fun (asl,w) ->
    let block0len = `LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i,4) inlist):int16 list)` in
    let sum = mk_binop `(+):num->num->num` `outlen0:num` block0len in
    let lt32 = snd(find (fun (_,th) -> concl th = mk_binop `(<):num->num->bool` sum `2 EXP 32`) asl) in
    let pop_len = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl) in
    let bridge = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),_) -> true | _ -> false) asl) in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let gt248 = REWRITE_RULE[SYM bridge] (snd(find (fun (_,th) -> concl th = `248 < LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list)`) asl)) in
    let ja_taken = MP (ISPECL [sum; `248`] JA_TAKEN_GT) (CONJ gt248 lt32) in
    ASSUME_TAC pop_len THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja_taken) THEN
  X86_STEPS_TAC EXEC (25--26) THEN
  (* resolve RIP s26 = pc+399 (mid-guard1 TAKEN)                             *)
  SUBGOAL_THEN `read RIP s26 = word (pc + 399):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let blk0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
             (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
      let rax_red0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
      let ja = find (fun (_,th) -> is_neg(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`248`))(concl th)) asl in
      FIRST_ASSUM(fun th -> if can(find_term(fun u->u=`pc + 399`))(concl th) then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[GSYM(snd blk0)] THEN REWRITE_TAC[snd rax_red0] THEN
      REWRITE_TAC[snd ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* discharge RAX collapse (bridge->niblen), RCX collapse                   *)
  W(fun (asl,w) ->
    let blk0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
           (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
    let rax_red0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
    let bridge = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),_) -> true | _ -> false) asl in
    REWRITE_TAC[GSYM(snd blk0); snd rax_red0; snd bridge]) THEN
  W(fun (asl,w) ->
    let ntake = MP (ISPECL [`LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list)`;`248`] JA_TAKEN_GT)
                   (CONJ (ASSUME `248 < LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list)`)
                         (ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) < 2 EXP 32`)) in
    REWRITE_TAC[ntake]) THEN
  (* RCX collapse                                                            *)
  SUBGOAL_THEN `val(word(16*i):int64) = 16*i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `16*i<=120` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `16*i` RCX4_COLLAPSE) THEN
  ANTS_TAC THENL [UNDISCH_TAC `16*i<=120` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* ========================================================================= *)
(* eta2 CORRECT: MID_EXIT_SUBITER2 (mid-guard-2 fires TAKEN).                *)
(*                                                                           *)
(* Sub-iter-1's mid-guard is NOT taken (niblen(16i+4)<=248), then sub-iter-2's *)
(* mid-guard fires TAKEN (niblen(16i+8)>248) -> pc+399 with RCX=16i+8,       *)
(* RAX=niblen(16i+8), res holding REJ_SAMPLE(0,16i+8).                       *)
(*                                                                           *)
(* Structure:                                                                *)
(* ETA2_MIDEXIT_PREFIX_TAC -> s20, SI1 store folded                          *)
(*   ETA2_MG1_NT_TAC                          -> s26, mid-guard-1 NOT taken  *)
(*                                               (pc+207), bound from DIRECT *)
(*                                               niblen(16i+4)<=248 via bridge *)
(* ETA2_SI2_FOLD -> s35, SI2 store folded                                    *)
(*   ETA2_SI2_MG2_TAKEN_TAC                   -> s41, mid-guard-2 TAKEN pc+399 *)
(*   ENSURES_FINAL + RAX/RCX discharge                                       *)
(*                                                                           *)
(* NEW tactics here:                                                         *)
(* - ETA2_MG1_NT_TAC = ETA2_SI1_COUNTER_TAC with the ONE bound step swapped: *)
(*    instead of SUBITER_OUTLEN_BOUND_1 (needs niblen(16(i+1))<=248), derive *)
(*    outlen0+block0len<=248 via SUBITER_BRIDGE_ETA2 + the DIRECT hyp        *)
(*    niblen_sample(16i+4)<=248 (FIRST[ACCEPT; PREFIX_MONO]).                *)
(* - ETA2_SI2_MG2_TAKEN_TAC = ETA2_SI2_MG_TAC with the bound swapped to      *)
(*    gt248/lt32 + JA_TAKEN_GT (mid-guard-2 fires) + RIP pc+399.             *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* Shared RIP-resolution step for the eta2 mid-guard twins.  The value chain  *)
(* grabs the assumption mentioning `pc + pcoff` directly; the memory-safety    *)
(* chain instead finds the RIP-COND assumption at state s<st> by shape (the    *)
(* anchored events fact also mentions pc+pcoff, so the bare find_term would    *)
(* grab it).                                                                   *)
let eta2_rip_mp (memsafe:bool) (pcoff:int) (st:int) : tactic =
  let pctm = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral pcoff) in
  let stv = mk_var("s"^string_of_int st,`:x86state`) in
  if memsafe then
    W(fun (asl,_) ->
      let ifrip = find (fun (_,th) -> match concl th with
         Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),v)),r) ->
           v=stv && (match r with Comb(Comb(Comb(Const("COND",_),_),_),_) -> true | _ -> false)
         | _ -> false) asl in
      MP_TAC (snd ifrip))
  else
    FIRST_ASSUM(fun th -> if can(find_term(fun u->u=pctm))(concl th) then MP_TAC th else NO_TAC);;

(* ETA2_MG1_NT_TAC: SI1 counter block s21-26, mid-guard-1 NOT taken (pc+207), *)
(* bound derived from the DIRECT hyp niblen_sample(16i+4)<=248 (via bridge)  *)
(* rather than SUBITER_OUTLEN_BOUND_1.                                       *)
let mk_eta2_mg1_nt (memsafe:bool) : tactic =
  X86_STEPS_TAC EXEC (21--24) THEN
  MP_TAC(ISPECL[`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `LENGTH(inlist:byte list) = 136` THEN
    UNDISCH_TAC `16 * i <= 120` THEN ARITH_TAC; STRIP_TAC] THEN
  W(fun (asl,w) ->
     let m8def = find (fun th -> match concl th with Comb(Comb(Const("=",_),_),Var("mask8",_)) -> true | _ -> false) (map snd asl) in
     RULE_ASSUM_TAC(fun th -> if concl th = maskbit_tgt ||
        can(find_term(fun u->match u with Const("TABLE_ENTRY",_)->true|_->false))(concl th)
        then th else REWRITE_RULE[GSYM m8def] th)) THEN
  (* pop_len (identical to SI1_COUNTER: R9 s24 popcount = block0len)         *)
  W(fun (asl,w) ->
    let r9 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("R9",_)),Var("s24",_))),_) -> true | _ -> false) asl in
    let goal_pc = find_term (fun t -> match t with Comb(Const("word_popcount",_),_) -> true | _ -> false) (concl(snd r9)) in
    let low8 = `bitval(bit 7 (word_subword (f1bnd:int256) (0,8):byte)) + bitval(bit 7 (word_subword f1bnd (8,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (16,8):byte)) + bitval(bit 7 (word_subword f1bnd (24,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (32,8):byte)) + bitval(bit 7 (word_subword f1bnd (40,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (48,8):byte)) + bitval(bit 7 (word_subword f1bnd (56,8):byte))` in
    let mr = CONV_RULE(DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV)
               (SPEC `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` MOD_RED) in
    let popeq = prove(mk_eq(goal_pc, low8),
      REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; MOD_MOD_EXP_MIN] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; mr] THEN
      MAP_EVERY (fun b -> BOOL_CASES_TAC b)
        [`bit 7 (word_subword (f1bnd:int256) (0,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (8,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (16,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (24,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (32,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (40,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (48,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (56,8):byte)`] THEN
      REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV) in
    let maskbit = snd(find (fun (_,th) -> let c=concl th in is_forall c &&
        can(find_term(fun u->u=`f1bnd:int256`))c && can(find_term(fun u->match u with Comb(Const("bit",_),_)->true|_->false))c &&
        not(can(find_term(fun u->match u with Const("word_zx",_)->true|_->false))c) &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (24,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (32,8):byte`))c)) asl) in
    let mb_tm = concl maskbit in
    let blk0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
           (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
    let blkeq = mk_eq(low8, `LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i,4) inlist):int16 list)`) in
    let blk0_tm = concl(snd blk0) in
    let bsum_raw = prove(mk_imp(mb_tm, mk_imp(blk0_tm, blkeq)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN DISCH_THEN(fun b -> REWRITE_TAC[b]) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER_ETA2] THEN
      ASM_SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let bsum = MP (MP bsum_raw maskbit) (snd blk0) in
    let pop_len = TRANS popeq bsum in
    ASSUME_TAC pop_len) THEN
  (* bridge: outlen0 + niblen(SUB(16i,4)) = niblen_sample(16i+4)             *)
  SUBGOAL_THEN `outlen0 + LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i`] SUBITER_BRIDGE_ETA2) THEN
    ANTS_TAC THENL [UNDISCH_TAC `16 * (i+1) <= 136` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=136` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN
    UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i) inlist):int32 list) = outlen0` THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  (* bnd: outlen0 + block0len <= 248, from the DIRECT niblen(16i+4)<=248 hyp *)
  SUBGOAL_THEN `outlen0 + LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i,4) inlist):int16 list) <= 248` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),_)->true|_->false) then SUBST1_TAC th else NO_TAC) THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           (FIRST_X_ASSUM(fun th -> match concl th with
              Comb(Comb(Const("<=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA2_BYTES",_),_))),k) when k=`248`
                -> MP_TAC th | _ -> NO_TAC) THEN
            MATCH_MP_TAC(ARITH_RULE `a <= b ==> b <= 248 ==> a <= 248`) THEN
            MATCH_MP_TAC REJ_SAMPLE_ETA2_PREFIX_MONO THEN ARITH_TAC)]; ALL_TAC] THEN
  W(fun (asl,w) ->
    let block0len = `LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i,4) inlist):int16 list)` in
    let sum = mk_binop `(+):num->num->num` `outlen0:num` block0len in
    let bnd = snd(find (fun (_,th) -> concl th = mk_binop `(<=):num->num->bool` sum `248`) asl) in
    let pop_len = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl) in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let ja = MP (ISPECL[sum; `248`] JA_NOT_TAKEN_LE) (CONJ bnd (ARITH_RULE `248 < 2 EXP 32`)) in
    ASSUME_TAC pop_len THEN ASSUME_TAC bnd THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja) THEN
  X86_STEPS_TAC EXEC (25--26) THEN
  SUBGOAL_THEN `read RIP s26 = word (pc + 207):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let blk0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
             (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
      let rax_red0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
      let ja = find (fun (_,th) -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th)) asl in
      eta2_rip_mp memsafe 207 26 THEN
      REWRITE_TAC[GSYM(snd blk0)] THEN REWRITE_TAC[snd rax_red0] THEN
      REWRITE_TAC[snd ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  W(fun (asl,w) ->
    let pl = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
    let rr = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
    RULE_ASSUM_TAC(REWRITE_RULE[snd pl]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd rr]));;

let ETA2_MG1_NT_TAC : tactic = mk_eta2_mg1_nt false;;

(* ------------------------------------------------------------------------- *)
(* ETA2_SI2_MG2_TAKEN_TAC: SI2 counter s36-41, mid-guard-2 fires TAKEN (pc+399). *)
(* From s35 (post-SI2-fold).                                                 *)
let mk_eta2_si2_mg2_taken (memsafe:bool) : tactic =
  X86_STEPS_TAC EXEC (36--39) THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
    let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
    let popcnt2 = REWRITE_RULE[m8b_def]
       (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE1)) in
    let lanesum8 = rand(concl popcnt2) in
    let mb2 = find_a (fun th -> let c=concl th in is_forall c &&
       can(find_term(fun u->u=`f1bnd:int256`))c &&
       can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),c) -> c=`8` | _ -> false))c) in
    let mb2_tm = concl mb2 in
    let i_le = find_a (fun th -> concl th = `16 * i <= 120`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
    let blk16 = find_a (fun th -> is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" &&
            length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=120 ==> 16*i+16<=136`) i_le)) blk16) in
    let blk1_eq = el 1 (CONJUNCTS bb) in
    let block1 = `[word_subword (chunk0:int128) (32,8); word_subword chunk0 (40,8);
                   word_subword chunk0 (48,8); word_subword chunk0 (56,8)]:byte list` in
    let block1len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA2`, block1)) in
    let bsum2_raw = prove(mk_imp(mb2_tm, mk_eq(lanesum8, block1len_x)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV)
            (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER_ETA2] THEN
      SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let pop_len2 = REWRITE_RULE[GSYM blk1_eq] (TRANS popcnt2 (MP bsum2_raw mb2)) in
    ASSUME_TAC pop_len2) THEN
  (* bridge2: acc1 + block1len = niblen_sample(16i+8)                        *)
  SUBGOAL_THEN `acc1 + LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i+4,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+4`] SUBITER_BRIDGE_ETA2) THEN
    ANTS_TAC THENL [UNDISCH_TAC `16 * (i+1) <= 136` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=136` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES; ARITH_RULE `(16*i+4)+4 = 16*i+8`] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) = acc1` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) < 2 EXP 32` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+4`] OUTLEN0_LE_256_FROM_SUBITER_ETA2) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `16 * (i+1) <= 136` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=136` THEN ARITH_TAC;
        FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) = acc1` then SUBST1_TAC th else NO_TAC) THEN FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(16*i+4)+4 = 16*i+8`] THEN ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let block1len = `LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i+4,4) inlist):int16 list)` in
    let sum = mk_binop `(+):num->num->num` `acc1:num` block1len in
    let bridge2 = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),_) -> true | _ -> false) asl) in
    let lt32 = REWRITE_RULE[SYM bridge2] (snd(find (fun (_,th) -> concl th = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) < 2 EXP 32`) asl)) in
    let pop_len2 = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl) in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let gt248 = REWRITE_RULE[SYM bridge2] (snd(find (fun (_,th) -> concl th = `248 < LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)`) asl)) in
    let ja_taken = MP (ISPECL [sum; `248`] JA_TAKEN_GT) (CONJ gt248 lt32) in
    ASSUME_TAC pop_len2 THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja_taken) THEN
  X86_STEPS_TAC EXEC (40--41) THEN
  SUBGOAL_THEN `read RIP s41 = word (pc + 399):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let pop_len2_old = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
      let zbe = MP (SPEC `val (mask8b:int64) MOD 256` zxbyte_eq) (ARITH_RULE `val (mask8b:int64) MOD 256 < 256`) in
      let pop_len2_typed = TRANS (AP_TERM `word_popcount:int32->num` zbe) (snd pop_len2_old) in
      let rax_red0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
      let ja = find (fun (_,th) -> is_neg(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`acc1:num`))(concl th)) asl in
      eta2_rip_mp memsafe 399 41 THEN
      REWRITE_TAC[pop_len2_typed] THEN REWRITE_TAC[snd rax_red0] THEN
      REWRITE_TAC[snd ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC];;

let ETA2_SI2_MG2_TAKEN_TAC : tactic = mk_eta2_si2_mg2_taken false;;

(* MID_EXIT_SUBITER2_ETA2: sub-iter-2 mid-guard fires TAKEN at pos 16i+8.    *)
let mk_midexit2_eta2 (memsafe:bool) (prefix:tactic) (disch:tactic) : tactic =
prefix THEN
  SUBGOAL_THEN `16 * i + 4 <= LENGTH(inlist:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i+1) <= 136` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=136` THEN ARITH_TAC; ALL_TAC] THEN
  (mk_eta2_mg1_nt memsafe) THEN
  ETA2_SI2_FOLD THEN
  (mk_eta2_si2_mg2_taken memsafe) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* RAX collapse (pop_len2_typed -> bridge2 -> niblen(16i+8)); ja_taken guard; RCX. *)
  W(fun (asl,w) ->
    let pop_len2 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
    let zbe = MP (SPEC `val (mask8b:int64) MOD 256` zxbyte_eq) (ARITH_RULE `val (mask8b:int64) MOD 256 < 256`) in
    let pop_len2_typed = TRANS (AP_TERM `word_popcount:int32->num` zbe) (snd pop_len2) in
    let rax_red0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
    let bridge2 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),_) -> true | _ -> false) asl in
    REWRITE_TAC[pop_len2_typed; snd rax_red0; snd bridge2]) THEN
  W(fun (asl,w) ->
    let ntake = MP (ISPECL [`LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)`;`248`] JA_TAKEN_GT)
                   (CONJ (ASSUME `248 < LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)`)
                         (ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) < 2 EXP 32`)) in
    REWRITE_TAC[ntake]) THEN
  (* RCX collapse: double +4 nest (16i -> 16i+4 -> 16i+8)                    *)
  MP_TAC(SPEC `16*i` RCX4_COLLAPSE) THEN ANTS_TAC THENL [UNDISCH_TAC `16*i<=120` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(SPEC `16*i+4` RCX4_COLLAPSE) THEN ANTS_TAC THENL [UNDISCH_TAC `16*i<=120` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `16*i+4+4 = 16*i+8`] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  (if memsafe then CONJ_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; disch] else TRY(AP_TERM_TAC THEN ARITH_TAC));;
let MID_EXIT_SUBITER2_ETA2 = prove(midexit2_eta2_tm, mk_midexit2_eta2 false ETA2_MIDEXIT_PREFIX_TAC ALL_TAC);;

(* ========================================================================= *)
(* eta2 CORRECT: MID_EXIT_SUBITER3 (mid-guard-3 fires TAKEN).                *)
(*                                                                           *)
(* Sub-iters 1+2 mid-guards NOT taken (niblen(16i+4)<=248, niblen(16i+8)<=248), *)
(* then sub-iter-3's mid-guard fires TAKEN (niblen(16i+12)>248) -> pc+399 with *)
(* RCX=16i+12, RAX=niblen(16i+12), res holding REJ_SAMPLE(0,16i+12).         *)
(*                                                                           *)
(* Structure:                                                                *)
(* ETA2_MIDEXIT_PREFIX_TAC -> s20 SI1 store folded                           *)
(* ETA2_MG1_NT_TAC -> s26 mg1 NOT taken (pc+207)                             *)
(* ETA2_SI2_FOLD -> s35 SI2 store folded                                     *)
(*   ETA2_MG2_NT_TAC                     -> s41   mg2 NOT taken (pc+273)     *)
(* ETA2_SI3_FOLD -> s50 SI3 store folded                                     *)
(*   ETA2_SI3_MG3_TAKEN_TAC             -> s56   mg3 TAKEN (pc+399)          *)
(*   ENSURES_FINAL + RAX/RCX discharge                                       *)
(*                                                                           *)
(* NEW tactics:                                                              *)
(*  - ETA2_MG2_NT_TAC = ETA2_SI2_MG2_TAKEN_TAC's pop_len2/bridge2 build but  *)
(*    JA_NOT_TAKEN_LE + RIP pc+273 (bound from DIRECT niblen(16i+8)<=248 via *)
(*    the bridge), ending with an RAX-fold so ETA2_SI3_FOLD's acc2 abbrev+RAX *)
(*    match works.                                                           *)
(*  - ETA2_SI3_MG3_TAKEN_TAC = ETA2_SI3_MG (build pop_len3/bridge3) then     *)
(*    gt248/lt32 + JA_TAKEN_GT -> RIP pc+399.                                *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* ETA2_SI3_BODY3_TAC: the SI3 store fold for the MID-EXIT context.  The     *)
(* clean-body ETA2_SI3_FOLD derives the                                      *)
(* acc2<=248 bound via SUBITER_OUTLEN_BOUND_3 (needs niblen(16(i+1))<=248),  *)
(* which is ABSENT in the mid-exit goals.  ETA2_SI3_BODY3 instead abbrevs acc2 *)
(* and derives acc2<=248 from the DIRECT hyp niblen_sample(16i+8)<=248 (via  *)
(* ACC2_IDENT giving niblen_sample(16i+8)=acc2), then runs the identical SI3 *)
(* step/refold/fold body as ETA2_SI3_FOLD's post-PRE portion.                *)
(* NOTE MG2_NT does NOT abbrev acc2 (unlike the clean-body SI2 counter), so the *)
(* ABBREV must happen here.                                                  *)
let ETA2_SI3_PRE3_TAC : tactic =
  ABBREV_TAC `acc2 = acc1 + LENGTH (REJ_NIBBLES_ETA2 (SUB_LIST (16*i+4,4) inlist):int16 list)` THEN
  REABBREV_TAC `mask8c = read R8 s41` THEN
  ACC2_IDENT_TAC THEN
  SUBGOAL_THEN `acc2 <= 248` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) = acc2` then SUBST1_TAC(SYM th) else NO_TAC) THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `acc2:num`;;

let ETA2_SI3_BODY3_TAC : tactic =
  ETA2_SI3_PRE3_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) = acc2`]) THEN
  (* s42 vextracti128 $1 -> XMM8 (HIGH-128 of EXPANDED f0sub); re-fold f0sub. *)
  X86_VSTEPS_TAC EXEC (42--42) THEN
  W(fun (asl,w) ->
     let f0d = find (fun th -> is_eq(concl th) &&
        (lhand(concl th) = `f0sub:int256` || rand(concl th) = `f0sub:int256`) &&
        can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
     let f0fold = if rand(concl f0d) = `f0sub:int256` then f0d else SYM f0d in
     RULE_ASSUM_TAC(fun th -> if concl th = concl f0d then th else REWRITE_RULE[f0fold] th)) THEN
  X86_VERBOSE_STEP_TAC EXEC "s43" THEN MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s42 = mask8c:int64`]) THEN
  (SUBGOAL_THEN maskbit_tgt_3 ASSUME_TAC THENL [MASKBIT_TGT_3_TAC; ALL_TAC]) THEN
  X86_VSTEPS_TAC EXEC (44--44) THEN ETA2_TAB3_TEQ_TAC THEN
  REABBREV_TAC `tab3 = read YMM9 s44` THEN
  X86_VSTEPS_TAC EXEC (45--45) THEN REABBREV_TAC `pshuf3 = read YMM9 s45` THEN
  PURGE_STALE_STATES_TAC ["s44"] THEN
  X86_VSTEPS_TAC EXEC (46--46) THEN REABBREV_TAC `sx3 = read YMM1 s46` THEN
  PURGE_STALE_STATES_TAC ["s45"] THEN
  X86_VSTEPS_TAC EXEC (47--47) THEN X86_VSTEPS_TAC EXEC (48--48) THEN
  X86_VSTEPS_TAC EXEC (49--49) THEN
  PURGE_STALE_STATES_TAC ["s46";"s47";"s48"] THEN
  VAL_INT64_TAC `acc2:num` THEN
  X86_STEPS_TAC EXEC (50--50) THEN
  ETA2_STORE_REFOLD_3_TAC THEN
  ETA2_SX3_CLEAN_TAC THEN
  ETA2_ESTABLISH_PF_TARGET_3_TAC THEN
  ACC2_IDENT_TAC THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
    let storerf = find (fun th -> is_eq(concl th) &&
         can(find_term(fun u->match u with Const("bytes256",_)->true|_->false)) (lhand(concl th)) &&
         can(find_term(fun u->match u with Const("red_lane",_)->true|_->false)) (rand(concl th)) &&
         not(can(find_term(fun u->match u with Const("word_mul",_)->true|_->false)) (rand(concl th)))) asms in
    let sx3clean = find (fun th -> is_eq(concl th) && lhand(concl th)=`sx3:int256` &&
         can(find_term(fun u->match u with Const("usimd8",_)->true|_->false)) (rand(concl th))) asms in
    let pfth = find (fun th -> concl th = pf_target_3) asms in
    let bg = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f0sub:int256`))c &&
        not(can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))c) &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (64,8):byte`))c &&
        can(find_term(fun u->u=`word_subword (f0sub:int256) (128,128):int128`))c) asms in
    let mthm = find (fun th -> concl th = maskbit_tgt_3) asms in
    let store_full = REWRITE_RULE[pfth] (REWRITE_RULE[sx3clean] storerf) in
    let g3 = `word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128` in
    let m = `word (val (mask8c:int64) MOD 256):byte` in
    let pc = ISPECL [`word_add res (word (4 * acc2)):int64`; `s50:x86state`; g3; m;
                     `LENGTH(ACC_IDX (word (val (mask8c:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND_RL in
    let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
    let spec = ISPECL [g3; m; `word_subword (chunk0:int128) (64,8):byte`;
        `word_subword (chunk0:int128) (72,8):byte`; `word_subword (chunk0:int128) (80,8):byte`;
        `word_subword (chunk0:int128) (88,8):byte`] SUBITER_STORE_SPEC in
    let specres = MP spec (CONJ mthm bg) in
    let rej_store = REWRITE_RULE[specres] res_th0 in
    let leninl = find (fun th -> match concl th with
         Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Var("inlist",_))),_) -> true | _ -> false) asms in
    let i116 = find (fun th -> match concl th with
         Comb(Comb(Const("<=",_),Comb(Comb(Const("*",_),_),Comb(Comb(Const("+",_),Var("i",_)),_))),_) -> true | _ -> false) asms in
    let blk16 = find (fun th -> is_eq(concl th) && hasC "SUB_LIST" th &&
         (try length(dest_list(rand(concl th))) = 16 with _ -> false)) asms in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*(i+1)<=136 ==> 16*i+16<=136`) i116)) blk16) in
    let blk2_eq = el 2 (CONJUNCTS bb) in
    let lr0 = MP (ISPECL [m;`word_subword (chunk0:int128) (64,8):byte`;`word_subword (chunk0:int128) (72,8):byte`;
        `word_subword (chunk0:int128) (80,8):byte`;`word_subword (chunk0:int128) (88,8):byte`] LEN_RECONCILE_GEN) mthm in
    let lr = REWRITE_RULE[GSYM blk2_eq] lr0 in
    let rej_store1 = REWRITE_RULE[GSYM blk2_eq] rej_store in
    let acc2_ident = find (fun th -> match concl th with
         Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA2_BYTES",_),_))),Var("acc2",_)) -> true | _ -> false) asms in
    let prefix_store0 = find (fun th -> (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s50",_))),_) -> true | _ -> false) &&
         hasC "num_of_wordlist" th && hasC "SUB_LIST" th && can(find_term(fun u->u=`acc2:num`))(lhand(concl th)) &&
         not(hasC "ACC_IDX" th) && not(hasC "bytes256" th)) asms in
    let prefix_store = REWRITE_RULE[GSYM acc2_ident] prefix_store0 in
    let rej_store2 = REWRITE_RULE[GSYM acc2_ident] rej_store1 in
    let fold = MP (ISPECL [`res:int64`;`s50:x86state`;m;`SUB_LIST(16*i+8,4) (inlist:byte list)`;`SUB_LIST(0,16*i+8) (inlist:byte list)`] SUBITER_FOLD_STEP)
                  (CONJ lr (CONJ prefix_store rej_store2)) in
    let split = REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i+8`;`4`;`0`] SUB_LIST_SPLIT) in
    let clean = REWRITE_RULE[GSYM split; ARITH_RULE `(16*i+8)+4 = 16*i+12`] fold in
    ASSUME_TAC clean);;

(* ------------------------------------------------------------------------- *)
(* ETA2_MG2_NT_TAC: SI2 counter s36-41, mid-guard-2 NOT taken -> pc+273.     *)
(* bound acc1+block1len<=248 from DIRECT niblen(16i+8)<=248 (FIRST[ACCEPT;MONO]) *)
(* Ends with an RAX-fold for the SI3 store.                                  *)
let mk_eta2_mg2_nt (memsafe:bool) : tactic =
  X86_STEPS_TAC EXEC (36--39) THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
    let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
    let popcnt2 = REWRITE_RULE[m8b_def]
       (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE1)) in
    let lanesum8 = rand(concl popcnt2) in
    let mb2 = find_a (fun th -> let c=concl th in is_forall c &&
       can(find_term(fun u->u=`f1bnd:int256`))c &&
       can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),n) -> n=`8` | _ -> false))c) in
    let mb2_tm = concl mb2 in
    let i_le = find_a (fun th -> concl th = `16 * i <= 120`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
    let blk16 = find_a (fun th -> is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" &&
            length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=120 ==> 16*i+16<=136`) i_le)) blk16) in
    let blk1_eq = el 1 (CONJUNCTS bb) in
    let block1 = `[word_subword (chunk0:int128) (32,8); word_subword chunk0 (40,8);
                   word_subword chunk0 (48,8); word_subword chunk0 (56,8)]:byte list` in
    let block1len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA2`, block1)) in
    let bsum2_raw = prove(mk_imp(mb2_tm, mk_eq(lanesum8, block1len_x)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV)
            (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER_ETA2] THEN
      SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let pop_len2 = REWRITE_RULE[GSYM blk1_eq] (TRANS popcnt2 (MP bsum2_raw mb2)) in
    ASSUME_TAC pop_len2) THEN
  SUBGOAL_THEN `acc1 + LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i+4,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+4`] SUBITER_BRIDGE_ETA2) THEN
    ANTS_TAC THENL [UNDISCH_TAC `16 * (i+1) <= 136` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=136` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES; ARITH_RULE `(16*i+4)+4 = 16*i+8`] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) = acc1` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `acc1 + LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i+4,4) inlist):int16 list) <= 248` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),_)->true|_->false) then SUBST1_TAC th else NO_TAC) THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           (FIRST_X_ASSUM(fun th -> match concl th with
              Comb(Comb(Const("<=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA2_BYTES",_),_))),k) when k=`248`
                -> MP_TAC th | _ -> NO_TAC) THEN
            MATCH_MP_TAC(ARITH_RULE `a <= b ==> b <= 248 ==> a <= 248`) THEN
            MATCH_MP_TAC REJ_SAMPLE_ETA2_PREFIX_MONO THEN ARITH_TAC)]; ALL_TAC] THEN
  W(fun (asl,w) ->
    let block1len = `LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i+4,4) inlist):int16 list)` in
    let sum = mk_binop `(+):num->num->num` `acc1:num` block1len in
    let bnd = snd(find (fun (_,th) -> concl th = mk_binop `(<=):num->num->bool` sum `248`) asl) in
    let pop_len2 = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl) in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let ja = MP (ISPECL [sum; `248`] JA_NOT_TAKEN_LE) (CONJ bnd (ARITH_RULE `248 < 2 EXP 32`)) in
    ASSUME_TAC pop_len2 THEN ASSUME_TAC bnd THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja) THEN
  X86_STEPS_TAC EXEC (40--41) THEN
  SUBGOAL_THEN `read RIP s41 = word (pc + 273):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      (* disambiguate the block1 pop_len (SUB_LIST(16i+4,4)) from the stale MG1
         pop_len (SUB_LIST(16i,4)) — both are word_popcount facts now. *)
      let pop_len2_old = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) ->
            can(find_term(fun u->u=`SUB_LIST(16*i+4,4) (inlist:byte list)`))(concl th) | _ -> false) asl in
      let zbe = MP (SPEC `val (mask8b:int64) MOD 256` zxbyte_eq) (ARITH_RULE `val (mask8b:int64) MOD 256 < 256`) in
      let pop_len2_typed = TRANS (AP_TERM `word_popcount:int32->num` zbe) (snd pop_len2_old) in
      let rax_red0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) ->
            can(find_term(fun u->u=`acc1:num`))(concl th) | _ -> false) asl in
      let ja = find (fun (_,th) -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`acc1:num`))(concl th)) asl in
      eta2_rip_mp memsafe 273 41 THEN
      REWRITE_TAC[pop_len2_typed] THEN REWRITE_TAC[snd rax_red0] THEN
      REWRITE_TAC[snd ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  (* RAX-fold so SI3 store discharges                                        *)
  W(fun (asl,w) ->
    let pl = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) ->
          can(find_term(fun u->u=`SUB_LIST(16*i+4,4) (inlist:byte list)`))(concl th) | _ -> false) asl in
    let zbe = MP (SPEC `val (mask8b:int64) MOD 256` zxbyte_eq) (ARITH_RULE `val (mask8b:int64) MOD 256 < 256`) in
    let pl_typed = TRANS (AP_TERM `word_popcount:int32->num` zbe) (snd pl) in
    let rr = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) ->
          can(find_term(fun u->u=`acc1:num`))(concl th) | _ -> false) asl in
    RULE_ASSUM_TAC(REWRITE_RULE[pl_typed]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd rr]));;

let ETA2_MG2_NT_TAC : tactic = mk_eta2_mg2_nt false;;

(* ------------------------------------------------------------------------- *)
(* ETA2_SI3_MG3_TAKEN_TAC: SI3 counter s51-56, mid-guard-3 fires TAKEN (pc+399). *)
(* = ETA2_SI3_MG's pop_len3/bridge3 build but JA_TAKEN_GT + RIP pc+399.      *)
let ETA2_SI3_MG3_TAKEN_TAC : tactic =
  X86_STEPS_TAC EXEC (51--54) THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let m8c_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8c:int64` | _ -> false) in
    let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
    let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
    let popcnt3 = REWRITE_RULE[m8b_def; m8c_def]
       (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE2)) in
    let lanesum = rand(concl popcnt3) in
    let mb3 = find_a (fun th -> let c=concl th in is_forall c &&
       can(find_term(fun u->u=`f1bnd:int256`))c &&
       can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),n) -> n=`16` | _ -> false))c) in
    let mb3_tm = concl mb3 in
    let i_le = find_a (fun th -> concl th = `16 * i <= 120`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
    let blk16 = find_a (fun th -> is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" &&
            length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=120 ==> 16*i+16<=136`) i_le)) blk16) in
    let blk2_eq = el 2 (CONJUNCTS bb) in
    let block2 = `[word_subword (chunk0:int128) (64,8); word_subword chunk0 (72,8);
                   word_subword chunk0 (80,8); word_subword chunk0 (88,8)]:byte list` in
    let block2len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA2`, block2)) in
    let bsum3_raw = prove(mk_imp(mb3_tm, mk_eq(lanesum, block2len_x)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV)
            (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER_ETA2] THEN
      SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let pop_len3 = REWRITE_RULE[GSYM blk2_eq] (TRANS popcnt3 (MP bsum3_raw mb3)) in
    ASSUME_TAC pop_len3) THEN
  (* bridge3: acc2 + block2len = niblen_sample(16i+12)                       *)
  SUBGOAL_THEN `acc2 + LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i+8,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+8`] SUBITER_BRIDGE_ETA2) THEN
    ANTS_TAC THENL [UNDISCH_TAC `16 * (i+1) <= 136` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=136` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES; ARITH_RULE `(16*i+8)+4 = 16*i+12`] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) = acc2` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) < 2 EXP 32` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+8`] OUTLEN0_LE_256_FROM_SUBITER_ETA2) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `16 * (i+1) <= 136` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=136` THEN ARITH_TAC;
        FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) = acc2` then SUBST1_TAC th else NO_TAC) THEN FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(16*i+8)+4 = 16*i+12`] THEN ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let block2len = `LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i+8,4) inlist):int16 list)` in
    let sum = mk_binop `(+):num->num->num` `acc2:num` block2len in
    let bridge3 = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),_) -> true | _ -> false) asl) in
    let lt32 = REWRITE_RULE[SYM bridge3] (snd(find (fun (_,th) -> concl th = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) < 2 EXP 32`) asl)) in
    let pop_len3 = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl) in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let gt248 = REWRITE_RULE[SYM bridge3] (snd(find (fun (_,th) -> concl th = `248 < LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)`) asl)) in
    let ja_taken = MP (ISPECL [sum; `248`] JA_TAKEN_GT) (CONJ gt248 lt32) in
    ASSUME_TAC pop_len3 THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja_taken) THEN
  X86_STEPS_TAC EXEC (55--56) THEN
  SUBGOAL_THEN `read RIP s56 = word (pc + 399):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let asms = map snd asl in
      let find_a p = find p asms in
      let i_le = find_a (fun th -> concl th = `16 * i <= 120`) in
      let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
      let blk16 = find_a (fun th -> is_eq(concl th) &&
         (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
      let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                  (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=120 ==> 16*i+16<=136`) i_le)) blk16) in
      let blk2_eq = el 2 (CONJUNCTS bb) in
      let rax_red0 = find_a (fun th -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) ->
            can(find_term(fun u->u=`acc2:num`))(concl th) | _ -> false) in
      let ja = find_a (fun th -> is_neg(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`acc2:num`))(concl th)) in
      let ifrip = find_a (fun th -> match concl th with
         Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s56",_))),r) ->
           (match r with Comb(Comb(Comb(Const("COND",_),_),_),_) -> true | _ -> false) | _ -> false) in
      MP_TAC ifrip THEN REWRITE_TAC[GSYM blk2_eq] THEN REWRITE_TAC[rax_red0] THEN
      REWRITE_TAC[ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC];;

(* MID_EXIT_SUBITER3_ETA2: sub-iter-3 mid-guard fires TAKEN at pos 16i+12.   *)
let mk_midexit3_eta2 (memsafe:bool) (prefix:tactic) (disch:tactic) : tactic =
prefix THEN
  SUBGOAL_THEN `16 * i + 4 <= LENGTH(inlist:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i+1) <= 136` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=136` THEN ARITH_TAC; ALL_TAC] THEN
  (mk_eta2_mg1_nt memsafe) THEN
  ETA2_SI2_FOLD THEN
  (mk_eta2_mg2_nt memsafe) THEN
  ETA2_SI3_BODY3_TAC THEN
  ETA2_SI3_MG3_TAKEN_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* RAX collapse (pop_len3 -> bridge3 -> niblen(16i+12)); ja_taken guard; RCX. *)
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let i_le = find_a (fun th -> concl th = `16 * i <= 120`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
    let blk16 = find_a (fun th -> is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=120 ==> 16*i+16<=136`) i_le)) blk16) in
    let blk2_eq = el 2 (CONJUNCTS bb) in
    let pop_len3 = find_a (fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) in
    let rax_red0 = find_a (fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) ->
          can(find_term(fun u->u=`acc2:num`))(concl th) | _ -> false) in
    let bridge3 = find_a (fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),_) -> true | _ -> false) in
    REWRITE_TAC[GSYM blk2_eq] THEN REWRITE_TAC[rax_red0] THEN REWRITE_TAC[bridge3]) THEN
  W(fun (asl,w) ->
    let ntake = MP (ISPECL [`LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)`;`248`] JA_TAKEN_GT)
                   (CONJ (ASSUME `248 < LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)`)
                         (ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) < 2 EXP 32`)) in
    REWRITE_TAC[ntake]) THEN
  (* RCX collapse: triple +4 nest (16i -> +4 -> +8 -> +12).  After each
     RCX4_COLLAPSE rewrite the goal carries `word((..)+4)`; NORMALISE that
     bracketed sum to the flat `16*i+k` form *after* the DISCH (not before, or
     the SPEC of the next level's collapse can't match).  Then AP_TERM+ARITH
     closes the final `word((16*i+8)+4) = word(16*i+12)`. *)
  MP_TAC(SPEC `16*i` RCX4_COLLAPSE) THEN ANTS_TAC THENL [UNDISCH_TAC `16*i<=120` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(SPEC `16*i+4` RCX4_COLLAPSE) THEN ANTS_TAC THENL [UNDISCH_TAC `16*i<=120` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[ARITH_RULE `(16*i+4)+4 = 16*i+8`] THEN
  MP_TAC(SPEC `16*i+8` RCX4_COLLAPSE) THEN ANTS_TAC THENL [UNDISCH_TAC `16*i<=120` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  TRY(AP_TERM_TAC THEN ARITH_TAC) THEN REWRITE_TAC[ARITH_RULE `(16*i+8)+4 = 16*i+12`] THEN (if memsafe then disch else ALL_TAC);;
let MID_EXIT_SUBITER3_ETA2 = prove(midexit3_eta2_tm, mk_midexit3_eta2 false ETA2_MIDEXIT_PREFIX_TAC ALL_TAC);;

(* ========================================================================= *)
(* eta2 CORRECT: MID_EXIT_CASE4 (all 3 internal guards clean, head-guard-1   *)
(* fires TAKEN at the back-edge).                                            *)
(*                                                                           *)
(* Sub-iters 1/2/3 mid-guards all NOT taken; sub-iter-4 processes, then      *)
(* niblen(16(i+1))>248 so the head-guard fires at the next loop-top pc+86.   *)
(*                                                                           *)
(* Structure:                                                                *)
(*   ETA2_MIDEXIT_PREFIX_TAC  -> s20  SI1 store folded                       *)
(*   ETA2_MG1_NT_TAC          -> s26  mg1 not taken (pc+207)                 *)
(*   ETA2_SI2_FOLD            -> s35  SI2 store folded                       *)
(*   ETA2_MG2_NT_TAC          -> s41  mg2 not taken (pc+273)                 *)
(*   ETA2_SI3_BODY3_TAC       -> s50  SI3 store folded                       *)
(*   ETA2_MG3_NT_TAC          -> s56  mg3 not taken (pc+339)                 *)
(*   ETA2_SI4_BODY4_TAC       -> s65  SI4 store folded                       *)
(*   ETA2_SI4_COUNTER_TAC     -> s69  popcnt/add/add/JMP -> pc+86            *)
(*   [head-guard-1 cmp eax,248 TAKEN] s70-71 -> pc+399, then ENSURES_FINAL.  *)
(*                                                                           *)
(* eta2-vs-eta4 divergence: eta4's SI4 sub-iter ends with the head-guard-1   *)
(* eax cmp inline.  In eta2 the SI4 counter is popcnt/add/add/JMP (s66-69,   *)
(* unconditional jmp to pc+86, no inline cmp/ja), so head-guard-1 (cmp       *)
(* eax,248; ja) is re-executed at the loop top after the jmp.  For CASE4     *)
(* that head-guard fires TAKEN (niblen(16(i+1))>248) -> pc+399.              *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* ETA2_MG3_NT_TAC: SI3 counter s51-56, mid-guard-3 NOT taken -> pc+339.     *)
(* bound acc2+block2len<=248 from DIRECT niblen(16i+12)<=248 (FIRST[ACCEPT;MONO]) *)
(* Ends with an RAX-fold for the SI4 store.                                  *)
let mk_eta2_mg3_nt (memsafe:bool) : tactic =
  X86_STEPS_TAC EXEC (51--54) THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let m8c_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8c:int64` | _ -> false) in
    let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
    let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
    let popcnt3 = REWRITE_RULE[m8b_def; m8c_def]
       (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE2)) in
    let lanesum = rand(concl popcnt3) in
    let mb3 = find_a (fun th -> let c=concl th in is_forall c &&
       can(find_term(fun u->u=`f1bnd:int256`))c &&
       can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),n) -> n=`16` | _ -> false))c) in
    let mb3_tm = concl mb3 in
    let i_le = find_a (fun th -> concl th = `16 * i <= 120`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
    let blk16 = find_a (fun th -> is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" &&
            length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=120 ==> 16*i+16<=136`) i_le)) blk16) in
    let blk2_eq = el 2 (CONJUNCTS bb) in
    let block2 = `[word_subword (chunk0:int128) (64,8); word_subword chunk0 (72,8);
                   word_subword chunk0 (80,8); word_subword chunk0 (88,8)]:byte list` in
    let block2len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA2`, block2)) in
    let bsum3_raw = prove(mk_imp(mb3_tm, mk_eq(lanesum, block2len_x)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV)
            (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER_ETA2] THEN
      SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let pop_len3 = REWRITE_RULE[GSYM blk2_eq] (TRANS popcnt3 (MP bsum3_raw mb3)) in
    ASSUME_TAC pop_len3) THEN
  (* bridge3: acc2 + block2len = niblen_sample(16i+12)                       *)
  SUBGOAL_THEN `acc2 + LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i+8,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+8`] SUBITER_BRIDGE_ETA2) THEN
    ANTS_TAC THENL [UNDISCH_TAC `16 * (i+1) <= 136` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=136` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES; ARITH_RULE `(16*i+8)+4 = 16*i+12`] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) = acc2` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  (* bound acc2 + block2len <= 248 from the DIRECT niblen(16i+12)<=248 hyp   *)
  SUBGOAL_THEN `acc2 + LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i+8,4) inlist):int16 list) <= 248` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),_)->true|_->false) then SUBST1_TAC th else NO_TAC) THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           (FIRST_X_ASSUM(fun th -> match concl th with
              Comb(Comb(Const("<=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA2_BYTES",_),_))),k) when k=`248`
                -> MP_TAC th | _ -> NO_TAC) THEN
            MATCH_MP_TAC(ARITH_RULE `a <= b ==> b <= 248 ==> a <= 248`) THEN
            MATCH_MP_TAC REJ_SAMPLE_ETA2_PREFIX_MONO THEN ARITH_TAC)]; ALL_TAC] THEN
  W(fun (asl,w) ->
    let block2len = `LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i+8,4) inlist):int16 list)` in
    let sum = mk_binop `(+):num->num->num` `acc2:num` block2len in
    let bnd = snd(find (fun (_,th) -> concl th = mk_binop `(<=):num->num->bool` sum `248`) asl) in
    let pop_len3 = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) ->
          can(find_term(fun u->u=`SUB_LIST(16*i+8,4) (inlist:byte list)`))(concl th) | _ -> false) asl) in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let ja = MP (ISPECL [sum; `248`] JA_NOT_TAKEN_LE) (CONJ bnd (ARITH_RULE `248 < 2 EXP 32`)) in
    ASSUME_TAC pop_len3 THEN ASSUME_TAC bnd THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja) THEN
  X86_STEPS_TAC EXEC (55--56) THEN
  SUBGOAL_THEN `read RIP s56 = word (pc + 339):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let asms = map snd asl in
      let find_a p = find p asms in
      let i_le = find_a (fun th -> concl th = `16 * i <= 120`) in
      let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
      let blk16 = find_a (fun th -> is_eq(concl th) &&
         (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
      let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                  (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=120 ==> 16*i+16<=136`) i_le)) blk16) in
      let blk2_eq = el 2 (CONJUNCTS bb) in
      let rax_red0 = find_a (fun th -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) ->
            can(find_term(fun u->u=`acc2:num`))(concl th) | _ -> false) in
      let ja = find_a (fun th -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`acc2:num`))(concl th)) in
      eta2_rip_mp memsafe 339 56 THEN
      REWRITE_TAC[GSYM blk2_eq] THEN REWRITE_TAC[rax_red0] THEN
      REWRITE_TAC[ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  (* RAX-fold so SI4 store discharges                                        *)
  W(fun (asl,w) ->
    let pl = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) ->
          can(find_term(fun u->u=`SUB_LIST(16*i+8,4) (inlist:byte list)`))(concl th) | _ -> false) asl in
    let rr = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) ->
          can(find_term(fun u->u=`acc2:num`))(concl th) | _ -> false) asl in
    RULE_ASSUM_TAC(REWRITE_RULE[snd pl]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd rr]));;

let ETA2_MG3_NT_TAC : tactic = mk_eta2_mg3_nt false;;

(* ------------------------------------------------------------------------- *)
(* ETA2_SI4_BODY4_TAC: SI4 store fold for MID-EXIT.                          *)
(* Forked SI4_PRE: acc3<=248 from DIRECT niblen(16i+12)<=248 (ACC3_IDENT +   *)
(* FIRST[ACCEPT;PREFIX_MONO]) instead of SUBITER_OUTLEN_BOUND_4.  RAX already *)
(* folded by MG3_NT, so PRE4 only abbrevs acc3, reabbrevs mask8d, bounds.    *)
(* The step/refold/fold body is identical to ETA2_SI4_FOLD's post-PRE portion. *)
let ETA2_SI4_PRE4_TAC : tactic =
  ABBREV_TAC `acc3 = acc2 + LENGTH (REJ_NIBBLES_ETA2 (SUB_LIST (16*i+8,4) inlist):int16 list)` THEN
  REABBREV_TAC `mask8d = read R8 s56` THEN
  ACC3_IDENT_TAC THEN
  SUBGOAL_THEN `acc3 <= 248` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) = acc3` then SUBST1_TAC(SYM th) else NO_TAC) THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `acc3:num`;;

let ETA2_SI4_BODY4_TAC : tactic =
  ETA2_SI4_PRE4_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) = acc3`]) THEN
  (* s57 vpsrldq $8 -> XMM8 (>>64 of the HIGH-128 of EXPANDED f0sub); re-fold f0sub. *)
  X86_VSTEPS_TAC EXEC (57--57) THEN
  W(fun (asl,w) ->
     let f0d = find (fun th -> is_eq(concl th) &&
        (lhand(concl th) = `f0sub:int256` || rand(concl th) = `f0sub:int256`) &&
        can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
     let f0fold = if rand(concl f0d) = `f0sub:int256` then f0d else SYM f0d in
     RULE_ASSUM_TAC(fun th -> if concl th = concl f0d then th else REWRITE_RULE[f0fold] th)) THEN
  X86_VERBOSE_STEP_TAC EXEC "s58" THEN MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s57 = mask8d:int64`]) THEN
  (SUBGOAL_THEN maskbit_tgt_4 ASSUME_TAC THENL [MASKBIT_TGT_4_TAC; ALL_TAC]) THEN
  X86_VSTEPS_TAC EXEC (59--59) THEN ETA2_TAB4_TEQ_TAC THEN
  REABBREV_TAC `tab4 = read YMM9 s59` THEN
  X86_VSTEPS_TAC EXEC (60--60) THEN REABBREV_TAC `pshuf4 = read YMM9 s60` THEN
  PURGE_STALE_STATES_TAC ["s59"] THEN
  X86_VSTEPS_TAC EXEC (61--61) THEN REABBREV_TAC `sx4 = read YMM1 s61` THEN
  PURGE_STALE_STATES_TAC ["s60"] THEN
  X86_VSTEPS_TAC EXEC (62--62) THEN X86_VSTEPS_TAC EXEC (63--63) THEN
  X86_VSTEPS_TAC EXEC (64--64) THEN
  PURGE_STALE_STATES_TAC ["s61";"s62";"s63"] THEN
  VAL_INT64_TAC `acc3:num` THEN
  X86_STEPS_TAC EXEC (65--65) THEN
  ETA2_STORE_REFOLD_4_TAC THEN
  ETA2_SX4_CLEAN_TAC THEN
  ETA2_ESTABLISH_PF_TARGET_4_TAC THEN
  ACC3_IDENT_TAC THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
    let storerf = find (fun th -> is_eq(concl th) &&
         can(find_term(fun u->match u with Const("bytes256",_)->true|_->false)) (lhand(concl th)) &&
         can(find_term(fun u->match u with Const("red_lane",_)->true|_->false)) (rand(concl th)) &&
         not(can(find_term(fun u->match u with Const("word_mul",_)->true|_->false)) (rand(concl th)))) asms in
    let sx4clean = find (fun th -> is_eq(concl th) && lhand(concl th)=`sx4:int256` &&
         can(find_term(fun u->match u with Const("usimd8",_)->true|_->false)) (rand(concl th))) asms in
    let pfth = find (fun th -> concl th = pf_target_4) asms in
    let bg = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f0sub:int256`))c &&
        can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (96,8):byte`))c &&
        can(find_term(fun u->u=`word_subword (f0sub:int256) (128,128):int128`))c) asms in
    let mthm = find (fun th -> concl th = maskbit_tgt_4) asms in
    let store_full = REWRITE_RULE[pfth] (REWRITE_RULE[sx4clean] storerf) in
    let g4 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128) 64):int128):int128` in
    let m = `word (val (mask8d:int64) MOD 256):byte` in
    let pc = ISPECL [`word_add res (word (4 * acc3)):int64`; `s65:x86state`; g4; m;
                     `LENGTH(ACC_IDX (word (val (mask8d:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND_RL in
    let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
    let spec = ISPECL [g4; m; `word_subword (chunk0:int128) (96,8):byte`;
        `word_subword (chunk0:int128) (104,8):byte`; `word_subword (chunk0:int128) (112,8):byte`;
        `word_subword (chunk0:int128) (120,8):byte`] SUBITER_STORE_SPEC in
    let specres = MP spec (CONJ mthm bg) in
    let rej_store = REWRITE_RULE[specres] res_th0 in
    let leninl = find (fun th -> match concl th with
         Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Var("inlist",_))),_) -> true | _ -> false) asms in
    let i116 = find (fun th -> match concl th with
         Comb(Comb(Const("<=",_),Comb(Comb(Const("*",_),_),Comb(Comb(Const("+",_),Var("i",_)),_))),_) -> true | _ -> false) asms in
    let blk16 = find (fun th -> is_eq(concl th) && hasC "SUB_LIST" th &&
         (try length(dest_list(rand(concl th))) = 16 with _ -> false)) asms in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*(i+1)<=136 ==> 16*i+16<=136`) i116)) blk16) in
    let blk3_eq = el 3 (CONJUNCTS bb) in
    let lr0 = MP (ISPECL [m;`word_subword (chunk0:int128) (96,8):byte`;`word_subword (chunk0:int128) (104,8):byte`;
        `word_subword (chunk0:int128) (112,8):byte`;`word_subword (chunk0:int128) (120,8):byte`] LEN_RECONCILE_GEN) mthm in
    let lr = REWRITE_RULE[GSYM blk3_eq] lr0 in
    let rej_store1 = REWRITE_RULE[GSYM blk3_eq] rej_store in
    let acc3_ident = find (fun th -> match concl th with
         Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA2_BYTES",_),_))),Var("acc3",_)) -> true | _ -> false) asms in
    let prefix_store0 = find (fun th -> (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s65",_))),_) -> true | _ -> false) &&
         hasC "num_of_wordlist" th && hasC "SUB_LIST" th && can(find_term(fun u->u=`acc3:num`))(lhand(concl th)) &&
         not(hasC "ACC_IDX" th) && not(hasC "bytes256" th)) asms in
    let prefix_store = REWRITE_RULE[GSYM acc3_ident] prefix_store0 in
    let rej_store2 = REWRITE_RULE[GSYM acc3_ident] rej_store1 in
    let fold = MP (ISPECL [`res:int64`;`s65:x86state`;m;`SUB_LIST(16*i+12,4) (inlist:byte list)`;`SUB_LIST(0,16*i+12) (inlist:byte list)`] SUBITER_FOLD_STEP)
                  (CONJ lr (CONJ prefix_store rej_store2)) in
    let split = REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i+12`;`4`;`0`] SUB_LIST_SPLIT) in
    let clean = REWRITE_RULE[GSYM split; ARITH_RULE `(16*i+12)+4 = 16*i+16`] fold in
    ASSUME_TAC clean);;

(* MID_EXIT_CASE4_ETA2: all 4 sub-iters clean, head-guard-1 fires at 16(i+1).*)
let mk_midexit4_eta2 (memsafe:bool) (prefix:tactic) (disch:tactic) : tactic =
prefix THEN
  SUBGOAL_THEN `16 * i + 4 <= LENGTH(inlist:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i+1) <= 136` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=136` THEN ARITH_TAC; ALL_TAC] THEN
  (* CASE4 hyp is niblen(16i+12)<=248; derive niblen(16i+4),niblen(16i+8)<=248 by mono. *)
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) <= 248` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) <= 248` then MP_TAC th else NO_TAC) THEN
    MATCH_MP_TAC(ARITH_RULE `a <= b ==> b <= 248 ==> a <= 248`) THEN
    MATCH_MP_TAC REJ_SAMPLE_ETA2_PREFIX_MONO THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) <= 248` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) <= 248` then MP_TAC th else NO_TAC) THEN
    MATCH_MP_TAC(ARITH_RULE `a <= b ==> b <= 248 ==> a <= 248`) THEN
    MATCH_MP_TAC REJ_SAMPLE_ETA2_PREFIX_MONO THEN ARITH_TAC; ALL_TAC] THEN
  (mk_eta2_mg1_nt memsafe) THEN
  ETA2_SI2_FOLD THEN
  (mk_eta2_mg2_nt memsafe) THEN
  ETA2_SI3_BODY3_TAC THEN
  (mk_eta2_mg3_nt memsafe) THEN
  ETA2_SI4_BODY4_TAC THEN
  ETA2_SI4_COUNTER_TAC THEN
  (* Step the head-guard 70-71 immediately after the counter, with the state clean
     (no le256/bridge4/<2^32 asserts yet — asserting them first puts `acc3+...`
     equations in scope that the stepper mis-applies to `read RAX s69`; the isolated
     step from a bare s69 succeeds).  RIP s69 = pc+86; s70 = cmp eax,0xf8; s71 = ja ->
     COND(pc+399,pc+97).  Then build the bounds + resolve. *)
  X86_STEPS_TAC EXEC (70--71) THEN
  (* SI4 counter jmp lands at pc+86; RAX/RCX raw nests.  Build the niblen(16(i+1))
     bound + pop_len4 + rax_red0 + head-guard1 ja TAKEN, then resolve RIP s71 -> pc+399. *)
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list) <= 256` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+12`] OUTLEN0_LE_256_FROM_SUBITER_ETA2) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `16 * (i+1) <= 136` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=136` THEN ARITH_TAC;
 (* ETA2_SI4_BODY4_TAC's RULE_ASSUM rewrote the mid-exit hyp
           `niblen(16i+12)<=248` into `acc3<=248` via the ACC3_IDENT fact
           `niblen(16i+12)=acc3`, so the antecedent is no longer present in the
           original form.  Accept it whether it survives as `niblen(16i+12)<=248`
           OR as `acc3<=248`: rewrite the goal via the ident fact (if present)
           then accept acc3<=248. *)
        FIRST[FIRST_ASSUM ACCEPT_TAC;
              (FIRST_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) = acc3` then SUBST1_TAC th else NO_TAC) THEN
               FIRST_ASSUM ACCEPT_TAC)]]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(16*i+12)+4 = 16*(i+1)`; ARITH_RULE `16*i+16=16*(i+1)`]; ALL_TAC] THEN
  (* bridge4: acc3 + block3len = niblen_sample(16(i+1))                      *)
  SUBGOAL_THEN `acc3 + LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i+12,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+12`] SUBITER_BRIDGE_ETA2) THEN
    ANTS_TAC THENL [UNDISCH_TAC `16 * (i+1) <= 136` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=136` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES; ARITH_RULE `(16*i+12)+4 = 16*(i+1)`; ARITH_RULE `16*i+16 = 16*(i+1)`] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) = acc3` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  (* niblen(16(i+1)) < 2^32 (for JA_TAKEN_GT / RAX_NEST_REDUCE).             *)
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list) < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list) <= 256` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `read RIP s71 = word (pc + 399):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let asms = map snd asl in
      let find_a p = find p asms in
      let m8c_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8c:int64` | _ -> false) in
      let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
      let m8d_val = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8d:int64` && can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))(concl th) | _ -> false) in
      let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
      let popcnt4 = REWRITE_RULE[m8d_val] (REWRITE_RULE[m8b_def; m8c_def]
         (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE3))) in
      let lanesum = rand(concl popcnt4) in
      let mb4 = find_a (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f1bnd:int256`))c &&
         can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),n) -> n=`24` | _ -> false))c) in
      let mb4_tm = concl mb4 in
      let i_le = find_a (fun th -> concl th = `16 * i <= 120`) in
      let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
      let blk16 = find_a (fun th -> is_eq(concl th) && (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
      let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                  (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=120 ==> 16*i+16<=136`) i_le)) blk16) in
      let blk3_eq = el 3 (CONJUNCTS bb) in
      let block3 = `[word_subword (chunk0:int128) (96,8); word_subword chunk0 (104,8); word_subword chunk0 (112,8); word_subword chunk0 (120,8)]:byte list` in
      let block3len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA2`, block3)) in
      let bsum4_raw = prove(mk_imp(mb4_tm, mk_eq(lanesum, block3len_x)),
        DISCH_THEN(fun mbthm ->
          let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
            CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
          REWRITE_TAC mbs) THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
        REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER_ETA2] THEN
        SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
      let pop_len4 = REWRITE_RULE[GSYM blk3_eq] (TRANS popcnt4 (MP bsum4_raw mb4)) in
      let bridge4 = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc3",_)),_)),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA2_BYTES",_),_)))->true|_->false) in
      let lt32 = REWRITE_RULE[SYM bridge4] (find_a (fun th -> concl th = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list) < 2 EXP 32`)) in
      let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
      let gt248 = REWRITE_RULE[SYM bridge4] (find_a (fun th -> concl th = `248 < LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list)`)) in
      let ja_taken = MP (ISPECL [mk_binop `(+):num->num->num` `acc3:num` `LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i+12,4) inlist):int16 list)`; `248`] JA_TAKEN_GT) (CONJ gt248 lt32) in
      (* POPCNT_BYTE3's masked arg is the byte-tower `word(val mask8d MOD 256):byte`
         (unlike POPCNT_BYTE1/BYTE2 which are i32-tower), so `pop_len4` already has the
         byte-tower LHS matching the RIP COND; the zbe (byte->i32) bridge needed for
         BYTE1/BYTE2 does not apply here.  Provide both the byte form and (only when it
         constructs) the zbe-bridged i32 form in the rewrite list, so REWRITE picks
         whichever matches the actual RIP COND tower — the try/with keeps a TRANS failure
         on the unused typed form from aborting the tactic. *)
      let poprws =
        pop_len4 ::
        (try [TRANS (AP_TERM `word_popcount:int32->num`
                (MP (SPEC `val (mask8d:int64) MOD 256` zxbyte_eq)
                    (ARITH_RULE `val (mask8d:int64) MOD 256 < 256`))) pop_len4]
         with Failure _ -> []) in
      eta2_rip_mp memsafe 399 71 THEN
      REWRITE_TAC poprws THEN REWRITE_TAC[rax_red0] THEN
      REWRITE_TAC[ja_taken] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  (* rebuild pop_len4/rax_red0/bridge4 for the RAX-final collapse below (ASSUME them now,
     AFTER stepping, so they don't interfere with the stepper). *)
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let m8c_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8c:int64` | _ -> false) in
    let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
    let m8d_val = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8d:int64` && can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))(concl th) | _ -> false) in
    let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
    let popcnt4 = REWRITE_RULE[m8d_val] (REWRITE_RULE[m8b_def; m8c_def]
       (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE3))) in
    let lanesum = rand(concl popcnt4) in
    let mb4 = find_a (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f1bnd:int256`))c &&
       can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),n) -> n=`24` | _ -> false))c) in
    let mb4_tm = concl mb4 in
    let i_le = find_a (fun th -> concl th = `16 * i <= 120`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
    let blk16 = find_a (fun th -> is_eq(concl th) && (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=120 ==> 16*i+16<=136`) i_le)) blk16) in
    let blk3_eq = el 3 (CONJUNCTS bb) in
    let block3 = `[word_subword (chunk0:int128) (96,8); word_subword chunk0 (104,8); word_subword chunk0 (112,8); word_subword chunk0 (120,8)]:byte list` in
    let block3len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA2`, block3)) in
    let bsum4_raw = prove(mk_imp(mb4_tm, mk_eq(lanesum, block3len_x)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER_ETA2] THEN
      SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let pop_len4 = REWRITE_RULE[GSYM blk3_eq] (TRANS popcnt4 (MP bsum4_raw mb4)) in
    let bridge4 = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc3",_)),_)),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA2_BYTES",_),_)))->true|_->false) in
    let lt32 = REWRITE_RULE[SYM bridge4] (find_a (fun th -> concl th = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list) < 2 EXP 32`)) in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    ASSUME_TAC pop_len4 THEN ASSUME_TAC rax_red0) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* Do not rewrite 16*(i+1)->16*i+16 here: the postcondition midexit4_eta2_tm is stated
     in 16*(i+1) form, and bridge4/ntake are too — an early normalise to 16*i+16 leaves the
     RAX/memory conjuncts as niblen(16*(i+1))=niblen(16*i+16) unclosed.  Keep 16*(i+1)
     throughout; the RCX collapse reconciles its own 16*i+16 tail back to 16*(i+1) at the end. *)
  (* RAX collapse (pop_len4 -> rax_red0 -> bridge4 -> niblen(16(i+1))).  pop_len4 is the
     byte-tower (POPCNT_BYTE3) so REWRITE directly; zbe-bridged form kept as fallback. *)
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let pop_len4 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) ->
          can(find_term(fun u->u=`mask8d:int64`))(concl th) | _ -> false) asl in
    let rax_red0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) ->
          can(find_term(fun u->u=`acc3:num`))(concl th) | _ -> false) asl in
    let bridge4 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc3",_)),_)),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA2_BYTES",_),_)))->true|_->false) asl in
 (* The RAX-conjunct carries the explicit block3 list [chunk0 96,104,112,120];
       convert -> SUB_LIST(16i+12,4) via GSYM blk3_eq first, so bridge4
       (SUB_LIST form) folds it. *)
    let i_le = find_a (fun th -> concl th = `16 * i <= 120`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 136`) in
    let blk16 = find_a (fun th -> is_eq(concl th) && (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=120 ==> 16*i+16<=136`) i_le)) blk16) in
    let blk3_eq = el 3 (CONJUNCTS bb) in
    let poprws =
      (snd pop_len4) ::
      (try [TRANS (AP_TERM `word_popcount:int32->num`
              (MP (SPEC `val (mask8d:int64) MOD 256` zxbyte_eq)
                  (ARITH_RULE `val (mask8d:int64) MOD 256 < 256`))) (snd pop_len4)]
       with Failure _ -> []) in
    REWRITE_TAC[GSYM blk3_eq] THEN
    REWRITE_TAC (poprws @ [snd rax_red0; snd bridge4])) THEN
 (* The RIP conjunct of the postcondition is the raw stepper
     COND `if <cond over niblen(16(i+1))> then pc+399 else pc+97`; after the RAX
     collapse folds it to a COND over niblen(16(i+1)), fold the COND -> pc+399 via
     JA_TAKEN_GT. Needs `248<niblen(16(i+1))` + `niblen(16(i+1))<2^32`
     (both in scope from the earlier SUBGOAL_THENs). *)
  W(fun (asl,w) ->
    let ntake = MP (ISPECL [`LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list)`;`248`] JA_TAKEN_GT)
                   (CONJ (ASSUME `248 < LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list)`)
                         (ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list) < 2 EXP 32`)) in
    REWRITE_TAC[ntake]) THEN
  (* RCX collapse: quadruple +4 nest (16i -> +4 -> +8 -> +12 -> +16)         *)
  MP_TAC(SPEC `16*i` RCX4_COLLAPSE) THEN ANTS_TAC THENL [UNDISCH_TAC `16*i<=120` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(SPEC `16*i+4` RCX4_COLLAPSE) THEN ANTS_TAC THENL [UNDISCH_TAC `16*i<=120` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[ARITH_RULE `(16*i+4)+4 = 16*i+8`] THEN
  MP_TAC(SPEC `16*i+8` RCX4_COLLAPSE) THEN ANTS_TAC THENL [UNDISCH_TAC `16*i<=120` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[ARITH_RULE `(16*i+8)+4 = 16*i+12`] THEN
  MP_TAC(SPEC `16*i+12` RCX4_COLLAPSE) THEN ANTS_TAC THENL [UNDISCH_TAC `16*i<=120` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[ARITH_RULE `(16*i+12)+4 = 16*i+16`] THEN
  (* After the RCX collapse two conjuncts remain — RCX
     `word(16*i+16) = word(16*(i+1))` and the memory store `read(mem...16*(i+1)...) = num_of_wordlist
     (...16*(i+1)...)`.  Normalise the goal's 16*(i+1) -> 16*i+16 (the SI4_BODY4 store fact is folded
     to SUB_LIST(0,16*i+16)), then ASM_REWRITE closes both (RCX by REFL, memory by the folded store
     assumption); REFL_TAC/ARITH mop up any residual. *)
  REWRITE_TAC[ARITH_RULE `16*(i+1) = 16*i+16`] THEN
  ASM_REWRITE_TAC[] THEN TRY(CONJ_TAC) THEN TRY REFL_TAC THEN TRY(AP_TERM_TAC THEN ARITH_TAC) THEN (if memsafe then disch else ALL_TAC);;
let MID_EXIT_CASE4_ETA2 = prove(midexit4_eta2_tm, mk_midexit4_eta2 false ETA2_MIDEXIT_PREFIX_TAC ALL_TAC);;

(* ========================================================================= *)
(* eta2 CORRECT: MIDEXIT_ARM_TAC + assemble MLDSA_REJ_UNIFORM_ETA2_CORRECT.  *)
(*                                                                           *)
(* MIDEXIT_ARM_TAC closes the scaffold's MID-EXIT arm (the FALSE branch of   *)
(* ASM_CASES niblen(16N)<=248): pre @ pc+86/pos16(N-1), niblen(16(N-1))<=248, *)
(* niblen(16N)>248.  Case-splits on the first crossover p in                 *)
(* {16(N-1)+4,+8,+12,16N} and dispatches MID_EXIT_SUBITER{1,2,3}@(N-1) /     *)
(* MID_EXIT_CASE4@(N-1) reaching pc+399@p, then SCALAR_TAIL_AT_P@p -> pc+542. *)
(*                                                                           *)
(* leg2 needs ENSURES_FRAME_SUBSUMED (AT_P frame ZMM0..6 c CORRECT ZMM0..9), *)
(* same as OFFSET_ARM's leg2.                                                *)
(* ========================================================================= *)

let AT_P_NOLET = CONV_RULE(TOP_DEPTH_CONV let_CONV) MLDSA_REJ_UNIFORM_ETA2_SCALAR_TAIL_AT_P;;

(* dispatch one crossover case: midthm @ i:=N-1 reaches pc+399@pexpr; prevpos =
   niblen(pexpr-4)<=248 (in context) used to derive niblen(pexpr)<=256; then
   SCALAR_TAIL_AT_P@pexpr.  eta2: pc+399, ZMM0..6 c ZMM0..9 subsumption in leg2. *)
let MIDEXIT_DISPATCH (midthm:thm) (pexpr:term) (prevpos:term) : tactic =
  let qpost = vsubst [`N-1`,`i:num`] (rand(rator(snd(dest_imp(snd(strip_forall(concl midthm))))))) in
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC qpost THEN
  CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* leg1: MID_EXIT lemma @ N-1 *)
    MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`N-1`;`stackpointer:int64`] midthm) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]); DISCH_THEN ACCEPT_TAC];
    (* leg2: niblen(pexpr)<=256 then SCALAR_TAIL_AT_P@pexpr                  *)
    SUBGOAL_THEN (mk_comb(mk_comb(`(<=):num->num->bool`,
        mk_comb(`LENGTH:(int32)list->num`, mk_comb(`REJ_SAMPLE_ETA2_BYTES:byte list->int32 list`,
          mk_comb(mk_comb(`SUB_LIST:num#num->byte list->byte list`,mk_pair(`0`,pexpr)),`inlist:byte list`)))), `256`)) ASSUME_TAC THENL
     [SUBGOAL_THEN (mk_eq(pexpr, mk_binop `(+):num->num->num` prevpos `4`)) SUBST1_TAC THENL
       [UNDISCH_TAC `~(N=0)` THEN UNDISCH_TAC `16 * N <= 136` THEN ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC OUTLEN0_LE_256_FROM_SUBITER_ETA2 THEN CONJ_TAC THENL
       [UNDISCH_TAC `16 * N <= 136` THEN UNDISCH_TAC `~(N=0)` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=136` THEN ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;pexpr;`stackpointer:int64`] AT_P_NOLET) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]); ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_FRAME_SUBSUMED) THEN
    REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN SUBSUMED_MAYCHANGE_TAC];;

let MIDEXIT_ARM_TAC : tactic =
  (* setup facts (idempotent if already present)                             *)
  SUBGOAL_THEN `248 < LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*N) inlist):int32 list)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(LENGTH (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,16 * N) inlist):int32 list) <= 248)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * N <= 136` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (N-1) <= 120` THEN UNDISCH_TAC `~(N=0)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * ((N-1)+1) <= 136` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * N <= 136` THEN UNDISCH_TAC `~(N=0)` THEN ARITH_TAC; ALL_TAC] THEN
  (* crossover case-split                                                    *)
  ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(N-1)+4) inlist):int32 list) <= 248` THENL
   [ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(N-1)+8) inlist):int32 list) <= 248` THENL
     [ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(N-1)+12) inlist):int32 list) <= 248` THENL
       [(* all 3 internal <=248 -> case-4, p = 16*((N-1)+1) *)
        SUBGOAL_THEN `248 < LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*((N-1)+1)) inlist):int32 list)` ASSUME_TAC THENL
         [SUBGOAL_THEN `16*((N-1)+1) = 16*N` SUBST1_TAC THENL
           [UNDISCH_TAC `~(N=0)` THEN ARITH_TAC; ALL_TAC] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MIDEXIT_DISPATCH MID_EXIT_CASE4_ETA2 `16*((N-1)+1)` `16*(N-1)+12`;
        (* niblen(16(N-1)+12)>248 -> case-3, p=16(N-1)+12                    *)
        MIDEXIT_DISPATCH MID_EXIT_SUBITER3_ETA2 `16*(N-1)+12` `16*(N-1)+8`];
      (* niblen(16(N-1)+8)>248 -> case-2, p=16(N-1)+8                        *)
      MIDEXIT_DISPATCH MID_EXIT_SUBITER2_ETA2 `16*(N-1)+8` `16*(N-1)+4`];
    (* niblen(16(N-1)+4)>248 -> case-1, p=16(N-1)+4                          *)
    MIDEXIT_DISPATCH MID_EXIT_SUBITER1_ETA2 `16*(N-1)+4` `16*(N-1)`];;

(* ========================================================================= *)
(* Main CORRECT theorem.                                                     *)
(* ========================================================================= *)
let MLDSA_REJ_UNIFORM_ETA2_CORRECT = prove(correct_eta2_tm,
  CORRECT_SCAFFOLD_TAC THEN
  ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THENL
   [OFFSET_ARM_TAC; MIDEXIT_ARM_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine correctness with array_abs_bound matching CBMC contract        *)
(* ensures(array_abs_bound(r, 0, return_value, MLDSA_ETA + 1)) for eta = 2.  *)
(* ------------------------------------------------------------------------- *)

(* NOTE: This must be kept in sync with the CBMC specification
 * in mldsa/src/native/x86_64/src/arith_native_x86_64.h *)

(* Bounded byte-shape core (CBMC array-abs-bound postcondition), exposed at   *)
(* top level so the Windows subroutine wrapper below can reuse it as its core *)
(* correctness theorem (the manual xmm-spill splice needs the BUTLAST form).  *)
let MLDSA_REJ_UNIFORM_ETA2_CORRECT_BOUND = prove
   (`!res buf table (inlist:byte list) pc.
      LENGTH inlist = 136 /\
      nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (res, 1024) /\
      nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (buf, 136) /\
      nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (table, 2048) /\
      nonoverlapping (res, 1024) (buf, 136) /\
      nonoverlapping (res, 1024) (table, 2048)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [res; buf; table] s /\
                read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
                read(memory :> bytes(table,2048)) s =
                  num_of_wordlist mldsa_rej_uniform_table)
           (\s. read RIP s = word(pc + LENGTH (BUTLAST mldsa_rej_uniform_eta2_tmc)) /\
                (let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA2_BYTES inlist) in
                 let outlen = LENGTH outlist in
                 outlen <= 256 /\
                 C_RETURN s = word outlen /\
                 read(memory :> bytes(res,4 * outlen)) s =
                   num_of_wordlist outlist /\
                 (!i. i < outlen
                      ==> ival(EL i outlist:int32) < &3 /\
                          -- &3 < ival(EL i outlist:int32))))
           (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(res,1024)])`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_STRENGTHEN_POST_X86 THEN
    EXISTS_TAC
     `\s:x86state.
        read RIP s = word(pc + LENGTH(BUTLAST mldsa_rej_uniform_eta2_tmc)) /\
        (let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA2_BYTES (inlist:byte list)) in
         let outlen = LENGTH outlist in
         C_RETURN s = word outlen /\
         read(memory :> bytes(res:int64,4 * outlen)) s =
           num_of_wordlist outlist)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MLDSA_REJ_UNIFORM_ETA2_CORRECT THEN ASM_REWRITE_TAC[];
      BETA_TAC THEN GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_ACCEPT_TAC LENGTH_SUB_LIST_REJ_SAMPLE_ETA2_BYTES; ALL_TAC] THEN
      MATCH_ACCEPT_TAC REJ_SAMPLE_ETA2_BYTES_EL_BOUND]);;

let MLDSA_REJ_UNIFORM_ETA2_CORRECT_BOUND_CONCRETE =
  CONV_RULE(REWRITE_CONV[LENGTH_MLDSA_REJ_UNIFORM_ETA2_TMC;
                         fst MLDSA_REJ_UNIFORM_ETA2_EXEC])
    MLDSA_REJ_UNIFORM_ETA2_CORRECT_BOUND;;

let MLDSA_REJ_UNIFORM_ETA2_NOIBT_SUBROUTINE_CORRECT =
  let correct_bound_concrete = MLDSA_REJ_UNIFORM_ETA2_CORRECT_BOUND_CONCRETE in
  let saved_tic = !type_invention_error in
  type_invention_error := false;
  let th = prove
   (`!res buf table (inlist:byte list) pc stackpointer returnaddress.
        LENGTH inlist = 136 /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (res, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (buf, 136) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (table, 2048) /\
        nonoverlapping (res, 1024) (buf, 136) /\
        nonoverlapping (res, 1024) (table, 2048) /\
        nonoverlapping (stackpointer, 8) (res, 1024) /\
        nonoverlapping (stackpointer, 8) (buf, 136) /\
        nonoverlapping (stackpointer, 8) (table, 2048) /\
        nonoverlapping (stackpointer, 8) (word pc, LENGTH mldsa_rej_uniform_eta2_tmc)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_rej_uniform_eta2_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [res; buf; table] s /\
                  read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (let outlist = SUB_LIST(0,256)
                      (REJ_SAMPLE_ETA2_BYTES inlist) in
                   let outlen = LENGTH outlist in
                   outlen <= 256 /\
                   C_RETURN s = word outlen /\
                   read(memory :> bytes(res,4 * outlen)) s =
                     num_of_wordlist outlist /\
                   (!i. i < outlen
                        ==> ival(EL i outlist:int32) < &3 /\
                            -- &3 < ival(EL i outlist:int32))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
    REWRITE_TAC[LENGTH_MLDSA_REJ_UNIFORM_ETA2_TMC] THEN
    X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_rej_uniform_eta2_tmc
      correct_bound_concrete) in
  type_invention_error := saved_tic;
  th;;

(* ------------------------------------------------------------------------- *)
(* 4. Full (untrimmed, IBT-prefixed) subroutine wrapper via ADD_IBT_RULE.    *)
(*    This is the byte-shaped inner theorem (postcondition over the          *)
(*    REJ_SAMPLE_ETA2_BYTES int16-path spec applied to a byte list); the     *)
(*    public spec below fronts it with the nibble-list REJ_SAMPLE_ETA2 spec. *)
(* ------------------------------------------------------------------------- *)
let MLDSA_REJ_UNIFORM_ETA2_SUBROUTINE_CORRECT_BYTES =
  ADD_IBT_RULE MLDSA_REJ_UNIFORM_ETA2_NOIBT_SUBROUTINE_CORRECT;;

(* ------------------------------------------------------------------------- *)
(* 5. Public subroutine correctness, fronted with the nibble-list spec       *)
(*    REJ_SAMPLE_ETA2 over inlist:(4 word) list (mirrors aarch64). The buffer *)
(*    is a fixed 136 bytes, so the nibble input list has length 272. We      *)
(*    bridge to the byte-shaped inner theorem: for any nibble list of even   *)
(*    length there is a byte list whose nibble decomposition matches it      *)
(*    (BYTES_TO_NIBBLES_SURJ), and REJ_SAMPLE_ETA2(BYTES_TO_NIBBLES bs) =    *)
(*    REJ_SAMPLE_ETA2_BYTES bs (REJ_SAMPLE_ETA2_BYTES_EQ).                   *)
(* ------------------------------------------------------------------------- *)
let MLDSA_REJ_UNIFORM_ETA2_SUBROUTINE_CORRECT = prove
 (`!res buf table (inlist:(4 word) list) pc stackpointer returnaddress.
      LENGTH inlist = 272 /\
      nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_mc) (res, 1024) /\
      nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_mc) (buf, 136) /\
      nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_mc) (table, 2048) /\
      nonoverlapping (res, 1024) (buf, 136) /\
      nonoverlapping (res, 1024) (table, 2048) /\
      nonoverlapping (stackpointer, 8) (res, 1024) /\
      nonoverlapping (stackpointer, 8) (buf, 136) /\
      nonoverlapping (stackpointer, 8) (table, 2048) /\
      nonoverlapping (stackpointer, 8) (word pc, LENGTH mldsa_rej_uniform_eta2_mc)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mldsa_rej_uniform_eta2_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [res; buf; table] s /\
                read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
                read(memory :> bytes(table,2048)) s =
                  num_of_wordlist mldsa_rej_uniform_table)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                (let outlist = SUB_LIST(0,256)
                    (REJ_SAMPLE_ETA2 inlist) in
                 let outlen = LENGTH outlist in
                 outlen <= 256 /\
                 C_RETURN s = word outlen /\
                 read(memory :> bytes(res,4 * outlen)) s =
                   num_of_wordlist outlist /\
                 (!i. i < outlen
                      ==> ival(EL i outlist:int32) < &3 /\
                          -- &3 < ival(EL i outlist:int32))))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,1024)])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPEC `inlist:(4 word) list` BYTES_TO_NIBBLES_SURJ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[EVEN_EXISTS] THEN EXISTS_TAC `136` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `bs:byte list` STRIP_ASSUME_TAC) THEN
  UNDISCH_THEN `BYTES_TO_NIBBLES (bs:byte list) = inlist`
    (SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_BYTES_TO_NIBBLES]) THEN
  SUBGOAL_THEN `LENGTH (bs:byte list) = 136` ASSUME_TAC THENL
   [UNDISCH_TAC `2 * LENGTH (bs:byte list) = 272` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NUM_OF_BYTES_TO_NIBBLES; GSYM REJ_SAMPLE_ETA2_BYTES_EQ] THEN
  MP_TAC(SPECL
   [`res:int64`; `buf:int64`; `table:int64`; `bs:byte list`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`]
   MLDSA_REJ_UNIFORM_ETA2_SUBROUTINE_CORRECT_BYTES) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

(* ========================================================================= *)
(* Memory safety.                                                            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Memory-safety section.  Rides on the generic constant-time / memory-safety *)
(* infrastructure in consttime.ml (which transitively pulls equiv.ml and     *)
(* supplies SIMPLIFY_MAYCHANGES_TAC / allowed_vars_e / EXISTS_E2_TAC /       *)
(* SAFE_META_EXISTS_TAC / DISCHARGE_MEMACCESS_INBOUNDS_TAC, plus             *)
(* memaccess_inbounds, MEMACCESS_INBOUNDS_APPEND and the CONTAINED_MODULO_*  *)
(* lemmas).  This file sets type_invention_error := true globally for the    *)
(* CORRECT proofs, but equiv.ml's MAYCHANGE-range helper only typechecks under *)
(* the HOL default (false); on a cold load these deps load fresh here, so we *)
(* toggle the default around the needs and then restore this file's setting. *)
(* ------------------------------------------------------------------------- *)
type_invention_error := false;;
needs "x86/proofs/consttime.ml";;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Shared memory-safety discharge tactics (ride on consttime.ml).            *)
(* ------------------------------------------------------------------------- *)

let DISCHARGE_MEMSAFE_TAC:tactic =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(* Like SIMPLE_ARITH_TAC but allows `val` in assumptions since
   contained_modulo bounds may involve val terms. Filters out
   read/write/word simulation cruft that makes ASM_ARITH_TAC slow. *)
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

(* Bring `bitval p <= 1` as a MP_TAC hypothesis so MEMSAFE_ARITH_TAC's
   ARITH_RULE can derive bounds on bitval-sum expressions arising from
   VPMOVMSKPS-derived table indices. *)

let MEMSAFE_BITVAL_TAC:tactic =
  W(fun (asl,w) ->
    let bvs = find_terms (fun t ->
      try fst(dest_const(rator t)) = "bitval" with _ -> false) w in
    let bvs = setify bvs in
    MAP_EVERY (fun bv ->
      MP_TAC(SPEC (rand bv) BITVAL_BOUND)) bvs);;

(* ASM-aware version of CONTAINED_TAC for loop-body proofs where
   memory addresses involve symbolic loop variables. Uses MEMSAFE_ARITH_TAC
   which filters assumptions to avoid the performance issues of ASM_ARITH_TAC
   with hundreds of symbolic simulation assumptions. *)

let CONTAINED_ASM_TAC =
  GEN_REWRITE_TAC I [GSYM CONTAINED_MODULO_MOD2] THEN
  GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o LAND_CONV o TOP_DEPTH_CONV)
   [VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC(BINOP_CONV(LAND_CONV MOD_DOWN_CONV)) THEN
  REWRITE_TAC[CONTAINED_MODULO_MOD2; CONTAINED_MODULO_LMOD] THEN
  ((GEN_REWRITE_TAC I [CONTAINED_MODULO_REFL] THEN
    MEMSAFE_BITVAL_TAC THEN MEMSAFE_ARITH_TAC) ORELSE
   (MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN
    MEMSAFE_BITVAL_TAC THEN MEMSAFE_ARITH_TAC) ORELSE
   (MATCH_MP_TAC CONTAINED_MODULO_SIMPLE THEN
    MEMSAFE_BITVAL_TAC THEN MEMSAFE_ARITH_TAC));;

(* ASM-aware version of DISCHARGE_MEMSAFE_TAC for loop bodies.
   Uses CONTAINED_ASM_TAC for contained_modulo proofs with symbolic bounds. *)

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

(* ========================================================================= *)
(* MEMSAFE component: PREFIX_G_FULL_MS2_TAC                                  *)
(* ========================================================================= *)

(* PREFIX_G_FULL_MS2_TAC  : a VERBATIM copy of the value
   PREFIX_G_FULL_TAC with a single edit — STRIP_EXISTS_ASSUM_TAC right after
   ENSURES_INIT_TAC "s0". Purpose: anchor the precondition's events existential
   `read events s0 = APPEND e_acc e` (state-free RHS) so the stepper FLATTENS each
   `read events s(k+1)=CONS(ev)(read events sk)` to reference only the current
   state — surviving BOTH DISCARD_OLDSTATE_TAC and PURGE_STALE_STATES_TAC. This is
   the events-preservation mechanism applied to the existing
 value chain (no KEEPEV, no _MS rewrites). Confirmed by exp_flatten. *)

let TABLE_IDX_LT_256 = prove
 (`!K:num. val((word_zx:(M)word->int64)
              ((word_zx:(N)word->(M)word)
              ((word:num->(N)word)(K MOD 256)))) < 256`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD] THEN
  TRANS_TAC LET_TRANS `K MOD 256` THEN
  CONJ_TAC THENL
   [MESON_TAC[MOD_LE; LE_TRANS];
    SIMP_TAC[DIVISION; ARITH_EQ]]);;

(* idx < 256  ==>  the 8-byte gather load at table + 8*idx is contained in
   the 2048-byte table region (8*idx + 8 <= 8*255 + 8 = 2048). *)

let GATHER_CONTAINED = prove
 (`!(table:int64) idx:int64. val idx < 256
     ==> contained_modulo (2 EXP 64)
           (val(word_add table (word(8 * val idx))),8) (val table,2048)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [GSYM CONTAINED_MODULO_MOD2] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV MOD_DOWN_CONV) THEN
  REWRITE_TAC[CONTAINED_MODULO_MOD2] THEN
  MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN
  ASM_ARITH_TAC);;

(* Per-residual closer: pick the `(table,2048)` disjunct and apply the bounds.
   Works uniformly for all 4 (the 3 mask gathers and the f1bnd popcount nest). *)

let GATHER_BOUND_TAC : tactic =
  DISJ2_TAC THEN MATCH_MP_TAC GATHER_CONTAINED THEN MATCH_ACCEPT_TAC TABLE_IDX_LT_256;;

(* ------------------------------------------------------------------------- *)
(* The full body proof.                                                      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Top-level discharge for a straight-line memory-safety obligation:         *)
(*   exists e2. read events s = APPEND e2 e /\ memaccess_inbounds e2 rr wr.  *)
(* (This is the events-only specialisation of consttime.ml's                 *)
(*  DISCHARGE_SAFETY_PROPERTY_TAC; the f_events unification clause is absent *)
(*  because the spec leaves e2 fully existential.)                           *)
(* ------------------------------------------------------------------------- *)
let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* Gather-index bound lemmas.                                                *)
(* The 4 residual disjuncts all carry a table index of the shape             *)
(* word_zx (word_zx (word (K MOD 256)))  for some K:num.                     *)
(* Since K is universally quantified, ONE lemma covers all four.             *)
(* ------------------------------------------------------------------------- *)

let ETA2_PREFIX_OPEN_MS_TAC : tactic = mk_eta2_prefix_open true;;

(* ETA2_PREFIX_TO_S8_MS_TAC = ETA2_PREFIX_TO_S8_TAC on top of the MS open. *)
let ETA2_PREFIX_TO_S8_MS_TAC : tactic = mk_eta2_prefix_to_s8 true;;

let ETA2_PREFIX_TO_S9_MS_TAC : tactic = mk_eta2_prefix_to_s9 true;;

let ETA2_PREFIX_TO_S11_MS_TAC : tactic = mk_eta2_prefix_to_s11 true;;

(* ------------------------------------------------------------------------- *)
(* ETA2_SI1_COUNTER_MS_TAC: as ETA2_SI1_COUNTER_TAC except the               *)
(* s26 mid-guard RIP resolution now uses the structural COND match (as SI2/SI3). *)
(* ------------------------------------------------------------------------- *)
let ETA2_SI1_COUNTER_MS_TAC : tactic =
  X86_STEPS_TAC EXEC (21--24) THEN
  MP_TAC(ISPECL[`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `LENGTH(inlist:byte list) = 136` THEN
    UNDISCH_TAC `16 * i <= 120` THEN ARITH_TAC; STRIP_TAC] THEN
  W(fun (asl,w) ->
     let m8def = find (fun th -> match concl th with Comb(Comb(Const("=",_),_),Var("mask8",_)) -> true | _ -> false) (map snd asl) in
     RULE_ASSUM_TAC(fun th -> if concl th = maskbit_tgt ||
        can(find_term(fun u->match u with Const("TABLE_ENTRY",_)->true|_->false))(concl th)
        then th else REWRITE_RULE[GSYM m8def] th)) THEN
  W(fun (asl,w) ->
    let r9 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("R9",_)),Var("s24",_))),_) -> true | _ -> false) asl in
    let goal_pc = find_term (fun t -> match t with Comb(Const("word_popcount",_),_) -> true | _ -> false) (concl(snd r9)) in
    let low8 = `bitval(bit 7 (word_subword (f1bnd:int256) (0,8):byte)) + bitval(bit 7 (word_subword f1bnd (8,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (16,8):byte)) + bitval(bit 7 (word_subword f1bnd (24,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (32,8):byte)) + bitval(bit 7 (word_subword f1bnd (40,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (48,8):byte)) + bitval(bit 7 (word_subword f1bnd (56,8):byte))` in
    let mr = CONV_RULE(DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV)
               (SPEC `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` MOD_RED) in
    let popeq = prove(mk_eq(goal_pc, low8),
      REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; MOD_MOD_EXP_MIN] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; mr] THEN
      MAP_EVERY (fun b -> BOOL_CASES_TAC b)
        [`bit 7 (word_subword (f1bnd:int256) (0,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (8,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (16,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (24,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (32,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (40,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (48,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (56,8):byte)`] THEN
      REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV) in
    let maskbit = snd(find (fun (_,th) -> let c=concl th in is_forall c &&
        can(find_term(fun u->u=`f1bnd:int256`))c && can(find_term(fun u->match u with Comb(Const("bit",_),_)->true|_->false))c &&
        not(can(find_term(fun u->match u with Const("word_zx",_)->true|_->false))c) &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (24,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (32,8):byte`))c)) asl) in
    let mb_tm = concl maskbit in
    let blk0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
           (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
    let blkeq = mk_eq(low8, `LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i,4) inlist):int16 list)`) in
    let blk0_tm = concl(snd blk0) in
    let bsum_raw = prove(mk_imp(mb_tm, mk_imp(blk0_tm, blkeq)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN DISCH_THEN(fun b -> REWRITE_TAC[b]) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER_ETA2] THEN
      ASM_SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let bsum = MP (MP bsum_raw maskbit) (snd blk0) in
    let pop_len = TRANS popeq bsum in
    let leninl = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Var("inlist",_))),_) -> true | _ -> false) asl in
    let i116 = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("<=",_),Comb(Comb(Const("*",_),_),Comb(Comb(Const("+",_),Var("i",_)),_))),_) -> true | _ -> false) asl in
    let nible = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("<=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_NIBBLES_ETA2",_),_))),_) -> true | _ -> false) asl in
    let len_eq = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) asl in
    let a1 = MP (MP (ARITH_RULE `16*(i+1)<=136 ==> (LENGTH(inlist:byte list)=136 ==> 16*(i+1)<=LENGTH inlist)`)
                    (snd i116)) (snd leninl) in
    let bnd0 = MP (ISPECL[`inlist:byte list`;`i:num`] SUBITER_OUTLEN_BOUND_1) (CONJ a1 (snd nible)) in
    let bnd = REWRITE_RULE[snd len_eq] bnd0 in
    let block0len = `LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i,4) inlist):int16 list)` in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let ja = MP (ISPECL[mk_binop `(+):num->num->num` `outlen0:num` block0len; `248`] JA_NOT_TAKEN_LE)
                (CONJ bnd (ARITH_RULE `248 < 2 EXP 32`)) in
    ASSUME_TAC pop_len THEN ASSUME_TAC bnd THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja) THEN
  X86_STEPS_TAC EXEC (25--26) THEN
  (* MS FIX: resolve RIP s26 = pc+207 via the structural COND match (SI2/SI3 style),
     not find_term(pc+207) — the anchored events fact also mentions pc+207. *)
  SUBGOAL_THEN `read RIP s26 = word (pc + 207):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let blk0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
             (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
      let rax_red0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
      let ja = find (fun (_,th) -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th)) asl in
      let ifrip = find (fun (_,th) -> match concl th with
         Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s26",_))),r) ->
           (match r with Comb(Comb(Comb(Const("COND",_),_),_),_) -> true | _ -> false) | _ -> false) asl in
      MP_TAC (snd ifrip) THEN
      REWRITE_TAC[GSYM(snd blk0)] THEN REWRITE_TAC[snd rax_red0] THEN
      REWRITE_TAC[snd ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  W(fun (asl,w) ->
    let pl = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
    let rr = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
    RULE_ASSUM_TAC(REWRITE_RULE[snd pl]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd rr])) THEN
  ALL_TAC;;

(* ------------------------------------------------------------------------- *)
(* The full body proof.  SI2/SI3/SI4 counters + SI*_FOLD + finals are reused *)
(* as-is (already events-robust); only PREFIX and SI1_COUNTER are MS copies. *)
(* ------------------------------------------------------------------------- *)
let ETA2_CLEAN_BODY_MS_FULL_TAC : tactic =
  ETA2_PREFIX_TO_S11_MS_TAC THEN
  ETA2_SI1_FOLD THEN ETA2_SI1_COUNTER_MS_TAC THEN
  ETA2_SI2_FOLD THEN ETA2_SI2_COUNTER_TAC THEN
  ETA2_SI3_FOLD THEN ETA2_SI3_COUNTER_TAC THEN
  ETA2_SI4_FOLD THEN ETA2_SI4_COUNTER_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16*i+16 = 16*(i+1)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ETA2_RAX_FINAL_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ETA2_RCX_FINAL_TAC; ALL_TAC] THEN
  DISCHARGE_MEMSAFE_ASM_TAC THEN
  GATHER_BOUND_TAC;;

(* ------------------------------------------------------------------------- *)
(* Build the MS goal terms (events existential in pre & post, layered onto    *)
(* the value CLEAN_BLOCK/CLEAN_BODY pre/post).  Prove the RELAXED-hyps        *)
(* CLEAN_BLOCK_MEMSAFE first by full simulation; the tighter-hyps             *)
(* CLEAN_BODY_MEMSAFE (two EXTRA hyps `~(N=0)`, `i+1<N`, identical conclusion) *)
(* then follows by weakening — no second 71-step simulation.                  *)
(* ------------------------------------------------------------------------- *)
let clean_block_ms_eta2_tm =
  let qvars, body = strip_forall clean_block_eta2_tm in
  let hyps_tm, ens = dest_imp body in
  let ensc, ppf = strip_comb ens in
  let pre = el 1 ppf and post = el 2 ppf and frame = el 3 ppf in
  let sv, preb = dest_abs pre in
  let sv2, postb = dest_abs post in
  let evtempl = `exists e_acc:(uarch_event)list. read events (s:x86state) = APPEND e_acc (e:(uarch_event)list) /\ memaccess_inbounds e_acc [(buf:int64),136; (table:int64),2048] [(res:int64),1024]` in
  let pre' = mk_abs(sv, mk_conj(preb, vsubst[sv,`s:x86state`] evtempl)) in
  let post' = mk_abs(sv2, mk_conj(postb, vsubst[sv2,`s:x86state`] evtempl)) in
  let ens' = list_mk_comb(ensc,[el 0 ppf; pre'; post'; frame]) in
  list_mk_forall(qvars @ [`e:(uarch_event)list`], mk_imp(hyps_tm, ens'));;

let ETA2_CLEAN_BLOCK_MEMSAFE = prove(clean_block_ms_eta2_tm, ETA2_CLEAN_BODY_MS_FULL_TAC);;

let clean_body_ms_eta2_tm =
  let qvars, body = strip_forall (concl MLDSA_REJ_UNIFORM_ETA2_CLEAN_BODY) in
  let hyps_tm, ens = dest_imp body in
  let ensc, ppf = strip_comb ens in
  let pre = el 1 ppf and post = el 2 ppf and frame = el 3 ppf in
  let sv, preb = dest_abs pre in
  let sv2, postb = dest_abs post in
  let evtempl = `exists e_acc:(uarch_event)list. read events (s:x86state) = APPEND e_acc (e:(uarch_event)list) /\ memaccess_inbounds e_acc [(buf:int64),136; (table:int64),2048] [(res:int64),1024]` in
  let pre' = mk_abs(sv, mk_conj(preb, vsubst[sv,`s:x86state`] evtempl)) in
  let post' = mk_abs(sv2, mk_conj(postb, vsubst[sv2,`s:x86state`] evtempl)) in
  let ens' = list_mk_comb(ensc,[el 0 ppf; pre'; post'; frame]) in
  list_mk_forall(qvars @ [`e:(uarch_event)list`], mk_imp(hyps_tm, ens'));;

let MLDSA_REJ_UNIFORM_ETA2_CLEAN_BODY_MEMSAFE =
  prove(clean_body_ms_eta2_tm,
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC ETA2_CLEAN_BLOCK_MEMSAFE THEN
    ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* ETA2 SCALAR_TAIL_BODY_MEMSAFE:                                            *)
(* the eta2 scalar-tail per-byte body (pc+399 -> pc+399) strengthened with the *)
(* memory-safety events conjunct                                             *)
(* exists e_acc. read events s = APPEND e_acc e /\                           *)
(* memaccess_inbounds e_acc [buf,136;table,2048] [res,1024]                  *)
(* in BOTH pre and post.                                                     *)
(*                                                                           *)
(* Reuses the value chain with two changes:                                  *)
(* 1. SCALAR_BODY_SETUP_ETA2 -> SCALAR_BODY_SETUP_ETA2_MS: STRIP_EXISTS_ASSUM_TAC *)
(* after ENSURES_INIT anchors `read events s0 = APPEND e_acc e` (state-free  *)
(* RHS) so each step's events CONS fact survives DISCARD_OLDSTATE.           *)
(* 2. Each of the 4 leaf value closers is wrapped in an OUTER CONJ_TAC that  *)
(* peels the trailing events existential FIRST (the MS post is               *)
(* `(value_post) /\ events`, events outermost), then DISCHARGE_MEMSAFE_ASM_TAC *)
(* closes it.  NO GATHER_BOUND_TAC: the scalar tail has no vpgatherdd; the   *)
(* only memory accesses are res-stores, bounded by CONTAINED_ASM_TAC inside  *)
(* DISCHARGE from outlen0 < 256.                                             *)
(* ========================================================================= *)

let EXEC_ETA2 = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* Setup to s8 with the events existential anchored (= SCALAR_BODY_SETUP_ETA2 plus
   STRIP_EXISTS_ASSUM_TAC right after ENSURES_INIT_TAC "s0"). *)
let SCALAR_BODY_SETUP_ETA2_MS =
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  MP_TAC(ISPECL [`inlist:byte list`; `buf:int64`; `s0:x86state`; `p:num`; `136`] READ_1BYTE_EL_ETA2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `outlen0 = LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list)` THEN
  FIRST_X_ASSUM(fun th -> if concl th = `L:num = outlen0` then SUBST_ALL_TAC th else NO_TAC) THEN
  SUBGOAL_THEN `~(&(val(word_zx(word outlen0:int64):int32)):int - &256 = &(val(word_sub(word_zx(word outlen0:int64):int32) (word 256):int32)))` ASSUME_TAC THENL
   [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(&(val(word_zx(word p:int64):int32)):int - &136 = &(val(word_sub(word_zx(word p:int64):int32) (word 136):int32)))` ASSUME_TAC THENL
   [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  X86_VSTEPS_TAC EXEC_ETA2 (1--8) THEN
  SUBGOAL_THEN `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64` ASSUME_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
    MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `p < 136`) THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64`;
                              ASSUME `read (memory :> bytes8 (word_add buf (word p))) s4 = EL p (inlist:byte list)`;
                              R10_NIBBLE_VAL_ETA2]) THEN
  DISCARD_OLDSTATE_TAC "s8";;

(* Build the MS goal term: events existential conjoined onto SCALAR_TAIL_BODY_ETA2's
   pre & post (events the OUTERMOST conjunct), universally over the extra `e`. *)
let scalar_body_ms_eta2_tm =
  let qvars, body = strip_forall (concl SCALAR_TAIL_BODY_ETA2) in
  let hyps_tm, ens = dest_imp body in
  let ensc, ppf = strip_comb ens in
  let pre = el 1 ppf and post = el 2 ppf and frame = el 3 ppf in
  let sv, preb = dest_abs pre in
  let sv2, postb = dest_abs post in
  let evtempl = `exists e_acc:(uarch_event)list. read events (s:x86state) = APPEND e_acc (e:(uarch_event)list) /\ memaccess_inbounds e_acc [(buf:int64),136; (table:int64),2048] [(res:int64),1024]` in
  let pre' = mk_abs(sv, mk_conj(preb, vsubst[sv,`s:x86state`] evtempl)) in
  let post' = mk_abs(sv2, mk_conj(postb, vsubst[sv2,`s:x86state`] evtempl)) in
  let ens' = list_mk_comb(ensc,[el 0 ppf; pre'; post'; frame]) in
  list_mk_forall(qvars @ [`e:(uarch_event)list`], mk_imp(hyps_tm, ens'));;

let SCALAR_TAIL_BODY_MEMSAFE_ETA2 = prove
 (scalar_body_ms_eta2_tm,
  SCALAR_BODY_SETUP_ETA2_MS THEN
  ASM_CASES_TAC `val(EL p (inlist:byte list)) MOD 16 < 15` THENL
   [(* ============ ACCEPT-LOW (low<15): jae s10 NOT taken ============ *)
    SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32)):int - &15 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32) (word 15):int32)))` ASSUME_TAC THENL
     [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    X86_VSTEPS_TAC EXEC_ETA2 (9--19) THEN
    FIRST_X_ASSUM(fun th -> let c=concl th in
       if is_eq c && can(find_term(fun t->t=`RAX`))c && can(find_term(fun t->t=`s19:x86state`))c
       then ASSUME_TAC(REWRITE_RULE[MATCH_MP RAX_INC_ETA2 (ASSUME `outlen0<256`)] th) else NO_TAC) THEN
    SUBGOAL_THEN `outlen0 + 1 < 256` ASSUME_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o check(fun th->let c=concl th in c=`outlen0<256`||c=`val(EL p (inlist:byte list)) MOD 16 < 15`||c=`~(outlen0=255/\val(EL p (inlist:byte list)) MOD 16 < 15)`))) THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(&(val(word_zx(word(outlen0+1):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(outlen0+1):int64):int32) (word 256):int32)))` ASSUME_TAC THENL
     [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    X86_VSTEPS_TAC EXEC_ETA2 (20--21) THEN
    RELOAD_PREP_ETA2 `s21:x86state` THEN
    X86_VSTEPS_TAC EXEC_ETA2 (22--24) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[R11_NIBBLE_VAL_ETA2]) THEN DISCARD_OLDSTATE_TAC "s24" THEN
    ASM_CASES_TAC `val(EL p (inlist:byte list)) DIV 16 < 15` THENL
     [(* ===== ACCEPT-ACCEPT ===== *)
      SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &15 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 15):int32)))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `val(word(outlen0+1):int64) = outlen0+1` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0+1<256`) THEN ARITH_TAC; ALL_TAC] THEN
      X86_VSTEPS_TAC EXEC_ETA2 (25--35) THEN
      X86_VSTEPS_TAC EXEC_ETA2 (36--36) THEN DISCARD_OLDSTATE_TAC "s36" THEN
      FIRST_X_ASSUM(fun th -> let c=concl th in
         if is_eq c && can(find_term(fun t->t=`RAX`))c && can(find_term(fun t->t=`s36:x86state`))c
         then ASSUME_TAC(REWRITE_RULE[MATCH_MP RAX_INC_ETA2 (ASSUME `outlen0+1<256`)] th) else NO_TAC) THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0 + 2` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_BOTH_ETA2) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      ASM_REWRITE_TAC[ARITH_RULE `(outlen0+1)+1 = outlen0+2`] THEN
      (* MS: peel events FIRST via an outer CONJ_TAC, then the value tail    *)
      CONJ_TAC THENL
       [TRY(CONJ_TAC THENL [RCX_INC_TAC; ALL_TAC]) THEN
        SUBGOAL_THEN `REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p+1) inlist) =
           APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist))
                  [word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32;
                   word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) DIV 16)) (word 5:int16))):int32]` SUBST1_TAC THENL
         [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_BOTH_ETA2) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `4 * (outlen0 + 2) = 4 * outlen0 + 8` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s36:x86state`;
           `REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list`;
           `[word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32;
             word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) DIV 16)) (word 5:int16))):int32]`;
           `4*outlen0`; `8`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[DIMINDEX_32] THEN
          FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC) THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM(REWRITE_CONV[APPEND] `APPEND [a:int32] [b:int32]`)] THEN
          SUBGOAL_THEN `(8:num) = 4 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
          MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `word_add res (word(4*outlen0)):int64`; `s36:x86state`;
             `[word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]`;
             `[word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) DIV 16)) (word 5:int16))):int32]`;
             `4`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
          ANTS_TAC THENL [REWRITE_TAC[DIMINDEX_32; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
          SUBGOAL_THEN `val(word outlen0:int64) = outlen0` ASSUME_TAC THENL
           [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0<256`) THEN ARITH_TAC; ALL_TAC] THEN
          ETA2_STORE_SPEC_TAC `s36:x86state` `val(EL p (inlist:byte list)) MOD 16` THEN
          ETA2_STORE_SPEC_TAC `s36:x86state` `val(EL p (inlist:byte list)) DIV 16` THEN
          CONJ_TAC THENL
           [FIRST_X_ASSUM(fun th -> let c=concl th in
               if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c && not(can(find_term is_cond)c)
               then MP_TAC th else NO_TAC) THEN
            ASM_REWRITE_TAC[] THEN
            STORE4_FROM_SPEC `s36:x86state` `word_add res (word(4 * outlen0)):int64`;
            SUBGOAL_THEN `word_add (word_add res (word (4 * outlen0))) (word 4):int64 = word_add res (word (4 * (outlen0+1)))` SUBST1_TAC THENL
             [CONV_TAC WORD_RULE; ALL_TAC] THEN
            FIRST_X_ASSUM(fun th -> let c=concl th in
               if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) DIV 16`))c && not(can(find_term is_cond)c)
               then MP_TAC th else NO_TAC) THEN
            ASM_REWRITE_TAC[] THEN
            STORE4_FROM_SPEC `s36:x86state` `word_add res (word(4 * (outlen0+1))):int64`]];
        DISCHARGE_MEMSAFE_ASM_TAC];
      (* ===== LO-only (low<15, high>=15): jae s26 TAKEN -> pc+399 =====     *)
      SUBGOAL_THEN `&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &15 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 15):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE_ETA2 THEN CONJ_TAC THENL
         [MP_TAC(ASSUME `~(val(EL p (inlist:byte list)) DIV 16 < 15)`) THEN ARITH_TAC;
          MP_TAC(ISPEC `EL p (inlist:byte list)` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
          MP_TAC(SPECL[`val(EL p (inlist:byte list))`;`16`] DIV_LE) THEN ARITH_TAC]; ALL_TAC] THEN
      X86_VSTEPS_TAC EXEC_ETA2 (25--26) THEN DISCARD_OLDSTATE_TAC "s26" THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0 + 1` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_LO_ETA2) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [TRY(CONJ_TAC THENL [RCX_INC_TAC; ALL_TAC]) THEN
        SUBGOAL_THEN `REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p+1) inlist) =
           APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist))
                  [word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]` SUBST1_TAC THENL
         [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_LO_ETA2) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `4 * (outlen0 + 1) = 4 * outlen0 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s26:x86state`;
           `REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list`;
           `[word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]`;
           `4*outlen0`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[DIMINDEX_32] THEN
          FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC) THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
        CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          SUBGOAL_THEN `val(word outlen0:int64) = outlen0` ASSUME_TAC THENL
           [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0<256`) THEN ARITH_TAC; ALL_TAC] THEN
          ETA2_STORE_SPEC_TAC `s26:x86state` `val(EL p (inlist:byte list)) MOD 16` THEN
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c && not(can(find_term is_cond)c)
             then MP_TAC th else NO_TAC) THEN
          ASM_REWRITE_TAC[] THEN
          STORE4_FROM_SPEC `s26:x86state` `word_add res (word(4 * outlen0)):int64`];
        DISCHARGE_MEMSAFE_ASM_TAC]];
    (* ============ REJECT-LOW (low>=15): jae s10 TAKEN -> movzbl s11 ============ *)
    SUBGOAL_THEN `&(val(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32)):int - &15 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32) (word 15):int32))` ASSUME_TAC THENL
     [MATCH_MP_TAC JAE_TAKEN_GE_ETA2 THEN CONJ_TAC THENL
       [MP_TAC(ASSUME `~(val(EL p (inlist:byte list)) MOD 16 < 15)`) THEN ARITH_TAC;
        MP_TAC(SPECL[`val(EL p (inlist:byte list))`;`16`] MOD_LT_EQ) THEN ARITH_TAC]; ALL_TAC] THEN
    X86_VSTEPS_TAC EXEC_ETA2 (9--10) THEN
    RELOAD_PREP_ETA2 `s10:x86state` THEN
    X86_VSTEPS_TAC EXEC_ETA2 (11--13) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[R11_NIBBLE_VAL_ETA2]) THEN DISCARD_OLDSTATE_TAC "s13" THEN
    ASM_CASES_TAC `val(EL p (inlist:byte list)) DIV 16 < 15` THENL
     [(* ===== HI-only (low>=15, high<15): jae s15 NOT taken -> store ===== *)
      SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &15 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 15):int32)))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `val(word outlen0:int64) = outlen0` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0<256`) THEN ARITH_TAC; ALL_TAC] THEN
      X86_VSTEPS_TAC EXEC_ETA2 (14--23) THEN
      X86_VSTEPS_TAC EXEC_ETA2 (24--25) THEN DISCARD_OLDSTATE_TAC "s25" THEN
      FIRST_X_ASSUM(fun th -> let c=concl th in
         if is_eq c && can(find_term(fun t->t=`RAX`))c && can(find_term(fun t->t=`s25:x86state`))c
         then ASSUME_TAC(REWRITE_RULE[MATCH_MP RAX_INC_ETA2 (ASSUME `outlen0<256`)] th) else NO_TAC) THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0 + 1` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_HI_ETA2) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [TRY(CONJ_TAC THENL [RCX_INC_TAC; ALL_TAC]) THEN
        SUBGOAL_THEN `REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p+1) inlist) =
           APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist))
                  [word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) DIV 16)) (word 5:int16))):int32]` SUBST1_TAC THENL
         [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_HI_ETA2) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `4 * (outlen0 + 1) = 4 * outlen0 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s25:x86state`;
           `REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list`;
           `[word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) DIV 16)) (word 5:int16))):int32]`;
           `4*outlen0`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[DIMINDEX_32] THEN
          FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC) THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
        CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          ETA2_STORE_SPEC_TAC `s25:x86state` `val(EL p (inlist:byte list)) DIV 16` THEN
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) DIV 16`))c && not(can(find_term is_cond)c)
             then MP_TAC th else NO_TAC) THEN
          ASM_REWRITE_TAC[] THEN
          STORE4_FROM_SPEC `s25:x86state` `word_add res (word(4 * outlen0)):int64`];
        DISCHARGE_MEMSAFE_ASM_TAC];
      (* ===== NONE (low>=15, high>=15): jae s15 TAKEN -> pc+399, no store ===== *)
      SUBGOAL_THEN `&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &15 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 15):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE_ETA2 THEN CONJ_TAC THENL
         [MP_TAC(ASSUME `~(val(EL p (inlist:byte list)) DIV 16 < 15)`) THEN ARITH_TAC;
          MP_TAC(ISPEC `EL p (inlist:byte list)` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
          MP_TAC(SPECL[`val(EL p (inlist:byte list))`;`16`] DIV_LE) THEN ARITH_TAC]; ALL_TAC] THEN
      X86_VSTEPS_TAC EXEC_ETA2 (14--15) THEN DISCARD_OLDSTATE_TAC "s15" THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_NONE_ETA2) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      SUBGOAL_THEN `REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p+1) inlist):int32 list = REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist)` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_NONE_ETA2) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      (* MS: in the NONE case ASM_REWRITE_TAC closes ALL value conjuncts (nothing
         changed: outlist = old list, RCX advance is an assumption), leaving ONLY
         the events existential — so no CONJ_TAC; DISCHARGE_MEMSAFE_ASM_TAC directly.
         TRY RCX_INC_TAC guards the (observed-absent) residual-RCX shape. *)
      TRY RCX_INC_TAC THEN DISCHARGE_MEMSAFE_ASM_TAC]]);;

(* ========================================================================= *)
(* ETA2 SCALAR_TAIL_RUN_MEMSAFE:                                             *)
(* the eta2 scalar-tail byte-loop (pc+399 -> pc+542) strengthened with the   *)
(* memory-safety events conjunct in pre & post.  Strong induction on the byte *)
(* budget `d` (136 - p <= d), reusing the value SCALAR_TAIL_RUN_ETA2 proof   *)
(* except:                                                                   *)
(* 1. STRIP_EXISTS_ASSUM_TAC after each ENSURES_INIT_TAC (anchors events s0). *)
(* 2. exit leaves: DISCHARGE_MEMSAFE_ASM_TAC closes the trailing events goal. *)
(* 3. recursive leaf: SCALAR_TAIL_BODY_ETA2 -> SCALAR_TAIL_BODY_MEMSAFE_ETA2 *)
(* (+`e` arg); the IH is the MS IH, so ENSURES_SEQUENCE_TAC's intermediate   *)
(* bodyQ carries events and the legs compose with a single shared `e`.       *)
(* No GATHER_BOUND_TAC (scalar tail has no vpgatherdd; res-stores discharge via *)
(* CONTAINED_ASM_TAC).                                                       *)
(*                                                                           *)
(* Events threaded DEEP-RIGHT on the conjunction spine (conj_append_right) so *)
(* RUN's pre/post keep the canonical `bytes_loaded /\ read RIP = word.. /\ REST` *)
(* shape that ENSURES_SEQUENCE_TAC's higher-order pattern (and ENSURES_INIT_TAC *)
(* in the exit leaves) require.  buf=136.                                    *)
(* ========================================================================= *)

let EXEC_ETA2 = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* Thread the events existential DEEP-RIGHT on the conjunction spine.        *)
let rec conj_append_right t ev =
  if is_conj t then
    let l,r = dest_conj t in mk_conj(l, conj_append_right r ev)
  else mk_conj(t, ev);;
let scalar_run_ms_eta2_tm =
  let qvars, body = strip_forall (concl SCALAR_TAIL_RUN_ETA2) in
  let hyps_tm, ens = dest_imp body in
  let ensc, ppf = strip_comb ens in
  let pre = el 1 ppf and post = el 2 ppf and frame = el 3 ppf in
  let sv, preb = dest_abs pre in
  let sv2, postb = dest_abs post in
  let evtempl = `exists e_acc:(uarch_event)list. read events (s:x86state) = APPEND e_acc (e:(uarch_event)list) /\ memaccess_inbounds e_acc [(buf:int64),136; (table:int64),2048] [(res:int64),1024]` in
  let pre' = mk_abs(sv, conj_append_right preb (vsubst[sv,`s:x86state`] evtempl)) in
  let post' = mk_abs(sv2, conj_append_right postb (vsubst[sv2,`s:x86state`] evtempl)) in
  let ens' = list_mk_comb(ensc,[el 0 ppf; pre'; post'; frame]) in
  list_mk_forall(qvars @ [`e:(uarch_event)list`], mk_imp(hyps_tm, ens'));;

let SCALAR_TAIL_RUN_MEMSAFE_ETA2 = prove
 (scalar_run_ms_eta2_tm,

  INDUCT_TAC THENL
   [(* ================= BASE CASE: d = 0 => p = 136 ================= *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `p = 136` SUBST_ALL_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> let c=concl th in c=`136 - p <= 0` || c=`p <= 136`))) THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `inlist:byte list` SUB_LIST_BYTE_136) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `SUB_LIST(0,136) (inlist:byte list) = inlist`]) THEN
    REWRITE_TAC[ASSUME `SUB_LIST(0,136) (inlist:byte list) = inlist`] THEN
    ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) = 256` THENL
     [(* --- BASE COUNT-EXIT: outlen = 256 --- *)
      MP_TAC(SPEC `REJ_SAMPLE_ETA2_BYTES inlist:int32 list` SUB_LIST_256_LE) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) = 256`] THEN
      REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) = REJ_SAMPLE_ETA2_BYTES inlist`] THEN
      ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
      SUBGOAL_THEN `&(val(word_zx(word 256:int64):int32)):int - &256 = &(val(word_sub(word_zx(word 256:int64):int32) (word 256):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE_ETA2 THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
      X86_VSTEPS_TAC EXEC_ETA2 (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) = 256`] THEN
      REWRITE_TAC[LENGTH_BUTLAST_TMC_ETA2] THEN ASM_REWRITE_TAC[] THEN DISCHARGE_MEMSAFE_ASM_TAC;
      (* --- BASE OFFSET-EXIT: outlen < 256, p = 136 ---                     *)
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) < 256` ASSUME_TAC THENL
       [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> let c=concl th in c=`LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) <= 256` || c=`~(LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) = 256)`))) THEN ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `REJ_SAMPLE_ETA2_BYTES inlist:int32 list` SUB_LIST_256_LE) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) = REJ_SAMPLE_ETA2_BYTES inlist`] THEN
      ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
      SUBGOAL_THEN `~(&(val(word_zx(word(LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list)):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list)):int64):int32) (word 256):int32)))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      SUBGOAL_THEN `&(val(word_zx(word 136:int64):int32)):int - &136 = &(val(word_sub(word_zx(word 136:int64):int32) (word 136):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE_ETA2 THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
      X86_VSTEPS_TAC EXEC_ETA2 (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[LENGTH_BUTLAST_TMC_ETA2] THEN ASM_REWRITE_TAC[] THEN DISCHARGE_MEMSAFE_ASM_TAC];
    (* ================= STEP CASE: SUC d =================                  *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_CASES_TAC `256 <= LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list)` THENL
     [(* --- STEP COUNT-EXIT: outlen >= 256 (=256 by invariant) --- *)
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) = 256` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`inlist:byte list`; `p:num`] SUB_LIST_256_PREFIX_GE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      MP_TAC(SPEC `REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list` SUB_LIST_256_LE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN DISCH_TAC THEN
      SUBGOAL_THEN `SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) = REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) = REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist)`;
                  ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) = 256`] THEN
      ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
      SUBGOAL_THEN `&(val(word_zx(word 256:int64):int32)):int - &256 = &(val(word_sub(word_zx(word 256:int64):int32) (word 256):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE_ETA2 THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
      X86_VSTEPS_TAC EXEC_ETA2 (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) = 256`; LENGTH_BUTLAST_TMC_ETA2] THEN
      ASM_REWRITE_TAC[] THEN DISCHARGE_MEMSAFE_ASM_TAC;
      (* --- not count-exit: outlen < 256 ---                                *)
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) < 256` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `p = 136` THENL
       [(* --- STEP OFFSET-EXIT: p = 136 --- *)
        FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `p = 136`)) THEN
        MP_TAC(SPEC `inlist:byte list` SUB_LIST_BYTE_136) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `SUB_LIST(0,136) (inlist:byte list) = inlist`]) THEN
        REWRITE_TAC[ASSUME `SUB_LIST(0,136) (inlist:byte list) = inlist`] THEN
        MP_TAC(SPEC `REJ_SAMPLE_ETA2_BYTES inlist:int32 list` SUB_LIST_256_LE) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
        REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) = REJ_SAMPLE_ETA2_BYTES inlist`] THEN
        ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
        SUBGOAL_THEN `~(&(val(word_zx(word(LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list)):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA2_BYTES inlist:int32 list)):int64):int32) (word 256):int32)))` ASSUME_TAC THENL
         [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
        SUBGOAL_THEN `&(val(word_zx(word 136:int64):int32)):int - &136 = &(val(word_sub(word_zx(word 136:int64):int32) (word 136):int32))` ASSUME_TAC THENL
         [MATCH_MP_TAC JAE_TAKEN_GE_ETA2 THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
        X86_VSTEPS_TAC EXEC_ETA2 (1--4) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        REWRITE_TAC[LENGTH_BUTLAST_TMC_ETA2] THEN ASM_REWRITE_TAC[] THEN DISCHARGE_MEMSAFE_ASM_TAC;
        (* --- p < 136 ---                                                   *)
        SUBGOAL_THEN `p < 136` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) = 255 /\ val(EL p (inlist:byte list)) MOD 16 < 15` THENL
         [(* --- STEP MID-BYTE EXIT: outlen=255, low<15 (accept low pushes to 256) --- *)
          FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th -> is_conj(concl th) && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))(concl th))) THEN
          SUBGOAL_THEN `256 <= LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+1) inlist):int32 list)` ASSUME_TAC THENL
           [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_ETA2_BYTES_STEP_1) THEN
            ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `?rest. REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+1) inlist):int32 list =
             APPEND (APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist))
                            [word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]) rest`
           STRIP_ASSUME_TAC THENL
           [ASM_CASES_TAC `val(EL p (inlist:byte list)) DIV 16 < 15` THENL
             [EXISTS_TAC `[word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) DIV 16)) (word 5:int16))):int32]` THEN
              MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_BOTH_ETA2) THEN
              ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
              DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[APPEND; GSYM APPEND_ASSOC];
              EXISTS_TAC `[]:int32 list` THEN
              MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_LO_ETA2) THEN
              ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
              DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[APPEND_NIL]]; ALL_TAC] THEN
          MP_TAC(SPECL [`inlist:byte list`; `p+1`] SUB_LIST_256_PREFIX_GE) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
          SUBGOAL_THEN `LENGTH(APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist))
                            [word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]:int32 list) = 256` ASSUME_TAC THENL
           [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) =
               APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist))
                      [word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]` ASSUME_TAC THENL
           [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && (try lhs(concl th) = `SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist:int32 list)` with _->false) then SUBST1_TAC th else NO_TAC) THEN
            FIRST_X_ASSUM(fun th -> if is_eq(concl th) && (try lhs(concl th) = `REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+1) inlist):int32 list` with _->false) then SUBST1_TAC th else NO_TAC) THEN
            W(fun (asl,gl) -> let lt = rhs gl in
               MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (mk_comb(`SUB_LIST(0,256):(int32)list->(int32)list`, lt)) THEN
               CONJ_TAC THENL
                [MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN ASM_REWRITE_TAC[LE_REFL];
                 MATCH_MP_TAC SUB_LIST_256_LE THEN ASM_REWRITE_TAC[LE_REFL]]); ALL_TAC] THEN
          REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) =
                APPEND (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist))
                [word_sx (word_sub (word 2:int16) (word_umod (word (val (EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]`] THEN
          REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) = 255`] THEN
          ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
          MP_TAC(ISPECL [`inlist:byte list`; `buf:int64`; `s0:x86state`; `p:num`; `136`] READ_1BYTE_EL_ETA2) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
          SUBGOAL_THEN `~(&(val(word_zx(word 255:int64):int32)):int - &256 = &(val(word_sub(word_zx(word 255:int64):int32) (word 256):int32)))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
          SUBGOAL_THEN `~(&(val(word_zx(word p:int64):int32)):int - &136 = &(val(word_sub(word_zx(word p:int64):int32) (word 136):int32)))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
          X86_VSTEPS_TAC EXEC_ETA2 (1--8) THEN
          SUBGOAL_THEN `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64` ASSUME_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
            MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `p < 136`) THEN ARITH_TAC; ALL_TAC] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64`;
                                      ASSUME `read (memory :> bytes8 (word_add buf (word p))) s4 = EL p (inlist:byte list)`;
                                      R10_NIBBLE_VAL_ETA2]) THEN
          DISCARD_OLDSTATE_TAC "s8" THEN
          SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32)):int - &15 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32) (word 15):int32)))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_NOT_TAKEN_LT_ETA2 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `val(word 255:int64) = 255` ASSUME_TAC THENL
           [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC; ALL_TAC] THEN
          X86_VSTEPS_TAC EXEC_ETA2 (9--19) THEN
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->t=`RAX`))c && can(find_term(fun t->t=`s19:x86state`))c
             then ASSUME_TAC(REWRITE_RULE[MATCH_MP RAX_INC_ETA2 (ARITH_RULE `255<256`)] th) else NO_TAC) THEN
          SUBGOAL_THEN `&(val(word_zx(word(255+1):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(255+1):int64):int32) (word 256):int32))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_TAKEN_GE_ETA2 THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
          X86_VSTEPS_TAC EXEC_ETA2 (20--21) THEN
          ENSURES_FINAL_STATE_TAC THEN
          REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA2_BYTES inlist:int32 list) =
                APPEND (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,p) inlist))
                [word_sx (word_sub (word 2:int16) (word_umod (word (val (EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]`] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
          REWRITE_TAC[ASSUME `LENGTH(APPEND (REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist))
                [word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]:int32 list) = 256`] THEN
          REWRITE_TAC[LENGTH_BUTLAST_TMC_ETA2] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
          [REPEAT CONJ_TAC THEN
          (* memory fold: bytes(res,4*256) = APPEND prefix [lo]              *)
          SUBGOAL_THEN `4 * 256 = 4 * 255 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
          MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s21:x86state`;
             `REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list`;
             `[word_sx(word_sub (word 2:int16) (word_umod (word(val(EL p (inlist:byte list)) MOD 16)) (word 5:int16))):int32]`;
             `4*255`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
          ANTS_TAC THENL [REWRITE_TAC[DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
          CONJ_TAC THENL
           [ASM_REWRITE_TAC[];
            SUBGOAL_THEN `word(4 * 255):int64 = word 1020` SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
            ETA2_STORE_SPEC_TAC `s21:x86state` `val(EL p (inlist:byte list)) MOD 16` THEN
            FIRST_X_ASSUM(fun th -> let c=concl th in
               if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c && not(can(find_term is_cond)c)
               then MP_TAC th else NO_TAC) THEN
            ASM_REWRITE_TAC[] THEN
            STORE4_FROM_SPEC `s21:x86state` `word_add res (word 1020):int64`];
           DISCHARGE_MEMSAFE_ASM_TAC];
          (* --- STEP CLEAN-RECURSIVE: body trip then IH at p+1 ---          *)
          SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p+1) inlist):int32 list) <= 256` ASSUME_TAC THENL
           [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_ETA2_BYTES_STEP_1) THEN ASM_REWRITE_TAC[] THEN
            DISCH_THEN SUBST1_TAC THEN
            REPEAT(FIRST_X_ASSUM(MP_TAC o check(fun th -> let c=concl th in
               c = `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) < 256` ||
               c = `~(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list) = 255 /\ val(EL p (inlist:byte list)) MOD 16 < 15)`))) THEN
            REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ARITH_TAC; ALL_TAC] THEN
          (* body lemma instance at (p, outlen(p))                           *)
          MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`p:num`;
             `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p) inlist):int32 list)`;`stackpointer:int64`;`e:(uarch_event)list`] SCALAR_TAIL_BODY_MEMSAFE_ETA2) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(fun body_th ->
            let bodyQ = rand(rator(concl body_th)) in
            ENSURES_SEQUENCE_TAC `pc + 399` bodyQ THEN
            CONJ_TAC THENL
             [(* leg1: P -> bodyQ via the body lemma (precond/postcond weaken) *)
              MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
              EXISTS_TAC (rand(rator(concl body_th))) THEN CONJ_TAC THENL
               [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]);
                MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
                EXISTS_TAC (rand(rator(rator(concl body_th)))) THEN CONJ_TAC THENL
                 [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]);
                  ACCEPT_TAC body_th]];
              (* leg2: bodyQ -> R = IH at p+1                                *)
              ALL_TAC]) THEN
          (* leg2: weaken pre to IH's expanded pre, then apply IH@(p+1)      *)
          FIRST_X_ASSUM(fun ih -> if is_forall(concl ih) then
            (let ih_inst = SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`p+1`;`stackpointer:int64`;`e:(uarch_event)list`] ih in
             let ih_pre = rand(rator(rator(snd(dest_imp(concl ih_inst))))) in
             MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC ih_pre THEN CONJ_TAC THENL
              [GEN_TAC THEN BETA_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]);
               MP_TAC ih_inst THEN ANTS_TAC THENL
                [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]])
            else NO_TAC)]]]]);;

(* ========================================================================= *)
(* MLDSA_REJ_UNIFORM_ETA2_SCALAR_TAIL_AT_P_MEMSAFE:                          *)
(* the scalar-tail MEMSAFE contract at an arbitrary exit position p, a trivial *)
(* corollary of SCALAR_TAIL_RUN_MEMSAFE_ETA2 with budget d := 136 - p (so    *)
(* 136-p<=d holds by LE_REFL). Events threaded deep-right (matching RUN); the *)
(* extra `e` arg is passed through and ASM_REWRITE closes the matching conjunct. *)
(* This is the form the core consumes (via SCALAR_TAIL_LEG2_MS).             *)
(* ========================================================================= *)
let scalar_at_p_ms_eta2_tm =
  let qvars, body = strip_forall (concl MLDSA_REJ_UNIFORM_ETA2_SCALAR_TAIL_AT_P) in
  let hyps_tm, ens = dest_imp body in
  let ensc, ppf = strip_comb ens in
  let pre = el 1 ppf and post = el 2 ppf and frame = el 3 ppf in
  let sv, preb = dest_abs pre in
  let sv2, postb = dest_abs post in
  let evtempl = `exists e_acc:(uarch_event)list. read events (s:x86state) = APPEND e_acc (e:(uarch_event)list) /\ memaccess_inbounds e_acc [(buf:int64),136; (table:int64),2048] [(res:int64),1024]` in
  let pre' = mk_abs(sv, conj_append_right preb (vsubst[sv,`s:x86state`] evtempl)) in
  let post' = mk_abs(sv2, conj_append_right postb (vsubst[sv2,`s:x86state`] evtempl)) in
  let ens' = list_mk_comb(ensc,[el 0 ppf; pre'; post'; frame]) in
  list_mk_forall(qvars @ [`e:(uarch_event)list`], mk_imp(hyps_tm, ens'));;

let MLDSA_REJ_UNIFORM_ETA2_SCALAR_TAIL_AT_P_MEMSAFE = prove
 (scalar_at_p_ms_eta2_tm,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`136 - p`; `res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`p:num`;`stackpointer:int64`;`e:(uarch_event)list`] SCALAR_TAIL_RUN_MEMSAFE_ETA2) THEN
  ASM_REWRITE_TAC[LE_REFL]);;

(* ========================================================================= *)
(* ETA2 MID-EXIT MEMSAFE lemmas: the four mid-guard "taken" exit cases       *)
(* of the eta2 SIMD loop body, each strengthened with the memory-safety events *)
(* conjunct                                                                  *)
(* exists e_acc. read events s = APPEND e_acc e /\                           *)
(* memaccess_inbounds e_acc [buf,136;table,2048] [res,1024]                  *)
(* in BOTH pre and post.  These are the MEMSAFE lifts of MID_EXIT_SUBITER1/2/3 *)
(* and MID_EXIT_CASE4.                                                       *)
(*                                                                           *)
(* As in CLEAN_BODY_MEMSAFE, three changes vs the value tactics:             *)
(* 1. ETA2_MIDEXIT_PREFIX_MS_TAC: STRIP_EXISTS_ASSUM_TAC right after         *)
(* ENSURES_INIT_TAC "s0", anchoring the events precond so each step's        *)
(* CONS-events fact flattens and survives DISCARD_OLDSTATE/PURGE_STALE.      *)
(* 2. The mid-guard RIP-resolution heuristics that use find_term(pc+K) become *)
(* events-aware: with events anchored, the per-step                          *)
(* `read events sN = CONS(EventJump(word(pc+K)),..)` fact ALSO matches       *)
(* find_term(pc+K), so REFL_TAC fails.  FIX = match the RIP assumption       *)
(* STRUCTURALLY (`read RIP sN = COND(..)`), exactly as SI2/SI3 counters and  *)
(* CLEAN_BODY's ETA2_SI1_COUNTER_MS_TAC already do.  Sites (value -> MS):    *)
(* - SUBITER1 s26/pc+399 -> COND match                                       *)
(* - MG1_NT s26/pc+207 -> COND match                                         *)
(* - SI2_MG2_TAKEN s41/pc+399 -> COND match                                  *)
(* - MG2_NT s41/pc+273 -> COND match                                         *)
(* - SI3_MG3_TAKEN s56/pc+399 -> ALREADY COND                                *)
(* - MG3_NT s56/pc+339 -> COND match                                         *)
(* - CASE4 s71/pc+399 -> COND match                                          *)
(* 3. After the value closers, DISCHARGE_MEMSAFE_ASM_TAC discharges the events *)
(* existential; GATHER_BOUND_TAC closes the 4 vpgatherdd table-gather        *)
(* contained_modulo disjuncts (idx<256 => table+8*idx in [table,2048]).      *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The MS prefix: ETA2_MIDEXIT_OPEN_TAC + STRIP_EXISTS after                 *)
(* ENSURES_INIT, then the s5-s11 SIMD chain + SI1 store fold (all events-robust, *)
(* reused from the ETA2_MIDEXIT_*_TAC bodies).                               *)
(* ------------------------------------------------------------------------- *)
let ETA2_MIDEXIT_OPEN_MS_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `16 * i <= 120` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i + 1) <= 136` THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  STRIP_EXISTS_ASSUM_TAC THEN
  MP_TAC(SPECL [`buf:int64`;`136`;`inlist:byte list`;`i:num`;`s0:x86state`] SUB_LIST_16_BYTES_FROM_INT128) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `16 * (i + 1) <= 136` THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `chunk0 = read(memory:>bytes128(word_add buf (word(16*i)))) s0` THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) <= 248` ASSUME_TAC THENL
   [FIRST [FIRST_ASSUM ACCEPT_TAC;
           (FIRST_X_ASSUM(fun th -> match concl th with
              Comb(Comb(Const("<=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA2_BYTES",_),_))),k) when k=`248`
                -> MP_TAC th | _ -> NO_TAC) THEN
            MATCH_MP_TAC(ARITH_RULE `a <= b ==> b <= 248 ==> a <= 248`) THEN
            MATCH_MP_TAC REJ_SAMPLE_ETA2_PREFIX_MONO THEN ARITH_TAC)]; ALL_TAC] THEN
  ABBREV_TAC `outlen0 = LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list)` THEN
  FIRST_ASSUM(fun th -> if concl th =
      `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) = outlen0`
    then (RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) else NO_TAC) THEN
  MP_TAC(SPECL [`outlen0:num`;`248`] JA_NOT_TAKEN_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`16*i`;`120`] JA_NOT_TAKEN_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  VAL_INT64_TAC `outlen0:num` THEN
  X86_STEPS_TAC EXEC (1--2) THEN
  SUBGOAL_THEN `read RIP s2 = word(pc + 97):int64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can(find_term((=)`&248:int`))(concl th)
                           then ASSUME_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if can(find_term((=)`pc + 399`))(concl th) &&
                              (match concl th with
                                 Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s2",_))),_) -> true
                               | _ -> false)
                            then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC; ALL_TAC] THEN
  X86_STEPS_TAC EXEC (3--4) THEN
  SUBGOAL_THEN `read RIP s4 = word(pc + 106):int64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can(find_term((=)`&120:int`))(concl th)
                           then ASSUME_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if can(find_term((=)`pc + 399`))(concl th) &&
                              (match concl th with
                                 Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s4",_))),_) -> true
                               | _ -> false)
                            then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC; ALL_TAC];;

(* s5-s8 + s9 maskbits + s10-s11 gather + SI1 fold: events-robust, reused from
   the ETA2_MIDEXIT_PREFIX_TAC tail. *)
let ETA2_MIDEXIT_PREFIX_MS_TAC : tactic =
  ETA2_MIDEXIT_OPEN_MS_TAC THEN
  (* ETA2_MIDEXIT_S5_S8_TAC body                                             *)
  X86_VSTEPS_TAC EXEC (5--5) THEN
  SUBGOAL_THEN `val(word(16*i):int64) = 16*i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `16*i <= 120` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word(16*i):int64) = 16*i`; ARITH_RULE `1 * x = x`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read (memory :> bytes128 (word_add buf (word (16 * i)))) s4 = chunk0`]) THEN
  SUBGOAL_THEN `read YMM0 s5 = usimd16 (\b:byte. word_zx b:int16) chunk0:int256` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can(find_term((=)`read YMM0 s5`))(lhand(concl th)) then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DROP_WORDJOIN_TAC THEN PURGE_STALE_STATES_TAC ["s4"] THEN
  X86_VSTEPS_TAC EXEC (6--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s5 = usimd16 (\b:byte. word_zx b:int16) chunk0:int256`]) THEN
  X86_VSTEPS_TAC EXEC (7--7) THEN X86_VSTEPS_TAC EXEC (8--8) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM3 s5 =
    word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256`]) THEN
  SUBGOAL_THEN (mk_eq(`read YMM0 s8:int256`, F0NIB_CHUNK0)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can(find_term((=)`read YMM0 s8`))(lhand(concl th)) then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DROP_WORDJOIN_TAC THEN PURGE_STALE_STATES_TAC ["s5";"s6";"s7"] THEN
  (* s9 + 4 maskbit foralls                                                  *)
  X86_VSTEPS_TAC EXEC (9--9) THEN
  ABBREV_TAC `f1bnd:int256 = read YMM1 s9` THEN
  ETA2_MASKBIT_ASSUME_TAC 0 THEN
  ETA2_MASKBIT_ASSUME_TAC 8 THEN
  ETA2_MASKBIT_ASSUME_TAC 16 THEN
  ETA2_MASKBIT_ASSUME_TAC 24 THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
     if is_eq(concl th) && lhand(concl th) = `f1bnd:int256`
     then ALL_TAC else failwith "keep")) THEN
  X86_VSTEPS_TAC EXEC (10--10) THEN
  X86_VSTEPS_TAC EXEC (11--11) THEN
  ABBREV_TAC `f0sub:int256 = read YMM0 s11` THEN
  eta2_gather_block g1_eta2 (eta2_ellist 0)  false THEN
  eta2_gather_block g2_eta2 (eta2_ellist 32) true THEN
  eta2_gather_block g3_eta2 (eta2_ellist 64) false THEN
  eta2_gather_block g4_eta2 (eta2_ellist 96) true THEN
  ETA2_SI1_FOLD;;

(* ------------------------------------------------------------------------- *)
(* Goal-term builder: conjoin the events existential OUTERMOST onto the value *)
(* midexit*_eta2_tm pre & post, universally over the extra `e` (buf=136).    *)
(* Same shape as the CLEAN_BODY_MEMSAFE builder.                             *)
(* ------------------------------------------------------------------------- *)
let midexit_ms_eta2_tm value_tm =
  let qvars, body = strip_forall value_tm in
  let hyps_tm, ens = dest_imp body in
  let ensc, ppf = strip_comb ens in
  let pre = el 1 ppf and post = el 2 ppf and frame = el 3 ppf in
  let sv, preb = dest_abs pre in
  let sv2, postb = dest_abs post in
  let evtempl = `exists e_acc:(uarch_event)list. read events (s:x86state) = APPEND e_acc (e:(uarch_event)list) /\ memaccess_inbounds e_acc [(buf:int64),136; (table:int64),2048] [(res:int64),1024]` in
  let pre' = mk_abs(sv, mk_conj(preb, vsubst[sv,`s:x86state`] evtempl)) in
  let post' = mk_abs(sv2, mk_conj(postb, vsubst[sv2,`s:x86state`] evtempl)) in
  let ens' = list_mk_comb(ensc,[el 0 ppf; pre'; post'; frame]) in
  list_mk_forall(qvars @ [`e:(uarch_event)list`], mk_imp(hyps_tm, ens'));;

let midexit1_ms_eta2_tm = midexit_ms_eta2_tm midexit1_eta2_tm;;
let midexit2_ms_eta2_tm = midexit_ms_eta2_tm midexit2_eta2_tm;;
let midexit3_ms_eta2_tm = midexit_ms_eta2_tm midexit3_eta2_tm;;
let midexit4_ms_eta2_tm = midexit_ms_eta2_tm midexit4_eta2_tm;;

(* ========================================================================= *)
(* MID_EXIT_SUBITER1_MEMSAFE: the MID_EXIT_SUBITER1_ETA2 body, with          *)
(* the MS prefix, the s26 RIP resolution switched to a structural COND match *)
(* (the anchored events fact at s26 also mentions pc+399), and the final     *)
(* DISCHARGE_MEMSAFE_ASM_TAC THEN GATHER_BOUND_TAC.                          *)
(* ========================================================================= *)
let MID_EXIT_SUBITER1_MEMSAFE_ETA2 = prove(midexit1_ms_eta2_tm,
  ETA2_MIDEXIT_PREFIX_MS_TAC THEN
  (* count facts                                                             *)
  SUBGOAL_THEN `16 * i + 4 <= LENGTH(inlist:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i+1) <= 136` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=136` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) <= 256` ASSUME_TAC THENL
   [MATCH_MP_TAC OUTLEN0_LE_256_FROM_SUBITER_ETA2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) <= 256` THEN ARITH_TAC; ALL_TAC] THEN
  X86_STEPS_TAC EXEC (21--24) THEN
  MP_TAC(ISPECL[`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `LENGTH(inlist:byte list) = 136` THEN
    UNDISCH_TAC `16 * i <= 120` THEN ARITH_TAC; STRIP_TAC] THEN
  W(fun (asl,w) ->
     let m8def = find (fun th -> match concl th with Comb(Comb(Const("=",_),_),Var("mask8",_)) -> true | _ -> false) (map snd asl) in
     RULE_ASSUM_TAC(fun th -> if concl th = maskbit_tgt ||
        can(find_term(fun u->match u with Const("TABLE_ENTRY",_)->true|_->false))(concl th)
        then th else REWRITE_RULE[GSYM m8def] th)) THEN
  W(fun (asl,w) ->
    let r9 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("R9",_)),Var("s24",_))),_) -> true | _ -> false) asl in
    let goal_pc = find_term (fun t -> match t with Comb(Const("word_popcount",_),_) -> true | _ -> false) (concl(snd r9)) in
    let low8 = `bitval(bit 7 (word_subword (f1bnd:int256) (0,8):byte)) + bitval(bit 7 (word_subword f1bnd (8,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (16,8):byte)) + bitval(bit 7 (word_subword f1bnd (24,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (32,8):byte)) + bitval(bit 7 (word_subword f1bnd (40,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (48,8):byte)) + bitval(bit 7 (word_subword f1bnd (56,8):byte))` in
    let mr = CONV_RULE(DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV)
               (SPEC `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` MOD_RED) in
    let popeq = prove(mk_eq(goal_pc, low8),
      REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; MOD_MOD_EXP_MIN] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; mr] THEN
      MAP_EVERY (fun b -> BOOL_CASES_TAC b)
        [`bit 7 (word_subword (f1bnd:int256) (0,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (8,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (16,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (24,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (32,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (40,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (48,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (56,8):byte)`] THEN
      REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV) in
    let maskbit = snd(find (fun (_,th) -> let c=concl th in is_forall c &&
        can(find_term(fun u->u=`f1bnd:int256`))c && can(find_term(fun u->match u with Comb(Const("bit",_),_)->true|_->false))c &&
        not(can(find_term(fun u->match u with Const("word_zx",_)->true|_->false))c) &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (24,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (32,8):byte`))c)) asl) in
    let mb_tm = concl maskbit in
    let blk0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
           (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
    let blkeq = mk_eq(low8, `LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i,4) inlist):int16 list)`) in
    let blk0_tm = concl(snd blk0) in
    let bsum_raw = prove(mk_imp(mb_tm, mk_imp(blk0_tm, blkeq)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN DISCH_THEN(fun b -> REWRITE_TAC[b]) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER_ETA2] THEN
      ASM_SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let bsum = MP (MP bsum_raw maskbit) (snd blk0) in
    let pop_len = TRANS popeq bsum in
    ASSUME_TAC pop_len) THEN
  (* bridge: outlen0 + niblen(SUB(16i,4)) = niblen_sample(16i+4)             *)
  SUBGOAL_THEN `outlen0 + LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i`] SUBITER_BRIDGE_ETA2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN
    UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i) inlist):int32 list) = outlen0` THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `outlen0 + LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i,4) inlist):int16 list) < 2 EXP 32` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),_)->true|_->false) then SUBST1_TAC th else NO_TAC) THEN
    UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) < 2 EXP 32` THEN REWRITE_TAC[]; ALL_TAC] THEN
  W(fun (asl,w) ->
    let block0len = `LENGTH(REJ_NIBBLES_ETA2 (SUB_LIST(16*i,4) inlist):int16 list)` in
    let sum = mk_binop `(+):num->num->num` `outlen0:num` block0len in
    let lt32 = snd(find (fun (_,th) -> concl th = mk_binop `(<):num->num->bool` sum `2 EXP 32`) asl) in
    let pop_len = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl) in
    let bridge = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),_) -> true | _ -> false) asl) in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let gt248 = REWRITE_RULE[SYM bridge] (snd(find (fun (_,th) -> concl th = `248 < LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list)`) asl)) in
    let ja_taken = MP (ISPECL [sum; `248`] JA_TAKEN_GT) (CONJ gt248 lt32) in
    ASSUME_TAC pop_len THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja_taken) THEN
  X86_STEPS_TAC EXEC (25--26) THEN
  (* MS FIX: resolve RIP s26 = pc+399 via the structural COND match (the anchored
     events fact `read events s26 = CONS(EventJump(pc+399)..)` also mentions pc+399). *)
  SUBGOAL_THEN `read RIP s26 = word (pc + 399):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let blk0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
             (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
      let rax_red0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
      let ja = find (fun (_,th) -> is_neg(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`248`))(concl th)) asl in
      let ifrip = find (fun (_,th) -> match concl th with
         Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s26",_))),r) ->
           (match r with Comb(Comb(Comb(Const("COND",_),_),_),_) -> true | _ -> false) | _ -> false) asl in
      MP_TAC (snd ifrip) THEN
      REWRITE_TAC[GSYM(snd blk0)] THEN REWRITE_TAC[snd rax_red0] THEN
      REWRITE_TAC[snd ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* discharge RAX collapse (bridge->niblen), RCX collapse                   *)
  W(fun (asl,w) ->
    let blk0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
           (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
    let rax_red0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
    let bridge = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),_) -> true | _ -> false) asl in
    REWRITE_TAC[GSYM(snd blk0); snd rax_red0; snd bridge]) THEN
  W(fun (asl,w) ->
    let ntake = MP (ISPECL [`LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list)`;`248`] JA_TAKEN_GT)
                   (CONJ (ASSUME `248 < LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list)`)
                         (ASSUME `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) < 2 EXP 32`)) in
    REWRITE_TAC[ntake]) THEN
  SUBGOAL_THEN `val(word(16*i):int64) = 16*i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `16*i<=120` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `16*i` RCX4_COLLAPSE) THEN
  ANTS_TAC THENL [UNDISCH_TAC `16*i<=120` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  DISCHARGE_MEMSAFE_ASM_TAC THEN GATHER_BOUND_TAC);;

(* ========================================================================= *)
(* MS variants of the internal mid-guard RIP-resolution tactics.  Each is a  *)
(* copy of the value tactic with the s26/s41/s56 RIP                         *)
(* resolution switched from FIRST_ASSUM(find_term(pc+K)) to a STRUCTURAL COND *)
(* match (the anchored events fact `read events sN = CONS(EventJump(pc+K)..)` *)
(* also mentions pc+K, so the value find_term heuristic would grab it and    *)
(* REFL_TAC would fail).  Everything else (pop_len/bridge/RAX-fold) is unchanged. *)
(* ========================================================================= *)

(* ETA2_MG1_NT_MS_TAC = ETA2_MG1_NT_TAC with s26 RIP -> COND match.          *)
let ETA2_MG1_NT_MS_TAC : tactic = mk_eta2_mg1_nt true;;

(* ETA2_SI2_MG2_TAKEN_MS_TAC = ETA2_SI2_MG2_TAKEN_TAC with s41 RIP -> COND.  *)
let ETA2_SI2_MG2_TAKEN_MS_TAC : tactic = mk_eta2_si2_mg2_taken true;;

let MID_EXIT_SUBITER2_MEMSAFE_ETA2 = prove(midexit2_ms_eta2_tm, mk_midexit2_eta2 true ETA2_MIDEXIT_PREFIX_MS_TAC (DISCHARGE_MEMSAFE_ASM_TAC THEN GATHER_BOUND_TAC));;

(* ETA2_MG2_NT_MS_TAC = ETA2_MG2_NT_TAC with s41 RIP -> COND match.          *)
let ETA2_MG2_NT_MS_TAC : tactic = mk_eta2_mg2_nt true;;

let MID_EXIT_SUBITER3_MEMSAFE_ETA2 = prove(midexit3_ms_eta2_tm, mk_midexit3_eta2 true ETA2_MIDEXIT_PREFIX_MS_TAC (DISCHARGE_MEMSAFE_ASM_TAC THEN GATHER_BOUND_TAC));;

(* ETA2_MG3_NT_MS_TAC = ETA2_MG3_NT_TAC with s56 RIP -> COND match.          *)
let ETA2_MG3_NT_MS_TAC : tactic = mk_eta2_mg3_nt true;;

let MID_EXIT_CASE4_MEMSAFE_ETA2 = prove(midexit4_ms_eta2_tm, mk_midexit4_eta2 true ETA2_MIDEXIT_PREFIX_MS_TAC (DISCHARGE_MEMSAFE_ASM_TAC THEN GATHER_BOUND_TAC));;

(* ETA2_CLEAN_BLOCK_MEMSAFE (relaxed-hyps SIMD block body, events-strengthened) *)
(* is proved earlier by full simulation, alongside CLEAN_BODY_MEMSAFE which now *)
(* derives from it by weakening.  See the CLEAN_BLOCK_MEMSAFE builder above.   *)

(* ========================================================================= *)
(* The core MLDSA_REJ_UNIFORM_ETA2_MEMSAFE.                                  *)
(* Follows the value CORRECT_SCAFFOLD_TAC / EXIT_OFFSET_ETA2 / OFFSET_ARM_TAC / *)
(* MIDEXIT_ARM_TAC, with the memory-safety events conjunct threaded through the *)
(* loop invariant (DEEP-RIGHT, so ENSURES_WHILE_UP_TAC's canonical-spine HO  *)
(* match works) and the per-block / exit lemmas swapped for their _MEMSAFE   *)
(* counterparts.  Key facts:                                                 *)
(* - buf=136; loop top pc+86; done pc+542; scalar entry pc+399.              *)
(* - WOP pred uses 120 (SIMD head guard cmp ecx,0x78) => OFFSET arm forces   *)
(* 16N=128 (N=8).                                                            *)
(* - init prologue is 17 insns with two vpbroadcastw COLLAPSE_VPBW dances.   *)
(* - FRAME: CORRECT/EXIT_OFFSET/core frame = ZMM0..9, but the MS building    *)
(* blocks are narrower (CLEAN_BODY/BLOCK/MID_EXIT [ZMM0;1;2;8;9],            *)
(* SCALAR_TAIL_AT_P [ZMM0..6]).  MS_BRIDGE_FROM's SUBSUMED_MAYCHANGE_TAC     *)
(* narrows automatically; the AT_P leg2s add an explicit                     *)
(* ENSURES_FRAME_SUBSUMED.                                                   *)
(*                                                                           *)
(* The MEMSAFE core composes the body + exit lemmas via ENSURES_WHILE_UP.    *)
(* ========================================================================= *)

(* Thread the events existential DEEP-RIGHT on the conjunction spine.        *)
let rec conj_append_right t ev =
  if is_conj t then let l,r = dest_conj t in mk_conj(l, conj_append_right r ev)
  else mk_conj(t, ev);;

let ev_existential_eta2 =
  `exists e_acc:(uarch_event)list.
      read events (s:x86state) = APPEND e_acc (e:(uarch_event)list) /\
      memaccess_inbounds e_acc [(buf:int64),136; (table:int64),2048] [(res:int64),1024]`;;

(* MEMSAFE_LOOPINV_ETA2 = CORRECT_LOOPINV_ETA2 + events deep-right.          *)
let MEMSAFE_LOOPINV_ETA2 =
  let iv,rest = dest_abs CORRECT_LOOPINV_ETA2 in
  let sv,body = dest_abs rest in
  mk_abs(iv, mk_abs(sv, conj_append_right body (vsubst[sv,`s:x86state`] ev_existential_eta2)));;

(* SUB_LIST-prefix length bound, used to rule out N=1.
   (Re-proved here from the base definitions.) *)
let LENGTH_REJ_SAMPLE_ETA2_BYTES_SUB_LIST_BOUND = prove
 (`!(inlist:byte list) k.
     k <= LENGTH inlist
     ==> LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,k) inlist):int32 list) <= 2 * k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `SUB_LIST(0, k) (inlist:byte list):byte list`
              LENGTH_REJ_SAMPLE_ETA2_BYTES_BOUND) THEN
  ASM_SIMP_TAC[LENGTH_SUB_LIST_0]);;

(* ------------------------------------------------------------------------- *)
(* G2_BODY_BRIDGE_TAC: bridge a loop-body goal (events deep-right, wide ZMM  *)
(* frame ZMM0..9) to MLDSA_REJ_UNIFORM_ETA2_CLEAN_BODY_MEMSAFE@i (events     *)
(* outermost, narrow frame [ZMM0;1;2;8;9]).                                  *)
(* ------------------------------------------------------------------------- *)
let G2_BODY_BRIDGE_ETA2_TAC : tactic =
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`N:num`;`i:num`;`stackpointer:int64`;`e:(uarch_event)list`] MLDSA_REJ_UNIFORM_ETA2_CLEAN_BODY_MEMSAFE) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `i + 1 < N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i+1` o check(is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THEN (FIRST [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]); ALL_TAC] THEN
  DISCH_THEN(fun bth ->
    W(fun (asl,gl) ->
      let lframe = rand(concl bth) in
      let lpost  = rand(rator(concl bth)) in
      let lpre   = rand(rator(rator(concl bth))) in
      let gframe = rand gl in
      let subsumed_tm = mk_binop `(subsumed):(x86state->x86state->bool)->(x86state->x86state->bool)->bool` lframe gframe in
      let subsumed_th = prove(subsumed_tm,
        REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN SUBSUMED_MAYCHANGE_TAC) in
      let bth' = MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ subsumed_th bth) in
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC lpre THEN
      CONJ_TAC THENL
       [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]);
        MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC lpost THEN
        CONJ_TAC THENL
         [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]);
          ACCEPT_TAC bth']]));;

(* ------------------------------------------------------------------------- *)
(* MEMSAFE_SCAFFOLD_ETA2_TAC: the value CORRECT_SCAFFOLD_TAC                 *)
(* with the MEMSAFE loop invariant + events-init on G1, and G2 swapped for the *)
(* events bridge.  After it, ONE goal remains — the exit-block obligation    *)
(* (pc+86/pos16(N-1) -> pc+542, MEMSAFE post).                               *)
(* ------------------------------------------------------------------------- *)
let MEMSAFE_SCAFFOLD_ETA2_TAC : tactic =
  MAP_EVERY X_GEN_TAC [`res:int64`; `buf:int64`; `table:int64`; `inlist:byte list`; `e:(uarch_event)list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES; LENGTH_MLDSA_REJ_UNIFORM_ETA2_TMC] THEN
  STRIP_TAC THEN GHOST_INTRO_TAC `stackpointer:int64` `read RSP` THEN
  (* Phase 1: WOP on the eta2 exit predicate (120 not 256).                  *)
  SUBGOAL_THEN `?i. 120 < 16 * i \/ 248 < LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(0, 16 * i) inlist):int16 list)` MP_TAC THENL
   [EXISTS_TAC `8:num` THEN ARITH_TAC; GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LT] th)) THEN
  SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES] THEN
    REWRITE_TAC[REJ_NIBBLES_ETA2_EMPTY; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  (* N=1 impossible: niblen(16)<=32<248 and 120<16 false                     *)
  ASM_CASES_TAC `N = 1` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = 1`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    REWRITE_TAC[ARITH_RULE `~(120 < 16 * 1)`] THEN
    MP_TAC(ISPECL [`inlist:byte list`; `16`] LENGTH_REJ_SAMPLE_ETA2_BYTES_SUB_LIST_BOUND) THEN
    ASM_REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN
    REWRITE_TAC[ARITH_RULE `16 * 1 = 16`] THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_WHILE_UP_TAC `N - 1` `pc + 86` `pc + 86` MEMSAFE_LOOPINV_ETA2 THEN
  REPEAT CONJ_TAC THENL
   [(* G0 ~(N-1=0) *)
    REPEAT(FIRST_X_ASSUM(MP_TAC o check(fun th->concl th=`~(N=0)`||concl th=`~(N=1)`))) THEN ARITH_TAC;
    (* G1 init pc -> pc+86 (17-insn prologue), i=0 events empty              *)
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA2_EXEC (1--10) THEN
    X86_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA2_EXEC "s11" THEN
    X86_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA2_EXEC "s12" THEN
    COLLAPSE_VPBW_TAC `read YMM6 s12` YMM6_CONST_ETA2 THEN
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA2_EXEC (13--13) THEN
    X86_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA2_EXEC "s14" THEN
    X86_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA2_EXEC "s15" THEN
    COLLAPSE_VPBW_TAC `read YMM7 s15` YMM7_CONST_ETA2 THEN
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA2_EXEC (16--17) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_ETA2_BYTES; REJ_NIBBLES_ETA2;
                NIBBLES_OF_BYTES; FILTER; MAP; LENGTH; num_of_wordlist] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_TRIVIAL] THEN CONV_TAC WORD_REDUCE_CONV THEN
    EXISTS_TAC `[]:(uarch_event)list` THEN
    REWRITE_TAC[APPEND; memaccess_inbounds; ALL; EX; FST; SND];
    (* G2 forward body edge: CLEAN_BODY_MEMSAFE@i + bridge                   *)
    G2_BODY_BRIDGE_ETA2_TAC;
    (* G3 re-entry body edge (0<i, pc+86->pc+86, inv i -> inv i): refl       *)
    REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    (* G4 exit obligation -- LEFT OPEN                                       *)
    ALL_TAC] THEN
  (* exit-block entry facts (hyp @ N-1), as in value CORRECT_SCAFFOLD_TAC.   *)
  SUBGOAL_THEN `16 * (N-1) <= 120 /\ LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(0,16*(N-1)) inlist):int16 list) <= 248` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `N-1` o check(is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(N-1)) inlist):int32 list) <= 248` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES]; ALL_TAC];;

(* ========================================================================= *)
(* G4 exit-block.  MEMSAFE_LOOPINV_ETA2(N-1) @ pc+86 -> weak MEMSAFE post @  *)
(* pc+542.  Follows the value proof's                                        *)
(* `ASM_CASES niblen(16N)<=248 THENL [OFFSET_ARM; MIDEXIT_ARM]`.  Intermediate *)
(* ENSURES_TRANS predicates (q86_ms, q399_ms) carry events DEEP-RIGHT.       *)
(* ========================================================================= *)

(* q399_ms / q86_ms: value q399_eta2 / q86_eta2 + events deep-right.         *)
let q399_ms_eta2 = `\s. (bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
      read RIP s = word(pc + 399) /\ read RSP s = stackpointer /\
      read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
      read(memory :> bytes(table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
      read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
      read RAX s = word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*N) inlist):int32 list)) /\
      read RCX s = word(16*N) /\
      read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*N) inlist):int32 list))) s =
        num_of_wordlist(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*N) inlist))) /\
      (exists e_acc:(uarch_event)list. read events s = APPEND e_acc (e:(uarch_event)list) /\
        memaccess_inbounds e_acc [(buf:int64),136; (table:int64),2048] [(res:int64),1024])`;;

let q86_ms_eta2 = `\s. (bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
      read RIP s = word(pc + 86) /\ read RSP s = stackpointer /\
      read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
      read(memory :> bytes(table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
      read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
      read YMM3 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
      read YMM4 s = word 908173248920127022929968509872062022378588115024631874819275168689514742274 /\
      read YMM5 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
      read YMM6 s = word 104203162506446325494781756494581186443189907921581107878096444258040508638816 /\
      read YMM7 s = word 8834370125682169483754557489027840684616615904908870377619408255734579205 /\
      read RAX s = word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*N) inlist):int32 list)) /\
      read RCX s = word(16*N) /\
      read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*N) inlist):int32 list))) s =
        num_of_wordlist(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*N) inlist))) /\
      (exists e_acc:(uarch_event)list. read events s = APPEND e_acc (e:(uarch_event)list) /\
        memaccess_inbounds e_acc [(buf:int64),136; (table:int64),2048] [(res:int64),1024])`;;

(* generic events-associativity + ZMM-frame bridge from a body/block lemma
   instance bth (events outermost) to the current goal (events deep-right). *)
let MS_BRIDGE_FROM_ETA2 (bth:thm) : tactic =
  W(fun (asl,gl) ->
    let lframe = rand(concl bth) in
    let lpost  = rand(rator(concl bth)) in
    let lpre   = rand(rator(rator(concl bth))) in
    let gframe = rand gl in
    let subsumed_tm = mk_binop `(subsumed):(x86state->x86state->bool)->(x86state->x86state->bool)->bool` lframe gframe in
    let subsumed_th = prove(subsumed_tm,
      REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN SUBSUMED_MAYCHANGE_TAC) in
    let bth' = MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ subsumed_th bth) in
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC lpre THEN
    CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]);
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC lpost THEN
      CONJ_TAC THENL
       [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]);
        ACCEPT_TAC bth']]);;

(* Generic leg2: from `<pc+399 @ p, value + events deep-right>` to the weak
   MEMSAFE post, via SCALAR_TAIL_AT_P_MEMSAFE @ p (post-weaken + pre-weaken +
   ENSURES_FRAME_SUBSUMED, since AT_P frame ZMM0..6 c goal frame ZMM0..9).
   p is the exit position term.

   The AT_P antecedent `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,p)))<=256` must
   be discharged.  For the MID-EXIT arm the caller (MIDEXIT_DISPATCH) ASSUMEs it
   first, so `FIRST_ASSUM ACCEPT_TAC` closes it.  For the OFFSET arm the context
   instead has the stronger `<=248` fact (at the SAME position p=16*N), so we add
   a 3-way alternative: find that `<=248` fact and ARITH it up to `<=256`.  Bare
   `ASM_ARITH_TAC` on the `LENGTH(...)<=256` antecedent is FATAL — it linearises
   the whole (non-arith) hyp pile and runs away; so the `<=248`-bridge
   alternative must come with a NARROW ARITH input, not a blanket ASM_ARITH_TAC. *)
(* structural test: goal is `LENGTH(REJ_SAMPLE_ETA2_BYTES ...) <= 256`.      *)
let is_le256_rej g =
  match g with
    Comb(Comb(Const("<=",_),
      Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA2_BYTES",_),_))),
      n) -> n = `256`
  | _ -> false;;
(* the matching `<=248` assumption at the SAME argument position.            *)
let CLOSE_LE256_TAC : tactic =
  W(fun (asl,g) ->
    let arg = rand(rand(lhand g)) in   (* the SUB_LIST(0,p) inlist argument *)
    FIRST_X_ASSUM(fun th ->
       match concl th with
         Comb(Comb(Const("<=",_),
           Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA2_BYTES",_),a))),
           Comb(Const("NUMERAL",_),_)) when a = arg -> MP_TAC th
       | _ -> NO_TAC) THEN
    ARITH_TAC);;
(* Normalize the position term across BOTH goal and assumptions.  In the OFFSET
   arm the context holds `16*N=128`; the intermediate q399_ms carries `16*N` and
   the EXISTS_TAC'd AT_P pre/post also carry `16*N`, but STRIP + ASM_REWRITE via
   `16*N=128` rewrites only some occurrences, leaving a `128`-vs-`16*N` mismatch
   that MESON then chases (the `..1797` runaway).  Fix: rewrite BOTH the goal and
   every assumption by the same `_*_=numeral` equations so all positions collapse
   to the numeral — but re-ASSUME each equation afterwards (REWRITE_RULE would
   otherwise self-reduce `16*N=128` to `128=128` and drop it, un-normalising the
   goal).  In the MID-EXIT arm there is no such equation and this is a no-op. *)
let NORMPOS_TAC : tactic =
  W(fun (asl,gl) ->
    let poseqs = mapfilter (fun (_,th) ->
        let l,_ = dest_eq(concl th) in
        if (match l with Comb(Comb(Const("*",_),_),_) -> true | _ -> false)
        then th else fail()) asl in
    if poseqs = [] then ALL_TAC
    else RULE_ASSUM_TAC(REWRITE_RULE poseqs) THEN REWRITE_TAC poseqs THEN
         MAP_EVERY (fun th -> ASSUME_TAC th) poseqs);;
let SCALAR_TAIL_LEG2_MS_ETA2 (p:term) : tactic =
  W(fun (asl,gl) ->
    let atp = SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;p;`stackpointer:int64`;`e:(uarch_event)list`] MLDSA_REJ_UNIFORM_ETA2_SCALAR_TAIL_AT_P_MEMSAFE in
    let atp_ens = snd(dest_imp(concl atp)) in
    let _,ppf = strip_comb atp_ens in
    let atp_pre = el 1 ppf and atp_post = el 2 ppf in
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC atp_post THEN
    CONJ_TAC THENL
     [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN NORMPOS_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC atp_pre THEN
      CONJ_TAC THENL
       [GEN_TAC THEN STRIP_TAC THEN NORMPOS_TAC THEN ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]);
        MP_TAC atp THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THEN
          (fun (a,g) ->
             if is_le256_rej g then
               (FIRST [FIRST_ASSUM ACCEPT_TAC; CLOSE_LE256_TAC]) (a,g)
             else (FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]) (a,g));
          MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_FRAME_SUBSUMED) THEN
          REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN SUBSUMED_MAYCHANGE_TAC]]]);;

(* The OFFSET-arm lemma (16N=128 forced by niblen<=248 + WOP-disjunct1);
   the value EXIT_OFFSET_ETA2 with events threaded + weak MEMSAFE post. *)
let exit_offset_ms_eta2_tm = `
  !res buf table (inlist:byte list) pc N stackpointer e.
       LENGTH inlist = 136 /\
       nonoverlapping_modulo (2 EXP 64) (pc, 543) (val res,1024) /\
       nonoverlapping_modulo (2 EXP 64) (pc, 543) (val buf, 136) /\
       nonoverlapping_modulo (2 EXP 64) (pc, 543) (val table,2048) /\
       nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 136) /\
       nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table,2048) /\
       16 * N = 128 /\
       LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(0,16*N) inlist):int16 list) <= 248
       ==> ensures x86
            (\s. (bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
                 read RIP s = word(pc + 86) /\ read RSP s = stackpointer /\
                 read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
                 read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                 read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                 read YMM3 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
                 read YMM4 s = word 908173248920127022929968509872062022378588115024631874819275168689514742274 /\
                 read YMM5 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
                 read YMM6 s = word 104203162506446325494781756494581186443189907921581107878096444258040508638816 /\
                 read YMM7 s = word 8834370125682169483754557489027840684616615904908870377619408255734579205 /\
                 read RAX s = word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*(N-1)) inlist):int32 list)) /\
                 read RCX s = word(16*(N-1)) /\
                 read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*(N-1)) inlist):int32 list))) s =
                   num_of_wordlist(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0, 16*(N-1)) inlist))) /\
                 (exists e_acc:(uarch_event)list. read events s = APPEND e_acc e /\
                   memaccess_inbounds e_acc [buf,136; table,2048] [res,1024]))
            (\s. read RIP s = word(pc + LENGTH(BUTLAST mldsa_rej_uniform_eta2_tmc)) /\
                 (exists e2. read events s = APPEND e2 e /\
                   memaccess_inbounds e2 [buf,136; table,2048] [res,1024]))
            (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
             MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9] ,,
             MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(res,1024)])`;;

let EXIT_OFFSET_MS_ETA2 = prove(exit_offset_ms_eta2_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_NIBBLES_ETA2(SUB_LIST(0,16*N) inlist):int16 list) <= 248` then ACCEPT_TAC th else NO_TAC); ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC q399_ms_eta2 THEN
  CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [(* leg1: pc+86 -> q399_ms : CLEAN_BLOCK_MEMSAFE@(N-1) -> q86_ms, head guards -> q399_ms *)
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC q86_ms_eta2 THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [(* leg1a: CLEAN_BLOCK_MEMSAFE@(N-1) -> q86_ms (pos 16N) *)
      SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL [UNDISCH_TAC `16 * N = 128` THEN ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`N:num`;`N-1`;`stackpointer:int64`;`e:(uarch_event)list`] ETA2_CLEAN_BLOCK_MEMSAFE) THEN
      SUBGOAL_THEN `N - 1 + 1 = N` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN (FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]); ALL_TAC] THEN
      DISCH_THEN(fun bth -> MS_BRIDGE_FROM_ETA2 bth);
      (* leg1b: q86_ms -> q399_ms via head guards (cmp eax,248 nt; cmp ecx,120 taken) *)
      ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,128) inlist):int32 list) <= 248` ASSUME_TAC THENL
       [UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THEN
        SUBST1_TAC(ASSUME `16 * N = 128`) THEN REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~(&(val(word_zx(word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,128) inlist):int32 list)):int64):int32)):int - &248 = &(val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,128) inlist):int32 list)):int64):int32) (word 248):int32))) \/ val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,128) inlist):int32 list)):int64):int32) (word 248):int32) = 0` ASSUME_TAC THENL
       [MATCH_MP_TAC JA_NOT_TAKEN_LE THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(~(&(val(word_zx(word(128):int64):int32)):int - &120 = &(val(word_sub(word_zx(word(128):int64):int32) (word 120):int32))) \/ val(word_sub(word_zx(word(128):int64):int32) (word 120):int32) = 0)` ASSUME_TAC THENL
       [MATCH_MP_TAC JA_TAKEN_GT THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA2_EXEC (1--4) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `16 * N = 128`]) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCHARGE_MEMSAFE_ASM_TAC];
    (* leg2: q399_ms -> pc+542 : SCALAR_TAIL_AT_P_MEMSAFE @ p=16N, post-weaken to weak MEMSAFE post *)
    SCALAR_TAIL_LEG2_MS_ETA2 `16*N`]);;

(* ------------------------------------------------------------------------- *)
(* MID-EXIT arm (the value MIDEXIT_ARM_TAC lifted to MEMSAFE). For a crossover at *)
(* pexpr, leg1 = MID_EXIT_*_MEMSAFE @ N-1 (reaches pc+399@pexpr, events      *)
(* outermost -> bridge to qpost_ms deep-right), leg2 = SCALAR_TAIL_AT_P_MEMSAFE *)
(* @ pexpr (post-weakened to weak MEMSAFE post).                             *)
(* ------------------------------------------------------------------------- *)

(* qpost_ms for a mid-exit lemma instance: its post (events outermost) re-threaded
   events deep-right, at i:=N-1.  midthm is the value-shape MEMSAFE lemma. *)
let midexit_qpost_ms_eta2 (midthm:thm) : term =
  let post = rand(rator(snd(dest_imp(snd(strip_forall(concl midthm)))))) in
  let post = vsubst [`N-1`,`i:num`] post in
  let sv, body = dest_abs post in
  (* body = value_post /\ ev  (events outermost) -> re-thread deep-right     *)
  let value_post = lhand body in
  mk_abs(sv, conj_append_right value_post (vsubst[sv,`s:x86state`] ev_existential_eta2));;

let MIDEXIT_DISPATCH_MS_ETA2 (midthm:thm) (pexpr:term) (prevpos:term) : tactic =
  let qpost = midexit_qpost_ms_eta2 midthm in
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC qpost THEN
  CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* leg1: MID_EXIT lemma @ N-1, bridge events-outermost post -> qpost deep-right *)
    MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`N-1`;`stackpointer:int64`;`e:(uarch_event)list`] midthm) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]); ALL_TAC] THEN
    DISCH_THEN(fun bth -> MS_BRIDGE_FROM_ETA2 bth);
    (* leg2: niblen(pexpr)<=256 then SCALAR_TAIL_AT_P_MEMSAFE@pexpr          *)
    SUBGOAL_THEN (mk_comb(mk_comb(`(<=):num->num->bool`,
        mk_comb(`LENGTH:(int32)list->num`, mk_comb(`REJ_SAMPLE_ETA2_BYTES:byte list->int32 list`,
          mk_comb(mk_comb(`SUB_LIST:num#num->byte list->byte list`,mk_pair(`0`,pexpr)),`inlist:byte list`)))), `256`)) ASSUME_TAC THENL
     [SUBGOAL_THEN (mk_eq(pexpr, mk_binop `(+):num->num->num` prevpos `4`)) SUBST1_TAC THENL
       [UNDISCH_TAC `~(N=0)` THEN UNDISCH_TAC `16 * N <= 136` THEN ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC OUTLEN0_LE_256_FROM_SUBITER_ETA2 THEN CONJ_TAC THENL
       [UNDISCH_TAC `16 * N <= 136` THEN UNDISCH_TAC `~(N=0)` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=136` THEN ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
    SCALAR_TAIL_LEG2_MS_ETA2 pexpr];;

(* ------------------------------------------------------------------------- *)
(* OFFSET arm: niblen(16N)<=248 in context -> force 16N=128 (N=8), apply     *)
(* EXIT_OFFSET_MS_ETA2 (the MEMSAFE analogue of value OFFSET_ARM_TAC).       *)
(* ------------------------------------------------------------------------- *)
let OFFSET_ARM_MS_ETA2_TAC : tactic =
  SUBGOAL_THEN `16 * N = 128` ASSUME_TAC THENL
   [SUBGOAL_THEN `120 < 16 * N` ASSUME_TAC THENL
     [UNDISCH_TAC `120 < 16 * N \/ 248 < LENGTH (REJ_NIBBLES_ETA2 (SUB_LIST (0,16 * N) inlist):int16 list)` THEN
      REWRITE_TAC[GSYM LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN
      UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `N = 8` (fun th -> REWRITE_TAC[th] THEN CONV_TAC NUM_REDUCE_CONV) THEN
    SUBGOAL_THEN `16 * N <= 136` ASSUME_TAC THENL
     [UNDISCH_TAC `16 * (N-1) <= 120` THEN UNDISCH_TAC `~(N=0)` THEN
      SPEC_TAC(`N:num`,`N:num`) THEN INDUCT_TAC THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `120 < 16 * N` THEN UNDISCH_TAC `16 * N <= 136` THEN ARITH_TAC; ALL_TAC] THEN
  (* EXIT_OFFSET_MS_ETA2 pre is events-OUTERMOST; the scaffold goal pre is events-deep-right.
     Bridge via MS_BRIDGE_FROM_ETA2 (pre-assoc + post + frame all match by content). *)
  MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`N:num`;`stackpointer:int64`;`e:(uarch_event)list`] EXIT_OFFSET_MS_ETA2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM LENGTH_REJ_SAMPLE_ETA2_BYTES] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THEN
    SUBST1_TAC(ASSUME `16 * N = 128`) THEN REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun bth -> MS_BRIDGE_FROM_ETA2 bth);;

let MIDEXIT_ARM_MS_ETA2_TAC : tactic =
  SUBGOAL_THEN `248 < LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*N) inlist):int32 list)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(LENGTH (REJ_SAMPLE_ETA2_BYTES (SUB_LIST (0,16 * N) inlist):int32 list) <= 248)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * N <= 136` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (N-1) <= 120` THEN UNDISCH_TAC `~(N=0)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * ((N-1)+1) <= 136` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * N <= 136` THEN UNDISCH_TAC `~(N=0)` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(N-1)+4) inlist):int32 list) <= 248` THENL
   [ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(N-1)+8) inlist):int32 list) <= 248` THENL
     [ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*(N-1)+12) inlist):int32 list) <= 248` THENL
       [SUBGOAL_THEN `248 < LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*((N-1)+1)) inlist):int32 list)` ASSUME_TAC THENL
         [SUBGOAL_THEN `16*((N-1)+1) = 16*N` SUBST1_TAC THENL
           [UNDISCH_TAC `~(N=0)` THEN ARITH_TAC; ALL_TAC] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MIDEXIT_DISPATCH_MS_ETA2 MID_EXIT_CASE4_MEMSAFE_ETA2 `16*((N-1)+1)` `16*(N-1)+12`;
        MIDEXIT_DISPATCH_MS_ETA2 MID_EXIT_SUBITER3_MEMSAFE_ETA2 `16*(N-1)+12` `16*(N-1)+8`];
      MIDEXIT_DISPATCH_MS_ETA2 MID_EXIT_SUBITER2_MEMSAFE_ETA2 `16*(N-1)+8` `16*(N-1)+4`];
    MIDEXIT_DISPATCH_MS_ETA2 MID_EXIT_SUBITER1_MEMSAFE_ETA2 `16*(N-1)+4` `16*(N-1)`];;

(* ------------------------------------------------------------------------- *)
(* The complete exit-block tactic + the core MLDSA_REJ_UNIFORM_ETA2_MEMSAFE. *)
(* ------------------------------------------------------------------------- *)
let EXIT_BLOCK_MS_ETA2_TAC : tactic =
  ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA2_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THENL
   [OFFSET_ARM_MS_ETA2_TAC; MIDEXIT_ARM_MS_ETA2_TAC];;

let core_ms_eta2_tm = `!res buf table (inlist:byte list) e pc.
        LENGTH inlist = 136 /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (res, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (buf, 136) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (table, 2048) /\
        nonoverlapping (res, 1024) (buf, 136) /\
        nonoverlapping (res, 1024) (table, 2048)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [res; buf; table] s /\
                  read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table /\
                  read events s = e)
             (\s. read RIP s = word(pc + LENGTH (BUTLAST mldsa_rej_uniform_eta2_tmc)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     memaccess_inbounds e2 [buf,136; table,2048] [res,1024]))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`;;

let MLDSA_REJ_UNIFORM_ETA2_MEMSAFE_CORE = prove(core_ms_eta2_tm,
  MEMSAFE_SCAFFOLD_ETA2_TAC THEN EXIT_BLOCK_MS_ETA2_TAC);;

let MLDSA_REJ_UNIFORM_ETA2_MEMSAFE = prove
 (`!res buf table (inlist:byte list) e pc.
    LENGTH inlist = 136 /\
    nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (res, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (buf, 136) /\
    nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (table, 2048) /\
    nonoverlapping (res, 1024) (buf, 136) /\
    nonoverlapping (res, 1024) (table, 2048)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [res; buf; table] s /\
              read(memory :> bytes(buf,136)) s = num_of_wordlist inlist /\
              read(memory :> bytes(table,2048)) s =
                num_of_wordlist mldsa_rej_uniform_table /\
              read events s = e)
         (\s. read RIP s = word(pc + LENGTH (BUTLAST mldsa_rej_uniform_eta2_tmc)) /\
              (?e2. read events s = APPEND e2 e /\
                    memaccess_inbounds e2 [buf,136; table,2048]
                                          [res,1024]))
         (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
          MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(res,1024)])`,
  MATCH_ACCEPT_TAC MLDSA_REJ_UNIFORM_ETA2_MEMSAFE_CORE);;

(* Concrete-length variant of the core MEMSAFE (exit RIP = word(pc+542)).    *)
let MLDSA_REJ_UNIFORM_ETA2_MEMSAFE_CORE_CONCRETE =
  CONV_RULE(REWRITE_CONV[LENGTH_MLDSA_REJ_UNIFORM_ETA2_TMC;
                         fst MLDSA_REJ_UNIFORM_ETA2_EXEC])
    MLDSA_REJ_UNIFORM_ETA2_MEMSAFE_CORE;;

(* ------------------------------------------------------------------------- *)
(* The subroutine memory safety theorem.                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_REJ_UNIFORM_ETA2_NOIBT_SUBROUTINE_SAFE =
  let saved_tic = !type_invention_error in
  type_invention_error := false;
  let th = prove
   (`!res buf table (inlist:byte list) e pc stackpointer returnaddress.
        LENGTH inlist = 136 /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (res, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (buf, 136) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (table, 2048) /\
        nonoverlapping (res, 1024) (buf, 136) /\
        nonoverlapping (res, 1024) (table, 2048) /\
        nonoverlapping (stackpointer, 8) (res, 1024) /\
        nonoverlapping (stackpointer, 8) (buf, 136) /\
        nonoverlapping (stackpointer, 8) (table, 2048) /\
        nonoverlapping (stackpointer, 8) (word pc, LENGTH mldsa_rej_uniform_eta2_tmc)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_rej_uniform_eta2_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [res; buf; table] s /\
                  read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                       [buf,136; table,2048; stackpointer,8]
                       [res,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
    REWRITE_TAC[LENGTH_MLDSA_REJ_UNIFORM_ETA2_TMC] THEN
    X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_rej_uniform_eta2_tmc
      MLDSA_REJ_UNIFORM_ETA2_MEMSAFE_CORE_CONCRETE THEN
    DISCHARGE_MEMSAFE_TAC) in
  type_invention_error := saved_tic;
  th;;

(* Full (untrimmed, IBT-prefixed) subroutine wrapper via ADD_IBT_RULE.       *)
let MLDSA_REJ_UNIFORM_ETA2_SUBROUTINE_SAFE =
  ADD_IBT_RULE MLDSA_REJ_UNIFORM_ETA2_NOIBT_SUBROUTINE_SAFE;;

(* ========================================================================= *)
(* Windows ABI variants.                                                     *)
(*                                                                           *)
(* The mldsa-native original ships no Windows theorems. We add them here     *)
(* following the template of x86/proofs/mlkem_rej_uniform_VARIABLE_TIME.ml   *)
(* (Windows CORRECT) and x86/proofs/mldsa_ntt.ml (manual xmm-spill splice).  *)
(*                                                                           *)
(* Unlike mlkem_rej_uniform (which deliberately avoids xmm6 so its Windows   *)
(* prologue only saves rdi/rsi and WINDOWS_X86_WRAP_STACK_TAC applies), the  *)
(* eta2 kernel uses xmm6-xmm9 as scratch registers (broadcast constants and  *)
(* the gather step). xmm6-xmm15 are nonvolatile under the Microsoft x64 ABI, *)
(* so the Windows entry point spills xmm6,xmm7,xmm8,xmm9 (and rdi/rsi) to an  *)
(* 80-byte stack frame. The standard wrap tactics do not model this spill,   *)
(* so we splice the SysV core into the Windows prologue/epilogue by hand,     *)
(* exactly as mldsa_ntt.ml does.                                             *)
(* ========================================================================= *)

let mldsa_rej_uniform_eta2_windows_mc = define_from_elf
   "mldsa_rej_uniform_eta2_windows_mc"
   "x86/mldsa/mldsa_rej_uniform_eta2_VARIABLE_TIME.obj";;

let mldsa_rej_uniform_eta2_windows_tmc = define_trimmed
   "mldsa_rej_uniform_eta2_windows_tmc" mldsa_rej_uniform_eta2_windows_mc;;

let MLDSA_REJ_UNIFORM_ETA2_WINDOWS_TMC_EXEC =
  X86_MK_EXEC_RULE mldsa_rej_uniform_eta2_windows_tmc;;

(* The Windows entry spills xmm6-xmm9 + rdi + rsi in a 12-instruction         *)
(* prologue (endbr64; sub rsp,80; movups [rsp],xmm6; movups [rsp+16],xmm7;    *)
(*  movups [rsp+32],xmm8; movups [rsp+48],xmm9; mov [rsp+64],rdi;             *)
(*  mov [rsp+72],rsi; mov rdi,rcx; mov rsi,rdx; mov rdx,r8), after which the  *)
(* SysV body begins at byte offset 0x30 = 48. Because the trimmed core        *)
(* (mldsa_rej_uniform_eta2_tmc) drops its own leading ENDBR64 (4 bytes), the  *)
(* SysV body's first real instruction is at Windows offset 48 = post-ENDBR64  *)
(* Windows-pc 44 plus the 4-byte core ENDBR64; the subprogram splice is keyed *)
(* on pc + 44. The epilogue restores xmm6-xmm9/rdi/rsi and pops the frame in  *)
(* 8 instructions.                                                           *)
let MLDSA_REJ_UNIFORM_ETA2_NOIBT_WINDOWS_SUBROUTINE_CORRECT =
  let saved_tic = !type_invention_error in
  type_invention_error := false;
  let th = prove
   (`!res buf table (inlist:byte list) pc stackpointer returnaddress.
        LENGTH inlist = 136 /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_windows_tmc) (res, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_windows_tmc) (buf, 136) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_windows_tmc) (table, 2048) /\
        nonoverlapping (res, 1024) (buf, 136) /\
        nonoverlapping (res, 1024) (table, 2048) /\
        nonoverlapping (word_sub stackpointer (word 80),88) (res, 1024) /\
        nonoverlapping (word_sub stackpointer (word 80),88) (buf, 136) /\
        nonoverlapping (word_sub stackpointer (word 80),88) (table, 2048) /\
        nonoverlapping (word_sub stackpointer (word 80),88)
                       (word pc, LENGTH mldsa_rej_uniform_eta2_windows_tmc)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_rej_uniform_eta2_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [res; buf; table] s /\
                  read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (let outlist = SUB_LIST(0,256)
                      (REJ_SAMPLE_ETA2_BYTES inlist) in
                   let outlen = LENGTH outlist in
                   outlen <= 256 /\
                   WINDOWS_C_RETURN s = word outlen /\
                   read(memory :> bytes(res,4 * outlen)) s =
                     num_of_wordlist outlist /\
                   (!i. i < outlen
                        ==> ival(EL i outlist:int32) < &3 /\
                            -- &3 < ival(EL i outlist:int32))))
             (MAYCHANGE [RSP] ,,
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(res,1024)] ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 80),80)])`,
    REWRITE_TAC[fst MLDSA_REJ_UNIFORM_ETA2_WINDOWS_TMC_EXEC] THEN
    REPLICATE_TAC 5 GEN_TAC THEN
    WORD_FORALL_OFFSET_TAC 80 THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[fst MLDSA_REJ_UNIFORM_ETA2_WINDOWS_TMC_EXEC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[WINDOWS_C_ARGUMENTS; WINDOWS_C_RETURN] THEN
    REWRITE_TAC[WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
    ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
    ENSURES_PRESERVED_TAC "init_xmm6" `ZMM6 :> bottomhalf :> bottomhalf` THEN
    ENSURES_PRESERVED_TAC "init_xmm7" `ZMM7 :> bottomhalf :> bottomhalf` THEN
    ENSURES_PRESERVED_TAC "init_xmm8" `ZMM8 :> bottomhalf :> bottomhalf` THEN
    ENSURES_PRESERVED_TAC "init_xmm9" `ZMM9 :> bottomhalf :> bottomhalf` THEN
    REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
    REWRITE_TAC(map GSYM [YMM6; YMM7; YMM8; YMM9]) THEN
    GHOST_INTRO_TAC `init_ymm6:int256` `read YMM6` THEN
    GHOST_INTRO_TAC `init_ymm7:int256` `read YMM7` THEN
    GHOST_INTRO_TAC `init_ymm8:int256` `read YMM8` THEN
    GHOST_INTRO_TAC `init_ymm9:int256` `read YMM9` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA2_WINDOWS_TMC_EXEC (1--10) THEN
    MP_TAC(SPECL [`res:int64`; `buf:int64`; `table:int64`; `inlist:byte list`;
                  `pc + 44`]
      MLDSA_REJ_UNIFORM_ETA2_CORRECT_BOUND_CONCRETE) THEN
    ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN NONOVERLAPPING_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    X86_BIGSTEP_TAC MLDSA_REJ_UNIFORM_ETA2_WINDOWS_TMC_EXEC "s11" THENL
     [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
       (BYTES_LOADED_SUBPROGRAM_RULE mldsa_rej_uniform_eta2_windows_tmc
       (REWRITE_RULE[BUTLAST_CLAUSES]
        (AP_TERM `BUTLAST:byte list->byte list` mldsa_rej_uniform_eta2_tmc))
       44));
      RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[C_RETURN]) THEN
    MAP_EVERY ABBREV_TAC
     [`ymm6_epilog = read YMM6 s11`;
      `ymm7_epilog = read YMM7 s11`;
      `ymm8_epilog = read YMM8 s11`;
      `ymm9_epilog = read YMM9 s11`] THEN
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA2_WINDOWS_TMC_EXEC (12--19) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (* Substitute the four preserved-xmm equations (init_xmmN =                *)
    (* word_subword init_ymmN (0,128)) into the goal before splitting, so each *)
    (* xmm-restore conjunct becomes a pure word identity closed by WORD_BLAST. *)
    EVERY(map (fun v ->
      TRY(FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (fun th -> is_eq(concl th) && rand(concl th) = v))))
      [`init_xmm6:int128`; `init_xmm7:int128`;
       `init_xmm8:int128`; `init_xmm9:int128`]) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_BLAST) THEN
    ASM_REWRITE_TAC[]) in
  type_invention_error := saved_tic;
  th;;

let MLDSA_REJ_UNIFORM_ETA2_WINDOWS_SUBROUTINE_CORRECT =
  ADD_IBT_RULE MLDSA_REJ_UNIFORM_ETA2_NOIBT_WINDOWS_SUBROUTINE_CORRECT;;

(* ------------------------------------------------------------------------- *)
(* Windows-ABI memory safety (SAFE).  Same manual 4-xmm-spill splice as the  *)
(* Windows CORRECT above, but wrapping the events/memaccess_inbounds core     *)
(* MLDSA_REJ_UNIFORM_ETA2_MEMSAFE_CORE_CONCRETE.  The safety witness e2 for   *)
(* the whole Windows body is the SysV core trace e2 framed by the spill       *)
(* prologue stores (xmm6/7/8/9 + rdi/rsi) and epilogue loads (xmm6/7/8/9 +    *)
(* rdi/rsi + return-address load) plus the final EventJump, all inside the    *)
(* [stackpointer-80,88]/[stackpointer-80,80] frame, discharged by            *)
(* DISCHARGE_MEMACCESS_INBOUNDS_TAC.                                         *)
(* ------------------------------------------------------------------------- *)
let MLDSA_REJ_UNIFORM_ETA2_NOIBT_WINDOWS_SUBROUTINE_SAFE =
  let saved_tic = !type_invention_error in
  type_invention_error := false;
  let th = prove
   (`!res buf table (inlist:byte list) e pc stackpointer returnaddress.
        LENGTH inlist = 136 /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_windows_tmc) (res, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_windows_tmc) (buf, 136) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_windows_tmc) (table, 2048) /\
        nonoverlapping (res, 1024) (buf, 136) /\
        nonoverlapping (res, 1024) (table, 2048) /\
        nonoverlapping (word_sub stackpointer (word 80),88) (res, 1024) /\
        nonoverlapping (word_sub stackpointer (word 80),88) (buf, 136) /\
        nonoverlapping (word_sub stackpointer (word 80),88) (table, 2048) /\
        nonoverlapping (word_sub stackpointer (word 80),88)
                       (word pc, LENGTH mldsa_rej_uniform_eta2_windows_tmc)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_rej_uniform_eta2_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [res; buf; table] s /\
                  read(memory :> bytes(buf, 136)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                       [buf,136; table,2048; word_sub stackpointer (word 80),88]
                       [res,1024; word_sub stackpointer (word 80),80]))
             (MAYCHANGE [RSP] ,,
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(res,1024)] ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 80),80)])`,
    REWRITE_TAC[fst MLDSA_REJ_UNIFORM_ETA2_WINDOWS_TMC_EXEC] THEN
    REPLICATE_TAC 6 GEN_TAC THEN
    WORD_FORALL_OFFSET_TAC 80 THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[fst MLDSA_REJ_UNIFORM_ETA2_WINDOWS_TMC_EXEC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[WINDOWS_C_ARGUMENTS; WINDOWS_C_RETURN] THEN
    REWRITE_TAC[WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
    ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
    ENSURES_PRESERVED_TAC "init_xmm6" `ZMM6 :> bottomhalf :> bottomhalf` THEN
    ENSURES_PRESERVED_TAC "init_xmm7" `ZMM7 :> bottomhalf :> bottomhalf` THEN
    ENSURES_PRESERVED_TAC "init_xmm8" `ZMM8 :> bottomhalf :> bottomhalf` THEN
    ENSURES_PRESERVED_TAC "init_xmm9" `ZMM9 :> bottomhalf :> bottomhalf` THEN
    REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
    REWRITE_TAC(map GSYM [YMM6; YMM7; YMM8; YMM9]) THEN
    GHOST_INTRO_TAC `init_ymm6:int256` `read YMM6` THEN
    GHOST_INTRO_TAC `init_ymm7:int256` `read YMM7` THEN
    GHOST_INTRO_TAC `init_ymm8:int256` `read YMM8` THEN
    GHOST_INTRO_TAC `init_ymm9:int256` `read YMM9` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA2_WINDOWS_TMC_EXEC (1--10) THEN
    MP_TAC(SPECL [`res:int64`; `buf:int64`; `table:int64`; `inlist:byte list`;
                  `read events s10`; `pc + 44`]
      MLDSA_REJ_UNIFORM_ETA2_MEMSAFE_CORE_CONCRETE) THEN
    ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN NONOVERLAPPING_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    X86_BIGSTEP_TAC MLDSA_REJ_UNIFORM_ETA2_WINDOWS_TMC_EXEC "s11" THENL
     [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
       (BYTES_LOADED_SUBPROGRAM_RULE mldsa_rej_uniform_eta2_windows_tmc
       (REWRITE_RULE[BUTLAST_CLAUSES]
        (AP_TERM `BUTLAST:byte list->byte list` mldsa_rej_uniform_eta2_tmc))
       44));
      RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN
    MAP_EVERY ABBREV_TAC
     [`ymm6_epilog = read YMM6 s11`;
      `ymm7_epilog = read YMM7 s11`;
      `ymm8_epilog = read YMM8 s11`;
      `ymm9_epilog = read YMM9 s11`] THEN
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA2_WINDOWS_TMC_EXEC (12--19) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [EXISTS_TAC
       `CONS (EventJump (word (pc + 622),returnaddress))
        (CONS (EventLoad (word_add stackpointer (word 80),8))
        (CONS (EventLoad (word_add stackpointer (word 72),8))
        (CONS (EventLoad (word_add stackpointer (word 64),8))
        (CONS (EventLoad (word_add stackpointer (word 48),16))
        (CONS (EventLoad (word_add stackpointer (word 32),16))
        (CONS (EventLoad (word_add stackpointer (word 16),16))
        (CONS (EventLoad (stackpointer,16))
        (APPEND e2
        (CONS (EventStore (word_add stackpointer (word 72),8))
        (CONS (EventStore (word_add stackpointer (word 64),8))
        (CONS (EventStore (word_add stackpointer (word 48),16))
        (CONS (EventStore (word_add stackpointer (word 32),16))
        (CONS (EventStore (word_add stackpointer (word 16),16))
        (CONS (EventStore (stackpointer,16)) []))))))))))))))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND];
        DISCHARGE_MEMACCESS_INBOUNDS_TAC];
      EVERY(map (fun v ->
        TRY(FIRST_X_ASSUM(SUBST1_TAC o SYM o
          check (fun th -> is_eq(concl th) && rand(concl th) = v))))
        [`init_xmm6:int128`; `init_xmm7:int128`;
         `init_xmm8:int128`; `init_xmm9:int128`]) THEN
      REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST]) in
  type_invention_error := saved_tic;
  th;;

let MLDSA_REJ_UNIFORM_ETA2_WINDOWS_SUBROUTINE_SAFE =
  ADD_IBT_RULE MLDSA_REJ_UNIFORM_ETA2_NOIBT_WINDOWS_SUBROUTINE_SAFE;;

(* NOTE: the mldsa-native original ends with a trailing                      *)
(*   needs "mldsa_native/x86_64/proofs/subroutine_signatures.ml"             *)
(* purely to register the subroutine signature in the constant-time harness. *)
(* In s2n-bignum that registration is not referenced by this proof (the      *)
(* SAFE theorems are derived from the MEMSAFE core, not via                   *)
(* PROVE_SAFETY_SPEC_TAC), so the load is dropped, matching                   *)
(* x86/proofs/mlkem_rej_uniform_VARIABLE_TIME.ml.                             *)
