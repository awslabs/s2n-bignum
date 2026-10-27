(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics shared by the proofs of code compiled from the C       *)
(* implementation in mlkem-native (see arm/mlkem_native/README.md).          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(* ------------------------------------------------------------------------- *)
(* Normalization of 32-bit arithmetic in W registers.                        *)
(* ------------------------------------------------------------------------- *)

(*** Writing and then reading a W register ***)

let WORD_ZX_ZX_32_64 = prove
 (`!x:int32. word_zx(word_zx x:int64) = x`,
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH]);;

(*** Simplify the results of 32-bit arithmetic as stored by the simulator ***)

let MLKEM_NATIVE_W_SIMP_TAC =
  REWRITE_TAC[WORD_ZX_ZX_32_64; WORD_ADD; WORD_MUL; WORD_VAL];;

(*** Truncation to 16 bits as reduction of the signed value ***)

let WORD_ZX_32_16 = prove
 (`!w:int32. (word_zx w:int16) = iword(ival w)`,
  REWRITE_TAC[GSYM word_sx] THEN BITBLAST_TAC);;

(*** Eliminate ival(iword t) when t is in range, innermost terms first ***)

let IVAL_IWORD_ELIM_TAC =
  REPEAT(W(fun (asl,w) ->
     let t = hd(sort free_in
        (find_terms (can (term_match [] `ival(iword x)`)) w)) in
     let th = PART_MATCH (lhand o rand) IVAL_IWORD t in
     MP_TAC th THEN REWRITE_TAC[DIMINDEX_16; DIMINDEX_32] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     ANTS_TAC THENL [BOUNDER_TAC[]; DISCH_THEN SUBST1_TAC]));;

(* ------------------------------------------------------------------------- *)
(* The scalar Barrett reduction mlk_barrett_reduce, as compiled using a pair *)
(* of 32-bit multiply-adds, is exactly the "barred" function used for the    *)
(* vectorized code.                                                          *)
(* ------------------------------------------------------------------------- *)

let BARRED_QUOTIENT = prove
 (`!x:int. ((&2 * x * &20159) div &65536 + &1024) div &2048 =
           (&33554432 + x * &20159) div &67108864`,
  GEN_TAC THEN
  SUBGOAL_THEN `(&2 * x * &20159) div &65536 = (x * &20159) div &32768`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_ARITH `&65536:int = &2 * &32768`] THEN
    SIMP_TAC[GSYM INT_DIV_DIV; INT_POS; GSYM INT_MUL_ASSOC] THEN
    SIMP_TAC[INT_DIV_MUL; INT_OF_NUM_EQ; ARITH_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[INT_ARITH `&33554432 + x:int = x + &1024 * &32768`;
              INT_ARITH `&67108864:int = &32768 * &2048`] THEN
  SIMP_TAC[GSYM INT_DIV_DIV; INT_POS; INT_DIV_MUL_ADD;
           INT_OF_NUM_EQ; ARITH_EQ]);;

let BARRED_SCALAR = prove
 (`!x:int16.
        word_zx(word_add (word_sx x)
                  (word_mul (word_ishr (word_add (word 33554432)
                                         (word_mul (word_sx x) (word 20159)))
                                       26)
                            (word 4294963967)):int32):int16 =
        barred x`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_ZX_32_16; WORD_ADD_IMODULAR; WORD_MUL_IMODULAR;
              imodular; word_sx; IVAL_WORD_ISHR] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN IVAL_IWORD_ELIM_TAC THEN
  REWRITE_TAC[barred; iword_saturate; word_INT_MIN; word_INT_MAX;
              DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REPEAT(COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[] `p ==> ~p ==> q`)) THEN
    REWRITE_TAC[INT_GT; INT_NOT_LT] THEN BOUNDER_TAC[];
    ASM_REWRITE_TAC[]]) THEN
  REWRITE_TAC[WORD_RULE
   `word_sub a (word_mul b (word n)) = iword(ival a - ival b * &n)`] THEN
  IVAL_IWORD_ELIM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[BARRED_QUOTIENT] THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Adding 3329 to a negative result of "barred" gives the remainder.         *)
(* ------------------------------------------------------------------------- *)

let BARRED_CONDADD_REM = prove
 (`!x:int16.
        ival(word_add (barred x)
                      (word_and (word_ishr (barred x) 15) (word 3329))) =
        ival x rem &3329`,
  let lemma = prove
   (`(y == x) (mod &3329) /\
     --(&1664) <= y /\ y <= &1664
     ==> x rem &3329 = if y < &0 then y + &3329 else y`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[INT_REM_UNIQUE] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN
    UNDISCH_TAC `(y:int == x) (mod &3329)` THEN
    SPEC_TAC(`&3329:int`,`p:int`) THEN CONV_TAC INTEGER_RULE) in
  REWRITE_TAC[MATCH_MP lemma (CONGBOUND_RULE `barred x`)] THEN
  BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Reading arrays given as lists, and building byte arrays incrementally.    *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES16_NUM_OF_WORDLIST = prove
 (`!a:int64 (l:int16 list) n j s:armstate.
        read (memory :> bytes(a,2 * n)) s = num_of_wordlist l /\
        LENGTH l = n /\ j < n
        ==> read (memory :> bytes16(word_add a (word(2 * j)))) s = EL j l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`l:int16 list`; `j:num`] NUM_OF_WORDLIST_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && is_comb(lhs(concl th)) &&
       can (term_match [] `read c s`) (lhs(concl th))
    then REWRITE_TAC[GSYM th] else failwith "") THEN
  REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `16 * j = 8 * (2 * j)`;
              ARITH_RULE `65536 = 2 EXP (8 * 2)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES_SNOC = prove
 (`!x:int64 n s:armstate.
        read (memory :> bytes(x,n + 1)) s =
        read (memory :> bytes(x,n)) s +
        2 EXP (8 * n) * val(read (memory :> bytes8(word_add x (word n))) s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; READ_BYTES_BYTES8]);;

let SUB_LIST_0_SNOC2 = prove
 (`!l:A list n.
        n + 2 <= LENGTH l
        ==> SUB_LIST(0,n + 2) l =
            APPEND (SUB_LIST(0,n) l) [EL n l; EL (n + 1) l]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUB_LIST_SPLIT; ADD_CLAUSES] THEN
  AP_TERM_TAC THEN REWRITE_TAC[ARITH_RULE `2 = 1 + 1`; SUB_LIST_SPLIT] THEN
  REWRITE_TAC[SUB_LIST_1] THEN
  ASM_SIMP_TAC[ARITH_RULE `n + 2 <= l ==> n < l /\ n + 1 < l`] THEN
  REWRITE_TAC[APPEND]);;

(* ------------------------------------------------------------------------- *)
(* The scalar Montgomery reduction mlk_montgomery_reduce, as compiled. This  *)
(* subtracts a multiple of 3329 rather than adding one as "montred" does,    *)
(* so the results can differ by 3329 and the overflow condition is slightly  *)
(* different, but it satisfies the analogous congruence and bounds.          *)
(* ------------------------------------------------------------------------- *)

let montred_scalar = define
 `montred_scalar (t:int32):int16 =
  word_zx(word_ishr
   (word_add t
     (word_mul (word_sxfrom 15 (word_subword (word_mul t (word 4294963969))
                                             (0,16):int32))
               (word 4294963967)))
   16)`;;

let SXFROM_15_SUBWORD = prove
 (`!w:int32. word_sxfrom 15 (word_subword w (0,16):int32) =
             word_sx(word_zx w:int16)`,
  BITBLAST_TAC);;

let MONTRED_SCALAR_LEMMA = prove
 (`!t:int32.
        &2 pow 16 * ival(montred_scalar t) =
        ival(word_add t
              (word_mul (word_sx(word_zx(word_mul t (word 4294963969)):int16))
                        (word 4294963967)))`,
  GEN_TAC THEN REWRITE_TAC[montred_scalar; SXFROM_15_SUBWORD] THEN
  CONV_TAC(LAND_CONV(LAND_CONV INT_REDUCE_CONV)) THEN
  MATCH_MP_TAC(BITBLAST_RULE
   `word_zx x:int16 = word 0
    ==> &65536 * ival(word_zx(word_ishr (x:int32) 16):int16) = ival x`) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_ZX_ADD o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_16; DIMINDEX_32; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_ZX_MUL o rand o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_16; DIMINDEX_32; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[WORD_BLAST `word_zx(word_sx (x:int16):int32) = x`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_ZX_MUL o
    lhand o rand o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_16; DIMINDEX_32; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM DIVIDES_MOD; DIMINDEX_16] THEN
  CONV_TAC WORD_REDUCE_CONV THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b + 1 == 0) (mod d) ==> d divides (x + (x * a) * b)`) THEN
  REWRITE_TAC[CONG] THEN ARITH_TAC);;

let INT_DIV_65536_BOUNDS = prove
 (`(!x w. &65536 * x <= w ==> x <= w div &65536) /\
   (!x w. w <= &65536 * x ==> w div &65536 <= x)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`w:int`; `&65536:int`] INT_DIVISION) THEN
  CONV_TAC INT_REDUCE_CONV THEN ASM_INT_ARITH_TAC);;

let CONGBOUND_MONTRED_SCALAR = prove
 (`!a a' l u.
      (ival a == a') (mod &3329) /\ l <= ival a /\ ival a <= u
      ==> --(&2038402305) <= l /\ u <= &2038398975
          ==> (ival(montred_scalar a) == &(inverse_mod 3329 65536) * a')
              (mod &3329) /\
              (l - &109081343) div &2 pow 16 <= ival(montred_scalar a) /\
              ival(montred_scalar a) <= (u + &109084672) div &2 pow 16`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV INVERSE_MOD_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POW_CONV) THEN
  MP_TAC(SPECL [`&169:int`; `&65536:int`; `&3329:int`] (INTEGER_RULE
   `!d e n:int. (e * d == &1) (mod n)
                ==> !x y. ((x == d * y) (mod n) <=>
                           (e * x == y) (mod n))`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM INT_REM_EQ] THEN INT_ARITH_TAC;
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  MATCH_MP_TAC(MESON[INT_DIV_65536_BOUNDS]
   `P /\ l <= &65536 * x /\ &65536 * x <= u
    ==> P /\ l div &65536 <= x /\ x <= u div &65536`) THEN
  REWRITE_TAC[CONV_RULE(ONCE_DEPTH_CONV INT_POW_CONV)
               MONTRED_SCALAR_LEMMA] THEN
  REWRITE_TAC[WORD_RULE
   `word_add c (word_mul a b) = iword(ival c + ival a * ival b)`] THEN
  ASM_SIMP_TAC[IVAL_WORD_SX; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  W(fun (asl,w) ->
    let t = find_term (fun t -> type_of t = `:int16` &&
                               can (term_match [] `word_zx x:int16`) t) w in
    MP_TAC(ISPEC t IVAL_BOUND)) THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POW_CONV) THEN STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o
    find_term (can (term_match [] `ival(iword x:int32)`)) o snd) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POW_CONV) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `!p x y a:int. (x + y * --p == a) (mod p) <=> (x == a) (mod p)`] THEN
  ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The same Montgomery reduction as vectorized by the compiler, in the form  *)
(* that the simulation gives for each lane.                                  *)
(* ------------------------------------------------------------------------- *)

let montred_neon = define
 `montred_neon (x:int32):int16 =
  word_subword
   (word_add
     (word_mul ((word_sx:int16->int32)
                  (word_mul (word_subword x (0,16)) (word 62209)))
               (word 4294963967))
     x)
   (16,16)`;;

let MONTRED_NEON_SCALAR = prove
 (`!t:int32. montred_neon t = montred_scalar t`,
  GEN_TAC THEN
  REWRITE_TAC[montred_neon; montred_scalar; SXFROM_15_SUBWORD] THEN
  SUBGOAL_THEN `word_zx(word_mul (t:int32) (word 4294963969)):int16 =
                word_mul (word_subword t (0,16)) (word 62209)`
  SUBST1_TAC THENL
   [SIMP_TAC[WORD_ZX_MUL; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
    REWRITE_TAC[WORD_ZX_SUBWORD; DIMINDEX_16] THEN CONV_TAC WORD_REDUCE_CONV;
    SPEC_TAC(`word_mul (word_sx (word_mul (word_subword (t:int32) (0,16))
                                          (word 62209):int16))
                       (word 4294963967):int32`, `m:int32`) THEN
    BITBLAST_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The table of zetas used by the C code, as the values in the source code   *)
(* and as the bytes of the read-only data in the compiled code. The latter   *)
(* is defined here so that it can be shared by several proofs; the proofs    *)
(* still check that it is the same as the data in their object files, since *)
(* define_assert_relocs_from_elf can then only make a benign redefinition.   *)
(* ------------------------------------------------------------------------- *)

let mlk_zetas = define
 `mlk_zetas:int list =
   [--(&1044); --(&758); --(&359); --(&1517); &1493; &1422; &287; &202;
    --(&171); &622; &1577; &182; &962; --(&1202); --(&1474); &1468; &573;
    --(&1325); &264; &383; --(&829); &1458; --(&1602); --(&130); --(&681);
    &1017; &732; &608; --(&1542); &411; --(&205); --(&1571); &1223; &652;
    --(&552); &1015; --(&1293); &1491; --(&282); --(&1544); &516; --(&8);
    --(&320); --(&666); --(&1618); --(&1162); &126; &1469; --(&853);
    --(&90); --(&271); &830; &107; --(&1421); --(&247); --(&951); --(&398);
    &961; --(&1508); --(&725); &448; --(&1065); &677; --(&1275); --(&1103);
    &430; &555; &843; --(&1251); &871; &1550; &105; &422; &587; &177;
    --(&235); --(&291); --(&460); &1574; &1653; --(&246); &778; &1159;
    --(&147); --(&777); &1483; --(&602); &1119; --(&1590); &644; --(&872);
    &349; &418; &329; --(&156); --(&75); &817; &1097; &603; &610; &1322;
    --(&1285); --(&1465); &384; --(&1215); --(&136); &1218; --(&1335);
    --(&874); &220; --(&1187); --(&1659); --(&1185); --(&1530); --(&1278);
    &794; --(&1510); --(&854); --(&870); &478; --(&108); --(&308); &996;
    &991; &958; --(&1460); &1522; &1628]`;;

let mlk_zetas_data =
  let zs = map (fun t -> Num.int_of_num(dest_intconst t))
               (dest_list(rand(concl mlk_zetas))) in
  let bs = Bytes.create (2 * length zs) in
  let _ = List.iteri (fun i z ->
    let m = (z + 65536) mod 65536 in
    Bytes.set bs (2 * i) (Char.chr (m land 255));
    Bytes.set bs (2 * i + 1) (Char.chr (m lsr 8))) zs in
  new_definition(mk_eq(mk_var("mlk_zetas_data",`:byte list`),
                       term_of_bytes bs));;

let MLK_ZETAS_DATA = prove
 (`num_of_bytelist mlk_zetas_data =
   num_of_wordlist (MAP iword mlk_zetas:int16 list)`,
  REWRITE_TAC[mlk_zetas_data; mlk_zetas; MAP] THEN
  REWRITE_TAC[num_of_bytelist; num_of_wordlist] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let LENGTH_MLK_ZETAS_DATA = CONV_RULE (RAND_CONV LENGTH_CONV)
   (AP_TERM `LENGTH:byte list->num` mlk_zetas_data);;

let LENGTH_MLK_ZETAS = CONV_RULE (RAND_CONV LENGTH_CONV)
   (AP_TERM `LENGTH:int list->num` mlk_zetas);;

let MLK_ZETAS_LOADED = prove
 (`!z s. bytes_loaded s (word z) mlk_zetas_data
         ==> !k. k < 128
                 ==> read(memory :> bytes16(word_add (word z) (word(2 * k))))
                     s = iword(EL k mlk_zetas)`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; LENGTH_MLK_ZETAS_DATA;
              MLK_ZETAS_DATA] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word z:int64`; `MAP iword mlk_zetas:int16 list`; `128`;
                 `k:num`; `s:armstate`]
         READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_MLK_ZETAS; ARITH] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC EL_MAP THEN
  ASM_REWRITE_TAC[LENGTH_MLK_ZETAS]);;


(* ------------------------------------------------------------------------- *)
(* Reasoning about 32-bit operations on small numbers, which the compiled    *)
(* code uses for loop counters and indices, and about the flags set when     *)
(* they or pointers with the same base are compared.                         *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_64_32_SMALL = prove
 (`!n. n < 4294967296 ==> word_zx(word n:int64):int32 = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_zx; VAL_WORD; DIMINDEX_64] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let WORD_CMP_32_FLAGS = prove
 (`!x y. x < 4294967296 /\ y < 4294967296
         ==> ((&(val(word x:int32)) - &(val(word y:int32)):int =
               &(val(word_sub (word x) (word y):int32)) <=> y <= x) /\
              (&(val(word x:int32)) - &y:int =
               &(val(word_sub (word x) (word y):int32)) <=> y <= x) /\
              (val(word_sub (word x) (word y):int32) = 0 <=> x = y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word x:int32) = x /\ val(word y:int32) = y`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
  REWRITE_TAC[INT_ARITH `x - y:int = z <=> x = y + z`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ASM_ARITH_TAC);;

let WORD_CMP_64_FLAGS = prove
 (`!x y. x < 18446744073709551616 /\ y < 18446744073709551616
         ==> ((&(val(word x:int64)) - &(val(word y:int64)):int =
               &(val(word_sub (word x) (word y):int64)) <=> y <= x) /\
              (val(word_sub (word x) (word y):int64) = 0 <=> x = y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word x:int64) = x /\ val(word y:int64) = y`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_64] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
  REWRITE_TAC[INT_ARITH `x - y:int = z <=> x = y + z`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ASM_ARITH_TAC);;

(*** Replace 32-bit views of small numbers in assumptions and goal ***)

let W32_SMALL_TAC =
  W(fun (asl,w) ->
    let tms = setify (find_terms
      (can (term_match [] `word_zx(word n:int64):int32`))
      (list_mk_conj(w::map (concl o snd) asl))) in
    MAP_EVERY (fun t ->
      MP_TAC(SPEC (rand(rand t)) WORD_ZX_64_32_SMALL) THEN
      ANTS_TAC THENL
       [SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                             REWRITE_TAC[th])]) tms);;

(*** Decide the carry and zero flags where they are arithmetic facts ***)

let DECIDE_FLAG_TAC p =
  (SUBGOAL_THEN p (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQT_INTRO th])) THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]) ORELSE
  (SUBGOAL_THEN (mk_neg p)
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQF_INTRO th])) THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]);;

let DECIDE_FLAGS_TAC =
  W(fun (asl,w) ->
     let ps = mapfilter (fun (_,th) ->
       let l,r = dest_eq(concl th) in
       let f = rand(rator l) in
       if mem f [`CF`;`ZF`] && not(r = `T` || r = `F`) then r
       else failwith "") asl in
     MAP_EVERY (fun p -> TRY(DECIDE_FLAG_TAC p)) ps);;

(*** Express the flags in terms of the numbers compared and decide them ***)

let CMP_FLAGS_TAC pat th =
  W(fun (asl,w) ->
    let tms = setify (find_terms (can (term_match [] pat))
                                 (list_mk_conj(map (concl o snd) asl))) in
    MAP_EVERY (fun t ->
      let x = rand(lhand t) and y = rand(rand t) in
      MP_TAC(SPECL [x;y] th) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))]) tms) THEN
  DECIDE_FLAGS_TAC;;

let W32_DECIDE_FLAGS_TAC =
  W32_SMALL_TAC THEN
  CMP_FLAGS_TAC `word_sub (word x) (word y):int32` WORD_CMP_32_FLAGS;;

let PTR_DECIDE_FLAGS_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`]) THEN
  CMP_FLAGS_TAC `word_sub (word x) (word y):int64` WORD_CMP_64_FLAGS;;

(*** Prove equations between words formed from small numbers ***)

let MOD_LT_ASM_TAC =
  W(fun (asl,w) ->
    let tms = find_terms
     (fun t -> is_binary "MOD" t && is_numeral(rand t) &&
               not(is_numeral(lhand t))) w in
    let t = hd(sort free_in tms) in
    MP_TAC(SPECL [lhand t; rand t] MOD_LT) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC]);;

let WORD_ADD_LCANCEL_EQ = prove
 (`!a x y:N word. word_add a x = word_add a y <=> x = y`,
  MESON_TAC[WORD_RULE `word_sub (word_add a x) a:N word = x`]);;

let WORD_SMALL_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SUB_CASES; VAL_WORD_ZX_GEN;
              VAL_WORD; VAL_WORD_SHL; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(MOD_LT_ASM_TAC ORELSE
         (COND_CASES_TAC THEN TRY(FIRST_ASSUM(fun th ->
            if is_neg(concl th) then
              (MP_TAC th THEN SIMPLE_ARITH_TAC) else NO_TAC)))) THEN
  SIMPLE_ARITH_TAC;;

(*** The index used in a load with a UXTW register offset ***)

let VAL_WORD_ZX_UXTW = prove
 (`!n. n < 4294967296
       ==> val(word_zx(word_zx(word_zx(word n:int64):int32):int32):int64) =
           n /\
           val(word_zx(word_zx(word n:int64):int32):int64) = n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT MOD_LT_ASM_TAC THEN REWRITE_TAC[]);;

(*** Results of 32-bit sums and differences stored as 16-bit values ***)

let WORD_ZX_ADD_ZX_16 = prove
 (`!(t:int32) (x:int16). word_zx(word_add t (word_zx x)):int16 =
                          word_add (word_zx t) x`,
  BITBLAST_TAC);;

let WORD_ZX_SUB_ZX_16 = prove
 (`!(t:int32) (x:int16). word_zx(word_sub (word_zx x) t):int16 =
                          word_sub x (word_zx t)`,
  BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Use an "ensures" theorem about part of the code to prove a goal with a    *)
(* stronger precondition, weaker postcondition and larger frame.             *)
(* ------------------------------------------------------------------------- *)

let ENSURES_WEAKEN_TAC =
  let pth = prove
   (`!P Q C P' Q' C'.
        ensures step P Q C /\
        (!s. P' s ==> P s) /\ (!s. Q s ==> Q' s) /\ C subsumed C'
        ==> ensures (step:A->A->bool) P' Q' C'`,
    REWRITE_TAC[subsumed] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_PRECONDITION_THM_GEN THEN
    EXISTS_TAC `P:A->bool` THEN EXISTS_TAC `C:A->A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `Q:A->bool` THEN ASM_REWRITE_TAC[]) in
  fun th ->
    match snd(strip_comb(concl th)) with
      [_;p;q;c] -> MATCH_MP_TAC pth THEN MAP_EVERY EXISTS_TAC [p;q;c] THEN
                   CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]
    | _ -> failwith "ENSURES_WEAKEN_TAC";;

(*** Use an events lemma at a point where events have accumulated: given
 *** a goal with precondition including
 ***   exists e2. read events s = APPEND e2 e /\ e2 = X /\
 ***              memaccess_inbounds e2 R W
 *** and a function mk taking the term `APPEND X e` to an instance of the
 *** lemma, with that as its initial events, apply the lemma.
 ***)

let EVENTS_LEMMA_TAC (mk:term->thm) =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  W(fun (asl,w) ->
    let pre = rand(rator(rator w)) in
    let ex = find_term (fun t -> is_exists t &&
                          name_of(fst(dest_exists t)) = "e2") pre in
    let c1,c2,c3 = match conjuncts(snd(dest_exists ex)) with
                     [c1;c2;c3] -> c1,c2,c3
                   | _ -> failwith "EVENTS_LEMMA_TAC" in
    let x = rand c2 and e0 = rand(rand c1) in
    let ib = subst [x,fst(dest_exists ex)] c3 in
    let th = CONV_RULE NUM_REDUCE_CONV (mk (list_mk_icomb "APPEND" [x;e0])) in
    ASM_CASES_TAC ib THENL
     [MP_TAC th THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
        CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
        DISCH_THEN ENSURES_WEAKEN_TAC] THEN
      REPEAT CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
        GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THEN TRY(AP_TERM_TAC THEN ARITH_TAC) THEN
        W(fun (asl,w) ->
          EXISTS_TAC(rand(hd(tl(conjuncts(snd(dest_exists w))))))) THEN
        REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_REWRITE_TAC[GSYM APPEND_ASSOC];
          ONCE_REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[subsumed]];
      REWRITE_TAC[ensures] THEN GEN_TAC THEN REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Congruence and bound propagation, also handling montred_scalar.           *)
(* ------------------------------------------------------------------------- *)

let rec MLKEM_NATIVE_CONGBOUND_RULE lfn tm =
  try apply lfn tm with Failure _ ->
  match tm with
    Comb(Const("montred_scalar",_),t) ->
      let th1 = WEAKEN_INTCONG_RULE (num 3329)
                 (MLKEM_NATIVE_CONGBOUND_RULE lfn t) in
      CONV_RULE(ONCE_DEPTH_CONV INVERSE_MOD_CONV)
       (CONCL_BOUNDS_RULE(SIDE_ELIM_RULE
         (MATCH_MP CONGBOUND_MONTRED_SCALAR th1)))
  | _ -> ASM_CONGBOUND_STEP (MLKEM_NATIVE_CONGBOUND_RULE lfn) tm;;

let rec MLKEM_NATIVE_LOCAL_CONGBOUND_RULE lfn asms =
  match asms with
    [] -> lfn
  | th::ths ->
      let bod,var = dest_eq (concl th) in
      let th1 = MLKEM_NATIVE_CONGBOUND_RULE lfn bod in
      let lfn' = (var |-> SUBS[th] th1) lfn in
      MLKEM_NATIVE_LOCAL_CONGBOUND_RULE lfn' ths;;
