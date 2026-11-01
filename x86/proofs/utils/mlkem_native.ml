(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics shared by the proofs of code compiled from the C       *)
(* implementation in mlkem-native (see x86/mlkem_native/README.md).          *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(* ------------------------------------------------------------------------- *)
(* Normalization of 32-bit and 16-bit arithmetic in the registers.           *)
(* ------------------------------------------------------------------------- *)

(*** Zero extension then truncation, or the reverse ***)

let WORD_ZX_ZX_GEN = prove
 (`!x:M word.
        dimindex(:P) <= dimindex(:N)
        ==> (word_zx:N word->P word) ((word_zx:M word->N word) x) = word_zx x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; MOD_MOD_EXP_MIN] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(*** Reading the 8-bit or 16-bit part of a register ***)

let WORD_VAL_MOD_256 = prove
 (`!x:N word. word (val x MOD 256):byte = word_zx x`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN
  REWRITE_TAC[GSYM DIMINDEX_8; WORD_MOD_SIZE; word_zx]);;

let WORD_VAL_MOD_65536 = prove
 (`!x:N word. word (val x MOD 65536):int16 = word_zx x`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `65536 = 2 EXP 16`] THEN
  REWRITE_TAC[GSYM DIMINDEX_16; WORD_MOD_SIZE; word_zx]);;

(*** The 16-bit part of a register after writing it ***)

let WORD_ZX_JOIN_48_16 = prove
 (`!(h:48 word) (l:int16). word_zx(word_join h l:int64):int16 = l`,
  BITBLAST_TAC);;

(*** Simplify the results of such arithmetic as stored by the simulator ***)

let MLKEM_NATIVE_WORD_SIMP_TAC =
  REWRITE_TAC[WORD_VAL_MOD_256; WORD_VAL_MOD_65536; WORD_ADD; WORD_MUL;
              WORD_VAL] THEN
  SIMP_TAC[WORD_ZX_ZX_GEN; WORD_ZX_TRIVIAL; DIMINDEX_8; DIMINDEX_16;
           DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  REWRITE_TAC[WORD_ZX_JOIN_48_16];;

(*** Cancellation of a common base address ***)

let WORD_ADD_LCANCEL_EQ = prove
 (`!a x y:N word. word_add a x = word_add a y <=> x = y`,
  MESON_TAC[WORD_RULE `word_sub (word_add a x) a:N word = x`]);;

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

(*** The Barrett reduction as compiled for x86, multiplying the bottom 16
 *** bits of the quotient by -3329 = 62207 in a 16-bit register
 ***)

let BARRED_GCC12_O2 = prove
 (`!x:int16.
     word_add x
      (word_mul (word_zx (word_ishr (word_add (word_mul (word_sx x)
                                                         (word 20159))
                                             (word 33554432)) 26:int32))
                (word 62207)):int16 =
     barred x`,
  GEN_TAC THEN REWRITE_TAC[GSYM BARRED_SCALAR] THEN
  SIMP_TAC[WORD_ZX_ADD; WORD_ZX_MUL; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
  REWRITE_TAC[ISPECL [`word_mul (word_sx (x:int16)) (word 20159):int32`;
                      `word 33554432:int32`] WORD_ADD_SYM] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN BITBLAST_TAC);;

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
 (`!a:int64 (l:int16 list) n j s:x86state.
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
 (`!x:int64 n s:x86state.
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
(* The same Montgomery reduction in the form compiled for x86, multiplying   *)
(* the bottom 16 bits by 62209 = 3329^-1 in a 16-bit register.               *)
(* ------------------------------------------------------------------------- *)

let montred_x86 = define
 `montred_x86 (t:int32):int16 =
  word_zx(word_ishr
   (word_add
     (word_mul (word_sx (word_mul (word_zx t:int16) (word 62209)):int32)
               (word 4294963967))
     t)
   16)`;;

let MONTRED_X86_SCALAR = prove
 (`!t:int32. montred_x86 t = montred_scalar t`,
  GEN_TAC THEN
  REWRITE_TAC[montred_x86; montred_scalar; SXFROM_15_SUBWORD] THEN
  SIMP_TAC[WORD_ZX_MUL; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_SYM]);;

(*** A 32-bit product formed from the 16-bit high and low halves given by
 *** PMULHW and PMULLW
 ***)

let WORD_JOIN_MULHI_MULLO = prove
 (`!a b:int16.
     word_join (word_subword (word_mul (word_sx a) (word_sx b):int32)
                             (16,16):int16)
               (word_mul a b:int16):int32 =
     word_mul (word_sx a) (word_sx b)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `word_mul a b:int16 = word_zx(word_mul (word_sx a) (word_sx b):int32)`
  SUBST1_TAC THENL
   [SIMP_TAC[WORD_ZX_MUL; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
    REWRITE_TAC[WORD_BLAST `word_zx(word_sx (x:int16):int32) = x`];
    SPEC_TAC(`word_mul (word_sx a) (word_sx b):int32`,`p:int32`) THEN
    BITBLAST_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Splitting off the 8 coefficients handled by one iteration of a loop that  *)
(* the compiler has vectorized.                                              *)
(* ------------------------------------------------------------------------- *)

let CHUNK8_INPUT_SPLIT = prove
 (`!P i. i < 32
         ==> ((!j. 8 * i <= j /\ j < 256 ==> P j) <=>
              (!j. 8 * (i + 1) <= j /\ j < 256 ==> P j) /\
              (!k. k < 8 ==> P(8 * i + k)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `8 * (i + 1) <= j` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - 8 * i`) THEN
    ASM_SIMP_TAC[ARITH_RULE `8 * i <= j ==> 8 * i + (j - 8 * i) = j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let CHUNK8_OUTPUT_SPLIT = prove
 (`!P i. (!j. j < 8 * (i + 1) ==> P j) <=>
         (!j. j < 8 * i ==> P j) /\ (!k. k < 8 ==> P(8 * i + k))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `j < 8 * i` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - 8 * i`) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(j < 8 * i) ==> 8 * i + (j - 8 * i) = j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let CHUNK8_ADDR = prove
 (`!a i k. word_add a (word(2 * (8 * i + k))):int64 =
           word_add (word_add a (word(16 * i))) (word(2 * k))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The table of zetas used by the C code, as the values in the source code   *)
(* and as the bytes of the read-only data in the compiled code. The latter   *)
(* is defined here so that it can be shared by several proofs; the proofs    *)
(* still check that it is the same as the data in their object files, since  *)
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
                 `k:num`; `s:x86state`]
         READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_MLK_ZETAS; ARITH] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC EL_MAP THEN
  ASM_REWRITE_TAC[LENGTH_MLK_ZETAS]);;

(* ------------------------------------------------------------------------- *)
(* Instantiating a quantified fact about memory at the address that the      *)
(* simulation computes from the registers, which for indexed addressing is   *)
(* not in the same form as in the fact.                                      *)
(* ------------------------------------------------------------------------- *)

let READ_INSTANCE_TAC tm =
  let l,r = dest_eq tm in
  let tryth th =
    let avs,bod = strip_forall(concl th) in
    let eq = if is_imp bod then rand bod else bod in
    if not (is_eq eq) then failwith "READ_INSTANCE_TAC" else
    let i = term_match (frees(concl th)) (rhs eq) r in
    let th1 = INSTANTIATE i (SPECL avs th) in
    MP_TAC th1 THEN
    (if is_imp(concl th1) then
       ANTS_TAC THENL
        [ARITH_TAC ORELSE
         (FIRST_ASSUM(MP_TAC o check
            (can (term_match [] `(i:num) < n`) o concl)) THEN ARITH_TAC) ORELSE
         ASM_ARITH_TAC;
         ALL_TAC]
     else ALL_TAC) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN
    (CONV_TAC WORD_RULE ORELSE
     (REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC) ORELSE
     (REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC)) in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> tryth th); ALL_TAC];;

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

(* ------------------------------------------------------------------------- *)
(* Reading a 128-bit vector of constants from loaded read-only data, and     *)
(* the XMM registers as parts of the YMM registers.                          *)
(* ------------------------------------------------------------------------- *)

let BYTES_LOADED_BYTES128 = prove
 (`!a l k s.
        bytes_loaded s a l /\ k + 16 <= LENGTH l
        ==> read (memory :> bytes128(word_add a (word k))) s =
            word((num_of_bytelist l DIV 2 EXP (8 * k)) MOD 2 EXP 128)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[bytes128; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  REWRITE_TAC[READ_BYTES_DIV; ARITH_RULE `2 EXP 128 = 2 EXP (8 * 16)`;
              READ_BYTES_MOD] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let XMM_EXISTSTOP = prove
 (`!c s:S. read (c :> zerotop_128) s = l
           ==> ?h. read c s = (word_join:int128->int128->int256) h l`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  EXISTS_TAC `word_subword (read c (s:S):int256) (128,128):int128` THEN
  REWRITE_TAC[READ_ZEROTOP_128] THEN CONV_TAC WORD_BLAST);;

let XMM_EXISTSTOP_RULE =
  REWRITE_RULE (map GSYM
   [XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7;
    XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15]) o
  C ISPEC XMM_EXISTSTOP;;

let XMM_EXISTSTOP_TAC top y =
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (XMM_EXISTSTOP_RULE y)) THEN
  DISCH_THEN(X_CHOOSE_TAC(mk_var(top,`:int128`)));;

(* ------------------------------------------------------------------------- *)
(* Folding the address of a RIP-relative operand of the instruction ending   *)
(* at pc + ofs, given as data - (pc + c) in the relocated code, to data + k. *)
(* ------------------------------------------------------------------------- *)

let RIPREL_FOLD = prove
 (`!pc ofs data c k.
     riprel32_within_bounds (data + k) (pc + ofs) /\ &ofs - c = &k
     ==> word (val (word (pc + ofs):int64) +
               val (word_sx (iword (&data - (&pc + c)):int32):int64)):int64 =
         word (data + k)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP WORD32_ADD_SUB_OF_LT) THEN
  REWRITE_TAC[word_add; modular] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN ASM_INT_ARITH_TAC);;

let RIPREL_FOLD_TAC data ofs c k =
  MP_TAC(SPECL [`pc:num`; ofs; data; c; k] RIPREL_FOLD) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; DISCH_TAC];;
