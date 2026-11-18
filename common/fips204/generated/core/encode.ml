(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Equivalence of the generated and the handwritten FIPS 204 encodings:      *)
(* the bit and byte conversions (FIPS 204 Algorithms 9-13), the bit          *)
(* packings SimpleBitPack/BitPack and SimpleBitUnpack/BitUnpack (Algorithms  *)
(* 16-19) and the key and commitment encodings pkEncode, pkDecode,           *)
(* skEncode, skDecode and w1Encode (Algorithms 22-25 and 28).                *)
(*                                                                           *)
(* The handwritten specification has no bit strings: a packing of fields of  *)
(* c bits is the byte string mldsa_encode c n f, read back by mldsa_field.   *)
(* The generated code goes through bit strings (bool list), so this file     *)
(* first relates a bit string to the number it represents (enc_num_of_bits   *)
(* and its inverse enc_bits_of_num), then expresses each generated           *)
(* conversion by that number, and finally identifies the numbers with the    *)
(* digit sums of mldsa_encode and mldsa_field.                               *)
(*                                                                           *)
(* SUMMARY (everything below is proved, no cheating tactics):                *)
(*                                                                           *)
(*   Needs core.ml and ball.ml, whose generators and tactics it reuses       *)
(*   (ball_bytes_to_bits_gen, ball_bitunpack_gen, BALL_SIMP_TAC,             *)
(*   BALL_FOLDL_TAC).                                                        *)
(*                                                                           *)
(*   Bits and bytes: BITLEN_EQ_MLDSA_BITLEN (bitlen n = mldsa_bitlen n);     *)
(*   ENC_BITSTOBYTES_8 and ENC_BITSTOBYTES_STRING (BitsToBytesString_hol of  *)
(*   bits_of_bytes B is Value B); ENC_BYTES_TO_BITS_N for N in {34, 96,      *)
(*   128, 320, 416} (BytesToBits_N z = Value (bits_of_bytes z) for LENGTH z  *)
(*   = N; N in {1, 66, 576, 640} are BALL_BYTES_TO_BITS_N of ball.ml) and    *)
(*   ENC_BYTES_TO_BITS_STRING (an alias of the ball.ml theorem);             *)
(*   ENC_INTEGER_TO_BITS_c for c in {3,4,6,10,13,18,20}.                     *)
(*   Not done here: IntegerToBytes_1/2 (ball.ml has INTEGER_TO_BYTES_2_NUM),*)
(*   the scalar conversions CoefficientToInteger, IntegerIdentity,           *)
(*   NonnegativeInteger, BitToInteger, IntegerToBitModulo, BitsToInteger     *)
(*   (BALL_BITS_TO_INTEGER covers BitsToInteger).                            *)
(*                                                                           *)
(*   Packing, hypotheses on 0 <= j < 256 only:                               *)
(*     ENC_BITPACK_{2,4,4095,131071,524287}: BitPack_a_b_hol (lift_intpoly w)*)
(*       (&a) (&b) = Value (mldsa_encode c 256 (\j. &b - w j)) if            *)
(*       --(&a) <= w j <= &b (c = 3, 4, 13, 18, 20);                         *)
(*     ENC_SIMPLEBITPACK_{15,43,1023}: SimpleBitPack_b_hol (lift_intpoly w)  *)
(*       (&b) = Value (mldsa_encode c 256 w) if 0 <= w j <= b (c = 4, 6, 10).*)
(*   Unpacking, LENGTH v = 32 * c:                                           *)
(*     ENC_BITUNPACK_{2,4,4095,131071,524287} (the last two are aliases of   *)
(*     BALL_BITUNPACK_N): BitUnpack_a_b_hol v (&a) (&b)                      *)
(*       = Value (lift_intpoly (\i. &b - mldsa_field c v i));                *)
(*     ENC_SIMPLEBITUNPACK_1023 (c = 10, no b - ...).                        *)
(*   (sigcodec.ml restates 131071 and 524287 in the form of hints_bitpack_hyp    *)
(*   and hints_bitunpack_hyp, and checks that they agree.)                   *)
(*                                                                           *)
(*   Vectors: a vector is given as t i j (row i < k, coefficient j < 256) as *)
(*   in hints.ml, lifted by lift_vec (\i. lift_intpoly (t i)), flat form     *)
(*   (\n. t (n DIV 256) (n MOD 256)):                                        *)
(*     EQ_PKENCODE_MLDSA{44,65,87}   (LENGTH rho = 32, 0 <= t i j <= 1023)   *)
(*     EQ_W1ENCODE_MLDSA{44,65,87}   (0 <= w i j <= 43 resp. 15)             *)
(*     EQ_SKENCODE_MLDSA{44,65,87}   (LENGTH rho = 32, K = 32, tr = 64;      *)
(*        -eta <= s1, s2 <= eta; -4095 <= t0 <= 4096)                        *)
(*     EQ_PKDECODE_MLDSA{44,65,87}   (LENGTH pk = 32 + 320 * k)              *)
(*     EQ_SKDECODE_MLDSA{44,65,87}   (LENGTH sk = 128 + 32*c*(l+k)+416*k)    *)
(*     EQ_DECODEDPUBLICKEYSTRINGS_MLDSA{44,65,87}                            *)
(*     EQ_DECODEDSECRETKEYSTRINGS_MLDSA{44,65,87}                            *)
(*   skDecode states the slices as numerals (mldsa_slice 128 384 sk etc.);   *)
(*   the handwritten mldsa_sign_mu uses 128 + 32 * c * l with c = mldsa_bitlen*)
(*   (2 * eta), which NUM_REDUCE_CONV and MLDSA_BITLEN_CLAUSES reduce.       *)
(*                                                                           *)
(*   Helpers worth reusing: ENC_FOLDL_INV and ENC_FOLDL_TAC (invariant for a *)
(*   loop over list_of_seq (\i. &i) n), MLDSA_ENCODE_APPEND and              *)
(*   ENC_ENCODE_VEC_STEP (mldsa_encode of blocks), ENC_FIELD_SLICE (field of *)
(*   a slice vs. field of its block), ENC_SLICE_NORM_TAC (typed_hol_list_    *)
(*   slice with bounds linear in k).                                         *)
(* ========================================================================= *)

needs "common/fips204/generated/core/common.ml";;
needs "common/fips204/generated/core/core.ml";;
needs "common/fips204/generated/core/ball.ml";;

(* ------------------------------------------------------------------------- *)
(* The monad: native_bind on each result, its associativity, and             *)
(* native_foldl over an appended index list.                                 *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* The counted loops: the schedule of a loop with step 8 (which BitsToBytes  *)
(* uses) is the list of its indices, and a loop whose body succeeds for      *)
(* every index is the iteration enc_fold of the body on the accumulator.     *)
(* ------------------------------------------------------------------------- *)

let ENC_SCHEDULE_8 = prove
 (`!k j m. m <= 8 * j + 8 * k
           ==> native_schedule k (\i:int. int_lt i (&m)) (\i. int_add i (&8))
                                (&(8 * j)) =
               list_of_seq (\i. &(8 * (j + i))) ((m + 7) DIV 8 - j)`,
  INDUCT_TAC THENL
   [SIMP_TAC[ARITH_RULE `m <= 8 * j + 8 * 0 ==> (m + 7) DIV 8 - j = 0`;
             list_of_seq; native_schedule_DEF];
    REPEAT STRIP_TAC THEN REWRITE_TAC[native_schedule_DEF] THEN
    REWRITE_TAC[INT_OF_NUM_LT] THEN COND_CASES_TAC THENL
     [SUBGOAL_THEN `(m + 7) DIV 8 - j = SUC((m + 7) DIV 8 - (j + 1))`
      SUBST1_TAC THENL
       [MP_TAC(SPEC `m:num` (MATCH_MP DIVISION (ARITH_RULE `~(8 = 0)`))) THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(&(8 * j) + &8:int) = &(8 * (j + 1))` SUBST1_TAC THENL
       [REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`j + 1`; `m:num`] th)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[LIST_OF_SEQ; o_DEF; ADD_CLAUSES] THEN
      REWRITE_TAC[ARITH_RULE `8 * SUC(j + x) = 8 * ((j + 1) + x)`];
      SUBGOAL_THEN `(m + 7) DIV 8 - j = 0` SUBST1_TAC THENL
       [MP_TAC(SPEC `m:num` (MATCH_MP DIVISION (ARITH_RULE `~(8 = 0)`))) THEN
        ASM_ARITH_TAC;
        REWRITE_TAC[list_of_seq]]]]);;

let enc_fold = define
 `(!(g:num->A->A) s. enc_fold g 0 s = s) /\
  (!(g:num->A->A) n s. enc_fold g (SUC n) s = g n (enc_fold g n s))`;;

(* ------------------------------------------------------------------------- *)
(* The list and scalar primitives of the generated code.                     *)
(* ------------------------------------------------------------------------- *)

let ENC_BIT_VALUE = prove
 (`!b. typed_hol_bit_value b = Value(&(bitval b))`,
  REWRITE_TAC[typed_hol_bit_value_DEF; bitval] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV);;

let ENC_SEQUENCE_EXTENT = prove
 (`!n (l:A list).
        typed_hol_sequence_extent n l =
        if LENGTH l = n then Value l else Fault Bounds_Error`,
  REWRITE_TAC[typed_hol_sequence_extent_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Bit strings and the numbers they stand for.                               *)
(* ------------------------------------------------------------------------- *)

let enc_num_of_bits = define
 `enc_num_of_bits [] = 0 /\
  (!b t. enc_num_of_bits (CONS b t) = bitval b + 2 * enc_num_of_bits t)`;;

let enc_bits_of_num = define
 `(!n. enc_bits_of_num 0 n = []) /\
  (!c n. enc_bits_of_num (SUC c) n =
         CONS (ODD n) (enc_bits_of_num c (n DIV 2)))`;;

let ENC_MLDSA_BITLEN_BOUNDS = prove
 (`!m. ~(m = 0) ==> m < 2 EXP (mldsa_bitlen m) /\
                    2 EXP (mldsa_bitlen m) <= 2 * m`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE(BETA_RULE(ISPEC `\c. m < 2 EXP c` MINIMAL)))) THEN
  ANTS_TAC THENL [EXISTS_TAC `m:num` THEN REWRITE_TAC[LT_POW2_REFL]; ALL_TAC] THEN
  REWRITE_TAC[GSYM mldsa_bitlen] THEN
  ABBREV_TAC `k = mldsa_bitlen m` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k - 1`) THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN FIRST_X_ASSUM MP_TAC THEN
    REWRITE_TAC[EXP] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP k = 2 * 2 EXP (k - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ARITH_TAC]);;

let BITLEN_EQ_MLDSA_BITLEN = prove
 (`!n. bitlen n = mldsa_bitlen n`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[MLDSA_BITLEN_0] THEN ONCE_REWRITE_TAC[bitlen_DEF] THEN REWRITE_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[bitlen_DEF] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n DIV 2 < n` ASSUME_TAC THENL
   [MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN
  REWRITE_TAC[ARITH_RULE `~(2 = 0)`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `n DIV 2 = 0` THENL
   [SUBGOAL_THEN `n = 1` SUBST_ALL_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 DIV 2 = 0`; MLDSA_BITLEN_0] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MLDSA_BITLEN_UNIQUE THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ENC_MLDSA_BITLEN_BOUNDS) THEN
  ABBREV_TAC `m = n DIV 2` THEN ABBREV_TAC `k = mldsa_bitlen m` THEN
  STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MLDSA_BITLEN_UNIQUE THEN
  REWRITE_TAC[EXP] THEN ASM_ARITH_TAC);;

(* ========================================================================= *)
(* Part 2: BitsToBytes, IntegerToBits and BitPack (uses core.ml, ball.ml).   *)
(* ========================================================================= *)

let ENC_FOLDL_INV = prove
 (`!(body:int->S->(S)native_result) n (P:num->S->bool) s.
        P 0 s /\
        (!k s. k < n /\ P k s
               ==> ?s'. body (&k) s = Value s' /\ P (SUC k) s')
        ==> ?s'. native_foldl body (list_of_seq (\i. &i) n) s = Value s' /\
                 P n s'`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[list_of_seq; native_foldl_DEF] THEN
    EXISTS_TAC `s:S` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[list_of_seq; NATIVE_FOLDL_APPEND] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`P:num->S->bool`; `s:S`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[LT]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:S` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[NATIVE_BIND; native_foldl_DEF] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s1:S`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LT_SUC_LE; LE_REFL]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s2:S` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[NATIVE_BIND; native_foldl_DEF] THEN
    EXISTS_TAC `s2:S` THEN ASM_REWRITE_TAC[]]);;

let ENC_LIST_OF_SEQ_CONV =
  let rec conv tm =
    if rand tm = `0` then REWR_CONV (CONJUNCT1 list_of_seq) tm
    else (RAND_CONV num_CONV THENC REWR_CONV(CONJUNCT2 list_of_seq) THENC
          LAND_CONV conv) tm in
  conv THENC DEPTH_CONV BETA_CONV THENC REWRITE_CONV[APPEND];;

let ENC_LIST8 = prove
 (`[&0:int; &1; &2; &3; &4; &5; &6; &7] = list_of_seq (\i. &i) 8`,
  CONV_TAC(RAND_CONV ENC_LIST_OF_SEQ_CONV) THEN REFL_TAC);;

let ENC_MOD_SUC_AUX = prove
 (`!a q2 t r. t < 2 /\ r < a
              ==> ((q2 * 2 + t) * a + r) MOD (2 * a) = r + t * a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q2:num` THEN
  SUBGOAL_THEN `t = 0 \/ t = 1` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES; ADD_CLAUSES; MULT_ASSOC] THEN
  TRY ARITH_TAC THEN ASM_ARITH_TAC);;

let ENC_MOD_SUC = prove
 (`!v k. v MOD 2 EXP (SUC k) =
         v MOD 2 EXP k + (if ODD(v DIV 2 EXP k) then 2 EXP k else 0)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `2 EXP (SUC k) = 2 * 2 EXP k` SUBST1_TAC THENL
   [REWRITE_TAC[EXP]; ALL_TAC] THEN
  SUBGOAL_THEN `~(2 EXP k = 0)` MP_TAC THENL
   [REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  SPEC_TAC(`2 EXP k`,`a:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`v:num`; `a:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`v DIV a`; `2`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  SUBGOAL_THEN `ODD(v DIV a) <=> (v DIV a) MOD 2 = 1` SUBST1_TAC THENL
   [REWRITE_TAC[ODD_MOD]; ALL_TAC] THEN
  SPEC_TAC(`(v DIV a) DIV 2`,`q2:num`) THEN
  SPEC_TAC(`(v DIV a) MOD 2`,`t:num`) THEN
  SPEC_TAC(`v MOD a`,`r:num`) THEN
  SPEC_TAC(`v DIV a`,`q:num`) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`a:num`; `q2:num`; `t:num`; `r:num`] ENC_MOD_SUC_AUX) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `t = 0 \/ t = 1` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  ARITH_TAC);;

(* Like BALL_FOLDL_TAC for a loop over list_of_seq (\i. &i) n.               *)
let ENC_FOLDL_TAC ptm fname : tactic =
  fun (asl,w) ->
    let is_foldl t =
      match strip_comb t with
        (c,[_;_;_]) -> is_const c && fst(dest_const c) = "native_foldl"
      | _ -> false in
    let tm = find_term is_foldl w in
    let body,sched,s0 = match snd(strip_comb tm) with
        [x;y;z] -> x,y,z | _ -> failwith "ENC_FOLDL_TAC" in
    let n = rand sched in
    let th = ISPECL [body; n; ptm; s0] ENC_FOLDL_INV in
    let sty = type_of s0 in
    let svar = mk_var(fname, sty) in
    (MP_TAC th THEN
     ANTS_TAC THENL
      [CONV_TAC(DEPTH_CONV BETA_CONV);
       DISCH_THEN(X_CHOOSE_THEN svar
           (CONJUNCTS_THEN2 SUBST1_TAC (ASSUME_TAC o BETA_RULE))) THEN
       REWRITE_TAC[NATIVE_BIND]]) (asl,w);;

g `!b:byte. BitsToBytes_8_hol (list_of_seq (\j. bit j b) 8) = Value [b]`;;
e(GEN_TAC THEN REWRITE_TAC[BitsToBytes_8_hol_DEF; ENC_LIST8] THEN
  BALL_SIMP_TAC[TYPED_HOL_INT_TO_BYTE_NUM; REPLICATE_ONE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[NATIVE_BIND]);;
e(ENC_FOLDL_TAC `\k (w:byte list). w = [word (val (b:byte) MOD 2 EXP k):byte]` "st" THENL
  [CONJ_TAC THENL [REWRITE_TAC[EXP; MOD_1]; ALL_TAC] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   SUBGOAL_THEN `k DIV 8 = 0 /\ k MOD 8 = k` STRIP_ASSUME_TAC THENL
    [ASM_SIMP_TAC[DIV_LT; MOD_LT]; ALL_TAC] THEN
   REWRITE_TAC[BALL_ISA_INT_NUM] THEN ASM_REWRITE_TAC[] THEN
   BALL_SIMP_TAC[LENGTH; ARITH_RULE `0 < 1`; NATIVE_LIST_INDEX_NUM; EL; HD] THEN
   ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
   MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
   DISCH_TAC THEN
   SUBGOAL_THEN `val(b:byte) MOD 2 EXP k < 256 /\
                 val(b:byte) MOD 2 EXP SUC k < 256 /\
                 val(b:byte) MOD 2 EXP k +
                 bitval(ODD(val(b:byte) DIV 2 EXP k)) * 2 EXP k =
                 val(b:byte) MOD 2 EXP SUC k` STRIP_ASSUME_TAC THENL
    [REPEAT CONJ_TAC THENL
      [MP_TAC(SPECL [`val(b:byte)`; `2 EXP k`] MOD_LE) THEN ASM_ARITH_TAC;
       MP_TAC(SPECL [`val(b:byte)`; `2 EXP SUC k`] MOD_LE) THEN
       ASM_ARITH_TAC;
       REWRITE_TAC[ENC_MOD_SUC; bitval] THEN
       COND_CASES_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]];
     ALL_TAC] THEN
   ASM_SIMP_TAC[TYPED_HOL_BYTE_VALUE; VAL_WORD; DIMINDEX_8; MOD_LT; BIT_VAL;
                TYPED_HOL_READ; NATIVE_BIND; ENC_BIT_VALUE; BALL_INT_ARITH] THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   ASM_SIMP_TAC[EL_LIST_OF_SEQ; MOD_LT; ARITH_RULE `2 EXP 8 = 256`] THEN
   REWRITE_TAC[GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_MUL;
               GSYM INT_OF_NUM_ADD] THEN
   ASM_REWRITE_TAC[] THEN REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_MUL; INT_OF_NUM_ADD] THEN
   REWRITE_TAC[TYPED_HOL_INT_TO_BYTE_NUM; NATIVE_BIND] THEN
   ASM_REWRITE_TAC[NATIVE_BIND; LENGTH_ISA_LIST_UPDATE; isa_list_update;
                   injectivity "native_result"; UNWIND_THM1] THEN
   ALL_TAC;
   ALL_TAC]);;
e(ASM_REWRITE_TAC[injectivity "native_result"; ARITH_RULE `2 EXP 8 = 256`;
                  CONS_11; NOT_CONS_NIL] THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT; WORD_VAL]);;
let ENC_BITSTOBYTES_8 = top_thm();;

let ENC_FOLDL_ACC8 = prove
 (`!(body:int->S->(S)native_result) (g:num->S->S) m s.
        (!i t. i < m ==> body (&(8 * i)) t = Value(g i t))
        ==> native_foldl body (list_of_seq (\i. &(8 * i)) m) s =
            Value(enc_fold g m s)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`s:S`,`s:S`) THEN SPEC_TAC(`m:num`,`m:num`) THEN
  INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; native_foldl_DEF; enc_fold] THEN
  REWRITE_TAC[NATIVE_FOLDL_APPEND] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `s:S` th)) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `i < m ==> i < SUC m`];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[NATIVE_BIND; native_foldl_DEF;
               ARITH_RULE `m < SUC m`]);;

let ENC_SCHEDULE_OUTER = prove
 (`!n. native_schedule (SUC (8 * n)) (\i:int. int_lt i (&(8 * n)))
         (\i. int_add i (&8)) (&0) = list_of_seq (\i. &(8 * i)) n`,
  GEN_TAC THEN
  MP_TAC(SPECL [`SUC (8 * n)`; `0`; `8 * n`] ENC_SCHEDULE_8) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(8 * n + 7) DIV 8 = n` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `7` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUB_0]);;

g `!(B:byte list) m. m < LENGTH B
       ==> native_foldl
            (\j block.
              if &(8 * m) + j < &(8 * LENGTH B)
              then native_bind
                    (typed_hol_read
                      (native_list_index (bits_of_bytes B) (&(8 * m) + j)))
                    (\vl. typed_hol_read (native_list_update block j vl))
              else Value block)
            (native_schedule 9 (\j. j < &8) (\j. j + &1) (&0))
            (REPLICATE 8 F) =
           Value (list_of_seq (\j. bit j (EL m B)) 8)`;;
e(REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`9`; `8`] NATIVE_SCHEDULE_NUM) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ENC_FOLDL_TAC `\k (blk:bool list). blk =
     list_of_seq (\j. if j < k then bit j (EL m (B:byte list)) else F) 8`
   "st" THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[REPLICATE_LIST_OF_SEQ; CONJUNCT1 LT]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `8 * m + k < 8 * LENGTH(B:byte list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_LT; NATIVE_LIST_INDEX_NUM; TYPED_HOL_READ;
                    NATIVE_BIND; NATIVE_LIST_UPDATE_NUM; LENGTH_LIST_OF_SEQ;
                    LENGTH_BITS_OF_BYTES] THEN
    ASM_SIMP_TAC[BALL_EL_BITS_OF_BYTES_BIT; BALL_DIV_MOD_8] THEN
    REWRITE_TAC[injectivity "native_result"; UNWIND_THM1;
                ISA_LIST_UPDATE_LIST_OF_SEQ] THEN
    MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[LT] THEN ASM_CASES_TAC `j:num = k` THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[LT];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[injectivity "native_result"] THEN
    MATCH_MP_TAC LIST_OF_SEQ_EQ THEN SIMP_TAC[]]);;
let ENC_BTB_INNER = top_thm();;

let ENC_ACC8_TAC gtm : tactic =
  fun (asl,w) ->
    let is_foldl t =
      match strip_comb t with
        (c,[_;_;_]) -> is_const c && fst(dest_const c) = "native_foldl"
      | _ -> false in
    let tm = lhand w in
    let body,sched,s0 = match snd(strip_comb tm) with
        [x;y;z] -> x,y,z | _ -> failwith "ENC_ACC8_TAC" in
    let n = rand sched in
    let th = ISPECL [body; gtm; n; s0] ENC_FOLDL_ACC8 in
    (MP_TAC th THEN ANTS_TAC THENL
      [CONV_TAC(DEPTH_CONV BETA_CONV); DISCH_THEN SUBST1_TAC]) (asl,w);;

let ENC_ENC_FOLD_LIST = prove
 (`!(B:byte list) k. enc_fold (\i y. APPEND y [EL i B]) k [] =
                     list_of_seq (\i. EL i B) k`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[enc_fold; list_of_seq]);;

g `!B:byte list. BitsToBytesString_hol (bits_of_bytes B) = Value B`;;
e(GEN_TAC THEN REWRITE_TAC[BitsToBytesString_hol_DEF] THEN
  BALL_SIMP_TAC[LENGTH_BITS_OF_BYTES; INT_OF_NUM_MUL; TYPED_HOL_INT_TO_BIT_NUM;
                ARITH_RULE `0 < 2`; REPLICATE_ONE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ENC_SCHEDULE_OUTER] THEN
  ENC_ACC8_TAC `\i y. APPEND y [EL i (B:byte list)]`);;
e(REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ENC_BTB_INNER; NATIVE_BIND; ENC_BITSTOBYTES_8] THEN
  SUBGOAL_THEN `0 <= 1 /\ 1 <= LENGTH [EL i (B:byte list)]` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[BALL_SLICE; TYPED_HOL_READ; NATIVE_BIND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BALL_LIST_OF_SEQ_1; ADD_CLAUSES; EL; HD]);;
e(REWRITE_TAC[ENC_ENC_FOLD_LIST; injectivity "native_result"] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM LIST_OF_SEQ_EQ_SELF] THEN REFL_TAC);;
let ENC_BITSTOBYTES_STRING = top_thm();;


let enc_int_to_bits_gen c def =
  let sc = string_of_int c in
  let goal = parse_term
   ("!n. IntegerToBits_" ^ sc ^ "_hol (&n) (&" ^ sc ^
    ") = Value (list_of_seq (\\i. ODD(n DIV 2 EXP i)) " ^ sc ^ ")") in
  let inv = parse_term
   ("\\k (s:bool list # int). s = (list_of_seq (\\j. if j < k then " ^
    "ODD(n DIV 2 EXP j) else F) " ^ sc ^ ", &(n DIV 2 EXP k))") in
  let sch = SPECL [parse_term("SUC " ^ sc); parse_term sc] NATIVE_SCHEDULE_NUM in
  prove(goal,
    GEN_TAC THEN REWRITE_TAC[def] THEN
    BALL_SIMP_TAC[ISA_NAT_NUM] THEN
    CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN REWRITE_TAC[ISA_NAT_NUM] THEN
    MP_TAC sch THEN ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ENC_FOLDL_TAC inv "st" THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[CONJUNCT1 LT; EXP; DIV_1; REPLICATE_LIST_OF_SEQ]; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[UNCURRY_DEF; BALL_ISA_INT_NUM; TYPED_HOL_INT_TO_BIT_NUM;
                  MOD_LT_EQ; ARITH_EQ; NATIVE_BIND; NATIVE_LIST_UPDATE_NUM;
                  LENGTH_LIST_OF_SEQ; BALL_INT_ARITH] THEN
      ASM_REWRITE_TAC[TYPED_HOL_READ; NATIVE_BIND; ISA_LIST_UPDATE_LIST_OF_SEQ;
                      injectivity "native_result"; UNWIND_THM1;
                      PAIR_EQ] THEN
      REWRITE_TAC[ARITH_EQ] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `j:num` THEN
        DISCH_TAC THEN REWRITE_TAC[LT] THEN
        ASM_CASES_TAC `j:num = k` THEN ASM_REWRITE_TAC[ODD_MOD] THEN
        ASM_REWRITE_TAC[LT];
        REWRITE_TAC[EXP; DIV_DIV; MULT_SYM]];
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[UNCURRY_DEF; injectivity "native_result"] THEN
      MATCH_MP_TAC LIST_OF_SEQ_EQ THEN SIMP_TAC[]]);;

let ENC_INTEGER_TO_BITS_18 = enc_int_to_bits_gen 18 IntegerToBits_18_hol_DEF;;

let ENC_ODD_MOD_EXP = prove
 (`!q r c. r < c
           ==> (ODD((q MOD 2 EXP c) DIV 2 EXP r) <=> ODD(q DIV 2 EXP r))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP c = 2 EXP r * 2 EXP (c - r)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_MOD] THEN
  REWRITE_TAC[ODD_MOD; MOD_MOD_EXP_MIN] THEN
  SUBGOAL_THEN `~(c - r = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(q DIV 2 EXP r) MOD 2 EXP (c - r) MOD 2 =
                (q DIV 2 EXP r) MOD 2` (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(SPECL [`q DIV 2 EXP r`; `2`; `c - r`; `1`] MOD_MOD_EXP_MIN) THEN
  REWRITE_TAC[EXP_1] THEN
  SUBGOAL_THEN `MIN (c - r) 1 = 1` (fun th -> REWRITE_TAC[th; EXP_1]) THEN
  ASM_ARITH_TAC);;

let ENC_EL_BITS_FIELD = prove
 (`!c (B:byte list) i r.
        r < c /\ c * i + r < 8 * LENGTH B
        ==> (EL (c * i + r) (bits_of_bytes B) <=>
             ODD(((num_of_bytelist B DIV 2 EXP (c * i)) MOD 2 EXP c)
                 DIV 2 EXP r))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BALL_EL_BITS_OF_BYTES] THEN
  ASM_SIMP_TAC[ENC_ODD_MOD_EXP] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV]);;

let ENC_BITZEROS_0 = prove
 (`BitZeros_hol (&0) = Value (Native_Value [])`,
  REWRITE_TAC[BitZeros_hol_DEF] THEN BALL_SIMP_TAC[TYPED_HOL_INT_TO_BIT_NUM] THEN
  CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
  REWRITE_TAC[ARITH_RULE `0 < 2`; NATIVE_BIND; LENGTH_REPLICATE; ISA_NAT_NUM;
              ARITH_RULE `0 < 1`; TYPED_HOL_READ] THEN
  REWRITE_TAC[native_schedule_DEF; INT_LT_REFL; native_foldl_DEF; NATIVE_BIND]);;

let ball_bitlen_fact n c =
  prove(parse_term (Printf.sprintf "bitlen %d = %d" n c),
   REPEAT(ONCE_REWRITE_TAC[bitlen_DEF] THEN
          CONV_TAC(NUM_REDUCE_CONV THENC REWRITE_CONV[])));;


(* ------------------------------------------------------------------------- *)
(* BytesToBits_N: the generator of ball.ml for the remaining lengths.        *)
(* ------------------------------------------------------------------------- *)

let ENC_BYTES_TO_BITS_34 = ball_bytes_to_bits_gen 34 BytesToBits_34_hol_DEF;;
let ENC_BYTES_TO_BITS_96 = ball_bytes_to_bits_gen 96 BytesToBits_96_hol_DEF;;
let ENC_BYTES_TO_BITS_128 = ball_bytes_to_bits_gen 128 BytesToBits_128_hol_DEF;;
let ENC_BYTES_TO_BITS_320 = ball_bytes_to_bits_gen 320 BytesToBits_320_hol_DEF;;
let ENC_BYTES_TO_BITS_416 = ball_bytes_to_bits_gen 416 BytesToBits_416_hol_DEF;;

let ENC_BYTES_TO_BITS_STRING = BALL_BYTES_TO_BITS_STRING;;

(* ------------------------------------------------------------------------- *)
(* BitPack and SimpleBitPack (FIPS 204 Algorithms 16 and 17): the pack of a  *)
(* polynomial w with 0 <= b - w (resp. 0 <= w) is mldsa_encode of the        *)
(* coefficients. Hypotheses are the coefficient ranges, for j < 256.         *)
(* ------------------------------------------------------------------------- *)

let enc_pack_gen simple a b c def itb =
  let pt s = parse_term s and sp = Printf.sprintf in
  let xk = if simple then "(w:num->int) k" else sp "&%d - (w:num->int) k" b in
  let xj = if simple then "(w:num->int) j" else sp "&%d - (w:num->int) j" b in
  let goal = pt(if simple then sp
   "!w. (!j. j < 256 ==> &0 <= w j /\\ w j <= &%d)
        ==> SimpleBitPack_%d_hol (lift_intpoly w) (&%d) =
            Value (mldsa_encode %d 256 (\\j. w j))" b b b c
   else sp
   "!w. (!j. j < 256 ==> --(&%d) <= w j /\\ w j <= &%d)
        ==> BitPack_%d_%d_hol (lift_intpoly w) (&%d) (&%d) =
            Value (mldsa_encode %d 256 (\\j. &%d - w j))" a b a b a b c b) in
  let bbs = sp "mldsa_encode %d 256 (\\j. %s)" c xj in
  let inv = pt(sp
   "\\k (z:(bool list)native_bottom). z = Native_Value (list_of_seq
      (\\t. EL t (bits_of_bytes (%s))) (%d * k))" bbs c) in
  let blen = ball_bitlen_fact (if simple then b else a + b) c in
  let sch = SPECL [`257`; `256`] NATIVE_SCHEDULE_NUM in
  let fld = pt(sp "(num_of_bytelist (%s) DIV 2 EXP (%d * k)) MOD 2 EXP %d = nk"
                  bbs c c) in
  let mfe = SPECL [mk_small_numeral c; `256`;
                   pt(sp "\\j. %s" xj); `k:num`]
                  MLDSA_FIELD_ENCODE_SMALL in
  let exnk = pt(sp "?nk. %s = &nk" xk) in
  let exw = pt(sp "num_of_int(%s)" xk) in
  let sucs = pt(sp "%d * SUC k = %d * k + %d" c c c) in
  let ebf = SPECL [mk_small_numeral c; pt bbs; `k:num`; `i:num`]
                  ENC_EL_BITS_FIELD in
  let len = pt(sp "LENGTH(%s) = %d" bbs (32 * c)) in
  let lseq = pt(sp
    "list_of_seq (\\t. EL t (bits_of_bytes (%s))) (%d * 256) =
     bits_of_bytes (%s)" bbs c bbs) in
  prove(goal,
    REPEAT STRIP_TAC THEN REWRITE_TAC[def] THEN
    BALL_SIMP_TAC[ENC_BITZEROS_0] THEN
    CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
    REWRITE_TAC[NATIVE_BIND; ISA_NAT_NUM] THEN
    MP_TAC sch THEN ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ENC_FOLDL_TAC inv "st" THENL
     [CONJ_TAC THENL [REWRITE_TAC[MULT_CLAUSES; list_of_seq]; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[lift_intpoly; fips204_intpoly_coefficients_DEF] THEN
      ASM_SIMP_TAC[NATIVE_LIST_INDEX_NUM; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ;
                   TYPED_HOL_READ; NATIVE_BIND; bitlen_semantic_DEF; ISA_NAT_NUM;
                   blen; INT_ARITH `~(&n:int < &0)`] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN exnk STRIP_ASSUME_TAC THENL
       [EXISTS_TAC exw THEN
        MATCH_MP_TAC(GSYM INT_OF_NUM_OF_INT) THEN ASM_INT_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN fld ASSUME_TAC THENL
       [MP_TAC mfe THEN
        REWRITE_TAC[mldsa_field] THEN
        ANTS_TAC THENL
         [CONV_TAC(DEPTH_CONV BETA_CONV) THEN
          REPEAT CONJ_TAC THENL
           [REWRITE_TAC[divides] THEN EXISTS_TAC (mk_small_numeral (32 * c)) THEN
            ARITH_TAC;
            ASM_REWRITE_TAC[];
            ASM_INT_ARITH_TAC;
            REWRITE_TAC[INT_POW; ARITH] THEN
            CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN ASM_INT_ARITH_TAC];
          CONV_TAC(DEPTH_CONV BETA_CONV) THEN
          REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_EQ] THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[INT_OF_NUM_EQ; EQ_SYM_EQ]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[itb; case_native_bottom_DEF; TYPED_HOL_READ;
                      NATIVE_BIND; injectivity "native_result";
                      injectivity "native_bottom"; UNWIND_THM1] THEN
      SUBGOAL_THEN sucs SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[LIST_OF_SEQ_ADD] THEN
      AP_TERM_TAC THEN
      MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `i:num` THEN
      DISCH_TAC THEN
      MP_TAC ebf THEN
      ASM_REWRITE_TAC[MLDSA_ENCODE_LENGTH] THEN
      ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
      FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
                       lhs(concl th) = `st:(bool list)native_bottom`
                      then SUBST1_TAC th else NO_TAC) THEN
      SUBGOAL_THEN len ASSUME_TAC THENL
       [REWRITE_TAC[MLDSA_ENCODE_LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN lseq SUBST1_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM LIST_OF_SEQ_EQ_SELF] THEN
        REWRITE_TAC[LENGTH_BITS_OF_BYTES] THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      REWRITE_TAC[case_native_bottom_DEF; ENC_BITSTOBYTES_STRING; NATIVE_BIND] THEN
      ASM_REWRITE_TAC[typed_hol_sequence_extent_DEF]]);;

let enc_bitpack_gen = enc_pack_gen false;;
let enc_simplebitpack_gen = enc_pack_gen true;;

let ENC_INTEGER_TO_BITS_20 = enc_int_to_bits_gen 20 IntegerToBits_20_hol_DEF;;
let ENC_INTEGER_TO_BITS_3 = enc_int_to_bits_gen 3 IntegerToBits_3_hol_DEF;;
let ENC_INTEGER_TO_BITS_4 = enc_int_to_bits_gen 4 IntegerToBits_4_hol_DEF;;
let ENC_INTEGER_TO_BITS_6 = enc_int_to_bits_gen 6 IntegerToBits_6_hol_DEF;;
let ENC_INTEGER_TO_BITS_10 = enc_int_to_bits_gen 10 IntegerToBits_10_hol_DEF;;
let ENC_INTEGER_TO_BITS_13 = enc_int_to_bits_gen 13 IntegerToBits_13_hol_DEF;;
let ENC_BITPACK_2 =
  enc_bitpack_gen 2 2 3 BitPack_2_2_hol_DEF ENC_INTEGER_TO_BITS_3;;
let ENC_BITPACK_4 =
  enc_bitpack_gen 4 4 4 BitPack_4_4_hol_DEF ENC_INTEGER_TO_BITS_4;;
let ENC_BITPACK_4095 =
  enc_bitpack_gen 4095 4096 13 BitPack_4095_4096_hol_DEF ENC_INTEGER_TO_BITS_13;;
let ENC_BITPACK_131071 =
  enc_bitpack_gen 131071 131072 18 BitPack_131071_131072_hol_DEF
                  ENC_INTEGER_TO_BITS_18;;
let ENC_BITPACK_524287 =
  enc_bitpack_gen 524287 524288 20 BitPack_524287_524288_hol_DEF
                  ENC_INTEGER_TO_BITS_20;;
let ENC_SIMPLEBITPACK_15 =
  enc_simplebitpack_gen 0 15 4 SimpleBitPack_15_hol_DEF ENC_INTEGER_TO_BITS_4;;
let ENC_SIMPLEBITPACK_43 =
  enc_simplebitpack_gen 0 43 6 SimpleBitPack_43_hol_DEF ENC_INTEGER_TO_BITS_6;;
let ENC_SIMPLEBITPACK_1023 =
  enc_simplebitpack_gen 0 1023 10 SimpleBitPack_1023_hol_DEF
                        ENC_INTEGER_TO_BITS_10;;

(* ------------------------------------------------------------------------- *)
(* BitUnpack and SimpleBitUnpack (Algorithms 18 and 19): the instances of    *)
(* ball_bitunpack_gen (ball.ml) for the remaining parameter sets.            *)
(* ------------------------------------------------------------------------- *)

let ENC_BITUNPACK_2 = ball_bitunpack_gen false 2 2 3
  BitUnpack_2_2_hol_DEF ENC_BYTES_TO_BITS_96;;
let ENC_BITUNPACK_4 = ball_bitunpack_gen false 4 4 4
  BitUnpack_4_4_hol_DEF ENC_BYTES_TO_BITS_128;;
let ENC_BITUNPACK_4095 = ball_bitunpack_gen false 4095 4096 13
  BitUnpack_4095_4096_hol_DEF ENC_BYTES_TO_BITS_416;;
let ENC_BITUNPACK_131071 = BALL_BITUNPACK_131071;;
let ENC_BITUNPACK_524287 = BALL_BITUNPACK_524287;;
let ENC_SIMPLEBITUNPACK_1023 = ball_bitunpack_gen true 0 1023 10
  SimpleBitUnpack_1023_hol_DEF ENC_BYTES_TO_BITS_320;;

(* ------------------------------------------------------------------------- *)
(* Concatenation of encodings: mldsa_encode of k * 256 values is the         *)
(* append of the encodings of the k polynomials.                             *)
(* ------------------------------------------------------------------------- *)


let ENC_ENCODE_VEC_STEP = prove
 (`!c i (z:num->num->int).
        mldsa_encode c (256 * SUC i) (\n. z (n DIV 256) (n MOD 256)) =
        APPEND (mldsa_encode c (256 * i) (\n. z (n DIV 256) (n MOD 256)))
               (mldsa_encode c 256 (z i))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `256 * SUC i = 256 * i + 256` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:num`; `256 * i`; `256`;
                `\n. (z:num->num->int) (n DIV 256) (n MOD 256)`]
               MLDSA_ENCODE_APPEND) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[divides] THENL
     [EXISTS_TAC `32 * c * i` THEN ARITH_TAC;
      EXISTS_TAC `32 * c` THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MLDSA_ENCODE_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  BETA_TAC THEN
  SUBGOAL_THEN `(256 * i + j) DIV 256 = i /\ (256 * i + j) MOD 256 = j`
    (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `j:num` THEN ASM_ARITH_TAC;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `i:num` THEN ASM_ARITH_TAC]);;

let ENC_FOLDL_VEC = prove
 (`!(body:int->(byte)list->((byte)list)native_result) (s0:byte list) k c
    (z:num->num->int).
        (!i t. i < k ==> body (&i) t =
                         Value(APPEND t (mldsa_encode c 256 (z i))))
        ==> native_foldl body (list_of_seq (\i. &i) k) s0 =
            Value(APPEND s0 (mldsa_encode c (256 * k)
                              (\n. z (n DIV 256) (n MOD 256))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`body:int->(byte)list->((byte)list)native_result`; `k:num`;
    `\i (t:byte list). t = APPEND s0 (mldsa_encode c (256 * i)
                              (\n. (z:num->num->int) (n DIV 256) (n MOD 256)))`;
    `s0:byte list`] ENC_FOLDL_INV) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MULT_CLAUSES; MLDSA_ENCODE_0; APPEND_NIL]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k':num`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `APPEND s0 (mldsa_encode c (256 * k')
        (\n. (z:num->num->int) (n DIV 256) (n MOD 256)))`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[injectivity "native_result"; UNWIND_THM1;
                ENC_ENCODE_VEC_STEP; APPEND_ASSOC];
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* pkEncode (Algorithm 22) and w1Encode (Algorithm 28). Vectors are given    *)
(* as t i j, coefficient j of polynomial i, for i < k and j < 256.           *)
(* ------------------------------------------------------------------------- *)

let ENC_VEC_TAC c ztm : tactic =
  fun (asl,w) ->
    let is_foldl t =
      match strip_comb t with
        (cc,[_;_;_]) -> is_const cc && fst(dest_const cc) = "native_foldl"
      | _ -> false in
    let tm = find_term is_foldl w in
    let body,sched,s0 = match snd(strip_comb tm) with
        [x;y;z] -> x,y,z | _ -> failwith "ENC_VEC_TAC" in
    let k = rand sched in
    let th = ISPECL [body; s0; k; mk_small_numeral c; ztm] ENC_FOLDL_VEC in
    (MP_TAC th THEN ANTS_TAC THENL
      [CONV_TAC(DEPTH_CONV BETA_CONV); DISCH_THEN SUBST1_TAC]) (asl,w);;

let ENC_VEC_ENTRY = prove
 (`!(v:num->(fips204_intpoly)) i.
     i < dimindex(:N)
     ==> native_list_index (common_vec_entries (lift_vec v:(N,fips204_intpoly)common_vec)) (&i) =
         SOME (v i)`,
  SIMP_TAC[COMMON_VEC_ENTRIES_LIFT; NATIVE_LIST_INDEX_NUM; LENGTH_LIST_OF_SEQ;
           EL_LIST_OF_SEQ]);;


let enc_pkencode_gen p k def =
  let pt s = parse_term s and sp = Printf.sprintf in
  let goal = pt(sp
   "!rho t. LENGTH rho = 32 /\\
            (!i j. i < %d /\\ j < 256 ==> &0 <= t i j /\\ t i j <= &1023)
            ==> pkEncode_MLDSA%s_Configuration_hol rho
                  (lift_vec (\\i. lift_intpoly (t i)):(%d,fips204_intpoly)common_vec) =
                Value (APPEND rho (mldsa_encode 10 (256 * %d)
                                    (\\n. t (n DIV 256) (n MOD 256))))"
   k p k k) in
  let sch = SPECL [pt(string_of_int (k + 1)); pt(string_of_int k)]
                  NATIVE_SCHEDULE_NUM in
  prove(goal,
    REPEAT STRIP_TAC THEN REWRITE_TAC[def] THEN
    BALL_SIMP_TAC[] THEN
    ASM_SIMP_TAC[TYPED_HOL_LIST_SLICE_ALL; TYPED_HOL_READ; NATIVE_BIND] THEN
    MP_TAC sch THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ENC_VEC_TAC 10 `t:num->num->int` THENL
     [REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[ENC_VEC_ENTRY; DIMINDEX_CONV(pt(sp "dimindex(:%d)" k));
                   TYPED_HOL_READ; NATIVE_BIND; bitlen_semantic_DEF; ISA_NAT_NUM;
                   ball_bitlen_fact 8380416 23; INT_ARITH `~(&n:int < &0)`] THEN
      CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
      REWRITE_TAC[BALL_INT_ARITH; NATIVE_BIND] THEN
      CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
      MP_TAC(SPEC `(t:num->num->int) i` ENC_SIMPLEBITPACK_1023) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NATIVE_BIND; ETA_AX];
      REFL_TAC]);;

let EQ_PKENCODE_MLDSA44 = enc_pkencode_gen "44" 4 pkEncode_MLDSA44_Configuration_hol_DEF;;
let EQ_PKENCODE_MLDSA65 = enc_pkencode_gen "65" 6 pkEncode_MLDSA65_Configuration_hol_DEF;;
let EQ_PKENCODE_MLDSA87 = enc_pkencode_gen "87" 8 pkEncode_MLDSA87_Configuration_hol_DEF;;

let ENC_BYTEZEROS_0 = prove
 (`ByteZeros_hol (&0) = Value (Native_Value [])`,
  REWRITE_TAC[ByteZeros_hol_DEF] THEN BALL_SIMP_TAC[TYPED_HOL_INT_TO_BYTE_NUM] THEN
  CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
  REWRITE_TAC[ARITH_RULE `0 < 256`; NATIVE_BIND; LENGTH_REPLICATE;
              ISA_NAT_NUM; ARITH_RULE `0 < 1`; TYPED_HOL_READ] THEN
  REWRITE_TAC[native_schedule_DEF; INT_LT_REFL; native_foldl_DEF; NATIVE_BIND]);;

let ENC_AQUOT = prove
 (`!m n. ~(n = 0) /\ m MOD n = 0
         ==> typed_hol_int_arithmetic AQuot (&m) (&n) = Value (&(m DIV n))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[typed_hol_int_arithmetic_DEF; arith_faults_DEF; int_op_DEF;
              case_aop_DEF; distinctness "aop"; INT_ARITH `~(&n:int < &0)`;
              ISA_INT_DIV_NUM_NUM; BALL_ISA_INT_NUM; INT_OF_NUM_EQ] THEN
  ASM_REWRITE_TAC[]);;

let ENC_FOLDL_VEC_NB = prove
 (`!(body:int->(byte list)native_bottom->(((byte)list)native_bottom)native_result)
    (s0:byte list) k c (z:num->num->int).
        (!i t. i < k ==> body (&i) (Native_Value t) =
                         Value(Native_Value
                                (APPEND t (mldsa_encode c 256 (z i)))))
        ==> native_foldl body (list_of_seq (\i. &i) k) (Native_Value s0) =
            Value(Native_Value
                   (APPEND s0 (mldsa_encode c (256 * k)
                              (\n. z (n DIV 256) (n MOD 256)))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`body:int->(byte list)native_bottom->(((byte)list)native_bottom)native_result`; `k:num`;
    `\i (t:(byte list)native_bottom). t = Native_Value (APPEND s0 (mldsa_encode c (256 * i)
                              (\n. (z:num->num->int) (n DIV 256) (n MOD 256))))`;
    `Native_Value s0:(byte list)native_bottom`] ENC_FOLDL_INV) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MULT_CLAUSES; MLDSA_ENCODE_0; APPEND_NIL]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k':num`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `APPEND s0 (mldsa_encode c (256 * k')
        (\n. (z:num->num->int) (n DIV 256) (n MOD 256)))`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[injectivity "native_result"; UNWIND_THM1;
                injectivity "native_bottom";
                ENC_ENCODE_VEC_STEP; APPEND_ASSOC];
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let ENC_VECNB_TAC c ztm : tactic =
  fun (asl,w) ->
    let is_foldl t =
      match strip_comb t with
        (cc,[_;_;_]) -> is_const cc && fst(dest_const cc) = "native_foldl"
      | _ -> false in
    let tm = find_term is_foldl w in
    let body,sched,s0 = match snd(strip_comb tm) with
        [x;y;z] -> x,y,z | _ -> failwith "ENC_VECNB_TAC" in
    let k = rand sched in
    let th = ISPECL [body; rand s0; k; mk_small_numeral c; ztm]
                    ENC_FOLDL_VEC_NB in
    (MP_TAC th THEN ANTS_TAC THENL
      [CONV_TAC(DEPTH_CONV BETA_CONV); DISCH_THEN SUBST1_TAC]) (asl,w);;

let enc_w1encode_gen p k m c def sbp =
  let pt s = parse_term s and sp = Printf.sprintf in
  let goal = pt(sp
   "!w. (!i j. i < %d /\\ j < 256 ==> &0 <= w i j /\\ w i j <= &%d)
        ==> w1Encode_MLDSA%s_Configuration_hol
              (lift_vec (\\i. lift_intpoly (w i)):(%d,fips204_intpoly)common_vec) =
            Value (Native_Value (mldsa_encode %d (256 * %d)
                                  (\\n. w (n DIV 256) (n MOD 256))))"
   k m p k c k) in
  let sch = SPECL [pt(string_of_int (k + 1)); pt(string_of_int k)]
                  NATIVE_SCHEDULE_NUM in
  let aquot =
    let n = (8380416 / (2 * (match p with "44" -> 95232 | _ -> 261888))) in
    let d = 2 * (match p with "44" -> 95232 | _ -> 261888) in
    ignore n;
    let m = mk_small_numeral 8380416 and dd = mk_small_numeral d in
    CONV_RULE(RAND_CONV(RAND_CONV(RAND_CONV NUM_REDUCE_CONV)))
     (MP (SPECL [m; dd] ENC_AQUOT)
       (CONJ (EQT_ELIM(NUM_REDUCE_CONV(mk_neg(mk_eq(dd,`0`)))))
             (EQT_ELIM(NUM_REDUCE_CONV(mk_eq(mk_binop `MOD` m dd,`0`)))))) in
  prove(goal,
    REPEAT STRIP_TAC THEN REWRITE_TAC[def] THEN
    BALL_SIMP_TAC[ENC_BYTEZEROS_0] THEN
    MP_TAC sch THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ENC_VECNB_TAC c `w:num->num->int` THENL
     [REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[ENC_VEC_ENTRY; DIMINDEX_CONV(pt(sp "dimindex(:%d)" k));
                   TYPED_HOL_READ; NATIVE_BIND; case_native_bottom_DEF] THEN
      REWRITE_TAC[aquot; NATIVE_BIND] THEN
      CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
      MP_TAC(SPEC `(w:num->num->int) i` sbp) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[NATIVE_BIND; ETA_AX; case_native_bottom_DEF; TYPED_HOL_READ];
      REWRITE_TAC[APPEND]]);;
let EQ_W1ENCODE_MLDSA44 =
  enc_w1encode_gen "44" 4 43 6 w1Encode_MLDSA44_Configuration_hol_DEF
                   ENC_SIMPLEBITPACK_43;;
let EQ_W1ENCODE_MLDSA65 =
  enc_w1encode_gen "65" 6 15 4 w1Encode_MLDSA65_Configuration_hol_DEF
                   ENC_SIMPLEBITPACK_15;;
let EQ_W1ENCODE_MLDSA87 =
  enc_w1encode_gen "87" 8 15 4 w1Encode_MLDSA87_Configuration_hol_DEF
                   ENC_SIMPLEBITPACK_15;;

(* ------------------------------------------------------------------------- *)
(* skEncode (Algorithm 24): rho || K || tr, then BitPack of s1 and s2 with   *)
(* (eta, eta) and of t0 with (2^12 - 1, 2^12).                               *)
(* ------------------------------------------------------------------------- *)

let enc_skencode_gen p k l eta c def bp =
  let pt s = parse_term s and sp = Printf.sprintf in
  let vty n = sp "(%d,fips204_intpoly)common_vec" n in
  let goal = pt(sp
   "!rho kk tr s1 s2 t0.
      LENGTH rho = 32 /\\ LENGTH kk = 32 /\\ LENGTH tr = 64 /\\
      (!i j. i < %d /\\ j < 256 ==> --(&%d) <= s1 i j /\\ s1 i j <= &%d) /\\
      (!i j. i < %d /\\ j < 256 ==> --(&%d) <= s2 i j /\\ s2 i j <= &%d) /\\
      (!i j. i < %d /\\ j < 256 ==> --(&4095) <= t0 i j /\\ t0 i j <= &4096)
      ==> skEncode_MLDSA%s_Configuration_hol rho kk tr
            (lift_vec (\\i. lift_intpoly (s1 i)):%s)
            (lift_vec (\\i. lift_intpoly (s2 i)):%s)
            (lift_vec (\\i. lift_intpoly (t0 i)):%s) =
          Value (APPEND rho (APPEND kk (APPEND tr
            (APPEND (mldsa_encode %d (256 * %d)
                      (\\n. &%d - s1 (n DIV 256) (n MOD 256)))
              (APPEND (mldsa_encode %d (256 * %d)
                        (\\n. &%d - s2 (n DIV 256) (n MOD 256)))
                      (mldsa_encode 13 (256 * %d)
                        (\\n. &4096 - t0 (n DIV 256) (n MOD 256))))))))"
   l eta eta k eta eta k p (vty l) (vty k) (vty k) c l eta c k eta k) in
  let sch n = SPECL [pt(string_of_int (n + 1)); pt(string_of_int n)]
                    NATIVE_SCHEDULE_NUM in
  let dim n = DIMINDEX_CONV(pt(sp "dimindex(:%d)" n)) in
  let step n v bpth =
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[ENC_VEC_ENTRY; dim n; TYPED_HOL_READ; NATIVE_BIND] THEN
    MP_TAC(SPEC v bpth) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NATIVE_BIND] in
  let sched n = MP_TAC(sch n) THEN
                ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] in
  let c1 = pt(sp "\\i j. &%d - (s1:num->num->int) i j" eta)
  and c2 = pt(sp "\\i j. &%d - (s2:num->num->int) i j" eta)
  and c3 = `\i j. &4096 - (t0:num->num->int) i j` in
  prove(goal,
    REPEAT STRIP_TAC THEN REWRITE_TAC[def] THEN
    BALL_SIMP_TAC[] THEN
    SUBGOAL_THEN `LENGTH(APPEND (APPEND (rho:byte list) (kk:byte list)) (tr:byte list)) = 128` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[TYPED_HOL_LIST_SLICE_ALL; TYPED_HOL_READ; NATIVE_BIND] THEN
    sched l THEN
    ENC_VEC_TAC c c1 THENL
     [step l `(s1:num->num->int) i` bp;
      REWRITE_TAC[NATIVE_BIND] THEN
      sched k THEN
      ENC_VEC_TAC c c2 THENL
       [step k `(s2:num->num->int) i` bp;
        REWRITE_TAC[NATIVE_BIND] THEN
        sched k THEN
        ENC_VEC_TAC 13 c3 THENL
         [REPEAT STRIP_TAC THEN
          ASM_SIMP_TAC[ENC_VEC_ENTRY; dim k; TYPED_HOL_READ; NATIVE_BIND] THEN
          REWRITE_TAC[BALL_INT_ARITH; NATIVE_BIND] THEN
          CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
          MP_TAC(SPEC `(t0:num->num->int) i` ENC_BITPACK_4095) THEN
          ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NATIVE_BIND];
          REWRITE_TAC[APPEND_ASSOC]]]]);;

let EQ_SKENCODE_MLDSA44 =
  enc_skencode_gen "44" 4 4 2 3 skEncode_MLDSA44_Configuration_hol_DEF ENC_BITPACK_2;;
let EQ_SKENCODE_MLDSA65 =
  enc_skencode_gen "65" 6 5 4 4 skEncode_MLDSA65_Configuration_hol_DEF ENC_BITPACK_4;;
let EQ_SKENCODE_MLDSA87 =
  enc_skencode_gen "87" 8 7 2 3 skEncode_MLDSA87_Configuration_hol_DEF ENC_BITPACK_2;;

(* ------------------------------------------------------------------------- *)
(* Fields of slices: field 256 * i + j of a slice of 32 * c * l bytes is     *)
(* field j of its i-th block of 32 * c bytes.                                *)
(* ------------------------------------------------------------------------- *)

let ENC_SLICE_SUC = prove
 (`!a n (b:byte list). mldsa_slice a (SUC n) b =
                       CONS (EL a b) (mldsa_slice (a + 1) n b)`,
  REWRITE_TAC[mldsa_slice; LIST_OF_SEQ; o_DEF; ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `SUC (a + x) = (a + 1) + x`]);;

let ENC_SLICE_0 = prove
 (`!a (b:byte list). mldsa_slice a 0 b = []`,
  REWRITE_TAC[mldsa_slice; list_of_seq]);;

let ENC_NUM_SLICE_SUC = prove
 (`!a n (b:byte list).
        num_of_bytelist (mldsa_slice a (SUC n) b) =
        val (EL a b) + 256 * num_of_bytelist (mldsa_slice (a + 1) n b)`,
  REWRITE_TAC[ENC_SLICE_SUC; num_of_bytelist]);;

let ENC_NUM_SLICE_DIV = prove
 (`!m a n (b:byte list). m <= n
        ==> num_of_bytelist (mldsa_slice a n b) DIV 256 EXP m =
            num_of_bytelist (mldsa_slice (a + m) (n - m) b)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[EXP; DIV_1; ADD_CLAUSES; SUB_0]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?n'. n = SUC n'` (X_CHOOSE_THEN `n':num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `n - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ENC_NUM_SLICE_SUC; EXP; GSYM DIV_DIV] THEN
  SUBGOAL_THEN `(val (EL a (b:byte list)) + 256 * num_of_bytelist (mldsa_slice (a + 1) n' b)) DIV 256 = num_of_bytelist (mldsa_slice (a + 1) n' b)` SUBST1_TAC THENL
   [MP_TAC(ISPEC `EL a (b:byte list)` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[ARITH_RULE `x + 256 * y = y * 256 + x`] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_EQ; DIV_LT; ADD_CLAUSES];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a + 1`; `n':num`; `b:byte list`]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ARITH_RULE `SUC n' - SUC m = n' - m`;
              ARITH_RULE `(a + 1) + m = a + SUC m`]);;

let ENC_MOD_256 = prove
 (`!v N Q. v < 256 ==> (v + 256 * N) MOD (256 * Q) = v + 256 * (N MOD Q)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `Q = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; MOD_ZERO]; ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `Q:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`N MOD Q`,`r:num`) THEN SPEC_TAC(`N DIV Q`,`q:num`) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q:num` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB] THEN ARITH_TAC; ASM_ARITH_TAC]);;

let ENC_NUM_SLICE_MOD = prove
 (`!n' a n (b:byte list). n' <= n
        ==> num_of_bytelist (mldsa_slice a n' b) =
            num_of_bytelist (mldsa_slice a n b) MOD 256 EXP n'`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[ENC_SLICE_0; num_of_bytelist; EXP; MOD_1]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?n''. n = SUC n''` (X_CHOOSE_THEN `n'':num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `n - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ENC_NUM_SLICE_SUC; EXP] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a + 1`; `n'':num`; `b:byte list`]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC(GSYM ENC_MOD_256) THEN
  MP_TAC(ISPEC `EL a (b:byte list)` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ENC_FIELD_SLICE = prove
 (`!c a l (b:byte list) i j.
        (i + 1) * (32 * c) <= l /\ j < 256
        ==> mldsa_field c (mldsa_slice a l b) (256 * i + j) =
            mldsa_field c (mldsa_slice (a + 32 * c * i) (32 * c) b) j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_field; INT_OF_NUM_EQ] THEN
  ABBREV_TAC `m = 32 * c * i` THEN
  SUBGOAL_THEN `m + 32 * c <= l` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * j + c <= 256 * c` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `c * j + c = c * (j + 1)`;
                ARITH_RULE `256 * c = c * 256`; LE_MULT_LCANCEL] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP (c * (256 * i + j)) = 256 EXP m * 2 EXP (c * j)`
    SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP; GSYM EXP_ADD] THEN
    AP_TERM_TAC THEN EXPAND_TAC "m" THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  SUBGOAL_THEN `num_of_bytelist (mldsa_slice a l (b:byte list)) DIV 256 EXP m =
                num_of_bytelist (mldsa_slice (a + m) (l - m) b)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC ENC_NUM_SLICE_DIV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`32 * c`; `a + m`; `l - m`; `b:byte list`] ENC_NUM_SLICE_MOD) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC `N' = num_of_bytelist (mldsa_slice (a + m) (l - m) (b:byte list))` THEN
  SUBGOAL_THEN `256 EXP (32 * c) = 2 EXP (c * j) * 2 EXP (256 * c - c * j)`
    SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP; GSYM EXP_ADD] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_MOD; MOD_MOD_EXP_MIN] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[MIN] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* pkDecode (Algorithm 23).                                                  *)
(* ------------------------------------------------------------------------- *)

let enc_pkdecode_gen p k def =
  let pt s = parse_term s and sp = Printf.sprintf in
  let vty = sp "(%d,fips204_intpoly)common_vec" k in
  let goal = pt(sp
   "!pk. LENGTH pk = 32 + 320 * %d
         ==> pkDecode_MLDSA%s_Configuration_hol pk =
             Value (mldsa_slice 0 32 pk,
                    (lift_vec (\\i. lift_intpoly (\\j. mldsa_field 10
                        (mldsa_slice 32 (320 * %d) pk) (256 * i + j))):%s))"
   k p k vty) in
  let inv = pt(sp
   "\\k (v:%s). v = lift_vec (\\j. if j < k then lift_intpoly (\\x. mldsa_field 10
        (mldsa_slice 32 (320 * %d) pk) (256 * j + x)) else lift_intpoly (\\x. &0))"
   vty k) in
  let sch = SPECL [pt(string_of_int (k + 1)); pt(string_of_int k)]
                  NATIVE_SCHEDULE_NUM in
  let dim = DIMINDEX_CONV(pt(sp "dimindex(:%d)" k)) in
  let fs = SPECL [`10`; `32`; pt(sp "320 * %d" k); `pk:byte list`; `k:num`;
                  `x:num`] ENC_FIELD_SLICE in
  prove(goal,
    REPEAT STRIP_TAC THEN REWRITE_TAC[def] THEN
    BALL_SIMP_TAC[BALL_INT_ARITH; INT_POW_ONE; TYPED_HOL_SEQUENCE_EXTENT] THEN
    CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
    REWRITE_TAC[NATIVE_BIND] THEN
    SUBGOAL_THEN `32 <= LENGTH(pk:byte list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[BALL_SLICE; TYPED_HOL_READ; NATIVE_BIND; ARITH_RULE `0 <= 32`] THEN
    MP_TAC sch THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ENC_FOLDL_TAC inv "st" THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[lift_vec; CONJUNCT1 LT; lift_intpoly; BALL_MAP_REPLICATE;
                    REPLICATE_LIST_OF_SEQ] THEN
        CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN REWRITE_TAC[];
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
        REWRITE_TAC[typed_hol_nonnegative_DEF; INT_POS; NATIVE_BIND;
                    bitlen_semantic_DEF; ISA_NAT_NUM;
                    ball_bitlen_fact 8380416 23;
                    INT_ARITH `~(&n:int < &0)`] THEN
        CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
        REWRITE_TAC[NATIVE_BIND; BALL_INT_ARITH; INT_POW_ONE; INT_OF_NUM_MUL;
                    INT_OF_NUM_ADD; INT_MUL_RID] THEN
        SUBGOAL_THEN `32 + 320 * (k + 1) <= LENGTH(pk:byte list)` ASSUME_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[MULT_CLAUSES] THEN
        ASM_SIMP_TAC[BALL_SLICE; ARITH_RULE `32 + 320 * k <= 32 + 320 * (k + 1)`;
                     TYPED_HOL_READ; NATIVE_BIND] THEN
        REWRITE_TAC[ARITH_RULE `(32 + 320 * (k + 1)) - (32 + 320 * k) = 320`] THEN
        REWRITE_TAC[GSYM mldsa_slice] THEN
        ASM_SIMP_TAC[TYPED_HOL_SEQUENCE_EXTENT; LENGTH_MLDSA_SLICE; NATIVE_BIND] THEN
        CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
        ASM_SIMP_TAC[ENC_SIMPLEBITUNPACK_1023; LENGTH_MLDSA_SLICE; NATIVE_BIND] THEN
        REWRITE_TAC[typed_hol_nominal_update_DEF; isa_map_option;
                    COMMON_VEC_ENTRIES_LIFT; dim;
                    NATIVE_LIST_UPDATE_NUM; LENGTH_LIST_OF_SEQ] THEN
        ASM_REWRITE_TAC[TYPED_HOL_READ; NATIVE_BIND; ISA_LIST_UPDATE_LIST_OF_SEQ;
                        injectivity "native_result"; UNWIND_THM1;
                        ISA_NAT_NUM] THEN
        REWRITE_TAC[isa_map_option; TYPED_HOL_READ; injectivity "native_result";
                    UNWIND_THM1] THEN
        REWRITE_TAC[lift_vec; dim] THEN
        AP_TERM_TAC THEN
        MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `i:num` THEN
        DISCH_TAC THEN REWRITE_TAC[LT] THEN
        ASM_CASES_TAC `i:num = k` THENL
         [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
          REWRITE_TAC[lift_intpoly; injectivity "fips204_intpoly"] THEN
          MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `x:num` THEN
          DISCH_TAC THEN BETA_TAC THEN
          MP_TAC fs THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[ARITH_RULE `32 * 10 * k = 320 * k`;
                      ARITH_RULE `32 * 10 = 320`] THEN
          DISCH_THEN(fun th -> REWRITE_TAC[th]);
          POP_ASSUM(fun th -> REWRITE_TAC[th])]];
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[NATIVE_BIND; injectivity "native_result"; PAIR_EQ] THEN
      REWRITE_TAC[ARITH_RULE `32 - 0 = 32`; ADD_CLAUSES] THEN
      ASM_SIMP_TAC[TYPED_HOL_SEQUENCE_EXTENT; LENGTH_LIST_OF_SEQ; NATIVE_BIND;
                   injectivity "native_result"; PAIR_EQ] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[mldsa_slice; ADD_CLAUSES];
        REWRITE_TAC[LIFT_VEC_EQ; dim] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]]);;
let EQ_PKDECODE_MLDSA44 =
  enc_pkdecode_gen "44" 4 pkDecode_MLDSA44_Configuration_hol_DEF;;
let EQ_PKDECODE_MLDSA65 =
  enc_pkdecode_gen "65" 6 pkDecode_MLDSA65_Configuration_hol_DEF;;
let EQ_PKDECODE_MLDSA87 =
  enc_pkdecode_gen "87" 8 pkDecode_MLDSA87_Configuration_hol_DEF;;

(* ------------------------------------------------------------------------- *)
(* Decoded{Public,Secret}KeyStrings bodies (identity on the lifted parts).   *)
(* ------------------------------------------------------------------------- *)

let ENC_INTPOLY_SELF = prove
 (`!p. FIPS204_IntPoly (fips204_intpoly_coefficients p) = p`,
  MATCH_MP_TAC fips204_intpoly_INDUCT THEN
  REWRITE_TAC[fips204_intpoly_coefficients_DEF]);;

let enc_decoded_pk_gen k p def =
  let pt s = parse_term s and sp = Printf.sprintf in
  let vty = sp "(%d,fips204_intpoly)common_vec" k in
  let goal = pt(sp
   "!rho (t1:%s). LENGTH rho = 32
        ==> DecodedPublicKeyStrings_%d_MLDSA%s_Configuration_body_hol (rho,t1) =
            Value (Native_Value (rho,t1))" vty k p) in
  prove(goal,
    REPEAT STRIP_TAC THEN REWRITE_TAC[def] THEN
    BALL_SIMP_TAC[COMMON_VEC_INTPOLY_ID; FST; SND] THEN
    ASM_SIMP_TAC[TYPED_HOL_LIST_SLICE_ALL; TYPED_HOL_READ; NATIVE_BIND]);;

let EQ_DECODEDPUBLICKEYSTRINGS_MLDSA44 =
  enc_decoded_pk_gen 4 "44" DecodedPublicKeyStrings_4_MLDSA44_Configuration_body_hol_DEF;;
let EQ_DECODEDPUBLICKEYSTRINGS_MLDSA65 =
  enc_decoded_pk_gen 6 "65" DecodedPublicKeyStrings_6_MLDSA65_Configuration_body_hol_DEF;;
let EQ_DECODEDPUBLICKEYSTRINGS_MLDSA87 =
  enc_decoded_pk_gen 8 "87" DecodedPublicKeyStrings_8_MLDSA87_Configuration_body_hol_DEF;;

let enc_decoded_sk_gen l k p def =
  let pt s = parse_term s and sp = Printf.sprintf in
  let vty n = sp "(%d,fips204_intpoly)common_vec" n in
  let goal = pt(sp
   "!rho kk tr (s1:%s) (s2:%s) (t0:%s).
        LENGTH rho = 32 /\\ LENGTH kk = 32 /\\ LENGTH tr = 64
        ==> DecodedSecretKeyStrings_%d_%d_MLDSA%s_Configuration_body_hol
              (rho,kk,tr,s1,s2,t0) =
            Value (Native_Value (rho,kk,tr,s1,s2,t0))"
   (vty l) (vty k) (vty k) l k p) in
  prove(goal,
    REPEAT STRIP_TAC THEN REWRITE_TAC[def] THEN
    BALL_SIMP_TAC[COMMON_VEC_INTPOLY_ID; FST; SND] THEN
    ASM_SIMP_TAC[TYPED_HOL_LIST_SLICE_ALL; TYPED_HOL_READ; NATIVE_BIND]);;

let EQ_DECODEDSECRETKEYSTRINGS_MLDSA44 =
  enc_decoded_sk_gen 4 4 "44" DecodedSecretKeyStrings_4_4_MLDSA44_Configuration_body_hol_DEF;;
let EQ_DECODEDSECRETKEYSTRINGS_MLDSA65 =
  enc_decoded_sk_gen 5 6 "65" DecodedSecretKeyStrings_5_6_MLDSA65_Configuration_body_hol_DEF;;
let EQ_DECODEDSECRETKEYSTRINGS_MLDSA87 =
  enc_decoded_sk_gen 7 8 "87" DecodedSecretKeyStrings_7_8_MLDSA87_Configuration_body_hol_DEF;;

(* ------------------------------------------------------------------------- *)
(* skDecode (Algorithm 25).                                                  *)
(* ------------------------------------------------------------------------- *)

(* Rewrite each typed_hol_list_slice xs (&A) (&B) of the goal, with A and B  *)
(* linear in the variable k, into SOME (mldsa_slice A' n xs), A' = c0 +      *)
(* c1*k.                                                                     *)
let ENC_SLICE_SOME = prove
 (`!(xs:byte list) l u. l <= u /\ u <= LENGTH xs
      ==> typed_hol_list_slice xs (&l) (&u) = SOME (mldsa_slice l (u - l) xs)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BALL_SLICE; mldsa_slice]);;

let ENC_SLICE_NORM_TAC : tactic =
  fun (asl,w) ->
    let is_slice t =
      match strip_comb t with
        (c,[_;_;_]) -> is_const c && fst(dest_const c) = "typed_hol_list_slice"
      | _ -> false in
    let good e =
      is_comb e && (match rator e with Const("int_of_num",_) -> true | _ -> false) &&
      subset (frees (rand e)) [`k:num`] && type_of (rand e) = `:num` in
    let slices = filter (fun sl ->
      match snd(strip_comb sl) with
        [_;l;u] -> good l && good u
      | _ -> false) (find_terms is_slice w) in
    let kv = `k:num` in
    let ev e n =
      let e' = vsubst [mk_small_numeral n,kv] e in
      if is_numeral e' then e' else rand(concl(NUM_REDUCE_CONV e')) in
    let norm e =
      if not (mem kv (frees e)) then
        let c0 = ev e 0 in mk_comb(mk_comb(`+`,c0),`0`)
      else failwith "x" in
    ignore norm;
    let polys e =
      if mem kv (frees e) then
        let c0 = ev e 0 and c1 = ev e 1 in
        let c0n = dest_numeral c0 and c1n = dest_numeral c1 in
        let d = c1n -/ c0n in
        mk_comb(mk_comb(`(+):num->num->num`,c0),
                mk_comb(mk_comb(`(*):num->num->num`,mk_numeral d),kv)), c0n, d
      else
        let c0 = ev e 0 in c0, dest_numeral c0, num 0 in
    let ths = map (fun sl ->
      match snd(strip_comb sl) with
        [xs;l;u] ->
          let a = rand l and b = rand u in
          let a',_,_ = polys a and b',_,_ = polys b in
          let ea = ARITH_RULE(mk_eq(a,a')) and eb = ARITH_RULE(mk_eq(b,b')) in
          let la = ARITH_RULE(mk_eq(mk_binop `(-):num->num->num` b' a',
                                    let (_,c0a,da) = polys a and (_,c0b,db) = polys b in
                                    if not(da = db) then failwith "slice length not constant"
                                    else mk_numeral(c0b -/ c0a))) in
          ignore la;
          let (_,c0a,da) = polys a and (_,c0b,db) = polys b in
          let len = mk_numeral(c0b -/ c0a) in
          let cond = mk_conj(mk_binop `(<=):num->num->bool` a' b',
                             mk_binop `(<=):num->num->bool` b' (mk_comb(`LENGTH:byte list->num`,xs))) in
          let condth = TAC_PROOF((asl,cond),
                          CONJ_TAC THENL
                           [ARITH_TAC; ASM_ARITH_TAC]) in
          let sth = MP (ISPECL [xs;a';b'] ENC_SLICE_SOME) condth in
          let lth = ARITH_RULE(mk_eq(mk_binop `(-):num->num->num` b' a',len)) in
          let triv th = let (l,r) = dest_eq(concl th) in aconv l r in
          filter (fun th -> not(triv th)) [ea;eb;lth;sth]
      | _ -> failwith "slice") slices in
    ignore ths;
    (REWRITE_TAC(flat ths)) (asl,w);;

let enc_skdecode_gen p k l eta c def bpth =
  let pt s = parse_term s and sp = Printf.sprintf in
  let vt n = sp "(%d,fips204_intpoly)common_vec" n in
  let a1 = 128 and a2 = 128 + 32 * c * l and a3 = 128 + 32 * c * (l + k) in
  let n1 = 32 * c * l and n2 = 32 * c * k and n3 = 416 * k in
  let slen = a3 + n3 in
  let goal = pt(sp
   "!sk. LENGTH sk = %d
        ==> skDecode_MLDSA%s_Configuration_hol sk =
            Value (mldsa_slice 0 32 sk, mldsa_slice 32 32 sk,
                   mldsa_slice 64 64 sk,
                   (lift_vec (\\i. lift_intpoly (\\j. &%d -
                      mldsa_field %d (mldsa_slice %d %d sk) (256 * i + j))):%s),
                   (lift_vec (\\i. lift_intpoly (\\j. &%d -
                      mldsa_field %d (mldsa_slice %d %d sk) (256 * i + j))):%s),
                   (lift_vec (\\i. lift_intpoly (\\j. &4096 -
                      mldsa_field 13 (mldsa_slice %d %d sk) (256 * i + j))):%s))"
   slen p eta c a1 n1 (vt l) eta c a2 n2 (vt k) a3 n3 (vt k)) in
  let inv a nn cc eb n = pt(sp
   "\\k (v:%s). v = lift_vec (\\j. if j < k then lift_intpoly (\\x. &%d -
      mldsa_field %d (mldsa_slice %d %d sk) (256 * j + x)) else lift_intpoly (\\x. &0))"
   (vt n) eb cc a nn) in
  let sch n = SPECL [pt(string_of_int (n + 1)); pt(string_of_int n)]
                    NATIVE_SCHEDULE_NUM in
  let dim n = DIMINDEX_CONV(pt(sp "dimindex(:%d)" n)) in
  let blen = ball_bitlen_fact (2 * eta) c in
  let base = REWRITE_TAC[lift_vec; CONJUNCT1 LT; lift_intpoly; BALL_MAP_REPLICATE;
                         REPLICATE_LIST_OF_SEQ] THEN
             CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN REWRITE_TAC[] in
  let stage n a nn cc unp =
    let fs = SPECL [mk_small_numeral cc; mk_small_numeral a;
                    mk_small_numeral nn; `sk:byte list`; `k:num`; `x:num`]
                   ENC_FIELD_SLICE in
    let bl = ball_bitlen_fact (2 * eta) c in
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[typed_hol_nonnegative_DEF; INT_POS; NATIVE_BIND;
                bitlen_semantic_DEF; ISA_NAT_NUM; bl;
                INT_ARITH `~(&n:int < &0)`] THEN
    CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
    REWRITE_TAC[NATIVE_BIND; BALL_INT_ARITH; INT_POW_ONE; INT_OF_NUM_MUL;
                INT_OF_NUM_ADD; INT_MUL_RID] THEN
    CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
    ENC_SLICE_NORM_TAC THEN
    REWRITE_TAC[TYPED_HOL_READ; NATIVE_BIND] THEN
    ASM_SIMP_TAC[TYPED_HOL_SEQUENCE_EXTENT; LENGTH_MLDSA_SLICE; NATIVE_BIND] THEN
    ASM_SIMP_TAC[unp; LENGTH_MLDSA_SLICE; NATIVE_BIND] THEN
    REWRITE_TAC[typed_hol_nominal_update_DEF; isa_map_option;
                COMMON_VEC_ENTRIES_LIFT; dim n;
                NATIVE_LIST_UPDATE_NUM; LENGTH_LIST_OF_SEQ] THEN
    ASM_REWRITE_TAC[TYPED_HOL_READ; NATIVE_BIND; ISA_LIST_UPDATE_LIST_OF_SEQ;
                    injectivity "native_result"; UNWIND_THM1; ISA_NAT_NUM] THEN
    REWRITE_TAC[isa_map_option; TYPED_HOL_READ; injectivity "native_result";
                UNWIND_THM1] THEN
    REWRITE_TAC[lift_vec; dim n] THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `i:num` THEN
    DISCH_TAC THEN REWRITE_TAC[LT] THEN
    ASM_CASES_TAC `i:num = k` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[lift_intpoly; injectivity "fips204_intpoly"] THEN
      MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `x:num` THEN
      DISCH_TAC THEN BETA_TAC THEN
      MP_TAC fs THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE(pt(sp "32 * %d * k = %d * k" cc (32 * cc)));
                  ARITH_RULE(pt(sp "32 * %d = %d" cc (32 * cc)))] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]);
      POP_ASSUM(fun th -> REWRITE_TAC[th])] in
  let sched n = TRY(MP_TAC(sch n) THEN
                    ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC]) in
  let inv1 = inv a1 n1 c eta l and inv2 = inv a2 n2 c eta k
  and inv3 = pt(sp
   "\\k (v:%s). v = lift_vec (\\j. if j < k then lift_intpoly (\\x. &4096 -
      mldsa_field 13 (mldsa_slice %d %d sk) (256 * j + x)) else lift_intpoly (\\x. &0))"
   (vt k) a3 n3) in
  let bpth4095 = ENC_BITUNPACK_4095 in
  prove(goal,
    REPEAT STRIP_TAC THEN REWRITE_TAC[def] THEN
    BALL_SIMP_TAC[BALL_INT_ARITH; INT_POW_ONE] THEN
    CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
    REWRITE_TAC[NATIVE_BIND] THEN
    ENC_SLICE_NORM_TAC THEN
    REWRITE_TAC[TYPED_HOL_READ; NATIVE_BIND] THEN
    ASM_SIMP_TAC[TYPED_HOL_SEQUENCE_EXTENT; LENGTH_MLDSA_SLICE; NATIVE_BIND] THEN
    sched l THEN
    ENC_FOLDL_TAC inv1 "st1" THENL
     [CONJ_TAC THENL [base; stage l a1 n1 c bpth];
      FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[NATIVE_BIND] THEN
      sched k THEN
      ENC_FOLDL_TAC inv2 "st2" THENL
       [CONJ_TAC THENL [base; stage k a2 n2 c bpth];
        FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[NATIVE_BIND] THEN
        sched k THEN
        ENC_FOLDL_TAC inv3 "st3" THENL
         [CONJ_TAC THENL [base; stage k a3 n3 13 bpth4095];
          FIRST_X_ASSUM SUBST_ALL_TAC THEN
          REWRITE_TAC[NATIVE_BIND; injectivity "native_result"; PAIR_EQ] THEN
          REPEAT CONJ_TAC THEN
          REWRITE_TAC[LIFT_VEC_EQ; dim l; dim k] THEN
          REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]]]);;
let EQ_SKDECODE_MLDSA44 =
  enc_skdecode_gen "44" 4 4 2 3 skDecode_MLDSA44_Configuration_hol_DEF ENC_BITUNPACK_2;;
let EQ_SKDECODE_MLDSA65 =
  enc_skdecode_gen "65" 6 5 4 4 skDecode_MLDSA65_Configuration_hol_DEF ENC_BITUNPACK_4;;
let EQ_SKDECODE_MLDSA87 =
  enc_skdecode_gen "87" 8 7 2 3 skDecode_MLDSA87_Configuration_hol_DEF ENC_BITUNPACK_2;;
