(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas connecting the specifications of the mlkem-native functions to the *)
(* FIPS 203 specification in common/fips203/fips203.ml, for the proofs of    *)
(* the K-PKE and ML-KEM functions. The specifications of the leaf functions  *)
(* use plain arithmetic (congruences mod q = 3329 and bounds on the 16-bit   *)
(* coefficients, numbers for byte arrays, and lists of words), and these     *)
(* lemmas relate them to the definitions of FIPS 203 and to its NTT-domain   *)
(* forms of K-PKE in common/fips203/properties/kpke_ntt_domain.ml.           *)
(* ========================================================================= *)

(* The part that depends on AArch64; the rest is in                          *)
(* common/fips203/properties/mlkem_native_fips203.ml.                        *)

needs "arm/proofs/utils/mlkem_native_image.ml";;
needs "common/mlkem_mldsa.ml";;
needs "common/fips203/properties/fips203_properties.ml";;
needs "common/fips203/properties/mlkem_native_fips203.ml";;

let WORDLIST_FROM_MEMORY_BYTES16 = prove
 (`!a n s (l:int16 list).
        wordlist_from_memory(a,n) s = l
        ==> !i. i < n
                ==> read (memory :> bytes16(word_add a (word(2 * i)))) s =
                    EL i l`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_WORDLIST_FROM_MEMORY; BYTES16_WBYTES] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN REFL_TAC);;

let READ_MEMORY_BYTES16_LIST_OF_SEQ = prove
 (`!a n (f:num->int16) s:armstate.
        (!i. i < n
             ==> read (memory :> bytes16(word_add a (word(2 * i)))) s = f i)
        ==> read (memory :> bytes(a,2 * n)) s =
            num_of_wordlist(list_of_seq f n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL;
                list_of_seq; num_of_wordlist];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC n = 2 * n + 2`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE; list_of_seq] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_APPEND; LENGTH_LIST_OF_SEQ;
              NUM_OF_WORDLIST_SING; DIMINDEX_16] THEN
  BINOP_TAC THENL
   [REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `8 * 2 * n = 16 * n`] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[ARITH_RULE `n < SUC n`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
                DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let READ16_OFFSET_EQ = prove
 (`!a x y s:armstate.
        x = y
        ==> read (memory :> bytes16(word_add a (word x))) s =
            read (memory :> bytes16(word_add a (word y))) s`,
  SIMP_TAC[]);;

let READ_MEMORY_BYTES_1 = prove
 (`!a s:armstate.
        read (memory :> bytes(a,1)) s = val(read (memory :> bytes8 a) s)`,
  REWRITE_TAC[BYTES8_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let READ_MEMORY_BYTES_SLICE = prove
 (`!a (l:byte list) k n s:armstate.
        read (memory :> bytes(a,LENGTH l)) s = num_of_bytelist l /\
        k + n <= LENGTH l
        ==> read (memory :> bytes(word_add a (word k),n)) s =
            num_of_bytelist(mlkem_slice k n l)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_SLICE_NUM] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

let MLKEM_NATIVE_SAMPLE_COEFF = prove
 (`!a s b k n.
        256 <= LENGTH(FILTER (\x. val x < 3329)
                 (MAP (word_zx:12 word->16 word)
                   (wordlist_of_num (336 + 112 * k)
                     (num_of_bytelist
                       (list_of_seq (shake128 b) (504 + 168 * k)))))) /\
        wordlist_from_memory(a,256) s =
        SUB_LIST(0,256)
         (FILTER (\x. val x < 3329)
           (MAP (word_zx:12 word->16 word)
             (wordlist_of_num (336 + 112 * k)
               (num_of_bytelist
                 (list_of_seq (shake128 b) (504 + 168 * k)))))) /\
        n < 256
        ==> ival(read (memory :> bytes16(word_add a (word(2 * n)))) s) =
            mlkem_sample_ntt b n`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[MATCH_MP WORDLIST_FROM_MEMORY_BYTES16 th]) THEN
  ASM_SIMP_TAC[MLKEM_SAMPLE_NTT_REJ] THEN MATCH_MP_TAC IVAL_VAL_SMALL THEN
  MATCH_MP_TAC(ARITH_RULE `x < 3329 ==> x < 32768`) THEN
  MATCH_MP_TAC MLKEM_SAMPLE_NTT_REJ_EL THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The hash function G, encoding of coefficients mod q, compression and      *)
(* decompression.                                                            *)
(* ------------------------------------------------------------------------- *)

let MLKEM_G_BYTES = prove
 (`!a c s:armstate.
        read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 c)
        ==> read (memory :> bytes(a,32)) s =
            num_of_bytelist(FST(mlkem_g c)) /\
            read (memory :> bytes(word_add a (word 32),32)) s =
            num_of_bytelist(SND(mlkem_g c))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `64`; `32`; `read memory (s:armstate)`]
                READ_BYTES_MOD) THEN
  MP_TAC(ISPECL [`a:int64`; `64`; `32`; `read memory (s:armstate)`]
                READ_BYTES_DIV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 64 32 = 32 /\ 64 - 32 = 32`] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[mlkem_g; mlkem_slice; sha3_512; ADD_CLAUSES] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `i < 32 ==> i < 64 /\ 32 + i < 64`;
           LIST_OF_SEQ_EQ] THEN
  REWRITE_TAC[ARITH_RULE `64 = 32 + 32`;
              NUM_OF_BYTELIST_LIST_OF_SEQ_SPLIT] THEN
  MP_TAC(ISPEC `list_of_seq (keccak_sponge 1024 6 c) 32`
                NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; EXP_EQ_0; ARITH_EQ;
               ADD_CLAUSES] THEN
  CONJ_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
  SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `i < 32 ==> i < 64 /\ i + 32 < 64`] THEN
  REWRITE_TAC[ADD_SYM]);;

let NONOVERLAPPING_ZERO_NONZERO = prove
 (`!a:int64 n k.
        nonoverlapping (word 0:int64,1) (a,n) /\ k < n
        ==> ~(word_add a (word k) = word 0)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; nonoverlapping_modulo] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD; VAL_WORD_0;
              DIMINDEX_64] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`0`; `k:num`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < 1`; ADD_CLAUSES] THEN
  REWRITE_TAC[CONG] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[ADD_MOD_MOD_REFL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let ASSIGNS_MEMORY_BYTES_0 = prove
 (`!a:int64.
        ASSIGNS (memory :> bytes(a,0)) = ((=):armstate->armstate->bool)`,
  GEN_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; ASSIGNS_THM; WRITE_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 bytes))] THEN
  MP_TAC(REWRITE_RULE[EXTENSIONALLY_VALID_COMPONENT]
   (EXTENSIONALLY_VALID_COMPONENT_CONV
     `extensionally_valid_component
       (memory:(armstate,int64->byte)component)`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;
