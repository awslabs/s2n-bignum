(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics for the proofs of the ML-KEM functions of mlkem-native *)
(* in the gcc 12 -O2 image, such as mlkem768_dec: the lengths of the results *)
(* of the algorithms of FIPS 203 and the forms of its internal ML-KEM        *)
(* algorithms used in the proofs, copies of 32-byte values as two 128-bit    *)
(* words, the constant-time comparison of byte arrays 16 bytes at a time,    *)
(* and the conditional move of 32 bytes one byte at a time.                  *)
(* ========================================================================= *)

(* The part that depends on AArch64; the rest is in                          *)
(* common/fips203/properties/mlkem_native_kem.ml.                            *)

needs "common/layout.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/utils/mlkem_native_fips203.ml";;
needs "common/fips203/properties/mlkem_native_kem.ml";;

let KEM_LABELS_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memset_contract mf ea el ev`) (concl th)
    then LABEL_TAC "H_MEMSET" (REWRITE_RULE[memset_contract] th)
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memcpy_contract mc ea el ev`) (concl th)
    then LABEL_TAC "H_MEMCPY" (REWRITE_RULE[memcpy_contract] th)
    else NO_TAC);;

let KEM_GOT_TAC gl =
  let pat n = subst [mk_small_numeral n,`n:num`]
   `read (memory :> bytes64 (word_add (word pc) (word n):int64)) s =
    (g:int64)` in
  MAP_EVERY (fun n ->
    TRY(FIRST_ASSUM(fun th ->
      if can (term_match [] (pat n)) (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC)))
   (map layout
      ["got_stack_chk_guard"; "got_memset"; "got_memcpy"]) gl;;

let KEM_BYTES128_HALVES = prove
 (`!a:int64 n s:armstate.
        read (memory :> bytes(a,32)) s = n
        ==> read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
            read (memory :> bytes128(word_add a (word 16))) s =
            word(n DIV 2 EXP 128)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 =
                          2 EXP (8 * 16)`; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let KEM_BYTES_32_OF_HALVES = prove
 (`!a:int64 n s:armstate.
        n < 2 EXP 256 /\
        read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(n DIV 2 EXP 128)
        ==> read (memory :> bytes(a,32)) s = n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `32 = 16 + 16`; READ_BYTES_COMBINE] THEN
  MP_TAC(ISPECL [`a:int64`; `16`; `read memory s`] READ_BYTES_BOUND) THEN
  MP_TAC(ISPECL [`word_add a (word 16):int64`; `16`; `read memory s`]
                READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n DIV 340282366920938463463374607431768211456 <
                340282366920938463463374607431768211456`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [UNDISCH_TAC `n < 2 EXP 256` THEN SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    MESON_TAC[DIVISION_SIMP; ADD_SYM; MULT_SYM]]);;

let KEM_HALVES_TAC a =
  FIRST_ASSUM(MP_TAC o MATCH_MP KEM_BYTES128_HALVES o check
   (can (term_match [] (subst [a,`a:int64`]
     `read (memory :> bytes(a,32)) s = n`)) o concl)) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC;;

let KEM_JOIN_TAC a l s =
  MP_TAC(SPECL [a; mk_comb(`num_of_bytelist`,l);
                mk_var(s,`:armstate`)] KEM_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC l NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* The constant-time comparison of two byte arrays: the 16 bytes at a time   *)
(* of the two arrays XORed together are ORed into one accumulator (and XORed *)
(* into another), which is zero if and only if the prefixes so far are       *)
(* equal.                                                                    *)
(* ------------------------------------------------------------------------- *)

let KEM_BYTES128 = prove
 (`!a l k n s:armstate.
        read (memory :> bytes(a,l)) s = n /\ 16 * k + 16 <= l
        ==> read (memory :> bytes128(word_add a (word(16 * k)))) s =
            word((n DIV 2 EXP (128 * k)) MOD 2 EXP 128)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `128 * k = 8 * 16 * k`; READ_BYTES_DIV] THEN
  REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 =
                          2 EXP (8 * 16)`; READ_BYTES_MOD; MOD_MOD_REFL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

let KEM_OR_STEP = prove
 (`!q:int128 a b.
        word_or
         (word_xor (word(a MOD 340282366920938463463374607431768211456))
                   (word(b MOD 340282366920938463463374607431768211456)))
         q = word 0 <=>
        q = word 0 /\ b MOD 2 EXP 128 = a MOD 2 EXP 128`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[VAL_EQ; CONJ_ACI; EQ_SYM_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The conditional move of 32 bytes, one byte at a time with a mask from the *)
(* comparison: the bytes of a value from offset i, the extension of a prefix *)
(* by one byte, the addresses of the bytes as computed by the code, and its  *)
(* loop test.                                                                *)
(* ------------------------------------------------------------------------- *)

let KEM_SPLIT1 = prove
 (`!a l x s:armstate.
        read (memory :> bytes(a,l + 1)) s = x
        ==> read (memory :> bytes8 a) s = word(x MOD 256) /\
            read (memory :> bytes(word_add a (word 1),l)) s = x DIV 256`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP (8 * 1)`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD; READ_BYTES_DIV] THEN
  REWRITE_TAC[ARITH_RULE `MIN (l + 1) 1 = 1`;
              ARITH_RULE `(l + 1) - 1 = l`] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_1; WORD_VAL]);;

let KEM_CMOV_TEST = prove
 (`!i. i < 32
       ==> (val(word_add (word (i + 1)) (word 18446744073709551584):int64) =
            0 <=> ~(i + 1 < 32))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `(i + 1) MOD 18446744073709551616 = i + 1` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `i + 1 < 32` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(ARITH_RULE `~(x = 0) /\ x MOD n = x ==> ~(x MOD n = 0)`) THEN
    CONJ_TAC THENL [ARITH_TAC; MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC];
    SUBGOAL_THEN `i + 1 = 32` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

(* ------------------------------------------------------------------------- *)
(* The random bytes written by randombytes, as the seeds d and z (64 bytes)  *)
(* or as the message m (32 bytes) of the algorithms of FIPS 203.             *)
(* ------------------------------------------------------------------------- *)

let KEM_RANDOM_SPLIT = prove
 (`!a:int64 n s:armstate.
        read (memory :> bytes(a,64)) s = n
        ==> read (memory :> bytes(a,32)) s =
            num_of_bytelist(bytelist_of_num 32 (n MOD 2 EXP 256)) /\
            read (memory :> bytes(word_add a (word 32),32)) s =
            num_of_bytelist(bytelist_of_num 32 (n DIV 2 EXP 256))`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[NUM_OF_BYTELIST_OF_NUM] THEN
  REWRITE_TAC[ARITH_RULE `256 EXP 32 = 2 EXP (8 * 32)`;
              ARITH_RULE `2 EXP 256 = 2 EXP (8 * 32)`] THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD; READ_BYTES_DIV] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPECL [`word_add a (word 32):int64`; `32`; `read memory s`]
                READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let KEM_RANDOM_32 = prove
 (`!a:int64 n s:armstate.
        read (memory :> bytes(a,32)) s = n
        ==> num_of_bytelist(bytelist_of_num 32 n) = n`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[NUM_OF_BYTELIST_OF_NUM] THEN MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  MP_TAC(ISPECL [`a:int64`; `32`; `read memory s`] READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;
