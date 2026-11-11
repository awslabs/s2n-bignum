(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the proofs of mldsa-native's Keccak code that do not depend on *)
(* the build, as in arm/proofs/utils/mldsa_native_keccak.ml, with the tools  *)
(* for byte arrays, Keccak states as 1600-bit words and 32-bit arguments     *)
(* that the AArch64 proofs take from arm/proofs/utils/mlkem_native_image.ml, *)
(* here for the x86 state, as in the x86 proofs of mlkem-native. The tools   *)
(* for the memset that gcc inlines with REP STOSQ, which the AArch64 code    *)
(* does not use, are in x86/proofs/utils/mldsa_native_memset.ml.             *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native.ml";;

let READ_MEMORY_BYTES_SNOC = prove
 (`!x:int64 n s:x86state.
        read (memory :> bytes(x,n + 1)) s =
        read (memory :> bytes(x,n)) s +
        2 EXP (8 * n) * val(read (memory :> bytes8(word_add x (word n))) s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; READ_BYTES_BYTES8]);;

(* ------------------------------------------------------------------------- *)
(* Byte arrays. As in common/fips202.ml, the contents of a byte array are    *)
(* given as a number n, and READ_MEMORY_BYTES8_OF_NUM gives its bytes;       *)
(* READ_MEMORY_BYTES_OF_BYTES8 gives the array from its bytes.               *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES8_OF_NUM = prove
 (`!a:int64 m n k s:x86state.
        read (memory :> bytes(a,m)) s = n /\ k < m
        ==> read (memory :> bytes8(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 256)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES8_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP (8 * 1)`; READ_BYTES_DIV;
              READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES_OF_BYTES8 = prove
 (`!a:int64 n x s:x86state.
        (!j. j < n
             ==> read (memory :> bytes8(word_add a (word j))) s =
                 word((x DIV 2 EXP (8 * j)) MOD 256))
        ==> read (memory :> bytes(a,n)) s = x MOD 2 EXP (8 * n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ADD1; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE;
              READ_BYTES_BYTES8] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `s:x86state`]) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `j < n ==> j < SUC n`];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[LT] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL; LEFT_ADD_DISTRIB; MULT_CLAUSES; EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; MOD_MULT_MOD] THEN ARITH_TAC);;

let WORD_VAL_MOD_256 = prove
 (`!x:N word. word (val x MOD 256):byte = word_zx x`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN
  REWRITE_TAC[GSYM DIMINDEX_8; WORD_MOD_SIZE; word_zx]);;

(* ------------------------------------------------------------------------- *)
(* A word in memory as the number of its bytes, and the case of a Keccak     *)
(* state of 200 bytes. KECCAK_STATE_WBYTES_TAC sv restates the fact that the *)
(* bytes of a state are val sv in the wbytes form, for a call.               *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_WBYTES_VAL = prove
 (`!a:int64 (x:N word) s:x86state.
        read (memory :> wbytes a) s = x <=>
        read (memory :> bytes(a,dimindex(:N) DIV 8)) s = val x`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM VAL_EQ] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES]);;

let READ_MEMORY_WBYTES_1600 =
  CONV_RULE(DEPTH_CONV DIMINDEX_CONV THENC ONCE_DEPTH_CONV NUM_DIV_CONV)
   (INST_TYPE [`:1600`,`:N`] READ_MEMORY_WBYTES_VAL);;

let KECCAK_STATE_WBYTES_TAC sv =
  let pat = subst [sv,`S:1600 word`]
   `read (memory :> bytes (a,200)) s = val(S:1600 word)` in
  FIRST_ASSUM(fun th ->
    if can (term_match [sv] pat) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600] th)
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Unsigned 32-bit arguments word n, as the code zero-extends them, and a    *)
(* 32-bit argument on the stack, which the caller stores as a 64-bit word:   *)
(* STACK_ARG32_TAC a gives the bytes32 at a from the fact for its bytes64.   *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_32_SMALL = prove
 (`!n. n < 2 EXP 32
       ==> word_zx(word_zx(word n:int64):int32):int64 = word n /\
           val(word_zx(word n:int64):int32) = n /\
           word_zx(word n:int32):int64 = word n`,
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN TRY(ONCE_REWRITE_TAC[GSYM VAL_EQ]) THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `n < 4294967296 ==> n < 18446744073709551616`]);;

let ARGS_32_TAC ns =
  MAP_EVERY (fun n ->
    MP_TAC(SPEC n WORD_ZX_32_SMALL) THEN
    ANTS_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))]) ns;;

let READ_MEMORY_BYTES32_OF_BYTES64 = prove
 (`!a:int64 n s:x86state.
        read (memory :> bytes64 a) s = word n /\ n < 2 EXP 32
        ==> read (memory :> bytes32 a) s = word n`,
  REPEAT GEN_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int64->num`) THEN
  REWRITE_TAC[BYTES64_WBYTES; BYTES32_WBYTES; READ_COMPONENT_COMPOSE;
              VAL_READ_WBYTES; VAL_WORD; DIMINDEX_64; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `n < 4294967296 ==> n < 18446744073709551616`] THEN
  DISCH_THEN(MP_TAC o C AP_THM `2 EXP (8 * 4)` o AP_TERM `(MOD)`) THEN
  REWRITE_TAC[READ_BYTES_MOD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT]);;

let STACK_ARG32_TAC a =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes64",_),aa))),_)),
           Comb(Const("word",_),n)) when aa = a ->
        SUBGOAL_THEN (mk_binop `(<):num->num->bool` n `2 EXP 32`)
         (fun lth -> ASSUME_TAC
            (MATCH_MP READ_MEMORY_BYTES32_OF_BYTES64 (CONJ th lth))) THENL
         [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC]
    | _ -> NO_TAC);;
