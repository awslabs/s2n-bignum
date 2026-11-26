(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the proofs of the API functions of the clang 23 -O3 build of   *)
(* mldsa-native, which inline mld_prepare_domain_separation_prefix for pure  *)
(* ML-DSA: it stores the bytes 0 and ctxlen and copies the context with      *)
(* memcpy, so that the prefix is the bytes 0 || ctxlen || ctx that the       *)
(* statements state as mld_domain_separation_prefix 0 ctx [].                *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_api.ml";;

(* ------------------------------------------------------------------------- *)
(* The 2 + ctxlen bytes at p, given the bytes 0 and ctxlen at p and p + 1    *)
(* and the context at p + 2, as a number.                                    *)
(* ------------------------------------------------------------------------- *)

let API_WORD_MOD_256 = prove
 (`!n. word (n MOD 256):byte = word n`,
  GEN_TAC THEN MP_TAC(ISPEC `n:num` (INST_TYPE [`:8`,`:N`] WORD_MOD_SIZE)) THEN
  REWRITE_TAC[DIMINDEX_8; ARITH_RULE `2 EXP 8 = 256`]);;

let API_PREFIX_BYTES = prove
 (`!(s:x86state) p ctxlen C.
        ctxlen <= 255 /\
        read (memory :> bytes8 p) s = word 0 /\
        read (memory :> bytes8 (word_add p (word 1))) s = word ctxlen /\
        read (memory :> bytes(word_add p (word 2),ctxlen)) s = C
        ==> read (memory :> bytes(p,2 + ctxlen)) s =
            num_of_bytelist
             (mld_domain_separation_prefix 0 (bytelist_of_num ctxlen C) [])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix; LENGTH_BYTELIST_OF_NUM;
              num_of_bytelist; NUM_OF_BYTELIST_OF_NUM; VAL_WORD_0] THEN
  SUBGOAL_THEN `val(word ctxlen:byte) = ctxlen` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `C MOD 256 EXP ctxlen = C` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPECL [`word_add p (word 2):int64`; `ctxlen:num`;
                   `read memory (s:x86state)`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes(p,2)) (s:x86state) = 256 * ctxlen`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 = 1 + 1`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    REWRITE_TAC[READ_MEMORY_BYTES_BYTES8] THEN
    ASM_REWRITE_TAC[VAL_WORD_0] THEN
    SUBGOAL_THEN `val(word ctxlen:byte) = ctxlen` SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
      MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The flags that CMP r8, 0xff sets decide JA as ctxlen <= 255 does.         *)
(* ------------------------------------------------------------------------- *)

let API_JA_255 = prove
 (`!n. n < 2 EXP 64
       ==> ((val(word n:int64) < 255 \/
             val(word_sub (word n:int64) (word 255)) = 0) <=> n <= 255)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word n:int64) = n` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64];
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
  SUBGOAL_THEN `val(word n:int64) = n` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word 255:int64) = 255` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_CASES_TAC `255 <= n` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The contract of memset states each byte of its result for a symbolic      *)
(* index, which makes every later store to the stack expensive to simulate:  *)
(* the fact about the bytes at i must be carried over the store for every i. *)
(* API_MEMSET_BYTES_TAC replaces it, for memset of 0, by the zero bytes as a *)
(* number (read (memory :> bytes(a,len)) s = 0), which is a single fact; the *)
(* individual bytes follow by SIGN_BYTES8_ZERO of utils/mldsa_native_signing *)
(* .ml when they are needed.                                                 *)
(* ------------------------------------------------------------------------- *)

let API_BYTES_ZERO_OF_BYTES8 = prove
 (`!(a:int64) n (s:x86state).
        (!i. i < n ==> read (memory :> bytes8 (word_add a (word i))) s = word 0)
        ==> read (memory :> bytes(a,n)) s = 0`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]; ALL_TAC] THEN
  X_GEN_TAC `s:x86state` THEN DISCH_TAC THEN
  REWRITE_TAC[ADD1; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[READ_MEMORY_BYTES_BYTES8] THEN
  SUBGOAL_THEN `read (memory :> bytes8 (word_add a (word n))) (s:x86state) =
                word 0` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[LT]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes(a,n)) (s:x86state) = 0` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s:x86state`) THEN ANTS_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
      ASM_SIMP_TAC[LT];
      DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES]);;

let API_MEMSET_ZERO = prove
 (`!(a:int64) (c:int64) (len:int64) (s:x86state).
        (!i. i < val len
             ==> read (memory :> bytes8 (word_add a (word i))) s = word_zx c) /\
        c = word 0
        ==> read (memory :> bytes(a,val len)) s = 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC API_BYTES_ZERO_OF_BYTES8 THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

let API_MEMSET_BYTES_TAC =
  FIRST_X_ASSUM(fun th ->
    if can (term_match []
         `!i. i < (n:num)
              ==> read (memory :> bytes8 (word_add (a:int64) (word i))) s =
                  (word_zx (word 0:int64):byte)`) (concl th)
    then ASSUME_TAC(MATCH_MP API_BYTES_ZERO_OF_BYTES8
           (CONV_RULE(ONCE_DEPTH_CONV WORD_REDUCE_CONV) th))
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* An aligned SSE store [rsp + n] after a call of memset: the simulator      *)
(* decides the alignment of the address as it forms it from the state after  *)
(* the call, and only finds the fact if it has that exact form (otherwise    *)
(* X86_FORCE_CONDITIONAL_CONV does not terminate). This adds the fact for    *)
(* the offset n of the frame pointer bot + 12102 in the forms word_add       *)
(* (read RSP s) (word n) and word_add (word_add bot (word 12102)) (word n),  *)
(* from the fact about the sum.                                              *)
(* ------------------------------------------------------------------------- *)

let API_ALIGN_TAC sname r n =
  let nt = mk_small_numeral n and rt = mk_small_numeral r in
  let st = mk_var(sname,`:x86state`) in
  let rsp = mk_comb(`read RSP`,st) in
  let f1 = subst [nt,`n:num`; rt,`r:num`]
     `aligned 16 (word_add (word_add bot (word r)) (word n):int64)` in
  let f2 = subst [nt,`n:num`; rsp,`x:int64`]
     `aligned 16 (word_add x (word n):int64)` in
  SUBGOAL_THEN f1 ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_add (word_add a (word x)) (word y) =
                           word_add a (word (x + y))`] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN f2 ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    TRY(REWRITE_TAC[WORD_RULE `word_add (word_add a (word x)) (word y) =
                               word_add a (word (x + y))`] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN FIRST_ASSUM ACCEPT_TAC);
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The prefix of HashML-DSA with the SHAKE256 pre-hash (hashalg = 12), for   *)
(* the functions that inline mld_prepare_domain_separation_prefix with it:   *)
(* the 2 + ctxlen + 11 + 64 bytes at p, given the bytes 1 and ctxlen at p    *)
(* and p + 1, the context at p + 2, the 11 bytes of the OID after it and the *)
(* pre-hash after those.                                                     *)
(* ------------------------------------------------------------------------- *)

let API_HASH_PREFIX_BYTES = prove
 (`!(s:x86state) p ctxlen C PH.
        ctxlen <= 255 /\
        read (memory :> bytes8 p) s = word 1 /\
        read (memory :> bytes8 (word_add p (word 1))) s = word ctxlen /\
        read (memory :> bytes(word_add p (word 2),ctxlen)) s = C /\
        read (memory :> bytes(word_add p (word (2 + ctxlen)),11)) s =
          num_of_bytelist(mld_prehash_oid 12) /\
        read (memory :> bytes(word_add p (word (2 + ctxlen + 11)),64)) s = PH
        ==> read (memory :> bytes(p,2 + ctxlen + 11 + 64)) s =
            num_of_bytelist
             (mld_domain_separation_prefix 12 (bytelist_of_num ctxlen C)
               (bytelist_of_num 64 PH))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix; LENGTH_BYTELIST_OF_NUM;
              num_of_bytelist; NUM_OF_BYTELIST_APPEND; LENGTH_APPEND;
              NUM_OF_BYTELIST_OF_NUM; ARITH_EQ] THEN
  SUBGOAL_THEN `LENGTH(mld_prehash_oid 12) = 11` ASSUME_TAC THENL
   [REWRITE_TAC[mld_prehash_oid; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word ctxlen:byte) = ctxlen` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C MOD 256 EXP ctxlen = C` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPECL [`word_add p (word 2):int64`; `ctxlen:num`; `read memory (s:x86state)`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `PH MOD 256 EXP 64 = PH` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPECL [`word_add p (word (2 + ctxlen + 11)):int64`; `64`; `read memory (s:x86state)`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes(p,2)) (s:x86state) = 1 + 256 * ctxlen` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 = 1 + 1`; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    REWRITE_TAC[READ_MEMORY_BYTES_BYTES8] THEN
    ASM_REWRITE_TAC[VAL_WORD_1] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `2 + ctxlen + 11 = (2 + ctxlen) + 11`]) THEN
  REWRITE_TAC[ARITH_RULE `2 + ctxlen + 11 + 64 = ((2 + ctxlen) + 11) + 64`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[VAL_WORD_1] THEN
  REWRITE_TAC[ARITH_RULE `8 * (2 + ctxlen) = 16 + 8 * ctxlen`;
              ARITH_RULE `8 * ((2 + ctxlen) + 11) = 104 + 8 * ctxlen`;
              ARITH_RULE `8 * 11 = 88`; EXP_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUM_RING);;

(* ------------------------------------------------------------------------- *)
(* The pieces of that prefix as the stores of the code leave them: the OID   *)
(* from a store of 8 bytes and one of 4 bytes that overlap in one byte (the  *)
(* first as its 7 bytes, as the simulator forgets it after the second), and  *)
(* the pre-hash from the four stores of 16 bytes.                            *)
(* ------------------------------------------------------------------------- *)

let API_BYTES8_OF_BYTES64 = prove
 (`!(a:int64) (s:x86state) x.
        read (memory :> bytes64 a) s = word x /\ x < 2 EXP 64
        ==> read (memory :> bytes(a,8)) s = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(AP_TERM `val:int64->num` (ASSUME `read (memory :> bytes64 a) s = word x`)) THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `x MOD 18446744073709551616 = x` ASSUME_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `x < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;
let API_BYTES4_OF_BYTES32 = prove
 (`!(a:int64) (s:x86state) x.
        read (memory :> bytes32 a) s = word x /\ x < 2 EXP 32
        ==> read (memory :> bytes(a,4)) s = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(AP_TERM `val:int32->num` (ASSUME `read (memory :> bytes32 a) s = word x`)) THEN
  REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `x MOD 4294967296 = x` ASSUME_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `x < 2 EXP 32` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;
let API_BYTES7_OF_BYTES64 = prove
 (`!(a:int64) (s:x86state) x.
        read (memory :> bytes64 a) s = word x /\ x < 2 EXP 64
        ==> read (memory :> bytes(a,7)) s = x MOD 2 EXP 56`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `8`; `x:num`; `0`; `7`; `s:x86state`] READ_MEMORY_BYTES_SUB) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [MATCH_MP_TAC API_BYTES8_OF_BYTES64 THEN ASM_REWRITE_TAC[]; ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; EXP; DIV_1] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;
let API_OID12_BYTES = prove
 (`!(a:int64) (s:x86state).
        read (memory :> bytes(a,7)) s = 244603165765273862 MOD 2 EXP 56 /\
        read (memory :> bytes32 (word_add a (word 7))) s = word 201458691
        ==> read (memory :> bytes(a,11)) s = num_of_bytelist(mld_prehash_oid 12)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`word_add a (word 7):int64`; `s:x86state`; `201458691`] API_BYTES4_OF_BYTES32) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `11 = 7 + 4`; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mld_prehash_oid; num_of_bytelist; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV);;
