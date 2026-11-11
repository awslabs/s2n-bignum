(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tools for the top-level functions of mldsa-native's x86-64     *)
(* code, as for AArch64 (arm/proofs/utils/mldsa_native_top.ml): bytes of     *)
(* memory as lists of bytes and as 128-bit chunks, and the folds of the      *)
(* constant-time comparison mld_ct_memcmp (ct.h), which the code vectorizes  *)
(* 16 bytes at a time, accumulating the OR and the XOR of the differences;   *)
(* and the proof of the FULL theorems for mld_sign_pk_from_sk                *)
(* (PFS_FULL_TAC).                                                           *)
(* ========================================================================= *)

needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;
needs "x86/proofs/utils/mldsa_native_scalar.ml";;
needs "x86/proofs/utils/mldsa_native_hints.ml";;
needs "x86/proofs/utils/mldsa_native_memset.ml";;
needs "x86/proofs/utils/mldsa_native_wrap.ml";;
needs "x86/proofs/utils/keccak_fips202.ml";;

(* ------------------------------------------------------------------------- *)
(* Bytes of memory as lists of bytes and as 128-bit chunks, and the folds of *)
(* the comparison, as for AArch64.                                           *)
(* ------------------------------------------------------------------------- *)

let READ_BYTES_OF_BYTES8 = prove
 (`!(a:int64) n (f:num->byte) s.
        (!j. j < n ==> read(memory :> bytes8(word_add a (word j))) s = f j)
        ==> read(memory :> bytes(a,n)) s = num_of_bytelist(list_of_seq f n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[list_of_seq; num_of_bytelist; READ_COMPONENT_COMPOSE;
                READ_BYTES_TRIVIAL];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ADD1; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; GSYM ADD1; list_of_seq;
              NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`f:num->byte`; `s:x86state`]) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[num_of_bytelist; READ_MEMORY_BYTES_BYTES8; MULT_CLAUSES;
              ADD_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LT] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let mld_chunk128 = new_definition
 `mld_chunk128 (f:num->byte) i =
    word(num_of_bytelist(list_of_seq (\k. f(16 * i + k)) 16)):int128`;;

let BYTES128_OF_BYTES8 = prove
 (`!(a:int64) n (f:num->byte) s i.
        (!j. j < n ==> read(memory :> bytes8(word_add a (word j))) s = f j) /\
        16 * i + 16 <= n
        ==> read(memory :> bytes128(word_add a (word(16 * i)))) s =
            mld_chunk128 f i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_chunk128] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `list_of_seq (\k. (f:num->byte)(16 * i + k)) 16`
         NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  MATCH_MP_TAC READ_BYTES_OF_BYTES8 THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC);;

let mld_or_fold = define
 `(mld_or_fold (a:num->int128) b 0 = word 0) /\
  (mld_or_fold a b (SUC i) =
     word_or (mld_or_fold a b i) (word_xor (a i) (b i)))`;;

let mld_xor_fold = define
 `(mld_xor_fold (a:num->int128) b 0 = word 0) /\
  (mld_xor_fold a b (SUC i) =
     word_xor (mld_xor_fold a b i) (word_xor (a i) (b i)))`;;

let MLD_OR_FOLD_EQ_0 = prove
 (`!(a:num->int128) b n.
        mld_or_fold a b n = word 0 <=> !i. i < n ==> a i = b i`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[mld_or_fold; LT] THEN
  REWRITE_TAC[WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[]);;

let WORD_NUM_OF_BYTELIST_16_EQ = prove
 (`!l1 l2:byte list.
        LENGTH l1 = 16 /\ LENGTH l2 = 16
        ==> ((word(num_of_bytelist l1):int128) = word(num_of_bytelist l2) <=>
             l1 = l2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  MP_TAC(ISPEC `l1:byte list` NUM_OF_BYTELIST_BOUND) THEN
  MP_TAC(ISPEC `l2:byte list` NUM_OF_BYTELIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN
  DISCH_THEN(MP_TAC o AP_TERM `bytelist_of_num 16`) THEN
  ASM_MESON_TAC[BYTELIST_OF_NUM_OF_BYTELIST]);;

let MLD_CHUNK128_EQ = prove
 (`!(f:num->byte) g n.
        (!i. i < n ==> mld_chunk128 f i = mld_chunk128 g i) <=>
        (!j. j < 16 * n ==> f j = g j)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[mld_chunk128; WORD_NUM_OF_BYTELIST_16_EQ; LENGTH_LIST_OF_SEQ] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j DIV 16`) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `EL (j MOD 16):byte list->byte`) THEN
    SIMP_TAC[EL_LIST_OF_SEQ; MOD_LT_EQ; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `16 * j DIV 16 + j MOD 16 = j`];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC]);;

let LIST_OF_SEQ_ADD_GEN = prove
 (`!(f:num->A) m n.
        list_of_seq f (m + n) =
        APPEND (list_of_seq f m) (list_of_seq (\k. f(m + k)) n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; list_of_seq; APPEND_NIL; APPEND_ASSOC]);;

let VAL_MLD_CHUNK128 = prove
 (`!(f:num->byte) i.
        val(mld_chunk128 f i) =
        num_of_bytelist(list_of_seq (\k. f(16 * i + k)) 16)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_chunk128; VAL_WORD; DIMINDEX_128] THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `list_of_seq (\k. (f:num->byte)(16 * i + k)) 16`
         NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let MLD_BYTES32_OF_CHUNKS = prove
 (`!a:int64 (f:num->byte) s.
        read (memory :> bytes128 a) s = mld_chunk128 f 0 /\
        read (memory :> bytes128 (word_add a (word 16))) s = mld_chunk128 f 1
        ==> read (memory :> bytes(a,32)) s = num_of_bytelist(list_of_seq f 32)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN (MP_TAC o AP_TERM `val:int128->num`)) THEN
  REWRITE_TAC[VAL_MLD_CHUNK128; BYTES128_WBYTES; READ_COMPONENT_COMPOSE;
              VAL_READ_WBYTES; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; ETA_AX] THEN
  REPEAT DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `32 = 16 + 16`; READ_BYTES_COMBINE] THEN
  ASM_REWRITE_TAC[LIST_OF_SEQ_ADD_GEN; NUM_OF_BYTELIST_APPEND;
                  LENGTH_LIST_OF_SEQ]);;

let WORD_ZX_ZX_ZX_32 = prove
 (`!x:int32. word_zx(word_zx(word_zx x:int64):int32):int64 = word_zx x`,
  CONV_TAC WORD_BLAST);;

let PFS_DIVMOD_LEMMA = prove
 (`!B x y u v. x < B /\ y < B /\ x + B * u = y + B * v ==> x = y /\ u = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x + B * u) MOD B = (y + B * v) MOD B /\
                (x + B * u) DIV B = (y + B * v) DIV B` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(B = 0)` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES]);;

let BYTES8_OF_BYTES = prove
 (`!(a:int64) n (f:num->byte) s.
        read(memory :> bytes(a,n)) s = num_of_bytelist(list_of_seq f n)
        ==> !j. j < n ==> read(memory :> bytes8(word_add a (word j))) s = f j`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LT] THEN
  MAP_EVERY X_GEN_TAC [`f:num->byte`; `s:x86state`] THEN
  REWRITE_TAC[ADD1; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; GSYM ADD1; list_of_seq;
              NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ] THEN
  REWRITE_TAC[num_of_bytelist; READ_MEMORY_BYTES_BYTES8; MULT_CLAUSES;
              ADD_CLAUSES] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`2 EXP (8 * n)`;
                `read(memory :> bytes(a,n)) s`;
                `num_of_bytelist(list_of_seq (f:num->byte) n)`;
                `val(read(memory :> bytes8(word_add a (word n))) s)`;
                `val((f:num->byte) n)`] PFS_DIVMOD_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
      MP_TAC(ISPEC `list_of_seq (f:num->byte) n` NUM_OF_BYTELIST_BOUND) THEN
      REWRITE_TAC[LENGTH_LIST_OF_SEQ; EXP_MULT] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`f:num->byte`; `s:x86state`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `j:num` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* More of the same: the folds one step further, the comparison as a         *)
(* predicate, 64 bytes as four chunks, the 32 bytes of two chunks, and two   *)
(* byte strings one after the other.                                         *)
(* ------------------------------------------------------------------------- *)

let MLD_OR_FOLD_ADD1 = prove
 (`!(a:num->int128) b i.
        mld_or_fold a b (i + 1) =
        word_or (mld_or_fold a b i) (word_xor (a i) (b i))`,
  REWRITE_TAC[GSYM ADD1; mld_or_fold]);;

let MLD_XOR_FOLD_ADD1 = prove
 (`!(a:num->int128) b i.
        mld_xor_fold a b (i + 1) =
        word_xor (mld_xor_fold a b i) (word_xor (a i) (b i))`,
  REWRITE_TAC[GSYM ADD1; mld_xor_fold]);;

let MLD_CT_MEMCMP_EQ_0 = prove
 (`!(a:num->byte) b n.
        mld_ct_memcmp a b n = word 0 <=> !i. i < n ==> a i = b i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_ct_memcmp] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

let MLD_CHUNKS4_EQ = prove
 (`!(f:num->byte) g.
        (!j. j < 64 ==> f(64 + j) = g j) <=>
        mld_chunk128 f 4 = mld_chunk128 g 0 /\
        mld_chunk128 f 5 = mld_chunk128 g 1 /\
        mld_chunk128 f 6 = mld_chunk128 g 2 /\
        mld_chunk128 f 7 = mld_chunk128 g 3`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\j. (f:num->byte)(64 + j)`; `g:num->byte`; `4`]
                MLD_CHUNK128_EQ) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN BETA_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  SUBGOAL_THEN `!i. mld_chunk128 (\j. (f:num->byte)(64 + j)) i =
                    mld_chunk128 f (4 + i)` (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[mld_chunk128] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    CONV_TAC NUM_REDUCE_CONV]);;

let MLD_BYTES8_OF_CHUNKS2 = prove
 (`!(a:int64) (f:num->byte) s.
        read (memory :> bytes128 a) s = mld_chunk128 f 0 /\
        read (memory :> bytes128 (word_add a (word 16))) s = mld_chunk128 f 1
        ==> !j. j < 32 ==> read(memory :> bytes8(word_add a (word j))) s =
                           f j`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MLD_BYTES32_OF_CHUNKS) THEN
  MATCH_ACCEPT_TAC BYTES8_OF_BYTES);;

let MLD_BYTES8_JOIN = prove
 (`!(a:int64) m n (f:num->byte) g s.
        (!j. j < m ==> read(memory :> bytes8(word_add a (word j))) s = f j) /\
        (!j. j < n
             ==> read(memory :> bytes8(word_add a (word(m + j)))) s = g j)
        ==> !j. j < m + n
                ==> read(memory :> bytes8(word_add a (word j))) s =
                    if j < m then f j else g(j - m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j - m:num`) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `m + j - m = j` (fun th -> REWRITE_TAC[th]) THEN
  SIMPLE_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* More lemmas: bytes at an offset from a base, as one number and as 128-bit *)
(* chunks, the low byte of a 32-bit word, and bytes cleared.                 *)
(* ------------------------------------------------------------------------- *)

let READ_BYTES_OF_BYTES8_OFF = prove
 (`!(a:int64) k n (f:num->byte) s.
     (!j. j < n ==> read(memory :> bytes8(word_add a (word(k + j)))) s = f j)
     ==> read(memory :> bytes(word_add a (word k),n)) s =
         num_of_bytelist(list_of_seq f n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC READ_BYTES_OF_BYTES8 THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

let BYTES128_OF_BYTES8_OFF = prove
 (`!(a:int64) k n (f:num->byte) s i.
     (!j. j < n ==> read(memory :> bytes8(word_add a (word(k + j)))) s = f j) /\
     16 * i + 16 <= n
     ==> read(memory :> bytes128(word_add a (word(k + 16 * i)))) s =
         mld_chunk128 f i`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC] THEN
  MATCH_MP_TAC BYTES128_OF_BYTES8 THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

let READ_BYTES32_LOW8 = prove
 (`!a:int64 x s:x86state.
     read (memory :> bytes32 a) s = x
     ==> read (memory :> bytes8 a) s = word_zx x`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; READ_COMPONENT_COMPOSE;
              BYTES32_WBYTES; BYTES8_WBYTES; VAL_READ_WBYTES;
              DIMINDEX_32; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP (8 * 1)`; READ_BYTES_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let BYTES8_ZERO_OF_BYTES = prove
 (`!a:int64 n s:x86state.
     read (memory :> bytes(a,n)) s = 0
     ==> !j. j < n ==> read(memory :> bytes8(word_add a (word j))) s = word 0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; BYTES8_WBYTES; READ_COMPONENT_COMPOSE;
              VAL_READ_WBYTES; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM
   `\x. (x DIV 2 EXP (8 * j)) MOD 2 EXP (8 * 1)`) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  REWRITE_TAC[DIV_0; MOD_0] THEN
  SUBGOAL_THEN `MIN (n - j) 1 = 1` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]]);;

let MLD_CHUNKS4_EQ0 = prove
 (`!(f:num->byte) g.
        (!j. j < 64 ==> f j = g j) <=>
        mld_chunk128 f 0 = mld_chunk128 g 0 /\
        mld_chunk128 f 1 = mld_chunk128 g 1 /\
        mld_chunk128 f 2 = mld_chunk128 g 2 /\
        mld_chunk128 f 3 = mld_chunk128 g 3`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:num->byte`; `g:num->byte`; `4`] MLD_CHUNK128_EQ) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN REWRITE_TAC[]);;

let WORD_VAL_MOD_256 = prove
 (`!x:M word. (word(val x MOD 256):N word) = word_zx(word_zx x:byte)`,
  GEN_TAC THEN REWRITE_TAC[word_zx; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Tools for the simulation. The facts of a byte string at a + k + j for j < *)
(* n give the 128-bit chunks at a + k + 16 * i (CHUNK128_TAC a k is), in the *)
(* latest state. After a call, which may change the vector registers,        *)
(* YMM_GHOST_TAC st regs gives names to their values in state st, so that    *)
(* the legacy SSE instructions after it, which keep the top halves, have     *)
(* known values. X86_CMP_RULE vor vxor hi th turns th, |- l = e with e the   *)
(* value of the vectorized mld_ct_memcmp as the simulation gives it, from    *)
(* the OR fold vor and the XOR fold vxor of the differences, into |- l = if  *)
(* vor = word 0 then word 0 else word hi: the OR-reduced and XOR-reduced     *)
(* values in e are generalized, so that BITBLAST_RULE proves the rest        *)
(* quickly (as PFS_CMP_RULE does for AArch64).                               *)
(* ------------------------------------------------------------------------- *)

let BYTES8_OFF_FACT a k st =
  fun th ->
    let c = concl th in
    let j,bod = dest_forall c in
    let ant,eq = dest_imp bod in
    let l,r = dest_eq eq in
    let addr = rand(rand(lhand l)) in
    if rand l = st &&
       addr = mk_comb(mk_comb(`word_add:int64->int64->int64`,a),
                      mk_comb(`word:num->int64`,
                              mk_binop `(+):num->num->num`
                               (mk_small_numeral k) j))
    then (rand ant, mk_abs(j,r)) else failwith "BYTES8_OFF_FACT";;

let pfs_latest_state (asl,w) =
  rand(lhand(concl(snd(find (fun (_,th) ->
    can (term_match [] `read RIP s = x`) (concl th)) asl))));;

let CHUNK128_TAC (a:term) (k:int) (is:int list) =
  W(fun (asl,w) ->
    let st = pfs_latest_state (asl,w) in
    FIRST_ASSUM(fun th ->
      let n,f = BYTES8_OFF_FACT a k st th in
      MAP_EVERY (fun i ->
        let ith = BETA_RULE(ISPECL [a; mk_small_numeral k; n; f; st;
                                    mk_small_numeral i]
                                   BYTES128_OF_BYTES8_OFF) in
        let bnd = EQT_ELIM(NUM_REDUCE_CONV(rand(lhand(concl ith)))) in
        ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
                    (MP ith (CONJ th bnd)))) is));;

let YMM_GHOST_TAC st regs =
  MAP_EVERY (fun (r,v) ->
    let t = mk_comb(mk_comb(`read:(x86state,int256)component->x86state->int256`,
                            mk_const(r,[])),st) in
    let y = `y:int256` in
    X_CHOOSE_TAC (mk_var(v,`:int256`))
      (EXISTS (mk_exists(y,mk_eq(t,y)),t) (REFL t))) regs;;

let X86_CMP_RULE vor vxor hi th =
  let th1 = CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV [] THENC
                                REWRITE_CONV[WORD_VAL_MOD_256])) th in
  let e = rhs(concl th1) in
  let isatom v t = type_of t = `:int128` && free_in v t in
  let x0 = find_term (isatom vor) e and x1 = find_term (isatom vxor) e in
  let g0 = genvar `:int128` and g1 = genvar `:int128` in
  let e' = subst [g0,x0; g1,x1] e in
  let ty = type_of e in
  let wd n = mk_comb(mk_const("word",[hd(snd(dest_type ty)),`:N`]),
                     mk_numeral n) in
  let zb t = mk_comb(`word_zx:int128->byte`,t) in
  let tgt = mk_cond(mk_eq(zb g0,`word 0:byte`),wd (num 0),wd hi) in
  let tha = SPECL [x0; x1]
    (BITBLAST_RULE (list_mk_forall([g0;g1],mk_eq(e',tgt)))) in
  let vv = genvar `:int128` in
  let thb = SPEC vor (BITBLAST_RULE
    (mk_forall(vv,mk_eq(mk_eq(zb(subst[vv,vor] x0),`word 0:byte`),
                        mk_eq(vv,`word 0:int128`))))) in
  TRANS th1 (CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV(REWR_CONV thb))) tha);;

let SIMD_STEPS_TAC execth ns =
  MAP_EVERY (fun n -> X86_STEPS_TAC execth [n] THEN SIMD_SIMPLIFY_TAC []) ns;;

(* ------------------------------------------------------------------------- *)
(* Branches decided by a fact: PFS_CASES_TAC p splits on p and rewrites the  *)
(* RIP and the events with the case.                                         *)
(* ------------------------------------------------------------------------- *)

let pfs_pcev th =
  try let l = lhs(concl th) in
      fst(dest_const(rator(rator l))) = "read" &&
      (rand(rator l) = `RIP` || rand(rator l) = `events`)
  with Failure _ -> false;;

let PFS_CASES_TAC p =
  ASM_CASES_TAC p THEN
  POP_ASSUM(fun cth ->
    let eq = if is_neg(concl cth) then EQF_INTRO cth else EQT_INTRO cth in
    RULE_ASSUM_TAC(fun th -> if pfs_pcev th then REWRITE_RULE[eq] th else th)
    THEN ASSUME_TAC cth);;

let pfs_asm_rhs (asl,w) l =
  rhs(concl(snd(find (fun (_,th) ->
    try lhs(concl th) = l with Failure _ -> false) asl)));;

(* ------------------------------------------------------------------------- *)
(* The proof of a FULL theorem for mldsa{44,65,87}_pk_from_sk. The record    *)
(* gives the parameter set (k, l, eta and the p bytes of a packed polynomial *)
(* of s1 and s2, with its unpacking), the sizes of the secret and the public *)
(* key, the frame N of the function with its callees and the SUB of the      *)
(* aligned frame, and the theorems for the callees. The code saves six       *)
(* registers, so k0 = N - 48, and the aligned frame (bot,k0 - 31) has, from  *)
(* RSP = bot + c (c = k0 - 31 - sub), the spills, the copies of rho, the key *)
(* and tr at c + 64, + 96 and + 128, the hash of the public key at c + 192,  *)
(* the scratch polynomial of s2 at c + 256, the buffer of t0 at c + 1280 and *)
(* s1 above it, up to the AND; mld_compute_pack_t0_t1 has the stack below    *)
(* bot + c. The proof is one loop over the 26 * k chunks of 16 bytes of t0   *)
(* that the code compares (as mld_or_fold and mld_xor_fold), with before it  *)
(* the copies, the calls that unpack and check s1 and s2, transform s1 and   *)
(* compute t, and after it the result of the comparison, the hash of the     *)
(* public key, the comparison of tr (four iterations of a loop, simulated as *)
(* such), the check (the validity predicate) and the two paths to the        *)
(* return, with the zeroing of the public key (an inlined memset of PKL      *)
(* bytes) on the invalid one and of the buffers on both. The code of the     *)
(* three functions differs only in its constants, so the steps are the same. *)
(* ------------------------------------------------------------------------- *)

type pfs_prm =
 { pfs_exec : thm * thm option array;
   pfs_fn : string;
   pfs_k : int; pfs_l : int; pfs_eta : int; pfs_p : int;
   pfs_unpack : term;
   pfs_sk : int; pfs_pk : int; pfs_fr : int; pfs_sub : int;
   pfs_cpt : thm; pfs_unpack_th : thm; pfs_chkl : thm; pfs_chkk : thm;
   pfs_ntt : thm; pfs_shake : thm };;

let pfs_n = mk_small_numeral;;

(*** RSP after the SUB, as an offset from bot ***)
let pfs_c prm = prm.pfs_fr - 48 - 31 - prm.pfs_sub;;

let pfs_inst prm =
  let n = pfs_n in
  let k = prm.pfs_k and l = prm.pfs_l and p = prm.pfs_p in
  let c = pfs_c prm in
  vsubst [n k,`KK:num`; n l,`LL:num`; n prm.pfs_eta,`ETA:num`; n p,`PP:num`;
          n prm.pfs_sk,`SKL:num`; n prm.pfs_pk,`PKL:num`;
          n (128 + l * p),`S2O:num`; n (128 + (l + k) * p),`T0O:num`;
          n (416 * k),`T0N:num`; n (26 * k),`NCH:num`;
          n (l * p),`S1N:num`; n (k * p),`S2N:num`; n (320 * k),`T1N:num`;
          n (prm.pfs_eta + 1),`BND:num`;
          n c,`C0:num`; n (c + 44),`C2C:num`; n (c + 128),`CTR:num`;
          n (c + 256),`CS2:num`; n (c + 1280),`CT0:num`;
          n (c + 1280 + 416 * k),`CS1:num`;
          n (prm.pfs_fr - 8),`F8:num`; n (prm.pfs_fr - 16),`F16:num`;
          n (prm.pfs_fr - 24),`F24:num`; n (prm.pfs_fr - 32),`F32:num`;
          n (prm.pfs_fr - 40),`F40:num`; n (prm.pfs_fr - 48),`F48:num`;
          n prm.pfs_fr,`FR:num`;
          prm.pfs_unpack,`unpack:(num->byte)->num->int32`];;

let pfs_terms prm =
  let inst = pfs_inst prm in
  let s1 = inst `mld_polyvec_unpack PP unpack (\j. (skb:num->byte)(128 + j))`
  and s2 = inst `mld_polyvec_unpack PP unpack (\j. (skb:num->byte)(S2O + j))`
  and skt0 = inst `\j. (skb:num->byte)(T0O + j)`
  and t0 = inst `mld_polyvec_pack 416 mld_polyt0_pack
                  (mld_polyvec_map mld_poly_power2round_lo
                    (mld_pk_from_sk_t LL unpack PP (skb:num->byte)))`
  and pkf = inst `mld_pk_from_sk_pk LL unpack PP (skb:num->byte)`
  and valid = inst `mld_pk_from_sk_valid KK LL ETA unpack PP (skb:num->byte)` in
  let m = inst (subst [pkf,`pkf:num->byte`]
                  `num_of_bytelist(list_of_seq pkf PKL)`) in
  let h = inst (subst [m,`m:num`] `mld_shake256_byte PKL m`) in
  let chk1 = inst (subst [s1,`s1:num->int32`]
                    `mld_polyvec_chknorm LL s1 (word BND)`)
  and chk2 = inst (subst [s2,`s2:num->int32`]
                    `mld_polyvec_chknorm KK s2 (word BND)`) in
  (s1, s2, skt0, t0, pkf, valid, m, h, chk1, chk2);;

let pfs_invariant prm =
  let (s1,s2,skt0,t0,pkf,valid,m,h,chk1,chk2) = pfs_terms prm in
  pfs_inst prm (subst
   [skt0,`skt0:num->byte`; t0,`t0c:num->byte`; pkf,`pkc:num->byte`;
    chk1,`chk1:int32`; chk2,`chk2:int32`]
   `\i s. read RSP s = word_add bot (word C0) /\
          read RBP s = word_add stackpointer (word F8) /\
          read (memory :> bytes64 (word_add stackpointer (word F8))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word F16))) s =
          r15_init /\
          read (memory :> bytes64 (word_add stackpointer (word F24))) s =
          r14_init /\
          read (memory :> bytes64 (word_add stackpointer (word F32))) s =
          r13_init /\
          read (memory :> bytes64 (word_add stackpointer (word F40))) s =
          r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word F48))) s =
          rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word FR))) s =
          returnaddress /\
          read RAX s = word(16 * i) /\
          read RBX s = sk /\
          read R9 s = word_add bot (word CT0) /\
          read R11 s = word 0 /\
          read R12 s = pk /\
          read R13 s = word_zx(chk1:int32) /\
          read R14 s = word_add bot (word CS1) /\
          read R15 s = word_add bot (word CS2) /\
          read (memory :> bytes32 (word_add bot (word C2C))) s = chk2 /\
          ~read DF s /\
          read XMM0 s = mld_or_fold (mld_chunk128 skt0) (mld_chunk128 t0c) i /\
          read XMM2 s = mld_xor_fold (mld_chunk128 skt0) (mld_chunk128 t0c) i /\
          (!j. j < SKL
               ==> read(memory :> bytes8(word_add sk (word j))) s = skb j) /\
          (!j. j < T0N
               ==> read(memory :> bytes8(word_add bot (word(CT0 + j)))) s =
                   t0c j) /\
          (!j. j < PKL
               ==> read(memory :> bytes8(word_add pk (word j))) s = pkc j) /\
          (!j. j < 64
               ==> read(memory :> bytes8(word_add bot (word(CTR + j)))) s =
                   skb(64 + j))`);;

let pfs_allowed =
  [`pc:num`; `pk:int64`; `sk:int64`; `skb:num->byte`; `mf:int64`;
   `stackpointer:int64`; `returnaddress:int64`; `r:num`; `bot:int64`];;

let PFS_CALL_TAC prm name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc prm.pfs_exec name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   pfs_allowed n;;

let pfs_st n = mk_var("s" ^ string_of_int n,`:x86state`);;

let PFS_SETUP_TAC prm =
  let inst = pfs_inst prm in
  let template = inst
   `\(pk:int64) (sk:int64) (rho:num) (valid:bool) (mf:int64) (pc:num)
     (stackpointer:int64) (returnaddress:int64).
     APPEND
      (if valid then f_ev_epil_v pk sk rho mf pc stackpointer returnaddress
       else f_ev_epil_i pk sk rho mf pc stackpointer returnaddress)
      (APPEND
        (ENUMERATEL NCH
          (\i. f_ev_loop pk sk rho mf pc stackpointer returnaddress i))
        (f_ev_prol pk sk rho mf pc stackpointer returnaddress))
     :(uarch_event)list` in
  let k0 = prm.pfs_fr - 48 in
  let c = pfs_c prm in
  let regions = map inst
   [`pk:int64,PKL:num`; `sk:int64,SKL:num`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `ea:int64,el:num`;
    `word_add stackpointer (word F48):int64,48`;
    `word_add stackpointer (word FR):int64,8`] in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP prm.pfs_cpt th) "H_CPT") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC prm.pfs_unpack_th "H_UNPACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC prm.pfs_chkl "H_CHKL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC prm.pfs_chkk "H_CHKK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC prm.pfs_ntt "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC prm.pfs_shake "H_SHAKE" THEN
  CONCRETIZE_F_EVENTS_TAC template THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  ABBREV_TAC `r = mld_sk_rho skb` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst prm.pfs_exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC k0 THEN REALIGN_FRAME_TAC prm.pfs_fr k0 THEN
  REALIGN_NONOV_TAC (k0 - 31) regions THEN
  REALIGN_ALIGNED_TAC
   (c :: map (fun d -> c + d) [64; 80; 96; 112; 128; 144; 160; 176;
                               192; 208; 224; 240; 1280]) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`;;

(*** The copies, the unpacking, checks and transform, and t ***)

let PFS_PROLOGUE_TAC prm =
  let (s1,s2,skt0,t0,pkf,valid,m,h,chk1,chk2) = pfs_terms prm in
  let inst = pfs_inst prm in
  let c = pfs_c prm in
  let exec = prm.pfs_exec in
  let teq = (REWRITE_CONV[mld_pk_from_sk_t; mld_sk_s1] THENC
             REWRITE_CONV[ADD_ASSOC] THENC NUM_REDUCE_CONV)
            (inst `mld_pk_from_sk_t LL unpack PP (skb:num->byte)`) in
  MAP_EVERY (fun n ->
   GHOST_INTRO_TAC (mk_var("ymm"^string_of_int n^"_init",`:int256`))
    (mk_comb(`read:(x86state,int256)component->x86state->int256`,
             mk_const("YMM"^string_of_int n,[])))) (3--7) THEN
  FULL_INIT_TAC THEN
  GLUE_LOAD128_TAC `sk:int64` [0; 16; 32; 48; 64; 80; 96; 112] THEN
  X86_STEPS_TAC exec (1--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_M128]) THEN
  X86_STEPS_TAC exec (11--11) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC exec (12--31) THEN
  GLUE_STORE_TAC `bot:int64` THEN
  SUBGOAL_THEN (subst [pfs_n(c + 64),`k:num`]
   `!j. j < 32 ==> read(memory :> bytes8(word_add bot (word(k + j)))) s31 =
                   (skb:num->byte) j`) ASSUME_TAC THENL
   [GLUE_BYTES_FINAL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (subst [pfs_n(c + 128),`k:num`]
   `!j. j < 64 ==> read(memory :> bytes8(word_add bot (word(k + j)))) s31 =
                   (skb:num->byte)(64 + j)`) ASSUME_TAC THENL
   [GLUE_BYTES_FINAL_TAC; ALL_TAC] THEN
  DISCARD_MATCHING_ASSUMPTIONS
   [`read (memory :> bytes8 (word_add bot (word n))) s31 = x`;
    `read (memory :> bytes128 a) s31 = x`] THEN
  X86_STEPS_TAC exec (32--32) THEN
  GLUE_SLICE_TAC (inst
   `!j. j < S1N ==> read(memory :> bytes8(word_add sk (word(128 + j)))) s32 =
                    (skb:num->byte)(128 + j)`) THEN
  PFS_CALL_TAC prm "H_UNPACK"
   [`read RDI s`; `read RSI s`; `\j. (skb:num->byte)(128 + j)`] 33 THEN
  X86_STEPS_TAC exec (34--36) THEN
  PFS_CALL_TAC prm "H_CHKL" [`read RDI s`; s1; `read RSI s`] 37 THEN
  X86_STEPS_TAC exec (38--44) THEN
  GLUE_SLICE_TAC (inst
   `!j. j < S2N ==> read(memory :> bytes8(word_add sk (word(S2O + j)))) s44 =
                    (skb:num->byte)(S2O + j)`) THEN
  PFS_CALL_TAC prm "H_CHKK"
   [`read RDI s`; inst `\j. (skb:num->byte)(S2O + j)`; `read RSI s`;
    `read RDX s`] 45 THEN
  X86_STEPS_TAC exec (46--48) THEN
  PFS_CALL_TAC prm "H_NTT" [`read RDI s`; s1] 49 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
  YMM_GHOST_TAC `s49:x86state` ["YMM6","ymm6_49"; "YMM7","ymm7_49"] THEN
  CHUNK128_TAC `bot:int64` (c + 64) [0; 1] THEN
  X86_STEPS_TAC exec (50--61) THEN
  FIRST_X_ASSUM(fun th1 ->
    if lhs(concl th1) = `read (memory :> bytes128 pk) s61` then
      FIRST_X_ASSUM(fun th2 ->
        if lhs(concl th2) =
           `read (memory :> bytes128 (word_add pk (word 16))) s61`
        then let f = CONV_RULE(SIMD_SIMPLIFY_CONV []) o REWRITE_RULE[ETA_AX] in
             ASSUME_TAC(MATCH_MP MLD_BYTES8_OF_CHUNKS2 (CONJ (f th1) (f th2)))
        else NO_TAC)
    else NO_TAC) THEN
  FIRST_ASSUM(fun eq -> if concl eq = `mld_sk_rho skb = r` then
    FIRST_ASSUM(fun th ->
      try let _ = BYTES8_OFF_FACT `bot:int64` (c + 64) `s61:x86state` th in
          ASSUME_TAC(REWRITE_RULE[GSYM mld_sk_rho; ETA_AX; eq]
                      (BETA_RULE (MATCH_MP READ_BYTES_OF_BYTES8_OFF th)))
      with Failure _ -> NO_TAC)
    else NO_TAC) THEN
  X86_STEPS_TAC exec (62--62) THEN
  PFS_CALL_TAC prm "H_CPT"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
    mk_comb(`mld_polyvec_map mld_poly_ntt`,s1);
    inst `\j. (skb:num->byte)(S2O + j)`; `r:num`] 63 THEN
  YMM_GHOST_TAC `s63:x86state` ["YMM0","ymm0_63"; "YMM2","ymm2_63"] THEN
  X86_STEPS_TAC exec (64--72) THEN
  FIRST_ASSUM(fun th1 ->
    if can (term_match []
      `!j. j < 32 ==> read (memory :> bytes8 (word_add pk (word j))) s72 =
                      (f:num->byte) j`) (concl th1) then
    FIRST_ASSUM(fun th2 ->
      if can (term_match [] (inst
        `!j. j < T1N ==> read (memory :> bytes8 (word_add pk (word(32 + j))))
                          s72 = (g:num->byte) j`)) (concl th2) then
       ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)
                   (MATCH_MP MLD_BYTES8_JOIN (CONJ th1 th2)))
      else NO_TAC)
    else NO_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[teq; mld_pk_from_sk_pk; mld_or_fold; mld_xor_fold;
              MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[XMM0; XMM2; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC WORD_BLAST THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** One chunk of 16 bytes of t0, with the loop test ***)

let PFS_BODY_TAC prm =
  let (s1,s2,skt0,t0,pkf,valid,m,h,chk1,chk2) = pfs_terms prm in
  let inst = pfs_inst prm in
  let c = pfs_c prm in
  let t0o = 128 + (prm.pfs_l + prm.pfs_k) * prm.pfs_p
  and t0n = 416 * prm.pfs_k in
  let ct0 = c + 1280 in
  let skr = ARITH_RULE(subst [pfs_n t0o,`k:num`]
              `k + 16 * i = 1 * 16 * i + k`)
  and t0r = ARITH_RULE(subst [pfs_n ct0,`k:num`]
              `k + 16 * i = k + 1 * 16 * i`) in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  FULL_INIT_TAC THEN
  XMM_EXISTSTOP_TAC "top0" `YMM0` THEN XMM_EXISTSTOP_TAC "top2" `YMM2` THEN
  MP_TAC(SPECL [inst `word_add (sk:int64) (word T0O)`; pfs_n t0n; skt0;
                `s0:x86state`; `i:num`] BYTES128_OF_BYTES8) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN BETA_TAC THEN
      FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN SIMPLE_ARITH_TAC);
      SIMPLE_ARITH_TAC];
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
    REWRITE_TAC[skr] THEN DISCH_TAC] THEN
  MP_TAC(SPECL [inst `word_add (bot:int64) (word CT0)`; pfs_n t0n; t0;
                `s0:x86state`; `i:num`] BYTES128_OF_BYTES8) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN SIMPLE_ARITH_TAC);
      SIMPLE_ARITH_TAC];
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
    REWRITE_TAC[t0r] THEN DISCH_TAC] THEN
  VAL_INT64_TAC `16 * i` THEN
  SUBGOAL_THEN (inst
   `aligned 16 (word_add (word_add bot (word CT0)) (word(1 * 16 * i)):int64)`)
  ASSUME_TAC THENL
   [MATCH_MP_TAC ALIGNED_WORD_ADD THEN
    ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  X86_STEPS_TAC prm.pfs_exec (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[MLD_OR_FOLD_ADD1; MLD_XOR_FOLD_ADD1] THEN
  LOOP_TEST_TAC THEN LOOP_COND_TAC THEN REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[XMM0; XMM2; READ_ZEROTOP_128] THEN
      ASM_REWRITE_TAC[MLD_OR_FOLD_ADD1; MLD_XOR_FOLD_ADD1] THEN
      CONV_TAC WORD_BLAST THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The comparisons, the hash, the check and the two paths to the return ***)

let pfs_low128 (asl,w) st r =
  rand(pfs_asm_rhs (asl,w)
         (mk_comb(mk_comb(`read:(x86state,int256)component->x86state->int256`,
                          mk_const(r,[])),st)));;

let PFS_EXIT_TAC prm =
  let (s1,s2,skt0,t0,pkf,valid,m,h,chk1,chk2) = pfs_terms prm in
  let inst = pfs_inst prm in
  let c = pfs_c prm in
  let exec = prm.pfs_exec in
  let fold f = subst [skt0,`skt0:num->byte`; t0,`t0c:num->byte`] f in
  let vth = (REWRITE_CONV[mld_pk_from_sk_valid; mld_sk_s1; mld_sk_s2] THENC
             REWRITE_CONV[ADD_ASSOC] THENC NUM_REDUCE_CONV) valid in
  let pkl = pfs_n prm.pfs_pk in
  let at k st = subst [pfs_n k,`k:num`; st,`s:x86state`] in
  REWRITE_TAC[] THEN
  ABBREV_TAC (mk_eq(`v2:int128`, inst(fold
    `mld_or_fold (mld_chunk128 skt0) (mld_chunk128 t0c) NCH`))) THEN
  ABBREV_TAC (mk_eq(`v1:int128`, inst(fold
    `mld_xor_fold (mld_chunk128 skt0) (mld_chunk128 t0c) NCH`))) THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  FULL_INIT_TAC THEN
  XMM_EXISTSTOP_TAC "top0" `YMM0` THEN XMM_EXISTSTOP_TAC "top2" `YMM2` THEN
  SIMD_STEPS_TAC exec (1--40) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] (at (c + 56) `s40:x86state`
         `read (memory :> bytes8 (word_add bot (word k))) s = x`)) (concl th)
    then ASSUME_TAC(X86_CMP_RULE `v2:int128` `v1:int128` (num 255) th)
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [pkl,`n:num`]
      `!j. j < n ==> read(memory :> bytes8(word_add pk (word j))) s40 =
                     (f:num->byte) j`)) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX] (MATCH_MP READ_BYTES_OF_BYTES8 th))
    else NO_TAC) THEN
  X86_STEPS_TAC exec (41--41) THEN
  PFS_CALL_TAC prm "H_SHAKE"
   [`read RDI s`; `64`; `read RDX s`; pkl; m] 42 THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] (at (c + 192) `s42:x86state`
         `read (memory :> bytes(word_add bot (word k),64)) s = x`)) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]
                     (MATCH_MP BYTES8_OF_BYTES th))
    else NO_TAC) THEN
  CHUNK128_TAC `bot:int64` (c + 192) [0; 1; 2; 3] THEN
  CHUNK128_TAC `bot:int64` (c + 128) [0; 1; 2; 3] THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] (at (c + 44) `s42:x86state`
         `read (memory :> bytes32 (word_add bot (word k))) s = x`)) (concl th)
    then ASSUME_TAC(MATCH_MP READ_BYTES32_LOW8 th) else NO_TAC) THEN
  YMM_GHOST_TAC `s42:x86state`
   ["YMM0","ymm0_42"; "YMM1","ymm1_42"; "YMM2","ymm2_42"] THEN
  SIMD_STEPS_TAC exec (43--77) THEN
  W(fun g -> ABBREV_TAC (mk_eq(`w2:int128`,
                               pfs_low128 g `s77:x86state` "YMM0"))) THEN
  W(fun g -> ABBREV_TAC (mk_eq(`w1:int128`,
                               pfs_low128 g `s77:x86state` "YMM1"))) THEN
  SIMD_STEPS_TAC exec (78--110) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read RAX s110 = x`) (concl th)
    then ASSUME_TAC(X86_CMP_RULE `w2:int128` `w1:int128` (num 4294967295) th)
    else NO_TAC) THEN
  X86_STEPS_TAC exec (111--114) THEN
  W(fun g ->
    let pcv = pfs_asm_rhs g `read RIP s114` in
    let cond = rand(rator(rator pcv)) in
    let t0eq = mk_iff(mk_eq(list_mk_comb(`mld_ct_memcmp`,
                 [t0; skt0; inst `T0N:num`]),`word 0:byte`),
                 `(v2:int128) = word 0`)
    and treq = mk_iff(mk_eq(list_mk_comb(`mld_ct_memcmp`,
                 [`\j. (skb:num->byte)(64 + j)`; h; `64`]),`word 0:byte`),
                 `(w2:int128) = word 0`) in
    SUBGOAL_THEN t0eq (LABEL_TAC "T0EQ") THENL
     [REWRITE_TAC[MLD_CT_MEMCMP_EQ_0] THEN
      FIRST_ASSUM(fun th -> if rhs(concl th) = `v2:int128`
                            then REWRITE_TAC[GSYM th] else NO_TAC) THEN
      REWRITE_TAC[MLD_OR_FOLD_EQ_0; MLD_CHUNK128_EQ] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN BETA_TAC THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN treq (LABEL_TAC "TREQ") THENL
     [FIRST_ASSUM(fun th -> if rhs(concl th) = `w2:int128`
                            then REWRITE_TAC[GSYM th] else NO_TAC) THEN
      REWRITE_TAC[MLD_CT_MEMCMP_EQ_0; WORD_OR_EQ_0; WORD_XOR_EQ_0; ETA_AX] THEN
      MP_TAC(ISPECL [`\j. (skb:num->byte)(64 + j)`; h] MLD_CHUNKS4_EQ0) THEN
      REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN (mk_iff(cond,valid)) (LABEL_TAC "CHECK") THENL
     [USE_THEN "T0EQ" (fun t0th -> USE_THEN "TREQ" (fun trth ->
        REWRITE_TAC[vth; t0th; trth])) THEN
      REWRITE_TAC[WORD_VAL_MOD_256; VAL_EQ_0] THEN
      SPEC_TAC(`(w2:int128) = word 0`,`b:bool`) THEN
      SPEC_TAC(`(v2:int128) = word 0`,`a:bool`) THEN
      SPEC_TAC(chk2,`c2:int32`) THEN SPEC_TAC(chk1,`c1:int32`) THEN
      REPEAT GEN_TAC THEN BOOL_CASES_TAC `a:bool` THEN
      BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[] THEN
      SPEC_TAC(`c2:int32`,`c2:int32`) THEN SPEC_TAC(`c1:int32`,`c1:int32`) THEN
      W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));
      ALL_TAC]) THEN
  USE_THEN "CHECK" (fun th -> RULE_ASSUM_TAC(fun t ->
    if pfs_pcev t then REWRITE_RULE[th] t else t)) THEN
  PFS_CASES_TAC valid THENL
   [SIMD_STEPS_TAC exec (115--147) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    SIMD_STEPS_TAC exec (115--125) THEN
    MEMSET_PREP_TAC THEN MEMSET_STEP_TAC exec 126 THEN
    MEMSET_DONE_TAC `pk:int64` prm.pfs_pk "s126" THEN
    SIMD_STEPS_TAC exec (127--159) THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] (subst [pkl,`n:num`]
           `read (memory :> bytes (pk,n)) s159 = 0`)) (concl th)
      then ASSUME_TAC(MATCH_MP BYTES8_ZERO_OF_BYTES th) else NO_TAC) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];;

let PFS_FULL_TAC prm =
  let lbl s = mk_binary "+" (`pc:num`,pfs_n(layout(prm.pfs_fn ^ "_" ^ s))) in
  PFS_SETUP_TAC prm THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (pfs_n(26 * prm.pfs_k)) (lbl "loop1")
   (lbl "loop1_exit") (pfs_invariant prm) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; PFS_PROLOGUE_TAC prm; PFS_BODY_TAC prm; PFS_EXIT_TAC prm];;
