(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the top-level functions of mldsa-native: bytes of memory as    *)
(* lists of bytes and as 128-bit chunks, and the folds of the constant-time  *)
(* comparison mld_ct_memcmp (ct.h), which the code vectorizes 16 bytes at a  *)
(* time, accumulating the OR and the XOR of the differences; and the proof   *)
(* of the FULL theorems for mld_sign_pk_from_sk (PFS_FULL_TAC).              *)
(* ========================================================================= *)

needs "common/layout.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

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
  FIRST_X_ASSUM(MP_TAC o SPECL [`f:num->byte`; `s:armstate`]) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
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
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

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
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `EL (j MOD 16):byte list->byte`) THEN
    SIMP_TAC[EL_LIST_OF_SEQ; MOD_LT_EQ; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `16 * j DIV 16 + j MOD 16 = j`];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

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
  SUBGOAL_THEN `~(B = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES]);;

let BYTES8_OF_BYTES = prove
 (`!(a:int64) n (f:num->byte) s.
        read(memory :> bytes(a,n)) s = num_of_bytelist(list_of_seq f n)
        ==> !j. j < n ==> read(memory :> bytes8(word_add a (word j))) s = f j`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LT] THEN
  MAP_EVERY X_GEN_TAC [`f:num->byte`; `s:armstate`] THEN
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
  FIRST_X_ASSUM(MP_TAC o SPECL [`f:num->byte`; `s:armstate`]) THEN
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
(* The result of mld_ct_memcmp as the code computes it from the OR fold vor  *)
(* and the XOR fold vxor of the differences: PFS_CMP_RULE vor vxor th turns  *)
(* th, |- l = e with e the value the simulation gives, into                  *)
(* |- l = if vor = word 0 then word 0 else word 255. The OR-reduced and      *)
(* XOR-reduced bytes of e are generalized, so that BITBLAST_RULE proves the  *)
(* rest quickly (WORD_BLAST takes far longer on these terms).                *)
(* ------------------------------------------------------------------------- *)

let PFS_SUBWORD8_32 = WORD_BLAST
  `!x:int128. word_subword x (0,8):int32 = word_zx(word_subword x (0,8):byte)`;;

let pfs_is_byte_sub t =
  try fst(dest_const(fst(strip_comb t))) = "word_subword" &&
      rand t = `(0,8)` && type_of t = `:byte`
  with Failure _ -> false;;

let pfs_word ty n =
  mk_comb(mk_const("word",[hd(snd(dest_type ty)),`:N`]),mk_small_numeral n);;

let PFS_CMP_RULE vor vxor th =
  let e = rhs(concl th) in
  let th0 = REWRITE_CONV[PFS_SUBWORD8_32] e in
  let eb = rhs(concl th0) in
  let rb = find_term (fun t -> pfs_is_byte_sub t && free_in vor t) eb
  and sb = find_term (fun t -> pfs_is_byte_sub t && free_in vxor t) eb in
  let rv = genvar `:byte` and qv = genvar `:byte` in
  let er = subst [rv,rb; qv,sb] eb in
  let ty = type_of e in
  let tgt r = mk_cond(mk_eq(r,`word 0:byte`),pfs_word ty 0,pfs_word ty 255) in
  let tha = SPECL [rb; sb]
    (BITBLAST_RULE (list_mk_forall([rv;qv], mk_eq(er, tgt rv)))) in
  let vv = genvar(type_of vor) in
  let thb = SPEC vor (BITBLAST_RULE
    (mk_forall(vv, mk_eq(mk_eq(subst[vv,vor] rb, `word 0:byte`),
                         mk_eq(vv, pfs_word (type_of vor) 0))))) in
  TRANS th (TRANS th0
    (CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV(REWR_CONV thb))) tha));;

(* ------------------------------------------------------------------------- *)
(* Branches decided by the facts: PFS_DECIDE_TAC evaluates the comparisons   *)
(* of addresses with the same base in the PC and the events, and             *)
(* PFS_CASES_TAC p splits on p and rewrites them with the case. PFS_RUN_TAC  *)
(* simulates from step n to the return, with the calls of memset through the *)
(* PLT, whose events are unified as those of the callees (the shared         *)
(* LIBC_SAFE_CALL_TAC does not allow the functions of the events template).  *)
(* ------------------------------------------------------------------------- *)

let PFS_WORD_SUB_ADD = WORD_RULE
  `!a:int64 x y. word_sub (word_add a x) (word_add a y) = word_sub x y`;;

let pfs_pcev th =
  try let l = lhs(concl th) in
      fst(dest_const(rator(rator l))) = "read" &&
      (rand(rator l) = `PC` || rand(rator l) = `events`)
  with Failure _ -> false;;

let PFS_DECIDE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if pfs_pcev th
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                   REWRITE_CONV[PFS_WORD_SUB_ADD] THENC
                   WORD_REDUCE_CONV THENC NUM_REDUCE_CONV THENC
                   REWRITE_CONV[]) th
    else th);;

let PFS_CASES_TAC p =
  ASM_CASES_TAC p THEN
  POP_ASSUM(fun cth ->
    let eq = if is_neg(concl cth) then EQF_INTRO cth else EQT_INTRO cth in
    RULE_ASSUM_TAC(fun th -> if pfs_pcev th then REWRITE_RULE[eq] th else th)
    THEN ASSUME_TAC cth);;

let pfs_current_pc (asl,w) =
  let s = rand w in
  rhs(concl(snd(find (fun (_,th) ->
    try lhs(concl th) = mk_comb(`read PC`,s) with Failure _ -> false) asl)));;

let pfs_pc_offset t =
  try dest_small_numeral(rand(rand t)) with Failure _ -> -1;;

let PFS_LIBC_SAFE_CALL_TAC name execth ilist allowed n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true execth th ilist n THENL
     [FULL_EXISTS_E2_TAC allowed; LABEL_TAC name th]);;

let rec PFS_RUN_TAC execth fn allowed n (asl,w) =
  let off = pfs_pc_offset (pfs_current_pc (asl,w)) in
  if off < 0 then ALL_TAC (asl,w)
  else if off = layout "plt_memset" then
    (LIBC_PLT_TAC execth (n - 1) THEN
     PFS_LIBC_SAFE_CALL_TAC "H_MEMSET" execth
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `read X30 s`] (ref allowed) (n + 4) THEN
     PFS_RUN_TAC execth fn allowed (n + 5)) (asl,w)
  else
    (ARM_STEPS_TAC execth [n] THEN
     (if off = layout(fn ^ "_adrp2") then MLKEM_NATIVE_ADRP_TAC
      else ALL_TAC) THEN
     PFS_DECIDE_TAC THEN PFS_RUN_TAC execth fn allowed (n + 1)) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* The memory safety of the events at the end of a segment. The events of    *)
(* the template instantiated so far are beta-reduced, and the list is        *)
(* normalized (PFS_LIST_CONV), so that the events of the invariant, e2, can  *)
(* be folded back; then each part is checked by itself, the parts of e2 and  *)
(* of the callees from the assumptions. The events e2 of the postcondition   *)
(* become a metavariable with a name of its own (PFS_META_EXISTS_TAC):       *)
(* META_EXISTS_TAC chooses a primed e2 that is only fresh in its own goal,   *)
(* which on the valid path is the name of the events of the last memset on   *)
(* the invalid path, and instantiating the metavariable also replaces that   *)
(* variable in the other goal, so that a justification fails (with ABS).     *)
(* ------------------------------------------------------------------------- *)

let rec PFS_MA_TAC (asl,w) =
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN CONJ_TAC THEN
    PFS_MA_TAC) ORELSE
   W(fun (_,w) ->
     let l = lhand(rator w) in
     if is_cons l && not(is_const(rand l) && fst(dest_const(rand l)) = "NIL")
     then GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_CONS] THEN CONJ_TAC THEN
          PFS_MA_TAC
     else NO_TAC) ORELSE
   DISCHARGE_MEMACCESS_INBOUNDS_TAC) (asl,w);;

let PFS_LIST_CONV = REWRITE_CONV[APPEND; APPEND_NIL; GSYM APPEND_ASSOC];;

let PFS_MEMACCESS_TAC =
  let isenum t = try fst(dest_const t) = "ENUMERATEL" with Failure _ -> false in
  CONV_TAC(RATOR_CONV(RATOR_CONV(RAND_CONV PFS_LIST_CONV))) THEN
  TRY(FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_var(lhs c) && can (find_term isenum) (rhs c)
    then REWRITE_TAC[GSYM(CONV_RULE(RAND_CONV PFS_LIST_CONV) th)]
    else NO_TAC)) THEN
  PFS_MA_TAC;;

let pfs_meta_count = ref 0;;

let PFS_META_EXISTS_TAC (asl,w) =
  let v = fst(dest_exists w) in
  pfs_meta_count := !pfs_meta_count + 1;
  let v' = mk_var("pfs_" ^ fst(dest_var v) ^ "_" ^
                  string_of_int !pfs_meta_count,type_of v) in
  (CONV_TAC(GEN_ALPHA_CONV v') THEN SAFE_META_EXISTS_TAC allowed_vars_e)
  (asl,w);;

let PFS_EVENTS_TAC =
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
  PFS_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    if is_conj w then CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
    else ALL_TAC) THEN
  PFS_MEMACCESS_TAC;;

(* ------------------------------------------------------------------------- *)
(* The proof of a FULL theorem for mldsa{44,65,87}_pk_from_sk. The record    *)
(* gives the parameter set (k, l, eta and the p bytes of a packed polynomial *)
(* of s1 and s2, with its unpacking), the sizes of the secret and the public *)
(* key, the stack (the frames of the function and its callees together, and  *)
(* that of the function alone), the theorems for the callees and the value   *)
(* of x28 in the loop, which differs between the parameter sets (with RHO    *)
(* for the address of the copy of rho on the stack). The buffers of the      *)
(* function are 32-byte aligned, at a base b from the stack pointer that     *)
(* depends on whether the stack pointer is a multiple of 32, so the proof    *)
(* has two cases, each with one loop over the 26 * k chunks of 16 bytes of   *)
(* t0 that the code compares (as mld_or_fold and mld_xor_fold). Before the   *)
(* loop come the copies of rho, the key and tr, and the calls that unpack    *)
(* and check s1 and s2, transform s1 and compute t (pfs_steps finds their    *)
(* steps from the labels of the layout); after it come the result of the     *)
(* comparison, the hash of the public key, the comparison of tr, the check   *)
(* (the validity predicate) and the two paths to the return, with the calls  *)
(* of memset.                                                                *)
(* ------------------------------------------------------------------------- *)

type pfs_prm =
 { pfs_exec : thm * thm option array;
   pfs_fn : string;
   pfs_k : int; pfs_l : int; pfs_eta : int; pfs_p : int;
   pfs_unpack : term;
   pfs_sk : int; pfs_pk : int; pfs_fr : int; pfs_own : int;
   pfs_cpt : thm; pfs_unpack_th : thm; pfs_chkl : thm; pfs_chkk : thm;
   pfs_ntt : thm; pfs_shake : thm;
   pfs_x28 : term };;

let pfs_n = mk_small_numeral;;
let pfs_sp n = subst [pfs_n n,`n:num`] `word_add stackpointer (word n):int64`;;
let pfs_sk n = subst [pfs_n n,`n:num`] `word_add sk (word n):int64`;;

(* the buffers of the function, at offsets from the base b                   *)
let pfs_offs prm b =
  let s1b = 1024 * prm.pfs_l and t0n = 416 * prm.pfs_k in
  let t0b = b + s1b in let s2k = t0b + t0n in let trc = s2k + 1024 in
  let tr = trc + 64 in let key = tr + 64 in let rho = key + 32 in
  (t0b, s2k, trc, tr, key, rho);;

let pfs_c prm = prm.pfs_fr - prm.pfs_own + 143;;
let pfs_bases prm =
  let c = pfs_c prm in
  let a = c land (lnot 31) and u = ((16 + c) land (lnot 31)) - 16 in (a, u);;

let pfs_inst prm =
  let n = pfs_n in
  let k = prm.pfs_k and l = prm.pfs_l and p = prm.pfs_p in
  vsubst [n k,`KK:num`; n l,`LL:num`; n prm.pfs_eta,`ETA:num`; n p,`PP:num`;
          n prm.pfs_sk,`SKL:num`; n prm.pfs_pk,`PKL:num`;
          n (128 + l * p),`S2O:num`; n (128 + (l + k) * p),`T0O:num`;
          n (416 * k),`T0N:num`; n (26 * k),`NCH:num`;
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
  let eb = pfs_n(prm.pfs_eta + 1) in
  let chk1 = list_mk_comb(`mld_polyvec_chknorm`,
               [pfs_n prm.pfs_l; s1; mk_comb(`word:num->int32`,eb)])
  and chk2 = list_mk_comb(`mld_polyvec_chknorm`,
               [pfs_n prm.pfs_k; s2; mk_comb(`word:num->int32`,eb)]) in
  (s1, s2, skt0, t0, pkf, valid, m, h, chk1, chk2);;

let pfs_invariant prm b =
  let (s1,s2,skt0,t0,pkf,valid,m,h,chk1,chk2) = pfs_terms prm in
  let (t0b,s2k,trc,tr,key,rho) = pfs_offs prm b in
  let spf = prm.pfs_fr - prm.pfs_own in
  let n = pfs_n in
  let tm = pfs_inst prm (subst
   [n b,`B:num`; n t0b,`T0B:num`; n s2k,`S2K:num`; n rho,`RHO:num`;
    n spf,`SPF:num`; n (prm.pfs_fr - 8),`CAN:num`;
    n tr,`TR0:num`; n (tr + 16),`TR1:num`; n (tr + 32),`TR2:num`;
    n (tr + 48),`TR3:num`;
    n (spf + 8),`SP8:num`; n (spf + 16),`SP16:num`; n (spf + 24),`SP24:num`;
    n (spf + 32),`SP32:num`; n (spf + 40),`SP40:num`; n (spf + 48),`SP48:num`;
    n (spf + 56),`SP56:num`; n (spf + 64),`SP64:num`; n (spf + 72),`SP72:num`;
    n (spf + 80),`SP80:num`;
    skt0,`skt0:num->byte`; t0,`t0c:num->byte`; pkf,`pkc:num->byte`;
    chk1,`chk1:int32`; chk2,`chk2:int32`;
    subst [n rho,`RHO:num`] prm.pfs_x28,`x28v:int64`]
   `\i s. read X0 s = word_add stackpointer (word(T0B + 16 * i)) /\
          read X1 s = word_add stackpointer (word S2K) /\
          read X19 s = word_add stackpointer (word B) /\
          read X20 s = word_add sk (word(T0O + 16 * i)) /\
          read X21 s = pk /\
          read X22 s = word 0 /\
          read X23 s = word_add stackpointer (word RHO) /\
          read X24 s = word_add stackpointer (word T0B) /\
          read X25 s = word_zx(chk1:int32) /\
          read X26 s = word_add stackpointer (word S2K) /\
          read X27 s = word_zx(chk2:int32) /\
          read X28 s = x28v /\
          read SP s = word_add stackpointer (word SPF) /\
          read (memory :> bytes64 (word_add stackpointer (word SPF))) s =
            x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word SP8))) s =
            x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word SP16))) s =
            x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word SP24))) s =
            x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word SP32))) s =
            x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word SP40))) s =
            x24_init /\
          read (memory :> bytes64 (word_add stackpointer (word SP48))) s =
            x25_init /\
          read (memory :> bytes64 (word_add stackpointer (word SP56))) s =
            x26_init /\
          read (memory :> bytes64 (word_add stackpointer (word SP64))) s =
            x27_init /\
          read (memory :> bytes64 (word_add stackpointer (word SP72))) s =
            x28_init /\
          read (memory :> bytes64 (word_add stackpointer (word SP80))) s =
            returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word CAN))) s =
            canary /\
          read (memory :> bytes64 (word_add (word pc)
                  (word got_stack_chk_guard))) s = guard /\
          read (memory :> bytes64 guard) s = canary /\
          read (memory :> bytes64 (word_add (word pc) (word got_memset))) s =
            mf /\
          read (memory :> bytes (ea,el)) s = ev /\
          read Q2 s = mld_or_fold (mld_chunk128 skt0) (mld_chunk128 t0c) i /\
          read Q1 s = mld_xor_fold (mld_chunk128 skt0) (mld_chunk128 t0c) i /\
          (!j. j < SKL
               ==> read(memory :> bytes8(word_add sk (word j))) s = skb j) /\
          (!j. j < T0N
               ==> read(memory :> bytes8
                         (word_add stackpointer (word(T0B + j)))) s =
                   t0c j) /\
          (!j. j < PKL
               ==> read(memory :> bytes8(word_add pk (word j))) s = pkc j) /\
          read (memory :> bytes128 (word_add stackpointer (word TR0))) s =
            mld_chunk128 skb 4 /\
          read (memory :> bytes128 (word_add stackpointer (word TR1))) s =
            mld_chunk128 skb 5 /\
          read (memory :> bytes128 (word_add stackpointer (word TR2))) s =
            mld_chunk128 skb 6 /\
          read (memory :> bytes128 (word_add stackpointer (word TR3))) s =
            mld_chunk128 skb 7`) in
  tm;;

let pfs_allowed =
  [`pc:num`; `pk:int64`; `sk:int64`; `skb:num->byte`; `guard:int64`;
   `mf:int64`; `stackpointer:int64`; `returnaddress:int64`; `r:num`];;

let PFS_CALL_TAC prm name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc prm.pfs_exec name ilist
   pfs_allowed n;;

(* the steps of the code before the loop: the bl of each call, the step of   *)
(* the adrp and of the and that rounds the buffer address                    *)
let pfs_steps prm =
  let base = layout prm.pfs_fn in
  let lbl s = layout(prm.pfs_fn ^ "_" ^ s) - base in
  let k = String.sub prm.pfs_fn 5 2 in
  let afters = ["after_mldsa" ^ k ^ "_polyvecl_unpack_eta";
                "after_mldsa" ^ k ^ "_polyvecl_chknorm";
                "after_mldsa" ^ k ^ "_polyveck_unpack_eta_chknorm";
                "after_mldsa" ^ k ^ "_polyvecl_ntt";
                "after_mld_compute_pack_t0_t1" ^ k] in
  let bls = List.mapi (fun c a -> (lbl a - 4) / 4 + 1 + c) afters in
  let adrp = lbl "adrp1" / 4 + 1 in
  let fin = List.nth bls 4 + 1 + 2 + (lbl "loop1" - (lbl "ret" + 4)) / 4 in
  (bls, adrp, fin);;

let PFS_STEPS_TAC prm bth adrp a b =
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC prm.pfs_exec [n] THEN
    (if n = 11 then MEXP_BUFFER_TAC bth else ALL_TAC) THEN
    (if n = adrp then MLKEM_NATIVE_ADRP_TAC else ALL_TAC)) (a--b);;

let PFS_SK_CHUNKS_TAC prm =
  let skl = pfs_n prm.pfs_sk in
  W(fun (asl,w) ->
    let skf = find (fun th -> can (term_match []
       (subst [skl,`n:num`]
         `!j. j < n ==> read(memory :> bytes8(word_add sk (word j))) s =
                        skb j`)) (concl th)) (map snd asl) in
    MAP_EVERY (fun m ->
      let th = MP (SPECL [`sk:int64`; skl; `skb:num->byte`;
                          rand(lhand(rand(snd(dest_forall(concl skf)))));
                          pfs_n m] BYTES128_OF_BYTES8)
                  (CONJ skf (EQT_ELIM(NUM_REDUCE_CONV
                     (subst [pfs_n m,`m:num`; skl,`n:num`]
                       `16 * m + 16 <= n`)))) in
      ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
                           REWRITE_CONV[WORD_ADD_0]) th)) (0--7));;

let PFS_INIT_TAC prm b =
  let (s1,s2,skt0,t0,pkf,valid,m,h,chk1,chk2) = pfs_terms prm in
  let (t0b,s2k,trc,tr,key,rho) = pfs_offs prm b in
  let (bls,adrp,fin) = pfs_steps prm in
  let bl i = List.nth bls i in
  let (ca,cu) = pfs_bases prm in
  let bth = MEXP_BUFFER_ADDRESS_RULE (pfs_c prm) ca cu in
  let st n = mk_var("s" ^ string_of_int n,`:armstate`) in
  let inst = pfs_inst prm in
  let teq = (REWRITE_CONV[mld_pk_from_sk_t; mld_sk_s1] THENC
             REWRITE_CONV[ADD_ASSOC] THENC NUM_REDUCE_CONV)
            (inst `mld_pk_from_sk_t LL unpack PP (skb:num->byte)`) in
  let slice off len s =
    inst(subst [pfs_n off,`ofs:num`; pfs_n len,`n:num`; st s,`s:armstate`]
      `!j. j < n ==> read(memory :> bytes8(word_add sk (word(ofs + j)))) s =
                     (skb:num->byte)(ofs + j)`) in
  let s2o = 128 + prm.pfs_l * prm.pfs_p in
  FULL_INIT_TAC THEN PFS_SK_CHUNKS_TAC prm THEN
  PFS_STEPS_TAC prm bth adrp 1 (bl 0) THEN
  VEC_SLICE_TAC (slice 128 (prm.pfs_l * prm.pfs_p) (bl 0)) THEN
  PFS_CALL_TAC prm "H_UNPACK"
   [`read X0 s`; `read X1 s`; `\j. (skb:num->byte)(128 + j)`; `pc:num`;
    `read SP s`; `read X30 s`] (bl 0 + 1) THEN
  PFS_STEPS_TAC prm bth adrp (bl 0 + 2) (bl 1) THEN
  PFS_CALL_TAC prm "H_CHKL"
   [`read X0 s`; s1; `read X1 s`; `pc:num`; `read SP s`; `read X30 s`]
   (bl 1 + 1) THEN
  PFS_STEPS_TAC prm bth adrp (bl 1 + 2) (bl 2) THEN
  VEC_SLICE_TAC (slice s2o (prm.pfs_k * prm.pfs_p) (bl 2)) THEN
  PFS_CALL_TAC prm "H_CHKK"
   [`read X0 s`; inst `\j. (skb:num->byte)(S2O + j)`; `read X1 s`;
    `read X2 s`; `pc:num`; `read SP s`; `read X30 s`] (bl 2 + 1) THEN
  PFS_STEPS_TAC prm bth adrp (bl 2 + 2) (bl 3) THEN
  PFS_CALL_TAC prm "H_NTT"
   [`read X0 s`; s1; `pc:num`; `read SP s`; `read X30 s`] (bl 3 + 1) THEN
  PFS_STEPS_TAC prm bth adrp (bl 3 + 2) (bl 4) THEN
  MP_TAC(ISPECL [pfs_sp rho; `skb:num->byte`; st (bl 4)]
                MLD_BYTES32_OF_CHUNKS) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM mld_sk_rho] THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(fun eq ->
      if concl eq = `mld_sk_rho skb = r` then ASSUME_TAC(REWRITE_RULE[eq] th)
      else NO_TAC))] THEN
  PFS_CALL_TAC prm "H_CPT"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    mk_comb(`mld_polyvec_map mld_poly_ntt`,s1);
    inst `\j. (skb:num->byte)(S2O + j)`; `r:num`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] (bl 4 + 1) THEN
  PFS_STEPS_TAC prm bth adrp (bl 4 + 2) fin THEN
  FIRST_ASSUM(fun th1 ->
    if lhs(concl th1) = mk_comb(`read (memory :> bytes128 pk)`,st fin) then
      FIRST_ASSUM(fun th2 ->
        if lhs(concl th2) =
           mk_comb(`read (memory :> bytes128 (word_add pk (word 16)))`,st fin)
        then ASSUME_TAC(MATCH_MP MLD_BYTES8_OF_CHUNKS2 (CONJ th1 th2))
        else NO_TAC)
    else NO_TAC) THEN
  FIRST_ASSUM(fun th1 ->
    if can (term_match [] (subst [st fin,`s:armstate`]
          `!j. j < 32 ==> read (memory :> bytes8
              (word_add pk (word j))) s = (skb:num->byte) j`)) (concl th1)
    then FIRST_ASSUM(fun th2 ->
      if can (term_match [] (subst [st fin,`s:armstate`;
                                    pfs_n(prm.pfs_pk - 32),`n:num`]
           `!j. j < n ==> read (memory :> bytes8
                (word_add pk (word(32 + j)))) s = (g:num->byte) j`))
             (concl th2)
      then ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)
                       (MATCH_MP MLD_BYTES8_JOIN (CONJ th1 th2)))
      else NO_TAC)
    else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_ZX_32]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[teq; mld_pk_from_sk_pk; mld_or_fold; mld_xor_fold;
              MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN PFS_EVENTS_TAC;;

let PFS_BODY_TAC prm b =
  let (s1,s2,skt0,t0,pkf,valid,m,h,chk1,chk2) = pfs_terms prm in
  let (t0b,s2k,trc,tr,key,rho) = pfs_offs prm b in
  let t0o = 128 + (prm.pfs_l + prm.pfs_k) * prm.pfs_p
  and t0n = 416 * prm.pfs_k in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  MP_TAC(SPECL [pfs_sk t0o; pfs_n t0n; skt0; `s0:armstate`; `i:num`]
               BYTES128_OF_BYTES8) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN BETA_TAC THEN
      FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN SIMPLE_ARITH_TAC);
      SIMPLE_ARITH_TAC];
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
    DISCH_TAC] THEN
  MP_TAC(SPECL [pfs_sp t0b; pfs_n t0n; t0; `s0:armstate`; `i:num`]
               BYTES128_OF_BYTES8) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN SIMPLE_ARITH_TAC);
      SIMPLE_ARITH_TAC];
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
    DISCH_TAC] THEN
  ARM_STEPS_TAC prm.pfs_exec (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[MLD_OR_FOLD_ADD1; MLD_XOR_FOLD_ADD1] THEN
  PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(W(fun (_,w) -> ACCEPT_TAC(WORD_BITWISE_RULE w)) THEN NO_TAC) THEN
  PFS_EVENTS_TAC;;

let pfs_asm_rhs (asl,w) l =
  rhs(concl(snd(find (fun (_,th) ->
    try lhs(concl th) = l with Failure _ -> false) asl)));;

let PFS_FINAL_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_0]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  PFS_EVENTS_TAC;;

let PFS_EXIT_GEN_TAC fin prm b =
  let (s1,s2,skt0,t0,pkf,valid,m,h,chk1,chk2) = pfs_terms prm in
  let (t0b,s2k,trc,tr,key,rho) = pfs_offs prm b in
  let inst = pfs_inst prm in
  let fold f = subst [skt0,`skt0:num->byte`; t0,`t0c:num->byte`] f in
  let spill = prm.pfs_fr - prm.pfs_own + 108 in
  let pkl = pfs_n prm.pfs_pk in
  let vth = (REWRITE_CONV[mld_pk_from_sk_valid; mld_sk_s1; mld_sk_s2] THENC
             REWRITE_CONV[ADD_ASSOC] THENC NUM_REDUCE_CONV) valid in
  let s33 = `s33:armstate` and s35 = `s35:armstate` in
  REWRITE_TAC[] THEN
  ABBREV_TAC (mk_eq(`v2:int128`, inst(fold
    `mld_or_fold (mld_chunk128 skt0) (mld_chunk128 t0c) NCH`))) THEN
  ABBREV_TAC (mk_eq(`v1:int128`, inst(fold
    `mld_xor_fold (mld_chunk128 skt0) (mld_chunk128 t0c) NCH`))) THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC prm.pfs_exec (1--33) THEN
  RULE_ASSUM_TAC(fun th ->
    try let l = lhs(concl th) in
        if l = `read X4 s33` ||
           l = subst [pfs_sp spill,`a:int64`] `read (memory :> bytes32 a) s33`
        then PFS_CMP_RULE `v2:int128` `v1:int128` th else th
    with Failure _ -> th) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [pkl,`n:num`] `!j. j < n ==> read(memory :>
              bytes8(word_add pk (word j))) s33 = (f:num->byte) j`)) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX] (MATCH_MP READ_BYTES_OF_BYTES8 th))
    else NO_TAC) THEN
  ARM_STEPS_TAC prm.pfs_exec (34--34) THEN
  PFS_CALL_TAC prm "H_SHAKE"
   [`read X0 s`; `64`; `read X2 s`; pkl; m; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 35 THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [pfs_sp trc,`a:int64`]
         `read (memory :> bytes (a,64)) s35 = x`)) (concl th)
    then ASSUME_TAC(MATCH_MP BYTES8_OF_BYTES th) else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [pfs_sp trc,`a:int64`]
         `!j. j < 64 ==> read (memory :> bytes8 (word_add a (word j))) s35 =
                         (f:num->byte) j`)) (concl th)
    then MAP_EVERY (fun i ->
      ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
        (CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
          (MP (SPECL [pfs_sp trc; `64`; h; s35; pfs_n i] BYTES128_OF_BYTES8)
              (CONJ th (EQT_ELIM(NUM_REDUCE_CONV
                 (subst [pfs_n i,`i:num`] `16 * i + 16 <= 64`))))))))
      (0--3)
    else NO_TAC) THEN
  ARM_STEPS_TAC prm.pfs_exec (36--48) THEN PFS_DECIDE_TAC THEN
  ARM_STEPS_TAC prm.pfs_exec (49--55) THEN PFS_DECIDE_TAC THEN
  ARM_STEPS_TAC prm.pfs_exec (56--62) THEN PFS_DECIDE_TAC THEN
  ARM_STEPS_TAC prm.pfs_exec (63--69) THEN PFS_DECIDE_TAC THEN
  W(fun g ->
    let q2v = pfs_asm_rhs g `read Q2 s69`
    and q0v = pfs_asm_rhs g `read Q0 s69` in
    ARM_STEPS_TAC prm.pfs_exec (70--94) THEN
    RULE_ASSUM_TAC(fun th ->
      try if lhs(concl th) = `read X0 s94` then PFS_CMP_RULE q2v q0v th
          else th
      with Failure _ -> th) THEN
    ARM_STEPS_TAC prm.pfs_exec (95--98) THEN
    W(fun g' ->
      let pcv = pfs_asm_rhs g' `read PC s98` in
      let cond = rand(rator(rator pcv)) in
      let t0eq = mk_iff(inst(subst [t0,`t0c:num->byte`; skt0,`skt0:num->byte`]
        `mld_ct_memcmp t0c skt0 T0N = word 0`), `(v2:int128) = word 0`)
      and treq = mk_iff(mk_eq(list_mk_comb(`mld_ct_memcmp`,
           [`\j. (skb:num->byte)(64 + j)`; h; `64`]), `word 0:byte`),
         mk_eq(q2v,`word 0:int128`)) in
      SUBGOAL_THEN t0eq (LABEL_TAC "T0EQ") THENL
       [REWRITE_TAC[MLD_CT_MEMCMP_EQ_0] THEN
        FIRST_ASSUM(fun th -> if rhs(concl th) = `v2:int128`
                              then REWRITE_TAC[GSYM th] else NO_TAC) THEN
        REWRITE_TAC[MLD_OR_FOLD_EQ_0; MLD_CHUNK128_EQ] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN BETA_TAC THEN
        MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN treq (LABEL_TAC "TREQ") THENL
       [REWRITE_TAC[MLD_CT_MEMCMP_EQ_0; WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
        BETA_TAC THEN REWRITE_TAC[MLD_CHUNKS4_EQ; ETA_AX] THEN
        W(fun (_,w) -> ACCEPT_TAC(CONJ_ACI_RULE w));
        ALL_TAC] THEN
      SUBGOAL_THEN (mk_iff(cond, valid)) (LABEL_TAC "CHECK") THENL
       [USE_THEN "T0EQ" (fun t0th -> USE_THEN "TREQ" (fun trth ->
          REWRITE_TAC[vth; t0th; trth])) THEN
        SPEC_TAC(mk_eq(q2v,`word 0:int128`),`b:bool`) THEN
        SPEC_TAC(`(v2:int128) = word 0`,`a:bool`) THEN
        SPEC_TAC(chk2,`c2:int32`) THEN SPEC_TAC(chk1,`c1:int32`) THEN
        REPEAT GEN_TAC THEN BOOL_CASES_TAC `a:bool` THEN
        BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[] THEN
        SPEC_TAC(`c2:int32`,`c2:int32`) THEN SPEC_TAC(`c1:int32`,`c1:int32`)
        THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));
        ALL_TAC] THEN
      USE_THEN "CHECK" (fun th -> RULE_ASSUM_TAC(fun t ->
        if pfs_pcev t then REWRITE_RULE[th] t else t)))) THEN
  PFS_CASES_TAC valid THEN
  PFS_RUN_TAC prm.pfs_exec prm.pfs_fn pfs_allowed 99 THEN
  fin;;

let PFS_EXIT_TAC = PFS_EXIT_GEN_TAC PFS_FINAL_TAC;;

let PFS_CASE_TAC prm b =
  let lbl s = mk_binary "+" (`pc:num`,pfs_n(layout(prm.pfs_fn ^ "_" ^ s))) in
  ENSURES_EVENTS_WHILE_UP2_TAC (pfs_n(26 * prm.pfs_k)) (lbl "loop1")
   (lbl "loop1_exit") (pfs_invariant prm b) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; PFS_INIT_TAC prm b; PFS_BODY_TAC prm b; PFS_EXIT_TAC prm b];;

let PFS_SETUP_TAC prm =
  let nch = pfs_n(26 * prm.pfs_k) in
  let template = subst [nch,`n:num`]
   `\(pk:int64) (sk:int64) (rho:num) (valid:bool) (guard:int64) (mf:int64)
     (pc:num) (stackpointer:int64) (returnaddress:int64).
     if aligned 32 stackpointer
     then APPEND
           (if valid
            then f_ev_epil_av pk sk rho guard mf pc stackpointer returnaddress
            else f_ev_epil_ai pk sk rho guard mf pc stackpointer returnaddress)
           (APPEND
             (ENUMERATEL n
               (\i. f_ev_loop_a pk sk rho guard mf pc stackpointer
                                returnaddress i))
             (f_ev_prol_a pk sk rho guard mf pc stackpointer returnaddress))
     else APPEND
           (if valid
            then f_ev_epil_uv pk sk rho guard mf pc stackpointer returnaddress
            else f_ev_epil_ui pk sk rho guard mf pc stackpointer returnaddress)
           (APPEND
             (ENUMERATEL n
               (\i. f_ev_loop_u pk sk rho guard mf pc stackpointer
                                returnaddress i))
             (f_ev_prol_u pk sk rho guard mf pc stackpointer returnaddress))
     :(uarch_event)list` in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP prm.pfs_cpt th) "H_CPT") THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th)
     "H_MEMSET") THEN
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
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC (subst [pfs_sp prm.pfs_fr,`a:int64`] `aligned 16 (a:int64)`)
    THEN CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--28);;

let PFS_FULL_TAC prm =
  let (ca,cu) = pfs_bases prm in
  PFS_SETUP_TAC prm THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN
    PFS_CASE_TAC prm ca;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    PFS_CASE_TAC prm cu];;
