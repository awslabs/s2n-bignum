(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The domain separation prefix: the proof (see                              *)
(* prepare_domain_separation_prefix_65_spec.ml).                             *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/prepare_domain_separation_prefix_65_spec.ml";;

let MLD_PREFIX65_EXEC =
  MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The two tables in the image, the address of oid_map, the addresses of     *)
(* the code after the check of the length of the pre-hash (JOIN) and of the  *)
(* load of the hashalg field in the loop over oid_map (HEAD), and the calls  *)
(* of memcpy, whose events may depend on the variables of the template.      *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX65_JUMP_TABLE =
  MLD_PREFIX_IMAGE_BYTES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   (layout "mldsa65_prepare_domain_separation_prefix_jump_table") 12;;

let MLD_PREFIX65_OID_MAP =
  MLD_PREFIX_IMAGE_BYTES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   (layout "mldsa65_prepare_domain_separation_prefix_oid_map") 192;;

let MLD_PREFIX65_OID =
  mk_small_numeral(layout "mldsa65_prepare_domain_separation_prefix_oid_map");;

let MLD_PREFIX65_JOIN =
  mk_comb(mk_comb(`(+):num->num->num`,`pc:num`),
          mk_small_numeral(layout "mldsa65_prepare_domain_separation_prefix" +
                           0x5c))
and MLD_PREFIX65_HEAD =
  mk_comb(mk_comb(`(+):num->num->num`,`pc:num`),
          mk_small_numeral(layout "mldsa65_prepare_domain_separation_prefix" +
                           0x88));;

let MLD_PREFIX65_MEMCPY_TAC x n =
  LIBC_SAFE_CALL_TAC "H_MEMCPY" MLD_PREFIX65_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; x;
    `read X30 s`]
   (ref [`prefix:int64`; `ph:int64`; `phlen:num`; `ctx:int64`;
         `ctxlen:num`; `hashalg:int64`; `mc:int64`; `pc:num`;
         `stackpointer:int64`; `returnaddress:int64`]) n;;

(* ------------------------------------------------------------------------- *)
(* The states at adrp1 (after the checks of ctxlen and of the range of       *)
(* hashalg) and at JOIN (after the check of the length of the pre-hash),     *)
(* with the frame of 48 bytes at stackpointer.                               *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX65_FRAME =
 `\s. read SP s = stackpointer /\
      read (memory :> bytes64 stackpointer) s = x19_init /\
      read (memory :> bytes64 (word_add stackpointer (word 8))) s =
      x20_init /\
      read (memory :> bytes64 (word_add stackpointer (word 16))) s =
      x21_init /\
      read (memory :> bytes64 (word_add stackpointer (word 24))) s =
      x22_init /\
      read (memory :> bytes64 (word_add stackpointer (word 32))) s =
      x23_init /\
      read (memory :> bytes64 (word_add stackpointer (word 40))) s =
      returnaddress /\
      read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s =
      mc /\
      read (memory :> bytes(ea,el)) s = ev /\
      read (memory :> bytes(ph,phlen)) s = P`;;

let MLD_PREFIX65_APP f x = rhs(concl(BETA_CONV(mk_comb(f,x))));;

let MLD_PREFIX65_STATE extra =
  let s = `s:armstate` in
  mk_abs(s,mk_conj(MLD_PREFIX65_APP extra s,
                   MLD_PREFIX65_APP MLD_PREFIX65_FRAME s));;

let MLD_PREFIX65_MID1 = MLD_PREFIX65_STATE
 `\s. read X1 s = ctx /\
      read X2 s = word_zx (word_sub (word_zx (hashalg:int64):int32)
                             (word 1)):int64 /\
      read X3 s = ctx /\ read X4 s = word ctxlen /\
      read X5 s = hashalg /\
      read X19 s = word ctxlen /\ read X20 s = word phlen /\
      read X21 s = prefix /\
      read X22 s = word_zx (word_zx (hashalg:int64):int32):int64 /\
      read X23 s = ph /\
      read (memory :> bytes(ctx,ctxlen)) s = C`;;

let MLD_PREFIX65_MID2 = MLD_PREFIX65_STATE
 `\s. read X1 s = ctx /\ read X3 s = ctx /\ read X4 s = word ctxlen /\
      read X5 s = (hashalg:int64) /\
      read X19 s = word ctxlen /\ read X20 s = word phlen /\
      read X21 s = prefix /\
      read X22 s = word_zx (word_zx (hashalg:int64):int32):int64 /\
      read X23 s = ph /\
      read (memory :> bytes(ctx,ctxlen)) s = C`;;

(* ------------------------------------------------------------------------- *)
(* The invariant of the loop over oid_map, at the load of the hashalg field  *)
(* of entry i, for i entries checked: w1 = i and x2 = 16 * i, except after   *)
(* the last iteration, which leaves them at the entry found (hashalg - 1,    *)
(* hence the MIN), with the address of oid_map in x0 and the first bytes of  *)
(* the prefix written.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX65_INV extra =
  let i = `i:num` and s = `s:armstate` in
  let core = subst [MLD_PREFIX65_OID,`oid:num`]
   `\(i:num) s.
       read X0 s = word_add (word pc) (word oid) /\
       read X1 s = word(MIN i (val(word_zx (hashalg:int64):int32) - 1)) /\
       read X2 s = word(16 * MIN i (val(word_zx hashalg:int32) - 1)) /\
       read X20 s = word phlen /\ read X21 s = prefix /\
       read X22 s = word_zx (word_zx (hashalg:int64):int32):int64 /\
       read X23 s = ph /\
       read (memory :> bytes8 prefix) s = word 1` in
  list_mk_abs([i;s],
   list_mk_conj[MLD_PREFIX65_APP (MLD_PREFIX65_APP core i) s;
                MLD_PREFIX65_APP extra s;
                MLD_PREFIX65_APP MLD_PREFIX65_FRAME s]);;

let MLD_PREFIX65_INV0 = MLD_PREFIX65_INV
 `\s. read X19 s = word 0 /\
      read (memory :> bytes8 (word_add prefix (word 1))) s = word 0`;;

let MLD_PREFIX65_INV1 = MLD_PREFIX65_INV
 `\s. read X19 s = word ctxlen /\
      read (memory :> bytes8 (word_add prefix (word 1))) s = word ctxlen /\
      read (memory :> bytes(word_add prefix (word 2),ctxlen)) s = C`;;

(* ------------------------------------------------------------------------- *)
(* The facts from the image: the hashalg fields of the entries of oid_map,   *)
(* for the loop, and the OID of entry j in two parts, its first 8 bytes      *)
(* (the same for all) and its bytes 7 to 10, with the addresses as the code  *)
(* computes them.                                                            *)
(* ------------------------------------------------------------------------- *)

(*** The address of entry j as the load [x2, x0] computes it ***)

let MLD_PREFIX65_ENTRY_ADDR = prove
 (subst [MLD_PREFIX65_OID,`oid:num`]
   `!j. word_add (word(16 * j)) (word_add (word pc) (word oid)):int64 =
        word_add (word pc) (word (oid + 16 * j))`,
  GEN_TAC THEN CONV_TAC WORD_RULE);;

let MLD_PREFIX65_ALGS_TAC =
  SUBGOAL_THEN (subst [MLD_PREFIX65_OID,`oid:num`]
    `!j. j < 12
         ==> read (memory :> bytes32
                    (word_add (word pc) (word (oid + 16 * j)))) s0 =
             word(j + 1)`) ASSUME_TAC THENL
   [MAP_EVERY (fun j -> MLD_PREFIX_TABLE_TAC MLD_PREFIX65_OID_MAP (16 * j) 4)
     (0--11) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    ASSUME_TAC(REWRITE_RULE[GSYM MLD_PREFIX65_ENTRY_ADDR] th));;

(*** The addresses of the OID of entry j as [x0, x2] and [x4, #7] with   ***)
(*** x2 = 16 * j + 4 and x4 = x0 + x2 compute them                       ***)

let MLD_PREFIX65_ENTRY_ADDR2 = prove
 (subst [MLD_PREFIX65_OID,`oid:num`]
   `!j. word_add (word_add (word pc) (word oid))
          (word_add (word(16 * j)) (word 4)):int64 =
        word_add (word pc) (word (oid + (4 + 16 * j))) /\
        word_add (word_add (word_add (word pc) (word oid))
          (word_add (word(16 * j)) (word 4))) (word 7):int64 =
        word_add (word pc) (word (oid + (4 + 16 * j) + 7))`,
  GEN_TAC THEN CONJ_TAC THEN CONV_TAC WORD_RULE);;

let MLD_PREFIX65_OID_TAC =
  SUBGOAL_THEN (subst [MLD_PREFIX65_OID,`oid:num`]
    `!j. j < 12
         ==> read (memory :> bytes64
                    (word_add (word_add (word pc) (word oid))
                      (word (4 + 16 * j)))) s0 =
             word 0x0365014886600906 /\
             read (memory :> bytes32
                    (word_add (word_add (word_add (word pc) (word oid))
                      (word (4 + 16 * j))) (word 7))) s0 =
             word (0x20403 + 0x1000000 *
                             val(EL 10 (mld_prehash_oid (j + 1))))`)
  ASSUME_TAC THENL
   [MAP_EVERY (fun j ->
      MLD_PREFIX_TABLE_TAC MLD_PREFIX65_OID_MAP (16 * j + 4) 8 THEN
      MLD_PREFIX_TABLE_TAC MLD_PREFIX65_OID_MAP (16 * j + 11) 4) (0--11) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[mld_prehash_oid] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
             ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* From adrp1 to JOIN or to the return of 0, for hashalg = k: the jump       *)
(* through the table (the byte at k - 1) to the check of the length of the   *)
(* pre-hash for k (CMP x20 and B.NE, with a B in between for the targets     *)
(* that share the B.NE), which takes 8 or 9 instructions to the code after   *)
(* the check if it holds, and 14 or 15 to the return if not.                 *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX65_JUMP_TAC valid k =
  let hk = mk_eq(`val(word_zx (hashalg:int64):int32)`,mk_small_numeral k) in
  let m = if mem k [1;5;7] then 8 else 9 in
  let n = if valid then m else m + 6 in
  let wk = mk_eq(`word_zx (hashalg:int64):int32`,
                 mk_comb(`word:num->int32`,mk_small_numeral k)) in
  REWRITE_TAC[ASSUME hk; ARITH_EQ] THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN wk (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
    RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN ASSUME_TAC th) THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_32] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MLD_PREFIX_TABLE_TAC MLD_PREFIX65_JUMP_TABLE (k - 1) 1 THEN
  ARM_STEPS_TAC MLD_PREFIX65_EXEC (1--1) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_PREFIX65_EXEC (2--6) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV MLD_PREFIX_PC_CONV)) THEN
  ARM_STEPS_TAC MLD_PREFIX65_EXEC (7--m) THEN MLD_PREFIX_BRANCH_TAC THEN
  (if n > m then ARM_STEPS_TAC MLD_PREFIX65_EXEC (m+1--n) else ALL_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* An iteration of the loop: the entry i, i < hashalg, is i + 1, and either  *)
(* i + 1 < hashalg and the loop continues, or it is hashalg and the loop     *)
(* exits to loop1_exit1.                                                     *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX65_CMP12 = prove
 (`!i. i < 12
       ==> (val(word_add (word i) (word 18446744073709551605):int64) = 0 <=>
            i = 11)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLD_PREFIX65_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `MIN i (val(word_zx (hashalg:int64):int32) - 1) = i /\
    MIN (i + 1) (val(word_zx (hashalg:int64):int32) - 1) =
    (if i + 1 < val(word_zx (hashalg:int64):int32) then i + 1 else i)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[MIN] THEN CONJ_TAC THEN TRY COND_CASES_TAC THEN
    TRY COND_CASES_TAC THEN MEMSAFE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `i < 12 /\ i + 1 < 2 EXP 32` STRIP_ASSUME_TAC THENL
   [MEMSAFE_ARITH_TAC; ALL_TAC] THEN
  ASSUME_TAC(MP (SPEC `i:num` MLD_PREFIX65_CMP12) (ASSUME `i < 12`)) THEN
  SUBGOAL_THEN `val(word(i + 1):int32) = i + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FULL_INIT_TAC THEN MLD_PREFIX65_ALGS_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC MLD_PREFIX65_EXEC (1--3) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_PREFIX_ZX_ZX]) THEN
  ASM_CASES_TAC `i + 1 < val(word_zx (hashalg:int64):int32)` THEN
  MLD_PREFIX_BRANCH_TAC THENL
   [ARM_STEPS_TAC MLD_PREFIX65_EXEC (4--6) THEN
    MLD_PREFIX_BRANCH_TAC THEN ARM_STEPS_TAC MLD_PREFIX65_EXEC (7--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE; PATH_DISCHARGE_TAC];
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    PATH_DISCHARGE_TAC];;

(* ------------------------------------------------------------------------- *)
(* After the loop: the copy of the OID of entry hashalg - 1 with an 8-byte   *)
(* load and store and a 4-byte one at offset 7 (the low 7 bytes of the first *)
(* store kept before the second), the copy of the pre-hash with memcpy and   *)
(* the return of 2 + ctxlen + 11 + phlen; memtac proves the prefix from the  *)
(* pieces in memory.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX65_EXIT_TAC memtac =
  SUBGOAL_THEN
   `MIN (val(word_zx (hashalg:int64):int32))
        (val(word_zx (hashalg:int64):int32) - 1) =
    val(word_zx (hashalg:int64):int32) - 1`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[MIN] THEN MEMSAFE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_zx (hashalg:int64):int32) - 1 < 12` ASSUME_TAC THENL
   [MEMSAFE_ARITH_TAC; ALL_TAC] THEN
  FULL_INIT_TAC THEN MLD_PREFIX65_OID_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `val(word_zx (hashalg:int64):int32) - 1`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MLD_PREFIX_ADDR_NORM_RULE) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM MLD_PREFIX65_ENTRY_ADDR2]) THEN
  ARM_STEPS_TAC MLD_PREFIX65_EXEC (1--6) THEN
  MLD_PREFIX_LOW7_TAC `prefix:int64` THEN
  ARM_STEPS_TAC MLD_PREFIX65_EXEC (7--14) THEN
  LIBC_PLT_TAC MLD_PREFIX65_EXEC 14 THEN
  MLD_PREFIX65_MEMCPY_TAC `P:num` 19 THEN
  ARM_STEPS_TAC MLD_PREFIX65_EXEC (20--25) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    memtac;
    MLD_PREFIX_DISCHARGE_TAC
     (ABBREV_TAC `j = val(word_zx (hashalg:int64):int32) - 1`)];;

(*** The common part of the two proofs of the prefix in memory ***)

let MLD_PREFIX65_PREHASH_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_PREFIX_ZX_ZX]) THEN
  SUBGOAL_THEN
   `val(word_zx (hashalg:int64):int32) - 1 + 1 =
    val(word_zx (hashalg:int64):int32)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MEMSAFE_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[MLD_PREFIX_ZX_ZX] THEN
  SUBGOAL_THEN `P < 256 EXP phlen` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM EXP_MULT]; ALL_TAC] THEN
  ASM_SIMP_TAC[NUM_OF_BYTELIST_OF_NUM_EQ] THEN
  W(fun (asl,w) ->
    let t = find_term (fun t -> is_comb t && rator t = `val:int32->num` &&
                                is_comb(rand t) &&
                                rator(rand t) = `word:num->int32`) w in
    SUBGOAL_THEN (mk_eq(t,rand(rand t))) SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN
      W(fun (asl,w) ->
        let x = find_term (fun t -> is_comb t && rator t = `val:byte->num`)
                  w in
        MP_TAC(ISPEC (rand x) VAL_BOUND)) THEN
      REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
      ALL_TAC]) THEN
  REWRITE_TAC[VAL_WORD_1; VAL_WORD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC;;

let MLD_PREFIX65_MEM0_TAC =
  MLD_PREFIX_BOUND_TAC `word_add (prefix:int64) (word 13)` THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[mld_domain_separation_prefix] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[bytelist_of_num; APPEND; LENGTH] THEN
  REWRITE_TAC[num_of_bytelist; MLD_PREFIX_NUM_OF_BYTELIST_APPEND;
              LENGTH_BYTELIST_OF_NUM; LENGTH_MLD_PREHASH_OID;
              MLD_PREFIX_OIDN] THEN
  REWRITE_TAC[MLD_PREFIX_HASH_SPLIT0; MLD_PREFIX_BYTES2] THEN
  MLD_PREFIX65_PREHASH_TAC;;

let MLD_PREFIX65_MEM1_TAC =
  MLD_PREFIX_BOUND_TAC `word_add (prefix:int64) (word 2)` THEN
  MLD_PREFIX_BOUND_TAC
   `word_add (prefix:int64) (word_add (word ctxlen) (word 13))` THEN
  SUBGOAL_THEN `C < 256 EXP ctxlen` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM EXP_MULT]; ALL_TAC] THEN
  MP_TAC(SPEC `ctxlen:num` MLD_PREFIX_VAL_BYTE) THEN
  ANTS_TAC THENL [MEMSAFE_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[mld_domain_separation_prefix] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[num_of_bytelist; MLD_PREFIX_NUM_OF_BYTELIST_APPEND;
              LENGTH_BYTELIST_OF_NUM; LENGTH_MLD_PREHASH_OID;
              MLD_PREFIX_OIDN] THEN
  REWRITE_TAC[MLD_PREFIX_HASH_SPLIT; MLD_PREFIX_BYTES2] THEN
  SIMP_TAC[NUM_OF_BYTELIST_OF_NUM_EQ; ASSUME `C < 256 EXP ctxlen`] THEN
  MLD_PREFIX65_PREHASH_TAC;;

(* ------------------------------------------------------------------------- *)
(* The prefix for pure ML-DSA in memory.                                     *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX65_PURE_MEM_TAC =
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[mld_domain_separation_prefix; LENGTH_BYTELIST_OF_NUM;
              num_of_bytelist] THEN
  REWRITE_TAC[MLD_PREFIX_BYTES_COMBINE; MLD_PREFIX_BYTES2] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `ctxlen:num` MLD_PREFIX_VAL_BYTE) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  SUBGOAL_THEN `C < 256 EXP ctxlen` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM EXP_MULT]; ALL_TAC] THEN
  ASM_SIMP_TAC[NUM_OF_BYTELIST_OF_NUM_EQ; VAL_WORD_0] THEN ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX65_SETUP_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[memcpy_full_contract] THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMCPY") THEN
  CONCRETIZE_F_EVENTS_TAC MLD_PREFIX_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `prefix:int64`; `ph:int64`; `phlen:num`;
    `ctx:int64`; `ctxlen:num`; `hashalg:int64`; `C:num`; `P:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 48 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLD_PREFIX65_EXEC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  MLD_PREFIX_VAL_LEN_TAC `prefix:int64` `332` `ctx:int64` `ctxlen:num` THEN
  MLD_PREFIX_VAL_LEN_TAC `prefix:int64` `332` `ph:int64` `phlen:num` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23`;;

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  MLD_PREFIX65_SETUP_TAC THEN
  ASM_CASES_TAC `255 < ctxlen` THENL
   [(*** The context is too long ***)

    MLD_PREFIX_SELECT_TAC THEN
    REWRITE_TAC[mld_domain_separation_prefix_length] THEN
    ASM_REWRITE_TAC[] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLD_PREFIX65_EXEC (1--2) THEN
    MLD_PREFIX_BRANCH_TAC THEN ARM_STEPS_TAC MLD_PREFIX65_EXEC (3--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `val(word_zx (hashalg:int64):int32) = 0` THENL
   [(*** Pure ML-DSA, with an empty context or not ***)

    ASM_CASES_TAC `ctxlen = 0` THEN MLD_PREFIX_SELECT_TAC THEN
    REWRITE_TAC[mld_domain_separation_prefix_length] THEN
    ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ctxlen = 0`))
      THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLD_PREFIX65_EXEC (1--2) THEN MLD_PREFIX_BRANCH_TAC THEN
      ARM_STEPS_TAC MLD_PREFIX65_EXEC (3--11) THEN MLD_PREFIX_BRANCH_TAC THEN
      ARM_STEPS_TAC MLD_PREFIX65_EXEC (12--14) THEN MLD_PREFIX_BRANCH_TAC THEN
      ARM_STEPS_TAC MLD_PREFIX65_EXEC (15--19) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ADD_CLAUSES; ARITH_EQ] THEN
      REWRITE_TAC[mld_domain_separation_prefix; LENGTH_BYTELIST_OF_NUM;
                  num_of_bytelist; bytelist_of_num; MLD_PREFIX_BYTES2] THEN
      ASM_REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      ENSURES_INIT_TAC "s0" THEN MLD_PREFIX_BOUND_TAC `ctx:int64` THEN
      ARM_STEPS_TAC MLD_PREFIX65_EXEC (1--2) THEN MLD_PREFIX_BRANCH_TAC THEN
      ARM_STEPS_TAC MLD_PREFIX65_EXEC (3--11) THEN MLD_PREFIX_BRANCH_TAC THEN
      ARM_STEPS_TAC MLD_PREFIX65_EXEC (12--14) THEN MLD_PREFIX_BRANCH_TAC THEN
      ARM_STEPS_TAC MLD_PREFIX65_EXEC (15--17) THEN
      LIBC_PLT_TAC MLD_PREFIX65_EXEC 17 THEN
      MLD_PREFIX65_MEMCPY_TAC `C:num` 22 THEN
      ARM_STEPS_TAC MLD_PREFIX65_EXEC (23--27) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [CONV_TAC WORD_RULE;
        MLD_PREFIX65_PURE_MEM_TAC;
        DISCHARGE_SAFETY_PROPERTY_TAC]];
    ALL_TAC] THEN
  ASM_CASES_TAC `12 < val(word_zx (hashalg:int64):int32)` THENL
   [(*** hashalg is not one of the MLD_PREHASH_* constants ***)

    MLD_PREFIX_SELECT_TAC THEN
    REWRITE_TAC[mld_domain_separation_prefix_length; mld_prehash_valid;
                GSYM NOT_LT] THEN
    ASM_REWRITE_TAC[] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLD_PREFIX65_EXEC (1--2) THEN
    MLD_PREFIX_BRANCH_TAC THEN ARM_STEPS_TAC MLD_PREFIX65_EXEC (3--11) THEN
    MLD_PREFIX_BRANCH_TAC THEN ARM_STEPS_TAC MLD_PREFIX65_EXEC (12--15) THEN
    MLD_PREFIX_RANGE_TAC THEN MLD_PREFIX_BRANCH_TAC THEN
    ARM_STEPS_TAC MLD_PREFIX65_EXEC (16--21) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN

  (*** HashML-DSA: to adrp1, then the jump ***)

  MLD_PREFIX_SELECT_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mldsa65_prepare_domain_separation_prefix_adrp1` MLD_PREFIX65_MID1 THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLD_PREFIX65_EXEC (1--2) THEN
    MLD_PREFIX_BRANCH_TAC THEN ARM_STEPS_TAC MLD_PREFIX65_EXEC (3--11) THEN
    MLD_PREFIX_BRANCH_TAC THEN ARM_STEPS_TAC MLD_PREFIX65_EXEC (12--15) THEN
    MLD_PREFIX_RANGE_TAC THEN MLD_PREFIX_BRANCH_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `mld_prehash_valid (val(word_zx (hashalg:int64):int32)) phlen`
  THENL
   [ALL_TAC;

    (*** The pre-hash does not have the length of the hash ***)

    MLD_PREFIX_SELECT_TAC THEN
    REWRITE_TAC[mld_domain_separation_prefix_length] THEN
    ASM_REWRITE_TAC[] THEN
    MLD_PREFIX_HCASES_TAC THENL map (MLD_PREFIX65_JUMP_TAC false) (1--12)] THEN

  (*** It does: to the code after the check, then the rest ***)

  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_PREFIX_PHLEN_LE) THEN
  MLD_PREFIX_SELECT_TAC THEN ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   MLD_PREFIX65_JOIN MLD_PREFIX65_MID2 THEN
  CONJ_TAC THENL
   [MLD_PREFIX_HCASES_TAC THENL map (MLD_PREFIX65_JUMP_TAC true) (1--12);
    ALL_TAC] THEN
  ASM_CASES_TAC `ctxlen = 0` THEN MLD_PREFIX_SELECT_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length] THEN ASM_REWRITE_TAC[] THENL
   [(*** An empty context ***)

    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ctxlen = 0`))
    THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `val(word_zx (hashalg:int64):int32)`
     MLD_PREFIX65_HEAD
     `pc + mldsa65_prepare_domain_separation_prefix_loop1_exit1`
     MLD_PREFIX65_INV0 THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      FULL_INIT_TAC THEN
      ARM_STEPS_TAC MLD_PREFIX65_EXEC (1--4) THEN MLD_PREFIX_BRANCH_TAC THEN
      ARM_STEPS_TAC MLD_PREFIX65_EXEC (5--5) THEN MLKEM_NATIVE_ADRP_TAC THEN
      ARM_STEPS_TAC MLD_PREFIX65_EXEC (6--8) THEN
      ENSURES_FINAL_STATE_TAC THEN
      REWRITE_TAC[MIN; LE_0; MULT_CLAUSES; ADD_CLAUSES] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CONJUNCT1 ENUMERATEL; CONJUNCT1 APPEND] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      MLD_PREFIX65_BODY_TAC;
      MLD_PREFIX65_EXIT_TAC MLD_PREFIX65_MEM0_TAC];

    (*** A context, copied by memcpy ***)

    ENSURES_EVENTS_WHILE_UP2_TAC `val(word_zx (hashalg:int64):int32)`
     MLD_PREFIX65_HEAD
     `pc + mldsa65_prepare_domain_separation_prefix_loop1_exit1`
     MLD_PREFIX65_INV1 THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      FULL_INIT_TAC THEN
      ARM_STEPS_TAC MLD_PREFIX65_EXEC (1--4) THEN MLD_PREFIX_BRANCH_TAC THEN
      ARM_STEPS_TAC MLD_PREFIX65_EXEC (5--7) THEN
      LIBC_PLT_TAC MLD_PREFIX65_EXEC 7 THEN
      MLD_PREFIX65_MEMCPY_TAC `C:num` 12 THEN
      ARM_STEPS_TAC MLD_PREFIX65_EXEC (13--13) THEN MLKEM_NATIVE_ADRP_TAC THEN
      ARM_STEPS_TAC MLD_PREFIX65_EXEC (14--16) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MLD_PREFIX_ZX_WORD]) THEN
      ENSURES_FINAL_STATE_TAC THEN
      REWRITE_TAC[MIN; LE_0; MULT_CLAUSES; ADD_CLAUSES] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CONJUNCT1 ENUMERATEL; CONJUNCT1 APPEND] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      MLD_PREFIX65_BODY_TAC;
      MLD_PREFIX65_EXIT_TAC MLD_PREFIX65_MEM1_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;
