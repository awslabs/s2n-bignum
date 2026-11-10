(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The domain separation prefix: the proof (see                              *)
(* prepare_domain_separation_prefix_87_spec.ml).                             *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/prepare_domain_separation_prefix_87_spec.ml";;
needs "x86/proofs/utils/mldsa_native_prefix.ml";;

let MLD_PREFIX87_EXEC =
  MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The two tables in the image, the address of oid_map, and the calls of     *)
(* memcpy through its PLT stub, whose events may depend on the variables of  *)
(* the template.                                                             *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX87_JUMP_TABLE =
  MLD_PREFIX_IMAGE_BYTES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   (layout "mldsa87_prepare_domain_separation_prefix_switch1_table") 52;;

let MLD_PREFIX87_OID_MAP =
  MLD_PREFIX_IMAGE_BYTES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   (layout "rodata_oid_map_0_3") 192;;

let MLD_PREFIX87_OID = mk_small_numeral(layout "rodata_oid_map_0_3");;

let MLD_PREFIX87_PLT_TAC k =
  LIBC_PLT_TAC MLD_PREFIX87_EXEC (layout "plt_memcpy") (layout "got_memcpy")
   k;;

let MLD_PREFIX87_MEMCPY_TAC x n =
  LIBC_FULL_CALL_TAC "H_MEMCPY" MLD_PREFIX87_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`; x;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   (ref [`prefix:int64`; `ph:int64`; `phlen:num`; `ctx:int64`;
         `ctxlen:num`; `hashalg:int64`; `mc:int64`; `pc:num`;
         `stackpointer:int64`; `returnaddress:int64`]) n;;

(* ------------------------------------------------------------------------- *)
(* The states at join3 (after the checks of ctxlen and of hashalg = 0) and   *)
(* at join6 (after the jump and the check of the length of the pre-hash),    *)
(* with the stack pointer offset by 64 (WORD_FORALL_OFFSET_TAC), so that the *)
(* frame of 56 bytes that the function pushes and reserves is at             *)
(* stackpointer + 8, with the four saved registers at stackpointer + 32,     *)
(* ..., + 56, and the return address at stackpointer + 64.                   *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX87_FRAME =
 `\s. read RSP s = word_add stackpointer (word 8) /\
      read (memory :> bytes64 (word_add stackpointer (word 32))) s =
      rbp_init /\
      read (memory :> bytes64 (word_add stackpointer (word 40))) s =
      r12_init /\
      read (memory :> bytes64 (word_add stackpointer (word 48))) s =
      r13_init /\
      read (memory :> bytes64 (word_add stackpointer (word 56))) s =
      r14_init /\
      read (memory :> bytes64 (word_add stackpointer (word 64))) s =
      returnaddress /\
      (read DF s <=> false) /\
      read (memory :> bytes64 (word(pc + got_memcpy))) s = mc /\
      read (memory :> bytes(ea,el)) s = ev /\
      read (memory :> bytes(ph,phlen)) s = P`;;

let MLD_PREFIX87_APP f x = rhs(concl(BETA_CONV(mk_comb(f,x))));;

let MLD_PREFIX87_STATE extra =
  let s = `s:x86state` in
  mk_abs(s,mk_conj(MLD_PREFIX87_APP extra s,
                   MLD_PREFIX87_APP MLD_PREFIX87_FRAME s));;

let MLD_PREFIX87_MID1 = MLD_PREFIX87_STATE
 `\s. read RDX s = word phlen /\ read RSI s = ph /\ read RCX s = ctx /\
      read R8 s = word ctxlen /\ read R9 s = (hashalg:int64) /\
      read RBP s = word ctxlen /\ read R12 s = prefix /\
      read (memory :> bytes(ctx,ctxlen)) s = C`;;

let MLD_PREFIX87_MID2 = MLD_PREFIX87_STATE
 `\s. read RCX s = ctx /\ read R9 s = (hashalg:int64) /\
      read RBP s = word ctxlen /\ read R12 s = prefix /\
      read R13 s = word phlen /\ read R14 s = ph /\
      read (memory :> bytes(ctx,ctxlen)) s = C`;;

(* ------------------------------------------------------------------------- *)
(* The invariant of the loop over oid_map, for i entries checked: EAX = i    *)
(* and RDX the address of entry i, except after the last iteration, which    *)
(* leaves them at the entry found (hashalg - 1, hence the MIN), with the     *)
(* address of oid_map in RCX and the first bytes of the prefix written. R9   *)
(* holds hashalg (if the context is empty) or its low 32 bits reloaded from  *)
(* the stack after the copy of the context.                                  *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX87_INV x9 extra =
  let i = `i:num` and s = `s:x86state` in
  let core = subst [MLD_PREFIX87_OID,`oid:num`; x9,`x9:int64`]
   `\(i:num) s.
       read RCX s = word(pc + oid) /\
       read RAX s = word(MIN i (val(word_zx (hashalg:int64):int32) - 1)) /\
       read RDX s = word_add (word(pc + oid))
                     (word(16 * MIN i (val(word_zx hashalg:int32) - 1))) /\
       read R9 s = x9 /\ read R12 s = prefix /\
       read R13 s = word phlen /\ read R14 s = ph /\
       read (memory :> bytes8 prefix) s = word 1` in
  list_mk_abs([i;s],
   list_mk_conj[MLD_PREFIX87_APP (MLD_PREFIX87_APP core i) s;
                MLD_PREFIX87_APP extra s;
                MLD_PREFIX87_APP MLD_PREFIX87_FRAME s]);;

let MLD_PREFIX87_INV0 = MLD_PREFIX87_INV `hashalg:int64`
 `\s. read RBP s = word 0 /\
      read (memory :> bytes8 (word_add prefix (word 1))) s = word 0`;;

let MLD_PREFIX87_INV1 =
  MLD_PREFIX87_INV `word_zx(word_zx (hashalg:int64):int32):int64`
 `\s. read RBP s = word ctxlen /\
      read (memory :> bytes8 (word_add prefix (word 1))) s =
      word(ctxlen MOD 256) /\
      read (memory :> bytes(word_add prefix (word 2),ctxlen)) s = C`;;

(* ------------------------------------------------------------------------- *)
(* The facts from the image: the hashalg fields of the entries of oid_map,   *)
(* for the loop, and the OID of entry j in two parts, its first 8 bytes (the *)
(* same for all) and its bytes 7 to 10, with the addresses as the code       *)
(* computes them.                                                            *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX87_ALGS_TAC =
  SUBGOAL_THEN (subst [MLD_PREFIX87_OID,`oid:num`]
    `!j. j < 12
         ==> read (memory :> bytes32
                    (word_add (word(pc + oid)) (word (16 * j)))) s0 =
             word(j + 1)`) ASSUME_TAC THENL
   [MAP_EVERY (fun j -> MLD_PREFIX_TABLE_TAC MLD_PREFIX87_OID_MAP (16 * j) 4)
     (0--11) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let MLD_PREFIX87_OID_TAC =
  SUBGOAL_THEN (subst [MLD_PREFIX87_OID,`oid:num`]
    `!j. j < 12
         ==> read (memory :> bytes64
                    (word_add (word(pc + oid)) (word (16 * j + 4)))) s0 =
             word 0x0365014886600906 /\
             read (memory :> bytes32
                    (word_add (word(pc + oid)) (word ((16 * j + 4) + 7)))) s0 =
             word (0x20403 + 0x1000000 *
                             val(EL 10 (mld_prehash_oid (j + 1))))`)
  ASSUME_TAC THENL
   [MAP_EVERY (fun j ->
      MLD_PREFIX_TABLE_TAC MLD_PREFIX87_OID_MAP (16 * j + 4) 8 THEN
      MLD_PREFIX_TABLE_TAC MLD_PREFIX87_OID_MAP (16 * j + 11) 4) (0--11) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[mld_prehash_oid] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* From join3 to join6 or to the return of 0, for hashalg = k: the check of  *)
(* the range of hashalg, which holds, and the jump through the table, to the *)
(* address of the table plus the signed offset at 4 * k in it, the check of  *)
(* the length of the pre-hash for k, which takes 2 instructions to join6 if  *)
(* it holds and 10 to the return if not.                                     *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX87_JUMP_TAC valid k =
  let hk = mk_eq(`val(word_zx (hashalg:int64):int32)`,mk_small_numeral k) in
  let n = if valid then 11 else 19 in
  REWRITE_TAC[ASSUME hk; ARITH_EQ] THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (1--2) THEN MLD_PREFIX_BRANCH_TAC THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (3--6) THEN MLD_PREFIX_HWORD_TAC k THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV MLD_PREFIX_RIPREL_CONV)) THEN
  MLD_PREFIX_TABLE_TAC MLD_PREFIX87_JUMP_TABLE (4 * k) 4 THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (7--8) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV MLD_PREFIX_PC_CONV)) THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (9--11) THEN MLD_PREFIX_BRANCH_TAC THEN
  (if n > 11 then X86_STEPS_TAC MLD_PREFIX87_EXEC (12--n) else ALL_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* An iteration of the loop: the entry i, i < hashalg, is i + 1, and either  *)
(* i + 1 < hashalg and the loop continues, or it is hashalg and the loop     *)
(* exits to loop1_exit2.                                                     *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX87_BODY_TAC =
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
  SUBGOAL_THEN `val(word(i + 1):int32) = i + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FULL_INIT_TAC THEN MLD_PREFIX87_ALGS_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (1--2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_PREFIX_ZX_ZX]) THEN
  ASM_CASES_TAC `i + 1 < val(word_zx (hashalg:int64):int32)` THEN
  MLD_PREFIX_BRANCH_TAC THENL
   [X86_STEPS_TAC MLD_PREFIX87_EXEC (3--6) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [MP (SPEC `i:num` MLD_PREFIX_ZX_ADD1) (ASSUME `i + 1 < 2 EXP 32`);
      MLD_PREFIX_ZX_WORD]) THEN
    MLD_PREFIX_BRANCH_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; PATH_DISCHARGE_TAC];
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    PATH_DISCHARGE_TAC];;

(* ------------------------------------------------------------------------- *)
(* After the loop: the copy of the OID of entry hashalg - 1 with an 8-byte   *)
(* load and store and a 4-byte one at offset 7 (the low 7 bytes of the first *)
(* store kept before the second), the copy of the pre-hash with memcpy and   *)
(* the return of 2 + ctxlen + 11 + phlen; memtac proves the prefix from the  *)
(* pieces in memory.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX87_EXIT_TAC memtac =
  SUBGOAL_THEN
   `MIN (val(word_zx (hashalg:int64):int32))
        (val(word_zx (hashalg:int64):int32) - 1) =
    val(word_zx (hashalg:int64):int32) - 1`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[MIN] THEN MEMSAFE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_zx (hashalg:int64):int32) - 1 < 12` ASSUME_TAC THENL
   [MEMSAFE_ARITH_TAC; ALL_TAC] THEN
  FULL_INIT_TAC THEN MLD_PREFIX87_OID_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `val(word_zx (hashalg:int64):int32) - 1`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (1--3) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `val(word_zx (hashalg:int64):int32) - 1` MLD_PREFIX_OID_OFFSET)
       (ASSUME `val(word_zx (hashalg:int64):int32) - 1 < 12`)]) THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (4--5) THEN
  MLD_PREFIX_LOW7_TAC `prefix:int64` THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (6--12) THEN
  MLD_PREFIX87_PLT_TAC 12 THEN
  MLD_PREFIX87_MEMCPY_TAC `P:num` 14 THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (15--21) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    memtac;
    MLD_PREFIX_DISCHARGE_TAC
     (ABBREV_TAC `j = val(word_zx (hashalg:int64):int32) - 1`)];;

(*** The common part of the two proofs of the prefix in memory ***)

let MLD_PREFIX87_PREHASH_TAC =
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

let MLD_PREFIX87_MEM0_TAC =
  MLD_PREFIX_BOUND_TAC `word_add (prefix:int64) (word 13)` THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[mld_domain_separation_prefix] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[bytelist_of_num; APPEND; LENGTH] THEN
  REWRITE_TAC[num_of_bytelist; MLD_PREFIX_NUM_OF_BYTELIST_APPEND;
              LENGTH_BYTELIST_OF_NUM; LENGTH_MLD_PREHASH_OID;
              MLD_PREFIX_OIDN] THEN
  REWRITE_TAC[MLD_PREFIX_HASH_SPLIT0; MLD_PREFIX_BYTES2] THEN
  MLD_PREFIX87_PREHASH_TAC;;

let MLD_PREFIX87_MEM1_TAC =
  MLD_PREFIX_BOUND_TAC `word_add (prefix:int64) (word 2)` THEN
  MLD_PREFIX_BOUND_TAC `word_add (prefix:int64) (word (1 * ctxlen + 13))` THEN
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
  MLD_PREFIX87_PREHASH_TAC;;

(* ------------------------------------------------------------------------- *)
(* The prefix for pure ML-DSA in memory.                                     *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX87_PURE_MEM_TAC =
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

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[memcpy_full_contract] THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMCPY") THEN
  CONCRETIZE_F_EVENTS_TAC MLD_PREFIX_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `prefix:int64`; `ph:int64`; `phlen:num`;
    `ctx:int64`; `ctxlen:num`; `hashalg:int64`; `C:num`; `P:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 64 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLD_PREFIX87_EXEC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MLD_PREFIX_VAL_LEN_TAC `prefix:int64` `332` `ctx:int64` `ctxlen:num` THEN
  MLD_PREFIX_VAL_LEN_TAC `prefix:int64` `332` `ph:int64` `phlen:num` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ASM_CASES_TAC `255 < ctxlen` THENL
   [(*** The context is too long ***)

    MLD_PREFIX_SELECT_TAC THEN
    REWRITE_TAC[mld_domain_separation_prefix_length] THEN
    ASM_REWRITE_TAC[] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLD_PREFIX87_EXEC (1--3) THEN
    MLD_PREFIX_BRANCH_TAC THEN X86_STEPS_TAC MLD_PREFIX87_EXEC (4--4) THEN
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
      X86_STEPS_TAC MLD_PREFIX87_EXEC (1--3) THEN MLD_PREFIX_BRANCH_TAC THEN
      X86_STEPS_TAC MLD_PREFIX87_EXEC (4--12) THEN MLD_PREFIX_BRANCH_TAC THEN
      X86_STEPS_TAC MLD_PREFIX87_EXEC (13--16) THEN MLD_PREFIX_BRANCH_TAC THEN
      X86_STEPS_TAC MLD_PREFIX87_EXEC (17--23) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ADD_CLAUSES; ARITH_EQ] THEN
      REWRITE_TAC[mld_domain_separation_prefix; LENGTH_BYTELIST_OF_NUM;
                  num_of_bytelist; bytelist_of_num; MLD_PREFIX_BYTES2] THEN
      ASM_REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      ENSURES_INIT_TAC "s0" THEN MLD_PREFIX_BOUND_TAC `ctx:int64` THEN
      X86_STEPS_TAC MLD_PREFIX87_EXEC (1--3) THEN MLD_PREFIX_BRANCH_TAC THEN
      X86_STEPS_TAC MLD_PREFIX87_EXEC (4--16) THEN MLD_PREFIX_BRANCH_TAC THEN
      X86_STEPS_TAC MLD_PREFIX87_EXEC (17--20) THEN
      MLD_PREFIX87_PLT_TAC 20 THEN
      MLD_PREFIX87_MEMCPY_TAC `C:num` 22 THEN
      X86_STEPS_TAC MLD_PREFIX87_EXEC (23--30) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [CONV_TAC WORD_RULE;
        MLD_PREFIX87_PURE_MEM_TAC;
        DISCHARGE_SAFETY_PROPERTY_TAC]];
    ALL_TAC] THEN
  ASM_CASES_TAC `12 < val(word_zx (hashalg:int64):int32)` THENL
   [(*** hashalg is not one of the MLD_PREHASH_* constants ***)

    MLD_PREFIX_SELECT_TAC THEN
    REWRITE_TAC[mld_domain_separation_prefix_length; mld_prehash_valid;
                GSYM NOT_LT] THEN
    ASM_REWRITE_TAC[] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLD_PREFIX87_EXEC (1--3) THEN
    MLD_PREFIX_BRANCH_TAC THEN X86_STEPS_TAC MLD_PREFIX87_EXEC (4--12) THEN
    MLD_PREFIX_BRANCH_TAC THEN X86_STEPS_TAC MLD_PREFIX87_EXEC (13--14) THEN
    MLD_PREFIX_BRANCH_TAC THEN X86_STEPS_TAC MLD_PREFIX87_EXEC (15--22) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN

  (*** HashML-DSA: to join3, then the jump ***)

  MLD_PREFIX_SELECT_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mldsa87_prepare_domain_separation_prefix_join3` MLD_PREFIX87_MID1 THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLD_PREFIX87_EXEC (1--3) THEN
    MLD_PREFIX_BRANCH_TAC THEN X86_STEPS_TAC MLD_PREFIX87_EXEC (4--12) THEN
    MLD_PREFIX_BRANCH_TAC THEN
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
    MLD_PREFIX_HCASES_TAC THENL map (MLD_PREFIX87_JUMP_TAC false) (1--12)] THEN

  (*** It does: to join6, then the rest ***)

  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_PREFIX_PHLEN_LE) THEN
  MLD_PREFIX_SELECT_TAC THEN ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mldsa87_prepare_domain_separation_prefix_join6` MLD_PREFIX87_MID2 THEN
  CONJ_TAC THENL
   [MLD_PREFIX_HCASES_TAC THENL map (MLD_PREFIX87_JUMP_TAC true) (1--12);
    ALL_TAC] THEN
  ASM_CASES_TAC `ctxlen = 0` THEN MLD_PREFIX_SELECT_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length] THEN ASM_REWRITE_TAC[] THENL
   [(*** An empty context ***)

    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ctxlen = 0`))
    THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `val(word_zx (hashalg:int64):int32)`
     `pc + mldsa87_prepare_domain_separation_prefix_loop1`
     `pc + mldsa87_prepare_domain_separation_prefix_loop1_exit2`
     MLD_PREFIX87_INV0 THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      FULL_INIT_TAC THEN
      X86_STEPS_TAC MLD_PREFIX87_EXEC (1--4) THEN MLD_PREFIX_BRANCH_TAC THEN
      X86_STEPS_TAC MLD_PREFIX87_EXEC (5--8) THEN
      RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV MLD_PREFIX_RIPREL_CONV)) THEN
      ENSURES_FINAL_STATE_TAC THEN
      REWRITE_TAC[MIN; LE_0; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CONJUNCT1 ENUMERATEL; CONJUNCT1 APPEND] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      MLD_PREFIX87_BODY_TAC;
      MLD_PREFIX87_EXIT_TAC MLD_PREFIX87_MEM0_TAC];

    (*** A context, copied by memcpy ***)

    ENSURES_EVENTS_WHILE_UP2_TAC `val(word_zx (hashalg:int64):int32)`
     `pc + mldsa87_prepare_domain_separation_prefix_loop1`
     `pc + mldsa87_prepare_domain_separation_prefix_loop1_exit2`
     MLD_PREFIX87_INV1 THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      FULL_INIT_TAC THEN
      X86_STEPS_TAC MLD_PREFIX87_EXEC (1--4) THEN MLD_PREFIX_BRANCH_TAC THEN
      X86_STEPS_TAC MLD_PREFIX87_EXEC (5--9) THEN
      MLD_PREFIX87_PLT_TAC 9 THEN
      MLD_PREFIX87_MEMCPY_TAC `C:num` 11 THEN
      X86_STEPS_TAC MLD_PREFIX87_EXEC (12--17) THEN
      RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV MLD_PREFIX_RIPREL_CONV)) THEN
      ENSURES_FINAL_STATE_TAC THEN
      REWRITE_TAC[MIN; LE_0; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CONJUNCT1 ENUMERATEL; CONJUNCT1 APPEND] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      MLD_PREFIX87_BODY_TAC;
      MLD_PREFIX87_EXIT_TAC MLD_PREFIX87_MEM1_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
