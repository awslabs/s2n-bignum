(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tools for the proofs of mldsa44_poly_challenge,                *)
(* mldsa65_poly_challenge and mldsa87_poly_challenge (see                    *)
(* common/mldsa_native_challenge.ml) for x86-64, as for AArch64 (see         *)
(* arm/proofs/utils/mldsa_native_challenge.ml, whose lemmas and tactics      *)
(* these are, for the x86 model).                                            *)
(*                                                                           *)
(* The code reads the bytes of the SHAKE256 output one by one from a buffer  *)
(* of one block, squeezing the next block when the buffer is used up. The    *)
(* proofs treat this as one loop over the bytes from position 8 on, whose    *)
(* head is the read of the next byte from the buffer, or the squeeze of the  *)
(* next block if the byte starts one: the loop head depends on the           *)
(* iteration, as in MLD_CHALLENGE_WHILE_THM, a form of the theorem behind    *)
(* ENSURES_WHILE_UP2_TAC with the PC of the head a function of the           *)
(* iteration, and MLD_CHALLENGE_WHILE_TAC is the corresponding form of       *)
(* ENSURES_EVENTS_WHILE_UP2_TAC.                                             *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_hash.ml";;
needs "x86/proofs/utils/mldsa_native_prefix.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;
needs "common/mldsa_native_challenge.ml";;
needs "common/fips204/properties/mldsa_native_challenge.ml";;

(* ------------------------------------------------------------------------- *)
(* A loop of k iterations whose iteration i starts at pcf i, the last one    *)
(* ending at pc2.                                                            *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_WHILE_THM = prove
 (`!k (pcf:num->num) pc2 (loopinv:num->A->bool) C precond postcond
    (pcounter:(A,(N)word)component).
     C ,, C = C /\ ~(k = 0) /\
     ensures step
      (\s. program_decodes s /\ read pcounter s = word pc /\ precond s)
      (\s. program_decodes s /\ read pcounter s = word(pcf 0) /\
           loopinv 0 s)
      C /\
     (!i. i < k
          ==> ensures step
               (\s. program_decodes s /\ read pcounter s = word(pcf i) /\
                    loopinv i s)
               (\s. program_decodes s /\
                    read pcounter s =
                    word(if i + 1 < k then pcf(i + 1) else pc2) /\
                    loopinv (i + 1) s)
               C) /\
     ensures step
      (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinv k s)
      postcond C
     ==> ensures step
          (\s. program_decodes s /\ read pcounter s = word pc /\ precond s)
          postcond C`,
  REPEAT GEN_TAC THEN INTRO_TAC "HC HK HPRE HLOOP HPOST" THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
  EXISTS_TAC `\s:A. program_decodes s /\
                    read (pcounter:(A,(N)word)component) s = word pc2 /\
                    loopinv (k:num) s` THEN
  CONJ_TAC THENL [ALL_TAC; USE_THEN "HPOST" ACCEPT_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
  EXISTS_TAC `\s:A. program_decodes s /\
                    read (pcounter:(A,(N)word)component) s =
                    word(pcf(k - 1)) /\
                    loopinv (k - 1) s` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    USE_THEN "HLOOP" (MP_TAC o SPEC `k - 1`) THEN
    ANTS_TAC THENL [USE_THEN "HK" MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `k - 1 + 1 = k` SUBST1_TAC THENL
     [USE_THEN "HK" MP_TAC THEN ARITH_TAC; REWRITE_TAC[LT_REFL]]] THEN
  SUBGOAL_THEN `k - 1 < k` MP_TAC THENL
   [USE_THEN "HK" MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`k - 1`,`j:num`) THEN INDUCT_TAC THENL
   [DISCH_TAC THEN USE_THEN "HPRE" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `SUC j < k` THEN ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
  EXISTS_TAC `\s:A. program_decodes s /\
                    read (pcounter:(A,(N)word)component) s = word(pcf j) /\
                    loopinv (j:num) s` THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "HLOOP" (MP_TAC o SPEC `j:num`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `SUC j < k` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM ADD1]);;

(* ------------------------------------------------------------------------- *)
(* MLD_CHALLENGE_WHILE_TAC k pcf pc2 inv applies MLD_CHALLENGE_WHILE_THM to  *)
(* a goal whose postcondition has the events                                 *)
(* e2 = APPEND (ENUMERATEL k body) front, with the invariant inv i s and the *)
(* events e2 = APPEND (ENUMERATEL i body) front so far, as                   *)
(* ENSURES_EVENTS_WHILE_UP2_TAC does, leaving the subgoals for ~(k = 0), the *)
(* start, the iterations and the end of the loop.                            *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_WHILE_TAC k pcf pc2 inv (asl,w) =
  let post = rand(rator w) in
  let ex = find_term (fun t -> is_exists t &&
             let v = fst(dest_exists t) in
             name_of v = "e2" && is_uarch_event_list_ty(type_of v)) post in
  let v,bod = dest_exists ex in
  let c1,eq,c3 = match conjuncts bod with
                   [c1;eq;c3] -> c1,eq,c3
                 | _ -> failwith "MLD_CHALLENGE_WHILE_TAC" in
  let enum,front = dest_binary "APPEND" (rhs eq) in
  let enumc,nb = strip_comb enum in
  let body = match nb with
               [n;b] when n = k -> b
             | _ -> failwith "MLD_CHALLENGE_WHILE_TAC: counter" in
  let iv,sv = match fst(strip_abs inv) with
                [iv;sv] -> iv,sv
              | _ -> failwith "MLD_CHALLENGE_WHILE_TAC: invariant" in
  let enum' = list_mk_comb(enumc,[iv;body]) in
  let ex' = mk_exists(v,list_mk_conj
             [c1; mk_eq(v,list_mk_icomb "APPEND" [enum'; front]); c3]) in
  let inv' = list_mk_abs([iv;sv],mk_conj(snd(strip_abs inv),ex')) in
  (MATCH_MP_TAC MLD_CHALLENGE_WHILE_THM THEN
   MAP_EVERY EXISTS_TAC [k; pcf; pc2; inv'] THEN BETA_TAC THEN
   CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* The bytes of a buffer holding a list given as a function.                 *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_READ_BYTE = prove
 (`!a n (f:num->byte) t (s:x86state).
     read (memory :> bytes(a,n)) s = num_of_bytelist(list_of_seq f n) /\
     t < n
     ==> read (memory :> bytes8(word_add a (word t))) s = f t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `n:num`; `t:num`; `1`;
                `num_of_bytelist(list_of_seq (f:num->byte) n)`;
                `s:x86state`] MLD_PREFIX_BYTES_SUB) THEN
  ASM_REWRITE_TAC[READ_MEMORY_BYTES_BYTES8] THEN
  ANTS_TAC THENL [UNDISCH_TAC `t < n` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(RAND_CONV NUM_REDUCE_CONV)) THEN
  ASM_SIMP_TAC[MLD_CHALLENGE_BYTELIST_DIGIT; VAL_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The sign bits as the code computes them, from the first 8 bytes f 0, ..., *)
(* f 7 of the buffer, each zero-extended and shifted left by 8 times its     *)
(* index (SHL by CL) and ORed into the 64-bit register.                      *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_SIGNS_WORD = prove
 (`!f:num->byte.
     ((((((word_shl (word_zx (word_zx (f 0):int32)) 0 ||
           word_shl (word_zx (word_zx (f 1):int32)) 8) ||
          word_shl (word_zx (word_zx (f 2):int32)) 16) ||
         word_shl (word_zx (word_zx (f 3):int32)) 24) ||
        word_shl (word_zx (word_zx (f 4):int32)) 32) ||
       word_shl (word_zx (word_zx (f 5):int32)) 40) ||
      word_shl (word_zx (word_zx (f 6):int32)) 48) ||
     word_shl (word_zx (word_zx (f 7):int32)) 56:int64 =
     mld_poly_challenge_signs f`,
  GEN_TAC THEN REWRITE_TAC[mld_poly_challenge_signs] THEN
  ABBREV_TAC
   `X:int64 = word(num_of_bytelist(list_of_seq (f:num->byte) 8))` THEN
  SUBGOAL_THEN
   `!t. t < 8 ==> (f:num->byte) t = word_subword (X:int64) (8 * t,8)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "X" THEN
    REWRITE_TAC[word_subword; GSYM VAL_EQ; VAL_WORD; DIMINDEX_8;
                DIMINDEX_64] THEN
    MP_TAC(ISPEC `list_of_seq (f:num->byte) 8` NUM_OF_BYTELIST_BOUND) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[MOD_LT] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[MLD_CHALLENGE_BYTELIST_DIGIT; MOD_MOD_REFL] THEN
    MP_TAC(ISPEC `(f:num->byte) t` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN BITBLAST_TAC);;

(*** The address of byte p of the buffer as the load from RSP + RAX + 32 ***)
(*** computes it, with RSP = a + 328 and the buffer at a + 360          ***)

let MLD_CHALLENGE_BUF_ADDR = prove
 (`!(a:int64) p. word_add a (word (360 + p)) =
                 word_add a (word (328 + 1 * p + 32))`,
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Values of words: the comparisons of the byte j (or the position) with i   *)
(* in 32-bit registers as CMP leaves them for JAE, JB and JNE, in either     *)
(* order, and the zero extensions of small values; the new position that the *)
(* 32-bit LEA computes, and the sign 1 - 2 * bit 0 of the remaining sign     *)
(* bits y as the code computes it with AND, ADD and SUB.                     *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_CMP_VAL2 = prove
 (`!x y:int32 m.
     val x = m
     ==> (&m - &(val y):int = &(val(word_sub x y)) <=> val y <= m)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MLD_CHALLENGE_CMP]);;

let MLD_CHALLENGE_LEA_ADD1 = prove
 (`!p. p + 1 < 2 EXP 32
       ==> word_zx(word_sx(word_add (word p) (word 1):int64):int32):int64 =
           word(p + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!y:int64. word_sx y:int32 = word_zx y`
   (fun th -> REWRITE_TAC[th]) THENL [BITBLAST_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `x < 4294967296 ==> x < 18446744073709551616`]);;

let MLD_CHALLENGE_SIGN_WORD = prove
 (`!y:int64.
     word_zx(word_zx(word_sub (word 1)
      (word_zx(word_add (word_zx(word_and (word_zx y) (word 1):int32):int64)
                        (word_zx(word_and (word_zx y) (word 1):int32))))
       :int32):int64):int32 =
     if bit 0 y then word_neg(word 1) else word 1`,
  GEN_TAC THEN BITBLAST_TAC);;

(*** The coefficients after memset, as 32-bit words ***)

let MLD_CHALLENGE_ZERO_POLY = prove
 (`!a (s:x86state).
     read (memory :> bytes(a,1024)) s = 0
     ==> !t. t < 256
             ==> read (memory :> bytes32(word_add a (word(4 * t)))) s =
                 word 0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[BYTES32_WBYTES; MLD_PREFIX_WBYTES_BYTES; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`a:int64`; `1024`; `4 * t`; `4`; `0`; `s:x86state`]
    MLD_PREFIX_BYTES_SUB) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `t < 256` THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_0; MOD_0]);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the simulation. MLD_CHALLENGE_BYTES_TAC buf ts adds the bytes *)
(* t in ts of the buffer at buf, from its value                              *)
(* num_of_bytelist(list_of_seq f 136), as f t, and MLD_CHALLENGE_LOAD_TAC    *)
(* buf t ths does so for one byte, the bound t < 136 following from the      *)
(* assumptions, rewriting f t with ths; the addresses are normalized as the  *)
(* simulation does.                                                          *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_BYTES_TAC buf ts =
  let pat = vsubst [buf,`a:int64`]
    `read (memory :> bytes(a,136)) s =
     num_of_bytelist(list_of_seq (f:num->byte) 136)` in
  FIRST_ASSUM(fun th ->
    if can (term_match [] pat) (concl th)
    then MAP_EVERY (fun t ->
           let th' = MP (SPEC t (MATCH_MP
              (REWRITE_RULE[IMP_CONJ] MLD_CHALLENGE_READ_BYTE) th))
                       (EQT_ELIM(NUM_REDUCE_CONV
                         (mk_binop `(<):num->num->bool` t `136`))) in
           ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV
                        NORMALIZE_RELATIVE_ADDRESS_CONV) th')) ts
    else NO_TAC);;

let MLD_CHALLENGE_LOAD_TAC buf idx ths =
  let pat = vsubst [buf,`a:int64`]
    `read (memory :> bytes(a,136)) s =
     num_of_bytelist(list_of_seq (f:num->byte) 136)` in
  FIRST_ASSUM(fun th ->
    if can (term_match [] pat) (concl th) then
      let lth = SPEC idx (MATCH_MP
                  (REWRITE_RULE[IMP_CONJ] MLD_CHALLENGE_READ_BYTE) th) in
      MP_TAC lth THEN ANTS_TAC THENL
       [SIMPLE_ARITH_TAC;
        DISCH_THEN(ASSUME_TAC o
          CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) o
          REWRITE_RULE ths o BETA_RULE)]
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* MLD_CHALLENGE_BRANCH_TAC decides the condition c of the RIP after a       *)
(* conditional jump, read RIP s = if c then a else b, from the assumptions:  *)
(* the comparisons become inequalities and equations of the values of the    *)
(* words (MLD_CHALLENGE_DECIDE_TAC; first as an equation of two addresses in *)
(* the buffer, for the loop over the sign bits), and it rewrites the         *)
(* assumptions (the RIP and the events) with it, keeping the RIP as an       *)
(* assumption of its own, without the condition as a hypothesis (whose       *)
(* variables the simulation could not instantiate, such as n); it does       *)
(* nothing if the simulation has decided the jump.                           *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_DECIDE_TAC =
  (REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; WORD_ADD_LCANCEL_EQ] THEN
   CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) ORELSE
  (ASM_SIMP_TAC[MLD_CHALLENGE_CMP_VAL; MLD_CHALLENGE_CMP_VAL2] THEN
   REWRITE_TAC[MLD_CHALLENGE_CMP; MLD_CHALLENGE_VAL_ZX3; VAL_WORD_SUB_EQ_0] THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
   SIMPLE_ARITH_TAC);;

let MLD_CHALLENGE_BRANCH_TAC =
  let is_rip_cond th =
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),_)),r)
        -> is_cond r
    | _ -> false
  and is_rip th =
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),_)),_)
        -> true
    | _ -> false in
  W(fun (asl,w) ->
    if not(exists (fun (_,th) -> is_rip_cond th) asl) then ALL_TAC else
    FIRST_X_ASSUM(fun th ->
      if not(is_rip_cond th) then NO_TAC else
      let c = rand(rator(rator(rand(concl th)))) in
      let use cth =
        ASSUME_TAC th THEN RULE_ASSUM_TAC(REWRITE_RULE[cth]) THEN
        FIRST_X_ASSUM(fun rth ->
          if is_rip rth then MP_TAC rth THEN DISCH_TAC else NO_TAC) in
      (SUBGOAL_THEN c use THENL [MLD_CHALLENGE_DECIDE_TAC; ALL_TAC]) ORELSE
      (SUBGOAL_THEN (mk_neg c) (use o EQF_INTRO) THENL
        [MLD_CHALLENGE_DECIDE_TAC; ALL_TAC])));;

(* ------------------------------------------------------------------------- *)
(* Rewriting some assumptions only: MLD_CHALLENGE_FIX_TAC p ths rewrites     *)
(* those whose conclusion satisfies p with ths, for example the value of one *)
(* register (mld_challenge_is_read_reg) or the 32-bit values in memory       *)
(* (mld_challenge_is_bytes32), and MLD_CHALLENGE_ZX_ZX_TAC t replaces the    *)
(* zero extensions of word t to 32 and back to 64 bits by word t, for a      *)
(* small t, in the assumptions.                                              *)
(* ------------------------------------------------------------------------- *)

let mld_challenge_is_read_reg r tm =
  is_eq tm && (try rand(rator(lhs tm)) = r with Failure _ -> false) &&
  (try fst(dest_const(rator(rator(lhs tm)))) = "read"
   with Failure _ -> false);;

let mld_challenge_is_bytes32 tm =
  is_eq tm && can (term_match [] `read (memory :> bytes32 a) s`) (lhs tm);;

(* ------------------------------------------------------------------------- *)
(* The end of an iteration of the loop over the bytes. The proof abbreviates *)
(* the values that depend on n (whose definitions mention val, which         *)
(* SIMPLE_ARITH_TAC ignores), and MLD_CHALLENGE_UNABBREV_TAC prs puts back   *)
(* the abbreviations v = t in prs that are there before the events are       *)
(* matched with the template. MLD_CHALLENGE_DISCHARGE_TAC tac then selects   *)
(* the path of the template by the case assumptions, as PATH_DISCHARGE_TAC   *)
(* does, with the safety property of the events so far split out of the one  *)
(* for e2 (which must stay free, see MLD_PREFIX_DISCHARGE_TAC), instantiates *)
(* the function of the path or checks the events against it if another case  *)
(* has instantiated it, and proves that the accesses are in bounds, after    *)
(* tac.                                                                      *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_DISCHARGE_TAC tac =
  let beta_all =
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) in
  let is_e2_def th = let c = concl th in
    is_eq c && is_var(lhs c) && name_of(lhs c) = "e2" in
  let is_e2_meminb th = let c = concl th in is_comb c &&
    (match strip_comb c with
       Const("memaccess_inbounds",_),(e::_) -> is_var e && name_of e = "e2"
     | _ -> false) in
  REWRITE_TAC[ENUMERATEL_ADD1] THEN beta_all THEN MLD_PREFIX_SELECT_TAC THEN
  TRY(FIRST_ASSUM(fun dth -> if is_e2_def dth then
        FIRST_ASSUM(fun mth -> if is_e2_meminb mth then
          STRIP_ASSUME_TAC(REWRITE_RULE[MEMACCESS_INBOUNDS_APPEND]
                            (REWRITE_RULE[dth] mth))
        else NO_TAC) else NO_TAC)) THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [FULL_UNIFY_F_EVENTS_TAC ORELSE
    (CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC] THEN NO_TAC);
    ALL_TAC] THEN
  beta_all THEN REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN tac THEN
  REPEAT CONJ_TAC THEN DISCHARGE_MEMACCESS_INBOUNDS_TAC;;
