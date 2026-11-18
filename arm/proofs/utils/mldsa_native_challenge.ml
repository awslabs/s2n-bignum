(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tools for the proofs of mldsa44_poly_challenge,                *)
(* mldsa65_poly_challenge and mldsa87_poly_challenge (see                    *)
(* common/mldsa_native_challenge.ml).                                        *)
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

(* The part that depends on AArch64; the rest is in                          *)
(* common/fips204/properties/mldsa_native_challenge.ml.                      *)

needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_hash.ml";;
needs "arm/proofs/utils/mldsa_native_prefix.ml";;
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

let MLD_CHALLENGE_READ_BYTE = prove
 (`!a n (f:num->byte) t (s:armstate).
     read (memory :> bytes(a,n)) s = num_of_bytelist(list_of_seq f n) /\
     t < n
     ==> read (memory :> bytes8(word_add a (word t))) s = f t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `n:num`; `t:num`; `1`;
                `num_of_bytelist(list_of_seq (f:num->byte) n)`;
                `s:armstate`] MLD_PREFIX_BYTES_SUB) THEN
  ASM_REWRITE_TAC[READ_MEMORY_BYTES_BYTES8] THEN
  ANTS_TAC THENL [UNDISCH_TAC `t < n` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(RAND_CONV NUM_REDUCE_CONV)) THEN
  ASM_SIMP_TAC[MLD_CHALLENGE_BYTELIST_DIGIT; VAL_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The sign bits as the code computes them, from the first 8 bytes f 0, ..., *)
(* f 7 of the buffer with shifts by the 64-bit register X0, and the          *)
(* coefficient 1 - 2 * bit 0 of the remaining sign bits y as a 32-bit word.  *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_SIGNS_WORD = prove
 (`!f:num->byte.
     ((((((word_jshl (word_zx (word_zx (f 0):int32)) (word 0) ||
           word_jshl (word_zx (word_zx (f 1):int32)) (word 8)) ||
          word_jshl (word_zx (word_zx (f 2):int32)) (word 16)) ||
         word_jshl (word_zx (word_zx (f 3):int32)) (word 24)) ||
        word_jshl (word_zx (word_zx (f 4):int32)) (word 32)) ||
       word_jshl (word_zx (word_zx (f 5):int32)) (word 40)) ||
      word_jshl (word_zx (word_zx (f 6):int32)) (word 48)) ||
     word_jshl (word_zx (word_zx (f 7):int32)) (word 56):int64 =
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
  STRIP_TAC THEN ASM_REWRITE_TAC[word_jshl; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN BITBLAST_TAC);;

let MLD_CHALLENGE_SIGN_WORD = prove
 (`!y:int64.
     word_zx(word_zx(word_sub (word 1)
       (word_zx(word_shl (word_subword y (0,1):int64) 1):int32)):int64):int32 =
     if bit 0 y then word_neg(word 1) else word 1`,
  GEN_TAC THEN BITBLAST_TAC);;

(*** The coefficients after memset, as 32-bit words ***)

let MLD_CHALLENGE_ZERO_POLY = prove
 (`!a (s:armstate).
     read (memory :> bytes(a,1024)) s = 0
     ==> !t. t < 256
             ==> read (memory :> bytes32(word_add a (word(4 * t)))) s =
                 word 0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[BYTES32_WBYTES; MLD_PREFIX_WBYTES_BYTES; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`a:int64`; `1024`; `4 * t`; `4`; `0`; `s:armstate`]
    MLD_PREFIX_BYTES_SUB) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `t < 256` THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_0; MOD_0]);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the simulation. MLD_CHALLENGE_GOT_TAC ns adds the facts about *)
(* the GOT entries at pc + n for n in ns in the form of the preconditions of *)
(* the callees. MLD_CHALLENGE_BYTES_TAC buf ts adds the bytes t in ts of the *)
(* buffer at buf, from its value num_of_bytelist(list_of_seq f 136), as      *)
(* f t, and MLD_CHALLENGE_LOAD_TAC buf t ths does so for one byte, the bound *)
(* t < 136 following from the assumptions, rewriting f t with ths; the       *)
(* addresses are normalized as the simulation does. MLD_CHALLENGE_UXTW_TAC t *)
(* adds the values of the zero extensions that the address of a load with a  *)
(* UXTW register offset t needs.                                             *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_GOT_TAC ns =
  MAP_EVERY (fun n ->
    FIRST_ASSUM(fun th ->
      if can (term_match []
               (vsubst [n,`n:num`]
                 `read (memory :> bytes64
                         (word_add (word (pc:num)) (word n):int64)) s =
                  (g:int64)`)) (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC)) ns;;

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
(* MLD_CHALLENGE_BRANCH_TAC decides the condition c of the PC after a        *)
(* conditional branch, read PC s = if c then a else b, from the assumptions: *)
(* the comparisons become inequalities and equations of the values of the    *)
(* words (MLD_CHALLENGE_DECIDE_TAC), and it rewrites the assumptions (the PC *)
(* and the events) with it; it does nothing if the simulation has decided    *)
(* the branch. MLD_CHALLENGE_EXIT_TEST_TAC first puts the test of the 64-bit *)
(* counter against its bound as an equation of numbers, as LOOP_TEST_TAC     *)
(* does in the goal.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_DECIDE_TAC =
  ASM_SIMP_TAC[MLD_CHALLENGE_CMP_VAL] THEN
  REWRITE_TAC[MLD_CHALLENGE_CMP; MLD_CHALLENGE_VAL_ZX3; VAL_WORD_SUB_EQ_0] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  SIMPLE_ARITH_TAC;;

let MLD_CHALLENGE_BRANCH_TAC =
  W(fun (asl,w) ->
    if not(exists (fun (_,th) ->
             match concl th with
               Comb(Comb(Const("=",_),
                         Comb(Comb(Const("read",_),Const("PC",_)),_)),r) ->
                 is_cond r
             | _ -> false) asl)
    then ALL_TAC else
  FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),_)),r)
      when is_cond r ->
        let c = rand(rator(rator r)) in
        let use cth =
          ASSUME_TAC th THEN RULE_ASSUM_TAC(REWRITE_RULE[cth]) in
        (SUBGOAL_THEN c use THENL [MLD_CHALLENGE_DECIDE_TAC; ALL_TAC]) ORELSE
        (SUBGOAL_THEN (mk_neg c) (use o EQF_INTRO) THENL
          [MLD_CHALLENGE_DECIDE_TAC; ALL_TAC])
    | _ -> NO_TAC));;

let mld_challenge_is_read_reg r tm =
  is_eq tm && (try rand(rator(lhs tm)) = r with Failure _ -> false) &&
  (try fst(dest_const(rator(rator(lhs tm)))) = "read"
   with Failure _ -> false);;

let mld_challenge_is_bytes32 tm =
  is_eq tm && can (term_match [] `read (memory :> bytes32 a) s`) (lhs tm);;

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
