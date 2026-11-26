(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tactics and lemmas for the stages of the clang 23 signature_internal      *)
(* proofs of ML-DSA-65 and ML-DSA-87 (signature_internal_65_stages.ml): the  *)
(* parts of signature_internal_44_stages.ml that do not depend on the        *)
(* parameter set, with the number of rows, the frame and the code ranges as  *)
(* arguments.                                                                *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_stage.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign6587.ml";;
needs "x86/proofs/utils/mldsa_native_signing_rr.ml";;
needs "x86/proofs/utils/mldsa_native_lazy_matrix.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/lazy_eq_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* Calls of region lemmas and of real callees inside a stage.                *)
(* ------------------------------------------------------------------------- *)

(* a fact for j < n from one for a larger bound *)
let SI_BOUND_TAC =
  W(fun (asl,w) ->
    let v,bd = dest_forall w in
    let ant = lhand bd in
    X_GEN_TAC v THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN UNDISCH_TAC ant THEN ARITH_TAC));;

(* the preconditions of a region lemma: word arithmetic, the facts as they   *)
(* are, bounds, extra tactics (pre), then those of VM_PRE_TAC                *)
let SI_GCALL_TAC exec allowed pre name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,exec,0x0,VM_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [REPEAT CONJ_TAC THEN
      TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
      TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
      TRY(REWRITE_TAC[GSYM ADD_ASSOC] THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
      TRY(SI_BOUND_TAC THEN NO_TAC) THEN
      TRY(pre THEN NO_TAC) THEN
      VM_PRE_TAC allowed;
      LABEL_TAC name th]);;

(* a real callee whose CALL is step n - 1 *)
let SI_GFCALL_TAC exec allowed pre name ilist n =
  SI_GCALL_TAC exec allowed pre name
   (ilist @ [`pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]) n THEN
  RSP_NORM_TAC THEN EXPAND_CALLEE_MEMACCESS_TAC;;

(* an XMM register as a numeral after its 128-bit load from the image *)
let SI_XMM_PRE_TAC =
  REWRITE_TAC[XMM4; XMM5; XMM6; XMM7; READ_COMPONENT_COMPOSE; READ_ZEROTOP_128] THEN
  ASM_REWRITE_TAC[VM_ZX_JOIN; WORD_XOR_REFL] THEN CONV_TAC WORD_REDUCE_CONV;;

(* the PC after a region lemma whose exit is fn + k, as one numeral *)
let SI_RIP_NORM_TAC =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read RIP s = x`) (concl th)
                           then CONV_RULE(DEPTH_CONV NUM_ADD_CONV) th else th);;

(* the RIP-relative 128-bit loads of the image constants named cs into the   *)
(* registers regs (YMM names), after state n, the first load ending at fn + *)
(* r and each next one 8 bytes later                                         *)
let SI_RCONST_TAC fn cs regs n r =
  let st = mk_var("s"^string_of_int n,`:x86state`) in
  YMM_GHOST_TAC st
    (map (fun g -> (g, String.lowercase_ascii g^"_"^string_of_int n)) regs) THEN
  EVERY (map2 (fun c i ->
    IMAGE_RIPREL_TAC (IMAGE_CONST_RULE_FOR VM_MC (layout c) 128)
      (layout fn + r + 8 * i)) cs (0--(length cs - 1)));;

(* RUN_STRAIGHT_TAC of inline_verify.ml from step n0, stopping at the image  *)
(* offset stop (or where the PC is no longer known, for stop = -1)           *)
let SI_RUN_TO_TAC execth memset_name allowed stop n0 =
  let plt = layout "plt_memset" and got = layout "got_memset" in
  let rec run n (asl,w) =
    let off = cur_pc_offset (asl,w) in
    if off = stop || off < 0 then ALL_TAC (asl,w)
    else if off = plt then
      (LIBC_PLT_TAC execth plt got (n - 1) THEN
       LIBC_FULL_CALL_TAC memset_name execth
        [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
         `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
        allowed (n + 1) THEN RSP_NORM_TAC THEN
       run (n + 2)) (asl,w)
    else (X86_STEPS_TAC execth [n] THEN run (n + 1)) (asl,w) in
  run n0;;

(* ------------------------------------------------------------------------- *)
(* Norm checks and the end of a stage.                                       *)
(* ------------------------------------------------------------------------- *)

(* the checks as (P <=> ok), so that rewriting with them keeps ok1 and ok2 *)
let SI_ORIENT_TAC =
  FIRST_X_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `ok1:bool`
                          then ASSUME_TAC(GSYM th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `ok1:bool`
                          then ASSUME_TAC(CONV_RULE(RAND_CONV SYM_CONV) th) else NO_TAC);;

(* the branch on a norm check (test eax, eax; jne) in the PC and in the events,
   as ok, from (mld_poly_chknorm x b = word 0 <=> ok), which is then dropped *)
let SI_DECIDE_TAC okv =
  FIRST_X_ASSUM(fun th ->
    if is_iff(concl th) && rhs(concl th) = okv then
      RULE_ASSUM_TAC(fun th' ->
        if can (term_match [] `read RIP s = x`) (concl th') ||
           can (term_match [] `read events s = x`) (concl th')
        then REWRITE_RULE[th] (REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0; WORD_AND_REFL] th')
        else th')
    else NO_TAC);;

let SI_MAYCHANGE_TAC d =
  W(fun (asl,w) -> if maychange_term w then ALL_TAC else NO_TAC) THEN
  SI_FB_NORM_TAC d THEN
  FIRST_X_ASSUM(fun th -> if maychange_term (concl th) && not(is_forall(concl th))
                          then MP_TAC th else NO_TAC) THEN
  DISCH_TAC THEN MONOTONE_MAYCHANGE_TAC;;

let SI_END_TAC d = REPEAT CONJ_TAC THEN (SI_MAYCHANGE_TAC d ORELSE SI_DISCHARGE_TAC d);;

(* a failed check: the PC with ~ok, then the end *)
let SI_FAIL_TAC d okv =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read RIP s = x`) (concl th)
                           then REWRITE_RULE[ASSUME(mk_neg okv)] th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI_END_TAC d;;

(* the PC with ok, and an implication with antecedent ok as its conclusion *)
let SI_PASS_TAC okv =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read RIP s = x`) (concl th)
                           then REWRITE_RULE[ASSUME okv] th else th) THEN
  TRY(FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = okv
                              then ASSUME_TAC(MP th (ASSUME okv)) else NO_TAC));;

(* the counter test of a loop of k iterations, from inc + cmp $k + jne *)
let SI_TEST_RULE k =
  let kt = mk_small_numeral k in
  let c = rhs(concl(NUM_REDUCE_CONV
            (mk_binop `(-):num->num->num` `18446744073709551616` (mk_small_numeral (k - 1))))) in
  prove(subst [kt,`k:num`; c,`c:num`]
   `!j. j < k ==> (val(word (j + c):int64) = 0 <=> ~(j + 1 < k))`,
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV);;

(* sub $-128 and its kin, as additions *)
let SI_SUB_NEG = WORD_BLAST
 `(!x:int64. word_sub x (word 18446744073709551488) = word_add x (word 128))`;;

(* a register as word (a + b) after an addition of a numeral *)
let SI_WORD_ADD_TAC =
  REWRITE_TAC[SI_SUB_NEG; GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Rows and vectors in memory.                                               *)
(* ------------------------------------------------------------------------- *)

let SI_ROW_ALIGNED = prove
 (`!rsp0:int64 b j. aligned 32 rsp0 /\ 16 divides b
                    ==> aligned 16 (word_add rsp0 (word (b + 1024 * j)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ALIGNED_WORD_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC(MP (ISPECL [`16`;`32`;`rsp0:int64`] ALIGNED_WORD_WEAKEN)
                    (EQT_ELIM(DIVIDES_CONV `16 divides 32`))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[];
      MATCH_MP_TAC DIVIDES_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC DIVIDES_RMUL THEN CONV_TAC DIVIDES_CONV]]);;

let SI_ROW_ALIGNED_TAC b =
  MP_TAC(SPECL [`rsp0:int64`; mk_small_numeral b; `j:num`] SI_ROW_ALIGNED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC DIVIDES_CONV; DISCH_TAC];;

(* the PC after row i of the first m <= k rows, from that of the row lemma *)
let SI_LOOP_PC = prove
 (`!i m k a b. i < m /\ m <= k
             ==> (if i + 1 < k then word a else word b):int64 =
                 word (if i + 1 < m then a else if m < k then a else b)`,
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMPLE_ARITH_TAC);;

let SI_SEED16 = prove
 (`!a:int64 r i j s:x86state.
        read (memory :> bytes(a,32)) s = r /\
        read (memory :> bytes16(word_add a (word 32))) s = word (j + 256 * i) /\
        j + 256 * i < 65536
        ==> read (memory :> bytes(a,34)) s = mld_matrix_seed r i j`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mld_matrix_seed; ARITH_RULE `34 = 32 + 2`;
              READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[CONJUNCT1 MLD_BYTES2] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;

let SI_JOIN_VECN32 = prove
 (`!(B:int64) off (V:num->int32) (s:x86state) n.
        (!r k. r < n /\ k < 256
               ==> read (memory :> bytes32 (word_add B (word ((off + 1024 * r) + 4 * k)))) s =
                   mld_poly_of V r k)
        ==> !i. i < 256 * n ==> read (memory :> bytes32 (word_add B (word (off + 4 * i)))) s = V i`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`i DIV 256`; `i MOD 256`]) THEN
  REWRITE_TAC[mld_poly_of] THEN
  MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_EQ_CONV)) THEN
  REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC [`q = i DIV 256`; `t = i MOD 256`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `q < n /\ (off + 1024 * q) + 4 * t = off + 4 * i /\ 256 * q + t = i`
   (fun th -> REWRITE_TAC[th] THEN ASM_REWRITE_TAC[]) THEN
  MAP_EVERY UNDISCH_TAC [`i = q * 256 + t`; `t < 256`; `i < 256 * n`] THEN ARITH_TAC);;

(* rows of 128 bytes (the packed w1 of gamma2 = (q-1)/32) *)
let SI_JOIN_VECN8 = prove
 (`!(B:int64) off (P:num->byte) (s:x86state) n.
        (!r j. r < n /\ j < 128
               ==> read (memory :> bytes8 (word_add B (word ((off + 128 * r) + j)))) s =
                   P (128 * r + j))
        ==> !t. t < 128 * n ==> read (memory :> bytes8 (word_add B (word (off + t)))) s = P t`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`t DIV 128`; `t MOD 128`]) THEN
  MP_TAC(SPECL [`t:num`; `128`] DIVISION) THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_EQ_CONV)) THEN
  REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC [`q = t DIV 128`; `u = t MOD 128`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `q < n /\ (off + 128 * q) + u = off + t /\ 128 * q + u = t`
   (fun th -> REWRITE_TAC[th] THEN ASM_REWRITE_TAC[]) THEN
  MAP_EVERY UNDISCH_TAC [`t = q * 128 + u`; `u < 128`; `t < 128 * n`] THEN ARITH_TAC);;

let SI_SLICE_VECN32 = prove
 (`!(B:int64) off (V:num->int32) (s:x86state) n r.
        (!i. i < 256 * n ==> read (memory :> bytes32 (word_add B (word (off + 4 * i)))) s = V i) /\
        r < n
        ==> !k. k < 256
                ==> read (memory :> bytes32 (word_add B (word ((off + 1024 * r) + 4 * k)))) s =
                    mld_poly_of V r k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_poly_of] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `256 * r + k`) THEN
  REWRITE_TAC[ARITH_RULE `off + 4 * (256 * r + k) = (off + 1024 * r) + 4 * k`] THEN
  DISCH_THEN MATCH_MP_TAC THEN MAP_EVERY UNDISCH_TAC [`r < n`; `k < 256`] THEN ARITH_TAC);;

let SI_MAP_POLY_OF = prove
 (`!(f:(num->int32)->num->int32) x r (B:int64) d (s:x86state).
     (!k. k < 256 ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s =
                      f (mld_poly_of x r) k)
     ==> (!k. k < 256 ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s =
                          mld_poly_of (mld_polyvec_map f x) r k)`,
  SIMP_TAC[MLD_POLY_OF_POLYVEC_MAP]);;

let SI_POLYVEC_POLY_OF = prove
 (`!(F:num->num->int32) r (B:int64) d (s:x86state).
     (!k. k < 256 ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s = F r k)
     ==> (!k. k < 256 ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s =
                          mld_poly_of (mld_polyvec F) r k)`,
  SIMP_TAC[MLD_POLY_OF_POLYVEC]);;

(* the facts for rows 0 .. n - 1 at B + off + 1024 r as one fact over r *)
let SI_ROWS_TAC b off st (pat:term) =
  let gl = subst [b,`B:int64`; mk_small_numeral off,`off:num`; st,`s:x86state`] pat in
  SUBGOAL_THEN gl ASSUME_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN FIRST_ASSUM ACCEPT_TAC);
    ALL_TAC];;

(* the fact of the form f (mld_poly_of x r) k after a region lemma, as row r
   of mld_polyvec_map f x *)
let SI_MAP_POLY_OF_TAC f =
  let pat = subst [f,`f:(num->int32)->num->int32`]
   `!k. k < 256
        ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s =
            (f:(num->int32)->num->int32) (mld_poly_of x r) k` in
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP SI_MAP_POLY_OF o
    check (fun th -> can (term_match [] pat) (concl th)));;

let SI_ZERO_LO_SPLIT = WORD_BLAST
 `!x:int128. word_subword (word_subword (word_join x (word 0:int128):int256) (0,128):int128) (0,64):int64 = word 0 /\
             word_subword (word_subword (word_join x (word 0:int128):int256) (0,128):int128) (64,64):int64 = word 0`;;

let SI_SX_ZX = WORD_BLAST `!v:int64. (word_sx v:int32) = word_zx v`;;

let SI_BL_NZ = prove
 (`!(h:56 word). ~(word_zx (word_join h (word 1:byte):int64) = (word 0:byte))`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* The paths of a whole attempt.                                             *)
(* ------------------------------------------------------------------------- *)

let SI_PC_TAC =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read RIP s = x`) (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NUM_LT_CONV THENC REWRITE_CONV[]) th else th) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `read RIP s = x`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(* the memaccess goal of a path, as at the end of SI_DISCHARGE_TAC: the
   facts of the callees split with their definitions (only equations of
   event-list variables, so that numeric equations such as r = 18 are left
   alone), the frame normalized to rsp0 - d *)
let SI_MEMACCESS_TAC d =
  let is_vdef th = let c = concl th in
    is_eq c && is_var(lhs c) && type_of(lhs c) = `:(uarch_event)list` in
  let is_meminb v th = let c = concl th in
    (match strip_comb c with
       Const("memaccess_inbounds",_),(e::_) -> e = v
     | _ -> false) in
  let split_tac =
    W(fun (asl,w) ->
      let defs = filter is_vdef (map snd asl) in
      MAP_EVERY (fun dth ->
        let v = lhs(concl dth) in
        MAP_EVERY (fun (_,mth) ->
          if is_meminb v mth then
            STRIP_ASSUME_TAC(REWRITE_RULE[MEMACCESS_INBOUNDS_APPEND] (REWRITE_RULE[dth] mth))
          else ALL_TAC) asl) defs) in
  SIGN_BETA_ALL_TAC THEN SI_FB_NORM_TAC d THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN split_tac THEN
  RULE_ASSUM_TAC(fun th -> if (match strip_comb(concl th) with
      (Const("memaccess_inbounds",_),_) -> true | _ -> false)
     then REWRITE_RULE[MEMACCESS_INBOUNDS_APPEND] th else th) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) &&
      (match strip_comb(fst(dest_conj(concl th))) with
         (Const("memaccess_inbounds",_),_) -> true | _ -> false)
     then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   BYTE_IDX_DISCHARGE_TAC DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let SI_PATH_DISCHARGE_TAC d =
  SIGN_BETA_ALL_TAC THEN SIGN_SELECT_TAC THEN SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_PATH_UNIFY_TAC; SI_MEMACCESS_TAC d];;

let SI_FIN_TAC d =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ZX_0] THEN
  REPEAT CONJ_TAC THEN (SI_MAYCHANGE_TAC d ORELSE SI_PATH_DISCHARGE_TAC d);;

(* ------------------------------------------------------------------------- *)
(* The unpacking of w1 for the hints (W1UNPACK4 of inline_sign6587.ml) with  *)
(* the nibble mask that the code loads into XMM5 (the image constant         *)
(* mldsaNN_signature_internal_const3, bytes 0f 0f 0f 0f 00 0f 00 0f ..):     *)
(* W1U4_MASK there has other upper bytes, which the unpacking does not use,  *)
(* so its lemmas cannot be called where the code loaded the real constant.   *)
(* The tactic is that of W1UNPACK4_TAC with this mask in the invariant.      *)
(* ------------------------------------------------------------------------- *)

let SI_W1U4_MASK = "0x0f000f000f000f000f000f000f0f0f0f";;

let SI_W1UNPACK4_STMT fn loop exit idx tmp ib ob =
  subst [mk_comb(`word:num->int128`,parse_term SI_W1U4_MASK),
         mk_comb(`word:num->int128`,parse_term W1U4_MASK)]
        (W1UNPACK4_STMT fn loop exit idx tmp ib ob);;

let SI_W1U4_SETUP_TAC exec fn loop exit idx ib ob =
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num).
      APPEND (f_ev_epil rsp0 pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop rsp0 pc i)) (f_ev_prol rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `b:num->byte`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(subst_tokens ["@IDX@",idx; "@IB@",string_of_int ib; "@OB@",string_of_int ob;
                             "@MASK@",SI_W1U4_MASK]
   "\\i s. read RSP s = rsp0 /\\ read @IDX@ s = word (4 * i) /\\
          read XMM4 s = word 0 /\\ read XMM5 s = word @MASK@ /\\
          (!j. j < 128 ==> read(memory :> bytes8(word_add rsp0 (word (@IB@ + j)))) s = b j) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(@OB@ + 4 * j)))) s =
                   mld_polyw1_unpack_32 b j)"));;

let SI_PROVE_W1UNPACK4 fn loop exit idx tmp ib ob =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
    [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(SI_W1UNPACK4_STMT fn loop exit idx tmp ib ob,
        SI_W1U4_SETUP_TAC exec fn loop exit idx ib ob THEN
        REPEAT CONJ_TAC THENL
         [ARITH_TAC; W1U4_PRE_TAC; W1U4_BODY_TAC exec ib ob THEN W1U4_FIN_TAC ob;
          FULL_EXIT0_TAC]);;
