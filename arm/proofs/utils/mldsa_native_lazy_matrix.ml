(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the matrix-vector products of the reduced-RAM     *)
(* code (mld_polyvec_matrix_pointwise_montgomery_row_lazy and _yvec_lazy):   *)
(* the code copies rho to a buffer of 64 bytes on the stack and stores the   *)
(* indices j and i of an entry after it before each call of                  *)
(* mldsa_poly_uniform, as mld_polyvec_matrix_expand_eager does (see          *)
(* utils/mldsa_native_matrix.ml), but for a row index i that is an argument  *)
(* of the function rather than a constant. The results are folded with       *)
(* mld_lazy_acc of common/mldsa_native_lazy.ml.                              *)
(* ========================================================================= *)

(* The part that depends on AArch64; the rest is in                          *)
(* common/fips204/properties/mldsa_native_lazy_matrix.ml.                    *)

needs "common/mldsa_native_lazy.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;
needs "arm/proofs/utils/mldsa_native_keypair.ml";;
needs "common/fips204/properties/mldsa_native_lazy_matrix.ml";;

(* ------------------------------------------------------------------------- *)
(* MLD_LAZY_ROW_SEED_TAC k buf j s: the 34 bytes at stackpointer + buf in    *)
(* state s are mld_matrix_seed r i j, from the two halves of rho stored      *)
(* there and the bytes j and i after it, for the row index i < k.            *)
(* MLD_LAZY_ROW_TERM_TAC k l j: the termination hypothesis for that seed,    *)
(* for j < l, from mld_matrix_terminates k l r rewritten with its definition *)
(* (MLD_LAZY_RBOUND_TAC, as MEXP_SETUP_TAC does).                            *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_RBOUND_TAC s =
  SUBGOAL_THEN `r < 2 EXP 256` (ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV) THENL
   [FIRST_ASSUM(MP_TAC o SYM o check
     (can (term_match []
        `read (memory :> bytes(word_add mat (word 1024),32)) s = n`) o
      concl)) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    MP_TAC(ISPECL [`word_add mat (word 1024):int64`; `32`;
                   mk_comb(`read memory`,mk_var(s,`:armstate`))]
                  READ_BYTES_BOUND) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[mld_matrix_terminates] o check
    (can (term_match [] `mld_matrix_terminates k l r`) o concl));;

let MLD_LAZY_ROW_SEED_TAC k buf j s =
  let a = MEXP_SP buf and a32 = MEXP_SP (buf + 32) in
  let sv = mk_var(s,`:armstate`) and jt = mk_small_numeral j in
  let kt = mk_small_numeral k in
  SUBGOAL_THEN (subst [a32,`a:int64`; sv,`s:armstate`; jt,`j:num`]
      `read (memory :> bytes(a,2)) s = j + 256 * i`) ASSUME_TAC THENL
   [REWRITE_TAC[CONJUNCT2 MLD_BYTES2] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32;
                DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE(mk_imp(mk_binop `(<):num->num->bool` `i:num` kt,
       `i < 256 /\ i < 4294967296 /\ i < 18446744073709551616`))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  MP_TAC(SPECL [a; `r:num`; `i:num`; jt; sv] MLD_SEED_INPUT) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* The copy of rho into the structure of the matrix sampled on demand        *)
(* (mld_polyvec_matrix_expand_lazy), whose contract gives the bytes:         *)
(* MLD_LAZY_RHO_BYTES s is the function of the 32 bytes at rho in state s,   *)
(* MLD_LAZY_RHO_BYTES_TAC s states the precondition of the call for it, and  *)
(* MLD_LAZY_RHO_COPY_TAC a s' proves read (memory :> bytes(a,32)) s' = r in  *)
(* the state s' after the call, for a = mat + 1024, from the postcondition   *)
(* and read (memory :> bytes(rho,32)) s' = r.                                *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_RHO_BYTES s =
  subst [mk_var(s,`:armstate`),`s:armstate`]
   `\j. read (memory :> bytes8 (word_add rho (word j))) s`;;

let MLD_LAZY_RHO_BYTES_TAC s =
  let b = MLD_LAZY_RHO_BYTES s in
  SUBGOAL_THEN
   (subst [b,`b:num->byte`; mk_var(s,`:armstate`),`s:armstate`]
     `!j. j < 32
          ==> read (memory :> bytes8 (word_add rho (word j))) s =
              (b:num->byte) j`)
   ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN REFL_TAC; ALL_TAC];;

let MLD_LAZY_RHO_COPY_TAC a s' =
  let sv' = mk_var(s',`:armstate`) in
  let b = subst [sv',`s:armstate`]
           `\j. read (memory :> bytes8 (word_add rho (word j))) s` in
  let copied th =
    let c = concl th in
    is_forall c && can (find_term ((=) sv')) c &&
    can (find_term ((=) `stackpointer:int64`)) c &&
    can (find_term ((=) `rho:int64`)) c in
  SUBGOAL_THEN
   (subst [a,`a:int64`; sv',`s:armstate`]
     `read (memory :> bytes(a,32)) s = r`)
   ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rho:int64`; `32`; b; sv'] MLD_KEYPAIR_BYTES_EQ_BYTES8) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MLD_KEYPAIR_BYTES_EQ_BYTES8] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check copied) THEN
    ASM_REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC];;

let MLD_LAZY_FULL_OF_FULL0_TAC full0 lemtac =
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MP_TAC(MATCH_MP full0 th)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC_ALL o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "ensures"
                             with Failure _ -> false)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ_ALT] ENSURES_POSTCONDITION_THM)) THEN
  lemtac THEN
  X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(EXISTS_TAC `e2:(uarch_event)list` THEN ASM_REWRITE_TAC[] THEN
      NO_TAC) THEN
  ASM_SIMP_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The loops of the signing product (see                                     *)
(* common/fips204/properties/mldsa_native_lazy_matrix.ml). The frame of 176  *)
(* bytes is at stackpointer + 1392 (the 1392 bytes below it are those of     *)
(* mldsa_poly_uniform), with the saved registers at stackpointer + 1392 and  *)
(* the canary at stackpointer + 1560; MLD_LAZY_INV_FRAME breg is the part of *)
(* the invariants for the frame, with the buffer buf of the seed in register *)
(* breg, the arguments in X23-X26 and the facts of the precondition that the *)
(* callees need. MLD_LAZY_BUFFER_SETUP_TAC n introduces the buffer, at       *)
(* stackpointer + boff where the code puts it, with its bound and the facts  *)
(* that it is apart from the other regions, for w of n bytes, and adds it to *)
(* the frame of the goal, so that the simulation keeps the writes to it in   *)
(* the frame; after the AND of the code, MLD_LAZY_BUFFER_REG_TAC breg puts   *)
(* buf in the register. MLD_LAZY_YVEC_SEED_TAC jt s proves that the 34 bytes *)
(* of the buffer in state s are the seed of entry (i,jt), from rho and the   *)
(* two bytes after it.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_INV_FRAME breg =
  "read SP s = word_add stackpointer (word 1392) /\\
   read " ^ breg ^ " s = buf /\\
   read X23 s = mat /\\ read X24 s = scratch /\\ read X25 s = y /\\
   read X26 s = w /\\
   read (memory :> bytes64 (word_add stackpointer (word 1392))) s =
   x19_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 1400))) s =
   x20_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 1408))) s =
   x21_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 1416))) s =
   x22_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 1424))) s =
   x23_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 1432))) s =
   x24_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 1440))) s =
   x25_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 1448))) s =
   x26_init /\\
   read (memory :> bytes64 (word_add stackpointer (word 1456))) s =
   returnaddress /\\
   read (memory :> bytes64 (word_add stackpointer (word 1560))) s =
   canary /\\
   read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard)))
    s = guard /\\
   read (memory :> bytes64 guard) s = canary /\\
   read (memory :> bytes64 (word(pc + got_memset))) s = mf /\\
   read (memory :> bytes(ea,el)) s = ev /\\
   read (memory :> bytes(buf,32)) s = r /\\
   read (memory :> bytes64 y) s = rp /\\
   read (memory :> bytes16 (word_add y (word 8))) s = kappa /\\
   read (memory :> bytes(rp,64)) s = RP";;

let MLD_LAZY_BUFFER_SETUP_TAC n =
  let wr = mk_pair(`w:int64`,mk_small_numeral n) in
  ABBREV_TAC
   `boff = 1503 - val(word_add stackpointer (word 1503):int64) MOD 32` THEN
  SUBGOAL_THEN `1472 <= boff /\ boff <= 1488` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "boff" THEN
    MP_TAC(MATCH_MP MLD_LAZY_BUFFER_BOUND
            (ASSUME `aligned 16 (stackpointer:int64)`)) THEN
    MP_TAC(SPECL [`val(word_add stackpointer (word 1503):int64)`; `32`]
                 MOD_LT_EQ) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 1503)) (word 18446744073709551584) =
    word_add stackpointer (word boff):int64`
   ASSUME_TAC THENL
   [EXPAND_TAC "boff" THEN MATCH_MP_TAC MLD_LAZY_BUFFER_AND THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `buf = word_add stackpointer (word boff):int64` THEN
  MAP_EVERY (fun r ->
    SUBGOAL_THEN
     (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                      `buf:int64,64`),r))
     ASSUME_TAC THENL
     [EXPAND_TAC "buf" THEN NONOVERLAPPING_TAC; ALL_TAC])
   [`stackpointer:int64,1464`; `word_add stackpointer (word 1560):int64,8`;
    wr; `mat:int64,1024`; `scratch:int64,1024`;
    `word_add mat (word 1024):int64,32`; `y:int64,16`; `rp:int64,64`;
    `word pc:int64,libmldsa_size`;
    `word_add (word pc) (word got_stack_chk_guard):int64,8`;
    `guard:int64,8`; `word(pc + got_memset):int64,8`; `ea:int64,el:num`] THEN
  W(fun (asl,w) ->
    let c = rand w in
    let c' = mk_comb(mk_comb(fst(strip_comb c),c),
                     `MAYCHANGE [memory :> bytes(buf:int64,64)]`) in
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC c' THEN
    CONJ_TAC THENL
     [EXPAND_TAC "buf" THEN EXPAND_TAC "boff" THEN SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC]);;

let MLD_LAZY_BUFFER_REG_TAC breg =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `word_and (word_add stackpointer (word 1503))
                            (word 18446744073709551584):int64 = x`)
           (concl th)
    then RULE_ASSUM_TAC(fun th' ->
           if free_in breg (concl th') then REWRITE_RULE[th] th' else th')
    else NO_TAC);;

let MLD_LAZY_SEED = prove
 (`!a:int64 r i j s:armstate.
        read (memory :> bytes(a,32)) s = r /\
        read (memory :> bytes(word_add a (word 32),2)) s = j + 256 * i
        ==> read (memory :> bytes(a,34)) s = mld_matrix_seed r i j`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mld_matrix_seed; ARITH_RULE `34 = 32 + 2`;
              READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLD_LAZY_YVEC_SEED_TAC jt s =
  let sv = mk_var(s,`:armstate`) in
  SUBGOAL_THEN (subst [jt,`j:num`; sv,`s:armstate`]
     `read (memory :> bytes(word_add buf (word 32),2)) s = j + 256 * i`)
   ASSUME_TAC THENL
   [REWRITE_TAC[CONJUNCT2 MLD_BYTES2] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32;
                DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  MP_TAC(SPECL [`buf:int64`; `r:num`; `i:num`; jt; sv] MLD_LAZY_SEED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;
