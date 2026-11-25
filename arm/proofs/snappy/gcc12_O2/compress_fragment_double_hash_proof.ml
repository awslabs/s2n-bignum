(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* CompressFragmentDoubleHash from its pieces: the start, then the pieces    *)
(* by induction on the potential of the model state (ENSURES_MEASURE_INDUCT, *)
(* common/ensures_measure.ml), until the return from join2.                  *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_spec.ml";;
needs "common/ensures_measure.ml";;

(* ------------------------------------------------------------------------- *)
(* Preconditions with an existential or a condition on the parameters.       *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_ENSURES_EXISTS_PRE = prove
 (`!(step:S->S->bool) (P:A->S->bool) Q C.
     (!x. ensures step (P x) Q C) ==> ensures step (\s. ?x. P x s) Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

let SNAPPY_ENSURES_STATIC_PRE = prove
 (`!(step:S->S->bool) A P Q C.
     (A ==> ensures step P Q C) ==> ensures step (\s. A /\ P s) Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* From any point to the return: the pieces put together, for the two forms  *)
(* of the end (with memcpy's correctness contract, the output; with its      *)
(* contract with memory safety, the output and the events in bounds).        *)
(* ------------------------------------------------------------------------- *)

let snappy_cf2_loop_stmt contract post =
  parse_term
   ("!" ^ snappy_cf2_vars ^ ". " ^ snappy_cf2_hyps ^ " /\\
     " ^ contract ^ " (imp \"memcpy\") ea el ev
     ==> !pt st. snappy_cf2_reach src st /\\ snappy_cf2_point pt
                 ==> ensures arm
                      (\\s. snappy_cf2_at " ^ snappy_cf2_args ^ " pt st s)
                      (\\s. " ^ post ^ ")
                      (" ^ snappy_cf2_frame ^ ")");;

let SNAPPY_CF2_GCC12_O2_LOOP_STMT =
  snappy_cf2_loop_stmt "memcpy_contract"
   "snappy_cf2_post src op stackpointer returnaddress x19 x20 x21 x29 s";;

let SNAPPY_CF2_GCC12_O2_LOOP_SAFE_STMT =
  snappy_cf2_loop_stmt "memcpy_correct_safe_contract"
   "snappy_cf2_post_safe src inp op table table2 ts pc stackpointer
      returnaddress x19 x20 x21 x29 ea el e s";;

let SNAPPY_ENSURES_POST_MONO = prove
 (`!(step:S->S->bool) P Q Q' C.
     ensures step P Q C ==> (!s. Q s ==> Q' s) ==> ensures step P Q' C`,
  MESON_TAC[ENSURES_POSTCONDITION_THM]);;

let SNAPPY_ENSURES_PRE_MONO = prove
 (`!(step:S->S->bool) P P' Q C.
     ensures step P Q C ==> (!s. P' s ==> P s) ==> ensures step P' Q C`,
  MESON_TAC[ENSURES_PRECONDITION_THM]);;

(* A piece at the point of the goal, its postcondition weakened to that of  *)
(* the induction: the return (join2), or a point with a smaller measure.    *)

let SNAPPY_CF2_PIECE_TAC th =
  MP_TAC(SPEC_ALL th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP SNAPPY_ENSURES_POST_MONO) THEN
  GEN_TAC THEN BETA_TAC THEN
  (DISCH_TAC THEN DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC ORELSE
   DISCH_THEN(X_CHOOSE_THEN `pt':num` (X_CHOOSE_THEN
     `st':snappy_cstate` STRIP_ASSUME_TAC)) THEN
   DISJ2_TAC THEN EXISTS_TAC `snappy_cf2_pot src st'` THEN
   CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`pt':num`; `st':snappy_cstate`] THEN
   ASM_REWRITE_TAC[]);;

let SNAPPY_CF2_LOOP_TAC join2th =
  let pieces =
   [SNAPPY_CF2_GCC12_O2_LOOP1; SNAPPY_CF2_GCC12_O2_LOOP2;
    SNAPPY_CF2_GCC12_O2_JOIN4; SNAPPY_CF2_GCC12_O2_LOOP4;
    SNAPPY_CF2_GCC12_O2_JOIN5; SNAPPY_CF2_GCC12_O2_LOOP5] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  W(fun (asl,w) ->
    let bod = snd(strip_forall w) in
    let ens = rand bod in
    let pre = lhand(rator ens) and q = lhand ens and c = rand ens in
    let ptv = `pt:num` and stv = `st:snappy_cstate` and nv = `n:num` in
    let sv = `s:armstate` in
    let atp = mk_abs(ptv,mk_abs(stv,pre)) in
    let r = mk_abs(nv,mk_abs(sv,
      list_mk_exists([ptv;stv],
        list_mk_conj[mk_comb(`snappy_cf2_reach src`,stv);
                     mk_eq(mk_comb(`snappy_cf2_pot src`,stv),nv);
                     mk_comb(`snappy_cf2_point`,ptv);
                     mk_comb(list_mk_comb(atp,[ptv;stv]),sv)]))) in
    MP_TAC(ISPECL [`arm`; r; q; c] ENSURES_MEASURE_INDUCT)) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      MAYCHANGE_IDEMPOT_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC SNAPPY_ENSURES_EXISTS_PRE THEN X_GEN_TAC `pt:num` THEN
    BETA_TAC THEN
    MATCH_MP_TAC SNAPPY_ENSURES_EXISTS_PRE THEN X_GEN_TAC `st:snappy_cstate` THEN
    BETA_TAC THEN
    REPEAT(MATCH_MP_TAC SNAPPY_ENSURES_STATIC_PRE THEN DISCH_TAC) THEN
    FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o
                  REWRITE_RULE[snappy_cf2_point]) THEN
    FIRST(map SNAPPY_CF2_PIECE_TAC (join2th :: pieces));
    DISCH_TAC THEN X_GEN_TAC `pt:num` THEN X_GEN_TAC `st:snappy_cstate` THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `snappy_cf2_pot src st`) THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP SNAPPY_ENSURES_PRE_MONO) THEN
    GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`pt:num`; `st:snappy_cstate`] THEN
    ASM_REWRITE_TAC[]];;

let SNAPPY_CF2_GCC12_O2_LOOP = prove
 (SNAPPY_CF2_GCC12_O2_LOOP_STMT, SNAPPY_CF2_LOOP_TAC SNAPPY_CF2_GCC12_O2_JOIN2);;

let SNAPPY_CF2_GCC12_O2_LOOP_SAFE = prove
 (SNAPPY_CF2_GCC12_O2_LOOP_SAFE_STMT,
  SNAPPY_CF2_LOOP_TAC SNAPPY_CF2_GCC12_O2_JOIN2_SAFE);;

(* ------------------------------------------------------------------------- *)
(* The theorems of DESIGN.md section 5.1: the start, then the pieces, with   *)
(* the callee-saved registers and SP preserved, and the input and output as  *)
(* byte lists.                                                               *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_CF2_COMBINE = prove
 (`!(step:S->S->bool) P (R:A->B->bool) Q Q' C.
     C ,, C = C /\
     ensures step P (\s. ?x y. R x y /\ Q x y s) C /\
     (!x y. R x y ==> ensures step (\s. Q x y s) Q' C)
     ==> ensures step P Q' C`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC `\s:S. ?x y. (R:A->B->bool) x y /\ Q x y s` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[ensures] THEN
  X_GEN_TAC `s:S` THEN BETA_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:B`]) THEN
  ASM_REWRITE_TAC[ensures] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let SNAPPY_CF2_ARGS =
  [`inp:byte list`; `src:int64`; `op:int64`; `table:int64`; `table2:int64`;
   `ts:num`; `pc:num`; `imp:string->int64`; `stackpointer:int64`;
   `returnaddress:int64`; `x19:int64`; `x20:int64`; `x21:int64`;
   `x29:int64`; `rw:num`; `ea:int64`; `el:num`; `ev:num`;
   `e:(uarch_event)list`];;

let SNAPPY_CF2_TOP_TAC safe loopth =
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_PRESERVED_TAC "x19" `X19` THEN ENSURES_PRESERVED_TAC "x20" `X20` THEN
  ENSURES_PRESERVED_TAC "x21" `X21` THEN ENSURES_PRESERVED_TAC "x29" `X29` THEN
  (if safe then ALL_TAC
   else GHOST_INTRO_TAC `e:(uarch_event)list` `read events`) THEN
  ABBREV_TAC `ts = snappy_table_size (LENGTH(inp:byte list)) DIV 2` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIRWISE; ALLPAIRS; ALL]) THEN
  MP_TAC(SPECL SNAPPY_CF2_ARGS SNAPPY_CF2_GCC12_O2_INIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ALLPAIRS; ALL]; DISCH_TAC] THEN
  MP_TAC(SPECL SNAPPY_CF2_ARGS loopth) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ALLPAIRS; ALL]; DISCH_TAC] THEN
  W(fun (asl,w) ->
    let is_ens t = try fst(dest_const(fst(strip_comb t))) = "ensures"
                   with Failure _ -> false in
    let ith = snd(find (fun (_,th) -> is_ens(concl th)) asl)
    and lth = snd(find (fun (_,th) -> is_forall(concl th) &&
                   is_ens(snd(dest_imp(snd(strip_forall(concl th)))))) asl) in
    let ith = REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] ith
    and lth = REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] lth in
    let c = rand(concl ith) in
    let idem = prove(mk_eq(list_mk_icomb ",," [c;c],c), MAYCHANGE_IDEMPOT_TAC) in
    let cth = MATCH_MP SNAPPY_CF2_COMBINE (CONJ idem (CONJ ith lth)) in
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC c THEN
    CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
    MAP_EVERY EXISTS_TAC [lhand(rator(concl cth)); lhand(concl cth)] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN
      REWRITE_TAC[C_ARGUMENTS; READ_BYTELIST_EQ_BYTES] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN BETA_TAC THEN
      REWRITE_TAC[snappy_cf2_post_safe; snappy_cf2_post; snappy_cf2_events;
                  C_RETURN; READ_BYTELIST_EQ_BYTES] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ACCEPT_TAC cth]);;

let SNAPPY_COMPRESS_FRAGMENT_DOUBLE_HASH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
   (SNAPPY_COMPRESS_FRAGMENT_DOUBLE_HASH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
    SNAPPY_CF2_TOP_TAC false SNAPPY_CF2_GCC12_O2_LOOP);;

let SNAPPY_COMPRESS_FRAGMENT_DOUBLE_HASH_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
   (SNAPPY_COMPRESS_FRAGMENT_DOUBLE_HASH_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
    SNAPPY_CF2_TOP_TAC true SNAPPY_CF2_GCC12_O2_LOOP_SAFE);;
