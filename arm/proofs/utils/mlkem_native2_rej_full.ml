(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform rejection sampling, mlkem_rej_uniform_alt_VARIABLE_TIME,          *)
(* appending to a partial result: the events as a function of the inputs,    *)
(* alone and together with the result ("FULL"), for the subroutine with its  *)
(* BTI landing pad. Loaded by the proof file of the leaf, with loadt, after  *)
(* the standalone proof of arm/proofs/mlkem_rej_uniform_alt_VARIABLE_TIME.ml, *)
(* whose names it uses.                                                      *)
(* ========================================================================= *)


(* The events depend on which numbers are accepted, so they do not follow a  *)
(* fixed template, but they depend only on the addresses, the count n and    *)
(* the input list inlist. Each block of code between loop labels is shown to *)
(* add a list of events depending only on such public values (and the chunk  *)
(* index and the current count), found by unification after the simulation;  *)
(* the loops are put together by induction, the events of the whole run      *)
(* being given by the existential at each stage and finally by Skolemization *)
(* over the arguments.                                                       *)

(* ------------------------------------------------------------------------- *)
(* The state at a loop label after p chunks of 24 bytes, as in rej_inv but   *)
(* without the events, which are stated separately, and the end state, as in *)
(* rej_fin for some number q of chunks used, after which either there are    *)
(* none left or the result is complete.                                      *)
(* ------------------------------------------------------------------------- *)

let rej_st = new_definition
 `rej_st (res:int64) (buf:int64) buflen (table:int64) curlist inlist
         (stackpointer:int64) p (s:armstate) <=>
    read SP s = stackpointer /\
    read X0 s = res /\ read X4 s = table /\
    read X2 s = word_add buf (word(24 * p)) /\
    read X3 s = word(buflen - 24 * p) /\
    read X1 s = word(LENGTH(rej_out curlist inlist p)) /\
    read X5 s = word_add res (word(2 * LENGTH(rej_out curlist inlist p))) /\
    read Q30 s = word 0x0d010d010d010d010d010d010d010d01 /\
    read Q31 s = word 0x01800140012001100108010401020101 /\
    read (memory :> bytes(table,4096)) s =
    num_of_wordlist mlkem_rej_uniform_table /\
    read (memory :> bytes(buf,buflen)) s = num_of_wordlist inlist /\
    read (memory :> bytes(res,2 * LENGTH(rej_out curlist inlist p))) s =
    num_of_wordlist (rej_out curlist inlist p)`;;

let rej_end = new_definition
 `rej_end (res:int64) (buf:int64) buflen (table:int64) curlist inlist
          (stackpointer:int64) (s:armstate) <=>
    ?q. 24 * q <= buflen /\
        (buflen < 24 * (q + 1) \/ 256 <= LENGTH(rej_out curlist inlist q)) /\
        rej_st res buf buflen table curlist inlist stackpointer q s`;;

(* The state in the final copy, as in rej_cinv but without the events        *)

let rej_cst = new_definition
 `rej_cst (res:int64) (buf:int64) buflen (table:int64)
          (inlist:(12 word)list)
          (stackpointer:int64) p (out:int16 list)
          (L:int16 list) m i (s:armstate) <=>
    read SP s = stackpointer /\
    read X0 s = res /\ read X4 s = table /\
    read X2 s = word_add buf (word(24 * (p + 1))) /\
    read X3 s = word(buflen - 24 * (p + 1)) /\
    read X1 s = word(LENGTH out + m) /\
    read X5 s = word_add res (word(2 * (LENGTH out + i))) /\
    read X11 s = word_add stackpointer (word(2 * i)) /\
    read X8 s = word(m - i) /\
    read Q30 s = word 0x0d010d010d010d010d010d010d010d01 /\
    read Q31 s = word 0x01800140012001100108010401020101 /\
    read (memory :> bytes(table,4096)) s =
    num_of_wordlist mlkem_rej_uniform_table /\
    read (memory :> bytes(buf,buflen)) s = num_of_wordlist inlist /\
    read (memory :> bytes(stackpointer,2 * LENGTH L)) s = num_of_wordlist L /\
    read (memory :> bytes(res,2 * (LENGTH out + i))) s =
    num_of_wordlist (APPEND out (SUB_LIST(0,i) L))`;;

(* The count after p chunks depends on curlist only through its length       *)

let rej_len = new_definition
 `rej_len k (inlist:(12 word)list) p =
  MIN 256 (k + LENGTH(REJ_SAMPLE(SUB_LIST(0,16 * p) inlist)))`;;

let LENGTH_REJ_OUT_LEN = prove
 (`!curlist inlist p.
        LENGTH(rej_out curlist inlist p) =
        rej_len (LENGTH curlist) inlist p`,
  REWRITE_TAC[rej_out; rej_len; LENGTH_SUB_LIST; LENGTH_APPEND; SUB_0]);;

(* ------------------------------------------------------------------------- *)
(* The sequencing of two blocks, the events of the second being added to     *)
(* those of the first.                                                       *)
(* ------------------------------------------------------------------------- *)

let ENSURES_FALSE_PRE = prove
 (`!step Q C. ensures step (\s. F) Q C`,
  REWRITE_TAC[ensures]);;

let REJ_EV_SEQ = prove
 (`!res stackpointer (pc:num) off1 off2 off3 (P:armstate->bool) Q S
    ev1 ev2 (e:(uarch_event)list) rd wr.
     ensures arm
      (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_tmc /\
           read PC s = word(pc + off1) /\ P s /\ read events s = e)
      (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_tmc /\
           read PC s = word(pc + off2) /\ Q s /\
           read events s = APPEND ev1 e /\ memaccess_inbounds ev1 rd wr)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(res,512);
                  memory :> bytes(stackpointer,48)]) /\
     ensures arm
      (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_tmc /\
           read PC s = word(pc + off2) /\ Q s /\
           read events s = APPEND ev1 e)
      (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_tmc /\
           read PC s = word(pc + off3) /\ S s /\
           read events s = APPEND ev2 (APPEND ev1 e) /\
           memaccess_inbounds ev2 rd wr)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(res,512);
                  memory :> bytes(stackpointer,48)])
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_tmc /\
               read PC s = word(pc + off1) /\ P s /\ read events s = e)
          (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_tmc /\
               read PC s = word(pc + off3) /\ S s /\
               read events s = APPEND (APPEND ev2 ev1) e /\
               memaccess_inbounds (APPEND ev2 ev1) rd wr)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(res,512);
                      memory :> bytes(stackpointer,48)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC REJ_TRANS THEN
  EXISTS_TAC
   `\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_tmc /\
        read PC s = word(pc + off2) /\ (Q:armstate->bool) s /\
        read events s = APPEND ev1 e /\
        memaccess_inbounds (ev1:(uarch_event)list) rd wr` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `memaccess_inbounds (ev1:(uarch_event)list) rd wr` THEN
  ASM_REWRITE_TAC[ENSURES_FALSE_PRE; MEMACCESS_INBOUNDS_APPEND;
                  GSYM APPEND_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* The events of a block. The statements are of the form                     *)
(*                                                                           *)
(*   !public. hyps ==> ?ev. !curlist e. ... ==> ensures arm                  *)
(*     (\s. ... /\ read events s = e)                                        *)
(*     (\s. ... /\ read events s = APPEND ev e /\                            *)
(*              memaccess_inbounds ev ...) ...                               *)
(*                                                                           *)
(* where ev is made a metavariable before the simulation, then unified with  *)
(* the new events with the abbreviations made on the way expanded, checking  *)
(* that they depend only on the public values. The memory safety is proved   *)
(* for the events with the abbreviations, for the bounds on them.            *)
(* ------------------------------------------------------------------------- *)

(* The metavariables, with distinct names since a tactic may be applied      *)
(* to several cases, and the variables allowed in their instantiations,      *)
(* those free in the goal when they are introduced.                          *)

let rej_ev_allowed = ref ([]:(term * term list) list);;

let rej_ev_current = ref ([]:term list);;

let REJ_EV_META_TAC:tactic =
  let n = ref 0 in
  fun (asl,w) ->
    let v,_ = dest_exists w in
    let fvs = freesl (w::(map (concl o snd) asl)) in
    let _ = n := !n + 1 in
    let mv = mk_var("ev_" ^ string_of_int !n,type_of v) in
    let _ = rej_ev_allowed := (mv,fvs)::(!rej_ev_allowed) in
    X_META_EXISTS_TAC mv (asl,w);;

(* The assumptions t = v abbreviating t as a variable v that is not public   *)

let rej_abbrevs asl =
  mapfilter (fun (_,th) ->
    let c = concl th in
    if is_eq c && is_var(rhs c) && not(mem (rhs c) (!rej_ev_current)) &&
       not(vfree_in (rhs c) (lhs c))
    then th else fail()) asl;;

(* Prove `l = APPEND ev e`, where l is the list of events after the block    *)
(* (the new events consed onto e) and ev the metavariable.                   *)

let REJ_EV_TAC:tactic =
  let nilth = prove
   (`!l m m':(uarch_event)list. m = m' /\ [] = l ==> m = APPEND l m'`,
    MESON_TAC[APPEND]) in
  W(fun (asl,w) ->
    let l,r = dest_eq w in
    let mv = lhand r in
    let _ = rej_ev_current := assoc mv (!rej_ev_allowed) in
    let abbrevs = map SYM (rej_abbrevs asl) in
    if l = rand r then
      MATCH_MP_TAC nilth THEN CONJ_TAC THENL
       [REFL_TAC; SAFE_UNIFY_REFL_TAC rej_ev_current (ref [])]
    else
      CONV_TAC(LAND_CONV CONS_TO_APPEND_CONV) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC(LAND_CONV(PURE_REWRITE_CONV abbrevs)) THEN
      SAFE_UNIFY_REFL_TAC rej_ev_current (ref []));;

(* Prove memaccess_inbounds for the new events, after the unification,       *)
(* with the abbreviations restored                                           *)

let REJ_MI_TAC:tactic =
  W(fun (asl,w) -> TRY(PURE_REWRITE_TAC(rej_abbrevs asl))) THEN
  REWRITE_TAC[memaccess_inbounds; memaccess_inbounds_def;
              ALL; EX; FST; SND] THEN
  REPEAT CONJ_TAC THEN
  TRY(REPEAT ((DISJ1_TAC THEN CONTAINED_ASM_TAC) ORELSE DISJ2_TAC ORELSE
              CONTAINED_ASM_TAC) THEN NO_TAC);;

let REJ_EV_CLOSE_TAC:tactic = CONJ_TAC THENL [REJ_EV_TAC; REJ_MI_TAC];;

(* ------------------------------------------------------------------------- *)
(* The exits from the loops, when there are not enough bytes left or no room *)
(* for all that they could give.                                             *)
(* ------------------------------------------------------------------------- *)

let REJ_EV_LOOP24_EXIT = prove
 (`!res buf buflen table inlist stackpointer pc p c.
     buflen < 2 EXP 64 /\ 24 * p <= buflen /\
     (buflen < 24 * (p + 1) \/ 256 <= c)
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x2f0) /\
                     rej_st res buf buflen table curlist inlist stackpointer
                            p s /\
                     read events s = e)
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x3c4) /\
                     rej_end res buf buflen table curlist inlist
                             stackpointer s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stackpointer,48]
                      [stackpointer,48; res,512])
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stackpointer,48)])`,
  let INTRO_TAC =
    REJ_EV_META_TAC THEN
    MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
    REWRITE_TAC[rej_st; rej_end;
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `c < 2 EXP 64 /\ buflen - 24 * p < 2 EXP 64`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPECL [`curlist:int16 list`; `inlist:(12 word)list`; `p:num`]
        LENGTH_REJ_OUT) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY VAL_INT64_TAC [`c:num`; `buflen - 24 * p`] in
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `buflen < 24 * (p + 1)` THEN INTRO_TAC THENL
   [SUBGOAL_THEN `buflen - 24 * p < 24` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC (1--2);
    SUBGOAL_THEN `~(buflen - 24 * p < 24) /\ 256 <= c` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC (1--4)] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL [EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  REJ_EV_CLOSE_TAC);;

let REJ_EV_LOOP48_EXIT = prove
 (`!res buf buflen table inlist stackpointer pc p c.
     buflen < 2 EXP 64 /\ 24 * p <= buflen /\
     (buflen < 24 * (p + 2) \/ 224 < c)
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x200) /\
                     rej_st res buf buflen table curlist inlist stackpointer
                            p s /\
                     read events s = e)
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x2f0) /\
                     rej_st res buf buflen table curlist inlist stackpointer
                            p s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stackpointer,48]
                      [stackpointer,48; res,512])
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stackpointer,48)])`,
  let INTRO_TAC =
    REJ_EV_META_TAC THEN
    MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
    REWRITE_TAC[rej_st; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `c < 2 EXP 64 /\ buflen - 24 * p < 2 EXP 64`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPECL [`curlist:int16 list`; `inlist:(12 word)list`; `p:num`]
        LENGTH_REJ_OUT) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY VAL_INT64_TAC [`c:num`; `buflen - 24 * p`] THEN
    SUBGOAL_THEN
     `(224 <= c /\ ~(val(word_sub (word c:int64) (word 224)) = 0)) <=>
      224 < c`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] in
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `buflen < 24 * (p + 2)` THEN INTRO_TAC THENL
   [SUBGOAL_THEN `buflen - 24 * p < 48` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC (1--2);
    SUBGOAL_THEN `~(buflen - 24 * p < 48) /\ 224 < c` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC (1--4)] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REJ_EV_CLOSE_TAC);;

let REJ_EV_LOOP96_EXIT = prove
 (`!res buf buflen table inlist stackpointer pc p c.
     buflen < 2 EXP 64 /\ 24 * p <= buflen /\
     (buflen < 24 * (p + 4) \/ 192 < c)
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x38) /\
                     rej_st res buf buflen table curlist inlist stackpointer
                            p s /\
                     read events s = e)
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x200) /\
                     rej_st res buf buflen table curlist inlist stackpointer
                            p s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stackpointer,48]
                      [stackpointer,48; res,512])
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stackpointer,48)])`,
  let INTRO_TAC =
    REJ_EV_META_TAC THEN
    MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
    REWRITE_TAC[rej_st; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `c < 2 EXP 64 /\ buflen - 24 * p < 2 EXP 64`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPECL [`curlist:int16 list`; `inlist:(12 word)list`; `p:num`]
        LENGTH_REJ_OUT) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY VAL_INT64_TAC [`c:num`; `buflen - 24 * p`] THEN
    SUBGOAL_THEN
     `(192 <= c /\ ~(val(word_sub (word c:int64) (word 192)) = 0)) <=>
      192 < c`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] in
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `buflen < 24 * (p + 4)` THEN INTRO_TAC THENL
   [SUBGOAL_THEN `buflen - 24 * p < 96` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC (1--2);
    SUBGOAL_THEN `~(buflen - 24 * p < 96) /\ 192 < c` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC (1--4)] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REJ_EV_CLOSE_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop by 24 bytes when the accepted numbers are stored directly.       *)
(* ------------------------------------------------------------------------- *)

let REJ_EV_LOOP24_DIRECT = prove
 (`!res buf buflen table inlist stackpointer pc p c.
     8 * buflen = 12 * LENGTH(inlist:(12 word)list) /\ 24 divides buflen /\
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x3d0); (stackpointer,48); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stackpointer,48))
         [(word pc,0x3d0); (buf,buflen); (table,4096)] /\
     24 * (p + 1) <= buflen /\ c <= 240
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x2f0) /\
                     rej_st res buf buflen table curlist inlist stackpointer
                            p s /\
                     read events s = e)
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x2f0) /\
                     rej_st res buf buflen table curlist inlist stackpointer
                            (p + 1) s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stackpointer,48]
                      [stackpointer,48; res,512])
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stackpointer,48)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REJ_EV_META_TAC THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  REWRITE_TAC[rej_st; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_TAC THEN
  ABBREV_TAC `out = rej_out curlist inlist p` THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`] THEN
  ABBREV_TAC
   `ch = word((num_of_wordlist(inlist:(12 word)list) DIV 2 EXP (8 * 24 * p))
              MOD 2 EXP 192):192 word` THEN
  SUBGOAL_THEN
   `!j. j < 16
        ==> EL (16 * p + j) inlist =
            word_subword (ch:192 word) (12 * j,12):12 word`
  (LABEL_TAC "chunk") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "ch" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REJ_CHUNK_EL_192 THEN
    MAP_EVERY UNDISCH_TAC
     [`j < 16`; `8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 1) <= buflen`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(val(word(buflen - 24 * p):int64) < 24)` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o lhand o rand o snd) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c < 2 EXP 64 /\ ~(256 <= c) /\ ~(240 < c) /\ c < 241`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `c:num` THEN
  SUBGOAL_THEN
   `(240 <= c /\ ~(val(word_sub (word c:int64) (word 240)) = 0)) <=> 240 < c`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`buf:int64`; `buflen:num`;
                `num_of_wordlist(inlist:(12 word)list)`;
                `24 * p`; `s0:armstate`] CHUNK_LOADS64) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `24 * (p + 1) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN

  (*** The computation of the two groups ***)

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [n] THEN
                      (if n = 6 then LD3_TAC
                       else SIMD_SIMPLIFY_TAC[rej_mask; rej_gsum]))
            (1--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE REJ_CANDIDATES_192) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[rej_mask; rej_gsum] THEN
                      SCALAR_SIMPLIFY_TAC) (13--22) THEN
  SCALAR_SIMPLIFY_ALL_TAC THEN
  TABLE_ABBREV_TAC "tab0" `X7` THEN TABLE_ABBREV_TAC "tab1" `X9` THEN
  TAB_LOOKUP_TAC `tab0:int128` THEN TAB_LOOKUP_TAC `tab1:int128` THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[rej_mask; rej_gsum]) (23--28) THEN
  SCALAR_SIMPLIFY_ALL_TAC THEN
  GROUP_APPLY_TAC `Q16` THEN GROUP_APPLY_TAC `Q17` THEN
  GROUP_ABBREV_TAC `Q16` "lis0" "len0" THEN
  GROUP_ABBREV_TAC `Q17` "lis1" "len1" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBWORD_84_AS_WORD; REJ_PACK]) THEN
  REWRITE_COUNT_TAC `len0:num` THEN REWRITE_COUNT_TAC `len1:num` THEN

  (*** The stores and the updates of the pointer and count ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC (29--31) THEN
  REJ_STORE_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match []
   `read (memory :> bytes(res,2 * (c + LENGTH(lis0:int16 list)))) s31 = x`) o
   concl)) THEN
  REWRITE_TAC[ASSUME `LENGTH(lis0:int16 list) = len0`] THEN DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [32] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_STEP]) THEN
  SUBGOAL_THEN `c + len0 <= 248` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`c < 241`; `len0 <= 8`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [33] THEN
  REJ_STORE_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [34] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_STEP]) THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC (35--37) THEN

  (*** The new result list ***)

  SUBGOAL_THEN
   `rej_out curlist inlist (p + 1) = APPEND (APPEND out lis0) lis1`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`curlist:int16 list`; `inlist:(12 word)list`; `p:num`; `1`]
      REJ_OUT_STEP) THEN
    REWRITE_TAC[ASSUME `rej_out curlist inlist p = out`;
                ASSUME `LENGTH(out:int16 list) = c`] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `c < 241` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; ARITH_RULE `16 * 1 = 16`] THEN
    AP_TERM_TAC THEN
    REJ_SAMPLE_EXPAND_TAC SUB_LIST_EXPAND_16 ["lis0"; "lis1"] ["chunk"]
     [`8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 1) <= buflen`];
    ALL_TAC] THEN

  (*** The final state ***)

  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[ASSUME
   `rej_out curlist inlist (p + 1) = APPEND (APPEND out lis0) lis1`;
   LENGTH_APPEND] THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`;
              ASSUME `LENGTH(lis0:int16 list) = len0`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    SUBGOAL_THEN `buflen - 24 * p = (buflen - 24 * (p + 1)) + 24`
    SUBST1_TAC THENL
     [UNDISCH_TAC `24 * (p + 1) <= buflen` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    REWRITE_TAC[WORD_ADD];
    REJ_EV_TAC;
    REJ_MI_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The final copy through the buffer on the stack, of the first m of the     *)
(* list L of the accepted numbers from the last 24 bytes: a step back to     *)
(* the start of the copy loop, the last step and the branch back to the      *)
(* loop by 24 bytes.                                                         *)
(* ------------------------------------------------------------------------- *)

let REJ_EV_COPY_STEP = prove
 (`!res buf buflen table inlist stackpointer pc p c L m i.
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x3d0); (stackpointer,48); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stackpointer,48))
         [(word pc,0x3d0); (buf,buflen); (table,4096)] /\
     m <= LENGTH L /\ LENGTH L <= 16 /\ c + m <= 256 /\ i + 1 < m
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x3b0) /\
                     rej_cst res buf buflen table inlist stackpointer p
                             (rej_out curlist inlist p) L m i s /\
                     read events s = e)
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x3b0) /\
                     rej_cst res buf buflen table inlist stackpointer p
                             (rej_out curlist inlist p) L m (i + 1) s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stackpointer,48]
                      [stackpointer,48; res,512])
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stackpointer,48)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REJ_EV_META_TAC THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  REWRITE_TAC[rej_cst; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_TAC THEN
  ABBREV_TAC `out = rej_out curlist inlist p` THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`] THEN
  SUBGOAL_THEN `i < LENGTH(L:int16 list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `m - i < 2 EXP 64 /\ ~(m - i = 0)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `m - i:num` THEN
  SUBGOAL_THEN `~(val(word_sub (word(m - i)) (word 1):int64) = 0)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1;
                    ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    UNDISCH_TAC `i + 1 < m` THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`stackpointer:int64`; `L:int16 list`; `i:num`; `s0:armstate`]
    READ_BYTES16_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC (1--3) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_INC]) THEN
  FIRST_X_ASSUM(MP_TAC o WORD_ZX_ZX_SIMP_RULE o check (can (term_match
    [`res:int64`]
    `read (memory :> bytes16 (word_add res (word (2 * n)))) s3 = x`) o
    concl)) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`res:int64`; `c + i:num`;
                `APPEND out (SUB_LIST(0,i) L):int16 list`;
                `EL i L:int16`; `s3:armstate`] REJ_STORE16) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST; SUB_0] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC(ARITH_RULE `i < l ==> MIN i l = i`) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [4] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[SUB_LIST_SNOC] THEN
  REWRITE_TAC[APPEND_ASSOC; ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `m - (i + 1) = (m - i) - 1` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= n <=> ~(n = 0)`];
    REJ_EV_TAC;
    REJ_MI_TAC]);;

let REJ_EV_COPY_LAST = prove
 (`!res buf buflen table inlist stackpointer pc p c L m i.
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x3d0); (stackpointer,48); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stackpointer,48))
         [(word pc,0x3d0); (buf,buflen); (table,4096)] /\
     m <= LENGTH L /\ LENGTH L <= 16 /\ c + m <= 256 /\ i + 1 = m
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c /\
           rej_out curlist inlist (p + 1) =
           APPEND (rej_out curlist inlist p) (SUB_LIST(0,m) L)
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x3b0) /\
                     rej_cst res buf buflen table inlist stackpointer p
                             (rej_out curlist inlist p) L m i s /\
                     read events s = e)
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x2f0) /\
                     rej_st res buf buflen table curlist inlist stackpointer
                            (p + 1) s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stackpointer,48]
                      [stackpointer,48; res,512])
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stackpointer,48)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REJ_EV_META_TAC THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  REWRITE_TAC[rej_cst; rej_st; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  ABBREV_TAC `out = rej_out curlist inlist p` THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST; SUB_0] THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= l ==> MIN m l = m`] THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> concl th = `i + 1 = m`)) THEN
  SUBGOAL_THEN `i < LENGTH(L:int16 list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(i + 1) - i = 1`] THEN
  SUBGOAL_THEN `val(word_sub (word 1) (word 1):int64) = 0` ASSUME_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`stackpointer:int64`; `L:int16 list`; `i:num`; `s0:armstate`]
    READ_BYTES16_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC (1--3) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_INC]) THEN
  FIRST_X_ASSUM(MP_TAC o WORD_ZX_ZX_SIMP_RULE o check (can (term_match
    [`res:int64`]
    `read (memory :> bytes16 (word_add res (word (2 * n)))) s3 = x`) o
    concl)) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`res:int64`; `c + i:num`;
                `APPEND out (SUB_LIST(0,i) L):int16 list`;
                `EL i L:int16`; `s3:armstate`] REJ_STORE16) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST; SUB_0] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC(ARITH_RULE `i < l ==> MIN i l = i`) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC (4--5) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[SUB_LIST_SNOC] THEN
  REWRITE_TAC[APPEND_ASSOC; ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN
  REJ_EV_CLOSE_TAC);;

(* The entry to the copy loop, the copy loop and the whole final copy        *)

let REJ_EV_COPY_ENTRY = prove
 (`!res buf buflen table inlist stackpointer pc p c L m.
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x3d0); (stackpointer,48); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stackpointer,48))
         [(word pc,0x3d0); (buf,buflen); (table,4096)] /\
     m <= LENGTH L /\ LENGTH L <= 16 /\ c + m <= 256 /\ ~(m = 0)
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x3ac) /\
                     rej_cst res buf buflen table inlist stackpointer p
                             (rej_out curlist inlist p) L m 0 s /\
                     read events s = e)
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x3b0) /\
                     rej_cst res buf buflen table inlist stackpointer p
                             (rej_out curlist inlist p) L m 0 s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stackpointer,48]
                      [stackpointer,48; res,512])
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stackpointer,48)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REJ_EV_META_TAC THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  REWRITE_TAC[rej_cst; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    REWRITE_TAC[th; SUB_0; ADD_CLAUSES; MULT_CLAUSES; SUB_LIST_CLAUSES;
                APPEND_NIL; WORD_ADD_0]) THEN
  SUBGOAL_THEN `m < 2 EXP 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `m:num` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REJ_EV_CLOSE_TAC);;

let REJ_DOWN_INDUCT = prove
 (`!P m. (!i. i + 1 = m ==> P i) /\ (!i. i + 1 < m /\ P(i + 1) ==> P i)
         ==> !i. i < m ==> P i`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "last") (LABEL_TAC "step")) THEN
  SUBGOAL_THEN `!d i. i + d + 1 = m ==> P i` ASSUME_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN USE_THEN "last" MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      X_GEN_TAC `d:num` THEN DISCH_THEN(LABEL_TAC "ih") THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN USE_THEN "step" MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "ih" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `m - i - 1` THEN
    ASM_ARITH_TAC]);;

let REJ_EV_COPY_LOOP = prove
 (`!res buf buflen table inlist stackpointer pc p c L m.
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x3d0); (stackpointer,48); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stackpointer,48))
         [(word pc,0x3d0); (buf,buflen); (table,4096)] /\
     m <= LENGTH L /\ LENGTH L <= 16 /\ c + m <= 256
     ==> !i. i < m
             ==> ?ev. !curlist e.
                   LENGTH(rej_out curlist inlist p) = c /\
                   rej_out curlist inlist (p + 1) =
                   APPEND (rej_out curlist inlist p) (SUB_LIST(0,m) L)
                   ==> ensures arm
                        (\s. aligned_bytes_loaded s (word pc)
                               mlkem_rej_uniform_alt_tmc /\
                             read PC s = word(pc + 0x3b0) /\
                             rej_cst res buf buflen table inlist stackpointer
                                     p (rej_out curlist inlist p) L m i s /\
                             read events s = e)
                        (\s. aligned_bytes_loaded s (word pc)
                               mlkem_rej_uniform_alt_tmc /\
                             read PC s = word(pc + 0x2f0) /\
                             rej_st res buf buflen table curlist inlist
                                    stackpointer (p + 1) s /\
                             read events s = APPEND ev e /\
                             memaccess_inbounds ev
                              [buf,buflen; table,4096; stackpointer,48]
                              [stackpointer,48; res,512])
                        (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                         MAYCHANGE [memory :> bytes(res,512);
                                    memory :> bytes(stackpointer,48)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC REJ_DOWN_INDUCT THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THENL
   [DISCH_TAC THEN MATCH_MP_TAC REJ_EV_COPY_LAST THEN ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_TAC `ev2:(uarch_event)list`))] THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                `inlist:(12 word)list`; `stackpointer:int64`; `pc:num`;
                `p:num`; `c:num`; `L:int16 list`; `m:num`; `i:num`]
    REJ_EV_COPY_STEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `ev1:(uarch_event)list`) THEN
  EXISTS_TAC `APPEND (ev2:(uarch_event)list) ev1` THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  STRIP_TAC THEN MATCH_MP_TAC REJ_EV_SEQ THEN
  MAP_EVERY EXISTS_TAC
   [`0x3b0`;
    `rej_cst res buf buflen table inlist stackpointer p
             (rej_out curlist inlist p) L m (i + 1)`] THEN
  ASM_SIMP_TAC[]);;

let REJ_EV_LASTCOPY = prove
 (`!res buf buflen table inlist stackpointer pc p c L m.
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x3d0); (stackpointer,48); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stackpointer,48))
         [(word pc,0x3d0); (buf,buflen); (table,4096)] /\
     m <= LENGTH L /\ LENGTH L <= 16 /\ c + m <= 256
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c /\
           rej_out curlist inlist (p + 1) =
           APPEND (rej_out curlist inlist p) (SUB_LIST(0,m) L)
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x3ac) /\
                     rej_cst res buf buflen table inlist stackpointer p
                             (rej_out curlist inlist p) L m 0 s /\
                     read events s = e)
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x2f0) /\
                     rej_st res buf buflen table curlist inlist stackpointer
                            (p + 1) s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stackpointer,48]
                      [stackpointer,48; res,512])
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stackpointer,48)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [REJ_EV_META_TAC THEN
    MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
    REWRITE_TAC[rej_cst; rej_st; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                NONOVERLAPPING_CLAUSES; ALL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    ASM_REWRITE_TAC[SUB_0; ADD_CLAUSES; MULT_CLAUSES; SUB_LIST_CLAUSES;
                    APPEND_NIL] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REJ_EV_CLOSE_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                `inlist:(12 word)list`; `stackpointer:int64`; `pc:num`;
                `p:num`; `c:num`; `L:int16 list`; `m:num`]
    REJ_EV_COPY_LOOP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < m <=> ~(m = 0)`] THEN
  DISCH_THEN(X_CHOOSE_TAC `ev2:(uarch_event)list`) THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                `inlist:(12 word)list`; `stackpointer:int64`; `pc:num`;
                `p:num`; `c:num`; `L:int16 list`; `m:num`]
    REJ_EV_COPY_ENTRY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `ev1:(uarch_event)list`) THEN
  EXISTS_TAC `APPEND (ev2:(uarch_event)list) ev1` THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  STRIP_TAC THEN MATCH_MP_TAC REJ_EV_SEQ THEN
  MAP_EVERY EXISTS_TAC
   [`0x3b0`;
    `rej_cst res buf buflen table inlist stackpointer p
             (rej_out curlist inlist p) L m 0`] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The loop by 24 bytes when there may not be room for all 16 numbers: the   *)
(* two groups go to the buffer on the stack, from which as many as there is  *)
(* room for are copied.                                                      *)
(* ------------------------------------------------------------------------- *)

let REJ_EV_LOOP24_HEAD = prove
 (`!res buf buflen table inlist stackpointer pc p c L m.
     8 * buflen = 12 * LENGTH(inlist:(12 word)list) /\ 24 divides buflen /\
     buflen < 2 EXP 64 /\ aligned 16 stackpointer /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x3d0); (stackpointer,48); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stackpointer,48))
         [(word pc,0x3d0); (buf,buflen); (table,4096)] /\
     24 * (p + 1) <= buflen /\ 240 < c /\ c < 256 /\
     REJ_SAMPLE (SUB_LIST(16 * p,16) inlist) = L /\
     MIN (LENGTH L) (256 - c) = m
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x2f0) /\
                     rej_st res buf buflen table curlist inlist stackpointer
                            p s /\
                     read events s = e)
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x3ac) /\
                     rej_cst res buf buflen table inlist stackpointer p
                             (rej_out curlist inlist p) L m 0 s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stackpointer,48]
                      [stackpointer,48; res,512])
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stackpointer,48)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REJ_EV_META_TAC THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  REWRITE_TAC[rej_st; rej_cst; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_TAC THEN
  ABBREV_TAC `out = rej_out curlist inlist p` THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`] THEN
  REWRITE_TAC[SUB_0; ADD_CLAUSES; MULT_CLAUSES; SUB_LIST_CLAUSES; APPEND_NIL;
              WORD_ADD_0] THEN
  ABBREV_TAC
   `ch = word((num_of_wordlist(inlist:(12 word)list) DIV 2 EXP (8 * 24 * p))
              MOD 2 EXP 192):192 word` THEN
  SUBGOAL_THEN
   `!j. j < 16
        ==> EL (16 * p + j) inlist =
            word_subword (ch:192 word) (12 * j,12):12 word`
  (LABEL_TAC "chunk") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "ch" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REJ_CHUNK_EL_192 THEN
    MAP_EVERY UNDISCH_TAC
     [`j < 16`; `8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 1) <= buflen`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(val(word(buflen - 24 * p):int64) < 24)` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o lhand o rand o snd) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c < 2 EXP 64 /\ ~(256 <= c) /\ 240 < c /\ c < 256`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `c:num` THEN
  SUBGOAL_THEN
   `(240 <= c /\ ~(val(word_sub (word c:int64) (word 240)) = 0)) <=> 240 < c`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`buf:int64`; `buflen:num`;
                `num_of_wordlist(inlist:(12 word)list)`;
                `24 * p`; `s0:armstate`] CHUNK_LOADS64) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `24 * (p + 1) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [n] THEN
                      (if n = 6 then LD3_TAC
                       else SIMD_SIMPLIFY_TAC[rej_mask; rej_gsum]))
            (1--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE REJ_CANDIDATES_192) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[rej_mask; rej_gsum] THEN
                      SCALAR_SIMPLIFY_TAC) (13--22) THEN
  SCALAR_SIMPLIFY_ALL_TAC THEN
  TABLE_ABBREV_TAC "tab0" `X7` THEN TABLE_ABBREV_TAC "tab1" `X9` THEN
  TAB_LOOKUP_TAC `tab0:int128` THEN TAB_LOOKUP_TAC `tab1:int128` THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[rej_mask; rej_gsum]) (23--28) THEN
  SCALAR_SIMPLIFY_ALL_TAC THEN
  GROUP_APPLY_TAC `Q16` THEN GROUP_APPLY_TAC `Q17` THEN
  GROUP_ABBREV_TAC `Q16` "lis0" "len0" THEN
  GROUP_ABBREV_TAC `Q17` "lis1" "len1" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBWORD_84_AS_WORD; REJ_PACK]) THEN
  REWRITE_COUNT_TAC `len0:num` THEN REWRITE_COUNT_TAC `len1:num` THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC (29--31) THEN
  MP_TAC(SPECL [`stackpointer:int64`; `lis0:int16 list`; `s31:armstate`]
    REJ_STORE0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [32] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_STEP0]) THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [33] THEN
  REJ_STORE_AT_TAC `stackpointer:int64` THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC (34--38) THEN
  SUBGOAL_THEN `L:int16 list = APPEND lis0 lis1` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    REJ_SAMPLE_EXPAND_TAC SUB_LIST_EXPAND_16 ["lis0"; "lis1"] ["chunk"]
     [`8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 1) <= buflen`];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(L:int16 list) = len0 + len1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match []
    `read X8 s38 = (if a then b else c)`) o concl)) THEN
  MP_TAC(SPECL [`len0:num`; `len1:num`; `c:num`] REJ_CSEL) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`len0 <= 8`; `len1 <= 8`; `c < 256`] THEN
    ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM(ASSUME `LENGTH(L:int16 list) = len0 + len1`)] THEN
  REWRITE_TAC[ASSUME `MIN (LENGTH(L:int16 list)) (256 - c) = m`] THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC (39--40) THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match [`stackpointer:int64`]
    `read (memory :> bytes (stackpointer,n)) s40 =
     num_of_wordlist(APPEND l1 l2)`) o concl)) THEN
  REWRITE_TAC[ASSUME `LENGTH(lis1:int16 list) = len1`] THEN DISCH_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[ASSUME `L:int16 list = APPEND lis0 lis1`; LENGTH_APPEND] THEN
  REWRITE_TAC[ASSUME `LENGTH(lis0:int16 list) = len0`;
              ASSUME `LENGTH(lis1:int16 list) = len1`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    SUBGOAL_THEN `buflen - 24 * p = (buflen - 24 * (p + 1)) + 24`
    SUBST1_TAC THENL
     [UNDISCH_TAC `24 * (p + 1) <= buflen` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    REWRITE_TAC[WORD_ADD];
    REJ_EV_TAC;
    REJ_MI_TAC]);;

let REJ_EV_LOOP24_LAST = prove
 (`!res buf buflen table inlist stackpointer pc p c.
     8 * buflen = 12 * LENGTH(inlist:(12 word)list) /\ 24 divides buflen /\
     buflen < 2 EXP 64 /\ aligned 16 stackpointer /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x3d0); (stackpointer,48); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stackpointer,48))
         [(word pc,0x3d0); (buf,buflen); (table,4096)] /\
     24 * (p + 1) <= buflen /\ 240 < c /\ c < 256
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x2f0) /\
                     rej_st res buf buflen table curlist inlist stackpointer
                            p s /\
                     read events s = e)
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x2f0) /\
                     rej_st res buf buflen table curlist inlist stackpointer
                            (p + 1) s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stackpointer,48]
                      [stackpointer,48; res,512])
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stackpointer,48)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `L = REJ_SAMPLE (SUB_LIST(16 * p,16) (inlist:(12 word)list))` THEN
  ABBREV_TAC `m = MIN (LENGTH(L:int16 list)) (256 - c)` THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                `inlist:(12 word)list`; `stackpointer:int64`; `pc:num`;
                `p:num`; `c:num`; `L:int16 list`; `m:num`]
    REJ_EV_LOOP24_HEAD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `ev1:(uarch_event)list`) THEN
  MP_TAC(ISPECL [`inlist:(12 word)list`; `16 * p`; `16`]
    LENGTH_REJ_SAMPLE_CHUNK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                `inlist:(12 word)list`; `stackpointer:int64`; `pc:num`;
                `p:num`; `c:num`; `L:int16 list`; `m:num`]
    REJ_EV_LASTCOPY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THEN ASM_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `ev2:(uarch_event)list`)] THEN
  EXISTS_TAC `APPEND (ev2:(uarch_event)list) ev1` THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `rej_out curlist inlist (p + 1) =
    APPEND (rej_out curlist inlist p) (SUB_LIST(0,m) L)`
  ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `LENGTH(rej_out curlist inlist p) = c`)) THEN
    MATCH_MP_TAC REJ_OUT_LAST THEN
    ASM_REWRITE_TAC[LENGTH_REJ_OUT];
    ALL_TAC] THEN
  MATCH_MP_TAC REJ_EV_SEQ THEN
  MAP_EVERY EXISTS_TAC
   [`0x3ac`;
    `rej_cst res buf buflen table inlist stackpointer p
             (rej_out curlist inlist p) L m 0`] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The loop by 48 bytes, the 32 numbers stored directly.                     *)
(* ------------------------------------------------------------------------- *)

let REJ_EV_LOOP48_BODY = prove
 (`!res buf buflen table inlist stackpointer pc p c.
     8 * buflen = 12 * LENGTH(inlist:(12 word)list) /\ 24 divides buflen /\
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x3d0); (stackpointer,48); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stackpointer,48))
         [(word pc,0x3d0); (buf,buflen); (table,4096)] /\
     24 * (p + 2) <= buflen /\ c <= 224
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x200) /\
                     rej_st res buf buflen table curlist inlist stackpointer
                            p s /\
                     read events s = e)
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x38) /\
                     rej_st res buf buflen table curlist inlist stackpointer
                            (p + 2) s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stackpointer,48]
                      [stackpointer,48; res,512])
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stackpointer,48)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REJ_EV_META_TAC THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  REWRITE_TAC[rej_st; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_TAC THEN
  ABBREV_TAC `out = rej_out curlist inlist p` THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`] THEN
  ABBREV_TAC
   `ch = word((num_of_wordlist(inlist:(12 word)list) DIV 2 EXP (8 * 24 * p))
              MOD 2 EXP 384):384 word` THEN
  SUBGOAL_THEN
   `!j. j < 32
        ==> EL (16 * p + j) inlist =
            word_subword (ch:384 word) (12 * j,12):12 word`
  (LABEL_TAC "chunk") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "ch" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REJ_CHUNK_EL_384 THEN
    MAP_EVERY UNDISCH_TAC
     [`j < 32`; `8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 2) <= buflen`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(val(word(buflen - 24 * p):int64) < 48)` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o lhand o rand o snd) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c < 2 EXP 64 /\ ~(224 < c) /\ c < 225`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `c:num` THEN
  SUBGOAL_THEN
   `(224 <= c /\ ~(val(word_sub (word c:int64) (word 224)) = 0)) <=> 224 < c`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`buf:int64`; `buflen:num`;
                `num_of_wordlist(inlist:(12 word)list)`;
                `24 * p`; `s0:armstate`] CHUNK_LOADS128) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `24 * (p + 2) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [n] THEN
                      (if n = 6 then LD3_TAC
                       else SIMD_SIMPLIFY_TAC[rej_mask; rej_gsum]))
            (1--18) THEN
  RULE_ASSUM_TAC(REWRITE_RULE REJ_CANDIDATES_384) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[rej_mask; rej_gsum] THEN
                      SCALAR_SIMPLIFY_TAC) (19--35) THEN
  SCALAR_SIMPLIFY_ALL_TAC THEN
  TABLE_ABBREV_TAC "tab0" `X7` THEN TABLE_ABBREV_TAC "tab1" `X9` THEN
  TABLE_ABBREV_TAC "tab2" `X11` THEN TABLE_ABBREV_TAC "tab3" `X13` THEN
  TAB_LOOKUP_TAC `tab0:int128` THEN TAB_LOOKUP_TAC `tab1:int128` THEN
  TAB_LOOKUP_TAC `tab2:int128` THEN TAB_LOOKUP_TAC `tab3:int128` THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[rej_mask; rej_gsum]) (36--47) THEN
  SCALAR_SIMPLIFY_ALL_TAC THEN
  GROUP_APPLY_TAC `Q16` THEN GROUP_APPLY_TAC `Q17` THEN
  GROUP_APPLY_TAC `Q18` THEN GROUP_APPLY_TAC `Q19` THEN
  GROUP_ABBREV_TAC `Q16` "lis0" "len0" THEN
  GROUP_ABBREV_TAC `Q17` "lis1" "len1" THEN
  GROUP_ABBREV_TAC `Q18` "lis2" "len2" THEN
  GROUP_ABBREV_TAC `Q19` "lis3" "len3" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBWORD_84_AS_WORD; REJ_PACK]) THEN
  REWRITE_COUNT_TAC `len0:num` THEN REWRITE_COUNT_TAC `len1:num` THEN
  REWRITE_COUNT_TAC `len2:num` THEN REWRITE_COUNT_TAC `len3:num` THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [48] THEN REJ_STORE_LEN_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [49] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_STEP]) THEN
  SUBGOAL_THEN `c + len0 <= 248` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`c < 225`; `len0 <= 8`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [50] THEN REJ_STORE_LEN_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [51] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_STEP]) THEN
  SUBGOAL_THEN `(c + len0) + len1 <= 248` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`c < 225`; `len0 <= 8`; `len1 <= 8`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [52] THEN REJ_STORE_LEN_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [53] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_STEP]) THEN
  SUBGOAL_THEN `((c + len0) + len1) + len2 <= 248` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`c < 225`; `len0 <= 8`; `len1 <= 8`; `len2 <= 8`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [54] THEN REJ_STORE_LEN_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [55] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_STEP]) THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC (56--60) THEN
  SUBGOAL_THEN
   `rej_out curlist inlist (p + 2) =
    APPEND (APPEND (APPEND (APPEND out lis0) lis1) lis2) lis3`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`curlist:int16 list`; `inlist:(12 word)list`; `p:num`; `2`]
      REJ_OUT_STEP) THEN
    REWRITE_TAC[ASSUME `rej_out curlist inlist p = out`;
                ASSUME `LENGTH(out:int16 list) = c`] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `c < 225` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; ARITH_RULE `16 * 2 = 32`] THEN
    AP_TERM_TAC THEN
    REJ_SAMPLE_EXPAND_TAC SUB_LIST_EXPAND_32
     ["lis0"; "lis1"; "lis2"; "lis3"] ["chunk"]
     [`8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 2) <= buflen`];
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[ASSUME
   `rej_out curlist inlist (p + 2) =
    APPEND (APPEND (APPEND (APPEND out lis0) lis1) lis2) lis3`;
   LENGTH_APPEND] THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`;
              ASSUME `LENGTH(lis0:int16 list) = len0`;
              ASSUME `LENGTH(lis1:int16 list) = len1`;
              ASSUME `LENGTH(lis2:int16 list) = len2`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    SUBGOAL_THEN `buflen - 24 * p = (buflen - 24 * (p + 2)) + 48`
    SUBST1_TAC THENL
     [UNDISCH_TAC `24 * (p + 2) <= buflen` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    REJ_EV_TAC;
    REJ_MI_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The loop by 96 bytes, two chunks of 48 bytes interleaved, the 64 numbers  *)
(* stored directly.                                                          *)
(* ------------------------------------------------------------------------- *)

let REJ_EV_LOOP96_BODY = prove
 (`!res buf buflen table inlist stackpointer pc p c.
     8 * buflen = 12 * LENGTH(inlist:(12 word)list) /\ 24 divides buflen /\
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x3d0); (stackpointer,48); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stackpointer,48))
         [(word pc,0x3d0); (buf,buflen); (table,4096)] /\
     24 * (p + 4) <= buflen /\ c <= 192
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x38) /\
                     rej_st res buf buflen table curlist inlist stackpointer
                            p s /\
                     read events s = e)
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x38) /\
                     rej_st res buf buflen table curlist inlist stackpointer
                            (p + 4) s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stackpointer,48]
                      [stackpointer,48; res,512])
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stackpointer,48)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REJ_EV_META_TAC THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  REWRITE_TAC[rej_st; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_TAC THEN
  ABBREV_TAC `out = rej_out curlist inlist p` THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`] THEN
  ABBREV_TAC
   `ch0 = word((num_of_wordlist(inlist:(12 word)list) DIV 2 EXP (8 * 24 * p))
               MOD 2 EXP 384):384 word` THEN
  ABBREV_TAC
   `ch1 = word((num_of_wordlist(inlist:(12 word)list) DIV
                2 EXP (8 * (24 * p + 48))) MOD 2 EXP 384):384 word` THEN
  SUBGOAL_THEN
   `!j. j < 32
        ==> EL (16 * p + j) inlist =
            word_subword (ch0:384 word) (12 * j,12):12 word`
  (LABEL_TAC "chunk0") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "ch0" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REJ_CHUNK_EL_384 THEN
    MAP_EVERY UNDISCH_TAC
     [`j < 32`; `8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 4) <= buflen`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < 32
        ==> EL (16 * p + 32 + j) inlist =
            word_subword (ch1:384 word) (12 * j,12):12 word`
  (LABEL_TAC "chunk1") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "ch1" THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[ARITH_RULE `8 * (24 * p + 48) = 8 * 24 * (p + 2)`;
                ARITH_RULE `16 * p + 32 + j = 16 * (p + 2) + j`] THEN
    MATCH_MP_TAC REJ_CHUNK_EL_384 THEN
    MAP_EVERY UNDISCH_TAC
     [`j < 32`; `8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 4) <= buflen`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(val(word(buflen - 24 * p):int64) < 96)` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o lhand o rand o snd) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c < 2 EXP 64 /\ ~(192 < c) /\ c < 193`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `c:num` THEN
  SUBGOAL_THEN
   `(192 <= c /\ ~(val(word_sub (word c:int64) (word 192)) = 0)) <=> 192 < c`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`buf:int64`; `buflen:num`;
                `num_of_wordlist(inlist:(12 word)list)`;
                `24 * p`; `s0:armstate`] CHUNK_LOADS128) THEN
  MP_TAC(SPECL [`buf:int64`; `buflen:num`;
                `num_of_wordlist(inlist:(12 word)list)`;
                `24 * p + 48`; `s0:armstate`] CHUNK_LOADS128) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `24 * (p + 4) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    REWRITE_CONV[GSYM ADD_ASSOC] THENC ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `24 * (p + 4) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
  W(fun (asl,w) ->
    let ths = filter (fun th ->
      can (find_term ((=) `ch1:384 word`)) (rand(concl th)) &&
      can (term_match [] `read (memory :> bytes128 a) s = (y:int128)`)
          (concl th))
      (map snd asl) in
    MAP_EVERY (ASSUME_TAC o REWRITE_RULE[WORD_ADD_SPLIT_OFFSET]) ths) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [n] THEN
                      (if n = 6 || n = 7 then LD3_TAC
                       else SIMD_SIMPLIFY_TAC[rej_mask; rej_gsum]))
            (1--7) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[rej_mask; rej_gsum])
            (8--31) THEN
  RULE_ASSUM_TAC(REWRITE_RULE REJ_CANDIDATES_384) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[rej_mask; rej_gsum] THEN
                      SCALAR_SIMPLIFY_TAC) (32--61) THEN
  SCALAR_SIMPLIFY_ALL_TAC THEN
  TABLE_ABBREV_TAC "tab0" `X7` THEN TABLE_ABBREV_TAC "tab1" `X9` THEN
  TABLE_ABBREV_TAC "tab2" `X11` THEN TABLE_ABBREV_TAC "tab3" `X13` THEN
  TAB_LOOKUP_TAC `tab0:int128` THEN TAB_LOOKUP_TAC `tab1:int128` THEN
  TAB_LOOKUP_TAC `tab2:int128` THEN TAB_LOOKUP_TAC `tab3:int128` THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[rej_mask; rej_gsum] THEN
                      SCALAR_SIMPLIFY_TAC) (62--69) THEN
  SCALAR_SIMPLIFY_ALL_TAC THEN
  TABLE_ABBREV_TAC "tab4" `X7` THEN TABLE_ABBREV_TAC "tab5" `X9` THEN
  TABLE_ABBREV_TAC "tab6" `X11` THEN TABLE_ABBREV_TAC "tab7" `X13` THEN
  TAB_LOOKUP_TAC `tab4:int128` THEN TAB_LOOKUP_TAC `tab5:int128` THEN
  TAB_LOOKUP_TAC `tab6:int128` THEN TAB_LOOKUP_TAC `tab7:int128` THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[rej_mask; rej_gsum]) (70--85) THEN
  SCALAR_SIMPLIFY_ALL_TAC THEN
  GROUP_APPLY_TAC `Q0` THEN GROUP_APPLY_TAC `Q1` THEN
  GROUP_APPLY_TAC `Q2` THEN GROUP_APPLY_TAC `Q18` THEN
  GROUP_APPLY_TAC `Q3` THEN GROUP_APPLY_TAC `Q4` THEN
  GROUP_APPLY_TAC `Q5` THEN GROUP_APPLY_TAC `Q23` THEN
  GROUP_ABBREV_TAC `Q0` "lis0" "len0" THEN
  GROUP_ABBREV_TAC `Q1` "lis1" "len1" THEN
  GROUP_ABBREV_TAC `Q2` "lis2" "len2" THEN
  GROUP_ABBREV_TAC `Q18` "lis3" "len3" THEN
  GROUP_ABBREV_TAC `Q3` "lis4" "len4" THEN
  GROUP_ABBREV_TAC `Q4` "lis5" "len5" THEN
  GROUP_ABBREV_TAC `Q5` "lis6" "len6" THEN
  GROUP_ABBREV_TAC `Q23` "lis7" "len7" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBWORD_84_AS_WORD; REJ_PACK]) THEN
  REWRITE_COUNT_TAC `len0:num` THEN REWRITE_COUNT_TAC `len1:num` THEN
  REWRITE_COUNT_TAC `len2:num` THEN REWRITE_COUNT_TAC `len3:num` THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [86] THEN REJ_STORE_LEN_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [87] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_STEP]) THEN
  REJ_BOUND_TAC `c + len0 <= 248` THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [88] THEN REJ_STORE_LEN_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [89] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_STEP]) THEN
  REJ_BOUND_TAC `(c + len0) + len1 <= 248` THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [90] THEN REJ_STORE_LEN_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [91] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_STEP]) THEN
  REJ_BOUND_TAC `((c + len0) + len1) + len2 <= 248` THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [92] THEN REJ_STORE_LEN_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [93] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_STEP]) THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC (94--101) THEN
  SCALAR_SIMPLIFY_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBWORD_84_AS_WORD]) THEN
  REWRITE_COUNT_TAC `len4:num` THEN REWRITE_COUNT_TAC `len5:num` THEN
  REWRITE_COUNT_TAC `len6:num` THEN REWRITE_COUNT_TAC `len7:num` THEN
  REJ_BOUND_TAC `(((c + len0) + len1) + len2) + len3 <= 248` THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [102] THEN REJ_STORE_LEN_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [103] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_STEP]) THEN
  REJ_BOUND_TAC `((((c + len0) + len1) + len2) + len3) + len4 <= 248` THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [104] THEN REJ_STORE_LEN_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [105] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_STEP]) THEN
  REJ_BOUND_TAC
   `(((((c + len0) + len1) + len2) + len3) + len4) + len5 <= 248` THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [106] THEN REJ_STORE_LEN_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [107] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_STEP]) THEN
  REJ_BOUND_TAC
   `((((((c + len0) + len1) + len2) + len3) + len4) + len5) + len6 <= 248` THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [108] THEN REJ_STORE_LEN_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [109] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_STEP]) THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC (110--114) THEN
  SUBGOAL_THEN
   `rej_out curlist inlist (p + 4) =
    APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND out
      lis0) lis1) lis2) lis3) lis4) lis5) lis6) lis7`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`curlist:int16 list`; `inlist:(12 word)list`; `p:num`; `4`]
      REJ_OUT_STEP) THEN
    REWRITE_TAC[ASSUME `rej_out curlist inlist p = out`;
                ASSUME `LENGTH(out:int16 list) = c`] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `c < 193` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; ARITH_RULE `16 * 4 = 64`] THEN
    AP_TERM_TAC THEN
    REJ_SAMPLE_EXPAND_TAC SUB_LIST_EXPAND_64
     ["lis0"; "lis1"; "lis2"; "lis3"; "lis4"; "lis5"; "lis6"; "lis7"]
     ["chunk0"; "chunk1"]
     [`8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 4) <= buflen`];
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[ASSUME
   `rej_out curlist inlist (p + 4) =
    APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND out
      lis0) lis1) lis2) lis3) lis4) lis5) lis6) lis7`;
   LENGTH_APPEND] THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`;
              ASSUME `LENGTH(lis0:int16 list) = len0`;
              ASSUME `LENGTH(lis1:int16 list) = len1`;
              ASSUME `LENGTH(lis2:int16 list) = len2`;
              ASSUME `LENGTH(lis3:int16 list) = len3`;
              ASSUME `LENGTH(lis4:int16 list) = len4`;
              ASSUME `LENGTH(lis5:int16 list) = len5`;
              ASSUME `LENGTH(lis6:int16 list) = len6`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    SUBGOAL_THEN `buflen - 24 * p = (buflen - 24 * (p + 4)) + 96`
    SUBST1_TAC THENL
     [UNDISCH_TAC `24 * (p + 4) <= buflen` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    REJ_EV_TAC;
    REJ_MI_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The loops as a whole, by induction on the number of chunks of 24 bytes    *)
(* left, ending at the label of the end. The events of each stage are those  *)
(* of the block taken, determined by the public values and the count         *)
(* rej_len k inlist p for an initial list of length k, followed by those of  *)
(* the rest.                                                                 *)
(* ------------------------------------------------------------------------- *)

(* The events of a block followed by those of the rest, ev1 and ev2 in the   *)
(* assumptions, with the intermediate label and state.                       *)

let REJ_EV_SEQ_TAC off q =
  EXISTS_TAC `APPEND (ev2:(uarch_event)list) ev1` THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  DISCH_TAC THEN MATCH_MP_TAC REJ_EV_SEQ THEN
  MAP_EVERY EXISTS_TAC [off; q] THEN
  ASM_SIMP_TAC[LENGTH_REJ_OUT_LEN];;

let REJ_EV_LOOP24_ALL = prove
 (`!res buf buflen table inlist stackpointer pc t k p.
     8 * buflen = 12 * LENGTH(inlist:(12 word)list) /\ buflen = 24 * t /\
     buflen < 2 EXP 64 /\ aligned 16 stackpointer /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x3d0); (stackpointer,48); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stackpointer,48))
         [(word pc,0x3d0); (buf,buflen); (table,4096)] /\
     p <= t
     ==> ?ev. !curlist e.
           LENGTH curlist = k
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x2f0) /\
                     rej_st res buf buflen table curlist inlist stackpointer
                            p s /\
                     read events s = e)
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_rej_uniform_alt_tmc /\
                     read PC s = word(pc + 0x3c4) /\
                     rej_end res buf buflen table curlist inlist
                             stackpointer s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stackpointer,48]
                      [stackpointer,48; res,512])
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stackpointer,48)])`,
  let EXIT_TAC =
    MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                  `inlist:(12 word)list`; `stackpointer:int64`; `pc:num`;
                  `p:num`; `rej_len k (inlist:(12 word)list) p`]
      REJ_EV_LOOP24_EXIT) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `ev1:(uarch_event)list`) THEN
    EXISTS_TAC `ev1:(uarch_event)list` THEN
    MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LENGTH_REJ_OUT_LEN] in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; LE_EXISTS] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` MP_TAC) THEN
  SUBGOAL_THEN `24 divides buflen` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MESON_TAC[DIVIDES_RMUL; DIVIDES_REFL]; ALL_TAC] THEN
  UNDISCH_TAC `buflen = 24 * t` THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  SPEC_TAC(`p:num`,`p:num`) THEN SPEC_TAC(`d:num`,`d:num`) THEN
  INDUCT_TAC THEN X_GEN_TAC `p:num` THEN DISCH_TAC THENL
   [EXIT_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `256 <= rej_len k (inlist:(12 word)list) p` THENL
   [EXIT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p + 1` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `ev2:(uarch_event)list`) THEN
  ASM_CASES_TAC `rej_len k (inlist:(12 word)list) p <= 240` THENL
   [MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                  `inlist:(12 word)list`; `stackpointer:int64`; `pc:num`;
                  `p:num`; `rej_len k (inlist:(12 word)list) p`]
      REJ_EV_LOOP24_DIRECT);
    MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                  `inlist:(12 word)list`; `stackpointer:int64`; `pc:num`;
                  `p:num`; `rej_len k (inlist:(12 word)list) p`]
      REJ_EV_LOOP24_LAST)] THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_TAC `ev1:(uarch_event)list`) THEN
   REJ_EV_SEQ_TAC `0x2f0`
    `rej_st res buf buflen table curlist inlist stackpointer (p + 1)`));;

let REJ_EV_LOOP96_ALL = prove
 (`!res buf buflen table inlist stackpointer pc t k p.
     8 * buflen = 12 * LENGTH(inlist:(12 word)list) /\ buflen = 24 * t /\
     buflen < 2 EXP 64 /\ aligned 16 stackpointer /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x3d0); (stackpointer,48); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stackpointer,48))
         [(word pc,0x3d0); (buf,buflen); (table,4096)] /\
     p <= t
     ==> (?ev. !curlist e.
            LENGTH curlist = k
            ==> ensures arm
                 (\s. aligned_bytes_loaded s (word pc)
                        mlkem_rej_uniform_alt_tmc /\
                      read PC s = word(pc + 0x200) /\
                      rej_st res buf buflen table curlist inlist stackpointer
                             p s /\
                      read events s = e)
                 (\s. aligned_bytes_loaded s (word pc)
                        mlkem_rej_uniform_alt_tmc /\
                      read PC s = word(pc + 0x3c4) /\
                      rej_end res buf buflen table curlist inlist
                              stackpointer s /\
                      read events s = APPEND ev e /\
                      memaccess_inbounds ev
                       [buf,buflen; table,4096; stackpointer,48]
                       [stackpointer,48; res,512])
                 (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                  MAYCHANGE [memory :> bytes(res,512);
                             memory :> bytes(stackpointer,48)])) /\
         (?ev. !curlist e.
            LENGTH curlist = k
            ==> ensures arm
                 (\s. aligned_bytes_loaded s (word pc)
                        mlkem_rej_uniform_alt_tmc /\
                      read PC s = word(pc + 0x38) /\
                      rej_st res buf buflen table curlist inlist stackpointer
                             p s /\
                      read events s = e)
                 (\s. aligned_bytes_loaded s (word pc)
                        mlkem_rej_uniform_alt_tmc /\
                      read PC s = word(pc + 0x3c4) /\
                      rej_end res buf buflen table curlist inlist
                              stackpointer s /\
                      read events s = APPEND ev e /\
                      memaccess_inbounds ev
                       [buf,buflen; table,4096; stackpointer,48]
                       [stackpointer,48; res,512])
                 (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                  MAYCHANGE [memory :> bytes(res,512);
                             memory :> bytes(stackpointer,48)]))`,
  let BLOCK_TAC th =
    MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                  `inlist:(12 word)list`; `stackpointer:int64`; `pc:num`;
                  `p:num`; `rej_len k (inlist:(12 word)list) p`] th) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `ev1:(uarch_event)list`)
  and IND_TAC n =
    FIRST_X_ASSUM(MP_TAC o SPEC (mk_binop `(-):num->num->num`
                                   `d:num` (mk_small_numeral n)) o
                  check (is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC (mk_binop `(+):num->num->num`
                                `p:num` (mk_small_numeral n))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `ev2:(uarch_event)list` o CONJUNCT2) in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; LE_EXISTS] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` MP_TAC) THEN
  SUBGOAL_THEN `24 divides buflen` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MESON_TAC[DIVIDES_RMUL; DIVIDES_REFL]; ALL_TAC] THEN
  SPEC_TAC(`p:num`,`p:num`) THEN SPEC_TAC(`d:num`,`d:num`) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN

  (*** The loop by 48 bytes, going to the loop by 24 bytes or back ***)

  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_CASES_TAC
     `buflen < 24 * (p + 2) \/ 224 < rej_len k (inlist:(12 word)list) p`
    THENL
     [MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                    `inlist:(12 word)list`; `stackpointer:int64`; `pc:num`;
                    `t:num`; `k:num`; `p:num`] REJ_EV_LOOP24_ALL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `ev2:(uarch_event)list`) THEN
      BLOCK_TAC REJ_EV_LOOP48_EXIT THEN
      REJ_EV_SEQ_TAC `0x2f0`
       `rej_st res buf buflen table curlist inlist stackpointer p`;
      IND_TAC 2 THEN BLOCK_TAC REJ_EV_LOOP48_BODY THEN
      REJ_EV_SEQ_TAC `0x38`
       `rej_st res buf buflen table curlist inlist stackpointer (p + 2)`];
    DISCH_THEN(X_CHOOSE_TAC `ev2:(uarch_event)list`)] THEN

  (*** The loop by 96 bytes, going to the loop by 48 bytes or back ***)

  ASM_CASES_TAC
   `buflen < 24 * (p + 4) \/ 192 < rej_len k (inlist:(12 word)list) p`
  THENL
   [BLOCK_TAC REJ_EV_LOOP96_EXIT THEN
    REJ_EV_SEQ_TAC `0x200`
     `rej_st res buf buflen table curlist inlist stackpointer p`;
    FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
      can (term_match [] `!curlist e. LENGTH curlist = k ==> P curlist e`)
          (concl th))) THEN
    IND_TAC 4 THEN BLOCK_TAC REJ_EV_LOOP96_BODY THEN
    REJ_EV_SEQ_TAC `0x38`
     `rej_st res buf buflen table curlist inlist stackpointer (p + 4)`]);;

(* ------------------------------------------------------------------------- *)
(* The core, from the first instruction after the stack adjustment to the    *)
(* last before the return, with the result and the events for some list      *)
(* depending only on the public values, then as a function of them, and      *)
(* the events alone.                                                         *)
(* ------------------------------------------------------------------------- *)

let REJ_FULL_CORE0 = prove
 (`!res n buf buflen table (inlist:(12 word)list) pc stackpointer.
      aligned 16 stackpointer /\
      24 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      val n <= 256 /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x3d0); (stackpointer,48); (buf,val buflen);
           (table,4096)] /\
      ALL (nonoverlapping (stackpointer,48))
          [(word pc,0x3d0); (buf,val buflen); (table,4096)]
      ==> ?ev. !e (curlist:int16 list).
            LENGTH curlist = val n
            ==> ensures arm
                 (\s. aligned_bytes_loaded s (word pc)
                        mlkem_rej_uniform_alt_tmc /\
                      read PC s = word(pc + 0x4) /\
                      read SP s = stackpointer /\
                      C_ARGUMENTS [res; n; buf; buflen; table] s /\
                      wordlist_from_memory(table,4096) s =
                      mlkem_rej_uniform_table /\
                      wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                      wordlist_from_memory(res,val n) s = curlist /\
                      read events s = e)
                 (\s. read PC s = word(pc + 0x3c8) /\
                      (let inlist' = MAP (word_zx:12 word->16 word) inlist in
                       let outlist =
                         SUB_LIST (0,256)
                          (APPEND curlist
                                  (FILTER (\x. val x < 3329) inlist')) in
                       let outlen = LENGTH outlist in
                       C_RETURN s = word outlen /\
                       wordlist_from_memory(res,outlen) s = outlist) /\
                      (exists e2.
                           read events s = APPEND e2 e /\
                           e2 = ev /\
                           memaccess_inbounds e2
                             [buf,val buflen; table,4096; stackpointer,48]
                             [stackpointer,48; res,512]))
                 (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                  MAYCHANGE [events] ,,
                  MAYCHANGE [memory :> bytes(res,512);
                             memory :> bytes(stackpointer,48)])`,
  MAP_EVERY X_GEN_TAC [`res:int64`; `n:int64`; `buf:int64`] THEN
  W64_GEN_TAC `buflen:num` THEN
  MAP_EVERY X_GEN_TAC
   [`table:int64`; `inlist:(12 word)list`; `pc:num`;
    `stackpointer:int64`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `t:num` (ASSUME_TAC o SYM) o
    REWRITE_RULE[divides] o
    check (fun th -> concl th = `24 divides buflen`)) THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                `inlist:(12 word)list`; `stackpointer:int64`; `pc:num`;
                `t:num`; `val(n:int64)`; `0`] REJ_EV_LOOP96_ALL) THEN
  ASM_REWRITE_TAC[LE_0] THEN
  DISCH_THEN(X_CHOOSE_TAC `ev:(uarch_event)list` o CONJUNCT2) THEN
  EXISTS_TAC `ev:(uarch_event)list` THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `curlist:int16 list`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o
    SPECL [`curlist:int16 list`; `e:(uarch_event)list`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC
   `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [memory :> bytes(res,512);
               memory :> bytes(stackpointer,48)]` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN] THEN
  MP_TAC(ISPECL
   [`table:int64`; `4096`; `4096`; `mlkem_rej_uniform_table`]
   (INST_TYPE [`:8`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  REWRITE_TAC[DIMINDEX_8] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL
   [`buf:int64`; `LENGTH(inlist:(12 word)list)`;
    `buflen:num`; `inlist:(12 word)list`]
   (INST_TYPE [`:12`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  ASM_REWRITE_TAC[DIMINDEX_CONV `dimindex(:12)`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL
   [`res:int64`; `val(n:int64)`; `2 * val(n:int64)`; `curlist:int16 list`]
   (INST_TYPE [`:16`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * n = 8 * 2 * n`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x3c4`
   `\s. rej_end res buf buflen table curlist inlist stackpointer s /\
        read events s = APPEND ev e /\
        memaccess_inbounds ev
         [buf,buflen; table,4096; stackpointer,48]
         [stackpointer,48; res,512]` THEN
  CONJ_TAC THENL
   [ENSURES_SEQUENCE_TAC `pc + 0x38`
     `\s. rej_st res buf buflen table curlist inlist stackpointer 0 s /\
          read events s = e` THEN
    CONJ_TAC THENL
     [(*** The setup ***)

      REWRITE_TAC[rej_st] THEN
      ASM_SIMP_TAC[REJ_OUT_0; LE_REFL] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; WORD_VAL] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC (1--13) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_SHL1_VAL];

      (*** The loops ***)

      FIRST_X_ASSUM(MP_TAC o
        check (fun th -> can (find_term ((=) `rej_end`)) (concl th))) THEN
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]];

    (*** The end, with the result as in MLKEM_REJ_UNIFORM_ALT_CORE ***)

    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[rej_end; rej_st] THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC o
                  check (is_exists o concl)) THEN
    MP_TAC(SPECL [`curlist:int16 list`; `inlist:(12 word)list`; `buflen:num`;
                  `q:num`] REJ_OUT_FINAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[GSYM REJ_SAMPLE] THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `rej_out a b c = SUB_LIST(0,256) l`) (concl th)
      then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    MP_TAC(ISPECL
     [`res:int64`; `LENGTH(rej_out curlist inlist q)`;
      `2 * LENGTH(rej_out curlist inlist q)`; `rej_out curlist inlist q`]
     (INST_TYPE [`:16`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
    REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * n = 8 * 2 * n`] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `ev:(uarch_event)list` THEN ASM_REWRITE_TAC[]]);;

let MLKEM_REJ_UNIFORM_ALT_CORE_FULL = prove
 (`exists f_events.
     forall e res n buf buflen table (curlist:int16 list)
            (inlist:(12 word)list) pc stackpointer.
      aligned 16 stackpointer /\
      24 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      LENGTH curlist = val n /\ val n <= 256 /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x3d0); (stackpointer,48); (buf,val buflen);
           (table,4096)] /\
      ALL (nonoverlapping (stackpointer,48))
          [(word pc,0x3d0); (buf,val buflen); (table,4096)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_tmc /\
                read PC s = word(pc + 0x4) /\
                read SP s = stackpointer /\
                C_ARGUMENTS [res; n; buf; buflen; table] s /\
                wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                wordlist_from_memory(res,val n) s = curlist /\
                read events s = e)
           (\s. read PC s = word(pc + 0x3c8) /\
                (let inlist' = MAP (word_zx:12 word->16 word) inlist in
                 let outlist =
                   SUB_LIST (0,256)
                    (APPEND curlist (FILTER (\x. val x < 3329) inlist')) in
                 let outlen = LENGTH outlist in
                 C_RETURN s = word outlen /\
                 wordlist_from_memory(res,outlen) s = outlist) /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events res n buf buflen table inlist pc
                                   stackpointer /\
                     memaccess_inbounds e2
                       [buf,val buflen; table,4096; stackpointer,48]
                       [stackpointer,48; res,512]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(stackpointer,48)])`,
  MP_TAC(REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] REJ_FULL_CORE0) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `res:int64`; `n:int64`; `buf:int64`;
    `buflen:int64`; `table:int64`; `curlist:int16 list`;
    `inlist:(12 word)list`; `pc:num`; `stackpointer:int64`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`res:int64`; `n:int64`; `buf:int64`; `buflen:int64`; `table:int64`;
    `inlist:(12 word)list`; `pc:num`; `stackpointer:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`e:(uarch_event)list`; `curlist:int16 list`]) THEN
  ASM_REWRITE_TAC[]);;

let MLKEM_REJ_UNIFORM_ALT_CORE_EVENTS = prove
 (`exists f_events.
     forall e res n buf buflen table (curlist:int16 list)
            (inlist:(12 word)list) pc stackpointer.
      aligned 16 stackpointer /\
      24 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      LENGTH curlist = val n /\ val n <= 256 /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x3d0); (stackpointer,48); (buf,val buflen);
           (table,4096)] /\
      ALL (nonoverlapping (stackpointer,48))
          [(word pc,0x3d0); (buf,val buflen); (table,4096)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_tmc /\
                read PC s = word(pc + 0x4) /\
                read SP s = stackpointer /\
                C_ARGUMENTS [res; n; buf; buflen; table] s /\
                wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                wordlist_from_memory(res,val n) s = curlist /\
                read events s = e)
           (\s. read PC s = word(pc + 0x3c8) /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events res n buf buflen table inlist pc
                                   stackpointer /\
                     memaccess_inbounds e2
                       [buf,val buflen; table,4096; stackpointer,48]
                       [stackpointer,48; res,512]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(stackpointer,48)])`,
  MP_TAC MLKEM_REJ_UNIFORM_ALT_CORE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  DISCH_THEN(ENSURES_WEAKEN_POST_TAC) THEN
  GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, the events of the core and the return added; the    *)
(* event list e comes first in the core and the form without BTI, as needed  *)
(* for ARM_ADD_RETURN_STACK_TAC.                                             *)
(*                                                                           *)
(* The events f_events res n buf buflen table inlist pc sp ra, for the       *)
(* stack pointer sp after the adjustment, are the jump of the return after   *)
(* the events of the blocks on the path through the loops, which is fixed    *)
(* by val buflen, val n and inlist: the jumps of the loop tests, the loads   *)
(* from buf + 24 * p and from the table at 16 times the index of each group  *)
(* of 8 candidates, the stores to res + 2 * c for the count c so far and,    *)
(* for the last chunk, the stores to the buffer at sp and the copy from it.  *)
(* ------------------------------------------------------------------------- *)

let MLKEM_REJ_UNIFORM_ALT_NOIBT_SUBROUTINE_EVENTS = time prove
 (`exists f_events.
     forall e res n buf buflen table (curlist:int16 list)
            (inlist:(12 word)list) pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      24 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      LENGTH curlist = val n /\ val n <= 256 /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x3d0); (word_sub stackpointer (word 48),48);
           (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,0x3d0); (buf,val buflen); (table,4096)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_tmc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [res; n; buf; buflen; table] s /\
                wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                wordlist_from_memory(res,val n) s = curlist /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events res n buf buflen table inlist pc
                                   (word_sub stackpointer (word 48))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [buf,val buflen; table,4096;
                        word_sub stackpointer (word 48),48]
                       [word_sub stackpointer (word 48),48; res,512]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  let TWEAK_CONV =
    TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[wordlist_from_memory] in
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC MLKEM_REJ_UNIFORM_ALT_EXEC
   (CONV_RULE TWEAK_CONV MLKEM_REJ_UNIFORM_ALT_CORE_EVENTS)
    `[]:int64 list` 48 THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* The same for the full code, with its BTI landing pad, with the variables  *)
(* in the order of the other subroutine theorems.                            *)

let MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_EVENTS = time prove
 (`exists f_events.
     forall res n buf buflen table (curlist:int16 list) (inlist:(12 word)list)
            pc e stackpointer returnaddress.
      aligned 16 stackpointer /\
      24 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      LENGTH curlist = val n /\ val n <= 256 /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x3d4); (word_sub stackpointer (word 48),48);
           (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,0x3d4); (buf,val buflen); (table,4096)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [res; n; buf; buflen; table] s /\
                wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                wordlist_from_memory(res,val n) s = curlist /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events res n buf buflen table inlist pc
                                   (word_sub stackpointer (word 48))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [buf,val buflen; table,4096;
                        word_sub stackpointer (word 48),48]
                       [word_sub stackpointer (word 48),48; res,512]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MP_TAC(ARM_ADD_IBT_RULE ~extra:[wordlist_from_memory]
    mlkem_rej_uniform_alt_mc mlkem_rej_uniform_alt_tmc
    MLKEM_REJ_UNIFORM_ALT_NOIBT_SUBROUTINE_EVENTS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`res:int64`; `n:int64`; `buf:int64`; `buflen:int64`; `table:int64`;
    `curlist:int16 list`; `inlist:(12 word)list`; `pc:num`;
    `e:(uarch_event)list`; `stackpointer:int64`; `returnaddress:int64`] THEN
  FIRST_X_ASSUM(ACCEPT_TAC o SPECL
   [`e:(uarch_event)list`; `res:int64`; `n:int64`; `buf:int64`;
    `buflen:int64`; `table:int64`; `curlist:int16 list`;
    `inlist:(12 word)list`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`]));;

(* ------------------------------------------------------------------------- *)
(* The result as in MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_CORRECT and the events  *)
(* in the same postcondition, for callers that need both at the same step,   *)
(* the event list e first as for the forms above without BTI.                *)
(* ------------------------------------------------------------------------- *)

let MLKEM_REJ_UNIFORM_ALT_NOIBT_SUBROUTINE_FULL = time prove
 (`exists f_events.
     forall e res n buf buflen table (curlist:int16 list)
            (inlist:(12 word)list) pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      24 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      LENGTH curlist = val n /\ val n <= 256 /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x3d0); (word_sub stackpointer (word 48),48);
           (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,0x3d0); (buf,val buflen); (table,4096)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_tmc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [res; n; buf; buflen; table] s /\
                wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                wordlist_from_memory(res,val n) s = curlist /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                (let inlist' = MAP (word_zx:12 word->16 word) inlist in
                 let outlist =
                   SUB_LIST (0,256)
                    (APPEND curlist (FILTER (\x. val x < 3329) inlist')) in
                 let outlen = LENGTH outlist in
                 C_RETURN s = word outlen /\
                 wordlist_from_memory(res,outlen) s = outlist) /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events res n buf buflen table inlist pc
                                   (word_sub stackpointer (word 48))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [buf,val buflen; table,4096;
                        word_sub stackpointer (word 48),48]
                       [word_sub stackpointer (word 48),48; res,512]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  let TWEAK_CONV =
    TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[wordlist_from_memory] in
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC MLKEM_REJ_UNIFORM_ALT_EXEC
   (CONV_RULE TWEAK_CONV MLKEM_REJ_UNIFORM_ALT_CORE_FULL)
    `[]:int64 list` 48 THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* The same for the full code, with its BTI landing pad.                     *)

let MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL = time prove
 (`exists f_events.
     forall e res n buf buflen table (curlist:int16 list)
            (inlist:(12 word)list) pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      24 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      LENGTH curlist = val n /\ val n <= 256 /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x3d4); (word_sub stackpointer (word 48),48);
           (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,0x3d4); (buf,val buflen); (table,4096)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [res; n; buf; buflen; table] s /\
                wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                wordlist_from_memory(res,val n) s = curlist /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                (let inlist' = MAP (word_zx:12 word->16 word) inlist in
                 let outlist =
                   SUB_LIST (0,256)
                    (APPEND curlist (FILTER (\x. val x < 3329) inlist')) in
                 let outlen = LENGTH outlist in
                 C_RETURN s = word outlen /\
                 wordlist_from_memory(res,outlen) s = outlist) /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events res n buf buflen table inlist pc
                                   (word_sub stackpointer (word 48))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [buf,val buflen; table,4096;
                        word_sub stackpointer (word 48),48]
                       [word_sub stackpointer (word 48),48; res,512]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE ~extra:[wordlist_from_memory]
    mlkem_rej_uniform_alt_mc mlkem_rej_uniform_alt_tmc
    MLKEM_REJ_UNIFORM_ALT_NOIBT_SUBROUTINE_FULL));;
