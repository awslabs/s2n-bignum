(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform rejection sampling, mlkem_rej_uniform_alt_VARIABLE_TIME,          *)
(* appending to a partial result: the events as a function of the inputs,    *)
(* together with the result ("FULL"), for the subroutine without and with    *)
(* its IBT landing pad. As arm/proofs/utils/mlkem_native2_rej_full.ml for    *)
(* AArch64, with the x86 forms of the code, the frame and the simulation.    *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_rej_uniform_alt_VARIABLE_TIME.ml";;

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
         (stk:int64) p (s:x86state) <=>
    read RSP s = stk /\ read R8 s = table /\
    read RDX s = word_add buf (word(24 * p)) /\
    read RCX s = word(buflen - 24 * p) /\
    read RSI s = word(LENGTH(rej_out curlist inlist p)) /\
    read RDI s = word_add res (word(2 * LENGTH(rej_out curlist inlist p))) /\
    read YMM3 s =
    word_join (word 0x0d010d010d010d010d010d010d010d01:int128)
              (word 0x0d010d010d010d010d010d010d010d01:int128) /\
    read YMM5 s =
    word_join (word 0x0fff0fff0fff0fff0fff0fff0fff0fff:int128)
              (word 0x0fff0fff0fff0fff0fff0fff0fff0fff:int128) /\
    read YMM12 s =
    word_join (word 0x0d800d800d800d800d800d800d800d80:int128)
              (word 0x0d800d800d800d800d800d800d800d80:int128) /\
    read YMM6 s =
    word_join (word 0x0f0e0e0d0c0b0b0a0908080706050504:int128)
              (word 0x0b0a0a09080707060504040302010100:int128) /\
    read YMM10 s =
    word_join (word 0x0b0a0a09080707060504040302010100:int128)
              (word 0x0b0a0a09080707060504040302010100:int128) /\
    read YMM11 s =
    word_join (word 0x0f0e0e0d0c0b0b0a0908080706050504:int128)
              (word 0x0f0e0e0d0c0b0b0a0908080706050504:int128) /\
    read (memory :> bytes(table,4096)) s =
    num_of_wordlist mlkem_rej_uniform_table /\
    read (memory :> bytes(buf,buflen)) s = num_of_wordlist inlist /\
    read (memory :> bytes(res,2 * LENGTH(rej_out curlist inlist p))) s =
    num_of_wordlist (rej_out curlist inlist p)`;;

let rej_end = new_definition
 `rej_end (res:int64) (buf:int64) buflen (table:int64) curlist inlist
          (stk:int64) (s:x86state) <=>
    ?q. 24 * q <= buflen /\
        (buflen < 24 * (q + 1) \/ 256 <= LENGTH(rej_out curlist inlist q)) /\
        rej_st res buf buflen table curlist inlist stk q s`;;

(* The state in the final copy, as in rej_cinv but without the events        *)

let rej_cst = new_definition
 `rej_cst (res:int64) (buf:int64) buflen (table:int64)
          (inlist:(12 word)list)
          (stk:int64) p (out:int16 list)
          (L:int16 list) m i (s:x86state) <=>
    read RSP s = stk /\ read R8 s = table /\
    read RDX s = word_add buf (word(24 * (p + 1))) /\
    read RCX s = word(buflen - 24 * (p + 1)) /\
    read RSI s = word(LENGTH out + m) /\
    read RDI s = word_add res (word(2 * (LENGTH out + i))) /\
    read R9 s = word i /\ read R11 s = word m /\
    read YMM3 s =
    word_join (word 0x0d010d010d010d010d010d010d010d01:int128)
              (word 0x0d010d010d010d010d010d010d010d01:int128) /\
    read YMM5 s =
    word_join (word 0x0fff0fff0fff0fff0fff0fff0fff0fff:int128)
              (word 0x0fff0fff0fff0fff0fff0fff0fff0fff:int128) /\
    read YMM12 s =
    word_join (word 0x0d800d800d800d800d800d800d800d80:int128)
              (word 0x0d800d800d800d800d800d800d800d80:int128) /\
    read YMM6 s =
    word_join (word 0x0f0e0e0d0c0b0b0a0908080706050504:int128)
              (word 0x0b0a0a09080707060504040302010100:int128) /\
    read YMM10 s =
    word_join (word 0x0b0a0a09080707060504040302010100:int128)
              (word 0x0b0a0a09080707060504040302010100:int128) /\
    read YMM11 s =
    word_join (word 0x0f0e0e0d0c0b0b0a0908080706050504:int128)
              (word 0x0f0e0e0d0c0b0b0a0908080706050504:int128) /\
    read (memory :> bytes(table,4096)) s =
    num_of_wordlist mlkem_rej_uniform_table /\
    read (memory :> bytes(buf,buflen)) s = num_of_wordlist inlist /\
    read (memory :> bytes(stk,2 * LENGTH L)) s = num_of_wordlist L /\
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
 (`!(step:A->A->bool) Q C. ensures step (\s. F) Q C`,
  REWRITE_TAC[ensures]);;

let REJ_EV_SEQ = prove
 (`!res stk (pc:num) off1 off2 off3 (P:x86state->bool) Q S
    ev1 ev2 (e:(uarch_event)list) rd wr.
     ensures x86
      (\s. bytes_loaded s (word pc) (BUTLAST mlkem_rej_uniform_alt_tmc) /\
           read RIP s = word(pc + off1) /\ P s /\ read events s = e)
      (\s. bytes_loaded s (word pc) (BUTLAST mlkem_rej_uniform_alt_tmc) /\
           read RIP s = word(pc + off2) /\ Q s /\
           read events s = APPEND ev1 e /\ memaccess_inbounds ev1 rd wr)
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(res,512); memory :> bytes(stk,32)]) /\
     ensures x86
      (\s. bytes_loaded s (word pc) (BUTLAST mlkem_rej_uniform_alt_tmc) /\
           read RIP s = word(pc + off2) /\ Q s /\
           read events s = APPEND ev1 e)
      (\s. bytes_loaded s (word pc) (BUTLAST mlkem_rej_uniform_alt_tmc) /\
           read RIP s = word(pc + off3) /\ S s /\
           read events s = APPEND ev2 (APPEND ev1 e) /\
           memaccess_inbounds ev2 rd wr)
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(res,512); memory :> bytes(stk,32)])
     ==> ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST mlkem_rej_uniform_alt_tmc) /\
               read RIP s = word(pc + off1) /\ P s /\ read events s = e)
          (\s. bytes_loaded s (word pc) (BUTLAST mlkem_rej_uniform_alt_tmc) /\
               read RIP s = word(pc + off3) /\ S s /\
               read events s = APPEND (APPEND ev2 ev1) e /\
               memaccess_inbounds (APPEND ev2 ev1) rd wr)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(res,512); memory :> bytes(stk,32)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC REJ_TRANS THEN
  EXISTS_TAC
   `\s. bytes_loaded s (word pc) (BUTLAST mlkem_rej_uniform_alt_tmc) /\
        read RIP s = word(pc + off2) /\ (Q:x86state->bool) s /\
        read events s = APPEND ev1 e /\
        memaccess_inbounds (ev1:(uarch_event)list) rd wr` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `memaccess_inbounds (ev1:(uarch_event)list) rd wr` THEN
  ASM_REWRITE_TAC[ENSURES_FALSE_PRE; MEMACCESS_INBOUNDS_APPEND;
                  GSYM APPEND_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* The events of a block. The statements are of the form                     *)
(*                                                                           *)
(*   !public. hyps ==> ?ev. !curlist e. ... ==> ensures x86                  *)
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
(* The exits from the loops, and the tests of the loop by 48 bytes, at its   *)
(* entry (A, at pc + 0x82) and at the end of its body (B, at pc + 0x185).    *)
(* ------------------------------------------------------------------------- *)

(*** The setup common to these: the metavariable for the events, the count
 *** c and the bytes left as 64-bit values, and the conditions of the
 *** branches as the code tests them
 ***)

let REJ_EV_TEST_PRE_TAC =
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let REJ_EV_TEST_SETUP_TAC =
  REJ_EV_META_TAC THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  REWRITE_TAC[rej_st; rej_end] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `c < 2 EXP 64 /\ buflen - 24 * p < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`curlist:int16 list`; `inlist:(12 word)list`; `p:num`]
      LENGTH_REJ_OUT) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY VAL_INT64_TAC [`c:num`; `buflen - 24 * p`] THEN
  SUBGOAL_THEN
   `(c < 224 \/ val (word_sub (word c:int64) (word 224)) = 0) <=> ~(224 < c)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV);;

let REJ_EV_TEST_SIM_TAC n =
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REJ_EV_CLOSE_TAC;;

let REJ_EV_LOOP24_EXIT = prove
 (`!res buf buflen table inlist stk pc p c.
     buflen < 2 EXP 64 /\ 24 * p <= buflen /\
     (buflen < 24 * (p + 1) \/ 256 <= c)
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures x86
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x198) /\
                     rej_st res buf buflen table curlist inlist stk p s /\
                     read events s = e)
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x284) /\
                     rej_end res buf buflen table curlist inlist stk s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stk,32] [stk,32; res,512])
                (MAYCHANGE [RSP] ,,
                 MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stk,32)])`,
  let EXIT_SIM_TAC n =
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (1--n) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    REJ_EV_CLOSE_TAC in
  REJ_EV_TEST_PRE_TAC THEN
  ASM_CASES_TAC `buflen < 24 * (p + 1)` THEN REJ_EV_TEST_SETUP_TAC THENL
   [SUBGOAL_THEN `buflen - 24 * p < 24` ASSUME_TAC THENL
     [ASM_ARITH_TAC; EXIT_SIM_TAC 2];
    SUBGOAL_THEN `~(buflen - 24 * p < 24) /\ 256 <= c` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; EXIT_SIM_TAC 4]]);;

let REJ_EV_LOOP48_EXIT_A = prove
 (`!res buf buflen table inlist stk pc p c.
     buflen < 2 EXP 64 /\ 24 * p <= buflen /\
     (buflen < 24 * (p + 2) \/ 224 < c)
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures x86
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x82) /\
                     rej_st res buf buflen table curlist inlist stk p s /\
                     read events s = e)
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x198) /\
                     rej_st res buf buflen table curlist inlist stk p s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stk,32] [stk,32; res,512])
                (MAYCHANGE [RSP] ,,
                 MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stk,32)])`,
  REJ_EV_TEST_PRE_TAC THEN
  ASM_CASES_TAC `buflen < 24 * (p + 2)` THEN REJ_EV_TEST_SETUP_TAC THENL
   [SUBGOAL_THEN `buflen - 24 * p < 48` ASSUME_TAC THENL
     [ASM_ARITH_TAC; REJ_EV_TEST_SIM_TAC 2];
    SUBGOAL_THEN `~(buflen - 24 * p < 48) /\ 224 < c` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; REJ_EV_TEST_SIM_TAC 4]]);;

let REJ_EV_LOOP48_ENTER_A = prove
 (`!res buf buflen table inlist stk pc p c.
     buflen < 2 EXP 64 /\ 24 * (p + 2) <= buflen /\ c <= 224
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures x86
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x82) /\
                     rej_st res buf buflen table curlist inlist stk p s /\
                     read events s = e)
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x9c) /\
                     rej_st res buf buflen table curlist inlist stk p s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stk,32] [stk,32; res,512])
                (MAYCHANGE [RSP] ,,
                 MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stk,32)])`,
  REJ_EV_TEST_PRE_TAC THEN REJ_EV_TEST_SETUP_TAC THEN
  SUBGOAL_THEN `~(buflen - 24 * p < 48) /\ ~(224 < c)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; REJ_EV_TEST_SIM_TAC 5]);;

let REJ_EV_LOOP48_EXIT_B = prove
 (`!res buf buflen table inlist stk pc p c.
     buflen < 2 EXP 64 /\ 24 * p <= buflen /\
     (buflen < 24 * (p + 2) \/ 224 < c)
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures x86
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x185) /\
                     rej_st res buf buflen table curlist inlist stk p s /\
                     read events s = e)
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x198) /\
                     rej_st res buf buflen table curlist inlist stk p s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stk,32] [stk,32; res,512])
                (MAYCHANGE [RSP] ,,
                 MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stk,32)])`,
  REJ_EV_TEST_PRE_TAC THEN
  ASM_CASES_TAC `buflen < 24 * (p + 2)` THEN REJ_EV_TEST_SETUP_TAC THENL
   [SUBGOAL_THEN `buflen - 24 * p < 48` ASSUME_TAC THENL
     [ASM_ARITH_TAC; REJ_EV_TEST_SIM_TAC 2];
    SUBGOAL_THEN `~(buflen - 24 * p < 48) /\ 224 < c /\ ~(c <= 224)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; REJ_EV_TEST_SIM_TAC 4]]);;

let REJ_EV_LOOP48_ENTER_B = prove
 (`!res buf buflen table inlist stk pc p c.
     buflen < 2 EXP 64 /\ 24 * (p + 2) <= buflen /\ c <= 224
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures x86
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x185) /\
                     rej_st res buf buflen table curlist inlist stk p s /\
                     read events s = e)
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x9c) /\
                     rej_st res buf buflen table curlist inlist stk p s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stk,32] [stk,32; res,512])
                (MAYCHANGE [RSP] ,,
                 MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stk,32)])`,
  REJ_EV_TEST_PRE_TAC THEN REJ_EV_TEST_SETUP_TAC THEN
  SUBGOAL_THEN `~(buflen - 24 * p < 48) /\ ~(224 < c) /\ c <= 224`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; REJ_EV_TEST_SIM_TAC 4]);;

(* ------------------------------------------------------------------------- *)
(* The loop by 24 bytes when the accepted numbers are stored directly.       *)
(* ------------------------------------------------------------------------- *)

let REJ_EV_LOOP24_DIRECT = prove
 (`!res buf buflen table inlist stk pc p c.
     8 * buflen = 12 * LENGTH(inlist:(12 word)list) /\ 24 divides buflen /\
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x28f); (stk,32); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stk,32))
         [(word pc,0x28f); (buf,buflen); (table,4096)] /\
     24 * (p + 1) <= buflen /\ c <= 240
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures x86
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x198) /\
                     rej_st res buf buflen table curlist inlist stk p s /\
                     read events s = e)
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x198) /\
                     rej_st res buf buflen table curlist inlist stk (p + 1)
                            s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stk,32] [stk,32; res,512])
                (MAYCHANGE [RSP] ,,
                 MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stk,32)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REJ_EV_META_TAC THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  REWRITE_TAC[rej_st; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_TAC THEN
  ABBREV_TAC `out = rej_out curlist inlist p` THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`] THEN
  ABBREV_TAC
   `chk = word((num_of_wordlist(inlist:(12 word)list) DIV 2 EXP (8 * 24 * p))
               MOD 2 EXP 192):192 word` THEN
  SUBGOAL_THEN
   `!j. j < 16
        ==> EL (16 * p + j) inlist =
            word_subword (chk:192 word) (12 * j,12):12 word`
  (LABEL_TAC "chunk") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "chk" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REJ_CHUNK_EL_192 THEN
    MAP_EVERY UNDISCH_TAC
     [`j < 16`; `8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 1) <= buflen`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `buflen - 24 * p < 2 EXP 64 /\ ~(buflen - 24 * p < 24)`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `buflen - 24 * p` THEN
  SUBGOAL_THEN `c < 2 EXP 64 /\ ~(256 <= c) /\ ~(240 < c) /\ c < 241`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `c:num` THEN
  SUBGOAL_THEN
   `(c < 240 \/ val (word_sub (word c:int64) (word 240)) = 0) <=> ~(240 < c)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`buf:int64`; `buflen:num`;
                `num_of_wordlist(inlist:(12 word)list)`;
                `24 * p`; `s0:x86state`] CHUNK_LOADS24) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `24 * (p + 1) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN

  (*** The 16 candidates, the masks and the counts ***)

  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (1--12) THEN
  REJ_CANDIDATES_TAC 1 THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC REJ_PACK_FOLD) (13--16) THEN
  REJ_MASK_SIMPLIFY_TAC 16 THEN REJ_MASK_ABBREV_TAC 16 ["m0"; "m1"] THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n])
            (17--25) THEN
  REJ_INDEX_TAC `R9` 25 `m0:byte` THEN REJ_INDEX_TAC `R10` 25 `m1:byte` THEN
  REJ_COUNT_TAC `R11` 25 `m0:byte` THEN REJ_COUNT_TAC `RAX` 25 `m1:byte` THEN

  (*** The table entries and the compaction ***)

  ASSUME_TAC(WORD_RULE `!x. word (1 * val(word x:int64)):int64 = word x`) THEN
  REJ_TAB_TAC "tab0" `m0:byte` 25 THEN REJ_TAB_TAC "tab1" `m1:byte` 25 THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (26--28) THEN
  REJ_GROUP_TAC `YMM0` 28 THEN
  REJ_LIST_ABBREV_TAC `YMM0` 28 ["lis0"; "lis1"] ["len0"; "len1"] THEN
  REJ_COUNTS_TAC THEN

  (*** The stores and the updates of the pointer and the count ***)

  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (29--31) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ZX_JOIN]) THEN REJ_STORE_LEN_TAC THEN
  SUBGOAL_THEN `len0 < 2 EXP 64 /\ len1 < 2 EXP 64 /\ len0 + len1 < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`len0 <= 8`; `len1 <= 8`] THEN ARITH_TAC;
    ALL_TAC] THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [32] THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MATCH_MP REJ_ADDR_NORM (ASSUME `len0 < 2 EXP 64`)]) THEN
  REJ_STORE_LEN_TAC THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (33--36) THEN

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

  SUBGOAL_THEN `c + len0 <= 248` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`c < 241`; `len0 <= 8`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[ASSUME
   `rej_out curlist inlist (p + 1) = APPEND (APPEND out lis0) lis1`;
   LENGTH_APPEND] THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`;
              ASSUME `LENGTH(lis0:int16 list) = len0`;
              ASSUME `LENGTH(lis1:int16 list) = len1`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    SUBGOAL_THEN `buflen - 24 * p = (buflen - 24 * (p + 1)) + 24`
    SUBST1_TAC THENL
     [UNDISCH_TAC `24 * (p + 1) <= buflen` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC];
    REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    SIMP_TAC[MOD_LT; ASSUME `len0 + len1 < 2 EXP 64`] THEN CONV_TAC WORD_RULE;
    REJ_EV_TAC;
    REJ_MI_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The final copy through the buffer on the stack, of the first m of the     *)
(* list L of the accepted numbers from the last 24 bytes: the entry to the   *)
(* copy loop, a step back to its start, the last step and the branch back to *)
(* the loop by 24 bytes.                                                     *)
(* ------------------------------------------------------------------------- *)

let REJ_EV_COPY_ENTRY = prove
 (`!res buf buflen table inlist stk pc p c L m.
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x28f); (stk,32); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stk,32))
         [(word pc,0x28f); (buf,buflen); (table,4096)] /\
     m <= LENGTH L /\ LENGTH L <= 16 /\ c + m <= 256 /\ ~(m = 0)
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures x86
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x262) /\
                     rej_cst res buf buflen table inlist stk p
                             (rej_out curlist inlist p) L m 0 s /\
                     read events s = e)
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x26b) /\
                     rej_cst res buf buflen table inlist stk p
                             (rej_out curlist inlist p) L m 0 s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stk,32] [stk,32; res,512])
                (MAYCHANGE [RSP] ,,
                 MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stk,32)])`,
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
  CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REJ_EV_CLOSE_TAC);;

let REJ_EV_COPY_STEP = prove
 (`!res buf buflen table inlist stk pc p c L m i.
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x28f); (stk,32); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stk,32))
         [(word pc,0x28f); (buf,buflen); (table,4096)] /\
     m <= LENGTH L /\ LENGTH L <= 16 /\ c + m <= 256 /\ i + 1 < m
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures x86
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x26b) /\
                     rej_cst res buf buflen table inlist stk p
                             (rej_out curlist inlist p) L m i s /\
                     read events s = e)
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x26b) /\
                     rej_cst res buf buflen table inlist stk p
                             (rej_out curlist inlist p) L m (i + 1) s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stk,32] [stk,32; res,512])
                (MAYCHANGE [RSP] ,,
                 MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stk,32)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REJ_EV_META_TAC THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  REWRITE_TAC[rej_cst; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_TAC THEN
  ABBREV_TAC `out = rej_out curlist inlist p` THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV) THEN
  SUBGOAL_THEN `i < LENGTH(L:int16 list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i < 2 EXP 64 /\ i + 1 < 2 EXP 64 /\ m < 2 EXP 64`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `i:num` THEN VAL_INT64_TAC `i + 1` THEN
  VAL_INT64_TAC `m:num` THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`stk:int64`; `L:int16 list`; `i:num`; `s0:x86state`]
    READ_BYTES16_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (1--5) THEN
  FIRST_X_ASSUM(MP_TAC o REJ_COPY_SIMP_RULE o check (can (term_match
    [`res:int64`]
    `read (memory :> bytes16 (word_add res (word (2 * n)))) s5 = x`) o
    concl)) THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_INC]) THEN
  MP_TAC(SPECL [`res:int64`; `c + i:num`;
                `APPEND out (SUB_LIST(0,i) L):int16 list`;
                `EL i L:int16`; `s5:x86state`] REJ_STORE16) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST; SUB_0] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC(ARITH_RULE `i < l ==> MIN i l = i`) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_ADD; ASSUME `val(word(i + 1):int64) = i + 1`]) THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [6] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[SUB_LIST_SNOC] THEN
  REWRITE_TAC[APPEND_ASSOC; ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN
  REJ_EV_CLOSE_TAC);;

let REJ_EV_COPY_LAST = prove
 (`!res buf buflen table inlist stk pc p c L m i.
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x28f); (stk,32); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stk,32))
         [(word pc,0x28f); (buf,buflen); (table,4096)] /\
     m <= LENGTH L /\ LENGTH L <= 16 /\ c + m <= 256 /\ i + 1 = m
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c /\
           rej_out curlist inlist (p + 1) =
           APPEND (rej_out curlist inlist p) (SUB_LIST(0,m) L)
           ==> ensures x86
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x26b) /\
                     rej_cst res buf buflen table inlist stk p
                             (rej_out curlist inlist p) L m i s /\
                     read events s = e)
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x198) /\
                     rej_st res buf buflen table curlist inlist stk (p + 1)
                            s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stk,32] [stk,32; res,512])
                (MAYCHANGE [RSP] ,,
                 MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stk,32)])`,
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
  CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV) THEN
  SUBGOAL_THEN `i < LENGTH(L:int16 list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i < 2 EXP 64 /\ i + 1 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `i:num` THEN VAL_INT64_TAC `i + 1` THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`stk:int64`; `L:int16 list`; `i:num`; `s0:x86state`]
    READ_BYTES16_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (1--5) THEN
  FIRST_X_ASSUM(MP_TAC o REJ_COPY_SIMP_RULE o check (can (term_match
    [`res:int64`]
    `read (memory :> bytes16 (word_add res (word (2 * n)))) s5 = x`) o
    concl)) THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_INC]) THEN
  MP_TAC(SPECL [`res:int64`; `c + i:num`;
                `APPEND out (SUB_LIST(0,i) L):int16 list`;
                `EL i L:int16`; `s5:x86state`] REJ_STORE16) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST; SUB_0] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC(ARITH_RULE `i < l ==> MIN i l = i`) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_ADD; ASSUME `val(word(i + 1):int64) = i + 1`; LT_REFL]) THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (6--7) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[SUB_LIST_SNOC] THEN
  REWRITE_TAC[APPEND_ASSOC; ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN
  REJ_EV_CLOSE_TAC);;

(* The copy loop and the whole final copy                                    *)

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
 (`!res buf buflen table inlist stk pc p c L m.
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x28f); (stk,32); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stk,32))
         [(word pc,0x28f); (buf,buflen); (table,4096)] /\
     m <= LENGTH L /\ LENGTH L <= 16 /\ c + m <= 256
     ==> !i. i < m
             ==> ?ev. !curlist e.
                   LENGTH(rej_out curlist inlist p) = c /\
                   rej_out curlist inlist (p + 1) =
                   APPEND (rej_out curlist inlist p) (SUB_LIST(0,m) L)
                   ==> ensures x86
                        (\s. bytes_loaded s (word pc)
                               (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                             read RIP s = word(pc + 0x26b) /\
                             rej_cst res buf buflen table inlist stk
                                     p (rej_out curlist inlist p) L m i s /\
                             read events s = e)
                        (\s. bytes_loaded s (word pc)
                               (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                             read RIP s = word(pc + 0x198) /\
                             rej_st res buf buflen table curlist inlist
                                    stk (p + 1) s /\
                             read events s = APPEND ev e /\
                             memaccess_inbounds ev
                              [buf,buflen; table,4096; stk,32]
                              [stk,32; res,512])
                        (MAYCHANGE [RSP] ,,
                         MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                         MAYCHANGE [memory :> bytes(res,512);
                                    memory :> bytes(stk,32)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC REJ_DOWN_INDUCT THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THENL
   [DISCH_TAC THEN MATCH_MP_TAC REJ_EV_COPY_LAST THEN ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_TAC `ev2:(uarch_event)list`))] THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                `inlist:(12 word)list`; `stk:int64`; `pc:num`;
                `p:num`; `c:num`; `L:int16 list`; `m:num`; `i:num`]
    REJ_EV_COPY_STEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `ev1:(uarch_event)list`) THEN
  EXISTS_TAC `APPEND (ev2:(uarch_event)list) ev1` THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  STRIP_TAC THEN MATCH_MP_TAC REJ_EV_SEQ THEN
  MAP_EVERY EXISTS_TAC
   [`0x26b`;
    `rej_cst res buf buflen table inlist stk p
             (rej_out curlist inlist p) L m (i + 1)`] THEN
  ASM_SIMP_TAC[]);;

let REJ_EV_LASTCOPY = prove
 (`!res buf buflen table inlist stk pc p c L m.
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x28f); (stk,32); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stk,32))
         [(word pc,0x28f); (buf,buflen); (table,4096)] /\
     m <= LENGTH L /\ LENGTH L <= 16 /\ c + m <= 256
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c /\
           rej_out curlist inlist (p + 1) =
           APPEND (rej_out curlist inlist p) (SUB_LIST(0,m) L)
           ==> ensures x86
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x262) /\
                     rej_cst res buf buflen table inlist stk p
                             (rej_out curlist inlist p) L m 0 s /\
                     read events s = e)
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x198) /\
                     rej_st res buf buflen table curlist inlist stk (p + 1)
                            s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stk,32] [stk,32; res,512])
                (MAYCHANGE [RSP] ,,
                 MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stk,32)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [REJ_EV_META_TAC THEN
    MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
    REWRITE_TAC[rej_cst; rej_st; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                NONOVERLAPPING_CLAUSES; ALL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    ASM_REWRITE_TAC[SUB_0; ADD_CLAUSES; MULT_CLAUSES; SUB_LIST_CLAUSES;
                    APPEND_NIL] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV) THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REJ_EV_CLOSE_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                `inlist:(12 word)list`; `stk:int64`; `pc:num`;
                `p:num`; `c:num`; `L:int16 list`; `m:num`]
    REJ_EV_COPY_LOOP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < m <=> ~(m = 0)`] THEN
  DISCH_THEN(X_CHOOSE_TAC `ev2:(uarch_event)list`) THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                `inlist:(12 word)list`; `stk:int64`; `pc:num`;
                `p:num`; `c:num`; `L:int16 list`; `m:num`]
    REJ_EV_COPY_ENTRY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `ev1:(uarch_event)list`) THEN
  EXISTS_TAC `APPEND (ev2:(uarch_event)list) ev1` THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  STRIP_TAC THEN MATCH_MP_TAC REJ_EV_SEQ THEN
  MAP_EVERY EXISTS_TAC
   [`0x26b`;
    `rej_cst res buf buflen table inlist stk p
             (rej_out curlist inlist p) L m 0`] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The loop by 24 bytes when there may not be room for all 16 numbers: the   *)
(* two groups go to the buffer on the stack, from which as many as there is  *)
(* room for are copied.                                                      *)
(* ------------------------------------------------------------------------- *)

let REJ_EV_LOOP24_HEAD = prove
 (`!res buf buflen table inlist stk pc p c L m.
     8 * buflen = 12 * LENGTH(inlist:(12 word)list) /\ 24 divides buflen /\
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x28f); (stk,32); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stk,32))
         [(word pc,0x28f); (buf,buflen); (table,4096)] /\
     24 * (p + 1) <= buflen /\ 240 < c /\ c < 256 /\
     REJ_SAMPLE (SUB_LIST(16 * p,16) inlist) = L /\
     MIN (LENGTH L) (256 - c) = m
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures x86
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x198) /\
                     rej_st res buf buflen table curlist inlist stk p s /\
                     read events s = e)
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x262) /\
                     rej_cst res buf buflen table inlist stk p
                             (rej_out curlist inlist p) L m 0 s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stk,32] [stk,32; res,512])
                (MAYCHANGE [RSP] ,,
                 MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stk,32)])`,
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
   `chk = word((num_of_wordlist(inlist:(12 word)list) DIV 2 EXP (8 * 24 * p))
               MOD 2 EXP 192):192 word` THEN
  SUBGOAL_THEN
   `!j. j < 16
        ==> EL (16 * p + j) inlist =
            word_subword (chk:192 word) (12 * j,12):12 word`
  (LABEL_TAC "chunk") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "chk" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REJ_CHUNK_EL_192 THEN
    MAP_EVERY UNDISCH_TAC
     [`j < 16`; `8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 1) <= buflen`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `buflen - 24 * p < 2 EXP 64 /\ ~(buflen - 24 * p < 24)`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `buflen - 24 * p` THEN
  SUBGOAL_THEN `c < 2 EXP 64 /\ ~(256 <= c) /\ 240 < c /\ c < 256`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `c:num` THEN
  SUBGOAL_THEN
   `(c < 240 \/ val (word_sub (word c:int64) (word 240)) = 0) <=> ~(240 < c)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`buf:int64`; `buflen:num`;
                `num_of_wordlist(inlist:(12 word)list)`;
                `24 * p`; `s0:x86state`] CHUNK_LOADS24) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `24 * (p + 1) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (1--12) THEN
  REJ_CANDIDATES_TAC 1 THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC REJ_PACK_FOLD) (13--16) THEN
  REJ_MASK_SIMPLIFY_TAC 16 THEN REJ_MASK_ABBREV_TAC 16 ["m0"; "m1"] THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n])
            (17--25) THEN
  REJ_INDEX_TAC `R9` 25 `m0:byte` THEN REJ_INDEX_TAC `R10` 25 `m1:byte` THEN
  REJ_COUNT_TAC `R11` 25 `m0:byte` THEN REJ_COUNT_TAC `RAX` 25 `m1:byte` THEN
  ASSUME_TAC(WORD_RULE `!x. word (1 * val(word x:int64)):int64 = word x`) THEN
  REJ_TAB_TAC "tab0" `m0:byte` 25 THEN REJ_TAB_TAC "tab1" `m1:byte` 25 THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (26--28) THEN
  REJ_GROUP_TAC `YMM0` 28 THEN
  REJ_LIST_ABBREV_TAC `YMM0` 28 ["lis0"; "lis1"] ["len0"; "len1"] THEN
  REJ_COUNTS_TAC THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (29--31) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ZX_JOIN]) THEN
  MP_TAC(SPECL [`stk:int64`; `lis0:int16 list`; `s31:x86state`]
    REJ_STORE0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `len0 < 2 EXP 64 /\ len1 < 2 EXP 64 /\ len0 + len1 < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`len0 <= 8`; `len1 <= 8`] THEN ARITH_TAC;
    ALL_TAC] THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [32] THEN
  VAL_INT64_TAC `len0:num` THEN VAL_INT64_TAC `len1:num` THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word len0:int64) = len0`]) THEN
  REJ_STORE_AT_TAC `stk:int64` THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (33--37) THEN
  SUBGOAL_THEN `L:int16 list = APPEND lis0 lis1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `REJ_SAMPLE (SUB_LIST(16 * p,16) inlist) = L`)) THEN
    REJ_SAMPLE_EXPAND_TAC SUB_LIST_EXPAND_16 ["lis0"; "lis1"] ["chunk"]
     [`8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 1) <= buflen`];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(L:int16 list) = len0 + len1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match []
    `read R11 s37 = (if a then b else c)`) o concl)) THEN
  MP_TAC(SPECL [`len0:num`; `len1:num`; `c:num`] REJ_CMOVA) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`len0 <= 8`; `len1 <= 8`; `c < 256`] THEN
    ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM(ASSUME `LENGTH(L:int16 list) = len0 + len1`)] THEN
  REWRITE_TAC[ASSUME `MIN (LENGTH(L:int16 list)) (256 - c) = m`] THEN
  DISCH_TAC THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (38--39) THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match [`stk:int64`]
    `read (memory :> bytes (stk,n)) s39 =
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
 (`!res buf buflen table inlist stk pc p c.
     8 * buflen = 12 * LENGTH(inlist:(12 word)list) /\ 24 divides buflen /\
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x28f); (stk,32); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stk,32))
         [(word pc,0x28f); (buf,buflen); (table,4096)] /\
     24 * (p + 1) <= buflen /\ 240 < c /\ c < 256
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures x86
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x198) /\
                     rej_st res buf buflen table curlist inlist stk p s /\
                     read events s = e)
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x198) /\
                     rej_st res buf buflen table curlist inlist stk (p + 1)
                            s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stk,32] [stk,32; res,512])
                (MAYCHANGE [RSP] ,,
                 MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stk,32)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `L = REJ_SAMPLE (SUB_LIST(16 * p,16) (inlist:(12 word)list))` THEN
  ABBREV_TAC `m = MIN (LENGTH(L:int16 list)) (256 - c)` THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                `inlist:(12 word)list`; `stk:int64`; `pc:num`;
                `p:num`; `c:num`; `L:int16 list`; `m:num`]
    REJ_EV_LOOP24_HEAD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `ev1:(uarch_event)list`) THEN
  MP_TAC(ISPECL [`inlist:(12 word)list`; `16 * p`; `16`]
    LENGTH_REJ_SAMPLE_CHUNK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                `inlist:(12 word)list`; `stk:int64`; `pc:num`;
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
   [`0x262`;
    `rej_cst res buf buflen table inlist stk p
             (rej_out curlist inlist p) L m 0`] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The loop by 48 bytes, the 32 numbers stored directly.                     *)
(* ------------------------------------------------------------------------- *)

let REJ_EV_LOOP48_BODY = prove
 (`!res buf buflen table inlist stk pc p c.
     8 * buflen = 12 * LENGTH(inlist:(12 word)list) /\ 24 divides buflen /\
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x28f); (stk,32); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stk,32))
         [(word pc,0x28f); (buf,buflen); (table,4096)] /\
     24 * (p + 2) <= buflen /\ c <= 224
     ==> ?ev. !curlist e.
           LENGTH(rej_out curlist inlist p) = c
           ==> ensures x86
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x9c) /\
                     rej_st res buf buflen table curlist inlist stk p s /\
                     read events s = e)
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x185) /\
                     rej_st res buf buflen table curlist inlist stk (p + 2)
                            s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stk,32] [stk,32; res,512])
                (MAYCHANGE [RSP] ,,
                 MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stk,32)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REJ_EV_META_TAC THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  REWRITE_TAC[rej_st; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_TAC THEN
  ABBREV_TAC `out = rej_out curlist inlist p` THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`] THEN
  ABBREV_TAC
   `chk = word((num_of_wordlist(inlist:(12 word)list) DIV 2 EXP (8 * 24 * p))
               MOD 2 EXP 384):384 word` THEN
  SUBGOAL_THEN
   `!j. j < 32
        ==> EL (16 * p + j) inlist =
            word_subword (chk:384 word) (12 * j,12):12 word`
  (LABEL_TAC "chunk") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "chk" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REJ_CHUNK_EL_384 THEN
    MAP_EVERY UNDISCH_TAC
     [`j < 32`; `8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 2) <= buflen`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `buflen - 24 * p < 2 EXP 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `buflen - 24 * p` THEN
  SUBGOAL_THEN `c < 2 EXP 64 /\ c < 225` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `c:num` THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`buf:int64`; `buflen:num`;
                `num_of_wordlist(inlist:(12 word)list)`;
                `24 * p`; `s0:x86state`] CHUNK_LOADS48) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `24 * (p + 2) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (1--14) THEN
  REJ_CANDIDATES_TAC 2 THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC REJ_PACK_FOLD48) (15--18) THEN
  REJ_MASK48_SIMPLIFY_TAC 18 THEN
  REJ_MASK_ABBREV_TAC 18 ["m0"; "m1"; "m2"; "m3"] THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n])
            (19--29) THEN
  REJ_INDEX_TAC `R9` 29 `m0:byte` THEN REJ_INDEX_TAC `R10` 29 `m1:byte` THEN
  REJ_INDEX_TAC `R11` 29 `m2:byte` THEN REJ_INDEX_TAC `RAX` 29 `m3:byte` THEN
  ASSUME_TAC(WORD_RULE `!x. word (1 * val(word x:int64)):int64 = word x`) THEN
  REJ_TAB_TAC "tab0" `m0:byte` 29 THEN REJ_TAB_TAC "tab1" `m1:byte` 29 THEN
  REJ_TAB_TAC "tab2" `m2:byte` 29 THEN REJ_TAB_TAC "tab3" `m3:byte` 29 THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (30--35) THEN
  REJ_GROUP_TAC `YMM0` 35 THEN REJ_GROUP_TAC `YMM7` 35 THEN
  REJ_LIST_ABBREV_TAC `YMM0` 35 ["lis0"; "lis2"] ["len0"; "len2"] THEN
  REJ_LIST_ABBREV_TAC `YMM7` 35 ["lis1"; "lis3"] ["len1"; "len3"] THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n])
            (36--39) THEN
  REJ_COUNT_TAC `R9` 39 `m0:byte` THEN REJ_COUNT_TAC `R10` 39 `m1:byte` THEN
  REJ_COUNT_TAC `R11` 39 `m2:byte` THEN REJ_COUNT_TAC `RAX` 39 `m3:byte` THEN
  REJ_COUNTS_TAC THEN
  SUBGOAL_THEN
   `len0 < 2 EXP 64 /\ len0 + len1 < 2 EXP 64 /\
    (len0 + len1) + len2 < 2 EXP 64 /\
    ((len0 + len1) + len2) + len3 < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`len0 <= 8`; `len1 <= 8`; `len2 <= 8`; `len3 <= 8`]
    THEN ARITH_TAC;
    ALL_TAC] THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [40] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ZX_JOIN]) THEN REJ_STORE_LEN_TAC THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [41] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ZX_JOIN;
    MATCH_MP REJ_ADDR_NORM (ASSUME `len0 < 2 EXP 64`)]) THEN
  REJ_STORE_LEN_TAC THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [42] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN
  VAL_INT64_TAC `len0 + len1` THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [43] THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_ASSOC;
    MATCH_MP REJ_ADDR_NORM (ASSUME `len0 + len1 < 2 EXP 64`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_SUM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_ASSOC]) THEN REJ_STORE_LEN_TAC THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [44] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN
  VAL_INT64_TAC `(len0 + len1) + len2` THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [45] THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_SUM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_ASSOC]) THEN REJ_STORE_LEN_TAC THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [46] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN
  VAL_INT64_TAC `((len0 + len1) + len2) + len3` THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (47--48) THEN
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
  SUBGOAL_THEN
   `c + len0 <= 248 /\ (c + len0) + len1 <= 248 /\
    ((c + len0) + len1) + len2 <= 248`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`c < 225`; `len0 <= 8`; `len1 <= 8`; `len2 <= 8`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[ASSUME
   `rej_out curlist inlist (p + 2) =
    APPEND (APPEND (APPEND (APPEND out lis0) lis1) lis2) lis3`;
   LENGTH_APPEND] THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`;
              ASSUME `LENGTH(lis0:int16 list) = len0`;
              ASSUME `LENGTH(lis1:int16 list) = len1`;
              ASSUME `LENGTH(lis2:int16 list) = len2`;
              ASSUME `LENGTH(lis3:int16 list) = len3`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    SUBGOAL_THEN `buflen - 24 * p = (buflen - 24 * (p + 2)) + 48`
    SUBST1_TAC THENL
     [UNDISCH_TAC `24 * (p + 2) <= buflen` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC];
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
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

(* The statement that some ev are the events from the label off, in the      *)
(* state after p chunks, to the end, for an initial list of length k.        *)

let rej_ev_to_end off p =
  subst [mk_small_numeral off,`off:num`; p,`p:num`]
  `?ev. !curlist e.
     LENGTH curlist = k
     ==> ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST mlkem_rej_uniform_alt_tmc) /\
               read RIP s = word(pc + off) /\
               rej_st res buf buflen table curlist inlist stk p s /\
               read events s = e)
          (\s. bytes_loaded s (word pc) (BUTLAST mlkem_rej_uniform_alt_tmc) /\
               read RIP s = word(pc + 0x284) /\
               rej_end res buf buflen table curlist inlist stk s /\
               read events s = APPEND ev e /\
               memaccess_inbounds ev
                [buf,buflen; table,4096; stk,32] [stk,32; res,512])
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(res,512); memory :> bytes(stk,32)])`;;

let REJ_EV_LOOP24_ALL = prove
 (`!res buf buflen table inlist stk pc t k p.
     8 * buflen = 12 * LENGTH(inlist:(12 word)list) /\ buflen = 24 * t /\
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x28f); (stk,32); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stk,32))
         [(word pc,0x28f); (buf,buflen); (table,4096)] /\
     p <= t
     ==> ?ev. !curlist e.
           LENGTH curlist = k
           ==> ensures x86
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x198) /\
                     rej_st res buf buflen table curlist inlist stk p s /\
                     read events s = e)
                (\s. bytes_loaded s (word pc)
                       (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                     read RIP s = word(pc + 0x284) /\
                     rej_end res buf buflen table curlist inlist stk s /\
                     read events s = APPEND ev e /\
                     memaccess_inbounds ev
                      [buf,buflen; table,4096; stk,32] [stk,32; res,512])
                (MAYCHANGE [RSP] ,,
                 MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [memory :> bytes(res,512);
                            memory :> bytes(stk,32)])`,
  let EXIT_TAC =
    MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                  `inlist:(12 word)list`; `stk:int64`; `pc:num`;
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
                  `inlist:(12 word)list`; `stk:int64`; `pc:num`;
                  `p:num`; `rej_len k (inlist:(12 word)list) p`]
      REJ_EV_LOOP24_DIRECT);
    MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                  `inlist:(12 word)list`; `stk:int64`; `pc:num`;
                  `p:num`; `rej_len k (inlist:(12 word)list) p`]
      REJ_EV_LOOP24_LAST)] THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_TAC `ev1:(uarch_event)list`) THEN
   REJ_EV_SEQ_TAC `0x198`
    `rej_st res buf buflen table curlist inlist stk (p + 1)`));;

let REJ_EV_LOOP48_ALL = prove
 (`!res buf buflen table inlist stk pc t k p.
     8 * buflen = 12 * LENGTH(inlist:(12 word)list) /\ buflen = 24 * t /\
     buflen < 2 EXP 64 /\
     ALL (nonoverlapping (res,512))
         [(word pc,0x28f); (stk,32); (buf,buflen); (table,4096)] /\
     ALL (nonoverlapping (stk,32))
         [(word pc,0x28f); (buf,buflen); (table,4096)] /\
     p <= t
     ==> (?ev. !curlist e.
            LENGTH curlist = k
            ==> ensures x86
                 (\s. bytes_loaded s (word pc)
                        (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                      read RIP s = word(pc + 0x185) /\
                      rej_st res buf buflen table curlist inlist stk p s /\
                      read events s = e)
                 (\s. bytes_loaded s (word pc)
                        (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                      read RIP s = word(pc + 0x284) /\
                      rej_end res buf buflen table curlist inlist stk s /\
                      read events s = APPEND ev e /\
                      memaccess_inbounds ev
                       [buf,buflen; table,4096; stk,32] [stk,32; res,512])
                 (MAYCHANGE [RSP] ,,
                  MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                  MAYCHANGE [memory :> bytes(res,512);
                             memory :> bytes(stk,32)])) /\
         (?ev. !curlist e.
            LENGTH curlist = k
            ==> ensures x86
                 (\s. bytes_loaded s (word pc)
                        (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                      read RIP s = word(pc + 0x82) /\
                      rej_st res buf buflen table curlist inlist stk p s /\
                      read events s = e)
                 (\s. bytes_loaded s (word pc)
                        (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                      read RIP s = word(pc + 0x284) /\
                      rej_end res buf buflen table curlist inlist stk s /\
                      read events s = APPEND ev e /\
                      memaccess_inbounds ev
                       [buf,buflen; table,4096; stk,32] [stk,32; res,512])
                 (MAYCHANGE [RSP] ,,
                  MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                  MAYCHANGE [memory :> bytes(res,512);
                             memory :> bytes(stk,32)]))`,
  let BLOCK_TAC th =
    MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                  `inlist:(12 word)list`; `stk:int64`; `pc:num`;
                  `p:num`; `rej_len k (inlist:(12 word)list) p`] th) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `ev1:(uarch_event)list`)
  and LOOP24_TAC =
    MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                  `inlist:(12 word)list`; `stk:int64`; `pc:num`;
                  `t:num`; `k:num`; `p:num`] REJ_EV_LOOP24_ALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `ev2:(uarch_event)list`) in

  (*** The body, then the rest from the test at its end for p + 2 ***)

  let BODY_REST_TAC =
    SUBGOAL_THEN (rej_ev_to_end 0x9c `p:num`)
     (X_CHOOSE_TAC `ev2:(uarch_event)list`) THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `d - 2` o check (is_forall o concl)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `p + 2`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `ev2:(uarch_event)list` o CONJUNCT1) THEN
      BLOCK_TAC REJ_EV_LOOP48_BODY THEN
      REJ_EV_SEQ_TAC `0x185`
       `rej_st res buf buflen table curlist inlist stk (p + 2)`;
      ALL_TAC] in

  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; LE_EXISTS] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` MP_TAC) THEN
  SUBGOAL_THEN `24 divides buflen` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MESON_TAC[DIVIDES_RMUL; DIVIDES_REFL]; ALL_TAC] THEN
  SPEC_TAC(`p:num`,`p:num`) THEN SPEC_TAC(`d:num`,`d:num`) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC
   `buflen < 24 * (p + 2) \/ 224 < rej_len k (inlist:(12 word)list) p`
  THENL
   [(*** To the loop by 24 bytes, from either test ***)

    LOOP24_TAC THEN CONJ_TAC THENL
     [BLOCK_TAC REJ_EV_LOOP48_EXIT_B;
      BLOCK_TAC REJ_EV_LOOP48_EXIT_A] THEN
    REJ_EV_SEQ_TAC `0x198`
     `rej_st res buf buflen table curlist inlist stk p`;

    (*** Through the body, from either test ***)

    BODY_REST_TAC THEN CONJ_TAC THENL
     [BLOCK_TAC REJ_EV_LOOP48_ENTER_B;
      BLOCK_TAC REJ_EV_LOOP48_ENTER_A] THEN
    REJ_EV_SEQ_TAC `0x9c`
     `rej_st res buf buflen table curlist inlist stk p`]);;

(* ------------------------------------------------------------------------- *)
(* The core, from the first instruction to the return, which it does not     *)
(* include, with the result and the events for some list depending only on   *)
(* the public values, then as a function of them.                            *)
(* ------------------------------------------------------------------------- *)

let REJ_FULL_CORE0 = prove
 (`!res n buf buflen table (inlist:(12 word)list) pc stackpointer.
      24 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      val n <= 256 /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x28f); (word_sub stackpointer (word 32),32);
           (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 32),32))
          [(word pc,0x28f); (buf,val buflen); (table,4096)]
      ==> ?ev. !e (curlist:int16 list).
            LENGTH curlist = val n
            ==> ensures x86
                 (\s. bytes_loaded s (word pc)
                        (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                      read RIP s = word pc /\
                      read RSP s = stackpointer /\
                      C_ARGUMENTS [res; n; buf; buflen; table] s /\
                      wordlist_from_memory(table,4096) s =
                      mlkem_rej_uniform_table /\
                      wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                      wordlist_from_memory(res,val n) s = curlist /\
                      read events s = e)
                 (\s. read RIP s = word(pc + 0x28e) /\
                      read RSP s = stackpointer /\
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
                             [buf,val buflen; table,4096;
                              word_sub stackpointer (word 32),32]
                             [word_sub stackpointer (word 32),32; res,512]))
                 (MAYCHANGE [RSP] ,,
                  MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                  MAYCHANGE [memory :> bytes(res,512);
                             memory :> bytes(word_sub stackpointer (word 32),
                                             32)])`,
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
                `inlist:(12 word)list`;
                `word_sub stackpointer (word 32):int64`; `pc:num`;
                `t:num`; `val(n:int64)`; `0`] REJ_EV_LOOP48_ALL) THEN
  ASM_REWRITE_TAC[LE_0] THEN
  DISCH_THEN(X_CHOOSE_TAC `ev:(uarch_event)list` o CONJUNCT2) THEN
  EXISTS_TAC `ev:(uarch_event)list` THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `curlist:int16 list`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o
    SPECL [`curlist:int16 list`; `e:(uarch_event)list`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
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
  ASM_REWRITE_TAC[] THEN GLOBALIZE_PRECONDITION_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x284`
   `\s. rej_end res buf buflen table curlist inlist
                (word_sub stackpointer (word 32)) s /\
        read events s = APPEND ev e /\
        memaccess_inbounds ev
         [buf,buflen; table,4096; word_sub stackpointer (word 32),32]
         [word_sub stackpointer (word 32),32; res,512]` THEN
  CONJ_TAC THENL
   [ENSURES_SEQUENCE_TAC `pc + 0x82`
     `\s. rej_st res buf buflen table curlist inlist
                 (word_sub stackpointer (word 32)) 0 s /\
          read events s = e` THEN
    CONJ_TAC THENL
     [(*** The setup, which has no events ***)

      REWRITE_TAC[rej_st] THEN
      ASM_SIMP_TAC[REJ_OUT_0; LE_REFL] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; WORD_VAL] THEN
      CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV) THEN
      ENSURES_INIT_TAC "s0" THEN
      MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                          SIMD_SIMPLIFY_TAC[]) (1--22) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

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
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (1--3) THEN
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
    (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
     EXISTS_TAC `ev:(uarch_event)list` THEN ASM_REWRITE_TAC[])]);;

let MLKEM_REJ_UNIFORM_ALT_CORE_FULL = prove
 (`exists f_events.
     forall e res n buf buflen table (curlist:int16 list)
            (inlist:(12 word)list) pc stackpointer.
      24 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      LENGTH curlist = val n /\ val n <= 256 /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x28f); (word_sub stackpointer (word 32),32);
           (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 32),32))
          [(word pc,0x28f); (buf,val buflen); (table,4096)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST mlkem_rej_uniform_alt_tmc) /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                C_ARGUMENTS [res; n; buf; buflen; table] s /\
                wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                wordlist_from_memory(res,val n) s = curlist /\
                read events s = e)
           (\s. read RIP s = word(pc + 0x28e) /\
                read RSP s = stackpointer /\
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
                       [buf,val buflen; table,4096;
                        word_sub stackpointer (word 32),32]
                       [word_sub stackpointer (word 32),32; res,512]))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`,
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

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, with the result as in the SUBROUTINE_CORRECT forms  *)
(* and the events in the same postcondition, the event list e first as for   *)
(* the other forms with f_events. The events f_events res n buf buflen table *)
(* inlist pc sp ra are the jump of the return and the load of the return     *)
(* address at sp after the events of the core, those of the blocks on the    *)
(* path through the loops, which is fixed by val buflen, val n and inlist:   *)
(* the jumps of the loop tests, the loads from buf + 24 * p and from the     *)
(* table at 16 times the acceptance mask of each group of 8 candidates, the  *)
(* stores to res + 2 * c for the count c so far and, for the last chunk, the *)
(* stores to the buffer at sp - 32 and the copy from it.                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_REJ_UNIFORM_ALT_NOIBT_SUBROUTINE_FULL = time prove
 (`exists f_events.
     forall e res n buf buflen table (curlist:int16 list)
            (inlist:(12 word)list) pc stackpointer returnaddress.
      24 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      LENGTH curlist = val n /\ val n <= 256 /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x28f); (word_sub stackpointer (word 32),40);
           (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 32),40))
          [(word pc,0x28f); (buf,val buflen); (table,4096)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_rej_uniform_alt_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [res; n; buf; buflen; table] s /\
                wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                wordlist_from_memory(res,val n) s = curlist /\
                read events s = e)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
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
                                   stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [buf,val buflen; table,4096;
                        word_sub stackpointer (word 32),40]
                       [word_sub stackpointer (word 32),32; res,512]))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`,
  let TWEAK_CONV =
    TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[wordlist_from_memory] in
  let execth = X86_MK_EXEC_RULE mlkem_rej_uniform_alt_tmc in

  (*** The events of the core, then the load of the return address and the
   *** jump to it
   ***)

  X_CHOOSE_THEN
   `core_events:int64->int64->int64->int64->int64->(12 word)list->num->
                int64->(uarch_event)list`
   (LABEL_TAC "core" o
    REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] o
    CONV_RULE TWEAK_CONV o X86_CORE_PROMOTE)
   MLKEM_REJ_UNIFORM_ALT_CORE_FULL THEN
  EXISTS_TAC
   `\(res:int64) (n:int64) (buf:int64) (buflen:int64) (table:int64)
     (inlist:(12 word)list) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
       CONS (EventJump (word(pc + 0x28f):int64,returnaddress))
        (CONS (EventLoad (stackpointer,8))
          (core_events res n buf buflen table inlist pc stackpointer))` THEN
  CONV_TAC TWEAK_CONV THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN] THEN
  STRIP_TAC THEN
  REMOVE_THEN "core" (MP_TAC o SPECL
   [`e:(uarch_event)list`; `res:int64`; `n:int64`; `buf:int64`;
    `buflen:int64`; `table:int64`; `curlist:int16 list`;
    `inlist:(12 word)list`; `pc:num`; `stackpointer:int64`]) THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC th) THEN
  X86_BIGSTEP_TAC execth "s1" THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  REPEAT STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC execth [2] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** The load of the return address is in the region from
   *** word_sub stackpointer (word 32), the events of the core within the
   *** smaller regions of the core theorem
   ***)

  EXISTS_TAC
   `CONS (EventJump (word(pc + 0x28f):int64,returnaddress:int64))
     (CONS (EventLoad (stackpointer:int64,8))
       ((core_events:int64->int64->int64->int64->int64->(12 word)list->
                     num->int64->(uarch_event)list)
        res n buf buflen table inlist pc stackpointer))` THEN
  ASM_REWRITE_TAC[APPEND] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV)
   [MESON[APPEND] `CONS (a:uarch_event) (CONS b l) = APPEND [a; b] l`] THEN
  GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN CONJ_TAC THENL
   [DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN
    DISJ2_TAC THEN DISJ2_TAC THEN
    SUBGOAL_THEN
     `stackpointer:int64 =
      word_add (word_sub stackpointer (word 32)) (word 32)`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th])
    THENL [CONV_TAC WORD_RULE; CONTAINED_TAC];
    DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC]);;

(* The same for the full code, with its IBT landing pad.                     *)

let MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL = time prove
 (`exists f_events.
     forall e res n buf buflen table (curlist:int16 list)
            (inlist:(12 word)list) pc stackpointer returnaddress.
      24 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      LENGTH curlist = val n /\ val n <= 256 /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x293); (word_sub stackpointer (word 32),40);
           (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 32),40))
          [(word pc,0x293); (buf,val buflen); (table,4096)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [res; n; buf; buflen; table] s /\
                wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                wordlist_from_memory(res,val n) s = curlist /\
                read events s = e)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
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
                                   stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [buf,val buflen; table,4096;
                        word_sub stackpointer (word 32),40]
                       [word_sub stackpointer (word 32),32; res,512]))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`,
  let TWEAK_CONV =
    TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[wordlist_from_memory] in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   (CONV_RULE TWEAK_CONV MLKEM_REJ_UNIFORM_ALT_NOIBT_SUBROUTINE_FULL)));;
