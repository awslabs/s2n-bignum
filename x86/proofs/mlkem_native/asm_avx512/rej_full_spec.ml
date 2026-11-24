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

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/rej_uniform_alt_VARIABLE_TIME_spec.ml";;

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

let LENGTH_REJ_OUT_LEN_STMT =
  `!curlist inlist p.
        LENGTH(rej_out curlist inlist p) =
        rej_len (LENGTH curlist) inlist p`;;

let LENGTH_REJ_OUT_LEN = assume_spec LENGTH_REJ_OUT_LEN_STMT;;

(* ------------------------------------------------------------------------- *)
(* The sequencing of two blocks, the events of the second being added to     *)
(* those of the first.                                                       *)
(* ------------------------------------------------------------------------- *)

let ENSURES_FALSE_PRE = prove
 (`!(step:A->A->bool) Q C. ensures step (\s. F) Q C`,
  REWRITE_TAC[ensures]);;

let REJ_EV_SEQ_STMT =
  `!res stk (pc:num) off1 off2 off3 (P:x86state->bool) Q S
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
           MAYCHANGE [memory :> bytes(res,512); memory :> bytes(stk,32)])`;;

let REJ_EV_SEQ = assume_spec REJ_EV_SEQ_STMT;;

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

let rej_ev_allowed = par_local_ref (fun () -> ([]:(term * term list) list));;

let rej_ev_current = par_local_ref (fun () -> ([]:term list));;

let REJ_EV_META_TAC:tactic =
  let n = ref 0 in
  fun (asl,w) ->
    let v,_ = dest_exists w in
    let fvs = freesl (w::(map (concl o snd) asl)) in
    let _ = n := !n + 1 in
    let mv = mk_var("ev_" ^ string_of_int !n,type_of v) in
    let _ = (rej_ev_allowed ()) := (mv,fvs)::(!(rej_ev_allowed ())) in
    X_META_EXISTS_TAC mv (asl,w);;

(* The assumptions t = v abbreviating t as a variable v that is not public   *)

let rej_abbrevs asl =
  mapfilter (fun (_,th) ->
    let c = concl th in
    if is_eq c && is_var(rhs c) && not(mem (rhs c) (!(rej_ev_current ()))) &&
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
    let _ = (rej_ev_current ()) := assoc mv (!(rej_ev_allowed ())) in
    let abbrevs = map SYM (rej_abbrevs asl) in
    if l = rand r then
      MATCH_MP_TAC nilth THEN CONJ_TAC THENL
       [REFL_TAC; SAFE_UNIFY_REFL_TAC (rej_ev_current ()) (ref [])]
    else
      CONV_TAC(LAND_CONV CONS_TO_APPEND_CONV) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC(LAND_CONV(PURE_REWRITE_CONV abbrevs)) THEN
      SAFE_UNIFY_REFL_TAC (rej_ev_current ()) (ref []));;

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

let REJ_EV_LOOP24_EXIT_STMT =
  `!res buf buflen table inlist stk pc p c.
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
                            memory :> bytes(stk,32)])`;;

let REJ_EV_LOOP24_EXIT = assume_spec REJ_EV_LOOP24_EXIT_STMT;;

let REJ_EV_LOOP48_EXIT_A_STMT =
  `!res buf buflen table inlist stk pc p c.
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
                            memory :> bytes(stk,32)])`;;

let REJ_EV_LOOP48_EXIT_A = assume_spec REJ_EV_LOOP48_EXIT_A_STMT;;

let REJ_EV_LOOP48_ENTER_A_STMT =
  `!res buf buflen table inlist stk pc p c.
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
                            memory :> bytes(stk,32)])`;;

let REJ_EV_LOOP48_ENTER_A = assume_spec REJ_EV_LOOP48_ENTER_A_STMT;;

let REJ_EV_LOOP48_EXIT_B_STMT =
  `!res buf buflen table inlist stk pc p c.
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
                            memory :> bytes(stk,32)])`;;

let REJ_EV_LOOP48_EXIT_B = assume_spec REJ_EV_LOOP48_EXIT_B_STMT;;

let REJ_EV_LOOP48_ENTER_B_STMT =
  `!res buf buflen table inlist stk pc p c.
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
                            memory :> bytes(stk,32)])`;;

let REJ_EV_LOOP48_ENTER_B = assume_spec REJ_EV_LOOP48_ENTER_B_STMT;;

(* ------------------------------------------------------------------------- *)
(* The loop by 24 bytes when the accepted numbers are stored directly.       *)
(* ------------------------------------------------------------------------- *)

let REJ_EV_LOOP24_DIRECT_STMT =
  `!res buf buflen table inlist stk pc p c.
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
                            memory :> bytes(stk,32)])`;;

let REJ_EV_LOOP24_DIRECT = assume_spec REJ_EV_LOOP24_DIRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The final copy through the buffer on the stack, of the first m of the     *)
(* list L of the accepted numbers from the last 24 bytes: the entry to the   *)
(* copy loop, a step back to its start, the last step and the branch back to *)
(* the loop by 24 bytes.                                                     *)
(* ------------------------------------------------------------------------- *)

let REJ_EV_COPY_ENTRY_STMT =
  `!res buf buflen table inlist stk pc p c L m.
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
                            memory :> bytes(stk,32)])`;;

let REJ_EV_COPY_ENTRY = assume_spec REJ_EV_COPY_ENTRY_STMT;;

let REJ_EV_COPY_STEP_STMT =
  `!res buf buflen table inlist stk pc p c L m i.
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
                            memory :> bytes(stk,32)])`;;

let REJ_EV_COPY_STEP = assume_spec REJ_EV_COPY_STEP_STMT;;

let REJ_EV_COPY_LAST_STMT =
  `!res buf buflen table inlist stk pc p c L m i.
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
                            memory :> bytes(stk,32)])`;;

let REJ_EV_COPY_LAST = assume_spec REJ_EV_COPY_LAST_STMT;;

(* The copy loop and the whole final copy                                    *)

let REJ_DOWN_INDUCT_STMT =
  `!P m. (!i. i + 1 = m ==> P i) /\ (!i. i + 1 < m /\ P(i + 1) ==> P i)
         ==> !i. i < m ==> P i`;;

let REJ_DOWN_INDUCT = assume_spec REJ_DOWN_INDUCT_STMT;;

let REJ_EV_COPY_LOOP_STMT =
  `!res buf buflen table inlist stk pc p c L m.
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
                                    memory :> bytes(stk,32)])`;;

let REJ_EV_COPY_LOOP = assume_spec REJ_EV_COPY_LOOP_STMT;;

let REJ_EV_LASTCOPY_STMT =
  `!res buf buflen table inlist stk pc p c L m.
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
                            memory :> bytes(stk,32)])`;;

let REJ_EV_LASTCOPY = assume_spec REJ_EV_LASTCOPY_STMT;;

(* ------------------------------------------------------------------------- *)
(* The loop by 24 bytes when there may not be room for all 16 numbers: the   *)
(* two groups go to the buffer on the stack, from which as many as there is  *)
(* room for are copied.                                                      *)
(* ------------------------------------------------------------------------- *)

let REJ_EV_LOOP24_HEAD_STMT =
  `!res buf buflen table inlist stk pc p c L m.
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
                            memory :> bytes(stk,32)])`;;

let REJ_EV_LOOP24_HEAD = assume_spec REJ_EV_LOOP24_HEAD_STMT;;

let REJ_EV_LOOP24_LAST_STMT =
  `!res buf buflen table inlist stk pc p c.
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
                            memory :> bytes(stk,32)])`;;

let REJ_EV_LOOP24_LAST = assume_spec REJ_EV_LOOP24_LAST_STMT;;

(* ------------------------------------------------------------------------- *)
(* The loop by 48 bytes, the 32 numbers stored directly.                     *)
(* ------------------------------------------------------------------------- *)

let REJ_EV_LOOP48_BODY_STMT =
  `!res buf buflen table inlist stk pc p c.
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
                            memory :> bytes(stk,32)])`;;

let REJ_EV_LOOP48_BODY = assume_spec REJ_EV_LOOP48_BODY_STMT;;

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

let REJ_EV_LOOP24_ALL_STMT =
  `!res buf buflen table inlist stk pc t k p.
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
                            memory :> bytes(stk,32)])`;;

let REJ_EV_LOOP24_ALL = assume_spec REJ_EV_LOOP24_ALL_STMT;;

let REJ_EV_LOOP48_ALL_STMT =
  `!res buf buflen table inlist stk pc t k p.
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
                             memory :> bytes(stk,32)]))`;;

let REJ_EV_LOOP48_ALL = assume_spec REJ_EV_LOOP48_ALL_STMT;;

(* ------------------------------------------------------------------------- *)
(* The core, from the first instruction to the return, which it does not     *)
(* include, with the result and the events for some list depending only on   *)
(* the public values, then as a function of them.                            *)
(* ------------------------------------------------------------------------- *)

let REJ_FULL_CORE0_STMT =
  `!res n buf buflen table (inlist:(12 word)list) pc stackpointer.
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
                                             32)])`;;

let REJ_FULL_CORE0 = assume_spec REJ_FULL_CORE0_STMT;;

let MLKEM_REJ_UNIFORM_ALT_CORE_FULL_STMT =
  `exists f_events.
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
                       memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_REJ_UNIFORM_ALT_CORE_FULL = assume_spec MLKEM_REJ_UNIFORM_ALT_CORE_FULL_STMT;;

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

let MLKEM_REJ_UNIFORM_ALT_NOIBT_SUBROUTINE_FULL_STMT =
  `exists f_events.
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
                       memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_REJ_UNIFORM_ALT_NOIBT_SUBROUTINE_FULL = assume_spec MLKEM_REJ_UNIFORM_ALT_NOIBT_SUBROUTINE_FULL_STMT;;

(* The same for the full code, with its IBT landing pad.                     *)

let MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL_STMT =
  `exists f_events.
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
                       memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL = assume_spec MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL_STMT;;
