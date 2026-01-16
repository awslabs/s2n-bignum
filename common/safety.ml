(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Definitions for the constant-time property and memory-safety property.    *)
(* ========================================================================= *)

needs "common/overlap.ml";;

(*** We define that an instruction raises an observable microarchitectural
 *** event if its cycles/power consumption/anything that can be observed by
 *** a side-channel attacker can vary depending on the inputs of
 *** the instruction. For example, instructions taking a constant number of
 *** cycles like ADD do not raise an observable event, whereas cond branch does.
 *** Its kinds (EventLoad/Store/...) describe the events distinguishable from
 *** each other by the attacker, and their parameters describe the values
 *** that are inputs and/or outputs of the instructions that will affect the
 *** observed cycles/etc.
 *** An opcode of instruction is not a parameter of the event, even if the
 *** number of taken cycles may depend on opcode. This relies on an assumption
 *** that a program is public information.
 *** One instruction can raise multiple events (e.g., one that reads PC from
 *** the memory and jumps to the address, even though this case will not exist
 *** in Arm).
 *** The formal semantics of instruction must emit a fixed list of events.
 *** It is not allowed for an instruction to raise one event when its input
 *** data is X and and two events when its input data is Y.
 *** Note: for x86, even if PUSH and POP instructions do memory access at RSP
 *** which is public information (stack address is public), these instructions
 *** must still explicitly raise EventLoad and EventStore because otherwise
 *** memory safety check will miss out-of-bounds stack access.
 ***)
let uarch_event_INDUCT, uarch_event_RECURSION = define_type
  "uarch_event =
    // (address, byte length)
    EventLoad (int64#num)
    // (address, byte length)
    | EventStore (int64#num)
    // (src pc, destination pc)
    | EventJump (int64#int64)

    // Instructions in X86 that are not in the DOIT list
    // (Data Operand Independent Timing Instructions)

    // PEXT (src1, src2, bitwidth)
    | EventX86PEXT (int64#int64#num)
    // POPCNT (src, bitwidth)
    | EventX86POPCNT (int64#num)
  ";;

(* ------------------------------------------------------------------------- *)
(* In-bound-ness of memory access                                            *)
(* ------------------------------------------------------------------------- *)

let memaccess_inbounds = new_definition `
  memaccess_inbounds (e2:(uarch_event)list) (readable_ranges:(int64#num)list)
                  (writable_ranges:(int64#num)list) <=>
    ALL (\(e:uarch_event). match e with
      | EventLoad (adr,sz) ->
        EX (\range. contained_modulo
            (2 EXP 64) (val adr, sz) (val (FST range), SND range))
           readable_ranges
      | EventStore (adr,sz) ->
        EX (\range. contained_modulo
            (2 EXP 64) (val adr, sz) (val (FST range), SND range))
           writable_ranges
      | _ -> true) e2`;;

let MEMACCESS_INBOUNDS_APPEND = prove(
  `forall e1 e2 rr wr. memaccess_inbounds (APPEND e1 e2) rr wr
    <=> memaccess_inbounds e1 rr wr /\ memaccess_inbounds e2 rr wr`,
  REWRITE_TAC[memaccess_inbounds;ALL_APPEND]);;

let MEMACCESS_INBOUNDS_MEM = prove(
  `forall e rr rr' wr wr'.
    ALL (\r. MEM r rr') rr /\ ALL (\w. MEM w wr') wr
    ==> memaccess_inbounds e rr wr
    ==> memaccess_inbounds e rr' wr'`,
  LIST_INDUCT_TAC THENL [
    REWRITE_TAC[memaccess_inbounds;ALL];

    CONV_TAC (ONCE_DEPTH_CONV
      (CONS_TO_APPEND_CONV)) THEN
    REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
    REPEAT STRIP_TAC THENL [

      UNDISCH_TAC `ALL (\(r:int64#num). MEM r rr') rr` THEN
      UNDISCH_TAC `ALL (\(w:int64#num). MEM w wr') wr` THEN
      UNDISCH_TAC `memaccess_inbounds [h] rr wr` THEN
      REWRITE_TAC[memaccess_inbounds;ALL] THEN
      SPEC_TAC (`(h:uarch_event)`,`(h:uarch_event)`) THEN
      MATCH_MP_TAC uarch_event_INDUCT THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL [
        REWRITE_TAC[FORALL_PAIR_THM] THEN
        REPEAT GEN_TAC THEN
        MESON_TAC [EX_SUBSET_LIST];

        REWRITE_TAC[FORALL_PAIR_THM] THEN
        REPEAT GEN_TAC THEN
        MESON_TAC [EX_SUBSET_LIST];
      ];

      ASM_METIS_TAC[];
    ]
  ]);;

let MEMACCESS_INBOUNDS_CONTAINED = prove(
  `forall e rr rr' wr wr'.
    ALL (\r. EX (\r'. contained r r') rr') rr /\
    ALL (\w. EX (\w'. contained w w') wr') wr
    ==> memaccess_inbounds e rr wr
    ==> memaccess_inbounds e rr' wr'`,
  LIST_INDUCT_TAC THENL [
    REWRITE_TAC[memaccess_inbounds;ALL];

    CONV_TAC (ONCE_DEPTH_CONV
      (CONS_TO_APPEND_CONV)) THEN
    REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
    REPEAT STRIP_TAC THENL [
      UNDISCH_TAC `ALL (\(r:int64#num). EX (\r'. contained r r') rr') rr` THEN
      UNDISCH_TAC `ALL (\(w:int64#num). EX (\w'. contained w w') wr') wr` THEN
      UNDISCH_TAC `memaccess_inbounds [h] rr wr` THEN
      REWRITE_TAC[memaccess_inbounds;ALL] THEN
      SPEC_TAC (`(h:uarch_event)`,`(h:uarch_event)`) THEN
      MATCH_MP_TAC uarch_event_INDUCT THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL [
        REWRITE_TAC[FORALL_PAIR_THM] THEN
        REPEAT GEN_TAC THEN
        DISCH_THEN (LABEL_TAC "H1") THEN
        DISCH_THEN (K ALL_TAC) THEN
        DISCH_THEN (LABEL_TAC "H2") THEN
        REMOVE_THEN "H1" (fun th1 -> REMOVE_THEN "H2"
          (fun th2 -> MP_TAC (CONJ th1 th2))) THEN
        MATCH_MP_TAC GEN_EX_SUBSET_LIST THEN
        REWRITE_TAC[FORALL_PAIR_THM] THEN
        MESON_TAC[contained; DIMINDEX_64;CONTAINED_MODULO_TRANS];

        REWRITE_TAC[FORALL_PAIR_THM] THEN
        REPEAT GEN_TAC THEN
        DISCH_THEN (LABEL_TAC "H1") THEN
        DISCH_THEN (LABEL_TAC "H2") THEN
        DISCH_THEN (K ALL_TAC) THEN
        REMOVE_THEN "H1" (fun th1 -> REMOVE_THEN "H2"
          (fun th2 -> MP_TAC (CONJ th1 th2))) THEN
        MATCH_MP_TAC GEN_EX_SUBSET_LIST THEN
        REWRITE_TAC[FORALL_PAIR_THM] THEN
        MESON_TAC[contained; DIMINDEX_64;CONTAINED_MODULO_TRANS];

      ];

      ASM_METIS_TAC[];
    ]
  ]);;

(* ------------------------------------------------------------------------- *)
(* Helper tactics for subroutines                                            *)
(* ------------------------------------------------------------------------- *)

let safety_print_log = ref false;;

(* Do ASSUME_TAC for safety proof which is `exists f_events. ...` after
  stripping the exists f_events part. *)
let ASSUME_CALLEE_SAFETY_TAC =
  let fresh_f_events_var_counter = ref 0 in
  fun (callee_safety_proof:thm) (asmname:string) :tactic ->
    let f_events_var_type = type_of (fst (dest_exists (concl callee_safety_proof))) in
    let f_events_callee =
      let _ = fresh_f_events_var_counter := 1 + !fresh_f_events_var_counter in
      mk_var("f_events_callee" ^ (string_of_int !fresh_f_events_var_counter),
              f_events_var_type) in
    (X_CHOOSE_THEN f_events_callee (LABEL_TAC asmname)) callee_safety_proof;;

(* Extension of ASSUME_CALLEE_SAFETY_TAC: given safety_th which is
  |- exists f_events. forall e x y ... . P e,
  split e into e_tail and e, and push e_tail into the innermost place.
  |- exists f_events. forall e x y ... e_tail. P (APPEND e_tail e)
*)
let ASSUME_CALLEE_SAFETY_TAILED_TAC =
  let append_lemma = MESON[APPEND_EXISTS]
    `(forall (e:(uarch_event)list). P e) <=>
      (forall e_tail e. P (APPEND e_tail e))` in
  fun (safety_th:thm) (name:string) ->
    let safety_th' = ONCE_REWRITE_RULE[append_lemma] safety_th in
    (* push e_tail to the innermost location *)
    let exarg,body = dest_exists (concl safety_th') in
    let args,body = strip_forall body in
    let args_rotated = (tl args) @ [hd args] in
    let eqth = MESON[](mk_eq(
        concl safety_th',
        mk_exists(exarg,list_mk_forall(args_rotated,body))))
      in
    let safety_th'' = ONCE_REWRITE_RULE[eqth] safety_th' in
    ASSUME_CALLEE_SAFETY_TAC safety_th'' name;;