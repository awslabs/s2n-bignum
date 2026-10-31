(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A combined contract for memset, for correctness and for constant time and *)
(* memory safety together, and its relation to the separate contracts in     *)
(* mlkem_native_libc.ml.                                                     *)
(*                                                                           *)
(* Callers whose events depend on the result of a call need the result and   *)
(* the events of the call at the same time. A correctness contract and a     *)
(* safety contract are separate ensures statements, whose postconditions     *)
(* might hold at different points of an execution, so they cannot be         *)
(* combined after the fact: the combined contract states both in one ensures *)
(* statement, and it implies the two separate contracts, so that it can      *)
(* replace them as the hypothesis of the theorems for the callers. This is   *)
(* needed for memset, which zeroes the contexts for the fourfold SHAKE128    *)
(* functions used in the rejection sampling of the matrix.                   *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native_libc.ml";;

let memset_full_contract = new_definition
 `memset_full_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    ?f_events.
      !e dst c len returnaddress.
        nonoverlapping (dst,val len) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [dst; c; len] s /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < val len
                       ==> read (memory :> bytes8(word_add dst (word i))) s =
                           word_zx c) /\
                  (?e2. read events s = APPEND e2 e /\
                        e2 = f_events dst c len returnaddress /\
                        memaccess_inbounds e2 [dst,val len; ea,el]
                                              [dst,val len]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(dst,val len)])`;;

(* ------------------------------------------------------------------------- *)
(* The combined contract implies the separate ones: the events in the        *)
(* precondition can be any, and the postconditions are weakened.             *)
(* ------------------------------------------------------------------------- *)

let ENSURES_ANY_EVENTS = prove
 (`!(P:armstate->bool) Q R.
        (!e. ensures arm (\s. P s /\ read events s = e) Q R)
        ==> ensures arm P Q R`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

let ENSURES_WEAKEN_PREPOST = MESON[ENSURES_PREPOSTCONDITION_THM]
 `ensures step P Q C
  ==> (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x)
      ==> ensures step P' Q' C`;;

let MEMSET_FULL_CONTRACT = prove
 (`!f ea el ev.
        memset_full_contract f ea el ev
        ==> memset_contract f ea el ev /\ memset_safety_contract f ea el ev`,
  REWRITE_TAC[memset_full_contract; memset_contract;
              memset_safety_contract] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC
   `f_events:int64->int64->int64->int64->(uarch_event)list`) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`dst:int64`; `c:int64`; `len:int64`;
                         `returnaddress:int64`] THEN
    DISCH_TAC THEN MATCH_MP_TAC ENSURES_ANY_EVENTS THEN
    X_GEN_TAC `e:(uarch_event)list` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`e:(uarch_event)list`; `dst:int64`;
      `c:int64`; `len:int64`; `returnaddress:int64`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_PREPOST) THEN
    SIMP_TAC[];
    EXISTS_TAC `f_events:int64->int64->int64->int64->(uarch_event)list` THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`e:(uarch_event)list`; `dst:int64`;
      `c:int64`; `len:int64`; `returnaddress:int64`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_PREPOST) THEN
    SIMP_TAC[]]);;
