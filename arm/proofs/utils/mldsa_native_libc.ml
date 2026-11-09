(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The combined contracts of the C library functions that mldsa-native       *)
(* calls, for correctness and for constant time and memory safety together   *)
(* (see utils/mlkem_native_libc_full.ml, which gives the one for memset).    *)
(* memcpy_full_contract is that for memcpy, and implies the separate         *)
(* contracts of utils/mlkem_native_libc.ml. For randombytes, whose           *)
(* correctness contract says nothing about the bytes written, the safety     *)
(* contract serves as the combined one: it implies the correctness           *)
(* contract.                                                                 *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native_libc_full.ml";;

let memcpy_full_contract = new_definition
 `memcpy_full_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    ?f_events.
      !e dst src len x returnaddress.
        nonoverlapping (dst,val len) (ea,el) /\
        nonoverlapping (dst,val len) (src,val len)
        ==> ensures arm
             (\s. read PC s = f /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [dst; src; len] s /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(src,val len)) s = x /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(dst,val len)) s = x /\
                  (?e2. read events s = APPEND e2 e /\
                        e2 = f_events dst src len returnaddress /\
                        memaccess_inbounds e2
                         [dst,val len; src,val len; ea,el] [dst,val len]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(dst,val len)])`;;

(* ------------------------------------------------------------------------- *)
(* The combined contract for memcpy implies the separate ones: for the       *)
(* correctness contract the events in the precondition can be any, and for   *)
(* the safety contract the source bytes are those of the initial state.      *)
(* ------------------------------------------------------------------------- *)

let MEMCPY_FULL_CONTRACT = prove
 (`!f ea el ev.
        memcpy_full_contract f ea el ev
        ==> memcpy_contract f ea el ev /\ memcpy_safety_contract f ea el ev`,
  REWRITE_TAC[memcpy_full_contract; memcpy_contract;
              memcpy_safety_contract] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC
   `f_events:int64->int64->int64->int64->(uarch_event)list`) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`dst:int64`; `src:int64`; `len:int64`; `x:num`;
                         `returnaddress:int64`] THEN
    DISCH_TAC THEN MATCH_MP_TAC ENSURES_ANY_EVENTS THEN
    X_GEN_TAC `e:(uarch_event)list` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`e:(uarch_event)list`; `dst:int64`;
      `src:int64`; `len:int64`; `x:num`; `returnaddress:int64`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_PREPOST) THEN
    SIMP_TAC[];
    EXISTS_TAC `f_events:int64->int64->int64->int64->(uarch_event)list` THEN
    MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `dst:int64`; `src:int64`;
                         `len:int64`; `returnaddress:int64`] THEN
    DISCH_TAC THEN REWRITE_TAC[ensures] THEN
    X_GEN_TAC `s0:armstate` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`e:(uarch_event)list`; `dst:int64`;
      `src:int64`; `len:int64`;
      `read (memory :> bytes(src,val(len:int64))) s0`;
      `returnaddress:int64`]) THEN
    ASM_REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s0:armstate`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[EVENTUALLY_MONO]
     `(!s:armstate. P s ==> Q s)
      ==> eventually arm P s0 ==> eventually arm Q s0`) THEN
    SIMP_TAC[]]);;

let RANDOMBYTES_SAFETY_CONTRACT = prove
 (`!f ea el ev.
        randombytes_safety_contract f ea el ev
        ==> randombytes_contract f ea el ev`,
  REWRITE_TAC[randombytes_safety_contract; randombytes_contract] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC
   `f_events:int64->int64->int64->(uarch_event)list`) THEN
  MAP_EVERY X_GEN_TAC [`buf:int64`; `len:int64`; `returnaddress:int64`] THEN
  DISCH_TAC THEN MATCH_MP_TAC ENSURES_ANY_EVENTS THEN
  X_GEN_TAC `e:(uarch_event)list` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`e:(uarch_event)list`; `buf:int64`;
    `len:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_PREPOST) THEN
  SIMP_TAC[]);;
