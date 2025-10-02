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
