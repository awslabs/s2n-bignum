(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A client of the heap model with two live blocks: heap_demo2.S allocates a *)
(* and stores x in it, allocates b and stores a[0] + 1 in it, frees a, reads *)
(* b, frees b and returns x + 1. The fact about a crosses the second call of *)
(* new and the fact about b crosses the call of delete for a; the heap ends  *)
(* as it began.                                                              *)
(*                                                                           *)
(* The second allocation is made with (a,16) live, at an address a that the  *)
(* theorem cannot name, so its room is a hypothesis for all addresses:       *)
(* !p. heap_room (CONS (p,16) H) 16.                                         *)
(* ========================================================================= *)

needs "arm/proofs/heap.ml";;

(**** print_literal_from_elf "arm/heap/heap_demo2.o";;
 ****)

let heap_demo2_mc = define_from_elf "heap_demo2_mc" "arm/heap/heap_demo2.o";;

let HEAP_DEMO2_EXEC = ARM_MK_EXEC_RULE heap_demo2_mc;;

let HEAP_DEMO2_SUBROUTINE_CORRECT = prove
 (`!heap_ok heap_fp heap_room stk f_new f_delete.
     heap_model heap_ok heap_fp heap_room stk f_new f_delete
     ==> !pc sp x H returnaddress e x19 x20 x21 x22 x29.
          aligned 16 sp /\
          heap_room H 16 /\ (!p. heap_room (CONS (p,16) H) 16) /\
          stk <= 1024 /\
          DISJOINT (memrange(word_sub sp (word 1072),1072)) (heap_fp H) /\
          DISJOINT (memrange(word pc,LENGTH heap_demo2_mc)) (heap_fp H) /\
          nonoverlapping (word pc,LENGTH heap_demo2_mc)
                         (word_sub sp (word 1072),1072)
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) heap_demo2_mc /\
                    read PC s = word pc /\ read SP s = sp /\
                    read X30 s = returnaddress /\
                    read X19 s = x19 /\ read X20 s = x20 /\
                    read X21 s = x21 /\ read X22 s = x22 /\ read X29 s = x29 /\
                    C_ARGUMENTS [x; f_new; f_delete] s /\
                    read events s = e /\
                    heap_ok H (read (memory :> footprint (heap_fp H)) s))
               (\s. read PC s = returnaddress /\ read SP s = sp /\
                    read X19 s = x19 /\ read X20 s = x20 /\
                    read X21 s = x21 /\ read X22 s = x22 /\ read X29 s = x29 /\
                    C_RETURN s = word_add x (word 1) /\
                    heap_ok H (read (memory :> footprint (heap_fp H)) s) /\
                    ?e2. read events s = APPEND e2 e /\
                         memaccess_inset e2
                          (heap_fp H UNION memrange(word_sub sp (word 1072),1072))
                          (heap_fp H UNION memrange(word_sub sp (word 1072),1072)))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [SP; X18; X19; X20; X21; X22; X29; X30] ,,
                MAYCHANGE [memory :> bytes(word_sub sp (word 1072),1024)] ,,
                MAYCHANGE [memory :> bytes(word_sub sp (word 48),48)] ,,
                MAYCHANGE [memory :> footprint (heap_fp H)])`,
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst HEAP_DEMO2_EXEC] THEN
  MAP_EVERY X_GEN_TAC
   [`heap_ok:(int64#num)list->(int64->byte)->bool`;
    `heap_fp:(int64#num)list->int64->bool`;
    `heap_room:(int64#num)list->num->bool`;
    `stk:num`; `f_new:int64`; `f_delete:int64`] THEN
  DISCH_THEN(fun model ->
    ASSUME_TAC model THEN X_GEN_TAC `pc:num` THEN
    WORD_FORALL_OFFSET_TAC 1072 THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    (* a = alloc(16); a[0] = x                                              *)
    ARM_BSTEP_TAC HEAP_DEMO2_EXEC (1--9) THEN
    ARM_HEAP_NEW_TAC HEAP_DEMO2_EXEC model "a" "s10" THEN
    ARM_BSTEP_TAC HEAP_DEMO2_EXEC (11--15) THEN
    (* b = alloc(16), with the room for it at the address a               *)
    FIRST_X_ASSUM(ASSUME_TAC o SPEC `a:int64` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> t = `heap_room:(int64#num)list->num->bool`))
                           (concl th))) THEN
    ARM_HEAP_NEW_TAC HEAP_DEMO2_EXEC model "b" "s16" THEN
    (* b[0] = a[0] + 1; release(a)                                         *)
    ARM_BSTEP_TAC HEAP_DEMO2_EXEC (17--23) THEN
    ARM_HEAP_DELETE_TAC HEAP_DEMO2_EXEC model "s24" THEN
    (* r = b[0]; release(b)                                                *)
    ARM_BSTEP_TAC HEAP_DEMO2_EXEC (25--28) THEN
    ARM_HEAP_DELETE_TAC HEAP_DEMO2_EXEC model "s29" THEN
    (* return r                                                            *)
    ARM_BSTEP_TAC HEAP_DEMO2_EXEC (30--34) THEN
    BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    MEMACCESS_INSET_TAC));;
