(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A client of the heap model of arm/proofs/heap.ml: heap_demo.S allocates   *)
(* 16 bytes, stores x and x + 1 in them, reads them back, frees the block    *)
(* and returns 2 * x + 1.                                                    *)
(*                                                                           *)
(* The theorem is about any allocator that meets the model (heap_model with  *)
(* any heap_ok, heap_fp, heap_room and stack bound stk <= 1024), called      *)
(* through the pointers in X1 and X2. It states correctness (the result, the *)
(* saved registers and SP restored), that the heap is as before (heap_ok H   *)
(* with the same H: no leak), and memory safety (the events of the run, the *)
(* allocator's included, read and write only the allocator's footprint and   *)
(* the stack). The frame has the footprint of H: the block is written while  *)
(* it is live and is inside heap_fp H. The stack below SP is in two parts:   *)
(* the 32 bytes of the function's frame, and 1024 bytes for the callees.     *)
(*                                                                           *)
(* The proof uses bstep (common/bstep.ml) throughout: blocks of code by      *)
(* ARM_BSTEP_TAC and the calls by ARM_HEAP_NEW_TAC and ARM_HEAP_DELETE_TAC.  *)
(* The facts about the block, the stack and the code cross the calls, and    *)
(* heap_ok crosses the code that writes the block and the stack, by the set  *)
(* facts of the hypotheses and of the contracts (common/footprint.ml).       *)
(* ========================================================================= *)

needs "arm/proofs/heap.ml";;

(**** print_literal_from_elf "arm/heap/heap_demo.o";;
 ****)

let heap_demo_mc = define_from_elf "heap_demo_mc" "arm/heap/heap_demo.o";;

let HEAP_DEMO_EXEC = ARM_MK_EXEC_RULE heap_demo_mc;;

let HEAP_DEMO_SUBROUTINE_CORRECT = prove
 (`!heap_ok heap_fp heap_room stk f_new f_delete.
     heap_model heap_ok heap_fp heap_room stk f_new f_delete
     ==> !pc sp x H returnaddress e x19 x20 x29.
          aligned 16 sp /\
          heap_room H 16 /\ stk <= 1024 /\
          DISJOINT (memrange(word_sub sp (word 1056),1056)) (heap_fp H) /\
          DISJOINT (memrange(word pc,LENGTH heap_demo_mc)) (heap_fp H) /\
          nonoverlapping (word pc,LENGTH heap_demo_mc)
                         (word_sub sp (word 1056),1056)
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) heap_demo_mc /\
                    read PC s = word pc /\ read SP s = sp /\
                    read X30 s = returnaddress /\
                    read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                    C_ARGUMENTS [x; f_new; f_delete] s /\
                    read events s = e /\
                    heap_ok H (read (memory :> footprint (heap_fp H)) s))
               (\s. read PC s = returnaddress /\ read SP s = sp /\
                    read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                    C_RETURN s = word_add x (word_add x (word 1)) /\
                    heap_ok H (read (memory :> footprint (heap_fp H)) s) /\
                    ?e2. read events s = APPEND e2 e /\
                         memaccess_inset e2
                          (heap_fp H UNION memrange(word_sub sp (word 1056),1056))
                          (heap_fp H UNION memrange(word_sub sp (word 1056),1056)))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [SP; X18; X19; X20; X29; X30] ,,
                MAYCHANGE [memory :> bytes(word_sub sp (word 1056),1024)] ,,
                MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)] ,,
                MAYCHANGE [memory :> footprint (heap_fp H)])`,
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst HEAP_DEMO_EXEC] THEN
  MAP_EVERY X_GEN_TAC
   [`heap_ok:(int64#num)list->(int64->byte)->bool`;
    `heap_fp:(int64#num)list->int64->bool`;
    `heap_room:(int64#num)list->num->bool`;
    `stk:num`; `f_new:int64`; `f_delete:int64`] THEN
  DISCH_THEN(fun model ->
    ASSUME_TAC model THEN X_GEN_TAC `pc:num` THEN
    WORD_FORALL_OFFSET_TAC 1056 THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    (* The frame and the arguments of the call of new                    *)
    ARM_BSTEP_TAC HEAP_DEMO_EXEC (1--7) THEN
    ARM_HEAP_NEW_TAC HEAP_DEMO_EXEC model "p" "s8" THEN
    (* Write and read the block, the call of delete                       *)
    ARM_BSTEP_TAC HEAP_DEMO_EXEC (9--16) THEN
    ARM_HEAP_DELETE_TAC HEAP_DEMO_EXEC model "s17" THEN
    (* The result and the epilogue                                         *)
    ARM_BSTEP_TAC HEAP_DEMO_EXEC (18--21) THEN
    BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    MEMACCESS_INSET_TAC));;

(* ------------------------------------------------------------------------- *)
(* The theorem for a real allocator: with heap_slab.S as new and delete      *)
(* (arm/heap/heap_slab.ml), and its empty heap, the hypotheses are met.      *)
(* ------------------------------------------------------------------------- *)

needs "arm/heap/heap_slab.ml";;

let HEAP_DEMO_SLAB = prove
 (`!pa pc sp x returnaddress e x19 x20 x29.
     16 divides pa /\ pa + 4608 < 2 EXP 64 /\
     aligned 16 sp /\
     DISJOINT (memrange(word_sub sp (word 1056),1056)) (heap_slab_fp pa []) /\
     DISJOINT (memrange(word pc,LENGTH heap_demo_mc)) (heap_slab_fp pa []) /\
     nonoverlapping (word pc,LENGTH heap_demo_mc) (word_sub sp (word 1056),1056)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) heap_demo_mc /\
               read PC s = word pc /\ read SP s = sp /\
               read X30 s = returnaddress /\
               read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
               C_ARGUMENTS [x; word pa; word(pa + 52)] s /\
               read events s = e /\
               heap_slab_ok pa []
                 (read (memory :> footprint (heap_slab_fp pa [])) s))
          (\s. read PC s = returnaddress /\ read SP s = sp /\
               read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
               C_RETURN s = word_add x (word_add x (word 1)) /\
               heap_slab_ok pa []
                 (read (memory :> footprint (heap_slab_fp pa [])) s) /\
               ?e2. read events s = APPEND e2 e /\
                    memaccess_inset e2
                     (heap_slab_fp pa [] UNION
                      memrange(word_sub sp (word 1056),1056))
                     (heap_slab_fp pa [] UNION
                      memrange(word_sub sp (word 1056),1056)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [SP; X18; X19; X20; X29; X30] ,,
           MAYCHANGE [memory :> bytes(word_sub sp (word 1056),1024)] ,,
           MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)] ,,
           MAYCHANGE [memory :> footprint (heap_slab_fp pa [])])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`pa:num`; `0`] HEAP_SLAB_MODEL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HEAP_DEMO_SUBROUTINE_CORRECT) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[LE_0] THEN MATCH_MP_TAC HEAP_SLAB_ROOM THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;
