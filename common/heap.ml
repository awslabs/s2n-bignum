(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* An abstract heap: the part of the model of an external allocator that     *)
(* does not depend on the instruction set. The contracts of its functions    *)
(* are in arm/proofs/heap.ml.                                                *)
(*                                                                           *)
(* The allocator is described by three parameters, about which client        *)
(* theorems know only what heap_props here and the contracts say:            *)
(*                                                                           *)
(*  - heap_ok H m, its invariant, for H : (int64 # num) list the live        *)
(*    blocks (address, size), a ghost state, and m the memory at its         *)
(*    footprint, read (memory :> footprint (heap_fp H)) s; so the invariant  *)
(*    depends only on the memory in heap_fp H, and a client that writes      *)
(*    outside heap_fp H keeps it;                                            *)
(*  - heap_fp H, the addresses that the allocator owns when H is live: its   *)
(*    code and data, the free memory, and any memory it may get later (as    *)
(*    from mmap); it is a function of H only, not of the state;              *)
(*  - heap_room H n, "an allocation of n bytes succeeds when H is live", a   *)
(*    function of H and n only.                                              *)
(*                                                                           *)
(* heap_props says that when heap_ok H holds the blocks of H are well formed *)
(* (nonzero addresses, no wrap-around, distinct addresses, pairwise          *)
(* disjoint) and outside heap_fp H. A client whose inputs are live blocks    *)
(* gets from it that they are outside heap_fp H (HEAP_BLOCK_DISJOINT).       *)
(* ========================================================================= *)

needs "common/footprint.ml";;

(* ------------------------------------------------------------------------- *)
(* Lists of live blocks.                                                     *)
(* ------------------------------------------------------------------------- *)

(* The blocks without the first one at the address p: the effect of freeing  *)
(* p. Allocation puts the new block in front, so a block that is allocated  *)
(* and then freed leaves H as it was: heap_remove p (CONS (p,n) H) = H.     *)

let heap_remove = define
 `(heap_remove (p:int64) [] = []) /\
  (heap_remove p (CONS (b:int64#num) t) =
     if FST b = p then t else CONS b (heap_remove p t))`;;

let heap_blocks = new_definition
 `heap_blocks (H:(int64#num)list) <=>
    ALL (\(p,n). ~(p = word 0) /\ val p + n < 2 EXP 64) H /\
    PAIRWISE (\(p,m) (q,n). ~(p = q) /\ DISJOINT (memrange(p,m)) (memrange(q,n)))
             H`;;

let heap_props = new_definition
 `heap_props (heap_ok:(int64#num)list->(int64->byte)->bool)
             (heap_fp:(int64#num)list->int64->bool) <=>
    !H m. heap_ok H m
          ==> heap_blocks H /\
              ALL (\(p,n). DISJOINT (memrange(p,n)) (heap_fp H)) H`;;

let HEAP_REMOVE_CONS = prove
 (`!(p:int64) n H. heap_remove p (CONS (p,n) H) = H`,
  REWRITE_TAC[heap_remove]);;

let MEM_HEAP_REMOVE = prove
 (`!(b:int64#num) p H. MEM b (heap_remove p H) ==> MEM b H`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[heap_remove; MEM] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[MEM] THEN ASM_MESON_TAC[]);;

(* With distinct addresses, freeing p removes exactly the blocks at p.       *)

let MEM_HEAP_REMOVE_DISTINCT = prove
 (`!(b:int64#num) p H.
        PAIRWISE (\b c. ~(FST b = FST c)) H
        ==> (MEM b (heap_remove p H) <=> MEM b H /\ ~(FST b = p))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[heap_remove; MEM; PAIRWISE; GSYM ALL_MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[MEM] THEN ASM_CASES_TAC `b:int64#num = h` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let HEAP_BLOCKS_DISTINCT = prove
 (`!H. heap_blocks H ==> PAIRWISE (\b c. ~(FST b = FST c)) H`,
  REWRITE_TAC[heap_blocks] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    PAIRWISE_IMPLIES)) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP_TAC[]);;

let HEAP_BLOCKS_MEM = prove
 (`!H p n. heap_blocks H /\ MEM (p,n) H
           ==> ~(p = word 0) /\ val p + n < 2 EXP 64`,
  REWRITE_TAC[heap_blocks; GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `(p:int64,n:num)`) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let HEAP_BLOCK_DISJOINT = prove
 (`!(heap_ok:(int64#num)list->(int64->byte)->bool) heap_fp H m p n.
        heap_props heap_ok heap_fp /\ heap_ok H m /\ MEM (p,n) H
        ==> DISJOINT (memrange(p,n)) (heap_fp H)`,
  REWRITE_TAC[heap_props; GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`H:(int64#num)list`; `m:int64->byte`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(p:int64,n:num)` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[]);;

let HEAP_PROPS_BLOCKS = prove
 (`!(heap_ok:(int64#num)list->(int64->byte)->bool) heap_fp H m.
        heap_props heap_ok heap_fp /\ heap_ok H m ==> heap_blocks H`,
  REWRITE_TAC[heap_props] THEN MESON_TAC[]);;

(* The facts about a block (p,n) just allocated with H live before: it is    *)
(* outside the new footprint; and a region outside heap_fp H is outside the  *)
(* new footprint and does not overlap the block.                             *)

let HEAP_NEW_BLOCK_DISJOINT = prove
 (`!(heap_ok:(int64#num)list->(int64->byte)->bool) heap_fp H m p n.
        heap_props heap_ok heap_fp /\ heap_ok (CONS (p,n) H) m
        ==> DISJOINT (memrange(p,n)) (heap_fp (CONS (p,n) H))`,
  MESON_TAC[HEAP_BLOCK_DISJOINT; MEM]);;

(* heap_ok H crosses any step whose frame keeps the footprint, such as code  *)
(* that writes only outside heap_fp H: with the classic tactics the frame    *)
(* condition is proved by MAYCHANGE_KEEPS_TAC (bstep moves the fact itself). *)

let HEAP_OK_KEEP = prove
 (`!(c:(S,int64->byte)component)
    (heap_ok:(int64#num)list->(int64->byte)->bool) heap_fp H R s s'.
        heap_ok H (read (c :> footprint (heap_fp H)) s) /\
        (!s s'. R s s' ==> read (c :> footprint (heap_fp H)) s' =
                           read (c :> footprint (heap_fp H)) s) /\
        R s s'
        ==> heap_ok H (read (c :> footprint (heap_fp H)) s')`,
  MESON_TAC[]);;

(* Freeing q keeps the blocks at other addresses.                            *)

let MEM_HEAP_REMOVE_OTHER = prove
 (`!(b:int64#num) q H. MEM b H /\ ~(FST b = q) ==> MEM b (heap_remove q H)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[heap_remove; MEM] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM] THEN ASM_MESON_TAC[]);;
