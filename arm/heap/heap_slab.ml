(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The non-vacuity of the heap model of arm/proofs/heap.ml: the allocator    *)
(* heap_slab.S (64 slots of 64 bytes, a bitmap of the slots in use) meets    *)
(* heap_model, for an invariant that holds after loading (the code in place *)
(* and the bitmap zero) and a heap_room that allows any allocation of at     *)
(* most 64 bytes while fewer than 64 blocks are live.                        *)
(*                                                                           *)
(* With the code at pc (16-byte aligned, the 4608 bytes of code and data     *)
(* not wrapping around):                                                     *)
(*                                                                           *)
(*  - heap_slab_fp pc H: the code, the bitmap, and the slots minus the live  *)
(*    blocks;                                                                *)
(*  - heap_slab_ok pc H m: the code is in m, every block of H is a slot with *)
(*    a size of at most 64 and the addresses are distinct, and bit i of the  *)
(*    bitmap is set iff slot i is the address of a block of H;               *)
(*  - heap_slab_room H n: n <= 64 and LENGTH H < 64.                         *)
(*                                                                           *)
(* The proofs of new and delete are bstep runs of the code; the frame        *)
(* clause MAYCHANGE [memory :> footprint (heap_slab_fp pc H)] takes the      *)
(* store to the bitmap, inside the footprint (common/footprint.ml).          *)
(* ========================================================================= *)

needs "arm/proofs/heap.ml";;

(**** print_literal_from_elf "arm/heap/heap_slab.o";;
 ****)

let heap_slab_mc = define_from_elf "heap_slab_mc" "arm/heap/heap_slab.o";;

let HEAP_SLAB_EXEC = ARM_MK_EXEC_RULE heap_slab_mc;;

(* ------------------------------------------------------------------------- *)
(* The model.                                                                *)
(* ------------------------------------------------------------------------- *)

let heap_slab_slot = new_definition
 `heap_slab_slot pc i:int64 = word_add (word pc) (word (512 + 64 * i))`;;

let heap_slab_fp = new_definition
 `heap_slab_fp pc (H:(int64#num)list) =
    memrange(word pc,96) UNION memrange(word_add (word pc) (word 256),8) UNION
    (memrange(word_add (word pc) (word 512),4096) DIFF
     {x | ?b. MEM b H /\ x IN memrange b})`;;

let heap_slab_ok = new_definition
 `heap_slab_ok pc (H:(int64#num)list) (m:int64->byte) <=>
    read (bytelist(word pc,96)) m = heap_slab_mc /\
    ALL (\(p,n). ?i. i < 64 /\ p = heap_slab_slot pc i /\ n <= 64) H /\
    PAIRWISE (\b c. ~(FST b = FST c)) H /\
    !i. i < 64
        ==> (bit i (read (bytes64 (word_add (word pc) (word 256))) m) <=>
             MEM (heap_slab_slot pc i) (MAP FST H))`;;

let heap_slab_room = new_definition
 `heap_slab_room (H:(int64#num)list) n <=> n <= 64 /\ LENGTH H < 64`;;

(* ------------------------------------------------------------------------- *)
(* The layout.                                                               *)
(* ------------------------------------------------------------------------- *)

let WORD_ADD_WORD_PC = prove
 (`!pc k. word_add (word pc) (word k):int64 = word(pc + k)`,
  REWRITE_TAC[WORD_ADD]);;

let IN_MEMRANGE_WORD = prove
 (`!a k x. a + k <= 2 EXP 64
           ==> (x IN memrange(word a:int64,k) <=>
                ?i. i < k /\ val x = a + i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_MEMRANGE; GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `i < k` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  TRY(MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC) THEN
  ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let DISJOINT_MEMRANGE_WORD = prove
 (`!a k b l. (a + k <= b \/ b + l <= a) /\
             a + k <= 2 EXP 64 /\ b + l <= 2 EXP 64
             ==> DISJOINT (memrange(word a:int64,k)) (memrange(word b,l))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_MEMRANGE_WORD] THEN
  ASM_ARITH_TAC);;

let SUBSET_MEMRANGE_WORD = prove
 (`!a k b l. b <= a /\ a + k <= b + l
             ==> memrange(word a:int64,k) SUBSET memrange(word b,l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word a:int64 = word_add (word b) (word(a - b))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC MEMRANGE_OFFSET_SUBSET THEN ASM_ARITH_TAC]);;

let HEAP_SLAB_SLOT = prove
 (`!pc i. heap_slab_slot pc i = word(pc + 512 + 64 * i)`,
  REWRITE_TAC[heap_slab_slot; WORD_ADD_WORD_PC]);;

let VAL_HEAP_SLAB_SLOT = prove
 (`!pc i. pc + 4608 < 2 EXP 64 /\ i < 64
          ==> val(heap_slab_slot pc i) = pc + 512 + 64 * i`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HEAP_SLAB_SLOT; VAL_WORD; DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let HEAP_SLAB_SLOT_INJ = prove
 (`!pc i j. pc + 4608 < 2 EXP 64 /\ i < 64 /\ j < 64
            ==> (heap_slab_slot pc i = heap_slab_slot pc j <=> i = j)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  ASM_SIMP_TAC[VAL_HEAP_SLAB_SLOT] THEN ARITH_TAC);;

let HEAP_SLAB_SLOT_POOL = prove
 (`!pc i n. pc + 4608 < 2 EXP 64 /\ i < 64 /\ n <= 64
            ==> memrange(heap_slab_slot pc i,n) SUBSET
                memrange(word_add (word pc) (word 512),4096)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HEAP_SLAB_SLOT; WORD_ADD_WORD_PC] THEN
  MATCH_MP_TAC SUBSET_MEMRANGE_WORD THEN ASM_ARITH_TAC);;

let HEAP_SLAB_SLOTS_DISJOINT = prove
 (`!pc i j m n.
        pc + 4608 < 2 EXP 64 /\ i < 64 /\ j < 64 /\ ~(i = j) /\
        m <= 64 /\ n <= 64
        ==> DISJOINT (memrange(heap_slab_slot pc i,m))
                     (memrange(heap_slab_slot pc j,n))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HEAP_SLAB_SLOT] THEN
  MATCH_MP_TAC DISJOINT_MEMRANGE_WORD THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(i:num = j) ==> i + 1 <= j \/ j + 1 <= i`)) THEN
  ASM_ARITH_TAC);;

let HEAP_SLAB_POOL_DISJOINT = prove
 (`!pc. pc + 4608 < 2 EXP 64
        ==> DISJOINT (memrange(word_add (word pc) (word 512):int64,4096))
                     (memrange(word pc,96) UNION
                      memrange(word_add (word pc) (word 256),8))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SET_RULE `DISJOINT s (t UNION u) <=> DISJOINT s t /\ DISJOINT s u`;
              WORD_ADD_WORD_PC] THEN
  CONJ_TAC THEN MATCH_MP_TAC DISJOINT_MEMRANGE_WORD THEN ASM_ARITH_TAC);;

let HEAP_SLAB_CTRL_SLOT_DISJOINT = prove
 (`!pc i n. pc + 4608 < 2 EXP 64 /\ i < 64 /\ n <= 64
            ==> DISJOINT (memrange(word_add (word pc) (word 256):int64,8))
                         (memrange(heap_slab_slot pc i,n))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HEAP_SLAB_SLOT; WORD_ADD_WORD_PC] THEN
  MATCH_MP_TAC DISJOINT_MEMRANGE_WORD THEN ASM_ARITH_TAC);;

let HEAP_SLAB_FP_CODE = prove
 (`!pc H. memrange(word pc,96) SUBSET heap_slab_fp pc H`,
  REWRITE_TAC[heap_slab_fp] THEN SET_TAC[]);;

let HEAP_SLAB_FP_CTRL = prove
 (`!pc H. memrange(word_add (word pc) (word 256),8) SUBSET heap_slab_fp pc H`,
  REWRITE_TAC[heap_slab_fp] THEN SET_TAC[]);;

(* The invariant in terms of the state.                                      *)

let HEAP_SLAB_OK_STATE = prove
 (`!pc H s.
     heap_slab_ok pc H (read (memory :> footprint (heap_slab_fp pc H)) s) <=>
     read (memory :> bytelist(word pc,96)) s = heap_slab_mc /\
     ALL (\(p,n). ?i. i < 64 /\ p = heap_slab_slot pc i /\ n <= 64) H /\
     PAIRWISE (\b c. ~(FST b = FST c)) H /\
     !i. i < 64
         ==> (bit i (read (memory :> bytes64 (word_add (word pc) (word 256))) s)
              <=> MEM (heap_slab_slot pc i) (MAP FST H))`,
  REWRITE_TAC[heap_slab_ok; bytelist; bytes64] THEN
  SIMP_TAC[READ_MEMORY_BYTES_SUB_FOOTPRINT; HEAP_SLAB_FP_CODE;
           HEAP_SLAB_FP_CTRL]);;

let HEAP_SLAB_LOADED = prove
 (`!pc s. 16 divides pc /\
          read (memory :> bytelist(word pc,96)) s = heap_slab_mc
          ==> aligned_bytes_loaded s (word pc) heap_slab_mc`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[aligned_bytes_loaded_word; bytes_loaded; fst HEAP_SLAB_EXEC] THEN
  MATCH_MP_TAC DIVIDES_TRANS THEN EXISTS_TAC `16` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC DIVIDES_CONV);;

(* ------------------------------------------------------------------------- *)
(* Lists of blocks.                                                          *)
(* ------------------------------------------------------------------------- *)

let PAIRWISE_HEAP_REMOVE = prove
 (`!R p (H:(int64#num)list). PAIRWISE R H ==> PAIRWISE R (heap_remove p H)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[heap_remove; PAIRWISE] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[PAIRWISE] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM ALL_MEM]) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[MEM_HEAP_REMOVE]);;

let MEM_MAP_FST_HEAP_REMOVE = prove
 (`!x p (H:(int64#num)list).
        PAIRWISE (\b c. ~(FST b = FST c)) H
        ==> (MEM x (MAP FST (heap_remove p H)) <=>
             MEM x (MAP FST H) /\ ~(x = p))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MEM_MAP] THEN
  ASM_SIMP_TAC[MEM_HEAP_REMOVE_DISTINCT] THEN MESON_TAC[]);;

let MEM_DISTINCT_FST = prove
 (`!(H:(int64#num)list) b c.
        PAIRWISE (\b c. ~(FST b = FST c)) H /\ MEM b H /\ MEM c H /\
        FST b = FST c
        ==> b = c`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; PAIRWISE; GSYM ALL_MEM] THEN
  ASM_MESON_TAC[]);;

let HEAP_REMOVE_CASES = prove
 (`!(H:(int64#num)list) p n b.
        PAIRWISE (\b c. ~(FST b = FST c)) H /\ MEM (p,n) H /\ MEM b H
        ==> MEM b (heap_remove p H) \/ b = (p,n)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MEM_HEAP_REMOVE_DISTINCT] THEN
  ASM_CASES_TAC `FST(b:int64#num) = p` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEM_DISTINCT_FST THEN EXISTS_TAC `H:(int64#num)list` THEN
  ASM_REWRITE_TAC[FST]);;

(* Fewer than 64 blocks leave a slot free.                                   *)

let HEAP_SLAB_FREE_SLOT = prove
 (`!pc (H:(int64#num)list).
        pc + 4608 < 2 EXP 64 /\ LENGTH H < 64
        ==> ?i. i < 64 /\ ~MEM (heap_slab_slot pc i) (MAP FST H)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[TAUT `p /\ ~q <=> ~(p ==> q)`; GSYM NOT_FORALL_THM] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (heap_slab_slot pc) {i:num | i < 64}`;
                 `set_of_list(MAP FST (H:(int64#num)list))`] CARD_SUBSET) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_SET_OF_LIST; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM;
                IN_SET_OF_LIST] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`heap_slab_slot pc`; `{i:num | i < 64}`] CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; FINITE_NUMSEG_LT] THEN
    ASM_MESON_TAC[HEAP_SLAB_SLOT_INJ];
    ALL_TAC] THEN
  REWRITE_TAC[CARD_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPEC `MAP FST (H:(int64#num)list)` CARD_SET_OF_LIST_LE) THEN
  REWRITE_TAC[LENGTH_MAP] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The properties of the invariant and the footprint.                        *)
(* ------------------------------------------------------------------------- *)

let HEAP_SLAB_BLOCK = prove
 (`!pc H m p n.
        heap_slab_ok pc H m /\ MEM (p,n) H
        ==> ?i. i < 64 /\ p = heap_slab_slot pc i /\ n <= 64`,
  REWRITE_TAC[heap_slab_ok; GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(p:int64,n:num)`) THEN ASM_REWRITE_TAC[]);;

let ALL_HEAP_SLAB_BLOCK = prove
 (`!pc H q n.
        ALL (\(p,n). ?i. i < 64 /\ p = heap_slab_slot pc i /\ n <= 64) H /\
        MEM (q,n) H
        ==> ?i. i < 64 /\ q = heap_slab_slot pc i /\ n <= 64`,
  REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(q:int64,n:num)`) THEN ASM_REWRITE_TAC[]);;

let HEAP_SLAB_PROPS = prove
 (`!pc. pc + 4608 < 2 EXP 64
        ==> heap_props (heap_slab_ok pc) (heap_slab_fp pc)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[heap_props] THEN
  MAP_EVERY X_GEN_TAC [`H:(int64#num)list`; `m:int64->byte`] THEN
  DISCH_TAC THEN REWRITE_TAC[heap_blocks; GSYM ALL_MEM; FORALL_PAIR_THM] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`p:int64`; `n:num`] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`pc:num`; `H:(int64#num)list`; `m:int64->byte`;
                  `p:int64`; `n:num`] HEAP_SLAB_BLOCK) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[VAL_HEAP_SLAB_SLOT; GSYM VAL_EQ_0] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC PAIRWISE_IMPLIES THEN
    EXISTS_TAC `\b:int64#num c:int64#num. ~(FST b = FST c)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[heap_slab_ok]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:int64`; `m':num`; `q:int64`; `n:num`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`pc:num`; `H:(int64#num)list`; `m:int64->byte`;
                  `p:int64`; `m':num`] HEAP_SLAB_BLOCK) THEN
    MP_TAC(SPECL [`pc:num`; `H:(int64#num)list`; `m:int64->byte`;
                  `q:int64`; `n:num`] HEAP_SLAB_BLOCK) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC HEAP_SLAB_SLOTS_DISJOINT THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`p:int64`; `n:num`] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`pc:num`; `H:(int64#num)list`; `m:int64->byte`;
                  `p:int64`; `n:num`] HEAP_SLAB_BLOCK) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`pc:num`; `i:num`; `n:num`] HEAP_SLAB_SLOT_POOL) THEN
    MP_TAC(SPEC `pc:num` HEAP_SLAB_POOL_DISJOINT) THEN
    ASM_REWRITE_TAC[heap_slab_fp] THEN
    UNDISCH_TAC `MEM (p:int64,n:num) H` THEN
    REWRITE_TAC[DISJOINT; SUBSET; EXTENSION; IN_INTER; IN_UNION; IN_DIFF;
                NOT_IN_EMPTY; IN_ELIM_THM] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* new.                                                                      *)
(* ------------------------------------------------------------------------- *)

let WORD_JSHL_1_POW2 = prove
 (`!i. i < 64 ==> word_jshl (word 1) (word i):int64 = word(2 EXP i)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[word_jshl; word_shl; VAL_WORD; DIMINDEX_64] THEN
  AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 64 ==> i < 2 EXP 64`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_CLAUSES]);;

(* The slot that new takes, 63 - clz of the complement of the bitmap.        *)

let HEAP_SLAB_NEW_SLOT = prove
 (`!pc bm.
     pc + 4608 < 2 EXP 64 /\ ~(word_not bm = word 0:int64)
     ==> word_clz(word_not bm) < 64 /\
         ~bit (63 - word_clz(word_not bm)) bm /\
         word_add (word_add (word pc) (word 512))
                  (word_shl (word_sub (word 63) (word(word_clz(word_not bm))))
                            6) =
         heap_slab_slot pc (63 - word_clz(word_not bm)) /\
         word_jshl (word 1)
                   (word_sub (word 63) (word(word_clz(word_not bm)))):int64 =
         word(2 EXP (63 - word_clz(word_not bm)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c = word_clz(word_not(bm:int64))` THEN
  SUBGOAL_THEN `c < 64` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    MP_TAC(ISPEC `word_not bm:int64` WORD_CLZ_LT_DIMINDEX) THEN
    ASM_REWRITE_TAC[DIMINDEX_64];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `word_sub (word 63) (word c):int64 = word(63 - c)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `c < 64 ==> c <= 63`]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`word_not bm:int64`; `c:num`] WORD_CLZ_UNIQUE_GEN) THEN
    ASM_REWRITE_TAC[DIMINDEX_64; BIT_WORD_NOT] THEN
    REWRITE_TAC[ARITH_RULE `64 - c - 1 = 63 - c`] THEN MESON_TAC[];
    REWRITE_TAC[heap_slab_slot; word_shl; VAL_WORD; DIMINDEX_64] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `c < 64 ==> 63 - c < 2 EXP 64`] THEN
    ARITH_TAC;
    REWRITE_TAC[word_jshl; word_shl; VAL_WORD; DIMINDEX_64] THEN
    AP_TERM_TAC THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `c < 64 ==> 63 - c < 2 EXP 64`;
                 ARITH_RULE `c < 64 ==> 63 - c < 64`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_CLAUSES]]);;

let HEAP_SLAB_NEW_CORRECT = prove
 (`!pc stk. 16 divides pc /\ pc + 4608 < 2 EXP 64
            ==> heap_new_contract (heap_slab_ok pc) (heap_slab_fp pc)
                                  heap_slab_room stk (word pc)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[heap_new_contract; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  MAP_EVERY X_GEN_TAC [`H:(int64#num)list`; `sz:int64`; `sp:int64`;
                       `returnaddress:int64`; `e:uarch_event list`] THEN
  REWRITE_TAC[heap_slab_room] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HEAP_SLAB_OK_STATE]) THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`pc:num`; `s0:armstate`] HEAP_SLAB_LOADED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASSUME_TAC(SPECL [`pc:num`; `H:(int64#num)list`] HEAP_SLAB_FP_CTRL) THEN
  ABBREV_TAC `bm = read (memory :> bytes64 (word_add (word pc) (word 256))) s0` THEN
  ARM_BSTEP_TAC HEAP_SLAB_EXEC (1--13) THEN
  BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
  (* The slot                                                              *)
  MP_TAC(SPECL [`pc:num`; `H:(int64#num)list`] HEAP_SLAB_FREE_SLOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(word_not bm = word 0:int64)` ASSUME_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_NOT; BIT_WORD_0; DIMINDEX_64] THEN
    REWRITE_TAC[NOT_FORALL_THM] THEN EXISTS_TAC `j:num` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`pc:num`; `bm:int64`] HEAP_SLAB_NEW_SLOT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `i = 63 - word_clz(word_not(bm:int64))` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~MEM (heap_slab_slot pc i) (MAP FST (H:(int64#num)list))`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `heap_slab_slot pc i` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* nonzero *)
    ASM_SIMP_TAC[GSYM VAL_EQ_0; VAL_HEAP_SLAB_SLOT] THEN ARITH_TAC;
    (* aligned *)
    REWRITE_TAC[aligned; DIMINDEX_64] THEN
    ASM_SIMP_TAC[VAL_HEAP_SLAB_SLOT] THEN CONJ_TAC THENL
     [CONV_TAC(NUM_REDUCE_CONV THENC DIVIDES_CONV);
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      MATCH_MP_TAC DIVIDES_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC DIVIDES_ADD THEN CONJ_TAC THENL
       [CONV_TAC DIVIDES_CONV;
        MATCH_MP_TAC DIVIDES_RMUL THEN CONV_TAC DIVIDES_CONV]];
    (* no wrap *)
    ASM_SIMP_TAC[VAL_HEAP_SLAB_SLOT] THEN ASM_ARITH_TAC;
    (* inside the footprint *)
    REWRITE_TAC[heap_slab_fp; SUBSET; IN_UNION; IN_DIFF; IN_ELIM_THM] THEN
    X_GEN_TAC `x:int64` THEN DISCH_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    CONJ_TAC THENL
     [MP_TAC(SPECL [`pc:num`; `i:num`; `val(sz:int64)`] HEAP_SLAB_SLOT_POOL) THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[NOT_EXISTS_THM; FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`q:int64`; `n:num`] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`pc:num`; `H:(int64#num)list`; `q:int64`; `n:num`]
                   ALL_HEAP_SLAB_BLOCK) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPECL [`pc:num`; `i:num`; `k:num`; `val(sz:int64)`; `n:num`]
                   HEAP_SLAB_SLOTS_DISJOINT) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `p /\ (q ==> F) ==> ~(p ==> q)`) THEN CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC
         `~MEM (heap_slab_slot pc k) (MAP FST (H:(int64#num)list))` THEN
        REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[FST];
        UNDISCH_TAC `x IN memrange(q:int64,n)` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `x IN memrange(heap_slab_slot pc i,val(sz:int64))` THEN
        SET_TAC[]]];
    (* the new footprint *)
    REWRITE_TAC[heap_slab_fp; MEM] THEN SET_TAC[];
    (* the new invariant *)
    REWRITE_TAC[HEAP_SLAB_OK_STATE; ALL; PAIRWISE; MAP; MEM] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM ALL_MEM] THEN
      UNDISCH_TAC `~MEM (heap_slab_slot pc i) (MAP FST (H:(int64#num)list))` THEN
      REWRITE_TAC[MEM_MAP] THEN MESON_TAC[];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      REWRITE_TAC[BIT_WORD_OR; BIT_WORD_POW2; DIMINDEX_64] THEN
      ASM_SIMP_TAC[HEAP_SLAB_SLOT_INJ] THEN ASM_MESON_TAC[]];
    (* the events *)
    MEMACCESS_INSET_TAC]);;

(* ------------------------------------------------------------------------- *)
(* delete.                                                                   *)
(* ------------------------------------------------------------------------- *)

let HEAP_SLAB_DELETE_INDEX = prove
 (`!pc i. pc + 4608 < 2 EXP 64 /\ i < 64
          ==> word_ushr (word_sub (word_sub (heap_slab_slot pc i) (word pc))
                                  (word 512)) 6 = word i:int64`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[heap_slab_slot; WORD_RULE
   `word_sub (word_sub (word_add x y) x) z:int64 = word_sub y z`] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word (a + b)) (word a):int64 = word b`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 64 ==> 64 * i < 2 EXP 64`;
               ARITH_RULE `i < 64 ==> i < 2 EXP 64`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let HEAP_SLAB_DELETE_CORRECT = prove
 (`!pc stk. 16 divides pc /\ pc + 4608 < 2 EXP 64
            ==> heap_delete_contract (heap_slab_ok pc) (heap_slab_fp pc)
                                     stk (word(pc + 52))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[heap_delete_contract; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`H:(int64#num)list`; `p:int64`; `n:num`; `sp:int64`;
                         `returnaddress:int64`; `e:uarch_event list`] THEN
    STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HEAP_SLAB_OK_STATE]) THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`pc:num`; `s0:armstate`] HEAP_SLAB_LOADED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASSUME_TAC(SPECL [`pc:num`; `H:(int64#num)list`] HEAP_SLAB_FP_CTRL) THEN
    (* The block is a slot i, and the facts that the run needs about it    *)
    MP_TAC(SPECL [`pc:num`; `H:(int64#num)list`; `p:int64`; `n:num`]
                 ALL_HEAP_SLAB_BLOCK) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `~(val(heap_slab_slot pc i) = 0)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[VAL_HEAP_SLAB_SLOT] THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`pc:num`; `i:num`] HEAP_SLAB_DELETE_INDEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun ith ->
    MP_TAC(SPECL [`pc:num`; `i:num`; `n:num`] HEAP_SLAB_CTRL_SLOT_DISJOINT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ABBREV_TAC
     `bm = read (memory :> bytes64 (word_add (word pc) (word 256))) s0` THEN
    ARM_BSTEP_TAC ~rewrites:[ith] HEAP_SLAB_EXEC (1--11)) THEN
    BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [(* the new footprint *)
      REWRITE_TAC[heap_slab_fp; SUBSET; IN_UNION; IN_DIFF; IN_ELIM_THM] THEN
      X_GEN_TAC `x:int64` THEN
      MP_TAC(SPECL [`H:(int64#num)list`; `heap_slab_slot pc i`; `n:num`]
                   HEAP_REMOVE_CASES) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      (* the new invariant *)
      REWRITE_TAC[HEAP_SLAB_OK_STATE] THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[PAIRWISE_HEAP_REMOVE; WORD_JSHL_1_POW2] THEN CONJ_TAC THENL
       [UNDISCH_TAC `ALL (\(p,n). ?i. i < 64 /\ p = heap_slab_slot pc i /\
                                      n <= 64) (H:(int64#num)list)` THEN
        REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[MEM_HEAP_REMOVE];
        X_GEN_TAC `k:num` THEN DISCH_TAC THEN
        ASM_SIMP_TAC[MEM_MAP_FST_HEAP_REMOVE; BIT_WORD_AND; BIT_WORD_NOT;
                     BIT_WORD_POW2; DIMINDEX_64; HEAP_SLAB_SLOT_INJ] THEN
        ASM_MESON_TAC[]];
      (* the events *)
      MEMACCESS_INSET_TAC];
    (* The null pointer                                                    *)
    MAP_EVERY X_GEN_TAC [`H:(int64#num)list`; `sp:int64`;
                         `returnaddress:int64`; `e:uarch_event list`] THEN
    STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HEAP_SLAB_OK_STATE]) THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`pc:num`; `s0:armstate`] HEAP_SLAB_LOADED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_BSTEP_TAC HEAP_SLAB_EXEC (1--2) THEN
    BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    MEMACCESS_INSET_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The model and its non-vacuity.                                            *)
(* ------------------------------------------------------------------------- *)

let HEAP_SLAB_MODEL = prove
 (`!pc stk. 16 divides pc /\ pc + 4608 < 2 EXP 64
            ==> heap_model (heap_slab_ok pc) (heap_slab_fp pc) heap_slab_room
                           stk (word pc) (word(pc + 52))`,
  SIMP_TAC[heap_model; HEAP_SLAB_PROPS; HEAP_SLAB_NEW_CORRECT;
           HEAP_SLAB_DELETE_CORRECT]);;

(* The invariant holds of the empty heap when the code is loaded and the     *)
(* bitmap is zero, as after loading a binary with the bitmap in .bss.        *)

let HEAP_SLAB_INIT = prove
 (`!pc s. pc + 4608 < 2 EXP 64 /\
          read (memory :> bytelist(word pc,96)) s = heap_slab_mc /\
          read (memory :> bytes64 (word_add (word pc) (word 256))) s = word 0
          ==> heap_slab_ok pc [] (read (memory :> footprint (heap_slab_fp pc [])) s)`,
  SIMP_TAC[HEAP_SLAB_OK_STATE; ALL; PAIRWISE; MAP; MEM; BIT_WORD_0]);;

(* The room: any allocation of at most 64 bytes while fewer than 64 blocks   *)
(* are live, so the hypothesis heap_room of a client is not vacuous.         *)

let HEAP_SLAB_ROOM = prove
 (`!H n. n <= 64 /\ LENGTH H < 64 ==> heap_slab_room H n`,
  REWRITE_TAC[heap_slab_room]);;

(* The non-vacuity of heap_model: for the code at a suitable pc, there are   *)
(* an invariant, a footprint and a room that meet the model, the invariant  *)
(* holds initially, and the room allows allocations.                         *)

let HEAP_MODEL_NONVACUOUS = prove
 (`!pc stk. 16 divides pc /\ pc + 4608 < 2 EXP 64
            ==> ?heap_ok heap_fp heap_room.
                  heap_model heap_ok heap_fp heap_room stk
                             (word pc) (word(pc + 52)) /\
                  (!s. read (memory :> bytelist(word pc,96)) s = heap_slab_mc /\
                       read (memory :> bytes64 (word_add (word pc) (word 256))) s =
                       word 0
                       ==> heap_ok [] (read (memory :> footprint (heap_fp [])) s)) /\
                  (!H n. n <= 64 /\ LENGTH H < 64 ==> heap_room H n)`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`heap_slab_ok pc`; `heap_slab_fp pc`; `heap_slab_room`] THEN
  ASM_SIMP_TAC[HEAP_SLAB_MODEL; HEAP_SLAB_INIT; HEAP_SLAB_ROOM]);;
