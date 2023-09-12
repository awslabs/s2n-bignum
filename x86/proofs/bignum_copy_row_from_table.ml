(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC
 *)

(* ========================================================================= *)
(* Constant-time table lookup.                                               *)
(* ========================================================================= *)

let bignum_copy_row_from_table_mc =
  define_assert_from_elf "bignum_copy_row_from_table_mc"
                         "x86/generic/bignum_copy_row_from_table.o"
[
  0x48; 0x85; 0xd2;        (* TEST (% rdx) (% rdx) *)
  0x74; 0x51;              (* JE (Imm8 (word 81)) *)
  0x48; 0x85; 0xc9;        (* TEST (% rcx) (% rcx) *)
  0x74; 0x4c;              (* JE (Imm8 (word 76)) *)
  0x48; 0x89; 0xf8;        (* MOV (% rax) (% rdi) *)
  0x49; 0x89; 0xc9;        (* MOV (% r9) (% rcx) *)
  0x48; 0xc7; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rax,0))) (Imm32 (word 0)) *)
  0x48; 0x83; 0xc0; 0x08;  (* ADD (% rax) (Imm8 (word 8)) *)
  0x49; 0xff; 0xc9;        (* DEC (% r9) *)
  0x75; 0xf0;              (* JNE (Imm8 (word 240)) *)
  0x49; 0xc7; 0xc1; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Imm32 (word 0)) *)
  0x48; 0x89; 0xf0;        (* MOV (% rax) (% rsi) *)
  0x49; 0x89; 0xca;        (* MOV (% r10) (% rcx) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x4d; 0x39; 0xc1;        (* CMP (% r9) (% r8) *)
  0x4e; 0x0f; 0x44; 0x5c; 0xd0; 0xf8;
                           (* CMOVE (% r11) (Memop Quadword (%%%% (rax,3,r10,-- &8))) *)
  0x4e; 0x09; 0x5c; 0xd7; 0xf8;
                           (* OR (Memop Quadword (%%%% (rdi,3,r10,-- &8))) (% r11) *)
  0x49; 0xff; 0xca;        (* DEC (% r10) *)
  0x75; 0xea;              (* JNE (Imm8 (word 234)) *)
  0x4c; 0x8d; 0x14; 0xcd; 0x00; 0x00; 0x00; 0x00;
                           (* LEA (% r10) (Bsid NONE (SOME rcx) (word 3) (word 0)) *)
  0x4c; 0x01; 0xd0;        (* ADD (% rax) (% r10) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x49; 0x39; 0xd1;        (* CMP (% r9) (% rdx) *)
  0x75; 0xd4;              (* JNE (Imm8 (word 212)) *)
  0xc3                     (* RET *)
];;

let BIGNUM_COPY_ROW_FROM_TABLE_EXEC = X86_MK_CORE_EXEC_RULE bignum_copy_row_from_table_mc;;

(* ARITH_RULE for proving `lp=rp` where lp and rp are pairs *)
let PAIR_EQ_ARITH_RULE (lp:term) (rp:term) =
  let lpl,lpr = dest_pair lp in
  let rpl,rpr = dest_pair rp in
  let lth = ARITH_RULE (mk_eq (lpl,rpl)) in
  let rth = ARITH_RULE (mk_eq (lpr,rpr)) in
  let th = REFL lp in
  let th = GEN_REWRITE_RULE (RAND_CONV o LAND_CONV) [lth] th in
  GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [rth] th;;

let REWRITE_ASSUMES_TAC (t:term) =
    UNDISCH_THEN t (fun thm -> RULE_ASSUM_TAC (REWRITE_RULE [thm]) THEN ASSUME_TAC thm);;

let READ_MEMORY_BYTES_0 = prove(`read (memory :> bytes (z,0)) s = 0`,
    REWRITE_TAC[PAIR_EQ_ARITH_RULE `(x:int64,0)` `(x:int64, 8*0)`] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL]);;

let SPLIT_FIRST_CONJ_ASSUM_TAC = FIRST_X_ASSUM (fun thm -> let t1,t2 = CONJ_PAIR thm in
                              MAP_EVERY ASSUME_TAC [t1;t2]);;

let CASES_FIRST_DISJ_ASSUM_TAC = FIRST_X_ASSUM (fun thm ->
    if is_disj (concl thm) then DISJ_CASES_TAC thm else failwith "");;

let LT_WORD_64 = prove(`!x (y:int64). x < val y ==> x < 2 EXP 64`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LT_TRANS `val (y:int64)` THEN
  ONCE_REWRITE_TAC [GSYM DIMINDEX_64] THEN ASM_REWRITE_TAC[VAL_BOUND]);;

let READ_MEMORY_BYTES_ELEM = prove(`!z w s m k.
  w > k /\ read (memory :> bytes (z,8 * w)) s = m ==>
  val (read (memory :> bytes64 (word_add z (word (8 * k)))) s) = lowdigits (highdigits m k) 1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT STRIP_TAC THEN EXPAND_TAC "m" THEN
  REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY; LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_SING] THEN
  AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES_FIRSTELEM = prove(`!z w s m.
  w > 0 /\ read (memory :> bytes (z,8 * w)) s = m ==>
  val (read (memory :> bytes64 z) s) = lowdigits m 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `z:int64 = word_add z (word (8 * 0))` (fun thm -> ONCE_REWRITE_TAC[thm]) THENL
  [CONV_TAC WORD_RULE; ALL_TAC] THEN
  IMP_REWRITE_TAC[READ_MEMORY_BYTES_ELEM] THEN REWRITE_TAC[HIGHDIGITS_0]);;

let READ_MEMORY_BYTES_SLICE = prove(`!z w s m k w'.
  w >= k + w' /\ read (memory :> bytes (z,8 * w)) s = m ==>
  read (memory :> bytes (word_add z (word (8 * k)), 8 * w')) s = lowdigits (highdigits m k) w'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT STRIP_TAC THEN EXPAND_TAC "m" THEN
  REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY; LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
  AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES_SLICE_HIGH = prove(`!z w s m k w'.
  w = k + w' /\ read (memory :> bytes (z,8 * w)) s = m ==>
  read (memory :> bytes (word_add z (word (8 * k)), 8 * w')) s = highdigits m k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT STRIP_TAC THEN EXPAND_TAC "m" THEN
  REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY] THEN
  AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES_MERGE = prove(`!z w w' w'' s m.
    read (memory :> bytes (z,8 * w)) s = lowdigits m w /\
    read (memory :> bytes (word_add z (word (8 * w)),8 * w')) s = highdigits m w /\
    w + w' = w'' ==>
    read (memory :> bytes (z, 8 * w'')) s = m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT STRIP_TAC THEN EXPAND_TAC "w''" THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
  REWRITE_TAC[HIGH_LOW_DIGITS]);;

let READ_MEMORY_BYTES_BYTES64 = prove(`!z s.
  read (memory :> bytes (z,8)) s = val (read (memory :> bytes64 z) s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PAIR_EQ_ARITH_RULE `(z:int64,8)` `(z:int64,8*1)`;
              GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_SING]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

g `!z table height width idx pc n m returnaddress.
    nonoverlapping (word pc, 0x57) (z, 8 * val width) /\
    nonoverlapping (word pc, 0x57) (table, 8 * val height * val width) /\
    nonoverlapping (z, 8 * val width) (table, 8 * val height * val width) /\
    8 * val width < 2 EXP 64 /\
    val idx < val height
    ==> ensures x86
      (\s. bytes_loaded s (word pc) (BUTLAST bignum_copy_row_from_table_mc) /\
           read RIP s = word pc /\
           C_ARGUMENTS [z; table; height; width; idx] s /\
           bignum_from_memory (table, val height * val width) s = n /\
           bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s = m)
      (\s. read RIP s = word (pc + 0x56) /\
           bignum_from_memory (z, val width) s = m)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(z,8 * val width)])`;;

e(REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; BIGNUM_COPY_ROW_FROM_TABLE_EXEC;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN

  ASM_CASES_TAC `val (height:(64)word) = 0` THENL [
    UNDISCH_TAC `val (idx:int64) < val (height:int64)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[LT] THEN ENSURES_INIT_TAC "s0" THEN ITAUT_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `width = (word 0):(64)word` THENL [
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_0; MULT_0; WORD_ADD_0] THEN
    X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC (1--4) THEN
    ASM_MESON_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(val (width:64 word) = 0)` ASSUME_TAC THENL [
    UNDISCH_TAC `~(width = word 0:64 word)` THEN
    REWRITE_TAC[VAL_EQ_0];
    ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0x10`
    `\s. // C arguments
         read RDI s = z /\ read RSI s = table /\
         read RDX s = height /\ read RCX s = width /\ read R8 s = idx /\
         // Temp vars
         read R9 s = width /\ read RAX s = z /\
         bignum_from_memory (table, val height * val width) s = n /\
         bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s
            = m` THEN CONJ_TAC THENL [
  X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC (1--6);

  ALL_TAC] THEN

  (* This is necessary to avoid stores from overwriting the table *)
  SUBGOAL_THEN `val (idx:int64) * val (width:int64) + val width <= val (height:int64) * val width` ASSUME_TAC
    THENL [IMP_REWRITE_TAC[LE_MULT_ADD]; ALL_TAC]);;

(* bignum_copy_row_from_table_initzero *)
e(ENSURES_WHILE_PDOWN_TAC `val (width:64 word):num` `pc + 0x10` `pc + 0x1e`
  `\i s. (read RDI s = z /\ read RSI s = table /\
          read RDX s = height /\ read RCX s = width /\ read R8 s = idx /\
          read R9 s = word i /\ read RAX s = word (val z + 8 * (val width - i)) /\
          bignum_from_memory (table, val height * val width) s = n /\
          bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s
              = m /\
          bignum_from_memory (z, val width - i) s = 0) /\
          (read ZF s <=> i = 0)` THEN REPEAT CONJ_TAC THENL [
  (* 1. width > 0 *)
  ASM_MESON_TAC[];

  (* 2. loop starts *)
  X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC [] THEN
    REWRITE_TAC[SUB_REFL; WORD_VAL; MULT_0; ADD_0; GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL];

  (* 3. loop body *)
  REPEAT STRIP_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes64 (word (val (z:int64) + 8 * (val (width:int64) - (i + 1))))]` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  CONJ_TAC THENL [
    REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    (* SIMPLE_ARITH_TAC isn't good at dealing with assumptions containing 'val'. Let's abbreviate
       val width. *)
    REWRITE_TAC[WORD_ADD; WORD_VAL] THEN
    ABBREV_TAC `w' = val (width:int64)` THEN
    SUBSUMED_MAYCHANGE_TAC;

    ALL_TAC] THEN

  ENSURES_INIT_TAC "s0" THEN

  SUBGOAL_THEN `val (width:64 word) - (i + 1) < val (width:64 word)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `8 * (val (width:int64) - (i + 1)) + 8 <= 18446744073709551616` ASSUME_TAC
    THENL [ASM_ARITH_TAC; ALL_TAC] THEN

  X86_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    CONV_TAC WORD_RULE;

    REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN UNDISCH_TAC `i < val (width:64 word)`
    THEN ARITH_TAC;

    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_SIMP_TAC [ARITH_RULE `i < val (width:64 word) ==> val width - i = (val width - (i + 1)) + 1`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; WORD_RULE `word_add z (word c) = word (val z + c)`] THEN
    CONV_TAC WORD_RULE;

    REWRITE_TAC[WORD_SUB_ADD; VAL_WORD] THEN
    SUBGOAL_THEN `i < 2 EXP 64` ASSUME_TAC THENL [
      TRANS_TAC LT_TRANS `val (width:64 word)` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `8 * val (width:64 word) < 2 EXP 64` THEN
      ARITH_TAC;

      ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT; DIMINDEX_64]];

  (* 4. loop backedge *)
  REPEAT STRIP_TAC THEN X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC (1--1);

  (* next *)
  ALL_TAC]);;

(* bignum_copy_row_from_table_outerloop *)
e(ENSURES_WHILE_PUP_TAC `val (height:64 word):num` `pc + 0x2a` `pc + 0x54`
  `\i s.  (read RDI s = z /\ read RSI s = table /\
          read RDX s = height /\ read RCX s = width /\ read R8 s = idx /\
          read R9 s = word i /\ read RAX s = word_add table (word (8 * i * val width)) /\
          bignum_from_memory (table, val height * val width) s = n /\
          bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s
              = m /\
           ((i <= val idx  /\ bignum_from_memory (z, val width) s = 0) \/
            (i > val idx /\ bignum_from_memory (z, val width) s = m))) /\
          (read ZF s <=> i = val height)` THEN REPEAT CONJ_TAC THENL [
  (* 1. height > 0 *)
  ASM_MESON_TAC[];

  (* 2. to loop start *)
  X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC (1--3) THEN
  REWRITE_TAC[ARITH_RULE `x * 0 = 0`; ARITH_RULE `0 * x = 0`; WORD_ADD_0] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [ARITH_RULE `x - 0 = x`]) THEN
  ASM_REWRITE_TAC[LE_0];

  (* 3. loop body - pass *)
  ALL_TAC;

  (* 4. loop backedge *)
  REPEAT STRIP_TAC THEN
  X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC (1--1);

  (* next *)
  X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC [1] THEN
  CASES_FIRST_DISJ_ASSUM_TAC THEN SPLIT_FIRST_CONJ_ASSUM_TAC THENL [
    UNDISCH_TAC `val (idx:int64) < val (height:int64)` THEN
    UNDISCH_TAC `val (height:int64) <= val (idx:int64)` THEN
    ARITH_TAC;

    ASM_MESON_TAC[]]] THEN

  REPEAT STRIP_TAC);;



e(ENSURES_WHILE_PDOWN_TAC `val (width:64 word):num` `pc + 0x2d` `pc + 0x41`
  `\j s.  (read RDI s = z /\ read RSI s = table /\
          read RDX s = height /\ read RCX s = width /\ read R8 s = idx /\
          read R9 s = word i /\
          read R10 s = word j /\
          read RAX s = word_add table (word (8 * i * val width)) /\
          bignum_from_memory (table, val height * val width) s = n /\
          bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s
              = m /\
           ((i < val idx /\
             bignum_from_memory (z, val width - j) s = 0 /\
             bignum_from_memory (word_add z (word (8 * (val width - j))), j) s = 0)
            \/
            (i = val idx /\
             bignum_from_memory (z, val width - j) s = lowdigits m (val width - j) /\
             bignum_from_memory (word_add z (word (8 * (val width - j))), j) s = 0)
            \/
            (i > val idx /\
             bignum_from_memory (z, val width - j) s = lowdigits m (val width - j) /\
             bignum_from_memory (word_add z (word (8 * (val width - j))), j) s = highdigits m (val width - j)))) /\
          (read ZF s <=> j = 0)` THEN REPEAT CONJ_TAC THENL [
  ASM_MESON_TAC[];

  X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC (1--1) THEN
  ASM_REWRITE_TAC[WORD_VAL; ADD_0; MULT_0; WORD_ADD_0;
      LOWDIGITS_0; HIGHDIGITS_0; READ_MEMORY_BYTES_0] THEN
  ASM_ARITH_TAC;

  (* loop body *)
  ALL_TAC;

  (* backedge *)
  REPEAT STRIP_TAC THEN
  X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC [1];

  (* finishes outer loop; pc 0x43 -> 0x54 *)
  X86_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC (1--5) THEN
  REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THENL [
    SUBGOAL_THEN `m < 2 EXP (64 * val (width:int64))` ASSUME_TAC THENL
    [EXPAND_TAC "m" THEN SIMP_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND]; ALL_TAC] THEN
    RULE_ASSUM_TAC (REWRITE_RULE[SUB_0;
      MATCH_MP LOWDIGITS_SELF (ASSUME `m < 2 EXP (64 * val (width:int64))`);
      MATCH_MP HIGHDIGITS_ZERO (ASSUME `m < 2 EXP (64 * val (width:int64))`);
      MULT_0; READ_MEMORY_BYTES_0]) THEN
    REPEAT CASES_FIRST_DISJ_ASSUM_TAC THEN REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN ASM_REWRITE_TAC[] THENL [
      UNDISCH_TAC `i < val (idx:int64)` THEN ARITH_TAC;
      UNDISCH_TAC `i = val (idx:int64)` THEN ARITH_TAC;
      UNDISCH_TAC `i > val (idx:int64)` THEN ARITH_TAC;
    ];

    (* fill in here *)
    SUBGOAL_THEN `i + 1 < 2 EXP 64` ASSUME_TAC THENL [
      TRANS_TAC LET_TRANS `val (height:int64)` THEN
      CONJ_TAC THENL [
        UNDISCH_TAC `i < val (height:int64)` THEN ARITH_TAC;
        REWRITE_TAC[VAL_BOUND_64]];

      ALL_TAC
    ] THEN
    REWRITE_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64;ARITH_RULE`1 MOD 2 EXP 64 = 1`; ADD_0] THEN
    ASM_SIMP_TAC[MOD_LT; MATCH_MP LT_WORD_64
      (ASSUME `i < val (height:int64)`)]
  ]
]);;

e(REPEAT STRIP_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN

MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes64 (word (val (z:int64) + 8 * (val (width:int64) - (i' + 1))))]` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  CONJ_TAC THENL [
    REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    (* SIMPLE_ARITH_TAC isn't good at dealing with assumptions containing 'val'. Let's abbreviate
       val width. *)
    REWRITE_TAC[WORD_ADD; WORD_VAL] THEN
    ABBREV_TAC `w' = val (width:int64)` THEN
    SUBSUMED_MAYCHANGE_TAC;

    ALL_TAC]);;

e(ENSURES_INIT_TAC "s0");;
e(X86_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC (1--6));;