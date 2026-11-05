(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The loops of poly_add, poly_sub and poly_tomont inlined into a caller, as *)
(* lemmas from the head of the loop to its exit, which the proof of the      *)
(* caller uses as it uses the theorem for a subroutine. Each lemma has the   *)
(* correctness and the events in its postcondition, so that it serves both   *)
(* the correctness proof and the proof of constant time and memory safety:  *)
(*                                                                           *)
(*   exists f_events. forall e a ... pc. ... ==> ensures arm                 *)
(*     (\s. ... read PC s = word(pc + loop) /\ <registers> /\ <input> /\     *)
(*          read events s = e)                                               *)
(*     (\s. read PC s = word(pc + exit) /\ <registers> /\ <result> /\        *)
(*          exists e2. read events s = APPEND e2 e /\ e2 = f_events ... /\   *)
(*                     memaccess_inbounds e2 ...)                            *)
(*     (MAYCHANGE <registers of the loop> ,, ...)                            *)
(*                                                                           *)
(* The lemmas are generated for the image (the name of its constant), the    *)
(* EXEC theorem of the caller, the labels of the loop and the registers, for *)
(* the shapes of loop that gcc 12 -O2 generates for one polynomial of 256    *)
(* coefficients, 16 bytes at a time:                                         *)
(*                                                                           *)
(*  - INLINE_PTR_LOOP op: D += S with pointers into both, op = "add" or      *)
(*    "sub" (word_add or word_sub of the coefficients of D and S):           *)
(*        ldr q1, [S], #16; ldr q0, [D]; op v0.8h, v0.8h, v1.8h;             *)
(*        str q0, [D], #16; cmp D, E (or cmp E, D); b.ne                     *)
(*  - INLINE_IDX_ADD_LOOP: T + 512 += U + 512, with an offset I from 0:      *)
(*        add P, T, I; add Q, U, I; add I, I, #16; ldr q1, [P, #512];        *)
(*        ldr q0, [Q, #512]; add v0.8h, v0.8h, v1.8h; str q0, [P, #512];     *)
(*        cmp I, #0x200; b.ne                                                *)
(*  - INLINE_REG_IDX_LOOP op: D op= S with an index I from 0:                *)
(*        ldr q0, [D, I]; ldr q1, [S, I]; op v0.8h, v0.8h, v1.8h;            *)
(*        str q0, [D, I]; add I, I, #16; cmp I, #0x200; b.ne                 *)
(*  - INLINE_TOMONT_LOOP_REG: the Montgomery form in place, with the pointer *)
(*    in a register D, the end in E and the vectors of constants in Q3, Q4   *)
(*    and Q5 (INLINE_TOMONT_LOOP: D = X2).                                   *)
(* ========================================================================= *)

(*** The loop tests ***)

let INLINE_LOOP_TEST = prove
 (`!a:int64 i.
        i < 32
        ==> (val(word_sub (word_add (word_add a (word(16 * i))) (word 16))
                          (word_add a (word 512))) = 0 <=>
             ~(i + 1 < 32))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
              WORD_RULE `word_sub (word_add a x) (word_add a y):int64 =
                         word_sub x y`] THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `16 * i + 16 < 2 EXP 64` (fun th -> SIMP_TAC[th; MOD_LT]) THENL
   [UNDISCH_TAC `i < 32` THEN ARITH_TAC;
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]);;

(*** The same with the operands of the comparison in either order ***)

let INLINE_LOOP_TEST2 = prove
 (`!a:int64 i.
        i < 32
        ==> (val(word_sub (word_add (word_add a (word(16 * i))) (word 16))
                          (word_add a (word 512))) = 0 <=>
             ~(i + 1 < 32)) /\
            (val(word_sub (word_add a (word 512))
                          (word_add (word_add a (word(16 * i))) (word 16))) =
             0 <=> ~(i + 1 < 32))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP (SPECL [`a:int64`; `i:num`] INLINE_LOOP_TEST)
                              th)]) THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN MESON_TAC[]);;

let INLINE_IDX_TEST = prove
 (`!i. i < 32
       ==> (val(word_add (word(16 * i)) (word 18446744073709551120):int64) =
            0 <=> ~(i + 1 < 32))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `(16 * i) MOD 18446744073709551616 = 16 * i` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `i = 31` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `(16 * i + 18446744073709551120) MOD 18446744073709551616 =
    16 * i + 18446744073709551120`
  SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let INLINE_IDX_ADDR = prove
 (`!t:int64 i k.
     word_add (word_add t (word 512)) (word(2 * (8 * i + k))) =
     word_add (word_add t (word(16 * i + 512))) (word(2 * k))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let INLINE_TOMONT_LANE = prove
 (`!x:int16.
     (ival(montred_neon(word_mul (word_sx x) (word 1353))) ==
      (&2 pow 16 * ival x) rem &3329) (mod &3329) /\
     abs(ival(montred_neon(word_mul (word_sx x) (word 1353)))) <= &3328`,
  GEN_TAC THEN REWRITE_TAC[MONTRED_NEON_SCALAR; INT_CONG_RREM] THEN
  MP_TAC(MLKEM_NATIVE_CONGBOUND_RULE undefined
   `montred_scalar(word_mul (word_sx (x:int16)) (word 1353))`) THEN
  MATCH_MP_TAC(TAUT `(p ==> p') /\ (q ==> q') ==> p /\ q ==> p' /\ q'`) THEN
  CONJ_TAC THENL [ALL_TAC; INT_ARITH_TAC] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(a * b:int == c) (mod n)
    ==> (x == a * y * b) (mod n) ==> (x == c * y) (mod n)`) THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

(*** The common steps of the proofs: the 8 coefficients of the iteration
     from the invariant, as one 128-bit word (merge), and the 8 results
     (split) ***)

let INLINE_CHUNK_IN_TAC addr_rule =
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
    [MATCH_MP CHUNK8_INPUT_SPLIT (ASSUME `i < 32`)]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[addr_rule; ADD_CLAUSES] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC;;

let INLINE_CHUNK_SRC_TAC b addr_rule =
  SUBGOAL_THEN
   (subst [b,`b:int64`]
     `!k. k < 8
          ==> read(memory :> bytes16(word_add b (word(2 * (8 * i + k)))))
                s0 = (y:num->int16)(8 * i + k)`)
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[addr_rule; ADD_CLAUSES] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC;;

let INLINE_CHUNK_OUT_TAC addr_rule ths =
  REWRITE_TAC[CHUNK8_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[addr_rule; ADD_CLAUSES] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC ths;;

let INLINE_SPLIT_STORE_TAC v =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE (SIMD_SIMPLIFY_CONV []) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (fun th ->
      can (term_match [] `read (memory :> bytes128 a) s = x`) (concl th) &&
      free_in v (concl th)));;

let INLINE_FINAL_BODY_TAC test out_tac =
  RULE_ASSUM_TAC(REWRITE_RULE [MATCH_MP test (ASSUME `i < 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  CONJ_TAC THENL [out_tac; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let INLINE_INIT_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let INLINE_EXIT_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let INLINE_BODY_START_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC;;

(*** D op= S with pointers ***)

let INLINE_PTR_LOOP mc exec op loop exit dreg sreg ereg =
  let wop = "word_" ^ op in
  let tm = parse_term(Printf.sprintf
   "exists f_events.
      forall e a b (x:num->int16) (y:num->int16) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmlkem_size <= 2 EXP 64 /\\
        nonoverlapping (a,512) (word pc,libmlkem_size) /\\
        nonoverlapping (a,512) (b,512)
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = a /\\ read %s s = b /\\
                  read %s s = word_add a (word 512) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes16(word_add a (word(2 * i))))
                            s = x i) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes16(word_add b (word(2 * i))))
                            s = y i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  read %s s = word_add a (word 512) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes16(word_add a (word(2 * i))))
                            s = %s (x i) (y i)) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a b pc /\\
                     memaccess_inbounds e2 [a,512; b,512] [a,512]))
             (MAYCHANGE [PC; %s; %s] ,, MAYCHANGE [Q0; Q1] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,512)])"
   mc loop dreg sreg ereg exit dreg wop dreg sreg) in
  let inv = parse_term(Printf.sprintf
   "\\i s. read %s s = word_add a (word(16 * i)) /\\
          read %s s = word_add b (word(16 * i)) /\\
          read %s s = word_add a (word 512) /\\
          (!j. j < 256
               ==> read(memory :> bytes16(word_add b (word(2 * j)))) s =
                   (y:num->int16) j) /\\
          (!j. 8 * i <= j /\\ j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   (x:num->int16) j) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   %s (x j) (y j))" dreg sreg ereg wop) in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (b:int64) (pc:num).
      APPEND (f_ev_epil a b pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop a b pc i)) (f_ev_prol a b pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `b:int64`; `x:num->int16`;
                       `y:num->int16`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst exec] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    INLINE_INIT_TAC;
    INLINE_BODY_START_TAC THEN
    INLINE_CHUNK_IN_TAC CHUNK8_ADDR THEN
    INLINE_CHUNK_SRC_TAC `b:int64` CHUNK8_ADDR THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add a (word(16 * i)))) s0`) THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add b (word(16 * i)))) s0`) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
    MAP_EVERY (fun n ->
      ARM_STEPS_TAC exec [n] THEN SIMD_SIMPLIFY_TAC[]) (1--4) THEN
    INLINE_SPLIT_STORE_TAC `a:int64` THEN
    ARM_STEPS_TAC exec (5--6) THEN
    INLINE_FINAL_BODY_TAC INLINE_LOOP_TEST2
      (INLINE_CHUNK_OUT_TAC CHUNK8_ADDR []);
    INLINE_EXIT_TAC]);;

(*** T + 512 += U + 512 with an offset ***)

let INLINE_IDX_ADD_LOOP mc exec loop exit treg ureg ireg preg qreg =
  let tm = parse_term(Printf.sprintf
   "exists f_events.
      forall e t u (x:num->int16) (y:num->int16) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmlkem_size <= 2 EXP 64 /\\
        nonoverlapping (word_add t (word 512),512) (word pc,libmlkem_size) /\\
        nonoverlapping (word_add t (word 512),512)
                       (word_add u (word 512),512)
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = t /\\ read %s s = u /\\ read %s s = word 0 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes16(word_add
                             (word_add t (word 512)) (word(2 * i)))) s =
                           x i) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes16(word_add
                             (word_add u (word 512)) (word(2 * i)))) s =
                           y i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  read %s s = word 512 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes16(word_add
                             (word_add t (word 512)) (word(2 * i)))) s =
                           word_add (x i) (y i)) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events t u pc /\\
                     memaccess_inbounds e2
                      [word_add t (word 512),512; word_add u (word 512),512]
                      [word_add t (word 512),512]))
             (MAYCHANGE [PC; %s; %s; %s] ,, MAYCHANGE [Q0; Q1] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add t (word 512),512)])"
   mc loop treg ureg ireg exit ireg preg qreg ireg) in
  let inv = parse_term(Printf.sprintf
   "\\i s. read %s s = t /\\ read %s s = u /\\ read %s s = word(16 * i) /\\
          (!j. j < 256
               ==> read(memory :> bytes16(word_add (word_add u (word 512))
                                            (word(2 * j)))) s =
                   (y:num->int16) j) /\\
          (!j. 8 * i <= j /\\ j < 256
               ==> read(memory :> bytes16(word_add (word_add t (word 512))
                                            (word(2 * j)))) s =
                   (x:num->int16) j) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add (word_add t (word 512))
                                            (word(2 * j)))) s =
                   word_add (x j) (y j))" treg ureg ireg) in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(t:int64) (u:int64) (pc:num).
      APPEND (f_ev_epil t u pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop t u pc i)) (f_ev_prol t u pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t:int64`; `u:int64`; `x:num->int16`;
                       `y:num->int16`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst exec] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    INLINE_INIT_TAC;
    INLINE_BODY_START_TAC THEN
    INLINE_CHUNK_IN_TAC INLINE_IDX_ADDR THEN
    INLINE_CHUNK_SRC_TAC `word_add u (word 512):int64` INLINE_IDX_ADDR THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add t (word(16 * i + 512)))) s0`) THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add u (word(16 * i + 512)))) s0`) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
    MAP_EVERY (fun n ->
      ARM_STEPS_TAC exec [n] THEN SIMD_SIMPLIFY_TAC[]) (1--7) THEN
    INLINE_SPLIT_STORE_TAC `t:int64` THEN
    ARM_STEPS_TAC exec (8--9) THEN
    INLINE_FINAL_BODY_TAC INLINE_IDX_TEST
      (INLINE_CHUNK_OUT_TAC INLINE_IDX_ADDR [WORD_ADD_SYM]);
    INLINE_EXIT_TAC]);;

(*** The Montgomery form in place, pointer in dreg, end in endreg ***)

let INLINE_TOMONT_LOOP_REG mc exec loop exit dreg endreg =
  let tm = parse_term(Printf.sprintf
   "exists f_events.
      forall e a (x:num->int16) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmlkem_size <= 2 EXP 64 /\\
        nonoverlapping (a,512) (word pc,libmlkem_size)
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = a /\\ read %s s = word_add a (word 512) /\\
                  read Q3 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\\
                  read Q4 s = word 0x05490549054905490549054905490549 /\\
                  read Q5 s = word 0xf301f301f301f301f301f301f301f301 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes16(word_add a (word(2 * i))))
                            s = x i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  read %s s = word_add a (word 512) /\\
                  (!i. i < 256
                       ==> let z_i = read(memory :> bytes16
                                       (word_add a (word(2 * i)))) s in
                           (ival z_i == (tomont_3329 (ival o x)) i)
                           (mod &3329) /\\
                           abs(ival z_i) <= &3328) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a pc /\\
                     memaccess_inbounds e2 [a,512] [a,512]))
             (MAYCHANGE [PC; %s] ,, MAYCHANGE [Q0; Q1; Q2] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,512)])"
   mc loop dreg endreg exit dreg dreg) in
  let inv = parse_term(Printf.sprintf
   "\\i s. read %s s = word_add a (word(16 * i)) /\\
          read %s s = word_add a (word 512) /\\
          read Q3 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\\
          read Q4 s = word 0x05490549054905490549054905490549 /\\
          read Q5 s = word 0xf301f301f301f301f301f301f301f301 /\\
          (!j. 8 * i <= j /\\ j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   (x:num->int16) j) /\\
          (!j. j < 8 * i
               ==> let z_j = read(memory :> bytes16
                                (word_add a (word(2 * j)))) s in
                   (ival z_j == (tomont_3329 (ival o x)) j) (mod &3329) /\\
                   abs(ival z_j) <= &3328)" dreg endreg) in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num).
      APPEND (f_ev_epil a pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop a pc i)) (f_ev_prol a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst exec] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    INLINE_INIT_TAC;
    INLINE_BODY_START_TAC THEN
    INLINE_CHUNK_IN_TAC CHUNK8_ADDR THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add a (word(16 * i)))) s0`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
    MAP_EVERY (fun n ->
      ARM_STEPS_TAC exec [n] THEN SIMD_SIMPLIFY_TAC[montred_neon]) (1--9) THEN
    INLINE_SPLIT_STORE_TAC `a:int64` THEN
    ARM_STEPS_TAC exec (10--11) THEN
    INLINE_FINAL_BODY_TAC INLINE_LOOP_TEST
     (INLINE_CHUNK_OUT_TAC CHUNK8_ADDR [] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[tomont_3329; o_THM; INLINE_TOMONT_LANE]);
    INLINE_EXIT_TAC]);;

let INLINE_TOMONT_LOOP mc exec loop exit endreg =
  INLINE_TOMONT_LOOP_REG mc exec loop exit "X2" endreg;;

(*** D op= S with an index I from 0 added to both bases:
       ldr q0, [D, I]; ldr q1, [S, I]; op v0.8h, v0.8h, v1.8h;
       str q0, [D, I]; add I, I, #16; cmp I, #0x200; b.ne ***)

let INLINE_REG_IDX_LOOP mc exec op loop exit dreg sreg ireg =
  let wop = "word_" ^ op in
  let tm = parse_term(Printf.sprintf
   "exists f_events.
      forall e a b (x:num->int16) (y:num->int16) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmlkem_size <= 2 EXP 64 /\\
        nonoverlapping (a,512) (word pc,libmlkem_size) /\\
        nonoverlapping (a,512) (b,512)
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = a /\\ read %s s = b /\\ read %s s = word 0 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes16(word_add a (word(2 * i))))
                            s = x i) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes16(word_add b (word(2 * i))))
                            s = y i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  read %s s = word 512 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes16(word_add a (word(2 * i))))
                            s = %s (x i) (y i)) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a b pc /\\
                     memaccess_inbounds e2 [a,512; b,512] [a,512]))
             (MAYCHANGE [PC; %s] ,, MAYCHANGE [Q0; Q1] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,512)])"
   mc loop dreg sreg ireg exit ireg wop ireg) in
  let inv = parse_term(Printf.sprintf
   "\\i s. read %s s = a /\\ read %s s = b /\\ read %s s = word(16 * i) /\\
          (!j. j < 256
               ==> read(memory :> bytes16(word_add b (word(2 * j)))) s =
                   (y:num->int16) j) /\\
          (!j. 8 * i <= j /\\ j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   (x:num->int16) j) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   %s (x j) (y j))" dreg sreg ireg wop) in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (b:int64) (pc:num).
      APPEND (f_ev_epil a b pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop a b pc i)) (f_ev_prol a b pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `b:int64`; `x:num->int16`;
                       `y:num->int16`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst exec] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    INLINE_INIT_TAC;
    INLINE_BODY_START_TAC THEN
    INLINE_CHUNK_IN_TAC CHUNK8_ADDR THEN
    INLINE_CHUNK_SRC_TAC `b:int64` CHUNK8_ADDR THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add a (word(16 * i)))) s0`) THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add b (word(16 * i)))) s0`) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
    MAP_EVERY (fun n ->
      ARM_STEPS_TAC exec [n] THEN SIMD_SIMPLIFY_TAC[]) (1--4) THEN
    INLINE_SPLIT_STORE_TAC `a:int64` THEN
    ARM_STEPS_TAC exec (5--7) THEN
    INLINE_FINAL_BODY_TAC INLINE_IDX_TEST
      (INLINE_CHUNK_OUT_TAC CHUNK8_ADDR []);
    INLINE_EXIT_TAC]);;
