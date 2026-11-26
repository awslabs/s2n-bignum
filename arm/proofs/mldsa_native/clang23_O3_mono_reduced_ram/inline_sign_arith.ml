(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the inlined polynomial loops of verify_internal and            *)
(* signature_internal in mldsa-native's clang 23 -O3 monolithic reduced-RAM  *)
(* build: poly_reduce, poly_chknorm, poly_decompose, poly_use_hint and       *)
(* poly_pointwise_montgomery. Each generator proves the loop of one shape,   *)
(* from its head to its exit, with the registers as parameters (see          *)
(* inline_sign.ml for INLINE_CADDQ_LOOP, whose conventions this follows).    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign.ml";;
needs "arm/proofs/utils/mldsa_native_rounding.ml";;

(*** Replace each @key@ in a template by its value ***)

let INLINE_FILL (tmpl:string) (kv:(string*string) list) =
  let replace s (k,v) =
    let key = "@" ^ k ^ "@" in
    let n = String.length key in
    let b = Buffer.create (String.length s) in
    let i = ref 0 in
    while !i < String.length s do
      if !i + n <= String.length s && String.sub s !i n = key
      then (Buffer.add_string b v; i := !i + n)
      else (Buffer.add_char b s.[!i]; incr i)
    done;
    Buffer.contents b in
  List.fold_left replace tmpl kv;;

(* ------------------------------------------------------------------------- *)
(* Chunks of 8 coefficients (two 128-bit vectors), as the loops of clang     *)
(* with LDP/STP of Q registers handle them.                                  *)
(* ------------------------------------------------------------------------- *)

let INLINE_CHUNK8_INPUT_SPLIT = prove
 (`!P i. i < 32
         ==> ((!j. 8 * i <= j /\ j < 256 ==> P j) <=>
              (!j. 8 * (i + 1) <= j /\ j < 256 ==> P j) /\
              (!k. k < 8 ==> P(8 * i + k)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `8 * (i + 1) <= j` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - 8 * i`) THEN
    ASM_SIMP_TAC[ARITH_RULE `8 * i <= j ==> 8 * i + (j - 8 * i) = j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let INLINE_CHUNK8_OUTPUT_SPLIT = prove
 (`!P i. (!j. j < 8 * (i + 1) ==> P j) <=>
         (!j. j < 8 * i ==> P j) /\ (!k. k < 8 ==> P(8 * i + k))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `j < 8 * i` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - 8 * i`) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(j < 8 * i) ==> 8 * i + (j - 8 * i) = j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(*** The address of coefficient 8 * i + k of the polynomial at word_add a ***)
(*** (word k0), as the simulator writes the addresses of the two vectors ***)
(*** of the iteration (word_add a (word (32 * i + k0)) and the same with ***)
(*** k0 + 16) and READ_MEMORY_MERGE_CONV writes the lanes of each.       ***)

let INLINE_LANE_ADDRS (bases:string*string*string) =
  let (pa,b0,b1) = bases in
  let off b n = if n = 0 then b else Printf.sprintf "word_add (%s) (word %d)" b n in
  map (fun (lhs,rhs) ->
        prove(parse_term(Printf.sprintf
          "!a i. word_add %s (word (%s)):int64 = %s" pa lhs rhs),
          CONV_TAC WORD_RULE))
   [ "4 * (8 * i)",      off b0 0;  "4 * (8 * i + 1)", off b0 4;
     "4 * (8 * i + 2)",  off b0 8;  "4 * (8 * i + 3)", off b0 12;
     "4 * (8 * i + 4)",  off b1 0;  "4 * (8 * i + 5)", off b1 4;
     "4 * (8 * i + 6)",  off b1 8;  "4 * (8 * i + 7)", off b1 12 ];;

(*** The polynomial and the addresses of the two vectors of an iteration, ***)
(*** as the simulator writes them                                        ***)

let INLINE_BASES kind k0 =
  if kind = "21" then
    ("a", "word_add a (word_sub (word (32 * i + 16)) (word 16))",
          "word_add a (word_sub (word (32 * i + 16)) (word 0))")
  else
    let pa = if k0 = 0 then "a" else Printf.sprintf "(word_add a (word %d))" k0 in
    let base c = if k0 + c = 0 then "word_add a (word (32 * i))"
                 else Printf.sprintf "word_add a (word (32 * i + %d))" (k0 + c) in
    (pa, base 0, base 16);;

(*** The lanes of the 32-bit result, as in gcc12_O2/poly_reduce_proof.ml ***)

let INLINE_REDUCE32_LANE = prove
 (`!x:int32. word_add x (word_mul (word_ishr (word_add x (word 4194304)) 23)
                                  (word 4286586879)) =
             mld_reduce32 x`,
  REWRITE_TAC[mld_reduce32; WORD_RULE
   `word_sub x (word_mul t c):N word =
    word_add x (word_mul t (word_neg c))`] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[]);;

(*** The address register of the loops that count the byte offset up to 0 ***)

let INLINE_NEG_PTR = prove
 (`!a i. word_add (word_add a (word 1024)) (word_sub (word (32 * i)) (word 1024))
         :int64 = word_add a (word (32 * i))`,
  CONV_TAC WORD_RULE);;

let INLINE_NEG1024 = prove
 (`word_sub (word 0) (word 1024):int64 = word 18446744073709550592`,
  CONV_TAC WORD_REDUCE_CONV);;

let INLINE_NEG_TEST = prove
 (`!i. i < 32 ==> (val (word_add (word_sub (word (32 * i)) (word 1024)) (word 32):int64) = 0 <=> 32 * i + 32 = 1024)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_add (word_sub (word (32 * i)) (word 1024)) (word 32):int64 = word_sub (word (32 * i + 32)) (word 1024)` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `(32 * i + 32) MOD 2 EXP 64 = 32 * i + 32` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1024 MOD 2 EXP 64 = 1024` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ARITH_TAC; ARITH_TAC]);;

let INLINE_BASE_FIX = map (fun s -> prove(parse_term s, CONV_TAC WORD_RULE))
 ["!a i. word_add a (word_sub (word (32 * i + 16)) (word 16)):int64 =
         word_add a (word (32 * i))";
  "!a i. word_add a (word_sub (word (32 * i + 16)) (word 0)):int64 =
         word_add a (word (32 * i + 16))"];;

let INLINE_FRAME_FIX_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> is_const t && fst(dest_const t) = "MAYCHANGE"))
           (concl th)
    then REWRITE_RULE INLINE_BASE_FIX th else th);;

let INLINE_PTR16 = prove
 (`!a i. word_sub (word_add a (word (32 * i + 16))) (word 16):int64 =
         word_add a (word (32 * i))`,
  CONV_TAC WORD_RULE);;

let INLINE_CNT_STEP = prove
 (`!i. i < 32 ==> word_sub (word (256 - 8 * i)) (word 8):int64 =
                  word (256 - 8 * (i + 1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `256 - 8 * (i + 1) = (256 - 8 * i) - 8` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_SUB] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let INLINE_CNT_TEST = prove
 (`!i. i < 32 ==> (val (word (256 - 8 * (i + 1)):int64) = 0 <=>
                   256 - 8 * (i + 1) = 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `(256 - 8 * (i + 1)) MOD 2 EXP 64 = 256 - 8 * (i + 1)`
    SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; REFL_TAC]);;

(*** The body of a loop with 8 coefficients of x per iteration: the input ***)
(*** facts for the 8 lanes, merged into two 128-bit loads, n steps, and   ***)
(*** the two 128-bit stores split into lanes again. The polynomial is at  ***)
(*** word_add a (word k0).                                                ***)

let INLINE_VEC8_BODY_TAC exec (bases:string*string*string) hook n =
  let (_,a0,a1) = bases in
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
    [MATCH_MP INLINE_CHUNK8_INPUT_SPLIT (ASSUME `i < 32`)] o
    check (fun th -> is_forall(concl th) &&
                     free_in `x:num->int32` (concl th) &&
                     not(free_in `mld_reduce32` (concl th)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC(INLINE_LANE_ADDRS bases) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  MP_TAC(READ_MEMORY_MERGE_CONV 2 (parse_term(Printf.sprintf
    "read (memory :> bytes128 (%s)) s0" a0))) THEN
  MP_TAC(READ_MEMORY_MERGE_CONV 2 (parse_term(Printf.sprintf
    "read (memory :> bytes128 (%s)) s0" a1))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
  ARM_STEPS_TAC exec [1] THEN hook THEN
  MAP_EVERY (fun k -> ARM_STEPS_TAC exec [k] THEN SIMD_SIMPLIFY_TAC[])
            (2--n) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE(SIMD_SIMPLIFY_CONV []) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
    check (fun th ->
      can (term_match [] `read (memory :> bytes128 a) s = x`) (concl th) &&
      not(free_in `s0:armstate` (concl th)))));;

let INLINE_VEC8_FINAL_TAC bases pre ths lanes =
  pre THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC ths THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[INLINE_CHUNK8_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC(INLINE_LANE_ADDRS bases) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC lanes THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* poly_reduce, as clang -O3 has inlined it: a[i] := mld_reduce32 a[i], in 32 *)
(* iterations of 8 coefficients (two vectors, v0, v1; t = (v + 2^22) >> 23,   *)
(* v := v + t * (-q) with mla). The vectors of 2^22 (C4) and -q (C5) are in   *)
(* registers. Four shapes (the registers are those of instances.py, in the    *)
(* order of first appearance; X for general and Q for vector registers):      *)
(*                                                                            *)
(*   "9"  (12 instructions, 12 instances), the polynomial at a:               *)
(*     R0 = x9 (temporary), R1 = a, R2 = x8 (byte offset, from 0),            *)
(*     R3, R4, R5, R7 = v0, v1, v2, v3 (temporaries), R6 = C4, R8 = C5        *)
(*       add R0, R1, R2; add R2, R2, #0x20; ldp q.R3, q.R4, [R0];             *)
(*       cmp R2, #0x400; ...; stp q.R3, q.R4, [R0]; b.ne                      *)
(*   "10" (14 instructions, 11 instances), the polynomial at a + k0, with     *)
(*     ldr q.R3, [R0, #k0]; ldr q.R4, [R0, #k0 + 16]; ... str, str, as above  *)
(*   "60" (13 instructions, 4 instances), the offset counting up to 0:        *)
(*     adds R2, R2, #0x20 (R2 from -1024), ldr q.R3, [R0, #k]; ...,           *)
(*     with the polynomial at a + k - 1024                                    *)
(*   "21" (11 instructions, 3 instances), after poly_sub:                     *)
(*     R0, R1 = v0, v1, R2 = x8 (pointer, from a + 16), R3 = x9 (count, 256), *)
(*     R4 = v2, R5 = C4, R6 = v3, R7 = C5                                     *)
(*       ldp q.R0, q.R1, [R2, #-16]; subs R3, R3, #8; ...;                    *)
(*       stp q.R0, q.R1, [R2, #-16]; add R2, R2, #0x20; b.ne                  *)
(* ------------------------------------------------------------------------- *)

let INLINE_REDUCE_LOOP_TERM kind mc loop exit k0 (rs:string list) =
  let r k = List.nth rs k in
  let c4 = "word 0x00400000004000000040000000400000"
  and c5 = "word 0xff801fffff801fffff801fffff801fff" in
  let pa = if k0 = 0 then "a" else Printf.sprintf "(word_add a (word %d))" k0 in
  let (pre,post,modregs,qmod,c4r,c5r) =
    if kind = "21" then
      (Printf.sprintf "read %s s = word_add a (word 16) /\\ read %s s = word 256"
         (r 2) (r 3),
       Printf.sprintf "read %s s = word_add a (word 1040) /\\ read %s s = word 0"
         (r 2) (r 3),
       Printf.sprintf "%s; %s" (r 2) (r 3),
       Printf.sprintf "%s; %s; %s; %s" (r 0) (r 1) (r 4) (r 6),
       r 5, r 7)
    else
      (Printf.sprintf "read %s s = %s /\\ read %s s = %s" (r 1)
         (if kind = "60" then "word_add a (word 1024)" else "a") (r 2)
         (if kind = "60" then "word 18446744073709550592" else "word 0"),
       Printf.sprintf "read %s s = %s" (r 2)
         (if kind = "60" then "word 0" else "word 1024"),
       Printf.sprintf "%s; %s" (r 0) (r 2),
       Printf.sprintf "%s; %s; %s; %s" (r 3) (r 4) (r 5) (r 7),
       r 6, r 8) in
  parse_term(INLINE_FILL
   "exists f_events.
      forall e a (x:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (@pa@,1024)) [(word pc,libmldsa_size)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) @mc@ /\\
                  read PC s = word (pc + @loop@) /\\
                  @pre@ /\\
                  read @c4r@ s = @c4@ /\\ read @c5r@ s = @c5@ /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add @pa@ (word(4 * i))))
                             s = x i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + @exit@) /\\
                  @post@ /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add @pa@ (word(4 * i))))
                             s = mld_poly_reduce x i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a pc /\\
                     memaccess_inbounds e2 [@pa@,1024] [@pa@,1024]))
             (MAYCHANGE [PC; @modregs@] ,, MAYCHANGE [@qmod@] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(@pa@,1024)])"
   ["pa",pa; "mc",mc; "loop",loop; "exit",exit; "pre",pre; "post",post;
    "c4",c4; "c5",c5; "c4r",c4r; "c5r",c5r; "modregs",modregs; "qmod",qmod]);;

let INLINE_REDUCE_LOOP kind mc exec loop exit k0 (rs:string list) =
  let r k = List.nth rs k in
  let tm = INLINE_REDUCE_LOOP_TERM kind mc loop exit k0 rs in
  let pa = if k0 = 0 then "a" else Printf.sprintf "(word_add a (word %d))" k0 in
  let (c4r,c5r) = if kind = "21" then (r 5,r 7) else (r 6,r 8) in
  let (regs,nsteps) =
    match kind with
      "9"  -> (Printf.sprintf "read %s s = a /\\ read %s s = word(32 * i)"
                 (r 1) (r 2), 12)
    | "10" -> (Printf.sprintf "read %s s = a /\\ read %s s = word(32 * i)"
                 (r 1) (r 2), 14)
    | "60" -> (Printf.sprintf
                 "read %s s = word_add a (word 1024) /\\ read %s s = word_sub (word(32 * i)) (word 1024)"
                 (r 1) (r 2), 13)
    | "21" -> (Printf.sprintf
                 "read %s s = word_add a (word(32 * i + 16)) /\\ read %s s = word(256 - 8 * i)"
                 (r 2) (r 3), 11)
    | _ -> failwith "INLINE_REDUCE_LOOP: unknown kind" in
  let inv = parse_term(INLINE_FILL
   "\\i s. @regs@ /\\
          read @c4r@ s = word 0x00400000004000000040000000400000 /\\
          read @c5r@ s = word 0xff801fffff801fffff801fffff801fff /\\
          (!j. 8 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add @pa@ (word(4 * j)))) s =
                   (x:num->int32) j) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes32(word_add @pa@ (word(4 * j)))) s =
                   mld_reduce32 (x j))"
   ["regs",regs; "c4r",c4r; "c5r",c5r; "pa",pa]) in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num).
      APPEND (f_ev_epil a pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop a pc i)) (f_ev_prol a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `x:num->int32`;
                       `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; mld_poly_reduce;
              fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; CONJUNCT1 LT; LE_0;
                WORD_ADD_0] THEN
    ASM_REWRITE_TAC[INLINE_NEG1024] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    INLINE_VEC8_BODY_TAC exec (INLINE_BASES kind k0)
      (if kind = "60" then RULE_ASSUM_TAC(REWRITE_RULE[INLINE_NEG_PTR])
       else ALL_TAC) (nsteps - 1) THEN
    ARM_STEPS_TAC exec [nsteps] THEN
    INLINE_VEC8_FINAL_TAC (INLINE_BASES kind k0)
      (if kind = "21" then INLINE_FRAME_FIX_TAC else ALL_TAC)
      (match kind with
         "60" -> [MATCH_MP INLINE_NEG_TEST (ASSUME `i < 32`)]
       | "21" -> [INLINE_PTR16; MATCH_MP INLINE_CNT_STEP (ASSUME `i < 32`);
                MATCH_MP INLINE_CNT_TEST (ASSUME `i < 32`)]
       | _ -> [])
      [INLINE_REDUCE32_LANE];

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[WORD_SUB_REFL] THEN DISCHARGE_SAFETY_PROPERTY_TAC]);;

(*** The instances: (kind, function, head label, exit label, k0, registers) ***)

let INLINE_REDUCE_INSTANCES = [
  ("9","mldsa44_signature_internal","loop14","loop14_exit",0,["X9";"X19";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("9","mldsa44_signature_internal","loop32","loop32_exit",0,["X9";"X20";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("9","mldsa44_signature_internal","loop43","loop43_exit",0,["X9";"X23";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("9","mldsa44_verify_internal","loop9","loop9_exit",0,["X9";"X24";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("9","mldsa65_signature_internal","loop18","loop18_exit",0,["X9";"X24";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("9","mldsa65_signature_internal","loop42","loop42_exit",0,["X9";"X22";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("9","mldsa65_signature_internal","loop53","loop53_exit",0,["X9";"X20";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("9","mldsa65_verify_internal","loop10","loop10_exit",0,["X9";"X25";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("9","mldsa87_signature_internal","loop22","loop22_exit",0,["X9";"X19";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("9","mldsa87_signature_internal","loop49","loop49_exit",0,["X9";"X23";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("9","mldsa87_signature_internal","loop60","loop60_exit",0,["X9";"X27";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("9","mldsa87_verify_internal","loop12","loop12_exit",0,["X9";"X23";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("10","mldsa44_signature_internal","loop15","loop15_exit",1024,["X9";"X19";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("10","mldsa44_signature_internal","loop16","loop16_exit",2048,["X9";"X19";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("10","mldsa44_signature_internal","loop17","loop17_exit",3072,["X9";"X19";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("10","mldsa65_signature_internal","loop19","loop19_exit",1024,["X9";"X24";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("10","mldsa65_signature_internal","loop20","loop20_exit",2048,["X9";"X24";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("10","mldsa65_signature_internal","loop21","loop21_exit",3072,["X9";"X24";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("10","mldsa65_signature_internal","loop22","loop22_exit",4096,["X9";"X24";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("10","mldsa87_signature_internal","loop23","loop23_exit",1024,["X9";"X19";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("10","mldsa87_signature_internal","loop24","loop24_exit",2048,["X9";"X19";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("10","mldsa87_signature_internal","loop25","loop25_exit",3072,["X9";"X19";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("10","mldsa87_signature_internal","loop26","loop26_exit",4096,["X9";"X19";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("60","mldsa65_signature_internal","loop23","loop23_exit",6144,["X9";"X24";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("60","mldsa87_signature_internal","loop27","loop27_exit",6144,["X9";"X19";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("60","mldsa87_signature_internal","loop28","loop28_exit",7168,["X9";"X19";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("60","mldsa87_signature_internal","loop29","loop29_exit",8192,["X9";"X19";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]);
  ("21","mldsa44_signature_internal","loop39","loop39_exit",0,["Q0";"Q1";"X8";"X9";"Q2";"Q4";"Q3";"Q5"]);
  ("21","mldsa65_signature_internal","loop49","loop49_exit",0,["Q0";"Q1";"X8";"X9";"Q2";"Q4";"Q3";"Q5"]);
  ("21","mldsa87_signature_internal","loop56","loop56_exit",0,["Q0";"Q1";"X8";"X9";"Q2";"Q4";"Q3";"Q5"])
];;

let INLINE_MC = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc";;

let INLINE_REDUCE_OF_INSTANCE (kind,fn,hl,el,k0,rs) =
  let l = fn ^ "_" ^ hl and e = fn ^ "_" ^ el in
  INLINE_REDUCE_LOOP kind INLINE_MC (INLINE_LOOP_EXEC l e) l e k0 rs;;

(* ------------------------------------------------------------------------- *)
(* poly_chknorm, as clang -O3 has inlined it: the accumulated mask of        *)
(* (B - 1) - |a[i]| < 0 over the 256 coefficients, one coefficient per       *)
(* iteration, no early exit. The code computes |a| as                        *)
(*   m = sx(a) >> 31; |a| = (-a & m) | (a & ~m)                              *)
(* and the sign of w_b - |a| (+/- an immediate c, folded into the bound B)   *)
(* by SXTW and LSR #31. The bound B is in W register R5 as follows (b is the  *)
(* bound B of mld_poly_chknorm), the other registers are those of            *)
(* instances.py:                                                              *)
(*   R0 = x10, R3 = x11, R4 = x12 (temporaries), R1 = a, R2 = x9 (byte        *)
(*   offset, from 0), R6 = x8 (the mask, ORed with the new one)               *)
(*   "17" (14 instructions): sub w10, R5, w10               R5 = b - 1        *)
(*   "22" (15, immediate c):  sub w10, R5, w10; sub w10, w10, #c              *)
(*                                                         R5 = b - 1 + c    *)
(*   "66" (15, immediate c):  sub w10, R5, w10; add w10, w10, #c              *)
(*                                                         R5 = b - 1 - c    *)
(*   "24" (14): eon w10, w10, w11; add w10, w10, R5        R5 = b            *)
(* Before the loop R6 holds an arbitrary mask m0 (its low 32 bits), after it  *)
(* m0 | mld_poly_chknorm a b.                                                 *)
(* ------------------------------------------------------------------------- *)


(*** The absolute value as the code selects it, and the 32-bit views of the ***)
(*** 64-bit values that SXTW and LSR #31 compute                            ***)

let INLINE_CT_ABS_SELECT = prove
 (`!y:int32. mld_ct_abs y =
             word_xor (word_and (word_xor (word_sub (word 0) y) y)
                                (word_ishr y 31)) y`,
  REWRITE_TAC[mld_ct_abs; GSYM MSB_IVAL; DIMINDEX_32;
              WORD_RULE `word_neg(y:N word) = word_sub (word 0) y`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN BITBLAST_TAC);;

let INLINE_EXISTS_LT_SUC = prove
 (`!P i. (?j. j < i + 1 /\ P j) <=> (?j. j < i /\ P j) \/ P i`,
  REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN MESON_TAC[]);;

let INLINE_MASK_SX = prove
 (`!z:int32. word_zx(word_ushr (word_sxfrom 31
               (word_subword (word_zx z:int64) (0,32):int64)) 31:int64):int32 =
             word_ishr z 31`,
  BITBLAST_TAC);;

let INLINE_ZX_SX = prove
 (`!y:int32. word_zx(word_sx y:int64):int32 = y`, BITBLAST_TAC);;

let INLINE_MASK_SHIFT = prove
 (`!y:int32. word_zx(word_ushr (word_sx y:int64) 31):int32 = word_ishr y 31`,
  BITBLAST_TAC);;

let INLINE_ABS_FORMS = prove
 (`!x:int32. ((word_sub (word 0) x && word_ishr x 31) ||
              (x && ~~(word_ishr x 31))) =
             (((word_sub (word 0) x ^^ x) && word_ishr x 31) ^^ x)`,
  BITBLAST_TAC);;

let INLINE_ONES_OR_32 = prove
 (`!y:int32. word_or (word 4294967295) y = word 4294967295`, BITBLAST_TAC);;

let INLINE_OR_ONES_32 = prove
 (`!y:int32. word_or y (word 4294967295) = word 4294967295`, BITBLAST_TAC);;

let INLINE_EON_FORM = prove
 (`!(x:int32) (b:int32).
     word_add ((word_sub (word 0) x && word_ishr x 31) ^^
               ~~(x && ~~word_ishr x 31)) b =
     word_sub (word_sub b (word 1))
              (((word_sub (word 0) x ^^ x) && word_ishr x 31) ^^ x)`,
  BITBLAST_TAC);;

let INLINE_BOUND_CANCEL = map (fun s -> prove(parse_term s, CONV_TAC WORD_RULE))
 ["!b y c:int32. word_sub (word_sub (word_add b c) y) c = word_sub b y";
  "!b y c:int32. word_add (word_sub (word_sub b c) y) c = word_sub b y"];;

(*** The mask accumulated for coefficients 0, ..., i, as a function of the ***)
(*** one for 0, ..., i - 1 and the new one                                  ***)

let INLINE_CHKNORM_MASK_TAC kind =
  REWRITE_TAC[INLINE_EXISTS_LT_SUC; GSYM INLINE_CT_ABS_SELECT] THEN
  SPEC_TAC(`?j. j < i /\ ival(word_sub (word_sub (b:int32) (word 1))
                                       (mld_ct_abs((x:num->int32) j))) < &0`,
           `p:bool`) THEN
  GEN_TAC THEN ASM_CASES_TAC `p:bool` THENL
   [ASM_REWRITE_TAC[GSYM WORD_ISHR_31_COND; INLINE_CT_ABS_SELECT] THEN
    REWRITE_TAC[INLINE_ONES_OR_32; INLINE_OR_ONES_32; WORD_ZX_ZX_32_64_32];
    ASM_REWRITE_TAC[GSYM WORD_ISHR_31_COND; INLINE_CT_ABS_SELECT] THEN
    REWRITE_TAC[INLINE_MASK_SX; WORD_ZX_ZX_32_64_32; INLINE_ZX_SX;
                INLINE_MASK_SHIFT; INLINE_ABS_FORMS; WORD_OR_0] THEN
    (if kind = "24" then REWRITE_TAC[INLINE_EON_FORM]
     else REWRITE_TAC INLINE_BOUND_CANCEL)];;

let INLINE_CHKNORM_BOUND kind c =
  match kind with
    "17" -> "word_sub b (word 1)"
  | "22" -> Printf.sprintf "word_add (word_sub b (word 1)) (word %d)" c
  | "66" -> Printf.sprintf "word_sub (word_sub b (word 1)) (word %d)" c
  | "24" -> "b"
  | _ -> failwith "INLINE_CHKNORM_BOUND";;

let INLINE_CHKNORM_LOOP_TERM kind mc loop exit c (rs:string list) =
  let r k = List.nth rs k in
  parse_term(INLINE_FILL
   "exists f_events.
      forall e a (x:num->int32) (b:int32) (m0:int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (a,1024)) [(word pc,libmldsa_size)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) @mc@ /\\
                  read PC s = word (pc + @loop@) /\\
                  read @a@ s = a /\\ read @i@ s = word 0 /\\
                  read @b@ s = word_zx (@bound@) /\\
                  read @acc@ s = word_zx m0 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + @exit@) /\\
                  read @i@ s = word 1024 /\\
                  read @acc@ s = word_zx (word_or m0 (mld_poly_chknorm x b)) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a pc /\\
                     memaccess_inbounds e2 [a,1024] []))
             (MAYCHANGE [PC; @t0@; @t3@; @t4@; @i@; @acc@] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])"
   ["mc",mc; "loop",loop; "exit",exit; "a",r 1; "i",r 2; "b",r 5; "acc",r 6;
    "t0",r 0; "t3",r 3; "t4",r 4; "bound",INLINE_CHKNORM_BOUND kind c]);;

let INLINE_CHKNORM_LOOP kind mc exec loop exit c (rs:string list) =
  let r k = List.nth rs k in
  let tm = INLINE_CHKNORM_LOOP_TERM kind mc loop exit c rs in
  let nsteps = if kind = "22" || kind = "66" then 15 else 14 in
  let inv = parse_term(INLINE_FILL
   "\\i s. read @a@ s = a /\\ read @i@ s = word(4 * i) /\\
          read @b@ s = word_zx (@bound@) /\\
          read @acc@ s = word_zx (word_or (m0:int32)
            (if ?j. j < i /\\
                    ival(word_sub (word_sub b (word 1))
                                  (mld_ct_abs((x:num->int32) j))) < &0
             then word 4294967295 else word 0)) /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s = x j)"
   ["a",r 1; "i",r 2; "b",r 5; "acc",r 6;
    "bound",INLINE_CHKNORM_BOUND kind c]) in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num).
      APPEND (f_ev_epil a pc)
       (APPEND (ENUMERATEL 256 (\i. f_ev_loop a pc i)) (f_ev_prol a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `x:num->int32`;
                       `b:int32`; `m0:int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0;
                NOT_EXISTS_THM; WORD_OR_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `x:num->int32` (concl th))) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
    ARM_STEPS_TAC exec (1--nsteps) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    TRY(INLINE_CHKNORM_MASK_TAC kind THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[mld_poly_chknorm] THEN DISCHARGE_SAFETY_PROPERTY_TAC]);;
let INLINE_CHKNORM_INSTANCES = [
  ("17","mldsa44_signature_internal","loop33","loop33_exit",0,["X10";"X20";"X9";"X11";"X12";"X13";"X8"]);
  ("17","mldsa65_signature_internal","loop50","loop50_exit",0,["X10";"X23";"X9";"X11";"X12";"X13";"X8"]);
  ("17","mldsa87_signature_internal","loop57","loop57_exit",0,["X10";"X24";"X9";"X11";"X12";"X13";"X8"]);
  ("22","mldsa44_signature_internal","loop40","loop40_exit",79,["X10";"X27";"X9";"X11";"X12";"X13";"X8"]);
  ("66","mldsa65_signature_internal","loop43","loop43_exit",314,["X10";"X22";"X9";"X11";"X12";"X24";"X8"]);
  ("66","mldsa65_signature_internal","loop54","loop54_exit",196,["X10";"X20";"X9";"X11";"X12";"X13";"X8"]);
  ("66","mldsa87_signature_internal","loop50","loop50_exit",390,["X10";"X23";"X9";"X11";"X12";"X13";"X8"]);
  ("66","mldsa87_signature_internal","loop61","loop61_exit",120,["X10";"X27";"X9";"X11";"X12";"X13";"X8"]);
  ("24","mldsa44_signature_internal","loop44","loop44_exit",0,["X10";"X23";"X9";"X11";"X12";"X13";"X8"])
];;

let INLINE_CHKNORM_OF_INSTANCE (kind,fn,hl,el,c,rs) =
  let l = fn ^ "_" ^ hl and e = fn ^ "_" ^ el in
  INLINE_CHKNORM_LOOP kind INLINE_MC (INLINE_LOOP_EXEC l e) l e c rs;;

(* ------------------------------------------------------------------------- *)
(* STATUS: INLINE_DECOMPOSE_LOOP proved shape "12" (44 signature loop22, 12   *)
(* seconds) before the address normalisation `normk` for k0 <> 0 was added;  *)
(* "13", "62" and "63" are NOT yet proved (a test run of them did not finish *)
(* in 10 minutes; the cause is not known, possibly the BITBLAST of the        *)
(* gamma2 = (q-1)/32 lanes). No instance list yet.                            *)
(*                                                                           *)
(* poly_decompose, as clang -O3 has inlined it (fused with the packing of    *)
(* w1 in polyveck_decompose_pack_w1): for each coefficient, a1[i] = the high *)
(* part and a[i] := the low part, one coefficient per iteration, with the    *)
(* constants of the decomposition in registers. gamma2 = (q - 1) / 88        *)
(* (ML-DSA-44, "12" and "13") or (q - 1) / 32 (ML-DSA-65 and 87, "62" and    *)
(* "63"). The polynomial a is at a + k0, the high parts at a1. All registers *)
(* are general registers (instances.py names R0, R1, ...):                   *)
(*                                                                           *)
(*   "12" (24 instr.) ldr w.R0, [R1, R2]; ..., a1 = R6, idx = R2             *)
(*        constants R4 = 11275, R5 = 2^23, R8 = 43, R9 = -2 * gamma2,         *)
(*        R10 = (q - 1) / 2, R11 = -q                                         *)
(*   "13" (25 instr.) add R0, R1, R2; ldr w.R3, [R0, #k0]; ..., a1 = R7       *)
(*        constants R5, R6, R9, R10, R11, R12 as above                        *)
(*   "62" (20 instr.) ldr w.R0, [R1, R2]; ..., a1 = R4, idx = R2             *)
(*        constants R5 = -2 * gamma2, R6 = (q - 1) / 2, R8 = -q               *)
(*   "63" (21 instr.) add R0, R1, R2; ldr w.R3, [R0, #k0]; ..., a1 = R5      *)
(*        constants R6 = -2 * gamma2, R7 = (q - 1) / 2, R9 = -q               *)
(* The byte offset R2 counts from 0 to 1024 in steps of 4.                   *)
(* ------------------------------------------------------------------------- *)

let INLINE_DECOMPOSE_LAYOUT kind =
  (* a1 register, constants (register index, value), temporaries, steps *)
  match kind with
    "12" -> (6, [4,"11275"; 5,"8388608"; 8,"43"; 9,"4294776832";
                 10,"4190208"; 11,"4286586879"], [0;3;7], 24)
  | "13" -> (7, [5,"11275"; 6,"8388608"; 9,"43"; 10,"4294776832";
                 11,"4190208"; 12,"4286586879"], [0;3;4;8], 25)
  | "62" -> (4, [5,"4294443520"; 6,"4190208"; 8,"4286586879"], [0;3;7], 20)
  | "63" -> (5, [6,"4294443520"; 7,"4190208"; 9,"4286586879"], [0;3;4;8], 21)
  | _ -> failwith "INLINE_DECOMPOSE_LAYOUT";;

let INLINE_DECOMPOSE_LOOP_TERM kind mc loop exit k0 (rs:string list) =
  let r k = List.nth rs k in
  let (a1r,consts,temps,_) = INLINE_DECOMPOSE_LAYOUT kind in
  let w = if kind = "12" || kind = "13" then "88" else "32" in
  let pa = if k0 = 0 then "a" else Printf.sprintf "(word_add a (word %d))" k0 in
  let creg = String.concat " /\\ "
    (map (fun (k,v) -> Printf.sprintf "read %s s = word %s" (r k) v) consts) in
  parse_term(INLINE_FILL
   "exists f_events.
      forall e a a1 (x:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        PAIRWISE nonoverlapping
         [(a1,1024); (@pa@,1024); (word pc,libmldsa_size)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) @mc@ /\\
                  read PC s = word (pc + @loop@) /\\
                  read @a@ s = a /\\ read @a1r@ s = a1 /\\
                  read @i@ s = word 0 /\\ @creg@ /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add @pa@ (word(4 * i))))
                             s = x i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + @exit@) /\\
                  read @i@ s = word 1024 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a1 (word(4 * i))))
                             s = mld_poly_decompose_hi_@w@ x i) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add @pa@ (word(4 * i))))
                             s = mld_poly_decompose_lo_@w@ x i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a a1 pc /\\
                     memaccess_inbounds e2
                      [@pa@,1024; a1,1024] [a1,1024; @pa@,1024]))
             (MAYCHANGE [PC; @tmps@; @i@] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a1,1024);
                         memory :> bytes(@pa@,1024)])"
   ["pa",pa; "mc",mc; "loop",loop; "exit",exit; "a",r 1; "a1r",r a1r;
    "i",r 2; "creg",creg; "w",w;
    "tmps",String.concat "; " (map r temps)]);;

let INLINE_DECOMPOSE_LOOP kind mc exec loop exit k0 (rs:string list) =
  let r k = List.nth rs k in
  let (a1r,consts,temps,nsteps) = INLINE_DECOMPOSE_LAYOUT kind in
  let w = if kind = "12" || kind = "13" then "88" else "32" in
  let pa = if k0 = 0 then "a" else Printf.sprintf "(word_add a (word %d))" k0 in
  let tm = INLINE_DECOMPOSE_LOOP_TERM kind mc loop exit k0 rs in
  let creg = String.concat " /\\ "
    (map (fun (k,v) -> Printf.sprintf "read %s s = word %s" (r k) v) consts) in
  let inv = parse_term(INLINE_FILL
   "\\i s. read @a@ s = a /\\ read @a1r@ s = a1 /\\
          read @ir@ s = word(4 * i) /\\ @creg@ /\\
          (!j. i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add @pa@ (word(4 * j)))) s =
                   (x:num->int32) j) /\\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a1 (word(4 * j)))) s =
                   mld_decompose_hi_@w@ (x j)) /\\
          (!j. j < i
               ==> read(memory :> bytes32(word_add @pa@ (word(4 * j)))) s =
                   mld_decompose_lo_@w@ (x j))"
   ["a",r 1; "a1r",r a1r; "ir",r 2; "creg",creg; "pa",pa; "w",w]) in
  let hi_defs,lo_defs =
    if w = "88" then [mld_decompose_hi_88; mld_ct_sel],
                     [DECOMPOSE_LO_88_ALT; mld_ct_sel]
    else [DECOMPOSE_HI_32_ALT], [DECOMPOSE_LO_32_ALT; mld_ct_sel] in
  let hi_f = if w = "88" then `mld_decompose_hi_88` else `mld_decompose_hi_32`
  and lo_f = if w = "88" then `mld_decompose_lo_88` else `mld_decompose_lo_32`
  and polyd = if w = "88" then [mld_poly_decompose_hi_88; mld_poly_decompose_lo_88]
              else [mld_poly_decompose_hi_32; mld_poly_decompose_lo_32] in
  let paddr = if k0 = 0 then `word_add (a:int64) (word(4 * i))`
              else parse_term(Printf.sprintf "word_add (a:int64) (word(4 * i + %d))" k0) in
  (*** The addresses of the polynomial as the simulator writes them ***)
  let normk =
    if k0 = 0 then ALL_TAC else
    let lem = prove(parse_term(Printf.sprintf
      "!a i. word_add (word_add a (word %d)) (word (4 * i)):int64 =
             word_add a (word (4 * i + %d))" k0 k0), CONV_TAC WORD_RULE) in
    RULE_ASSUM_TAC(REWRITE_RULE[lem]) THEN REWRITE_TAC[lem] in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (a1:int64) (pc:num).
      APPEND (f_ev_epil a a1 pc)
       (APPEND (ENUMERATEL 256 (\i. f_ev_loop a a1 pc i)) (f_ev_prol a a1 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `a1:int64`;
                       `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC(NONOVERLAPPING_CLAUSES::PAIRWISE::ALL::SOME_FLAGS::fst exec::polyd) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN normk THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in hi_f (concl th)) && not(free_in lo_f (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ARM_STEPS_TAC exec (1--nsteps) THEN
    SCALAR_LANE_TAC `word_add (a1:int64) (word(4 * i))` `(x:num->int32) i`
      hi_f hi_defs THEN
    SCALAR_LANE_TAC paddr `(x:num->int32) i` lo_f lo_defs THEN
    FULL_FINAL_TAC [ONE_OUTPUT_SPLIT];

    INLINE_EXIT_TAC]);;


(*** The instances of the decompose shapes "12" and "13" (gamma2 = (q-1)/88, ***)
(*** ML-DSA-44; all four prove, in 9 seconds each): function, head, exit,   ***)
(*** shape, the offset k0 of the polynomial, registers R0 .. R12. The shapes ***)
(*** "62" and "63" (gamma2 = (q-1)/32) do not finish: the bit-blasting of    ***)
(*** the lanes takes more than ten minutes.                                  ***)

let INLINE_DECOMPOSE_88_INSTANCES = [
  ("mldsa44_signature_internal","mldsa44_signature_internal_loop22","mldsa44_signature_internal_loop22_exit","12",0,["X9";"X19";"X8";"X10";"X15";"X16";"X23";"X11";"X17";"X13";"X18";"X14"]);
  ("mldsa44_signature_internal","mldsa44_signature_internal_loop23","mldsa44_signature_internal_loop23_exit","13",1024,["X9";"X19";"X8";"X10";"X11";"X15";"X16";"X23";"X12";"X17";"X13";"X18";"X14"]);
  ("mldsa44_signature_internal","mldsa44_signature_internal_loop24","mldsa44_signature_internal_loop24_exit","13",2048,["X9";"X19";"X8";"X10";"X11";"X15";"X16";"X23";"X12";"X17";"X13";"X18";"X14"]);
  ("mldsa44_signature_internal","mldsa44_signature_internal_loop25","mldsa44_signature_internal_loop25_exit","13",3072,["X9";"X19";"X8";"X10";"X11";"X15";"X16";"X23";"X12";"X17";"X13";"X18";"X14"]);

];;

let INLINE_DECOMPOSE_OF_INSTANCE (fn,hl,el,kind,k0,rs) =
  INLINE_DECOMPOSE_LOOP kind "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
    (INLINE_LOOP_EXEC hl el) hl el k0 rs;;
