(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Loops that clang 23 -O3 inlines into                                      *)
(* mldsa{44,65,87}_polyvec_matrix_pointwise_montgomery_row_lazy of           *)
(* mldsa-native's monolithic reduced-RAM build, as lemmas from the head of a *)
(* loop to its exit (see inline_sign.ml for the form of the lemmas): the     *)
(* pointwise Montgomery product of two polynomials, the sum of two           *)
(* polynomials with SSE, and the reduction of a polynomial with SSE. Unlike  *)
(* those of inline_sign.ml, they address their polynomials through pointer   *)
(* registers, which the lemmas take as variables.                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_cp.ml";;

(* A numeral expression linear in one variable as s * i + c (or c, or s * i) *)
let LIN2_ADDR_CONV s tm =
  let (+/) = (+) and ( */ ) = ( * ) in
  let rec ev t =
    match t with
      Comb(Comb(Const("+",_),a),b) -> let (c1,s1) = ev a and (c2,s2) = ev b in (c1 +/ c2, s1 +/ s2)
    | Comb(Comb(Const("*",_),a),b) ->
        let (c1,s1) = ev a and (c2,s2) = ev b in
        if s1 = 0 then (c1 */ c2, c1 */ s2)
        else if s2 = 0 then (c1 */ c2, s1 */ c2)
        else failwith "LIN2_ADDR_CONV: not linear"
    | Var(_,_) -> (0,1)
    | _ -> (dest_small_numeral t, 0) in
  let (c,s') = ev tm in
  if s' <> s then failwith "LIN2_ADDR_CONV: other stride" else
  let iv = hd (frees tm) in
  let si = mk_comb(mk_comb(`(*):num->num->num`, mk_small_numeral s), iv) in
  let r = if c = 0 then si
          else mk_comb(mk_comb(`(+):num->num->num`, si), mk_small_numeral c) in
  if r = tm then failwith "LIN2_ADDR_CONV: unchanged" else
  ARITH_RULE (mk_eq(tm, r));;

let RL_NORM_WORD_CONV s tm =
  match tm with
    Comb(Const("word",_),n)
      when type_of tm = `:int64` && not(is_numeral n) && is_comb n ->
        (try AP_TERM `word:num->int64` (LIN2_ADDR_CONV s n)
         with Failure _ -> REFL tm)
  | _ -> failwith "RL_NORM_WORD_CONV";;

let RL_ADDR_LINEAR_TAC s =
  let pat = `read (memory :> c) (st:x86state) = v` in
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] pat) (concl th)
    then (try CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV (RL_NORM_WORD_CONV s))) th
          with Failure _ -> th)
    else th);;

let RL_GOAL_LINEAR_TAC s =
  CONV_TAC(ONCE_DEPTH_CONV (RL_NORM_WORD_CONV s));;

(* the end of the body of an iteration: as CP_FULL_FINAL_TAC of inline_cp.ml *)
let RL_FULL_FINAL_TAC s n ars (extra:tactic) (spec_tac:tactic) =
  RL_ADDR_LINEAR_TAC s THEN ADDR_NORMALIZE_TAC THEN RL_ADDR_LINEAR_TAC s THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC ars THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(extra THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT_N n] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      RL_GOAL_LINEAR_TAC s THEN
      ASM_REWRITE_TAC[] THEN spec_tac THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* the address of the simulation of [r + rax * 4 + d] with RAX = word it *)
let RL_SIM_FORM it d =
  if d < 0 then
    Printf.sprintf "4 * (%s) + %s" it
      (Num.string_of_num (Num.add_num (Num.power_num (Num.num_of_int 2) (Num.num_of_int 64)) (Num.num_of_int d)))
  else if d = 0 then Printf.sprintf "4 * (%s)" it
  else Printf.sprintf "4 * (%s) + %d" it d;;

(* ------------------------------------------------------------------------- *)
(* mld_poly_pointwise_montgomery of x at xp by y at yp + dy, in place in x:   *)
(* 128 iterations of two coefficients, with the index RAX = rax0 + 2 i       *)
(* addressed as [xr + rax * 4 + (rax0 - 1) * 4 .. ], xr the register that    *)
(* holds xp, and R15 = yp, with the constant q^-1 * 2^32 in R13 and the      *)
(* Montgomery reduction by IMUL, SAR, IMUL by -q, ADD, SHR (as PWMLOOP of    *)
(* inline_sign.ml). The first coefficient is at displacement -4 if rax0 is 1 *)
(* and 0 if it is 0.                                                         *)
(* ------------------------------------------------------------------------- *)

let RL_YPTR dy = if dy = 0 then "yp" else Printf.sprintf "(word_add yp (word %d))" dy;;
let RL_YOFF dy v = if dy = 0 then Printf.sprintf "4*%s" v else Printf.sprintf "%d + 4*%s" dy v;;

let PWMPTR_STMT fn loop exit xr dy rax0 =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e xp yp pc (x:num->int32) (y:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (xp,1024))
        [(%s,1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read %s s = xp /\\ read R15 s = yp /\\
              read RAX s = word %d /\\ read R13 s = word 0x0380200100000000 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add xp (word (4*i)))) s = x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add yp (word (%s)))) s = y i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read %s s = xp /\\ read R15 s = yp /\\
              read RAX s = word %d /\\ read R13 s = word 0x0380200100000000 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add xp (word (4*i)))) s = mld_poly_pointwise_montgomery x y i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add yp (word (%s)))) s = y i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events xp yp pc /\\
                 memaccess_inbounds e2 [xp,1024; %s,1024]
                                       [xp,1024]))
         (MAYCHANGE [RIP; RAX; RCX; RDX] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(xp,1024)])"
  (RL_YPTR dy) image_mc fn loop xr rax0 (RL_YOFF dy "i") fn exit xr (rax0 + 256) (RL_YOFF dy "i") (RL_YPTR dy));;

let PWMPTR_TAC exec fn loop exit xr dy rax0 =
  let it = if rax0 = 0 then "2 * i" else "1 + 2 * i" in
  let d1 = if rax0 = 0 then 0 else -4 in
  let forms =
    [(RL_SIM_FORM it d1, "8 * i");
     (RL_SIM_FORM it (d1 + 4), "8 * i + 4")] in
  let yforms =
    [(RL_SIM_FORM it (d1 + dy), (if dy = 0 then "8 * i" else Printf.sprintf "8 * i + %d" dy));
     (RL_SIM_FORM it (d1 + dy + 4), (Printf.sprintf "8 * i + %d" (dy + 4)))] in
  let alias_tac =
    MAP_EVERY (fun (sim,can) ->
      SUBGOAL_THEN (parse_term(Printf.sprintf
        "word_add (xp:int64) (word (%s)) = word_add xp (word (%s))" sim can))
        ASSUME_TAC THENL [CP_ALIAS64_TAC; ALL_TAC]) forms THEN
    MAP_EVERY (fun (sim,can) ->
      SUBGOAL_THEN (parse_term(Printf.sprintf
        "word_add (yp:int64) (word (%s)) = word_add yp (word (%s))" sim can))
        ASSUME_TAC THENL [CP_ALIAS64_TAC; ALL_TAC]) yforms in
  CONCRETIZE_F_EVENTS_TAC
   `\(xp:int64) (yp:int64) (pc:num).
      APPEND (f_ev_epil xp yp pc)
       (APPEND (ENUMERATEL 128 (\i. f_ev_loop xp yp pc i)) (f_ev_prol xp yp pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `xp:int64`; `yp:int64`; `pc:num`; `x:num->int32`; `y:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_pointwise_montgomery] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `128` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read %s s = xp /\\ read R15 s = yp /\\ read R13 s = word 0x0380200100000000 /\\
          read RAX s = word (%s) /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add yp (word(%s)))) s = y j) /\\
          (!j. 2 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add xp (word(4 * j)))) s = x j) /\\
          (!j. j < 2 * i
               ==> read(memory :> bytes32(word_add xp (word(4 * j)))) s =
                   mld_montgomery_reduce (word_mul (word_sx (x j)) (word_sx (y j))))" xr it (RL_YOFF dy "j"))) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    alias_tac THEN
    FULL_INIT_TAC THEN
    VAL_INT64_TAC (parse_term(if rax0 = 0 then "2 * i" else "1 + 2 * i")) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATCH_MP (CHUNK_INPUT_SPLIT_N 2) (ASSUME `i < 128`)] o
      check (fun th -> free_in `x:num->int32` (concl th) && not(free_in `mld_montgomery_reduce` (concl th)) && is_forall(concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN RL_ADDR_LINEAR_TAC 8 THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf "!k. k < 2 ==> read(memory :> bytes32(word_add yp (word(%s)))) s0 = (y:num->int32)(2 * i + k)" (RL_YOFF dy "(2 * i + k)"))) MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN RL_ADDR_LINEAR_TAC 8 THEN
    X86_STEPS_TAC exec (1--10) THEN RULE_ASSUM_TAC(REWRITE_RULE[PWM_MONTRED_CLANG2]) THEN
    X86_STEPS_TAC exec (11--20) THEN RULE_ASSUM_TAC(REWRITE_RULE[PWM_MONTRED_CLANG2]) THEN
    X86_STEPS_TAC exec (21--23) THEN
    RL_FULL_FINAL_TAC 8 2
      [ARITH_RULE `2 * (i + 1) = 2 * i + 2`; ARITH_RULE `1 + 2 * (i + 1) = 1 + 2 * i + 2`;
       ARITH_RULE `0 + 2 * (i + 1) = 0 + 2 * i + 2`] ALL_TAC ALL_TAC;
    FULL_EXIT0_TAC];;

let PROVE_PWMPTR fn loop exit xr dy rax0 =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(PWMPTR_STMT fn loop exit xr dy rax0, PWMPTR_TAC exec fn loop exit xr dy rax0);;

(* ------------------------------------------------------------------------- *)
(* A wide read of a region as the join of the narrower facts, with the        *)
(* addresses of the form word_add p (word (s * i + c)).                      *)
(* ------------------------------------------------------------------------- *)

let RL_MERGE_TAC n s tm =
  MP_TAC(CONV_RULE(RAND_CONV(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                             DEPTH_CONV(fun t ->
                               if type_of t = `:num` && not(is_numeral t) && is_comb t
                               then LIN2_ADDR_CONV s t else failwith "")))
         (READ_MEMORY_MERGE_CONV n tm)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(* ------------------------------------------------------------------------- *)
(* mld_poly_add as clang -O3 has vectorised it (SSE2, unaligned): x += y,    *)
(* 16 iterations of 64 bytes, RAX = 16 i, with the loads of y at [yr + rax * *)
(* 4 + 16 g], those of x at [xr + rax * 4 + 16 g], PADDD, and the stores to  *)
(* [xr + rax * 4 + 16 g]. xr holds xp and yr holds yp.                       *)
(* ------------------------------------------------------------------------- *)

let SSEADD_STMT fn loop exit xr yr =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e xp yp pc (x:num->int32) (y:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    nonoverlapping (xp,1024) (yp,1024) /\\
    nonoverlapping (xp,1024) (word pc,libmldsa_size)
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read %s s = xp /\\ read %s s = yp /\\ read RAX s = word 0 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add xp (word (4*i)))) s = x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add yp (word (4*i)))) s = y i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read %s s = xp /\\ read %s s = yp /\\ read RAX s = word 256 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add xp (word (4*i)))) s = mld_poly_add x y i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add yp (word (4*i)))) s = y i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events xp yp pc /\\
                 memaccess_inbounds e2 [xp,1024; yp,1024] [xp,1024]))
         (MAYCHANGE [RIP; RAX] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(xp,1024)])"
  image_mc fn loop xr yr fn exit xr yr);;

let SSEADD_TAC exec fn loop exit xr yr =
  let chunks = [0;1;2;3] in
  let simf c = if c = 0 then "4 * (16 * i)" else Printf.sprintf "4 * (16 * i) + %d" (16 * c) in
  let canf c = if c = 0 then "64 * i" else Printf.sprintf "64 * i + %d" (16 * c) in
  let alias_tac =
    MAP_EVERY (fun c ->
      SUBGOAL_THEN (parse_term(Printf.sprintf
        "word_add (xp:int64) (word (%s)) = word_add xp (word (%s))" (simf c) (canf c)))
        ASSUME_TAC THENL [CP_ALIAS64_TAC; ALL_TAC] THEN
      SUBGOAL_THEN (parse_term(Printf.sprintf
        "word_add (yp:int64) (word (%s)) = word_add yp (word (%s))" (simf c) (canf c)))
        ASSUME_TAC THENL [CP_ALIAS64_TAC; ALL_TAC]) chunks in
  CONCRETIZE_F_EVENTS_TAC
   `\(xp:int64) (yp:int64) (pc:num).
      APPEND (f_ev_epil xp yp pc)
       (APPEND (ENUMERATEL 16 (\i. f_ev_loop xp yp pc i)) (f_ev_prol xp yp pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `xp:int64`; `yp:int64`; `pc:num`; `x:num->int32`; `y:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_add] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `16` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read %s s = xp /\\ read %s s = yp /\\ read RAX s = word (16 * i) /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add yp (word(4 * j)))) s = y j) /\\
          (!j. 16 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add xp (word(4 * j)))) s = x j) /\\
          (!j. j < 16 * i
               ==> read(memory :> bytes32(word_add xp (word(4 * j)))) s =
                   word_add (x j) (y j))" xr yr)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    alias_tac THEN
    MAP_EVERY (fun n ->
      GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" n,`:int256`))
        (parse_term(Printf.sprintf "read YMM%d" n))) [0;1;2;3] THEN
    FULL_INIT_TAC THEN
    VAL_INT64_TAC `16 * i` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATCH_MP (CHUNK_INPUT_SPLIT_N 16) (ASSUME `i < 16`)] o
      check (fun th -> free_in `x:num->int32` (concl th) && not(free_in `word_add` (concl th) && free_in `y:num->int32` (concl th)) && is_forall(concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN RL_ADDR_LINEAR_TAC 64 THEN
    SUBGOAL_THEN `!k. k < 16 ==> read(memory :> bytes32(word_add yp (word(4 * (16 * i + k))))) s0 = (y:num->int32)(16 * i + k)` MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN RL_ADDR_LINEAR_TAC 64 THEN
    MAP_EVERY (fun c ->
      RL_MERGE_TAC 2 64 (parse_term(Printf.sprintf "read(memory :> bytes128(word_add xp (word (%s)))) s0" (canf c))) THEN
      RL_MERGE_TAC 2 64 (parse_term(Printf.sprintf "read(memory :> bytes128(word_add yp (word (%s)))) s0" (canf c)))) chunks THEN
    VERIF_SSE_STEPS_TAC exec (1--16) THEN X86_STEPS_TAC exec (17--19) THEN
    MAP_EVERY (fun c ->
      let lhs_tm = parse_term(Printf.sprintf "read (memory :> bytes128 (word_add (xp:int64) (word (%s)))) (s19:x86state)" (canf c)) in
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
        check (fun th -> is_eq(concl th) && aconv (lhs(concl th)) lhs_tm))) chunks THEN
    RL_FULL_FINAL_TAC 64 16
      [ARITH_RULE `16 * (i + 1) = 16 * i + 16`] ALL_TAC (REWRITE_TAC[WORD_ADD_SYM]);
    FULL_EXIT0_TAC];;

let PROVE_SSEADD fn loop exit xr yr =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(SSEADD_STMT fn loop exit xr yr, SSEADD_TAC exec fn loop exit xr yr);;

(* ------------------------------------------------------------------------- *)
(* mld_poly_reduce on the polynomial at xp as clang -O3 has vectorised it    *)
(* (SSE2, unaligned): 32 iterations of 8 coefficients, with RAX = 8 i,        *)
(* addressed as [xr + rax * 4 + 16 g], 2^22 in XMM0 and -q in XMM1 (as        *)
(* REDLOOP of inline_sign.ml, with the constants in other registers).        *)
(* ------------------------------------------------------------------------- *)

let REDPTR_STMT fn loop exit xr =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e xp pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    nonoverlapping (xp,1024) (word pc,libmldsa_size)
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read %s s = xp /\\ read RAX s = word 0 /\\
              read XMM0 s = word 0x00400000004000000040000000400000 /\\
              read XMM1 s = word 0xff801fffff801fffff801fffff801fff /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add xp (word (4*i)))) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read %s s = xp /\\ read RAX s = word 256 /\\
              read XMM0 s = word 0x00400000004000000040000000400000 /\\
              read XMM1 s = word 0xff801fffff801fffff801fffff801fff /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add xp (word (4*i)))) s = mld_poly_reduce x i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events xp pc /\\
                 memaccess_inbounds e2 [xp,1024] [xp,1024]))
         (MAYCHANGE [RIP; RAX] ,, MAYCHANGE [ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(xp,1024)])"
  image_mc fn loop xr fn exit xr);;

let REDPTR_TAC exec fn loop exit xr =
  let chunks = [0;1] in
  let simf c = if c = 0 then "4 * (8 * i)" else Printf.sprintf "4 * (8 * i) + %d" (16 * c) in
  let canf c = if c = 0 then "32 * i" else Printf.sprintf "32 * i + %d" (16 * c) in
  let alias_tac =
    MAP_EVERY (fun c ->
      SUBGOAL_THEN (parse_term(Printf.sprintf
        "word_add (xp:int64) (word (%s)) = word_add xp (word (%s))" (simf c) (canf c)))
        ASSUME_TAC THENL [CP_ALIAS64_TAC; ALL_TAC]) chunks in
  CONCRETIZE_F_EVENTS_TAC
   `\(xp:int64) (pc:num).
      APPEND (f_ev_epil xp pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop xp pc i)) (f_ev_prol xp pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `xp:int64`; `pc:num`; `x:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_reduce] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read %s s = xp /\\ read RAX s = word (8 * i) /\\
          read XMM0 s = word 0x00400000004000000040000000400000 /\\
          read XMM1 s = word 0xff801fffff801fffff801fffff801fff /\\
          (!j. 8 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add xp (word(4 * j)))) s = x j) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes32(word_add xp (word(4 * j)))) s = mld_reduce32 (x j))" xr)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    alias_tac THEN
    MAP_EVERY (fun n ->
      GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" n,`:int256`))
        (parse_term(Printf.sprintf "read YMM%d" n))) [2;3;4;5;6] THEN
    FULL_INIT_TAC THEN
    XMM_EXISTSTOP_TAC "top0" `YMM0` THEN XMM_EXISTSTOP_TAC "top1" `YMM1` THEN
    VAL_INT64_TAC `8 * i` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATCH_MP (CHUNK_INPUT_SPLIT_N 8) (ASSUME `i < 32`)] o
      check (fun th -> free_in `x:num->int32` (concl th) && not(free_in `mld_reduce32` (concl th)) && is_forall(concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN RL_ADDR_LINEAR_TAC 32 THEN
    MAP_EVERY (fun c ->
      RL_MERGE_TAC 2 32 (parse_term(Printf.sprintf "read(memory :> bytes128(word_add xp (word (%s)))) s0" (canf c)))) chunks THEN
    VERIF_SSE_STEPS_TAC exec (1--24) THEN X86_STEPS_TAC exec (25--27) THEN
    MAP_EVERY (fun c ->
      let lhs_tm = parse_term(Printf.sprintf "read (memory :> bytes128 (word_add (xp:int64) (word (%s)))) (s27:x86state)" (canf c)) in
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
        check (fun th -> is_eq(concl th) && aconv (lhs(concl th)) lhs_tm))) chunks THEN
    RL_FULL_FINAL_TAC 32 8
      [ARITH_RULE `8 * (i + 1) = 8 * i + 8`]
      (REWRITE_TAC[XMM0; XMM1; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST)
      (REWRITE_TAC[mld_reduce32] THEN REPEAT CONJ_TAC THEN APP_BLAST_TAC `x:num->int32`);
    FULL_EXIT0_TAC];;

let PROVE_REDPTR fn loop exit xr =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(REDPTR_STMT fn loop exit xr, REDPTR_TAC exec fn loop exit xr);;

(* ------------------------------------------------------------------------- *)
(* The test of the code for the overlap of two polynomials (t at xp and the  *)
(* entry at yp, 1024 bytes each) before the vector loop: two comparisons of  *)
(* addresses, as for the data and the state in inline_sponge_tail_glue.ml    *)
(* (whose proofs these are, for 1024 bytes). If the regions do not overlap,  *)
(* the two unsigned comparisons are not both true.                           *)
(* ------------------------------------------------------------------------- *)

let RL_MOD1 = prove(`!a. 2 EXP 64 <= a /\ a < 2 * 2 EXP 64 ==> a MOD 2 EXP 64 = a - 2 EXP 64`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a = (a - 2 EXP 64) + 1 * 2 EXP 64` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;
let RL_CONG1 = NUMBER_RULE `!x n. (x + n == x) (mod n)`;;
let RL_CONG2 = NUMBER_RULE `!x y. x = y ==> (x == y) (mod n)`;;
let RL_ALIAS = prove(`!m s r. m < 2 EXP 64 /\ s < 2 EXP 64 /\ r <= 1024 /\ nonoverlapping_modulo (2 EXP 64) (m,r) (s,1024)
         ==> ~(s < (m + r) MOD 2 EXP 64 /\ m < (s + r) MOD 2 EXP 64)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match [] `nonoverlapping_modulo n (a,b) (c,d)`) (concl th))) THEN
  REWRITE_TAC[nonoverlapping_modulo; NOT_EXISTS_THM] THEN DISCH_TAC THEN
  ASM_CASES_TAC `m + r < 2 EXP 64` THEN ASM_CASES_TAC `s + r < 2 EXP 64` THENL
   [(* no wraps *)
    SUBGOAL_THEN `s < m + r /\ m < s + r` STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `s <= m` THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `m - s`]) THEN
      SUBGOAL_THEN `m + 0 = s + (m - s)` (fun th -> REWRITE_TAC[th; CONG_REFL]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPECL [`s - m`; `0`]) THEN
      SUBGOAL_THEN `m + (s - m) = s + 0` (fun th -> REWRITE_TAC[th; CONG_REFL]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC];
    (* s + r wraps *)
    SUBGOAL_THEN `m < (s + r) - 2 EXP 64` ASSUME_TAC THENL
     [SUBGOAL_THEN `(s + r) MOD 2 EXP 64 = (s + r) - 2 EXP 64` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [MATCH_MP_TAC RL_MOD1 THEN ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `m + 2 EXP 64 - s`]) THEN
    SUBGOAL_THEN `(m + 0 == s + (m + 2 EXP 64 - s)) (mod (2 EXP 64))` (fun th -> REWRITE_TAC[th]) THENL
     [SUBGOAL_THEN `s + (m + 2 EXP 64 - s) = m + 2 EXP 64` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ADD_CLAUSES; RL_CONG1; CONG_SYM] THEN ONCE_REWRITE_TAC[CONG_SYM] THEN REWRITE_TAC[RL_CONG1]; ALL_TAC] THEN
    ASM_ARITH_TAC;
    (* m + r wraps *)
    SUBGOAL_THEN `s < (m + r) - 2 EXP 64` ASSUME_TAC THENL
     [SUBGOAL_THEN `(m + r) MOD 2 EXP 64 = (m + r) - 2 EXP 64` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [MATCH_MP_TAC RL_MOD1 THEN ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s + 2 EXP 64 - m`; `0`]) THEN
    SUBGOAL_THEN `(m + (s + 2 EXP 64 - m) == s + 0) (mod (2 EXP 64))` (fun th -> REWRITE_TAC[th]) THENL
     [SUBGOAL_THEN `m + (s + 2 EXP 64 - m) = s + 2 EXP 64` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ADD_CLAUSES; RL_CONG1]; ALL_TAC] THEN
    ASM_ARITH_TAC;
    (* both wrap *)
    SUBGOAL_THEN `s < (m + r) - 2 EXP 64 /\ m < (s + r) - 2 EXP 64` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(m + r) MOD 2 EXP 64 = (m + r) - 2 EXP 64 /\ (s + r) MOD 2 EXP 64 = (s + r) - 2 EXP 64` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC RL_MOD1 THEN ASM_ARITH_TAC; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `s <= m` THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `m - s`]) THEN
      SUBGOAL_THEN `m + 0 = s + (m - s)` (fun th -> REWRITE_TAC[th; CONG_REFL]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPECL [`s - m`; `0`]) THEN
      SUBGOAL_THEN `m + (s - m) = s + 0` (fun th -> REWRITE_TAC[th; CONG_REFL]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC]]);;

let RL_ALIAS_W = prove(`!(mp:int64) (st:int64) r. r <= 1024 /\ nonoverlapping_modulo (2 EXP 64) (val mp,r) (val st,1024)
    ==> ~(val st < val (word_add mp (word r)) /\ val mp < val (word_add st (word r)))`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  ASSUME_TAC(REWRITE_RULE[DIMINDEX_64] (ISPEC `mp:int64` VAL_BOUND)) THEN
  ASSUME_TAC(REWRITE_RULE[DIMINDEX_64] (ISPEC `st:int64` VAL_BOUND)) THEN
  MP_TAC(SPECL [`val (mp:int64)`; `val (st:int64)`; `r:num`] RL_ALIAS) THEN
  ASM_REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `r MOD 2 EXP 64 = r` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[]);;

let RL_SETB = prove(`!(x:56 word) (c:bool). word (val (word_join x (if c then word 1 else word 0:byte):64 word) MOD 256):byte = (if c then word 1 else word 0)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN CONV_TAC WORD_BLAST);;
let RL_COND_AND = prove(`!c1 c2. ~(c1 /\ c2) ==> val((if c1 then word 1 else word 0:byte) && (if c2 then word 1 else word 0)) = 0`,
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC [`c1:bool`; `c2:bool`] THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;
let RL_RES ths =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read RIP s = x`) (concl th) || can (term_match [] `read events s = x`) (concl th)
    then REWRITE_RULE ths th else th);;

(* the test of the code for the overlap of t and the entry at mat, from the  *)
(* comparisons in RAX and RCX: with the regions not overlapping, the branch   *)
(* goes to the vector loop *)
let RL_ALIAS_TAC =
  FIRST_ASSUM(fun nov ->
    if can (term_match [] `nonoverlapping_modulo (2 EXP 64) (val t,1024) (val mat,1024)`) (concl nov)
    then
      let a = MP (SPECL [`t:int64`; `mat:int64`; `1024`] RL_ALIAS_W) (CONJ (ARITH_RULE `1024 <= 1024`) nov) in
      let c1 = `val (t:int64) < val (word_add (mat:int64) (word 1024))`
      and c2 = `val (mat:int64) < val (word_add (t:int64) (word 1024))` in
      let sw = INST [c1,`a:bool`; c2,`b:bool`] (TAUT `~(b /\ a) ==> ~(a /\ b)`) in
      let ca = MP (SPECL [c1; c2] RL_COND_AND) (MP sw a) in
      RL_RES [RL_SETB; ca]
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* mld_polyeta_unpack for eta = 4 as clang -O3 has inlined it into           *)
(* mld_compute_pack_t0_t165: the 128 bytes at bp become the 256 coefficients *)
(* 4 - nibble at rsp0 + ob, 32 iterations of 4 bytes (two 16-bit words, each *)
(* of 4 nibbles, unpacked to 4 lanes of 32 bits with PUNPCKLBW, PAND and     *)
(* PUNPCKLWD against zero, and subtracted from 4), with RBX = bp + 2 and     *)
(* RAX = 4 i, the words read at [rbx + rax - 2] and [rbx + rax] and the      *)
(* vectors written at [rsp + rax * 8 + ob - 32 + 32 g] (g = 1, 2).           *)
(* ------------------------------------------------------------------------- *)

let ETA4LOOP_STMT fn loop exit ob =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e bq rsp0 pc (b:num->byte).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 (word_add rsp0 (word %d)) /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024))
        [(bq,128); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RBX s = word_add bq (word 2) /\\ read RAX s = word 0 /\\
              read XMM4 s = word 0x0f000f000f000f000f000f000f0f0f0f /\\
              read XMM5 s = word 0 /\\
              read XMM6 s = word 0x00000004000000040000000400000004 /\\
              (!j. j < 128 ==> read (memory :> bytes8 (word_add bq (word j))) s = b j) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RBX s = word_add bq (word 2) /\\ read RAX s = word 128 /\\
              read XMM4 s = word 0x0f000f000f000f000f000f000f0f0f0f /\\
              read XMM5 s = word 0 /\\
              read XMM6 s = word 0x00000004000000040000000400000004 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = mld_polyeta_unpack_4 b i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events bq rsp0 pc /\\
                 memaccess_inbounds e2 [bq,128; word_add rsp0 (word %d),1024]
                                       [word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RAX; RCX] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob ob image_mc fn loop fn exit ob ob ob ob);;

let ETA_DM0 =
  CONJUNCTS (REWRITE_RULE[GSYM(ARITH_RULE `8 * i = 2 * (4 * i) + 0`)]
   (MP (SPECL [`2`; `4 * i`; `0`] DIVMOD_CHUNK) (ARITH_RULE `0 < 2`)));;

let ETA_DIVMODS = flat(map (fun k ->
  let q = k / 2 and r = k mod 2 in
  let eq = ARITH_RULE (parse_term(Printf.sprintf "8 * i + %d = 2 * (4 * i + %d) + %d" k q r)) in
  let th = MP (SPECL [`2`; parse_term(Printf.sprintf "4 * i + %d" q); mk_small_numeral r] DIVMOD_CHUNK)
              (ARITH_RULE (parse_term(Printf.sprintf "%d < 2" r))) in
  CONJUNCTS (REWRITE_RULE[GSYM eq] th)) [1;2;3;4;5;6;7]);;

let ETA4LOOP_TAC exec fn loop exit ob =
  let simst c = Printf.sprintf "8 * (4 * i) + %d" (ob + 16 * c)
  and canst c = Printf.sprintf "32 * i + %d" (ob + 16 * c) in
  CONCRETIZE_F_EVENTS_TAC
   `\(bq:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil bq rsp0 pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop bq rsp0 pc i)) (f_ev_prol bq rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `bq:int64`; `rsp0:int64`; `pc:num`; `b:num->byte`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\ read RBX s = word_add bq (word 2) /\\
          read RAX s = word (4 * i) /\\
          read XMM4 s = word 0x0f000f000f000f000f000f000f0f0f0f /\\
          read XMM5 s = word 0 /\\
          read XMM6 s = word 0x00000004000000040000000400000004 /\\
          (!j. j < 128 ==> read (memory :> bytes8 (word_add bq (word j))) s = b j) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = mld_polyeta_unpack_4 b j)" ob)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
    FULL_INIT_TAC THEN
    XMM_EXISTSTOP_TAC "top4" `YMM4` THEN XMM_EXISTSTOP_TAC "top5" `YMM5` THEN XMM_EXISTSTOP_TAC "top6" `YMM6` THEN
    VAL_INT64_TAC `4 * i` THEN
    SUBGOAL_THEN `word_add (word_add (bq:int64) (word 2)) (word (1 * (4 * i) + 18446744073709551614)) = word_add bq (word (4 * i))` ASSUME_TAC THENL [CP_ALIAS64_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `word_add (word_add (bq:int64) (word 2)) (word (1 * (4 * i))) = word_add bq (word (4 * i + 2))` ASSUME_TAC THENL [CP_ALIAS64_TAC; ALL_TAC] THEN
    MAP_EVERY (fun c ->
      SUBGOAL_THEN (parse_term(Printf.sprintf "word_add (rsp0:int64) (word (%s)) = word_add rsp0 (word (%s))" (simst c) (canst c))) ASSUME_TAC THENL [CP_ALIAS64_TAC; ALL_TAC] THEN
      ALIGN16_IDX_TAC `rsp0:int64` (parse_term(canst c)) THEN ALIGN16_IDX_TAC `rsp0:int64` (parse_term(simst c))) [0;1] THEN
    SUBGOAL_THEN `!k. k < 4 ==> read(memory :> bytes8(word_add bq (word(4 * i + k)))) s0 = (b:num->byte)(4 * i + k)` MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN STRIP_TAC THEN RL_ADDR_LINEAR_TAC 4 THEN
    RL_MERGE_TAC 1 4 `read(memory :> bytes16(word_add bq (word (4 * i)))) s0` THEN
    RL_MERGE_TAC 1 4 `read(memory :> bytes16(word_add bq (word (4 * i + 2)))) s0` THEN
    VERIF_SSE_STEPS_TAC exec (1--22) THEN X86_STEPS_TAC exec (23--25) THEN
    MAP_EVERY (fun c ->
      let lhs_tm = parse_term(Printf.sprintf "read (memory :> bytes128 (word_add (rsp0:int64) (word (%s)))) (s25:x86state)" (canst c)) in
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
        check (fun th -> is_eq(concl th) && aconv (lhs(concl th)) lhs_tm))) [0;1] THEN
    RL_FULL_FINAL_TAC 32 8 [ARITH_RULE `4 * (i + 1) = 4 * i + 4`]
     (REWRITE_TAC[XMM4; XMM5; XMM6; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST)
     (REWRITE_TAC[mld_polyeta_unpack_4] THEN REWRITE_TAC (ETA_DM0 @ ETA_DIVMODS) THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; COND_CLAUSES] THEN REPEAT CONJ_TAC THEN APP_BLAST_TAC `b:num->byte`);
    FULL_EXIT0_TAC];;

let PROVE_ETA4LOOP fn loop exit ob =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(ETA4LOOP_STMT fn loop exit ob, ETA4LOOP_TAC exec fn loop exit ob);;
