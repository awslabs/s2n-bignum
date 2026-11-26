(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Loops that clang 23 -O3 inlines into mld_compute_pack_t0_t1{44,65,87} of  *)
(* mldsa-native's monolithic reduced-RAM build, as lemmas from the head of   *)
(* a loop to its exit (see inline_sign.ml for the form of the lemmas and     *)
(* the loops that the functions of verification share): the addition of the  *)
(* polynomial of s2 to that of the inverse NTT (SSE), the splitting at 2^13  *)
(* and the packing of t1. The reduction and the addition of q are the        *)
(* lemmas PROVE_REDLOOP and PROVE_CADDQ of inline_sign.ml.                   *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_verify.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign.ml";;

(* ------------------------------------------------------------------------- *)
(* Address forms. LINEAR_ADDR_CONV_B of inline_sign.ml, applied by          *)
(* ONCE_DEPTH_CONV, descends into the subterms of a numeral expression that  *)
(* it has already put in its normal form, and so breaks it; these versions   *)
(* apply it to the argument of a `word` only, and leave a normal form alone. *)
(* ------------------------------------------------------------------------- *)

let CP_NORM_WORD_CONV bases tm =
  match tm with
    Comb(Const("word",_),n)
      when type_of tm = `:int64` && not(is_numeral n) && is_comb n ->
        (try AP_TERM `word:num->int64` (LINEAR_ADDR_CONV_B bases n)
         with Failure _ -> REFL tm)
  | _ -> failwith "CP_NORM_WORD_CONV";;

let CP_ADDR_LINEAR_TAC bases =
  let pat = `read (memory :> c) (s:x86state) = v` in
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] pat) (concl th)
    then (try CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV (CP_NORM_WORD_CONV bases))) th
          with Failure _ -> th)
    else th);;

let CP_GOAL_LINEAR_TAC bases =
  CONV_TAC(ONCE_DEPTH_CONV (CP_NORM_WORD_CONV bases));;

(* a normalised copy of each fact about a 32-bit value whose address changes *)
let CP_ADDR_COPY_TAC bases =
  let pat32 = `read (memory :> bytes32 a) (s:x86state) = v` in
  W(fun (asl,w) ->
    MAP_EVERY (fun (_,th) ->
      if can (term_match [] pat32) (concl th)
      then (try let th' = CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV (CP_NORM_WORD_CONV bases))) th in
              if concl th' = concl th then ALL_TAC else ASSUME_TAC th'
            with Failure _ -> ALL_TAC)
      else ALL_TAC) asl);;

(* word_add a (word (c + 2^64)) = word_add a (word c') for the displacements
   that the simulator writes as large numerals: proved by arithmetic mod 2^64 *)
let CP_ALIAS64_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN AP_TERM_TAC THEN
  W(fun (asl,w) ->
    let a = rand(lhs w) and b = rand(rhs w) in
    if a = b then REFL_TAC else
    let eq = (try ARITH_RULE(mk_eq(a,mk_binop `(+):num->num->num` b `18446744073709551616`))
              with Failure _ -> ARITH_RULE(mk_eq(a,b))) in
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [eq] THEN
    REWRITE_TAC[WORD_ADD; WORD_REDUCE_CONV `word 18446744073709551616:int64`; WORD_ADD_0]);;

(* the end of the body of an iteration of a loop over a polynomial, as
   CHUNKN_FULL_FINAL_TAC of inline_sign.ml with the address forms above *)
let CP_FULL_FINAL_TAC bases n ars (extra:tactic) (spec_tac:tactic) =
  CP_ADDR_LINEAR_TAC bases THEN ADDR_NORMALIZE_TAC THEN CP_ADDR_LINEAR_TAC bases THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC ars THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(extra THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT_N n] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      CP_GOAL_LINEAR_TAC bases THEN
      ASM_REWRITE_TAC[] THEN spec_tac THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* mld_poly_add as clang -O3 has vectorised it (SSE2): a += b, 16 iterations *)
(* of 64 bytes, with RAX = 12 + 16 i. The four vectors of b are loaded first, *)
(* at [rsp + rax * 4 + kb + 16 g], then added to those of a at               *)
(* [rsp + rax * 4 + ka + 16 g] by PADDD with a memory operand, and stored    *)
(* back to a, with ka = ob - 48, which is negative for ob < 48: ob = 32 is   *)
(* the polynomial of the inverse NTT at rsp0 + 32, and bb = 1056 that of s2. *)
(* The simulator writes the addresses of a as 4 * (12 + 16 i) + ka + 16 g    *)
(* (with a numeral 2^64 + ka for ka < 0, and without the + 0), which cannot  *)
(* be compared with the other addresses, so that each is replaced by         *)
(* 64 i + ob + 16 g through an equation among the assumptions.              *)
(* ------------------------------------------------------------------------- *)

let ADDLOOP_STMT fn loop exit ob bb =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e rsp0 pc (x:num->int32) (y:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 (word_add rsp0 (word %d)) /\\ aligned 16 (word_add rsp0 (word %d)) /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024))
        [(word_add rsp0 (word %d),1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word 12 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = y i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word 268 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = mld_poly_add x y i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = y i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),1024; word_add rsp0 (word %d),1024]
                                       [word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RAX] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob bb ob bb image_mc fn loop ob bb fn exit ob bb ob bb ob ob);;

let ADDLOOP_TAC exec fn loop exit ob bb =
  let ka = ob - 48 in
  let simform g =
    let d = ka + 16 * g in
    if d < 0 then Printf.sprintf "4 * (12 + 16 * i) + %s" (Num.string_of_num (Num.add_num (Num.power_num (Num.num_of_int 2) (Num.num_of_int 64)) (Num.num_of_int d)))
    else if d = 0 then "4 * (12 + 16 * i)"
    else Printf.sprintf "4 * (12 + 16 * i) + %d" d
  and canform g = Printf.sprintf "64 * i + %d" (ob + 16 * g) in
  let forms = map (fun g -> (simform g, canform g)) [0;1;2;3] in
  let alias_tac =
    MAP_EVERY (fun (sim,can) ->
      SUBGOAL_THEN (parse_term(Printf.sprintf
        "word_add (rsp0:int64) (word (%s)) = word_add rsp0 (word (%s))" sim can))
        ASSUME_TAC THENL [CP_ALIAS64_TAC; ALL_TAC]) forms in
  let align_tac =
    MAP_EVERY (fun k -> ALIGN16_IDX_TAC `rsp0:int64`
                 (parse_term(Printf.sprintf "4 * (12 + 16 * i) + %d" (bb - 48 + 16 * k)))) [0;1;2;3] THEN
    MAP_EVERY (fun (s,c) ->
      ALIGN16_IDX_TAC `rsp0:int64` (parse_term c) THEN
      (if s = fst (hd forms) then ALL_TAC else ALIGN16_IDX_TAC `rsp0:int64` (parse_term s))) forms in
  let split_ass pat =
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATCH_MP (CHUNK_INPUT_SPLIT_N 16) (ASSUME `i < 16`)] o
      check (fun th -> free_in `x:num->int32` (concl th) && not(free_in `y:num->int32` (concl th)) && is_forall(concl th))) in
  let fin_tac =
    MAP_EVERY (fun (_,c) ->
      let lhs_tm = parse_term(Printf.sprintf "read (memory :> bytes128 (word_add (rsp0:int64) (word (%s)))) (s15:x86state)" c) in
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
        check (fun th -> is_eq(concl th) && aconv (lhs(concl th)) lhs_tm))) forms in
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num).
      APPEND (f_ev_epil rsp0 pc)
       (APPEND (ENUMERATEL 16 (\i. f_ev_loop rsp0 pc i)) (f_ev_prol rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `x:num->int32`; `y:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_add] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `16` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read RAX s = word (12 + 16 * i) /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = y j) /\\
          (!j. 16 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = x j) /\\
          (!j. j < 16 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s =
                   word_add (y j) (x j))" bb ob ob)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    alias_tac THEN
    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
    FULL_INIT_TAC THEN
    VAL_INT64_TAC `12 + 16 * i` THEN
    align_tac THEN
    split_ass () THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN CP_ADDR_LINEAR_TAC [bb; ob] THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf "!k. k < 16 ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * (16 * i + k))))) s0 = (y:num->int32)(16 * i + k)" bb)) MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN CP_ADDR_LINEAR_TAC [bb; ob] THEN
    MAP_EVERY (fun g ->
      MERGE_LIN_TAC_B 2 [bb; ob]
        (parse_term(Printf.sprintf "read(memory :> bytes128(word_add rsp0 (word (4 * (12 + 16 * i) + %d)))) s0" (bb - 48 + 16 * g)))) [0;1;2;3] THEN
    MAP_EVERY (fun (_,c) ->
      MERGE_LIN_TAC_B 2 [bb; ob]
        (parse_term(Printf.sprintf "read(memory :> bytes128(word_add rsp0 (word (%s)))) s0" c))) forms THEN
    VERIF_SSE_STEPS_TAC exec (1--8) THEN CP_ADDR_COPY_TAC [bb; ob] THEN
    VERIF_SSE_STEPS_TAC exec (9--12) THEN X86_STEPS_TAC exec (13--15) THEN
    fin_tac THEN
    CP_FULL_FINAL_TAC [bb; ob] 16
      [ARITH_RULE `16 * (i + 1) = 16 * i + 16`; ARITH_RULE `12 + 16 * (i + 1) = 12 + 16 * i + 16`] ALL_TAC ALL_TAC;
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBST1_TAC(MP (SPEC `i:num` (ASSUME (parse_term(Printf.sprintf
        "forall j. j < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4 * j)))) s0 = word_add ((y:num->int32) j) ((x:num->int32) j)" ob))))
        (ASSUME `i < 256`)) THEN
      REWRITE_TAC[WORD_ADD_SYM];
      DISCHARGE_SAFETY_PROPERTY_TAC]];;

let PROVE_ADDLOOP fn loop exit ob bb =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(ADDLOOP_STMT fn loop exit ob bb, ADDLOOP_TAC exec fn loop exit ob bb);;

(* ------------------------------------------------------------------------- *)
(* mld_poly_power2round (a1 = (a + 2^12 - 1) >> 13 and a0 = a - a1 * 2^13) of *)
(* the polynomial at rsp0 + ob, in place, with a1 at rsp0 + hb, as clang -O3 *)
(* has vectorised it (SSE2): 32 iterations of 8 coefficients, two 128-bit    *)
(* words, RAX = 4 + 8 i addressed as [rsp + rax * 4 + k] (k = ob - 16 for a0 *)
(* and k = hb - 16 for a1), with 2^12 - 1 in XMM6 and ~(2^13 - 1) in XMM7.   *)
(* ------------------------------------------------------------------------- *)

(* the statements of the lemmas for the splitting at 2^13 and the packing of t1 *)
let P2RLOOP_STMT fn loop exit ob hb =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e rsp0 pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 (word_add rsp0 (word %d)) /\\ aligned 16 (word_add rsp0 (word %d)) /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024))
        [(word_add rsp0 (word %d),1024); (word pc,libmldsa_size)] /\\
    nonoverlapping (word_add rsp0 (word %d),1024) (word pc,libmldsa_size)
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word 4 /\\
              read XMM6 s = word 0x00000fff00000fff00000fff00000fff /\\
              read XMM7 s = word 0xffffe000ffffe000ffffe000ffffe000 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word 260 /\\
              read XMM6 s = word 0x00000fff00000fff00000fff00000fff /\\
              read XMM7 s = word 0xffffe000ffffe000ffffe000ffffe000 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = mld_poly_power2round_lo x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = mld_poly_power2round_hi x i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),1024]
                                       [word_add rsp0 (word %d),1024; word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RAX] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024); memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob hb ob hb hb image_mc fn loop ob fn exit ob hb ob ob hb ob hb);;

(* mld_polyt1_pack of the polynomial at rsp0 + ib into 320 bytes at op:
   64 iterations of 4 coefficients, RAX = 12 + 16 i, RCX = op + 4 + 5 i *)
let T1PACK_STMT fn loop exit ib =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e rsp0 op pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024))
        [(op,320); (word pc,libmldsa_size)] /\\
    nonoverlapping (op,320) (word pc,libmldsa_size)
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word 12 /\\ read RCX s = word_add op (word 4) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word 1036 /\\ read RCX s = word_add op (word 324) /\\
              (!j. j < 320 ==> read (memory :> bytes8 (word_add op (word j))) s = mld_polyt1_pack x j) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 op pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),1024; op,320] [op,320]))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(op,320)])"
  ib image_mc fn loop ib fn exit ib);;

let POWER2ROUND_LANES = prove
 (`!x:int32.
     word_ishr (word_add x (word 4095)) 13 = mld_power2round_hi x /\
     word_sub x (word_and (word_add x (word 4095)) (word 4294959104)) =
     mld_power2round_lo x`,
  REWRITE_TAC[mld_power2round_lo; mld_power2round_hi] THEN GEN_TAC THEN
  AP_TERM_TAC THEN SPEC_TAC(`word_add (x:int32) (word 4095)`,`y:int32`) THEN
  BITBLAST_TAC);;

let P2RLOOP_TAC exec fn loop exit ob hb =
  let k = ob - 16 and kh = hb - 16 in
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num).
      APPEND (f_ev_epil rsp0 pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop rsp0 pc i)) (f_ev_prol rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `x:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_power2round_lo; mld_poly_power2round_hi] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read RAX s = word (4 + 8 * i) /\\
          read XMM6 s = word 0x00000fff00000fff00000fff00000fff /\\
          read XMM7 s = word 0xffffe000ffffe000ffffe000ffffe000 /\\
          (!j. 8 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = x j) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = mld_power2round_lo (x j)) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = mld_power2round_hi (x j))"
     ob ob hb)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY (fun n ->
      GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" n,`:int256`))
        (parse_term(Printf.sprintf "read YMM%d" n))) [0;1;2;3;4;5] THEN
    FULL_INIT_TAC THEN
    XMM_EXISTSTOP_TAC "top6" `YMM6` THEN XMM_EXISTSTOP_TAC "top7" `YMM7` THEN
    VAL_INT64_TAC `4 + 8 * i` THEN
    MAP_EVERY (fun g ->
      MAP_EVERY (fun kk -> ALIGN16_IDX_TAC `rsp0:int64`
        (parse_term(Printf.sprintf "4 * (4 + 8 * i) + %d" (kk + 16 * g)))) [k; kh]) [0;1] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATCH_MP (CHUNK_INPUT_SPLIT_N 8) (ASSUME `i < 32`)] o
      check (fun th -> free_in `x:num->int32` (concl th) && not(free_in `mld_power2round_lo` (concl th)) && not(free_in `mld_power2round_hi` (concl th)) && is_forall(concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN CP_ADDR_LINEAR_TAC [ob] THEN
    MAP_EVERY (fun g ->
      MERGE_LIN_TAC_B 2 [ob]
        (parse_term(Printf.sprintf "read(memory :> bytes128(word_add rsp0 (word (4 * (4 + 8 * i) + %d)))) s0" (k + 16 * g)))) [0;1] THEN
    VERIF_SSE_STEPS_TAC exec (1--18) THEN X86_STEPS_TAC exec (19--21) THEN
    MAP_EVERY (fun kk ->
      MAP_EVERY (fun g ->
        let lhs_tm = parse_term(Printf.sprintf
          "read (memory :> bytes128 (word_add (rsp0:int64) (word (4 * (4 + 8 * i) + %d)))) (s21:x86state)" (kk + 16 * g)) in
        FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
          check (fun th -> is_eq(concl th) && aconv (lhs(concl th)) lhs_tm))) [0;1]) [kh; k] THEN
    CP_FULL_FINAL_TAC [hb; ob] 8
      [ARITH_RULE `8 * (i + 1) = 8 * i + 8`; ARITH_RULE `4 + 8 * (i + 1) = 4 + 8 * i + 8`]
      (REWRITE_TAC[XMM6; XMM7; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST)
      (REWRITE_TAC[mld_power2round_lo; mld_power2round_hi] THEN REPEAT CONJ_TAC THEN APP_BLAST_TAC `x:num->int32`);
    FULL_EXIT0_TAC];;

let PROVE_P2RLOOP fn loop exit ob hb =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(P2RLOOP_STMT fn loop exit ob hb, P2RLOOP_TAC exec fn loop exit ob hb);;

(* ------------------------------------------------------------------------- *)
(* mld_polyt1_pack of the polynomial at rsp0 + ib into the 320 bytes at op,   *)
(* as clang -O3 has compiled it (scalar): 64 iterations of 4 coefficients     *)
(* to 5 bytes, with RAX = 12 + 16 i, so that coefficient m of iteration i is *)
(* at [rsp + rax + ib - 12 + 4 m], and RCX = op + 4 + 5 i for the stores at   *)
(* [rcx - 4 .. rcx]. The addresses of the loads and of the stores are        *)
(* replaced by those of the invariant by equations among the assumptions,    *)
(* which the simulation uses to rewrite them.                                *)
(* ------------------------------------------------------------------------- *)

let T1PACK_TAC exec fn loop exit ib =
  let alias_loads =
    MAP_EVERY (fun m ->
      SUBGOAL_THEN (parse_term(Printf.sprintf
        "word_add (rsp0:int64) (word (1 * (12 + 16 * i) + %d)) = word_add rsp0 (word (%d + 16 * i%s))"
        (ib - 12 + 4 * m) ib (if m = 0 then "" else Printf.sprintf " + %d" (4 * m)))) ASSUME_TAC THENL
       [CP_ALIAS64_TAC; ALL_TAC]) [0;1;2;3]
  and alias_stores =
    MAP_EVERY (fun (neg,m) ->
      SUBGOAL_THEN (parse_term(Printf.sprintf
        "word_add (word_add (op:int64) (word (4 + 5 * i))) (word %s) = word_add (word_add op (word (5 * i))) (word %d)" neg m))
        ASSUME_TAC THENL [CP_ALIAS64_TAC; ALL_TAC])
     ["18446744073709551612",0; "18446744073709551613",1; "18446744073709551614",2; "18446744073709551615",3] THEN
    SUBGOAL_THEN `word_add (op:int64) (word (4 + 5 * i)) = word_add (word_add op (word (5 * i))) (word 4)`
      ASSUME_TAC THENL [CP_ALIAS64_TAC; ALL_TAC] in
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (op:int64) (pc:num).
      APPEND (f_ev_epil rsp0 op pc)
       (APPEND (ENUMERATEL 64 (\i. f_ev_loop rsp0 op pc i)) (f_ev_prol rsp0 op pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `op:int64`; `pc:num`; `x:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read RAX s = word (12 + 16 * i) /\\
          read RCX s = word_add op (word (4 + 5 * i)) /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = x j) /\\
          (!j. j < 5 * i
               ==> read(memory :> bytes8(word_add op (word j))) s = mld_polyt1_pack x j)" ib)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    alias_loads THEN alias_stores THEN
    FULL_INIT_TAC THEN VAL_INT64_TAC `12 + 16 * i` THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf
      "!k. k < 4 ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * (4 * i + k))))) s0 = (x:num->int32)(4 * i + k)" ib)) MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN CP_ADDR_LINEAR_TAC [ib] THEN
    X86_STEPS_TAC exec (1--25) THEN
    CP_ADDR_LINEAR_TAC [ib] THEN ADDR_NORMALIZE_TAC THEN CP_ADDR_LINEAR_TAC [ib] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(REWRITE_TAC [ARITH_RULE `12 + 16 * (i + 1) = 12 + 16 * i + 16`;
                     ARITH_RULE `4 + 5 * (i + 1) = 4 + 5 * i + 5`] THEN
        CONV_TAC WORD_RULE THEN NO_TAC) THEN
    TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT_N 5] THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC EXPAND_CASES_CONV THEN
        REWRITE_TAC[mld_polyt1_pack] THEN
        SIMP_TAC[DIVMOD_CHUNK; ARITH] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[ADD_CLAUSES; LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
        REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN
        CONV_TAC(DEPTH_CONV BETA_CONV) THEN
        ASM_REWRITE_TAC[WORD_VAL_MOD_256; WORD_VAL_DIV_256_MOD_256] THEN
        REPEAT CONJ_TAC THEN APP_BLAST_TAC `x:num->int32` THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    FULL_EXIT0_TAC];;

let PROVE_T1PACK fn loop exit ib =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(T1PACK_STMT fn loop exit ib, T1PACK_TAC exec fn loop exit ib);;
