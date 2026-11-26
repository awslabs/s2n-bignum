(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* polyw1_unpack_88 as clang 23 -O3 has inlined it into pack_sig_h of        *)
(* mldsa44_signature_internal (one loop per row of w1 packed): 48 bytes and  *)
(* 64 coefficients per iteration, 4 iterations. The code loads the bytes     *)
(* with LD3, spreads them with TBL (indices 0 to 7 and out-of-range bytes),  *)
(* USHR, SHL, AND and ORR, and stores four vectors with ST4. There are two   *)
(* shapes:                                                                   *)
(*   A (row 0): input a + x8 (offset 48 i), output pointer x9 = r + 256 i,   *)
(*     and the two TBL index vectors q0, q1 loaded in each iteration from    *)
(*     the constants of the function through x14 and x16;                    *)
(*   B (rows 1 to 3): input register + x9 (offset 48 i), output pointer      *)
(*     x10 = r + 256 i, q0 and q1 already loaded.                            *)
(* q12, q13 hold the indices 0 to 3 and 4 to 7, q14 and q15 the masks 0x30   *)
(* and 0x3c in each lane.                                                    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_unpack.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_eta.ml";;

type w1u_inst =
  { wu_loop : string; wu_exit : string; wu_shape : string;
    wu_in : string; wu_off : string; wu_out : string; wu_mods : string list };;

let SI_W1U_Q0 = "0xffffff0fffffff0effffff0dffffff0c";;
let SI_W1U_Q1 = "0xffffff0bffffff0affffff09ffffff08";;

let SI_W1U_TERM mc p =
  let qmods,xmods = partition (fun r -> String.get r 0 = 'Q') p.wu_mods in
  let pre = if p.wu_shape = "A" then
      "read X14 s = word_add (word pc) (word 245760) /\\
       read X16 s = word_add (word pc) (word 245760) /\\"
    else Printf.sprintf
      "read Q0 s = word %s /\\ read Q1 s = word %s /\\" SI_W1U_Q0 SI_W1U_Q1 in
  let post = Printf.sprintf
      "read Q0 s = word %s /\\ read Q1 s = word %s /\\" SI_W1U_Q0 SI_W1U_Q1 in
  let rd = if p.wu_shape = "A" then
      "a,192; r,1024; word (pc + mldsa44_signature_internal_consts),128"
    else "a,192; r,1024" in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e r a (b:num->byte) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,192)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = a /\\ read %s s = word 0 /\\ read %s s = r /\\
                  read Q12 s = word 0xffffff03ffffff02ffffff01ffffff00 /\\
                  read Q13 s = word 0xffffff07ffffff06ffffff05ffffff04 /\\
                  read Q14 s = word 0x00000030000000300000003000000030 /\\
                  read Q15 s = word 0x0000003c0000003c0000003c0000003c /\\ %s
                  (!j. j < 192
                       ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\ %s
                  read %s s = a /\\ read %s s = word 192 /\\
                  read %s s = word_add r (word 1024) /\\
                  (!j. j < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                           mld_polyw1_unpack_88 b j) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events r a pc /\\
                     memaccess_inbounds e2 [%s] [r,1024]))
             (MAYCHANGE [PC; %s] ,, MAYCHANGE [%s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(r,1024)])"
   mc p.wu_loop p.wu_in p.wu_off p.wu_out pre
   p.wu_exit post p.wu_in p.wu_off p.wu_out rd
   (String.concat "; " xmods) (String.concat "; " qmods));;

let SI_W1U_INV p =
  let q = Printf.sprintf "read Q0 s = word %s /\\ read Q1 s = word %s" SI_W1U_Q0 SI_W1U_Q1 in
  Printf.sprintf
   "\\i s. read %s s = a /\\ read %s s = word (48 * i) /\\
          read %s s = word_add r (word (256 * i)) /\\
          read Q12 s = word 0xffffff03ffffff02ffffff01ffffff00 /\\
          read Q13 s = word 0xffffff07ffffff06ffffff05ffffff04 /\\
          read Q14 s = word 0x00000030000000300000003000000030 /\\
          read Q15 s = word 0x0000003c0000003c0000003c0000003c /\\ %s /\\
          (!j. j < 192 ==> read(memory :> bytes8(word_add a (word j))) s = (b:num->byte) j) /\\
          (!j. j < 64 * i
               ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                   mld_polyw1_unpack_88 b j)"
   p.wu_in p.wu_off p.wu_out
   (if p.wu_shape = "A" then
      "read X14 s = word_add (word pc) (word 245760) /\\
       read X16 s = word_add (word pc) (word 245760) /\\ (0 < i ==> " ^ q ^ ")"
    else q);;

let SI_W1U_DIV4 = prove
 (`!i k. (64 * i + k) DIV 4 = 16 * i + k DIV 4`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `64 * i + k = (16 * i) * 4 + k`] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ]);;

let SI_W1U_MOD4 = prove
 (`!i k. (64 * i + k) MOD 4 = k MOD 4`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `64 * i + k = (16 * i) * 4 + k`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

(*** The proof: four iterations of the body (simulated with the input as   ***)
(*** 128-bit words and the normalization of inline_polyeta.ml), the ST4    ***)
(*** stores split into lanes and the lanes bit-blasted against             ***)
(*** mld_polyw1_unpack_88                                                  ***)

(*** The input pointer of an iteration as a variable ai = a + 48 i: the   ***)
(*** LD3 reads 48 bytes at x11 and looks for the 128-bit facts at ai,     ***)
(*** ai + 16 and ai + 32 in exactly that form                             ***)

let SI_W1U_AB asl = snd(find (fun (_,th) ->
  concl th = `word_add (a:int64) (word (48 * i)) = ai`) asl);;

let SI_W1U_IS_B8 c =
  is_eq c &&
  (try fst(dest_const(rator(rand(rand(rator(lhs c)))))) = "bytes8"
   with Failure _ -> false);;

let SI_W1U_AI_TAC =
  ABBREV_TAC `ai = word_add (a:int64) (word (48 * i))` THEN
  W(fun (asl,w) ->
    let ab = SI_W1U_AB asl in
    let eqs = ab :: map (fun k -> REWRITE_RULE[ab] (WORD_RULE(parse_term(Printf.sprintf
        "word_add (a:int64) (word (48 * i + %d)) =
         word_add (word_add a (word (48 * i))) (word %d)" k k)))) (1--47) in
    RULE_ASSUM_TAC(fun th -> if SI_W1U_IS_B8(concl th) && not(is_forall(concl th))
                             then REWRITE_RULE eqs th else th)) THEN
  W(fun (asl,w) ->
    let b8 = map snd (filter (fun (_,th) -> SI_W1U_IS_B8(concl th) &&
                                free_in `ai:int64` (concl th)) asl) in
    MAP_EVERY (fun k ->
      let addr = if k = 0 then `ai:int64` else
        mk_comb(mk_comb(`word_add:int64->int64->int64`,`ai:int64`),
                mk_comb(`word:num->int64`,mk_small_numeral k)) in
      let tm = subst [addr,`A:int64`] `read (memory :> bytes128 A) (s0:armstate)` in
      let th = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))
                 (READ_MEMORY_MERGE_CONV 4 tm) in
      ASSUME_TAC(REWRITE_RULE b8 th)) [0;16;32]);;

let SI_W1U_REG_AI_TAC =
  W(fun (asl,w) -> let ab = SI_W1U_AB asl in
    RULE_ASSUM_TAC(fun th -> if SI_ETA_IS_REG(concl th) then REWRITE_RULE[ab] th
                             else th));;

let SI_W1U_UNAI_TAC =
  W(fun (asl,w) -> let ab = SI_W1U_AB asl in
    RULE_ASSUM_TAC(fun th -> if concl th = concl ab ||
                                not(free_in `ai:int64` (concl th)) then th
                             else REWRITE_RULE[SYM ab] th) THEN
    REWRITE_TAC[SYM ab]);;

let SI_W1U_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[ARITH_RULE `48 * (i + 1) = 48 * i + 48`;
                  ARITH_RULE `256 * (i + 1) = 256 * i + 256`] THEN
      CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT; CHUNK_OUTPUT_SPLIT_1] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC EXPAND_CASES_CONV THEN
      REWRITE_TAC[mld_polyw1_unpack_88; SI_W1U_DIV4; SI_W1U_MOD4] THEN
      SIMP_TAC[DIVMOD_CHUNK; ARITH] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN APP_BLAST_TAC `b:num->byte` THEN
      NO_TAC) THEN
  SI_W1U_UNAI_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let SI_W1U_PROVE mc p nsteps =
  let ex = INLINE_LOOP_EXEC p.wu_loop p.wu_exit in
  prove(SI_W1U_TERM mc p,
  CONCRETIZE_F_EVENTS_TAC
   `\(r:int64) (a:int64) (pc:num).
      APPEND (f_ev_epil r a pc)
       (APPEND (ENUMERATEL 4 (\i. f_ev_loop r a pc i)) (f_ev_prol r a pc))
      :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `r:int64`; `a:int64`;
                       `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst ex] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `4` (parse_term("pc + " ^ p.wu_loop))
   (parse_term("pc + " ^ p.wu_exit)) (parse_term(SI_W1U_INV p)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LT_REFL; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `b:num->byte` 48 THEN
    SI_W1U_AI_TAC THEN
    (if p.wu_shape = "A" then
       MAP_EVERY (fun th -> FIRST_ASSUM(fun a ->
         if concl a = hd(hyp (UNDISCH th)) then ASSUME_TAC(MP th a) else NO_TAC))
        (ETA_CONST_FACTS "mldsa44" `s0:armstate`)
     else ALL_TAC) THEN
    MAP_EVERY (fun k -> ARM_STEPS_TAC ex [k] THEN ETA_NORM THEN
                        (if k = 1 then SI_W1U_REG_AI_TAC else ALL_TAC)) (1--nsteps) THEN
    SI_W1U_UNAI_TAC THEN INLINE_NORMALIZE_TAC THEN
    WIDE_STORE_SPLIT_TAC `r:int64` 32 THEN INLINE_ST4_LANES_TAC THEN
    RULE_ASSUM_TAC(fun th -> if SI_W1U_IS_B8 (concl th) then th
                             else CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) th) THEN
    SI_W1U_FINAL_TAC;
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `0 < 4`]) THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;
