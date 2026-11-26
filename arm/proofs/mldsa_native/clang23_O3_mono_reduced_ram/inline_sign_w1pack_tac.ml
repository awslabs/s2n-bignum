(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The statement, lemmas and tactics of the inlined polyw1_pack_88 of        *)
(* mldsa44_verify_internal (the theorem is in inline_sign_w1pack.ml; the     *)
(* lemmas on LD4/ST3 lanes and the byte extraction are shared with           *)
(* inline_sign_w1pack32.ml). polyw1_pack_88 as clang 23 -O3 has inlined it   *)
(* into the row loop of                                                      *)
(* mldsa44_verify_internal (+0x16b8 to +0x1a88, 244 instructions without     *)
(* branches): 16 LD4 of 64 bytes of the 256 coefficients of w1 at F + 1472,  *)
(* the shifts and ORs of the 6-bit fields, UZP1 to narrow them to bytes,     *)
(* spills to the stack at F + 48 and F + 368, and 4 ST3 of 48 bytes to the   *)
(* row i of w1' packed at F + 8800 + 192 * i. The code also advances the pk  *)
(* pointer x28 by 320 and the row index x3, compares it with 4 for the loop  *)
(* test, and reloads d8.                                                     *)
(*                                                                           *)
(* The proof simulates the code with the inputs as 128-bit words of 4 lanes  *)
(* (INLINE_MAP_INPUT_TAC), rewrites the results of LD4 into lanes            *)
(* (INLINE_DEINTERLEAVE4_JOIN), extracts each output byte from the ST3       *)
(* store that holds it (INLINE_INTERLEAVE3_BYTES, W1P_EXTRACT_CONV) and      *)
(* proves it equal to mld_polyw1_pack_88 by bit-blasting on the two          *)
(* coefficients it depends on.                                               *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_map.ml";;
needs "common/mldsa_native_packing.ml";;

(*** The statement ***)

let INLINE_W1PACK44_TERM =
 `exists f_events.
    forall e (fp:int64) (x:num->int32) i (tp:int64) pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 fp /\ i < 4 /\
      nonoverlapping (word_add fp (word 48),272) (word pc,libmldsa_size) /\
      nonoverlapping (word_add fp (word 368),64) (word pc,libmldsa_size) /\
      nonoverlapping (word_add fp (word (8800 + 192 * i)),192) (word pc,libmldsa_size)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                read PC s = word (pc + mldsa44_verify_internal_loop12_exit) /\
                read SP s = fp /\ read X24 s = word_add fp (word 1472) /\
                read X3 s = word i /\ read X28 s = tp /\
                read (memory :> bytes64 (word_add fp (word 32))) s =
                  word 0xfafafafafcfcfcfc /\
                (!j. j < 256
                     ==> read(memory :> bytes32(word_add fp (word(1472 + 4 * j)))) s =
                         x j) /\
                read events s = e)
           (\s. read PC s = word (pc + mldsa44_verify_internal_loop6_back) /\
                read X3 s = word (i + 1) /\ read X28 s = word_add tp (word 320) /\
                read Q8 s = word 0xfafafafafcfcfcfc /\
                (read ZF s <=> i + 1 = 4) /\
                (!j. j < 192
                     ==> read(memory :> bytes8(word_add fp (word(8800 + 192 * i + j)))) s =
                         mld_polyw1_pack_88 x j) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_events fp i pc /\
                   memaccess_inbounds e2
                    [word_add fp (word 32),8; word_add fp (word 48),272;
                     word_add fp (word 368),64; word_add fp (word 1472),1024;
                     word_add fp (word (8800 + 192 * i)),192]
                    [word_add fp (word 48),272; word_add fp (word 368),64;
                     word_add fp (word (8800 + 192 * i)),192]))
           (MAYCHANGE [PC; X3; X8; X9; X10; X11; X28] ,,
            MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12;
                       Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23;
                       Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(word_add fp (word 48),272);
                       memory :> bytes(word_add fp (word 368),64);
                       memory :> bytes(word_add fp (word (8800 + 192 * i)),192)])`;;


(*** ST3 of three 128-bit vectors with 8-bit elements: byte n of the 384 ***)
(*** bits stored is byte n DIV 3 of the vector n MOD 3                   ***)

let INLINE_INTERLEAVE3_BYTE = prove
 (`!a b c:int128 n. n < 48
    ==> word_subword (word_interleave 8 [a;b;c]:384 word) (8 * n,8):byte =
        word_subword (EL (n MOD 3) [a;b;c]) (8 * (n DIV 3),8)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; DIMINDEX_8] THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `MIN 8 8 = 8`] THEN
  REWRITE_TAC[word_interleave] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH; ARITH] THEN
  MP_TAC(SPECL [`8`;`n:num`;`r:num`] DIVMOD_CHUNK) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:384)`] THEN
  SUBGOAL_THEN `8 * n + r < 384` (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

let INLINE_INTERLEAVE3_BYTES =
  map (fun n ->
    let nt = mk_small_numeral n in
    let th = INST [nt,`n:num`] (SPEC_ALL INLINE_INTERLEAVE3_BYTE) in
    let th = MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))) in
    GENL [`a:int128`;`b:int128`;`c:int128`]
     (CONV_RULE(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_MOD_CONV ORELSEC
                           NUM_DIV_CONV) THENC
                DEPTH_CONV EL_CONV) th)) (0--47);;

(*** LD4 of 32-bit elements: lane k of vector j is element 4 * k + j ***)

let INLINE_DEINTERLEAVE4_LANE = prove
 (`!(z:512 word) j k. j < 4 /\ k < 4
    ==> word_subword (word_subdeinterleave 4 32 z j:int128) (32 * k,32):int32 =
        word_subword z (32 * (4 * k + j),32)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; DIMINDEX_32] THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `MIN 32 32 = 32`] THEN
  REWRITE_TAC[word_subdeinterleave] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPECL [`32`;`k:num`;`r:num`] DIVMOD_CHUNK) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DIMINDEX_128; DIMINDEX_CONV `dimindex(:512)`] THEN
  SUBGOAL_THEN `32 * k + r < 128 /\ 32 * (4 * k + j) + r < 512 /\
                (4 * k + j) * 32 + r = 32 * (4 * k + j) + r`
   (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

let INLINE_INT128_LANES = WORD_BLAST
 `!v:int128. v = word_join (word_join (word_subword v (96,32):int32)
                                     (word_subword v (64,32):int32):int64)
                          (word_join (word_subword v (32,32):int32)
                                     (word_subword v (0,32):int32):int64)`;;

let INLINE_DEINTERLEAVE4_JOIN =
  map (fun j ->
    let jt = mk_small_numeral j in
    let lane k =
      let th = SPECL [`z:512 word`; jt; mk_small_numeral k]
                 INLINE_DEINTERLEAVE4_LANE in
      CONV_RULE(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV))
       (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) in
    let th0 = ISPEC (mk_comb(mk_comb(mk_comb(
                `word_subdeinterleave 4 32:512 word->num->int128`,`z:512 word`),
                jt) |> (fun t -> rator t), jt)) INLINE_INT128_LANES in
    GEN `z:512 word`
     (CONV_RULE(RAND_CONV(REWRITE_CONV(map lane (0--3)))) th0)) (0--3);;

let INLINE_W1P_FIX_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> is_const t &&
                         fst(dest_const t) = "word_subdeinterleave")) (concl th)
    then CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)
          (REWRITE_RULE INLINE_DEINTERLEAVE4_JOIN th)
    else th);;

let INLINE_BYTES8_OF_BYTES128 = prove
 (`!(a:int64) (v:int128) s t.
        read (memory :> bytes128 a) s = v /\ t < 16
        ==> read (memory :> bytes8 (word_add a (word t))) s =
            word_subword v (8 * t,8)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; BYTES8_WBYTES; BYTES128_WBYTES;
              READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_8; DIMINDEX_128] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MIN_CONV) THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 8 = 2 EXP (8 * 1)`] THEN
  REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let rec W1P_EXTRACT_CONV tm =
  let isop name t = try fst(dest_const(fst(strip_comb t))) = name
                    with Failure _ -> false in
  if not(isop "word_subword" tm) then REFL tm else
  let x = lhand tm in
  if isop "word_or" x then
    (REWR_CONV WORD_SUBWORD_OR THENC BINOP_CONV W1P_EXTRACT_CONV) tm
  else if isop "word_and" x then
    (REWR_CONV WORD_SUBWORD_AND THENC BINOP_CONV W1P_EXTRACT_CONV) tm
  else if isop "word_interleave" x then
    (FIRST_CONV (map REWR_CONV INLINE_INTERLEAVE3_BYTES) THENC
     W1P_EXTRACT_CONV) tm
  else
    (try (WORD_SIMPLE_SUBWORD_CONV THENC
          (fun t -> if isop "word_subword" t && not(t = tm)
                    then W1P_EXTRACT_CONV t else REFL t)) tm
     with Failure _ -> REFL tm);;

(*** Byte j of the output: the store fact for its 16 bytes, the byte ***)
(*** extracted, and the packing by bit-blasting on its coefficients  ***)

let W1P_BITBLAST_TAC =
  W(fun (asl,w) ->
    let atoms = setify(find_terms (fun t -> is_comb t &&
                         rator t = `x:num->int32`) w) in
    let vs = map (fun a -> mk_var("xv"^string_of_int(dest_small_numeral(rand a)),
                                  `:int32`)) atoms in
    let lem = BITBLAST_RULE(subst (zip vs atoms) w) in
    ACCEPT_TAC(INST (zip atoms vs) lem));;

let W1P_BYTE_TAC base stores j =
  let m = j / 16 and t = j mod 16 in
  let addr = if m = 0 then base else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,base),
            mk_comb(`word:num->int64`,mk_small_numeral(16 * m))) in
  let sth = find (fun th -> rand(rand(rand(rator(lhs(concl th))))) = addr) stores in
  let bth = MP (SPECL [addr; rhs(concl sth); rand(lhs(concl sth));
                       mk_small_numeral t] INLINE_BYTES8_OF_BYTES128)
               (CONJ sth (EQT_ELIM(NUM_REDUCE_CONV
                  (mk_binop `(<):num->num->bool` (mk_small_numeral t) `16`)))) in
  let bth = CONV_RULE(RAND_CONV(RAND_CONV(LAND_CONV NUM_MULT_CONV) THENC
                                W1P_EXTRACT_CONV)) bth in
  let baddr = rand(rand(rand(rator(lhs(concl bth))))) in
  W(fun (asl,w) ->
    let gaddr = rand(rand(rand(rator(lhs w)))) in
    let eq = prove(mk_eq(gaddr,baddr),
                   REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
                   AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) in
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [eq] THEN
    GEN_REWRITE_TAC LAND_CONV [bth] THEN
    REWRITE_TAC[mld_polyw1_pack_88] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV THENC DEPTH_CONV NUM_RED_CONV) THEN
    REWRITE_TAC[] THEN W1P_BITBLAST_TAC);;

let W1P_BASE_EQ = prove
 (`i < 4 ==> word (val (word_add (fp:int64) (word 8800)) + val (word i:int64) * 192):int64 =
             word_add fp (word (8800 + 192 * i))`,
  DISCH_TAC THEN SUBGOAL_THEN `val(word i:int64) = i` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_VAL] THEN CONV_TAC WORD_RULE);;

let INLINE_W1PACK44_LD4 =
  [4;7;10;11;53;54;57;64;124;125;130;139;173;174;183;189];;

let W1P_BYTES_TAC =
  CONV_TAC EXPAND_CASES_CONV THEN
  W(fun (asl,w) ->
    let base = `word_add (fp:int64) (word (8800 + 192 * i))` in
    let stores = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c && free_in `i:num` c &&
         (try fst(dest_const(rator(rand(rand(rator(lhs c)))))) = "bytes128"
          with Failure _ -> false)
      then th else fail()) asl in
    REPEAT CONJ_TAC THENL (map (W1P_BYTE_TAC base stores) (0--191)));;

let W1P_EXEC = INLINE_LOOP_EXEC "mldsa44_verify_internal_loop12_exit"
                                "mldsa44_verify_internal_loop6_back";;

let INLINE_W1PACK44_PROVE tm =
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (i:num) (pc:num). f_ev_w1 fp i pc :(uarch_event)list` THEN
  META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst W1P_EXEC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN INLINE_MAP_INPUT_TAC 1472 `x:num->int32` THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC W1P_EXEC [n] THEN
                      (if mem n INLINE_W1PACK44_LD4 then INLINE_W1P_FIX_TAC
                       else ALL_TAC)) (1--244) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP W1P_BASE_EQ (ASSUME `i < 4`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [CONV_TAC WORD_RULE THEN NO_TAC;
         UNDISCH_TAC `i < 4` THEN SPEC_TAC(`i:num`,`i:num`) THEN
         CONV_TAC EXPAND_CASES_CONV THEN
         CONV_TAC(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV) THEN NO_TAC;
         W1P_BYTES_TAC;
         REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC;
         DISCHARGE_SAFETY_PROPERTY_TAC]);;
