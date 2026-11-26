(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* polyw1_pack_32 (gamma2 = (q - 1) / 32) as clang 23 -O3 has inlined it    *)
(* into the row loop of mldsa65_verify_internal and mldsa87_verify_internal  *)
(* (from the exit of the use_hint loop to the back branch of the row loop,   *)
(* without branches): 32 LD2 of 32 bytes of the 256 coefficients of w1 at    *)
(* F + win, which split the even and the odd coefficients, SHL by 4 of the   *)
(* odd ones and ORR, UZP1 twice to narrow the 32-bit lanes to bytes, spills  *)
(* to the stack at F + 48 .. F + 304, and STP of the 128 bytes to row i of   *)
(* w1' packed at F + wout + 128 * i. The code also advances the pk pointer   *)
(* by 320 and the row index x3, and compares it with K for the loop test.    *)
(*                                                                           *)
(* The proof simulates the code with the input as 256-bit words of 8 lanes   *)
(* (INLINE_MAP_INPUT256_TAC), rewrites the results of LD2 into lanes         *)
(* (INLINE_DEINTERLEAVE2_JOIN), takes the base of the stores as             *)
(* F + wout + 128 * i (W1P2_BASE_EQ), extracts each output byte from the    *)
(* store that holds it and proves it equal to mld_polyw1_pack_32 by         *)
(* bit-blasting on the two coefficients it depends on.                       *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_w1pack_tac.ml";;

(*** LD2 of 32-bit elements: lane k of the first vector is element 2 * k, ***)
(*** of the second element 2 * k + 1                                      ***)

let INLINE_DEINTERLEAVE2_JOIN =
  let lanes v ks =
    let l k = subst [mk_small_numeral(32 * k),`p:num`]
                `word_subword (z:256 word) (p,32):int32` in
    let w a b = list_mk_comb(`word_join:int32->int32->int64`,[a;b]) in
    list_mk_comb(`word_join:int64->int64->int128`,
      [w (l (el 3 ks)) (l (el 2 ks)); w (l (el 1 ks)) (l (el 0 ks))]) in
  let mk f ks =
    GEN `z:256 word`
     (prove(mk_eq(mk_comb(f,`z:256 word`),lanes `z:256 word` ks),
            REWRITE_TAC[word_deinterleave4_x; word_deinterleave4_y;
                        word_deinterleave2_x; word_deinterleave2_y;
                        word_split_lo; word_split_hi] THEN
            CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
            CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC WORD_BLAST)) in
  [mk `word_deinterleave4_x:256 word->int128` [0;2;4;6];
   mk `word_deinterleave4_y:256 word->int128` [1;3;5;7]];;

let INLINE_W1P2_FIX_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> is_const t &&
              (fst(dest_const t) = "word_deinterleave4_x" ||
               fst(dest_const t) = "word_deinterleave4_y"))) (concl th)
    then CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)
          (REWRITE_RULE INLINE_DEINTERLEAVE2_JOIN th)
    else th);;

(*** After each step, the vector registers as joins of their 32-bit lanes ***)
(*** in terms of the inputs: the lane selections pushed through the ORs and ***)
(*** the joins (W1P_EXTRACT_CONV), which keeps the terms small               ***)

let INLINE_W1P2_SIMP_TAC =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c &&
       (try String.get (fst(dest_const(rand(rator(lhs c))))) 0 = 'Q'
        with Failure _ -> false)
    then CONV_RULE(RAND_CONV(TOP_DEPTH_CONV(CHANGED_CONV W1P_EXTRACT_CONV))) th
    else th);;

(*** LD2 reads 256 bits: the input as 256-bit words, joins of the 128-bit ***)
(*** words of INLINE_MAP_INPUT_TAC                                         ***)

let INLINE_MAP_INPUT256_TAC (off:int) =
  let fv = `fp:int64` in
  let addr n = mk_comb(mk_comb(`word_add:int64->int64->int64`,fv),
                       mk_comb(`word:num->int64`,mk_small_numeral n)) in
  W(fun (asl,w) ->
    let f128 = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c &&
         can (term_match [] `read (memory :> bytes128 a) (s0:armstate)`) (lhs c)
      then th else fail()) asl in
    MAP_EVERY (fun k ->
      let tm = subst [addr(off + 32 * k),`A:int64`]
                `read (memory :> bytes256 A) (s0:armstate)` in
      let eth = GEN_REWRITE_CONV I
                 [el 0 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] tm in
      let eth = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV
                  NORMALIZE_RELATIVE_ADDRESS_CONV)) eth in
      ASSUME_TAC(REWRITE_RULE f128 eth)) (0--31));;

(*** The statement for the function fn: the labels of the start and the  ***)
(*** stop, the offsets of w1 and of w1' packed, the number of rows K, the ***)
(*** register of the pk pointer                                           ***)

type w1p32_inst =
  { wp_fn : string; wp_start : string; wp_stop : string; wp_in : int;
    wp_out : int; wp_k : int; wp_xw : string; wp_tp : string; wp_steps : int;
    wp_mods : string list };;

let INLINE_W1PACK32_TERM p =
  parse_term(Printf.sprintf
 "exists f_events.
    forall e (fp:int64) (x:num->int32) i (tp:int64) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\ i < %d /\\
      nonoverlapping (word_add fp (word 48),256) (word pc,libmldsa_size) /\\
      nonoverlapping (word_add fp (word (%d + 128 * i)),128) (word pc,libmldsa_size)
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + %s_%s) /\\
                read SP s = fp /\\ read %s s = word_add fp (word %d) /\\
                read X3 s = word i /\\ read %s s = tp /\\
                (!j. j < 256
                     ==> read(memory :> bytes32(word_add fp (word(%d + 4 * j)))) s =
                         x j) /\\
                read events s = e)
           (\\s. read PC s = word (pc + %s_%s) /\\
                read X3 s = word (i + 1) /\\ read %s s = word_add tp (word 320) /\\
                (read ZF s <=> i + 1 = %d) /\\
                (!j. j < 128
                     ==> read(memory :> bytes8(word_add fp (word(%d + 128 * i + j)))) s =
                         mld_polyw1_pack_32 x j) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events fp i pc /\\
                   memaccess_inbounds e2
                    [word_add fp (word 48),256; word_add fp (word %d),1024;
                     word_add fp (word (%d + 128 * i)),128]
                    [word_add fp (word 48),256;
                     word_add fp (word (%d + 128 * i)),128]))
           (MAYCHANGE [PC; X3; %s] ,,
            MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q9; Q10; Q11; Q12;
                       Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23;
                       Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(word_add fp (word 48),256);
                       memory :> bytes(word_add fp (word (%d + 128 * i)),128)])"
  p.wp_k p.wp_out p.wp_fn p.wp_start p.wp_xw p.wp_in p.wp_tp p.wp_in
  p.wp_fn p.wp_stop p.wp_tp p.wp_k p.wp_out p.wp_in p.wp_out p.wp_out
  (String.concat "; " (p.wp_tp :: p.wp_mods)) p.wp_out);;

(*** Byte j of the output: the store fact for its 16 bytes, the byte ***)
(*** extracted, and the packing by bit-blasting                      ***)

let W1P2_BYTE_TAC base stores j =
  let m = j / 16 and t = j mod 16 in
  let addr = if m = 0 then base else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,base),
            mk_comb(`word:num->int64`,mk_small_numeral(16 * m))) in
  let nrm a = try rhs(concl(NORMALIZE_RELATIVE_ADDRESS_CONV a)) with Failure _ -> a in
  let sth = find (fun th ->
    nrm(rand(rand(rand(rator(lhs(concl th)))))) = nrm addr) stores in
  let faddr = rand(rand(rand(rator(lhs(concl sth))))) in
  let bth = MP (SPECL [faddr; rhs(concl sth); rand(lhs(concl sth));
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
    REWRITE_TAC[mld_polyw1_pack_32] THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    REWRITE_TAC[] THEN W1P_BITBLAST_TAC);;

let W1P2_SHL7 = prove
 (`!i. word_shl (word i:int64) 7 = word(128 * i)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let W1P2_BASE_EQ k out = prove
 (subst [mk_small_numeral k,`k:num`; mk_small_numeral out,`n:num`]
   `i < k ==> word_add (word_add (fp:int64) (word n)) (word_shl (word i) 7):int64 =
              word_add fp (word (n + 128 * i))`,
  DISCH_TAC THEN REWRITE_TAC[W1P2_SHL7; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

let W1P2_BYTES_TAC p =
  CONV_TAC EXPAND_CASES_CONV THEN
  W(fun (asl,w) ->
    let base = subst [mk_small_numeral p.wp_out,`n:num`]
                 `word_add (fp:int64) (word (n + 128 * i))` in
    let stores = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c && free_in `i:num` c &&
         (try fst(dest_const(rator(rand(rand(rator(lhs c)))))) = "bytes128"
          with Failure _ -> false)
      then th else fail()) asl in
    REPEAT CONJ_TAC THENL (map (W1P2_BYTE_TAC base stores) (0--127)));;

let W1P2_EXEC p = INLINE_LOOP_EXEC (p.wp_fn ^ "_" ^ p.wp_start)
                                   (p.wp_fn ^ "_" ^ p.wp_stop);;

let INLINE_W1PACK32_PROVE p =
  let ex = W1P2_EXEC p in
  let ith = parse_term(Printf.sprintf "i < %d" p.wp_k) in
  prove(INLINE_W1PACK32_TERM p,
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (i:num) (pc:num). f_ev_w1 fp i pc :(uarch_event)list` THEN
  META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst ex] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN INLINE_MAP_INPUT_TAC p.wp_in `x:num->int32` THEN
  INLINE_MAP_INPUT256_TAC p.wp_in THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC ex [n] THEN INLINE_W1P2_FIX_TAC THEN
    INLINE_W1P2_SIMP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (W1P2_BASE_EQ p.wp_k p.wp_out) (ASSUME ith)]))
   (1--p.wp_steps) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [CONV_TAC WORD_RULE THEN NO_TAC;
         UNDISCH_TAC ith THEN SPEC_TAC(`i:num`,`i:num`) THEN
         CONV_TAC EXPAND_CASES_CONV THEN
         CONV_TAC(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV) THEN NO_TAC;
         W1P2_BYTES_TAC p;
         REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC;
         DISCHARGE_SAFETY_PROPERTY_TAC]);;

(*** The instances ***)

let INLINE_W1PACK32_65 =
  { wp_fn = "mldsa65_verify_internal"; wp_start = "loop13_exit";
    wp_stop = "loop7_back"; wp_in = 1376; wp_out = 9792; wp_k = 6;
    wp_xw = "X25"; wp_tp = "X22"; wp_steps = 180;
    wp_mods = ["X8"; "X9"; "X10"; "X11"; "X12"] };;

let INLINE_W1PACK32_87 =
  { wp_fn = "mldsa87_verify_internal"; wp_start = "loop15_exit";
    wp_stop = "loop9_back"; wp_in = 1376; wp_out = 11840; wp_k = 8;
    wp_xw = "X23"; wp_tp = "X22"; wp_steps = 180;
    wp_mods = ["X8"; "X9"; "X10"; "X11"; "X12"] };;
