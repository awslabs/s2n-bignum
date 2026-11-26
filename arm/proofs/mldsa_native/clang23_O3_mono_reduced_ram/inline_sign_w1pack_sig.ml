(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* polyw1_pack_88 as clang 23 -O3 has inlined it into                        *)
(* polyveck_decompose_pack_w1 of mldsa44_signature_internal: after the       *)
(* decompose loop of row i has left w1_i at F + 9056 (1024 bytes), a block   *)
(* of straight-line vector code (16 LD4 of 64 bytes through x23 = F + 9056,  *)
(* x21 = F + 9312, x27 = F + 9568 and F + 9056 itself, the shifts and ORs of *)
(* the 6-bit fields, UZP1 to bytes, spills to the stack, and 4 ST3 of 48     *)
(* bytes) packs it into row i of w1 packed at F + 8288 + 192 * i. The first  *)
(* ST3 goes through x20 (row 0) or a pointer slot, the other three through   *)
(* pointer slots in the frame (F + 56 to F + 191), which the code of the     *)
(* function fills once before the attempts. The four blocks differ in their *)
(* registers, spills and slots, and the last one also sets the arguments of *)
(* the following call of mld_H44.                                            *)
(*                                                                           *)
(* The statement of a block is made from a record of its parameters         *)
(* (SI_W1PS_TERM), and the proof is that of inline_sign_w1pack_tac.ml with   *)
(* the stores found by their normalized addresses (SI_W1PS_PROVE).           *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_w1pack32.ml";;

type w1ps_inst =
  { ws_start : string; ws_stop : string; ws_steps : int;
    ws_in : int; ws_out : int;
    ws_pre : string; ws_post : string;
    ws_spill : int * int; ws_mods : string list };;

(*** The statement: w1 (x) at F + ws_in, the packed row at F + ws_out, the ***)
(*** pointer slots in F + 56 .. F + 191, the spill area ws_spill           ***)

let SI_W1PS_TERM mc p =
  let (slo,slen) = p.ws_spill in
  parse_term(Printf.sprintf
 "exists f_events.
    forall e (fp:int64) (x:num->int32) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\
      nonoverlapping (word_add fp (word %d),%d) (word pc,libmldsa_size) /\\
      nonoverlapping (word_add fp (word %d),192) (word pc,libmldsa_size)
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc) %s /\\
                read PC s = word (pc + %s) /\\
                read SP s = fp /\\ %s /\\
                (!j. j < 256
                     ==> read(memory :> bytes32(word_add fp (word(%d + 4 * j)))) s =
                         x j) /\\
                read events s = e)
           (\\s. read PC s = word (pc + %s) /\\ %s
                (!j. j < 192
                     ==> read(memory :> bytes8(word_add fp (word(%d + j)))) s =
                         mld_polyw1_pack_88 x j) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events fp pc /\\
                   memaccess_inbounds e2
                    [word_add fp (word 56),136; word_add fp (word %d),1024;
                     word_add fp (word %d),%d; word_add fp (word %d),192]
                    [word_add fp (word %d),%d; word_add fp (word %d),192]))
           (MAYCHANGE [PC; %s] ,,
            MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12;
                       Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23;
                       Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31] ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(word_add fp (word %d),%d);
                       memory :> bytes(word_add fp (word %d),192)])"
  slo slen p.ws_out mc p.ws_start p.ws_pre p.ws_in p.ws_stop p.ws_post
  p.ws_out p.ws_in slo slen p.ws_out slo slen p.ws_out
  (String.concat "; " p.ws_mods) slo slen p.ws_out);;

(*** Byte j of the output from the 128-bit store that holds it, found by ***)
(*** its normalized address F + out + 16 * (j DIV 16)                    ***)

let SI_W1PS_BYTE_TAC out stores j =
  let m = j / 16 and t = j mod 16 in
  let addr = mk_comb(mk_comb(`word_add:int64->int64->int64`,`fp:int64`),
                     mk_comb(`word:num->int64`,mk_small_numeral(out + 16 * m))) in
  let nrm a = try rhs(concl(NORMALIZE_RELATIVE_ADDRESS_CONV a)) with Failure _ -> a in
  let sth = find (fun th ->
    nrm(rand(rand(rand(rator(lhs(concl th)))))) = addr) stores in
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
    REWRITE_TAC[mld_polyw1_pack_88] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV THENC DEPTH_CONV NUM_RED_CONV) THEN
    REWRITE_TAC[] THEN W1P_BITBLAST_TAC);;

let SI_W1PS_BYTES_TAC out =
  CONV_TAC EXPAND_CASES_CONV THEN
  W(fun (asl,w) ->
    let stores = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c &&
         (try fst(dest_const(rator(rand(rand(rator(lhs c)))))) = "bytes128"
          with Failure _ -> false)
      then th else fail()) asl in
    REPEAT CONJ_TAC THENL (map (SI_W1PS_BYTE_TAC out stores) (0--191)));;

(*** The proof: simulate with the input as 128-bit words, with the LD4 ***)
(*** results as lanes and the vector registers simplified after each step ***)

let SI_W1PS_PROVE mc p =
  let ex = INLINE_LOOP_EXEC p.ws_start p.ws_stop in
  prove(SI_W1PS_TERM mc p,
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (pc:num). f_ev_w1 fp pc :(uarch_event)list` THEN
  META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst ex] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN INLINE_MAP_INPUT_TAC p.ws_in `x:num->int32` THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC ex [n] THEN INLINE_W1P_FIX_TAC THEN
                      INLINE_W1P2_SIMP_TAC) (1--p.ws_steps) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [CONV_TAC WORD_RULE THEN NO_TAC;
         SI_W1PS_BYTES_TAC p.ws_out;
         MONOTONE_MAYCHANGE_TAC THEN NO_TAC;
         DISCHARGE_SAFETY_PROPERTY_TAC]);;
