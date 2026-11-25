(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::SnappyDecompressor::DecompressAllTags<SnappyArrayWriter>: the     *)
(* proof (statement in the spec file), with the lemmas and tactics of        *)
(* ..._lib.ml. The segment T is proved by the class of the tag byte, one     *)
(* job each (..._t_{b,s}_<class>_proof.ml); this file proves the others,     *)
(* combines the classes and proves the theorem.                              *)
(*                                                                           *)
(* Cut points (ENSURES_MEASURE_INDUCT, common/ensures_measure.ml) with the   *)
(* measure 2 * LENGTH rest (+ 1 at L, + 2 at the entry), rest the unread     *)
(* stream at ip in one of two states (DESIGN.md 7, 7e): the buffer (ip in    *)
(* the input, ip_limit_ = q + LENGTH inp, ip_limit_min_maxtaglen_ 4 below    *)
(* it, at least 5 bytes left) or scratch_ (ip = d + 41, at most 4 bytes, the *)
(* source empty):                                                            *)
(*                                                                           *)
(*  - E, the entry: the prologue and RefillTag (EMPTY with k = 0), then L or *)
(*    the exit;                                                              *)
(*  - L (loop1): DecompressBranchless (its tags as snappy_steps), then T, or *)
(*    RefillTag (WINDOW or EMPTY) and T or the exit;                         *)
(*  - T (join3): one tag of the slow path by kind (literal, long literal     *)
(*    with v = 240..252, copies with 1-, 2- and 4-byte offsets: memmove of   *)
(*    64 bytes or IncrementalCopy), then L directly or RefillTag and L, or   *)
(*    the exit.                                                              *)
(*                                                                           *)
(* The model at each cut point is snappy_decode_tags m inp [] =             *)
(* snappy_decode_tags m rest ob, ob the output so far at out. The frame of  *)
(* the segments is one footprint clause for all the memory written (so that *)
(* C ,, C = C), weakened to the frame of the statement at the end            *)
(* (FOOTPRINT_UNION_SUBSUMED_SEQ, MAYCHANGE_FOOTPRINT_MEMRANGE_SUBSUMED).     *)
(* The code is run one instruction at a time; branches on data are split   *)
(* and the cases that the arithmetic facts contradict are closed; the       *)
(* conditions of the others are kept as arithmetic.                        *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_lib.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_t_b_lit_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_t_b_long240_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_t_b_long244_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_t_b_long248_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_t_b_long252_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_t_b_copy1_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_t_b_copy2_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_t_b_copy4_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_t_s_lit_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_t_s_long240_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_t_s_long244_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_t_s_long248_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_t_s_long252_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_t_s_copy1_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_t_s_copy2_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_t_s_copy4_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The whole function: the measure induction over the cut points.           *)
(* ------------------------------------------------------------------------- *)

let DAW_FRAME_TAC : tactic =
  REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN CONJ_TAC THENL
         [MATCH_ACCEPT_TAC SUBSUMED_REFL; ALL_TAC]) THEN
  REPEAT(MATCH_MP_TAC FOOTPRINT_UNION_SUBSUMED_SEQ THEN
         REPEAT CONJ_TAC THENL
          [CONV_TAC VALID_COMPONENT_CONV; ALL_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC MAYCHANGE_FOOTPRINT_MEMRANGE_SUBSUMED THEN
  REWRITE_TAC[DIMINDEX_64] THEN
  ((CONV_TAC NUM_REDUCE_CONV THEN NO_TAC) ORELSE
   (UNDISCH_TAC `m < 2 EXP 32` THEN ARITH_TAC));;

(* A segment lemma for the disjunct of R n at hand.                         *)
let DAW_SEGMENT_TAC (segs:thm list) : tactic =
  fun (asl,w) ->
    tryfind (fun th ->
      let th' = SPEC `n:num` th in
      let th' = MP (SPECL (snd(strip_comb(lhand(concl(SPEC_ALL th'))))) th') TRUTH in
      ACCEPT_TAC th' (asl,w)) segs;;

let daw_safe_tac (segs:thm list) : tactic =
  MAP_EVERY X_GEN_TAC daw_vars THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC daw_C THEN CONJ_TAC THENL
   [FIRST_X_ASSUM STRIP_ASSUME_TAC THEN DAW_FRAME_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`arm`; daw_R; daw_Q; daw_C] ENSURES_MEASURE_INDUCT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
      X_GEN_TAC `n:num` THEN BETA_TAC THEN
      REPEAT(MATCH_MP_TAC ENSURES_DISJ_PRECONDITION THEN CONJ_TAC) THEN
      W(fun (asl,w) ->
        let tm = mk_imp(daw_hyp,w) in
        let segth = tryfind (fun th ->
            let th1 = SPECL (`n:num` :: daw_vars) th in
            let c = concl th1 in
            let eq = DEPTH_CONV BETA_CONV (rand c) and eq' = DEPTH_CONV BETA_CONV w in
            if aconv (rhs(concl eq)) (rhs(concl eq')) then
              EQ_MP (SYM eq') (EQ_MP eq (UNDISCH th1))
            else failwith "") segs in
        let _ = tm in
        MP_TAC segth THEN REWRITE_TAC[] THEN DISCH_THEN ACCEPT_TAC)];
    DISCH_THEN(MP_TAC o SPEC `2 * LENGTH(inp:byte list) + 2`) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
    BETA_TAC THEN GEN_TAC THEN STRIP_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[]];;

let daw_safe_proof (segs:thm list) = prove(DAW_STMT, daw_safe_tac segs);;

(* ------------------------------------------------------------------------- *)
(* The segments and the theorem.                                             *)
(* ------------------------------------------------------------------------- *)

let daw_seg_prove name (g,t) =
  let t0 = Unix.gettimeofday() in
  let th = (try prove(g,t) with Failure msg -> failwith (name ^ ": " ^ msg)) in
  Printf.printf "DAT segment %s: %.0f s\n%!" name (Unix.gettimeofday() -. t0); th;;

let DAW_E_SEGMENT = daw_seg_prove "E" (DAW_E_GOAL, DAW_E_TAC);;
let DAW_LB_SEGMENT = daw_seg_prove "LB" (DAW_LB_GOAL, DAW_L_TAC true);;
let DAW_LS_SEGMENT = daw_seg_prove "LS" (DAW_LS_GOAL, DAW_L_TAC false);;
let DAW_TB_SEGMENT = daw_seg_prove "TB" (DAW_TB_GOAL, DAW_T_FROM_CLASSES_TAC
  [SNAPPY_DAT_SAW_T_B_LIT;
   SNAPPY_DAT_SAW_T_B_LONG240;
   SNAPPY_DAT_SAW_T_B_LONG244;
   SNAPPY_DAT_SAW_T_B_LONG248;
   SNAPPY_DAT_SAW_T_B_LONG252;
   SNAPPY_DAT_SAW_T_B_COPY1;
   SNAPPY_DAT_SAW_T_B_COPY2;
   SNAPPY_DAT_SAW_T_B_COPY4]);;
let DAW_TS_SEGMENT = daw_seg_prove "TS" (DAW_TS_GOAL, DAW_T_FROM_CLASSES_TAC
  [SNAPPY_DAT_SAW_T_S_LIT;
   SNAPPY_DAT_SAW_T_S_LONG240;
   SNAPPY_DAT_SAW_T_S_LONG244;
   SNAPPY_DAT_SAW_T_S_LONG248;
   SNAPPY_DAT_SAW_T_S_LONG252;
   SNAPPY_DAT_SAW_T_S_COPY1;
   SNAPPY_DAT_SAW_T_S_COPY2;
   SNAPPY_DAT_SAW_T_S_COPY4]);;

let SNAPPY_DECOMPRESSOR_DECOMPRESS_ALL_TAGS_SNAPPY_ARRAY_WRITER_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  daw_safe_proof
    [DAW_E_SEGMENT; DAW_LB_SEGMENT; DAW_LS_SEGMENT; DAW_TB_SEGMENT; DAW_TS_SEGMENT];;
