(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* DecompressAllTags<SnappyDecompressionValidator> (0x6a30): correctness and *)
(* memory safety (snappy_decompressor_decompress_all_tags_validator_spec.ml), *)
(* relative to DecompressBranchless<size_t> and RefillTag.                    *)
(*                                                                           *)
(* Cut points L = 0x6a80 (before DecompressBranchless, measure 2 |rest| + 1) *)
(* and T = 0x6aa4 (one tag of the slow path, measure 2 |rest|), with the     *)
(* window in the input (B: at q + i, at least 5 bytes left) or in scratch_  *)
(* (S: at d + 41, 1 to 4 bytes); the model: (decode_tags m r [] = NONE <=>   *)
(* decode_tags m rest out = NONE), LENGTH out + 22 |rest| <= 22 |r|, and     *)
(* produced = LENGTH out. Segments: the entry, L_B, L_S, T_B, T_S (the tag   *)
(* by class, the branches decided by case facts set up before the run). The *)
(* induction is over a frame with one footprint (idempotent), weakened to   *)
(* and from the frame of the spec.                                           *)
(*                                                                           *)
(* T_B and T_S are combined here from their tag classes, the contracts of    *)
(* the pieces ..._validator_t_{b,s}_{class}_spec.ml, each proved in its own *)
(* proof file (independent jobs). The tactics are in                         *)
(* arm/proofs/snappy/dat_validator_lib.ml. First assembled by a development  *)
(* script, now maintained by hand.                                           *)
(* ========================================================================= *)

needs "arm/proofs/snappy/dat_validator_lib.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_validator_t_b_lit_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_validator_t_b_litlong60_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_validator_t_b_litlong61_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_validator_t_b_litlong62_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_validator_t_b_litlong63_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_validator_t_b_c1_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_validator_t_b_c2_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_validator_t_b_c4_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_validator_t_s_lit_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_validator_t_s_litlong_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_validator_t_s_c1_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_validator_t_s_c2_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_validator_t_s_c4_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The whole function: entry, cut points with the measure, the frame with    *)
(* one footprint for the induction, back to the frame of the spec.           *)
(* ------------------------------------------------------------------------- *)

let dat_W =
 `memrange(word_sub sp (word 96),96) UNION
  memrange(word_sub sp (word 320),224) UNION
  memrange((d:int64),41) UNION
  memrange(word_add d (word 41),5) UNION
  memrange(word_add src (word 8),16) UNION
  memrange(word_add v (word 8),8)`;;

let dat_cstar =
  subst [dat_W,`W:int64->bool`]
   `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X25; X26; X29; X30] ,,
    MAYCHANGE [memory :> footprint W]`;;

let DAT_SUBSUMED_TRANS = prove
 (`!(R:A->A->bool) S U. R subsumed S /\ S subsumed U ==> R subsumed U`,
  REWRITE_TAC[subsumed] THEN MESON_TAC[]);;

(* The footprint of a union of memranges, subsumed by their byte clauses.    *)

let rec dat_fp_decomp (w:term) : thm =
  match w with
    Comb(Comb(Const("UNION",_),a),b) ->
      let th1 = ISPECL [a;b] DAT_FOOTPRINT_UNION_SUBSUMED in
      let tha = dat_fp_decomp a and thb = dat_fp_decomp b in
      let th2 = MATCH_MP SUBSUMED_SEQ (CONJ tha thb) in
      MATCH_MP DAT_SUBSUMED_TRANS (CONJ th1 th2)
  | Comb(Const("memrange",_),r) ->
      let a,k = dest_pair r in
      MP (ISPECL [`memory:(armstate,int64->byte)component`; a; k]
            MAYCHANGE_FOOTPRINT_MEMRANGE_SUBSUMED)
         (EQT_ELIM((REWRITE_CONV[DIMINDEX_64] THENC NUM_REDUCE_CONV)(mk_binary "<=" (k,`2 EXP dimindex(:64)`))))
  | _ -> failwith "dat_fp_decomp";;

let DAT_CSTAR_SUBSUMED = prove
 (mk_comb(mk_comb(`(subsumed):(armstate->armstate->bool)->(armstate->armstate->bool)->bool`,
                  dat_cstar),dat_frame),
  let th = dat_fp_decomp dat_W in
  MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL] THEN
  MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL] THEN
  ACCEPT_TAC th);;

let DAT_BYTES_SUB_FP = prove
 (`!(a:int64) k t. memrange(a,k) SUBSET t
       ==> MAYCHANGE [memory :> bytes(a,k)] subsumed MAYCHANGE [memory :> footprint t]`,
  REWRITE_TAC[MAYCHANGE_SING] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSUMED_ASSIGNS_SUBCOMPONENTS THEN
  MATCH_MP_TAC SUBSUMED_ASSIGNS_BYTES_FOOTPRINT THEN ASM_REWRITE_TAC[]);;

let DAT_SEQ_SUB_IDEM = prove
 (`!(X:A->A->bool) Y Z. X subsumed Z /\ Y subsumed Z /\ (Z ,, Z) = Z ==> (X ,, Y) subsumed Z`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUBSUMED_SEQ THEN ASM_REWRITE_TAC[]);;

let DAT_FRAME_SUBSUMED = prove
 (mk_comb(mk_comb(`(subsumed):(armstate->armstate->bool)->(armstate->armstate->bool)->bool`,
                  dat_frame),dat_cstar),
  MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL] THEN
  MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL] THEN
  REPEAT(MATCH_MP_TAC DAT_SEQ_SUB_IDEM THEN REPEAT CONJ_TAC) THEN
  TRY MAYCHANGE_IDEMPOT_TAC THEN
  MATCH_MP_TAC DAT_BYTES_SUB_FP THEN SET_TAC[]);;

let DAT_CSTAR_IDEM = prove
 (mk_eq(list_mk_icomb ",," [dat_cstar; dat_cstar],dat_cstar),
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC);;

let ENSURES_WEAKEN = prove
 (`!P Q Q' (C:armstate->armstate->bool) C'.
     ensures arm P Q C /\ (!s. Q s ==> Q' s) /\ C subsumed C'
     ==> ensures arm P Q' C'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC `C:armstate->armstate->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC `Q:armstate->bool` THEN ASM_REWRITE_TAC[]);;

(* R n: a cut point with its measure.                                         *)

let dat_R =
  let lb = dat_body dat_L_b and ls = dat_body dat_L_s
  and tb = dat_body dat_T_b and ts = dat_body dat_T_s in
  let v3 = [`i:num`; `rest:byte list`; `out:byte list`] in
  let d1 = list_mk_exists(v3,mk_conj(`n = 2 * LENGTH(rest:byte list) + 1`,mk_disj(lb,ls)))
  and d2 = list_mk_exists(v3,mk_conj(`n = 2 * LENGTH(rest:byte list)`,mk_disj(tb,ts))) in
  list_mk_abs([`n:num`; `s:armstate`],mk_disj(d1,d2));;

(* The cut points and their segments, with predicate variables.              *)

let DAT_CUT_LEMMA = prove
 (`!(step:A->A->bool) Post (Lb:num->byte list->byte list->A->bool)
     (Ls:num->byte list->byte list->A->bool) (Tb:num->byte list->byte list->A->bool)
     (Ts:num->byte list->byte list->A->bool) C.
     (!i rest out. ensures step (Lb i rest out)
        (\s. Post s \/
             (?i' rest' out'. LENGTH rest' <= LENGTH rest /\ Tb i' rest' out' s) \/
             (?i' rest' out'. LENGTH rest' <= LENGTH rest /\ Ts i' rest' out' s)) C) /\
     (!i rest out. ensures step (Ls i rest out)
        (\s. Post s \/
             (?i' rest' out'. LENGTH rest' <= LENGTH rest /\ Tb i' rest' out' s) \/
             (?i' rest' out'. LENGTH rest' <= LENGTH rest /\ Ts i' rest' out' s)) C) /\
     (!i rest out. ensures step (Tb i rest out)
        (\s. Post s \/
             (?i' rest' out'. LENGTH rest' < LENGTH rest /\ Lb i' rest' out' s) \/
             (?i' rest' out'. LENGTH rest' < LENGTH rest /\ Ls i' rest' out' s)) C) /\
     (!i rest out. ensures step (Ts i rest out)
        (\s. Post s \/
             (?i' rest' out'. LENGTH rest' < LENGTH rest /\ Lb i' rest' out' s) \/
             (?i' rest' out'. LENGTH rest' < LENGTH rest /\ Ls i' rest' out' s)) C)
     ==> !n. ensures step
              (\s. (?i rest out. n = 2 * LENGTH rest + 1 /\
                                 (Lb i rest out s \/ Ls i rest out s)) \/
                   (?i rest out. n = 2 * LENGTH rest /\
                                 (Tb i rest out s \/ Ts i rest out s)))
              (\s. Post s \/
                   ?m. m < n /\
                       ((?i rest out. m = 2 * LENGTH rest + 1 /\
                                      (Lb i rest out s \/ Ls i rest out s)) \/
                        (?i rest out. m = 2 * LENGTH rest /\
                                      (Tb i rest out s \/ Ts i rest out s)))) C`,
  let pre_fact = prove
   (`!(step:A->A->bool) p P Q C. (p ==> ensures step P Q C) ==> ensures step (\s. p /\ P s) Q C`,
    REWRITE_TAC[ensures] THEN MESON_TAC[]) in
  let post = prove
   (`!(step:A->A->bool) P Q Q' C. ensures step P Q C /\ (!s. Q s ==> Q' s)
                                  ==> ensures step P Q' C`,
    MESON_TAC[ENSURES_POSTCONDITION_THM]) in
  let ex3 = REPEAT(MATCH_MP_TAC ENSURES_EXISTS_PRECONDITION THEN GEN_TAC THEN BETA_TAC) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC ENSURES_DISJ_PRECONDITION THEN CONJ_TAC THEN ex3 THEN
  MATCH_MP_TAC pre_fact THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC ENSURES_DISJ_PRECONDITION THEN CONJ_TAC THEN
  CONV_TAC(RATOR_CONV(RATOR_CONV(RAND_CONV(TRY_CONV ETA_CONV)))) THEN
  MATCH_MP_TAC post THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(rator(concl(SPEC_ALL th)))) THEN
    CONJ_TAC THENL [ACCEPT_TAC (SPEC_ALL th); ALL_TAC]) THEN
  REWRITE_TAC[] THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ2_TAC THEN
  let fin = (DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC) ORELSE
            (DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC) in
  let pick d = d THEN MAP_EVERY EXISTS_TAC [`i':num`; `rest':byte list`; `out':byte list`] THEN
               CONJ_TAC THENL [REFL_TAC; fin] in
  let m1 = `2 * LENGTH(rest':byte list)`
  and m2 = `2 * LENGTH(rest':byte list) + 1` in
  (EXISTS_TAC m1 THEN CONJ_TAC THENL [ASM_ARITH_TAC; pick DISJ2_TAC]) ORELSE
  (EXISTS_TAC m2 THEN CONJ_TAC THENL [ASM_ARITH_TAC; pick DISJ1_TAC]));;

let dat_lam4 str = list_mk_abs([`i:num`; `rest:byte list`; `out:byte list`],dat_lam str);;

let DAT_MAIN_TAC (entry:thm) (lb:thm) (ls:thm) (tb:thm) (ts:thm) : tactic =
  let cut = REWRITE_RULE[] (ISPECL [`arm`; dat_post; dat_lam4 dat_L_b; dat_lam4 dat_L_s;
                                    dat_lam4 dat_T_b; dat_lam4 dat_T_s; dat_cstar]
                                   DAT_CUT_LEMMA) in
  let seg th =
    REPEAT GEN_TAC THEN MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC dat_frame THEN CONJ_TAC THENL
     [ACCEPT_TAC DAT_FRAME_SUBSUMED;
      MATCH_MP_TAC (REWRITE_RULE[] th) THEN
      REPEAT(W(fun (_,w) -> if is_exists w then EXISTS_TAC (fst(dest_exists w))
                            else NO_TAC)) THEN
      FIRST_ASSUM ACCEPT_TAC] in
  let entry_post = rand(rator(snd(dest_imp(snd(strip_forall(concl entry)))))) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC dat_cstar THEN
  CONJ_TAC THENL [ACCEPT_TAC DAT_CSTAR_SUBSUMED; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_CUT_ENTRY THEN EXISTS_TAC dat_R THEN
  REPEAT CONJ_TAC THENL
   [ACCEPT_TAC DAT_CSTAR_IDEM;
    MATCH_MP_TAC ENSURES_WEAKEN THEN
    MAP_EVERY EXISTS_TAC [entry_post; dat_frame] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC entry THEN
      REPEAT(W(fun (_,w) -> if is_exists w then EXISTS_TAC (fst(dest_exists w))
                            else NO_TAC)) THEN
      FIRST_ASSUM ACCEPT_TAC;
      GEN_TAC THEN REWRITE_TAC[] THEN
      DISCH_THEN(DISJ_CASES_THEN2 (fun th -> DISJ1_TAC THEN ACCEPT_TAC th)
        (fun th -> DISJ2_TAC THEN EXISTS_TAC `2 * LENGTH(r:byte list) + 1` THEN
                   DISJ1_TAC THEN
                   MAP_EVERY EXISTS_TAC [`0`; `r:byte list`; `[]:byte list`] THEN
                   REWRITE_TAC[LENGTH; ADD_CLAUSES; WORD_ADD_0] THEN
                   MP_TAC th THEN MATCH_MP_TAC(TAUT `(a ==> c) /\ (b ==> d) ==> a \/ b ==> c \/ d`) THEN
                   CONJ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]));
      ACCEPT_TAC DAT_FRAME_SUBSUMED];
    MATCH_MP_TAC ENSURES_MEASURE_INDUCT THEN CONJ_TAC THENL
     [ACCEPT_TAC DAT_CSTAR_IDEM; ALL_TAC] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC cut THEN
    REPEAT CONJ_TAC THENL [seg lb; seg ls; seg tb; seg ts]];;

(* ------------------------------------------------------------------------- *)
(* The segments and the function.                                            *)
(* ------------------------------------------------------------------------- *)

Printf.printf "DAT segment SNAPPY_DAT_ENTRY\n%!";;

let SNAPPY_DAT_ENTRY = timed_section "seg.ENTRY" prove
 (dat_entry_stmt, DAT_ENTRY_TAC);;

Printf.printf "DAT segment SNAPPY_DAT_L_B\n%!";;

let SNAPPY_DAT_L_B = timed_section "seg.L_B" prove
 (dat_seg_stmt dat_L_b [dat_T_b,"<="; dat_T_s,"<="], DAT_L_TAC "B");;

Printf.printf "DAT segment SNAPPY_DAT_L_S\n%!";;

let SNAPPY_DAT_L_S = timed_section "seg.L_S" prove
 (dat_seg_stmt dat_L_s [dat_T_b,"<="; dat_T_s,"<="], DAT_L_TAC "S");;

Printf.printf "DAT segment SNAPPY_DAT_T_B\n%!";;

let SNAPPY_DAT_T_B = timed_section "seg.T_B" prove
 (dat_seg_stmt dat_T_b [dat_L_b,"<"; dat_L_s,"<"],
  DAT_T_FROM_CLASSES_TAC
   (dat_class_split ["LIT"; "LITLONG60"; "LITLONG61"; "LITLONG62"; "LITLONG63";
                     "C1"; "C2"; "C4"])
   [SNAPPY_DAT_VALIDATOR_T_B_LIT; SNAPPY_DAT_VALIDATOR_T_B_LITLONG60;
    SNAPPY_DAT_VALIDATOR_T_B_LITLONG61; SNAPPY_DAT_VALIDATOR_T_B_LITLONG62;
    SNAPPY_DAT_VALIDATOR_T_B_LITLONG63; SNAPPY_DAT_VALIDATOR_T_B_C1; SNAPPY_DAT_VALIDATOR_T_B_C2;
    SNAPPY_DAT_VALIDATOR_T_B_C4]);;

Printf.printf "DAT segment SNAPPY_DAT_T_S\n%!";;

let SNAPPY_DAT_T_S = timed_section "seg.T_S" prove
 (dat_seg_stmt dat_T_s [dat_L_b,"<"; dat_L_s,"<"],
  DAT_T_FROM_CLASSES_TAC (dat_class_split dat_classes)
   [SNAPPY_DAT_VALIDATOR_T_S_LIT; SNAPPY_DAT_VALIDATOR_T_S_LITLONG;
    SNAPPY_DAT_VALIDATOR_T_S_C1; SNAPPY_DAT_VALIDATOR_T_S_C2;
    SNAPPY_DAT_VALIDATOR_T_S_C4]);;

Printf.printf "DAT segment SNAPPY_DECOMPRESSOR_DECOMPRESS_ALL_TAGS_VALIDATOR_GCC12_O2_IMAGE_SUBROUTINE_SAFE\n%!";;

let SNAPPY_DECOMPRESSOR_DECOMPRESS_ALL_TAGS_VALIDATOR_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
 timed_section "seg.MAIN" prove
 (SNAPPY_DECOMPRESSOR_DECOMPRESS_ALL_TAGS_VALIDATOR_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  DAT_MAIN_TAC SNAPPY_DAT_ENTRY SNAPPY_DAT_L_B SNAPPY_DAT_L_S
               SNAPPY_DAT_T_B SNAPPY_DAT_T_S);;

tactic_timing_report "DAT";;
