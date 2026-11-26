(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The unpacking of the hints of polynomial i (mld_sig_unpack_hints) as      *)
(* clang 23 -O3 inlines it into the ML-DSA-65 and ML-DSA-87 versions of      *)
(* verify_internal: the region lemma HINTS44 of inline_verify.ml with omega, *)
(* K, the offsets and the registers as parameters. The code is that of 44    *)
(* with other registers: the index i of the row is in R13 on entry (44: a    *)
(* stack slot) and is copied to another register, the count w of the hints   *)
(* up to polynomial i is in R13, the start s in another register, and the    *)
(* pointer to t1 is saved in a register or a stack slot; the mask of the     *)
(* packing of w1 is loaded into XMM5 after the memset. The loops L1 (the     *)
(* positions after the first) and L2 (the unused bytes of the last           *)
(* polynomial) are those of 44 with these registers.                         *)
(*                                                                           *)
(* The segments of the proof and their tactics are those of 44 (see the      *)
(* comments there); a record hk_params gives the parameters of an instance.  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_verify65.ml";;

type hk_params = {
  hk_fn : string;        (* the function *)
  hk_om : int;           (* omega *)
  hk_k : int;            (* K, the number of polynomials *)
  hk_sh : int;           (* the offset of the hints in the signature *)
  hk_cb : int;           (* the offset of the coefficients from rsp0 *)
  hk_fr : int;           (* the size of the frame from rsp0 with the slots *)
  hk_sigslot : int;      (* the stack slot of the pointer to the signature *)
  hk_entry : string;     (* the label of the start (the exit of caddq) *)
  hk_l1 : int;           (* the offset of the entry of L1 *)
  hk_l1hd : string;      (* the label of the head of L1 *)
  hk_l2 : string;        (* the label of the loop L2 *)
  hk_end : string;       (* the label of the end (the use of the hints) *)
  hk_sreg : string;      (* the register of s *)
  hk_ireg : string;      (* the register of the copy of i *)
  hk_frame : string;     (* the facts that all the segments keep *)
  hk_inv_c : string;     (* the registers at join8 if the hints are ok *)
  hk_post : string;      (* the registers at the end if the hints are ok *)
  hk_mc : string;        (* the registers that the region changes *)
  hk_memc : string;      (* the memory that it changes, besides the hints *)
  hk_c5 : int;           (* the offset of the end of the load of the mask *)
  hk_c5name : string;    (* the layout name of the mask *)
  hk_n1 : int;           (* steps of segment 1a to the branch on i *)
  hk_n2 : int;           (* steps of segment 1a to the test of w *)
  hk_n2a : int;          (* steps of segment 2 to the branch on i *)
};;

let hk_tokens p =
  ["@FN@",p.hk_fn; "@MC@",image_mc; "@OM@",string_of_int p.hk_om;
   "@K@",string_of_int p.hk_k; "@K1@",string_of_int (p.hk_k - 1);
   "@SH@",string_of_int p.hk_sh; "@SH1@",string_of_int (p.hk_sh + 1);
   "@HB@",string_of_int (p.hk_om + p.hk_k);
   "@CB@",string_of_int p.hk_cb; "@FR@",string_of_int p.hk_fr;
   "@SIGSLOT@",string_of_int p.hk_sigslot;
   "@SREG@",p.hk_sreg; "@IREG@",p.hk_ireg;
   "@ENTRY@",p.hk_entry; "@L1HD@",p.hk_l1hd; "@L2@",p.hk_l2; "@END@",p.hk_end;
   "@L1@",string_of_int (layout p.hk_fn + p.hk_l1);
   "@SOM@",string_of_int (p.hk_sh + p.hk_om);
   "@SOM1@",string_of_int (p.hk_sh + p.hk_om - 1);
   "@OM1@",string_of_int (p.hk_om - 1);
   "@C5@",p.hk_c5name];;

let hk_sub p s = subst_tokens (hk_tokens p) s;;
let hk_tm p s = parse_term (hk_sub p s);;

(* ------------------------------------------------------------------------- *)
(* L2: the unused bytes of the last polynomial, from w to omega - 1.         *)
(* ------------------------------------------------------------------------- *)

let HK_L2_STMT p =
  hk_tm p
  "exists f_events.
   forall e sig w pc (b:num->byte).
     aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\ w < @OM@
     ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
               read RIP s = word (pc + @FN@_@L2@) /\\
               read R8 s = sig /\\ read RAX s = word w /\\
               (!j. j < @HB@ ==> read (memory :> bytes8 (word_add sig (word (@SH@ + j)))) s = b j) /\\
               read events s = e)
          (\\s. read RIP s = word (if cl_zeros @OM@ b w then pc + @FN@_join8 else pc + @FN@_join1) /\\
               read R8 s = sig /\\
               (!j. j < @HB@ ==> read (memory :> bytes8 (word_add sig (word (@SH@ + j)))) s = b j) /\\
               (exists e2. read events s = APPEND e2 e /\\ e2 = f_events sig w pc b /\\
                  memaccess_inbounds e2 [word_add sig (word @SH@),@HB@] []))
          (MAYCHANGE [RIP; RAX] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])";;

let HK_L2_TAC p execth =
  let fn = p.hk_fn and om = p.hk_om in
  let omt = mk_small_numeral om in
  let tm = hk_tm p in
  let j8 = mk_small_numeral(layout(fn^"_join8"))
  and j1 = mk_small_numeral(layout(fn^"_join1"))
  and lp = mk_small_numeral(layout(fn^"_"^p.hk_l2)) in
  let pcp n = mk_binop `(+):num->num->num` `pc:num` n in
  let path_end =
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD1_64] THEN
    LOOP_TEST_TAC THEN
    DECIDE_NUM_CONDS_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[ADD_ASSOC] THEN NO_TAC) THEN
    TRY(ASM_REWRITE_TAC[GSYM ADD_ASSOC] THEN NO_TAC) THEN
    PATH_DISCHARGE_TAC in
  let n2 = tm "cl_n2 @OM@ b w" and z2 = tm "cl_zeros @OM@ (b:num->byte) w" in
  CONCRETIZE_F_EVENTS_TAC
   (tm "\\(sig:int64) (w:num) (pc:num) (b:num->byte).
      APPEND (f_ev_epil sig w pc b)
       (APPEND (ENUMERATEL (cl_n2 @OM@ b w)
          (\\p. if p + 1 < cl_n2 @OM@ b w then f_ev_it sig w pc b p
               else if cl_zeros @OM@ b w then f_ev_ok sig w pc b p
               else f_ev_bad sig w pc b p))
        (f_ev_prol sig w pc b)) :(uarch_event)list") THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `sig:int64`; `w:num`; `pc:num`; `b:num->byte`] THEN
  REWRITE_TAC[SOME_FLAGS; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [omt; `b:num->byte`; `w:num`] CL_N2) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN (tm "w + cl_n2 @OM@ b w <= @OM@") ASSUME_TAC THENL
   [ASM_CASES_TAC z2 THEN ASM_MESON_TAC[LE_REFL]; ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC n2 (pcp lp) (mk_cond(z2,pcp j8,pcp j1))
   (tm "\\p s. read R8 s = sig /\\
          (p < cl_n2 @OM@ b w \\/ cl_zeros @OM@ b w ==> read RAX s = word (w + p)) /\\
          (!j. j < @HB@ ==> read (memory :> bytes8 (word_add sig (word (@SH@ + j)))) s = b j)") THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN (tm "w + p < @OM@") ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC (tm "p + 1 < cl_n2 @OM@ b w") THENL
     [FIRST_ASSUM(MP_TAC o SPEC `p:num` o check (fun th ->
        is_forall(concl th) && free_in `cl_n2` (concl th))) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC];
      SUBGOAL_THEN (tm "w + cl_n2 @OM@ b w - 1 = w + p") ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC z2 THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
          lhand(concl th) = z2)) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        SUBGOAL_THEN (tm "w + p + 1 = @OM@") ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC];
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
          lhand(concl th) = mk_neg z2)) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC]] THEN
    (FULL_INIT_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) &&
                             can (find_term ((=) (mk_small_numeral p.hk_sh))) (concl th)
       then MP_TAC(SPEC `w + p:num` th) else NO_TAC) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    VAL_INT64_TAC `w + p:num` THEN
    ALIAS_ASSUME_TAC [hk_sub p "word_add sig (word (1 * (w + p) + @SH@)):int64 = word_add sig (word (@SH@ + w + p))"] THEN
    X86_STEPS_TAC execth (1--2) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_0; VAL_EQ_0]) THEN
    ASM_REWRITE_TAC[] THEN
    (fun g -> if can (find_term (fun t -> t = `~((b:num->byte)(w + p) = word 0)`)) (snd g) ||
                 exists (fun (_,th) -> concl th = `~((b:num->byte)(w + p) = word 0)`) (fst g)
              then ALL_TAC g else X86_STEPS_TAC execth (3--5) g) THEN
    path_end);
    FULL_EXIT0_TAC];;

let PROVE_HK_L2 p =
  let fn = p.hk_fn in
  let execth = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^p.hk_l2), layout (fn^"_join8"))] in
  prove(HK_L2_STMT p, HK_L2_TAC p execth);;

(* ------------------------------------------------------------------------- *)
(* L1: the positions of polynomial i after the first, as L1 of 44 with w in  *)
(* R13 and w - 1 in RCX.                                                     *)
(* ------------------------------------------------------------------------- *)

let HK_L1_STMT p =
  hk_tm p
  "exists f_events.
   forall e sig rsp0 pc (b:num->byte) i.
     aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
     ~glue_suh_early @OM@ b i /\\
     mld_hints_start @OM@ b i + 1 < glue_suh_new @OM@ b i /\\
     nonoverlapping (word_add rsp0 (word @CB@),1024) (word pc,libmldsa_size) /\\
     nonoverlapping (word_add rsp0 (word @CB@),1024) (word_add sig (word @SH@),@HB@)
     ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
               read RIP s = word (pc + @L1@) /\\
               read RSP s = rsp0 /\\ read R8 s = sig /\\
               read RAX s = word (mld_hints_start @OM@ b i) /\\
               read R13 s = word (glue_suh_new @OM@ b i) /\\
               (!j. j < @HB@ ==> read (memory :> bytes8 (word_add sig (word (@SH@ + j)))) s = b j) /\\
               (!q. q < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@CB@ + 4 * q)))) s =
                                glue_suh_h @OM@ b i 1 q) /\\
               read events s = e)
          (\\s. read RIP s = word (if glue_suh_ok1 @OM@ b i then pc + @FN@_join7 else pc + @FN@_join1) /\\
               read RSP s = rsp0 /\\ read R8 s = sig /\\
               read RAX s = word (mld_hints_start @OM@ b i) /\\
               read R13 s = word (glue_suh_new @OM@ b i) /\\
               (!j. j < @HB@ ==> read (memory :> bytes8 (word_add sig (word (@SH@ + j)))) s = b j) /\\
               (glue_suh_ok1 @OM@ b i
                ==> !q. q < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@CB@ + 4 * q)))) s =
                                    mld_unpack_hints @OM@ b i q) /\\
               (exists e2. read events s = APPEND e2 e /\\ e2 = f_events sig rsp0 pc b i /\\
                  memaccess_inbounds e2 [word_add sig (word @SH@),@HB@; word_add rsp0 (word @CB@),1024]
                                        [word_add rsp0 (word @CB@),1024]))
          (MAYCHANGE [RIP; RDX; RSI; RDI; RCX] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(word_add rsp0 (word @CB@),1024)])";;

let HK_L1_TAC p execth =
  let fn = p.hk_fn in
  let tm = hk_tm p and sub = hk_sub p in
  let omt = mk_small_numeral p.hk_om and sht = mk_small_numeral p.hk_sh
  and cbt = mk_small_numeral p.hk_cb in
  let lbl l = mk_small_numeral(layout(fn^"_"^l)) in
  let pcp n = mk_binop `(+):num->num->num` `pc:num` n in
  let s_ = tm "mld_hints_start @OM@ (b:num->byte) i"
  and w_ = tm "glue_suh_new @OM@ (b:num->byte) i" in
  let ok1 = tm "glue_suh_ok1 @OM@ (b:num->byte) i" in
  let n1 = tm "cl_n1 @OM@ (b:num->byte) i" in
  let j = tm "mld_hints_start @OM@ (b:num->byte) i + p + 1" in
  let bnds = [j; s_; tm "glue_suh_new @OM@ (b:num->byte) i - 1"] in
  let is_sh th = is_forall(concl th) && can (find_term ((=) sht)) (concl th) in
  let common_pre =
    FULL_INIT_TAC THEN
    MAP_EVERY (fun t ->
      FIRST_ASSUM(fun th -> if is_sh th then MP_TAC(SPEC t th) else NO_TAC) THEN
      ANTS_TAC THENL [LOCAL_ARITH_TAC; DISCH_TAC])
     [tm "mld_hints_start @OM@ (b:num->byte) i + p"; j] THEN
    VAL_INT64_TAC (tm "mld_hints_start @OM@ (b:num->byte) i + p") THEN
    ALIAS_ASSUME_TAC
     [sub "word_add sig (word (1 * (mld_hints_start @OM@ b i + p) + @SH1@)):int64 = word_add sig (word (@SH@ + mld_hints_start @OM@ b i + p + 1))";
      sub "word_add sig (word (1 * (mld_hints_start @OM@ b i + p) + @SH@)):int64 = word_add sig (word (@SH@ + mld_hints_start @OM@ b i + p))"] THEN
    X86_STEPS_TAC execth (1--4) THEN RIP_DECIDE_TAC bnds THEN
    X86_STEPS_TAC execth (5--6) THEN RIP_DECIDE_TAC bnds in
  let store_tac =
    FIRST_ASSUM(fun th ->
      if is_forall(concl th) && free_in `glue_suh_h` (concl th) then
        ASSUME_TAC(TAC_PROOF(([],subst [j,`j:num`; omt,`om:num`; cbt,`cb:num`]
          `!q. q < 256 /\ ~(q = val((b:num->byte) j))
               ==> read(memory :> bytes32(word_add rsp0 (word(cb + 4 * q)))) s6 =
                   glue_suh_h om b i (p + 1) q`),
          REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]))
      else NO_TAC) THEN
    ASSUME_TAC(SPEC (mk_comb(`b:num->byte`,j)) GLUE_VAL_BYTE) THEN
    ASSUME_TAC(ISPEC (mk_comb(`b:num->byte`,j)) BYTE_ZX2_VAL) THEN
    ALIAS_ASSUME_TAC [sub "word_add rsp0 (word (4 * val ((b:num->byte) (mld_hints_start @OM@ b i + p + 1)) + @CB@)):int64 = word_add rsp0 (word (@CB@ + 4 * val ((b:num->byte) (mld_hints_start @OM@ b i + p + 1))))"] THEN
    X86_STEPS_TAC execth (7--10) THEN RIP_DECIDE_TAC bnds in
  let h_tac =
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GLUE_SUH_H_ADD1] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]] in
  let path_end =
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD1_64] THEN
    REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[GSYM ADD_ASSOC] THEN NO_TAC) THEN
    TRY(ASM_REWRITE_TAC[GSYM ADD_ASSOC] THEN NO_TAC) THEN
    TRY(h_tac THEN NO_TAC) THEN
    TRY(FIRST_X_ASSUM(fun th -> if can (find_term (fun t -> is_const t && fst(dest_const t) = "MAYCHANGE")) (concl th) &&
                                 not(is_imp(concl th)) then MP_TAC th else NO_TAC) THEN
        VAL_BYTE_GEN_TAC THEN DISCH_TAC THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC) THEN
    BYTE_IDX_DISCHARGE_TAC PATH_DISCHARGE_TAC in
  let is_n1_fact th = is_forall(concl th) && free_in `glue_suh_n1` (concl th) &&
                      free_in `val:byte->num` (concl th) in
  CONCRETIZE_F_EVENTS_TAC
   (tm "\\(sig:int64) (rsp0:int64) (pc:num) (b:num->byte) (i:num).
      APPEND (f_ev_epil sig rsp0 pc b i)
       (APPEND (ENUMERATEL (cl_n1 @OM@ b i)
          (\\p. if p + 1 < cl_n1 @OM@ b i then f_ev_it sig rsp0 pc b i p
               else if glue_suh_ok1 @OM@ b i then f_ev_ok sig rsp0 pc b i p
               else f_ev_bad sig rsp0 pc b i p))
        (f_ev_prol sig rsp0 pc b i)) :(uarch_event)list") THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `sig:int64`; `rsp0:int64`; `pc:num`;
                       `b:num->byte`; `i:num`] THEN
  REWRITE_TAC[SOME_FLAGS; fst execth; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [omt; `b:num->byte`; `i:num`] GLUE_SUH_N1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC(SPECL [omt; `b:num->byte`; `i:num`] GLUE_SUH_BOUNDS) THEN
  SUBGOAL_THEN (tm "glue_suh_new @OM@ (b:num->byte) i <= @OM@") ASSUME_TAC THENL
   [UNDISCH_TAC (tm "~glue_suh_early @OM@ (b:num->byte) i") THEN
    REWRITE_TAC[glue_suh_early] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (tm "0 < cl_n1 @OM@ (b:num->byte) i /\\
                mld_hints_start @OM@ b i + cl_n1 @OM@ b i + 1 <= glue_suh_new @OM@ b i /\\
                cl_n1 @OM@ b i <= glue_suh_n1 @OM@ b i")
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[cl_n1] THEN COND_CASES_TAC THENL
     [SUBGOAL_THEN (tm "mld_hints_start @OM@ b i + glue_suh_n1 @OM@ b i = glue_suh_new @OM@ b i")
       MP_TAC THENL [ASM_MESON_TAC[]; ASM_ARITH_TAC];
      FIRST_ASSUM(MP_TAC o C MP (ASSUME (mk_neg ok1)) o
        check (fun th -> is_imp(concl th) && is_neg(lhand(concl th)))) THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN (tm "1 <= glue_suh_new @OM@ (b:num->byte) i") ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_iff(concl th) && lhand(concl th) = ok1
    then ASSUME_TAC(fst(EQ_IMP_RULE th)) else NO_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC n1 (pcp (lbl p.hk_l1hd))
   (mk_cond(ok1,pcp (lbl "join7"),pcp (lbl "join1")))
   (tm "\\p s. read RSP s = rsp0 /\\ read R8 s = sig /\\
          read RAX s = word (mld_hints_start @OM@ b i) /\\
          read R13 s = word (glue_suh_new @OM@ b i) /\\
          read RCX s = word (glue_suh_new @OM@ b i - 1) /\\
          (!j. j < @HB@ ==> read (memory :> bytes8 (word_add sig (word (@SH@ + j)))) s = b j) /\\
          (p < cl_n1 @OM@ b i \\/ glue_suh_ok1 @OM@ b i
           ==> read RDX s = word (mld_hints_start @OM@ b i + p) /\\
               (!q. q < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@CB@ + 4 * q)))) s =
                                glue_suh_h @OM@ b i (p + 1) q))") THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    FULL_INIT_TAC THEN X86_STEPS_TAC execth (1--3) THEN
    RULE_ASSUM_TAC(fun th -> try REWRITE_RULE[MATCH_MP WORD_ADD_M1_64
       (ASSUME (tm "1 <= glue_suh_new @OM@ (b:num->byte) i"))] th with Failure _ -> th) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC (tm "p + 1 < cl_n1 @OM@ b i") THENL
     [FIRST_ASSUM(MP_TAC o SPEC `p:num` o check is_n1_fact) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
      common_pre THEN store_tac THEN path_end;
      ASM_CASES_TAC ok1 THENL
       [SUBGOAL_THEN (tm "mld_hints_start @OM@ b i + cl_n1 @OM@ b i + 1 = glue_suh_new @OM@ b i /\\
                      p + 1 < glue_suh_n1 @OM@ b i") STRIP_ASSUME_TAC THENL
         [SUBGOAL_THEN (tm "mld_hints_start @OM@ b i + glue_suh_n1 @OM@ b i = glue_suh_new @OM@ b i /\\
                        cl_n1 @OM@ b i = glue_suh_n1 @OM@ b i - 1") MP_TAC THENL
           [REWRITE_TAC[cl_n1] THEN ASM_SIMP_TAC[]; ASM_ARITH_TAC];
          ALL_TAC] THEN
        FIRST_ASSUM(MP_TAC o SPEC `p:num` o check is_n1_fact) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
        common_pre THEN store_tac THEN path_end;
        SUBGOAL_THEN (tm "mld_hints_start @OM@ b i + glue_suh_n1 @OM@ b i =
                      mld_hints_start @OM@ b i + p + 1 /\\
                      (mld_hints_start @OM@ b i + glue_suh_n1 @OM@ b i) - 1 =
                      mld_hints_start @OM@ b i + p") STRIP_ASSUME_TAC THENL
         [SUBGOAL_THEN (tm "cl_n1 @OM@ b i = glue_suh_n1 @OM@ b i") MP_TAC THENL
           [REWRITE_TAC[cl_n1] THEN ASM_REWRITE_TAC[]; ASM_ARITH_TAC];
          ALL_TAC] THEN
        FIRST_ASSUM(MP_TAC o C MP (ASSUME (mk_neg ok1)) o
          check (fun th -> is_imp(concl th) && is_neg(lhand(concl th)))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        common_pre THEN X86_STEPS_TAC execth (7--7) THEN path_end]];
    REWRITE_TAC[LT_REFL] THEN FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(DISCH_TAC THEN
        SUBGOAL_THEN (tm "mld_hints_start @OM@ b i + cl_n1 @OM@ b i + 1 = glue_suh_new @OM@ b i")
         ASSUME_TAC THENL
         [SUBGOAL_THEN (tm "mld_hints_start @OM@ b i + glue_suh_n1 @OM@ b i = glue_suh_new @OM@ b i /\\
                        cl_n1 @OM@ b i = glue_suh_n1 @OM@ b i - 1") MP_TAC THENL
           [REWRITE_TAC[cl_n1] THEN ASM_SIMP_TAC[]; ASM_ARITH_TAC];
          ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
          free_in `glue_suh_h` (concl th))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        X_GEN_TAC `q:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `q:num` o check (fun th -> is_forall (concl th) &&
          free_in `glue_suh_h` (concl th))) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC GLUE_SUH_H_FULL THEN ASM_ARITH_TAC THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let PROVE_HK_L1 p =
  let fn = p.hk_fn in
  let execth = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout fn + p.hk_l1, layout (fn^"_"^p.hk_l1hd) + 0x21)] in
  prove(HK_L1_STMT p, HK_L1_TAC p execth);;

(* ------------------------------------------------------------------------- *)
(* The whole region, from the exit of the caddq loop to the use of the       *)
(* hints, or to join1 if they are malformed.                                 *)
(* ------------------------------------------------------------------------- *)

(*** The helpers of the segments of 44 for any omega and offset of the ***)
(*** coefficients                                                       ***)

let VM_ZX_JOIN_HK = WORD_BLAST `word_zx (word_join (x:int128) (y:int128):int256):int128 = y`;;

let HZ_ZX_TAC_HK p =
  MAP_EVERY (fun t -> ASSUME_TAC(MATCH_MP VAL_ZX32_SMALL (ASSUME t)))
    [hk_tm p "mld_hints_start @OM@ (b:num->byte) i < 256";
     hk_tm p "glue_suh_new @OM@ (b:num->byte) i < 256"];;

let HZ_H1_TAC_HK p st =
  let sv = mk_var(st,`:x86state`) in
  let gl = subst [sv,`s:x86state`]
    (hk_tm p "!q. q < 256 ==> read(memory :> bytes32(word_add rsp0 (word(@CB@ + 4 * q)))) s =
                     glue_suh_h @OM@ (b:num->byte) i 1 q") in
  SUBGOAL_THEN gl ASSUME_TAC THENL
   [X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [mk_small_numeral p.hk_om; `b:num->byte`; `i:num`; `0`; `q:num`] GLUE_SUH_H_ADD1) THEN
    REWRITE_TAC[ADD_CLAUSES; GLUE_SUH_H_0] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(ACCEPT_TAC o GSYM)];
    ALL_TAC];;

let HK_OK1_SMALL = prove
 (`!om (b:num->byte) i. ~(mld_hints_start om b i + 1 < glue_suh_new om b i)
                        ==> glue_suh_ok1 om b i`,
  REWRITE_TAC[glue_suh_ok1] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let HK_CL_ZEROS p =
  prove(hk_tm p "!(b:num->byte) w. ~(w < @OM@) ==> cl_zeros @OM@ b w",
        REWRITE_TAC[cl_zeros] THEN ARITH_TAC);;

(* an XMM5 fact (the mask) as a YMM5 fact at the start of a segment *)
let XMM5_TOP_TAC = TRY(XMM_EXISTSTOP_TAC "top5" `YMM5`);;

let HK_STMT p =
  hk_tm p
  ("!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig rsp0 pc (b:num->byte) i t1p.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\ i < @K@ /\\
          ALL (nonoverlapping (rsp0,@FR@))
              [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el);
               (word_add sig (word @SH@),@HB@)] /\\
          ALL (nonoverlapping (word_sub rsp0 (word 8),8))
              [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el);
               (word_add sig (word @SH@),@HB@)]
          ==> ensures x86
               (\\s. bytes_loaded s (word pc) @MC@ /\\
                    read RIP s = word (pc + @FN@_@ENTRY@) /\\
                    read RSP s = rsp0 /\\ read R13 s = word i /\\ read RBX s = t1p /\\
                    read (memory :> bytes64 (word_add rsp0 (word @SIGSLOT@))) s = sig /\\
                    (!j. j < @HB@ ==> read (memory :> bytes8 (word_add sig (word (@SH@ + j)))) s = b j) /\\
                    (read DF s <=> false) /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    read events s = e)
               (\\s. read RIP s = word (if mld_unpack_hints_ok @OM@ @K@ b i
                                       then pc + @FN@_@END@ else pc + @FN@_join1) /\\
                    read RSP s = rsp0 /\\
                    read (memory :> bytes64 (word_add rsp0 (word @SIGSLOT@))) s = sig /\\
                    (!j. j < @HB@ ==> read (memory :> bytes8 (word_add sig (word (@SH@ + j)))) s = b j) /\\
                    (read DF s <=> false) /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    (mld_unpack_hints_ok @OM@ @K@ b i
                     ==> " ^ p.hk_post ^ " /\\
                         read XMM5 s = word 0x000000ff000000ff000000ff000000ff /\\
                         (!q. q < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@CB@ + 4 * q)))) s =
                                          mld_unpack_hints @OM@ b i q)) /\\
                    (exists e2. read events s = APPEND e2 e /\\
                       e2 = f_events rsp0 sig pc b i mf /\\
                       memaccess_inbounds e2
                        [rsp0,@FR@; word_sub rsp0 (word 8),8; word_add sig (word @SH@),@HB@;
                         word(pc + got_memset),8; ea,el; word(pc + @C5@),16]
                        [rsp0,@FR@; word_sub rsp0 (word 8),8]))
               (MAYCHANGE [" ^ p.hk_mc ^ "] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [" ^ p.hk_memc ^ "memory :> bytes(word_add rsp0 (word @CB@),1024);
                           memory :> bytes(word_sub rsp0 (word 8),8)])");;

let HK_TEMPLATE p =
  hk_tm p
  "\\(rsp0:int64) (sig:int64) (pc:num) (b:num->byte) (i:num) (mf:int64).
    APPEND (if mld_unpack_hints_ok @OM@ @K@ b i then f_ev_c rsp0 sig pc b i mf
            else f_ev_cs rsp0 sig pc b i mf)
    (APPEND (if glue_suh_early @OM@ b i \\/ ~glue_suh_ok1 @OM@ b i then f_ev_bs rsp0 sig pc b i mf
             else if i = @K1@ then
               (if glue_suh_new @OM@ b i < @OM@
                then (if cl_zeros @OM@ b (glue_suh_new @OM@ b i) then f_ev_bz rsp0 sig pc b i mf
                      else f_ev_bnz rsp0 sig pc b i mf)
                else f_ev_bw rsp0 sig pc b i mf)
             else f_ev_bn rsp0 sig pc b i mf)
    (APPEND (if glue_suh_early @OM@ b i then f_ev_ms rsp0 sig pc b i mf
             else if mld_hints_start @OM@ b i < glue_suh_new @OM@ b i
             then (if mld_hints_start @OM@ b i + 1 < glue_suh_new @OM@ b i
                   then f_ev_ml rsp0 sig pc b i mf else f_ev_mq rsp0 sig pc b i mf)
             else f_ev_me rsp0 sig pc b i mf)
     (if glue_suh_early @OM@ b i
      then (if 0 < i then (if @OM@ < glue_suh_new @OM@ b i then f_ev_x1 rsp0 sig pc b i mf
                           else f_ev_x2 rsp0 sig pc b i mf)
            else f_ev_x0 rsp0 sig pc b i mf)
      else (if 0 < i then f_ev_p1 rsp0 sig pc b i mf else f_ev_p0 rsp0 sig pc b i mf))))
   :(uarch_event)list";;

let HK_FRAME p =
  hk_sub p ("read RSP s = rsp0 /\\ " ^ p.hk_frame ^ " /\\
   read (memory :> bytes64 (word_add rsp0 (word @SIGSLOT@))) s = sig /\\
   (!j. j < @HB@ ==> read (memory :> bytes8 (word_add sig (word (@SH@ + j)))) s = b j) /\\
   (read DF s <=> false) /\\
   read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
   read (memory :> bytes(ea,el)) s = ev");;

let HK_INV_A p = hk_tm p ("\\s. " ^ HK_FRAME p ^ " /\\
   (~glue_suh_early @OM@ b i ==>
      read @SREG@ s = word (mld_hints_start @OM@ b i) /\\
      read R13 s = word (glue_suh_new @OM@ b i) /\\
      (!q. q < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@CB@ + 4 * q)))) s = word 0))");;

let HK_INV_B p = hk_tm p ("\\s. " ^ HK_FRAME p ^ " /\\
   (~(glue_suh_early @OM@ b i \\/ ~glue_suh_ok1 @OM@ b i) ==>
      read R13 s = word (glue_suh_new @OM@ b i) /\\ read R8 s = sig /\\
      read XMM5 s = word 0x000000ff000000ff000000ff000000ff /\\
      (!q. q < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@CB@ + 4 * q)))) s =
                       mld_unpack_hints @OM@ b i q))");;

let HK_INV_C p = hk_tm p ("\\s. " ^ HK_FRAME p ^ " /\\
   (mld_unpack_hints_ok @OM@ @K@ b i ==>
      " ^ p.hk_inv_c ^ "read R8 s = sig /\\
      read XMM5 s = word 0x000000ff000000ff000000ff000000ff /\\
      (!q. q < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@CB@ + 4 * q)))) s =
                       mld_unpack_hints @OM@ b i q))");;

let HK_SETUP_TAC p l1th l2th t1a t1b t2 t3 =
  let fn = p.hk_fn in
  let tm = hk_tm p in
  let lbl l = mk_small_numeral(layout(fn^"_"^l)) in
  let pcp n = mk_binop `(+):num->num->num` `pc:num` n in
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_full_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC l1th "H_L1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC l2th "H_L2" THEN
  CONCRETIZE_F_EVENTS_TAC (HK_TEMPLATE p) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `sig:int64`; `rsp0:int64`; `pc:num`;
    `b:num->byte`; `i:num`; `t1p:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  STRIP_ASSUME_TAC(SPECL [mk_small_numeral p.hk_om; `b:num->byte`; `i:num`] GLUE_SUH_BOUNDS) THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   (mk_cond(tm "mld_unpack_hints_ok @OM@ @K@ b i",pcp (lbl "join8"),pcp (lbl "join1")))
   (HK_INV_C p) THEN CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC
     (mk_cond(tm "glue_suh_early @OM@ b i \\/ ~glue_suh_ok1 @OM@ b i",pcp (lbl "join1"),pcp (lbl "join7")))
     (HK_INV_B p) THEN CONJ_TAC THENL
     [ENSURES_EVENTS_SEQUENCE_TAC
       (mk_cond(tm "glue_suh_early @OM@ b i",pcp (lbl "join1"),pcp (lbl "after_memset_7")))
       (HK_INV_A p) THEN CONJ_TAC THENL [t1a; t1b];
      t2];
    t3];;

let HK_EQS_TAC p =
  let tm = hk_tm p in
  SUBGOAL_THEN (tm "val((b:num->byte)(@OM@ + i)) = glue_suh_new @OM@ b i") ASSUME_TAC THENL
   [REWRITE_TAC[glue_suh_new]; ALL_TAC] THEN
  SUBGOAL_THEN (tm "0 < i ==> val((b:num->byte)(@OM1@ + i)) = mld_hints_start @OM@ b i") ASSUME_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[mld_hints_start] THEN
    ASM_SIMP_TAC[ARITH_RULE (tm "0 < i ==> ~(i = 0) /\\ @OM@ + (i - 1) = @OM1@ + i")];
    ALL_TAC] THEN
  SUBGOAL_THEN (tm "i = 0 ==> mld_hints_start @OM@ (b:num->byte) i = 0") ASSUME_TAC THENL
   [SIMP_TAC[mld_hints_start]; ALL_TAC];;

let HK_RIP_TAC p =
  let isrip th = let c = concl th in
    is_eq c && (can (term_match [] `read RIP s`) (lhs c) ||
                can (term_match [] `read events s`) (lhs c)) in
  let omb = ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral p.hk_om) `256`) in
  RULE_ASSUM_TAC(fun th -> if isrip th then
    SIMP_RULE[CF32_BYTE; ZF32_BYTE; omb]
      (REWRITE_RULE[BYTE_ZX1_VAL]
        (REWRITE_RULE[GLUE_CF_LEMMA; GLUE_ZF_LEMMA] (REWRITE_RULE[ZX3_BYTE32] th))) else th) THEN
  HZ_RIP0_TAC;;

(* Segment 1a: from the exit of caddq to after the memset, or to join1 *)
let HK_S1A_TAC p execth =
  let tm = hk_tm p and sub = hk_sub p in
  let sht = mk_small_numeral p.hk_sh in
  let n1 = p.hk_n1 and n2 = p.hk_n2 in
  let allowed = ref [`rsp0:int64`; `sig:int64`; `pc:num`; `b:num->byte`; `i:num`; `mf:int64`] in
  let fin =
    RULE_ASSUM_TAC(REWRITE_RULE[BYTE_ZX2_WORD]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[BYTE_ZX2_WORD] THEN
    REWRITE_TAC[WORD_VAL_ADD_64; GSYM ADD_ASSOC] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    REPEAT CONJ_TAC THEN
    TRY(DISCH_TAC THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
    PATH_DISCHARGE_TAC in
  let memset_path n =
    X86_STEPS_TAC execth ((n+1)--(n+2)) THEN HK_RIP_TAC p THEN
    X86_STEPS_TAC execth ((n+3)--(n+6)) THEN HZ_MEMSET_TAC execth allowed (n+6) in
  let early = tm "glue_suh_early @OM@ (b:num->byte) i" in
  FULL_INIT_TAC THEN HK_EQS_TAC p THEN
  SUBGOAL_THEN (tm "nonoverlapping (word_add rsp0 (word @CB@):int64,1024) (word_sub rsp0 (word 8),8)")
   ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_sub (x:int64) y = word_add x (word_neg y)`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[nonoverlapping; DIMINDEX_64] THEN
    MATCH_MP_TAC(REWRITE_RULE[DIMINDEX_64] (INST_TYPE [`:64`,`:N`] NONOVERLAPPING_MODULO_OFFSET_BOTH)) THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MAP_EVERY (fun t ->
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) sht)) (concl th)
       then MP_TAC(SPEC t th) else NO_TAC) THEN
    ANTS_TAC THENL [LOCAL_ARITH_TAC; DISCH_TAC]) [tm "@OM@ + i"; tm "@OM1@ + i"] THEN
  VAL_INT64_TAC `i:num` THEN
  ALIAS_ASSUME_TAC [sub "word_add sig (word (1 * i + @SOM@)):int64 = word_add sig (word (@SH@ + @OM@ + i))";
                    sub "word_add sig (word (1 * i + @SOM1@)):int64 = word_add sig (word (@SH@ + @OM1@ + i))"] THEN
  X86_STEPS_TAC execth (1--n1) THEN
  ASM_CASES_TAC `0 < i` THEN RIP_DECIDE_TAC [] THEN
  TRY(FIRST_ASSUM(fun th0 -> if concl th0 = `0 < i` then
        FIRST_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `0 < i`
          then ASSUME_TAC(MP th th0) else NO_TAC) else NO_TAC)) THEN
  (ASM_CASES_TAC (tm "@OM@ < glue_suh_new @OM@ (b:num->byte) i") THENL
   [SUBGOAL_THEN early ASSUME_TAC THENL
     [ASM_REWRITE_TAC[glue_suh_early]; ALL_TAC] THEN
    X86_STEPS_TAC execth ((n1+1)--n2) THEN HK_RIP_TAC p THEN
    (fun g -> if exists (fun (_,th) -> concl th = `0 < i`) (fst g)
              then X86_STEPS_TAC execth ((n2+1)--(n2+1)) g else ALL_TAC g) THEN
    fin;
    X86_STEPS_TAC execth ((n1+1)--n2) THEN HK_RIP_TAC p THEN
    (fun g -> if exists (fun (_,th) -> concl th = `0 < i`) (fst g)
     then
       (ASM_CASES_TAC (tm "glue_suh_new @OM@ (b:num->byte) i < mld_hints_start @OM@ b i") THENL
         [SUBGOAL_THEN early ASSUME_TAC THENL
           [ASM_REWRITE_TAC[glue_suh_early]; ALL_TAC] THEN
          X86_STEPS_TAC execth ((n2+1)--(n2+2)) THEN HK_RIP_TAC p THEN fin;
          SUBGOAL_THEN (mk_neg early) ASSUME_TAC THENL
           [ASM_REWRITE_TAC[glue_suh_early]; ALL_TAC] THEN
          memset_path n2 THEN fin]) g
     else
       (SUBGOAL_THEN (tm "mld_hints_start @OM@ (b:num->byte) i = 0") ASSUME_TAC THENL
         [FIRST_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `i = 0`
                                then MATCH_MP_TAC th else NO_TAC) THEN
          LOCAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN (mk_neg early) ASSUME_TAC THENL
         [ASM_REWRITE_TAC[glue_suh_early] THEN LOCAL_ARITH_TAC; ALL_TAC] THEN
        memset_path n2 THEN fin) g)]);;

(* The mask of the packing of w1 as an XMM5 fact, from the YMM5 fact of the
   load *)
let HK_XMM5_TAC =
  REWRITE_TAC[XMM5; READ_COMPONENT_COMPOSE; READ_ZEROTOP_128] THEN
  ASM_REWRITE_TAC[VM_ZX_JOIN_HK] THEN CONV_TAC WORD_REDUCE_CONV;;

(* Segment 1b: after the memset, the first hint and L1, to join7 *)
let HK_S1B_TAC p execth =
  let tm = hk_tm p and sub = hk_sub p in
  let sht = mk_small_numeral p.hk_sh and cbt = mk_small_numeral p.hk_cb in
  let s_ = tm "mld_hints_start @OM@ (b:num->byte) i" in
  let bs_ = tm "(b:num->byte)(mld_hints_start @OM@ b i)" in
  let allowed = [`rsp0:int64`; `sig:int64`; `pc:num`; `b:num->byte`; `i:num`; `mf:int64`] in
  let zx2 = tm "word_zx (word_zx (word (mld_hints_start @OM@ (b:num->byte) i):int64):int32):int64 =
             word (mld_hints_start @OM@ b i)" in
  let early = tm "glue_suh_early @OM@ (b:num->byte) i" in
  let ok1 = tm "glue_suh_ok1 @OM@ (b:num->byte) i" in
  let c5 = IMAGE_CONST_RULE_FOR mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
             (layout p.hk_c5name) 128 in
  let ok1_tac =
    SUBGOAL_THEN ok1 ASSUME_TAC THENL
     [MATCH_MP_TAC HK_OK1_SMALL THEN LOCAL_ARITH_TAC; ALL_TAC] in
  let fin_b =
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(X_GEN_TAC `q:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
    TRY(HK_XMM5_TAC THEN NO_TAC) THEN
    TRY(HZ_MAYCHANGE_TAC THEN NO_TAC) THEN
    BYTE_IDX_DISCHARGE_TAC SEG_DISCHARGE_TAC in
  let start pre =
    FULL_INIT_TAC THEN pre THEN
    YMM_GHOST_TAC `s0:x86state` ["YMM5","ymm5_hk"] THEN
    X86_STEPS_TAC execth (1--2) THEN
    IMAGE_RIPREL_TAC c5 (layout p.hk_fn + p.hk_c5) THEN
    X86_STEPS_TAC execth (3--4) THEN HZ_ZX_TAC_HK p THEN HZ_B_RIP_TAC in
  ASM_CASES_TAC early THENL
   [HZ_SKIP_TAC [early];
    REWRITE_TAC[ASSUME (mk_neg early)] THEN
    MP_TAC(REWRITE_RULE[glue_suh_early; DE_MORGAN_THM] (ASSUME (mk_neg early))) THEN STRIP_TAC THEN
    ASM_CASES_TAC (tm "mld_hints_start @OM@ (b:num->byte) i < glue_suh_new @OM@ b i") THENL
     [start
       (ASSUME_TAC(MATCH_MP WORD_ZX2_SMALL (ASSUME (tm "mld_hints_start @OM@ (b:num->byte) i < 256"))) THEN
        FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) sht)) (concl th)
            then MP_TAC(SPEC s_ th) else NO_TAC) THEN
        ANTS_TAC THENL [LOCAL_ARITH_TAC; DISCH_TAC] THEN
        VAL_INT64_TAC s_ THEN
        ALIAS_ASSUME_TAC [sub "word_add sig (word (1 * mld_hints_start @OM@ b i + @SH@)):int64 = word_add sig (word (@SH@ + mld_hints_start @OM@ b i))"]) THEN
      X86_STEPS_TAC execth (5--5) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME zx2]) THEN
      X86_STEPS_TAC execth (6--6) THEN
      FIRST_ASSUM(fun th ->
        if is_forall(concl th) && can (find_term ((=) cbt)) (concl th) &&
           not(is_imp(snd(dest_forall(concl th))) && is_conj(lhand(snd(dest_forall(concl th))))) then
          ASSUME_TAC(TAC_PROOF(([],
            subst [cbt,`cb:num`; s_,`st:num`]
            `!q. q < 256 /\ ~(q = val((b:num->byte) st))
                 ==> read(memory :> bytes32(word_add rsp0 (word(cb + 4 * q)))) s6 = word 0`),
            REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]))
        else NO_TAC) THEN
      ASSUME_TAC(SPEC bs_ GLUE_VAL_BYTE) THEN
      ASSUME_TAC(ISPEC bs_ BYTE_ZX2_VAL) THEN
      ALIAS_ASSUME_TAC [sub "word_add rsp0 (word (4 * val ((b:num->byte) (mld_hints_start @OM@ b i)) + @CB@)):int64 = word_add rsp0 (word (@CB@ + 4 * val ((b:num->byte) (mld_hints_start @OM@ b i))))"] THEN
      X86_STEPS_TAC execth (7--10) THEN HZ_H1_TAC_HK p "s10" THEN
      ASSUME_TAC(MATCH_MP INC32_VAL (ASSUME (tm "mld_hints_start @OM@ (b:num->byte) i < 256"))) THEN
      ASM_CASES_TAC (tm "mld_hints_start @OM@ (b:num->byte) i + 1 < glue_suh_new @OM@ b i") THEN
      HZ_B_RIP_TAC THENL
       [FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_L1"
         [`sig:int64`; `rsp0:int64`; `pc:num`; `b:num->byte`; `i:num`] allowed 11 THEN
        ASM_CASES_TAC ok1 THENL
         [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = ok1
             then ASSUME_TAC(MP th (ASSUME ok1)) else NO_TAC) THEN
          fin_b;
          fin_b];
        ok1_tac THEN
        SUBGOAL_THEN (tm "!q. mld_unpack_hints @OM@ (b:num->byte) i q = glue_suh_h @OM@ b i 1 q")
         ASSUME_TAC THENL
         [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC GLUE_SUH_H_FULL THEN LOCAL_ARITH_TAC;
          ALL_TAC] THEN
        fin_b];
      start ALL_TAC THEN
      ok1_tac THEN
      SUBGOAL_THEN (tm "!q. mld_unpack_hints @OM@ (b:num->byte) i q = word 0") ASSUME_TAC THENL
       [GEN_TAC THEN
        MP_TAC(SPECL [mk_small_numeral p.hk_om; `b:num->byte`; `i:num`; `0`; `q:num`] GLUE_SUH_H_FULL) THEN
        REWRITE_TAC[GLUE_SUH_H_0; ADD_CLAUSES] THEN
        ANTS_TAC THENL [LOCAL_ARITH_TAC; SIMP_TAC[]];
        ALL_TAC] THEN
      fin_b]];;

(* Segment 2: from join7, L2 for i = K - 1 and w < omega, to join8 *)
let HK_S2_TAC p execth =
  let tm = hk_tm p in
  let n = p.hk_n2a in
  let c = tm "glue_suh_early @OM@ (b:num->byte) i \\/ ~glue_suh_ok1 @OM@ b i" in
  let ok = tm "mld_unpack_hints_ok @OM@ @K@ (b:num->byte) i" in
  let w_ = tm "glue_suh_new @OM@ (b:num->byte) i" in
  let zw = tm "cl_zeros @OM@ (b:num->byte) (glue_suh_new @OM@ b i)" in
  let omb = ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral p.hk_om) `256`) in
  let allowed = [`rsp0:int64`; `sig:int64`; `pc:num`; `b:num->byte`; `i:num`; `mf:int64`] in
  let fin =
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(X_GEN_TAC `q:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
    TRY(HK_XMM5_TAC THEN NO_TAC) in
  let ik = tm "i = @K1@" in
  let i3 = SUBGOAL_THEN ik ASSUME_TAC THENL [LOCAL_ARITH_TAC; ALL_TAC] in
  let k1t = mk_small_numeral (p.hk_k - 1) in
  ASM_CASES_TAC c THENL
   [SUBGOAL_THEN (mk_neg ok) ASSUME_TAC THENL
     [UNDISCH_TAC c THEN REWRITE_TAC[GLUE_SUH_OK] THEN CONV_TAC TAUT; ALL_TAC] THEN
    HZ_SKIP_TAC [c; mk_neg ok];
    REWRITE_TAC[ASSUME (mk_neg c)] THEN
    MP_TAC(REWRITE_RULE[DE_MORGAN_THM] (ASSUME (mk_neg c))) THEN STRIP_TAC THEN
    ASM_CASES_TAC (tm "i < @K1@") THENL
     [SUBGOAL_THEN (mk_neg ik) ASSUME_TAC THENL [LOCAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN ok ASSUME_TAC THENL
       [REWRITE_TAC[GLUE_SUH_OK] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FULL_INIT_TAC THEN XMM5_TOP_TAC THEN
      X86_STEPS_TAC execth (1--n) THEN RIP_DECIDE_TAC [`i:num`; k1t] THEN
      fin THEN SEG_DISCHARGE_TAC;
      SUBGOAL_THEN (mk_iff(ok, zw)) ASSUME_TAC THENL
       [REWRITE_TAC[GLUE_SUH_OK] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        SUBGOAL_THEN ik (fun th -> REWRITE_TAC[EQT_INTRO th]) THENL
         [LOCAL_ARITH_TAC; REWRITE_TAC[glue_suh_zeros; cl_zeros]];
        ALL_TAC] THEN
      FIRST_ASSUM(fun th -> if is_iff(concl th) && lhand(concl th) = ok
                            then REWRITE_TAC[th] else NO_TAC) THEN
      FULL_INIT_TAC THEN XMM5_TOP_TAC THEN
      ASSUME_TAC(MATCH_MP VAL_ZX8_SMALL (ASSUME (tm "glue_suh_new @OM@ (b:num->byte) i < 256"))) THEN
      ASSUME_TAC(MATCH_MP WORD_ZX2_SMALL (ASSUME (tm "glue_suh_new @OM@ (b:num->byte) i < 256"))) THEN
      X86_STEPS_TAC execth (1--n) THEN RIP_DECIDE_TAC [`i:num`; k1t] THEN
      X86_STEPS_TAC execth ((n+1)--(n+2)) THEN
      W(fun (asl,w) ->
        let zths = filter (fun th ->
            can (term_match [] `val(word_zx (word n:int64):byte) = n`) (concl th)) (map snd asl) in
        RIP_REWRITE_TAC [WORD_VAL_MOD_256] THEN
        RULE_ASSUM_TAC(fun th ->
          if is_eq(concl th) && can (term_match [] `read RIP s`) (lhs(concl th))
          then SIMP_RULE[CF8_NUM; omb] th else th) THEN
        RIP_REWRITE_TAC zths) THEN
      ASM_CASES_TAC (tm "glue_suh_new @OM@ (b:num->byte) i < @OM@") THEN
      RIP_DECIDE_TAC [] THENL
       [X86_STEPS_TAC execth ((n+3)--(n+4)) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WORD_ZX2_SMALL
          (ASSUME (tm "glue_suh_new @OM@ (b:num->byte) i < 256"))]) THEN
        FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_L2"
         [`sig:int64`; w_; `pc:num`; `b:num->byte`] allowed (n+5) THEN
        ASM_CASES_TAC zw THEN
        fin THEN i3 THEN SEG_DISCHARGE_TAC;
        SUBGOAL_THEN zw ASSUME_TAC THENL
         [MATCH_MP_TAC (HK_CL_ZEROS p) THEN LOCAL_ARITH_TAC; ALL_TAC] THEN
        fin THEN i3 THEN SEG_DISCHARGE_TAC]]];;

(* Segment 3: from join8 to the use of the hints *)
let HK_S3_TAC p execth =
  let ok = hk_tm p "mld_unpack_hints_ok @OM@ @K@ (b:num->byte) i" in
  ASM_CASES_TAC ok THENL
   [REWRITE_TAC[ASSUME ok] THEN FULL_INIT_TAC THEN XMM5_TOP_TAC THEN
    X86_STEPS_TAC execth (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(X_GEN_TAC `q:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
    TRY(HK_XMM5_TAC THEN NO_TAC) THEN
    SEG_DISCHARGE_TAC;
    HZ_SKIP_TAC [mk_neg ok]];;

let PROVE_HK p =
  let fn = p.hk_fn in
  let mc = mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc in
  let ex1a = X86_MK_EXEC_RANGES_RULE mc
    [(layout (fn^"_"^p.hk_entry), layout (fn^"_after_memset_7") + 0x13);
     layout_range "plt_memset"]
  and ex1b = X86_MK_EXEC_RANGES_RULE mc
    [(layout (fn^"_after_memset_7"), layout (fn^"_join7"))]
  and ex2 = X86_MK_EXEC_RANGES_RULE mc
    [(layout (fn^"_join7"), layout (fn^"_"^p.hk_l2))]
  and ex3 = X86_MK_EXEC_RANGES_RULE mc
    [(layout (fn^"_join8"), layout (fn^"_join8") + 0x19)] in
  let l1th = PROVE_HK_L1 p and l2th = PROVE_HK_L2 p in
  prove(HK_STMT p,
        HK_SETUP_TAC p l1th l2th (HK_S1A_TAC p ex1a) (HK_S1B_TAC p ex1b)
          (HK_S2_TAC p ex2) (HK_S3_TAC p ex3));;
