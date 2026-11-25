(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof of CompressFragment (compress_fragment_spec.ml): the entry to   *)
(* the first cut point and the segments between the cut points               *)
(* (stated in compress_fragment_seg*_spec.ml and proved, as jobs of their  *)
(* own, in compress_fragment_seg*_proof.ml) combined by                     *)
(* ENSURES_MEASURE_INDUCT, the potential of the model state decreasing at   *)
(* every segment, with X19, X29 and SP restored at the return.              *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_lib.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_seg15_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_seg2_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_seg4_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_seg6_spec.ml";;
needs "arm/proofs/heap_plt.ml";;

let snappy_cstate_CASES = prove_cases_thm snappy_cstate_INDUCT;;

(* ------------------------------------------------------------------------- *)
(* The frame of the segments is idempotent.                                  *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_CF1_FRAME_IDEM_STMT = parse_term
  ("!(inp:byte list) op table stackpointer. (" ^ snappy_cf1_frame_str ^ ") ,, (" ^
   snappy_cf1_frame_str ^ ") = (" ^ snappy_cf1_frame_str ^ ")");;
let SNAPPY_CF1_FRAME_IDEM = prove
 (SNAPPY_CF1_FRAME_IDEM_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  MAYCHANGE_IDEMPOT_TAC);;

(* ------------------------------------------------------------------------- *)
(* All the segments, by the phase of the model state at the cut point.      *)
(* ------------------------------------------------------------------------- *)

let snappy_cf1_segments_stmt extra dn = parse_term
  ("!pc src (inp:byte list) op table stackpointer x19 x29 ra rw ea el ev imp e n.
     " ^ extra ^ snappy_cf1_hyps_str ^ "
     ==> ensures arm
          (\\s. snappy_cf1_cut pc src inp op table stackpointer x19 x29 ra rw ea el ev e n s)
          (\\s. " ^ dn ^ " s \\/
               ?m. m < n /\\
                   snappy_cf1_cut pc src inp op table stackpointer x19 x29 ra rw ea el ev e m s)
          (" ^ snappy_cf1_frame_str ^ ")");;

let SNAPPY_CF1_SEGMENTS_STMT =
  snappy_cf1_segments_stmt snappy_cf1_memcpy_str snappy_cf1_done_str;;
let SNAPPY_CF1_SEGMENTS_SAFE_STMT =
  snappy_cf1_segments_stmt snappy_cf1_memcpy_safe_str snappy_cf1_done_safe_str;;

(* The segment of phase p from the case of the model state; dn the end of    *)
(* the segments that are stated for any end D.                               *)

let SNAPPY_CF1_SEG_DISPATCH_TAC (p:int) (dn:term option) (th:thm) =
  ASM_CASES_TAC (mk_eq(`ph:num`,mk_small_numeral p)) THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL ((match dn with Some d -> [d] | None -> []) @
                  [`pc:num`; `src:int64`; `inp:byte list`; `op:int64`; `table:int64`;
                  `stackpointer:int64`; `x19:int64`; `x29:int64`; `ra:int64`;
                  `rw:num`; `ea:int64`; `el:num`; `ev:num`; `imp:string->int64`;
                  `e:uarch_event list`;
                  `k:num`; `ip:num`; `ne:num`; `sk:num`; `c:num`; `x:num`;
                  `t1:num->num`; `t2:num->num`; `out:byte list`]) th) THEN
    ASM_REWRITE_TAC[ensures] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC];;

let SNAPPY_CF1_SEGMENTS_TAC (dn:term) (seg5:thm) =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ensures] THEN
  X_GEN_TAC `s:armstate` THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[snappy_cf1_cut]) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
  MP_TAC(ISPEC `snappy_crun (snappy_cf1_step inp) k (snappy_cf1_init inp)`
    snappy_cstate_CASES) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`ph:num`; `ip:num`; `ne:num`; `sk:num`; `c:num`; `x:num`;
                       `t1:num->num`; `t2:num->num`; `out:byte list`] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN SUBST1_TAC th) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  SNAPPY_CF1_SEG_DISPATCH_TAC 1 (Some dn) SNAPPY_CF1_SEG1 THEN
  SNAPPY_CF1_SEG_DISPATCH_TAC 2 (Some dn) SNAPPY_CF1_SEG2 THEN
  SNAPPY_CF1_SEG_DISPATCH_TAC 4 (Some dn) SNAPPY_CF1_SEG4 THEN
  SNAPPY_CF1_SEG_DISPATCH_TAC 5 None seg5 THEN
  SNAPPY_CF1_SEG_DISPATCH_TAC 6 (Some dn) SNAPPY_CF1_SEG6 THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "snappy_cf1_mach"
    with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[snappy_cf1_mach; snappy_phase];;

let SNAPPY_CF1_SEGMENTS = prove
 (SNAPPY_CF1_SEGMENTS_STMT,
  SNAPPY_CF1_SEGMENTS_TAC
   `snappy_cf1_done src inp op stackpointer x19 x29 ra` SNAPPY_CF1_SEG5);;

let SNAPPY_CF1_SEGMENTS_SAFE = prove
 (SNAPPY_CF1_SEGMENTS_SAFE_STMT,
  SNAPPY_CF1_SEGMENTS_TAC
   `snappy_cf1_done_safe pc src inp op table stackpointer x19 x29 ra ea el e`
   SNAPPY_CF1_SEG5_SAFE);;

(* ------------------------------------------------------------------------- *)
(* The theorems: _SAFE, and _CORRECT from the same proof with memcpy's       *)
(* correctness contract and the events of the call as a variable, which is   *)
(* then dropped (the segments keep the events in any case; only the end of   *)
(* emit_remainder, after memcpy, differs).                                   *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_PRESERVED_TAC pname ctm =
  MATCH_MP_TAC(ISPEC ctm ENSURES_MAYCHANGE_PRESERVED) THEN
  CONJ_TAC THENL [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV; ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_PRESERVED_KEEP_TAC;
    REWRITE_TAC[GSYM CONJ_ASSOC; GSYM SEQ_ASSOC] THEN
    W(fun (asl,w) -> X_GEN_TAC(mk_var(pname,type_of(fst(dest_forall w)))))];;

let SNAPPY_CF1_TOP_TAC (safe:bool) =
  let dn = if safe then
    `\s. snappy_cf1_done_safe pc src inp op table stackpointer x19 x29
           returnaddress ea el e s`
   else `\s. snappy_cf1_done src inp op stackpointer x19 x29 returnaddress s` in
  let segs = if safe then SNAPPY_CF1_SEGMENTS_SAFE else SNAPPY_CF1_SEGMENTS in
  MAP_EVERY X_GEN_TAC [`e:uarch_event list`; `src:int64`; `inp:byte list`;
    `op:int64`; `table:int64`;
    `pc:num`; `imp:string->int64`; `ea:int64`; `el:num`; `ev:num`; `rw:num`;
    `stackpointer:int64`; `returnaddress:int64`] THEN
  DISCH_TAC THEN
  SNAPPY_PRESERVED_TAC "x19" `X19` THEN SNAPPY_PRESERVED_TAC "x29" `X29` THEN
  MATCH_MP_TAC(ISPECL [`SP`; `stackpointer:int64`]
    ENSURES_MAYCHANGE_EXISTING_PRESERVED) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV;
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_PRESERVED_KEEP_TAC;
    SIMP_TAC[];
    REWRITE_TAC[GSYM SEQ_ASSOC]] THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC `\s. ?n. snappy_cf1_cut pc src inp op table stackpointer x19 x29
                        returnaddress rw ea el ev e n s` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SNAPPY_CF1_FRAME_IDEM];
    MP_TAC(SPECL [`pc:num`; `src:int64`; `inp:byte list`; `op:int64`;
                  `table:int64`; `stackpointer:int64`; `x19:int64`; `x29:int64`;
                  `returnaddress:int64`; `rw:num`; `ea:int64`; `el:num`;
                  `ev:num`; `imp:string->int64`; `e:uarch_event list`]
      SNAPPY_CF1_ENTRY) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC dn THEN
  CONJ_TAC THENL [REWRITE_TAC[snappy_cf1_done_safe; snappy_cf1_done;
                              snappy_cf1_ev; C_RETURN] THEN MESON_TAC[];
                  ALL_TAC] THEN
  W(fun (asl,w) ->
    let fr = rand w in
    MP_TAC(BETA_RULE(ISPECL
     [`arm`;
      `\n s. snappy_cf1_cut pc src inp op table stackpointer x19 x29
               returnaddress rw ea el ev e n s`;
      dn; fr]
     ENSURES_MEASURE_INDUCT))) THEN
  REWRITE_TAC[SNAPPY_CF1_FRAME_IDEM] THEN
  ANTS_TAC THENL
   [GEN_TAC THEN
    MP_TAC(SPECL [`pc:num`; `src:int64`; `inp:byte list`; `op:int64`;
                  `table:int64`; `stackpointer:int64`; `x19:int64`; `x29:int64`;
                  `returnaddress:int64`; `rw:num`; `ea:int64`; `el:num`;
                  `ev:num`; `imp:string->int64`; `e:uarch_event list`; `n:num`]
      segs) THEN
    ASM_REWRITE_TAC[ETA_AX];
    REWRITE_TAC[ensures] THEN MESON_TAC[]];;

let SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SNAPPY_CF1_TOP_TAC true);;

(* The correctness statement with the events of the call as a variable.     *)

let SNAPPY_CF1_CORRECT_EVENTS = prove
 (let tm = SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT in
  let vs,bod = strip_forall tm in
  let hyp,ens = dest_imp bod in
  let [arm;pre;post;fr] = snd(strip_comb ens) in
  let sv,pb = dest_abs pre in
  let e = `e:uarch_event list` in
  let pre' = mk_abs(sv,mk_conj(pb,mk_eq(mk_comb(`read events`,sv),e))) in
  let ens' = list_mk_comb(fst(strip_comb ens),[arm;pre';post;fr]) in
  list_mk_forall(e::vs,mk_imp(hyp,ens')),
  SNAPPY_CF1_TOP_TAC false);;

let SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  ENSURES_DROP_EVENTS_TAC SNAPPY_CF1_CORRECT_EVENTS);;
