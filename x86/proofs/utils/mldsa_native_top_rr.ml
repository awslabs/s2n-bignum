(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof of the FULL theorems for mld_sign_pk_from_sk of the builds with *)
(* MLD_CONFIG_REDUCE_RAM (PFS_RR_FULL_TAC), as PFS_FULL_TAC of               *)
(* utils/mldsa_native_top.ml does for the default builds, from whose code    *)
(* theirs differs only in the frame of mld_compute_pack_t0_t1: these builds  *)
(* call no function of the C library, so that there is no contract for one,  *)
(* and mld_compute_pack_t0_t1 computes t with the lazy matrix product        *)
(* (mld_compute_t_lazy of common/mldsa_native_polyvec_lazy.ml), whose packed *)
(* t1 and t0 are those of mld_pk_from_sk_t by the assumed lemma              *)
(* MLD_PK_FROM_SK_T_LAZY_XX of the build's lazy_spec.ml, given to the        *)
(* tactic. The parts of the proof after the computation of t (the loop over  *)
(* the chunks of t0 and the comparisons, the hash and the two paths to the   *)
(* return) are those of utils/mldsa_native_top.ml, PFS_BODY_TAC and          *)
(* PFS_EXIT_TAC, whose list of the variables allowed in the events,          *)
(* pfs_allowed, has one for the address of a library function, which does    *)
(* not occur here.                                                           *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_top.ml";;
needs "common/mldsa_native_polyvec_lazy.ml";;

(* ------------------------------------------------------------------------- *)
(* The facts of a byte string from the lazy t, turned into those from the    *)
(* default one by an equation of the two on its bytes.                       *)
(* ------------------------------------------------------------------------- *)

let PFS_RR_LAZY_IMP = prove
 (`!n (a:num->byte) b.
     (!j. j < n ==> a j = b j)
     ==> !x. (!j. j < n ==> x j = a j) ==> (!j. j < n ==> x j = b j)`,
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The setup and the part up to the loop over the chunks of t0, as in        *)
(* utils/mldsa_native_top.ml but with no contract for a library function:    *)
(* the template of the events and the allowed variables have no address of   *)
(* one, and the regions apart from the frame no GOT entry and no region that *)
(* it may read.                                                              *)
(* ------------------------------------------------------------------------- *)

let pfs_rr_allowed =
  [`pc:num`; `pk:int64`; `sk:int64`; `skb:num->byte`;
   `stackpointer:int64`; `returnaddress:int64`; `r:num`; `bot:int64`];;

let PFS_RR_CALL_TAC prm name ilist n =
  FULL_CALL_TAC (mldsa_native_image_def prm.pfs_exec) prm.pfs_exec name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   pfs_rr_allowed n;;

let PFS_RR_SETUP_TAC prm =
  let inst = pfs_inst prm in
  let template = inst
   `\(pk:int64) (sk:int64) (rho:num) (valid:bool) (pc:num)
     (stackpointer:int64) (returnaddress:int64).
     APPEND
      (if valid then f_ev_epil_v pk sk rho pc stackpointer returnaddress
       else f_ev_epil_i pk sk rho pc stackpointer returnaddress)
      (APPEND
        (ENUMERATEL NCH
          (\i. f_ev_loop pk sk rho pc stackpointer returnaddress i))
        (f_ev_prol pk sk rho pc stackpointer returnaddress))
     :(uarch_event)list` in
  let k0 = prm.pfs_fr - 48 in
  let c = pfs_c prm in
  let regions = map inst
   [`pk:int64,PKL:num`; `sk:int64,SKL:num`; `word pc:int64,libmldsa_size`;
    `word_add stackpointer (word F48):int64,48`;
    `word_add stackpointer (word FR):int64,8`] in
  ASSUME_CALLEE_SAFETY_TAILED_TAC prm.pfs_cpt "H_CPT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC prm.pfs_unpack_th "H_UNPACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC prm.pfs_chkl "H_CHKL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC prm.pfs_chkk "H_CHKK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC prm.pfs_ntt "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC prm.pfs_shake "H_SHAKE" THEN
  CONCRETIZE_F_EVENTS_TAC template THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  ABBREV_TAC `r = mld_sk_rho skb` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst prm.pfs_exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC k0 THEN REALIGN_FRAME_TAC prm.pfs_fr k0 THEN
  REALIGN_NONOV_TAC (k0 - 31) regions THEN
  REALIGN_ALIGNED_TAC
   (c :: map (fun d -> c + d) [64; 80; 96; 112; 128; 144; 160; 176;
                               192; 208; 224; 240; 1280]) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`;;

(*** The packed t1 and t0 from the lazy t as those of mld_pk_from_sk_t, ***)
(*** in the form of PFS_PROLOGUE_TAC, given lazyth                      ***)

let PFS_RR_LAZY_TAC lazyth =
  let cnv = REWRITE_CONV[mld_pk_from_sk_t; mld_sk_s1] THENC
            REWRITE_CONV[ADD_ASSOC] THENC NUM_REDUCE_CONV in
  W(fun (asl,w) ->
    let req = snd(find (fun (_,th) -> concl th = `mld_sk_rho skb = r`) asl) in
    let lth = REWRITE_RULE[req]
               (CONV_RULE cnv (SPEC `skb:num->byte` lazyth)) in
    let tth = MP lth (ASSUME(lhand(concl lth))) in
    let ths = map (MATCH_MP PFS_RR_LAZY_IMP) (CONJUNCTS tth) in
    RULE_ASSUM_TAC(fun th ->
      try tryfind (fun l -> MATCH_MP l th) ths with Failure _ -> th));;

(*** The copies, the unpacking, checks and transform, and t ***)

let PFS_RR_PROLOGUE_TAC prm lazyth =
  let (s1,s2,skt0,t0,pkf,valid,m,h,chk1,chk2) = pfs_terms prm in
  let inst = pfs_inst prm in
  let c = pfs_c prm in
  let exec = prm.pfs_exec in
  let teq = (REWRITE_CONV[mld_pk_from_sk_t; mld_sk_s1] THENC
             REWRITE_CONV[ADD_ASSOC] THENC NUM_REDUCE_CONV)
            (inst `mld_pk_from_sk_t LL unpack PP (skb:num->byte)`) in
  MAP_EVERY (fun n ->
   GHOST_INTRO_TAC (mk_var("ymm"^string_of_int n^"_init",`:int256`))
    (mk_comb(`read:(x86state,int256)component->x86state->int256`,
             mk_const("YMM"^string_of_int n,[])))) (3--7) THEN
  FULL_INIT_TAC THEN
  GLUE_LOAD128_TAC `sk:int64` [0; 16; 32; 48; 64; 80; 96; 112] THEN
  X86_STEPS_TAC exec (1--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_M128]) THEN
  X86_STEPS_TAC exec (11--11) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC exec (12--31) THEN
  GLUE_STORE_TAC `bot:int64` THEN
  SUBGOAL_THEN (subst [pfs_n(c + 64),`k:num`]
   `!j. j < 32 ==> read(memory :> bytes8(word_add bot (word(k + j)))) s31 =
                   (skb:num->byte) j`) ASSUME_TAC THENL
   [GLUE_BYTES_FINAL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (subst [pfs_n(c + 128),`k:num`]
   `!j. j < 64 ==> read(memory :> bytes8(word_add bot (word(k + j)))) s31 =
                   (skb:num->byte)(64 + j)`) ASSUME_TAC THENL
   [GLUE_BYTES_FINAL_TAC; ALL_TAC] THEN
  DISCARD_MATCHING_ASSUMPTIONS
   [`read (memory :> bytes8 (word_add bot (word n))) s31 = x`;
    `read (memory :> bytes128 a) s31 = x`] THEN
  X86_STEPS_TAC exec (32--32) THEN
  GLUE_SLICE_TAC (inst
   `!j. j < S1N ==> read(memory :> bytes8(word_add sk (word(128 + j)))) s32 =
                    (skb:num->byte)(128 + j)`) THEN
  PFS_RR_CALL_TAC prm "H_UNPACK"
   [`read RDI s`; `read RSI s`; `\j. (skb:num->byte)(128 + j)`] 33 THEN
  X86_STEPS_TAC exec (34--36) THEN
  PFS_RR_CALL_TAC prm "H_CHKL" [`read RDI s`; s1; `read RSI s`] 37 THEN
  X86_STEPS_TAC exec (38--44) THEN
  GLUE_SLICE_TAC (inst
   `!j. j < S2N ==> read(memory :> bytes8(word_add sk (word(S2O + j)))) s44 =
                    (skb:num->byte)(S2O + j)`) THEN
  PFS_RR_CALL_TAC prm "H_CHKK"
   [`read RDI s`; inst `\j. (skb:num->byte)(S2O + j)`; `read RSI s`;
    `read RDX s`] 45 THEN
  X86_STEPS_TAC exec (46--48) THEN
  PFS_RR_CALL_TAC prm "H_NTT" [`read RDI s`; s1] 49 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
  YMM_GHOST_TAC `s49:x86state` ["YMM6","ymm6_49"; "YMM7","ymm7_49"] THEN
  CHUNK128_TAC `bot:int64` (c + 64) [0; 1] THEN
  X86_STEPS_TAC exec (50--61) THEN
  FIRST_X_ASSUM(fun th1 ->
    if lhs(concl th1) = `read (memory :> bytes128 pk) s61` then
      FIRST_X_ASSUM(fun th2 ->
        if lhs(concl th2) =
           `read (memory :> bytes128 (word_add pk (word 16))) s61`
        then let f = CONV_RULE(SIMD_SIMPLIFY_CONV []) o REWRITE_RULE[ETA_AX] in
             ASSUME_TAC(MATCH_MP MLD_BYTES8_OF_CHUNKS2 (CONJ (f th1) (f th2)))
        else NO_TAC)
    else NO_TAC) THEN
  FIRST_ASSUM(fun eq -> if concl eq = `mld_sk_rho skb = r` then
    FIRST_ASSUM(fun th ->
      try let _ = BYTES8_OFF_FACT `bot:int64` (c + 64) `s61:x86state` th in
          ASSUME_TAC(REWRITE_RULE[GSYM mld_sk_rho; ETA_AX; eq]
                      (BETA_RULE (MATCH_MP READ_BYTES_OF_BYTES8_OFF th)))
      with Failure _ -> NO_TAC)
    else NO_TAC) THEN
  X86_STEPS_TAC exec (62--62) THEN
  PFS_RR_CALL_TAC prm "H_CPT"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
    mk_comb(`mld_polyvec_map mld_poly_ntt`,s1);
    inst `\j. (skb:num->byte)(S2O + j)`; `r:num`] 63 THEN
  PFS_RR_LAZY_TAC lazyth THEN
  YMM_GHOST_TAC `s63:x86state` ["YMM0","ymm0_63"; "YMM2","ymm2_63"] THEN
  X86_STEPS_TAC exec (64--72) THEN
  FIRST_ASSUM(fun th1 ->
    if can (term_match []
      `!j. j < 32 ==> read (memory :> bytes8 (word_add pk (word j))) s72 =
                      (f:num->byte) j`) (concl th1) then
    FIRST_ASSUM(fun th2 ->
      if can (term_match [] (inst
        `!j. j < T1N ==> read (memory :> bytes8 (word_add pk (word(32 + j))))
                          s72 = (g:num->byte) j`)) (concl th2) then
       ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)
                   (MATCH_MP MLD_BYTES8_JOIN (CONJ th1 th2)))
      else NO_TAC)
    else NO_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[teq; mld_pk_from_sk_pk; mld_or_fold; mld_xor_fold;
              MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[XMM0; XMM2; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC WORD_BLAST THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The whole proof, with the loop over the 26 * k chunks of t0 and the part  *)
(* after it as for the default builds.                                       *)
(* ------------------------------------------------------------------------- *)

let PFS_RR_FULL_TAC prm lazyth =
  let lbl s = mk_binary "+" (`pc:num`,pfs_n(layout(prm.pfs_fn ^ "_" ^ s))) in
  PFS_RR_SETUP_TAC prm THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (pfs_n(26 * prm.pfs_k)) (lbl "loop1")
   (lbl "loop1_exit") (pfs_invariant prm) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; PFS_RR_PROLOGUE_TAC prm lazyth; PFS_BODY_TAC prm;
    PFS_EXIT_TAC prm];;
