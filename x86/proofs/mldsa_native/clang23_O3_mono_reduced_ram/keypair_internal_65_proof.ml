(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the proof (see keypair_internal_65_spec.ml).              *)
(*                                                                           *)
(* This is the proof of keypair_internal_87_proof.ml for ML-DSA-65 (k = 6,   *)
(* l = 5, eta = 4): clang 23 calls mldsa65_poly_uniform_eta_4x three times   *)
(* (s2 2 to 5, then s1 4 and s2 0 and 1 with the nonce 255 in vain, then s1  *)
(* 0 to 3), each followed by inlined vectorised packings into the secret key *)
(* (PACK1 to PACK11, with the vectors of constants loaded into XMM8 to XMM13 *)
(* before the first of each group), mldsa_poly_ntt for the five polynomials  *)
(* of s1 and mld_compute_pack_t0_t165, with the region lemmas of             *)
(* keypair_internal_65_lemmas.ml. The frame of 5632 bytes is at rsp0 = bot + *)
(* 4909, as for ML-DSA-44, with the five polynomials at rsp0 + 0x1e0.        *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_top.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "x86/proofs/utils/mldsa_native_keypair.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/lazy_eq_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_eta_4x_65_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/compute_pack_t0_t1_65_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keypair_internal_65_lemmas.ml";;

(* ------------------------------------------------------------------------- *)
(* The steps are numbered by the counter kp_ctr: KP_STEPS k simulates the    *)
(* next k instructions, KP_CALL and KP_REGION a call of a subroutine or of a *)
(* region lemma as the next step, and templates of facts name the latest     *)
(* state by @ (kp_sub), as in pk_from_sk_65_proof.ml.                        *)
(* ------------------------------------------------------------------------- *)


let KP65_EXEC = MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let KP65_MC = mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc;;

let KP65_VARS = [`pk:int64`; `sk:int64`; `seed:int64`; `rhov:num`; `D:num->bool list`;
                 `mf:int64`; `mc:int64`; `pc:num`; `stackpointer:int64`;
                 `returnaddress:int64`; `bot:int64`];;

let kp_ctr = ref 0;;

let KP_STEPS k : tactic = fun g ->
  let a = !kp_ctr + 1 and b = !kp_ctr + k in kp_ctr := b; X86_STEPS_TAC KP65_EXEC (a--b) g;;

let KP_SSE_STEPS k : tactic = fun g ->
  let a = !kp_ctr + 1 and b = !kp_ctr + k in kp_ctr := b; VERIF_SSE_STEPS_TAC KP65_EXEC (a--b) g;;

let KP_RESET : tactic = fun g -> kp_ctr := 0; ALL_TAC g;;

let kp_state () = mk_var("s" ^ string_of_int !kp_ctr,`:x86state`);;

let kp_sub tmpl =
  let sn = "s" ^ string_of_int !kp_ctr in
  let rec go i acc =
    match (try Some (String.index_from tmpl i '@') with Not_found -> None) with
      None -> acc ^ String.sub tmpl i (String.length tmpl - i)
    | Some j -> go (j+1) (acc ^ String.sub tmpl i (j - i) ^ sn) in
  go 0 "";;

let KP_SUBGOAL tmpl (tac:tactic) : tactic = fun g ->
  (SUBGOAL_THEN (parse_term (kp_sub tmpl)) ASSUME_TAC THENL [tac; ALL_TAC]) g;;

let KP_SLICE tmpl : tactic = fun g -> GLUE_SLICE_TAC (parse_term (kp_sub tmpl)) g;;

let KP_SHIFT =
  let ev = `e:(uarch_event)list` in
  let app_nil = prove(`!l:(uarch_event)list. l = APPEND [] l`, REWRITE_TAC[APPEND]) in
  let app_cons = CONJUNCT2 APPEND in
  let rec shift tm =
    if tm = ev then SPEC ev app_nil
    else match tm with
      Comb(Comb(Const("CONS",_),x),t) ->
        let th = shift t in
        let t0 = lhand(rand(concl th)) in
        let ev' = rand(rand(concl th)) in
        TRANS (AP_TERM (mk_comb(rator(rator tm),x)) th)
              (SYM (SPECL [x; t0; ev'] app_cons))
    | Comb(Comb(Const("APPEND",_),a),t) ->
        let th = shift t in
        let t0 = lhand(rand(concl th)) in
        TRANS (AP_TERM (rator tm) th)
              (SPECL [a; t0; ev] APPEND_ASSOC)
    | _ -> failwith ("KP_SHIFT: " ^ string_of_term tm) in
  shift;;

let KP_EXISTS_E2_TAC : tactic =
  FULL_EXISTS_E2_TAC (ref KP65_VARS) ORELSE
  (W(fun (asl,w) ->
     let l = lhand w in
     let th = KP_SHIFT l in
     REWRITE_TAC[th] THEN
     SAFE_UNIFY_REFL_TAC (ref KP65_VARS) (ref ["f_events_callee"; "f_ev_"])));;

let KP_CALL name ilist : tactic = fun g -> let n = !kp_ctr + 1 in kp_ctr := n;
  (REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (KP65_MC,KP65_EXEC,0x0,KP65_MC,th)
      (`e:(uarch_event)list`::(ilist @ [`pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`])) n THENL
     [KP_EXISTS_E2_TAC; LABEL_TAC name th])) g;;

let KP_REGION name ilist : tactic = fun g -> let n = !kp_ctr + 1 in kp_ctr := n;
  (REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (KP65_MC,KP65_EXEC,0x0,KP65_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [KP_EXISTS_E2_TAC; LABEL_TAC name th])) g;;

(* aligned 32 of bot + off, from the AND of the realignment *)
let KP_ALIGNED32_TAC offs =
  let pat = `word_and (word_add stackpointer (word k)) (word 18446744073709551584):int64 = x` in
  FIRST_ASSUM(fun th ->
    if not (can (term_match [] pat) (concl th)) then NO_TAC else
    let ba = rhs(concl th) in
    let a = dest_small_numeral(rand(rand ba)) in
    let th32 = REWRITE_RULE[th] (SPEC (lhand(lhs(concl th))) REALIGN_ALIGNED_AND) in
    MAP_EVERY (fun off ->
      let d = mk_small_numeral(a - off) in
      let bo = subst [mk_small_numeral off,`n:num`] `word_add bot (word n):int64` in
      let sub = mk_comb(mk_comb(`word_sub:int64->int64->int64`,ba),
                        mk_comb(`word:num->int64`,d)) in
      let eq = WORD_RULE(mk_eq(bo,sub)) in
      let c = NORMALIZE_ALIGNED_WORD_CONV (mk_comb(`aligned 32:int64->bool`,sub)) in
      ASSUME_TAC(REWRITE_RULE[SYM eq] (EQ_MP (SYM c) th32))) offs);;

(* ------------------------------------------------------------------------- *)
(* The nonces of the samplings (as KP65_NONCE_TAC of the gcc proof).         *)
(* ------------------------------------------------------------------------- *)

let KP65_N n = mk_small_numeral n;;

let KP65_USED = `\n. n < 11 \/ n = 255`;;

let KP65_NONCE_TAC =
  FIRST_ASSUM(fun th ->
    if concl th <> `mld_keypair_terminates_65 SEED` then NO_TAC else
    let tth = REWRITE_RULE[mld_keypair_terminates_65] th in
    MAP_EVERY (fun n ->
      let nt = KP65_N n in
      let uth = prove(mk_comb(KP65_USED,nt), BETA_TAC THEN ARITH_TAC) in
      let ith = SPECL [`4`; `6`; `5`; KP65_USED; `SEED:num`; nt] in
      let th1 = MP (ith MLD_KEYPAIR_TERMINATES_USED) (CONJ tth uth) in
      let th2 = REWRITE_RULE[GSYM mld_keypair_declass_65]
                 (MP (ith MLD_KEYPAIR_DECLASS_USED) uth) in
      ASSUME_TAC th1 THEN
      FIRST_ASSUM(fun dth ->
        if concl dth = `mld_keypair_declass_65 SEED = D`
        then ASSUME_TAC(REWRITE_RULE[dth] th2) else NO_TAC) THEN
      ASSUME_TAC(WORD_REDUCE_CONV
        (mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,nt)))) THEN
      ASSUME_TAC(WORD_REDUCE_CONV
        (mk_comb(`word_zx:int64->byte`,mk_comb(`word:num->int64`,nt)))))
     [0;1;2;3;4;5;6;7;8;9;10;255]);;

let KP65_POLY n =
  mk_comb(`mld_poly_uniform_eta 4 (mld_keypair_rhoprime 6 5 SEED)`,
          mk_comb(`word:num->byte`,KP65_N n));;


let KP65_ASSUME_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcb = CONJ_PAIR th in
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL th) "H_CPT" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL th) "H_ETA" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] ms) "H_MEMSET" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 KP65_SEED) "H_SEED" THEN
    MAP_EVERY (fun (n,pth) ->
      ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 pth) ("H_PACK" ^ string_of_int n))
     (zip (1--11) KP65_PACKS) THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 KP65_HASH) "H_HASH");;

let KP65_SETUP_TAC =
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  ABBREV_TAC `rhov = mld_keypair_rho 6 5 SEED` THEN
  ABBREV_TAC `D = mld_keypair_declass_65 SEED` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst KP65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 10572 THEN REALIGN_FRAME_TAC 10620 10572 THEN
  REALIGN_NONOV_TAC 10541
   [`pk:int64,1952`; `sk:int64,4032`; `seed:int64,32`;
    `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`;
    `word_add stackpointer (word 10572):int64,48`;
    `word_add stackpointer (word 10620):int64,8`] THEN
  REALIGN_ALIGNED_TAC (map (fun q -> 4909 + 16 * q) (0--29) @ map (fun n -> 5389 + 1024 * n) (0--4)) THEN
  KP_ALIGNED32_TAC [4909] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  KP65_NONCE_TAC;;

(* a slice of a byte string at bot + src + j for j < n, at the offset off *)
let KP_SLICE_FROM src srcn off tmpl : tactic = fun g ->
  let st = kp_state () in
  (KP_SUBGOAL tmpl
   (X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_forall c && free_in st c && free_in `bot:int64` c &&
         can (find_term (fun t -> t = mk_small_numeral src)) c &&
         (let j,b = dest_forall c in is_imp b && is_binary "<" (lhand b) && rand(lhand b) = mk_small_numeral srcn)
      then MP_TAC(SPEC (mk_binary "+" (mk_small_numeral off,`j:num`)) th) else NO_TAC) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD_ASSOC; ADD_CLAUSES] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    DISCH_THEN ACCEPT_TAC)) g;;

(* the seed buffer at bot + 5261, rho and rho' *)
let KP_SEEDBUF_TAC : tactic =
  KP_SUBGOAL "!j. j < 128 ==> read (memory :> bytes8 (word_add bot (word (5261 + j)))) @ = mld_keypair_seedbuf 6 5 SEED j"
   (X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `bot:int64` (concl th) &&
                             can (find_term (fun t -> t = `mld_keypair_seedbuf 6 5 SEED`)) (concl th)
                          then MP_TAC(MP (SPEC `j:num` th) (ASSUME `j < 128`)) else NO_TAC) THEN
    REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN DISCH_THEN ACCEPT_TAC) THEN
  KP_SLICE_FROM 5261 128 0 "!j. j < 32 ==> read (memory :> bytes8 (word_add bot (word (5261 + j)))) @ = mld_keypair_seedbuf 6 5 SEED j" THEN
  KP_SLICE_FROM 5261 128 32 "!j. j < 64 ==> read (memory :> bytes8 (word_add bot (word (5293 + j)))) @ = mld_keypair_seedbuf 6 5 SEED (32 + j)" THEN
  KP_SLICE_FROM 5261 128 96 "!j. j < 32 ==> read (memory :> bytes8 (word_add bot (word (5357 + j)))) @ = mld_keypair_seedbuf 6 5 SEED (96 + j)" THEN
  (fun g -> let st = kp_state () in
    (FIRST_ASSUM(fun th ->
       if can (term_match [] (subst [st,`s:x86state`] `!j. j < 32 ==> read (memory :> bytes8 (word_add bot (word (5261 + j)))) s = mld_keypair_seedbuf 6 5 SEED j`)) (concl th)
       then FIRST_ASSUM(fun eq -> if concl eq = `mld_keypair_rho 6 5 SEED = rhov` then
              ASSUME_TAC(REWRITE_RULE[ETA_AX; GSYM mld_keypair_rho; eq] (BETA_RULE (MATCH_MP READ_BYTES_OF_BYTES8_OFF th)))
              else NO_TAC)
       else NO_TAC) THEN
     FIRST_ASSUM(fun th ->
       if can (term_match [] (subst [st,`s:x86state`] `!j. j < 64 ==> read (memory :> bytes8 (word_add bot (word (5293 + j)))) s = mld_keypair_seedbuf 6 5 SEED (32 + j)`)) (concl th)
       then ASSUME_TAC(REWRITE_RULE[GSYM mld_keypair_rhoprime] (BETA_RULE (MATCH_MP READ_BYTES_OF_BYTES8_OFF th)))
       else NO_TAC)) g);;

let KP_ETA_ARGS n0 = [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
   `mld_keypair_rhoprime 6 5 SEED`;
   mk_comb(`word:num->int64`,KP65_N n0); mk_comb(`word:num->int64`,KP65_N (n0+1));
   mk_comb(`word:num->int64`,KP65_N (n0+2)); mk_comb(`word:num->int64`,KP65_N (n0+3))];;

(* the pack (PACK4) of polynomial nonce from the buffer at rsp0 + cb: its
   facts restated in the form of the instantiated precondition *)
let KP_PACK idx nonce cb =
  KP_SUBGOAL (Printf.sprintf "!i. i < 256 ==> read (memory :> bytes32 (word_add bot (word (4909 + %d + 4 * i)))) @ = mld_poly_uniform_eta 4 (mld_keypair_rhoprime 6 5 SEED) (word %d) i" cb nonce)
   (X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term (fun t -> t = mk_small_numeral(4909 + cb))) (concl th) &&
                             can (find_term (fun t -> t = KP65_POLY nonce)) (concl th)
                          then ACCEPT_TAC(MP (SPEC `i:num` th) (ASSUME `i < 256`)) else NO_TAC)) THEN
  KP_REGION ("H_PACK" ^ string_of_int idx) [`sk:int64`; `read RSP s`; `pc:num`; KP65_POLY nonce];;

(*** The vector constants of the packings in XMM8 to XMM13, loaded with
     MOVDQA from mldsa65_keypair_internal_const1..6 (constant k at 0x25280 +
     16 k in the image); r is the offset of the instruction after the load ***)

let KP65_CONST_RULE = IMAGE_CONST_RULE_FOR mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc;;

let KP_RIP_TAC k r = IMAGE_RIPREL_TAC (KP65_CONST_RULE (0x25280 + 16 * k) 128) (KP65_FB + r);;

let KP_YMM_GHOST : tactic = fun g ->
  let n = string_of_int !kp_ctr in
  YMM_GHOST_TAC (mk_var("s" ^ n,`:x86state`))
   (map (fun k -> Printf.sprintf "YMM%d" k, Printf.sprintf "y%d_c%s" k n) (8--13)) g;;

(* the low 128 bits of YMMk as XMMk, with the value of the constant *)
let KP_XMM_TAC : tactic = fun g ->
  let sn = "s" ^ string_of_int !kp_ctr in
  let xmms = [XMM8; XMM9; XMM10; XMM11; XMM12; XMM13] in
  (MAP_EVERY (fun ((r,v),xmm) ->
     SUBGOAL_THEN (parse_term(Printf.sprintf "read %s (%s:x86state) = word %s" r sn v))
      ASSUME_TAC THENL
      [REWRITE_TAC[xmm; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST;
       ALL_TAC]) (zip KPPACK4_CONSTS xmms)) g;;

(* the loads of the six constants, in the order of the registers (8 to 13)
   with the offsets of the instructions after the loads, and the n steps
   from the return of the sampling to the head of the first loop *)
let KP_CONSTS loads n =
  KP_YMM_GHOST THEN MAP_EVERY (fun (k,r) -> KP_RIP_TAC k r) loads THEN
  KP_SSE_STEPS n THEN KP_XMM_TAC;;

let KP65_S1 = `mld_keypair_s 4 6 5 SEED`;;

(* coefficients of polynomial n of s at bot + 5389 + 1024 n, as mld_poly_of *)
let KP_NTT_PRE n = KP_SUBGOAL (Printf.sprintf "!i. i < 256 ==> read (memory :> bytes32 (word_add bot (word (%d + 4 * i)))) @ = mld_poly_of (mld_keypair_s 4 6 5 SEED) %d i" (5389 + 1024 * n) n)
  (X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   REWRITE_TAC[mld_poly_of] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   ASM_SIMP_TAC[MLD_KEYPAIR_S_COEFF] THEN
   FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term (fun t -> t = mk_small_numeral(5389 + 1024 * n))) (concl th) &&
                            can (find_term (fun t -> t = KP65_POLY n)) (concl th)
                         then ACCEPT_TAC(MP (SPEC `i:num` th) (ASSUME `i < 256`)) else NO_TAC));;

let KP_NTT_CALL n = KP_NTT_PRE n THEN
  KP_CALL "H_NTT" [`read RDI s`; mk_comb(mk_comb(`mld_poly_of:(num->int32)->num->num->int32`,KP65_S1),KP65_N n)];;

let KP_JOIN_HYP_TAC =
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REPEAT CONJ_TAC THEN REWRITE_TAC[ADD_ASSOC; ADD_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN ASM_REWRITE_TAC[];;

let KP_NTT_JOIN : tactic = fun g ->
  let st = kp_state () in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "!j. j < 1280 ==> read (memory :> bytes32 (word_add bot (word (5389 + 4 * j)))) %s = mld_polyvec_map mld_poly_ntt (mld_keypair_s 4 6 5 SEED) j" (fst(dest_var st)))) ASSUME_TAC THENL
   [MP_TAC(SPECL [`bot:int64`; `5389`; `\n i. mld_poly_ntt (mld_poly_of (mld_keypair_s 4 6 5 SEED) n) i`; `5`; st] PK_JOIN) THEN
    ANTS_TAC THENL [KP_JOIN_HYP_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th ->
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `j:num` th) THEN ANTS_TAC THENL [UNDISCH_TAC `j < 1280` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[mld_polyvec_map; mld_polyvec] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      DISCH_THEN ACCEPT_TAC);
    ALL_TAC]) g;;

(* the packed s at sk + 128, from the eleven packings *)
let KP_SREGION_TAC : tactic = fun g ->
  let st = kp_state () in
  (SUBGOAL_THEN (subst [st,`s:x86state`]
    `!j. j < 1408
         ==> read (memory :> bytes8 (word_add sk (word (128 + j)))) s =
             mld_polyvec_pack 128 mld_polyeta_pack_4 (mld_keypair_s 4 6 5 SEED) j`) ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1408 = 128 * 11`] THEN
    MATCH_MP_TAC MLD_KEYPAIR_JOIN8 THEN SIMP_TAC[MLD_KEYPAIR_S_PACK_4] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC]) g;;

let KP_NTT_BOUND : tactic =
  SUBGOAL_THEN
   `!j. j < 1280
        ==> abs(ival(mld_polyvec_map mld_poly_ntt
                      (mld_keypair_s 4 6 5 SEED) j)) <
            &94279689`
   ASSUME_TAC THENL
   [MP_TAC(SPECL [`5`; `mld_keypair_s 4 6 5 SEED`]
                 MLD_LAZY_POLYVEC_NTT_BOUND) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(SPECL [`4`; `6`; `5`; `\n. n < 11 \/ n = 255`; `SEED:num`]
                 MLD_LAZY_KEYPAIR_S_BOUND) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM mld_keypair_terminates_65] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC];;

let KP_S2_SLICE : tactic = fun g ->
  let st = kp_state () in
  (SUBGOAL_THEN (subst [st,`s:x86state`]
   `!j. j < 768
        ==> read (memory :> bytes8 (word_add sk (word (768 + j)))) s =
            mld_polyvec_pack 128 mld_polyeta_pack_4 (mld_keypair_s 4 6 5 SEED)
             (5 * 128 + j)`)
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if can (term_match [] (subst [st,`s:x86state`]
      `!j. j < 1408 ==> read (memory :> bytes8 (word_add sk (word (128 + j)))) s = x j`)) (concl th)
      then MP_TAC(SPEC `5 * 128 + j` th) else NO_TAC) THEN
    REWRITE_TAC[ARITH_RULE `128 + 5 * 128 + j = 768 + j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
    ALL_TAC]) g;;

(* rho in the first 32 bytes of pk *)
let KP_RHO_PK : tactic = fun g ->
  let st = kp_state () in
  let at t = subst [st,`s:x86state`] t in
  let f = CONV_RULE(SIMD_SIMPLIFY_CONV []) in
  (FIRST_ASSUM(fun th1 ->
    if lhs(concl th1) = at `read (memory :> bytes128 pk) s` then
      FIRST_ASSUM(fun th2 ->
        if lhs(concl th2) = at `read (memory :> bytes128 (word_add pk (word 16))) s`
        then ASSUME_TAC(BETA_RULE(MATCH_MP MLD_BYTES8_OF_CHUNKS2 (CONJ (f th1) (f th2))))
        else NO_TAC)
    else NO_TAC)) g;;

let KP65_T = `mld_keypair_t 4 6 5 mld_polyeta_pack_4 mld_polyeta_unpack_4 128 SEED`;;

(* the public key as mld_keypair_pk_65, byte by byte and as a number *)
let KP_PK_BYTES : tactic = fun g ->
  let st = kp_state () in
  (SUBGOAL_THEN
   `mld_compute_t 5 mld_polyeta_unpack_4 128 rhov
     (mld_polyvec_map mld_poly_ntt (mld_keypair_s 4 6 5 SEED))
     (\j. mld_polyvec_pack 128 mld_polyeta_pack_4 (mld_keypair_s 4 6 5 SEED)
           (5 * 128 + j)) =
    mld_keypair_t 4 6 5 mld_polyeta_pack_4 mld_polyeta_unpack_4 128 SEED`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[mld_keypair_t] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN (subst [st,`s:x86state`] `read (memory :> bytes(pk,32)) s = mld_keypair_rho 6 5 SEED`) ASSUME_TAC THENL
   [REWRITE_TAC[mld_keypair_rho] THEN MATCH_MP_TAC READ_BYTES_OF_BYTES8 THEN
    FIRST_ASSUM(fun th -> if can (term_match [] (subst [st,`s:x86state`] `!j. j < 32 ==> read (memory :> bytes8 (word_add pk (word j))) s = mld_keypair_seedbuf 6 5 SEED j`)) (concl th) then ACCEPT_TAC th else NO_TAC);
    ALL_TAC] THEN
   MP_TAC(CONV_RULE NUM_REDUCE_CONV
    (SPECL [`pk:int64`; st; `4`; `6`; `5`; `mld_polyeta_pack_4`;
            `mld_polyeta_unpack_4`; `128`; `SEED:num`]
           MLD_KEYPAIR_PK_BYTES)) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[GSYM mld_keypair_pk_65] THEN DISCH_TAC THEN
   FIRST_ASSUM(fun th ->
     if can (term_match []
          (subst [st,`s:x86state`] `!j. j < 1952
               ==> read (memory :> bytes8 (word_add pk (word j))) s =
                   mld_keypair_pk_65 SEED j`)) (concl th)
     then ASSUME_TAC(REWRITE_RULE[ETA_AX] (MATCH_MP READ_BYTES_OF_BYTES8 th))
     else NO_TAC)) g;;


(* the hash state at bot + 4925 as chunks, for the copy of tr *)
let KP_HASH_CHUNKS_TAC = TR_STATE_CHUNKS_TAC `word_add bot (word 4925):int64` (0--3) [];;

(* the bytes of tr in sk, from the four chunks stored at sk + 64 *)
let KP_TR_SK_TAC : tactic = fun g ->
  let st = kp_state () in
  let hk = `keccak_f1600 (mld_shake256_state 1952 (num_of_bytelist (list_of_seq (mld_keypair_pk_65 SEED) 1952)))` in
  (SUBGOAL_THEN (subst [st,`s:x86state`; hk,`K:1600 word`]
     `!j. j < 64 ==> read (memory :> bytes8 (word_add sk (word (64 + j)))) s =
                     mld_shake256_byte 1952 (num_of_bytelist (list_of_seq (mld_keypair_pk_65 SEED) 1952)) j`)
    ASSUME_TAC THENL
   [MP_TAC(SPECL [`word_add sk (word 64):int64`; hk; st; `4`] KP_SQUEEZE_CHUNKS) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    ANTS_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN ASM_REWRITE_TAC[];
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN ASM_SIMP_TAC[th] THEN
                           MATCH_MP_TAC KP_SHAKE_BYTE THEN ASM_ARITH_TAC)];
    ALL_TAC]) g;;

(* the 32 bytes at sk + off from two chunks of f *)
let KP_SK32_TAC off f : tactic = fun g ->
  let st = kp_state () in
  let a = if off = 0 then `sk:int64` else mk_comb(mk_comb(`word_add:int64->int64->int64`,`sk:int64`),mk_comb(`word:num->int64`,mk_small_numeral off)) in
  (MP_TAC(ISPECL [a; f; st] MLD_BYTES8_OF_CHUNKS2) THEN
   ANTS_TAC THENL
    [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN ASM_REWRITE_TAC[];
     DISCH_THEN(ASSUME_TAC o BETA_RULE o CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))]) g;;

let KP_MEMSET_CALL : tactic = fun g ->
  let plt = layout "plt_memset" and got = layout "got_memset" in
  let n = !kp_ctr in
  kp_ctr := n + 2;
  (LIBC_PLT_TAC KP65_EXEC plt got n THEN
   REMOVE_THEN "H_MEMSET" (fun th ->
     LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true KP65_EXEC th
       [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`; `read RSP s`;
        `read (memory :> bytes64 (read RSP s)) s`] (n + 2) THENL
     [KP_EXISTS_E2_TAC; LABEL_TAC "H_MEMSET" th]) THEN RSP_NORM_TAC) g;;

(* the secret key as mld_keypair_sk_65 *)
let KP_SK_BYTES : tactic = fun g ->
  let st = kp_state () in
  (MP_TAC(CONV_RULE NUM_REDUCE_CONV
    (SPECL [`sk:int64`; st; `4`; `6`; `5`; `mld_polyeta_pack_4`;
            `mld_polyeta_unpack_4`; `128`; `SEED:num`]
           MLD_KEYPAIR_SK_BYTES)) THEN
   REWRITE_TAC[GSYM mld_keypair_pk_65; GSYM mld_keypair_sk_65] THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) g;;

let KP_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;


(* ------------------------------------------------------------------------- *)
(* The whole function.                                                       *)
(* ------------------------------------------------------------------------- *)

let KP65_ETA_ARGS2 = [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
   `mld_keypair_rhoprime 6 5 SEED`; `word 4:int64`; `word 5:int64`; `word 6:int64`; `word 255:int64`];;

let KP65_FULL_TAC =
  (KP65_ASSUME_TAC THEN KP65_SETUP_TAC) THEN
  (FULL_INIT_TAC THEN KP_RESET THEN KP_STEPS 8 THEN REALIGN_RSP_TAC THEN KP_STEPS 4) THEN
  (KP_REGION "H_SEED" [`read RSP s`; `seed:int64`; `pk:int64`; `pc:num`; `SEED:num`] THEN
   KP_SEEDBUF_TAC) THEN
  (KP_STEPS 13 THEN KP_CALL "H_ETA" (KP_ETA_ARGS 7) THEN
   KP_CONSTS [0,0x28e; 1,0x297; 2,0x2a0; 3,0x2a9; 4,0x2b2; 5,0x2bb] 9 THEN
   KP_PACK 1 7 480 THEN KP_STEPS 4 THEN KP_PACK 2 8 1504 THEN
   KP_STEPS 4 THEN KP_PACK 3 9 2528 THEN KP_STEPS 4 THEN KP_PACK 4 10 3552) THEN
  (KP_STEPS 13 THEN KP_CALL "H_ETA" KP65_ETA_ARGS2 THEN
   KP_CONSTS [5,0x7c3; 4,0x7cc; 3,0x7d5; 2,0x7de; 1,0x7e7; 0,0x7f0] 9 THEN
   KP_PACK 5 4 4576 THEN KP_STEPS 4 THEN KP_PACK 6 5 480 THEN
   KP_STEPS 4 THEN KP_PACK 7 6 1504) THEN
  (KP_STEPS 13 THEN KP_CALL "H_ETA" (KP_ETA_ARGS 0) THEN
   KP_CONSTS [5,0xbdd; 4,0xbe6; 3,0xbef; 2,0xbf8; 1,0xc01; 0,0xc0a] 9 THEN
   KP_PACK 8 0 480 THEN KP_STEPS 4 THEN KP_PACK 9 1 1504 THEN
   KP_STEPS 4 THEN KP_PACK 10 2 2528 THEN KP_STEPS 4 THEN KP_PACK 11 3 3552 THEN
   KP_SREGION_TAC) THEN
  (KP_STEPS 5 THEN KP_NTT_CALL 0 THEN
   MAP_EVERY (fun n -> KP_STEPS 2 THEN KP_NTT_CALL n) (1--4) THEN
   KP_NTT_JOIN) THEN
  (CHUNK128_TAC `bot:int64` 5261 [0; 1] THEN
   (fun g -> YMM_GHOST_TAC (kp_state ()) ["YMM0","y0_r"; "YMM1","y1_r"] g) THEN
   KP_STEPS 4 THEN KP_RHO_PK) THEN
  (KP_STEPS 7 THEN KP_NTT_BOUND THEN KP_S2_SLICE THEN
   KP_CALL "H_CPT" [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
     `mld_polyvec_map mld_poly_ntt (mld_keypair_s 4 6 5 SEED)`;
     `\j. mld_polyvec_pack 128 mld_polyeta_pack_4 (mld_keypair_s 4 6 5 SEED) (5 * 128 + j)`;
     `rhov:num`] THEN
   KP_PK_BYTES) THEN
  (KP_REGION "H_HASH" [`read RSP s`; `pk:int64`; `pc:num`;
     `num_of_bytelist (list_of_seq (mld_keypair_pk_65 SEED) 1952)`] THEN
   KP_HASH_CHUNKS_TAC THEN
   (fun g -> YMM_GHOST_TAC (kp_state ())
              ["YMM0","y0_h"; "YMM1","y1_h"; "YMM2","y2_h"; "YMM3","y3_h"] g) THEN
   KP_SSE_STEPS 8 THEN KP_STEPS 14) THEN
  (CHUNK128_TAC `bot:int64` 5261 [0; 1] THEN CHUNK128_TAC `bot:int64` 5357 [0; 1] THEN
   KP_SSE_STEPS 8 THEN KP_SSE_STEPS 8 THEN
   KP_SK32_TAC 0 `\j. mld_keypair_seedbuf 6 5 SEED j` THEN
   KP_SK32_TAC 32 `\j. mld_keypair_seedbuf 6 5 SEED (96 + j)` THEN
   KP_TR_SK_TAC) THEN
  (KP_STEPS 4 THEN KP_MEMSET_CALL THEN KP_SK_BYTES) THEN
  (KP_STEPS 33 THEN KP_FINAL_TAC);;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  KP65_FULL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
