(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key: the proof (see pk_from_sk_44_spec.ml).    *)
(*                                                                           *)
(* clang 23 calls mldsa44_polyeta_unpack, mldsa44_polyvecl_chknorm,          *)
(* mldsa_poly_ntt and mld_compute_pack_t0_t144 from mldsa44_pk_from_sk and   *)
(* inlines the rest of mld_sign_pk_from_sk. The proof composes the theorems  *)
(* of the callees with the region lemmas of pk_from_sk_44_lemmas.ml: the     *)
(* norm checks of the four polynomials of s2 (SCAN1 to SCAN4), the          *)
(* comparison loop of t0 (CMP), the rest of the checks with the SHAKE256 of  *)
(* pk (TAIL) and the end from join1 to the return (CL).                      *)
(*                                                                           *)
(* The prologue realigns RSP to 32 bytes below the six registers that it     *)
(* pushes (REALIGN_TAC), so that the frame of 7264 bytes is at rsp0 = bot +  *)
(* 4909, above the 4901 bytes of the stack of mld_compute_pack_t0_t1. The    *)
(* code copies rho, the key and tr from the secret key to the frame and rho  *)
(* to pk, unpacks s1 into the frame (the four calls, joined into the vector  *)
(* by PK_JOIN), checks its norm, unpacks and checks each polynomial of s2    *)
(* into one scratch buffer, transforms s1, and computes t1 into pk and t0    *)
(* into the frame. After the comparison of t0 and TAIL, the low byte of R13  *)
(* is zero exactly when the key is valid (PK44_VALID relates the checks as   *)
(* the code makes them to mld_pk_from_sk_valid). On the invalid path the     *)
(* code clears pk with memset; both paths then run CL.                       *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_top.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/lazy_eq_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyeta_unpack_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvecl_chknorm_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/compute_pack_t0_t1_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/pk_from_sk_44_lemmas.ml";;

(* ------------------------------------------------------------------------- *)
(* The steps are numbered by the counter pk_ctr: PK_STEPS k simulates the    *)
(* next k instructions, PK_CALL and PK_REGION a call of a subroutine or of a *)
(* region lemma as the next step, and templates of facts name the latest     *)
(* state by @ (pk_sub).                                                      *)
(* ------------------------------------------------------------------------- *)

let PK44_EXEC = MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let PK44_MC = mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc;;

let PK44_VARS = [`pk:int64`; `sk:int64`; `skb:num->byte`; `mf:int64`; `mc:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`; `r:num`; `bot:int64`];;

let pk_ctr = ref 0;;

let PK_STEPS k : tactic = fun g -> let a = !pk_ctr + 1 and b = !pk_ctr + k in pk_ctr := b; X86_STEPS_TAC PK44_EXEC (a--b) g;;

let PK_RESET : tactic = fun g -> pk_ctr := 0; ALL_TAC g;;

let PK44_TEMPLATE = `\(pk:int64) (sk:int64) (rho:num) (valid:bool) (mf:int64) (mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64). if valid then f_ev_v pk sk rho mf mc pc stackpointer returnaddress else f_ev_i pk sk rho mf mc pc stackpointer returnaddress :(uarch_event)list`;;

let PK44_ASSUME_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcb = CONJ_PAIR th in
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL th) "H_CPT" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_UNPACK" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC MLDSA_NATIVE_POLYVECL_CHKNORM_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_CHKL" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] ms) "H_MEMSET" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 PK44_SCAN1) "H_SCAN1" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 PK44_SCAN2) "H_SCAN2" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 PK44_SCAN3) "H_SCAN3" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 PK44_SCAN4) "H_SCAN4" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 PK44_CMP) "H_CMP" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 PK44_TAIL) "H_TAIL" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 (MATCH_MP PK44_CL ms)) "H_CL");;

(* aligned 32 of bot + off, from the AND of the realignment (as
   REALIGN_ALIGNED_TAC for aligned 16) *)
let PK_ALIGNED32_TAC offs =
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

let PK44_SETUP_TAC =
  CONCRETIZE_F_EVENTS_TAC PK44_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  ABBREV_TAC `r = mld_sk_rho skb` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst PK44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 12204 THEN REALIGN_FRAME_TAC 12252 12204 THEN
  REALIGN_NONOV_TAC 12173
   [`pk:int64,1312`; `sk:int64,2560`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`;
    `word_add stackpointer (word 12204):int64,48`;
    `word_add stackpointer (word 12252):int64,8`] THEN
  REALIGN_ALIGNED_TAC (4909 :: 4909 + 1472 :: map (fun q -> 4909 + 16 * q) (1--27)) THEN
  PK_ALIGNED32_TAC [4909] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`;;

(* instantiate the state name of the latest step in a template *)
let pk_sub tmpl = 
  let sn = "s" ^ string_of_int !pk_ctr in
  let rec go i acc = 
    match (try Some (String.index_from tmpl i '@') with Not_found -> None) with
      None -> acc ^ String.sub tmpl i (String.length tmpl - i)
    | Some j -> go (j+1) (acc ^ String.sub tmpl i (j - i) ^ sn) in
  go 0 "";;

let PK_SLICE tmpl : tactic = fun g -> GLUE_SLICE_TAC (parse_term (pk_sub tmpl)) g;;

let PK_SUBGOAL tmpl (tac:tactic) : tactic = fun g -> (SUBGOAL_THEN (parse_term (pk_sub tmpl)) ASSUME_TAC THENL [tac; ALL_TAC]) g;;

let PK_SHIFT =
  let ev = `e:(uarch_event)list` in
  let nil = `[]:(uarch_event)list` in
  let app_nil = prove(`!l:(uarch_event)list. l = APPEND [] l`, REWRITE_TAC[APPEND]) in
  let app_cons = CONJUNCT2 APPEND in   (* APPEND (CONS h t) l = CONS h (APPEND t l) *)
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
    | _ -> failwith ("PK_SHIFT: " ^ string_of_term tm) in
  shift;;

let PK_EXISTS_E2_TAC : tactic =
  FULL_EXISTS_E2_TAC (ref PK44_VARS) ORELSE
  (W(fun (asl,w) ->
     let l = lhand w in
     let th = PK_SHIFT l in
     REWRITE_TAC[th] THEN
     SAFE_UNIFY_REFL_TAC (ref PK44_VARS) (ref ["f_events_callee"; "f_ev_"])));;

let PK_CALL name ilist : tactic = fun g -> let n = !pk_ctr + 1 in pk_ctr := n;
  (REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (PK44_MC,PK44_EXEC,0x0,PK44_MC,th)
      (`e:(uarch_event)list`::(ilist @ [`pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`])) n THENL
     [PK_EXISTS_E2_TAC; LABEL_TAC name th])) g;;

let PK_REGION name ilist : tactic = fun g -> let n = !pk_ctr + 1 in pk_ctr := n;
  (REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (PK44_MC,PK44_EXEC,0x0,PK44_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [PK_EXISTS_E2_TAC; LABEL_TAC name th])) g;;

let PK_UNPACK_ARGS n = [`read RDI s`; `read RSI s`; subst [mk_small_numeral (128 + 96 * n),`K:num`] `\j. (skb:num->byte) (K + j)`];;

let PK_SLICE_S1 n = PK_SLICE (Printf.sprintf "!j. j < 96 ==> read (memory :> bytes8 (word_add sk (word (%d + j)))) @ = (skb:num->byte) (%d + j)" (128 + 96 * n) (128 + 96 * n));;

let PK_JOIN_HYP_TAC =
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REPEAT CONJ_TAC THEN REWRITE_TAC[ADD_ASSOC; ADD_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN ASM_REWRITE_TAC[];;

let PK_S1_JOIN : tactic = fun g ->
  let sn = "s" ^ string_of_int !pk_ctr in
  let st = mk_var(sn,`:x86state`) in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "!j. j < 1024 ==> read (memory :> bytes32 (word_add bot (word (8045 + 4 * j)))) %s = mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\\j. (skb:num->byte) (128 + j)) j" sn)) ASSUME_TAC THENL
   [MP_TAC(SPECL [`bot:int64`; `8045`; `\n i. mld_polyeta_unpack_2 (\t. (skb:num->byte) (128 + (96 * n + t))) i`; `4`; st] PK_JOIN) THEN
    ANTS_TAC THENL [PK_JOIN_HYP_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th ->
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `j:num` th) THEN ANTS_TAC THENL [UNDISCH_TAC `j < 1024` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[mld_polyvec_unpack; mld_polyvec] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      DISCH_THEN ACCEPT_TAC);
    ALL_TAC]) g;;

let PK_S2_UNPACK_ARGS n = [`read RDI s`; `read RSI s`; subst [mk_small_numeral (512 + 96 * n),`K:num`] `\j. (skb:num->byte) (K + j)`];;

let PK_SLICE_S2 n = PK_SLICE (Printf.sprintf "!j. j < 96 ==> read (memory :> bytes8 (word_add sk (word (%d + j)))) @ = (skb:num->byte) (%d + j)" (512 + 96 * n) (512 + 96 * n));;

let PK_SCAN_PRE n = PK_SUBGOAL (Printf.sprintf "!i. i < 256 ==> read (memory :> bytes32 (word_add bot (word (4909 + 448 + 4 * i)))) @ = mld_polyeta_unpack_2 (\\j. (skb:num->byte) (%d + j)) i" (512 + 96 * n))
  (X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term (fun t -> t = `5357`)) (concl th) && free_in `bot:int64` (concl th) && not(free_in `sk:int64` (concl th)) then ACCEPT_TAC(MP (SPEC `i:num` th) (ASSUME `i < 256`)) else NO_TAC));;

let PK_S2_SCAN n = PK_SCAN_PRE n THEN PK_REGION ("H_SCAN" ^ string_of_int (n + 1))
   [subst [mk_small_numeral (512 + 96 * n),`K:num`] `mld_polyeta_unpack_2 (\j. (skb:num->byte) (K + j))`; `read RSP s`; `pc:num`];;

let PK_S1 = `mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte) (128 + j))`;;

let PK_NTT_PRE n = PK_SUBGOAL (Printf.sprintf "!i. i < 256 ==> read (memory :> bytes32 (word_add bot (word (%d + 4 * i)))) @ = mld_poly_of (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\\j. (skb:num->byte) (128 + j))) %d i" (8045 + 1024 * n) n)
  (X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[PK_POLY_OF_UNPACK] THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; ADD_ASSOC] THEN
   CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
   FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term (fun t -> t = mk_small_numeral(8045 + 1024 * n))) (concl th) && free_in `bot:int64` (concl th) && free_in `mld_polyeta_unpack_2` (concl th) && not(free_in `sk:int64` (concl th)) && not(free_in `mld_poly_of` (concl th)) then ACCEPT_TAC(MP (SPEC `i:num` th) (ASSUME `i < 256`)) else NO_TAC));;

let PK_NTT_CALL n = PK_NTT_PRE n THEN PK_CALL "H_NTT" [`read RDI s`; mk_comb(mk_comb(`mld_poly_of:(num->int32)->num->num->int32`,PK_S1),mk_small_numeral n)];;

let PK_NTT_JOIN : tactic = fun g ->
  let sn = "s" ^ string_of_int !pk_ctr in
  let st = mk_var(sn,`:x86state`) in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "!j. j < 1024 ==> read (memory :> bytes32 (word_add bot (word (8045 + 4 * j)))) %s = mld_polyvec_map mld_poly_ntt (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\\j. (skb:num->byte) (128 + j))) j" sn)) ASSUME_TAC THENL
   [MP_TAC(SPECL [`bot:int64`; `8045`; `\n i. mld_poly_ntt (mld_poly_of (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte) (128 + j))) n) i`; `4`; st] PK_JOIN) THEN
    ANTS_TAC THENL [PK_JOIN_HYP_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th ->
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `j:num` th) THEN ANTS_TAC THENL [UNDISCH_TAC `j < 1024` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[mld_polyvec_map; mld_polyvec] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      DISCH_THEN ACCEPT_TAC);
    ALL_TAC]) g;;

let PK_RHO_FACT : tactic = fun g ->
  let sn = "s" ^ string_of_int !pk_ctr in
  let st = mk_var(sn,`:x86state`) in
  (FIRST_ASSUM(fun eq -> if concl eq = `mld_sk_rho skb = r` then
    FIRST_ASSUM(fun th ->
      try let _ = BYTES8_OFF_FACT `bot:int64` 5165 st th in
          ASSUME_TAC(REWRITE_RULE[GSYM mld_sk_rho; ETA_AX; eq] (BETA_RULE (MATCH_MP READ_BYTES_OF_BYTES8_OFF th)))
      with Failure _ -> NO_TAC)
    else NO_TAC)) g;;

let PK_NTT_BOUND : tactic =
  SUBGOAL_THEN `!j. j < 1024 ==> abs(ival(mld_polyvec_map mld_poly_ntt (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte) (128 + j))) j)) < &94279689` ASSUME_TAC THENL
   [MP_TAC(SPECL [`4`; `mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte) (128 + j))`] MLD_LAZY_POLYVEC_NTT_BOUND) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[mld_polyvec_unpack; mld_polyvec; MLD_LAZY_ETA_UNPACK_BOUND];
    ALL_TAC];;

let PK_RHO_CHUNKS : tactic = fun g ->
  let st = mk_var("s" ^ string_of_int !pk_ctr,`:x86state`) in
  let f = CONV_RULE(SIMD_SIMPLIFY_CONV []) o REWRITE_RULE[ETA_AX] in
  let at t = subst [st,`s:x86state`] t in
  (FIRST_ASSUM(fun th1 ->
    if lhs(concl th1) = at `read (memory :> bytes128 pk) s` then
      FIRST_ASSUM(fun th2 ->
        if lhs(concl th2) = at `read (memory :> bytes128 (word_add pk (word 16))) s`
        then ASSUME_TAC(MATCH_MP MLD_BYTES8_OF_CHUNKS2 (CONJ (f th1) (f th2)))
        else NO_TAC)
    else NO_TAC)) g;;

let PK_T0P = "mld_polyvec_pack 416 mld_polyt0_pack (mld_polyvec_map mld_poly_power2round_lo (mld_compute_t 4 mld_polyeta_unpack_2 96 r (mld_polyvec_map mld_poly_ntt (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\\j. (skb:num->byte) (128 + j)))) (\\j. (skb:num->byte) (512 + j))))";;

(* all 16-byte chunks of a byte string at a + k, as a fact about a + tk + 16 c *)
let PK_CHUNKS a k n f tk : tactic = fun g ->
  let sn = "s" ^ string_of_int !pk_ctr in
  let st = mk_var(sn,`:x86state`) in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "!c. c < %d ==> read (memory :> bytes128 (word_add %s (word (%s + 16 * c)))) %s = mld_chunk128 (%s) c" (n / 16) a tk sn f)) ASSUME_TAC THENL
   [X_GEN_TAC `c:num` THEN DISCH_TAC THEN REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    MP_TAC(BETA_RULE(ISPECL [parse_term (a ^ ":int64"); mk_small_numeral k; mk_small_numeral n; parse_term f; st; `c:num`] BYTES128_OF_BYTES8_OFF)) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; UNDISCH_TAC (parse_term (Printf.sprintf "c < %d" (n / 16))) THEN ARITH_TAC];
      DISCH_THEN ACCEPT_TAC];
    ALL_TAC]) g;;

let PK_CMP_CALL = 
  PK_SLICE "!j. j < 1664 ==> read (memory :> bytes8 (word_add sk (word (896 + j)))) @ = (skb:num->byte) (896 + j)" THEN
  PK_CHUNKS "sk" 896 1664 "\\j. (skb:num->byte) (896 + j)" "896" THEN
  PK_CHUNKS "bot" 6381 1664 PK_T0P "4909 + 1472" THEN
  PK_REGION "H_CMP" [`read R15 s`; `read RSP s`; `mld_chunk128 (\j. (skb:num->byte) (896 + j))`;
     parse_term ("mld_chunk128 (" ^ PK_T0P ^ ")"); `pc:num`];;

(* ------------------------------------------------------------------------- *)
(* The checks as the code combines them, against mld_pk_from_sk_valid.       *)
(* ------------------------------------------------------------------------- *)

let PK_CHK_OR_LEMMA = prove
 (`!a b c d e f g h:int32.
     word_zx(word_or ((((word 0 || a) || b) || c) || d) (word_or e (word_or f (word_or g h)))):byte = word 0 <=>
     word_zx(word_or ((((word 0 || a) || b) || c) || d) ((((word 0 || e) || f) || g) || h)):byte = word 0`,
  CONV_TAC WORD_BLAST);;

let PK44_T0P_STR = "mld_polyvec_pack 416 mld_polyt0_pack (mld_polyvec_map mld_poly_power2round_lo (mld_compute_t 4 mld_polyeta_unpack_2 96 r (mld_polyvec_map mld_poly_ntt (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\\j. (skb:num->byte) (128 + j)))) (\\j. (skb:num->byte) (512 + j))))";;

let PK44_VALID_STMT = parse_term(subst_tokens ["@T0P@",PK44_T0P_STR]
  "!(skb:num->byte) r (v0:int128) (v1:int128).
     mld_sk_rho skb = r /\\
     word_or v1 v0 = mld_or_fold (mld_chunk128 (\\j. skb(896 + j))) (mld_chunk128 (@T0P@)) 104
     ==> (word_zx (word_or (mld_polyvec_chknorm 4 (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\\j. skb(128 + j))) (word 3))
                  (word_or (mld_poly_chknorm (mld_polyeta_unpack_2 (\\j. skb(512 + j))) (word 3))
                  (word_or (mld_poly_chknorm (mld_polyeta_unpack_2 (\\j. skb(608 + j))) (word 3))
                  (word_or (mld_poly_chknorm (mld_polyeta_unpack_2 (\\j. skb(704 + j))) (word 3))
                           (mld_poly_chknorm (mld_polyeta_unpack_2 (\\j. skb(800 + j))) (word 3)))))):byte = word 0 /\\
          word_or v0 v1 = word 0 /\\
          num_of_bytelist(list_of_seq (mld_shake256_byte 1312
            (num_of_bytelist(list_of_seq (mld_pk_from_sk_pk 4 mld_polyeta_unpack_2 96 skb) 1312))) 64) =
          num_of_bytelist(list_of_seq (\\j. skb(64 + j)) 64)
          <=> mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2 96 skb)");;

let PK44_VALID = prove
 (PK44_VALID_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `mld_sk_rho (skb:num->byte) = r`)) THEN
  REWRITE_TAC[mld_pk_from_sk_valid] THEN
  BINOP_TAC THENL
   [REWRITE_TAC[mld_sk_s2; mld_sk_s1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    REWRITE_TAC[num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; mld_polyvec_chknorm] THEN
    REWRITE_TAC[PK_CHKNORM_UNPACK] THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    MATCH_ACCEPT_TAC PK_CHK_OR_LEMMA;
    ALL_TAC] THEN
  BINOP_TAC THENL
   [ONCE_REWRITE_TAC[WORD_OR_SYM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MLD_OR_FOLD_EQ_0; MLD_CT_MEMCMP_EQ_0; MLD_CHUNK128_EQ] THEN
    REWRITE_TAC[mld_pk_from_sk_t; mld_sk_s1] THEN
    REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    MESON_TAC[];
    REWRITE_TAC[PK_BYTELIST_EQ; MLD_CT_MEMCMP_EQ_0] THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* After the comparison of t0 (state s97): the facts for TAIL (pk as the     *)
(* bytes of mld_pk_from_sk_pk, tr and the result of the check of s1), TAIL, *)
(* the branch on the low byte of R13 as mld_pk_from_sk_valid, and the two     *)
(* paths to the return.                                                      *)
(* ------------------------------------------------------------------------- *)

let pk_state () = mk_var("s" ^ string_of_int !pk_ctr,`:x86state`);;
let pk_find p (asl,w) = concl(snd(find (fun (_,th) -> p (concl th)) asl));;

let PK_CMP_STRIP : tactic =
  TRY(FIRST_X_ASSUM(fun th -> if is_exists(concl th) && can (find_term (fun t -> t = `XMM1`)) (concl th)
                              then STRIP_ASSUME_TAC th else NO_TAC));;

(* pk: rho stored by the two MOVDQU, and t1 from mld_compute_pack_t0_t1 *)
let PK_PK_BYTES : tactic = fun g ->
  let st = pk_state () in
  let f = CONV_RULE(SIMD_SIMPLIFY_CONV []) o REWRITE_RULE[ETA_AX] in
  let at t = subst [st,`s:x86state`] t in
  (FIRST_ASSUM(fun th1 ->
    if can (term_match [] (at `!j. j < 32 ==> read (memory :> bytes8 (word_add pk (word j))) s = (f:num->byte) j`)) (concl th1) then
      FIRST_ASSUM(fun th2 ->
        let th2' = REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] th2 in
        if can (term_match [] (at `!j. j < 1280 ==> read (memory :> bytes8 (word_add pk (word(32 + j)))) s = (g:num->byte) j`)) (concl th2')
        then ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV) (MATCH_MP MLD_BYTES8_JOIN (CONJ th1 th2')))
        else NO_TAC)
    else NO_TAC) THEN
   SUBGOAL_THEN (at `!j. j < 1312 ==> read (memory :> bytes8 (word_add pk (word j))) s =
                     mld_pk_from_sk_pk 4 mld_polyeta_unpack_2 96 skb j`)
    ASSUME_TAC THENL
    [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
     FIRST_ASSUM(fun th -> if can (term_match [] (at `!j. j < 1312 ==> read (memory :> bytes8 (word_add pk (word j))) s = (f:num->byte) j`)) (concl th) && not(free_in `mld_pk_from_sk_pk` (concl th))
                           then REWRITE_TAC[MATCH_MP th (ASSUME `j < 1312`)] else NO_TAC) THEN
     REWRITE_TAC[mld_pk_from_sk_pk; mld_pk_from_sk_t; mld_sk_s1] THEN
     FIRST_ASSUM(fun th -> if concl th = `mld_sk_rho skb = r` then REWRITE_TAC[th] else NO_TAC) THEN
     CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN BETA_TAC THEN
     REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV);
     ALL_TAC] THEN
   FIRST_ASSUM(fun th -> if can (term_match [] (at `!j. j < 1312 ==> read (memory :> bytes8 (word_add pk (word j))) s = mld_pk_from_sk_pk 4 mld_polyeta_unpack_2 96 skb j`)) (concl th)
     then ASSUME_TAC(REWRITE_RULE[ETA_AX] (MATCH_MP READ_BYTES_OF_BYTES8 th)) else NO_TAC)) g;;

(* tr: the 64 bytes copied to bot + 5261 *)
let PK_TR_BYTES : tactic = fun g ->
  let st = pk_state () in
  (FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [st,`s:x86state`] `!j. j < 64 ==> read (memory :> bytes8 (word_add bot (word (5261 + j)))) s = (skb:num->byte) (64 + j)`)) (concl th)
    then ASSUME_TAC(BETA_RULE(MATCH_MP READ_BYTES_OF_BYTES8_OFF (CONV_RULE(ONCE_DEPTH_CONV ETA_CONV) th)))
    else NO_TAC)) g;;

(* the result of the check of s1, stored at bot + 5153 *)
let PK_CF4_TAC : tactic =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read (memory :> bytes32 (word_add bot (word 5153))) s = x`) (concl th)
    then REWRITE_RULE[WORD_ZX_ZX_32_64_32] th else th);;

let pk_reg_zx r (asl,w) =
  let st = pk_state () in
  let t = mk_comb(mk_comb(`read:(x86state,int64)component->x86state->int64`,mk_const(r,[])),st) in
  rand(rhs(pk_find (fun c -> is_eq c && lhs c = t) (asl,w)));;

let PK_TAIL_CALL : tactic = fun g ->
  let st = pk_state () in
  let cf4 = rhs(pk_find (fun c -> is_eq c && lhs c =
     mk_comb(`read (memory :> bytes32 (word_add bot (word 5153)))`,st)) g) in
  let cs = map (fun r -> pk_reg_zx r g) ["R14"; "R12"; "R13"; "RBX"] in
  PK_REGION "H_TAIL"
   ([`read RSP s`; `pk:int64`; `pc:num`;
     `num_of_bytelist(list_of_seq (mld_pk_from_sk_pk 4 mld_polyeta_unpack_2 96 skb) 1312)`;
     `num_of_bytelist(list_of_seq (\j. (skb:num->byte)(64 + j)) 64)`;
     `v0:int128`; `v1:int128`; `v2:int128`; `v3:int128`] @ cs @ [cf4]) g;;

(* a name for the value of R13 after the region, and the check as valid *)
let PK_R13_GHOST : tactic = fun g ->
  let st = pk_state () in
  let t = mk_comb(`read R13`, st) in
  let y = `y:int64` in
  (X_CHOOSE_TAC `r13v:int64` (EXISTS (mk_exists(y,mk_eq(t,y)),t) (REFL t)) THEN
   FIRST_ASSUM(fun eq -> if concl eq = mk_eq(t,`r13v:int64`) then
     RULE_ASSUM_TAC(fun th -> if concl th = concl eq then th else REWRITE_RULE[eq] th)
   else NO_TAC)) g;;

let PK_VALID_TAC : tactic =
  FIRST_ASSUM(fun rth -> if concl rth = `mld_sk_rho skb = r` then
    FIRST_ASSUM(fun fth -> if can (term_match [] `word_or (v1:int128) v0 = mld_or_fold a b 104`) (concl fth) then
      ASSUME_TAC(MATCH_MP PK44_VALID (CONJ rth fth)) else NO_TAC) else NO_TAC);;

let PK44_VALIDT = `mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2 96 skb`;;

(* the condition of the branch after the test of R13 is valid *)
let PK_BRANCH_TAC : tactic = fun (asl,w) ->
  let st = pk_state () in
  let pcv = rhs(pk_find (fun c -> is_eq c && lhs c = mk_comb(`read RIP`,st)) (asl,w)) in
  let cond = rand(rator(rator pcv)) in
  (SUBGOAL_THEN (mk_iff(cond,PK44_VALIDT)) (LABEL_TAC "CHECK") THENL
    [REWRITE_TAC[WORD_VAL_MOD_256; VAL_EQ_0] THEN
     FIRST_ASSUM(fun th -> if is_iff(concl th) && rand(concl th) = PK44_VALIDT then REWRITE_TAC[GSYM th] else NO_TAC) THEN
     FIRST_ASSUM(fun th -> if is_iff(concl th) && lhand(concl th) = `word_zx (r13v:int64):byte = word 0` then REWRITE_TAC[GSYM th] else NO_TAC) THEN
     SPEC_TAC(`r13v:int64`,`x:int64`) THEN GEN_TAC THEN BITBLAST_TAC;
     USE_THEN "CHECK" (fun th -> RULE_ASSUM_TAC(fun t -> if pfs_pcev t then REWRITE_RULE[th] t else t))]) (asl,w);;

let PK_MEMSET_CALL : tactic = fun g ->
  let plt = layout "plt_memset" and got = layout "got_memset" in
  let n = !pk_ctr in
  pk_ctr := n + 2;
  (LIBC_PLT_TAC PK44_EXEC plt got n THEN
   REMOVE_THEN "H_MEMSET" (fun th ->
     LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true PK44_EXEC th
       [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`; `read RSP s`;
        `read (memory :> bytes64 (read RSP s)) s`] (n + 2) THENL
     [PK_EXISTS_E2_TAC; LABEL_TAC "H_MEMSET" th]) THEN RSP_NORM_TAC) g;;

let PK_CL_CALL : tactic =
  MAP_EVERY (fun r ->
    SUBGOAL_THEN (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                                  `word_add bot (word 4901):int64,7272`),r)) ASSUME_TAC THENL
     [EXPAND_TAC "bot" THEN NONOVERLAPPING_TAC; ALL_TAC])
   [`word pc:int64,libmldsa_size`; `word(pc + got_memset):int64,8`; `ea:int64,el:num`;
    `word_add stackpointer (word 12204):int64,56`] THEN
  PK_REGION "H_CL"
   [`read RSP s`; `word_add stackpointer (word 12204):int64`; `read RBX s`; `pc:num`;
    `rbx_init:int64`; `r12_init:int64`; `r13_init:int64`; `r14_init:int64`;
    `r15_init:int64`; `rbp_init:int64`; `returnaddress:int64`];;

let PK_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let PK_VALID_PATH_TAC : tactic = fun g ->
  pk_ctr := 100; (PK_STEPS 1 THEN PK_CL_CALL THEN PK_FINAL_TAC) g;;

let PK_INVALID_PATH_TAC : tactic = fun g ->
  pk_ctr := 100;
  (PK_STEPS 4 THEN PK_MEMSET_CALL THEN
   (fun g -> let st = pk_state () in
     FIRST_X_ASSUM(fun th -> let c = concl th in
       if is_forall c && free_in st c && can (find_term (fun t -> t = `1312`)) c &&
          can (find_term (fun t -> t = `pk:int64`)) c && can (find_term (fun t -> t = `word_zx:int64->byte` || t = `word_zx:int32->byte` || t = `word_zx:byte->byte`)) c &&
          not (free_in `mld_pk_from_sk_pk` c)
       then ASSUME_TAC(REWRITE_RULE[WORD_ZX_0] th) else NO_TAC) g) THEN
   PK_STEPS 2 THEN PK_CL_CALL THEN PK_FINAL_TAC) g;;

(* ------------------------------------------------------------------------- *)
(* The whole function.                                                       *)
(* ------------------------------------------------------------------------- *)

let PK44_FULL_TAC =
  (PK44_ASSUME_TAC THEN PK44_SETUP_TAC) THEN
  (FULL_INIT_TAC THEN
   YMM_GHOST_TAC `s0:x86state` ["YMM0","y0"; "YMM1","y1"; "YMM2","y2"; "YMM3","y3"] THEN
   GLUE_LOAD128_TAC `sk:int64` [0; 16; 32; 48; 64; 80; 96; 112] THEN
   PK_RESET THEN PK_STEPS 8 THEN REALIGN_RSP_TAC THEN PK_STEPS 21) THEN
  (GLUE_STORE_TAC `bot:int64` THEN
   PK_SUBGOAL "!j. j < 32 ==> read (memory :> bytes8 (word_add bot (word (5165 + j)))) @ = (skb:num->byte) j" GLUE_BYTES_FINAL_TAC THEN
   PK_SUBGOAL "!j. j < 32 ==> read (memory :> bytes8 (word_add bot (word (5325 + j)))) @ = (skb:num->byte) (32 + j)" GLUE_BYTES_FINAL_TAC THEN
   PK_SUBGOAL "!j. j < 64 ==> read (memory :> bytes8 (word_add bot (word (5261 + j)))) @ = (skb:num->byte) (64 + j)" GLUE_BYTES_FINAL_TAC THEN
   DISCARD_MATCHING_ASSUMPTIONS
    [`read (memory :> bytes8 (word_add bot (word n))) s29 = x`;
     `read (memory :> bytes128 a) s29 = x`] THEN
   PK_STEPS 4 THEN
   PK_SLICE "!j. j < 96 ==> read (memory :> bytes8 (word_add sk (word (128 + j)))) @ = (skb:num->byte) (128 + j)") THEN
  (PK_CALL "H_UNPACK" (PK_UNPACK_ARGS 0) THEN
   PK_STEPS 3 THEN PK_SLICE_S1 1 THEN PK_CALL "H_UNPACK" (PK_UNPACK_ARGS 1) THEN
   PK_STEPS 3 THEN PK_SLICE_S1 2 THEN PK_CALL "H_UNPACK" (PK_UNPACK_ARGS 2) THEN
   PK_STEPS 3 THEN PK_SLICE_S1 3 THEN PK_CALL "H_UNPACK" (PK_UNPACK_ARGS 3)) THEN
  (PK_S1_JOIN) THEN
  (PK_STEPS 3 THEN
   PK_CALL "H_CHKL" [`read RDI s`; `mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte) (128 + j))`; `read RSI s`] THEN
   PK_STEPS 4 THEN PK_SLICE_S2 0 THEN PK_CALL "H_UNPACK" (PK_S2_UNPACK_ARGS 0) THEN PK_S2_SCAN 0) THEN
  (PK_STEPS 3 THEN PK_SLICE_S2 1 THEN PK_CALL "H_UNPACK" (PK_S2_UNPACK_ARGS 1) THEN PK_S2_SCAN 1 THEN
   PK_STEPS 4 THEN PK_SLICE_S2 2 THEN PK_CALL "H_UNPACK" (PK_S2_UNPACK_ARGS 2) THEN PK_S2_SCAN 2 THEN
   PK_STEPS 3 THEN PK_SLICE_S2 3 THEN PK_CALL "H_UNPACK" (PK_S2_UNPACK_ARGS 3) THEN PK_S2_SCAN 3) THEN
  (PK_STEPS 2 THEN PK_NTT_CALL 0 THEN PK_STEPS 2 THEN PK_NTT_CALL 1 THEN
   PK_STEPS 2 THEN PK_NTT_CALL 2 THEN PK_STEPS 2 THEN PK_NTT_CALL 3 THEN PK_NTT_JOIN) THEN
  (CHUNK128_TAC `bot:int64` 5165 [0; 1] THEN
   (fun g -> YMM_GHOST_TAC (mk_var("s" ^ string_of_int !pk_ctr,`:x86state`)) ["YMM0","y0_r"; "YMM1","y1_r"] g) THEN
   PK_STEPS 5 THEN PK_RHO_FACT THEN PK_RHO_CHUNKS) THEN
  (PK_STEPS 6 THEN
   PK_SLICE "!j. j < 384 ==> read (memory :> bytes8 (word_add sk (word (512 + j)))) @ = (skb:num->byte) (512 + j)" THEN
   PK_NTT_BOUND THEN
   PK_CALL "H_CPT" [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
      `mld_polyvec_map mld_poly_ntt (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte) (128 + j)))`;
      `\j. (skb:num->byte) (512 + j)`; `r:num`]) THEN
  (PK_CMP_CALL) THEN
  PK_CMP_STRIP THEN PK_PK_BYTES THEN PK_TR_BYTES THEN PK_CF4_TAC THEN
  PK_TAIL_CALL THEN PK_R13_GHOST THEN PK_VALID_TAC THEN
  PK_STEPS 2 THEN PK_BRANCH_TAC THEN
  PFS_CASES_TAC PK44_VALIDT THENL [PK_VALID_PATH_TAC; PK_INVALID_PATH_TAC];;

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  PK44_FULL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
