(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing with the secret key, all the attempts (ML-DSA-65, clang 23 -O3    *)
(* mono reduced-RAM): the proof (see signature_internal_65_spec.ml).         *)
(*                                                                           *)
(* An attempt is SI65_ATT of signature_internal_65_stages.ml, at the frame   *)
(* fp of the function. The proof of the whole function is that of            *)
(* signature_internal_44_proof.ml with the offsets of this function: the     *)
(* prologue (the saved registers, the frame fp = (sp - 12960) rounded down   *)
(* to 32 bytes, that is stackpointer + b with b = 1504 if the bottom         *)
(* stackpointer of the stack region is a multiple of 32 and 1488 otherwise,  *)
(* the probe of the stack page by page, the canary, the inlined unpack_sk,   *)
(* mu with mld_H65 or copied from m when ext is not 0, rho'' with mld_H65    *)
(* and the setup of the slots and registers of the attempts), then the loop  *)
(* over the attempts (ENSURES_EVENTS_WHILE_UP2_TAC up to mld_sign_natt       *)
(* 13106 18 D), each one SI65_ATT, after the last failed one the zeroing of  *)
(* the signature with memset and -4 in w19, and the epilogue (the zeroing of *)
(* the pointers into the secret key, of the buffers with memset and of the   *)
(* 256 bytes of the copies of the key, the check of the canary, the          *)
(* restored registers and x1..x18 cleared). The proof is done once for each  *)
(* value of b.                                                               *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;
needs "arm/proofs/utils/mldsa_native_verify.ml";;
needs "arm/proofs/utils/mldsa_native_top.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_65_stages.ml";;

(* ------------------------------------------------------------------------- *)
(* The facts about the attempts that the main proof needs, for D =           *)
(* mld_sign_declass_65 and its number of attempts (as in the gcc proof).     *)
(* ------------------------------------------------------------------------- *)

let SI65_DECLASS_FACTS = prove
 (`!skb MU RND.
        0 < mld_sign_natt 13106 18 (mld_sign_declass_65 skb MU RND) /\
        mld_sign_natt 13106 18 (mld_sign_declass_65 skb MU RND) <= 13106 /\
        (!i. i < mld_sign_natt 13106 18 (mld_sign_declass_65 skb MU RND)
             ==> mld_sign_declass_65 skb MU RND i =
                 mld_sign_attempt_declass 6 5 48 49 mld_poly_uniform_gamma1_19
                  524092 261692 261888
                  (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
                  128 mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55
                  (mld_polyvec_matrix_expand 5 (mld_sk_rho skb))
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 128 mld_polyeta_unpack_4
                      (\j. skb(128 + j))))
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 128 mld_polyeta_unpack_4
                      (\j. skb(768 + j))))
                  (mld_polyvec_map mld_poly_ntt
                    (mld_polyvec_unpack 416 mld_polyt0_unpack
                      (\j. skb(1536 + j))))
                  MU (mld_sign_rhoprime (\j. skb(32 + j)) RND MU) (5 * i)) /\
        (!i. i + 1 < mld_sign_natt 13106 18 (mld_sign_declass_65 skb MU RND)
             ==> ~(FST(SND(mld_sign_declass_65 skb MU RND i)) = 18)) /\
        (mld_sign_ok_65 skb MU RND <=>
         FST(SND(mld_sign_declass_65 skb MU RND
                  (mld_sign_natt 13106 18 (mld_sign_declass_65 skb MU RND) -
                   1))) = 18) /\
        (~mld_sign_ok_65 skb MU RND
         ==> mld_sign_natt 13106 18 (mld_sign_declass_65 skb MU RND) =
             13106) /\
        mld_sign_sig_65 skb MU RND =
        (if mld_sign_ok_65 skb MU RND
         then mld_sign_attempt_sig 6 5 48 49 mld_poly_uniform_gamma1_19
               mld_polyz_pack_19 640
               (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
               mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55
               (mld_polyvec_matrix_expand 5 (mld_sk_rho skb))
               (mld_polyvec_map mld_poly_ntt
                 (mld_polyvec_unpack 128 mld_polyeta_unpack_4
                   (\j. skb(128 + j))))
               (mld_polyvec_map mld_poly_ntt
                 (mld_polyvec_unpack 128 mld_polyeta_unpack_4
                   (\j. skb(768 + j))))
               (mld_polyvec_map mld_poly_ntt
                 (mld_polyvec_unpack 416 mld_polyt0_unpack
                   (\j. skb(1536 + j))))
               MU (mld_sign_rhoprime (\j. skb(32 + j)) RND MU)
               (5 * (mld_sign_natt 13106 18 (mld_sign_declass_65 skb MU RND) -
                     1))
         else \t. word 0) /\
        (mld_sign_terminates_65 skb MU RND
         ==> !i. i < mld_sign_natt 13106 18 (mld_sign_declass_65 skb MU RND)
                 ==> mld_poly_challenge_terminates 49 48
                      (FST(mld_sign_declass_65 skb MU RND i)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_sign_declass_65; mld_sign_ok_65; mld_sign_sig_65;
              mld_sign_terminates_65] THEN
  MP_TAC(SPECL
   [`6`; `5`; `mld_polyeta_unpack_4`; `128`; `48`; `49`;
    `mld_poly_uniform_gamma1_19`; `524092`; `261692`; `261888`;
    `mld_polyw1_pack_32 o mld_poly_decompose_hi_32`; `128`;
    `mld_poly_decompose_lo_32`; `mld_polyvec_make_hint_32`; `55`; `13106`;
    `skb:num->byte`; `MU:num`; `RND:num`] SIGN_NATT_DECLASS) THEN
  CONV_TAC(LAND_CONV(LAND_CONV(RATOR_CONV(RAND_CONV NUM_REDUCE_CONV)))) THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL
   [`6`; `5`; `mld_polyeta_unpack_4`; `128`; `48`; `49`;
    `mld_poly_uniform_gamma1_19`; `524092`; `261692`; `261888`;
    `mld_polyw1_pack_32 o mld_poly_decompose_hi_32`; `128`;
    `mld_poly_decompose_lo_32`; `mld_polyvec_make_hint_32`; `55`; `13106`;
    `skb:num->byte`; `MU:num`; `RND:num`] SIGN_NATTEMPTS_PROPS) THEN
  CONV_TAC(LAND_CONV(LAND_CONV NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV))) THEN
  ABBREV_TAC
   `N = mld_sign_nattempts 6 5 mld_polyeta_unpack_4 128 48 49
         mld_poly_uniform_gamma1_19 524092 261692 261888
         (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
         mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55 13106
         skb MU RND` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mld_sign_declass; mld_sign_sig; mld_sign_terminates] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mld_sk_s1; mld_sk_s2; mld_sk_t0] THEN SIGN_NUMS_TAC THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `i < N` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `i + 1 < N` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SIGN_ATTEMPT_DECLASS_REJ] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      can (term_match [] `!i. i + 1 < N ==> P i`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[mld_sign_rejn; mld_sk_s1; mld_sk_s2; mld_sk_t0] THEN
    SIGN_NUMS_TAC THEN REWRITE_TAC[];
    SUBGOAL_THEN `N - 1 < N` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `0 < N` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SIGN_ATTEMPT_DECLASS_REJ] THEN
    REWRITE_TAC[mld_sign_rejn; mld_sk_s1; mld_sk_s2; mld_sk_t0] THEN
    SIGN_NUMS_TAC THEN REWRITE_TAC[];
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Bytes of the secret key and of m as the 128-bit loads of the inlined      *)
(* unpack_sk and of the copy of mu read them, and back.                      *)
(* ------------------------------------------------------------------------- *)

let SI65_SK_CHUNK = prove
 (`!(sk:int64) (skb:num->byte) k i (s:armstate).
     (!j. j < 4032 ==> read (memory :> bytes8 (word_add sk (word j))) s = skb j) /\
     k + 16 * i + 16 <= 4032
     ==> read (memory :> bytes128 (word_add sk (word (k + 16 * i)))) s =
         mld_chunk128 (\j. skb (k + j)) i`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`word_add sk (word k):int64`; `4032 - k`; `\j. (skb:num->byte)(k + j)`;
                `s:armstate`; `i:num`] BYTES128_OF_BYTES8) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN BETA_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    REWRITE_TAC[ADD_ASSOC]]);;

let SI65_SKCHUNK_TAC k i st =
  MP_TAC(SPECL [`sk:int64`; `skb:num->byte`; mk_small_numeral k; mk_small_numeral i; st]
               SI65_SK_CHUNK) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES; ETA_AX] THEN DISCH_TAC;;

let SI65_BYTES64_OF_CHUNKS = prove
 (`!a:int64 (f:num->byte) s.
     read (memory :> bytes128 a) s = mld_chunk128 f 0 /\
     read (memory :> bytes128 (word_add a (word 16))) s = mld_chunk128 f 1 /\
     read (memory :> bytes128 (word_add a (word 32))) s = mld_chunk128 f 2 /\
     read (memory :> bytes128 (word_add a (word 48))) s = mld_chunk128 f 3
     ==> read (memory :> bytes(a,64)) s = num_of_bytelist(list_of_seq f 64)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mld_chunk128 (f:num->byte) 2 = mld_chunk128 (\j. f(32 + j)) 0 /\
                mld_chunk128 f 3 = mld_chunk128 (\j. f(32 + j)) 1`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mld_chunk128] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ARITH_RULE `!k. 16 * 2 + k = 32 + 16 * 0 + k`;
                ARITH_RULE `!k. 16 * 3 + k = 32 + 16 * 1 + k`];
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `f:num->byte`; `s:armstate`] MLD_BYTES32_OF_CHUNKS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`word_add a (word 32):int64`; `\j. (f:num->byte)(32 + j)`; `s:armstate`]
               MLD_BYTES32_OF_CHUNKS) THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add (a:int64) (word 32)) (word 16) =
                         word_add a (word 48)`] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[LIST_OF_SEQ_ADD_GEN; NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ]);;

(* ------------------------------------------------------------------------- *)
(* The stack probe of the prologue (as in verify_internal_44_proof.ml): the  *)
(* stack pointer goes down by 4096 at a time to below the frame and is       *)
(* compared (signed) with x9 = the frame. With 32768 <= val(stackpointer +   *)
(* 14624) < 2^63, the values of the signed comparisons are those of the      *)
(* offsets.                                                                  *)
(* ------------------------------------------------------------------------- *)

let SI65_VAL_ADD = prove
 (`!(sp:int64) n m. n <= val(word_add sp (word n):int64) /\
                    val(word_add sp (word n):int64) < 2 EXP 63 /\ m <= n
    ==> val(word_add sp (word m):int64) = val sp + m /\ val sp + m < 2 EXP 63`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n < 2 EXP 63` ASSUME_TAC THENL [ASM_MESON_TAC[LET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `m < 2 EXP 63` ASSUME_TAC THENL [ASM_MESON_TAC[LET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word n:int64) = n /\ val(word m:int64) = m` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`sp:int64`; `word n:int64`] VAL_WORD_ADD_CASES) THEN
  MP_TAC(ISPECL [`sp:int64`; `word m:int64`] VAL_WORD_ADD_CASES) THEN
  MP_TAC(SPEC `sp:int64` VAL_BOUND_64) THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_64]) THEN
  REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `val(sp:int64) + n < 2 EXP 64` THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    UNDISCH_TAC `n <= val(word_add sp (word n):int64)` THEN
    UNDISCH_TAC `val(word_add sp (word n):int64) < 2 EXP 63` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let SI65_IVAL_ADD = prove
 (`!s:int64 k. val s + k < 2 EXP 63 ==> ival(word_add s (word k)) = &(val s) + &k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add s (word k):int64) = val s + k` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `k < 2 EXP 64` (fun th -> SIMP_TAC[th; MOD_LT]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add s (word k):int64) < 2 EXP (dimindex(:64) - 1)`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[IVAL_EQ_VAL; INT_OF_NUM_ADD]);;

(*** val stackpointer + 14624 < 2^63 and 18144 <= val stackpointer ***)

let SI65_SP_BOUNDS_TAC =
  MP_TAC(SPECL [`stackpointer:int64`; `14624`; `14624`] SI65_VAL_ADD) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `18144 <= val(stackpointer:int64)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC];;

let SI65_SP_PC_CONV =
  REWRITE_CONV[VERIF_PTR_SUB; INT_ARITH `!v a b:int. (v + a) - (v + b) = a - b`;
               INT_ARITH `!v a b:int. (v + a) - (v - b) = a + b`;
               INT_ARITH `!v a b:int. (v - a) - (v + b) = --(a + b)`;
               INT_ARITH `!v a b:int. (v - a) - (v - b) = b - a`] THENC
  DEPTH_CONV WORD_RED_CONV THENC
  REWRITE_CONV[INT_OF_NUM_EQ; INT_OF_NUM_LT; ARITH_EQ; ARITH_LT; ARITH_LE;
               INT_LT_REFL; INT_OF_NUM_LE] THENC
  DEPTH_CONV INT_RED_CONV THENC REWRITE_CONV[];;

let SI65_NEGSUB = WORD_RULE `word_sub (s:int64) y = word_add s (word_neg y)`;;

let SI65_NEGADD_CONV tm =
  match tm with
    Comb(Comb(Const("word_add",_),s),Comb(Const("word",_),k))
      when is_numeral k && type_of tm = `:int64` &&
           dest_numeral k >=/ ((Num.num_of_int 2) **/ (Num.num_of_int 63)) ->
      let m = ((Num.num_of_int 2) **/ (Num.num_of_int 64)) -/ dest_numeral k in
      let rhs_tm = mk_comb(mk_comb(`word_sub:int64->int64->int64`,s),
                           mk_comb(`word:num->int64`,mk_numeral m)) in
      prove(mk_eq(tm,rhs_tm),
            REWRITE_TAC[SI65_NEGSUB] THEN
            CONV_TAC(RAND_CONV(RAND_CONV WORD_REDUCE_CONV)) THEN REFL_TAC)
  | _ -> failwith "SI65_NEGADD_CONV";;

let SI65_PROBE_PC_TAC =
  let isadd t = can (term_match [] `ival(word_add (stackpointer:int64) (word k))`) t
  and issub t = can (term_match [] `ival(word_sub (stackpointer:int64) (word k))`) t in
  W(fun (asl,w) ->
    let hyps = end_itlist CONJ (map snd (filter (fun (_,th) ->
      mem (concl th) [`val(stackpointer:int64) + 14624 < 2 EXP 63`;
                      `18144 <= val(stackpointer:int64)`]) asl)) in
    let side tm = MP (ARITH_RULE(mk_imp(concl hyps,tm))) hyps in
    RULE_ASSUM_TAC(fun th ->
      let c = concl th in
      if is_eq c && is_comb(lhand c) &&
         rator(lhand c) = `read PC:armstate->int64` &&
         free_in `stackpointer:int64` (rhs c)
      then
        let th1 = CONV_RULE(RAND_CONV(REWRITE_CONV[VERIF_PTR_SUB] THENC
                                      DEPTH_CONV WORD_RED_CONV THENC
                                      DEPTH_CONV SI65_NEGADD_CONV)) th in
        let ts = setify(find_terms (fun t -> isadd t || issub t) (concl th1)) in
        let eqs = map (fun t ->
          let k = rand(rand(rand t)) in
          if isadd t then
            MP (SPECL [`stackpointer:int64`; k] SI65_IVAL_ADD)
               (side (subst [k,`k:num`] `val(stackpointer:int64) + k < 2 EXP 63`))
          else
            MP (SPECL [`stackpointer:int64`; k] IVAL_SP_SUB)
               (side (subst [k,`k:num`]
                 `k <= val(stackpointer:int64) /\ val stackpointer < 2 EXP 63 /\
                  k < 2 EXP 63`))) ts in
        CONV_RULE(RAND_CONV(REWRITE_CONV eqs THENC SI65_SP_PC_CONV)) th1
      else th));;

let SI65_PROBE_TAC exec n =
  ARM_STEPS_TAC exec [n] THEN SI65_PROBE_PC_TAC;;

(* ------------------------------------------------------------------------- *)
(* The main proof. The events are those of the prologue (one function for    *)
(* each case of ext), then attempt i for each i < N, the number of attempts  *)
(* (mld_sign_natt 13106 18 D, with D what is declassified): an attempt that  *)
(* is followed by another (i + 1 < N), the successful last one, or the last  *)
(* one after which the signature is zeroed (13106 attempts, all rejected),   *)
(* then those of the epilogue; all of it twice, for the two positions of     *)
(* the frame, stackpointer + 1504 if stackpointer is a multiple of 32 and    *)
(* stackpointer + 1488 otherwise.                                            *)
(* ------------------------------------------------------------------------- *)

let SI65_EXEC = MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;
let SI65_MCODE = mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc;;

let SI65_TEMPLATE =
  let case x =
    let f n = "(f_ev_" ^ n ^ x ^ " sig m mlen pre prelen rnd sk ext rh D guard mf mc pc " ^
              "stackpointer returnaddress)" in
    let fi n = "(f_ev_" ^ n ^ x ^ " sig m mlen pre prelen rnd sk ext rh D guard mf mc pc " ^
               "stackpointer returnaddress i)" in
    "APPEND " ^ f "epil" ^
    " (APPEND (ENUMERATEL (mld_sign_natt 13106 18 D)" ^
    " (\\i. if i + 1 < mld_sign_natt 13106 18 D then " ^ fi "cont" ^
    " else if FST(SND(D i)) = 18 then " ^ fi "succ" ^ " else " ^ fi "exh" ^ "))" ^
    " (if word_zx ext = (word 0:int32) then " ^ f "prolh" ^ " else " ^ f "prolx" ^ "))" in
  parse_term(
   "\\(sig:int64) (m:int64) (mlen:num) (pre:int64) (prelen:num) (rnd:int64)
     (sk:int64) (ext:int64) (rh:num)
     (D:num->num#num#(num->int32)#(num->byte)) (guard:int64) (mf:int64)
     (mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
     if aligned 32 stackpointer then " ^ case "a" ^ " else " ^ case "u" ^
   " :(uarch_event)list");;

(*** The callee-saved registers, saved at stackpointer + 14464 .. 14623 ***)

let SI65_SAVED_FACTS =
  String.concat " /\\\n" (map (fun (r,k) ->
     Printf.sprintf
      "read (memory :> bytes64 (word_add stackpointer (word %d))) s = %s" k r)
   ["d15_init",14464; "d14_init",14472; "d13_init",14480; "d12_init",14488;
    "d11_init",14496; "d10_init",14504; "d9_init",14512; "d8_init",14520;
    "x29_init",14528; "returnaddress",14536; "x28_init",14544;
    "x27_init",14552; "x26_init",14560; "x25_init",14568; "x24_init",14576;
    "x23_init",14584; "x22_init",14592; "x21_init",14600; "x20_init",14608;
    "x19_init",14616]);;

(*** A term with fp for the frame, at the frame stackpointer + b ***)

let SI65_FP_RULE b tm =
  let fpb = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                    mk_comb(`word:num->int64`,mk_small_numeral b)) in
  rhs(concl(REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))
             (subst [fpb,`fp:int64`] tm)));;

let SI65_RHOP = `mld_sign_rhoprime (\j. (skb:num->byte)(32 + j)) RND MU`;;

(* ------------------------------------------------------------------------- *)
(* The invariant of the loop over the attempts: the saved registers, the     *)
(* canary, the facts that an attempt needs (the setup registers and slots,   *)
(* rho at fp + 1568, mu at fp + 1728, rho'' at fp + 1792, the secret key);   *)
(* before attempt i its number in w10; after the last attempt the result in  *)
(* w19 and the signature.                                                    *)
(* ------------------------------------------------------------------------- *)

(*** SI65_HEAD_PRE but x19, which holds a constant during the attempts and ***)
(*** the result after them                                                  ***)

let SI65_INV_PRE =
 "read SP s = fp /\\
  read X20 s = word_add fp (word 10816) /\\
  read X26 s = word 18446744073701171199 /\\
  read X28 s = word_add fp (word 10824) /\\
  read (memory :> bytes64 (word_add fp (word 56))) s = word_add fp (word 1568) /\\
  read (memory :> bytes64 (word_add fp (word 328))) s = word_add fp (word 9036) /\\
  read (memory :> bytes64 (word_add fp (word 336))) s = word_add fp (word 8012) /\\
  read (memory :> bytes64 (word_add fp (word 344))) s = word_add fp (word 9024) /\\
  read (memory :> bytes64 (word_add fp (word 408))) s = word_add fp (word 10057) /\\
  read (memory :> bytes64 (word_add fp (word 440))) s = word_add fp (word 1792) /\\
  read (memory :> bytes128 (word_add fp (word 368))) s =
  word 339618401959998730991157055895298383871 /\\
  read (memory :> bytes (word_add fp (word 1568),32)) s = rho /\\
  read (memory :> bytes (word_add fp (word 1728),64)) s = MU /\\
  read (memory :> bytes (word_add fp (word 1792),64)) s = RHO /\\
  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
  read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev";;

let SI65_INV b =
  let body = parse_term(
   "\\i s.
     read SP s = fp /\\
     read X29 s = word_add stackpointer (word 14528) /\\\n" ^ SI65_SAVED_FACTS ^ " /\\
     read (memory :> bytes64 (word_add fp (word 12952))) s = canary /\\
     read (memory :> bytes64 guard) s = canary /\\\n" ^ SI65_INV_PRE ^ " /\\\n" ^
     SI65_SLOT_FACTS [24,8000; 32,6976; 40,5952; 48,4928; 320,2888; 352,12265; 360,2880] ^
   "read (memory :> bytes64 (word_add fp (word 64))) s = sig /\\
     read (memory :> bytes64 (word_add fp (word 16))) s = word_add sig (word 3248) /\\
     read (memory :> bytes64 (word_add fp (word 448))) s = word_add sk (word 768) /\\
     read (memory :> bytes64 (word_add fp (word 480))) s = word_add sk (word 1536) /\\
     read (memory :> bytes64 (word_add fp (word 512))) s = word_add sk (word 128) /\\
     (!j. j < 4032 ==> read (memory :> bytes8 (word_add sk (word j))) s = skb j) /\\
     (i < mld_sign_natt 13106 18 D
      ==> read X10 s = word i /\\ read X19 s = word 252236767799803904) /\\
     (i = mld_sign_natt 13106 18 D
      ==> read X19 s =
          (if mld_sign_ok_65 skb MU RND then word 0 else word 4294967292) /\\
          (!t. t < 3309
               ==> read (memory :> bytes8 (word_add sig (word t))) s =
                   mld_sign_sig_65 skb MU RND t))") in
  SI65_FP_RULE b (subst [`rh:num`,`rho:num`; SI65_RHOP,`RHO:num`] body);;

(* ------------------------------------------------------------------------- *)
(* The start: the callees as assumptions, the template, the stack pointer at *)
(* the bottom of the stack region, the abbreviations rh and D (arguments of  *)
(* the events), mu, the canary, the preserved registers and the facts about  *)
(* the attempts.                                                             *)
(* ------------------------------------------------------------------------- *)

let SI65_START_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcs = CONJ_PAIR th in
    SI65_ASSUME_CALLEE_TAILED_TAC (MP (SPEC_ALL SI65_ATT) th) "H_ATT" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
      (MATCH_MP MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL mcs)
      "H_H" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] ms) "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC SI65_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `m:int64`; `mlen:num`;
    `pre:int64`; `prelen:num`; `rnd:int64`; `sk:int64`; `ext:int64`;
    `skb:num->byte`; `M:num`; mk_var("PRE",`:num`); `RND:num`; `MU:num`;
    `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 14624 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  ABBREV_TAC `rh = mld_sk_rho skb` THEN
  ABBREV_TAC `D = mld_sign_declass_65 skb MU RND` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SI65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `MU = (if p then a else b)`) (concl th))) THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 14624):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init") (mk_const(r,[]))) (19--29) THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_DREG_TAC ("d"^string_of_int n^"_init")
     (mk_const("D"^string_of_int n,[]))) (8--15) THEN
  MP_TAC(SPECL [`skb:num->byte`; `MU:num`; `RND:num`] SI65_DECLASS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SI65_SP_BOUNDS_TAC;;

(* ------------------------------------------------------------------------- *)
(* The frame: x9 = (sp - 12960) rounded down to 32 bytes, with sp =          *)
(* stackpointer + 14464 after the pushes, is stackpointer + 1504 or + 1488,  *)
(* aligned to 32 in both cases, and its top fp + 12960 does not wrap (the    *)
(* bound that the attempts state).                                           *)
(* ------------------------------------------------------------------------- *)

let SI65_BUF_TAC =
  FIRST_ASSUM(fun a16 ->
    if concl a16 <> `aligned 16 (stackpointer:int64)` then NO_TAC else
    let th = MP (SPEC `stackpointer:int64` (MLD_WRAP_BUFFER_RULE `1504`)) a16 in
    FIRST_ASSUM(fun cth ->
      if concl cth = `aligned 32 (stackpointer:int64)` ||
         concl cth = `~aligned 32 (stackpointer:int64)`
      then RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_RULE[cth] th])
      else NO_TAC));;

let SI65_FP_ALIGNED = prove
 (`!sp:int64. aligned 16 sp
              ==> aligned 32 (word_add sp (word (if aligned 32 sp then 1504 else 1488)))`,
  REWRITE_TAC[MLD_WRAP_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let SI65_FP_ALIGNED_TAC =
  FIRST_ASSUM(fun a16 ->
    if concl a16 <> `aligned 16 (stackpointer:int64)` then NO_TAC else
    let th = MP (SPEC `stackpointer:int64` SI65_FP_ALIGNED) a16 in
    FIRST_ASSUM(fun cth ->
      if concl cth = `aligned 32 (stackpointer:int64)` ||
         concl cth = `~aligned 32 (stackpointer:int64)`
      then ASSUME_TAC(REWRITE_RULE[cth] th)
      else NO_TAC));;

let SI65_FP_BOUND_TAC b =
  let fpb = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                    mk_comb(`word:num->int64`,mk_small_numeral b)) in
  let goal = subst [fpb,`fp:int64`] `val (fp:int64) + 12960 < 2 EXP 63` in
  let veq = subst [fpb,`fp:int64`; mk_small_numeral b,`b:num`]
    `val (fp:int64) = val (stackpointer:int64) + b` in
  SUBGOAL_THEN goal ASSUME_TAC THENL
   [SUBGOAL_THEN veq SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `val(stackpointer:int64) + 14624 < 2 EXP 63` THEN ARITH_TAC;
      UNDISCH_TAC `val(stackpointer:int64) + 14624 < 2 EXP 63` THEN ARITH_TAC];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The prologue, up to the first attempt at loop2: the pushes, the frame and *)
(* the probe, the canary, the inlined unpack_sk (rho, tr and the key copied  *)
(* to fp + 1600, + 1632 and + 1696, the pointers to s1, s2, t0 and rho''),   *)
(* mu at fp + 1728 (mld_H65 of tr, pre and m if ext is 0, else the 64 bytes  *)
(* of m), rho'' = mld_H65 of the key, rnd and mu at fp + 1792, and the setup *)
(* of the slots and the registers of the attempts (with rho copied to        *)
(* fp + 1568).                                                                *)
(* ------------------------------------------------------------------------- *)

let SI65_DANGER =
  [`mld_sign_ok_65 skb MU RND <=> P`;
   `mld_sign_sig_65 skb MU RND = x`];;

let SI65_MALLOWED =
  [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`;
   `rnd:int64`; `sk:int64`; `ext:int64`; `rh:num`;
   `D:num->num#num#(num->int32)#(num->byte)`; `guard:int64`; `mf:int64`;
   `mc:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`];;

let SI65_MCALL_TAC name ilist n =
  FULL_CALL_TAC SI65_MCODE SI65_EXEC name ilist SI65_MALLOWED n;;

let SI65_CHUNKS_TAC lem off f st =
  let a = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                  mk_comb(`word:num->int64`,mk_small_numeral off)) in
  MP_TAC(SPECL [a; f; st] lem) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC];;

let SI65_NUMV s b k = subst [mk_small_numeral(b + k), mk_var(s,`:num`)];;

let SI65_MU_TAC b n =
  let sv = mk_var("s"^string_of_int n,`:armstate`) in
  let mgoal = subst [sv,`s:armstate`] (SI65_NUMV "oMU" b 1728
   `read (memory :> bytes (word_add stackpointer (word oMU),64)) s = MU`)
  and mpat = subst [sv,`s:armstate`] (SI65_NUMV "oMU" b 1728
   `read (memory :> bytes (word_add stackpointer (word oMU),64)) s =
    num_of_bytelist l`) in
  SUBGOAL_THEN mgoal ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "MU" &&
         not(is_cond(lhs(concl th)))
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_mu] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV));
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (term_match [] mpat) (concl th)));;

let SI65_RHOP_TAC b n =
  let sn = mk_var("s"^string_of_int n,`:armstate`) in
  let rgoal = subst [sn,`s:armstate`] (SI65_NUMV "oRHO" b 1792
   `read (memory :> bytes (word_add stackpointer (word oRHO),64)) s =
    mld_sign_rhoprime (\j. skb(32 + j)) RND MU`)
  and rpat = SI65_NUMV "oRHO" b 1792
   `read (memory :> bytes (word_add stackpointer (word oRHO),64)) s =
    num_of_bytelist l` in
  SUBGOAL_THEN rgoal ASSUME_TAC THENL
   [REWRITE_TAC[mld_sign_rhoprime] THEN CONV_TAC SIGN_NUM_ARITH_CONV THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o CONV_RULE SIGN_NUM_ARITH_CONV o
      check (fun th -> can (term_match [] rpat) (concl th)));
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (term_match [] rpat) (concl th)));;

(*** The ORRs of the frame address with 8 and 9 (SI65_ORR_THM at fp) ***)

let SI65_MORR_TAC b k c =
  let fpb = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                    mk_comb(`word:num->int64`,mk_small_numeral b)) in
  let th = CONV_RULE(REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)))
             (INST [fpb,`fp:int64`] (SI65_ORR_THM k c)) in
  FIRST_ASSUM(fun ath -> if concl ath = lhand(concl th)
    then SI65_ASM_RW_TAC[MP th ath] else NO_TAC);;

let SI65_PROL_END_TAC b n =
  let st = mk_var("s"^string_of_int n,`:armstate`) in
  SI65_MORR_TAC b 10048 9 THEN SI65_MORR_TAC b 2880 8 THEN SI65_MORR_TAC b 12256 9 THEN
  SI65_MORR_TAC b 10816 8 THEN
  SI65_CHUNKS_TAC MLD_BYTES32_OF_CHUNKS (b + 1568) `skb:num->byte` st THEN
  RULE_ASSUM_TAC(fun th ->
    if can (term_match []
         `read (memory :> bytes (a,32)) s = num_of_bytelist(list_of_seq skb 32)`) (concl th)
    then REWRITE_RULE[GSYM mld_sk_rho; ASSUME `mld_sk_rho skb = rh`] th else th) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (term_match [] `read (memory :> bytes (word_add stackpointer (word n),k)) s =
                        num_of_bytelist l`) (concl th)))) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `0 = n <=> n = 0`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  SIGN_SEL_DISCHARGE_TAC;;

(*** From join2 (step n0): rho'' (the BL being step n0 + 10, the callee     ***)
(*** step n0 + 11) and the setup (48 instructions), to loop2                ***)

let SI65_PROL_TAIL_TAC b n0 =
  ARM_STEPS_TAC SI65_EXEC (n0--(n0+10)) THEN
  SI65_MCALL_TAC "H_H"
   [`read X0 s`; `64`; `read X2 s`; `32`; `read X4 s`; `32`;
    `read X6 s`; `64`;
    `num_of_bytelist(list_of_seq (\j. (skb:num->byte)(32 + j)) 32)`;
    `RND:num`; `MU:num`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] (n0+11) THEN
  SI65_RHOP_TAC b (n0+11) THEN
  ARM_STEPS_TAC SI65_EXEC ((n0+12)--(n0+59)) THEN
  SI65_PROL_END_TAC b (n0+59);;

(*** mu = H(tr || pre || m) for ext = 0 (the BL being step 69) ***)

let SI65_PROL_H_TAC b =
  SIGN_PC_SIMP_RW_TAC[WORD_ZX_ZX_32_64_32; VAL_EQ_0] THEN
  ARM_STEPS_TAC SI65_EXEC (60--69) THEN
  SI65_MCALL_TAC "H_H"
   [`read X0 s`; `64`; `read X2 s`; `64`; `read X4 s`; `prelen:num`;
    `read X6 s`; `mlen:num`;
    `num_of_bytelist(list_of_seq (\j. (skb:num->byte)(64 + j)) 64)`;
    mk_var("PRE",`:num`); `M:num`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 70 THEN
  FIRST_ASSUM(fun th ->
    if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "MU"
    then ASSUME_TAC(REWRITE_RULE [ASSUME `word_zx(ext:int64) = (word 0:int32)`] th)
    else NO_TAC) THEN
  SI65_MU_TAC b 70 THEN
  SI65_PROL_TAIL_TAC b 71;;

(*** mu copied from m for ext <> 0 ***)

let SI65_M128_TAC s =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `~(word_zx (ext:int64) = (word 0:int32)) ==> 64 <= mlen`) (concl th)
    then ASSUME_TAC(MP th (ASSUME `~(word_zx(ext:int64) = (word 0:int32))`))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [`m:int64`] `read (memory :> bytes(m,mlen)) s = M`)
           (concl th)
    then MAP_EVERY (fun n ->
           MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; mk_small_numeral n;
                         s] SIGN_BYTES128_OF_BYTES) THEN
           ASM_REWRITE_TAC[] THEN
           ANTS_TAC THENL [UNDISCH_TAC `64 <= mlen` THEN ARITH_TAC;
                           CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
                           REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC])
         [0;1;2;3]
    else NO_TAC);;

let SI65_PROL_X_TAC b =
  let mu = SI65_NUMV "oMU" b 1728 `word_add stackpointer (word oMU):int64` in
  let mgoal = SI65_NUMV "oMU" b 1728
   `read (memory :> bytes (word_add stackpointer (word oMU),64)) s64 = MU`
  and mpat = SI65_NUMV "oMU" b 1728
   `read (memory :> bytes (word_add stackpointer (word oMU),64)) s64 =
    M MOD 2 EXP 512` in
  SIGN_PC_SIMP_RW_TAC[WORD_ZX_ZX_32_64_32; VAL_EQ_0] THEN
  SI65_M128_TAC `s59:armstate` THEN
  ARM_STEPS_TAC SI65_EXEC (60--64) THEN
  MP_TAC(SPECL [mu; `M:num`; `4`; `s64:armstate`] SIGN_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; WORD_ADD_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    CONV_TAC(LAND_CONV(DEPTH_CONV NUM_MULT_CONV)) THEN DISCH_TAC] THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && is_var(rhs(concl th)) &&
       name_of(rhs(concl th)) = "MU"
    then ASSUME_TAC(REWRITE_RULE
          [ASSUME `~(word_zx(ext:int64) = (word 0:int32))`] th)
    else NO_TAC) THEN
  SUBGOAL_THEN mgoal ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "MU" &&
         not(is_cond(lhs(concl th)))
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (term_match [] mpat) (concl th))) THEN
  SI65_PROL_TAIL_TAC b 65;;

(*** The pushes (1-14), the probe (17-29, three pages), the canary, the ***)
(*** loads of the key (from step 43) and the test of ext (step 59)      ***)

let SI65_PROL_TAC b =
  FULL_INIT_TAC THEN SI65_GOT_TAC THEN
  ARM_STEPS_TAC SI65_EXEC (1--14) THEN SI65_BUF_TAC THEN
  ARM_STEPS_TAC SI65_EXEC (15--16) THEN
  MAP_EVERY (fun n -> SI65_PROBE_TAC SI65_EXEC n) (17--29) THEN
  ARM_STEPS_TAC SI65_EXEC (30--33) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC SI65_EXEC (34--42) THEN
  MAP_EVERY (fun (k,i) -> SI65_SKCHUNK_TAC k i `s42:armstate`)
   [0,0; 0,1; 32,0; 32,1; 64,0; 64,1; 64,2; 64,3] THEN
  ARM_STEPS_TAC SI65_EXEC (43--58) THEN
  SI65_CHUNKS_TAC MLD_BYTES32_OF_CHUNKS (b + 1696) `\j. (skb:num->byte)(32 + j)`
    `s58:armstate` THEN
  SI65_CHUNKS_TAC SI65_BYTES64_OF_CHUNKS (b + 1632) `\j. (skb:num->byte)(64 + j)`
    `s58:armstate` THEN
  ARM_STEPS_TAC SI65_EXEC [59] THEN
  ASM_CASES_TAC `word_zx(ext:int64) = (word 0:int32)` THENL
   [SI65_PROL_H_TAC b; SI65_PROL_X_TAC b];;

(* ------------------------------------------------------------------------- *)
(* An iteration of the loop over the attempts (as gcc's SIGN65_BODY): the    *)
(* facts about attempt i (its record D i, the termination of its challenge,  *)
(* the result and the signature if it is the last), the attempt (SI65_ATT at *)
(* fp = stackpointer + b), then the three exits: on success w19 = 0 and to   *)
(* join23; on rejection back to loop2 with i + 1 in w10 or, after the last   *)
(* attempt, the signature zeroed with memset, -4 in w19 and to join23. The   *)
(* equations for mld_sign_ok_65 and mld_sign_sig_65 are made conditional on  *)
(* ~(i + 1 < N) first, else a call would rewrite the postcondition with      *)
(* them.                                                                     *)
(* ------------------------------------------------------------------------- *)

let SI65_BALLOWED = SI65_MALLOWED @ [`i:num`];;

let SI65_BODY_INIT_TAC =
  let nth = UNDISCH(MP (ARITH_RULE
   `i < mld_sign_natt 13106 18 D
    ==> ~(i + 1 < mld_sign_natt 13106 18 D)
    ==> mld_sign_natt 13106 18 D - 1 = i`)
   (ASSUME `i < mld_sign_natt 13106 18 D`)) in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[ASSUME `i < mld_sign_natt 13106 18 D`;
              ASSUME `~(i = mld_sign_natt 13106 18 D)`] THEN
  SUBGOAL_THEN `i < 13106` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`i < mld_sign_natt 13106 18 D`; `mld_sign_natt 13106 18 D <= 13106`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `!i. i < mld_sign_natt 13106 18 D
              ==> (D:num->num#num#(num->int32)#(num->byte)) i = x`)
         (concl th)
    then
      let th1 = MP (SPEC `i:num` th)
                   (ASSUME `i < mld_sign_natt 13106 18 D`) in
      let tup = `FST((D:num->num#num#(num->int32)#(num->byte)) i),
                 FST(SND(D i)),FST(SND(SND(D i))),SND(SND(SND(D i)))` in
      ASSUME_TAC(TRANS (SYM th1) (SYM(REWRITE_CONV[PAIR] tup)))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `!i. i < mld_sign_natt 13106 18 D
              ==> mld_poly_challenge_terminates 49 48
                   (FST((D:num->num#num#(num->int32)#(num->byte)) i))`)
         (concl th)
    then ASSUME_TAC(MP (SPEC `i:num` th)
                       (ASSUME `i < mld_sign_natt 13106 18 D`))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `!i. i + 1 < mld_sign_natt 13106 18 D
              ==> ~(FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) =
                    18)`)
         (concl th)
    then ASSUME_TAC(SPEC `i:num` th)
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `mld_sign_ok_65 skb MU RND <=> P`) (concl th)
    then ASSUME_TAC(DISCH `~(i + 1 < mld_sign_natt 13106 18 D)`
                     (REWRITE_RULE[nth] th))
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `mld_sign_sig_65 skb MU RND = x`) (concl th)
    then ASSUME_TAC(DISCH `~(i + 1 < mld_sign_natt 13106 18 D)`
                     (REWRITE_RULE[nth] th))
    else NO_TAC);;

let SI65_ATT_ILIST b =
  let fpb = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                    mk_comb(`word:num->int64`,mk_small_numeral b)) in
  [`sig:int64`; `sk:int64`; `skb:num->byte`; fpb; `rh:num`; `MU:num`; SI65_RHOP;
   `i:num`; `FST((D:num->num#num#(num->int32)#(num->byte)) i)`;
   `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i))`;
   `FST(SND(SND((D:num->num#num#(num->int32)#(num->byte)) i)))`;
   `SND(SND(SND((D:num->num#num#(num->int32)#(num->byte)) i)))`;
   `guard:int64`; `pc:num`];;

let SI65_BODY_ATT_TAC b =
  FULL_INIT_TAC THEN SI65_GOT_TAC THEN
  FULL_CALL_TAC SI65_MCODE SI65_EXEC "H_ATT" (SI65_ATT_ILIST b) SI65_BALLOWED 1;;

let SI65_BODY_DISCHARGE_TAC =
  REWRITE_TAC[ENUMERATEL_ADD1] THEN SIGN_BETA_ALL_TAC THEN SIGN_SELECT_TAC THEN
  SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_SUFFIX_UNIFY_TAC; SIGN_SUFFIX_MEMACCESS_TAC];;

let SI65_CASE_TH = ASSUME
  `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 18`;;

let SI65_NCASE_TH = ASSUME
  `~(FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 18)`;;

let SI65_LAST_TAC cth =
  SUBGOAL_THEN `i + 1 = mld_sign_natt 13106 18 D` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`i < mld_sign_natt 13106 18 D`; `~(i + 1 < mld_sign_natt 13106 18 D)`]
    THEN ARITH_TAC;
    DISCH_THEN(fun th -> ASSUME_TAC(EQT_INTRO th))] THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match []
         `~(i + 1 < mld_sign_natt 13106 18 D)
          ==> (mld_sign_ok_65 skb MU RND <=> P)`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[cth]
          (MP th (ASSUME `~(i + 1 < mld_sign_natt 13106 18 D)`)))
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match []
         `~(i + 1 < mld_sign_natt 13106 18 D)
          ==> mld_sign_sig_65 skb MU RND = x`) (concl th)
    then FIRST_ASSUM(fun oth ->
           let c = concl oth in
           if c = `mld_sign_ok_65 skb MU RND` ||
              c = `~mld_sign_ok_65 skb MU RND`
           then ASSUME_TAC(REWRITE_RULE[oth]
                 (MP th (ASSUME `~(i + 1 < mld_sign_natt 13106 18 D)`)))
           else NO_TAC)
    else NO_TAC);;

(*** success: w19 = 0 and to join23 (2 instructions) ***)

let SI65_SUCC_TAC =
  SIGN_PC_SIMP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 18 ==> P`)
    (concl th))) THEN
  REWRITE_TAC[SI65_CASE_TH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(i + 1 < mld_sign_natt 13106 18 D)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> can (term_match []
     `i + 1 < mld_sign_natt 13106 18 D ==> P`) (concl th))) THEN
    REWRITE_TAC[SI65_CASE_TH];
    ALL_TAC] THEN
  SI65_LAST_TAC SI65_CASE_TH THEN
  ARM_STEPS_TAC SI65_EXEC (2--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SI65_BODY_DISCHARGE_TAC;;

(*** rejection, another attempt follows ***)

let SI65_CONT_TAC =
  SUBGOAL_THEN `i + 1 < mld_sign_natt 13106 18 D` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th ->
      if can (term_match []
           `~(i + 1 < mld_sign_natt 13106 18 D)
            ==> (mld_sign_ok_65 skb MU RND <=> P)`) (concl th)
      then ASSUME_TAC(REWRITE_RULE[SI65_NCASE_TH]
            (MP th (ASSUME `~(i + 1 < mld_sign_natt 13106 18 D)`)))
      else NO_TAC) THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `~mld_sign_ok_65 skb MU RND ==> P`) (concl th)
      then MP_TAC(MP th (ASSUME `~mld_sign_ok_65 skb MU RND`))
      else NO_TAC) THEN
    MAP_EVERY UNDISCH_TAC
     [`i < mld_sign_natt 13106 18 D`; `~(i + 1 < mld_sign_natt 13106 18 D)`;
      `i + 1 < 13106`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(i + 1 = mld_sign_natt 13106 18 D)` ASSUME_TAC THENL
   [UNDISCH_TAC `i + 1 < mld_sign_natt 13106 18 D` THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SI65_BODY_DISCHARGE_TAC;;

(*** rejection of the last attempt: from loop2_exit1, the signature zeroed ***)
(*** with memset (the bl being step 7) and -4 in w19, to join23           ***)

let SI65_EXH_TAC =
  ARM_STEPS_TAC SI65_EXEC (2--7) THEN
  SI65_MEMSET_TAC SI65_EXEC SI65_BALLOWED 7 THEN
  ARM_STEPS_TAC SI65_EXEC [13] THEN
  RULE_ASSUM_TAC(PURE_REWRITE_RULE[WORD_ZX_0]) THEN
  SUBGOAL_THEN `~(i + 1 < mld_sign_natt 13106 18 D)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`mld_sign_natt 13106 18 D <= 13106`; `~(i + 1 < 13106)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SI65_LAST_TAC SI65_NCASE_TH THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SI65_BODY_DISCHARGE_TAC;;

let SI65_FAIL_TAC =
  SIGN_PC_SIMP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `~(FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 18) ==> P`)
    (concl th))) THEN
  REWRITE_TAC[SI65_NCASE_TH] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match []
    `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 18 ==> P`)
    (concl th))) THEN
  ASM_CASES_TAC `i + 1 < 13106` THEN SIGN_PC_SIMP_TAC THENL
   [SI65_CONT_TAC; SI65_EXH_TAC];;

let SI65_BODY_TAC b =
  SI65_BODY_INIT_TAC THEN SI65_BODY_ATT_TAC b THEN
  ASM_CASES_TAC
   `FST(SND((D:num->num#num#(num->int32)#(num->byte)) i)) = 18` THENL
   [SI65_SUCC_TAC; SI65_FAIL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The epilogue, from join23: the zeroing of the pointers to s1, s2 and t0,  *)
(* the memset of fp + 544 .. fp + 1600 (the bl being step 11), the inlined   *)
(* zeroing of the 256 bytes at fp + 1600, the check of the canary, the       *)
(* restored registers and x1..x18 cleared.                                   *)
(* ------------------------------------------------------------------------- *)

let SI65_ZX128 = WORD_BLAST `!x:int64. word_zx(word_zx x:int128):int64 = x`;;

let SI65_EPIL_DISCHARGE_TAC =
  SIGN_BETA_ALL_TAC THEN SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_SUFFIX_UNIFY_TAC; SIGN_SUFFIX_MEMACCESS_TAC];;

let SI65_EPIL_TAC =
  SIGN_DROP_TAC SI65_DANGER THEN
  REWRITE_TAC[LT_REFL] THEN FULL_INIT_TAC THEN SI65_GOT_TAC THEN
  ARM_STEPS_TAC SI65_EXEC (1--11) THEN
  SI65_MEMSET_TAC SI65_EXEC SI65_MALLOWED 11 THEN
  ARM_STEPS_TAC SI65_EXEC (17--34) THEN SI65_ADRP_STEPS_TAC SI65_EXEC [35] THEN
  ARM_STEPS_TAC SI65_EXEC (36--71) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[SIGN_RET_ZX] THEN
  REWRITE_TAC[SI65_ZX128] THEN SI65_EPIL_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Each case of the frame: the loop over the attempts with the prologue, the *)
(* body and the epilogue.                                                    *)
(* ------------------------------------------------------------------------- *)

let SI65_CASE_TAC b =
  SI65_FP_ALIGNED_TAC THEN SI65_FP_BOUND_TAC b THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `mld_sign_natt 13106 18 D`
   `pc + mldsa65_signature_internal_loop2`
   `pc + mldsa65_signature_internal_join23` (SI65_INV b) THEN
  REPEAT CONJ_TAC THENL
   [SIMPLE_ARITH_TAC; SI65_PROL_TAC b; SI65_BODY_TAC b; SI65_EPIL_TAC];;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  SI65_START_TAC THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN SI65_CASE_TAC 1504;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN SI65_CASE_TAC 1488]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
