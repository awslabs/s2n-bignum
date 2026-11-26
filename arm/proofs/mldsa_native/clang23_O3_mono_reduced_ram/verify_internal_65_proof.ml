(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* mldsa65_verify_internal of the clang 23 -O3 monolithic reduced-RAM build: *)
(* the proof of verify_internal_65_spec.ml, templated from that of           *)
(* verify_internal_44_proof.ml. clang has inlined most of the callees of the *)
(* gcc builds; the proof composes the region lemmas of the inlined code      *)
(* (inline_sign_*.ml) and the specifications of the real callees with the    *)
(* code between them, in the order of the code:                              *)
(*                                                                           *)
(* - the prologue with the stack probe, the copy of c~, z unpacked by five   *)
(*   inlined loops (INLINE_POLYZ19) and polyvecl_chknorm;                    *)
(* - if the norm check fails, the result -6 and the cleanup;                 *)
(* - mu: copied from m (external mu) or H(tr || pre || m, 64) with           *)
(*   tr = SHAKE256(pk, 64) by the inlined sponge (INLINE_SHAKE_PROVE of      *)
(*   SHAKE65_INST);                                                          *)
(* - the NTT of z, rho, the challenge and its NTT;                           *)
(* - the loop over the 6 rows: row_lazy, the inlined polyt1_unpack, shiftl,  *)
(*   NTT, pointwise product, sub, reduce, invntt, caddq, the hints           *)
(*   (INLINE_HINTSK_PROVE), use_hint for gamma2 = (q - 1) / 32               *)
(*   (INLINE_USEHINT32_LOOP) and the packing of w1 (INLINE_W1PACK32_PROVE);  *)
(* - after the loop, c2 = H(mu || w1', 48) by mld_H65, the branch-free       *)
(*   compare with c~ (bit-blasted once), the result and the cleanup.         *)
(*                                                                           *)
(* The stack frame F = stackpointer + b is aligned to 32 bytes: b = 1696 or  *)
(* 1680, one proof for each (VI65_CASE_TAC b).                               *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_internal_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;
needs "arm/proofs/utils/mldsa_native_verify.ml";;
needs "arm/proofs/utils/mldsa_native_lazy_matrix.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/lazy_eq_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/H_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvecl_chknorm_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_challenge_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_unpackz19.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_map2.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_usehint32.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_hintsk.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_w1pack32.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_shake_gen.ml";;

(* ------------------------------------------------------------------------- *)
(* The callees: the region lemmas and specifications.                        *)
(* ------------------------------------------------------------------------- *)

let VI65_ROW_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL;;

let VI65_INV_FULL =
  MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL;;

let VI65_MC_NAME = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc";;

let VI65_T1_TH =
  INLINE_POLYT1_OF_INSTANCE
   (find (fun (fn,hl,_,_,_) -> fn = "mldsa65_verify_internal") INLINE_POLYT1_INSTANCES);;

let VI65_SHL_TH = INLINE_SHIFTL65 ();;
let VI65_SUB_TH = INLINE_SUB65 ();;

let VI65_PWM_TH = INLINE_PWM4_OF_INSTANCE
  (find (fun (fn,hl,_,_) -> hl = "mldsa65_verify_internal_loop9") INLINE_PWM4_INSTANCES);;

let VI65_RED_TH = INLINE_REDUCE_OF_INSTANCE
  (find (fun (_,fn,hl,_,_,_) -> fn = "mldsa65_verify_internal" && hl = "loop10")
        INLINE_REDUCE_INSTANCES);;

let VI65_CADDQ_TH = INLINE_CADDQ_LOOP VI65_MC_NAME
  (INLINE_LOOP_EXEC "mldsa65_verify_internal_loop11" "mldsa65_verify_internal_loop11_exit")
  "mldsa65_verify_internal_loop11" "mldsa65_verify_internal_loop11_exit"
  ["X9";"X25";"X8";"X10";"X11";"X19"];;

let VI65_Z_THS = map INLINE_POLYZ19_OF_INSTANCE INLINE_POLYZ19_INSTANCES;;
let VI65_SHAKE_TH = INLINE_SHAKE_PROVE SHAKE65_INST;;
let VI65_USEHINT_TH =
  INLINE_USEHINT32_OF_INSTANCE (hd INLINE_USEHINT32_INSTANCES);;
let VI65_W1PACK_TH = INLINE_W1PACK32_PROVE INLINE_W1PACK32_65;;
let VI65_HINTS_TH = INLINE_HINTSK_PROVE INLINE_HINTS65_INST;;


let VI65_EXEC = MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;
let VI65_MC = mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc;;

let VI65_ARGS =
  "sig m mlen pre prelen pk ext sigb pkb M PRE guard mf mc pc stackpointer " ^
  "returnaddress";;

let VI65_LAMBDA =
  "\\(sig:int64) (m:int64) (mlen:num) (pre:int64) (prelen:num) (pk:int64) " ^
  "(ext:int64) (sigb:num->byte) (pkb:num->byte) (M:num) PRE " ^
  "(guard:int64) (mf:int64) (mc:int64) (pc:num) (stackpointer:int64) " ^
  "(returnaddress:int64).";;

let VI65_HOK = "mld_unpack_hints_ret 55 6 (\\t. sigb(3248 + t)) i = word 0";;

let VI65_HINTSOK = "(!i. i < 6 ==> " ^ VI65_HOK ^ ")";;

let VI65_K =
  "(if " ^ VI65_HINTSOK ^ " then 6 else (minimal i. ~(" ^ VI65_HOK ^
  ")) + 1)";;

let VI65_NORMOK =
  "mld_polyvec_chknorm 5 (mld_polyvec_unpack 640 mld_polyz_unpack_19 " ^
  "(\\j. sigb(48 + j))) (word 524092) = word 0";;

let VI65_OK =
  "mld_verify_internal_ok 6 5 48 mld_polyz_unpack_19 640 524092 " ^
  "mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49 sigb pkb " ^
  "(if word_zx ext = (word 0:int32) " ^
  "then mld_verify_mu 1952 pkb prelen PRE mlen M else M MOD 2 EXP 512)";;

(*** The template: the alignment of the stack (a/u), then the code up to  ***)
(*** the norm check (pre), then the failure of the check (nf) or the rest ***)

let VI65_TEMPLATE_CASE x =
  let f n = "(f_ev_" ^ n ^ "_" ^ x ^ " " ^ VI65_ARGS ^ ")" in
  let fi n = "(f_ev_" ^ n ^ "_" ^ x ^ " " ^ VI65_ARGS ^ " i)" in
  "(APPEND (if " ^ VI65_NORMOK ^ " then " ^
  "APPEND (if " ^ VI65_HINTSOK ^ " then (if " ^ VI65_OK ^ " then " ^
  f "acc" ^ " else " ^ f "rej" ^ ") else " ^ f "hf" ^ ") " ^
  "(APPEND (ENUMERATEL " ^ VI65_K ^ " (\\i. if " ^ VI65_HOK ^ " then " ^
  fi "row" ^ " else " ^ fi "rowf" ^ ")) " ^
  "(APPEND " ^ f "mid" ^ " (if word_zx ext = (word 0:int32) then " ^
  f "hash" ^ " else " ^ f "copy" ^ "))) else " ^ f "nf" ^ ") " ^
  f "pre" ^ ")";;

let VI65_TEMPLATE =
  parse_term(VI65_LAMBDA ^ " if aligned 32 stackpointer then " ^
             VI65_TEMPLATE_CASE "a" ^ " else " ^ VI65_TEMPLATE_CASE "u" ^
             " :(uarch_event)list");;

let VI65_HOK_TM = parse_term VI65_HOK;;
let VI65_HINTSOK_TM = parse_term VI65_HINTSOK;;
let VI65_NORMOK_TM = parse_term VI65_NORMOK;;
let VI65_EXT0 = `word_zx (ext:int64) = (word 0:int32)`;;

let VI65_Z =
  `mld_polyvec_unpack 640 mld_polyz_unpack_19 (\j. (sigb:num->byte)(48 + j))`;;

(*** Words of the stack frame ***)

let VI65_SP k =
  mk_comb(`word_add (stackpointer:int64)`,
          mk_comb(`word:num->int64`,mk_small_numeral k));;

(*** The callee-saved registers, saved at stackpointer + 12288 .. 12447 ***)

let VI65_SAVED_FACTS =
  String.concat " /\\\n" (map (fun (r,k) ->
     Printf.sprintf
      "read (memory :> bytes64 (word_add stackpointer (word %d))) s = %s" k r)
   ["d15_init",12288; "d14_init",12296; "d13_init",12304; "d12_init",12312;
    "d11_init",12320; "d10_init",12328; "d9_init",12336; "d8_init",12344;
    "x29_init",12352; "returnaddress",12360; "x28_init",12368;
    "x27_init",12376; "x26_init",12384; "x25_init",12392; "x24_init",12400;
    "x23_init",12408; "x22_init",12416; "x21_init",12424; "x20_init",12432;
    "x19_init",12440]);;

(* ------------------------------------------------------------------------- *)
(* The stack probe of the prologue, as for ML-DSA-44: with                   *)
(* 32768 <= val(stackpointer + 12448) < 2^63, the values of the signed       *)
(* comparisons are those of the offsets.                                     *)
(* ------------------------------------------------------------------------- *)

let VI65_VAL_ADD = prove
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

let VI65_IVAL_ADD = prove
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

(*** val stackpointer + 12448 < 2^63 and 20320 <= val stackpointer ***)

let VI65_SP_BOUNDS_TAC =
  MP_TAC(SPECL [`stackpointer:int64`; `12448`; `12448`] VI65_VAL_ADD) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `20320 <= val(stackpointer:int64)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC];;

let VI65_IVAL_SP = prove
 (`!s:int64. val s < 2 EXP 63 ==> ival s = &(val s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IVAL_EQ_VAL THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_ARITH_TAC);;

let VI65_SP_PC_CONV =
  REWRITE_CONV[VERIF_PTR_SUB; INT_ARITH `!v a b:int. (v + a) - (v + b) = a - b`;
               INT_ARITH `!v b:int. v - (v + b) = --b`;
               INT_ARITH `!v b:int. (v + b) - v = b`;
               INT_ARITH `!v a b:int. (v + a) - (v - b) = a + b`;
               INT_ARITH `!v a b:int. (v - a) - (v + b) = --(a + b)`;
               INT_ARITH `!v a b:int. (v - a) - (v - b) = b - a`] THENC
  DEPTH_CONV WORD_RED_CONV THENC
  REWRITE_CONV[INT_OF_NUM_EQ; INT_OF_NUM_LT; ARITH_EQ; ARITH_LT; ARITH_LE;
               INT_LT_REFL; INT_OF_NUM_LE] THENC
  DEPTH_CONV INT_RED_CONV THENC REWRITE_CONV[];;

let VI65_NEGSUB = WORD_RULE `word_sub (s:int64) y = word_add s (word_neg y)`;;

let VI65_NEGADD_CONV tm =
  match tm with
    Comb(Comb(Const("word_add",_),s),Comb(Const("word",_),k))
      when is_numeral k && type_of tm = `:int64` &&
           dest_numeral k >=/ ((Num.num_of_int 2) **/ (Num.num_of_int 63)) ->
      let m = ((Num.num_of_int 2) **/ (Num.num_of_int 64)) -/ dest_numeral k in
      let rhs_tm = mk_comb(mk_comb(`word_sub:int64->int64->int64`,s),
                           mk_comb(`word:num->int64`,mk_numeral m)) in
      prove(mk_eq(tm,rhs_tm),
            REWRITE_TAC[VI65_NEGSUB] THEN
            CONV_TAC(RAND_CONV(RAND_CONV WORD_REDUCE_CONV)) THEN REFL_TAC)
  | _ -> failwith "VI65_NEGADD_CONV";;

let VI65_PROBE_PC_TAC =
  let isadd t = can (term_match [] `ival(word_add (stackpointer:int64) (word k))`) t
  and issub t = can (term_match [] `ival(word_sub (stackpointer:int64) (word k))`) t in
  W(fun (asl,w) ->
    let hyps = end_itlist CONJ (map snd (filter (fun (_,th) ->
      mem (concl th) [`val(stackpointer:int64) + 12448 < 2 EXP 63`;
                      `20320 <= val(stackpointer:int64)`]) asl)) in
    let side tm = MP (ARITH_RULE(mk_imp(concl hyps,tm))) hyps in
    RULE_ASSUM_TAC(fun th ->
      let c = concl th in
      if is_eq c && is_comb(lhand c) &&
         rator(lhand c) = `read PC:armstate->int64` &&
         free_in `stackpointer:int64` (rhs c)
      then
        let th1 = CONV_RULE(RAND_CONV(REWRITE_CONV[VERIF_PTR_SUB] THENC
                                      DEPTH_CONV WORD_RED_CONV THENC
                                      DEPTH_CONV VI65_NEGADD_CONV)) th in
        let th1 = if free_in `ival(stackpointer:int64)` (concl th1)
                  then REWRITE_RULE[MP (SPEC `stackpointer:int64` VI65_IVAL_SP)
                         (side `val(stackpointer:int64) < 2 EXP 63`)] th1
                  else th1 in
        let ts = setify(find_terms (fun t -> isadd t || issub t) (concl th1)) in
        let eqs = map (fun t ->
          let k = rand(rand(rand t)) in
          if isadd t then
            MP (SPECL [`stackpointer:int64`; k] VI65_IVAL_ADD)
               (side (subst [k,`k:num`] `val(stackpointer:int64) + k < 2 EXP 63`))
          else
            MP (SPECL [`stackpointer:int64`; k] IVAL_SP_SUB)
               (side (subst [k,`k:num`]
                 `k <= val(stackpointer:int64) /\ val stackpointer < 2 EXP 63 /\
                  k < 2 EXP 63`))) ts in
        CONV_RULE(RAND_CONV(REWRITE_CONV eqs THENC VI65_SP_PC_CONV)) th1
      else th));;

let VI65_PROBE_TAC exec n =
  ARM_STEPS_TAC exec [n] THEN VI65_PROBE_PC_TAC;;

(*** The five polynomials of z from the five unpacking loops ***)

let VI65_ZJOIN = prove
 (`!(sp:int64) n (b:num->byte) s.
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 4 * i)))) s =
             mld_polyz_unpack_19 (\j. b (48 + j)) i) /\
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 1024 + 4 * i)))) s =
             mld_polyz_unpack_19 (\j. b (688 + j)) i) /\
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 2048 + 4 * i)))) s =
             mld_polyz_unpack_19 (\j. b (1328 + j)) i) /\
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 3072 + 4 * i)))) s =
             mld_polyz_unpack_19 (\j. b (1968 + j)) i) /\
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 4096 + 4 * i)))) s =
             mld_polyz_unpack_19 (\j. b (2608 + j)) i)
    ==> !i. i < 1280
            ==> read (memory :> bytes32 (word_add sp (word (n + 4 * i)))) s =
                mld_polyvec_unpack 640 mld_polyz_unpack_19 (\j. b(48 + j)) i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[mld_polyvec_unpack; mld_polyvec] THEN
  SUBGOAL_THEN `?p k. p < 5 /\ k < 256 /\ i = 256 * p + k` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`i DIV 256`; `i MOD 256`] THEN
    MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[DIVMOD_CHUNK] THEN
  SUBGOAL_THEN `p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4` MP_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)] THEN
  REWRITE_TAC[ARITH_RULE `!n k. n + 4 * (256 * 0 + k) = n + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 1 + k) = n + 1024 + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 2 + k) = n + 2048 + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 3 + k) = n + 3072 + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 4 + k) = n + 4096 + 4 * k`;
              ARITH_RULE `!t. 48 + 640 * 0 + t = 48 + t`;
              ARITH_RULE `!t. 48 + 640 * 1 + t = 688 + t`;
              ARITH_RULE `!t. 48 + 640 * 2 + t = 1328 + t`;
              ARITH_RULE `!t. 48 + 640 * 3 + t = 1968 + t`;
              ARITH_RULE `!t. 48 + 640 * 4 + t = 2608 + t`] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The facts that hold from the prologue on, with the frame at              *)
(* stackpointer + b (b = 1696 if stackpointer is a multiple of 32, 1680     *)
(* otherwise): the saved registers, the canary at b + 10584, the GOT, the   *)
(* inputs.                                                                   *)
(* ------------------------------------------------------------------------- *)

let VI65_FRAME_FACTS b =
  Printf.sprintf
   "read SP s = word_add stackpointer (word %d) /\\
    read X29 s = word_add stackpointer (word 12352) /\\
    %s /\\
    read (memory :> bytes64 (word_add stackpointer (word %d))) s = canary /\\
    read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard)))
      s = guard /\\
    read (memory :> bytes64 guard) s = canary /\\
    read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\\
    read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s = mc /\\
    read (memory :> bytes (ea,el)) s = ev /\\
    (!j. j < 3309
         ==> read (memory :> bytes8 (word_add sig (word j))) s = sigb j) /\\
    (!j. j < 1952
         ==> read (memory :> bytes8 (word_add pk (word j))) s = pkb j)"
   b VI65_SAVED_FACTS (b + 10584);;

(*** The state after the norm check (+0x65c): prelen is on the stack at  ***)
(*** b + 336, c~ at b + 9664 and z unpacked at b + 4480                  ***)

let VI65_PRE b =
  subst [VI65_Z,`VI65Z:num->int32`] (parse_term(Printf.sprintf
   "\\s. aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
        read PC s = word (pc + mldsa65_verify_internal_after_mldsa65_polyvecl_chknorm) /\\
        %s /\\
        read X0 s = word_zx(mld_polyvec_chknorm 5 VI65Z (word 524092)) /\\
        read X19 s = sig /\\ read X20 s = pk /\\ read X21 s = m /\\
        read X23 s = word mlen /\\
        read X24 s = pre /\\ read X25 s = word_zx(word_zx (ext:int64):int32) /\\
        read X22 s = word_add stackpointer (word %d) /\\
        read X26 s = word_add stackpointer (word %d) /\\
        read X27 s = word_add stackpointer (word %d) /\\
        read X28 s = word_add stackpointer (word %d) /\\
        read (memory :> bytes64 (word_add stackpointer (word %d))) s = word prelen /\\
        read (memory :> bytes(m,mlen)) s = M /\\
        read (memory :> bytes(pre,prelen)) s = PRE' /\\
        (!i. i < 1280
             ==> read (memory :> bytes32 (word_add stackpointer (word (%d + 4 * i))))
                   s = VI65Z i) /\\
        read (memory :> bytes128 (word_add stackpointer (word %d))) s =
          mld_chunk128 sigb 0 /\\
        read (memory :> bytes128 (word_add stackpointer (word %d))) s =
          mld_chunk128 sigb 1 /\\
        read (memory :> bytes128 (word_add stackpointer (word %d))) s =
          mld_chunk128 sigb 2"
   (VI65_FRAME_FACTS b) (b + 4480) (b + 4480) (b + 4480) (b + 4480) (b + 336)
   (b + 4480) (b + 9664) (b + 9680) (b + 9696)));;

(* ------------------------------------------------------------------------- *)
(* The prologue and the unpacking of z, to the return of the norm check.     *)
(* ------------------------------------------------------------------------- *)

let VI65_CONSTS =
  map (fun d -> MLDSA_NATIVE_IMAGE_CONST_RULE d 128)
   [layout "mldsa65_verify_internal_const1";
    layout "mldsa65_verify_internal_const2"];;

let VI65_CONSTS_TAC =
  MAP_EVERY (fun th -> FIRST_ASSUM(fun ath ->
     try ASSUME_TAC(MATCH_MP th ath) with Failure _ -> NO_TAC)) VI65_CONSTS;;

let VI65_SIG_CHUNKS_TAC =
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`sig:int64`; `3309`; `sigb:num->byte`; `s0:armstate`;
                  mk_small_numeral i] BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
                    ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC) [0;1;2];;

let VI65_BUF_TAC =
  FIRST_ASSUM(fun a16 ->
    if concl a16 <> `aligned 16 (stackpointer:int64)` then NO_TAC else
    let th = MP (SPEC `stackpointer:int64` (MLD_WRAP_BUFFER_RULE `1696`)) a16 in
    FIRST_ASSUM(fun cth ->
      if concl cth = `aligned 32 (stackpointer:int64)` ||
         concl cth = `~aligned 32 (stackpointer:int64)`
      then RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_RULE[cth] th])
      else NO_TAC));;

let VI65_ALLOWED =
  [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`;
   `pk:int64`; `ext:int64`; `sigb:num->byte`; `pkb:num->byte`; `M:num`;
   `PRE':num`; `guard:int64`; `mf:int64`; `mc:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`];;

let VI65_CALL_GEN_TAC allowed name ilist n =
  FULL_CALL_TAC VI65_MC VI65_EXEC name ilist allowed n;;

let VI65_CALL_TAC = VI65_CALL_GEN_TAC VI65_ALLOWED;;

let VI65_BYTES_SLICE_TAC tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC];;

let VI65_Z_CALL_TAC k reg off n =
  let s = mk_var("s"^string_of_int(n-1),`:armstate`) in
  let tm = subst [mk_small_numeral off,`off:num`; s,`s:armstate`]
   `!j. j < 640 ==> read(memory :> bytes8(word_add sig (word(off + j)))) s =
                    (sigb:num->byte)(off + j)` in
  VI65_BYTES_SLICE_TAC tm THEN
  VI65_CALL_TAC ("H_Z"^string_of_int k)
   [mk_comb(`read:(armstate,int64)component->armstate->int64`,mk_const(reg,[])) |>
    (fun t -> mk_comb(t,`s:armstate`));
    subst [mk_small_numeral off,`off:num`] `word_add (sig:int64) (word off)`;
    subst [mk_small_numeral off,`off:num`] `\j. (sigb:num->byte)(off + j)`;
    `pc:num`] n;;

let VI65_BND_TAC =
  let tm = `word_zx (word 524092:int64):int32` in
  let th = WORD_REDUCE_CONV tm in
  RULE_ASSUM_TAC(fun ath ->
    if free_in tm (concl ath) then REWRITE_RULE[th] ath else ath);;

let VI65_PROLOGUE_TAC b =
  FULL_INIT_TAC THEN VI65_SIG_CHUNKS_TAC THEN
  ARM_STEPS_TAC VI65_EXEC (1--14) THEN VI65_BUF_TAC THEN
  ARM_STEPS_TAC VI65_EXEC (15--16) THEN
  MAP_EVERY (fun n -> VI65_PROBE_TAC VI65_EXEC n) (17--26) THEN
  ARM_STEPS_TAC VI65_EXEC (27--28) THEN
  ARM_STEPS_TAC VI65_EXEC [29] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC VI65_EXEC (30--49) THEN
  VI65_Z_CALL_TAC 0 "X10" 48 50 THEN
  ARM_STEPS_TAC VI65_EXEC (51--56) THEN
  VI65_Z_CALL_TAC 1 "X26" 688 57 THEN
  ARM_STEPS_TAC VI65_EXEC (58--62) THEN
  VI65_Z_CALL_TAC 2 "X27" 1328 63 THEN
  ARM_STEPS_TAC VI65_EXEC (64--68) THEN
  VI65_Z_CALL_TAC 3 "X28" 1968 69 THEN
  ARM_STEPS_TAC VI65_EXEC (70--75) THEN
  VI65_Z_CALL_TAC 4 "X22" 2608 76 THEN
  ARM_STEPS_TAC VI65_EXEC (77--81) THEN
  MP_TAC(SPECL [`stackpointer:int64`; mk_small_numeral(b + 4480); `sigb:num->byte`; `s81:armstate`]
               VI65_ZJOIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  VI65_CALL_TAC "H_CHKNORM"
   [`read X0 s`; VI65_Z; `read X1 s`; `pc:num`; `read SP s`; `read X30 s`] 82 THEN
  VI65_BND_TAC;;

(* ------------------------------------------------------------------------- *)
(* The events so far as a variable old, in a segment whose precondition has  *)
(* e2 = X: X is generalized everywhere in the goal.                          *)
(* ------------------------------------------------------------------------- *)

let VI65_GEN_OLD_TAC name =
  W(fun (asl,w) ->
    let pre = rand(rator(rator w)) in
    let t = find_term (fun t -> is_exists t &&
              name_of(fst(dest_exists t)) = "e2") pre in
    let c = el 1 (conjuncts(snd(dest_exists t))) in
    let x = rhs c in
    SPEC_TAC(x,mk_var(name,type_of x)) THEN GEN_TAC);;

let VI65_ALLOWED_OLD = `old:(uarch_event)list`::VI65_ALLOWED;;

(* ------------------------------------------------------------------------- *)
(* From join3 (state k) to the return: the memset calls through the PLT     *)
(* that zero the buffers, the inline zeroing, the check of the canary, the   *)
(* restoring of the registers and the clearing of x1..x18.                   *)
(* ------------------------------------------------------------------------- *)

let VI65_MEMSET_TAC allowed n =
  LIBC_PLT_TAC VI65_EXEC n THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" VI65_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`]
   (ref allowed) (n + 5);;

let VI65_CLEANUP_TAC b allowed k =
  let ms = VI65_MEMSET_TAC allowed in
  VERIF_DROP_MEM_TAC (VERIF_KEEP_FRAME 12288 12440 (b + 10584)) THEN
  ARM_STEPS_TAC VI65_EXEC ((k+1)--(k+5)) THEN ms (k+5) THEN
  ARM_STEPS_TAC VI65_EXEC ((k+11)--(k+15)) THEN ms (k+15) THEN
  ARM_STEPS_TAC VI65_EXEC ((k+21)--(k+25)) THEN ms (k+25) THEN
  ARM_STEPS_TAC VI65_EXEC ((k+31)--(k+35)) THEN ms (k+35) THEN
  ARM_STEPS_TAC VI65_EXEC ((k+41)--(k+47)) THEN ms (k+47) THEN
  ARM_STEPS_TAC VI65_EXEC ((k+53)--(k+76)) THEN ms (k+76) THEN
  ARM_STEPS_TAC VI65_EXEC [k+82] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC VI65_EXEC ((k+83)--(k+118));;

(*** mld_verify_internal_ok for the parameters of ML-DSA-65 ***)

let VI65_RHO = `num_of_bytelist (list_of_seq (pkb:num->byte) 32)`;;
let VI65_ZHAT = mk_comb(`mld_polyvec_map mld_poly_ntt`,VI65_Z);;
let VI65_C = `num_of_bytelist (list_of_seq (sigb:num->byte) 48)`;;
let VI65_CP = mk_comb(`mld_poly_challenge 49 48`,VI65_C);;
let VI65_CPHAT = mk_comb(`mld_poly_ntt`,VI65_CP);;

let VI65_W1B =
  subst [VI65_RHO,`rho:num`; VI65_ZHAT,`zhat:num->int32`;
         VI65_CPHAT,`cphat:num->int32`]
   `mld_polyvec_pack 128 mld_polyw1_pack_32
     (mld_polyvec
       (mld_verify_w1 5 mld_poly_use_hint_32 rho zhat cphat pkb 55
         (\t. (sigb:num->byte) (3248 + t))))`;;

let VI65_OK_THM = GEN_ALL(prove
 (subst [VI65_W1B,`w1b:num->byte`]
  `mld_verify_internal_ok 6 5 48 mld_polyz_unpack_19 640 524092
       mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49 (sigb:num->byte)
       (pkb:num->byte) mu <=>
     mld_polyvec_chknorm 5
       (mld_polyvec_unpack 640 mld_polyz_unpack_19 (\j. sigb(48 + j)))
       (word 524092) = word 0 /\
     (!i. i < 6
          ==> mld_unpack_hints_ret 55 6 (\t. sigb(3248 + t)) i = word 0) /\
     (!j. j < 48
          ==> sigb j =
              mld_shake256_byte 832
               (mu + 2 EXP 512 * num_of_bytelist(list_of_seq w1b 768)) j)`,
  REWRITE_TAC[mld_verify_internal_ok] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ARITH_RULE `48 + 5 * 640 + t = 3248 + t`;
              ARITH_RULE `64 + 6 * 128 = 832`; ARITH_RULE `6 * 128 = 768`]));;

let VI65_ZX128 = WORD_BLAST `!x:int64. word_zx(word_zx x:int128):int64 = x`;;

let VI65_FINAL_THMS = [WORD_ZX_ZX_32_64_32; WORD_ZX_0; VI65_OK_THM; VI65_ZX128];;

(* ------------------------------------------------------------------------- *)
(* The failure of the norm check: -6 in w27 and the cleanup.                 *)
(* ------------------------------------------------------------------------- *)

let VI65_NF_TAC b =
  FULL_INIT_TAC THEN ARM_STEPS_TAC VI65_EXEC [1] THEN
  VERIF_PC_TAC [VI65_NORMOK_TM] THEN ARM_STEPS_TAC VI65_EXEC [2] THEN
  VI65_CLEANUP_TAC b VI65_ALLOWED_OLD 2 THEN
  VERIF_FINAL_TAC VI65_FINAL_THMS THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_EVENTS_TAC [`old:(uarch_event)list`];;

(* ------------------------------------------------------------------------- *)
(* join4 (+0x180c): mu is ready at b + 9728, z still unpacked at b + 4480.   *)
(* ------------------------------------------------------------------------- *)

let VI65_MU =
  `if word_zx (ext:int64) = (word 0:int32)
   then mld_verify_mu 1952 pkb prelen PRE' mlen M else M MOD 2 EXP 512`;;

let VI65_JOIN4 b =
  subst [VI65_Z,`VI65Z:num->int32`; VI65_MU,`VI65MU:num`]
  (parse_term(Printf.sprintf
   "\\s. aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
        read PC s = word (pc + mldsa65_verify_internal_join4) /\\
        %s /\\
        read X19 s = sig /\\ read X20 s = pk /\\
        read X22 s = word_add stackpointer (word %d) /\\
        read X26 s = word_add stackpointer (word %d) /\\
        read X27 s = word_add stackpointer (word %d) /\\
        read X28 s = word_add stackpointer (word %d) /\\
        (!i. i < 1280
             ==> read (memory :> bytes32 (word_add stackpointer (word (%d + 4 * i))))
                   s = VI65Z i) /\\
        read (memory :> bytes (word_add stackpointer (word %d),64)) s = VI65MU /\\
        read (memory :> bytes128 (word_add stackpointer (word %d))) s =
          mld_chunk128 sigb 0 /\\
        read (memory :> bytes128 (word_add stackpointer (word %d))) s =
          mld_chunk128 sigb 1 /\\
        read (memory :> bytes128 (word_add stackpointer (word %d))) s =
          mld_chunk128 sigb 2"
   (VI65_FRAME_FACTS b) (b + 4480) (b + 4480) (b + 4480) (b + 4480) (b + 4480)
   (b + 9728) (b + 9664) (b + 9680) (b + 9696)));;

(*** mu copied from m (ext nonzero): the 4 chunks of the 64 bytes at m ***)

let VI65_CHUNK_NORM_RULE th =
  REWRITE_RULE[WORD_ADD_0; EXP; DIV_1]
   (CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) th);;

let VI65_M_CHUNKS_TAC =
  SUBGOAL_THEN `64 <= mlen` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; mk_small_numeral i;
                  `s0:armstate`] VERIF_BYTES128_OF_BYTES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o VI65_CHUNK_NORM_RULE)) [0;1;2;3];;

let VI65_MU_OF_CHUNKS_TAC a s =
  MP_TAC(SPECL [a; `M:num`; `4`; s] VERIF_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC];;

let VI65_COPY_TAC b =
  FULL_INIT_TAC THEN VI65_M_CHUNKS_TAC THEN
  ARM_STEPS_TAC VI65_EXEC [1] THEN VERIF_PC_TAC [VI65_NORMOK_TM] THEN
  ARM_STEPS_TAC VI65_EXEC [2] THEN VERIF_PC_TAC [VI65_EXT0] THEN
  ARM_STEPS_TAC VI65_EXEC (3--9) THEN
  VI65_MU_OF_CHUNKS_TAC (VI65_SP(b + 9728)) `s9:armstate` THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_EVENTS_TAC [`old:(uarch_event)list`];;

(* ------------------------------------------------------------------------- *)
(* The loop over the rows (head loop7 = +0x1b98, row i), with the buffers at *)
(* stackpointer + b + k: the scalars at 32 (the hints + 1), 40 (cp + 8), 304 *)
(* (-q in each lane), 320 and 336 (the TBL indices of polyt1_unpack), 336    *)
(* also prelen before the loop, the polynomials t1 (then the hints) at 352,  *)
(* w1 at 1376, the matrix at 2400, rho at 3424, cp at 3456, z (then zhat)    *)
(* at 4480, c2 at 9600, c~ at 9664, mu at 9728, w1' packed at 9792.          *)
(* ------------------------------------------------------------------------- *)

let VI65_W1NUM =
  mk_comb(`num_of_bytelist`,
          mk_comb(mk_comb(`list_of_seq:(num->byte)->num->byte list`,VI65_W1B),
                  `768`));;

let VI65_INV b =
  let n k = string_of_int(b + k) in
  let s = "\\i s. aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
    " ^ VI65_FRAME_FACTS b ^ " /\\
    read X20 s = word 18446744073701171199 /\\
    read X23 s = word 252236767799803904 /\\
    read X25 s = word_add stackpointer (word " ^ n 1376 ^ ") /\\
    read X28 s = word_add stackpointer (word " ^ n 352 ^ ") /\\
    read (Q8 :> bottomhalf) s = word 0xfafafafafcfcfcfc /\\
    read (memory :> bytes64 (word_add stackpointer (word " ^ n 32 ^ "))) s =
      word_add sig (word 3249) /\\
    read (memory :> bytes64 (word_add stackpointer (word " ^ n 40 ^ "))) s =
      word_add stackpointer (word " ^ n 3464 ^ ") /\\
    read (memory :> bytes128 (word_add stackpointer (word " ^ n 304 ^ "))) s =
      word 0xff801fffff801fffff801fffff801fff /\\
    read (memory :> bytes128 (word_add stackpointer (word " ^ n 320 ^ "))) s =
      word 0xffffff07ffffff06ffffff05ffffff04 /\\
    read (memory :> bytes128 (word_add stackpointer (word " ^ n 336 ^ "))) s =
      word 0xffffff03ffffff02ffffff01ffffff00 /\\
    read (memory :> bytes (word_add stackpointer (word " ^ n 3424 ^ "),32)) s =
      VI65RHO /\\
    (!j. j < 1280
         ==> read (memory :> bytes32
                    (word_add stackpointer (word (" ^ n 4480 ^ " + 4 * j)))) s =
             VI65ZHAT j) /\\
    (!j. j < 256
         ==> read (memory :> bytes32
                    (word_add stackpointer (word (" ^ n 3456 ^ " + 4 * j)))) s =
             VI65CPHAT j) /\\
    read (memory :> bytes (word_add stackpointer (word " ^ n 9728 ^ "),64)) s =
      VI65MU /\\
    read (memory :> bytes128 (word_add stackpointer (word " ^ n 9664 ^ "))) s =
      mld_chunk128 sigb 0 /\\
    read (memory :> bytes128 (word_add stackpointer (word " ^ n 9680 ^ "))) s =
      mld_chunk128 sigb 1 /\\
    read (memory :> bytes128 (word_add stackpointer (word " ^ n 9696 ^ "))) s =
      mld_chunk128 sigb 2 /\\
    ((!j. j < i ==> mld_unpack_hints_ret 55 6 (\\t. sigb(3248 + t)) j = word 0)
     ==> read X3 s = word i /\\
         read X19 s = word 8380417 /\\
         read X21 s = word_add stackpointer (word " ^ n 3456 ^ ") /\\
         read X24 s = word_add stackpointer (word " ^ n 3464 ^ ") /\\
         read X27 s = word_add sig (word 3248) /\\
         read X22 s = word_add pk (word (51 + 320 * i)) /\\
         (!j. j < 128 * i
              ==> read (memory :> bytes8
                         (word_add stackpointer (word (" ^ n 9792 ^ " + j)))) s =
                  VI65W1B j)) /\\
    (~(!j. j < i ==> mld_unpack_hints_ret 55 6 (\\t. sigb(3248 + t)) j = word 0)
     ==> read X27 s = word 4294967290)" in
  subst [VI65_MU,`VI65MU:num`; VI65_W1B,`VI65W1B:num->byte`;
         VI65_RHO,`VI65RHO:num`; VI65_ZHAT,`VI65ZHAT:num->int32`;
         VI65_CPHAT,`VI65CPHAT:num->int32`]
        (parse_term s);;

let VI65_PC2 =
  parse_term("if " ^ VI65_HINTSOK ^
             " then pc + mldsa65_verify_internal_loop7_exit5" ^
             " else pc + mldsa65_verify_internal_join3");;

(* ------------------------------------------------------------------------- *)
(* From join4 to the loop: the NTT of each polynomial of z, the copy of rho  *)
(* to F + 3424, the challenge from c~ and its NTT, and the constants of the  *)
(* loop.                                                                     *)
(* ------------------------------------------------------------------------- *)

let VI65_SPLIT5 = prove
 (`!(sp:int64) n x s.
     (!i. i < 1280
          ==> read (memory :> bytes32 (word_add sp (word (n + 4 * i)))) s =
              x i)
     ==> !p m. p < 5 /\ m = n + 1024 * p
               ==> !i. i < 256
                       ==> read (memory :> bytes32
                                   (word_add sp (word (m + 4 * i)))) s =
                           mld_poly_of x p i`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[mld_poly_of] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `256 * p + i`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `n + 4 * (256 * p + i) = (n + 1024 * p) + 4 * i`]);;

let VI65_JOIN5_MAP = prove
 (`!(sp:int64) n0 n1 n2 n3 n4 (f:(num->int32)->num->int32) x s.
     n1 = n0 + 1024 /\ n2 = n0 + 2048 /\ n3 = n0 + 3072 /\ n4 = n0 + 4096 /\
     (!i. i < 256
          ==> read (memory :> bytes32 (word_add sp (word (n0 + 4 * i)))) s =
              f (mld_poly_of x 0) i) /\
     (!i. i < 256
          ==> read (memory :> bytes32 (word_add sp (word (n1 + 4 * i)))) s =
              f (mld_poly_of x 1) i) /\
     (!i. i < 256
          ==> read (memory :> bytes32 (word_add sp (word (n2 + 4 * i)))) s =
              f (mld_poly_of x 2) i) /\
     (!i. i < 256
          ==> read (memory :> bytes32 (word_add sp (word (n3 + 4 * i)))) s =
              f (mld_poly_of x 3) i) /\
     (!i. i < 256
          ==> read (memory :> bytes32 (word_add sp (word (n4 + 4 * i)))) s =
              f (mld_poly_of x 4) i)
     ==> !i. i < 1280
             ==> read (memory :> bytes32 (word_add sp (word (n0 + 4 * i)))) s =
                 mld_polyvec_map f x i`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[mld_polyvec_map; mld_polyvec] THEN
  SUBGOAL_THEN `?p k. p < 5 /\ k < 256 /\ i = 256 * p + k` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`i DIV 256`; `i MOD 256`] THEN
    MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[DIVMOD_CHUNK] THEN
  SUBGOAL_THEN `p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4` MP_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)] THEN
  REWRITE_TAC[ARITH_RULE `!n k. n + 4 * (256 * 0 + k) = n + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 1 + k) = (n + 1024) + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 2 + k) = (n + 2048) + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 3 + k) = (n + 3072) + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 4 + k) = (n + 4096) + 4 * k`] THEN
  ASM_SIMP_TAC[]);;

let VI65_OR8 = prove
 (`!x:int64. aligned 16 x ==> word_or x (word 8) = word_add x (word 8)`,
  GEN_TAC THEN REWRITE_TAC[MLD_WRAP_ALIGNED_16_32] THEN
  DISCH_THEN(fun th -> MP_TAC th) THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let VI65_ZSPLIT_TAC n0 s =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_forall c && can (find_term ((=) VI65_Z)) c &&
       can (find_term ((=) `1280`)) c
    then
      let th1 = CONV_RULE(ONCE_DEPTH_CONV ETA_CONV) (MATCH_MP VI65_SPLIT5 th) in
      MAP_EVERY (fun p ->
        let pt = mk_small_numeral p and mt = mk_small_numeral(n0 + 1024 * p) in
        let th2 = SPECL [pt; mt] th1 in
        ASSUME_TAC(MP th2 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th2))))))
        (0--4)
    else NO_TAC);;

let VI65_PK_CHUNKS_TAC s =
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`pk:int64`; `1952`; `pkb:num->byte`; s;
                  mk_small_numeral i] BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
                    ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC) [0;1];;

let VI65_Q8BOT = prove
   (`read (Q8 :> bottomhalf) s = word_zx(read Q8 s):int64`,
    CONV_TAC(ONCE_DEPTH_CONV COMPONENT_CANON_CONV) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_ZEROTOP_64;
                bottomhalf; subword; read; FUN_EQ_THM] THEN
    REWRITE_TAC[word_zx; DIV_1; EXP; WORD_MOD_SIZE]);;

let VI65_Q8JOIN = WORD_BLAST
  `!q:int128. q = word_join (word_subword q (64,64):int64) (word_zx q:int64)`;;

(*** The fact about d8 (the shifts of polyt1_unpack, which the calls keep) ***)
(*** from that about q8, in state s                                        ***)

let VI65_D8_TAC s =
  SUBGOAL_THEN (subst [s,`s:armstate`]
    `read (Q8 :> bottomhalf) s = word 0xfafafafafcfcfcfc`) ASSUME_TAC THENL
   [REWRITE_TAC[VI65_Q8BOT] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV; ALL_TAC];;

(*** The value of q8 for the lemma of polyt1_unpack, from the fact about d8 ***)

let VI65_Q8_TAC s =
  ABBREV_TAC (subst [s,`s:armstate`]
    `h8 = word_subword (read Q8 s) (64,64):int64`) THEN
  SUBGOAL_THEN (subst [s,`s:armstate`]
    `read Q8 s = word_join (h8:int64) (word 0xfafafafafcfcfcfc:int64)`)
   ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      lhand(concl th) = subst [s,`s:armstate`] `read (Q8 :> bottomhalf) s`)) THEN
    REWRITE_TAC[VI65_Q8BOT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXPAND_TAC "h8" THEN
    SPEC_TAC(subst [s,`s:armstate`] `read Q8 s`,`q:int128`) THEN
    REWRITE_TAC[GSYM VI65_Q8JOIN];
    ALL_TAC];;

let VI65_CONST3 =
  MLDSA_NATIVE_IMAGE_CONST_RULE (layout "mldsa65_verify_internal_const3") 64;;

let VI65_MID_TAC b =
  let VI65_MCALL_TAC = VI65_CALL_GEN_TAC (`old2:(uarch_event)list`::VI65_ALLOWED) in
  let n k = mk_small_numeral(b + k) in
  let pz p = mk_comb(mk_comb(`mld_poly_of`,VI65_Z),mk_small_numeral p) in
  FULL_INIT_TAC THEN VI65_ZSPLIT_TAC (b + 4480) `s0:armstate` THEN
  VI65_CONSTS_TAC THEN
  FIRST_ASSUM(fun th ->
    if free_in `s0:armstate` (concl th)
    then (try ASSUME_TAC(MATCH_MP VI65_CONST3 th) with Failure _ -> NO_TAC)
    else NO_TAC) THEN
  ARM_STEPS_TAC VI65_EXEC (1--5) THEN
  VI65_MCALL_TAC "H_NTT" [`read X0 s`; pz 0; `pc:num`; `read SP s`;
    `read X30 s`] 6 THEN
  ARM_STEPS_TAC VI65_EXEC (7--8) THEN
  VI65_MCALL_TAC "H_NTT" [`read X0 s`; pz 1; `pc:num`; `read SP s`;
    `read X30 s`] 9 THEN
  ARM_STEPS_TAC VI65_EXEC (10--11) THEN
  VI65_MCALL_TAC "H_NTT" [`read X0 s`; pz 2; `pc:num`; `read SP s`;
    `read X30 s`] 12 THEN
  ARM_STEPS_TAC VI65_EXEC (13--14) THEN
  VI65_MCALL_TAC "H_NTT" [`read X0 s`; pz 3; `pc:num`; `read SP s`;
    `read X30 s`] 15 THEN
  ARM_STEPS_TAC VI65_EXEC (16--17) THEN
  VI65_MCALL_TAC "H_NTT" [`read X0 s`; pz 4; `pc:num`; `read SP s`;
    `read X30 s`] 18 THEN
  MP_TAC(SPECL [`stackpointer:int64`; n 4480; n 5504; n 6528; n 7552; n 8576;
                `mld_poly_ntt`; VI65_Z; `s18:armstate`] VI65_JOIN5_MAP) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  VI65_PK_CHUNKS_TAC `s18:armstate` THEN
  ARM_STEPS_TAC VI65_EXEC (19--25) THEN
  MP_TAC(SPECL [VI65_SP(b + 9664); `sigb:num->byte`; `3`; `s25:armstate`]
               VERIF_BYTES_OF_CHUNKS) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC] THEN
  MP_TAC(SPECL [VI65_SP(b + 3424); `pkb:num->byte`; `2`; `s25:armstate`]
               VERIF_BYTES_OF_CHUNKS) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC] THEN
  ARM_STEPS_TAC VI65_EXEC [26] THEN MLD_WRAP_GOT_TAC THEN
  VI65_MCALL_TAC "H_CHAL"
   [`read X0 s`; `read X1 s`; VI65_C; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 27 THEN
  ARM_STEPS_TAC VI65_EXEC (28--29) THEN
  VI65_MCALL_TAC "H_NTT" [`read X0 s`; VI65_CP; `pc:num`; `read SP s`;
    `read X30 s`] 30 THEN
  ARM_STEPS_TAC VI65_EXEC [31] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC VI65_EXEC (32--34) THEN
  ARM_STEPS_TAC VI65_EXEC [35] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC VI65_EXEC [36] THEN
  ARM_STEPS_TAC VI65_EXEC [37] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC VI65_EXEC (38--44) THEN
  SUBGOAL_THEN (mk_comb(`aligned 16:int64->bool`,VI65_SP(b + 3456))) ASSUME_TAC
  THENL [CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
  ARM_STEPS_TAC VI65_EXEC [45] THEN
  FIRST_ASSUM(fun th ->
    if concl th = mk_comb(`aligned 16:int64->bool`,VI65_SP(b + 3456))
    then RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP VI65_OR8 th]) else NO_TAC) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  ARM_STEPS_TAC VI65_EXEC (46--53) THEN VI65_D8_TAC `s53:armstate`;;

(* ------------------------------------------------------------------------- *)
(* The loop body for row i.                                                  *)
(* ------------------------------------------------------------------------- *)

let VI65_HOK_TM = parse_term VI65_HOK;;

let VI65_ROWS_TAC =
  MP_TAC(BETA_RULE(SPECL [mk_abs(`i:num`,VI65_HOK_TM); `6`; `i:num`]
                         VERIF_ROWS)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && is_forall(lhand(concl th)) &&
    fst(dest_forall(lhand(concl th))) = `j:num`)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC];;

let VI65_T1 = `mld_polyt1_unpack (\j. (pkb:num->byte) (32 + 320 * i + j))`;;
let VI65_SHL = mk_comb(`mld_poly_shiftl`,VI65_T1);;
let VI65_NTT1 = mk_comb(`mld_poly_ntt`,VI65_SHL);;
let VI65_PWM =
  list_mk_comb(`mld_poly_pointwise_montgomery`,[VI65_NTT1;VI65_CPHAT]);;
let VI65_ROWL =
  subst [VI65_RHO,`rho:num`; VI65_ZHAT,`zhat:num->int32`]
   `mld_polyvec_matrix_row_lazy 5 rho zhat i`;;
let VI65_SUBL = list_mk_comb(`mld_poly_sub`,[VI65_ROWL;VI65_PWM]);;
let VI65_REDL = mk_comb(`mld_poly_reduce`,VI65_SUBL);;
let VI65_INVTL = mk_comb(`mld_poly_invntt_tomont`,VI65_REDL);;
let VI65_CADDQL = mk_comb(`mld_poly_caddq`,VI65_INVTL);;

let VI65_ALLOWED_LOOP =
  `front:(uarch_event)list`::`i:num`::VI65_ALLOWED;;

let VI65_LOOP_CALL_TAC = VI65_CALL_GEN_TAC VI65_ALLOWED_LOOP;;

(*** The inputs of the lemmas of inline_sign_map.ml, whose addresses are ***)
(*** fp + (off + 4 * i), as the simulation forms them with fp = sp + b:   ***)
(*** sp + (b + off + 4 * i); and the folding of the outputs to sp + N + 4i ***)

let VI65_UNFOLD_TAC b off =
  let n = b + off in
  let eq = ARITH_RULE(parse_term(Printf.sprintf
    "!i. %d + 4 * i = %d + %d + 4 * i" n b off)) in
  let pat = parse_term(Printf.sprintf
    "word_add (stackpointer:int64) (word (%d + 4 * i))" n) in
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_forall c && can (find_term (fun t -> can (term_match [] pat) t)) c
      then REWRITE_RULE[eq] th else fail()) asl in
    MAP_EVERY ASSUME_TAC ths);;

let VI65_FOLD_CONV tm =
  match tm with
    Comb(Const("word",_),Comb(Comb(Const("+",_),m),
           Comb(Comb(Const("+",_),n),t))) when is_numeral m && is_numeral n ->
      let th = SPECL [m;n;t] ADD_ASSOC in
      CONV_RULE(RAND_CONV(RAND_CONV(LAND_CONV NUM_ADD_CONV))) (AP_TERM (rator tm) th)
  | _ -> failwith "VI65_FOLD_CONV";;

let VI65_FOLD_TAC =
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  RULE_ASSUM_TAC(fun th ->
    if is_forall(concl th) && free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV VI65_FOLD_CONV) th else th);;

let VI65_BODY1_TAC b =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  VERIF_GEN_TAIL_TAC false "front" THEN
  FULL_INIT_TAC THEN VI65_ROWS_TAC THEN
  ARM_STEPS_TAC VI65_EXEC (1--6) THEN MLD_WRAP_GOT_TAC THEN
  VI65_LOOP_CALL_TAC "H_ROW"
   [`read X0 s`; `read X1 s`; `read X2 s`; VI65_RHO; VI65_ZHAT; `i:num`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 7 THEN
  ARM_STEPS_TAC VI65_EXEC (8--11) THEN
  SUBGOAL_THEN
   `!j. j < 320
        ==> read(memory :> bytes8(word_add pk (word((32 + 320 * i) + j)))) s11 =
            (pkb:num->byte)(32 + 320 * i + j)` ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if lhand(concl th) = `read X9 s11`
    then ASSUME_TAC(TRANS th (WORD_RULE
          `word_add pk (word (51 + 320 * i)):int64 =
           word_add pk (word ((32 + 320 * i) + 19))`))
    else NO_TAC) THEN
  VI65_Q8_TAC `s11:armstate` THEN
  VI65_LOOP_CALL_TAC "H_T1"
   [`read X28 s`; `word_add (pk:int64) (word (32 + 320 * i))`;
    `\j. (pkb:num->byte)(32 + 320 * i + j)`;
    `h8:int64`; `pc:num`] 12 THEN
  VI65_UNFOLD_TAC b 352 THEN
  VI65_LOOP_CALL_TAC "H_SHL" [`read SP s`; VI65_T1; `pc:num`] 13 THEN
  VI65_FOLD_TAC THEN
  ARM_STEPS_TAC VI65_EXEC [14] THEN
  VI65_LOOP_CALL_TAC "H_NTT" [`read X0 s`; VI65_SHL; `pc:num`; `read SP s`;
    `read X30 s`] 15 THEN
  ARM_STEPS_TAC VI65_EXEC [16] THEN
  VI65_LOOP_CALL_TAC "H_PWM"
   [`read X28 s`; `read X21 s`; VI65_NTT1; VI65_CPHAT; `pc:num`] 17 THEN
  VI65_UNFOLD_TAC b 352 THEN VI65_UNFOLD_TAC b 1376 THEN
  VI65_LOOP_CALL_TAC "H_SUB" [`read SP s`; VI65_PWM; VI65_ROWL; `pc:num`] 18 THEN
  VI65_FOLD_TAC THEN
  VI65_LOOP_CALL_TAC "H_RED" [`read X25 s`; VI65_SUBL; `pc:num`] 19 THEN
  ARM_STEPS_TAC VI65_EXEC (20--21) THEN
  VI65_LOOP_CALL_TAC "H_INV" [`read X0 s`; VI65_REDL; `pc:num`; `read SP s`;
    `read X30 s`] 22 THEN
  ARM_STEPS_TAC VI65_EXEC [23] THEN
  VI65_LOOP_CALL_TAC "H_CADDQ" [`read X25 s`; VI65_INVTL; `pc:num`] 24;;

(*** The lazy product of the row made nonnegative is that of the spec ***)

let VI65_CADDQ = mk_comb(`mld_poly_caddq`,
  mk_comb(`mld_poly_invntt_tomont`, mk_comb(`mld_poly_reduce`,
   list_mk_comb(`mld_poly_sub`,[
    subst [VI65_RHO,`rho:num`; VI65_ZHAT,`zhat:num->int32`]
     `mld_polyvec_pointwise_acc_montgomery 5
       (\j. mld_polyvec_matrix_expand 5 rho (1280 * i + j)) zhat`;
    VI65_PWM]))));;

let VI65_ZHAT_BOUND =
  subst [VI65_ZHAT,`zhat:num->int32`]
   `!j. j < 1280 ==> abs(ival((zhat:num->int32) j)) < &94279689`;;

let VI65_ZHAT_BOUND_TAC =
  SUBGOAL_THEN VI65_ZHAT_BOUND ASSUME_TAC THENL
   [MP_TAC(SPECL [`5`; VI65_Z] MLD_LAZY_POLYVEC_NTT_BOUND) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[mld_polyvec_unpack; mld_polyvec; MLD_LAZY_Z_UNPACK_BOUND];
    ALL_TAC];;

let VI65_CADDQ_TAC =
  FIRST_ASSUM(fun th ->
    if not(is_forall(concl th)) ||
       not(can (find_term ((=) VI65_CADDQL)) (concl th))
    then failwith "VI65_CADDQ_TAC" else
    SUBGOAL_THEN (subst [VI65_CADDQ,VI65_CADDQL] (concl th)) ASSUME_TAC THENL
     [X_GEN_TAC `n:num` THEN
      DISCH_THEN(fun nth -> REWRITE_TAC[MP (SPEC `n:num` th) nth] THEN
                            ASSUME_TAC nth) THEN
      MP_TAC(SPECL [`6`; `5`; VI65_RHO; VI65_ZHAT; VI65_PWM; `i:num`; `n:num`]
                   MLD_LAZY_VERIFY) THEN
      CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[MLD_LAZY_POINTWISE_BOUND] THEN CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[]];
      ALL_TAC]);;

let VI65_HINTS = `mld_unpack_hints 55 (\t. (sigb:num->byte) (3248 + t)) i`;;
let VI65_UH = list_mk_comb(`mld_poly_use_hint_32`,[VI65_CADDQ;VI65_HINTS]);;

let VI65_BODY2_TAC b =
  VI65_CADDQ_TAC THEN
  VI65_BYTES_SLICE_TAC
   `!j. j < 61
        ==> read(memory :> bytes8(word_add sig (word(3248 + j)))) s24 =
            (sigb:num->byte)(3248 + j)` THEN
  VI65_LOOP_CALL_TAC "H_HINTS"
   [`read SP s`; `read X27 s`; `\t. (sigb:num->byte)(3248 + t)`; `i:num`;
    `read X22 s`; `pc:num`] 25 THEN
  VI65_FOLD_TAC;;

(*** The row fails: the hints do not unpack, the code is at join3 ***)

let VI65_BODY_FAIL_TAC =
  VERIF_MP_CASE_TAC (mk_neg VI65_HOK_TM) THEN
  VERIF_PC_TAC [VI65_HOK_TM] THEN
  VERIF_FINAL_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
      REWRITE_TAC[ARITH_RULE `i < i + 1`; ASSUME (mk_neg VI65_HOK_TM)] THEN
      NO_TAC) THEN
  TRY(DISCH_TAC THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_EVENTS_TAC [`front:(uarch_event)list`];;

(*** The row succeeds: use_hint and the packing of w1, and the loop test ***)

let VI65_PC_OK_TAC =
  ASM_CASES_TAC `i + 1 < 6` THENL
   [SUBGOAL_THEN `~(i + 1 = 6)` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `i + 1 < 6`; ASSUME `~(i + 1 = 6)`];
    SUBGOAL_THEN `i + 1 = 6` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN VI65_HINTSOK_TM ASSUME_TAC THENL
     [VERIF_IMP_CASE_TAC `~(i + 1 < 6)`; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `~(i + 1 < 6)`; ASSUME `i + 1 = 6`;
                ASSUME VI65_HINTSOK_TM]];;

let VI65_JOIN_W1_TAC =
  DISCH_TAC THEN REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC THEN NO_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  MATCH_MP_TAC VEC_JOIN_POLY THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[MATCH_MP (SPEC_ALL VERIF_W1B_ROW_32) (ASSUME `k < 128`)] THEN
    REWRITE_TAC[mld_verify_w1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    FIRST_ASSUM(fun th ->
      MATCH_MP_TAC(REWRITE_RULE[GSYM ADD_ASSOC] th)) THEN
    FIRST_ASSUM ACCEPT_TAC];;

let VI65_BODY_OK_TAC b =
  VERIF_MP_CASE_TAC VI65_HOK_TM THEN
  RULE_ASSUM_TAC(fun th -> if concl th = VI65_HOK_TM then th else
    REWRITE_RULE[EQT_INTRO(ASSUME VI65_HOK_TM)] th) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) && free_in `mld_unpack_hints` (concl th)
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  VI65_FOLD_TAC THEN
  ARM_STEPS_TAC VI65_EXEC (26--36) THEN
  VI65_LOOP_CALL_TAC "H_USEHINT"
   [`read X25 s`; `read X28 s`; VI65_CADDQ; VI65_HINTS; `pc:num`] 37 THEN
  VI65_UNFOLD_TAC b 1376 THEN
  VI65_LOOP_CALL_TAC "H_W1PACK"
   [`read SP s`; VI65_UH; `i:num`; `read X22 s`; `pc:num`] 38 THEN
  VI65_FOLD_TAC THEN
  ARM_STEPS_TAC VI65_EXEC [39] THEN
  VERIF_FINAL_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN
  CONJ_TAC THENL [VI65_PC_OK_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [VI65_JOIN_W1_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN X_GEN_TAC `j:num` THEN
    DISCH_TAC THEN ASM_CASES_TAC `j:num = i` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && free_in `mld_unpack_hints_ret` (concl th) &&
        is_imp(snd(dest_forall(concl th))))) THEN
      MATCH_MP_TAC(ARITH_RULE `j < i + 1 /\ ~(j = i) ==> j < i`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_EVENTS_TAC [`front:(uarch_event)list`];;

(* ------------------------------------------------------------------------- *)
(* After the loop (loop7_exit5, state 0), if all hints unpack: c2 = H(mu ||  *)
(* w1', 48) by mld_H65 (bl at 13, the callee at 14), then the branch-free    *)
(* compare of c~ (F + 9664) and c2 (F + 9600) as three 128-bit chunks, csel  *)
(* w27 at 48, b join3 at 49, the cleanup. The condition of the csel is       *)
(* reduced to cc0 = dd0 /\ cc1 = dd1 /\ cc2 = dd2 by bit-blasting once       *)
(* (VI65_CMP_MEMO).                                                          *)
(* ------------------------------------------------------------------------- *)

let VI65_ALLOWED_OLD2 = `old2:(uarch_event)list`::VI65_ALLOWED;;

let VI65_W1_BYTES_TAC b s =
  MP_TAC(SPECL [VI65_SP(b + 9792); `768`; VI65_W1B; s]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `mld_polyw1_pack_32`)) (concl th))) THEN
    UNDISCH_TAC `j < 768` THEN ARITH_TAC;
    DISCH_TAC];;

let VI65_SQ =
  subst [VI65_MU,`mu:num`; VI65_W1NUM,`w:num`]
   `mld_shake256_byte 832 (mu + 2 EXP 512 * w)`;;

let VI65_C2_NORM_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `mld_shake256_byte` (concl th) &&
       free_in `64 + 768 + 0` (concl th)
    then REWRITE_RULE[ARITH_RULE `64 + 768 + 0 = 832`;
                      ARITH_RULE `8 * 64 = 512`; MULT_CLAUSES; ADD_CLAUSES] th
    else th);;

let VI65_C2_CHUNKS_TAC a s =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && can (term_match [] `read (memory :> bytes(x,48)) s = n`) c &&
       fst(dest_pair(rand(rand(rand(rator(lhand c)))))) = a
    then ASSUME_TAC(MATCH_MP BYTES8_OF_BYTES th) else NO_TAC) THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [a; `48`; VI65_SQ; s; mk_small_numeral i]
                 BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
                    ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
    DISCH_TAC) [0;1;2];;

let VI65_CHUNK_VARS = ["cc0";"cc1";"cc2";"dd0";"dd1";"dd2"];;

let VI65_CHUNK_ABBREV_TAC =
  let mk n i f = (mk_var(n ^ string_of_int i,`:int128`),
                  mk_comb(mk_comb(`mld_chunk128`,f),mk_small_numeral i)) in
  let abbs = map (fun i -> mk "cc" i `sigb:num->byte`) [0;1;2] @
             map (fun i -> mk "dd" i VI65_SQ) [0;1;2] in
  MAP_EVERY (fun (v,t) ->
    ABBREV_TAC (mk_eq(v,t)) THEN
    FIRST_ASSUM(fun eth ->
      if concl eth <> mk_eq(t,v) then NO_TAC else
      RULE_ASSUM_TAC(fun th ->
        let c = concl th in
        if is_eq c && rhs c = t &&
           can (term_match [] `read (memory :> bytes128 a) s = x:int128`) c
        then TRANS th eth else th))) abbs;;

let VI65_CMP_MEMO = ref ([]:(term * thm) list);;

let VI65_OK_TM =
  mk_comb(`mld_verify_internal_ok 6 5 48 mld_polyz_unpack_19 640 524092
     mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49 (sigb:num->byte)
     (pkb:num->byte)`, VI65_MU);;

let VI65_ZX_COND = prove
 (`!b. (word_zx:int32->int64) (if b then word 0 else word 4294967290) =
       if b then word 0 else word 4294967290`,
  GEN_TAC THEN COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV);;

let VI65_ZX_COND2 = prove
 (`!b. (word_zx:int32->int64)
         (word_zx (if b then word 0 else word 4294967290:int64)) =
       if b then word 0 else word 4294967290`,
  GEN_TAC THEN COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV);;

let VI65_CC_EQ = `cc0:int128 = dd0 /\ cc1:int128 = dd1 /\ cc2:int128 = dd2`;;

let VI65_CMP_EQ_TAC s =
  W(fun (asl,w) ->
    let th = snd(find (fun (_,th) ->
      can (term_match [] (subst [s,`s:armstate`] `read X27 s = x`)) (concl th))
      asl) in
    let c = rand(rator(rator(rand(rhs(concl th))))) in
    let tm = list_mk_forall([`cc0:int128`;`cc1:int128`;`cc2:int128`;
                             `dd0:int128`;`dd1:int128`;`dd2:int128`],
      mk_eq(c, VI65_CC_EQ)) in
    let lem = try assoc tm (!VI65_CMP_MEMO) with Failure _ ->
      let th = BITBLAST_RULE tm in
      (VI65_CMP_MEMO := (tm,th)::(!VI65_CMP_MEMO); th) in
    SUBGOAL_THEN (mk_eq(VI65_CC_EQ,VI65_OK_TM))
     ASSUME_TAC THENL
     [W(fun (asl,w) -> REWRITE_TAC(mapfilter (fun (_,th) ->
        let c = concl th in
        if is_eq c && is_var(rhs c) && mem (fst(dest_var(rhs c))) VI65_CHUNK_VARS
        then SYM th else fail()) asl)) THEN
      REWRITE_TAC[VI65_OK_THM; ASSUME VI65_NORMOK_TM;
                  EQT_INTRO(ASSUME VI65_HINTSOK_TM)] THEN
      MP_TAC(ISPECL [`sigb:num->byte`; VI65_SQ; `3`] MLD_CHUNK128_EQ) THEN
      CONV_TAC(LAND_CONV(LAND_CONV EXPAND_CASES_CONV)) THEN
      REWRITE_TAC[ARITH_RULE `16 * 3 = 48`] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MESON_TAC[];
      FIRST_X_ASSUM(fun eqth ->
        if concl eqth <> mk_eq(VI65_CC_EQ,VI65_OK_TM)
        then NO_TAC else
        RULE_ASSUM_TAC(fun th ->
          if can (term_match [] (subst [s,`s:armstate`] `read X27 s = x`))
                 (concl th)
          then CONV_RULE(DEPTH_CONV WORD_RED_CONV)
                (REWRITE_RULE[lem; eqth; VI65_ZX_COND] th) else th))] THEN
    ABBREV_TAC (mk_eq(`okb:bool`,VI65_OK_TM)) THEN
    FIRST_ASSUM(fun eqth ->
      if concl eqth <> mk_eq(VI65_OK_TM,`okb:bool`) then NO_TAC else
      RULE_ASSUM_TAC(fun th ->
        if can (term_match [] (subst [s,`s:armstate`] `read X27 s = x`))
               (concl th)
        then REWRITE_RULE[eqth] th else th)));;

let VI65_HF_LEMMA = prove
 (`!P. ~(!i. i < 6 ==> P i) ==> ~(!j. j < (minimal i. ~P i) + 1 ==> P j)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?i. ~(P:num->bool) i` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN BETA_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  EXISTS_TAC `minimal i. ~(P:num->bool) i` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let VI65_HF_X27_TAC =
  let lam = mk_abs(`i:num`,VI65_HOK_TM) in
  let th0 = BETA_RULE(ISPEC lam VI65_HF_LEMMA) in
  let hth = UNDISCH th0 in
  let c = concl hth in
  FIRST_ASSUM(fun nh ->
    if not(aconv (concl nh) (lhand(concl th0))) then NO_TAC else
    let cth = PROVE_HYP (EQ_MP (ALPHA (concl nh) (lhand(concl th0))) nh) hth in
    FIRST_X_ASSUM(fun th ->
      if is_imp(concl th) && aconv (lhand(concl th)) c
      then ASSUME_TAC(MP th (EQ_MP (ALPHA c (lhand(concl th))) cth))
      else NO_TAC));;

let VI65_POST_HF_TAC b =
  REWRITE_TAC[EQF_INTRO(ASSUME (mk_neg VI65_HINTSOK_TM))] THEN
  FULL_INIT_TAC THEN VI65_HF_X27_TAC THEN
  VI65_CLEANUP_TAC b VI65_ALLOWED_OLD2 0 THEN
  VERIF_FINAL_TAC VI65_FINAL_THMS THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_EVENTS_TAC [`old2:(uarch_event)list`];;

let VI65_EMPTY_FACTS_TAC b s =
  SUBGOAL_THEN (subst [s,`s:armstate`] `read (memory :> bytes(word 0,0)) s = 0`)
   ASSUME_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]; ALL_TAC] THEN
  SUBGOAL_THEN (subst [VI65_SP(b - 544),`a:int64`]
    `nonoverlapping_modulo (2 EXP 64) (val (a:int64),544) (0,0)`) ASSUME_TAC
  THENL [MATCH_MP_TAC NONOVERLAPPING_MODULO_TRIVIAL THEN REWRITE_TAC[];
         ALL_TAC];;

let VI65_POST_OK_TAC b =
  REWRITE_TAC[EQT_INTRO(ASSUME VI65_HINTSOK_TM)] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC VI65_EXEC (1--12) THEN
  VI65_W1_BYTES_TAC b `s12:armstate` THEN
  VI65_EMPTY_FACTS_TAC b `s12:armstate` THEN MLD_WRAP_GOT_TAC THEN
  ARM_STEPS_TAC VI65_EXEC [13] THEN
  VI65_CALL_GEN_TAC VI65_ALLOWED_OLD2 "H_H65"
   [`read X0 s`; `48`; `read X2 s`; `64`; `read X4 s`; `768`; `word 0:int64`;
    `0`; VI65_MU; VI65_W1NUM; `0`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 14 THEN
  MLD_WRAP_EMPTY_REGIONS_TAC THEN
  VI65_C2_NORM_TAC THEN VI65_C2_CHUNKS_TAC (VI65_SP(b + 9600)) `s14:armstate` THEN
  VI65_CHUNK_ABBREV_TAC THEN
  ARM_STEPS_TAC VI65_EXEC (15--49) THEN
  VI65_CMP_EQ_TAC `s49:armstate` THEN
  VI65_CLEANUP_TAC b VI65_ALLOWED_OLD2 49 THEN
  VERIF_FINAL_TAC [WORD_ZX_ZX_32_64_32; WORD_ZX_0; VI65_ZX128; VI65_ZX_COND2] THEN
  VERIF_EVENTS_ONLY_TAC THEN ASM_CASES_TAC `okb:bool` THEN
  VERIF_EVENTS_TAC [`old2:(uarch_event)list`];;

let VI65_POST_TAC b =
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN VERIF_GEN_TAIL_TAC true "old2" THEN
  ASM_CASES_TAC VI65_HINTSOK_TM THENL [VI65_POST_OK_TAC b; VI65_POST_HF_TAC b];;

(* ------------------------------------------------------------------------- *)
(* mu from the message (ext = 0): tr = SHAKE256(pk, 64) by the inlined       *)
(* sponge (VI65_SHAKE_TH, at 3, from in_shake256_init to the bl of mld_H65   *)
(* at 4), mu = H(tr || pre || m, 64) by mld_H65 (5), and the zeroing of tr.  *)
(* ------------------------------------------------------------------------- *)

let VI65_PKNUM = `num_of_bytelist(list_of_seq (pkb:num->byte) 1952)`;;

let VI65_TRNUM =
  subst [VI65_PKNUM,`p:num`]
   `num_of_bytelist(list_of_seq (mld_shake256_byte 1952 p) 64)`;;

let VI65_HASH_TAC b =
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC VI65_EXEC [1] THEN VERIF_PC_TAC [VI65_NORMOK_TM] THEN
  ARM_STEPS_TAC VI65_EXEC [2] THEN VERIF_PC_TAC [VI65_EXT0] THEN
  MP_TAC(SPECL [`pk:int64`; `1952`; `pkb:num->byte`; `s2:armstate`]
               READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  VI65_CALL_GEN_TAC VI65_ALLOWED_OLD "H_SHAKE"
   [`read SP s`; `read X20 s`; VI65_PKNUM; `read X21 s`; `read X23 s`;
    `read X24 s`; `word prelen:int64`; `pc:num`] 3 THEN
  ARM_STEPS_TAC VI65_EXEC [4] THEN MLD_WRAP_GOT_TAC THEN
  VI65_CALL_GEN_TAC VI65_ALLOWED_OLD "H_H65"
   [`read X0 s`; `64`; `read X2 s`; `64`; `read X4 s`; `prelen:num`;
    `read X6 s`; `mlen:num`; VI65_TRNUM; `PRE':num`; `M:num`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 5 THEN
  ARM_STEPS_TAC VI65_EXEC (6--10) THEN
  RULE_ASSUM_TAC(fun th ->
    if free_in `2 EXP (8 * 64)` (concl th)
    then REWRITE_RULE[ARITH_RULE `8 * 64 = 512`] th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[mld_verify_mu; WORD_ZX_ZX_32_64_32; WORD_ZX_0] THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_EVENTS_TAC [`old:(uarch_event)list`];;

(* ------------------------------------------------------------------------- *)
(* The row of the loop: stage 1 (row_lazy to caddq), the hints, and the two  *)
(* outcomes.                                                                 *)
(* ------------------------------------------------------------------------- *)

let VI65_BODY_TAC b =
  VI65_BODY1_TAC b THEN VI65_BODY2_TAC b THEN
  ASM_CASES_TAC VI65_HOK_TM THENL [VI65_BODY_OK_TAC b; VI65_BODY_FAIL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Each case of the alignment of the stack, with the buffers at              *)
(* stackpointer + b: the prologue to the norm check, then either its failure *)
(* or mu (hash or copy), the setup of the loop, the loop and the end.        *)
(* ------------------------------------------------------------------------- *)

let VI65_CASE_TAC b =
  VI65_SP_BOUNDS_TAC THEN VI65_ZHAT_BOUND_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mldsa65_verify_internal_after_mldsa65_polyvecl_chknorm` (VI65_PRE b) THEN
  CONJ_TAC THENL
   [VI65_PROLOGUE_TAC b THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    VERIF_EVENTS_ONLY_TAC THEN VERIF_DISCHARGE_TAC;
    VI65_GEN_OLD_TAC "old" THEN
    ASM_CASES_TAC VI65_NORMOK_TM THEN FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THENL
     [ENSURES_EVENTS_WHILE_UP2_TAC (parse_term VI65_K)
       `pc + mldsa65_verify_internal_loop7` VI65_PC2 (VI65_INV b) THEN
      REPEAT CONJ_TAC THENL
       [COND_CASES_TAC THEN ARITH_TAC;
        REWRITE_TAC[ENUMERATEL; APPEND; MULT_CLAUSES; ADD_CLAUSES;
                    CONJUNCT1 LT; LT_REFL] THEN
        REWRITE_TAC[GSYM APPEND_ASSOC] THEN
        ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa65_verify_internal_join4`
         (VI65_JOIN4 b) THEN
        CONJ_TAC THENL
         [ASM_CASES_TAC VI65_EXT0 THEN FIRST_ASSUM(fun th -> REWRITE_TAC[th])
          THEN VI65_GEN_OLD_TAC "old" THENL
           [VI65_HASH_TAC b; VI65_COPY_TAC b];
          VI65_GEN_OLD_TAC "old2" THEN VI65_MID_TAC b THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          VERIF_EVENTS_ONLY_TAC THEN VERIF_EVENTS_TAC [`old2:(uarch_event)list`]];
        VI65_BODY_TAC b;
        VI65_POST_TAC b];
      VI65_NF_TAC b]];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let VI65_CALLEES_TAC =
  FIRST_ASSUM(fun th ->
    let m1 = CONJUNCT1 th and m2 = CONJUNCT2 th in
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_ret_full_contract] m1)
     "H_MEMSET" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL m2)
     "H_H65" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
               (MATCH_MP MEMSET_RET_FULL_CONTRACT m1)) "H_CHAL" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP VI65_ROW_FULL
       (CONJ (MATCH_MP MEMSET_RET_FULL_CONTRACT m1) m2)) "H_ROW" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP VI65_HINTS_TH m1) "H_HINTS") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_CHKNORM" THEN
  MAP_EVERY (fun (th,k) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th ("H_Z"^string_of_int k))
   (zip VI65_Z_THS (0--4)) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC VI65_SHAKE_TH "H_SHAKE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC VI65_T1_TH "H_T1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC VI65_SHL_TH "H_SHL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC VI65_PWM_TH "H_PWM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC VI65_SUB_TH "H_SUB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC VI65_RED_TH "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC VI65_INV_FULL "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC VI65_CADDQ_TH "H_CADDQ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC VI65_USEHINT_TH "H_USEHINT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC VI65_W1PACK_TH "H_W1PACK";;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN VI65_CALLEES_TAC THEN
  CONCRETIZE_F_EVENTS_TAC VI65_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst VI65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 12448):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--29) THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_DREG_TAC ("d"^string_of_int n^"_init")
     (mk_const("D"^string_of_int n,[]))) (8--15) THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN VI65_CASE_TAC 1696;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN VI65_CASE_TAC 1680]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;
