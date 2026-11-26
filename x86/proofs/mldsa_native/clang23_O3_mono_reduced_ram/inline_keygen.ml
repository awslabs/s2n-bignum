(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Loops and regions that clang 23 -O3 inlines into mldsa{44,65,87}_        *)
(* pk_from_sk and mldsa{44,65,87}_keypair_internal in the monolithic         *)
(* reduced-RAM build, as lemmas from a label of the code to another that     *)
(* the proofs of the callers use as they use the theorem for a subroutine    *)
(* (see inline_sign.ml).                                                     *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_api.ml";;
needs "x86/proofs/utils/mldsa_native_signing.ml";;
needs "x86/proofs/utils/mldsa_native_verify.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/chknorm_tools.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sponge_region.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_verify.ml";;

(* ------------------------------------------------------------------------- *)
(* The norm check of a polynomial that pk_from_sk makes on s2 after each     *)
(* unpacking into the buffer at rsp0 + 448 (mld_poly_chknorm with the bound  *)
(* 3 = eta + 1, inlined as a loop of 256 iterations): the mask, all ones or  *)
(* zero, of the 256 coefficients is in the 32 bits of the register reg,      *)
(* which the region clears first, as well as RAX, the index. The region      *)
(* starts after the call of the unpacking, at the instruction that clears    *)
(* reg, and ends at the exit of the loop.                                    *)
(* ------------------------------------------------------------------------- *)

let PKSCAN_STMT_G fn hexpr exit reg boff bnd =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e x rsp0 pc.
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
              read RIP s = word (pc + %s) /\\
              read RSP s = rsp0 /\\
              (!i. i < 256
                   ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4 * i)))) s =
                       (x:num->int32) i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\
              read %s s = word_zx(mld_poly_chknorm x (word %d):int32) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),1024] []))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; %s] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events])"
  hexpr boff fn exit reg bnd boff reg);;

let PKSCAN_STMT_BB fn head exit reg boff bnd =
  PKSCAN_STMT_G fn (fn^"_"^head) exit reg boff bnd;;

let PKSCAN_STMT_B fn head exit reg boff = PKSCAN_STMT_BB fn head exit reg boff 3;;

let PKSCAN_STMT fn head exit reg = PKSCAN_STMT_B fn head exit reg 448;;

let PKSCAN_TAC_BB exec fn head loop exit reg ninit boff bnd =
  let wb = mk_comb(`word:num->int32`,mk_small_numeral bnd)
  and wb1 = mk_comb(`word:num->int32`,mk_small_numeral (bnd - 1)) in
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num).
      APPEND (f_ev_epil rsp0 pc)
       (APPEND (ENUMERATEL 256 (\i. f_ev_loop rsp0 pc i)) (f_ev_prol rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `x:num->int32`; `rsp0:int64`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256`
   (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read RAX s = word i /\\
          read %s s = word_zx(if ?j. j < i /\\ ival(word_sub (word_sub (word %d) (word 1)) (mld_ct_abs(x j))) < &0 then word 4294967295 else word 0:int32) /\\
          (!j. j < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4 * j)))) s = (x:num->int32) j)" reg bnd boff)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    X86_STEPS_TAC exec (1--ninit) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[WORD_ZX_0; LT; EXISTS_SIMP] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `x:num->int32` (concl th))) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `val(word i:int64) = i` ASSUME_TAC THENL
     [ASM_SIMP_TAC[VAL_WORD_SMALL_IDX]; ALL_TAC] THEN
    SUBGOAL_THEN (subst [mk_small_numeral boff,`b:num`]
      `read (memory :> bytes32 (word_add rsp0 (word (4 * i + b)))) s0 = (x:num->int32) i`) ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE(subst [mk_small_numeral boff,`b:num`] `4 * i + b = b + 4 * i`)] THEN
      FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    X86_STEPS_TAC exec (1--16) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    TRY(REWRITE_TAC[WORD_RULE(mk_eq(mk_comb(mk_comb(`word_sub:int32->int32->int32`,wb),`word 1:int32`),wb1));
                    EXISTS_LT_SUC_SPLIT] THEN ASM_REWRITE_TAC[] THEN
        SPEC_TAC(subst [wb1,`w:int32`] `?j. j < i /\ ival(word_sub w (mld_ct_abs((x:num->int32) j))) < &0`,`p:bool`) THEN
        GEN_TAC THEN ASM_CASES_TAC `p:bool` THEN ASM_REWRITE_TAC[] THENL
         [REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_SX_32_64_32; WORD_ZX_USHR_SX_31; WORD_OR_ONES_32];
          REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_SX_32_64_32; WORD_ZX_USHR_SX_31] THEN
          REWRITE_TAC[WORD_OR_0; WORD_ISHR_31_COND; MLD_CT_ABS_SELECT]] THEN
        NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[mld_poly_chknorm] THEN
    REPEAT CONJ_TAC THEN
    TRY(REFL_TAC THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let PKSCAN_TAC_B exec fn head loop exit reg ninit boff =
  PKSCAN_TAC_BB exec fn head loop exit reg ninit boff 3;;

let PKSCAN_TAC exec fn head loop exit reg ninit =
  PKSCAN_TAC_B exec fn head loop exit reg ninit 448;;

(*** boff: the offset of the buffer from rsp0 (448 for ML-DSA-44, 480 for
     ML-DSA-87) ***)

(*** bnd: the bound of mld_poly_chknorm (eta + 1: 3, or 5 for ML-DSA-65) ***)

let PROVE_PKSCAN_BB fn head loop exit reg ninit boff bnd =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^head), layout (fn^"_"^exit))] in
  prove(PKSCAN_STMT_BB fn head exit reg boff bnd, PKSCAN_TAC_BB exec fn head loop exit reg ninit boff bnd);;

(*** The same with the start at hoff bytes after the label head (for a scan
     that the code starts after stores to slots) ***)

let PROVE_PKSCAN_OFF fn head hoff loop exit reg ninit boff bnd =
  let h = layout (fn^"_"^head) + hoff in
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(h, layout (fn^"_"^exit))] in
  prove(PKSCAN_STMT_G fn (string_of_int h) exit reg boff bnd,
        PKSCAN_TAC_BB exec fn head loop exit reg ninit boff bnd);;

let PROVE_PKSCAN_B fn head loop exit reg ninit boff =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^head), layout (fn^"_"^exit))] in
  prove(PKSCAN_STMT_B fn head exit reg boff, PKSCAN_TAC_B exec fn head loop exit reg ninit boff);;

let PROVE_PKSCAN fn head loop exit reg ninit =
  PROVE_PKSCAN_B fn head loop exit reg ninit 448;;

(* ------------------------------------------------------------------------- *)
(* The comparison of t0 with the t0 of the secret key in pk_from_sk, the     *)
(* vectorized mld_ct_memcmp: for n iterations of 64 bytes, the chunks A of   *)
(* 16 bytes at m + soff (m the secret key in R15) and B at rsp0 + boff are   *)
(* XORed; the XMM1 and XMM0 collect the ORs of the differences of the chunks *)
(* 4 k + 0 and 4 k + 2 resp. 4 k + 1 and 4 k + 3, and XMM2 and XMM3 their    *)
(* XORs. The region starts after the call of mld_compute_pack_t0_t1, at the  *)
(* clearing of the four registers, and ends at the exit of the loop. The     *)
(* chunks are given as functions A and B of the index, as 128-bit words.     *)
(* ------------------------------------------------------------------------- *)

let PKCMP_RES n = Printf.sprintf
 "(?v1 v0 v2 v3. read XMM1 s = v1 /\\ read XMM0 s = v0 /\\
                read XMM2 s = v2 /\\ read XMM3 s = v3 /\\
                word_or v1 v0 = mld_or_fold A B (%s) /\\
                word_xor v2 v3 = mld_xor_fold A B (%s))" n n;;

let PKCMP_STMT fn head exit soff boff nit = parse_term(Printf.sprintf
 "exists f_events. forall e m rsp0 (A:num->int128) (B:num->int128) pc.
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   aligned 16 (word_add rsp0 (word %d))
   ==> ensures x86
    (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
          read RIP s = word (pc + %s_%s) /\\ read RSP s = rsp0 /\\
          read R15 s = m /\\
          (!c. c < %d ==> read (memory :> bytes128 (word_add m (word (%d + 16 * c)))) s = A c) /\\
          (!c. c < %d ==> read (memory :> bytes128 (word_add rsp0 (word (%d + 16 * c)))) s = B c) /\\
          read events s = e)
    (\\s. read RIP s = word (pc + %s_%s) /\\ read RSP s = rsp0 /\\
          read R15 s = m /\\
          %s /\\
          (exists e2. read events s = APPEND e2 e /\\
             e2 = f_events m rsp0 pc /\\
             memaccess_inbounds e2
              [word_add m (word %d),%d; word_add rsp0 (word %d),%d] []))
    (MAYCHANGE [RIP; RAX] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])"
  boff fn head (4 * nit) soff (4 * nit) boff fn exit (PKCMP_RES (string_of_int (4 * nit))) soff (64 * nit) boff (64 * nit));;

(*** The chunk 4 i + q of A (at m + soff) or of B (at rsp0 + boff), as the
     simulation addresses it: base + (1 * 64 * i + soff + 16 q) ***)

let PKCMP_FACT who base off nit q =
  let c = Printf.sprintf "4 * i + %d" q in
  let k = off + 16 * q in
  let goal = parse_term(Printf.sprintf
    "read (memory :> bytes128 (word_add %s (word (1 * 64 * i + %d)))) s0 = (%s:num->int128) (%s)"
    base k who c) in
  let eq = parse_term(Printf.sprintf "1 * 64 * i + %d = %d + 16 * (%s)" k off c) in
  SUBGOAL_THEN goal ASSUME_TAC THENL
   [SUBGOAL_THEN eq (fun th -> REWRITE_TAC[th]) THENL [ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th ->
      let c0 = concl th in
      if is_forall c0 && free_in (parse_term (who ^ ":num->int128")) c0 &&
         free_in (parse_term (base ^ ":int64")) c0
      then (MP_TAC(SPEC (parse_term c) th) THEN
            ANTS_TAC THENL [UNDISCH_TAC (parse_term(Printf.sprintf "i < %d" nit)) THEN ARITH_TAC; ALL_TAC] THEN
            DISCH_THEN ACCEPT_TAC)
      else NO_TAC);
    ALL_TAC];;

let PKCMP_ALIGN off q =
  let k = off + 16 * q in
  SUBGOAL_THEN (parse_term(Printf.sprintf
    "aligned 16 (word_add rsp0 (word (1 * 64 * i + %d)):int64)" k)) ASSUME_TAC THENL
   [SUBGOAL_THEN (parse_term(Printf.sprintf
      "word_add rsp0 (word (1 * 64 * i + %d)):int64 = word_add (word_add rsp0 (word %d)) (word (64 * i + %d))" k off (16 * q)))
      SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    MATCH_MP_TAC ALIGNED_WORD_ADD THEN
    CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE];
    ALL_TAC];;

let PKCMP_INV soff boff nit = parse_term(Printf.sprintf
  "\\i s. read RSP s = rsp0 /\\ read R15 s = m /\\ read RAX s = word(64 * i) /\\
          %s /\\
          (!c. c < %d ==> read (memory :> bytes128 (word_add m (word (%d + 16 * c)))) s = (A:num->int128) c) /\\
          (!c. c < %d ==> read (memory :> bytes128 (word_add rsp0 (word (%d + 16 * c)))) s = (B:num->int128) c)"
  (PKCMP_RES "4 * i") (4 * nit) soff (4 * nit) boff);;

let PKCMP_YMM_GHOST lo hi =
  MAP_EVERY (fun n ->
   GHOST_INTRO_TAC (mk_var("ymm"^string_of_int n^"_init",`:int256`))
    (mk_comb(`read:(x86state,int256)component->x86state->int256`,
             mk_const("YMM"^string_of_int n,[])))) (lo--hi);;


(*** The relation of the ORs and XORs after an iteration with the folds: the
     folds unfolded four times (before the arguments are rewritten to
     4 * i + k), the folds after i iterations replaced by the ORs or XORs of
     the chosen v, and all 128-bit atoms generalized for BITBLAST_TAC (on
     these terms WORD_BLAST does not finish) ***)

let PKCMP_GEN_ATOMS_TAC : tactic = fun (asl,w) ->
  let isatom t = type_of t = `:int128` && (is_var t || (is_comb t && is_var (rator t))) in
  let ats = setify (find_terms isatom w) in
  MAP_EVERY (fun t -> SPEC_TAC(t, genvar(type_of t))) ats (asl,w);;

let PKCMP_FOLD_STEP_TAC =
  REWRITE_TAC[XMM0; XMM1; XMM2; XMM3; READ_ZEROTOP_128] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `4 * (i + 1) = SUC (SUC (SUC (SUC (4 * i))))`;
              mld_or_fold; mld_xor_fold] THEN
  REWRITE_TAC[ARITH_RULE `SUC (4 * i) = 4 * i + 1`;
              ARITH_RULE `SUC (SUC (4 * i)) = 4 * i + 2`;
              ARITH_RULE `SUC (SUC (SUC (4 * i))) = 4 * i + 3`;
              ARITH_RULE `4 * i + 0 = 4 * i`] THEN
  MAP_EVERY (fun pat ->
    TRY(FIRST_ASSUM(fun th ->
      if can (term_match [] pat) (concl th) then REWRITE_TAC[GSYM th] else NO_TAC)))
   [`word_or a b = mld_or_fold A B (4 * i)`;
    `word_xor a b = mld_xor_fold A B (4 * i)`] THEN
  PKCMP_GEN_ATOMS_TAC THEN REPEAT GEN_TAC THEN BITBLAST_TAC;;

let PKCMP_EX_TAC =
  MAP_EVERY EXISTS_TAC [`read XMM1 s21`; `read XMM0 s21`; `read XMM2 s21`; `read XMM3 s21`] THEN
  REPEAT CONJ_TAC THEN FIRST [REFL_TAC; PKCMP_FOLD_STEP_TAC];;

let PK_WRAP name (tac:tactic) : tactic = fun g ->
  try tac g with ex -> (Printf.printf "PK_WRAP failure in %s\n%!" name; raise ex);;

let PKCMP_STRIP_XMM =
  FIRST_X_ASSUM(fun th ->
    if is_exists(concl th) && can (find_term (fun t -> t = `XMM1`)) (concl th)
    then STRIP_ASSUME_TAC th else NO_TAC);;

let PKCMP_TAC exec fn head loop exit soff boff nit =
  let nt = mk_small_numeral nit in
  CONCRETIZE_F_EVENTS_TAC
   (subst [nt,`NIT:num`]
   `\(m:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil m rsp0 pc)
       (APPEND (ENUMERATEL NIT (\i. f_ev_loop m rsp0 pc i)) (f_ev_prol m rsp0 pc))
    :(uarch_event)list`) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `m:int64`; `rsp0:int64`; `A:num->int128`; `B:num->int128`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC nt
   (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit)) (PKCMP_INV soff boff nit) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    PKCMP_YMM_GHOST 0 3 THEN
    FULL_INIT_TAC THEN X86_STEPS_TAC exec (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[MULT_CLAUSES] THEN NO_TAC) THEN
    TRY(MAP_EVERY EXISTS_TAC [`word 0:int128`; `word 0:int128`; `word 0:int128`; `word 0:int128`] THEN
        REWRITE_TAC[mld_or_fold; mld_xor_fold; MULT_CLAUSES; WORD_OR_0; WORD_XOR_0] THEN
        REPEAT CONJ_TAC THEN
        REWRITE_TAC[XMM0; XMM1; XMM2; XMM3; READ_ZEROTOP_128] THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    PK_WRAP "ghost" (PKCMP_YMM_GHOST 4 7) THEN
    PK_WRAP "init" FULL_INIT_TAC THEN
    PK_WRAP "strip" PKCMP_STRIP_XMM THEN
    PK_WRAP "top" (XMM_EXISTSTOP_TAC "top0" `YMM0` THEN XMM_EXISTSTOP_TAC "top1" `YMM1` THEN
    XMM_EXISTSTOP_TAC "top2" `YMM2` THEN XMM_EXISTSTOP_TAC "top3" `YMM3`) THEN
    PK_WRAP "val" (VAL_INT64_TAC `64 * i`) THEN
    PK_WRAP "facts" (EVERY(map (fun q -> PKCMP_FACT "A" "m" soff nit q THEN PKCMP_FACT "B" "rsp0" boff nit q) [0;1;2;3])) THEN
    PK_WRAP "align" (EVERY(map (fun q -> PKCMP_ALIGN boff q) [0;1;2;3])) THEN
    PK_WRAP "steps" (SIMD_STEPS_TAC exec (1--21)) THEN
    PK_WRAP "final" (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) THEN
    PK_WRAP "loop" (LOOP_TEST_TAC THEN LOOP_COND_TAC THEN REPEAT CONJ_TAC) THEN
    PK_WRAP "goals" (TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    TRY(PKCMP_EX_TAC THEN NO_TAC)) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN PKCMP_STRIP_XMM THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(MAP_EVERY EXISTS_TAC [`v1:int128`; `v0:int128`; `v2:int128`; `v3:int128`] THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let PROVE_PKCMP fn head loop exit soff boff nit =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^head), layout (fn^"_"^exit))] in
  prove(PKCMP_STMT fn head exit soff boff nit, PKCMP_TAC exec fn head loop exit soff boff nit);;

(* ------------------------------------------------------------------------- *)
(* The L polynomials that calls of the unpacking or of the NTT leave, one at *)
(* a time, at a + 1024 n, are the vector: coefficient j of the vector is     *)
(* coefficient j MOD 256 of polynomial j DIV 256. Polynomial n of an         *)
(* unpacked vector is the unpacking of its P bytes, at the coefficients      *)
(* below 256.                                                                *)
(* ------------------------------------------------------------------------- *)

let PK_JOIN = prove
 (`!(a:int64) c (g:num->num->int32) L (s:x86state).
     (!n. n < L
          ==> !i. i < 256
                  ==> read (memory :> bytes32
                             (word_add a (word (c + 1024 * n + 4 * i)))) s =
                      g n i)
     ==> !j. j < 256 * L
             ==> read (memory :> bytes32 (word_add a (word (c + 4 * j)))) s =
                 g (j DIV 256) (j MOD 256)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `j DIV 256 < L` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `j MOD 256 < 256` ASSUME_TAC THENL
   [MP_TAC(SPECL [`j:num`; `256`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c + 1024 * (j DIV 256) + 4 * (j MOD 256) = c + 4 * j`
   ASSUME_TAC THENL
   [MP_TAC(SPECL [`j:num`; `256`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j DIV 256`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `j MOD 256`) THEN ASM_REWRITE_TAC[]);;

let PK_POLY_OF_UNPACK = prove
 (`!P (f:(num->byte)->num->int32) (b:num->byte) n i.
     i < 256
     ==> mld_poly_of (mld_polyvec_unpack P f b) n i = f (\t. b(P * n + t)) i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_poly_of; mld_polyvec_unpack; mld_polyvec] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  SUBGOAL_THEN `(256 * n + i) DIV 256 = n /\ (256 * n + i) MOD 256 = i`
    (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i:num` THEN ASM_ARITH_TAC;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `n:num` THEN ASM_ARITH_TAC]);;

(*** The norm check of polynomial n of an unpacked vector is that of the
     unpacking of the P bytes of the polynomial ***)

let PK_CHKNORM_UNPACK = prove
 (`!P (f:(num->byte)->num->int32) (b:num->byte) n B.
     mld_poly_chknorm (mld_poly_of (mld_polyvec_unpack P f b) n) B =
     mld_poly_chknorm (f (\t. b(P * n + t))) B`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_poly_chknorm] THEN
  SUBGOAL_THEN
   `(?i. i < 256 /\
         ival(word_sub (word_sub B (word 1))
                (mld_ct_abs (mld_poly_of (mld_polyvec_unpack P f b) n i))) < &0) <=>
    (?i. i < 256 /\
         ival(word_sub (word_sub B (word 1))
                (mld_ct_abs (f (\t. (b:num->byte)(P * n + t)) i))) < &0)`
   (fun th -> REWRITE_TAC[th]) THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `i:num` THEN
  ASM_MESON_TAC[PK_POLY_OF_UNPACK]);;

(* ------------------------------------------------------------------------- *)
(* The rest of the checks, from the exit of the comparison loop of t0 to the *)
(* test of the result, in three regions and a fourth that composes them.     *)
(*                                                                           *)
(* RED: the comparison loop leaves in XMM1 and XMM0 the ORs of the           *)
(* differences of t0 (x1 OR x0 is the OR fold) and in XMM2 and XMM3 their    *)
(* XORs. The code reduces both to a byte (pk_xbyte for the XOR), stores the  *)
(* XOR byte at rsp0 + 240, and the OR result, 0 or 0xFFFFFFFF, XORed with    *)
(* the XOR byte, at rsp0 + 232. The XOR byte is clang's value barrier: the   *)
(* code XORs it in a second time in the last block of the hash, so that it   *)
(* cancels (PK_SLOT_CANCEL).                                                 *)
(* ------------------------------------------------------------------------- *)

let pk_xbyte =
  let x = `x:int128` in
  let byte k = mk_comb(mk_comb(`word_subword:int128->num#num->byte`,x),
                       mk_pair(mk_small_numeral(8*k),`8`)) in
  let body = itlist (fun k acc -> mk_comb(mk_comb(`word_xor:byte->byte->byte`,acc),byte k))
               (rev (1--15)) (byte 0) in
  new_definition(mk_eq(mk_comb(`pk_xbyte:int128->byte`,x),body));;

(*** xoff: the slot of the XOR byte, zoff: that of the OR result, regs: the
     regions of the frame that the code writes (one for ML-DSA-44, where the
     slots are next to each other) ***)

let PKRED_STMT_G fn head exit xoff zoff regs =
  let rg (off,len) = Printf.sprintf "word_add rsp0 (word %d),%d" off len in
  let nonov = String.concat " /\\ "
    (map (fun r -> "nonoverlapping (word pc,libmldsa_size) (" ^ rg r ^ ")") regs) in
  let rl = String.concat "; " (map rg regs) in
  let mc = String.concat "; " (map (fun r -> "memory :> bytes(" ^ rg r ^ ")") regs) in
  parse_term(subst_tokens
 ["@MC@",image_mc; "@H@",string_of_int head; "@X@",string_of_int exit;
  "@NONOV@",nonov; "@RL@",rl; "@MCH@",mc;
  "@XO@",string_of_int xoff; "@ZO@",string_of_int zoff]
 "exists f_events. forall e rsp0 pc (x0:int128) (x1:int128) (x2:int128) (x3:int128).
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   @NONOV@
   ==> ensures x86
    (\\s. bytes_loaded s (word pc) @MC@ /\\
         read RIP s = word (pc + @H@) /\\ read RSP s = rsp0 /\\
         read XMM0 s = x0 /\\ read XMM1 s = x1 /\\ read XMM2 s = x2 /\\ read XMM3 s = x3 /\\
         read events s = e)
    (\\s. read RIP s = word (pc + @X@) /\\ read RSP s = rsp0 /\\
         read (memory :> bytes8 (word_add rsp0 (word @XO@))) s = pk_xbyte (word_xor x2 x3) /\\
         read (memory :> bytes64 (word_add rsp0 (word @ZO@))) s =
           word_xor (if word_or x0 x1 = word 0 then word 0 else word 4294967295)
                    (word_zx (pk_xbyte (word_xor x2 x3))) /\\
         (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
            memaccess_inbounds e2 [@RL@] [@RL@]))
    (MAYCHANGE [RIP; RAX; RCX] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [@MCH@])");;

let PKRED_STMT fn head exit = PKRED_STMT_G fn head exit 240 232 [232,12];;

(*** The slot at rsp0 + 232 as the simulation leaves it, from the OR- and the
     XOR-reduced vectors r0 and r1 (generalized, so that BITBLAST_RULE is
     quick), as in X86_CMP_RULE of utils/mldsa_native_top.ml ***)

let PKRED_CMP_TAC : tactic = fun (asl,w) ->
  let e = lhs w and rt = rhs w in
  let x0 = `x0:int128` and x1 = `x1:int128` and x2 = `x2:int128` in
  let isatom v t = type_of t = `:int128` && free_in v t in
  let r0 = find_term (isatom x0) e and r1 = find_term (isatom x2) e in
  let g0 = genvar `:int128` and g1 = genvar `:int128` in
  let e' = subst [g0,r0; g1,r1] e in
  let tgt = subst [g0,`g0:int128`; g1,`g1:int128`]
    `word_xor (if word_zx (g0:int128):byte = word 0 then word 0 else word 4294967295:int64)
              (word_zx (word_zx (g1:int128):byte))` in
  let tha = SPECL [r0; r1] (BITBLAST_RULE (list_mk_forall([g0;g1], mk_eq(e',tgt)))) in
  let isor t = t = `word_or x0 x1:int128` || t = `word_or x1 x0:int128` in
  let ot = find_term isor r0 and ot2 = find_term isor rt in
  let v' = genvar `:int128` in
  let thb0 = SPEC ot (BITBLAST_RULE (mk_forall(v',
     mk_eq(mk_eq(mk_comb(`word_zx:int128->byte`,subst[v',ot] r0),`word 0:byte`),
           mk_eq(v',`word 0:int128`))))) in
  let thb = if ot = ot2 then thb0 else
    TRANS thb0 (AP_THM (AP_TERM `(=):int128->int128->bool` (ISPECL [lhand ot; rand ot] WORD_OR_SYM)) `word 0:int128`) in
  let isx t = t = `word_xor x2 x3:int128` || t = `word_xor x3 x2:int128` in
  let xo = find_term isx rt in
  let thc = prove(mk_eq(mk_comb(`word_zx:int128->byte`,r1),mk_comb(`pk_xbyte`,xo)),
                  REWRITE_TAC[pk_xbyte] THEN BITBLAST_TAC) in
  (CONV_TAC(LAND_CONV(REWR_CONV tha)) THEN REWRITE_TAC[thb; thc]) (asl,w);;

let PKRED_TAC_G exec xoff =
  CONCRETIZE_F_EVENTS_TAC `\(rsp0:int64) (pc:num). f_ev_r rsp0 pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `x0:int128`; `x1:int128`; `x2:int128`; `x3:int128`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  XMM_EXISTSTOP_TAC "top0" `YMM0` THEN XMM_EXISTSTOP_TAC "top1" `YMM1` THEN
  XMM_EXISTSTOP_TAC "top2" `YMM2` THEN XMM_EXISTSTOP_TAC "top3" `YMM3` THEN
  SIMD_STEPS_TAC exec (1--30) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> if can (term_match [] (subst [mk_small_numeral xoff,`n:num`]
                                  `read (memory :> bytes32 (word_add rsp0 (word n))) s30 = x`)) (concl th)
      then REWRITE_TAC[MATCH_MP READ_BYTES32_LOW8 th] else NO_TAC) THEN
    REWRITE_TAC[pk_xbyte] THEN BITBLAST_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV(LAND_CONV(SIMD_SIMPLIFY_CONV [] THENC REWRITE_CONV[WORD_VAL_MOD_256]))) THEN
  CONJ_TAC THENL [PKRED_CMP_TAC; DISCHARGE_SAFETY_PROPERTY_TAC];;

let PKRED_TAC exec = PKRED_TAC_G exec 240;;

let PROVE_PKRED_G fn head exit xoff zoff regs =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc [(head, exit)] in
  prove(PKRED_STMT_G fn head exit xoff zoff regs, PKRED_TAC_G exec xoff);;

let PROVE_PKRED fn head exit = PROVE_PKRED_G fn head exit 240 232 [232,12];;

(* ------------------------------------------------------------------------- *)
(* HASH: the inlined SHAKE256 of pk (1312 bytes for ML-DSA-44), from the     *)
(* zeroing of the state at rsp0 + 16 to the return of the last permutation.  *)
(* It is the TR44 region of inline_verify.ml with the state at fb + 312      *)
(* instead of fb + 424 (fb = rsp0 - 296), the key loaded into R15 from the   *)
(* slot at rsp0 + 248 at the start of the first block, and three more        *)
(* instructions in the last block, which XOR the byte at rsp0 + 240 into the *)
(* low byte of the slot at rsp0 + 232. The proof reuses the lemmas and tools *)
(* of TR44 (TR_BLK_MERGE, TR_FIN_MERGE, TR_ZERO_MERGE, TR44_STATE_EQ).       *)
(* ------------------------------------------------------------------------- *)

let PKH_STMT fn head = parse_term(subst_tokens
 ["@FN@",fn; "@MC@",image_mc; "@START@",string_of_int head]
 "exists f_events.
   forall e rsp0 pk pc PK X Y.
     aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
     aligned 32 (rsp0:int64) /\\
     ALL (nonoverlapping (word_sub rsp0 (word 296),552))
         [(word pc,libmldsa_size); (pk,1312)]
     ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
               read RIP s = word (pc + @START@) /\\
               read RSP s = rsp0 /\\
               read (memory :> bytes64 (word_add rsp0 (word 248))) s = pk /\\
               read (memory :> bytes(pk,1312)) s = PK /\\
               read (memory :> bytes64 (word_add rsp0 (word 232))) s = X /\\
               read (memory :> bytes8 (word_add rsp0 (word 240))) s = Y /\\
               read events s = e)
          (\\s. read RIP s = word (pc + @FN@_after_mldsa_keccakf1600_permute_10) /\\
               read RSP s = rsp0 /\\ read R15 s = pk /\\
               read (memory :> wbytes (word_add rsp0 (word 16))) s =
               keccak_f1600 (mld_shake256_state 1312 PK) /\\
               read (memory :> bytes64 (word_add rsp0 (word 232))) s =
               word_xor X (word_zx Y) /\\
               (exists e2. read events s = APPEND e2 e /\\
                  e2 = f_events (word_sub rsp0 (word 296)) pk pc /\\
                  memaccess_inbounds e2
                   [pk,1312; word_sub rsp0 (word 296),552;
                    word(pc + rodata_mld_KeccakF_RoundConstants),192]
                   [word_sub rsp0 (word 296),536]))
          (MAYCHANGE [RSP; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub rsp0 (word 296),536)])");;

(*** One full block k, as TR_BLOCK_TAC with the state at fb + soff ***)

let PKH_BLOCK_TAC soff execth k n0 =
  let a = tr_fb_add soff in
  let nsteps = if k = 0 then 25 else 28 in
  let ncall = n0 + nsteps + 1 in
  let sn = mk_var("s"^string_of_int(n0 + nsteps),`:x86state`) in
  let sv = if k = 0 then tr_st 0 else mk_var("st"^string_of_int k,`:1600 word`)
  and wv = mk_var("wb"^string_of_int k,`:1600 word`) in
  TR_STATE_CHUNKS_TAC a (0--7) (16--24) THEN
  TR_PK_TAC k (0--7) [16] THEN
  (if k = 0 then ALL_TAC else TR_NAME_TAC (tr_st k) ("st"^string_of_int k)) THEN
  TR_NAME_TAC (tr_wb k) ("wb"^string_of_int k) THEN
  X86_STEPS_TAC execth ((n0+1)--(n0+nsteps)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO; VERIF_SUBWORD_JOIN_HI]) THEN
  MP_TAC(SPECL [a; sv; wv; sn] TR_BLK_MERGE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL
     [ALL_TAC; TR_UNNAME_GOAL_TAC ("wb"^string_of_int k)]]] THEN
    TR_ANTE_TAC;
    DISCH_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_PERM"
   [`read RDI s`; mk_comb(mk_comb(`word_xor:1600 word->1600 word->1600 word`,sv),wv);
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`fb:int64`; `pk:int64`; `pc:num`] ncall THEN
  (if k = 0 then ALL_TAC else TR_UNNAME_TAC ("st"^string_of_int k)) THEN
  TR_UNNAME_TAC ("wb"^string_of_int k) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TR_BLOCKS_STEP k]) THEN
  YMM_GHOST_TAC (mk_var("s"^string_of_int ncall,`:x86state`))
   ["YMM0","y0_"^string_of_int k; "YMM1","y1_"^string_of_int k];;

(*** The last block of 88 bytes, the padding and the last permutation, as
     TR44_FINAL_TAC, with 30 steps (3 more for the slot) ***)

let PKH_FINAL_TAC soff execth n0 =
  let a = tr_fb_add soff in
  let sv = mk_var("st9",`:1600 word`) and wv = mk_var("wb9",`:1600 word`) in
  let sn = mk_var("s"^string_of_int(n0 + 30),`:x86state`) in
  let fin = list_mk_icomb "word_xor"
             [list_mk_icomb "word_xor"
               [list_mk_icomb "word_xor" [sv; wv]; `word(2 EXP 704 * 31):1600 word`];
              `word(2 EXP 1080 * 128):1600 word`] in
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(pk,1312)) (s:x86state) = PK`) (concl th)
    then let st = rand(lhs(concl th)) in
         let b = ISPECL [`pk:int64`; `1312`;
                         mk_comb(`read memory:x86state->int64->byte`,st)] READ_BYTES_BOUND in
         ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
                     (REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE; th] b))
    else NO_TAC) THEN
  TR_STATE_CHUNKS_TAC a [] ((0--10) @ (12--15) @ (17--24)) THEN
  TR_STATE_BYTES_TAC a ((88--95) @ (128--135)) THEN
  TR_PK_TAC 9 [] (0--10) THEN
  TR_NAME_TAC (tr_st 9) "st9" THEN TR_NAME_TAC (tr_wb 9) "wb9" THEN
  X86_STEPS_TAC execth ((n0+1)--(n0+30)) THEN
  MP_TAC(SPECL [a; sv; wv; sn] TR_FIN_MERGE) THEN
  ANTS_TAC THENL
   [REPEAT(CONJ_TAC THENL [TR_ANTE_TAC; ALL_TAC]) THEN
    TR_UNNAME_GOAL_TAC "wb9" THEN
    CONV_TAC(DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC TR_NORM_CONV THEN
    REPEAT CONJ_TAC THEN
    MATCH_MP_TAC(TR_NORM_RULE(SPECL [`PK:num`; `9`] TR_HI_ZERO)) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_PERM"
   [`read RDI s`; fin; `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`fb:int64`; `pk:int64`; `pc:num`] (n0 + 31) THEN
  TR_UNNAME_TAC "st9" THEN TR_UNNAME_TAC "wb9" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM TR44_STATE_EQ]);;

let PKH_ALIGN_OFFS = [0x10;0x20;0x30;0x40;0x50;0x60;0x70;0x80;0x90;0xa0;0xb0;0xc0];;

let PKH_EXEC fn head = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(head, layout (fn^"_after_mldsa_keccakf1600_permute_10"))];;

let PKH_SETUP_TAC execth =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fb:int64) (pk:int64) (pc:num). f_ev_all fb pk pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  X_GEN_TAC `e:(uarch_event)list` THEN WORD_FORALL_OFFSET_TAC 296 THEN
  MAP_EVERY X_GEN_TAC [`fb:int64`; `pk:int64`; `pc:num`; `PK:num`; `X:int64`; `Y:byte`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  TR_ALIGNED_TAC 296 PKH_ALIGN_OFFS THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC execth (1--2) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes128 (word_add fb (word 500))) s2 = x`)
           (concl th)
    then STRIP_ASSUME_TAC(CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th) else NO_TAC) THEN
  ADDR_NORMALIZE_TAC THEN
  X86_STEPS_TAC execth (3--14) THEN
  MP_TAC(SPECL [tr_fb_add 312; `s14:x86state`] TR_ZERO_MERGE) THEN
  ANTS_TAC THENL [TR_ANTE_TAC; DISCH_TAC];;

let PKH_TAC execth =
  PKH_SETUP_TAC execth THEN
  PKH_BLOCK_TAC 312 execth 0 14 THEN
  MAP_EVERY (fun k -> PKH_BLOCK_TAC 312 execth k (40 + 29 * (k - 1))) (1--8) THEN
  PKH_FINAL_TAC 312 execth 272 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[WORD_VAL_MOD_256] THEN CONV_TAC WORD_BLAST;
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let PROVE_PKHASH fn head =
  prove(PKH_STMT fn head, PKH_TAC (PKH_EXEC fn head));;

(* ------------------------------------------------------------------------- *)
(* HASHB: the inlined SHAKE256 of pk as in ML-DSA-65 and ML-DSA-87, for any  *)
(* length plen of the key: the state at rsp0 + soff, nb = plen DIV 136 full  *)
(* blocks and a last block of r = plen MOD 136 bytes (a multiple of 8), and  *)
(* no slot XORed into the last block (the code of these parameter sets XORs  *)
(* the check byte in TRCB). The tools are those of HASH, with the length as  *)
(* a parameter: TRB_PK_TAC, TRB_HI_ZERO, TRB_FIN_MERGE r and TRB_STATE_EQ.   *)
(* ------------------------------------------------------------------------- *)

let pk_rsp0_add k =
  if k = 0 then "rsp0" else Printf.sprintf "word_add rsp0 (word %d)" k;;

let PKHB_STMT fn head exitl soff pslot plen rlen wlen = parse_term(subst_tokens
 ["@FN@",fn; "@MC@",image_mc; "@START@",string_of_int head; "@EXIT@",exitl;
  "@SA@",pk_rsp0_add soff; "@PS@",string_of_int pslot; "@PLEN@",string_of_int plen;
  "@RLEN@",string_of_int rlen; "@WLEN@",string_of_int wlen]
 "exists f_events.
   forall e rsp0 pk pc PK.
     aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
     aligned 32 (rsp0:int64) /\\
     ALL (nonoverlapping (word_sub rsp0 (word 296),@RLEN@))
         [(word pc,libmldsa_size); (pk,@PLEN@)]
     ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
               read RIP s = word (pc + @START@) /\\
               read RSP s = rsp0 /\\
               read (memory :> bytes64 (word_add rsp0 (word @PS@))) s = pk /\\
               read (memory :> bytes(pk,@PLEN@)) s = PK /\\
               read events s = e)
          (\\s. read RIP s = word (pc + @FN@_@EXIT@) /\\
               read RSP s = rsp0 /\\ read R15 s = pk /\\
               read (memory :> wbytes (@SA@)) s =
               keccak_f1600 (mld_shake256_state @PLEN@ PK) /\\
               (exists e2. read events s = APPEND e2 e /\\
                  e2 = f_events (word_sub rsp0 (word 296)) pk pc /\\
                  memaccess_inbounds e2
                   [pk,@PLEN@; word_sub rsp0 (word 296),@RLEN@;
                    word(pc + rodata_mld_KeccakF_RoundConstants),192]
                   [word_sub rsp0 (word 296),@WLEN@]))
          (MAYCHANGE [RSP; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub rsp0 (word 296),@WLEN@)])");;

(*** The loads of block k of the key of plen bytes, as TR_PK_TAC ***)

let TRB_PK_TAC plen (k:int) (chunks:int list) (lanes:int list) =
  let wb = tr_wb k in
  let pt = subst [mk_small_numeral plen,`n:num`] `read (memory :> bytes(pk,n)) (s:x86state)` in
  let one bits off pos =
    FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && can (term_match [] pt) (lhs c)
      then
        let s = rand(lhs c) in
        let lem = if bits = 128 then TR_CHUNK128_OF_NUM else TR_CHUNK64_OF_NUM in
        let th1 = TR_NORM_RULE(tr_mp_conj
                    (SPECL [`pk:int64`; mk_small_numeral plen; `PK:num`; mk_small_numeral off; s] lem) th) in
        let ty = if bits = 128 then `:128` else `:64` in
        let th2 = TR_NORM_RULE(tr_mp_num (INST_TYPE [ty,`:N`]
                    (SPECL [`PK:num`; mk_small_numeral k; mk_small_numeral pos; mk_small_numeral bits]
                     TR_BLK_SUB))) in
        ASSUME_TAC(TRANS th1 (SYM th2))
      else NO_TAC) in
  ignore wb;
  MAP_EVERY (fun j -> one 128 (136 * k + 16 * j) (128 * j)) chunks THEN
  MAP_EVERY (fun n -> one 64 (136 * k + 8 * n) (64 * n)) lanes;;

(*** The bits of the last block above the key are zero ***)

let TRB_HI_ZERO = prove
 (`!PK B k p n. PK < 2 EXP B /\ B <= 1088 * k + p
        ==> (word_subword (word((PK DIV 2 EXP (1088 * k)) MOD 2 EXP 1088):1600 word)
                          (p,n):N word) = word 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_subword; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(MESON[MOD_0] `!x n. x = 0 ==> x MOD n = 0`) THEN
  SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  TRANS_TAC LET_TRANS `PK DIV 2 EXP (1088 * k)` THEN CONJ_TAC THENL
   [MESON_TAC[MOD_LE; LE_TRANS];
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    TRANS_TAC LTE_TRANS `2 EXP B` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ASM_ARITH_TAC]);;

(*** The state after the last r bytes W (r = 8 L, as L lanes) and the padding
     bytes, as TR_FIN_MERGE (which is the case r = 88) ***)

let TRB_FIN_MERGE_C r c =
  let l = r / 8 in
  let nl = l - 2 * c in
  let sub = subst_tokens
    ["@C@",string_of_int c; "@NLA@",string_of_int nl; "@C16@",string_of_int (16 * c);
     "@C128@",string_of_int (128 * c);
     "@R@",string_of_int r; "@R8@",string_of_int (8 * r);
     "@R1@",string_of_int (r + 1); "@R18@",string_of_int (8 * (r + 1));
     "@R8B@",string_of_int (r + 8); "@R88@",string_of_int (8 * (r + 8));
     "@NL@",string_of_int (15 - l); "@NW@",string_of_int (25 - l)] in
  let chunks = if c = 0 then "" else
    "(!j. j < @C@ ==> read (memory :> bytes128 (word_add a (word (16 * j)))) s =
                  word_xor (word_subword W (128 * j,128)) (word_subword S (128 * j,128))) /\\ " in
  let lanes = if nl = 0 then "" else if c = 0 then
    "(!n. n < @NLA@ ==> read (memory :> bytes64 (word_add a (word (8 * n)))) s =
                  word_xor (word_subword S (64 * n,64)) (word_subword W (64 * n,64))) /\\ "
    else
    "(!n. n < @NLA@ ==> read (memory :> bytes64 (word_add a (word (@C16@ + 8 * n)))) s =
                  word_xor (word_subword S (@C128@ + 64 * n,64)) (word_subword W (@C128@ + 64 * n,64))) /\\ " in
  prove(parse_term(sub(
 "!(a:int64) (S:1600 word) (W:1600 word) (s:x86state). " ^ chunks ^ lanes ^
 "read (memory :> bytes8 (word_add a (word @R@))) s =
  word_xor (word_subword S (@R8@,8)) (word 31) /\\
  (!m. m < 7 ==> read (memory :> bytes8 (word_add a (word (@R1@ + m)))) s =
                 word_subword S (@R18@ + 8 * m,8)) /\\
  (!n. n < @NL@ ==> read (memory :> bytes64 (word_add a (word (@R8B@ + 8 * n)))) s =
                 word_subword S (@R88@ + 64 * n,64)) /\\
  (!m. m < 7 ==> read (memory :> bytes8 (word_add a (word (128 + m)))) s =
                 word_subword S (1024 + 8 * m,8)) /\\
  read (memory :> bytes8 (word_add a (word 135))) s =
  word_xor (word_subword S (1080,8)) (word 128) /\\
  (!n. n < 8 ==> read (memory :> bytes64 (word_add a (word (136 + 8 * n)))) s =
                 word_subword S (1088 + 64 * n,64)) /\\
  (!n. n < @NW@ ==> word_subword W (@R8@ + 64 * n,64) = (word 0:int64))
  ==> read (memory :> wbytes a) s =
      word_xor (word_xor (word_xor S W) (word(2 EXP @R8@ * 31)))
               (word(2 EXP 1080 * 128))")),
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV EXPAND_CASES_CONV)) THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV) THENC
                     REWRITE_CONV[WORD_ADD_0])) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC READ_MEMORY_WBYTES_OF_LANES THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  MAP_EVERY (fun j ->
    FIRST_ASSUM(fun th ->
      let cc = concl th in
      if is_eq cc && can (term_match [] `read (memory :> bytes128 x) (s:x86state)`) (lhs cc) &&
         (let ad = rand(rand(rand(rator(lhs cc)))) in
          ad = (if j = 0 then `a:int64` else
                subst [mk_small_numeral(16 * j),`n:num`] `word_add (a:int64) (word n)`))
      then let th' = MATCH_MP READ_MEMORY_BYTES64_OF_BYTES128 th in
           STRIP_ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th')
      else NO_TAC)) (if c = 0 then [] else 0--(c-1)) THEN
  MAP_EVERY (fun k ->
    let t = subst [mk_small_numeral k,`k:num`]
              `read (memory :> bytes64 (word_add (a:int64) (word k))) (s:x86state)` in
    GEN_REWRITE_TAC (ONCE_DEPTH_CONV o LAND_CONV)
     [CONV_RULE(RAND_CONV(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))
                 (READ_MEMORY_MERGE_CONV 3 t)]) [r; 128] THEN
  ASM_REWRITE_TAC[WORD_SUBWORD_XOR; WORD_XOR_0] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let TRB_FIN_MERGE r = TRB_FIN_MERGE_C r 0;;

(*** The padded state of a key of plen bytes as the code computes it, as
     TR44_STATE_EQ; trb_fin builds its right-hand side from the state and
     the last block ***)

let trb_fin plen sv wv =
  let r = plen mod 136 in
  list_mk_icomb "word_xor"
   [list_mk_icomb "word_xor"
     [list_mk_icomb "word_xor" [sv; wv];
      mk_comb(`word:num->1600 word`,
              mk_binop `( * ):num->num->num`
               (mk_binop `EXP` `2` (mk_small_numeral (8 * r))) `31`)];
    `word(2 EXP 1080 * 128):1600 word`];;

let TRB_STATE_EQ plen =
  let nb = plen / 136 in
  let lhs = mk_comb(mk_comb(`mld_shake256_state`,mk_small_numeral plen),`PK:num`) in
  let rhs = trb_fin plen (tr_st nb) (tr_wb nb) in
  prove(mk_forall(`PK:num`,mk_eq(lhs,rhs)),
  GEN_TAC THEN
  REWRITE_TAC[mld_shake256_state; mld_keccak_absorb; mld_keccak_finalize] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV ORELSEC NUM_DIV_CONV ORELSEC
                      NUM_MOD_CONV ORELSEC NUM_SUB_CONV)) THEN
  REWRITE_TAC[CONJUNCT1 EXP; MULT_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(*** One full block, as PKH_BLOCK_TAC for a key of plen bytes ***)

let PKHB_BLOCK_TAC plen soff execth k n0 =
  let a = tr_fb_add (296 + soff) in
  let nsteps = if k = 0 then 25 else 28 in
  let ncall = n0 + nsteps + 1 in
  let sn = mk_var("s"^string_of_int(n0 + nsteps),`:x86state`) in
  let sv = if k = 0 then tr_st 0 else mk_var("st"^string_of_int k,`:1600 word`)
  and wv = mk_var("wb"^string_of_int k,`:1600 word`) in
  TR_STATE_CHUNKS_TAC a (0--7) (16--24) THEN
  TRB_PK_TAC plen k (0--7) [16] THEN
  (if k = 0 then ALL_TAC else TR_NAME_TAC (tr_st k) ("st"^string_of_int k)) THEN
  TR_NAME_TAC (tr_wb k) ("wb"^string_of_int k) THEN
  X86_STEPS_TAC execth ((n0+1)--(n0+nsteps)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO; VERIF_SUBWORD_JOIN_HI]) THEN
  MP_TAC(SPECL [a; sv; wv; sn] TR_BLK_MERGE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL
     [ALL_TAC; TR_UNNAME_GOAL_TAC ("wb"^string_of_int k)]]] THEN
    TR_ANTE_TAC;
    DISCH_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_PERM"
   [`read RDI s`; mk_comb(mk_comb(`word_xor:1600 word->1600 word->1600 word`,sv),wv);
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`fb:int64`; `pk:int64`; `pc:num`] ncall THEN
  (if k = 0 then ALL_TAC else TR_UNNAME_TAC ("st"^string_of_int k)) THEN
  TR_UNNAME_TAC ("wb"^string_of_int k) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TR_BLOCKS_STEP k]) THEN
  YMM_GHOST_TAC (mk_var("s"^string_of_int ncall,`:x86state`))
   ["YMM0","y0_"^string_of_int k; "YMM1","y1_"^string_of_int k];;

(*** The last block of r bytes as L lanes (mov and xor each), the padding
     and the last permutation, from the state after the call at step n0 ***)

let PKHB_FINAL_TAC_C plen soff c execth n0 =
  let nb = plen / 136 and r = plen mod 136 in
  let l = r / 8 in
  let nst = 3 * c + 2 * (l - 2 * c) + 5 in
  let cl = if c = 0 then [] else 0--(c-1) in
  let ll = if l - 2 * c = 0 then [] else (2*c)--(l-1) in
  let a = tr_fb_add (296 + soff) in
  let sv = mk_var("st"^string_of_int nb,`:1600 word`)
  and wv = mk_var("wb"^string_of_int nb,`:1600 word`) in
  let sn = mk_var("s"^string_of_int(n0 + nst),`:x86state`) in
  let fin = trb_fin plen sv wv in
  let pt = subst [mk_small_numeral plen,`n:num`] `read (memory :> bytes(pk,n)) (s:x86state) = PK` in
  let hz = TR_NORM_RULE(SPECL [`PK:num`; mk_small_numeral (8 * plen); mk_small_numeral nb] TRB_HI_ZERO) in
  FIRST_ASSUM(fun th ->
    if can (term_match [] pt) (concl th)
    then let st = rand(lhs(concl th)) in
         let b = ISPECL [`pk:int64`; mk_small_numeral plen;
                         mk_comb(`read memory:x86state->int64->byte`,st)] READ_BYTES_BOUND in
         ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
                     (REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE; th] b))
    else NO_TAC) THEN
  TR_STATE_CHUNKS_TAC a cl (ll @ ((l+1)--15) @ (17--24)) THEN
  TR_STATE_BYTES_TAC a ((r--(r+7)) @ (128--135)) THEN
  TRB_PK_TAC plen nb cl ll THEN
  TR_NAME_TAC (tr_st nb) ("st"^string_of_int nb) THEN
  TR_NAME_TAC (tr_wb nb) ("wb"^string_of_int nb) THEN
  X86_STEPS_TAC execth ((n0+1)--(n0+nst)) THEN
  MP_TAC(SPECL [a; sv; wv; sn] (TRB_FIN_MERGE_C r c)) THEN
  ANTS_TAC THENL
   [REPEAT(CONJ_TAC THENL [TR_ANTE_TAC; ALL_TAC]) THEN
    TR_UNNAME_GOAL_TAC ("wb"^string_of_int nb) THEN
    CONV_TAC(DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC TR_NORM_CONV THEN
    REPEAT CONJ_TAC THEN
    MATCH_MP_TAC hz THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_PERM"
   [`read RDI s`; fin; `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`fb:int64`; `pk:int64`; `pc:num`] (n0 + nst + 1) THEN
  TR_UNNAME_TAC ("st"^string_of_int nb) THEN TR_UNNAME_TAC ("wb"^string_of_int nb) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM (TRB_STATE_EQ plen)]);;

let PKHB_FINAL_LANES_TAC plen soff execth n0 = PKHB_FINAL_TAC_C plen soff 0 execth n0;;

(*** From the zeroing of the state (pxor and 13 stores, the first a MOVDQU
     at rsp0 + soff + 188) to the state before the first block ***)

let PKHB_SETUP_TAC soff execth =
  let base = 296 + soff in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fb:int64) (pk:int64) (pc:num). f_ev_all fb pk pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  X_GEN_TAC `e:(uarch_event)list` THEN WORD_FORALL_OFFSET_TAC 296 THEN
  MAP_EVERY X_GEN_TAC [`fb:int64`; `pk:int64`; `pc:num`; `PK:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  TR_ALIGNED_TAC 296 (map (fun j -> soff + 16 * j) (if soff = 0 then 1--11 else 0--11)) THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC execth (1--2) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] (subst [mk_small_numeral (base + 188),`n:num`]
              `read (memory :> bytes128 (word_add fb (word n))) s2 = x`))
           (concl th)
    then STRIP_ASSUME_TAC(CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th) else NO_TAC) THEN
  ADDR_NORMALIZE_TAC THEN
  X86_STEPS_TAC execth (3--14) THEN
  MP_TAC(SPECL [tr_fb_add base; `s14:x86state`] TR_ZERO_MERGE) THEN
  ANTS_TAC THENL [TR_ANTE_TAC; DISCH_TAC];;

let PKHB_EXEC fn head exitl = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(head, layout (fn^"_"^exitl))];;

let PKHB_TAC_C plen soff c execth =
  let nb = plen / 136 in
  PKHB_SETUP_TAC soff execth THEN
  PKHB_BLOCK_TAC plen soff execth 0 14 THEN
  MAP_EVERY (fun k -> PKHB_BLOCK_TAC plen soff execth k (40 + 29 * (k - 1))) (1--(nb-1)) THEN
  PKHB_FINAL_TAC_C plen soff c execth (40 + 29 * (nb - 1)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PKHB_TAC plen soff execth = PKHB_TAC_C plen soff 0 execth;;

(*** c: the number of 16-byte chunks (SSE) of the last block before its
     lanes (0 for ML-DSA-87, whose last block is one lane; 3 for ML-DSA-65,
     whose last block of 48 bytes is three chunks) ***)

let PROVE_PKHASHB_C fn head exitl soff pslot plen rlen wlen c =
  prove(PKHB_STMT fn head exitl soff pslot plen rlen wlen,
        PKHB_TAC_C plen soff c (PKHB_EXEC fn head exitl));;

let PROVE_PKHASHB fn head exitl soff pslot plen rlen wlen =
  PROVE_PKHASHB_C fn head exitl soff pslot plen rlen wlen 0;;

(* ------------------------------------------------------------------------- *)
(* TRC: after the last permutation, the 64 bytes of the hash copied to       *)
(* rsp0 + 288, the state zeroed, the comparison of the hash with tr at       *)
(* rsp0 + 352 (an OR- and an XOR-reduction, the latter again cancelling), and *)
(* the OR of all checks into the low byte of R13: the norm checks in R14,    *)
(* R12, R13, RBX and at rsp0 + 244, and that of t0 in the low byte of the    *)
(* slot at rsp0 + 232. The region ends at the test of R13. The four 128-bit  *)
(* differences of the hash and tr are named d0 .. d3 before the reductions,  *)
(* which keeps the terms small.                                              *)
(* ------------------------------------------------------------------------- *)

let PKTRC_STMT fn head exit = parse_term(subst_tokens
 ["@MC@",image_mc; "@H@",string_of_int head; "@X@",string_of_int exit]
 "exists f_events. forall e rsp0 pc (K:1600 word) TB (c14:int32) (c12:int32) (c13:int32) (cbx:int32) (cf4:int32) (Z:int64).
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   aligned 32 (rsp0:int64) /\\
   nonoverlapping (word pc,libmldsa_size) (word_add rsp0 (word 16),400)
   ==> ensures x86
    (\\s. bytes_loaded s (word pc) @MC@ /\\
         read RIP s = word (pc + @H@) /\\ read RSP s = rsp0 /\\
         read (memory :> wbytes (word_add rsp0 (word 16))) s = K /\\
         read (memory :> bytes(word_add rsp0 (word 352),64)) s = TB /\\
         read R14 s = word_zx c14 /\\ read R12 s = word_zx c12 /\\
         read R13 s = word_zx c13 /\\ read RBX s = word_zx cbx /\\
         read (memory :> bytes32 (word_add rsp0 (word 244))) s = cf4 /\\
         read (memory :> bytes64 (word_add rsp0 (word 232))) s = Z /\\
         read events s = e)
    (\\s. read RIP s = word (pc + @X@) /\\ read RSP s = rsp0 /\\
         (word_zx (read R13 s):byte = word 0 <=>
          word_zx (word_or cf4 (word_or c14 (word_or c12 (word_or c13 cbx)))):byte = word 0 /\\
          word_zx Z:byte = word 0 /\\
          val K MOD 2 EXP 512 = TB) /\\
         (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
            memaccess_inbounds e2 [word_add rsp0 (word 16),400] [word_add rsp0 (word 16),336]))
    (MAYCHANGE [RIP; RAX; RCX; R13; R14] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(word_add rsp0 (word 16),336)])");;

(* the 512 bits of a word as four 128-bit chunks *)
let PK_W512_CHUNKS = prove
 (`!x w:512 word. x = w <=>
     word_subword x (0,128):int128 = word_subword w (0,128) /\
     word_subword x (128,128):int128 = word_subword w (128,128) /\
     word_subword x (256,128):int128 = word_subword w (256,128) /\
     word_subword x (384,128):int128 = word_subword w (384,128)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; DIMINDEX_128; DIMINDEX_512] THEN
  REWRITE_TAC[ARITH_RULE `MIN 128 128 = 128`] THEN
  DISCH_THEN(fun th -> X_GEN_TAC `i:num` THEN DISCH_TAC THEN MP_TAC th) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `i:num`) (CONJUNCTS_THEN2 (MP_TAC o SPEC `i - 128`)
    (CONJUNCTS_THEN2 (MP_TAC o SPEC `i - 256`) (MP_TAC o SPEC `i - 384`)))) THEN
  ASM_CASES_TAC `i < 128` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  MAP_EVERY (fun (b,lo) ->
    ASM_CASES_TAC (subst [mk_small_numeral b,`b:num`] `i < b`) THENL
     [SUBGOAL_THEN (subst [mk_small_numeral lo,`l:num`] `i - l < 128 /\ l + (i - l) = i`)
        STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
      CONV_TAC TAUT;
      ALL_TAC]) [256,128; 384,256; 512,384] THEN
  ASM_ARITH_TAC);;

let PK_VAL512_CHUNKS = prove
 (`!(K:1600 word) TB. TB < 2 EXP 512
     ==> (val K MOD 2 EXP 512 = TB <=>
          !k. k < 4 ==> word_subword K (128 * k,128):int128 =
                        word((TB DIV 2 EXP (128 * k)) MOD 2 EXP 128))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val (K:1600 word) MOD 2 EXP 512 = TB <=> (word_zx K:512 word) = word TB` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_512] THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  REWRITE_TAC[PK_W512_CHUNKS] THEN
  CONV_TAC(RAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[word_subword; VAL_WORD; VAL_WORD_ZX_GEN; DIMINDEX_512; DIMINDEX_128] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let PK_READ_BYTES64_LOW8 = prove
 (`!a:int64 x s:x86state.
     read (memory :> bytes64 a) s = x
     ==> read (memory :> bytes8 a) s = word_zx x`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; READ_COMPONENT_COMPOSE;
              BYTES64_WBYTES; BYTES8_WBYTES; VAL_READ_WBYTES;
              DIMINDEX_64; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP (8 * 1)`; READ_BYTES_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let PKTRC_ALIGN_TAC offs =
  FIRST_ASSUM(fun a32 -> if concl a32 = `aligned 32 (rsp0:int64)` then
    let a16 = MATCH_MP (MP (ISPECL [`16`;`32`;`rsp0:int64`] ALIGNED_WORD_WEAKEN)
                          (EQT_ELIM(DIVIDES_CONV `16 divides 32`))) a32 in
    ASSUME_TAC a16 THEN
    MAP_EVERY (fun k -> ASSUME_TAC (MATCH_MP ALIGNED_WORD_ADD (CONJ a16 (SPONGE_A16 k)))) offs
   else NO_TAC);;

let PKTRC_PRE_TAC exec =
  CONCRETIZE_F_EVENTS_TAC `\(rsp0:int64) (pc:num). f_ev_t rsp0 pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `K:1600 word`; `TB:num`;
    `c14:int32`; `c12:int32`; `c13:int32`; `cbx:int32`; `cf4:int32`; `Z:int64`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  PKTRC_ALIGN_TAC [16;32;48;64;80;96;112;128;144;160;176;192;208;288;304;320;336;352;368;384;400] THEN
  MAP_EVERY (fun n ->
   GHOST_INTRO_TAC (mk_var("ymm"^string_of_int n^"_init",`:int256`))
    (mk_comb(`read:(x86state,int256)component->x86state->int256`,
             mk_const("YMM"^string_of_int n,[])))) (0--4) THEN
  FULL_INIT_TAC THEN
  FIRST_ASSUM(fun th -> if concl th = `read (memory :> wbytes (word_add (rsp0:int64) (word 16))) s0 = (K:1600 word)` then
    MAP_EVERY (fun t -> let f = SPONGE_NUMRED(MATCH_MP READ_MEMORY_BYTES128_OF_WBYTES (CONJ th (ARITH_RULE(sponge_ltc t 12)))) in
                ASSUME_TAC (CONV_RULE(RAND_CONV(DEPTH_CONV NUM_MULT_CONV)) (SPONGE_NORMADDR f))) [0;1;2;3]
    else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if concl th = `read (memory :> bytes(word_add (rsp0:int64) (word 352),64)) s0 = TB` then
    MAP_EVERY (fun t -> ASSUME_TAC(TR_NORM_RULE(tr_mp_conj (SPECL [`word_add (rsp0:int64) (word 352)`; `64`; `TB:num`; mk_small_numeral (16*t); `s0:x86state`] TR_CHUNK128_OF_NUM) th))) [0;1;2;3]
    else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if concl th = `read (memory :> bytes64 (word_add (rsp0:int64) (word 232))) s0 = Z`
    then ASSUME_TAC(MATCH_MP PK_READ_BYTES64_LOW8 th) else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if concl th = `read (memory :> bytes(word_add (rsp0:int64) (word 352),64)) s0 = TB`
      then let b = ISPECL [`word_add (rsp0:int64) (word 352)`; `64`;
                           `read memory (s0:x86state)`] READ_BYTES_BOUND in
           ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) (REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE; th] b))
      else NO_TAC);;

(*** name the 128-bit low parts of YMM0..3 in state s by variables d0..d3 ***)
let PKTRC_NAME_XMM_TAC (s:term) =
  MAP_EVERY (fun n ->
    FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && lhs c = mk_comb(mk_comb(`read:(x86state,int256)component->x86state->int256`,
                                            mk_const("YMM"^string_of_int n,[])),s)
      then
        let r = rhs c in
        let x = if is_comb r && is_comb (rator r) &&
                   (try fst(dest_const(rator(rator r))) = "word_join" with _ -> false)
                then rand r else failwith "PKTRC_NAME_XMM_TAC" in
        TR_NAME_TAC x ("d"^string_of_int n)
      else NO_TAC)) [0;1;2;3];;

let PKTRC_CMP_TAC : tactic = fun (asl,w) ->
  let l = lhs w in
  let ds = [`d0:int128`; `d1:int128`; `d2:int128`; `d3:int128`] in
  let cands = find_terms (fun t -> type_of t = `:int128` && exists (fun d -> free_in d t) ds) l in
  let maxs = filter (fun t -> not (exists (fun u -> u <> t && free_in t u) cands)) cands in
  let isor t = can (find_term (fun u -> is_comb u && is_comb(rator u) &&
                   (try fst(dest_const(rator(rator u))) = "word_or" with _ -> false) &&
                   type_of u = `:int128`)) t in
  let ror = find isor maxs in
  let gs = map (fun t -> genvar `:int128`) maxs in
  let l' = subst (zip gs maxs) l in
  let gor = assoc ror (zip maxs gs) in
  let tgt = mk_conj(`word_zx (word_or (cf4:int32) (word_or c14 (word_or c12 (word_or c13 cbx)))):byte = word 0`,
             mk_conj(`word_zx (Z:int64):byte = word 0`,
                     mk_eq(mk_comb(`word_zx:int128->byte`,gor),`word 0:byte`))) in
  let tha = SPECL maxs (BITBLAST_RULE (list_mk_forall(gs, mk_eq(l',tgt)))) in
  let dg = map (fun d -> genvar `:int128`) ds in
  let thb = SPECL ds (BITBLAST_RULE (list_mk_forall(dg,
     mk_eq(mk_eq(mk_comb(`word_zx:int128->byte`,subst (zip dg ds) ror),`word 0:byte`),
           list_mk_conj(map (fun d -> mk_eq(d,`word 0:int128`)) dg))))) in
  (CONV_TAC(LAND_CONV(REWR_CONV tha)) THEN REWRITE_TAC[thb]) (asl,w);;

let PKTRC_TAC exec =
  PKTRC_PRE_TAC exec THEN
  SIMD_STEPS_TAC exec (1--31) THEN
  PKTRC_NAME_XMM_TAC `s31:x86state` THEN
  SIMD_STEPS_TAC exec (32--72) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [CONV_TAC(LAND_CONV(LAND_CONV(SIMD_SIMPLIFY_CONV [] THENC REWRITE_CONV[WORD_VAL_MOD_256]))) THEN
    PKTRC_CMP_TAC THEN
    MAP_EVERY (fun v -> TR_UNNAME_GOAL_TAC v) ["d0";"d1";"d2";"d3"] THEN
    REWRITE_TAC[WORD_XOR_EQ_0] THEN
    REWRITE_TAC[MATCH_MP (SPECL [`K:1600 word`; `TB:num`] PK_VAL512_CHUNKS) (ASSUME `TB < 2 EXP 512`)] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_1; CONJ_ACI];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let PROVE_PKTRC fn head exit =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc [(head, exit)] in
  prove(PKTRC_STMT fn head exit, PKTRC_TAC exec);;

(* ------------------------------------------------------------------------- *)
(* TAIL: RED, HASH and TRC in a row, from the exit of the comparison loop to *)
(* the test of R13: the low byte of R13 is zero if and only if the norm      *)
(* checks passed, the t0 comparison found no difference and the SHAKE256 of  *)
(* the key equals tr. The callers use this region alone.                     *)
(* ------------------------------------------------------------------------- *)

let PK_SHAKE_BYTES_OF_SUBWORDS = prove
 (`!(X:1600 word) n.
     8 * n <= 1600
     ==> num_of_bytelist(list_of_seq (\j. word_subword X (8 * j,8):byte) n) =
         val X MOD 2 EXP (8 * n)`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; num_of_bytelist; MULT_CLAUSES; EXP; MOD_1] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ; num_of_bytelist;
                  MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 + 8 * n = 8 * n + 8`; EXP_ADD] THEN
  MP_TAC(SPECL [`val(X:1600 word)`; `2 EXP (8 * n)`; `2 EXP 8`] MOD_MULT_MOD) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `256 * x = x * 256`] THEN ARITH_TAC);;

let PK_SHAKE_BYTES = prove
 (`!n P. num_of_bytelist(list_of_seq (mld_shake256_byte n P) 64) =
         val(keccak_f1600 (mld_shake256_state n P)) MOD 2 EXP 512`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`keccak_f1600 (mld_shake256_state n P)`; `64`] PK_SHAKE_BYTES_OF_SUBWORDS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[mld_shake256_byte; mld_keccak_squeeze_byte] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `(136 + j) DIV 136 = 1 /\ (136 + j) MOD 136 = j` (fun th -> REWRITE_TAC[th]) THENL
   [ONCE_REWRITE_TAC[ADD_SYM] THEN
    SUBGOAL_THEN `j + 136 = j + 1 * 136` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_EQ; DIV_LT; MOD_LT;
                 ARITH_RULE `j < 64 ==> j < 136`] THEN ARITH_TAC;
    REWRITE_TAC[num_CONV `1`; keccak_squeeze]]);;

let PK_SLOT_CANCEL = prove
 (`!b (y:byte).
     word_zx (word_xor (word_xor (if b then word 0 else word 4294967295:int64)
                                 (word_zx y)) (word_zx y)):byte = word 0 <=> b`,
  GEN_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_BLAST);;

let PKTAIL_STMT fn head exit = parse_term(subst_tokens
 ["@MC@",image_mc; "@H@",string_of_int head; "@X@",string_of_int exit]
 "exists f_events.
   forall e rsp0 pk pc PK TB (x0:int128) (x1:int128) (x2:int128) (x3:int128)
          (c14:int32) (c12:int32) (c13:int32) (cbx:int32) (cf4:int32).
     aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
     aligned 32 (rsp0:int64) /\\
     ALL (nonoverlapping (word_sub rsp0 (word 296),712))
         [(word pc,libmldsa_size); (pk,1312)]
     ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
               read RIP s = word (pc + @H@) /\\ read RSP s = rsp0 /\\
               read XMM0 s = x0 /\\ read XMM1 s = x1 /\\ read XMM2 s = x2 /\\ read XMM3 s = x3 /\\
               read R14 s = word_zx c14 /\\ read R12 s = word_zx c12 /\\
               read R13 s = word_zx c13 /\\ read RBX s = word_zx cbx /\\
               read (memory :> bytes32 (word_add rsp0 (word 244))) s = cf4 /\\
               read (memory :> bytes64 (word_add rsp0 (word 248))) s = pk /\\
               read (memory :> bytes(pk,1312)) s = PK /\\
               read (memory :> bytes(word_add rsp0 (word 352),64)) s = TB /\\
               read events s = e)
          (\\s. read RIP s = word (pc + @X@) /\\ read RSP s = rsp0 /\\ read R15 s = pk /\\
               (word_zx (read R13 s):byte = word 0 <=>
                word_zx (word_or cf4 (word_or c14 (word_or c12 (word_or c13 cbx)))):byte = word 0 /\\
                word_or x0 x1 = word 0 /\\
                num_of_bytelist(list_of_seq (mld_shake256_byte 1312 PK) 64) = TB) /\\
               (exists e2. read events s = APPEND e2 e /\\
                  e2 = f_events (word_sub rsp0 (word 296)) pk pc /\\
                  memaccess_inbounds e2
                   [pk,1312; word_sub rsp0 (word 296),712;
                    word(pc + rodata_mld_KeccakF_RoundConstants),192]
                   [word_sub rsp0 (word 296),648]))
          (MAYCHANGE [RSP; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub rsp0 (word 296),648)])");;

let PKTAIL_TAC fn head exit red hash trc =
  let execth = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(head, exit)] in
  let vars = [`fb:int64`; `pk:int64`; `pc:num`] in
  let xv = `word_xor (if word_or (x0:int128) x1 = word 0 then word 0 else word 4294967295)
                     (word_zx (pk_xbyte (word_xor (x2:int128) x3))):int64`
  and yv = `pk_xbyte (word_xor (x2:int128) x3)` in
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 red) "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 hash) "H_HASH" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 trc) "H_TRC" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fb:int64) (pk:int64) (pc:num). f_ev_all fb pk pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  X_GEN_TAC `e:(uarch_event)list` THEN WORD_FORALL_OFFSET_TAC 296 THEN
  MAP_EVERY X_GEN_TAC [`fb:int64`; `pk:int64`; `pc:num`; `PK:num`; `TB:num`;
    `x0:int128`; `x1:int128`; `x2:int128`; `x3:int128`;
    `c14:int32`; `c12:int32`; `c13:int32`; `cbx:int32`; `cf4:int32`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_RED"
   [`read RSP s`; `pc:num`; `x0:int128`; `x1:int128`; `x2:int128`; `x3:int128`] vars 1 THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_HASH"
   [`read RSP s`; `pk:int64`; `pc:num`; `PK:num`; xv; yv] vars 2 THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_TRC"
   [`read RSP s`; `pc:num`; `keccak_f1600 (mld_shake256_state 1312 PK)`; `TB:num`;
    `c14:int32`; `c12:int32`; `c13:int32`; `cbx:int32`; `cf4:int32`;
    mk_comb(mk_comb(`word_xor:int64->int64->int64`,xv),`word_zx (pk_xbyte (word_xor (x2:int128) x3)):int64`)] vars 3 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[PK_SLOT_CANCEL; PK_SHAKE_BYTES] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PROVE_PKTAIL fn head exit red hash trc =
  prove(PKTAIL_STMT fn head exit, PKTAIL_TAC fn head exit red hash trc);;

(* ------------------------------------------------------------------------- *)
(* TRCB and TAILB: TRC and TAIL as in ML-DSA-65 and ML-DSA-87, where the      *)
(* state is at rsp0, the hash is copied to rsp0 + cpy and compared with tr   *)
(* at rsp0 + tbo, the check byte (the slot at rsp0 + zo XORed with the byte  *)
(* at rsp0 + yo) is computed here, and the norm checks of s2 are partly in   *)
(* 64-bit slots (as word_zx of their 32-bit result) and partly in registers, *)
(* with the result in register res. The norm checks are given as lists      *)
(* slots = [offset,name] and regs = [register,name], and order lists the     *)
(* names in the order of the polynomials of s2; the statement has the OR of  *)
(* the check of s1 (cf, at rsp0 + cfo) and those of s2 in this order.        *)
(* ------------------------------------------------------------------------- *)

let pkb_or order =
  let rec go l = match l with
      [] -> failwith "pkb_or"
    | [c] -> c
    | c::t -> "word_or " ^ c ^ " (" ^ go t ^ ")" in
  "word_or (cf:int32) (" ^ go order ^ ")";;

let pkb_cvars order = String.concat " " (map (fun c -> "(" ^ c ^ ":int32)") order);;

let pkb_slots slots = String.concat " /\\\n         "
  (map (fun (off,c) -> Printf.sprintf
     "read (memory :> bytes64 (word_add rsp0 (word %d))) s = word_zx %s" off c) slots);;

let pkb_regs regs = String.concat " /\\\n         "
  (map (fun (r,c) -> Printf.sprintf "read %s s = word_zx %s" r c) regs);;

let PKTRCB_STMT fn head exit tbo cfo zo yo slots regs order res rlen wlen =
  parse_term(subst_tokens
 ["@MC@",image_mc; "@H@",string_of_int head; "@X@",string_of_int exit;
  "@TB@",string_of_int tbo; "@CF@",string_of_int cfo; "@Z@",string_of_int zo;
  "@Y@",string_of_int yo; "@CVARS@",pkb_cvars order; "@SLOTS@",pkb_slots slots;
  "@REGS@",pkb_regs regs; "@OR@",pkb_or order; "@RES@",res;
  "@RLEN@",string_of_int rlen; "@WLEN@",string_of_int wlen]
 "exists f_events. forall e rsp0 pc (K:1600 word) TB @CVARS@ (cf:int32) (Z:int64) (Y:byte).
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   aligned 32 (rsp0:int64) /\\
   nonoverlapping (word pc,libmldsa_size) (rsp0,@RLEN@)
   ==> ensures x86
    (\\s. bytes_loaded s (word pc) @MC@ /\\
         read RIP s = word (pc + @H@) /\\ read RSP s = rsp0 /\\
         read (memory :> wbytes rsp0) s = K /\\
         read (memory :> bytes(word_add rsp0 (word @TB@),64)) s = TB /\\
         @SLOTS@ /\\
         @REGS@ /\\
         read (memory :> bytes32 (word_add rsp0 (word @CF@))) s = cf /\\
         read (memory :> bytes64 (word_add rsp0 (word @Z@))) s = Z /\\
         read (memory :> bytes8 (word_add rsp0 (word @Y@))) s = Y /\\
         read events s = e)
    (\\s. read RIP s = word (pc + @X@) /\\ read RSP s = rsp0 /\\
         (word_zx (read @RES@ s):byte = word 0 <=>
          word_zx (@OR@):byte = word 0 /\\
          word_zx (word_xor Z (word_zx Y)):byte = word 0 /\\
          val K MOD 2 EXP 512 = TB) /\\
         (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
            memaccess_inbounds e2 [rsp0,@RLEN@] [rsp0,@WLEN@]))
    (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; @RES@] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(rsp0,@WLEN@)])");;

let PK_READ_BYTES64_LOW32 = prove
 (`!a:int64 x s:x86state.
     read (memory :> bytes64 a) s = x
     ==> read (memory :> bytes32 a) s = word_zx x`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; READ_COMPONENT_COMPOSE;
              BYTES64_WBYTES; BYTES32_WBYTES; VAL_READ_WBYTES;
              DIMINDEX_64; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP (8 * 4)`; READ_BYTES_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(*** the slots of the checks, also as 32-bit reads (the code reads some of
     them with OR r32, m32) ***)

let PKB_SLOTS32_TAC =
  let pat = `read (memory :> bytes64 (word_add (rsp0:int64) (word n))) s0 = word_zx (c:int32)` in
  W(fun (asl,w) ->
    MAP_EVERY (fun (_,th) ->
      if can (term_match [] pat) (concl th)
      then ASSUME_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32] (MATCH_MP PK_READ_BYTES64_LOW32 th))
      else ALL_TAC) asl);;

let PKTRCB_PRE_TAC exec vars aoffs tbo =
  let tba = subst [mk_small_numeral tbo,`n:num`] `word_add (rsp0:int64) (word n)` in
  let tbf = subst [tba,`a:int64`] `read (memory :> bytes(a,64)) s0 = TB` in
  CONCRETIZE_F_EVENTS_TAC `\(rsp0:int64) (pc:num). f_ev_t rsp0 pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC vars THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  PKTRC_ALIGN_TAC aoffs THEN
  MAP_EVERY (fun n ->
   GHOST_INTRO_TAC (mk_var("ymm"^string_of_int n^"_init",`:int256`))
    (mk_comb(`read:(x86state,int256)component->x86state->int256`,
             mk_const("YMM"^string_of_int n,[])))) (0--4) THEN
  FULL_INIT_TAC THEN
  FIRST_ASSUM(fun th -> if concl th = `read (memory :> wbytes (rsp0:int64)) s0 = (K:1600 word)` then
    MAP_EVERY (fun t -> let f = SPONGE_NUMRED(MATCH_MP READ_MEMORY_BYTES128_OF_WBYTES (CONJ th (ARITH_RULE(sponge_ltc t 12)))) in
                ASSUME_TAC (CONV_RULE(RAND_CONV(DEPTH_CONV NUM_MULT_CONV))
                             (REWRITE_RULE[WORD_ADD_0] (SPONGE_NORMADDR f)))) [0;1;2;3]
    else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if concl th = tbf then
    MAP_EVERY (fun t -> ASSUME_TAC(TR_NORM_RULE(tr_mp_conj (SPECL [tba; `64`; `TB:num`; mk_small_numeral (16*t); `s0:x86state`] TR_CHUNK128_OF_NUM) th))) [0;1;2;3]
    else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if concl th = tbf
      then let b = ISPECL [tba; `64`; `read memory (s0:x86state)`] READ_BYTES_BOUND in
           ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) (REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE; th] b))
      else NO_TAC) THEN
  PKB_SLOTS32_TAC;;

(*** As PKTRC_CMP_TAC, with the conjuncts of the checks given ***)

let PKTRCB_CMP_TAC orc zyc : tactic = fun (asl,w) ->
  let l = lhs w in
  let ds = [`d0:int128`; `d1:int128`; `d2:int128`; `d3:int128`] in
  let cands = find_terms (fun t -> type_of t = `:int128` && exists (fun d -> free_in d t) ds) l in
  let maxs = filter (fun t -> not (exists (fun u -> u <> t && free_in t u) cands)) cands in
  let isor t = can (find_term (fun u -> is_comb u && is_comb(rator u) &&
                   (try fst(dest_const(rator(rator u))) = "word_or" with _ -> false) &&
                   type_of u = `:int128`)) t in
  let ror = find isor maxs in
  let gs = map (fun t -> genvar `:int128`) maxs in
  let l' = subst (zip gs maxs) l in
  let gor = assoc ror (zip maxs gs) in
  let tgt = mk_conj(orc, mk_conj(zyc,
                     mk_eq(mk_comb(`word_zx:int128->byte`,gor),`word 0:byte`))) in
  let tha = SPECL maxs (BITBLAST_RULE (list_mk_forall(gs, mk_eq(l',tgt)))) in
  let dg = map (fun d -> genvar `:int128`) ds in
  let thb = SPECL ds (BITBLAST_RULE (list_mk_forall(dg,
     mk_eq(mk_eq(mk_comb(`word_zx:int128->byte`,subst (zip dg ds) ror),`word 0:byte`),
           list_mk_conj(map (fun d -> mk_eq(d,`word 0:int128`)) dg))))) in
  (CONV_TAC(LAND_CONV(REWR_CONV tha)) THEN REWRITE_TAC[thb]) (asl,w);;

let PKTRCB_TAC exec vars aoffs tbo n1 n2 order =
  let orc = parse_term("word_zx (" ^ pkb_or (map (fun c -> "(" ^ c ^ ":int32)") order) ^ "):byte = word 0")
  and zyc = `word_zx (word_xor (Z:int64) (word_zx (Y:byte))):byte = word 0` in
  PKTRCB_PRE_TAC exec vars aoffs tbo THEN
  SIMD_STEPS_TAC exec (1--n1) THEN
  PKTRC_NAME_XMM_TAC (mk_var("s"^string_of_int n1,`:x86state`)) THEN
  SIMD_STEPS_TAC exec ((n1+1)--n2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [CONV_TAC(LAND_CONV(LAND_CONV(SIMD_SIMPLIFY_CONV [] THENC REWRITE_CONV[WORD_VAL_MOD_256]))) THEN
    PKTRCB_CMP_TAC orc zyc THEN
    MAP_EVERY (fun v -> TR_UNNAME_GOAL_TAC v) ["d0";"d1";"d2";"d3"] THEN
    REWRITE_TAC[WORD_XOR_EQ_0] THEN
    REWRITE_TAC[MATCH_MP (SPECL [`K:1600 word`; `TB:num`] PK_VAL512_CHUNKS) (ASSUME `TB < 2 EXP 512`)] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_1; CONJ_ACI];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

(*** cpy: the offset of the copy of the hash; aoffs are the 16-byte aligned
     offsets the code accesses (the state, the copy and tr) ***)

let PROVE_PKTRCB fn head exit cpy tbo cfo zo yo slots regs order res rlen wlen n1 n2 =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc [(head, exit)] in
  let vars = [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `K:1600 word`; `TB:num`] @
             map (fun c -> mk_var(c,`:int32`)) order @ [`cf:int32`; `Z:int64`; `Y:byte`] in
  let aoffs = map (fun j -> 16 * j) (1--12) @ map (fun j -> cpy + 16 * j) (0--3) @
              map (fun j -> tbo + 16 * j) (0--3) in
  prove(PKTRCB_STMT fn head exit tbo cfo zo yo slots regs order res rlen wlen,
        PKTRCB_TAC exec vars aoffs tbo n1 n2 order);;

let PKTAILB_STMT fn head exit pslot plen tbo cfo slots regs order res rlen wlen =
  parse_term(subst_tokens
 ["@MC@",image_mc; "@H@",string_of_int head; "@X@",string_of_int exit;
  "@PS@",string_of_int pslot; "@PLEN@",string_of_int plen;
  "@TB@",string_of_int tbo; "@CF@",string_of_int cfo;
  "@CVARS@",pkb_cvars order; "@SLOTS@",pkb_slots slots;
  "@REGS@",pkb_regs regs; "@OR@",pkb_or order; "@RES@",res;
  "@RLEN@",string_of_int rlen; "@WLEN@",string_of_int wlen]
 "exists f_events.
   forall e rsp0 pk pc PK TB (x0:int128) (x1:int128) (x2:int128) (x3:int128)
          @CVARS@ (cf:int32).
     aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
     aligned 32 (rsp0:int64) /\\
     ALL (nonoverlapping (word_sub rsp0 (word 296),@RLEN@))
         [(word pc,libmldsa_size); (pk,@PLEN@)]
     ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
               read RIP s = word (pc + @H@) /\\ read RSP s = rsp0 /\\
               read XMM0 s = x0 /\\ read XMM1 s = x1 /\\ read XMM2 s = x2 /\\ read XMM3 s = x3 /\\
               @SLOTS@ /\\
               @REGS@ /\\
               read (memory :> bytes32 (word_add rsp0 (word @CF@))) s = cf /\\
               read (memory :> bytes64 (word_add rsp0 (word @PS@))) s = pk /\\
               read (memory :> bytes(pk,@PLEN@)) s = PK /\\
               read (memory :> bytes(word_add rsp0 (word @TB@),64)) s = TB /\\
               read events s = e)
          (\\s. read RIP s = word (pc + @X@) /\\ read RSP s = rsp0 /\\ read R15 s = pk /\\
               (word_zx (read @RES@ s):byte = word 0 <=>
                word_zx (@OR@):byte = word 0 /\\
                word_or x0 x1 = word 0 /\\
                num_of_bytelist(list_of_seq (mld_shake256_byte @PLEN@ PK) 64) = TB) /\\
               (exists e2. read events s = APPEND e2 e /\\
                  e2 = f_events (word_sub rsp0 (word 296)) pk pc /\\
                  memaccess_inbounds e2
                   [pk,@PLEN@; word_sub rsp0 (word 296),@RLEN@;
                    word(pc + rodata_mld_KeccakF_RoundConstants),192]
                   [word_sub rsp0 (word 296),@WLEN@]))
          (MAYCHANGE [RSP; @RES@; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub rsp0 (word 296),@WLEN@)])");;

let PKTAILB_TAC head exit plen order red hash trc =
  let execth = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(head, exit)] in
  let vars = [`fb:int64`; `pk:int64`; `pc:num`] in
  let cs = map (fun c -> mk_var(c,`:int32`)) order in
  let xv = `word_xor (if word_or (x0:int128) x1 = word 0 then word 0 else word 4294967295)
                     (word_zx (pk_xbyte (word_xor (x2:int128) x3))):int64`
  and yv = `pk_xbyte (word_xor (x2:int128) x3)` in
  let st = subst [mk_small_numeral plen,`n:num`] `keccak_f1600 (mld_shake256_state n PK)` in
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 red) "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 hash) "H_HASH" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 trc) "H_TRC" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fb:int64) (pk:int64) (pc:num). f_ev_all fb pk pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  X_GEN_TAC `e:(uarch_event)list` THEN WORD_FORALL_OFFSET_TAC 296 THEN
  MAP_EVERY X_GEN_TAC ([`fb:int64`; `pk:int64`; `pc:num`; `PK:num`; `TB:num`;
    `x0:int128`; `x1:int128`; `x2:int128`; `x3:int128`] @ cs @ [`cf:int32`]) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_RED"
   [`read RSP s`; `pc:num`; `x0:int128`; `x1:int128`; `x2:int128`; `x3:int128`] vars 1 THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_HASH"
   [`read RSP s`; `pk:int64`; `pc:num`; `PK:num`] vars 2 THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_TRC"
   ([`read RSP s`; `pc:num`; st; `TB:num`] @ cs @ [`cf:int32`; xv; yv]) vars 3 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[PK_SLOT_CANCEL; PK_SHAKE_BYTES] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PROVE_PKTAILB fn head exit pslot plen tbo cfo slots regs order res rlen wlen red hash trc =
  prove(PKTAILB_STMT fn head exit pslot plen tbo cfo slots regs order res rlen wlen,
        PKTAILB_TAC head exit plen order red hash trc);;

(* ------------------------------------------------------------------------- *)
(* The end of pk_from_sk, from join1 to the return: the memsets and SSE      *)
(* stores that clear the buffers in the frame, and the epilogue. This is     *)
(* CL_STMT of inline_verify.ml (in the version of c23-x86-C, with the saved  *)
(* registers and the return address as two regions) with the result in RBX  *)
(* instead of R14, and proved with the same tools (RUN_STRAIGHT_TAC).        *)
(* ------------------------------------------------------------------------- *)

let PKCL_STMT fn fr =
  let frs = string_of_int (fr + 8) in
  parse_term(subst_tokens ["@FN@",fn; "@FR8@",frs; "@MC@",image_mc]
  "!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e rsp0 rb r pc rbx0 r12_0 r13_0 r14_0 r15_0 rbp_0 ra.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 (rsp0:int64) /\\
          ALL (nonoverlapping (word_sub rsp0 (word 8),@FR8@))
              [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el);
               (rb,56)]
          ==> ensures x86
               (\\s. bytes_loaded s (word pc) @MC@ /\\
                    read RIP s = word (pc + @FN@_join1) /\\
                    read RSP s = rsp0 /\\ read RBP s = word_add rb (word 40) /\\
                    read RBX s = r /\\
                    read (memory :> bytes64 rb) s = rbx0 /\\
                    read (memory :> bytes64 (word_add rb (word 8))) s = r12_0 /\\
                    read (memory :> bytes64 (word_add rb (word 16))) s = r13_0 /\\
                    read (memory :> bytes64 (word_add rb (word 24))) s = r14_0 /\\
                    read (memory :> bytes64 (word_add rb (word 32))) s = r15_0 /\\
                    read (memory :> bytes64 (word_add rb (word 40))) s = rbp_0 /\\
                    read (memory :> bytes64 (word_add rb (word 48))) s = ra /\\
                    (read DF s <=> false) /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    read events s = e)
               (\\s. read RIP s = ra /\\
                    read RSP s = word_add rb (word 56) /\\
                    read RAX s = word_zx(word_zx r:int32) /\\
                    read RBX s = rbx0 /\\ read R12 s = r12_0 /\\ read R13 s = r13_0 /\\
                    read R14 s = r14_0 /\\ read R15 s = r15_0 /\\ read RBP s = rbp_0 /\\
                    (exists e2. read events s = APPEND e2 e /\\
                       e2 = f_events (word_sub rsp0 (word 8)) rb mf pc ra /\\
                       memaccess_inbounds e2
                        [word_sub rsp0 (word 8),@FR8@; rb,48; word_add rb (word 48),8;
                         word(pc + got_memset),8; ea,el]
                        [word_sub rsp0 (word 8),@FR8@]))
               (MAYCHANGE [RSP; RBX; RBP; R12; R13; R14; R15] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(word_sub rsp0 (word 8),@FR8@)])");;

let PKCL_TAC fn fr aoffs =
  let execth = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_join1"), layout (fn^"_ret") + 1); layout_range "plt_memset"] in
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_full_contract] th) "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (rb:int64) (mf:int64) (pc:num) (ra:int64).
      f_ev_all rsp0 rb mf pc ra:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  X_GEN_TAC `e:(uarch_event)list` THEN WORD_FORALL_OFFSET_TAC 8 THEN
  MAP_EVERY X_GEN_TAC [`rsp0:int64`; `rb:int64`; `r:int64`; `pc:num`;
    `rbx0:int64`; `r12_0:int64`; `r13_0:int64`; `r14_0:int64`; `r15_0:int64`; `rbp_0:int64`; `ra:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  CL_ALIGNED_TAC aoffs THEN
  ASSUME_TAC(prove(`word_add (word_add rb (word 40)) (word 18446744073709551576):int64 = rb`,
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[WORD_ADD_0])) THEN
  FULL_INIT_TAC THEN
  RUN_STRAIGHT_TAC execth "H_MEMSET"
    (ref [`rsp0:int64`; `rb:int64`; `mf:int64`; `pc:num`; `ra:int64`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_VAL_ADD_64; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PROVE_PKCL fn fr aoffs = prove(PKCL_STMT fn fr, PKCL_TAC fn fr aoffs);;

(* ------------------------------------------------------------------------- *)
(* Two byte strings of length n, as numbers, are equal if and only if their  *)
(* bytes are.                                                                *)
(* ------------------------------------------------------------------------- *)

let PK_BYTELIST_EQ = prove
 (`!(f:num->byte) g n.
     num_of_bytelist(list_of_seq f n) = num_of_bytelist(list_of_seq g n) <=>
     !j. j < n ==> f j = g j`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `bytelist_of_num n`) THEN
    MP_TAC(ISPEC `list_of_seq (f:num->byte) n` BYTELIST_OF_NUM_OF_BYTELIST) THEN
    MP_TAC(ISPEC `list_of_seq (g:num->byte) n` BYTELIST_OF_NUM_OF_BYTELIST) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `EL j:(byte)list->byte`) THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ];
    DISCH_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN ASM_REWRITE_TAC[]]);;

