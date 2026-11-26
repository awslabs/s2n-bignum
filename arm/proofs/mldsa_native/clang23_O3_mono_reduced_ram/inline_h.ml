(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Region lemmas for mld_H44, mld_H65 and mld_H87 of the                     *)
(* clang23_O3_mono_reduced_ram image, where clang inlined the absorbing of   *)
(* three inputs into one SHAKE256 state (at the stack pointer), the padding  *)
(* and the squeezing. The XOR of a number of bytes of an input into the      *)
(* state at a position off takes one of several paths over the loops of      *)
(* inline_sponge.ml (blocks of 32 bytes, of 8 bytes, single bytes), chosen   *)
(* by the length; a run-time test of whether the input overlaps the state    *)
(* picks the byte loop or the vector loops. Both are correct when the input  *)
(* and the state do not overlap, and the lemmas cover both, so that nothing  *)
(* has to be known about the addresses beyond that.                          *)
(*                                                                           *)
(* The code of the three functions has the same shape: mld_H65 is mld_H44    *)
(* at another address, and mld_H87 has other registers, offsets 4 lower in   *)
(* the absorbing part and other names for the labels of the vector loops at  *)
(* the end. The generators take the names of the labels and registers.       *)
(* ========================================================================= *)

needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_hash.ml";;
needs "common/fips202/properties/keccak_fips202.ml";;
needs "arm/proofs/utils/mldsa_native_signing.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;
needs "common/fips204/properties/mldsa_native_squeeze.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sponge3.ml";;

let H_MC = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc";;

(* ------------------------------------------------------------------------- *)
(* The registers and labels of a function. d1/l1, d2/l2, d3/l3: the input    *)
(* pointers and lengths (l1 holds the position after the first absorb);      *)
(* the names of the loops of the vector paths of the three tails.            *)
(* ------------------------------------------------------------------------- *)

type hfn =
  { hf : string;
    d1 : string; l1 : string; d2 : string; l2 : string;
    d3 : string; l3 : string;
    t1q : string; t1d : string;
    t2q : string; t2d : string;
    t3q : string; t3d : string };;

let H44_FN =
  { hf = "mld_H44"; d1 = "X26"; l1 = "X23"; d2 = "X25"; l2 = "X24";
    d3 = "X22"; l3 = "X21";
    t1q = "loop13"; t1d = "loop14"; t2q = "loop17"; t2d = "loop18";
    t3q = "loop15"; t3d = "loop16" };;

let H65_FN = { H44_FN with hf = "mld_H65" };;

let H87_FN =
  { hf = "mld_H87"; d1 = "X25"; l1 = "X22"; d2 = "X24"; l2 = "X23";
    d3 = "X21"; l3 = "X20";
    t1q = "loop12"; t1d = "loop13"; t2q = "loop16"; t2d = "loop17";
    t3q = "loop14"; t3d = "loop15" };;

let H_LAB h l = h.hf ^ "_" ^ l;;

let H_EXEC_CACHE = ref ([]:(string * (thm * thm option array)) list);;

let H_EXEC h =
  try assoc h.hf !H_EXEC_CACHE with Failure _ ->
  let th = ARM_MK_EXEC_RANGES_RULE
             mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
             (if h.hf = "mld_H87" then [layout_range h.hf]
              else [layout_range h.hf; layout_range "plt_memcpy"]) in
  H_EXEC_CACHE := (h.hf,th) :: !H_EXEC_CACHE; th;;

(* ------------------------------------------------------------------------- *)
(* The loop lemmas of inline_sponge.ml for the loops of a function.          *)
(* ------------------------------------------------------------------------- *)

let H_PTR h loop dr pr cr t1 t2 =
  INLINE_XOR_BYTES_PTR_LOOP H_MC (H_EXEC h) (H_LAB h loop)
    (H_LAB h (loop ^ "_exit")) dr pr cr t1 t2;;

let H_IDX h loop dr pr ir lr t1 t2 =
  INLINE_XOR_BYTES_IDX_LOOP H_MC (H_EXEC h) (H_LAB h loop)
    (H_LAB h (loop ^ "_exit")) dr pr ir lr t1 t2;;

let H_DL h loop dr pr cr =
  INLINE_XOR_BYTES_D_LOOP H_MC (H_EXEC h) (H_LAB h loop)
    (H_LAB h (loop ^ "_exit")) dr pr cr ["Q0";"Q1"];;

let H_QL h loop dr pr cr =
  INLINE_XOR_BYTES_Q_LOOP H_MC (H_EXEC h) (H_LAB h loop)
    (H_LAB h (loop ^ "_exit")) dr pr cr ["Q0";"Q1";"Q2";"Q3"];;

(* ------------------------------------------------------------------------- *)
(* The XOR of len bytes of the data at d into the state at a, from position  *)
(* off on, as a region lemma from the label ent to the label ext. The state  *)
(* is given as 200 bytes, val S before and the XOR after; regs are the facts *)
(* about the registers on entry (and on exit, kept), as strings, and ch the  *)
(* registers that the region changes.                                        *)
(* ------------------------------------------------------------------------- *)

let H_XR_STMT h ent ext hyp regs_in regs_out ch =
  parse_term(Printf.sprintf
   "exists f_events. forall e a d off len (S:1600 word) m pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      %s /\\ off + len <= 200 /\\
      nonoverlapping (a,200) (word pc,libmldsa_size) /\\
      nonoverlapping (a,200) (d,len)
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc) %s /\\
                read PC s = word (pc + %s) /\\ %s /\\
                read (memory :> bytes(d,len)) s = m /\\
                read (memory :> bytes(a,200)) s = val S /\\
                read events s = e)
           (\\s. read PC s = word (pc + %s) /\\ %s /\\
                read (memory :> bytes(d,len)) s = m /\\
                read (memory :> bytes(a,200)) s =
                val(word_xor S (word(2 EXP (8 * off) * m))) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events a d off len pc /\\
                   memaccess_inbounds e2 [a,200; d,len] [a,200]))
           (MAYCHANGE [PC; %s] ,, MAYCHANGE [Q0; Q1; Q2; Q3] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(a,200)])"
   hyp H_MC (H_LAB h ent) regs_in (H_LAB h ext) regs_out
   (String.concat "; " ch));;

(*** The tail of the second (t = 2) or third (t = 3) absorb, with the state
     pointer X8 at a + off: TVB from the byte loop (join10 / join19, any
     0 < len), TVV from the overlap test (join9 / join18, 8 <= len) ***)

let H_TV_REGS h t =
  let dr,lr = if t = 2 then h.d2,h.l2 else h.d3,h.l3 in
  Printf.sprintf "read X8 s = word_add a (word off) /\\ read %s s = d /\\ read %s s = word len" dr lr,
  Printf.sprintf "read %s s = d /\\ read %s s = word len" dr lr;;

let H_TV_ENT t v = match t,v with
    2,true -> "join9" | 2,false -> "join10"
  | _,true -> "join18" | _,false -> "join19";;
let H_TV_EXT t = if t = 2 then "join12" else "join21";;
let H_TV_JOIN11 t = if t = 2 then "join11" else "join20";;
let H_TV_LOOPB t = if t = 2 then "loop6" else "loop11";;

let H_TV_STMT h t v =
  let ri,ro = H_TV_REGS h t in
  H_XR_STMT h (H_TV_ENT t v) (H_TV_EXT t)
    (if v then "8 <= len" else "0 < len") ri ro
    ["X8"; "X9"; "X10"; "X11"; "X12"; "X13"];;

(* ------------------------------------------------------------------------- *)
(* Tactics for the paths of the XOR regions.                                 *)
(* ------------------------------------------------------------------------- *)

(*** From the state as 200 bytes, the split form of inline_sponge.ml at the
     start (byte off), simplified ***)

let H_START_TAC =
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) &&
       can (term_match [] `read (memory :> bytes(a:int64,200)) s = val(S:1600 word)`) (concl th)
    then
      let s = rand(lhand(concl th)) in
      MP_TAC(SPECL [`a:int64`; `S:1600 word`; `m:num`; `off:num`; s] XOR_START) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [SIMPLE_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
                      REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC]
    else NO_TAC);;

(*** At the end, the state as 200 bytes from the split form at off + len ***)

let H_FINAL_TAC sname =
  let s = mk_var(sname,`:armstate`) in
  MP_TAC(SPECL [`a:int64`; `d:int64`; `S:1600 word`; `m:num`; `off:num`;
                `len:num`; s] XOR_FINAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; SIMPLE_ARITH_TAC];
    DISCH_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; MONOTONE_MAYCHANGE_TAC;
         DISCHARGE_SAFETY_PROPERTY_TAC];;

(*** A loop lemma specialized to the arguments, simplified, as a hypothesis
     named newname; and its call at step n ***)

let H_SIMP =
  REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES; EXP; DIV_1; WORD_ADD_0; SUB_0];;

let H_SPEC_HYP name newname args =
  USE_THEN name (fun th ->
    let e0 = `e0:(uarch_event)list` in
    LABEL_TAC newname (GEN e0 (H_SIMP (SPECL (e0::args) th))));;

let H_XR_VARS = [`a:int64`; `d:int64`; `off:num`; `len:num`; `pc:num`];;

(*** A call of a region lemma: as FULL_CALL_TAC, but the simulation may
     leave equations of addresses before the events, as conjuncts ***)

let H_ADDR_EQ_TAC =
  CONV_TAC WORD_RULE ORELSE
  (REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
   AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let H_E2_TAC vars =
  REPEAT(CONJ_TAC THENL [H_ADDR_EQ_TAC; ALL_TAC]) THEN
  FULL_EXISTS_E2_TAC (ref vars);;

let H_FULL_CALL_TAC execth name ilist vars n =
  REMOVE_THEN name (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,execth,0x0,
       mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [H_E2_TAC vars; LABEL_TAC name th]);;

let H_CALL_TAC h name n = H_FULL_CALL_TAC (H_EXEC h) name [] H_XR_VARS n;;

(*** The setup of a region proof: the loop lemmas as hypotheses (named),
     the template of the events, the variables and the precondition ***)

let H_XR_SETUP h lemmas tmpl =
  MAP_EVERY (fun (th,name) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th name) lemmas THEN
  CONCRETIZE_F_EVENTS_TAC tmpl THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `d:int64`; `off:num`; `len:num`;
    `S:1600 word`; `m:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst (H_EXEC h)] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `len < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `off + len <= 200` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word len:int64) = len` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `off + len <= 200` THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN H_START_TAC;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic of the masks of the length in the dispatch code.               *)
(* ------------------------------------------------------------------------- *)

let H_AND_LOW = prove
 (`!n k. k <= 64 ==> word_and (word n:int64) (word(2 EXP k - 1)) = word(n MOD 2 EXP k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_AND_MASK_WORD] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= 64 ==> MIN 64 k = k /\ MIN k 64 = k`]);;
let H_MASKNEG = prove
 (`!n. word_and (word n:int64) (word 18446744073709551584) =
       word(32 * n DIV 32) /\
       word_and (word n:int64) (word 18446744073709551608) =
       word(8 * n DIV 8)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!x:int64. word_and x (word 18446744073709551584) =
              word_sub x (word_and x (word(2 EXP 5 - 1))) /\
              word_and x (word 18446744073709551608) =
              word_sub x (word_and x (word(2 EXP 3 - 1)))`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC NUM_REDUCE_CONV THEN GEN_TAC THEN CONJ_TAC THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  SIMP_TAC[H_AND_LOW; ARITH_RULE `5 <= 64 /\ 3 <= 64`] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[WORD_SUB2; MOD_LE] THEN CONJ_TAC THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`n:num`; `32`] DIVISION) THEN
  MP_TAC(SPECL [`n:num`; `8`] DIVISION) THEN ARITH_TAC);;

(*** The facts on len for the paths: masks, comparisons, differences ***)

let H_LEN_FACTS_TAC =
  SUBGOAL_THEN `len < 256` ASSUME_TAC THENL
   [UNDISCH_TAC `off + len <= 200` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> STRIP_ASSUME_TAC(MATCH_MP SPONGE2_MASK th)) THEN
  STRIP_ASSUME_TAC(SPEC `len:num` H_MASKNEG) THEN
  ASSUME_TAC(CONJUNCT2(SPEC `len:num` TL_MOD4)) THEN
  MAP_EVERY (fun t ->
    SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,mk_comb(`word:num->int64`,t)),t))
      ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      UNDISCH_TAC `len < 256` THEN ARITH_TAC; ALL_TAC])
   [`32 * len DIV 32`; `8 * len DIV 8`; `8 * (len DIV 8) MOD 4`;
    `len MOD 32`; `len MOD 8`] THEN
  SUBGOAL_THEN
   `32 * len DIV 32 <= len /\ len < 32 * len DIV 32 + 32 /\
    8 * len DIV 8 <= len /\ len < 8 * len DIV 8 + 8 /\
    32 * len DIV 32 + len MOD 32 = len /\ 8 * len DIV 8 + len MOD 8 = len /\
    (len DIV 8) MOD 4 < 4`
   STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`len:num`; `32`] DIVISION) THEN
    MP_TAC(SPECL [`len:num`; `8`] DIVISION) THEN
    MP_TAC(SPECL [`len DIV 8`; `4`] DIVISION) THEN ARITH_TAC;
    ALL_TAC];;

(*** The case split on len MOD 32 < 8, with the fact on the mask 0x18 ***)

let H_CASE_LT8_TAC t1 t2 =
  ASM_CASES_TAC `len MOD 32 < 8` THENL
   [SUBGOAL_THEN `8 * (len DIV 8) MOD 4 = 0` ASSUME_TAC THENL
     [MP_TAC(CONJUNCT1(SPEC `len:num` TL_MOD4)) THEN ASM_REWRITE_TAC[];
      t1];
    SUBGOAL_THEN `~(8 * (len DIV 8) MOD 4 = 0)` ASSUME_TAC THENL
     [MP_TAC(CONJUNCT1(SPEC `len:num` TL_MOD4)) THEN ASM_REWRITE_TAC[];
      t2]];;

let H_ARITH_CONSTS =
  ["="; "<"; "<="; ">"; ">="; "+"; "-"; "*"; "DIV"; "MOD"; "EXP"; "NUMERAL";
   "BIT0"; "BIT1"; "_0"; "~"; "/\\"; "\\/"; "==>"; "COND"; "T"; "F"; "SUC"];;

let H_IS_ARITH tm =
  forall (fun v -> type_of v = `:num`) (frees tm) &&
  forall (fun c -> mem (fst(dest_const c)) H_ARITH_CONSTS)
    (find_terms is_const tm);;

(*** Arithmetic from the small facts on numbers (as SPHS_ARITH_TAC) ***)

let H_ARITH_TAC =
  W(fun (asl,_) ->
    let ok th =
      let c = concl th in
      H_IS_ARITH c && String.length(string_of_term c) < 120 in
    MAP_EVERY MP_TAC (filter ok (map snd asl)) THEN ARITH_TAC);;

(*** Close a goal whose arithmetic facts are contradictory (a vacuous path) ***)

let H_CONTRA_TAC =
  TRY(fun (asl,w) ->
    (SUBGOAL_THEN `F` (fun th -> ACCEPT_TAC(CONTR w th)) THEN H_ARITH_TAC) (asl,w));;

(*** Replace the fact read R s = t by read R s = t' (t = t' proved) ***)

(* ------------------------------------------------------------------------- *)
(* The 32-bit position arithmetic of the code (add w23, w23, w24 and         *)
(* sub w8, w8, w23) on small numbers.                                        *)
(* ------------------------------------------------------------------------- *)

let H_W32_ADD = prove
 (`!a b. a + b < 2 EXP 32
         ==> word_zx(word_add (word_zx (word a:int64):int32)
                              (word_zx (word b:int64):int32)):int64 =
             word(a + b)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_ZX_WORD; DIMINDEX_32; DIMINDEX_64; GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `a < 18446744073709551616 /\ b < 18446744073709551616`
   STRIP_ASSUME_TAC THENL [UNDISCH_TAC `a + b < 2 EXP 32` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN REWRITE_TAC[GSYM WORD_ADD] THEN
  REWRITE_TAC[WORD_ZX_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN AP_TERM_TAC THEN
  REWRITE_TAC[ADD_MOD_MOD_REFL] THEN CONV_TAC MOD_DOWN_CONV THEN
  MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `a + b < 2 EXP 32` THEN ARITH_TAC);;

let H_W32_SUB136 = prove
 (`!p. p < 136
       ==> word_zx(word_sub (word 136:int32) (word_zx (word p:int64))):int64 =
           word(136 - p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_zx (word p:int64):int32 = word p` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_ZX_WORD; DIMINDEX_64] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[WORD_SUB2; ASSUME `p < 136`; LT_IMP_LE] THEN
  REWRITE_TAC[WORD_ZX_WORD; DIMINDEX_32] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;


let H_ZX2 = prove
 (`!n. n < 2 EXP 32 ==> word_zx(word_zx(word n:int64):int32):int64 = word n`,
  SIMP_TAC[WORD_ZX_UXTW_SMALL]);;

let H_NORM_TERM tm =
  rhs(concl((REWRITE_CONV[ADD_CLAUSES; MULT_CLAUSES; EXP; DIV_1; WORD_ADD_0;
                          SUB_0; WORD_SUB_0]) tm));;

let H_REG_TAC sname reg tgt0 =
  let tgt = H_NORM_TERM tgt0 in
  let s = mk_var(sname,`:armstate`) in
  let l = list_mk_comb(`read:(armstate,int64)component->armstate->int64`,[reg;s]) in
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && lhand(concl th) = l then
      if rand(concl th) = tgt then ASSUME_TAC th else
      SUBGOAL_THEN (mk_eq(rand(concl th),tgt)) (fun eq -> ASSUME_TAC(TRANS th eq)) THENL
       [FIRST
         [REWRITE_TAC[WORD_ADD_0; WORD_SUB_0] THEN NO_TAC;
          REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN H_ARITH_TAC;
          ASM_REWRITE_TAC[] THEN NO_TAC;
          MATCH_MP_TAC SPONGE2_WSUB THEN CONJ_TAC THEN H_ARITH_TAC;
          ASM_REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN NO_TAC;
          MATCH_MP_TAC H_W32_ADD THEN H_ARITH_TAC;
          MATCH_MP_TAC H_ZX2 THEN H_ARITH_TAC;
          SUBGOAL_THEN `off = 0` SUBST1_TAC THENL
           [H_ARITH_TAC; REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN NO_TAC];
          CONV_TAC WORD_RULE];
        ALL_TAC]
    else NO_TAC);;

(*** The arithmetic antecedents of a loop lemma, as facts before its call ***)

let H_PRE_TAC tms =
  MAP_EVERY (fun t ->
    let t' = H_NORM_TERM t in
    SUBGOAL_THEN t' ASSUME_TAC THENL [H_ARITH_TAC; ALL_TAC]) tms;;

(*** Split on the condition of a conditional PC ***)

let H_PC_SPLIT_TAC sname =
  let s = mk_var(sname,`:armstate`) in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = mk_comb(`read PC`,s) && is_cond(rand c) then
      let b,_ = dest_cond(rand c) in
      ASM_CASES_TAC b THEN
      FIRST_X_ASSUM(fun bth -> if concl bth = b || concl bth = mk_neg b then
        RULE_ASSUM_TAC(REWRITE_RULE[bth]) THEN ASSUME_TAC bth else NO_TAC)
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The vector part of the tails of the second and third absorbs (TVV), from  *)
(* the comparison of len with 32 at step n (after the overlap test). The     *)
(* paths: len < 32: 8-byte blocks, then the bytes if len MOD 8 <> 0;         *)
(* len >= 32: 32-byte blocks, then done, or the bytes, or 8-byte blocks and  *)
(* maybe the bytes. Each byte loop is from join11 / join20 with X9 = j0.     *)
(* ------------------------------------------------------------------------- *)

let H_SN n = "s" ^ string_of_int n;;

(*** Decide the condition of a conditional PC in state sname from the facts
     in the context; step with that after each instruction ***)

let H_COND_PROVE_TAC =
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN H_ARITH_TAC;;

let H_DECIDE_TAC sname =
  let s = mk_var(sname,`:armstate`) in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = mk_comb(`read PC`,s) && is_cond(rand c) then
      let b,_ = dest_cond(rand c) in
      let rw eth = FIRST_X_ASSUM(fun pth -> if concl pth = c then
                     ASSUME_TAC(REWRITE_RULE[eth] pth) else NO_TAC) in
      (SUBGOAL_THEN b (fun bth -> rw (EQT_INTRO bth)) THENL
        [H_COND_PROVE_TAC; ALL_TAC]) ORELSE
      (SUBGOAL_THEN (mk_neg b) (fun bth -> rw (EQF_INTRO bth)) THENL
        [H_COND_PROVE_TAC; ALL_TAC])
    else NO_TAC);;

let H_STEPS_TAC h l =
  MAP_EVERY (fun i -> ARM_STEPS_TAC (H_EXEC h) [i] THEN
                      TRY(H_DECIDE_TAC (H_SN i))) l;;

(*** The byte loop from join11 (X9 = word j0) at step n: 3 steps and the
     loop, then the final state ***)

let H_TV_BYTES_TAC h n j0 =
  let exec = H_EXEC h in
  H_STEPS_TAC h (n--(n+2)) THEN
  H_REG_TAC (H_SN (n+2)) `X10` (subst [j0,`j0:num`] `word(len - j0):int64`) THEN
  H_REG_TAC (H_SN (n+2)) `X8` (subst [j0,`j0:num`] `word_add (a:int64) (word(off + j0))`) THEN
  H_REG_TAC (H_SN (n+2)) `X9` (subst [j0,`j0:num`] `word_add (d:int64) (word j0)`) THEN
  H_PRE_TAC [subst [j0,`j0:num`] `j0 < len`] THEN
  H_SPEC_HYP "H_PTR" "H_PTR1"
   [`a:int64`; `d:int64`; `off:num`; `len:num`; j0; `S:1600 word`;
    `m:num`; `pc:num`] THEN
  H_CALL_TAC h "H_PTR1" (n+3) THEN
  H_FINAL_TAC (H_SN (n+3));;

(*** The 8-byte loop from join28 / join27 (X9 = word j0) at step n: 5
     steps, the loop of k blocks, the test; then the exit or the bytes ***)

let H_TV_DBLK_TAC h n j0 k =
  let exec = H_EXEC h in
  let sb = subst [j0,`j0:num`; k,`k:num`] in
  H_STEPS_TAC h (n--(n+4)) THEN
  H_REG_TAC (H_SN (n+4)) `X12` (sb `word_add (d:int64) (word j0)`) THEN
  H_REG_TAC (H_SN (n+4)) `X10` (sb `word_sub (word j0) (word(j0 + 8 * k)):int64`) THEN
  H_REG_TAC (H_SN (n+4)) `X11` (sb `word_add (a:int64) (word(off + j0))`) THEN
  H_PRE_TAC [sb `0 < k`; sb `j0 + 8 * k <= len`] THEN
  H_SPEC_HYP "H_D" "H_D1"
   [`a:int64`; `d:int64`; `off:num`; `len:num`; j0; k; `S:1600 word`;
    `m:num`; `pc:num`] THEN
  H_CALL_TAC h "H_D1" (n+5) THEN
  ASM_CASES_TAC `len MOD 8 = 0` THENL
   [SUBGOAL_THEN `8 * len DIV 8 = len` ASSUME_TAC THENL [H_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `8 * len DIV 8 = len`]) THEN
    H_STEPS_TAC h ((n+6)--(n+7)) THEN H_FINAL_TAC (H_SN (n+7));
    SUBGOAL_THEN `~(len = 8 * len DIV 8)` ASSUME_TAC THENL [H_ARITH_TAC; ALL_TAC] THEN
    H_STEPS_TAC h ((n+6)--(n+8)) THEN
    H_TV_BYTES_TAC h (n+9) `8 * len DIV 8`];;

let H_TV_VEC_TAC h n =
  let exec = H_EXEC h in
  ASM_CASES_TAC `len < 32` THENL
   [H_STEPS_TAC h (n--(n+3)) THEN
    H_TV_DBLK_TAC h (n+4) `0` `len DIV 8`;
    H_STEPS_TAC h (n--(n+6)) THEN
    H_REG_TAC (H_SN (n+6)) `X13` `word(32 * len DIV 32):int64` THEN
    H_PRE_TAC [`0 < len DIV 32`; `32 * len DIV 32 <= len`] THEN
    H_SPEC_HYP "H_Q" "H_Q1"
     [`a:int64`; `d:int64`; `off:num`; `len:num`; `0`; `len DIV 32`;
      `S:1600 word`; `m:num`; `pc:num`] THEN
    H_CALL_TAC h "H_Q1" (n+7) THEN
    ASM_CASES_TAC `len MOD 32 = 0` THENL
     [SUBGOAL_THEN `32 * len DIV 32 = len` ASSUME_TAC THENL [H_ARITH_TAC; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `32 * len DIV 32 = len`]) THEN
      H_STEPS_TAC h ((n+8)--(n+9)) THEN H_FINAL_TAC (H_SN (n+9));
      SUBGOAL_THEN `~(len = 32 * len DIV 32)` ASSUME_TAC THENL [H_ARITH_TAC; ALL_TAC] THEN
      H_CASE_LT8_TAC
        (H_STEPS_TAC h ((n+8)--(n+10)) THEN
        H_TV_BYTES_TAC h (n+11) `32 * len DIV 32`)
        (H_STEPS_TAC h ((n+8)--(n+10)) THEN
        H_TV_DBLK_TAC h (n+11) `32 * len DIV 32` `(len DIV 8) MOD 4`)]];;

(*** TVB: the byte loop from join10 / join19 ***)

let H_TVB_TAC h t =
  let exec = H_EXEC h in
  let dr = if t = 2 then h.d2 else h.d3 in
  let ptr = H_PTR h (H_TV_LOOPB t) "X9" "X8" "X10" "X11" "X12" in
  H_XR_SETUP h [ptr,"H_PTR"]
   `\(a:int64) (d:int64) (off:num) (len:num) (pc:num).
      f_ev_b a d off len pc:(uarch_event)list` THEN
  H_STEPS_TAC h (1--4) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_0; WORD_ADD_0]) THEN
  H_SPEC_HYP "H_PTR" "H_PTR0"
   [`a:int64`; `d:int64`; `off:num`; `len:num`; `0`; `S:1600 word`;
    `m:num`; `pc:num`] THEN
  H_CALL_TAC h "H_PTR0" 5 THEN
  H_FINAL_TAC "s5";;

(*** TVV: from the overlap test (join9 / join18) ***)

let H_TVV_TAC h t tmpl =
  let exec = H_EXEC h in
  let lb = H_TV_LOOPB t in
  let ptr = H_PTR h lb "X9" "X8" "X10" "X11" "X12" in
  let ql,dl = if t = 2 then h.t2q,h.t2d else h.t3q,h.t3d in
  let qlem = H_QL h ql "X12" "X11" "X13"
  and dlem = H_DL h dl "X12" "X11" "X10" in
  H_XR_SETUP h [ptr,"H_PTR"; qlem,"H_Q"; dlem,"H_D"] tmpl THEN
  H_LEN_FACTS_TAC THEN
  if t = 2 then
    H_STEPS_TAC h (1--5) THEN H_PC_SPLIT_TAC "s5" THENL
     [H_TV_VEC_TAC h 6;
      H_STEPS_TAC h (6--6) THEN H_TV_BYTES_TAC h 7 `0`]
  else
    H_STEPS_TAC h (1--3) THEN H_PC_SPLIT_TAC "s3" THENL
     [H_TV_VEC_TAC h 4;
      H_STEPS_TAC h (4--6) THEN H_PC_SPLIT_TAC "s6" THENL
       [H_TV_VEC_TAC h 7;
        H_STEPS_TAC h (7--7) THEN H_TV_BYTES_TAC h 8 `0`]];;

(* ------------------------------------------------------------------------- *)
(* The tail of the first absorb (T1), from join1 to join4: the XOR of the    *)
(* 0 < len < 136 bytes of in1 left after the blocks into the state at SP     *)
(* (off = 0). The byte loop is loop2, with an index (INLINE_XOR_BYTES_IDX),  *)
(* from join3 with X8 = word j0.                                             *)
(* ------------------------------------------------------------------------- *)

let H_T1_STMT h =
  H_XR_STMT h "join1" "join4" "off <= 0 /\\ 0 < len"
    (Printf.sprintf "read SP s = a /\\ read %s s = d /\\ read %s s = word len" h.d1 h.l1)
    (Printf.sprintf "read SP s = a /\\ read %s s = d /\\ read %s s = word len" h.d1 h.l1)
    ["X8"; "X9"; "X10"; "X11"; "X12"];;

(*** The byte loop from join3 (X8 = word j0) at step n: 1 step and the loop ***)

let H_T1_BYTES_TAC h n j0 =
  H_STEPS_TAC h (n--n) THEN
  H_REG_TAC (H_SN n) `X9` `word_add (a:int64) (word off)` THEN
  H_REG_TAC (H_SN n) `X8` (subst [j0,`j0:num`] `word j0:int64`) THEN
  H_PRE_TAC [subst [j0,`j0:num`] `j0 < len`] THEN
  H_SPEC_HYP "H_IDX" "H_IDX1"
   [`a:int64`; `d:int64`; `off:num`; `len:num`; j0; `S:1600 word`;
    `m:num`; `pc:num`] THEN
  H_CALL_TAC h "H_IDX1" (n+1) THEN
  H_FINAL_TAC (H_SN (n+1));;

(*** The 8-byte loop from join26 (X8 = word j0) at step n: 6 steps, the loop
     (D = X11, P = X10, C = X9), the test; then the exit or the bytes ***)

let H_T1_DBLK_TAC h n j0 k =
  let exec = H_EXEC h in
  let sb = subst [j0,`j0:num`; k,`k:num`] in
  H_STEPS_TAC h (n--(n+5)) THEN
  H_REG_TAC (H_SN (n+5)) `X11` (sb `word_add (d:int64) (word j0)`) THEN
  H_REG_TAC (H_SN (n+5)) `X9` (sb `word_sub (word j0) (word(j0 + 8 * k)):int64`) THEN
  H_REG_TAC (H_SN (n+5)) `X10` (sb `word_add (a:int64) (word(off + j0))`) THEN
  H_PRE_TAC [sb `0 < k`; sb `j0 + 8 * k <= len`] THEN
  H_SPEC_HYP "H_D" "H_D1"
   [`a:int64`; `d:int64`; `off:num`; `len:num`; j0; k; `S:1600 word`;
    `m:num`; `pc:num`] THEN
  H_CALL_TAC h "H_D1" (n+6) THEN
  ASM_CASES_TAC `len MOD 8 = 0` THENL
   [SUBGOAL_THEN `8 * len DIV 8 = len` ASSUME_TAC THENL [H_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `8 * len DIV 8 = len`]) THEN
    H_STEPS_TAC h ((n+7)--(n+8)) THEN H_FINAL_TAC (H_SN (n+8));
    SUBGOAL_THEN `~(len = 8 * len DIV 8)` ASSUME_TAC THENL [H_ARITH_TAC; ALL_TAC] THEN
    H_STEPS_TAC h ((n+7)--(n+9)) THEN
    H_T1_BYTES_TAC h (n+10) `8 * len DIV 8`];;

let H_T1_VEC_TAC h n =
  let exec = H_EXEC h in
  ASM_CASES_TAC `len < 32` THENL
   [H_STEPS_TAC h (n--(n+3)) THEN
    H_T1_DBLK_TAC h (n+4) `0` `len DIV 8`;
    H_STEPS_TAC h (n--(n+7)) THEN
    H_REG_TAC (H_SN (n+7)) `X12` `word(32 * len DIV 32):int64` THEN
    H_REG_TAC (H_SN (n+7)) `X10` `word_add (word_add (a:int64) (word off)) (word 16)` THEN
    H_PRE_TAC [`0 < len DIV 32`; `32 * len DIV 32 <= len`] THEN
    H_SPEC_HYP "H_Q" "H_Q1"
     [`a:int64`; `d:int64`; `off:num`; `len:num`; `0`; `len DIV 32`;
      `S:1600 word`; `m:num`; `pc:num`] THEN
    H_CALL_TAC h "H_Q1" (n+8) THEN
    ASM_CASES_TAC `len MOD 32 = 0` THENL
     [SUBGOAL_THEN `32 * len DIV 32 = len` ASSUME_TAC THENL [H_ARITH_TAC; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `32 * len DIV 32 = len`]) THEN
      H_STEPS_TAC h ((n+9)--(n+10)) THEN H_FINAL_TAC (H_SN (n+10));
      SUBGOAL_THEN `~(len = 32 * len DIV 32)` ASSUME_TAC THENL [H_ARITH_TAC; ALL_TAC] THEN
      H_CASE_LT8_TAC
        (H_STEPS_TAC h ((n+9)--(n+11)) THEN
        H_T1_BYTES_TAC h (n+12) `32 * len DIV 32`)
        (H_STEPS_TAC h ((n+9)--(n+11)) THEN
        H_T1_DBLK_TAC h (n+12) `32 * len DIV 32` `(len DIV 8) MOD 4`)]];;

let H_T1_TAC h tmpl =
  let exec = H_EXEC h in
  let idx = H_IDX h "loop2" h.d1 "X9" "X8" h.l1 "X10" "X11" in
  let qlem = H_QL h h.t1q "X11" "X10" "X12"
  and dlem = H_DL h h.t1d "X11" "X10" "X9" in
  H_XR_SETUP h [idx,"H_IDX"; qlem,"H_Q"; dlem,"H_D"] tmpl THEN
  H_LEN_FACTS_TAC THEN
  ASM_CASES_TAC `len < 8` THENL
   [H_STEPS_TAC h (1--3) THEN H_T1_BYTES_TAC h 4 `0`;
    H_STEPS_TAC h (1--8) THEN H_PC_SPLIT_TAC "s8" THENL
     [H_T1_VEC_TAC h 9;
      H_STEPS_TAC h (9--9) THEN H_T1_BYTES_TAC h 10 `0`]];;

(* ------------------------------------------------------------------------- *)
(* The XOR of one block of the second (F2) and third (F3) absorbs: len bytes *)
(* (0 < len <= 136, len = 136 - off for the first block, 136 for the later   *)
(* ones) at position off, from loop3 to join5 (F2) and from loop7 to join15  *)
(* (F3). F2 XORs 32-byte chunks with straight-line code (up to 4 of them for *)
(* 136 bytes), F3 with the loop loop8; then both use an 8-byte loop and a    *)
(* byte loop for the rest.                                                   *)
(* ------------------------------------------------------------------------- *)

let H_F_STMT h t =
  if t = 2 then
    let r = Printf.sprintf
      "read X8 s = word len /\\ read %s s = word off /\\ read %s s = d /\\ read %s s = a"
      h.l1 h.d2 h.d1 in
    H_XR_STMT h "loop3" "join5" "0 < len /\\ off + len <= 136" r r
      ["X9"; "X10"; "X11"; "X12"; "X13"]
  else
    let r = Printf.sprintf
      "read X8 s = word len /\\ read %s s = word off /\\ read %s s = d /\\ read %s s = a /\\ read %s s = word_add a (word 16)"
      h.l1 h.d3 h.l2 h.d2 in
    H_XR_STMT h "loop7" "join15" "0 < len /\\ off + len <= 136" r r
      ["X9"; "X10"; "X11"; "X12"; "X13"; "X14"];;

(*** The split form at the start, without simplification (for chunk 0) ***)

let H_START_RAW_TAC =
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) &&
       can (term_match [] `read (memory :> bytes(a:int64,200)) s = val(S:1600 word)`) (concl th)
    then
      let s = rand(lhand(concl th)) in
      MP_TAC(SPECL [`a:int64`; `S:1600 word`; `m:num`; `off:num`; s] XOR_START) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [SIMPLE_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
                      STRIP_TAC]
    else NO_TAC);;

(*** One 32-byte chunk c of F2 (0-based), whose first step is n: chunk 0
     has 9 steps (with the mask of X8 to X9 after the 4th), the others 7.
     sname is the state before the first step ***)

let H_F2_CHUNK_TAC h n c =
  let exec = H_EXEC h in
  let j = mk_small_numeral(32 * c) and j16 = mk_small_numeral(32 * c + 16)
  and jn = mk_small_numeral(32 * c + 32) in
  let p = mk_binop `(+):num->num->num` `off:num` j
  and p' = mk_binop `(+):num->num->num` `off:num` jn in
  let sname = H_SN (n - 1) in
  XOR_LOAD_FACTS_TAC sname p `len:num` [] [] [j; j16] THEN
  XOR_REST_TAC sname p p' THEN
  (if c = 0 then
     H_STEPS_TAC h (n--(n+3)) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `word_and (word len:int64) (word 224) =
                                         word(32 * len DIV 32)`]) THEN
     H_STEPS_TAC h ((n+4)--(n+8))
   else H_STEPS_TAC h (n--(n+6))) THEN
  XOR_STORE_TAC j 16 THEN XOR_STORE_TAC j16 16 THEN
  XOR_EXTEND_TAC j 16 j16 THEN XOR_EXTEND_TAC j16 16 jn;;

(*** The byte loop of F2 from join8 (X9 = word j0) at step n: 4 steps, the
     loop (D = X9, P = X11, C = X10), the branch to join5 ***)

let H_F2_BYTES_TAC h n j0 =
  let sb = subst [j0,`j0:num`] in
  H_STEPS_TAC h (n--(n+3)) THEN
  H_REG_TAC (H_SN (n+3)) `X10` (sb `word(len - j0):int64`) THEN
  H_REG_TAC (H_SN (n+3)) `X11` (sb `word_add (a:int64) (word(off + j0))`) THEN
  H_REG_TAC (H_SN (n+3)) `X9` (sb `word_add (d:int64) (word j0)`) THEN
  H_PRE_TAC [subst [j0,`j0:num`] `j0 < len`] THEN
  H_SPEC_HYP "H_PTR" "H_PTR1"
   [`a:int64`; `d:int64`; `off:num`; `len:num`; j0; `S:1600 word`;
    `m:num`; `pc:num`] THEN
  H_CALL_TAC h "H_PTR1" (n+4) THEN
  H_STEPS_TAC h ((n+5)--(n+5)) THEN
  H_FINAL_TAC (H_SN (n+5));;

(*** The 8-byte loop of F2 from join7 (X9 = word j0) at step n: 6 steps,
     the loop (D = X12, P = X11, C = X10), the test; the exit or the bytes ***)

let H_F2_DBLK_TAC h n j0 k =
  let sb = subst [j0,`j0:num`; k,`k:num`] in
  H_STEPS_TAC h (n--(n+5)) THEN
  H_REG_TAC (H_SN (n+5)) `X12` (sb `word_add (d:int64) (word j0)`) THEN
  H_REG_TAC (H_SN (n+5)) `X10` (sb `word_sub (word j0) (word(j0 + 8 * k)):int64`) THEN
  H_REG_TAC (H_SN (n+5)) `X11` (sb `word_add (a:int64) (word(off + j0))`) THEN
  H_PRE_TAC [sb `0 < k`; sb `j0 + 8 * k <= len`] THEN
  H_SPEC_HYP "H_D" "H_D1"
   [`a:int64`; `d:int64`; `off:num`; `len:num`; j0; k; `S:1600 word`;
    `m:num`; `pc:num`] THEN
  H_CALL_TAC h "H_D1" (n+6) THEN
  ASM_CASES_TAC `len MOD 8 = 0` THENL
   [SUBGOAL_THEN `8 * len DIV 8 = len` ASSUME_TAC THENL [H_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `8 * len DIV 8 = len`]) THEN
    H_STEPS_TAC h ((n+7)--(n+8)) THEN H_FINAL_TAC (H_SN (n+8));
    H_CONTRA_TAC THEN
    H_STEPS_TAC h ((n+7)--(n+8)) THEN
    H_F2_BYTES_TAC h (n+9) `8 * len DIV 8`];;

(*** k = len DIV 32 chunks from step 5, then the rest from join6 ***)

let H_F2_CHUNKS_TAC h k =
  let rec chunks c n =
    if c >= k then ALL_TAC
    else H_F2_CHUNK_TAC h n c THEN chunks (c + 1) (if c = 0 then n + 9 else n + 7) in
  let n = 7 * k + 7 in
  let kk = mk_small_numeral(32 * k) in
  let oK = mk_binop `(+):num->num->num` `off:num` kk in
  let eqk = mk_eq(`off + 32 * len DIV 32`,oK) in
  chunks 0 5 THEN
  SUBGOAL_THEN eqk ASSUME_TAC THENL [H_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `len MOD 32 = 0` THENL
   [SUBGOAL_THEN (mk_eq(oK,`off + len`))
      (fun eq -> RULE_ASSUM_TAC(REWRITE_RULE[eq])) THENL [H_ARITH_TAC; ALL_TAC] THEN
    H_STEPS_TAC h (n--(n+1)) THEN
    H_FINAL_TAC (H_SN (n+1));
    H_CASE_LT8_TAC
        (H_STEPS_TAC h (n--(n+3)) THEN
      H_F2_BYTES_TAC h (n+4) kk)
        (SUBGOAL_THEN (mk_eq(mk_binop `(+):num->num->num` kk `8 * (len DIV 8) MOD 4`,
                             `8 * len DIV 8`)) ASSUME_TAC THENL
          [H_ARITH_TAC; ALL_TAC] THEN
         H_STEPS_TAC h (n--(n+3)) THEN
      H_F2_DBLK_TAC h (n+4) kk `(len DIV 8) MOD 4`)];;

let H_F2_TAC h tmpl =
  let ptr = H_PTR h "loop5" "X9" "X11" "X10" "X12" "X13" in
  let dlem = H_DL h "loop4" "X12" "X11" "X10" in
  H_XR_SETUP h [ptr,"H_PTR"; dlem,"H_D"] tmpl THEN
  H_LEN_FACTS_TAC THEN
  ASM_CASES_TAC `len < 8` THENL
   [H_STEPS_TAC h (1--4) THEN H_F2_BYTES_TAC h 5 `0`;
    ASM_CASES_TAC `len < 32` THENL
     [H_STEPS_TAC h (1--6) THEN H_F2_DBLK_TAC h 7 `0` `len DIV 8`;
      H_STEPS_TAC h (1--4) THEN H_START_RAW_TAC THEN
      ASM_CASES_TAC `len DIV 32 = 1` THENL
       [H_F2_CHUNKS_TAC h 1;
        ASM_CASES_TAC `len DIV 32 = 2` THENL
         [H_F2_CHUNKS_TAC h 2;
          ASM_CASES_TAC `len DIV 32 = 3` THENL
           [H_F2_CHUNKS_TAC h 3;
            SUBGOAL_THEN `len DIV 32 = 4` ASSUME_TAC THENL
             [H_ARITH_TAC; H_F2_CHUNKS_TAC h 4]]]]]];;

(*** The byte loop of F3 from join17 (X10 = word j0) at step n: 4 steps, the
     loop (D = X10, P = X11, C = X9), the branch to join15 ***)

let H_F3_BYTES_TAC h n j0 =
  let sb = subst [j0,`j0:num`] in
  H_STEPS_TAC h (n--(n+3)) THEN
  H_REG_TAC (H_SN (n+3)) `X9` (sb `word(len - j0):int64`) THEN
  H_REG_TAC (H_SN (n+3)) `X11` (sb `word_add (a:int64) (word(off + j0))`) THEN
  H_REG_TAC (H_SN (n+3)) `X10` (sb `word_add (d:int64) (word j0)`) THEN
  H_PRE_TAC [subst [j0,`j0:num`] `j0 < len`] THEN
  H_SPEC_HYP "H_PTR" "H_PTR1"
   [`a:int64`; `d:int64`; `off:num`; `len:num`; j0; `S:1600 word`;
    `m:num`; `pc:num`] THEN
  H_CALL_TAC h "H_PTR1" (n+4) THEN
  H_STEPS_TAC h ((n+5)--(n+5)) THEN
  H_FINAL_TAC (H_SN (n+5));;

(*** The 8-byte loop of F3 from join16 (X10 = word j0) at step n: 6 steps,
     the loop (D = X13, P = X12, C = X11), the test; the exit or the bytes ***)

let H_F3_DBLK_TAC h n j0 k =
  let sb = subst [j0,`j0:num`; k,`k:num`] in
  H_STEPS_TAC h (n--(n+5)) THEN
  H_REG_TAC (H_SN (n+5)) `X13` (sb `word_add (d:int64) (word j0)`) THEN
  H_REG_TAC (H_SN (n+5)) `X11` (sb `word_sub (word j0) (word(j0 + 8 * k)):int64`) THEN
  H_REG_TAC (H_SN (n+5)) `X12` (sb `word_add (a:int64) (word(off + j0))`) THEN
  H_PRE_TAC [sb `0 < k`; sb `j0 + 8 * k <= len`] THEN
  H_SPEC_HYP "H_D" "H_D1"
   [`a:int64`; `d:int64`; `off:num`; `len:num`; j0; k; `S:1600 word`;
    `m:num`; `pc:num`] THEN
  H_CALL_TAC h "H_D1" (n+6) THEN
  ASM_CASES_TAC `len MOD 8 = 0` THENL
   [SUBGOAL_THEN `8 * len DIV 8 = len` ASSUME_TAC THENL [H_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `8 * len DIV 8 = len`]) THEN
    H_STEPS_TAC h ((n+7)--(n+8)) THEN H_FINAL_TAC (H_SN (n+8));
    H_STEPS_TAC h ((n+7)--(n+8)) THEN
    H_F3_BYTES_TAC h (n+9) `8 * len DIV 8`];;

let H_F3_FACTS_TAC =
  SUBGOAL_THEN `off < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `off + len <= 200` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> STRIP_ASSUME_TAC(MATCH_MP WORD_ZX_UXTW_SMALL th)) THEN
  SUBGOAL_THEN `val(word_zx (word off:int64):int32) = off` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `off MOD 18446744073709551616 = off` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `off < 2 EXP 32` THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `off < 2 EXP 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASSUME_TAC(MP (SPEC `len:num` WORD_AND_FFFFFFE0_64) (ASSUME `len < 2 EXP 32`)) THEN
  ASSUME_TAC(MP (SPEC `len:num` WORD_AND_FFFFFFF8_64) (ASSUME `len < 2 EXP 32`));;

let H_F3_TAC h tmpl =
  let ptr = H_PTR h "loop10" "X10" "X11" "X9" "X12" "X13" in
  let qlem = H_QL h "loop8" "X13" "X12" "X14"
  and dlem = H_DL h "loop9" "X13" "X12" "X11" in
  H_XR_SETUP h [ptr,"H_PTR"; qlem,"H_Q"; dlem,"H_D"] tmpl THEN
  H_LEN_FACTS_TAC THEN H_F3_FACTS_TAC THEN
  H_STEPS_TAC h (1--4) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `word_zx(word_zx(word off:int64):int32):int64 = word off`]) THEN
  ASM_CASES_TAC `len < 8` THENL
   [H_STEPS_TAC h (5--7) THEN H_F3_BYTES_TAC h 8 `0`;
    ASM_CASES_TAC `len < 32` THENL
     [H_STEPS_TAC h (5--9) THEN H_F3_DBLK_TAC h 10 `0` `len DIV 8`;
      H_STEPS_TAC h (5--12) THEN
      H_REG_TAC "s12" `X14` `word(32 * len DIV 32):int64` THEN
      H_REG_TAC "s12" `X12` `word_add (word_add (a:int64) (word off)) (word 16)` THEN
      H_PRE_TAC [`0 < len DIV 32`; `32 * len DIV 32 <= len`] THEN
    H_SPEC_HYP "H_Q" "H_Q1"
       [`a:int64`; `d:int64`; `off:num`; `len:num`; `0`; `len DIV 32`;
        `S:1600 word`; `m:num`; `pc:num`] THEN
      H_CALL_TAC h "H_Q1" 13 THEN
      ASM_CASES_TAC `len MOD 32 = 0` THENL
       [SUBGOAL_THEN `32 * len DIV 32 = len` ASSUME_TAC THENL [H_ARITH_TAC; ALL_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `32 * len DIV 32 = len`]) THEN
        H_STEPS_TAC h (14--15) THEN H_FINAL_TAC "s15";
        H_CASE_LT8_TAC
        (H_STEPS_TAC h (14--16) THEN H_F3_BYTES_TAC h 17 `32 * len DIV 32`)
        (H_STEPS_TAC h (14--16) THEN
          H_F3_DBLK_TAC h 17 `32 * len DIV 32` `(len DIV 8) MOD 4`)]]];;

(* ------------------------------------------------------------------------- *)
(* The loop over the full blocks of in1 (loop1), as SPONGE2_L1 of            *)
(* inline_sponge2.ml but with the state at the stack pointer (sp) instead of *)
(* sp + 64; the proof is that of SPONGE2_L1 with this address.               *)
(* ------------------------------------------------------------------------- *)

let H_L1_STMT h = parse_term(Printf.sprintf
 "exists f_events. forall e d mlen M n (S0:1600 word) sp pc.
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   aligned 16 sp /\\ mlen DIV 136 = n /\\ 0 < n /\\ mlen < 2 EXP 64 /\\
   nonoverlapping (d,mlen) (word_sub sp (word 240),440) /\\
   nonoverlapping (word pc,libmldsa_size) (word_sub sp (word 240),440)
   ==> ensures arm
    (\\s. aligned_bytes_loaded s (word pc) %s /\\
          read PC s = word (pc + %s) /\\ read SP s = sp /\\
          read %s s = d /\\ read %s s = word mlen /\\
          read (memory :> bytes(d,mlen)) s = M /\\
          read (memory :> wbytes sp) s = S0 /\\
          read events s = e)
    (\\s. read PC s = word (pc + %s) /\\ read SP s = sp /\\
          read %s s = word_add d (word (136 * n)) /\\
          read %s s = word (mlen - 136 * n) /\\
          read (memory :> bytes(d,mlen)) s = M /\\
          read (memory :> wbytes sp) s =
            mld_keccak_absorb_blocks 136 S0 M n /\\
          (exists e2. read events s = APPEND e2 e /\\
             e2 = f_events d mlen sp n pc /\\
             memaccess_inbounds e2
              [d,mlen; sp,200; word_sub sp (word 240),240;
               word(pc + rodata_mld_KeccakF_RoundConstants),192]
              [sp,200; word_sub sp (word 240),240]))
    (MAYCHANGE [PC; X30; %s; %s] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [X18] ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(sp,200);
                memory :> bytes(word_sub sp (word 240),240)])"
  H_MC (H_LAB h "loop1") h.d1 h.l1 (H_LAB h "loop1_exit") h.d1 h.l1 h.d1 h.l1);;

let H_L1_INV h = parse_term(Printf.sprintf
 "\\k s. read SP s = sp /\\
        read %s s = word_add d (word (136 * k)) /\\
        read %s s = word (mlen - 136 * k) /\\
        read (memory :> bytes(d,mlen)) s = M /\\
        read (memory :> wbytes sp) s =
          mld_keccak_absorb_blocks 136 S0 M k" h.d1 h.l1);;

let H_L1_STATE_FACTS_TAC =
  FIRST_ASSUM(fun xx ->
    if concl xx = `read (memory :> wbytes sp) (s0:armstate) = (XX:1600 word)` then
      MAP_EVERY (fun k ->
        let th = MP (SPECL [`sp:int64`; `XX:1600 word`;
                            mk_small_numeral k; `s0:armstate`]
                           SPONGE2_BYTES64_OF_WBYTES)
                    (CONJ xx (ARITH_RULE(mk_binop `(<):num->num->bool`
                                (mk_small_numeral k) `25`))) in
        let th = CONV_RULE (DEPTH_CONV NUM_MULT_CONV) th in
        ASSUME_TAC th THEN ASSUME_TAC (SPONGE2_NORMADDR th) THEN
        ASSUME_TAC (REWRITE_RULE[WORD_ADD_0] th)) (0--24)
    else NO_TAC);;

let H_L1_BODY h =
  let exec = H_EXEC h in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  SUBGOAL_THEN `136 * (i + 1) <= mlen` ASSUME_TAC THENL
   [SUBGOAL_THEN `i + 1 <= n` MP_TAC THENL
     [UNDISCH_TAC `i < n` THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `mlen DIV 136 = n` THEN
    MP_TAC(SPECL [`mlen:num`; `136`] DIVISION) THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `BLK = (M DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136)` THEN
  ABBREV_TAC `XX = mld_keccak_absorb_blocks 136 S0 M i` THEN
  SUBGOAL_THEN `BLK < 2 EXP 1088` ASSUME_TAC THENL
   [EXPAND_TAC "BLK" THEN REWRITE_TAC[ARITH_RULE `8 * 136 = 1088`; MOD_LT_EQ_LT] THEN
    REWRITE_TAC[ARITH_RULE `0 < 2 EXP 1088`]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes(word_add d (word (136 * i)),136)) s0 = BLK`
   ASSUME_TAC THENL
   [EXPAND_TAC "BLK" THEN REWRITE_TAC[ARITH_RULE `8 * 136 * i = 8 * (136 * i)`] THEN
    MATCH_MP_TAC SPONGE2_BYTES_SUB THEN EXISTS_TAC `mlen:num` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `136 * (i + 1) <= mlen` THEN ARITH_TAC;
    ALL_TAC] THEN
  SPONGE2_L1_BLOCK_FACTS_TAC THEN H_L1_STATE_FACTS_TAC THEN
  ARM_STEPS_TAC exec (1--48) THEN
  MAP_EVERY (fun k ->
    ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV)
      (MATCH_MP SPONGE2_SUBWORD_HI
        (CONJ (ASSUME `BLK < 2 EXP 1088`)
              (ARITH_RULE(mk_binop `(<=):num->num->bool` `17`
                                   (mk_small_numeral k))))))) (17--24) THEN
  SUBGOAL_THEN `read (memory :> wbytes sp) (s48:armstate) =
                word_xor (XX:1600 word) (word BLK:1600 word)` ASSUME_TAC THENL
   [MATCH_MP_TAC SPONGE2_WBYTES_OF_LANES THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    ASM_REWRITE_TAC[WORD_SUBWORD_XOR; SPONGE2_LANE_XOR; WORD_XOR_0] THEN
    TRY(REWRITE_TAC[WORD_XOR_SYM] THEN NO_TAC);
    ALL_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec "H_PERMUTE"
   [`sp:int64`; `word_xor (XX:1600 word) (word BLK:1600 word)`;
    `pc:num`; `sp:int64`; `read X30 s48`] SPONGE2_L1_VARS 49 THEN
  ARM_STEPS_TAC exec (50--51) THEN
  SUBGOAL_THEN `i + 1 <= n` ASSUME_TAC THENL
   [UNDISCH_TAC `i < n` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (mlen - 136 * i)) (word 136):int64 =
                word (mlen - 136 * (i + 1))` ASSUME_TAC THENL
   [MATCH_MP_TAC SPONGE2_L1_X24 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `word_sub (word (mlen - 136 * i)) (word 136):int64 =
                word (mlen - 136 * (i + 1))`]) THEN
  FIRST_ASSUM(fun th -> if concl th = `mlen < 2 EXP 64` then
    MP_TAC(MATCH_MP SPONGE2_L1_TEST
      (CONJ th (CONJ (ASSUME `mlen DIV 136 = n`) (ASSUME `i + 1 <= n`))))
    else NO_TAC) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let H_L1_TAC h =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (SPONGE2_RENAME_E2
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600)
   "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(d:int64) (mlen:num) (sp:int64) (n:num) (pc:num).
      APPEND (f_ev_epil d mlen sp n pc)
       (APPEND (ENUMERATEL n (\i. f_ev_loop d mlen sp n pc i))
               (f_ev_prol d mlen sp n pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `d:int64`; `mlen:num`; `M:num`; `n:num`;
    `S0:1600 word`; `sp:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES;
              ALL; fst (H_EXEC h)] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `n:num` (parse_term ("pc + " ^ H_LAB h "loop1"))
   (parse_term ("pc + " ^ H_LAB h "loop1_exit")) (H_L1_INV h) THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[mld_keccak_absorb_blocks; MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    H_L1_BODY h THEN SPONGE2_L1_FIN;
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC];;

let H_PROVE_L1 h = prove(H_L1_STMT h, H_L1_TAC h);;

(* ------------------------------------------------------------------------- *)
(* The templates of the events of the regions, by the paths. The conditions  *)
(* of the overlap tests are as the simulation gives them (the carry flag of  *)
(* the comparisons).                                                         *)
(* ------------------------------------------------------------------------- *)

let H_EV p = Printf.sprintf "f_ev_%s a d off len pc" p;;

let H_VEC_EV p = Printf.sprintf
  "(if len < 32 then (if len MOD 8 = 0 then %s else %s)
    else if len MOD 32 = 0 then %s
    else if len MOD 32 < 8 then %s
    else if len MOD 8 = 0 then %s else %s)"
  (H_EV (p^"1")) (H_EV (p^"2")) (H_EV (p^"3")) (H_EV (p^"4"))
  (H_EV (p^"5")) (H_EV (p^"6"));;

let H_TMPL body = parse_term(
  "\\(a:int64) (d:int64) (off:num) (len:num) (pc:num). (" ^ body ^ "):(uarch_event)list");;

(*** The overlap condition of the tail of the second absorb (and of T1) with
     the state pointer p (a term string) and the data d of len bytes ***)

let H_ALIAS2 p = Printf.sprintf
  "(if val (d:int64) < val (word_add (%s) (word len))
    then &(val (%s)) - &(val (word_add d (word len))) =
         &(val (word_sub (%s) (word_add d (word len)))):int
    else T)" p p p;;

let H_TV2_TMPL = H_TMPL(Printf.sprintf "if %s then %s else %s"
  (H_ALIAS2 "word_add (a:int64) (word off)") (H_VEC_EV "v") (H_EV "b"));;

let H_TVB_TMPL = H_TMPL(H_EV "b");;

let H_TV3_TMPL = H_TMPL(Printf.sprintf
  "if val (word_add (d:int64) (word len)) <= val (word_add (a:int64) (word off))
   then %s
   else if val (word_add (word_add (a:int64) (word off)) (word len)) <= val (d:int64)
   then %s else %s"
  (H_VEC_EV "v") (H_VEC_EV "w") (H_EV "b"));;

let H_T1_TMPL = H_TMPL(Printf.sprintf "if len < 8 then %s else if %s then %s else %s"
  (H_EV "s") (H_ALIAS2 "a:int64") (H_VEC_EV "v") (H_EV "b"));;

let H_F_TMPL t =
  let chunk k = Printf.sprintf
    "(if len MOD 32 = 0 then %s else if len MOD 32 < 8 then %s
      else if len MOD 8 = 0 then %s else %s)"
    (H_EV (Printf.sprintf "c%d0" k)) (H_EV (Printf.sprintf "c%d1" k))
    (H_EV (Printf.sprintf "c%d2" k)) (H_EV (Printf.sprintf "c%d3" k)) in
  if t = 2 then
    H_TMPL(Printf.sprintf
     "if len < 8 then %s else if len < 32 then (if len MOD 8 = 0 then %s else %s)
      else if len DIV 32 = 1 then %s else if len DIV 32 = 2 then %s
      else if len DIV 32 = 3 then %s else %s"
     (H_EV "b") (H_EV "d1") (H_EV "d2") (chunk 1) (chunk 2) (chunk 3) (chunk 4))
  else
    H_TMPL(Printf.sprintf "if len < 8 then %s else %s" (H_EV "b") (H_VEC_EV "v"));;

(*** The XOR regions of a function ***)

let H_PROVE_TVB h t = prove(H_TV_STMT h t false, H_TVB_TAC h t);;
let H_PROVE_TVV h t =
  prove(H_TV_STMT h t true,
        H_TVV_TAC h t (if t = 2 then H_TV2_TMPL else H_TV3_TMPL));;
let H_PROVE_T1 h = prove(H_T1_STMT h, H_T1_TAC h H_T1_TMPL);;
let H_PROVE_F h t =
  prove(H_F_STMT h t, (if t = 2 then H_F2_TAC else H_F3_TAC) h (H_F_TMPL t));;

(* ------------------------------------------------------------------------- *)
(* Absorbing at a position: the blocks of the stream 2^(8 pos) * M as the    *)
(* bytes of M that the code XORs (block 0 from byte pos on, the others whole) *)
(* and the state of mld_keccak_absorb from the blocks and the rest.          *)
(* ------------------------------------------------------------------------- *)

let H_BLOCK = prove
 (`!pos M i. pos <= 136
     ==> 2 EXP (8 * (pos - 136 * i)) *
         (M DIV 2 EXP (8 * (136 * i - pos))) MOD
         2 EXP (8 * (136 - (pos - 136 * i))) =
         ((2 EXP (8 * pos) * M) DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[MULT_CLAUSES; SUB_0; SUB_REFL; EXP; DIV_1] THEN
    SUBGOAL_THEN `2 EXP (8 * 136) = 2 EXP (8 * pos) * 2 EXP (8 * (136 - pos))`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MOD_MULT2];
    SUBGOAL_THEN `pos - 136 * i = 0` SUBST1_TAC THENL
     [UNDISCH_TAC `~(i = 0)` THEN UNDISCH_TAC `pos <= 136` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; EXP] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `2 EXP (8 * 136 * i) = 2 EXP (8 * pos) * 2 EXP (8 * (136 * i - pos))`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `~(i = 0)` THEN UNDISCH_TAC `pos <= 136` THEN ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ]]);;

let H_ABSORB_FST0 = prove
 (`!S pos len M. pos + len < 136 /\ M < 2 EXP (8 * len)
     ==> FST(mld_keccak_absorb 136 S pos len M) =
         word_xor S (word(2 EXP (8 * pos) * M))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_keccak_absorb] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[DIV_LT; mld_keccak_absorb_blocks; MULT_CLAUSES; EXP; DIV_1] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN
  TRANS_TAC LTE_TRANS `2 EXP (8 * pos) * 2 EXP (8 * len)` THEN
  ASM_REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD; LE_EXP] THEN
  ASM_ARITH_TAC);;

let H_ABSORB_FST1 = prove
 (`!S pos len M. pos < 136 /\ 136 <= pos + len /\ M < 2 EXP (8 * len)
     ==> FST(mld_keccak_absorb 136 S pos len M) =
         word_xor (mld_keccak_absorb_blocks 136 S (2 EXP (8 * pos) * M)
                    ((pos + len) DIV 136))
          (word((M DIV 2 EXP (8 * (136 * ((pos + len) DIV 136) - pos))) MOD
                2 EXP (8 * ((pos + len) MOD 136))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_keccak_absorb] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FST] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  ABBREV_TAC `N = (pos + len) DIV 136` THEN
  SUBGOAL_THEN `0 < N /\ 136 * N <= pos + len /\ pos + len < 136 * N + 136 /\
                (pos + len) MOD 136 = (pos + len) - 136 * N` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`pos + len`; `136`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    UNDISCH_TAC `136 <= pos + len` THEN EXPAND_TAC "N" THEN
    SIMP_TAC[DIV_EQ_0; ARITH_EQ; ARITH_RULE `0 < n <=> ~(n = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP (8 * 136 * N) = 2 EXP (8 * pos) * 2 EXP (8 * (136 * N - pos))`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `0 < N` THEN UNDISCH_TAC `pos < 136` THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ] THEN
  SUBGOAL_THEN `M DIV 2 EXP (8 * (136 * N - pos)) < 2 EXP (8 * ((pos + len) MOD 136))`
   ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    TRANS_TAC LTE_TRANS `2 EXP (8 * len)` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN MATCH_MP_TAC MOD_LT THEN
  TRANS_TAC LTE_TRANS `2 EXP (8 * ((pos + len) MOD 136))` THEN
  ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC);;

(*** The loop test after a block: b.ls on the length that is left ***)

let H_LS136 = prove
 (`!x. x < 2 EXP 64
       ==> ((135 <= val(word x:int64) /\ ~(val(word_sub (word x:int64) (word 135)) = 0)) <=>
            136 <= x)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; VAL_WORD_SUB_EQ_0] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop over the blocks of the second (t = 2: loop3) and third (t = 3:   *)
(* loop7) absorbs, when the input fills the block from pos on: N = (pos +    *)
(* len) DIV 136 >= 1 iterations, each the XOR of a block (F2 / F3: the       *)
(* 136 - pos bytes from pos on in the first, 136 bytes in the others) and    *)
(* the permutation. The position in iteration i is if i = 0 then pos else 0. *)
(* ------------------------------------------------------------------------- *)

let H_P_LAB t = if t = 2 then "loop3","loop3_exit" else "loop7","loop7_exit";;

let H_P_REGS h t =
  if t = 2 then h.d2,h.l2,Printf.sprintf "read %s s = sp" h.d1
  else h.d3,h.l3,
       Printf.sprintf "read %s s = sp /\\ read %s s = word_add sp (word 16)" h.l2 h.d2;;

let H_P_STMT h t =
  let lp,ex = H_P_LAB t in
  let dr,lr,sr = H_P_REGS h t in
  parse_term(Printf.sprintf
 "exists f_events. forall e d len M (S:1600 word) pos sp pc.
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   aligned 16 sp /\\ pos < 136 /\\ 136 <= pos + len /\\ len < 2 EXP 64 /\\
   nonoverlapping (d,len) (word_sub sp (word 240),440) /\\
   nonoverlapping (word pc,libmldsa_size) (word_sub sp (word 240),440)
   ==> ensures arm
    (\\s. aligned_bytes_loaded s (word pc) %s /\\
          read PC s = word (pc + %s) /\\ read SP s = sp /\\
          read X8 s = word (136 - pos) /\\ read %s s = word pos /\\
          read %s s = d /\\ read %s s = word len /\\ %s /\\
          read (memory :> bytes(d,len)) s = M /\\
          read (memory :> wbytes sp) s = S /\\
          read events s = e)
    (\\s. read PC s = word (pc + %s) /\\ read SP s = sp /\\
          read %s s = word 0 /\\
          read %s s = word_add d (word (136 * (pos + len) DIV 136 - pos)) /\\
          read %s s = word ((pos + len) MOD 136) /\\ %s /\\
          read (memory :> bytes(d,len)) s = M /\\
          read (memory :> wbytes sp) s =
            mld_keccak_absorb_blocks 136 S (2 EXP (8 * pos) * M)
              ((pos + len) DIV 136) /\\
          (exists e2. read events s = APPEND e2 e /\\
             e2 = f_events d len pos sp pc /\\
             memaccess_inbounds e2
              [d,len; sp,200; word_sub sp (word 240),240;
               word(pc + rodata_mld_KeccakF_RoundConstants),192]
              [sp,200; word_sub sp (word 240),240]))
    (MAYCHANGE [PC; X30; %s; %s; %s] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [X18] ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(sp,200);
                memory :> bytes(word_sub sp (word 240),240)])"
  H_MC (H_LAB h lp) h.l1 dr lr sr (H_LAB h ex) h.l1 dr lr sr h.l1 dr lr);;

let H_P_INV h t =
  let dr,lr,sr = H_P_REGS h t in
  parse_term(Printf.sprintf
 "\\i s. read SP s = sp /\\
        read X8 s = word (136 - (pos - 136 * i)) /\\
        read %s s = word (pos - 136 * i) /\\
        read %s s = word_add d (word (136 * i - pos)) /\\
        read %s s = word (len - (136 * i - pos)) /\\
        %s /\\
        read (memory :> bytes(d,len)) s = M /\\
        read (memory :> wbytes sp) s =
          mld_keccak_absorb_blocks 136 S (2 EXP (8 * pos) * M) i" h.l1 dr lr sr);;

let H_P_VARS = [`d:int64`; `len:num`; `pos:num`; `sp:int64`; `pc:num`; `i:num`];;

(*** Arithmetic on the iterations, by cases on i = 0 ***)

let H_P_ARITH_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    let c = concl th in
    String.length(string_of_term c) < 150 && H_IS_ARITH c))) THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
  MP_TAC(SPECL [`pos + len`; `136`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC;;

let H_P_BODY h t =
  let exec = H_EXEC h in
  let dr,lr,_ = H_P_REGS h t in
  let ot = `pos - 136 * i` in
  let c = `136 * i - pos` in
  let sbc = subst [c,`c:num`; ot,`oo:num`] in
  let rg r = mk_const(r,[]) in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  SUBGOAL_THEN `M < 2 EXP (8 * len)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = `M:num` &&
      can (term_match [] `read (memory :> bytes(d:int64,len)) s = M`) (concl th)
      then ACCEPT_TAC(MATCH_MP MLD_WRAP_READ_BYTES_BOUND th) else NO_TAC);
    ALL_TAC] THEN
  SUBGOAL_THEN (sbc
   `c + (136 - oo) <= len /\ 0 < 136 - oo /\ oo + (136 - oo) <= 136 /\
    oo + (136 - oo) <= 200 /\ 136 - oo <= len - c /\
    (len - c) - (136 - oo) = len - (136 * (i + 1) - pos) /\ pos - 136 * (i + 1) = 0 /\ 
    c + (136 - oo) = 136 * (i + 1) - pos /\
    (136 <= len - (136 * (i + 1) - pos) <=> i + 1 < (pos + len) DIV 136) /\
    len - (136 * (i + 1) - pos) < 2 EXP 64`)
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN H_P_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (sbc
   `read (memory :> bytes(word_add d (word c),136 - oo)) s0 =
    (M DIV 2 EXP (8 * c)) MOD 2 EXP (8 * (136 - oo))`) ASSUME_TAC THENL
   [MATCH_MP_TAC SPONGE2_BYTES_SUB THEN EXISTS_TAC `len:num` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> wbytes sp) s0 = x:1600 word`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th) else NO_TAC) THEN
  H_SPEC_HYP "H_F" "H_F1"
   [`sp:int64`; sbc `word_add (d:int64) (word c)`; ot; sbc `136 - oo`;
    `mld_keccak_absorb_blocks 136 S (2 EXP (8 * pos) * M) i`;
    sbc `(M DIV 2 EXP (8 * c)) MOD 2 EXP (8 * (136 - oo))`; `pc:num`] THEN
  H_FULL_CALL_TAC exec "H_F1" [] H_P_VARS 1 THEN
  MP_TAC(SPECL [`pos:num`; `M:num`; `i:num`] H_BLOCK) THEN
  ANTS_TAC THENL [UNDISCH_TAC `pos < 136` THEN ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes(sp:int64,200)) s1 = val(x:1600 word)`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600;
                                 ASSUME(rand(concl(SPECL [`pos:num`; `M:num`; `i:num`] H_BLOCK)))] th)
    else NO_TAC) THEN
  ARM_STEPS_TAC exec (2--5) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec "H_PERMUTE"
   [`sp:int64`;
    `word_xor (mld_keccak_absorb_blocks 136 S (2 EXP (8 * pos) * M) i)
       (word(((2 EXP (8 * pos) * M) DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136))):1600 word`;
    `pc:num`; `sp:int64`; `read X30 s5`] H_P_VARS 6 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(CONJUNCT2 mld_keccak_absorb_blocks); ADD1]) THEN
  ARM_STEPS_TAC exec (7--10) THEN
  SUBGOAL_THEN (sbc `word_sub (word (len - c)) (word (136 - oo)):int64 =
                     word (len - (136 * (i + 1) - pos))`) ASSUME_TAC THENL
   [ASM_SIMP_TAC[WORD_SUB2]; ALL_TAC] THEN
  SUBGOAL_THEN (sbc `word_add (word_add d (word c)) (word (136 - oo)):int64 =
                     word_add d (word (136 * (i + 1) - pos))`) ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ASSUME(sbc `word_sub (word (len - c)) (word (136 - oo)):int64 =
                word (len - (136 * (i + 1) - pos))`);
    ASSUME(sbc `word_add (word_add d (word c)) (word (136 - oo)):int64 =
                word_add d (word (136 * (i + 1) - pos))`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `len - (136 * (i + 1) - pos)` H_LS136)
       (ASSUME `len - (136 * (i + 1) - pos) < 2 EXP 64`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ASSUME `136 <= len - (136 * (i + 1) - pos) <=> i + 1 < (pos + len) DIV 136`]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[COND_SWAP; SUB_0] THEN
  REPEAT CONJ_TAC THEN
  FIRST [REWRITE_TAC[] THEN NO_TAC;
         COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC;
         MONOTONE_MAYCHANGE_TAC;
         SIGN_LOOP_DISCHARGE_TAC];;

let H_P_TAC h t flem =
  let exec = H_EXEC h in
  let lp,ex = H_P_LAB t in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (SPONGE2_RENAME_E2
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600)
   "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE2_RENAME_E2 flem) "H_F" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(d:int64) (len:num) (pos:num) (sp:int64) (pc:num).
      APPEND (f_ev_epil d len pos sp pc)
       (APPEND (ENUMERATEL ((pos + len) DIV 136)
                  (\i. f_ev_loop d len pos sp pc i))
               (f_ev_prol d len pos sp pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `d:int64`; `len:num`; `M:num`; `S:1600 word`;
    `pos:num`; `sp:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES;
              ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `(pos + len) DIV 136`
   (parse_term ("pc + " ^ H_LAB h lp)) (parse_term ("pc + " ^ H_LAB h ex))
   (H_P_INV h t) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`pos + len`; `136`] DIVISION) THEN
    REWRITE_TAC[ARITH_EQ] THEN ASM_ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[mld_keccak_absorb_blocks; MULT_CLAUSES; ADD_CLAUSES;
                    SUB_REFL; WORD_ADD_0; SUB_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    H_P_BODY h t;
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    SUBGOAL_THEN `1 <= (pos + len) DIV 136` ASSUME_TAC THENL
     [SIMP_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; DIV_EQ_0; ARITH_EQ] THEN
      UNDISCH_TAC `136 <= pos + len` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `pos - 136 * (pos + len) DIV 136 = 0 /\
                  len - (136 * (pos + len) DIV 136 - pos) = (pos + len) MOD 136`
      STRIP_ASSUME_TAC THENL
     [MP_TAC(SPECL [`pos + len`; `136`] DIVISION) THEN
      REWRITE_TAC[ARITH_EQ] THEN UNDISCH_TAC `1 <= (pos + len) DIV 136` THEN
      UNDISCH_TAC `pos < 136` THEN ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `pos - 136 * (pos + len) DIV 136 = 0`]) THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC];;

let H_PROVE_P h t flem = prove(H_P_STMT h t, H_P_TAC h t flem);;

(* ------------------------------------------------------------------------- *)
(* The second (t = 2, join4 to join14) and third (t = 3, join14 to join23)   *)
(* absorbs: the input of len bytes at position pos, as mld_keccak_absorb.    *)
(* Paths: len = 0 (nothing), pos + len < 136 (the tail at pos), and the      *)
(* blocks (H_P) followed by the tail of r = (pos + len) MOD 136 bytes at 0.  *)
(* ------------------------------------------------------------------------- *)

let H_A_LAB t = if t = 2 then "join4","join14" else "join14","join23";;

let H_A_REGS h t =
  if t = 2 then h.d2,h.l2,[h.l1; h.d1; h.d2; h.l2]
  else h.d3,h.l3,[h.l1; h.l2; h.d2; h.d3; h.l3];;

let H_A_STMT h t =
  let en,ex = H_A_LAB t in
  let dr,lr,ch = H_A_REGS h t in
  parse_term(Printf.sprintf
 "exists f_events. forall e d len M (S:1600 word) pos sp pc.
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   aligned 16 sp /\\ pos < 136 /\\ len < 2 EXP 64 /\\
   nonoverlapping (d,len) (word_sub sp (word 240),444) /\\
   nonoverlapping (word pc,libmldsa_size) (word_sub sp (word 240),444)
   ==> ensures arm
    (\\s. aligned_bytes_loaded s (word pc) %s /\\
          read PC s = word (pc + %s) /\\ read SP s = sp /\\
          read %s s = word pos /\\ read %s s = d /\\ read %s s = word len /\\
          read (memory :> bytes(d,len)) s = M /\\
          read (memory :> wbytes sp) s = S /\\
          read events s = e)
    (\\s. read PC s = word (pc + %s) /\\ read SP s = sp /\\
          read %s s = word ((pos + len) MOD 136) /\\
          read (memory :> wbytes sp) s = FST(mld_keccak_absorb 136 S pos len M) /\\
          (exists e2. read events s = APPEND e2 e /\\
             e2 = f_events d len pos sp pc /\\
             memaccess_inbounds e2
              [d,len; sp,204; word_sub sp (word 240),240;
               word(pc + rodata_mld_KeccakF_RoundConstants),192]
              [sp,204; word_sub sp (word 240),240]))
    (MAYCHANGE [PC; X30; %s] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [X18] ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(sp,204);
                memory :> bytes(word_sub sp (word 240),240)])"
  H_MC (H_LAB h en) h.l1 dr lr (H_LAB h ex) h.l1 (String.concat "; " ch));;

let H_A_VARS = [`d:int64`; `len:num`; `pos:num`; `sp:int64`; `pc:num`];;

let H_A_TMPL = parse_term
 "\\(d:int64) (len:num) (pos:num) (sp:int64) (pc:num).
    (if len < 1 then f_ev_z d len pos sp pc
     else if pos + len < 136 then
       (if len < 8 then f_ev_tb d len pos sp pc else f_ev_tv d len pos sp pc)
     else if (pos + len) MOD 136 = 0 then f_ev_b0 d len pos sp pc
     else if (pos + len) MOD 136 < 8 then f_ev_bb d len pos sp pc
     else f_ev_bv d len pos sp pc):(uarch_event)list";;

(*** The call of a tail region (TVB or TVV) with the state at sp, at step n ***)

let H_WB_TAC sname =
  TRY(FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> wbytes sp) s = x:1600 word`) (concl th) &&
                           rand(lhand(concl th)) = mk_var(sname,`:armstate`)
    then ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th) else NO_TAC)) THEN
  TRY(FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes(sp:int64,200)) s = val(x:1600 word)`) (concl th) &&
                           rand(lhand(concl th)) = mk_var(sname,`:armstate`)
    then ASSUME_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600] th) else NO_TAC));;

let H_A_TAIL_TAC h name d off len m sname n =
  H_PRE_TAC [subst [len,`l:num`] (if name = "H_TB" then `0 < l` else `8 <= l`);
             subst [off,`oo:num`; len,`l:num`] `oo + l <= 200`] THEN
  H_WB_TAC sname THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> wbytes sp) s = x:1600 word`) (concl th) &&
                           rand(lhand(concl th)) = mk_var(sname,`:armstate`)
    then
      let sv = rand(concl th) in
      H_SPEC_HYP name (name ^ "1") [`sp:int64`; d; off; len; sv; m; `pc:num`]
    else NO_TAC) THEN
  H_FULL_CALL_TAC (H_EXEC h) (name ^ "1") [] H_A_VARS n THEN
  H_WB_TAC (H_SN n);;

(*** The end: X23 from the 32-bit add, the state from the lemmas ***)

let H_SAFE_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  (CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]) THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  REPEAT CONJ_TAC THEN DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

let H_A_END_TAC sname fst_th =
  H_WB_TAC sname THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [REWRITE_TAC[fst_th] THEN
         REWRITE_TAC[EXP; MULT_CLAUSES; ADD_CLAUSES; WORD_XOR_0; MOD_1] THEN
         ASM_REWRITE_TAC[] THEN NO_TAC;
         MONOTONE_MAYCHANGE_TAC;
         H_SAFE_TAC;
         DISCHARGE_SAFETY_PROPERTY_TAC];;

(*** The proof of the absorb lemma, from the lemmas for the blocks (plem) and
     the tails (tvb, tvv) of the function ***)

let H_A_TAC h t plem tvb tvv =
  let exec = H_EXEC h in
  let k0 = if t = 2 then 1 else 0 in
  let dr,lr,_ = H_A_REGS h t in
  let lreg = mk_const(lr,[]) and preg = mk_const(h.l1,[]) in
  let rd r n = list_mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            [r; mk_var(H_SN n,`:armstate`)]) in
  (*** after a tail lemma at step n: add w23, w23, wLEN; str; the end ***)
  let tail_end n p r fst_th =
    H_STEPS_TAC h ((n+1)--(n+2)) THEN
    H_REG_TAC (H_SN (n+2)) preg (subst [p,`p:num`; r,`r:num`] `word(p + r):int64`) THEN
    H_A_END_TAC (H_SN (n+2)) fst_th in
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE2_RENAME_E2 plem) "H_P" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE2_RENAME_E2 tvb) "H_TB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE2_RENAME_E2 tvv) "H_TV" THEN
  CONCRETIZE_F_EVENTS_TAC H_A_TMPL THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `d:int64`; `len:num`; `M:num`; `S:1600 word`;
    `pos:num`; `sp:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES;
              ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> wbytes sp) s0 = x:1600 word`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th) else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes(d:int64,len)) s = M`) (concl th) &&
                           rand(concl th) = `M:num`
    then ASSUME_TAC(MATCH_MP MLD_WRAP_READ_BYTES_BOUND th) else NO_TAC) THEN
  SUBGOAL_THEN `val(word len:int64) = len` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  SUBGOAL_THEN `pos < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `pos < 136` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> STRIP_ASSUME_TAC(MATCH_MP WORD_ZX_UXTW_SMALL th)) THEN
  ASM_CASES_TAC `len < 1` THENL
   [(*** Nothing to absorb ***)
    SUBGOAL_THEN `M = 0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `M < 2 EXP (8 * len)` THEN
      SUBGOAL_THEN `len = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      ALL_TAC] THEN
    H_STEPS_TAC h (1--(1+k0)) THEN
    MP_TAC(SPECL [`S:1600 word`; `pos:num`; `len:num`; `0`] H_ABSORB_FST0) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[EXP_LT_0; ARITH_EQ] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `(pos + len) MOD 136 = pos` ASSUME_TAC THENL
     [SUBGOAL_THEN `len = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ADD_CLAUSES] THEN MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    H_A_END_TAC (H_SN (1+k0)) (ASSUME `FST(mld_keccak_absorb 136 S pos len 0) =
                                       word_xor S (word(2 EXP (8 * pos) * 0))`);
    ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word 136) (word pos):int64 = word(136 - pos) /\
                word_zx(word_sub (word 136:int32) (word_zx (word pos:int64))):int64 =
                word(136 - pos) /\
                val(word(136 - pos):int64) = 136 - pos`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WORD_SUB2 THEN ASM_ARITH_TAC;
      MATCH_MP_TAC H_W32_SUB136 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `pos + len < 136` THENL
   [(*** The tail at pos: TVB or TVV at a = sp, off = pos ***)
    MP_TAC(SPECL [`S:1600 word`; `pos:num`; `len:num`; `M:num`] H_ABSORB_FST0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `(pos + len) MOD 136 = pos + len` ASSUME_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `len < 8` THENL
     [H_STEPS_TAC h (1--(10+k0)) THEN
      H_REG_TAC (H_SN (10+k0)) `X8` `word_add (sp:int64) (word pos)` THEN
      H_A_TAIL_TAC h "H_TB" `d:int64` `pos:num` `len:num` `M:num`
        (H_SN (10+k0)) (11+k0) THEN
      tail_end (11+k0) `pos:num` `len:num`
        (ASSUME `FST(mld_keccak_absorb 136 S pos len M) =
                 word_xor S (word(2 EXP (8 * pos) * M))`);
      H_STEPS_TAC h (1--(9+k0)) THEN
      H_REG_TAC (H_SN (9+k0)) `X8` `word_add (sp:int64) (word pos)` THEN
      H_A_TAIL_TAC h "H_TV" `d:int64` `pos:num` `len:num` `M:num`
        (H_SN (9+k0)) (10+k0) THEN
      tail_end (10+k0) `pos:num` `len:num`
        (ASSUME `FST(mld_keccak_absorb 136 S pos len M) =
                 word_xor S (word(2 EXP (8 * pos) * M))`)];
    ALL_TAC] THEN
  (*** The blocks, then the rest r at 0 ***)
  SUBGOAL_THEN `136 <= pos + len` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`S:1600 word`; `pos:num`; `len:num`; `M:num`] H_ABSORB_FST1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  H_STEPS_TAC h (1--8) THEN
  H_WB_TAC "s8" THEN
  H_SPEC_HYP "H_P" "H_P1"
   [`d:int64`; `len:num`; `M:num`; `S:1600 word`; `pos:num`; `sp:int64`; `pc:num`] THEN
  H_FULL_CALL_TAC exec "H_P1" [] H_A_VARS 9 THEN
  H_WB_TAC "s9" THEN
  SUBGOAL_THEN `((pos + len) MOD 136) < 136 /\ 136 * (pos + len) DIV 136 - pos + ((pos + len) MOD 136) = len /\
                val(word ((pos + len) MOD 136):int64) = ((pos + len) MOD 136)`
   STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`pos + len`; `136`] DIVISION) THEN
    REWRITE_TAC[ARITH_EQ] THEN
    SUBGOAL_THEN `1 <= (pos + len) DIV 136` MP_TAC THENL
     [SIMP_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; DIV_EQ_0; ARITH_EQ] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `pos < 136` THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; ARITH_RULE `x < 136 ==> x < 2 EXP 64`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes(word_add d (word (136 * (pos + len) DIV 136 - pos)),((pos + len) MOD 136))) s9 =
                (M DIV 2 EXP (8 * (136 * (pos + len) DIV 136 - pos))) MOD 2 EXP (8 * ((pos + len) MOD 136))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC SPONGE2_BYTES_SUB THEN EXISTS_TAC `len:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(pos + len) MOD 136 = 0` THENL
   [H_STEPS_TAC h (10--12) THEN
    H_A_END_TAC "s12" (ASSUME `FST(mld_keccak_absorb 136 S pos len M) =
        word_xor (mld_keccak_absorb_blocks 136 S (2 EXP (8 * pos) * M) ((pos + len) DIV 136))
         (word((M DIV 2 EXP (8 * (136 * (pos + len) DIV 136 - pos))) MOD 2 EXP (8 * (pos + len) MOD 136)))`);
    ALL_TAC] THEN
  ASM_CASES_TAC `((pos + len) MOD 136) < 8` THEN
  H_STEPS_TAC h (10--14) THEN
  H_REG_TAC "s14" `X8` `word_add (sp:int64) (word 0)` THENL
   [H_A_TAIL_TAC h "H_TB" `word_add (d:int64) (word (136 * (pos + len) DIV 136 - pos))`
      `0` `(pos + len) MOD 136` `(M DIV 2 EXP (8 * (136 * (pos + len) DIV 136 - pos))) MOD 2 EXP (8 * ((pos + len) MOD 136))`
      "s14" 15;
    H_A_TAIL_TAC h "H_TV" `word_add (d:int64) (word (136 * (pos + len) DIV 136 - pos))`
      `0` `(pos + len) MOD 136` `(M DIV 2 EXP (8 * (136 * (pos + len) DIV 136 - pos))) MOD 2 EXP (8 * ((pos + len) MOD 136))`
      "s14" 15] THEN
  tail_end 15 `0` `(pos + len) MOD 136`
    (ASSUME `FST(mld_keccak_absorb 136 S pos len M) =
        word_xor (mld_keccak_absorb_blocks 136 S (2 EXP (8 * pos) * M) ((pos + len) DIV 136))
         (word((M DIV 2 EXP (8 * (136 * (pos + len) DIV 136 - pos))) MOD 2 EXP (8 * ((pos + len) MOD 136))))`);;

let H_PROVE_A h t plem tvb tvv = prove(H_A_STMT h t, H_A_TAC h t plem tvb tvv);;

(* ------------------------------------------------------------------------- *)
(* The padding (from join23): 0x1f XORed at byte r of the state and 0x80 at  *)
(* byte 135, and 136 stored as the position, as SPONGE2_FIN of              *)
(* inline_sponge2.ml but with the state at sp and without the permutation.   *)
(* mld_H44/65 then branch to the squeezing loop (loop12, 12 steps), mld_H87  *)
(* is at the call of the permutation (in_shake256_finalize_end, 10 steps).   *)
(* The registers it sets: X25 = sp, X24 = 0, X26 = X23 = 136 (H44), X20 = X0 *)
(* = sp, X9 = 136 (H87).                                                     *)
(* ------------------------------------------------------------------------- *)

let H_FIN_INFO h =
  if h.hf = "mld_H87" then
    "in_shake256_finalize_end", 10, 4,
    "read X20 s = sp /\\ read X0 s = sp /\\ read X9 s = word 136",
    ["X0"; "X8"; "X9"; "X20"]
  else
    "loop12", 12, 4,
    "read X25 s = sp /\\ read X24 s = word 0 /\\ read X26 s = word 136 /\\ read X23 s = word 136",
    ["X8"; "X23"; "X24"; "X25"; "X26"];;

let H_FIN_STMT h =
  let ex,_,_,regs,ch = H_FIN_INFO h in
  parse_term(Printf.sprintf
 "exists f_events. forall e (S1:1600 word) r sp pc.
   r < 136 /\\ aligned 16 sp /\\ aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (sp,204) (word pc,libmldsa_size)
   ==> ensures arm
    (\\s. aligned_bytes_loaded s (word pc) %s /\\
          read PC s = word (pc + %s) /\\ read SP s = sp /\\
          read %s s = word r /\\
          read (memory :> wbytes sp) s = S1 /\\
          read events s = e)
    (\\s. read PC s = word (pc + %s) /\\ read SP s = sp /\\ %s /\\
          read (memory :> wbytes sp) s = mld_keccak_finalize 136 31 S1 r /\\
          (exists e2. read events s = APPEND e2 e /\\
             e2 = f_events r sp pc /\\
             memaccess_inbounds e2 [sp,204] [sp,204]))
    (MAYCHANGE [PC; %s] ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(sp,204)])"
  H_MC (H_LAB h "join23") h.l1 (H_LAB h ex) regs (String.concat "; " ch));;

let H_FIN_ST = `read (memory :> bytes(sp,200)) (s0:armstate) = val (S1:1600 word)`;;

let H_FIN_BYTES_PIECE k l =
  FIRST_ASSUM(fun th -> if concl th = H_FIN_ST then
    let side = SPONGE2_PIECE_SIDE
      (mk_binop `(<=):num->num->bool` (mk_binop `(+):num->num->num` k l) `200`) in
    let f = MP (SPECL [`sp:int64`; `200`; `val(S1:1600 word)`;
                       k; l; `s0:armstate`] SPONGE2_BYTES_SUB) (CONJ th side) in
    ASSUME_TAC f THEN ASSUME_TAC (SPONGE2_NORMADDR f)
  else NO_TAC);;

let H_FIN_BYTE_PIECE k def =
  FIRST_ASSUM(fun th -> if concl th = H_FIN_ST then
    let side = SPONGE2_PIECE_SIDE (mk_binop `(<):num->num->bool` k `200`) in
    let f = MP (SPECL [`sp:int64`; `200`; `val(S1:1600 word)`;
                       k; `s0:armstate`] READ_MEMORY_BYTES8_OF_NUM) (CONJ th side) in
    FIRST_ASSUM(fun d -> if concl d = def then
      let f = REWRITE_RULE[d] f in
      let f = CONV_RULE(DEPTH_CONV NUM_MULT_CONV) f in
      ASSUME_TAC f THEN ASSUME_TAC (SPONGE2_NORMADDR f)
      else NO_TAC)
  else NO_TAC);;

let H_FIN_STATE_TAC sn =
  MP_TAC(SPECL [`sp:int64`; `S1:1600 word`; mk_var(sn,`:armstate`)] SPONGE2_PAD135) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPONGE2_HIGH_MOD]) THEN SPONGE2_FIN_NORM_TAC THEN
  FIRST_ASSUM(fun d -> if concl d = `word((val(S1:1600 word) DIV 2 EXP (8 * 135)) MOD 256):byte = b135` then REWRITE_TAC[d] else NO_TAC) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC];;

let H_FIN_STATE2_TAC sn =
  MP_TAC(SPECL [`sp:int64`; `S1:1600 word`; `r:num`; mk_var(sn,`:armstate`)] SPONGE2_PAD1) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPONGE2_HIGH_MOD]) THEN SPONGE2_FIN_NORM_TAC THEN
  FIRST_ASSUM(fun d -> if concl d = `word((val(S1:1600 word) DIV 2 EXP (8 * r)) MOD 256):byte = b1` then REWRITE_TAC[d] else NO_TAC) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  MP_TAC(SPECL [`sp:int64`;
                `word_xor S1 (word (2 EXP (8 * r) * 31)):1600 word`;
                mk_var(sn,`:armstate`)] SPONGE2_PAD2) THEN
  SPONGE2_FIN_NORM_TAC THEN
  FIRST_ASSUM(fun d -> if is_eq(concl d) && is_binary "MOD" (lhs(concl d)) &&
      can (find_term (fun t -> t = `word_xor:1600 word->1600 word->1600 word`)) (concl d)
    then REWRITE_TAC[d] else NO_TAC) THEN
  FIRST_ASSUM(fun d -> if concl d = `word((val(S1:1600 word) DIV 2 EXP (8 * 135)) MOD 256):byte = b135` then REWRITE_TAC[d] else NO_TAC) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC];;

let H_FIN_END_TAC sn rt =
  let sb = vsubst [rt,`r:num`] in
  SUBGOAL_THEN (subst [mk_var(sn,`:armstate`),`s:armstate`]
                 (sb `read (memory :> wbytes sp) (s:armstate) =
                      mld_keccak_finalize 136 31 (S1:1600 word) r`)) ASSUME_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_1600; mld_keccak_finalize; ARITH_RULE `136 - 1 = 135`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [REWRITE_TAC[] THEN NO_TAC; MONOTONE_MAYCHANGE_TAC;
         DISCHARGE_SAFETY_PROPERTY_TAC];;

let H_FIN_TAC h =
  let exec = H_EXEC h in
  let _,n,_,_,_ = H_FIN_INFO h in
  let sn = H_SN n in
  CONCRETIZE_F_EVENTS_TAC
   `\(r:num) (sp:int64) (pc:num).
      if r = 135 then f_ev_a r sp pc else f_ev_b r sp pc
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `S1:1600 word`; `r:num`; `sp:int64`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN H_FIN_ST ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `read (memory :> wbytes sp) (s0:armstate) = (S1:1600 word)` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[READ_MEMORY_WBYTES_1600]; ALL_TAC] THEN
  SUBGOAL_THEN `r < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `r < 136` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> STRIP_ASSUME_TAC(MATCH_MP WORD_ZX_UXTW_SMALL th)) THEN
  ABBREV_TAC `b135 = word((val(S1:1600 word) DIV 2 EXP (8 * 135)) MOD 256):byte` THEN
  ASM_CASES_TAC `r = 135` THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `r = 135` then SUBST_ALL_TAC th else NO_TAC) THEN
    REWRITE_TAC[] THEN
    H_FIN_BYTES_PIECE `0` `135` THEN H_FIN_BYTES_PIECE `136` `64` THEN
    H_FIN_BYTE_PIECE `135` `word((val(S1:1600 word) DIV 2 EXP (8 * 135)) MOD 256):byte = b135` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `8 * 0 = 0`; EXP; DIV_1; WORD_ADD_0]) THEN
    ARM_STEPS_TAC exec (1--n) THEN
    SPONGE2_CHAIN_FIX_TAC sn "word_add sp (word 135)" `b135:byte`
      (fun b -> mk_comb(mk_comb(`word_xor:byte->byte->byte`,
         mk_comb(mk_comb(`word_xor:byte->byte->byte`,b),`word 31:byte`)),`word 128:byte`)) THEN
    H_FIN_STATE_TAC sn THEN
    H_FIN_END_TAC sn `135`;
    SUBGOAL_THEN `r < 135` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `b1 = word((val(S1:1600 word) DIV 2 EXP (8 * r)) MOD 256):byte` THEN
    H_FIN_BYTES_PIECE `0` `r:num` THEN H_FIN_BYTES_PIECE `r + 1` `134 - r` THEN
    H_FIN_BYTES_PIECE `136` `64` THEN
    H_FIN_BYTE_PIECE `135` `word((val(S1:1600 word) DIV 2 EXP (8 * 135)) MOD 256):byte = b135` THEN
    H_FIN_BYTE_PIECE `r:num` `word((val(S1:1600 word) DIV 2 EXP (8 * r)) MOD 256):byte = b1` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `8 * 0 = 0`; EXP; DIV_1; WORD_ADD_0]) THEN
    ARM_STEPS_TAC exec (1--n) THEN
    SPONGE2_CHAIN_FIX_TAC sn "word_add sp (word r)" `b1:byte`
      (fun b -> mk_comb(mk_comb(`word_xor:byte->byte->byte`,b),`word 31:byte`)) THEN
    SPONGE2_CHAIN_FIX_TAC sn "word_add sp (word 135)" `b135:byte`
      (fun b -> mk_comb(mk_comb(`word_xor:byte->byte->byte`,b),`word 128:byte`)) THEN
    H_FIN_STATE2_TAC sn THEN
    H_FIN_END_TAC sn `r:num`];;

let H_PROVE_FIN h = prove(H_FIN_STMT h, H_FIN_TAC h);;

(* ------------------------------------------------------------------------- *)
(* The squeezing loop of mld_H44/65 (loop12 to loop12_exit): per iteration   *)
(* the permutation and a memcpy of l = MIN (outlen - 136 * i) 136 bytes of   *)
(* the state to out + 136 * i, N = MAX 1 ((outlen + 135) DIV 136) times     *)
(* (the code permutes and calls memcpy for 0 bytes when outlen = 0).         *)
(* ------------------------------------------------------------------------- *)

let H_SQ_N = `MAX 1 ((outlen + 135) DIV 136)`;;

let H_SQ_STMT h = parse_term(Printf.sprintf
 "!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> exists f_events.
      forall e out outlen (S0:1600 word) sp pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 sp /\\ outlen < 2 EXP 64 /\\
        ALLPAIRS nonoverlapping [(out,outlen); (word_sub sp (word 240),440)]
          [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)] /\\
        nonoverlapping (out,outlen) (word_sub sp (word 240),440)
        ==> ensures arm
          (\\s. aligned_bytes_loaded s (word pc) %s /\\
                read PC s = word (pc + %s) /\\
                read SP s = sp /\\ read X19 s = word outlen /\\ read X20 s = out /\\
                read X23 s = word 136 /\\ read X24 s = word 0 /\\
                read X25 s = sp /\\ read X26 s = word 136 /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> wbytes sp) s = S0 /\\
                read events s = e)
          (\\s. read PC s = word (pc + %s) /\\
                read SP s = sp /\\ read X20 s = out /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq (mld_keccak_squeeze_byte 136 S0 136) outlen) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events out outlen sp mc pc /\\
                   memaccess_inbounds e2
                    [out,outlen; sp,200; word_sub sp (word 240),240;
                     word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192]
                    [out,outlen; sp,200; word_sub sp (word 240),240]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
           MAYCHANGE [X19; X21; X22; X24; X26] ,,
           MAYCHANGE [memory :> bytes(out,outlen); memory :> bytes(sp,200);
                      memory :> bytes(word_sub sp (word 240),240)])"
  H_MC (H_LAB h "loop12") (H_LAB h "loop12_exit"));;

let H_SQ_INV = parse_term
 "\\i s. read SP s = sp /\\ read X19 s = word(outlen - 136 * i) /\\
        read X20 s = out /\\ read X23 s = word 136 /\\
        read X24 s = word(MIN (136 * i) outlen) /\\
        read X25 s = sp /\\
        (i < MAX 1 ((outlen + 135) DIV 136) ==> read X26 s = word 136) /\\
        read (memory :> bytes64(word_add (word pc) (word got_memcpy))) s = mc /\\
        read (memory :> bytes(ea,el)) s = ev /\\
        read (memory :> wbytes sp) s = keccak_squeeze i S0 /\\
        read (memory :> bytes(out,MIN (136 * i) outlen)) s =
          num_of_bytelist
           (list_of_seq (mld_keccak_squeeze_byte 136 S0 136) (MIN (136 * i) outlen))";;

let H_SQ_VARS = [`out:int64`; `outlen:num`; `sp:int64`; `mc:int64`; `pc:num`; `i:num`];;

(*** The first l bytes of a state ***)

let H_FIRST_BYTES = prove
 (`!(a:int64) (X:1600 word) l s:armstate.
     read (memory :> wbytes a) s = X /\ l <= 200
     ==> read (memory :> bytes(a,l)) s = val X MOD 2 EXP (8 * l)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[READ_MEMORY_WBYTES_1600]) ASSUME_TAC) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD] THEN
  ASM_SIMP_TAC[ARITH_RULE `l <= 200 ==> MIN 200 l = l`]);;

let H_SQ_SUC = prove(`!(S:1600 word) i. keccak_f1600 (keccak_squeeze i S) = keccak_squeeze (i + 1) S`,
  REWRITE_TAC[GSYM ADD1; keccak_squeeze]);;

(*** The bytes of the output after block i ***)

let H_SQ_EXT = prove
 (`!(out:int64) (S0:1600 word) i l outlen s:armstate.
     136 * i < outlen \/ i = 0 ==>
     l = MIN (outlen - 136 * i) 136 ==>
     read (memory :> bytes(out,MIN (136 * i) outlen)) s =
       num_of_bytelist(list_of_seq (mld_keccak_squeeze_byte 136 S0 136) (MIN (136 * i) outlen)) /\
     read (memory :> bytes(word_add out (word (136 * i)),l)) s =
       val(keccak_squeeze (i + 1) S0) MOD 2 EXP (8 * l)
     ==> read (memory :> bytes(out,MIN (136 * (i + 1)) outlen)) s =
         num_of_bytelist(list_of_seq (mld_keccak_squeeze_byte 136 S0 136)
                          (MIN (136 * (i + 1)) outlen))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `MIN (136 * i) outlen = 136 * i /\
                MIN (136 * (i + 1)) outlen = 136 * i + MIN (outlen - 136 * i) 136`
   (CONJUNCTS_THEN (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th])) THENL
   [UNDISCH_TAC `136 * i < outlen \/ i = 0` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`136`; `S0:1600 word`; `136`; `136 * i`; `i + 1`; `0`;
                `MIN (outlen - 136 * i) 136`] SQUEEZE_CHUNK) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXP; MULT_CLAUSES; DIV_1] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REFL_TAC);;

(*** The calls of the contract of memcpy, with the events unified ***)

let H_LEFTASSOC_CONV = TRY_CONV(CONS_TO_APPEND_CONV) THENC REWRITE_CONV[APPEND_ASSOC];;
let H_E2_CORE allowed =
  CONV_TAC(LAND_CONV H_LEFTASSOC_CONV) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SAFE_UNIFY_REFL_TAC allowed (ref ["f_events_callee"; "f_ev_"]);;
let H_E2_ANY_TAC allowed =
  REPEAT(CONJ_TAC THENL [H_ADDR_EQ_TAC; ALL_TAC]) THEN
  (FULL_EXISTS_E2_TAC allowed ORELSE H_E2_CORE allowed);;
let H_LIBC_CALL_TAC name execth ilist vars n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true execth th ilist n THENL
     [H_E2_ANY_TAC (ref vars); LABEL_TAC name th]);;

let H_NOV tm =
  SUBGOAL_THEN tm (fun th -> ASSUME_TAC th THEN
                             ASSUME_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES] th)) THENL
   [NONOVERLAPPING_TAC; ALL_TAC];;

let H_SQ_ARITH = prove
 (`!outlen i. outlen < 2 EXP 64 /\ i < MAX 1 ((outlen + 135) DIV 136)
    ==> (136 * i < outlen \/ i = 0) /\
        MIN (136 * i) outlen = 136 * i /\
        MIN (outlen - 136 * i) 136 <= 200 /\
        136 * i + MIN (outlen - 136 * i) 136 <= outlen /\
        (if val(word(outlen - 136 * i):int64) < 136 then word(outlen - 136 * i)
         else word 136):int64 = word(MIN (outlen - 136 * i) 136) /\
        word_sub (word(outlen - 136 * i)) (word(MIN (outlen - 136 * i) 136)):int64 =
          word(outlen - 136 * (i + 1)) /\
        (val(word(outlen - 136 * (i + 1)):int64) = 0 <=>
         ~(i + 1 < MAX 1 ((outlen + 135) DIV 136))) /\
        word_add (word(MIN (outlen - 136 * i) 136)) (word(136 * i)):int64 =
          word(MIN (136 * (i + 1)) outlen) /\
        (i + 1 < MAX 1 ((outlen + 135) DIV 136)
         ==> MIN (outlen - 136 * i) 136 = 136)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `136 * i < outlen \/ i = 0` ASSUME_TAC THENL
   [MP_TAC(SPECL [`outlen + 135`; `136`] DIVISION) THEN
    UNDISCH_TAC `i < MAX 1 ((outlen + 135) DIV 136)` THEN
    REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(i + 1 < MAX 1 ((outlen + 135) DIV 136) <=> 136 * (i + 1) < outlen)`
   ASSUME_TAC THENL
   [MP_TAC(SPECL [`outlen + 135`; `136`] DIVISION) THEN
    UNDISCH_TAC `i < MAX 1 ((outlen + 135) DIV 136)` THEN
    REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x <= outlen ==> val(word x:int64) = x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
    REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  FIRST
   [FIRST_ASSUM ACCEPT_TAC;
    ASM_ARITH_TAC;
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ARITH_RULE `outlen - 136 * i <= outlen`)]) THEN
    COND_CASES_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    SIMP_TAC[WORD_SUB2; ARITH_RULE `MIN a b <= a`] THEN AP_TERM_TAC THEN ARITH_TAC;
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ARITH_RULE `outlen - 136 * (i + 1) <= outlen`)]) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;

let H_SQ_BODY_TAC h =
  let exec = H_EXEC h in
  let l = `MIN (outlen - 136 * i) 136` in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN FULL_INIT_TAC THEN
  MP_TAC(SPECL [`outlen:num`; `i:num`] H_SQ_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[];
                  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))] THEN
  RULE_ASSUM_TAC(fun th ->
    if concl th = `MIN (136 * i) outlen = 136 * i` then th
    else REWRITE_RULE[ASSUME `MIN (136 * i) outlen = 136 * i`;
                      ASSUME `i < MAX 1 ((outlen + 135) DIV 136)`] th) THEN
  SUBGOAL_THEN `val(word(MIN (outlen - 136 * i) 136):int64) = MIN (outlen - 136 * i) 136`
   ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC exec (1--5) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec "H_PERM"
   [`sp:int64`; `keccak_squeeze i (S0:1600 word)`; `pc:num`; `sp:int64`; `read X30 s5`]
   H_SQ_VARS 6 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[H_SQ_SUC]) THEN
  H_WB_TAC "s6" THEN
  FIRST_X_ASSUM(fun th -> if can (term_match [] `read (memory :> wbytes sp) s6 = x:1600 word`) (concl th)
    then ASSUME_TAC th THEN
         ASSUME_TAC(MP (SPECL [`sp:int64`; rand(concl th); l; `s6:armstate`] H_FIRST_BYTES)
                       (CONJ th (ASSUME(subst [l,`l:num`] `l <= 200`))))
    else NO_TAC) THEN
  ARM_STEPS_TAC exec (7--14) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ASSUME `(if val(word(outlen - 136 * i):int64) < 136 then word(outlen - 136 * i)
             else word 136):int64 = word(MIN (outlen - 136 * i) 136)`]) THEN
  LIBC_PLT_TAC exec 14 THEN
  MAP_EVERY H_NOV
   [`nonoverlapping (word_add out (word (136 * i)):int64,MIN (outlen - 136 * i) 136) (sp,200)`;
    `nonoverlapping (word_add out (word (136 * i)):int64,MIN (outlen - 136 * i) 136)
                    (word_add (word pc) (word got_memcpy),8)`;
    `nonoverlapping (word_add out (word (136 * i)):int64,MIN (outlen - 136 * i) 136)
                    (out,136 * i)`;
    `nonoverlapping (word_add out (word (136 * i)):int64,MIN (outlen - 136 * i) 136) (ea,el)`] THEN
  H_LIBC_CALL_TAC "H_MEMCPY" exec
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `val(keccak_squeeze (i + 1) (S0:1600 word)) MOD 2 EXP (8 * MIN (outlen - 136 * i) 136)`;
    `read X30 s`] H_SQ_VARS 19 THEN
  ARM_STEPS_TAC exec (20--23) THEN
  H_WB_TAC "s23" THEN
  MP_TAC(SPECL [`out:int64`; `S0:1600 word`; `i:num`; l; `outlen:num`; `s23:armstate`] H_SQ_EXT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ASSUME `word_sub (word(outlen - 136 * i)) (word(MIN (outlen - 136 * i) 136)):int64 =
            word(outlen - 136 * (i + 1))`;
    ASSUME `word_add (word(MIN (outlen - 136 * i) 136)) (word(136 * i)):int64 =
            word(MIN (136 * (i + 1)) outlen)`;
    ASSUME `(val(word(outlen - 136 * (i + 1)):int64) = 0 <=>
             ~(i + 1 < MAX 1 ((outlen + 135) DIV 136)))`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `MAX 1 ((outlen + 135) DIV 136) <= i + 1 <=>
                                           ~(i + 1 < MAX 1 ((outlen + 135) DIV 136))`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[COND_SWAP] THEN
  ASM_CASES_TAC `i + 1 < MAX 1 ((outlen + 135) DIV 136)` THEN
  TRY(SUBGOAL_THEN `MIN (outlen - 136 * i) 136 = 136`
       (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
      [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> concl th =
         `i + 1 < MAX 1 ((outlen + 135) DIV 136) ==> MIN (outlen - 136 * i) 136 = 136`)) THEN
       FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [REWRITE_TAC[] THEN NO_TAC;
         ASM_REWRITE_TAC[] THEN NO_TAC;
         CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         MONOTONE_MAYCHANGE_TAC;
         REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
         ASM_REWRITE_TAC[] THEN H_SAFE_TAC;
         H_SAFE_TAC;
         SIGN_LOOP_DISCHARGE_TAC];;

let H_SQ_TAC h =
  let exec = H_EXEC h in
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[memcpy_full_contract] th) "H_MEMCPY") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(out:int64) (outlen:num) (sp:int64) (mc:int64) (pc:num).
      APPEND (f_ev_epil out outlen sp mc pc)
       (APPEND (ENUMERATEL (MAX 1 ((outlen + 135) DIV 136))
                  (\i. if i + 1 < MAX 1 ((outlen + 135) DIV 136)
                       then f_ev_c out outlen sp mc pc i
                       else f_ev_l out outlen sp mc pc i))
               (f_ev_prol out outlen sp mc pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `out:int64`; `outlen:num`; `S0:1600 word`;
    `sp:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(fun th -> (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) th THEN
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)(REWRITE_RULE[NONOVERLAPPING_CLAUSES; fst exec] th)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `MAX 1 ((outlen + 135) DIV 136)`
   (parse_term ("pc + " ^ H_LAB h "loop12")) (parse_term ("pc + " ^ H_LAB h "loop12_exit"))
   H_SQ_INV THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; ARITH_RULE `MIN 0 n = 0`; keccak_squeeze;
                CONJUNCT1 ENUMERATEL; CONJUNCT1 APPEND; list_of_seq;
                num_of_bytelist; READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    H_SQ_BODY_TAC h;
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    SUBGOAL_THEN `MIN (136 * MAX 1 ((outlen + 135) DIV 136)) outlen = outlen`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [MP_TAC(SPECL [`outlen + 135`; `136`] DIVISION) THEN
      REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC];;

let H_PROVE_SQ h = prove(H_SQ_STMT h, H_SQ_TAC h);;

(* ------------------------------------------------------------------------- *)
(* The first absorb (from in_shake256_absorb_1_part2, the b.cc on the test   *)
(* of in1len < 136, to join4): the blocks of 136 bytes (H_L1), then the tail *)
(* of the r = len MOD 136 bytes left (H_T1) unless r = 0, into the zero      *)
(* state. The code has no test for len = 0 when len < 136 (see the spec).    *)
(* ------------------------------------------------------------------------- *)

let H_A1_STMT h = parse_term(Printf.sprintf
 "exists f_events. forall e d len M sp pc.
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   aligned 16 sp /\\ ~(len = 0) /\\ len < 2 EXP 64 /\\
   nonoverlapping (d,len) (word_sub sp (word 240),440) /\\
   nonoverlapping (word pc,libmldsa_size) (word_sub sp (word 240),440)
   ==> ensures arm
    (\\s. aligned_bytes_loaded s (word pc) %s /\\
          read PC s = word (pc + %s) /\\ read SP s = sp /\\
          read %s s = d /\\ read %s s = word len /\\
          (read CF s <=> 136 <= len) /\\
          read (memory :> bytes(d,len)) s = M /\\
          read (memory :> wbytes sp) s = (word 0:1600 word) /\\
          read events s = e)
    (\\s. read PC s = word (pc + %s) /\\ read SP s = sp /\\
          read %s s = word (len MOD 136) /\\
          read (memory :> wbytes sp) s = FST(mld_keccak_absorb 136 (word 0) 0 len M) /\\
          (exists e2. read events s = APPEND e2 e /\\
             e2 = f_events d len sp pc /\\
             memaccess_inbounds e2
              [d,len; sp,200; word_sub sp (word 240),240;
               word(pc + rodata_mld_KeccakF_RoundConstants),192]
              [sp,200; word_sub sp (word 240),240]))
    (MAYCHANGE [PC; X30; %s; %s] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [X18] ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(sp,200);
                memory :> bytes(word_sub sp (word 240),240)])"
  H_MC (H_LAB h "in_shake256_absorb_1_part2") h.d1 h.l1 (H_LAB h "join4")
  h.l1 h.d1 h.l1);;

let H_A1_VARS = [`d:int64`; `len:num`; `sp:int64`; `pc:num`];;

let H_A1_TAC h l1lem t1lem =
  let exec = H_EXEC h in
  let tcall d len m n =
    FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> wbytes sp) s = x:1600 word`) (concl th) &&
                             rand(lhand(concl th)) = mk_var(H_SN (n-1),`:armstate`)
      then
        let sv = rand(concl th) in
        ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th) THEN
        H_SPEC_HYP "H_T1" "H_T11" [`sp:int64`; d; `0`; len; sv; m; `pc:num`]
      else NO_TAC) THEN
    H_FULL_CALL_TAC exec "H_T11" [] H_A1_VARS n THEN
    FIRST_X_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes(sp:int64,200)) s = val(x:1600 word)`) (concl th) &&
                               rand(lhand(concl th)) = mk_var(H_SN n,`:armstate`)
      then ASSUME_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600] th) else NO_TAC) in
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE2_RENAME_E2 l1lem) "H_L1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE2_RENAME_E2 t1lem) "H_T1" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(d:int64) (len:num) (sp:int64) (pc:num).
      (if len < 136 then f_ev_s d len sp pc
       else if len MOD 136 = 0 then f_ev_b0 d len sp pc
       else f_ev_bt d len sp pc):(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `d:int64`; `len:num`; `M:num`; `sp:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES;
              ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes(d:int64,len)) s = M`) (concl th) &&
                           rand(concl th) = `M:num`
    then ASSUME_TAC(MATCH_MP MLD_WRAP_READ_BYTES_BOUND th) else NO_TAC) THEN
  ASM_CASES_TAC `len < 136` THENL
   [SUBGOAL_THEN `~(136 <= len)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`word 0:1600 word`; `0`; `len:num`; `M:num`] H_ABSORB_FST0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ADD_CLAUSES]; DISCH_TAC] THEN
    SUBGOAL_THEN `len MOD 136 = len` ASSUME_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `0 <= 0 /\ 0 < len /\ len <= 200` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    H_STEPS_TAC h (1--1) THEN
    tcall `d:int64` `len:num` `M:num` 2 THEN
    H_A_END_TAC "s2" (ASSUME `FST(mld_keccak_absorb 136 (word 0) 0 len M) =
                              word_xor (word 0) (word(2 EXP (8 * 0) * M))`);
    ALL_TAC] THEN
  SUBGOAL_THEN `136 <= len /\ 0 < len DIV 136 /\ 0 + len < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`; DIV_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`word 0:1600 word`; `0`; `len:num`; `M:num`] H_ABSORB_FST1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ADD_CLAUSES; ARITH]; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES; EXP; SUB_0]) THEN
  H_STEPS_TAC h (1--1) THEN
  H_SPEC_HYP "H_L1" "H_L11"
   [`d:int64`; `len:num`; `M:num`; `len DIV 136`; `word 0:1600 word`; `sp:int64`; `pc:num`] THEN
  H_FULL_CALL_TAC exec "H_L11" [] H_A1_VARS 2 THEN
  SUBGOAL_THEN `len - 136 * len DIV 136 = len MOD 136 /\ len MOD 136 < 136 /\
                136 * len DIV 136 + len MOD 136 = len`
   STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`len:num`; `136`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `len - 136 * len DIV 136 = len MOD 136`]) THEN
  SUBGOAL_THEN `val(word(len MOD 136):int64) = len MOD 136` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `len MOD 136 = 0` THENL
   [H_STEPS_TAC h (3--3) THEN
    H_A_END_TAC "s3" (ASSUME `FST(mld_keccak_absorb 136 (word 0) 0 len M) =
        word_xor (mld_keccak_absorb_blocks 136 (word 0) M (len DIV 136))
         (word((M DIV 2 EXP (8 * 136 * len DIV 136)) MOD 2 EXP (8 * len MOD 136)))`);
    ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes(word_add d (word (136 * len DIV 136)),len MOD 136)) s2 =
                (M DIV 2 EXP (8 * 136 * len DIV 136)) MOD 2 EXP (8 * len MOD 136)`
   ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8 * 136 * n = 8 * (136 * n)`] THEN
    MATCH_MP_TAC SPONGE2_BYTES_SUB THEN EXISTS_TAC `len:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `0 <= 0 /\ 0 < len MOD 136 /\ len MOD 136 <= 200` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  H_STEPS_TAC h (3--3) THEN
  tcall `word_add (d:int64) (word (136 * len DIV 136))` `len MOD 136`
        `(M DIV 2 EXP (8 * 136 * len DIV 136)) MOD 2 EXP (8 * len MOD 136)` 4 THEN
  H_A_END_TAC "s4" (ASSUME `FST(mld_keccak_absorb 136 (word 0) 0 len M) =
        word_xor (mld_keccak_absorb_blocks 136 (word 0) M (len DIV 136))
         (word((M DIV 2 EXP (8 * 136 * len DIV 136)) MOD 2 EXP (8 * len MOD 136)))`);;

let H_PROVE_A1 h l1lem t1lem = prove(H_A1_STMT h, H_A1_TAC h l1lem t1lem);;
