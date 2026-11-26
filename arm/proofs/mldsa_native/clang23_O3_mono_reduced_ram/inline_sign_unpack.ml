(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the unpacking loops that clang 23 -O3 has inlined into         *)
(* mldsa{44,65,87}_verify_internal and signature_internal (see inline_sign.ml *)
(* and inline_sign_pack.ml for the conventions): polyt1_unpack.              *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_pack.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_pwm.ml";;

(*** The final tactic of CHUNK_FULL_FINAL_TAC, where the spec function takes ***)
(*** the group of the coefficient with a division by a number other than the ***)
(*** number of coefficients of an iteration (polyt1: 4 coefficients per five ***)
(*** bytes, 16 per iteration): extra rewrites the indices into numerals.     ***)

let INLINE_CHUNK_FINAL_TAC fdef (x:term) (extra:thm list) (ptrs:thm list)
                           (events:string list list) =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC ptrs THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT; CHUNK_OUTPUT_SPLIT_1] THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      REWRITE_TAC[fdef] THEN
      REWRITE_TAC extra THEN
      SIMP_TAC[DIVMOD_CHUNK; ARITH] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN APP_BLAST_TAC x THEN
      NO_TAC) THEN
  INLINE_EVENT_TAC events THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let INLINE_DIV4_16 = prove
 (`!i k. (16 * i + k) DIV 4 = 4 * i + k DIV 4`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `16 * i + k = (4 * i) * 4 + k`] THEN
  REWRITE_TAC[DIV_MULT_ADD; ARITH_RULE `~(4 = 0)`] THEN
  SIMP_TAC[ADD_CLAUSES; DIV_MULT; ARITH_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ARITH_TAC);;

let INLINE_MOD4_16 = prove
 (`!i k. (16 * i + k) MOD 4 = k MOD 4`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `16 * i + k = (4 * i) * 4 + k`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

(* ------------------------------------------------------------------------- *)
(* The result of ST4 of four vectors of four 32-bit lanes, as the model has  *)
(* it: word_interleave 32 [v0; v1; v2; v3] of 512 bits. Its 32-bit lane n is *)
(* lane n DIV 4 of the vector n MOD 4; the library evaluates                 *)
(* word_interleave only of literals, so the lanes are rewritten with the     *)
(* lemma for each n.                                                         *)
(* ------------------------------------------------------------------------- *)

let INLINE_INTERLEAVE4_LANE = prove
 (`!a b c d:int128 n. n < 16
    ==> word_subword (word_interleave 32 [a;b;c;d]:int512) (32 * n,32):int32 =
        word_subword (EL (n MOD 4) [a;b;c;d]) (32 * (n DIV 4),32)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; DIMINDEX_32] THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `MIN 32 32 = 32`] THEN
  REWRITE_TAC[word_interleave] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH; ARITH] THEN
  MP_TAC(SPECL [`32`;`n:num`;`r:num`] DIVMOD_CHUNK) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:512)`] THEN
  SUBGOAL_THEN `32 * n + r < 512` (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

let INLINE_INTERLEAVE4_LANES =
  map (fun n ->
    let nt = mk_small_numeral n in
    let th = INST [nt,`n:num`] (SPEC_ALL INLINE_INTERLEAVE4_LANE) in
    let th = MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))) in
    GENL [`a:int128`;`b:int128`;`c:int128`;`d:int128`]
     (CONV_RULE(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_MOD_CONV ORELSEC
                           NUM_DIV_CONV) THENC
                DEPTH_CONV EL_CONV) th)) (0--15);;

(*** The facts about 32-bit lanes of a 128-bit store of the result of ST4 ***)

let INLINE_ST4_LANES_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> is_const t && fst(dest_const t) = "word_interleave"))
           (concl th)
    then REWRITE_RULE INLINE_INTERLEAVE4_LANES
           (CONV_RULE(SIMD_SIMPLIFY_CONV []) th)
    else th);;


(* ------------------------------------------------------------------------- *)
(* polyt1_unpack (shape 42, 3 instances), in verify_internal: 20 bytes of    *)
(* the input and 16 coefficients per iteration (byte loads, lane inserts,    *)
(* USHL and TBL to spread the bytes, ST4 of four vectors), 16 iterations.    *)
(* The input pointer is a + 19 at the head (the loop reads at -19 .. 0), the *)
(* output pointer r and the offset 64 * i.                                   *)
(*                                                                           *)
(* The vector registers that the loop reads and does not write are Q22       *)
(* (0xff in the low byte of each lane), Q21 and Q20 (the TBL indices) and    *)
(* the low 64 bits of Q8 (the shifts of USHL), as constants from the image.  *)
(* The high 64 bits of Q8 are an arbitrary h8: the callers keep only d8 (the *)
(* low half) across their calls, as the ABI lets the callees change the      *)
(* rest.                                                                     *)
(* The loop inserts bytes into the lanes of Q6 without having defined it,    *)
(* which the lemma treats as an unknown value q6 (the bytes of it that the   *)
(* loop reads are masked).                                                   *)
(* ------------------------------------------------------------------------- *)

let INLINE_T1_ALIASES =
  List.concat(map (fun m ->
    let k = 19 - m in
    let old = if k = 0 then "word_add a (word (20 * i))"
              else Printf.sprintf "word_add a (word (20 * i + %d))" k in
    [Printf.sprintf "word_add a (word ((20 * i + 19) + %s)):int64 = %s"
       (string_of_num (((Num.num_of_int 2) **/ (Num.num_of_int 64)) -/
                       (Num.num_of_int m))) old;
     Printf.sprintf "word_add a (word_sub (word (20 * i + 19)) (word %d)):int64 = %s"
       m old]) (1--19));;

let INLINE_T1_EVENTS =
  [List.concat(map (fun m ->
    let k = 19 - m in
    let old = if k = 0 then "word_add a (word (20 * i))"
              else Printf.sprintf "word_add a (word (20 * i + %d))" k in
    [Printf.sprintf "word_add (word_add a (word (20 * i + 19))) (word %s):int64 = %s"
       (string_of_num (((Num.num_of_int 2) **/ (Num.num_of_int 64)) -/
                       (Num.num_of_int m))) old;
     Printf.sprintf "word_sub (word_add a (word (20 * i + 19))) (word %d):int64 = %s"
       m old;
     Printf.sprintf "word_add a (word_sub (word (20 * i + 19)) (word %d)):int64 = %s"
       m old]) (1--19))];;

let INLINE_POLYT1_LOOP_TERM mc loop exit (xin,xout,xoff) (qmask,qi1,qi0,qsh)
                            (mods:string list) =
  INLINE_STMT mc loop exit "r a (b:num->byte) (h8:int64)" 320 1024
   (Printf.sprintf
     "read %s s = word_add a (word 19) /\\ read %s s = r /\\
      read %s s = word 0 /\\
      read %s s = word 0x000000ff000000ff000000ff000000ff /\\
      read %s s = word 0xffffff07ffffff06ffffff05ffffff04 /\\
      read %s s = word 0xffffff03ffffff02ffffff01ffffff00 /\\
      read %s s = word_join (h8:int64) (word 0xfafafafafcfcfcfc:int64):int128 /\\
      (!j. j < 320 ==> read(memory :> bytes8(word_add a (word j))) s = b j)"
     xin xout xoff qmask qi1 qi0 qsh)
   (Printf.sprintf
     "read %s s = word_add a (word 339) /\\ read %s s = word 1024 /\\
      (!i. i < 256
           ==> read(memory :> bytes32(word_add r (word(4 * i)))) s =
               mld_polyt1_unpack b i)" xin xoff)
   mods;;

let INLINE_POLYT1_LOOP mc exec loop exit (xin,xout,xoff) (qmask,qi1,qi0,qsh)
                       (mods:string list) =
  INLINE_CHUNK_PROVE
   (INLINE_POLYT1_LOOP_TERM mc loop exit (xin,xout,xoff)
      (qmask,qi1,qi0,qsh) mods)
   "(r:int64) (a:int64)" "r a"
   ["r:int64"; "a:int64"; "b:num->byte"; "h8:int64"; "pc:num"]
   16 exec loop exit
   (Printf.sprintf
     "\\i s. read %s s = word_add a (word (20 * i + 19)) /\\
            read %s s = r /\\ read %s s = word (64 * i) /\\
            read %s s = word 0x000000ff000000ff000000ff000000ff /\\
            read %s s = word 0xffffff07ffffff06ffffff05ffffff04 /\\
            read %s s = word 0xffffff03ffffff02ffffff01ffffff00 /\\
            read %s s = word_join (h8:int64) (word 0xfafafafafcfcfcfc:int64):int128 /\\
            (!j. j < 320
                 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
            (!j. j < 16 * i
                 ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                     mld_polyt1_unpack b j)"
     xin xout xoff qmask qi1 qi0 qsh)
   (CHUNK_INPUT_TAC `b:num->byte` 20 THEN
    INLINE_ALIAS_TAC INLINE_T1_ALIASES THEN
    SUBGOAL_THEN `?q6:int128. read Q6 s0 = q6` (X_CHOOSE_TAC `q6:int128`) THENL
     [EXISTS_TAC `read Q6 s0:int128` THEN REFL_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC exec (1--88) THEN
    WIDE_STORE_SPLIT_TAC `r:int64` 32 THEN INLINE_ST4_LANES_TAC THEN
    INLINE_CHUNK_FINAL_TAC mld_polyt1_unpack `b:num->byte`
      [INLINE_DIV4_16; INLINE_MOD4_16]
      [ARITH_RULE `64 * (i + 1) = 64 * i + 64`;
       ARITH_RULE `20 * (i + 1) + 19 = (20 * i + 19) + 20`]
      INLINE_T1_EVENTS);;

(*** The instances of polyt1_unpack: function, head, exit, the scalar  ***)
(*** registers (input pointer, output base, offset), the vector        ***)
(*** registers of the constants (mask, indices of the second and the   ***)
(*** first TBL, shifts)                                                ***)

let INLINE_POLYT1_MODS =
  ["X0";"X1";"X2";"X8";"X9";"X10";"X11";"X12";"X13";"X14";"X15";"X16";"X17";
   "X18";"Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7";"Q16";"Q17";"Q18";"Q19"];;

let INLINE_POLYT1_INSTANCES =
 ["mldsa44_verify_internal", "mldsa44_verify_internal_loop7",
  "mldsa44_verify_internal_loop7_exit",
  ("X9","X27","X8"), ("Q22","Q21","Q20","Q8");
  "mldsa65_verify_internal", "mldsa65_verify_internal_loop8",
  "mldsa65_verify_internal_loop8_exit",
  ("X9","X28","X8"), ("Q20","Q22","Q21","Q8");
  "mldsa87_verify_internal", "mldsa87_verify_internal_loop10",
  "mldsa87_verify_internal_loop10_exit",
  ("X9","X28","X8"), ("Q20","Q22","Q21","Q8")];;

let INLINE_POLYT1_OF_INSTANCE (fn,hl,el,xs,qs) =
  INLINE_POLYT1_LOOP "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
    (INLINE_LOOP_EXEC hl el) hl el xs qs INLINE_POLYT1_MODS;;
