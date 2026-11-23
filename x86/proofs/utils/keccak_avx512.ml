(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the AVX-512VL Keccak-f1600 permutations of the    *)
(* AVX-512 version of mlkem_native2, sha3_keccak4_f1600_avx512 and           *)
(* sha3_keccak_f1600_avx512: each keeps every lane in a register of its own  *)
(* and computes the XORs of theta and chi with vpternlogq.                   *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/keccak_spec.ml";;
needs "x86/proofs/utils/keccak_avx2.ml";;

(*** The two functions of vpternlogq in the code, as the model computes
 *** them: the disjunction of the minterms selected by the immediate, those
 *** of the zero bits dropped
 ***)

let KECCAK_AVX512_TERNLOG_96 = WORD_BITWISE_RULE
 `word_or (word_and (word_not a) (word_and (word_not b) c))
   (word_or (word_and (word_not a) (word_and b (word_not c)))
     (word_or (word_and a (word_and (word_not b) (word_not c)))
              (word_and a (word_and b c)))):N word =
  word_xor a (word_xor b c)`;;

let KECCAK_AVX512_TERNLOG_D2 = WORD_BITWISE_RULE
 `word_or (word_and (word_not a) (word_and (word_not b) c))
   (word_or (word_and a (word_and (word_not b) (word_not c)))
     (word_or (word_and a (word_and b (word_not c)))
              (word_and a (word_and b c)))):N word =
  word_xor a (word_and (word_not b) c)`;;

(*** The simplification of the new value of a register after a step, as by
 *** KECCAK_AVX2_SIMPLIFY_TAC, with vpternlogq as XOR and AND-NOT first
 ***)

let KECCAK_AVX512_SIMPLIFY_TAC =
  let is_simd th =
    can (term_match [] `read X (s:x86state):int256 = whatever`) (concl th) ||
    can (term_match [] `read X (s:x86state):int128 = whatever`) (concl th) in
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV
     (GEN_REWRITE_CONV TOP_DEPTH_CONV
       [KECCAK_AVX512_TERNLOG_96; KECCAK_AVX512_TERNLOG_D2] THENC
      TOP_DEPTH_CONV
       (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV) THENC
      DEPTH_CONV WORD_NUM_RED_CONV)) o
    check is_simd));;

(*** keccak_round of a list of 25 lanes, with the lets expanded ***)

let KECCAK_ROUND_EXPLICIT =
  let xs = map (fun k -> mk_var("x"^string_of_int k,`:int64`)) (0--24) in
  let tm = list_mk_comb(`keccak_round`,[`c:int64`; mk_list(xs,`:int64`)]) in
  GENL (`c:int64`::xs)
   ((REWRITE_CONV[keccak_round] THENC TOP_DEPTH_CONV let_CONV THENC
     TOP_DEPTH_CONV EL_CONV) tm);;

(* ------------------------------------------------------------------------- *)
(* The layout of the state in the registers. Both permutations keep lane k   *)
(* in register k at the start of each iteration of four rounds; each round   *)
(* writes the lanes back where pi took them from, so the lane in each        *)
(* register after rounds 1, 2 and 3 is given by keccak_avx512_layout1-3, and *)
(* after round 4, once the moves at its end have been made, by               *)
(* keccak_avx512_layout0 again. The lists give the lane in each register.    *)
(* ------------------------------------------------------------------------- *)

let keccak_avx512_layout0 = define
 `keccak_avx512_layout0 =
    [0;1;2;3;4;5;6;7;8;9;10;11;12;
     13;14;15;16;17;18;19;20;21;22;23;24]`;;

let keccak_avx512_layout1 = define
 `keccak_avx512_layout1 =
    [0;10;20;5;15;16;1;11;21;6;7;17;2;
     12;22;23;8;18;3;13;14;24;9;19;4]`;;

let keccak_avx512_layout2 = define
 `keccak_avx512_layout2 =
    [0;7;14;16;23;8;10;17;24;1;11;18;20;
     2;9;19;21;3;5;12;22;4;6;13;15]`;;

let keccak_avx512_layout3 = define
 `keccak_avx512_layout3 =
    [0;11;22;8;19;21;7;18;4;10;17;3;14;
     20;6;13;24;5;16;2;9;15;1;12;23]`;;

(* ------------------------------------------------------------------------- *)
(* The loop: rsi points to the round constants of the iteration, and rax to  *)
(* the end of the table, rsi + 192, so cmp rsi, rax ends the loop after six  *)
(* iterations.                                                               *)
(* ------------------------------------------------------------------------- *)

let KECCAK_AVX512_RSI = prove
 (`!rc:int64 i.
     word_add (word_add rc (word (32 * i))) (word 32) =
     word_add rc (word (32 * (i + 1)))`,
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; WORD_ADD; WORD_ADD_ASSOC]);;

let KECCAK_AVX512_ZF = prove
 (`!rc:int64 i.
     i < 6
     ==> (val (word_sub (word_add (word_add rc (word (32 * i))) (word 32))
                        (word_add rc (word 192))) = 0 <=> i + 1 = 6)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `word_sub (word_add (word_add rc (word (32 * i))) (word 32))
             (word_add rc (word 192)):int64 =
    word_sub (word(32 * i + 32)) (word 192)`
  SUBST1_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
    SPEC_TAC(`i:num`,`i:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV))]);;

let KECCAK_AVX512_BRANCH = prove
 (`!rc:int64 i.
     i < 6
     ==> (~(val (word_add (word_add rc (word (32 * i))) (word 32)) =
            val (word_add rc (word 192))) <=> i + 1 < 6)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_WORD_SUB_EQ_0] THEN
  ASM_SIMP_TAC[KECCAK_AVX512_ZF] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The simulation for the safety proofs.                                     *)
(* ------------------------------------------------------------------------- *)

(*** The values in the SIMD registers do not matter for safety, and the
 *** simulation of a whole iteration with them would be slow, so they are
 *** dropped after each step
 ***)

let KECCAK_AVX512_SAFE_SIM_TAC execth n =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY (fun k ->
    X86_STEPS_TAC execth [k] THEN
    DISCARD_ASSUMPTIONS_TAC
     (can (term_match [] `read X (s:x86state):int256 = y`) o concl))
   (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0];;

needs "x86/proofs/consttime.ml";;

(* ------------------------------------------------------------------------- *)
(* For the theorems that are correctness and safety in one ("FULL"): the     *)
(* events of the rest of an iteration reassociated to split off those of its *)
(* next round, and the branch back as a condition on the iteration.          *)
(* ------------------------------------------------------------------------- *)

let KECCAK_AVX512_EVENTS_REASSOC_TAC =
  CONV_TAC(ONCE_DEPTH_CONV(fun t ->
    if is_eq t && is_var(lhs t) && name_of(lhs t) = "e2"
    then RAND_CONV(REWR_CONV(GSYM APPEND_ASSOC)) t
    else failwith "KECCAK_AVX512_EVENTS_REASSOC_TAC"));;

let KECCAK_AVX512_ZF_BRANCH = prove
 (`!rc:int64 i.
     i < 6
     ==> (~(val (word_sub (word_add (word_add rc (word (32 * i))) (word 32))
                          (word_add rc (word 192))) = 0) <=> i + 1 < 6)`,
  SIMP_TAC[KECCAK_AVX512_ZF] THEN ARITH_TAC);;

let KECCAK_AVX512_WORD_COND = prove
 (`!p x y. (if p then word x else word y):int64 = word(if p then x else y)`,
  MESON_TAC[]);;
