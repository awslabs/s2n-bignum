(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Functional correctness of mldsa_chknorm:                                  *)
(* Check if any polynomial coefficient has absolute value >= bound           *)
(* Returns 1 if norm check fails (|coeff| >= bound), 0 otherwise             *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "x86/mldsa/mldsa_chknorm.o";;
 ****)

let mldsa_chknorm_mc = define_assert_from_elf "mldsa_chknorm_mc" "x86/mldsa/mldsa_chknorm.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x83; 0xee; 0x01;        (* SUB (% esi) (Imm8 (word 1)) *)
  0xc5; 0xf1; 0xef; 0xc9;  (* VPXOR (%_% xmm1) (%_% xmm1) (%_% xmm1) *)
  0xc5; 0xf9; 0x6e; 0xd6;  (* VMOVD (%_% xmm2) (% esi) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xd2;
                           (* VPBROADCASTD (%_% ymm2) (%_% xmm2) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0x07;
                           (* VPABSD (%_% ymm0) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0x66; 0xc2;  (* VPCMPGTD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xc8;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0x5f; 0x20;
                           (* VPABSD (%_% ymm3) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xe5; 0x66; 0xda;  (* VPCMPGTD (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcb;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0x67; 0x40;
                           (* VPABSD (%_% ymm4) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xdd; 0x66; 0xe2;  (* VPCMPGTD (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcc;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0x6f; 0x60;
                           (* VPABSD (%_% ymm5) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0xd5; 0x66; 0xea;  (* VPCMPGTD (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcd;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm5) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VPABSD (%_% ymm0) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0xfd; 0x66; 0xc2;  (* VPCMPGTD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xc8;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0x9f; 0xa0; 0x00; 0x00; 0x00;
                           (* VPABSD (%_% ymm3) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0xe5; 0x66; 0xda;  (* VPCMPGTD (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcb;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0xa7; 0xc0; 0x00; 0x00; 0x00;
                           (* VPABSD (%_% ymm4) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0xdd; 0x66; 0xe2;  (* VPCMPGTD (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcc;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0xaf; 0xe0; 0x00; 0x00; 0x00;
                           (* VPABSD (%_% ymm5) (Memop Word256 (%% (rdi,224))) *)
  0xc5; 0xd5; 0x66; 0xea;  (* VPCMPGTD (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcd;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm5) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0x87; 0x00; 0x01; 0x00; 0x00;
                           (* VPABSD (%_% ymm0) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0xfd; 0x66; 0xc2;  (* VPCMPGTD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xc8;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0x9f; 0x20; 0x01; 0x00; 0x00;
                           (* VPABSD (%_% ymm3) (Memop Word256 (%% (rdi,288))) *)
  0xc5; 0xe5; 0x66; 0xda;  (* VPCMPGTD (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcb;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0xa7; 0x40; 0x01; 0x00; 0x00;
                           (* VPABSD (%_% ymm4) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0xdd; 0x66; 0xe2;  (* VPCMPGTD (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcc;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0xaf; 0x60; 0x01; 0x00; 0x00;
                           (* VPABSD (%_% ymm5) (Memop Word256 (%% (rdi,352))) *)
  0xc5; 0xd5; 0x66; 0xea;  (* VPCMPGTD (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcd;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm5) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* VPABSD (%_% ymm0) (Memop Word256 (%% (rdi,384))) *)
  0xc5; 0xfd; 0x66; 0xc2;  (* VPCMPGTD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xc8;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0x9f; 0xa0; 0x01; 0x00; 0x00;
                           (* VPABSD (%_% ymm3) (Memop Word256 (%% (rdi,416))) *)
  0xc5; 0xe5; 0x66; 0xda;  (* VPCMPGTD (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcb;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0xa7; 0xc0; 0x01; 0x00; 0x00;
                           (* VPABSD (%_% ymm4) (Memop Word256 (%% (rdi,448))) *)
  0xc5; 0xdd; 0x66; 0xe2;  (* VPCMPGTD (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcc;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0xaf; 0xe0; 0x01; 0x00; 0x00;
                           (* VPABSD (%_% ymm5) (Memop Word256 (%% (rdi,480))) *)
  0xc5; 0xd5; 0x66; 0xea;  (* VPCMPGTD (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcd;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm5) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0x87; 0x00; 0x02; 0x00; 0x00;
                           (* VPABSD (%_% ymm0) (Memop Word256 (%% (rdi,512))) *)
  0xc5; 0xfd; 0x66; 0xc2;  (* VPCMPGTD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xc8;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0x9f; 0x20; 0x02; 0x00; 0x00;
                           (* VPABSD (%_% ymm3) (Memop Word256 (%% (rdi,544))) *)
  0xc5; 0xe5; 0x66; 0xda;  (* VPCMPGTD (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcb;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0xa7; 0x40; 0x02; 0x00; 0x00;
                           (* VPABSD (%_% ymm4) (Memop Word256 (%% (rdi,576))) *)
  0xc5; 0xdd; 0x66; 0xe2;  (* VPCMPGTD (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcc;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0xaf; 0x60; 0x02; 0x00; 0x00;
                           (* VPABSD (%_% ymm5) (Memop Word256 (%% (rdi,608))) *)
  0xc5; 0xd5; 0x66; 0xea;  (* VPCMPGTD (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcd;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm5) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0x87; 0x80; 0x02; 0x00; 0x00;
                           (* VPABSD (%_% ymm0) (Memop Word256 (%% (rdi,640))) *)
  0xc5; 0xfd; 0x66; 0xc2;  (* VPCMPGTD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xc8;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0x9f; 0xa0; 0x02; 0x00; 0x00;
                           (* VPABSD (%_% ymm3) (Memop Word256 (%% (rdi,672))) *)
  0xc5; 0xe5; 0x66; 0xda;  (* VPCMPGTD (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcb;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0xa7; 0xc0; 0x02; 0x00; 0x00;
                           (* VPABSD (%_% ymm4) (Memop Word256 (%% (rdi,704))) *)
  0xc5; 0xdd; 0x66; 0xe2;  (* VPCMPGTD (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcc;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0xaf; 0xe0; 0x02; 0x00; 0x00;
                           (* VPABSD (%_% ymm5) (Memop Word256 (%% (rdi,736))) *)
  0xc5; 0xd5; 0x66; 0xea;  (* VPCMPGTD (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcd;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm5) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0x87; 0x00; 0x03; 0x00; 0x00;
                           (* VPABSD (%_% ymm0) (Memop Word256 (%% (rdi,768))) *)
  0xc5; 0xfd; 0x66; 0xc2;  (* VPCMPGTD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xc8;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0x9f; 0x20; 0x03; 0x00; 0x00;
                           (* VPABSD (%_% ymm3) (Memop Word256 (%% (rdi,800))) *)
  0xc5; 0xe5; 0x66; 0xda;  (* VPCMPGTD (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcb;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0xa7; 0x40; 0x03; 0x00; 0x00;
                           (* VPABSD (%_% ymm4) (Memop Word256 (%% (rdi,832))) *)
  0xc5; 0xdd; 0x66; 0xe2;  (* VPCMPGTD (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcc;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0xaf; 0x60; 0x03; 0x00; 0x00;
                           (* VPABSD (%_% ymm5) (Memop Word256 (%% (rdi,864))) *)
  0xc5; 0xd5; 0x66; 0xea;  (* VPCMPGTD (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcd;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm5) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0x87; 0x80; 0x03; 0x00; 0x00;
                           (* VPABSD (%_% ymm0) (Memop Word256 (%% (rdi,896))) *)
  0xc5; 0xfd; 0x66; 0xc2;  (* VPCMPGTD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xc8;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0x9f; 0xa0; 0x03; 0x00; 0x00;
                           (* VPABSD (%_% ymm3) (Memop Word256 (%% (rdi,928))) *)
  0xc5; 0xe5; 0x66; 0xda;  (* VPCMPGTD (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcb;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0xa7; 0xc0; 0x03; 0x00; 0x00;
                           (* VPABSD (%_% ymm4) (Memop Word256 (%% (rdi,960))) *)
  0xc5; 0xdd; 0x66; 0xe2;  (* VPCMPGTD (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcc;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x1e; 0xaf; 0xe0; 0x03; 0x00; 0x00;
                           (* VPABSD (%_% ymm5) (Memop Word256 (%% (rdi,992))) *)
  0xc5; 0xd5; 0x66; 0xea;  (* VPCMPGTD (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xf5; 0xeb; 0xcd;  (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm5) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x17; 0xc9;
                           (* VPTEST (%_% ymm1) (%_% ymm1) *)
  0x0f; 0x95; 0xc0;        (* SETNE (% al) *)
  0xc3                     (* RET *)
];;

let mldsa_chknorm_tmc = define_trimmed "mldsa_chknorm_tmc" mldsa_chknorm_mc;;

let MLDSA_CHKNORM_TMC_EXEC = X86_MK_CORE_EXEC_RULE mldsa_chknorm_tmc;;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas                                                             *)
(* ------------------------------------------------------------------------- *)

(* Expression emerging from the AVX2 code converting a bool to 32-bit mask *)
let bit_to_mask32 = new_definition `bit_to_mask32 (b : bool) : 32 word = word_neg (word (bitval b) : 32 word)`;;

(* Bound check predicate: |v| > b - 1 iff |v| >= b (with b > 0).
   The asm subtracts 1 from B and uses VPCMPGTD; this bd captures the
   resulting per-lane test. *)
let bd = new_definition `bd (v : int32) (b: int32) : bool =
    word_igt (iword (abs (ival v)) : 32 word) (word_sub b (word 1))`;;

let BD_SIMP = prove(
  `abs(ival(x : int32)) < &2 pow 31 /\ &0 <= ival(b:int32)
   ==> (bd x b <=> abs (ival x) >= ival b)`,
  REWRITE_TAC[bd; word_igt; irelational2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ival(iword(abs(ival(x:32 word))) : 32 word) = abs(ival x)` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `b:int32` IVAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `ival(word_sub (b:int32) (word 1)) = ival b - &1`
     (fun th -> REWRITE_TAC[th]) THENL
   [ALL_TAC; ASM_INT_ARITH_TAC] THEN
  SUBGOAL_THEN `word_sub (b:int32) (word 1) = iword(ival b - &1)` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_INT_ARITH_TAC);;

let BIT_TO_MASK32_OR = prove(
  `word_or (bit_to_mask32 b0) (bit_to_mask32 b1) = bit_to_mask32 (b0 \/ b1)`,
  REWRITE_TAC[bit_to_mask32] THEN
  BOOL_CASES_TAC `b0:bool` THEN BOOL_CASES_TAC `b1:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV);;

(* word_join with same pattern preserves OR *)
let WORD_JOIN_OR_TYBIT0 = prove(
  `word_or (word_join (a:N word) (b:N word) : (N tybit0) word) (word_join (c:N word) (d:N word)) =
   word_join (word_or a c) (word_or b d)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; BIT_WORD_JOIN; DIMINDEX_TYBIT0] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i < 2 * dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p ==> (q <=> p /\ q)`) THEN ASM_ARITH_TAC);;

(* The vpabsd lane operation: under the precondition |ival x| < 2^31, the
   semantics simplifies to iword(abs(ival x)). *)
let VPABSD_LANE = prove(
  `abs(ival(x:int32)) < &2 pow 31 ==>
   (if word_igt (word 0:int32) x then word_neg x else x) = iword(abs(ival x))`,
  REWRITE_TAC[WORD_IGT; IVAL_WORD_0] THEN STRIP_TAC THEN
  COND_CASES_TAC THENL
   [CONV_TAC(LAND_CONV(REWR_CONV(GSYM IWORD_IVAL))) THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `word_neg(x:int32) = iword(--(ival x))` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) IVAL_IWORD o lhs o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_INT_ARITH_TAC;
    CONV_TAC(LAND_CONV(REWR_CONV(GSYM IWORD_IVAL))) THEN AP_TERM_TAC THEN
    ASM_INT_ARITH_TAC]);;

(* The vpcmpgtd lane: if word_igt y x then 0xFFFFFFFF else 0 = bit_to_mask32(word_igt y x) *)
let VPCMPGTD_LANE = prove(
  `(if word_igt (y:int32) x then (word 0xffffffff:int32) else word 0) = bit_to_mask32(word_igt y x)`,
  REWRITE_TAC[bit_to_mask32] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV);;

(* Combined vpabsd+vpcmpgtd lane: folds directly into bd. *)
let VPABSD_VPCMPGTD_BD = prove(
  `abs(ival(x:int32)) < &2 pow 31 ==>
     word_igt (if word_igt (word 0:int32) x then word_neg x else x) (word_sub b (word 1)) = bd x b`,
  DISCH_TAC THEN ONCE_REWRITE_TAC[bd] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VPABSD_LANE THEN ASM_REWRITE_TAC[]);;

(* val(word_join a b) = 0 iff val a = 0 /\ val b = 0 (for tybit0 doubled type) *)
let VAL_WORD_JOIN_TYBIT0_EQ_0 = prove(
  `!a:N word. !b:N word. (val(word_join a b :(N tybit0)word) = 0) <=> val a = 0 /\ val b = 0`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; ARITH_RULE `n + n = 2 * n`; DIMINDEX_TYBIT0] THEN
  MP_TAC(ISPEC `a:N word` VAL_BOUND) THEN
  MP_TAC(ISPEC `b:N word` VAL_BOUND) THEN
  ABBREV_TAC `p = 2 EXP dimindex(:N)` THEN
  ABBREV_TAC `m = val(a:N word)` THEN ABBREV_TAC `n = val(b:N word)` THEN
  REPEAT(POP_ASSUM(K ALL_TAC)) THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `m = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  SUBGOAL_THEN `1 <= p * m` MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN ASM_ARITH_TAC;
    ARITH_TAC]);;

(* val(bit_to_mask32 b) = 0 iff ~b *)
let VAL_BIT_TO_MASK32_EQ_0 = prove(
  `(val(bit_to_mask32 b) = 0) <=> ~b`,
  REWRITE_TAC[bit_to_mask32] THEN BOOL_CASES_TAC `b:bool` THENL
   [REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN ARITH_TAC;
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV]);;

(* Postamble fold: word_join (word 0 : 56 word) (if D then word 1 else word 0 : byte) : int64 = word(bitval D) *)
let WORD_JOIN_BYTE_BIT_TO_BITVAL = prove(
  `word_join (word 0:56 word) (if D then (word 1:byte) else word 0):int64 = word(bitval D)`,
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_CHKNORM_CORRECT = prove(
 `!a (x:num->int32) (bound:int32) pc.
        nonoverlapping (word pc, 558) (a, 1024)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_chknorm_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [a; word_zx bound] s /\
                  &0 <= ival bound /\
                  (!i. i < 256 ==>
                     read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
                  (!i. i < 256 ==> abs(ival(x i)) < &2 pow 31))
             (\s. read RIP s = word(pc + 557) /\
                  read RAX s = word(bitval(~(!i. i < 256 ==> abs(ival(x i)) < ival bound))))
             (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5] ,,
              MAYCHANGE [RAX; RSI] ,, MAYCHANGE SOME_FLAGS)`,
  (* Bridge the CBMC-aligned universal-negation postcondition to the existential
     form that the rest of the proof reasons about. *)
  REWRITE_TAC[MESON[INT_NOT_LT; INT_GE]
   `(~(!i. i < n ==> abs(ival((x:num->int32) i)) < (b:int))) <=>
    (?i. i < n /\ abs(ival(x i)) >= b)`] THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int32`; `bound:int32`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; fst MLDSA_CHKNORM_TMC_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  (* Expand the bounded forall over memory reads to 256 explicit equalities. *)
  UNDISCH_TAC
    `forall i. i < 256
       ==> read (memory :> bytes32 (word_add a (word (4 * i)))) s0 = x i` THEN
  CONV_TAC(ONCE_DEPTH_CONV
    (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  REPEAT STRIP_TAC THEN
  (* Merge bytes32 reads into bytes256 reads (32 chunks of 8 lanes each). *)
  MP_TAC(end_itlist CONJ
    (map (fun n -> READ_MEMORY_MERGE_CONV 3
                     (subst[mk_small_numeral(32*n),`n:num`]
                           `read (memory :> bytes256(word_add a (word n))) s0`))
         (0--31))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
  STRIP_TAC THEN
  (* Expand the bounded forall over absolute-value bounds. *)
  UNDISCH_TAC `forall i. i < 256 ==> abs (ival (x i:int32)) < &2 pow 31` THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV)) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  (* Symbolically execute all instructions until target PC, folding lane masks. *)
  MAP_UNTIL_TARGET_PC (fun n ->
    X86_STEPS_TAC MLDSA_CHKNORM_TMC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
      [VPCMPGTD_LANE; BIT_TO_MASK32_OR; WORD_JOIN_OR_TYBIT0])) 1 THEN
  (* Clean up nested word_zx around the broadcast bound. *)
  RULE_ASSUM_TAC(REWRITE_RULE
    [WORD_BLAST `(word_zx:int64->int32)((word_zx:int32->int64) x) = x`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* Fold vpabsd+vpcmpgtd lane forms into bd, then to abs(ival x) >= ival bound. *)
  ASM_SIMP_TAC[VPABSD_VPCMPGTD_BD] THEN
  REWRITE_TAC[GSYM bd] THEN
  ASM_SIMP_TAC[BD_SIMP] THEN
  (* Reduce val(word_join(...)) = 0 to disjunction of bit_to_mask32 vals. *)
  REWRITE_TAC[VAL_WORD_JOIN_TYBIT0_EQ_0; VAL_BIT_TO_MASK32_EQ_0] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN
  (* Fold the byte-level ITE into bitval. *)
  REWRITE_TAC[WORD_JOIN_BYTE_BIT_TO_BITVAL] THEN
  (* Now the goal is `bitval(D) = bitval(?i. i<256 /\ abs(ival(x i)) >= ival bound)`.
     Both sides are propositional combinations of 256 atoms. *)
  AP_TERM_TAC THEN
  GEN_REWRITE_TAC (BINOP_CONV o ONCE_DEPTH_CONV)
    [prove(`b = ~ (~ (b : bool))`, REWRITE_TAC[])] THEN
  GEN_REWRITE_TAC TOP_SWEEP_CONV
    [MESON[] `~(?i. i < n /\ P i) <=> (!i. i < n ==> ~P i)`; DE_MORGAN_THM] THEN
  CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  REPEAT AP_TERM_TAC THEN EQ_TAC THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine correctness theorem (includes return)                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_CHKNORM_NOIBT_SUBROUTINE_CORRECT = prove(
 `!a (x:num->int32) (bound:int32) pc stackpointer returnaddress.
        nonoverlapping (word pc, LENGTH mldsa_chknorm_tmc) (a, 1024) /\
        nonoverlapping (stackpointer,8) (a, 1024)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_chknorm_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; word_zx bound] s /\
                  &0 <= ival bound /\
                  (!i. i < 256 ==>
                     read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
                  (!i. i < 256 ==> abs(ival(x i)) < &2 pow 31))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read RAX s = word(bitval(~(!i. i < 256 ==> abs(ival(x i)) < ival bound))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_chknorm_tmc MLDSA_CHKNORM_CORRECT);;

let MLDSA_CHKNORM_SUBROUTINE_CORRECT = prove(
 `!a (x:num->int32) (bound:int32) pc stackpointer returnaddress.
        nonoverlapping (word pc, LENGTH mldsa_chknorm_mc) (a, 1024) /\
        nonoverlapping (stackpointer,8) (a, 1024)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_chknorm_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; word_zx bound] s /\
                  &0 <= ival bound /\
                  (!i. i < 256 ==>
                     read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
                  (!i. i < 256 ==> abs(ival(x i)) < &2 pow 31))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read RAX s = word(bitval(~(!i. i < 256 ==> abs(ival(x i)) < ival bound))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_CHKNORM_NOIBT_SUBROUTINE_CORRECT));;

(* ========================================================================= *)
(* Constant-time and memory safety proof.                                    *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mldsa_chknorm" subroutine_signatures)
    (REWRITE_RULE[SOME_FLAGS] MLDSA_CHKNORM_CORRECT)
    MLDSA_CHKNORM_TMC_EXEC;;

let MLDSA_CHKNORM_SAFE =
  REWRITE_RULE [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS]
  (time prove
   (full_spec,
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS] THEN
    PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars
      MLDSA_CHKNORM_TMC_EXEC));;

let MLDSA_CHKNORM_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a (bound:int32) pc stackpointer returnaddress.
          nonoverlapping (word pc, LENGTH mldsa_chknorm_tmc) (a, 1024) /\
          nonoverlapping (stackpointer, 8) (a, 1024)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_chknorm_tmc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a; word_zx bound] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc stackpointer returnaddress /\
                         memaccess_inbounds e2 [a,1024; stackpointer,8]
                                               [a,1024; stackpointer,8]))
               (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_chknorm_tmc MLDSA_CHKNORM_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLDSA_CHKNORM_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a (bound:int32) pc stackpointer returnaddress.
          nonoverlapping (word pc, LENGTH mldsa_chknorm_mc) (a, 1024) /\
          nonoverlapping (stackpointer, 8) (a, 1024)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_chknorm_mc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a; word_zx bound] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc stackpointer returnaddress /\
                         memaccess_inbounds e2 [a,1024; stackpointer,8]
                                               [a,1024; stackpointer,8]))
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_CHKNORM_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let mldsa_chknorm_windows_mc = define_from_elf
   "mldsa_chknorm_windows_mc" "x86/mldsa/mldsa_chknorm.obj";;

let mldsa_chknorm_windows_tmc =
  define_trimmed "mldsa_chknorm_windows_tmc" mldsa_chknorm_windows_mc;;

let MLDSA_CHKNORM_WINDOWS_TMC_EXEC =
  X86_MK_EXEC_RULE mldsa_chknorm_windows_tmc;;

let MLDSA_CHKNORM_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove(
 `!a (x:num->int32) (bound:int32) pc stackpointer returnaddress.
        nonoverlapping (word pc, LENGTH mldsa_chknorm_windows_tmc) (a, 1024) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (a,1024) /\
        nonoverlapping (word pc,LENGTH mldsa_chknorm_windows_tmc)
                       (word_sub stackpointer (word 16),16)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_chknorm_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [a; word_zx bound] s /\
                  &0 <= ival bound /\
                  (!i. i < 256 ==>
                     read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
                  (!i. i < 256 ==> abs(ival(x i)) < &2 pow 31))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read RAX s = word(bitval(~(!i. i < 256 ==> abs(ival(x i)) < ival bound))))
             (MAYCHANGE [RSP] ,,
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC mldsa_chknorm_windows_tmc mldsa_chknorm_tmc
      MLDSA_CHKNORM_CORRECT);;

let MLDSA_CHKNORM_WINDOWS_SUBROUTINE_CORRECT = prove(
 `!a (x:num->int32) (bound:int32) pc stackpointer returnaddress.
        nonoverlapping (word pc, LENGTH mldsa_chknorm_windows_mc) (a, 1024) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (a,1024) /\
        nonoverlapping (word pc,LENGTH mldsa_chknorm_windows_mc)
                       (word_sub stackpointer (word 16),16)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_chknorm_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [a; word_zx bound] s /\
                  &0 <= ival bound /\
                  (!i. i < 256 ==>
                     read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
                  (!i. i < 256 ==> abs(ival(x i)) < &2 pow 31))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read RAX s = word(bitval(~(!i. i < 256 ==> abs(ival(x i)) < ival bound))))
             (MAYCHANGE [RSP] ,,
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_CHKNORM_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

(* Windows safety proofs *)

let MLDSA_CHKNORM_NOIBT_WINDOWS_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a (bound:int32) pc stackpointer returnaddress.
          nonoverlapping (word pc, LENGTH mldsa_chknorm_windows_tmc) (a, 1024) /\
          nonoverlapping (word_sub stackpointer (word 16),24) (a,1024) /\
          nonoverlapping (word pc,LENGTH mldsa_chknorm_windows_tmc)
                         (word_sub stackpointer (word 16),16)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_chknorm_windows_tmc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    WINDOWS_C_ARGUMENTS [a; word_zx bound] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc (word_sub stackpointer (word 16)) returnaddress /\
                         memaccess_inbounds e2
                           [a,1024; word_sub stackpointer (word 16),24]
                           [a,1024; word_sub stackpointer (word 16),16]))
               (MAYCHANGE [RSP] ,,
                WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16), 16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC mldsa_chknorm_windows_tmc mldsa_chknorm_tmc
      MLDSA_CHKNORM_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLDSA_CHKNORM_WINDOWS_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a (bound:int32) pc stackpointer returnaddress.
          nonoverlapping (word pc, LENGTH mldsa_chknorm_windows_mc) (a, 1024) /\
          nonoverlapping (word_sub stackpointer (word 16),24) (a,1024) /\
          nonoverlapping (word pc,LENGTH mldsa_chknorm_windows_mc)
                         (word_sub stackpointer (word 16),16)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_chknorm_windows_mc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    WINDOWS_C_ARGUMENTS [a; word_zx bound] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc (word_sub stackpointer (word 16)) returnaddress /\
                         memaccess_inbounds e2
                           [a,1024; word_sub stackpointer (word 16),24]
                           [a,1024; word_sub stackpointer (word 16),16]))
               (MAYCHANGE [RSP] ,,
                WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16), 16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_CHKNORM_NOIBT_WINDOWS_SUBROUTINE_SAFE));;
