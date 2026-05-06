(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of correctness for gcm_gmult_v8                                    *)
(* (GHASH polynomial multiply: Xi = H * Xi mod P).                          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/gcm_gmult_v8_nist.ml";;

let gcm_gmult_v8_mc = define_assert_from_elf "gcm_gmult_v8_mc"
  "arm/aes-gcm/gcm_gmult_v8.o"
[
  0x3dc00010;       (* ldr q16, [x0] *)
  0xd2f84002;       (* mov x2, #0xc200000000000000 *)
  0x4e080c54;       (* dup v20.2d, x2 *)
  0x3dc00032;       (* ldr q18, [x1] *)
  0x3dc00433;       (* ldr q19, [x1, #16] *)
  0x6e124252;       (* ext v18.16b, v18.16b, v18.16b, #8 *)
  0x4e200a10;       (* rev64 v16.16b, v16.16b *)
  0x6e104203;       (* ext v3.16b, v16.16b, v16.16b, #8 *)
  0x0ee3e240;       (* pmull v0.1q, v18.1d, v3.1d *)
  0x6e231e10;       (* eor v16.16b, v16.16b, v3.16b *)
  0x4ee3e242;       (* pmull2 v2.1q, v18.2d, v3.2d *)
  0x0ef0e261;       (* pmull v1.1q, v19.1d, v16.1d *)
  0x6e024010;       (* ext v16.16b, v0.16b, v2.16b, #8 *)
  0x6e221c11;       (* eor v17.16b, v0.16b, v2.16b *)
  0x6e301c21;       (* eor v1.16b, v1.16b, v16.16b *)
  0x6e311c21;       (* eor v1.16b, v1.16b, v17.16b *)
  0x0ef4e011;       (* pmull v17.1q, v0.1d, v20.1d *)
  0x6e084422;       (* mov v2.d[0], v1.d[1] *)
  0x6e180401;       (* mov v1.d[1], v0.d[0] *)
  0x6e311c20;       (* eor v0.16b, v1.16b, v17.16b *)
  0x6e004011;       (* ext v17.16b, v0.16b, v0.16b, #8 *)
  0x0ef4e000;       (* pmull v0.1q, v0.1d, v20.1d *)
  0x6e221e31;       (* eor v17.16b, v17.16b, v2.16b *)
  0x6e311c00;       (* eor v0.16b, v0.16b, v17.16b *)
  0x4e200800;       (* rev64 v0.16b, v0.16b *)
  0x6e004000;       (* ext v0.16b, v0.16b, v0.16b, #8 *)
  0x3d800000;       (* str q0, [x0] *)
  0xd65f03c0        (* ret *)
];;

let GCM_GMULT_V8_EXEC = ARM_MK_EXEC_RULE gcm_gmult_v8_mc;;

let WORD_INSERT_AS_JOIN_1 = prove(
  `!(a:(128)word) (b:(128)word).
    word_insert a (0,64) (word_subword b (64,64):(128)word) =
    (word_join (word_subword a (64,64):(64)word) (word_subword b (64,64):(64)word):(128)word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_INSERT; BIT_WORD_JOIN;
              BIT_WORD_SUBWORD; DIMINDEX_64; DIMINDEX_128;
              SUB_0; LE_0; ADD_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[COND_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 128 /\ ~(i < 64) ==> i - 64 < 64`;
               ARITH_RULE `i < 128 /\ ~(i < 64) ==> 64 + i - 64 = i`]);;

let WORD_INSERT_AS_JOIN_2 = prove(
  `!(a:(128)word) (b:(128)word).
    word_insert a (64,64) (word_subword b (0,64):(128)word) =
    (word_join (word_subword b (0,64):(64)word) (word_subword a (0,64):(64)word):(128)word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_INSERT; BIT_WORD_JOIN;
              BIT_WORD_SUBWORD; DIMINDEX_64; DIMINDEX_128;
              SUB_0; LE_0; ADD_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[COND_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `64 <= i /\ i < 128 ==> ~(i < 64)`;
               ARITH_RULE `64 <= i /\ i < 128 ==> i - 64 < 64`;
               ARITH_RULE `~(64 <= i /\ i < 128) /\ i < 128 ==> i < 64`;
               ARITH_RULE `0 + i = i`]);;

(* The simulation produces word_xor of 128-bit words for the Karatsuba
   XOR, but the simplified spec XORs the 64-bit halves directly. *)
let KAR_SUBWORD_LEMMA = prove(
  `!(xi_rev:(128)word).
    word_subword
      (word_xor xi_rev
        (word_subword (word_join xi_rev xi_rev:(256)word) (64,128)))
      (0,64):(64)word =
    word_xor (word_subword xi_rev (0,64):(64)word)
             (word_subword xi_rev (64,64):(64)word)`,
  CONV_TAC WORD_BLAST);;

(* ---- Per-step SIMD simplification tactic -------------------------------- *)

(* Applied after every ARM step to eagerly simplify SIMD byte-level
   expansions, collapse double half-swaps, and reduce nested subwords.
   This keeps terms manageable throughout the simulation. *)
let GCM_SIMD_SIMPLIFY_TAC =
  SIMD_SIMPLIFY_ASSUM_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE [WORD_SWAP_HALVES_INVOLUTION]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) th
    with _ -> th);;

(* ---- Functional correctness proof ---------------------------------------- *)

let GCM_GMULT_V8_EXEC_CORRECT = prove
 (`!xi_ptr htable_ptr (xi:(128)word) (h:(128)word) (hhl:(128)word) pc.
    nonoverlapping (word pc,112) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,112) (htable_ptr:int64,32) /\
    nonoverlapping (xi_ptr,16) (htable_ptr,32)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) gcm_gmult_v8_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [xi_ptr; htable_ptr] s /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = hhl)
      (\s. read PC s = word(pc + 108) /\
           read (memory :> bytes128 xi_ptr) s = gcm_gmult_spec xi h hhl)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(xi_ptr,16)])`,
  MAP_EVERY X_GEN_TAC
    [`xi_ptr:int64`; `htable_ptr:int64`; `xi:(128)word`;
     `h:(128)word`; `hhl:(128)word`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              SOME_FLAGS; NONOVERLAPPING_CLAUSES; fst GCM_GMULT_V8_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Simulate all 27 instructions, simplifying SIMD terms after each step *)
  MAP_EVERY (fun n -> ARM_STEPS_TAC GCM_GMULT_V8_EXEC [n] THEN
                      GCM_SIMD_SIMPLIFY_TAC) (1--27) THEN

  (* Close the simulation and prove functional correctness *)
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[gcm_gmult_spec; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_BITWISE_RULE `word_xor a b = word_xor b a`;
              WORD_INSERT_AS_JOIN_1; WORD_INSERT_AS_JOIN_2;
              KAR_SUBWORD_LEMMA]);;

(* ---- Subroutine correctness (adds return address handling) -------------- *)

let GCM_GMULT_V8_SUBROUTINE_CORRECT = prove
 (`!xi_ptr htable_ptr (xi:(128)word) (h:(128)word) (hhl:(128)word)
    pc returnaddress.
    nonoverlapping (word pc,112) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,112) (htable_ptr:int64,32) /\
    nonoverlapping (xi_ptr,16) (htable_ptr,32)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) gcm_gmult_v8_mc /\
           read PC s = word pc /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [xi_ptr; htable_ptr] s /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = hhl)
      (\s. read PC s = returnaddress /\
           read (memory :> bytes128 xi_ptr) s = gcm_gmult_spec xi h hhl)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(xi_ptr,16)])`,
  ARM_ADD_RETURN_NOSTACK_TAC GCM_GMULT_V8_EXEC GCM_GMULT_V8_EXEC_CORRECT);;
