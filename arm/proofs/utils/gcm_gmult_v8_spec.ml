(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SIMD simplification lemmas and specification for gcm_gmult_v8            *)
(* ========================================================================= *)

(* ---- REV64 lane-reversal lemmas ---------------------------------------- *)

(* The ARM simulator expands REV64.16B into a 4-level nested tree of
   word_join / word_subword operations (128->64->32->16->8 bits).
   These three lemmas collapse that tree back to word_reversefields 8.
   All other word_join/word_subword simplifications are handled by
   WORD_SIMPLE_SUBWORD_CONV in the per-step tactic. *)

(* Lower 64-bit lane: byte-join = word_reversefields 8 of lower half *)
let REV64_LOWER_LANE = prove(
  `!(xi:(128)word).
    word_join
      (word_join (word_join (word_subword xi (0,8):(8)word) (word_subword xi (8,8):(8)word):(16)word)
                 (word_join (word_subword xi (16,8):(8)word) (word_subword xi (24,8):(8)word):(16)word):(32)word)
      (word_join (word_join (word_subword xi (32,8):(8)word) (word_subword xi (40,8):(8)word):(16)word)
                 (word_join (word_subword xi (48,8):(8)word) (word_subword xi (56,8):(8)word):(16)word):(32)word):(64)word =
    word_reversefields 8 (word_subword xi (0,64):(64)word)`,
  CONV_TAC WORD_BLAST);;

(* Upper 64-bit lane: byte-join = word_reversefields 8 of upper half *)
let REV64_UPPER_LANE = prove(
  `!(xi:(128)word).
    word_join
      (word_join (word_join (word_subword xi (64,8):(8)word) (word_subword xi (72,8):(8)word):(16)word)
                 (word_join (word_subword xi (80,8):(8)word) (word_subword xi (88,8):(8)word):(16)word):(32)word)
      (word_join (word_join (word_subword xi (96,8):(8)word) (word_subword xi (104,8):(8)word):(16)word)
                 (word_join (word_subword xi (112,8):(8)word) (word_subword xi (120,8):(8)word):(16)word):(32)word):(64)word =
    word_reversefields 8 (word_subword xi (64,64):(64)word)`,
  CONV_TAC WORD_BLAST);;

(* Full REV64 on 128-bit: per-lane reversal = halves-swapped full reversal *)
let REV64_128 = prove(
  `!(xi:(128)word).
    word_join
      (word_reversefields 8 (word_subword xi (64,64):(64)word))
      (word_reversefields 8 (word_subword xi (0,64):(64)word)):(128)word =
    word_subword (word_join (word_reversefields 8 xi:(128)word)
                            (word_reversefields 8 xi:(128)word):(256)word) (64,128)`,
  CONV_TAC WORD_BLAST);;

(* Double half-swap is the identity: swap(swap(a)) = a.
   Used directly in GCM_SIMD_SIMPLIFY_TAC, not in SIMD_SIMPLIFY_RULES. *)
let WORD_SWAP_HALVES_INVOLUTION = prove(
  `!(a:(128)word).
    word_subword
      (word_join
        (word_subword (word_join a a:(256)word) (64,128):(128)word)
        (word_subword (word_join a a:(256)word) (64,128):(128)word):(256)word)
      (64,128):(128)word = a`,
  CONV_TAC WORD_BLAST);;

(* ---- Rewrite rule set and tactic --------------------------------------- *)

let SIMD_SIMPLIFY_RULES = [
  REV64_LOWER_LANE; REV64_UPPER_LANE; REV64_128];;

let SIMD_SIMPLIFY_ASSUM_TAC =
  RULE_ASSUM_TAC(fun th ->
    try REWRITE_RULE SIMD_SIMPLIFY_RULES th with _ -> th);;

(* ---- Specification ---------------------------------------------------- *)

(* gcm_gmult_spec xi h hhl
   Inputs:
     xi  = GHASH accumulator, read from [x0]         (LDR Q16)
     h   = hash key, read from [x1]                  (LDR Q18)
     hhl = Karatsuba helper, read from [x1+16]       (LDR Q19)
           lower 64 bits hold (H_hi XOR H_lo), precomputed by gcm_init_v8

   The spec mirrors the assembly register data-flow line by line.
   Register names (Q0-Q20) are noted on the right for reference.

   -- Byte reversal + half-swap (steps 7-8) --
   xi_rev  = REV64(xi): byte-reverse within each 64-bit lane       [Q16]
   xi_swp  = EXT(xi_rev, #8): swap halves of xi_rev                [Q3]
             REV64 + EXT together = full 128-bit byte reversal.
             xi_swp is the GCM polynomial representation of xi.
             xi_rev (without the swap) is kept for the Karatsuba XOR.

   -- Karatsuba polynomial multiply (steps 9-12) --
   xl      = PMULL  h_lo * xi_swp_lo   (low 64x64->128 product)   [Q0]
   xh      = PMULL2 h_hi * xi_swp_hi   (high 64x64->128 product)  [Q2]
   kar_pre = xi_swp XOR xi_rev = (xi_lo XOR xi_hi) in both halves  [Q16]
   xm      = PMULL hhl_lo * kar_pre_lo  (middle, Karatsuba)        [Q1]
             One multiply instead of two: (h_lo+h_hi)*(xi_lo+xi_hi)

   -- Combine partial products (steps 13-16) --
   t1      = EXT(xh, xl, #8): cross-extract overlapping middle     [Q16]
   t2      = xl XOR xh                                             [Q17]
   xm'     = xm XOR t1 XOR t2: Karatsuba recombination             [Q1]

   -- Reduction phase 1 (steps 17-20) --
   red1    = PMULL xl_lo * 0xC2..0  (reduce with GCM polynomial)   [Q17]
   xh'     = xh with low half <- xm' high half  (INS, accumulate)  [Q2]
   xl_rot  = xm' with high half <- xl low half  (INS, rotate up)   [Q1]
   phase1  = red1 XOR xl_rot                                       [Q0]

   -- Reduction phase 2 (steps 21-24) --
   t3      = EXT(phase1, #8): half-swap                            [Q17]
   red2    = PMULL phase1_lo * 0xC2..0  (second reduction round)   [Q0]
   t3'     = xh' XOR t3                                            [Q17]
   phase2  = t3' XOR red2: fully reduced 128-bit result            [Q0]

   -- Final byte reversal (steps 25-26) --
   result  = REV64 + EXT of phase2: back to memory byte order      [Q0]
             Stored to [x0] via STR (step 27).                          *)

let gcm_gmult_spec = new_definition
  `gcm_gmult_spec (xi:(128)word) (h:(128)word) (hhl:(128)word) =
   let xi_rev:int128 = word_reversefields 8 xi in
   let xl:int128 = word_pmul (word_subword h (64,64):(64)word) (word_subword xi_rev (0,64):(64)word) in
   let xh:int128 = word_pmul (word_subword h (0,64):(64)word) (word_subword xi_rev (64,64):(64)word) in
   let kar_lo:int64 = word_xor (word_subword xi_rev (0,64):(64)word) (word_subword xi_rev (64,64):(64)word) in
   let xm:int128 = word_pmul (word_subword hhl (0,64):(64)word) kar_lo in
   let t1:int128 = word_subword (word_join xh xl:(256)word) (64,128) in
   let t2:int128 = word_xor xl xh in
   let xm':int128 = word_xor t2 (word_xor t1 xm) in
   let red1:int128 = word_pmul (word_subword xl (0,64):(64)word) (word 0xc200000000000000:(64)word) in
   let xh':int128 = word_join (word_subword xh (64,64):(64)word) (word_subword xm' (64,64):(64)word) in
   let xl_rot:int128 = word_join (word_subword xl (0,64):(64)word) (word_subword xm' (0,64):(64)word) in
   let phase1:int128 = word_xor red1 xl_rot in
   let t3:int128 = word_subword (word_join phase1 phase1:(256)word) (64,128) in
   let red2:int128 = word_pmul (word_subword phase1 (0,64):(64)word) (word 0xc200000000000000:(64)word) in
   let t3':int128 = word_xor xh' t3 in
   let phase2:int128 = word_xor t3' red2 in
   let result_rev:int128 = word_reversefields 8 phase2 in
   result_rev`;;

(* ---- Test vectors for gcm_gmult_spec ----------------------------------- *)

(* Shared proof tactic: expand spec, beta-reduce, simplify subwords,
   then fully evaluate word operations and polynomial multiplications. *)
let GCM_GMULT_TEST_TAC =
  REWRITE_TAC[gcm_gmult_spec; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV (WORD_RED_CONV ORELSEC WORD_PMUL_CONV));;

(* Test 0: zero input always yields zero output *)
let GCM_GMULT_TEST_ZERO = prove(
  `gcm_gmult_spec (word 0:(128)word)
                   (word 0:(128)word)
                   (word 0:(128)word) =
   (word 0:(128)word)`,
  GCM_GMULT_TEST_TAC);;

(* Test 1: input byte values derived from NIST SP 800-38D, Appendix B,
     Test Case 2 (McGrew & Viega). H = 66e94bd4...2b2e, C = 0388dace...fe78.
     These are the little-endian 128-bit word representations.
     The expected output is computed by evaluating the spec, not taken
     directly from the NIST document (the htable format differs).
     xi = 0x78feb271b9c228f392a3b660ceda8803
     h  = 0x2e2b34ca59fa4c883b2c8aefd44be966
     hhl = 0x1507be258db1a5ee *)
let GCM_GMULT_TEST_1 = prove(
  `gcm_gmult_spec (word 0x78feb271b9c228f392a3b660ceda8803:(128)word)
                   (word 0x2e2b34ca59fa4c883b2c8aefd44be966:(128)word)
                   (word 0x1507be258db1a5ee:(128)word) =
   (word 0xf1b3db4c76b5a38114e7cce1360c534a:(128)word)`,
  GCM_GMULT_TEST_TAC);;

(* Test 2: mixed inputs *)
let GCM_GMULT_TEST_2 = prove(
  `gcm_gmult_spec (word 0xdeadbeef00112233aabbccdd44556677:(128)word)
                   (word 0x0102030405060708090a0b0c0d0e0f10:(128)word)
                   (word 0x0c060a04080e0210:(128)word) =
   (word 0x3950d31d1937a36a220b6f0b98977b79:(128)word)`,
  GCM_GMULT_TEST_TAC);;

(* Test 3: all-ones xi and h, zero hhl *)
let GCM_GMULT_TEST_3 = prove(
  `gcm_gmult_spec (word 0xffffffffffffffffffffffffffffffff:(128)word)
                   (word 0xffffffffffffffffffffffffffffffff:(128)word)
                   (word 0x0:(128)word) =
   (word 0x5555555555555555555555555555017a:(128)word)`,
  GCM_GMULT_TEST_TAC);;
