(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas on the prefix of HashML-DSA with SHAKE256, 1 || ctxlen || ctx ||   *)
(* OID || PH, that the functions mldsa{44,65,87}_{signature,verify}_pre_hash *)
(* _shake256 of the clang23_O3_mono_reduced_ram image build in a buffer on   *)
(* the stack with stores, after the call of memcpy for the context: the      *)
(* prefix as a number from the pieces in memory.                             *)
(* ========================================================================= *)

needs "arm/proofs/utils/mldsa_native_wrap.ml";;
needs "arm/proofs/utils/mldsa_native_prefix.ml";;
needs "common/fips202/properties/keccak_fips202.ml";;

(*** The OID of SHAKE256 (hashalg = 12), 11 bytes, as a number ***)

let MLD_SPHS_OID12_NUM = prove
 (`num_of_bytelist(mld_prehash_oid 12) = 14516628599920749990381830`,
  REWRITE_TAC[mld_prehash_oid] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[num_of_bytelist; VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV);;

let MLD_SPHS_OID12_LEN = prove
 (`LENGTH(mld_prehash_oid 12) = 11`,
  REWRITE_TAC[mld_prehash_oid] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(*** The prefix of a context of at most 255 bytes and a pre-hash of 64 bytes
     as a number: 1, ctxlen, ctx, the OID and the pre-hash ***)

let MLD_SPHS_PREFIX_NUM = prove
 (`!ctxlen C PH.
        ctxlen <= 255 /\ C < 256 EXP ctxlen /\ PH < 256 EXP 64
        ==> num_of_bytelist(mld_domain_separation_prefix 12
              (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) =
            1 + 256 * ctxlen + 2 EXP 16 * C +
            2 EXP (16 + 8 * ctxlen) *
            (14516628599920749990381830 + 2 EXP 88 * PH)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `ctxlen:num` MLD_PREFIX_VAL_BYTE) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[mld_domain_separation_prefix; LENGTH_BYTELIST_OF_NUM; ARITH_EQ] THEN
  REWRITE_TAC[num_of_bytelist; NUM_OF_BYTELIST_APPEND; LENGTH_BYTELIST_OF_NUM;
              LENGTH_APPEND; MLD_SPHS_OID12_LEN; MLD_SPHS_OID12_NUM] THEN
  ASM_SIMP_TAC[NUM_OF_BYTELIST_OF_NUM_EQ; ARITH_RULE `256 EXP 64 = 2 EXP 512`] THEN
  ASM_REWRITE_TAC[EXP_ADD] THEN
  SUBGOAL_THEN `val(word 1:byte) = 1` (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `8 * 11 = 88`] THEN CONV_TAC NUM_RING);;

(*** The buffer at a is the prefix if its pieces are: the two bytes 1 and
     ctxlen, the context, the 11 bytes of the OID and the pre-hash ***)

let MLD_SPHS_PREFIX_MEM = prove
 (`!(a:int64) ctxlen C PH (s:armstate).
      read (memory :> bytes(a,2)) s = 1 + 256 * ctxlen /\
      read (memory :> bytes(word_add a (word 2),ctxlen)) s = C /\
      read (memory :> bytes(word_add a (word (2 + ctxlen)),11)) s =
        14516628599920749990381830 /\
      read (memory :> bytes(word_add a (word (13 + ctxlen)),64)) s = PH
      ==> read (memory :> bytes(a,ctxlen + 77)) s =
          1 + 256 * ctxlen + 2 EXP 16 * C +
          2 EXP (16 + 8 * ctxlen) *
          (14516628599920749990381830 + 2 EXP 88 * PH)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ctxlen + 77 = 2 + (ctxlen + (11 + 64))` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MLD_PREFIX_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
              ARITH_RULE `2 + ctxlen + 11 = 13 + ctxlen`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXP_ADD; ARITH_RULE `8 * (11 + 64) = 600`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `8 * 11 = 88`; ARITH_RULE `8 * 2 = 16`] THEN
  CONV_TAC NUM_RING);;
