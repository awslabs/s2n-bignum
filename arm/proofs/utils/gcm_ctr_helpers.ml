(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)
(* ========================================================================= *)
(* Shared AES-GCM counter-mode helpers (binary-agnostic spec layer).         *)
(*                                                                            *)
(* This file is the "shared spec home" (counter core) for the AES-GCM        *)
(* encrypt/decrypt proofs.  It collects the per-block CTR increment used by   *)
(* the ARM binary (gcm_ctr_inc), its lane-byte form (GCM_CTR_INC_LANES), the  *)
(* NIST SP 800-38D inc32 and the byteswap bridge between them, and a defined  *)
(* counter iterator (gcm_ctr_inc_iter) so block k's counter composes in a     *)
(* recursion / N-block induction.                                            *)
(*                                                                            *)
(* Provenance / coordination (see                                            *)
(*   _docs/aesv8-gcm-nblock-generalization-plan-20260617.md):                 *)
(*  - gcm_ctr_inc + GCM_CTR_INC_LANES are lifted VERBATIM (byte-identical)    *)
(*    from arm/proofs/aesv8_gcm_8x_enc_256_2block.ml so that file can later   *)
(*    drop its inline copies and `needs` this one as a no-op.  Same def as    *)
(*    Mila's gcm_ctr_inc in manastasova/s2n-bignum-dev@756df852               *)
(*    arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml (coordinate names verbatim*)
(*    so a future merge is a no-op -- cf. plan R5).                           *)
(*  - inc32 is COPIED verbatim from awslabs/s2n-bignum PR#389                 *)
(*    (sgmenda:gcm-spec@2f81c762, common/gcm.ml); see the BEGIN/END block.     *)
(*                                                                            *)
(* No CHEAT_TAC, no new axioms.  Depends only on base.ml (word primitives).   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(* ========================================================================= *)
(* The AES-GCM counter increment (the ARM binary's rev32+ADD+rev32).          *)
(*                                                                            *)
(* gcm_ctr_inc ivec = ivec with its top 32-bit lane byte-reversed, +1, and    *)
(* byte-reversed back.  Lifted verbatim from                                  *)
(* arm/proofs/aesv8_gcm_8x_enc_256_2block.ml (and matching Mila's def at      *)
(* manastasova/s2n-bignum-dev@756df852 .../gcm_aesgcm_nblock_helpers.ml#L38). *)
(* ========================================================================= *)

let gcm_ctr_inc = new_definition
 `gcm_ctr_inc (ivec:(128)word) : (128)word =
   word_insert ivec (96,32)
     (word_bytereverse
        (word_add (word_bytereverse
                     (word_subword ivec (96,32):(32)word))
                  (word 1:(32)word)))`;;

(* gcm_ctr_inc as the explicit per-byte lane-shuffle the front simulation     *)
(* emits (rev32 of the top lane incremented, low 96 bits unchanged, all built  *)
(* from 8-bit subwords of ctr0).  One BITBLAST (~1s); used to fold the spec     *)
(* var ctr1 to the form the Q9 keystream readback carries.                     *)
(* Lifted VERBATIM from aesv8_gcm_8x_enc_256_2block.ml.                         *)
let GCM_CTR_INC_LANES = prove(
 `!ctr0:int128.
    gcm_ctr_inc ctr0 =
    word_join
    (word_join
     (word_join
      (word_join
       (word_subword
        (word_add
         (word_join
          (word_join (word_subword ctr0 (96,8):(8)word) (word_subword ctr0 (104,8):(8)word)
           :(16)word)
          (word_join (word_subword ctr0 (112,8):(8)word) (word_subword ctr0 (120,8):(8)word)
           :(16)word) :(32)word)
         (word 1:(32)word)) (0,8) :(8)word)
       (word_subword
        (word_add
         (word_join
          (word_join (word_subword ctr0 (96,8):(8)word) (word_subword ctr0 (104,8):(8)word)
           :(16)word)
          (word_join (word_subword ctr0 (112,8):(8)word) (word_subword ctr0 (120,8):(8)word)
           :(16)word) :(32)word)
         (word 1:(32)word)) (8,8) :(8)word) :(16)word)
      (word_join
       (word_subword
        (word_add
         (word_join
          (word_join (word_subword ctr0 (96,8):(8)word) (word_subword ctr0 (104,8):(8)word)
           :(16)word)
          (word_join (word_subword ctr0 (112,8):(8)word) (word_subword ctr0 (120,8):(8)word)
           :(16)word) :(32)word)
         (word 1:(32)word)) (16,8) :(8)word)
       (word_subword
        (word_add
         (word_join
          (word_join (word_subword ctr0 (96,8):(8)word) (word_subword ctr0 (104,8):(8)word)
           :(16)word)
          (word_join (word_subword ctr0 (112,8):(8)word) (word_subword ctr0 (120,8):(8)word)
           :(16)word) :(32)word)
         (word 1:(32)word)) (24,8) :(8)word) :(16)word) :(32)word)
     (word_join
      (word_join (word_subword ctr0 (88,8):(8)word) (word_subword ctr0 (80,8):(8)word) :(16)word)
      (word_join (word_subword ctr0 (72,8):(8)word) (word_subword ctr0 (64,8):(8)word) :(16)word)
      :(32)word) :(64)word)
    (word_join
     (word_join
      (word_join (word_subword ctr0 (56,8):(8)word) (word_subword ctr0 (48,8):(8)word) :(16)word)
      (word_join (word_subword ctr0 (40,8):(8)word) (word_subword ctr0 (32,8):(8)word) :(16)word)
      :(32)word)
     (word_join
      (word_join (word_subword ctr0 (24,8):(8)word) (word_subword ctr0 (16,8):(8)word) :(16)word)
      (word_join (word_subword ctr0 (8,8):(8)word) (word_subword ctr0 (0,8):(8)word) :(16)word)
      :(32)word) :(64)word) :(128)word`,
  GEN_TAC THEN REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;

(* ========================================================================= *)
(* NIST SP 800-38D inc32 and the byteswap bridge to gcm_ctr_inc.              *)
(* ========================================================================= *)

(* === BEGIN copied from awslabs/s2n-bignum PR#389 (sgmenda:gcm-spec@2f81c762) ===
   common/gcm.ml : inc32.  Self-contained (word primitives only, zero deps).
   REMOVE this copy and `needs "common/gcm.ml"` once PR#389 merges. *)
let inc32 = new_definition
 `inc32 (cb:128 word) : 128 word =
    let top96:96 word = word_subword cb (32,96) in
    let bot32:32 word = word_subword cb (0,32) in
    word_join top96 (word_add bot32 (word 1 : 32 word)) : 128 word`;;
(* === END copied from PR#389 === *)

(* @UPSTREAM-389?: INC32_GCM_CTR_INC -- the NIST inc32 <-> ARM gcm_ctr_inc     *)
(* counter bridge.  Spec-adjacent, but gcm_ctr_inc is an ARM-proof artifact;   *)
(* let the PR#389 authors decide whether the bridge lives upstream or here.    *)
(*                                                                            *)
(* Byte-order relationship: inc32 increments the LOW 32 bits of its argument   *)
(* (NIST big-endian counter), keeping the top 96; gcm_ctr_inc increments the   *)
(* TOP 32-bit lane viewed byte-reversed.  They are conjugate by a full 128-bit *)
(* byteswap: gcm_ctr_inc x = word_bytereverse (inc32 (word_bytereverse x)).    *)
let GCM_CTR_INC_INC32 = prove
 (`!x:128 word. gcm_ctr_inc x = word_bytereverse (inc32 (word_bytereverse x))`,
  GEN_TAC THEN REWRITE_TAC[gcm_ctr_inc; inc32] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN BITBLAST_TAC);;

(* ========================================================================= *)
(* The counter iterator: block k's CTR input is gcm_ctr_inc_iter k ctr0.      *)
(* Defined (not a tactic phrase) so it composes in a recursion / N-block      *)
(* induction.  Equals ITER k gcm_ctr_inc, so existing ITER lemmas apply.      *)
(* ========================================================================= *)

let gcm_ctr_inc_iter = define
 `gcm_ctr_inc_iter 0 (x:128 word) = x /\
  gcm_ctr_inc_iter (SUC k) (x:128 word) = gcm_ctr_inc (gcm_ctr_inc_iter k x)`;;

let GCM_CTR_INC_ITER_ITER = prove
 (`!k x:128 word. gcm_ctr_inc_iter k x = ITER k gcm_ctr_inc x`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[gcm_ctr_inc_iter; ITER]);;

(* Base case sanity: one increment = gcm_ctr_inc (the 2-block block-1 form).   *)
let GCM_CTR_INC_ITER_1 = prove
 (`!x:128 word. gcm_ctr_inc_iter 1 x = gcm_ctr_inc x`,
  REWRITE_TAC[ONE; gcm_ctr_inc_iter]);;

(* Iterator splits over +, so an N-block proof can peel one block at a time.   *)
let GCM_CTR_INC_ITER_ADD = prove
 (`!m n x:128 word.
     gcm_ctr_inc_iter (m + n) x = gcm_ctr_inc_iter m (gcm_ctr_inc_iter n x)`,
  REWRITE_TAC[GCM_CTR_INC_ITER_ITER; ITER_ADD]);;

(* @UPSTREAM-389?: the iterated NIST bridge.  Lets the spec state block k's    *)
(* counter NIST-faithfully (ITER k inc32 over the byteswapped ivec) while the  *)
(* proof folds the binary's lanes via gcm_ctr_inc_iter.                        *)
let GCM_CTR_INC_ITER_INC32 = prove
 (`!k x:128 word.
     gcm_ctr_inc_iter k x = word_bytereverse (ITER k inc32 (word_bytereverse x))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[gcm_ctr_inc_iter; ITER; WORD_BYTEREVERSE_BYTEREVERSE];
    ASM_REWRITE_TAC[gcm_ctr_inc_iter; ITER; GCM_CTR_INC_INC32;
                    WORD_BYTEREVERSE_BYTEREVERSE]]);;
