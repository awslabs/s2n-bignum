(* ========================================================================= *)
(* Bridge: Mila's aes256_block_enc  ==  the AES-XTS aes256_encrypt.            *)
(*                                                                            *)
(* The two AES-256 single-block keystream models in the tree compute the same *)
(* function but are stated differently:                                       *)
(*                                                                            *)
(*  - aes256_block_enc (manastasova .../aes256_gcm_block_enc_spec.ml): flat    *)
(*    15-register-arg `aesmc (aese ...)` tower, matching the ARM AESE+AESMC    *)
(*    instruction sequence (each round key folded INSIDE the next `aese`).     *)
(*                                                                            *)
(*  - aes256_encrypt (arm/proofs/utils/aes_encrypt_spec.ml): the AES-XTS       *)
(*    substrate, `int128 list` keys + `aes256_encrypt_round` fold (round key   *)
(*    XORed at the END of each round), last round split into                   *)
(*    aes_shift_rows / aes_sub_bytes / word_xor.                               *)
(*                                                                            *)
(* They differ ONLY in where each round key is added (inside the next aese vs  *)
(* at the end of the round); unfolding aese/aesmc and let-reducing both sides  *)
(* makes them syntactically identical -- no GF(2^8) reasoning needed.          *)
(*                                                                            *)
(* This is the gating lemma for sharing ONE AES block primitive between the    *)
(* GCM and XTS proofs (handback doc divergence D2).  Put this in a shared      *)
(* common/ or arm/proofs/utils/ home so neither tree carries two AES models.   *)
(* ========================================================================= *)

needs "common/aes.ml";;                          (* aese, aesmc, aes_* round helpers     *)
needs "arm/proofs/utils/aes_encrypt_spec.ml";;   (* aes256_encrypt, aes256_encrypt_round, EL_15_128_CLAUSES *)

(* Mila's primitive (verbatim from manastasova/s2n-bignum-dev@b2b19c83,
   arm/proofs/utils/aes256_gcm_block_enc_spec.ml).  Included here so this file
   is self-contained; delete this copy once the two trees share one home. *)
let aes256_block_enc = new_definition
  `aes256_block_enc (input:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word) : (128)word =
   let s0 = aesmc (aese input rk0) in
   let s1 = aesmc (aese s0 rk1) in
   let s2 = aesmc (aese s1 rk2) in
   let s3 = aesmc (aese s2 rk3) in
   let s4 = aesmc (aese s3 rk4) in
   let s5 = aesmc (aese s4 rk5) in
   let s6 = aesmc (aese s5 rk6) in
   let s7 = aesmc (aese s6 rk7) in
   let s8 = aesmc (aese s7 rk8) in
   let s9 = aesmc (aese s8 rk9) in
   let s10 = aesmc (aese s9 rk10) in
   let s11 = aesmc (aese s10 rk11) in
   let s12 = aesmc (aese s11 rk12) in
   let s13 = aese s12 rk13 in
   word_xor s13 rk14`;;

(* The bridge.  One-shot: unfold both, rewrite aese/aesmc, let-reduce, REFL. *)
let AES256_BLOCK_ENC_EQ_ENCRYPT = prove
 (`!input k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14.
     aes256_block_enc input k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 =
     aes256_encrypt input [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[aes256_block_enc; aes256_encrypt] THEN
  REWRITE_TAC EL_15_128_CLAUSES THEN
  REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REFL_TAC);;
