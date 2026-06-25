(* ========================================================================= *)
(* Shared AES-256 block-cipher unfolding lemma for the AES-256-GCM proofs.    *)
(*                                                                           *)
(* The GCM proofs encrypt each counter block with the upstream math-level     *)
(* aes256_encrypt (arm/proofs/utils/aes_encrypt_spec.ml), but symbolic        *)
(* execution of the AESE+AESMC instruction sequence leaves the keystream as   *)
(* an aese/aesmc composition.  AES256_ENCRYPT_UNFOLD bridges the two: it      *)
(* rewrites aes256_encrypt (applied to a literal 15-element round-key list)   *)
(* into exactly that instruction-shaped chain:                                *)
(*   Rounds 0-12: aesmc(aese(state, rk_i))                                  *)
(*   Round 13:    aese(state, rk13)  (no MixColumns)                         *)
(*   Final:       XOR with rk14                                              *)
(*                                                                           *)
(* This is the AES keystream rewrite reused by every aes256_gcm_<N>_block     *)
(* proof (via gcm_aesgcm_helpers.ml).                                          *)
(* ========================================================================= *)

needs "common/aes.ml";;
needs "arm/proofs/aes.ml";;
needs "arm/proofs/utils/aes_encrypt_spec.ml";;

let AES256_ENCRYPT_UNFOLD = prove
 (`!(input:(128)word)
     (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
     (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
     (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
     (rk12:(128)word) (rk13:(128)word) (rk14:(128)word).
     aes256_encrypt input
       [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] =
     (let s0 = aesmc (aese input rk0) in
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
      word_xor s13 rk14)`,
  REWRITE_TAC[aes256_encrypt; aes256_encrypt_round; aese; aesmc;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;
