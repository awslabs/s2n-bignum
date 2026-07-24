(* ========================================================================= *)
(* JRH-style AES tower reconstruction lemmas, shared across the AES-GCM      *)
(* decrypt chain (wb bands, NIST convergence layer, future main-loop proof). *)
(*                                                                           *)
(* The machine leaves per-block keystreams as raw 14-round aese/aesmc        *)
(* towers; these lemmas fold them onto the aes256_encrypt spec once, so      *)
(* every capture site is a rewrite instead of a per-site unfold + blast      *)
(* (the AES128_CIPHER_RECONSTRUCT pattern from jargh's x4 kernels).          *)
(*                                                                           *)
(* Hoisted verbatim from arm/proofs/aesv8_gcm_8x_dec_256_wb.ml.              *)
(* ========================================================================= *)

needs "arm/proofs/utils/aes_encrypt_spec.ml";;

(* The machine's 14-round aese/aesmc keystream tower XOR (k14 xor cph) equals
   the spec keystream XOR: proved ONCE, so every per-block plaintext capture is
   a rewrite (replaces the per-site aes256_encrypt unfold + WORD_BLAST). *)
let AES256_XOR_ENCRYPT_RECONSTRUCT = prove
 (`!ctr cph k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14:int128.
    word_xor
     (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese
       (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
       (aese ctr k0) ) k1) ) k2) ) k3) ) k4) ) k5) ) k6) ) k7) ) k8) ) k9) ) k10) ) k11) ) k12) ) k13)
     (word_xor k14 cph) =
    word_xor cph (aes256_encrypt ctr [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
  REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC WORD_BLAST);;

(* The named 13-round partial tower (the keystream register shape at the
   shared-front seam: rounds 0..12 + the final aese, NO 14th-key xor -- that
   xor happens per-block in the tail eor3).  Naming it collapses in-flight
   front-postcondition Q towers from ~2.6k chars each to one application, and
   the reconstruct lemma below keeps every tail capture site working on the
   folded form. *)
let aes13 = new_definition
 `aes13 (p:int128) (k0:int128) (k1:int128) (k2:int128) (k3:int128) (k4:int128)
        (k5:int128) (k6:int128) (k7:int128) (k8:int128) (k9:int128) (k10:int128)
        (k11:int128) (k12:int128) (k13:int128) : int128 =
    aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese
      (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
      (aese p k0) ) k1) ) k2) ) k3) ) k4) ) k5) ) k6) ) k7) ) k8) ) k9) ) k10) ) k11) ) k12) ) k13`;;

(* All tail capture sites rewrite with GSYM of this; rebinding it over aes13
   keeps them verbatim while the front postcondition stays folded. *)
let AES256_XOR_ENCRYPT_RECONSTRUCT =
  REWRITE_RULE[GSYM aes13] AES256_XOR_ENCRYPT_RECONSTRUCT;;
