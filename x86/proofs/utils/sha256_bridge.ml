(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bridges from the scalar x86 SHA-256 instruction idioms to the spec        *)
(* primitives of x86/proofs/utils/sha256_spec.ml.                            *)
(*                                                                           *)
(* The implementation computes each FIPS 180-4 primitive by a                *)
(* rotate/xor/shift chain on 32-bit registers:                               *)
(*                                                                           *)
(*   Sigma1(e): ror 14; xor e; ror 5; xor e; ror 6                           *)
(*   Sigma0(a): ror 9;  xor a; ror 11; xor a; ror 2                          *)
(*   Ch(e,f,g): ((f ^ g) & e) ^ g                                            *)
(*   Maj(a,b,c): b ^ ((b ^ c) & (a ^ b))   [b ^ c carried between rounds]    *)
(*   sigma0(w): ror(ror(w,11) ^ w, 7) ^ (w >> 3)                             *)
(*   sigma1(w): ror(ror(w,2) ^ w, 17) ^ (w >> 10)                            *)
(*                                                                           *)
(* Each lemma equates the raw chain (as symbolic execution produces it)      *)
(* with the spec primitive. They are used only at cut-points, never during   *)
(* stepping.                                                                 *)
(* ========================================================================= *)

needs "x86/proofs/utils/sha256_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The big Sigma functions as rotate-xor chains.                             *)
(* ------------------------------------------------------------------------- *)

let SHA256_SIGMA1_BRIDGE = prove
 (`!e:int32.
     word_ror (word_xor (word_ror (word_xor (word_ror e 14) e) 5) e) 6 =
     sha_hash_sigma_1 e`,
  REWRITE_TAC[sha_hash_sigma_1] THEN CONV_TAC WORD_BLAST);;

let SHA256_SIGMA0_BRIDGE = prove
 (`!a:int32.
     word_ror (word_xor (word_ror (word_xor (word_ror a 9) a) 11) a) 2 =
     sha_hash_sigma_0 a`,
  REWRITE_TAC[sha_hash_sigma_0] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Choose and majority as the and-xor chains.                                *)
(* ------------------------------------------------------------------------- *)

let SHA256_CHOOSE_BRIDGE = prove
 (`!e f g:int32.
     word_xor (word_and (word_xor f g) e) g = sha_choose e f g`,
  REWRITE_TAC[sha_choose]);;

let SHA256_MAJ_BRIDGE = prove
 (`!a b c:int32.
     word_xor b (word_and (word_xor b c) (word_xor a b)) = sha_maj a b c`,
  REWRITE_TAC[sha_maj] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* The message-schedule small sigma functions as rotate-shift chains.        *)
(* ------------------------------------------------------------------------- *)

let SHA256_MSG_SIGMA0_BRIDGE = prove
 (`!w:int32.
     word_xor (word_ushr w 3) (word_ror (word_xor (word_ror w 11) w) 7) =
     sha_msg_sigma_0 w`,
  REWRITE_TAC[sha_msg_sigma_0] THEN CONV_TAC WORD_BLAST);;

let SHA256_MSG_SIGMA1_BRIDGE = prove
 (`!w:int32.
     word_xor (word_ror (word_xor (word_ror w 2) w) 17) (word_ushr w 10) =
     sha_msg_sigma_1 w`,
  REWRITE_TAC[sha_msg_sigma_1] THEN CONV_TAC WORD_BLAST);;
