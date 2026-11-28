(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bridges from the scalar x86 SHA-512 instruction idioms to the spec        *)
(* primitives of x86/proofs/utils/sha512_spec.ml.                            *)
(*                                                                           *)
(* The Ragamuffin/OpenSSL scalar code computes each FIPS 180-4 primitive by  *)
(* a characteristic rotate/xor/shift chain on 64-bit registers.  The rotate  *)
(* and shift amounts below were decoded directly from the frozen object      *)
(* x86/sha512/sha512_compress.o (head round 0 at 0x07b and the first inner   *)
(* sub-round at 0x71f); see orchestrator/logs/sha512-phase0-facts.md.        *)
(*                                                                           *)
(*   Sigma1(e):  ror 23; xor e; ror 4;  xor e; ror 14   = ROTR14^18^41       *)
(*   Sigma0(a):  ror 5;  xor a; ror 6;  xor a; ror 28   = ROTR28^34^39       *)
(*   Ch(e,f,g):  ((f ^ g) & e) ^ g                                           *)
(*   Maj(a,b,c): b ^ ((b ^ c) & (a ^ b))   [b ^ c carried between rounds]    *)
(*   sigma0(w):  ror(ror(w,7) ^ w, 1)  ^ (w >> 7)       = ROTR1^8^SHR7       *)
(*   sigma1(w):  ror(ror(w,42) ^ w, 19) ^ (w >> 6)      = ROTR19^61^SHR6     *)
(*                                                                           *)
(* Each lemma equates the raw chain (as symbolic execution produces it)      *)
(* with the spec primitive.  They are used only at cut-points, never during  *)
(* stepping.  (The exact operand order of the chains as they emerge from     *)
(* stepping is confirmed in the Phase-4 head-round proof; word_and/word_xor  *)
(* are commutative so the WORD_BLAST equivalence holds for either order.)    *)
(* ========================================================================= *)

needs "x86/proofs/utils/sha512_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The big Sigma functions as rotate-xor chains.                             *)
(* ------------------------------------------------------------------------- *)

let SHA512_SIGMA1_BRIDGE = prove
 (`!e:int64.
     word_ror (word_xor (word_ror (word_xor (word_ror e 23) e) 4) e) 14 =
     sha512_hash_sigma_1 e`,
  REWRITE_TAC[sha512_hash_sigma_1] THEN CONV_TAC WORD_BLAST);;

let SHA512_SIGMA0_BRIDGE = prove
 (`!a:int64.
     word_ror (word_xor (word_ror (word_xor (word_ror a 5) a) 6) a) 28 =
     sha512_hash_sigma_0 a`,
  REWRITE_TAC[sha512_hash_sigma_0] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Choose and majority as the and-xor chains.                                *)
(* ------------------------------------------------------------------------- *)

let SHA512_CHOOSE_BRIDGE = prove
 (`!e f g:int64.
     word_xor (word_and (word_xor f g) e) g = sha512_choose e f g`,
  REWRITE_TAC[sha512_choose]);;

let SHA512_MAJ_BRIDGE = prove
 (`!a b c:int64.
     word_xor b (word_and (word_xor b c) (word_xor a b)) = sha512_maj a b c`,
  REWRITE_TAC[sha512_maj] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* The message-schedule small sigma functions as rotate-shift chains.        *)
(* ------------------------------------------------------------------------- *)

let SHA512_MSG_SIGMA0_BRIDGE = prove
 (`!w:int64.
     word_xor (word_ushr w 7) (word_ror (word_xor (word_ror w 7) w) 1) =
     sha512_msg_sigma_0 w`,
  REWRITE_TAC[sha512_msg_sigma_0] THEN CONV_TAC WORD_BLAST);;

let SHA512_MSG_SIGMA1_BRIDGE = prove
 (`!w:int64.
     word_xor (word_ror (word_xor (word_ror w 42) w) 19) (word_ushr w 6) =
     sha512_msg_sigma_1 w`,
  REWRITE_TAC[sha512_msg_sigma_1] THEN CONV_TAC WORD_BLAST);;
