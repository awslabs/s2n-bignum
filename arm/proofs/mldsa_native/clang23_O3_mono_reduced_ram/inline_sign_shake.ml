(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The SHAKE256 of pk that clang 23 -O3 has inlined into                      *)
(* mldsa44_verify_internal for tr = H(pk, 64), from in_shake256_init         *)
(* (+0xae8) to the bl of mld_H44 (+0x1600): the instance SHAKE44_INST of the *)
(* lemma of inline_sign_shake_gen.ml. The state at F + 2496 is zeroed and    *)
(* the 1312 bytes of pk are XORed into it with a call of keccakf1600_permute *)
(* after each of the 9 full blocks; the last 11 lanes, the padding bytes     *)
(* 0x1F at byte 88 and 0x80 at byte 135, the permutation, the copy of the    *)
(* first 64 bytes of the state to tr at F + 3552, the arguments of mld_H44   *)
(* and the zeroing of the state. The proof takes about 30 minutes.           *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_shake_gen.ml";;

let INLINE_SHAKE44_TERM = INLINE_SHAKE_TERM SHAKE44_INST;;

let INLINE_SHAKE44 = INLINE_SHAKE_PROVE SHAKE44_INST;;
