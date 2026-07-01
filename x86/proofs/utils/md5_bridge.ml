(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Layer-2 bridge lemmas for the x86-64 MD5 block-compression proof.         *)
(*                                                                           *)
(* The assembly computes the four MD5 auxiliary functions F/G/H/I in         *)
(* algebraically-optimized bit-op forms that differ from the canonical       *)
(* RFC 1321 forms of the Layer-1 spec (md5_spec.ml).  Each lemma proves      *)
(* `asm-form = spec-form` by bit-blasting, so the `ensures` proofs can       *)
(* refold raw hardware bit-op terms into md5_f/g/h/i at cut points.          *)
(*                                                                           *)
(* The asm forms below are read off the frozen instruction bytes in          *)
(* x86/proofs/md5_compress.ml (the bytes are the ground truth,               *)
(* not C-macro prose).  With a,b,c,d the working words:                      *)
(*                                                                           *)
(*  F (rounds 0..15):  mov d,t ; xor c,t ; and b,t ; xor d,t                 *)
(*      => ((d XOR c) AND b) XOR d, one register.                            *)
(*                                                                           *)
(*  G (rounds 16..31): G is never materialized in one register; two AND      *)
(*    terms are added into the accumulator separately:                       *)
(*      mov d,t1 ; not t1 ; and c,t1     (= ~d AND c)                        *)
(*      mov d,t2 ;          and b,t2     (=  d AND b)                        *)
(*      ... add t1,acc ... add t2,acc                                        *)
(*    Bit i of d selects exactly one of the two ANDs, so they have disjoint  *)
(*    set bits and their sum equals their OR, i.e. md5_g: a SUM identity.    *)
(*    Both the textbook operand order (c AND ~d) + (b AND d) and the asm     *)
(*    operand order (~d AND c) + (d AND b) are proved -- AND-commutativity   *)
(*    is not a WORD_RULE ring identity, so the refold atoms must match the   *)
(*    stepper output exactly.                                                *)
(*                                                                           *)
(*  H (rounds 32..47): mov c,t ; xor d,t ; xor b,t  =>  (c XOR d) XOR b.     *)
(*                                                                           *)
(*  I (rounds 48..63): mov $0xffffffff,t ; xor d,t ; or b,t ; xor c,t        *)
(*      =>  ((0xffffffff XOR d) OR b) XOR c    (0xffffffff XOR d = ~d).      *)
(* ========================================================================= *)

needs "x86/proofs/utils/md5_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* F: ((d XOR c) AND b) XOR d  =  md5_f b c d.                               *)
(* ------------------------------------------------------------------------- *)

let MD5_F_BRIDGE = prove
 (`!b c d:int32. word_xor (word_and (word_xor d c) b) d = md5_f b c d`,
  REWRITE_TAC[md5_f] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* G, textbook operand order: (c AND ~d) + (b AND d)  =  md5_g b c d.        *)
(* ------------------------------------------------------------------------- *)

let MD5_G_BRIDGE = prove
 (`!b c d:int32.
     word_add (word_and c (word_not d)) (word_and b d) = md5_g b c d`,
  REWRITE_TAC[md5_g] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* G, asm operand order: (~d AND c) + (d AND b)  =  md5_g b c d.  This is    *)
(* the form the stepper actually produces (NOT %r11d before AND %ecx,%r11d). *)
(* ------------------------------------------------------------------------- *)

let MD5_G_BRIDGE_ASM = prove
 (`!b c d:int32.
     word_add (word_and (word_not d) c) (word_and d b) = md5_g b c d`,
  REWRITE_TAC[md5_g] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* H: (c XOR d) XOR b  =  md5_h b c d.                                       *)
(* ------------------------------------------------------------------------- *)

let MD5_H_BRIDGE = prove
 (`!b c d:int32. word_xor (word_xor c d) b = md5_h b c d`,
  REWRITE_TAC[md5_h] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* I: ((0xffffffff XOR d) OR b) XOR c  =  md5_i b c d.  The constant is the  *)
(* asm's `mov $0xffffffff,%r11d` materialization of ~0.                      *)
(* ------------------------------------------------------------------------- *)

let MD5_I_BRIDGE = prove
 (`!b c d:int32.
     word_xor (word_or (word_xor (word 0xffffffff) d) b) c = md5_i b c d`,
  REWRITE_TAC[md5_i] THEN CONV_TAC WORD_BLAST);;
