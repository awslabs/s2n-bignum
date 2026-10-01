(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Functional correctness, constant-time and memory-safety proofs of the      *)
(* AES-128-GCM bulk encryption kernel aes128_gcm_enc.                         *)
(*                                                                           *)
(* The kernel processes a whole number of 16-byte blocks: each block is       *)
(* encrypted in counter mode, the ciphertext is folded into the GHASH         *)
(* authenticator, and the counter and authenticator are written back.  Its   *)
(* main four-block loop is software-pipelined, so the proof works from a      *)
(* single mid-pipeline loop invariant (swp_inv, asserted at the loop head     *)
(* pc+0x1ec) driving one ENSURES_WHILE, with fill and drain legs, the          *)
(* single-block tail loop, and separate legs for the degenerate loop counts.  *)
(* The core theorem AES128_GCM_ENC_CORRECT (pc+0x2c to pc+0x710) is wrapped   *)
(* into AES128_GCM_ENC_SUBROUTINE_CORRECT; the safety theorems follow the     *)
(* same leg structure with the event-tracking simulator.                      *)
(*                                                                           *)
(* The lemma substrate shared with the other three AES-GCM proofs (counter,   *)
(* AES and GHASH-reduce reconstruction, the pipelined stepper, the safety     *)
(* closers) lives in aes_gcm_utils.ml.                                        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/fips197.ml";;
needs "common/polyval_ghash.ml";;
needs "common/ghash_nist_bridge.ml";;
needs "common/karatsuba_pmul.ml";;
needs "arm/proofs/aes_gcm_utils.ml";;

(* ------------------------------------------------------------------------- *)
(* Scalar counter representation.  Unlike the vector-IV kernels, this variant *)
(* keeps the counter block in scalar registers: after "ldp x11,x12,[x4]" the *)
(* two 64-bit halves of the (little-endian) IV live in X11 (low) and X12      *)
(* (high); the running counter is byte-reversed out of X12's top word into    *)
(* X13.  The loop rebuilds the reversed counter block via                     *)
(*   w14 = rev(w13);  x14 = orr x12 (w14 lsl 32);  Q0 = word_join x14 x11.     *)
(* These lemmas connect that scalar reconstruction back to ctr_block.         *)

(* Given the initial IV halves (join = reversed ctr_block for counter 2), the *)
(* loop-built block for any counter value equals the reversed ctr_block.      *)

(* Closed form: with X11/X12 written as (counter-free) subwords of the reversed
   ctr_block for the canonical counter 2, the loop-built block for counter cval
   equals the reversed ctr_block for cval.  This is what the loop body invokes. *)

(* Epilogue byte-splice: the final "str w14,[x4,#12]" overwrites only the top 4 bytes *)
(* of the ivec (the byte-reversed counter word); the low 12 bytes keep their initial  *)
(* value (the reversed nonce from ctr_block nonce c).  Recombining gives the reversed *)
(* ctr_block for the final counter value.                                             *)

(* Same splice phrased for the 64/64 then 32/32 decomposition of the 128-bit ivec    *)
(* read (which is how READ_MEMORY_BYTESIZED_SPLIT breaks it): the stored counter word *)
(* is the top 32 bits of the high 64-bit half, the rest is the unchanged nonce.       *)

(* After the 32-bit-cell split (and collapsing the word_zx conversion chain with     *)
(* ZX_COUNTER_UD), the counter cell (offset 12) is word_bytereverse(word c), which    *)
(* equals the top 32 bits of the reversed ctr_block.                                  *)

(* The low three 32-bit cells of the reversed ivec (the nonce) are independent of the *)
(* counter value, so they still hold their initial (counter-2) contents.              *)

(* Split a 128-bit input-block memory read into two 64-bit halves whose addresses  *)
(* are folded back to the canonical "in_p + word(off)" form.  The scalar_rk final  *)
(* round loads each input block as scalars via "ldp x22,x23,[x0,#K]", i.e. it reads *)
(* the block's two 64-bit halves at x0+K and x0+K+8.  READ_MEMORY_SPLIT_CONV emits  *)
(* the high half at address (in_p + word off) + word 8; the simulator's memory      *)
(* lookup will not match that against x0+K+8 unless we renormalise it to            *)
(* in_p + word(off+8).  NORMALIZE_RELATIVE_ADDRESS_CONV reassociates and GSYM       *)

(* Tail-loop variant of the input split.  The tail block is loaded by the         *)
(* POST-INDEXED "ldp x22,x23,[x0],#16": the ARM model reads the second register    *)
(* x23 from address in_p + word((64*loop_count + 16*i) + 8) — the "+ 8" stays a    *)
(* separate num-level summand because the block offset (64*loop_count + 16*i) has   *)
(* a symbolic i, so NUM_ADD_CONV cannot fold it.  The plain SPLIT + NORMALISE (no   *)
(* ADD_ASSOC/NUM fold) reproduces exactly that address form, letting the           *)
(* post-indexed load resolve x23 (offset-mode loads in the main loop DO fold, hence *)

(* In the scalar_rk variant the final AES round key (EL 10) is XORed in scalar    *)
(* registers X20/X21 into the input block halves, and the block ciphertext is     *)
(* word_xor (word_join <input_hi ^ key10_hi> <input_lo ^ key10_lo>) (9-round Q0). *)
(* This lemma rewrites that scalar-built form into the word_xor <9round>           *)
(* (word_xor rk10 inblock) shape that XOR_AES128_CIPHER_RECONSTRUCT consumes,      *)
(* with rk10 = word_reversefields 8 (EL 10 rk) and inblock = word_join of the      *)
(* input halves.  Both operand orders of the outer word_xor are covered: the       *)
(* ciphertext-output copy keeps the (word_join ... ) nineround order from the       *)
(* "eor v0,v29,v0", while the GHASH-accumulated copy has the operands commuted by   *)

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem.                                                 *)
(*                                                                           *)
(* This covers the body of the function with the save/restore boilerplate    *)
(* excised: PC starts at pc + 0x2c (first real instruction after the 11      *)
(* save instructions) and ends at pc + 0x448 (first ldp of the postamble).   *)
(* The stackpointer is the value AFTER the sub sp, #0xe0 adjustment, i.e.    *)
(* the value the SP register actually holds inside the function body.        *)
(*                                                                           *)
(* Arguments (Standard ARM ABI, values in registers at core entry):          *)
(*   X0 = in        input buffer (len_bits/8 bytes)                          *)
(*   X1 = len_bits  length in bits (whole 16-byte blocks)                    *)
(*   X2 = out       output buffer (len_bits/8 bytes)                         *)
(*   X3 = tag       16-byte GHASH accumulator (in/out)                       *)
(*   X4 = ivec      16-byte counter block (in/out)                           *)
(*   X5 = key       AES-128 round keys (176 bytes = 11 x 16)                 *)
(*   X6 = Htable    192-byte precomputed H-powers table                      *)
(*   returns X0 = byte_len (= len_bits / 8)                                  *)
(* ------------------------------------------------------------------------- *)

(*** Note that the NIST-level specs consider all byte-level encodings as
 *** big-endian, and the AES-related ARM instructions take that view too.
 *** Hence in the precondition "ctr_block" and "rk" correspond as 128-bit
 *** words to the NIST specifications. Since they are loaded from memory
 *** in the usual little-endian ARM fashion, we byte-reverse when
 *** specifying them as the values in any memory cells.
 ***)


(* ========================================================================= *)
(* SWP DE-INTERLEAVED KERNEL (B;A rotation of the clean loop).               *)
(* Proof by A/B-rotation: invariant asserted at the CLEAN seam 0x354 (after  *)
(* B, before A), where the GHASH tag is SETTLED and no partial AES is in     *)
(* flight -- so the invariant is clean-C's settled loop invariant, index-    *)
(* shifted. Loop plumbing = bignum_inv_p25519 pattern: ENSURES_WHILE with    *)
(* pc1=pc2=0x354 interior to the body; physical back-branch cbnz@0x4b0->0x1ec *)
(* buried inside the body leg. The tail (0x61c..0x710) replays clean-C's     *)
(* tail (its 0x354..0x448) shifted by +0x2c8.                                *)
(* ========================================================================= *)


(* ===================== aes128_gcm_enc_mc + the direct correctness proof ===================== *)

let aes128_gcm_enc_mc = define_assert_from_elf "aes128_gcm_enc_mc" "arm/aes_gcm/aes128_gcm_enc.o"
[
  0xd10383ff;       (* arm_SUB SP SP (rvalue (word 224)) *)
  0xa90053f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&0))) *)
  0xa9015bf5;       (* arm_STP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  0xa90263f7;       (* arm_STP X23 X24 SP (Immediate_Offset (iword (&32))) *)
  0xa9036bf9;       (* arm_STP X25 X26 SP (Immediate_Offset (iword (&48))) *)
  0xa90473fb;       (* arm_STP X27 X28 SP (Immediate_Offset (iword (&64))) *)
  0xa9057bfd;       (* arm_STP X29 X30 SP (Immediate_Offset (iword (&80))) *)
  0x6d0627e8;       (* arm_STP D8 D9 SP (Immediate_Offset (iword (&96))) *)
  0x6d072fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&112))) *)
  0x6d0837ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&128))) *)
  0x6d093fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&144))) *)
  0xd343fc2f;       (* arm_LSR X15 X1 3 *)
  0x3dc000b2;       (* arm_LDR Q18 X5 (Immediate_Offset (word 0)) *)
  0x3dc004b3;       (* arm_LDR Q19 X5 (Immediate_Offset (word 16)) *)
  0x3dc008b4;       (* arm_LDR Q20 X5 (Immediate_Offset (word 32)) *)
  0x3dc00cb5;       (* arm_LDR Q21 X5 (Immediate_Offset (word 48)) *)
  0x3dc010b6;       (* arm_LDR Q22 X5 (Immediate_Offset (word 64)) *)
  0x3dc014b7;       (* arm_LDR Q23 X5 (Immediate_Offset (word 80)) *)
  0x3dc018b8;       (* arm_LDR Q24 X5 (Immediate_Offset (word 96)) *)
  0x3dc01cb9;       (* arm_LDR Q25 X5 (Immediate_Offset (word 112)) *)
  0x3dc020ba;       (* arm_LDR Q26 X5 (Immediate_Offset (word 128)) *)
  0x3dc024bb;       (* arm_LDR Q27 X5 (Immediate_Offset (word 144)) *)
  0xa94a54b4;       (* arm_LDP X20 X21 X5 (Immediate_Offset (iword (&160))) *)
  0x3dc0007e;       (* arm_LDR Q30 X3 (Immediate_Offset (word 0)) *)
  0x4e200bde;       (* arm_REV64_VEC Q30 Q30 8 *)
  0xa940308b;       (* arm_LDP X11 X12 X4 (Immediate_Offset (iword (&0))) *)
  0xd360fd8d;       (* arm_LSR X13 X12 32 *)
  0x5ac009ad;       (* arm_REV W13 W13 *)
  0x2a0c018c;       (* arm_ORR W12 W12 W12 *)
  0xd344fde7;       (* arm_LSR X7 X15 4 *)
  0xd342fce1;       (* arm_LSR X1 X7 2 *)
  0x924004f0;       (* arm_AND X16 X7 (rvalue (word 3)) *)
  0x0f06e447;       (* arm_MOVI D7 (word 14033993530586874562) *)
  0x5f7854e7;       (* arm_SHL_VEC Q7 Q7 56 64 64 *)
  0xb4002ca1;       (* arm_CBZ X1 (word 1428) *)
  0x11000dae;       (* arm_ADD W14 W13 (rvalue (word 3)) *)
  0x110001b3;       (* arm_ADD W19 W13 (rvalue (word 0)) *)
  0x110009b8;       (* arm_ADD W24 W13 (rvalue (word 2)) *)
  0x110005be;       (* arm_ADD W30 W13 (rvalue (word 1)) *)
  0x110011ad;       (* arm_ADD W13 W13 (rvalue (word 4)) *)
  0x5ac00b16;       (* arm_REV W22 W24 *)
  0x5ac00bde;       (* arm_REV W30 W30 *)
  0xaa16819a;       (* arm_ORR X26 X12 (Shiftedreg X22 LSL 32) *)
  0xaa1e8199;       (* arm_ORR X25 X12 (Shiftedreg X30 LSL 32) *)
  0xa90c6beb;       (* arm_STP X11 X26 SP (Immediate_Offset (iword (&192))) *)
  0xa90b67eb;       (* arm_STP X11 X25 SP (Immediate_Offset (iword (&176))) *)
  0x5ac00a7d;       (* arm_REV W29 W19 *)
  0x3dc033e9;       (* arm_LDR Q9 SP (Immediate_Offset (word 192)) *)
  0xa941580a;       (* arm_LDP X10 X22 X0 (Immediate_Offset (iword (&16))) *)
  0xaa1d8191;       (* arm_ORR X17 X12 (Shiftedreg X29 LSL 32) *)
  0x5ac009db;       (* arm_REV W27 W14 *)
  0xaa1b8188;       (* arm_ORR X8 X12 (Shiftedreg X27 LSL 32) *)
  0xa90a47eb;       (* arm_STP X11 X17 SP (Immediate_Offset (iword (&160))) *)
  0xca1502d7;       (* arm_EOR X23 X22 X21 *)
  0xa942581c;       (* arm_LDP X28 X22 X0 (Immediate_Offset (iword (&32))) *)
  0x4e284a49;       (* arm_AESE Q9 Q18 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0xa90d23eb;       (* arm_STP X11 X8 SP (Immediate_Offset (iword (&208))) *)
  0xa943601d;       (* arm_LDP X29 X24 X0 (Immediate_Offset (iword (&48))) *)
  0x4e284a69;       (* arm_AESE Q9 Q19 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0xca1502da;       (* arm_EOR X26 X22 X21 *)
  0xca14038e;       (* arm_EOR X14 X28 X20 *)
  0xca14015c;       (* arm_EOR X28 X10 X20 *)
  0xa90c6bee;       (* arm_STP X14 X26 SP (Immediate_Offset (iword (&192))) *)
  0xca150308;       (* arm_EOR X8 X24 X21 *)
  0xca1403a7;       (* arm_EOR X7 X29 X20 *)
  0x4e284a89;       (* arm_AESE Q9 Q20 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x3dc037fc;       (* arm_LDR Q28 SP (Immediate_Offset (word 208)) *)
  0xa90d23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&208))) *)
  0x3dc02fec;       (* arm_LDR Q12 SP (Immediate_Offset (word 176)) *)
  0x4e284aa9;       (* arm_AESE Q9 Q21 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284a5c;       (* arm_AESE Q28 Q18 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4e284a4c;       (* arm_AESE Q12 Q18 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x3dc037ef;       (* arm_LDR Q15 SP (Immediate_Offset (word 208)) *)
  0x4e284a7c;       (* arm_AESE Q28 Q19 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4e284ac9;       (* arm_AESE Q9 Q22 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284a9c;       (* arm_AESE Q28 Q20 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4e284abc;       (* arm_AESE Q28 Q21 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4e284adc;       (* arm_AESE Q28 Q22 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4e284afc;       (* arm_AESE Q28 Q23 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4e284ae9;       (* arm_AESE Q9 Q23 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284a6c;       (* arm_AESE Q12 Q19 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4e284a8c;       (* arm_AESE Q12 Q20 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4e284b1c;       (* arm_AESE Q28 Q24 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x3dc000c5;       (* arm_LDR Q5 X6 (Immediate_Offset (word 0)) *)
  0x4e284aac;       (* arm_AESE Q12 Q21 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4e284b3c;       (* arm_AESE Q28 Q25 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x3dc008d1;       (* arm_LDR Q17 X6 (Immediate_Offset (word 32)) *)
  0x4e284acc;       (* arm_AESE Q12 Q22 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x3dc004df;       (* arm_LDR Q31 X6 (Immediate_Offset (word 16)) *)
  0x4e284b5c;       (* arm_AESE Q28 Q26 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4e284aec;       (* arm_AESE Q12 Q23 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4e284b7c;       (* arm_AESE Q28 Q27 *)
  0x3dc033ea;       (* arm_LDR Q10 SP (Immediate_Offset (word 192)) *)
  0x4e284b0c;       (* arm_AESE Q12 Q24 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4e284b09;       (* arm_AESE Q9 Q24 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x3dc010c6;       (* arm_LDR Q6 X6 (Immediate_Offset (word 64)) *)
  0x4e284b2c;       (* arm_AESE Q12 Q25 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0xb4001661;       (* arm_CBZ X1 (word 716) *)
  0x3dc02be0;       (* arm_LDR Q0 SP (Immediate_Offset (word 160)) *)
  0x4e284b29;       (* arm_AESE Q9 Q25 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x11000dae;       (* arm_ADD W14 W13 (rvalue (word 3)) *)
  0x110001b3;       (* arm_ADD W19 W13 (rvalue (word 0)) *)
  0x4e284b4c;       (* arm_AESE Q12 Q26 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x6e3c1def;       (* arm_EOR_VEC Q15 Q15 Q28 128 *)
  0x110009b8;       (* arm_ADD W24 W13 (rvalue (word 2)) *)
  0xa90b5ffc;       (* arm_STP X28 X23 SP (Immediate_Offset (iword (&176))) *)
  0x4e284b49;       (* arm_AESE Q9 Q26 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x3dc014cb;       (* arm_LDR Q11 X6 (Immediate_Offset (word 80)) *)
  0x110005be;       (* arm_ADD W30 W13 (rvalue (word 1)) *)
  0x110011ad;       (* arm_ADD W13 W13 (rvalue (word 4)) *)
  0x4e2009f0;       (* arm_REV64_VEC Q16 Q15 8 *)
  0x4e284b6c;       (* arm_AESE Q12 Q27 *)
  0x5ac00b16;       (* arm_REV W22 W24 *)
  0xa8c41c11;       (* arm_LDP X17 X7 X0 (Postimmediate_Offset (iword (&64))) *)
  0x3dc02fed;       (* arm_LDR Q13 SP (Immediate_Offset (word 176)) *)
  0x4e284b69;       (* arm_AESE Q9 Q27 *)
  0x5ac00bde;       (* arm_REV W30 W30 *)
  0xaa16819a;       (* arm_ORR X26 X12 (Shiftedreg X22 LSL 32) *)
  0x5e180601;       (* arm_DUP_ELEM_SCALAR Q1 Q16 1 64 *)
  0x4e284a40;       (* arm_AESE Q0 Q18 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xaa1e8199;       (* arm_ORR X25 X12 (Shiftedreg X30 LSL 32) *)
  0xa90c6beb;       (* arm_STP X11 X26 SP (Immediate_Offset (iword (&192))) *)
  0x0ee5e20e;       (* arm_PMULL_VEC Q14 Q16 Q5 64 *)
  0x6e291d5c;       (* arm_EOR_VEC Q28 Q10 Q9 128 *)
  0xa90b67eb;       (* arm_STP X11 X25 SP (Immediate_Offset (iword (&176))) *)
  0x5ac00a7d;       (* arm_REV W29 W19 *)
  0x3dc033e9;       (* arm_LDR Q9 SP (Immediate_Offset (word 192)) *)
  0x4e284a60;       (* arm_AESE Q0 Q19 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xca1500e7;       (* arm_EOR X7 X7 X21 *)
  0xca140228;       (* arm_EOR X8 X17 X20 *)
  0x4e200b88;       (* arm_REV64_VEC Q8 Q28 8 *)
  0x4ee5e202;       (* arm_PMULL2_VEC Q2 Q16 Q5 64 *)
  0xa941580a;       (* arm_LDP X10 X22 X0 (Immediate_Offset (iword (&16))) *)
  0xa90a1fe8;       (* arm_STP X8 X7 SP (Immediate_Offset (iword (&160))) *)
  0x4e284a80;       (* arm_AESE Q0 Q20 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x2e301c24;       (* arm_EOR_VEC Q4 Q1 Q16 64 *)
  0xaa1d8191;       (* arm_ORR X17 X12 (Shiftedreg X29 LSL 32) *)
  0x5ac009db;       (* arm_REV W27 W14 *)
  0x0ef1e101;       (* arm_PMULL_VEC Q1 Q8 Q17 64 *)
  0x3dc02bf0;       (* arm_LDR Q16 SP (Immediate_Offset (word 160)) *)
  0xaa1b8188;       (* arm_ORR X8 X12 (Shiftedreg X27 LSL 32) *)
  0xa90a47eb;       (* arm_STP X11 X17 SP (Immediate_Offset (iword (&160))) *)
  0x4ef1e103;       (* arm_PMULL2_VEC Q3 Q8 Q17 64 *)
  0x6e2c1dad;       (* arm_EOR_VEC Q13 Q13 Q12 128 *)
  0x0effe085;       (* arm_PMULL_VEC Q5 Q4 Q31 64 *)
  0x6e211dd1;       (* arm_EOR_VEC Q17 Q14 Q1 128 *)
  0xca1502d7;       (* arm_EOR X23 X22 X21 *)
  0xa942581c;       (* arm_LDP X28 X22 X0 (Immediate_Offset (iword (&32))) *)
  0x6e231c44;       (* arm_EOR_VEC Q4 Q2 Q3 128 *)
  0x4e284aa0;       (* arm_AESE Q0 Q21 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc00cc1;       (* arm_LDR Q1 X6 (Immediate_Offset (word 48)) *)
  0x4e284a49;       (* arm_AESE Q9 Q18 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0xa90d23eb;       (* arm_STP X11 X8 SP (Immediate_Offset (iword (&208))) *)
  0x4e284ac0;       (* arm_AESE Q0 Q22 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2009a2;       (* arm_REV64_VEC Q2 Q13 8 *)
  0xa943601d;       (* arm_LDP X29 X24 X0 (Immediate_Offset (iword (&48))) *)
  0x4e284a69;       (* arm_AESE Q9 Q19 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0xca1502da;       (* arm_EOR X26 X22 X21 *)
  0xca14038e;       (* arm_EOR X14 X28 X20 *)
  0x3d80044d;       (* arm_STR Q13 X2 (Immediate_Offset (word 16)) *)
  0x4e284ae0;       (* arm_AESE Q0 Q23 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xca14015c;       (* arm_EOR X28 X10 X20 *)
  0x3d80085c;       (* arm_STR Q28 X2 (Immediate_Offset (word 32)) *)
  0x0ee1e05d;       (* arm_PMULL_VEC Q29 Q2 Q1 64 *)
  0x5e18045c;       (* arm_DUP_ELEM_SCALAR Q28 Q2 1 64 *)
  0x4e284b00;       (* arm_AESE Q0 Q24 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xa90c6bee;       (* arm_STP X14 X26 SP (Immediate_Offset (iword (&192))) *)
  0xca150308;       (* arm_EOR X8 X24 X21 *)
  0x4ee1e04d;       (* arm_PMULL2_VEC Q13 Q2 Q1 64 *)
  0x6e3d1e31;       (* arm_EOR_VEC Q17 Q17 Q29 128 *)
  0xca1403a7;       (* arm_EOR X7 X29 X20 *)
  0x2e221f82;       (* arm_EOR_VEC Q2 Q28 Q2 64 *)
  0x4e284b20;       (* arm_AESE Q0 Q25 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e08410a;       (* arm_EXT Q10 Q8 Q8 64 *)
  0x4e284a89;       (* arm_AESE Q9 Q20 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc037fc;       (* arm_LDR Q28 SP (Immediate_Offset (word 208)) *)
  0xa90d23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&208))) *)
  0x0ee6e05d;       (* arm_PMULL_VEC Q29 Q2 Q6 64 *)
  0x3dc02fec;       (* arm_LDR Q12 SP (Immediate_Offset (word 176)) *)
  0x6e281d42;       (* arm_EOR_VEC Q2 Q10 Q8 128 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x3d800c4f;       (* arm_STR Q15 X2 (Immediate_Offset (word 48)) *)
  0x4e284aa9;       (* arm_AESE Q9 Q21 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x6e201e01;       (* arm_EOR_VEC Q1 Q16 Q0 128 *)
  0x4e284a5c;       (* arm_AESE Q28 Q18 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4e284a4c;       (* arm_AESE Q12 Q18 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x3dc037ef;       (* arm_LDR Q15 SP (Immediate_Offset (word 208)) *)
  0x4e284a7c;       (* arm_AESE Q28 Q19 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4e200830;       (* arm_REV64_VEC Q16 Q1 8 *)
  0x3c840441;       (* arm_STR Q1 X2 (Postimmediate_Offset (word 64)) *)
  0x4e284ac9;       (* arm_AESE Q9 Q22 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284a9c;       (* arm_AESE Q28 Q20 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x6e3e1e0e;       (* arm_EOR_VEC Q14 Q16 Q30 128 *)
  0x6e2d1c8d;       (* arm_EOR_VEC Q13 Q4 Q13 128 *)
  0x4effe044;       (* arm_PMULL2_VEC Q4 Q2 Q31 64 *)
  0x6e0e41c3;       (* arm_EXT Q3 Q14 Q14 64 *)
  0x4eebe1c1;       (* arm_PMULL2_VEC Q1 Q14 Q11 64 *)
  0x6e241cbf;       (* arm_EOR_VEC Q31 Q5 Q4 128 *)
  0x4e284abc;       (* arm_AESE Q28 Q21 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x6e2e1c60;       (* arm_EOR_VEC Q0 Q3 Q14 128 *)
  0x0eebe1ce;       (* arm_PMULL_VEC Q14 Q14 Q11 64 *)
  0x6e3d1fe4;       (* arm_EOR_VEC Q4 Q31 Q29 128 *)
  0x4e284adc;       (* arm_AESE Q28 Q22 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4ee6e006;       (* arm_PMULL2_VEC Q6 Q0 Q6 64 *)
  0x6e2e1e2e;       (* arm_EOR_VEC Q14 Q17 Q14 128 *)
  0x4e284afc;       (* arm_AESE Q28 Q23 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x6e211da1;       (* arm_EOR_VEC Q1 Q13 Q1 128 *)
  0x6e261c9d;       (* arm_EOR_VEC Q29 Q4 Q6 128 *)
  0x4e284ae9;       (* arm_AESE Q9 Q23 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x6e211dcd;       (* arm_EOR_VEC Q13 Q14 Q1 128 *)
  0x4e284a6c;       (* arm_AESE Q12 Q19 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x0ee7e023;       (* arm_PMULL_VEC Q3 Q1 Q7 64 *)
  0x6e014024;       (* arm_EXT Q4 Q1 Q1 64 *)
  0x6e2d1fa1;       (* arm_EOR_VEC Q1 Q29 Q13 128 *)
  0x4e284a8c;       (* arm_AESE Q12 Q20 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x6e231c91;       (* arm_EOR_VEC Q17 Q4 Q3 128 *)
  0x4e284b1c;       (* arm_AESE Q28 Q24 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x3dc000c5;       (* arm_LDR Q5 X6 (Immediate_Offset (word 0)) *)
  0x4e284aac;       (* arm_AESE Q12 Q21 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x6e311c23;       (* arm_EOR_VEC Q3 Q1 Q17 128 *)
  0x4e284b3c;       (* arm_AESE Q28 Q25 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x3dc008d1;       (* arm_LDR Q17 X6 (Immediate_Offset (word 32)) *)
  0x4e284acc;       (* arm_AESE Q12 Q22 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x0ee7e070;       (* arm_PMULL_VEC Q16 Q3 Q7 64 *)
  0x3dc004df;       (* arm_LDR Q31 X6 (Immediate_Offset (word 16)) *)
  0x4e284b5c;       (* arm_AESE Q28 Q26 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x6e034062;       (* arm_EXT Q2 Q3 Q3 64 *)
  0x4e284aec;       (* arm_AESE Q12 Q23 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x6e301dce;       (* arm_EOR_VEC Q14 Q14 Q16 128 *)
  0x4e284b7c;       (* arm_AESE Q28 Q27 *)
  0x3dc033ea;       (* arm_LDR Q10 SP (Immediate_Offset (word 192)) *)
  0x6e221dd0;       (* arm_EOR_VEC Q16 Q14 Q2 128 *)
  0x4e284b0c;       (* arm_AESE Q12 Q24 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4e284b09;       (* arm_AESE Q9 Q24 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x3dc010c6;       (* arm_LDR Q6 X6 (Immediate_Offset (word 64)) *)
  0x4e284b2c;       (* arm_AESE Q12 Q25 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x6e10421e;       (* arm_EXT Q30 Q16 Q16 64 *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0xb5ffe9e1;       (* arm_CBNZ X1 (word 2096444) *)
  0x3dc02be0;       (* arm_LDR Q0 SP (Immediate_Offset (word 160)) *)
  0x4e284b29;       (* arm_AESE Q9 Q25 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284b4c;       (* arm_AESE Q12 Q26 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x6e3c1def;       (* arm_EOR_VEC Q15 Q15 Q28 128 *)
  0xa90b5ffc;       (* arm_STP X28 X23 SP (Immediate_Offset (iword (&176))) *)
  0x4e284b49;       (* arm_AESE Q9 Q26 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x3dc014cb;       (* arm_LDR Q11 X6 (Immediate_Offset (word 80)) *)
  0x4e2009f0;       (* arm_REV64_VEC Q16 Q15 8 *)
  0x4e284b6c;       (* arm_AESE Q12 Q27 *)
  0xa8c41c11;       (* arm_LDP X17 X7 X0 (Postimmediate_Offset (iword (&64))) *)
  0x3dc02fed;       (* arm_LDR Q13 SP (Immediate_Offset (word 176)) *)
  0x4e284b69;       (* arm_AESE Q9 Q27 *)
  0x5e180601;       (* arm_DUP_ELEM_SCALAR Q1 Q16 1 64 *)
  0x4e284a40;       (* arm_AESE Q0 Q18 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x0ee5e20e;       (* arm_PMULL_VEC Q14 Q16 Q5 64 *)
  0x6e291d5c;       (* arm_EOR_VEC Q28 Q10 Q9 128 *)
  0x4e284a60;       (* arm_AESE Q0 Q19 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xca1500e7;       (* arm_EOR X7 X7 X21 *)
  0xca140228;       (* arm_EOR X8 X17 X20 *)
  0x4e200b88;       (* arm_REV64_VEC Q8 Q28 8 *)
  0x4ee5e202;       (* arm_PMULL2_VEC Q2 Q16 Q5 64 *)
  0xa90a1fe8;       (* arm_STP X8 X7 SP (Immediate_Offset (iword (&160))) *)
  0x4e284a80;       (* arm_AESE Q0 Q20 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x2e301c24;       (* arm_EOR_VEC Q4 Q1 Q16 64 *)
  0x0ef1e101;       (* arm_PMULL_VEC Q1 Q8 Q17 64 *)
  0x3dc02bf0;       (* arm_LDR Q16 SP (Immediate_Offset (word 160)) *)
  0x4ef1e103;       (* arm_PMULL2_VEC Q3 Q8 Q17 64 *)
  0x6e2c1dad;       (* arm_EOR_VEC Q13 Q13 Q12 128 *)
  0x0effe085;       (* arm_PMULL_VEC Q5 Q4 Q31 64 *)
  0x6e211dd1;       (* arm_EOR_VEC Q17 Q14 Q1 128 *)
  0x6e231c44;       (* arm_EOR_VEC Q4 Q2 Q3 128 *)
  0x4e284aa0;       (* arm_AESE Q0 Q21 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc00cc1;       (* arm_LDR Q1 X6 (Immediate_Offset (word 48)) *)
  0x4e284ac0;       (* arm_AESE Q0 Q22 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2009a2;       (* arm_REV64_VEC Q2 Q13 8 *)
  0x3d80044d;       (* arm_STR Q13 X2 (Immediate_Offset (word 16)) *)
  0x4e284ae0;       (* arm_AESE Q0 Q23 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3d80085c;       (* arm_STR Q28 X2 (Immediate_Offset (word 32)) *)
  0x0ee1e05d;       (* arm_PMULL_VEC Q29 Q2 Q1 64 *)
  0x5e18045c;       (* arm_DUP_ELEM_SCALAR Q28 Q2 1 64 *)
  0x4e284b00;       (* arm_AESE Q0 Q24 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ee1e04d;       (* arm_PMULL2_VEC Q13 Q2 Q1 64 *)
  0x6e3d1e31;       (* arm_EOR_VEC Q17 Q17 Q29 128 *)
  0x2e221f82;       (* arm_EOR_VEC Q2 Q28 Q2 64 *)
  0x4e284b20;       (* arm_AESE Q0 Q25 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e08410a;       (* arm_EXT Q10 Q8 Q8 64 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x0ee6e05d;       (* arm_PMULL_VEC Q29 Q2 Q6 64 *)
  0x6e281d42;       (* arm_EOR_VEC Q2 Q10 Q8 128 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x3d800c4f;       (* arm_STR Q15 X2 (Immediate_Offset (word 48)) *)
  0x6e201e01;       (* arm_EOR_VEC Q1 Q16 Q0 128 *)
  0x4e200830;       (* arm_REV64_VEC Q16 Q1 8 *)
  0x3c840441;       (* arm_STR Q1 X2 (Postimmediate_Offset (word 64)) *)
  0x6e3e1e0e;       (* arm_EOR_VEC Q14 Q16 Q30 128 *)
  0x6e2d1c8d;       (* arm_EOR_VEC Q13 Q4 Q13 128 *)
  0x4effe044;       (* arm_PMULL2_VEC Q4 Q2 Q31 64 *)
  0x6e0e41c3;       (* arm_EXT Q3 Q14 Q14 64 *)
  0x4eebe1c1;       (* arm_PMULL2_VEC Q1 Q14 Q11 64 *)
  0x6e241cbf;       (* arm_EOR_VEC Q31 Q5 Q4 128 *)
  0x6e2e1c60;       (* arm_EOR_VEC Q0 Q3 Q14 128 *)
  0x0eebe1ce;       (* arm_PMULL_VEC Q14 Q14 Q11 64 *)
  0x6e3d1fe4;       (* arm_EOR_VEC Q4 Q31 Q29 128 *)
  0x4ee6e006;       (* arm_PMULL2_VEC Q6 Q0 Q6 64 *)
  0x6e2e1e2e;       (* arm_EOR_VEC Q14 Q17 Q14 128 *)
  0x6e211da1;       (* arm_EOR_VEC Q1 Q13 Q1 128 *)
  0x6e261c9d;       (* arm_EOR_VEC Q29 Q4 Q6 128 *)
  0x6e211dcd;       (* arm_EOR_VEC Q13 Q14 Q1 128 *)
  0x0ee7e023;       (* arm_PMULL_VEC Q3 Q1 Q7 64 *)
  0x6e014024;       (* arm_EXT Q4 Q1 Q1 64 *)
  0x6e2d1fa1;       (* arm_EOR_VEC Q1 Q29 Q13 128 *)
  0x6e231c91;       (* arm_EOR_VEC Q17 Q4 Q3 128 *)
  0x6e311c23;       (* arm_EOR_VEC Q3 Q1 Q17 128 *)
  0x0ee7e070;       (* arm_PMULL_VEC Q16 Q3 Q7 64 *)
  0x6e034062;       (* arm_EXT Q2 Q3 Q3 64 *)
  0x6e301dce;       (* arm_EOR_VEC Q14 Q14 Q16 128 *)
  0x6e221dd0;       (* arm_EOR_VEC Q16 Q14 Q2 128 *)
  0x6e10421e;       (* arm_EXT Q30 Q16 Q16 64 *)
  0x3dc000cc;       (* arm_LDR Q12 X6 (Immediate_Offset (word 0)) *)
  0x3dc008cd;       (* arm_LDR Q13 X6 (Immediate_Offset (word 32)) *)
  0x3dc004ce;       (* arm_LDR Q14 X6 (Immediate_Offset (word 16)) *)
  0xb40006b0;       (* arm_CBZ X16 (word 212) *)
  0xa8c15c16;       (* arm_LDP X22 X23 X0 (Postimmediate_Offset (iword (&16))) *)
  0x110001ae;       (* arm_ADD W14 W13 (rvalue (word 0)) *)
  0x5ac009ce;       (* arm_REV W14 W14 *)
  0xaa0e818e;       (* arm_ORR X14 X12 (Shiftedreg X14 LSL 32) *)
  0xa90a3beb;       (* arm_STP X11 X14 SP (Immediate_Offset (iword (&160))) *)
  0x3dc02be0;       (* arm_LDR Q0 SP (Immediate_Offset (word 160)) *)
  0x4e284a40;       (* arm_AESE Q0 Q18 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a60;       (* arm_AESE Q0 Q19 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a80;       (* arm_AESE Q0 Q20 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284aa0;       (* arm_AESE Q0 Q21 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ac0;       (* arm_AESE Q0 Q22 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ae0;       (* arm_AESE Q0 Q23 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b00;       (* arm_AESE Q0 Q24 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b20;       (* arm_AESE Q0 Q25 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xa90a5ff6;       (* arm_STP X22 X23 SP (Immediate_Offset (iword (&160))) *)
  0x3dc02bfd;       (* arm_LDR Q29 SP (Immediate_Offset (word 160)) *)
  0x6e201fa0;       (* arm_EOR_VEC Q0 Q29 Q0 128 *)
  0x3c810440;       (* arm_STR Q0 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200800;       (* arm_REV64_VEC Q0 Q0 8 *)
  0x6e3e1c00;       (* arm_EOR_VEC Q0 Q0 Q30 128 *)
  0x0eece008;       (* arm_PMULL_VEC Q8 Q0 Q12 64 *)
  0x4eece009;       (* arm_PMULL2_VEC Q9 Q0 Q12 64 *)
  0x5e18040b;       (* arm_DUP_ELEM_SCALAR Q11 Q0 1 64 *)
  0x2e201d6b;       (* arm_EOR_VEC Q11 Q11 Q0 64 *)
  0x0eeee16a;       (* arm_PMULL_VEC Q10 Q11 Q14 64 *)
  0x6e291d00;       (* arm_EOR_VEC Q0 Q8 Q9 128 *)
  0x0ee7e121;       (* arm_PMULL_VEC Q1 Q9 Q7 64 *)
  0x6e094129;       (* arm_EXT Q9 Q9 Q9 64 *)
  0x6e201d4a;       (* arm_EOR_VEC Q10 Q10 Q0 128 *)
  0x6e211d21;       (* arm_EOR_VEC Q1 Q9 Q1 128 *)
  0x6e211d4a;       (* arm_EOR_VEC Q10 Q10 Q1 128 *)
  0x0ee7e149;       (* arm_PMULL_VEC Q9 Q10 Q7 64 *)
  0x6e291d08;       (* arm_EOR_VEC Q8 Q8 Q9 128 *)
  0x6e0a414a;       (* arm_EXT Q10 Q10 Q10 64 *)
  0x6e2a1d1e;       (* arm_EOR_VEC Q30 Q8 Q10 128 *)
  0x6e1e43de;       (* arm_EXT Q30 Q30 Q30 64 *)
  0x110005ad;       (* arm_ADD W13 W13 (rvalue (word 1)) *)
  0xd1000610;       (* arm_SUB X16 X16 (rvalue (word 1)) *)
  0xb5fff9b0;       (* arm_CBNZ X16 (word 2096948) *)
  0xaa0f03e0;       (* arm_MOV X0 X15 *)
  0x4e200bde;       (* arm_REV64_VEC Q30 Q30 8 *)
  0x3d80007e;       (* arm_STR Q30 X3 (Immediate_Offset (word 0)) *)
  0x5ac009ae;       (* arm_REV W14 W13 *)
  0xb9000c8e;       (* arm_STR W14 X4 (Immediate_Offset (word 12)) *)
  0x6d4627e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&96))) *)
  0x6d472fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&112))) *)
  0x6d4837ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&128))) *)
  0x6d493fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&144))) *)
  0xa94053f3;       (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&0))) *)
  0xa9415bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  0xa94263f7;       (* arm_LDP X23 X24 SP (Immediate_Offset (iword (&32))) *)
  0xa9436bf9;       (* arm_LDP X25 X26 SP (Immediate_Offset (iword (&48))) *)
  0xa94473fb;       (* arm_LDP X27 X28 SP (Immediate_Offset (iword (&64))) *)
  0xa9457bfd;       (* arm_LDP X29 X30 SP (Immediate_Offset (iword (&80))) *)
  0x910383ff;       (* arm_ADD SP SP (rvalue (word 224)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
let AES128_GCM_ENC_EXEC = ARM_MK_EXEC_RULE aes128_gcm_enc_mc;;

let aes8c = new_definition
 `aes8c nonce (rk:int128 list) c : int128 =
    aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
      (word_reversefields 8 (ctr_block nonce c))
      (word_reversefields 8 (EL 0 rk))))(word_reversefields 8 (EL 1 rk))))
      (word_reversefields 8 (EL 2 rk))))(word_reversefields 8 (EL 3 rk))))
      (word_reversefields 8 (EL 4 rk))))(word_reversefields 8 (EL 5 rk))))
      (word_reversefields 8 (EL 6 rk))))(word_reversefields 8 (EL 7 rk)))`;;

(* aes10p = the PRE-final-XOR 10-aese tower (10 aese, 9 aesmc, keys EL 0..EL 9, NO final rk10 XOR). *)
let aes10p = new_definition
 `aes10p (nonce:96 word) (rk:int128 list) (c:num) : int128 =
    aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
     (aesmc(aese (word_reversefields 8 (ctr_block nonce c))
       (word_reversefields 8 (EL 0 rk))))(word_reversefields 8 (EL 1 rk))))
       (word_reversefields 8 (EL 2 rk))))(word_reversefields 8 (EL 3 rk))))
       (word_reversefields 8 (EL 4 rk))))(word_reversefields 8 (EL 5 rk))))
       (word_reversefields 8 (EL 6 rk))))(word_reversefields 8 (EL 7 rk))))
       (word_reversefields 8 (EL 8 rk))))(word_reversefields 8 (EL 9 rk))`;;

let AES10P_COMPLETE = prove
 (`[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
    EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk
   ==> word_xor (aes10p nonce rk c) (word_reversefields 8 (EL 10 rk))
       = word_reversefields 8 (aes128_cipher (ctr_block nonce c) rk)`,
  DISCH_TAC THEN REWRITE_TAC[aes10p] THEN
  GEN_REWRITE_TAC LAND_CONV
   [INST ((`word_reversefields 8 (ctr_block nonce c):int128`,`plaintext:int128`) ::
          map (fun j -> (parse_term(Printf.sprintf "word_reversefields 8 (EL %d rk):int128" j),
                         mk_var("rk"^string_of_int j,`:int128`))) (0--10))
         AES128_CIPHER_RECONSTRUCT] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; MAP] THEN ASM_REWRITE_TAC[]);;

(* ---- Q30 GHASH collapse lemmas (fold ALL 4 syntactic keystream forms in
   the reduce tower to nist_cipher_block, so the g3-body reconstruction applies).  The keystreams
   appear as: (1) word_xor(aes10p c)(word_xor inb rk10); (2) aese-rounds over aes7c c; (3) over aes8c c;
   (4) fully-expanded 10-aese over rev8(ctr_block c); (5) lane-split word_join(word_xor lanes).  Each
   folds by a one-liner below; then CT_TO_NCB turns word_xor(rev8(aes128_cipher(ctr(j+2))))(inblock j)
   into rev8(nist_cipher_block j).  Index pairing verified consistent: ctr(j+2)<->aes_ctr_block(j)<->inblock(j). *)
let AES10P_VIA_AES7C = prove
 (`aes10p nonce rk c =
   aese(aesmc(aese(aesmc(aese (aes7c nonce rk c) (word_reversefields 8 (EL 7 rk))))
     (word_reversefields 8 (EL 8 rk))))(word_reversefields 8 (EL 9 rk))`,
  REWRITE_TAC[aes10p; aes7c]);;
let AES10P_VIA_AES8C = prove
 (`aes10p nonce rk c =
   aese(aesmc(aese (aes8c nonce rk c) (word_reversefields 8 (EL 8 rk)))) (word_reversefields 8 (EL 9 rk))`,
  REWRITE_TAC[aes10p; aes8c]);;
let KEYSTREAM_FOLD = prove
 (`[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
    EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk
   ==> word_xor (aes10p nonce rk c) (word_xor inb (word_reversefields 8 (EL 10 rk)))
       = word_xor (word_reversefields 8 (aes128_cipher (ctr_block nonce c) rk)) inb`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP AES10P_COMPLETE th)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN CONV_TAC WORD_BITWISE_RULE);;
let CT_TO_NCB = prove
 (`word_xor (word_reversefields 8 (aes128_cipher (ctr_block nonce (j+c)) rk)) (inblock j)
   = word_reversefields 8 (nist_cipher_block c nonce rk inblock j)`,
  REWRITE_TAC[nist_cipher_block; cipher_block; aes_ctr_block; WORD_REVERSEFIELDS_REVERSEFIELDS]);;

let ZXZX32 = prove
 (`word_zx (word_zx (x:int32):int64):int32 = x`, CONV_TAC WORD_BLAST);;

(* ---- the elaborated invariant swp_inv (44+1 conjuncts, all cross-iteration regs pinned) ---- *)
let swp_inv = `\(i:num) s.
    read X0 s = word_add in_p (word (64 * i)) /\
    read X2 s = word_add out_p (word (64 * i)) /\
    read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
    read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
    read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
    read (memory :> bytes128 (word_add stackpointer (word 160))) s =
        word_reversefields 8 (ctr_block nonce (4*i+c)) /\
    read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
    read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
    read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
    read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
    read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
    read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
    read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
    read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
    read X12 s = word_zx (word_zx (word_subword
        (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
    read X13 s = word_zx (word (4 * i + c + 4):int32):int64 /\
    read Q7 s = word 13979173243358019584 /\
    read Q9  s = aes7c nonce rk (4*i+c+2) /\
    read Q12 s = aes8c nonce rk (4*i+c+1) /\
    read Q28 s = aes10p nonce rk (4*i+c+3) /\
    read Q30 s = byteswap128
        (nist_ghash (aes128_cipher (word 0) rk) tag0
           (list_of_seq (nist_cipher_block c nonce rk inblock) (4 * i))) /\
    read X1 s = word (loop_count - (i+1)) /\ read X15 s = word(len_bits DIV 8) /\ read X16 s = word loop_remain /\
    htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
    (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
    (!j. j < 4 * i ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
             word_xor (aes_ctr_block c nonce rk j) (inblock j)) /\
    read Q5 s = byteswap128(h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
    read Q31 s = word_join (karatsuba_mid(h_power (ghash_twist (aes128_cipher (word 0) rk)) 1):int64)
                           (karatsuba_mid(h_power (ghash_twist (aes128_cipher (word 0) rk)) 0):int64) /\
    read Q17 s = byteswap128(h_power (ghash_twist (aes128_cipher (word 0) rk)) 1) /\
    read Q6 s = word_join (karatsuba_mid(h_power (ghash_twist (aes128_cipher (word 0) rk)) 3):int64)
                          (karatsuba_mid(h_power (ghash_twist (aes128_cipher (word 0) rk)) 2):int64) /\
    read (memory :> bytes128 (word_add stackpointer (word 176))) s = word_reversefields 8 (ctr_block nonce (4*i+c+1)) /\
    read (memory :> bytes128 (word_add stackpointer (word 192))) s = word_xor (inblock (4*i+2)) (word_reversefields 8 (EL 10 rk)) /\
    read (memory :> bytes128 (word_add stackpointer (word 208))) s = word_xor (inblock (4*i+3)) (word_reversefields 8 (EL 10 rk)) /\
    read Q10 s = word_xor (inblock (4*i+2)) (word_reversefields 8 (EL 10 rk)) /\
    read Q15 s = word_xor (inblock (4*i+3)) (word_reversefields 8 (EL 10 rk)) /\
    read X23 s = word_subword (word_xor (inblock (4*i+1)) (word_reversefields 8 (EL 10 rk)):int128) (64,64):int64 /\
    read X28 s = word_subword (word_xor (inblock (4*i+1)) (word_reversefields 8 (EL 10 rk)):int128) (0,64):int64`;;

(* Build a leg pre/post state predicate `\s. aligned_bytes_loaded s (word pc) aes128_gcm_enc_mc /\
   read PC s = word(pc+off) /\ <BETA-reduced+ADD_CLAUSES-normalized inv idx body>` as a FLAT conjunction.
   This EXACTLY matches what ENSURES_SEQUENCE_TAC / ENSURES_WHILE_UP_TAC produce for their obligations
   (program_decodes /\ PC /\ Q s, then BETA_TAC), so a leg's conclusion unifies via MATCH_MP_TAC against
   the composed goal.  (The old form mk_conj(`aligned/\PC`, list_mk_comb(inv,[idx;s])) was UNREDUCED +
   nested-associated -> MATCH_MP_TAC No match.) *)
let leg_state inv off idx =
  let body = rhs(concl((TOP_DEPTH_CONV BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES])
                        (list_mk_comb(inv,[idx;`s:armstate`])))) in
  mk_abs(`s:armstate`,
    list_mk_conj(`aligned_bytes_loaded s (word pc) aes128_gcm_enc_mc` ::
                 mk_eq(`read PC s`,mk_comb(`word:num->int64`,mk_binop `+` `pc:num` off)) ::
                 conjuncts body));;

(* body-leg goal builder *)
let mk_body_goal inv =
  mk_imp(`([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
      EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk) /\
     len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
     2 <= loop_count /\ i < loop_count - 1 /\ 16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
     nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,1856) /\
     nonoverlapping (out_p:int64,16 * nblocks) (in_p:int64,16 * nblocks) /\
     nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,192) /\
     nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
     nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
     nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (word pc:int64,1856) /\
     nonoverlapping (tag_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (tag_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (ivec_p:int64,16) (word pc:int64,1856) /\
     nonoverlapping (ivec_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (ivec_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,1856) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (in_p:int64,16*nblocks) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,192)`,
   list_mk_icomb "ensures" [`arm`;
     (* pre/post as FLAT, BETA-reduced conjunctions (leg_state) so this leg composes via MATCH_MP_TAC
        against ENSURES_SEQUENCE/WHILE obligations (which are flat+reduced).  POST carries aligned too. *)
     leg_state inv `0x1ec` `i:num` ;
     leg_state inv `0x4b0` `i+1` ;
     (* Frame MUST also permit the callee-saved regs the body clobbers (preamble saved/restores them):
        X19..X30 and the FULL Q8..Q15 (ABI only permits Q8..Q15 :> tophalf).
        Without these, Q9/Q12/Q15/X23/X28 etc. aren't subsumed -> frame fails. *)
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`]);;

let body_goal = mk_body_goal swp_inv;;

(* store sites for MERGE_CTR128_TAC *)
let merges = [(10,176);(28,192);(31,176);(41,160);(50,160);(63,208);(81,192);(95,208)];;

(* GHASH-reduce Q-regs + the counter/input X-lanes carried through the reduce lineage. *)
let REDSETX = ["Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q8";"Q13";"Q14";"Q16";"Q17";"Q28";"Q29";"Q30";"Q31";
               "X7";"X8";"X11";"X13";"X14";"X17";"X23";"X24";"X25";"X26";"X28";"X30"];;
(* The stepper anchors the input-block reads (the read-only input-split facts at s0). *)
let enc_anchors = [`in_p:int64`];;

(* loop-head scalar lanes to GHOST_INTRO (so their s0 value is a logic var kept across the body, not a
   discarded ghost).  X23/X28 ARE here (consumed early @0x210->Q13@0x21c) so they must be KEPT; the
   invariant now ALSO pins them, so GHOST_INTRO turns the pin conjunct into ghost_X23 = subword(...),
   which is exactly the equation the block-4i+1 keystream collapse needs. *)
let ghost_lanes = ["X7";"X8";"X17";"X22";"X23";"X24";"X25";"X26";"X28";"X29";"X30";"X10";"X14";"X19";"X27"];;

(* input-split preamble, EXTENDED to blocks 4i+0..4i+7: the body loads the current
   group (4i+0..3, ldp [x0]/[x0,#16/32/48]) AND prefetches the next group (4i+4..7) into the carried
   lanes X23/X28/Q10/Q15/[sp+192/208] for iteration i+1.  Splitting all 8 blocks into bytes64 halves
   lets both the current ciphertext AND the inv(i+1) carried-lane pins resolve.  Bound 4i+7<nblocks
   needs i < loop_count-2 (the FILL/DRAIN steady range). *)
let INPUT_SPLIT_TAC =
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * (4*i+0))))) s0 = inblock (4*i+0) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+1))))) s0 = inblock (4*i+1) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+2))))) s0 = inblock (4*i+2) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+3))))) s0 = inblock (4*i+3) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+4))))) s0 = inblock (4*i+4) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+5))))) s0 = inblock (4*i+5) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+6))))) s0 = inblock (4*i+6) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+7))))) s0 = inblock (4*i+7)`
   STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `4*i+7 < nblocks` ASSUME_TAC THENL
      [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `i < loop_count - 1` THEN
       UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16 * (4*i+0) = 64*i`; ARITH_RULE `16 * (4*i+1) = 64*i+16`;
     ARITH_RULE `16 * (4*i+2) = 64*i+32`; ARITH_RULE `16 * (4*i+3) = 64*i+48`;
     ARITH_RULE `16 * (4*i+4) = 64*i+64`; ARITH_RULE `16 * (4*i+5) = 64*i+80`;
     ARITH_RULE `16 * (4*i+6) = 64*i+96`; ARITH_RULE `16 * (4*i+7) = 64*i+112`]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
     check (fun th -> let c = concl th in is_eq c && free_in `in_p:int64` (lhs c) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))));;

(* ABBREV-based setup (John's key fix): GHOST_INTRO the loop-head scalar lanes, then ENSURES_INIT +
   input-split, then ABBREV every remaining `read C s0` to init_ logic vars.  This makes every in-body
   value a stable init_-expression that DISCARD_OLDSTATE never drops, keeping the reduce towers BOUNDED
   (init_ atoms, not read-state megabyte towers).  Then the stepper keeps the reduce lineage -> orphan-free Q30. *)
let setup_tac =
  STRIP_TAC THEN REWRITE_TAC[fst AES128_GCM_ENC_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  INPUT_SPLIT_TAC THEN
  (* ABBREV all non-j-parametric `read C s0` reads to init_ vars, EXCEPT in_p-memory reads: those
     are the read-only input-split anchors (read(bytes64 in_p+X) s0 = subword(inblock..)) that the
     body's prefetch loads (at s39/s55/s66) fold through - abbreviating them breaks the inblock fold
     (the anchor becomes init_k=subword(inblock..) and the reduced-to-s0 prefetch read finds no target). *)
  (fun (asl,w) ->
    let jv = `j:num` in
    let reads0 = setify(flat(map (fun (_,th) -> find_terms (fun t -> try let h,a=strip_comb t in
         fst(dest_const h)="read" && length a=2 && string_of_term(hd(tl a))="s0" with _->false) (concl th)) asl)) in
    let toab = filter (fun t -> not(free_in jv t) && not(free_in `in_p:int64` t)
                              && string_of_term t <> "read PC s0") reads0 in
    (EVERY (List.mapi (fun k t -> ABBREV_TAC (mk_eq(mk_var(Printf.sprintf "init_%d" k, type_of t), t))) toab)) (asl,w));;

(* Stepper: keep-latest over REDSETX (keeps Q30 + reduce lineage; plain discard would drop
   Q30@176).  The init_-ABBREV setup keeps the towers bounded.  Prefetch input reads for blocks 4i+5/6/7
   (feeding the i+1 pins X23/Q10/Q15) settle as read(bytes64 (in_p+word(64i))+word K) sN with a NESTED
   address + a non-s0 state, so they don't auto-match the s0 split anchors; a post-step normalization
   (addr-fold + input-forall @ current state) resolves them (see prefetch_fold_tac). *)
let step_body_tac =
  setup_tac THEN
  SWP_STEPS_TAC enc_anchors [] REDSETX AES128_GCM_ENC_EXEC (K ALL_TAC) merges (1--177) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                           IN_P_ADDR_FOLD_CONV)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let closers_0_6 =
  [ REWRITE_TAC[ARITH_RULE `64*(i+1)=64*i+64`; LEFT_ADD_DISTRIB] THEN CONV_TAC WORD_RULE;
    REWRITE_TAC[ARITH_RULE `64*(i+1)=64*i+64`; LEFT_ADD_DISTRIB] THEN CONV_TAC WORD_RULE;
    REWRITE_TAC[ZXNEST4] THEN
      SUBGOAL_THEN `word (4*i+c+4):int32 = word(4*(i+1)+c)` SUBST1_TAC THENL
       [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN ACCEPT_TAC (mk_cbv `4*(i+1)+c`);
    REWRITE_TAC[ZXZX32] THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[aes7c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN REWRITE_TAC[ZXNEST4;ZXZX32] THEN
      SUBGOAL_THEN `word_add (word (4*i+c+4):int32) (word 2) = word(4*(i+1)+c+2):int32` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN ACCEPT_TAC (mk_cbv `4*(i+1)+c+2`);
    REWRITE_TAC[aes8c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN REWRITE_TAC[ZXNEST4;ZXZX32] THEN
      SUBGOAL_THEN `word_add (word (4*i+c+4):int32) (word 1) = word(4*(i+1)+c+1):int32` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN ACCEPT_TAC (mk_cbv `4*(i+1)+c+1`);
    REWRITE_TAC[aes10p] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN REWRITE_TAC[ZXNEST4;ZXZX32] THEN
      SUBGOAL_THEN `word_add (word (4*i+c+4):int32) (word 3) = word(4*(i+1)+c+3):int32` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN ACCEPT_TAC (mk_cbv `4*(i+1)+c+3`)];;

(* ---- goal [7] closer: Q30 GHASH tag.  The stepped tower (0 orphans, ghost pins for X23/X28 in asms)
   collapses all 4 keystreams to nist_cipher_block, then the g3-body reduce reconstruction folds
   the pmull-Karatsuba tower to the settled nist_ghash..(4(i+1)).
   ksf is built inside (MATCH_MP KEYSTREAM_FOLD the rk-list hyp, which is in the assumptions). *)
(* collapse-only part of the Q30 closer (steps 0-4): fold ghost pins + all 4 keystreams to
   nist_cipher_block, leaving the g3-body pmull-Karatsuba tower over the settled cipherblocks.
   Split out so the harness can dump the post-collapse form (isolating collapse from reconstruction). *)
let collapse_q30 : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th =
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) asl)
      with _ -> failwith "collapse_q30: rk-list hyp not found" in
    let ksf = MATCH_MP KEYSTREAM_FOLD rkth in
    let ghostpins = List.filter_map (fun (_,th) ->
      let c = concl th in
      if is_eq c then (match lhs c with
        | Var(nm,_) when String.length nm>=6 && String.sub nm 0 6="ghost_"
            && can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="inblock" with _->false)) (rhs c)
          -> Some th | _ -> None) else None) asl in
    (
    (* (0) normalize the RHS tag index 4*(i+1) -> 4*i+4 so the SUC^4 unfold + GHASH_ACC_APPEND fire. *)
    REWRITE_TAC[ARITH_RULE `4*(i+1) = 4*i+4`] THEN
    (* (1) fold X23/X28 ghost pins + recombine word_join(hi)(lo) -> word_xor(inblock(4i+1))(rk10). *)
    REWRITE_TAC(JOIN_SUBWORD_RECOMBINE :: ghostpins) THEN
    (* (2) NO byteswap-split here - leave the goal byteswap128-wrapped so the reconstruction (which does
       a single byteswap-split + MATCH_MP) applies.  The keystream folds below reach the
       keystreams DEEP in the LHS tower regardless of the outer word_subword/byteswap wrapper. *)
    (* (3) normalize all 4 keystream syntactic forms -> aes10p, lane-join, ksf, counter-arith, CT_TO_NCB.
       NB the RHS tag is now 4*i+4; the `4*i+4=(4*i+2)+2` rewrite would hit it, but step (4)'s inverse
       restores it, so it round-trips.  The keystream counter args (4i+2..5) are what genuinely fold. *)
    REWRITE_TAC[GSYM AES10P_VIA_AES7C; GSYM AES10P_VIA_AES8C; GSYM aes10p] THEN
    REWRITE_TAC[JOIN_XOR_LANES] THEN
    REWRITE_TAC[ksf] THEN
    REWRITE_TAC[ARITH_RULE `4*i+c+3 = (4*i+3)+c`; ARITH_RULE `4*i+c+2 = (4*i+2)+c`;
                ARITH_RULE `4*i+c+1 = (4*i+1)+c`; ARITH_RULE `4*i+0 = 4*i`] THEN
    REWRITE_TAC[CT_TO_NCB] THEN
    (* (4) canonicalize block indices to flat 4*i+K. *)
    REWRITE_TAC[ARITH_RULE `(4*i+0)+2 = 4*i+2`; ARITH_RULE `(4*i+1)+2 = 4*i+3`;
                ARITH_RULE `(4*i+2)+2 = 4*i+4`; ARITH_RULE `(4*i+3)+2 = 4*i+5`;
                ARITH_RULE `4*i+0 = 4*i`]
    ) (asl,w);;

let close_goal7 : tactic =
  fun (asl,w) ->
    (
    collapse_q30 THEN
    (* (5) g3-body reduce reconstruction (4*i variant).  The goal
       here is byteswap128-wrapped `word_subword(word_join(tower))(64,128) = byteswap128(nist_ghash..4*i+4)`
       (collapse did NOT strip byteswap).  normalize + SINGLE byteswap-split + MATCH_MP + ABBREV
       + RECONSTRUCT applies directly. *)
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
    SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC [byteswap128; WORD_BLAST
      `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
       word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
    MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y
      ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
    MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block c nonce rk inblock) (4 * i)))`;
      `cipherblock_0 = nist_cipher_block c nonce rk inblock (4 * i)`;
      `cipherblock_1 = nist_cipher_block c nonce rk inblock (4 * i + 1)`;
      `cipherblock_2 = nist_cipher_block c nonce rk inblock (4 * i + 2)`;
      `cipherblock_3 = nist_cipher_block c nonce rk inblock (4 * i + 3)`;
      `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
      `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
      `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`;
      `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
    REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
    TRANS_TAC EQ_TRANS
     `polyval_reduce_prop3
          (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
          (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
          (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
          (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
      REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
      REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
      ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
       `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM karatsuba_join] THEN MATCH_ACCEPT_TAC KARATSUBA_JOIN_XOR4;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                   `[cipherblock_1;cipherblock_2;cipherblock_3]:(int128)list`;
                   `sofar:int128`; `cipherblock_0:int128`]
                  GHASH_POLYVAL_ACC_BATCHED) THEN
    REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
     `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    EXPAND_TAC "sofar" THEN
    REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
    REWRITE_TAC[ARITH_RULE `4*i+4 = SUC(SUC(SUC(SUC(4*i))))`] THEN
    REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    REWRITE_TAC[APPEND] THEN
    REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL]
    ) (asl,w);;


(* ---- goal [8]: X1 = word_sub (word (loop_count - i)) (word 1) = word(loop_count - (i+1)).  Uses the
   loop bounds (2<=loop_count, i<loop_count-2) in the assumptions. ---- *)
(* X1 body goal (with inv X1 = word(loop_count-(i+1))): word_sub(word(loop_count-(i+1)))(word 1) =
   word(loop_count-((i+1)+1)) = word(loop_count-(i+2)).  Needs loop_count-(i+2)=(loop_count-(i+1))-1 and
   1<=loop_count-(i+1) (from i<loop_count-2). *)
let close_goal8 : tactic =
  fun (asl,w) ->
    let bnds = List.filter_map (fun (_,th) -> let c = concl th in
      if c = `2 <= loop_count` || c = `i < loop_count - 2` || c = `i < loop_count - 1` then Some th else None) asl in
    (MAP_EVERY (fun th -> ASSUME_TAC th) bnds THEN
     SUBGOAL_THEN `loop_count - ((i+1)+1) = (loop_count - (i+1)) - 1 /\ 1 <= loop_count - (i+1)` STRIP_ASSUME_TAC THENL
      [MAP_EVERY (fun th -> MP_TAC th) bnds THEN ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[WORD_SUB; VAL_WORD_1] THEN
     REWRITE_TAC[GSYM VAL_WORD_1] THEN AP_TERM_TAC THEN
     MAP_EVERY (fun th -> MP_TAC th) bnds THEN ARITH_TAC) (asl,w);;

(* ---- carried-lane pin preservation closers (goals 3-9 in the dump), all pure word identities +
   the block-index shift 4*(i+1)+k = 4*i+(k+4). ---- *)
(* [sp+176] counter -> rev8(ctr_block(4(i+1)+3)) : reassembled reversed-lane counter, +1 increment. *)
let close_ctr176 : tactic =
  REWRITE_TAC[ZXNEST4;ZXZX32] THEN
  SUBGOAL_THEN `word_add (word (4*i+c+4):int32) (word 1) = word(4*(i+1)+c+1):int32` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  ACCEPT_TAC (mk_cbv `4*(i+1)+c+1`);;
(* Q10/Q15/[sp+192]/[sp+208] lane pins: word_join(word_xor lanes) = word_xor(inblock(4(i+1)+k))(rk10). *)
let close_lanejoin : tactic =
  REWRITE_TAC[ARITH_RULE `4*(i+1)+0 = 4*i+4`; ARITH_RULE `4*(i+1)+1 = 4*i+5`;
              ARITH_RULE `4*(i+1)+2 = 4*i+6`; ARITH_RULE `4*(i+1)+3 = 4*i+7`] THEN
  REWRITE_TAC[ARITH_RULE `4*(i+1)+c = 4*i+c+4`; ARITH_RULE `4*(i+1)+c+1 = 4*i+c+5`] THEN
  REWRITE_TAC[JOIN_XOR_LANES];;
(* X23/X28 subword pins: word_xor(subword..)(subword..) = subword(word_xor(inblock(4(i+1)+1))(rk10))(lane). *)
let close_subwordpin : tactic =
  REWRITE_TAC[ARITH_RULE `4*(i+1)+0 = 4*i+4`; ARITH_RULE `4*(i+1)+1 = 4*i+5`;
              ARITH_RULE `4*(i+1)+2 = 4*i+6`; ARITH_RULE `4*(i+1)+3 = 4*i+7`] THEN CONV_TAC WORD_BLAST;;

(* output-block keystream identities (the 3-way conjunction close_goal9 leaves): each
   word_xor(<aesNc-tower/aes10p>)(input^rk10) = word_xor(rev8(aes128_cipher(ctr(4i+k))))(inblock).
   Fold: JOIN_SUBWORD_RECOMBINE (block-4i+1 lanes) + normalize aesNc->aes10p + KEYSTREAM_FOLD.  The RHS
   is already in aes128_cipher form (NOT nist_cipher_block) so ksf lands directly. *)
let close_ksfold : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th =
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) asl)
      with _ -> failwith "close_ksfold: no rk-hyp" in
    (REPEAT CONJ_TAC THEN
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC[GSYM AES10P_VIA_AES7C; GSYM AES10P_VIA_AES8C] THEN
     REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD rkth]) (asl,w);;

(* ---- goal [9]: output-forall j < 4*(i+1).  Split into the OLD stores (j<4*i, from the invariant) and
   the 4 NEW stores (blocks 4*i+0..3, this group), each reconstructing to word_xor(aes_ctr_block j)(inblock j).
   Re-indexed to the 4*i-based invariant. ---- *)
let close_goal9 : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th =
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) asl)
      with _ -> failwith "close_goal9: no rk-hyp" in
    (REWRITE_TAC[ARITH_RULE `j < 4 * (i+1) <=>
                          j < 4 * i \/ j = 4*i+0 \/ j = 4*i+1 \/ j = 4*i+2 \/ j = 4*i+3`] THEN
     ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
     REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
     REWRITE_TAC[ARITH_RULE `16 * (4*i+0) = 64*i`; ARITH_RULE `16 * (4*i+1) = 64*i+16`;
        ARITH_RULE `16 * (4*i+2) = 64*i+32`; ARITH_RULE `16 * (4*i+3) = 64*i+48`] THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
     REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
     REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
     ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
     REWRITE_TAC[aes_ctr_block] THEN
     REWRITE_TAC[ARITH_RULE `4 * i + c + 3 = (4 * i + 3) + c`;
                 ARITH_RULE `4 * i + c + 2 = (4 * i + 2) + c`;
                 ARITH_RULE `4 * i + c + 1 = (4 * i + 1) + c`;
                 ARITH_RULE `4 * i + 0 = 4 * i`] THEN ASM_REWRITE_TAC[] THEN
     (* the reconstruction leaves the 4 output-block keystream identities; fold them (ksfold). *)
     REPEAT CONJ_TAC THEN
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC[GSYM AES10P_VIA_AES7C; GSYM AES10P_VIA_AES8C] THEN
     REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD rkth] THEN
     REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`]) (asl,w);;

(* ---- goal [10]: MAYCHANGE frame.  MP all the per-step
   MAYCHANGE assumptions, then a SINGLE MONOTONE_MAYCHANGE_TAC.  (REPEAT(MONOTONE.. ORELSE SUBSUMED..)
   LOOPS - MONOTONE makes trivial progress forever.) ---- *)
(* The frame goal is `<declared frame> s0 s177`.  The stepper may leave several MAYCHANGE assumptions (one per step,
   various state pairs); MONOTONE_MAYCHANGE_TAC's FIRST_ASSUM may pick a WRONG one (e.g. a per-step
   fragment sk s(k+1)) -> "No match".  Fix: find the ONE full-body maychange assumption whose 2nd state
   arg is s177 (the final state), MP it, then subsumed.  Fallbacks retained. *)
let close_goal10 : tactic =
  fun (asl,w) ->
    let is_mc c = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) c with _->false in
    (* The stepper may leave several MAYCHANGE-bearing assumptions; the RIGHT one is the full-body `bigR s0 s177`.
       Try each maychange assumption with MATCH_MP pth + SUBSUMED; whichever works wins.  First establish
       the current-group output-store bound `4*i+3 < nblocks` (SUBSUMED needs it for out_p containment). *)
    let pth = prove(`R s s' ==> R subsumed R' ==> R' s s'`, REWRITE_TAC[subsumed] THEN MESON_TAC[]) in
    (* establish the out_p-store bound SUBSUMED needs.  Body-leg: 4*i+3<nblocks (from i<loop_count-2).
       FILL (i=0, concrete blocks 0..3): 8<=nblocks (from 2<=loop_count) covers it.  Assert both via TRY. *)
    (TRY(SUBGOAL_THEN `4*i+3 < nblocks` ASSUME_TAC THENL
      [MAP_EVERY (fun t -> TRY(UNDISCH_TAC t))
         [`nblocks DIV 4 = loop_count`; `i < loop_count - 1`; `i < loop_count - 2`; `2 <= loop_count`] THEN ARITH_TAC;
       ALL_TAC]) THEN
     TRY(SUBGOAL_THEN `8 <= nblocks` ASSUME_TAC THENL
      [MAP_EVERY (fun t -> TRY(UNDISCH_TAC t))
         [`nblocks DIV 4 = loop_count`; `2 <= loop_count`] THEN ARITH_TAC;
       ALL_TAC]) THEN
     (* try each maychange assumption; the correct cumulative s0 s177 one works via pth+SUBSUMED.
        Also try the shipped idiom (MONOTONE) + folding all maychange asms as fallbacks. *)
     (* the correct cumulative `bigR s0 s177` closes via MATCH_MP pth + REWRITE[ETA;ABI] + SUBSUMED.
        REWRITE ABI is ESSENTIAL: the declared frame's MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI must be
        expanded to the register list so SUBSUMED can check per-reg containment. *)
     (fun (asl2,w2) ->
        let mcths = List.filter_map (fun (_,th) -> if is_mc(concl th) then Some th else None) asl2 in
        (FIRST (map (fun th -> fun g ->
            (MATCH_MP_TAC(MATCH_MP pth th) THEN
             REWRITE_TAC[ETA_AX; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
             SUBSUMED_MAYCHANGE_TAC) g) mcths)) (asl2,w2))) (asl,w);;

(* per-conjunct dispatcher.  The expensive close_goal7 (BITBLAST + reduce reconstruction) is gated to
   run ONLY on the Q30 conjunct (is_eq & RHS mentions nist_ghash).  Every OTHER goal gets a broad FIRST
   over all the cheap closers, so routing can't mis-fire on subtle shape differences - whichever closes
   wins, and if none do the goal is left for the dump. *)
(* CHEAP closers only - close_goal7 (Q30, expensive) is EXCLUDED and applied separately ONCE.  The Q30
   conjunct (is_eq & RHS nist_ghash) is explicitly SKIPPED here (fail) so the loop leaves it for the
   dedicated pass; every other goal gets the broad FIRST. *)

(* ---- FINAL single-tactic dispatcher for the assembled prove(): applied to EACH conjunct after
   REPEAT CONJ_TAC.  Shape-gated so close_goal7 (expensive) runs only on the Q30 (NG) conjunct and
   close_goal10 only on the frame.  Each branch fully closes-or-fails. ---- *)
let close_all_tac : tactic =
  fun (asl,w) ->
    let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
    let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
    let dispatch (asl,w) =
      if has_mc w then close_goal10 (asl,w)                                    (* MAYCHANGE frame *)
      else if has "aligned_bytes_loaded" w then ASM_REWRITE_TAC[] (asl,w)      (* aligned (preserved asm) *)
      else if is_forall w then MUST close_goal9 (asl,w)                        (* output-forall *)
      else if is_eq w && has "nist_ghash" (rhs w) then close_goal7 (asl,w)     (* Q30 GHASH tag *)
      else
        (FIRST (map MUST
          [ close_ksfold; close_goal9;
            el 0 closers_0_6; el 1 closers_0_6; el 2 closers_0_6; close_ctr176; el 3 closers_0_6;
            el 4 closers_0_6; el 5 closers_0_6; el 6 closers_0_6;
            close_lanejoin; close_subwordpin; close_goal8; CONV_TAC WORD_RULE ])) (asl,w) in
    dispatch (asl,w)
    ;;

(* The assembled body-leg tactic (single prove()): step + split + dispatch. *)
let body_leg_tac : tactic =
  step_body_tac THEN REPEAT CONJ_TAC THEN close_all_tac;;

(* ===== the assembled body-leg theorem: one loop body inv i @0x1ec -> inv(i+1) @0x4b0. ===== *)
let BODYLEG = prove(body_goal, body_leg_tac);;

(* ============================================================================
   FILL leg: 0x88 -> 0x1ec establishing swp_inv 0 (i=0), for the steady case 2 <= loop_count.
   The fill 0x88..0x1ec runs 89 instructions: the guard cbz x1@0x88 is not taken (loop_count>=1), and
   the 0x1e4 sub x1,#1 + cbz@0x1e8 fall through for loop_count>=2, with FILL stopping at 0x1ec just
   after.  Endpoint invariant = swp_inv 0 (mid-pipeline) so the closers reconstruct the i=0 partials.
   ============================================================================ *)
let mk_fill_goal inv =
  mk_imp(`([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
      EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk) /\
     len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
     2 <= loop_count /\ 16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
     nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,1856) /\
     nonoverlapping (out_p:int64,16 * nblocks) (in_p:int64,16 * nblocks) /\
     nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,192) /\
     nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
     nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
     nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (word pc:int64,1856) /\
     nonoverlapping (tag_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (tag_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (ivec_p:int64,16) (word pc:int64,1856) /\
     nonoverlapping (ivec_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (ivec_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,1856) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (in_p:int64,16*nblocks) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,192)`,
   list_mk_icomb "ensures" [`arm`;
     mk_abs(`s:armstate`, list_mk_conj
       [`aligned_bytes_loaded s (word pc) aes128_gcm_enc_mc`; `read PC s = word (pc + 0x88)`;
        `read X0 s = in_p`; `read X2 s = out_p`; `read X3 s = tag_p`; `read X4 s = ivec_p`;
        `read X6 s = htable_p`; `read SP s = stackpointer`;
        `read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0`;
        `read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c)`;
        `read Q18 s = word_reversefields 8 (EL 0 rk)`; `read Q19 s = word_reversefields 8 (EL 1 rk)`;
        `read Q20 s = word_reversefields 8 (EL 2 rk)`; `read Q21 s = word_reversefields 8 (EL 3 rk)`;
        `read Q22 s = word_reversefields 8 (EL 4 rk)`; `read Q23 s = word_reversefields 8 (EL 5 rk)`;
        `read Q24 s = word_reversefields 8 (EL 6 rk)`; `read Q25 s = word_reversefields 8 (EL 7 rk)`;
        `read Q26 s = word_reversefields 8 (EL 8 rk)`; `read Q27 s = word_reversefields 8 (EL 9 rk)`;
        `read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64`;
        `read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64`;
        `read Q7 s = word 13979173243358019584`;
        `read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64`;
        `read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64`;
        `read X13 s = word_zx (word c:int32):int64`; `read X15 s = word(len_bits DIV 8)`;
        `read X1 s = word loop_count`; `read X7 s = word nblocks`; `read X16 s = word loop_remain`;
        `read Q30 s = byteswap128 tag0`;
        `htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s`;
        `!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j`]) ;
     leg_state inv `0x1ec` `0` ;
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`]);;
let fill_goal = mk_fill_goal swp_inv;;

(* FILL setup: like the body-leg setup but at 0x88 entry.  The guard cbz x1@0x88: x1=word loop_count,
   loop_count>=2 so val(word loop_count)=loop_count != 0 -> not taken -> falls to 0x8c.  The mid-FILL
   sub x1,#1 @0x1e4 + cbz@0x1e8: after it x1=word(loop_count-1); for loop_count>=2, loop_count-1 != 0
   -> cbz not taken -> falls to 0x1ec (the head).  Input-split blocks 0..7 (the fill reads groups 0,1). *)
let FILL_INPUT_SPLIT_TAC =
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s0 = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 3)))) s0 = inblock 3 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 4)))) s0 = inblock 4 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 5)))) s0 = inblock 5 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 6)))) s0 = inblock 6 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 7)))) s0 = inblock 7`
   STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `7 < nblocks` ASSUME_TAC THENL
      [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16 * 0 = 0`; ARITH_RULE `16 * 1 = 16`; ARITH_RULE `16 * 2 = 32`;
     ARITH_RULE `16 * 3 = 48`; ARITH_RULE `16 * 4 = 64`; ARITH_RULE `16 * 5 = 80`;
     ARITH_RULE `16 * 6 = 96`; ARITH_RULE `16 * 7 = 112`; WORD_ADD_0]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
     check (fun th -> let c = concl th in is_eq c && free_in `in_p:int64` (lhs c) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))));;

(* fill guard-resolution: val(word loop_count)=loop_count, ~(loop_count=0), and after sub@0x1e4:
   val(word_sub(word loop_count)(word 1))=loop_count-1, ~(loop_count-1=0). *)
let fill_valfacts_tac =
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `16 * nblocks < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(loop_count = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (word loop_count) (word 1):int64) = loop_count - 1` ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word 1:int64) <= val(word loop_count:int64)` MP_TAC THENL
     [REWRITE_TAC[VAL_WORD_1] THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[VAL_WORD_SUB_CASES; th; VAL_WORD_1]) THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `~(loop_count - 1 = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC];;

(* FILL merge sites (first-89-instruction prefix): (11,192)(12,176)(19,160)
   (24,208)(31,192)(37,208).  Verify by disasm if the diagnostic shows mis-merges. *)
let fill_merges = [(11,192);(12,176);(19,160);(24,208);(31,192);(37,208)];;

let fill_step_tac =
  STRIP_TAC THEN REWRITE_TAC[fst AES128_GCM_ENC_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  FILL_INPUT_SPLIT_TAC THEN
  fill_valfacts_tac THEN
  (* guard cbz@0x88: step 1, resolve the COND via ~(loop_count=0) *)
  ARM_STEPS_TAC AES128_GCM_ENC_EXEC [1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word loop_count:int64) = loop_count`;
                             ASSUME `~(loop_count = 0)`; COND_CLAUSES]) THEN
  (* steps 2..88 with per-step subword + MERGE at fill_merges; then step 89 (the mid cbz) resolves via
     the loop_count-1 valfacts; then 90..N to reach 0x1ec.  The stepper keeps the i=0 partials. *)
  SWP_STEPS_TAC enc_anchors [] REDSETX AES128_GCM_ENC_EXEC (K ALL_TAC) fill_merges (2--88) THEN
  ARM_STEPS_TAC AES128_GCM_ENC_EXEC [89] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word_sub (word loop_count) (word 1):int64) = loop_count - 1`;
                             ASSUME `~(loop_count - 1 = 0)`; COND_CLAUSES]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[];;

(* ---- FILL closers.  With a symbolic initial counter c the group-0 counter blocks are the symbolic
   reassembled-lane form (no concrete packed constant), so the counter/aesNc conjuncts fold directly via
   the symbolic mk_cbv at counters 4*0+c .. 4*0+c+3, exactly as the body leg does. ---- *)

(* FILL per-conjunct dispatcher (i=0, no Q30 tower). *)
let fill_close_all : tactic =
  fun (asl,w) ->
    let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
    let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
    (if has_mc w then close_goal10 (asl,w)
    else if has "aligned_bytes_loaded" w then ASM_REWRITE_TAC[] (asl,w)
    else if is_forall w then
      (* output-forall j<4*0: vacuous *) (REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT] THEN
        REWRITE_TAC[ARITH_RULE `j < 0 <=> F`]) (asl,w)
    else
      (REWRITE_TAC[ZXNEST4; ZXZX32; GSYM WORD_ADD] THEN FIRST (map MUST
        [ (* ptrs: in_p = word_add in_p (word(64*0)) *)
          (REWRITE_TAC[ARITH_RULE `64*0=0`; WORD_ADD_0] THEN REFL_TAC);
          (* Q30: byteswap128 tag0 = byteswap128(nist_ghash..(4*0)) *)
          (REWRITE_TAC[ARITH_RULE `4*0=0`; list_of_seq; nist_ghash]);
          (* X13: sim next-counter lane = word_zx(word(4*0+c+4)) *)
          (REWRITE_TAC[ZXNEST4; ZXZX32] THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC);
          (* [sp+160] counter ctr(4*0+c): sim lane-form is bare `word c`; normalize 4*0+c->c then mk_cbv c *)
          (REWRITE_TAC[ARITH_RULE `4 * 0 + c = c`; ZXNEST4; ZXZX32] THEN ACCEPT_TAC(mk_cbv `c:num`));
          (* [sp+176] counter ctr(4*0+c+1) *)
          (REWRITE_TAC[ARITH_RULE `4 * 0 + c + 1 = c + 1`; ZXNEST4; ZXZX32] THEN ACCEPT_TAC(mk_cbv `(c:num) + 1`));
          (* aes7c(4*0+c+2) *)
          (REWRITE_TAC[ARITH_RULE `4 * 0 + c + 2 = c + 2`; aes7c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
           ACCEPT_TAC(mk_cbv `(c:num) + 2`));
          (* aes8c(4*0+c+1) *)
          (REWRITE_TAC[ARITH_RULE `4 * 0 + c + 1 = c + 1`; aes8c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
           ACCEPT_TAC(mk_cbv `(c:num) + 1`));
          (* aes10p(4*0+c+3) *)
          (REWRITE_TAC[ARITH_RULE `4 * 0 + c + 3 = c + 3`; aes10p] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
           ACCEPT_TAC(mk_cbv `(c:num) + 3`));
          (* X1: word_sub(word loop_count)(word 1) = word(loop_count-(0+1)) = word(loop_count-1); needs
             1<=loop_count (from 2<=loop_count). *)
          (fun (a,w) ->
            let bnd = try snd(find (fun (_,th)->concl th = `2 <= loop_count`) a) with _ -> TRUTH in
            (REWRITE_TAC[ARITH_RULE `(0:num)+1=1`] THEN
             SUBGOAL_THEN `1 <= loop_count` ASSUME_TAC THENL [MP_TAC bnd THEN ARITH_TAC; ALL_TAC] THEN
             ASM_SIMP_TAC[WORD_SUB; VAL_WORD_1] THEN REWRITE_TAC[GSYM VAL_WORD_1] THEN
             AP_TERM_TAC THEN MP_TAC bnd THEN ARITH_TAC) (a,w));
          (* lane pins Q10/Q15/[sp+192/208]: word_join(word_xor lanes)=word_xor(inblock(4*0+2/3))(rk10) *)
          (REWRITE_TAC[ARITH_RULE `4*0+2=2`; ARITH_RULE `4*0+3=3`] THEN REWRITE_TAC[JOIN_XOR_LANES]);
          (* subword pins X23/X28: word_xor(subword..)=subword(word_xor(inblock(4*0+1))(rk10))(lane) *)
          (REWRITE_TAC[ARITH_RULE `4*0+1=1`] THEN CONV_TAC WORD_BLAST);
          CONV_TAC WORD_RULE ])) (asl,w))
    ;;

(* Prove a leg and GEN_ALL the result.  NB: prove(mk_imp(precond, ...)) does NOT auto-generalize the free
   vars (unlike prove of an explicit `!vars. ...`), so GEN_ALL is essential: otherwise MATCH_MP_TAC of the
   leg treats key_p (free) as fixed and leaves NO ?key_p, and the caller's EXISTS_TAC key_p (in CORE_FROM88)
   fails with "Goal not existentially quantified". *)
let leaf_prove label goal tac = GEN_ALL(prove(goal, tac));;

(* ===== the FILL theorem (single prove) ===== *)
let FILLLEG = leaf_prove "FILLLEG" fill_goal (fill_step_tac THEN REPEAT CONJ_TAC THEN fill_close_all);;

(* ============================================================================
   DRAINTAIL leg: g5 of the WHILE = swp_inv(loop_count-1) @ 0x4b0 -> post @ 0x710.
   Decompose:
     REDUCELAST : swp_inv(loop_count-1) @0x4b0 -> BRIDGE @0x61c
                  (cbnz@0x4b0 NOT taken since X1=word 0; reduce_last drains the in-flight GHASH,
                   settles Q30 4*(loop_count-1)->4*loop_count, stores the last group's 4 outputs.)
     TAILLEG  : BRIDGE @0x61c -> post @0x710.
   The BRIDGE state is the 0x61c post (settled seam): X0/X2 = ptr+64*loop_count, X1=word 0,
   X13=word(4*loop_count+2), Q30=byteswap128(nist_ghash..(4*loop_count)), all j<4*loop_count stored.
   Frame = the BROAD frame (adds tag_p, ivec_p) - the tail writes them; the WHILE needs ONE shared frame.
   BODYLEG/FILLLEG (narrow frame) are widened to this broad frame at glue time via ENSURES_FRAME_SUBSUMED.
   ============================================================================ *)

(* The shared BROAD frame, used uniformly across all legs. *)
let swps_broad_frame =
  `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
   MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
   MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
   MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks);
              memory :> bytes(tag_p:int64, 16); memory :> bytes(ivec_p:int64, 16);
              memory :> bytes(word_add stackpointer (word 160):int64, 64)]`;;

(* The full nonoverlapping precondition shared by all legs (with key_p
   dropped - the loop does not touch key_p; matches mk_body_goal's set + adds the key-free ones). *)
let swps_leg_precond =
  `([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
      EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk) /\
     len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
     2 <= loop_count /\ 16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
     nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,1856) /\
     nonoverlapping (out_p:int64,16 * nblocks) (in_p:int64,16 * nblocks) /\
     nonoverlapping (out_p:int64,16 * nblocks) (key_p:int64,176) /\
     nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,192) /\
     nonoverlapping (tag_p:int64,16) (word pc:int64,1856) /\
     nonoverlapping (tag_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (tag_p:int64,16) (key_p:int64,176) /\
     nonoverlapping (tag_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (ivec_p:int64,16) (word pc:int64,1856) /\
     nonoverlapping (ivec_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (ivec_p:int64,16) (key_p:int64,176) /\
     nonoverlapping (ivec_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,1856) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (in_p:int64,16*nblocks) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (key_p:int64,176) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,192) /\
     nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
     nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
     nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
     nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64)`;;

(* the BRIDGE state @0x61c (settled seam).  Everything indexed at 4*loop_count. *)
let swps_bridge_post =
  mk_abs(`s:armstate`, list_mk_conj
    [`aligned_bytes_loaded s (word pc) aes128_gcm_enc_mc`; `read PC s = word (pc + 0x61c)`;
     `read X0 s = word_add in_p (word (64 * loop_count))`;
     `read X2 s = word_add out_p (word (64 * loop_count))`;
     `read X3 s = tag_p`; `read X4 s = ivec_p`; `read X6 s = htable_p`; `read SP s = stackpointer`;
     `read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0`;
     `read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c)`;
     `read Q18 s = word_reversefields 8 (EL 0 rk)`; `read Q19 s = word_reversefields 8 (EL 1 rk)`;
     `read Q20 s = word_reversefields 8 (EL 2 rk)`; `read Q21 s = word_reversefields 8 (EL 3 rk)`;
     `read Q22 s = word_reversefields 8 (EL 4 rk)`; `read Q23 s = word_reversefields 8 (EL 5 rk)`;
     `read Q24 s = word_reversefields 8 (EL 6 rk)`; `read Q25 s = word_reversefields 8 (EL 7 rk)`;
     `read Q26 s = word_reversefields 8 (EL 8 rk)`; `read Q27 s = word_reversefields 8 (EL 9 rk)`;
     `read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64`;
     `read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64`;
     `read Q7 s = word 13979173243358019584`;
     `read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64`;
     `read X12 s = word_zx (word_zx (word_subword
         (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64`;
     `read X13 s = word_zx (word (4 * loop_count + c):int32):int64`;
     `read X15 s = word(len_bits DIV 8)`; `read X1 s = word 0`; `read X16 s = word loop_remain`;
     `read Q30 s = byteswap128
          (nist_ghash (aes128_cipher (word 0) rk) tag0
             (list_of_seq (nist_cipher_block c nonce rk inblock) (4 * loop_count)))`;
     `htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s`;
     `!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j`;
     `!j. j < 4 * loop_count ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
              word_xor (aes_ctr_block c nonce rk j) (inblock j)`]);;

(* REDUCELAST goal: precond swp_inv(loop_count-1) @0x4b0 -> swps_bridge_post @0x61c, broad frame. *)
let reducelast_goal =
  mk_imp(swps_leg_precond,
   list_mk_icomb "ensures" [`arm`;
     leg_state swp_inv `0x4b0` `loop_count - 1` ;
     swps_bridge_post ;
     swps_broad_frame]);;

(* REDUCELAST setup: at 0x4b0 with inv(loop_count-1).  Set m = loop_count-1 so the state is inv(m)@0x4b0
   (X1 = word(loop_count-(m+1)) = word 0).  Input blocks needed: the LAST group 4m+0..3 (= 4*loop_count-4
   ..4*loop_count-1); no prefetch group (4m+4 = 4*loop_count is out of range for loop_remain=0, and the
   drain doesn't load it - it only completes the in-flight reduce + stores the last outputs).
   Guard: cbnz@0x4b0 with X1=word 0 -> val(word 0)=0 -> NOT taken -> falls to 0x4b4. *)
let reducelast_merges = [(8,176);(28,160)];;  (* the 2 counter stp sites in reduce_last: stp[sp,#176]@0x4cc=step8, stp[sp,#160]@0x51c=step28 (rel 0x4b0=step1) *)

let REDUCELAST_INPUT_SPLIT_TAC =
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * (4*m+0))))) s0 = inblock (4*m+0) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*m+1))))) s0 = inblock (4*m+1) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*m+2))))) s0 = inblock (4*m+2) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*m+3))))) s0 = inblock (4*m+3)`
   STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `4*m+3 < nblocks` ASSUME_TAC THENL
      [MAP_EVERY (fun t -> TRY(UNDISCH_TAC t))
         [`nblocks DIV 4 = loop_count`; `loop_count = m + 1`; `2 <= loop_count`] THEN ARITH_TAC; ALL_TAC] THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16 * (4*m+0) = 64*m`; ARITH_RULE `16 * (4*m+1) = 64*m+16`;
     ARITH_RULE `16 * (4*m+2) = 64*m+32`; ARITH_RULE `16 * (4*m+3) = 64*m+48`]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
     check (fun th -> let c = concl th in is_eq c && free_in `in_p:int64` (lhs c) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))));;

(* val facts for the guard cbnz@0x4b0: X1 = word 0 (inv(loop_count-1) X1 conjunct simplifies via
   loop_count-((loop_count-1)+1)=0).  We introduce m=loop_count-1, rewrite the X1 read to word 0. *)
let reducelast_step_tac =
  STRIP_TAC THEN REWRITE_TAC[fst AES128_GCM_ENC_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  ABBREV_TAC `m = loop_count - 1` THEN
  SUBGOAL_THEN `loop_count = m + 1` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  (* simplify the X1 read to word 0.  After ABBREV_TAC m=loop_count-1, the inv X1 conjunct
     `word(loop_count - ((loop_count-1)+1))` has its `loop_count-1` folded to m, becoming
     `word(loop_count - (m+1))`; with loop_count=m+1 that is word((m+1)-(m+1)) = word 0.  Rewrite the
     X1 read in place (match on `read X1 s0 = word(loop_count - (m+1))`, robust to the ABBREV fold). *)
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read X1 s0 = word (loop_count - (m + 1))`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ASSUME `loop_count = m + 1`;
                     ARITH_RULE `(m + 1) - (m + 1) = 0`] th)
    else NO_TAC) THEN
  REDUCELAST_INPUT_SPLIT_TAC THEN
  (* guard cbnz@0x4b0: step 1, X1=word 0 -> val 0 -> not taken *)
  ARM_STEPS_TAC AES128_GCM_ENC_EXEC [1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_0; COND_CLAUSES]) THEN
  (* steps 2..91 (reduce_last 0x4b4..0x618) with per-step subword + MERGE; the stepper keeps the reduce set. *)
  SWP_STEPS_TAC enc_anchors [] REDSETX AES128_GCM_ENC_EXEC (K ALL_TAC) reducelast_merges (2--91) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* REDUCELAST closer: the bridge post @0x61c.  Indexing: precond is inv(m) with m=loop_count-1, so the
   bridge (indexed at loop_count = m+1) appears as "(m+1)"-forms.  Q30 settles 4m -> 4m+4 = 4*(m+1) via
   the DRAIN reconstruction (the 4-block settled-acc tag-settle).  output-forall
   splits into OLD (j<4m, from inv) + the last group (4m+0..3).  Most other conjuncts are settled regs. *)
let reducelast_close_ghash : tactic =
  (* Q30: word_subword(word_join(drain tower))(64,128) = byteswap128(nist_ghash..(4*(m+1))).  The 4 last
     cipherblocks fold from the pipeline pins (aes7c/8c/10p + fresh v0), then the reduce reconstruction
     (settled sofar@4m + 4 blocks -> 4m+4).  Reuse close_goal7's body but with m-indexing (sofar@4m). *)
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th =
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) asl)
      with _ -> failwith "reducelast_close_ghash: no rk-hyp" in
    let ksf = MATCH_MP KEYSTREAM_FOLD rkth in
    let ghostpins = List.filter_map (fun (_,th) ->
      let c = concl th in
      if is_eq c then (match lhs c with
        | Var(nm,_) when String.length nm>=6 && String.sub nm 0 6="ghost_"
            && can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="inblock" with _->false)) (rhs c)
          -> Some th | _ -> None) else None) asl in
    (
    (* normalize the tag index 4*(m+1) -> 4*m+4 and fold the 4 last-group keystreams. *)
    REWRITE_TAC[ARITH_RULE `4*(m+1) = 4*m+4`] THEN
    REWRITE_TAC(JOIN_SUBWORD_RECOMBINE :: ghostpins) THEN
    REWRITE_TAC[GSYM AES10P_VIA_AES7C; GSYM AES10P_VIA_AES8C; GSYM aes10p] THEN
    REWRITE_TAC[JOIN_XOR_LANES] THEN
    REWRITE_TAC[ksf] THEN
    REWRITE_TAC[ARITH_RULE `4*m+c+3 = (4*m+3)+c`; ARITH_RULE `4*m+c+2 = (4*m+2)+c`;
                ARITH_RULE `4*m+c+1 = (4*m+1)+c`; ARITH_RULE `4*m+0 = 4*m`] THEN
    REWRITE_TAC[CT_TO_NCB] THEN
    REWRITE_TAC[ARITH_RULE `(4*m+0)+2 = 4*m+2`; ARITH_RULE `(4*m+1)+2 = 4*m+3`;
                ARITH_RULE `(4*m+2)+2 = 4*m+4`; ARITH_RULE `(4*m+3)+2 = 4*m+5`;
                ARITH_RULE `4*m+0 = 4*m`] THEN
    (* reduce reconstruction (4*m variant). *)
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
    SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC [byteswap128; WORD_BLAST
      `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
       word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
    MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y
      ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
    MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block c nonce rk inblock) (4 * m)))`;
      `cipherblock_0 = nist_cipher_block c nonce rk inblock (4 * m)`;
      `cipherblock_1 = nist_cipher_block c nonce rk inblock (4 * m + 1)`;
      `cipherblock_2 = nist_cipher_block c nonce rk inblock (4 * m + 2)`;
      `cipherblock_3 = nist_cipher_block c nonce rk inblock (4 * m + 3)`;
      `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
      `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
      `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`;
      `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
    REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
    TRANS_TAC EQ_TRANS
     `polyval_reduce_prop3
          (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
          (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
          (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
          (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
      REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
      REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
      ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
       `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM karatsuba_join] THEN MATCH_ACCEPT_TAC KARATSUBA_JOIN_XOR4;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                   `[cipherblock_1;cipherblock_2;cipherblock_3]:(int128)list`;
                   `sofar:int128`; `cipherblock_0:int128`]
                  GHASH_POLYVAL_ACC_BATCHED) THEN
    REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
     `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    EXPAND_TAC "sofar" THEN
    REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
    REWRITE_TAC[ARITH_RULE `4*m+4 = SUC(SUC(SUC(SUC(4*m))))`] THEN
    REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    REWRITE_TAC[APPEND] THEN
    REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL]
    ) (asl,w);;

(* output-forall for the bridge: j < 4*(m+1) splits into OLD (j<4m, from inv's output-forall) + the last
   group (4m+0..3).  Mirrors close_goal9 but at m/(m+1) indexing. *)
let reducelast_close_outputs : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th =
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) asl)
      with _ -> failwith "reducelast_close_outputs: no rk-hyp" in
    (REWRITE_TAC[ARITH_RULE `4 * (m+1) = 4*m+4`] THEN
     REWRITE_TAC[ARITH_RULE `j < 4*m+4 <=>
                          j < 4 * m \/ j = 4*m+0 \/ j = 4*m+1 \/ j = 4*m+2 \/ j = 4*m+3`] THEN
     ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
     REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
     REWRITE_TAC[ARITH_RULE `16 * (4*m+0) = 64*m`; ARITH_RULE `16 * (4*m+1) = 64*m+16`;
        ARITH_RULE `16 * (4*m+2) = 64*m+32`; ARITH_RULE `16 * (4*m+3) = 64*m+48`] THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
     REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
     REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
     ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
     REWRITE_TAC[aes_ctr_block] THEN
     REWRITE_TAC[ARITH_RULE `4 * i + c + 3 = (4 * i + 3) + c`;
                 ARITH_RULE `4 * i + c + 2 = (4 * i + 2) + c`;
                 ARITH_RULE `4 * i + c + 1 = (4 * i + 1) + c`;
                 ARITH_RULE `4 * i + 0 = 4 * i`] THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC[GSYM AES10P_VIA_AES7C; GSYM AES10P_VIA_AES8C] THEN
     REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD rkth]) (asl,w);;

(* REDUCELAST per-conjunct dispatcher (m = loop_count-1 in context; bridge indexed at m+1). *)
let reducelast_close_all : tactic =
  fun (asl,w) ->
    let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
    let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
    (if has_mc w then close_goal10 (asl,w)
    else if has "aligned_bytes_loaded" w then ASM_REWRITE_TAC[] (asl,w)
    else if is_forall w then MUST reducelast_close_outputs (asl,w)
    else if is_eq w && has "nist_ghash" (rhs w) then reducelast_close_ghash (asl,w)
    else
      (FIRST (map MUST
        [ (* X0/X2 ptr: word_add p (word(64*m+64)) = word_add p (word(64*(m+1))) *)
          (REWRITE_TAC[ARITH_RULE `64*(m+1)=64*m+64`; LEFT_ADD_DISTRIB] THEN CONV_TAC WORD_RULE);
          (* X13: word_zx(word(4*m+6)) = word_zx(word(4*(m+1)+2)) *)
          (REWRITE_TAC[ARITH_RULE `4*(m+1)+2 = 4*m+6`] THEN CONV_TAC WORD_RULE);
          (* X13 (symbolic c): word_zx(word(4*m+c+4)) = word_zx(word(4*(m+1)+c)) -- num-level, not WORD_RULE *)
          (AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);
          (* X1: word 0 (already settled) *)
          REFL_TAC;
          CONV_TAC WORD_RULE;
          CONV_TAC WORD_BLAST ])) (asl,w))
    ;;

let REDUCELAST = leaf_prove "REDUCELAST" reducelast_goal
         (reducelast_step_tac THEN REPEAT CONJ_TAC THEN reducelast_close_all);;

(* ============================================================================
   TAILLEG: BRIDGE @0x61c -> final spec @0x710, over the tail region 0x4b4..0x73c.
   Precond = swps_bridge_post's body (the 0x61c seam); post = the two
   memory facts (output blocks + settled tag + ivec writeback); broad frame.
   ============================================================================ *)
(* per-step subword normalizer that leaves (forall j) region invariants untouched. *)
let SUBWORD_NONFORALL =
  RULE_ASSUM_TAC(fun th ->
    if is_forall (concl th) then th
    else CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) th);;

(* the tail needs NO `2 <= loop_count` (it runs for any loop_count incl 0/1, so its precondition
   omits it).  FROM88's leg-2 reaches TAILLEG for ALL loop_count, so TAILLEG must not require it, else
   the 2<=loop_count precond subgoal can't be discharged from FROM88's (case-split) context. *)
let swps_tail_precond =
  list_mk_conj(filter (fun c -> c <> `2 <= loop_count`) (conjuncts swps_leg_precond));;
let swps_tail_goal =
  mk_imp(swps_tail_precond,
   list_mk_icomb "ensures" [`arm`;
     swps_bridge_post ;
     mk_abs(`s:armstate`, list_mk_conj
       [`read PC s = word (pc + 0x710)`;
        `!i. i < nblocks ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                 word_xor (aes_ctr_block c nonce rk i) (inblock i)`;
        `read (memory :> bytes128 tag_p) s =
           word_reversefields 8
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block c nonce rk inblock) nblocks))`;
        `read (memory :> bytes128 ivec_p) s =
           word_reversefields 8 (ctr_block nonce (nblocks + c))`;
        `read X0 s = word (len_bits DIV 8)`]) ;
     swps_broad_frame]);;

let swps_tail_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  (*** loop_remain = 0: no tail iterations, just the finalize (ivec/tag writeback) ***)
  ASM_CASES_TAC `loop_remain = 0` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `ivec_p:int64` (lhs c) &&
        not(free_in `out_p:int64` (lhs c)) && not(free_in `key_p:int64` (lhs c)) &&
        not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `n MOD 4 = 0 ==> 4 * n DIV 4 = n`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV(fun t ->
      if is_eq t && free_in `ivec_p:int64` (lhs t) &&
         not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
      then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[ZX_COUNTER_UD; CTR_ZX_NORM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128; ctr_block] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  (*** loop_remain >= 1: tail loop via ENSURES_WHILE (0x62c head, 0x6f8 back-edge) ***)
  ENSURES_WHILE_UP_TAC `loop_remain:num` `pc + 0x62c` `pc + 0x6f8`
    `\i s.
      read X0  s = word_add in_p  (word (64 * loop_count + 16 * i)) /\
      read X2  s = word_add out_p (word (64 * loop_count + 16 * i)) /\
      read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
      read SP s = stackpointer /\
      read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
      read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
      read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
      read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
      read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
      read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
      read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
      read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
      read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
      read Q7 s = word 13979173243358019584 /\
      read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
      read X12 s = word_zx (word_zx (word_subword
          (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
      read X13 s = word_zx (word (4 * loop_count + i + c):int32):int64 /\
      read X15 s = word(len_bits DIV 8) /\ read X16 s = word(loop_remain - i) /\
      read Q30 s = byteswap128
          (nist_ghash (aes128_cipher (word 0) rk) tag0
             (list_of_seq (nist_cipher_block c nonce rk inblock) (4 * loop_count + i))) /\
      htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
      read Q12 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
      read Q14 s = word_join
       (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1))
       (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
        (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
      (!j. j < 4 * loop_count + i
           ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
               word_xor (aes_ctr_block c nonce rk j) (inblock j))` THEN
  ASM_REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
   [(*** base case: bridge 0x61c -> 0x62c, i=0 ***)
    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (1--3) THEN
    ARM_STEPS_TAC AES128_GCM_ENC_EXEC [4] THEN
    SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      EXPAND_TAC "loop_remain" THEN
      W(fun _ -> MP_TAC(SPECL [`nblocks:num`;`4`] MOD_LT_EQ)) THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> match concl th with
      | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),Var("s4",_))),
             Comb(Comb(Comb(Const("COND",_),_),_),_)) ->
          ASSUME_TAC(REWRITE_RULE[ASSUME `val(word loop_remain:int64) = loop_remain`;
                                  ASSUME `~(loop_remain = 0)`; COND_CLAUSES] th)
      | _ -> NO_TAC) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0];

    (*** loop body: 0x62c -> 0x6f8, one block; Inv(i) -> Inv(i+1) ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes128 (word_add in_p (word (64 * loop_count + 16 * i)))) s0 =
      inblock (4 * loop_count + i)`
    ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `64 * a + 16 * b = 16 * (4 * a + b)`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_TAIL_CONV o
      check (fun th -> let c = concl th in
        is_eq c && free_in `in_p:int64` (lhs c) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))) THEN
    SUBGOAL_THEN `4 * loop_count + i < nblocks` ASSUME_TAC THENL
     [MAP_EVERY (fun t -> UNDISCH_TAC t)
        [`i < loop_remain`; `nblocks MOD 4 = loop_remain`; `nblocks DIV 4 = loop_count`] THEN
      ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN SUBWORD_NONFORALL) (1--5) THEN
    MERGE_CTR128_TAC 160 "s5" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN SUBWORD_NONFORALL) (6--28) THEN
    MERGE_CTR128_TAC 160 "s28" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN SUBWORD_NONFORALL) (29--51) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `j < a + i + 1 <=> j < a + i \/ j = a + i`] THEN
    ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
    REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
    REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0; ADD_0] THEN
    REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
    REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
    REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
    ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
    REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
    DISCARD_STATE_TAC "s51" THEN
    REWRITE_TAC[ADD_ASSOC; ARITH] THEN
    REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
    REWRITE_TAC[GSYM cipher_block] THEN
    REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
    SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    FIRST_ASSUM(fun th -> if can (term_match []
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) (concl th)
      then REWRITE_TAC[th] else NO_TAC) THEN
    REPEAT(CONJ_TAC THENL
      [CONV_TAC WORD_RULE ORELSE (AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);
       ALL_TAC]) THEN
    REWRITE_TAC [byteswap128; WORD_BLAST
    `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
     word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
    MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y
      ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
    MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block c nonce rk inblock) (4 * loop_count + i)))`;
      `cipherblock = nist_cipher_block c nonce rk inblock (4 * loop_count + i)`;
      `h = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
      `k = karatsuba_mid h`] THEN
    REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
    TRANS_TAC EQ_TRANS
      `polyval_reduce_prop3 (word_pmul (word_xor sofar cipherblock:int128) (h:int128))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
      REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      ASM_REWRITE_TAC[] THEN LET_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "k" THEN REWRITE_TAC[karatsuba_mid] THEN
      ASM_REWRITE_TAC[] THEN REPEAT LET_TAC THEN
      REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM polyval_dot] THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[h_power] THEN
    REWRITE_TAC[GSYM NIST_DOT_IS_POLYVAL_DOT] THEN
    REWRITE_TAC[ARITH_RULE `(k + 1) = SUC k`] THEN
    REWRITE_TAC[list_of_seq; NIST_GHASH_APPEND; NIST_GHASH_CONS; nist_ghash] THEN
    ASM_REWRITE_TAC[];

    (*** trivial loop-back: 0x6f8 test taken ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC AES128_GCM_ENC_EXEC [1] THEN
    SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      EXPAND_TAC "loop_remain" THEN
      W(fun _ -> MP_TAC(SPECL [`nblocks:num`;`4`] MOD_LT_EQ)) THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; VAL_EQ_0; WORD_SUB_EQ_0] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ] THEN ASM_ARITH_TAC;

    (*** finalize: 0x6f8 test not taken -> ivec/tag writeback -> 0x710 ***)
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `ivec_p:int64` (lhs c) &&
        not(free_in `out_p:int64` (lhs c)) && not(free_in `key_p:int64` (lhs c)) &&
        not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    SUBGOAL_THEN `nblocks = 4 * loop_count + loop_remain` SUBST_ALL_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV(fun t ->
      if is_eq t && free_in `ivec_p:int64` (lhs t) &&
         not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
      then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[ZX_COUNTER_UD] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128; ctr_block] THEN
    REWRITE_TAC[ADD_ASSOC; ZX_COUNTER_UD; CTR_ZX_NORM] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC WORD_BLAST];;

let TAILLEG = leaf_prove "TAILLEG" swps_tail_goal swps_tail_tac;;

(* ============================================================================
   Frame-widening: BODYLEG/FILLLEG are proven with the NARROW frame (no tag_p/ivec_p).  The WHILE + tail
   need the shared BROAD frame.  ENSURES_FRAME_SUBSUMED widens: narrow subsumed broad /\ ensures P Q narrow
   ==> ensures P Q broad.  narrow subsumed broad discharges by SUBSUMED_MAYCHANGE_TAC (broad = narrow + more).
   ============================================================================ *)
(* widen the frame of an `[hyps] |- ensures arm P Q narrow` thm to the broad frame. *)
let widen_frame_to_broad th =
  let narrow = rand(concl th) in
  let subth = prove(list_mk_icomb "subsumed" [narrow; swps_broad_frame],
     REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) in
  MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ subth th);;

(* BODYLEG_BROAD / FILLLEG_BROAD : the same legs, broad frame, precond re-DISCHed, then RE-GENERALIZED
   over the leg's original universally-quantified vars (so downstream `SPEC `loop_count-2`` / MATCH_MP_TAC
   work).  Works whether or not the leg's conclusion carries leading foralls: SPEC_ALL strips any that are
   present, we widen the bare `pre ==> ensures`, then GENL re-closes over exactly those vars, or over the
   free variables when there were none. *)
let widen_leg leg =
  let vars,body = strip_forall (concl leg) in
  let leg0 = SPEC_ALL leg in                    (* leg0 : pre ==> ensures ... (vars now free) *)
  let pre = lhand(concl leg0) in
  let broad = DISCH pre (widen_frame_to_broad (UNDISCH leg0)) in
  (* re-generalize: prefer the leg's own forall vars; if none, close over the free vars. *)
  GENL (if vars = [] then frees(concl broad) else vars) broad;;
let BODYLEG_BROAD = widen_leg BODYLEG;;
let FILLLEG_BROAD = widen_leg FILLLEG;;

(* ============================================================================
   DRAINLEG: the g5/lc2 DRAIN = inv(loop_count-2) @0x1ec -> bridge @0x61c, broad frame.  Composes
   BODYLEG_BROAD@(loop_count-2) (0x1ec->0x4b0, lands inv(loop_count-1)) ;; REDUCELAST (0x4b0->0x61c) via
   ENSURES_SEQUENCE@0x4b0.  A SINGLE combined leg so both the WHILE g5
   AND the loop_count=2 degenerate case dispatch to it uniformly (index loop_count-2), with no fragile
   goal-index rewrites.  BODYLEG_BROAD's post-index (loop_count-2)+1 is rewritten to loop_count-1 IN THE
   THEOREM (from 2<=loop_count arith), never in the goal. ============================================ *)
let swps_drain_goal =
  mk_imp(swps_leg_precond,
    list_mk_icomb "ensures" [`arm`;
      leg_state swp_inv `0x1ec` `loop_count - 2` ;
      swps_bridge_post ;
      swps_broad_frame]);;

let DRAINLEG =
    let th = GEN_ALL(prove(swps_drain_goal,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
     SUBGOAL_THEN `(loop_count - 2) + 1 = loop_count - 1` ASSUME_TAC THENL
      [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
     ENSURES_SEQUENCE_TAC `pc + 0x4b0`
       (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,`loop_count - 1`))))) THEN
     CONJ_TAC THENL
      [(* BODYLEG_BROAD @ i:=loop_count-2.  Rewrite the waypoint post inv(loop_count-1) -> inv((loop_count-2)+1)
          [via GSYM of the SUBGOAL] so MATCH_MP_TAC BODYLEG_BROAD unifies i:=loop_count-2 directly (same robust
          pattern as the WHILE g3 half; the earlier INST[loop_count-2/i] form no-matched because GEN_ALL may
          rename the bound var away from `i`).  Then discharge BODYLEG's precond (loop_count-2<loop_count-1). *)
       FIRST_X_ASSUM(fun th -> if concl th = `(loop_count - 2) + 1 = loop_count - 1`
         then REWRITE_TAC[SYM th] else NO_TAC) THEN
       REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
       MATCH_MP_TAC BODYLEG_BROAD THEN ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;
       (* REDUCELAST: inv(loop_count-1)@0x4b0 -> bridge@0x61c.  Its precond forall-binds key_p (only in
          nonoverlapping hyps), so MATCH_MP_TAC leaves ?key_p; supply the actual key_p. *)
       REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
       MATCH_MP_TAC REDUCELAST THEN EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[]])) in
    th;;

(* ============================================================================
   MAINLEG: the main body 0x88 -> 0x61c (FILL + software-pipelined WHILE + DRAIN), with the
   DISTINCT-pc physical loop realized as a SEAM-TO-SEAM
   WHILE at 0x1ec (g3 body = 0x1ec->0x4b0 [BODYLEG_BROAD] ;; 0x4b0->0x1ec [backedge cbnz taken]; g4 trivial;
   g5 = DRAIN = BODYLEG_BROAD@(loop_count-2) ;; REDUCELAST).  Precond = the 0x88 preamble-end state; post = bridge.
   ============================================================================ *)
(* the 0x88 preamble-end precondition (= FILL's precond body, restated for the sequence). *)
let swps_pre88 = mk_abs(`s:armstate`, list_mk_conj
   [`aligned_bytes_loaded s (word pc) aes128_gcm_enc_mc`; `read PC s = word (pc + 0x88)`;
    `read X0 s = in_p`; `read X2 s = out_p`; `read X3 s = tag_p`; `read X4 s = ivec_p`;
    `read X6 s = htable_p`; `read SP s = stackpointer`;
    `read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0`;
    `read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c)`;
    `read Q18 s = word_reversefields 8 (EL 0 rk)`; `read Q19 s = word_reversefields 8 (EL 1 rk)`;
    `read Q20 s = word_reversefields 8 (EL 2 rk)`; `read Q21 s = word_reversefields 8 (EL 3 rk)`;
    `read Q22 s = word_reversefields 8 (EL 4 rk)`; `read Q23 s = word_reversefields 8 (EL 5 rk)`;
    `read Q24 s = word_reversefields 8 (EL 6 rk)`; `read Q25 s = word_reversefields 8 (EL 7 rk)`;
    `read Q26 s = word_reversefields 8 (EL 8 rk)`; `read Q27 s = word_reversefields 8 (EL 9 rk)`;
    `read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64`;
    `read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64`;
    `read Q7 s = word 13979173243358019584`;
    `read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64`;
    `read X12 s = word_zx (word_zx (word_subword
        (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64`;
    `read X13 s = word_zx (word c:int32):int64`; `read X15 s = word(len_bits DIV 8)`;
    `read X1 s = word loop_count`; `read X7 s = word nblocks`; `read X16 s = word loop_remain`;
    `read Q30 s = byteswap128 tag0`;
    `htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s`;
    `!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j`]);;

let swps_leg1_goal =
  mk_imp(swps_leg_precond,
    list_mk_icomb "ensures" [`arm`; swps_pre88; swps_bridge_post; swps_broad_frame]);;

(* the WHILE body-invariant (swp_inv with the aligned_bytes_loaded folded in) used by ENSURES_WHILE_UP_TAC.
   The rule wants a num->armstate->bool; swp_inv already is that (modulo the aligned/PC which the rule adds). *)
let swps_while_inv = swp_inv;;

(* no-op tactic marking the WHILE-glue legs (FILL/g1..g5/DRAIN); a readable structural label. *)
let LOG (_:string) : tactic = ALL_TAC;;

let swps_leg1_tac =
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     (* expand the ABI macro into ASSIGNS so ENSURES_SEQUENCE/WHILE's C,,C=C idempotence
        (MAYCHANGE_IDEMPOT_TAC -> ASSIGNS_SEQ_ABSORB_CONV) can decompose the frame.  Each MATCH_MP_TAC
        of a leg (whose frame keeps ABI FOLDED) is preceded by GSYM to re-fold. *)
     REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
     (* FILL: 0x88 -> 0x1ec, inv 0 *)
     ENSURES_SEQUENCE_TAC `pc + 0x1ec`
       (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,`0`))))) THEN
     CONJ_TAC THENL
      [(* FILL leg discharges this; re-fold ABI so FILLLEG_BROAD's frame matches. *)
       LOG "FILL" THEN REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
       MATCH_MP_TAC FILLLEG_BROAD THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     (* now: inv 0 @0x1ec -> bridge @0x61c, broad frame. Case-split loop_count = 2. *)
     ASM_CASES_TAC `loop_count = 2` THENL
      [(* loop_count=2: WHILE runs 0 iters; DRAIN directly.  Pre = inv 0 (from FILL) but DRAINLEG wants
          inv(loop_count-2); ENSURES_PRECONDITION_TAC changes the pre to inv(loop_count-2)@0x1ec, proving
          the FILL-post => it via the loop_count=2 rewrite (2-2=0, scoped to the whole predicate - safe).
          Then MATCH_MP_TAC DRAINLEG. *)
       LOG "lc2" THEN
       (fun (asl,w) ->
         (* dpre = aligned /\ PC=0x1ec /\ <inv(loop_count-2) body>, built with the SAME single-BETA_CONV
            +ADD_CLAUSES normalization, so the impl-goal `!s. dpre s ==> FILL-post s`
            (FILL-post = inv 0, same normalization) closes via loop_count->2, 2-2->0, REWRITE[] (X==>X). *)
         let sv = `s:armstate` in
         let invbody = rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES])
                         (mk_comb(swp_inv,`loop_count - 2`)))) in
         let invbody_s = rhs(concl(BETA_CONV(mk_comb(invbody,sv)))) in
         let dpre = mk_abs(sv, list_mk_conj(
           [`aligned_bytes_loaded s (word pc) aes128_gcm_enc_mc`;
            `read PC s = word (pc + 0x1ec)`] @ conjuncts invbody_s)) in
         (ENSURES_PRECONDITION_TAC dpre THEN
          CONJ_TAC THENL
           [(* impl goal: !x. A x ==> B x, where A (inv 0) and B (inv(loop_count-2)) become IDENTICAL
               under loop_count=2.  GEN_TAC, normalize the whole `A==>B` (loop_count->2 + 2-2->0 +
               NUM_REDUCE, both sides -> the same C), leaving C==>C; DISCH_THEN ACCEPT_TAC closes it. *)
            GEN_TAC THEN
            CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
            ASM_REWRITE_TAC[ARITH_RULE `2 - 2 = 0`; ADD_CLAUSES] THEN
            CONV_TAC(DEPTH_CONV NUM_REDUCE_CONV) THEN
            DISCH_THEN ACCEPT_TAC;
            REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
            MATCH_MP_TAC DRAINLEG THEN EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[]]) (asl,w));
       ALL_TAC] THEN
     (* loop_count >= 3: FILL(done) + seam-to-seam WHILE(loop_count-2) at 0x1ec + DRAIN. *)
     LOG "before-WHILE" THEN
     ENSURES_WHILE_UP_TAC `loop_count - 2` `pc + 0x1ec` `pc + 0x1ec` swps_while_inv THEN
     REPEAT CONJ_TAC THENL
      [(* g1 ~(loop_count-2 = 0) *)
       LOG "g1" THEN UNDISCH_TAC `~(loop_count = 2)` THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;
       (* g2 base: inv 0 @0x1ec -> inv 0 @0x1ec (identity).  Leftover after ASM_REWRITE:
          word(loop_count-1) = word(loop_count-(0+1)) [the X1 pin]; fold 0+1=1 (ADD_CLAUSES). *)
       LOG "g2" THEN ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
       REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[];
       (* g3 body: inv i @0x1ec -> inv(i+1) @0x1ec, via 0x4b0 (BODYLEG_BROAD ;; backedge) *)
       LOG "g3" THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
       ENSURES_SEQUENCE_TAC `pc + 0x4b0`
         (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,`i+1`))))) THEN
       CONJ_TAC THENL
        [(* g3 first half: goal post is inv(i+1)@0x4b0 = BODYLEG_BROAD's post exactly; MATCH_MP_TAC
            unifies i:=i, leaves BODYLEG_BROAD's precond as subgoal (discharge from the g3 hyps). *)
         LOG "g3-BODY" THEN REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
         MATCH_MP_TAC BODYLEG_BROAD THEN ASM_REWRITE_TAC[] THEN
         MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`i < loop_count - 2`; `2 <= loop_count`] THEN ARITH_TAC;
         (* backedge cbnz@0x4b0 taken (X1=word(loop_count-(i+2))!=0 for i<loop_count-2) -> 0x1ec.
            Expand htable_mem_4 in BOTH the asm (s0) and goal so the 6 htable reads carry through the
            1-instr step (cbnz doesn't touch htable memory) and ASM_REWRITE closes them at s1. *)
         ENSURES_INIT_TAC "s0" THEN
         RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
         SUBGOAL_THEN `val(word (loop_count - (i + 2)):int64) = loop_count - (i + 2) /\ ~(loop_count - (i+2) = 0)`
         STRIP_ASSUME_TAC THENL
          [CONJ_TAC THENL
            [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
             MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC;
             MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`i < loop_count - 2`] THEN ARITH_TAC]; ALL_TAC] THEN
         (* the inv(i+1) X1 conjunct is word(loop_count-((i+1)+1)) = word(loop_count-(i+2)) *)
         RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(i+1)+1 = i+2`]) THEN
         ARM_STEPS_TAC AES128_GCM_ENC_EXEC [1] THEN
         RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word (loop_count - (i + 2)):int64) = loop_count - (i + 2)`;
                                     ASSUME `~(loop_count - (i+2) = 0)`; COND_CLAUSES]) THEN
         ENSURES_FINAL_STATE_TAC THEN
         (* leftover: word(loop_count-(i+2)) = word(loop_count-((i+1)+1)) [X1 pin] + the 6 htable reads
            (goal's htable_mem_4 was pre-expanded).  Fold (i+1)+1=i+2, then ASM_REWRITE closes the X1 eq
            and the 6 htable reads (carried to s1 from the expanded s0 asms). *)
         REWRITE_TAC[ARITH_RULE `(i+1)+1 = i+2`] THEN ASM_REWRITE_TAC[]];
       (* g4 back-edge trivial (pc1=pc2=0x1ec identity) *)
       LOG "g4" THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
       REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[];
       (* g5 DRAIN: inv(loop_count-2) @0x1ec -> bridge @0x61c.  This IS DRAINLEG's goal (modulo the
          key_p existential MATCH_MP_TAC leaves - supply key_p). *)
       LOG "g5" THEN REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
       MATCH_MP_TAC DRAINLEG THEN EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[]];;

(* GEN_ALL so FROM88's MATCH_MP_TAC MAINLEG THEN EXISTS_TAC key_p works (prove of a mk_imp does NOT
   auto-generalize; key_p would stay free and no ?key_p would be left). *)
let MAINLEG = GEN_ALL(prove(swps_leg1_goal, swps_leg1_tac));;

(* ============================================================================
   MAINLEG_LC1: loop_count=1 degenerate leg (0x88 -> 0x61c): A_0 ; reduce_last (B_0 as drain).
   The two stepped regions are 0x88..0x1e4 (A_0) and 0x4b4..0x618 (reduce_last). ============================ *)
let MAINLEG_LC1 = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer nblocks loop_count loop_remain.
       [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk /\
       len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\
       nblocks MOD 4 = loop_remain /\
       loop_count = 1 /\
       16 * nblocks < 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (out_p,16 * nblocks) (word pc,1856) /\
       nonoverlapping (out_p,16 * nblocks) (in_p,16 * nblocks) /\
       nonoverlapping (out_p,16 * nblocks) (key_p,176) /\
       nonoverlapping (out_p,16 * nblocks) (htable_p,192) /\
       nonoverlapping (tag_p:int64,16) (word pc,1856) /\
       nonoverlapping (tag_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (tag_p:int64,16) (key_p,176) /\
       nonoverlapping (tag_p:int64,16) (htable_p,192) /\
       nonoverlapping (ivec_p:int64,16) (word pc,1856) /\
       nonoverlapping (ivec_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (ivec_p:int64,16) (key_p,176) /\
       nonoverlapping (ivec_p:int64,16) (htable_p,192) /\
       nonoverlapping (word_add stackpointer (word 160),64) (word pc,1856) /\
       nonoverlapping (word_add stackpointer (word 160),64) (in_p,16 * nblocks) /\
       nonoverlapping (word_add stackpointer (word 160),64) (key_p,176) /\
       nonoverlapping (word_add stackpointer (word 160),64) (htable_p,192) /\
       nonoverlapping (out_p,16 * nblocks) (tag_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (ivec_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (word_add stackpointer (word 160),64) /\
       nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
       nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160),64) /\
       nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160),64)
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes128_gcm_enc_mc /\
           read PC s = word (pc + 0x88) /\
           read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
           read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
           read Q18 s = word_reversefields 8 (EL 0 rk) /\
           read Q19 s = word_reversefields 8 (EL 1 rk) /\
           read Q20 s = word_reversefields 8 (EL 2 rk) /\
           read Q21 s = word_reversefields 8 (EL 3 rk) /\
           read Q22 s = word_reversefields 8 (EL 4 rk) /\
           read Q23 s = word_reversefields 8 (EL 5 rk) /\
           read Q24 s = word_reversefields 8 (EL 6 rk) /\
           read Q25 s = word_reversefields 8 (EL 7 rk) /\
           read Q26 s = word_reversefields 8 (EL 8 rk) /\
           read Q27 s = word_reversefields 8 (EL 9 rk) /\
           read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
           read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
           read Q7 s = word 13979173243358019584 /\
           read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
           read X12 s = word_zx (word_zx (word_subword
               (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
           read X13 s = word_zx (word c:int32):int64 /\ read X15 s = word(len_bits DIV 8) /\
           read X1 s = word loop_count /\ read X7 s = word nblocks /\ read X16 s = word loop_remain /\
           read Q30 s = byteswap128 tag0 /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
           (!i. i < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s = inblock i))
      (\s. aligned_bytes_loaded s (word pc) aes128_gcm_enc_mc /\
           read PC s = word (pc + 0x61c) /\
           read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
        read Q18 s = word_reversefields 8 (EL 0 rk) /\
        read Q19 s = word_reversefields 8 (EL 1 rk) /\
        read Q20 s = word_reversefields 8 (EL 2 rk) /\
        read Q21 s = word_reversefields 8 (EL 3 rk) /\
        read Q22 s = word_reversefields 8 (EL 4 rk) /\
        read Q23 s = word_reversefields 8 (EL 5 rk) /\
        read Q24 s = word_reversefields 8 (EL 6 rk) /\
        read Q25 s = word_reversefields 8 (EL 7 rk) /\
        read Q26 s = word_reversefields 8 (EL 8 rk) /\
        read Q27 s = word_reversefields 8 (EL 9 rk) /\
        read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
        read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
        read Q7 s = word 13979173243358019584 /\
        read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
        read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word (4 * loop_count + c):int32):int64 /\
        read X15 s = word(len_bits DIV 8) /\ read X1 s = word 0 /\
        read X16 s = word loop_remain /\
        read Q30 s = byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block c nonce rk inblock) (4 * loop_count))) /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
        (!j. j < 4 * loop_count
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block c nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nblocks);
                  memory :> bytes(tag_p, 16); memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[htable_mem_4] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  ENSURES_INIT_TAC "s0" THEN
  (*** derive the 4 group-0 input blocks from the nblocks-forall (nblocks >= 4) ***)
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s0 = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 3)))) s0 = inblock 3`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `4 <= nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ARITH_RULE `16 * 0 = 0`; ARITH_RULE `16 * 1 = 16`;
    ARITH_RULE `16 * 2 = 32`; ARITH_RULE `16 * 3 = 48`; WORD_ADD_0]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_TAIL_CONV o
    check (fun th -> let c = concl th in
      is_eq c && can (find_term (fun t -> t = `(memory :> bytes128 in_p)`)) (lhs c))) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
    check (fun th -> let c = concl th in
      is_eq c && free_in `in_p:int64` (lhs c) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (1--11) THEN
  MERGE_CTR128_TAC 192 "s11" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (12--12) THEN
  MERGE_CTR128_TAC 176 "s12" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (13--19) THEN
  MERGE_CTR128_TAC 160 "s19" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (20--24) THEN
  MERGE_CTR128_TAC 208 "s24" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (25--31) THEN
  MERGE_CTR128_TAC 192 "s31" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (32--37) THEN
  MERGE_CTR128_TAC 208 "s37" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (38--96) THEN
  MERGE_CTR128_TAC 176 "s96" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (97--116) THEN
  MERGE_CTR128_TAC 160 "s116" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (117--179) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_THEN `loop_count = 1` SUBST_ALL_TAC THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `j < 4 <=> j = 0 \/ j = 1 \/ j = 2 \/ j = 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 4 * i = 64 * i`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(4 * i + 2) + n = 4 * i + (2 + n)`] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[(prove(`word 144115188075855872:int64 = word_shl (word_zx (word_bytereverse (word 2:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 216172782113783808:int64 = word_shl (word_zx (word_bytereverse (word 3:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 288230376151711744:int64 = word_shl (word_zx (word_bytereverse (word 4:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 360287970189639680:int64 = word_shl (word_zx (word_bytereverse (word 5:int32)):int64) 32`, CONV_TAC WORD_BLAST))] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
  REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `(1:num) + c = c + 1`; ARITH_RULE `(2:num) + c = c + 2`;
              ARITH_RULE `(3:num) + c = c + 3`; ARITH_RULE `(4:num) + c = c + 4`;
              ARITH_RULE `(0:num) + c = c`] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
  DISCARD_STATE_TAC "s179" THEN
  REWRITE_TAC[ADD_ASSOC; ARITH] THEN
  (*** loop_count=1 => the 4 blocks have LITERAL counters 2,3,4,5, so the symbolic     ***)
  (*** AES_CTR_BLOCK_RECONSTRUCT (pattern i+2) cannot fire; use its i=0 specialization. ***)
  REWRITE_TAC[REWRITE_RULE[ADD_CLAUSES]
               (INST [`0`,`i:num`] AES_CTR_BLOCK_RECONSTRUCT)] THEN
  REWRITE_TAC[GSYM cipher_block] THEN
  REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  FIRST_ASSUM(fun th -> if can (term_match []
      `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  REPEAT(CONJ_TAC THENL
    [CONV_TAC WORD_RULE ORELSE (AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);
     ALL_TAC]) THEN
  REWRITE_TAC [byteswap128; WORD_BLAST
  `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
   word_join (word_subword h (0,64):int64)
             (word_subword l (64,64):int64)`] THEN
  MATCH_MP_TAC(BITBLAST_RULE
   `x:int128 = y
    ==> word_join (word_subword x (0,64):int64)
                  (word_subword x (64,64):int64):int128 =
        word_join (word_subword y (0,64):int64)
                  (word_subword y (64,64):int64):int128`) THEN
  (*** loop_count=1 => the GHASH accumulator is still tag0 (nist_ghash h tag0 [] = tag0), ***)
  (*** so there is no `sofar` to abbreviate: block 0 is word_xor tag0 cipherblock_0.       ***)
  MAP_EVERY ABBREV_TAC
   [`cipherblock_0 = nist_cipher_block c nonce rk inblock 0`;
    `cipherblock_1 = nist_cipher_block c nonce rk inblock 1`;
    `cipherblock_2 = nist_cipher_block c nonce rk inblock 2`;
    `cipherblock_3 = nist_cipher_block c nonce rk inblock 3`;
    `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
    `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
    `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`;
    `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
   `polyval_reduce_prop3
        (word_xor
        (word_pmul (cipherblock_3:int128) (h0:int128))
        (word_xor
        (word_pmul (cipherblock_2:int128) (h1:int128))
        (word_xor
        (word_pmul (cipherblock_1:int128) (h2:int128))
        (word_pmul (word_xor (tag0:int128) cipherblock_0)
                   (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
    REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[karatsuba_mid] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
     `word_pmul (word_xor a b) (word_xor c d) =
      word_pmul (word_xor b a) (word_xor c d)`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM karatsuba_join] THEN MATCH_ACCEPT_TAC KARATSUBA_JOIN_XOR4;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                 `[cipherblock_1;cipherblock_2;cipherblock_3]:(int128)list`;
                 `tag0:int128`; `cipherblock_0:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
   `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
  CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL]);;


(* ============================================================================
   CORE_FROM88: main body 0x88 -> 0x710 (leg1 case-split
   loop_count 0/1/>=2 -> MAINLEG_LC1/MAINLEG ; leg2 TAILLEG). ============================ *)
let core_from88_stmt =
  `!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer nblocks loop_count loop_remain.
       [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk /\
       len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\
       nblocks MOD 4 = loop_remain /\
       16 * nblocks < 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (out_p,16 * nblocks) (word pc,1856) /\
       nonoverlapping (out_p,16 * nblocks) (in_p,16 * nblocks) /\
       nonoverlapping (out_p,16 * nblocks) (key_p,176) /\
       nonoverlapping (out_p,16 * nblocks) (htable_p,192) /\
       nonoverlapping (tag_p:int64,16) (word pc,1856) /\
       nonoverlapping (tag_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (tag_p:int64,16) (key_p,176) /\
       nonoverlapping (tag_p:int64,16) (htable_p,192) /\
       nonoverlapping (ivec_p:int64,16) (word pc,1856) /\
       nonoverlapping (ivec_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (ivec_p:int64,16) (key_p,176) /\
       nonoverlapping (ivec_p:int64,16) (htable_p,192) /\
       nonoverlapping (word_add stackpointer (word 160),64) (word pc,1856) /\
       nonoverlapping (word_add stackpointer (word 160),64) (in_p,16 * nblocks) /\
       nonoverlapping (word_add stackpointer (word 160),64) (key_p,176) /\
       nonoverlapping (word_add stackpointer (word 160),64) (htable_p,192) /\
       nonoverlapping (out_p,16 * nblocks) (tag_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (ivec_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (word_add stackpointer (word 160),64) /\
       nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
       nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160),64) /\
       nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160),64)
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes128_gcm_enc_mc /\
           read PC s = word (pc + 0x88) /\
           read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
           read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
           read Q18 s = word_reversefields 8 (EL 0 rk) /\
           read Q19 s = word_reversefields 8 (EL 1 rk) /\
           read Q20 s = word_reversefields 8 (EL 2 rk) /\
           read Q21 s = word_reversefields 8 (EL 3 rk) /\
           read Q22 s = word_reversefields 8 (EL 4 rk) /\
           read Q23 s = word_reversefields 8 (EL 5 rk) /\
           read Q24 s = word_reversefields 8 (EL 6 rk) /\
           read Q25 s = word_reversefields 8 (EL 7 rk) /\
           read Q26 s = word_reversefields 8 (EL 8 rk) /\
           read Q27 s = word_reversefields 8 (EL 9 rk) /\
           read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
           read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
           read Q7 s = word 13979173243358019584 /\
           read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
           read X12 s = word_zx (word_zx (word_subword
               (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
           read X13 s = word_zx (word c:int32):int64 /\ read X15 s = word(len_bits DIV 8) /\
           read X1 s = word loop_count /\ read X7 s = word nblocks /\ read X16 s = word loop_remain /\
           read Q30 s = byteswap128 tag0 /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
           (!i. i < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s = inblock i))
      (\s. read PC s = word (pc + 0x710) /\
           (!i. i < nblocks
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block c nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block c nonce rk inblock) nblocks)) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nblocks + c)) /\
           read X0 s = word (len_bits DIV 8))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nblocks);
                  memory :> bytes(tag_p, 16); memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])`;;
let core_from88_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  (*** Sequence at the tail-entry pc+0x61c: leg 1 = fill+loop+drain (main body, produces the
   *** first 4*loop_count blocks + settles tag=ghash(4*loop_count)); leg 2 = the single-block
   *** tail, discharged by TAILLEG.  The waypoint predicate is EXACTLY TAILLEG's
   *** precondition (the bridge state). ***)
  ENSURES_SEQUENCE_TAC `pc + 0x61c`
   `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
        read Q18 s = word_reversefields 8 (EL 0 rk) /\
        read Q19 s = word_reversefields 8 (EL 1 rk) /\
        read Q20 s = word_reversefields 8 (EL 2 rk) /\
        read Q21 s = word_reversefields 8 (EL 3 rk) /\
        read Q22 s = word_reversefields 8 (EL 4 rk) /\
        read Q23 s = word_reversefields 8 (EL 5 rk) /\
        read Q24 s = word_reversefields 8 (EL 6 rk) /\
        read Q25 s = word_reversefields 8 (EL 7 rk) /\
        read Q26 s = word_reversefields 8 (EL 8 rk) /\
        read Q27 s = word_reversefields 8 (EL 9 rk) /\
        read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
        read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
        read Q7 s = word 13979173243358019584 /\
        read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
        read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word (4 * loop_count + c):int32):int64 /\
        read X15 s = word(len_bits DIV 8) /\ read X1 s = word 0 /\
        read X16 s = word loop_remain /\
        read Q30 s = byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block c nonce rk inblock) (4 * loop_count))) /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
        (!j. j < 4 * loop_count
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block c nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(*** leg 1: fill + main loop + drain (pc+0x88 -> pc+0x61c).  Case-split on the group
     *** count BEFORE stepping so each case stays a clean `ensures` (dispatchable by lemma). ***)
    ASM_CASES_TAC `loop_count = 0` THENL
     [(*** loop_count = 0: cbz@0x88 taken -> 0x61c, nothing produced (tag still ghash([])=tag0).
       *** Substitute loop_count=0 BEFORE INIT (post-INIT, FIRST_X_ASSUM would grab a read-eq). ***)
      UNDISCH_THEN `loop_count = 0` SUBST_ALL_TAC THEN
      ENSURES_INIT_TAC "s0" THEN
      RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      ARM_STEPS_TAC AES128_GCM_ENC_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[htable_mem_4; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0;
                      list_of_seq; nist_ghash] THEN
      REWRITE_TAC[CONJUNCT1 LT];
      (*** loop_count >= 1: run A_0 (the group-0 producer, 0x8c..0x1e0), then the
       *** sub x1,#1 ; cbz x1,0x4b4.  If loop_count = 1 the cbz is taken -> reduce_last
       *** (B_0 as the drain), producing the bridge directly (MAINLEG_LC1).  If loop_count >= 2
       *** the cbz falls through to B_0 -> the seam 0x354, then the pipelined main loop and
       *** the reduce_last drain. ***)
      ASM_CASES_TAC `loop_count = 1` THENL
       [(*** loop_count = 1: A_0 ; reduce_last -> bridge (one group, no loop): MAINLEG_LC1.
         *** key_p appears only in MAINLEG_LC1's hyps, so MATCH_MP_TAC leaves it existential
         *** (supply it); ASM_REWRITE then discharges every hyp incl. loop_count=1. ***)
        LOG "F88-LC1" THEN REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
        MATCH_MP_TAC MAINLEG_LC1 THEN
        EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[];
        (*** loop_count >= 2: A_0 ; B_0 -> seam 0x354 ; main loop ; drain -> bridge.
         *** MAINLEG is exactly this leg (0x88 -> 0x61c); its precond/post/frame match this
         *** goal, so MATCH_MP_TAC applies after re-folding the ABI frame; supply key_p, then
         *** ASM_REWRITE discharges every hyp except `2 <= loop_count`, from ~(lc=0)/\~(lc=1). ***)
        LOG "F88-LC2" THEN REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
        MATCH_MP_TAC MAINLEG THEN
        EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[] THEN
        (* residual 2 <= loop_count (from ~(lc=0) /\ ~(lc=1)); ASM_ARITH_TAC uses all assms robustly. *)
        ASM_ARITH_TAC]];
    (*** leg 2: single-block tail (pc+0x61c -> pc+0x710) via TAILLEG.  TAILLEG's key_p
     *** appears only in its hyps (not its conclusion), so MATCH_MP_TAC leaves an existential
     *** over key_p; supply the actual key_p, then ASM_REWRITE discharges every hyp (incl. the
     *** rk-list fold and 16*nblocks<2^64, both carried as CORE_FROM88 assumptions). ***)
    LOG "F88-TAIL" THEN REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC TAILLEG THEN
    EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[]];;
let CORE_FROM88 = prove(core_from88_stmt, core_from88_tac);;

(* ============================================================================
   AES_GCM_..._SWP_S_CORRECT: the full-function correctness 0x2c -> 0x710 (preamble + CORE_FROM88).
   ============================ *)
let AES128_GCM_ENC_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer.
       aligned 16 stackpointer /\
       ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes128_gcm_enc_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
       PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes128_gcm_enc_mc /\
           read PC s = word (pc + 0x2c) /\
           read SP s = stackpointer /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p)  s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           wordlist_from_memory(key_p,11) s =
             MAP (word_reversefields 8) rk /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s =
                    inblock i) /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk))
                      htable_p s)
      (\s. read PC s = word (pc + 0x710) /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block c nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block c nonce rk inblock)
                              (val len_bits DIV 128))) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8
               (ctr_block nonce (val len_bits DIV 128 + c)) /\
           read X0 s = word (val len_bits DIV 8))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24;
                  X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])`,
  (*** setup boilerplate ***)
  GEN_TAC THEN GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst AES128_GCM_ENC_EXEC] THEN
  ABBREV_TAC `nblocks = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN STRIP_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  (*** round-key list length split ***)
  ASM_CASES_TAC `LENGTH(rk:int128 list) = 11` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LENGTH_EQ_LIST_OF_SEQ]) THEN
    CONV_TAC(LAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    EXPAND_TAC "rk" THEN REWRITE_TAC[MAP; CONS_11; GSYM CONJ_ASSOC] THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:int128 list->num`) THEN
    ASM_REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY; LENGTH_MAP]] THEN
  (*** sequence at the preamble-end pc+0x88; leg 1 = preamble, leg 2 = CORE_FROM88 ***)
  ENSURES_SEQUENCE_TAC `pc + 0x88`
   `\s. read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
        read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
        read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
        read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
        read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
        read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
        read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
        read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
        read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
        read Q7 s = word 13979173243358019584 /\
        read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
        read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word c:int32):int64 /\ read X15 s = word(len_bits DIV 8) /\
        read X1 s = word loop_count /\ read X7 s = word nblocks /\ read X16 s = word loop_remain /\
        read Q30 s = byteswap128 tag0 /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!i. i < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s = inblock i)` THEN
  CONJ_TAC THENL
   [(*** leg 1: preamble pc+0x2c -> pc+0x88 ***)
    REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN
    ENSURES_INIT_TAC "s0" THEN
    UNDISCH_TAC `read (memory :> bytes128 ivec_p) s0 = word_reversefields 8 (ctr_block nonce c)` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
    DISCH_TAC THEN
    ABBREV_TAC `ivlo:int64 = read (memory :> bytes64 ivec_p) s0` THEN
    ABBREV_TAC `ivhi:int64 = read (memory :> bytes64 (word_add ivec_p (word 8))) s0` THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 1) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `key_p:int64` (lhs c) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c) &&
        can (find_term (fun t -> t = `160`)) (lhs c))) THEN
    ARM_STEPS_TAC AES128_GCM_ENC_EXEC (1--23) THEN ENSURES_FINAL_STATE_TAC THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
      then ASSUME_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(fun th -> if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
        then ACCEPT_TAC(MATCH_MP X11_SETUP th) else NO_TAC);
      FIRST_ASSUM(fun th -> if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
        then ACCEPT_TAC(MATCH_MP X12_SETUP th) else NO_TAC);
      FIRST_ASSUM(fun th -> if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
        then ACCEPT_TAC(MATCH_MP X13_SETUP th) else NO_TAC);
      ASM_REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN MAP_EVERY EXPAND_TAC ["loop_count"; "nblocks"] THEN
      REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN EXPAND_TAC "nblocks" THEN
      AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN REWRITE_TAC[ARITH_RULE `3 = 2 EXP 2 - 1`] THEN
      REWRITE_TAC[WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
      MAP_EVERY EXPAND_TAC ["loop_remain"; "nblocks"] THEN
      AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST];
    (*** leg 2: main body pc+0x88 -> pc+0x710, via CORE_FROM88.  htable_mem_4 stays FOLDED
         here (only leg 1 expanded it); refold the ABI frame so the sequenced goal is a
         direct instance of CORE_FROM88.  key_p appears only in the hyps, so MATCH_MP_TAC
         leaves an existential we satisfy with the actual key_p. ***)
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC CORE_FROM88 THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[] THEN
    (*** CORE_FROM88's wrap-freedom hyp 16*nblocks<2^64: nblocks = len_bits DIV 128 and     ***)
    (*** W64_GEN_TAC gives len_bits < 2^64, so 16*nblocks <= len_bits/8 < 2^64.              ***)
    EXPAND_TAC "nblocks" THEN
    UNDISCH_TAC `len_bits < 2 EXP 64` THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine wrapper: same public contract as the non-pipelined kernel,     *)
(* recovered from the core theorem by wrapping the 224-byte-frame prologue /  *)
(* epilogue (11 saved-register steps each side) via ARM_ADD_RETURN_STACK_TAC. *)
(* ------------------------------------------------------------------------- *)

let AES128_GCM_ENC_SUBROUTINE_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock
    pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
      [(word pc, LENGTH aes128_gcm_enc_mc);
       (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes128_gcm_enc_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p)  s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           wordlist_from_memory(key_p,11) s =
             MAP (word_reversefields 8) rk /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s =
                    inblock i) /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk))
                      htable_p s)
      (\s. read PC s = returnaddress /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block c nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block c nonce rk inblock)
                              (val len_bits DIV 128))) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8
               (ctr_block nonce (val len_bits DIV 128 + c)) /\
           read X0 s = word (val len_bits DIV 8))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_sub stackpointer (word 224), 224)])`,
  REWRITE_TAC[fst AES128_GCM_ENC_EXEC; htable_mem_4] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
  ARM_ADD_RETURN_STACK_TAC
    ~pre_post_nsteps:(11, 11)
    AES128_GCM_ENC_EXEC
    (CONV_RULE(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV)
       (REWRITE_RULE[fst AES128_GCM_ENC_EXEC; htable_mem_4]
          AES128_GCM_ENC_CORRECT))
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
      D8; D9; D10; D11; D12; D13; D14; D15]` 224);;

(* ========================================================================= *)
(* Constant-time + memory-safety (appended to the correctness proof).        *)
(*                                                                           *)
(* Two theorems, both axiom-free:                                            *)
(*   ..._SWP_S_SAFE            -- core (pc+0x2c .. pc+0x6fc)                  *)
(*   ..._SWP_S_SUBROUTINE_SAFE -- whole function (pc .. returnaddress)       *)
(*                                                                           *)
(* The outer `exists f_events. forall <public args> ...` says the event      *)
(* trace is a FUNCTION of the public arguments only (independent of the      *)
(* secret plaintext/key bytes) = constant-time; the memaccess_inbounds       *)
(* conjunct says every load/store stays within the declared buffers =        *)
(* memory-safety.  The MAIN loop is single-buffered (X0/X2 advance 64*i,     *)
(* counter word(loop_count-1-i), STEADY runs loop_count-1 times); the TAIL   *)
(* is a plain WHILE.  See the core proof's control-flow map above.           *)
(* ========================================================================= *)

let EXEC = AES128_GCM_ENC_EXEC;;

let SAFE_SIM = SAFE_SIM_TAC EXEC;;

(* --- SWP-specific closers. --- *)

(* The pipeline is single-buffered: STEADY runs loop_count-1 times, so the DRAIN entry *)
(* pointer is base + 64*(loop_count-1) and must reconcile with the SEQUENCE post   *)
(* base + 64*loop_count.  DRAIN_ADDR normalises loop_count = (loop_count-1)+1 so    *)
(* WORD_RULE sees only linear combinations.                                        *)
let DRAIN_ADDR = DRAIN_ADDR_K `1`;;

(* Frugal branch-nonzero fact (no ASM_ over the post-sim context): cv = loop_count *)


(* Scaffold: e2 = APPEND (tail-simple) (APPEND (main-3way) prologue).  The main   *)
(* region has three paths: lc=0 (f_ev_m0), lc=1 (f_ev_m1 = fill+drain, no steady), *)
(* and lc>=2 (drain + ENUMERATEL(lc-2) steady + fill).                            *)
let OPEN_ENC = OPEN_SWP_SAFE EXEC;;

let scaffold_enc =
 `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64) (key_p:int64) (htable_p:int64)
   (len_bits:int64) (pc:num) (stackpointer:int64).
   APPEND
     (if val len_bits DIV 128 MOD 4 = 0 then
        f_ev_tail0 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer
      else
        APPEND
          (f_ev_tail_post in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)
          (APPEND
            (ENUMERATEL (val len_bits DIV 128 MOD 4)
              (\i. f_ev_tail_body in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer i))
            (f_ev_tail_pre in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)))
     (APPEND
       (if val len_bits DIV 128 DIV 4 = 0 then
          f_ev_m0 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer
        else if val len_bits DIV 128 DIV 4 = 1 then
          f_ev_m1 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer
        else if val len_bits DIV 128 DIV 4 = 2 then
          f_ev_m2 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer
        else
          APPEND
            (f_ev_drain in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)
            (APPEND
              (ENUMERATEL (val len_bits DIV 128 DIV 4 - 1)
                (\i. f_ev_steady in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer i))
              (f_ev_fill in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)))
       (f_ev_pro in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer))
   :(uarch_event) list`;;

let AES128_GCM_ENC_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes128_gcm_enc_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
      PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_enc_mc /\
               read PC s = word (pc + 0x2c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               read events s = e)
          (\s. read PC s = word (pc + 0x6fc) /\
               (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer /\
                    memaccess_inbounds e2
                      [in_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16; key_p, 176; htable_p, 192;
                       out_p, 16 * val len_bits DIV 128; word_add stackpointer (word 160), 64]
                      [out_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16;
                       word_add stackpointer (word 160), 64]))
          (\s s'. T)`,
  CONCRETIZE_F_EVENTS_TAC scaffold_enc THEN
  OPEN_ENC THEN

  (*** Top split at 0x61c (main region -> tail region). ***)
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x61c`
   `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\ read X16 s = word loop_remain` THEN
  CONJ_TAC THENL
   [(*** MAIN REGION pc+0x2c -> pc+0x61c (setup + pipelined loop). ***)
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x88`
     `\s. read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
          read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
          read X1 s = word loop_count /\ read X16 s = word loop_remain` THEN
    CONJ_TAC THENL [SAFE_SIM (1--23) THEN CLOSE; ALL_TAC] THEN

    (*** loop_count = 0 : cbz @0x88 taken -> 0x61c. ***)
    ASM_CASES_TAC `loop_count = 0` THENL
     [REDUCE_IF0 `loop_count:num` THEN SAFE_SIM (1--1) THEN CLOSE; ALL_TAC] THEN
    REDUCE_IFN0 `loop_count:num` THEN

    (*** loop_count = 1 : FILL (cbz @0x1e8 taken) + DRAIN. ***)
    ASM_CASES_TAC `loop_count = 1` THENL
     [REDUCE_IFEQ `loop_count:num` `1` THEN SAFE_SIM (1--179) THEN CLOSE; ALL_TAC] THEN
    REDUCE_IFNE `loop_count:num` `1` THEN

    (*** loop_count = 2 : FILL + one STEADY (cbnz @0x4b0 falls through) + DRAIN. ***)
    ASM_CASES_TAC `loop_count = 2` THENL
     [REDUCE_IFEQ `loop_count:num` `2` THEN SAFE_SIM (1--357) THEN CLOSE; ALL_TAC] THEN
    REDUCE_IFNE `loop_count:num` `2` THEN

    (*** loop_count >= 3 : FILL + STEADY(loop_count-1) + DRAIN. ***)
    (*** The pipeline is SINGLE-buffered: FILL does NOT prefetch a block, so X0/X2 ***)
    (*** advance by 64*i (not 64*i+64), the counter reads word(loop_count-1-i), ***)
    (*** and STEADY runs loop_count-1 times (matches correctness i<loop_count-1). ***)
    SUBGOAL_THEN `3 <= loop_count` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `loop_count - 1` `pc + 0x1ec` `pc + 0x4b4`
     `\i s. read X0 s = word_add in_p (word (64 * i)) /\
            read X2 s = word_add out_p (word (64 * i)) /\
            read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
            read SP s = stackpointer /\ read X16 s = word loop_remain /\
            read X1 s = word (loop_count - 1 - i)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [(*** ~(loop_count - 1 = 0) ***)
      ASM_ARITH_TAC;
      (*** FILL: 0x88 -> 0x1ec, establish inv 0.  BEQ_NZ resolves the loop-head    ***)
      (*** cbz during the sim, so REPEAT CONJ_TAC leaves exactly [X0; X2; X1; ev].  ***)
      BEQ_NZ `1` THEN SAFE_SIM (1--89) THEN
      BEQ_NZ `2` THEN
      REPEAT CONJ_TAC THENL
       [ADDR_RECON;
        ADDR_RECON;
        (* X1 = word(loop_count - 1 - 0) *)
        REWRITE_TAC[SUB_0] THEN GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `3 <= loop_count ==> 1 <= loop_count`];
        DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC];
      (*** back-edge / STEADY body: 0x1ec -> 0x4b4, inv i -> inv (i+1). ***)
      REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      SUBGOAL_THEN `loop_count - 1 < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SAFE_SIM (1--178) THEN CLOSE_R2;
      (*** DRAIN post-leg: 0x4b4 -> 0x61c. ***)
      SAFE_SIM (1--90) THEN REPEAT CONJ_TAC THENL
       [DRAIN_ADDR; DRAIN_ADDR; DEABBR THEN DISCHARGE_SAFE_ROBUST]];

    ALL_TAC] THEN

  (*** TAIL REGION pc+0x61c -> pc+0x6fc (plain WHILE on loop_remain). ***)
  ASM_CASES_TAC `loop_remain = 0` THENL
   [REDUCE_IF0 `loop_remain:num` THEN SAFE_SIM (1--4) THEN CLOSE_R2; ALL_TAC] THEN
  REDUCE_IFN0 `loop_remain:num` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `loop_remain:num` `pc + 0x62c` `pc + 0x6fc`
   `\i s. read X0 s = word_add in_p (word (64 * loop_count + 16 * i)) /\
          read X2 s = word_add out_p (word (64 * loop_count + 16 * i)) /\
          read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
          read SP s = stackpointer /\ read X16 s = word (loop_remain - i)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SAFE_SIM (1--4) THEN CLOSE_R2;
    ALL_TAC;
    REWRITE_TAC[] THEN SAFE_SIM [] THEN CLOSE_R2] THEN
  REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  SAFE_SIM (1--52) THEN CLOSE_R2);;


(* ------------------------------------------------------------------------- *)
(* Whole-function (subroutine) constant-time + memory-safety.                *)
(*                                                                           *)
(* The wrapper adds the byte-identical prologue (pc..0x2c, 11 saves, frame   *)
(* 224, x30 at sp+88) and epilogue (0x6fc..ret, 17 steps: mov x0,x15;        *)
(* rev64/str q30,[x3] tag; rev/str w14,[x4,#12] ctr; 11 ldp; add sp; ret).   *)
(* The invariant carries the saved-x30 slot (sp+88) so the epilogue restore  *)
(* + ret provably returns to returnaddress; and X3=tag_p / X4=ivec_p so the  *)
(* epilogue tag/counter stores are shown in-bounds.  The main loop uses the  *)
(* SAME single-buffered plumbing as the core proof (X0/X2 advance 64*i,       *)
(* counter word(loop_count-1-i), STEADY runs loop_count-1 times).            *)
(* ------------------------------------------------------------------------- *)

let AES128_GCM_ENC_SUBROUTINE_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
        [(word pc, LENGTH aes128_gcm_enc_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
      PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_enc_mc /\
               read PC s = word pc /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events in_p out_p tag_p ivec_p key_p htable_p len_bits pc
                           (word_sub stackpointer (word 224)) returnaddress /\
                    memaccess_inbounds e2
                      [in_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16; key_p, 176; htable_p, 192;
                       out_p, 16 * val len_bits DIV 128; word_sub stackpointer (word 224), 224]
                      [out_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16;
                       word_sub stackpointer (word 224), 224]))
          (\s s'. T)`,
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64) (key_p:int64) (htable_p:int64)
      (len_bits:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      APPEND
        (f_ev_epi in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)
        (APPEND
           (if val len_bits DIV 128 MOD 4 = 0 then
              f_ev_tail0 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress
            else
              APPEND
                (f_ev_tail_post in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)
                (APPEND
                  (ENUMERATEL (val len_bits DIV 128 MOD 4)
                    (\i. f_ev_tail_body in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress i))
                  (f_ev_tail_pre in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)))
           (APPEND
             (if val len_bits DIV 128 DIV 4 = 0 then
                f_ev_m0 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress
              else if val len_bits DIV 128 DIV 4 = 1 then
                f_ev_m1 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress
              else if val len_bits DIV 128 DIV 4 = 2 then
                f_ev_m2 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress
              else
                APPEND
                  (f_ev_drain in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)
                  (APPEND
                    (ENUMERATEL (val len_bits DIV 128 DIV 4 - 1)
                      (\i. f_ev_steady in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress i))
                    (f_ev_fill in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)))
             (f_ev_pro in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)))
      :(uarch_event) list` THEN

  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 224 THEN GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst EXEC] THEN
  ABBREV_TAC `nblocks     = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count  = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `loop_count < 2 EXP 64 /\ loop_remain < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "loop_count" THEN EXPAND_TAC "nblocks" THEN REWRITE_TAC[DIV_DIV] THEN
      TRANS_TAC LET_TRANS `len_bits:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      EXPAND_TAC "loop_remain" THEN TRANS_TAC LTE_TRANS `4` THEN
      SIMP_TAC[MOD_LT_EQ; ARITH_RULE `~(4 = 0)`] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count /\ val(word loop_remain:int64) = loop_remain`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  STRIP_TAC THEN

  (*** Epilogue split at pc+0x6fc.  The epilogue stores the tag (str q30,[x3]) and the counter    ***)
  (*** (str w14,[x4,#12]), so X3=tag_p and X4=ivec_p must be carried to prove those stores do not  ***)
  (*** hit code; X15 holds the value moved into x0 (mov x0,x15) but is not a store address.        ***)
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x6fc`
   `\s. read X3 s = tag_p /\ read X4 s = ivec_p /\ read SP s = stackpointer /\
        read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
  CONJ_TAC THENL
   [(*** REGION A: pc -> pc+0x6fc (prologue + pipelined body). ***)
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x61c`
     `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
          read X2 s = word_add out_p (word (64 * loop_count)) /\
          read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
          read SP s = stackpointer /\ read X16 s = word loop_remain /\
          read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
    CONJ_TAC THENL
     [(*** setup incl prologue: pc -> 0x88 = 11 prologue + 23 setup = 34 steps. ***)
      ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x88`
       `\s. read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
            read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
            read X1 s = word loop_count /\ read X16 s = word loop_remain /\
            read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
      CONJ_TAC THENL [SAFE_SIM (1--34) THEN CLOSE_SUB; ALL_TAC] THEN

      ASM_CASES_TAC `loop_count = 0` THENL
       [REDUCE_IF0 `loop_count:num` THEN SAFE_SIM (1--1) THEN CLOSE_SUB; ALL_TAC] THEN
      REDUCE_IFN0 `loop_count:num` THEN
      ASM_CASES_TAC `loop_count = 1` THENL
       [REDUCE_IFEQ `loop_count:num` `1` THEN SAFE_SIM (1--179) THEN CLOSE_SUB; ALL_TAC] THEN
      REDUCE_IFNE `loop_count:num` `1` THEN
      ASM_CASES_TAC `loop_count = 2` THENL
       [REDUCE_IFEQ `loop_count:num` `2` THEN SAFE_SIM (1--357) THEN CLOSE_SUB; ALL_TAC] THEN
      REDUCE_IFNE `loop_count:num` `2` THEN
      SUBGOAL_THEN `3 <= loop_count` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `loop_count - 1` `pc + 0x1ec` `pc + 0x4b4`
       `\i s. read X0 s = word_add in_p (word (64 * i)) /\
              read X2 s = word_add out_p (word (64 * i)) /\
              read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
              read SP s = stackpointer /\ read X16 s = word loop_remain /\
              read X1 s = word (loop_count - 1 - i) /\
              read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC;
        BEQ_NZ `1` THEN SAFE_SIM (1--89) THEN
        BEQ_NZ `2` THEN
        REPEAT CONJ_TAC THEN
        W(fun (asl,w) ->
          if is_exists w then (DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC)
          else if is_branch_goal w then (ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE)
          else if can dest_eq w &&
                  (let l,_ = dest_eq w in
                   can (find_term (fun t -> t = `word_sub (word loop_count:int64) (word 1)`)) l)
          then (REWRITE_TAC[SUB_0] THEN GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
                ASM_SIMP_TAC[ARITH_RULE `3 <= loop_count ==> 1 <= loop_count`])
          else (ADDR_RECON ORELSE MEM_PRESERVE));
        REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        SUBGOAL_THEN `loop_count - 1 < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        SAFE_SIM (1--178) THEN CLOSE_R2_SUB;
        SAFE_SIM (1--90) THEN REPEAT CONJ_TAC THEN
        W(fun (asl,w) ->
          if is_exists w then (DEABBR THEN DISCHARGE_SAFE_ROBUST)
          else (DRAIN_ADDR ORELSE MEM_PRESERVE))];

      ALL_TAC] THEN
    (*** TAIL region of the body: pc+0x61c -> pc+0x6fc. ***)
    ASM_CASES_TAC `loop_remain = 0` THENL
     [REDUCE_IF0 `loop_remain:num` THEN SAFE_SIM (1--4) THEN CLOSE_R2_SUB; ALL_TAC] THEN
    REDUCE_IFN0 `loop_remain:num` THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `loop_remain:num` `pc + 0x62c` `pc + 0x6fc`
     `\i s. read X0 s = word_add in_p (word (64 * loop_count + 16 * i)) /\
            read X2 s = word_add out_p (word (64 * loop_count + 16 * i)) /\
            read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
            read SP s = stackpointer /\ read X16 s = word (loop_remain - i) /\
            read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SAFE_SIM (1--4) THEN CLOSE_R2_SUB;
      ALL_TAC;
      REWRITE_TAC[] THEN SAFE_SIM [] THEN CLOSE_R2_SUB] THEN
    REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    SAFE_SIM (1--52) THEN CLOSE_R2_SUB;

    (*** REGION B: pc+0x6fc -> returnaddress (epilogue: mov x0,x15; rev64/str tag; rev/str ctr;   ***)
    (*** then 11 ldp; add sp; ret = 17 steps).                                                     ***)
    SAFE_SIM (1--17) THEN REPEAT CONJ_TAC THEN
    (MEM_PRESERVE ORELSE DISCHARGE_SAFETY_PROPERTY_TAC)] );;
