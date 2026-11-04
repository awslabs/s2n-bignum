(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-256-GCM decryption of whole blocks, 8 blocks at a time: the 8-way     *)
(* kernel aes256_gcm_dec_alt.                                                *)
(*                                                                           *)
(* Contract (AES256_GCM_DEC_ALT_SUBROUTINE_CORRECT).  The kernel processes   *)
(* nblk = gcm_wb_blocks len_bits whole 16-byte blocks (none when len_bits is *)
(* not a multiple of 128) and returns 16 * nblk.  Given the FIPS-197 key     *)
(* schedule rk at key_p, the key table htable_mem_8 at htable_p for the      *)
(* GHASH key                                                                 *)
(*   H = aes256_cipher (word 0) rk                                           *)
(* and the counter block ctr_block nonce c at ivec_p, output block j is      *)
(* input block j XOR aes_ctr_block aes256_cipher c nonce rk j, the tag at    *)
(* tag_p becomes nist_ghash H over the input (ciphertext) blocks, continued  *)
(* from the old tag, and ivec_p advances to ctr_block nonce (nblk + c); the  *)
(* tag and the counter block are stored byte-reversed.  The buffers must be  *)
(* disjoint, and val in_p + 16 * nblk < 2 EXP 63 since the kernel compares   *)
(* pointers with signed conditions.  AES256_GCM_DEC_ALT_SUBROUTINE_SAFE is   *)
(* the matching constant-time and memory-safety theorem.                     *)
(*                                                                           *)
(* The code begins with a bti c landing pad.  The proofs are about the code  *)
(* without it, the code of a -DNO_IBT build, so every offset in this file    *)
(* (pc + 0x1c, 0x4bc, ...) is one of that code; the theorems for the full    *)
(* code follow by ARM_ADD_IBT_RULE.                                          *)
(*                                                                           *)
(* Proof structure.  The entry guard (0x0..0x8) returns 0 for an empty or    *)
(* invalid len_bits, and the prologue (0xc..0x18) saves d8-d15.  The core    *)
(* runs from pc + 0x1c to its exit pc + 4508 (0x119c,                        *)
(* L256_dec_frame_restore); its theorem is the spine WBN_DEC_CORE_BYTELIST,  *)
(* which splits on nblk:                                                     *)
(* - nblk <= 8, the <=8-block chain (AES256_GCM_DEC_ALT_DISPATCH): for       *)
(*   nblk <= 4 the b.le at 0x38 enters the small-input path L256_dec_small   *)
(*   (WB_FUSED_1BLOCK .. WB_FUSED_4BLOCK); for 5..8 the shared front         *)
(*   (WB_FRONT_BUF) takes the b.ge at 0x448, and the tail runs from the seam *)
(*   pc + 3824 (0xef0) through the block cascade, or the exact-8 drain for   *)
(*   nblk = 8 (WB_TAIL_GEN2_k);                                              *)
(* - 9 <= nblk <= 16: the front falls through at 0x448 and takes the b.ge at *)
(*   0x4b8 to the prepretail at 0xa0c, skipping the main loop                *)
(*   (WBN_FRONT_TO_END_916);                                                 *)
(* - nblk >= 17: the front reaches the loop head 0x4bc, the main loop        *)
(*   L256_dec_main_loop (0x4bc..0xa08, 8 blocks per iteration, run           *)
(*   (nblk - 9) DIV 8 times) is an ENSURES_WHILE loop (WBN_MAIN_LOOP_raw),   *)
(*   and the prepretail brings the state to the tail seam, where the same    *)
(*   tail runs on the last 1..8 blocks (WBN_FRONT_TO_END).                   *)
(* GHASH lags the stores by one 8-block group, so the loop invariant has two *)
(* streams: stores and counters are at block 8 (i + 1), the GHASH            *)
(* accumulator covers blocks 0 .. 8 i - 1, and q8..q15 hold the raw          *)
(* ciphertext blocks 8 i .. 8 i + 7 in between.                              *)
(*                                                                           *)
(* The internal theorems state the input and output as byte lists, over the  *)
(* round keys as they sit in memory, an opaque initial counter block and a   *)
(* free GHASH key.  The spines WBN_DEC_CORE_BYTELIST and                     *)
(* WBN_DEC_SUBROUTINE_BYTELIST (the ABI wrapper) carry the simulation proof, *)
(* and the exported theorems are derived from them without re-simulation, in *)
(* the shared AES-GCM vocabulary of arm/proofs/utils/aes_gcm_spec.ml         *)
(* (ctr_block, aes_ctr_block, nist_ghash, nist_input_block, htable_mem_8,    *)
(* ghash_twist, gcm_wb_blocks).                                              *)
(*                                                                           *)
(* The part of the proof that does not depend on the key size or the machine *)
(* code (GHASH/Karatsuba bridge, SIMD-fold steppers, counter core, byte-list *)
(* lemmas, decrypt specification, shared tactics) is in                      *)
(* arm/proofs/utils/aes_gcm_dec_alt_common.ml, shared with the AES-128       *)
(* proof.  This file holds, in order: the CTR specification over             *)
(* aes256_encrypt; the machine code; the <=8-block chain (band tails, shared *)
(* front, small-input path, readable band and dispatch theorems); the nblk > *)
(* 8 proof in sections 1 to 12 (section 2, the symbolic counter layer, comes *)
(* earlier, with the band tails that use it); the spines and the exported    *)
(* theorems; the constant-time and memory-safety proof; the no-access        *)
(* theorems for rejected lengths.                                            *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/aes_gcm_dec_alt_common.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(* ========================================================================= *)
(* The AES-256 counter-mode (CTR) output over int128 block lists.            *)
(*                                                                           *)
(* CTR is symmetric: the same specification serves encryption and            *)
(* decryption, since both compute                                            *)
(*   word_xor x (aes256_encrypt (gcm_ctr_inc_iter k ctr0) keys).             *)
(*                                                                           *)
(* Design:                                                                   *)
(* - each int128 element represents one 16-byte block;                       *)
(* - byte-list adapters appear only where the memory readback needs them;    *)
(* - block k uses gcm_ctr_inc_iter k ctr0, so the recursion composes and an  *)
(*   N-block induction advances k to k+1.                                    *)
(* ========================================================================= *)

(* The AES-XTS byte-list substrate: byte_list_at, bytes_to_int128,           *)
(* int128_to_bytes and the shared readback machinery.                        *)

(* One CTR output block: data XOR the AES-256 keystream for block index k.   *)
(* This four-argument definition applies CTR to a plaintext/ciphertext block *)
(* indexed by raw ctr0/k rather than by a NIST nonce/counter pair.           *)
let aes_ctr_output_block = new_definition
 `aes_ctr_output_block (ctr0:int128) (k:num) (pt:int128) (keys:int128 list) : int128 =
    word_xor pt (aes256_encrypt (gcm_ctr_inc_iter k ctr0) keys)`;;

(* Recursive CTR over a block list. Position i uses counter                  *)
(* gcm_ctr_inc_iter (k+i) ctr0, where k is the starting block index.         *)
(* This is plain structural recursion, with no well-founded measure needed.  *)
let aes_ctr_rec = define
 `aes_ctr_rec (ctr0:int128) (k:num) ([]:int128 list) (keys:int128 list) = [] /\
  aes_ctr_rec (ctr0:int128) (k:num) (CONS pt pts) (keys:int128 list) =
    CONS (aes_ctr_output_block ctr0 k pt keys)
         (aes_ctr_rec ctr0 (k+1) pts keys)`;;

(* Top spec: CTR-encrypt the whole block list starting at block 0.           *)
let aes_ctr = new_definition
 `aes_ctr (ctr0:int128) (pts:int128 list) (keys:int128 list) : int128 list =
    aes_ctr_rec ctr0 0 pts keys`;;

(* LENGTH is preserved (so a bytes(out_p,16*N) framing matches).             *)
let LENGTH_AES_CTR_REC = prove
 (`!pts ctr0 k keys. LENGTH(aes_ctr_rec ctr0 k pts keys) = LENGTH pts`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[aes_ctr_rec; LENGTH]);;

let LENGTH_AES_CTR = prove
 (`!pts ctr0 keys. LENGTH(aes_ctr ctr0 pts keys) = LENGTH pts`,
  REWRITE_TAC[aes_ctr; LENGTH_AES_CTR_REC]);;

(* Element i of the recursive ciphertext, for any N.                         *)
let EL_AES_CTR_REC = prove
 (`!pts ctr0 k keys i.
     i < LENGTH pts
     ==> EL i (aes_ctr_rec ctr0 k pts keys) =
         aes_ctr_output_block ctr0 (k+i) (EL i pts) keys`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; aes_ctr_rec; LT] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  ASM_REWRITE_TAC[EL; HD; TL; ADD_CLAUSES; LT_SUC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < LENGTH(t:int128 list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ctr0:int128`;`k+1`;`keys:int128 list`;`n:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `(k+1)+n = SUC(k+n)`]);;

(* Element i of the top spec, in the explicit word_xor / aes256_encrypt form *)
(* a binary postcondition's per-block store readback carries.                *)
let EL_AES_CTR = prove
 (`!pts ctr0 keys i.
     i < LENGTH pts
     ==> EL i (aes_ctr ctr0 pts keys) =
         word_xor (EL i pts) (aes256_encrypt (gcm_ctr_inc_iter i ctr0) keys)`,
  REWRITE_TAC[aes_ctr] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_AES_CTR_REC; aes_ctr_output_block; ADD_CLAUSES]);;

(* The aes_ctr output as a byte list (int128_list_to_bytes above).           *)
let aes_ctr_bytes = new_definition
 `aes_ctr_bytes (ctr0:int128) (pts:int128 list) (keys:int128 list) : byte list =
    int128_list_to_bytes (aes_ctr ctr0 pts keys)`;;

(* Targeted lane closer: fold only the 64-bit lane-subword equations (whose  *)
(* right-hand side is a qqNl/qqNh variable), not the pmul atom definitions   *)
(* (which would re-expand the qq atoms), then a flat 64-bit WORD_RULE        *)
(* (XOR-ACI over the named lanes).                                           *)
let LANE_CLOSE_TAC : tactic = fun (asl,w) ->
  let is_lane_def (_,th) =
    let c = concl th in is_eq c &&
    (try let r = rhs c in is_var r &&
       (let n = fst(dest_var r) in String.length n>=3 && String.sub n 0 2="qq" &&
        (let last = n.[String.length n-1] in last='l' || last='h'))
     with _ -> false) &&
    (try let l = lhs c in is_comb l && fst(dest_const(rator(rator l)))="word_subword" with _ -> false) in
  let lane_ths = map snd (filter is_lane_def asl) in
  (REWRITE_TAC lane_ths THEN CONV_TAC WORD_RULE) (asl,w);;

(* ========================================================================= *)
(* Decrypt-specific lemmas and tactics.                                      *)
(*                                                                           *)
(* Everything below is keyed to the decrypt dataflow: GHASH reads the raw    *)
(* loaded ciphertext blocks cph_i, the last block included (no block is      *)
(* masked).  In the encrypt kernels GHASH reads the computed ciphertext, so  *)
(* these lemmas and tactics do not transfer.                                 *)
(* ========================================================================= *)

(* XOR-commutativity helper for the wal lane (the two byteforms present the  *)
(* wa-round lane sum in opposite operand order).                             *)
let DEC2_WXSYM = WORD_RULE `word_xor qq6l qq1l = word_xor qq1l qq6l`;;

(* ----------------------------------------------------------------------------
   Output plaintext byte buffer (decrypt): counter mode over the same whole
   input blocks (aes_ctr XORs the keystream onto the ciphertext, recovering
   the plaintext).
   ------------------------------------------------------------------------- *)
let gcm_dec_pt_bytes = new_definition
 `gcm_dec_pt_bytes (len:num) (x:byte list) (ctr0:int128) (keys:int128 list) : byte list =
    aes_ctr_bytes ctr0 (gcm_dec_blocks_from 0 (len DIV 16) x) keys`;;

let build_pt_bytes_whole n =
  prove(list_mk_forall([`x:byte list`; `ctr0:int128`; `keys:int128 list`],
          mk_eq(list_mk_comb(`gcm_dec_pt_bytes`,
                  [mk_small_numeral (16 * n); `x:byte list`; `ctr0:int128`;
                   `keys:int128 list`]),
                list_mk_comb(`aes_ctr_bytes`,
                  [`ctr0:int128`; gcm_dec_whole_blocks_tm n;
                   `keys:int128 list`]))),
        REPEAT GEN_TAC THEN REWRITE_TAC[gcm_dec_pt_bytes] THEN
        GCM_DEC_BLOCKS_FROM_UNFOLD_TAC n);;

let GCM_DEC_PT_BYTES_WHOLE_1 = build_pt_bytes_whole 1;;
let GCM_DEC_PT_BYTES_WHOLE_2 = build_pt_bytes_whole 2;;
let GCM_DEC_PT_BYTES_WHOLE_3 = build_pt_bytes_whole 3;;
let GCM_DEC_PT_BYTES_WHOLE_4 = build_pt_bytes_whole 4;;
let GCM_DEC_PT_BYTES_WHOLE_5 = build_pt_bytes_whole 5;;
let GCM_DEC_PT_BYTES_WHOLE_6 = build_pt_bytes_whole 6;;
let GCM_DEC_PT_BYTES_WHOLE_7 = build_pt_bytes_whole 7;;
let GCM_DEC_PT_BYTES_WHOLE_8 = build_pt_bytes_whole 8;;

(* ------------------------------------------------------------------------- *)
(* Machine code (print_literal_from_elf "arm/aes_gcm/aes256_gcm_dec_alt.o")  *)
(* ------------------------------------------------------------------------- *)

let aes256_gcm_dec_alt_mc = define_assert_from_elf "aes256_gcm_dec_alt_mc"
  "arm/aes_gcm/aes256_gcm_dec_alt.o"
[
  0xd503245f;       (* arm_BTI *)
  0xb400b861;       (* arm_CBZ X1 (word 5900) *)
  0xf240183f;       (* arm_TST X1 (rvalue (word 127)) *)
  0x5400b821;       (* arm_BNE (word 5892) *)
  0x6dbb27e8;       (* arm_STP D8 D9 SP (Preimmediate_Offset (iword (-- &80))) *)
  0x6d012fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d0237ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d033fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0xd343fc29;       (* arm_LSR X9 X1 3 *)
  0xaa0403f0;       (* arm_MOV X16 X4 *)
  0xaa0503eb;       (* arm_MOV X11 X5 *)
  0xd2f84005;       (* arm_MOVZ X5 (word 49664) 48 *)
  0xa9047fe5;       (* arm_STP X5 XZR SP (Immediate_Offset (iword (&64))) *)
  0x910103ea;       (* arm_ADD X10 SP (rvalue (word 64)) *)
  0xf101013f;       (* arm_CMP X9 (rvalue (word 64)) *)
  0x540097ed;       (* arm_BLE (word 4860) *)
  0x4c407200;       (* arm_LDR Q0 X16 No_Offset *)
  0xd2c0002f;       (* arm_MOVZ X15 (word 1) 32 *)
  0x4f00e41f;       (* arm_MOVI Q31 (word 0) *)
  0x4e181dff;       (* arm_INS_GEN Q31 X15 64 64 *)
  0x4ebf87fc;       (* arm_ADD_VEC Q28 Q31 Q31 32 128 *)
  0x4ebf878a;       (* arm_ADD_VEC Q10 Q28 Q31 32 128 *)
  0x4ebc878b;       (* arm_ADD_VEC Q11 Q28 Q28 32 128 *)
  0x4ebf856c;       (* arm_ADD_VEC Q12 Q11 Q31 32 128 *)
  0x4ebc856d;       (* arm_ADD_VEC Q13 Q11 Q28 32 128 *)
  0x4eaa856e;       (* arm_ADD_VEC Q14 Q11 Q10 32 128 *)
  0xaa0903e5;       (* arm_MOV X5 X9 *)
  0xd10004a5;       (* arm_SUB X5 X5 (rvalue (word 1)) *)
  0x6e20081d;       (* arm_REV32_VEC Q29 Q0 8 *)
  0x4ebf87a8;       (* arm_ADD_VEC Q8 Q29 Q31 32 128 *)
  0x4ebc87a9;       (* arm_ADD_VEC Q9 Q29 Q28 32 128 *)
  0x4eaa87af;       (* arm_ADD_VEC Q15 Q29 Q10 32 128 *)
  0x4eab87b0;       (* arm_ADD_VEC Q16 Q29 Q11 32 128 *)
  0x4eac87b1;       (* arm_ADD_VEC Q17 Q29 Q12 32 128 *)
  0x4ead87b2;       (* arm_ADD_VEC Q18 Q29 Q13 32 128 *)
  0x4eae87be;       (* arm_ADD_VEC Q30 Q29 Q14 32 128 *)
  0x6e200901;       (* arm_REV32_VEC Q1 Q8 8 *)
  0x6e200922;       (* arm_REV32_VEC Q2 Q9 8 *)
  0x6e2009e3;       (* arm_REV32_VEC Q3 Q15 8 *)
  0x6e200a04;       (* arm_REV32_VEC Q4 Q16 8 *)
  0x6e200a25;       (* arm_REV32_VEC Q5 Q17 8 *)
  0x6e200a46;       (* arm_REV32_VEC Q6 Q18 8 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x9279e0a5;       (* arm_AND X5 X5 (rvalue (word 18446744073709551488)) *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4c407073;       (* arm_LDR Q19 X3 No_Offset *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x8b410c04;       (* arm_ADD X4 X0 (Shiftedreg X1 LSR 3) *)
  0x8b0000a5;       (* arm_ADD X5 X5 X0 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x540054aa;       (* arm_BGE (word 2708) *)
  0xacc12408;       (* arm_LDP Q8 Q9 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc12c0a;       (* arm_LDP Q10 Q11 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc1340c;       (* arm_LDP Q12 Q13 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc13c0e;       (* arm_LDP Q14 Q15 X0 (Postimmediate_Offset (iword (&32))) *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0xce017121;       (* arm_EOR3 Q1 Q9 Q1 Q28 *)
  0xce007100;       (* arm_EOR3 Q0 Q8 Q0 Q28 *)
  0xac810440;       (* arm_STP Q0 Q1 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc0;       (* arm_REV32_VEC Q0 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce037163;       (* arm_EOR3 Q3 Q11 Q3 Q28 *)
  0xce0571a5;       (* arm_EOR3 Q5 Q13 Q5 Q28 *)
  0xce047184;       (* arm_EOR3 Q4 Q12 Q4 Q28 *)
  0x6e200bc1;       (* arm_REV32_VEC Q1 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce027142;       (* arm_EOR3 Q2 Q10 Q2 Q28 *)
  0xac810c42;       (* arm_STP Q2 Q3 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc2;       (* arm_REV32_VEC Q2 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce0671c6;       (* arm_EOR3 Q6 Q14 Q6 Q28 *)
  0x6e200bc3;       (* arm_REV32_VEC Q3 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xac811444;       (* arm_STP Q4 Q5 X2 (Postimmediate_Offset (iword (&32))) *)
  0xce0771e7;       (* arm_EOR3 Q7 Q15 Q7 Q28 *)
  0xac811c46;       (* arm_STP Q6 Q7 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x54002aaa;       (* arm_BGE (word 1364) *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e200929;       (* arm_REV64_VEC Q9 Q9 8 *)
  0x3dc024d7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 144)) *)
  0x3dc02cd9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 176)) *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e200908;       (* arm_REV64_VEC Q8 Q8 8 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e20098c;       (* arm_REV64_VEC Q12 Q12 8 *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 *)
  0x4e2009ef;       (* arm_REV64_VEC Q15 Q15 8 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x6e331d08;       (* arm_EOR_VEC Q8 Q8 Q19 128 *)
  0x3dc018d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 96)) *)
  0x3dc020d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 128)) *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e20094a;       (* arm_REV64_VEC Q10 Q10 8 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4ec82932;       (* arm_TRN1 Q18 Q9 Q8 64 128 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4ef6e15d;       (* arm_PMULL2_VEC Q29 Q10 Q22 64 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ef7e130;       (* arm_PMULL2_VEC Q16 Q9 Q23 64 *)
  0x0ef7e137;       (* arm_PMULL_VEC Q23 Q9 Q23 64 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ec86928;       (* arm_TRN2 Q8 Q9 Q8 64 128 *)
  0x4ef4e169;       (* arm_PMULL2_VEC Q9 Q11 Q20 64 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e301e31;       (* arm_EOR_VEC Q17 Q17 Q16 128 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3dc01cd5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 112)) *)
  0x3dc028d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 160)) *)
  0x6e321d08;       (* arm_EOR_VEC Q8 Q8 Q18 128 *)
  0x0ef6e156;       (* arm_PMULL_VEC Q22 Q10 Q22 64 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0xce1d2631;       (* arm_EOR3 Q17 Q17 Q29 Q9 *)
  0x4eca297d;       (* arm_TRN1 Q29 Q11 Q10 64 128 *)
  0x4e2009ad;       (* arm_REV64_VEC Q13 Q13 8 *)
  0x4ef8e112;       (* arm_PMULL2_VEC Q18 Q8 Q24 64 *)
  0x0ef8e118;       (* arm_PMULL_VEC Q24 Q8 Q24 64 *)
  0x4eca696a;       (* arm_TRN2 Q10 Q11 Q10 64 128 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ecc29b0;       (* arm_TRN1 Q16 Q13 Q12 64 128 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x6e3d1d4a;       (* arm_EOR_VEC Q10 Q10 Q29 128 *)
  0x0ef4e174;       (* arm_PMULL_VEC Q20 Q11 Q20 64 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4ef5e15d;       (* arm_PMULL2_VEC Q29 Q10 Q21 64 *)
  0x0ef5e155;       (* arm_PMULL_VEC Q21 Q10 Q21 64 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e2009ce;       (* arm_REV64_VEC Q14 Q14 8 *)
  0x6e381e52;       (* arm_EOR_VEC Q18 Q18 Q24 128 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0xce157652;       (* arm_EOR3 Q18 Q18 Q21 Q29 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ef9e188;       (* arm_PMULL2_VEC Q8 Q12 Q25 64 *)
  0x0ef9e199;       (* arm_PMULL_VEC Q25 Q12 Q25 64 *)
  0x4ecc69ac;       (* arm_TRN2 Q12 Q13 Q12 64 128 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ef7e1aa;       (* arm_PMULL2_VEC Q10 Q13 Q23 64 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x0ef7e1b7;       (* arm_PMULL_VEC Q23 Q13 Q23 64 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ef6e1cb;       (* arm_PMULL2_VEC Q11 Q14 Q22 64 *)
  0x4ece29ed;       (* arm_TRN1 Q13 Q15 Q14 64 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x0ef6e1d6;       (* arm_PMULL_VEC Q22 Q14 Q22 64 *)
  0x4ece69ee;       (* arm_TRN2 Q14 Q15 Q14 64 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce082a31;       (* arm_EOR3 Q17 Q17 Q8 Q10 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x6e2d1dce;       (* arm_EOR_VEC Q14 Q14 Q13 128 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xacc12408;       (* arm_LDP Q8 Q9 X0 (Postimmediate_Offset (iword (&32))) *)
  0x6e301d8c;       (* arm_EOR_VEC Q12 Q12 Q16 128 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4ef5e1cd;       (* arm_PMULL2_VEC Q13 Q14 Q21 64 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef8e190;       (* arm_PMULL2_VEC Q16 Q12 Q24 64 *)
  0x0ef8e198;       (* arm_PMULL_VEC Q24 Q12 Q24 64 *)
  0x4ef4e1ec;       (* arm_PMULL2_VEC Q12 Q15 Q20 64 *)
  0x0ef4e1f4;       (* arm_PMULL_VEC Q20 Q15 Q20 64 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x0ef5e1d5;       (* arm_PMULL_VEC Q21 Q14 Q21 64 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xce195e73;       (* arm_EOR3 Q19 Q19 Q25 Q23 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xce184252;       (* arm_EOR3 Q18 Q18 Q24 Q16 *)
  0xce0b3231;       (* arm_EOR3 Q17 Q17 Q11 Q12 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x6e200bd4;       (* arm_REV32_VEC Q20 Q30 8 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0xce153652;       (* arm_EOR3 Q18 Q18 Q21 Q13 *)
  0x6e200bd6;       (* arm_REV32_VEC Q22 Q30 8 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xacc12c0a;       (* arm_LDP Q10 Q11 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x6e200bd7;       (* arm_REV32_VEC Q23 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x0ef0e23d;       (* arm_PMULL_VEC Q29 Q17 Q16 64 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xacc1340c;       (* arm_LDP Q12 Q13 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0xacc13c0e;       (* arm_LDP Q14 Q15 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x6e200bd9;       (* arm_REV32_VEC Q25 Q30 8 *)
  0xce027142;       (* arm_EOR3 Q2 Q10 Q2 Q28 *)
  0xce017121;       (* arm_EOR3 Q1 Q9 Q1 Q28 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0xce0571a5;       (* arm_EOR3 Q5 Q13 Q5 Q28 *)
  0xce007100;       (* arm_EOR3 Q0 Q8 Q0 Q28 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0xac810440;       (* arm_STP Q0 Q1 X2 (Postimmediate_Offset (iword (&32))) *)
  0x4eb41e80;       (* arm_MOV_VEC Q0 Q20 128 *)
  0xce047184;       (* arm_EOR3 Q4 Q12 Q4 Q28 *)
  0xce154673;       (* arm_EOR3 Q19 Q19 Q21 Q17 *)
  0xce037163;       (* arm_EOR3 Q3 Q11 Q3 Q28 *)
  0xac810c42;       (* arm_STP Q2 Q3 X2 (Postimmediate_Offset (iword (&32))) *)
  0x4eb91f23;       (* arm_MOV_VEC Q3 Q25 128 *)
  0x4eb71ee2;       (* arm_MOV_VEC Q2 Q23 128 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4eb61ec1;       (* arm_MOV_VEC Q1 Q22 128 *)
  0xac811444;       (* arm_STP Q4 Q5 X2 (Postimmediate_Offset (iword (&32))) *)
  0xce0771e7;       (* arm_EOR3 Q7 Q15 Q7 Q28 *)
  0xce0671c6;       (* arm_EOR3 Q6 Q14 Q6 Q28 *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0xac811c46;       (* arm_STP Q6 Q7 X2 (Postimmediate_Offset (iword (&32))) *)
  0x54ffd5ab;       (* arm_BLT (word 2095796) *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e20098c;       (* arm_REV64_VEC Q12 Q12 8 *)
  0x3dc01cd5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 112)) *)
  0x3dc028d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 160)) *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 *)
  0x4e200908;       (* arm_REV64_VEC Q8 Q8 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x3dc024d7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 144)) *)
  0x3dc02cd9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 176)) *)
  0x4e200929;       (* arm_REV64_VEC Q9 Q9 8 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 *)
  0x4e20094a;       (* arm_REV64_VEC Q10 Q10 8 *)
  0x3dc018d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 96)) *)
  0x3dc020d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 128)) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e331d08;       (* arm_EOR_VEC Q8 Q8 Q19 128 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ef7e130;       (* arm_PMULL2_VEC Q16 Q9 Q23 64 *)
  0x4ec82932;       (* arm_TRN1 Q18 Q9 Q8 64 128 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0x0ef7e137;       (* arm_PMULL_VEC Q23 Q9 Q23 64 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e2009ce;       (* arm_REV64_VEC Q14 Q14 8 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ef6e15d;       (* arm_PMULL2_VEC Q29 Q10 Q22 64 *)
  0x4ec86928;       (* arm_TRN2 Q8 Q9 Q8 64 128 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef4e169;       (* arm_PMULL2_VEC Q9 Q11 Q20 64 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e301e31;       (* arm_EOR_VEC Q17 Q17 Q16 128 *)
  0x6e321d08;       (* arm_EOR_VEC Q8 Q8 Q18 128 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x0ef6e156;       (* arm_PMULL_VEC Q22 Q10 Q22 64 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xce1d2631;       (* arm_EOR3 Q17 Q17 Q29 Q9 *)
  0x4eca297d;       (* arm_TRN1 Q29 Q11 Q10 64 128 *)
  0x4eca696a;       (* arm_TRN2 Q10 Q11 Q10 64 128 *)
  0x4ef8e112;       (* arm_PMULL2_VEC Q18 Q8 Q24 64 *)
  0x0ef4e174;       (* arm_PMULL_VEC Q20 Q11 Q20 64 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x0ef8e118;       (* arm_PMULL_VEC Q24 Q8 Q24 64 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x6e381e52;       (* arm_EOR_VEC Q18 Q18 Q24 128 *)
  0x6e3d1d4a;       (* arm_EOR_VEC Q10 Q10 Q29 128 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef5e15d;       (* arm_PMULL2_VEC Q29 Q10 Q21 64 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x0ef5e155;       (* arm_PMULL_VEC Q21 Q10 Q21 64 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e2009ef;       (* arm_REV64_VEC Q15 Q15 8 *)
  0x4e2009ad;       (* arm_REV64_VEC Q13 Q13 8 *)
  0xce157652;       (* arm_EOR3 Q18 Q18 Q21 Q29 *)
  0x4ecc29b0;       (* arm_TRN1 Q16 Q13 Q12 64 128 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4ef9e188;       (* arm_PMULL2_VEC Q8 Q12 Q25 64 *)
  0x4ef7e1aa;       (* arm_PMULL2_VEC Q10 Q13 Q23 64 *)
  0x0ef9e199;       (* arm_PMULL_VEC Q25 Q12 Q25 64 *)
  0x4ecc69ac;       (* arm_TRN2 Q12 Q13 Q12 64 128 *)
  0x0ef7e1b7;       (* arm_PMULL_VEC Q23 Q13 Q23 64 *)
  0x4ece29ed;       (* arm_TRN1 Q13 Q15 Q14 64 128 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4ef6e1cb;       (* arm_PMULL2_VEC Q11 Q14 Q22 64 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x0ef6e1d6;       (* arm_PMULL_VEC Q22 Q14 Q22 64 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xce082a31;       (* arm_EOR3 Q17 Q17 Q8 Q10 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ece69ee;       (* arm_TRN2 Q14 Q15 Q14 64 128 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e301d8c;       (* arm_EOR_VEC Q12 Q12 Q16 128 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x6e2d1dce;       (* arm_EOR_VEC Q14 Q14 Q13 128 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4ef8e190;       (* arm_PMULL2_VEC Q16 Q12 Q24 64 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x0ef8e198;       (* arm_PMULL_VEC Q24 Q12 Q24 64 *)
  0x4ef4e1ec;       (* arm_PMULL2_VEC Q12 Q15 Q20 64 *)
  0x4ef5e1cd;       (* arm_PMULL2_VEC Q13 Q14 Q21 64 *)
  0x0ef5e1d5;       (* arm_PMULL_VEC Q21 Q14 Q21 64 *)
  0x0ef4e1f4;       (* arm_PMULL_VEC Q20 Q15 Q20 64 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0xce195e73;       (* arm_EOR3 Q19 Q19 Q25 Q23 *)
  0xce184252;       (* arm_EOR3 Q18 Q18 Q24 Q16 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xce0b3231;       (* arm_EOR3 Q17 Q17 Q11 Q12 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0xce153652;       (* arm_EOR3 Q18 Q18 Q21 Q13 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x0ef0e23d;       (* arm_PMULL_VEC Q29 Q17 Q16 64 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0xce154673;       (* arm_EOR3 Q19 Q19 Q21 Q17 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x6e134270;       (* arm_EXT Q16 Q19 Q19 64 *)
  0xcb000085;       (* arm_SUB X5 X4 X0 *)
  0xf101c0bf;       (* arm_CMP X5 (rvalue (word 112)) *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0xad4564d8;       (* arm_LDP Q24 Q25 X6 (Immediate_Offset (iword (&160))) *)
  0x4ebc1f9d;       (* arm_MOV_VEC Q29 Q28 128 *)
  0xad4354d4;       (* arm_LDP Q20 Q21 X6 (Immediate_Offset (iword (&96))) *)
  0xce00752c;       (* arm_EOR3 Q12 Q9 Q0 Q29 *)
  0xad445cd6;       (* arm_LDP Q22 Q23 X6 (Immediate_Offset (iword (&128))) *)
  0x540015ac;       (* arm_BGT (word 692) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea31c64;       (* arm_MOV_VEC Q4 Q3 128 *)
  0x0f00e413;       (* arm_MOVI D19 (word 0) *)
  0x0f00e411;       (* arm_MOVI D17 (word 0) *)
  0x0f00e412;       (* arm_MOVI D18 (word 0) *)
  0x4ea21c43;       (* arm_MOV_VEC Q3 Q2 128 *)
  0xf10180bf;       (* arm_CMP X5 (rvalue (word 96)) *)
  0x4ea11c22;       (* arm_MOV_VEC Q2 Q1 128 *)
  0x5400046c;       (* arm_BGT (word 140) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0xf10140bf;       (* arm_CMP X5 (rvalue (word 80)) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea31c64;       (* arm_MOV_VEC Q4 Q3 128 *)
  0x4ea11c23;       (* arm_MOV_VEC Q3 Q1 128 *)
  0x5400052c;       (* arm_BGT (word 164) *)
  0xf10100bf;       (* arm_CMP X5 (rvalue (word 64)) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea11c24;       (* arm_MOV_VEC Q4 Q1 128 *)
  0x5400062c;       (* arm_BGT (word 196) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0xf100c0bf;       (* arm_CMP X5 (rvalue (word 48)) *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea11c25;       (* arm_MOV_VEC Q5 Q1 128 *)
  0x5400072c;       (* arm_BGT (word 228) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0xf10080bf;       (* arm_CMP X5 (rvalue (word 32)) *)
  0x4ea11c26;       (* arm_MOV_VEC Q6 Q1 128 *)
  0x5400088c;       (* arm_BGT (word 272) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea11c27;       (* arm_MOV_VEC Q7 Q1 128 *)
  0xf10040bf;       (* arm_CMP X5 (rvalue (word 16)) *)
  0x540009ec;       (* arm_BGT (word 316) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x1400005d;       (* arm_B (word 372) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x4ef7e11c;       (* arm_PMULL2_VEC Q28 Q8 Q23 64 *)
  0x0ef7e11a;       (* arm_PMULL_VEC Q26 Q8 Q23 64 *)
  0xce02752c;       (* arm_EOR3 Q12 Q9 Q2 Q29 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef8e37b;       (* arm_PMULL_VEC Q27 Q27 Q24 64 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x6e1542aa;       (* arm_EXT Q10 Q21 Q21 64 *)
  0x0eeae37b;       (* arm_PMULL_VEC Q27 Q27 Q10 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0xce03752c;       (* arm_EOR3 Q12 Q9 Q3 Q29 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x0ef5e37b;       (* arm_PMULL_VEC Q27 Q27 Q21 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0xce04752c;       (* arm_EOR3 Q12 Q9 Q4 Q29 *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0xce05752c;       (* arm_EOR3 Q12 Q9 Q5 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e18430b;       (* arm_EXT Q11 Q24 Q24 64 *)
  0x0ef9e11a;       (* arm_PMULL_VEC Q26 Q8 Q25 64 *)
  0x4ef9e11c;       (* arm_PMULL2_VEC Q28 Q8 Q25 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x0eebe37b;       (* arm_PMULL_VEC Q27 Q27 Q11 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x0ef7e11a;       (* arm_PMULL_VEC Q26 Q8 Q23 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0xce06752c;       (* arm_EOR3 Q12 Q9 Q6 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x0ef8e37b;       (* arm_PMULL_VEC Q27 Q27 Q24 64 *)
  0x4ef7e11c;       (* arm_PMULL2_VEC Q28 Q8 Q23 64 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x6e1542aa;       (* arm_EXT Q10 Q21 Q21 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0xce07752c;       (* arm_EOR3 Q12 Q9 Q7 Q29 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0x0eeae37b;       (* arm_PMULL_VEC Q27 Q27 Q10 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e200bde;       (* arm_REV32_VEC Q30 Q30 8 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e084110;       (* arm_EXT Q16 Q8 Q8 64 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0x2e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 64 *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x0ef5e210;       (* arm_PMULL_VEC Q16 Q16 Q21 64 *)
  0x6e301e52;       (* arm_EOR_VEC Q18 Q18 Q16 128 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x0ef0e235;       (* arm_PMULL_VEC Q21 Q17 Q16 64 *)
  0x6e331e2e;       (* arm_EOR_VEC Q14 Q17 Q19 128 *)
  0x6e114231;       (* arm_EXT Q17 Q17 Q17 64 *)
  0x4c00704c;       (* arm_STR Q12 X2 No_Offset *)
  0x6e2e1e52;       (* arm_EOR_VEC Q18 Q18 Q14 128 *)
  0x6e351e35;       (* arm_EOR_VEC Q21 Q17 Q21 128 *)
  0x6e351e52;       (* arm_EOR_VEC Q18 Q18 Q21 128 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x6e124252;       (* arm_EXT Q18 Q18 Q18 64 *)
  0x6e311e73;       (* arm_EOR_VEC Q19 Q19 Q17 128 *)
  0x6e321e73;       (* arm_EOR_VEC Q19 Q19 Q18 128 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0x4c007073;       (* arm_STR Q19 X3 No_Offset *)
  0xaa0903e0;       (* arm_MOV X0 X9 *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x6cc527e8;       (* arm_LDP D8 D9 SP (Postimmediate_Offset (iword (&80))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x6e184312;       (* arm_EXT Q18 Q24 Q24 64 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0xce01752c;       (* arm_EOR3 Q12 Q9 Q1 Q29 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x0ef2e372;       (* arm_PMULL_VEC Q18 Q27 Q18 64 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x4ef7e10d;       (* arm_PMULL2_VEC Q13 Q8 Q23 64 *)
  0x0ef7e10e;       (* arm_PMULL_VEC Q14 Q8 Q23 64 *)
  0xce02752c;       (* arm_EOR3 Q12 Q9 Q2 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef8e36f;       (* arm_PMULL_VEC Q15 Q27 Q24 64 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x6e1542aa;       (* arm_EXT Q10 Q21 Q21 64 *)
  0x0eeae37b;       (* arm_PMULL_VEC Q27 Q27 Q10 64 *)
  0xce1c3631;       (* arm_EOR3 Q17 Q17 Q28 Q13 *)
  0xce03752c;       (* arm_EOR3 Q12 Q9 Q3 Q29 *)
  0xce1a3a73;       (* arm_EOR3 Q19 Q19 Q26 Q14 *)
  0xce1b3e52;       (* arm_EOR3 Q18 Q18 Q27 Q15 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0ef4e10e;       (* arm_PMULL_VEC Q14 Q8 Q20 64 *)
  0x4ef4e10d;       (* arm_PMULL2_VEC Q13 Q8 Q20 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef5e36f;       (* arm_PMULL_VEC Q15 Q27 Q21 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0xce04752c;       (* arm_EOR3 Q12 Q9 Q4 Q29 *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0xce05752c;       (* arm_EOR3 Q12 Q9 Q5 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e18430b;       (* arm_EXT Q11 Q24 Q24 64 *)
  0x0ef9e11a;       (* arm_PMULL_VEC Q26 Q8 Q25 64 *)
  0x4ef9e11c;       (* arm_PMULL2_VEC Q28 Q8 Q25 64 *)
  0x0eebe37b;       (* arm_PMULL_VEC Q27 Q27 Q11 64 *)
  0xce1a3a73;       (* arm_EOR3 Q19 Q19 Q26 Q14 *)
  0xce1c3631;       (* arm_EOR3 Q17 Q17 Q28 Q13 *)
  0xce1b3e52;       (* arm_EOR3 Q18 Q18 Q27 Q15 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x0ef7e10e;       (* arm_PMULL_VEC Q14 Q8 Q23 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0xce06752c;       (* arm_EOR3 Q12 Q9 Q6 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef8e36f;       (* arm_PMULL_VEC Q15 Q27 Q24 64 *)
  0x4ef7e10d;       (* arm_PMULL2_VEC Q13 Q8 Q23 64 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x6e1542aa;       (* arm_EXT Q10 Q21 Q21 64 *)
  0xce1a3a73;       (* arm_EOR3 Q19 Q19 Q26 Q14 *)
  0xce07752c;       (* arm_EOR3 Q12 Q9 Q7 Q29 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0x0eeae37b;       (* arm_PMULL_VEC Q27 Q27 Q10 64 *)
  0xce1c3631;       (* arm_EOR3 Q17 Q17 Q28 Q13 *)
  0xce1b3e52;       (* arm_EOR3 Q18 Q18 Q27 Q15 *)
  0x6e200bde;       (* arm_REV32_VEC Q30 Q30 8 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e084110;       (* arm_EXT Q16 Q8 Q8 64 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0x2e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 64 *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x0ef5e210;       (* arm_PMULL_VEC Q16 Q16 Q21 64 *)
  0x6e301e52;       (* arm_EOR_VEC Q18 Q18 Q16 128 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x17ffff8d;       (* arm_B (word 268434996) *)
  0x4c40721e;       (* arm_LDR Q30 X16 No_Offset *)
  0x4c407073;       (* arm_LDR Q19 X3 No_Offset *)
  0xd2c0002f;       (* arm_MOVZ X15 (word 1) 32 *)
  0x4f00e41f;       (* arm_MOVI Q31 (word 0) *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0x4e181dff;       (* arm_INS_GEN Q31 X15 64 64 *)
  0x6e134270;       (* arm_EXT Q16 Q19 Q19 64 *)
  0x6e200bdd;       (* arm_REV32_VEC Q29 Q30 8 *)
  0xad400961;       (* arm_LDP Q1 Q2 X11 (Immediate_Offset (iword (&0))) *)
  0xad411163;       (* arm_LDP Q3 Q4 X11 (Immediate_Offset (iword (&32))) *)
  0xad421965;       (* arm_LDP Q5 Q6 X11 (Immediate_Offset (iword (&64))) *)
  0xad432167;       (* arm_LDP Q7 Q8 X11 (Immediate_Offset (iword (&96))) *)
  0xad442969;       (* arm_LDP Q9 Q10 X11 (Immediate_Offset (iword (&128))) *)
  0xad45316b;       (* arm_LDP Q11 Q12 X11 (Immediate_Offset (iword (&160))) *)
  0xad46396d;       (* arm_LDP Q13 Q14 X11 (Immediate_Offset (iword (&192))) *)
  0x3dc0396f;       (* arm_LDR Q15 X11 (Immediate_Offset (word 224)) *)
  0xf100813f;       (* arm_CMP X9 (rvalue (word 32)) *)
  0x5400008c;       (* arm_BGT (word 16) *)
  0xf100413f;       (* arm_CMP X9 (rvalue (word 16)) *)
  0x540003a0;       (* arm_BEQ (word 116) *)
  0x14000014;       (* arm_B (word 80) *)
  0xf100c13f;       (* arm_CMP X9 (rvalue (word 48)) *)
  0x54000140;       (* arm_BEQ (word 40) *)
  0x14000001;       (* arm_B (word 4) *)
  0x3dc014d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 80)) *)
  0xfd4024d9;       (* arm_LDR D25 X6 (Immediate_Offset (word 72)) *)
  0x6e104215;       (* arm_EXT Q21 Q16 Q16 64 *)
  0x2e301eb5;       (* arm_EOR_VEC Q21 Q21 Q16 64 *)
  0x4ef8e211;       (* arm_PMULL2_VEC Q17 Q16 Q24 64 *)
  0x0ef8e213;       (* arm_PMULL_VEC Q19 Q16 Q24 64 *)
  0x0ef9e2b2;       (* arm_PMULL_VEC Q18 Q21 Q25 64 *)
  0x14000019;       (* arm_B (word 100) *)
  0x3dc00cd8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 48)) *)
  0xfd4020d9;       (* arm_LDR D25 X6 (Immediate_Offset (word 64)) *)
  0x6e104215;       (* arm_EXT Q21 Q16 Q16 64 *)
  0x2e301eb5;       (* arm_EOR_VEC Q21 Q21 Q16 64 *)
  0x4ef8e211;       (* arm_PMULL2_VEC Q17 Q16 Q24 64 *)
  0x0ef8e213;       (* arm_PMULL_VEC Q19 Q16 Q24 64 *)
  0x0ef9e2b2;       (* arm_PMULL_VEC Q18 Q21 Q25 64 *)
  0x1400003c;       (* arm_B (word 240) *)
  0x3dc008d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 32)) *)
  0xfd400cd9;       (* arm_LDR D25 X6 (Immediate_Offset (word 24)) *)
  0x6e104215;       (* arm_EXT Q21 Q16 Q16 64 *)
  0x2e301eb5;       (* arm_EOR_VEC Q21 Q21 Q16 64 *)
  0x4ef8e211;       (* arm_PMULL2_VEC Q17 Q16 Q24 64 *)
  0x0ef8e213;       (* arm_PMULL_VEC Q19 Q16 Q24 64 *)
  0x0ef9e2b2;       (* arm_PMULL_VEC Q18 Q21 Q25 64 *)
  0x1400005f;       (* arm_B (word 380) *)
  0x3dc000d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 0)) *)
  0xfd4008d9;       (* arm_LDR D25 X6 (Immediate_Offset (word 16)) *)
  0x6e104215;       (* arm_EXT Q21 Q16 Q16 64 *)
  0x2e301eb5;       (* arm_EOR_VEC Q21 Q21 Q16 64 *)
  0x4ef8e211;       (* arm_PMULL2_VEC Q17 Q16 Q24 64 *)
  0x0ef8e213;       (* arm_PMULL_VEC Q19 Q16 Q24 64 *)
  0x0ef9e2b2;       (* arm_PMULL_VEC Q18 Q21 Q25 64 *)
  0x14000082;       (* arm_B (word 520) *)
  0x3cc1041a;       (* arm_LDR Q26 X0 (Postimmediate_Offset (word 16)) *)
  0x6e200ba0;       (* arm_REV32_VEC Q0 Q29 8 *)
  0x4ebf87bd;       (* arm_ADD_VEC Q29 Q29 Q31 32 128 *)
  0x4e284820;       (* arm_AESE Q0 Q1 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc014d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 80)) *)
  0xfd4024d9;       (* arm_LDR D25 X6 (Immediate_Offset (word 72)) *)
  0x4e200b54;       (* arm_REV64_VEC Q20 Q26 8 *)
  0x6e144295;       (* arm_EXT Q21 Q20 Q20 64 *)
  0x4e284840;       (* arm_AESE Q0 Q2 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284860;       (* arm_AESE Q0 Q3 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284880;       (* arm_AESE Q0 Q4 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848a0;       (* arm_AESE Q0 Q5 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x2e341eb5;       (* arm_EOR_VEC Q21 Q21 Q20 64 *)
  0x4ef8e296;       (* arm_PMULL2_VEC Q22 Q20 Q24 64 *)
  0x0ef8e297;       (* arm_PMULL_VEC Q23 Q20 Q24 64 *)
  0x0ef9e2be;       (* arm_PMULL_VEC Q30 Q21 Q25 64 *)
  0x4e2848c0;       (* arm_AESE Q0 Q6 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848e0;       (* arm_AESE Q0 Q7 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284900;       (* arm_AESE Q0 Q8 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284920;       (* arm_AESE Q0 Q9 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284940;       (* arm_AESE Q0 Q10 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e361e31;       (* arm_EOR_VEC Q17 Q17 Q22 128 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x6e3e1e52;       (* arm_EOR_VEC Q18 Q18 Q30 128 *)
  0x4e284960;       (* arm_AESE Q0 Q11 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284980;       (* arm_AESE Q0 Q12 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849a0;       (* arm_AESE Q0 Q13 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849c0;       (* arm_AESE Q0 Q14 *)
  0xce003f40;       (* arm_EOR3 Q0 Q26 Q0 Q15 *)
  0x3c810440;       (* arm_STR Q0 X2 (Postimmediate_Offset (word 16)) *)
  0x3cc1041a;       (* arm_LDR Q26 X0 (Postimmediate_Offset (word 16)) *)
  0x6e200ba0;       (* arm_REV32_VEC Q0 Q29 8 *)
  0x4ebf87bd;       (* arm_ADD_VEC Q29 Q29 Q31 32 128 *)
  0x4e284820;       (* arm_AESE Q0 Q1 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc00cd8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 48)) *)
  0xfd4020d9;       (* arm_LDR D25 X6 (Immediate_Offset (word 64)) *)
  0x4e200b54;       (* arm_REV64_VEC Q20 Q26 8 *)
  0x6e144295;       (* arm_EXT Q21 Q20 Q20 64 *)
  0x4e284840;       (* arm_AESE Q0 Q2 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284860;       (* arm_AESE Q0 Q3 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284880;       (* arm_AESE Q0 Q4 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848a0;       (* arm_AESE Q0 Q5 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x2e341eb5;       (* arm_EOR_VEC Q21 Q21 Q20 64 *)
  0x4ef8e296;       (* arm_PMULL2_VEC Q22 Q20 Q24 64 *)
  0x0ef8e297;       (* arm_PMULL_VEC Q23 Q20 Q24 64 *)
  0x0ef9e2be;       (* arm_PMULL_VEC Q30 Q21 Q25 64 *)
  0x4e2848c0;       (* arm_AESE Q0 Q6 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848e0;       (* arm_AESE Q0 Q7 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284900;       (* arm_AESE Q0 Q8 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284920;       (* arm_AESE Q0 Q9 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284940;       (* arm_AESE Q0 Q10 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e361e31;       (* arm_EOR_VEC Q17 Q17 Q22 128 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x6e3e1e52;       (* arm_EOR_VEC Q18 Q18 Q30 128 *)
  0x4e284960;       (* arm_AESE Q0 Q11 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284980;       (* arm_AESE Q0 Q12 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849a0;       (* arm_AESE Q0 Q13 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849c0;       (* arm_AESE Q0 Q14 *)
  0xce003f40;       (* arm_EOR3 Q0 Q26 Q0 Q15 *)
  0x3c810440;       (* arm_STR Q0 X2 (Postimmediate_Offset (word 16)) *)
  0x3cc1041a;       (* arm_LDR Q26 X0 (Postimmediate_Offset (word 16)) *)
  0x6e200ba0;       (* arm_REV32_VEC Q0 Q29 8 *)
  0x4ebf87bd;       (* arm_ADD_VEC Q29 Q29 Q31 32 128 *)
  0x4e284820;       (* arm_AESE Q0 Q1 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc008d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 32)) *)
  0xfd400cd9;       (* arm_LDR D25 X6 (Immediate_Offset (word 24)) *)
  0x4e200b54;       (* arm_REV64_VEC Q20 Q26 8 *)
  0x6e144295;       (* arm_EXT Q21 Q20 Q20 64 *)
  0x4e284840;       (* arm_AESE Q0 Q2 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284860;       (* arm_AESE Q0 Q3 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284880;       (* arm_AESE Q0 Q4 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848a0;       (* arm_AESE Q0 Q5 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x2e341eb5;       (* arm_EOR_VEC Q21 Q21 Q20 64 *)
  0x4ef8e296;       (* arm_PMULL2_VEC Q22 Q20 Q24 64 *)
  0x0ef8e297;       (* arm_PMULL_VEC Q23 Q20 Q24 64 *)
  0x0ef9e2be;       (* arm_PMULL_VEC Q30 Q21 Q25 64 *)
  0x4e2848c0;       (* arm_AESE Q0 Q6 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848e0;       (* arm_AESE Q0 Q7 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284900;       (* arm_AESE Q0 Q8 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284920;       (* arm_AESE Q0 Q9 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284940;       (* arm_AESE Q0 Q10 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e361e31;       (* arm_EOR_VEC Q17 Q17 Q22 128 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x6e3e1e52;       (* arm_EOR_VEC Q18 Q18 Q30 128 *)
  0x4e284960;       (* arm_AESE Q0 Q11 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284980;       (* arm_AESE Q0 Q12 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849a0;       (* arm_AESE Q0 Q13 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849c0;       (* arm_AESE Q0 Q14 *)
  0xce003f40;       (* arm_EOR3 Q0 Q26 Q0 Q15 *)
  0x3c810440;       (* arm_STR Q0 X2 (Postimmediate_Offset (word 16)) *)
  0x3cc1041a;       (* arm_LDR Q26 X0 (Postimmediate_Offset (word 16)) *)
  0x6e200ba0;       (* arm_REV32_VEC Q0 Q29 8 *)
  0x4ebf87bd;       (* arm_ADD_VEC Q29 Q29 Q31 32 128 *)
  0x4e284820;       (* arm_AESE Q0 Q1 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc000d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 0)) *)
  0xfd4008d9;       (* arm_LDR D25 X6 (Immediate_Offset (word 16)) *)
  0x4e200b54;       (* arm_REV64_VEC Q20 Q26 8 *)
  0x6e144295;       (* arm_EXT Q21 Q20 Q20 64 *)
  0x4e284840;       (* arm_AESE Q0 Q2 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x2e341eb5;       (* arm_EOR_VEC Q21 Q21 Q20 64 *)
  0x4ef8e296;       (* arm_PMULL2_VEC Q22 Q20 Q24 64 *)
  0x0ef8e297;       (* arm_PMULL_VEC Q23 Q20 Q24 64 *)
  0x0ef9e2be;       (* arm_PMULL_VEC Q30 Q21 Q25 64 *)
  0x4e284860;       (* arm_AESE Q0 Q3 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284880;       (* arm_AESE Q0 Q4 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e361e31;       (* arm_EOR_VEC Q17 Q17 Q22 128 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x6e3e1e52;       (* arm_EOR_VEC Q18 Q18 Q30 128 *)
  0x4e2848a0;       (* arm_AESE Q0 Q5 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848c0;       (* arm_AESE Q0 Q6 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x0ef0e236;       (* arm_PMULL_VEC Q22 Q17 Q16 64 *)
  0x4e2848e0;       (* arm_AESE Q0 Q7 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e331e37;       (* arm_EOR_VEC Q23 Q17 Q19 128 *)
  0x6e114231;       (* arm_EXT Q17 Q17 Q17 64 *)
  0x4e284900;       (* arm_AESE Q0 Q8 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e371e52;       (* arm_EOR_VEC Q18 Q18 Q23 128 *)
  0x6e361e36;       (* arm_EOR_VEC Q22 Q17 Q22 128 *)
  0x4e284920;       (* arm_AESE Q0 Q9 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e361e52;       (* arm_EOR_VEC Q18 Q18 Q22 128 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x4e284940;       (* arm_AESE Q0 Q10 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e124252;       (* arm_EXT Q18 Q18 Q18 64 *)
  0x4e284960;       (* arm_AESE Q0 Q11 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e311e73;       (* arm_EOR_VEC Q19 Q19 Q17 128 *)
  0x6e321e73;       (* arm_EOR_VEC Q19 Q19 Q18 128 *)
  0x4e284980;       (* arm_AESE Q0 Q12 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0x4e2849a0;       (* arm_AESE Q0 Q13 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4c007073;       (* arm_STR Q19 X3 No_Offset *)
  0x6e200bbe;       (* arm_REV32_VEC Q30 Q29 8 *)
  0x4e2849c0;       (* arm_AESE Q0 Q14 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0xce003f40;       (* arm_EOR3 Q0 Q26 Q0 Q15 *)
  0x3c810440;       (* arm_STR Q0 X2 (Postimmediate_Offset (word 16)) *)
  0x17fffea5;       (* arm_B (word 268434068) *)
  0x52800000;       (* arm_MOV W0 (rvalue (word 0)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

(* The code begins with the BTI landing pad (bti c).  As for x86 IBT, the    *)
(* proofs are about the trimmed code without it, which is the code of a      *)
(* -DNO_IBT build, and the subroutine theorems for the full code are derived *)
(* from them by ARM_ADD_IBT_RULE.  So the code offsets in this file, pc + n  *)
(* in the statements and 0x... in the comments, are those of the trimmed     *)
(* code, as in a disassembly of a -DNO_IBT object.  In the default object,   *)
(* and in the comments of the .S file, they are 4 larger.                    *)

let aes256_gcm_dec_alt_tmc =
  define_trimmed "aes256_gcm_dec_alt_tmc" aes256_gcm_dec_alt_mc;;
let AES256_GCM_DEC_ALT_EXEC = ARM_MK_EXEC_RULE aes256_gcm_dec_alt_tmc;;

(* `|- LENGTH aes256_gcm_dec_alt_tmc = 5908`.  Most statements spell the code
   region in their nonoverlapping preconditions as
   `LENGTH aes256_gcm_dec_alt_tmc`; the small-path theorems WB_FUSED_1BLOCK to
   WB_FUSED_4BLOCK and some terms of the safety proof write the numeral 5908.
   The store-safety check of the stepper (NONSELFMODIFYING_STATE_UPDATE_TAC,
   through ORTHOGONAL_COMPONENTS_RULE) does numeric arithmetic on that length,
   so each simulation first reduces it to the numeral with
   RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]), as aes_xts_decrypt.ml does. *)
let WB_MC_LEN = fst AES256_GCM_DEC_ALT_EXEC;;

(* ------------------------------------------------------------------------- *)
(* Shared statement and capture machinery.                                   *)
(* ------------------------------------------------------------------------- *)

(* ========================================================================= *)
(* AES tower reconstruction: AES256_XOR_ENCRYPT_RECONSTRUCT and aes13.       *)
(*                                                                           *)
(* The kernel leaves the per-block keystreams as raw 14-round aese/aesmc     *)
(* towers.  These lemmas fold them onto the aes256_encrypt specification     *)
(* once, so that every capture site is a rewrite rather than an unfold and a *)
(* blast of its own (as AES256_CIPHER_RECONSTRUCT of aes_gcm_common.ml does  *)
(* for aes256_cipher).                                                       *)
(* ========================================================================= *)

(* The kernel's 14-round aese/aesmc tower XORed with (k14 XOR cph) is the
   ciphertext XORed with the aes256_encrypt keystream; proved once, so that
   every per-block plaintext capture is a rewrite. *)
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

(* The kernel's in-flight keystream tower: rounds 0..12 (aese then aesmc) and
   the final aese with k13.  The last round key k14 is XORed in later, together
   with the ciphertext, by one eor3 per block, so naming this partial tower
   keeps the register contracts between the front, the loop and the tail at
   one application per block, and the reconstruct lemma below lets every tail
   capture site work on the folded form.  The shared
   XOR_AES256_CIPHER_RECONSTRUCT folds only the complete cipher, so aes13
   stays private machine-level vocabulary: the exported theorems mention only
   aes256_cipher. *)
let aes13 = new_definition
 `aes13 (p:int128) (k0:int128) (k1:int128) (k2:int128) (k3:int128) (k4:int128)
        (k5:int128) (k6:int128) (k7:int128) (k8:int128) (k9:int128) (k10:int128)
        (k11:int128) (k12:int128) (k13:int128) : int128 =
    aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese
      (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
      (aese p k0) ) k1) ) k2) ) k3) ) k4) ) k5) ) k6) ) k7) ) k8) ) k9) ) k10) ) k11) ) k12) ) k13`;;

(* The same lemma over aes13.  The tail capture sites rewrite with its GSYM,
   so rebinding the name keeps them unchanged while the front postcondition
   stays folded. *)
let AES256_XOR_ENCRYPT_RECONSTRUCT =
  REWRITE_RULE[GSYM aes13] AES256_XOR_ENCRYPT_RECONSTRUCT;;

(* The memoized normalizer: the three rewrites of GCM_SIMD_SIMPLIFY_CORE_TAC,
   applied only to the `read Qn s = ...` assumptions, with tbl recording the
   conclusions already at their fixpoint, which are then skipped.  The
   rewrites depend only on the conclusion, so the result is the same as
   without the table.  Its three users each own a table, cleared at the start
   of each proof. *)
let GCM_SIMD_SIMPLIFY_MEMO_TAC (tbl:(term,unit) Hashtbl.t) : tactic =
  let is_qreg_read c = match c with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),cmp),_)),_) ->
        (match cmp with Const(rn,_) ->
           String.length rn >= 2 && rn.[0]='Q' && rn.[1]>='0' && rn.[1]<='9'
         | _ -> false)
    | _ -> false in
  let apply_F th =
    let th1 = (try REWRITE_RULE SIMD_SIMPLIFY_RULES th with _ -> th) in
    let th2 = REWRITE_RULE [WORD_SWAP_HALVES_INVOLUTION; EXT8_LANE0_IS_SUBWORD_HI] th1 in
    (try CONV_RULE(RAND_CONV(REV32_LANE_SUBWORD_CONV)) th2 with _ -> th2) in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if not(is_qreg_read c) then th
    else if Hashtbl.mem tbl c then th
    else let th' = apply_F th in
         (if concl th' = c then Hashtbl.add tbl c ());
         th');;
let GCM_SIMD_SIMPLIFY_KGH_TAC = GCM_SIMD_SIMPLIFY_MEMO_TAC gcm_simd_kgh_tbl;;
let ARM_STEPS_FOLD_KEEPGH_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_KGH_TAC THEN
              DISCARD_OLDSTATE_KEEPGH_TAC s THEN CLARIFY_TAC) (statenames "s" snums);;

(* ------------------------------------------------------------------------- *)
(* Machinery shared by the band tails: bridge closers, spec folds, steppers. *)
(* ------------------------------------------------------------------------- *)

(* The 2-block bridge close (by GMULT2_FULL_CORRECT_BA), with karatsuba_mid
   unfolded first: htable_mem_dec presents the hk slot as
   word_join (karatsuba_mid h2) (karatsuba_mid h), and the merge needs the
   expanded subword form to pair the machine mids with the spec mids. *)
let WB2_GMULT2_BRIDGE_TAC : tactic =
  let a0t = `word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`
  and a1t = `word_bytereverse cph1:int128` in
  let gmult2_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [a0t; `byteswap128 h2:int128`; a1t; `byteswap128 h:int128`] GMULT2_FULL_CORRECT_BA) in
  let r1def = `word_xor (word_xor (word_shl (word_zx (wal:64 word):128 word) 63) (word_shl (word_zx wal:128 word) 62)) (word_shl (word_zx wal:128 word) 57)` in
  let udef = `word_xor (word_subword (r1:128 word) (0,64):64 word) (word_xor (word_xor qq1h qq6h) (word_xor (word_xor qq0l (word_xor qq1l qq4l)) (word_xor qq5l (word_xor qq10l qq6l))))` in
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th)=`byteswap128 h2` with _->false)
    then GEN_REWRITE_TAC RAND_CONV
           [REWRITE_RULE[GSYM gmult2_dec]
             (GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) [GSYM th]
               (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
                       `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`]
                 GHASH_POLYVAL_ACC_2))]
    else NO_TAC) THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[byteswap128] THEN
  REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
  REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
  REWRITE_TAC[karatsuba_mid] THEN
  ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
  REWRITE_TAC[PMUL_W_64_128] THEN REWRITE_TAC[JOINMID] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  EVERY (map (fun a ->
    let av = mk_var(a,`:int128`) in
    ABBREV_TAC (mk_eq(mk_var(a^"l",`:64 word`), mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, av), `(0,64)`))) THEN
    ABBREV_TAC (mk_eq(mk_var(a^"h",`:64 word`), mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, av), `(64,64)`))))
    ["qq0";"qq1";"qq4";"qq5";"qq6";"qq10"]) THEN
  ABBREV_TAC `wal:64 word = word_xor qq1l qq6l` THEN
  REWRITE_TAC[DEC2_WXSYM] THEN
  FIRST_ASSUM(fun th -> if (try rhs(concl th)=`wal:64 word` && lhs(concl th)=`word_xor qq1l qq6l:64 word` with _->false) then REWRITE_TAC[th] else NO_TAC) THEN
  ABBREV_TAC (mk_eq(`r1:128 word`, r1def)) THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 63) (0,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 62) (0,64):64 word)) (word_subword (word_shl (word_zx wal:128 word) 57) (0,64):64 word) = word_subword (r1:128 word) (0,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 63) (64,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 62) (64,64):64 word)) (word_subword (word_shl (word_zx wal:128 word) 57) (64,64):64 word) = word_subword (r1:128 word) (64,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 57) (0,64):64 word) (word_xor (word_subword (word_shl (word_zx wal:128 word) 62) (0,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 63) (0,64):64 word)) = word_subword (r1:128 word) (0,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 57) (64,64):64 word) (word_xor (word_subword (word_shl (word_zx wal:128 word) 62) (64,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 63) (64,64):64 word)) = word_subword (r1:128 word) (64,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  ABBREV_TAC (mk_eq(`u:64 word`, udef)) THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_xor qq10l qq4l) (word_xor wal (word_xor qq0l qq5l))) (word_xor (word_xor qq1h qq6h) (word_subword (r1:128 word) (0,64):64 word)) = u`
   (fun th -> REWRITE_TAC[th]) THENL [MAP_EVERY EXPAND_TAC ["u";"wal"] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_subword (r1:128 word) (0,64):64 word) (word_xor (word_xor qq1h qq6h) (word_xor (word_xor qq0l (word_xor qq1l qq4l)) (word_xor qq5l (word_xor qq10l qq6l)))) = u`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "u" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC `us57:128 word = word_shl (word_zx (u:64 word):128 word) 57` THEN
  ABBREV_TAC `us62:128 word = word_shl (word_zx (u:64 word):128 word) 62` THEN
  ABBREV_TAC `us63:128 word = word_shl (word_zx (u:64 word):128 word) 63` THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_CLOSE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The band tails WB_TAIL_1_TAC .. WB_TAIL_8_TAC, from the seam pc+3824      *)
(* through the residue cascade (or the exact-8 drain), the GHASH multiply    *)
(* and reduction, the bridge and the stores to the core exit pc+4508.  Their *)
(* states are numbered on from s265, the name WB_PREP_TAC gives the seam     *)
(* state (WB_FRONT_BUF reaches it as s273).                                  *)
(* ------------------------------------------------------------------------- *)

let WB_TAIL_1_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AES256_GCM_DEC_ALT_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AES256_GCM_DEC_ALT_EXEC (278--313) THEN
  (* 314..333: the GHASH multiply, with the KEEPGH stepper keeping Q16-Q19 *)
  ARM_STEPS_FOLD_KEEPGH_TAC AES256_GCM_DEC_ALT_EXEC (314--333) THEN
  (* plaintext capture: Q12 = word_xor cph (aes256_encrypt ctr0 keys) *)
  SUBGOAL_THEN `read Q12 (s333:armstate) = word_xor cph (aes256_encrypt (ctr0:int128)
      [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q12 s333` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q12 s333` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  (* 334: st1 {v12.16b},[x2], the output store; carry its readback across
     the discard *)
  ARM_VSTEPS_FOLD_TAC AES256_GCM_DEC_ALT_EXEC [334] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 out_p) s334` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_TAC "s334" THEN DISCH_TAC THEN
  (* 335..341: the GHASH reduction, keeping Q16-Q19; Q19 at s341 is then a
     term over word_bytereverse xi, cph and h with no state references *)
  ARM_STEPS_FOLD_KEEPGH_TAC AES256_GCM_DEC_ALT_EXEC (335--341) THEN
  (* the GHASH bridge at s341 (pc+4496, after eor v19,v19,v18) *)
  SUBGOAL_THEN
    `read Q19 (s341:armstate) =
     polyval_dot (word_xor (word_bytereverse xi) (word_bytereverse cph))
       (byteswap128 h)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s341` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s341` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   GEN_REWRITE_TAC RAND_CONV
     [GSYM(REWRITE_RULE[LET_DEF; LET_END_DEF]
        (ISPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph) : int128`;
          `byteswap128 h:int128`] GMULT_FULL_CORRECT_BA))] THEN
   REWRITE_TAC[byteswap128] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_PMUL_ATOMS_TAC THEN
   TRY(SUBGOAL_THEN `qq5:int128 = qq2` (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qq5" THEN EXPAND_TAC "qq2" THEN REWRITE_TAC[karatsuba_mid] THEN
     ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST)
      ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
              MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST));
     ALL_TAC]) THEN
   REWRITE_TAC[SUBWORD0_LEMMAS; WORD_XOR_0] THEN REWRITE_TAC[WORD_XOR_0] THEN
   REWRITE_TAC[PMUL_W_64_128] THEN
   REWRITE_TAC[JOINMID] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   ABBREV_TAC `xll:64 word = word_subword (qq0:int128) (0,64)` THEN
   ABBREV_TAC `xlh:64 word = word_subword (qq0:int128) (64,64)` THEN
   ABBREV_TAC `xhl:64 word = word_subword (qq1:int128) (0,64)` THEN
   ABBREV_TAC `xhh:64 word = word_subword (qq1:int128) (64,64)` THEN
   ABBREV_TAC `xml:64 word = word_subword (qq2:int128) (0,64)` THEN
   ABBREV_TAC `xmh:64 word = word_subword (qq2:int128) (64,64)` THEN
   ABBREV_TAC
    `r1:(128)word = word_xor (word_xor (word_shl (word_zx (xhl:(64)word):(128)word) 63)
                                       (word_shl (word_zx xhl:(128)word) 62))
                             (word_shl (word_zx xhl:(128)word) 57)` THEN
   SUBGOAL_THEN
    `word_xor (word_xor (word_subword (word_shl (word_zx (xhl:(64)word):(128)word) 63) (0,64):(64)word)
                        (word_subword (word_shl (word_zx xhl:(128)word) 62) (0,64):(64)word))
              (word_subword (word_shl (word_zx xhl:(128)word) 57) (0,64):(64)word) =
     word_subword (r1:(128)word) (0,64):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   SUBGOAL_THEN
    `word_xor (word_xor (word_subword (word_shl (word_zx (xhl:(64)word):(128)word) 63) (64,64):(64)word)
                        (word_subword (word_shl (word_zx xhl:(128)word) 62) (64,64):(64)word))
              (word_subword (word_shl (word_zx xhl:(128)word) 57) (64,64):(64)word) =
     word_subword (r1:(128)word) (64,64):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   ABBREV_TAC `u:(64)word = word_xor (word_xor (word_subword (r1:128 word) (0,64)) (xhh:64 word)) (word_xor (word_xor (xll:64 word) (xhl:64 word)) (xml:64 word))` THEN
   SUBGOAL_THEN
    `word_xor (word_xor (xhh:64 word) (word_xor (word_xor (xml:64 word) (xhl:64 word)) (xll:64 word))) (word_subword (r1:128 word) (0,64)) = u`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "u" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   ABBREV_TAC
    `r2:(128)word = word_xor (word_xor (word_shl (word_zx (u:(64)word):(128)word) 63)
                                       (word_shl (word_zx u:(128)word) 62))
                             (word_shl (word_zx u:(128)word) 57)` THEN
   SUBGOAL_THEN
    `word_xor (word_xor (word_subword (word_shl (word_zx (u:(64)word):(128)word) 63) (0,64):(64)word)
                        (word_subword (word_shl (word_zx u:(128)word) 62) (0,64):(64)word))
              (word_subword (word_shl (word_zx u:(128)word) 57) (0,64):(64)word) =
     word_subword (r2:(128)word) (0,64):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r2" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   SUBGOAL_THEN
    `word_xor (word_xor (word_subword (word_shl (word_zx (u:(64)word):(128)word) 63) (64,64):(64)word)
                        (word_subword (word_shl (word_zx u:(128)word) 62) (64,64):(64)word))
              (word_subword (word_shl (word_zx u:(128)word) 57) (64,64):(64)word) =
     word_subword (r2:(128)word) (64,64):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r2" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   TRY(SUBGOAL_THEN `qq0:int128 = word_join (xlh:64 word) (xll:64 word)`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "xll" THEN EXPAND_TAC "xlh" THEN CONV_TAC WORD_BLAST; ALL_TAC]) THEN
   CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = polyval_dot (word_xor (word_bytereverse xi)
    (word_bytereverse cph)) (byteswap128 h)` THEN
  (* 342 ext (half-swap), 343 rev64 -> Q19 = word_bytereverse gval *)
  ARM_VSTEPS_FOLD_TAC AES256_GCM_DEC_ALT_EXEC (342--343) THEN
  SUBGOAL_THEN `read Q19 (s343:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s343` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s343` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  (* 344 = st1 {v19.16b},[x3] (tag store); exit at pc+4508 *)
  ARM_VSTEPS_TAC AES256_GCM_DEC_ALT_EXEC [344] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [CONJ_TAC THENL
    [EXPAND_TAC "gval" THEN AP_TERM_TAC THEN REWRITE_TAC[GHASH_1BLOCK_CORRECT];
     ivtac];
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
   REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]];;

let WB_TAIL_2_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AES256_GCM_DEC_ALT_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AES256_GCM_DEC_ALT_EXEC (278--313) THEN
  (* 314..319: the block-0 GHASH round of L256_dec_blocks_more_than_1;
     capture the block-0 plaintext at s319 *)
  ARM_STEPS_FOLD_KEEPGH_TAC AES256_GCM_DEC_ALT_EXEC (314--319) THEN
  SUBGOAL_THEN `read Q12 (s319:armstate) = word_xor cph0 (aes256_encrypt (ctr0:int128)
      [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q12 s319` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q12 s319` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  (* 320: st1 {v12.16b},[x2],#16, the block-0 store; carry its readback
     across the discard *)
  ARM_VSTEPS_FOLD_TAC AES256_GCM_DEC_ALT_EXEC [320] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 out_p) s320` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_KEEPGH_TAC "s320" THEN DISCH_TAC THEN
  (* 321..325: the block-1 plaintext lands in Q12 by eor3 v12,v9,v7,v29;
     capture it, with GCM_CTR_INC_LANES folding the keystream input to
     gcm_ctr_inc ctr0 *)
  ARM_STEPS_FOLD_KEEPGH_TAC AES256_GCM_DEC_ALT_EXEC (321--325) THEN
  SUBGOAL_THEN `read Q12 (s325:armstate) = word_xor cph1 (aes256_encrypt
      (gcm_ctr_inc ctr0:int128)
      [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q12 s325` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q12 s325` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  (* 326..347: the block-1 GHASH round and the start of the reduction *)
  ARM_STEPS_FOLD_KEEPGH_TAC AES256_GCM_DEC_ALT_EXEC (326--347) THEN
  (* 348: st1 {v12.16b},[x2], the block-1 store, by plain ARM_VSTEPS_TAC
     (the simplifier of the FOLD variant gets stuck here); carry both out_p
     readbacks across the discard *)
  ARM_VSTEPS_TAC AES256_GCM_DEC_ALT_EXEC [348] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add out_p (word 16))) s348` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 out_p) s348` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_KEEPGH_TAC "s348" THEN DISCH_TAC THEN DISCH_TAC THEN
  (* 349..355: the single Prop3 reduction of both blocks; bridge at s355 *)
  ARM_STEPS_FOLD_KEEPGH_TAC AES256_GCM_DEC_ALT_EXEC (349--355) THEN
  (* the GMULT2 bridge at s355 (pc+4496, after eor v19,v19,v18) *)
  SUBGOAL_THEN
    `read Q19 (s355:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s355` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s355` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   WB2_GMULT2_BRIDGE_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1]` THEN
  (* 356 ext (half-swap), 357 rev64 -> Q19 = word_bytereverse gval *)
  ARM_VSTEPS_FOLD_TAC AES256_GCM_DEC_ALT_EXEC (356--357) THEN
  SUBGOAL_THEN `read Q19 (s357:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s357` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s357` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  (* 358 = st1 {v19.16b},[x3] (tag store); exit at pc+4508 *)
  ARM_VSTEPS_TAC AES256_GCM_DEC_ALT_EXEC [358] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [ivtac;
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
   REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]];;

let WB_TAIL_3_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AES256_GCM_DEC_ALT_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AES256_GCM_DEC_ALT_EXEC (278--309)  THEN
  ARM_STEPS_FOLD_Q18LATEST_TAC AES256_GCM_DEC_ALT_EXEC (310--359) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s359` THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AES256_GCM_DEC_ALT_EXEC (360--366) THEN
  SUBGOAL_THEN
    `read Q19 (s366:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s366` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s366` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   (fun (asl,w) ->
     let gmult3_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
       (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h3:int128`;
               `word_bytereverse cph1:int128`; `byteswap128 h2:int128`;
               `word_bytereverse cph2:int128`; `byteswap128 h:int128`] GMULT3_FULL_CORRECT_BA) in
     let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
     let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
     (GEN_REWRITE_TAC RAND_CONV
        [TRANS (MP spec_to_byteform_wb3 (CONJ h2asm h3asm)) (GSYM gmult3_dec)]) (asl,w)) THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   REWRITE_TAC[karatsuba_mid] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   (fun (asl,w) ->
     let (_,th) = List.find (fun (_,th) ->
       try rand(concl th) = `midacc:int128` && is_eq(concl th) with _ -> false) asl in
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w)) THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   AUTO_MERGE_MIDS_KM_TAC THEN
   WA_UNIFY_BB_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_Z_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]` THEN
  ARM_VSTEPS_FOLD_TAC AES256_GCM_DEC_ALT_EXEC (367--368) THEN
  SUBGOAL_THEN `read Q19 (s368:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s368` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s368` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AES256_GCM_DEC_ALT_EXEC [369] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(ivtac THEN NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST(map (fun lanes ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lanes] THEN
        REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC)
      [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES]) THEN NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;

let WB_TAIL_4_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AES256_GCM_DEC_ALT_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AES256_GCM_DEC_ALT_EXEC (278--303)  THEN
  ARM_STEPS_FOLD_Q18LATEST_TAC AES256_GCM_DEC_ALT_EXEC (304--370) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s370` THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AES256_GCM_DEC_ALT_EXEC (371--377) THEN
  SUBGOAL_THEN
    `read Q19 (s377:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1;
        word_bytereverse cph2; word_bytereverse cph3]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s377` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s377` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   (fun (asl,w) ->
     let gmult4_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
       (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h4:int128`;
               `word_bytereverse cph1:int128`; `byteswap128 h3:int128`;
               `word_bytereverse cph2:int128`; `byteswap128 h2:int128`;
               `word_bytereverse cph3:int128`; `byteswap128 h:int128`] GMULT4_FULL_CORRECT_BA) in
     let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
     let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
     let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
     (GEN_REWRITE_TAC RAND_CONV
        [TRANS (MP spec_to_byteform_wb4 (CONJ h2asm (CONJ h3asm h4asm))) (GSYM gmult4_dec)]) (asl,w)) THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   REWRITE_TAC[karatsuba_mid] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   (fun (asl,w) ->
     let (_,th) = List.find (fun (_,th) ->
       try rand(concl th) = `midacc:int128` && is_eq(concl th) with _ -> false) asl in
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w)) THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   AUTO_MERGE_MIDS_KM_TAC THEN
   WA_UNIFY_BB_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_Z_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
       word_bytereverse cph3]` THEN
  ARM_VSTEPS_FOLD_TAC AES256_GCM_DEC_ALT_EXEC (378--379) THEN
  SUBGOAL_THEN `read Q19 (s379:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s379` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s379` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AES256_GCM_DEC_ALT_EXEC [380] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(ivtac THEN NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST(map (fun lanes ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lanes] THEN
        REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC)
      [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES]) THEN NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;

let WB_TAIL_5_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AES256_GCM_DEC_ALT_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AES256_GCM_DEC_ALT_EXEC (278--297)  THEN
  ARM_STEPS_FOLD_Q18LATEST_TAC AES256_GCM_DEC_ALT_EXEC (298--378) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s378` THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AES256_GCM_DEC_ALT_EXEC (379--385) THEN
  SUBGOAL_THEN
    `read Q19 (s385:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1;
        word_bytereverse cph2; word_bytereverse cph3; word_bytereverse cph4]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s385` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s385` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   (fun (asl,w) ->
     let gmult5_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
       (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h5:int128`;
               `word_bytereverse cph1:int128`; `byteswap128 h4:int128`;
               `word_bytereverse cph2:int128`; `byteswap128 h3:int128`;
               `word_bytereverse cph3:int128`; `byteswap128 h2:int128`;
               `word_bytereverse cph4:int128`; `byteswap128 h:int128`] GMULT5_FULL_CORRECT_BA) in
     let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
     let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
     let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
     let h5asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h5` with _->false) asl) in
     (GEN_REWRITE_TAC RAND_CONV
        [TRANS (MP spec_to_byteform_wb5 (CONJ h2asm (CONJ h3asm (CONJ h4asm h5asm)))) (GSYM gmult5_dec)]) (asl,w)) THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   REWRITE_TAC[karatsuba_mid] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   (fun (asl,w) ->
     let (_,th) = List.find (fun (_,th) ->
       try rand(concl th) = `midacc:int128` && is_eq(concl th) with _ -> false) asl in
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w)) THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   AUTO_MERGE_MIDS_KM_TAC THEN
   WA_UNIFY_BB_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_Z_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
       word_bytereverse cph3; word_bytereverse cph4]` THEN
  ARM_VSTEPS_FOLD_TAC AES256_GCM_DEC_ALT_EXEC (386--387) THEN
  SUBGOAL_THEN `read Q19 (s387:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s387` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s387` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AES256_GCM_DEC_ALT_EXEC [388] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(ivtac THEN NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST(map (fun lanes ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lanes] THEN
        REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC)
      [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES]) THEN NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;

let WB_TAIL_6_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AES256_GCM_DEC_ALT_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AES256_GCM_DEC_ALT_EXEC (278--290)  THEN
  ARM_STEPS_FOLD_Q18LATEST_TAC AES256_GCM_DEC_ALT_EXEC (291--386) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s386` THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AES256_GCM_DEC_ALT_EXEC (387--393) THEN
  SUBGOAL_THEN
    `read Q19 (s393:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
        word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s393` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s393` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   (fun (asl,w) ->
     let gmult6_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
       (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h6:int128`;
               `word_bytereverse cph1:int128`; `byteswap128 h5:int128`;
               `word_bytereverse cph2:int128`; `byteswap128 h4:int128`;
               `word_bytereverse cph3:int128`; `byteswap128 h3:int128`;
               `word_bytereverse cph4:int128`; `byteswap128 h2:int128`;
               `word_bytereverse cph5:int128`; `byteswap128 h:int128`] GMULT6_FULL_CORRECT_BA) in
     let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
     let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
     let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
     let h5asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h5` with _->false) asl) in
     let h6asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h6` with _->false) asl) in
     (GEN_REWRITE_TAC RAND_CONV
        [TRANS (MP spec_to_byteform_wb6 (CONJ h2asm (CONJ h3asm (CONJ h4asm (CONJ h5asm h6asm))))) (GSYM gmult6_dec)]) (asl,w)) THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   REWRITE_TAC[karatsuba_mid] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   (fun (asl,w) ->
     let (_,th) = List.find (fun (_,th) ->
       try rand(concl th) = `midacc:int128` && is_eq(concl th) with _ -> false) asl in
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w)) THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   AUTO_MERGE_MIDS_KM_TAC THEN
   WA_UNIFY_BB_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_Z_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
       word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5]` THEN
  ARM_VSTEPS_FOLD_TAC AES256_GCM_DEC_ALT_EXEC (394--395) THEN
  SUBGOAL_THEN `read Q19 (s395:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s395` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s395` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AES256_GCM_DEC_ALT_EXEC [396] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(ivtac THEN NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST(map (fun lanes ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lanes] THEN
        REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC)
      [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES;
       GCM_CTR_INC5_LANES]) THEN NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;

let WB_TAIL_7_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AES256_GCM_DEC_ALT_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AES256_GCM_DEC_ALT_EXEC (278--282)  THEN
  ARM_STEPS_FOLD_Q18LATEST_TAC AES256_GCM_DEC_ALT_EXEC (283--392) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s392` THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AES256_GCM_DEC_ALT_EXEC (393--399) THEN
  SUBGOAL_THEN
    `read Q19 (s399:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
        word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
        word_bytereverse cph6]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s399` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s399` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   (fun (asl,w) ->
     let gmult7_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
       (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h7:int128`;
               `word_bytereverse cph1:int128`; `byteswap128 h6:int128`;
               `word_bytereverse cph2:int128`; `byteswap128 h5:int128`;
               `word_bytereverse cph3:int128`; `byteswap128 h4:int128`;
               `word_bytereverse cph4:int128`; `byteswap128 h3:int128`;
               `word_bytereverse cph5:int128`; `byteswap128 h2:int128`;
               `word_bytereverse cph6:int128`; `byteswap128 h:int128`] GMULT7_FULL_CORRECT_BA) in
     let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
     let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
     let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
     let h5asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h5` with _->false) asl) in
     let h6asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h6` with _->false) asl) in
     let h7asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h7` with _->false) asl) in
     (GEN_REWRITE_TAC RAND_CONV
        [TRANS (MP spec_to_byteform_wb7 (CONJ h2asm (CONJ h3asm (CONJ h4asm (CONJ h5asm (CONJ h6asm h7asm)))))) (GSYM gmult7_dec)]) (asl,w)) THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   REWRITE_TAC[karatsuba_mid] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   (fun (asl,w) ->
     let (_,th) = List.find (fun (_,th) ->
       try rand(concl th) = `midacc:int128` && is_eq(concl th) with _ -> false) asl in
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w)) THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   AUTO_MERGE_MIDS_KM_TAC THEN
   WA_UNIFY_BB_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_Z_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
       word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
       word_bytereverse cph6]` THEN
  ARM_VSTEPS_FOLD_TAC AES256_GCM_DEC_ALT_EXEC (400--401) THEN
  SUBGOAL_THEN `read Q19 (s401:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s401` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s401` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AES256_GCM_DEC_ALT_EXEC [402] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(ivtac THEN NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST(map (fun lanes ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lanes] THEN
        REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC)
      [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES;
       GCM_CTR_INC5_LANES; GCM_CTR_INC6_LANES]) THEN NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;

let WB_TAIL_8_TAC ivtac =
  (* r = 8 takes the b.gt at 0xf00 into the straight-line drain
     L256_dec_exact8_drain (0x11b4..0x1330) instead of the residue cascade,
     which only r = 1..7 enter.  The drain folds three block pairs with eor3
     (the first block of each pair parks its products in v13/v14/v15, which
     are added into the accumulators together with the second block's) and
     rejoins the shared reduction at 0x1164 (L256_dec_epilogue) with a b;
     XOR is associative and commutative, so the same byteform close applies.
     ARM_STEPS_RESOLVE_TAC (266--270) resolves the b.gt into the drain. *)
  ARM_STEPS_RESOLVE_TAC AES256_GCM_DEC_ALT_EXEC (266--270)  THEN
  (* 271..370: the drain and the start of the reduction, by the Q18-latest
     stepper (the store readbacks carry themselves forward) *)
  ARM_STEPS_FOLD_Q18LATEST_TAC AES256_GCM_DEC_ALT_EXEC (271--370) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s370` THEN
  (* orient the definition as tree = midacc, so that the steppers rewrite
     towards the atom *)
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AES256_GCM_DEC_ALT_EXEC (371--377) THEN
  SUBGOAL_THEN
    `read Q19 (s377:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
        word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
        word_bytereverse cph6; word_bytereverse cph7]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s377` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s377` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
      (fun (asl,w) ->
     let gmult8_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
       (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h8:int128`;
               `word_bytereverse cph1:int128`; `byteswap128 h7:int128`;
               `word_bytereverse cph2:int128`; `byteswap128 h6:int128`;
               `word_bytereverse cph3:int128`; `byteswap128 h5:int128`;
               `word_bytereverse cph4:int128`; `byteswap128 h4:int128`;
               `word_bytereverse cph5:int128`; `byteswap128 h3:int128`;
               `word_bytereverse cph6:int128`; `byteswap128 h2:int128`;
               `word_bytereverse cph7:int128`; `byteswap128 h:int128`] GMULT8_FULL_CORRECT_BA) in
     let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
     let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
     let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
     let h5asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h5` with _->false) asl) in
     let h6asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h6` with _->false) asl) in
     let h7asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h7` with _->false) asl) in
     let h8asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h8` with _->false) asl) in
     (GEN_REWRITE_TAC RAND_CONV
        [TRANS (MP spec_to_byteform_wb8 (CONJ h2asm (CONJ h3asm (CONJ h4asm (CONJ h5asm (CONJ h6asm (CONJ h7asm h8asm))))))) (GSYM gmult8_dec)]) (asl,w)) THEN
      REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
      REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
      REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
      REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
      REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
      REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
      REWRITE_TAC[karatsuba_mid] THEN
      ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
      MERGE_ANY_TAC THEN
   (fun (asl,w) ->
     let (_,th) = List.find (fun (_,th) ->
       try rand(concl th) = `midacc:int128` && is_eq(concl th) with _ -> false) asl in
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w)) THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   AUTO_MERGE_MIDS_KM_TAC THEN
   WA_UNIFY_BB_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
       word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
       word_bytereverse cph6; word_bytereverse cph7]` THEN
  ARM_VSTEPS_FOLD_TAC AES256_GCM_DEC_ALT_EXEC (378--379) THEN
  SUBGOAL_THEN `read Q19 (s379:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s379` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s379` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AES256_GCM_DEC_ALT_EXEC [380] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(ivtac THEN NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST(map (fun lanes ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lanes] THEN
        REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC)
      [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES;
       GCM_CTR_INC5_LANES; GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES]) THEN NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;

(* The statement of WB_FRONT_BUF.  Its postcondition wb_front_postcond (below)
   is the simulated state s273 at the seam, with the 8 in-flight keystream
   towers folded to aes13; it is built with term builders, so that the front is
   simulated only in the proof. *)

let wb_front_pre_tm = `\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
          read PC s = word (pc + 0x1c) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word (128 * nblk); out_p; tag_p; ivec_p; key_p; htable_p] s /\
          read (memory :> bytes (in_p, 16 * nblk)) s = num_of_bytelist ibytes /\
          read (memory :> bytes128 tag_p) s = xi /\
          read (memory :> bytes128 ivec_p) s = ctr0 /\
          read (memory :> bytes128 key_p) s = k0 /\
          read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
          read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
          read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
          read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
          read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
          read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
          read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
          read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
          read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
          read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
          read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
          read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
          read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
          read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
          htable_mem_dec h htable_p s`;;

(* The band 5 <= nblk <= 8: WB_FRONT_BUF, stated with these hypotheses, is used
   only by prove_band for bands 5..8 (bands 1..4 take the b.le at step 8 to the
   small-message path and are proved by WB_FUSED_1BLOCK .. WB_FUSED_4BLOCK).
   The bands supply nblk = 5..8, so 5 <= nblk closes by NUM_REDUCE_CONV, and
   the union band wbn_front_hyps_uni_tm also starts with 5 <= nblk. *)
let wb_front_hyps_tm = `5 <= nblk /\ nblk <= 8 /\ LENGTH (ibytes:byte list) = 16 * nblk /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc, LENGTH aes256_gcm_dec_alt_tmc) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, LENGTH aes256_gcm_dec_alt_tmc) (out_p:int64, 16 * nblk) /\
    nonoverlapping (word pc, LENGTH aes256_gcm_dec_alt_tmc) (tag_p:int64, 16) /\
    nonoverlapping (word pc, LENGTH aes256_gcm_dec_alt_tmc) (ivec_p:int64, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 16 * nblk) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htable_p:int64, 192) /\
    nonoverlapping (in_p, 16 * nblk) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htable_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (tag_p, 16) (in_p, 16 * nblk) /\
    nonoverlapping (tag_p, 16) (key_p, 240) /\
    nonoverlapping (tag_p, 16) (htable_p, 192) /\
    nonoverlapping (tag_p, 16) (stackpointer, 80)`;;

let wb_front_vars = [`pc:num`;`stackpointer:int64`;`out_p:int64`;`tag_p:int64`;`ivec_p:int64`;
            `in_p:int64`;`key_p:int64`;`htable_p:int64`;`nblk:num`;`ibytes:byte list`;
            `xi:int128`;`ctr0:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;
            `k4:int128`;`k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;
            `k10:int128`;`k11:int128`;`k12:int128`;`k13:int128`;`k14:int128`;`h:int128`];;

let mk_wb_front_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wb_front_hyps_tm, ens));;

(* The simulated postconditions (wb_front_postcond and the others built below)
   state the 8 in-flight keystream towers folded to aes13 (gcm_ctr_inc^i ctr0)
   k0 .. k13, which keeps the Q-register conjuncts readable; wb_front_fold_tac
   applies the same folds, GSYM aes13 and the GSYM of the lane lemmas, to the
   simulated assumptions before the final-state match. *)
let wb_front_fold_tac =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM aes13]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE(map GSYM wb_ctr_lanes_thms));;

(* the keystream tower aes13 ctr k0 .. k13 *)
let wbp_aes13 ctr =
  list_mk_comb(`aes13`, ctr :: map (fun i -> mk_var("k"^string_of_int i,`:int128`)) (0--13));;
(* the round keys k0 .. k14 and the 12 htable_mem_dec slots as memory reads *)
let wbp_key_reads =
  map (fun i -> mk_eq(wbp_mem128 `key_p:int64` i, mk_var("k"^string_of_int i,`:int128`))) (0--14);;
(* the registers the front sets up for the whole kernel (Q19 holds xi
   reversed; Q26, Q27, Q28 hold the round keys k12, k13, k14) *)
let wbp_ctx xi =
  [`read X16 s = ivec_p`;
   `read X10 s = word_add stackpointer (word 64)`;
   `read X15 s = word 4294967296`;
   `read Q31 s = word 79228162514264337593543950336`;
   wbp_rd `Q19` (mk_comb(`word_bytereverse:int128->int128`, xi));
   `read X4 s = word_add in_p (word (16 * nblk))`;
   `read Q27 s = k13`;
   `read Q26 s = k12`;
   `read Q28 s = k14`];;
(* decrypted block i, word_xor (word_xor cph_i (aes13 ctr_i k0 .. k13)) k14,
   and its store *)
let wbp_pt i = mk_comb(mk_comb(`word_xor:int128->int128->int128`,
  mk_comb(mk_comb(`word_xor:int128->int128->int128`, mk_cph i), wbp_aes13 (mk_ctr i))), `k14:int128`);;
let wbp_out i = mk_eq(wbp_mem128 `out_p:int64` i, wbp_pt i);;

let wb_front_postcond = wbp_post
 ([`aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc`;
   `read PC s = word (pc + 3824)`;
   wbp_rd `Q24` (wbp_hmid 7);
   wbp_rd `Q25` (wbp_hpow 8)] @
  wbp_cmpi_flags `word (16 * nblk):int64` 112 @
  [`read Q16 s = word_subword (word_join (word_bytereverse (xi:int128)) (word_bytereverse xi):256 word) (64,128)`;
   wbp_rd `Q7` (wbp_aes13 (mk_ctr 7));
   wbp_rd `Q6` (wbp_aes13 (mk_ctr 6));
   wbp_rd `Q0` (wbp_aes13 (mk_ctr 0));
   wbp_rd `Q1` (wbp_aes13 (mk_ctr 1));
   `read (memory :> bytes64 (word_add stackpointer (word 64))) s = word 13979173243358019584`;
   `read (memory :> bytes64 (word_add stackpointer (word 72))) s = word 0`;
   `read X11 s = key_p`;
   `read X9 s = word (16 * nblk)`;
   `read SP s = stackpointer`;
   `read X1 s = word (128 * nblk)`;
   `read X2 s = out_p`;
   `read X3 s = tag_p`;
   `read X6 s = htable_p`;
   `read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes`;
   `read (memory :> bytes128 tag_p) s = xi`;
   `read (memory :> bytes128 ivec_p) s = ctr0`] @
  wbp_key_reads @ wbp_htable_reads @
  [mk_eq(wbp_mem128 `in_p:int64` 0, mk_cph 0)] @ wbp_ctx `xi:int128` @
  [wbp_rd `Q5` (wbp_aes13 (mk_ctr 5));
   wbp_rd `Q2` (wbp_aes13 (mk_ctr 2));
   wbp_rd `Q4` (wbp_aes13 (mk_ctr 4));
   wbp_rd `Q3` (wbp_aes13 (mk_ctr 3));
   `read X5 s = word (16 * nblk)`;
   `read X0 s = word_add in_p (word 16)`;
   wbp_rd `Q9` (mk_cph 0)]);;

(* The front postcondition also states the advanced raw counter Q30, so that
   the band proofs and the shared back-legs WB_TAIL_GEN2_r, which start from
   it (WB_TAIL_GEN2_r from it less the 5 cells it drops), can close the ivec
   write-back.  The front sets v30 to the reversed counter base + 7 and later
   adds 1, so at the seam s273 (pc+3824, reached when the 0x448 b.ge is taken
   for nblk <= 8) Q30 = gcm_ctr_raw (word 8) ctr0: the simulated top lane is
   word_add (word_add (ctr0 top bytes) (word 7)) (word 1). *)
let wb_front_postcond = mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs wb_front_postcond),
            `read Q30 (s:armstate) = gcm_ctr_raw (word 8) ctr0`));;

let AND_MASK_16NBLK_ANY = prove
 (`!nblk. 1 <= nblk /\ 16 * nblk < 2 EXP 64
        ==> word_and (word_sub (word (16 * nblk)) (word 1))
                     (word 18446744073709551488):int64 =
            word (128 * ((nblk - 1) DIV 8))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word 18446744073709551488:int64 = word_not (word (2 EXP 7 - 1))`
    SUBST1_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD] THEN
  SUBGOAL_THEN `word_sub (word (16 * nblk)) (word 1):int64 = word (16 * nblk - 1)`
    SUBST1_TAC THENL
   [REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (16 * nblk - 1):int64) = 16 * nblk - 1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `(16 * nblk - 1) DIV 2 EXP 7 = (nblk - 1) DIV 8` SUBST1_TAC THENL
   [ALL_TAC; ARITH_TAC] THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d = (nblk - 1) DIV 8` THEN ABBREV_TAC `m = (nblk - 1) MOD 8` THEN
  ASM_ARITH_TAC);;

(* The union band: the hypotheses of the 5..8 band without nblk <= 8, plus
   128 * nblk < 2 EXP 64; the 5..8 band and the >=9 band both imply it.  Its
   consumers (bands 5..8 through WB_FRONT_BUF, and the >=9 chain) all lie on
   the fall-through side of the dispatch b.le; bands 1..4 take the
   small-message path.  GUARD_LE_FALLTHRU needs 5 <= nblk and
   16 * nblk < 2 EXP 63, which follows from 128 * nblk < 2 EXP 64. *)
let wbn_front_hyps_uni_tm =
  let cs8 = conjuncts wb_front_hyps_tm in
  end_itlist (curry mk_conj)
    (`5 <= nblk`::`128 * nblk < 2 EXP 64`::
     (filter (fun c -> not(c = `5 <= nblk` || c = `1 <= nblk` || c = `nblk <= 8`)) cs8));;

let WBN_FRONT_PREP_BUF_UNI_TAC =
  SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 in_p) s0 = bytes_to_int128 (SUB_LIST (0,16) ibytes)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`] INPUT_PREFIX_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
    ANTS_TAC THENL [NBLK_ARITH_UNI_TAC; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)` ASSUME_TAC THENL
   [MATCH_MP_TAC USHR_128NBLK_ANY THEN NBLK_ARITH_UNI_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word_sub (word (16 * nblk)) (word 1)) (word 18446744073709551488):int64 = word (128 * ((nblk - 1) DIV 8))` ASSUME_TAC THENL
   [MATCH_MP_TAC AND_MASK_16NBLK_ANY THEN NBLK_ARITH_UNI_TAC; ALL_TAC];;

let wbn_init_uni_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check(is_conj o concl)) THEN
  WBN_FRONT_PREP_BUF_UNI_TAC;;

(* The shared prefix, steps 1..267 (the entry pc+0x1c to the 0x448 b.ge at
   pc+1096); it stops before the band-dependent 0x448 branch, so that X5 stays
   general.  Step 1 is the entry 0x1c, step 6 the add x10 at 0x30, steps 7, 8
   the dispatch cmp x9,#0x40 ; b.le, and step 9 the first vector instruction,
   the ld1 at 0x3c.  The b.le falls through for the union band nblk >= 5
   (16 * nblk >= 80 > 64): GUARD_LE_FALLTHRU is added to the assumptions
   before steps 7--8, so that the stepper folds the branch.  The counter
   setup (all counter SIMD first, then the AES rounds 0 and 1) is stepped with
   GCM_SIMD_SIMPLIFY_TAC after each of the steps 9--43. *)
let WBN_FRONT_PREBRANCH_STEPS_TAC =
  ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (1--6) THEN
  MP_TAC(SPEC `nblk:num` GUARD_LE_FALLTHRU) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (7--8) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC) (9--43)) THEN
  ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (44--92) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (93--181) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (182--185) THEN
  GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_STALE_Q30_TAC THEN
  (* 186..197: the tag load (ld1/ext/rev64 of v19), whose REV64 byte tree
     ARM_STEPS_FOLD_DISCARD_TAC folds into Q19 before it discards the older
     states at each step; no store readback is needed in this window, so the
     per-step discard is safe *)
  ARM_STEPS_FOLD_DISCARD_TAC AES256_GCM_DEC_ALT_EXEC (186--197) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[Q19_BREVXI]) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (198--262) THEN
  DISCARD_STALE_Q30_TAC THEN GCM_SIMD_SIMPLIFY_TAC THEN
  ARM_VSTEPS_TAC AES256_GCM_DEC_ALT_EXEC [263] THEN
  ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (264--267);;

let WBN_FRONT_PREBRANCH_TAC = wbn_init_uni_tac THEN WBN_FRONT_PREBRANCH_STEPS_TAC;;

(* prefix goal builder: union-band hypotheses, front precondition and frame *)
let mk_wbn_prebranch_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_uni_tm, ens));;

(* The pre-branch postcondition, the s267 state at the 0x448 b.ge, built like
   wb_front_postcond above as the final state of WBN_FRONT_PREBRANCH_TAC THEN
   wb_front_fold_tac.  X5 is the general
   word_add (word (128 * ((nblk - 1) DIV 8))) in_p, and the raw NF/VF/ZF/CF
   facts are kept, so that each consumer's post-branch leg can resolve the
   branch in its band. *)
let wbn_front_prebranch_postcond = wbp_post
 ([`aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc`;
   `read PC s = word (pc + 1096)`;
   wbp_rd `Q7` (wbp_aes13 (mk_ctr 7));
   wbp_rd `Q6` (wbp_aes13 (mk_ctr 6));
   wbp_rd `Q0` (wbp_aes13 (mk_ctr 0));
   wbp_rd `Q1` (wbp_aes13 (mk_ctr 1))] @
  wbp_cmp_flags `in_p:int64` `word_add (word (128 * (nblk - 1) DIV 8)) in_p:int64` @
  [wbp_rd `Q30` (wbp_raw_acc 7);
   `read X5 s = word_add (word (128 * (nblk - 1) DIV 8)) in_p`;
   `read (memory :> bytes64 (word_add stackpointer (word 64))) s = word 13979173243358019584`;
   `read (memory :> bytes64 (word_add stackpointer (word 72))) s = word 0`;
   `read X11 s = key_p`;
   `read X9 s = word (16 * nblk)`;
   `read SP s = stackpointer`;
   `read X0 s = in_p`;
   `read X1 s = word (128 * nblk)`;
   `read X2 s = out_p`;
   `read X3 s = tag_p`;
   `read X6 s = htable_p`;
   `read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes`;
   `read (memory :> bytes128 tag_p) s = xi`;
   `read (memory :> bytes128 ivec_p) s = ctr0`] @
  wbp_key_reads @ wbp_htable_reads @
  [mk_eq(wbp_mem128 `in_p:int64` 0, mk_cph 0)] @ wbp_ctx `xi:int128` @
  [wbp_rd `Q5` (wbp_aes13 (mk_ctr 5));
   wbp_rd `Q2` (wbp_aes13 (mk_ctr 2));
   wbp_rd `Q4` (wbp_aes13 (mk_ctr 4));
   wbp_rd `Q3` (wbp_aes13 (mk_ctr 3))]);;

(* The shared pre-branch prefix lemma. *)
let WBN_FRONT_PREBRANCH = prove(mk_wbn_prebranch_goal wbn_front_prebranch_postcond,
  WBN_FRONT_PREBRANCH_TAC THEN wb_front_fold_tac THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC);;

(* ivec: the front sets v30 to the reversed counter base + 7 and later adds 1,
   so Q30's top lane is word_add(word_add(...)(word 7))(word 1); this folds the
   +7+1 to +8 so the raw tower matches the gcm_ctr_raw (word 8) ctr0 literal.
   A precomputed `let` value: inlining the WORD_RULE in the tactic fails with
   "RAND_CONV: Not a combination". *)
let WB_FRONT_Q30_TOPLANE = WORD_RULE
  `word_add (word_add (x:32 word) (word 7)) (word 1) = word_add x (word 8)`;;

(* The front of bands 5..8: WBN_FRONT_PREBRANCH (0x1c to the 0x448 b.ge),
   chained by ENSURES_TRANS_SIMPLE, then the 0x448 b.ge taken (X5 = in_p for
   nblk <= 8, so the cmp x0,x5 at 0x3fc compares equal) and the tail entry,
   steps 268..273, to the seam s273 at pc+3824.  It is used by prove_band for
   bands 5..8; bands 1..4 take the small-message path. *)
let WB_FRONT_BUF = prove(mk_wb_front_goal wb_front_postcond,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_front_prebranch_postcond THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_PREBRANCH THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ENSURES_INIT_TAC "s267" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `nblk:num` D_ZERO_LE8)
       (CONJ (MATCH_MP (ARITH_RULE `5 <= nblk ==> 1 <= nblk`) (ASSUME `5 <= nblk`))
             (ASSUME `nblk <= 8`))]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
    SUBGOAL_THEN `ival (in_p:int64) - ival in_p = &0` ASSUME_TAC THENL
     [CONV_TAC INT_ARITH; ALL_TAC] THEN
    (* Step 273 (ldp q24,q25,[x6,#160]) needs a per-step normalization that a
       batched ARM_STEPS_TAC defers, which then fails with
       "RAND_CONV: Not a combination", so it is stepped on its own. *)
    ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (268--272) THEN
    ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (273--273) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
      `word_sub (word_add in_p (word (16 * nblk))) in_p:int64 = word (16 * nblk)`]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WB_FRONT_Q30_TOPLANE] THEN REWRITE_TAC[gcm_ctr_raw_def] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC]);;

let mk_out_conj i =
  mk_eq(mk_outp_read i,
    subst [mk_cph i,`ccc:int128`; mk_ctr i,`ttt:int128`]
      `word_xor (ccc:int128) (aes256_encrypt (ttt:int128)
        [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`);;

let mk_band_goal k =
  let n16 = mk_small_numeral(16*k) and n128 = mk_small_numeral(128*k) in
  let hyps = subst [n16,`sss:num`]
    `LENGTH (ibytes:byte list) = sss /\
     aligned 16 stackpointer /\
     nonoverlapping (word pc, LENGTH aes256_gcm_dec_alt_tmc) (stackpointer:int64, 80) /\
     nonoverlapping (word pc, LENGTH aes256_gcm_dec_alt_tmc) (out_p:int64, sss) /\
     nonoverlapping (word pc, LENGTH aes256_gcm_dec_alt_tmc) (tag_p:int64, 16) /\
     nonoverlapping (word pc, LENGTH aes256_gcm_dec_alt_tmc) (ivec_p:int64, 16) /\
     nonoverlapping (out_p, sss) (tag_p, 16) /\
     nonoverlapping (out_p, sss) (ivec_p, 16) /\
     nonoverlapping (tag_p, 16) (ivec_p, 16) /\
     nonoverlapping (ivec_p, 16) (in_p:int64, sss) /\
     nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
     nonoverlapping (ivec_p, 16) (htable_p:int64, 192) /\
     nonoverlapping (in_p, sss) (stackpointer, 80) /\
     nonoverlapping (key_p, 240) (stackpointer, 80) /\
     nonoverlapping (htable_p, 192) (stackpointer, 80) /\
     nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
     nonoverlapping (tag_p, 16) (in_p, sss) /\
     nonoverlapping (tag_p, 16) (key_p, 240) /\
     nonoverlapping (tag_p, 16) (htable_p, 192) /\
     nonoverlapping (tag_p, 16) (stackpointer, 80) /\
     nonoverlapping (out_p, sss) (in_p, sss) /\
     nonoverlapping (out_p, sss) (key_p, 240) /\
     nonoverlapping (out_p, sss) (htable_p, 192) /\
     nonoverlapping (out_p, sss) (stackpointer, 80)` in
  let pre = subst [n16,`sss:num`; n128,`bbb:num`]
    `\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
        read PC s = word (pc + 0x1c) /\ read SP s = stackpointer /\
        C_ARGUMENTS [in_p; word bbb; out_p; tag_p; ivec_p; key_p; htable_p] s /\
        read (memory :> bytes (in_p, sss)) s = num_of_bytelist ibytes /\
        read (memory :> bytes128 tag_p) s = xi /\
        read (memory :> bytes128 ivec_p) s = ctr0 /\
        read (memory :> bytes128 key_p) s = k0 /\
        read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
        read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
        read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
        read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
        read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
        read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
        read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
        read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
        read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
        read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
        read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
        read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
        read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
        read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
        htable_mem_dec h htable_p s` in
  let pc_post = `read PC s = word (pc + 4508)` in
  let x9_post = subst [n16,`sss:num`] `read X9 s = word sss` in
  let outs = map mk_out_conj (0--(k-1)) in
  let xi_post = subst [mk_ghash_list k,`lll:int128 list`]
    `read (memory :> bytes128 tag_p) s =
     word_bytereverse
       (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi) (lll:int128 list))` in
  (* The counter write-back at band exit, in spine form
     gcm_ctr_inc_iter k ctr0 (= gcm_ctr_add (word k) ctr0), closed by
     WB_IVEC_CLOSE_TAC k in WB_TAIL_k_TAC. *)
  let ivec_post = mk_ivec_conj k in
  let post = mk_abs(`s:armstate`,
    end_itlist (curry mk_conj) (pc_post :: x9_post :: outs @ [xi_post; ivec_post])) in
  let frame = subst [n16,`sss:num`]
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(out_p:int64, sss); memory :> bytes(tag_p:int64, 16);
                memory :> bytes(ivec_p:int64, 16);
                memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31]` in
  let ens = subst [pre,`PPP:armstate->bool`; post,`QQQ:armstate->bool`;
                   frame,`CCC:armstate->armstate->bool`] `ensures arm PPP QQQ CCC` in
  let vars = subtract wb_front_vars [`nblk:num`] in
  list_mk_forall(vars, mk_imp(hyps, ens));;

(* front lemma instantiated at nblk:=k, arithmetic normalized *)
let wbf_at k = REWRITE_RULE[arith_16k k; arith_128k k]
  (SPECL [`pc:num`;`stackpointer:int64`;`out_p:int64`;`tag_p:int64`;`ivec_p:int64`;
          `in_p:int64`;`key_p:int64`;`htable_p:int64`; mk_small_numeral k;
          `ibytes:byte list`;`xi:int128`;`ctr0:int128`;`k0:int128`;`k1:int128`;
          `k2:int128`;`k3:int128`;`k4:int128`;`k5:int128`;`k6:int128`;`k7:int128`;
          `k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;`k12:int128`;
          `k13:int128`;`k14:int128`;`h:int128`] WB_FRONT_BUF);;
(* intermediate assertion = WB_FRONT_BUF's postcond @ nblk:=k, normalized *)
let q_at k = rhs(concl(REWRITE_CONV[arith_16k k; arith_128k k]
  (vsubst [mk_small_numeral k,`nblk:num`] wb_front_postcond)));;

(* Back-leg preparation for band k: init at the seam, derive the input lanes
   1..k-1, and abbreviate the cph names and the h powers, so that the band
   tails apply.  The seam state is named s265 here, although WB_FRONT_BUF
   reaches it as s273, and the tail states are numbered on from it. *)
let WB_PREP_TAC k =
  let n16 = mk_small_numeral(16*k) in
  let lanes =
    if k = 1 then ALL_TAC else
    SUBGOAL_THEN (subst [mk_small_numeral k,`kkk:num`]
      `!i. i < kkk ==> read (memory :> bytes128 (word_add in_p (word (16 * i)))) s265 =
              bytes_to_int128 (SUB_LIST (16 * i, 16) (ibytes:byte list))`)
      MP_TAC THENL
    [MATCH_MP_TAC INPUT_PREFIX_TO_BYTE128_LANES THEN
     SUBGOAL_THEN (subst [n16,`sss:num`] `SUB_LIST (0,sss) (ibytes:byte list) = ibytes`)
       (fun th -> ASM_REWRITE_TAC[th; LE_REFL;
          ARITH_RULE(mk_eq(mk_binop `( * ):num->num->num` `16` (mk_small_numeral k), n16))]) THEN
     MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL];
     DISCH_THEN(fun lth ->
       EVERY(map (fun i ->
         ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)
           (MP (SPEC (mk_small_numeral i) lth)
               (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral i) (mk_small_numeral k))))))
         (1--(k-1))))] in
  let cphs =
    if k = 1 then ABBREV_TAC (mk_eq(`cph:int128`, mk_cph 0))
    else EVERY(map (fun i ->
      ABBREV_TAC (mk_eq(mk_var("cph"^string_of_int i,`:int128`), mk_cph i))) (0--(k-1))) in
  let habbrevs = if k = 1 then ALL_TAC else EVERY(map mk_habbrev (2--k)) in
  CLEAR_KEEPGH_MEMO_TAC THEN  (* clear the KEEPGH memo table *)
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN ENSURES_INIT_TAC "s265" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  lanes THEN cphs THEN habbrevs;;

(* ========================================================================= *)
(* The shared per-block back-leg, proved once per residue.                   *)
(*                                                                           *)
(* The back-leg simulation WB_PREP_TAC k THEN WB_TAIL_k_TAC, from the seam   *)
(* pc+3824 to the core exit pc+4508, is proved once per k as WB_TAIL_GEN2_k, *)
(* from a strictly weaker precondition than that of prove_band: q_at k       *)
(* without 5 cells that the tail does not read.  Both goals share the        *)
(* postcondition and the frame of mk_band_goal k, so the weak-precondition   *)
(* back-leg implies the full one by dropping conjuncts                       *)
(* (ENSURES_PRECONDITION_THM, no re-simulation), and WB_TAIL_GEN2_k serves   *)
(* both prove_band (below) and the nblk > 8 recomposition (WBN_PREP_TO_END,  *)
(* further below).                                                           *)
(*                                                                           *)
(* The 5 dropped cells (sp+72, tag_p, ivec_p, in_p block 0, X1) are never    *)
(* read by the tail code, [0xef0,0x119c) and the exact-8 drain               *)
(* [0x11b4,0x1334).  X9 is not read either, but it is kept generically as    *)
(* return_value, so that the theorems record that the byte count reaches the *)
(* mov x0,x9 at the core exit.  Proving WB_TAIL_GEN2_k from the weak         *)
(* precondition checks both facts.                                           *)
(* ========================================================================= *)

(* the band goal split into (vars, hyps, pre, post, frame) *)
let wbn_dissect_band k =
  let g = mk_band_goal k in
  let vars, body = strip_forall g in
  let hyps, ens = dest_imp body in
  let _, args = strip_comb ens in
  (vars, hyps, el 1 args, el 2 args, el 3 args);;

let wbn_weak_q_at5_return k return_value =
  let cs = conjuncts (snd(dest_abs (q_at k))) in
  let kept = filter (fun c -> not (is_eq c && mem (lhs c) wbn_tail_drop_lhs5)) cs in
  wbn_replace_x9 return_value
    (mk_abs(`s:armstate`, end_itlist (curry mk_conj) kept));;
let wbn_weak_q_at5 k = wbn_weak_q_at5_return k (wbn_band_return k);;
let wbn_tail_backleg_goal5_return r =
  let (vars, hyps, pre0, post, frame) = wbn_dissect_band r in
  ignore pre0;
  let return_value = `return_value:int64` in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_weak_q_at5_return r return_value;
     wbn_replace_x9 return_value post;
     frame]) in
  list_mk_forall(vars @ [return_value], mk_imp(hyps, ens));;

(* The 8 shared back-legs.  Their proofs from the weakened precondition show *)
(* that the tail does not read X1 and leaves X9 unchanged.                   *)
let WB_TAIL_GEN2_1 = prove(wbn_tail_backleg_goal5_return 1,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 1 THEN WB_TAIL_1_TAC (WB_IVEC_CLOSE_TAC 1));;
let WB_TAIL_GEN2_2 = prove(wbn_tail_backleg_goal5_return 2,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 2 THEN WB_TAIL_2_TAC (WB_IVEC_CLOSE_TAC 2));;
let WB_TAIL_GEN2_3 = prove(wbn_tail_backleg_goal5_return 3,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 3 THEN WB_TAIL_3_TAC (WB_IVEC_CLOSE_TAC 3));;
let WB_TAIL_GEN2_4 = prove(wbn_tail_backleg_goal5_return 4,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 4 THEN WB_TAIL_4_TAC (WB_IVEC_CLOSE_TAC 4));;
let WB_TAIL_GEN2_5 = prove(wbn_tail_backleg_goal5_return 5,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 5 THEN WB_TAIL_5_TAC (WB_IVEC_CLOSE_TAC 5));;
let WB_TAIL_GEN2_6 = prove(wbn_tail_backleg_goal5_return 6,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 6 THEN WB_TAIL_6_TAC (WB_IVEC_CLOSE_TAC 6));;
let WB_TAIL_GEN2_7 = prove(wbn_tail_backleg_goal5_return 7,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 7 THEN WB_TAIL_7_TAC (WB_IVEC_CLOSE_TAC 7));;
let WB_TAIL_GEN2_8 = prove(wbn_tail_backleg_goal5_return 8,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 8 THEN WB_TAIL_8_TAC (WB_IVEC_CLOSE_TAC 8));;

let GCM_SIMD_SIMPLIFY_CORE_QSCOPED_TAC =
  GCM_SIMD_SIMPLIFY_MEMO_TAC gcm_simd_fixpt_tbl;;

(* DISCARD_STALE_TAC, used by the stepper below, is the shared one in
   arm/proofs/utils/aes_gcm_common.ml. *)

(* The small-path stepper, one step at a time over the range:
   ARM_VERBOSE_STEP_TAC, one pass of the Q-scoped normalizer (a second pass
   would only fold the block-boundary REV64 trees, which the bridge folds
   anyway by RF8_SUBWORD), the KEEPGHALL discard, DISCARD_STALE_TAC and
   CLARIFY_TAC. *)
let ARM_STEPS_FOLD_KEEPGHALL_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_CORE_QSCOPED_TAC THEN
              DISCARD_OLDSTATE_KEEPGHALL_TAC s THEN DISCARD_STALE_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;

let DEC_BRIDGE_ROUTEB_TAC sN spec_eq (lo_triple,hi_triple,mid_triple) : tactic =
  fun (asl,w) ->
  let q19asm = snd(List.find(fun(_,th)->
    try lhs(concl th)=parse_term(Printf.sprintf "read Q19 s%d" sN) with _->false) asl) in
  (GEN_REWRITE_TAC LAND_CONV [q19asm] THEN
   GEN_REWRITE_TAC RAND_CONV [spec_eq] THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   bridge_qq_land lo_triple THEN
   bridge_qq_land hi_triple THEN
   bridge_qq_mid mid_triple THEN
   REWRITE_TAC[WORD_SUBWORD_XOR] THEN
   WA_UNIFY_TAC THEN WV_UNIFY_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_TAC)
  (asl,w);;

(* ---- nblk = 1 ---- *)

(* The k = 1 bridge.  After one block the tag is polyval_dot (xi XOR cph) H
   (GHASH_1BLOCK_CORRECT), which GMULT_FULL_CORRECT_BA states in the byte
   form of the machine; the machine instead multiplies the seed Xi' and the
   block by H separately and XORs the products.  FOLD_LO/FOLD_HI and
   FOLD_LO_N/FOLD_HI_N (two spellings of a reversed lane) fold such a pair of
   64-bit products into the product of the XOR, FOLD_MID and FOLD_MID2 the
   two middle products, and BRIDGE_CLOSE_FULL_TAC closes the rest with
   FINISH_WV_LANE_TAC. *)
let FOLD_LO = prove(
  `word_xor (word_pmul (word_subword (word_reversefields 8 (cph:int128)) (64,64):64 word)
                       (word_subword (h:int128) (0,64):64 word))
            (word_pmul (word_reversefields 8 (word_subword (xi:int128) (0,64):64 word))
                       (word_subword h (0,64):64 word)) : int128
   = word_pmul (word_subword h (0,64):64 word)
       (word_xor (word_reversefields 8 (word_subword xi (0,64):64 word))
                 (word_reversefields 8 (word_subword cph (0,64):64 word)))`,
  REWRITE_TAC[RF8_SUBWORD] THEN
  GEN_REWRITE_TAC RAND_CONV [CONJUNCT2 WORD_PMUL_XOR] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  REWRITE_TAC[WORD_XOR_ACI]);;
let FOLD_HI = prove(
  `word_xor (word_pmul (word_subword (word_reversefields 8 (cph:int128)) (0,64):64 word)
                       (word_subword (h:int128) (64,64):64 word))
            (word_pmul (word_reversefields 8 (word_subword (xi:int128) (64,64):64 word))
                       (word_subword h (64,64):64 word)) : int128
   = word_pmul (word_subword h (64,64):64 word)
       (word_xor (word_reversefields 8 (word_subword xi (64,64):64 word))
                 (word_reversefields 8 (word_subword cph (64,64):64 word)))`,
  REWRITE_TAC[RF8_SUBWORD] THEN
  GEN_REWRITE_TAC RAND_CONV [CONJUNCT2 WORD_PMUL_XOR] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  REWRITE_TAC[WORD_XOR_ACI]);;
let FOLD_LO_N = prove(
  `word_xor (word_pmul (word_reversefields 8 (word_subword (cph:int128) (0,64):64 word))
                       (word_subword (h:int128) (0,64):64 word))
            (word_pmul (word_reversefields 8 (word_subword (xi:int128) (0,64):64 word))
                       (word_subword h (0,64):64 word)) : int128
   = word_pmul (word_subword h (0,64):64 word)
       (word_xor (word_reversefields 8 (word_subword xi (0,64):64 word))
                 (word_reversefields 8 (word_subword cph (0,64):64 word)))`,
  GEN_REWRITE_TAC RAND_CONV [CONJUNCT2 WORD_PMUL_XOR] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  REWRITE_TAC[WORD_XOR_ACI]);;
let FOLD_HI_N = prove(
  `word_xor (word_pmul (word_reversefields 8 (word_subword (cph:int128) (64,64):64 word))
                       (word_subword (h:int128) (64,64):64 word))
            (word_pmul (word_reversefields 8 (word_subword (xi:int128) (64,64):64 word))
                       (word_subword h (64,64):64 word)) : int128
   = word_pmul (word_subword h (64,64):64 word)
       (word_xor (word_reversefields 8 (word_subword xi (64,64):64 word))
                 (word_reversefields 8 (word_subword cph (64,64):64 word)))`,
  GEN_REWRITE_TAC RAND_CONV [CONJUNCT2 WORD_PMUL_XOR] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  REWRITE_TAC[WORD_XOR_ACI]);;
let FOLD_MID = prove(
  `word_xor
    (word_pmul
      (word_subword
        (word_xor
          (word_subword (word_join (word_reversefields 8 (cph:int128)) (word_reversefields 8 cph):256 word) (64,128):128 word)
          (word_reversefields 8 cph)) (0,64):64 word)
      (word_xor (word_subword (h:int128) (0,64):64 word) (word_subword h (64,64):64 word)))
    (word_pmul
      (word_subword
        (word_xor
          (word_subword
            (word_join
              (word_join (word_reversefields 8 (word_subword (xi:int128) (0,64):64 word))
                         (word_reversefields 8 (word_subword xi (64,64):64 word)):128 word)
              (word_join (word_reversefields 8 (word_subword xi (0,64):64 word))
                         (word_reversefields 8 (word_subword xi (64,64):64 word)):128 word):256 word)
            (64,128):128 word)
          (word_join (word_reversefields 8 (word_subword xi (0,64):64 word))
                     (word_reversefields 8 (word_subword xi (64,64):64 word)):128 word)) (0,64):64 word)
      (word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word))) : int128
   = word_pmul (word_xor (word_subword h (64,64):64 word) (word_subword h (0,64):64 word))
       (word_xor
         (word_xor (word_reversefields 8 (word_subword xi (64,64):64 word))
                   (word_reversefields 8 (word_subword cph (64,64):64 word)))
         (word_xor (word_reversefields 8 (word_subword xi (0,64):64 word))
                   (word_reversefields 8 (word_subword cph (0,64):64 word))))`,
  REWRITE_TAC[JOINMID; JOIN_SUBWORD_RULES; WORD_SUBWORD_SUBWORD; RF8_SUBWORD] THEN
  REWRITE_TAC[SUBWORD_XOR_JOIN_DIST; JOIN_SUBWORD_RULES; WORD_SUBWORD_SUBWORD; RF8_SUBWORD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM (CONJUNCT1 WORD_PMUL_XOR)] THEN
  GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
  MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(* FINISH_WV_LANE_TAC: the lane-split close of the k = 1 bridge, of the same
   shape as the close of the k >= 2 bridges (JOIN_EQ_SPLIT, then
   LANE_FINISH_TAC): if two word_pmul terms remain, prove them equal
   (PMUL_CONG_128 on their operands), then split the 128-bit equality into
   its two 64-bit lanes (QQ0SPLIT, JOIN_EQ_SPLIT) and blast each lane.  One
   128-bit WORD_BLAST of the whole goal would be much slower. *)
let FINISH_WV_LANE_TAC : tactic = fun (asl,w) ->
  let is_pmul_app t =
    try let (h,a) = strip_comb t in fst(dest_const h) = "word_pmul" && length a = 2
    with _ -> false in
  ((match setify(find_terms is_pmul_app w) with
    | [p0;p1] ->
       SUBGOAL_THEN (mk_eq(p0,p1)) (fun th -> REWRITE_TAC[th]) THENL
        [MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC]
    | _ -> ALL_TAC) THEN
   GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [QQ0SPLIT] THEN
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN CONV_TAC WORD_BLAST) (asl,w);;

let BRIDGE_CLOSE_FULL_TAC =
  GEN_REWRITE_TAC RAND_CONV
    [GSYM(REWRITE_RULE[LET_DEF; LET_END_DEF]
       (ISPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph) : int128`;
         `byteswap128 h:int128`] GMULT_FULL_CORRECT_BA))] THEN
  REWRITE_TAC[byteswap128] THEN
  REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
  REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
  REWRITE_TAC[GSYM (CONJUNCT1 SUBWORD_XOR_JOIN_DIST); GSYM (CONJUNCT2 SUBWORD_XOR_JOIN_DIST)] THEN
  REWRITE_TAC[FOLD_LO; FOLD_HI; FOLD_MID; FOLD_LO_N; FOLD_HI_N] THEN
  ABBREV_INNER_PMULS_TAC THEN
  SUBGOAL_THEN `word_xor (qq4:int128) qq3 = qq2` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["qq2";"qq3";"qq4"] THEN ACCEPT_TAC FOLD_MID2; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `word_xor (qq4:int128) qq3 = qq2` then REWRITE_TAC[th] else NO_TAC) THEN
  ABBREV_INNER_PMULS_TAC THEN
  FINISH_WV_LANE_TAC;;

(* WB_FUSED_1BLOCK, nblk = 1: 97 steps from the core entry pc+0x1c to the
   core exit pc+4508.  s1-s8 the front and the dispatch (the b.le at s8 is
   taken), s9-s29 L256_dec_small (the counter, tag and round-key loads and
   the x9 compares), s30-s37 L256_dec_small_seed_1 (the seed Xi' * H),
   s38-s96 L256_dec_small_blk_1 (the AES-256 tower, the reduced GHASH at
   s84, ext and rev64 at s87 and s88, the tag store at s91, the counter store
   at s94, the plaintext eor3 at s95 and its store at s96), s97 the b at
   L256_dec_small_done.  The KEEPGHALL stepper runs from the first seed
   product (s34) to the reduce, where BRIDGE_CLOSE_FULL_TAC proves Q19 to be
   the one-block GHASH (gval). *)
let WB_FUSED_1BLOCK = prove(
 `!pc stackpointer out_p tag_p ivec_p in_p key_p htable_p
    cph xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 5908) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 5908) (out_p:int64, 16) /\
    nonoverlapping (word pc, 5908) (tag_p:int64, 16) /\
    nonoverlapping (word pc, 5908) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 16) (tag_p, 16) /\
    nonoverlapping (out_p, 16) (ivec_p, 16) /\
    nonoverlapping (tag_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 16) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htable_p:int64, 192) /\
    nonoverlapping (in_p, 16) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htable_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (tag_p, 16) (in_p, 16) /\
    nonoverlapping (tag_p, 16) (key_p, 240) /\
    nonoverlapping (tag_p, 16) (htable_p, 192) /\
    nonoverlapping (tag_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 16) (in_p, 16) /\
    nonoverlapping (out_p, 16) (key_p, 240) /\
    nonoverlapping (out_p, 16) (htable_p, 192) /\
    nonoverlapping (out_p, 16) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
          read PC s = word (pc + 0x1c) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word 128; out_p; tag_p; ivec_p; key_p; htable_p] s /\
          read (memory :> bytes128 in_p) s = cph /\
          read (memory :> bytes128 tag_p) s = xi /\
          read (memory :> bytes128 ivec_p) s = ctr0 /\
          read (memory :> bytes128 key_p) s = k0 /\
          read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
          read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
          read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
          read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
          read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
          read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
          read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
          read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
          read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
          read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
          read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
          read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
          read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
          read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
          read (memory :> bytes128 htable_p) s = h /\
          read (memory :> bytes128 (word_add htable_p (word 16))) s = hk)
     (\s. read PC s = word (pc + 0x119c) /\
          read X9 s = word 16 /\
          read (memory :> bytes128 out_p) s =
          word_xor cph (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 tag_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph]) /\
          read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 1 ctr0)
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 16); memory :> bytes(tag_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  CLEAR_KEEPGHALL_MEMO_TAC THEN  (* empty the normalizer fixpoint table *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htable_p (word 16))) s0`
        with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN
          STRIP_TAC)
    else NO_TAC) THEN
  ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (1--33) THEN
  ARM_STEPS_FOLD_KEEPGHALL_TAC AES256_GCM_DEC_ALT_EXEC (34--84) THEN
  (fun (asl,w) ->
     let picks = mapfilter (fun (_,th) ->
       match concl th with
       | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),st)),_)
           when (match st with Var(n,_)->n<>"s84"|_->false) -> th
       | _ -> fail()) asl in
     RULE_ASSUM_TAC(fun th ->
       if (try lhs(concl th) = `read Q19 s84` with _ -> false)
       then REWRITE_RULE picks th else th) (asl,w)) THEN
  DISCARD_OLDSTATE_TAC "s84" THEN
  SUBGOAL_THEN
    `read Q19 (s84:armstate) =
     polyval_dot (word_xor (word_bytereverse xi) (word_bytereverse cph))
       (byteswap128 h)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s84`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s84` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   BRIDGE_CLOSE_FULL_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = polyval_dot (word_xor (word_bytereverse xi)
    (word_bytereverse cph)) (byteswap128 h)` THEN
  ARM_STEPS_FOLD_DISCARD_TAC AES256_GCM_DEC_ALT_EXEC (85--88) THEN
  SUBGOAL_THEN `read Q19 (s88:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s88`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s88` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_STEPS_FOLD_DISCARD_TAC AES256_GCM_DEC_ALT_EXEC (89--97) THEN
  (* Split the three 128-bit store readbacks at s97 (out, xi, ivec) into
     their 64-bit halves, the form of the goals ENSURES_FINAL_STATE_TAC
     leaves for them. *)
  RULE_ASSUM_TAC(fun th ->
    match concl th with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
        Comb(Comb(Const(":>",_),Const("memory",_)),
             Comb(Const("bytes128",_),_))),st)),_)
        when (try fst(dest_var st)="s97" with _ -> false) ->
        (try CONV_RULE(READ_MEMORY_SPLIT_CONV 1) th with _ -> th)
    | _ -> th) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  ENSURES_FINAL_STATE_TAC THEN
  (* Close each remaining conjunct by the closer of its kind. *)
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  (* xi half: gval by its definition, then GHASH_1BLOCK_CORRECT *)
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (fun th -> try rhs(concl th) = `gval:int128` &&
                             (match lhs(concl th) with
                              | Comb(Comb(Const("polyval_dot",_),_),_) -> true | _ -> false)
                         with _ -> false)) THEN
      REWRITE_TAC[GHASH_1BLOCK_CORRECT] THEN NO_TAC) THEN
  (* ivec half *)
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[num_CONV `1`; gcm_ctr_inc_iter; GCM_CTR_INC_LANES] THEN NO_TAC) THEN
  (* out half *)
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[JOIN_IS_CTR0] THEN
      REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
      REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  (* MAYCHANGE frame *)
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC));;

(* BRIDGE_CLOSE_2_CPH1_TAC sN: the nblk = 2 bridge at the reduce state sN,
   by DEC_BRIDGE_ROUTEB_TAC with spec_eq from spec_to_byteform_2 and
   GMULT2_FULL_CORRECT_BA at dec_bridge_specl_2_cph1.  The identities of
   block 0's products with H^2: qq8 = qq1 XOR qq5 and qq7 = qq0 XOR qq4
   (outer), qq12 = qq9 XOR qq10 (middle). *)
let BRIDGE_CLOSE_2_CPH1_TAC sN : tactic = fun (asl,w) ->
  let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
  let gmult_dec = REWRITE_RULE[LET_DEF;LET_END_DEF] (SPECL dec_bridge_specl_2_cph1 GMULT2_FULL_CORRECT_BA) in
  let spec_eq = TRANS (MP spec_to_byteform_2 h2asm) (GSYM gmult_dec) in
  DEC_BRIDGE_ROUTEB_TAC sN spec_eq
    (("qq8","qq1","qq5"),("qq7","qq0","qq4"),("qq12","qq9","qq10")) (asl,w);;

(* WB_FUSED_2BLOCK, nblk = 2: 141 steps.  s1-s8 the front and the dispatch,
   s9-s30 L256_dec_small, s31-s38 L256_dec_small_seed_2 (the seed Xi' * H^2),
   s39-s81 small_blk_2 (block 0, folded with H^2, stored at s81), s82-s140
   small_blk_1 (block 1, the reduce at s128, ext and rev64 at s131 and s132,
   then the tag, counter and block-1 stores) and s141 the b at
   L256_dec_small_done.  Two details of the simulation:
   (1) the hk read (htable_p+16) is split into its 64-bit halves, and the
       address of the high half, htable_p+16+8, is normalized to htable_p+24, the
       address of the ldr d25,[x6,#24] that loads the Karatsuba mid of H^2;
       otherwise that load is not resolved and the discard drops the Q18
       accumulator that depends on it (nblk = 1 has no such load);
   (2) Q17-Q19 are made self-contained at the block-0 store s81
       (INLINE_SELFCONTAINED) before the discard, so that the accumulator
       chain of block 0 survives it.
   BRIDGE_CLOSE_2_CPH1_TAC closes Q19 at the reduce s128. *)
let WB_FUSED_2BLOCK = prove(
 `!pc stackpointer out_p tag_p ivec_p in_p key_p htable_p
    cph0 cph1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 5908) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 5908) (out_p:int64, 32) /\
    nonoverlapping (word pc, 5908) (tag_p:int64, 16) /\
    nonoverlapping (word pc, 5908) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 32) (tag_p, 16) /\
    nonoverlapping (out_p, 32) (ivec_p, 16) /\
    nonoverlapping (tag_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 32) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htable_p:int64, 192) /\
    nonoverlapping (in_p, 32) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htable_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (tag_p, 16) (in_p, 32) /\
    nonoverlapping (tag_p, 16) (key_p, 240) /\
    nonoverlapping (tag_p, 16) (htable_p, 192) /\
    nonoverlapping (tag_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 32) (in_p, 32) /\
    nonoverlapping (out_p, 32) (key_p, 240) /\
    nonoverlapping (out_p, 32) (htable_p, 192) /\
    nonoverlapping (out_p, 32) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word) /\
    word_subword hk (64,64) :64 word =
      word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64):64 word) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
          read PC s = word (pc + 0x1c) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word 256; out_p; tag_p; ivec_p; key_p; htable_p] s /\
          read (memory :> bytes128 in_p) s = cph0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
          read (memory :> bytes128 tag_p) s = xi /\
          read (memory :> bytes128 ivec_p) s = ctr0 /\
          read (memory :> bytes128 key_p) s = k0 /\
          read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
          read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
          read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
          read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
          read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
          read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
          read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
          read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
          read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
          read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
          read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
          read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
          read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
          read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
          read (memory :> bytes128 htable_p) s = h /\
          read (memory :> bytes128 (word_add htable_p (word 16))) s = hk /\
          read (memory :> bytes128 (word_add htable_p (word 32))) s = h2)
     (\s. read PC s = word (pc + 0x119c) /\
          read X9 s = word 32 /\
          read (memory :> bytes128 out_p) s =
          word_xor cph0 (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 16))) s =
          word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0)
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 tag_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph0; word_bytereverse cph1]) /\
          read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 2 ctr0)
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 32); memory :> bytes(tag_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  CLEAR_KEEPGHALL_MEMO_TAC THEN  (* empty the normalizer fixpoint table *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htable_p (word 16))) s0`
        with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN
          STRIP_TAC)
    else NO_TAC) THEN
  (* detail (1): htable_p+16+8 = htable_p+24 *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (htable_p:int64) (word 16)) (word 8) = word_add htable_p (word 24)`]) THEN
  ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (1--30) THEN
  ARM_STEPS_FOLD_KEEPGHALL_TAC AES256_GCM_DEC_ALT_EXEC (31--81) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 out_p) (s81:armstate) =
     word_xor cph0 (aes256_encrypt ctr0
       [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN REWRITE_TAC[JOIN_IS_CTR0] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  (* detail (2): Q17-Q19 self-contained at s81 *)
  INLINE_SELFCONTAINED "Q17" "s81" 24 THEN
  INLINE_SELFCONTAINED "Q18" "s81" 24 THEN
  INLINE_SELFCONTAINED "Q19" "s81" 24 THEN
  DISCARD_OLDSTATE_TAC "s81" THEN
  ARM_STEPS_FOLD_KEEPGHALL_TAC AES256_GCM_DEC_ALT_EXEC (82--128) THEN
  INLINE_SELFCONTAINED "Q19" "s128" 8 THEN
  DISCARD_OLDSTATE_TAC "s128" THEN
  SUBGOAL_THEN
    `read Q19 (s128:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s128` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [BRIDGE_CLOSE_2_CPH1_TAC 128;   (* the bridge at the reduce *)
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1]` THEN
  ARM_STEPS_FOLD_DISCARD_TAC AES256_GCM_DEC_ALT_EXEC (129--132) THEN
  SUBGOAL_THEN `read Q19 (s132:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s132` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s132` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_STEPS_FOLD_DISCARD_TAC AES256_GCM_DEC_ALT_EXEC (133--141) THEN
  RULE_ASSUM_TAC(fun th ->
    match concl th with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
        Comb(Comb(Const(":>",_),Const("memory",_)),
             Comb(Const("bytes128",_),_))),st)),_)
        when (try fst(dest_var st)="s141" with _ -> false) ->
        (try CONV_RULE(READ_MEMORY_SPLIT_CONV 1) th with _ -> th)
    | _ -> th) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  (* Normalize out_p+16+8 to out_p+24, so that the split readback of the high
     half of block 1 matches the address of its goal (as for the hk load). *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (out_p:int64) (word 16)) (word 8) = word_add out_p (word 24)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_RULE
    `word_add (word_add (out_p:int64) (word 16)) (word 8) = word_add out_p (word 24)`] THEN
  REPEAT CONJ_TAC THEN
  (* xi half: gval by its definition *)
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (fun th -> try rhs(concl th) = `gval:int128` &&
                             (match lhs(concl th) with
                              | Comb(Comb(Const("ghash_polyval_acc",_),_),_) -> true | _ -> false)
                         with _ -> false)) THEN
      REFL_TAC THEN NO_TAC) THEN
  (* ivec half: gcm_ctr_inc_iter 2 ctr0 = gcm_ctr_inc (gcm_ctr_inc ctr0), whose
     lane form (GCM_CTR_INC2_LANES) is the term the machine computes *)
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `gcm_ctr_inc_iter 2 ctr0 = gcm_ctr_inc (gcm_ctr_inc ctr0)`
        SUBST1_TAC THENL
       [REWRITE_TAC[num_CONV `2`; num_CONV `1`; gcm_ctr_inc_iter]; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GCM_CTR_INC2_LANES] THEN
      REFL_TAC THEN NO_TAC) THEN
  (* out block 0, both halves: JOIN_IS_CTR0, then the AES-256 rounds *)
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[JOIN_IS_CTR0] THEN
      REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
      REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  (* out block 1 (out_p+16): the counter in its lane form (GCM_CTR_INC_LANES),
     then the AES-256 rounds; WORD_BLAST where WORD_RULE fails *)
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
      REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
      REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[aese; aesmc] THEN (CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST) THEN NO_TAC) THEN
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC));;

(* ---- nblk = 3 ---- *)

(* The frame lemma for nblk = 3.  SUBSUMED_MAYCHANGE_TAC on the frame the
   simulation accumulates is impractical in the context the simulation
   leaves, so the subsumption by the goal frame is proved here as a lemma,
   before the simulation, and applied at the MAYCHANGE goal through
   WB3_FRAME_IMP.  Pure frame algebra. *)
let WB3_FRAME_SUBSUMED = prove(
 `(MAYCHANGE [PC] ,, MAYCHANGE [X9] ,, MAYCHANGE [X16] ,, MAYCHANGE [X11] ,,
   MAYCHANGE [X5] ,, MAYCHANGE [memory :> bytes64 (word_add stackpointer (word 64))] ,,
   MAYCHANGE [memory :> bytes64 (word_add stackpointer (word 72))] ,, MAYCHANGE [events] ,,
   MAYCHANGE [X10] ,, MAYCHANGE [NF] ,, MAYCHANGE [ZF] ,, MAYCHANGE [CF] ,, MAYCHANGE [VF] ,,
   MAYCHANGE [Q30] ,, MAYCHANGE [Q19] ,, MAYCHANGE [X15] ,, MAYCHANGE [Q31] ,, MAYCHANGE [Q16] ,,
   MAYCHANGE [Q29] ,, MAYCHANGE [Q1] ,, MAYCHANGE [Q2] ,, MAYCHANGE [Q3] ,, MAYCHANGE [Q4] ,,
   MAYCHANGE [Q5] ,, MAYCHANGE [Q6] ,, MAYCHANGE [Q7] ,, MAYCHANGE [Q8] ,, MAYCHANGE [Q9] ,,
   MAYCHANGE [Q10] ,, MAYCHANGE [Q11] ,, MAYCHANGE [Q12] ,, MAYCHANGE [Q13] ,, MAYCHANGE [Q14] ,,
   MAYCHANGE [Q15] ,, MAYCHANGE [Q24] ,, MAYCHANGE [Q25] ,, MAYCHANGE [Q21] ,, MAYCHANGE [Q17] ,,
   MAYCHANGE [Q18] ,, MAYCHANGE [Q26] ,, MAYCHANGE [X0] ,, MAYCHANGE [Q0] ,, MAYCHANGE [Q20] ,,
   MAYCHANGE [Q22] ,, MAYCHANGE [Q23] ,, MAYCHANGE [memory :> bytes128 out_p] ,, MAYCHANGE [X2] ,,
   MAYCHANGE [memory :> bytes128 (word_add out_p (word 16))] ,, MAYCHANGE [memory :> bytes128 tag_p] ,,
   MAYCHANGE [memory :> bytes128 ivec_p] ,,
   MAYCHANGE [memory :> bytes128 (word_add out_p (word 32))]
   :armstate->armstate->bool) subsumed
  (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
   MAYCHANGE [memory :> bytes(out_p:int64, 48); memory :> bytes(tag_p:int64,16);
              memory :> bytes(ivec_p:int64,16);
              memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
   MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
              Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC);;

(* The subsumption as an implication between the two frames at the initial
   and final states s0 and s183 (REWRITE_RULE[subsumed], then SPECL).  Its
   right side is the goal frame applied directly, with no eta-redex, so the
   MAYCHANGE goal closes by one MATCH_MP and ACCEPT_TAC, without an ETA_AX
   rewrite in the large context the simulation leaves. *)
let WB3_FRAME_IMP =
  SPECL [`s0:armstate`; `s183:armstate`] (REWRITE_RULE[subsumed] WB3_FRAME_SUBSUMED);;

(* BRIDGE_CLOSE_3_CPH2_TAC sN: the nblk = 3 bridge, as for nblk = 2, with
   spec_to_byteform_wb3 and GMULT3_FULL_CORRECT_BA at dec_bridge_specl_3_cph2.
   The identities of block 0's products with H^3: qq11 = qq1 XOR qq7 and
   qq10 = qq0 XOR qq6 (outer), qq16 = qq12 XOR qq13 (middle). *)
let BRIDGE_CLOSE_3_CPH2_TAC sN : tactic = fun (asl,w) ->
  let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
  let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
  let gmult_dec = REWRITE_RULE[LET_DEF;LET_END_DEF] (SPECL dec_bridge_specl_3_cph2 GMULT3_FULL_CORRECT_BA) in
  let spec_eq = TRANS (MP spec_to_byteform_wb3 (CONJ h2asm h3asm)) (GSYM gmult_dec) in
  DEC_BRIDGE_ROUTEB_TAC sN spec_eq
    (("qq11","qq1","qq7"),("qq10","qq0","qq6"),("qq16","qq12","qq13")) (asl,w);;

(* WB_FUSED_3BLOCK, nblk = 3: 183 steps.  s1-s8 the front and the dispatch,
   s9-s29 L256_dec_small and L256_dec_small_ge3, s30-s37
   L256_dec_small_seed_3 (the seed Xi' * H^3), s38-s80 small_blk_3 (block 0,
   stored at s80), s81-s123 small_blk_2 (block 1, stored at s123), s124-s182
   small_blk_1 (block 2, the reduce at s170, ext and rev64 at s173 and s174,
   the tag store at s177, the counter store at s180, the block-2 store at
   s182) and s183 the b at L256_dec_small_done.
   The table reads hk (htable_p+16) and h3k (htable_p+64) are split into their
   64-bit halves, which hold the Karatsuba mids the blocks load: of H at +16,
   of H^2 at +24, of H^3 at +64.  The simulation runs in windows that end at
   the block stores s80 and s123, where the block just stored is captured,
   and at the reduce s170; at each cut the accumulators are made
   self-contained, so that the older states can be discarded.
   BRIDGE_CLOSE_3_CPH2_TAC closes Q19 at s170, and the frame closes by
   WB3_FRAME_IMP. *)
let WB_FUSED_3BLOCK = prove(
 `!pc stackpointer out_p tag_p ivec_p in_p key_p htable_p
    cph0 cph1 cph2 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 h3 h3k.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 5908) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 5908) (out_p:int64, 48) /\
    nonoverlapping (word pc, 5908) (tag_p:int64, 16) /\
    nonoverlapping (word pc, 5908) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 48) (tag_p, 16) /\
    nonoverlapping (out_p, 48) (ivec_p, 16) /\
    nonoverlapping (tag_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 48) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htable_p:int64, 192) /\
    nonoverlapping (in_p, 48) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htable_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (tag_p, 16) (in_p, 48) /\
    nonoverlapping (tag_p, 16) (key_p, 240) /\
    nonoverlapping (tag_p, 16) (htable_p, 192) /\
    nonoverlapping (tag_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 48) (in_p, 48) /\
    nonoverlapping (out_p, 48) (key_p, 240) /\
    nonoverlapping (out_p, 48) (htable_p, 192) /\
    nonoverlapping (out_p, 48) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word) /\
    word_subword hk (64,64) :64 word =
      word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64):64 word) /\
    word_subword h3k (0,64) :64 word =
      word_xor (word_subword h3 (0,64):64 word) (word_subword h3 (64,64):64 word) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
    byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
          read PC s = word (pc + 0x1c) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word 384; out_p; tag_p; ivec_p; key_p; htable_p] s /\
          read (memory :> bytes128 in_p) s = cph0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
          read (memory :> bytes128 (word_add in_p (word 32))) s = cph2 /\
          read (memory :> bytes128 tag_p) s = xi /\
          read (memory :> bytes128 ivec_p) s = ctr0 /\
          read (memory :> bytes128 key_p) s = k0 /\
          read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
          read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
          read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
          read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
          read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
          read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
          read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
          read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
          read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
          read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
          read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
          read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
          read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
          read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
          read (memory :> bytes128 htable_p) s = h /\
          read (memory :> bytes128 (word_add htable_p (word 16))) s = hk /\
          read (memory :> bytes128 (word_add htable_p (word 32))) s = h2 /\
          read (memory :> bytes128 (word_add htable_p (word 48))) s = h3 /\
          read (memory :> bytes128 (word_add htable_p (word 64))) s = h3k)
     (\s. read PC s = word (pc + 0x119c) /\
          read X9 s = word 48 /\
          read (memory :> bytes128 out_p) s =
          word_xor cph0 (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 16))) s =
          word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0)
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 32))) s =
          word_xor cph2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0))
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 tag_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]) /\
          read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 3 ctr0)
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 48); memory :> bytes(tag_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  CLEAR_KEEPGHALL_MEMO_TAC THEN  (* empty the normalizer fixpoint table *)
  (* split hk at htable_p+16: the Karatsuba mids of H (low) and H^2 (high) *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htable_p (word 16))) s0`
        with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN
          STRIP_TAC)
    else NO_TAC) THEN
  (* split h3k at htable_p+64: the Karatsuba mid of H^3 (low) *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htable_p (word 64))) s0`
        with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN
          STRIP_TAC)
    else NO_TAC) THEN
  (* htable_p+16+8 = htable_p+24, the address of the ldr d25,[x6,#24] *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (htable_p:int64) (word 16)) (word 8) = word_add htable_p (word 24)`]) THEN
  ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (1--30) THEN
  (* the seed and block 0 (H^3), steps 31-80; block 0 is stored at s80 *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AES256_GCM_DEC_ALT_EXEC (31--80) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 out_p) (s80:armstate) =
     word_xor cph0 (aes256_encrypt ctr0
       [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN REWRITE_TAC[JOIN_IS_CTR0] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  INLINE_SELFCONTAINED "Q17" "s80" 30 THEN
  INLINE_SELFCONTAINED "Q18" "s80" 30 THEN
  INLINE_SELFCONTAINED "Q19" "s80" 30 THEN
  DISCARD_OLDSTATE_TAC "s80" THEN
  (* block 1 (H^2), steps 81-123, stored at s123; capture its plaintext
     (counter gcm_ctr_inc ctr0) before the discard *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AES256_GCM_DEC_ALT_EXEC (81--123) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 (word_add out_p (word 16))) (s123:armstate) =
     word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0)
       [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[aese; aesmc] THEN (CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST);
   ALL_TAC] THEN
  INLINE_SELFCONTAINED "Q17" "s123" 40 THEN
  INLINE_SELFCONTAINED "Q18" "s123" 40 THEN
  INLINE_SELFCONTAINED "Q19" "s123" 40 THEN
  DISCARD_OLDSTATE_TAC "s123" THEN
  (* block 2 (H) and the reduce, steps 124-170; the bridge at s170 *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AES256_GCM_DEC_ALT_EXEC (124--170) THEN
  INLINE_SELFCONTAINED "Q19" "s170" 12 THEN
  DISCARD_OLDSTATE_TAC "s170" THEN
  SUBGOAL_THEN
    `read Q19 (s170:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s170` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [BRIDGE_CLOSE_3_CPH2_TAC 170;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]` THEN
  (* ext and rev64 of v19 (s173, s174): Q19 = word_bytereverse gval *)
  ARM_STEPS_FOLD_DISCARD_TAC AES256_GCM_DEC_ALT_EXEC (171--174) THEN
  SUBGOAL_THEN `read Q19 (s174:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s174` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s174` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_STEPS_FOLD_DISCARD_TAC AES256_GCM_DEC_ALT_EXEC (175--183) THEN
  (* split the s183 bytes128 store readbacks into bytes64 halves *)
  RULE_ASSUM_TAC(fun th ->
    match concl th with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
        Comb(Comb(Const(":>",_),Const("memory",_)),
             Comb(Const("bytes128",_),_))),st)),_)
        when (try fst(dest_var st)="s183" with _ -> false) ->
        (try CONV_RULE(READ_MEMORY_SPLIT_CONV 1) th with _ -> th)
    | _ -> th) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  (* normalize block-1/block-2 store hi-half addresses *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (out_p:int64) (word 16)) (word 8) = word_add out_p (word 24)`;
    WORD_RULE
    `word_add (word_add (out_p:int64) (word 32)) (word 8) = word_add out_p (word 40)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_RULE
    `word_add (word_add (out_p:int64) (word 16)) (word 8) = word_add out_p (word 24)`;
    WORD_RULE
    `word_add (word_add (out_p:int64) (word 32)) (word 8) = word_add out_p (word 40)`] THEN
  (* Block 1 closes here, by its plaintext captured at s123.  Each closer
     below is guarded to the conjuncts of its own kind, by the counter its
     right side mentions, so that none runs on a conjunct it cannot close:
     the block-0 closer, for one, does not terminate on the +2 counter of
     block 2. *)
  REPEAT CONJ_TAC THEN
  (* The guards are positive and mutually exclusive, and the tag closer runs
     first: the tag goal has no gcm_ctr_inc, so a negative block-0 guard (no
     gcm_ctr_inc) would accept it and run WORD_BLAST into the GHASH
     polynomial.  The block-0 guard requires aes256_encrypt. *)
  (* xi: strip word_bytereverse and replace gval by its definition through a
     check-based SUBST1_TAC; EXPAND_TAC "gval" could pick an assumption
     `read Q19 sN = gval` instead. *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="ghash_polyval_acc" with _->false)) w
              || can (find_term (fun t -> t = `gval:int128`)) w)
        then failwith "not-xi" else
        (TRY(AP_THM_TAC THEN AP_TERM_TAC) THEN AP_TERM_TAC THEN
         FIRST_X_ASSUM(SUBST1_TAC o SYM o
           check (fun th -> try rhs(concl th) = `gval:int128` &&
                                (match lhs(concl th) with
                                 | Comb(Comb(Const("ghash_polyval_acc",_),_),_) -> true | _ -> false)
                            with _ -> false)) THEN
         REFL_TAC) (asl,w))
      THEN NO_TAC) THEN
  (* ivec: gcm_ctr_inc_iter 3 ctr0 in its lane form (GCM_CTR_INC3_LANES) *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="gcm_ctr_inc_iter" with _->false)) w)
        then failwith "not-ivec" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         SUBGOAL_THEN `gcm_ctr_inc_iter 3 ctr0 = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))`
           SUBST1_TAC THENL
          [REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`; gcm_ctr_inc_iter]; ALL_TAC] THEN
         GEN_REWRITE_TAC RAND_CONV [GCM_CTR_INC3_LANES] THEN REFL_TAC) (asl,w)) THEN NO_TAC) THEN
  (* out block 2 (out_p+32, counter gcm_ctr_inc (gcm_ctr_inc ctr0)) *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> t = `gcm_ctr_inc (gcm_ctr_inc ctr0):int128`)) w)
        then failwith "not-blk2" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC2_LANES] THEN
         ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
         REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
         REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST) (asl,w)) THEN NO_TAC) THEN
  (* out block 0 (out_p, counter ctr0): aes256_encrypt without gcm_ctr_inc or
     GHASH, so only the two halves of block 0 *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="aes256_encrypt" with _->false)) w)
           || can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="gcm_ctr_inc" with _->false)) w
           || can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="ghash_polyval_acc" with _->false)) w
        then failwith "not-blk0" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         REWRITE_TAC[JOIN_IS_CTR0] THEN
         ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
         REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
         REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST) (asl,w)) THEN NO_TAC) THEN
  (* MAYCHANGE: SUBSUMED_MAYCHANGE_TAC is impractical on the accumulated
     frame here, so keep only the MAYCHANGE assumption and apply
     WB3_FRAME_IMP (one MATCH_MP and ACCEPT_TAC) *)
  DISCARD_ASSUMPTIONS_TAC (fun th -> not(maychange_term(concl th))) THEN
  FIRST_X_ASSUM(fun th -> ACCEPT_TAC(MATCH_MP WB3_FRAME_IMP th)));;

(* ---- nblk = 4 ---- *)

(* The frame lemma for nblk = 4 and its implication at s0 and s227, as
   WB3_FRAME_SUBSUMED and WB3_FRAME_IMP for nblk = 3. *)
let WB4_FRAME_SUBSUMED = prove(
 `(MAYCHANGE [PC] ,, MAYCHANGE [X9] ,, MAYCHANGE [X16] ,, MAYCHANGE [X11] ,,
   MAYCHANGE [X5] ,, MAYCHANGE [memory :> bytes64 (word_add stackpointer (word 64))] ,,
   MAYCHANGE [memory :> bytes64 (word_add stackpointer (word 72))] ,, MAYCHANGE [events] ,,
   MAYCHANGE [X10] ,, MAYCHANGE [NF] ,, MAYCHANGE [ZF] ,, MAYCHANGE [CF] ,, MAYCHANGE [VF] ,,
   MAYCHANGE [Q30] ,, MAYCHANGE [Q19] ,, MAYCHANGE [X15] ,, MAYCHANGE [Q31] ,, MAYCHANGE [Q16] ,,
   MAYCHANGE [Q29] ,, MAYCHANGE [Q1] ,, MAYCHANGE [Q2] ,, MAYCHANGE [Q3] ,, MAYCHANGE [Q4] ,,
   MAYCHANGE [Q5] ,, MAYCHANGE [Q6] ,, MAYCHANGE [Q7] ,, MAYCHANGE [Q8] ,, MAYCHANGE [Q9] ,,
   MAYCHANGE [Q10] ,, MAYCHANGE [Q11] ,, MAYCHANGE [Q12] ,, MAYCHANGE [Q13] ,, MAYCHANGE [Q14] ,,
   MAYCHANGE [Q15] ,, MAYCHANGE [Q24] ,, MAYCHANGE [Q25] ,, MAYCHANGE [Q21] ,, MAYCHANGE [Q17] ,,
   MAYCHANGE [Q18] ,, MAYCHANGE [Q26] ,, MAYCHANGE [X0] ,, MAYCHANGE [Q0] ,, MAYCHANGE [Q20] ,,
   MAYCHANGE [Q22] ,, MAYCHANGE [Q23] ,, MAYCHANGE [memory :> bytes128 out_p] ,, MAYCHANGE [X2] ,,
   MAYCHANGE [memory :> bytes128 (word_add out_p (word 16))] ,,
   MAYCHANGE [memory :> bytes128 (word_add out_p (word 32))] ,,
   MAYCHANGE [memory :> bytes128 tag_p] ,,
   MAYCHANGE [memory :> bytes128 ivec_p] ,,
   MAYCHANGE [memory :> bytes128 (word_add out_p (word 48))]
   :armstate->armstate->bool) subsumed
  (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
   MAYCHANGE [memory :> bytes(out_p:int64, 64); memory :> bytes(tag_p:int64,16);
              memory :> bytes(ivec_p:int64,16);
              memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
   MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
              Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC);;

let WB4_FRAME_IMP =
  SPECL [`s0:armstate`; `s227:armstate`] (REWRITE_RULE[subsumed] WB4_FRAME_SUBSUMED);;

(* BRIDGE_CLOSE_4_CPH3_TAC sN: the nblk = 4 bridge, with spec_to_byteform_wb4
   and GMULT4_FULL_CORRECT_BA at dec_bridge_specl_4_cph3.  The identities of
   block 0's products with H^4: qq14 = qq9 XOR qq1 and qq13 = qq8 XOR qq0
   (outer), qq20 = qq15 XOR qq16 (middle). *)
let BRIDGE_CLOSE_4_CPH3_TAC sN : tactic = fun (asl,w) ->
  let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
  let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
  let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
  let gmult_dec = REWRITE_RULE[LET_DEF;LET_END_DEF] (SPECL dec_bridge_specl_4_cph3 GMULT4_FULL_CORRECT_BA) in
  let spec_eq = TRANS (MP spec_to_byteform_wb4 (CONJ h2asm (CONJ h3asm h4asm))) (GSYM gmult_dec) in
  DEC_BRIDGE_ROUTEB_TAC sN spec_eq
    (("qq14","qq9","qq1"),("qq13","qq8","qq0"),("qq20","qq15","qq16")) (asl,w);;

(* WB_FUSED_4BLOCK, nblk = 4: 227 steps.  s1-s8 the front and the dispatch,
   s9-s30 L256_dec_small and L256_dec_small_ge3, s31-s38
   L256_dec_small_seed_4 (the seed Xi' * H^4), s39-s81 small_blk_4 (block 0,
   stored at s81), s82-s124 small_blk_3 (block 1, stored at s124), s125-s167
   small_blk_2 (block 2, stored at s167), s168-s226 small_blk_1 (block 3, the
   reduce at s214, ext and rev64 at s217 and s218, the tag store at s221, the
   counter store at s224, the block-3 store at s226) and s227 the b at
   L256_dec_small_done.
   The proof is that of nblk = 3 with one more window: hk and h3k are split
   (the Karatsuba mids of H and H^2 at +16 and +24, of H^3 and H^4 at +64 and
   +72), the windows end at the block stores s81, s124, s167 and at the
   reduce s214, where BRIDGE_CLOSE_4_CPH3_TAC closes Q19, the closers below
   take the conjuncts by kind, and the frame closes by WB4_FRAME_IMP. *)
let WB_FUSED_4BLOCK = prove(
 `!pc stackpointer out_p tag_p ivec_p in_p key_p htable_p
    cph0 cph1 cph2 cph3 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 h3 h3k h4.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 5908) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 5908) (out_p:int64, 64) /\
    nonoverlapping (word pc, 5908) (tag_p:int64, 16) /\
    nonoverlapping (word pc, 5908) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 64) (tag_p, 16) /\
    nonoverlapping (out_p, 64) (ivec_p, 16) /\
    nonoverlapping (tag_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 64) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htable_p:int64, 192) /\
    nonoverlapping (in_p, 64) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htable_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (tag_p, 16) (in_p, 64) /\
    nonoverlapping (tag_p, 16) (key_p, 240) /\
    nonoverlapping (tag_p, 16) (htable_p, 192) /\
    nonoverlapping (tag_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 64) (in_p, 64) /\
    nonoverlapping (out_p, 64) (key_p, 240) /\
    nonoverlapping (out_p, 64) (htable_p, 192) /\
    nonoverlapping (out_p, 64) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word) /\
    word_subword hk (64,64) :64 word =
      word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64):64 word) /\
    word_subword h3k (0,64) :64 word =
      word_xor (word_subword h3 (0,64):64 word) (word_subword h3 (64,64):64 word) /\
    word_subword h3k (64,64) :64 word =
      word_xor (word_subword h4 (0,64):64 word) (word_subword h4 (64,64):64 word) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
    byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
          read PC s = word (pc + 0x1c) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word 512; out_p; tag_p; ivec_p; key_p; htable_p] s /\
          read (memory :> bytes128 in_p) s = cph0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
          read (memory :> bytes128 (word_add in_p (word 32))) s = cph2 /\
          read (memory :> bytes128 (word_add in_p (word 48))) s = cph3 /\
          read (memory :> bytes128 tag_p) s = xi /\
          read (memory :> bytes128 ivec_p) s = ctr0 /\
          read (memory :> bytes128 key_p) s = k0 /\
          read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
          read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
          read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
          read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
          read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
          read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
          read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
          read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
          read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
          read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
          read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
          read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
          read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
          read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
          read (memory :> bytes128 htable_p) s = h /\
          read (memory :> bytes128 (word_add htable_p (word 16))) s = hk /\
          read (memory :> bytes128 (word_add htable_p (word 32))) s = h2 /\
          read (memory :> bytes128 (word_add htable_p (word 48))) s = h3 /\
          read (memory :> bytes128 (word_add htable_p (word 64))) s = h3k /\
          read (memory :> bytes128 (word_add htable_p (word 80))) s = h4)
     (\s. read PC s = word (pc + 0x119c) /\
          read X9 s = word 64 /\
          read (memory :> bytes128 out_p) s =
          word_xor cph0 (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 16))) s =
          word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0)
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 32))) s =
          word_xor cph2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0))
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 48))) s =
          word_xor cph3 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 tag_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3]) /\
          read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 4 ctr0)
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 64); memory :> bytes(tag_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  CLEAR_KEEPGHALL_MEMO_TAC THEN  (* empty the normalizer fixpoint table *)
  (* split hk at htable_p+16: the Karatsuba mids of H (low) and H^2 (high) *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htable_p (word 16))) s0` with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN STRIP_TAC)
    else NO_TAC) THEN
  (* split h3k at htable_p+64: Karatsuba mids of H^3 (low) and H^4 (high) *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htable_p (word 64))) s0` with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN STRIP_TAC)
    else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (htable_p:int64) (word 16)) (word 8) = word_add htable_p (word 24)`;
    WORD_RULE
    `word_add (word_add (htable_p:int64) (word 64)) (word 8) = word_add htable_p (word 72)`]) THEN
  ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (1--30) THEN
  (* the seed and block 0 (H^4), steps 31-81; block 0 is stored at s81 *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AES256_GCM_DEC_ALT_EXEC (31--81) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 out_p) (s81:armstate) =
     word_xor cph0 (aes256_encrypt ctr0
       [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN REWRITE_TAC[JOIN_IS_CTR0] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  INLINE_SELFCONTAINED "Q17" "s81" 30 THEN
  INLINE_SELFCONTAINED "Q18" "s81" 30 THEN
  INLINE_SELFCONTAINED "Q19" "s81" 30 THEN
  DISCARD_OLDSTATE_TAC "s81" THEN
  (* block 1 (H^3), steps 82-124, stored at s124 *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AES256_GCM_DEC_ALT_EXEC (82--124) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 (word_add out_p (word 16))) (s124:armstate) =
     word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0)
       [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[aese; aesmc] THEN (CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST);
   ALL_TAC] THEN
  INLINE_SELFCONTAINED "Q17" "s124" 40 THEN
  INLINE_SELFCONTAINED "Q18" "s124" 40 THEN
  INLINE_SELFCONTAINED "Q19" "s124" 40 THEN
  DISCARD_OLDSTATE_TAC "s124" THEN
  (* block 2 (H^2), steps 125-167, stored at s167 *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AES256_GCM_DEC_ALT_EXEC (125--167) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 (word_add out_p (word 32))) (s167:armstate) =
     word_xor cph2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0))
       [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC2_LANES] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[aese; aesmc] THEN (CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST);
   ALL_TAC] THEN
  INLINE_SELFCONTAINED "Q17" "s167" 40 THEN
  INLINE_SELFCONTAINED "Q18" "s167" 40 THEN
  INLINE_SELFCONTAINED "Q19" "s167" 40 THEN
  DISCARD_OLDSTATE_TAC "s167" THEN
  (* block 3 (H) and the reduce, steps 168-214; the bridge at s214 *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AES256_GCM_DEC_ALT_EXEC (168--214) THEN
  INLINE_SELFCONTAINED "Q19" "s214" 12 THEN
  DISCARD_OLDSTATE_TAC "s214" THEN
  SUBGOAL_THEN
    `read Q19 (s214:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s214` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [BRIDGE_CLOSE_4_CPH3_TAC 214;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3]` THEN
  (* ext and rev64 of v19 (s217, s218): Q19 = word_bytereverse gval *)
  ARM_STEPS_FOLD_DISCARD_TAC AES256_GCM_DEC_ALT_EXEC (215--218) THEN
  SUBGOAL_THEN `read Q19 (s218:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s218` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s218` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_STEPS_FOLD_DISCARD_TAC AES256_GCM_DEC_ALT_EXEC (219--227) THEN
  (* split the s227 bytes128 store readbacks into bytes64 halves *)
  RULE_ASSUM_TAC(fun th ->
    match concl th with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
        Comb(Comb(Const(":>",_),Const("memory",_)),
             Comb(Const("bytes128",_),_))),st)),_)
        when (try fst(dest_var st)="s227" with _ -> false) ->
        (try CONV_RULE(READ_MEMORY_SPLIT_CONV 1) th with _ -> th)
    | _ -> th) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (out_p:int64) (word 16)) (word 8) = word_add out_p (word 24)`;
    WORD_RULE
    `word_add (word_add (out_p:int64) (word 32)) (word 8) = word_add out_p (word 40)`;
    WORD_RULE
    `word_add (word_add (out_p:int64) (word 48)) (word 8) = word_add out_p (word 56)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_RULE
    `word_add (word_add (out_p:int64) (word 16)) (word 8) = word_add out_p (word 24)`;
    WORD_RULE
    `word_add (word_add (out_p:int64) (word 32)) (word 8) = word_add out_p (word 40)`;
    WORD_RULE
    `word_add (word_add (out_p:int64) (word 48)) (word 8) = word_add out_p (word 56)`] THEN
  REPEAT CONJ_TAC THEN
  (* xi, as for nblk = 3 *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="ghash_polyval_acc" with _->false)) w
              || can (find_term (fun t -> t = `gval:int128`)) w)
        then failwith "not-xi" else
        (TRY(AP_THM_TAC THEN AP_TERM_TAC) THEN AP_TERM_TAC THEN
         FIRST_X_ASSUM(SUBST1_TAC o SYM o
           check (fun th -> try rhs(concl th) = `gval:int128` &&
                                (match lhs(concl th) with
                                 | Comb(Comb(Const("ghash_polyval_acc",_),_),_) -> true | _ -> false)
                            with _ -> false)) THEN
         REFL_TAC) (asl,w)) THEN NO_TAC) THEN
  (* ivec: gcm_ctr_inc_iter 4 ctr0 in its lane form (GCM_CTR_INC4_LANES) *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="gcm_ctr_inc_iter" with _->false)) w)
        then failwith "not-ivec" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         SUBGOAL_THEN `gcm_ctr_inc_iter 4 ctr0 = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))`
           SUBST1_TAC THENL
          [REWRITE_TAC[num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; gcm_ctr_inc_iter]; ALL_TAC] THEN
         GEN_REWRITE_TAC RAND_CONV [GCM_CTR_INC4_LANES] THEN REFL_TAC) (asl,w)) THEN NO_TAC) THEN
  (* out block 3 (out_p+48, counter gcm_ctr_inc^3 ctr0) *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> t = `gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)):int128`)) w)
        then failwith "not-blk3" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC3_LANES] THEN
         ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
         REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
         REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST) (asl,w)) THEN NO_TAC) THEN
  (* out block 2 (out_p+32): gcm_ctr_inc^2 ctr0 but not gcm_ctr_inc^3 ctr0 *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> t = `gcm_ctr_inc (gcm_ctr_inc ctr0):int128`)) w)
           || can (find_term (fun t -> t = `gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)):int128`)) w
        then failwith "not-blk2" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC2_LANES] THEN
         ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
         REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
         REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST) (asl,w)) THEN NO_TAC) THEN
  (* out block 1 (out_p+16): gcm_ctr_inc ctr0 but not gcm_ctr_inc^2 ctr0 *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> t = `gcm_ctr_inc ctr0:int128`)) w)
           || can (find_term (fun t -> t = `gcm_ctr_inc (gcm_ctr_inc ctr0):int128`)) w
        then failwith "not-blk1" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
         ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
         REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
         REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST) (asl,w)) THEN NO_TAC) THEN
  (* out block 0 (out_p): aes256_encrypt without gcm_ctr_inc or GHASH *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="aes256_encrypt" with _->false)) w)
           || can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="gcm_ctr_inc" with _->false)) w
           || can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="ghash_polyval_acc" with _->false)) w
        then failwith "not-blk0" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         REWRITE_TAC[JOIN_IS_CTR0] THEN
         ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
         REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
         REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST) (asl,w)) THEN NO_TAC) THEN
  (* MAYCHANGE: keep only the MAYCHANGE assumption and apply WB4_FRAME_IMP *)
  DISCARD_ASSUMPTIONS_TAC (fun th -> not(maychange_term(concl th))) THEN
  FIRST_X_ASSUM(fun th -> ACCEPT_TAC(MATCH_MP WB4_FRAME_IMP th)));;

let s42_key_args = [`xi:int128`;`ctr0:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;
                `k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;
                `k12:int128`;`k13:int128`;`k14:int128`;`h:int128`];;
let s42_fused_specl_args k =
  let cphs = map s42_cph_tm (0--(k-1)) in
  let htail =
    if k = 1 then [s42_hk_tm]
    else if k = 2 then [s42_hk_tm; s42_hpow 2]
    else if k = 3 then [s42_hk_tm; s42_hpow 2; s42_hpow 3; s42_h3k_tm]
    else [s42_hk_tm; s42_hpow 2; s42_hpow 3; s42_h3k_tm; s42_hpow 4] in
  s42_ptr_args @ cphs @ s42_key_args @ htail;;
let s42_lane_discharge k =
  EVERY(map (fun i ->
    let ni = mk_small_numeral i and nk = mk_small_numeral k in
    MP_TAC(SPECL [nk; `in_p:int64`; `ibytes:byte list`; `x:armstate`] INPUT_PREFIX_TO_BYTE128_LANES) THEN
    REWRITE_TAC[ARITH_RULE(mk_eq(mk_binop `( * ):num->num->num` `16` nk, mk_small_numeral(16*k)))] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    DISCH_THEN(fun lth -> MP_TAC(SPEC ni lth)) THEN
    REWRITE_TAC[ARITH_RULE(mk_binop `(<):num->num->bool` ni nk)] THEN
    (if i = 0 then REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0]
     else REWRITE_TAC[ARITH_RULE(mk_eq(mk_binop `( * ):num->num->num` `16` ni, mk_small_numeral(16*i)))]) THEN
    DISCH_TAC)
    (0--(k-1))) THEN
  ASM_REWRITE_TAC[];;
let mk_band_from_fused k fused_thm =
  let fused_inst = SPECL (s42_fused_specl_args k) fused_thm in
  let fused_pre = el 1 (snd(strip_comb(snd(dest_imp(concl fused_inst))))) in
  prove(mk_band_goal k,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC fused_pre THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[htable_mem_dec] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN (subst [mk_small_numeral(16*k),`sss:num`]
        `SUB_LIST (0,sss) (ibytes:byte list) = ibytes`) ASSUME_TAC THENL
       [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      s42_lane_discharge k;
      MP_TAC fused_inst THEN ANTS_TAC THENL
       [REWRITE_TAC[GSYM WB_MC_LEN] THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[HK_LOW_IS_KARA; HK_HI_IS_KARA; karatsuba_mid] THEN
        REWRITE_TAC[BYTESWAP128_INVOLUTION];
        DISCH_THEN ACCEPT_TAC]]);;

(* The back-leg theorems WB_TAIL_GEN2_1..8 as a list: entry k - 1 is the
   back-leg of a k-block tail. *)
let wbn_backlegs =
  [WB_TAIL_GEN2_1; WB_TAIL_GEN2_2; WB_TAIL_GEN2_3; WB_TAIL_GEN2_4;
   WB_TAIL_GEN2_5; WB_TAIL_GEN2_6; WB_TAIL_GEN2_7; WB_TAIL_GEN2_8];;
(* The band prover, for k = 5..8 (bands 1..4 take the small path above):
   ENSURES_FRAME_SUBSUMED and ENSURES_TRANS split the band at the seam
   pc+3824 (q_at k), since ENSURES_SEQUENCE_TAC fails in MAYCHANGE_IDEMPOT on
   this frame.  WB_FRONT_BUF discharges the front leg; the back leg is not
   simulated again: it follows from WB_TAIL_GEN2_k by precondition weakening
   (q_at k implies its weaker precondition, which omits five cells the tail
   does not read). *)
let prove_band k =
  prove(mk_band_goal k,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC (fdbl_at k) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_TRANS THEN EXISTS_TAC (q_at k) THEN CONJ_TAC THENL
     [MATCH_MP_TAC (wbf_at k) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC (wbn_weak_q_at5 k) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC (el (k-1) wbn_backlegs) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]);;

(* ---- the eight band theorems, without simulation ---- *)
(* Bands 1..4 take the small-message path, so they come from WB_FUSED_kBLOCK
   by mk_band_from_fused; prove_band, which takes the front through
   WB_FRONT_BUF, needs 5 <= nblk.  Bands 5..8 reuse the back-legs
   WB_TAIL_GEN2_k. *)
let AES256_GCM_DEC_ALT_BUF_1BLOCK = mk_band_from_fused 1 WB_FUSED_1BLOCK;;
let AES256_GCM_DEC_ALT_BUF_2BLOCK = mk_band_from_fused 2 WB_FUSED_2BLOCK;;
let AES256_GCM_DEC_ALT_BUF_3BLOCK = mk_band_from_fused 3 WB_FUSED_3BLOCK;;
let AES256_GCM_DEC_ALT_BUF_4BLOCK = mk_band_from_fused 4 WB_FUSED_4BLOCK;;
let AES256_GCM_DEC_ALT_BUF_5BLOCK = prove_band 5;;
let AES256_GCM_DEC_ALT_BUF_6BLOCK = prove_band 6;;
let AES256_GCM_DEC_ALT_BUF_7BLOCK = prove_band 7;;
let AES256_GCM_DEC_ALT_BUF_8BLOCK = prove_band 8;;

(* ---- step 2: whole-blocks output bridge (per-block stores -> byte_list_at).
   Byte i of the output is byte i MOD 16 of block i DIV 16
   (EL_INT128_LIST_TO_BYTES), read off the bytes128 store of that block
   (BYTE8_OF_BYTES128); the input-side mirror is WBN_INPUT_ASSEMBLE below. *)
let BYTE_LIST_AT_WHOLE_CTR = prove
 (`!ctr0 pts keys n out_p (len:int64) s.
    1 <= n /\ n = LENGTH pts /\ val len = 16 * n /\
    (!j. j < n ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                   EL j (aes_ctr ctr0 pts keys))
    ==> byte_list_at (aes_ctr_bytes ctr0 pts keys) out_p len s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[byte_list_at; aes_ctr_bytes] THEN
  X_GEN_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `i DIV 16 < n` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`aes_ctr ctr0 pts keys`; `i:num`] EL_INT128_LIST_TO_BYTES) THEN
  REWRITE_TAC[LENGTH_AES_CTR] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
    `word_add out_p (word i):int64 =
     word_add (word_add out_p (word (16 * (i DIV 16)))) (word (i MOD 16))`
    SUBST1_TAC THENL
   [SUBGOAL_THEN `i = 16 * (i DIV 16) + i MOD 16`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
     [MESON_TAC[DIVISION_SIMP]; ALL_TAC] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  MP_TAC(SPECL [`word_add out_p (word (16 * (i DIV 16))):int64`; `s:armstate`;
                `i MOD 16`] BYTE8_OF_BYTES128) THEN
  ANTS_TAC THENL [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]);;

(* ---- step 3: build_aes_ctr_el k, the k elements of aes_ctr over a k-block
   list: EL j = pt_j XOR aes256_encrypt (gcm_ctr_inc^j ctr0) keys ---- *)
let build_aes_ctr_el k =
  let pts = map (fun i -> mk_var("pt"^string_of_int i,`:int128`)) (0--(k-1)) in
  let plist = mk_flist pts in
  let rec ctr j = if j = 0 then `ctr0:int128` else mk_comb(`gcm_ctr_inc`, ctr (j-1)) in
  let conj_of j =
    mk_eq(list_mk_comb(`EL:num->(int128)list->int128`,
            [mk_small_numeral j;
             list_mk_comb(`aes_ctr`, [`ctr0:int128`; plist; `keys:int128 list`])]),
          list_mk_comb(`word_xor:int128->int128->int128`,
            [el j pts;
             list_mk_comb(`aes256_encrypt`, [ctr j; `keys:int128 list`])])) in
  let goal = list_mk_conj (map conj_of (0--(k-1))) in
  let sucs = map (fun i -> num_CONV (mk_small_numeral i)) (1--(k-1)) in
  prove(goal,
    REWRITE_TAC[aes_ctr; aes_ctr_rec; aes_ctr_output_block; gcm_ctr_inc_iter] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC(sucs @ [EL; HD; TL]) THEN
    REWRITE_TAC[gcm_ctr_inc_iter] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC(sucs @ [gcm_ctr_inc_iter]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC(sucs @ [gcm_ctr_inc_iter]));;

(* ---- step 4: wrapper goal builder and prover ----
   The wrapper is the BUF band statement with (a) the input buffer read
   replaced by byte_list_at ibytes and (b) the per-block stores and the
   explicit GHASH of the postcondition replaced by gcm_dec_pt_bytes and
   gcm_dec_final_xi over the whole buffer.  No simulation: the precondition
   by BYTE_LIST_AT_TO_READ_BYTES, the postcondition by BYTE_LIST_AT_WHOLE_CTR
   and the EL facts of the band; the specifications unfold by
   GCM_DEC_GHASH_BLOCKS_WHOLE_k and GCM_DEC_PT_BYTES_WHOLE_k. *)
let wb_keys_tm = `[k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]`;;
let mk_wb_wrapper_goal k =
  let g = mk_band_goal k in
  let vars, body = strip_forall g in
  let hyps, ens = dest_imp body in
  let frame = rand ens and post = rand(rator ens) and pre = rand(rator(rator ens)) in
  let n16 = mk_small_numeral(16*k) in
  let sv = `s:armstate` in
  let oldread = subst [n16,`nnn:num`]
    `read (memory :> bytes (in_p,nnn)) s = num_of_bytelist (ibytes:byte list)` in
  let newread = subst [n16,`nnn:num`]
    `byte_list_at (ibytes:byte list) in_p (word nnn) s` in
  let pre_body = snd(dest_abs pre) in
  let pre' = mk_abs(sv, list_mk_conj
    (map (fun c -> if c = oldread then newread else c) (conjuncts pre_body))) in
  let post_body = snd(dest_abs post) in
  let pcc = hd(conjuncts post_body) in
  let x9c = el 1 (conjuncts post_body) in
  let outpost = subst [n16,`nnn:num`; wb_keys_tm,`kl:int128 list`]
    `byte_list_at (gcm_dec_pt_bytes nnn ibytes ctr0 (kl:int128 list)) out_p (word nnn) s` in
  let xipost = subst [n16,`nnn:num`]
    `read (memory :> bytes128 tag_p) s = gcm_dec_final_xi nnn ibytes xi h` in
  (* the counter write-back conjunct of the band, unchanged *)
  let ivecpost = mk_ivec_conj k in
  let post' = mk_abs(sv, list_mk_conj [pcc; x9c; outpost; xipost; ivecpost]) in
  list_mk_forall(vars,
    mk_imp(hyps, list_mk_comb(rator(rator(rator ens)), [pre'; post'; frame])));;

let pt_wholes = [GCM_DEC_PT_BYTES_WHOLE_1;GCM_DEC_PT_BYTES_WHOLE_2;
                 GCM_DEC_PT_BYTES_WHOLE_3;GCM_DEC_PT_BYTES_WHOLE_4;
                 GCM_DEC_PT_BYTES_WHOLE_5;GCM_DEC_PT_BYTES_WHOLE_6;
                 GCM_DEC_PT_BYTES_WHOLE_7;GCM_DEC_PT_BYTES_WHOLE_8];;
let prove_wb_wrapper k buf_thm =
  let n16 = mk_small_numeral(16*k) in
  let band = mk_band_goal k in
  let _, bbody = strip_forall band in
  let _, bens = dest_imp bbody in
  let pre_buf = rand(rator(rator bens)) and post_buf = rand(rator bens) in
  let el_facts = build_aes_ctr_el k in
  let inbridge = CONV_RULE (ONCE_DEPTH_CONV WORD_REDUCE_CONV)
    (SPECL [`ibytes:byte list`;`in_p:int64`; mk_comb(`word:num->int64`,n16); `s:armstate`]
       BYTE_LIST_AT_TO_READ_BYTES) in
  let jsplit = ARITH_RULE
    (mk_eq(subst [mk_small_numeral k,`kkk:num`] `j < kkk:num`,
           list_mk_disj (map (fun i -> mk_eq(`j:num`, mk_small_numeral i)) (0--(k-1))))) in
  prove(mk_wb_wrapper_goal k,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[gcm_dec_final_xi; el (k-1) ghash_wholes; el (k-1) pt_wholes; MAP] THEN
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC pre_buf THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC inbridge THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
      EXISTS_TAC post_buf THEN
      CONJ_TAC THENL
       [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC BYTE_LIST_AT_WHOLE_CTR THEN
        EXISTS_TAC (mk_small_numeral k) THEN
        REPEAT CONJ_TAC THENL
         [ARITH_TAC;
          REWRITE_TAC[LENGTH] THEN ARITH_TAC;
          CONV_TAC WORD_REDUCE_CONV THEN ARITH_TAC;
          X_GEN_TAC `j:num` THEN REWRITE_TAC[jsplit] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          REWRITE_TAC[WORD_ADD_0; el_facts] THEN ASM_REWRITE_TAC[el_facts]];
        MATCH_MP_TAC buf_thm THEN ASM_REWRITE_TAC[]]]);;

(* ---- key condensation: the round-key list and its 15 bytes128 reads ---- *)
let RK_ETA_15 = prove_rk_eta 15;;

let KEY_READS_FROM_WORDLIST = prove_key_reads 15;;

(* ---- the readable-band prover ----
   For band k: (1) prove_wb_wrapper k buf_thm gives the internal byte-list
   wrapper over _BUF_kBLOCK; (2) mk_wrapper_nist instantiates it at
   ki := EL i rk, h := byteswap128 (ghash_twist H), xi := word_reversefields
   8 tag0 and rewrites it into the NIST vocabulary; (3) WB_READABLE_TAC
   closes the literal statement: the ALLPAIRS/PAIRWISE/ALL unfolding and
   NONOVERLAPPING_SYM match the pairwise hypotheses of the wrapper,
   RK_ETA_15 folds the EL list back to rk, and ENSURES_PRECONDITION_THM with
   KEY_READS_FROM_WORDLIST bridges the key reads. *)
let mk_wrapper_nist k wrapper_thm =
  let winst = SPECL ([`pc:num`;`stackpointer:int64`;`out_p:int64`;`tag_p:int64`;`ivec_p:int64`;
                      `in_p:int64`;`key_p:int64`;`htable_p:int64`;`ibytes:byte list`;
                      `word_reversefields 8 (tag0:int128)`;`ctr0:int128`] @
                     map (fun i -> list_mk_comb(`EL:num->(int128)list->int128`,
                            [mk_small_numeral i; `rk:int128 list`])) (0--14) @
                     [`byteswap128 (ghash_twist H)`]) wrapper_thm in
  let xi_rw = MP (SPECL [`H:int128`; `byteswap128 (ghash_twist H)`;
                         mk_small_numeral(16*k); `ibytes:byte list`;
                         `word_reversefields 8 (tag0:int128)`] GCM_DEC_FINAL_XI_NIST)
                 bsw_inv in
  REWRITE_RULE[HTABLE_MEM_DEC_IS_HTABLE_MEM_8; BYTESWAP128_INVOLUTION; xi_rw;
               GSYM (el (k-1) LIST_OF_SEQ_NIST_INPUT); BREV_RF8_INV_128; BREV_RF8_128] winst;;

let wb_rk15_tm = `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
                   EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk;
                   EL 13 rk; EL 14 rk]:int128 list`;;
let WB_READABLE_TAC k buf_thm =
  let wn = mk_wrapper_nist k (prove_wb_wrapper k buf_thm) in
  REPEAT GEN_TAC THEN REWRITE_TAC[ALLPAIRS;PAIRWISE;ALL] THEN STRIP_TAC THEN
  MP_TAC wn THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(wb_rk15_tm,`rk:int128 list`)) SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RK_ETA_15 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  FIRST_X_ASSUM(fun th ->
    EXISTS_TAC (rand(rator(rator(concl th)))) THEN MP_TAC th) THEN
  DISCH_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th ->
    try MP_TAC(MATCH_MP KEY_READS_FROM_WORDLIST th)
    with Failure _ -> failwith "no wordlist assumption") THEN
  SIMP_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The eight readable band theorems (literal statements: the specification). *)
(* Reading guide for N blocks: under the ABI and nonoverlapping side         *)
(* conditions, decrypting N whole blocks writes to out_p the CTR keystream   *)
(* XORed onto the input bytes (gcm_dec_pt_bytes), replaces the tag at tag_p  *)
(* with the SP 800-38D GHASH of the N raw ciphertext blocks folded onto tag0 *)
(* under the NIST hash key H (both tag values byte-reversed, as the AWS-LC   *)
(* caller keeps them), stores the counter block advanced by N at ivec_p      *)
(* (gcm_ctr_inc_iter N ctr0), and leaves the byte count 16 * N in X9.        *)
(* ------------------------------------------------------------------------- *)

let AES256_GCM_DEC_ALT_1BLOCK = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 16 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,16; tag_p,16; ivec_p,16]
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16; key_p,240; htable_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,16; tag_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16; key_p,240; htable_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 128; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               byte_list_at ibytes in_p (word 16) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = word (pc + 4508) /\
               read X9 s = word 16 /\
               byte_list_at (gcm_dec_pt_bytes 16 ibytes ctr0 rk) out_p (word 16) s /\
               read (memory :> bytes128 tag_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 1))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 1 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,16); memory :> bytes(tag_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 1 AES256_GCM_DEC_ALT_BUF_1BLOCK);;

let AES256_GCM_DEC_ALT_2BLOCK = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 32 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,32; tag_p,16; ivec_p,16]
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,32; key_p,240; htable_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,32; tag_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,32; key_p,240; htable_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 256; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               byte_list_at ibytes in_p (word 32) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = word (pc + 4508) /\
               read X9 s = word 32 /\
               byte_list_at (gcm_dec_pt_bytes 32 ibytes ctr0 rk) out_p (word 32) s /\
               read (memory :> bytes128 tag_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 2))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 2 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,32); memory :> bytes(tag_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 2 AES256_GCM_DEC_ALT_BUF_2BLOCK);;

let AES256_GCM_DEC_ALT_3BLOCK = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 48 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,48; tag_p,16; ivec_p,16]
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,48; key_p,240; htable_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,48; tag_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,48; key_p,240; htable_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 384; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               byte_list_at ibytes in_p (word 48) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = word (pc + 4508) /\
               read X9 s = word 48 /\
               byte_list_at (gcm_dec_pt_bytes 48 ibytes ctr0 rk) out_p (word 48) s /\
               read (memory :> bytes128 tag_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 3))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 3 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,48); memory :> bytes(tag_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 3 AES256_GCM_DEC_ALT_BUF_3BLOCK);;

let AES256_GCM_DEC_ALT_4BLOCK = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 64 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,64; tag_p,16; ivec_p,16]
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,64; key_p,240; htable_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,64; tag_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,64; key_p,240; htable_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 512; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               byte_list_at ibytes in_p (word 64) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = word (pc + 4508) /\
               read X9 s = word 64 /\
               byte_list_at (gcm_dec_pt_bytes 64 ibytes ctr0 rk) out_p (word 64) s /\
               read (memory :> bytes128 tag_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 4))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 4 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,64); memory :> bytes(tag_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 4 AES256_GCM_DEC_ALT_BUF_4BLOCK);;

let AES256_GCM_DEC_ALT_5BLOCK = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 80 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,80; tag_p,16; ivec_p,16]
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,80; key_p,240; htable_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,80; tag_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,80; key_p,240; htable_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 640; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               byte_list_at ibytes in_p (word 80) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = word (pc + 4508) /\
               read X9 s = word 80 /\
               byte_list_at (gcm_dec_pt_bytes 80 ibytes ctr0 rk) out_p (word 80) s /\
               read (memory :> bytes128 tag_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 5))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 5 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,80); memory :> bytes(tag_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 5 AES256_GCM_DEC_ALT_BUF_5BLOCK);;

let AES256_GCM_DEC_ALT_6BLOCK = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 96 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,96; tag_p,16; ivec_p,16]
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,96; key_p,240; htable_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,96; tag_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,96; key_p,240; htable_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 768; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               byte_list_at ibytes in_p (word 96) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = word (pc + 4508) /\
               read X9 s = word 96 /\
               byte_list_at (gcm_dec_pt_bytes 96 ibytes ctr0 rk) out_p (word 96) s /\
               read (memory :> bytes128 tag_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 6))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 6 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,96); memory :> bytes(tag_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 6 AES256_GCM_DEC_ALT_BUF_6BLOCK);;

let AES256_GCM_DEC_ALT_7BLOCK = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 112 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,112; tag_p,16; ivec_p,16]
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,112; key_p,240; htable_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,112; tag_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,112; key_p,240; htable_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 896; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               byte_list_at ibytes in_p (word 112) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = word (pc + 4508) /\
               read X9 s = word 112 /\
               byte_list_at (gcm_dec_pt_bytes 112 ibytes ctr0 rk) out_p (word 112) s /\
               read (memory :> bytes128 tag_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 7))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 7 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,112); memory :> bytes(tag_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 7 AES256_GCM_DEC_ALT_BUF_7BLOCK);;

let AES256_GCM_DEC_ALT_8BLOCK = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 128 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,128; tag_p,16; ivec_p,16]
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,128; key_p,240; htable_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,128; tag_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,128; key_p,240; htable_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 1024; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               byte_list_at ibytes in_p (word 128) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = word (pc + 4508) /\
               read X9 s = word 128 /\
               byte_list_at (gcm_dec_pt_bytes 128 ibytes ctr0 rk) out_p (word 128) s /\
               read (memory :> bytes128 tag_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 8))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 8 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,128); memory :> bytes(tag_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 8 AES256_GCM_DEC_ALT_BUF_8BLOCK);;

(* ---- the <=8-block dispatch theorem ----
   One readable theorem for every whole-blocks call with 1 <= nblk <= 8:
   symbolic nblk, the C argument len_bits = word (128 * nblk), byte_list_at
   input and output over the whole 16 * nblk-byte buffer, and the NIST
   vocabulary of the bands.  Proof: a case split on nblk; each case reduces
   16 * k and 128 * k to numerals and applies the band theorem. *)
let AES256_GCM_DEC_ALT_DISPATCH = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p
    nblk ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     1 <= nblk /\ nblk <= 8 /\
     LENGTH ibytes = 16 * nblk /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,16 * nblk; tag_p,16; ivec_p,16]
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,240; htable_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,240; htable_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word (128 * nblk); out_p; tag_p; ivec_p; key_p; htable_p] s /\
               byte_list_at ibytes in_p (word (16 * nblk)) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = word (pc + 4508) /\
               read X9 s = word (16 * nblk) /\
               byte_list_at (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p (word (16 * nblk)) s /\
               read (memory :> bytes128 tag_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) nblk))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter nblk ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,16 * nblk); memory :> bytes(tag_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  let bands = [AES256_GCM_DEC_ALT_1BLOCK;AES256_GCM_DEC_ALT_2BLOCK;
               AES256_GCM_DEC_ALT_3BLOCK;AES256_GCM_DEC_ALT_4BLOCK;
               AES256_GCM_DEC_ALT_5BLOCK;AES256_GCM_DEC_ALT_6BLOCK;
               AES256_GCM_DEC_ALT_7BLOCK;AES256_GCM_DEC_ALT_8BLOCK] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `nblk = 1 \/ nblk = 2 \/ nblk = 3 \/ nblk = 4 \/ nblk = 5 \/ nblk = 6 \/ nblk = 7 \/ nblk = 8`
    MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  FIRST (map (fun w -> MATCH_MP_TAC w THEN ASM_REWRITE_TAC[]) bands));;

(* ========================================================================= *)
(* End of the <=8-block chain.  Below: the proof for nblk > 8, in Secs 1 and *)
(* 3 to 12 (Sec 2, the symbolic counter layer, comes earlier, ahead of the   *)
(* band-tail ivec closer that uses it).                                      *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 1. Scalar rung lemmas: the nblk > 8 generalizations of the scalar rungs   *)
(* of the <=8-block chain (word and arithmetic lemmas, no simulation).       *)
(*                                                                           *)
(* The cmp x0,x5 at 0x3fc, 0x45c and 0xa00 feed the b.ge at 0x448 and 0x4b8  *)
(* and the b.lt at 0xa08, signed conditions on pointers.  For nblk <= 8      *)
(* x5 = in_p, so the first compare is reflexive.  For nblk > 8 the signed    *)
(* difference ival x0 - ival x5 equals ival (word_sub x0 x5) only if the     *)
(* buffer does not straddle the signed 2^63 boundary, hence the hypothesis   *)
(* val in_p + 16 * nblk < 2 EXP 63 of wbn_front_hyps_tm, which user-space    *)
(* buffers satisfy.                                                          *)
(* ------------------------------------------------------------------------- *)

(* ival (word_neg (word d)) = -- &d needs d <= 2^63 *)
let IVAL_NEG_SMALL = prove
 (`!d. d <= 2 EXP 63 ==> ival (word_neg (word d):int64) = -- &d`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_NEG] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[INT_ARITH `--(&9223372036854775808):int <= -- &d /\ -- &d < &9223372036854775808 <=> &d <= &9223372036854775808`] THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC);;

(* small pointer has exact ival *)
let IVAL_SMALL_PTR = prove
 (`!(p:int64). val p < 2 EXP 63 ==> ival p = &(val p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IVAL_VAL; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SUBGOAL_THEN `bit 63 (p:int64) <=> F` SUBST1_TAC THENL
   [MP_TAC(ISPEC `p:int64` MSB_VAL) THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[BITVAL_CLAUSES] THEN INT_ARITH_TAC]);;

(* the generic signed pointer-compare flag resolver:
   cmp x0,x5 with x0 = p + a, x5 = (word d) + p; b.ge/b.lt read NF<=>VF,
   which under no-2^63-straddle collapses to a < d *)
let WB_PTRCMP_FLAGS = prove
 (`!(in_p:int64) a d.
      val in_p + a < 2 EXP 63 /\ val in_p + d < 2 EXP 63
      ==> (ival (word_sub (word_add in_p (word a)) (word_add (word d) in_p)) < &0 <=> a < d) /\
          ((ival (word_add in_p (word a)) - ival (word_add (word d) in_p) =
            ival (word_sub (word_add in_p (word a)) (word_add (word d) in_p))) <=> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_add (word d) in_p:int64 = word_add in_p (word d)` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `ival (word_add in_p (word a):int64) = &(val in_p + a) /\
                ival (word_add in_p (word d):int64) = &(val in_p + d)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC IVAL_PTR_ADD THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word_add in_p (word a)) (word_add in_p (word d)):int64 =
                word_sub (word a) (word d)` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `ival (word_sub (word a) (word d):int64) = &a - &d` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_SUB_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  REWRITE_TAC[INT_ARITH `(&v + &a) - (&v + &d):int = &a - &d`] THEN
  REWRITE_TAC[INT_ARITH `&a - &d:int < &0 <=> &a:int < &d`; INT_OF_NUM_LT]);;

(* ------------------------------------------------------------------------- *)
(* 3. FRONT-N: the nblk > 8 front, from the entry 0x1c to the loop head      *)
(* 0x4bc, as WBN_FRONT_BUF.  Its simulated postcondition, the state s296 at  *)
(* the loop head, gives the i = 0 instance of the loop invariant (Sec 8).    *)
(*                                                                           *)
(* Against the <=8-block WB_FRONT_BUF (from 0x1c through the taken 0x448     *)
(* b.ge to the tail seam pc+3824):                                           *)
(* - the band 5 <= nblk /\ nblk <= 8 becomes 17 <= nblk /\                   *)
(*   128 * nblk < 2 EXP 64 /\ val in_p + 16 * nblk < 2 EXP 63 (the signed    *)
(*   pointer compares must not straddle 2^63), and out_p must not overlap    *)
(*   the stack frame (wbn_front_hyps_tm below);                              *)
(* - X5 = in_p + 128 * ((nblk - 1) DIV 8) rather than in_p (the _ANY scalar  *)
(*   rungs), so after the shared prefix WBN_FRONT_PREBRANCH (steps 1..267)   *)
(*   the 0x448 b.ge falls through (WB_LOOPENTER_FLAGS_GE9);                  *)
(* - steps 269..295 (0x44c..0x4b4) load input blocks 0..7, store plaintext   *)
(*   blocks 0..7 and advance the counters, with the stale Q30 facts          *)
(*   discarded (DISCARD_STALE_Q30_TAC); the 0x4b8 b.ge (step 296) falls      *)
(*   through to the loop head (WB_PTRCMP_FLAGS, D_GT_128).                   *)
(*                                                                           *)
(* As for WB_FRONT_BUF, the postcondition is the final state of the          *)
(* simulation (the keystream towers folded to aes13 by wb_front_fold_tac),   *)
(* built below with the term builders.                                       *)
(* ------------------------------------------------------------------------- *)

(* The >=17 front hypotheses: wb_front_hyps_tm with its 5 <= nblk /\ nblk <= 8
   prefix replaced by the >=17 band, keeping every other conjunct, plus
   nonoverlapping (out_p,16 * nblk) (stackpointer,80), which the <=8 hypotheses
   do not need.  The front-N stores to out_p (the four stp q,q,[x2],#32 at
   0x468..0x4ac) before the loop head; without out_p against the stack the
   stepper cannot show that these stores miss [sp+64], and it drops the
   reduction constant read (memory :> bytes64 (sp+64)) s =
   word 0xc200000000000000, which the GHASH reduction of the loop body needs
   (the [sp+64] conjunct of the invariant). *)
let wbn_front_hyps_tm =
  let _,rest1 = dest_conj wb_front_hyps_tm in
  let _,rest = dest_conj rest1 in
  mk_conj(`17 <= nblk /\ 128 * nblk < 2 EXP 64 /\ val (in_p:int64) + 16 * nblk < 2 EXP 63`,
          mk_conj(`nonoverlapping (out_p:int64,16 * nblk) (stackpointer:int64,80)`,
                  rest));;

let mk_wbn_front_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_tm, ens));;

(* The 0x4b8 b.ge (step 296): after the cmp x0,x5 at 0x45c X0 = in_p + 128 and
   X5 = in_p + d with d = 128 * ((nblk - 1) DIV 8) > 128 for nblk >= 17, so NF
   is true and VF false: it falls through to the loop head 0x4bc. *)
let WBN_RESOLVE_49C_TAC : tactic = fun (asl,w) ->
  (MP_TAC(SPECL [`in_p:int64`; `128`; `128 * (nblk - 1) DIV 8`] WB_PTRCMP_FLAGS) THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL
      [MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN NBLK_ARITH_TAC;
       MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN
       MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN NBLK_ARITH_TAC];
     ALL_TAC] THEN
   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
   MP_TAC(SPEC `nblk:num` D_GT_128) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* The front prefix, simulated once.                                         *)
(*                                                                           *)
(* The >=17 leg (WBN_FRONT_BUF, to the loop head 0x4bc) and the 9..16 leg    *)
(* (WBN_FRONT_TO_PREP_916, to the prepretail 0xa0c) run the same steps up to *)
(* the 0x4b8 b.ge, which the >=17 leg falls through and the 9..16 leg takes; *)
(* the 0x448 b.ge falls through in both.  So the prefix (0x1c to 0x4b8) is   *)
(* proved once on the union band 9 <= nblk (WBN_FRONT_PREFIX), keeping the   *)
(* raw s295 state with the NZCV facts of the cmp x0,x5 at 0x45c that the     *)
(* b.ge reads.  Each leg then resolves the branch in its own band, in a      *)
(* one-step leg chained by ENSURES_TRANS_SIMPLE.                             *)
(* ------------------------------------------------------------------------- *)

(* the union band: wbn_front_hyps_tm with 17 <= nblk relaxed to 9 <= nblk *)
let wbn_front_hyps_ge9_tm =
  let rec repl t = match t with
    | Comb(Comb(Const("/\\",_),a),b) -> mk_conj(repl a, repl b)
    | _ -> if t = `17 <= nblk` then `9 <= nblk` else t in
  repl wbn_front_hyps_tm;;

(* The 0x448 b.ge falls through whenever d = 128 * ((nblk - 1) DIV 8) >= 1,
   i.e. nblk >= 9, in both the >=17 and the 9..16 legs: the cmp x0,x5 at 0x3fc
   compares in_p with in_p + d. *)
let WB_LOOPENTER_FLAGS_GE9 = prove
 (`!(in_p:int64) nblk. 9 <= nblk /\ 128 * nblk < 2 EXP 64 /\
        val in_p + 16 * nblk < 2 EXP 63
    ==> (ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) < &0 <=> T) /\
        (ival in_p - ival (word_add (word (128 * (nblk - 1) DIV 8)) in_p) =
         ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) <=> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `d = 128 * (nblk - 1) DIV 8` THEN
  SUBGOAL_THEN `1 <= d /\ d <= 16 * nblk /\ d <= 2 EXP 63` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN
    MP_TAC(ASSUME `9 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 64`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub p (word_add (word d) p):int64 = word_neg (word d)`] THEN
  ASM_SIMP_TAC[IVAL_NEG_SMALL] THEN
  SUBGOAL_THEN `word_add (word d) in_p:int64 = word_add in_p (word d)` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `ival (word_add in_p (word d):int64) = &(val in_p + d)` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_PTR_ADD THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ival (in_p:int64) = &(val in_p)` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_SMALL_PTR THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `--(&d):int < &0 <=> &0:int < &d`; INT_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC]);;

(* the 0x448 b.ge falls through, by WB_LOOPENTER_FLAGS_GE9 *)
let WBN_RESOLVE_42C_GE9_TAC : tactic =
  MP_TAC(SPECL [`in_p:int64`; `nblk:num`] WB_LOOPENTER_FLAGS_GE9) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]));;

(* prefix goal builder (union band, postcondition at the loop-skip b.ge) *)
let mk_wbn_prefix_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_ge9_tm, ens));;

(* The s295 prefix postcondition, the state at the 0x4b8 b.ge before it
   executes: input blocks 0..7 in Q8..Q15, plaintext blocks 0..7 stored and
   5..7 still in Q5..Q7, the counters 8..12 in Q0..Q4 and Q30 = the raw
   counter + 13, with the NZCV facts of the cmp x0,x5 at 0x45c, which each leg
   resolves in its band at step 296.  It has no facts about the input buffer,
   the key schedule or the htable; WBN_FRONT_BUF_EXT and WBN_FRONT_PREFIX_EXT
   (Sec 7) add them back.  Built like wb_front_postcond, as the final state of
   the prefix simulation. *)
let wbn_front_prefix_postcond = wbp_post
 ([`aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc`;
   `read PC s = word (pc + 1208)`;
   wbp_rd `Q30` (wbp_raw_acc 12);
   wbp_out 6; wbp_out 7;
   `read X2 s = word_add out_p (word 128)`;
   wbp_out 4; wbp_out 5;
   wbp_rd `Q3` (wbp_rev_ctr 11);
   wbp_out 2; wbp_out 3;
   wbp_rd `Q0` (wbp_rev_ctr 8)] @
  wbp_cmp_flags `word_add in_p (word 128):int64`
                `word_add (word (128 * (nblk - 1) DIV 8)) in_p:int64` @
  [wbp_rd `Q12` (mk_cph 4); wbp_rd `Q13` (mk_cph 5);
   wbp_rd `Q8` (mk_cph 0); wbp_rd `Q9` (mk_cph 1);
   `read X5 s = word_add (word (128 * (nblk - 1) DIV 8)) in_p`;
   `read (memory :> bytes64 (word_add stackpointer (word 64))) s = word 13979173243358019584`;
   `read (memory :> bytes64 (word_add stackpointer (word 72))) s = word 0`;
   `read X11 s = key_p`;
   `read X9 s = word (16 * nblk)`;
   `read SP s = stackpointer`;
   `read X1 s = word (128 * nblk)`;
   `read X3 s = tag_p`;
   `read X6 s = htable_p`] @
  wbp_ctx `xi:int128` @
  [wbp_rd `Q11` (mk_cph 3); wbp_rd `Q10` (mk_cph 2);
   `read X0 s = word_add in_p (word 128)`;
   wbp_rd `Q15` (mk_cph 7); wbp_rd `Q14` (mk_cph 6);
   wbp_out 1; wbp_out 0;
   wbp_rd `Q5` (wbp_pt 5);
   wbp_rd `Q1` (wbp_rev_ctr 9); wbp_rd `Q2` (wbp_rev_ctr 10);
   wbp_rd `Q6` (wbp_pt 6); wbp_rd `Q7` (wbp_pt 7);
   wbp_rd `Q4` (wbp_rev_ctr 12)]);;

(* Input blocks 0..7 as 128-bit lanes at s267, for the ldp q8..q15 of the
   front-N (0x44c..0x458), from the input-buffer fact; the SPECL state must be
   the one ENSURES_INIT_TAC names in WBN_FRONT_PREFIX. *)
let WBN_LANES_PREBRANCH_GE9_TAC =
  SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k < 8 ==> read (memory :> bytes128 (word_add in_p (word (16 * k)))) s267 =
                  bytes_to_int128 (SUB_LIST (16 * k, 16) (ibytes:byte list))`
   MP_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s267:armstate`]
      INPUT_PREFIX_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN(fun lth -> X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `k:num` lth) THEN ANTS_TAC THENL
       [MP_TAC(ASSUME `k < 8`) THEN NBLK_ARITH_GE9_TAC; REWRITE_TAC[]]);
    DISCH_THEN(fun lth ->
      EVERY(map (fun i ->
        ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)
          (MP (SPEC (mk_small_numeral i) lth)
              (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral i) `8`)))))
        (0--7)))];;

(* The front prefix (union band 9 <= nblk): WBN_FRONT_PREBRANCH (steps 1..267,
   to the 0x448 b.ge), chained by ENSURES_TRANS_SIMPLE; then the 0x448 b.ge
   falls through (step 268, WB_LOOPENTER_FLAGS_GE9) and the front-N runs steps
   269..295 to the 0x4b8 b.ge (pc+1208, state s295). *)
let WBN_FRONT_PREFIX = prove(mk_wbn_prefix_goal wbn_front_prefix_postcond,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_front_prebranch_postcond THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_PREBRANCH THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ENSURES_INIT_TAC "s267" THEN RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
    WBN_LANES_PREBRANCH_GE9_TAC THEN WBN_RESOLVE_42C_GE9_TAC THEN
    ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (268--268) THEN
    EVERY(map (fun i -> ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (i--i) THEN
               GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_STALE_Q30_TAC) (269--295)) THEN
    wb_front_fold_tac THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC]);;

(* The s296 postcondition at the loop head, from which the i = 0 instance of
   the loop invariant follows (Sec 8): the facts of wbn_front_prefix_postcond
   one step later, after the 0x4b8 b.ge, in reverse order, with PC = pc+1212
   and without the NF and VF facts. *)
let wbn_front_postcond_i0 =
  let cs = conjuncts(snd(dest_abs wbn_front_prefix_postcond)) in
  let nf_vf c = try mem (rand(rator(lhs c))) [`NF`; `VF`] with Failure _ -> false in
  wbp_post (hd cs :: `read PC s = word (pc + 1212)` ::
            filter (not o nf_vf) (rev (tl (tl cs))));;

(* WBN_FRONT_BUF, the >=17 front: WBN_FRONT_PREFIX (0x1c to the 0x4b8 b.ge),
   chained by ENSURES_TRANS_SIMPLE, then step 296: the 0x4b8 b.ge falls through
   for 17 <= nblk (WBN_RESOLVE_49C_TAC) to the loop head 0x4bc = pc+1212.  The
   postcondition is the two-stream state at i = 0: Q8..Q15 = the raw ciphertext
   blocks 0..7, not yet folded into GHASH; Q19 = word_bytereverse xi, the GHASH
   accumulator over no blocks; the stores of blocks 0..7 done; the counters
   8..12 in Q0..Q4; X0 = in_p + 128 and X2 = out_p + 128. *)
let WBN_FRONT_BUF = prove(mk_wbn_front_goal wbn_front_postcond_i0,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_front_prefix_postcond THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_PREFIX THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ENSURES_INIT_TAC "s295" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
    WBN_RESOLVE_49C_TAC THEN
    ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (296--296) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 4. The two-stream loop invariant, at the loop head pc+0x4bc.              *)
(*                                                                           *)
(* wbn_loop_invariant_raw is WBN_FRONT_BUF's s296 postcondition generalized  *)
(* to the iteration index i.  The GHASH computation lags the stores by one   *)
(* 8-block group, so the invariant has two streams, bridged by the raw       *)
(* ciphertext blocks in Q8..Q15:                                             *)
(* - the store/counter stream runs ahead at 8(i+1): X0 = in_p + 128(i+1),    *)
(*   X2 = out_p + 128(i+1), Q0..Q4 = gcm_ctr_add (word (8i+8..8i+12)) ctr0   *)
(*   (the counters of the next group), Q5..Q7 = the plaintext blocks         *)
(*   8i+5..8i+7, the stores done for all j < 8(i+1), and                     *)
(*   Q30 = gcm_ctr_raw (word (8i+13)) ctr0;                                  *)
(* - the GHASH stream lags at 8i: Q19 = ghash_polyval_acc (byteswap128 h)    *)
(*   (word_bytereverse xi) over the byte-reversed raw ciphertext blocks      *)
(*   0..8i-1, and Q8..Q15 = the raw ciphertext blocks 8i..8i+7, not yet      *)
(*   folded in.                                                              *)
(*                                                                           *)
(* The last 17 conjuncts (the input buffer, the key schedule k0..k14 and     *)
(* htable_mem_dec) are loop constants that the simulated front postcondition *)
(* does not restate: WBN_FRONT_BUF_EXT (Sec 7) adds them, and                *)
(* WBN_LOOP_INVARIANT_ENTRY_RAW (Sec 8) derives the i = 0 instance.          *)
(*                                                                           *)
(* The loop control is the cmp x0,x5 at 0xa00 and the signed b.lt 0x4bc at   *)
(* 0xa08 (resolved by WB_PTRCMP_FLAGS); the exit falls through to the        *)
(* prepretail at 0xa0c, and the loop runs (nblk - 9) DIV 8 times.  Q26, Q27  *)
(* and Q28, which hold k12, k13 and k14 at the loop head, are not in the     *)
(* invariant: the loop body reloads them (ldp q26,q27,[x11] at 0x4c0,        *)
(* ldp q28,q26,[x11,#32] at 0x534) before their first use, and so does the   *)
(* prepretail (from 0xa0c).                                                  *)
(*                                                                           *)
(* Comments inside the quotation below have to use HOL's // syntax: OCaml    *)
(* comment brackets or a backquote there break the parse.                    *)
(* ------------------------------------------------------------------------- *)

let wbn_loop_invariant_raw = new_definition
 `wbn_loop_invariant_raw (pc:num) (ctr0:int128) (in_p:int64) (out_p:int64)
    (tag_p:int64) (ivec_p:int64) (key_p:int64) (htable_p:int64) (stackpointer:int64)
    (nblk:num) (ibytes:byte list) (xi:int128) (h:int128)
    (k0:int128) k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 (k14:int128) =
  \(i:num) (s:armstate).
    aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
    read PC s = word (pc + 1212) /\
    read Q0 s = gcm_ctr_add (word (8 * i + 8)) ctr0 /\
    read Q1 s = gcm_ctr_add (word (8 * i + 9)) ctr0 /\
    read Q2 s = gcm_ctr_add (word (8 * i + 10)) ctr0 /\
    read Q3 s = gcm_ctr_add (word (8 * i + 11)) ctr0 /\
    read Q4 s = gcm_ctr_add (word (8 * i + 12)) ctr0 /\
    read Q5 s =
    word_xor
    (word_xor (bytes_to_int128 (SUB_LIST (16 * (8 * i + 5),16) ibytes))
    (aes13 (gcm_ctr_inc_iter (8 * i + 5) ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
     k10 k11 k12 k13)) k14 /\
    read Q6 s =
    word_xor
    (word_xor (bytes_to_int128 (SUB_LIST (16 * (8 * i + 6),16) ibytes))
    (aes13 (gcm_ctr_inc_iter (8 * i + 6) ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
     k10 k11 k12 k13)) k14 /\
    read Q7 s =
    word_xor
    (word_xor (bytes_to_int128 (SUB_LIST (16 * (8 * i + 7),16) ibytes))
    (aes13 (gcm_ctr_inc_iter (8 * i + 7) ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
     k10 k11 k12 k13)) k14 /\
    read Q8 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 0),16) ibytes) /\
    read Q9 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 1),16) ibytes) /\
    read Q10 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 2),16) ibytes) /\
    read Q11 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 3),16) ibytes) /\
    read Q12 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 4),16) ibytes) /\
    read Q13 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 5),16) ibytes) /\
    read Q14 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 6),16) ibytes) /\
    read Q15 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 7),16) ibytes) /\
    read Q19 s =
    ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
    (MAP word_bytereverse
    (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) (8 * i))) /\
    read X0 s = word_add in_p (word (128 * (i + 1))) /\
    read X2 s = word_add out_p (word (128 * (i + 1))) /\
    read X4 s = word_add in_p (word (16 * nblk)) /\
    read X5 s = word_add (word (128 * (nblk - 1) DIV 8)) in_p /\
    read X9 s = word (16 * nblk) /\
    read X10 s = word_add stackpointer (word 64) /\
    read X1 s = word (128 * nblk) /\
    read X15 s = word 4294967296 /\
    read Q31 s = word 79228162514264337593543950336 /\
    read Q30 s = gcm_ctr_raw (word (8 * i + 13)) ctr0 /\
    read X16 s = ivec_p /\
    read X6 s = htable_p /\
    read X3 s = tag_p /\
    read X11 s = key_p /\
    read SP s = stackpointer /\
    read (memory :> bytes64 (word_add stackpointer (word 64))) s =
    word 13979173243358019584 /\
    (!j. j < 8 * (i + 1)
         ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
             word_xor
             (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16) ibytes))
             (aes13 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
              k10 k11 k12 k13)) k14) /\
    read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes /\
    read (memory :> bytes128 key_p) s = k0 /\
    read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
    read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
    read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
    read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
    read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
    read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
    read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
    read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
    read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
    read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
    read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
    read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
    read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
    read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
    htable_mem_dec h htable_p s`;;

let WBN_MACHINE_REDUCE_IS_PROP3_PACK = prove
 (`!PL PH PM:int128.
     word_xor
      (word_xor PH
       (word_subword
        (word_join
         (word_xor
          (word_xor (word_xor (word_xor PM PL) PH)
          (word_pmul (word_subword PL (0,64) :64 word) (word 13979173243358019584 :64 word)))
         (word_subword (word_join PL PL :256 word) (64,128)))
        (word_xor
         (word_xor (word_xor (word_xor PM PL) PH)
         (word_pmul (word_subword PL (0,64) :64 word) (word 13979173243358019584 :64 word)))
        (word_subword (word_join PL PL :256 word) (64,128))) :256 word)
       (64,128)))
      (word_pmul
       (word_subword
        (word_xor
         (word_xor (word_xor (word_xor PM PL) PH)
         (word_pmul (word_subword PL (0,64) :64 word) (word 13979173243358019584 :64 word)))
        (word_subword (word_join PL PL :256 word) (64,128)))
       (0,64) :64 word)
      (word 13979173243358019584 :64 word)) =
     polyval_reduce_prop3 (pack_corrected PL PH PM)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PACK_CORRECTED_KARATSUBA_JOIN;
              GSYM POLYVAL_REDUCE_G2_KARATSUBA_JOIN] THEN
  REWRITE_TAC[polyval_reduce_g2; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `w1:int128 = word_pmul (word_subword (PL:int128) (0,64):64 word)
                                    (word 13979173243358019584:64 word)` THEN
  SUBGOAL_THEN
   `word_subword
      (word_xor (word_xor (word_xor (word_xor PM PL) PH) (w1:int128))
                (word_subword (word_join (PL:int128) PL :256 word) (64,128)))
      (0,64) :64 word =
    word_xor (word_xor (word_subword w1 (0,64)) (word_subword PL (64,64)))
             (word_subword (word_xor (word_xor PL PH) PM) (0,64))`
   SUBST1_TAC THENL [BITBLAST_TAC; ALL_TAC] THEN
  ABBREV_TAC `w2:int128 = word_pmul
     (word_xor (word_xor (word_subword (w1:int128) (0,64):64 word)
                         (word_subword (PL:int128) (64,64)))
               (word_subword (word_xor (word_xor PL PH) PM) (0,64)))
     (word 13979173243358019584:64 word)` THEN
  BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Compose the value equality into the Q19 close.                            *)
(*                                                                           *)
(* build_q19_reduce_clean pl_t ph_t pm_t: from the three accumulator terms   *)
(* at the wire-in state (read Q17/Q19/Q18 there, over h, xi, ibytes and i),  *)
(* the theorem                                                               *)
(*   |- <machine reduce byteform> =                                          *)
(*        ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)            *)
(*          (MAP word_bytereverse (list_of_seq blk (8*(i+1))))               *)
(* the invariant's Q19 at i+1.  It chains                                    *)
(*   reduce_id   : byteform = polyval_reduce_prop3 (pack_corrected PL PH PM) *)
(*                 [WBN_MACHINE_REDUCE_IS_PROP3_PACK]                        *)
(*   KARA_PACK_EQ: pack_corrected PL PH PM = SPEC_TOWERS, under kqok         *)
(*                 [PROJ_PL, PROJ_PH, PROJ_PM, KARA_ACC_PACK_HELPER]         *)
(*   body_ready2 : ghash..(8(i+1)) = polyval_reduce_prop3 SPEC_TOWERS        *)
(*                 [BODY_Q19_CLOSE_ALGEBRA, BYTESWAP128_INVOLUTION]          *)
(* The eight kqok side conditions (word_subword hk_j (0,64) =                *)
(* karatsuba_mid ..) are discharged by instantiating                         *)
(* hk_j := word_join (word 0) (karatsuba_mid ..), after which each holds by  *)
(* WORD_BLAST; PROJ_PM is proved with the hk_j free, under the kqok          *)
(* hypotheses, and instantiated afterwards.                                  *)
(* ------------------------------------------------------------------------- *)

(* build_q19_reduce_clean_idx idx: the same construction for the fold at index
   idx, for the prepretail's Q19 close (idx = k = (nblk-9) DIV 8, where the
   loop body has i).  Only the instantiation i := idx of BODY_Q19_CLOSE_ALGEBRA
   depends on the index, not the reduce identity or the block algebra. *)
let build_q19_reduce_clean_idx idx pl_t ph_t pm_t =
  let bsh = `byteswap128 h` in
  let rec tower n = if n <= 1 then bsh else mk_comb(mk_comb(`polyval_dot`, tower(n-1)), bsh) in
  let inst_list = map (fun n -> (mk_comb(`byteswap128`, tower n), mk_var("h"^string_of_int n, `:int128`))) (2--8) in
  let body_base = INST [idx, `i:num`] BODY_Q19_CLOSE_ALGEBRA in
  let body_inst2 = INST inst_list body_base in
  let body_ready2 = REWRITE_RULE[BYTESWAP128_INVOLUTION]
       (MP body_inst2 (prove(fst(dest_imp(concl body_inst2)), REWRITE_TAC[BYTESWAP128_INVOLUTION]))) in
  let spec_towers = rand(rhs(concl body_ready2)) in
  let rec strip_xor t = match t with Comb(Comb(Const("word_xor",_),a),b) -> strip_xor a @ strip_xor b | _ -> [t] in
  let spec_leaves = strip_xor spec_towers in
  let spec_input j = rand(rator (List.nth spec_leaves j)) in
  let mk_quadT j = let inp = spec_input j in let tw = tower(8-j) in
    mk_pair(inp, mk_pair(mk_comb(`byteswap128`, tw), mk_pair(mk_var("hk"^string_of_int j, `:int128`), tw))) in
  let quadsT = mk_list(map mk_quadT (0--7), `:int128#int128#int128#int128`) in
  let kqok_hyp j = mk_eq(mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, mk_var("hk"^string_of_int j,`:int128`)), `(0,64)`),
                  mk_comb(`karatsuba_mid`, mk_comb(`byteswap128`, tower (8-j)))) in
  let kqok_hyps = map kqok_hyp (0--7) in
  let projtac = REWRITE_TAC[project_triples; kara_acc; karatsuba_block_pl; karatsuba_block_ph; karatsuba_block_pm] THEN
      CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; SND] in
  let mk_proj sel concrete = mk_eq(mk_comb(sel, subst [quadsT, `QUADS:(int128#int128#int128#int128)list`]
              `kara_acc (project_triples QUADS) (word 0:int128) (word 0:int128) (word 0:int128)`), concrete) in
  let PROJ_PL = BETA_RULE(prove(mk_proj `FST:int128#int128#int128->int128` pl_t,
     projtac THEN REWRITE_TAC[GSYM BREV_RF8_128; LANE_COLLAPSE; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let PROJ_PH = BETA_RULE(prove(mk_proj `\t:int128#int128#int128. FST(SND t)` ph_t,
     projtac THEN REWRITE_TAC[GSYM BREV_RF8_128; LANE_COLLAPSE; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let PROJ_PM = BETA_RULE(prove(mk_imp(list_mk_conj kqok_hyps, mk_proj `\t:int128#int128#int128. SND(SND t)` pm_t),
     STRIP_TAC THEN projtac THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[GSYM BREV_RF8_128; LANE_COLLAPSE_PM_A; LANE_COLLAPSE_PM_B; PM_LANE_HI'; PM_LANE_LO'; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let kp = rand(lhs(concl PROJ_PL)) in
  let KARA_QUAD_OK_T = prove(mk_imp(list_mk_conj kqok_hyps, mk_comb(`kara_quad_ok`, quadsT)),
    STRIP_TAC THEN REWRITE_TAC[kara_quad_ok] THEN REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC KMID_BYTESWAP_INV) in
  let TESTQT = prove(mk_eq(subst [quadsT, `QUADS:(int128#int128#int128#int128)list`] `kara_quad_pmul QUADS (word 0:256 word)`, spec_towers),
    REWRITE_TAC[kara_quad_pmul; WORD_XOR_0_LEFT] THEN CONV_TAC WORD_RULE) in
  let helper = MP (SPECL [quadsT; `word 0:256 word`] KARA_ACC_PACK_HELPER)
                  (MP KARA_QUAD_OK_T (end_itlist CONJ (map ASSUME kqok_hyps))) in
  let KARA_PACK_EQ = prove(mk_imp(list_mk_conj kqok_hyps,
        mk_eq(list_mk_comb(`pack_corrected`, [pl_t; ph_t; pm_t]), spec_towers)),
    STRIP_TAC THEN
    (let pm_thm = MP PROJ_PM (end_itlist CONJ (map ASSUME kqok_hyps)) in
     let sndkp = mk_comb(`SND:int128#int128#int128->int128#int128`, kp) in
     let sndkp_eq = TRANS (GSYM(ISPEC sndkp PAIR)) (MK_COMB(AP_TERM `(,):int128->int128->int128#int128` PROJ_PH, pm_thm)) in
     let kp_triple = TRANS (GSYM(ISPEC kp PAIR)) (MK_COMB(AP_TERM `(,):int128->int128#int128->int128#int128#int128` PROJ_PL, sndkp_eq)) in
     REWRITE_TAC[GSYM TESTQT] THEN MP_TAC helper THEN
     REWRITE_TAC[LET_DEF; LET_END_DEF] THEN SUBST1_TAC kp_triple THEN
     CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[WORD_XOR_0_LEFT] THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC)) in
  let reduce_id = SPECL [pl_t;ph_t;pm_t] WBN_MACHINE_REDUCE_IS_PROP3_PACK in
  let q19_final = TRANS (TRANS reduce_id (AP_TERM `polyval_reduce_prop3` (UNDISCH_ALL KARA_PACK_EQ))) (SYM body_ready2) in
  let q19_disch = itlist DISCH (hyp q19_final) q19_final in
  let hk_inst = map (fun j ->
     let kmid = mk_comb(`karatsuba_mid`, mk_comb(`byteswap128`, tower (8-j))) in
     (mk_comb(mk_comb(`word_join:64 word->64 word->128 word`, `word 0:64 word`), kmid),
      mk_var("hk"^string_of_int j, `:int128`))) (0--7) in
  let inst_thm = INST hk_inst q19_disch in
  MP inst_thm (prove(fst(dest_imp(concl inst_thm)),
     REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST));;

let build_q19_reduce_clean pl_t ph_t pm_t =
  build_q19_reduce_clean_idx `i:num` pl_t ph_t pm_t;;

let WBN_Q19_CLOSE_TAC : tactic =
  fun (asl,w) ->
    let clean = build_q19_reduce_clean (!wbn_q19_pl) (!wbn_q19_ph) (!wbn_q19_pm) in
    let defthms = filter (fun th -> match concl th with
      | Comb(Comb(Const("=",_),_),Var(("PL"|"PH"|"PM"),_)) -> true | _ -> false) (map snd asl) in
    let clean' = REWRITE_RULE (ARITH_RULE `8 * (i + 1) = 8 * i + 8` :: defthms) clean in
    ACCEPT_TAC clean' (asl,w);;

(* WBN_Q19_PREPRETAIL_CLOSE_TAC idx closes the two GHASH conjuncts of the    *)
(* prepretail postcondition, Q19 = ghash..(8*(k+1)) and its staging copy     *)
(* Q16 = word_subword (word_join <caught_up> <caught_up>) (64,128); the      *)
(* caller applies it, after ENSURES_FINAL_STATE_TAC and REPEAT CONJ_TAC, to  *)
(* the conjuncts that mention ghash_polyval_acc.  idx is the prepretail      *)
(* index (`k:num`).  ASM_REWRITE_TAC substitutes the machine byteform, the   *)
(* value equality of build_q19_reduce_clean_idx folds it to ghash..(8*k+8),  *)
(* and rewriting 8*k+8 to 8*(k+1) leaves an identity.                        *)
let WBN_Q19_PREPRETAIL_CLOSE_TAC (idx:term) : tactic =
  fun (asl,w) ->
    let clean = build_q19_reduce_clean_idx idx (!wbn_q19_pl) (!wbn_q19_ph) (!wbn_q19_pm) in
    let defthms = filter (fun th -> match concl th with
      | Comb(Comb(Const("=",_),_),Var(("PL"|"PH"|"PM"),_)) -> true | _ -> false) (map snd asl) in
    let clean' = REWRITE_RULE (ARITH_RULE `8 * (i + 1) = 8 * i + 8` :: defthms) clean in
    (ASM_REWRITE_TAC[] THEN REWRITE_TAC[clean'] THEN
     REWRITE_TAC[ARITH_RULE `8 * k + 8 = 8 * (k + 1)`] THEN
     TRY REFL_TAC) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* 6. Strengthening an ensures postcondition with a fact the frame           *)
(* preserves, without re-simulation.                                         *)
(*                                                                           *)
(* From `ensures step P Q C` and `!s s'. P s /\ C s s' ==> R s'`,            *)
(* ENSURES_ADD_PRESERVED gives `ensures step P (\s. Q s /\ R s) C`.          *)
(* WBN_FRONT_BUF_EXT and WBN_FRONT_PREFIX_EXT (Sec 7) use it to add the loop *)
(* constants R (wbn_front_R_tm: the input buffer, the key schedule k0..k14   *)
(* and htable_mem_dec) to the front postconditions: the front frame          *)
(* wb_front_frame_tm writes only out_p, tag_p, ivec_p, the stack slot        *)
(* [sp+64,sp+80) and registers, which the nonoverlapping hypotheses keep     *)
(* apart from in_p, key_p and htable_p.  The recomposition of Sec 12 uses it *)
(* to carry the stores of the first output blocks through the tail legs.     *)
(* ------------------------------------------------------------------------- *)

let ENSURES_ADD_PRESERVED = prove
 (`!(step:A->A->bool) P Q R C.
    ensures step P Q C /\ (!s s'. P s /\ C s s' ==> R s')
    ==> ensures step P (\s. Q s /\ R s) C`,
  REWRITE_TAC[ensures] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `s0:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!s':A. Q s' /\ C (s0:A) s' ==> (Q s' /\ R s') /\ C s0 s'`
    (MP_TAC o MATCH_MP EVENTUALLY_MONO) THENL
   [X_GEN_TAC `s1:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`s0:A`;`s1:A`] th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    DISCH_THEN(MP_TAC o SPECL [`step:A->A->bool`; `s0:A`]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 7. WBN_FRONT_BUF_EXT: the front with the loop constants re-asserted.      *)
(*                                                                           *)
(* The i = 0 invariant needs the loop constants R at the loop head (the      *)
(* input buffer, the 15 key reads k0..k14 and htable_mem_dec,                *)
(* wbn_front_R_tm), which WBN_FRONT_BUF's simulated postcondition does not   *)
(* restate.  The front frame preserves them provided out_p is disjoint from  *)
(* in_p, key_p and htable_p; wbn_front_hyps_tm does not have those three     *)
(* disjointness conjuncts, so wbn_front_hyps_wide_tm adds them.              *)
(* WBN_FRONT_BUF_EXT is ENSURES_ADD_PRESERVED applied to WBN_FRONT_BUF       *)
(* (whose hypotheses the wide ones imply) and to the preservation            *)
(* obligation, which needs no simulation: the frame is unfolded and each     *)
(* read of R is pushed through the writes by WBN_PUSH_LHS_READ_TAC.          *)
(* ------------------------------------------------------------------------- *)

(* the wide >=17 hypotheses: wbn_front_hyps_tm plus the disjointness of out_p
   from in_p, key_p and htable_p *)
let wbn_front_hyps_wide_tm =
  mk_conj(wbn_front_hyps_tm,
    `nonoverlapping (out_p:int64,16 * nblk) (in_p:int64,16 * nblk) /\
     nonoverlapping (out_p:int64,16 * nblk) (key_p:int64,240) /\
     nonoverlapping (out_p:int64,16 * nblk) (htable_p:int64,192)`);;

(* the WBN_FRONT_BUF pieces: P = precondition, Q0 = simulated postcondition,
   C = frame *)
let wbn_front_P_tm, wbn_front_Q0_tm, wbn_front_C_tm =
  let ens = snd(dest_imp(snd(strip_forall(concl WBN_FRONT_BUF)))) in
  rand(rator(rator ens)), rand(rator ens), rand ens;;

(* R = the loop constants (the input buffer, k0..k14, htable_mem_dec), spelled
   as wbn_loop_invariant_raw states them *)
let wbn_front_R_tm =
  let sv = fst(dest_abs wbn_front_P_tm) in
  mk_abs(sv, list_mk_conj
    [`read (memory :> bytes (in_p:int64,16 * nblk)) s = num_of_bytelist ibytes`;
     `read (memory :> bytes128 (key_p:int64)) s = (k0:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 16))) s = (k1:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 32))) s = (k2:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 48))) s = (k3:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 64))) s = (k4:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 80))) s = (k5:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 96))) s = (k6:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 112))) s = (k7:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 128))) s = (k8:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 144))) s = (k9:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 160))) s = (k10:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 176))) s = (k11:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 192))) s = (k12:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 208))) s = (k13:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 224))) s = (k14:int128)`;
     `htable_mem_dec h (htable_p:int64) s`]);;

(* the EXT goal: wide hypotheses ==> ensures arm P (\s. Q0 s /\ R s) C *)
let wbn_front_ext_goal =
  let newQ = mk_abs(fst(dest_abs wbn_front_P_tm),
    mk_conj(rhs(concl(BETA_CONV(mk_comb(wbn_front_Q0_tm,fst(dest_abs wbn_front_P_tm))))),
            rhs(concl(BETA_CONV(mk_comb(wbn_front_R_tm,fst(dest_abs wbn_front_P_tm))))))) in
  let ens = list_mk_comb(`ensures arm`,[wbn_front_P_tm; newQ; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_FRONT_BUF_EXT = prove(wbn_front_ext_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_ADD_PRESERVED THEN CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_BUF THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[htable_mem_dec] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC(REDEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    CONV_TAC(REDEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_eq(concl th) &&
        (match rhs(concl th) with Var("s'",_) -> true | _ -> false))) THEN
    WBN_PUSH_LHS_READ_TAC]);;

(* ------------------------------------------------------------------------- *)
(* WBN_FRONT_PREFIX_EXT: the shared prefix with the loop constants R         *)
(* re-asserted, so that the 9..16 front leg (WBN_FRONT_TO_PREP_916, whose    *)
(* postcondition wbn_core_applied 0 states the key and htable reads) reuses  *)
(* the one prefix simulation.  As for WBN_FRONT_BUF_EXT, R is preserved      *)
(* through the front frame (ENSURES_ADD_PRESERVED).  The band is             *)
(* wbn_front_hyps_ge9_wide_tm, the wide hypotheses that                      *)
(* WBN_PUSH_LHS_READ_TAC needs to push the reads of R past the out_p stores; *)
(* the 9..16 leg discharges it by strengthening its hypotheses.              *)
(* (WBN_FRONT_BUF needs no R and uses the plain WBN_FRONT_PREFIX.)           *)
(* ------------------------------------------------------------------------- *)

(* the wide hypotheses with 17 <= nblk relaxed to 9 <= nblk: the band of
   WBN_FRONT_PREFIX_EXT *)
let wbn_front_hyps_ge9_wide_tm =
  let rec repl t = match t with
    | Comb(Comb(Const("/\\",_),a),b) -> mk_conj(repl a, repl b)
    | _ -> if t = `17 <= nblk` then `9 <= nblk` else t in
  repl wbn_front_hyps_wide_tm;;

let wbn_front_prefix_ext_goal =
  let sv = fst(dest_abs wbn_front_prefix_postcond) in
  let newQ = mk_abs(sv,
    mk_conj(rhs(concl(BETA_CONV(mk_comb(wbn_front_prefix_postcond,sv)))),
            rhs(concl(BETA_CONV(mk_comb(wbn_front_R_tm,sv)))))) in
  let ens = list_mk_comb(`ensures arm`,[wbn_front_P_tm; newQ; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_ge9_wide_tm, ens));;

let WBN_FRONT_PREFIX_EXT = prove(wbn_front_prefix_ext_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_ADD_PRESERVED THEN CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_PREFIX THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[htable_mem_dec] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC(REDEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    CONV_TAC(REDEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_eq(concl th) &&
        (match rhs(concl th) with Var("s'",_) -> true | _ -> false))) THEN
    WBN_PUSH_LHS_READ_TAC]);;

(* the strengthened prefix postcondition (prefix post /\ R) *)
let wbn_front_prefix_ext_post =
  rand(rator(snd(dest_imp(snd(strip_forall(concl WBN_FRONT_PREFIX_EXT))))));;

(* ------------------------------------------------------------------------- *)
(* 8. WBN_LOOP_INVARIANT_ENTRY_RAW: the front reaches the i = 0 invariant,   *)
(*   ensures arm (\s. decodes /\ PC = pc+0x1c /\ precondition s)             *)
(*     (\s. decodes /\ PC = pc+0x4bc /\ wbn_loop_invariant_raw ... 0 s)      *)
(*     frame                                                                 *)
(* the first leg of WBN_FRONT_TO_PREP_EXT2 (Sec 12), which chains it with    *)
(* the loop and the prepretail by ENSURES_TRANS_SIMPLE.  It weakens the      *)
(* postcondition Q0 /\ R of WBN_FRONT_BUF_EXT to the i = 0 invariant by      *)
(* ENSURES_POSTCONDITION_THM: one simplification brings the counter terms of *)
(* both sides to the same gcm_ctr_add form (GCM_CTR_ADD_LANES,               *)
(* GCM_CTR_INC_LANES .. GCM_CTR_INC7_LANES, GCM_CTR_INC_ITER_AS_ADD), the    *)
(* GHASH fold over no blocks is the reversed tag, the store forall for j < 8 *)
(* expands to the eight stores, and a numeral normalization (0 + n, 16 * (0  *)
(* + k), block 0 = ctr0 by GCM_CTR_ADD_0) closes the rest against the        *)
(* postcondition; the raw counter Q30 (the front's base + 12, then + 1) is   *)
(* gcm_ctr_raw (word 13) ctr0.                                               *)
(* ------------------------------------------------------------------------- *)

(* the invariant applied to its 28 parameters, as a num->armstate->bool *)
let wbn_inv_applied =
  list_mk_comb(`wbn_loop_invariant_raw`,
    [`pc:num`;`ctr0:int128`;`in_p:int64`;`out_p:int64`;`tag_p:int64`;`ivec_p:int64`;
     `key_p:int64`;`htable_p:int64`;`stackpointer:int64`;`nblk:num`;`ibytes:byte list`;
     `xi:int128`;`h:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;
     `k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;
     `k12:int128`;`k13:int128`;`k14:int128`]);;

(* post = \s. decodes /\ PC = pc+0x4bc /\ inv 0 s *)
let wbn_entry_post =
  subst [wbn_inv_applied,`INVAPP:num->armstate->bool`]
    `\s:armstate. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
                  read PC s = word (pc + 0x4bc) /\
                  INVAPP (0:num) s`;;

let wbn_entry_goal =
  let ens = list_mk_comb(`ensures arm`,[wbn_front_P_tm; wbn_entry_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

(* the Q to weaken from: WBN_FRONT_BUF_EXT's postcondition \s. Q0 s /\ R s *)
let wbn_extQ =
  let sv = fst(dest_abs wbn_front_P_tm) in
  mk_abs(sv, mk_conj(
    rhs(concl(BETA_CONV(mk_comb(wbn_front_Q0_tm,sv)))),
    rhs(concl(BETA_CONV(mk_comb(wbn_front_R_tm,sv)))))) ;;

let WBN_LOOP_INVARIANT_ENTRY_RAW = prove(wbn_entry_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC wbn_extQ THEN CONJ_TAC THENL
   [(* (Q0 x /\ R x) ==> decodes /\ PC=pc+0x4bc /\ inv 0 x *)
    GEN_TAC THEN REWRITE_TAC[wbn_loop_invariant_raw] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
    REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD; GCM_CTR_ADD_1; GSYM GCM_CTR_ADD_LANES] THEN
    REWRITE_TAC[list_of_seq; MAP; ghash_polyval_acc] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES;
       GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES; GCM_CTR_INC5_LANES;
       GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
    REWRITE_TAC[GCM_CTR_ADD_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
    (* numeral normalization: 0+n, 16*(0+k), block 0 = ctr0 *)
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM GCM_CTR_ADD_LANES; GCM_CTR_ADD_0] THEN
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[GCM_CTR_ADD_0] THEN
    (* Q30 residual: the only conjunct the closer leaves open.  The i=0 raw
       tower (top lane += 12 then += 1) collapses to gcm_ctr_raw (word 13) ctr0
       = the invariant's 8*0+13 value. *)
    REWRITE_TAC[gcm_ctr_raw_def;
      WORD_RULE `word_add (word_add (x:32 word) (word 12)) (word 1) =
                 word_add x (word 13)`;
      WORD_ADD_0];
    (* the ensures = WBN_FRONT_BUF_EXT *)
    MATCH_MP_TAC WBN_FRONT_BUF_EXT THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 9. The PC- and decode-free core of the invariant, and its split.          *)
(*                                                                           *)
(* The first two conjuncts of wbn_loop_invariant_raw are                     *)
(*   C1  aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc             *)
(*   C2  read PC s = word (pc + 1212)                    (the loop head)     *)
(* The ENSURES_WHILE tactics put program_decodes and `read PC s = word pcX`  *)
(* around the loop invariant themselves, at the loop head pc1 and at the     *)
(* exit pc2, so a PC inside the invariant would be redundant at pc1 and      *)
(* contradictory at pc2 (it would force PC = pc+0x4bc at the exit pc+0xa0c). *)
(* So the loop is stated with wbn_loop_inv_core_raw, the invariant without   *)
(* C1 and C2 (built by dropping the first two conjuncts of the definition,   *)
(* so the two stay in step), and WBN_INV_RAW_SPLIT relates the two forms:    *)
(*   wbn_loop_invariant_raw ... i s <=>                                      *)
(*     aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\            *)
(*     read PC s = word (pc + 1212) /\ wbn_loop_inv_core_raw ... i s         *)
(* The entry theorem gives the left-hand side at i = 0, and the body and the *)
(* exit carry only the core across the frame.                                *)
(* ------------------------------------------------------------------------- *)

let wbn_loop_inv_core_raw =
  let eqn = snd(strip_forall(concl wbn_loop_invariant_raw)) in
  let lhs_full, rhs_full = dest_eq eqn in
  let hd, params = strip_comb lhs_full in
  let ivars, body = strip_abs rhs_full in
  let cs = conjuncts body in
  (* drop C1 (aligned_bytes_loaded) and C2 (read PC) *)
  let core_body = list_mk_conj (List.tl (List.tl cs)) in
  let core_rhs = list_mk_abs(ivars, core_body) in
  let newhead = mk_var("wbn_loop_inv_core_raw", type_of hd) in
  new_definition (mk_eq(list_mk_comb(newhead, params), core_rhs));;

let wbn_inv_args =
  snd(strip_comb(fst(dest_eq(snd(strip_forall(concl wbn_loop_invariant_raw))))));;

let WBN_INV_RAW_SPLIT = prove
 (list_mk_forall(wbn_inv_args @ [`i:num`;`s:armstate`],
    mk_eq(
      list_mk_comb(`wbn_loop_invariant_raw`, wbn_inv_args @ [`i:num`;`s:armstate`]),
      list_mk_conj[
        `aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc`;
        `read PC s = word (pc + 1212)`;
        list_mk_comb(`wbn_loop_inv_core_raw`, wbn_inv_args @ [`i:num`;`s:armstate`])])),
  REWRITE_TAC[wbn_loop_invariant_raw; wbn_loop_inv_core_raw] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[CONJ_ACI]);;

(* ------------------------------------------------------------------------- *)
(* 10. The ENSURES_WHILE skeleton for WBN_MAIN_LOOP_raw.                     *)
(*                                                                           *)
(* The back-edge of L256_dec_main_loop is                                    *)
(*   cmp x0,x5 @0xa00 ; stp q6,q7,[x2],#32 @0xa04 ; b.lt 0x4bc @0xa08        *)
(* so the signed b.lt is the last body instruction and its cmp is two        *)
(* instructions earlier, both inside the body, and the flags need not be     *)
(* carried in the invariant.  That is the ENSURES_WHILE_UP2_TAC shape, where *)
(* the body postcondition's PC is                                            *)
(*   word (if i + 1 < k then pc1 else pc2)                                   *)
(* and the exit is the fall-through pc2; here                                *)
(*   k = (nblk - 9) DIV 8, pc1 = pc+0x4bc (the loop head),                   *)
(*   pc2 = pc+0xa0c (the exit).                                              *)
(*                                                                           *)
(* ENSURES_WHILE_UP2_TAC proves its `C ,, C = C` premise with                *)
(* MAYCHANGE_IDEMPOT_TAC, which fails on this frame while                    *)
(* MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI is folded.  So up2_pth          *)
(* re-proves the theorem inside the tactic (pth in common/relational.ml),    *)
(* and UP2_ABI_TAC applies it as ENSURES_WHILE_UP2_TAC does, with the ABI    *)
(* macro expanded before MAYCHANGE_IDEMPOT_TAC.                              *)
(* ------------------------------------------------------------------------- *)

(* the core applied to its parameters, as a num->armstate->bool and as \i s. *)
let wbn_core_applied =
  list_mk_comb(`wbn_loop_inv_core_raw`,
    [`pc:num`;`ctr0:int128`;`in_p:int64`;`out_p:int64`;`tag_p:int64`;`ivec_p:int64`;
     `key_p:int64`;`htable_p:int64`;`stackpointer:int64`;`nblk:num`;`ibytes:byte list`;
     `xi:int128`;`h:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;
     `k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;
     `k12:int128`;`k13:int128`;`k14:int128`]);;

let wbn_core_iv = list_mk_abs([`i:num`;`s:armstate`],
  mk_comb(mk_comb(wbn_core_applied,`i:num`),`s:armstate`));;

(* ENSURES_WHILE_UP2_TAC's internal theorem pth (common/relational.ml),
   re-proved here for UP2_ABI_TAC, which proves its idempotence premise
   differently *)
let up2_pth = prove(
  `forall k pc1 pc2 (loopinv:num->A->bool) C precond postcond
      (pcounter:(A,(N)word)component) step pc.
    C ,, C = C /\ ~(k = 0) /\
    ensures step
      (\s. program_decodes s /\ read pcounter s = word pc /\ precond s)
      (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinv 0 s)
      C /\
    (forall i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
      ==> ensures step
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinv i s)
        (\s. program_decodes s /\
             read pcounter s = word (if i + 1 < k then pc1 else pc2) /\
             loopinv (i + 1) s)
        C) /\
    ensures step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinv k s)
        postcond C
    ==>
    ensures step
      (\s. program_decodes s /\ read pcounter s = word pc /\ precond s)
      postcond C`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "HC HK HPRE HLOOP HPOST" THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
  META_EXISTS_TAC THEN CONJ_TAC THENL
  [ALL_TAC; USE_THEN "HPOST" (UNIFY_ACCEPT_TAC [`Q:A->bool`])] THEN
  REMOVE_THEN "HPOST" (K ALL_TAC) THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
  EXISTS_TAC `(\(s:A). program_decodes s /\
                       read pcounter s = (word pc1:(N)word) /\
                       loopinv (k - 1) s)` THEN
  CONJ_TAC THENL [
    ALL_TAC;
    USE_THEN "HLOOP" (fun th -> MP_TAC (SPEC `(k-1)` th)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `k - 1 + 1 = k` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC]
    THEN REWRITE_TAC[LT_REFL]
  ] THEN
  SUBGOAL_THEN `k - 1 < k` MP_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  SPEC_TAC (`k - 1`,`j:num`) THEN INDUCT_TAC THENL [
    ASM_REWRITE_TAC[] THEN NO_TAC;
    FIRST_X_ASSUM (fun th -> DISCH_TAC THEN MP_TAC th) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN (LABEL_TAC "HPREVLOOP") THEN
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
    META_EXISTS_TAC THEN CONJ_TAC THENL
    [USE_THEN "HPREVLOOP" (UNIFY_ACCEPT_TAC [`Q:A->bool`]); ALL_TAC] THEN
    USE_THEN "HLOOP" (fun th -> MP_TAC (SPEC `j:num` th)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM ADD1] THEN NO_TAC
  ]);;

(* ENSURES_WHILE_UP2_TAC with MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI
   expanded before MAYCHANGE_IDEMPOT_TAC. *)
let UP2_ABI_TAC k pc1 pc2 iv =
  MATCH_MP_TAC up2_pth THEN
  MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv] THEN
  BETA_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC];;

let WBN_RAWCT_READ = prove
 (`i < (nblk - 9) DIV 8 /\ 9 <= nblk /\
   LENGTH (ibytes:byte list) = 16 * nblk /\
   read (memory :> bytes (in_p:int64, 16 * nblk)) s = num_of_bytelist ibytes
   ==> !m. m < 8
       ==> read (memory :> bytes128 (word_add in_p (word (16 * (8*(i+1)+m))))) s =
           bytes_to_int128 (SUB_LIST (16 * (8*(i+1)+m), 16) ibytes)`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s:armstate`]
    INPUT_PREFIX_TO_BYTE128_LANES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL] THEN
    SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` SUBST1_TAC THENL
     [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC_ALL WBN_RAWCT_BOUND) THEN ASM_SIMP_TAC[]]);;

(* 9 <= nblk from a nonzero loop count *)
let WBN_NBLK_GE_9 = prove
 (`0 < (nblk - 9) DIV 8 ==> 9 <= nblk`,
  MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 10b. Loop-body postcondition machinery.                                   *)
(*                                                                           *)
(* The body's postcondition conjuncts close once these sub-problems are      *)
(* solved.                                                                   *)
(*                                                                           *)
(* (A) Q8..Q15, the raw ciphertext of the next group.  Right after each ldp  *)
(* (step 221 from s220, 273 from s272, 306 from s305, 309 from s308) the     *)
(* stepper gives                                                             *)
(*   read Qk sN = read (memory :> bytes128 ADDR) s(N-1),                     *)
(* a read at the old state, which cannot be closed once s(N-1) is discarded. *)
(* RAWCT_LEMMA_AT "s(N-1)" assumes the WBN_RAWCT_READ !m lemma at that       *)
(* state, and RESOLVE_LDP2_TAC (with RESOLVE_QREG_C, Sec 10c) rewrites read  *)
(* Qk sN to                                                                  *)
(*   bytes_to_int128 (SUB_LIST (16*(8*(i+1)+m),16) ibytes)                   *)
(* for m = 0..7 (Q8..Q15 in load order).  The stepper then carries this      *)
(* state-free value forward, so it survives every later discard.             *)
(*                                                                           *)
(* (B) The counter folds up to the end of the body: the next group's         *)
(* counters and Q30 are folded as they are computed, the last ones inside    *)
(* the store window (REV32_FOLD_TAC "Q25" at s326, CTR_INCR_NORM_TAC at s335 *)
(* and s337, REV32_FOLD_TAC "Q4" at s336): raw counter towers with several   *)
(* unfolded adds are beyond WORD_BLAST.                                      *)
(*                                                                           *)
(* (C) The other conjuncts: the X0/X2 advances by CONV_TAC WORD_RULE; the    *)
(* plaintexts Q5..Q7 by PLAINTEXT_CLOSE_TAC; the store forall by the         *)
(* invariant's own forall for the old blocks and NEWBLK_CLOSE_TAC for the 8  *)
(* new ones; the htable by unfolding htable_mem_dec (REWRITE_TAC, let_CONV,  *)
(* ASM_REWRITE_TAC); the frame by MONOTONE_MAYCHANGE_TAC.                    *)
(* ------------------------------------------------------------------------- *)

(* RAWCT_LEMMA_AT sprev: add the WBN_RAWCT_READ !m lemma at state sprev to the
   assumptions; its premises come from the assumptions, with 9 <= nblk by
   WBN_NBLK_GE_9. *)
let RAWCT_LEMMA_AT sprev : tactic =
  SUBGOAL_THEN
    (subst[mk_var(sprev,`:armstate`),`s:armstate`]
      `!m. m < 8 ==> read (memory :> bytes128 (word_add in_p (word (16 * (8*(i+1)+m))))) s =
                     bytes_to_int128 (SUB_LIST (16 * (8*(i+1)+m), 16) ibytes)`)
    ASSUME_TAC THENL
   [MATCH_MP_TAC WBN_RAWCT_READ THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WBN_NBLK_GE_9 THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let GCM_SIMD_SIMPLIFY_KD_TAC = GCM_SIMD_SIMPLIFY_MEMO_TAC gcm_simd_kd_tbl;;
let ARM_STEPS_FOLD_KEEPDATA_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_KD_TAC THEN
              DISCARD_STALE_DATA_TAC THEN DISCARD_OLDSTATE_KEEPDATA_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;
(* DISCARD_QREGS_TAC qns: drop every `read Qn sN` fact of the listed registers,
   at any state; used before the final split of the body postcondition to drop
   the GHASH and scratch registers no conjunct needs. *)
let DISCARD_QREGS_TAC qns : tactic =
  DISCARD_ASSUMPTIONS_TAC(fun th -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(n,_)),Var(_,_))),_) -> List.mem n qns
    | _ -> false);;

(* RESOLVE_LDP2_TAC exec qa qb ma mb sload scur: take the step scur of an ldp
   that loads the raw ciphertext blocks 8(i+1)+ma and 8(i+1)+mb into qa and qb.
   Assume the raw lemma at the load-input state sload (RAWCT_LEMMA_AT), take
   the step without discarding, so that the lemma survives, resolve qa and qb
   (RESOLVE_QREG_C), then drop the raw memory-read forms and the old-state
   facts. *)
let RESOLVE_LDP2_TAC exec qa qb ma mb sload scur : tactic =
  RAWCT_LEMMA_AT sload THEN
  ARM_VERBOSE_STEP_TAC exec scur THEN
  RESOLVE_QREG_C qa scur ma THEN
  RESOLVE_QREG_C qb scur mb THEN
  DISCARD_ASSUMPTIONS_TAC(fun th -> match concl th with
     Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(n,_)),_)),
          Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),_)),_))
       -> n=qa || n=qb
   | _ -> false) THEN
  DISCARD_STALE_DATA_TAC THEN DISCARD_OLDSTATE_KEEPDATA_TAC scur THEN CLARIFY_TAC;;

(* NEWBLK_CLOSE_TAC: close one new-block leg of the store forall,
   j = 8*(i+1)+m with 0 <= m < 8.  Canonicalize the block indices 8*(i+1)+m
   to 8*i+(8+m), normalize both store-readback address forms
   (out_p+(128*(i+1)+16m) and (out_p+128*(i+1))+16m) to the flat goal form,
   fire the readback, then fold the plaintext (GSYM aes13 and
   GCM_CTR_INC_ITER_AS_ADD) and bridge the SUB_LIST index. *)
let NEWBLK_CLOSE_TAC =
  let canon = [ARITH_RULE `16 * 8 * (i+1) = 128*(i+1)`;
    ARITH_RULE `8*(i+1)+0 = 8*i+8`; ARITH_RULE `8*(i+1)+1 = 8*i+9`;
    ARITH_RULE `8*(i+1)+2 = 8*i+10`; ARITH_RULE `8*(i+1)+3 = 8*i+11`;
    ARITH_RULE `8*(i+1)+4 = 8*i+12`; ARITH_RULE `8*(i+1)+5 = 8*i+13`;
    ARITH_RULE `8*(i+1)+6 = 8*i+14`; ARITH_RULE `8*(i+1)+7 = 8*i+15`;
    ARITH_RULE `8*(i+1) = 8*i+8`] in
  let subbr = [ARITH_RULE `128 * (i + 1) = 16 * (8 * i + 8)`;
    ARITH_RULE `128 * (i + 1) + 16 = 16 * (8 * i + 9)`;
    ARITH_RULE `128 * (i + 1) + 32 = 16 * (8 * i + 10)`;
    ARITH_RULE `128 * (i + 1) + 48 = 16 * (8 * i + 11)`;
    ARITH_RULE `128 * (i + 1) + 64 = 16 * (8 * i + 12)`;
    ARITH_RULE `128 * (i + 1) + 80 = 16 * (8 * i + 13)`;
    ARITH_RULE `128 * (i + 1) + 96 = 16 * (8 * i + 14)`;
    ARITH_RULE `128 * (i + 1) + 112 = 16 * (8 * i + 15)`] in
  let addrbr = map (fun m -> WORD_RULE(subst[mk_small_numeral(16*m),`OFF:num`; mk_small_numeral m,`M:num`]
      `word_add (word_add out_p (word (128*(i+1)))) (word OFF):int64 =
       word_add out_p (word (16*(8*(i+1)+M))):int64`)) (0--7) in
  RULE_ASSUM_TAC(REWRITE_RULE addrbr) THEN
  REWRITE_TAC canon THEN RULE_ASSUM_TAC(REWRITE_RULE (canon @ subbr)) THEN
  (* Fire the store-readback assumption (ASM_REWRITE) before folding the raw
     aese/aesmc tower: with GSYM aes13 first, the goal's left-hand side is
     still `read(mem) s340` (the tower not yet substituted), so the fold has
     nothing to match and REFL_TAC fails on the 8 new-block legs. *)
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM aes13] THEN REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD] THEN
  REWRITE_TAC (canon @ subbr) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM aes13] THEN REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD] THEN
  REWRITE_TAC (canon @ subbr) THEN REFL_TAC;;
(* fold the keystream tower to aes13 and the counter to gcm_ctr_add, for the
   plaintext conjuncts Q5, Q6, Q7 *)
let PLAINTEXT_CLOSE_TAC =
  REWRITE_TAC[GSYM aes13] THEN REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(8*i+8)+5 = 8*i+13`; ARITH_RULE `(8*i+8)+6 = 8*i+14`;
              ARITH_RULE `(8*i+8)+7 = 8*i+15`] THEN
  REFL_TAC;;

(* word distributes over the back-edge if *)
let WBN_PC_IF = prove
 (`(if b then word (pc + 1212) else word (pc + 2572)):int64 =
   word (if b then pc + 1212 else pc + 2572)`,
  COND_CASES_TAC THEN REWRITE_TAC[]);;

(* The loop: PC = pc+0x4bc /\ core 0 ==> PC = pc+0xa0c /\ core k, over the
   front frame.  In WBN_MAIN_LOOP_raw below, the entry and exit legs are 0-step
   ensures (the same state at the loop head and at the exit), the count is
   nonzero by DIVISION arithmetic ((nblk - 9) DIV 8 >= 1 for 17 <= nblk), and
   the body is proved inline. *)
let wbn_main_loop_goal =
  let kk = `(nblk - 9) DIV 8` in
  let loop_pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc`;
      `read PC s = word (pc + 0x4bc)`;
      mk_comb(mk_comb(wbn_core_applied,`0`),`s:armstate`)]) in
  let loop_post = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc`;
      `read PC s = word (pc + 0xa0c)`;
      mk_comb(mk_comb(wbn_core_applied,kk),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[loop_pre; loop_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_MAIN_LOOP_raw = prove(wbn_main_loop_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UP2_ABI_TAC `(nblk - 9) DIV 8` `pc + 0x4bc` `pc + 0xa0c` wbn_core_iv THEN
  REPEAT CONJ_TAC THENL
   [ (* 1. the count is nonzero: (nblk - 9) DIV 8 >= 1 *)
    SUBGOAL_THEN `1 <= nblk - 1` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN ASM_ARITH_TAC;
    (* 2. entry: PC = 0x4bc /\ core 0, a 0-step ensures *)
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC;
    (* 3. The loop body.  After REPEAT STRIP_TAC, the unfolding of
       wbn_loop_inv_core_raw and ENSURES_INIT_TAC "s0", state s0 is at 0x4bc
       in iteration i, with
         X0 = in_p+128(i+1), X2 = out_p+128(i+1), X4 = in_p+16nblk,
         X5 = 128*((nblk-1) DIV 8)+in_p, X1 = 128nblk, X9 = 16nblk,
         X10 = sp+64, X11 = key_p, X3 = tag_p, X6 = htable_p, X16 = ivec_p,
         X15 = word 2^32, SP = stackpointer,
         Q0..Q4 = gcm_ctr_add (8i+8 .. 8i+12) ctr0, the counters ahead,
         Q5..Q7 = the plaintexts of blocks 8i+5 .. 8i+7,
         Q8..Q15 = the raw ciphertext blocks 8i .. 8i+7, not yet in GHASH,
         Q19 = ghash_polyval_acc over the blocks 0 .. 8i-1, Q31 = word 2^96,
         Q30 = gcm_ctr_raw (word (8i+13)) ctr0,
       and has to reach the core at i+1 with
         PC = if i+1 < k then 0x4bc else 0xa0c.
       The rev32 and add folds of the counter (REV32_FOLD_TAC and
       CTR_INCR_NORM_TAC, once per add) keep the counter terms flat; the Q19
       conjunct closes by WBN_Q19_CLOSE_TAC (the 8-block extension algebra of
       Sec 5); and the signed b.lt at 0xa08 is resolved inside the body by
       WB_PTRCMP_FLAGS (x0 against x5) and WBN_PC_BRIDGE, so the PC lands at
         if i+1 < (nblk-9) DIV 8 then pc+1212 else pc+2572. *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core_raw] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0" THEN
    CLEAR_KEEPDATA_MEMO_TAC THEN  (* empty the KEEPDATA memo table *)
    RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
    (* split htable_mem_dec at s0 into its 12 table reads *)
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
    FIRST_X_ASSUM(fun th ->
      let c = concl th in
      if can (find_term (fun t->match t with Const("byteswap128",_)->true|_->false)) c &&
         can (find_term (fun t->match t with Const("karatsuba_mid",_)->true|_->false)) c
      then STRIP_ASSUME_TAC th else NO_TAC) THEN
    (* The simulation s0..s340 and the postcondition close.  The KEEPDATA
       steppers keep Q0..Q19, the keystreams included; the ldp's of the next
       group are resolved at load (RESOLVE_LDP2_TAC). *)
    (* steps 1..13: the counter setup, with the rev32 and add folds *)
    ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (1--1) THEN
    REV32_FOLD_TAC "Q5" "s1" `word (8*i+13):32 word` THEN
    ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (2--3) THEN GCM_SIMD_SIMPLIFY_TAC THEN
    CTR_INCR_NORM_TAC "s3" 13 THEN
    ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (4--7) THEN GCM_SIMD_SIMPLIFY_TAC THEN
    REV32_FOLD_TAC "Q6" "s7" `word (8*i+14):32 word` THEN
    ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (8--8) THEN GCM_SIMD_SIMPLIFY_TAC THEN
    CTR_INCR_NORM_TAC "s8" 14 THEN
    ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (9--13) THEN GCM_SIMD_SIMPLIFY_TAC THEN
    REV32_FOLD_TAC "Q7" "s13" `word (8*i+15):32 word` THEN
    (* steps 14..212: AES and GHASH *)
    ARM_STEPS_FOLD_KEEPDATA_TAC AES256_GCM_DEC_ALT_EXEC (14--120) THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AES256_GCM_DEC_ALT_EXEC (121--211) THEN DISCARD_STALE_Q19_TAC THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AES256_GCM_DEC_ALT_EXEC (212--212) THEN DISCARD_STALE_Q19_TAC THEN
    CTR_INCR_NORM_TAC "s212" 15 THEN
    (* steps 213..289; the ldp at step 221 loads Q8, Q9 *)
    ARM_STEPS_FOLD_KEEPDATA_TAC AES256_GCM_DEC_ALT_EXEC (213--220) THEN
    RESOLVE_LDP2_TAC AES256_GCM_DEC_ALT_EXEC "Q8" "Q9" 0 1 "s220" "s221" THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AES256_GCM_DEC_ALT_EXEC (222--258) THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AES256_GCM_DEC_ALT_EXEC (259--259) THEN
    REV32_FOLD_TAC "Q20" "s259" `word (8*i+16):32 word` THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AES256_GCM_DEC_ALT_EXEC (260--261) THEN
    CTR_INCR_NORM_TAC "s261" 16 THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AES256_GCM_DEC_ALT_EXEC (262--270) THEN
    REV32_FOLD_TAC "Q22" "s270" `word (8*i+17):32 word` THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AES256_GCM_DEC_ALT_EXEC (271--272) THEN
    (* the ldp at step 273 loads Q10, Q11 *)
    RESOLVE_LDP2_TAC AES256_GCM_DEC_ALT_EXEC "Q10" "Q11" 2 3 "s272" "s273" THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AES256_GCM_DEC_ALT_EXEC (274--279) THEN
    CTR_INCR_NORM_TAC "s279" 17 THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AES256_GCM_DEC_ALT_EXEC (280--288) THEN
    REV32_FOLD_TAC "Q23" "s288" `word (8*i+18):32 word` THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AES256_GCM_DEC_ALT_EXEC (289--289) THEN
    CTR_INCR_NORM_TAC "s289" 18 THEN
    (* The Q19 wire-in: abbreviate the three accumulators at s289 (Q17/Q19/Q18
       = PL/PH/PM) so that the reduction byteform stays small, then keep
       Q16..Q19 through the reduction with the NOSIMP stepper.  read Q19 s326
       is then the left-hand side of WBN_MACHINE_REDUCE_IS_PROP3_PACK over
       PL/PH/PM, and WBN_Q19_CLOSE_TAC closes the Q19 conjunct of the
       postcondition. *)
    WBN_Q19_EXTRACT_ABBREV_TAC "s289" THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AES256_GCM_DEC_ALT_EXEC (290--305) THEN
    (* the ldp's at steps 306 and 309 load Q12, Q13 and Q14, Q15 *)
    RESOLVE_LDP2_TAC AES256_GCM_DEC_ALT_EXEC "Q12" "Q13" 4 5 "s305" "s306" THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AES256_GCM_DEC_ALT_EXEC (307--308) THEN
    RESOLVE_LDP2_TAC AES256_GCM_DEC_ALT_EXEC "Q14" "Q15" 6 7 "s308" "s309" THEN
    (* steps 310..337, the stores: the next group's counters are folded as they
       are computed, Q25 at s326 (before its mov to Q3), Q4 at s336, Q30 at
       s335 and s337 *)
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AES256_GCM_DEC_ALT_EXEC (310--326) THEN
    REV32_FOLD_TAC "Q25" "s326" `word (8*i+19):32 word` THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AES256_GCM_DEC_ALT_EXEC (327--335) THEN
    CTR_INCR_NORM_TAC "s335" 19 THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AES256_GCM_DEC_ALT_EXEC (336--336) THEN
    REV32_FOLD_TAC "Q4" "s336" `word (8*i+20):32 word` THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AES256_GCM_DEC_ALT_EXEC (337--337) THEN
    CTR_INCR_NORM_TAC "s337" 20 THEN
    (* the back-edge: normalize X0, the cmp at step 338, resolve NF/VF, the stp
       at step 339 and the b.lt at step 340 *)
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
      `word_add (word_add in_p (word (128 * (i + 1)))) (word 128):int64 =
       word_add in_p (word (128*(i+2)))`]) THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AES256_GCM_DEC_ALT_EXEC (338--338) THEN
    SUBGOAL_THEN `9 <= nblk` ASSUME_TAC THENL
     [MATCH_MP_TAC WBN_NBLK_GE_9 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    (* derive the NF/VF equivalences of WB_PTRCMP_FLAGS as separate theorems
       and rewrite them into the assumptions; adding them to the goal with
       MP_TAC breaks the stp step that follows *)
    (fun (asl,w) ->
       let prem = MATCH_MP WBN_PTRCMP_PREMS
         (CONJ (ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`)
               (ASSUME `i < (nblk - 9) DIV 8`)) in
       let flags = MATCH_MP (SPECL [`in_p:int64`; `128*(i+2)`; `128*((nblk-1) DIV 8)`]
                     WB_PTRCMP_FLAGS) prem in
       RULE_ASSUM_TAC(REWRITE_RULE[CONJUNCT1 flags; CONJUNCT2 flags]) (asl,w)) THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AES256_GCM_DEC_ALT_EXEC (339--340) THEN
    FIRST_X_ASSUM(fun th -> if can (find_term (fun t -> t = `read PC s340`)) (concl th)
      then ASSUME_TAC(REWRITE_RULE[MATCH_MP WBN_PC_BRIDGE (ASSUME `9 <= nblk`)] th)
      else NO_TAC) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (* the postcondition: the PC (WBN_PC_IF), the counter indices
       (8*(i+1) = 8*i+8), then the plaintexts, Q8..Q15 (already resolved), Q19
       and the store forall *)
    REWRITE_TAC[WBN_PC_IF] THEN
    REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN
    REWRITE_TAC[ARITH_RULE `(8*i+8)+8 = 8*i+16`; ARITH_RULE `(8*i+8)+9 = 8*i+17`;
      ARITH_RULE `(8*i+8)+10 = 8*i+18`; ARITH_RULE `(8*i+8)+11 = 8*i+19`;
      ARITH_RULE `(8*i+8)+12 = 8*i+20`; ARITH_RULE `(8*i+8)+13 = 8*i+21`] THEN
    (* ASM_REWRITE closes the conjuncts already resolved (the counters Q0..Q4,
       the raw ciphertext Q8..Q15); split the rest and close each conjunct,
       after dropping the GHASH reduction and scratch registers Q16..Q25 and
       Q29, to keep the assumption list small *)
    DISCARD_QREGS_TAC ["Q16";"Q17";"Q18";"Q19";"Q20";"Q21";"Q22";"Q23";"Q24";"Q25";"Q29"] THEN
    REPEAT CONJ_TAC THENL
     [ (* [0-2] plaintext Q5,Q6,Q7 *)
       PLAINTEXT_CLOSE_TAC; PLAINTEXT_CLOSE_TAC; PLAINTEXT_CLOSE_TAC;
       (* [3] Q19, the wire-in close: the goal
            <machine reduction byteform over PL/PH/PM> = ghash..(8*i+8)
          is the value equality that WBN_Q19_CLOSE_TAC builds from the stashed
          s289 accumulators, by WBN_MACHINE_REDUCE_IS_PROP3_PACK and the block
          algebra of Sec 5 *)
       WBN_Q19_CLOSE_TAC;
       (* [4-5] X0/X2 pointer advances *)
       CONV_TAC WORD_RULE; CONV_TAC WORD_RULE;
       (* [6] the store forall: the old blocks (j < 8*(i+1)) by the
          invariant's own forall, the 8 new ones (8*(i+1) <= j < 8*(i+1)+8)
          by NEWBLK_CLOSE_TAC *)
       X_GEN_TAC `j:num` THEN DISCH_TAC THEN
       ASM_CASES_TAC `j < 8 * (i + 1)` THENL
        [ FIRST_ASSUM(fun th -> match concl th with
            Comb(Const("!",_),Abs(Var("j",_),Comb(Comb(Const("==>",_),
              Comb(Comb(Const("<",_),_),Comb(Comb(Const("*",_),_),
                Comb(Comb(Const("+",_),_),_)))),_))) ->
              MP_TAC(SPEC `j:num` th) | _ -> NO_TAC) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])];
          MP_TAC(ARITH_RULE
            `~(j < 8 * (i + 1)) /\ j < 8 * i + 16
             ==> j = 8*(i+1) \/ j = 8*(i+1)+1 \/ j = 8*(i+1)+2 \/ j = 8*(i+1)+3 \/
                 j = 8*(i+1)+4 \/ j = 8*(i+1)+5 \/ j = 8*(i+1)+6 \/ j = 8*(i+1)+7`) THEN
          ASM_REWRITE_TAC[] THEN
          DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
          NEWBLK_CLOSE_TAC ];
       (* [7] htable predicate *)
       REWRITE_TAC[htable_mem_dec] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
       ASM_REWRITE_TAC[];
       (* [8] MAYCHANGE frame *)
       REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
       REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC ];
    (* 4. exit: PC = 0xa0c /\ core k, a 0-step ensures *)
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC]);;

(* ========================================================================= *)
(* 11. The prepretail: from the loop exit 0xa0c (pc+2572) to the tail seam   *)
(* pc+3824 (0xef0).                                                          *)
(*                                                                           *)
(* The main loop (WBN_MAIN_LOOP_raw) exits at k = (nblk-9) DIV 8 with the    *)
(* GHASH stream one 8-block group behind the stores.  This leg simulates the *)
(* 313 straight-line instructions 0xa0c..0xeec.  The prepretail 0xa0c..0xed8 *)
(* folds that last in-flight group (blocks 8k..8k+7) into Q19, catching the  *)
(* GHASH stream up, and computes the keystream towers of blocks 8k+8..8k+15  *)
(* in Q0..Q7; the tail entry 0xedc..0xeec (ext v16; sub x5,x4,x0;            *)
(* cmp x5,#0x70; ldr q9,[x0],#16; ldp q24,q25,[x6,#160]) then sets up the    *)
(* tail's Q9, Q24, Q25, X0 and X5.  So the leg is the pipelined analogue of  *)
(* the front of the <=8-block chain, which folds no block                    *)
(* (Q19 = word_bytereverse xi) and leaves all r blocks to the tail.          *)
(*                                                                           *)
(* The end state feeds the tail back-legs WB_TAIL_GEN2_r of the <=8-block    *)
(* chain, which start at the same PC (their state s265, q_at r), by          *)
(* precondition weakening at shifted arguments (shift_vals r in Sec 12):     *)
(*   ctr0   := gcm_ctr_add (word (8*(k+1))) ctr0                             *)
(*   in_p   := word_add in_p (word (128*(k+1)))                              *)
(*   out_p  := word_add out_p (word (128*(k+1)))                             *)
(*   ibytes := the last r = nblk - 8*(k+1) blocks of ibytes   (r = 1..8)     *)
(*   xi     := the reversed caught-up accumulator (all 8*(k+1) blocks)       *)
(* The counter registers reconcile by GCM_CTR_ADD_COMPOSE:                   *)
(*   gcm_ctr_add (8k+8+i) ctr0 = gcm_ctr_inc^i (gcm_ctr_add (8(k+1)) ctr0).  *)
(* The simulation is WBN_PREPRETAIL_EXT2_TAC below.                          *)
(*                                                                           *)
(* The state at s313 (k = (nblk-9) DIV 8):                                   *)
(*   PC = pc+3824                                                            *)
(*   Q0..Q7 = aes13 (gcm_ctr_add (8k+8..8k+15) ctr0) k0..k13                 *)
(*   Q24 = karatsuba_mid h8 || karatsuba_mid h7, Q25 = h8   (ldp at 0xeec)   *)
(*   Q19 = the caught-up accumulator (wbn_caught_up), Q16 = its staging      *)
(*   X0 = in_p+128(k+1)+16, X2 = out_p+128(k+1), X4 = in_p+16nblk,           *)
(*   X5 = (in_p+16nblk) - (in_p+128(k+1)) = word (16*r), and the NZCV        *)
(*   of cmp x5,#0x70 (112)                                                   *)
(*   preserved: X1 = 128nblk, X9 = 16nblk, X10 = sp+64, X11 = key_p,         *)
(*   X3 = tag_p, X6 = htable_p, X16 = ivec_p, X15 = 2^32, Q31 = 2^96,        *)
(*   SP = stackpointer, [sp+64] = 0xC2..., the round keys k0..k14, the       *)
(*   htable, the input buffer and the stores j < 8*(k+1)                     *)
(* ========================================================================= *)

(* The s313 seam state, built like wb_front_postcond from the final state of
   the simulation.  Q19 and its staging Q16 are stated at a fresh xi', as the
   substitution source for wbn_prepretail_post below: with xi' unconstrained
   this is not a true postcondition (word_bytereverse is a bijection and the
   model is deterministic).  The counter registers are
   Q0..Q7 = aes13 (gcm_ctr_add (word (8*k+8+i)) ctr0) k0..k13, i = 0..7.  It
   leaves out the tag_p, ivec_p, [sp+72] and in_p block 0 cells, which the tail
   does not read: the tail (0xef0..0x1198, and the exact-8 drain
   0x11b4..0x1330) only stores ivec_p (str q30,[x16] at 0x1130, or 0x1300 in
   the drain) and tag_p (st1 v19,[x3] at 0x1198), and its only stack load is the
   reduction constant at [sp+64].  It also leaves out Q9, which the tail does
   read and which the extended post below restates in spec form. *)
let wbn_prepretail_post_raw =
  let ctr j = subst [mk_small_numeral j,`jjj:num`]
    `gcm_ctr_add (word (8 * (nblk - 9) DIV 8 + jjj)) ctr0` in
  wbp_post
  ([`aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc`;
    `read PC s = word (pc + 3824)`;
    wbp_rd `Q24` (wbp_hmid 7);
    wbp_rd `Q25` (wbp_hpow 8)] @
   wbp_cmpi_flags `word_sub (word_add in_p (word (16 * nblk)))
                            (word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1)))):int64` 112 @
   [`read Q16 s = word_subword (word_join (word_bytereverse (xi':int128)) (word_bytereverse xi'):256 word) (64,128)`;
    wbp_rd `Q7` (wbp_aes13 (ctr 15));
    wbp_rd `Q6` (wbp_aes13 (ctr 14));
    wbp_rd `Q0` (wbp_aes13 (ctr 8));
    wbp_rd `Q1` (wbp_aes13 (ctr 9));
    `read (memory :> bytes64 (word_add stackpointer (word 64))) s = word 13979173243358019584`;
    `read X11 s = key_p`;
    `read X9 s = word (16 * nblk)`;
    `read SP s = stackpointer`;
    `read X1 s = word (128 * nblk)`;
    `read X2 s = word_add out_p (word (128 * ((nblk - 9) DIV 8 + 1)))`;
    `read X3 s = tag_p`;
    `read X6 s = htable_p`;
    `read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes`] @
   wbp_key_reads @ wbp_htable_reads @ wbp_ctx `xi':int128` @
   [wbp_rd `Q5` (wbp_aes13 (ctr 13));
    wbp_rd `Q2` (wbp_aes13 (ctr 10));
    wbp_rd `Q4` (wbp_aes13 (ctr 12));
    wbp_rd `Q3` (wbp_aes13 (ctr 11));
    `read X5 s = word_sub (word_add in_p (word (16 * nblk)))
                          (word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1))))`;
    `read X0 s = word_add (word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1)))) (word 16)`]);;

(* The seam post: the raw post with its fresh word_bytereverse xi', which
   occurs only in the Q19 and Q16 conjuncts, replaced by the caught-up
   accumulator, so that Q19 = wbn_caught_up (the invariant's shape at
   i := k + 1) and Q16 is its staging
   word_subword (word_join wbn_caught_up wbn_caught_up) (64,128).  xi' is gone,
   so the post is over the variables of wb_front_vars only. *)
let wbn_prepretail_post =
  subst [wbn_caught_up, `word_bytereverse (xi':int128)`] wbn_prepretail_post_raw;;

(* ------------------------------------------------------------------------- *)
(* 12. Recomposition of the nblk > 8 chain.                                  *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The output stores of the first 8*(k+1) blocks.                            *)
(*                                                                           *)
(* wbn_prepretail_post (64 conjuncts) does not contain the loop invariant's  *)
(* output-store conjunct                                                     *)
(*   !j. j < 8*((nblk-9)DIV8 + 1) ==>                                        *)
(*       read (memory :> bytes128 (word_add out_p (word (16*j)))) s =        *)
(*       word_xor (word_xor (bytes_to_int128 (SUB_LIST (16*j,16) ibytes))    *)
(*                (aes13 (gcm_ctr_inc_iter j ctr0) k0..k13)) k14             *)
(* the decrypted blocks before the tail.  The final post needs the stores of *)
(* all nblk blocks and the tail leg produces only the last                   *)
(* r = nblk - 8*(k+1), so the first 8*(k+1) have to be carried through the   *)
(* seam.  The prepretail (0xa0c..0xeec) stores nothing, so the forall passes *)
(* through the simulation unchanged, and the extended post closes by         *)
(* ASM_REWRITE: it is a preserved read fact, not frame preservation          *)
(* (ENSURES_ADD_PRESERVED does not apply, since the frame allows writes to   *)
(* out_p).                                                                   *)
(*                                                                           *)
(* wbn_out_forall is that forall at i := k, as a predicate on s, taken from  *)
(* wbn_loop_inv_core_raw so that it is the term the simulation preserves,    *)
(* and the extended post (65 conjuncts) is                                   *)
(*   wbn_prepretail_post_ext = wbn_prepretail_post /\ wbn_out_forall.        *)
(* ------------------------------------------------------------------------- *)

let wbn_out_forall =
  let full = list_mk_comb(wbn_core_applied, [`(nblk - 9) DIV 8`; `s:armstate`]) in
  let inv_cs = conjuncts (rhs(concl (REWRITE_CONV[wbn_loop_inv_core_raw] full))) in
  mk_abs(`s:armstate`, find is_forall inv_cs);;

let wbn_prepretail_post_ext =
  mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs wbn_prepretail_post),
            snd(dest_abs wbn_out_forall)));;

(* ------------------------------------------------------------------------- *)
(* WBN_Q9_SPEC: the first tail block in spec form.                           *)
(*                                                                           *)
(* At the seam the simulation has executed the ldr q9,[x0],#16 at 0xee8      *)
(* (step 312, with x0 = in_p + 128*(k+1)), so Q9 is a raw read of the input  *)
(* memory in the state before it.  The tail reads that Q9                    *)
(* (eor3 v12,v9,v0,v29 at 0xef8) before any reload of q9, so Q9 has to reach *)
(* the seam in spec form.  This lemma gives the value of the read, the first *)
(* tail block (global block 8*(k+1))                                         *)
(*   bytes_to_int128 (SUB_LIST (16*8*(k+1),16) ibytes),                      *)
(* by INPUT_PREFIX_TO_BYTE128_LANES at lane 8*(k+1), from 8*(k+1) < nblk and *)
(* the whole-buffer input fact.  WBN_PREPRETAIL_EXT2_TAC applies it at s311, *)
(* the state before the ldr.                                                 *)
(* ------------------------------------------------------------------------- *)
let WBN_Q9_SPEC = prove
 (`!(nblk:num) (in_p:int64) (ibytes:byte list) (k:num) (s:armstate).
     LENGTH ibytes = 16 * nblk /\
     8 * (k + 1) < nblk /\
     read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes
     ==> read (memory :> bytes128 (word_add in_p (word (128 * (k + 1))))) s =
         bytes_to_int128 (SUB_LIST (16 * (8 * (k + 1)),16) ibytes)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s:armstate`]
    INPUT_PREFIX_TO_BYTE128_LANES) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_ARITH_TAC;
      SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` SUBST1_TAC THENL
       [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `8 * (k + 1):num`) THEN
    ANTS_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `16 * (8 * (k + 1)) = 128 * (k + 1)`] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th])]]);;

(* The extended seam post: wbn_prepretail_post_ext (the stores of the first
   8 * (k + 1) blocks) and two more conjuncts.
   - Q9 = the first tail block, global block 8 * (k + 1), in spec form
     (WBN_Q9_SPEC at k := (nblk - 9) DIV 8): the tail reads the incoming
     Q9 before it reloads q9.  The simulation resolves the load in the state
     before the ldr q9, where the whole-buffer input fact is live.
   - Q30 = gcm_ctr_raw (word (8 * k + 16)) ctr0: the raw counter three adds
     past its loop-head value gcm_ctr_raw (word (8 * k + 13)) ctr0, for the
     ivec write-back.  INNER_TAIL_FEED_TAC discharges the shifted tail's Q30
     precondition from it (GCM_CTR_RAW_ABSORB_NUM). *)
let wbn_prepretail_post_ext2 =
  mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs wbn_prepretail_post_ext),
            mk_conj(
              `read Q9 (s:armstate) =
               bytes_to_int128 (SUB_LIST (16 * 8 * ((nblk - 9) DIV 8 + 1),16) ibytes)`,
              `read Q30 (s:armstate) =
               gcm_ctr_raw (word (8 * ((nblk - 9) DIV 8) + 16)) ctr0`)));;

let wbn_prepretail_ext2_goal =
  let kk = `(nblk - 9) DIV 8` in
  let pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc`;
      `read PC s = word (pc + 0xa0c)`;
      mk_comb(mk_comb(wbn_core_applied,kk),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[pre; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

(* The prepretail simulation, parameterized by the first-tail-block index bound
   (idx_lt_thm: ... ==> 8 * ((nblk-9) DIV 8) + 8 < nblk): init at the invariant
   (i := k); the counter folds at s2, s3, s7, s9 and s14; the KEEPDATA bulk
   15..240; the GHASH wire-in at s242, where PL, PH and PM (Q17, Q19, Q18) are
   complete (their last writes are s239, s240 and s242): they are abbreviated
   (WBN_Q19_EXTRACT_ABBREV_TAC) so that the reduce byteform stays small, and
   the reduce and the rest run without simplification; the third counter add
   (step 306) folded at s311; Q9 resolved at s311, before the ldr q9 at 0xee8
   (step 312).  ENSURES_FINAL and ASM_REWRITE close the preserved and shifted
   conjuncts, WBN_Q19_PREPRETAIL_CLOSE_TAC the two GHASH conjuncts. *)
let WBN_PREPRETAIL_EXT2_TAC idx_lt_thm =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core_raw] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0" THEN
  CLEAR_KEEPDATA_MEMO_TAC THEN  (* reset the KEEPDATA fixpoint cache *)
  RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (find_term (fun t->match t with Const("byteswap128",_)->true|_->false)) c &&
       can (find_term (fun t->match t with Const("karatsuba_mid",_)->true|_->false)) c
    then STRIP_ASSUME_TAC th else NO_TAC) THEN
  ABBREV_TAC `k = (nblk - 9) DIV 8` THEN
  ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (1--1) THEN
  ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (2--2) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q5" "s2" `word (8*k+13):32 word` THEN
  ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (3--3) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  CTR_INCR_NORM_TAC "s3" 13 THEN
  ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (4--7) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q6" "s7" `word (8*k+14):32 word` THEN
  ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (8--9) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  CTR_INCR_NORM_TAC "s9" 14 THEN
  ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (10--14) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q7" "s14" `word (8*k+15):32 word` THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AES256_GCM_DEC_ALT_EXEC (15--120) THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AES256_GCM_DEC_ALT_EXEC (121--211) THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AES256_GCM_DEC_ALT_EXEC (212--240) THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AES256_GCM_DEC_ALT_EXEC (241--242) THEN
  WBN_Q19_EXTRACT_ABBREV_TAC "s242" THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AES256_GCM_DEC_ALT_EXEC (243--306) THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AES256_GCM_DEC_ALT_EXEC (307--311) THEN
  (* the third add v30 (step 306), in the unsimplified window: fold it, then
     normalize 8*k+15+1 to 8*k+16; no later step writes v30 *)
  CTR_RAW_INCR_FOLD_TAC "Q30" "s311" `word (8*k+15):32 word` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word (8*k+15)) (word 1):32 word = word (8*k+16)`]) THEN
  MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `k:num`; `s311:armstate`]
    WBN_Q9_SPEC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `nblk:num` idx_lt_thm) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_TAC] THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AES256_GCM_DEC_ALT_EXEC (312--313) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM aes13]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE(map GSYM wb_ctr_lanes_thms)) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN
  TRY(W(fun (asl,w) ->
        if can (find_term (fun t -> is_const t && fst(dest_const t) = "ghash_polyval_acc")) w
        then WBN_Q19_PREPRETAIL_CLOSE_TAC `k:num` else NO_TAC)) THEN
  TRY MONOTONE_MAYCHANGE_TAC THEN
  TRY (ASM_REWRITE_TAC[]);;

(* The union band: wbn_front_hyps_wide_tm with 17 <= nblk replaced by
   9 <= nblk, by the same recursive replacement as wbn_front_hyps_916_tm
   below. *)
let wbn_front_hyps_9_tm =
  let rec repl t = match t with
    | Comb(Comb(Const("/\\",_),a),b) -> mk_conj(repl a, repl b)
    | _ -> if t = `17 <= nblk` then `9 <= nblk` else t in
  repl wbn_front_hyps_wide_tm;;

let wbn_prepretail_ext2_uni_goal =
  let kk = `(nblk - 9) DIV 8` in
  let pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc`;
      `read PC s = word (pc + 0xa0c)`;
      mk_comb(mk_comb(wbn_core_applied,kk),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[pre; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_9_tm, ens));;

(* The prepretail, simulated once on the union band 9 <= nblk: its pre, post
   and steps are the same for the >=17 band and the 9..16 leg, and the only
   band-dependent side condition, the Q9 index bound, holds for 9 <= nblk
   (WBN_Q9_INDEX_LT_9). *)
let WBN_PREPRETAIL_EXT2_UNIFIED =
  prove(wbn_prepretail_ext2_uni_goal, WBN_PREPRETAIL_EXT2_TAC WBN_Q9_INDEX_LT_9);;

(* The >=17 band, from the union-band theorem by strengthening the hypotheses
   (no simulation). *)
let WBN_PREPRETAIL_EXT2 =
  prove(wbn_prepretail_ext2_goal,
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC WBN_PREPRETAIL_EXT2_UNIFIED THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* The loop and the prepretail, from the loop head pc+0x4bc to the seam
   (WBN_LOOP_PREP_EXT2: WBN_MAIN_LOOP_raw, then WBN_PREPRETAIL_EXT2), and the
   front, the loop and the prepretail, from pc+0x1c to the seam
   (WBN_FRONT_TO_PREP_EXT2: WBN_LOOP_INVARIANT_ENTRY_RAW, then
   WBN_LOOP_PREP_EXT2), both by ENSURES_TRANS_SIMPLE.  The second weakens the
   precondition of WBN_LOOP_PREP_EXT2 to the entry post through
   WBN_INV_RAW_SPLIT (ENSURES_PRECONDITION_THM). *)
let wbn_loop_prep_ext2_goal =
  let loop_pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc`;
      `read PC s = word (pc + 0x4bc)`;
      mk_comb(mk_comb(wbn_core_applied,`0`),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[loop_pre; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_LOOP_PREP_EXT2 = prove(wbn_loop_prep_ext2_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC (rand(rator(snd(dest_imp(snd(strip_forall(concl WBN_MAIN_LOOP_raw))))))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL wb_front_vars WBN_MAIN_LOOP_raw) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
    MP_TAC(SPECL wb_front_vars WBN_PREPRETAIL_EXT2) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC]]);;

let wbn_front_to_prep_ext2_goal =
  let ens = list_mk_comb(`ensures arm`,
    [wbn_front_P_tm; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_FRONT_TO_PREP_EXT2 = prove(wbn_front_to_prep_ext2_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_entry_post THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL wb_front_vars WBN_LOOP_INVARIANT_ENTRY_RAW) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (rand(rator(rator(snd(dest_imp(snd(strip_forall(concl WBN_LOOP_PREP_EXT2)))))))) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[WBN_INV_RAW_SPLIT] THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[ARITH_RULE `pc + 0x4bc = pc + 1212`] THEN CONV_TAC TAUT;
      MP_TAC(SPECL wb_front_vars WBN_LOOP_PREP_EXT2) THEN
      ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC]]]);;

(* Input-read restriction to a slice of length m (= 16*r) at 128*(k+1): the
   r-block shifted tail reads 16*r input bytes there, m kept symbolic under
   128*(k+1)+m <= 16*nblk.  The slice of the list is a DIV then a MOD of its
   number (NUM_OF_WORDLIST_SUB_LIST), which READ_BYTES_DIV and READ_BYTES_MOD
   turn back into reads. *)
let WBN_INPUT_SLICE_GEN = prove
 (`!(nblk:num) (in_p:int64) (ibytes:byte list) (k:num) (m:num) (s:armstate).
     LENGTH ibytes = 16 * nblk /\ 128 * (k + 1) + m <= 16 * nblk /\
     read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes
     ==> read (memory :> bytes (word_add in_p (word (128 * (k + 1))),m)) s =
         num_of_bytelist (SUB_LIST (128 * (k + 1),m) ibytes)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`in_p:int64`; `16 * nblk`; `128 * (k+1)`; `read memory (s:armstate)`]
    READ_BYTES_DIV) THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes (word_add in_p (word (128 * (k + 1))),m)) s =
     (read (memory :> bytes (word_add in_p (word (128 * (k + 1))),
                             16 * nblk - 128 * (k + 1))) s) MOD 2 EXP (8 * m)`
   SUBST1_TAC THENL
   [MP_TAC(ISPECL [`word_add in_p (word (128 * (k+1))):int64`;
                   `16 * nblk - 128 * (k+1)`; `m:num`; `read memory (s:armstate)`]
       READ_BYTES_MOD) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    SUBGOAL_THEN `MIN (16 * nblk - 128 * (k + 1)) m = m` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NUM_OF_BYTELIST_EQ_WORDLIST] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST; DIMINDEX_8] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Feeding the shifted r-block tail.                                         *)
(*                                                                           *)
(* With nblk = 8*((nblk-9) DIV 8 + 1) + r (r = 1..8), INNER_TAIL_FEED_TAC    *)
(* below proves                                                              *)
(*   ensures arm wbn_prepretail_post_ext2 (shifted band_post r) narrow_frame *)
(* by weakening the precondition of WB_TAIL_GEN2_r at shift_vals r.  The     *)
(* tail's own hypotheses (nonoverlapping over the shifted out_p, tag_p and   *)
(* ivec_p regions) need three disjointness clauses the wide hypotheses do    *)
(* not carry:                                                                *)
(*   nonoverlapping (out_p,16*nblk) (tag_p,16)                               *)
(*   nonoverlapping (out_p,16*nblk) (ivec_p,16)                              *)
(*   nonoverlapping (tag_p,16)       (ivec_p,16)                             *)
(* They are genuine preconditions of the whole function: the output buffer   *)
(* is disjoint from the tag and the counter block, and those two from each   *)
(* other.  Rather than widen wbn_front_hyps_wide_tm, which would mean        *)
(* re-proving the chain, they are side conditions of the tail legs           *)
(* (wbn_prep_to_end_extra_clauses), carried up to WBN_DEC_CORE_BYTELIST,     *)
(* whose PAIRWISE nonoverlapping premise implies them.                       *)
(* ------------------------------------------------------------------------- *)

(* The WB_TAIL_GEN2_r instantiation for residue r, in the order of
   wb_front_vars without nblk, then return_value: out_p, in_p, ibytes, xi and
   ctr0 are shifted past the first 8 * (k + 1) blocks (xi becomes the reversed
   caught-up accumulator), and the return value is the whole-call count
   word (16 * nblk). *)
let shift_vals r =
  let rt = mk_small_numeral r in
  let slice = subst [rt, `r_:num`]
                `SUB_LIST (128 * ((nblk - 9) DIV 8 + 1), 16 * r_) (ibytes:byte list)` in
  let xi_shifted = mk_comb(`word_bytereverse:int128->int128`, wbn_caught_up) in
  [ `pc:num`; `stackpointer:int64`;
    `word_add out_p (word (128 * ((nblk - 9) DIV 8 + 1))):int64`;
    `tag_p:int64`; `ivec_p:int64`;
    `word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1))):int64`;
    `key_p:int64`; `htable_p:int64`;
    slice; xi_shifted;
    `gcm_ctr_add (word (8 * ((nblk - 9) DIV 8 + 1))) ctr0:int128`;
    `k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;`k5:int128`;`k6:int128`;`k7:int128`;
    `k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;`k12:int128`;`k13:int128`;`k14:int128`;`h:int128`;
    `word (16 * nblk):int64`];;

(* ------------------------------------------------------------------------- *)
(* WBN_PREP_TO_END_FULL_r: the seam post fed to the shifted tail, with the   *)
(* full-nblk contract as its post (not the r-block band_post).  The post is  *)
(* wbn_end_post: PC = pc+4508, X9 = word (16 * nblk), the output forall over *)
(* all nblk blocks (in the aes13 / k14 form of the seam's carried forall),   *)
(* the tag folded over list_of_seq cph nblk by GHASH_ACC_APPEND, and the     *)
(* ivec write-back.                                                          *)
(*                                                                           *)
(* Route: ENSURES_FRAME_SUBSUMED (the narrow tail frame inside the wide      *)
(* wbn_front_C_tm), then ENSURES_POSTCONDITION_THM with the intermediate     *)
(* post wbn_full_inter_post r, the conjunction of the shifted band_post r    *)
(* and the seam's forall, which splits into                                  *)
(*   (1) wbn_full_inter_post r ==> wbn_end_post: the tag fold and the        *)
(*       re-indexing of the stores;                                          *)
(*   (2) ensures ext2post (wbn_full_inter_post r) narrow_frame, by           *)
(*       ENSURES_ADD_PRESERVED: the tail leg by INNER_TAIL_FEED_TAC, and the *)
(*       forall carried by read-over-write through the narrow frame, which   *)
(*       writes only bytes (out_p+128(k+1),16*r), disjoint from the first    *)
(*       128(k+1) output bytes.                                              *)
(* ------------------------------------------------------------------------- *)

(* the nblk-uniform end post (PC + byte count in X9 + output/tag/counter). *)
let wbn_end_post =
  let end_forall = `forall j. j < nblk
    ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
        word_xor (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16) ibytes))
        (aes13 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13)) k14` in
  let tag = `read (memory :> bytes128 tag_p) s =
    word_bytereverse (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      (MAP word_bytereverse
        (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) nblk)))` in
  (* ivec: the whole-buffer counter write-back, spine form
     gcm_ctr_inc_iter nblk ctr0.  FULL_r reconciles the shifted band's
     gcm_ctr_inc_iter r (gcm_ctr_add (word 8(q+1)) ctr0) to this via
     GCM_CTR_INC_ITER_AS_ADD + GCM_CTR_ADD_COMPOSE (8(q+1)+r = nblk). *)
  let ivec = `read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter nblk ctr0` in
  mk_abs(`s:armstate`,
    list_mk_conj [`read PC s = word (pc + 4508)`;
                  `read X9 s = word (16 * nblk)`;
                  end_forall; tag; ivec]);;

(* full-post goal for a given r *)
let wbn_prep_to_end_full_goal r =
  let nblk_eq = subst[mk_small_numeral r,`r_:num`]
                  `nblk = 8 * ((nblk - 9) DIV 8 + 1) + r_` in
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_wide_tm :: nblk_eq :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_prepretail_post_ext2; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

(* the back-leg theorem WB_TAIL_GEN2_r for residue r *)
let wbn_tail_gen2 r =
  if r=1 then WB_TAIL_GEN2_1 else if r=2 then WB_TAIL_GEN2_2
  else if r=3 then WB_TAIL_GEN2_3 else if r=4 then WB_TAIL_GEN2_4
  else if r=5 then WB_TAIL_GEN2_5 else if r=6 then WB_TAIL_GEN2_6
  else if r=7 then WB_TAIL_GEN2_7 else WB_TAIL_GEN2_8;;

(* the narrow tail frame for residue r, the frame of WB_TAIL_GEN2_r at
   shift_vals r: it writes only the last r output blocks *)
let wbn_narrow_frame r =
  el 3 (snd(strip_comb(snd(dest_imp(concl(SPECL (shift_vals r) (wbn_tail_gen2 r)))))));;

(* INNER_TAIL_FEED_TAC r tail_r: the tail leg of WBN_PREP_TO_END_FULL_r (the
   first half of its ENSURES_ADD_PRESERVED step),
     ensures ext2post (shifted band_post r) narrow_frame,
   by ENSURES_PRECONDITION_THM into tail_r = WB_TAIL_GEN2_r at shift_vals r. *)
let INNER_TAIL_FEED_TAC r tail_r =
  let rt = mk_small_numeral r in
  let m16r = mk_binop `( * ):num->num->num` `16` rt in
  let mnum = mk_small_numeral (16 * r) in
  let sv = shift_vals r in
  let tail = SPECL sv tail_r in
  let _,targs = strip_comb (snd(dest_imp(concl tail))) in
  let tail_pre = el 1 targs in
  let slice_close =
    MP_TAC(SPECL [`nblk:num`;`in_p:int64`;`ibytes:byte list`;`q:num`;mnum;`x:armstate`]
             WBN_INPUT_SLICE_GEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE(mk_eq(m16r,mnum))] THEN DISCH_THEN ACCEPT_TAC] in
  let counter_close =
    REPLICATE_TAC 14 AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC WORD_RULE in
  (* ivec: with the Q30 conjunct carried in wbn_weak_q_at5_return r, the
     shifted tail's precondition wants
     read Q30 = gcm_ctr_raw (word 8) (gcm_ctr_add (word (8*(q+1))) ctr0); the
     seam post (ext2post, rewritten in above) gives
     gcm_ctr_raw (word (8*q+16)) ctr0.  GCM_CTR_RAW_ABSORB_NUM absorbs the
     prior add into the counter offset (8*(q+1)+8 = 8*q+16). *)
  let q30_close =
    GEN_REWRITE_TAC RAND_CONV [GCM_CTR_RAW_ABSORB_NUM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC in
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC tail_pre THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE] THEN
    ABBREV_TAC `q = (nblk - 9) DIV 8` THEN
    SUBGOAL_THEN (subst[rt,`r_:num`] `16 * nblk = 128 * (q + 1) + 16 * r_`)
      ASSUME_TAC THENL
     [UNDISCH_TAC (subst[rt,`r_:num`] `nblk = 8 * (q + 1) + r_`) THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM GCM_CTR_ADD_1; GCM_CTR_ADD_COMPOSE] THEN
    MP_TAC(SPECL [`nblk:num`;`in_p:int64`;`ibytes:byte list`;`q:num`;m16r;`x:armstate`]
      WBN_INPUT_SLICE_GEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    REWRITE_TAC[SUB_LIST_MIN_RIGHT; ARITH_RULE(subst[rt,`r_:num`] `MIN 16 (16 * r_) = 16`);
                ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (subst[rt,`r_:num`]
      `word_sub (word_add in_p (word (128 * (q + 1) + 16 * r_)))
                (word_add in_p (word (128 * (q + 1)))):int64 = word (16 * r_)`)
      SUBST_ALL_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    FIRST [REFL_TAC; CONV_TAC WORD_RULE; counter_close; slice_close; q30_close];
    MP_TAC tail THEN ANTS_TAC THENL
     [CONJ_TAC THENL
        [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
         ALL_TAC] THEN
      REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NONOVERLAPPING_TAC);
      DISCH_THEN ACCEPT_TAC]];;

(* The r = 1 full-post leg, by its own tactic.  The tactic does not depend on
   the band, so it also proves the 9..16 leg's r = 1 case
   (WBN_PREP_TO_END_FULL_916_1 below). *)
let WBN_PREP_TO_END_FULL_1_HAND_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC (wbn_narrow_frame 1) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs(el 2 (snd(strip_comb(snd(dest_imp(concl(SPECL (shift_vals 1) WB_TAIL_GEN2_1)))))))),
            el 64 (conjuncts (snd(dest_abs wbn_prepretail_post_ext2)))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ABBREV_TAC `q = (nblk - 9) DIV 8` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `j < 8 * (q + 1)` THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM ACCEPT_TAC;
        SUBGOAL_THEN `j = 8 * (q + 1)` SUBST_ALL_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`; GCM_CTR_INC_ITER_AS_ADD] THEN
        FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
          (match lhs(concl th) with Comb(Comb(Const("read",_),_),_) ->
             (can (find_term (fun t -> t = `aes256_encrypt`)) (concl th)) | _ -> false)
          then SUBST1_TAC th else NO_TAC) THEN
        SUBGOAL_THEN `SUB_LIST (0,16) (SUB_LIST (128 * (q + 1),16 * 1) (ibytes:byte list)) =
                      SUB_LIST (128 * (q + 1),16) ibytes` SUBST1_TAC THENL
         [REWRITE_TAC[SUB_LIST_MIN_RIGHT] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN
        CONV_TAC WORD_RULE];
      CONJ_TAC THENL
       [REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE] THEN AP_TERM_TAC THEN
        SUBGOAL_THEN
          `list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) (ibytes:byte list))) nblk =
           list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) (8 * (q + 1) + 1)`
          SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[LIST_OF_SEQ_ADD; MAP_APPEND; GHASH_ACC_APPEND] THEN AP_TERM_TAC THEN
        REWRITE_TAC[LIST_OF_SEQ_CLAUSES; MAP; MULT_CLAUSES; ADD_CLAUSES] THEN
        REWRITE_TAC[SUB_LIST_MIN_RIGHT; ARITH_RULE `MIN 16 16 = 16`;
                    ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`];
        (* ivec: the shifted band's
           gcm_ctr_inc_iter 1 (gcm_ctr_add (word (8*(q+1))) ctr0) is
           gcm_ctr_inc_iter nblk ctr0 by GCM_CTR_INC_ITER_AS_ADD,
           GCM_CTR_ADD_COMPOSE and nblk = 8*(q+1)+1. *)
        REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD; GCM_CTR_ADD_COMPOSE] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC]];
    MATCH_MP_TAC ENSURES_ADD_PRESERVED THEN CONJ_TAC THENL
     [INNER_TAIL_FEED_TAC 1 WB_TAIL_GEN2_1;
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE; SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
      CONV_TAC(REDEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM] THEN
      CONV_TAC(REDEPTH_CONV BETA_CONV) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
        (match rhs(concl th) with Var("s'",_) -> true | _ -> false))) THEN
      SUBGOAL_THEN `nonoverlapping (word_add out_p (word (16 * j)):int64,16)
         (word_add out_p (word (128 * ((nblk - 9) DIV 8 + 1))),16)` ASSUME_TAC THENL
       [NONOVERLAPPING_TAC; ALL_TAC] THEN
      WBN_PUSH_LHS_READ_TAC THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) then MATCH_MP_TAC th else NO_TAC) THEN
      FIRST_X_ASSUM ACCEPT_TAC]];;

let WBN_PREP_TO_END_FULL_1 = prove(wbn_prep_to_end_full_goal 1,
  WBN_PREP_TO_END_FULL_1_HAND_TAC);;

(* the standalone per-block value bridge goal + tactic. *)
let wbn_block_bridge_goal r i =
  let it = mk_small_numeral i and rt = mk_small_numeral r in
  let gcph = subst[it,`i_:num`]
    `bytes_to_int128 (SUB_LIST (16 * (8 * (q + 1) + i_),16) (ibytes:byte list))` in
  let gval = list_mk_comb(`word_xor:int128->int128->int128`,
    [list_mk_comb(`word_xor:int128->int128->int128`,
       [gcph; list_mk_comb(`aes13`,[wbn_full_goal_ctr i;
          `k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;`k5:int128`;`k6:int128`;
          `k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;`k12:int128`;`k13:int128`])]);
     `k14:int128`]) in
  let scph = subst[it,`i_:num`;rt,`r_:num`]
    `bytes_to_int128 (SUB_LIST (16 * i_,16) (SUB_LIST (128 * (q + 1),16 * r_) (ibytes:byte list)))` in
  let sval = list_mk_comb(`word_xor:int128->int128->int128`,
    [scph; list_mk_comb(`aes256_encrypt`,
       [wbn_full_store_ctr i;
        `[k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]:(int128)list`])]) in
  mk_forall(`q:num`, mk_imp(subst[it,`i_:num`;rt,`r_:num`] `i_ < r_`, mk_eq(gval,sval)));;

let wbn_block_bridge_tac r i =
  let it = mk_small_numeral i and rt = mk_small_numeral r in
  let sublist_inst = SPECL [`ibytes:byte list`;`q:num`;it;rt] WBN_SUBLIST_SHIFT in
  let ctr_eq = mk_eq(wbn_full_goal_ctr i, wbn_full_store_ctr i) in
  GEN_TAC THEN DISCH_TAC THEN
  (MP_TAC sublist_inst THEN ANTS_TAC THENL [ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
  SUBGOAL_THEN ctr_eq SUBST1_TAC THENL
   [REWRITE_TAC[GCM_CTR_INC_FOLD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE;;

(* close one output block j = 8*(q+1)+i, one the tail stored, in the output
   forall of FULL_r *)
let wbn_block_close_tac r i =
  let brg = SPEC `q:num` (prove(wbn_block_bridge_goal r i, wbn_block_bridge_tac r i)) in
  let it = mk_small_numeral i in
  let mul_red = ARITH_RULE (mk_eq(mk_binop `( * ):num->num->num` `16` it,
                                  mk_small_numeral(16 * i))) in
  let common = REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD] THEN
    MP_TAC brg THEN (ANTS_TAC THENL [ARITH_TAC; ALL_TAC]) THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[mul_red] in
  if i = 0 then
    common THEN
    REWRITE_TAC[ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`; MULT_CLAUSES; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[]
  else
    let addr_eq = mk_eq(wbn_full_goal_addr i, wbn_full_store_addr i) in
    let addr_arith = subst[it,`i_:num`]
      `16 * (8 * (q + 1) + i_) = 128 * (q + 1) + 16 * i_` in
    common THEN
    SUBGOAL_THEN addr_eq SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE addr_arith; mul_red] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    FIRST_X_ASSUM ACCEPT_TAC;;

(* (A) the output forall for shift r: the blocks j < 8*(q+1) from the seam's
   forall, the others (case 2) by wbn_block_close_tac *)
let wbn_case2_forall_tac r =
  let one_block i =
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> match concl th with
      Comb(Comb(Const("=",_),Var("j",_)),_) -> true | _ -> false)) THEN
    wbn_block_close_tac r i in
  let disj = end_itlist (fun a b -> mk_disj(a,b))
    (map (fun i -> subst[mk_small_numeral i,`i_:num`] `j = 8 * (q + 1) + i_`) (0--(r-1))) in
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_CASES_TAC `j < 8 * (q + 1)` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN disj STRIP_ASSUME_TAC THENL
     ((UNDISCH_TAC (subst[mk_small_numeral r,`r_:num`] `nblk = 8 * (q + 1) + r_`) THEN
       UNDISCH_TAC `~(j < 8 * (q + 1))` THEN UNDISCH_TAC `j < nblk` THEN ARITH_TAC) ::
      map one_block (0--(r-1)))];;

(* (B) the tag fold: the explicit r-element tag list to list_of_seq cph nblk,
   split at 8*(q+1) by nblk = 8*(q+1)+r (LIST_OF_SEQ_ADD) *)
let wbn_tag_elt_close r i =
  let mul_red = ARITH_RULE (mk_eq(mk_binop `( * ):num->num->num` `16` (mk_small_numeral i),
                                  mk_small_numeral(16 * i))) in
  MP_TAC(REWRITE_RULE[mul_red; MULT_CLAUSES]
           (SPECL [`ibytes:byte list`;`q:num`;mk_small_numeral i;mk_small_numeral r]
              WBN_SUBLIST_SHIFT)) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN MATCH_ACCEPT_TAC];;
let wbn_tag_fold_tac r =
  let rt = mk_small_numeral r in
  AP_TERM_TAC THEN
  SUBGOAL_THEN (subst[rt,`r_:num`]
     `list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) (ibytes:byte list))) nblk =
      list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) (8 * (q + 1) + r_)`)
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIST_OF_SEQ_ADD; MAP_APPEND; GHASH_ACC_APPEND] THEN
  REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE] THEN AP_TERM_TAC THEN
  REWRITE_TAC[LIST_OF_SEQ_CLAUSES; LIST_OF_SEQ_CLAUSES_5_8; MAP; o_DEF] THEN
  REWRITE_TAC[CONS_11] THEN
  (if r = 1 then ALL_TAC else REPEAT CONJ_TAC) THEN
  FIRST (map (fun i -> AP_TERM_TAC THEN AP_TERM_TAC THEN wbn_tag_elt_close r i) (0--(r-1)));;

(* the intermediate post: the shifted band_post r of WB_TAIL_GEN2_r at
   shift_vals r, and the seam's forall over the first 8*(k+1) output blocks
   (conjunct 64 of wbn_prepretail_post_ext2) *)
let wbn_full_inter_post r =
  let band_post_r =
    el 2 (snd(strip_comb(snd(dest_imp(concl(SPECL (shift_vals r) (wbn_tail_gen2 r))))))) in
  mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs band_post_r),
            el 64 (conjuncts (snd(dest_abs wbn_prepretail_post_ext2)))));;

(* WBN_PREP_TO_END_FULL_r_TAC r, used here for r = 2..8:
   ENSURES_FRAME_SUBSUMED, then ENSURES_POSTCONDITION_THM with
   wbn_full_inter_post r, which splits into (A) the output forall, (B) the tag
   fold and the ivec write-back, and ENSURES_ADD_PRESERVED:
   INNER_TAIL_FEED_TAC, with the forall carried through the narrow tail
   writes. *)
let WBN_PREP_TO_END_FULL_r_TAC r =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC (wbn_narrow_frame r) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (wbn_full_inter_post r) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ABBREV_TAC `q = (nblk - 9) DIV 8` THEN
    CONJ_TAC THENL
     [wbn_case2_forall_tac r;
      CONJ_TAC THENL
       [wbn_tag_fold_tac r;
        (* ivec: the shifted band's
           gcm_ctr_inc_iter r (gcm_ctr_add (word (8*(q+1))) ctr0) is
           gcm_ctr_inc_iter nblk ctr0 by GCM_CTR_INC_ITER_AS_ADD,
           GCM_CTR_ADD_COMPOSE and nblk = 8*(q+1)+r. *)
        REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD; GCM_CTR_ADD_COMPOSE] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC]];
    MATCH_MP_TAC ENSURES_ADD_PRESERVED THEN CONJ_TAC THENL
     [INNER_TAIL_FEED_TAC r (wbn_tail_gen2 r);
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE; SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
      CONV_TAC(REDEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM] THEN
      CONV_TAC(REDEPTH_CONV BETA_CONV) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
        (match rhs(concl th) with Var("s'",_) -> true | _ -> false))) THEN
      SUBGOAL_THEN (subst[mk_small_numeral r,`r_:num`]
        `nonoverlapping (word_add out_p (word (16 * j)):int64,16)
         (word_add out_p (word (128 * ((nblk - 9) DIV 8 + 1))),16 * r_)`) ASSUME_TAC THENL
       [NONOVERLAPPING_TAC; ALL_TAC] THEN
      WBN_PUSH_LHS_READ_TAC THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) then MATCH_MP_TAC th else NO_TAC) THEN
      FIRST_X_ASSUM ACCEPT_TAC]];;

(* ------------------------------------------------------------------------- *)
(* The r = 2..8 legs, proved once on the union band 9 <= nblk.               *)
(*                                                                           *)
(* WBN_PREP_TO_END_FULL_r_TAC uses no band literal (17 <= nblk or 9 <= nblk) *)
(* and no band-specific lemma; it only abbreviates q = (nblk-9) DIV 8.  Its  *)
(* two consumer families, FULL_r on 17 <= nblk and FULL_916_r on             *)
(* 9 <= nblk /\ nblk <= 16, are therefore derived from one proof per r on    *)
(* the weaker band 9 <= nblk (WBN_PREP_TO_END_FREE_r) by strengthening the   *)
(* hypotheses.  The ensures term is the same for all three bands (only the   *)
(* band conjunct of the hypotheses differs), so MATCH_MP_TAC and             *)
(* ASM_ARITH_TAC close each, and the derived theorems keep the statements    *)
(* the dispatchers wbn_full_thm and wbn_full_916_thm use.                    *)
(* ------------------------------------------------------------------------- *)

(* the wide front hypotheses with the band conjunct `17<=nblk` weakened to
   `9<=nblk`. *)
let wbn_front_hyps_free_tm =
  let rec repl t = match t with
    | Comb(Comb(Const("/\\",_),a),b) -> mk_conj(repl a, repl b)
    | _ -> if t = `17 <= nblk` then `9 <= nblk` else t in
  repl wbn_front_hyps_wide_tm;;

(* the full-post goal for residue r on the union band 9 <= nblk *)
let wbn_prep_to_end_full_free_goal r =
  let nblk_eq = subst[mk_small_numeral r,`r_:num`]
                  `nblk = 8 * ((nblk - 9) DIV 8 + 1) + r_` in
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_free_tm :: nblk_eq :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_prepretail_post_ext2; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

(* r = 2..8 on the union band 9 <= nblk, one proof per r. *)

let WBN_PREP_TO_END_FREE_2 = prove(wbn_prep_to_end_full_free_goal 2, WBN_PREP_TO_END_FULL_r_TAC 2);;
let WBN_PREP_TO_END_FREE_3 = prove(wbn_prep_to_end_full_free_goal 3, WBN_PREP_TO_END_FULL_r_TAC 3);;
let WBN_PREP_TO_END_FREE_4 = prove(wbn_prep_to_end_full_free_goal 4, WBN_PREP_TO_END_FULL_r_TAC 4);;
let WBN_PREP_TO_END_FREE_5 = prove(wbn_prep_to_end_full_free_goal 5, WBN_PREP_TO_END_FULL_r_TAC 5);;
let WBN_PREP_TO_END_FREE_6 = prove(wbn_prep_to_end_full_free_goal 6, WBN_PREP_TO_END_FULL_r_TAC 6);;
let WBN_PREP_TO_END_FREE_7 = prove(wbn_prep_to_end_full_free_goal 7, WBN_PREP_TO_END_FULL_r_TAC 7);;
let WBN_PREP_TO_END_FREE_8 = prove(wbn_prep_to_end_full_free_goal 8, WBN_PREP_TO_END_FULL_r_TAC 8);;

(* r = 2..8, derived from the union-band FREE_r without re-simulation; r = 1 is
   WBN_PREP_TO_END_FULL_1 above. *)

let WBN_PREP_TO_END_FULL_2 = prove(wbn_prep_to_end_full_goal 2, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_2);;
let WBN_PREP_TO_END_FULL_3 = prove(wbn_prep_to_end_full_goal 3, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_3);;
let WBN_PREP_TO_END_FULL_4 = prove(wbn_prep_to_end_full_goal 4, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_4);;
let WBN_PREP_TO_END_FULL_5 = prove(wbn_prep_to_end_full_goal 5, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_5);;
let WBN_PREP_TO_END_FULL_6 = prove(wbn_prep_to_end_full_goal 6, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_6);;
let WBN_PREP_TO_END_FULL_7 = prove(wbn_prep_to_end_full_goal 7, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_7);;
let WBN_PREP_TO_END_FULL_8 = prove(wbn_prep_to_end_full_goal 8, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_8);;

(* ------------------------------------------------------------------------- *)
(* WBN_PREP_TO_END: the 8-way case split on r = 1 + (nblk-9) MOD 8.          *)
(*                                                                           *)
(* From the seam post to the full nblk-uniform wbn_end_post, under 9 <= nblk *)
(* and the three side conditions.  Each residue rr in {0..7} dispatches to   *)
(* WBN_PREP_TO_END_FULL_(rr+1); the per-branch length hypothesis             *)
(* nblk = 8*((nblk-9) DIV 8 + 1) + (rr+1) follows by ARITH from the DIVISION *)
(* identity and 9 <= nblk.                                                   *)
(* ------------------------------------------------------------------------- *)

let wbn_full_thm = Array.of_list
  [WBN_PREP_TO_END_FULL_1;  (* index 0 is a placeholder; entry r is FULL_r *)
   WBN_PREP_TO_END_FULL_1; WBN_PREP_TO_END_FULL_2; WBN_PREP_TO_END_FULL_3;
   WBN_PREP_TO_END_FULL_4; WBN_PREP_TO_END_FULL_5; WBN_PREP_TO_END_FULL_6;
   WBN_PREP_TO_END_FULL_7; WBN_PREP_TO_END_FULL_8];;

let wbn_prep_to_end_goal_final =
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_wide_tm :: `9 <= nblk` :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_prepretail_post_ext2; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

let WBN_PREP_TO_END = prove(wbn_prep_to_end_goal_final,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `nblk - 9` (MATCH_MP DIVISION (ARITH_RULE `~(8 = 0)`))) THEN
  ABBREV_TAC `rr = (nblk - 9) MOD 8` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `rr < 8` then MP_TAC th else NO_TAC) THEN
  REWRITE_TAC[ARITH_RULE
    `rr < 8 <=> rr = 0 \/ rr = 1 \/ rr = 2 \/ rr = 3 \/
                rr = 4 \/ rr = 5 \/ rr = 6 \/ rr = 7`] THEN
  STRIP_TAC THEN
  FIRST (map (fun r ->
    MATCH_MP_TAC wbn_full_thm.(r) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `nblk - 9 = (nblk - 9) DIV 8 * 8 + rr` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `9 <= nblk` THEN ARITH_TAC) (1--8)));;

(* ------------------------------------------------------------------------- *)
(* WBN_FRONT_TO_END: the whole >=17 chain, from pc+0x1c to the core exit:    *)
(* WBN_FRONT_TO_PREP_EXT2 then WBN_PREP_TO_END, by ENSURES_TRANS_SIMPLE      *)
(* (they share the frame wbn_front_C_tm and meet at                          *)
(* wbn_prepretail_post_ext2).  The precondition is wbn_front_P_tm, the front *)
(* precondition at pc+0x1c; the post is wbn_end_post.  The three side        *)
(* conditions of the shifted tail ride the antecedent outward (only          *)
(* WBN_PREP_TO_END needs them), and 9 <= nblk follows from 17 <= nblk.       *)
(* ------------------------------------------------------------------------- *)

let wbn_front_to_end_goal =
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_wide_tm :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_front_P_tm; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

let WBN_FRONT_TO_END = prove(wbn_front_to_end_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_prepretail_post_ext2 THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    MATCH_MP_TAC WBN_FRONT_TO_PREP_EXT2 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WBN_PREP_TO_END THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `17 <= nblk` THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The nblk 9..16 leg: the main loop is not entered.                         *)
(*                                                                           *)
(* For 9 <= nblk <= 16, q = (nblk - 9) DIV 8 = 0 and                         *)
(* d = 128 * ((nblk - 1) DIV 8) = 128, since (nblk - 1) DIV 8 = 1 throughout *)
(* 9..16.  So at the loop-skip branch (the b.ge 0xa0c at 0x4b8, on the cmp   *)
(* x0,x5 at 0x45c) X0 = in_p + 128 equals X5 = in_p + 128: the branch is     *)
(* taken, and control goes from the front straight to the prepretail 0xa0c.  *)
(* (For nblk >= 17, d >= 256, so X0 < X5 and the b.ge falls through to the   *)
(* loop head 0x4bc: the path of WBN_FRONT_TO_END.)                           *)
(*                                                                           *)
(* The 9..16 leg is therefore a chain of three parts:                        *)
(*   front       pc+0x1c -> 0xa0c (b.ge taken)  WBN_FRONT_TO_PREP_916        *)
(*   prepretail  0xa0c -> pc+3824, k = 0        WBN_PREPRETAIL_EXT2_916      *)
(*   tail        pc+3824 -> pc+4508             WBN_PREP_TO_END_916          *)
(* The front shares its prefix simulation with the >=17 front                *)
(* (WBN_FRONT_PREFIX_EXT) and differs from it only in the hypotheses         *)
(* (9 <= nblk /\ nblk <= 16 for 17 <= nblk) and in the resolution of the     *)
(* 0x4b8 branch, which changes only the PC.  The prepretail is               *)
(* WBN_PREPRETAIL_EXT2_UNIFIED, and the tail is symbolic in q, so it covers  *)
(* q = 0.                                                                    *)
(* ------------------------------------------------------------------------- *)

(* The 9..16 band: wbn_front_hyps_wide_tm with 17 <= nblk replaced by
   9 <= nblk /\ nblk <= 16. *)
let wbn_front_hyps_916_tm =
  let rec repl t = match t with
    | Comb(Comb(Const("/\\",_),a),b) -> mk_conj(repl a, repl b)
    | _ -> if t = `17 <= nblk` then `9 <= nblk /\ nblk <= 16` else t in
  repl wbn_front_hyps_wide_tm;;

(* (nblk-1) DIV 8 = 1 for 9..16  ->  the loop-skip pointer d = 128*1 = 128. *)
let DIV8_916 = prove
 (`!nblk. 9 <= nblk /\ nblk <= 16 ==> (nblk - 1) DIV 8 = 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL[`nblk - 1`;`8`] DIVISION) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* Resolve the 0x4b8 b.ge for 9..16 (taken, d = 128): rewrite with
   (nblk - 1) DIV 8 = 1, then WB_PTRCMP_FLAGS with a = d = 128 turns the branch
   condition into 128 < 128, that is F, in the assumptions. *)
let WBN_RESOLVE_49C_916_TAC : tactic = fun (asl,w) ->
  (MP_TAC(SPEC `nblk:num` DIV8_916) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                        REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
   MP_TAC(SPECL [`in_p:int64`; `128`; `128`] WB_PTRCMP_FLAGS) THEN
   ANTS_TAC THENL
    [CONJ_TAC THEN MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN
     MP_TAC(ASSUME `9 <= nblk`) THEN ARITH_TAC;
     ALL_TAC] THEN
   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(128 < 128) <=> F`;
                               ARITH_RULE `128 * 1 = 128`])) (asl,w);;

(* The close of the 9..16 front leg at s296, after the taken b.ge: the
   invariant core at i = 0, as in the first branch of
   WBN_LOOP_INVARIANT_ENTRY_RAW. *)
let ENTRY_CLOSER_916 =
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[wbn_loop_inv_core_raw] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
  REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD; GCM_CTR_ADD_1; GSYM GCM_CTR_ADD_LANES] THEN
  REWRITE_TAC[list_of_seq; MAP; ghash_polyval_acc] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES;
     GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES; GCM_CTR_INC5_LANES;
     GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
  REWRITE_TAC[GCM_CTR_ADD_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM GCM_CTR_ADD_LANES; GCM_CTR_ADD_0] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[GCM_CTR_ADD_0] THEN
  REWRITE_TAC[gcm_ctr_raw_def;
    WORD_RULE `word_add (word_add (x:32 word) (word 12)) (word 1) =
               word_add x (word 13)`;
    WORD_ADD_0];;

(* The postcondition of the 9..16 front leg: wbn_core_applied 0 at PC 0xa0c. *)
let wbn_entry_post_916 =
  mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc`;
      `read PC s = word (pc + 0xa0c)`;
      mk_comb(mk_comb(wbn_core_applied,`0:num`),`s:armstate`)]);;

let wbn_front_to_prep_916_goal =
  let ens = list_mk_comb(`ensures arm`,[wbn_front_P_tm; wbn_entry_post_916; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_916_tm, ens));;

(* The 9..16 front leg: the shared prefix WBN_FRONT_PREFIX_EXT (pc+0x1c to the
   0x4b8 b.ge, with the loop constants R) via ENSURES_TRANS_SIMPLE, then step
   296: the b.ge is taken for 9..16 (WBN_RESOLVE_49C_916_TAC) and lands at the
   prepretail entry 0xa0c with wbn_core_applied 0, closed by ENTRY_CLOSER_916
   and WB_PTRCMP_FLAGS.  The htable predicate is unfolded into its reads right
   after the init, so that they propagate through step 296 (the stepper does
   not track the folded htable_mem_dec). *)
let WBN_FRONT_TO_PREP_916 = prove(wbn_front_to_prep_916_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_front_prefix_ext_post THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_PREFIX_EXT THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ENSURES_INIT_TAC "s295" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
    WBN_RESOLVE_49C_916_TAC THEN
    ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (296--296) THEN
    wb_front_fold_tac THEN
    ENTRY_CLOSER_916 THEN
    MP_TAC(SPECL [`in_p:int64`; `128`; `128`] WB_PTRCMP_FLAGS) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN
      MP_TAC(ASSUME `9 <= nblk`) THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ARITH_RULE `(128 < 128) <=> F`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[htable_mem_dec] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[];
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC]]);;

(* The 9..16 prepretail, derived without simulation from
   WBN_PREPRETAIL_EXT2_UNIFIED by strengthening the hypotheses: that theorem is
   proved on the band 9 <= nblk, which contains 9..16, so MATCH_MP_TAC and
   ASM_ARITH_TAC close it. *)
let wbn_prepretail_ext2_916_goal =
  let kk = `(nblk - 9) DIV 8` in
  let pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc`;
      `read PC s = word (pc + 0xa0c)`;
      mk_comb(mk_comb(wbn_core_applied,kk),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[pre; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_916_tm, ens));;

let WBN_PREPRETAIL_EXT2_916 =
  prove(wbn_prepretail_ext2_916_goal,
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC WBN_PREPRETAIL_EXT2_UNIFIED THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* The 9..16 front and prepretail composed, from pc+0x1c to the seam post
   wbn_prepretail_post_ext2.  The precondition bridge reduces (nblk - 9) DIV 8
   to 0 (q = 0 for 9..16), which turns the postcondition of the front
   (wbn_core_applied 0) into the precondition of the prepretail. *)
let wbn_front_to_prep_ext2_916_goal =
  let ens = list_mk_comb(`ensures arm`,
    [wbn_front_P_tm; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_916_tm, ens));;

let WBN_FRONT_TO_PREP_EXT2_916 = prove(wbn_front_to_prep_ext2_916_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_entry_post_916 THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_TO_PREP_916 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (rand(rator(rator(snd(dest_imp(snd(strip_forall(concl WBN_PREPRETAIL_EXT2_916)))))))) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      SUBGOAL_THEN `(nblk - 9) DIV 8 = 0` SUBST1_TAC THENL
       [MP_TAC(SPECL[`nblk - 9`;`8`] DIVISION) THEN ASM_ARITH_TAC;
        DISCH_THEN(fun th -> ACCEPT_TAC th)];
      MATCH_MP_TAC WBN_PREPRETAIL_EXT2_916 THEN ASM_REWRITE_TAC[]]]);;

(* WBN_PREP_TO_END_916: from the seam to the core exit for the 9..16 band.
   Like WBN_PREP_TO_END it splits on the residue rr = (nblk - 9) MOD 8 into the
   legs WBN_PREP_TO_END_FULL_916_r, r = rr + 1 (symbolic in q, here q = 0),
   with the 9..16 hypotheses. *)

(* The 9..16 version of wbn_prep_to_end_full_goal. *)
let wbn_prep_to_end_full_916_goal r =
  let nblk_eq = subst[mk_small_numeral r,`r_:num`]
                  `nblk = 8 * ((nblk - 9) DIV 8 + 1) + r_` in
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_916_tm :: nblk_eq :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_prepretail_post_ext2; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

(* r = 1 uses WBN_PREP_TO_END_FULL_1_HAND_TAC, the tactic of
   WBN_PREP_TO_END_FULL_1, which does not depend on the band; r = 2..8 are
   derived, with no re-simulation, from the WBN_PREP_TO_END_FREE_r theorems
   proved on the band 9 <= nblk above. *)
let WBN_PREP_TO_END_FULL_916_1 = prove(wbn_prep_to_end_full_916_goal 1, WBN_PREP_TO_END_FULL_1_HAND_TAC);;
let WBN_PREP_TO_END_FULL_916_2 = prove(wbn_prep_to_end_full_916_goal 2, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_2);;
let WBN_PREP_TO_END_FULL_916_3 = prove(wbn_prep_to_end_full_916_goal 3, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_3);;
let WBN_PREP_TO_END_FULL_916_4 = prove(wbn_prep_to_end_full_916_goal 4, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_4);;
let WBN_PREP_TO_END_FULL_916_5 = prove(wbn_prep_to_end_full_916_goal 5, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_5);;
let WBN_PREP_TO_END_FULL_916_6 = prove(wbn_prep_to_end_full_916_goal 6, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_6);;
let WBN_PREP_TO_END_FULL_916_7 = prove(wbn_prep_to_end_full_916_goal 7, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_7);;
let WBN_PREP_TO_END_FULL_916_8 = prove(wbn_prep_to_end_full_916_goal 8, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_8);;

let wbn_full_916_thm = Array.of_list
  [WBN_PREP_TO_END_FULL_916_1;  (* index 0 unused; use r directly 1..8 *)
   WBN_PREP_TO_END_FULL_916_1; WBN_PREP_TO_END_FULL_916_2; WBN_PREP_TO_END_FULL_916_3;
   WBN_PREP_TO_END_FULL_916_4; WBN_PREP_TO_END_FULL_916_5; WBN_PREP_TO_END_FULL_916_6;
   WBN_PREP_TO_END_FULL_916_7; WBN_PREP_TO_END_FULL_916_8];;

let wbn_prep_to_end_916_goal =
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_916_tm :: `9 <= nblk` :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_prepretail_post_ext2; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

let WBN_PREP_TO_END_916 = prove(wbn_prep_to_end_916_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `nblk - 9` (MATCH_MP DIVISION (ARITH_RULE `~(8 = 0)`))) THEN
  ABBREV_TAC `rr = (nblk - 9) MOD 8` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `rr < 8` then MP_TAC th else NO_TAC) THEN
  REWRITE_TAC[ARITH_RULE
    `rr < 8 <=> rr = 0 \/ rr = 1 \/ rr = 2 \/ rr = 3 \/
                rr = 4 \/ rr = 5 \/ rr = 6 \/ rr = 7`] THEN
  STRIP_TAC THEN
  FIRST (map (fun r ->
    MATCH_MP_TAC wbn_full_916_thm.(r) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `nblk - 9 = (nblk - 9) DIV 8 * 8 + rr` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `9 <= nblk` THEN ARITH_TAC) (1--8)));;

(* WBN_FRONT_TO_END_916: the whole 9..16 chain, from pc+0x1c to the core exit:
   WBN_FRONT_TO_PREP_EXT2_916 then WBN_PREP_TO_END_916, by
   ENSURES_TRANS_SIMPLE. *)
let wbn_front_to_end_916_goal =
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_916_tm :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_front_P_tm; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

let WBN_FRONT_TO_END_916 = prove(wbn_front_to_end_916_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_prepretail_post_ext2 THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    MATCH_MP_TAC WBN_FRONT_TO_PREP_EXT2_916 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WBN_PREP_TO_END_916 THEN ASM_REWRITE_TAC[]]);;

(* gcm_dec_pt_bytes at a symbolic nblk: (16 * nblk) DIV 16 = nblk blocks. *)
let GCM_DEC_PT_BYTES_WHOLE_SYM = prove
 (`!nblk ibytes ctr0 rk. 1 <= nblk
     ==> gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk =
         aes_ctr_bytes ctr0 (gcm_dec_blocks_from 0 nblk ibytes) rk`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_dec_pt_bytes] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Pointwise data output.                                                    *)
(*                                                                           *)
(* The data postcondition of the spines is the whole-buffer byte-list form   *)
(* byte_list_at (gcm_dec_pt_bytes (16 * nblk) ..), which reads as though     *)
(* arbitrary byte lengths were accepted.  The pointwise form                 *)
(*   !j. j<nblk ==> read(memory:>bytes128(out_p+16j)) s = EL j (aes_ctr ...) *)
(* says that the routine handles whole blocks, in the shape of the other     *)
(* AES-GCM proofs; the exported theorems are stated in it, so it is not      *)
(* folded back into the byte-list form.                                      *)
(* ------------------------------------------------------------------------- *)

(* The 16 bytes at offset 16 * j of int128_list_to_bytes repack to EL j: the
   reverse direction of the int128-list / byte-list correspondence. *)
let SUB_LIST_INT128_LIST_TO_BYTES_EL = prove
 (`!cts j. j < LENGTH cts
     ==> bytes_to_int128 (SUB_LIST (16 * j,16) (int128_list_to_bytes cts)) =
         EL j cts`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `SUB_LIST (16 * j,16) (int128_list_to_bytes (cts:int128 list)) =
     int128_to_bytes (EL j cts)`
   SUBST1_TAC THENL
   [REWRITE_TAC[LIST_EQ] THEN
    REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_INT128_LIST_TO_BYTES;
                LENGTH_OF_INT128_TO_BYTES] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `j < n ==> MIN 16 (16 * n - 16 * j) = 16`];
      X_GEN_TAC `i:num` THEN REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`16 * j`; `int128_list_to_bytes (cts:int128 list)`;
                     `16 * j + i`; `16`] EL_SUB_LIST_GENERAL) THEN
      REWRITE_TAC[LENGTH_INT128_LIST_TO_BYTES] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(16 * j + i) - 16 * j = i` SUBST1_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(SPECL [`cts:int128 list`; `16 * j + i`] EL_INT128_LIST_TO_BYTES) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `(16 * j + i) DIV 16 = j /\ (16 * j + i) MOD 16 = i`
        (CONJUNCTS_THEN SUBST1_TAC) THENL
       [ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_EQ; DIV_LT; MOD_LT] THEN
        REWRITE_TAC[ADD_CLAUSES];
        ALL_TAC] THEN
      ASM_SIMP_TAC[EL_INT128_TO_BYTES]];
    REWRITE_TAC[BYTES_TO_INT128_OF_INT128_TO_BYTES]]);;

(* byte_list_at (gcm_dec_pt_bytes ..) -> the per-block bytes128 reads.  At
   16 * nblk bytes gcm_dec_pt_bytes is the flattened counter-mode stream over
   the nblk input blocks (GCM_DEC_PT_BYTES_WHOLE_SYM), so each 16-byte slice is
   EL j of it: BYTE_LIST_AT_1BLOCKS at byte 16 * j reads block j as that slice,
   and the repack lemma above closes it back to EL j. *)
let WBN_OUTPUT_POINTWISE = prove
 (`!nblk ibytes ctr0 rk out_p s.
     1 <= nblk /\ 128 * nblk < 2 EXP 64 /\
     byte_list_at (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk)
                  out_p (word (16 * nblk)) s
     ==> !j. j < nblk
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 EL j (aes_ctr ctr0 (gcm_dec_blocks_from 0 nblk ibytes) rk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `byte_list_at (int128_list_to_bytes
        (aes_ctr ctr0 (gcm_dec_blocks_from 0 nblk ibytes) rk))
        out_p (word (16 * nblk)) s`
   ASSUME_TAC THENL
   [ASM_MESON_TAC[GCM_DEC_PT_BYTES_WHOLE_SYM; aes_ctr_bytes]; ALL_TAC] THEN
  SUBGOAL_THEN
    `LENGTH (int128_list_to_bytes
        (aes_ctr ctr0 (gcm_dec_blocks_from 0 nblk ibytes) rk)) =
     val (word (16 * nblk):int64)`
   ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_INT128_LIST_TO_BYTES; LENGTH_AES_CTR;
                LENGTH_GCM_DEC_BLOCKS_FROM] THEN
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MP_TAC(ASSUME `128 * nblk < 2 EXP 64`) THEN ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`16 * j`; `int128_list_to_bytes
                   (aes_ctr ctr0 (gcm_dec_blocks_from 0 nblk ibytes) rk)`;
                 `out_p:int64`; `word (16 * nblk):int64`; `s:armstate`]
         BYTE_LIST_AT_1BLOCKS) THEN
  ASM_REWRITE_TAC[LENGTH_INT128_LIST_TO_BYTES; LENGTH_AES_CTR;
                  LENGTH_GCM_DEC_BLOCKS_FROM] THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) &&
         (try can (find_term (fun t -> t = `val (word (16 * nblk):int64)`))
                  (concl th) with _ -> false)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[LENGTH_INT128_LIST_TO_BYTES; LENGTH_AES_CTR;
                LENGTH_GCM_DEC_BLOCKS_FROM] THEN
    MP_TAC(ASSUME `j < nblk`) THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUB_LIST_INT128_LIST_TO_BYTES_EL THEN
  REWRITE_TAC[LENGTH_AES_CTR; LENGTH_GCM_DEC_BLOCKS_FROM] THEN
  MP_TAC(ASSUME `j < nblk`) THEN ARITH_TAC);;

(* Per-block value bridge: the store value of wbn_end_post,
   word_xor (word_xor cph (aes13 ..)) k14, is EL j of aes_ctr over the
   gcm_dec_blocks_from list and the 15 round keys.  A separate lemma keeps the
   AES and counter algebra out of the ensures context; it is the symbolic-j
   analogue of build_aes_ctr_el. *)
let WBN_ENDBLOCK_IS_AES_CTR = prove
 (`!nblk ibytes ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 j.
     j < nblk
     ==> word_xor
           (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16) ibytes))
             (aes13 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
                    k10 k11 k12 k13))
           k14 =
         EL j (aes_ctr ctr0 (gcm_dec_blocks_from 0 nblk ibytes)
                 [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`nblk:num`; `0`; `j:num`; `ibytes:byte list`]
    EL_GCM_DEC_BLOCKS_FROM) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`gcm_dec_blocks_from 0 nblk ibytes`; `ctr0:int128`;
    `[k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]:int128 list`; `j:num`]
    EL_AES_CTR) THEN
  ASM_REWRITE_TAC[LENGTH_GCM_DEC_BLOCKS_FROM] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE);;

(* The output bridge: the per-block store forall of wbn_end_post
   (word_xor (word_xor cph (aes13 ..)) k14) collapses to
   byte_list_at (gcm_dec_pt_bytes (16 * nblk) ..) over the whole buffer, the
   symbolic-nblk analogue of the BYTE_LIST_AT_WHOLE_CTR leg of
   prove_wb_wrapper.  128 * nblk < 2 EXP 64 (from the chain hypotheses) gives
   val (word (16 * nblk)) = 16 * nblk. *)
let WBN_END_OUTPUT_BYTE_LIST = prove
 (`!nblk ibytes ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 out_p s.
     1 <= nblk /\ 128 * nblk < 2 EXP 64 /\
     (!j. j < nblk
          ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
              word_xor
              (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16) ibytes))
              (aes13 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
               k10 k11 k12 k13))
              k14)
     ==> byte_list_at
           (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0
              [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])
           out_p (word (16 * nblk)) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GCM_DEC_PT_BYTES_WHOLE_SYM] THEN
  MATCH_MP_TAC BYTE_LIST_AT_WHOLE_CTR THEN EXISTS_TAC `nblk:num` THEN
  REWRITE_TAC[LENGTH_GCM_DEC_BLOCKS_FROM] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC WBN_ENDBLOCK_IS_AES_CTR THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Roadmap of the theorems below.                                            *)
(*                                                                           *)
(* The exported theorems come at the end of the file, in the shared AES-GCM  *)
(* vocabulary of aes_gcm_spec.ml: the correctness contract                   *)
(* AES256_GCM_DEC_ALT_NOIBT_SUBROUTINE_CORRECT (the AAPCS64 wrapper) for the *)
(* trimmed code (that of a -DNO_IBT build),                                  *)
(* AES256_GCM_DEC_ALT_SUBROUTINE_CORRECT for the full code (by               *)
(* ARM_ADD_IBT_RULE) with its all-zero-key instance                          *)
(* AES256_GCM_DEC_ALT_ZERO_KEY_CORRECT, and the matching safety theorems     *)
(* AES256_GCM_DEC_ALT_SAFE, AES256_GCM_DEC_ALT_NOIBT_SUBROUTINE_SAFE and     *)
(* AES256_GCM_DEC_ALT_SUBROUTINE_SAFE.  The correctness contract is derived, *)
(* without re-running any simulation, from two internal spines with a free   *)
(* GHASH key H and byte-list input and output, by fixing the key words, H    *)
(* and the counter block to the shared FIPS-197 / NIST convention and        *)
(* restating the input and the output per block (WBN_EXPORT_FROM_SPINE_TAC): *)
(*   WBN_DEC_CORE_BYTELIST        the core, pc+0x1c to pc+4508               *)
(*   WBN_DEC_SUBROUTINE_BYTELIST  the ABI wrapper: entry guard, d8-d15       *)
(*                                spills, WBN_DEC_CORE_BYTELIST, restores    *)
(* WBN_DEC_CORE_BYTELIST splits on the block count:                          *)
(*   nblk <= 8        AES256_GCM_DEC_ALT_DISPATCH (the <=8-block chain)      *)
(*   9 <= nblk <= 16  WBN_FRONT_TO_END_916 (the main loop is skipped)        *)
(*   nblk >= 17       WBN_FRONT_TO_END ((nblk - 9) DIV 8 loop iterations)    *)
(* Each nblk > 8 chain composes, by ENSURES_TRANS_SIMPLE, the segments the   *)
(* code runs in sequence:                                                    *)
(*   front       WBN_FRONT_PREFIX (pc+0x1c to the 0x4b8 b.ge), then for      *)
(*               >= 17 WBN_FRONT_BUF to the loop head 0x4bc (with the loop   *)
(*               constants WBN_FRONT_BUF_EXT, as the i = 0 invariant         *)
(*               WBN_LOOP_INVARIANT_ENTRY_RAW), for 9..16                    *)
(*               WBN_FRONT_TO_PREP_916 to 0xa0c                              *)
(*   loop        WBN_MAIN_LOOP_raw, 0x4bc to 0xa0c over all the iterations   *)
(*   prepretail  WBN_PREPRETAIL_EXT2_UNIFIED, 0xa0c to the seam pc+3824      *)
(*               (0xef0)                                                     *)
(*   tail        WBN_PREP_TO_END / WBN_PREP_TO_END_916, the seam to the core *)
(*               exit pc+4508 (0x119c), through the cascade or the exact-8   *)
(*               drain                                                       *)
(* with WBN_LOOP_PREP_EXT2 = loop ; prepretail,                              *)
(* WBN_FRONT_TO_PREP_EXT2 = front ; loop ; prepretail,                       *)
(* WBN_FRONT_TO_PREP_EXT2_916 = front ; prepretail and                       *)
(* WBN_FRONT_TO_END(_916) = WBN_FRONT_TO_PREP_EXT2(_916) ; tail.             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* WBN_DEC_CORE_BYTELIST: the core spine, pc+0x1c to pc+4508, for every      *)
(* nblk >= 1, with H free and the output as the whole-buffer byte list.      *)
(*                                                                           *)
(* The statement is written out in full.  It is the DISPATCH statement with  *)
(* nblk <= 8 replaced by 1 <= nblk and with the two size premises            *)
(* 128 * nblk < 2 EXP 64 and val in_p + 16 * nblk < 2 EXP 63 added: for      *)
(* nblk <= 8 they follow from the small nblk, for a symbolic nblk they rule  *)
(* out pointer and length overflow.  (The exported subroutine theorem gets   *)
(* the first from the 64-bit len_bits and keeps the second as a              *)
(* precondition.)                                                            *)
(*                                                                           *)
(* The proof splits on nblk: nblk <= 8 is DISPATCH, already in the NIST      *)
(* vocabulary; 9..16 is WBN_FRONT_TO_END_916 and >= 17 WBN_FRONT_TO_END.     *)
(* These chains go from wbn_front_P_tm (the raw xi, the key words k0..k14    *)
(* read one by one, htable_mem_dec h) to wbn_end_post (the raw per-block     *)
(* stores), and WBN_CHAIN_TO_NIST_TAC moves them to the NIST vocabulary      *)
(* under the band identifications                                            *)
(*   ki := EL i rk,  h := byteswap128 (ghash_twist H),                       *)
(*   xi := word_reversefields 8 tag0                                         *)
(* by ENSURES_PRECONDITION_THM (the NIST precondition implies the raw one:   *)
(* KEY_READS_FROM_WORDLIST, HTABLE_MEM_DEC_IS_HTABLE_MEM_8,                  *)
(* BYTESWAP128_INVOLUTION, BYTE_LIST_AT_TO_READ_BYTES) and                   *)
(* ENSURES_POSTCONDITION_THM (the raw postcondition implies the NIST one:    *)
(* RK_ETA_15 and WBN_END_OUTPUT_BYTE_LIST for the output,                    *)
(* WBN_TAG_NIST_BRIDGE for the tag).  The hypotheses of the chains are the   *)
(* flattened ALLPAIRS / PAIRWISE / ALL ones.                                 *)
(* ------------------------------------------------------------------------- *)

let WBN_DEC_CORE_BYTELIST = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p nblk ibytes rk H
    tag0 ctr0.
    1 <= nblk /\
    128 * nblk < 2 EXP 64 /\
    val in_p + 16 * nblk < 2 EXP 63 /\
    LENGTH ibytes = 16 * nblk /\
    LENGTH rk = 15 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16]
    [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,240; htable_p,192; stackpointer,80] /\
    PAIRWISE nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16] /\
    ALL (nonoverlapping (stackpointer,80))
    [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,240; htable_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
              read PC s = word (pc + 28) /\
              read SP s = stackpointer /\
              C_ARGUMENTS
                [in_p; word (128 * nblk); out_p; tag_p; ivec_p; key_p; htable_p]
                s /\
              byte_list_at ibytes in_p (word (16 * nblk)) s /\
              read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
              read (memory :> bytes128 ivec_p) s = ctr0 /\
              wordlist_from_memory (key_p,15) s = rk /\
              htable_mem_8 (ghash_twist H) htable_p s)
         (\s. read PC s = word (pc + 4508) /\
              read X9 s = word (16 * nblk) /\
              byte_list_at (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p
              (word (16 * nblk)) s /\
              read (memory :> bytes128 tag_p) s =
              word_reversefields 8
              (nist_ghash H tag0
              (list_of_seq (nist_input_block_bytes ibytes) nblk)) /\
              read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter nblk ctr0)
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
          [memory :> bytes (out_p,16 * nblk); memory :> bytes (tag_p,16);
           memory :> bytes (ivec_p,16);
           memory :> bytes (word_add stackpointer (word 64),16)] ,,
          MAYCHANGE
          [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14;
           Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27;
           Q28; Q29; Q30; Q31])`,
  (* The proof moves the raw per-block vocabulary of the chains to the NIST
     vocabulary of DISPATCH; these helpers are local to the proof. *)
  (* identification substitution: raw chain vars -> DISPATCH NIST vars *)
  let idsub =
    [`word_reversefields 8 (tag0:int128)`,`xi:int128`;
     `byteswap128 (ghash_twist H)`,`h:int128`] @
    (map (fun i -> mk_comb(mk_comb(`EL:num->(int128)list->int128`,mk_small_numeral i),
                           `rk:int128 list`),
                   mk_var("k"^string_of_int i,`:int128`)) (0--14)) in
  let raw_pre'  = subst idsub wbn_front_P_tm
  and raw_post' = subst idsub wbn_end_post in
  (* the shared reconcile tactic, parameterized by the chain theorem *)
  let WBN_CHAIN_TO_NIST_TAC chain_thm =
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC raw_pre' THEN CONJ_TAC THENL
     [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[HTABLE_MEM_DEC_IS_HTABLE_MEM_8; BYTESWAP128_INVOLUTION] THEN
      MP_TAC(SPECL [`key_p:int64`; `rk:int128 list`; `s:armstate`]
        KEY_READS_FROM_WORDLIST) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`ibytes:byte list`; `in_p:int64`; `word (16 * nblk):int64`;
        `s:armstate`] BYTE_LIST_AT_TO_READ_BYTES) THEN
      SUBGOAL_THEN `val (word (16 * nblk):int64) = 16 * nblk` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC raw_post' THEN
      CONJ_TAC THENL
       [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN
           `gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk =
            gcm_dec_pt_bytes (16 * nblk) ibytes ctr0
              [EL 0 rk;EL 1 rk;EL 2 rk;EL 3 rk;EL 4 rk;EL 5 rk;EL 6 rk;EL 7 rk;
               EL 8 rk;EL 9 rk;EL 10 rk;EL 11 rk;EL 12 rk;EL 13 rk;EL 14 rk]`
           SUBST1_TAC THENL
           [AP_TERM_TAC THEN MATCH_MP_TAC RK_ETA_15 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
          MATCH_MP_TAC WBN_END_OUTPUT_BYTE_LIST THEN ASM_REWRITE_TAC[];
          (* The ivec conjunct is the same in the raw and the NIST post (idsub
             touches neither ctr0 nor gcm_ctr_inc_iter), so the
             ASM_REWRITE_TAC[] above discharged it: this leg is the tag alone,
             a single conjunct. *)
          MP_TAC(SPECL [`H:int128`; `byteswap128 (ghash_twist H)`;
            `word_reversefields 8 (tag0:int128)`; `tag0:int128`; `ibytes:byte list`;
            `nblk:num`] WBN_TAG_NIST_BRIDGE) THEN
          REWRITE_TAC[BYTESWAP128_INVOLUTION] THEN DISCH_THEN MATCH_ACCEPT_TAC];
        MATCH_MP_TAC chain_thm THEN
        RULE_ASSUM_TAC(REWRITE_RULE
          [ALLPAIRS; PAIRWISE; ALL; MAP; NONOVERLAPPING_CLAUSES]) THEN
        REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; MAP; NONOVERLAPPING_CLAUSES] THEN
        REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_ARITH_TAC) THEN
        ASM_MESON_TAC[NONOVERLAPPING_MODULO_SYM; nonoverlapping]]] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `nblk <= 8` THENL
   [ASM_MESON_TAC[AES256_GCM_DEC_ALT_DISPATCH]; ALL_TAC] THEN
  ASM_CASES_TAC `nblk <= 16` THENL
   [WBN_CHAIN_TO_NIST_TAC WBN_FRONT_TO_END_916;
    WBN_CHAIN_TO_NIST_TAC WBN_FRONT_TO_END]);;

(* ------------------------------------------------------------------------- *)
(* WBN_DEC_SUBROUTINE_BYTELIST: the ABI wrapper spine (H free, byte-list     *)
(* output), from which the exported subroutine theorem is derived below      *)
(* (through WBN_DEC_VALID_CALL_CORRECT).  It covers len_bits = 128 * nblk    *)
(* for any nblk, so it is the whole-blocks contract of the function: for     *)
(* nblk = 0 the entry cbz x1 is taken and the function returns 0, with the   *)
(* output empty and the tag unchanged; for nblk >= 1 the entry guard falls   *)
(* through and the prologue, the core and the epilogue run.                  *)
(*                                                                           *)
(* The code: the entry guard (cbz x1; tst x1,#127; b.ne, at 0x0..0x8) comes  *)
(* before the d8-d15 spills (stp d8,d9,[sp,#-80]! and three more stp, at     *)
(* 0xc..0x18); the core runs from pc+0x1c to its exit pc+0x119c (pc+4508);   *)
(* the epilogue (mov x0,x9; the ldp of d10..d15; ldp d8,d9,[sp],#80; ret, at *)
(* 0x119c..0x11b0) restores the registers.  X30 is not saved; ret returns    *)
(* through it.                                                               *)
(*                                                                           *)
(* The wrapper is written by hand rather than with ARM_ADD_RETURN_STACK_TAC: *)
(* the guard fall-through facts must be in the assumptions before the first  *)
(* steps (without them the PC after the b.ne stays symbolic), and the core   *)
(* is instantiated at the in-frame SP:                                       *)
(* - WB_CORE_INST is WBN_DEC_CORE_BYTELIST at                                *)
(*   stackpointer := word_sub stackpointer (word 80), the SP after the       *)
(*   stp ..,[sp,#-80]! of the prologue;                                      *)
(* - WB_CORE_INST_UF2 unfolds its input memory predicates (byte_list_at,     *)
(*   wordlist_from_memory, htable_mem_8) and reduces val (word (16 * nblk))  *)
(*   to 16 * nblk (from 128 * nblk < 2 EXP 64), so that the stepper carries  *)
(*   the quantified input-byte read past the stack stores instead of         *)
(*   dropping it;                                                            *)
(* - WB_GUARD_FALLTHROUGH_TAC adds the guard fall-through facts              *)
(*   val (word (128 * nblk)) = 128 * nblk, ~(128 * nblk = 0) and             *)
(*   val (word_and (word (128 * nblk)) (word 127)) = 0.                      *)
(*                                                                           *)
(* Then ARM_STEPS_TAC 1--7 (guard and spills), ARM_BIGSTEP_TAC s8 (the       *)
(* core), ARM_STEPS_TAC 9--14 (the epilogue) and ENSURES_FINAL_STATE_TAC.    *)
(* d8-d15 are preserved because the stack frame of the core,                 *)
(* bytes (sp + 64,16), is disjoint from the spill area [sp, sp + 64).        *)
(* ------------------------------------------------------------------------- *)

let WBN_DEC_SUBROUTINE_BYTELIST = prove
   (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p nblk ibytes rk H
      tag0 ctr0 returnaddress.
      128 * nblk < 2 EXP 64 /\
      val in_p + 16 * nblk < 2 EXP 63 /\
      LENGTH ibytes = 16 * nblk /\
      LENGTH rk = 15 /\
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16]
      [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,240; htable_p,192;
       word_sub stackpointer (word 80),80] /\
      PAIRWISE nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16] /\
      ALL (nonoverlapping (word_sub stackpointer (word 80),80))
      [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,240; htable_p,192]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word pc /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS
               [in_p; word (128 * nblk); out_p; tag_p; ivec_p; key_p; htable_p]
               s /\
               byte_list_at ibytes in_p (word (16 * nblk)) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = returnaddress /\
               C_RETURN s = word (16 * nblk) /\
               byte_list_at (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p
               (word (16 * nblk)) s /\
               read (memory :> bytes128 tag_p) s =
               word_reversefields 8
               (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) nblk)) /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter nblk ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE
           [memory :> bytes (out_p,16 * nblk); memory :> bytes (tag_p,16);
            memory :> bytes (ivec_p,16);
            memory :> bytes (word_sub stackpointer (word 80),80)])`,
  (* The wrapper is written by hand (see above); these helpers are local to the
     proof. *)
  let EXEC = AES256_GCM_DEC_ALT_EXEC in
  (* the core, SP set to the post-prologue in-frame value *)
  let WB_CORE_INST =
    SPECL [`pc:num`; `word_sub stackpointer (word 80):int64`;
           `in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
           `key_p:int64`; `htable_p:int64`; `nblk:num`; `ibytes:byte list`;
           `rk:int128 list`; `H:int128`; `tag0:int128`; `ctr0:int128`]
          WBN_DEC_CORE_BYTELIST in
  (* val(word(16*nblk))=16*nblk from 128*nblk<2 EXP 64 (so 16*nblk<2 EXP 64) *)
  let VAL16EQ = prove
   (`128 * nblk < 2 EXP 64 ==> val (word (16 * nblk):int64) = 16 * nblk`,
    DISCH_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    ASM_ARITH_TAC) in
  (* unfold folded input mem preds + concretize the byte bound in the core *)
  let WB_CORE_INST_UF2 =
    REWRITE_RULE[byte_list_at; wordlist_from_memory; HTABLE_MEM_8_FLAT; DIMINDEX_128;
                 fst EXEC; UNDISCH VAL16EQ] WB_CORE_INST in
  (* guard fall-through: cbz/b.ne both fall through for len_bits = 128*nblk *)
  let WB_GUARD_FALLTHROUGH_TAC =
    SUBGOAL_THEN `val (word (128 * nblk):int64) = 128 * nblk` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(128 * nblk = 0)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val (word_and (word (128 * nblk):int64) (word 127)) = 0`
      ASSUME_TAC THENL
     [SUBGOAL_THEN `(127:num) = 2 EXP 7 - 1` SUBST1_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(2:num) EXP 7 = 128` SUBST1_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      REWRITE_TAC[MOD_MULT];
      ALL_TAC] in
  REWRITE_TAC[byte_list_at; wordlist_from_memory; HTABLE_MEM_8_FLAT; DIMINDEX_128;
                fst EXEC] THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; PAIRWISE; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    (* nblk = 0: the entry cbz x1 (0x0) is taken before the prologue, so the
       function returns 0 in X0 touching no memory (L256_dec_ret at 0x170c:
       mov w0,#0; ret); d8-d15 and SP are untouched (never spilled).  The
       output byte list is empty (byte_list_at over word 0 is vacuous) and the
       tag is unchanged (nist_ghash H tag0 [] = tag0). *)
    ASM_CASES_TAC `nblk = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; ARITH_RULE `128 * 0 = 0`;
                  ARITH_RULE `16 * 0 = 0`] THEN
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
        MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS; fst EXEC] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[byte_list_at; list_of_seq; nist_ghash; VAL_WORD_0;
                      ARITH_RULE `i < 0 <=> F`; gcm_ctr_inc_iter];
      ALL_TAC] THEN
    SUBGOAL_THEN `1 <= nblk` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val (word (16 * nblk):int64) = 16 * nblk` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC WB_CORE_INST_UF2 THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; PAIRWISE; ALLPAIRS; ALL] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MATCH_MP_TAC ALIGNED_WORD_SUB THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[aligned; WORD_VAL] THEN CONV_TAC WORD_REDUCE_CONV THEN
      REWRITE_TAC[DIMINDEX_64] THEN CONJ_TAC THEN CONV_TAC NUM_DIVIDES_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
       MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS; fst EXEC] THEN
    DISCH_THEN(fun th ->
      (ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
       MAP_EVERY (fun c -> ENSURES_PRESERVED_DREG_TAC ("init_"^fst(dest_const c)) c)
         [`D8`;`D9`;`D10`;`D11`;`D12`;`D13`;`D14`;`D15`]) THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
      WB_GUARD_FALLTHROUGH_TAC THEN
      ARM_STEPS_TAC EXEC (1--7) THEN MP_TAC th) THEN
    ARM_BIGSTEP_TAC EXEC "s8" THENL
     [REWRITE_TAC[C_ARGUMENTS] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC(!simulation_precanon_thms) THEN ARM_STEPS_TAC EXEC (9--14) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_BLAST `(word_zx:int128->int64)(word_zx(x:int64)) = x`] THEN
      CONV_TAC WORD_RULE]);;

(* ------------------------------------------------------------------------- *)
(* Bridge: the whole-buffer byte-list output collapses to the per-block,     *)
(* NIST-nonce-named keystream form of the exported theorems:                 *)
(*   byte_list_at (gcm_dec_pt_bytes ..) ==> !j. j < nblk ==>                 *)
(*     read bytes128 (out_p + 16 j) = cph_j XOR E_K(nonce||(c + j))          *)
(* given word_bytereverse ctr0 = ctr_block nonce c.  It combines             *)
(* WBN_OUTPUT_POINTWISE (byte list -> EL j of aes_ctr), EL_AES_CTR (element  *)
(* j is input block j XOR its keystream) and GCM_CTR_INC_ITER_CTR_BLOCK (the *)
(* counter gcm_ctr_inc_iter j ctr0 is the byte-reversed NIST block           *)
(* nonce||(c + j)).                                                          *)
(* ------------------------------------------------------------------------- *)
let WBN_OUTPUT_POINTWISE_NONCE = prove
 (`!nblk ibytes ctr0 rk out_p s nonce c.
     1 <= nblk /\ 128 * nblk < 2 EXP 64 /\
     word_bytereverse ctr0 = ctr_block nonce c /\
     byte_list_at (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk)
                  out_p (word (16 * nblk)) s
     ==> !j. j < nblk
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (EL j (gcm_dec_blocks_from 0 nblk ibytes))
                          (aes256_encrypt
                             (word_bytereverse (ctr_block nonce (c + j))) rk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`nblk:num`; `ibytes:byte list`; `ctr0:int128`; `rk:int128 list`;
               `out_p:int64`; `s:armstate`] WBN_OUTPUT_POINTWISE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`gcm_dec_blocks_from 0 nblk ibytes`; `ctr0:int128`;
               `rk:int128 list`; `j:num`] EL_AES_CTR) THEN
  REWRITE_TAC[LENGTH_GCM_DEC_BLOCKS_FROM] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`j:num`; `nonce:96 word`; `c:num`; `ctr0:int128`]
    GCM_CTR_INC_ITER_CTR_BLOCK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Abstract indexed-input bridges.  They restate the exported contracts over *)
(* an abstract input function inblock : num -> int128, pinned by a per-block *)
(* read hypothesis, the shape of the other AES-GCM proofs.  The internal     *)
(* byte-list spine is instantiated with the concrete witness                 *)
(*   ibytes := int128_list_to_bytes (list_of_seq inblock nblk)               *)
(* and these lemmas discharge its byte_list_at precondition and rewrite its  *)
(* EL / nist_input_block_bytes vocabulary back to inblock.  No simulation.   *)
(* ------------------------------------------------------------------------- *)

(* pointwise list_of_seq congruence (only the values at i < n matter). *)
let LIST_OF_SEQ_EQ_PTWISE = prove
 (`!(f:num->B) g n. (!i. i < n ==> f i = g i) ==> list_of_seq f n = list_of_seq g n`,
  ONCE_REWRITE_TAC[MESON[] `(!f g n. P f g n) <=> (!n f g. P f g n)`] THEN
  INDUCT_TAC THEN REWRITE_TAC[LIST_OF_SEQ] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:num->B) 0 = g 0` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o
    check (fun th -> is_forall(concl th))) THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* Input assembler: the per-block int128 reads (= inblock j) assemble into the
   byte_list_at precondition of the spine, at ibytes = the flattened list.  The
   mirror of WBN_OUTPUT_POINTWISE (byte_list_at -> per-block reads). *)
let WBN_INPUT_ASSEMBLE = prove
 (`!inblock nblk in_p s.
     128 * nblk < 2 EXP 64 /\
     (!j. j < nblk
          ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
              inblock j)
     ==> byte_list_at (int128_list_to_bytes (list_of_seq inblock nblk)) in_p
                      (word (16 * nblk)) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[byte_list_at] THEN
  SUBGOAL_THEN `val (word (16 * nblk):int64) = 16 * nblk` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MP_TAC(ASSUME `128 * nblk < 2 EXP 64`) THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i DIV 16 < nblk` ASSUME_TAC THENL
   [SUBGOAL_THEN `i < 16 * nblk` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`list_of_seq (inblock:num->int128) nblk`; `i:num`]
    EL_INT128_LIST_TO_BYTES) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  SUBGOAL_THEN
    `word_add in_p (word i):int64 =
     word_add (word_add in_p (word (16 * (i DIV 16)))) (word (i MOD 16))`
    SUBST1_TAC THENL
   [SUBGOAL_THEN `i = 16 * (i DIV 16) + i MOD 16`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
     [MESON_TAC[DIVISION_SIMP]; ALL_TAC] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  MP_TAC(SPECL [`word_add in_p (word (16 * (i DIV 16))):int64`; `s:armstate`;
                `i MOD 16`] BYTE8_OF_BYTES128) THEN
  ANTS_TAC THENL [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then MP_TAC(SPEC `i DIV 16` th) else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* Identity A: input block j read off the assembled ibytes is inblock j. *)
let INBLOCK_OF_ASSEMBLED = prove
 (`!inblock nblk j. j < nblk
     ==> bytes_to_int128
           (SUB_LIST (16 * j,16)
             (int128_list_to_bytes (list_of_seq inblock nblk))) = inblock j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`list_of_seq (inblock:num->int128) nblk`; `j:num`]
    SUB_LIST_INT128_LIST_TO_BYTES_EL) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;

(* Identity A': gcm_dec_blocks_from over the assembled ibytes is inblock. *)
let GCM_DEC_BLOCKS_FROM_ASSEMBLED = prove
 (`!inblock nblk j. j < nblk
     ==> EL j (gcm_dec_blocks_from 0 nblk
                 (int128_list_to_bytes (list_of_seq inblock nblk))) = inblock j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`nblk:num`; `0`; `j:num`;
                `int128_list_to_bytes (list_of_seq (inblock:num->int128) nblk)`]
         EL_GCM_DEC_BLOCKS_FROM) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[INBLOCK_OF_ASSEMBLED]);;

(* Identity B: the GHASH input list over the assembled ibytes is the shared
   NIST (big-endian) view of inblock.  In decryption GHASH runs over the
   ciphertext, which is the input, so the byte-list view nist_input_block_bytes
   of the spines becomes nist_input_block (aes_gcm_spec.ml). *)
let NIST_INPUT_OF_ASSEMBLED = prove
 (`!inblock nblk.
     list_of_seq
       (nist_input_block_bytes (int128_list_to_bytes (list_of_seq inblock nblk))) nblk =
     list_of_seq (nist_input_block inblock) nblk`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ_PTWISE THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[nist_input_block_bytes; nist_input_block] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC INBLOCK_OF_ASSEMBLED THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The house AES-256 against the FIPS-197 cipher, and the keystream and the  *)
(* counter write-back in the shared vocabulary (aes_gcm_spec.ml).            *)
(*                                                                           *)
(* The spines state the keystream with the house aes256_encrypt              *)
(* (aes_encrypt_spec.ml) over the round keys as they sit in memory.  The     *)
(* exported theorems use the shared key convention: rk is the FIPS-197       *)
(* schedule, and memory holds MAP (word_reversefields 8) rk.  Both ciphers   *)
(* are the kernel's aese/aesmc tower: AES256_XOR_ENCRYPT_RECONSTRUCT (above) *)
(* folds the tower to aes256_encrypt, and XOR_AES256_CIPHER_RECONSTRUCT      *)
(* (aes_gcm_common.ml) folds it to aes256_cipher, so the two lemmas at a     *)
(* zero data block give the relation.                                        *)
(* ========================================================================= *)

let AES256_ENCRYPT_AS_CIPHER = prove
 (`!x (rk:int128 list).
     LENGTH rk = 15
     ==> aes256_encrypt x (MAP (word_reversefields 8) rk) =
         word_reversefields 8 (aes256_cipher (word_reversefields 8 x) rk)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP RK_ETA_15) THEN REWRITE_TAC[MAP] THEN
  MP_TAC(SPECL
   (`x:int128` :: `word 0:int128` ::
    map (fun i -> mk_comb(`word_reversefields 8:int128->int128`,
                    mk_comb(mk_comb(`EL:num->int128 list->int128`,
                                    mk_small_numeral i), `rk:int128 list`)))
        (0--14))
   (REWRITE_RULE[aes13] AES256_XOR_ENCRYPT_RECONSTRUCT)) THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  REWRITE_TAC[WORD_BITWISE_RULE `word_xor (word 0) (x:int128) = x`;
              WORD_BITWISE_RULE `word_xor (x:int128) (word 0) = x`;
              MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  DISCH_THEN(ACCEPT_TAC o SYM));;

(* Block j's keystream, as WBN_OUTPUT_POINTWISE_NONCE states it at the       *)
(* exported instantiation, is the shared aes_ctr_block.                      *)
let AES256_ENCRYPT_CTR_AS_AES_CTR_BLOCK = prove
 (`!(nonce:96 word) c j (rk:int128 list).
     LENGTH rk = 15
     ==> aes256_encrypt (word_bytereverse (ctr_block nonce (c + j)))
                        (MAP (word_reversefields 8) rk) =
         aes_ctr_block aes256_cipher c nonce rk j`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[AES256_ENCRYPT_AS_CIPHER] THEN
  REWRITE_TAC[aes_ctr_block; BREV_RF8_128; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[ADD_SYM]);;

(* ------------------------------------------------------------------------- *)
(* The export lift.  WBN_EXPORT_FROM_SPINE_TAC spine proves a statement in   *)
(* the exported vocabulary from a spine, without re-running any simulation,  *)
(* by the instantiation                                                      *)
(*   rk     := MAP (word_reversefields 8) rk  (the memory image of the       *)
(*                                            FIPS-197 schedule rk)          *)
(*   H      := aes256_cipher (word 0) rk      (the NIST GHASH key,           *)
(*                                            E_K(0^128))                    *)
(*   ctr0   := word_reversefields 8 (ctr_block nonce c)                      *)
(*   ibytes := int128_list_to_bytes (list_of_seq inblock nblk)               *)
(* followed by restating the input per block (WBN_INPUT_ASSEMBLE), the       *)
(* output per block over the shared keystream (WBN_OUTPUT_POINTWISE_NONCE,   *)
(* GCM_DEC_BLOCKS_FROM_ASSEMBLED, AES256_ENCRYPT_CTR_AS_AES_CTR_BLOCK), the  *)
(* GHASH input as nist_input_block (NIST_INPUT_OF_ASSEMBLED) and the counter *)
(* write-back (GCM_CTR_INC_ITER_NIST_IVEC).  The key precondition forces     *)
(* LENGTH rk = 15, so the spine's hypothesis LENGTH rk = 15 needs no         *)
(* counterpart: when it fails, the precondition is unsatisfiable.  Every     *)
(* other hypothesis of the spine must be a hypothesis of the goal.           *)
(* ------------------------------------------------------------------------- *)

let WBN_EXPORT_FROM_SPINE_TAC spine =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `LENGTH(rk:int128 list) = 15` THENL
   [ALL_TAC;
    ENSURES_PRECONDITION_TAC `\s:armstate. F` THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM(fun th ->
        let c = concl th in
        if is_eq c &&
           can (find_term (fun t -> is_const t &&
                             fst(dest_const t) = "wordlist_from_memory")) c
        then MP_TAC(AP_TERM `LENGTH:int128 list->num` th) else NO_TAC) THEN
      REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY; LENGTH_MAP] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[ENSURES_TRIVIAL]]] THEN
  MP_TAC(INST
   [`MAP (word_reversefields 8) (rk:int128 list)`,`rk:int128 list`;
    `aes256_cipher (word 0) (rk:int128 list)`,`H:int128`;
    `word_reversefields 8 (ctr_block (nonce:96 word) c)`,`ctr0:int128`;
    `int128_list_to_bytes (list_of_seq (inblock:num->int128) nblk)`,
    `ibytes:byte list`]
   (SPEC_ALL spine)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_INT128_LIST_TO_BYTES; LENGTH_LIST_OF_SEQ;
                    LENGTH_MAP];
    ALL_TAC] THEN
  DISCH_THEN(fun sp ->
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (rand(rator(rator(concl sp)))) THEN CONJ_TAC THENL
     [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WBN_INPUT_ASSEMBLE THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
      EXISTS_TAC (rand(rator(concl sp))) THEN
      CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC sp]]) THEN
  X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[NIST_INPUT_OF_ASSEMBLED; GCM_CTR_INC_ITER_NIST_IVEC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL
   [`nblk:num`;
    `int128_list_to_bytes (list_of_seq (inblock:num->int128) nblk)`;
    `word_reversefields 8 (ctr_block (nonce:96 word) c)`;
    `MAP (word_reversefields 8) (rk:int128 list)`; `out_p:int64`;
    `s:armstate`; `nonce:96 word`; `c:num`] WBN_OUTPUT_POINTWISE_NONCE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[BREV_RF8_INV_128] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[GCM_DEC_BLOCKS_FROM_ASSEMBLED;
               AES256_ENCRYPT_CTR_AS_AES_CTR_BLOCK] THEN
  MATCH_ACCEPT_TAC WORD_XOR_SYM;;

(* The whole-block subroutine result for len_bits = 128 * nblk, any nblk     *)
(* including 0: an internal helper for the public arbitrary-length theorem.  *)
let WBN_DEC_VALID_CALL_CORRECT = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p nblk inblock rk
    tag0 nonce c returnaddress.
    128 * nblk < 2 EXP 64 /\
    val in_p + 16 * nblk < 2 EXP 63 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16]
    [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,240; htable_p,192;
     word_sub stackpointer (word 80),80] /\
    PAIRWISE nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16] /\
    ALL (nonoverlapping (word_sub stackpointer (word 80),80))
    [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,240; htable_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
              read PC s = word pc /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS
              [in_p; word (128 * nblk); out_p; tag_p; ivec_p; key_p; htable_p]
              s /\
              (!j. j < nblk
                   ==> read (memory :> bytes128
                              (word_add in_p (word (16 * j)))) s = inblock j) /\
              read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce c) /\
              wordlist_from_memory (key_p,15) s =
              MAP (word_reversefields 8) rk /\
              htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word (16 * nblk) /\
              (!j. j < nblk
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block aes256_cipher c nonce rk j)
                                (inblock j)) /\
              read (memory :> bytes128 tag_p) s =
              word_reversefields 8
              (nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_input_block inblock) nblk)) /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce (nblk + c)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
          [memory :> bytes (out_p,16 * nblk); memory :> bytes (tag_p,16);
           memory :> bytes (ivec_p,16);
           memory :> bytes (word_sub stackpointer (word 80),80)])`,
  WBN_EXPORT_FROM_SPINE_TAC WBN_DEC_SUBROUTINE_BYTELIST);;

(* The exported subroutine contract (the AAPCS64-callable result), for an
   arbitrary len_bits, first for the trimmed code, the code of a -DNO_IBT
   build.  gcm_wb_blocks len_bits is the number of blocks processed, and
   every data-dependent clause is indexed by it, so one postcondition
   describes all three paths:
   - a non-multiple of 128 is rejected by the entry guard (cbz falls through,
     tst/b.ne branches to the return), which returns 0 and touches no memory;
   - zero and the nonzero multiples of 128 are WBN_DEC_VALID_CALL_CORRECT at
     len_bits = word (128 * nblk), where 128 * nblk < 2 EXP 64 is just
     VAL_BOUND_64.
   The pointer bound val in_p + 16 * nblk < 2 EXP 63 is genuine: the kernel
   compares pointers with signed conditions.
   This routine does not enforce the NIST GCM message limit. Callers must
   ensure the cumulative message length does not exceed 2^36 - 32 bytes
   (2^39 - 256 bits). *)
let AES256_GCM_DEC_ALT_NOIBT_SUBROUTINE_CORRECT = prove
 (`!pc stackpointer in_p len_bits out_p tag_p ivec_p key_p htable_p inblock rk
    tag0 nonce c returnaddress.
    val in_p + 16 * gcm_wb_blocks len_bits < 2 EXP 63 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
    [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16]
    [word pc, LENGTH aes256_gcm_dec_alt_tmc;
     in_p,16 * gcm_wb_blocks len_bits; key_p,240; htable_p,192;
     word_sub stackpointer (word 80),80] /\
    PAIRWISE nonoverlapping
    [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16] /\
    ALL (nonoverlapping (word_sub stackpointer (word 80),80))
    [word pc, LENGTH aes256_gcm_dec_alt_tmc;
     in_p,16 * gcm_wb_blocks len_bits; key_p,240; htable_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
              read PC s = word pc /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS
              [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
              (!j. j < gcm_wb_blocks len_bits
                   ==> read (memory :> bytes128
                              (word_add in_p (word (16 * j)))) s = inblock j) /\
              read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce c) /\
              wordlist_from_memory (key_p,15) s =
              MAP (word_reversefields 8) rk /\
              htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word (16 * gcm_wb_blocks len_bits) /\
              (!j. j < gcm_wb_blocks len_bits
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block aes256_cipher c nonce rk j)
                                (inblock j)) /\
              read (memory :> bytes128 tag_p) s =
              word_reversefields 8
              (nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_input_block inblock)
                           (gcm_wb_blocks len_bits))) /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8
                (ctr_block nonce (gcm_wb_blocks len_bits + c)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
          [memory :> bytes
             (out_p,16 * gcm_wb_blocks len_bits);
           memory :> bytes (tag_p,16);
           memory :> bytes (ivec_p,16);
           memory :> bytes (word_sub stackpointer (word 80),80)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `nblk = gcm_wb_blocks len_bits` THEN
  ASM_CASES_TAC `val(len_bits:int64) MOD 128 = 0` THENL
   [(* Whole blocks, including zero: len_bits = word (128 * nblk). *)
    SUBGOAL_THEN `val(len_bits:int64) = 128 * nblk` ASSUME_TAC THENL
     [EXPAND_TAC "nblk" THEN ASM_SIMP_TAC[GCM_WB_BLOCKS_VALID];
      ALL_TAC] THEN
    SUBGOAL_THEN `128 * nblk < 2 EXP 64` ASSUME_TAC THENL
     [MP_TAC(ISPEC `len_bits:int64` VAL_BOUND_64) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `len_bits:int64 = word (128 * nblk)` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(fun th ->
        if concl th = `val(len_bits:int64) = 128 * nblk`
        then SUBST1_TAC(SYM th) else NO_TAC) THEN
      REWRITE_TAC[WORD_VAL];
      ALL_TAC] THEN
    MATCH_MP_TAC WBN_DEC_VALID_CALL_CORRECT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* A non-multiple of 128: cbz falls through, tst/b.ne rejects, and no
     memory is touched. *)
  SUBGOAL_THEN `nblk = 0` SUBST_ALL_TAC THENL
   [EXPAND_TAC "nblk" THEN REWRITE_TAC[gcm_wb_blocks] THEN
    ASM_REWRITE_TAC[COND_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(val(len_bits:int64) = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(val(len_bits:int64) MOD 128 = 0)` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(val(word_and (len_bits:int64) (word 127)) = 0)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `127 = 2 EXP 7 - 1` SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 EXP 7 = 128`];
    ALL_TAC] THEN
  REWRITE_TAC[MULT_CLAUSES;ADD_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_SIMD_REGS;MODIFIABLE_GPRS;
              MODIFIABLE_UPPER_SIMD_REGS;C_ARGUMENTS;C_RETURN;SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES256_GCM_DEC_ALT_EXEC (1--5) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[list_of_seq;nist_ghash] THEN
  REWRITE_TAC[ARITH_RULE `j < 0 <=> F`]);;

(* The same for the full code, with its BTI landing pad. *)

let AES256_GCM_DEC_ALT_SUBROUTINE_CORRECT = prove
 (`!pc stackpointer in_p len_bits out_p tag_p ivec_p key_p htable_p inblock rk
    tag0 nonce c returnaddress.
    val in_p + 16 * gcm_wb_blocks len_bits < 2 EXP 63 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
    [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16]
    [word pc, LENGTH aes256_gcm_dec_alt_mc;
     in_p,16 * gcm_wb_blocks len_bits; key_p,240; htable_p,192;
     word_sub stackpointer (word 80),80] /\
    PAIRWISE nonoverlapping
    [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16] /\
    ALL (nonoverlapping (word_sub stackpointer (word 80),80))
    [word pc, LENGTH aes256_gcm_dec_alt_mc;
     in_p,16 * gcm_wb_blocks len_bits; key_p,240; htable_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_mc /\
              read PC s = word pc /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS
              [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
              (!j. j < gcm_wb_blocks len_bits
                   ==> read (memory :> bytes128
                              (word_add in_p (word (16 * j)))) s = inblock j) /\
              read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce c) /\
              wordlist_from_memory (key_p,15) s =
              MAP (word_reversefields 8) rk /\
              htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word (16 * gcm_wb_blocks len_bits) /\
              (!j. j < gcm_wb_blocks len_bits
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block aes256_cipher c nonce rk j)
                                (inblock j)) /\
              read (memory :> bytes128 tag_p) s =
              word_reversefields 8
              (nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_input_block inblock)
                           (gcm_wb_blocks len_bits))) /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8
                (ctr_block nonce (gcm_wb_blocks len_bits + c)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
          [memory :> bytes
             (out_p,16 * gcm_wb_blocks len_bits);
           memory :> bytes (tag_p,16);
           memory :> bytes (ivec_p,16);
           memory :> bytes (word_sub stackpointer (word 80),80)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    ~extra:[htable_mem_8; htable_mem_4; wordlist_from_memory]
    aes256_gcm_dec_alt_mc aes256_gcm_dec_alt_tmc
    AES256_GCM_DEC_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* The exported theorem at the all-zero key:                                 *)
(* AES256_GCM_DEC_ALT_SUBROUTINE_CORRECT with rk the FIPS-197 schedule of    *)
(* that key and the key-table precondition evaluated to the real table (see  *)
(* ALT_ZERO_KEY_RULE in arm/proofs/utils/aes_gcm_common.ml).                 *)
(* ------------------------------------------------------------------------- *)

let AES256_GCM_DEC_ALT_ZERO_KEY_CORRECT =
  ALT_ZERO_KEY_RULE "AES256_GCM_DEC_ALT_ZERO_KEY_CORRECT"
    aes256_cipher AESAVS_ZERO_KEY_256_SCHEDULE
    `word 0x5a9144292508410f7b2b80f144811313:int128`
    AES256_GCM_DEC_ALT_SUBROUTINE_CORRECT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(*                                                                           *)
(* AES256_GCM_DEC_ALT_SAFE is the safety theorem of the core, from pc+0x1c   *)
(* to the core exit pc+4508, for len_bits = 128 * nblk with 1 <= nblk.       *)
(* CORE_SAFE_TAC splits on nblk:                                             *)
(* - bands 1..4: driven step by step from the core entry                     *)
(*   (concrete_band_close_tac);                                              *)
(* - bands 5..8: one shared front to the tail compare at pc+0xee4, then the  *)
(*   reusable tail theorem for the band (WB_TAIL_SAFE_1_EXISTS ..            *)
(*   WB_TAIL_SAFE_8_EXISTS);                                                 *)
(* - bands 9..16: a symbolic front through the prepretail to the same        *)
(*   compare, then the reusable tail for nblk - 8 blocks;                    *)
(* - nblk >= 17: the front to the loop head, the main loop                   *)
(*   (ENSURES_EVENTS_WHILE_UP2_TAC) and the prepretail, then the reusable    *)
(*   tail for the residue, (nblk - 9) MOD 8 + 1 blocks.                      *)
(*                                                                           *)
(* AES256_GCM_DEC_ALT_NOIBT_SUBROUTINE_SAFE adds the ABI wrapper, for any    *)
(* len_bits (ARBITRARY_WRAPPER_SAFE_TAC), and                                *)
(* AES256_GCM_DEC_ALT_SUBROUTINE_SAFE is its IBT lift (ARM_ADD_IBT_RULE).    *)
(* ------------------------------------------------------------------------- *)

let EXEC = AES256_GCM_DEC_ALT_EXEC;;

(* ---- DRIVE_TAC target maxsteps ----
   Steps one instruction at a time from the current state; when the PC becomes
   a symbolic if-term, applies WB_TAIL_RESOLVE_TAC to make it concrete, then
   steps on; stops when PC = word (pc + target).

   This is GEN_PROVE_SAFETY_SPEC_TAC's own driver loop (common/consttime.ml:
   find the `read PC` assumption, compare its right side with the destination,
   else take one more step) with one addition, which is why the stock tactic
   cannot be used here: the nblk dispatch leaves the PC a symbolic if-term
   part-way through a leg, and the stock loop has no resolver for that; it only
   compares for equality, so it would stop, having neither reached the
   destination nor made progress.  BIGNUM_EMONTREDC_8N_CORRECT resolves such a
   PC by hand (UNDISCH the if-term PC, rewrite it concrete, DISCH, keep
   stepping).  Here that would have to be repeated at every dispatch point of
   the twelve driven legs, the bands 1..4 and the eight residue tails, so the
   resolve step is part of the loop instead. ---- *)
let rec DRIVE_TAC target maxsteps : tactic = fun (asl,w) ->
  if maxsteps <= 0 then failwith "DRIVE_TAC: maxsteps exhausted" else
  let (sidx, off) = pc_info (asl,w) in
  if off = target then ALL_TAC (asl,w)
  else if off = -3 then failwith "DRIVE_TAC: no PC assumption"
  else if off = -2 then
    (WB_TAIL_RESOLVE_TAC THEN
     (fun g ->
        let (sidx2, off2) = pc_info g in
        if off2 = target then ALL_TAC g
        else if off2 = -2 then failwith "DRIVE_TAC: resolver left PC symbolic"
        else (ARM_QSTEP_TAC EXEC ("s"^string_of_int (sidx2+1)) THEN
              DRIVE_TAC target (maxsteps-1)) g)) (asl,w)
  else
    (ARM_QSTEP_TAC EXEC ("s"^string_of_int (sidx+1)) THEN
     DRIVE_TAC target (maxsteps-1)) (asl,w);;

(* ---- the opening of a simulated leg: unfold the list wrappers of the
   nonoverlapping hypotheses (keeping nonoverlapping itself folded, with the
   code length as a numeral), split the resulting conjunctions into single
   assumptions, init state s0 ---- *)
let LEG_INIT_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; ALLPAIRS; PAIRWISE; MAP; WB_MC_LEN]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  ENSURES_INIT_TAC "s0";;

(* ---- the concrete-band closer, for the bands 1..4 (the small-message path):
   open, then DRIVE from s0 to pc+4508, finalize.  Every branch condition on
   these bands is concrete arithmetic that the resolver reduces directly, so no
   band-specific step count is needed.  The bands 5..8 and 9..16 run a shared
   front instead (FRONT_58_CLOSE_TAC, front_916_sim_tac below). ---- *)
let concrete_band_close_tac =
  LEG_INIT_TAC THEN
  DRIVE_TAC 4508 700 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ---- n-way split of a bounded nblk leg lo..hi, then close each band ---- *)
let split_close_tac lo hi =
  WB_CASES_TAC `nblk:num` (lo,hi) ASM_ARITH_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  concrete_band_close_tac;;

let mk_tail_safe_goal r =
  subst [mk_small_numeral r,`rr:num`]
   `exists f_events.
      forall e pc stackpointer in_p out_p tag_p ivec_p key_p htable_p nblk
             tail_in tail_out.
        1 <= nblk /\
        128 * nblk < 2 EXP 64 /\
        contained (tail_in,16 * rr) (in_p,16 * nblk) /\
        contained (tail_out,16 * rr) (out_p,16 * nblk) /\
        nonoverlapping
          (word pc,LENGTH aes256_gcm_dec_alt_tmc) (stackpointer,80) /\
        ALLPAIRS nonoverlapping
          [out_p,16 * nblk; tag_p,16; ivec_p,16]
          [word pc,LENGTH aes256_gcm_dec_alt_tmc]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
                  read PC s = word (pc + 0xee4) /\
                  read X0 s = tail_in /\
                  read X2 s = tail_out /\
                  read X3 s = tag_p /\
                  read X5 s = word (16 * rr) /\
                  read X6 s = htable_p /\
                  read X10 s = word_add stackpointer (word 64) /\
                  read X16 s = ivec_p /\
                  read events s = e)
             (\s. read PC s = word (pc + 4508) /\
                  (exists e2.
                       read events s = APPEND e2 e /\
                       e2 =
                       f_events in_p key_p htable_p out_p tag_p ivec_p nblk
                                tail_in tail_out pc stackpointer /\
                       memaccess_inbounds e2
                       [in_p,16 * nblk; tag_p,16; ivec_p,16;
                        key_p,240; htable_p,192; out_p,16 * nblk;
                        stackpointer,80]
                       [out_p,16 * nblk; tag_p,16; ivec_p,16;
                        stackpointer,80]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
              [memory :> bytes (tail_out,16 * rr); memory :> bytes (tag_p,16);
               memory :> bytes (ivec_p,16);
               memory :> bytes (word_add stackpointer (word 64),16)] ,,
              MAYCHANGE
              [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13;
               Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25;
               Q26; Q27; Q28; Q29; Q30; Q31])`;;

let prove_tail_safe r =
  let tail_len = mk_binary "*" (`16`,mk_small_numeral r) in
  let tail_code_nonoverlap =
    subst [tail_len,`tail_len:num`]
      `nonoverlapping (word pc,5908) (tail_out:int64,tail_len)` in
  let tail_reads =
    subst [tail_len,`tail_len:num`]
      `[(tail_in:int64),tail_len; tag_p,16; ivec_p,16; key_p,240; htable_p,192;
        tail_out,tail_len; stackpointer,80]` in
  let tail_writes =
    subst [tail_len,`tail_len:num`]
      `[(tail_out:int64),tail_len; tag_p,16; ivec_p,16; stackpointer,80]` in
  prove(mk_tail_safe_goal r,
    META_EXISTS_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
                MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL; ALLPAIRS; WB_MC_LEN]) THEN
    REPEAT(FIRST_X_ASSUM
      (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    MAP_EVERY (fun t ->
        SUBGOAL_THEN t ASSUME_TAC THENL
         [ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN ASM_REWRITE_TAC[];
          ALL_TAC])
     [`nonoverlapping (word pc,5908) (out_p:int64,16 * nblk)`;
      `nonoverlapping (word pc,5908) (tag_p:int64,16)`;
      `nonoverlapping (word pc,5908) (ivec_p:int64,16)`] THEN
    SUBGOAL_THEN tail_code_nonoverlap ASSUME_TAC THENL
     [MATCH_MP_TAC NONOVERLAPPING_SUBREGIONS THEN
      MAP_EVERY EXISTS_TAC
       [`word pc:int64`; `5908`; `out_p:int64`; `16 * nblk`] THEN
      ASM_REWRITE_TAC[WB_CONTAINED_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `val (word (128 * nblk):int64) DIV 8 * 1 = 16 * nblk`
      SUBST_ALL_TAC THENL
     [MATCH_MP_TAC WB_SAFETY_BYTES_LEN THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    DRIVE_TAC 4508 400 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    WB_SAFETY_PROPERTY_TAC
     (W (fun (asl,w) ->
        let _,[evs; target_reads; target_writes] = strip_comb w in
        MATCH_MP_TAC
          (REWRITE_RULE[IMP_IMP]
            (ISPECL [evs; tail_reads; target_reads;
                     tail_writes; target_writes]
              MEMACCESS_INBOUNDS_CONTAINED))) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[ALL; EX; MEM] THEN
        ASM_REWRITE_TAC[WB_CONTAINED_REFL];
        DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC]));;

let WB_TAIL_SAFE_1_EXISTS = prove_tail_safe 1;;
let WB_TAIL_SAFE_2_EXISTS = prove_tail_safe 2;;
let WB_TAIL_SAFE_3_EXISTS = prove_tail_safe 3;;
let WB_TAIL_SAFE_4_EXISTS = prove_tail_safe 4;;
let WB_TAIL_SAFE_5_EXISTS = prove_tail_safe 5;;
let WB_TAIL_SAFE_6_EXISTS = prove_tail_safe 6;;
let WB_TAIL_SAFE_7_EXISTS = prove_tail_safe 7;;
let WB_TAIL_SAFE_8_EXISTS = prove_tail_safe 8;;

let wbn_tail_safeties =
  map SELECT_RULE
   [WB_TAIL_SAFE_1_EXISTS; WB_TAIL_SAFE_2_EXISTS;
    WB_TAIL_SAFE_3_EXISTS; WB_TAIL_SAFE_4_EXISTS;
    WB_TAIL_SAFE_5_EXISTS; WB_TAIL_SAFE_6_EXISTS;
    WB_TAIL_SAFE_7_EXISTS; WB_TAIL_SAFE_8_EXISTS];;

(* Specialize the selected r-block tail theorem to a leg with block count nblk
   whose residual tail reads tail_in and writes tail_out, at the current
   accumulated event trace of state sname.  Using the state equation's right
   side keeps the old state variable from surviving ARM_BIGSTEP_TAC's
   cleanup. *)
let MP_WB_TAIL_SAFE_TAC r sname nblk tail_in tail_out : tactic =
  let args =
    [`pc:num`; `stackpointer:int64`; `in_p:int64`; `out_p:int64`;
     `tag_p:int64`; `ivec_p:int64`; `key_p:int64`; `htable_p:int64`;
     nblk; tail_in; tail_out] in
  fun (asl,w) ->
    let ev = events_of_state asl (mk_var(sname,`:armstate`)) in
    MP_TAC(SPECL (ev :: args) (el (r-1) wbn_tail_safeties)) (asl,w);;

(* ---- the nblk 9..16 leg: the front runs symbolically, its branches resolved
   by GUARD_LE_FALLTHRU, WB_LOOPENTER_FLAGS_GE9 and WB_PTRCMP_FLAGS, and each
   band is made concrete only afterwards. ---- *)

let front_916_setup_tac =
  SUBGOAL_THEN `9 <= nblk` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)` ASSUME_TAC THENL
   [MATCH_MP_TAC USHR_128NBLK_ANY THEN NBLK_ARITH_GE9_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word_sub (word (16 * nblk)) (word 1)) (word 18446744073709551488):int64
       = word (128 * ((nblk - 1) DIV 8))` ASSUME_TAC THENL
   [MATCH_MP_TAC AND_MASK_16NBLK_ANY THEN NBLK_ARITH_GE9_TAC; ALL_TAC] THEN
  LEG_INIT_TAC THEN
  MP_TAC(SPEC `nblk:num` GUARD_LE_FALLTHRU) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [NBLK_ARITH_GE9_TAC;
      MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN NBLK_ARITH_GE9_TAC]; DISCH_TAC] THEN
  MP_TAC(SPECL [`in_p:int64`; `nblk:num`] WB_LOOPENTER_FLAGS_GE9) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [NBLK_ARITH_GE9_TAC;
      MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN NBLK_ARITH_GE9_TAC]; DISCH_TAC];;

(* front steps 1--295 to the b.ge at pc+1208 (0x4b8), the flags of its
   cmp x0,x5 at 0x45c resolved by WB_PTRCMP_FLAGS, then step 296 to the
   prepretail pc+2572 (0xa0c) *)
let front_916_sim_tac =
  ARM_QSTEPS_TAC EXEC (1--295) THEN
  SUBGOAL_THEN `(nblk - 1) DIV 8 = 1` ASSUME_TAC THENL
   [MP_TAC(ASSUME `9 <= nblk`) THEN MP_TAC(ASSUME `nblk <= 16`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(nblk - 1) DIV 8 = 1`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  MP_TAC(SPECL [`in_p:int64`; `128`; `128`] WB_PTRCMP_FLAGS) THEN ANTS_TAC THENL
   [CONJ_TAC THEN MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN
    MP_TAC(ASSUME `9 <= nblk`) THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(128 < 128) <=> F`]) THEN
  ARM_QSTEPS_TAC EXEC (296--296);;

(* ---- front invariant at pc+0x4bc (the loop head; the i=0 register state of
   wbn_loop_invariant_raw).  SEQUENCE augments it with e2 = f_ev_front. ---- *)
let front_inv = `\s:armstate.
     aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
     read SP s = stackpointer /\
     read X0 s = word_add in_p (word 128) /\
     read X2 s = word_add out_p (word 128) /\
     read X4 s = word_add in_p (word (16 * nblk)) /\
     read X5 s = word_add (word (128 * ((nblk - 1) DIV 8))) in_p /\
     read X9 s = word (16 * nblk) /\
     read X10 s = word_add stackpointer (word 64) /\
     read X1 s = word (128 * nblk) /\
     read X16 s = ivec_p /\
     read X6 s = htable_p /\
     read X3 s = tag_p /\
     read X11 s = key_p`;;

(* ---- nblk 5..8 shared front.  These four paths execute the same 270
   instructions from pc+0x1c through the taken branch at pc+0x448 and the
   common tail setup, landing at pc+0xee4 immediately before the tail compare.
   SEQUENCE augments the invariant with e2 = f_ev_58_front. ---- *)
let front_58_inv = `\s:armstate.
     aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
     read PC s = word (pc + 0xee4) /\
     read SP s = stackpointer /\
     read X0 s = in_p /\
     read X2 s = out_p /\
     read X3 s = tag_p /\
     read X4 s = word_add in_p (word (16 * nblk)) /\
     read X5 s = word (16 * nblk) /\
     read X6 s = htable_p /\
     read X9 s = word (16 * nblk) /\
     read X10 s = word_add stackpointer (word 64) /\
     read X11 s = key_p /\
     read X16 s = ivec_p`;;

let FRONT_58_ENTER_TAC =
  SUBGOAL_THEN `5 <= nblk` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~(nblk <= 4)`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;
    ALL_TAC] THEN
  LE8_58_LADDER_OPEN_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xee4` front_58_inv THEN CONJ_TAC;;

let FRONT_58_CLOSE_TAC =
  SUBGOAL_THEN `word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)` ASSUME_TAC THENL
   [MATCH_MP_TAC USHR_128NBLK_ANY THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_and (word_sub (word (16 * nblk)) (word 1))
             (word 18446744073709551488):int64 = word 0`
   ASSUME_TAC THENL
   [MATCH_MP_TAC AND_MASK_16NBLK THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  LEG_INIT_TAC THEN
  MP_TAC(SPEC `nblk:num` GUARD_LE_FALLTHRU) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  ARM_QSTEPS_TAC EXEC (1--267) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `nblk:num` D_ZERO_LE8)
    (CONJ (MATCH_MP (ARITH_RULE `5 <= nblk ==> 1 <= nblk`) (ASSUME `5 <= nblk`))
          (ASSUME `nblk <= 8`))]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  SUBGOAL_THEN `ival (in_p:int64) - ival in_p = &0` ASSUME_TAC THENL
   [CONV_TAC INT_ARITH; ALL_TAC] THEN
  ARM_QSTEPS_TAC EXEC (268--270) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_sub (word_add in_p (word (16 * nblk))) in_p:int64 = word (16 * nblk)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let close_58_tail_band k =
  UNDISCH_TAC (mk_eq(`nblk:num`, mk_small_numeral k)) THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  LEG_INIT_TAC THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  MP_WB_TAIL_SAFE_TAC k "s0" (mk_small_numeral k) `in_p:int64` `out_p:int64` THEN
  ANTS_TAC THENL
   [REWRITE_TAC[WB_CONTAINED_REFL; ALLPAIRS; ALL; WB_MC_LEN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN WB_FIRST_NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  USE_WB_TAIL_SAFE_TAC
   (GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    DISCHARGE_WB_COMPOSED_TAIL_TAC);;

(* ---- >=17 leg entry.  Leaves two subgoals: the front (pc+28 to pc+1212),
   then the rest (loop and tail, pc+1212 to pc+4508). ---- *)
let GE17_ENTER_TAC =
  GE17_PREP_TAC THEN RESHAPE_LOOP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x4bc` front_inv THEN CONJ_TAC;;

(* ---- the >=17 front leg, pc+28 to pc+1212 (the loop head).  The b.ge at
   0x4b8 is the main-loop entry test; the flags of its cmp x0,x5 (0x45c) are
   resolved by WB_PTRCMP_FLAGS and D_GT_128 rather than by the affine resolver,
   since X5 depends on nblk, which is symbolic on this leg. ---- *)
let GE17_FRONT_CLOSE_TAC =
  front_916_setup_tac THEN
  ARM_QSTEPS_TAC EXEC (1--295) THEN
  MP_TAC(SPECL [`in_p:int64`; `128`; `128 * ((nblk-1) DIV 8)`] WB_PTRCMP_FLAGS) THEN ANTS_TAC THENL
   [CONJ_TAC THEN MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN
    MP_TAC(ASSUME `17 <= nblk`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  MP_TAC(SPEC `nblk:num` D_GT_128) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ARM_QSTEPS_TAC EXEC (296--296) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ---- loop invariant: the register state at the loop head on iteration i.
   WHILE augments it with
   `e2 = APPEND (ENUMERATEL i f_ev_loop) (APPEND [] front)`. ---- *)
let loop_inv = `\(i:num) s:armstate.
     aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
     read SP s = stackpointer /\
     read X0 s = word_add in_p (word (128 * (i + 1))) /\
     read X2 s = word_add out_p (word (128 * (i + 1))) /\
     read X4 s = word_add in_p (word (16 * nblk)) /\
     read X5 s = word_add (word (128 * ((nblk - 1) DIV 8))) in_p /\
     read X9 s = word (16 * nblk) /\
     read X10 s = word_add stackpointer (word 64) /\
     read X1 s = word (128 * nblk) /\
     read X16 s = ivec_p /\
     read X6 s = htable_p /\
     read X3 s = tag_p /\
     read X11 s = key_p`;;

(* ---- the main loop, on the rest subgoal (pc+1212 to pc+4508) once the front
   leg is closed: ENSURES_EVENTS_WHILE_UP2_TAC then REPEAT CONJ_TAC leave four
   subgoals, in this order:
     G0 the count is nonzero, ~((nblk-9) DIV 8 = 0)
     G1 entry (i = 0) at pc+1212: the invariant at 0
     G2 the loop body, for all i
     G3 exit and tail, pc+2572 to pc+4508 (the residue dispatch) ---- *)
let GE17_LOOP_OPEN_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `(nblk - 9) DIV 8` `pc + 0x4bc` `pc + 0xa0c` loop_inv THEN
  REPEAT CONJ_TAC;;

(* G2, the loop body.  STRIP_EXISTS_ASSUM_TAC after ENSURES_INIT_TAC is
   required, not cosmetic: the invariant carries an accumulated
   `exists e2. read events s0 = APPEND e2 e /\ ...`, and unless it is stripped,
   `read events s0` is never exposed and the closing EXISTS_E2_TAC fails in
   AP_THM_TAC.  This mirrors what bignum_copy_row_from_table_8n.ml gets from
   ARM_SIM_TAC's ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC).  WBN_PC_BRIDGE
   already has i free, so it is MP'd rather than SPEC'd. *)
let ptrcmp_i = SPECL [`in_p:int64`; `128 * (i + 2)`; `128 * ((nblk - 1) DIV 8)`] WB_PTRCMP_FLAGS;;

let GE17_BODY_CLOSE_TAC =
  REPEAT STRIP_TAC THEN
  LEG_INIT_TAC THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_QSTEPS_TAC EXEC (1--340) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[x0norm_i]) THEN
  MP_TAC ptrcmp_i THEN ANTS_TAC THENL
   [CONJ_TAC THEN MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN
    MP_TAC(ASSUME `i < (nblk - 9) DIV 8`) THEN MP_TAC(ASSUME `17 <= nblk`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN SIMP_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pcbridge_i]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `(i + 1) + 1 = i + 2`; GSYM COND_RAND] THEN
  GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [CONJUNCT1 APPEND] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* tail setup: init, strip the accumulated e2, and simulate the part shared by
   all residues, the prepretail and the tail entry, up to the tail compare at
   pc+0xee4 *)
let GE17_TAIL_SETUP_TAC =
  LEG_INIT_TAC THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_QSTEPS_TAC EXEC (1--310) THEN                (* pc+2572 -> pc+3812 *)
  MP_TAC TAIL_LEFTOVER_BYTES THEN ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  SUBGOAL_THEN `(nblk - 9) MOD 8 < 8` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC; ALL_TAC];;

(* per-residue closer: instantiate the reusable tail theorem for rr + 1 blocks
   at s310 (MP_WB_TAIL_SAFE_TAC), consume it through
   USE_WB_COMPOSED_TAIL_SAFE_TAC, collapse the ladder to this residue's
   f_ev_t<rr>, then discharge. *)
let close_tail_residue rr =
  (* the DIVISION identity is needed: without it CONTAINED_TAC's arithmetic
     cannot show that the residue store at out_p+128*((nblk-9) DIV 8+1)+k is in
     bounds. *)
  SUBGOAL_THEN `16 * nblk = 128 * ((nblk - 9) DIV 8 + 1) + 16 * ((nblk - 9) MOD 8 + 1)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    MP_TAC(ASSUME `17 <= nblk`) THEN ARITH_TAC; ALL_TAC] THEN
  MP_WB_TAIL_SAFE_TAC (rr+1) "s310" `nblk:num`
    `word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1))):int64`
    `word_add out_p (word (128 * ((nblk - 9) DIV 8 + 1))):int64` THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; ALL; WB_MC_LEN] THEN
    REPEAT CONJ_TAC THEN
    (* Here nblk is still symbolic, so three of the eight conjuncts of the tail
       theorem's antecedent are not closed by an assumption hit.

       (a) `1 <= nblk` follows from the leg's `17 <= nblk`, so it needs an
       arithmetic closer: NBLK_ARITH_TAC, not ASM_ARITH_TAC, because the goal
       carries the many post-simulation memory assumptions, which are too much
       for the arithmetic decision procedure.  NBLK_ARITH_TAC keeps only the
       two nblk bounds and drops the rest before ARITH_TAC.

       (b) The two `contained (tail_ptr,16*(rr+1)) (base,16*nblk)` conjuncts
       need `contained` unfolded first: CONTAINED_TAC (common/components.ml)
       starts with GEN_REWRITE_TAC I [GSYM CONTAINED_MODULO_MOD2], so it
       applies only to a top-level contained_modulo and fails on a folded
       `contained`.  The DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC that
       prove_tail_safe above uses does the same REWRITE_TAC[contained] before
       its contained closer.

       As in the 9..16 chain below, MUST makes every alternative close its
       conjunct or fail.  Unlike that chain there is no NUM_REDUCE step: nblk
       is symbolic, so it would close none of these conjuncts. *)
    FIRST (map MUST
     [WB_FIRST_NONOVERLAPPING_TAC;
      REWRITE_TAC[contained] THEN CONTAINED_TAC;
      CONTAINED_TAC;
      NBLK_ARITH_TAC]);
    ALL_TAC] THEN
  USE_WB_COMPOSED_TAIL_SAFE_TAC
   (GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN
    WB_TAIL_POST_ASM_REWRITE_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[
      ASSUME (mk_eq(`(nblk - 9) MOD 8`, mk_small_numeral rr))]) THEN
    GEN_REWRITE_TAC (ONCE_DEPTH_CONV)
      [ASSUME (mk_eq(`(nblk - 9) MOD 8`, mk_small_numeral rr))] THEN
    TRY(CONV_TAC WORD_RULE) THEN
    CONV_TAC(DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC[COND_CLAUSES] THEN
    GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [CONJUNCT1 APPEND] THEN
    DISCHARGE_WB_COMPOSED_TAIL_TAC);;

(* per-band closer for nblk 9..16, after the shared symbolic front *)
let close_916_band k =
  let r = k - 8 in
  let structural_closers =
    [REWRITE_TAC[contained] THEN CONTAINED_TAC; CONTAINED_TAC;
     WB_FIRST_NONOVERLAPPING_TAC] in
  UNDISCH_TAC (mk_eq(`nblk:num`, mk_small_numeral k)) THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  (* s606 is the tail theorem's entry pc+3812, after the 296 front steps and
     the 310 prepretail and tail-entry steps: all eight precondition registers
     hold there (two steps later the ldr q9,[x0],#16 advances X0). *)
  MP_WB_TAIL_SAFE_TAC r "s606" (mk_small_numeral k)
    `word_add in_p (word 128):int64` `word_add out_p (word 128):int64` THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; ALL; WB_MC_LEN] THEN
    REPEAT CONJ_TAC THEN
    (* MUST, the fail-closed guard of the shared leaf closers, makes every
       alternative close its conjunct or fail, so one that merely rewrites (as
       NUM_REDUCE does to any conjunct with a reducible numeral) cannot shadow
       the alternatives after it; their order affects only speed.  Both
       `contained` conjuncts close under the unfold and all four
       `nonoverlapping` ones under WB_FIRST_NONOVERLAPPING_TAC.  NUM_REDUCE
       closes the two arithmetic conjuncts (`1 <= 9`, `128 * 9 < 2 EXP 64`); on
       a structural conjunct whose numerals are still unfolded
       (`nonoverlapping (out_p,16 * 9) ...`) it only normalizes the spelling,
       so the structural closers are retried after it.  TRY keeps the
       arithmetic case, where the retry has nothing left to do. *)
    FIRST (map MUST
     (structural_closers @
      [CONV_TAC NUM_REDUCE_CONV THEN
       TRY(FIRST (map MUST structural_closers))]));
    ALL_TAC] THEN
  USE_WB_COMPOSED_TAIL_SAFE_TAC
   (GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN
    WB_TAIL_POST_ASM_REWRITE_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    (* WORD_RULE would normalize any pointer arithmetic left in the goal, but
       on these bands the preceding NUM_REDUCE already leaves the event-trace
       existential, which is not a word equation, and WORD_RULE fails on it in
       RAND_CONV; hence TRY.  The 5..8 closer has no such step. *)
    TRY(CONV_TAC WORD_RULE) THEN
    DISCHARGE_WB_COMPOSED_TAIL_TAC);;

let CORE_SAFE_TAC =
  CORE_SAFE_OPEN_TAC THEN
  ASM_CASES_TAC `nblk <= 8` THENL [
    ASM_CASES_TAC `nblk <= 4` THENL [
      split_close_tac 1 4;
      FRONT_58_ENTER_TAC THENL [
        FRONT_58_CLOSE_TAC;
        WB_CASES_TAC `nblk:num` (5,8)
          (BOUNDS_ARITH_TAC [`5 <= nblk`; `nblk <= 8`]) THENL
         (map close_58_tail_band (5--8))
      ]
    ];
    ASM_CASES_TAC `nblk <= 16` THENL [
      front_916_setup_tac THEN front_916_sim_tac THEN ARM_QSTEPS_TAC EXEC (297--606) THEN
      WB_CASES_TAC `nblk:num` (9,16)
        (BOUNDS_ARITH_TAC [`9 <= nblk`; `nblk <= 16`]) THENL
       (map close_916_band (9--16));
      GE17_ENTER_TAC THENL [
        GE17_FRONT_CLOSE_TAC;
        GE17_LOOP_OPEN_TAC THENL [
          GE17_COUNT_TAC;
          GE17_ENTRY_TAC;
          GE17_BODY_CLOSE_TAC;
          GE17_TAIL_SETUP_TAC THEN
          WB_CASES_TAC `(nblk - 9) MOD 8` (0,7)
            (BOUNDS_ARITH_TAC [`(nblk - 9) MOD 8 < 8`]) THENL
           (map close_tail_residue (0--7))
        ]
      ]
    ]
  ];;

(* ---- the core safety theorem, over the real MAYCHANGE frame the wrapper
   needs.  Its memaccess bounds are the assembly's exact footprint.  The public
   theorem below takes its bounds from the C signature through mk_safety_spec:
   the tag and ivec (16), key (240) and htable (192) bounds and the 80-byte
   frame equal this footprint, while the in/out bounds are the C length
   len_bits/8 (val len_bits DIV 8 bytes), which contains the 16 * nblk footprint
   and equals it when len_bits = word (128 * nblk). ---- *)
let AES256_GCM_DEC_ALT_SAFE = prove
 (`exists f_events.
     forall e pc stackpointer in_p out_p tag_p ivec_p key_p htable_p nblk.
         1 <= nblk /\
         128 * nblk < 2 EXP 64 /\
         val in_p + 16 * nblk < 2 EXP 63 /\
         aligned 16 stackpointer /\
         ALLPAIRS nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16]
         [word pc,LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk;
          key_p,240; htable_p,192; stackpointer,80] /\
         PAIRWISE nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16] /\
         ALL (nonoverlapping (stackpointer,80))
         [word pc,LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk;
          key_p,240; htable_p,192]
         ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
                  read PC s = word (pc + 28) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS
                  [in_p; word (128 * nblk); out_p; tag_p; ivec_p; key_p; htable_p]
                  s /\
                  read events s = e)
             (\s. read PC s = word (pc + 4508) /\
                  (exists e2.
                       read events s = APPEND e2 e /\
                       e2 =
                       f_events in_p key_p htable_p out_p tag_p ivec_p nblk pc
                       stackpointer /\
                       memaccess_inbounds e2
                       [in_p,16 * nblk; tag_p,16; ivec_p,16;
                        key_p,240; htable_p,192; out_p,16 * nblk;
                        stackpointer,80]
                       [out_p,16 * nblk; tag_p,16; ivec_p,16;
                        stackpointer,80]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
              [memory :> bytes (out_p,16 * nblk); memory :> bytes (tag_p,16);
               memory :> bytes (ivec_p,16);
               memory :> bytes (word_add stackpointer (word 64),16)] ,,
              MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15])`,
  PURE_REWRITE_TAC[GSYM WB_CORE_FRAME_EQ] THEN CORE_SAFE_TAC);;

(* The wrapper's f_events gets an explicit three-path witness rather than
   CONCRETIZE_F_EVENTS_TAC and UNIFY_REFL_TAC.  The latter leave the core's
   X_CHOOSE'd f_events_callee variable in the witness, which then escapes its
   scope and makes the CHOOSE fail at extraction.

   The public witness dispatches only on the public len_bits:
   - invalid non-multiple: the three reject-path jumps;
   - zero: the cbz/return jumps;
   - valid nonzero: prologue stores/jumps, the core trace, and epilogue
     loads/return.

   f_events_core is a placeholder for the core's trace; the only part that
   cannot be written down is which variable holds it, since
   ASSUME_CALLEE_SAFETY_TAILED_TAC chooses that variable itself. *)
let wrapper_witness_template =
 `\(in_p:int64) (key_p:int64) (htable_p:int64) (out_p:int64) (tag_p:int64)
   (ivec_p:int64) (len_bits:int64) (pc:num) (sp:int64) (ra:int64).
     if val len_bits MOD 128 = 0 then
       if val len_bits = 0 then
         [EventJump (word (pc + 5904),ra);
          EventJump (word pc,word (pc + 5900))]
       else
         APPEND
           [EventJump (word (pc + 4528),ra); EventLoad (sp,16);
            EventLoad (word_add sp (word 48),16);
            EventLoad (word_add sp (word 32),16);
            EventLoad (word_add sp (word 16),16)]
           (APPEND
             (f_events_core in_p key_p htable_p out_p tag_p ivec_p
               (gcm_wb_blocks len_bits) pc sp)
             [EventStore (word_add sp (word 48),16);
              EventStore (word_add sp (word 32),16);
              EventStore (word_add sp (word 16),16); EventStore (sp,16);
              EventJump (word (pc + 8),word (pc + 12));
              EventJump (word pc,word (pc + 4))])
     else
       [EventJump (word (pc + 5904),ra);
        EventJump (word (pc + 8),word (pc + 5900));
        EventJump (word pc,word (pc + 4))]:(uarch_event)list`;;

let f_events_core_placeholder =
  find_term (fun t -> is_var t && name_of t = "f_events_core")
            wrapper_witness_template;;

(* Plug the core's chosen f_events variable into the template above.  The core
   theorem is closed, so the labelled CORE assumption has exactly one free
   variable, the chosen one; reading it off that way does not depend on the
   name ASSUME_CALLEE_SAFETY_TAC mints for it. *)
let build_wrapper_witness (asl:(string*thm)list) : term =
  match frees (concl (assoc "CORE" asl)) with
    [fev] -> subst [fev, f_events_core_placeholder] wrapper_witness_template
  | _ -> failwith "build_wrapper_witness: CORE is not a closed core theorem";;

(* An early return of the entry guard, once the path's facts are assumed:
   reduce the witness to the path's branch, simulate the n guard instructions
   to the ret, and take e2 from the witness's `e2 = ...` conjunct, so the
   template above is the only place the path's trace is written down.
   close_tac closes the instantiated goal, whose trace has no memory events. *)
let WB_GUARD_RETURN_TAC n close_tac =
  ASM_REWRITE_TAC[COND_CLAUSES;MULT_CLAUSES;ADD_CLAUSES] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    MODIFIABLE_SIMD_REGS;MODIFIABLE_GPRS;MODIFIABLE_UPPER_SIMD_REGS;
    fst EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  HINT_EXISTS_REFL_TAC THEN close_tac;;

let ARBITRARY_WRAPPER_SAFE_TAC coreth =
  ASSUME_CALLEE_SAFETY_TAILED_TAC coreth "CORE" THEN
  W(fun (asl,w) -> EXISTS_TAC (build_wrapper_witness asl)) THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES;PAIRWISE;ALLPAIRS;ALL] THEN
  REWRITE_TAC[C_ARGUMENTS;C_RETURN;SOME_FLAGS] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN BETA_TAC THEN
  ABBREV_TAC `nblk = gcm_wb_blocks len_bits` THEN
  ASM_CASES_TAC `val(len_bits:int64) MOD 128 = 0` THENL
   [ALL_TAC;
    (* Invalid non-multiple: reject before any memory access. *)
    SUBGOAL_THEN `nblk = 0` SUBST_ALL_TAC THENL
     [EXPAND_TAC "nblk" THEN REWRITE_TAC[gcm_wb_blocks] THEN
      ASM_REWRITE_TAC[COND_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(val(len_bits:int64) = 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~(val(len_bits:int64) MOD 128 = 0)` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~(val(word_and (len_bits:int64) (word 127)) = 0)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `127 = 2 EXP 7 - 1` SUBST1_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
      ASM_REWRITE_TAC[ARITH_RULE `2 EXP 7 = 128`];
      ALL_TAC] THEN
    WB_GUARD_RETURN_TAC 5
      (REWRITE_TAC[APPEND;memaccess_inbounds;ALL;EX;FST;SND])] THEN
  ASM_CASES_TAC `val(len_bits:int64) = 0` THENL
   [(* Zero: cbz returns before the stack saves. *)
    SUBGOAL_THEN `nblk = 0` SUBST_ALL_TAC THENL
     [EXPAND_TAC "nblk" THEN REWRITE_TAC[gcm_wb_blocks] THEN
      ASM_REWRITE_TAC[COND_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `len_bits:int64 = word 0` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[GSYM VAL_EQ_0];
      ALL_TAC] THEN
    WB_GUARD_RETURN_TAC 3
      (REWRITE_TAC[APPEND;VAL_WORD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
       REWRITE_TAC[memaccess_inbounds;ALL;EX;FST;SND]);
    ALL_TAC] THEN
  (* Valid nonzero: recover word (128*nblk), then use the valid-only core
     safety theorem inside the existing wrapper simulation. *)
  SUBGOAL_THEN `1 <= nblk` ASSUME_TAC THENL
   [EXPAND_TAC "nblk" THEN REWRITE_TAC[gcm_wb_blocks] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`val(len_bits:int64)`; `128`]
      (CONJUNCT2 DIVISION_SIMP)) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(len_bits:int64) = 128 * nblk` ASSUME_TAC THENL
   [EXPAND_TAC "nblk" THEN ASM_SIMP_TAC[GCM_WB_BLOCKS_VALID];
    ALL_TAC] THEN
  SUBGOAL_THEN `128 * nblk < 2 EXP 64` ASSUME_TAC THENL
   [MP_TAC(ISPEC `len_bits:int64` VAL_BOUND_64) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `len_bits:int64 = word (128 * nblk)` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if concl th = `val(len_bits:int64) = 128 * nblk`
      then MP_TAC th else failwith "") THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[COND_CLAUSES] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;MODIFIABLE_SIMD_REGS;
    MODIFIABLE_GPRS;MODIFIABLE_UPPER_SIMD_REGS;fst EXEC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun c -> ENSURES_PRESERVED_DREG_TAC ("init_"^fst(dest_const c)) c)
    [`D8`;`D9`;`D10`;`D11`;`D12`;`D13`;`D14`;`D15`] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
  WB_GUARD_FALLTHROUGH_TAC THEN ARM_STEPS_TAC EXEC (1--7) THEN
  W(fun (asl,w) ->
     let pd =
       subst [`[]:(uarch_event)list`,`e:(uarch_event)list`]
         (events_of_state asl `s7:armstate`) in
     USE_THEN "CORE" (fun cth -> MP_TAC (SPECL
       [`e:(uarch_event)list`;`pc:num`;
        `word_sub stackpointer (word 80):int64`;
        `in_p:int64`;`out_p:int64`;`tag_p:int64`;`ivec_p:int64`;
        `key_p:int64`;`htable_p:int64`;`nblk:num`;pd] cth))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES;PAIRWISE;ALLPAIRS;ALL] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC ALIGNED_WORD_SUB THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[aligned;WORD_VAL] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_DIVIDES_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;MODIFIABLE_SIMD_REGS;
    MODIFIABLE_GPRS;MODIFIABLE_UPPER_SIMD_REGS;fst EXEC] THEN
  ARM_BIGSTEP_TAC EXEC "s8" THENL
   [REWRITE_TAC[C_ARGUMENTS;APPEND] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ARM_STEPS_TAC EXEC (9--14) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [HINT_EXISTS_REFL_TAC THEN
    REWRITE_TAC[GSYM APPEND_ASSOC;APPEND] THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC;
    REWRITE_TAC
     [WORD_BLAST`(word_zx:int128->int64)(word_zx(x:int64))=x`] THEN
    CONV_TAC WORD_RULE];;

let noibt_full_spec,_ = mk_safety_spec
    ~keep_maychanges:true
    (assoc "aes256_gcm_dec_alt" subroutine_signatures)
    AES256_GCM_DEC_ALT_NOIBT_SUBROUTINE_CORRECT
    AES256_GCM_DEC_ALT_EXEC;;

(* The statement of the exported safety theorem, for an arbitrary len_bits,
   first for the trimmed code.  The theorem below is proved as the
   noibt_full_spec that mk_safety_spec generates above from
   AES256_GCM_DEC_ALT_NOIBT_SUBROUTINE_CORRECT and the C signature, and the
   load fails unless that term is exactly the one written here:
   - the correctness theorem's hypotheses: the signed pointer bound, the stack
     alignment and the nonoverlapping lists;
   - access bounds sized by the C objects: in/out len_bits/8, tag 16, ivec 16,
     key 240, htable 24 * 8 = 192, and the 80-byte frame;
   - by keep_maychanges, the correctness theorem's MAYCHANGE frame, based on
     gcm_wb_blocks.
   Apart from the loaded code it constrains no memory contents (no key
   schedule, table, tag, counter or data precondition), so it holds for every
   content.
   This routine does not enforce the NIST GCM message limit. Callers must
   ensure the cumulative message length does not exceed 2^36 - 32 bytes
   (2^39 - 256 bits). *)
let AES256_GCM_DEC_ALT_NOIBT_SUBROUTINE_SAFE = prove
 (`exists f_events.
     forall e pc stackpointer in_p len_bits out_p tag_p ivec_p key_p htable_p
            returnaddress.
         val in_p + 16 * gcm_wb_blocks len_bits < 2 EXP 63 /\
         aligned 16 stackpointer /\
         ALLPAIRS nonoverlapping
         [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16]
         [word pc,LENGTH aes256_gcm_dec_alt_tmc;
          in_p,16 * gcm_wb_blocks len_bits; key_p,240; htable_p,192;
          word_sub stackpointer (word 80),80] /\
         PAIRWISE nonoverlapping
         [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16] /\
         ALL (nonoverlapping (word_sub stackpointer (word 80),80))
         [word pc,LENGTH aes256_gcm_dec_alt_tmc;
          in_p,16 * gcm_wb_blocks len_bits; key_p,240; htable_p,192]
         ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    aes256_gcm_dec_alt_tmc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS
                  [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                       read events s = APPEND e2 e /\
                       e2 =
                       f_events in_p key_p htable_p out_p tag_p ivec_p len_bits pc
                         (word_sub stackpointer (word 80)) returnaddress /\
                       memaccess_inbounds e2
                       [in_p,val len_bits DIV 8 * 1; tag_p,16; ivec_p,16;
                        key_p,240; htable_p,192; out_p,val len_bits DIV 8 * 1;
                        word_sub stackpointer (word 80),80]
                       [out_p,val len_bits DIV 8 * 1; tag_p,16; ivec_p,16;
                        word_sub stackpointer (word 80),80]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
              [memory :> bytes (out_p,16 * gcm_wb_blocks len_bits);
               memory :> bytes (tag_p,16);
               memory :> bytes (ivec_p,16);
               memory :> bytes (word_sub stackpointer (word 80),80)])`,
  ASSERT_CONCL_TAC noibt_full_spec THEN
  ARBITRARY_WRAPPER_SAFE_TAC
   (PURE_REWRITE_RULE[GSYM WB_CORE_FRAME_EQ] AES256_GCM_DEC_ALT_SAFE));;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "aes256_gcm_dec_alt" subroutine_signatures)
    AES256_GCM_DEC_ALT_SUBROUTINE_CORRECT
    AES256_GCM_DEC_ALT_EXEC;;

(* The same for the full code, with its BTI landing pad: the full_spec that
   mk_safety_spec generates from AES256_GCM_DEC_ALT_SUBROUTINE_CORRECT. *)

let AES256_GCM_DEC_ALT_SUBROUTINE_SAFE = prove
 (`exists f_events.
     forall e pc stackpointer in_p len_bits out_p tag_p ivec_p key_p htable_p
            returnaddress.
         val in_p + 16 * gcm_wb_blocks len_bits < 2 EXP 63 /\
         aligned 16 stackpointer /\
         ALLPAIRS nonoverlapping
         [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16]
         [word pc,LENGTH aes256_gcm_dec_alt_mc;
          in_p,16 * gcm_wb_blocks len_bits; key_p,240; htable_p,192;
          word_sub stackpointer (word 80),80] /\
         PAIRWISE nonoverlapping
         [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16] /\
         ALL (nonoverlapping (word_sub stackpointer (word 80),80))
         [word pc,LENGTH aes256_gcm_dec_alt_mc;
          in_p,16 * gcm_wb_blocks len_bits; key_p,240; htable_p,192]
         ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    aes256_gcm_dec_alt_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS
                  [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                       read events s = APPEND e2 e /\
                       e2 =
                       f_events in_p key_p htable_p out_p tag_p ivec_p len_bits pc
                         (word_sub stackpointer (word 80)) returnaddress /\
                       memaccess_inbounds e2
                       [in_p,val len_bits DIV 8 * 1; tag_p,16; ivec_p,16;
                        key_p,240; htable_p,192; out_p,val len_bits DIV 8 * 1;
                        word_sub stackpointer (word 80),80]
                       [out_p,val len_bits DIV 8 * 1; tag_p,16; ivec_p,16;
                        word_sub stackpointer (word 80),80]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
              [memory :> bytes (out_p,16 * gcm_wb_blocks len_bits);
               memory :> bytes (tag_p,16);
               memory :> bytes (ivec_p,16);
               memory :> bytes (word_sub stackpointer (word 80),80)])`,
  ASSERT_CONCL_TAC full_spec THEN
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    aes256_gcm_dec_alt_mc aes256_gcm_dec_alt_tmc
    AES256_GCM_DEC_ALT_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* No-access early-return guarantee.                                         *)
(*                                                                           *)
(* The exported CORRECT and SAFE theorems still carry the key, table, tag,   *)
(* counter, stack and separation premises on a rejected call.  These two     *)
(* theorems state what holds there without any of them: when len_bits is     *)
(* zero or not a whole number of 128-bit blocks, the routine returns 0 with  *)
(* no memory access (see ALT_GUARD_REJECT_TAC in aes_gcm_common.ml).  They   *)
(* are not named *_SUBROUTINE_CORRECT/_SAFE, so tools/count-proofs.sh does   *)
(* not count them and arm/proofs/specifications.txt does not list them.      *)
(* The padded form follows from the trimmed one by ARM_ADD_IBT_RULE, and     *)
(* needs no ~extra, as the precondition has no opaque state predicate.       *)
(* ------------------------------------------------------------------------- *)

let AES256_GCM_DEC_ALT_NOIBT_REJECT_NOACCESS = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p len_bits pc returnaddress e.
    val len_bits = 0 \/ ~(val len_bits MOD 128 = 0)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
           read PC s = word pc /\
           read X30 s = returnaddress /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read events s = e)
      (\s. read PC s = returnaddress /\
           C_RETURN s = word 0 /\
           (?e2. read events s = APPEND e2 e /\ memaccess_inbounds e2 [] []))
      (MAYCHANGE [PC; X0] ,, MAYCHANGE [events] ,, MAYCHANGE SOME_FLAGS)`,
  ALT_GUARD_REJECT_TAC AES256_GCM_DEC_ALT_EXEC);;

let AES256_GCM_DEC_ALT_REJECT_NOACCESS = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p len_bits pc returnaddress e.
    val len_bits = 0 \/ ~(val len_bits MOD 128 = 0)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_mc /\
           read PC s = word pc /\
           read X30 s = returnaddress /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read events s = e)
      (\s. read PC s = returnaddress /\
           C_RETURN s = word 0 /\
           (?e2. read events s = APPEND e2 e /\ memaccess_inbounds e2 [] []))
      (MAYCHANGE [PC; X0] ,, MAYCHANGE [events] ,, MAYCHANGE SOME_FLAGS)`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
                     aes256_gcm_dec_alt_mc aes256_gcm_dec_alt_tmc
                     AES256_GCM_DEC_ALT_NOIBT_REJECT_NOACCESS));;
