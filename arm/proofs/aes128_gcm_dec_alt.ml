(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-128-GCM decryption of whole blocks, 8 blocks at a time: the 8-way     *)
(* kernel aes128_gcm_dec_alt.                                                *)
(*                                                                           *)
(* Contract (AES128_GCM_DEC_ALT_SUBROUTINE_CORRECT).  The kernel processes   *)
(* nblk = gcm_wb_blocks len_bits whole 16-byte blocks (none when len_bits is *)
(* not a multiple of 128) and returns 16 * nblk.  Given the FIPS-197 key     *)
(* schedule rk at key_p, the key table htable_mem_8 at htable_p for the      *)
(* GHASH key                                                                 *)
(*   H = aes128_cipher (word 0) rk                                           *)
(* and the counter block ctr_block nonce c at ivec_p, output block j is      *)
(* input block j XOR aes_ctr_block aes128_cipher c nonce rk j, the tag at    *)
(* tag_p becomes nist_ghash H over the input (ciphertext) blocks, continued  *)
(* from the old tag, and ivec_p advances to ctr_block nonce (nblk + c); the  *)
(* tag and the counter block are stored byte-reversed.  The buffers must be  *)
(* disjoint, and val in_p + 16 * nblk < 2 EXP 63 since the kernel compares   *)
(* pointers with signed conditions.  AES128_GCM_DEC_ALT_SUBROUTINE_SAFE is   *)
(* the matching constant-time and memory-safety theorem.                     *)
(*                                                                           *)
(* The code begins with a bti c landing pad.  The proofs are about the code  *)
(* without it, the code of a -DNO_IBT build, so every offset in this file    *)
(* (pc + 0x1c, 0x3b4, ...) is one of that code; the theorems for the full    *)
(* code follow by ARM_ADD_IBT_RULE.                                          *)
(*                                                                           *)
(* Proof structure.  The kernel is the AES-128 counterpart of                *)
(* aes256_gcm_dec_alt, and this proof has the structure of the AES-256 one   *)
(* (arm/proofs/aes256_gcm_dec_alt.ml), with the ten-round keystream tower    *)
(* aes9, the eleven round keys and the AES-128 instruction schedule.  The    *)
(* entry guard (0x0..0x8) returns 0 for an empty or invalid len_bits, and    *)
(* the prologue (0xc..0x18) saves d8-d15.  The core runs from pc + 0x1c to   *)
(* its exit pc + 3708 (0xe7c, L128_dec_frame_restore); its theorem is the    *)
(* spine WBN_DEC_CORE_BYTELIST, which splits on nblk:                        *)
(* - nblk <= 8, the <=8-block chain (AES128_GCM_DEC_ALT_DISPATCH): for       *)
(*   nblk <= 4 the b.le at 0x38 enters the small-input path L128_dec_small   *)
(*   (WB_FUSED_1BLOCK .. WB_FUSED_4BLOCK); for 5..8 the shared front         *)
(*   (WB_FRONT_BUF) takes the b.ge at 0x340, and the tail runs from the seam *)
(*   pc + 3032 (0xbd8) through the block cascade, or the exact-8 drain for   *)
(*   nblk = 8 (WB_TAIL_GEN2_k);                                              *)
(* - 9 <= nblk <= 16: the front falls through at 0x340 and takes the b.ge at *)
(*   0x3b0 to the prepretail at 0x7fc, skipping the main loop                *)
(*   (WBN_FRONT_TO_END_916);                                                 *)
(* - nblk >= 17: the front reaches the loop head 0x3b4, the main loop        *)
(*   L128_dec_main_loop (0x3b4..0x7f8, 8 blocks per iteration, run           *)
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
(* arm/proofs/utils/aes_gcm_dec_alt_common.ml, shared with the AES-256       *)
(* proof.  This file holds, in order: the AES-128 vocabulary (aes9,          *)
(* aes128_encrypt, the CTR output specification gcm_dec128_pt_bytes); the    *)
(* machine code; the <=8-block chain (shared front, band tails, small-input  *)
(* path, readable band and dispatch theorems); the export lemmas; the nblk > *)
(* 8 proof (front, main loop, prepretail, recomposition); the spines and the *)
(* exported theorems; the constant-time and memory-safety proof; the         *)
(* no-access theorems for rejected lengths.                                  *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/aes_gcm_dec_alt_common.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(* ========================================================================= *)
(* The AES-128 vocabulary.                                                   *)
(*                                                                           *)
(* aes256_gcm_dec_alt.ml states its keystream with the house aes256_encrypt  *)
(* (aes_encrypt_spec.ml) and its CTR output with its own aes_ctr and         *)
(* gcm_dec_pt_bytes.  These are the AES-128 counterparts, so that this proof *)
(* can be built the same way:                                                *)
(* - aes9, the kernel's in-flight keystream tower (nine aese/aesmc rounds    *)
(*   and the final aese, before the last round key is XORed in), and its     *)
(*   reconstruct lemma AES128_XOR_ENCRYPT_RECONSTRUCT;                       *)
(* - aes128_encrypt, AES-128 in lane order (the byte order of a bytes128     *)
(*   read), defined from the FIPS-197 aes128_cipher so that the bridge to    *)
(*   the shared aes_ctr_block aes128_cipher is definitional;                 *)
(* - the CTR and byte-list vocabulary aes128_ctr, aes128_ctr_bytes and       *)
(*   gcm_dec128_pt_bytes, with their LENGTH/EL lemmas and the per-N unfolds; *)
(*   the cipher-free gcm_dec_blocks_from, gcm_dec_ghash_blocks and           *)
(*   gcm_dec_final_xi are those of aes_gcm_dec_alt_common.ml;                *)
(* - the 11-slot key reads RK_ETA_11 and KEY_READS_FROM_WORDLIST.            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The keystream tower and AES-128 in lane order.                            *)
(* ------------------------------------------------------------------------- *)

(* The kernel's in-flight keystream tower: rounds 0..8 (aese then aesmc) and *)
(* the final aese with k9.  The last round key k10 is XORed in later,        *)
(* together with the ciphertext, by one eor3 per block, so naming this       *)
(* partial tower keeps the register contracts between the front, the loop   *)
(* and the tail at one application per block.                                *)
let aes9 = new_definition
 `aes9 (p:int128) (k0:int128) (k1:int128) (k2:int128) (k3:int128)
       (k4:int128) (k5:int128) (k6:int128) (k7:int128) (k8:int128)
       (k9:int128) : int128 =
    aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese
      (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese p k0)) k1)) k2))
      k3)) k4)) k5)) k6)) k7)) k8)) k9`;;

(* AES-128 on lane-order blocks and round keys: the block and the keys are   *)
(* byte-reversed into the FIPS-197 order, enciphered, and the result is      *)
(* byte-reversed back.  This is the AES-128 counterpart of the house         *)
(* aes256_encrypt the AES-256 proof is stated with.                          *)
let aes128_encrypt = new_definition
 `aes128_encrypt (block:int128) (keys:int128 list) : int128 =
    word_reversefields 8
      (aes128_cipher (word_reversefields 8 block)
                     (MAP (word_reversefields 8) keys))`;;

(* The plaintext capture: tower XOR (k10 XOR ciphertext) is the ciphertext   *)
(* XOR the keystream (XOR_AES128_CIPHER_RECONSTRUCT, aes_gcm_common.ml).     *)
let AES128_XOR_ENCRYPT_RECONSTRUCT = prove
 (`!ctr cph k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10:int128.
    word_xor (aes9 ctr k0 k1 k2 k3 k4 k5 k6 k7 k8 k9) (word_xor k10 cph) =
    word_xor cph (aes128_encrypt ctr [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10])`,
  REWRITE_TAC[aes9; XOR_AES128_CIPHER_RECONSTRUCT; aes128_encrypt] THEN
  MATCH_ACCEPT_TAC WORD_XOR_SYM);;

(* Over the memory image MAP (word_reversefields 8) rk of a FIPS-197 key     *)
(* schedule rk, aes128_encrypt is the FIPS-197 cipher in lane order.         *)
let AES128_ENCRYPT_AS_CIPHER = prove
 (`!x (rk:int128 list).
     aes128_encrypt x (MAP (word_reversefields 8) rk) =
     word_reversefields 8 (aes128_cipher (word_reversefields 8 x) rk)`,
  REWRITE_TAC[aes128_encrypt; GSYM MAP_o; o_DEF;
              WORD_REVERSEFIELDS_REVERSEFIELDS; MAP_ID]);;

(* Block j's keystream, as WBN_OUTPUT_POINTWISE_NONCE states it at the       *)
(* exported instantiation, is the shared aes_ctr_block.                      *)
let AES128_ENCRYPT_CTR_AS_AES_CTR_BLOCK = prove
 (`!(nonce:96 word) c j (rk:int128 list).
     aes128_encrypt (word_bytereverse (ctr_block nonce (c + j)))
                    (MAP (word_reversefields 8) rk) =
     aes_ctr_block aes128_cipher c nonce rk j`,
  REWRITE_TAC[AES128_ENCRYPT_AS_CIPHER] THEN
  REWRITE_TAC[aes_ctr_block; BREV_RF8_128; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[ADD_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Counter mode over an int128 block list, and its byte-list view (the       *)
(* AES-128 counterparts of the output specification of                       *)
(* aes256_gcm_dec_alt.ml).                                                   *)
(* ------------------------------------------------------------------------- *)

(* One output block: the block XOR the keystream for block index k.          *)
let aes128_ctr_output_block = new_definition
 `aes128_ctr_output_block (ctr0:int128) (k:num) (pt:int128)
                          (keys:int128 list) : int128 =
    word_xor pt (aes128_encrypt (gcm_ctr_inc_iter k ctr0) keys)`;;

(* Counter mode over a block list; position i uses counter                   *)
(* gcm_ctr_inc_iter (k+i) ctr0, where k is the starting block index.         *)
let aes128_ctr_rec = define
 `aes128_ctr_rec (ctr0:int128) (k:num) ([]:int128 list) (keys:int128 list) =
    [] /\
  aes128_ctr_rec (ctr0:int128) (k:num) (CONS pt pts) (keys:int128 list) =
    CONS (aes128_ctr_output_block ctr0 k pt keys)
         (aes128_ctr_rec ctr0 (k+1) pts keys)`;;

let aes128_ctr = new_definition
 `aes128_ctr (ctr0:int128) (pts:int128 list) (keys:int128 list)
    : int128 list =
    aes128_ctr_rec ctr0 0 pts keys`;;

let LENGTH_AES128_CTR_REC = prove
 (`!pts ctr0 k keys. LENGTH(aes128_ctr_rec ctr0 k pts keys) = LENGTH pts`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[aes128_ctr_rec; LENGTH]);;

let LENGTH_AES128_CTR = prove
 (`!pts ctr0 keys. LENGTH(aes128_ctr ctr0 pts keys) = LENGTH pts`,
  REWRITE_TAC[aes128_ctr; LENGTH_AES128_CTR_REC]);;

let EL_AES128_CTR_REC = prove
 (`!pts ctr0 k keys i.
     i < LENGTH pts
     ==> EL i (aes128_ctr_rec ctr0 k pts keys) =
         aes128_ctr_output_block ctr0 (k+i) (EL i pts) keys`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; aes128_ctr_rec; LT] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  ASM_REWRITE_TAC[EL; HD; TL; ADD_CLAUSES; LT_SUC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < LENGTH(t:int128 list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`ctr0:int128`;`k+1`;`keys:int128 list`;`n:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `(k+1)+n = SUC(k+n)`]);;

(* Element i in the explicit word_xor / aes128_encrypt form.                 *)
let EL_AES128_CTR = prove
 (`!pts ctr0 keys i.
     i < LENGTH pts
     ==> EL i (aes128_ctr ctr0 pts keys) =
         word_xor (EL i pts) (aes128_encrypt (gcm_ctr_inc_iter i ctr0) keys)`,
  REWRITE_TAC[aes128_ctr] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_AES128_CTR_REC; aes128_ctr_output_block; ADD_CLAUSES]);;

(* The output as a byte list (int128_list_to_bytes above).                  *)
let aes128_ctr_bytes = new_definition
 `aes128_ctr_bytes (ctr0:int128) (pts:int128 list) (keys:int128 list)
    : byte list =
    int128_list_to_bytes (aes128_ctr ctr0 pts keys)`;;

(* The decrypted bytes of the len DIV 16 whole blocks of the input x.        *)
let gcm_dec128_pt_bytes = new_definition
 `gcm_dec128_pt_bytes (len:num) (x:byte list) (ctr0:int128)
                      (keys:int128 list) : byte list =
    aes128_ctr_bytes ctr0 (gcm_dec_blocks_from 0 (len DIV 16) x) keys`;;

(* gcm_dec128_pt_bytes at len = 16 * N, N = 1..8, over the explicit N-block  *)
(* list (as GCM_DEC_GHASH_BLOCKS_WHOLE_N above for the GHASH input).         *)
let build_pt128_bytes_whole n =
  prove(list_mk_forall([`x:byte list`; `ctr0:int128`; `keys:int128 list`],
          mk_eq(list_mk_comb(`gcm_dec128_pt_bytes`,
                  [mk_small_numeral (16 * n); `x:byte list`; `ctr0:int128`;
                   `keys:int128 list`]),
                list_mk_comb(`aes128_ctr_bytes`,
                  [`ctr0:int128`; gcm_dec_whole_blocks_tm n;
                   `keys:int128 list`]))),
        REPEAT GEN_TAC THEN REWRITE_TAC[gcm_dec128_pt_bytes] THEN
        GCM_DEC_BLOCKS_FROM_UNFOLD_TAC n);;

let GCM_DEC128_PT_BYTES_WHOLE_1 = build_pt128_bytes_whole 1;;
let GCM_DEC128_PT_BYTES_WHOLE_2 = build_pt128_bytes_whole 2;;
let GCM_DEC128_PT_BYTES_WHOLE_3 = build_pt128_bytes_whole 3;;
let GCM_DEC128_PT_BYTES_WHOLE_4 = build_pt128_bytes_whole 4;;
let GCM_DEC128_PT_BYTES_WHOLE_5 = build_pt128_bytes_whole 5;;
let GCM_DEC128_PT_BYTES_WHOLE_6 = build_pt128_bytes_whole 6;;
let GCM_DEC128_PT_BYTES_WHOLE_7 = build_pt128_bytes_whole 7;;
let GCM_DEC128_PT_BYTES_WHOLE_8 = build_pt128_bytes_whole 8;;

(* ------------------------------------------------------------------------- *)
(* Key condensation: the round-key list and its 11 bytes128 reads.           *)
(* ------------------------------------------------------------------------- *)

let RK_ETA_11 = prove
 (`!rk:int128 list. LENGTH rk = 11
     ==> rk = [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
               EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]`,
  GEN_TAC THEN REWRITE_TAC[LENGTH_EQ_LIST_OF_SEQ] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  REWRITE_TAC(map num_CONV (map mk_small_numeral (rev(1--11)))) THEN
  REWRITE_TAC[LIST_OF_SEQ; o_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let KEY_READS_FROM_WORDLIST = prove
 (`!(key_p:int64) (rk:int128 list) s.
     wordlist_from_memory (key_p,11) s = rk
     ==> read (memory :> bytes128 key_p) s = EL 0 rk /\
         read (memory :> bytes128 (word_add key_p (word 16))) s = EL 1 rk /\
         read (memory :> bytes128 (word_add key_p (word 32))) s = EL 2 rk /\
         read (memory :> bytes128 (word_add key_p (word 48))) s = EL 3 rk /\
         read (memory :> bytes128 (word_add key_p (word 64))) s = EL 4 rk /\
         read (memory :> bytes128 (word_add key_p (word 80))) s = EL 5 rk /\
         read (memory :> bytes128 (word_add key_p (word 96))) s = EL 6 rk /\
         read (memory :> bytes128 (word_add key_p (word 112))) s = EL 7 rk /\
         read (memory :> bytes128 (word_add key_p (word 128))) s = EL 8 rk /\
         read (memory :> bytes128 (word_add key_p (word 144))) s = EL 9 rk /\
         read (memory :> bytes128 (word_add key_p (word 160))) s = EL 10 rk`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC(map num_CONV (map mk_small_numeral (rev(1--10)))) THEN
  REWRITE_TAC[EL; HD; TL]);;

(* ------------------------------------------------------------------------- *)
(* Machine code (print_literal_from_elf "arm/aes_gcm/aes128_gcm_dec_alt.o")  *)
(* ------------------------------------------------------------------------- *)

let aes128_gcm_dec_alt_mc = define_assert_from_elf "aes128_gcm_dec_alt_mc"
  "arm/aes_gcm/aes128_gcm_dec_alt.o"
[
  0xd503245f;       (* arm_BTI *)
  0xb40074a1;       (* arm_CBZ X1 (word 3732) *)
  0xf240183f;       (* arm_TST X1 (rvalue (word 127)) *)
  0x54007461;       (* arm_BNE (word 3724) *)
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
  0x54007ecd;       (* arm_BLE (word 4056) *)
  0xaa0903e5;       (* arm_MOV X5 X9 *)
  0x4c407200;       (* arm_LDR Q0 X16 No_Offset *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0xd10004a5;       (* arm_SUB X5 X5 (rvalue (word 1)) *)
  0xd2c0002f;       (* arm_MOVZ X15 (word 1) 32 *)
  0x4f00e41f;       (* arm_MOVI Q31 (word 0) *)
  0x4e181dff;       (* arm_INS_GEN Q31 X15 64 64 *)
  0x4ebf87e8;       (* arm_ADD_VEC Q8 Q31 Q31 32 128 *)
  0x4ebf8509;       (* arm_ADD_VEC Q9 Q8 Q31 32 128 *)
  0x4ea8850a;       (* arm_ADD_VEC Q10 Q8 Q8 32 128 *)
  0x4ebf854b;       (* arm_ADD_VEC Q11 Q10 Q31 32 128 *)
  0x4ea8854c;       (* arm_ADD_VEC Q12 Q10 Q8 32 128 *)
  0x4ea9854d;       (* arm_ADD_VEC Q13 Q10 Q9 32 128 *)
  0x4c407073;       (* arm_LDR Q19 X3 No_Offset *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0x6e20080e;       (* arm_REV32_VEC Q14 Q0 8 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ebf85cf;       (* arm_ADD_VEC Q15 Q14 Q31 32 128 *)
  0x4ea885d0;       (* arm_ADD_VEC Q16 Q14 Q8 32 128 *)
  0x4ea985d1;       (* arm_ADD_VEC Q17 Q14 Q9 32 128 *)
  0x4eaa85d2;       (* arm_ADD_VEC Q18 Q14 Q10 32 128 *)
  0x4eab85d4;       (* arm_ADD_VEC Q20 Q14 Q11 32 128 *)
  0x4eac85d5;       (* arm_ADD_VEC Q21 Q14 Q12 32 128 *)
  0x4ead85de;       (* arm_ADD_VEC Q30 Q14 Q13 32 128 *)
  0x6e2009e1;       (* arm_REV32_VEC Q1 Q15 8 *)
  0x6e200a02;       (* arm_REV32_VEC Q2 Q16 8 *)
  0x6e200a23;       (* arm_REV32_VEC Q3 Q17 8 *)
  0x6e200a44;       (* arm_REV32_VEC Q4 Q18 8 *)
  0x6e200a85;       (* arm_REV32_VEC Q5 Q20 8 *)
  0x6e200aa6;       (* arm_REV32_VEC Q6 Q21 8 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 *)
  0x9279e0a5;       (* arm_AND X5 X5 (rvalue (word 18446744073709551488)) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x8b0000a5;       (* arm_ADD X5 X5 X0 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x3dc0297b;       (* arm_LDR Q27 X11 (Immediate_Offset (word 160)) *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x8b410c04;       (* arm_ADD X4 X0 (Shiftedreg X1 LSR 3) *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0x5400442a;       (* arm_BGE (word 2180) *)
  0xacc12408;       (* arm_LDP Q8 Q9 X0 (Postimmediate_Offset (iword (&32))) *)
  0xce006d00;       (* arm_EOR3 Q0 Q8 Q0 Q27 *)
  0xce016d21;       (* arm_EOR3 Q1 Q9 Q1 Q27 *)
  0xac810440;       (* arm_STP Q0 Q1 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc0;       (* arm_REV32_VEC Q0 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xacc12c0a;       (* arm_LDP Q10 Q11 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc1340c;       (* arm_LDP Q12 Q13 X0 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc1;       (* arm_REV32_VEC Q1 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xacc13c0e;       (* arm_LDP Q14 Q15 X0 (Postimmediate_Offset (iword (&32))) *)
  0xce036d63;       (* arm_EOR3 Q3 Q11 Q3 Q27 *)
  0xce026d42;       (* arm_EOR3 Q2 Q10 Q2 Q27 *)
  0xac810c42;       (* arm_STP Q2 Q3 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc2;       (* arm_REV32_VEC Q2 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce066dc6;       (* arm_EOR3 Q6 Q14 Q6 Q27 *)
  0x6e200bc3;       (* arm_REV32_VEC Q3 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce046d84;       (* arm_EOR3 Q4 Q12 Q4 Q27 *)
  0xce056da5;       (* arm_EOR3 Q5 Q13 Q5 Q27 *)
  0xac811444;       (* arm_STP Q4 Q5 X2 (Postimmediate_Offset (iword (&32))) *)
  0xce076de7;       (* arm_EOR3 Q7 Q15 Q7 Q27 *)
  0xac811c46;       (* arm_STP Q6 Q7 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x5400226a;       (* arm_BGE (word 1100) *)
  0x3dc024d7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 144)) *)
  0x3dc02cd9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 176)) *)
  0x4e200929;       (* arm_REV64_VEC Q9 Q9 8 *)
  0x4e200908;       (* arm_REV64_VEC Q8 Q8 8 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e2009ce;       (* arm_REV64_VEC Q14 Q14 8 *)
  0x3dc018d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 96)) *)
  0x3dc020d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 128)) *)
  0x6e331d08;       (* arm_EOR_VEC Q8 Q8 Q19 128 *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e20094a;       (* arm_REV64_VEC Q10 Q10 8 *)
  0x4e20098c;       (* arm_REV64_VEC Q12 Q12 8 *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x3dc01cd5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 112)) *)
  0x3dc028d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 160)) *)
  0x4ef7e130;       (* arm_PMULL2_VEC Q16 Q9 Q23 64 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 *)
  0x4ec82932;       (* arm_TRN1 Q18 Q9 Q8 64 128 *)
  0x4e2009ad;       (* arm_REV64_VEC Q13 Q13 8 *)
  0x0ef7e137;       (* arm_PMULL_VEC Q23 Q9 Q23 64 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x4ec86928;       (* arm_TRN2 Q8 Q9 Q8 64 128 *)
  0x4ef6e15d;       (* arm_PMULL2_VEC Q29 Q10 Q22 64 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ef4e169;       (* arm_PMULL2_VEC Q9 Q11 Q20 64 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e301e31;       (* arm_EOR_VEC Q17 Q17 Q16 128 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x6e321d08;       (* arm_EOR_VEC Q8 Q8 Q18 128 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0xce1d2631;       (* arm_EOR3 Q17 Q17 Q29 Q9 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4eca297d;       (* arm_TRN1 Q29 Q11 Q10 64 128 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x0ef6e156;       (* arm_PMULL_VEC Q22 Q10 Q22 64 *)
  0x4eca696a;       (* arm_TRN2 Q10 Q11 Q10 64 128 *)
  0x4ef8e112;       (* arm_PMULL2_VEC Q18 Q8 Q24 64 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x0ef8e118;       (* arm_PMULL_VEC Q24 Q8 Q24 64 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x0ef4e174;       (* arm_PMULL_VEC Q20 Q11 Q20 64 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e3d1d4a;       (* arm_EOR_VEC Q10 Q10 Q29 128 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x6e381e52;       (* arm_EOR_VEC Q18 Q18 Q24 128 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4ecc29b0;       (* arm_TRN1 Q16 Q13 Q12 64 128 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ef5e15d;       (* arm_PMULL2_VEC Q29 Q10 Q21 64 *)
  0x0ef5e155;       (* arm_PMULL_VEC Q21 Q10 Q21 64 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e2009ef;       (* arm_REV64_VEC Q15 Q15 8 *)
  0x4ef9e188;       (* arm_PMULL2_VEC Q8 Q12 Q25 64 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x0ef9e199;       (* arm_PMULL_VEC Q25 Q12 Q25 64 *)
  0xce157652;       (* arm_EOR3 Q18 Q18 Q21 Q29 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4ecc69ac;       (* arm_TRN2 Q12 Q13 Q12 64 128 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ef7e1aa;       (* arm_PMULL2_VEC Q10 Q13 Q23 64 *)
  0x0ef7e1b7;       (* arm_PMULL_VEC Q23 Q13 Q23 64 *)
  0x4ef6e1cb;       (* arm_PMULL2_VEC Q11 Q14 Q22 64 *)
  0x0ef6e1d6;       (* arm_PMULL_VEC Q22 Q14 Q22 64 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x6e301d8c;       (* arm_EOR_VEC Q12 Q12 Q16 128 *)
  0x4ece29ed;       (* arm_TRN1 Q13 Q15 Q14 64 128 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ece69ee;       (* arm_TRN2 Q14 Q15 Q14 64 128 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ef8e190;       (* arm_PMULL2_VEC Q16 Q12 Q24 64 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e2d1dce;       (* arm_EOR_VEC Q14 Q14 Q13 128 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x0ef8e198;       (* arm_PMULL_VEC Q24 Q12 Q24 64 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ef4e1ec;       (* arm_PMULL2_VEC Q12 Q15 Q20 64 *)
  0xce184252;       (* arm_EOR3 Q18 Q18 Q24 Q16 *)
  0xce195e73;       (* arm_EOR3 Q19 Q19 Q25 Q23 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xce082a31;       (* arm_EOR3 Q17 Q17 Q8 Q10 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef5e1cd;       (* arm_PMULL2_VEC Q13 Q14 Q21 64 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x0ef4e1f4;       (* arm_PMULL_VEC Q20 Q15 Q20 64 *)
  0x0ef5e1d5;       (* arm_PMULL_VEC Q21 Q14 Q21 64 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce0b3231;       (* arm_EOR3 Q17 Q17 Q11 Q12 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e200bd4;       (* arm_REV32_VEC Q20 Q30 8 *)
  0xce153652;       (* arm_EOR3 Q18 Q18 Q21 Q13 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x6e200bd6;       (* arm_REV32_VEC Q22 Q30 8 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0x0ef0e23d;       (* arm_PMULL_VEC Q29 Q17 Q16 64 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xacc12408;       (* arm_LDP Q8 Q9 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc12c0a;       (* arm_LDP Q10 Q11 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e200bd7;       (* arm_REV32_VEC Q23 Q30 8 *)
  0xacc1340c;       (* arm_LDP Q12 Q13 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0xacc13c0e;       (* arm_LDP Q14 Q15 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x3dc0297b;       (* arm_LDR Q27 X11 (Immediate_Offset (word 160)) *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0x6e200bd9;       (* arm_REV32_VEC Q25 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0xce016d21;       (* arm_EOR3 Q1 Q9 Q1 Q27 *)
  0xce006d00;       (* arm_EOR3 Q0 Q8 Q0 Q27 *)
  0xce076de7;       (* arm_EOR3 Q7 Q15 Q7 Q27 *)
  0xce066dc6;       (* arm_EOR3 Q6 Q14 Q6 Q27 *)
  0xce026d42;       (* arm_EOR3 Q2 Q10 Q2 Q27 *)
  0xac810440;       (* arm_STP Q0 Q1 X2 (Postimmediate_Offset (iword (&32))) *)
  0x4eb61ec1;       (* arm_MOV_VEC Q1 Q22 128 *)
  0xce046d84;       (* arm_EOR3 Q4 Q12 Q4 Q27 *)
  0xce115673;       (* arm_EOR3 Q19 Q19 Q17 Q21 *)
  0x4eb41e80;       (* arm_MOV_VEC Q0 Q20 128 *)
  0xce036d63;       (* arm_EOR3 Q3 Q11 Q3 Q27 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0xac810c42;       (* arm_STP Q2 Q3 X2 (Postimmediate_Offset (iword (&32))) *)
  0xce056da5;       (* arm_EOR3 Q5 Q13 Q5 Q27 *)
  0x4eb71ee2;       (* arm_MOV_VEC Q2 Q23 128 *)
  0xac811444;       (* arm_STP Q4 Q5 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xac811c46;       (* arm_STP Q6 Q7 X2 (Postimmediate_Offset (iword (&32))) *)
  0x4eb91f23;       (* arm_MOV_VEC Q3 Q25 128 *)
  0x54ffddeb;       (* arm_BLT (word 2096060) *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200908;       (* arm_REV64_VEC Q8 Q8 8 *)
  0x4e20094a;       (* arm_REV64_VEC Q10 Q10 8 *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x3dc024d7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 144)) *)
  0x3dc02cd9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 176)) *)
  0x6e331d08;       (* arm_EOR_VEC Q8 Q8 Q19 128 *)
  0x4e200929;       (* arm_REV64_VEC Q9 Q9 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x3dc018d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 96)) *)
  0x3dc020d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 128)) *)
  0x4e2009ad;       (* arm_REV64_VEC Q13 Q13 8 *)
  0x4e20098c;       (* arm_REV64_VEC Q12 Q12 8 *)
  0x4e2009ce;       (* arm_REV64_VEC Q14 Q14 8 *)
  0x3dc01cd5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 112)) *)
  0x3dc028d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 160)) *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4ef7e130;       (* arm_PMULL2_VEC Q16 Q9 Q23 64 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x4ec82932;       (* arm_TRN1 Q18 Q9 Q8 64 128 *)
  0x4ec86928;       (* arm_TRN2 Q8 Q9 Q8 64 128 *)
  0x4ef6e15d;       (* arm_PMULL2_VEC Q29 Q10 Q22 64 *)
  0x0ef7e137;       (* arm_PMULL_VEC Q23 Q9 Q23 64 *)
  0x4ef4e169;       (* arm_PMULL2_VEC Q9 Q11 Q20 64 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e301e31;       (* arm_EOR_VEC Q17 Q17 Q16 128 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e321d08;       (* arm_EOR_VEC Q8 Q8 Q18 128 *)
  0x0ef6e156;       (* arm_PMULL_VEC Q22 Q10 Q22 64 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xce1d2631;       (* arm_EOR3 Q17 Q17 Q29 Q9 *)
  0x4eca297d;       (* arm_TRN1 Q29 Q11 Q10 64 128 *)
  0x4eca696a;       (* arm_TRN2 Q10 Q11 Q10 64 128 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ef8e112;       (* arm_PMULL2_VEC Q18 Q8 Q24 64 *)
  0x0ef8e118;       (* arm_PMULL_VEC Q24 Q8 Q24 64 *)
  0x0ef4e174;       (* arm_PMULL_VEC Q20 Q11 Q20 64 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x6e3d1d4a;       (* arm_EOR_VEC Q10 Q10 Q29 128 *)
  0x6e381e52;       (* arm_EOR_VEC Q18 Q18 Q24 128 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x4ef5e15d;       (* arm_PMULL2_VEC Q29 Q10 Q21 64 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x0ef5e155;       (* arm_PMULL_VEC Q21 Q10 Q21 64 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0xce157652;       (* arm_EOR3 Q18 Q18 Q21 Q29 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ecc29b0;       (* arm_TRN1 Q16 Q13 Q12 64 128 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4ef9e188;       (* arm_PMULL2_VEC Q8 Q12 Q25 64 *)
  0x0ef9e199;       (* arm_PMULL_VEC Q25 Q12 Q25 64 *)
  0x4ecc69ac;       (* arm_TRN2 Q12 Q13 Q12 64 128 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e2009ef;       (* arm_REV64_VEC Q15 Q15 8 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4ef7e1aa;       (* arm_PMULL2_VEC Q10 Q13 Q23 64 *)
  0x0ef7e1b7;       (* arm_PMULL_VEC Q23 Q13 Q23 64 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ece29ed;       (* arm_TRN1 Q13 Q15 Q14 64 128 *)
  0x4ef6e1cb;       (* arm_PMULL2_VEC Q11 Q14 Q22 64 *)
  0x0ef6e1d6;       (* arm_PMULL_VEC Q22 Q14 Q22 64 *)
  0x4ece69ee;       (* arm_TRN2 Q14 Q15 Q14 64 128 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e301d8c;       (* arm_EOR_VEC Q12 Q12 Q16 128 *)
  0xce082a31;       (* arm_EOR3 Q17 Q17 Q8 Q10 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e2d1dce;       (* arm_EOR_VEC Q14 Q14 Q13 128 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ef8e190;       (* arm_PMULL2_VEC Q16 Q12 Q24 64 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x0ef8e198;       (* arm_PMULL_VEC Q24 Q12 Q24 64 *)
  0x4ef4e1ec;       (* arm_PMULL2_VEC Q12 Q15 Q20 64 *)
  0x4ef5e1cd;       (* arm_PMULL2_VEC Q13 Q14 Q21 64 *)
  0x0ef5e1d5;       (* arm_PMULL_VEC Q21 Q14 Q21 64 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0xce184252;       (* arm_EOR3 Q18 Q18 Q24 Q16 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x0ef4e1f4;       (* arm_PMULL_VEC Q20 Q15 Q20 64 *)
  0xce195e73;       (* arm_EOR3 Q19 Q19 Q25 Q23 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xce153652;       (* arm_EOR3 Q18 Q18 Q21 Q13 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xce0b3231;       (* arm_EOR3 Q17 Q17 Q11 Q12 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x0ef0e23d;       (* arm_PMULL_VEC Q29 Q17 Q16 64 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x3dc0297b;       (* arm_LDR Q27 X11 (Immediate_Offset (word 160)) *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xce115673;       (* arm_EOR3 Q19 Q19 Q17 Q21 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4ebb1f7d;       (* arm_MOV_VEC Q29 Q27 128 *)
  0xcb000085;       (* arm_SUB X5 X4 X0 *)
  0xf101c0bf;       (* arm_CMP X5 (rvalue (word 112)) *)
  0xad4564d8;       (* arm_LDP Q24 Q25 X6 (Immediate_Offset (iword (&160))) *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0xad4354d4;       (* arm_LDP Q20 Q21 X6 (Immediate_Offset (iword (&96))) *)
  0x6e134270;       (* arm_EXT Q16 Q19 Q19 64 *)
  0xad445cd6;       (* arm_LDP Q22 Q23 X6 (Immediate_Offset (iword (&128))) *)
  0xce00752c;       (* arm_EOR3 Q12 Q9 Q0 Q29 *)
  0x540015ac;       (* arm_BGT (word 692) *)
  0xf10180bf;       (* arm_CMP X5 (rvalue (word 96)) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x0f00e413;       (* arm_MOVI D19 (word 0) *)
  0x0f00e411;       (* arm_MOVI D17 (word 0) *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea31c64;       (* arm_MOV_VEC Q4 Q3 128 *)
  0x4ea21c43;       (* arm_MOV_VEC Q3 Q2 128 *)
  0x4ea11c22;       (* arm_MOV_VEC Q2 Q1 128 *)
  0x0f00e412;       (* arm_MOVI D18 (word 0) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x5400046c;       (* arm_BGT (word 140) *)
  0xf10140bf;       (* arm_CMP X5 (rvalue (word 80)) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea31c64;       (* arm_MOV_VEC Q4 Q3 128 *)
  0x4ea11c23;       (* arm_MOV_VEC Q3 Q1 128 *)
  0x5400052c;       (* arm_BGT (word 164) *)
  0xf10100bf;       (* arm_CMP X5 (rvalue (word 64)) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea11c24;       (* arm_MOV_VEC Q4 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x5400062c;       (* arm_BGT (word 196) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea11c25;       (* arm_MOV_VEC Q5 Q1 128 *)
  0xf100c0bf;       (* arm_CMP X5 (rvalue (word 48)) *)
  0x5400072c;       (* arm_BGT (word 228) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0xf10080bf;       (* arm_CMP X5 (rvalue (word 32)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4ea11c26;       (* arm_MOV_VEC Q6 Q1 128 *)
  0x5400088c;       (* arm_BGT (word 272) *)
  0xf10040bf;       (* arm_CMP X5 (rvalue (word 16)) *)
  0x4ea11c27;       (* arm_MOV_VEC Q7 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x540009ec;       (* arm_BGT (word 316) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x1400005d;       (* arm_B (word 372) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef7e11a;       (* arm_PMULL_VEC Q26 Q8 Q23 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x0ef8e37b;       (* arm_PMULL_VEC Q27 Q27 Q24 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x4ef7e11c;       (* arm_PMULL2_VEC Q28 Q8 Q23 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0xce02752c;       (* arm_EOR3 Q12 Q9 Q2 Q29 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0xce03752c;       (* arm_EOR3 Q12 Q9 Q3 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x4ef5e37b;       (* arm_PMULL2_VEC Q27 Q27 Q21 64 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0xce04752c;       (* arm_EOR3 Q12 Q9 Q4 Q29 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x0ef5e37b;       (* arm_PMULL_VEC Q27 Q27 Q21 64 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x0ef9e11a;       (* arm_PMULL_VEC Q26 Q8 Q25 64 *)
  0x4ef9e11c;       (* arm_PMULL2_VEC Q28 Q8 Q25 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0xce05752c;       (* arm_EOR3 Q12 Q9 Q5 Q29 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x4ef8e37b;       (* arm_PMULL2_VEC Q27 Q27 Q24 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef7e11a;       (* arm_PMULL_VEC Q26 Q8 Q23 64 *)
  0x4ef7e11c;       (* arm_PMULL2_VEC Q28 Q8 Q23 64 *)
  0x0ef8e37b;       (* arm_PMULL_VEC Q27 Q27 Q24 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0xce06752c;       (* arm_EOR3 Q12 Q9 Q6 Q29 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0xce07752c;       (* arm_EOR3 Q12 Q9 Q7 Q29 *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x4ef5e37b;       (* arm_PMULL2_VEC Q27 Q27 Q21 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0x6e084110;       (* arm_EXT Q16 Q8 Q8 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x2e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 64 *)
  0x0ef5e210;       (* arm_PMULL_VEC Q16 Q16 Q21 64 *)
  0x4c00704c;       (* arm_STR Q12 X2 No_Offset *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x6e301e52;       (* arm_EOR_VEC Q18 Q18 Q16 128 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e331e2e;       (* arm_EOR_VEC Q14 Q17 Q19 128 *)
  0x0ef0e235;       (* arm_PMULL_VEC Q21 Q17 Q16 64 *)
  0x6e114231;       (* arm_EXT Q17 Q17 Q17 64 *)
  0x6e2e1e52;       (* arm_EOR_VEC Q18 Q18 Q14 128 *)
  0xce115652;       (* arm_EOR3 Q18 Q18 Q17 Q21 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x6e124252;       (* arm_EXT Q18 Q18 Q18 64 *)
  0xce124673;       (* arm_EOR3 Q19 Q19 Q18 Q17 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0x4c007073;       (* arm_STR Q19 X3 No_Offset *)
  0x6e200bde;       (* arm_REV32_VEC Q30 Q30 8 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0xaa0903e0;       (* arm_MOV X0 X9 *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x6cc527e8;       (* arm_LDP D8 D9 SP (Postimmediate_Offset (iword (&80))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0x52800000;       (* arm_MOV W0 (rvalue (word 0)) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e184312;       (* arm_EXT Q18 Q24 Q24 64 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0xce01752c;       (* arm_EOR3 Q12 Q9 Q1 Q29 *)
  0x0ef2e372;       (* arm_PMULL_VEC Q18 Q27 Q18 64 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef7e10e;       (* arm_PMULL_VEC Q14 Q8 Q23 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0ef8e36f;       (* arm_PMULL_VEC Q15 Q27 Q24 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x4ef7e10d;       (* arm_PMULL2_VEC Q13 Q8 Q23 64 *)
  0xce02752c;       (* arm_EOR3 Q12 Q9 Q2 Q29 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0xce03752c;       (* arm_EOR3 Q12 Q9 Q3 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x4ef5e37b;       (* arm_PMULL2_VEC Q27 Q27 Q21 64 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0xce1a3a73;       (* arm_EOR3 Q19 Q19 Q26 Q14 *)
  0xce1b3e52;       (* arm_EOR3 Q18 Q18 Q27 Q15 *)
  0xce1c3631;       (* arm_EOR3 Q17 Q17 Q28 Q13 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4ef4e10d;       (* arm_PMULL2_VEC Q13 Q8 Q20 64 *)
  0x0ef4e10e;       (* arm_PMULL_VEC Q14 Q8 Q20 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0xce04752c;       (* arm_EOR3 Q12 Q9 Q4 Q29 *)
  0x0ef5e36f;       (* arm_PMULL_VEC Q15 Q27 Q21 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x0ef9e11a;       (* arm_PMULL_VEC Q26 Q8 Q25 64 *)
  0x4ef9e11c;       (* arm_PMULL2_VEC Q28 Q8 Q25 64 *)
  0xce05752c;       (* arm_EOR3 Q12 Q9 Q5 Q29 *)
  0xce1a3a73;       (* arm_EOR3 Q19 Q19 Q26 Q14 *)
  0x4ef8e37b;       (* arm_PMULL2_VEC Q27 Q27 Q24 64 *)
  0xce1c3631;       (* arm_EOR3 Q17 Q17 Q28 Q13 *)
  0xce1b3e52;       (* arm_EOR3 Q18 Q18 Q27 Q15 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef7e10e;       (* arm_PMULL_VEC Q14 Q8 Q23 64 *)
  0x4ef7e10d;       (* arm_PMULL2_VEC Q13 Q8 Q23 64 *)
  0x0ef8e36f;       (* arm_PMULL_VEC Q15 Q27 Q24 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0xce06752c;       (* arm_EOR3 Q12 Q9 Q6 Q29 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0xce1c3631;       (* arm_EOR3 Q17 Q17 Q28 Q13 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0xce07752c;       (* arm_EOR3 Q12 Q9 Q7 Q29 *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x4ef5e37b;       (* arm_PMULL2_VEC Q27 Q27 Q21 64 *)
  0xce1a3a73;       (* arm_EOR3 Q19 Q19 Q26 Q14 *)
  0xce1b3e52;       (* arm_EOR3 Q18 Q18 Q27 Q15 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0x6e084110;       (* arm_EXT Q16 Q8 Q8 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x2e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 64 *)
  0x0ef5e210;       (* arm_PMULL_VEC Q16 Q16 Q21 64 *)
  0x4c00704c;       (* arm_STR Q12 X2 No_Offset *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x6e301e52;       (* arm_EOR_VEC Q18 Q18 Q16 128 *)
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
  0x3dc0296b;       (* arm_LDR Q11 X11 (Immediate_Offset (word 160)) *)
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
  0x14000034;       (* arm_B (word 208) *)
  0x3dc008d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 32)) *)
  0xfd400cd9;       (* arm_LDR D25 X6 (Immediate_Offset (word 24)) *)
  0x6e104215;       (* arm_EXT Q21 Q16 Q16 64 *)
  0x2e301eb5;       (* arm_EOR_VEC Q21 Q21 Q16 64 *)
  0x4ef8e211;       (* arm_PMULL2_VEC Q17 Q16 Q24 64 *)
  0x0ef8e213;       (* arm_PMULL_VEC Q19 Q16 Q24 64 *)
  0x0ef9e2b2;       (* arm_PMULL_VEC Q18 Q21 Q25 64 *)
  0x1400004f;       (* arm_B (word 316) *)
  0x3dc000d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 0)) *)
  0xfd4008d9;       (* arm_LDR D25 X6 (Immediate_Offset (word 16)) *)
  0x6e104215;       (* arm_EXT Q21 Q16 Q16 64 *)
  0x2e301eb5;       (* arm_EOR_VEC Q21 Q21 Q16 64 *)
  0x4ef8e211;       (* arm_PMULL2_VEC Q17 Q16 Q24 64 *)
  0x0ef8e213;       (* arm_PMULL_VEC Q19 Q16 Q24 64 *)
  0x0ef9e2b2;       (* arm_PMULL_VEC Q18 Q21 Q25 64 *)
  0x1400006a;       (* arm_B (word 424) *)
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
  0x6e361e31;       (* arm_EOR_VEC Q17 Q17 Q22 128 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x6e3e1e52;       (* arm_EOR_VEC Q18 Q18 Q30 128 *)
  0x4e284940;       (* arm_AESE Q0 Q10 *)
  0xce002f40;       (* arm_EOR3 Q0 Q26 Q0 Q11 *)
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
  0x6e361e31;       (* arm_EOR_VEC Q17 Q17 Q22 128 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x6e3e1e52;       (* arm_EOR_VEC Q18 Q18 Q30 128 *)
  0x4e284940;       (* arm_AESE Q0 Q10 *)
  0xce002f40;       (* arm_EOR3 Q0 Q26 Q0 Q11 *)
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
  0x6e361e31;       (* arm_EOR_VEC Q17 Q17 Q22 128 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x6e3e1e52;       (* arm_EOR_VEC Q18 Q18 Q30 128 *)
  0x4e284940;       (* arm_AESE Q0 Q10 *)
  0xce002f40;       (* arm_EOR3 Q0 Q26 Q0 Q11 *)
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
  0x6e124252;       (* arm_EXT Q18 Q18 Q18 64 *)
  0x6e311e73;       (* arm_EOR_VEC Q19 Q19 Q17 128 *)
  0x6e321e73;       (* arm_EOR_VEC Q19 Q19 Q18 128 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0x4c007073;       (* arm_STR Q19 X3 No_Offset *)
  0x6e200bbe;       (* arm_REV32_VEC Q30 Q29 8 *)
  0x4e284940;       (* arm_AESE Q0 Q10 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0xce002f40;       (* arm_EOR3 Q0 Q26 Q0 Q11 *)
  0x3c810440;       (* arm_STR Q0 X2 (Postimmediate_Offset (word 16)) *)
  0x17fffec8        (* arm_B (word 268434208) *)
];;

(* The code begins with the BTI landing pad (bti c).  As for x86 IBT, the    *)
(* proofs are about the trimmed code without it, which is the code of a      *)
(* -DNO_IBT build, and the subroutine theorems for the full code are derived *)
(* from them by ARM_ADD_IBT_RULE.  So the code offsets in this file, pc + n  *)
(* in the statements and 0x... in the comments, are those of the trimmed     *)
(* code, as in a disassembly of a -DNO_IBT object.  In the default object    *)
(* they are 4 larger.                                                        *)

let aes128_gcm_dec_alt_tmc =
  define_trimmed "aes128_gcm_dec_alt_tmc" aes128_gcm_dec_alt_mc;;
let AES128_GCM_DEC_ALT_EXEC = ARM_MK_EXEC_RULE aes128_gcm_dec_alt_tmc;;

(* `|- LENGTH aes128_gcm_dec_alt_tmc = 4960`.  The statements spell the code
   region in their nonoverlapping preconditions as
   `LENGTH aes128_gcm_dec_alt_tmc`; only some terms of the safety proof write
   the numeral 4960.  The store-safety check of the stepper does numeric
   arithmetic on that length, so each simulation first reduces it to the
   numeral with RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]). *)
let WB_MC_LEN = fst AES128_GCM_DEC_ALT_EXEC;;

(* The input buffer, read as whole blocks.  First for a 16 * n-byte prefix   *)
(* of x, by induction on n: the top block of a 16 * (n + 1)-byte read, and   *)
(* the 16 * n-byte prefix read the induction hypothesis takes, are           *)
(* READ_BYTES_AND_BYTE128_MERGE.  Then for the whole buffer, the form every  *)
(* consumer has.                                                             *)
let INPUT_PREFIX_TO_BYTE128_LANES = prove
 (`!n (in_p:int64) (x:byte list) s.
    16 * n <= LENGTH x /\
    read (memory :> bytes (in_p, 16 * n)) s = num_of_bytelist (SUB_LIST (0, 16 * n) x)
    ==> !k. k < n ==> read (memory :> bytes128 (word_add in_p (word (16 * k)))) s =
                      bytes_to_int128 (SUB_LIST (16 * k, 16) x)`,
  INDUCT_TAC THEN REWRITE_TAC[LT; ARITH_RULE `16 * SUC n = 16 * n + 16`] THEN
  ASM_MESON_TAC[READ_BYTES_AND_BYTE128_MERGE; ARITH_RULE `a + 16 <= l ==> a <= l`]);;

let INPUT_BYTES_TO_BYTE128_LANES = prove
 (`!n (in_p:int64) (x:byte list) s.
    LENGTH x = 16 * n /\
    read (memory :> bytes (in_p, 16 * n)) s = num_of_bytelist x
    ==> !k. k < n ==> read (memory :> bytes128 (word_add in_p (word (16 * k)))) s =
                      bytes_to_int128 (SUB_LIST (16 * k, 16) x)`,
  MESON_TAC[INPUT_PREFIX_TO_BYTE128_LANES; SUB_LIST_LENGTH_IMPLIES; LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The shared front: the entry pc+0x1c to the 0x340 b.ge (pc+832), steps     *)
(* 1..201.  It loads ivec, the tag and the 11 round keys, computes the 8     *)
(* counter blocks from the reversed base counter and the increments +1..+7   *)
(* (one add and one rev32 each) and runs the 8 keystream towers up to the    *)
(* final aese (aes9).  It reads no input block and no key-table entry, and   *)
(* its one data-dependent branch before the 0x340 b.ge is the dispatch b.le  *)
(* at step 8, which falls through for nblk >= 5.  So WBN_FRONT_PREBRANCH     *)
(* proves it once, on the union band                                         *)
(*   5 <= nblk /\ 128 * nblk < 2 EXP 64,                                     *)
(* with X5 general and the raw flags of the cmp x0,x5 (step 201) kept.  The  *)
(* 5..8 leg (WB_FRONT_BUF) takes the b.ge and runs the 5 tail-entry steps to *)
(* the shared seam pc+3032; the >=9 leg falls through to the front-N.        *)
(* ------------------------------------------------------------------------- *)

(* The statement of WB_FRONT_BUF.  Its postcondition wb_front_postcond (below)
   is the simulated state s207 at the seam, with the 8 in-flight keystream
   towers folded to aes9; it is built with term builders, so that the front is
   simulated only in the proof. *)
let wb_front_pre_tm = `\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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
          htable_mem_dec h htable_p s`;;

(* The band 5 <= nblk <= 8: WB_FRONT_BUF, stated with these hypotheses, is used
   only by prove_band for bands 5..8 (bands 1..4 take the b.le at step 8 to the
   small-message path and are proved by WB_FUSED_1BLOCK .. WB_FUSED_4BLOCK).
   The bands supply nblk = 5..8, so 5 <= nblk closes by NUM_REDUCE_CONV, and
   the union band wbn_front_hyps_uni_tm also starts with 5 <= nblk. *)
let wb_front_hyps_tm = `5 <= nblk /\ nblk <= 8 /\ LENGTH (ibytes:byte list) = 16 * nblk /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (out_p:int64, 16 * nblk) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (tag_p:int64, 16) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (ivec_p:int64, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 16 * nblk) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 176) /\
    nonoverlapping (ivec_p, 16) (htable_p:int64, 192) /\
    nonoverlapping (in_p, 16 * nblk) (stackpointer, 80) /\
    nonoverlapping (key_p, 176) (stackpointer, 80) /\
    nonoverlapping (htable_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (tag_p, 16) (in_p, 16 * nblk) /\
    nonoverlapping (tag_p, 16) (key_p, 176) /\
    nonoverlapping (tag_p, 16) (htable_p, 192) /\
    nonoverlapping (tag_p, 16) (stackpointer, 80)`;;

let wb_front_vars = [`pc:num`;`stackpointer:int64`;`out_p:int64`;`tag_p:int64`;`ivec_p:int64`;
            `in_p:int64`;`key_p:int64`;`htable_p:int64`;`nblk:num`;`ibytes:byte list`;
            `xi:int128`;`ctr0:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;
            `k4:int128`;`k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;
            `k10:int128`;`h:int128`];;

let mk_wb_front_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wb_front_hyps_tm, ens));;

(* The simulated postconditions (wb_front_postcond and the others built below)
   state the 8 in-flight keystream towers folded to aes9 (gcm_ctr_inc^i ctr0)
   k0 .. k9, which keeps the Q-register conjuncts readable; wb_front_fold_tac
   applies the same folds, GSYM aes9 and the GSYM of the lane lemmas, to the
   simulated assumptions before the final-state match. *)
let wb_front_fold_tac =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM aes9]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE(map GSYM wb_ctr_lanes_thms));;

(* the keystream tower aes9 ctr k0 .. k9 *)
let wbp_aes9 ctr =
  list_mk_comb(`aes9`, ctr :: map (fun i -> mk_var("k"^string_of_int i,`:int128`)) (0--9));;
(* the round keys k0 .. k10 and the 12 htable_mem_dec slots as memory reads *)
let wbp_key_reads =
  map (fun i -> mk_eq(wbp_mem128 `key_p:int64` i, mk_var("k"^string_of_int i,`:int128`))) (0--10);;
(* the registers the front sets up for the whole kernel (Q19 holds xi
   reversed; Q26, Q27, Q28 hold the round keys k9, k10, k8) *)
let wbp_ctx xi =
  [`read X16 s = ivec_p`;
   `read X10 s = word_add stackpointer (word 64)`;
   `read X15 s = word 4294967296`;
   `read Q31 s = word 79228162514264337593543950336`;
   wbp_rd `Q19` (mk_comb(`word_bytereverse:int128->int128`, xi));
   `read X4 s = word_add in_p (word (16 * nblk))`;
   `read Q27 s = k10`;
   `read Q26 s = k9`;
   `read Q28 s = k8`];;
(* decrypted block i, word_xor (word_xor cph_i (aes9 ctr_i k0 .. k9)) k10,
   and its store *)
let wbp_pt i = mk_comb(mk_comb(`word_xor:int128->int128->int128`,
  mk_comb(mk_comb(`word_xor:int128->int128->int128`, mk_cph i), wbp_aes9 (mk_ctr i))), `k10:int128`);;
let wbp_out i = mk_eq(wbp_mem128 `out_p:int64` i, wbp_pt i);;

(* the in-flight keystream tower of block i in register Qi *)
let wbp_towers = map (fun i -> wbp_rd (mk_const("Q"^string_of_int i,[])) (wbp_aes9 (mk_ctr i))) (0--7);;

(* The seam state at pc+3032, after the 0x340 b.ge is taken (nblk <= 8) and
   the tail entry has run mov v29,v27 (Q29 = k10), sub x5,x4,x0
   (X5 = 16 * nblk), cmp x5,#0x70, ldp q24,q25,[x6,#160] (the key-table
   entries at offsets 160 and 176: Q24 = the packed Karatsuba mids of H^8 and
   H^7, Q25 = H^8) and ldr q9,[x0],#16 (input block 0).  The front sets v30
   to the base counter + 7 and adds the increment once more, so
   Q30 = gcm_ctr_raw (word 8) ctr0. *)
let wb_front_postcond = wbp_post
 ([`aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc`;
   `read PC s = word (pc + 3032)`;
   wbp_rd `Q24` (wbp_hmid 7);
   wbp_rd `Q25` (wbp_hpow 8)] @
  wbp_cmpi_flags `word (16 * nblk):int64` 112 @
  wbp_towers @
  [`read (memory :> bytes64 (word_add stackpointer (word 64))) s = word 13979173243358019584`;
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
  [`read X5 s = word (16 * nblk)`;
   `read X0 s = word_add in_p (word 16)`;
   wbp_rd `Q9` (mk_cph 0);
   `read Q29 s = k10`;
   `read Q30 s = gcm_ctr_raw (word 8) ctr0`]);;

let AND_MASK_16NBLK_ANY = prove
 (`!nblk. 1 <= nblk /\ 16 * nblk < 2 EXP 64
        ==> word_and (word_sub (word (16 * nblk)) (word 1))
                     (word 18446744073709551488):int64 =
            word (128 * ((nblk - 1) DIV 8))`,
  REWRITE_TAC[WORD_ARITH
   `word 18446744073709551488:int64 = word_not(word(2 EXP 7 - 1))`;
   WORD_AND_NOT_MASK_WORD] THEN
  SIMP_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1; VAL_WORD_EQ; DIMINDEX_64;
           ARITH_RULE `2 EXP 7 = 128`; ARITH_RULE `1 <= n ==> 1 <= 16 * n`;
           ARITH_RULE `(16 * n - 1) DIV 128 = (n - 1) DIV 8`]);;

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
  SUBGOAL_THEN `read (memory :> bytes128 in_p) s0 = bytes_to_int128 (SUB_LIST (0,16) ibytes)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`] INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
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

(* Steps 1..201.  The dispatch b.le (s8) falls through (GUARD_LE_FALLTHRU);  *)
(* the increments +2..+7 (s16-s21) reduce to word constants; the tag load    *)
(* (s22-s24) is folded by Q19_BREVXI.  Each of the steps 25..56 (the counter *)
(* setup at s25-s41: the base rev32 and the adds and rev32s of blocks 1..7,  *)
(* with the first AES rounds around it) and the eighth add of v30, at s174,  *)
(* is followed by GCM_SIMD_SIMPLIFY_TAC; the flat word_add lanes this leaves *)
(* after s56 are folded to gcm_ctr_inc^k ctr0 by GSYM wb_ctr_lanes_thms.     *)
(* DISCARD_STALE_Q30_TAC keeps only the latest Q30 fact.                     *)
let WBN_FRONT_PREBRANCH_STEPS_TAC =
  ARM_STEPS_TAC AES128_GCM_DEC_ALT_EXEC (1--6) THEN
  MP_TAC(SPEC `nblk:num` GUARD_LE_FALLTHRU) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  ARM_STEPS_TAC AES128_GCM_DEC_ALT_EXEC (7--8) THEN
  ARM_STEPS_TAC AES128_GCM_DEC_ALT_EXEC (9--15) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AES128_GCM_DEC_ALT_EXEC (i--i) THEN
                      GCM_SIMD_SIMPLIFY_TAC) (16--21)) THEN
  ARM_STEPS_FOLD_DISCARD_TAC AES128_GCM_DEC_ALT_EXEC (22--24) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[Q19_BREVXI]) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AES128_GCM_DEC_ALT_EXEC (i--i) THEN
                      GCM_SIMD_SIMPLIFY_TAC) (25--56)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE(map GSYM wb_ctr_lanes_thms)) THEN
  ARM_STEPS_TAC AES128_GCM_DEC_ALT_EXEC (57--100) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AES128_GCM_DEC_ALT_EXEC (101--173) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AES128_GCM_DEC_ALT_EXEC (174--174) THEN
  GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AES128_GCM_DEC_ALT_EXEC (175--201) THEN DISCARD_STALE_Q30_TAC;;

let WBN_FRONT_PREBRANCH_TAC = wbn_init_uni_tac THEN WBN_FRONT_PREBRANCH_STEPS_TAC;;

(* prefix goal builder: union-band hypotheses, front precondition and frame *)
let mk_wbn_prebranch_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_uni_tm, ens));;

(* The pre-branch postcondition: the s201 state at the 0x340 b.ge.          *)
let wbn_front_prebranch_postcond = wbp_post
 ([`aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc`;
   `read PC s = word (pc + 832)`] @
  wbp_towers @
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
  [mk_eq(wbp_mem128 `in_p:int64` 0, mk_cph 0)] @ wbp_ctx `xi:int128`);;

(* The shared pre-branch prefix lemma. *)
let WBN_FRONT_PREBRANCH = prove(mk_wbn_prebranch_goal wbn_front_prebranch_postcond,
  WBN_FRONT_PREBRANCH_TAC THEN wb_front_fold_tac THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC);;

(* The front of bands 5..8: WBN_FRONT_PREBRANCH, chained by                  *)
(* ENSURES_TRANS_SIMPLE, then step 202, the 0x340 b.ge, taken (X5 = in_p for *)
(* nblk <= 8, so the cmp x0,x5 compares equal), and the 5 tail-entry steps   *)
(* 0xbc4..0xbd4 (203..207) to the seam pc+3032.  As in                       *)
(* WBN_FRONT_TO_PREP_916, one simplification comes first (X5 = in_p by       *)
(* D_ZERO_LE8, so NF = VF = F and the stepper takes the b.ge; the ABI frame  *)
(* is unfolded for the final state), then a close for the sub x5,x4,x0 value *)
(* and for the top lane of v30, the base counter + 7 then + 1 of the front,  *)
(* as gcm_ctr_raw (word 8) ctr0.                                             *)
let WB_FRONT_BUF = prove(mk_wb_front_goal wb_front_postcond,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_front_prebranch_postcond THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    MATCH_MP_TAC WBN_FRONT_PREBRANCH THEN
    ASM_SIMP_TAC[ARITH_RULE `nblk <= 8 ==> 128 * nblk < 2 EXP 64`];
    ASM_SIMP_TAC[D_ZERO_LE8; ARITH_RULE `5 <= nblk ==> 1 <= nblk`; WORD_ADD_0;
                 WORD_SUB_REFL; IVAL_WORD_0; INT_SUB_REFL; INT_LT_REFL;
                 MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ARM_SIM_TAC AES128_GCM_DEC_ALT_EXEC (202--207) THEN
    REWRITE_TAC[gcm_ctr_raw_def;
                WORD_RULE `word_sub (word_add x y) x:int64 = y`;
                WORD_RULE `word_add (word_add (x:32 word) (word 7)) (word 1) =
                           word_add x (word 8)`]]);;

let GCM_SIMD_SIMPLIFY_KGH_TAC =
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
    else if Hashtbl.mem gcm_simd_kgh_tbl c then th
    else let th' = apply_F th in
         (if concl th' = c then Hashtbl.add gcm_simd_kgh_tbl c ());
         th');;
let ARM_STEPS_FOLD_KEEPGH_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_KGH_TAC THEN
              DISCARD_OLDSTATE_KEEPGH_TAC s THEN CLARIFY_TAC) (statenames "s" snums);;

(* The sub v30.4s cascade: the stepper leaves word_subword (word_join ..)    *)
(* unreduced, so without this each sub would nest the whole previous Q30    *)
(* four times; a top-down WORD_SIMPLE_SUBWORD_CONV on Q30 after every       *)
(* cascade step keeps it as flat word_sub chains on the four lanes.         *)
let Q30_NORM_TAC : tactic =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if (try (match lhs c with
             | Comb(Comb(Const("read",_),Const("Q30",_)),_) -> true
             | _ -> false) with _ -> false)
    then CONV_RULE(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) th
    else th);;
let ARM_STEPS_RESOLVE_Q30_TAC exec range =
  MAP_EVERY (fun n -> RESOLVE_BRANCH_TAC THEN ARM_STEPS_TAC exec [n] THEN Q30_NORM_TAC) range;;

(* Plaintext capture: the eor3 with the ciphertext and k10 leaves            *)
(*   read q sn = word_xor (word_xor cph (aes9 ctr ..)) k10,                  *)
(* which is word_xor cph (aes128_encrypt ctr ..) by                          *)
(* AES128_XOR_ENCRYPT_RECONSTRUCT; the captured form replaces the read.      *)
let WB_PT_CAPTURE_TAC sn q cphv ctr =
  let st = mk_var(sn,`:armstate`) in
  let lhs_tm = list_mk_icomb "read" [q; st] in
  let goal_tm = mk_eq(lhs_tm, subst [cphv,`ccc:int128`; ctr,`ttt:int128`]
    `word_xor (ccc:int128) (aes128_encrypt (ttt:int128) [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10])`) in
  SUBGOAL_THEN goal_tm
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = lhs_tm with _ -> false) then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = lhs_tm with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   REWRITE_TAC[GSYM AES128_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE;
   ALL_TAC];;

(* The 1-block GHASH bridge: GMULT_FULL_CORRECT_BA unfolds the spec side to  *)
(* the byte form, the pmul atoms of the two sides are abbreviated and merged *)
(* (ABBREV_INNER_PMULS_TAC, MERGE_PMUL_ATOMS_TAC), the reduction-constant    *)
(* products are put in shift form (PMUL_W_64_128), and BITBLAST_TAC decides  *)
(* the GF(2)-linear rest.  The eor3s of the tail reduction (0xe58, 0xe64)    *)
(* only reorder that linear form.                                            *)
let WB1_GMULT_BRIDGE_TAC : tactic =
  POP_ASSUM_LIST(K ALL_TAC) THEN
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
  BITBLAST_TAC;;

(* Replace the assumption `read c sn = _` by the proved clean form.          *)
let WB_REPLACE_READ_TAC (lhs_tm:term) (proof:tactic) (rhs_tm:term) =
  SUBGOAL_THEN (mk_eq(lhs_tm, rhs_tm))
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = lhs_tm with _ -> false) then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = lhs_tm with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN proof;
   ALL_TAC];;

(* The 2-block GHASH bridge: GHASH_POLYVAL_ACC_2, with the h2 fact, and      *)
(* GMULT2_FULL_CORRECT_BA unfold the spec side to the byte form,             *)
(* MERGE_2BLK_TAC merges the pmul atoms of the two sides, and BITBLAST_TAC   *)
(* decides the remaining GF(2)-linear identity, whose shape the eor3s of the *)
(* tail reduction change.                                                    *)
let WB2_GMULT2_BITBLAST_TAC : tactic =
  let a0t = `word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`
  and a1t = `word_bytereverse cph1:int128` in
  let gmult2_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [a0t; `byteswap128 h2:int128`; a1t; `byteswap128 h:int128`] GMULT2_FULL_CORRECT_BA) in
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th)=`byteswap128 h2` with _->false)
    then GEN_REWRITE_TAC RAND_CONV
           [REWRITE_RULE[GSYM gmult2_dec]
             (GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) [GSYM th]
               (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
                       `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`]
                 GHASH_POLYVAL_ACC_2))]
    else NO_TAC) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
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
  BITBLAST_TAC;;

let mk_out_conj i =
  mk_eq(mk_outp_read i,
    subst [mk_cph i,`ccc:int128`; mk_ctr i,`ttt:int128`]
      `word_xor (ccc:int128) (aes128_encrypt (ttt:int128)
        [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10])`);;

let mk_band_goal k =
  let n16 = mk_small_numeral(16*k) and n128 = mk_small_numeral(128*k) in
  let hyps = subst [n16,`sss:num`]
    `LENGTH (ibytes:byte list) = sss /\
     aligned 16 stackpointer /\
     nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (stackpointer:int64, 80) /\
     nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (out_p:int64, sss) /\
     nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (tag_p:int64, 16) /\
     nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (ivec_p:int64, 16) /\
     nonoverlapping (out_p, sss) (tag_p, 16) /\
     nonoverlapping (out_p, sss) (ivec_p, 16) /\
     nonoverlapping (tag_p, 16) (ivec_p, 16) /\
     nonoverlapping (ivec_p, 16) (in_p:int64, sss) /\
     nonoverlapping (ivec_p, 16) (key_p:int64, 176) /\
     nonoverlapping (ivec_p, 16) (htable_p:int64, 192) /\
     nonoverlapping (in_p, sss) (stackpointer, 80) /\
     nonoverlapping (key_p, 176) (stackpointer, 80) /\
     nonoverlapping (htable_p, 192) (stackpointer, 80) /\
     nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
     nonoverlapping (tag_p, 16) (in_p, sss) /\
     nonoverlapping (tag_p, 16) (key_p, 176) /\
     nonoverlapping (tag_p, 16) (htable_p, 192) /\
     nonoverlapping (tag_p, 16) (stackpointer, 80) /\
     nonoverlapping (out_p, sss) (in_p, sss) /\
     nonoverlapping (out_p, sss) (key_p, 176) /\
     nonoverlapping (out_p, sss) (htable_p, 192) /\
     nonoverlapping (out_p, sss) (stackpointer, 80)` in
  let pre = subst [n16,`sss:num`; n128,`bbb:num`]
    `\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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
        htable_mem_dec h htable_p s` in
  let pc_post = `read PC s = word (pc + 3708)` in
  let x9_post = subst [n16,`sss:num`] `read X9 s = word sss` in
  let outs = map mk_out_conj (0--(k-1)) in
  let xi_post = subst [mk_ghash_list k,`lll:int128 list`]
    `read (memory :> bytes128 tag_p) s =
     word_bytereverse
       (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi) (lll:int128 list))` in
  (* The counter write-back at band exit, in spine form
     gcm_ctr_inc_iter k ctr0 (= gcm_ctr_add (word k) ctr0), closed in the
     band tails by WB_IVEC_CLOSE_TAC k (WB_IVEC_CLOSE8_TAC for k = 8). *)
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
          `k8:int128`;`k9:int128`;`k10:int128`;`h:int128`] WB_FRONT_BUF);;
(* intermediate assertion = WB_FRONT_BUF's postcond @ nblk:=k, normalized *)
let q_at k = rhs(concl(REWRITE_CONV[arith_16k k; arith_128k k]
  (vsubst [mk_small_numeral k,`nblk:num`] wb_front_postcond)));;

(* Back-leg preparation for band k: init at the seam, derive the input lanes
   1..k-1, and abbreviate the cph names and the h powers, so that the band
   tails apply.  The seam state is named s199 here, although WB_FRONT_BUF
   reaches it as s207, and the tail states are numbered on from it. *)
let WB_PREP_TAC k =
  let n16 = mk_small_numeral(16*k) in
  let lanes =
    if k = 1 then ALL_TAC else
    SUBGOAL_THEN (subst [mk_small_numeral k,`kkk:num`]
      `!i. i < kkk ==> read (memory :> bytes128 (word_add in_p (word (16 * i)))) s199 =
              bytes_to_int128 (SUB_LIST (16 * i, 16) (ibytes:byte list))`)
      MP_TAC THENL
    [MATCH_MP_TAC INPUT_BYTES_TO_BYTE128_LANES THEN
     ASM_REWRITE_TAC[ARITH_RULE(mk_eq(mk_binop `( * ):num->num->num` `16` (mk_small_numeral k), n16))];
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
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN ENSURES_INIT_TAC "s199" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  lanes THEN cphs THEN habbrevs;;

(* ========================================================================= *)
(* The shared per-block back-leg, proved once per residue.                   *)
(*                                                                           *)
(* The back-leg simulation, WB_PREP_TAC k followed by the tail tactic of     *)
(* band k, from the seam pc+3032 to the core exit pc+3708, is proved once    *)
(* per k as WB_TAIL_GEN2_k, from a strictly weaker precondition than that of *)
(* prove_band: q_at k without 5 cells that the tail does not read.  Both     *)
(* goals share the postcondition and the frame of mk_band_goal k, so the     *)
(* weak-precondition back-leg implies the full one by dropping conjuncts     *)
(* (ENSURES_PRECONDITION_THM, no re-simulation), and WB_TAIL_GEN2_k serves   *)
(* both prove_band (below) and the nblk > 8 recomposition (further below).   *)
(*                                                                           *)
(* The 5 dropped cells (sp+72, tag_p, ivec_p, in_p block 0, X1) are never    *)
(* read by the tail code, [0xbd8,0xe7c) and the exact-8 drain                *)
(* [0xe9c,0x1010).  X9 is not read either, but it is kept generically as     *)
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

(* ------------------------------------------------------------------------- *)
(* Per-band tail tactics, from the seam s199 (pc+3032) to the core exit      *)
(* pc+3708.  Each block's plaintext is captured as soon as its eor3 with the *)
(* ciphertext and k10 lands in Q12.  The residue cascade is stepped with the *)
(* Q30 normalizer, the GHASH rounds with the KEEPGH stepper in the bands 1   *)
(* and 2 and with the Q18-latest stepper in the bands 3..8, and the          *)
(* reduction with the KEEPGH stepper; the tag is bridged at the last eor3 of *)
(* the shared reduction (0xe64).                                             *)
(* ------------------------------------------------------------------------- *)

(* r = 1: s203 eor3 (block-0 plaintext), s204-s250 the cascade to 0xe14,     *)
(* s251-s263 the block-0 GHASH round (with the output store st1 at s259),    *)
(* s264-s271 the reduction, s272/s273 ext/rev64, s274 tag store, s275/s276   *)
(* rev32 v30 / str q30,[x16] (ivec write-back).                              *)
let WB_TAIL_1_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AES128_GCM_DEC_ALT_EXEC (200--203) THEN
  WB_PT_CAPTURE_TAC "s203" `Q12` `cph:int128` `ctr0:int128` THEN
  ARM_STEPS_RESOLVE_Q30_TAC AES128_GCM_DEC_ALT_EXEC (204--251) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AES128_GCM_DEC_ALT_EXEC (252--258) THEN
  (* 259: st1 {v12.16b},[x2], the output store; carry its readback across
     the discard *)
  ARM_VSTEPS_FOLD_TAC AES128_GCM_DEC_ALT_EXEC [259] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 out_p) s259` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_TAC "s259" THEN DISCH_TAC THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AES128_GCM_DEC_ALT_EXEC (260--271) THEN
  (* the GHASH bridge at s271 (pc+3688, after eor3 v19,v19,v18,v17) *)
  WB_REPLACE_READ_TAC `read Q19 (s271:armstate)` WB1_GMULT_BRIDGE_TAC
    `polyval_dot (word_xor (word_bytereverse xi) (word_bytereverse cph)) (byteswap128 h)` THEN
  ABBREV_TAC `gval:int128 = polyval_dot (word_xor (word_bytereverse xi)
    (word_bytereverse cph)) (byteswap128 h)` THEN
  (* 272 ext (half-swap), 273 rev64 -> Q19 = word_bytereverse gval *)
  ARM_VSTEPS_FOLD_TAC AES128_GCM_DEC_ALT_EXEC (272--273) THEN
  WB_REPLACE_READ_TAC `read Q19 (s273:armstate)` (CONV_TAC WORD_BLAST)
    `word_bytereverse (gval:int128)` THEN
  (* 274: st1 {v19.16b},[x3], the tag store; 275, 276: rev32 v30 and
     str q30,[x16], the ivec write-back *)
  ARM_VSTEPS_TAC AES128_GCM_DEC_ALT_EXEC [274] THEN
  ARM_VSTEPS_FOLD_TAC AES128_GCM_DEC_ALT_EXEC (275--276) THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [CONJ_TAC THENL
    [EXPAND_TAC "gval" THEN AP_TERM_TAC THEN REWRITE_TAC[GHASH_1BLOCK_CORRECT];
     ivtac];
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
   REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]];;

(* r = 2: s203 eor3 (block-0 plaintext), s204-s247 the cascade to the taken  *)
(* b.gt at 0xc94, s248 st1 (block-0 store, x2 += 16), s249-s264 the block-0  *)
(* GHASH round with h2 (with the block-1 plaintext eor3 at s260), s265-s277  *)
(* the block-1 round with h (with the block-1 store st1 at s273), s278-s285  *)
(* the reduction, s286/s287 ext/rev64, s288 tag store, s289/s290 the ivec    *)
(* write-back.                                                               *)
let WB_TAIL_2_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AES128_GCM_DEC_ALT_EXEC (200--203) THEN
  WB_PT_CAPTURE_TAC "s203" `Q12` `cph0:int128` `ctr0:int128` THEN
  ARM_STEPS_RESOLVE_Q30_TAC AES128_GCM_DEC_ALT_EXEC (204--247) THEN
  (* 248: st1 {v12.16b},[x2],#16, the block-0 store; carry its readback
     across the discard *)
  ARM_VSTEPS_FOLD_TAC AES128_GCM_DEC_ALT_EXEC [248] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 out_p) s248` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_KEEPGH_TAC "s248" THEN DISCH_TAC THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AES128_GCM_DEC_ALT_EXEC (249--260) THEN
  WB_PT_CAPTURE_TAC "s260" `Q12` `cph1:int128` `gcm_ctr_inc ctr0:int128` THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AES128_GCM_DEC_ALT_EXEC (261--272) THEN
  (* 273: st1 {v12.16b},[x2], the block-1 store; carry both readbacks across
     the discard *)
  ARM_VSTEPS_TAC AES128_GCM_DEC_ALT_EXEC [273] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add out_p (word 16))) s273` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 out_p) s273` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_KEEPGH_TAC "s273" THEN DISCH_TAC THEN DISCH_TAC THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AES128_GCM_DEC_ALT_EXEC (274--285) THEN
  (* the GHASH bridge at s285 (pc+3688, after eor3 v19,v19,v18,v17) *)
  WB_REPLACE_READ_TAC `read Q19 (s285:armstate)` WB2_GMULT2_BITBLAST_TAC
    `ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1]` THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1]` THEN
  (* 286 ext (half-swap), 287 rev64 -> Q19 = word_bytereverse gval *)
  ARM_VSTEPS_FOLD_TAC AES128_GCM_DEC_ALT_EXEC (286--287) THEN
  WB_REPLACE_READ_TAC `read Q19 (s287:armstate)` (CONV_TAC WORD_BLAST)
    `word_bytereverse (gval:int128)` THEN
  (* 288: st1 {v19.16b},[x3], the tag store; 289, 290: rev32 v30 and
     str q30,[x16], the ivec write-back *)
  ARM_VSTEPS_TAC AES128_GCM_DEC_ALT_EXEC [288] THEN
  ARM_VSTEPS_FOLD_TAC AES128_GCM_DEC_ALT_EXEC (289--290) THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [ivtac;
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
   REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]];;

(* The 8 shared back-legs.  Their proofs from the weakened precondition show *)
(* that the tail does not read X1 and leaves X9 unchanged.                   *)
let WB_TAIL_GEN2_1 = prove(wbn_tail_backleg_goal5_return 1,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 1 THEN WB_TAIL_1_TAC (WB_IVEC_CLOSE_TAC 1));;
let WB_TAIL_GEN2_2 = prove(wbn_tail_backleg_goal5_return 2,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 2 THEN WB_TAIL_2_TAC (WB_IVEC_CLOSE_TAC 2));;

(* The band prover, for k = 5..8 (bands 1..4 take the small-message path
   below): ENSURES_FRAME_SUBSUMED and ENSURES_TRANS split the band at the seam
   pc+3032 (q_at k), WB_FRONT_BUF discharges the front leg, and the back leg is
   not simulated again: it follows from the back-leg theorem backleg
   (WB_TAIL_GEN2_k) by precondition weakening (q_at k implies its weaker
   precondition, which omits five cells the tail does not read). *)
let prove_band k backleg =
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
      MATCH_MP_TAC backleg THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]);;

(* XOR_LANE_CLOSE_TAC closes a GF(2)-linear 128-bit word identity over pmul  *)
(* atoms without bit-blasting the big terms: it splits the identity into its *)
(* two 64-bit lanes (WORD_EQ_LANES_128), pushes subword, zx and shl through  *)
(* every xor, generalizes each distinct xor leaf, largest first, to a fresh  *)
(* 64-bit variable (XOR_LEAVES_GEN_TAC), and decides the remaining pure-xor  *)
(* identity, which BITBLAST_TAC does on variables only.                      *)
let WORD_EQ_LANES_128 = prove
 (`!x y:int128. x = y <=>
     word_subword x (0,64):64 word = word_subword y (0,64) /\
     word_subword x (64,64):64 word = word_subword y (64,64)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[QQ0SPLIT] THEN ASM_REWRITE_TAC[]);;
let XOR_LEAVES_GEN_TAC : tactic = fun (asl,w) ->
  let rec leaves t = match t with
    | Comb(Comb(Const("word_xor",_),a),b) -> leaves a @ leaves b
    | _ -> [t] in
  let l, r = dest_eq w in
  let ls = setify (filter (fun t -> not (is_var t) &&
                     not (try fst(dest_const(rator t)) = "word" with _ -> false))
                   (leaves l @ leaves r)) in
  let size t = String.length (string_of_term t) in
  let ls = sort (fun a b -> size a > size b) ls in
  let n = ref 0 in
  EVERY (map (fun t -> incr n;
    SPEC_TAC(t, mk_var("xl"^string_of_int !n, type_of t))) ls) (asl,w);;
let XOR_LANE_CLOSE_TAC : tactic =
  GEN_REWRITE_TAC I [WORD_EQ_LANES_128] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR; WORD_ZX_XOR; WORD_SHL_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR; WORD_ZX_XOR; WORD_SHL_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_ZX_0; WORD_SHL_0; WORD_SUBWORD_0] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONJ_TAC THEN XOR_LEAVES_GEN_TAC THEN BITBLAST_TAC;;

(* The midacc re-expansion: the definition of midacc is the assumption       *)
(* `<value> = midacc` whose left side is not a state read (the steppers also *)
(* carry `read Q18 sN = midacc` forward, which must not be picked).          *)
let MIDACC_EXPAND_TAC : tactic = fun (asl,w) ->
  let (_,th) = List.find (fun (_,th) ->
    try let c = concl th in
        is_eq c && rand c = `midacc:int128` &&
        not (try fst(dest_const(fst(strip_comb(lhs c)))) = "read" with _ -> false)
    with _ -> false) asl in
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w);;

(* Undo the abbreviations of the reduction-constant products word_pmul x     *)
(* (word 0xC2..), so that PMUL_W_64_128 can put them in shift form.          *)
let EXPAND_WPMUL_ATOMS_TAC : tactic = fun (asl,w) ->
  let defs = filter (fun (_,th) -> let c = concl th in
    is_eq c && is_var(rhs c) && isWpmul(lhs c)) asl in
  REWRITE_TAC (map (GSYM o snd) defs) (asl,w);;

(* The 3-block GHASH bridge: spec_to_byteform_wb3 (with the h2 and h3 facts) *)
(* and GMULT3_FULL_CORRECT_BA unfold the spec side to the byte form; the     *)
(* pmul atoms are merged in two rounds (MERGE_2BLK_TAC, MERGE_ANY_TAC,       *)
(* AUTO_MERGE_MIDS_KM_TAC) with the midacc expansion between them            *)
(* (MIDACC_EXPAND_TAC); the reduction-constant products are put back in      *)
(* shift form (EXPAND_WPMUL_ATOMS_TAC, PMUL_W_64_128), the remaining data    *)
(* pmuls are merged once more, and XOR_LANE_CLOSE_TAC closes the             *)
(* GF(2)-linear rest lane by lane.                                           *)
let WB3_GMULT3_BRIDGE_TAC : tactic =
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
  MIDACC_EXPAND_TAC THEN
  ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
  AUTO_MERGE_MIDS_KM_TAC THEN
  EXPAND_WPMUL_ATOMS_TAC THEN
  REWRITE_TAC[PMUL_W_64_128] THEN REWRITE_TAC[JOINMID] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  ABBREV_INNER_PMULS_TAC THEN AUTO_MERGE_MIDS_KM_TAC THEN
  XOR_LANE_CLOSE_TAC;;

(* r = 3: s203 eor3 (block-0 plaintext), s204-s243 the cascade to the taken *)
(* b.gt at 0xc84, s244-s288 the three GHASH rounds (h3, h2, h) with the     *)
(* stores at s245/s259/s284 and the block-1/2 plaintext eor3s at s257/s271, *)
(* Q18 (the mid accumulator) named midacc at s288, s289-s296 the reduction, *)
(* s297/s298 ext/rev64, s299 tag store, s300/s301 the ivec write-back.      *)
let WB_TAIL_3_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AES128_GCM_DEC_ALT_EXEC (200--203) THEN
  WB_PT_CAPTURE_TAC "s203" `Q12` `cph0:int128` `ctr0:int128` THEN
  ARM_STEPS_RESOLVE_Q30_TAC AES128_GCM_DEC_ALT_EXEC (204--243) THEN
  ARM_STEPS_FOLD_Q18LATEST_TAC AES128_GCM_DEC_ALT_EXEC (244--257) THEN
  WB_PT_CAPTURE_TAC "s257" `Q12` `cph1:int128` `gcm_ctr_inc ctr0:int128` THEN
  ARM_STEPS_FOLD_Q18LATEST_TAC AES128_GCM_DEC_ALT_EXEC (258--271) THEN
  WB_PT_CAPTURE_TAC "s271" `Q12` `cph2:int128` `gcm_ctr_inc (gcm_ctr_inc ctr0):int128` THEN
  ARM_STEPS_FOLD_Q18LATEST_TAC AES128_GCM_DEC_ALT_EXEC (272--288) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s288` THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AES128_GCM_DEC_ALT_EXEC (289--296) THEN
  (* the GHASH bridge at s296 (pc+3688, after eor3 v19,v19,v18,v17) *)
  WB_REPLACE_READ_TAC `read Q19 (s296:armstate)` WB3_GMULT3_BRIDGE_TAC
    `ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]` THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]` THEN
  (* 297 ext (half-swap), 298 rev64 -> Q19 = word_bytereverse gval *)
  ARM_VSTEPS_FOLD_TAC AES128_GCM_DEC_ALT_EXEC (297--298) THEN
  WB_REPLACE_READ_TAC `read Q19 (s298:armstate)` (CONV_TAC WORD_BLAST)
    `word_bytereverse (gval:int128)` THEN
  (* 299: st1 {v19.16b},[x3], the tag store; 300, 301: rev32 v30 and
     str q30,[x16], the ivec write-back *)
  ARM_VSTEPS_TAC AES128_GCM_DEC_ALT_EXEC [299] THEN
  ARM_VSTEPS_FOLD_TAC AES128_GCM_DEC_ALT_EXEC (300--301) THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [ivtac;
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
   REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]];;

let WB_TAIL_GEN2_3 = prove(wbn_tail_backleg_goal5_return 3,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 3 THEN WB_TAIL_3_TAC (WB_IVEC_CLOSE_TAC 3));;

(* Merge every remaining data pmul with its spec atom, in rounds until no    *)
(* pmul is left: each round normalizes the insert, subword and join operands *)
(* (WB_MID_FIX), then abbreviates and merges the innermost pmuls             *)
(* (AUTO_MERGE_MIDS_KM_TAC), so that a pmul nested in the operand of another *)
(* is merged in a later round.                                               *)
let MERGE_ALL_PMULS_TAC : tactic =
  let is_pmul_app t = try let (h,args) = strip_comb t in
        fst(dest_const h) = "word_pmul" && length args = 2 with _ -> false in
  REPEAT (W(fun (_,w) ->
    if can (find_term is_pmul_app) w
    then REWRITE_TAC WB_MID_FIX THEN ABBREV_INNER_PMULS_TAC THEN AUTO_MERGE_MIDS_KM_TAC
    else NO_TAC));;

(* The N-block GHASH bridge (N >= 3), WB3_GMULT3_BRIDGE_TAC generalized:     *)
(* gmultn (GMULTn_FULL_CORRECT_BA) is instantiated at the block pairing of   *)
(* the tail (block 0 with the tag folded in, times H^N, and block i times    *)
(* H^(N-i)), spec_to_bf (spec_to_byteform_wbN) is given the h2 .. hN facts,  *)
(* and the last merge round is MERGE_ALL_PMULS_TAC.                          *)
let WBN_GMULT_BRIDGE_TAC n gmultn spec_to_bf : tactic =
  (fun (asl,w) ->
     let cph i = mk_comb(`word_bytereverse:int128->int128`,
                         mk_var("cph"^string_of_int i,`:int128`)) in
     let hb j = if j = 1 then `byteswap128 h:int128`
                else mk_comb(`byteswap128:int128->int128`, mk_var("h"^string_of_int j,`:int128`)) in
     let a0 = mk_comb(mk_comb(`word_xor:int128->int128->int128`, `word_bytereverse xi:int128`), cph 0) in
     let args = [a0; hb n] @ List.concat (map (fun i -> [cph i; hb (n-i)]) (1--(n-1))) in
     let gmult_dec = REWRITE_RULE[LET_DEF;LET_END_DEF] (SPECL args gmultn) in
     let hasm j = snd(List.find(fun(_,th)->try lhs(concl th) = hb j with _->false) asl) in
     let hyps = end_itlist CONJ (map hasm (2--n)) in
     (GEN_REWRITE_TAC RAND_CONV [TRANS (MP spec_to_bf hyps) (GSYM gmult_dec)]) (asl,w)) THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
  REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
  REWRITE_TAC[karatsuba_mid] THEN
  ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
  MIDACC_EXPAND_TAC THEN
  ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
  AUTO_MERGE_MIDS_KM_TAC THEN
  EXPAND_WPMUL_ATOMS_TAC THEN
  REWRITE_TAC[PMUL_W_64_128] THEN REWRITE_TAC[JOINMID] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  MERGE_ALL_PMULS_TAC THEN
  XOR_LANE_CLOSE_TAC;;

(* The tail of residue n (used for n = 4..8) from the seam s199, driven by   *)
(* its step map: `taken` is the taken b.gt (for n = 8 the first one, into    *)
(* the exact-8 drain), `pts` the (state, block) pairs of the plaintext eor3s *)
(* after the one of block 0 at s203, `ex` the exit state; the reduction is   *)
(* the 8 steps ex-12 .. ex-5 (0xe48 .. 0xe64), and the mid accumulator is    *)
(* named at ex-13.                                                           *)
let WB_TAIL_N_TAC n taken pts ex bridge ivtac =
  let sn k = "s"^string_of_int k in
  let rd q k = list_mk_icomb "read" [q; mk_var(sn k,`:armstate`)] in
  let cphv j = mk_var("cph"^string_of_int j,`:int128`) in
  let rec seg from caps = match caps with
    | [] -> ARM_STEPS_FOLD_Q18LATEST_TAC AES128_GCM_DEC_ALT_EXEC (from--(ex-13))
    | (s,j)::rest ->
        ARM_STEPS_FOLD_Q18LATEST_TAC AES128_GCM_DEC_ALT_EXEC (from--s) THEN
        WB_PT_CAPTURE_TAC (sn s) `Q12` (cphv j) (mk_ctr j) THEN seg (s+1) rest in
  let glist = mk_flist(map (fun j -> mk_comb(`word_bytereverse:int128->int128`, cphv j)) (0--(n-1))) in
  let gtm = subst [glist,`lll:int128 list`]
    `ghash_polyval_acc (byteswap128 h) (word_bytereverse xi) (lll:int128 list)` in
  ARM_STEPS_RESOLVE_TAC AES128_GCM_DEC_ALT_EXEC (200--203) THEN
  WB_PT_CAPTURE_TAC "s203" `Q12` `cph0:int128` `ctr0:int128` THEN
  ARM_STEPS_RESOLVE_Q30_TAC AES128_GCM_DEC_ALT_EXEC (204--taken) THEN
  seg (taken+1) pts THEN
  ABBREV_TAC (mk_eq(`midacc:int128`, rd `Q18` (ex-13))) THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AES128_GCM_DEC_ALT_EXEC ((ex-12)--(ex-5)) THEN
  WB_REPLACE_READ_TAC (rd `Q19` (ex-5)) bridge gtm THEN
  ABBREV_TAC (mk_eq(`gval:int128`, gtm)) THEN
  ARM_VSTEPS_FOLD_TAC AES128_GCM_DEC_ALT_EXEC ((ex-4)--(ex-3)) THEN
  WB_REPLACE_READ_TAC (rd `Q19` (ex-3)) (CONV_TAC WORD_BLAST) `word_bytereverse (gval:int128)` THEN
  ARM_VSTEPS_TAC AES128_GCM_DEC_ALT_EXEC [ex-2] THEN
  ARM_VSTEPS_FOLD_TAC AES128_GCM_DEC_ALT_EXEC ((ex-1)--ex) THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [ivtac;
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
   REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]];;

let WB_TAIL_GEN2_4 = prove(wbn_tail_backleg_goal5_return 4,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 4 THEN
  WB_TAIL_N_TAC 4 237 [250,1; 268,2; 282,3] 312
    (WBN_GMULT_BRIDGE_TAC 4 GMULT4_FULL_CORRECT_BA spec_to_byteform_wb4)
    (WB_IVEC_CLOSE_TAC 4));;

(* r = 4..8 through WB_TAIL_N_TAC (r = 4 just above), from their step maps   *)
(* (states numbered from the seam s199): the taken b.gt of the cascade, the  *)
(* plaintext eor3s of blocks 1..r-1 and the exit state (after the ivec store *)
(* at 0xe78):                                                                *)
(*   r = 4: b.gt s237 (0xc6c); eor3 s250 s268 s282; exit s312.               *)
(*   r = 5: b.gt s231 (0xc54); eor3 s242 s258 s276 s290; exit s320.          *)
(*   r = 6: b.gt s224 (0xc38); eor3 s230 s250 s266 s284 s298; exit s328.     *)
(*   r = 7: b.gt s216 (0xc18); eor3 s230 s236 s256 s272 s290 s304;           *)
(*          exit s334.                                                       *)
(*   r = 8: b.gt s204 (0xbe8, into the drain); eor3 s214 s224 s229 s245      *)
(*          s257 s271 s282; exit s312.                                       *)
let WB_TAIL_GEN2_5 = prove(wbn_tail_backleg_goal5_return 5,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 5 THEN
  WB_TAIL_N_TAC 5 231 [242,1; 258,2; 276,3; 290,4] 320
    (WBN_GMULT_BRIDGE_TAC 5 GMULT5_FULL_CORRECT_BA spec_to_byteform_wb5)
    (WB_IVEC_CLOSE_TAC 5));;

let AES128_GCM_DEC_ALT_BUF_5BLOCK = prove_band 5 WB_TAIL_GEN2_5;;

let WB_TAIL_GEN2_6 = prove(wbn_tail_backleg_goal5_return 6,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 6 THEN
  WB_TAIL_N_TAC 6 224 [230,1; 250,2; 266,3; 284,4; 298,5] 328
    (WBN_GMULT_BRIDGE_TAC 6 GMULT6_FULL_CORRECT_BA spec_to_byteform_wb6)
    (WB_IVEC_CLOSE_TAC 6));;

let AES128_GCM_DEC_ALT_BUF_6BLOCK = prove_band 6 WB_TAIL_GEN2_6;;

let WB_TAIL_GEN2_7 = prove(wbn_tail_backleg_goal5_return 7,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 7 THEN
  WB_TAIL_N_TAC 7 216 [230,1; 236,2; 256,3; 272,4; 290,5; 304,6] 334
    (WBN_GMULT_BRIDGE_TAC 7 GMULT7_FULL_CORRECT_BA spec_to_byteform_wb7)
    (WB_IVEC_CLOSE_TAC 7));;

let AES128_GCM_DEC_ALT_BUF_7BLOCK = prove_band 7 WB_TAIL_GEN2_7;;

(* r = 8 takes the first b.gt (0xbe8) to the exact-8 drain (0xe9c), so      *)
(* there is no `sub v30`: Q30 is still gcm_ctr_raw (word 8) ctr0 at the     *)
(* ivec write-back, and WB_IVEC_CLOSE_TAC 8's sub_chain rewrites would be   *)
(* the looping x = word_sub x (word 0).  The same close without them.       *)
(* That path also skips the movi zeroing of v17/v18/v19; its                *)
(* `ext v18.16b,v24.16b,v24.16b,#8` (s207) overwrites the seam's            *)
(* unconstrained Q18 whole, and the pmull at s215 reads only its lane 0.    *)
(* The drain (s205-s297) feeds the partial tag into its first block only,   *)
(* defers three blocks' products to v13-v15 and folds each into the next    *)
(* block's accumulations with eor3, and rejoins the cascade at reduce       *)
(* (0xe40) by the `b` at s297.  The 8-block GHASH bridge closes it          *)
(* unchanged, the reordering being GF(2)-linear.                            *)
let WB_IVEC_CLOSE8_TAC =
  REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD] THEN
  REWRITE_TAC[gcm_ctr_raw_def; SUBW_RAW_96; SUBW_RAW_64; SUBW_RAW_32; SUBW_RAW_0] THEN
  GEN_REWRITE_TAC RAND_CONV [GCM_CTR_ADD_LANES] THEN
  W(fun (_,gw) ->
     let atom = find_term (fun t -> match t with
       | Comb(Comb(Const("word_add",_),_),Comb(Const("word",_),_)) -> true | _ -> false) gw in
     SPEC_TAC(atom, `aa:32 word`)) THEN
  GEN_TAC THEN CONV_TAC WORD_BLAST;;

let WB_TAIL_GEN2_8 = prove(wbn_tail_backleg_goal5_return 8,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 8 THEN
  WB_TAIL_N_TAC 8 204 [214,1; 224,2; 229,3; 245,4; 257,5; 271,6; 282,7] 312
    (WBN_GMULT_BRIDGE_TAC 8 GMULT8_FULL_CORRECT_BA spec_to_byteform_wb8)
    WB_IVEC_CLOSE8_TAC);;

let AES128_GCM_DEC_ALT_BUF_8BLOCK = prove_band 8 WB_TAIL_GEN2_8;;

let GCM_SIMD_SIMPLIFY_CORE_QSCOPED_TAC =
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
    else if Hashtbl.mem gcm_simd_fixpt_tbl c then th
    else let th' = apply_F th in
         (if concl th' = c then Hashtbl.add gcm_simd_fixpt_tbl c ());
         th');;

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

(* The finisher of every bridge, BRIDGE_CLOSE_1_TAC's too: unify the         *)
(* reduction's W-products on the two sides (WA_UNIFY_TAC, WV_UNIFY_TAC),     *)
(* then split the 128-bit equality into its 64-bit lanes and close each      *)
(* (LANE_FINISH_TAC).                                                        *)
let BRIDGE_FINISH_TAC : tactic =
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  WA_UNIFY_TAC THEN WV_UNIFY_TAC THEN ABBREV_WAWV_TAC THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_TAC;;

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
   BRIDGE_FINISH_TAC)
  (asl,w);;

(* ---- nblk = 1 ---- *)

(* The k = 1 bridge lemmas.  By GHASH_1BLOCK_CORRECT the tag after one block is
   polyval_dot (xi XOR cph) H; the machine instead multiplies the seed Xi' and
   the block by H separately and XORs the products.  FOLD_LANE (either 64-bit
   lane) folds such a pair of 64-bit products into the product of the XOR, and
   FOLD_MID2 does the same for the two middle products. *)
let FOLD_LANE = prove(
  `!i. word_xor (word_pmul (word_reversefields 8 (word_subword (cph:int128) (i,64):64 word))
                         (word_subword (h:int128) (i,64):64 word))
              (word_pmul (word_reversefields 8 (word_subword (xi:int128) (i,64):64 word))
                         (word_subword h (i,64):64 word)) : int128
     = word_pmul (word_subword h (i,64):64 word)
         (word_xor (word_reversefields 8 (word_subword xi (i,64):64 word))
                   (word_reversefields 8 (word_subword cph (i,64):64 word)))`,
  GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [CONJUNCT2 WORD_PMUL_XOR] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  REWRITE_TAC[WORD_XOR_ACI]);;

(* BRIDGE_CLOSE_1_TAC sN: the nblk = 1 bridge at the reduce state sN.
   GMULT_FULL_CORRECT_BA states the one-block tag of GHASH_1BLOCK_CORRECT in
   the byte form of the machine; where the k >= 2 bridges distribute the
   products of the spec (the qq triples of DEC_BRIDGE_ROUTEB_TAC), here the
   products of the seed and of the block fold pairwise into those of the spec,
   by FOLD_LANE in the rewrite and FOLD_MID2 on the abbreviated middle terms.
   The close is BRIDGE_FINISH_TAC, as for k >= 2. *)
let BRIDGE_CLOSE_1_TAC sN : tactic = fun (asl,w) ->
  let q19asm = snd(List.find(fun(_,th)->
    try lhs(concl th)=parse_term(Printf.sprintf "read Q19 s%d" sN) with _->false) asl) in
  let spec_eq = TRANS
    (GSYM(ISPECL [`word_bytereverse xi:int128`; `word_bytereverse cph:int128`;
                  `byteswap128 h:int128`] GHASH_1BLOCK_CORRECT))
    (GSYM(REWRITE_RULE[LET_DEF; LET_END_DEF]
       (ISPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph):int128`;
                `byteswap128 h:int128`] GMULT_FULL_CORRECT_BA))) in
  (GEN_REWRITE_TAC LAND_CONV [q19asm] THEN
   GEN_REWRITE_TAC RAND_CONV [spec_eq] THEN
   REWRITE_TAC[byteswap128; WORD_BYTEREVERSE_REVERSEFIELDS; WORD_INSERT_SUBWORD;
               WORD_SUBWORD_SUBWORD; SUBWORD_XOR_JOIN_DIST; JOIN_SUBWORD_RULES;
               RF8_SUBWORD] THEN
   REWRITE_TAC[GSYM (CONJUNCT1 SUBWORD_XOR_JOIN_DIST); GSYM (CONJUNCT2 SUBWORD_XOR_JOIN_DIST);
               FOLD_LANE] THEN
   ABBREV_INNER_PMULS_TAC THEN
   SUBGOAL_THEN `word_xor (qq4:int128) qq3 = qq2` (fun th -> REWRITE_TAC[th]) THENL
    [MAP_EVERY EXPAND_TAC ["qq2";"qq3";"qq4"] THEN ACCEPT_TAC FOLD_MID2; ALL_TAC] THEN
   BRIDGE_FINISH_TAC) (asl,w);;

(* The goal of WB_FUSED_1BLOCK, nblk = 1: 87 steps from the core entry pc+0x1c
   to the core exit pc+3708.  s1-s8 the front and the dispatch (the b.le at s8
   is taken), s9-s27 L128_dec_small (the counter, tag and round-key loads and
   the x9 compares), s28-s35 L128_dec_small_seed_1 (the seed Xi' * H), s36-s86
   L128_dec_small_blk_1 (the AES-128 tower, the reduced GHASH at s78, the tag
   store at s81, the counter store at s84, the plaintext eor3 at s85 and its
   store at s86), s87 the b at L128_dec_small_done. *)
let fused1_goal =
 `!pc stackpointer out_p tag_p ivec_p in_p key_p htable_p
    cph xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 h hk.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (out_p:int64, 16) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (tag_p:int64, 16) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 16) (tag_p, 16) /\
    nonoverlapping (out_p, 16) (ivec_p, 16) /\
    nonoverlapping (tag_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 16) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 176) /\
    nonoverlapping (ivec_p, 16) (htable_p:int64, 192) /\
    nonoverlapping (in_p, 16) (stackpointer, 80) /\
    nonoverlapping (key_p, 176) (stackpointer, 80) /\
    nonoverlapping (htable_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (tag_p, 16) (in_p, 16) /\
    nonoverlapping (tag_p, 16) (key_p, 176) /\
    nonoverlapping (tag_p, 16) (htable_p, 192) /\
    nonoverlapping (tag_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 16) (in_p, 16) /\
    nonoverlapping (out_p, 16) (key_p, 176) /\
    nonoverlapping (out_p, 16) (htable_p, 192) /\
    nonoverlapping (out_p, 16) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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
          read (memory :> bytes128 htable_p) s = h /\
          read (memory :> bytes128 (word_add htable_p (word 16))) s = hk)
     (\s. read PC s = word (pc + 3708) /\
          read X9 s = word 16 /\
          read (memory :> bytes128 out_p) s =
          word_xor cph (aes128_encrypt ctr0 [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]) /\
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
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`;;

let WB_FUSED_1BLOCK = prove(fused1_goal,
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              WB_MC_LEN] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN CLEAR_KEEPGHALL_MEMO_TAC THEN
  (* the 64-bit halves of the 128-bit reads, for the ldr d25 of hk *)
  MEMORY_SPLIT_TAC 1 THEN
  (* The windows: the front, L128_dec_small and L128_dec_small_seed_1 (s1-s35),
     then L128_dec_small_blk_1 up to the reduce (s36-s78).  Each ends with the
     accumulator registers made self-contained, so that the older states can be
     discarded.  The plaintext store needs no cut-point: the close proves the
     block at s87. *)
  MAP_EVERY (fun (a,b) -> let st = "s" ^ string_of_int b in
      ARM_STEPS_FOLD_KEEPGHALL_TAC AES128_GCM_DEC_ALT_EXEC (a--b) THEN
      INLINE_SELFCONTAINED "Q17" st 40 THEN INLINE_SELFCONTAINED "Q18" st 40 THEN
      INLINE_SELFCONTAINED "Q19" st 40 THEN DISCARD_OLDSTATE_TAC st)
    [1,35; 36,78] THEN
  SUBGOAL_THEN
    `read Q19 (s78:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi) [word_bytereverse cph]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s78` with _ -> false) then th else asm)) THENL
   [BRIDGE_CLOSE_1_TAC 78; ALL_TAC] THEN
  ARM_STEPS_FOLD_DISCARD_TAC AES128_GCM_DEC_ALT_EXEC (79--87) THEN
  (* The rev64/ext of the reduced accumulator (s79-s80) makes the tag store  *)
  (* its word_bytereverse by Q19_BREVXI, and the kernel's counter lanes fold *)
  (* back to gcm_ctr_inc ctr0.  With the write-back's gcm_ctr_inc_iter 1 and *)
  (* the AES-128 tower unfolded too, what is left of the plaintext block and *)
  (* the counter write-back is word algebra.                                 *)
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[Q19_BREVXI; JOIN_IS_CTR0; GSYM GCM_CTR_INC_LANES;
                  num_CONV `1`; gcm_ctr_inc_iter;
                  GSYM AES128_XOR_ENCRYPT_RECONSTRUCT; aes9] THEN
  CONV_TAC WORD_RULE);;

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

(* The goal of WB_FUSED_2BLOCK, nblk = 2: 123 steps.  s1-s8 the front and the
   dispatch, s9-s28 L128_dec_small, s29-s36 L128_dec_small_seed_2 (the seed Xi'
   * H^2), s37-s71 small_blk_2 (block 0, folded with H^2, stored at s71),
   s72-s122 small_blk_1 (block 1, the reduce at s114, then the tag, counter and
   block-1 stores) and s123 the b at L128_dec_small_done. *)
let fused2_goal =
 `!pc stackpointer out_p tag_p ivec_p in_p key_p htable_p
    cph0 cph1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 h hk h2.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (out_p:int64, 32) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (tag_p:int64, 16) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 32) (tag_p, 16) /\
    nonoverlapping (out_p, 32) (ivec_p, 16) /\
    nonoverlapping (tag_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 32) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 176) /\
    nonoverlapping (ivec_p, 16) (htable_p:int64, 192) /\
    nonoverlapping (in_p, 32) (stackpointer, 80) /\
    nonoverlapping (key_p, 176) (stackpointer, 80) /\
    nonoverlapping (htable_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (tag_p, 16) (in_p, 32) /\
    nonoverlapping (tag_p, 16) (key_p, 176) /\
    nonoverlapping (tag_p, 16) (htable_p, 192) /\
    nonoverlapping (tag_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 32) (in_p, 32) /\
    nonoverlapping (out_p, 32) (key_p, 176) /\
    nonoverlapping (out_p, 32) (htable_p, 192) /\
    nonoverlapping (out_p, 32) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word) /\
    word_subword hk (64,64) :64 word =
      word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64):64 word) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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
          read (memory :> bytes128 htable_p) s = h /\
          read (memory :> bytes128 (word_add htable_p (word 16))) s = hk /\
          read (memory :> bytes128 (word_add htable_p (word 32))) s = h2)
     (\s. read PC s = word (pc + 3708) /\
          read X9 s = word 32 /\
          read (memory :> bytes128 out_p) s =
          word_xor cph0 (aes128_encrypt ctr0 [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]) /\
          read (memory :> bytes128 (word_add out_p (word 16))) s =
          word_xor cph1 (aes128_encrypt (gcm_ctr_inc ctr0) [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]) /\
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
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`;;

let WB_FUSED_2BLOCK = prove(fused2_goal,
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              WB_MC_LEN] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN CLEAR_KEEPGHALL_MEMO_TAC THEN
  (* the 64-bit halves of the 128-bit reads, for the ldr d25 of hk *)
  MEMORY_SPLIT_TAC 1 THEN
  (* The windows: the front, L128_dec_small and L128_dec_small_seed_2 (s1-s36),
     then small_blk_2 (s37-s71) and small_blk_1 up to the reduce (s72-s114).
     Each ends with the accumulator registers made self-contained, so that the
     older states can be discarded.  The plaintext stores need no cut-point:
     the close proves both blocks at s123. *)
  MAP_EVERY (fun (a,b) -> let st = "s" ^ string_of_int b in
      ARM_STEPS_FOLD_KEEPGHALL_TAC AES128_GCM_DEC_ALT_EXEC (a--b) THEN
      INLINE_SELFCONTAINED "Q17" st 40 THEN INLINE_SELFCONTAINED "Q18" st 40 THEN
      INLINE_SELFCONTAINED "Q19" st 40 THEN DISCARD_OLDSTATE_TAC st)
    [1,36; 37,71; 72,114] THEN
  SUBGOAL_THEN
    `read Q19 (s114:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s114` with _ -> false) then th else asm)) THENL
   [BRIDGE_CLOSE_2_CPH1_TAC 114; ALL_TAC] THEN
  ARM_STEPS_FOLD_DISCARD_TAC AES128_GCM_DEC_ALT_EXEC (115--123) THEN
  (* The rev64/ext of the reduced accumulator (s115-s116) makes the tag      *)
  (* store its word_bytereverse by Q19_BREVXI, and the kernel's counter      *)
  (* lanes fold back to gcm_ctr_inc^j ctr0.  With the write-back's           *)
  (* gcm_ctr_inc_iter 2 and the AES-128 towers unfolded too, what is left of *)
  (* the two plaintext blocks and the counter write-back is word algebra.    *)
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[Q19_BREVXI; JOIN_IS_CTR0; GSYM GCM_CTR_INC_LANES; GSYM GCM_CTR_INC2_LANES;
                  num_CONV `2`; num_CONV `1`; gcm_ctr_inc_iter;
                  GSYM AES128_XOR_ENCRYPT_RECONSTRUCT; aes9] THEN
  CONV_TAC WORD_RULE);;

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

(* The goal of WB_FUSED_3BLOCK, nblk = 3: 157 steps.  s1-s8 the front and the
   dispatch, s9-s27 L128_dec_small and L128_dec_small_ge3, s28-s35
   L128_dec_small_seed_3 (the seed Xi' * H^3), s36-s70 small_blk_3 (block 0,
   stored at s70), s71-s105 small_blk_2 (block 1, stored at s105), s106-s156
   small_blk_1 (block 2, the reduce at s148, then the tag, counter and block-2
   stores) and s157 the b at L128_dec_small_done. *)
let fused3_goal =
 `!pc stackpointer out_p tag_p ivec_p in_p key_p htable_p
    cph0 cph1 cph2 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 h hk h2 h3 h3k.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (out_p:int64, 48) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (tag_p:int64, 16) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 48) (tag_p, 16) /\
    nonoverlapping (out_p, 48) (ivec_p, 16) /\
    nonoverlapping (tag_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 48) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 176) /\
    nonoverlapping (ivec_p, 16) (htable_p:int64, 192) /\
    nonoverlapping (in_p, 48) (stackpointer, 80) /\
    nonoverlapping (key_p, 176) (stackpointer, 80) /\
    nonoverlapping (htable_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (tag_p, 16) (in_p, 48) /\
    nonoverlapping (tag_p, 16) (key_p, 176) /\
    nonoverlapping (tag_p, 16) (htable_p, 192) /\
    nonoverlapping (tag_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 48) (in_p, 48) /\
    nonoverlapping (out_p, 48) (key_p, 176) /\
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
     (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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
          read (memory :> bytes128 htable_p) s = h /\
          read (memory :> bytes128 (word_add htable_p (word 16))) s = hk /\
          read (memory :> bytes128 (word_add htable_p (word 32))) s = h2 /\
          read (memory :> bytes128 (word_add htable_p (word 48))) s = h3 /\
          read (memory :> bytes128 (word_add htable_p (word 64))) s = h3k)
     (\s. read PC s = word (pc + 3708) /\
          read X9 s = word 48 /\
          read (memory :> bytes128 out_p) s =
          word_xor cph0 (aes128_encrypt ctr0
            [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]) /\
          read (memory :> bytes128 (word_add out_p (word 16))) s =
          word_xor cph1 (aes128_encrypt (gcm_ctr_inc ctr0)
            [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]) /\
          read (memory :> bytes128 (word_add out_p (word 32))) s =
          word_xor cph2 (aes128_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0))
            [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]) /\
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
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`;;

let WB_FUSED_3BLOCK = prove(fused3_goal,
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              WB_MC_LEN] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN CLEAR_KEEPGHALL_MEMO_TAC THEN
  (* the 64-bit halves of the 128-bit reads, for the ldr d25 of hk and h3k *)
  MEMORY_SPLIT_TAC 1 THEN
  (* The windows: the front, L128_dec_small, L128_dec_small_ge3 and
     L128_dec_small_seed_3 (s1-s35), then small_blk_3 (s36-s70), small_blk_2
     (s71-s105) and small_blk_1 up to the reduce (s106-s148).  Each ends with
     the accumulator registers made self-contained, so that the older states
     can be discarded.  The plaintext stores need no cut-point: the close
     proves all three blocks at s157. *)
  MAP_EVERY (fun (a,b) -> let st = "s" ^ string_of_int b in
      ARM_STEPS_FOLD_KEEPGHALL_TAC AES128_GCM_DEC_ALT_EXEC (a--b) THEN
      INLINE_SELFCONTAINED "Q17" st 40 THEN INLINE_SELFCONTAINED "Q18" st 40 THEN
      INLINE_SELFCONTAINED "Q19" st 40 THEN DISCARD_OLDSTATE_TAC st)
    [1,35; 36,70; 71,105; 106,148] THEN
  SUBGOAL_THEN
    `read Q19 (s148:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s148` with _ -> false) then th else asm)) THENL
   [BRIDGE_CLOSE_3_CPH2_TAC 148; ALL_TAC] THEN
  ARM_STEPS_FOLD_DISCARD_TAC AES128_GCM_DEC_ALT_EXEC (149--157) THEN
  (* The rev64/ext of the reduced accumulator (s149-s150) makes the tag      *)
  (* store its word_bytereverse by Q19_BREVXI, and the kernel's counter      *)
  (* lanes fold back to gcm_ctr_inc^j ctr0.  With the write-back's           *)
  (* gcm_ctr_inc_iter 3 and the AES-128 towers unfolded too, what is left of *)
  (* the three plaintext blocks and the counter write-back is word algebra.  *)
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[Q19_BREVXI; JOIN_IS_CTR0; GSYM GCM_CTR_INC_LANES; GSYM GCM_CTR_INC2_LANES;
                  GSYM GCM_CTR_INC3_LANES; num_CONV `3`; num_CONV `2`; num_CONV `1`;
                  gcm_ctr_inc_iter; GSYM AES128_XOR_ENCRYPT_RECONSTRUCT; aes9] THEN
  CONV_TAC WORD_RULE);;

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

(* The goal of WB_FUSED_4BLOCK, nblk = 4: 193 steps.  s1-s8 the front and the
   dispatch, s9-s28 L128_dec_small and L128_dec_small_ge3, s29-s36
   L128_dec_small_seed_4 (the seed Xi' * H^4), s37-s71 small_blk_4, s72-s106
   small_blk_3 and s107-s141 small_blk_2 (blocks 0..2, stored at s71, s106 and
   s141), s142-s192 small_blk_1 (block 3, the reduce at s184, then the tag,
   counter and block-3 stores) and s193 the b at L128_dec_small_done. *)
let fused4_goal =
 `!pc stackpointer out_p tag_p ivec_p in_p key_p htable_p
    cph0 cph1 cph2 cph3 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 h hk h2 h3 h3k h4.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (out_p:int64, 64) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (tag_p:int64, 16) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 64) (tag_p, 16) /\
    nonoverlapping (out_p, 64) (ivec_p, 16) /\
    nonoverlapping (tag_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 64) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 176) /\
    nonoverlapping (ivec_p, 16) (htable_p:int64, 192) /\
    nonoverlapping (in_p, 64) (stackpointer, 80) /\
    nonoverlapping (key_p, 176) (stackpointer, 80) /\
    nonoverlapping (htable_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (tag_p, 16) (in_p, 64) /\
    nonoverlapping (tag_p, 16) (key_p, 176) /\
    nonoverlapping (tag_p, 16) (htable_p, 192) /\
    nonoverlapping (tag_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 64) (in_p, 64) /\
    nonoverlapping (out_p, 64) (key_p, 176) /\
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
     (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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
          read (memory :> bytes128 htable_p) s = h /\
          read (memory :> bytes128 (word_add htable_p (word 16))) s = hk /\
          read (memory :> bytes128 (word_add htable_p (word 32))) s = h2 /\
          read (memory :> bytes128 (word_add htable_p (word 48))) s = h3 /\
          read (memory :> bytes128 (word_add htable_p (word 64))) s = h3k /\
          read (memory :> bytes128 (word_add htable_p (word 80))) s = h4)
     (\s. read PC s = word (pc + 3708) /\
          read X9 s = word 64 /\
          read (memory :> bytes128 out_p) s =
          word_xor cph0 (aes128_encrypt ctr0
            [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]) /\
          read (memory :> bytes128 (word_add out_p (word 16))) s =
          word_xor cph1 (aes128_encrypt (gcm_ctr_inc ctr0)
            [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]) /\
          read (memory :> bytes128 (word_add out_p (word 32))) s =
          word_xor cph2 (aes128_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0))
            [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]) /\
          read (memory :> bytes128 (word_add out_p (word 48))) s =
          word_xor cph3 (aes128_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))
            [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]) /\
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
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`;;

let WB_FUSED_4BLOCK = prove(fused4_goal,
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              WB_MC_LEN] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN CLEAR_KEEPGHALL_MEMO_TAC THEN
  (* the 64-bit halves of the Karatsuba table entries hk and h3k *)
  MAP_EVERY (fun v -> FIRST_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 1) o
    check (fun th -> rand(concl th) = v))) [`hk:int128`; `h3k:int128`] THEN
  ARM_STEPS_TAC AES128_GCM_DEC_ALT_EXEC (1--36) THEN
  (* After plain steps 1..36 (the front, L128_dec_small, L128_dec_small_ge3 and
     L128_dec_small_seed_4), the windows small_blk_4 (s37-s71), small_blk_3,
     small_blk_2 and small_blk_1 up to the reduce (s142-s184): each ends with
     the accumulator registers made self-contained, so that the older states
     can be discarded.  The plaintext stores need no cut-point: the close
     proves all four blocks at s193. *)
  MAP_EVERY (fun (a,b) -> let st = "s" ^ string_of_int b in
      ARM_STEPS_FOLD_KEEPGHALL_TAC AES128_GCM_DEC_ALT_EXEC (a--b) THEN
      INLINE_SELFCONTAINED "Q17" st 40 THEN INLINE_SELFCONTAINED "Q18" st 40 THEN
      INLINE_SELFCONTAINED "Q19" st 40 THEN DISCARD_OLDSTATE_TAC st)
    [37,71; 72,106; 107,141; 142,184] THEN
  SUBGOAL_THEN
    `read Q19 (s184:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s184` with _ -> false) then th else asm)) THENL
   [BRIDGE_CLOSE_4_CPH3_TAC 184; ALL_TAC] THEN
  ARM_STEPS_FOLD_DISCARD_TAC AES128_GCM_DEC_ALT_EXEC (185--193) THEN
  (* The rev64/ext of the reduced accumulator (s185-s186) makes the tag      *)
  (* store its word_bytereverse by Q19_BREVXI, and the kernel's counter      *)
  (* lanes fold back to gcm_ctr_inc^j ctr0.  Left after the rewrite: the     *)
  (* four plaintext blocks and the counter write-back; unfold the            *)
  (* write-back's gcm_ctr_inc_iter 4 and the AES-128 towers.                 *)
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[Q19_BREVXI; JOIN_IS_CTR0; GSYM GCM_CTR_INC_LANES; GSYM GCM_CTR_INC2_LANES;
                  GSYM GCM_CTR_INC3_LANES; GSYM GCM_CTR_INC4_LANES] THEN
  REPEAT CONJ_TAC THEN
  REWRITE_TAC[num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; gcm_ctr_inc_iter;
              GSYM AES128_XOR_ENCRYPT_RECONSTRUCT; aes9] THEN
  CONV_TAC WORD_RULE);;

let s42_key_args = [`xi:int128`;`ctr0:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;
                `k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`h:int128`];;
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
    MP_TAC(SPECL [nk; `in_p:int64`; `ibytes:byte list`; `x:armstate`] INPUT_BYTES_TO_BYTE128_LANES) THEN
    REWRITE_TAC[ARITH_RULE(mk_eq(mk_binop `( * ):num->num->num` `16` nk, mk_small_numeral(16*k)))] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
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
      s42_lane_discharge k;
      MP_TAC fused_inst THEN ANTS_TAC THENL
       [REWRITE_TAC[GSYM WB_MC_LEN] THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[HK_LOW_IS_KARA; HK_HI_IS_KARA; karatsuba_mid] THEN
        REWRITE_TAC[BYTESWAP128_INVOLUTION];
        DISCH_THEN ACCEPT_TAC]]);;

(* Bands 1..4 take the small-message path, so they come from WB_FUSED_kBLOCK by
   mk_band_from_fused; prove_band, which takes the front through WB_FRONT_BUF,
   needs 5 <= nblk (bands 5..8 are proved above, after their back-legs). *)
let AES128_GCM_DEC_ALT_BUF_1BLOCK = mk_band_from_fused 1 WB_FUSED_1BLOCK;;
let AES128_GCM_DEC_ALT_BUF_2BLOCK = mk_band_from_fused 2 WB_FUSED_2BLOCK;;
let AES128_GCM_DEC_ALT_BUF_3BLOCK = mk_band_from_fused 3 WB_FUSED_3BLOCK;;
let AES128_GCM_DEC_ALT_BUF_4BLOCK = mk_band_from_fused 4 WB_FUSED_4BLOCK;;

(* ---- step 2: whole-blocks output bridge (per-block stores -> byte_list_at).
   Byte i of the output is byte i MOD 16 of block i DIV 16
   (EL_INT128_LIST_TO_BYTES), read off the bytes128 store of that block
   (BYTE8_OF_BYTES128); the input-side mirror is WBN_INPUT_ASSEMBLE below. *)
let BYTE_LIST_AT_WHOLE_CTR = prove
 (`!ctr0 pts keys out_p (len:int64) s.
    val len = 16 * LENGTH pts /\
    (!j. j < LENGTH pts
         ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
             EL j (aes128_ctr ctr0 pts keys))
    ==> byte_list_at (aes128_ctr_bytes ctr0 pts keys) out_p len s`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[byte_list_at; aes128_ctr_bytes] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`word_add out_p (word (16 * (i DIV 16))):int64`; `s:armstate`;
                `i MOD 16`] BYTE8_OF_BYTES128) THEN
  ASM_SIMP_TAC[EL_INT128_LIST_TO_BYTES; LENGTH_AES128_CTR; RDIV_LT_EQ; MOD_LT_EQ;
               ARITH_EQ; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; DIVISION_SIMP]);;

(* ---- step 3: build_aes_ctr_el k, the k elements of aes128_ctr over a k-block
   list: EL j = pt_j XOR aes128_encrypt (gcm_ctr_inc^j ctr0) keys ---- *)
let build_aes_ctr_el k =
  let pts = map (fun i -> mk_var("pt"^string_of_int i,`:int128`)) (0--(k-1)) in
  let plist = mk_flist pts in
  let rec ctr j = if j = 0 then `ctr0:int128` else mk_comb(`gcm_ctr_inc`, ctr (j-1)) in
  let conj_of j =
    mk_eq(list_mk_comb(`EL:num->(int128)list->int128`,
            [mk_small_numeral j;
             list_mk_comb(`aes128_ctr`, [`ctr0:int128`; plist; `keys:int128 list`])]),
          list_mk_comb(`word_xor:int128->int128->int128`,
            [el j pts;
             list_mk_comb(`aes128_encrypt`, [ctr j; `keys:int128 list`])])) in
  let goal = list_mk_conj (map conj_of (0--(k-1))) in
  let sucs = map (fun i -> num_CONV (mk_small_numeral i)) (1--(k-1)) in
  prove(goal,
    REWRITE_TAC[aes128_ctr; aes128_ctr_rec; aes128_ctr_output_block; gcm_ctr_inc_iter] THEN
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
   explicit GHASH of the postcondition replaced by gcm_dec128_pt_bytes and
   gcm_dec_final_xi over the whole buffer.  No simulation: the precondition
   by BYTE_LIST_AT_TO_READ_BYTES, the postcondition by BYTE_LIST_AT_WHOLE_CTR
   and the EL facts of the band; the specifications unfold by
   GCM_DEC_GHASH_BLOCKS_WHOLE_k and GCM_DEC128_PT_BYTES_WHOLE_k. *)
let wb_keys_tm = `[k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]`;;
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
    `byte_list_at (gcm_dec128_pt_bytes nnn ibytes ctr0 (kl:int128 list)) out_p (word nnn) s` in
  let xipost = subst [n16,`nnn:num`]
    `read (memory :> bytes128 tag_p) s = gcm_dec_final_xi nnn ibytes xi h` in
  (* the counter write-back conjunct of the band, unchanged *)
  let ivecpost = mk_ivec_conj k in
  let post' = mk_abs(sv, list_mk_conj [pcc; x9c; outpost; xipost; ivecpost]) in
  list_mk_forall(vars,
    mk_imp(hyps, list_mk_comb(rator(rator(rator ens)), [pre'; post'; frame])));;

let pt_wholes = [GCM_DEC128_PT_BYTES_WHOLE_1;GCM_DEC128_PT_BYTES_WHOLE_2;
                 GCM_DEC128_PT_BYTES_WHOLE_3;GCM_DEC128_PT_BYTES_WHOLE_4;
                 GCM_DEC128_PT_BYTES_WHOLE_5;GCM_DEC128_PT_BYTES_WHOLE_6;
                 GCM_DEC128_PT_BYTES_WHOLE_7;GCM_DEC128_PT_BYTES_WHOLE_8];;
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
        REWRITE_TAC[LENGTH] THEN CONV_TAC(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV) THEN
        REWRITE_TAC[jsplit] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD_0; el_facts] THEN ASM_REWRITE_TAC[el_facts];
        MATCH_MP_TAC buf_thm THEN ASM_REWRITE_TAC[]]]);;

(* ---- the readable-band prover ----
   For band k: (1) prove_wb_wrapper k buf_thm gives the internal byte-list
   wrapper over _BUF_kBLOCK; (2) mk_wrapper_nist instantiates it at
   ki := EL i rk, h := byteswap128 (ghash_twist H), xi := word_reversefields
   8 tag0 and rewrites it into the NIST vocabulary; (3) WB_READABLE_TAC
   closes the literal statement: the ALLPAIRS/PAIRWISE/ALL unfolding and
   NONOVERLAPPING_SYM match the pairwise hypotheses of the wrapper,
   RK_ETA_11 folds the EL list back to rk, and ENSURES_PRECONDITION_THM with
   KEY_READS_FROM_WORDLIST bridges the key reads. *)
let mk_wrapper_nist k wrapper_thm =
  let winst = SPECL ([`pc:num`;`stackpointer:int64`;`out_p:int64`;`tag_p:int64`;`ivec_p:int64`;
                      `in_p:int64`;`key_p:int64`;`htable_p:int64`;`ibytes:byte list`;
                      `word_reversefields 8 (tag0:int128)`;`ctr0:int128`] @
                     map (fun i -> list_mk_comb(`EL:num->(int128)list->int128`,
                            [mk_small_numeral i; `rk:int128 list`])) (0--10) @
                     [`byteswap128 (ghash_twist H)`]) wrapper_thm in
  let xi_rw = MP (SPECL [`H:int128`; `byteswap128 (ghash_twist H)`;
                         mk_small_numeral(16*k); `ibytes:byte list`;
                         `word_reversefields 8 (tag0:int128)`] GCM_DEC_FINAL_XI_NIST)
                 bsw_inv in
  REWRITE_RULE[HTABLE_MEM_DEC_IS_HTABLE_MEM_8; BYTESWAP128_INVOLUTION; xi_rw;
               GSYM (el (k-1) LIST_OF_SEQ_NIST_INPUT); BREV_RF8_INV_128; BREV_RF8_128] winst;;

let wb_rk11_tm = `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
                   EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:int128 list`;;
let WB_READABLE_TAC k buf_thm =
  let wn = mk_wrapper_nist k (prove_wb_wrapper k buf_thm) in
  REPEAT GEN_TAC THEN REWRITE_TAC[ALLPAIRS;PAIRWISE;ALL] THEN STRIP_TAC THEN
  MP_TAC wn THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(wb_rk11_tm,`rk:int128 list`)) SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RK_ETA_11 THEN ASM_REWRITE_TAC[];
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
(* XORed onto the input bytes (gcm_dec128_pt_bytes), replaces the tag at     *)
(* tag_p with the SP 800-38D GHASH of the N raw ciphertext blocks folded     *)
(* onto tag0 under the NIST hash key H (both tag values byte-reversed, as    *)
(* the AWS-LC caller keeps them), stores the counter block advanced by N at  *)
(* ivec_p (gcm_ctr_inc_iter N ctr0), and leaves the byte count 16 * N in X9. *)
(* ------------------------------------------------------------------------- *)

let AES128_GCM_DEC_ALT_1BLOCK = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 16 /\ LENGTH rk = 11 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,16; tag_p,16; ivec_p,16]
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16; key_p,176; htable_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,16; tag_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16; key_p,176; htable_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 128; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               byte_list_at ibytes in_p (word 16) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = word (pc + 3708) /\
               read X9 s = word 16 /\
               byte_list_at (gcm_dec128_pt_bytes 16 ibytes ctr0 rk) out_p (word 16) s /\
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
  WB_READABLE_TAC 1 AES128_GCM_DEC_ALT_BUF_1BLOCK);;

let AES128_GCM_DEC_ALT_2BLOCK = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 32 /\ LENGTH rk = 11 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,32; tag_p,16; ivec_p,16]
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,32; key_p,176; htable_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,32; tag_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,32; key_p,176; htable_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 256; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               byte_list_at ibytes in_p (word 32) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = word (pc + 3708) /\
               read X9 s = word 32 /\
               byte_list_at (gcm_dec128_pt_bytes 32 ibytes ctr0 rk) out_p (word 32) s /\
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
  WB_READABLE_TAC 2 AES128_GCM_DEC_ALT_BUF_2BLOCK);;

let AES128_GCM_DEC_ALT_3BLOCK = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 48 /\ LENGTH rk = 11 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,48; tag_p,16; ivec_p,16]
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,48; key_p,176; htable_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,48; tag_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,48; key_p,176; htable_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 384; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               byte_list_at ibytes in_p (word 48) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = word (pc + 3708) /\
               read X9 s = word 48 /\
               byte_list_at (gcm_dec128_pt_bytes 48 ibytes ctr0 rk) out_p (word 48) s /\
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
  WB_READABLE_TAC 3 AES128_GCM_DEC_ALT_BUF_3BLOCK);;

let AES128_GCM_DEC_ALT_4BLOCK = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 64 /\ LENGTH rk = 11 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,64; tag_p,16; ivec_p,16]
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,64; key_p,176; htable_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,64; tag_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,64; key_p,176; htable_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 512; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               byte_list_at ibytes in_p (word 64) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = word (pc + 3708) /\
               read X9 s = word 64 /\
               byte_list_at (gcm_dec128_pt_bytes 64 ibytes ctr0 rk) out_p (word 64) s /\
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
  WB_READABLE_TAC 4 AES128_GCM_DEC_ALT_BUF_4BLOCK);;

let AES128_GCM_DEC_ALT_5BLOCK = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 80 /\ LENGTH rk = 11 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,80; tag_p,16; ivec_p,16]
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,80; key_p,176; htable_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,80; tag_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,80; key_p,176; htable_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 640; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               byte_list_at ibytes in_p (word 80) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = word (pc + 3708) /\
               read X9 s = word 80 /\
               byte_list_at (gcm_dec128_pt_bytes 80 ibytes ctr0 rk) out_p (word 80) s /\
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
  WB_READABLE_TAC 5 AES128_GCM_DEC_ALT_BUF_5BLOCK);;

let AES128_GCM_DEC_ALT_6BLOCK = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 96 /\ LENGTH rk = 11 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,96; tag_p,16; ivec_p,16]
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,96; key_p,176; htable_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,96; tag_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,96; key_p,176; htable_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 768; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               byte_list_at ibytes in_p (word 96) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = word (pc + 3708) /\
               read X9 s = word 96 /\
               byte_list_at (gcm_dec128_pt_bytes 96 ibytes ctr0 rk) out_p (word 96) s /\
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
  WB_READABLE_TAC 6 AES128_GCM_DEC_ALT_BUF_6BLOCK);;

let AES128_GCM_DEC_ALT_7BLOCK = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 112 /\ LENGTH rk = 11 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,112; tag_p,16; ivec_p,16]
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,112; key_p,176; htable_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,112; tag_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,112; key_p,176; htable_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 896; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               byte_list_at ibytes in_p (word 112) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = word (pc + 3708) /\
               read X9 s = word 112 /\
               byte_list_at (gcm_dec128_pt_bytes 112 ibytes ctr0 rk) out_p (word 112) s /\
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
  WB_READABLE_TAC 7 AES128_GCM_DEC_ALT_BUF_7BLOCK);;

let AES128_GCM_DEC_ALT_8BLOCK = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 128 /\ LENGTH rk = 11 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,128; tag_p,16; ivec_p,16]
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,128; key_p,176; htable_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,128; tag_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,128; key_p,176; htable_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 1024; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               byte_list_at ibytes in_p (word 128) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = word (pc + 3708) /\
               read X9 s = word 128 /\
               byte_list_at (gcm_dec128_pt_bytes 128 ibytes ctr0 rk) out_p (word 128) s /\
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
  WB_READABLE_TAC 8 AES128_GCM_DEC_ALT_BUF_8BLOCK);;

(* ---- the <=8-block dispatch theorem ----
   One readable theorem for every whole-blocks call with 1 <= nblk <= 8:
   symbolic nblk, the C argument len_bits = word (128 * nblk), byte_list_at
   input and output over the whole 16 * nblk-byte buffer, and the NIST
   vocabulary of the bands.  Proof: a case split on nblk; each case reduces
   16 * k and 128 * k to numerals and applies the band theorem. *)
let AES128_GCM_DEC_ALT_DISPATCH = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p
    nblk ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     1 <= nblk /\ nblk <= 8 /\
     LENGTH ibytes = 16 * nblk /\ LENGTH rk = 11 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,16 * nblk; tag_p,16; ivec_p,16]
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htable_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htable_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word (128 * nblk); out_p; tag_p; ivec_p; key_p; htable_p] s /\
               byte_list_at ibytes in_p (word (16 * nblk)) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = word (pc + 3708) /\
               read X9 s = word (16 * nblk) /\
               byte_list_at (gcm_dec128_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p (word (16 * nblk)) s /\
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
  let bands = [AES128_GCM_DEC_ALT_1BLOCK;AES128_GCM_DEC_ALT_2BLOCK;
               AES128_GCM_DEC_ALT_3BLOCK;AES128_GCM_DEC_ALT_4BLOCK;
               AES128_GCM_DEC_ALT_5BLOCK;AES128_GCM_DEC_ALT_6BLOCK;
               AES128_GCM_DEC_ALT_7BLOCK;AES128_GCM_DEC_ALT_8BLOCK] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `nblk = 1 \/ nblk = 2 \/ nblk = 3 \/ nblk = 4 \/ nblk = 5 \/ nblk = 6 \/ nblk = 7 \/ nblk = 8`
    MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  FIRST (map (fun w -> MATCH_MP_TAC w THEN ASM_REWRITE_TAC[]) bands));;

(* gcm_dec128_pt_bytes at a symbolic nblk: (16 * nblk) DIV 16 = nblk. *)
let GCM_DEC128_PT_BYTES_WHOLE_SYM = prove
 (`!nblk ibytes ctr0 rk. 1 <= nblk
     ==> gcm_dec128_pt_bytes (16 * nblk) ibytes ctr0 rk =
         aes128_ctr_bytes ctr0 (gcm_dec_blocks_from 0 nblk ibytes) rk`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_dec128_pt_bytes] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Pointwise data output.                                                    *)
(*                                                                           *)
(* The data postcondition of the spines is the whole-buffer byte-list form   *)
(* byte_list_at (gcm_dec128_pt_bytes (16 * nblk) ..), which reads as though  *)
(* arbitrary byte lengths were accepted.  The pointwise form                 *)
(*   !j. j<nblk ==> read(memory:>bytes128(out_p+16j)) s =                    *)
(*                  EL j (aes128_ctr ...)                                    *)
(* says that the routine handles whole blocks, in the shape of the other     *)
(* AES-GCM proofs; the exported theorems are stated in it, so it is not      *)
(* folded back into the byte-list form.                                      *)
(* ------------------------------------------------------------------------- *)

(* The 16 bytes at offset 16 * j of int128_list_to_bytes repack to EL j: the
   reverse direction of the int128-list / byte-list correspondence.  By
   induction on cts and cases on j: block 0 is the first 16 bytes
   (SUB_LIST_APPEND_LEFT), block SUC j is block j of the tail
   (SUB_LIST_APPEND_RIGHT_GENERAL past the 16 bytes of the head). *)
let SUB_LIST_INT128_LIST_TO_BYTES_EL = prove
 (`!cts j. j < LENGTH cts
     ==> bytes_to_int128 (SUB_LIST (16 * j,16) (int128_list_to_bytes cts)) =
         EL j cts`,
  LIST_INDUCT_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[int128_list_to_bytes; LENGTH; CONJUNCT1 LT; LT_SUC; EL; HD; TL;
               MULT_CLAUSES; SUB_LIST_APPEND_LEFT; LENGTH_INT128_TO_BYTES; LE_REFL;
               SUB_LIST_OF_INT128_TO_BYTES; BYTES_TO_INT128_OF_INT128_TO_BYTES;
               MATCH_MP SUB_LIST_APPEND_RIGHT_GENERAL
                        (SPEC_ALL LENGTH_INT128_TO_BYTES);
               GE; LE_ADD; ADD_SUB2]);;

(* byte_list_at (gcm_dec128_pt_bytes ..) -> the per-block bytes128 reads.  At
   16 * nblk bytes gcm_dec128_pt_bytes is the flattened counter-mode stream
   over the nblk input blocks (GCM_DEC128_PT_BYTES_WHOLE_SYM), so each 16-byte
   slice is EL j of it: BYTE_LIST_AT_1BLOCKS at byte 16 * j reads block j as
   that slice, and the repack lemma above closes it back to EL j. *)
let WBN_OUTPUT_POINTWISE = prove
 (`!nblk ibytes ctr0 rk out_p s.
     1 <= nblk /\ 128 * nblk < 2 EXP 64 /\
     byte_list_at (gcm_dec128_pt_bytes (16 * nblk) ibytes ctr0 rk)
                  out_p (word (16 * nblk)) s
     ==> !j. j < nblk
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 EL j (aes128_ctr ctr0 (gcm_dec_blocks_from 0 nblk ibytes) rk)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `16 * j` o MATCH_MP BYTE_LIST_AT_1BLOCKS) THEN
  ASM_SIMP_TAC[GCM_DEC128_PT_BYTES_WHOLE_SYM; aes128_ctr_bytes;
               LENGTH_INT128_LIST_TO_BYTES; LENGTH_AES128_CTR;
               LENGTH_GCM_DEC_BLOCKS_FROM; VAL_WORD_EQ; DIMINDEX_64;
               ARITH_RULE `128 * n < 2 EXP 64 ==> 16 * n < 2 EXP 64`;
               ARITH_RULE `16 * j + 16 <= 16 * n <=> j < n`;
               SUB_LIST_INT128_LIST_TO_BYTES_EL]);;

(* ------------------------------------------------------------------------- *)
(* Bridge: the whole-buffer byte-list output collapses to the per-block,     *)
(* NIST-nonce-named keystream form of the exported theorems:                 *)
(*   byte_list_at (gcm_dec128_pt_bytes ..) ==> !j. j < nblk ==>              *)
(*     read bytes128 (out_p + 16 j) = cph_j XOR E_K(nonce||(c + j))          *)
(* given word_bytereverse ctr0 = ctr_block nonce c.  It combines             *)
(* WBN_OUTPUT_POINTWISE (byte list -> EL j of aes128_ctr), EL_AES128_CTR     *)
(* (element j is input block j XOR its keystream) and                        *)
(* GCM_CTR_INC_ITER_CTR_BLOCK (the counter gcm_ctr_inc_iter j ctr0 is the    *)
(* byte-reversed NIST block nonce||(c + j)).                                 *)
(* ------------------------------------------------------------------------- *)
let WBN_OUTPUT_POINTWISE_NONCE = prove
 (`!nblk ibytes ctr0 rk out_p s nonce c.
     1 <= nblk /\ 128 * nblk < 2 EXP 64 /\
     word_bytereverse ctr0 = ctr_block nonce c /\
     byte_list_at (gcm_dec128_pt_bytes (16 * nblk) ibytes ctr0 rk)
                  out_p (word (16 * nblk)) s
     ==> !j. j < nblk
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (EL j (gcm_dec_blocks_from 0 nblk ibytes))
                          (aes128_encrypt
                             (word_bytereverse (ctr_block nonce (c + j))) rk)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`nblk:num`; `ibytes:byte list`; `ctr0:int128`; `rk:int128 list`;
                `out_p:int64`; `s:armstate`] WBN_OUTPUT_POINTWISE) THEN
  ASM_SIMP_TAC[EL_AES128_CTR; LENGTH_GCM_DEC_BLOCKS_FROM;
               ISPECL [`j:num`; `nonce:96 word`; `c:num`] GCM_CTR_INC_ITER_CTR_BLOCK]);;

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
  SIMP_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

(* Input assembler: the per-block int128 reads (= inblock j) assemble into the
   byte_list_at precondition of the spine, at ibytes = the flattened list.  The
   mirror of WBN_OUTPUT_POINTWISE (byte_list_at -> per-block reads): byte i of
   the flattened list and the byte at in_p + i are both byte i MOD 16 of block
   i DIV 16 (EL_INT128_LIST_TO_BYTES, BYTE8_OF_BYTES128). *)
let WBN_INPUT_ASSEMBLE = prove
 (`!inblock nblk in_p s.
     128 * nblk < 2 EXP 64 /\
     (!j. j < nblk
          ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
              inblock j)
     ==> byte_list_at (int128_list_to_bytes (list_of_seq inblock nblk)) in_p
                      (word (16 * nblk)) s`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[byte_list_at; VAL_WORD_EQ; DIMINDEX_64;
               ARITH_RULE `128 * n < 2 EXP 64 ==> 16 * n < 2 EXP 64`] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`word_add in_p (word (16 * (i DIV 16))):int64`; `s:armstate`;
                `i MOD 16`] BYTE8_OF_BYTES128) THEN
  ASM_SIMP_TAC[EL_INT128_LIST_TO_BYTES; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ;
               RDIV_LT_EQ; MOD_LT_EQ; ARITH_EQ;
               GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; DIVISION_SIMP]);;

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

(* ------------------------------------------------------------------------- *)
(* The export lift.  WBN_EXPORT_FROM_SPINE_TAC spine proves a statement in   *)
(* the exported vocabulary from a spine, without re-running any              *)
(* simulation, by the instantiation                                          *)
(*   rk     := MAP (word_reversefields 8) rk  (the memory image of the       *)
(*                                            FIPS-197 schedule rk)          *)
(*   H      := aes128_cipher (word 0) rk      (the NIST GHASH key,           *)
(*                                            E_K(0^128))                    *)
(*   ctr0   := word_reversefields 8 (ctr_block nonce c)                      *)
(*   ibytes := int128_list_to_bytes (list_of_seq inblock nblk)               *)
(* followed by restating the input per block (WBN_INPUT_ASSEMBLE), the       *)
(* output per block over the shared keystream (WBN_OUTPUT_POINTWISE_NONCE,   *)
(* GCM_DEC_BLOCKS_FROM_ASSEMBLED, AES128_ENCRYPT_CTR_AS_AES_CTR_BLOCK), the  *)
(* GHASH input as nist_input_block (NIST_INPUT_OF_ASSEMBLED) and the         *)
(* counter write-back (GCM_CTR_INC_ITER_NIST_IVEC).  The key precondition    *)
(* forces LENGTH rk = 11, so the spine's hypothesis LENGTH rk = 11 needs no  *)
(* counterpart: when it fails, the precondition is unsatisfiable.  Every     *)
(* other hypothesis of the spine must be a hypothesis of the goal.           *)
(* ------------------------------------------------------------------------- *)
let WBN_EXPORT_FROM_SPINE_TAC spine =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `LENGTH(rk:int128 list) = 11` THENL
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
    `aes128_cipher (word 0) (rk:int128 list)`,`H:int128`;
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
               AES128_ENCRYPT_CTR_AS_AES_CTR_BLOCK] THEN
  MATCH_ACCEPT_TAC WORD_XOR_SYM;;

(* ------------------------------------------------------------------------- *)
(* Scalar rung lemmas: the nblk > 8 generalizations of the scalar rungs of   *)
(* the <=8-block chain (word and arithmetic lemmas, no simulation).          *)
(*                                                                           *)
(* The cmp x0,x5 at 0x33c, 0x3a8 and 0x7d4 feed the b.ge at 0x340 and 0x3b0  *)
(* and the b.lt at 0x7f8, signed conditions on pointers.  For nblk <= 8      *)
(* x5 = in_p, so the first compare is reflexive.  For nblk > 8 the signed    *)
(* difference ival x0 - ival x5 equals ival (word_sub x0 x5) only if the     *)
(* buffer does not straddle the signed 2^63 boundary, hence the hypothesis   *)
(* val in_p + 16 * nblk < 2 EXP 63 of wbn_front_hyps_tm, which user-space    *)
(* buffers satisfy.                                                          *)
(* ------------------------------------------------------------------------- *)

(* signed sub of two small words: by IVAL_IWORD_GALOIS the word is iword of
   the integer difference, which lies in the signed range *)
let IVAL_WSUB_SMALL = prove
 (`!a d. a < 2 EXP 63 /\ d < 2 EXP 63
      ==> ival (word_sub (word a) (word d):int64) = &a - &d`,
  REWRITE_TAC[IVAL_IWORD_GALOIS; WORD_IWORD; IWORD_INT_SUB; DIMINDEX_64] THEN
  ARITH_TAC);;

(* the generic signed pointer-compare flag resolver:
   cmp x0,x5 with x0 = p + a, x5 = (word d) + p; b.ge/b.lt read NF<=>VF,
   which under no-2^63-straddle collapses to a < d: the two pointers are
   word (val p + a) and word (val p + d), both below 2^63, so
   IVAL_WORD_SMALL and IVAL_WSUB_SMALL give their signed values *)
let WB_PTRCMP_FLAGS = prove
 (`!(in_p:int64) a d.
      val in_p + a < 2 EXP 63 /\ val in_p + d < 2 EXP 63
      ==> (ival (word_sub (word_add in_p (word a)) (word_add (word d) in_p)) < &0 <=> a < d) /\
          ((ival (word_add in_p (word a)) - ival (word_add (word d) in_p) =
            ival (word_sub (word_add in_p (word a)) (word_add (word d) in_p))) <=> T)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_add (p:int64) (word a) = word (val p + a)`;
              WORD_RULE `word_add (word a) (p:int64) = word (val p + a)`] THEN
  ASM_SIMP_TAC[IVAL_WSUB_SMALL; IVAL_WORD_SMALL] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The >=17 front: the entry pc+0x1c to the loop head 0x3b4 (pc+948).        *)
(*                                                                           *)
(* Against the 5..8 leg WB_FRONT_BUF:                                        *)
(* - the band 5 <= nblk /\ nblk <= 8 becomes 17 <= nblk /\                   *)
(*   128 * nblk < 2 EXP 64 /\ val in_p + 16 * nblk < 2 EXP 63 (the signed    *)
(*   pointer compares must not straddle 2^63), and out_p must not overlap    *)
(*   the stack frame or the input (wbn_front_hyps_tm below);                 *)
(* - after the shared WBN_FRONT_PREBRANCH (steps 1..201) the 0x340 b.ge      *)
(*   falls through (WB_LOOPENTER_FLAGS_GE9), the front-N 0x344..0x3ac (steps *)
(*   203..229) loads input blocks 0..7, stores plaintext blocks 0..7 and     *)
(*   advances the counter chain to 13, and the 0x3b0 b.ge (step 230) falls   *)
(*   through to the loop head (WB_PTRCMP_FLAGS, D_GT_128).                   *)
(* ------------------------------------------------------------------------- *)

(* The >=17 front hypotheses: wb_front_hyps_tm with its 5 <= nblk /\ nblk <= 8
   prefix replaced by the >=17 band, keeping every other conjunct, plus two
   out_p disjointness facts the <=8 hypotheses do not need.  The front-N
   stores to out_p (the four stp q,q,[x2],#32 at 0x350..0x3a0) before the
   loop head.  Without out_p against the stack the stepper cannot show that
   these stores miss [sp+64], and it drops the reduction constant
   read (memory :> bytes64 (sp+64)) s = word 0xc200000000000000, which the
   GHASH reduction of the loop body needs (the [sp+64] conjunct of the
   invariant).  Without out_p against in_p the first store (step 206), which
   comes before the ldp's of input blocks 2..7 (steps 209, 210, 213), would
   drop every input fact, so those loads would read unknown values. *)
let wbn_front_hyps_tm =
  let _,rest1 = dest_conj wb_front_hyps_tm in
  let _,rest = dest_conj rest1 in
  mk_conj(`17 <= nblk /\ 128 * nblk < 2 EXP 64 /\ val (in_p:int64) + 16 * nblk < 2 EXP 63`,
   mk_conj(`nonoverlapping (out_p:int64,16 * nblk) (stackpointer:int64,80)`,
    mk_conj(`nonoverlapping (out_p:int64,16 * nblk) (in_p:int64,16 * nblk)`,
            rest)));;

let mk_wbn_front_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_tm, ens));;

(* The 0x3b0 b.ge (step 230): after the cmp x0,x5 at 0x3a8, X0 = in_p + 128
   and X5 = in_p + d with d = 128 * ((nblk - 1) DIV 8) > 128 for nblk >= 17,
   so NF is true and VF false, and the b.ge falls through to the loop head
   0x3b4 (WB_PTRCMP_FLAGS, D_GT_128). *)
let WBN_RESOLVE_394_TAC : tactic = fun (asl,w) ->
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
(* The >=17 leg (to the loop head 0x3b4) and the 9..16 leg (to the           *)
(* prepretail 0x7fc) run the same steps up to the 0x3b0 b.ge, which the >=17 *)
(* leg falls through and the 9..16 leg takes; the 0x340 b.ge falls through   *)
(* in both.  So the prefix (0x1c to 0x3b0) is proved once on the union band  *)
(* 9 <= nblk (WBN_FRONT_PREFIX), keeping the raw s229 state with the NZCV    *)
(* facts of the cmp x0,x5 at 0x3a8 that the b.ge reads.  Each leg then       *)
(* resolves the branch in its own band, in a one-step leg chained by         *)
(* ENSURES_TRANS_SIMPLE (WBN_FRONT_BUF and WBN_LOOP_INVARIANT_ENTRY_RAW for  *)
(* >=17, WBN_FRONT_TO_PREP_916 for 9..16).                                   *)
(* ------------------------------------------------------------------------- *)

(* the union band: wbn_front_hyps_tm with 17 <= nblk relaxed to 9 <= nblk *)
let wbn_front_hyps_ge9_tm =
  let rec repl t = match t with
    | Comb(Comb(Const("/\\",_),a),b) -> mk_conj(repl a, repl b)
    | _ -> if t = `17 <= nblk` then `9 <= nblk` else t in
  repl wbn_front_hyps_tm;;

(* The 0x340 b.ge falls through whenever d = 128 * ((nblk - 1) DIV 8) >= 1,
   i.e. nblk >= 9, in both the >=17 and the 9..16 legs: the cmp x0,x5 at 0x33c
   compares in_p with in_p + d (the a = 0 case of WB_PTRCMP_FLAGS). *)
let WB_LOOPENTER_FLAGS_GE9 = prove
 (`!(in_p:int64) nblk. 9 <= nblk /\ 128 * nblk < 2 EXP 64 /\
        val in_p + 16 * nblk < 2 EXP 63
    ==> (ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) < &0 <=> T) /\
        (ival in_p - ival (word_add (word (128 * (nblk - 1) DIV 8)) in_p) =
         ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) <=> T)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`in_p:int64`; `0`; `128 * (nblk - 1) DIV 8`] WB_PTRCMP_FLAGS) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ARITH_TAC);;

(* the 0x340 b.ge falls through, by WB_LOOPENTER_FLAGS_GE9 *)
let WBN_RESOLVE_324_GE9_TAC : tactic =
  MP_TAC(SPECL [`in_p:int64`; `nblk:num`] WB_LOOPENTER_FLAGS_GE9) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]));;

(* prefix goal builder (union band, postcondition at the loop-skip b.ge) *)
let mk_wbn_prefix_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_ge9_tm, ens));;

(* The s229 prefix postcondition, the state at the 0x3b0 b.ge before it
   executes: input blocks 0..7 in Q8..Q15, plaintext blocks 0..7 stored and
   5..7 still in Q5..Q7, the counters 8..12 in Q0..Q4 and Q30 = the raw
   counter + 13, with the NZCV facts of the cmp x0,x5 at 0x3a8, which each leg
   resolves in its band at step 230.  The key, htable, tag and ivec memory
   facts do not survive the first out_p store (step 206), and the
   input-buffer facts are not restated; WBN_FRONT_PREFIX_EXT below adds back
   the input buffer, the round keys and the htable, which the frame
   preserves.  Built like wb_front_postcond, as the final state of the prefix
   simulation. *)
let wbn_front_prefix_postcond = wbp_post
 ([`aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc`;
   `read PC s = word (pc + 944)`] @
  wbp_cmp_flags `word_add in_p (word 128):int64`
                `word_add (word (128 * (nblk - 1) DIV 8)) in_p:int64` @
  [wbp_out 6; wbp_out 7;
   `read X2 s = word_add out_p (word 128)`;
   wbp_out 4; wbp_out 5;
   wbp_rd `Q3` (wbp_rev_ctr 11);
   wbp_out 2; wbp_out 3;
   wbp_rd `Q12` (mk_cph 4); wbp_rd `Q13` (mk_cph 5);
   wbp_out 0; wbp_out 1;
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
  [wbp_rd `Q9` (mk_cph 1); wbp_rd `Q8` (mk_cph 0);
   wbp_rd `Q0` (wbp_rev_ctr 8);
   wbp_rd `Q11` (mk_cph 3); wbp_rd `Q10` (mk_cph 2);
   wbp_rd `Q1` (wbp_rev_ctr 9);
   `read X0 s = word_add in_p (word 128)`;
   wbp_rd `Q15` (mk_cph 7); wbp_rd `Q14` (mk_cph 6);
   wbp_rd `Q2` (wbp_rev_ctr 10);
   wbp_rd `Q6` (wbp_pt 6); wbp_rd `Q5` (wbp_pt 5); wbp_rd `Q7` (wbp_pt 7);
   wbp_rd `Q4` (wbp_rev_ctr 12);
   wbp_rd `Q30` (wbp_raw_acc 12)]);;

(* Input blocks 0..7 as 128-bit lanes at s201, for the ldp q8..q15 of the
   front-N (0x344..0x36c), from the input-buffer fact; the SPECL state must be
   the one ENSURES_INIT_TAC names in WBN_FRONT_PREFIX. *)
let WBN_LANES_PREBRANCH_GE9_TAC =
  SUBGOAL_THEN
   `!k. k < 8 ==> read (memory :> bytes128 (word_add in_p (word (16 * k)))) s201 =
                  bytes_to_int128 (SUB_LIST (16 * k, 16) (ibytes:byte list))`
   MP_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s201:armstate`]
      INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun lth -> X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `k:num` lth) THEN ANTS_TAC THENL
       [MP_TAC(ASSUME `k < 8`) THEN NBLK_ARITH_GE9_TAC; REWRITE_TAC[]]);
    DISCH_THEN(fun lth ->
      EVERY(map (fun i ->
        ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)
          (MP (SPEC (mk_small_numeral i) lth)
              (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral i) `8`)))))
        (0--7)))];;

(* The front prefix (union band 9 <= nblk): WBN_FRONT_PREBRANCH (steps 1..201,
   to the 0x340 b.ge), chained by ENSURES_TRANS_SIMPLE; then the 0x340 b.ge
   falls through (step 202, WBN_RESOLVE_324_GE9_TAC) and the front-N runs
   steps 203..229 to the 0x3b0 b.ge (pc+944, state s229).  The ABI frame is
   unfolded before the simulation, so the final state discharges it. *)
let WBN_FRONT_PREFIX = prove(mk_wbn_prefix_goal wbn_front_prefix_postcond,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_front_prebranch_postcond THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ASM_SIMP_TAC[WBN_FRONT_PREBRANCH; ARITH_RULE `9 <= nblk ==> 5 <= nblk`];
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_INIT_TAC "s201" THEN RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
    WBN_LANES_PREBRANCH_GE9_TAC THEN WBN_RESOLVE_324_GE9_TAC THEN
    EVERY(map (fun i -> ARM_STEPS_TAC AES128_GCM_DEC_ALT_EXEC (i--i) THEN
               GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_STALE_Q30_TAC) (202--229)) THEN
    wb_front_fold_tac THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0]]);;

(* The s230 postcondition of WBN_FRONT_BUF at the loop head: the facts of
   wbn_front_prefix_postcond one step later, after the 0x3b0 b.ge, in reverse
   order, with PC = pc+948 and without the NF and VF facts. *)
let wbn_front_postcond_i0 =
  let cs = conjuncts(snd(dest_abs wbn_front_prefix_postcond)) in
  let nf_vf c = try mem (rand(rator(lhs c))) [`NF`; `VF`] with Failure _ -> false in
  wbp_post (hd cs :: `read PC s = word (pc + 948)` ::
            filter (not o nf_vf) (rev (tl (tl cs))));;

(* WBN_FRONT_BUF, the >=17 front: WBN_FRONT_PREFIX (pc+0x1c to the 0x3b0
   b.ge), chained by ENSURES_TRANS_SIMPLE, then step 230: the 0x3b0 b.ge falls
   through for 17 <= nblk (WBN_RESOLVE_394_TAC) to the loop head
   0x3b4 = pc+948.  The later legs take their precondition and frame from its
   statement (wbn_front_P_tm and wbn_front_C_tm below). *)
let WBN_FRONT_BUF = prove(mk_wbn_front_goal wbn_front_postcond_i0,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_front_prefix_postcond THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ASM_SIMP_TAC[WBN_FRONT_PREFIX; ARITH_RULE `17 <= nblk ==> 9 <= nblk`];
    REWRITE_TAC[WORD_ADD_0; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ARM_SIM_TAC ~preprocess_tac:WBN_RESOLVE_394_TAC
      AES128_GCM_DEC_ALT_EXEC (230--230)]);;

(* ------------------------------------------------------------------------- *)
(* The two-stream main-loop invariant at the loop head 0x3b4 (pc+948).       *)
(*                                                                           *)
(* The state at the loop head, generalized to the iteration index i:         *)
(* - the store/counter stream runs ahead at 8(i+1): X0 = in_p + 128(i+1),    *)
(*   X2 = out_p + 128(i+1), Q0..Q4 = the counters 8i+8..8i+12, Q5..Q7 = the  *)
(*   plaintexts of blocks 8i+5..8i+7 (already stored), the stores done for   *)
(*   all j < 8(i+1), Q30 = the raw counter + 8i+13;                          *)
(* - the GHASH stream lags at 8i: Q19 = the accumulator over the raw         *)
(*   ciphertext blocks 0..8i-1, Q8..Q15 = the raw blocks 8i..8i+7 not yet    *)
(*   folded in.                                                              *)
(* The loop body and the prepretail read exactly these registers (Q0..Q4,    *)
(* Q8..Q15, Q19, Q30, Q31, X0, X2, X4, X5, X6, X10, X11); the round keys the *)
(* front leaves in Q26, Q27 and Q28 are dead (both reload them before use),  *)
(* and the remaining conjuncts are facts the later legs pass through.  The   *)
(* loop control is the cmp x0,x5 at 0x7d4 and the signed b.lt 0x3b4 at       *)
(* 0x7f8; the exit falls through to the prepretail 0x7fc (pc+2044); the loop *)
(* runs (nblk - 9) DIV 8 times.                                              *)
(* ------------------------------------------------------------------------- *)

let wbn128_loop_invariant = new_definition
 `wbn128_loop_invariant (pc:num) (ctr0:int128) (in_p:int64) (out_p:int64)
    (tag_p:int64) (ivec_p:int64) (key_p:int64) (htable_p:int64) (stackpointer:int64)
    (nblk:num) (ibytes:byte list) (xi:int128) (h:int128)
    (k0:int128) k1 k2 k3 k4 k5 k6 k7 k8 k9 (k10:int128) =
  \(i:num) (s:armstate).
    aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
    read PC s = word (pc + 948) /\
    read Q0 s = gcm_ctr_add (word (8 * i + 8)) ctr0 /\
    read Q1 s = gcm_ctr_add (word (8 * i + 9)) ctr0 /\
    read Q2 s = gcm_ctr_add (word (8 * i + 10)) ctr0 /\
    read Q3 s = gcm_ctr_add (word (8 * i + 11)) ctr0 /\
    read Q4 s = gcm_ctr_add (word (8 * i + 12)) ctr0 /\
    read Q5 s =
    word_xor
    (word_xor (bytes_to_int128 (SUB_LIST (16 * (8 * i + 5),16) ibytes))
    (aes9 (gcm_ctr_inc_iter (8 * i + 5) ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9))
    k10 /\
    read Q6 s =
    word_xor
    (word_xor (bytes_to_int128 (SUB_LIST (16 * (8 * i + 6),16) ibytes))
    (aes9 (gcm_ctr_inc_iter (8 * i + 6) ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9))
    k10 /\
    read Q7 s =
    word_xor
    (word_xor (bytes_to_int128 (SUB_LIST (16 * (8 * i + 7),16) ibytes))
    (aes9 (gcm_ctr_inc_iter (8 * i + 7) ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9))
    k10 /\
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
             (aes9 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9))
             k10) /\
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
    htable_mem_dec h htable_p s`;;

(* ------------------------------------------------------------------------- *)
(* Strengthening an ensures postcondition with a fact the frame preserves,   *)
(* without re-simulation: from                                               *)
(*   ensures step P Q C   and   !s s'. P s /\ C s s' ==> R s'                *)
(* ENSURES_ADD_PRESERVED gives                                               *)
(*   ensures step P (\s. Q s /\ R s) C                                       *)
(* (ENSURES_SUBLEMMA_THM with the same precondition and frame).              *)
(* WBN_FRONT_PREFIX_EXT uses it to add the loop constants to the prefix      *)
(* postcondition, and the recomposition below uses it to carry the stores of *)
(* the first output blocks through the tail legs.                            *)
(* ------------------------------------------------------------------------- *)

let ENSURES_ADD_PRESERVED = prove
 (`!(step:A->A->bool) P Q R C.
    ensures step P Q C /\ (!s s'. P s /\ C s s' ==> R s')
    ==> ensures step P (\s. Q s /\ R s) C`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `ensures (step:A->A->bool) P Q C` THEN
  MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN
  ASM_MESON_TAC[SUBSUMED_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The front prefix with the loop constants re-asserted.  The invariant      *)
(* needs the input buffer, the 11 round keys and the htable at the loop      *)
(* head.  The simulated postcondition of the prefix does not restate them    *)
(* (the key and htable facts do not survive the first out_p store), but the  *)
(* front frame preserves them: it lets the front change only out_p, tag_p,   *)
(* ivec_p, the 16 bytes at sp+64 and registers.  The preservation needs      *)
(* out_p disjoint from key_p and htable_p as well, which the wide hypotheses *)
(* add (out_p against in_p is already in wbn_front_hyps_tm).                 *)
(* ------------------------------------------------------------------------- *)

(* the wide >=17 hypotheses: wbn_front_hyps_tm plus the disjointness of out_p
   from key_p and htable_p *)
let wbn_front_hyps_wide_tm =
  mk_conj(wbn_front_hyps_tm,
    `nonoverlapping (out_p:int64,16 * nblk) (key_p:int64,176) /\
     nonoverlapping (out_p:int64,16 * nblk) (htable_p:int64,192)`);;

(* the WBN_FRONT_BUF pieces: P = precondition, Q0 = simulated postcondition,
   C = frame *)
let wbn_front_P_tm, wbn_front_Q0_tm, wbn_front_C_tm =
  let ens = snd(dest_imp(snd(strip_forall(concl WBN_FRONT_BUF)))) in
  rand(rator(rator ens)), rand(rator ens), rand ens;;

(* R = the loop constants (the input buffer, k0..k10, htable_mem_dec), spelled
   as wbn128_loop_invariant states them *)
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
     `htable_mem_dec h (htable_p:int64) s`]);;

(* WBN_FRONT_PREFIX_EXT, the front prefix with the loop constants, serves both
   legs from the 0x3b0 b.ge: the >=17 loop entry WBN_LOOP_INVARIANT_ENTRY_RAW
   and the 9..16 leg WBN_FRONT_TO_PREP_916 to the prepretail. *)

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
    REWRITE_TAC[htable_mem_dec; LET_DEF; LET_END_DEF;
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE; SEQ_ID;
                GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC(REDEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_eq(concl th) &&
        (match rhs(concl th) with Var("s'",_) -> true | _ -> false))) THEN
    WBN_PUSH_LHS_READ_TAC]);;

(* the strengthened prefix postcondition (prefix post /\ R) *)
let wbn_front_prefix_ext_post =
  rand(rator(snd(dest_imp(snd(strip_forall(concl WBN_FRONT_PREFIX_EXT))))));;

(* ------------------------------------------------------------------------- *)
(* WBN_LOOP_INVARIANT_ENTRY_RAW: the >=17 front establishes the i = 0        *)
(* invariant.  As WBN_FRONT_TO_PREP_916 does for 9..16, it runs the shared   *)
(* prefix WBN_FRONT_PREFIX_EXT and then step 230, the 0x3b0 b.ge, which      *)
(* here falls through to the loop head (WBN_RESOLVE_394_TAC).  The store     *)
(* forall j < 8 expands to the eight stores and one simplification takes     *)
(* both sides to the rev32 lanes: the invariant's gcm_ctr_add (word k) ctr0  *)
(* and the front's gcm_ctr_inc^k ctr0 unfold to the same lanes, the Q19 fold *)
(* over no blocks is the reversed tag, and Q30 (the raw counter + 12, then   *)
(* + 1) is gcm_ctr_raw (word 13) ctr0.                                       *)
(* ------------------------------------------------------------------------- *)

(* the invariant applied to its 24 parameters, as a num->armstate->bool *)
let wbn_inv_applied =
  list_mk_comb(`wbn128_loop_invariant`,
    [`pc:num`;`ctr0:int128`;`in_p:int64`;`out_p:int64`;`tag_p:int64`;`ivec_p:int64`;
     `key_p:int64`;`htable_p:int64`;`stackpointer:int64`;`nblk:num`;`ibytes:byte list`;
     `xi:int128`;`h:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;
     `k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`]);;

(* post = \s. decodes /\ PC = pc+948 /\ inv 0 s *)
let wbn_entry_post =
  subst [wbn_inv_applied,`INVAPP:num->armstate->bool`]
    `\s:armstate. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
                  read PC s = word (pc + 948) /\
                  INVAPP (0:num) s`;;

let wbn_entry_goal =
  let ens = list_mk_comb(`ensures arm`,[wbn_front_P_tm; wbn_entry_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_LOOP_INVARIANT_ENTRY_RAW = prove(wbn_entry_goal,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_front_prefix_ext_post THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    MATCH_MP_TAC WBN_FRONT_PREFIX_EXT THEN
    ASM_SIMP_TAC[ARITH_RULE `17 <= nblk ==> 9 <= nblk`];
    REWRITE_TAC[wbn128_loop_invariant; htable_mem_dec; LET_DEF; LET_END_DEF;
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ARM_SIM_TAC ~preprocess_tac:WBN_RESOLVE_394_TAC
      AES128_GCM_DEC_ALT_EXEC (230--230) THEN
    CONV_TAC(NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
             NUM_REDUCE_CONV) THEN
    ASM_SIMP_TAC(wb_ctr_lanes_thms @
      [GCM_CTR_ADD_LANES; gcm_ctr_inc_iter; GCM_CTR_INC_ITER_AS_ADD;
       gcm_ctr_raw_def; list_of_seq; MAP; ghash_polyval_acc; WORD_ADD_0;
       WORD_RULE `word_add (word_add (x:32 word) (word 12)) (word 1) =
                  word_add x (word 13)`])]);;

(* ------------------------------------------------------------------------- *)
(* The PC- and decode-free core of the invariant and its split.  The         *)
(* ENSURES_WHILE tactics put `aligned_bytes_loaded` and `read PC s = ...`    *)
(* around their own loop invariant, at the loop head and at the exit, so     *)
(* the loop is stated with the core (the invariant without its first two     *)
(* conjuncts, built from the definition so the two stay in step);            *)
(* WBN_INV_RAW_SPLIT relates the two forms.                                  *)
(* ------------------------------------------------------------------------- *)

let wbn128_loop_inv_core =
  let eqn = snd(strip_forall(concl wbn128_loop_invariant)) in
  let lhs_full, rhs_full = dest_eq eqn in
  let hd, params = strip_comb lhs_full in
  let ivars, body = strip_abs rhs_full in
  let cs = conjuncts body in
  let core_body = list_mk_conj (List.tl (List.tl cs)) in
  let core_rhs = list_mk_abs(ivars, core_body) in
  let newhead = mk_var("wbn128_loop_inv_core", type_of hd) in
  new_definition (mk_eq(list_mk_comb(newhead, params), core_rhs));;

let wbn_inv_args =
  snd(strip_comb(fst(dest_eq(snd(strip_forall(concl wbn128_loop_invariant))))));;

let WBN_INV_RAW_SPLIT = prove
 (list_mk_forall(wbn_inv_args @ [`i:num`;`s:armstate`],
    mk_eq(
      list_mk_comb(`wbn128_loop_invariant`, wbn_inv_args @ [`i:num`;`s:armstate`]),
      list_mk_conj[
        `aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc`;
        `read PC s = word (pc + 948)`;
        list_mk_comb(`wbn128_loop_inv_core`, wbn_inv_args @ [`i:num`;`s:armstate`])])),
  REWRITE_TAC[wbn128_loop_invariant; wbn128_loop_inv_core] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[CONJ_ACI]);;

(* ------------------------------------------------------------------------- *)
(* The ENSURES_WHILE skeleton of the main loop.  The back-edge is            *)
(*   cmp x0,x5 @0x7d4 ... b.lt 0x3b4 @0x7f8,                                 *)
(* a signed branch that is the last body instruction, with its cmp inside    *)
(* the body: the ENSURES_WHILE_UP2_TAC shape, where the body postcondition's *)
(* PC is word (if i + 1 < k then pc1 else pc2) and the exit is the           *)
(* fall-through pc2.  k = (nblk - 9) DIV 8, pc1 = pc+948, pc2 = pc+2044.     *)
(* ENSURES_WHILE_UP2_TAC's frame-idempotence step fails on this frame        *)
(* unless MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI is expanded first, so    *)
(* WBN_MAIN_LOOP_OF_BODY expands it in its goal before calling the tactic.   *)
(* ------------------------------------------------------------------------- *)

(* the core applied to its parameters, as a num->armstate->bool and as \i s. *)
let wbn_core_applied =
  list_mk_comb(`wbn128_loop_inv_core`,
    [`pc:num`;`ctr0:int128`;`in_p:int64`;`out_p:int64`;`tag_p:int64`;`ivec_p:int64`;
     `key_p:int64`;`htable_p:int64`;`stackpointer:int64`;`nblk:num`;`ibytes:byte list`;
     `xi:int128`;`h:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;
     `k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`]);;

let wbn_core_iv = list_mk_abs([`i:num`;`s:armstate`],
  mk_comb(mk_comb(wbn_core_applied,`i:num`),`s:armstate`));;

(* The loop, PC = pc+948 /\ core 0 ==> PC = pc+2044 /\ core k over the front
   frame (the statement of WBN_MAIN_LOOP_raw below), and one iteration of its
   body, for every i < k (the statement of WBN_LOOP_BODY below):
     PC = pc+948 /\ core i ==>
     PC = (if i + 1 < k then pc+948 else pc+2044) /\ core (i+1). *)
let wbn_main_loop_goal =
  let kk = `(nblk - 9) DIV 8` in
  let loop_pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc`;
      `read PC s = word (pc + 948)`;
      mk_comb(mk_comb(wbn_core_applied,`0`),`s:armstate`)]) in
  let loop_post = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc`;
      `read PC s = word (pc + 2044)`;
      mk_comb(mk_comb(wbn_core_applied,kk),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[loop_pre; loop_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let wbn_loop_body_tm =
  let kk = `(nblk - 9) DIV 8` in
  let body_pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc`;
      `read PC s = word (pc + 948)`;
      mk_comb(mk_comb(wbn_core_applied,`i:num`),`s:armstate`)]) in
  let body_post = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc`;
      `read PC s = word (if i + 1 < (nblk - 9) DIV 8 then pc + 948 else pc + 2044)`;
      mk_comb(mk_comb(wbn_core_applied,`i + 1`),`s:armstate`)]) in
  mk_forall(`i:num`, mk_imp(mk_binop `(<):num->num->bool` `i:num` kk,
    list_mk_comb(`ensures arm`,[body_pre; body_post; wbn_front_C_tm])));;

let wbn_loop_body_goal =
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, wbn_loop_body_tm));;

(* WBN_MAIN_LOOP_OF_BODY: the loop from its body.  The count is nonzero      *)
(* (17 <= nblk), and the entry and exit legs are the 0-step ensures from     *)
(* the loop head and from the exit.                                          *)
let WBN_MAIN_LOOP_OF_BODY = prove
 (list_mk_forall(wb_front_vars,
    mk_imp(wbn_front_hyps_wide_tm,
      mk_imp(wbn_loop_body_tm, snd(dest_imp(snd(strip_forall wbn_main_loop_goal)))))),
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_THEN(LABEL_TAC "body") THEN
  ENSURES_WHILE_UP2_TAC `(nblk - 9) DIV 8` `pc + 948` `pc + 2044` wbn_core_iv THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN ASM_ARITH_TAC;
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "body" (fun th -> MATCH_ACCEPT_TAC
      (MP (SPEC `i:num` th) (ASSUME `i < (nblk - 9) DIV 8`)));
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let WBN_MACHINE_REDUCE_IS_PROP3_PACK = prove
 (`!PL PH PM:int128.
     word_xor
      (word_xor PH
       (word_pmul
        (word_subword
         (word_xor
          (word_xor (word_xor (word_xor PM PL) PH)
          (word_pmul (word_subword PL (0,64) :64 word) (word 13979173243358019584 :64 word)))
         (word_subword (word_join PL PL :256 word) (64,128)))
        (0,64) :64 word)
       (word 13979173243358019584 :64 word)))
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
      (64,128)) =
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

let build_q19_reduce_clean pl_t ph_t pm_t =
  let bsh = `byteswap128 h` in
  let rec tower n = if n <= 1 then bsh else mk_comb(mk_comb(`polyval_dot`, tower(n-1)), bsh) in
  let inst_list = map (fun n -> (mk_comb(`byteswap128`, tower n), mk_var("h"^string_of_int n, `:int128`))) (2--8) in
  let body_inst2 = INST inst_list BODY_Q19_CLOSE_ALGEBRA in
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
     projtac THEN REWRITE_TAC[WRF8_IS_BYTEREVERSE; LANE_COLLAPSE; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let PROJ_PH = BETA_RULE(prove(mk_proj `\t:int128#int128#int128. FST(SND t)` ph_t,
     projtac THEN REWRITE_TAC[WRF8_IS_BYTEREVERSE; LANE_COLLAPSE; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let PROJ_PM = BETA_RULE(prove(mk_imp(list_mk_conj kqok_hyps, mk_proj `\t:int128#int128#int128. SND(SND t)` pm_t),
     STRIP_TAC THEN projtac THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[WRF8_IS_BYTEREVERSE; LANE_COLLAPSE_PM_A; LANE_COLLAPSE_PM_B; PM_LANE_HI'; PM_LANE_LO'; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
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

let WBN_Q19_CLOSE_TAC : tactic =
  fun (asl,w) ->
    let clean = build_q19_reduce_clean (!wbn_q19_pl) (!wbn_q19_ph) (!wbn_q19_pm) in
    let defthms = filter (fun th -> match concl th with
      | Comb(Comb(Const("=",_),_),Var(("PL"|"PH"|"PM"),_)) -> true | _ -> false) (map snd asl) in
    let clean' = REWRITE_RULE (ARITH_RULE `8 * (i + 1) = 8 * i + 8` :: defthms) clean in
    ACCEPT_TAC clean' (asl,w);;

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
     projtac THEN REWRITE_TAC[WRF8_IS_BYTEREVERSE; LANE_COLLAPSE; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let PROJ_PH = BETA_RULE(prove(mk_proj `\t:int128#int128#int128. FST(SND t)` ph_t,
     projtac THEN REWRITE_TAC[WRF8_IS_BYTEREVERSE; LANE_COLLAPSE; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let PROJ_PM = BETA_RULE(prove(mk_imp(list_mk_conj kqok_hyps, mk_proj `\t:int128#int128#int128. SND(SND t)` pm_t),
     STRIP_TAC THEN projtac THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[WRF8_IS_BYTEREVERSE; LANE_COLLAPSE_PM_A; LANE_COLLAPSE_PM_B; PM_LANE_HI'; PM_LANE_LO'; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
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

(* 9 <= nblk from a nonzero loop count *)
let WBN_NBLK_GE_9 = prove
 (`i < (nblk - 9) DIV 8 ==> 9 <= nblk`,
  MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN ARITH_TAC);;

let GCM_SIMD_SIMPLIFY_KD_TAC =
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
    else if Hashtbl.mem gcm_simd_kd_tbl c then th
    else let th' = apply_F th in
         (if concl th' = c then Hashtbl.add gcm_simd_kd_tbl c ());
         th');;
let ARM_STEPS_FOLD_KEEPDATA_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_KD_TAC THEN
              DISCARD_STALE_DATA_TAC THEN DISCARD_OLDSTATE_KEEPDATA_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;

(* ------------------------------------------------------------------------- *)
(* The prepretail: from the loop exit 0x7fc (pc+2044) to the tail seam       *)
(* pc+3032 (0xbd8).                                                          *)
(*                                                                           *)
(* The main loop (WBN_MAIN_LOOP_raw) exits at k = (nblk-9) DIV 8 with the    *)
(* GHASH stream one 8-block group behind the stores.  This leg simulates the *)
(* 247 straight-line instructions 0x7fc..0xbd4.  The prepretail 0x7fc..0xbc0 *)
(* folds that last in-flight group (blocks 8k..8k+7) into Q19, catching the  *)
(* GHASH stream up, and computes the keystream towers of blocks 8k+8..8k+15  *)
(* in Q0..Q7; then the tail entry 0xbc4..0xbd4                               *)
(*   mov v29,v27; sub x5,x4,x0; cmp x5,#0x70; ldp q24,q25,[x6,#160];         *)
(*   ldr q9,[x0],#16                                                         *)
(* sets up the tail's registers.  So the leg is the pipelined analogue of    *)
(* the front of the <=8-block chain, which folds no block (there Q19 is the  *)
(* reversed tag) and leaves all r blocks to the tail.                        *)
(*                                                                           *)
(* The end state feeds the tail back-legs WB_TAIL_GEN2_r, which start at the *)
(* same PC (their state s199), by precondition weakening at shifted          *)
(* arguments (shift_vals r below):                                           *)
(*   ctr0   := gcm_ctr_add (word (8*(k+1))) ctr0                             *)
(*   in_p   := word_add in_p (word (128*(k+1)))                              *)
(*   out_p  := word_add out_p (word (128*(k+1)))                             *)
(*   ibytes := the last r = nblk - 8*(k+1) blocks of ibytes   (r = 1..8)     *)
(*   xi     := the reversed caught-up accumulator (all 8*(k+1) blocks)       *)
(* The counter registers reconcile by GCM_CTR_ADD_COMPOSE:                   *)
(*   gcm_ctr_add (8k+8+i) ctr0 = gcm_ctr_inc^i (gcm_ctr_add (8(k+1)) ctr0).  *)
(* The simulation is WBN_PREPRETAIL_EXT2_TAC below.  Its cut points: the     *)
(* counter folds at s5, s11, s19, s20, s36 and s235; the GHASH wire-in at    *)
(* s182, where PL, PH and PM are complete (their last writes are s182, s175  *)
(* and s174), after which the reduction s195..s234 runs on the abbreviated   *)
(* accumulators; and the incoming Q9 (the first tail block) resolved at      *)
(* s246, before the ldr q9 at s247.                                          *)
(* ------------------------------------------------------------------------- *)

(* The s247 seam state, built like wb_front_postcond, with Q19 stated at a   *)
(* fresh xi' as the substitution source for wbn_prepretail_post below (as   *)
(* written, with xi' unconstrained, it is not a true postcondition).  It     *)
(* drops what the tail does not read: the tag_p, ivec_p, [sp+72] and in_p    *)
(* block 0 cells, and Q9, which the extended post below restates in spec     *)
(* form.                                                                     *)
let wbn_prepretail_post_raw =
  let ctr j = subst [mk_small_numeral j,`jjj:num`]
    `gcm_ctr_add (word (8 * (nblk - 9) DIV 8 + jjj)) ctr0` in
  let x5v = `word_sub (word_add in_p (word (16 * nblk)))
                      (word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1)))):int64` in
  wbp_post
  ([`aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc`;
    `read PC s = word (pc + 3032)`;
    wbp_rd `Q24` (wbp_hmid 7);
    wbp_rd `Q25` (wbp_hpow 8)] @
   wbp_cmpi_flags x5v 112 @
   map (fun i -> wbp_rd (mk_const("Q"^string_of_int i,[])) (wbp_aes9 (ctr (8 + i)))) (0--7) @
   [`read (memory :> bytes64 (word_add stackpointer (word 64))) s = word 13979173243358019584`;
    `read X11 s = key_p`;
    `read X9 s = word (16 * nblk)`;
    `read SP s = stackpointer`;
    `read X1 s = word (128 * nblk)`;
    `read X2 s = word_add out_p (word (128 * ((nblk - 9) DIV 8 + 1)))`;
    `read X3 s = tag_p`;
    `read X6 s = htable_p`;
    `read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes`] @
   wbp_key_reads @ wbp_htable_reads @ wbp_ctx `xi':int128` @
   [mk_eq(`read X5 s`, x5v);
    `read X0 s = word_add (word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1)))) (word 16)`;
    `read Q29 s = k10`]);;

(* The seam post: the raw post with its fresh word_bytereverse xi', which
   occurs only in the Q19 and Q16 conjuncts, replaced by the caught-up
   accumulator, so that Q19 = wbn_caught_up (the invariant's shape at
   i := k + 1) and Q16 is its staging
   word_subword (word_join wbn_caught_up wbn_caught_up) (64,128).  xi' is gone,
   so the post is over the variables of wb_front_vars only. *)
let wbn_prepretail_post =
  subst [wbn_caught_up, `word_bytereverse (xi':int128)`] wbn_prepretail_post_raw;;

(* ------------------------------------------------------------------------- *)
(* The output stores of the first 8*(k+1) blocks.                            *)
(*                                                                           *)
(* wbn_prepretail_post does not contain the loop invariant's output-store    *)
(* conjunct                                                                  *)
(*   !j. j < 8*((nblk-9)DIV8 + 1) ==>                                        *)
(*       read (memory :> bytes128 (word_add out_p (word (16*j)))) s =        *)
(*       word_xor (word_xor (bytes_to_int128 (SUB_LIST (16*j,16) ibytes))    *)
(*                (aes9 (gcm_ctr_inc_iter j ctr0) k0..k9)) k10               *)
(* the decrypted blocks before the tail.  The final post needs the stores of *)
(* all nblk blocks and the tail leg produces only the last                   *)
(* r = nblk - 8*(k+1), so the first 8*(k+1) have to be carried through the   *)
(* seam.  The prepretail (0x7fc..0xbd4) stores nothing, so the forall passes *)
(* through the simulation unchanged, and the extended post closes by         *)
(* ASM_REWRITE: it is a preserved read fact, not frame preservation          *)
(* (ENSURES_ADD_PRESERVED does not apply, since the frame allows writes to   *)
(* out_p).                                                                   *)
(*                                                                           *)
(* wbn_out_forall is that forall at i := k, as a predicate on s, taken from  *)
(* wbn128_loop_inv_core so that it is the term the simulation preserves, and *)
(* the extended post is                                                      *)
(*   wbn_prepretail_post_ext = wbn_prepretail_post /\ wbn_out_forall.        *)
(* ------------------------------------------------------------------------- *)
let wbn_out_forall =
  let full = list_mk_comb(wbn_core_applied, [`(nblk - 9) DIV 8`; `s:armstate`]) in
  let inv_cs = conjuncts (rhs(concl (REWRITE_CONV[wbn128_loop_inv_core] full))) in
  mk_abs(`s:armstate`, find is_forall inv_cs);;

let wbn_prepretail_post_ext =
  mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs wbn_prepretail_post),
            snd(dest_abs wbn_out_forall)));;

(* ------------------------------------------------------------------------- *)
(* WBN_Q9_SPEC: the first tail block in spec form.                           *)
(*                                                                           *)
(* At the seam the simulation has executed the ldr q9,[x0],#16 at 0xbd4      *)
(* (step 247, with x0 = in_p + 128*(k+1)), so Q9 is a raw read of the input  *)
(* memory in the state before it.  The tail reads that Q9                    *)
(* (eor3 v12,v9,v0,v29 at 0xbe4) before any reload of q9, so Q9 has to reach *)
(* the seam in spec form.  This lemma gives the value of the read, the first *)
(* tail block (global block 8*(k+1))                                         *)
(*   bytes_to_int128 (SUB_LIST (16*8*(k+1),16) ibytes),                      *)
(* by INPUT_BYTES_TO_BYTE128_LANES at lane 8*(k+1), from 8*(k+1) < nblk and  *)
(* the whole-buffer input fact.  WBN_PREPRETAIL_EXT2_TAC applies it at s246, *)
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
    INPUT_BYTES_TO_BYTE128_LANES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
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

let mk_wbn_prepretail_goal hyps =
  let kk = `(nblk - 9) DIV 8` in
  let pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc`;
      `read PC s = word (pc + 2044)`;
      mk_comb(mk_comb(wbn_core_applied,kk),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[pre; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

(* the >=17 band and the union band 9 <= nblk (shared with the 9..16 leg) *)
let wbn_prepretail_ext2_goal = mk_wbn_prepretail_goal wbn_front_hyps_wide_tm;;
let wbn_prepretail_ext2_uni_goal = mk_wbn_prepretail_goal wbn_front_hyps_ge9_wide_tm;;

(* The prepretail simulation, parameterized by the first-tail-block index bound
   (idx_lt_thm: ... ==> 8 * ((nblk-9) DIV 8) + 8 < nblk): init at the invariant
   (i := k); the counter folds at s5, s11, s19, s20 and s36; the KEEPDATA bulk
   21..180; the GHASH wire-in at s182, where PL, PH and PM (Q17, Q19, Q18) are
   complete (their last writes are s182, s175 and s174): they are abbreviated
   (WBN_Q19_EXTRACT_ABBREV_TAC) so that the reduce byteform stays small, and
   the reduce and the rest run without simplification; the third counter add
   (step 235) folded at s235; Q9 resolved at s246, before the ldr q9 at 0xbd4
   (step 247).  ENSURES_FINAL and ASM_REWRITE close the preserved and shifted
   conjuncts, WBN_Q19_PREPRETAIL_CLOSE_TAC the two GHASH conjuncts. *)
let WBN_PREPRETAIL_EXT2_TAC idx_lt_thm =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wbn128_loop_inv_core] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0" THEN
  CLEAR_KEEPDATA_MEMO_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (find_term (fun t->match t with Const("byteswap128",_)->true|_->false)) c &&
       can (find_term (fun t->match t with Const("karatsuba_mid",_)->true|_->false)) c
    then STRIP_ASSUME_TAC th else NO_TAC) THEN
  ABBREV_TAC `k = (nblk - 9) DIV 8` THEN
  ARM_STEPS_TAC AES128_GCM_DEC_ALT_EXEC (1--5) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q5" "s5" `word (8*k+13):32 word` THEN
  ARM_STEPS_TAC AES128_GCM_DEC_ALT_EXEC (6--11) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  CTR_INCR_NORM_TAC "s11" 13 THEN
  ARM_STEPS_TAC AES128_GCM_DEC_ALT_EXEC (12--19) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q6" "s19" `word (8*k+14):32 word` THEN
  ARM_STEPS_TAC AES128_GCM_DEC_ALT_EXEC (20--20) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  CTR_INCR_NORM_TAC "s20" 14 THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AES128_GCM_DEC_ALT_EXEC (21--36) THEN
  REV32_FOLD_TAC "Q7" "s36" `word (8*k+15):32 word` THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AES128_GCM_DEC_ALT_EXEC (37--120) THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AES128_GCM_DEC_ALT_EXEC (121--180) THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AES128_GCM_DEC_ALT_EXEC (181--182) THEN
  WBN_Q19_EXTRACT_ABBREV_TAC "s182" THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AES128_GCM_DEC_ALT_EXEC (183--235) THEN
  (* the third add v30 (step 235), in the unsimplified window: fold it, then
     normalize 8*k+15+1 to 8*k+16; no later step writes v30 *)
  CTR_RAW_INCR_FOLD_TAC "Q30" "s235" `word (8*k+15):32 word` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word (8*k+15)) (word 1):32 word = word (8*k+16)`]) THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AES128_GCM_DEC_ALT_EXEC (236--246) THEN
  MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `k:num`; `s246:armstate`]
    WBN_Q9_SPEC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `nblk:num` idx_lt_thm) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_TAC] THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AES128_GCM_DEC_ALT_EXEC (247--247) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM aes9]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE(map GSYM wb_ctr_lanes_thms)) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN
  TRY(W(fun (asl,w) ->
        if can (find_term (fun t -> is_const t && fst(dest_const t) = "ghash_polyval_acc")) w
        then WBN_Q19_PREPRETAIL_CLOSE_TAC `k:num` else NO_TAC)) THEN
  TRY MONOTONE_MAYCHANGE_TAC THEN
  TRY (ASM_REWRITE_TAC[]);;

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
  REPEAT GEN_TAC THEN
  REWRITE_TAC[NUM_OF_BYTELIST_EQ_WORDLIST; NUM_OF_WORDLIST_SUB_LIST; DIMINDEX_8] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD;
               ARITH_RULE `a + m <= n ==> MIN (n - a) m = m`]);;

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
    `k8:int128`;`k9:int128`;`k10:int128`;`h:int128`;
    `word (16 * nblk):int64`];;

(* ------------------------------------------------------------------------- *)
(* The full-post tail legs WBN_PREP_TO_END_FREE_r and                        *)
(* WBN_PREP_TO_END_FULL_r: the seam post fed to the shifted tail, with the   *)
(* full-nblk contract as the post (not the r-block band_post).  The post is  *)
(* wbn_end_post: PC = pc+3708, X9 = word (16 * nblk), the output forall over *)
(* all nblk blocks (in the aes9 / k10 form of the seam's carried forall),    *)
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
        (aes9 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9)) k10` in
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
    list_mk_conj [`read PC s = word (pc + 3708)`;
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

(* INNER_TAIL_FEED_TAC r tail_r: the tail leg of WBN_PREP_TO_END_FULL_r_TAC
   (the first half of its ENSURES_ADD_PRESERVED step),
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
    REPLICATE_TAC 10 AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
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
    MATCH_MP_TAC tail THEN CONJ_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NONOVERLAPPING_TAC)]];;

(* the standalone per-block value bridge goal + tactic. *)
let wbn_block_bridge_goal r i =
  let it = mk_small_numeral i and rt = mk_small_numeral r in
  let gcph = subst[it,`i_:num`]
    `bytes_to_int128 (SUB_LIST (16 * (8 * (q + 1) + i_),16) (ibytes:byte list))` in
  let gval = list_mk_comb(`word_xor:int128->int128->int128`,
    [list_mk_comb(`word_xor:int128->int128->int128`,
       [gcph; list_mk_comb(`aes9`,[wbn_full_goal_ctr i;
          `k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;`k5:int128`;`k6:int128`;
          `k7:int128`;`k8:int128`;`k9:int128`])]);
     `k10:int128`]) in
  let scph = subst[it,`i_:num`;rt,`r_:num`]
    `bytes_to_int128 (SUB_LIST (16 * i_,16) (SUB_LIST (128 * (q + 1),16 * r_) (ibytes:byte list)))` in
  let sval = list_mk_comb(`word_xor:int128->int128->int128`,
    [scph; list_mk_comb(`aes128_encrypt`,
       [wbn_full_store_ctr i;
        `[k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]:(int128)list`])]) in
  mk_forall(`q:num`, mk_eq(gval,sval));;

let wbn_block_bridge_tac r i =
  let it = mk_small_numeral i and rt = mk_small_numeral r in
  let sublist_inst = SPECL [`ibytes:byte list`;`q:num`;it;rt] WBN_SUBLIST_SHIFT in
  let ctr_eq = mk_eq(wbn_full_goal_ctr i, wbn_full_store_ctr i) in
  GEN_TAC THEN
  (MP_TAC sublist_inst THEN ANTS_TAC THENL [ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
  SUBGOAL_THEN ctr_eq SUBST1_TAC THENL
   [REWRITE_TAC[GCM_CTR_INC_FOLD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM AES128_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE;;

(* close one output block j = 8*(q+1)+i, one the tail stored, in the output
   forall of FULL_r *)
let wbn_block_close_tac r i =
  let brg = SPEC `q:num` (prove(wbn_block_bridge_goal r i, wbn_block_bridge_tac r i)) in
  let it = mk_small_numeral i in
  let mul_red = ARITH_RULE (mk_eq(mk_binop `( * ):num->num->num` `16` it,
                                  mk_small_numeral(16 * i))) in
  let common = REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD] THEN SUBST1_TAC brg THEN
    REWRITE_TAC[mul_red] in
  if i = 0 then
    common THEN
    REWRITE_TAC[ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`; ADD_CLAUSES] THEN
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
  MP_TAC(REWRITE_RULE[mul_red]
           (SPECL [`ibytes:byte list`;`q:num`;mk_small_numeral i;mk_small_numeral r]
              WBN_SUBLIST_SHIFT)) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN MATCH_ACCEPT_TAC];;
let wbn_tag_fold_tac r =
  AP_TERM_TAC THEN
  ASM_REWRITE_TAC[LIST_OF_SEQ_ADD; MAP_APPEND; GHASH_ACC_APPEND; WORD_BYTEREVERSE_BYTEREVERSE] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[LIST_OF_SEQ_CLAUSES; LIST_OF_SEQ_CLAUSES_5_8; MAP; o_DEF; CONS_11] THEN
  REPEAT CONJ_TAC THEN
  FIRST (map (fun i -> AP_TERM_TAC THEN AP_TERM_TAC THEN wbn_tag_elt_close r i) (0--(r-1)));;

(* the intermediate post: the shifted band_post r of WB_TAIL_GEN2_r at
   shift_vals r, and the seam's forall over the first 8*(k+1) output blocks
   (wbn_out_forall) *)
let wbn_full_inter_post r =
  let band_post_r =
    el 2 (snd(strip_comb(snd(dest_imp(concl(SPECL (shift_vals r) (wbn_tail_gen2 r))))))) in
  mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs band_post_r),
            snd(dest_abs wbn_out_forall)));;
(* WBN_PREP_TO_END_FULL_r_TAC r, used for r = 1..8 (WBN_PREP_TO_END_FREE_r):
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
        ASM_REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD; GCM_CTR_ADD_COMPOSE; GSYM WORD_ADD]]];
    MATCH_MP_TAC ENSURES_ADD_PRESERVED THEN CONJ_TAC THENL
     [INNER_TAIL_FEED_TAC r (wbn_tail_gen2 r);
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE; SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
      CONV_TAC(REDEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN
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
(* The legs for r = 1..8, proved once on the union band 9 <= nblk.           *)
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

(* r = 1..8 on the union band 9 <= nblk, one proof per r. *)
let WBN_PREP_TO_END_FREE_1 = prove(wbn_prep_to_end_full_free_goal 1, WBN_PREP_TO_END_FULL_r_TAC 1);;
let WBN_PREP_TO_END_FREE_2 = prove(wbn_prep_to_end_full_free_goal 2, WBN_PREP_TO_END_FULL_r_TAC 2);;
let WBN_PREP_TO_END_FREE_3 = prove(wbn_prep_to_end_full_free_goal 3, WBN_PREP_TO_END_FULL_r_TAC 3);;
let WBN_PREP_TO_END_FREE_4 = prove(wbn_prep_to_end_full_free_goal 4, WBN_PREP_TO_END_FULL_r_TAC 4);;
let WBN_PREP_TO_END_FREE_5 = prove(wbn_prep_to_end_full_free_goal 5, WBN_PREP_TO_END_FULL_r_TAC 5);;
let WBN_PREP_TO_END_FREE_6 = prove(wbn_prep_to_end_full_free_goal 6, WBN_PREP_TO_END_FULL_r_TAC 6);;
let WBN_PREP_TO_END_FREE_7 = prove(wbn_prep_to_end_full_free_goal 7, WBN_PREP_TO_END_FULL_r_TAC 7);;
let WBN_PREP_TO_END_FREE_8 = prove(wbn_prep_to_end_full_free_goal 8, WBN_PREP_TO_END_FULL_r_TAC 8);;

(* r = 1..8, derived from the union-band FREE_r without re-simulation. *)
let WBN_PREP_TO_END_FULL_1 = prove(wbn_prep_to_end_full_goal 1, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_1);;
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
(* The nblk 9..16 leg: the main loop is not entered.                         *)
(*                                                                           *)
(* For 9 <= nblk <= 16, q = (nblk - 9) DIV 8 = 0 and                         *)
(* d = 128 * ((nblk - 1) DIV 8) = 128, since (nblk - 1) DIV 8 = 1 throughout *)
(* 9..16.  So at the loop-skip branch (the b.ge 0x7fc at 0x3b0, on the cmp   *)
(* x0,x5 at 0x3a8) X0 = in_p + 128 equals X5 = in_p + 128: the branch is     *)
(* taken, and control goes from the front straight to the prepretail 0x7fc.  *)
(* (For nblk >= 17, d >= 256, so X0 < X5 and the b.ge falls through to the   *)
(* loop head 0x3b4: the path of WBN_FRONT_TO_END.)                           *)
(*                                                                           *)
(* The 9..16 leg is therefore a chain of three parts:                        *)
(*   front       pc+0x1c -> 0x7fc (b.ge taken)  WBN_FRONT_TO_PREP_916        *)
(*   prepretail  0x7fc -> pc+3032, k = 0        WBN_PREPRETAIL_EXT2_916      *)
(*   tail        pc+3032 -> pc+3708             WBN_PREP_TO_END_916          *)
(* The front shares its prefix simulation with the >=17 front                *)
(* (WBN_FRONT_PREFIX_EXT) and differs from it only in the hypotheses         *)
(* (9 <= nblk /\ nblk <= 16 for 17 <= nblk) and in the resolution of the     *)
(* 0x3b0 branch, which changes only the PC.  The prepretail is               *)
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

(* The postcondition of the 9..16 front leg: wbn_core_applied 0 at PC 0x7fc. *)
let wbn_entry_post_916 =
  mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc`;
      `read PC s = word (pc + 2044)`;
      mk_comb(mk_comb(wbn_core_applied,`0:num`),`s:armstate`)]);;

let wbn_front_to_prep_916_goal =
  let ens = list_mk_comb(`ensures arm`,[wbn_front_P_tm; wbn_entry_post_916; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_916_tm, ens));;

(* The 9..16 front leg: the shared prefix WBN_FRONT_PREFIX_EXT (pc+0x1c to the
   0x3b0 b.ge, with the loop constants R) via ENSURES_TRANS_SIMPLE, then step
   230: the b.ge is taken for 9..16, since the cmp x0,x5 at 0x3a8 compares
   X0 = in_p + 128 with X5 = in_p + 128 * ((nblk - 1) DIV 8) = in_p + 128
   (NF = VF = F), landing at 0x7fc with wbn_core_applied 0.  The invariant
   core, the htable and the ABI frame are unfolded before the step, so that the
   htable reads propagate through it (the stepper does not track the folded
   htable_mem_dec) and the final state discharges the frame; the counters close
   as gcm_ctr_add lanes, Q19 as the reversed tag over no blocks and Q30 as the
   raw counter + 13. *)
let WBN_FRONT_TO_PREP_916 = prove(wbn_front_to_prep_916_goal,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_front_prefix_ext_post THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    MATCH_MP_TAC WBN_FRONT_PREFIX_EXT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[wbn128_loop_inv_core; htable_mem_dec; LET_DEF; LET_END_DEF;
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ARM_SIM_TAC AES128_GCM_DEC_ALT_EXEC (230--230) THEN
    CONV_TAC(NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
             NUM_REDUCE_CONV) THEN
    ASM_SIMP_TAC(wb_ctr_lanes_thms @
      [ARITH_RULE `9 <= nblk /\ nblk <= 16 ==> (nblk - 1) DIV 8 = 1`;
       MULT_CLAUSES; ISPECL [`word 128:int64`; `in_p:int64`] WORD_ADD_SYM;
       WORD_SUB_REFL; IVAL_WORD_0; INT_SUB_REFL; INT_LT_REFL;
       GCM_CTR_ADD_LANES; gcm_ctr_inc_iter; GCM_CTR_INC_ITER_AS_ADD;
       gcm_ctr_raw_def; list_of_seq; MAP; ghash_polyval_acc; WORD_ADD_0;
       WORD_RULE `word_add (word_add (x:32 word) (word 12)) (word 1) =
                  word_add x (word 13)`])]);;

(* The 9..16 prepretail, derived without simulation from
   WBN_PREPRETAIL_EXT2_UNIFIED by strengthening the hypotheses: that theorem is
   proved on the band 9 <= nblk, which contains 9..16, so MATCH_MP_TAC and
   ASM_ARITH_TAC close it. *)
let wbn_prepretail_ext2_916_goal = mk_wbn_prepretail_goal wbn_front_hyps_916_tm;;

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
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_entry_post_916 THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ASM_SIMP_TAC[WBN_FRONT_TO_PREP_916];
    MP_TAC(SPECL wb_front_vars WBN_PREPRETAIL_EXT2_916) THEN
    ASM_SIMP_TAC[ARITH_RULE `nblk <= 16 ==> (nblk - 9) DIV 8 = 0`]]);;

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

(* r = 1..8, derived without re-simulation from the WBN_PREP_TO_END_FREE_r
   theorems proved on the band 9 <= nblk above. *)
let WBN_PREP_TO_END_FULL_916_1 = prove(wbn_prep_to_end_full_916_goal 1, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_1);;
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

let WBN_RAWCT_READ = prove
 (`i < (nblk - 9) DIV 8 /\ 9 <= nblk /\
   LENGTH (ibytes:byte list) = 16 * nblk /\
   read (memory :> bytes (in_p:int64, 16 * nblk)) s = num_of_bytelist ibytes
   ==> !m. m < 8
       ==> read (memory :> bytes128 (word_add in_p (word (16 * (8*(i+1)+m))))) s =
           bytes_to_int128 (SUB_LIST (16 * (8*(i+1)+m), 16) ibytes)`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s:armstate`]
    INPUT_BYTES_TO_BYTE128_LANES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC_ALL WBN_RAWCT_BOUND) THEN ASM_SIMP_TAC[]]);;

(* RAWCT_LEMMA_AT sprev: add the WBN_RAWCT_READ !m lemma at state sprev to the
   assumptions; its premises come from the assumptions. *)
let RAWCT_LEMMA_AT sprev : tactic =
  SUBGOAL_THEN
    (subst[mk_var(sprev,`:armstate`),`s:armstate`]
      `!m. m < 8 ==> read (memory :> bytes128 (word_add in_p (word (16 * (8*(i+1)+m))))) s =
                     bytes_to_int128 (SUB_LIST (16 * (8*(i+1)+m), 16) ibytes)`)
    ASSUME_TAC THENL
   [MATCH_MP_TAC WBN_RAWCT_READ THEN ASM_REWRITE_TAC[]; ALL_TAC];;

(* RESOLVE_LDP_TAC sn: an ldp of the next group leaves its raw-ciphertext
   registers (Qn holds block 8 * (i + 1) + n - 8) as read Qn sn = read
   (memory :> bytes128 a) sl; resolve them against the raw lemma at the
   load-input state sl, then drop the raw forms *)
let RESOLVE_LDP_TAC (sn:string) : tactic =
  fun (asl,w) ->
    let raws = mapfilter (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(q,_)),Var(s,_))),
             Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),_)),Var(sl,_)))
          when s = sn && mem q ["Q8";"Q9";"Q10";"Q11";"Q12";"Q13";"Q14";"Q15"] -> (q, sl)
      | _ -> fail()) asl in
    match raws with
      [] -> ALL_TAC (asl,w)
    | (_,sl)::_ ->
       let qs = map fst raws in
       (RAWCT_LEMMA_AT sl THEN
        EVERY (map (fun q -> RESOLVE_QREG_C q sn
                 (int_of_string(String.sub q 1 (String.length q - 1)) - 8)) qs) THEN
        DISCARD_ASSUMPTIONS_TAC(fun th -> match concl th with
           Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(n,_)),_)),
                Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),_)),_))
             -> mem n qs
         | _ -> false)) (asl,w);;

(* CTR_FOLD_TAC sn: v30, the raw counter, is read only by rev32 vk,v30 (the
   AES input of a block) and add v30,v30,v31 (its increment); fold whichever
   of the two step sn ran.  A Q register other than Q30 holding a gcm_ctr_raw
   tower is a fresh rev32 (REV32_FOLD_TAC), a Q30 that is not gcm_ctr_raw
   itself a fresh add (CTR_INCR_NORM_TAC). *)
let CTR_FOLD_TAC (sn:string) : tactic =
  fun (asl,w) ->
    let is_raw t = match t with
        Comb(Comb(Const("gcm_ctr_raw",_),_),_) -> true | _ -> false in
    let raw_arg r = rand(rator(find_term is_raw r)) in
    let fold (_,th) = match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(q,_)),Var(s,_))),r)
          when s = sn && String.length q >= 2 && q.[0] = 'Q' ->
          if q <> "Q30" then REV32_FOLD_TAC q sn (raw_arg r)
          else if is_raw r then fail()
          else CTR_INCR_NORM_TAC sn (dest_small_numeral(rand(rand(raw_arg r))))
      | _ -> fail() in
    (try tryfind fold asl with Failure _ -> ALL_TAC) (asl,w);;

(* The body steppers: the KEEPDATA ones with the counter folded after every
   step, the unsimplified one also resolving the ldp's.  The first resets the
   KEEPDATA memo, so each simulation is hermetic. *)
let ARM_STEPS_CTR_KEEPDATA_TAC exec snums =
  CLEAR_KEEPDATA_MEMO_TAC THEN
  MAP_EVERY (fun n -> ARM_STEPS_FOLD_KEEPDATA_TAC exec [n] THEN
                      CTR_FOLD_TAC ("s"^string_of_int n)) snums;;
let ARM_STEPS_CTR_KEEPDATA_NOSIMP_TAC exec snums =
  MAP_EVERY (fun n -> let s = "s"^string_of_int n in
     ARM_VERBOSE_STEP_TAC exec s THEN RESOLVE_LDP_TAC s THEN
     DISCARD_STALE_DATA_TAC THEN DISCARD_OLDSTATE_KEEPDATA_TAC s THEN CLARIFY_TAC THEN
     CTR_FOLD_TAC s) snums;;

(* NEWBLK_CLOSE_TAC: close one new-block leg of the store forall, j = 8*(i+1)+m
   with 0 <= m < 8.  Canonicalize the block indices 8*(i+1)+m to 8*i+(8+m),
   normalize both store-readback address forms (out_p+(128*(i+1)+16m) and
   (out_p+128*(i+1))+16m) to the flat goal form, fire the readback, then fold
   the plaintext (GSYM aes9 and GCM_CTR_INC_ITER_AS_ADD) and bridge the
   SUB_LIST index. *)
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
     aese/aesmc tower: with GSYM aes9 first, the goal's left-hand side is still
     `read(mem) s274` (the tower not yet substituted), so the fold has nothing
     to match and REFL_TAC fails on the 8 new-block legs. *)
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM aes9] THEN REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD] THEN
  REWRITE_TAC (canon @ subbr) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM aes9] THEN REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD] THEN
  REWRITE_TAC (canon @ subbr) THEN REFL_TAC;;

(* fold the keystream tower to aes9 and the counter to gcm_ctr_add, for the
   plaintext conjuncts Q5, Q6, Q7 *)
let PLAINTEXT_CLOSE_TAC =
  REWRITE_TAC[GSYM aes9] THEN REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(8*i+8)+5 = 8*i+13`; ARITH_RULE `(8*i+8)+6 = 8*i+14`;
              ARITH_RULE `(8*i+8)+7 = 8*i+15`] THEN
  REFL_TAC;;

(* word distributes over the back-edge if *)
let WBN_PC_IF = prove
 (`(if b then word (pc + 948) else word (pc + 2044)):int64 =
   word (if b then pc + 948 else pc + 2044)`,
  COND_CASES_TAC THEN REWRITE_TAC[]);;

(* X0 and X2 after the four 32-byte post-increments of an iteration *)
let WBN_PTR_ADV = WORD_RULE
  `word_add (word_add p (word (128 * (i + 1)))) (word 128):int64 =
   word_add p (word (128 * (i + 2)))`;;

(* The loop body: one iteration, for every i < (nblk - 9) DIV 8. *)
let WBN_LOOP_BODY = prove(wbn_loop_body_goal,
  (* the invariant, the htable and the ABI frame unfolded in the goal, so
     ENSURES_INIT_TAC splits the htable reads, they close with the other
     state facts and ENSURES_FINAL_STATE_TAC discharges the frame *)
  REWRITE_TAC[WB_MC_LEN; wbn128_loop_inv_core; htable_mem_dec; LET_DEF; LET_END_DEF;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP WBN_NBLK_GE_9) THEN
  ENSURES_INIT_TAC "s0" THEN
  (* the AES/GHASH bulk, keeping the latest Q0..Q19, the counter folded at
     each rev32 and add of v30 *)
  ARM_STEPS_CTR_KEEPDATA_TAC AES128_GCM_DEC_ALT_EXEC (1--196) THEN
  (* the GHASH wire-in: PL/PH/PM complete at s197, abbreviated; from here
     on the steps run unsimplified, the next group's ciphertext resolved
     at load *)
  ARM_STEPS_CTR_KEEPDATA_NOSIMP_TAC AES128_GCM_DEC_ALT_EXEC (197--197) THEN
  WBN_Q19_EXTRACT_ABBREV_TAC "s197" THEN
  ARM_STEPS_CTR_KEEPDATA_NOSIMP_TAC AES128_GCM_DEC_ALT_EXEC (198--274) THEN
  (* the back-edge: X0 normalized, and the NF/VF of the cmp x0,x5 at s265
     resolved as standalone theorems rewritten into the assumptions *)
  (fun (asl,w) ->
     let prem = MATCH_MP WBN_PTRCMP_PREMS
       (CONJ (ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`)
             (ASSUME `i < (nblk - 9) DIV 8`)) in
     let flags = MATCH_MP (SPECL [`in_p:int64`; `128*(i+2)`; `128*((nblk-1) DIV 8)`]
                   WB_PTRCMP_FLAGS) prem in
     RULE_ASSUM_TAC(REWRITE_RULE[WBN_PTR_ADV; CONJUNCT1 flags; CONJUNCT2 flags])
       (asl,w)) THEN
  (* the postcondition: PC (the b.lt bridged to i + 1 < k), counter indices
     and the X0/X2 advances, then the residual conjuncts *)
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[MATCH_MP WBN_PC_BRIDGE (ASSUME `9 <= nblk`); WBN_PC_IF; WBN_PTR_ADV;
    ARITH_RULE `8 * (i + 1) = 8 * i + 8`;
    ARITH_RULE `(8*i+8)+8 = 8*i+16`; ARITH_RULE `(8*i+8)+9 = 8*i+17`;
    ARITH_RULE `(8*i+8)+10 = 8*i+18`; ARITH_RULE `(8*i+8)+11 = 8*i+19`;
    ARITH_RULE `(8*i+8)+12 = 8*i+20`; ARITH_RULE `(8*i+8)+13 = 8*i+21`;
    ARITH_RULE `128 * ((i + 1) + 1) = 128 * (i + 2)`] THEN
  (* the plaintexts Q5, Q6, Q7 by PLAINTEXT_CLOSE_TAC, leaving Q19 and the
     stores *)
  REPEAT CONJ_TAC THEN TRY PLAINTEXT_CLOSE_TAC THENL
   [(* Q19: the reduce byteform over PL/PH/PM is the fold over 8 * i + 8 *)
    WBN_Q19_CLOSE_TAC;
    (* the stores: j < 8 * (i + 1) from the invariant, the 8 new blocks by
       NEWBLK_CLOSE_TAC *)
    ASM_REWRITE_TAC[ARITH_RULE `j < 8 * i + 16 <=>
        j < 8 * (i + 1) \/ j = 8*(i+1) \/ j = 8*(i+1)+1 \/ j = 8*(i+1)+2 \/
        j = 8*(i+1)+3 \/ j = 8*(i+1)+4 \/ j = 8*(i+1)+5 \/ j = 8*(i+1)+6 \/
        j = 8*(i+1)+7`;
      TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`; FORALL_AND_THM;
      FORALL_UNWIND_THM2] THEN
    REPEAT CONJ_TAC THEN NEWBLK_CLOSE_TAC]);;

(* The main loop, PC = pc+948 /\ core 0 to PC = pc+2044 /\ core k: the skeleton
   WBN_MAIN_LOOP_OF_BODY applied to the body WBN_LOOP_BODY. *)
let WBN_MAIN_LOOP_raw = prove(wbn_main_loop_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun hyps -> MATCH_MP_TAC (MP (SPEC_ALL WBN_MAIN_LOOP_OF_BODY) hyps)) THEN
  FIRST_ASSUM(fun hyps -> ACCEPT_TAC (MP (SPEC_ALL WBN_LOOP_BODY) hyps)));;

(* ------------------------------------------------------------------------- *)
(* The >=17 chain: the front to the loop head, the loop, the prepretail and  *)
(* the shifted tail, pc+0x1c to the core exit pc+3708.                       *)
(* ------------------------------------------------------------------------- *)

(* The loop and the prepretail, from the loop head pc+948 (0x3b4) to the seam
   (WBN_LOOP_PREP_EXT2: WBN_MAIN_LOOP_raw, then WBN_PREPRETAIL_EXT2), and the
   front, the loop and the prepretail, from pc+0x1c to the seam
   (WBN_FRONT_TO_PREP_EXT2: WBN_LOOP_INVARIANT_ENTRY_RAW, then
   WBN_LOOP_PREP_EXT2), both by ENSURES_TRANS_SIMPLE. *)
let wbn_loop_prep_ext2_goal =
  let loop_pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc`;
      `read PC s = word (pc + 948)`;
      mk_comb(mk_comb(wbn_core_applied,`0`),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[loop_pre; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_LOOP_PREP_EXT2 = prove(wbn_loop_prep_ext2_goal,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC (rand(rator(snd(dest_imp(snd(strip_forall(concl WBN_MAIN_LOOP_raw))))))) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ASM_SIMP_TAC[WBN_MAIN_LOOP_raw];
    ASM_SIMP_TAC[WBN_PREPRETAIL_EXT2]]);;

let wbn_front_to_prep_ext2_goal =
  let ens = list_mk_comb(`ensures arm`,
    [wbn_front_P_tm; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_FRONT_TO_PREP_EXT2 = prove(wbn_front_to_prep_ext2_goal,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_entry_post THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ASM_SIMP_TAC[WBN_LOOP_INVARIANT_ENTRY_RAW];
    (* with the invariant split, the entry post is the loop's precondition up
       to the order and repetition of its conjuncts *)
    MP_TAC(SPECL wb_front_vars WBN_LOOP_PREP_EXT2) THEN
    ASM_REWRITE_TAC[WBN_INV_RAW_SPLIT; CONJ_ACI]]);;

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

(* Per-block value bridge: the store value of wbn_end_post,
   word_xor (word_xor cph (aes9 ..)) k10, is EL j of aes128_ctr over the
   gcm_dec_blocks_from list and the 11 round keys.  A separate lemma keeps the
   AES and counter algebra out of the ensures context; it is the symbolic-j
   analogue of build_aes_ctr_el. *)
let WBN_ENDBLOCK_IS_AES_CTR = prove
 (`!nblk ibytes ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 j.
     j < nblk
     ==> word_xor
           (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16) ibytes))
             (aes9 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9))
           k10 =
         EL j (aes128_ctr ctr0 (gcm_dec_blocks_from 0 nblk ibytes)
                 [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`nblk:num`; `0`; `j:num`; `ibytes:byte list`]
    EL_GCM_DEC_BLOCKS_FROM) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`gcm_dec_blocks_from 0 nblk ibytes`; `ctr0:int128`;
    `[k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]:int128 list`; `j:num`]
    EL_AES128_CTR) THEN
  ASM_REWRITE_TAC[LENGTH_GCM_DEC_BLOCKS_FROM] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM AES128_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE);;

(* The output bridge: the per-block store forall of wbn_end_post
   (word_xor (word_xor cph (aes9 ..)) k10) collapses to
   byte_list_at (gcm_dec128_pt_bytes (16 * nblk) ..) over the whole buffer, the
   symbolic-nblk analogue of the BYTE_LIST_AT_WHOLE_CTR leg of
   prove_wb_wrapper.  128 * nblk < 2 EXP 64 (from the chain hypotheses) gives
   val (word (16 * nblk)) = 16 * nblk. *)
let WBN_END_OUTPUT_BYTE_LIST = prove
 (`!nblk ibytes ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 out_p s.
     1 <= nblk /\ 128 * nblk < 2 EXP 64 /\
     (!j. j < nblk
          ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
              word_xor
              (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16) ibytes))
              (aes9 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9))
              k10)
     ==> byte_list_at
           (gcm_dec128_pt_bytes (16 * nblk) ibytes ctr0
              [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10])
           out_p (word (16 * nblk)) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GCM_DEC128_PT_BYTES_WHOLE_SYM] THEN
  MATCH_MP_TAC BYTE_LIST_AT_WHOLE_CTR THEN
  REWRITE_TAC[LENGTH_GCM_DEC_BLOCKS_FROM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC WBN_ENDBLOCK_IS_AES_CTR THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* WBN_DEC_CORE_BYTELIST: the core spine, pc+28 to pc+3708, for every        *)
(* 1 <= nblk, with H free and the output as the whole-buffer byte list.      *)
(* It is DISPATCH's statement with nblk <= 8 dropped and the two size        *)
(* premises 128 * nblk < 2 EXP 64 and val in_p + 16 * nblk < 2 EXP 63        *)
(* added.  nblk <= 8 is DISPATCH; above that ENSURES_PREPOSTCONDITION_THM    *)
(* moves the chain from its raw vocabulary (k0..k10, h, xi) to the NIST one  *)
(* (EL i rk, byteswap128 (ghash_twist H), word_reversefields 8 tag0), and    *)
(* the chain is WBN_FRONT_TO_END_916 for 9..16 blocks (the loop skipped)     *)
(* and WBN_FRONT_TO_END for >= 17.                                           *)
(* ------------------------------------------------------------------------- *)

let WBN_DEC_CORE_BYTELIST = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p nblk ibytes rk H
    tag0 ctr0.
    1 <= nblk /\
    128 * nblk < 2 EXP 64 /\
    val in_p + 16 * nblk < 2 EXP 63 /\
    LENGTH ibytes = 16 * nblk /\
    LENGTH rk = 11 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16]
    [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htable_p,192; stackpointer,80] /\
    PAIRWISE nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16] /\
    ALL (nonoverlapping (stackpointer,80))
    [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htable_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
              read PC s = word (pc + 28) /\
              read SP s = stackpointer /\
              C_ARGUMENTS
                [in_p; word (128 * nblk); out_p; tag_p; ivec_p; key_p; htable_p]
                s /\
              byte_list_at ibytes in_p (word (16 * nblk)) s /\
              read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
              read (memory :> bytes128 ivec_p) s = ctr0 /\
              wordlist_from_memory (key_p,11) s = rk /\
              htable_mem_8 (ghash_twist H) htable_p s)
         (\s. read PC s = word (pc + 3708) /\
              read X9 s = word (16 * nblk) /\
              byte_list_at (gcm_dec128_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p
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
  (* identification substitution: raw chain vars -> DISPATCH NIST vars *)
  let idsub =
    [`word_reversefields 8 (tag0:int128)`,`xi:int128`;
     `byteswap128 (ghash_twist H)`,`h:int128`] @
    (map (fun i -> mk_comb(mk_comb(`EL:num->(int128)list->int128`,mk_small_numeral i),
                           `rk:int128 list`),
                   mk_var("k"^string_of_int i,`:int128`)) (0--10)) in
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `nblk <= 8` THENL
   [ASM_MESON_TAC[AES128_GCM_DEC_ALT_DISPATCH]; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
  EXISTS_TAC (subst idsub wbn_front_P_tm) THEN
  EXISTS_TAC (subst idsub wbn_end_post) THEN
  REPEAT CONJ_TAC THENL
   [(* the NIST precondition implies the raw one: the htable renamed, the key
       reads from the word list, the input read from the byte list *)
    REWRITE_TAC[HTABLE_MEM_DEC_IS_HTABLE_MEM_8; BYTESWAP128_INVOLUTION] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP KEY_READS_FROM_WORDLIST) THEN
    MP_TAC(ISPECL [`ibytes:byte list`; `in_p:int64`; `word (16 * nblk):int64`]
      BYTE_LIST_AT_TO_READ_BYTES) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64;
                 ARITH_RULE `128 * n < 2 EXP 64 ==> 16 * n < 2 EXP 64`];
    (* the raw postcondition implies the NIST one: PC, X9 and ivec agree, and
       with rk as its 11 elements the output and the tag are the two bridges *)
    BETA_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP RK_ETA_11) THEN
    ASM_MESON_TAC[WBN_END_OUTPUT_BYTE_LIST; WBN_TAG_NIST_BRIDGE;
                  BYTESWAP128_INVOLUTION];
    (* the raw chain: 9..16 blocks skip the main loop, >= 17 run it.  Its side
       conditions are the flattened hypotheses, oriented alike on both sides by
       NONOVERLAPPING_SYM (permutative, so HOL rewrites in order), and the band
       conditions follow by ASM_ARITH_TAC *)
    ASM_CASES_TAC `nblk <= 16` THENL
     [MATCH_MP_TAC WBN_FRONT_TO_END_916; MATCH_MP_TAC WBN_FRONT_TO_END] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_SYM]) THEN
    ASM_REWRITE_TAC[NONOVERLAPPING_SYM] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* WBN_DEC_SUBROUTINE_BYTELIST: the ABI wrapper spine, for                   *)
(* len_bits = 128 * nblk and any nblk including 0.  For nblk >= 1 it is the  *)
(* stock ARM_ADD_RETURN_STACK_TAC wrapper of WBN_DEC_CORE_BYTELIST at the    *)
(* in-frame SP: the entry guard (cbz x1; tst x1,#127; b.ne) falls through    *)
(* and the prologue spills d8..d15 to the 80-byte frame (steps 1..7), the    *)
(* core is one big step from pc+0x1c to pc+0xe7c, and the epilogue           *)
(* (mov x0,x9; the d-register reloads; ret) runs steps 9..14.  For nblk = 0  *)
(* the cbz is taken and the call returns 0 through the reject path.          *)
(* ------------------------------------------------------------------------- *)

let WBN_DEC_SUBROUTINE_BYTELIST = prove
   (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p nblk ibytes rk H
      tag0 ctr0 returnaddress.
      128 * nblk < 2 EXP 64 /\
      val in_p + 16 * nblk < 2 EXP 63 /\
      LENGTH ibytes = 16 * nblk /\
      LENGTH rk = 11 /\
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16]
      [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htable_p,192;
       word_sub stackpointer (word 80),80] /\
      PAIRWISE nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16] /\
      ALL (nonoverlapping (word_sub stackpointer (word 80),80))
      [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htable_p,192]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word pc /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS
               [in_p; word (128 * nblk); out_p; tag_p; ivec_p; key_p; htable_p]
               s /\
               byte_list_at ibytes in_p (word (16 * nblk)) s /\
               read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htable_p s)
          (\s. read PC s = returnaddress /\
               C_RETURN s = word (16 * nblk) /\
               byte_list_at (gcm_dec128_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p
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
  let EXEC = AES128_GCM_DEC_ALT_EXEC in
  (* nblk >= 1 in the shape ARM_ADD_RETURN_STACK_TAC takes: the statement
     below with stackpointer and returnaddress quantified last, and with the
     input byte bound and the facts that make the entry guard fall through
     (cbz x1 not taken; tst x1,#127 sets Z for the b.ne) as hypotheses, so
     that the prologue steps can use them *)
  let WBN_DEC_SUBROUTINE_NZ = prove
   (`!pc in_p out_p tag_p ivec_p key_p htable_p nblk ibytes rk H tag0 ctr0
        stackpointer returnaddress.
        ~(nblk = 0) /\
        val (word (16 * nblk):int64) = 16 * nblk /\
        ~(val (word (128 * nblk):int64) = 0) /\
        val (word_and (word (128 * nblk):int64) (word 127)) = 0 /\
        128 * nblk < 2 EXP 64 /\
        val in_p + 16 * nblk < 2 EXP 63 /\
        LENGTH ibytes = 16 * nblk /\
        LENGTH rk = 11 /\
        aligned 16 stackpointer /\
        ALLPAIRS nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16]
        [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htable_p,192;
         word_sub stackpointer (word 80),80] /\
        PAIRWISE nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16] /\
        ALL (nonoverlapping (word_sub stackpointer (word 80),80))
        [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htable_p,192]
        ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
                 read PC s = word pc /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS
                 [in_p; word (128 * nblk); out_p; tag_p; ivec_p; key_p; htable_p]
                 s /\
                 byte_list_at ibytes in_p (word (16 * nblk)) s /\
                 read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
                 read (memory :> bytes128 ivec_p) s = ctr0 /\
                 wordlist_from_memory (key_p,11) s = rk /\
                 htable_mem_8 (ghash_twist H) htable_p s)
            (\s. read PC s = returnaddress /\
                 C_RETURN s = word (16 * nblk) /\
                 byte_list_at (gcm_dec128_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p
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
    REWRITE_TAC[byte_list_at; wordlist_from_memory; HTABLE_MEM_8_FLAT; DIMINDEX_128] THEN
    ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(7,5) EXEC
     (REWRITE_RULE[byte_list_at; wordlist_from_memory; HTABLE_MEM_8_FLAT; DIMINDEX_128;
                   ARITH_RULE `1 <= n <=> ~(n = 0)`]
       (GENL [`pc:num`; `in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
              `key_p:int64`; `htable_p:int64`; `nblk:num`; `ibytes:byte list`;
              `rk:int128 list`; `H:int128`; `tag0:int128`; `ctr0:int128`;
              `stackpointer:int64`]
         (SPEC_ALL WBN_DEC_CORE_BYTELIST)))
     `[D8; D9; D10; D11; D12; D13; D14; D15]` 80) in
  REPEAT STRIP_TAC THEN
  (* nblk = 0: the entry cbz x1 (0x0) is taken before the prologue, so the
     function returns 0 in X0 touching no memory (L128_dec_ret at 0xe94:
     mov w0,#0; ret); d8-d15 and SP are untouched (never spilled).  The output
     byte list is empty (byte_list_at over word 0 is vacuous) and the tag is
     unchanged (nist_ghash H tag0 [] = tag0). *)
  ASM_CASES_TAC `nblk = 0` THENL
   [ASM_REWRITE_TAC[byte_list_at; C_ARGUMENTS; C_RETURN; SOME_FLAGS;
                    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
                    MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS;
                    MULT_CLAUSES; VAL_WORD_0; ARITH_RULE `i < 0 <=> F`;
                    list_of_seq; nist_ghash; gcm_ctr_inc_iter] THEN
    ARM_SIM_TAC EXEC (1--3);
    (* nblk >= 1: the lemma's extra hypotheses follow from ~(nblk = 0) and
       128 * nblk < 2 EXP 64 *)
    MATCH_MP_TAC WBN_DEC_SUBROUTINE_NZ THEN
    ASM_REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `127 = 2 EXP 7 - 1`] THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; MULT_EQ_0; ARITH_EQ; MOD_MULT;
                 ARITH_RULE `2 EXP 7 = 128`;
                 ARITH_RULE `128 * n < 2 EXP 64 ==> 16 * n < 2 EXP 64`]]);;

(* The whole-block subroutine result for len_bits = 128 * nblk, any nblk     *)
(* including 0: an internal helper for the public arbitrary-length theorem.  *)
let WBN_DEC_VALID_CALL_CORRECT = prove
 (`!pc stackpointer in_p out_p tag_p ivec_p key_p htable_p nblk inblock rk
    tag0 nonce c returnaddress.
    128 * nblk < 2 EXP 64 /\
    val in_p + 16 * nblk < 2 EXP 63 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16]
    [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htable_p,192;
     word_sub stackpointer (word 80),80] /\
    PAIRWISE nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16] /\
    ALL (nonoverlapping (word_sub stackpointer (word 80),80))
    [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htable_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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
              wordlist_from_memory (key_p,11) s =
              MAP (word_reversefields 8) rk /\
              htable_mem_8 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word (16 * nblk) /\
              (!j. j < nblk
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block aes128_cipher c nonce rk j)
                                (inblock j)) /\
              read (memory :> bytes128 tag_p) s =
              word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
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
let AES128_GCM_DEC_ALT_NOIBT_SUBROUTINE_CORRECT = prove
 (`!pc stackpointer in_p len_bits out_p tag_p ivec_p key_p htable_p inblock rk
    tag0 nonce c returnaddress.
    val in_p + 16 * gcm_wb_blocks len_bits < 2 EXP 63 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
    [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16]
    [word pc, LENGTH aes128_gcm_dec_alt_tmc;
     in_p,16 * gcm_wb_blocks len_bits; key_p,176; htable_p,192;
     word_sub stackpointer (word 80),80] /\
    PAIRWISE nonoverlapping
    [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16] /\
    ALL (nonoverlapping (word_sub stackpointer (word 80),80))
    [word pc, LENGTH aes128_gcm_dec_alt_tmc;
     in_p,16 * gcm_wb_blocks len_bits; key_p,176; htable_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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
              wordlist_from_memory (key_p,11) s =
              MAP (word_reversefields 8) rk /\
              htable_mem_8 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word (16 * gcm_wb_blocks len_bits) /\
              (!j. j < gcm_wb_blocks len_bits
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block aes128_cipher c nonce rk j)
                                (inblock j)) /\
              read (memory :> bytes128 tag_p) s =
              word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
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
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `val(len_bits:int64) MOD 128 = 0` THENL
   [(* Whole blocks, including zero: WBN_DEC_VALID_CALL_CORRECT at
       nblk = gcm_wb_blocks len_bits, where word (128 * nblk) is
       word (val len_bits) = len_bits by GCM_WB_BLOCKS_VALID. *)
    MP_TAC(INST [`gcm_wb_blocks len_bits`,`nblk:num`]
                (SPEC_ALL WBN_DEC_VALID_CALL_CORRECT)) THEN
    ASM_SIMP_TAC[GSYM GCM_WB_BLOCKS_VALID; WORD_VAL; VAL_BOUND_64];
    (* A non-multiple of 128: no blocks (gcm_wb_blocks len_bits = 0); cbz
       falls through (val len_bits <> 0), tst/b.ne rejects (the low seven
       bits are not all zero), and no memory is touched. *)
    SUBGOAL_THEN `~(val(len_bits:int64) = 0) /\
                  ~(val(word_and (len_bits:int64) (word 127)) = 0)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[VAL_WORD_AND_MASK_WORD; MOD_0;
                    ARITH_RULE `127 = 2 EXP 7 - 1 /\ 2 EXP 7 = 128`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[gcm_wb_blocks; MULT_CLAUSES; ADD_CLAUSES;
                    C_ARGUMENTS; C_RETURN; SOME_FLAGS;
                    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS;
                    MODIFIABLE_UPPER_SIMD_REGS;
                    list_of_seq; nist_ghash; ARITH_RULE `j < 0 <=> F`] THEN
    ARM_SIM_TAC AES128_GCM_DEC_ALT_EXEC (1--5)]);;

(* The same for the full code, with its BTI landing pad. *)

let AES128_GCM_DEC_ALT_SUBROUTINE_CORRECT = prove
 (`!pc stackpointer in_p len_bits out_p tag_p ivec_p key_p htable_p inblock rk
    tag0 nonce c returnaddress.
    val in_p + 16 * gcm_wb_blocks len_bits < 2 EXP 63 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
    [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16]
    [word pc, LENGTH aes128_gcm_dec_alt_mc;
     in_p,16 * gcm_wb_blocks len_bits; key_p,176; htable_p,192;
     word_sub stackpointer (word 80),80] /\
    PAIRWISE nonoverlapping
    [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16] /\
    ALL (nonoverlapping (word_sub stackpointer (word 80),80))
    [word pc, LENGTH aes128_gcm_dec_alt_mc;
     in_p,16 * gcm_wb_blocks len_bits; key_p,176; htable_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_mc /\
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
              wordlist_from_memory (key_p,11) s =
              MAP (word_reversefields 8) rk /\
              htable_mem_8 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word (16 * gcm_wb_blocks len_bits) /\
              (!j. j < gcm_wb_blocks len_bits
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block aes128_cipher c nonce rk j)
                                (inblock j)) /\
              read (memory :> bytes128 tag_p) s =
              word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
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
    aes128_gcm_dec_alt_mc aes128_gcm_dec_alt_tmc
    AES128_GCM_DEC_ALT_NOIBT_SUBROUTINE_CORRECT));;
(* ------------------------------------------------------------------------- *)
(* The exported theorem at the all-zero key:                                 *)
(* AES128_GCM_DEC_ALT_SUBROUTINE_CORRECT with rk the FIPS-197 schedule of    *)
(* that key and the key-table precondition evaluated to the real table (see  *)
(* ALT_ZERO_KEY_RULE in arm/proofs/utils/aes_gcm_common.ml).                 *)
(* ------------------------------------------------------------------------- *)

let AES128_GCM_DEC_ALT_ZERO_KEY_CORRECT =
  ALT_ZERO_KEY_RULE "AES128_GCM_DEC_ALT_ZERO_KEY_CORRECT"
    aes128_cipher AESAVS_ZERO_KEY_128_SCHEDULE
    `word 0x1099f4b39468565ccdd297a9df145877:int128`
    AES128_GCM_DEC_ALT_SUBROUTINE_CORRECT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(*                                                                           *)
(* AES128_GCM_DEC_ALT_SAFE is the safety theorem of the core, from pc+0x1c   *)
(* to the core exit pc+3708, for len_bits = 128 * nblk with 1 <= nblk.       *)
(* CORE_SAFE_TAC splits on nblk:                                             *)
(* - bands 1..4: driven step by step from the core entry                     *)
(*   (concrete_band_close_tac);                                              *)
(* - bands 5..8: one shared front to the tail compare at pc+0xbcc, then the  *)
(*   reusable tail theorem for the band (WB_TAIL_SAFE_1_EXISTS ..            *)
(*   WB_TAIL_SAFE_8_EXISTS);                                                 *)
(* - bands 9..16: a symbolic front through the prepretail to the same        *)
(*   compare, then the reusable tail for nblk - 8 blocks;                    *)
(* - nblk >= 17: the front to the loop head, the main loop                   *)
(*   (ENSURES_EVENTS_WHILE_UP2_TAC) and the prepretail, then the reusable    *)
(*   tail for the residue, (nblk - 9) MOD 8 + 1 blocks.                      *)
(*                                                                           *)
(* AES128_GCM_DEC_ALT_NOIBT_SUBROUTINE_SAFE adds the ABI wrapper, for any    *)
(* len_bits (ARBITRARY_WRAPPER_SAFE_TAC), and                                *)
(* AES128_GCM_DEC_ALT_SUBROUTINE_SAFE is its IBT lift (ARM_ADD_IBT_RULE).    *)
(* ------------------------------------------------------------------------- *)

let EXEC = AES128_GCM_DEC_ALT_EXEC;;

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
   open, then DRIVE from s0 to pc+3708, finalize.  Every branch condition on
   these bands is concrete arithmetic that the resolver reduces directly, so no
   band-specific step count is needed.  The bands 5..8 and 9..16 run a shared
   front instead (FRONT_58_CLOSE_TAC, front_916_sim_tac below). ---- *)
let concrete_band_close_tac =
  LEG_INIT_TAC THEN
  DRIVE_TAC 3708 700 THEN
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
          (word pc,LENGTH aes128_gcm_dec_alt_tmc) (stackpointer,80) /\
        ALLPAIRS nonoverlapping
          [out_p,16 * nblk; tag_p,16; ivec_p,16]
          [word pc,LENGTH aes128_gcm_dec_alt_tmc]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
                  read PC s = word (pc + 0xbcc) /\
                  read X0 s = tail_in /\
                  read X2 s = tail_out /\
                  read X3 s = tag_p /\
                  read X5 s = word (16 * rr) /\
                  read X6 s = htable_p /\
                  read X10 s = word_add stackpointer (word 64) /\
                  read X16 s = ivec_p /\
                  read events s = e)
             (\s. read PC s = word (pc + 3708) /\
                  (exists e2.
                       read events s = APPEND e2 e /\
                       e2 =
                       f_events in_p key_p htable_p out_p tag_p ivec_p nblk
                                tail_in tail_out pc stackpointer /\
                       memaccess_inbounds e2
                       [in_p,16 * nblk; tag_p,16; ivec_p,16;
                        key_p,176; htable_p,192; out_p,16 * nblk;
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
      `nonoverlapping (word pc,4960) (tail_out:int64,tail_len)` in
  let tail_reads =
    subst [tail_len,`tail_len:num`]
      `[(tail_in:int64),tail_len; tag_p,16; ivec_p,16; key_p,176; htable_p,192;
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
     [`nonoverlapping (word pc,4960) (out_p:int64,16 * nblk)`;
      `nonoverlapping (word pc,4960) (tag_p:int64,16)`;
      `nonoverlapping (word pc,4960) (ivec_p:int64,16)`] THEN
    SUBGOAL_THEN tail_code_nonoverlap ASSUME_TAC THENL
     [MATCH_MP_TAC NONOVERLAPPING_SUBREGIONS THEN
      MAP_EVERY EXISTS_TAC
       [`word pc:int64`; `4960`; `out_p:int64`; `16 * nblk`] THEN
      ASM_REWRITE_TAC[WB_CONTAINED_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `val (word (128 * nblk):int64) DIV 8 * 1 = 16 * nblk`
      SUBST_ALL_TAC THENL
     [MATCH_MP_TAC WB_SAFETY_BYTES_LEN THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    DRIVE_TAC 3708 400 THEN
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

(* front steps 1--229 to the b.ge at pc+944 (0x3b0), the flags of its cmp x0,x5
   at 0x3a8 resolved by WB_PTRCMP_FLAGS, then step 230 to the prepretail
   pc+2044 (0x7fc) *)
let front_916_sim_tac =
  ARM_QSTEPS_TAC EXEC (1--229) THEN
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
  ARM_QSTEPS_TAC EXEC (230--230);;

(* ---- front invariant at pc+0x3b4 (the loop head; the i=0 register state of
   wbn_loop_invariant_raw).  SEQUENCE augments it with e2 = f_ev_front. ---- *)
let front_inv = `\s:armstate.
     aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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

(* ---- nblk 5..8 shared front.  These four paths execute the same 204
   instructions from pc+0x1c through the taken branch at pc+0x340 and the
   common tail setup, landing at pc+0xbcc immediately before the tail compare.
   SEQUENCE augments the invariant with e2 = f_ev_58_front. ---- *)
let front_58_inv = `\s:armstate.
     aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
     read PC s = word (pc + 0xbcc) /\
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
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xbcc` front_58_inv THEN CONJ_TAC;;

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
  ARM_QSTEPS_TAC EXEC (1--201) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `nblk:num` D_ZERO_LE8)
    (CONJ (MATCH_MP (ARITH_RULE `5 <= nblk ==> 1 <= nblk`) (ASSUME `5 <= nblk`))
          (ASSUME `nblk <= 8`))]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  SUBGOAL_THEN `ival (in_p:int64) - ival in_p = &0` ASSUME_TAC THENL
   [CONV_TAC INT_ARITH; ALL_TAC] THEN
  ARM_QSTEPS_TAC EXEC (202--204) THEN
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

(* ---- >=17 leg entry.  Leaves two subgoals: the front (pc+28 to pc+948), then
   the rest (loop and tail, pc+948 to pc+3708). ---- *)
let GE17_ENTER_TAC =
  GE17_PREP_TAC THEN RESHAPE_LOOP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x3b4` front_inv THEN CONJ_TAC;;

(* ---- the >=17 front leg, pc+28 to pc+948 (the loop head).  The b.ge at 0x3b0
   is the main-loop entry test; the flags of its cmp x0,x5 (0x3a8) are resolved
   by WB_PTRCMP_FLAGS and D_GT_128 rather than by the affine resolver, since X5
   depends on nblk, which is symbolic on this leg. ---- *)
let GE17_FRONT_CLOSE_TAC =
  front_916_setup_tac THEN
  ARM_QSTEPS_TAC EXEC (1--229) THEN
  MP_TAC(SPECL [`in_p:int64`; `128`; `128 * ((nblk-1) DIV 8)`] WB_PTRCMP_FLAGS) THEN ANTS_TAC THENL
   [CONJ_TAC THEN MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN
    MP_TAC(ASSUME `17 <= nblk`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  MP_TAC(SPEC `nblk:num` D_GT_128) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ARM_QSTEPS_TAC EXEC (230--230) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ---- loop invariant: the register state at the loop head on iteration i.
   WHILE augments it with
   `e2 = APPEND (ENUMERATEL i f_ev_loop) (APPEND [] front)`. ---- *)
let loop_inv = `\(i:num) s:armstate.
     aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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

(* ---- the main loop, on the rest subgoal (pc+948 to pc+3708) once the front
   leg is closed: ENSURES_EVENTS_WHILE_UP2_TAC then REPEAT CONJ_TAC leave four
   subgoals, in this order:
     G0 the count is nonzero, ~((nblk-9) DIV 8 = 0)
     G1 entry (i = 0) at pc+948: the invariant at 0
     G2 the loop body, for all i
     G3 exit and tail, pc+2044 to pc+3708 (the residue dispatch) ---- *)
let GE17_LOOP_OPEN_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `(nblk - 9) DIV 8` `pc + 0x3b4` `pc + 0x7fc` loop_inv THEN
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
  ARM_QSTEPS_TAC EXEC (1--274) THEN
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
   pc+0xbcc *)
let GE17_TAIL_SETUP_TAC =
  LEG_INIT_TAC THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_QSTEPS_TAC EXEC (1--244) THEN                (* pc+2044 -> pc+3020 *)
  MP_TAC TAIL_LEFTOVER_BYTES THEN ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  SUBGOAL_THEN `(nblk - 9) MOD 8 < 8` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC; ALL_TAC];;

(* per-residue closer: instantiate the reusable tail theorem for rr + 1 blocks
   at s244 (MP_WB_TAIL_SAFE_TAC), consume it through
   USE_WB_COMPOSED_TAIL_SAFE_TAC, collapse the ladder to this residue's
   f_ev_t<rr>, then discharge. *)
let close_tail_residue rr =
  (* the DIVISION identity is needed: without it CONTAINED_TAC's arithmetic
     cannot show that the residue store at out_p+128*((nblk-9) DIV 8+1)+k is in
     bounds. *)
  SUBGOAL_THEN `16 * nblk = 128 * ((nblk - 9) DIV 8 + 1) + 16 * ((nblk - 9) MOD 8 + 1)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    MP_TAC(ASSUME `17 <= nblk`) THEN ARITH_TAC; ALL_TAC] THEN
  MP_WB_TAIL_SAFE_TAC (rr+1) "s244" `nblk:num`
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
  (* s474 is the tail theorem's entry pc+3020, after the 230 front steps and
     the 244 prepretail and tail-entry steps: all eight precondition registers
     hold there (three steps later the ldr q9,[x0],#16 advances X0). *)
  MP_WB_TAIL_SAFE_TAC r "s474" (mk_small_numeral k)
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
      front_916_setup_tac THEN front_916_sim_tac THEN ARM_QSTEPS_TAC EXEC (231--474) THEN
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
   the tag and ivec (16), key (176) and htable (192) bounds and the 80-byte
   frame equal this footprint, while the in/out bounds are the C length
   len_bits/8 (val len_bits DIV 8 bytes), which contains the 16 * nblk footprint
   and equals it when len_bits = word (128 * nblk). ---- *)
let AES128_GCM_DEC_ALT_SAFE = prove
 (`exists f_events.
     forall e pc stackpointer in_p out_p tag_p ivec_p key_p htable_p nblk.
         1 <= nblk /\
         128 * nblk < 2 EXP 64 /\
         val in_p + 16 * nblk < 2 EXP 63 /\
         aligned 16 stackpointer /\
         ALLPAIRS nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16]
         [word pc,LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk;
          key_p,176; htable_p,192; stackpointer,80] /\
         PAIRWISE nonoverlapping [out_p,16 * nblk; tag_p,16; ivec_p,16] /\
         ALL (nonoverlapping (stackpointer,80))
         [word pc,LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk;
          key_p,176; htable_p,192]
         ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
                  read PC s = word (pc + 28) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS
                  [in_p; word (128 * nblk); out_p; tag_p; ivec_p; key_p; htable_p]
                  s /\
                  read events s = e)
             (\s. read PC s = word (pc + 3708) /\
                  (exists e2.
                       read events s = APPEND e2 e /\
                       e2 =
                       f_events in_p key_p htable_p out_p tag_p ivec_p nblk pc
                       stackpointer /\
                       memaccess_inbounds e2
                       [in_p,16 * nblk; tag_p,16; ivec_p,16;
                        key_p,176; htable_p,192; out_p,16 * nblk;
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
         [EventJump (word (pc + 3736),ra);
          EventJump (word pc,word (pc + 3732))]
       else
         APPEND
           [EventJump (word (pc + 3728),ra); EventLoad (sp,16);
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
       [EventJump (word (pc + 3736),ra);
        EventJump (word (pc + 8),word (pc + 3732));
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
    (assoc "aes128_gcm_dec_alt" subroutine_signatures)
    AES128_GCM_DEC_ALT_NOIBT_SUBROUTINE_CORRECT
    AES128_GCM_DEC_ALT_EXEC;;

(* The statement of the exported safety theorem, for an arbitrary len_bits,
   first for the trimmed code.  The theorem below is proved as the
   noibt_full_spec that mk_safety_spec generates above from
   AES128_GCM_DEC_ALT_NOIBT_SUBROUTINE_CORRECT and the C signature, and the
   load fails unless that term is exactly the one written here:
   - the correctness theorem's hypotheses: the signed pointer bound, the stack
     alignment and the nonoverlapping lists;
   - access bounds sized by the C objects: in/out len_bits/8, tag 16, ivec 16,
     key 176, htable 24 * 8 = 192, and the 80-byte frame;
   - by keep_maychanges, the correctness theorem's MAYCHANGE frame, based on
     gcm_wb_blocks.
   Apart from the loaded code it constrains no memory contents (no key
   schedule, table, tag, counter or data precondition), so it holds for every
   content.
   This routine does not enforce the NIST GCM message limit. Callers must
   ensure the cumulative message length does not exceed 2^36 - 32 bytes
   (2^39 - 256 bits). *)
let AES128_GCM_DEC_ALT_NOIBT_SUBROUTINE_SAFE = prove
 (`exists f_events.
     forall e pc stackpointer in_p len_bits out_p tag_p ivec_p key_p htable_p
            returnaddress.
         val in_p + 16 * gcm_wb_blocks len_bits < 2 EXP 63 /\
         aligned 16 stackpointer /\
         ALLPAIRS nonoverlapping
         [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16]
         [word pc,LENGTH aes128_gcm_dec_alt_tmc;
          in_p,16 * gcm_wb_blocks len_bits; key_p,176; htable_p,192;
          word_sub stackpointer (word 80),80] /\
         PAIRWISE nonoverlapping
         [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16] /\
         ALL (nonoverlapping (word_sub stackpointer (word 80),80))
         [word pc,LENGTH aes128_gcm_dec_alt_tmc;
          in_p,16 * gcm_wb_blocks len_bits; key_p,176; htable_p,192]
         ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    aes128_gcm_dec_alt_tmc /\
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
                        key_p,176; htable_p,192; out_p,val len_bits DIV 8 * 1;
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
   (PURE_REWRITE_RULE[GSYM WB_CORE_FRAME_EQ] AES128_GCM_DEC_ALT_SAFE));;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "aes128_gcm_dec_alt" subroutine_signatures)
    AES128_GCM_DEC_ALT_SUBROUTINE_CORRECT
    AES128_GCM_DEC_ALT_EXEC;;

(* The same for the full code, with its BTI landing pad: the full_spec that
   mk_safety_spec generates from AES128_GCM_DEC_ALT_SUBROUTINE_CORRECT. *)

let AES128_GCM_DEC_ALT_SUBROUTINE_SAFE = prove
 (`exists f_events.
     forall e pc stackpointer in_p len_bits out_p tag_p ivec_p key_p htable_p
            returnaddress.
         val in_p + 16 * gcm_wb_blocks len_bits < 2 EXP 63 /\
         aligned 16 stackpointer /\
         ALLPAIRS nonoverlapping
         [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16]
         [word pc,LENGTH aes128_gcm_dec_alt_mc;
          in_p,16 * gcm_wb_blocks len_bits; key_p,176; htable_p,192;
          word_sub stackpointer (word 80),80] /\
         PAIRWISE nonoverlapping
         [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16] /\
         ALL (nonoverlapping (word_sub stackpointer (word 80),80))
         [word pc,LENGTH aes128_gcm_dec_alt_mc;
          in_p,16 * gcm_wb_blocks len_bits; key_p,176; htable_p,192]
         ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    aes128_gcm_dec_alt_mc /\
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
                        key_p,176; htable_p,192; out_p,val len_bits DIV 8 * 1;
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
    aes128_gcm_dec_alt_mc aes128_gcm_dec_alt_tmc
    AES128_GCM_DEC_ALT_NOIBT_SUBROUTINE_SAFE));;

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

let AES128_GCM_DEC_ALT_NOIBT_REJECT_NOACCESS = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p len_bits pc returnaddress e.
    val len_bits = 0 \/ ~(val len_bits MOD 128 = 0)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
           read PC s = word pc /\
           read X30 s = returnaddress /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read events s = e)
      (\s. read PC s = returnaddress /\
           C_RETURN s = word 0 /\
           (?e2. read events s = APPEND e2 e /\ memaccess_inbounds e2 [] []))
      (MAYCHANGE [PC; X0] ,, MAYCHANGE [events] ,, MAYCHANGE SOME_FLAGS)`,
  ALT_GUARD_REJECT_TAC AES128_GCM_DEC_ALT_EXEC);;

let AES128_GCM_DEC_ALT_REJECT_NOACCESS = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p len_bits pc returnaddress e.
    val len_bits = 0 \/ ~(val len_bits MOD 128 = 0)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_mc /\
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
                     aes128_gcm_dec_alt_mc aes128_gcm_dec_alt_tmc
                     AES128_GCM_DEC_ALT_NOIBT_REJECT_NOACCESS));;
